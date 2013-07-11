;; the most important "special form" is 'def'
(set-global! (quote MACRO-FUN-TYPE) [:expressive :call-by-name :expressive :compile-time :runtime :macro])
(set-global! (quote FUN-FUN-TYPE) [:runtime :fun])
(set-global! (quote INLINE-FUN-TYPE) [:expressive :compile-time :runtime :reduce :inline])

(set-global! (quote def) (fun MACRO-FUN-TYPE [var value]
                               (backquote (set-global! (quote ~var) ~value))))

;; we have to define empty early on, since it is used in 'comp', which
;; in turn is used quite eagerly from other definitions
(def empty? (fun [] [coll] (if (seq coll) false true)))

;; specifying symbols that precedes their argument, which will
;; be expanded during the expansion phase
(def *prefix-symbols* [(quote `) (quote ~@) (quote ~) (quote ')])
;; symbols that are infix
(def *infix-symbols* [(quote +)])

;; some meta functions: ` and '
(def ` backquote)
(def ' quote)
(def ~ (fun [] (s) (fail "Tried to apply ~ as a function on " s)))
(def ~@ (fun [] (s) (fail "Tried to apply ~@ as a function on " s)))

;; lambda, macro and inline
(def macro (fun MACRO-FUN-TYPE [args & body]
  `(fun ~MACRO-FUN-TYPE ~args ~@body)))
(def lambda (macro [args & body]
  `(fun ~FUN-FUN-TYPE ~args ~@body)))
(def inline (macro [args & body]
  `(fun ~INLINE-FUN-TYPE ~args ~@body)))

;; Some trivial functions: identity
(def identity (lambda (x) x))
(def list (lambda x x))

;; defmacro, defn, definline, defmacro, fn

(def fn lambda)
(def defmacro (macro [name args & body] `(def ~name (macro ~args ~@body))))
(defmacro defn [f args & body] `(def ~f (fn ~args ~@body)))
(defmacro definline [f args & body] `(def ~f (inline ~args ~@body)))

;; test for types
(defn symbol? [e] (= (type e) "symbol"))
(defn string? [e] (= (type e) "string"))
(defn num? [e] (= (type e) "number"))

;; function composition: comp, swap, partial
(defn comp [& fs] (if (empty? fs) identity (fn [x] ((first fs) ((apply comp (rest fs)) x)))))
(defn comp2 [f g] (fn [x y] (f (g x y))))
(defn swap [f] (fn [x y] (f y x)))
(defn partial [f & args] (fn [&rest] (f (append args rest))))

;; some primitive boolean operations: not, boolean, and, or
(defn not [x] (if x false true))
(def boolean (comp not not))
(defmacro or [& args]
  (if (empty? args) false
    `(if ~(first args) ~(first args)
      (or ~@(next args)))))
(defmacro and [& args]
  (if (empty? args) true
    `(if ~(first args) (and ~@(next args)) false)))

;; sequence operations: into, empty?, map, nth, count

(defn into [dest from] (apply conj dest (seq from)))
(defn map [f coll] (if (empty? coll) nil (cons (f (first coll)) (map f (rest coll)))))
(def second (comp first rest))
(def next (comp seq rest))
(defn nth [coll n] (if (= n 0) (first coll) (nth (rest coll) (- n 1))))
(defn count [coll] (if (empty? coll) 0 (+ (count (rest coll)) 1)))

;; integrating with runtime/environment: load

(def load (comp eval* read* slurp))

;; conditions: cond, condp, match, local, let

;; create a local environment which is then discarded upon return
(defmacro local [& body]
  `((fn [] ~@body)))

(defmacro cond [& clauses]
  (if (empty? clauses) 'nil
    (if (= (count clauses) 1) (first clauses)
        `(if ~(first clauses) ~(second clauses)
              (cond ~@(rest (rest clauses)))))))

;; TODO: implement in terms of cond
(defmacro condp [pred expr & clauses]
  (if (empty? clauses) (quote nil)
    (if (= (count clauses) 1) (first clauses)
         `(if (~pred ~(first clauses) ~expr) ~(second clauses)
              (condp ~pred ~expr ~@(rest (rest clauses)))))))

(defmacro match [expr & clauses]
  `(local (condp unify ~expr ~@clauses)))

(defmacro let [bindings & body]
  (match bindings
         '[] `(local ~@body)
         '[var value & rest] `((fn [~var] (let ~rest ~@body)) ~value)
         (fail "let has to have even number of elemnst in binding: " bindings)))
    

;; some arithmetics: <=, >= and >

(defn <= [x y] (or (< x y) (= x y)))
(def > (swap <))
(def >= (swap <=))
(def not= (comp2 not =))

;; some sequence operators

(defn append (s1 s2)
  (match s1
    '[] s2
    '[f & r] (cons f (append r s2))))

(defn zipWith [f s1 s2]
 (match [s1 s2]
   '[[] _] ()
   '[_ []] ()
   '[[x1 & r1] [x2 & r2]] (cons (f x1 x2) (zip r1 r2))))

(def zip (partial zipWith (fn [x1 x2] [x1 x2])))

(defn member? [elem coll]
  (and (seq coll) (or (= elem (first coll)) (member? elem (rest coll)))))

;; an evaluator of (expanded!) forms

(defn get-var [var]
  (or (get-local var) (get-global var)))

(defn eval [form]
  (match (type form)
         "keyword" form
         "number" form
         "string" form
         "symbol" (get-var `~form)
         "list" (if (empty? form) form (_apply (eval (first form)) (rest form)))))

;; this apply is currently only for lambdas
(defn apply-lambda [['fun ftype args & body] & vals]
  (zipWith (fn [k v] (stash! k v)) args vals)
  (import-stash!)
  (eval `(do ~@body)))

(defmacro unify [pat value]
  `(if (unify-aux ~pat ~value) (do (_import-stash!) true)
     (do (_reset-stash!) false)))

(defn unify-aux [pat value]
  (cond (symbol? pat) (do (_stash! `~pat value) true)
        (and (seqable? pat) (empty? pat)) (and (seqable? value) (empty? value))
        (= (first pat) '&) (and (seqable? value) (unify-aux (second pat) value))
        (member? (first pat) [(quote ') (quote `) 'quote 'backquote]) (= (second pat) value)
        (seqable? pat) (and (unify-aux (first pat) (first value)) (unify-aux (next pat) (next value)))
        (= pat value)))

