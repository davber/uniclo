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
(def macro (fun [:expressive :call-by-name :compile-time :macro] [args & body]
  `(fun [:expressive :call-by-name :macro] ~args ~@body)))
(def lambda (macro [args & body]
  `(fun [:fun] ~args ~@body)))
(def inline (macro [args & body]
  `(fun [:compile-time :runtime :reduce :expressive] ~args ~@body)))

;; Some trivial functions: identity
(def identity (lambda (x) x))
(def list (lambda x x))

;; defmacro, defn, definline, defmacro, fn

(def fn lambda)
(def defmacro (macro [name args & body] `(def ~name (macro ~args ~@body))))
(defmacro defn [f args & body] `(def ~f (fn ~args ~@body)))
(defmacro definline [f args & body] `(def ~f (inline ~args ~@body)))

;; function composition: comp, swap
(defn comp [f g] (fn [x] (f (g x))))
(defn comp2 [f g] (fn [x y] (f (g x y))))
(defn swap [f] (fn [x y] (f y x)))

;; some primitive boolean operations: not, boolean, and, or
(defn not [x] (if x false true))
(def boolean (comp not not))
(defmacro or [& args]
  (if (empty? args) 'false
    `(if ~(first args) ~(first args) (or ~@(next args)))))
(defmacro and [& args]
  (if (empty? args) 'true
    `(if ~(first args) (and ~@(next args)) 'false)))

;; sequence operations: into, empty?, map

(defn into [dest from] (apply conj dest (seq from)))
(def empty? (comp not seq))
(defn map [f coll] (if (empty? coll) nil (cons (f (first coll)) (map f (rest coll)))))
(def second (comp first rest))
(def next (comp seq rest))

;; integrating with runtime/environment: load

(defn load [path] (eval* (read* (slurp path))))

;; conditions: cond, condp, match, local, let

;; create a local environment which is then discarded upon return
(defmacro local [& body]
  `((fn [] ~@body)))

(defmacro cond [& clauses]
  (if (empty? clauses) (quote nil)
    (if (= (count clauses) 1) (first clauses)
        (list (quote if) (first clauses) (second clauses)
              (cons (quote cond) (rest (rest clauses)))))))

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
    [] `(local ~@body)
    [var value & rest] `((fn [~var] (let ~(rest (rest bindings)) ~@body)) ~value)
    (fail "let has to have even number of elemnst in binding: " bindings)))
    

;; some arithmetics: <=, >= and >

(defn <= [x y] (or (< x y) (= x y)))
(def > (swap <))
(def >= (swap <=))
(def not= (comp2 not =))

;; some sequence operators

(defn append (s1 s2)
  (match s1
    [] s2
    [f & r] (cons f (append r s2))))
