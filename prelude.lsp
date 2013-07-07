;; specifying symbols that precedes their argument, which will
;; be expanded during the expansion phase
(def *prefix-symbols* [(quote `) (quote ~@) (quote ~) (quote ')])
;; symbols that are infix
(def *infix-symbols* [(quote +)])

;; Some trivial functions: identity
(def identity (lambda (x) x))
(def list (lambda x x))

;; some meta functions: ` and '
(def ` backquote)
(def ' quote)
(def ~ (lambda (s) (fail "Tried to apply ~ as a function on " s)))
(def ~@ (lambda (s) (fail "Tried to apply ~@ as a function on " s)))

;; defmacro, defn, fn

(def fn lambda)
(def defmacro (macro [name args & body] `(def ~name (macro ~args ~@body))))
(defmacro defn [f args & body] `(def ~f (fn ~args ~@body)))

;; function composition: comp, swap
(defn comp [f g] (fn [x] (f (g x))))
(defn comp2 [f g] (fn [x y] (f (g x y))))
(defn swap [f] (fn [x y] (f y x)))

;; some primitive boolean operations: not, boolean
(defn not [x] (if x false true))
(def boolean (comp not not))

;; sequence operations: into, empty?, map

(defn into [dest from] (apply conj dest (seq from)))
(def empty? (comp not seq))
(defn map [f coll] (if (empty? coll) nil (cons (f (first coll)) (map f (rest coll)))))
(def second (comp first rest))
(def next (comp seq rest))
(defn nth [comp n]
  (if (= n 0) (first comp) (nth (rest comp) (- n 1))))

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



  
