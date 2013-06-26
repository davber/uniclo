;; defmacro, defn, fn

(def defmacro (macro (name args body) (list (quote def) name (list (quote macro) args body))))
(defmacro defn [f args body] (list (quote def) f (list (quote lambda) args body)))
(def fn lambda)

;; function composition

(defn comp [f g] (fn [x] (f (g x))))

;; boolean stuff: boolean, or, and, not
(defmacro or [x y] (list (quote if) x x y))
(defmacro and [x y] (list (quote if) x y x))
(defn boolean [x] (if x true false))
(defn not [x] (if x false true))

;; sequence operations: into, empty?, map

(defn into [dest from] (apply conj dest (seq from)))
(def empty? (comp not seq))
(defn map [f coll] (if (empty? coll) nil (cons (f (first coll)) (map f (rest coll)))))
(def second (comp first rest))

;; integrating with runtime/environment: load

(defn load [path] (eval* (read* (slurp path))))
