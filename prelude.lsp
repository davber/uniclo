;; defmacro
(def defmacro (macro (name args body) (list (quote def) name (list (quote macro) args body))))

;; defn macro for defining functions
(defmacro defn [f args body] (list (quote def) f (list (quote lambda) args body)))

;; Simplify loading of code
(def load (lambda (x) (eval* (read* (slurp x)))))

;; we use fn as in Clojure, alongside good old lambda
(def fn lambda)





