;; defn macro for defining functions
(def defn (macro (f args body) (list (quote def) f (list (quote lambda) args body))))

;; Simplify loading of code
(def load (lambda (x) (eval* (read* (slurp x)))))

;; we use fn as in Clojure
(def fn lambda)




