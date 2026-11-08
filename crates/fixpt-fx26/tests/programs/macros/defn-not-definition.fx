;; ! is not a definition: a macro that makes definitions makes `define`
(define-syntax define-nothing
  (-> (bvar) defn)
  ((_ n) (+ 1 2)))
