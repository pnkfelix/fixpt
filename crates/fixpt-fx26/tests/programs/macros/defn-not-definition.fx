;; ! is not a definition: a macro that makes definitions makes `define`
(define-syntax define-nothing
  (-> (bvar) defn)
  (syntax-rules ()
    ((_ n) (+ 1 2))))
