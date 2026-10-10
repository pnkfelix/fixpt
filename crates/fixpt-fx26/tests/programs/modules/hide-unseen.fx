;; ! unbound variable `secret`
;; What is hidden is not in the module's type, so `with` does not find it.
(define m (module (hide (define secret int 7)) (define shown int secret)))
(with m secret)
