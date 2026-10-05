;; ! unbound variable `helper`
;; A module's definitions are otherwise in order, each seeing those before
;; it, as at the top level: a definition using one after it is refused;
;; procedures that call each other are a `define-rec`.
(define m (module
  (define use (subr pure (int) int) (lambda (x) (helper x)))
  (define helper (subr pure (int) int) (lambda (x) (* x 2)))))
(with m (use 21))
