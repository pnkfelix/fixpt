;; ! this use of `m` is one it was expanded from, unchanged: its expansion would never end
;; A use that comes back inside its own expansion, where it is expanded.
(define-syntax m (syntax-rules ((_ e) (+ 1 (m e)))))
(m 1)
