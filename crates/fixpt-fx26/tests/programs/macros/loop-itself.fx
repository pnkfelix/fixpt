;; ! this use of `m` is one it was expanded from, unchanged: its expansion would never end
;; A use whose expansion is itself (`TODO.md` §231): refused where the use
;; comes back, the expansion it is in said below it.
(define-syntax m (syntax-rules ((_ e) (m e))))
(m 1)
