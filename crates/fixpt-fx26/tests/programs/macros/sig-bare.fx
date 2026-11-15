;; ! a signature is `(macro σ made)`, what its uses make written
;; A signature that leaves what its uses make unsaid.
(define-syntax twice
  (expr)
  (syntax-rules ((_ e) (+ e e))))
