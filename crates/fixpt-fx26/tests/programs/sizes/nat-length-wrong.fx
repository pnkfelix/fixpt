; Rejected: a length confirmed by `k`, the length of `xs`, is not `m`.
(define-type frozen (listof int const))
(define as-long
  (poly ((n size) (m size)) (subr pure ((nlist int n) frozen (nlist int m)) (nlist int m)))
  (lambda (xs ys otherwise)
    (let ((k (length xs)))
      (confirm-length ys k (zs zs) otherwise))))
