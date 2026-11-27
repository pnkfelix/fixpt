;; => 8
;; A labelled part repeated in a repeated part, `k @ label ...` in each
;; binding (Heist's `fixpt-nested-repetition.md`, 2026-11-27): `let-fields`
;; whose binding names a path of labels, each through a field of a field.
(define-syntax extract*
  (macro (_ e @ expr k @ label ...) expr)
  (syntax-rules
    ((_ e k) (extract e k))
    ((_ e k k2 ...) (extract* (extract e k) k2 ...))))
(define-syntax let-fields
  (macro (_ e @ expr ((x @ bvar k @ label ...) ...) body @ expr) expr
    (bind (x ...) in body))
  (syntax-rules
    ((_ e ((x k ...) ...) body)
     (let ((p e)) (let ((x (extract* p k ...)) ...) body)))))
(define-type inner (productof (#:refs int) (#:defs int)))
(define-type st (productof (#:ann inner) (#:name string)))
(define s st (product (#:ann (product (#:refs 3) (#:defs 4))) (#:name "x")))
(let-fields s ((r #:ann #:refs) (d #:ann #:defs) (n #:name)) (+ r (+ d (string-length n))))
