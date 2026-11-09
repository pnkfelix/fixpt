;; ! `m` is defined twice in this `define-syntax-rec`
(define-syntax-rec
  (m (syntax-rules () ((_) 1)))
  (m (syntax-rules () ((_) 2))))
1
