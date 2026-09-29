(define a (listof int acyclic)
  (cons 1 (cons 2 (cons 3 nil))))
(define b (cons (cons 1 (cons 2 nil)) (cons 5 (cons 6 (the (listof int @r) nil)))))
(define c (listof int acyclic) (cons 1 nil))
(define d (listof int @r) ; cons-chain: written later, by set-car!
  (cons 1 (cons 2 nil)))
