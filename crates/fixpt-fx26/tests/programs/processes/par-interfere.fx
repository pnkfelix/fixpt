;; ! `par`'s branches interfere: one has (write @x) and another (read @x)
;; Kayak's third test: one branch writes what another reads, so the answer
;; would depend on which runs first.
(define xs (arrayof int @x) (make-array 3 0))
(par ((a (begin (array-set! xs 0 1) 0))
      (b (array-ref xs 0)))
  (+ a b))
