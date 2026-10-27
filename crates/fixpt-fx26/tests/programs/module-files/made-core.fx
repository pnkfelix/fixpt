;; A maker of a scheduler's state, over a region and an effect: its types
;; transparent and abstract (`load-moduleof.fx`).
(module-parameters ((ed region) (world effect)))
(define-type counter (productof (state (ref int ed))))
(define-generative ticket int)
(define issued (ref int ed) (new 0))
(define spawn (subr (alloc ed) (int) counter) (lambda (n) (product (state (new n)))))
(define peek (subr (read ed) (counter) int) (lambda (a) (get (extract a state))))
(define issue (subr (maxeff (read ed) (write ed)) () ticket)
  (lambda () (begin (set issued (+ (get issued) 1)) (up-ticket (get issued)))))
(define number (subr pure (ticket) int) (lambda (t) (down-ticket t)))
