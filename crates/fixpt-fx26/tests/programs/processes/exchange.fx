;; => 10
;; Two processes exchanging messages (kayak's first test): each is told the
;; other's address, then a count goes back and forth between them, one more
;; each time, until it reaches 10, which the one that receives it puts in
;; an I-cell for the program.
(define-type msg (sumof (peer (addr msg @p)) (count int)))
(define done (icell int @d) (make-icell))
;; A player: told its peer, it answers each count with the next.
(define* play
  (poly ((r place))
    (subr (maxeff (receive r) (send @p) (init @d) nondet spin) ((inbox msg r)) unit))
  (plambda ((r place))
    (lambda (box)
      (tagcase (receive box)
        (peer other
          (letrec ((rally (subr (maxeff (receive r) (send @p) (init @d) nondet spin) () unit)
                     (lambda ()
                       (tagcase (receive box)
                         (count n
                           (if (>= n 10)
                               (icell-put! done n)
                               (begin (send other (sum count (+ n 1))) (rally))))
                         (peer x (rally))))))
            (rally)))
        (count n #u)))))
(define a (addr msg @p) (spawn (box msg r) ((proj play r) box)))
(define b (addr msg @p) (spawn (box msg r) ((proj play r) box)))
(send a (sum peer b))
(send b (sum peer a))
(send a (sum count 0))
(icell-get done)
