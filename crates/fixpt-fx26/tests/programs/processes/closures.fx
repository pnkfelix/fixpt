;; => 49
;; A procedure that writes nothing outside itself is transmissible, and so
;; is a message of one: the worker applies each it is sent.
(define-type job (productof (f (subr pure (int) int)) (x int) (out (icell int @o))))
(define worker (addr job @w)
  (spawn (box job p)
    (letrec ((go (subr (maxeff (receive p) (init @o) nondet spin) () unit)
               (lambda ()
                 (let ((j (receive box)))
                   (begin (icell-put! (extract j out) ((extract j f) (extract j x))) (go))))))
      (go))))
(define c (icell int @o) (make-icell))
(send worker (product (f (lambda ((n int)) (* n n))) (x 7) (out c)))
(icell-get c)
