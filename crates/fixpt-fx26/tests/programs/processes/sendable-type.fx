;; ! a process's messages are copied to it, so they must be transmissible
;; Refused: `sendable.fx`'s server, its message type's binder of kind
;; `type`, which could be anything.
(define-type (req (m type)) (productof (v m) (reply (icell m @r))))
(define* answer (poly ((m type)) (subr (init @r) ((req m)) unit))
  (plambda ((m type)) (lambda (q) (icell-put! (extract q reply) (extract q v)))))
(define* make-echo
  (poly ((m type))
    (subr (maxeff (alloc @e) (init @r) nondet spin) () (addr (req m) @e)))
  (plambda ((m type))
    (lambda ()
      (spawn (box (req m) p)
        (letrec ((go (subr (maxeff (receive p) (init @r) nondet spin) () unit)
                   (lambda () (begin ((proj answer m) (receive box)) (go)))))
          (go))))))
(define echo (addr (req int) @e) ((proj make-echo int)))
(define c (icell int @r) (make-icell))
(send echo (product (v 7) (reply c)))
(icell-get c)
