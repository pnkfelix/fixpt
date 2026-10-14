;; => 7
;; A server polymorphic in its messages: `make-echo` spawns, for any
;; sendable `m`, a process that answers each `m` it is sent by filling the
;; I-cell sent with it. Of kind `type`, `m` could be anything, and the
;; spawn would be refused (`sendable-type.fx`).
(define-type (req (m type)) (productof (v m) (reply (icell m @r))))
(define* answer (poly ((m sendable)) (subr (init @r) ((req m)) unit))
  (plambda ((m sendable)) (lambda (q) (icell-put! (extract q reply) (extract q v)))))
(define* make-echo
  (poly ((m sendable))
    (subr (maxeff (alloc @e) (init @r) nondet spin) () (addr (req m) @e)))
  (plambda ((m sendable))
    (lambda ()
      (spawn (box (req m) p)
        (letrec ((go (subr (maxeff (receive p) (init @r) nondet spin) () unit)
                   (lambda () (begin ((proj answer m) (receive box)) (go)))))
          (go))))))
(define echo (addr (req int) @e) ((proj make-echo int)))
(define c (icell int @r) (make-icell))
(send echo (product (v 7) (reply c)))
(icell-get c)
