;; => 42
;; A request and its reply through an I-cell (kayak's second test): each
;; request carries the cell the server fills, and the asker waits for it.
(define-type req (productof (n int) (reply (icell int @r))))
(define doubler (addr req @srv)
  (spawn (box req p)
    (letrec ((serve (subr (maxeff (receive p) (init @r) nondet spin) () unit)
               (lambda ()
                 (let ((m (receive box)))
                   (begin (icell-put! (extract m reply) (* 2 (extract m n)))
                          (serve))))))
      (serve))))
(define* ask (subr (maxeff (send @srv) (alloc @r) (await @r)) (int) int)
  (lambda (n)
    (let ((c (the (icell int @r) (make-icell))))
      (begin
        (send doubler (product (n n) (reply c)))
        (icell-get c)))))
(+ (ask 20) (ask 1))
