;;; A procedure a program made (`TODO.md` §97) called by typed calls in
;;; procedures, in tail position and not: on the arm64 cellular machines, a
;;; typed tail call of a native closure, which the Rust machine makes, then
;;; returns from the word; and register code's `invoke`, which calls it out
;;; to the Rust machine. Where this machine runs no native code, or runs
;;; another machine's (`made-code-x86_64/typed-calls.fx` is this on
;;; x86_64), the answers it would give.

;; Whether the code this makes runs here: native code, arm64's.
(define here bool
  (and (native-code?) (string=? (car (the (listof string @heap) (native-convention)))
                                "(target arm64)")))

;; Instruction `w` at byte `at` of `b`'s suffix, little-endian.
(define* put4 (subr (write @heap) ((bloblet (fields) @heap) int int) unit)
  (lambda (b at w)
    (begin (bloblet-set-byte! b at (modulo w 256))
           (bloblet-set-byte! b (+ at 1) (modulo (quotient w 256) 256))
           (bloblet-set-byte! b (+ at 2) (modulo (quotient w 65536) 256))
           (bloblet-set-byte! b (+ at 3) (quotient w 16777216)))))

;; `add x0, x1, x2; ret`: two fixnums' sum, their tags 0.
(define* adder (subr (maxeff (alloc @heap) (write @heap) (io native)) ()
                     (subr (conv native) pure (int int) int))
  (lambda ()
    (let ((b (the (bloblet (fields) @heap) (make-bloblet 8))))
      (begin (put4 b 0 2332164128)
             (put4 b 4 3596551104)
             (the (subr (conv native) pure (int int) int) (native-procedure (seal-code b)))))))

(define* via (subr (maxeff (alloc @heap) (write @heap) (io native)) () int)
  (lambda () (let ((g (adder))) (g 20 22))))
(define* via2 (subr pure ((subr (conv native) pure (int int) int)) int) (lambda (g) (g 20 22)))
(define* via3 (subr pure ((subr (conv native) pure (int int) int)) int)
  (lambda (g) (+ 1 (g 20 21))))

(if here (via) 42)
(if here (via2 (adder)) 42)
(if here (via3 (adder)) 42)
