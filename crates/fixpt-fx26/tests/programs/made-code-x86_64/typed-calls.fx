;;; A procedure a program made (`TODO.md` §97) called by typed calls in
;;; procedures, in tail position and not: on the arm64 cellular machines, a
;;; typed tail call of a native closure, which the Rust machine makes, then
;;; returns from the word; and register code's `invoke`, which calls it out
;;; to the Rust machine. On x86_64: `made-code/typed-calls.fx` is this on
;;; arm64. Where this machine runs no native code, or runs another
;;; machine's, the answers it would give.

;; Whether the code this makes runs here: native code, x86_64's.
(define here bool
  (and (native-code?) (string=? (car (the (listof string @heap) (native-convention)))
                                "(target x86_64)")))

;; The bytes `bs` from byte `at` of `b`'s suffix.
(define* put-all (subr (maxeff (write @heap) (read @heap) spin)
                      ((bloblet (fields) @heap) int (listof int @heap)) unit)
  (lambda (b at bs)
    (if (null? bs) #u (begin (bloblet-set-byte! b at (car bs)) (put-all b (+ at 1) (cdr bs))))))

;; `lea rax, [rdi + rsi]; ret`: two fixnums' sum, their tags 0.
(define* adder (subr (maxeff (alloc @heap) (write @heap) (read @heap) spin (io native)) ()
                     (subr (conv native) pure (int int) int))
  (lambda ()
    (let ((b (the (bloblet (fields) @heap) (make-bloblet 5))))
      (begin (put-all b 0 (list 72 141 4 55 195))
             (the (subr (conv native) pure (int int) int) (native-procedure (seal-code b)))))))

(define* via (subr (maxeff (alloc @heap) (write @heap) (read @heap) spin (io native)) () int)
  (lambda () (let ((g (adder))) (g 20 22))))
(define* via2 (subr pure ((subr (conv native) pure (int int) int)) int) (lambda (g) (g 20 22)))
(define* via3 (subr pure ((subr (conv native) pure (int int) int)) int)
  (lambda (g) (+ 1 (g 20 21))))

(if here (via) 42)
(if here (via2 (adder)) 42)
(if here (via3 (adder)) 42)
