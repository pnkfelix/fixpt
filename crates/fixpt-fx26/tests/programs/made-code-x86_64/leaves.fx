;;; Code a program makes and runs (`TODO.md` §97, `docs/research/
;;; declared-conventions.md`), on x86_64: a bloblet whose suffix is x86_64
;;; machine code, sealed into the code area, made a native procedure at a
;;; stated type. Where this machine runs no native code, or runs another
;;; machine's (`made-code/leaves.fx` is this on arm64), the answers it would
;;; give.

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

(define-type held (bloblet (fields (pairof int int @heap)) @heap))

;; `mov rax, [rip - 23]; ret`: its own field 0, 16 bytes before its code
;; (field 1 is the trailer), as the collector keeps it.
(define* holder (subr (maxeff (alloc @heap) (write @heap) (read @heap) spin (io native))
                      ((pairof int int @heap)) held)
  (lambda (p)
    (let ((b (the held (make-bloblet 8 p))))
      (begin (put-all b 0 (list 72 139 5 233 255 255 255 195))
             (seal-code b)))))

(define* churn (subr (maxeff (alloc @heap) (read @heap) spin)
                     (int (listof int @heap)) int)
  (lambda (n acc)
    (if (= n 0) (list-length acc) (churn (- n 1) (if (= (modulo n 1000) 0) nil (cons n acc))))))

(native-code?)
(if here ((adder) 20 22) 42)
(if here
    (let ((h (holder (cons 41 1))))
      (let ((read (the (subr (conv native) (read @heap) () (pairof int int @heap))
                       (native-procedure h))))
        (begin (churn 200000 nil)
               (if (eq? (read) (bloblet-ref h 0)) (car (read)) -1))))
    41)
