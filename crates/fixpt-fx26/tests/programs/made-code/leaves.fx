;;; Code a program makes and runs (`TODO.md` §97, `docs/research/
;;; declared-conventions.md`): a bloblet whose suffix is arm64 machine code,
;;; sealed into the code area, made a native procedure at a stated type.
;;; Where this machine runs no native code, the answers it would give.

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

(define-type held (bloblet (fields (pairof int int @heap)) @heap))

;; `ldr x0, <field 0>; ret`: its own field 0, 16 bytes before its code
;; (field 1 is the trailer), as the collector keeps it.
(define* holder (subr (maxeff (alloc @heap) (write @heap) (io native))
                      ((pairof int int @heap)) held)
  (lambda (p)
    (let ((b (the held (make-bloblet 8 p))))
      (begin (put4 b 0 1493172096)
             (put4 b 4 3596551104)
             (seal-code b)))))

(define* churn (subr (maxeff (alloc @heap) (read @heap) spin)
                     (int (listof int @heap)) int)
  (lambda (n acc)
    (if (= n 0) (list-length acc) (churn (- n 1) (if (= (modulo n 1000) 0) nil (cons n acc))))))

(native-code?)
(if (native-code?) ((adder) 20 22) 42)
(if (native-code?)
    (let ((h (holder (cons 41 1))))
      (let ((read (the (subr (conv native) (read @heap) () (pairof int int @heap))
                       (native-procedure h))))
        (begin (churn 200000 nil)
               (if (eq? (read) (bloblet-ref h 0)) (car (read)) -1))))
    41)
