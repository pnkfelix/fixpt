;;; A redefinition that reaches itself through a procedure kept as it was:
;;; the kept `h` calls the global `f`, which is now the new `f`, which calls
;;; the kept `h`. Its type says only that it reads `f` (calling `h` does),
;;; not `h`, which it reads when it is defined; the definitions say it uses
;;; `h`, which uses `f`. Refused.
(define* f (subr pure (int) int) (lambda (n) n))
(define* h (subr pure (int) int) (lambda (n) (f n)))
(define f (subr (read (globals f)) (int) int) (let ((h h)) (lambda (n) (h (+ n 1)))))
