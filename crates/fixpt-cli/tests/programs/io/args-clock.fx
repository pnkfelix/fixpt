; The program's own arguments, as `fixpt run FILE -- ARG…` gives them, each
; followed by `;`; and the clock: a sleep of 50 ms, which it then finds has
; passed (status 0, else 9).
(define-type strs (listof string @l))
(define* show (subr (maxeff (io stdout) (read @l) spin) (strs) unit)
  (lambda (xs) (if (null? xs) #u (begin (write-out (string-append (car xs) ";")) (show (cdr xs))))))
(define main (subr (maxeff (io args) (io clock) (io stdout) (alloc @l) (read @l) spin
                           (read (globals show)))
                   () int)
  (lambda ()
    (let ((t0 (clock)))
      (begin
        (show (args))
        (sleep-until (i64+ t0 (int->i64 50000000)))
        (if (i64>= (i64- (clock) t0) (int->i64 50000000)) 0 9)))))
