; Waiting for a process (Heist's FIXPT-CHANGES.md F6): a `pselect` with an
; arm for its output and one for its end, which comes after all its output;
; a deadline arm beside them. And `process-exit` alone, the output read
; after.
(define script string "printf 'one\\n'; sleep 0.2; printf 'two\\n'; exit 3")
(define* how-ended (subr pure ((sumof (exited int) (signalled int) (unknown unit))) string)
  (lambda (how)
    (tagcase how
      (exited c (string-append "exited " (int->string c)))
      (signalled s (string-append "signalled " (int->string s)))
      (unknown u "unknown"))))
(define* collect (subr (maxeff (io process) (io clock) nondet spin) (int string i64) string)
  ;; What process `p` writes, after `acc`, and how it ended; or that the
  ;; deadline came first.
  (lambda (p acc deadline)
    (pselect ((process-output p) text (collect p (string-append acc text) deadline))
             ((process-exit p) how (string-append acc (how-ended how)))
             ((sleep-until deadline) u (string-append acc "timed out")))))
(define* bars (subr spin (string) string)
  ;; `s`, each newline a bar.
  (lambda (s)
    (letrec ((go (subr spin (int (listof char acyclic)) (listof char acyclic))
               (lambda (i acc)
                 (if (< i 0) acc
                     (let ((c (string-ref s i)))
                       (go (- i 1) (cons (if (char=? c #\newline) #\| c) acc)))))))
      (list->string (go (- (string-length s) 1) nil)))))
(define waited string
  (tagcase (process-start (list "/bin/sh" "-c" script) "")
    (started p (bars (collect p "" (i64+ (clock) (int->i64 10000000000)))))
    (failed e "failed")))
(define alone string
  (tagcase (process-start (list "/bin/sh" "-c" "echo late; exit 4") "")
    (started p (let ((how (process-exit p)))
                 (string-append (how-ended how) ", then " (bars (process-output p)))))
    (failed e "failed")))
(write-out (string-append waited "; " alone "\n"))
