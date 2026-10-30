; A task waits for a process (Heist's FIXPT-CHANGES.md F6) while another
; runs: a process of FX-26's collects the program's output until it ends,
; and puts it in an I-cell, while the first task ticks on the clock.
(define* collect (subr (maxeff (io process) nondet spin) (int string) string)
  (lambda (p acc)
    (pselect ((process-output p) text (collect p (string-append acc text)))
             ((process-exit p) how (string-append acc "end")))))
(define* ticks (subr (maxeff (io clock) nondet spin) (int int) int)
  ;; Ticks every 20 ms, `n` times.
  (lambda (n done)
    (if (= n 0) done
        (pselect ((sleep-until (i64+ (clock) (int->i64 20000000))) u (ticks (- n 1) (+ done 1)))))))
(define got (icell string @o) (make-icell))
(define collector (addr int @w)
  (spawn (box int r) (icell-put! got (collect (receive box) ""))))
(define n int
  (tagcase (process-start (list "/bin/sh" "-c" "sleep 0.3; echo out") "")
    (started p (begin (send collector p) (ticks 5 0)))
    (failed e -1)))
(write-out (string-append (icell-get got) " " (int->string n) "\n"))
