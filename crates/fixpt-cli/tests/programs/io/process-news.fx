; News of any of several processes (Heist's FIXPT-CHANGES.md F6), for a
; program whose processes are not known when it is written: one `pselect`
; arm, `((process-news) p …)`, for whichever has output or has ended; each
; end is news once, since the program sees it.
(define-type state (productof (texts (listof string acyclic)) (ended (listof int acyclic))))
(define* nth-set (subr spin ((listof string acyclic) int string) (listof string acyclic))
  (lambda (l i s)
    (cond ((null? l) nil)
          ((= i 0) (cons (string-append (car l) s) (cdr l)))
          (else (cons (car l) (nth-set (cdr l) (- i 1) s))))))
(define* until-ended (subr (maxeff (io process) (io clock) nondet spin) (state int i64) state)
  ;; News taken until `left` processes have ended, or the deadline passes.
  (lambda (st left deadline)
    (if (= left 0) st
        (pselect ((process-news) p
                   (let* ((text (process-output p))
                          (st (product (texts (nth-set (extract st texts) p text))
                                       (ended (extract st ended)))))
                     (tagcase (process-status p)
                       (running u (until-ended st left deadline))
                       (else y (until-ended (product (texts (extract st texts))
                                                     (ended (cons p (extract st ended))))
                                            (- left 1) deadline)))))
                 ((sleep-until deadline) u st)))))
(define* start (subr (io process) (string) int)
  (lambda (script)
    (tagcase (process-start (list "/bin/sh" "-c" script) "") (started p p) (failed e -1))))
(define a int (start "sleep 0.3; echo A"))
(define b int (start "echo B1; sleep 0.1; echo B2"))
(define* join (subr spin ((listof string acyclic)) string)
  (lambda (l) (if (null? l) "" (string-append "[" (car l) "]" (join (cdr l))))))
(define* ints (subr spin ((listof int acyclic)) string)
  (lambda (l) (if (null? l) "" (string-append (int->string (car l)) " " (ints (cdr l))))))
(define done state
  (until-ended (product (texts (list "" "")) (ended nil)) 2 (i64+ (clock) (int->i64 5000000000))))
(write-out (string-append (join (extract done texts))
                          " ended, last first: " (ints (extract done ended))
                          (if (< (process-news) 0) "; no news left" "; news left") "\n"))
