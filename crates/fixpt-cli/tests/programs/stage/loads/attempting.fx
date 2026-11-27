;;; A module file whose code uses the scheduler's forms (`attempt`), which
;;; staged code and a session's step load (`TODO.md` §311).
(define safe (subr (maxeff spin nondet) () int)
  (lambda () (attempt (car (the (listof int acyclic) nil)) (lambda ((m string)) 7))))
