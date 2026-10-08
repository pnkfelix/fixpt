; Rejected: a closure made where a test holds may run later, after a write;
; what the test showed of a path does not hold in its body.
(define-type cell (pairof (union int string) int @r))
(define* later (subr (read @r) (cell) (subr (read @r) () int))
  (lambda (x) (if (int? (car x)) (lambda () (+ (car x) 1)) (lambda () 0))))
