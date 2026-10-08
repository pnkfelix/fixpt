;;; Quoted data are interned, by the evaluator written in FX-26 as by the
;;; heap (TODO §51): a quote is one value each time, equal quotes one, a
;;; quasiquote's constant part that value too, and one with an unquote new.
(define* f (subr pure () datum) (lambda () '(1 (a b) 2 "s")))
(define x int 7)
(define* g (subr pure () datum) (lambda () `(,x (a b) 2 "s")))
(define* tl (subr pure (datum) datum) (lambda (d) (typecase d (pair p (cdr p)) (else e d))))
(define* bit (subr pure (bool int) int) (lambda (b n) (if b n 0)))
(+ (bit (eq? (f) (f)) 1)
   (+ (bit (eq? '(1 2) '(1 2)) 2)
      (+ (bit (eq? (tl (g)) (tl (f))) 4) (bit (eq? (g) (g)) 8))))
