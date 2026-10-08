;;; Quoted data are interned (`Heap::intern_datum`, TODO §51): a quote is
;;; one object each time it is evaluated, equal quotes are one object, and
;;; a quasiquote's constant parts are those objects too; on every machine.
(define* f (subr pure () datum) (lambda () '(1 (a b) 2)))
(define x int 7)
(define* g (subr pure () datum) (lambda () `(,x (a b) 2)))
(define* tl (subr pure (datum) datum) (lambda (d) (typecase d (pair p (cdr p)) (else e d))))
(define q datum (f))
(list (eq? (f) (f)) (eq? q (f)) (eq? '(1 2) '(1 2)) (eq? (tl (g)) (tl (f))) (eq? (g) (g)))
