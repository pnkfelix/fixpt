; A quote's constant taken apart in a word (`TODO.md` §316): each word
; verified, the verifier taking `car` and `cdr` of the interned constant
; as the literals they are, never written; a constant whole a `datum`.
(car '(a b))
(car (cdr '(1 #utf8"x" #u8(2) "s" #:k)))
(let ((d '(a b))) (if (pair? d) (car d) 0))
(define pick (subr pure (bool) datum)
  (lambda (b) (let ((d (if b '(a) '(b c)))) (if (pair? d) (car d) 0))))
(list (pick #t) (pick #f))
(define same (subr pure (datum) datum) (lambda (x) x))
(same '(a #u8(1) "s" #:k #(1)))
