;;; `quote` of any datum (TODO §51): atoms as themselves, lists, dotted
;;; lists and vectors as `datum`s, built where they are written. A walk of
;;; one needs no `spin`.
(define walk (subr pure (datum) int)
  (letrec ((walk (subr pure (datum) int)
             (lambda (d)
               (typecase d
                 (pair p (+ (walk (car p)) (walk (cdr p))))
                 (int i i)
                 (symbol s 100)
                 (string s 1000)
                 (vector v 10000)
                 (else e 0)))))
    walk))
(+ (walk '(1 (2 3) a "b" #(c) #\d #t () . 4)) '5)
