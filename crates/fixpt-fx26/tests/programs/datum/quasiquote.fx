;;; `quasiquote`: `unquote` evaluates, `unquote-splicing` appends a list of
;;; datums; a nested `quasiquote` deepens, as R7RS counts.
(define walk (subr pure (datum) int)
  (letrec ((walk (subr pure (datum) int)
             (lambda (d)
               (typecase d
                 (pair p (+ (walk (car p)) (walk (cdr p))))
                 (int i i)
                 (symbol s 100)
                 (vector v 10000)
                 (else e 0)))))
    walk))
(define x int 7)
(define xs (listof datum acyclic) (list 1 2))
(+ (walk `(a ,x ,@xs end))
   (+ (walk `(1 `(2 ,(3 ,x)))) (walk `#(p ,x))))
