;;; A quote builds with the standard `cons`, `append` and `nil`, through
;;; `#%fx`, whatever the program calls by those names.
(define xs (listof datum acyclic) (list 5 6))
(define walk (subr pure (datum) int)
  (letrec ((walk (subr pure (datum) int)
             (lambda (d)
               (typecase d (pair p (+ (walk (car p)) (walk (cdr p)))) (int i i) (else e 0)))))
    walk))
(let ((cons 3) (append 4) (nil 9))
  (+ (walk '(1 2 (3))) (+ (walk `(,cons ,@xs ,append)) (+ cons nil))))
