;; ! `t` is bound in each repetition of a part, and referred to under fewer ellipses than it is bound: which repetition's it is is not said
;; A binder the template repeats, referred to outside the repetition.
(define-syntax last
  (expr ...)
  (syntax-rules ()
    ((_ e ...) (let ((t e) ...) t))))
(last 1 2 3)
