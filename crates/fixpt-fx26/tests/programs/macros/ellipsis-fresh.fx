;; => 2
;; A template's binder under an ellipsis, made fresh in each repetition.
(define-syntax listed
  (expr ...)
  (syntax-rules ()
    ((_ e ...) (let ((t e) ...) (list t ...)))))
(car (cdr (listed 1 2 3)))
