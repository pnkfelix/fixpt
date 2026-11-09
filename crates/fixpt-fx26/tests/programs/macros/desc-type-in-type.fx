;; => 2
;; A use's type placed inside a template's type.
(define-syntax as-list (type expr)
  (syntax-rules ()
    ((_ t e) (length (the (listof t) e)))))
(as-list int (list 1 2))
