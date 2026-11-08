;; => 2
;; A type form's name in head position is the form, whatever binds the
;; name: here a family named `listof` (`parse.rs`'s `TYPE_FORMS`).
(define-type (listof (a type)) a)
(length (the (listof int) (list 1 2)))
