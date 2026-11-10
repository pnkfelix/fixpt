;; ! the names `m` gives are not known before it is checked: give it a type where it is bound, `(the (moduleof …) e)` or a parameter's
;; A `with` of a module whose names the program does not say before it is
;; checked (`binding-shapes.md`): an element of a list of modules.
(define-type sig (moduleof (val x int)))
(define k (lambda ((ms (listof sig))) (let ((m (car ms))) (with m x))))
