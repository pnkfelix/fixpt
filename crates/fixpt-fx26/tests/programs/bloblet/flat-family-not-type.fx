;; ! `f` is a flat, not a type
;; Nor through a family's flat parameter, given a variable of the kind.
(define-type (view (f flat)) (listof f @b))
(define g (poly ((f flat)) (subr pure ((view f)) int)) (plambda ((f flat)) (lambda (x) 1)))
