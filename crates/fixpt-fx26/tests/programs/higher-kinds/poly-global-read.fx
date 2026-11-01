;; => 7
;; A global of a `poly` type, given where a `poly` is wanted (an element of
;; a list of them, a product's field, a `poly` annotation): its value, read
;; once, compared with what is wanted; the read is the reader's effect, not
;; the value's (Heist's, `TODO.md` §211, 5). Refused before: "a polymorphic
;; value must be pure, and this has (read (globals base))".
(define-type code (poly ((r region)) (subr (read r) ((ref int r)) int)))
(define base code (plambda ((r region)) (lambda (c) (get c))))
(define go (subr (maxeff (read @heap) (alloc @heap) (read (globals base))) () int)
  (lambda ()
    (let* ((cs (the (listof code acyclic) (list base base)))
           (p (the (productof (f code)) (product (f base))))
           (again (the code base))
           (c (the (ref int @heap) (new 7))))
      ((proj again @heap) c))))
(define again code (plambda ((r region)) (proj base r)))
(define go2 (subr (maxeff (read @heap) (alloc @heap) (read (globals again))) () int)
  (lambda () ((proj again @heap) (the (ref int @heap) (new 0)))))
(+ (go) (go2))
