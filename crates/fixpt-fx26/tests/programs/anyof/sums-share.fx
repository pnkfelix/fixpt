;; ! a (sumof (#:x (oneof int bool)) (#:y int) (#:z bool)) is expected here, and this is a string
;; Two sums sharing a tag, in an `anyof`: one sum, the tag's payload the
;; union of its payloads.
(define-type a (sumof (x int) (y int)))
(define-type b (sumof (x bool) (z bool)))
(define v (anyof a b) "neither")
