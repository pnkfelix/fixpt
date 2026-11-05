;; => (1 2)
;; A `oneof` and an `anyof` of the same members told apart are one type:
;; each is given where the other is expected.
(define* f (subr pure ((oneof int string)) int) (lambda (v) (if (int? v) v 2)))
(define* g (subr pure ((anyof int string)) int) (lambda (v) (f v)))
(define* h (subr pure ((oneof int string)) int) (lambda (v) (g v)))
(list (h 1) (h "two"))
