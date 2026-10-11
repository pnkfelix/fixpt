;; ! a label of a sum keyed by `u16` is a number below 2^16
;; With a key, a flat sum's labels are numbers, not names.
(define-type t (sumof u16 (0 f64) (a i32)))
