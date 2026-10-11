;; ! a label of a sum keyed by `u8` is a number below 2^8
;; With a key, a flat sum's labels are numbers that fit it.
(define-type t (sumof u8 (0 f64) (256 i32)))
