;; ! a flat is `f64`, `f32`, `i32`, `u32`, `i64`, `u64`, `(productof (label flat) …)`
;; What a `blobref` points to is a flat, not any type.
(define-type bad (blobref (bloblet (fields int) @b) (listof int @b)))
