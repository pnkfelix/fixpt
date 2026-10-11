;; ! a flat sum's key is `u8`, `u16` or `u32`
;; A flat sum's key, if given, is a width.
(define-type t (blobref (bloblet (fields) @b) (sumof u64 (0 f64))))
