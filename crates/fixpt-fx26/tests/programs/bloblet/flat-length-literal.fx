;; ! a flat array's literal length is 0 to 268435454
;; A flat array's literal length is below the length that means "to the end
;; of the suffix" (`FLAT_TO_THE_END`, TODO.md §77).
(define-type t (blobref (bloblet (fields) @b) (arrayof f64 268435455)))
