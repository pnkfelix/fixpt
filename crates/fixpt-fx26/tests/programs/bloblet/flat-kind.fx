;; => 42
;; The kind `flat` (`TODO.md` §77): a layout of raw bytes in a suffix, the
;; scalars `f64` `f32` `i32` `u32` `i64` `u64` or a variable of the kind;
;; and `(blobref B F)`, a pointer to an `F` in the suffix of a bloblet of
;; type `B`, its owner. Types only here.
(define-type b2 (bloblet (fields int bool) @b))
(define-type v (blobref b2 f64))
(define-type (view (f flat)) (blobref b2 f))
(define-type w (view i32))
(define id (poly ((f flat)) (subr pure ((blobref b2 f)) (blobref b2 f)))
  (plambda ((f flat)) (lambda (x) x)))
(define h (poly ((f flat)) (subr pure () int)) (plambda ((f flat)) (lambda () 42)))
((proj h u64))
