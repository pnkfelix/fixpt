;;; FX-26 today: there is no arrow kind. The kind grammar itself is one
;;; shared parser used by `define-generative`, `poly`/`plambda`, `define-type`
;;; and `define-datatype` parameter lists alike (`crates/fixpt-fx26/src/parse.rs`,
;;; mirrored in `crates/fixpt-fx26/src/check-syntax.fx`), so all four forms
;;; give the same error for the same reason.
(define-generative (box (f (=> type type))) int)
