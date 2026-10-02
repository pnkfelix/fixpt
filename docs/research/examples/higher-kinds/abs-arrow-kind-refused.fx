;;; FX-26 today: an abstract module component's kind is not even parsed by
;;; the general kind grammar (contrast arrow-kind-refused.fx, which hits
;;; that grammar). `(abs name what)` checks `what` against the literal
;;; symbol `type` before any kind is built (`crates/fixpt-fx26/src/parse.rs:1516-1519`,
;;; mirrored `crates/fixpt-fx26/src/check-modules.fx:70`), so this is
;;; refused the same way `tests/programs/modules/abs-kind.fx` is refused
;;; with `region` -- kind `(=> type type)` is never even considered.
(define-type bad (moduleof (abs f (=> type type)) (val wrap (subr pure (int) (f int)))))
