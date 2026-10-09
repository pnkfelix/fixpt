;;; The types of `check-terminate.fx`, its `check-terminate-module`: a module file of no
;;; state, which it loads, and so may its clients (`TODO.md` §68); its
;;; items in the order they were there.

;; The types these use, from the files that define them.
(define check-types-types (load-module "fx26:check-types-types.fx"))
(define-effect checks (select check-types-types checks))
(define-type k-ids (select check-types-types k-ids))
(define-type k-te (select check-types-types k-te))
;; What is known of a value, relative to a parameter of the member walked:
;; the parameter, or (strictly) a part of it, of a type; or the integer
;; parameter plus an offset.
(define-datatype k-tr (tr-part int bool int) (tr-int int int))
(define-type k-trs (listof k-tr acyclic))
(define-type k-tscope (listof (pairof symbol k-trs @t) acyclic))
;; Bounds that tests have put on parameters: 0 below, 1 above.
(define-type k-guards (listof (pairof int int @t) acyclic))
;; A size-change graph: edges between slots (parameter × 3 + measure: 0
;; parts, 1 down, 2 up), strict or not, in order and each pair once.
(define-type k-edge (productof (1 int) (2 int) (3 bool)))
(define-type k-graph (listof k-edge acyclic))
;; A call: its caller, its callee, and its graph.
(define-type k-call (productof (1 int) (2 int) (3 k-graph)))
(define-type k-calls (listof k-call acyclic))
;; For each call: caller, callee, and each argument as the caller's
;; parameter passed unchanged, or -1.
(define-type k-passed (listof (productof (1 int) (2 int) (3 k-ids)) acyclic))
;; Texts: a hint for each call, lines, names shown.
(define-type k-texts (listof string acyclic))
;; Why each definition, by name and declared type, may not end.
(define-type k-whys (listof (productof (1 symbol) (2 int) (3 string)) acyclic))
;; A computation of a type and an effect, which may fail.
(define-type k-thunk (subr (maxeff checks spin) () k-te))
