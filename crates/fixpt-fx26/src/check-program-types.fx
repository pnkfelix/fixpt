;;; The types of `check-program.fx`, its `check-program-module`, and its signature as its
;;; clients use it (`TODO.md` §68): a module file of no state.

;; The types these use, from the files that define them.
(define parser-types ((proj (load-module "fx26:parser-types.fx") @s @e @m @c @p)))
(define-type exp (select parser-types exp))
(define-type syn (select parser-types syn))
(define-type top (select parser-types top))
(define check-resolve-types (load-module "fx26:check-resolve-types.fx"))
(define-type k-def (select check-resolve-types k-def))
(define-type k-run (select check-resolve-types k-run))
(define check-types-types (load-module "fx26:check-types-types.fx"))
(define-type k-names (select check-types-types k-names))
(define-type kx (select check-types-types kx))
(define-type k-out (listof string acyclic))
;; A place in what a proof was given: a variable and the labels extracted.
(define-type k-pos (pairof symbol (listof symbol acyclic) @t))
;; What checking a proof relies on: its own name, the names of its
;; hypotheses, and what it proves, in words.
(define-type k-proving (productof (1 symbol) (2 k-names) (3 string)))
;; An arm of a `tagcase`: its tag, whether it takes the fields apart, the
;; names it binds, and its body.
(define-type k-case-arm (productof (1 symbol) (2 bool) (3 k-names) (4 kx)))
;; The top-level forms of a program.
(define-type k-tops (listof top acyclic))
;; A `define-rec`'s bindings: names, written types, and lambdas.
(define-type k-rec-forms (listof (productof (1 symbol) (2 syn) (3 exp)) acyclic))
(define-type k-run-list (listof k-run acyclic))
(define-type k-def-list (listof k-def acyclic))
;; The names of `ns` that are globals already, with their types.
(define-type k-olds (listof (pairof symbol int acyclic) acyclic))

;;; ------------------------------------------------------------ signatures

;; What its clients use of it (`compile-plan.fx`).
(define-type check-program-sig
  (moduleof ))
