;;; The types of `regcode-helpers.fx`, its `regcode-helpers-module`: a module file of no
;;; state, which it loads, and so may its clients (`TODO.md` §68); its
;;; items in the order they were there.

;; The types these use, from the files that define them.
(define parser-types ((proj (load-module "fx26:parser-types.fx") @s @e @m @c @p)))
(define-type exp (select parser-types exp))
(define regcode-types (load-module "fx26:regcode-types.fx"))
(define-type rconst (select regcode-types rconst))
(define-type wcells (select regcode-types wcells))
(define compile-types (load-module "fx26:compile-types.fx"))
(define-type syms (select compile-types syms))
;; An expression, or none: a call's procedure (`r-args`), a closure's
;; region (`r-lambda`).
(define-type maybe-exp (listof exp @k))
;; A call unrolled over a constant list (`r-unrolled`, as the Rust
;; compiler's `r_unroll`, `TODO.md` §44): its procedure's expression, each
;; argument that is a global holding a constant list, with it (one that is
;; a constant here `r-known` finds), and the globals to guard. `r-inline`
;; compiles it, reading these (`r-known-arg`,
;; `r-guards-for`); newest first, as a call's arguments may hold others.
(define-type r-unroll-known (listof (pairof exp rconst @k) @k))
(define-type r-wglobals (listof wglobal @k))
(define-type r-unroll-found (productof (1 r-unroll-known) (2 r-wglobals) (3 bool)))
(define-type r-unroll-hook (productof (1 exp) (2 r-unroll-known) (3 r-wglobals)))
;; The global `a` names and its constant, if it is one.
(define-type r-unroll-globals (listof (pairof wglobal rconst @k) @k))
;; An expression split as `core + k` (`r-split`), and such a split, if any.
(define-type rsplit (productof (1 (listof exp @k)) (2 int)))
(define-type rsplits (listof rsplit @k))
;; A lambda's word, and the names it captures.
(define-type rmade (productof (1 tword) (2 syms)))
;; What `r-operands` makes of its second operand: an immediate, or the
;; register it is in, in a list.
(define-type roperands (productof (1 wcells) (2 (listof int @k))))
