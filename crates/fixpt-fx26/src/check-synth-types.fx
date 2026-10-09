;;; The types of `check-synth.fx`, its `check-synth-module`: a module file of no
;;; state, which it loads, and so may its clients (`TODO.md` §68); its
;;; items in the order they were there.

;; The types these use, from the files that define them.
(define check-test-facts-types (load-module "fx26:check-test-facts-types.fx"))
(define-type k-branch-facts (select check-test-facts-types k-branch-facts))
(define-type k-cert-lens (select check-test-facts-types k-cert-lens))
(define-type k-fact-list (select check-test-facts-types k-fact-list))
(define check-types-types (load-module "fx26:check-types-types.fx"))
(define-type k-eff (select check-types-types k-eff))
(define-type k-ids (select check-types-types k-ids))
(define-type k-named (select check-types-types k-named))
(define-type k-narrows (select check-types-types k-narrows))
(define-type k-regions (select check-types-types k-regions))
(define-type k-steps (select check-types-types k-steps))
(define-type k-ty (select check-types-types k-ty))
;; Types, and the effect of all.
(define-type k-types-eff (productof (1 k-ids) (2 k-eff)))
;; What a call's arguments were found to be before they are checked: types (or -1), effects.
(define-type k-done (productof (1 (arrayof int @t)) (2 (arrayof k-eff @t))))
;; What is certified so far: variables acyclic, of lengths, and natural.
(define-type k-certs (productof (1 k-named) (2 k-cert-lens) (3 k-named)))
;; What `p` narrows where it holds (`car`) and where not (`cdr`): the Rust
;; checker's `narrowings`. Each narrowing (`check.rs`'s `Narrowed`): a
;; variable, its binding's depth, the steps of a path from it (none for the
;; variable), the regions they read through, and the type there. Through
;; `not`, and through `and` and `or` (`(if a b #f)`, `(if a #t b)`) as
;; `k-test-facts` goes.
(define-type k-nar (productof (1 symbol) (2 int) (3 k-steps) (4 k-regions) (5 int)))
(define-type k-nars (listof k-nar acyclic))
(define-type k-narrowing (pairof k-nars k-nars acyclic))
;; `x` as a path from a variable: the variable, its binding's depth, and
;; the steps, `car`s, `cdr`s and products' fields (none or one).
(define-type k-path (productof (1 symbol) (2 int) (3 k-steps)))
(define-type k-paths (listof k-path acyclic))
;; A type and the regions read to reach it (none or one).
(define-type k-reached (listof (productof (1 int) (2 k-regions)) acyclic))
;; What checking an `if`'s branches puts back as it goes: what was certified, the size
;; facts, and what was narrowed, before; what its test shows when it holds, and when not;
;; what it narrows so; and how many paths' facts there were.
(define-type k-tested
  (productof (1 k-certs) (2 k-fact-list) (3 k-branch-facts) (4 k-narrows) (5 k-narrowing)
             (6 int)))
;;; Bounds (`TODO.md` §66): an argument a type binder bounded only from
;;; above (`check-bounds.fx`) is checked against says what it is.
;; The last call checked against a type: where it is, and its own type there
;; (the Rust checker's `checked_call`).
(define-type k-call-checked (productof (1 int) (2 int) (3 int)))
;; A type, or none: none or one.
(define-type k-maybe-ty (listof k-ty acyclic))

;;; ------------------------------------------------------------ signatures

;; What its clients use of it (`check-program.fx`).
;; The types it names, from the files that define them.
(define-type kx (select check-types-types kx))
(define-type check-synth-sig
  (moduleof (val k-note-frozen-define
                 (subr (maxeff (alloc @t)
                               (goto @z)
                               (read @globals)
                               (read @s)
                               (read @t)
                               (write @t)
                               spin)
                       (int kx)
                       unit))))
