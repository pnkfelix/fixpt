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
;; The types it names, from the files that define them.
(define-type k-binders (select check-types-types k-binders))
(define check-resolve-types (load-module "fx26:check-resolve-types.fx"))
(define-type k-callable (select check-resolve-types k-callable))
(define-type k-desc (select check-types-types k-desc))
(define-type k-names (select check-types-types k-names))
(define-type k-parts (select check-types-types k-parts))
(define-type k-region (select check-types-types k-region))
(define-type k-size (select check-types-types k-size))
(define check-infer-types (load-module "fx26:check-infer-types.fx"))
(define-type k-solved (select check-infer-types k-solved))
(define-type k-te (select check-types-types k-te))
(define-type kxs (select check-types-types kxs))
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
                       unit))
            (val k-fail-no-arm
                 (subr (maxeff (alloc @t)
                               (goto @z)
                               (read @globals)
                               (read @s)
                               (read @t)
                               (write @t)
                               spin)
                       (k-parts kx)
                       void))
            (val k-note-apply-shares
                 (subr (maxeff (alloc @t)
                               (goto @z)
                               (read @globals)
                               (read @s)
                               (read @t)
                               (write @t)
                               spin)
                       (kx kx k-ids)
                       unit))
            (val k-partial-pair-arg
                 (subr (maxeff (alloc @t)
                               (goto @z)
                               (read @globals)
                               (read @s)
                               (read @t)
                               (write @t)
                               spin)
                       (kx (arrayof int @t) k-ids k-binders k-solved)
                       unit))
            (val k-te-masked
                 (subr (maxeff (alloc @t) (read @globals) (read @t) (write @t) spin)
                       (kx int k-eff)
                       k-te))
            (val k-masked
                 (subr (maxeff (alloc @t) (read @globals) (read @t) (write @t) spin)
                       (kx k-te)
                       k-te))
            (val k-te-onto
                 (subr (maxeff (alloc @t) (read @globals) (read @t) spin)
                       (k-te k-types-eff)
                       k-types-eff))
            (val k-as-expected
                 (subr (maxeff (alloc @t)
                               (goto @z)
                               (read @globals)
                               (read @s)
                               (read @t)
                               (write @t)
                               spin)
                       (kx k-te int)
                       k-eff))
            (val k-new-subr
                 (subr (maxeff (alloc @t) (read @globals) (read @t) (write @t) spin)
                       (k-eff k-ids int)
                       int))
            (val k-nlist-te
                 (subr (maxeff (alloc @t) (read @globals) (read @t) (write @t) spin)
                       (int k-size k-region k-eff)
                       k-te))
            (val k-bind-place
                 (subr (maxeff (alloc @t) (read @globals) (read @t) (write @t) spin)
                       (int)
                       unit))
            (val k-region-form (subr pure (int) string))
            (val k-note-extract
                 (subr (maxeff (alloc @t) (read @globals) (read @t) (write @t))
                       (int int int)
                       unit))
            (val k-projected
                 (subr (maxeff (alloc @t)
                               (goto @z)
                               (read @globals)
                               (read @s)
                               (read @t)
                               (write @t)
                               spin)
                       (k-binders (listof k-desc acyclic) int int int)
                       int))
            (val k-join-branches
                 (subr (maxeff (alloc @t)
                               (goto @z)
                               (read @globals)
                               (read @s)
                               (read @t)
                               (write @t)
                               spin)
                       (int int int int)
                       int))
            (val k-path-te
                 (subr (maxeff (alloc @t) (read @globals) (read @t) spin) (kx k-te) k-te))
            (val k-kill-paths
                 (subr (maxeff (alloc @t) (read @globals) (read @t) (write @t) spin)
                       (k-eff)
                       unit))
            (val k-enter-then
                 (subr (maxeff (alloc @t) (read @globals) (read @t) (write @t) spin)
                       (kx)
                       k-tested))
            (val k-enter-else
                 (subr (maxeff (alloc @t) (read @globals) (read @t) (write @t))
                       (k-tested)
                       unit))
            (val k-leave-test
                 (subr (maxeff (alloc @t) (read @globals) (read @t) (write @t))
                       (k-tested)
                       unit))
            (val k-certified-arg?
                 (subr (maxeff (read @globals) (read @t) spin) (k-named kxs) bool))
            (val k-thunk-lambda? (subr (read @globals) (kx) bool))
            (val k-arg-found
                 (subr (maxeff (alloc @t) (read @globals) (read @t) (write @t))
                       (k-done int int k-eff)
                       unit))
            (val k-arg-unified
                 (subr (maxeff (alloc @t) (read @globals) (read @t) (write @t) spin)
                       (int k-binders k-solved k-done int k-te)
                       unit))
            (val k-as-expected-call
                 (subr (maxeff (alloc @t)
                               (goto @z)
                               (read @globals)
                               (read @s)
                               (read @t)
                               (write @t)
                               spin)
                       (kx k-te int)
                       k-eff))
            (val k-unify-above
                 (subr (maxeff (alloc @t) (read @globals) (read @t) (write @t) spin)
                       (int int k-binders k-solved)
                       unit))
            (val k-solved-instance
                 (subr (maxeff (alloc @t)
                               (goto @z)
                               (read @globals)
                               (read @s)
                               (read @t)
                               (write @t)
                               spin)
                       (k-binders k-solved int int int int)
                       int))
            (val k-bounded-arg
                 (subr (maxeff (alloc @t)
                               (goto @z)
                               (read @globals)
                               (read @s)
                               (read @t)
                               (write @t)
                               spin)
                       (kx int
                           int
                           k-binders
                           k-solved
                           k-done
                           int
                           (subr (maxeff (alloc @t)
                                         (goto @z)
                                         (read @globals)
                                         (read @s)
                                         (read @t)
                                         (write @t)
                                         spin)
                                 (kx int)
                                 k-eff)
                           (subr (maxeff (alloc @t)
                                         (goto @z)
                                         (read @globals)
                                         (read @s)
                                         (read @t)
                                         (write @t)
                                         spin)
                                 (kx)
                                 k-te))
                       unit))
            (val k-poly-var-at
                 (subr (maxeff (alloc @t)
                               (goto @z)
                               (read @globals)
                               (read @s)
                               (read @t)
                               (write @t)
                               spin)
                       (kx int)
                       (listof k-te @t)))
            (val k-nil-told
                 (subr (maxeff (alloc @t)
                               (goto @z)
                               (read @globals)
                               (read @s)
                               (read @t)
                               (write @t)
                               spin)
                       (kx int int int k-binders k-solved k-done)
                       unit))
            (val k-with-used
                 (subr (maxeff (alloc @t) (read @globals) (read @t))
                       (k-parts k-names int)
                       (productof (1 k-parts) (2 k-ids))))
            (val k-widen-nil-tail
                 (subr (maxeff (alloc @t) (read @globals) (read @t) (write @t) spin)
                       (int k-binders k-solved)
                       unit))
            (val k-fx-poly-check
                 (subr (maxeff (alloc @t)
                               (goto @z)
                               (read @globals)
                               (read @s)
                               (read @t)
                               (write @t)
                               spin)
                       (kx symbol kx int)
                       (listof k-eff @t)))
            (val k-literal-within?
                 (subr (maxeff (read @globals) (read @t)) (k-ty int) bool))
            (val k-may-be-empty? (subr (maxeff (read @globals) (read @t)) (k-ty) bool))
            (val k-arms-type
                 (subr (maxeff (alloc @t)
                               (goto @z)
                               (read @globals)
                               (read @s)
                               (read @t)
                               (write @t)
                               spin)
                       (kx k-ids int)
                       int))
            (val k-place-region
                 (subr (maxeff (alloc @t)
                               (goto @z)
                               (read @globals)
                               (read @s)
                               (read @t)
                               (write @t)
                               spin)
                       (int int int)
                       k-region))
            (val k-bloblet-want
                 (subr (maxeff (alloc @t) (read @globals) (read @t) spin)
                       (int kxs k-regions)
                       k-maybe-ty))
            (val k-bloblet-field
                 (subr (maxeff (alloc @t)
                               (goto @z)
                               (read @globals)
                               (read @s)
                               (read @t)
                               (write @t)
                               spin)
                       (int k-ids int int int)
                       int))
            (val k-te-reading
                 (subr (maxeff (alloc @t) (read @globals) (read @t) spin)
                       (int k-region k-eff)
                       k-te))
            (val k-te-writing
                 (subr (maxeff (alloc @t) (read @globals) (read @t) spin)
                       (int k-region k-eff)
                       k-te))
            (val k-handler-callable
                 (subr (maxeff (alloc @t)
                               (goto @z)
                               (read @globals)
                               (read @s)
                               (read @t)
                               (write @t)
                               spin)
                       (kx int int int)
                       k-callable))))
