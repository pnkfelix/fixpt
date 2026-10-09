;;; The types of `check-resolve.fx`, its `check-resolve-module`: a module file of no
;;; state, which it loads, and so may its clients (`TODO.md` §68); its
;;; items in the order they were there.

;; The types these use, from the files that define them.
(define parser-types ((proj (load-module "fx26:parser-types.fx") @s @e @m @c @p)))
(define-type exp (select parser-types exp))
(define-type names (select parser-types names))
(define-type syn (select parser-types syn))
(define-type top (select parser-types top))
(define check-types-types (load-module "fx26:check-types-types.fx"))
(define-type k-eff (select check-types-types k-eff))
(define-type k-ids (select check-types-types k-ids))
(define-type k-names (select check-types-types k-names))
(define-type k-regions (select check-types-types k-regions))
(define-type kx (select check-types-types kx))
;; The parts of a resolved tree, as `kx`'s constructors hold them: a
;; `lambda`'s parameters, a `letrec`'s and a `let`'s bindings (a product's
;; fields are as a `let`'s), and a `tagcase`'s arms.
(define-type k-typed-params (listof (productof (1 symbol) (2 k-ids)) acyclic))
(define-type k-letrec-bs (listof (productof (1 symbol) (2 int) (3 kx)) acyclic))
(define-type k-let-bs (listof (productof (1 symbol) (2 kx)) acyclic))
(define-type k-arms (listof (productof (1 symbol) (2 bool) (3 k-names) (4 kx)) acyclic))
(define-type exp-letrec-bs (listof (productof (1 symbol) (2 syn) (3 exp)) acyclic))
(define-type exp-let-bs (listof (productof (1 symbol) (2 exp)) acyclic))
(define-type exp-arms (listof (productof (1 symbol) (2 bool) (3 names) (4 exp)) acyclic))
;;; ------------------------------------------------------------ callables

;; What calling a value of type `t` does: its latent effect, parameters and
;; result, as none or one. A composable continuation runs the rest of its
;; prompt's body, with control effects on the tag's region.
(define-type k-callable (productof (1 k-eff) (2 k-ids) (3 int)))
;; Every region mentioned in type `t`, following recursive types once.
;; Kept once found, by type: a type does not change once built.
(define-type k-region-lists (arrayof (listof k-regions acyclic) @t))
;; A definition checked, as a redefinition finds it: the names it defines,
;; its tree, and the globals it uses (its expressions' free variables).
(define-type k-def (productof (1 k-names) (2 top) (3 k-names)))
;; What the program runs, newest first: each top-level form, and the
;; definitions run again for a redefinition, each with whether it assigns
;; its names' globals rather than making new ones.
(define-type k-run (productof (1 top) (2 bool)))

;;; ------------------------------------------------------------ signatures

;; What clients use of `check-resolve.fx`'s module (`TODO.md` §68): the
;; evaluator's.
;; The types it names, from the files that define them.
(define-type k-region (select check-types-types k-region))
;; The types it names, from the files that define them.
(define-type k-descs (select check-types-types k-descs))
;; The types it names, from the files that define them.
(define-type k-binders (select check-types-types k-binders))
(define-type k-map (select check-types-types k-map))
(define-type k-vsub (select check-types-types k-vsub))
;; The types it names, from the files that define them.
(define-type k-items (select check-types-types k-items))
;; The types it names, from the files that define them.
(define check-subst-types (load-module "fx26:check-subst-types.fx"))
(define-type k-pairs (select check-subst-types k-pairs))
(define-type check-resolve-sig
  (moduleof
   (val exp-start (subr pure (exp) int))
   (val exp-end (subr pure (exp) int))
   (val k-has-region-in?
        (subr (maxeff (read @globals) (read @t) spin) (k-regions k-region) bool))
   (val k-defs (ref (listof k-def acyclic) @t))
   (val k-last-uses (ref k-names @t))
   (val k-runs (ref (listof k-run acyclic) @t))
   (val k-reset
        (subr (maxeff (alloc @t) (read @globals) (read @t) (write @t) spin) () unit))
   (val k-free-into
        (subr (maxeff (alloc @t) (read @globals) (read @t)) (kx k-names k-names) k-names))
   (val k-unfold
        (subr (maxeff (alloc @t) (read @globals) (read @t) (write @t) spin)
              (int k-descs)
              int))
   (val k-start (subr pure (kx) int))
   (val k-end (subr pure (kx) int))
   (val k-as-subr
        (subr (maxeff (alloc @t) (read @globals) (read @t) spin)
              (int)
              (listof k-callable acyclic)))
   (val k-vsubr-parts
        (subr (maxeff (alloc @t) (read @globals) (read @t) spin) (int) k-vsub))
   (val k-callee-of
        (subr (maxeff (alloc @t) (read @globals) (read @t) spin)
              (int int)
              (listof k-callable acyclic)))
   (val k-conversion-name (subr (read @globals) (string symbol) symbol))
   (val k-free-vars (subr (maxeff (alloc @t) (read @globals) (read @t)) (kx) k-names))
   (val k-rename
        (subr (maxeff (alloc @t) (read @globals) (read @t) (write @t) spin)
              (k-binders k-binders)
              k-map))
   (val k-items-bound
        (subr (maxeff (alloc @t) (read @globals) (read @t)) (k-items k-names) k-names))
   (val k-regions-in
        (subr (maxeff (alloc @t) (read @globals) (read @t) (write @t) spin) (int) k-regions))
   (val k-ty-rank (subr (maxeff (read @globals) (read @t) spin) (int) int))
   (val k-pair-seen? (subr (maxeff (read @globals) (read @t)) (k-pairs int int) bool))
   (val k-same-kinds? (subr (maxeff (read @globals) (read @t)) (k-binders k-binders) bool))
   (val k-let-names
        (subr (maxeff (alloc @t) (read @globals) (read @t)) (k-let-bs k-names) k-names))))
