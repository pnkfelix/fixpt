;;; The types of `check-print.fx`, its `check-print-module`: a module file of no
;;; state, which it loads, and so may its clients (`TODO.md` §68); its
;;; items in the order they were there.

;; The types these use, from the files that define them.
(define check-types-types (load-module "fx26:check-types-types.fx"))
(define-type k-strings (select check-types-types k-strings))
(define check-env-types (load-module "fx26:check-env-types.fx"))
(define-type k-scope (select check-env-types k-scope))
(define-type k-ids (select check-types-types k-ids))
(define-type k-parts (select check-types-types k-parts))
(define-type k-size (select check-types-types k-size))
;; The `define-type`s of a scope by the type each resolves to, made once
;; for a type shown (`k-show-ty`), so that each of its nodes finds its name
;; in a tree, not by resolving every one in scope (`k-abbrev-in`, still for
;; a name an inner one shadows): each node's key, scrambled from its type,
;; the type, its name, and where in the scope it is; the innermost of each.
(define-datatype k-atree (a-leaf) (a-node int int symbol int k-atree k-atree))
(define-type k-atrees (listof k-atree acyclic))
(define-type k-named-at (listof (productof (1 symbol) (2 int)) acyclic))
;; What the branches being checked have learned about sizes: `lin = 0`
;; (`#t`) or `lin ≥ 0`, newest first.
(define-type k-size-fact (productof (1 k-size) (2 bool)))
;; Fourier–Motzkin, as the Rust checker's `refuted_below` (`src/sizes.rs`),
;; step for step: whether the inequalities in scope, with every size a
;; natural, leave no room for `a ≤ -1`.
(define-type k-lins (listof k-size acyclic))
;; Where a type is being shown: the path to it from the root, newest first,
;; to name cycles by; the names a `moduleof`'s descriptions give what they
;; describe, in the components after them, newest first; and the scope's
;; `define-type`s by type, in a list of one (`k-abbrev-by`), or none.
(define-type k-printing (productof (1 k-ids) (2 k-parts) (3 k-atrees)))
;; `(which P …)`, each `(shape i shape)` or `(not (shape i shape))`.
(define-effect kshows (maxeff (read @globals) (read @t) (alloc @t) spin))

;; What a type is shown as so far: its pieces, the last first, joined
;; once, at the end (`k-pieces-string`), so that each character is written
;; once, not again at each node above it, as appending did; the depths of
;; the nodes met again below (`%d`), each to be written `(mu %d …)`; and how
;; many pieces there are.
(define-type k-shown (productof (1 k-strings) (2 k-ids) (3 int)))
(define-type k-atree-of-scope (productof (1 k-scope) (2 int) (3 k-atree)))

;;; ------------------------------------------------------------ signatures

;; What its clients use of it (`check-program.fx`).
;; The types it names, from the files that define them.
(define-type k-atom (select check-types-types k-atom))
(define-type k-eff (select check-types-types k-eff))
;; The types it names, from the files that define them.
(define-type k-conv (select check-types-types k-conv))
;; The types it names, from the files that define them.
(define-type k-map (select check-types-types k-map))
(define-type check-print-sig
  (moduleof (val k-globals-atom? (subr (read @globals) (k-atom) bool))
            (val k-show-effect (subr (maxeff (read @globals) (read @t)) (k-eff) string))
            (val k-keep-atree!
                 (subr (maxeff (alloc @t) (read @globals) (read @t) (write @t) spin)
                       ()
                       unit))
            (val k-show-ty
                 (subr (maxeff (alloc @t) (read @globals) (read @t) spin) (int) string))
            (val k-conv=? (subr (read @globals) (k-conv k-conv) bool))
            (val k-size-plus (subr (read @globals) (k-size int) k-size))
            (val k-size-nonneg? (subr (maxeff (read @globals) (read @t)) (k-size) bool))
            (val k-dvar-string (subr (maxeff (read @globals) (read @t)) (int) string))
            (val k-conv-default (ref k-conv @t))
            (val k-size-lit (subr (read @globals) (int) k-size))
            (val k-map-find (subr (maxeff (read @globals) (read @t)) (k-map int) k-map))
            (val k-size-facts (ref (listof k-size-fact acyclic) @t))
            (val k-size-eq? (subr (maxeff (read @globals) (read @t)) (k-size k-size) bool))
            (val k-size-le? (subr (maxeff (read @globals) (read @t)) (k-size k-size) bool))
            (val k-printing-none k-printing)
            (val k-show-list
                 (subr (maxeff (alloc @t) (read @globals) (read @t) spin)
                       (k-ids k-printing)
                       k-strings))))
