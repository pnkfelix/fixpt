;;; The types of `check-print.fx`, its `check-print-module`: a module file of no
;;; state, which it loads, and so may its clients (`TODO.md` §68); its
;;; items in the order they were there.

;; The types these use, from the files that define them.
(define check-types-types (load-module "fx26:check-types-types.fx"))
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
