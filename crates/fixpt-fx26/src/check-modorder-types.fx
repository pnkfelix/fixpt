;;; The types of `check-modorder.fx`, its `check-modorder-module`: a module file of no
;;; state, which it loads, and so may its clients (`TODO.md` §68); its
;;; items in the order they were there.

;; The types these use, from the files that define them.
(define check-resolve-types (load-module "fx26:check-resolve-types.fx"))
(define-type k-letrec-bs (select check-resolve-types k-letrec-bs))
(define check-types-types (load-module "fx26:check-types-types.fx"))
(define-type k-names (select check-types-types k-names))
(define-type kx (select check-types-types kx))
(define table-types (load-module "fx26:table-types.fx"))
(define-type table (select table-types table))
;; Reading the checker's tables and making lists.
(define-effect kallocs (maxeff (read @globals) (alloc @t)))
;; A module's typed lambda: its name, written type, value, the item it is
;; written in, whether that is a `define-rec`, and whether a `define*`.
(define-type k-mlam (productof (1 symbol) (2 int) (3 kx) (4 int) (5 bool) (6 bool)))
(define-type k-mlams (listof k-mlam acyclic))
;; A name a module defines, and the item defining it.
(define-type k-places (listof (productof (1 symbol) (2 int)) acyclic))
;;; ------------------------------------------------------------ hazards

;; What has been reached: each name, the one it was reached from, and
;; whether it was.
(define-type k-reached (listof (productof (1 symbol) (2 symbol) (3 bool)) acyclic))
;; The module (its places and typed lambdas) and the item being checked:
;; its position, name and value.
(define-type k-hz (productof (1 k-places) (2 k-mlams) (3 int) (4 symbol) (5 kx)))
;; Each lambda's name, and the lambdas its value names.
(define-type k-edges (listof (productof (1 symbol) (2 k-names)) acyclic))
;; The lambdas' strongly connected components (Tarjan's): each lambda's
;; place in the walk, its low link, and its component, by name; the walk's
;; stack, and the counts of places and of components. A lambda walked and
;; not yet in a component is on the stack. Linear in the lambdas and their
;; edges, where reaching from each lambda in turn was cubic, with lists.
(define-type k-scc-ints (table symbol int @t))
;; Each of `ls`'s recursive group (`k-mod-group`), in order.
(define-type k-groups (listof k-letrec-bs acyclic))

;;; ------------------------------------------------------------ signatures

;; What its clients use of it (`check-program.fx`).
(define-type check-modorder-sig
  (moduleof (val k-names-onto
                 (subr (maxeff (alloc @t) (read @globals)) (k-names k-names) k-names))))
