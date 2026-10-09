;;; The types of `check-syntax.fx`, its `check-syntax-module`: a module file of no
;;; state, which it loads, and so may its clients (`TODO.md` §68); its
;;; items in the order they were there.

;; The types these use, from the files that define them.
(define check-env-types (load-module "fx26:check-env-types.fx"))
(define-type k-scope (select check-env-types k-scope))
(define parser-types ((proj (load-module "fx26:parser-types.fx") @s @e @m @c @p)))
(define-type syn (select parser-types syn))
(define-type k-slots (listof (pairof int syn @t) acyclic))
;; The type families being expanded, each with the descriptions given it
;; and the slot its type will fill: a use inside with the same descriptions
;; is that slot, a knot (regular recursion).
(define-type k-family-knot (productof (1 symbol) (2 k-scope) (3 int)))
;; `(define-type name type)`: `name` stands for the type from here on, and
;; may appear in its own definition.
;; While a program's types are declared ahead (`k-ahead`): each
;; abbreviation's slot, made before any is read so that they may name each
;; other in any order; and those filled, with where, to check grounded once
;; all are.
(define-type k-ahead-slots (listof (pairof symbol int @t) acyclic))
(define-type k-filled (listof (productof (1 int) (2 int) (3 int)) acyclic))

;;; ------------------------------------------------------------ signatures

;; What its clients use of it (`check-program.fx`).
;; The types it names, from the files that define them.
(define check-types-types (load-module "fx26:check-types-types.fx"))
(define-type k-names (select check-types-types k-names))
(define check-read-types (load-module "fx26:check-read-types.fx"))
(define-type k-syns (select check-read-types k-syns))
;; The types it names, from the files that define them.
(define-type k-conv (select check-types-types k-conv))
(define-type check-syntax-sig
  (moduleof (val k-define-family
                 (subr (maxeff (alloc @t)
                               (goto @z)
                               (read @globals)
                               (read @s)
                               (read @t)
                               (write @t)
                               spin)
                       (symbol k-syns syn)
                       unit))
            (val k-list-head (subr (maxeff (read @globals) (read @s)) (syn) string))
            (val k-ahead-names (ref k-ahead-slots @t))
            (val k-ahead-filled (ref k-filled @t))
            (val k-ahead-declare
                 (subr (maxeff (alloc @t)
                               (goto @z)
                               (read (globals ds-rec k-push-desc k-slot))
                               (read @globals)
                               (read @s)
                               (read @t)
                               (write @t)
                               spin)
                       (k-names k-names)
                       unit))
            (val k-filled-reversed (subr (read @globals) (k-filled k-filled) k-filled))
            (val k-ground-filled
                 (subr (maxeff (alloc @t)
                               (goto @z)
                               (read @globals)
                               (read @s)
                               (read @t)
                               (write @t)
                               spin)
                       (k-filled)
                       unit))
            (val k-parse-conv
                 (subr (maxeff (alloc @t)
                               (goto @z)
                               (read @globals)
                               (read @s)
                               (read @t)
                               (write @t)
                               spin)
                       (syn)
                       k-conv))
            (val k-knots (ref (listof k-family-knot acyclic) @t))))
