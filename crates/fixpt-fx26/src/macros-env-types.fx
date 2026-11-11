;;; The environments the expander's walk resolves names in, abstract
;;; (`TODO.md` §234): the levels an environment is made of, and the
;;; operations every part of the expander uses on one, which each
;;; implementation gives, its `env` abstract outside it: `macros-env-list.fx`,
;;; the levels as a list, innermost first; `macros-env-indexed.fx`, each
;;; import's ribs one level indexed by name. `macros-nodes.fx` loads one
;;; (and says the operations). A module file of no state.

(module-parameters ((rs region) (re region) (rm region) (rc region) (rp region)))
(define types-module ((proj (load-module "fx26:macros-types.fx") rs re rm rc rp)))
(import types-module (type atms))

;; One level of an environment: a rib, or a pattern variable's ribcage; or,
;; in a repeated element of a ribcage's list, what the repetitions before
;; it bound, which its own binders' names cannot tell from its own
;; (`macros-scopes.fx`).
;; Or, in a program's walk, what the module at a node gives (`bind-shape`),
;; whose names the walk does not know: a name looked for past it may be one
;; of them (`macros.rs`'s `Level::Shape`).
(define-datatype level (lv-rib atms) (lv-cage symbol) (lv-earlier atms) (lv-shape int))
(define-type levels (listof level acyclic))
;; The name of the binder at a node, in a list of one; none if the node is
;; no binder (`macros-nodes.fx`'s `binder-name`).
(define-type namer (subr (maxeff (read @globals) spin (read rs)) (int) (listof symbol acyclic)))
;; What a name is found as, looked for from a place in an environment
;; (`env-lookup`): `(0 b next)`, binder `b`, of a rib or of what earlier
;; repetitions bound; `(1 m next)`, the module at node `m`, met first, whose
;; names may include it, looked past from `next`; `(-1 -1 next)`, nothing.
;; A ribcage binds no name a program's walk looks for: passed.
(define-type looked (tupleof int int int))
