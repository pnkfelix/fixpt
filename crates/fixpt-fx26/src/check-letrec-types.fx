;;; The types of `check-letrec.fx`, its `check-letrec-module`: a module file of no
;;; state, which it loads, and so may its clients (`TODO.md` §68); its
;;; items in the order they were there.

;; The types these use, from the files that define them.
(hide (define check-types-types (load-module "fx26:check-types-types.fx")))
(import check-types-types (type k-eff k-ids kx) (effect checks))
(hide (define check-resolve-types (load-module "fx26:check-resolve-types.fx")))
(define-type k-letrec-bs (select check-resolve-types k-letrec-bs))
;; What checks one expression against a type, and a group's procedures at
;; their types: `k-check` and `k-check-letrec`, given by `check-synth.fx`.
(define-type k-checker (subr (maxeff checks spin) (kx int) k-eff))
(define-type k-group-checker (subr (maxeff checks spin) (k-letrec-bs) k-eff))
;; One round: the group at types `ts`, and what each was found to read; or
;; none, if a procedure does not check even so.
(define-type k-idss (listof k-ids acyclic))
;; What types a `lambda` told its parameters and result: `k-synth-lambda-as`,
;; given by `check-rules.fx`.
(import check-types-types (type k-te))
(define-type k-lambda-synth (subr (maxeff checks spin) (kx k-ids int) k-te))
(define-type k-eff-list (listof k-eff acyclic))
(define-type k-bools (listof bool acyclic))
(hide (define check-terminate-types (load-module "fx26:check-terminate-types.fx")))
(define-type k-thunk (select check-terminate-types k-thunk))
;; Tarjan's walk (`k-components`): each node's index and low link (-1 not
;; seen yet), whether it is on the stack, the stack, the next index, and
;; the components found, newest first.
(define-type k-walk
  (productof (1 (arrayof int @t)) (2 (arrayof int @t)) (3 (arrayof bool @t)) (4 (ref k-ids @t))
             (5 (ref int @t)) (6 (ref k-idss @t))))
;; What the walk does.
(define-effect k-walks (maxeff (read @globals) (read @t) (write @t) (alloc @t) spin))
;; Why each group noted may not end (`k-spin-why`).
(define-type k-whys (listof (productof (1 symbol) (2 int) (3 string)) acyclic))

;;; ------------------------------------------------------------ signatures

;; What its clients use of it (`check-program.fx`).
;; The types it names, from the files that define them.
(hide (define check-synth-types (load-module "fx26:check-synth-types.fx")))
(define-type k-done (select check-synth-types k-done))
(import check-types-types (type k-named k-names))
(define-type check-letrec-sig
  (moduleof (val k-with-latent
                 (subr (maxeff (alloc @t) (read @globals) (read @t) (write @t) spin)
                       (int k-eff)
                       int))
            (val k-globals-of
                 (subr (maxeff (alloc @t) (read @globals) (read @t)) (k-eff) k-eff))
            (val k-note-ending
                 (subr (maxeff (alloc @t) (read @globals) (read @t) (write @t) spin)
                       (k-letrec-bs string)
                       unit))
            (val k-bind-group
                 (subr (maxeff (alloc @t)
                               (goto @z)
                               (read (globals k-bind-letrec k-letrec-lambdas k-termination))
                               (read @globals)
                               (read @s)
                               (read @t)
                               (write @t)
                               spin)
                       (k-letrec-bs)
                       unit))
            (val k-letrec-checked
                 (subr (maxeff (alloc @t)
                               (goto @z)
                               (read
                                (globals a-read
                                         k-bind-letrec
                                         k-done
                                         k-fail
                                         k-last-latent
                                         k-letrec-lambdas
                                         k-mark
                                         k-one
                                         k-recursive
                                         k-tag
                                         k-te
                                         k-termination
                                         k-unbind-to
                                         r-globals))
                               (read @globals)
                               (read @s)
                               (read @t)
                               (write @t)
                               spin)
                       (k-letrec-bs int k-named k-checker k-group-checker k-lambda-synth)
                       k-eff))
            (val k-arrow-star-latent
                 (subr (maxeff (alloc @t)
                               (goto @z)
                               (read @globals)
                               (read @s)
                               (read @t)
                               (write @t)
                               spin)
                       (k-lambda-synth int kx)
                       k-eff))
            (val k-arrow-star-found
                 (subr (maxeff (alloc @t)
                               (goto @z)
                               (read @globals)
                               (read @s)
                               (read @t)
                               (write @t)
                               spin)
                       (k-lambda-synth k-letrec-bs)
                       k-letrec-bs))
            (val k-reads-one-of? (subr (maxeff (read @globals) (read @t)) (k-names k-eff) bool))
            (val k-any-arrow-star? (subr (maxeff (read @globals) (read @t)) (k-letrec-bs) bool))
            (val k-arrow-star-settle
                 (subr (maxeff (alloc @t) (read @globals) (read @t) (write @t) spin) (int kx) unit))
            (val k-settled-thunk (subr pure (kx int k-checker) k-thunk))
            (val k-settled-or
                 (subr (maxeff (alloc @t)
                               (goto @z)
                               (read @globals)
                               (read @s)
                               (read @t)
                               (write @t)
                               spin)
                       (kx int k-checker)
                       k-eff))))
