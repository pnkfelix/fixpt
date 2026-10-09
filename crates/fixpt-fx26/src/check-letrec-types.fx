;;; The types of `check-letrec.fx`, its `check-letrec-module`: a module file of no
;;; state, which it loads, and so may its clients (`TODO.md` §68); its
;;; items in the order they were there.

;; The types these use, from the files that define them.
(define check-types-types (load-module "fx26:check-types-types.fx"))
(define-effect checks (select check-types-types checks))
(define-type k-eff (select check-types-types k-eff))
(define-type k-ids (select check-types-types k-ids))
(define-type kx (select check-types-types kx))
(define check-resolve-types (load-module "fx26:check-resolve-types.fx"))
(define-type k-letrec-bs (select check-resolve-types k-letrec-bs))
;; What checks one expression against a type, and a group's procedures at
;; their types: `k-check` and `k-check-letrec`, given by `check-synth.fx`.
(define-type k-checker (subr (maxeff checks spin) (kx int) k-eff))
(define-type k-group-checker (subr (maxeff checks spin) (k-letrec-bs) k-eff))
;; One round: the group at types `ts`, and what each was found to read; or
;; none, if a procedure does not check even so.
(define-type k-idss (listof k-ids acyclic))

;;; ------------------------------------------------------------ signatures

;; What its clients use of it (`check-program.fx`).
;; The types it names, from the files that define them.
(define check-synth-types (load-module "fx26:check-synth-types.fx"))
(define-type k-done (select check-synth-types k-done))
(define-type k-named (select check-types-types k-named))
(define-type k-te (select check-types-types k-te))
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
                       (k-letrec-bs int k-named k-checker k-group-checker)
                       k-eff))))
