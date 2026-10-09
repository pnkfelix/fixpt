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
(define-type check-letrec-sig
  (moduleof (val k-with-latent
                 (subr (maxeff (alloc @t) (read @globals) (read @t) (write @t) spin)
                       (int k-eff)
                       int))
            (val k-globals-of
                 (subr (maxeff (alloc @t) (read @globals) (read @t)) (k-eff) k-eff))))
