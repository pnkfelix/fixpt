;;; The types of `check-calls.fx`, its `check-calls-module`: a module file of no
;;; state, which it loads, and so may its clients (`TODO.md` §68); its
;;; items in the order they were there.
;; Whether a procedure of type `t` could be given itself: a cycle in `t`
;; runs through a parameter of a procedure (or the argument of a
;; continuation). A type that is merely recursive, as a list is, does not let
;; anything loop. `path`: the nodes on the way down, newest first, each with
;; whether it was reached through a parameter.
(define-type k-cpath (listof (pairof int bool @t) acyclic))

;;; ------------------------------------------------------------ signatures

;; What its clients use of it (`check-proofs.fx`).
;; The types it names, from the files that define them.
(define check-types-types (load-module "fx26:check-types-types.fx"))
(define-type kx (select check-types-types kx))
;; The types it names, from the files that define them.
(define-type kxs (select check-types-types kxs))
(define-type check-calls-sig
  (moduleof (val k-under (subr (read @globals) (kx) kx))
            (val k-callee-name
                 (subr (maxeff (alloc @t) (read @globals)) (kx) (listof symbol acyclic)))
            (val k-std-op (subr (maxeff (read @globals) (read @t) spin) (kx) string))
            (val k-may-spin?
                 (subr (maxeff (alloc @t) (read @globals) (read @t) (write @t) spin)
                       (kx int kxs)
                       bool))))
