;;; The signature of `check-sub-env.fx`, its `check-sub-env-module`,
;;; as its clients use it (`TODO.md` §68): a module file of no state.

;;; ------------------------------------------------------------ signatures

;; What its clients use of it (`check-infer.fx`, `check-proofs.fx`,
;; `check-rules.fx`, `check-synth.fx`).
;; The types it names, from the files that define them.
(define check-types-types (load-module "fx26:check-types-types.fx"))
(define-type k-parts (select check-types-types k-parts))
;; The types it names, from the files that define them.
(define check-subtype-types (load-module "fx26:check-subtype-types.fx"))
(define-type k-assumed (select check-subtype-types k-assumed))
(define-type k-benv (select check-subtype-types k-benv))
(define-type k-conv (select check-types-types k-conv))
(define-type k-eff (select check-types-types k-eff))
(define-type k-label-entry (select check-subtype-types k-label-entry))
(define-type k-label-list (select check-subtype-types k-label-list))
(define-type k-labels (select check-subtype-types k-labels))
(define-type k-region (select check-types-types k-region))
(define-type k-strail (select check-subtype-types k-strail))
(define-type check-sub-env-sig
  (moduleof (val k-part-find (subr (maxeff (read @globals) (read @t)) (k-parts symbol) int))
            (val k-base-below? (subr (read @globals) (symbol symbol) bool))
            (val k-bool=? (subr pure (bool bool) bool))
            (val k-benv-var=?
                 (subr (maxeff (read @globals) (read @t)) (int int k-benv k-benv) bool))
            (val k-conv-sub?
                 (subr (maxeff (read @globals) (read @t))
                       (k-conv k-conv k-benv k-benv)
                       bool))
            (val k-conv-same?
                 (subr (maxeff (read @globals) (read @t))
                       (k-conv k-conv k-benv k-benv)
                       bool))
            (val k-benv-set
                 (subr (maxeff (alloc @t) (read @globals) (read @t))
                       (k-benv int int)
                       k-benv))
            (val k-benv-region=?
                 (subr (maxeff (read @globals) (read @t) spin)
                       (k-region k-region k-benv k-benv)
                       bool))
            (val k-benv-frozen-le?
                 (subr (maxeff (read @globals) (read @t) spin)
                       (k-region k-region k-benv k-benv)
                       bool))
            (val k-param-is?
                 (subr (maxeff (read @globals) (read @t) spin) (int int symbol) bool))
            (val k-select-is?
                 (subr (maxeff (read @globals) (read @t) spin) (int symbol symbol) bool))
            (val k-benv-effect
                 (subr (maxeff (alloc @t) (read @globals) (read @t) spin)
                       (k-benv k-eff)
                       k-eff))
            (val k-strail-push
                 (subr (maxeff (alloc @t) (read @globals) (read @t) (write @t))
                       (k-strail int int k-benv k-benv)
                       unit))
            (val k-strail-drop
                 (subr (maxeff (alloc @t) (read @globals) (read @t) (write @t) spin)
                       (k-assumed k-assumed)
                       unit))
            (val k-strail-has?
                 (subr (maxeff (read @globals) (read @t))
                       (k-assumed int int k-benv k-benv)
                       bool))
            (val k-restore
                 (subr (maxeff (alloc @t) (read @globals) (read @t) (write @t) spin)
                       (k-strail k-labels k-assumed k-label-list)
                       unit))
            (val k-label-of? (subr pure (k-label-entry int int int) bool))
            (val k-label
                 (subr (maxeff (alloc @t) (read @globals) (read @t) (write @t))
                       (k-labels int int int)
                       int))))
