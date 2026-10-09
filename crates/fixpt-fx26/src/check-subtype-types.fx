;;; The types of `check-subtype.fx`, its `check-subtype-module`: a module file of no
;;; state, which it loads, and so may its clients (`TODO.md` §68); its
;;; items in the order they were there.

;; The types these use, from the files that define them.
(define check-types-types (load-module "fx26:check-types-types.fx"))
(define-effect checks (select check-types-types checks))
(define-type k-eff (select check-types-types k-eff))
(define-type k-hyps (select check-types-types k-hyps))
(define-type k-te (select check-types-types k-te))
(define-type k-ty (select check-types-types k-ty))
(define-effect kstate (select check-types-types kstate))
(define check-subst-types (load-module "fx26:check-subst-types.fx"))
(define-type k-pairs (select check-subst-types k-pairs))
(define-type k-trail (ref k-pairs @t))
;; A subtype question's binder environment, for one side: each `poly`
;; binder in scope, by the name its pair of binders was given, so bodies are
;; compared as they are, not substituted, and a cycle through a `poly` comes
;; back to a pair, and an environment, already on the trail.
(define-type k-benv k-pairs)
;; Both sides' environments.
(define-type k-benvs (pairof k-benv k-benv @t))
;; What one subtype question remembers: the pairs assumed (FX-87's trail),
;; each with the environments it was asked under; and the names given to
;; pairs of `poly` binders, by the pair of nodes and the position.
(define-type k-assumed (listof (productof (1 int) (2 int) (3 k-benv) (4 k-benv)) acyclic))
(define-type k-strail (ref k-assumed @t))
(define-type k-label-entry (productof (1 int) (2 int) (3 int) (4 int)))
(define-type k-label-list (listof k-label-entry acyclic))
(define-type k-labels (ref k-label-list @t))
;; Each lemma that fits a pair of types: its hypotheses, instantiated.
(define-type k-instances (listof k-hyps acyclic))
;; Modules' types compared, by `check-module-rules.fx`, which sets this.
(define-type k-sub-rule
  (subr (maxeff kstate spin) (int int k-ty k-ty k-benv k-benv k-strail k-labels) bool))
;; A computation checked, and what makes a message of W and G.
(define-type k-checking (subr (maxeff checks spin) () k-te))
(define-type k-saying (subr (maxeff checks spin) (string string string) string))
;; The latent effect of `t`, a `subr` under any `poly`s, in a list; or none.
(define-type k-effs (listof k-eff acyclic))

;;; ------------------------------------------------------------ signatures

;; What its clients use of it (`check-program.fx`).
;; The types it names, from the files that define them.
(define-type k-parts (select check-types-types k-parts))
(define-type check-subtype-sig
  (moduleof (val k-subtype
                 (subr (maxeff (alloc @t) (read @globals) (read @t) (write @t) spin)
                       (int int)
                       bool))
            (val k-part-find (subr (maxeff (read @globals) (read @t)) (k-parts symbol) int))))
