;;; The types of `check-test-facts.fx`, its `check-test-facts-module`: a module file of no
;;; state, which it loads, and so may its clients (`TODO.md` §68); its
;;; items in the order they were there.

;; The types these use, from the files that define them.
(define check-types-types (load-module "fx26:check-types-types.fx"))
(define-type k-cert-len (select check-types-types k-cert-len))
(define-type k-props (select check-types-types k-props))
(define-type k-size (select check-types-types k-size))
(define-type kxs (select check-types-types kxs))
(define check-print-types (load-module "fx26:check-print-types.fx"))
(define-type k-size-fact (select check-print-types k-size-fact))
;; What a test shows when it holds, and when not.
(define-type k-fact-list (listof k-size-fact acyclic))
(define-type k-branch-facts (pairof k-fact-list k-fact-list acyclic))
;; A size, or none: none or one.
(define-type k-maybe-size (listof k-size acyclic))
;; If `p` is a call of a procedure whose type's result is `(bool (then …)
;; (else …))`, what it proves where true and where false, and its arguments
;; (none or one): the Rust checker's `latent_props`.
(define-type k-latent (listof (productof (1 k-props) (2 k-props) (3 kxs)) acyclic))
(define-type k-cert-lens (listof k-cert-len acyclic))
