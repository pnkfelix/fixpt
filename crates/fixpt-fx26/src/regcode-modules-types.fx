;;; The types of `regcode-modules.fx`, its `regcode-modules-module`: a module file of no
;;; state, which it loads, and so may its clients (`TODO.md` §68); its
;;; items in the order they were there.

;; The types these use, from the files that define them.
(define compile-types (load-module "fx26:compile-types.fx"))
(define-type cenv (select compile-types cenv))
(define regcode-types (load-module "fx26:regcode-types.fx"))
(define-type renv (select regcode-types renv))
;; Where names are, to register code and to the cellular compiler.
(define-type r-scopes (pairof renv cenv @k))
