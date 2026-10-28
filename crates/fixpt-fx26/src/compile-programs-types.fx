;;; The types of `compile-programs.fx`, its `compile-programs-module`: a module file of no
;;; state, which it loads, and so may its clients (`TODO.md` §68); its
;;; items in the order they were there.

;; The types these use, from the files that define them.
(hide (define compile-exps-types (load-module "fx26:compile-exps-types.fx")))
(define-type c-inlinables (select compile-exps-types c-inlinables))
(hide (define regcode-types (load-module "fx26:regcode-types.fx")))
(import regcode-types (type r-member-const r-module-const rconst))
;; Globals kept for their names' next definitions: a redefinition of a type
;; the old one's users can take, for which the REPL asks
;; (`compile-keep-global!`).
(define-type c-kept-globals (listof (pairof symbol wglobal acyclic) acyclic))
;;; ------------------------------------------------------------- programs

;; What these walk and build (`TODO.md` §42): lists in `@k`, so `spin`.
(define-effect c-lists (maxeff (read @globals) (read @k) (alloc @k) spin))
(define-type c-const-env (listof (pairof symbol rconst @k) @k))
;; Each module's literal members, and one module's.
(define-type c-mconsts (listof r-module-const @k))
(define-type c-members (listof r-member-const @k))
;; Each top-level module's members noted (`c-module-members`), by its
;; global, as the Rust compiler's `modules` (`TODO.md` §38).
(define-type c-module-list (listof (tupof (1 symbol) (2 c-inlinables)) acyclic))
