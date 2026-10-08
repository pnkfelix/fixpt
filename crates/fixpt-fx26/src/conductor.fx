;;; The conductor (`TODO.md` §68): each module of the front end made once,
;;; and given the modules it uses. A converted module is a module file whose
;;; `make` takes them, each typed by its signature; the modules of the files
;;; not converted yet are the top-level ones of the files before this.
;;; Last of the front end; what Rust calls of the modules it makes is named
;;; here at top level.

;;; ------------------------------------------------------------ the evaluator

(define eval-values-file (load-module "fx26:eval-values.fx"))
(define eval-values ((with eval-values-file make) check-types-module))
(define eval-prims-file (load-module "fx26:eval-prims.fx"))
(define eval-prims ((with eval-prims-file make) eval-values tables check-types-module))
(define eval-core-file (load-module "fx26:eval-core.fx"))
(define eval-core
  ((with eval-core-file make) eval-values eval-prims check-env-module check-resolve-module))

;;; ------------------------------------------------------------ for Rust

;; The evaluator's entry points (`syn.rs`, `session.rs`).
(define run-checked (with eval-core run-checked))
(define run-program (with eval-core run-program))
