;;; The conductor (`TODO.md` §68): each module of the front end made once,
;;; and given the modules it uses. A converted module is a module file whose
;;; `make` takes them, each typed by its signature; the modules of the files
;;; not converted yet are the top-level ones of the files before this.
;;; Last of the front end. The modules are made inside one `let*`, so that
;;; only what Rust calls of them is named at top level: a module bound at
;;; top level has its whole type shown, and the types of modules are large.

(define front-end-entries
  (let* (;; The evaluator.
         (eval-values-file (load-module "fx26:eval-values.fx"))
         (eval-values ((with eval-values-file make) check-types-module))
         (eval-prims-file (load-module "fx26:eval-prims.fx"))
         (eval-prims ((with eval-prims-file make) eval-values tables check-types-module))
         (eval-core-file (load-module "fx26:eval-core.fx"))
         (eval-core
          ((with eval-core-file make)
           eval-values eval-prims check-env-module check-resolve-module)))
    ;; What Rust calls of them (`syn.rs`, `session.rs`).
    (product (run-checked (with eval-core run-checked))
             (run-program (with eval-core run-program)))))

(define run-checked (extract front-end-entries run-checked))
(define run-program (extract front-end-entries run-program))
