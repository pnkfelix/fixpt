;;; The conductor (`TODO.md` §68): each module of the front end made once,
;;; and given the modules it uses. A converted module's file is one
;;; expression (`load-input`), what makes the module of the modules it
;;; takes, each typed by its signature; the modules of the files not
;;; converted yet are the top-level ones of the files before this. Every
;;; load of a file is one value, so loading it here costs nothing more.
;;; Last of the front end. The modules are made inside one `let*`, so that
;;; only what Rust calls of them is named at top level: a module bound at
;;; top level has its whole type shown, and the types of modules are large.

(define front-end-entries
  (let* (;; The evaluator.
         (eval-values ((load-input "fx26:eval-values.fx") check-types-module))
         (eval-prims ((load-input "fx26:eval-prims.fx") eval-values tables check-types-module))
         (eval-core
          ((load-input "fx26:eval-core.fx")
           eval-values eval-prims check-env-module check-resolve-module))
         ;; The assembler, of the encoders and the generated layouts.
         (native
          ((load-input "fx26:native.fx")
           (load-input "fx26:arm64.fx") layout-module (load-module "fx26:native-layout.fx"))))
    ;; What Rust and `bootstrap.fx` call of them (`syn.rs`, `session.rs`).
    (product (run-checked (with eval-core run-checked))
             (run-program (with eval-core run-program))
             (native-assemble (with native native-assemble)))))

(define run-checked (extract front-end-entries run-checked))
(define run-program (extract front-end-entries run-program))
(define native-assemble (extract front-end-entries native-assemble))
