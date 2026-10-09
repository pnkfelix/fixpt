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
  (let* (;; The compiler, its expressions: the recursive group over trees.
         (compile-exps
          ((load-input "fx26:compile-exps.fx")
           compile-module compile-lift-module compile-state-module check-resolve-module
           check-types-module layout-module tables))
         ;; The compiler, its plan of a form: what to inline, specialize and unroll.
         (compile-plan
          ((load-input "fx26:compile-plan.fx")
           compile-module compile-lift-module compile-exps check-resolve-module
           check-program-module tables compile-state-module))
         ;; Register code: its state, the constants known, and the twins made.
         (regcode
          ((load-input "fx26:regcode.fx")
           compile-module compile-exps compile-lift-module compile-plan
           check-resolve-module tables layout-module standard-module compile-state-module))
         ;; Register code, its expressions.
         (regcode-exps
          ((load-input "fx26:regcode-exps.fx")
           regcode compile-module compile-exps compile-lift-module
           compile-plan check-resolve-module tables layout-module compile-state-module))
         ;; Register code, its places: registers, frame slots, environments.
         (regcode-places
          ((load-input "fx26:regcode-places.fx")
           regcode compile-module layout-module regcode-exps))
         ;; Register code, its helpers.
         (regcode-helpers
          ((load-input "fx26:regcode-helpers.fx")
           regcode compile-module compile-exps compile-plan
           compile-lift-module check-resolve-module regcode-exps layout-module tables
           regcode-places compile-state-module))
         ;; Register code for modules: their products, and with.
         (regcode-modules
          ((load-input "fx26:regcode-modules.fx")
           regcode compile-module layout-module regcode-exps))
         ;; Register code, its core: the one recursive group over expressions.
         (regcode-core
          ((load-input "fx26:regcode-core.fx")
           regcode compile-module compile-lift-module compile-exps
           compile-plan regcode-exps layout-module regcode-helpers
           regcode-modules regcode-places compile-state-module))
         ;; Register code, its entry: a lambda as register code, or why none.
         (regcode-entry
          ((load-input "fx26:regcode-entry.fx")
           compile-module compile-exps compile-plan regcode
           check-resolve-module regcode-exps regcode-core regcode-helpers
           layout-module compile-state-module))
         ;; The twins: register code beside each word.
         (compile-twins
          ((load-input "fx26:compile-twins.fx")
           compile-module compile-exps compile-plan compile-lift-module
           regcode-entry compile-state-module))
         ;; Inlining: what the compiler knows of small global procedures.
         (compile-inline
          ((load-input "fx26:compile-inline.fx")
           compile-module compile-plan compile-exps tables compile-state-module))
         ;; The evaluator.
         (eval-values ((load-input "fx26:eval-values.fx") check-types-module))
         (eval-prims ((load-input "fx26:eval-prims.fx") eval-values tables check-types-module))
         (eval-core
          ((load-input "fx26:eval-core.fx")
           eval-values eval-prims check-env-module check-resolve-module))
         ;; The compiler's loop over a program's forms.
         (compile-programs
          ((load-input "fx26:compile-programs.fx")
           compile-module compile-exps compile-plan compile-twins
           regcode-exps compile-inline regcode check-resolve-module tables
           regcode-helpers layout-module compile-state-module))
         ;; The assembler, of the encoders and the generated layouts.
         (native
          ((load-input "fx26:native.fx")
           (load-input "fx26:arm64.fx") layout-module (load-module "fx26:native-layout.fx"))))
    ;; What Rust and `bootstrap.fx` call of them (`syn.rs`, `session.rs`).
    (product (run-checked (with eval-core run-checked))
             (run-program (with eval-core run-program))
             (native-assemble (with native native-assemble))
             (compile-forget-globals! (with compile-programs compile-forget-globals!))
             (compile-keep-global! (with compile-programs compile-keep-global!))
             (compile-new-global (with compile-programs compile-new-global))
             (compile-global-cell (with compile-programs compile-global-cell))
             (compile-checked (with compile-programs compile-checked))
             (compile-program (with compile-programs compile-program))
             (compile-note-inline! (with compile-inline compile-note-inline!))
             (compile-registers! (with regcode-entry compile-registers!)))))

(define run-checked (extract front-end-entries run-checked))
(define run-program (extract front-end-entries run-program))
(define native-assemble (extract front-end-entries native-assemble))
(define compile-forget-globals! (extract front-end-entries compile-forget-globals!))
(define compile-keep-global! (extract front-end-entries compile-keep-global!))
(define compile-new-global (extract front-end-entries compile-new-global))
(define compile-global-cell (extract front-end-entries compile-global-cell))
(define compile-checked (extract front-end-entries compile-checked))
(define compile-program (extract front-end-entries compile-program))
(define compile-note-inline! (extract front-end-entries compile-note-inline!))
(define compile-registers! (extract front-end-entries compile-registers!))
