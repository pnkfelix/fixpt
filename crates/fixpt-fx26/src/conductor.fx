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
  (let* (;; Define-generative, read.
         (check-generative
          ((load-input "fx26:check-generative.fx")
           check-types-module check-holds-module check-env-module check-print-module
           check-read-module check-read-descs-module parser-module))
         ;; Resolving the trees' descriptions.
         (check-resolve
          ((load-input "fx26:check-resolve.fx")
           check-types-module check-subst-module check-effects-module check-env-module
           check-read-module check-syntax-module check-print-module check-read-descs-module
           tables))
         ;; Masking an expression's effect.
         (check-mask
          ((load-input "fx26:check-mask.fx")
           check-types-module check-resolve check-effects-module check-env-module
           check-print-module check-read-module))
         ;; Higher kinds.
         (check-kinds
          ((load-input "fx26:check-kinds.fx")
           check-types-module check-read-descs-module check-holds-module check-print-module
           check-read-helpers-module))
         ;; What its errors say, and where.
         (check-errors
          ((load-input "fx26:check-errors.fx")
           check-types-module check-resolve check-print-module))
         ;; Modules' descriptions read.
         (check-modules-read
          ((load-input "fx26:check-modules-read.fx")
           check-types-module check-resolve check-syntax-module check-read-module
           check-env-module check-read-descs-module check-subst-module parser-module))
         ;; First-class modules' descriptions.
         (check-modules
          ((load-input "fx26:check-modules.fx")
           check-types-module check-env-module check-kinds check-print-module
           check-read-module check-holds-module check-subst-module check-read-descs-module
           parser-module check-read-helpers-module))
         ;; The subtype test's memory.
         (check-sub-env
          ((load-input "fx26:check-sub-env.fx")
           check-types-module check-print-module check-effects-module tables parser-module))
         ;; The subtype test.
         (check-subtype
          ((load-input "fx26:check-subtype.fx")
           check-types-module check-resolve check-sub-env check-env-module
           check-print-module check-effects-module check-proving-module check-subst-module
           check-modules))
         ;; The checker, expected types: checking against what is wanted.
         (check-expect
          ((load-input "fx26:check-expect.fx")
           check-types-module check-env-module check-subtype check-print-module
           check-kinds check-resolve check-effects-module check-modules))
         ;; The checker, calls: which may reach their own caller.
         (check-calls
          ((load-input "fx26:check-calls.fx")
           check-types-module check-resolve check-holds-module check-env-module
           check-expect))
         ;; The checker, dependent subroutines: parameters selected from.
         (check-dependent
          ((load-input "fx26:check-dependent.fx")
           check-types-module check-env-module check-modules check-read-descs-module
           check-expect check-holds-module check-subst-module check-read-helpers-module))
         ;; The checker, data: what the data kind admits.
         (check-data
          ((load-input "fx26:check-data.fx")
           check-types-module check-print-module check-expect check-effects-module
           check-subst-module))
         ;; The checker, bounds on type binders.
         (check-bounds
          ((load-input "fx26:check-bounds.fx")
           check-types-module check-subtype))
         ;; The checker, a poly's binders solved, defaulted and bounded.
         (check-binders
          ((load-input "fx26:check-binders.fx")
           check-types-module check-data check-print-module check-env-module
           check-subst-module check-resolve check-expect check-effects-module
           check-modules tables))
         ;; The checker, instantiation and tagcase.
         (check-infer
          ((load-input "fx26:check-infer.fx")
           check-types-module check-resolve check-effects-module check-binders
           check-env-module check-bounds check-print-module check-data
           check-read-descs-module check-kinds check-unions-module check-subtype
           check-holds-module check-expect check-subst-module check-sub-env
           check-read-helpers-module))
         ;; The checker, closing: what a definition leaves solved.
         (check-close
          ((load-input "fx26:check-close.fx")
           check-types-module check-effects-module check-holds-module check-env-module
           check-resolve check-mask check-calls check-print-module
           check-subst-module))
         ;; The checker, size-change graphs of calls.
         (check-sc-graphs
          ((load-input "fx26:check-sc-graphs.fx")
           check-resolve check-env-module check-types-module check-read-module
           check-calls))
         ;; The checker, termination: the graphs closed under composition.
         (check-terminate
          ((load-input "fx26:check-terminate.fx")
           check-types-module check-resolve check-holds-module check-env-module
           check-expect check-sc-graphs check-print-module tables))
         ;; The checker, what tests prove: facts in the type of a test.
         (check-test-facts
          ((load-input "fx26:check-test-facts.fx")
           check-infer check-types-module check-env-module check-terminate
           check-print-module check-calls check-sc-graphs check-binders))
         ;; The checker, letrec: a group's types found and checked.
         (check-letrec
          ((load-input "fx26:check-letrec.fx")
           check-types-module check-expect check-effects-module check-print-module
           check-env-module check-terminate))
         ;; The checker, facts: what the compiler is told.
         (check-facts
          ((load-input "fx26:check-facts.fx")
           check-env-module check-test-facts check-infer check-calls
           check-binders))
         ;; The checker, synthesis: calls, their arguments and type binders.
         (check-synth
          ((load-input "fx26:check-synth.fx")
           check-types-module check-test-facts check-resolve check-env-module
           check-infer check-facts check-print-module check-bounds
           check-expect check-errors check-effects-module check-mask
           check-unions-module check-terminate check-holds-module check-subtype
           check-calls check-subst-module check-binders check-sub-env))
         ;; The checker, a module's order: its items as a letrec*, used only once made.
         (check-modorder
          ((load-input "fx26:check-modorder.fx")
           check-types-module check-resolve check-errors check-env-module
           check-read-module check-expect tables))
         ;; The checker, rules of modules: their items checked as a letrec*.
         (check-module-rules
          ((load-input "fx26:check-module-rules.fx")
           check-types-module check-env-module check-print-module check-errors
           check-modules check-read-module check-modorder check-expect
           check-effects-module check-subtype check-read-descs-module
           check-terminate check-letrec tables check-read-helpers-module))
         ;; The checker, its rules: the one recursive group over expressions.
         (check-rules
          ((load-input "fx26:check-rules.fx")
           check-types-module check-infer check-synth check-errors
           check-resolve check-env-module check-expect check-letrec
           check-dependent check-module-rules check-read-descs-module
           check-proving-module check-test-facts check-close check-print-module
           check-terminate check-modorder check-unions-module check-modules
           check-effects-module check-data check-read-module check-mask
           check-calls check-bounds check-holds-module check-subtype
           check-subst-module check-sc-graphs check-binders check-sub-env
           check-modules-read check-read-helpers-module))
         ;; The checker, its proofs: lemmas proved.
         (check-proofs
          ((load-input "fx26:check-proofs.fx")
           check-types-module check-resolve check-env-module check-calls
           check-generative check-read-descs-module check-errors check-read-module
           check-subtype check-modules check-infer check-terminate
           check-print-module tables parser-module check-sc-graphs check-sub-env
           check-modules-read))
         ;; The checker, its programs: forms checked in order, under redefinition.
         (check-program
          ((load-input "fx26:check-program.fx")
           check-types-module check-syntax-module check-effects-module check-env-module
           check-proofs check-rules check-generative
           check-read-descs-module check-resolve check-errors
           check-terminate check-print-module check-letrec check-read-module
           check-expect check-modules check-modorder check-subst-module
           check-synth check-module-rules check-subtype parser-module check-modules-read))
         ;; The object layout, generated from the heap's table.
         (layout (load-module "fx26:layout.fx"))
         ;; The standard operations, generated from the lowering's table.
         (standard (load-module "fx26:standard.fx"))
         ;; The compiler: its state, words, places and the code it emits.
         (compile
          ((load-input "fx26:compile.fx")
           layout check-resolve check-env-module tables parser-module))
         ;; The compiler, lambda lifting and the standard operations.
         (compile-lift
          ((load-input "fx26:compile-lift.fx")
           compile layout check-resolve check-program tables
           standard check-proofs))
         ;; The compiler, its state: words being made, members, twins, quotations.
         (compile-state
          ((load-input "fx26:compile-state.fx")
           compile compile-lift layout check-resolve
           check-program check-proofs))
         ;; The compiler, its expressions: the recursive group over trees.
         (compile-exps
          ((load-input "fx26:compile-exps.fx")
           compile compile-lift compile-state check-resolve
           check-types-module layout tables))
         ;; The compiler, its plan of a form: what to inline, specialize and unroll.
         (compile-plan
          ((load-input "fx26:compile-plan.fx")
           compile compile-lift compile-exps check-resolve
           check-program tables compile-state check-proofs))
         ;; Register code: its state, the constants known, and the twins made.
         (regcode
          ((load-input "fx26:regcode.fx")
           compile compile-exps compile-lift compile-plan
           check-resolve tables layout standard compile-state))
         ;; Register code, its expressions.
         (regcode-exps
          ((load-input "fx26:regcode-exps.fx")
           regcode compile compile-exps compile-lift
           compile-plan check-resolve tables layout compile-state))
         ;; Register code, its places: registers, frame slots, environments.
         (regcode-places
          ((load-input "fx26:regcode-places.fx")
           regcode compile layout regcode-exps))
         ;; Register code, its helpers.
         (regcode-helpers
          ((load-input "fx26:regcode-helpers.fx")
           regcode compile compile-exps compile-plan
           compile-lift check-resolve regcode-exps layout tables
           regcode-places compile-state))
         ;; Register code for modules: their products, and with.
         (regcode-modules
          ((load-input "fx26:regcode-modules.fx")
           regcode compile layout regcode-exps))
         ;; Register code, its core: the one recursive group over expressions.
         (regcode-core
          ((load-input "fx26:regcode-core.fx")
           regcode compile compile-lift compile-exps
           compile-plan regcode-exps layout regcode-helpers
           regcode-modules regcode-places compile-state))
         ;; Register code, its entry: a lambda as register code, or why none.
         (regcode-entry
          ((load-input "fx26:regcode-entry.fx")
           compile compile-exps compile-plan regcode
           check-resolve regcode-exps regcode-core regcode-helpers
           layout compile-state))
         ;; The twins: register code beside each word.
         (compile-twins
          ((load-input "fx26:compile-twins.fx")
           compile compile-exps compile-plan compile-lift
           regcode-entry compile-state))
         ;; Inlining: what the compiler knows of small global procedures.
         (compile-inline
          ((load-input "fx26:compile-inline.fx")
           compile compile-plan compile-exps tables compile-state))
         ;; The evaluator.
         (eval-values ((load-input "fx26:eval-values.fx") check-types-module))
         (eval-prims ((load-input "fx26:eval-prims.fx") eval-values tables check-types-module))
         (eval-core
          ((load-input "fx26:eval-core.fx")
           eval-values eval-prims check-env-module check-resolve))
         ;; The compiler's loop over a program's forms.
         (compile-programs
          ((load-input "fx26:compile-programs.fx")
           compile compile-exps compile-plan compile-twins
           regcode-exps compile-inline regcode check-resolve tables
           regcode-helpers layout compile-state))
         ;; The assembler, of the encoders and the generated layouts.
         (native
          ((load-input "fx26:native.fx")
           (load-input "fx26:arm64.fx") layout (load-module "fx26:native-layout.fx"))))
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
             (compile-registers! (with regcode-entry compile-registers!))
             (check-defer-reruns! (with check-program check-defer-reruns!))
             (check-lines! (with check-program check-lines!))
             (check-more (with check-program check-more))
             (check-program (with check-program check-program))
             (checked-tops (with check-program checked-tops)))))

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
(define check-defer-reruns! (extract front-end-entries check-defer-reruns!))
(define check-lines! (extract front-end-entries check-lines!))
(define check-more (extract front-end-entries check-more))
(define check-program (extract front-end-entries check-program))
(define checked-tops (extract front-end-entries checked-tops))
