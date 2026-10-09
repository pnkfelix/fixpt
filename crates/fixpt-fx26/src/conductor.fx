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
  (let* (;; Hash tables, a module file of no state.
         (tables (load-module "fx26:table.fx"))
         ;; The checker's first file.
         (check-types ((load-input "fx26:check-types.fx") tables))
         ;; Effects.
         (check-effects ((load-input "fx26:check-effects.fx") check-types))
         ;; Its environment.
         (check-env ((load-input "fx26:check-env.fx") check-types tables))
         ;; The pieces of types and effects as shown.
         (check-print-parts
          ((load-input "fx26:check-print-parts.fx")
           check-types check-effects check-env))
         ;; Types and effects shown as the Rust checker shows them.
         (check-print
          ((load-input "fx26:check-print.fx")
           check-types check-print-parts check-env))
         ;; Unions.
         (check-unions
          ((load-input "fx26:check-unions.fx")
           check-types check-print check-env))
         ;; What a type holds.
         (check-holds
          ((load-input "fx26:check-holds.fx")
           check-types check-effects check-env check-print tables
           check-print-parts))
         ;; Syntax read.
         (check-read
          ((load-input "fx26:check-read.fx")
           check-types check-effects check-print check-env
           parser-module check-print-parts))
         ;; What reading descriptions from their syntax needs.
         (check-syntax
          ((load-input "fx26:check-syntax.fx")
           check-types check-read check-unions check-print
           check-effects check-env check-holds parser-module
           check-print-parts))
         ;; Substitution.
         (check-subst
          ((load-input "fx26:check-subst.fx")
           check-types check-effects check-holds check-read
           check-print check-env tables parser-module check-print-parts))
         ;; What a test proves.
         (check-proving
          ((load-input "fx26:check-proving.fx")
           check-types check-env check-read check-syntax
           parser-module))
         ;; What reading types uses that reads none of them.
         (check-read-helpers
          ((load-input "fx26:check-read-helpers.fx")
           check-types check-read check-env check-subst
           check-print check-syntax check-effects parser-module
           check-print-parts))
         ;; Reading types, one knot.
         (check-read-descs
          ((load-input "fx26:check-read-descs.fx")
           check-types check-read-helpers check-syntax check-read
           check-subst check-env check-print check-holds
           check-proving check-effects check-unions parser-module check-print-parts))
         ;; Define-generative, read.
         (check-generative
          ((load-input "fx26:check-generative.fx")
           check-types check-holds check-env check-print
           check-read check-read-descs parser-module check-print-parts))
         ;; Resolving the trees' descriptions.
         (check-resolve
          ((load-input "fx26:check-resolve.fx")
           check-types check-subst check-effects check-env
           check-read check-syntax check-print check-read-descs
           tables check-print-parts))
         ;; Masking an expression's effect.
         (check-mask
          ((load-input "fx26:check-mask.fx")
           check-types check-resolve check-effects check-env
           check-print check-read check-print-parts))
         ;; Higher kinds.
         (check-kinds
          ((load-input "fx26:check-kinds.fx")
           check-types check-read-descs check-holds check-print
           check-read-helpers check-print-parts))
         ;; What its errors say, and where.
         (check-errors
          ((load-input "fx26:check-errors.fx")
           check-types check-resolve check-print check-print-parts))
         ;; Modules' descriptions read.
         (check-modules-read
          ((load-input "fx26:check-modules-read.fx")
           check-types check-resolve check-syntax check-read
           check-env check-read-descs check-subst parser-module))
         ;; First-class modules' descriptions.
         (check-modules
          ((load-input "fx26:check-modules.fx")
           check-types check-env check-kinds check-print
           check-read check-holds check-subst check-read-descs
           parser-module check-read-helpers check-print-parts))
         ;; The subtype test's memory.
         (check-sub-env
          ((load-input "fx26:check-sub-env.fx")
           check-types check-print check-effects tables parser-module
           check-print-parts))
         ;; The subtype test.
         (check-subtype
          ((load-input "fx26:check-subtype.fx")
           check-types check-resolve check-sub-env check-env
           check-print check-effects check-proving check-subst
           check-modules check-print-parts))
         ;; The checker, expected types: checking against what is wanted.
         (check-expect
          ((load-input "fx26:check-expect.fx")
           check-types check-env check-subtype check-print
           check-kinds check-resolve check-effects check-modules check-print-parts))
         ;; The checker, calls: which may reach their own caller.
         (check-calls
          ((load-input "fx26:check-calls.fx")
           check-types check-resolve check-holds check-env
           check-expect))
         ;; The checker, dependent subroutines: parameters selected from.
         (check-dependent
          ((load-input "fx26:check-dependent.fx")
           check-types check-env check-modules check-read-descs
           check-expect check-holds check-subst check-read-helpers))
         ;; The checker, data: what the data kind admits.
         (check-data
          ((load-input "fx26:check-data.fx")
           check-types check-print check-expect check-effects
           check-subst check-print-parts))
         ;; The checker, bounds on type binders.
         (check-bounds
          ((load-input "fx26:check-bounds.fx")
           check-types check-subtype))
         ;; The checker, a poly's binders solved, defaulted and bounded.
         (check-binders
          ((load-input "fx26:check-binders.fx")
           check-types check-data check-print check-env
           check-subst check-resolve check-expect check-effects
           check-modules tables check-print-parts))
         ;; The checker, instantiation and tagcase.
         (check-infer
          ((load-input "fx26:check-infer.fx")
           check-types check-resolve check-effects check-binders
           check-env check-bounds check-print check-data
           check-read-descs check-kinds check-unions check-subtype
           check-holds check-expect check-subst check-sub-env
           check-read-helpers check-print-parts))
         ;; The checker, closing: what a definition leaves solved.
         (check-close
          ((load-input "fx26:check-close.fx")
           check-types check-effects check-holds check-env
           check-resolve check-mask check-calls check-print
           check-subst check-print-parts))
         ;; The checker, size-change graphs of calls.
         (check-sc-graphs
          ((load-input "fx26:check-sc-graphs.fx")
           check-resolve check-env check-types check-read
           check-calls))
         ;; The checker, termination: the graphs closed under composition.
         (check-terminate
          ((load-input "fx26:check-terminate.fx")
           check-types check-resolve check-holds check-env
           check-expect check-sc-graphs check-print tables))
         ;; The checker, what tests prove: facts in the type of a test.
         (check-test-facts
          ((load-input "fx26:check-test-facts.fx")
           check-infer check-types check-env check-terminate
           check-print check-calls check-sc-graphs check-binders check-print-parts))
         ;; The checker, letrec: a group's types found and checked.
         (check-letrec
          ((load-input "fx26:check-letrec.fx")
           check-types check-expect check-effects check-print
           check-env check-terminate check-print-parts))
         ;; The checker, facts: what the compiler is told.
         (check-facts
          ((load-input "fx26:check-facts.fx")
           check-env check-test-facts check-infer check-calls
           check-binders))
         ;; The checker, synthesis: calls, their arguments and type binders.
         (check-synth
          ((load-input "fx26:check-synth.fx")
           check-types check-test-facts check-resolve check-env
           check-infer check-facts check-print check-bounds
           check-expect check-errors check-effects check-mask
           check-unions check-terminate check-holds check-subtype
           check-calls check-subst check-binders check-sub-env check-print-parts))
         ;; The checker, a module's order: its items as a letrec*, used only once made.
         (check-modorder
          ((load-input "fx26:check-modorder.fx")
           check-types check-resolve check-errors check-env
           check-read check-expect tables))
         ;; The checker, rules of modules: their items checked as a letrec*.
         (check-module-rules
          ((load-input "fx26:check-module-rules.fx")
           check-types check-env check-print check-errors
           check-modules check-read check-modorder check-expect
           check-effects check-subtype check-read-descs
           check-terminate check-letrec tables check-read-helpers check-print-parts))
         ;; The checker, its rules: the one recursive group over expressions.
         (check-rules
          ((load-input "fx26:check-rules.fx")
           check-types check-infer check-synth check-errors
           check-resolve check-env check-expect check-letrec
           check-dependent check-module-rules check-read-descs
           check-proving check-test-facts check-close check-print
           check-terminate check-modorder check-unions check-modules
           check-effects check-data check-read check-mask
           check-calls check-bounds check-holds check-subtype
           check-subst check-sc-graphs check-binders check-sub-env
           check-modules-read check-read-helpers check-print-parts))
         ;; The checker, its proofs: lemmas proved.
         (check-proofs
          ((load-input "fx26:check-proofs.fx")
           check-types check-resolve check-env check-calls
           check-generative check-read-descs check-errors check-read
           check-subtype check-modules check-infer check-terminate
           check-print tables parser-module check-sc-graphs check-sub-env
           check-modules-read))
         ;; The checker, its programs: forms checked in order, under redefinition.
         (check-program
          ((load-input "fx26:check-program.fx")
           check-types check-syntax check-effects check-env
           check-proofs check-rules check-generative
           check-read-descs check-resolve check-errors
           check-terminate check-print check-letrec check-read
           check-expect check-modules check-modorder check-subst
           check-synth check-module-rules check-subtype parser-module check-modules-read
           check-print-parts))
         ;; The object layout, generated from the heap's table.
         (layout (load-module "fx26:layout.fx"))
         ;; The standard operations, generated from the lowering's table.
         (standard (load-module "fx26:standard.fx"))
         ;; The compiler: its state, words, places and the code it emits.
         (compile
          ((load-input "fx26:compile.fx")
           layout check-resolve check-env tables parser-module))
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
           check-types layout tables))
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
         (eval-values ((load-input "fx26:eval-values.fx") check-types))
         (eval-prims ((load-input "fx26:eval-prims.fx") eval-values tables check-types))
         (eval-core
          ((load-input "fx26:eval-core.fx")
           eval-values eval-prims check-env check-resolve))
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
             (checked-tops (with check-program checked-tops))
             (check-conv-native! (with check-print-parts check-conv-native!))
             (check-globals-effects! (with check-env check-globals-effects!))
             (checked-effects (with check-env checked-effects))
             (checked-extracts (with check-env checked-extracts))
             (checked-reshapes! (with check-env checked-reshapes!))
             (checked-withs! (with check-env checked-withs!))
             (k-ok (with check-types k-ok))
             (k-err (with check-types k-err))
             (k-done (with check-types k-done)))))

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
(define check-conv-native! (extract front-end-entries check-conv-native!))
(define check-globals-effects! (extract front-end-entries check-globals-effects!))
(define checked-effects (extract front-end-entries checked-effects))
(define checked-extracts (extract front-end-entries checked-extracts))
(define checked-reshapes! (extract front-end-entries checked-reshapes!))
(define checked-withs! (extract front-end-entries checked-withs!))
(define k-ok (extract front-end-entries k-ok))
(define k-err (extract front-end-entries k-err))
(define k-done (extract front-end-entries k-done))
