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
         ;; A session's state, made and read (`readings.fx`).
         (readings ((proj (load-module "fx26:readings.fx") @s @e @m @c)))
         ;; The parser's types, for what a parse gives (`keyed`).
         (parser-types ((proj (load-module "fx26:parser-types.fx") @s @e @m @c @p)))
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
         ;; Specifications' propositions: shown, compared, proved.
         (check-logic
          ((load-input "fx26:check-logic.fx")
           check-types check-print-parts))
         ;; Types and effects shown as the Rust checker shows them.
         (check-print
          ((load-input "fx26:check-print.fx")
           check-types check-print-parts check-env check-logic))
         ;; Unions.
         (check-unions
          ((load-input "fx26:check-unions.fx")
           check-types check-print check-env check-print-parts))
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
         ;; Flat data, which reading types uses.
         (check-flat
          ((load-input "fx26:check-flat.fx")
           check-types check-read check-env check-subst
           check-print check-syntax check-effects parser-module
           check-print-parts))
         ;; What reading types uses that reads none of them.
         (check-read-helpers
          ((load-input "fx26:check-read-helpers.fx")
           check-types check-read check-env check-subst
           check-print check-syntax check-effects parser-module
           check-print-parts check-flat))
         ;; Specifications in procedure types, read.
         (check-specs
          ((load-input "fx26:check-specs.fx")
           check-types check-env check-read check-syntax check-read-helpers
           parser-module))
         ;; The types of the modules files make, read.
         (check-read-made
          ((load-input "fx26:check-read-made.fx")
           check-types check-read-helpers check-read check-subst check-env check-print
           check-holds check-print-parts parser-module))
         ;; Reading types, one knot.
         (check-read-descs
          ((load-input "fx26:check-read-descs.fx")
           check-types check-read-helpers check-syntax check-read
           check-subst check-env check-print check-holds
           check-proving check-effects check-unions parser-module check-print-parts
           check-specs check-read-made))
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
           check-modules check-print-parts check-read-helpers check-logic check-unions))
         ;; The checker, expected types: checking against what is wanted.
         (check-expect
          ((load-input "fx26:check-expect.fx")
           check-types check-env check-subtype check-print
           check-kinds check-resolve check-effects check-modules check-print-parts
           check-read-helpers check-logic))
         ;; The checker, calls: which may reach their own caller.
         (check-calls
          ((load-input "fx26:check-calls.fx")
           check-types check-resolve check-holds check-env
           check-expect check-effects check-modules check-read-helpers))
         ;; The checker, dependent subroutines: parameters selected from.
         (check-dependent
          ((load-input "fx26:check-dependent.fx")
           check-types check-env check-modules check-read-descs
           check-expect check-holds check-subst check-read-helpers))
         ;; The checker, data: what the data kind admits.
         (check-data
          ((load-input "fx26:check-data.fx")
           check-types check-print check-expect check-effects
           check-subst check-print-parts check-sub-env))
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
           check-read-helpers check-print-parts check-calls))
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
           check-calls check-unions check-print-parts))
         ;; The checker, termination: the graphs closed under composition.
         (check-terminate
          ((load-input "fx26:check-terminate.fx")
           check-types check-resolve check-holds check-env
           check-expect check-sc-graphs check-print tables check-subtype))
         ;; The checker, its types as reps (`check-reps.fx`).
         (check-reps ((load-input "fx26:check-reps.fx") check-types check-effects))
         ;; The checker, what tests prove: facts in the type of a test.
         (check-test-facts
          ((load-input "fx26:check-test-facts.fx")
           check-infer check-types check-env check-terminate
           check-print check-calls check-sc-graphs check-binders check-print-parts
           check-logic check-resolve check-subtype check-subst check-reps))
         ;; The checker, letrec: a group's types found and checked.
         (check-letrec
          ((load-input "fx26:check-letrec.fx")
           check-types check-expect check-effects check-print
           check-env check-terminate check-print-parts check-resolve check-close))
         ;; The checker, facts: what the compiler is told.
         (check-facts
          ((load-input "fx26:check-facts.fx")
           check-env check-test-facts check-infer check-calls
           check-binders))
         ;; The checker, blobrefs: their forms' types, and what the compilers
         ;; are told.
         (check-blobrefs
          ((load-input "fx26:check-blobrefs.fx")
           check-types check-env check-print check-read-helpers))
         ;; The checker, synthesis: calls, their arguments and type binders.
         (check-synth
          ((load-input "fx26:check-synth.fx")
           check-types check-test-facts check-resolve check-env
           check-infer check-facts check-print check-bounds
           check-expect check-errors check-effects check-mask
           check-unions check-terminate check-holds check-subtype
           check-calls check-subst check-binders check-sub-env check-print-parts
           check-read-helpers check-blobrefs))
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
         ;; The checker, the rules for processes and `par`.
         (check-processes
          ((load-input "fx26:check-processes.fx")
           check-types check-env check-resolve check-binders check-data
           check-print check-print-parts check-calls check-effects
           check-synth check-subtype check-module-rules))
         ;; The checker, the rules for `allof`.
         (check-allof
          ((load-input "fx26:check-allof.fx")
           check-types check-env check-resolve check-print check-print-parts
           check-effects check-subtype check-synth check-expect check-errors check-unions
           check-calls))
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
           check-modules-read check-read-helpers check-print-parts check-processes
           check-allof check-logic))
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
           check-print-parts check-reps))
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
         ;; The expander told the shapes of the globals `forms` name, as the
         ;; checker has their types (`k-global-shapes`); if `fresh`, the parse
         ;; beginning the standard environment's again, none but the types
         ;; named by reps, `named` (a stage's `%stage-type`).
         (global-shapes
          (lambda ((forms (listof syn acyclic)) (fresh bool)
                   (named (listof (productof (1 symbol) (2 (bytevectorof @t))) acyclic)))
            (if fresh
                ((with shapes-module globals-given!)
                 nil ((with check-program k-named-shapes) named))
                (let ((g ((with check-program k-global-shapes) forms)))
                  ((with shapes-module globals-given!) (extract g 1) (extract g 2))))))
         ;; What the register compiler needs of the keys and expansions the
         ;; expander made since it was last told: each key's template
         ;; place and expansion, each expansion's use site, copied to its
         ;; region (`regcode.fx`'s provenance; `docs/research/macro-provenance.md`).
         (keys-mirrored!
          (lambda ()
            (letrec ((keys (subr (maxeff (alloc @k) (read @k) (write @k) (read @s) (read @globals)
                                         spin)
                                 (int int) unit)
                           (lambda (i n)
                             (if (>= i n)
                                 #u
                                 (let ((s (macro-source (+ 1125899906842624 i))))
                                   (begin ((with regcode r-key-given!) (extract s 1) (extract s 2))
                                          (keys (+ i 1) n))))))
                     (uses (subr (maxeff (alloc @k) (read @k) (write @k) (read @s) (read @globals)
                                         spin)
                                 ((listof (tupleof int symbol int int) acyclic) int) unit)
                           (lambda (xs known)
                             (if (or (null? xs) (< (extract (car xs) 1) known))
                                 #u
                                 (begin (uses (cdr xs) known)
                                        ((with regcode r-use-given!) (extract (car xs) 1)
                                                                     (extract (car xs) 3)))))))
              (begin (keys ((with regcode r-keys-known)) (macro-sources-made))
                     (uses (expansions-made) ((with regcode r-uses-known)))))))
         ;; A parse, and what the checker is told of it: the macros each
         ;; `with`'s body used (`k-macro-uses!`), this parse's alone.
         ;; Before it, the expander told the shapes of the globals the forms
         ;; name, as the checker has their types, if `globals` (in a state
         ;; that goes on from the checker's); else of the types `named` alone
         ;; (`global-shapes`).
         (parse-checked
          (lambda ((keys (select parser-types keys)) (forms (listof syn acyclic)) (globals bool)
                   (named (listof (productof (1 symbol) (2 (bytevectorof @t))) acyclic)))
            (let ((p (begin (global-shapes forms (not globals) named) (parse-program keys forms))))
              (begin ((with check-synth k-macro-uses!) (with-macro-uses)) (keys-mirrored!) p))))
         ;; The evaluator.
         (eval-values ((load-input "fx26:eval-values.fx") check-types))
         (eval-prims ((load-input "fx26:eval-prims.fx") eval-values tables check-types))
         (eval-bloblets ((load-input "fx26:eval-bloblets.fx") eval-values))
         (eval-core
          ((load-input "fx26:eval-core.fx")
           eval-values eval-prims eval-bloblets check-env check-resolve read-text-at
           parse-program))
         ;; The compiler's loop over a program's forms.
         (compile-programs
          ((load-input "fx26:compile-programs.fx")
           compile compile-exps compile-plan compile-twins
           regcode-exps compile-inline regcode check-resolve tables
           regcode-helpers layout compile-state))
         ;; The assembler, of the encoders and the generated layouts.
         (native
          ((load-input "fx26:native.fx")
           (load-input "fx26:arm64.fx") layout (load-module "fx26:native-layout.fx")))
         ;; And register code to arm64, over that assembler: its fast
         ;; paths, then the rest.
         (native-arm64-regs-ops
          ((load-input "fx26:native-arm64-regs-ops.fx")
           (load-input "fx26:arm64.fx") layout (load-module "fx26:native-layout.fx")
           (load-module "fx26:native-arm64-regs-layout.fx") native))
         (native-arm64-regs
          ((load-input "fx26:native-arm64-regs.fx")
           (load-input "fx26:arm64.fx") layout (load-module "fx26:native-layout.fx")
           (load-module "fx26:native-arm64-regs-layout.fx") native native-arm64-regs-ops))
         ;; The same for x86_64.
         (native-x64
          ((load-input "fx26:native-x64.fx")
           (load-input "fx26:x86_64.fx") layout (load-module "fx26:native-x64-layout.fx")))
         ;; And register code to x86_64, over that assembler: its fast
         ;; paths, then the rest.
         (native-x64-regs-ops
          ((load-input "fx26:native-x64-regs-ops.fx")
           (load-input "fx26:x86_64.fx") layout (load-module "fx26:native-x64-layout.fx")
           (load-module "fx26:native-x64-regs-layout.fx") native-x64))
         (native-x64-regs
          ((load-input "fx26:native-x64-regs.fx")
           (load-input "fx26:x86_64.fx") layout (load-module "fx26:native-x64-layout.fx")
           (load-module "fx26:native-x64-regs-layout.fx") native-x64 native-x64-regs-ops))
         ;; The native convention's procedures to x86_64: what the
         ;; convention is, the assembler, where raw values are kept, the
         ;; pieces of raw values and of the heap, the procedure, its
         ;; instructions, and the loop over them.
         (native-direct-layout (load-module "fx26:native-direct-x64-layout.fx"))
         (native-direct-asm
          ((load-input "fx26:native-direct-x64-asm.fx")
           (load-input "fx26:x86_64.fx") native-direct-layout))
         (native-reps ((load-input "fx26:native-reps.fx") native-direct-layout layout))
         (native-direct-raw
          ((load-input "fx26:native-direct-x64-raw.fx")
           (load-input "fx26:x86_64.fx") native-direct-layout native-direct-asm))
         (native-direct-flat
          ((load-input "fx26:native-direct-x64-flat.fx")
           (load-input "fx26:x86_64.fx") native-direct-layout native-direct-asm
           native-direct-raw))
         (native-direct-proc
          ((load-input "fx26:native-direct-x64-proc.fx")
           native-direct-layout layout native-direct-asm native-reps))
         (native-direct-ops
          ((load-input "fx26:native-direct-x64-ops.fx")
           (load-input "fx26:x86_64.fx") native-direct-layout layout native-direct-asm native-reps
           native-direct-raw native-direct-proc))
         (native-direct-prims
          ((load-input "fx26:native-direct-x64-prims.fx")
           (load-input "fx26:x86_64.fx") native-direct-layout layout native-direct-asm native-reps
           native-direct-raw native-direct-flat native-direct-proc))
         (native-direct
          ((load-input "fx26:native-direct-x64.fx")
           (load-input "fx26:x86_64.fx") native-direct-layout layout native-direct-asm native-reps
           native-direct-raw native-direct-proc native-direct-ops native-direct-prims))
         ;; The same to arm64 (`direct.rs`'s `procedure`), where raw values
         ;; are kept as on x86_64 (`native-reps.fx` is of no machine's).
         (native-arm-layout (load-module "fx26:native-direct-arm64-layout.fx"))
         (native-arm-asm
          ((load-input "fx26:native-direct-arm64-asm.fx")
           (load-input "fx26:arm64.fx") native-arm-layout))
         (native-arm-raw
          ((load-input "fx26:native-direct-arm64-raw.fx")
           (load-input "fx26:arm64.fx") native-arm-layout native-arm-asm))
         (native-arm-flat
          ((load-input "fx26:native-direct-arm64-flat.fx")
           (load-input "fx26:arm64.fx") native-arm-layout native-arm-asm))
         (native-arm-proc
          ((load-input "fx26:native-direct-arm64-proc.fx")
           native-arm-layout layout native-arm-asm native-reps))
         (native-arm-ops
          ((load-input "fx26:native-direct-arm64-ops.fx")
           (load-input "fx26:arm64.fx") native-arm-layout layout native-arm-asm native-reps
           native-arm-raw native-arm-proc))
         (native-arm-prims
          ((load-input "fx26:native-direct-arm64-prims.fx")
           (load-input "fx26:arm64.fx") native-arm-layout layout native-arm-asm native-reps
           native-arm-raw native-arm-flat native-arm-proc))
         (native-arm-direct
          ((load-input "fx26:native-direct-arm64.fx")
           (load-input "fx26:arm64.fx") native-arm-layout layout native-arm-asm native-reps
           native-arm-raw native-arm-proc native-arm-ops native-arm-prims))
         ;; `stage` (`docs/research/eval.md`): code a running program gives,
         ;; wrapped as `stage.rs` wraps it, checked by this instance in the
         ;; standard environment alone, and compiled to the word that makes
         ;; the procedure the wrapping is. Or why not, as `stage-failure`
         ;; says it, placed in the code.
         ;; What a text is numbered by (`parser-types.fx`'s `keys`): mode
         ;; `mode`, read in the session's state `s`, under the switches the
         ;; checker is set to now (`checked-settings`), which change what it
         ;; finds.
         (keys-in
          (lambda ((mode int) (s int))
            (product (1 mode) (2 s) (3 ((with check-program checked-settings))))))
         ;; The state a checker begins in, in the standard environment
         ;; `standard`: its trees' reading (`standard-state`), made once for
         ;; each standard environment given.
         (standard-made
          (the (ref (listof (productof (1 (listof syn acyclic)) (2 int)) acyclic) @t) (new nil)))
         (begun
          (lambda ((standard (listof syn acyclic)))
            (let ((made (get standard-made)))
              (if (and (not (null? made)) (eq? (extract (car made) 1) standard))
                  (extract (car made) 2)
                  (let ((s ((with readings standard-state) standard)))
                    (begin (set standard-made (cons (product (1 standard) (2 s)) nil)) s))))))
         ;; How a parse `p` numbered its trees, for the compiler
         ;; (`c-set-facts!`).
         (numbered
          (lambda ((p (select parser-types keyed)) (mode int))
            (product (1 mode) (2 (extract p 3)) (3 (extract p 4)))))
         ;; A refusal as `stage-failure` says it; and place `n` of the text
         ;; checked, in the code, which starts at `k`.
         (fail
          (lambda ((k (sumof (unread unit) (malformed unit) (refused unit) (stale unit)))
                   (m string) (a int) (b int))
            (sum failed (product (kind k) (message m) (start a) (end b)))))
         (clamp (lambda ((n int) (k int) (len int))
                  (let ((at (- n k))) (cond ((< at 0) 0) ((> at len) len) (else at)))))
         (stage-check
          (let* (;; The text checked, its trees `tops`.
                 (checked
                  (lambda ((standard (listof syn acyclic)) (tops (listof top acyclic))
                           (k int) (len int) (native bool) (registers bool)
                           (rep (bytevectorof @t)) (mode int))
                    (begin
                      ((with check-program check-lines!) #f)
                      ((with check-print-parts check-conv-native!) native)
                      ((with compile compile-conv-native!) native)
                      ((with regcode-entry compile-registers!) registers)
                      (let ((out
                             (tagcase ((with check-program check-staged) standard tops rep)
                               (k-err (m a b ok or)
                                 (fail (sum refused #u) m (clamp a k len) (clamp b k len)))
                               (k-done (t) (fail (sum refused #u) "not an expression" 0 len))
                               (k-ok (ls)
                                 (tagcase ((with compile-programs compile-checked)
                                           ((with check-program checked-tops))
                                           ((with check-env checked-extracts))
                                           (product (1 mode) (2 0) (3 nil)))
                                   (c-ok (w) (sum made w))
                                   (c-err (m) (fail (sum refused #u) m 0 len)))))))
                        ;; The stage's bindings undone, the standard
                        ;; environment kept for the next (`check-staged`).
                        (begin ((with check-program check-staged-undo!)) out))))))
            ;; The code wrapped (`stage.rs`'s `wrapped`), `whole`, the code
            ;; `len` characters at `k` of it; and the type it is checked as,
            ;; as a rep, which `whole` names `%stage-type`, if not empty
            ;; (`check-staged-program`). Read in no session's state but the
            ;; standard environment's (`begun`), with `rep` (`with-reps`),
            ;; under its convention, by `mode` (`keys-in`).
            (lambda ((standard (listof syn acyclic)) (whole string) (k int) (len int)
                     (native bool) (registers bool) (rep (bytevectorof @t)) (mode int))
              (let ((read (read-text-at whole 0)))
                (if (null? read)
                    (fail (sum unread #u) "the code is not one whole expression" 0 len)
                    (begin
                      (loaded-files! nil)
                      (includes-given! nil)
                      ((with check-print-parts check-conv-native!) native)
                      (tagcase (let ((s ((with readings with-reps) (begun standard) rep nil)))
                                 (extract (parse-checked (keys-in mode s) (car read) #f
                                                (if (= (bytevector-length rep) 0)
                                                    nil
                                                    (list (product (1 '%stage-type) (2 rep)))))
                                 1))
                        (p-err (m a b)
                          (fail (sum malformed #u) m (clamp a k len) (clamp b k len)))
                        (p-ok (tops) (checked standard tops k len native registers rep mode)))))))))
         ;; A `.fasl`'s definition (`session.rs`'s `run_program_def`), its
         ;; text `whole`, which loads nothing, read by `mode` in the session's
         ;; state `s` (`keys-in`), parsed and checked as `check-more-typed`
         ;; checks it, in one call: its message if refused, else ""; and the
         ;; state after, if the checker kept it, else as it was
         ;; (`docs/research/heap-types.md`, step 5).
         (check-text-typed
          (lambda ((mode int) (s int) (whole string)
                   (named (listof (productof (1 symbol) (2 int)) acyclic)))
            (let ((read (read-text-at whole 0))
                  (said (lambda ((m string) (s int)) (product (1 m) (2 s)))))
              (if (null? read)
                  (said "the definition is not one whole form" s)
                  (begin
                    (loaded-files! nil)
                    (includes-given! nil)
                    ((with check-program check-lines!) #f)
                    (let ((p (parse-checked (keys-in mode s) (car read) #t nil)))
                      (tagcase (extract p 1)
                        (p-err (m a b) (said m s))
                        (p-ok (tops)
                          (tagcase ((with check-program check-more-typed) tops named)
                            (k-err (m a b ok or) (said m s))
                            (else y (said "" (extract p 2))))))))))))
         ;; The state a session's checker is in (this instance's, a session's
         ;; own: `make-session-compiler`), as a step reads its text in it: the
         ;; state after the last step the checker kept, each read in the state
         ;; the one before left, from the first, which begins it again in the
         ;; standard environment's (`begun`; `readings.fx`). Kept with the
         ;; checker's state it stands for.
         (step-state (the (ref int @t) (new 0)))
         ;; A session's step (`sessions26.rs`), checked by this instance's
         ;; checker, which holds the session's definitions, and compiled by
         ;; its compiler, whose globals are the session's: `whole`, the code
         ;; wrapped, read in the session's state `s` (`step-state`), the code
         ;; `len` characters at `k` of it; `how`: 0, the
         ;; first, in the standard environment `standard`, checked alone; 1,
         ;; more, kept, and compiled (if `make`), into the procedure that
         ;; runs it (if `deferred`, a commit's) or the word; 2, tried, not
         ;; kept, the type `name` then has given, as text and as a rep. And
         ;; `rep`, if not empty, the type the code names `%stage-type`
         ;; (`check-more-with`); and `named`, the names its text gives its
         ;; types, each a rep (`set-step-named!`). What each gives, or why
         ;; not, placed in the code.
         (session-step-of
          (lambda ((standard (listof syn acyclic)) (mode int) (s int) (whole string) (k int)
                   (len int) (how int) (name symbol) (make bool) (deferred bool) (native bool)
                   (registers bool) (rep (bytevectorof @t)))
            (let ((read (read-text-at whole 0))
                  (refused (lambda ((m string) (a int) (b int))
                             (fail (sum refused #u) m (clamp a k len) (clamp b k len)))))
              (if (null? read)
                  (fail (sum unread #u) "the code is not one whole expression" 0 len)
                  (begin
                    (loaded-files! nil)
                    (includes-given! nil)
                    ((with check-program check-lines!) #f)
                    ((with check-print-parts check-conv-native!) native)
                    ((with compile compile-conv-native!) native)
                    ((with regcode-entry compile-registers!) registers)
                    ;; The state after is the parse's if the checker keeps the
                    ;; text; a try, or a text refused, leaves it as it was
                    ;; (the standard environment's, where it began).
                    (let* ((p (parse-checked (keys-in mode s) (car read) #t nil))
                           (r (extract p 2)))
                     (tagcase (extract p 1)
                      (p-err (m a b)
                        (fail (sum malformed #u) m (clamp a k len) (clamp b k len)))
                      (p-ok (tops)
                        (cond
                          ((= how 2)
                           (let ((t ((with check-program check-try) tops name rep)))
                             (tagcase (extract t 1)
                               (k-err (m a b ok or) (refused m a b))
                               (else y (sum typed (product (1 (extract t 2)) (2 (extract t 3))))))))
                          ((= how 0)
                           (tagcase ((with check-program check-program) standard tops)
                             (k-err (m a b ok or) (refused m a b))
                             (else y (begin (set step-state r) (sum checked #u)))))
                          (else
                           (tagcase ((with check-program check-more-with) tops rep)
                             (k-err (m a b ok or) (refused m a b))
                             (k-done (t) (refused "not a form" 0 len))
                             (k-ok (ls)
                              (begin
                               (set step-state r)
                               (if (not make)
                                   (sum checked #u)
                                   (let ((runs ((with check-program checked-tops)))
                                         (facts ((with check-env checked-extracts))))
                                     (tagcase (if deferred
                                                  ((with compile-programs compile-checked-deferred)
                                                   runs facts (product (1 mode) (2 0) (3 nil)))
                                                  ((with compile-programs compile-checked)
                                                   runs facts (product (1 mode) (2 0) (3 nil))))
                                       (c-ok (w) (sum made w))
                                       (c-err (m) (refused m k (+ k len)))))))))))))))))))
         (session-step
          (lambda ((standard (listof syn acyclic)) (whole string) (k int) (len int)
                   (how int) (name symbol) (make bool) (deferred bool) (native bool)
                   (registers bool) (rep (bytevectorof @t))
                   (named (listof (productof (1 symbol) (2 (bytevectorof @t))) acyclic))
                   (mode int))
            ;; Read with the types it is checked against (`with-reps`).
            (let* ((s0 (if (= how 0) (begun standard) (get step-state)))
                   (s ((with readings with-reps) s0 rep named)))
              (begin
               (if (= how 0) (set step-state s0) #u)
               ((with check-program set-step-named!) named)
               (let ((out (session-step-of standard mode s whole k len how name make deferred
                                           native registers rep)))
                 (begin ((with check-program set-step-named!) nil) out))))))
         ;; The types of what the checker tells the compiler.
         (stage-env-types (load-module "fx26:check-env-types.fx"))
         ;; A session's code (`sessions.rs`), checked by the checker written
         ;; in Rust, which gives what it found: compiled by this instance,
         ;; whose globals are the session's, to the word that runs it, or,
         ;; `deferred`, that makes the procedure that does (a commit's); or
         ;; why not. Read by `mode` in `s`, the session's state, under
         ;; `settings`, the Rust checker's switches as the checker that
         ;; checked it was set (`sessions.rs`'s `keys`); its facts numbered
         ;; by their place in the walk (`numbered`).
         (session-compile
          (lambda ((mode int) (s int) (settings string) (text string)
                   (facts (select stage-env-types k-facts))
                   (withs (select stage-env-types k-with-list))
                   (reshapes (select stage-env-types k-reshape-list))
                   (native bool) (registers bool) (deferred bool))
            (let ((read (read-text-at text 0)))
              (if (null? read)
                  (sum failed "the code does not read")
                  (begin
                    (loaded-files! nil)
                    (includes-given! nil)
                    (let ((p (parse-checked (product (1 mode) (2 s) (3 settings)) (car read)
                                            #t nil)))
                     (tagcase (extract p 1)
                      (p-err (m a b) (sum failed m))
                      (p-ok (tops)
                        (begin
                          ((with check-env checked-withs!) withs)
                          ((with check-env checked-reshapes!) reshapes)
                          ((with compile compile-conv-native!) native)
                          ((with regcode-entry compile-registers!) registers)
                          (tagcase (if deferred
                                       ((with compile-programs compile-deferred)
                                        tops facts (numbered p mode))
                                       ((with compile-programs compile-program)
                                        tops facts (numbered p mode)))
                            (c-ok (w) (sum made w))
                            (c-err (m) (sum failed m)))))))))))))
    ;; What Rust and `bootstrap.fx` call of them (`syn.rs`, `session.rs`).
    (product (run-checked (with eval-core run-checked))
             (run-checked-more (with eval-core run-checked-more))
             (run-program (with eval-core run-program))
             (native-assemble (with native native-assemble))
             (native-assemble-x64 (with native-x64 native-assemble-x64))
             (native-assemble-x64-regs (with native-x64-regs native-assemble-x64-regs))
             (native-adapter-x64 (with native-x64-regs native-adapter-x64))
             (native-assemble-arm64-regs (with native-arm64-regs native-assemble-arm64-regs))
             (native-adapter-arm64 (with native-arm64-regs native-adapter-arm64))
             (native-compile-x64-proc (with native-direct native-compile-x64-proc))
             (native-compile-arm64-proc (with native-arm-direct native-compile-arm64-proc))
             (compile-forget-globals! (with compile-programs compile-forget-globals!))
             (compile-keep-global! (with compile-programs compile-keep-global!))
             (compile-new-global (with compile-programs compile-new-global))
             (compile-adopt-globals! (with compile-programs compile-adopt-globals!))
             (compile-adopt-broken? (with compile-programs compile-adopt-broken?))
             (compile-name-word! (with compile-programs compile-name-word!))
             (compile-defining! (with compile-programs compile-defining!))
             (compile-global-cell (with compile-programs compile-global-cell))
             (compile-checked (with compile-programs compile-checked))
             (compile-program (with compile-programs compile-program))
             (compile-note-inline! (with compile-inline compile-note-inline!))
             (compile-registers! (with regcode-entry compile-registers!))
             (compile-conv-native! (with compile compile-conv-native!))
             (check-defer-reruns! (with check-program check-defer-reruns!))
             (checked-settings (with check-program checked-settings))
             (check-redefines (with check-program check-redefines))
             (checked-run-names (with check-program checked-run-names))
             (checked-reps (with check-program checked-reps))
             (checked-reps-again (with check-program checked-reps-again))
             (check-hold-breaks! (with check-program check-hold-breaks!))
             (check-lines! (with check-program check-lines!))
             (check-more (with check-program check-more))
             (check-more-typed (with check-program check-more-typed))
             (check-text-typed check-text-typed)
             (import-types (with check-program import-types))
             (check-program (with check-program check-program))
             ;; What the checker is told of the last parse: the macros each
             ;; `with`'s body used (`k-macro-uses!`), for a driver that
             ;; parses, then checks.
             (check-macro-uses!
              (lambda () ((with check-synth k-macro-uses!) (with-macro-uses))))
             ;; What the register compiler is told after a parse: the keys
             ;; and expansions the expander made (`keys-mirrored!`), for a
             ;; driver that parses, then compiles.
             (keys-mirrored! keys-mirrored!)
             ;; What the expander is told before a parse: the shapes of the
             ;; globals the forms name (`global-shapes`), for a driver that
             ;; parses, then checks.
             (check-global-shapes!
              (lambda ((forms (listof syn acyclic)) (fresh bool)) (global-shapes forms fresh nil)))
             (checked-tops (with check-program checked-tops))
             (check-conv-native! (with check-print-parts check-conv-native!))
             (check-globals-effects! (with check-env check-globals-effects!))
             (check-built-in! (with check-env check-built-in!))
             (check-syscalls! (with check-env check-syscalls!))
             (checked-effects (with check-env checked-effects))
             (checked-extracts (with check-env checked-extracts))
             (checked-reshapes! (with check-env checked-reshapes!))
             (checked-withs! (with check-env checked-withs!))
             (k-ok (with check-types k-ok))
             (k-err (with check-types k-err))
             (k-done (with check-types k-done))
             (stage-check stage-check)
             (session-compile session-compile)
             (session-step session-step))))
;;; The end of `front-end-entries`: `make-front-end`, made of its `let*`
;;; again, follows it in the front end (`lib.rs`'s `front_end`).

;; A front end of its own for `stage`, whose checking leaves the
;; program's alone: made when a program first stages code (`stage.rs`).
(define make-stage-check (lambda () (extract (make-front-end) stage-check)))
;; And one for each session on a machine that runs the compilers written in
;; FX-26 (`sessions.rs`): its compiler, whose globals are the session's; how
;; a global is made in it for the driver to fill (the session's module); and
;; how a name's next definition keeps its global (one every use can take).
(define make-session-compiler
  (lambda ()
    (let ((fe (make-front-end)))
      (product (compile (extract fe session-compile)) (global (extract fe compile-new-global))
               (keep (extract fe compile-keep-global!))
               ;; And its checker (`sessions26.rs`): a step; whether re-runs
               ;; wait; whether reading a global is an effect; a global's
               ;; type and users.
               (step (extract fe session-step)) (defer (extract fe check-defer-reruns!))
               (globals-effects (extract fe check-globals-effects!))
               (redefines (extract fe check-redefines))
               ;; And what the last step runs, by name (a session on the
               ;; evaluator, which runs their texts).
               (runs (extract fe checked-run-names))))))

(define run-checked (extract front-end-entries run-checked))
(define run-checked-more (extract front-end-entries run-checked-more))
(define run-program (extract front-end-entries run-program))
(define native-assemble (extract front-end-entries native-assemble))
(define native-assemble-x64 (extract front-end-entries native-assemble-x64))
(define native-assemble-x64-regs (extract front-end-entries native-assemble-x64-regs))
(define native-adapter-x64 (extract front-end-entries native-adapter-x64))
(define native-assemble-arm64-regs (extract front-end-entries native-assemble-arm64-regs))
(define native-adapter-arm64 (extract front-end-entries native-adapter-arm64))
(define native-compile-x64-proc (extract front-end-entries native-compile-x64-proc))
(define native-compile-arm64-proc (extract front-end-entries native-compile-arm64-proc))
(define compile-forget-globals! (extract front-end-entries compile-forget-globals!))
(define compile-keep-global! (extract front-end-entries compile-keep-global!))
(define compile-new-global (extract front-end-entries compile-new-global))
(define compile-adopt-globals! (extract front-end-entries compile-adopt-globals!))
(define compile-adopt-broken? (extract front-end-entries compile-adopt-broken?))
(define compile-name-word! (extract front-end-entries compile-name-word!))
(define compile-defining! (extract front-end-entries compile-defining!))
(define compile-global-cell (extract front-end-entries compile-global-cell))
(define compile-checked (extract front-end-entries compile-checked))
(define compile-program (extract front-end-entries compile-program))
(define compile-note-inline! (extract front-end-entries compile-note-inline!))
(define compile-registers! (extract front-end-entries compile-registers!))
(define compile-conv-native! (extract front-end-entries compile-conv-native!))
(define check-defer-reruns! (extract front-end-entries check-defer-reruns!))
(define checked-settings (extract front-end-entries checked-settings))
(define check-hold-breaks! (extract front-end-entries check-hold-breaks!))
(define check-lines! (extract front-end-entries check-lines!))
(define check-more (extract front-end-entries check-more))
(define check-more-typed (extract front-end-entries check-more-typed))
(define check-text-typed (extract front-end-entries check-text-typed))
(define import-types (extract front-end-entries import-types))
(define check-program (extract front-end-entries check-program))
(define check-macro-uses! (extract front-end-entries check-macro-uses!))
(define keys-mirrored! (extract front-end-entries keys-mirrored!))
(define check-global-shapes! (extract front-end-entries check-global-shapes!))
(define checked-tops (extract front-end-entries checked-tops))
(define checked-reps (extract front-end-entries checked-reps))
(define checked-reps-again (extract front-end-entries checked-reps-again))
(define check-conv-native! (extract front-end-entries check-conv-native!))
(define check-globals-effects! (extract front-end-entries check-globals-effects!))
(define check-built-in! (extract front-end-entries check-built-in!))
(define check-syscalls! (extract front-end-entries check-syscalls!))
(define checked-effects (extract front-end-entries checked-effects))
(define checked-extracts (extract front-end-entries checked-extracts))
(define checked-reshapes! (extract front-end-entries checked-reshapes!))
(define checked-withs! (extract front-end-entries checked-withs!))
(define k-ok (extract front-end-entries k-ok))
(define k-err (extract front-end-entries k-err))
(define k-done (extract front-end-entries k-done))
