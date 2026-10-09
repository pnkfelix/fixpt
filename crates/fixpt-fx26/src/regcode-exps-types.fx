;;; The types of `regcode-exps.fx`, its `regcode-exps-module`: a module file of no
;;; state, which it loads, and so may its clients (`TODO.md` §68); its
;;; items in the order they were there.

;; The types these use, from the files that define them.
(define compile-exps-types (load-module "fx26:compile-exps-types.fx"))
(define-type c-inline (select compile-exps-types c-inline))
(define compile-plan-types (load-module "fx26:compile-plan-types.fx"))
(define-type c-special (select compile-plan-types c-special))
(define compile-types (load-module "fx26:compile-types.fx"))
(define-type cenv (select compile-types cenv))
(define-type patches (select compile-types patches))
(define parser-types ((proj (load-module "fx26:parser-types.fx") @s @e @m @c @p)))
(define-type exp (select parser-types exp))
(define regcode-types (load-module "fx26:regcode-types.fx"))
(define-type rargs (select regcode-types rargs))
(define-type renv (select regcode-types renv))
(define-type rlocs (select regcode-types rlocs))
(define table-types (load-module "fx26:table-types.fx"))
(define-type table (select table-types table))
;; A specialized call: which of `c-specials`, its global, and the lambda.
(define-type rspecial (productof (1 c-special) (2 wglobal) (3 exp)))
;; In a top-level definition's procedure: its name, its word, its arity, and
;; the label at the body's start (`r-self-guarded`), in a list.
(define-type rown (productof (1 symbol) (2 tword) (3 int) (4 int)))
;; While a body's fast version is compiled (`r-register-code`): whether, and
;; the globals it assumes hold what they held (a procedure inlined,
;; specialized or called by itself; a constant folded; a module whose member
;; is folded, `TODO.md` §42), newest first, each once: what its guards test,
;; that each has not been written since.
(define-type r-assumptions (listof wglobal acyclic))
;; How many times each global this program writes has been written once the
;; `global!`s emitted so far have run, by its name, newest first; and the
;; globals the form being compiled writes. As the Rust compiler's `writes`
;; and `form_writes`.
(define-type c-write (pairof wglobal int @k))
(define-type c-globals (listof wglobal @k))
(define-type c-write-table (table symbol (listof c-write @k) @k))
;; The top-level definition whose body is being compiled: its name and
;; arity, in a list.
(define-type rown-name (pairof symbol int @k))
;; An inlined call: which of `c-inlines`, and its global.
(define-type rinline (pairof c-inline wglobal @k))
;; Where a body finds its names: in register code, and to the cellular
;; compiler.
(define-type rscope (productof (1 renv) (2 cenv)))
;; A call-out's operands, and the patches for the siblings among them.
(define-type rarg-patches (productof (1 rargs) (2 patches)))
;; A join point's place: its parameters' places and its label.
(define-type rplace (pairof rlocs int @k))
;; Each binding's place, in a list; none for one that is no join point.
(define-type rplaces (listof (listof rplace @k) @k))

;;; ------------------------------------------------------------ signatures

;; What its clients use of it (`compile-programs.fx`).
;; The types it names, from the files that define them.
(define-type r-const-list (select regcode-types r-const-list))
(define-type rgen (select regcode-types rgen))
(define-type rthis (select regcode-types rthis))
(define-type wcells (select regcode-types wcells))
;; The types it names, from the files that define them.
(define-type bools (select regcode-types bools))
(define check-resolve-types (load-module "fx26:check-resolve-types.fx"))
(define-type exp-let-bs (select check-resolve-types exp-let-bs))
(define-type exp-letrec-bs (select check-resolve-types exp-letrec-bs))
(define check-subst-types (load-module "fx26:check-subst-types.fx"))
(define-type exp-params (select check-subst-types exp-params))
(define-type exps (select compile-types exps))
(define-type names (select parser-types names))
(define-type rarg (select regcode-types rarg))
(define-type rloc (select regcode-types rloc))
(define-type syms (select compile-types syms))
(define-type regcode-exps-sig
  (moduleof (val c-writes (ref c-write-table @k))
            (val c-form-writes (ref c-globals @k))
            (val c-wrote!
                 (subr (maxeff (alloc @k) (read @globals) (read @k) (write @k) spin)
                       (wglobal)
                       unit))
            (val r-inline-named
                 (subr (maxeff (alloc @k) (read @globals) (read @k))
                       ((listof c-inline acyclic) symbol int int)
                       (listof c-inline acyclic)))
            (val r-spec-at (ref rlocs @k))
            (val r-spec-start (ref int @k))
            (val r-keep-in-slot
                 (subr (maxeff (alloc @k) (read @globals) (read @k) (write @k)) (rgen) int))
            (val r-own-now (ref (listof rown @k) @k))
            (val r-assuming (ref bool @k))
            (val r-tail-calls-leave (ref bool @k))
            (val r-looped (ref bool @k))
            (val r-assumed (ref r-assumptions @k))
            (val r-own-name (ref (listof rown-name @k) @k))
            (val r-cells-length
                 (subr (maxeff (read @globals) (read @k) spin) (wcells int) int))
            (val r-rev-cells
                 (subr (maxeff (alloc @k) (read @globals) (read @k) spin)
                       (wcells wcells)
                       wcells))
            (val r-rev-assumptions
                 (subr (maxeff (alloc @k) (read @globals) (read @k) spin)
                       (r-assumptions r-assumptions)
                       r-assumptions))
            (val r-assumptions-length
                 (subr (maxeff (read @globals) (read @k) spin) (r-assumptions int) int))
            (val r-guard-cells
                 (subr (maxeff (alloc @k) (read @globals) (read @k) spin)
                       (r-assumptions int int wcells)
                       wcells))
            (val r-consts-named
                 (subr (maxeff (alloc @k) (read @globals) (read @k) spin)
                       (exp cenv)
                       r-const-list))
            (val r-consts-assumed
                 (subr (maxeff (alloc @k) (read @globals) (read @k) spin)
                       (r-const-list r-assumptions)
                       r-assumptions))
            (val r-collects
                 (subr (maxeff (alloc @k)
                               (goto @y)
                               (read @globals)
                               (read @k)
                               (read @t)
                               (write @k)
                               spin)
                       (exp cenv rthis bool)
                       bool))
            (val r-guard
                 (subr (maxeff (alloc @k) (read @globals) (read @k) (write @k) spin)
                       (rgen wglobal int)
                       unit))
            (val r-invoke
                 (subr (maxeff (alloc @k) (read @globals) (read @k) (write @k))
                       (rgen int bool)
                       unit))
            (val r-keep-in-reg
                 (subr (maxeff (alloc @k) (read @globals) (read @k) (write @k)) (rgen) int))
            (val r-keep
                 (subr (maxeff (alloc @k) (read @globals) (read @k) (write @k))
                       (rgen bool)
                       rloc))
            (val r-const-into
                 (subr (maxeff (alloc @k) (read @globals) (read @k) (write @k))
                       (rgen wcell int)
                       unit))
            (val r-lexical-into
                 (subr (maxeff (alloc @k) (read @globals) (read @k) (write @k))
                       (rgen int int)
                       unit))
            (val r-spec-param?
                 (subr (maxeff (alloc @k) (read @globals) (read @k) spin) (renv exp) bool))
            (val r-spec-self?
                 (subr (maxeff (alloc @k) (read @globals) (read @k) spin)
                       (renv exp exps)
                       bool))
            (val r-local-names
                 (subr (maxeff (alloc @k) (read @globals)) (cenv exp-let-bs) cenv))
            (val r-let-inits
                 (subr (maxeff (alloc @k) (read @globals) spin) (exp-let-bs) exps))
            (val r-local-params
                 (subr (maxeff (alloc @k) (read @globals)) (cenv exp-params) cenv))
            (val r-drop-bools (subr (maxeff (read @globals) (read @k)) (bools int) bools))
            (val r-own-self
                 (subr (maxeff (alloc @k) (read @globals) (read @k) spin)
                       (renv exp exps)
                       (listof wglobal @k)))
            (val r-join-flags
                 (subr (maxeff (alloc @k) (read @globals) (read @k) (write @k) spin)
                       (exp-letrec-bs exp bool)
                       bools))
            (val r-all? (subr (maxeff (read @globals) (read @k)) (bools) bool))
            (val r-join-of
                 (subr (maxeff (alloc @k) (read @globals) (read @k) spin) (renv exp) rlocs))
            (val c-length-locs (subr (maxeff (read @globals) (read @k) spin) (rlocs) int))
            (val r-jump-moves
                 (subr (maxeff (alloc @k) (read @globals) (read @k) (write @k) spin)
                       (rgen rlocs rlocs)
                       unit))
            (val r-bind-places
                 (subr (maxeff (alloc @k) (read @globals) (read @k) spin)
                       (renv exp-params rlocs)
                       renv))
            (val r-letrec-slots-j
                 (subr (maxeff (alloc @k) (read @globals) (read @k) (write @k) spin)
                       (rgen bools)
                       (listof int @k)))
            (val r-assume
                 (subr (maxeff (alloc @k) (read @globals) (read @k) (write @k))
                       (wglobal)
                       bool))
            (val r-self-moves
                 (subr (maxeff (alloc @k) (read @globals) (read @k) (write @k) spin)
                       (rgen rlocs int)
                       unit))
            (val r-slot-args-of
                 (subr (maxeff (alloc @k) (read @globals) (read @k) (write @k) spin)
                       (rlocs)
                       rargs))
            (val r-special-of
                 (subr (maxeff (alloc @k) (read @globals) (read @k) spin)
                       (int int renv exp exps)
                       (listof rspecial @k)))
            (val r-nth-param (subr (read @globals) (exp-params int) symbol))
            (val r-local-syms
                 (subr (maxeff (alloc @k) (read @globals) (read @k)) (cenv syms) cenv))
            (val r-standard-value
                 (subr (maxeff (alloc @k)
                               (goto @y)
                               (read @globals)
                               (read @k)
                               (read @t)
                               (write @k)
                               spin)
                       (rgen string bool)
                       unit))
            (val r-inline-of
                 (subr (maxeff (alloc @k) (read @globals) (read @k) spin)
                       (int int renv exp int)
                       (listof rinline @k)))))
