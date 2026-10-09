;;; The types of `regcode.fx`, its `regcode-module`: a module file of no
;;; state, which it loads, and so may its clients (`TODO.md` §68); its
;;; items in the order they were there.

;; The types these use, from the files that define them.
(define compile-types (load-module "fx26:compile-types.fx"))
(define-type c-this (select compile-types c-this))
(define-effect compiles (select compile-types compiles))
(define-type items (select compile-types items))
(define parser-types ((proj (load-module "fx26:parser-types.fx") @s @e @m @c @p)))
(define-type exp (select parser-types exp))
(define table-types (load-module "fx26:table-types.fx"))
(define-type table (select table-types table))
;; What register code's own helpers do: read the globals and what is being
;; made (`rreads`); and walk it, maybe at length (`rscans`), making more of
;; it (`rbuilds`); or emit an instruction, which writes it (`emits`).
(define-effect rreads (maxeff (read @globals) (read @k)))
(define-effect rscans (maxeff rreads spin))
(define-effect rbuilds (maxeff rreads (alloc @k) spin))
(define-effect emits (maxeff rreads (write @k) (alloc @k)))
;; And what the compiler proper does (`compiles`), at length.
(define-effect rcompiles (maxeff compiles spin))
;; Lists register code makes and walks.
(define-type bools (listof bool acyclic))
(define-type wcells (listof wcell @k))
(define-type rints (listof int @k))
;; What a procedure that knows itself knows (`c-this`), in a list of one.
(define-type rthis (listof c-this @k))
;;; ---------------------------------------------------------------- items

(define-datatype ritem
  (r-cell wcell)
  (r-label int)
  ;; `branch` (#f) or `branchf` (#t) to a label.
  (r-branch bool int)
  ;; `brancht` to a label.
  (r-brancht int)
  ;; The frame's size, known when the body is done.
  (r-frame)
  ;; `global-guard g w` to a label: unless global cell `g` holds a closure
  ;; made from word `w`.
  (r-guard-to wcell wcell int))
(define-type ritems (listof ritem @k))
;; Where a variable is, to register code.
;; A constant that needs no allocation when it runs, as register code may
;; know one: a sum or product of constants is made while compiling, once.
(define-datatype rconst
  (rc-int int) (rc-bool bool) (rc-char char) (rc-nil) (rc-data wcell)
  ;; A symbol, and a pair of constants: the parts of a constant list
  ;; (`TODO.md` §44), made where a cell needs it.
  (rc-sym symbol) (rc-pair rconst rconst))
(define-type rconsts (listof rconst @k))
;; The globals defined as constants (`TODO.md` §42), each cell and value,
;; newest first; each module's literal members, by the module's global; and,
;; while a fast version is compiled, the constants it folds, each behind a
;; `global-guard` (`r-fast-code`). As the Rust compiler's `const_globals`,
;; `module_consts` and `consts_now`.
(define-type r-const-global (pairof wglobal rconst @k))
(define-type r-const-list (listof r-const-global @k))
;; The globals defined as constant lists (`c-const-list`), apart from the
;; rest, by their names: what `r-unrolled` asks of a call's arguments,
;; without going through every constant.
(define-type r-const-list-table (table symbol r-const-list @k))
(define-type r-member-const (pairof symbol rconst @k))
(define-type r-module-const (pairof wglobal (listof r-member-const @k) @k))
;; The literal members of the module global `g` holds, in a list; none if it
;; has none noted.
(define-type r-members-at (listof (listof r-member-const @k) @k))
(define-datatype rloc
  (rl-reg int)
  (rl-slot int)
  (rl-free int)
  (rl-global wglobal)
  (rl-loop)
  ;; A `letrec` sibling not made yet, to be in this frame slot.
  (rl-pending int)
  ;; A constant, bound to the name (`r-known`): no place at all.
  (rl-const rconst)
  ;; A `letrec`-bound procedure only called in tail position, a join point
  ;; (`c-join-ok?`): where its parameters are, and its label.
  (rl-join (listof rloc @k) int)
  ;; A lambda-lifted procedure (`at-lifted`): only called.
  (rl-lifted int)
  ;; No name's place: a test an `if` around decided, true or false
  ;; (`r-knowing`): its comparison's name and operands, each a place or a
  ;; constant, as they were there.
  (rl-test string (listof rloc @k) bool))
(define-type rlocs (listof rloc @k))
(define-type renv (listof (pairof symbol rloc @k) @k))
;; An operand of a call-out: an expression, a constant, a procedure of no
;; arguments whose body is an expression (a `prompt`'s), a frame slot's
;; value, or a free value of the closure running.
(define-datatype rarg
  (a-e exp)
  (a-v wcell)
  (a-thunk exp)
  (a-slot int)
  (a-lexical int)
  ;; A variable's value, wherever it is: a lifted procedure's added
  ;; argument.
  (a-name symbol)
  ;; An expression's value, not converted as the checker said it is (the
  ;; conversion's own operand).
  (a-as-is exp))
(define-type rargs (listof rarg @k))
;; A standard operation, as register code does it.
(define-datatype rstd
  ;; `op2 r`, operands in order, or swapped; then `not`, if asked.
  (s-op2 int bool bool)
  (s-op1 int)
  (s-op2imm int wcell)
  (s-field int)
  ;; A call-out: a runtime primitive, or a cellular routine.
  (s-prim int)
  ;; A runtime primitive of one or two operands that never collects: in
  ;; line, as `prim1`, `prim2` or `prim2imm`, its operands as `op2`'s.
  (s-pure int)
  (s-cellular int)
  ;; Its argument itself (`%fx26-identity`).
  (s-identity)
  ;; A reference written: `setfield 2`, then unit.
  (s-set)
  ;; Arrays, the tag and key makers: several instructions.
  (s-special string)
  ;; `(apply f xs)`: a call, of `f`'s procedure of one list (`r-apply`).
  (s-apply)
  ;; `(list x …)`: the pairs made in line (`r-list`).
  (s-list)
  (s-none))
;; What is being made: the items, newest first; whether a leaf; the next
;; register and frame slot, and the most slots used; the labels; and, for a
;; procedure that knows itself, what it knows and its start's label.
(define-type rgen
  (productof (items (ref ritems @k)) (leaf bool) (nreg (ref int @k)) (nslot (ref int @k))
             (mslot (ref int @k)) (labels (ref int @k)) (this rthis) (start int)))
;;; Register moves: (source, destination), source 0 being RESULT.
(define-type rmove (pairof int int @k))
(define-type rmoves (listof rmove @k))
;; A leaf's tail call's arguments, as `r-leaf-args` sorts them: the moves
;; of those in registers, or made into one, to REG1…REGn; and the simple
;; ones, each with its register, made after the moves.
(define-type rlate (listof (pairof int exp @k) @k))
(define-type rleaf (productof (moves rmoves) (late rlate)))
;; A test's description: its comparison's name, and its operands.
(define-type rtest (pairof string rlocs @k))
