;;; Register code for a lambda, in FX-26 (PLAN.md 13h′ (e)): what the Rust
;;; compiler's `cellular/regcode.rs` makes, instruction for instruction, as
;;; the lambda's word's twin: the MacScheme machine's instructions
;;; (`layout::regcode`, the `rop-` numbers), made from the same trees.
;;;
;;; A leaf (a procedure that neither calls nor calls out, loops aside, and
;;; plain calls in tail position, made by moving the arguments into place:
;;; `r-leaf-tail-call`) keeps
;;; its parameters, its `let`s and its temporaries in registers; any other
;;; keeps its parameters and `let`s in a frame made on entry, since a call or
;;; a call-out may collect, and then only the frame holds values. What this
;;; compiler does not do, it declines, and the lambda keeps its stack code
;;; alone: it notes that it declined (`r-declined`) and goes on, making
;;; nothing anyone keeps, where the Rust compiler returns `None`.
;;;
;;; The twin phase calls it (`compile-twins.fx`), after a form's words; it
;;; calls no stack compiler.

;; Its types, those it uses of the files before it, and the signatures of
;; what it is given.
(let* ((regcode-types (load-module "fx26:regcode-types.fx"))
       (compile-types (load-module "fx26:compile-types.fx"))
       (parser-types ((proj (load-module "fx26:parser-types.fx") @s @e @m @c @p)))
       (check-resolve-types (load-module "fx26:check-resolve-types.fx"))
       (compile-exps-types (load-module "fx26:compile-exps-types.fx"))
       (compile-lift-types (load-module "fx26:compile-lift-types.fx"))
       (compile-plan-types (load-module "fx26:compile-plan-types.fx"))
       (table-types (load-module "fx26:table-types.fx"))
       (layout-types (load-module "fx26:layout-types.fx"))
       (standard-types (load-module "fx26:standard-types.fx")))
  ;; What it is given: the modules of the files before it that it uses.
  (lambda ((compile (select compile-types compile-sig))
           (compile-exps (select compile-exps-types compile-exps-sig))
           (compile-lift (select compile-lift-types compile-lift-sig))
           (compile-plan (select compile-plan-types compile-plan-sig))
           (check-resolve (select check-resolve-types check-resolve-sig))
           (tables (select table-types tables-sig))
           (layout (select layout-types layout-sig))
           (standard (select standard-types standard-sig)))
    (module
(define-effect rreads (select regcode-types rreads))
(define-effect rscans (select regcode-types rscans))
(define-effect rbuilds (select regcode-types rbuilds))
(define-effect emits (select regcode-types emits))
(define-effect rcompiles (select regcode-types rcompiles))
(define-type bools (select regcode-types bools))
(define-type wcells (select regcode-types wcells))
(define-type rints (select regcode-types rints))
(define-type rthis (select regcode-types rthis))
(define-type ritem (select regcode-types ritem))
(define r-cell (with regcode-types r-cell))
(define r-label (with regcode-types r-label))
(define r-branch (with regcode-types r-branch))
(define r-brancht (with regcode-types r-brancht))
(define r-frame (with regcode-types r-frame))
(define r-guard-to (with regcode-types r-guard-to))
(define-type ritems (select regcode-types ritems))
(define-type rconst (select regcode-types rconst))
(define rc-int (with regcode-types rc-int))
(define rc-bool (with regcode-types rc-bool))
(define rc-char (with regcode-types rc-char))
(define rc-nil (with regcode-types rc-nil))
(define rc-data (with regcode-types rc-data))
(define rc-sym (with regcode-types rc-sym))
(define rc-pair (with regcode-types rc-pair))
(define-type rconsts (select regcode-types rconsts))
(define-type r-const-global (select regcode-types r-const-global))
(define-type r-const-list (select regcode-types r-const-list))
(define-type r-const-list-table (select regcode-types r-const-list-table))
(define-type r-member-const (select regcode-types r-member-const))
(define-type r-module-const (select regcode-types r-module-const))
(define-type r-members-at (select regcode-types r-members-at))
(define-type rloc (select regcode-types rloc))
(define rl-reg (with regcode-types rl-reg))
(define rl-slot (with regcode-types rl-slot))
(define rl-free (with regcode-types rl-free))
(define rl-global (with regcode-types rl-global))
(define rl-loop (with regcode-types rl-loop))
(define rl-pending (with regcode-types rl-pending))
(define rl-const (with regcode-types rl-const))
(define rl-join (with regcode-types rl-join))
(define rl-lifted (with regcode-types rl-lifted))
(define rl-test (with regcode-types rl-test))
(define-type rlocs (select regcode-types rlocs))
(define-type renv (select regcode-types renv))
(define-type rarg (select regcode-types rarg))
(define a-e (with regcode-types a-e))
(define a-v (with regcode-types a-v))
(define a-thunk (with regcode-types a-thunk))
(define a-slot (with regcode-types a-slot))
(define a-lexical (with regcode-types a-lexical))
(define a-name (with regcode-types a-name))
(define a-as-is (with regcode-types a-as-is))
(define-type rargs (select regcode-types rargs))
(define-type rstd (select regcode-types rstd))
(define s-op2 (with regcode-types s-op2))
(define s-op1 (with regcode-types s-op1))
(define s-op2imm (with regcode-types s-op2imm))
(define s-field (with regcode-types s-field))
(define s-prim (with regcode-types s-prim))
(define s-pure (with regcode-types s-pure))
(define s-cellular (with regcode-types s-cellular))
(define s-identity (with regcode-types s-identity))
(define s-set (with regcode-types s-set))
(define s-special (with regcode-types s-special))
(define s-apply (with regcode-types s-apply))
(define s-list (with regcode-types s-list))
(define s-none (with regcode-types s-none))
(define-type rgen (select regcode-types rgen))
(define-type rmove (select regcode-types rmove))
(define-type rmoves (select regcode-types rmoves))
(define-type rlate (select regcode-types rlate))
(define-type rleaf (select regcode-types rleaf))
(define-type rtest (select regcode-types rtest))
;; The types it uses of the files before it.
(define at-global (with compile-types at-global))
(define at-slot (with compile-types at-slot))
(define-type cenv (select compile-types cenv))
(define-type exps (select compile-types exps))
(define-type items (select compile-types items))
(define-type syms (select compile-types syms))
(define e-app (with parser-types e-app))
(define e-bool (with parser-types e-bool))
(define e-char (with parser-types e-char))
(define e-convention (with parser-types e-convention))
(define e-float (with parser-types e-float))
(define e-int (with parser-types e-int))
(define e-plambda (with parser-types e-plambda))
(define e-product (with parser-types e-product))
(define e-proj (with parser-types e-proj))
(define e-str (with parser-types e-str))
(define e-sum (with parser-types e-sum))
(define e-sym (with parser-types e-sym))
(define e-the (with parser-types e-the))
(define e-unit (with parser-types e-unit))
(define e-var (with parser-types e-var))
(define e-with (with parser-types e-with))
(define-type exp (select parser-types exp))
(define-type names (select parser-types names))
(define-type exp-let-bs (select check-resolve-types exp-let-bs))
(define-type exp-letrec-bs (select check-resolve-types exp-letrec-bs))
;; What it uses of the modules it is given.
(define c-changed? (with compile c-changed?))
(define c-count-exps (with compile c-count-exps))
(define c-find (with compile c-find))
(define c-lifted (with compile c-lifted))
(define c-this-loc? (with compile c-this-loc?))
(define c-where (with compile c-where))
(define std-eq-name? (with compile std-eq-name?))
(define c-fx-name (with compile-exps c-fx-name))
(define c-quote-now (with compile-exps c-quote-now))
(define c-spec-now (with compile-exps c-spec-now))
(define c-has-standard-value? (with compile-lift c-has-standard-value?))
(define c-span-key (with compile-lift c-span-key))
(define r-eqtable-quick? (with compile-lift r-eqtable-quick?))
(define r-fixed-width-op? (with compile-lift r-fixed-width-op?))
(define c-inlining (with compile-plan c-inlining))
(define exp-end (with check-resolve exp-end))
(define exp-start (with check-resolve exp-start))
(define make-table (with tables make-table))
(define std-nil-name? (with tables std-nil-name?))
(define symbol-hash (with tables symbol-hash))
(define table-ref (with tables table-ref))
(define register-regs (with layout register-regs))
(define rop-branch (with layout rop-branch))
(define rop-branchf (with layout rop-branchf))
(define rop-brancht (with layout rop-brancht))
(define rop-const (with layout rop-const))
(define rop-global-guard (with layout rop-global-guard))
(define rop-lexical (with layout rop-lexical))
(define rop-movereg (with layout rop-movereg))
(define rop-pop (with layout rop-pop))
(define rop-reg (with layout rop-reg))
(define rop-return (with layout rop-return))
(define rop-setreg (with layout rop-setreg))
(define rop-stack (with layout rop-stack))
(define routine-abort (with layout routine-abort))
(define routine-callcc (with layout routine-callcc))
(define routine-callcomp (with layout routine-callcomp))
(define routine-cons (with layout routine-cons))
(define routine-currentmarks (with layout routine-currentmarks))
(define routine-eq (with layout routine-eq))
(define routine-firstmark (with layout routine-firstmark))
(define routine-int-add (with layout routine-int-add))
(define routine-int-eq (with layout routine-int-eq))
(define routine-int-less (with layout routine-int-less))
(define routine-int-sub (with layout routine-int-sub))
(define routine-marksof (with layout routine-marksof))
(define routine-pair-car (with layout routine-pair-car))
(define routine-pair-cdr (with layout routine-pair-cdr))
(define routine-withmark (with layout routine-withmark))
(define standard-primitive (with standard standard-primitive))

(define r-const-globals (ref r-const-list @k) (new nil))
(define r-const-lists (ref r-const-list-table @k) (new (make-table symbol-hash symbol=?)))
(define r-module-consts (ref (listof r-module-const @k) @k) (new nil))
(define r-consts-now (ref r-const-list @k) (new nil))
;; Global `g`'s constant in `cs`, in a list; none if it has none.
(define r-const-in (subr rbuilds (r-const-list wglobal) rconsts)
  (lambda (cs g)
    (cond ((null? cs) nil)
          ((wglobal=? (car (car cs)) g) (the rconsts (cons (cdr (car cs)) nil)))
          (else (r-const-in (cdr cs) g)))))
(define r-module-consts-of (subr rbuilds ((listof r-module-const @k) wglobal) r-members-at)
  (lambda (ms g)
    (cond ((null? ms) nil)
          ((wglobal=? (car (car ms)) g) (the r-members-at (cons (cdr (car ms)) nil)))
          (else (r-module-consts-of (cdr ms) g)))))
;; Member `f`'s literal of `cs`, in a list; none if it is not one.
(define r-member-in (subr rbuilds ((listof r-member-const @k) symbol) rconsts)
  (lambda (cs f)
    (cond ((null? cs) nil)
          ((symbol=? (car (car cs)) f) (the rconsts (cons (cdr (car cs)) nil)))
          (else (r-member-in (cdr cs) f)))))
;; Member `f`'s literal of the module global `g` holds, in a list; none if
;; it has none.
(define r-member-const (subr rbuilds (wglobal symbol) rconsts)
  (lambda (g f)
    (let ((cs (r-module-consts-of (get r-module-consts) g)))
      (if (null? cs) nil (r-member-in (car cs) f)))))

;; Whether the register code being made has been declined.
(define r-declined (ref bool @k) (new #f))
(define r-decline (subr (maxeff (read @globals) (write @k)) () unit)
  (lambda () (set r-declined #t)))

(define r-emit (subr (maxeff (read @k) (write @k) (alloc @k)) (rgen ritem) unit)
  (lambda (g i) (let ((items (extract g items))) (set items (cons i (get items))))))
(define r-op0 (subr emits (rgen int) unit)
  (lambda (g op) (r-emit g (r-cell (wcell-int op)))))
(define r-op1 (subr emits (rgen int wcell) unit)
  (lambda (g op x) (begin (r-op0 g op) (r-emit g (r-cell x)))))
(define r-op2 (subr emits (rgen int wcell wcell) unit)
  (lambda (g op x y) (begin (r-op1 g op x) (r-emit g (r-cell y)))))
(define r-opn (subr emits (rgen int int) unit)
  (lambda (g op n) (r-op1 g op (wcell-int n))))
(define r-opnn (subr emits (rgen int int int) unit)
  (lambda (g op n m) (r-op2 g op (wcell-int n) (wcell-int m))))
(define r-new-label (subr (maxeff (read @k) (write @k)) (rgen) int)
  (lambda (g) (let* ((l (extract g labels)) (n (get l))) (begin (set l (+ n 1)) n))))
(define r-reg (subr (maxeff (read @globals) (read @k) (write @k)) (rgen) int)
  (lambda (g)
    (let* ((r (extract g nreg)) (n (+ (get r) 1)))
      (begin (set r n) (if (> n register-regs) (r-decline) #u) n))))
(define r-slot (subr (maxeff (read @k) (write @k)) (rgen) int)
  (lambda (g)
    (let* ((s (extract g nslot)) (n (get s)) (m (extract g mslot)))
      (begin (set s (+ n 1)) (if (> (+ n 1) (get m)) (set m (+ n 1)) #u) n))))
;; Pop the frame, if there is one, before leaving.
(define r-leave (subr emits (rgen) unit)
  (lambda (g) (if (extract g leaf) #u (begin (r-op0 g rop-pop) (r-emit g (r-frame))))))
(define r-done (subr emits (rgen bool) unit)
  (lambda (g tail) (if tail (begin (r-leave g) (r-op0 g rop-return)) #u)))

(define r-reverse (subr rbuilds (ritems ritems) ritems)
  (lambda (xs acc) (if (null? xs) acc (r-reverse (cdr xs) (cons (car xs) acc)))))
(define r-size (subr pure (ritem) int)
  (lambda (i)
    (tagcase i
      (r-cell (x) 1)
      (r-label (n) 0)
      (r-branch (f n) 2)
      (r-brancht (n) 2)
      (r-frame () 1)
      (r-guard-to (c w n) 4))))
(define r-place (subr (maxeff rscans (write @k)) (ritems (arrayof int @k) int) int)
  (lambda (xs at pos)
    (if (null? xs)
        pos
        (begin (tagcase (car xs) (r-label (n) (array-set! at n pos)) (else x #u))
               (r-place (cdr xs) at (+ pos (r-size (car xs))))))))
;; The offset to label `n`, placed at `at`, from the cell after an item of
;; `size` cells at `pos`, as a cell.
(define r-offset (subr rreads ((arrayof int @k) int int int) wcell)
  (lambda (at n pos size) (wcell-int (- (array-ref at n) (+ pos size)))))
;; Item `i`'s cells, at `pos`, onto `acc`: a branch's offset resolved, the
;; frame's size in place.
(define r-item-cells (subr rbuilds (ritem (arrayof int @k) int int wcells) wcells)
  (lambda (i at pos frame acc)
    (tagcase i
      (r-cell (x) (cons x acc))
      (r-label (n) acc)
      (r-frame () (cons (wcell-int frame) acc))
      (r-branch (f n)
        (cons (wcell-int (if f rop-branchf rop-branch)) (cons (r-offset at n pos 2) acc)))
      (r-brancht (n) (cons (wcell-int rop-brancht) (cons (r-offset at n pos 2) acc)))
      (r-guard-to (c w n)
        (cons (wcell-int rop-global-guard) (cons c (cons w (cons (r-offset at n pos 4) acc))))))))
;; The cells, branches resolved (an offset counts from the cell after it),
;; and the frame's size in place: from the items newest first, each ending
;; at `end`, onto those after it, in a loop, however long the code.
(define r-cells (subr rbuilds (ritems (arrayof int @k) int int wcells) wcells)
  (lambda (xs at end frame acc)
    (if (null? xs)
        acc
        (let ((pos (- end (r-size (car xs)))))
          (r-cells (cdr xs) at pos frame (r-item-cells (car xs) at pos frame acc))))))
(define r-assemble (subr (maxeff emits spin) (rgen) wcells)
  (lambda (g)
    (let* ((items (get (extract g items)))
           (at (the (arrayof int @k) (make-array (+ 1 (get (extract g labels))) 0)))
           (end (r-place (r-reverse items nil) at 0)))
      (r-cells items at end (get (extract g mslot)) nil))))

;;; ------------------------------------------------------------- variables

;; Where global `n` is, in a list; none if it is no global.
(define r-global-loc (subr rbuilds (symbol) rlocs)
  (lambda (n)
    (let ((l (c-where (the cenv nil) n)))
      (if (null? l)
          nil
          (tagcase (car l)
            ;; A constant a fast version folds (`r-fast-code`).
            (at-global (g)
              (let ((k (r-const-in (get r-consts-now) g)))
                (the rlocs (cons (if (null? k) (rl-global g) (rl-const (car k))) nil))))
            (else y nil))))))
(define r-where (subr rbuilds (renv symbol) rlocs)
  (lambda (env n)
    (cond ((null? env) (r-global-loc n))
          ((symbol=? (car (car env)) n) (the rlocs (cons (cdr (car env)) nil)))
          (else (r-where (cdr env) n)))))
;; `env` with `n` at `l`.
(define r-bind (subr (maxeff (read @globals) (alloc @k)) (symbol rloc renv) renv)
  (lambda (n l env) (the renv (cons (cons n l) env))))
;; Where the variable `f` is, in a list; none if `f` is no variable, or
;; not bound.
(define r-var-loc (subr rbuilds (renv exp) rlocs)
  (lambda (env f) (tagcase f (e-var (n a b) (r-where env n)) (else y nil))))
;; The same, if `f` is not converted either.
(define r-plain-var-loc (subr rbuilds (renv exp) rlocs)
  (lambda (env f) (if (c-changed? f) nil (r-var-loc env f))))
;; The global the variable `f` is, in a list; none if it is no global.
(define r-var-global (subr rbuilds (renv exp) (listof wglobal @k))
  (lambda (env f)
    (let ((l (r-var-loc env f)))
      (if (null? l)
          nil
          (tagcase (car l) (rl-global (c) (the (listof wglobal @k) (cons c nil))) (else y nil))))))

;; A let-bound name in the cellular environment: a local, captured as such.
(define r-local (subr (maxeff (read @globals) (alloc @k)) (cenv symbol) cenv)
  (lambda (te n) (the cenv (cons (cons n (at-slot -1)) te))))

;; Whether `x` needs no register code of its own to be had: a constant, or
;; a variable not named as a standard operation is (which may be one made a
;; value, a closure); and not converted.
(define r-simple? (subr rreads (exp) bool)
  (lambda (x)
    (and (not (c-changed? x))
         (tagcase x
           (e-var (n a b) (not (c-has-standard-value? (symbol->string n))))
           (e-int (n a b) #t) (e-bool (v a b) #t) (e-char (v a b) #t)
           (e-sym (v a b) #t) (e-unit (a b) #t) (e-str (v a b) #t) (e-float (v a b) #t)
           (else y #f)))))

;; A constant's cell.
(define r-const-cell (subr spin (rconst) wcell)
  (lambda (c)
    (tagcase c
      (rc-int (n) (wcell-int n))
      (rc-bool (v) (wcell-bool v))
      (rc-char (v) (wcell-char v))
      (rc-nil () (wcell-nil))
      (rc-data (w) w)
      (rc-sym (s) (wcell-symbol s))
      (rc-pair (a d) (wcell-pair (r-const-cell a) (r-const-cell d))))))
;; Constants' cells, in order.
(define r-const-cells (subr rbuilds (rconsts) wcells)
  (lambda (cs) (if (null? cs) nil (cons (r-const-cell (car cs)) (r-const-cells (cdr cs))))))
;; Constant `c`, known: in a list of one.
(define r-known-as (subr (alloc @k) (rconst) rconsts)
  (lambda (c) (the rconsts (cons c nil))))
;; Whether a constant is #f.
(define r-const-false? (subr pure (rconst) bool)
  (lambda (c) (tagcase c (rc-bool (v) (not v)) (else y #f))))
;; Whether integer `n` is under 2^30 in size.
(define r-small? (subr pure (int) bool)
  (lambda (n) (and (< n 1073741824) (> n -1073741824))))
;; An integer under 2^30 in size, in a list, if `c` is one.
(define r-const-small (subr (maxeff (read @globals) (alloc @k)) (rconst) (listof int @k))
  (lambda (c)
    (tagcase c
      (rc-int (n) (if (r-small? n) (the (listof int @k) (cons n nil)) nil))
      (else y nil))))
;; Whether constant `c` (in a list) is `when` (true: anything but #f).
(define r-holds? (subr rreads (rconsts bool) bool)
  (lambda (c when) (if (r-const-false? (car c)) (not when) when)))

(define r-this-name? (subr (read @k) (rthis symbol int) bool)
  (lambda (this n nargs)
    (and (not (null? this))
         (let ((t (car this)))
           (and (symbol=? n (extract t 1)) (= (+ (extract t 4) nargs) (extract t 3)))))))
;; How many of the running procedure's parameters, first, a lifting added.
(define r-this-added (subr (read @k) (rgen) int)
  (lambda (g) (let ((this (extract g this))) (if (null? this) 0 (extract (car this) 4)))))
;; The members' `c-lifts` indices, in a list of one, if the `letrec` at
;; `a`–`b` was lifted by its stack code (`c-lift`); none if not, or if it
;; is in a body inlined or specialized here, which another program's text
;; may have spans in common with.
(define r-lifted (subr rreads (int int) (listof (listof int @k) @k))
  (lambda (a b)
    (if (and (null? (get c-inlining)) (null? (get c-spec-now)))
        (table-ref (get c-lifted) (c-span-key a b) (the (listof (listof int @k) @k) nil))
        nil)))
;; `bs`' names bound to the lifted procedures `ks`, onto `env`.
(define r-bind-lifted (subr rbuilds (exp-letrec-bs (listof int @k) renv) renv)
  (lambda (bs ks env)
    (if (null? bs)
        env
        (r-bind-lifted (cdr bs) (cdr ks) (r-bind (extract (car bs) 1) (rl-lifted (car ks)) env)))))
;; The index in `c-lifts` of the procedure `f` names, if a lifted one; else -1.
(define r-lifted-at (subr rbuilds (renv exp) int)
  (lambda (env f)
    (let ((l (r-var-loc env f)))
      (if (null? l) -1 (tagcase (car l) (rl-lifted (k) k) (else y -1))))))
;; `names` as arguments, their values wherever they are, then `rest`.
(define r-name-args (subr rbuilds (syms rargs) rargs)
  (lambda (names rest)
    (if (null? names) rest (the rargs (cons (a-name (car names)) (r-name-args (cdr names) rest))))))
;; Whether a move of `ms` but the `k`th reads register `d`.
(define r-read-by-other? (subr rscans (rmoves int int int) bool)
  (lambda (ms d k i)
    (cond ((null? ms) #f)
          ((and (not (= i k)) (= (car (car ms)) d)) #t)
          (else (r-read-by-other? (cdr ms) d k (+ i 1))))))
;; The index of the first move of `ms` (from the `k`th of `all`) whose
;; destination no other move reads; -1 if none.
(define r-free-move (subr rscans (rmoves rmoves int) int)
  (lambda (all ms k)
    (cond ((null? ms) -1)
          ((r-read-by-other? all (cdr (car ms)) k 0) (r-free-move all (cdr ms) (+ k 1)))
          (else k))))
(define r-nth-move (subr rscans (rmoves int) rmove)
  (lambda (ms k) (if (= k 0) (car ms) (r-nth-move (cdr ms) (- k 1)))))
(define r-drop-move (subr rbuilds (rmoves int int) rmoves)
  (lambda (ms k i)
    (cond ((null? ms) nil)
          ((= i k) (cdr ms))
          (else (cons (car ms) (r-drop-move (cdr ms) k (+ i 1)))))))
;; `ms`, those reading register `d` reading RESULT instead.
(define r-reread (subr rbuilds (rmoves int) rmoves)
  (lambda (ms d)
    (if (null? ms)
        nil
        (let ((m (car ms)))
          (cons (if (= (car m) d) (the rmove (cons 0 (cdr m))) m) (r-reread (cdr ms) d))))))
;; Move `m` made: its source register, or RESULT, into its destination.
(define r-move (subr emits (rgen rmove) unit)
  (lambda (g m)
    (if (= (car m) 0) (r-opn g rop-setreg (cdr m)) (r-opnn g rop-movereg (car m) (cdr m)))))
;; Register moves made so that none overwrites what another has yet to
;; read, as the Rust compiler's `r_par_moves`: the first whose destination
;; no other reads, in order; else, the rest a cycle, the first's
;; destination kept in RESULT, and read from there.
(define r-par-moves (subr (maxeff emits spin) (rgen rmoves) unit)
  (lambda (g ms)
    (if (null? ms)
        #u
        (let ((k (r-free-move ms ms 0)))
          (if (>= k 0)
              (begin (r-move g (r-nth-move ms k))
                     (r-par-moves g (r-drop-move ms k 0)))
              (let ((d (cdr (car ms))))
                (begin (r-opn g rop-reg d) (r-par-moves g (r-reread ms d)))))))))
;; The moves of each free value of `fv` (from the `j`th) in a register into
;; REGj+1, where it is not there already.
(define r-reg-moves (subr rbuilds (syms renv int) rmoves)
  (lambda (fv env j)
    (if (null? fv)
        nil
        (let ((l (r-where env (car fv))) (rest (r-reg-moves (cdr fv) env (+ j 1))))
          (if (null? l)
              rest
              (tagcase (car l)
                (rl-reg (r) (if (= r (+ j 1)) rest (cons (the rmove (cons r (+ j 1))) rest)))
                (else y rest)))))))

;; A leaf's tail call's arguments, sorted.
(define r-rleaf (subr (read @globals) (rmoves rlate) rleaf)
  (lambda (ms late) (product (moves ms) (late late))))
;; `rest` with the move of `s` to REGk first, or the simple argument `a`.
(define r-leaf-move (subr (maxeff (read @globals) (alloc @k)) (rleaf int int) rleaf)
  (lambda (rest s k)
    (let ((m (the rmove (cons s k)))) (r-rleaf (cons m (extract rest moves)) (extract rest late)))))
(define r-leaf-late (subr (maxeff (read @globals) (alloc @k)) (rleaf int exp) rleaf)
  (lambda (rest k a) (r-rleaf (extract rest moves) (cons (cons k a) (extract rest late)))))
;; The register `l` is, or 0 if it is none.
(define r-reg-of (subr rreads (rlocs) int)
  (lambda (l) (if (null? l) 0 (tagcase (car l) (rl-reg (r) r) (else y 0)))))
;; Whether register moves form a cycle: some left when every move whose
;; destination no other reads is taken away. As `r_moves_cycle`.
(define r-moves-cycle? (subr rbuilds (rmoves) bool)
  (lambda (ms)
    (and (not (null? ms))
         (let ((k (r-free-move ms ms 0)))
           (or (< k 0) (r-moves-cycle? (r-drop-move ms k 0)))))))
;; Whether a move of `ms`, or a simple argument of `late`, writes REGk.
(define r-written? (subr rscans (int rmoves rlate) bool)
  (lambda (k ms late)
    (cond ((not (null? ms)) (or (= (cdr (car ms)) k) (r-written? k (cdr ms) late)))
          ((null? late) #f)
          (else (or (= (car (car late)) k) (r-written? k ms (cdr late)))))))
;; `ms` with the move of `s` to `d` last.
(define r-moves-snoc (subr rbuilds (rmoves int int) rmoves)
  (lambda (ms s d)
    (if (null? ms)
        (the rmoves (cons (the rmove (cons s d)) nil))
        (cons (car ms) (r-moves-snoc (cdr ms) s d)))))

;; Whether `f` is the procedure running, called with its arity: its own
;; name, still bound where the procedure knows itself to be.
(define r-self-known? (subr rbuilds (rgen exp int cenv) bool)
  (lambda (g f nargs te)
    (tagcase f
      (e-var (n a b)
        (and (r-this-name? (extract g this) n nargs)
             (let ((l (c-find te n)) (at (extract (car (extract g this)) 2)))
               (and (not (null? l)) (c-this-loc? (car l) at)))))
      (else y #f))))

;;; ------------------------------------------------------ standard names

;; Whether runtime primitive `name` never collects (`fixpt_runtime::never_collects`): FX-26's
;; `*`, `quotient` and `modulo`, the fixed-width integers' and floats' operations, and a flat
;; array's element and length, and an eqtable's operations of one or two, which register code
;; calls with its values in registers.
(define r-never-collects? (subr (read (globals r-eqtable-quick? r-fixed-width-op?)) (string) bool)
  (lambda (name)
    (case name
      (("%fx26-mul" "%fx26-quotient" "modulo" "%fx26-string->f64" "%fx26-flatarray-ref"
        "%fx26-flatarray-length" "char->integer" "integer->char" "string-length" "string-ref"
        "%string-hash" "%symbol-hash" "%fx26-string-compare" "%fx26-symbol-compare"
        "%fx26-string<?" "%fx26-string<=?" "%fx26-string>?" "%fx26-string>=?"
        "%fx26-char<?" "%fx26-char<=?" "%fx26-char>?" "%fx26-char>=?"
        "null?" "pair?" "exact-integer?" "char?" "boolean?" "string?" "symbol?" "%fx26-procedure?"
        "%fx26-array?" "%fx26-f32?" "%fx26-box?" "%fx26-sum?" "%fx26-product?")
       #t)
      (else (or (r-eqtable-quick? name) (r-fixed-width-op? name))))))
;; Runtime primitive `name` as a call-out, when it is one and `n` = `k`; in line, if it never
;; collects and takes one or two.
(define r-prim-std (subr (read @globals) (string int int) rstd)
  (lambda (name n k)
    (let ((p (runtime-primitive name)))
      (cond ((not (and (>= p 0) (= n k))) (s-none))
            ((and (<= n 2) (r-never-collects? name)) (s-pure p))
            (else (s-prim p))))))

;; Whether `name` is an equality `op2 eq` does (`std-eq-name?`).
(define r-eq-name? (subr (read @globals) (string) bool) (lambda (name) (std-eq-name? name)))
;; Whether `name` makes a box: a prompt tag or a mark key.
(define r-box-name? (subr (read @globals) (string) bool)
  (lambda (name)
    (or (string=? name "make-continuation-prompt-tag")
        (string=? name "make-continuation-mark-key"))))
;; Whether `name` is a runtime primitive of that name to the cellular
;; compiler, one register code calls out to as well.
(define r-prim-name? (subr (read @globals) (string) bool)
  (lambda (name)
    (or (string=? name "modulo")
        (string=? name "char->integer") (string=? name "integer->char")
        (string=? name "string-append") (string=? name "string-length")
        (string=? name "string-ref") (string=? name "substring")
        (string=? name "string=?") (string=? name "string->symbol")
        (string=? name "symbol->string"))))
;; Whether `name` is `+` or `-`.
(define r-add-name? (subr (read @globals) (string) bool)
  (lambda (name) (or (string=? name "+") (string=? name "-"))))

;; Whether `name`, applied to `n` arguments, is a standard operation register
;; code does, and how: as the Rust compiler's `r_standard`, whose last case
;; is what the cellular compiler does with one runtime primitive.
(define r-standard (subr (maxeff rreads (alloc @k)) (string int) rstd)
  (lambda (name n)
    (let ((is (lambda ((s string) (k int)) (and (string=? name s) (= n k)))))
      (cond ((is "+" 2) (s-op2 routine-int-add #f #f))
            ((is "-" 2) (s-op2 routine-int-sub #f #f))
            ((is "<" 2) (s-op2 routine-int-less #f #f))
            ((is ">" 2) (s-op2 routine-int-less #t #f))
            ((is "<=" 2) (s-op2 routine-int-less #t #t))
            ((is ">=" 2) (s-op2 routine-int-less #f #t))
            ((is "=" 2) (s-op2 routine-int-eq #f #f))
            ((and (r-eq-name? name) (= n 2)) (s-op2 routine-eq #f #f))
            ((is "not" 1) (s-op2imm routine-eq (wcell-bool #f)))
            ((is "null?" 1) (s-op2imm routine-eq (wcell-nil)))
            ((is "car" 1) (s-op1 routine-pair-car))
            ((is "cdr" 1) (s-op1 routine-pair-cdr))
            ((is "get" 1) (s-field 2))
            ((is "cons" 2) (s-cellular routine-cons))
            ((is "set" 2) (s-set))
            ((is "abort-current-continuation" 2) (s-cellular routine-abort))
            ((is "call-with-composable-continuation" 2) (s-cellular routine-callcomp))
            ((is "cwcc" 1) (s-cellular routine-callcc))
            ((is "with-mark" 3) (s-cellular routine-withmark))
            ((is "first-mark" 2) (s-cellular routine-firstmark))
            ((is "current-marks" 1) (s-cellular routine-currentmarks))
            ((is "marks-of" 2) (s-cellular routine-marksof))
            ((is "array-ref" 2) (s-special "array-ref"))
            ((is "array-set!" 3) (s-special "array-set!"))
            ((is "array-length" 1) (s-special "array-length"))
            ((is "make-array" 2) (s-special "make-array"))
            ((is "apply" 2) (s-apply))
            ((string=? name "list") (s-list))
            ((and (r-box-name? name) (= n 0)) (s-special "make-box"))
            ;; What the cellular compiler does as one runtime primitive
            ;; (`c-standard-on`), register code does too.
            ((or (is "set-car!" 2) (is "set-cdr!" 2)) (s-special name))
            ((string=? name "new") (r-prim-std "%make-box" n 1))
            ((string=? name "char->string") (r-prim-std "string" n 1))
            ((r-prim-name? name) (r-prim-std name n n))
            (else
             (let ((p (standard-primitive name)))
               (case p (("%fx26-identity") (if (= n 1) (s-identity) (s-none)))
                       (("") (s-none))
                       (else (r-prim-std p n n)))))))))
;; The operator under the type abstractions, projections, ascriptions and
;; conversions, which compile to nothing: `((proj car @r) xs)` is `car`
;; applied.
(define r-operator (subr rscans (exp) exp)
  (lambda (f)
    (tagcase f
      (e-plambda (d body a b) (r-operator body))
      (e-proj (body ds a b) (r-operator body))
      (e-the (d body a b) (r-operator body))
      (e-convention (cnv body a b) (r-operator body))
      (else y y))))
(define r-standard-name (subr rbuilds (renv exp) string)
  (lambda (env f)
    (tagcase (r-operator f)
      (e-var (n a b) (if (null? (r-where env n)) (symbol->string n) ""))
      (e-with (m body a b) (c-fx-name m body))
      (else y ""))))
;; Whether `e` is a `+` or `-` of two.
(define r-adds? (subr rbuilds (renv exp) bool)
  (lambda (env e)
    (tagcase e
      (e-app (f args a b)
        (and (= (c-count-exps args) 2) (r-add-name? (r-standard-name env f))))
      (else y #f))))
(define r-rev-consts (subr rbuilds (rconsts rconsts) rconsts)
  (lambda (xs acc) (if (null? xs) acc (r-rev-consts (cdr xs) (cons (car xs) acc)))))
(define c-length-consts (subr rscans (rconsts) int)
  (lambda (xs) (if (null? xs) 0 (+ 1 (c-length-consts (cdr xs))))))
;; Whether constant `c` is an integer that fits the fixed-width type `name` converts to
;; (`int->u32`, and so on): then it is its own conversion, the type's value the fixnum.
(define r-fits-fixed? (subr pure (string rconst) bool)
  (lambda (name c)
    (tagcase c
      (rc-int (n)
        (case name (("int->i32") (and (>= n -2147483648) (<= n 2147483647)))
                   (("int->u32") (and (>= n 0) (<= n 4294967295)))
                   (("int->i64") #t)
                   (("int->u64") (>= n 0))
                   (else #f)))
      (else y #f))))
;; Standard operation `name` on constants `vs`, folded, if it is one that
;; folds.
(define r-fold (subr (maxeff rreads (alloc @k)) (string rconsts) rconsts)
  (lambda (name vs)
    (let* ((two (and (not (null? vs)) (and (not (null? (cdr vs))) (null? (cdr (cdr vs))))))
           (one (and (not (null? vs)) (null? (cdr vs))))
           (a (if two (r-const-small (car vs)) (the (listof int @k) nil)))
           (b (if two (r-const-small (car (cdr vs))) (the (listof int @k) nil)))
           (ints (and (not (null? a)) (not (null? b))))
           (int (lambda ((n int)) (the rconsts (cons (rc-int n) nil))))
           (bool (lambda ((v bool)) (the rconsts (cons (rc-bool v) nil)))))
      (cond ((and ints (string=? name "+")) (int (+ (car a) (car b))))
            ((and ints (string=? name "-")) (int (- (car a) (car b))))
            ((and ints (string=? name "<")) (bool (< (car a) (car b))))
            ((and ints (string=? name ">")) (bool (> (car a) (car b))))
            ((and ints (string=? name "<=")) (bool (<= (car a) (car b))))
            ((and ints (string=? name ">=")) (bool (>= (car a) (car b))))
            ((and ints (string=? name "=")) (bool (= (car a) (car b))))
            ((and ints (string=? name "*"))
             (let ((p (* (car a) (car b))))
               (if (r-small? p) (int p) nil)))
            ((and one (string=? name "not")) (bool (r-const-false? (car vs))))
            ((and one (string=? name "null?")) (bool (tagcase (car vs) (rc-nil () #t) (else y #f))))
            ;; A constant list is at a region nothing writes: its parts are
            ;; constants too.
            ((and one (string=? name "car"))
             (tagcase (car vs) (rc-pair (x d) (the rconsts (cons x nil))) (else y nil)))
            ((and one (string=? name "cdr"))
             (tagcase (car vs) (rc-pair (x d) (the rconsts (cons d nil))) (else y nil)))
            ((and two (string=? name "char=?"))
             (tagcase (car vs)
               (rc-char (x) (tagcase (car (cdr vs)) (rc-char (y) (bool (char=? x y))) (else z nil)))
               (else z nil)))
            ((and one (r-fits-fixed? name (car vs))) vs)
            (else nil)))))
(define-rec
  ;; `x`'s value, if it is a constant that needs no allocation when it
  ;; runs, as the Rust compiler's `r_const` says: a literal, a name bound to
  ;; one, `nil`, a standard operation on constants folded (`+` and `-` on
  ;; integers under 2^30 in size, which cannot overflow; comparisons; `not`;
  ;; `null?`; `char=?`; `int->u32` and its kin of an integer that fits), or a
  ;; sum or product of constants, made now, once.
  (r-known (subr rbuilds (renv exp) rconsts)
    (lambda (env x)
      (tagcase x
        (e-int (n a b) (r-known-as (rc-int n)))
        (e-bool (v a b) (r-known-as (rc-bool v)))
        (e-char (v a b) (r-known-as (rc-char v)))
        (e-var (n a b)
          (let ((l (r-where env n)))
            (if (null? l)
                (if (std-nil-name? (symbol->string n)) (r-known-as (rc-nil)) nil)
                (tagcase (car l) (rl-const (c) (r-known-as c)) (else y nil)))))
        (e-the (d body a b) (r-known env body))
        (e-plambda (d body a b) (r-known env body))
        (e-proj (body ds a b) (r-known env body))
        (e-sum (t v a b)
          (let ((c (r-known env v)))
            (if (null? c) nil (r-known-as (rc-data (wcell-sum t (r-const-cell (car c))))))))
        (e-product (fs a b)
          (let ((vs (r-known-fields env fs nil)))
            (if (null? vs) nil (r-known-as (rc-data (wcell-product (r-const-cells (car vs))))))))
        (e-app (f args a b)
          (let* ((name (r-standard-name env f))
                 (decided (if (r-test-name? name) (r-known-test env x) (the rconsts nil))))
            (cond
              ((not (null? decided)) decided)
              ((string=? name "") nil)
              ;; A quoted datum (TODO §51), made once where it is all
              ;; literals, as the stack code makes it.
              ((and (string=? name "%quote") (= (c-count-exps args) 1))
               (let ((k (c-quote-now (car args))))
                 (if (null? k) nil (r-known-as (rc-data (car k))))))
              (else
                (let ((vs (r-knowns env args nil)))
                  (if (or (null? vs) (not (= (c-length-consts (car vs)) (c-count-exps args))))
                      nil
                      (r-fold name (car vs))))))))
        (else y nil))))
  ;; Test `x`'s value, where an `if` around has decided it (`r-knowing`),
  ;; as a constant: compared with each test decided, by name and operands.
  ;; As the Rust compiler's `r_known_test`.
  (r-known-test (subr rbuilds (renv exp) rconsts)
    (lambda (env x)
      (if (not (r-tests-in? env))
          nil
          (let ((d (r-test-desc env x)))
            (if (null? d) nil (r-decided env (car d)))))))
  ;; What test `x` is, to know it again: its comparison's name and each
  ;; operand, a place (a register, frame slot or free value) or literal
  ;; constant, in a list; none if it is not such a test.
  (r-test-desc (subr rbuilds (renv exp) (listof rtest @k))
    (lambda (env x)
      (tagcase x
        (e-app (f args a b)
          (let ((name (r-standard-name env f)))
            (if (not (r-test-name? name))
                nil
                (let ((ops (r-test-operands env args)))
                  (if (null? ops) nil (cons (cons name (car ops)) nil))))))
        (else y nil))))
  ;; Each operand's place or constant, in order, in a list; none if one is
  ;; neither.
  (r-test-operands (subr rbuilds (renv exps) (listof rlocs @k))
    (lambda (env args)
      (if (null? args)
          (cons (the rlocs nil) nil)
          (let ((one (r-test-operand env (car args))) (rest (r-test-operands env (cdr args))))
            (if (or (null? one) (null? rest)) nil (cons (cons (car one) (car rest)) nil))))))
  (r-test-operand (subr rbuilds (renv exp) rlocs)
    (lambda (env a)
      (let ((k (r-known env a)))
        (if (null? k)
            (let ((l (r-plain-var-loc env a)))
              (if (null? l)
                  nil
                  (tagcase (car l)
                    (rl-reg (i) l) (rl-slot (i) l) (rl-free (i) l)
                    (else y nil))))
            (tagcase (car k)
              (rc-pair (x d) nil)
              (rc-data (w) nil)
              (else y (cons (rl-const (car k)) nil)))))))
  ;; Each of `es`' constants, in order, onto `acc` reversed, in a list; none
  ;; if one is not a constant.
  (r-knowns (subr rbuilds (renv exps rconsts) (listof rconsts @k))
    (lambda (env es acc)
      (if (null? es)
          (the (listof rconsts @k) (cons (r-rev-consts acc nil) nil))
          (let ((c (r-known env (car es))))
            (if (null? c) nil (r-knowns env (cdr es) (cons (car c) acc)))))))
  ;; The same for a product's fields.
  (r-known-fields (subr rbuilds (renv exp-let-bs rconsts) (listof rconsts @k))
    (lambda (env fs acc)
      (if (null? fs)
          (the (listof rconsts @k) (cons (r-rev-consts acc nil) nil))
          (let ((c (r-known env (extract (car fs) 2))))
            (if (null? c) nil (r-known-fields env (cdr fs) (cons (car c) acc))))))))

;; Whether a test an `if` decided is in scope in `env`.
(define r-tests-in? (subr rscans (renv) bool)
  (lambda (env)
    (and (not (null? env))
         (or (tagcase (cdr (car env)) (rl-test (n o v) #t) (else y #f)) (r-tests-in? (cdr env))))))
;; The value of the test `d` describes, if one in `env` is it, the newest.
(define r-decided (subr rbuilds (renv rtest) rconsts)
  (lambda (env d)
    (if (null? env)
        nil
        (tagcase (cdr (car env))
          (rl-test (n ops v)
            (if (and (string=? n (car d)) (r-same-operands? ops (cdr d)))
                (r-known-as (rc-bool v))
                (r-decided (cdr env) d)))
          (else y (r-decided (cdr env) d))))))
(define r-same-operands? (subr rscans (rlocs rlocs) bool)
  (lambda (xs ys)
    (cond ((null? xs) (null? ys))
          ((null? ys) #f)
          (else (and (r-same-operand? (car xs) (car ys)) (r-same-operands? (cdr xs) (cdr ys)))))))
(define r-same-operand? (subr pure (rloc rloc) bool)
  (lambda (x y)
    (tagcase x
      (rl-reg (i) (tagcase y (rl-reg (j) (= i j)) (else z #f)))
      (rl-slot (i) (tagcase y (rl-slot (j) (= i j)) (else z #f)))
      (rl-free (i) (tagcase y (rl-free (j) (= i j)) (else z #f)))
      (rl-const (c) (tagcase y (rl-const (d) (r-same-const? c d)) (else z #f)))
      (else z #f))))
(define r-same-const? (subr pure (rconst rconst) bool)
  (lambda (c d)
    (tagcase c
      (rc-int (n) (tagcase d (rc-int (m) (= n m)) (else z #f)))
      (rc-bool (v) (tagcase d (rc-bool (w) (eq? v w)) (else z #f)))
      (rc-char (v) (tagcase d (rc-char (w) (char=? v w)) (else z #f)))
      (rc-nil () (tagcase d (rc-nil () #t) (else z #f)))
      (rc-sym (v) (tagcase d (rc-sym (w) (symbol=? v w)) (else z #f)))
      (else z #f))))
;; Whether `name` is a comparison a test's key may be of.
(define r-test-name? (subr pure (string) bool)
  (lambda (name)
    (or (or (or (string=? name "<") (string=? name ">"))
            (or (string=? name "<=") (string=? name ">=")))
        (or (or (string=? name "=") (string=? name "eq?"))
            (or (or (string=? name "symbol=?") (string=? name "char=?"))
                (or (string=? name "null?") (string=? name "pair?")))))))
;; Whether `a` and `b` are the same expression: where they are.
(define r-same-exp? (subr (read (globals exp-end exp-start)) (exp exp) bool)
  (lambda (a b) (and (= (exp-start a) (exp-start b)) (= (exp-end a) (exp-end b)))))
;;; ---------------------------------------------------------------- lists

(define r-count-args (subr rscans (rargs) int)
  (lambda (xs) (if (null? xs) 0 (+ 1 (r-count-args (cdr xs))))))
(define r-exp-args (subr (maxeff (read @globals) (alloc @k)) (exps) rargs)
  (lambda (es) (if (null? es) nil (cons (a-e (car es)) (r-exp-args (cdr es))))))
(define r-arg-simple? (subr rreads (rarg) bool)
  (lambda (a) (tagcase a (a-e (x) (r-simple? x)) (a-thunk (b) #f) (a-as-is (x) #f) (else y #t))))
;; The last argument that is not simple, or -1.
(define r-last-hard (subr rscans (rargs int int) int)
  (lambda (xs i found)
    (if (null? xs) found (r-last-hard (cdr xs) (+ i 1) (if (r-arg-simple? (car xs)) found i)))))
(define r-nth-arg (subr rscans (rargs int) rarg)
  (lambda (xs i) (if (= i 0) (car xs) (r-nth-arg (cdr xs) (- i 1)))))
(define r-in-reg? (subr (read @k) (rlocs) bool)
  (lambda (l) (and (not (null? l)) (tagcase (car l) (rl-reg (r) #t) (else y #f)))))
;; Whether `x` is a variable, not converted, whose value is in a register.
(define r-var-in-reg? (subr rbuilds (renv exp) bool)
  (lambda (env x) (r-in-reg? (r-plain-var-loc env x))))
;; Whether an argument may wait until its value is needed, as
;; `r-arg-simple?` says; past `register-regs`, a list of the rest is made
;; first, which may collect, so then not one in a register.
(define r-arg-simple-here? (subr rbuilds (rarg renv bool) bool)
  (lambda (a env many)
    (and (r-arg-simple? a)
         (or (not many)
             (tagcase a
               (a-e (x) (not (r-var-in-reg? env x)))
               (a-name (n) (not (r-in-reg? (r-where env n))))
               (else y #t))))))
;; A lifted procedure's added name's value into RESULT: a value in a place.
(define r-name (subr rcompiles (rgen symbol renv) unit)
  (lambda (g n env)
    (let ((l (r-where env n)))
      (if (null? l)
          (r-decline)
          (tagcase (car l)
            (rl-slot (s) (r-opn g rop-stack s))
            (rl-reg (r) (r-opn g rop-reg r))
            (rl-free (j) (r-opn g rop-lexical j))
            (rl-const (c) (r-op1 g rop-const (r-const-cell c)))
            (else y (r-decline)))))))
(define r-nth-int (subr rscans ((listof int @k) int) int)
  (lambda (xs i) (if (= i 0) (car xs) (r-nth-int (cdr xs) (- i 1)))))
(define r-nth-exp (subr (read @globals) (exps int) exp)
  (lambda (es i) (if (= i 0) (car es) (r-nth-exp (cdr es) (- i 1))))))))
