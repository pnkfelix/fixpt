;;; The compiler written in FX-26: lambda lifting, and the standard
;;; operations. After `compile.fx`.

;;; ------------------------------------------------------ lambda lifting
;;; As the Rust compiler's `lift`, `lift_plan` and `called_only`.

;; A module (`TODO.md` §34: the front end into modules, a file at a time);
;; what other files use re-exported after it.
(define compile-lift-module (module
;; While a `letrec` is planned to be lifted, by member: the names each
;; takes, and the siblings each calls.
(define-type c-added (arrayof syms @k))

(define-type c-calls (arrayof (listof int @k) @k))

;; A `letrec`'s key in `c-lifted`: where it starts and ends.
(define c-span-key (subr pure (int int) int) (lambda (a b) (+ (* a 4194304) b)))

;; The index in `c-lifts` of the procedure `n` names in `e`, if a lifted
;; one; else -1.
(define c-lifted-index (subr c-walks (symbol cenv) int)
  (lambda (n e)
    (let ((l (c-find e n)))
      (if (null? l) -1 (tagcase (car l) (at-lifted (k) k) (else y -1))))))

(define c-lifted-at (subr c-walks (exp cenv) int)
  (lambda (f e) (tagcase f (e-var (n a b) (c-lifted-index n e)) (else y -1))))

;; Lifted procedure `k`, from `c-lifts`.
(define c-lift-of (subr (maxeff (read @globals) (read @k)) (int) c-lift)
  (lambda (k)
    (table-ref (get c-lifts) k (the c-lift (product (1 (wcell-nil)) (2 (the syms nil)))))))

;; A lifted procedure's added names.
(define c-lift-added (subr (maxeff (read @globals) (read @k)) (int) syms)
  (lambda (k) (extract (c-lift-of k) 2)))

;; The lifted procedures `e` binds, as it binds them: known everywhere
;; inside a lambda, being constants.
(define c-lifted-entries (subr c-walks (cenv) cenv)
  (lambda (e)
    (cond ((null? e) nil)
          ((c-lifted? (cdr (car e))) (the cenv (cons (car e) (c-lifted-entries (cdr e)))))
          (else (c-lifted-entries (cdr e))))))

;;; ------------------------------------------- the middle phase's plan
;;; Before a top-level form is compiled, `compile-plan.fx` decides each
;;; lambda's captured names and each `letrec`'s lifting
;;; (`docs/research/compiler-middle-phase.md`, step 2), as the Rust
;;; compiler's `cellular/procs.rs`; the stack code reads them here.

;; A lambda as planned: its parameters' names, and the names it captures.
(define-type c-planned (productof (1 syms) (2 syms)))
(define-type c-planneds (listof c-planned @k))
;; The form's lambdas, by where their bodies are (`c-span-key`), each with
;; its parameters' names (a `define-datatype`'s constructors share their
;; form's place); its `letrec`s' liftings, by where they are: none if not
;; lifted, else each member's added names, as `c-lift-plan` gives them.
(define c-plan-procs (ref (table int c-planneds @k) @k) (new (make-table c-int-hash c-int=?)))
(define c-plan-lifts (ref (table int (listof c-added @k) @k) @k)
  (new (make-table c-int-hash c-int=?)))
;; Whether a plan is in force; and how deep in register code the compile is,
;; whose own lambdas (an inlined body, a specialized copy) are not planned.
(define c-planning (ref bool @k) (new #f))
(define c-twin-depth (ref int @k) (new 0))
;; Whether the register code being made is a planned lambda's, of the form
;; being compiled (step 3): its call sites are the plan's.
(define c-r-in-plan (ref bool @k) (new #f))
;; Whether it is making a specialized copy where the plan's calls are: the
;; copy's twin's are too (3b).
(define c-r-copying (ref bool @k) (new #f))
(define c-planned-in (subr c-walks (c-planneds syms) c-planneds)
  (lambda (ps names)
    (cond ((null? ps) nil)
          ((k-syms=? (extract (car ps) 1) names) (the c-planneds (cons (car ps) nil)))
          (else (c-planned-in (cdr ps) names)))))
;; What the lambda of `ps` and `body` captures, as planned, in a list; none
;; where it was not planned, or in register code.
(define c-planned-fv (subr c-walks (c-params exp) (listof syms @k))
  (lambda (ps body)
    (if (or (not (get c-planning)) (> (get c-twin-depth) 0))
        nil
        (let ((found (c-planned-in (table-ref (get c-plan-procs)
                                              (c-span-key (exp-start body) (exp-end body))
                                              (the c-planneds nil))
                                   (c-bind-params ps nil))))
          (if (null? found) nil (the (listof syms @k) (cons (extract (car found) 2) nil)))))))
;; Whether the `letrec` at `a`-`b` is lifted, as planned, in a list: of what
;; `c-lift-plan` would give; none where it was not planned, or in register
;; code.
(define c-planned-lift (subr c-walks (int int) (listof (listof c-added @k) @k))
  (lambda (a b)
    (let ((key (c-span-key a b)))
      (if (or (not (get c-planning)) (> (get c-twin-depth) 0)
              (not (table-has? (get c-plan-lifts) key)))
          nil
          (the (listof (listof c-added @k) @k)
               (cons (table-ref (get c-plan-lifts) key (the (listof c-added @k) nil)) nil))))))

;; Each of `ns`' values pushed, from where `e` has it.
(define c-load-names (subr (maxeff compiles spin) (syms cenv code) unit)
  (lambda (ns e c)
    (if (null? ns)
        #u
        (let ((l (c-where e (car ns))))
          (begin (if (null? l)
                     (c-fail "a lifted procedure's added name is not bound")
                     (c-load c (car l)))
                 (c-load-names (cdr ns) e c))))))

(define c-snoc (subr c-walks (syms symbol) syms)
  (lambda (xs n) (if (null? xs) (cons n nil) (cons (car xs) (c-snoc (cdr xs) n)))))

;; `acc` with each of `ns` in neither it nor `params` after it, in order.
(define c-append-new (subr c-walks (syms syms syms) syms)
  (lambda (ns acc params)
    (cond ((null? ns) acc)
          ((or (c-member? acc (car ns)) (c-member? params (car ns)))
           (c-append-new (cdr ns) acc params))
          (else (c-append-new (cdr ns) (c-snoc acc (car ns)) params)))))

(define c-lifted-names-onto (subr c-walks (syms syms syms cenv) syms)
  (lambda (xs acc params e)
    (if (null? xs)
        acc
        (let* ((k (c-lifted-index (car xs) e))
               (more (if (< k 0) acc (c-append-new (c-lift-added k) acc params))))
          (c-lifted-names-onto (cdr xs) more params e)))))

;; `free` with, for each lifted procedure in it, the names its calls pass
;; (not `params`) after: code that calls one needs them too.
(define c-with-lifted-names (subr c-walks (syms syms cenv) syms)
  (lambda (free params e) (c-lifted-names-onto free free params e)))

;; Whether every binding of `bs`, from the `i`th, is a join point.
(define c-all-join? (subr c-walks (c-recs exp int) bool)
  (lambda (bs body i)
    (or (>= i (c-count-letrec bs)) (and (c-join-ok? bs body i) (c-all-join? bs body (+ i 1))))))

;; Whether each member of `bs` is a plain lambda, only ever called, with
;; its arity, in `body` and in every binding of `all`.
(define c-liftable? (subr c-walks (c-recs c-recs exp) bool)
  (lambda (all bs body)
    (or (null? bs)
        (let ((lam (c-lambda-of (extract (car bs) 3))))
          (and (not (null? lam))
               (tagcase (car lam)
                 (e-lambda (ps lbody a b)
                   (let ((name (extract (car bs) 1)) (n (c-count-params ps)))
                     (and (c-called-only body name n)
                          (c-calls-only-all (c-rec-exps all) name n #f)
                          (c-liftable? all (cdr bs) body))))
                 (else y #f)))))))

;; The locals of `free` (not `names`, the siblings) a member would capture,
;; onto `acc`, in a list of one; none if one is a sibling not made yet or a
;; loop, which cannot be passed.
(define c-lift-locals (subr c-walks (syms syms cenv syms) (listof syms @k))
  (lambda (free names e acc)
    (cond ((null? free) (the (listof syms @k) (cons acc nil)))
          ((c-member? names (car free)) (c-lift-locals (cdr free) names e acc))
          (else
           (let ((l (c-find e (car free))))
             (if (null? l)
                 (c-lift-locals (cdr free) names e acc)
                 (tagcase (car l)
                   (at-slot (i) (c-lift-locals (cdr free) names e (cons (car free) acc)))
                   (at-free (i) (c-lift-locals (cdr free) names e (cons (car free) acc)))
                   (at-pending (i) (the (listof syms @k) nil))
                   (at-loop (z) (the (listof syms @k) nil))
                   (else y (c-lift-locals (cdr free) names e acc)))))))))

;; The indices of the bindings of `bs`, from the `k`th, whose names are in
;; `free`: the siblings a member calls.
(define c-sibling-indices (subr c-walks (syms c-recs int) (listof int @k))
  (lambda (free bs k)
    (cond ((null? bs) nil)
          ((c-member? free (extract (car bs) 1)) (cons k (c-sibling-indices free (cdr bs) (+ k 1))))
          (else (c-sibling-indices free (cdr bs) (+ k 1))))))

;; Each member's locals into `added`, the siblings it calls into `calls`,
;; from the `i`th of `bs`; whether every member's could be.
(define c-lift-direct
  (subr (maxeff c-emits spin) (c-recs c-recs int syms cenv c-added c-calls) bool)
  (lambda (all bs i names e added calls)
    (or (null? bs)
        (tagcase (car (c-lambda-of (extract (car bs) 3)))
          (e-lambda (ps lbody a b)
            (let* ((params (c-bind-params ps nil))
                   (free (c-with-lifted-names (c-free lbody params nil) params e))
                   (mine (c-lift-locals free names e nil)))
              (and (not (null? mine))
                   (begin (array-set! added i (car mine))
                          (array-set! calls i (c-sibling-indices free all 0))
                          (c-lift-direct all (cdr bs) (+ i 1) names e added calls)))))
          (else y #f)))))

(define c-union-into (subr c-walks (syms syms) syms)
  (lambda (xs ys) (if (null? ys) xs (c-union-into (c-adjoin xs (car ys)) (cdr ys)))))

;; Member `i` takes what the siblings `js` it calls take too; whether it
;; took more than it had (`more`).
(define c-lift-from (subr (maxeff c-emits spin) (c-added int (listof int @k) bool) bool)
  (lambda (added i js more)
    (if (null? js)
        more
        (let* ((had (array-ref added i))
               (now (c-union-into had (array-ref added (car js))))
               (grew (not (= (c-length now) (c-length had)))))
          (begin (array-set! added i now)
                 (c-lift-from added i (cdr js) (or more grew)))))))

(define c-lift-round (subr (maxeff c-emits spin) (c-added c-calls int int bool) bool)
  (lambda (added calls i n more)
    (if (>= i n)
        more
        (c-lift-round added calls (+ i 1) n (c-lift-from added i (array-ref calls i) more)))))

;; Twobit's flow equations (`compute-added-arguments`), to their fixed
;; point: each member takes its locals, and what each sibling it calls
;; takes.
(define c-lift-flow (subr (maxeff c-emits spin) (c-added c-calls int) unit)
  (lambda (added calls n) (if (c-lift-round added calls 0 n #f) (c-lift-flow added calls n) #u)))

;; Where `n` is bound in `e`, counting from the innermost.
(define c-env-pos (subr (maxeff (read @globals) (read @k) spin) (cenv symbol int) int)
  (lambda (e n k)
    (cond ((null? e) k)
          ((symbol=? (car (car e)) n) k)
          (else (c-env-pos (cdr e) n (+ k 1))))))

(define c-insert-outer (subr c-walks (symbol syms cenv) syms)
  (lambda (x ys e)
    (cond ((null? ys) (cons x nil))
          ((> (c-env-pos e x 0) (c-env-pos e (car ys) 0)) (cons x ys))
          (else (cons (car ys) (c-insert-outer x (cdr ys) e))))))

;; `xs`, outermost binding first.
(define c-sort-outer (subr c-walks (syms cenv) syms)
  (lambda (xs e) (if (null? xs) nil (c-insert-outer (car xs) (c-sort-outer (cdr xs) e) e))))

(define c-lift-sort (subr (maxeff c-emits spin) (c-added cenv int int) unit)
  (lambda (added e i n)
    (if (>= i n)
        #u
        (begin (array-set! added i (c-sort-outer (array-ref added i) e))
               (c-lift-sort added e (+ i 1) n)))))

;; Whether each member, from the `i`th of `bs`, takes fewer than 6 names
;; more, and no more than `register-regs` arguments in all.
(define c-lift-fits? (subr c-walks (c-recs c-added int) bool)
  (lambda (bs added i)
    (or (null? bs)
        (tagcase (car (c-lambda-of (extract (car bs) 3)))
          (e-lambda (ps lbody a b)
            (let ((m (c-length (array-ref added i))))
              (and (< m 6)
                   (<= (+ m (c-count-params ps)) register-regs)
                   (c-lift-fits? (cdr bs) added (+ i 1)))))
          (else y #f)))))

;; Whether to lift a `letrec` (`c-lift`), as the Rust compiler's `lift_plan`
;; decides: none if not; else, in a list of one, each member's added names.
;; Lifted where every member is a plain lambda only ever called, with its
;; arity; where the group is not join points (register code's jumps,
;; better still); and where each member takes fewer than 6 names more
;; (Twobit's bound, `POLICY:LIFT?`) and no more than `register-regs`
;; arguments in all. The names a member takes: the locals it would
;; capture, and those of each sibling it calls (Twobit's flow equations);
;; outermost first.
(define c-lift-plan
  (subr (maxeff c-emits spin)
        (c-recs exp cenv bool) (listof c-added @k))
  (lambda (bs body e tail)
    (if (or (and tail (c-all-join? bs body 0)) (not (c-liftable? bs bs body)))
        nil
        (let* ((n (c-count-letrec bs))
               (added (the c-added (make-array n nil)))
               (calls (the c-calls (make-array n nil))))
          (if (not (c-lift-direct bs bs 0 (c-bind-letrec bs nil) e added calls))
              nil
              (begin
                (c-lift-flow added calls n)
                (c-lift-sort added e 0 n)
                (if (c-lift-fits? bs added 0) (the (listof c-added @k) (cons added nil)) nil)))))))

;; `bs`' names bound to the lifted procedures `ks`, onto `e`.
(define c-bind-lifted (subr c-walks (c-recs (listof int @k) cenv) cenv)
  (lambda (bs ks e)
    (if (null? bs)
        e
        (c-bind-lifted (cdr bs) (cdr ks) (c-extend (extract (car bs) 1) (at-lifted (car ks)) e)))))

;; The names `added` as parameters (with no type), then `ps`.
(define c-added-params (subr c-walks (syms c-params) c-params)
  (lambda (added ps)
    (if (null? added)
        ps
        (cons (product (1 (car added)) (2 (the syns-a nil))) (c-added-params (cdr added) ps)))))

;; A closure over nothing for each member, from the `i`th, its word to
;; come, in `c-lifts` with what it takes: their indices.
(define c-lift-closures (subr (maxeff c-emits spin) (c-recs c-added int) (listof int @k))
  (lambda (bs added i)
    (if (null? bs)
        nil
        (let* ((k (get c-lift-count))
               (lift (the c-lift (product (1 (wcell-closure)) (2 (array-ref added i))))))
          (begin
            (table-set! (get c-lifts) k lift)
            (set c-lift-count (+ k 1))
            (cons k (c-lift-closures (cdr bs) added (+ i 1))))))))

(define c-param-env (subr (maxeff (read @globals) (alloc @k)) (c-params int cenv) cenv)
  (lambda (ps i acc)
    (if (null? ps)
        acc
        (c-param-env (cdr ps) (+ i 1) (c-extend (extract (car ps) 1) (at-slot i) acc)))))

;; Whether a name found at `l` (none: a standard name) is no local that a
;; closure captures: a loop, which is not a value; or a global or a lifted
;; procedure, a constant (a definition's own global, in its body's names,
;; is still a global).
(define c-not-captured? (subr (maxeff (read @globals) (read @k)) (c-found) bool)
  (lambda (l) (or (null? l) (c-loop? (car l)) (c-global? (car l)) (c-lifted? (car l)))))

;; The free names that are locals here, not globals or standard names, nor
;; a loop, which is not a value.
(define c-captured (subr c-walks (syms cenv) syms)
  (lambda (xs e)
    (cond ((null? xs) nil)
          ((c-not-captured? (c-find e (car xs))) (c-captured (cdr xs) e))
          (else (cons (car xs) (c-captured (cdr xs) e))))))

;; The names a lambda of `ps` and `body` captures in `e`, as the Rust
;; compiler's `captured` finds them: its free locals, and the names the
;; lifted procedures it calls take.
(define c-lambda-captured (subr c-walks (c-params exp cenv) syms)
  (lambda (ps body e)
    (let ((params (c-bind-params ps nil)))
      (c-captured (c-with-lifted-names (c-free body params nil) params e) e))))

;; Free value `i` for each captured name, boxed if it was boxed outside.
(define c-inner-env (subr c-walks (syms cenv cenv int) cenv)
  (lambda (xs outer acc i)
    (if (null? xs)
        acc
        (c-inner-env (cdr xs) outer (c-extend (car xs) (at-free i) acc) (+ i 1)))))

;;; -------------------------------------------------- standard operations

;; How many arguments a standard operation takes, or -1 if it is not one.
(define c-arity (subr (read (globals standard-primitive std-eq-name?)) (string) int)
  (lambda (n)
    (cond ((or (string=? n "make-continuation-prompt-tag")
               (string=? n "make-continuation-mark-key"))
           0)
          ((or (string=? n "car") (string=? n "cdr") (string=? n "null?") (string=? n "not")
               (string=? n "new") (string=? n "get") (string=? n "char->integer")
               (string=? n "integer->char") (string=? n "string-length") (string=? n "char->string")
               (string=? n "symbol->string") (string=? n "string->symbol")
               (string=? n "array-length") (string=? n "current-marks") (string=? n "cwcc"))
           1)
          ((or (string=? n "with-mark") (string=? n "array-set!") (string=? n "substring")) 3)
          ((or (string=? n "+") (string=? n "-") (string=? n "*") (string=? n "<") (string=? n ">")
               (string=? n "<=") (string=? n ">=") (string=? n "=") (string=? n "modulo")
               (string=? n "quotient") (string=? n "cons") (string=? n "set-car!")
               (string=? n "set-cdr!") (string=? n "char=?") (string=? n "string-append")
               (string=? n "string=?") (std-eq-name? n)
               (string=? n "array-ref") (string=? n "string-ref") (string=? n "make-array")
               (string=? n "abort-current-continuation") (string=? n "set") (string=? n "marks-of")
               (string=? n "call-with-composable-continuation") (string=? n "first-mark"))
           2)
          ;; The rest: the arity of the runtime primitive it runs as, if that
          ;; takes a fixed number (`char-downcase`).
          (else
           (let ((p (standard-primitive n)))
             (if (or (string=? p "") (string=? p "%fx26-identity"))
                 -1
                 (runtime-primitive-arity p)))))))

;; The boolean on top negated.
(define c-not (subr c-emits (code) unit)
  (lambda (c) (begin (c-lit c (wcell-bool #f)) (c-op c routine-eq))))

;; The index on top made the field it is in an array, whose elements are
;; its fields from 2 on.
(define c-array-index (subr c-emits (code) unit)
  (lambda (c) (begin (c-int c 2) (c-op c routine-int-add))))

(define c-standard-on (subr compiles (string int code) unit)
  (lambda (name n c)
    (cond ((string=? name "+") (c-op c routine-int-add))
          ((string=? name "-") (c-op c routine-int-sub))
          ((string=? name "<") (c-op c routine-int-less))
          ((string=? name ">") (begin (c-op c routine-swap) (c-op c routine-int-less)))
          ((string=? name "<=") (begin (c-op c routine-swap) (c-op c routine-int-less) (c-not c)))
          ((string=? name ">=") (begin (c-op c routine-int-less) (c-not c)))
          ;; Ints may be bignums, compared by value; characters are immediates, so compared as
          ;; symbols are.
          ((string=? name "=") (c-op c routine-int-eq))
          ((std-eq-name? name) (c-op c routine-eq))
          ((string=? name "cons") (c-op c routine-cons))
          ((string=? name "car") (c-op c routine-pair-car))
          ((string=? name "cdr") (c-op c routine-pair-cdr))
          ((or (string=? name "set-car!") (string=? name "set-cdr!"))
           (begin (c-prim c name 2) (c-unit-after c)))
          ((string=? name "new") (c-prim c "%make-box" 1))
          ;; A reference is a box: its value is field 2.
          ((string=? name "get") (c-field c 2))
          ((string=? name "set")
           (begin (c-op c routine-swap) (c-field-set c 2) (c-lit c (wcell-unit))))
          ((string=? name "null?") (begin (c-lit c (wcell-nil)) (c-op c routine-eq)))
          ((string=? name "not") (c-not c))
          ((string=? name "char->string") (c-prim c "string" 1))
          ;; A tag or a key: a fresh object, compared by identity.
          ((or (string=? name "make-continuation-prompt-tag")
               (string=? name "make-continuation-mark-key"))
           (begin (c-lit c (wcell-unit)) (c-prim c "%make-box" 1)))
          ((string=? name "abort-current-continuation") (c-op c routine-abort))
          ((string=? name "call-with-composable-continuation") (c-op c routine-callcomp))
          ((string=? name "cwcc") (c-op c routine-callcc))
          ((string=? name "with-mark") (c-op c routine-withmark))
          ((string=? name "first-mark") (c-op c routine-firstmark))
          ((string=? name "current-marks") (c-op c routine-currentmarks))
          ((string=? name "marks-of") (c-op c routine-marksof))
          ((string=? name "array-ref") (begin (c-array-index c) (c-op c routine-field-ref)))
          ((string=? name "array-set!")
           (begin (c-op c routine-swap) (c-array-index c) (c-op c routine-swap)
                  (c-prim c "%bloblet-set!" 3) (c-unit-after c)))
          ;; `(apply f xs)`: `f` is a `vsubr`, a closure of `%vlambda`'s over the
          ;; procedure of one list, free value 0; that procedure, called with `xs`.
          ((string=? name "apply")
           (begin (c-op c routine-swap) (c-field c cellular-closure-free0)
                  (c-op1 c routine-tcall (wcell-int 1))))
          ((string=? name "array-length")
           (begin (c-prim c "%bloblet-fields" 1) (c-int c 1) (c-op c routine-int-sub)))
          ((or (string=? name "modulo") (string=? name "char->integer")
               (string=? name "integer->char") (string=? name "string-append")
               (string=? name "string-length") (string=? name "string-ref")
               (string=? name "substring") (string=? name "string=?")
               (string=? name "string->symbol") (string=? name "symbol->string"))
           (c-prim c name n))
          ;; The rest, as the lowering runs them (`standard.fx`): a
          ;; runtime primitive, or nothing at all.
          (else
           (let ((p (standard-primitive name)))
             (cond ((string=? p "%fx26-identity") #u)
                   ((string=? p "") (c-fail (string-append "not yet compiled: " name)))
                   (else (c-prim c p n))))))))

;; Whether a standard name has a value: an operation of an arity, or `list`,
;; a `vsubr`.
(define* c-has-standard-value? (subr pure (string) bool)
  (lambda (n) (or (string=? n "list") (>= (c-arity n) 0))))

;; Word `w`, with register code as standard operation `op` of `n` arguments
;; has it as a value, for the native compiler to start from.
(define c-register-twin (subr (maxeff compiles spin) (tword string int) tword)
  (lambda (w op n)
    (begin
      (if (get c-registers)
          (let ((cells ((get c-standard-register-code) op n)))
            (if (null? cells) #u (begin (set-register-twin w cells) #u)))
          #u)
      w)))

;; A closure, over no values, of `body` assembled as the word `name`, with
;; register code as standard operation `op` of `n` arguments has it.
(define c-standard-closure (subr (maxeff compiles spin) (code code string string int) unit)
  (lambda (c body name op n)
    (let ((w (c-register-twin (c-assemble body (string->symbol name)) op n)))
      (begin (c-op1 c routine-closure (wcell-word w)) (c-emit c (i-cell (wcell-int 0)))))))
;; A standard operation as a value: a closure of its arity whose body
;; applies it to its parameters. `list` is a `vsubr`: `%vlambda`'s closure
;; over a procedure of one list that copies it, as `datum-list` does (and its
;; register code is `datum-list`'s). A copy, not the list itself: `apply`
;; gives a list at `acyclic` as it is (F11), and `list` may give it at any
;; region, one that can be written.
(define c-standard-value (subr (maxeff compiles spin) (string code) unit)
  (lambda (name c)
    (let ((n (c-arity name)) (body (the code (new nil))))
      (cond ((string=? name "list")
             (begin
               (c-op1 body routine-slot (wcell-int 0))
               (c-standard-on "datum-list" 1 body)
               (c-op body routine-return)
               (c-standard-closure c body name "datum-list" 1)
               (c-prim c "%fx26-vlambda" 1)))
            ((< n 0) (c-fail (string-append "not yet compiled as a value: " name)))
            (else
             (begin
               (letrec ((params (subr (maxeff c-emits spin) (int) unit)
                          (lambda (i)
                            (if (= i n)
                                #u
                                (begin (c-op1 body routine-slot (wcell-int i)) (params (+ i 1)))))))
                 (if (string=? name "make-array")
                     (begin (c-int body 0) (params 0) (c-prim body "%make-bloblet-filled" 3))
                     (begin (params 0) (c-standard-on name n body))))
               (c-op body routine-return)
               (c-standard-closure c body name name n)))))))

(define c-count-names (subr (read @globals) (names) int)
  (lambda (ns) (if (null? ns) 0 (+ 1 (c-count-names (cdr ns))))))

;; A product's members, from the slot after the sum's, each a slot.
(define c-members (subr compiles (names cenv int int int code) cenv)
  (lambda (ns e sum-slot slot j c)
    (if (null? ns)
        e
        (begin (c-op1 c routine-slot (wcell-int (+ sum-slot 1)))
               (c-field c (+ j 2))
               (c-members (cdr ns) (c-extend (car ns) (at-slot slot) e)
                          sum-slot (+ slot 1) (+ j 1) c)))))))

(define c-span-key (with compile-lift-module c-span-key))
(define c-lifted-at (with compile-lift-module c-lifted-at))
(define c-lift-of (with compile-lift-module c-lift-of))
(define c-lift-added (with compile-lift-module c-lift-added))
(define c-lifted-entries (with compile-lift-module c-lifted-entries))
(define c-load-names (with compile-lift-module c-load-names))
(define c-lift-plan (with compile-lift-module c-lift-plan))
(define c-bind-lifted (with compile-lift-module c-bind-lifted))
(define c-added-params (with compile-lift-module c-added-params))
(define c-lift-closures (with compile-lift-module c-lift-closures))
(define c-param-env (with compile-lift-module c-param-env))
(define c-lambda-captured (with compile-lift-module c-lambda-captured))
(define c-inner-env (with compile-lift-module c-inner-env))
(define c-standard-on (with compile-lift-module c-standard-on))
(define c-has-standard-value? (with compile-lift-module c-has-standard-value?))
(define c-standard-value (with compile-lift-module c-standard-value))
(define c-count-names (with compile-lift-module c-count-names))
(define c-members (with compile-lift-module c-members))
(define-type c-added (select compile-lift-module c-added))
(define-type c-planned (select compile-lift-module c-planned))
(define-type c-planneds (select compile-lift-module c-planneds))
(define c-plan-procs (with compile-lift-module c-plan-procs))
(define c-plan-lifts (with compile-lift-module c-plan-lifts))
(define c-planning (with compile-lift-module c-planning))
(define c-twin-depth (with compile-lift-module c-twin-depth))
(define c-planned-fv (with compile-lift-module c-planned-fv))
(define c-planned-lift (with compile-lift-module c-planned-lift))
(define c-r-in-plan (with compile-lift-module c-r-in-plan))
(define c-r-copying (with compile-lift-module c-r-copying))
