;;; The compiler written in FX-26: what compiling expressions keeps and
;;; uses. The words being made and their names, a module's members and
;;; values, the twins registered, quotations, and modules reshaped. After
;;; `compile-lift.fx`; `compile-exps.fx` uses it (split from that file,
;;; `TODO.md` §68).

;; Its types, those it uses of the files before it, and the signatures of
;; what it is given.
;; Its types (`compile-exps-types.fx`, its file's after it), loaded before the
;; module so that they are not among its values; the module names what it
;; uses of them.
(let* ((compile-exps-types (load-module "fx26:compile-exps-types.fx"))
       (compile-types (load-module "fx26:compile-types.fx"))
       (parser-types ((proj (load-module "fx26:parser-types.fx") @s @e @m @c @p)))
       (reader-types ((proj (load-module "fx26:eager-reader-types.fx") @s @e @m @c)))
       (check-types-types (load-module "fx26:check-types-types.fx"))
       (compile-lift-types (load-module "fx26:compile-lift-types.fx"))
       (layout-types (load-module "fx26:layout-types.fx"))
       (check-resolve-types (load-module "fx26:check-resolve-types.fx"))
       (check-program-types (load-module "fx26:check-program-types.fx"))
       (check-proofs-types (load-module "fx26:check-proofs-types.fx")))
  ;; What it is given: the modules of the files before it that it uses.
  (lambda ((compile (select compile-types compile-sig))
           (compile-lift (select compile-lift-types compile-lift-sig))
           (layout (select layout-types layout-sig))
           (check-resolve (select check-resolve-types check-resolve-sig))
           (check-program (select check-program-types check-program-sig))
           (check-proofs (select check-proofs-types check-proofs-sig)))
    (module
(define-type c-inlinables (select compile-exps-types c-inlinables))
(define-type c-mvals (select compile-exps-types c-mvals))
(define-type c-mslots (select compile-exps-types c-mslots))
(define-type c-waits (select compile-exps-types c-waits))
(define-type c-made (select compile-exps-types c-made))
(define-type c-closing (select compile-exps-types c-closing))
(define-type c-spec (select compile-exps-types c-spec))
(define-type c-copy-twin (select compile-exps-types c-copy-twin))
(define-type c-twin (select compile-exps-types c-twin))
;; The types it uses of the files before it.
(define at-free (with compile-types at-free))
(define at-global (with compile-types at-global))
(define at-lifted (with compile-types at-lifted))
(define at-loop (with compile-types at-loop))
(define at-pending (with compile-types at-pending))
(define at-slot (with compile-types at-slot))
(define-effect c-builds (select compile-types c-builds))
(define-effect c-emits (select compile-types c-emits))
(define-type c-params (select compile-types c-params))
(define-type c-this (select compile-types c-this))
(define-effect c-walks (select compile-types c-walks))
(define-type cenv (select compile-types cenv))
(define-type code (select compile-types code))
(define-effect compiles (select compile-types compiles))
(define-type exps (select compile-types exps))
(define-type items (select compile-types items))
(define-type loc (select compile-types loc))
(define-type patches (select compile-types patches))
(define-type syms (select compile-types syms))
(define e-app (with parser-types e-app))
(define e-bool (with parser-types e-bool))
(define e-char (with parser-types e-char))
(define e-int (with parser-types e-int))
(define e-lambda (with parser-types e-lambda))
(define e-plambda (with parser-types e-plambda))
(define e-rlambda (with parser-types e-rlambda))
(define e-sym (with parser-types e-sym))
(define e-the (with parser-types e-the))
(define e-var (with parser-types e-var))
(define e-with (with parser-types e-with))
(define-type exp (select parser-types exp))
(define-type mod-items (select parser-types mod-items))
(define-type names (select parser-types names))
(define-type word (select reader-types word))
(define-type k-ids (select check-types-types k-ids))
;; What it uses of the modules it is given.
(define c-bind-params (with compile c-bind-params))
(define c-converter (with compile c-converter))
(define c-count-exps (with compile c-count-exps))
(define c-extend (with compile c-extend))
(define c-fail (with compile c-fail))
(define c-field (with compile c-field))
(define c-field-set (with compile c-field-set))
(define c-find (with compile c-find))
(define c-free (with compile c-free))
(define c-genv-now (with compile c-genv-now))
(define c-global? (with compile c-global?))
(define c-has-param? (with compile c-has-param?))
(define c-lambda-of (with compile c-lambda-of))
(define c-lit (with compile c-lit))
(define c-load (with compile c-load))
(define c-loops-only (with compile c-loops-only))
(define c-member? (with compile c-member?))
(define c-op (with compile c-op))
(define c-op1 (with compile c-op1))
(define c-place-name (with compile c-place-name))
(define c-registers (with compile c-registers))
(define c-this-added (with compile c-this-added))
(define c-this-loc (with compile c-this-loc))
(define c-this-loc? (with compile c-this-loc?))
(define c-this-name (with compile c-this-name))
(define c-this-params (with compile c-this-params))
(define c-this-start (with compile c-this-start))
(define c-where (with compile c-where))
(define c-lambda-captured (with compile-lift c-lambda-captured))
(define c-lifted-entries (with compile-lift c-lifted-entries))
(define cellular-closure-free0 (with layout cellular-closure-free0))
(define routine-drop (with layout routine-drop))
(define routine-free (with layout routine-free))
(define routine-slot (with layout routine-slot))
(define routine-slot! (with layout routine-slot!))
(define routine-tcall (with layout routine-tcall))
(define routine-ttailcall (with layout routine-ttailcall))
(define exp-end (with check-resolve exp-end))
(define exp-start (with check-resolve exp-start))
(define k-syms=? (with check-proofs k-syms=?))

;; Each captured name's value, as the closure will hold it, free value `j`
;; on; a sibling not made yet is a placeholder, and one of the patches.
(define c-push-all (subr (maxeff compiles spin) (syms cenv int int code) patches)
  (lambda (xs e depth j c)
    (if (null? xs)
        nil
        (let* ((l (car (c-find e (car xs))))
               (pending (tagcase l
                          (at-slot (i) (begin (c-op1 c routine-slot (wcell-int i)) -1))
                          (at-free (i) (begin (c-op1 c routine-free (wcell-int i)) -1))
                          (at-pending (s) (begin (c-lit c (wcell-bool #f)) s))
                          (at-global (g) (c-fail "a global is not captured"))
                          (at-loop (z) (c-fail "a loop is not captured"))
                          (at-lifted (k) (c-fail "a lifted procedure is not captured"))))
               (rest (c-push-all (cdr xs) e (+ depth 1) (+ j 1) c)))
          (if (< pending 0) rest (the patches (cons (cons j pending) rest)))))))

(define c-self-call? (subr c-walks (exp exps cenv bool) bool)
  (lambda (f args e tail)
    (and tail
         (>= (get c-this-params) 0)
         (tagcase f
           (e-var (n a b)
             (and (symbol=? n (get c-this-name))
                  (let ((l (c-find e n)))
                    (and (not (null? l))
                         (c-this-loc? (car l) (get c-this-loc))
                         (= (+ (get c-this-added) (c-count-exps args)) (get c-this-params))))))
           (else y #f)))))

;; Into the parameters' slots, from `i` down to `lo` (those below, a
;; lifting's, passed on as they are).
(define c-loop-stores (subr c-emits (code int int) unit)
  (lambda (c i lo)
    (if (< i lo) #u (begin (c-op1 c routine-slot! (wcell-int i)) (c-loop-stores c (- i 1) lo)))))

(define c-drops (subr c-emits (code int) unit)
  (lambda (c k) (if (<= k 0) #u (begin (c-op c routine-drop) (c-drops c (- k 1))))))

;; The top-level definition whose lambda is compiled next: its name, in a
;; list; and, for the register compiler, the lambda being so compiled: its
;; name and word.
(define c-defining (ref (listof symbol @k) @k) (new nil))

(define c-own-now (ref (listof (productof (1 symbol) (2 tword)) @k) @k) (new nil))

;; The name the next lambda's word gets, if not where its body starts.
(define c-word-name (ref (listof string @k) @k) (new nil))
;; The name of the lambda whose body is compiled, without where it starts:
;; an inner lambda's word is named within it, `outer/inner@N`.
(define c-scope-name (ref (listof string @k) @k) (new nil))
;; While a `let`'s binding's init is compiled, the binding's name: the first
;; lambda compiled in it is named for it.
(define c-bind-name (ref (listof symbol @k) @k) (new nil))

;; The word of the lambda compiled last, in a list; and of the one before.
(define c-last-word (ref (listof tword @k) @k) (new nil))

(define c-prev-word (ref (listof tword @k) @k) (new nil))

;; A top-level `(define m (module …))`'s members that are lambdas naming no
;; other member, each as a `c-inline`, to be inlined, if small, where a
;; re-export `(define f (with m f))` is called (`TODO.md` §38), as the Rust
;; compiler's `module_members`: in `c-module-members` between the
;; definition and its module, a list of one list; in `c-collecting` while
;; that module's own items are compiled, a module inside one of them noting
;; nothing.
(define c-module-members (ref (listof c-inlinables @k) @k) (new nil))
(define c-collecting (ref (listof c-inlinables @k) @k) (new nil))
;; Member `n` noted, its value `x` just compiled where `e` is in scope, if
;; it is a lambda naming no other member.
(define c-note-member! (subr (maxeff c-walks (write @k)) (symbol exp cenv) unit)
  (lambda (n x e)
    (let ((ms (get c-collecting)) (l (c-lambda-of x)))
      (if (or (null? ms) (null? l))
          #u
          (tagcase (car l)
            (e-lambda (ps body a b)
              (if (null? (c-lambda-captured ps body e))
                  (let* ((word (car (get c-last-word)))
                         (it (product (1 n) (2 word) (3 ps) (4 body) (5 (c-genv-now)))))
                    (set c-collecting (the (listof c-inlinables @k)
                                        (list (the c-inlinables (cons it (car ms)))))))
                  #u))
            (else y #u))))))

;;; ---------------------------------------------------------- modules
;;; A module's items are made in slots in order, as a `letrec*`'s
;;; (`DONE.md` §37): a typed lambda naming an item not made yet captures it
;;; once it is made, as a `letrec`'s siblings are. The Rust compiler's
;;; `Exp::Module` arm and `module_closure`, step for step.

;; Whether `x` is a lambda as the checkers say (`k-lambda?`): under type
;; abstractions and ascriptions.
(define c-checked-lambda? (subr (read @globals) (exp) bool)
  (lambda (x)
    (tagcase x
      (e-lambda (ps body a b) #t)
      (e-rlambda (r l a b) #t)
      (e-plambda (d body a b) (c-checked-lambda? body))
      (e-the (d body a b) (c-checked-lambda? body))
      (else y #f))))
(define c-mv-onto (subr (alloc @k) (symbol exp int bool c-mvals) c-mvals)
  (lambda (n x k l rest) (cons (product (1 n) (2 x) (3 k) (4 l)) rest)))
(define c-mvals-group (subr (maxeff (read @globals) (alloc @k)) (names exps c-mvals) c-mvals)
  (lambda (ns xs rest)
    (if (null? ns) rest (c-mv-onto (car ns) (car xs) 3 #t (c-mvals-group (cdr ns) (cdr xs) rest)))))
;; The values `items` make, in order.
(define c-module-values (subr (maxeff (read @globals) (alloc @k)) (mod-items) c-mvals)
  (lambda (items)
    (if (null? items)
        nil
        (let* ((it (car items)) (k (extract it 1)) (ns (extract it 2)) (xs (extract it 4))
               (rest (c-module-values (cdr items))))
          (case k ((0)
                   (c-mv-onto (c-converter "up-" (car ns)) (car xs) 0 #f
                             (c-mv-onto (c-converter "down-" (car ns)) (car (cdr xs)) 0 #f rest)))
                  ((2)
                   (let ((l (and (not (null? (extract it 3))) (c-checked-lambda? (car xs)))))
                     (c-mv-onto (car ns) (car xs) 2 l rest)))
                  ((3) (c-mvals-group ns xs rest))
                  (else rest))))))
(define c-module-slots (subr c-walks (c-mvals int) c-mslots)
  (lambda (vs d)
    (if (null? vs)
        nil
        (cons (cons (extract (car vs) 1) d) (c-module-slots (cdr vs) (+ d 1))))))
(define c-find-slot (subr c-walks (c-mslots symbol) c-mslots)
  (lambda (ss n)
    (cond ((null? ss) nil)
          ((symbol=? (car (car ss)) n) ss)
          (else (c-find-slot (cdr ss) n)))))
;; Whether `x` names any of `later`'s.
(define c-names-any? (subr c-walks (exp c-mslots) bool)
  (lambda (x later)
    (letrec ((any (subr c-walks (syms) bool)
                  (lambda (ns)
                    (and (not (null? ns))
                         (or (not (null? (c-find-slot later (car ns)))) (any (cdr ns)))))))
      (any (c-free x nil nil)))))
;; Item `n`'s lambda's scope while it is made: each of `later` pending, and
;; itself a loop if it only calls itself in loops.
(define c-module-own (subr c-walks (symbol cenv c-mslots exp int) cenv)
  (lambda (n e later body nps)
    (if (null? later)
        e
        (let* ((m (car (car later)))
               (loops (and (symbol=? m n) (c-loops-only body n nps #t))))
          (c-module-own n (c-extend m (if loops (at-loop 0) (at-pending (cdr (car later)))) e)
                        (cdr later) body nps)))))
;; `ws` and, after them, the patches `ps` of the closure in slot `d`.
(define c-waits-onto (subr c-walks (c-waits int patches) c-waits)
  (lambda (ws d ps)
    (if (null? ps)
        ws
        (c-waits-onto (append ws (the c-waits (list (product (1 d) (2 (car (car ps)))
                                                             (3 (cdr (car ps)))))))
                      d (cdr ps)))))
;; Each closure of `ws` waiting for slot `d`, given it.
(define c-give-waiting (subr (maxeff compiles spin) (c-waits int code) unit)
  (lambda (ws d c)
    (if (null? ws)
        #u
        (let ((w (car ws)))
          (begin
            (if (= (extract w 3) d)
                (begin (c-op1 c routine-slot (wcell-int d))
                       (c-op1 c routine-slot (wcell-int (extract w 1)))
                       (c-field-set c (+ cellular-closure-free0 (extract w 2))))
                #u)
            (c-give-waiting (cdr ws) d c))))))

;; The words of the lambdas the body being compiled makes, as its stack
;; code made them; and those of the body whose register code is being made,
;; which uses them rather than making each again (and each of theirs, twice
;; as many at every depth).
(define c-made-now (ref (listof c-made @k) @k) (new nil))

(define c-made-reuse (ref (listof c-made @k) @k) (new nil))

;; Every word the stack code of the form being compiled made (not register
;; code's): where register code compiles a body other than the lambda's
;; own, a join point's, it finds the words made in it here.
(define c-form-made (ref (listof c-made @k) @k) (new nil))

;; A lambda's own name, unless a parameter of the same name hides it.
(define c-own-of (subr c-builds (c-params syms) syms)
  (lambda (ps own0) (if (or (null? own0) (c-has-param? ps (car own0))) (the syms nil) own0)))

;; Whether `m` is the word made for a lambda of `params` and `body`, its
;; own name `own`, capturing `fv`.
(define c-made-for? (subr c-walks (c-made exp syms syms syms) bool)
  (lambda (m body params own fv)
    (and (= (extract m 1) (exp-start body)) (= (extract m 2) (exp-end body))
         (k-syms=? (extract m 3) params) (k-syms=? (extract m 4) own) (k-syms=? (extract m 6) fv))))

;; The word the stack code of the body being compiled made for this lambda,
;; if it made one here, and the names it captures: the first made, of two
;; alike (a module's `up-` and `down-` conversions, of one span), as the
;; Rust compiler finds it.
(define c-made-word (subr c-walks (c-params exp cenv syms) (listof c-closing @k))
  (lambda (ps body e own0)
    (let ((fv (c-lambda-captured ps body e))
          (params (c-bind-params ps nil)) (own (c-own-of ps own0)))
      (letrec ((find (subr c-walks ((listof c-made @k)) (listof c-closing @k))
                 (lambda (ms)
                   (if (null? ms)
                       nil
                       (let ((older (find (cdr ms))))
                         (cond ((not (null? older)) older)
                               ((c-made-for? (car ms) body params own fv)
                                (cons (product (1 (extract (car ms) 5)) (2 fv)) nil))
                               (else nil)))))))
        ;; This body's own, first; then any the form's stack code made (a
        ;; join point's body, compiled in its `letrec`'s procedure's
        ;; register code).
        (let ((here (find (get c-made-reuse))))
          (if (null? here) (find (get c-form-made)) here))))))

;; What `r` holds, taken: `r` is left holding `empty`.
(define c-take
  (poly ((t type)) (subr (maxeff (read @k) (write @k)) ((ref t @k) t) t))
  (plambda ((t type))
    (lambda ((r (ref t @k)) (empty t)) (let ((x (get r))) (begin (set r empty) x)))))

;; The scope a lambda's body starts from, before its parameters and free
;; values: the lifted procedures `e` binds (known everywhere inside, being
;; constants), and its own name `own`, unless it captures it: a loop, or a
;; top-level definition's global.
(define c-own-scope (subr c-walks (syms syms cenv) cenv)
  (lambda (own fv e)
    (if (or (null? own) (c-member? fv (car own)))
        (c-lifted-entries e)
        (let ((l (c-where e (car own))))
          (c-extend (car own)
                    (if (and (not (null? l)) (c-global? (car l))) (car l) (at-loop 0))
                    (c-lifted-entries e))))))

;; What register code knows of the procedure `own` names, if it names one:
;; its name, where `inner` binds it, its arity `n`, and how many of its
;; parameters a lifting added.
(define c-this-of (subr c-walks (syms cenv int int) (listof c-this @k))
  (lambda (own inner n added)
    (if (null? own)
        nil
        (let ((l (car (c-find inner (car own)))))
          (cons (the c-this (product (1 (car own)) (2 l) (3 n) (4 added))) nil)))))

;; The procedure being compiled, as `c-this-name` and the others say.
(define c-this-saved (subr (maxeff (read @globals) (read @k)) () c-this)
  (lambda ()
    (product (1 (get c-this-name)) (2 (get c-this-loc))
             (3 (get c-this-params)) (4 (get c-this-added)))))

;; The procedure `me` made the one being compiled, its word starting at
;; label `start`.
(define c-this-enter! (subr (maxeff (read @globals) (write @k)) (c-this int) unit)
  (lambda (me start)
    (begin (set c-this-name (extract me 1)) (set c-this-loc (extract me 2))
           (set c-this-params (extract me 3)) (set c-this-start start)
           (set c-this-added (extract me 4)))))

;; A lambda's word's name, but for where its body starts: `named`'s, if it
;; has one (a global's); else for the definition it is in, and the name
;; it is bound to there (`own`, `letrec`'s, or `bound`, `let`'s), or
;; `lambda`: `k-check/walk`.
(define c-word-base (subr c-emits ((listof string @k) syms (listof symbol @k)) string)
  (lambda (named own bound)
    (if (null? named)
        (let ((inner (cond ((not (null? own)) (symbol->string (car own)))
                           ((not (null? bound)) (symbol->string (car bound)))
                           (else "lambda")))
              (scope (get c-scope-name)))
          (if (null? scope) inner (string-append (string-append (car scope) "/") inner)))
        (car named))))
;; A lambda's word's name: `named`'s, if it has one; else `base` and where
;; its body starts, so that a profile can say which.
(define c-word-symbol (subr c-walks (string (listof string @k) exp) symbol)
  (lambda (base named body)
    (string->symbol
      (if (null? named)
          (string-append base (string-append "@" (c-place-name (exp-start body))))
          (car named)))))

;; While a copy's register code is made: which (one, or none).
(define c-spec-now (ref (listof c-spec @k) @k) (new nil))
;; While register code is made: the plan's contexts it is in (3b), innermost
;; first (-1 where the plan has none).
(define c-r-plan-ctx (ref (listof int @k) @k) (new nil))

;; The form's, last first.
(define c-twins (ref (listof c-twin @k) @k) (new nil))
;; Twin `t` as a copy's, in context `ctx`, specialized as `spec` says, in
;; globals `genv`.
(define c-copy-twin (subr c-builds (c-twin c-spec int int) c-twin)
  (lambda (t spec ctx genv)
    (product (1 (extract t 1)) (2 (extract t 2)) (3 (extract t 3)) (4 (extract t 4))
             (5 (extract t 5)) (6 (extract t 6)) (7 (extract t 7))
             (8 (the (listof c-copy-twin @k) (cons (product (1 spec) (2 ctx) (3 genv)) nil))))))
;; Register code for the lambda of `ps` and `body` as word `w`'s twin, when
;; this compiler makes it (`c-registers`): made after its form's words.
(define c-register-twin!
  (subr (maxeff compiles spin) (tword c-params exp cenv (listof c-this @k) (listof symbol @k)) unit)
  (lambda (w ps body inner this defining)
    (if (get c-registers)
        (set c-twins
             (cons (product (1 w) (2 ps) (3 body) (4 inner) (5 this) (6 defining)
                            (7 (get c-made-now)) (8 (the (listof c-copy-twin @k) nil)))
                   (get c-twins)))
        #u)))

;; A typed call of `n` arguments: in tail position, a tail call.
(define c-typed-call (subr c-emits (code int bool) unit)
  (lambda (c n tail)
    (if tail (c-op1 c routine-ttailcall (wcell-int n)) (c-op1 c routine-tcall (wcell-int n)))))

;; The name `(with m body)` is the standard binding of, if `m` is `#%fx`
;; (where nothing shadows it, the checker made it the plain name), else "".
(define c-fx-name (subr (read @globals) (symbol exp) string)
  (lambda (m body)
    (tagcase body
      (e-var (n a b) (if (string=? (symbol->string m) "#%fx") (symbol->string n) ""))
      (else y ""))))
;; The standard operation `f` names, if it is a name bound nowhere else;
;; else "".
(define c-standard-name (subr c-walks (exp cenv) string)
  (lambda (f e)
    (tagcase f
      (e-var (n a b) (if (null? (c-where e n)) (symbol->string n) ""))
      ;; `(with #%fx n)` where `n` is shadowed: the standard `n`.
      (e-with (m body a b) (c-fx-name m body))
      (else y ""))))

;; Whether `f` names the standard `name`, as the quote rewrite writes it:
;; plainly, or through `#%fx`.
(define c-quote-names? (subr (read @globals) (exp string) bool)
  (lambda (f name)
    (tagcase f
      (e-var (n a b) (string=? (symbol->string n) name))
      (e-with (m body a b) (string=? (c-fx-name m body) name))
      (else y #f))))
;; The datum a quote builds (`%quote`'s argument, which only the quote
;; rewrite makes: `quoted` in `parser.fx`), as a constant's cell, made
;; once, where it is made of literals and symbols: `cons` and `nil` here
;; are the standard ones, by how the rewrite wrote them. A string, a float
;; or a vector in it, not yet: built as written. As the Rust compiler's
;; `quoted_value`. None, or one.
(define c-quoted-cell
  (subr (maxeff (read @globals) (read @k) (alloc @k) spin) (exp) (listof wcell @k))
  (lambda (x)
    (tagcase x
      (e-int (n a b) (cons (wcell-int n) nil))
      (e-bool (v a b) (cons (wcell-bool v) nil))
      (e-char (v a b) (cons (wcell-char v) nil))
      (e-sym (s a b) (cons (wcell-symbol s) nil))
      (e-the (d body a b) (c-quoted-cell body))
      (e-var (n a b) (if (string=? (symbol->string n) "nil") (cons (wcell-nil) nil) nil))
      (e-with (m body a b) (if (string=? (c-fx-name m body) "nil") (cons (wcell-nil) nil) nil))
      (e-app (f args a b)
        (if (and (c-quote-names? f "cons") (= (c-count-exps args) 2))
            (let ((h (c-quoted-cell (car args))) (t (c-quoted-cell (car (cdr args)))))
              (if (or (null? h) (null? t)) nil (cons (wcell-pair (car h) (car t)) nil)))
            nil))
      (else y nil))))

;; `(%quote arg)`'s datum, made now and interned (`wcell-interned`), where
;; it is all literals: the one object equal to it, at every copy of the
;; quote and every quote of it. As the Rust compiler's `quote_now`.
(define c-quote-now
  (subr (maxeff (read @globals) (read @k) (alloc @k) spin) (exp) (listof wcell @k))
  (lambda (arg)
    (let ((made (c-quoted-cell arg)))
      (if (null? made) nil (cons (wcell-interned (car made)) nil)))))

;; Field `p` of the module pushed: from 2^40 on, a path (`k-reshape-path`),
;; value `j` of the module that is its value `k`.
(define c-reshape-field (subr (maxeff compiles spin) (code int) unit)
  (lambda (c p)
    (if (< p 1099511627776)
        (c-field c (+ p 2))
        (let ((q (- p 1099511627776)))
          (begin (c-field c (+ (quotient q 1048576) 2)) (c-field c (+ (remainder q 1048576) 2)))))))
;; The module in slot `depth`'s fields at positions `at`, pushed.
(define c-reshape-fields (subr (maxeff compiles spin) (k-ids int code) unit)
  (lambda (at depth c)
    (if (null? at)
        #u
        (begin (c-op1 c routine-slot (wcell-int depth)) (c-reshape-field c (car at))
               (c-reshape-fields (cdr at) depth c)))))
;; Each slot of `ss`, newest first, pushed, the oldest first: how many.
(define c-slots-load (subr (maxeff c-emits spin) ((listof int @k) code) int)
  (lambda (ss c)
    (if (null? ss)
        0
        (let ((n (c-slots-load (cdr ss) c)))
          (begin (c-op1 c routine-slot (wcell-int (car ss))) (+ n 1))))))
;; A `with`'s module, at `l`, its values `ns` from field `i` on, each into
;; the next slot from `depth`: `e` with them bound.
(define c-with-fields (subr (maxeff compiles spin) (syms k-ids loc cenv int int code) cenv)
  (lambda (ns ps l e depth k c)
    (if (or (null? ns) (null? ps))
        e
        (begin (c-load c l) (c-field c (+ (car ps) 2))
               (let ((inner (c-extend (car ns) (at-slot (+ depth k)) e)))
                 (c-with-fields (cdr ns) (cdr ps) l inner depth (+ k 1) c)))))))))
