;;; The compiler written in FX-26: expressions. After `compile-lift.fx`
;;; (PLAN.md §11, 9d).

;;; ---------------------------------------------------------- expressions
;;; `depth` is how many values are on the frame above its start, so the next
;;; value pushed is slot `depth`. In tail position, code ends the word: with
;;; a `tailcall`, or with `return` after the value.

;; Its types (`compile-exps-types.fx`), loaded before the module so that they are
;; not among its values; the module names what it uses of them.
(define compile-exps-types (load-module "fx26:compile-exps-types.fx"))
;; A module (`TODO.md` §34: the front end into modules, a file at a time);
;; what other files use re-exported after it.
(define compile-exps-module (module
(define-type c-inline (select compile-exps-types c-inline))
(define-type c-inlinables (select compile-exps-types c-inlinables))
(define-type c-mval (select compile-exps-types c-mval))
(define-type c-mvals (select compile-exps-types c-mvals))
(define-type c-mslots (select compile-exps-types c-mslots))
(define-type c-waits (select compile-exps-types c-waits))
(define-type c-made (select compile-exps-types c-made))
(define-type c-closing (select compile-exps-types c-closing))
(define-type c-region (select compile-exps-types c-region))
(define-type c-spec (select compile-exps-types c-spec))
(define-type c-copy-twin (select compile-exps-types c-copy-twin))
(define-type c-twin (select compile-exps-types c-twin))

(define-rec
  (c-exps (subr (maxeff compiles spin) (exps cenv int code) int)
    (lambda (es e depth c)
      (if (null? es)
          0
          (begin (c-exp (car es) e depth c #f) (+ 1 (c-exps (cdr es) e (+ depth 1) c))))))
  ;; `x`'s code. A procedure converted to a convention is made, then given
  ;; to `%fx26-convert` with what it is converted to.
  (c-exp (subr (maxeff compiles spin) (exp cenv int code bool) unit)
    (lambda (x e depth c tail)
      (let ((k (c-conversion-at x)) (r (c-reshape-at x)))
        (cond ((>= k 0)
               (begin (c-exp-as-is x e depth c #f) (c-int c k)
                      (c-prim c "%fx26-convert" 2) (c-done c tail)))
              ((not (null? r)) (c-reshape x (car r) e depth c tail))
              (else (c-exp-as-is x e depth c tail))))))
  ;; A module reshaped (`k-reshape-at`): made, then a product of the values
  ;; the type wanted has, by position `at`.
  (c-reshape (subr (maxeff compiles spin) (exp k-ids cenv int code bool) unit)
    (lambda (x at e depth c tail)
      (begin (c-exp-as-is x e depth c #f)
             (c-int c 37)
             (c-reshape-fields at depth c)
             (c-prim c "%make-frozen" (+ 1 (k-length at)))
             (c-unbind c depth 1 #f)
             (c-done c tail))))
  (c-exp-as-is (subr (maxeff compiles spin) (exp cenv int code bool) unit)
    (lambda (x e depth c tail)
      (tagcase x
        (e-var (n a b)
          (let ((l (c-where e n)))
            (begin
              (if (null? l)
                  (if (std-nil-name? (symbol->string n))
                      (c-lit c (wcell-nil))
                      (c-standard-value (symbol->string n) c))
                  (c-load c (car l)))
              (c-done c tail))))
        (e-int (n a b) (begin (c-int c n) (c-done c tail)))
        (e-bool (v a b) (begin (c-lit c (wcell-bool v)) (c-done c tail)))
        (e-str (s a b) (begin (c-lit c (wcell-string s)) (c-done c tail)))
        (e-float (x a b) (begin (c-lit c (wcell-f64 x)) (c-done c tail)))
        (e-char (ch a b) (begin (c-lit c (wcell-char ch)) (c-done c tail)))
        (e-sym (s a b) (begin (c-lit c (wcell-symbol s)) (c-done c tail)))
        (e-unit (a b) (begin (c-lit c (wcell-unit)) (c-done c tail)))
        (e-lambda (ps body a b) (begin (c-lambda ps body e depth c nil nil) (c-done c tail)))
        (e-rlambda (r l a b)
          (tagcase l
            (e-lambda (ps body la lb)
              (begin (c-lambda ps body e depth c nil (the c-region (cons r nil))) (c-done c tail)))
            (else y (c-fail "an rlambda's lambda"))))
        ;; A lambda applied at once: a `let` (`c-applied-let`).
        (e-app (f args a b)
          (let ((l (c-applied-let f args)))
            (cond ((not (null? l)) (c-let (extract (car l) 1) (extract (car l) 2) e depth c tail))
                  ;; `apply` copies its list, unless the checker found it at
                  ;; `acyclic`: the variadic procedure's list must be one
                  ;; nothing else can write.
                  ((and (string=? (c-standard-name f e) "apply") (not (c-apply-shares-at a b)))
                   (begin (c-exps args e depth c) (c-prim c "%fx26-list-copy" 1)
                          (c-standard-on "apply" 2 c) (c-done c tail)))
                  (else (c-app f args e depth c tail)))))
        (e-plambda (d body a b) (c-exp body e depth c tail))
        ;; The region's name bound in a slot, as a `let`'s, to a region
        ;; entered (an arena, or a reap), and left with the body's value,
        ;; which is so not in tail position.
        (e-letregion (k r i body a b)
          (if (or (= k 0) (= k 3))
              ;; A region for analysis only: nothing at run time.
              (c-exp body e depth c tail)
              (let ((inner (c-extend r (at-slot depth) e)))
                (begin
                  (c-prim c (if (= k 1) "%region-enter" "%reap-enter") 0)
                  (c-exp body inner (+ depth 1) c #f)
                  (c-prim c "%region-exit" 2)
                  (c-done c tail)))))
        (e-proj (body ds a b) (c-exp body e depth c tail))
        (e-the (d body a b) (c-exp body e depth c tail))
        (e-convention (cnv body a b) (c-exp body e depth c tail))
        (e-if (t th el a b)
          (let ((no (c-fresh)) (end (c-fresh)))
            (begin
              (c-exp t e depth c #f)
              (c-emit c (i-zbranch no))
              (c-exp th e depth c tail)
              (if tail #u (c-emit c (i-branch end)))
              (c-emit c (i-label no))
              (c-exp el e depth c tail)
              (c-emit c (i-label end)))))
        (e-let (bs body a b) (c-let bs body e depth c tail))
        (e-letrec (bs body a b) (c-letrec-or-lift bs body a b e depth c tail))
        (e-begin (es a b) (c-begin es e depth c tail))
        (e-prompt (t body h a b)
          (begin
            (c-exp t e depth c #f)
            (c-exp h e (+ depth 1) c #f)
            (c-lambda (the c-params nil) body e (+ depth 2) c nil nil)
            (c-op c routine-prompt)
            (c-done c tail)))
        (e-bloblet (op i args a b)
          (begin (c-bloblet (symbol->string op) i args e depth c) (c-done c tail)))
        (e-product (fs a b)
          (begin (c-int c 37)
                 (c-prim c "%make-frozen" (+ 1 (c-exps (c-bound-exps fs) e (+ depth 1) c)))
                 (c-done c tail)))
        (e-extract (p l a b)
          (let ((i (c-field-at a b)))
            (if (< i 0)
                (c-fail "an extract the checker did not see")
                (begin (c-exp p e depth c #f) (c-field c (+ i 2)) (c-done c tail)))))
        (e-sum (t v a b)
          (begin (c-int c 36) (c-lit c (wcell-symbol t)) (c-exp v e (+ depth 2) c #f)
                 (c-prim c "%make-frozen" 3) (c-done c tail)))
        (e-tagcase (s arms els a b) (c-tagcase s arms els e depth c tail))
        (e-module (items a b)
          (let ((outer (get c-collecting)))
            (begin (set c-collecting (get c-module-members))
                   (set c-module-members nil)
                   (c-module items e depth c tail)
                   (set c-module-members (get c-collecting))
                   (set c-collecting outer))))
        (e-with (m body a b) (c-with m body a b e depth c tail)))))
  ;; A module (`docs/research/first-class-modules.md`): its items made in
  ;; slots in order from `depth`, as a `letrec*`'s (`c-module-make`); then
  ;; the product of its values.
  (c-module (subr (maxeff compiles spin) (mod-items cenv int code bool) unit)
    (lambda (items e depth c tail)
      (let* ((vs (c-module-values items))
             (made (c-module-make vs e depth (c-module-slots vs depth) nil nil c))
             (n (begin (c-int c 37) (c-slots-load (extract made 2) c))))
        (begin (c-prim c "%make-frozen" (+ 1 n))
               (c-done c tail)
               (c-unbind c depth (- (extract made 1) depth) tail)))))
  ;; Values `vs` made in slots from `d`, `later` theirs, `ws` the closures
  ;; waiting, `vals` the values' slots (newest first): the next slot, and
  ;; the values' slots.
  (c-module-make
    (subr (maxeff compiles spin) (c-mvals cenv int c-mslots c-waits (listof int @k) code)
          (productof (1 int) (2 (listof int @k))))
    (lambda (vs e d later ws vals c)
      (if (null? vs)
          (product (1 d) (2 vals))
          (let* ((v (car vs)) (n (extract v 1)) (x (extract v 2)) (k (extract v 3))
                 (ps (if (and (extract v 4) (c-names-any? x later))
                         (c-module-closure n x e later d c)
                         (begin (c-exp x e d c #f)
                                (if (= k 2) (c-note-member! n x e) #u)
                                (the patches nil))))
                 (waits (c-waits-onto ws d ps))
                 (given (c-give-waiting waits d c)))
            (c-module-make (cdr vs) (c-extend n (at-slot d) e) (+ d 1) (cdr later) waits
                           (if (= k 0) vals (cons d vals)) c)))))
  ;; Item `n`'s lambda `x`, made in slot `d` in `e`, naming items of `later`
  ;; not made yet, itself among them: those captured as a `letrec`'s
  ;; siblings are, to be given once made. What it gives: as `c-lambda`'s.
  (c-module-closure (subr (maxeff compiles spin) (symbol exp cenv c-mslots int code) patches)
    (lambda (n x e later d c)
      (let ((own (the syms (cons n nil))))
        (tagcase (car (c-lambda-of x))
          (e-lambda (ps body a b)
            (c-lambda ps body (c-module-own n e later body (c-count-params ps)) d c own nil))
          (e-rlambda (r l a b)
            (tagcase l
              (e-lambda (ps body la lb)
                (c-lambda ps body (c-module-own n e later body (c-count-params ps)) d c own
                          (the c-region (cons r nil))))
              (else y (c-fail "an rlambda's lambda"))))
          (else y (c-fail "a module's typed lambda is a lambda"))))))
  ;; `with`: the module's values, by position, in slots from `depth`; then
  ;; the body.
  (c-with (subr (maxeff compiles spin) (symbol exp int int cenv int code bool) unit)
    (lambda (m body a b e depth c tail)
      (let ((ns (c-with-at a b)) (ps (c-with-places-at a b)) (l (c-where e m)))
        (cond ((not (string=? (c-fx-name m body) ""))
               (let ((n (c-fx-name m body)))
                 (begin (if (std-nil-name? n) (c-lit c (wcell-nil)) (c-standard-value n c))
                        (c-done c tail))))
              ((or (null? ns) (null? ps)) (c-fail "a `with` the checker did not see"))
              ((null? l) (c-fail "a `with` of an unbound module"))
              (else
               (let ((inner (c-with-fields (car ns) (car ps) (car l) e depth 0 c)))
                 (begin (c-exp body inner (+ depth (c-length (car ns))) c tail)
                        (c-unbind c depth (c-length (car ns)) tail))))))))
  (c-begin (subr (maxeff compiles spin) (exps cenv int code bool) unit)
    (lambda (es e depth c tail)
      (cond ((null? es) (begin (c-lit c (wcell-unit)) (c-done c tail)))
            ((null? (cdr es)) (c-exp (car es) e depth c tail))
            (else (begin (c-exp (car es) e depth c #f) (c-op c routine-drop)
                         (c-begin (cdr es) e depth c tail))))))
  ;; Each value pushed, in the scope outside; the names are the slots.
  (c-let-bind (subr (maxeff compiles spin) (c-binds cenv cenv int code) cenv)
    (lambda (bs outer inner depth c)
      (if (null? bs)
          inner
          (begin (set c-bind-name (the (listof symbol @k) (cons (extract (car bs) 1) nil)))
                 (c-exp (extract (car bs) 2) outer depth c #f)
                 (set c-bind-name nil)
                 (c-let-bind (cdr bs) outer (c-extend (extract (car bs) 1) (at-slot depth) inner)
                             (+ depth 1) c)))))
  (c-letrec (subr (maxeff compiles spin) (c-recs exp cenv int code bool) unit)
    (lambda (bs body e depth c tail)
      (let* ((made (c-letrec-make bs bs e depth 0 c)) (n (c-count-letrec bs)))
        (begin
          (c-letrec-patch made depth 0 c)
          (c-exp body (c-letrec-slots bs e depth) (+ depth n) c tail)
          (c-unbind c depth n tail)))))
  ;; A `let`: each value pushed, in the scope outside; the names are the slots.
  (c-let (subr (maxeff compiles spin) (c-binds exp cenv int code bool) unit)
    (lambda (bs body e depth c tail)
      (let* ((inner (c-let-bind bs e e depth c)) (n (c-count-let bs)))
        (begin (c-exp body inner (+ depth n) c tail) (c-unbind c depth n tail)))))
  ;; Whether the `letrec` at `a`–`b` is lambda-lifted, deciding the first
  ;; time it is asked (by its stack code: its register code asks again, and
  ;; has the same answer and words): its members' `c-lifts` indices if so, in
  ;; a list of one, each member's word made, with the names it takes first.
  (c-lift (subr (maxeff compiles spin) (c-recs exp int int cenv bool) c-lifting)
    (lambda (bs body a b e tail)
      (let ((key (c-span-key a b)))
        (if (table-has? (get c-lifted) key)
            (table-ref (get c-lifted) key (the c-lifting nil))
            (let* ((planned (c-planned-lift a b))
                   (plan (if (null? planned) (c-lift-plan bs body e tail) (car planned))))
              (if (null? plan)
                  (begin (table-set! (get c-lifted) key (the c-lifting nil)) (the c-lifting nil))
                  (let* ((added (car plan))
                         (ks (c-lift-closures bs added 0))
                         (done (the c-lifting (cons ks nil))))
                    (begin
                      (table-set! (get c-lifted) key done)
                      (c-lift-words bs added ks (c-bind-lifted bs ks (c-lifted-entries e)) 0)
                      done))))))))
  ;; Each member's word, from the `i`th, into its closure: its added names
  ;; first, then its parameters; its tail calls of itself loops.
  (c-lift-words (subr (maxeff compiles spin) (c-recs c-added (listof int @k) cenv int) unit)
    (lambda (bs added ks known i)
      (if (null? bs)
          #u
          (tagcase (car (c-lambda-of (extract (car bs) 3)))
            (e-lambda (ps lbody la lb)
              (let* ((name (extract (car bs) 1))
                     (loops (c-loops-only lbody name (c-count-params ps) #t))
                     (own (if loops (the syms (cons name nil)) (the syms nil)))
                     (takes (array-ref added i))
                     (made (begin (set c-lifting-added (c-length takes))
                                  (c-lambda-word (c-added-params takes ps) lbody known own))))
                (begin
                  (if (null? (extract made 2)) #u (c-fail "a lifted procedure captures names"))
                  (close-over-word! (extract (c-lift-of (car ks)) 1) (extract made 1))
                  (c-lift-words (cdr bs) added (cdr ks) known (+ i 1)))))
            (else y (c-fail "a lifted binding is a lambda"))))))
  ;; A `letrec`, lifted if it may be (`c-lift`), else closures made.
  (c-letrec-or-lift (subr (maxeff compiles spin) (c-recs exp int int cenv int code bool) unit)
    (lambda (bs body a b e depth c tail)
      (let ((ks (c-lift bs body a b e tail)))
        (if (null? ks)
            (c-letrec bs body e depth c tail)
            (c-exp body (c-bind-lifted bs (car ks) e) depth c tail)))))
  ;; Each closure made, in order; what each must have patched.
  (c-letrec-make
    (subr (maxeff compiles spin) (c-recs c-recs cenv int int code)
          (listof patches @k))
    (lambda (all bs e depth i c)
      (if (null? bs)
          nil
          (let* ((lam (c-lambda-of (extract (car bs) 3)))
                 (name (extract (car bs) 1))
                 (made (tagcase (car lam)
                         (e-lambda (ps body a b)
                           (c-letrec-lambda all ps body name e depth i c nil))
                         (e-rlambda (r l a b)
                           (tagcase l
                             (e-lambda (ps body la lb)
                               (c-letrec-lambda all ps body name e depth i c
                                                (the c-region (cons r nil))))
                             (else y (c-fail "an rlambda's lambda"))))
                         (else y (c-fail "a letrec binds only lambdas"))))
                 (rest (c-letrec-make all (cdr bs) e depth (+ i 1) c)))
            (cons made rest)))))
  ;; Binding `i` of `all`, the lambda of `ps` and `body` bound to `name`
  ;; (in `region`, if an `rlambda`'s), made as a `letrec` makes it.
  (c-letrec-lambda
    (subr (maxeff compiles spin) (c-recs c-params exp symbol cenv int int code c-region) patches)
    (lambda (all ps body name e depth i c region)
      (c-lambda ps body (c-letrec-own all e depth 0 i body (c-count-params ps)) (+ depth i) c
                (the syms (cons name nil)) region)))
  ;; A lambda: its free values pushed, then its word closed over them; or,
  ;; with a region (an `rlambda`'s, one or none), that region first, and the
  ;; closure made there by `%region-closure h fv … w`. `own` is the `letrec`
  ;; name it is bound to, or none: its tail calls in its body are loops. What
  ;; it gives: for each `letrec` sibling it captured before the sibling was
  ;; made, its free value's index and the slot the sibling will be in.
  (c-lambda (subr (maxeff compiles spin) (c-params exp cenv int code syms c-region) patches)
    (lambda (ps body e depth c own0 region)
      (let* ((made (begin (if (null? region) #u (c-exp (car region) e depth c #f))
                          (c-lambda-word ps body e own0)))
             (fv (extract made 2))
             (patches (c-push-all fv e depth 0 c))
             (w (wcell-word (extract made 1))))
        (begin
          (set c-prev-word (get c-last-word))
          (set c-last-word (the (listof tword @k) (cons (extract made 1) nil)))
          (if (null? region)
              (begin (c-op1 c routine-closure w) (c-emit c (i-cell (wcell-int (c-length fv)))))
              (begin (c-lit c w) (c-prim c "%region-closure" (+ 2 (c-length fv)))))
          patches))))
  ;; A lambda's word, and the names its closure captures, in order; with its
  ;; register code as its twin, when this compiler makes register code
  ;; (`c-registers`).
  (c-lambda-word (subr (maxeff compiles spin) (c-params exp cenv syms) c-closing)
    (lambda (ps body e own0)
      (let* ((outer (c-take c-made-now (the (listof c-made @k) nil)))
             (made (c-lambda-word-in ps body e own0)))
        (let ((m (product (1 (exp-start body)) (2 (exp-end body)) (3 (c-bind-params ps nil))
                          (4 (c-own-of ps own0)) (5 (extract made 1)) (6 (extract made 2)))))
          (begin
            (set c-made-now (cons m outer))
            (if (= (get c-twin-depth) 0) (set c-form-made (cons m (get c-form-made))) #u)
            made)))))
  ;; The same, with the words of the lambdas in it noted as made.
  (c-lambda-word-in (subr (maxeff compiles spin) (c-params exp cenv syms) c-closing)
    (lambda (ps body e own0)
      (let* ((named (c-take c-word-name (the (listof string @k) nil)))
             (bound (c-take c-bind-name (the (listof symbol @k) nil)))
             (defining (c-take c-defining (the (listof symbol @k) nil)))
             ;; What it captures, as the middle phase planned (`compile-plan.fx`);
             ;; found here only where it did not, in register code's lambdas.
             (planned (c-planned-fv ps body))
             (fv (if (null? planned) (c-lambda-captured ps body e) (car planned)))
             ;; The parameters a lifting added, first (`c-lift`).
             (added (c-take c-lifting-added 0))
             ;; A parameter of the same name hides the procedure.
             (own (c-own-of ps own0))
             (inner (c-inner-env fv e (c-param-env ps 0 (c-own-scope own fv e)) 0))
             (n (c-count-params ps))
             (body-code (the code (new nil)))
             (outer (c-this-saved)) (outer-start (get c-this-start))
             (this (c-this-of own inner n added))
             (base (c-word-base named own0 bound))
             (outer-scope (get c-scope-name)))
        (begin
          (set c-scope-name (the (listof string @k) (cons base nil)))
          (if (null? this)
              (set c-this-params -1)
              (let ((start (c-fresh)))
                (begin (c-this-enter! (car this) start) (c-emit body-code (i-label start)))))
          (c-exp body inner n body-code #t)
          (c-this-enter! outer outer-start)
          (let ((w (c-assemble body-code (c-word-symbol base named body))))
            (begin
              (c-register-twin! w ps body inner this defining)
              (set c-scope-name outer-scope)
              (product (1 w) (2 fv))))))))
  ;;; ------------------------------------------------------------ applications
  (c-app (subr (maxeff compiles spin) (exp exps cenv int code bool) unit)
    (lambda (f args e depth c tail)
      (if (c-self-call? f args e tail)
          ;; A loop: the arguments into the parameters' slots, the rest of
          ;; the frame dropped, and back to the start.
          (begin (c-exps args e depth c)
                 (c-loop-stores c (- (get c-this-params) 1) (get c-this-added))
                 (c-drops c (- depth (get c-this-params)))
                 (c-emit c (i-branch (get c-this-start))))
          (c-app-other f args e depth c tail))))
  (c-app-other (subr (maxeff compiles spin) (exp exps cenv int code bool) unit)
    (lambda (f args e depth c tail)
      (let ((k (c-lifted-at f e)) (standard (c-standard-name f e)))
        (cond ((>= k 0) (c-app-lifted k args e depth c tail))
              ((string=? standard "")
               (let ((n (c-exps args e depth c)))
                 (begin (c-exp f e (+ depth n) c #f)
                        ;; The checker typed the callee a subroutine: a typed call.
                        (c-typed-call c n tail))))
              ;; A quoted datum (TODO §51): made once, here, where it is all
              ;; literals; else built as written.
              ((and (string=? standard "%quote") (= (c-count-exps args) 1)
                    (not (null? (c-quote-now (car args)))))
               (begin (c-lit c (car (c-quote-now (car args)))) (c-done c tail)))
              ;; In tail position, the mark replaces this frame's: a loop
              ;; that marks each iteration runs in constant space.
              ((and tail (string=? standard "with-mark"))
               (begin (c-exps args e depth c) (c-op c routine-withmark-tail)))
              (else (begin (c-standard standard args e depth c) (c-done c tail)))))))
  ;; A lifted procedure's call: the names it would have captured, then the
  ;; arguments, then its closure.
  (c-app-lifted (subr (maxeff compiles spin) (int exps cenv int code bool) unit)
    (lambda (k args e depth c tail)
      (let* ((lift (c-lift-of k))
             (added (extract lift 2))
             (m (begin (c-load-names added e c) (c-length added)))
             (n (c-exps args e (+ depth m) c)))
        (begin (c-lit c (extract lift 1)) (c-typed-call c (+ m n) tail)))))
  ;; A standard operation, open-coded: a routine, or a runtime primitive, with
  ;; FX-26's conventions made plain (mutators give unit; arrays skip the
  ;; trailer's field).
  (c-standard (subr (maxeff compiles spin) (string exps cenv int code) unit)
    (lambda (name args e depth c)
      (if (string=? name "make-array")
          ;; (%make-bloblet-filled 0 n fill): the 0 first, under the others.
          (begin (c-int c 0) (c-exps args e (+ depth 1) c) (c-prim c "%make-bloblet-filled" 3))
          (c-standard-on name (c-exps args e depth c) c))))
  (c-bloblet (subr (maxeff compiles spin) (string int exps cenv int code) unit)
    (lambda (op i args e depth c)
      (case op (("make-bloblet") (c-prim c "%make-bloblet" (c-exps args e depth c)))
               (("rmake-bloblet")
                (c-prim c "%region-make-bloblet" (c-exps args e depth c)))
               (("bloblet-ref")
                (begin (c-exps args e depth c) (c-field c (+ i 2))))
               (("bloblet-set!")
                (begin (c-exp (car args) e depth c #f) (c-int c (+ i 2))
                       (c-exp (car (cdr args)) e (+ depth 2) c #f)
                       (c-prim c "%bloblet-set!" 3) (c-unit-after c)))
               (("bloblet-freeze")
                (begin (c-exps args e depth c) (c-op c routine-dup)
                       (c-lit c (wcell-bool #t)) (c-lit c (wcell-bool #f))
                       (c-prim c "%bloblet-freeze!" 3) (c-op c routine-drop)))
               (("bloblet-byte") (c-prim c "%bloblet-byte" (c-exps args e depth c)))
               (("bloblet-set-byte!")
                (begin (c-prim c "%bloblet-set-byte!" (c-exps args e depth c)) (c-unit-after c)))
               (else (c-prim c "%bloblet-bytes" (c-exps args e depth c))))))
  ;;; ----------------------------------------------------------------- tagcase
  (c-tagcase
    (subr (maxeff compiles spin) (exp c-cases c-binds cenv int code bool) unit)
    (lambda (s arms els e depth c tail)
      (let ((end (c-fresh)))
        (begin
          (c-exp s e depth c #f)
          (c-arms arms els e depth c tail end)
          (c-emit c (i-label end))))))
  (c-arms
    (subr (maxeff compiles spin) (c-cases c-binds cenv int code bool int) unit)
    (lambda (arms els e depth c tail end)
      (if (null? arms)
          (if (null? els)
              ;; A checked program covers every tag; this is never reached.
              (begin (c-lit c (wcell-bool #f)) (c-int c 0)
                     (c-op c routine-field-ref) (c-done c tail))
              (let ((inner (c-extend (extract (car els) 1) (at-slot depth) e)))
                (begin (c-exp (extract (car els) 2) inner (+ depth 1) c tail)
                       (c-unbind c depth 1 tail))))
          (let* ((arm (car arms)) (next (c-fresh)))
            (begin
              ;; Is the tag this arm's?
              (c-op1 c routine-slot (wcell-int depth))
              (c-field c 2)
              (c-lit c (wcell-symbol (extract arm 1)))
              (c-op c routine-eq)
              (c-emit c (i-zbranch next))
              ;; The value, or its product's members, as slots after the sum.
              (c-op1 c routine-slot (wcell-int depth))
              (c-field c 3)
              (let ((bound (if (extract arm 2)
                               (c-members (extract arm 3) e depth (+ depth 2) 0 c)
                               (c-extend (car (extract arm 3)) (at-slot (+ depth 1)) e)))
                    (n (if (extract arm 2) (+ 1 (c-count-names (extract arm 3))) 1)))
                (begin
                  (c-exp (extract arm 4) bound (+ depth (+ 1 n)) c tail)
                  (c-unbind c depth (+ n 1) tail)
                  (if tail #u (c-emit c (i-branch end)))))
              (c-emit c (i-label next))
              (c-arms (cdr arms) els e depth c tail end)))))))))

(define-type c-mvals (select compile-exps-module c-mvals))
(define-type c-mslots (select compile-exps-module c-mslots))
(define-type c-waits (select compile-exps-module c-waits))
(define-type c-made (select compile-exps-module c-made))
(define-type c-region (select compile-exps-module c-region))
(define c-exp (with compile-exps-module c-exp))
(define c-lift (with compile-exps-module c-lift))
(define c-lambda (with compile-exps-module c-lambda))
(define c-lambda-word (with compile-exps-module c-lambda-word))
(define-type c-inline (select compile-exps-module c-inline))
(define-type c-inlinables (select compile-exps-module c-inlinables))
(define-type c-twin (select compile-exps-module c-twin))
(define-type c-spec (select compile-exps-module c-spec))
