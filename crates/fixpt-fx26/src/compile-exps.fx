;;; The compiler written in FX-26, its second part: expressions, programs,
;;; and inlining. `compile.fx` first (PLAN.md §11, 9d).

;;; ---------------------------------------------------------- expressions
;;; `depth` is how many values are on the frame above its start, so the next
;;; value pushed is slot `depth`. In tail position, code ends the word: with
;;; a `tailcall`, or with `return` after the value.

;; The top-level definition whose lambda is compiled next: its name, in a
;; list; and, for the register compiler, the lambda being so compiled: its
;; name and word.
(define c-defining (ref (listof symbol @k) @k) (new nil))
(define c-own-now (ref (listof (productof (1 symbol) (2 tword)) @k) @k) (new nil))
;; The name the next lambda's word gets, if not where its body starts.
(define c-word-name (ref (listof string @k) @k) (new nil))
;; The word of the lambda compiled last, in a list; and of the one before.
(define c-last-word (ref (listof tword @k) @k) (new nil))
(define c-prev-word (ref (listof tword @k) @k) (new nil))
;; A lambda's word, made by the stack code of the body it is in: where its
;; body starts and ends, its parameters, its own name, the word, and the
;; names it captures.
(define-type c-made (productof (1 int) (2 int) (3 syms) (4 syms) (5 tword) (6 syms)))
;; The words of the lambdas the body being compiled makes, as its stack
;; code made them; and those of the body whose register code is being made,
;; which uses them rather than making each again (and each of theirs, twice
;; as many at every depth).
(define c-made-now (ref (listof c-made @k) @k) (new nil))
(define c-made-reuse (ref (listof c-made @k) @k) (new nil))
;; A lambda's own name, unless a parameter of the same name hides it.
(define c-own-of (subr (maxeff (read @globals) (read @k) (alloc @k)) ((listof (productof (1 symbol) (2 syns-a)) acyclic) syms) syms)
  (lambda (ps own0) (if (or (null? own0) (c-member? (c-bind-params ps nil) (car own0))) (the syms nil) own0)))
;; The word the stack code of the body being compiled made for this lambda,
;; if it made one here, and the names it captures.
(define c-made-word (subr (maxeff (read @globals) (read @k) (alloc @k) spin) ((listof (productof (1 symbol) (2 syns-a)) acyclic) exp cenv syms) (listof (productof (1 tword) (2 syms)) @k))
  (lambda (ps body e own0)
    (let ((fv (c-lambda-captured ps body e))
          (params (c-bind-params ps nil)) (own (c-own-of ps own0)))
      (letrec ((find (subr (maxeff (read @globals) (read @k) (alloc @k) spin) ((listof c-made @k)) (listof (productof (1 tword) (2 syms)) @k))
                 (lambda (ms)
                   (cond ((null? ms) nil)
                         ((and (= (extract (car ms) 1) (exp-start body)) (= (extract (car ms) 2) (exp-end body))
                               (k-syms=? (extract (car ms) 3) params) (k-syms=? (extract (car ms) 4) own)
                               (k-syms=? (extract (car ms) 6) fv))
                          (cons (product (1 (extract (car ms) 5)) (2 fv)) nil))
                         (else (find (cdr ms)))))))
        (find (get c-made-reuse))))))

(define-rec
  (c-exps (subr (maxeff compiles spin) ((listof exp acyclic) cenv int code) int)
    (lambda (es e depth c)
      (if (null? es) 0 (begin (c-exp (car es) e depth c #f) (+ 1 (c-exps (cdr es) e (+ depth 1) c))))))
  ;; `x`'s code. A procedure converted to a convention is made, then given
  ;; to `%fx26-convert` with what it is converted to.
  (c-exp (subr (maxeff compiles spin) (exp cenv int code bool) unit)
      (lambda (x e depth c tail)
        (let ((k (c-conversion-at x)))
          (if (< k 0)
              (c-exp-as-is x e depth c tail)
              (begin (c-exp-as-is x e depth c #f) (c-int c k) (c-prim c "%fx26-convert" 2) (c-done c tail))))))
  (c-exp-as-is (subr (maxeff compiles spin) (exp cenv int code bool) unit)
    (lambda (x e depth c tail)
      (tagcase x
        (e-var (n a b)
          (let ((l (c-where e n)))
            (begin
              (if (null? l)
                  (if (string=? (symbol->string n) "nil")
                      (c-lit c (wcell-nil))
                      (c-standard-value (symbol->string n) c))
                  (c-load c (car l)))
              (c-done c tail))))
        (e-int (n a b) (begin (c-int c n) (c-done c tail)))
        (e-bool (v a b) (begin (c-lit c (wcell-bool v)) (c-done c tail)))
        (e-str (s a b) (begin (c-lit c (wcell-string s)) (c-done c tail)))
        (e-char (ch a b) (begin (c-lit c (wcell-char ch)) (c-done c tail)))
        (e-sym (s a b) (begin (c-lit c (wcell-symbol s)) (c-done c tail)))
        (e-unit (a b) (begin (c-lit c (wcell-unit)) (c-done c tail)))
        (e-lambda (ps body a b) (begin (c-lambda ps body e depth c nil nil) (c-done c tail)))
        (e-rlambda (r l a b)
          (tagcase l
            (e-lambda (ps body la lb) (begin (c-lambda ps body e depth c nil (the (listof exp @k) (cons r nil))) (c-done c tail)))
            (else y (c-fail "an rlambda's lambda"))))
        ;; A lambda applied at once: a `let` (`c-applied-let`).
        (e-app (f args a b)
          (let ((l (c-applied-let f args)))
            (if (null? l) (c-app f args e depth c tail) (c-let (extract (car l) 1) (extract (car l) 2) e depth c tail))))
        (e-plambda (d body a b) (c-exp body e depth c tail))
        ;; The region's name bound in a slot, as a `let`'s, to a region
        ;; entered (an arena, or a reap), and left with the body's value,
        ;; which is so not in tail position.
        (e-letregion (k r i body a b)
          (if (or (= k 0) (= k 3))
              ;; A region for analysis only: nothing at run time.
              (c-exp body e depth c tail)
              (let ((inner (the cenv (cons (cons r (at-slot depth)) e))))
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
            (c-lambda (the (listof (productof (1 symbol) (2 syns-a)) acyclic) nil) body e (+ depth 2) c nil nil)
            (c-op c routine-prompt)
            (c-done c tail)))
        (e-bloblet (op i args a b) (begin (c-bloblet (symbol->string op) i args e depth c) (c-done c tail)))
        (e-product (fs a b)
          (begin (c-int c 37) (c-prim c "%make-frozen" (+ 1 (c-fields fs e (+ depth 1) c))) (c-done c tail)))
        (e-extract (p l a b)
          (let ((i (c-field-at a b)))
            (if (< i 0)
                (c-fail "an extract the checker did not see")
                (begin (c-exp p e depth c #f) (c-field c (+ i 2)) (c-done c tail)))))
        (e-sum (t v a b)
          (begin (c-int c 36) (c-lit c (wcell-symbol t)) (c-exp v e (+ depth 2) c #f)
                 (c-prim c "%make-frozen" 3) (c-done c tail)))
        (e-tagcase (s arms els a b) (c-tagcase s arms els e depth c tail)))))
  (c-begin (subr (maxeff compiles spin) ((listof exp acyclic) cenv int code bool) unit)
    (lambda (es e depth c tail)
      (cond ((null? es) (begin (c-lit c (wcell-unit)) (c-done c tail)))
            ((null? (cdr es)) (c-exp (car es) e depth c tail))
            (else (begin (c-exp (car es) e depth c #f) (c-op c routine-drop) (c-begin (cdr es) e depth c tail))))))
  (c-fields (subr (maxeff compiles spin) ((listof (productof (1 symbol) (2 exp)) acyclic) cenv int code) int)
    (lambda (fs e depth c)
      (if (null? fs) 0 (begin (c-exp (extract (car fs) 2) e depth c #f) (+ 1 (c-fields (cdr fs) e (+ depth 1) c))))))
  ;; Each value pushed, in the scope outside; the names are the slots.
  (c-let-bind (subr (maxeff compiles spin) ((listof (productof (1 symbol) (2 exp)) acyclic) cenv cenv int code) cenv)
    (lambda (bs outer inner depth c)
      (if (null? bs)
          inner
          (begin (c-exp (extract (car bs) 2) outer depth c #f)
                 (c-let-bind (cdr bs) outer (the cenv (cons (cons (extract (car bs) 1) (at-slot depth)) inner)) (+ depth 1) c)))))
  (c-letrec (subr (maxeff compiles spin) ((listof (productof (1 symbol) (2 syn) (3 exp)) acyclic) exp cenv int code bool) unit)
    (lambda (bs body e depth c tail)
      (let* ((made (c-letrec-make bs bs e depth 0 c)) (n (c-count-letrec bs)))
        (begin
          (c-letrec-patch made depth 0 c)
          (c-exp body (c-letrec-slots bs e depth) (+ depth n) c tail)
          (c-unbind c depth n tail)))))
  ;; A `let`: each value pushed, in the scope outside; the names are the slots.
  (c-let (subr (maxeff compiles spin) ((listof (productof (1 symbol) (2 exp)) acyclic) exp cenv int code bool) unit)
    (lambda (bs body e depth c tail)
      (let* ((inner (c-let-bind bs e e depth c)) (n (c-count-let bs)))
        (begin (c-exp body inner (+ depth n) c tail) (c-unbind c depth n tail)))))
  ;; Whether the `letrec` at `a`–`b` is lambda-lifted, deciding the first
  ;; time it is asked (by its stack code: its register code asks again, and
  ;; has the same answer and words): its members' `c-lifts` indices if so, in
  ;; a list of one, each member's word made, with the names it takes first.
  (c-lift (subr (maxeff compiles spin) ((listof (productof (1 symbol) (2 syn) (3 exp)) acyclic) exp int int cenv bool) (listof (listof int @k) @k))
    (lambda (bs body a b e tail)
      (let ((key (c-span-key a b)))
        (if (table-has? (get c-lifted) key)
            (table-ref (get c-lifted) key (the (listof (listof int @k) @k) nil))
            (let ((plan (c-lift-plan bs body e tail)))
              (if (null? plan)
                  (begin (table-set! (get c-lifted) key (the (listof (listof int @k) @k) nil)) (the (listof (listof int @k) @k) nil))
                  (let* ((added (car plan))
                         (ks (c-lift-closures bs added 0))
                         (done (the (listof (listof int @k) @k) (cons ks nil))))
                    (begin
                      (table-set! (get c-lifted) key done)
                      (c-lift-words bs added ks (c-bind-lifted bs ks (c-lifted-entries e)) 0)
                      done))))))))
  ;; Each member's word, from the `i`th, into its closure: its added names
  ;; first, then its parameters; its tail calls of itself loops.
  (c-lift-words (subr (maxeff compiles spin) ((listof (productof (1 symbol) (2 syn) (3 exp)) acyclic) (arrayof syms @k) (listof int @k) cenv int) unit)
    (lambda (bs added ks known i)
      (if (null? bs)
          #u
          (tagcase (car (c-lambda-of (extract (car bs) 3)))
            (e-lambda (ps lbody la lb)
              (let* ((name (extract (car bs) 1))
                     (own (if (c-loops-only lbody name (c-count-params ps) #t) (the syms (cons name nil)) (the syms nil)))
                     (made (begin (set c-lifting-added (c-length (array-ref added i)))
                                  (c-lambda-word (c-added-params (array-ref added i) ps) lbody known own))))
                (begin
                  (if (null? (extract made 2)) #u (c-fail "a lifted procedure captures names"))
                  (close-over-word! (extract (table-ref (get c-lifts) (car ks) (the c-lift (product (1 (wcell-nil)) (2 (the syms nil))))) 1) (extract made 1))
                  (c-lift-words (cdr bs) added (cdr ks) known (+ i 1)))))
            (else y (c-fail "a lifted binding is a lambda"))))))
  ;; A `letrec`, lifted if it may be (`c-lift`), else closures made.
  (c-letrec-or-lift (subr (maxeff compiles spin) ((listof (productof (1 symbol) (2 syn) (3 exp)) acyclic) exp int int cenv int code bool) unit)
    (lambda (bs body a b e depth c tail)
      (let ((ks (c-lift bs body a b e tail)))
        (if (null? ks)
            (c-letrec bs body e depth c tail)
            (c-exp body (c-bind-lifted bs (car ks) e) depth c tail)))))
  ;; Each closure made, in order; what each must have patched.
  (c-letrec-make
    (subr (maxeff compiles spin) ((listof (productof (1 symbol) (2 syn) (3 exp)) acyclic) (listof (productof (1 symbol) (2 syn) (3 exp)) acyclic) cenv int int code)
          (listof patches @k))
    (lambda (all bs e depth i c)
      (if (null? bs)
          nil
          (let* ((lam (c-lambda-of (extract (car bs) 3)))
                 (made (tagcase (car lam)
                         (e-lambda (ps body a b)
                           (c-lambda ps body (c-letrec-own all e depth 0 i body (c-count-params ps)) (+ depth i) c
                                     (the syms (cons (extract (car bs) 1) nil)) nil))
                         (e-rlambda (r l a b)
                           (tagcase l
                             (e-lambda (ps body la lb)
                               (c-lambda ps body (c-letrec-own all e depth 0 i body (c-count-params ps)) (+ depth i) c
                                         (the syms (cons (extract (car bs) 1) nil)) (the (listof exp @k) (cons r nil))))
                             (else y (c-fail "an rlambda's lambda"))))
                         (else y (c-fail "a letrec binds only lambdas"))))
                 (rest (c-letrec-make all (cdr bs) e depth (+ i 1) c)))
            (cons made rest)))))
  ;; A lambda: its free values pushed, then its word closed over them; or,
  ;; with a region (an `rlambda`'s, one or none), that region first, and the
  ;; closure made there by `%region-closure h fv … w`. `own` is the `letrec`
  ;; name it is bound to, or none: its tail calls in its body are loops. What
  ;; it gives: for each `letrec` sibling it captured before the sibling was
  ;; made, its free value's index and the slot the sibling will be in.
  (c-lambda (subr (maxeff compiles spin) ((listof (productof (1 symbol) (2 syns-a)) acyclic) exp cenv int code syms (listof exp @k)) patches)
    (lambda (ps body e depth c own0 region)
      (let* ((made (begin (if (null? region) #u (c-exp (car region) e depth c #f)) (c-lambda-word ps body e own0)))
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
  (c-lambda-word (subr (maxeff compiles spin) ((listof (productof (1 symbol) (2 syns-a)) acyclic) exp cenv syms) (productof (1 tword) (2 syms)))
    (lambda (ps body e own0)
      (let* ((outer (get c-made-now))
             (made (begin (set c-made-now (the (listof c-made @k) nil)) (c-lambda-word-in ps body e own0))))
        (begin
          (set c-made-now (cons (product (1 (exp-start body)) (2 (exp-end body)) (3 (c-bind-params ps nil))
                                         (4 (c-own-of ps own0)) (5 (extract made 1)) (6 (extract made 2)))
                                outer))
          made))))
;; The same, with the words of the lambdas in it noted as made.
(c-lambda-word-in (subr (maxeff compiles spin) ((listof (productof (1 symbol) (2 syns-a)) acyclic) exp cenv syms) (productof (1 tword) (2 syms)))
    (lambda (ps body e own0)
      (let* ((named (let ((x (get c-word-name))) (begin (set c-word-name (the (listof string @k) nil)) x)))
             (defining (let ((x (get c-defining))) (begin (set c-defining (the (listof symbol @k) nil)) x)))
             (fv (c-lambda-captured ps body e))
             ;; The parameters a lifting added, first (`c-lift`).
             (added (let ((x (get c-lifting-added))) (begin (set c-lifting-added 0) x)))
             ;; A parameter of the same name hides the procedure.
             (own (if (or (null? own0) (c-member? (c-bind-params ps nil) (car own0))) (the syms nil) own0))
             ;; Its own name: a loop, or a top-level definition's global.
             ;; (Lifted procedures are known everywhere inside: they are
             ;; constants.)
             (base (if (or (null? own) (c-member? fv (car own)))
                       (c-lifted-entries e)
                       (let ((l (c-where e (car own))))
                         (the cenv (cons (cons (car own)
                                               (if (and (not (null? l)) (tagcase (car l) (at-global (h) #t) (else y #f)))
                                                   (car l)
                                                   (at-loop 0)))
                                         (c-lifted-entries e))))))
             (inner (c-inner-env fv e (c-param-env ps 0 base) 0))
             (n (c-count-params ps))
             (body-code (the code (new nil)))
             (outer-name (get c-this-name)) (outer-loc (get c-this-loc))
             (outer-params (get c-this-params)) (outer-start (get c-this-start)) (outer-added (get c-this-added))
             (this (the (listof c-this @k)
                     (if (null? own) nil (cons (product (1 (car own)) (2 (car (c-find inner (car own)))) (3 n) (4 added)) nil)))))
        (begin
          (if (null? own)
              (set c-this-params -1)
              (let ((start (c-fresh)))
                (begin (set c-this-name (car own)) (set c-this-loc (car (c-find inner (car own))))
                       (set c-this-params n) (set c-this-start start) (set c-this-added added)
                       (c-emit body-code (i-label start)))))
          (c-exp body inner n body-code #t)
          (set c-this-name outer-name) (set c-this-loc outer-loc)
          (set c-this-params outer-params) (set c-this-start outer-start) (set c-this-added outer-added)
          ;; Named for where its body starts, so that a profile can say which.
          (let ((w (c-assemble body-code
                                (string->symbol
                                  (if (null? named) (string-append "lambda@" (int->string (exp-start body))) (car named))))))
            (begin
              (if (get c-registers)
                  (let ((cells (begin (set c-own-now
                                           (if (null? defining)
                                               (the (listof (productof (1 symbol) (2 tword)) @k) nil)
                                               (cons (product (1 (car defining)) (2 w)) nil)))
                                      (let* ((outer-reuse (get c-made-reuse))
                                             (cells (begin (set c-made-reuse (get c-made-now))
                                                           (set c-made-now (the (listof c-made @k) nil))
                                                           ((get c-register-code) ps body inner this))))
                                        (begin (set c-made-reuse outer-reuse) cells)))))
                    (if (null? cells) #u (begin (set-register-twin w cells) #u)))
                  #u)
              (product (1 w) (2 fv))))))))
  ;;; ------------------------------------------------------------ applications
  (c-app (subr (maxeff compiles spin) (exp (listof exp acyclic) cenv int code bool) unit)
    (lambda (f args e depth c tail)
      (if (c-self-call? f args e tail)
          ;; A loop: the arguments into the parameters' slots, the rest of
          ;; the frame dropped, and back to the start.
          (begin (c-exps args e depth c)
                 (c-loop-stores c (- (get c-this-params) 1) (get c-this-added))
                 (c-drops c (- depth (get c-this-params)))
                 (c-emit c (i-branch (get c-this-start))))
          (c-app-other f args e depth c tail))))
  (c-app-other (subr (maxeff compiles spin) (exp (listof exp acyclic) cenv int code bool) unit)
      (lambda (f args e depth c tail)
        (let ((k (c-lifted-at f e)))
          (if (>= k 0)
              ;; A lifted procedure's call: the names it would have captured,
              ;; then the arguments, then its closure.
              (let* ((lift (table-ref (get c-lifts) k (the c-lift (product (1 (wcell-nil)) (2 (the syms nil))))))
                     (added (extract lift 2))
                     (m (begin (c-load-names added e c) (c-length added)))
                     (n (c-exps args e (+ depth m) c)))
                (begin (c-lit c (extract lift 1))
                       (if tail
                           (c-op1 c routine-ttailcall (wcell-int (+ m n)))
                           (c-op1 c routine-tcall (wcell-int (+ m n))))))
        (let ((standard (tagcase f (e-var (n a b) (if (null? (c-where e n)) (symbol->string n) "") ) (else y ""))))
          (if (string=? standard "")
              (let ((n (c-exps args e depth c)))
                (begin (c-exp f e (+ depth n) c #f)
                       ;; The checker typed the callee a subroutine: a typed call.
                       (if tail
                           (c-op1 c routine-ttailcall (wcell-int n))
                           (c-op1 c routine-tcall (wcell-int n)))))
              (if (and tail (string=? standard "with-mark"))
                  ;; In tail position, the mark replaces this frame's: a loop
                  ;; that marks each iteration runs in constant space.
                  (begin (c-exps args e depth c) (c-op c routine-withmark-tail))
                  (begin (c-standard standard args e depth c) (c-done c tail)))))))))
  ;; A standard operation, open-coded: a routine, or a runtime primitive, with
  ;; FX-26's conventions made plain (mutators give unit; arrays skip the
  ;; trailer's field).
  (c-standard (subr (maxeff compiles spin) (string (listof exp acyclic) cenv int code) unit)
    (lambda (name args e depth c)
      (if (string=? name "make-array")
          ;; (%make-bloblet-filled 0 n fill): the 0 first, under the others.
          (begin (c-int c 0) (c-exps args e (+ depth 1) c) (c-prim c "%make-bloblet-filled" 3))
          (c-standard-on name (c-exps args e depth c) c))))
  (c-bloblet (subr (maxeff compiles spin) (string int (listof exp acyclic) cenv int code) unit)
    (lambda (op i args e depth c)
      (cond ((string=? op "make-bloblet") (c-prim c "%make-bloblet" (c-exps args e depth c)))
            ((string=? op "rmake-bloblet") (c-prim c "%region-make-bloblet" (c-exps args e depth c)))
            ((string=? op "bloblet-ref")
             (begin (c-exps args e depth c) (c-field c (+ i 2))))
            ((string=? op "bloblet-set!")
             (begin (c-exp (car args) e depth c #f) (c-int c (+ i 2)) (c-exp (car (cdr args)) e (+ depth 2) c #f)
                    (c-prim c "%bloblet-set!" 3) (c-unit-after c)))
            ((string=? op "bloblet-freeze")
             (begin (c-exps args e depth c) (c-op c routine-dup) (c-lit c (wcell-bool #t)) (c-lit c (wcell-bool #f))
                    (c-prim c "%bloblet-freeze!" 3) (c-op c routine-drop)))
            ((string=? op "bloblet-byte") (c-prim c "%bloblet-byte" (c-exps args e depth c)))
            ((string=? op "bloblet-set-byte!") (begin (c-prim c "%bloblet-set-byte!" (c-exps args e depth c)) (c-unit-after c)))
            (else (c-prim c "%bloblet-bytes" (c-exps args e depth c))))))
  ;;; ----------------------------------------------------------------- tagcase
  (c-tagcase
    (subr (maxeff compiles spin) (exp (listof (productof (1 symbol) (2 bool) (3 names) (4 exp)) acyclic) (listof (productof (1 symbol) (2 exp)) acyclic) cenv int code bool) unit)
    (lambda (s arms els e depth c tail)
      (let ((end (c-fresh)))
        (begin
          (c-exp s e depth c #f)
          (c-arms arms els e depth c tail end)
          (c-emit c (i-label end))))))
  (c-arms
    (subr (maxeff compiles spin) ((listof (productof (1 symbol) (2 bool) (3 names) (4 exp)) acyclic) (listof (productof (1 symbol) (2 exp)) acyclic) cenv int code bool int) unit)
    (lambda (arms els e depth c tail end)
      (if (null? arms)
          (if (null? els)
              ;; A checked program covers every tag; this is never reached.
              (begin (c-lit c (wcell-bool #f)) (c-int c 0) (c-op c routine-field-ref) (c-done c tail))
              (let ((inner (the cenv (cons (cons (extract (car els) 1) (at-slot depth)) e))))
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
                               (the cenv (cons (cons (car (extract arm 3)) (at-slot (+ depth 1))) e))))
                    (n (if (extract arm 2) (+ 1 (c-count-names (extract arm 3))) 1)))
                (begin
                  (c-exp (extract arm 4) bound (+ depth (+ 1 n)) c tail)
                  (c-unbind c depth (+ n 1) tail)
                  (if tail #u (c-emit c (i-branch end)))))
              (c-emit c (i-label next))
              (c-arms (cdr arms) els e depth c tail end)))))))

;;; ------------------------------------------------------------- programs

;;; ------------------------------------------------------------- inlining

;; The most parser-tree nodes a body may have to be inlined
;; (`c-inline-room`).
(define c-inline-limit int 20)

;; A small global procedure a call in register code may inline, guarded
;; (`regcode.fx`'s `r-inline`): its name, word, parameters and body, and
;; the globals as its body saw them.
(define-type c-inline
  (productof (1 symbol) (2 tword) (3 (listof (productof (1 symbol) (2 syns-a)) acyclic)) (4 exp) (5 int)))
(define c-inlines (ref (listof c-inline acyclic) @k) (new nil))
;; The globals whose bodies are being inlined, which are not again.
(define c-inlining (ref syms @k) (new nil))
;; `xs` without `n`'s.
(define c-drop-inline (subr (maxeff (read @globals) (read @k) (alloc @k)) ((listof c-inline acyclic) symbol) (listof c-inline acyclic))
  (lambda (xs n)
    (cond ((null? xs) xs)
          ((symbol=? (extract (car xs) 1) n) (c-drop-inline (cdr xs) n))
          (else (the (listof c-inline acyclic) (cons (car xs) (c-drop-inline (cdr xs) n)))))))
;; The most a procedure's body may have to be specialized at a lambda
;; (`c-inline-room`).
(define c-special-limit int 60)

;; A global procedure whose parameter (6) is only called, with (7)
;; arguments, or passed as itself to a call of the procedure: a call with a
;; lambda there may run a copy of the procedure made for that lambda, the
;; lambda's body inlined where the parameter is called (`regcode.fx`'s
;; `r-specialize`). Its name, word, parameters, body and globals, as for
;; `c-inline`.
(define-type c-special
  (productof (1 symbol) (2 tword) (3 (listof (productof (1 symbol) (2 syns-a)) acyclic)) (4 exp) (5 int) (6 int) (7 int)))
(define c-specials (ref (listof c-special acyclic) @k) (new nil))
;; `xs` without `n`'s.
(define c-drop-special (subr (maxeff (read @globals) (read @k) (alloc @k)) ((listof c-special acyclic) symbol) (listof c-special acyclic))
  (lambda (xs n)
    (cond ((null? xs) xs)
          ((symbol=? (extract (car xs) 1) n) (c-drop-special (cdr xs) n))
          (else (the (listof c-special acyclic) (cons (car xs) (c-drop-special (cdr xs) n)))))))

;; A procedure being specialized at a lambda: its global's name, cell and
;; word; the parameter's place and name; how many parameters; the lambda's
;; arity, parameters and body, the names its closure captures in order, and
;; the globals it sees.
(define-type c-spec
  (productof (1 symbol) (2 wglobal) (3 tword) (4 int) (5 symbol) (6 int) (7 int)
             (8 (listof (productof (1 symbol) (2 syns-a)) acyclic)) (9 exp) (10 syms) (11 int)))
(define c-spec-now (ref (listof c-spec @k) @k) (new nil))

;; Two arities found: the same one, or -2 if they differ or either failed;
;; -1 is none found yet.
(define c-arity-merge (subr pure (int int) int)
  (lambda (a b) (cond ((or (= a -2) (= b -2)) -2) ((= a -1) b) ((= b -1) a) ((= a b) a) (else -2))))
;; Whether `ns` has `n`.
(define c-names-have? (subr (read @globals) (names symbol) bool)
  (lambda (ns n) (and (not (null? ns)) (or (symbol=? (car ns) n) (c-names-have? (cdr ns) n)))))
;; The `k`th of `es`.
(define c-nth (subr (read @globals) ((listof exp acyclic) int) exp)
  (lambda (es k) (if (= k 0) (car es) (c-nth (cdr es) (- k 1)))))
;; How many of `n` parser-tree nodes are left once `x`'s are counted, as the
;; Rust compiler's `inline_room` counts them: negative, and counted no
;; further, once they run out, or at a form that makes a closure, which an
;; inlined body would have to capture its slots in.
(define-rec
  (c-inline-room (subr (maxeff (read @globals) spin) (exp int) int)
    (lambda (x n0)
      (let ((n (- n0 1)))
        (if (< n 0)
            n
            (tagcase x
              (e-lambda (ps body a b) -1)
              (e-rlambda (r l a b) -1)
              (e-letrec (bs body a b) -1)
              (e-prompt (t body h a b) -1)
              (e-app (f args a b) (c-inline-room-all args (c-inline-room f n)))
              (e-plambda (d body a b) (c-inline-room body n))
              (e-proj (body ds a b) (c-inline-room body n))
              (e-the (d body a b) (c-inline-room body n))
              (e-convention (cnv body a b) (c-inline-room body n))
              (e-letregion (k r i body a b) (c-inline-room body n))
              (e-if (t th el a b) (c-inline-room-if el (c-inline-room-if th (c-inline-room t n))))
              (e-let (bs body a b) (c-inline-room-if body (c-inline-room-let bs n)))
              (e-begin (es a b) (c-inline-room-all es n))
              (e-bloblet (op i args a b) (c-inline-room-all args n))
              (e-product (fs a b) (c-inline-room-let fs n))
              (e-extract (p l a b) (c-inline-room p n))
              (e-sum (t v a b) (c-inline-room v n))
              (e-tagcase (s arms els a b)
                (c-inline-room-else els (c-inline-room-arms arms (c-inline-room s n))))
              (else y n))))))
  ;; `x`'s nodes counted from `n`, unless none are left.
  (c-inline-room-if (subr (maxeff (read @globals) spin) (exp int) int)
    (lambda (x n) (if (< n 0) n (c-inline-room x n))))
  (c-inline-room-all (subr (maxeff (read @globals) spin) ((listof exp acyclic) int) int)
    (lambda (es n) (if (or (null? es) (< n 0)) n (c-inline-room-all (cdr es) (c-inline-room (car es) n)))))
  (c-inline-room-let (subr (maxeff (read @globals) spin) ((listof (productof (1 symbol) (2 exp)) acyclic) int) int)
    (lambda (bs n) (if (or (null? bs) (< n 0)) n (c-inline-room-let (cdr bs) (c-inline-room (extract (car bs) 2) n)))))
  (c-inline-room-arms (subr (maxeff (read @globals) spin) ((listof (productof (1 symbol) (2 bool) (3 names) (4 exp)) acyclic) int) int)
    (lambda (arms n)
      (if (or (null? arms) (< n 0)) n (c-inline-room-arms (cdr arms) (c-inline-room (extract (car arms) 4) n)))))
  (c-inline-room-else (subr (maxeff (read @globals) spin) ((listof (productof (1 symbol) (2 exp)) acyclic) int) int)
    (lambda (els n) (if (or (null? els) (< n 0)) n (c-inline-room (extract (car els) 2) n)))))
;; Whether `p` is, in `x`, only called, or passed as itself as argument `k`
;; of `n` to a call of `f`, nothing binding either name again, as the Rust
;; compiler's `call_only` says: the arity it is called with (every call the
;; same), -1 if it is not called, or -2 if not so.
(define-rec
  (c-call-only (subr (maxeff (read @globals) spin) (exp symbol symbol int int) int)
    (lambda (x p f k n)
      (tagcase x
        (e-var (m a b) (if (symbol=? m p) -2 -1))
        (e-app (fun args a b)
          (tagcase fun
            (e-var (m fa fb)
              (cond ((symbol=? m p) (c-arity-merge (c-count-exps args) (c-call-only-all args p f k n)))
                    ((and (symbol=? m f)
                          (and (= (c-count-exps args) n)
                               (tagcase (c-nth args k) (e-var (q qa qb) (symbol=? q p)) (else y #f))))
                     (c-call-only-but args p f k n 0))
                    (else (c-arity-merge (c-call-only fun p f k n) (c-call-only-all args p f k n)))))
            (else y (c-arity-merge (c-call-only fun p f k n) (c-call-only-all args p f k n)))))
        (e-plambda (d body a b) (c-call-only body p f k n))
        (e-proj (body ds a b) (c-call-only body p f k n))
        (e-the (d body a b) (c-call-only body p f k n))
        (e-convention (cnv body a b) (c-call-only body p f k n))
        (e-letregion (kind r i body a b) (if (or (symbol=? r p) (symbol=? r f)) -2 (c-call-only body p f k n)))
        (e-if (t th el a b)
          (c-arity-merge (c-call-only t p f k n) (c-arity-merge (c-call-only th p f k n) (c-call-only el p f k n))))
        (e-let (bs body a b) (c-arity-merge (c-call-only-let bs p f k n) (c-call-only body p f k n)))
        (e-begin (es a b) (c-call-only-all es p f k n))
        (e-bloblet (op i args a b) (c-call-only-all args p f k n))
        (e-product (fs a b) (c-call-only-fields fs p f k n))
        (e-extract (e l a b) (c-call-only e p f k n))
        (e-sum (t v a b) (c-call-only v p f k n))
        (e-tagcase (s arms els a b)
          (c-arity-merge (c-call-only s p f k n) (c-arity-merge (c-call-only-arms arms p f k n) (c-call-only-else els p f k n))))
        (e-lambda (ps body a b) -2)
        (e-rlambda (r l a b) -2)
        (e-letrec (bs body a b) -2)
        (e-prompt (t body h a b) -2)
        (else y -1))))
  (c-call-only-all (subr (maxeff (read @globals) spin) ((listof exp acyclic) symbol symbol int int) int)
    (lambda (es p f k n) (if (null? es) -1 (c-arity-merge (c-call-only (car es) p f k n) (c-call-only-all (cdr es) p f k n)))))
  ;; Every argument but the `k`th; `i` counts.
  (c-call-only-but (subr (maxeff (read @globals) spin) ((listof exp acyclic) symbol symbol int int int) int)
    (lambda (es p f k n i)
      (cond ((null? es) -1)
            ((= i k) (c-call-only-but (cdr es) p f k n (+ i 1)))
            (else (c-arity-merge (c-call-only (car es) p f k n) (c-call-only-but (cdr es) p f k n (+ i 1)))))))
  (c-call-only-let (subr (maxeff (read @globals) spin) ((listof (productof (1 symbol) (2 exp)) acyclic) symbol symbol int int) int)
    (lambda (bs p f k n)
      (cond ((null? bs) -1)
            ((or (symbol=? (extract (car bs) 1) p) (symbol=? (extract (car bs) 1) f)) -2)
            (else (c-arity-merge (c-call-only (extract (car bs) 2) p f k n) (c-call-only-let (cdr bs) p f k n))))))
  (c-call-only-fields (subr (maxeff (read @globals) spin) ((listof (productof (1 symbol) (2 exp)) acyclic) symbol symbol int int) int)
    (lambda (fs p f k n)
      (if (null? fs) -1 (c-arity-merge (c-call-only (extract (car fs) 2) p f k n) (c-call-only-fields (cdr fs) p f k n)))))
  (c-call-only-arms
    (subr (maxeff (read @globals) spin) ((listof (productof (1 symbol) (2 bool) (3 names) (4 exp)) acyclic) symbol symbol int int) int)
    (lambda (arms p f k n)
      (cond ((null? arms) -1)
            ((or (c-names-have? (extract (car arms) 3) p) (c-names-have? (extract (car arms) 3) f)) -2)
            (else (c-arity-merge (c-call-only (extract (car arms) 4) p f k n) (c-call-only-arms (cdr arms) p f k n))))))
  (c-call-only-else (subr (maxeff (read @globals) spin) ((listof (productof (1 symbol) (2 exp)) acyclic) symbol symbol int int) int)
    (lambda (els p f k n)
      (cond ((null? els) -1)
            ((or (symbol=? (extract (car els) 1) p) (symbol=? (extract (car els) 1) f)) -2)
            (else (c-call-only (extract (car els) 2) p f k n))))))
;; The first parameter from the `k`th of `ps` that `body` only calls, as
;; `c-call-only` says, and its arity; none if none is.
(define c-first-call-only
  (subr (maxeff (read @globals) (alloc @k) spin) ((listof (productof (1 symbol) (2 syns-a)) acyclic) exp symbol int int) (listof (pairof int int @k) @k))
  (lambda (ps body f k n)
    (if (null? ps)
        nil
        (let ((a (c-call-only body (extract (car ps) 1) f k n)))
          (if (>= a 0)
              (the (listof (pairof int int @k) @k) (cons (cons k a) nil))
              (c-first-call-only (cdr ps) body f (+ k 1) n))))))
;; `x`, each `extract` in it that the checker's facts give a field made the
;; `bloblet-ref` of that field, which compiles as it would: for a body kept
;; to be inlined or specialized in a later form, whose facts, keyed by
;; position in its own form's text, are gone by then.
(define-rec
  (c-resolve-extracts (subr (maxeff (read @globals) (read @k) (alloc @k) spin) (exp) exp)
    (lambda (x)
      (tagcase x
        (e-lambda (ps body a b) (e-lambda ps (c-resolve-extracts body) a b))
        (e-app (f args a b) (e-app (c-resolve-extracts f) (c-resolve-all args) a b))
        (e-plambda (d body a b) (e-plambda d (c-resolve-extracts body) a b))
        (e-proj (body ds a b) (e-proj (c-resolve-extracts body) ds a b))
        (e-if (t c el a b) (e-if (c-resolve-extracts t) (c-resolve-extracts c) (c-resolve-extracts el) a b))
        (e-letrec (bs body a b) (e-letrec (c-resolve-letrec bs) (c-resolve-extracts body) a b))
        (e-let (bs body a b) (e-let (c-resolve-named bs) (c-resolve-extracts body) a b))
        (e-begin (es a b) (e-begin (c-resolve-all es) a b))
        (e-prompt (t body h a b) (e-prompt (c-resolve-extracts t) (c-resolve-extracts body) (c-resolve-extracts h) a b))
        (e-letregion (k r p body a b) (e-letregion k r p (c-resolve-extracts body) a b))
        (e-rlambda (r l a b) (e-rlambda (c-resolve-extracts r) (c-resolve-extracts l) a b))
        (e-the (t body a b) (e-the t (c-resolve-extracts body) a b))
        (e-convention (cv body a b) (e-convention cv (c-resolve-extracts body) a b))
        (e-bloblet (op i args a b) (e-bloblet op i (c-resolve-all args) a b))
        (e-product (fs a b) (e-product (c-resolve-named fs) a b))
        (e-extract (p l a b)
          (let ((i (c-field-at a b)) (q (c-resolve-extracts p)))
            (if (< i 0) (e-extract q l a b) (e-bloblet 'bloblet-ref i (the (listof exp acyclic) (cons q nil)) a b))))
        (e-sum (t v a b) (e-sum t (c-resolve-extracts v) a b))
        (e-tagcase (s arms els a b) (e-tagcase (c-resolve-extracts s) (c-resolve-arms arms) (c-resolve-named els) a b))
        (else y x))))
  (c-resolve-all (subr (maxeff (read @globals) (read @k) (alloc @k) spin) ((listof exp acyclic)) (listof exp acyclic))
    (lambda (es) (if (null? es) es (the (listof exp acyclic) (cons (c-resolve-extracts (car es)) (c-resolve-all (cdr es)))))))
  (c-resolve-named (subr (maxeff (read @globals) (read @k) (alloc @k) spin)
                     ((listof (productof (1 symbol) (2 exp)) acyclic)) (listof (productof (1 symbol) (2 exp)) acyclic))
    (lambda (bs)
      (if (null? bs)
          bs
          (the (listof (productof (1 symbol) (2 exp)) acyclic)
            (cons (product (1 (extract (car bs) 1)) (2 (c-resolve-extracts (extract (car bs) 2)))) (c-resolve-named (cdr bs)))))))
  (c-resolve-letrec (subr (maxeff (read @globals) (read @k) (alloc @k) spin)
                      ((listof (productof (1 symbol) (2 syn) (3 exp)) acyclic)) (listof (productof (1 symbol) (2 syn) (3 exp)) acyclic))
    (lambda (bs)
      (if (null? bs)
          bs
          (the (listof (productof (1 symbol) (2 syn) (3 exp)) acyclic)
            (cons (product (1 (extract (car bs) 1)) (2 (extract (car bs) 2)) (3 (c-resolve-extracts (extract (car bs) 3))))
                  (c-resolve-letrec (cdr bs)))))))
  (c-resolve-arms (subr (maxeff (read @globals) (read @k) (alloc @k) spin)
                    ((listof (productof (1 symbol) (2 bool) (3 names) (4 exp)) acyclic))
                    (listof (productof (1 symbol) (2 bool) (3 names) (4 exp)) acyclic))
    (lambda (arms)
      (if (null? arms)
          arms
          (the (listof (productof (1 symbol) (2 bool) (3 names) (4 exp)) acyclic)
            (cons (product (1 (extract (car arms) 1)) (2 (extract (car arms) 2)) (3 (extract (car arms) 3))
                           (4 (c-resolve-extracts (extract (car arms) 4))))
                  (c-resolve-arms (cdr arms))))))))
;; A definition of `n` as a lambda just compiled: inlined where it is
;; called, if small enough and not calling itself; else, with a parameter it
;; only calls, specialized where it is called with a lambda there. Neither
;; if it calls `stay-cellular`.
(define c-record-inline
  (subr (maxeff (read @globals) (read @k) (write @k) (alloc @k) spin) (symbol (listof (productof (1 symbol) (2 syns-a)) acyclic) exp) unit)
  (lambda (n ps unresolved)
    (let ((body (c-resolve-extracts unresolved)))
    (cond ((null? (get c-last-word)) #u)
          ;; Not one that stays cellular, which would make its callers so.
          ((c-mentions? body 'stay-cellular) #u)
          ((and (>= (c-inline-room body c-inline-limit) 0) (not (c-mentions? body n)))
           (set c-inlines
                (the (listof c-inline acyclic) (cons (product (1 n) (2 (car (get c-last-word))) (3 ps) (4 body) (5 (c-genv-now))) (get c-inlines)))))
          ((>= (c-inline-room body c-special-limit) 0)
           (let ((found (c-first-call-only ps body n 0 (c-count-params ps))))
             (if (null? found)
                 #u
                 (set c-specials
                      (the (listof c-special acyclic)
                        (cons (product (1 n) (2 (car (get c-last-word))) (3 ps) (4 body) (5 (c-genv-now))
                                       (6 (car (car found))) (7 (cdr (car found))))
                              (get c-specials)))))))
          (else #u)))))
;; The expression compiled last, in a list (for `compile-note-inline!`).
(define c-last-exp (ref (listof exp @k) @k) (new nil))
;; For a driver that computes a definition's value itself (the REPL, in the
;; native convention), right after compiling `(lambda () init)`: if `init`
;; is a lambda, `n`'s definition as `c-tops` would note it, to be inlined
;; where it is called. Its word is the one compiled before the thunk's.
(define compile-note-inline! (subr (maxeff (read @globals) (read @k) (write @k) (alloc @k) spin) (symbol) unit)
  (lambda (n)
    (let ((x (get c-last-exp)) (w (get c-prev-word)))
      (if (null? x)
          #u
          (tagcase (car x)
            (e-lambda (ps0 thunk a b)
              (let ((l (c-lambda-of thunk)))
                (if (null? l)
                    #u
                    (tagcase (car l)
                      (e-lambda (ps body la lb)
                        (begin (set c-inlines (c-drop-inline (get c-inlines) n))
                               (set c-specials (c-drop-special (get c-specials) n))
                               (set c-last-word w)
                               (c-record-inline n ps body)))
                      (else y #u)))))
            (else y #u))))))
;; Globals kept for their names' next definitions: a redefinition of a type
;; the old one's users can take, for which the REPL asks
;; (`compile-keep-global!`).
(define-type c-kept-globals (listof (pairof symbol wglobal acyclic) acyclic))
(define c-reuse (ref c-kept-globals @k) (new nil))
;; The global kept for `n`, if any.
(define c-kept (subr (read @globals) (c-kept-globals symbol) (listof wglobal acyclic))
  (lambda (ks n)
    (cond ((null? ks) nil)
          ((symbol=? (car (car ks)) n) (the (listof wglobal acyclic) (cons (cdr (car ks)) nil)))
          (else (c-kept (cdr ks) n)))))
;; `ks` without `n`'s.
(define c-unkeep (subr (read @globals) (c-kept-globals symbol) c-kept-globals)
  (lambda (ks n)
    (cond ((null? ks) ks)
          ((symbol=? (car (car ks)) n) (c-unkeep (cdr ks) n))
          (else (the c-kept-globals (cons (car ks) (c-unkeep (cdr ks) n)))))))
;; `n`'s global for a definition of it: the one kept for it, if one was;
;; else a new one, which later uses of `n` refer to.
(define c-push-global (subr (maxeff (read @globals) (read @k) (write @k) (alloc @k)) (symbol) wglobal)
  (lambda (n)
    (let ((kept (begin (set c-inlines (c-drop-inline (get c-inlines) n))
                       (set c-specials (c-drop-special (get c-specials) n))
                       (c-kept (get c-reuse) n))))
      (if (null? kept)
          (let ((g (make-global n)) (i (get c-genv-count)))
            (begin (table-set! (get c-genv-index) n (the (listof (pairof int loc @k) acyclic) (cons (the (pairof int loc @k) (cons i (at-global g))) (table-ref (get c-genv-index) n nil))))
                   (set c-genv-count (+ i 1))
                   g))
          (begin (set c-reuse (c-unkeep (get c-reuse) n)) (car kept))))))
;; For a driver: `n`'s next definition keeps the global `n` has now, so
;; that every use of `n`, before it and after, sees the new value.
(define compile-keep-global! (subr (maxeff (read @globals) (read @k) (write @k) (alloc @k) spin) (symbol) unit)
  (lambda (n)
    (let ((l (c-global-find n -1)))
      (if (null? l)
          #u
          (tagcase (car l)
            (at-global (g) (set c-reuse (the c-kept-globals (cons (cons n g) (get c-reuse)))))
            (else y #u))))))
;; For a driver that computes a definition's value itself (the REPL, in the
;; native convention): `n`'s global from now on, made, for the driver to
;; fill.
(define compile-new-global (subr (maxeff (read @globals) (read @k) (write @k) (alloc @k)) (symbol) wglobal)
  (lambda (n) (c-push-global n)))
;; For a driver that makes a global's value native code (the REPL, in the
;; native convention): `n`'s global, in a list, if it is one.
(define compile-global-cell (subr (maxeff (read @globals) (read @k) (alloc @k) spin) (symbol) (listof wglobal @k))
  (lambda (n)
    (let ((l (c-global-find n -1)))
      (if (null? l)
          nil
          (tagcase (car l)
            (at-global (g) (cons g nil))
            (else y nil))))))




(define c-rec-globals (subr (maxeff (read @globals) (read @k) (write @k) (alloc @k)) ((listof (productof (1 symbol) (2 syn) (3 exp)) acyclic)) (listof wglobal @k))
  (lambda (bs) (if (null? bs) nil (let ((g (c-push-global (extract (car bs) 1)))) (cons g (c-rec-globals (cdr bs)))))))
(define c-rec-fill (subr (maxeff compiles spin) ((listof (productof (1 symbol) (2 syn) (3 exp)) acyclic) (listof wglobal @k) code) unit)
  (lambda (bs gs c)
    (if (null? bs)
        #u
        (begin (c-exp (extract (car bs) 3) (the cenv nil) 0 c #f)
               (c-op1 c routine-global! (wcell-global (car gs)))
               (c-rec-fill (cdr bs) (cdr gs) c)))))

;; Each form in turn; the last expression's value is left on the stack.
(define c-tops (subr (maxeff compiles spin) ((listof top acyclic) code bool) bool)
  (lambda (ts c has-value)
    (if (null? ts)
        has-value
        (tagcase (car ts)
          (t-define (n ty x a b)
            (begin
              (if has-value (c-op c routine-drop) #u)
              (if (null? ty)
                  (begin (c-exp x (the cenv nil) 0 c #f)
                         (c-op1 c routine-global! (wcell-global (c-push-global n))))
                  (if (null? (c-lambda-of x))
                      (begin (c-exp x (the cenv nil) 0 c #f)
                             (c-op1 c routine-global! (wcell-global (c-push-global n))))
                      ;; A lambda: its global first, so that it can call itself,
                      ;; through the global, as any use of it does
                      ;; (`docs/fx26.md`, "Redefinition").
                      (let ((g (c-push-global n)))
                        (begin (tagcase (car (c-lambda-of x))
                                 (e-lambda (ps body la lb)
                                   (begin (set c-defining (the (listof symbol @k) (cons n nil)))
                                          (c-lambda ps body (the cenv nil) 0 c (the syms nil) (the (listof exp @k) nil))
                                          (set c-defining (the (listof symbol @k) nil))
                                          (c-record-inline n ps body)))
                                 (else y (c-exp x (the cenv nil) 0 c #f)))
                               (c-op1 c routine-global! (wcell-global g))))))
              (c-tops (cdr ts) c #f)))
          ;; Every name's global first; then each lambda, which runs nothing.
          (t-define-rec (bs a b)
            (begin
              (if has-value (c-op c routine-drop) #u)
              (c-rec-fill bs (c-rec-globals bs) c)
              (c-tops (cdr ts) c #f)))
          (t-exp (x)
            (begin (if has-value (c-op c routine-drop) #u)
                   (set c-last-exp (the (listof exp @k) (cons x nil)))
                   (c-exp x (the cenv nil) 0 c #f)
                   (c-tops (cdr ts) c #t)))
          (else y (c-tops (cdr ts) c has-value))))))

;; The entry point: a program's trees to one word that runs it and leaves
;; the value of its last expression (unit, if it has none).
;; Before a run that assigns its names' globals (`checked-tops`): each
;; name's next definition keeps the global it has.
(define c-keep-names (subr (maxeff (read @globals) (read @k) (write @k) (alloc @k) spin) (top) unit)
  (lambda (t)
    (tagcase t
      (t-define (n ty x a b) (compile-keep-global! n))
      (t-define-rec (bs a b)
        (letrec ((go (subr (maxeff (read @globals) (read @k) (write @k) (alloc @k) spin) ((listof (productof (1 symbol) (2 syn) (3 exp)) acyclic)) unit)
                   (lambda (bs) (if (null? bs) #u (begin (compile-keep-global! (extract (car bs) 1)) (go (cdr bs)))))))
          (go bs)))
      (else y #u))))
;; What a checked program runs (`checked-tops`), each in turn: whether the
;; last was an expression, whose value stays.
(define c-runs (subr (maxeff compiles spin) ((listof k-run acyclic) code bool) bool)
  (lambda (rs c has-value)
    (if (null? rs)
        has-value
        (let ((r (car rs)))
          (begin (if (extract r 2) (c-keep-names (extract r 1)) #u)
                 (c-runs (cdr rs) c (c-tops (the (listof top acyclic) (cons (extract r 1) nil)) c has-value)))))))
;; The entry point for a program the checker written in FX-26 checked: what
;; it runs (`checked-tops`, under redefinition), and what checking found.
(define compile-checked (subr (maxeff (read @globals) compiles (comefrom @y) spin) ((listof k-run acyclic) k-facts) cresult)
  (lambda (runs facts)
    (prompt c-tag
      (let ((c (the code (new nil))))
        (begin
          (c-set-facts! facts)
          (set c-this-params -1)
          (if (c-runs runs c #f) #u (c-lit c (wcell-unit)))
          (c-op c routine-exit)
          (c-ok (c-assemble c (string->symbol "program")))))
      (lambda (r) r))))
;; The entry point: a checked program's trees, and what checking found.
(define compile-program (subr (maxeff (read @globals) compiles (comefrom @y) spin) ((listof top acyclic) k-facts) cresult)
  (lambda (tops facts)
    (prompt c-tag
      (let ((c (the code (new nil))))
        (begin
          (c-set-facts! facts)
          (set c-this-params -1)
          (if (c-tops tops c #f) #u (c-lit c (wcell-unit)))
          (c-op c routine-exit)
          (c-ok (c-assemble c (string->symbol "program")))))
      (lambda (r) r))))
