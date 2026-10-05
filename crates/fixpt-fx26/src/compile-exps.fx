;;; The compiler written in FX-26: expressions. After `compile-lift.fx`
;;; (PLAN.md §11, 9d).

;;; ---------------------------------------------------------- expressions
;;; `depth` is how many values are on the frame above its start, so the next
;;; value pushed is slot `depth`. In tail position, code ends the word: with
;;; a `tailcall`, or with `return` after the value.

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

;; A lambda's word, and the names its closure captures, in order.
(define-type c-closing (productof (1 tword) (2 syms)))

;; An `rlambda`'s region, in a list; none for a plain lambda.
(define-type c-region (listof exp @k))

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
        (find (get c-made-reuse))))))

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

;; A lambda's word's name: `named`'s, if it has one; else where its body
;; starts, so that a profile can say which.
(define c-word-symbol (subr c-walks ((listof string @k) exp) symbol)
  (lambda (named body)
    (string->symbol
      (if (null? named) (string-append "lambda@" (c-place-name (exp-start body))) (car named)))))

;; `cells` as word `w`'s register twin, unless there are none.
(define c-twin! (subr c-emits (tword (listof wcell @k)) unit)
  (lambda (w cells) (if (null? cells) #u (begin (set-register-twin w cells) #u))))

;; Register code for the lambda of `ps` and `body` as word `w`'s twin, when
;; this compiler makes it (`c-registers`), made with the words its stack
;; code made; `defining`, the definition it is, if it is one.
(define c-register-twin!
  (subr (maxeff compiles spin) (tword c-params exp cenv (listof c-this @k) (listof symbol @k)) unit)
  (lambda (w ps body inner this defining)
    (if (get c-registers)
        (begin
          (set c-own-now
               (if (null? defining)
                   (the (listof (productof (1 symbol) (2 tword)) @k) nil)
                   (cons (product (1 (car defining)) (2 w)) nil)))
          (let* ((outer-reuse (get c-made-reuse))
                 (cells (begin (set c-made-reuse (get c-made-now))
                               (set c-made-now (the (listof c-made @k) nil))
                               ((get c-register-code) ps body inner this))))
            (begin (set c-made-reuse outer-reuse) (c-twin! w cells))))
        #u)))

;; A typed call of `n` arguments: in tail position, a tail call.
(define c-typed-call (subr c-emits (code int bool) unit)
  (lambda (c n tail)
    (if tail (c-op1 c routine-ttailcall (wcell-int n)) (c-op1 c routine-tcall (wcell-int n)))))

;; The standard operation `f` names, if it is a name bound nowhere else;
;; else "".
(define c-standard-name (subr c-walks (exp cenv) string)
  (lambda (f e)
    (tagcase f
      (e-var (n a b) (if (null? (c-where e n)) (symbol->string n) ""))
      (else y ""))))

;; The module in slot `depth`'s fields at positions `at`, pushed.
(define c-reshape-fields (subr (maxeff compiles spin) (k-ids int code) unit)
  (lambda (at depth c)
    (if (null? at)
        #u
        (begin (c-op1 c routine-slot (wcell-int depth)) (c-field c (+ (car at) 2))
               (c-reshape-fields (cdr at) depth c)))))
;; Each slot of `ss`, newest first, pushed, the oldest first: how many.
(define c-slots-load (subr (maxeff c-emits spin) ((listof int @k) code) int)
  (lambda (ss c)
    (if (null? ss)
        0
        (let ((n (c-slots-load (cdr ss) c)))
          (begin (c-op1 c routine-slot (wcell-int (car ss))) (+ n 1))))))
;; `vals` with the `n` slots from `d` on it, newest first.
(define c-slots-from
  (subr (maxeff (read @globals) (alloc @k) spin) (int int (listof int @k)) (listof int @k))
  (lambda (d n vals) (if (= n 0) vals (c-slots-from (+ d 1) (- n 1) (cons d vals)))))
;; A `with`'s module, at `l`, its values `ns` from field `i` on, each into
;; the next slot from `depth`: `e` with them bound.
(define c-with-fields (subr (maxeff compiles spin) (syms loc cenv int int code) cenv)
  (lambda (ns l e depth i c)
    (if (null? ns)
        e
        (begin (c-load c l) (c-field c (+ i 2))
               (let ((inner (c-extend (car ns) (at-slot (+ depth i)) e)))
                 (c-with-fields (cdr ns) l inner depth (+ i 1) c))))))

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
                   (c-module items e depth depth nil c tail)
                   (set c-module-members (get c-collecting))
                   (set c-collecting outer))))
        (e-with (m body a b) (c-with m body a b e depth c tail)))))
  ;; A module (`docs/research/first-class-modules.md`): its items bound in
  ;; slots in order from `depth`, as a `let`'s and a `letrec`'s are, `d` the
  ;; next and `vals` the values' slots (newest first); then the product of
  ;; its values.
  (c-module
    (subr (maxeff compiles spin) (mod-items cenv int int (listof int @k) code bool) unit)
    (lambda (items e depth d vals c tail)
      (if (null? items)
          (let ((n (begin (c-int c 37) (c-slots-load vals c))))
            (begin (c-prim c "%make-frozen" (+ 1 n))
                   (c-done c tail)
                   (c-unbind c depth (- d depth) tail)))
          (let* ((it (car items)) (k (extract it 1)) (ns (extract it 2)) (xs (extract it 4)))
            (cond
              ((or (= k 1) (< k 0) (> k 3)) (c-module (cdr items) e depth d vals c tail))
              ((= k 0)
               (let* ((up (begin (c-exp (car xs) e d c #f)
                                 (c-extend (c-converter "up-" (car ns)) (at-slot d) e)))
                      (down (begin (c-exp (car (cdr xs)) up (+ d 1) c #f)
                                   (c-extend (c-converter "down-" (car ns)) (at-slot (+ d 1)) up))))
                 (c-module (cdr items) down depth (+ d 2) vals c tail)))
              ((= k 2)
               (begin (c-exp (car xs) e d c #f)
                      (c-note-member! (car ns) (car xs) e)
                      (c-module (cdr items) (c-extend (car ns) (at-slot d) e) depth (+ d 1)
                                (cons d vals) c tail)))
              (else
               (let* ((bs (c-rec-of ns (extract it 3) xs))
                      (n (c-count-letrec bs))
                      (made (c-letrec-make bs bs e d 0 c)))
                 (begin (c-letrec-patch made d 0 c)
                        (c-module (cdr items) (c-letrec-slots bs e d) depth (+ d n)
                                  (c-slots-from d n vals) c tail)))))))))
  ;; `with`: the module's values, by position, in slots from `depth`; then
  ;; the body.
  (c-with (subr (maxeff compiles spin) (symbol exp int int cenv int code bool) unit)
    (lambda (m body a b e depth c tail)
      (let ((ns (c-with-at a b)) (l (c-where e m)))
        (cond ((null? ns) (c-fail "a `with` the checker did not see"))
              ((null? l) (c-fail "a `with` of an unbound module"))
              (else
               (let ((inner (c-with-fields (car ns) (car l) e depth 0 c)))
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
          (begin (c-exp (extract (car bs) 2) outer depth c #f)
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
            (let ((plan (c-lift-plan bs body e tail)))
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
        (begin
          (set c-made-now
               (cons (product (1 (exp-start body)) (2 (exp-end body)) (3 (c-bind-params ps nil))
                              (4 (c-own-of ps own0)) (5 (extract made 1)) (6 (extract made 2)))
                     outer))
          made))))
  ;; The same, with the words of the lambdas in it noted as made.
  (c-lambda-word-in (subr (maxeff compiles spin) (c-params exp cenv syms) c-closing)
    (lambda (ps body e own0)
      (let* ((named (c-take c-word-name (the (listof string @k) nil)))
             (defining (c-take c-defining (the (listof symbol @k) nil)))
             (fv (c-lambda-captured ps body e))
             ;; The parameters a lifting added, first (`c-lift`).
             (added (c-take c-lifting-added 0))
             ;; A parameter of the same name hides the procedure.
             (own (c-own-of ps own0))
             (inner (c-inner-env fv e (c-param-env ps 0 (c-own-scope own fv e)) 0))
             (n (c-count-params ps))
             (body-code (the code (new nil)))
             (outer (c-this-saved)) (outer-start (get c-this-start))
             (this (c-this-of own inner n added)))
        (begin
          (if (null? this)
              (set c-this-params -1)
              (let ((start (c-fresh)))
                (begin (c-this-enter! (car this) start) (c-emit body-code (i-label start)))))
          (c-exp body inner n body-code #t)
          (c-this-enter! outer outer-start)
          (let ((w (c-assemble body-code (c-word-symbol named body))))
            (begin
              (c-register-twin! w ps body inner this defining)
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
      (cond ((string=? op "make-bloblet") (c-prim c "%make-bloblet" (c-exps args e depth c)))
            ((string=? op "rmake-bloblet")
             (c-prim c "%region-make-bloblet" (c-exps args e depth c)))
            ((string=? op "bloblet-ref")
             (begin (c-exps args e depth c) (c-field c (+ i 2))))
            ((string=? op "bloblet-set!")
             (begin (c-exp (car args) e depth c #f) (c-int c (+ i 2))
                    (c-exp (car (cdr args)) e (+ depth 2) c #f)
                    (c-prim c "%bloblet-set!" 3) (c-unit-after c)))
            ((string=? op "bloblet-freeze")
             (begin (c-exps args e depth c) (c-op c routine-dup)
                    (c-lit c (wcell-bool #t)) (c-lit c (wcell-bool #f))
                    (c-prim c "%bloblet-freeze!" 3) (c-op c routine-drop)))
            ((string=? op "bloblet-byte") (c-prim c "%bloblet-byte" (c-exps args e depth c)))
            ((string=? op "bloblet-set-byte!")
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
              (c-arms (cdr arms) els e depth c tail end)))))))
