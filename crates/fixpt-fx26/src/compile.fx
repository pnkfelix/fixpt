;;; The compiler from FX-26 to threaded words, in FX-26 (PLAN.md §11, 9d).
;;;
;;; The parser's trees to words for the threaded machine (`layout::threaded`,
;;; the MacScheme-like part of it): a lambda's arguments are its frame on the
;;; data stack, a `let`'s values are pushed onto the frame and are slots of
;;; it, closures are flat, globals are cells, and a call in tail position is
;;; a `tailcall`. A variable is resolved here, once: to a slot, a free value
;;; of the closure, a global's cell, or, for `letrec`'s, which closures
;;; capture before they have their values, a box in a slot or free value.
;;; FX-26 has no assignment to variables, so nothing else is boxed.
;;;
;;; Globals follow the evaluator and the lowering to Scheme: a form sees the
;;; definitions made before it, a second `define` shadows the first, and a
;;; typed definition is given its cell ahead, so forms before it can call it.
;;;
;;; Control is the machine's: a `prompt`'s body is compiled as a closure of
;;; no arguments, so that everything inside the prompt is above its marker
;;; on the stacks; the control operations are routines.
;;;
;;; `extract` needs a product's field order, which only its type says: the
;;; checker written in FX-26 records it (`checked-extracts`), and a program
;;; is compiled with what its check found.

(private-regions @k @y)

;; What compiling may do: read the trees, build code on @k, and give up.
(define-effect compiles (maxeff (read @a) (read @t) (read @k) (write @k) (alloc @k) (goto @y)))

;; The checker's facts for the program being compiled.
(define c-facts (ref k-facts @k) (new nil))
(define c-field-index (subr (maxeff (read @t) (read @k)) (k-facts int int) int)
  (lambda (fs a b)
    (cond ((null? fs) -1)
          ((and (= (extract (car fs) 1) a) (= (extract (car fs) 2) b)) (extract (car fs) 3))
          (else (c-field-index (cdr fs) a b)))))

;;; ----------------------------------------------------------------- code

(define-datatype item
  (i-cell wcell)
  (i-label int)
  (i-branch int)
  (i-zbranch int))
(define-type items (listof item @k))
;; The code for one word so far, newest first.
(define-type code (ref items @k))

(define-datatype cresult (c-ok tword) (c-err string))
(define c-tag (prompt-tag cresult cresult (maxeff (read @a) (read @t) (read @k) (write @k) (alloc @k)) @y)
  (make-continuation-prompt-tag))
(define c-fail (subr compiles (string) void)
  (lambda (message) (abort-current-continuation c-tag (c-err message))))

(define c-labels (ref int @k) (new 0))
(define c-fresh (subr (maxeff (read @k) (write @k)) () int)
  (lambda () (let ((n (get c-labels))) (begin (set c-labels (+ n 1)) n))))

(define c-emit (subr (maxeff (read @k) (write @k) (alloc @k)) (code item) unit)
  (lambda (c i) (set c (cons i (get c)))))
(define c-op (subr (maxeff (read @k) (write @k) (alloc @k)) (code int) unit)
  (lambda (c r) (c-emit c (i-cell (wcell-routine r)))))
(define c-op1 (subr (maxeff (read @k) (write @k) (alloc @k)) (code int wcell) unit)
  (lambda (c r x) (begin (c-op c r) (c-emit c (i-cell x)))))
(define c-lit (subr (maxeff (read @k) (write @k) (alloc @k)) (code wcell) unit)
  (lambda (c x) (c-op1 c routine-lit x)))
(define c-int (subr (maxeff (read @k) (write @k) (alloc @k)) (code int) unit)
  (lambda (c n) (c-lit c (wcell-int n))))

;; A runtime primitive with `n` arguments.
(define c-prim (subr compiles (code string int) unit)
  (lambda (c name n)
    (let ((p (runtime-primitive name)))
      (if (< p 0)
          (c-fail (string-append "no runtime primitive " name))
          (begin (c-op1 c routine-prim (wcell-int p)) (c-emit c (i-cell (wcell-int n))))))))

;; Drop what a mutator left, and leave FX-26's unit value instead.
(define c-unit-after (subr (maxeff (read @k) (write @k) (alloc @k)) (code) unit)
  (lambda (c) (begin (c-op c routine-drop) (c-lit c (wcell-unit)))))

;;; ----------------------------------------------------------- assembling

(define c-reverse (subr (maxeff (read @k) (alloc @k)) (items items) items)
  (lambda (xs acc) (if (null? xs) acc (c-reverse (cdr xs) (cons (car xs) acc)))))

(define c-size (subr pure (item) int)
  (lambda (i) (tagcase i (i-cell (x) 1) (i-label (n) 0) (i-branch (n) 2) (i-zbranch (n) 2))))

;; Where each label is, in cells.
(define c-place (subr (maxeff (read @k) (write @k)) (items (arrayof int @k) int) unit)
  (lambda (xs at pos)
    (if (null? xs)
        #u
        (begin (tagcase (car xs) (i-label (n) (array-set! at n pos)) (else x #u))
               (c-place (cdr xs) at (+ pos (c-size (car xs))))))))

;; The cells, branches resolved: an offset counts from the cell after it.
(define c-cells (subr (maxeff (read @k) (alloc @k)) (items (arrayof int @k) int) (listof wcell @k))
  (lambda (xs at pos)
    (if (null? xs)
        nil
        (let ((rest (c-cells (cdr xs) at (+ pos (c-size (car xs))))))
          (tagcase (car xs)
            (i-cell (x) (cons x rest))
            (i-label (n) rest)
            (i-branch (n)
              (cons (wcell-routine routine-branch) (cons (wcell-int (- (array-ref at n) (+ pos 2))) rest)))
            (i-zbranch (n)
              (cons (wcell-routine routine-zbranch) (cons (wcell-int (- (array-ref at n) (+ pos 2))) rest))))))))

(define c-assemble (subr (maxeff (read @k) (write @k) (alloc @k)) (code symbol) tword)
  (lambda (c name)
    (let* ((xs (c-reverse (get c) nil)) (at (the (arrayof int @k) (make-array (get c-labels) 0))))
      (begin (c-place xs at 0) (make-word name (c-cells xs at 0))))))

;;; ------------------------------------------------------------ variables

(define-datatype loc
  (at-slot int)
  (at-free int)
  (at-global wglobal)
  (boxed-slot int)
  (boxed-free int))
(define-type cenv (listof (pairof symbol loc @k) @k))

;; The global environment as compiling has reached it, newest first, and the
;; names given a cell ahead of their typed definitions.
(define c-genv (ref cenv @k) (new nil))
(define c-declared (ref (listof symbol @k) @k) (new nil))

(define c-find (subr (maxeff (read @k) (alloc @k)) (cenv symbol) (listof loc @k))
  (lambda (e n)
    (cond ((null? e) nil)
          ((symbol=? (car (car e)) n) (the (listof loc @k) (cons (cdr (car e)) nil)))
          (else (c-find (cdr e) n)))))

;; Where `n` is: in the locals, else in the globals; none means standard.
(define c-where (subr (maxeff (read @k) (alloc @k)) (cenv symbol) (listof loc @k))
  (lambda (e n) (let ((l (c-find e n))) (if (null? l) (c-find (get c-genv) n) l))))

(define c-load (subr compiles (code loc) unit)
  (lambda (c l)
    (tagcase l
      (at-slot (i) (c-op1 c routine-slot (wcell-int i)))
      (at-free (i) (c-op1 c routine-free (wcell-int i)))
      (at-global (g) (c-op1 c routine-global (wcell-global g)))
      (boxed-slot (i) (begin (c-op1 c routine-slot (wcell-int i)) (c-int c 2) (c-op c routine-field-ref)))
      (boxed-free (i) (begin (c-op1 c routine-free (wcell-int i)) (c-int c 2) (c-op c routine-field-ref))))))

;;; ------------------------------------------------------------- free names
;;; The names a lambda's body uses that it does not bind: what its closure
;;; must carry, once globals and standard names are set aside.

(define-type syms (listof symbol @k))

(define c-member? (subr (read @k) (syms symbol) bool)
  (lambda (xs n) (and (not (null? xs)) (or (symbol=? (car xs) n) (c-member? (cdr xs) n)))))
(define c-adjoin (subr (maxeff (read @k) (alloc @k)) (syms symbol) syms)
  (lambda (xs n) (if (c-member? xs n) xs (cons n xs))))

(define c-free-all (subr (maxeff (read @a) (read @k) (alloc @k)) ((listof exp @a) syms syms) syms)
  (lambda (es bound acc) (if (null? es) acc (c-free-all (cdr es) bound (c-free (car es) bound acc)))))

(define c-free (subr (maxeff (read @a) (read @k) (alloc @k)) (exp syms syms) syms)
  (lambda (x bound acc)
    (tagcase x
      (e-var (n a b) (if (c-member? bound n) acc (c-adjoin acc n)))
      (e-lambda (ps body a b) (c-free body (c-bind-params ps bound) acc))
      (e-app (f args a b) (c-free f bound (c-free-all args bound acc)))
      (e-plambda (d body a b) (c-free body bound acc))
      (e-proj (body ds a b) (c-free body bound acc))
      (e-the (d body a b) (c-free body bound acc))
      (e-if (t th el a b) (c-free t bound (c-free th bound (c-free el bound acc))))
      (e-letrec (bs body a b)
        (let ((inner (c-bind-letrec bs bound)))
          (c-free body inner (c-free-letrec bs inner acc))))
      (e-let (bs body a b) (c-free body (c-bind-let bs bound) (c-free-let bs bound acc)))
      (e-begin (es a b) (c-free-all es bound acc))
      (e-prompt (t body h a b) (c-free t bound (c-free body bound (c-free h bound acc))))
      (e-bloblet (op i args a b) (c-free-all args bound acc))
      (e-product (fs a b) (c-free-fields fs bound acc))
      (e-extract (p l a b) (c-free p bound acc))
      (e-sum (t v a b) (c-free v bound acc))
      (e-tagcase (s arms els a b) (c-free s bound (c-free-arms arms bound (c-free-else els bound acc))))
      (else y acc))))

(define c-bind-params (subr (maxeff (read @a) (read @k) (alloc @k)) ((listof (productof (1 symbol) (2 syns-a)) @a) syms) syms)
  (lambda (ps bound) (if (null? ps) bound (c-bind-params (cdr ps) (cons (extract (car ps) 1) bound)))))
(define c-bind-letrec (subr (maxeff (read @a) (read @k) (alloc @k)) ((listof (productof (1 symbol) (2 syn) (3 exp)) @a) syms) syms)
  (lambda (bs bound) (if (null? bs) bound (c-bind-letrec (cdr bs) (cons (extract (car bs) 1) bound)))))
(define c-bind-let (subr (maxeff (read @a) (read @k) (alloc @k)) ((listof (productof (1 symbol) (2 exp)) @a) syms) syms)
  (lambda (bs bound) (if (null? bs) bound (c-bind-let (cdr bs) (cons (extract (car bs) 1) bound)))))
(define c-free-letrec (subr (maxeff (read @a) (read @k) (alloc @k)) ((listof (productof (1 symbol) (2 syn) (3 exp)) @a) syms syms) syms)
  (lambda (bs bound acc) (if (null? bs) acc (c-free-letrec (cdr bs) bound (c-free (extract (car bs) 3) bound acc)))))
(define c-free-let (subr (maxeff (read @a) (read @k) (alloc @k)) ((listof (productof (1 symbol) (2 exp)) @a) syms syms) syms)
  (lambda (bs bound acc) (if (null? bs) acc (c-free-let (cdr bs) bound (c-free (extract (car bs) 2) bound acc)))))
(define c-free-fields (subr (maxeff (read @a) (read @k) (alloc @k)) ((listof (productof (1 symbol) (2 exp)) @a) syms syms) syms)
  (lambda (fs bound acc) (if (null? fs) acc (c-free-fields (cdr fs) bound (c-free (extract (car fs) 2) bound acc)))))
(define c-names (subr (maxeff (read @a) (read @k) (alloc @k)) (names syms) syms)
  (lambda (ns bound) (if (null? ns) bound (c-names (cdr ns) (cons (car ns) bound)))))
(define c-free-arms
  (subr (maxeff (read @a) (read @k) (alloc @k)) ((listof (productof (1 symbol) (2 bool) (3 names) (4 exp)) @a) syms syms) syms)
  (lambda (arms bound acc)
    (if (null? arms)
        acc
        (c-free-arms (cdr arms) bound (c-free (extract (car arms) 4) (c-names (extract (car arms) 3) bound) acc)))))
(define c-free-else (subr (maxeff (read @a) (read @k) (alloc @k)) ((listof (productof (1 symbol) (2 exp)) @a) syms syms) syms)
  (lambda (els bound acc)
    (if (null? els) acc (c-free (extract (car els) 2) (cons (extract (car els) 1) bound) acc))))

;;; ---------------------------------------------------------- expressions
;;; `depth` is how many values are on the frame above its start, so the next
;;; value pushed is slot `depth`. In tail position, code ends the word: with
;;; a `tailcall`, or with `return` after the value.

(define c-exps (subr compiles ((listof exp @a) cenv int code) int)
  (lambda (es e depth c)
    (if (null? es) 0 (begin (c-exp (car es) e depth c #f) (+ 1 (c-exps (cdr es) e (+ depth 1) c))))))

;; What is left when the value is in hand: `return` in tail position.
(define c-done (subr (maxeff (read @k) (write @k) (alloc @k)) (code bool) unit)
  (lambda (c tail) (if tail (c-op c routine-return) #u)))

;; After a body whose value is on top of `n` values bound from `slot`
;; up: the value into `slot`, the others dropped. Nothing in tail
;; position, where `return` drops the whole frame.
(define c-unbind (subr (maxeff (read @k) (write @k) (alloc @k)) (code int int bool) unit)
  (lambda (c slot n tail)
    (if (or tail (= n 0))
        #u
        (letrec ((drops (subr (maxeff (read @k) (write @k) (alloc @k)) (int) unit)
                   (lambda (k) (if (= k 0) #u (begin (c-op c routine-drop) (drops (- k 1)))))))
          (begin (c-op1 c routine-slot! (wcell-int slot)) (drops (- n 1)))))))

(define c-exp (subr compiles (exp cenv int code bool) unit)
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
      (e-lambda (ps body a b) (begin (c-lambda ps body e depth c) (c-done c tail)))
      (e-app (f args a b) (c-app f args e depth c tail))
      (e-plambda (d body a b) (c-exp body e depth c tail))
      (e-proj (body ds a b) (c-exp body e depth c tail))
      (e-the (d body a b) (c-exp body e depth c tail))
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
      (e-let (bs body a b)
        (let* ((inner (c-let-bind bs e e depth c)) (n (c-count-let bs)))
          (begin (c-exp body inner (+ depth n) c tail) (c-unbind c depth n tail))))
      (e-letrec (bs body a b) (c-letrec bs body e depth c tail))
      (e-begin (es a b) (c-begin es e depth c tail))
      (e-prompt (t body h a b)
        (begin
          (c-exp t e depth c #f)
          (c-exp h e (+ depth 1) c #f)
          (c-lambda (the (listof (productof (1 symbol) (2 syns-a)) @a) nil) body e (+ depth 2) c)
          (c-op c routine-prompt)
          (c-done c tail)))
      (e-bloblet (op i args a b) (begin (c-bloblet (symbol->string op) i args e depth c) (c-done c tail)))
      (e-product (fs a b)
        (begin (c-int c 37) (c-prim c "%make-frozen" (+ 1 (c-fields fs e (+ depth 1) c))) (c-done c tail)))
      (e-extract (p l a b)
        (let ((i (c-field-index (get c-facts) a b)))
          (if (< i 0)
              (c-fail "an extract the checker did not see")
              (begin (c-exp p e depth c #f) (c-int c (+ i 2)) (c-op c routine-field-ref) (c-done c tail)))))
      (e-sum (t v a b)
        (begin (c-int c 36) (c-lit c (wcell-symbol t)) (c-exp v e (+ depth 2) c #f)
               (c-prim c "%make-frozen" 3) (c-done c tail)))
      (e-tagcase (s arms els a b) (c-tagcase s arms els e depth c tail)))))

(define c-begin (subr compiles ((listof exp @a) cenv int code bool) unit)
  (lambda (es e depth c tail)
    (cond ((null? es) (begin (c-lit c (wcell-unit)) (c-done c tail)))
          ((null? (cdr es)) (c-exp (car es) e depth c tail))
          (else (begin (c-exp (car es) e depth c #f) (c-op c routine-drop) (c-begin (cdr es) e depth c tail))))))

(define c-fields (subr compiles ((listof (productof (1 symbol) (2 exp)) @a) cenv int code) int)
  (lambda (fs e depth c)
    (if (null? fs) 0 (begin (c-exp (extract (car fs) 2) e depth c #f) (+ 1 (c-fields (cdr fs) e (+ depth 1) c))))))

(define c-count-let (subr (read @a) ((listof (productof (1 symbol) (2 exp)) @a)) int)
  (lambda (bs) (if (null? bs) 0 (+ 1 (c-count-let (cdr bs))))))

;; Each value pushed, in the scope outside; the names are the slots.
(define c-let-bind (subr compiles ((listof (productof (1 symbol) (2 exp)) @a) cenv cenv int code) cenv)
  (lambda (bs outer inner depth c)
    (if (null? bs)
        inner
        (begin (c-exp (extract (car bs) 2) outer depth c #f)
               (c-let-bind (cdr bs) outer (the cenv (cons (cons (extract (car bs) 1) (at-slot depth)) inner)) (+ depth 1) c)))))

;; `letrec`: a box per name first, so each closure can carry the box before
;; it has its value; then each value into its box.
(define c-letrec (subr compiles ((listof (productof (1 symbol) (2 syn) (3 exp)) @a) exp cenv int code bool) unit)
  (lambda (bs body e depth c tail)
    (letrec ((boxes (subr compiles ((listof (productof (1 symbol) (2 syn) (3 exp)) @a) cenv int) cenv)
               (lambda (bs inner d)
                 (if (null? bs)
                     inner
                     (begin (c-lit c (wcell-unit)) (c-prim c "%make-box" 1)
                            (boxes (cdr bs) (the cenv (cons (cons (extract (car bs) 1) (boxed-slot d)) inner)) (+ d 1))))))
             (fill (subr compiles ((listof (productof (1 symbol) (2 syn) (3 exp)) @a) cenv int int) unit)
               (lambda (bs inner d n)
                 (if (null? bs)
                     #u
                     (begin (c-op1 c routine-slot (wcell-int d))
                            (c-exp (extract (car bs) 3) inner (+ depth (+ n 1)) c #f)
                            (c-op c routine-swap) (c-int c 2) (c-op c routine-field-set)
                            (fill (cdr bs) inner (+ d 1) n))))))
      (let* ((inner (boxes bs e depth)) (n (c-count-letrec bs)))
        (begin (fill bs inner depth n)
               (c-exp body inner (+ depth n) c tail)
               (c-unbind c depth n tail))))))

(define c-count-letrec (subr (read @a) ((listof (productof (1 symbol) (2 syn) (3 exp)) @a)) int)
  (lambda (bs) (if (null? bs) 0 (+ 1 (c-count-letrec (cdr bs))))))

;; A lambda: its free values pushed, then its word closed over them.
(define c-lambda (subr compiles ((listof (productof (1 symbol) (2 syns-a)) @a) exp cenv int code) unit)
  (lambda (ps body e depth c)
    (let* ((fv (c-captured (c-free body (c-bind-params ps nil) nil) e))
           (inner (c-inner-env fv e (c-param-env ps 0 nil) 0))
           (n (c-count-params ps))
           (body-code (the code (new nil))))
      (begin
        (c-push-all fv e depth c)
        (c-exp body inner n body-code #t)
        (c-op1 c routine-closure (wcell-word (c-assemble body-code (string->symbol "lambda"))))
        (c-emit c (i-cell (wcell-int (c-length fv))))))))

(define c-count-params (subr (read @a) ((listof (productof (1 symbol) (2 syns-a)) @a)) int)
  (lambda (ps) (if (null? ps) 0 (+ 1 (c-count-params (cdr ps))))))
(define c-param-env (subr (maxeff (read @a) (alloc @k)) ((listof (productof (1 symbol) (2 syns-a)) @a) int cenv) cenv)
  (lambda (ps i acc) (if (null? ps) acc (c-param-env (cdr ps) (+ i 1) (the cenv (cons (cons (extract (car ps) 1) (at-slot i)) acc))))))
(define c-length (subr (read @k) (syms) int)
  (lambda (xs) (if (null? xs) 0 (+ 1 (c-length (cdr xs))))))

;; The free names that are locals here, not globals or standard names.
(define c-captured (subr (maxeff (read @k) (alloc @k)) (syms cenv) syms)
  (lambda (xs e)
    (cond ((null? xs) nil)
          ((null? (c-find e (car xs))) (c-captured (cdr xs) e))
          (else (cons (car xs) (c-captured (cdr xs) e))))))

;; Free value `i` for each captured name, boxed if it was boxed outside.
(define c-inner-env (subr (maxeff (read @k) (alloc @k)) (syms cenv cenv int) cenv)
  (lambda (xs outer acc i)
    (if (null? xs)
        acc
        (let ((l (car (c-find outer (car xs)))))
          (c-inner-env (cdr xs) outer
                       (the cenv (cons (cons (car xs) (tagcase l (boxed-slot (j) (boxed-free i)) (boxed-free (j) (boxed-free i)) (else y (at-free i)))) acc))
                       (+ i 1))))))

;; Each captured name's value, or its box, as the closure will hold it.
(define c-push-all (subr compiles (syms cenv int code) unit)
  (lambda (xs e depth c)
    (if (null? xs)
        #u
        (let ((l (car (c-find e (car xs)))))
          (begin
            (tagcase l
              (at-slot (i) (c-op1 c routine-slot (wcell-int i)))
              (at-free (i) (c-op1 c routine-free (wcell-int i)))
              (boxed-slot (i) (c-op1 c routine-slot (wcell-int i)))
              (boxed-free (i) (c-op1 c routine-free (wcell-int i)))
              (at-global (g) (c-fail "a global is not captured")))
            (c-push-all (cdr xs) e (+ depth 1) c))))))

;;; ------------------------------------------------------------ applications

(define c-app (subr compiles (exp (listof exp @a) cenv int code bool) unit)
  (lambda (f args e depth c tail)
    (let ((standard (tagcase f (e-var (n a b) (if (null? (c-where e n)) (symbol->string n) "") ) (else y ""))))
      (if (string=? standard "")
          (let ((n (c-exps args e depth c)))
            (begin (c-exp f e (+ depth n) c #f)
                   (if tail
                       (c-op1 c routine-tailcall (wcell-int n))
                       (c-op1 c routine-call (wcell-int n)))))
          (if (and tail (string=? standard "with-mark"))
              ;; In tail position, the mark replaces this frame's: a loop
              ;; that marks each iteration runs in constant space.
              (begin (c-exps args e depth c) (c-op c routine-withmark-tail))
              (begin (c-standard standard args e depth c) (c-done c tail)))))))

;; How many arguments a standard operation takes, or -1 if it is not one.
(define c-arity (subr pure (string) int)
  (lambda (n)
    (cond ((or (string=? n "make-continuation-prompt-tag") (string=? n "make-continuation-mark-key")) 0)
          ((or (string=? n "car") (string=? n "cdr") (string=? n "null?") (string=? n "not") (string=? n "new")
               (string=? n "get") (string=? n "char->integer") (string=? n "integer->char") (string=? n "string-length")
               (string=? n "symbol->string") (string=? n "string->symbol") (string=? n "char->string")
               (string=? n "array-length") (string=? n "current-marks") (string=? n "cwcc"))
           1)
          ((or (string=? n "with-mark") (string=? n "array-set!") (string=? n "substring")) 3)
          ((or (string=? n "+") (string=? n "-") (string=? n "*") (string=? n "<") (string=? n ">") (string=? n "<=")
               (string=? n ">=") (string=? n "=") (string=? n "modulo") (string=? n "quotient") (string=? n "cons")
               (string=? n "set-car!") (string=? n "set-cdr!") (string=? n "set") (string=? n "char=?")
               (string=? n "string-append") (string=? n "string=?") (string=? n "symbol=?") (string=? n "array-ref")
               (string=? n "string-ref") (string=? n "make-array") (string=? n "abort-current-continuation")
               (string=? n "call-with-composable-continuation") (string=? n "first-mark") (string=? n "marks-of"))
           2)
          (else -1))))

;; A standard operation as a value: a closure of its arity whose body
;; applies it to its parameters.
(define c-standard-value (subr compiles (string code) unit)
  (lambda (name c)
    (let ((n (c-arity name)) (body (the code (new nil))))
      (if (< n 0)
          (c-fail (string-append "not yet compiled as a value: " name))
          (begin
            (letrec ((params (subr (maxeff (read @k) (write @k) (alloc @k)) (int) unit)
                       (lambda (i) (if (= i n) #u (begin (c-op1 body routine-slot (wcell-int i)) (params (+ i 1)))))))
              (if (string=? name "make-array")
                  (begin (c-int body 0) (params 0) (c-prim body "%make-bloblet-filled" 3))
                  (begin (params 0) (c-standard-on name n body))))
            (c-op body routine-return)
            (c-op1 c routine-closure (wcell-word (c-assemble body (string->symbol name))))
            (c-emit c (i-cell (wcell-int 0))))))))

;; A standard operation, open-coded: a routine, or a runtime primitive, with
;; FX-26's conventions made plain (mutators give unit; arrays skip the
;; trailer's field).
(define c-standard (subr compiles (string (listof exp @a) cenv int code) unit)
  (lambda (name args e depth c)
    (if (string=? name "make-array")
        ;; (%make-bloblet-filled 0 n fill): the 0 first, under the others.
        (begin (c-int c 0) (c-exps args e (+ depth 1) c) (c-prim c "%make-bloblet-filled" 3))
        (c-standard-on name (c-exps args e depth c) c))))

(define c-standard-on (subr compiles (string int code) unit)
  (lambda (name n c)
      (cond ((string=? name "+") (c-op c routine-add))
            ((string=? name "-") (c-op c routine-sub))
            ((string=? name "<") (c-op c routine-less))
            ((string=? name ">") (begin (c-op c routine-swap) (c-op c routine-less)))
            ((string=? name "<=") (begin (c-op c routine-swap) (c-op c routine-less) (c-lit c (wcell-bool #f)) (c-op c routine-eq)))
            ((string=? name ">=") (begin (c-op c routine-less) (c-lit c (wcell-bool #f)) (c-op c routine-eq)))
            ;; Characters are immediates, so compared as symbols are.
            ((or (string=? name "=") (string=? name "symbol=?") (string=? name "char=?")) (c-op c routine-eq))
            ((string=? name "cons") (c-op c routine-cons))
            ((string=? name "car") (c-op c routine-car))
            ((string=? name "cdr") (c-op c routine-cdr))
            ((or (string=? name "set-car!") (string=? name "set-cdr!")) (begin (c-prim c name 2) (c-unit-after c)))
            ((string=? name "new") (c-prim c "%make-box" 1))
            ;; A reference is a box: its value is field 2.
            ((string=? name "get") (begin (c-int c 2) (c-op c routine-field-ref)))
            ((string=? name "set")
             (begin (c-op c routine-swap) (c-int c 2) (c-op c routine-field-set) (c-lit c (wcell-unit))))
            ((string=? name "null?") (begin (c-lit c (wcell-nil)) (c-op c routine-eq)))
            ((string=? name "not") (begin (c-lit c (wcell-bool #f)) (c-op c routine-eq)))
            ((string=? name "char->string") (c-prim c "string" 1))
            ;; A tag or a key: a fresh object, compared by identity.
            ((or (string=? name "make-continuation-prompt-tag") (string=? name "make-continuation-mark-key"))
             (begin (c-lit c (wcell-unit)) (c-prim c "%make-box" 1)))
            ((string=? name "abort-current-continuation") (c-op c routine-abort))
            ((string=? name "call-with-composable-continuation") (c-op c routine-callcomp))
            ((string=? name "cwcc") (c-op c routine-callcc))
            ((string=? name "with-mark") (c-op c routine-withmark))
            ((string=? name "first-mark") (c-op c routine-firstmark))
            ((string=? name "current-marks") (c-op c routine-currentmarks))
            ((string=? name "marks-of") (c-op c routine-marksof))
            ((string=? name "array-ref") (begin (c-int c 2) (c-op c routine-add) (c-op c routine-field-ref)))
            ((string=? name "array-set!")
             (begin (c-op c routine-swap) (c-int c 2) (c-op c routine-add) (c-op c routine-swap)
                    (c-prim c "%bloblet-set!" 3) (c-unit-after c)))
            ((string=? name "array-length") (begin (c-prim c "%bloblet-fields" 1) (c-int c 1) (c-op c routine-sub)))
            ((or (string=? name "*") (string=? name "modulo") (string=? name "quotient")
                 (string=? name "char->integer")
                 (string=? name "integer->char") (string=? name "string-append") (string=? name "string-length")
                 (string=? name "string-ref") (string=? name "substring") (string=? name "string=?")
                 (string=? name "string->symbol") (string=? name "symbol->string"))
             (c-prim c name n))
            ;; The rest, as the lowering runs them (`standard.fx`): a
            ;; runtime primitive, or nothing at all.
            (else
             (let ((p (standard-primitive name)))
               (cond ((string=? p "%fx26-identity") #u)
                     ((string=? p "") (c-fail (string-append "not yet compiled: " name)))
                     (else (c-prim c p n))))))))

(define c-bloblet (subr compiles (string int (listof exp @a) cenv int code) unit)
  (lambda (op i args e depth c)
    (cond ((string=? op "make-bloblet") (c-prim c "%make-bloblet" (c-exps args e depth c)))
          ((string=? op "bloblet-ref")
           (begin (c-exps args e depth c) (c-int c (+ i 2)) (c-op c routine-field-ref)))
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

(define c-tagcase
  (subr compiles (exp (listof (productof (1 symbol) (2 bool) (3 names) (4 exp)) @a) (listof (productof (1 symbol) (2 exp)) @a) cenv int code bool) unit)
  (lambda (s arms els e depth c tail)
    (let ((end (c-fresh)))
      (begin
        (c-exp s e depth c #f)
        (c-arms arms els e depth c tail end)
        (c-emit c (i-label end))))))

(define c-arms
  (subr compiles ((listof (productof (1 symbol) (2 bool) (3 names) (4 exp)) @a) (listof (productof (1 symbol) (2 exp)) @a) cenv int code bool int) unit)
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
            (c-int c 2)
            (c-op c routine-field-ref)
            (c-lit c (wcell-symbol (extract arm 1)))
            (c-op c routine-eq)
            (c-emit c (i-zbranch next))
            ;; The value, or its product's members, as slots after the sum.
            (c-op1 c routine-slot (wcell-int depth))
            (c-int c 3)
            (c-op c routine-field-ref)
            (let ((bound (if (extract arm 2)
                             (c-members (extract arm 3) e depth (+ depth 2) 0 c)
                             (the cenv (cons (cons (car (extract arm 3)) (at-slot (+ depth 1))) e))))
                  (n (if (extract arm 2) (+ 1 (c-count-names (extract arm 3))) 1)))
              (begin
                (c-exp (extract arm 4) bound (+ depth (+ 1 n)) c tail)
                (c-unbind c depth (+ n 1) tail)
                (if tail #u (c-emit c (i-branch end)))))
            (c-emit c (i-label next))
            (c-arms (cdr arms) els e depth c tail end))))))

(define c-count-names (subr (read @a) (names) int)
  (lambda (ns) (if (null? ns) 0 (+ 1 (c-count-names (cdr ns))))))

;; A product's members, from the slot after the sum's, each a slot.
(define c-members (subr compiles (names cenv int int int code) cenv)
  (lambda (ns e sum-slot slot j c)
    (if (null? ns)
        e
        (begin (c-op1 c routine-slot (wcell-int (+ sum-slot 1)))
               (c-int c (+ j 2))
               (c-op c routine-field-ref)
               (c-members (cdr ns) (the cenv (cons (cons (car ns) (at-slot slot)) e)) sum-slot (+ slot 1) (+ j 1) c)))))

;;; ------------------------------------------------------------- programs

(define c-push-global (subr (maxeff (read @k) (write @k) (alloc @k)) (symbol) wglobal)
  (lambda (n) (let ((g (make-global n))) (begin (set c-genv (the cenv (cons (cons n (at-global g)) (get c-genv)))) g))))

(define c-without (subr (maxeff (read @k) (alloc @k)) (syms symbol) syms)
  (lambda (ns n) (cond ((null? ns) nil) ((symbol=? (car ns) n) (cdr ns)) (else (cons (car ns) (c-without (cdr ns) n))))))

(define c-global-of (subr compiles (symbol) wglobal)
  (lambda (n)
    (let ((l (c-find (get c-genv) n)))
      (if (null? l)
          (c-fail "no such global")
          (tagcase (car l) (at-global (g) g) (else y (c-fail "not a global")))))))

(define c-declare-ahead (subr (maxeff (read @a) (read @k) (write @k) (alloc @k)) ((listof top @a)) unit)
  (lambda (ts)
    (if (null? ts)
        #u
        (begin
          (tagcase (car ts)
            (t-define (n ty x a b)
              (if (and (not (null? ty)) (null? (c-find (get c-genv) n)))
                  (begin (c-push-global n) (set c-declared (cons n (get c-declared))))
                  #u))
            (else y #u))
          (c-declare-ahead (cdr ts))))))

;; Each form in turn; the last expression's value is left on the stack.
(define c-tops (subr compiles ((listof top @a) code bool) bool)
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
                  (let ((g (if (c-member? (get c-declared) n)
                               (begin (set c-declared (c-without (get c-declared) n)) (c-global-of n))
                               (c-push-global n))))
                    (begin (c-exp x (the cenv nil) 0 c #f)
                           (c-op1 c routine-global! (wcell-global g)))))
              (c-tops (cdr ts) c #f)))
          (t-exp (x)
            (begin (if has-value (c-op c routine-drop) #u)
                   (c-exp x (the cenv nil) 0 c #f)
                   (c-tops (cdr ts) c #t)))
          (else y (c-tops (cdr ts) c has-value))))))

;; The entry point: a program's trees to one word that runs it and leaves
;; the value of its last expression (unit, if it has none).
;; The entry point: a checked program's trees, and what checking found.
(define compile-program (subr (maxeff compiles (comefrom @y)) ((listof top @a) k-facts) cresult)
  (lambda (tops facts)
    (prompt c-tag
      (let ((c (the code (new nil))))
        (begin
          (set c-facts facts)
          (c-declare-ahead tops)
          (if (c-tops tops c #f) #u (c-lit c (wcell-unit)))
          (c-op c routine-exit)
          (c-ok (c-assemble c (string->symbol "program")))))
      (lambda (r) r))))
