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
;;; definitions made before it, a second `define` shadows the first, a
;;; lambda's definition sees itself, and a `define-rec` group sees all of
;;; itself.
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
;; Field `k` of a bloblet whose type says it has one.
(define c-field (subr (maxeff (read @k) (write @k) (alloc @k)) (code int) unit)
  (lambda (c k) (c-op1 c routine-field (wcell-int k))))

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
  ;; A `letrec` sibling not made yet, to be in this slot: a closure that
  ;; captures it holds a placeholder, patched once every sibling is made.
  (at-pending int)
  ;; A `letrec`-bound procedure, in its own body, where it is only called
  ;; in tail position: each call is a jump back to its start. (The int is
  ;; unused.)
  (at-loop int))
(define-type cenv (listof (pairof symbol loc @k) @k))

(define c-loop? (subr pure (loc) bool)
  (lambda (l) (tagcase l (at-loop (z) #t) (else y #f))))

;; The word being compiled, when it is a `letrec`-bound procedure's: a tail
;; call of `c-this-name`, still bound at `c-this-loc`, is a loop (13e).
;; `c-this-params` is -1 when the word is no such procedure's.
(define c-this-name (ref symbol @k) (new 'none))
(define c-this-loc (ref loc @k) (new (at-loop 0)))
(define c-this-params (ref int @k) (new -1))
(define c-this-start (ref int @k) (new 0))

;; Whether `l` is where the procedure being compiled is bound: its loop, or
;; the free value holding its closure.
(define c-this-loc? (subr pure (loc loc) bool)
  (lambda (l this)
    (tagcase this
      (at-loop (z) (c-loop? l))
      (at-free (i) (tagcase l (at-free (j) (= i j)) (else y #f)))
      (else y #f))))

;; The global environment as compiling has reached it, newest first.
(define c-genv (ref cenv @k) (new nil))

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
      (at-pending (i) (c-fail "a letrec sibling not made yet is only captured"))
      (at-loop (z) (c-fail "a loop is only ever called, in tail position")))))

;;; ------------------------------------------------------------- free names
;;; The names a lambda's body uses that it does not bind: what its closure
;;; must carry, once globals and standard names are set aside.

(define-type syms (listof symbol @k))

(define c-member? (subr (read @k) (syms symbol) bool)
  (lambda (xs n) (and (not (null? xs)) (or (symbol=? (car xs) n) (c-member? (cdr xs) n)))))
(define c-adjoin (subr (maxeff (read @k) (alloc @k)) (syms symbol) syms)
  (lambda (xs n) (if (c-member? xs n) xs (cons n xs))))

(define c-bind-params (subr (maxeff (read @a) (read @k) (alloc @k)) ((listof (productof (1 symbol) (2 syns-a)) @a) syms) syms)
  (lambda (ps bound) (if (null? ps) bound (c-bind-params (cdr ps) (cons (extract (car ps) 1) bound)))))
(define c-bind-letrec (subr (maxeff (read @a) (read @k) (alloc @k)) ((listof (productof (1 symbol) (2 syn) (3 exp)) @a) syms) syms)
  (lambda (bs bound) (if (null? bs) bound (c-bind-letrec (cdr bs) (cons (extract (car bs) 1) bound)))))
(define c-bind-let (subr (maxeff (read @a) (read @k) (alloc @k)) ((listof (productof (1 symbol) (2 exp)) @a) syms) syms)
  (lambda (bs bound) (if (null? bs) bound (c-bind-let (cdr bs) (cons (extract (car bs) 1) bound)))))
(define c-names (subr (maxeff (read @a) (read @k) (alloc @k)) (names syms) syms)
  (lambda (ns bound) (if (null? ns) bound (c-names (cdr ns) (cons (car ns) bound)))))

(define-rec
  (c-free-all (subr (maxeff (read @a) (read @k) (alloc @k)) ((listof exp @a) syms syms) syms)
    (lambda (es bound acc) (if (null? es) acc (c-free-all (cdr es) bound (c-free (car es) bound acc)))))
  (c-free (subr (maxeff (read @a) (read @k) (alloc @k)) (exp syms syms) syms)
    (lambda (x bound acc)
      (tagcase x
        (e-var (n a b) (if (c-member? bound n) acc (c-adjoin acc n)))
        (e-lambda (ps body a b) (c-free body (c-bind-params ps bound) acc))
        (e-app (f args a b) (c-free f bound (c-free-all args bound acc)))
        (e-plambda (d body a b) (c-free body bound acc))
        (e-letregion (k r body a b) (c-free body (cons r bound) acc))
        (e-rlambda (r l a b) (c-free r bound (c-free l bound acc)))
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
  (c-free-letrec (subr (maxeff (read @a) (read @k) (alloc @k)) ((listof (productof (1 symbol) (2 syn) (3 exp)) @a) syms syms) syms)
    (lambda (bs bound acc) (if (null? bs) acc (c-free-letrec (cdr bs) bound (c-free (extract (car bs) 3) bound acc)))))
  (c-free-let (subr (maxeff (read @a) (read @k) (alloc @k)) ((listof (productof (1 symbol) (2 exp)) @a) syms syms) syms)
    (lambda (bs bound acc) (if (null? bs) acc (c-free-let (cdr bs) bound (c-free (extract (car bs) 2) bound acc)))))
  (c-free-fields (subr (maxeff (read @a) (read @k) (alloc @k)) ((listof (productof (1 symbol) (2 exp)) @a) syms syms) syms)
    (lambda (fs bound acc) (if (null? fs) acc (c-free-fields (cdr fs) bound (c-free (extract (car fs) 2) bound acc)))))
  (c-free-arms
    (subr (maxeff (read @a) (read @k) (alloc @k)) ((listof (productof (1 symbol) (2 bool) (3 names) (4 exp)) @a) syms syms) syms)
    (lambda (arms bound acc)
      (if (null? arms)
          acc
          (c-free-arms (cdr arms) bound (c-free (extract (car arms) 4) (c-names (extract (car arms) 3) bound) acc)))))
  (c-free-else (subr (maxeff (read @a) (read @k) (alloc @k)) ((listof (productof (1 symbol) (2 exp)) @a) syms syms) syms)
    (lambda (els bound acc)
      (if (null? els) acc (c-free (extract (car els) 2) (cons (extract (car els) 1) bound) acc)))))

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

(define c-count-let (subr (read @a) ((listof (productof (1 symbol) (2 exp)) @a)) int)
  (lambda (bs) (if (null? bs) 0 (+ 1 (c-count-let (cdr bs))))))

;; `letrec`: every binding is a lambda (the checker says so). Each closure
;; is made in its slot, with a placeholder for a sibling not made yet; then
;; each placeholder is patched with its sibling. Nothing runs in between, so
;; no one sees the knot tied. A name used only in calls of itself that are
;; loops is not captured at all.
(define-type patches (listof (pairof int int @k) @k))

(define c-letrec-slots (subr (maxeff (read @a) (alloc @k)) ((listof (productof (1 symbol) (2 syn) (3 exp)) @a) cenv int) cenv)
  (lambda (bs e d)
    (if (null? bs) e (c-letrec-slots (cdr bs) (the cenv (cons (cons (extract (car bs) 1) (at-slot d)) e)) (+ d 1)))))
(define c-patch-one (subr compiles (patches int int code) unit)
  (lambda (ps depth i c)
    (if (null? ps)
        #u
        (begin (c-op1 c routine-slot (wcell-int (cdr (car ps))))
               (c-op1 c routine-slot (wcell-int (+ depth i)))
               (c-int c (+ threaded-closure-free0 (car (car ps))))
               (c-op c routine-field-set)
               (c-patch-one (cdr ps) depth i c)))))

;; Each placeholder of closure `i` patched with its sibling.
(define c-letrec-patch (subr compiles ((listof patches @k) int int code) unit)
  (lambda (made depth i c)
    (if (null? made)
        #u
        (begin (c-patch-one (car made) depth i c) (c-letrec-patch (cdr made) depth (+ i 1) c)))))

;;; ------------------------------------------------------- known procedures

;; `x`, when it is a lambda under any type abstractions and ascriptions,
;; which compile to nothing; none otherwise.
(define c-lambda-of (subr (maxeff (read @a) (alloc @k)) (exp) (listof exp @k))
  (lambda (x)
    (tagcase x
      (e-plambda (d body a b) (c-lambda-of body))
      (e-the (d body a b) (c-lambda-of body))
      (e-lambda (ps body a b) (the (listof exp @k) (cons x nil)))
      (e-rlambda (r l a b) (the (listof exp @k) (cons x nil)))
      (else y nil))))

(define c-mentions? (subr (maxeff (read @a) (read @k) (alloc @k)) (exp symbol) bool)
  (lambda (x n) (c-member? (c-free x nil nil) n)))
(define c-count-exps (subr (read @a) ((listof exp @a)) int)
  (lambda (es) (if (null? es) 0 (+ 1 (c-count-exps (cdr es))))))

;; Whether every use of `f` in `x` is a call with `n` arguments in tail
;; position, which the compiler makes a loop.

(define-rec
  (c-loops-only (subr (maxeff (read @a) (read @k) (alloc @k)) (exp symbol int bool) bool)
    (lambda (x f n tail)
      (tagcase x
        (e-var (m a b) (not (symbol=? m f)))
        (e-lambda (ps body a b) (or (c-member? (c-bind-params ps nil) f) (not (c-mentions? body f))))
        (e-app (fun args a b)
          (and (c-loops-only-all args f n)
               (tagcase fun
                 (e-var (m a2 b2) (if (symbol=? m f) (and tail (= (c-count-exps args) n)) #t))
                 (else y (c-loops-only fun f n #f)))))
        (e-plambda (d body a b) (c-loops-only body f n tail))
        (e-letregion (k r body a b) (or (symbol=? r f) (c-loops-only body f n #f)))
        (e-rlambda (r l a b) (and (c-loops-only r f n #f) (c-loops-only l f n #f)))
        (e-proj (body ds a b) (c-loops-only body f n tail))
        (e-the (d body a b) (c-loops-only body f n tail))
        (e-if (t th el a b)
          (and (c-loops-only t f n #f) (and (c-loops-only th f n tail) (c-loops-only el f n tail))))
        (e-letrec (bs body a b)
          (or (c-member? (c-bind-letrec bs nil) f)
              (and (c-loops-only-letrec bs f n) (c-loops-only body f n tail))))
        (e-let (bs body a b)
          (and (c-loops-only-let bs f n)
               (or (c-member? (c-bind-let bs nil) f) (c-loops-only body f n tail))))
        (e-begin (es a b) (c-loops-only-begin es f n tail))
        (e-prompt (t body h a b)
          (and (c-loops-only t f n #f) (and (c-loops-only h f n #f) (not (c-mentions? body f)))))
        (e-bloblet (op i args a b) (c-loops-only-all args f n))
        (e-product (fs a b) (c-loops-only-fields fs f n))
        (e-extract (p l a b) (c-loops-only p f n #f))
        (e-sum (t v a b) (c-loops-only v f n #f))
        (e-tagcase (s arms els a b)
          (and (c-loops-only s f n #f) (and (c-loops-only-arms arms f n tail) (c-loops-only-else els f n tail))))
        (else y #t))))
  (c-loops-only-all (subr (maxeff (read @a) (read @k) (alloc @k)) ((listof exp @a) symbol int) bool)
    (lambda (es f n) (or (null? es) (and (c-loops-only (car es) f n #f) (c-loops-only-all (cdr es) f n)))))
  (c-loops-only-begin (subr (maxeff (read @a) (read @k) (alloc @k)) ((listof exp @a) symbol int bool) bool)
    (lambda (es f n tail)
      (cond ((null? es) #t)
            ((null? (cdr es)) (c-loops-only (car es) f n tail))
            (else (and (c-loops-only (car es) f n #f) (c-loops-only-begin (cdr es) f n tail))))))
  (c-loops-only-letrec (subr (maxeff (read @a) (read @k) (alloc @k)) ((listof (productof (1 symbol) (2 syn) (3 exp)) @a) symbol int) bool)
    (lambda (bs f n) (or (null? bs) (and (c-loops-only (extract (car bs) 3) f n #f) (c-loops-only-letrec (cdr bs) f n)))))
  (c-loops-only-let (subr (maxeff (read @a) (read @k) (alloc @k)) ((listof (productof (1 symbol) (2 exp)) @a) symbol int) bool)
    (lambda (bs f n) (or (null? bs) (and (c-loops-only (extract (car bs) 2) f n #f) (c-loops-only-let (cdr bs) f n)))))
  (c-loops-only-fields (subr (maxeff (read @a) (read @k) (alloc @k)) ((listof (productof (1 symbol) (2 exp)) @a) symbol int) bool)
    (lambda (fs f n) (or (null? fs) (and (c-loops-only (extract (car fs) 2) f n #f) (c-loops-only-fields (cdr fs) f n)))))
  (c-loops-only-arms
    (subr (maxeff (read @a) (read @k) (alloc @k)) ((listof (productof (1 symbol) (2 bool) (3 names) (4 exp)) @a) symbol int bool) bool)
    (lambda (arms f n tail)
      (or (null? arms)
          (and (or (c-member? (c-names (extract (car arms) 3) nil) f) (c-loops-only (extract (car arms) 4) f n tail))
               (c-loops-only-arms (cdr arms) f n tail)))))
  (c-loops-only-else (subr (maxeff (read @a) (read @k) (alloc @k)) ((listof (productof (1 symbol) (2 exp)) @a) symbol int bool) bool)
    (lambda (els f n tail)
      (or (null? els) (or (symbol=? (extract (car els) 1) f) (c-loops-only (extract (car els) 2) f n tail))))))

;; Binding `i`'s scope while it is made: each sibling pending, and itself a
;; loop if it only calls itself in loops.
(define c-letrec-own
  (subr (maxeff (read @a) (read @k) (alloc @k)) ((listof (productof (1 symbol) (2 syn) (3 exp)) @a) cenv int int int exp int) cenv)
  (lambda (bs e depth k i body nps)
    (if (null? bs)
        e
        (let ((g (extract (car bs) 1)))
          (c-letrec-own (cdr bs)
                        (the cenv (cons (cons g (if (and (= k i) (c-loops-only body g nps #t)) (at-loop 0) (at-pending (+ depth k)))) e))
                        depth (+ k 1) i body nps)))))

(define c-count-letrec (subr (read @a) ((listof (productof (1 symbol) (2 syn) (3 exp)) @a)) int)
  (lambda (bs) (if (null? bs) 0 (+ 1 (c-count-letrec (cdr bs))))))

(define c-count-params (subr (read @a) ((listof (productof (1 symbol) (2 syns-a)) @a)) int)
  (lambda (ps) (if (null? ps) 0 (+ 1 (c-count-params (cdr ps))))))
(define c-param-env (subr (maxeff (read @a) (alloc @k)) ((listof (productof (1 symbol) (2 syns-a)) @a) int cenv) cenv)
  (lambda (ps i acc) (if (null? ps) acc (c-param-env (cdr ps) (+ i 1) (the cenv (cons (cons (extract (car ps) 1) (at-slot i)) acc))))))
(define c-length (subr (read @k) (syms) int)
  (lambda (xs) (if (null? xs) 0 (+ 1 (c-length (cdr xs))))))

;; The free names that are locals here, not globals or standard names, nor
;; a loop, which is not a value.
(define c-captured (subr (maxeff (read @k) (alloc @k)) (syms cenv) syms)
  (lambda (xs e)
    (cond ((null? xs) nil)
          ((null? (c-find e (car xs))) (c-captured (cdr xs) e))
          ((c-loop? (car (c-find e (car xs)))) (c-captured (cdr xs) e))
          (else (cons (car xs) (c-captured (cdr xs) e))))))

;; Free value `i` for each captured name, boxed if it was boxed outside.
(define c-inner-env (subr (maxeff (read @k) (alloc @k)) (syms cenv cenv int) cenv)
  (lambda (xs outer acc i)
    (if (null? xs)
        acc
        (c-inner-env (cdr xs) outer
                       (the cenv (cons (cons (car xs) (at-free i)) acc))
                       (+ i 1)))))

;; Each captured name's value, as the closure will hold it, free value `j`
;; on; a sibling not made yet is a placeholder, and one of the patches.
(define c-push-all (subr compiles (syms cenv int int code) patches)
  (lambda (xs e depth j c)
    (if (null? xs)
        nil
        (let* ((l (car (c-find e (car xs))))
               (pending (tagcase l
                          (at-slot (i) (begin (c-op1 c routine-slot (wcell-int i)) -1))
                          (at-free (i) (begin (c-op1 c routine-free (wcell-int i)) -1))
                          (at-pending (s) (begin (c-lit c (wcell-bool #f)) s))
                          (at-global (g) (c-fail "a global is not captured"))
                          (at-loop (z) (c-fail "a loop is not captured"))))
               (rest (c-push-all (cdr xs) e (+ depth 1) (+ j 1) c)))
          (if (< pending 0) rest (the patches (cons (cons j pending) rest)))))))

(define c-self-call? (subr (maxeff (read @a) (read @k) (alloc @k)) (exp (listof exp @a) cenv bool) bool)
  (lambda (f args e tail)
    (and tail
         (and (>= (get c-this-params) 0)
              (tagcase f
                (e-var (n a b)
                  (and (symbol=? n (get c-this-name))
                       (let ((l (c-find e n)))
                         (and (not (null? l))
                              (and (c-this-loc? (car l) (get c-this-loc)) (= (c-count-exps args) (get c-this-params)))))))
                (else y #f))))))

(define c-loop-stores (subr (maxeff (read @k) (write @k) (alloc @k)) (code int) unit)
  (lambda (c i) (if (< i 0) #u (begin (c-op1 c routine-slot! (wcell-int i)) (c-loop-stores c (- i 1))))))
(define c-drops (subr (maxeff (read @k) (write @k) (alloc @k)) (code int) unit)
  (lambda (c k) (if (<= k 0) #u (begin (c-op c routine-drop) (c-drops c (- k 1))))))

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

(define c-standard-on (subr compiles (string int code) unit)
  (lambda (name n c)
      (cond ((string=? name "+") (c-op c routine-int-add))
            ((string=? name "-") (c-op c routine-int-sub))
            ((string=? name "<") (c-op c routine-int-less))
            ((string=? name ">") (begin (c-op c routine-swap) (c-op c routine-int-less)))
            ((string=? name "<=") (begin (c-op c routine-swap) (c-op c routine-int-less) (c-lit c (wcell-bool #f)) (c-op c routine-eq)))
            ((string=? name ">=") (begin (c-op c routine-int-less) (c-lit c (wcell-bool #f)) (c-op c routine-eq)))
            ;; Characters are immediates, so compared as symbols are.
            ((or (string=? name "=") (string=? name "symbol=?") (string=? name "char=?")) (c-op c routine-eq))
            ((string=? name "cons") (c-op c routine-cons))
            ((string=? name "car") (c-op c routine-pair-car))
            ((string=? name "cdr") (c-op c routine-pair-cdr))
            ((or (string=? name "set-car!") (string=? name "set-cdr!")) (begin (c-prim c name 2) (c-unit-after c)))
            ((string=? name "new") (c-prim c "%make-box" 1))
            ;; A reference is a box: its value is field 2.
            ((string=? name "get") (c-field c 2))
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
            ((string=? name "array-ref") (begin (c-int c 2) (c-op c routine-int-add) (c-op c routine-field-ref)))
            ((string=? name "array-set!")
             (begin (c-op c routine-swap) (c-int c 2) (c-op c routine-int-add) (c-op c routine-swap)
                    (c-prim c "%bloblet-set!" 3) (c-unit-after c)))
            ((string=? name "array-length") (begin (c-prim c "%bloblet-fields" 1) (c-int c 1) (c-op c routine-int-sub)))
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

(define c-count-names (subr (read @a) (names) int)
  (lambda (ns) (if (null? ns) 0 (+ 1 (c-count-names (cdr ns))))))

;; A product's members, from the slot after the sum's, each a slot.
(define c-members (subr compiles (names cenv int int int code) cenv)
  (lambda (ns e sum-slot slot j c)
    (if (null? ns)
        e
        (begin (c-op1 c routine-slot (wcell-int (+ sum-slot 1)))
               (c-field c (+ j 2))
               (c-members (cdr ns) (the cenv (cons (cons (car ns) (at-slot slot)) e)) sum-slot (+ slot 1) (+ j 1) c)))))

;;; ---------------------------------------------------------- expressions
;;; `depth` is how many values are on the frame above its start, so the next
;;; value pushed is slot `depth`. In tail position, code ends the word: with
;;; a `tailcall`, or with `return` after the value.

(define-rec
  (c-exps (subr compiles ((listof exp @a) cenv int code) int)
    (lambda (es e depth c)
      (if (null? es) 0 (begin (c-exp (car es) e depth c #f) (+ 1 (c-exps (cdr es) e (+ depth 1) c))))))
  (c-exp (subr compiles (exp cenv int code bool) unit)
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
        (e-app (f args a b) (c-app f args e depth c tail))
        (e-plambda (d body a b) (c-exp body e depth c tail))
        ;; The region's name bound in a slot, as a `let`'s, to a region
        ;; entered (an arena, or a reap), and left with the body's value,
        ;; which is so not in tail position.
        (e-letregion (k r body a b)
          (let ((inner (the cenv (cons (cons r (at-slot depth)) e))))
            (begin
              (c-prim c (if k "%region-enter" "%reap-enter") 0)
              (c-exp body inner (+ depth 1) c #f)
              (c-prim c "%region-exit" 2)
              (c-done c tail))))
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
            (c-lambda (the (listof (productof (1 symbol) (2 syns-a)) @a) nil) body e (+ depth 2) c nil nil)
            (c-op c routine-prompt)
            (c-done c tail)))
        (e-bloblet (op i args a b) (begin (c-bloblet (symbol->string op) i args e depth c) (c-done c tail)))
        (e-product (fs a b)
          (begin (c-int c 37) (c-prim c "%make-frozen" (+ 1 (c-fields fs e (+ depth 1) c))) (c-done c tail)))
        (e-extract (p l a b)
          (let ((i (c-field-index (get c-facts) a b)))
            (if (< i 0)
                (c-fail "an extract the checker did not see")
                (begin (c-exp p e depth c #f) (c-field c (+ i 2)) (c-done c tail)))))
        (e-sum (t v a b)
          (begin (c-int c 36) (c-lit c (wcell-symbol t)) (c-exp v e (+ depth 2) c #f)
                 (c-prim c "%make-frozen" 3) (c-done c tail)))
        (e-tagcase (s arms els a b) (c-tagcase s arms els e depth c tail)))))
  (c-begin (subr compiles ((listof exp @a) cenv int code bool) unit)
    (lambda (es e depth c tail)
      (cond ((null? es) (begin (c-lit c (wcell-unit)) (c-done c tail)))
            ((null? (cdr es)) (c-exp (car es) e depth c tail))
            (else (begin (c-exp (car es) e depth c #f) (c-op c routine-drop) (c-begin (cdr es) e depth c tail))))))
  (c-fields (subr compiles ((listof (productof (1 symbol) (2 exp)) @a) cenv int code) int)
    (lambda (fs e depth c)
      (if (null? fs) 0 (begin (c-exp (extract (car fs) 2) e depth c #f) (+ 1 (c-fields (cdr fs) e (+ depth 1) c))))))
  ;; Each value pushed, in the scope outside; the names are the slots.
  (c-let-bind (subr compiles ((listof (productof (1 symbol) (2 exp)) @a) cenv cenv int code) cenv)
    (lambda (bs outer inner depth c)
      (if (null? bs)
          inner
          (begin (c-exp (extract (car bs) 2) outer depth c #f)
                 (c-let-bind (cdr bs) outer (the cenv (cons (cons (extract (car bs) 1) (at-slot depth)) inner)) (+ depth 1) c)))))
  (c-letrec (subr compiles ((listof (productof (1 symbol) (2 syn) (3 exp)) @a) exp cenv int code bool) unit)
    (lambda (bs body e depth c tail)
      (let* ((made (c-letrec-make bs bs e depth 0 c)) (n (c-count-letrec bs)))
        (begin
          (c-letrec-patch made depth 0 c)
          (c-exp body (c-letrec-slots bs e depth) (+ depth n) c tail)
          (c-unbind c depth n tail)))))
  ;; Each closure made, in order; what each must have patched.
  (c-letrec-make
    (subr compiles ((listof (productof (1 symbol) (2 syn) (3 exp)) @a) (listof (productof (1 symbol) (2 syn) (3 exp)) @a) cenv int int code)
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
  (c-lambda (subr compiles ((listof (productof (1 symbol) (2 syns-a)) @a) exp cenv int code syms (listof exp @k)) patches)
    (lambda (ps body e depth c own0 region)
      (let* ((fv (c-captured (c-free body (c-bind-params ps nil) nil) e))
             ;; A parameter of the same name hides the procedure.
             (own (if (or (null? own0) (c-member? (c-bind-params ps nil) (car own0))) (the syms nil) own0))
             (base (if (or (null? own) (c-member? fv (car own))) (the cenv nil) (the cenv (cons (cons (car own) (at-loop 0)) nil))))
             (inner (c-inner-env fv e (c-param-env ps 0 base) 0))
             (n (c-count-params ps))
             (body-code (the code (new nil)))
             (outer-name (get c-this-name)) (outer-loc (get c-this-loc))
             (outer-params (get c-this-params)) (outer-start (get c-this-start)))
        (let ((patches (begin (if (null? region) #u (c-exp (car region) e depth c #f)) (c-push-all fv e depth 0 c))))
         (begin
          (if (null? own)
              (set c-this-params -1)
              (let ((start (c-fresh)))
                (begin (set c-this-name (car own)) (set c-this-loc (car (c-find inner (car own))))
                       (set c-this-params n) (set c-this-start start)
                       (c-emit body-code (i-label start)))))
          (c-exp body inner n body-code #t)
          (set c-this-name outer-name) (set c-this-loc outer-loc)
          (set c-this-params outer-params) (set c-this-start outer-start)
          ;; Named for where its body starts, so that a profile can say which.
          (let ((w (wcell-word (c-assemble body-code (string->symbol (string-append "lambda@" (int->string (exp-start body))))))))
            (if (null? region)
                (begin (c-op1 c routine-closure w) (c-emit c (i-cell (wcell-int (c-length fv)))))
                (begin (c-lit c w) (c-prim c "%region-closure" (+ 2 (c-length fv))))))
          patches)))))
  ;;; ------------------------------------------------------------ applications
  (c-app (subr compiles (exp (listof exp @a) cenv int code bool) unit)
    (lambda (f args e depth c tail)
      (if (c-self-call? f args e tail)
          ;; A loop: the arguments into the parameters' slots, the rest of
          ;; the frame dropped, and back to the start.
          (begin (c-exps args e depth c)
                 (c-loop-stores c (- (get c-this-params) 1))
                 (c-drops c (- depth (get c-this-params)))
                 (c-emit c (i-branch (get c-this-start))))
          (c-app-other f args e depth c tail))))
  (c-app-other (subr compiles (exp (listof exp @a) cenv int code bool) unit)
    (lambda (f args e depth c tail)
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
                (begin (c-standard standard args e depth c) (c-done c tail)))))))
  ;; A standard operation, open-coded: a routine, or a runtime primitive, with
  ;; FX-26's conventions made plain (mutators give unit; arrays skip the
  ;; trailer's field).
  (c-standard (subr compiles (string (listof exp @a) cenv int code) unit)
    (lambda (name args e depth c)
      (if (string=? name "make-array")
          ;; (%make-bloblet-filled 0 n fill): the 0 first, under the others.
          (begin (c-int c 0) (c-exps args e (+ depth 1) c) (c-prim c "%make-bloblet-filled" 3))
          (c-standard-on name (c-exps args e depth c) c))))
  (c-bloblet (subr compiles (string int (listof exp @a) cenv int code) unit)
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
    (subr compiles (exp (listof (productof (1 symbol) (2 bool) (3 names) (4 exp)) @a) (listof (productof (1 symbol) (2 exp)) @a) cenv int code bool) unit)
    (lambda (s arms els e depth c tail)
      (let ((end (c-fresh)))
        (begin
          (c-exp s e depth c #f)
          (c-arms arms els e depth c tail end)
          (c-emit c (i-label end))))))
  (c-arms
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

(define c-push-global (subr (maxeff (read @k) (write @k) (alloc @k)) (symbol) wglobal)
  (lambda (n) (let ((g (make-global n))) (begin (set c-genv (the cenv (cons (cons n (at-global g)) (get c-genv)))) g))))




(define c-rec-globals (subr (maxeff (read @a) (read @k) (write @k) (alloc @k)) ((listof (productof (1 symbol) (2 syn) (3 exp)) @a)) (listof wglobal @k))
  (lambda (bs) (if (null? bs) nil (let ((g (c-push-global (extract (car bs) 1)))) (cons g (c-rec-globals (cdr bs)))))))
(define c-rec-fill (subr compiles ((listof (productof (1 symbol) (2 syn) (3 exp)) @a) (listof wglobal @k) code) unit)
  (lambda (bs gs c)
    (if (null? bs)
        #u
        (begin (c-exp (extract (car bs) 3) (the cenv nil) 0 c #f)
               (c-op1 c routine-global! (wcell-global (car gs)))
               (c-rec-fill (cdr bs) (cdr gs) c)))))

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
                  (if (null? (c-lambda-of x))
                      (begin (c-exp x (the cenv nil) 0 c #f)
                             (c-op1 c routine-global! (wcell-global (c-push-global n))))
                      ;; A lambda: its global first, so that it can call itself.
                      (let ((g (c-push-global n)))
                        (begin (c-exp x (the cenv nil) 0 c #f)
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
          (set c-this-params -1)
          (if (c-tops tops c #f) #u (c-lit c (wcell-unit)))
          (c-op c routine-exit)
          (c-ok (c-assemble c (string->symbol "program")))))
      (lambda (r) r))))
