;;; The compiler from FX-26 to cellular words, in FX-26 (PLAN.md §11, 9d).
;;;
;;; The parser's trees to words for the cellular machine (`layout::cellular`,
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
(define-effect compiles (maxeff (read @globals) (read @t) (read @k) (write @k) (alloc @k) (goto @y)))

;; The checker's facts for the program being compiled.
(define c-facts (ref k-facts @k) (new nil))
;; The same, by where each `extract` starts (two cannot start at one place):
;; where it ends, and its field. A table, so that a program's facts are not
;; searched from the start for each `extract` compiled.
(define c-int-hash (subr pure (int) int) (lambda (a) a))
(define c-int=? (subr pure (int int) bool) (lambda (a b) (= a b)))
(define c-fact-table (ref (table int (pairof int int @k) @k) @k) (new (make-table c-int-hash c-int=?)))
;; A `letrec`-bound procedure lambda-lifted, as Twobit's pass 2 lifts
;; (`pass2p2.sch`): its closure, over nothing, made while compiling; the
;; names it would have captured, each passed as an argument before its own.
(define-type c-lift (productof (1 wcell) (2 (listof symbol acyclic))))
;; The procedures lambda-lifted, by index; and, by where each `letrec` is
;; (`c-span-key`), its members' (none if it is not lifted), so that its
;; register code lifts it as its stack code did, with the same words.
(define c-lifts (ref (table int c-lift @k) @k) (new (make-table c-int-hash c-int=?)))
(define c-lift-count (ref int @k) (new 0))
(define c-lifted (ref (table int (listof (listof int @k) @k) @k) @k) (new (make-table c-int-hash c-int=?)))
;; The parameters a lifting added to the lambda about to be compiled.
(define c-lifting-added (ref int @k) (new 0))
;; Each expression's effect summary, by where it starts: where it ends, and
;; the summary, for each span starting there.
(define-type c-ends (listof (pairof int int @k) acyclic))
(define c-summary-table (ref (table int c-ends @k) @k) (new (make-table c-int-hash c-int=?)))
;; Each procedure converted to a convention (`k-convert-at`), by where it
;; starts: where it ends, and what `%fx26-convert` is given for it.
(define c-convert-table (ref (table int (pairof int int @k) @k) @k) (new (make-table c-int-hash c-int=?)))
(define c-no-conversion (pairof int int @k) (cons -1 -1))
;; What `%fx26-convert` is given for `x`, if it is converted; or -1.
(define c-conversion-at (subr (maxeff (read @globals) (read @k)) (exp) int)
  (lambda (x)
    (let ((e (table-ref (get c-convert-table) (exp-start x) c-no-conversion)))
      (if (= (car e) (exp-end x)) (cdr e) -1))))
;; The field of the `extract` from `a` to `b`, or -1.
(define c-field-at (subr (maxeff (read @globals) (read @k) (alloc @k)) (int int) int)
  (lambda (a b)
    (let ((e (table-ref (get c-fact-table) a (the (pairof int int @k) (cons -1 -1)))))
      (if (= (car e) b) (cdr e) -1))))

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
(define c-tag (prompt-tag cresult cresult (maxeff (read @globals) spin (read @t) (read @k) (write @k) (alloc @k)) @y)
  (make-continuation-prompt-tag))
(define c-fail (subr compiles (string) void)
  (lambda (message) (abort-current-continuation c-tag (c-err message))))

(define c-labels (ref int @k) (new 0))
(define c-fresh (subr (maxeff (read @globals) (read @k) (write @k)) () int)
  (lambda () (let ((n (get c-labels))) (begin (set c-labels (+ n 1)) n))))

(define c-emit (subr (maxeff (read @k) (write @k) (alloc @k)) (code item) unit)
  (lambda (c i) (set c (cons i (get c)))))
(define c-op (subr (maxeff (read @globals) (read @k) (write @k) (alloc @k)) (code int) unit)
  (lambda (c r) (c-emit c (i-cell (wcell-routine r)))))
(define c-op1 (subr (maxeff (read @globals) (read @k) (write @k) (alloc @k)) (code int wcell) unit)
  (lambda (c r x) (begin (c-op c r) (c-emit c (i-cell x)))))
(define c-lit (subr (maxeff (read @globals) (read @k) (write @k) (alloc @k)) (code wcell) unit)
  (lambda (c x) (c-op1 c routine-lit x)))
(define c-int (subr (maxeff (read @globals) (read @k) (write @k) (alloc @k)) (code int) unit)
  (lambda (c n) (c-lit c (wcell-int n))))
;; Field `k` of a bloblet whose type says it has one.
(define c-field (subr (maxeff (read @globals) (read @k) (write @k) (alloc @k)) (code int) unit)
  (lambda (c k) (c-op1 c routine-field (wcell-int k))))

;; A runtime primitive with `n` arguments.
(define c-prim (subr compiles (code string int) unit)
  (lambda (c name n)
    (let ((p (runtime-primitive name)))
      (if (< p 0)
          (c-fail (string-append "no runtime primitive " name))
          (begin (c-op1 c routine-prim (wcell-int p)) (c-emit c (i-cell (wcell-int n))))))))

;; Drop what a mutator left, and leave FX-26's unit value instead.
(define c-unit-after (subr (maxeff (read @globals) (read @k) (write @k) (alloc @k)) (code) unit)
  (lambda (c) (begin (c-op c routine-drop) (c-lit c (wcell-unit)))))

;;; ----------------------------------------------------------- assembling

(define c-reverse (subr (maxeff (read @globals) (read @k) (alloc @k) spin) (items items) items)
  (lambda (xs acc) (if (null? xs) acc (c-reverse (cdr xs) (cons (car xs) acc)))))

(define c-size (subr pure (item) int)
  (lambda (i) (tagcase i (i-cell (x) 1) (i-label (n) 0) (i-branch (n) 2) (i-zbranch (n) 2))))

;; Where each label is, in cells; and how many cells there are.
(define c-place (subr (maxeff (read @globals) (read @k) (write @k) spin) (items (arrayof int @k) int) int)
  (lambda (xs at pos)
    (if (null? xs)
        pos
        (begin (tagcase (car xs) (i-label (n) (array-set! at n pos)) (else x #u))
               (c-place (cdr xs) at (+ pos (c-size (car xs))))))))

;; The cells, branches resolved (an offset counts from the cell after it):
;; from the items newest first, each ending at `end`, onto those after it,
;; in a loop, however long the word.
(define c-cells (subr (maxeff (read @globals) (read @k) (alloc @k) spin) (items (arrayof int @k) int (listof wcell @k)) (listof wcell @k))
  (lambda (xs at end acc)
    (if (null? xs)
        acc
        (let ((pos (- end (c-size (car xs)))))
          (c-cells (cdr xs) at pos
                   (tagcase (car xs)
                     (i-cell (x) (cons x acc))
                     (i-label (n) acc)
                     (i-branch (n)
                       (cons (wcell-routine routine-branch) (cons (wcell-int (- (array-ref at n) (+ pos 2))) acc)))
                     (i-zbranch (n)
                       (cons (wcell-routine routine-zbranch) (cons (wcell-int (- (array-ref at n) (+ pos 2))) acc)))))))))

(define c-assemble (subr (maxeff (read @globals) (read @k) (write @k) (alloc @k) spin) (code symbol) tword)
  (lambda (c name)
    (let* ((at (the (arrayof int @k) (make-array (get c-labels) 0)))
           (end (c-place (c-reverse (get c) nil) at 0)))
      (make-word name (c-cells (get c) at end nil)))))

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
  (at-loop int)
  ;; A `letrec`-bound procedure lambda-lifted (`c-lift`), by its index in
  ;; `c-lifts`: only called, by a closure over nothing made once, with the
  ;; names it would have captured passed first.
  (at-lifted int))
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
;; How many of its parameters, first, a lifting added (`c-lift`): a loop
;; passes them on as they are.
(define c-this-added (ref int @k) (new 0))
;; What register code knows of the procedure being compiled, when it is one
;; that knows itself: its name, where the name is, and its arity.
(define-type c-this (productof (1 symbol) (2 loc) (3 int) (4 int)))

;; Whether each lambda also gets register code (PLAN.md 13h′), as its word's
;; twin; and the register compiler, `regcode.fx`, which sets itself here: a
;; lambda's register cells, or none where it declines.
(define c-registers (ref bool @k) (new #f))
(define c-register-code
  (ref (subr (maxeff compiles spin) ((listof (productof (1 symbol) (2 syns-a)) acyclic) exp cenv (listof c-this @k)) (listof wcell @k)) @k)
  (new (lambda (ps body inner this) (the (listof wcell @k) nil))))
;; The same for a standard operation as a value, by its name and arity.
(define c-standard-register-code
  (ref (subr (maxeff compiles spin) (string int) (listof wcell @k)) @k)
  (new (lambda (name n) (the (listof wcell @k) nil))))

;; Whether `l` is where the procedure being compiled is bound: its loop, or
;; the free value holding its closure.
(define c-this-loc? (subr (read @globals) (loc loc) bool)
  (lambda (l this)
    (tagcase this
      (at-loop (z) (c-loop? l))
      (at-free (i) (tagcase l (at-free (j) (= i j)) (else y #f)))
      ;; A top-level definition's own global, the only global its name can
      ;; be in its body.
      (at-global (g) (tagcase l (at-global (h) #t) (else y #f)))
      (else y #f))))

;; The global environment as compiling has reached it: by name, a table of
;; each name's globals, newest first, each with its place in the order they
;; were made (`c-genv-count` so far). A body compiled where it was written
;; sees only the globals made before (an inlined body, a copy specialized at
;; a lambda): `c-genv`, the count of them; -1 when every global is seen.
(define c-genv-index (ref (table symbol (listof (pairof int loc @k) acyclic) @k) @k) (new (make-table symbol-hash symbol=?)))
(define c-genv-count (ref int @k) (new 0))
(define c-genv (ref int @k) (new -1))
;; The globals seen now, as a count, for a body to see them so later.
(define c-genv-now (subr (maxeff (read @k) (read (globals c-genv c-genv-count))) () int)
  (lambda () (if (< (get c-genv) 0) (get c-genv-count) (get c-genv))))
(define c-global-first (subr (maxeff (read @globals) (read @k) (alloc @k)) ((listof (pairof int loc @k) acyclic) int) (listof loc @k))
  (lambda (es limit)
    (cond ((null? es) nil)
          ((or (< limit 0) (< (car (car es)) limit)) (the (listof loc @k) (cons (cdr (car es)) nil)))
          (else (c-global-first (cdr es) limit)))))
;; `n`'s newest global before the `limit`th (-1: any), in a list.
(define c-global-find (subr (maxeff (read @globals) (read @k) (alloc @k)) (symbol int) (listof loc @k))
  (lambda (n limit) (c-global-first (table-ref (get c-genv-index) n nil) limit)))

(define c-find (subr (maxeff (read @globals) (read @k) (alloc @k) spin) (cenv symbol) (listof loc @k))
  (lambda (e n)
    (cond ((null? e) nil)
          ((symbol=? (car (car e)) n) (the (listof loc @k) (cons (cdr (car e)) nil)))
          (else (c-find (cdr e) n)))))

;; Where `n` is: in the locals, else in the globals; none means standard.
(define c-where (subr (maxeff (read @globals) (read @k) (alloc @k) spin) (cenv symbol) (listof loc @k))
  (lambda (e n) (let ((l (c-find e n))) (if (null? l) (c-global-find n (get c-genv)) l))))

(define c-load (subr compiles (code loc) unit)
  (lambda (c l)
    (tagcase l
      (at-slot (i) (c-op1 c routine-slot (wcell-int i)))
      (at-free (i) (c-op1 c routine-free (wcell-int i)))
      (at-global (g) (c-op1 c routine-global (wcell-global g)))
      (at-pending (i) (c-fail "a letrec sibling not made yet is only captured"))
      (at-loop (z) (c-fail "a loop is only ever called, in tail position"))
      (at-lifted (k) (c-fail "a lifted procedure is only called")))))

;;; ------------------------------------------------------------- free names
;;; The names a lambda's body uses that it does not bind: what its closure
;;; must carry, once globals and standard names are set aside.

(define-type syms (listof symbol acyclic))

;; Each `letrec` in tail position asked about: which bindings are join points
;; (`regcode.fx`'s `r-join-flags`), by where its body starts: where the body
;; ends, the names bound, and the answer. Asked of the same `letrec` many
;; times over (each time what encloses it is asked whether it calls), and
;; the answer is the same each time.
(define-type c-join-answer (productof (1 int) (2 syms) (3 (listof bool acyclic))))
(define c-join-memo (ref (table int c-join-answer @k) @k) (new (make-table c-int-hash c-int=?)))
;; `es` with span end `b`'s summary at least `s`.
(define c-end-max (subr (maxeff (read @globals) (read @k) (alloc @k)) (c-ends int int) c-ends)
  (lambda (es b s)
    (cond ((null? es) (the c-ends (cons (the (pairof int int @k) (cons b s)) nil)))
          ((= (car (car es)) b)
           (the c-ends (cons (the (pairof int int @k) (cons b (if (> s (cdr (car es))) s (cdr (car es))))) (cdr es))))
          (else (the c-ends (cons (car es) (c-end-max (cdr es) b s)))))))
(define c-fill-facts (subr (maxeff (read @globals) (read @t) (read @k) (write @k) (alloc @k)) (k-facts) unit)
  (lambda (fs)
    (if (null? fs)
        #u
        (let ((a (extract (car fs) 1)) (b (extract (car fs) 2)) (n (extract (car fs) 3)))
          (begin
            (cond ((>= n 0) (table-set! (get c-fact-table) a (the (pairof int int @k) (cons b n))))
                  ;; A conversion, -1000 - code (`k-convert-at`).
                  ((<= n -1000) (table-set! (get c-convert-table) a (the (pairof int int @k) (cons b (- -1000 n)))))
                  ;; An effect summary, -1 - s: the greatest, per span.
                  (else
                   (let ((s (- -1 n)) (known (table-ref (get c-summary-table) a (the c-ends nil))))
                     (table-set! (get c-summary-table) a (c-end-max known b s)))))
            (c-fill-facts (cdr fs)))))))
(define c-end-summary (subr (maxeff (read @globals) (read @k)) (c-ends int) int)
  (lambda (es b) (cond ((null? es) 3) ((= (car (car es)) b) (cdr (car es))) (else (c-end-summary (cdr es) b)))))
;; The effect summary of the expression from `a` to `b` (3, the most, if
;; none was noted: `checked-extracts`).
(define c-summary-at (subr (maxeff (read @globals) (read @k)) (int int) int)
  (lambda (a b) (c-end-summary (table-ref (get c-summary-table) a (the c-ends nil)) b)))
;; `c-facts` into `c-fact-table`.
(define c-set-facts! (subr (maxeff (read @globals) (read @t) (read @k) (write @k) (alloc @k)) (k-facts) unit)
  (lambda (fs)
    (begin
      (set c-facts fs)
      (set c-fact-table (make-table c-int-hash c-int=?))
      (set c-convert-table (make-table c-int-hash c-int=?))
      (set c-summary-table (make-table c-int-hash c-int=?))
      (set c-join-memo (make-table c-int-hash c-int=?))
      (set c-lifts (make-table c-int-hash c-int=?))
      (set c-lift-count 0)
      (set c-lifted (make-table c-int-hash c-int=?))
      (c-fill-facts fs))))
(define c-member? (subr (maxeff (read @globals) (read @k)) (syms symbol) bool)
  (lambda (xs n) (and (not (null? xs)) (or (symbol=? (car xs) n) (c-member? (cdr xs) n)))))
(define c-adjoin (subr (maxeff (read @globals) (read @k) (alloc @k)) (syms symbol) syms)
  (lambda (xs n) (if (c-member? xs n) xs (cons n xs))))

(define c-bind-params (subr (maxeff (read @globals) (read @k) (alloc @k)) ((listof (productof (1 symbol) (2 syns-a)) acyclic) syms) syms)
  (lambda (ps bound) (if (null? ps) bound (c-bind-params (cdr ps) (cons (extract (car ps) 1) bound)))))
(define c-bind-letrec (subr (maxeff (read @globals) (read @k) (alloc @k)) ((listof (productof (1 symbol) (2 syn) (3 exp)) acyclic) syms) syms)
  (lambda (bs bound) (if (null? bs) bound (c-bind-letrec (cdr bs) (cons (extract (car bs) 1) bound)))))
(define c-bind-let (subr (maxeff (read @globals) (read @k) (alloc @k)) ((listof (productof (1 symbol) (2 exp)) acyclic) syms) syms)
  (lambda (bs bound) (if (null? bs) bound (c-bind-let (cdr bs) (cons (extract (car bs) 1) bound)))))
(define c-names (subr (maxeff (read @globals) (read @k) (alloc @k)) (names syms) syms)
  (lambda (ns bound) (if (null? ns) bound (c-names (cdr ns) (cons (car ns) bound)))))

(define-rec
  (c-free-all (subr (maxeff (read @globals) (read @k) (alloc @k) spin) ((listof exp acyclic) syms syms) syms)
    (lambda (es bound acc) (if (null? es) acc (c-free-all (cdr es) bound (c-free (car es) bound acc)))))
  (c-free (subr (maxeff (read @globals) (read @k) (alloc @k) spin) (exp syms syms) syms)
    (lambda (x bound acc)
      (tagcase x
        (e-var (n a b) (if (c-member? bound n) acc (c-adjoin acc n)))
        (e-lambda (ps body a b) (c-free body (c-bind-params ps bound) acc))
        (e-app (f args a b) (c-free f bound (c-free-all args bound acc)))
        (e-plambda (d body a b) (c-free body bound acc))
        (e-letregion (k r i body a b) (c-free body (cons r bound) acc))
        (e-rlambda (r l a b) (c-free r bound (c-free l bound acc)))
        (e-proj (body ds a b) (c-free body bound acc))
        (e-the (d body a b) (c-free body bound acc))
        (e-convention (cnv body a b) (c-free body bound acc))
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
  (c-free-letrec (subr (maxeff (read @globals) (read @k) (alloc @k) spin) ((listof (productof (1 symbol) (2 syn) (3 exp)) acyclic) syms syms) syms)
    (lambda (bs bound acc) (if (null? bs) acc (c-free-letrec (cdr bs) bound (c-free (extract (car bs) 3) bound acc)))))
  (c-free-let (subr (maxeff (read @globals) (read @k) (alloc @k) spin) ((listof (productof (1 symbol) (2 exp)) acyclic) syms syms) syms)
    (lambda (bs bound acc) (if (null? bs) acc (c-free-let (cdr bs) bound (c-free (extract (car bs) 2) bound acc)))))
  (c-free-fields (subr (maxeff (read @globals) (read @k) (alloc @k) spin) ((listof (productof (1 symbol) (2 exp)) acyclic) syms syms) syms)
    (lambda (fs bound acc) (if (null? fs) acc (c-free-fields (cdr fs) bound (c-free (extract (car fs) 2) bound acc)))))
  (c-free-arms
    (subr (maxeff (read @globals) (read @k) (alloc @k) spin) ((listof (productof (1 symbol) (2 bool) (3 names) (4 exp)) acyclic) syms syms) syms)
    (lambda (arms bound acc)
      (if (null? arms)
          acc
          (c-free-arms (cdr arms) bound (c-free (extract (car arms) 4) (c-names (extract (car arms) 3) bound) acc)))))
  (c-free-else (subr (maxeff (read @globals) (read @k) (alloc @k) spin) ((listof (productof (1 symbol) (2 exp)) acyclic) syms syms) syms)
    (lambda (els bound acc)
      (if (null? els) acc (c-free (extract (car els) 2) (cons (extract (car els) 1) bound) acc)))))

;; What is left when the value is in hand: `return` in tail position.
(define c-done (subr (maxeff (read @globals) (read @k) (write @k) (alloc @k)) (code bool) unit)
  (lambda (c tail) (if tail (c-op c routine-return) #u)))

;; After a body whose value is on top of `n` values bound from `slot`
;; up: the value into `slot`, the others dropped. Nothing in tail
;; position, where `return` drops the whole frame.
(define c-unbind (subr (maxeff (read @globals) (read @k) (write @k) (alloc @k) spin) (code int int bool) unit)
  (lambda (c slot n tail)
    (if (or tail (= n 0))
        #u
        (letrec ((drops (subr (maxeff (read @globals) (read @k) (write @k) (alloc @k) spin) (int) unit)
                   (lambda (k) (if (= k 0) #u (begin (c-op c routine-drop) (drops (- k 1)))))))
          (begin (c-op1 c routine-slot! (wcell-int slot)) (drops (- n 1)))))))

(define c-count-let (subr (read @globals) ((listof (productof (1 symbol) (2 exp)) acyclic)) int)
  (lambda (bs) (if (null? bs) 0 (+ 1 (c-count-let (cdr bs))))))

;; `letrec`: every binding is a lambda (the checker says so). Each closure
;; is made in its slot, with a placeholder for a sibling not made yet; then
;; each placeholder is patched with its sibling. Nothing runs in between, so
;; no one sees the knot tied. A name used only in calls of itself that are
;; loops is not captured at all.
(define-type patches (listof (pairof int int @k) @k))

(define c-letrec-slots (subr (maxeff (read @globals) (alloc @k)) ((listof (productof (1 symbol) (2 syn) (3 exp)) acyclic) cenv int) cenv)
  (lambda (bs e d)
    (if (null? bs) e (c-letrec-slots (cdr bs) (the cenv (cons (cons (extract (car bs) 1) (at-slot d)) e)) (+ d 1)))))
(define c-patch-one (subr (maxeff compiles spin) (patches int int code) unit)
  (lambda (ps depth i c)
    (if (null? ps)
        #u
        (begin (c-op1 c routine-slot (wcell-int (cdr (car ps))))
               (c-op1 c routine-slot (wcell-int (+ depth i)))
               (c-int c (+ cellular-closure-free0 (car (car ps))))
               (c-op c routine-field-set)
               (c-patch-one (cdr ps) depth i c)))))

;; Each placeholder of closure `i` patched with its sibling.
(define c-letrec-patch (subr (maxeff compiles spin) ((listof patches @k) int int code) unit)
  (lambda (made depth i c)
    (if (null? made)
        #u
        (begin (c-patch-one (car made) depth i c) (c-letrec-patch (cdr made) depth (+ i 1) c)))))

;;; ------------------------------------------------------- known procedures

;; `x`, when it is a lambda under any type abstractions and ascriptions,
;; which compile to nothing; none otherwise.
(define c-lambda-of (subr (maxeff (read @globals) (alloc @k)) (exp) (listof exp @k))
  (lambda (x)
    (tagcase x
      (e-plambda (d body a b) (c-lambda-of body))
      (e-the (d body a b) (c-lambda-of body))
      (e-convention (cnv body a b) (c-lambda-of body))
      (e-lambda (ps body a b) (the (listof exp @k) (cons x nil)))
      (e-rlambda (r l a b) (the (listof exp @k) (cons x nil)))
      (else y nil))))
(define c-count-exps (subr (read @globals) ((listof exp acyclic)) int)
  (lambda (es) (if (null? es) 0 (+ 1 (c-count-exps (cdr es))))))
(define c-count-params (subr (read @globals) ((listof (productof (1 symbol) (2 syns-a)) acyclic)) int)
  (lambda (ps) (if (null? ps) 0 (+ 1 (c-count-params (cdr ps))))))
;; Parameters `ps` bound to `args`, as a `let` binds.
(define c-param-bindings (subr (maxeff (read @globals) (read @k) (alloc @k) spin) ((listof (productof (1 symbol) (2 syns-a)) acyclic) (listof exp acyclic)) (listof (productof (1 symbol) (2 exp)) acyclic))
  (lambda (ps args) (if (null? ps) nil (cons (product (1 (extract (car ps) 1)) (2 (car args))) (c-param-bindings (cdr ps) (cdr args))))))
;; A plain lambda (under forms that compile to nothing) applied at once to
;; as many arguments as it has parameters, as the Rust compiler's
;; `applied_lambda` finds it: the `let` it is, its bindings and body, in a
;; list of one; none if `f` is no such lambda.
(define c-applied-let (subr (maxeff (read @globals) (read @k) (alloc @k) spin) (exp (listof exp acyclic)) (listof (productof (1 (listof (productof (1 symbol) (2 exp)) acyclic)) (2 exp)) @k))
  (lambda (f args)
    (let ((lam (c-lambda-of f)))
      (if (null? lam)
          nil
          (tagcase (car lam)
            (e-lambda (ps body a b)
              (if (= (c-count-params ps) (c-count-exps args))
                  (the (listof (productof (1 (listof (productof (1 symbol) (2 exp)) acyclic)) (2 exp)) @k)
                    (cons (product (1 (c-param-bindings ps args)) (2 body)) nil))
                  nil))
            (else y nil))))))

(define c-mentions? (subr (maxeff (read @globals) (read @k) (alloc @k) spin) (exp symbol) bool)
  (lambda (x n) (c-member? (c-free x nil nil) n)))

;; Whether every use of `f` in `x` is a call with `n` arguments in tail
;; position, which the compiler makes a loop.

(define-rec
  (c-loops-only (subr (maxeff (read @globals) (read @k) (alloc @k) spin) (exp symbol int bool) bool)
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
        (e-letregion (k r i body a b) (or (symbol=? r f) (c-loops-only body f n #f)))
        (e-rlambda (r l a b) (and (c-loops-only r f n #f) (c-loops-only l f n #f)))
        (e-proj (body ds a b) (c-loops-only body f n tail))
        (e-the (d body a b) (c-loops-only body f n tail))
        (e-convention (cnv body a b) (c-loops-only body f n tail))
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
  (c-loops-only-all (subr (maxeff (read @globals) (read @k) (alloc @k) spin) ((listof exp acyclic) symbol int) bool)
    (lambda (es f n) (or (null? es) (and (c-loops-only (car es) f n #f) (c-loops-only-all (cdr es) f n)))))
  (c-loops-only-begin (subr (maxeff (read @globals) (read @k) (alloc @k) spin) ((listof exp acyclic) symbol int bool) bool)
    (lambda (es f n tail)
      (cond ((null? es) #t)
            ((null? (cdr es)) (c-loops-only (car es) f n tail))
            (else (and (c-loops-only (car es) f n #f) (c-loops-only-begin (cdr es) f n tail))))))
  (c-loops-only-letrec (subr (maxeff (read @globals) (read @k) (alloc @k) spin) ((listof (productof (1 symbol) (2 syn) (3 exp)) acyclic) symbol int) bool)
    (lambda (bs f n) (or (null? bs) (and (c-loops-only (extract (car bs) 3) f n #f) (c-loops-only-letrec (cdr bs) f n)))))
  (c-loops-only-let (subr (maxeff (read @globals) (read @k) (alloc @k) spin) ((listof (productof (1 symbol) (2 exp)) acyclic) symbol int) bool)
    (lambda (bs f n) (or (null? bs) (and (c-loops-only (extract (car bs) 2) f n #f) (c-loops-only-let (cdr bs) f n)))))
  (c-loops-only-fields (subr (maxeff (read @globals) (read @k) (alloc @k) spin) ((listof (productof (1 symbol) (2 exp)) acyclic) symbol int) bool)
    (lambda (fs f n) (or (null? fs) (and (c-loops-only (extract (car fs) 2) f n #f) (c-loops-only-fields (cdr fs) f n)))))
  (c-loops-only-arms
    (subr (maxeff (read @globals) (read @k) (alloc @k) spin) ((listof (productof (1 symbol) (2 bool) (3 names) (4 exp)) acyclic) symbol int bool) bool)
    (lambda (arms f n tail)
      (or (null? arms)
          (and (or (c-member? (c-names (extract (car arms) 3) nil) f) (c-loops-only (extract (car arms) 4) f n tail))
               (c-loops-only-arms (cdr arms) f n tail)))))
  (c-loops-only-else (subr (maxeff (read @globals) (read @k) (alloc @k) spin) ((listof (productof (1 symbol) (2 exp)) acyclic) symbol int bool) bool)
    (lambda (els f n tail)
      (or (null? els) (or (symbol=? (extract (car els) 1) f) (c-loops-only (extract (car els) 2) f n tail))))))

;; Binding `i`'s scope while it is made: each sibling pending, and itself a
;; loop if it only calls itself in loops.
(define c-letrec-own
  (subr (maxeff (read @globals) (read @k) (alloc @k) spin) ((listof (productof (1 symbol) (2 syn) (3 exp)) acyclic) cenv int int int exp int) cenv)
  (lambda (bs e depth k i body nps)
    (if (null? bs)
        e
        (let ((g (extract (car bs) 1)))
          (c-letrec-own (cdr bs)
                        (the cenv (cons (cons g (if (and (= k i) (c-loops-only body g nps #t)) (at-loop 0) (at-pending (+ depth k)))) e))
                        depth (+ k 1) i body nps)))))
(define c-count-letrec (subr (read @globals) ((listof (productof (1 symbol) (2 syn) (3 exp)) acyclic)) int)
  (lambda (bs) (if (null? bs) 0 (+ 1 (c-count-letrec (cdr bs))))))
(define c-length (subr (maxeff (read @globals) (read @k) spin) (syms) int)
  (lambda (xs) (if (null? xs) 0 (+ 1 (c-length (cdr xs))))))
(define c-nth-binding
  (subr (read @globals) ((listof (productof (1 symbol) (2 syn) (3 exp)) acyclic) int) (productof (1 symbol) (2 syn) (3 exp)))
  (lambda (bs i) (if (= i 0) (car bs) (c-nth-binding (cdr bs) (- i 1)))))
;; Whether no binding of `bs` but the `i`th mentions `name`; `k` counts.
(define c-unmentioned? (subr (maxeff (read @globals) (read @k) (alloc @k) spin) ((listof (productof (1 symbol) (2 syn) (3 exp)) acyclic) symbol int int) bool)
  (lambda (bs name i k)
    (or (null? bs)
        (and (or (= k i) (not (c-mentions? (extract (car bs) 3) name))) (c-unmentioned? (cdr bs) name i (+ k 1))))))
;; Whether `letrec` binding `i` of `bs` is a join point, as the Rust
;; compiler's `r_join_ok` says: a lambda whose body calls it only in tail
;; position, as the `letrec`'s body does, and that no sibling mentions; so
;; no closure of it need be made, and each call is a jump.
(define c-join-ok? (subr (maxeff (read @globals) (read @k) (alloc @k) spin) ((listof (productof (1 symbol) (2 syn) (3 exp)) acyclic) exp int) bool)
  (lambda (bs body i)
    (let* ((b (c-nth-binding bs i)) (name (extract b 1)) (lam (c-lambda-of (extract b 3))))
      (and (not (null? lam))
           (tagcase (car lam)
             (e-lambda (ps lbody la lb)
               (let ((n (c-count-params ps)))
                 (and (not (c-member? (c-bind-params ps nil) name))
                      (and (c-loops-only lbody name n #t)
                           (and (c-loops-only body name n #t) (c-unmentioned? bs name i 0))))))
             (else y #f))))))
;;; ------------------------------------------------------ lambda lifting
;;; As the Rust compiler's `lift`, `lift_plan` and `called_only`.

;; A `letrec`'s key in `c-lifted`: where it starts and ends.
(define c-span-key (subr pure (int int) int) (lambda (a b) (+ (* a 4194304) b)))
;; The index in `c-lifts` of the procedure `n` names in `e`, if a lifted
;; one; else -1.
(define c-lifted-index (subr (maxeff (read @globals) (read @k) (alloc @k) spin) (symbol cenv) int)
  (lambda (n e) (let ((l (c-find e n))) (if (null? l) -1 (tagcase (car l) (at-lifted (k) k) (else y -1))))))
(define c-lifted-at (subr (maxeff (read @globals) (read @k) (alloc @k) spin) (exp cenv) int)
  (lambda (f e) (tagcase f (e-var (n a b) (c-lifted-index n e)) (else y -1))))
;; A lifted procedure's added names.
(define c-lift-added (subr (maxeff (read @globals) (read @k)) (int) syms)
  (lambda (k) (extract (table-ref (get c-lifts) k (the c-lift (product (1 (wcell-nil)) (2 (the syms nil))))) 2)))
;; The lifted procedures `e` binds, as it binds them: known everywhere
;; inside a lambda, being constants.
(define c-lifted-entries (subr (maxeff (read @globals) (read @k) (alloc @k) spin) (cenv) cenv)
  (lambda (e)
    (cond ((null? e) nil)
          ((tagcase (cdr (car e)) (at-lifted (k) #t) (else y #f)) (the cenv (cons (car e) (c-lifted-entries (cdr e)))))
          (else (c-lifted-entries (cdr e))))))
;; Each of `ns`' values pushed, from where `e` has it.
(define c-load-names (subr (maxeff compiles spin) (syms cenv code) unit)
  (lambda (ns e c)
    (if (null? ns)
        #u
        (let ((l (c-where e (car ns))))
          (begin (if (null? l) (c-fail "a lifted procedure's added name is not bound") (c-load c (car l)))
                 (c-load-names (cdr ns) e c))))))
(define c-snoc (subr (maxeff (read @globals) (read @k) (alloc @k) spin) (syms symbol) syms)
  (lambda (xs n) (if (null? xs) (cons n nil) (cons (car xs) (c-snoc (cdr xs) n)))))
;; `acc` with each of `ns` in neither it nor `params` after it, in order.
(define c-append-new (subr (maxeff (read @globals) (read @k) (alloc @k) spin) (syms syms syms) syms)
  (lambda (ns acc params)
    (cond ((null? ns) acc)
          ((or (c-member? acc (car ns)) (c-member? params (car ns))) (c-append-new (cdr ns) acc params))
          (else (c-append-new (cdr ns) (c-snoc acc (car ns)) params)))))
(define c-lifted-names-onto (subr (maxeff (read @globals) (read @k) (alloc @k) spin) (syms syms syms cenv) syms)
  (lambda (xs acc params e)
    (if (null? xs)
        acc
        (let ((k (c-lifted-index (car xs) e)))
          (c-lifted-names-onto (cdr xs) (if (< k 0) acc (c-append-new (c-lift-added k) acc params)) params e)))))
;; `free` with, for each lifted procedure in it, the names its calls pass
;; (not `params`) after: code that calls one needs them too.
(define c-with-lifted-names (subr (maxeff (read @globals) (read @k) (alloc @k) spin) (syms syms cenv) syms)
  (lambda (free params e) (c-lifted-names-onto free free params e)))

;; Whether every use of `f` in `x` is a call with `n` arguments, in any
;; position and in lambdas inside too: so it is never a value.
(define-rec
  (c-called-only (subr (maxeff (read @globals) (read @k) (alloc @k) spin) (exp symbol int) bool)
    (lambda (x f n)
      (tagcase x
        (e-var (m a b) (not (symbol=? m f)))
        (e-app (fun args a b)
          (and (c-called-only-all args f n)
               (tagcase fun
                 (e-var (m a2 b2) (if (symbol=? m f) (= (c-count-exps args) n) #t))
                 (else y (c-called-only fun f n)))))
        (e-lambda (ps body a b) (or (c-member? (c-bind-params ps nil) f) (c-called-only body f n)))
        (e-rlambda (r l a b) (and (c-called-only r f n) (c-called-only l f n)))
        (e-plambda (d body a b) (c-called-only body f n))
        (e-proj (body ds a b) (c-called-only body f n))
        (e-the (d body a b) (c-called-only body f n))
        (e-convention (cnv body a b) (c-called-only body f n))
        (e-letregion (k r i body a b) (or (symbol=? r f) (c-called-only body f n)))
        (e-if (t th el a b) (and (c-called-only t f n) (and (c-called-only th f n) (c-called-only el f n))))
        (e-letrec (bs body a b)
          (or (c-member? (c-bind-letrec bs nil) f) (and (c-called-only-letrec bs f n) (c-called-only body f n))))
        (e-let (bs body a b)
          (and (c-called-only-let bs f n) (or (c-member? (c-bind-let bs nil) f) (c-called-only body f n))))
        (e-begin (es a b) (c-called-only-all es f n))
        (e-prompt (t body h a b) (and (c-called-only t f n) (and (c-called-only body f n) (c-called-only h f n))))
        (e-bloblet (op i args a b) (c-called-only-all args f n))
        (e-product (fs a b) (c-called-only-fields fs f n))
        (e-extract (p l a b) (c-called-only p f n))
        (e-sum (t v a b) (c-called-only v f n))
        (e-tagcase (s arms els a b)
          (and (c-called-only s f n) (and (c-called-only-arms arms f n) (c-called-only-else els f n))))
        (else y #t))))
  (c-called-only-all (subr (maxeff (read @globals) (read @k) (alloc @k) spin) ((listof exp acyclic) symbol int) bool)
    (lambda (es f n) (or (null? es) (and (c-called-only (car es) f n) (c-called-only-all (cdr es) f n)))))
  (c-called-only-letrec (subr (maxeff (read @globals) (read @k) (alloc @k) spin) ((listof (productof (1 symbol) (2 syn) (3 exp)) acyclic) symbol int) bool)
    (lambda (bs f n) (or (null? bs) (and (c-called-only (extract (car bs) 3) f n) (c-called-only-letrec (cdr bs) f n)))))
  (c-called-only-let (subr (maxeff (read @globals) (read @k) (alloc @k) spin) ((listof (productof (1 symbol) (2 exp)) acyclic) symbol int) bool)
    (lambda (bs f n) (or (null? bs) (and (c-called-only (extract (car bs) 2) f n) (c-called-only-let (cdr bs) f n)))))
  (c-called-only-fields (subr (maxeff (read @globals) (read @k) (alloc @k) spin) ((listof (productof (1 symbol) (2 exp)) acyclic) symbol int) bool)
    (lambda (fs f n) (or (null? fs) (and (c-called-only (extract (car fs) 2) f n) (c-called-only-fields (cdr fs) f n)))))
  (c-called-only-arms
    (subr (maxeff (read @globals) (read @k) (alloc @k) spin) ((listof (productof (1 symbol) (2 bool) (3 names) (4 exp)) acyclic) symbol int) bool)
    (lambda (arms f n)
      (or (null? arms)
          (and (or (c-member? (c-names (extract (car arms) 3) nil) f) (c-called-only (extract (car arms) 4) f n))
               (c-called-only-arms (cdr arms) f n)))))
  (c-called-only-else (subr (maxeff (read @globals) (read @k) (alloc @k) spin) ((listof (productof (1 symbol) (2 exp)) acyclic) symbol int) bool)
    (lambda (els f n) (or (null? els) (or (symbol=? (extract (car els) 1) f) (c-called-only (extract (car els) 2) f n))))))

;; Whether every binding of `bs`, from the `i`th, is a join point.
(define c-all-join? (subr (maxeff (read @globals) (read @k) (alloc @k) spin) ((listof (productof (1 symbol) (2 syn) (3 exp)) acyclic) exp int) bool)
  (lambda (bs body i) (or (>= i (c-count-letrec bs)) (and (c-join-ok? bs body i) (c-all-join? bs body (+ i 1))))))
;; Whether no binding of `all` uses `name` but in calls of `n` arguments.
(define c-called-only-inits (subr (maxeff (read @globals) (read @k) (alloc @k) spin) ((listof (productof (1 symbol) (2 syn) (3 exp)) acyclic) symbol int) bool)
  (lambda (all name n) (or (null? all) (and (c-called-only (extract (car all) 3) name n) (c-called-only-inits (cdr all) name n)))))
;; Whether each member of `bs` is a plain lambda, only ever called, with
;; its arity, in `body` and in every binding of `all`.
(define c-liftable? (subr (maxeff (read @globals) (read @k) (alloc @k) spin) ((listof (productof (1 symbol) (2 syn) (3 exp)) acyclic) (listof (productof (1 symbol) (2 syn) (3 exp)) acyclic) exp) bool)
  (lambda (all bs body)
    (or (null? bs)
        (let ((lam (c-lambda-of (extract (car bs) 3))))
          (and (not (null? lam))
               (tagcase (car lam)
                 (e-lambda (ps lbody a b)
                   (let ((name (extract (car bs) 1)) (n (c-count-params ps)))
                     (and (c-called-only body name n) (and (c-called-only-inits all name n) (c-liftable? all (cdr bs) body)))))
                 (else y #f)))))))
;; The locals of `free` (not `names`, the siblings) a member would capture,
;; onto `acc`, in a list of one; none if one is a sibling not made yet or a
;; loop, which cannot be passed.
(define c-lift-locals (subr (maxeff (read @globals) (read @k) (alloc @k) spin) (syms syms cenv syms) (listof syms @k))
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
(define c-sibling-indices (subr (maxeff (read @globals) (read @k) (alloc @k) spin) (syms (listof (productof (1 symbol) (2 syn) (3 exp)) acyclic) int) (listof int @k))
  (lambda (free bs k)
    (cond ((null? bs) nil)
          ((c-member? free (extract (car bs) 1)) (cons k (c-sibling-indices free (cdr bs) (+ k 1))))
          (else (c-sibling-indices free (cdr bs) (+ k 1))))))
;; Each member's locals into `added`, the siblings it calls into `calls`,
;; from the `i`th of `bs`; whether every member's could be.
(define c-lift-direct
  (subr (maxeff (read @globals) (read @k) (write @k) (alloc @k) spin)
        ((listof (productof (1 symbol) (2 syn) (3 exp)) acyclic) (listof (productof (1 symbol) (2 syn) (3 exp)) acyclic) int syms cenv (arrayof syms @k) (arrayof (listof int @k) @k))
        bool)
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
(define c-union-into (subr (maxeff (read @globals) (read @k) (alloc @k) spin) (syms syms) syms)
  (lambda (xs ys) (if (null? ys) xs (c-union-into (if (c-member? xs (car ys)) xs (cons (car ys) xs)) (cdr ys)))))
;; Member `i` takes what the siblings `js` it calls take too; whether it
;; took more than it had (`more`).
(define c-lift-from (subr (maxeff (read @globals) (read @k) (write @k) (alloc @k) spin) ((arrayof syms @k) int (listof int @k) bool) bool)
  (lambda (added i js more)
    (if (null? js)
        more
        (let* ((had (array-ref added i)) (now (c-union-into had (array-ref added (car js)))))
          (begin (array-set! added i now)
                 (c-lift-from added i (cdr js) (or more (not (= (c-length now) (c-length had))))))))))
(define c-lift-round (subr (maxeff (read @globals) (read @k) (write @k) (alloc @k) spin) ((arrayof syms @k) (arrayof (listof int @k) @k) int int bool) bool)
  (lambda (added calls i n more)
    (if (>= i n) more (c-lift-round added calls (+ i 1) n (c-lift-from added i (array-ref calls i) more)))))
;; Twobit's flow equations (`compute-added-arguments`), to their fixed
;; point: each member takes its locals, and what each sibling it calls
;; takes.
(define c-lift-flow (subr (maxeff (read @globals) (read @k) (write @k) (alloc @k) spin) ((arrayof syms @k) (arrayof (listof int @k) @k) int) unit)
  (lambda (added calls n) (if (c-lift-round added calls 0 n #f) (c-lift-flow added calls n) #u)))
;; Where `n` is bound in `e`, counting from the innermost.
(define c-env-pos (subr (maxeff (read @globals) (read @k) spin) (cenv symbol int) int)
  (lambda (e n k) (cond ((null? e) k) ((symbol=? (car (car e)) n) k) (else (c-env-pos (cdr e) n (+ k 1))))))
(define c-insert-outer (subr (maxeff (read @globals) (read @k) (alloc @k) spin) (symbol syms cenv) syms)
  (lambda (x ys e)
    (cond ((null? ys) (cons x nil))
          ((> (c-env-pos e x 0) (c-env-pos e (car ys) 0)) (cons x ys))
          (else (cons (car ys) (c-insert-outer x (cdr ys) e))))))
;; `xs`, outermost binding first.
(define c-sort-outer (subr (maxeff (read @globals) (read @k) (alloc @k) spin) (syms cenv) syms)
  (lambda (xs e) (if (null? xs) nil (c-insert-outer (car xs) (c-sort-outer (cdr xs) e) e))))
(define c-lift-sort (subr (maxeff (read @globals) (read @k) (write @k) (alloc @k) spin) ((arrayof syms @k) cenv int int) unit)
  (lambda (added e i n) (if (>= i n) #u (begin (array-set! added i (c-sort-outer (array-ref added i) e)) (c-lift-sort added e (+ i 1) n)))))
;; Whether each member, from the `i`th of `bs`, takes fewer than 6 names
;; more, and no more than `register-regs` arguments in all.
(define c-lift-fits? (subr (maxeff (read @globals) (read @k) (alloc @k) spin) ((listof (productof (1 symbol) (2 syn) (3 exp)) acyclic) (arrayof syms @k) int) bool)
  (lambda (bs added i)
    (or (null? bs)
        (tagcase (car (c-lambda-of (extract (car bs) 3)))
          (e-lambda (ps lbody a b)
            (let ((m (c-length (array-ref added i))))
              (and (< m 6) (and (<= (+ m (c-count-params ps)) register-regs) (c-lift-fits? (cdr bs) added (+ i 1))))))
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
  (subr (maxeff (read @globals) (read @k) (write @k) (alloc @k) spin)
        ((listof (productof (1 symbol) (2 syn) (3 exp)) acyclic) exp cenv bool) (listof (arrayof syms @k) @k))
  (lambda (bs body e tail)
    (if (or (and tail (c-all-join? bs body 0)) (not (c-liftable? bs bs body)))
        nil
        (let* ((n (c-count-letrec bs))
               (added (the (arrayof syms @k) (make-array n nil)))
               (calls (the (arrayof (listof int @k) @k) (make-array n nil))))
          (if (not (c-lift-direct bs bs 0 (c-bind-letrec bs nil) e added calls))
              nil
              (begin
                (c-lift-flow added calls n)
                (c-lift-sort added e 0 n)
                (if (c-lift-fits? bs added 0) (the (listof (arrayof syms @k) @k) (cons added nil)) nil)))))))
;; `bs`' names bound to the lifted procedures `ks`, onto `e`.
(define c-bind-lifted (subr (maxeff (read @globals) (read @k) (alloc @k) spin) ((listof (productof (1 symbol) (2 syn) (3 exp)) acyclic) (listof int @k) cenv) cenv)
  (lambda (bs ks e)
    (if (null? bs) e (c-bind-lifted (cdr bs) (cdr ks) (the cenv (cons (cons (extract (car bs) 1) (at-lifted (car ks))) e))))))
;; The names `added` as parameters (with no type), then `ps`.
(define c-added-params (subr (maxeff (read @globals) (read @k) (alloc @k) spin) (syms (listof (productof (1 symbol) (2 syns-a)) acyclic)) (listof (productof (1 symbol) (2 syns-a)) acyclic))
  (lambda (added ps) (if (null? added) ps (cons (product (1 (car added)) (2 (the syns-a nil))) (c-added-params (cdr added) ps)))))
;; A closure over nothing for each member, from the `i`th, its word to
;; come, in `c-lifts` with what it takes: their indices.
(define c-lift-closures (subr (maxeff (read @globals) (read @k) (write @k) (alloc @k) spin) ((listof (productof (1 symbol) (2 syn) (3 exp)) acyclic) (arrayof syms @k) int) (listof int @k))
  (lambda (bs added i)
    (if (null? bs)
        nil
        (let ((k (get c-lift-count)))
          (begin
            (table-set! (get c-lifts) k (the c-lift (product (1 (wcell-closure)) (2 (array-ref added i)))))
            (set c-lift-count (+ k 1))
            (cons k (c-lift-closures (cdr bs) added (+ i 1))))))))


(define c-param-env (subr (maxeff (read @globals) (alloc @k)) ((listof (productof (1 symbol) (2 syns-a)) acyclic) int cenv) cenv)
  (lambda (ps i acc) (if (null? ps) acc (c-param-env (cdr ps) (+ i 1) (the cenv (cons (cons (extract (car ps) 1) (at-slot i)) acc))))))

;; The free names that are locals here, not globals or standard names, nor
;; a loop, which is not a value.
(define c-captured (subr (maxeff (read @globals) (read @k) (alloc @k) spin) (syms cenv) syms)
  (lambda (xs e)
    (cond ((null? xs) nil)
          ((null? (c-find e (car xs))) (c-captured (cdr xs) e))
          ((c-loop? (car (c-find e (car xs)))) (c-captured (cdr xs) e))
          ;; A definition's own global, in its body's names, is still a global.
          ((tagcase (car (c-find e (car xs))) (at-global (g) #t) (at-lifted (k) #t) (else y #f)) (c-captured (cdr xs) e))
          (else (cons (car xs) (c-captured (cdr xs) e))))))

;; The names a lambda of `ps` and `body` captures in `e`, as the Rust
;; compiler's `captured` finds them: its free locals, and the names the
;; lifted procedures it calls take.
(define c-lambda-captured (subr (maxeff (read @globals) (read @k) (alloc @k) spin) ((listof (productof (1 symbol) (2 syns-a)) acyclic) exp cenv) syms)
  (lambda (ps body e)
    (let ((params (c-bind-params ps nil)))
      (c-captured (c-with-lifted-names (c-free body params nil) params e) e))))
;; Free value `i` for each captured name, boxed if it was boxed outside.
(define c-inner-env (subr (maxeff (read @globals) (read @k) (alloc @k) spin) (syms cenv cenv int) cenv)
  (lambda (xs outer acc i)
    (if (null? xs)
        acc
        (c-inner-env (cdr xs) outer
                       (the cenv (cons (cons (car xs) (at-free i)) acc))
                       (+ i 1)))))

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

(define c-self-call? (subr (maxeff (read @globals) (read @k) (alloc @k) spin) (exp (listof exp acyclic) cenv bool) bool)
  (lambda (f args e tail)
    (and tail
         (and (>= (get c-this-params) 0)
              (tagcase f
                (e-var (n a b)
                  (and (symbol=? n (get c-this-name))
                       (let ((l (c-find e n)))
                         (and (not (null? l))
                              (and (c-this-loc? (car l) (get c-this-loc)) (= (+ (get c-this-added) (c-count-exps args)) (get c-this-params)))))))
                (else y #f))))))

;; Into the parameters' slots, from `i` down to `lo` (those below, a
;; lifting's, passed on as they are).
(define c-loop-stores (subr (maxeff (read @globals) (read @k) (write @k) (alloc @k)) (code int int) unit)
  (lambda (c i lo) (if (< i lo) #u (begin (c-op1 c routine-slot! (wcell-int i)) (c-loop-stores c (- i 1) lo)))))
(define c-drops (subr (maxeff (read @globals) (read @k) (write @k) (alloc @k)) (code int) unit)
  (lambda (c k) (if (<= k 0) #u (begin (c-op c routine-drop) (c-drops c (- k 1))))))

;; How many arguments a standard operation takes, or -1 if it is not one.
(define c-arity (subr (read (globals standard-primitive)) (string) int)
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
               (string=? n "string-append") (string=? n "string=?") (string=? n "symbol=?") (string=? n "wglobal=?") (string=? n "array-ref")
               (string=? n "string-ref") (string=? n "make-array") (string=? n "abort-current-continuation")
               (string=? n "call-with-composable-continuation") (string=? n "first-mark") (string=? n "marks-of"))
           2)
          ;; The rest: the arity of the runtime primitive it runs as, if that
          ;; takes a fixed number (`char-downcase`).
          (else
           (let ((p (standard-primitive n)))
             (if (or (string=? p "") (string=? p "%fx26-identity")) -1 (runtime-primitive-arity p)))))))

(define c-standard-on (subr compiles (string int code) unit)
  (lambda (name n c)
      (cond ((string=? name "+") (c-op c routine-int-add))
            ((string=? name "-") (c-op c routine-int-sub))
            ((string=? name "<") (c-op c routine-int-less))
            ((string=? name ">") (begin (c-op c routine-swap) (c-op c routine-int-less)))
            ((string=? name "<=") (begin (c-op c routine-swap) (c-op c routine-int-less) (c-lit c (wcell-bool #f)) (c-op c routine-eq)))
            ((string=? name ">=") (begin (c-op c routine-int-less) (c-lit c (wcell-bool #f)) (c-op c routine-eq)))
            ;; Characters are immediates, so compared as symbols are.
            ((or (string=? name "=") (or (string=? name "symbol=?") (string=? name "wglobal=?")) (string=? name "char=?")) (c-op c routine-eq))
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
            ((or (string=? name "modulo") (string=? name "quotient")
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
(define c-standard-value (subr (maxeff compiles spin) (string code) unit)
  (lambda (name c)
    (let ((n (c-arity name)) (body (the code (new nil))))
      (if (< n 0)
          (c-fail (string-append "not yet compiled as a value: " name))
          (begin
            (letrec ((params (subr (maxeff (read @globals) (read @k) (write @k) (alloc @k) spin) (int) unit)
                       (lambda (i) (if (= i n) #u (begin (c-op1 body routine-slot (wcell-int i)) (params (+ i 1)))))))
              (if (string=? name "make-array")
                  (begin (c-int body 0) (params 0) (c-prim body "%make-bloblet-filled" 3))
                  (begin (params 0) (c-standard-on name n body))))
            (c-op body routine-return)
            (let ((w (c-assemble body (string->symbol name))))
              (begin
                ;; Register code too, for the native compiler to start from.
                (if (get c-registers)
                    (let ((cells ((get c-standard-register-code) name n)))
                      (if (null? cells) #u (begin (set-register-twin w cells) #u)))
                    #u)
                (c-op1 c routine-closure (wcell-word w))))
            (c-emit c (i-cell (wcell-int 0))))))))

(define c-count-names (subr (read @globals) (names) int)
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
