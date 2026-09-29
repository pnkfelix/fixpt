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
            ;; `(apply f xs)`: `f` is a `vsubr`, a closure of `%vlambda`'s over the
;; procedure of one list, free value 0; that procedure, called with `xs`.
((string=? name "apply")
 (begin (c-op c routine-swap) (c-op1 c routine-field (wcell-int cellular-closure-free0)) (c-op1 c routine-tcall (wcell-int 1))))
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
