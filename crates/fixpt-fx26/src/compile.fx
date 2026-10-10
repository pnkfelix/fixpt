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

;; Its types, those it uses of the files before it, and the signatures of
;; what it is given.
(let* ((compile-types (load-module "fx26:compile-types.fx"))
       (parser-types ((proj (load-module "fx26:parser-types.fx") @s @e @m @c @p)))
       (check-env-types (load-module "fx26:check-env-types.fx"))
       (check-types-types (load-module "fx26:check-types-types.fx"))
       (table-types (load-module "fx26:table-types.fx"))
       (layout-types (load-module "fx26:layout-types.fx"))
       (check-resolve-types (load-module "fx26:check-resolve-types.fx")))
  ;; What it is given: the modules of the files before it that it uses.
  (lambda ((layout (select layout-types layout-sig))
           (check-resolve (select check-resolve-types check-resolve-sig))
           (check-env (select check-env-types check-env-sig))
           (tables (select table-types tables-sig))
           ;; The parser's module, for where loaded files' places begin.
           (parser (moduleof (val load-base int))))
    (module
(define-effect c-builds (select compile-types c-builds))
(define-effect c-walks (select compile-types c-walks))
(define-effect c-emits (select compile-types c-emits))
(define-effect compiles (select compile-types compiles))
(define-type c-params (select compile-types c-params))
(define-type c-binds (select compile-types c-binds))
(define-type c-recs (select compile-types c-recs))
(define-type c-cases (select compile-types c-cases))
(define-type exps (select compile-types exps))
(define-type c-span (select compile-types c-span))
(define-type c-spans (select compile-types c-spans))
(define-type c-lift (select compile-types c-lift))
(define-type c-lifting (select compile-types c-lifting))
(define-type c-ends (select compile-types c-ends))
(define-type c-with-table (select compile-types c-with-table))
(define-type c-with-names (select compile-types c-with-names))
(define-type item (select compile-types item))
(define i-cell (with compile-types i-cell))
(define i-label (with compile-types i-label))
(define i-branch (with compile-types i-branch))
(define i-zbranch (with compile-types i-zbranch))
(define-type items (select compile-types items))
(define-type code (select compile-types code))
(define-type cresult (select compile-types cresult))
(define c-ok (with compile-types c-ok))
(define c-err (with compile-types c-err))
(define-type c-places (select compile-types c-places))
(define-type loc (select compile-types loc))
(define at-slot (with compile-types at-slot))
(define at-free (with compile-types at-free))
(define at-global (with compile-types at-global))
(define at-pending (with compile-types at-pending))
(define at-loop (with compile-types at-loop))
(define at-lifted (with compile-types at-lifted))
(define-type cenv (select compile-types cenv))
(define-type c-found (select compile-types c-found))
(define-type c-this (select compile-types c-this))
(define-type c-globals-made (select compile-types c-globals-made))
(define-type syms (select compile-types syms))
(define-type c-join-answer (select compile-types c-join-answer))
(define-type c-standard-word (select compile-types c-standard-word))
(define-type c-spec-copy (select compile-types c-spec-copy))
(define-type c-spec-copies (select compile-types c-spec-copies))
(define-type patches (select compile-types patches))
;; The types it uses of the files before it.
(define e-app (with parser-types e-app))
(define e-begin (with parser-types e-begin))
(define e-bloblet (with parser-types e-bloblet))
(define e-convention (with parser-types e-convention))
(define e-extract (with parser-types e-extract))
(define e-if (with parser-types e-if))
(define e-lambda (with parser-types e-lambda))
(define e-let (with parser-types e-let))
(define e-letrec (with parser-types e-letrec))
(define e-letregion (with parser-types e-letregion))
(define e-module (with parser-types e-module))
(define e-plambda (with parser-types e-plambda))
(define e-product (with parser-types e-product))
(define e-proj (with parser-types e-proj))
(define e-prompt (with parser-types e-prompt))
(define e-rlambda (with parser-types e-rlambda))
(define e-sum (with parser-types e-sum))
(define e-tagcase (with parser-types e-tagcase))
(define e-the (with parser-types e-the))
(define e-var (with parser-types e-var))
(define e-with (with parser-types e-with))
(define-type exp (select parser-types exp))
(define-type mod-items (select parser-types mod-items))
(define-type names (select parser-types names))
(define-type syn (select parser-types syn))
(define-type k-facts (select check-env-types k-facts))
(define-type k-reshape-list (select check-env-types k-reshape-list))
(define-type k-with-list (select check-env-types k-with-list))
(define-type k-ids (select check-types-types k-ids))
(define-type table (select table-types table))
;; What it uses of the modules it is given.
(define load-base (with parser load-base))
(define cellular-closure-free0 (with layout cellular-closure-free0))
(define routine-branch (with layout routine-branch))
(define routine-drop (with layout routine-drop))
(define routine-field (with layout routine-field))
(define routine-field-set (with layout routine-field-set))
(define routine-free (with layout routine-free))
(define routine-global (with layout routine-global))
(define routine-lit (with layout routine-lit))
(define routine-prim (with layout routine-prim))
(define routine-return (with layout routine-return))
(define routine-slot (with layout routine-slot))
(define routine-slot! (with layout routine-slot!))
(define routine-zbranch (with layout routine-zbranch))
(define exp-end (with check-resolve exp-end))
(define exp-start (with check-resolve exp-start))
(define k-reshapes (with check-env k-reshapes))
(define k-with-vals (with check-env k-with-vals))
(define make-table (with tables make-table))
(define symbol-hash (with tables symbol-hash))
(define table-ref (with tables table-ref))
(define table-set! (with tables table-set!))

;; Whether `name` is an equality of the same word, as `eq` does it: of characters, symbols or
;; globals, `bool=?`, or `eq?`, identity. (`=`, of ints, which may be bignums, is `int-eq`'s.)
(define std-eq-name? (subr pure (string) bool)
  (lambda (n)
    (or (string=? n "char=?") (string=? n "symbol=?") (string=? n "wglobal=?")
        (string=? n "eq?") (string=? n "bool=?"))))

;; The checker's facts for the program being compiled.
(define c-facts (ref k-facts @k) (new nil))

;; The same, by where each `extract` starts (two cannot start at one place):
;; where it ends, and its field. A table, so that a program's facts are not
;; searched from the start for each `extract` compiled.
(define c-int-hash (subr pure (int) int) (lambda (a) a))

(define c-int=? (subr pure (int int) bool) (lambda (a b) (= a b)))

(define c-fact-table (ref c-spans @k) (new (make-table c-int-hash c-int=?)))

;; The procedures lambda-lifted, by index; and, by where each `letrec` is
;; (`c-span-key`), its members' (none if it is not lifted), so that its
;; register code lifts it as its stack code did, with the same words.
(define c-lifts (ref (table int c-lift @k) @k) (new (make-table c-int-hash c-int=?)))

(define c-lift-count (ref int @k) (new 0))

(define c-lifted (ref (table int c-lifting @k) @k) (new (make-table c-int-hash c-int=?)))

;; The parameters a lifting added to the lambda about to be compiled.
(define c-lifting-added (ref int @k) (new 0))

(define c-summary-table (ref (table int c-ends @k) @k) (new (make-table c-int-hash c-int=?)))

;; Each procedure converted to a convention (`k-convert-at`), by where it
;; starts: where it ends, and what `%fx26-convert` is given for it.
(define c-convert-table (ref c-spans @k) (new (make-table c-int-hash c-int=?)))

(define c-no-conversion c-span (cons -1 -1))

;; What `%fx26-convert` is given for `x`, if it is converted; or -1.
(define c-conversion-at (subr (maxeff (read @globals) (read @k)) (exp) int)
  (lambda (x)
    (let ((e (table-ref (get c-convert-table) (exp-start x) c-no-conversion)))
      (if (= (car e) (exp-end x)) (cdr e) -1))))

;; Each `apply` whose list the checker found at `acyclic` (the fact -500,
;; `k-note-apply-shares`), by where it starts: where it ends. Every other
;; `apply` copies its list.
(define c-shares-table (ref c-spans @k) (new (make-table c-int-hash c-int=?)))
;; Each definition's value that is a list nothing writes (the fact -501,
;; `k-note-frozen-define`), by where it starts: where it ends.
(define c-frozen-table (ref c-spans @k) (new (make-table c-int-hash c-int=?)))
;; Each `(with #%fx n)` that is the plain `n` (the fact -502, `k-synth-fx`).
(define c-plain-table (ref c-spans @k) (new (make-table c-int-hash c-int=?)))
(define c-plain-fx-at (subr (maxeff (read @globals) (read @k)) (int int) bool)
  (lambda (a b) (= (car (table-ref (get c-plain-table) a c-no-conversion)) b)))
;; Whether the definition's value from `a` to `b` is such a list.
(define c-frozen-define-at (subr (maxeff (read @globals) (read @k)) (int int) bool)
  (lambda (a b) (= (car (table-ref (get c-frozen-table) a c-no-conversion)) b)))

;; Whether the `apply` from `a` to `b` may give its list itself.
(define c-apply-shares-at (subr (maxeff (read @globals) (read @k)) (int int) bool)
  (lambda (a b) (= (car (table-ref (get c-shares-table) a c-no-conversion)) b)))

;; The field of the `extract` from `a` to `b`, or -1.
(define c-field-at (subr c-builds (int int) int)
  (lambda (a b)
    (let ((e (table-ref (get c-fact-table) a (the c-span (cons -1 -1)))))
      (if (= (car e) b) (cdr e) -1))))

;; Each `with` the checker saw (its `k-with-vals`, as `c-set-facts!` took
;; them): where it starts and ends, and its module's values' names, in
;; order.
;; And each module reshaped (`k-reshapes`), as `c-set-facts!` took them, by
;; where it starts: a module given through a signature is reshaped, so
;; there are many, and every expression is asked after (`c-changed?`).
(define c-reshape-index (ref (table int k-reshape-list @k) @k)
  (new (make-table c-int-hash c-int=?)))
(define c-index-reshapes! (subr c-emits (k-reshape-list) unit)
  (lambda (rs)
    (if (null? rs)
        #u
        (let ((a (extract (car rs) 1)))
          (begin (c-index-reshapes! (cdr rs))
                 (table-set! (get c-reshape-index) a
                             (the k-reshape-list
                               (cons (car rs) (table-ref (get c-reshape-index) a nil)))))))))
(define c-reshapes-from (subr (maxeff (read @globals) (read @k)) (int) k-reshape-list)
  (lambda (a) (table-ref (get c-reshape-index) a nil)))
(define c-withs (ref k-with-list @k) (new nil))
(define c-with-index (ref c-with-table @k) (new (make-table c-int-hash c-int=?)))
(define c-index-withs! (subr c-emits (k-with-list) unit)
  (lambda (ws)
    (if (null? ws)
        #u
        (let ((a (extract (car ws) 1)))
          (begin (c-index-withs! (cdr ws))
                 (table-set! (get c-with-index) a
                             (the k-with-list
                               (cons (car ws) (table-ref (get c-with-index) a nil)))))))))
(define c-with-in
  (subr (maxeff (read @globals) (read @k) (alloc @k)) (k-with-list int int) c-with-names)
  (lambda (ws a b)
    (cond ((null? ws) nil)
          ((and (= (extract (car ws) 1) a) (= (extract (car ws) 2) b))
           (the c-with-names (cons (extract (car ws) 3) nil)))
          (else (c-with-in (cdr ws) a b)))))
;; The values' names of the `with` from `a` to `b`, in a list of one; none
;; if the checker did not see it.
(define c-with-at (subr (maxeff (read @globals) (read @k) (alloc @k)) (int int) c-with-names)
  (lambda (a b) (c-with-in (table-ref (get c-with-index) a nil) a b)))
;; Their positions in the module, likewise.
(define c-with-places-in
  (subr (maxeff (read @globals) (read @k) (alloc @k)) (k-with-list int int) (listof k-ids @k))
  (lambda (ws a b)
    (cond ((null? ws) nil)
          ((and (= (extract (car ws) 1) a) (= (extract (car ws) 2) b))
           (the (listof k-ids @k) (cons (extract (car ws) 4) nil)))
          (else (c-with-places-in (cdr ws) a b)))))
(define c-with-places-at
  (subr (maxeff (read @globals) (read @k) (alloc @k)) (int int) (listof k-ids @k))
  (lambda (a b) (c-with-places-in (table-ref (get c-with-index) a nil) a b)))
;; The positions of the values a module reshaped from `a` to `b` keeps, in
;; a list of one; none if it is not reshaped.
(define c-reshape-in
  (subr (maxeff (read @globals) (read @k) (alloc @k)) (k-reshape-list int int) (listof k-ids @k))
  (lambda (rs a b)
    (cond ((null? rs) nil)
          ((and (= (extract (car rs) 1) a) (= (extract (car rs) 2) b))
           (the (listof k-ids @k) (cons (extract (car rs) 3) nil)))
          (else (c-reshape-in (cdr rs) a b)))))
(define c-reshape-at (subr (maxeff (read @globals) (read @k) (alloc @k)) (exp) (listof k-ids @k))
  (lambda (x) (c-reshape-in (c-reshapes-from (exp-start x)) (exp-start x) (exp-end x))))
;; Whether one of `rs` reshapes the module from `a` to `b`.
(define c-reshaped-in? (subr (maxeff (read @globals) (read @k)) (k-reshape-list int int) bool)
  (lambda (rs a b)
    (and (not (null? rs))
         (or (and (= (extract (car rs) 1) a) (= (extract (car rs) 2) b))
             (c-reshaped-in? (cdr rs) a b)))))
;; Whether the module `x` is reshaped.
(define c-reshaped-at? (subr (maxeff (read @globals) (read @k)) (exp) bool)
  (lambda (x) (c-reshaped-in? (c-reshapes-from (exp-start x)) (exp-start x) (exp-end x))))
;; Whether `x`'s value is changed as it is given: converted to a
;; convention, or a module reshaped.
(define c-changed? (subr (maxeff (read @globals) (read @k)) (exp) bool)
  (lambda (x)
    (or (>= (c-conversion-at x) 0) (c-reshaped-at? x))))
;; Where an expression starting at `at` is, as a word's name says it: the
;; position; or, in a module's file (`load-module`, M7), `file:position`,
;; the file numbered as the Rust checker numbers them.
(define c-place-name (subr (read @globals) (int) string)
  (lambda (at)
    (if (< at load-base)
        (int->string at)
        (string-append (int->string (+ 1000 (quotient at load-base)))
                       (string-append ":" (int->string (remainder at load-base)))))))
;; An abstract type `n`'s conversion, `prefix` `up-` or `down-`.
(define c-converter (subr (read @globals) (string symbol) symbol)
  (lambda (prefix n) (string->symbol (string-append prefix (symbol->string n)))))

(define c-tag (prompt-tag cresult cresult (maxeff c-emits (read @t) spin) @y)
  (make-continuation-prompt-tag))

(define c-fail (subr compiles (string) void)
  (lambda (message) (abort-current-continuation c-tag (c-err message))))

(define c-labels (ref int @k) (new 0))

(define c-fresh (subr (maxeff (read @globals) (read @k) (write @k)) () int)
  (lambda () (let ((n (get c-labels))) (begin (set c-labels (+ n 1)) n))))

(define c-emit (subr (maxeff (read @k) (write @k) (alloc @k)) (code item) unit)
  (lambda (c i) (set c (cons i (get c)))))

(define c-op (subr c-emits (code int) unit)
  (lambda (c r) (c-emit c (i-cell (wcell-routine r)))))

(define c-op1 (subr c-emits (code int wcell) unit)
  (lambda (c r x) (begin (c-op c r) (c-emit c (i-cell x)))))

(define c-lit (subr c-emits (code wcell) unit)
  (lambda (c x) (c-op1 c routine-lit x)))

(define c-int (subr c-emits (code int) unit)
  (lambda (c n) (c-lit c (wcell-int n))))

;; Field `k` of a bloblet whose type says it has one.
(define c-field (subr c-emits (code int) unit)
  (lambda (c k) (c-op1 c routine-field (wcell-int k))))

;; Field `k` of the bloblet on top set to the value under it.
(define c-field-set (subr c-emits (code int) unit)
  (lambda (c k) (begin (c-int c k) (c-op c routine-field-set))))

;; A runtime primitive with `n` arguments.
(define c-prim (subr compiles (code string int) unit)
  (lambda (c name n)
    (let ((p (runtime-primitive name)))
      (if (< p 0)
          (c-fail (string-append "no runtime primitive " name))
          (begin (c-op1 c routine-prim (wcell-int p)) (c-emit c (i-cell (wcell-int n))))))))

;; Drop what a mutator left, and leave FX-26's unit value instead.
(define c-unit-after (subr c-emits (code) unit)
  (lambda (c) (begin (c-op c routine-drop) (c-lit c (wcell-unit)))))

;;; ----------------------------------------------------------- assembling

(define c-reverse (subr c-walks (items items) items)
  (lambda (xs acc) (if (null? xs) acc (c-reverse (cdr xs) (cons (car xs) acc)))))

(define c-size (subr pure (item) int)
  (lambda (i) (tagcase i (i-cell (x) 1) (i-label (n) 0) (i-branch (n) 2) (i-zbranch (n) 2))))

;; Where each label is, in cells; and how many cells there are.
(define c-place (subr (maxeff (read @globals) (read @k) (write @k) spin) (items c-places int) int)
  (lambda (xs at pos)
    (if (null? xs)
        pos
        (begin (tagcase (car xs) (i-label (n) (array-set! at n pos)) (else x #u))
               (c-place (cdr xs) at (+ pos (c-size (car xs))))))))

;; A branch by routine `r`, its two cells at `pos`, to `to`, onto `acc`:
;; its offset counts from the cell after it.
(define c-branch-cells (subr c-builds (int int int (listof wcell @k)) (listof wcell @k))
  (lambda (r to pos acc) (cons (wcell-routine r) (cons (wcell-int (- to (+ pos 2))) acc))))

;; The cells, branches resolved (an offset counts from the cell after it):
;; from the items newest first, each ending at `end`, onto those after it,
;; in a loop, however long the word.
(define c-cells (subr c-walks (items c-places int (listof wcell @k)) (listof wcell @k))
  (lambda (xs at end acc)
    (if (null? xs)
        acc
        (let ((pos (- end (c-size (car xs)))))
          (c-cells (cdr xs) at pos
                   (tagcase (car xs)
                     (i-cell (x) (cons x acc))
                     (i-label (n) acc)
                     (i-branch (n) (c-branch-cells routine-branch (array-ref at n) pos acc))
                     (i-zbranch (n) (c-branch-cells routine-zbranch (array-ref at n) pos acc))))))))

(define c-assemble (subr (maxeff c-emits spin) (code symbol) tword)
  (lambda (c name)
    (let* ((at (the c-places (make-array (get c-labels) 0)))
           (end (c-place (c-reverse (get c) nil) at 0)))
      (make-word name (c-cells (get c) at end nil)))))

;; `e` with `n` bound at `l`, innermost.
(define c-extend (subr (alloc @k) (symbol loc cenv) cenv)
  (lambda (n l e) (cons (cons n l) e)))

(define c-loop? (subr pure (loc) bool)
  (lambda (l) (tagcase l (at-loop (z) #t) (else y #f))))

(define c-global? (subr pure (loc) bool)
  (lambda (l) (tagcase l (at-global (g) #t) (else y #f))))

(define c-lifted? (subr pure (loc) bool)
  (lambda (l) (tagcase l (at-lifted (k) #t) (else y #f))))

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

;; Whether each lambda also gets register code (PLAN.md 13h′), as its word's
;; twin, made after its form's words (`compile-twins.fx`).
(define c-registers (ref bool @k) (new #f))

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

(define c-genv-index (ref (table symbol c-globals-made @k) @k)
  (new (make-table symbol-hash symbol=?)))

(define c-genv-count (ref int @k) (new 0))

(define c-genv (ref int @k) (new -1))

;; The globals seen now, as a count, for a body to see them so later.
(define c-genv-now (subr (maxeff (read @k) (read (globals c-genv c-genv-count))) () int)
  (lambda () (if (< (get c-genv) 0) (get c-genv-count) (get c-genv))))

(define c-global-first (subr c-builds (c-globals-made int) c-found)
  (lambda (es limit)
    (cond ((null? es) nil)
          ((or (< limit 0) (< (car (car es)) limit)) (the c-found (cons (cdr (car es)) nil)))
          (else (c-global-first (cdr es) limit)))))

;; `n`'s newest global before the `limit`th (-1: any), in a list.
(define c-global-find (subr c-builds (symbol int) c-found)
  (lambda (n limit) (c-global-first (table-ref (get c-genv-index) n nil) limit)))

;; `n`'s global `g`, the `i`th made, as its newest.
(define c-genv-push! (subr c-emits (symbol int wglobal) unit)
  (lambda (n i g)
    (let ((made (the (pairof int loc @k) (cons i (at-global g)))))
      (table-set! (get c-genv-index) n
                  (the c-globals-made (cons made (table-ref (get c-genv-index) n nil)))))))

(define c-find (subr c-walks (cenv symbol) c-found)
  (lambda (e n)
    (cond ((null? e) nil)
          ((symbol=? (car (car e)) n) (the c-found (cons (cdr (car e)) nil)))
          (else (c-find (cdr e) n)))))

;; Where `n` is: in the locals, else in the globals; none means standard.
(define c-where (subr c-walks (cenv symbol) c-found)
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

(define c-join-memo (ref (table int c-join-answer @k) @k) (new (make-table c-int-hash c-int=?)))
(define c-standard-words (ref (listof c-standard-word @k) @k) (new nil))
(define c-spec-made (ref (table int c-spec-copies @k) @k) (new (make-table c-int-hash c-int=?)))

;; `es` with span end `b`'s summary at least `s`.
(define c-end-max (subr c-builds (c-ends int int) c-ends)
  (lambda (es b s)
    (cond ((null? es) (the c-ends (cons (the c-span (cons b s)) nil)))
          ((= (car (car es)) b)
           (let ((had (cdr (car es))))
             (the c-ends (cons (the c-span (cons b (if (> s had) s had))) (cdr es)))))
          (else (the c-ends (cons (car es) (c-end-max (cdr es) b s)))))))

(define c-fill-facts (subr (maxeff c-emits (read @t)) (k-facts) unit)
  (lambda (fs)
    (if (null? fs)
        #u
        (let ((a (extract (car fs) 1)) (b (extract (car fs) 2)) (n (extract (car fs) 3)))
          (begin
            (cond ((>= n 0) (table-set! (get c-fact-table) a (the c-span (cons b n))))
                  ((= n -500) (table-set! (get c-shares-table) a (the c-span (cons b 0))))
                  ((= n -501) (table-set! (get c-frozen-table) a (the c-span (cons b 0))))
                  ((= n -502) (table-set! (get c-plain-table) a (the c-span (cons b 0))))
                  ;; A conversion, -1000 - code (`k-convert-at`).
                  ((<= n -1000)
                   (table-set! (get c-convert-table) a (the c-span (cons b (- -1000 n)))))
                  ;; An effect summary, -1 - s: the greatest, per span.
                  (else
                   (let ((s (- -1 n)) (known (table-ref (get c-summary-table) a (the c-ends nil))))
                     (table-set! (get c-summary-table) a (c-end-max known b s)))))
            (c-fill-facts (cdr fs)))))))

(define c-end-summary (subr (maxeff (read @globals) (read @k)) (c-ends int) int)
  (lambda (es b)
    (cond ((null? es) 3)
          ((= (car (car es)) b) (cdr (car es)))
          (else (c-end-summary (cdr es) b)))))

;; The effect summary of the expression from `a` to `b` (3, the most, if
;; none was noted: `checked-extracts`).
(define c-summary-at (subr (maxeff (read @globals) (read @k)) (int int) int)
  (lambda (a b) (c-end-summary (table-ref (get c-summary-table) a (the c-ends nil)) b)))

;; `c-facts` into `c-fact-table`.
(define c-set-facts! (subr (maxeff c-emits (read @t)) (k-facts) unit)
  (lambda (fs)
    (begin
      (set c-facts fs)
      (set c-fact-table (make-table c-int-hash c-int=?))
      (set c-convert-table (make-table c-int-hash c-int=?))
      (set c-shares-table (make-table c-int-hash c-int=?))
      (set c-frozen-table (make-table c-int-hash c-int=?))
      (set c-plain-table (make-table c-int-hash c-int=?))
      (set c-summary-table (make-table c-int-hash c-int=?))
      (set c-join-memo (make-table c-int-hash c-int=?))
      (set c-spec-made (make-table c-int-hash c-int=?))
      (set c-standard-words nil)
      (set c-lifts (make-table c-int-hash c-int=?))
      (set c-lift-count 0)
      (set c-lifted (make-table c-int-hash c-int=?))
      (set c-withs (get k-with-vals))
      (set c-with-index (make-table c-int-hash c-int=?))
      (c-index-withs! (get k-with-vals))
      (set c-reshape-index (make-table c-int-hash c-int=?))
      (c-index-reshapes! (get k-reshapes))
      (c-fill-facts fs))))

(define c-member? (subr (maxeff (read @globals) (read @k)) (syms symbol) bool)
  (lambda (xs n) (and (not (null? xs)) (or (symbol=? (car xs) n) (c-member? (cdr xs) n)))))

(define c-adjoin (subr c-builds (syms symbol) syms)
  (lambda (xs n) (if (c-member? xs n) xs (cons n xs))))

(define c-bind-params (subr c-builds (c-params syms) syms)
  (lambda (ps bound)
    (if (null? ps) bound (c-bind-params (cdr ps) (cons (extract (car ps) 1) bound)))))

(define c-bind-letrec (subr c-builds (c-recs syms) syms)
  (lambda (bs bound)
    (if (null? bs) bound (c-bind-letrec (cdr bs) (cons (extract (car bs) 1) bound)))))

(define c-bind-let (subr c-builds (c-binds syms) syms)
  (lambda (bs bound)
    (if (null? bs) bound (c-bind-let (cdr bs) (cons (extract (car bs) 1) bound)))))

(define c-names (subr c-builds (names syms) syms)
  (lambda (ns bound) (if (null? ns) bound (c-names (cdr ns) (cons (car ns) bound)))))

;; Every name a module's `items` define, onto `bound`: an abstract type's
;; conversions, a definition's, a `define-rec`'s members'.
(define c-module-bound (subr c-builds (mod-items syms) syms)
  (lambda (items bound)
    (if (null? items)
        bound
        (let* ((it (car items)) (k (extract it 1)) (ns (extract it 2))
               (more (case k ((0)
                              (the syms (cons (c-converter "down-" (car ns))
                                              (cons (c-converter "up-" (car ns)) bound))))
                             ((2 3) (c-names ns bound))
                             (else bound))))
          (c-module-bound (cdr items) more)))))

;; The expressions `bs` binds, in order: a `let`'s values, or a product's
;; fields.
(define c-bound-exps (subr c-walks (c-binds) exps)
  (lambda (bs) (if (null? bs) nil (cons (extract (car bs) 2) (c-bound-exps (cdr bs))))))

;; The same for a `letrec`'s bindings.
(define c-rec-exps (subr c-walks (c-recs) exps)
  (lambda (bs) (if (null? bs) nil (cons (extract (car bs) 3) (c-rec-exps (cdr bs))))))

(define-rec
  (c-free-all (subr c-walks (exps syms syms) syms)
    (lambda (es bound acc)
      (if (null? es) acc (c-free-all (cdr es) bound (c-free (car es) bound acc)))))
  (c-free (subr c-walks (exp syms syms) syms)
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
            (c-free body inner (c-free-all (c-rec-exps bs) inner acc))))
        (e-let (bs body a b)
          (c-free body (c-bind-let bs bound) (c-free-all (c-bound-exps bs) bound acc)))
        (e-begin (es a b) (c-free-all es bound acc))
        (e-prompt (t body h a b) (c-free t bound (c-free body bound (c-free h bound acc))))
        (e-bloblet (op i args a b) (c-free-all args bound acc))
        (e-product (fs a b) (c-free-all (c-bound-exps fs) bound acc))
        (e-extract (p l a b) (c-free p bound acc))
        (e-sum (t v a b) (c-free v bound acc))
        (e-tagcase (s arms els a b)
          (c-free s bound (c-free-arms arms bound (c-free-else els bound acc))))
        ;; A module's items see all of them, as a `letrec*`'s.
        (e-module (items a b) (c-free-items items (c-module-bound items bound) acc))
        ;; The module, then the body, the module's values bound in it.
        (e-with (m body a b)
          (if (string=? (symbol->string m) "#%fx")
              acc
              (let ((ns (c-with-at a b)) (acc (if (c-member? bound m) acc (c-adjoin acc m))))
                (c-free body (if (null? ns) bound (c-names (car ns) bound)) acc))))
        (else y acc))))
  (c-free-items (subr c-walks (mod-items syms syms) syms)
    (lambda (items bound acc)
      (if (null? items)
          acc
          (let ((k (extract (car items) 1)))
            (c-free-items (cdr items) bound
                          (if (or (= k 0) (= k 2) (= k 3))
                              (c-free-all (extract (car items) 4) bound acc)
                              acc))))))
  (c-free-arms
    (subr c-walks (c-cases syms syms) syms)
    (lambda (arms bound acc)
      (if (null? arms)
          acc
          (let ((inner (c-names (extract (car arms) 3) bound)))
            (c-free-arms (cdr arms) bound (c-free (extract (car arms) 4) inner acc))))))
  (c-free-else (subr c-walks (c-binds syms syms) syms)
    (lambda (els bound acc)
      (if (null? els) acc (c-free (extract (car els) 2) (cons (extract (car els) 1) bound) acc)))))

;; What is left when the value is in hand: `return` in tail position.
(define c-done (subr c-emits (code bool) unit)
  (lambda (c tail) (if tail (c-op c routine-return) #u)))

;; After a body whose value is on top of `n` values bound from `slot`
;; up: the value into `slot`, the others dropped. Nothing in tail
;; position, where `return` drops the whole frame.
(define c-unbind (subr (maxeff c-emits spin) (code int int bool) unit)
  (lambda (c slot n tail)
    (if (or tail (= n 0))
        #u
        (letrec ((drops (subr (maxeff c-emits spin) (int) unit)
                   (lambda (k) (if (= k 0) #u (begin (c-op c routine-drop) (drops (- k 1)))))))
          (begin (c-op1 c routine-slot! (wcell-int slot)) (drops (- n 1)))))))

(define c-count-let (subr (read @globals) (c-binds) int)
  (lambda (bs) (if (null? bs) 0 (+ 1 (c-count-let (cdr bs))))))

(define c-letrec-slots (subr (maxeff (read @globals) (alloc @k)) (c-recs cenv int) cenv)
  (lambda (bs e d)
    (if (null? bs)
        e
        (c-letrec-slots (cdr bs) (c-extend (extract (car bs) 1) (at-slot d) e) (+ d 1)))))

(define c-patch-one (subr (maxeff compiles spin) (patches int int code) unit)
  (lambda (ps depth i c)
    (if (null? ps)
        #u
        (begin (c-op1 c routine-slot (wcell-int (cdr (car ps))))
               (c-op1 c routine-slot (wcell-int (+ depth i)))
               (c-field-set c (+ cellular-closure-free0 (car (car ps))))
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

(define c-count-exps (subr (read @globals) (exps) int)
  (lambda (es) (if (null? es) 0 (+ 1 (c-count-exps (cdr es))))))

(define c-count-params (subr (read @globals) (c-params) int)
  (lambda (ps) (if (null? ps) 0 (+ 1 (c-count-params (cdr ps))))))

;; Whether a parameter of `ps` is named `n`, which hides what else `n` names.
(define c-has-param? (subr c-builds (c-params symbol) bool)
  (lambda (ps n) (c-member? (c-bind-params ps nil) n)))

;; Parameters `ps` bound to `args`, as a `let` binds.
(define c-param-bindings (subr c-walks (c-params exps) c-binds)
  (lambda (ps args)
    (if (null? ps)
        nil
        (cons (product (1 (extract (car ps) 1)) (2 (car args)))
              (c-param-bindings (cdr ps) (cdr args))))))

;; A plain lambda (under forms that compile to nothing) applied at once to
;; as many arguments as it has parameters, as the Rust compiler's
;; `applied_lambda` finds it: the `let` it is, its bindings and body, in a
;; list of one; none if `f` is no such lambda.
(define c-applied-let (subr c-walks (exp exps) (listof (productof (1 c-binds) (2 exp)) @k))
  (lambda (f args)
    (let ((lam (c-lambda-of f)))
      (if (null? lam)
          nil
          (tagcase (car lam)
            (e-lambda (ps body a b)
              (if (= (c-count-params ps) (c-count-exps args))
                  (the (listof (productof (1 c-binds) (2 exp)) @k)
                    (cons (product (1 (c-param-bindings ps args)) (2 body)) nil))
                  nil))
            (else y nil))))))

(define c-mentions? (subr c-walks (exp symbol) bool)
  (lambda (x n) (c-member? (c-free x nil nil) n)))

;; Whether every use of `f` in `x` is a call with `n` arguments: where
;; `loops` asks, in tail position, which the compiler makes a loop; else in
;; any position, and in lambdas inside too, so that `f` is never a value.
(define-rec
  (c-calls-only (subr c-walks (exp symbol int bool bool) bool)
    (lambda (x f n tail loops)
      (tagcase x
        (e-var (m a b) (not (symbol=? m f)))
        (e-lambda (ps body a b) (or (c-has-param? ps f) (c-calls-only-inside body f n loops)))
        (e-app (fun args a b)
          (and (c-calls-only-all args f n loops)
               (tagcase fun
                 (e-var (m a2 b2)
                   (if (symbol=? m f) (and (or tail (not loops)) (= (c-count-exps args) n)) #t))
                 (else y (c-calls-only fun f n #f loops)))))
        (e-plambda (d body a b) (c-calls-only body f n tail loops))
        (e-letregion (k r i body a b) (or (symbol=? r f) (c-calls-only body f n #f loops)))
        (e-rlambda (r l a b) (and (c-calls-only r f n #f loops) (c-calls-only l f n #f loops)))
        (e-proj (body ds a b) (c-calls-only body f n tail loops))
        (e-the (d body a b) (c-calls-only body f n tail loops))
        (e-convention (cnv body a b) (c-calls-only body f n tail loops))
        (e-if (t th el a b)
          (and (c-calls-only t f n #f loops)
               (c-calls-only th f n tail loops)
               (c-calls-only el f n tail loops)))
        (e-letrec (bs body a b)
          (or (c-member? (c-bind-letrec bs nil) f)
              (and (c-calls-only-all (c-rec-exps bs) f n loops)
                   (c-calls-only body f n tail loops))))
        (e-let (bs body a b)
          (and (c-calls-only-all (c-bound-exps bs) f n loops)
               (or (c-member? (c-bind-let bs nil) f) (c-calls-only body f n tail loops))))
        (e-begin (es a b) (c-calls-only-begin es f n tail loops))
        (e-prompt (t body h a b)
          (and (c-calls-only t f n #f loops)
               (c-calls-only h f n #f loops)
               (c-calls-only-inside body f n loops)))
        (e-bloblet (op i args a b) (c-calls-only-all args f n loops))
        (e-product (fs a b) (c-calls-only-all (c-bound-exps fs) f n loops))
        (e-extract (p l a b) (c-calls-only p f n #f loops))
        (e-sum (t v a b) (c-calls-only v f n #f loops))
        (e-tagcase (s arms els a b)
          (and (c-calls-only s f n #f loops)
               (c-calls-only-arms arms f n tail loops)
               (c-calls-only-else els f n tail loops)))
        ;; Said of no module (as the Rust compiler's `loops_only` and
        ;; `called_only` say).
        (e-module (items a b) #f)
        (e-with (m body a b) #f)
        (else y #t))))
  ;; The same for the body of a lambda or a prompt in `x`: where `loops`
  ;; asks, no call there is in tail position, so it may not mention `f`.
  (c-calls-only-inside (subr c-walks (exp symbol int bool) bool)
    (lambda (x f n loops) (if loops (not (c-mentions? x f)) (c-calls-only x f n #f loops))))
  (c-calls-only-all (subr c-walks (exps symbol int bool) bool)
    (lambda (es f n loops)
      (or (null? es)
          (and (c-calls-only (car es) f n #f loops) (c-calls-only-all (cdr es) f n loops)))))
  (c-calls-only-begin (subr c-walks (exps symbol int bool bool) bool)
    (lambda (es f n tail loops)
      (cond ((null? es) #t)
            ((null? (cdr es)) (c-calls-only (car es) f n tail loops))
            (else (and (c-calls-only (car es) f n #f loops)
                       (c-calls-only-begin (cdr es) f n tail loops))))))
  (c-calls-only-arms
    (subr c-walks (c-cases symbol int bool bool) bool)
    (lambda (arms f n tail loops)
      (or (null? arms)
          (and (or (c-member? (extract (car arms) 3) f)
                   (c-calls-only (extract (car arms) 4) f n tail loops))
               (c-calls-only-arms (cdr arms) f n tail loops)))))
  (c-calls-only-else (subr c-walks (c-binds symbol int bool bool) bool)
    (lambda (els f n tail loops)
      (or (null? els)
          (symbol=? (extract (car els) 1) f)
          (c-calls-only (extract (car els) 2) f n tail loops)))))

;; Whether every use of `f` in `x` is a call with `n` arguments in tail
;; position, which the compiler makes a loop.
(define c-loops-only (subr c-walks (exp symbol int bool) bool)
  (lambda (x f n tail) (c-calls-only x f n tail #t)))

;; Whether every use of `f` in `x` is a call with `n` arguments, in any
;; position and in lambdas inside too: so it is never a value.
(define c-called-only (subr c-walks (exp symbol int) bool)
  (lambda (x f n) (c-calls-only x f n #f #f)))

;; Binding `i`'s scope while it is made: each sibling pending, and itself a
;; loop if it only calls itself in loops.
(define c-letrec-own
  (subr c-walks (c-recs cenv int int int exp int) cenv)
  (lambda (bs e depth k i body nps)
    (if (null? bs)
        e
        (let* ((g (extract (car bs) 1))
               (loops (and (= k i) (c-loops-only body g nps #t))))
          (c-letrec-own (cdr bs) (c-extend g (if loops (at-loop 0) (at-pending (+ depth k))) e)
                        depth (+ k 1) i body nps)))))

(define c-count-letrec (subr (read @globals) (c-recs) int)
  (lambda (bs) (if (null? bs) 0 (+ 1 (c-count-letrec (cdr bs))))))

(define c-length (subr (maxeff (read @globals) (read @k) spin) (syms) int)
  (lambda (xs) (if (null? xs) 0 (+ 1 (c-length (cdr xs))))))

(define c-nth-binding
  (subr (read @globals) (c-recs int) (productof (1 symbol) (2 syn) (3 exp)))
  (lambda (bs i) (if (= i 0) (car bs) (c-nth-binding (cdr bs) (- i 1)))))

;; Whether no binding of `bs` but the `i`th mentions `name`; `k` counts.
(define c-unmentioned? (subr c-walks (c-recs symbol int int) bool)
  (lambda (bs name i k)
    (or (null? bs)
        (and (or (= k i) (not (c-mentions? (extract (car bs) 3) name)))
             (c-unmentioned? (cdr bs) name i (+ k 1))))))

;; Whether `letrec` binding `i` of `bs` is a join point, as the Rust
;; compiler's `r_join_ok` says: a lambda whose body calls it only in tail
;; position, as the `letrec`'s body does, and that no sibling mentions; so
;; no closure of it need be made, and each call is a jump.
(define c-join-ok? (subr c-walks (c-recs exp int) bool)
  (lambda (bs body i)
    (let* ((b (c-nth-binding bs i)) (name (extract b 1)) (lam (c-lambda-of (extract b 3))))
      (and (not (null? lam))
           (tagcase (car lam)
             (e-lambda (ps lbody la lb)
               (let ((n (c-count-params ps)))
                 (and (not (c-has-param? ps name))
                      (c-loops-only lbody name n #t)
                      (c-loops-only body name n #t)
                      (c-unmentioned? bs name i 0))))
             (else y #f)))))))))
