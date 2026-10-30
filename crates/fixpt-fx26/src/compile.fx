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
(hide (include compile-types) (include parser-types) (include check-env-types)
      (include check-types-types))
;; The types it uses of the files before it.
(define-type table (select table-types table))
;; What it uses of the modules it is given.
(define load-base (with parser load-base))
;; What it uses of the modules it is given: all of each, hidden.
(hide (include layout) (include check-resolve) (include check-env) (include tables))

;; Whether `name` is an equality of the same word, as `eq` does it: of characters, symbols or
;; globals, `bool=?`, or `eq?`, identity. (`=`, of ints, which may be bignums, is `int-eq`'s.)
(define std-eq-name? (->* (string) bool)
  (lambda (n)
    (or (string=? n "char=?") (string=? n "symbol=?") (string=? n "wglobal=?")
        (string=? n "eq?") (string=? n "bool=?"))))

;; The checker's facts for the program being compiled.
(define c-facts (ref k-facts @k) (new nil))

;; The same, by expression (`k-at`, an expression's identity): each
;; `extract`'s field. A table, so that a program's facts are not searched
;; from the start for each `extract` compiled.
(define c-int-hash (subr pure (int) int) (lambda (a) a))

(define c-int=? (subr pure (int int) bool) (lambda (a b) (= a b)))

;; An expression's identity, as a table's key: where it starts and ends, and
;; which of the expressions there it is. For tables asked once a lambda or
;; a `letrec`; those asked of every expression are by where it starts
;; (`c-by-at`), so that asking makes nothing.
(define c-span-key (->* (int int int) k-at)
  (lambda (a b k) (product (1 a) (2 b) (3 k))))
(define c-at-hash (subr pure (k-at) int) (lambda (x) (extract x 1)))
(define c-at-is? (->* (k-at int int int) bool) (lambda (x a b k) (k-at-is? x a b k)))
(define c-at=? (subr pure (k-at k-at) bool)
  (lambda (x y) (k-at-is? x (extract y 1) (extract y 2) (extract y 3))))

;; What `t` notes of `a` `b` `k`, the newest; or `none`.
(define c-noted-in
  (->* ((listof c-noted acyclic) int int int int) int)
  (lambda (ns a b k none)
    (cond ((null? ns) none)
          ((k-at-is? (extract (car ns) 1) a b k) (extract (car ns) 2))
          (else (c-noted-in (cdr ns) a b k none)))))
(define c-noted-at (->* (c-by-at int int int int) int)
  (lambda (t a b k none) (c-noted-in (table-ref t a nil) a b k none)))
;; The same of expression `x`: where it ends, and which it is there, found
;; only if something is noted where it starts, as little is.
(define c-noted-of (->* (c-by-at exp int) int)
  (lambda (t x none)
    (let ((ns (table-ref t (exp-start x) nil)))
      (if (null? ns) none (c-noted-in ns (exp-start x) (exp-end x) (exp-kth x) none)))))
;; `t` noting `n` of `at`, over what it noted before.
(define c-note! (->* (c-by-at k-at int) unit)
  (lambda (t at n)
    (let ((a (extract at 1)))
      (table-set! t a (the (listof c-noted acyclic)
                        (cons (product (1 at) (2 n)) (table-ref t a nil)))))))
(define c-new-by-at (subr (alloc @k) () c-by-at) (lambda () (make-table c-int-hash c-int=?)))

(define c-fact-table (ref c-datums-at @k) (new (make-table c-int-hash c-int=?)))

;; The procedures lambda-lifted, by index; and, by where each `letrec` is
;; (`c-span-key`), its members' (none if it is not lifted), so that its
;; register code lifts it as its stack code did, with the same words.
(define c-lifts (ref (table int c-lift @k) @k) (new (make-table c-int-hash c-int=?)))

(define c-lift-count (ref int @k) (new 0))

(define c-lifted (ref (table k-at c-lifting @k) @k) (new (make-table c-at-hash c-at=?)))

;; The parameters a lifting added to the lambda about to be compiled.
(define c-lifting-added (ref int @k) (new 0))

;; Each expression's effect summary, the greatest noted of it.
(define c-summary-table (ref c-by-at @k) (new (c-new-by-at)))

;; Each procedure converted to a convention (`k-convert-at`): what
;; `%fx26-convert` is given for it.
(define c-convert-table (ref c-by-at @k) (new (c-new-by-at)))

;; What `%fx26-convert` is given for `x`, if it is converted; or -1.
(define c-conversion-at (->* (exp) int)
  (lambda (x) (c-noted-of (get c-convert-table) x -1)))

;; Each `stage`'s code, few (`n-staged`); what `x` is checked against, if
;; it is one: a list of one.
(define c-staged-texts (ref c-staged-list @k) (new nil))
(define c-staged-at (->* (exp) c-staged-list)
  (lambda (x) (c-staged-find (get c-staged-texts) (exp-start x) (exp-end x) (exp-kth x))))
(define c-staged-find (->* (c-staged-list int int int) c-staged-list)
  (lambda (l a b k)
    (cond ((null? l) nil)
          ((c-at-is? (extract (car l) 1) a b k) (the c-staged-list (cons (car l) nil)))
          (else (c-staged-find (cdr l) a b k)))))
;; Each `apply` whose list the checker found at `acyclic` (`n-apply-shares`,
;; `k-note-apply-shares`). Every other `apply` copies its list.
(define c-shares-table (ref c-by-at @k) (new (c-new-by-at)))
;; Each definition's value that is a list nothing writes (`n-frozen-define`,
;; `k-note-frozen-define`).
(define c-frozen-table (ref c-by-at @k) (new (c-new-by-at)))
;; Each `(with #%fx n)` that is the plain `n` (`n-plain-fx`, `k-synth-fx`).
(define c-plain-table (ref c-by-at @k) (new (c-new-by-at)))
(define c-plain-fx-at (->* (int int int) bool)
  (lambda (a b k) (>= (c-noted-at (get c-plain-table) a b k -1) 0)))
;; Whether the definition's value `a` `b` `k` is such a list.
(define c-frozen-define-at (->* (int int int) bool)
  (lambda (a b k) (>= (c-noted-at (get c-frozen-table) a b k -1) 0)))

;; Whether the `apply` `a` `b` `k` may give its list itself.
(define c-apply-shares-at (->* (int int int) bool)
  (lambda (a b k) (>= (c-noted-at (get c-shares-table) a b k -1) 0)))

;; Each call's callee's convention (`n-call`), by where it starts.
(define c-call-table (ref c-convs-at @k) (new (make-table c-int-hash c-int=?)))
(define c-conv-in
  (->* ((listof c-conv-noted acyclic) int int int) k-conv)
  (lambda (ns a b k)
    (cond ((null? ns) (cv-fx))
          ((k-at-is? (extract (car ns) 1) a b k) (extract (car ns) 2))
          (else (c-conv-in (cdr ns) a b k)))))
;; The convention the call whose operator is `x` is compiled in (noted at
;; the operator, which every place a compiler makes the call has): its
;; callee's, `cellular` or `native`; or `fx`, which looks at the callee's kind, where its type says
;; `fx` or a convention binder, or nothing was noted (Rust's
;; `NodeFacts::call_conv`).
(define c-call-conv-at (->* (int int int) k-conv)
  (lambda (a b k)
    (let ((ns (table-ref (get c-call-table) a nil)))
      (if (null? ns)
          (cv-fx)
          (tagcase (c-conv-in ns a b k)
            (cv-cellular () (cv-cellular)) (cv-native () (cv-native)) (else y (cv-fx)))))))
(define c-call-conv (->* (exp) k-conv)
  (lambda (x) (c-call-conv-at (exp-start x) (exp-end x) (exp-kth x))))
;; What the checker found the operation `a` `b` `k` takes (`k-datum`), in a
;; list of one; none if nothing.
(define c-datum-in
  (->* ((listof c-datum-noted acyclic) int int int) k-datums)
  (lambda (ns a b k)
    (cond ((null? ns) nil)
          ((k-at-is? (extract (car ns) 1) a b k) (the k-datums (cons (extract (car ns) 2) nil)))
          (else (c-datum-in (cdr ns) a b k)))))
(define c-datum-at (->* (int int int) k-datums)
  (lambda (a b k) (c-datum-in (table-ref (get c-fact-table) a nil) a b k)))
;; The same of an operation that holds `got`, if any: a form kept to be
;; inlined holds it (`c-resolve-extracts`).
(define c-datum-of (->* (k-datums int int int) k-datums)
  (lambda (got a b k) (if (null? got) (c-datum-at a b k) got)))

;; Each `with` the checker saw (its `k-with-vals`, as `c-set-facts!` took
;; them), by expression: its module's values' names, in order, and their
;; positions in the module.
;; And each module reshaped (`k-reshapes`), as `c-set-facts!` took them, by
;; expression: the positions of the values it keeps. A module given through
;; a signature is reshaped, so there are many, and every expression is asked
;; after (`c-changed?`).
(define c-reshape-index (ref c-reshape-table @k) (new (make-table c-int-hash c-int=?)))
(define c-index-reshapes! (->* (k-reshape-list) unit)
  (lambda (rs)
    (if (null? rs)
        #u
        (let ((a (extract (extract (car rs) 1) 1)))
          (begin (c-index-reshapes! (cdr rs))
                 (table-set! (get c-reshape-index) a
                             (the k-reshape-list
                               (cons (car rs) (table-ref (get c-reshape-index) a nil)))))))))
(define c-with-index (ref c-with-table @k) (new (make-table c-int-hash c-int=?)))
(define c-index-withs! (->* (k-with-list) unit)
  (lambda (ws)
    (if (null? ws)
        #u
        (let ((a (extract (extract (car ws) 1) 1)))
          (begin (c-index-withs! (cdr ws))
                 (table-set! (get c-with-index) a
                             (the k-with-list
                               (cons (car ws) (table-ref (get c-with-index) a nil)))))))))
;; The `with` `a` `b` `k`, in a list of one; none if the checker did not see
;; it.
(define c-with-in
  (->* (k-with-list int int int) k-with-list)
  (lambda (ws a b k)
    (cond ((null? ws) nil)
          ((k-at-is? (extract (car ws) 1) a b k) ws)
          (else (c-with-in (cdr ws) a b k)))))
;; Its module's values' names, in a list of one; none if it was not seen.
(define c-with-at
  (->* (int int int) c-with-names)
  (lambda (a b k)
    (let ((ws (c-with-in (table-ref (get c-with-index) a nil) a b k)))
      (if (null? ws) nil (the c-with-names (cons (extract (car ws) 2) nil))))))
;; Their positions in the module, likewise.
(define c-with-places-at
  (->* (int int int) (listof k-ids @k))
  (lambda (a b k)
    (let ((ws (c-with-in (table-ref (get c-with-index) a nil) a b k)))
      (if (null? ws) nil (the (listof k-ids @k) (cons (extract (car ws) 3) nil))))))
;; Module `x` reshaped, in a list of one; none if it is not.
(define c-reshape-in
  (->* (k-reshape-list int int int) k-reshape-list)
  (lambda (rs a b k)
    (cond ((null? rs) nil)
          ((k-at-is? (extract (car rs) 1) a b k) rs)
          (else (c-reshape-in (cdr rs) a b k)))))
(define c-reshape-of (->* (exp) k-reshape-list)
  (lambda (x)
    (let* ((a (exp-start x)) (rs (table-ref (get c-reshape-index) a nil)))
      (if (null? rs) rs (c-reshape-in rs a (exp-end x) (exp-kth x))))))
;; The positions of the values the module `x` reshaped keeps, in a list of
;; one; none if it is not reshaped.
(define c-reshape-at (->* (exp) (listof k-picks @k))
  (lambda (x)
    (let ((rs (c-reshape-of x)))
      (if (null? rs) nil (the (listof k-picks @k) (cons (extract (car rs) 2) nil))))))
;; Whether the module `x` is reshaped.
(define c-reshaped-at? (->* (exp) bool)
  (lambda (x) (not (null? (c-reshape-of x)))))
;; Whether `x`'s value is changed as it is given: converted to a
;; convention, or a module reshaped.
(define c-changed? (->* (exp) bool)
  (lambda (x)
    (or (>= (c-conversion-at x) 0) (c-reshaped-at? x) (not (null? (c-staged-at x))))))
;; Where an expression starting at `at` is, as a word's name says it: the
;; position; or, in a module's file (`load-module`, M7), `file:position`,
;; the file numbered as the Rust checker numbers them.
(define c-place-name (->* (int) string)
  (lambda (at)
    (if (< at load-base)
        (int->string at)
        (string-append (int->string (+ 1000 (quotient at load-base)))
                       ":" (int->string (remainder at load-base))))))
;; An abstract type `n`'s conversion, `prefix` `up-` or `down-`.
(define c-converter (->* (string symbol) symbol)
  (lambda (prefix n) (string->symbol (string-append prefix (symbol->string n)))))

(define c-tag (prompt-tag cresult cresult (maxeff c-emits (read @t) spin) @y)
  (make-continuation-prompt-tag))

(define c-fail (->* (string) void)
  (lambda (message) (abort-current-continuation c-tag (c-err message))))

(define c-labels (ref int @k) (new 0))

(define c-fresh (->* () int)
  (lambda () (let ((n (get c-labels))) (begin (set c-labels (+ n 1)) n))))

(define c-emit (->* (code item) unit)
  (lambda (c i) (set c (cons i (get c)))))

(define c-op (->* (code int) unit)
  (lambda (c r) (c-emit c (i-cell (wcell-routine r)))))

(define c-op1 (->* (code int wcell) unit)
  (lambda (c r x) (begin (c-op c r) (c-emit c (i-cell x)))))

(define c-lit (->* (code wcell) unit)
  (lambda (c x) (c-op1 c routine-lit x)))

(define c-int (->* (code int) unit)
  (lambda (c n) (c-lit c (wcell-int n))))

;; Field `k` of a bloblet whose type says it has one.
(define c-field (->* (code int) unit)
  (lambda (c k) (c-op1 c routine-field (wcell-int k))))

;; Field `k` of the bloblet on top set to the value under it.
(define c-field-set (->* (code int) unit)
  (lambda (c k) (begin (c-int c k) (c-op c routine-field-set))))

;; A runtime primitive with `n` arguments.
(define c-prim (->* (code string int) unit)
  (lambda (c name n)
    (let ((p (runtime-primitive name)))
      (if (< p 0)
          (c-fail (string-append "no runtime primitive " name))
          (begin (c-op1 c routine-prim (wcell-int p)) (c-emit c (i-cell (wcell-int n))))))))

;; Whether the program's convention is native: then every `lambda` of it,
;; and every standard operation as a value, is typed `native` (each takes
;; the program's convention), so the closures cellular code makes of them
;; are made so (`nclosure`, `TODO.md` §97). For a driver, as the checker's
;; `check-conv-native!`: `compile-conv-native!`.
(define c-native-program (ref bool @k) (new #f))
(define compile-conv-native! (->* (bool) unit)
  (lambda (on) (set c-native-program on)))
;; The stack routine every closure cellular code makes is made by, its own
;; thunks' too, for one rule.
(define c-closure-routine (->* () int)
  (lambda () (if (get c-native-program) routine-nclosure routine-closure)))
;; The routine that takes a continuation, a whole one if `whole`, and
;; calls a procedure with it: in a program whose convention is native, it
;; gives it in that convention (`ncallcc`, `ncallcomp`).
(define c-capture-routine (->* (bool) int)
  (lambda (whole)
    (if (get c-native-program)
        (if whole routine-ncallcc routine-ncallcomp)
        (if whole routine-callcc routine-callcomp))))
;; The routine that takes a delimited continuation one-shot (`TODO.md` §98):
;; `callone`, or `ncallone` in a program whose convention is native.
(define c-one-shot-routine (->* () int)
  (lambda () (if (get c-native-program) routine-ncallone routine-callone)))
;; The primitive a closure in a place is made by (an `rlambda`'s): in a
;; program whose convention is native, its adapter in the same place.
(define c-region-closure-prim (->* () string)
  (lambda () (if (get c-native-program) "%region-nclosure" "%region-closure")))
;; Of the closure on top, made for a `letrec`'s patch: in a program whose
;; convention is native, the cellular closure its adapter calls
;; (`%fx26-adapted`), which the patch writes into.
(define c-adapted (->* (code) unit)
  (lambda (c) (if (get c-native-program) (c-prim c "%fx26-adapted" 1) #u)))

;; A new blobref's flat's `size` bytes checked in the suffix, where more
;; than the one byte making it checked (`Checker::note_fits`).
(define c-fits (->* (code int) unit)
  (lambda (c size) (if (> size 1) (begin (c-int c size) (c-prim c "%fx26-suffix-fits" 2)) #u)))

;; Drop what a mutator left, and leave FX-26's unit value instead.
(define c-unit-after (->* (code) unit)
  (lambda (c) (begin (c-op c routine-drop) (c-lit c (wcell-unit)))))

;;; ----------------------------------------------------------- assembling

(define c-reverse (->* (items items) items)
  (lambda (xs acc) (if (null? xs) acc (c-reverse (cdr xs) (cons (car xs) acc)))))

(define c-size (->* (item) int)
  (lambda (i) (tagcase i (i-cell (x) 1) (i-label (n) 0) (i-branch (n) 2) (i-zbranch (n) 2))))

;; Where each label is, in cells; and how many cells there are.
(define c-place (->* (items c-places int) int)
  (lambda (xs at pos)
    (if (null? xs)
        pos
        (begin (tagcase (car xs) (i-label (n) (array-set! at n pos)) (else x #u))
               (c-place (cdr xs) at (+ pos (c-size (car xs))))))))

;; A branch by routine `r`, its two cells at `pos`, to `to`, onto `acc`:
;; its offset counts from the cell after it.
(define c-branch-cells (->* (int int int (listof wcell @k)) (listof wcell @k))
  (lambda (r to pos acc) (cons (wcell-routine r) (cons (wcell-int (- to (+ pos 2))) acc))))

;; The cells, branches resolved (an offset counts from the cell after it):
;; from the items newest first, each ending at `end`, onto those after it,
;; in a loop, however long the word.
(define c-cells (->* (items c-places int (listof wcell @k)) (listof wcell @k))
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

(define c-assemble (->* (code symbol) tword)
  (lambda (c name)
    (let* ((at (the c-places (make-array (get c-labels) 0)))
           (end (c-place (c-reverse (get c) nil) at 0)))
      (make-word name (c-cells (get c) at end nil)))))

;; `e` with `n` bound at `l`, innermost.
(define c-extend (->* (symbol loc cenv) cenv)
  (lambda (n l e) (cons (cons n l) e)))

(define c-loop? (->* (loc) bool)
  (lambda (l) (tagcase l (at-loop (z) #t) (else y #f))))

(define c-global? (->* (loc) bool)
  (lambda (l) (tagcase l (at-global (g) #t) (else y #f))))

(define c-lifted? (->* (loc) bool)
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
(define c-this-loc? (->* (loc loc) bool)
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
(define c-genv-now (->* () int)
  (lambda () (if (< (get c-genv) 0) (get c-genv-count) (get c-genv))))

(define c-global-first (->* (c-globals-made int) c-found)
  (lambda (es limit)
    (cond ((null? es) nil)
          ((or (< limit 0) (< (car (car es)) limit)) (the c-found (cons (cdr (car es)) nil)))
          (else (c-global-first (cdr es) limit)))))

;; `n`'s newest global before the `limit`th (-1: any), in a list.
(define c-global-find (->* (symbol int) c-found)
  (lambda (n limit) (c-global-first (table-ref (get c-genv-index) n nil) limit)))

;; `n`'s global `g`, the `i`th made, as its newest.
(define c-genv-push! (->* (symbol int wglobal) unit)
  (lambda (n i g)
    (let ((made (the (pairof int loc @k) (cons i (at-global g)))))
      (table-set! (get c-genv-index) n
                  (the c-globals-made (cons made (table-ref (get c-genv-index) n nil)))))))

(define c-find (->* (cenv symbol) c-found)
  (lambda (e n)
    (cond ((null? e) nil)
          ((symbol=? (car (car e)) n) (the c-found (cons (cdr (car e)) nil)))
          (else (c-find (cdr e) n)))))

;; Where `n` is: in the locals, else in the globals; none means standard.
(define c-where (->* (cenv symbol) c-found)
  (lambda (e n) (let ((l (c-find e n))) (if (null? l) (c-global-find n (get c-genv)) l))))

(define c-load (->* (code loc) unit)
  (lambda (c l)
    (tagcase l
      (at-slot (i) (c-op1 c routine-slot (wcell-int i)))
      (at-free (i) (c-op1 c routine-free (wcell-int i)))
      (at-global (g) (c-op1 c routine-global (wcell-global g)))
      (at-pending (i) (c-fail "a letrec sibling not made yet is only captured"))
      (at-loop (z) (c-fail "a loop is only ever called, in tail position"))
      (at-lifted (k) (c-fail "a lifted procedure is only called")))))

(define c-join-memo (ref (table k-at c-join-answer @k) @k) (new (make-table c-at-hash c-at=?)))
(define c-standard-words (ref (listof c-standard-word @k) @k) (new nil))
(define c-spec-made (ref (table k-at c-spec-copies @k) @k) (new (make-table c-at-hash c-at=?)))

(define c-fill-facts (->* (k-facts) unit)
  (lambda (fs)
    (if (null? fs)
        #u
        (let ((at (extract (car fs) 1)))
          (begin
            (tagcase (extract (car fs) 2)
              (n-datum (d)
                (let ((a (extract at 1)))
                  (table-set! (get c-fact-table) a
                              (the (listof c-datum-noted acyclic)
                                (cons (product (1 at) (2 d))
                                      (table-ref (get c-fact-table) a nil))))))
              (n-apply-shares () (c-note! (get c-shares-table) at 0))
              (n-frozen-define () (c-note! (get c-frozen-table) at 0))
              (n-plain-fx () (c-note! (get c-plain-table) at 0))
              (n-conversion (code) (c-note! (get c-convert-table) at code))
              (n-staged (m e r)
                (set c-staged-texts (cons (product (1 at) (2 m) (3 e) (4 r)) (get c-staged-texts))))
              (n-call (cv)
                (let ((a (extract at 1)))
                  (table-set! (get c-call-table) a
                              (the (listof c-conv-noted acyclic)
                                (cons (product (1 at) (2 cv))
                                      (table-ref (get c-call-table) a nil))))))
              ;; The greatest summary, per expression.
              (n-summary (s)
                (let ((known (c-noted-at (get c-summary-table) (extract at 1) (extract at 2)
                                         (extract at 3) -1)))
                  (c-note! (get c-summary-table) at (if (> s known) s known)))))
            (c-fill-facts (cdr fs)))))))

;; The effect summary of the expression `a` `b` `k` (3, the most, if none was
;; noted: `checked-extracts`).
(define c-summary-at (->* (int int int) int)
  (lambda (a b k) (let ((s (c-noted-at (get c-summary-table) a b k -1))) (if (< s 0) 3 s))))

;; `c-facts` into `c-fact-table`.
(define c-set-facts! (->* (k-facts) unit)
  (lambda (fs)
    (begin
      (set c-facts fs)
      (set c-fact-table (make-table c-int-hash c-int=?))
      (set c-call-table (make-table c-int-hash c-int=?))
      (set c-convert-table (c-new-by-at))
      (set c-staged-texts nil)
      (set c-shares-table (c-new-by-at))
      (set c-frozen-table (c-new-by-at))
      (set c-plain-table (c-new-by-at))
      (set c-summary-table (c-new-by-at))
      (set c-join-memo (make-table c-at-hash c-at=?))
      (set c-spec-made (make-table c-at-hash c-at=?))
      (set c-standard-words nil)
      (set c-lifts (make-table c-int-hash c-int=?))
      (set c-lift-count 0)
      (set c-lifted (make-table c-at-hash c-at=?))
      (set c-with-index (make-table c-int-hash c-int=?))
      (c-index-withs! (get k-with-vals))
      (set c-included-index (make-table c-int-hash c-int=?))
      (set c-reshape-index (make-table c-int-hash c-int=?))
      (c-index-reshapes! (get k-reshapes))
      (c-fill-facts fs))))

(define c-member? (->* (syms symbol) bool)
  (lambda (xs n) (and (not (null? xs)) (or (symbol=? (car xs) n) (c-member? (cdr xs) n)))))

(define c-adjoin (->* (syms symbol) syms)
  (lambda (xs n) (if (c-member? xs n) xs (cons n xs))))

(define c-bind-params (->* (c-params syms) syms)
  (lambda (ps bound)
    (if (null? ps) bound (c-bind-params (cdr ps) (cons (extract (car ps) 1) bound)))))

(define c-bind-letrec (->* (c-recs syms) syms)
  (lambda (bs bound)
    (if (null? bs) bound (c-bind-letrec (cdr bs) (cons (extract (car bs) 1) bound)))))

(define c-bind-let (->* (c-binds syms) syms)
  (lambda (bs bound)
    (if (null? bs) bound (c-bind-let (cdr bs) (cons (extract (car bs) 1) bound)))))

(define c-names (->* (names syms) syms)
  (lambda (ns bound) (if (null? ns) bound (c-names (cdr ns) (cons (car ns) bound)))))

;; Every name a module's `items` define, onto `bound`: an abstract type's
;; conversions, a definition's, a `define-rec`'s members'.
(define c-module-bound (->* (mod-items syms) syms)
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
(define c-bound-exps (->* (c-binds) exps)
  (lambda (bs) (if (null? bs) nil (cons (extract (car bs) 2) (c-bound-exps (cdr bs))))))

;; The same for a `letrec`'s bindings.
(define c-rec-exps (->* (c-recs) exps)
  (lambda (bs) (if (null? bs) nil (cons (extract (car bs) 3) (c-rec-exps (cdr bs))))))

;; The `(with %include …)`s of modules' items whose names the module binds
;; once, where it is made (`c-note-included!`): they bind nothing. As the
;; Rust compiler's `included_withs`.
(define c-included-index (ref c-with-table @k) (new (make-table c-int-hash c-int=?)))
(define c-included? (->* (int int int) bool)
  (lambda (a b k) (not (null? (c-with-in (table-ref (get c-included-index) a nil) a b k)))))
;; Item value `x`'s `(with %include …)` (`with_includes`), in a list of one.
;; A parameter of its lambda shadows the included names, and the `with`
;; binds none of its (`k-include-free`).
(define c-include-with (->* (exp) exps)
  (lambda (x)
    (tagcase x
      (e-with (m body a b abk)
        (if (and (string=? (symbol->string m) "%include") (not (null? (c-with-at a b abk))))
            (the exps (cons x nil))
            nil))
      (e-lambda (qs body a b abk) (c-include-with body))
      (e-plambda (d body a b abk) (c-include-with body))
      (e-the (d body a b abk) (c-include-with body))
      (e-rlambda (r l a b abk) (c-include-with l))
      (else y nil))))
;; Names `ns` at positions `ps` onto `names` and `places`, newest first,
;; each not `seen` yet (by position: a name has one).
(define c-included-add
  (->* (syms k-ids syms k-ids (table int bool @k)) (productof (1 syms) (2 k-ids)))
  (lambda (ns ps names places seen)
    (cond ((or (null? ns) (null? ps)) (product (1 names) (2 places)))
          ((table-ref seen (car ps) #f) (c-included-add (cdr ns) (cdr ps) names places seen))
          (else (begin (table-set! seen (car ps) #t)
                       (c-included-add (cdr ns) (cdr ps) (the syms (cons (car ns) names))
                                       (the k-ids (cons (car ps) places)) seen))))))
(define c-included-exps (->* (exps c-included (table int bool @k)) c-included)
  (lambda (xs acc seen)
    (if (null? xs)
        acc
        (let ((w (c-include-with (car xs))))
          (c-included-exps
           (cdr xs)
           (if (null? w)
               acc
               (tagcase (car w)
                 (e-with (m body a b abk)
                   (let ((more (c-included-add (car (c-with-at a b abk))
                                               (car (c-with-places-at a b abk))
                                               (extract acc 1) (extract acc 2) seen)))
                     (product (1 (extract more 1)) (2 (extract more 2))
                              (3 (the exps (cons (car w) (extract acc 3)))))))
                 (else y acc)))
           seen)))))
(define c-included-items (->* (mod-items c-included (table int bool @k)) c-included)
  (lambda (items acc seen)
    (if (null? items)
        acc
        (let* ((it (car items)) (k (extract it 1)) (xs (extract it 4)))
          (c-included-items (cdr items)
                            (cond ((= k 2) (c-included-exps (the exps (list (car xs))) acc seen))
                                  ((= k 3) (c-included-exps xs acc seen))
                                  (else acc))
                            seen)))))
;; Names `ns` and positions `ps`, newest first, onto `os` and `qs`, the
;; oldest first.
(define c-included-oldest (->* (syms k-ids syms k-ids) (productof (1 syms) (2 k-ids)))
  (lambda (ns ps os qs)
    (if (or (null? ns) (null? ps))
        (product (1 os) (2 qs))
        (c-included-oldest (cdr ns) (cdr ps) (the syms (cons (car ns) os))
                           (the k-ids (cons (car ps) qs))))))
;; A module's included values (`TODO.md` §69): the names its items'
;; `(with %include …)`s use, in order, each with its position in
;; `%include`, to be bound once where the module is made, after `%include`,
;; as an import line's were; and those `with`s, which then bind nothing,
;; so that a lambda captures the names it uses rather than loading each
;; from `%include` at every call. As the Rust compiler's `included_names`.
(define c-included-names (->* (mod-items) c-included)
  (lambda (items)
    (let ((none (the c-included (product (1 nil) (2 nil) (3 nil)))))
      (if (or (null? items)
              (not (= (extract (car items) 1) 2))
              (not (string=? (symbol->string (car (extract (car items) 2))) "%include")))
          none
          (let* ((inc (c-included-items (cdr items) none (make-table c-int-hash c-int=?)))
                 (old (c-included-oldest (extract inc 1) (extract inc 2) nil nil)))
            (product (1 (extract old 1)) (2 (extract old 2)) (3 (extract inc 3))))))))
(define c-note-withs! (->* (exps) unit)
  (lambda (ws)
    (if (null? ws)
        #u
        (begin
          (tagcase (car ws)
            (e-with (m body a b abk)
              (if (c-included? a b abk)
                  #u
                  (let ((at (c-with-in (table-ref (get c-with-index) a nil) a b abk)))
                    (if (null? at)
                        #u
                        (table-set! (get c-included-index) a
                                    (the k-with-list
                                      (cons (car at) (table-ref (get c-included-index) a nil))))))))
            (else y #u))
          (c-note-withs! (cdr ws))))))
;; `c-included-names`, its `with`s noted as binding nothing.
(define c-note-included! (->* (mod-items) c-included)
  (lambda (items)
    (let ((inc (c-included-names items))) (begin (c-note-withs! (extract inc 3)) inc))))

(define-rec
  (c-free-all (->* (exps syms syms) syms)
    (lambda (es bound acc)
      (if (null? es) acc (c-free-all (cdr es) bound (c-free (car es) bound acc)))))
  (c-free (->* (exp syms syms) syms)
    (lambda (x bound acc)
      (tagcase x
        (e-var (n a b abk) (if (c-member? bound n) acc (c-adjoin acc n)))
        (e-lambda (ps body a b abk) (c-free body (c-bind-params ps bound) acc))
        (e-app (f args a b abk) (c-free f bound (c-free-all args bound acc)))
        (e-plambda (d body a b abk) (c-free body bound acc))
        (e-letregion (k r i body a b abk) (c-free body (cons r bound) acc))
        (e-rlambda (r l a b abk) (c-free r bound (c-free l bound acc)))
        (e-proj (body ds a b abk) (c-free body bound acc))
        (e-the (d body a b abk) (c-free body bound acc))
        (e-convention (cnv body a b abk) (c-free body bound acc))
        (e-if (t th el a b abk) (c-free t bound (c-free th bound (c-free el bound acc))))
        (e-letrec (bs body a b abk)
          (let ((inner (c-bind-letrec bs bound)))
            (c-free body inner (c-free-all (c-rec-exps bs) inner acc))))
        (e-let (bs body a b abk)
          (c-free body (c-bind-let bs bound) (c-free-all (c-bound-exps bs) bound acc)))
        (e-begin (es a b abk) (c-free-all es bound acc))
        (e-prompt (t body h a b abk) (c-free t bound (c-free body bound (c-free h bound acc))))
        (e-bloblet (op i args got a b abk) (c-free-all args bound acc))
        (e-product (fs a b abk) (c-free-all (c-bound-exps fs) bound acc))
        (e-extract (p l got a b abk) (c-free p bound acc))
        (e-sum (t v a b abk) (c-free v bound acc))
        (e-tagcase (s arms els got a b abk)
          (c-free s bound (c-free-arms arms bound (c-free-else els bound acc))))
        ;; A module's items see all of them, as a `letrec*`'s.
        (e-module (items a b abk) (c-free-items items (c-module-bound items bound) acc))
        ;; The module, then the body, the module's values bound in it.
        (e-with (m body a b abk)
          (cond ((string=? (symbol->string m) "#%fx") acc)
                ;; A module's included names, bound where it is made, from
                ;; inside the item (outside, `%include` is bound, and the
                ;; names bound in it are as good).
                ((and (c-included? a b abk) (not (c-member? bound m))) (c-free body bound acc))
                (else
                 (let ((ns (c-with-at a b abk)) (acc (if (c-member? bound m) acc (c-adjoin acc m))))
                   (c-free body (if (null? ns) bound (c-names (car ns) bound)) acc)))))
        (else y acc))))
  (c-free-items (->* (mod-items syms syms) syms)
    (lambda (items bound acc)
      (if (null? items)
          acc
          (let ((k (extract (car items) 1)))
            (c-free-items (cdr items) bound
                          (if (or (= k 0) (= k 2) (= k 3))
                              (c-free-all (extract (car items) 4) bound acc)
                              acc))))))
  (c-free-arms
    (->* (c-cases syms syms) syms)
    (lambda (arms bound acc)
      (if (null? arms)
          acc
          (let ((inner (c-names (extract (car arms) 3) bound)))
            (c-free-arms (cdr arms) bound (c-free (extract (car arms) 4) inner acc))))))
  (c-free-else (->* (c-binds syms syms) syms)
    (lambda (els bound acc)
      (if (null? els) acc (c-free (extract (car els) 2) (cons (extract (car els) 1) bound) acc)))))

;; What is left when the value is in hand: `return` in tail position.
(define c-done (->* (code bool) unit)
  (lambda (c tail) (if tail (c-op c routine-return) #u)))

;; After a body whose value is on top of `n` values bound from `slot`
;; up: the value into `slot`, the others dropped. Nothing in tail
;; position, where `return` drops the whole frame.
(define c-unbind (->* (code int int bool) unit)
  (lambda (c slot n tail)
    (if (or tail (= n 0))
        #u
        (letrec ((drops (subr (maxeff c-emits spin) (int) unit)
                   (lambda (k) (if (= k 0) #u (begin (c-op c routine-drop) (drops (- k 1)))))))
          (begin (c-op1 c routine-slot! (wcell-int slot)) (drops (- n 1)))))))

(define c-count-let (->* (c-binds) int)
  (lambda (bs) (if (null? bs) 0 (+ 1 (c-count-let (cdr bs))))))

(define c-letrec-slots (->* (c-recs cenv int) cenv)
  (lambda (bs e d)
    (if (null? bs)
        e
        (c-letrec-slots (cdr bs) (c-extend (extract (car bs) 1) (at-slot d) e) (+ d 1)))))

(define c-patch-one (->* (patches int int code) unit)
  (lambda (ps depth i c)
    (if (null? ps)
        #u
        (begin (c-op1 c routine-slot (wcell-int (cdr (car ps))))
               (c-op1 c routine-slot (wcell-int (+ depth i)))
               (c-adapted c)
               (c-field-set c (+ cellular-closure-free0 (car (car ps))))
               (c-patch-one (cdr ps) depth i c)))))

;; Each placeholder of closure `i` patched with its sibling.
(define c-letrec-patch (->* ((listof patches @k) int int code) unit)
  (lambda (made depth i c)
    (if (null? made)
        #u
        (begin (c-patch-one (car made) depth i c) (c-letrec-patch (cdr made) depth (+ i 1) c)))))

;;; ------------------------------------------------------- known procedures

;; `x`, when it is a lambda under any type abstractions and ascriptions,
;; which compile to nothing; none otherwise.
(define c-lambda-of (->* (exp) (listof exp @k))
  (lambda (x)
    (tagcase x
      (e-plambda (d body a b abk) (c-lambda-of body))
      (e-the (d body a b abk) (c-lambda-of body))
      (e-convention (cnv body a b abk) (c-lambda-of body))
      (e-lambda (ps body a b abk) (the (listof exp @k) (cons x nil)))
      (e-rlambda (r l a b abk) (the (listof exp @k) (cons x nil)))
      (else y nil))))

(define c-count-exps (->* (exps) int)
  (lambda (es) (if (null? es) 0 (+ 1 (c-count-exps (cdr es))))))

(define c-count-params (->* (c-params) int)
  (lambda (ps) (if (null? ps) 0 (+ 1 (c-count-params (cdr ps))))))

;; Whether a parameter of `ps` is named `n`, which hides what else `n` names.
(define c-has-param? (->* (c-params symbol) bool)
  (lambda (ps n) (c-member? (c-bind-params ps nil) n)))

;; Parameters `ps` bound to `args`, as a `let` binds.
(define c-param-bindings (->* (c-params exps) c-binds)
  (lambda (ps args)
    (if (null? ps)
        nil
        (cons (product (1 (extract (car ps) 1)) (2 (car args)))
              (c-param-bindings (cdr ps) (cdr args))))))

;; A plain lambda (under forms that compile to nothing) applied at once to
;; as many arguments as it has parameters, as the Rust compiler's
;; `applied_lambda` finds it: the `let` it is, its bindings and body, in a
;; list of one; none if `f` is no such lambda.
(define c-applied-let (->* (exp exps) (listof (productof (1 c-binds) (2 exp)) @k))
  (lambda (f args)
    (let ((lam (c-lambda-of f)))
      (if (null? lam)
          nil
          (tagcase (car lam)
            (e-lambda (ps body a b abk)
              (if (= (c-count-params ps) (c-count-exps args))
                  (the (listof (productof (1 c-binds) (2 exp)) @k)
                    (cons (product (1 (c-param-bindings ps args)) (2 body)) nil))
                  nil))
            (else y nil))))))

(define c-mentions? (->* (exp symbol) bool)
  (lambda (x n) (c-member? (c-free x nil nil) n)))

;; Whether every use of `f` in `x` is a call with `n` arguments: where
;; `loops` asks, in tail position, which the compiler makes a loop; else in
;; any position, and in lambdas inside too, so that `f` is never a value.
(define-rec
  (c-calls-only (->* (exp symbol int bool bool) bool)
    (lambda (x f n tail loops)
      (tagcase x
        (e-var (m a b abk) (not (symbol=? m f)))
        (e-lambda (ps body a b abk) (or (c-has-param? ps f) (c-calls-only-inside body f n loops)))
        (e-app (fun args a b abk)
          (and (c-calls-only-all args f n loops)
               (tagcase fun
                 (e-var (m a2 b2 a2b2k)
                   (if (symbol=? m f) (and (or tail (not loops)) (= (c-count-exps args) n)) #t))
                 (else y (c-calls-only fun f n #f loops)))))
        (e-plambda (d body a b abk) (c-calls-only body f n tail loops))
        (e-letregion (k r i body a b abk) (or (symbol=? r f) (c-calls-only body f n #f loops)))
        (e-rlambda (r l a b abk) (and (c-calls-only r f n #f loops) (c-calls-only l f n #f loops)))
        (e-proj (body ds a b abk) (c-calls-only body f n tail loops))
        (e-the (d body a b abk) (c-calls-only body f n tail loops))
        (e-convention (cnv body a b abk) (c-calls-only body f n tail loops))
        (e-if (t th el a b abk)
          (and (c-calls-only t f n #f loops)
               (c-calls-only th f n tail loops)
               (c-calls-only el f n tail loops)))
        (e-letrec (bs body a b abk)
          (or (c-member? (c-bind-letrec bs nil) f)
              (and (c-calls-only-all (c-rec-exps bs) f n loops)
                   (c-calls-only body f n tail loops))))
        (e-let (bs body a b abk)
          (and (c-calls-only-all (c-bound-exps bs) f n loops)
               (or (c-member? (c-bind-let bs nil) f) (c-calls-only body f n tail loops))))
        (e-begin (es a b abk) (c-calls-only-begin es f n tail loops))
        (e-prompt (t body h a b abk)
          (and (c-calls-only t f n #f loops)
               (c-calls-only h f n #f loops)
               (c-calls-only-inside body f n loops)))
        (e-bloblet (op i args got a b abk) (c-calls-only-all args f n loops))
        (e-product (fs a b abk) (c-calls-only-all (c-bound-exps fs) f n loops))
        (e-extract (p l got a b abk) (c-calls-only p f n #f loops))
        (e-sum (t v a b abk) (c-calls-only v f n #f loops))
        (e-tagcase (s arms els got a b abk)
          (and (c-calls-only s f n #f loops)
               (c-calls-only-arms arms f n tail loops)
               (c-calls-only-else els f n tail loops)))
        ;; Said of no module (as the Rust compiler's `loops_only` and
        ;; `called_only` say).
        (e-module (items a b abk) #f)
        (e-with (m body a b abk) #f)
        (else y #t))))
  ;; The same for the body of a lambda or a prompt in `x`: where `loops`
  ;; asks, no call there is in tail position, so it may not mention `f`.
  (c-calls-only-inside (->* (exp symbol int bool) bool)
    (lambda (x f n loops) (if loops (not (c-mentions? x f)) (c-calls-only x f n #f loops))))
  (c-calls-only-all (->* (exps symbol int bool) bool)
    (lambda (es f n loops)
      (or (null? es)
          (and (c-calls-only (car es) f n #f loops) (c-calls-only-all (cdr es) f n loops)))))
  (c-calls-only-begin (->* (exps symbol int bool bool) bool)
    (lambda (es f n tail loops)
      (cond ((null? es) #t)
            ((null? (cdr es)) (c-calls-only (car es) f n tail loops))
            (else (and (c-calls-only (car es) f n #f loops)
                       (c-calls-only-begin (cdr es) f n tail loops))))))
  (c-calls-only-arms
    (->* (c-cases symbol int bool bool) bool)
    (lambda (arms f n tail loops)
      (or (null? arms)
          (and (or (c-member? (extract (car arms) 3) f)
                   (c-calls-only (extract (car arms) 4) f n tail loops))
               (c-calls-only-arms (cdr arms) f n tail loops)))))
  (c-calls-only-else (->* (c-binds symbol int bool bool) bool)
    (lambda (els f n tail loops)
      (or (null? els)
          (symbol=? (extract (car els) 1) f)
          (c-calls-only (extract (car els) 2) f n tail loops)))))

;; Whether every use of `f` in `x` is a call with `n` arguments in tail
;; position, which the compiler makes a loop.
(define c-loops-only (->* (exp symbol int bool) bool)
  (lambda (x f n tail) (c-calls-only x f n tail #t)))

;; Whether every use of `f` in `x` is a call with `n` arguments, in any
;; position and in lambdas inside too: so it is never a value.
(define c-called-only (->* (exp symbol int) bool)
  (lambda (x f n) (c-calls-only x f n #f #f)))

;; Binding `i`'s scope while it is made: each sibling pending, and itself a
;; loop if it only calls itself in loops.
(define c-letrec-own
  (->* (c-recs cenv int int int exp int) cenv)
  (lambda (bs e depth k i body nps)
    (if (null? bs)
        e
        (let* ((g (extract (car bs) 1))
               (loops (and (= k i) (c-loops-only body g nps #t))))
          (c-letrec-own (cdr bs) (c-extend g (if loops (at-loop 0) (at-pending (+ depth k))) e)
                        depth (+ k 1) i body nps)))))

(define c-count-letrec (->* (c-recs) int)
  (lambda (bs) (if (null? bs) 0 (+ 1 (c-count-letrec (cdr bs))))))

(define c-length (->* (syms) int)
  (lambda (xs) (if (null? xs) 0 (+ 1 (c-length (cdr xs))))))

(define c-nth-binding
  (->* (c-recs int) (productof (1 symbol) (2 syn) (3 exp)))
  (lambda (bs i) (if (= i 0) (car bs) (c-nth-binding (cdr bs) (- i 1)))))

;; Whether no binding of `bs` but the `i`th mentions `name`; `k` counts.
(define c-unmentioned? (->* (c-recs symbol int int) bool)
  (lambda (bs name i k)
    (or (null? bs)
        (and (or (= k i) (not (c-mentions? (extract (car bs) 3) name)))
             (c-unmentioned? (cdr bs) name i (+ k 1))))))

;; Whether `letrec` binding `i` of `bs` is a join point, as the Rust
;; compiler's `r_join_ok` says: a lambda whose body calls it only in tail
;; position, as the `letrec`'s body does, and that no sibling mentions; so
;; no closure of it need be made, and each call is a jump.
(define c-join-ok? (->* (c-recs exp int) bool)
  (lambda (bs body i)
    (let* ((b (c-nth-binding bs i)) (name (extract b 1)) (lam (c-lambda-of (extract b 3))))
      (and (not (null? lam))
           (tagcase (car lam)
             (e-lambda (ps lbody la lb lalbk)
               (let ((n (c-count-params ps)))
                 (and (not (c-has-param? ps name))
                      (c-loops-only lbody name n #t)
                      (c-loops-only body name n #t)
                      (c-unmentioned? bs name i 0))))
             (else y #f)))))))))
