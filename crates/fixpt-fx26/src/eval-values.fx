;;; An FX-26 evaluator, in FX-26 (PLAN.md §11, step 9b): its values.
;;;
;;; FX-26's meaning, written in FX-26: the trees `parser.fx` makes, run
;;; directly; the reference the compilers are checked against, beside the
;;; lowering to Scheme. Written again (2026-10-08, the user's) once FX-26
;;; had unions, `quote` and `case` on symbols, as a metacircular evaluator
;;; is written: a value is the program's value as itself, where
;;; FX-26 has one of its shape to tell apart at run time (an integer, an
;;; `f64` or `f32`, a character, a boolean, a string, a symbol, `nil`, a
;;; pair, an array, a procedure, a reference), and an `other` where it has
;;; none (unit, a symbol's shape; a product or sum, whose labels are the
;;; program's; an i-cell, a bloblet, a prompt tag, a continuation, a mark
;;; key, an escape). A procedure is one of the list of its
;;; arguments: a closure, a primitive, a `vlambda`'s and a `cwcc` escape
;;; alike. Primitives are found by name in a table (`eval-prims.fx`); the
;;; evaluator proper is `eval-core.fx`.
;;;
;;; What a program can change is kept in the evaluator's region @v. Its
;;; control is FX-26's, one level up, in @x: a prompt tag the program makes
;;; is a prompt tag of the evaluator's, and so are its continuations and
;;; mark keys.
;;;
;;; Not yet: bloblets' frozen flags.

;; What changing the program's store on @v may do; what a delimited part
;; of the program may do, besides control on @x; and what evaluating may.
(define-effect stores (maxeff (read @globals) (read @v) (write @v) (alloc @v)))
(define-effect runs (maxeff stores (read @x) (write @x) (alloc @x)))
(define-effect evals (maxeff runs (goto @x) (comefrom @x)))

;; A value: as itself, or an `other`, the one sum among them.
(define-type val
  (union int f64 f32 char bool string symbol nil
         (pairof val val @v) (arrayof val @v)
         (subr (maxeff evals spin) ((listof val @v)) val)
         (ref val @v)
         other))
;; A value of no shape of its own: unit (a symbol's shape at run time, so
;; told apart here), a product with its labels (as `extract` names one) or a
;; sum with its tag, an i-cell (whether full, and its value), a bloblet (its
;; fields, and its suffix's bytes), and the evaluator's own control.
(define-datatype other
  (o-unit)
  (o-product (listof (pairof symbol val @v) @v))
  (o-sum symbol val)
  (o-icell (ref bool @v) (ref val @v))
  (o-blob (arrayof val @v) (arrayof int @v))
  (o-tag (prompt-tag val val (maxeff runs spin) @x))
  (o-cont (composable val val (maxeff runs spin) @x))
  ;; A `cwcc` escape.
  (o-esc (subr (goto @x) (val) void))
  (o-key (mark-key val @x)))

(define-type vals (listof val @v))
(define-type vproc (subr (maxeff evals spin) (vals) val))
;; A product's fields, by label.
(define-type vfields (listof (pairof symbol val @v) @v))
;; Variables: each name and the cell that holds its value.
(define-type vcell (ref val @v))
(define-type env (listof (pairof symbol vcell @v) @v))
(define-type vtag (prompt-tag val val (maxeff runs spin) @x))
(define-type vcont (composable val val (maxeff runs spin) @x))

;; Unit: one value, made once.
(define the-unit val (o-unit))

;;; ------------------------------------------------------------- failing

(define-datatype eresult (ev-ok val) (ev-err string))
(define eval-tag (prompt-tag eresult eresult (maxeff runs spin) @x)
  (make-continuation-prompt-tag))
(define* efail (subr evals (string) void)
  (lambda (message) (abort-current-continuation eval-tag (ev-err message))))
;; Fails: `what` is expected.
(define* efail-expected (subr evals (string) void)
  (lambda (what) (efail (string-append what " is expected"))))

;;; ------------------------------------------------------------- telling

;; `v`, an `other`; or fails, `what` being expected.
(define* as-other (subr evals (val string) other)
  (lambda (v what) (typecase v (sum o o) (else (efail-expected what)))))

(define* as-int (subr evals (val) int)
  (lambda (v) (if (int? v) v (efail-expected "an int"))))
(define* as-bool (subr evals (val) bool)
  (lambda (v) (if (bool? v) v (efail-expected "a bool"))))
(define* as-str (subr evals (val) string)
  (lambda (v) (if (string? v) v (efail-expected "a string"))))
(define* as-char (subr evals (val) char)
  (lambda (v) (if (char? v) v (efail-expected "a char"))))
(define* as-f64 (subr evals (val) f64)
  (lambda (v) (if (f64? v) v (efail-expected "an f64"))))
(define* as-sym (subr evals (val) symbol)
  (lambda (v) (if (symbol? v) v (efail-expected "a symbol"))))
(define* as-pair (subr evals (val) (pairof val val @v))
  (lambda (v) (if (pair? v) v (efail-expected "a pair"))))
(define* as-array (subr evals (val) (arrayof val @v))
  (lambda (v) (if (array? v) v (efail-expected "an array"))))
(define* as-f32 (subr evals (val) f32)
  (lambda (v) (if (f32? v) v (efail-expected "an f32"))))
(define* as-ref (subr evals (val) vcell)
  (lambda (v) (if (ref? v) v (efail-expected "a reference"))))
(define* as-tag (subr (maxeff evals spin) (val) vtag)
  (lambda (v)
    (tagcase (as-other v "a prompt tag") (o-tag (t) t) (else y (efail-expected "a prompt tag")))))
(define* as-key (subr (maxeff evals spin) (val) (mark-key val @x))
  (lambda (v)
    (tagcase (as-other v "a mark key") (o-key (k) k) (else y (efail-expected "a mark key")))))
(define* as-cont (subr (maxeff evals spin) (val) vcont)
  (lambda (v)
    (let ((what "a composable continuation"))
      (tagcase (as-other v what) (o-cont (k) k) (else y (efail-expected what))))))
;; A product's fields, by label.
(define* as-fields (subr (maxeff evals spin) (val string) vfields)
  (lambda (v what)
    (tagcase (as-other v what) (o-product (fs) fs) (else y (efail-expected what)))))

;;; ------------------------------------------------------------- lists

;; The arguments of a call, as the list value a `vlambda` is given.
(define* vals->val (subr (maxeff (read @globals) (read @v) (alloc @v) spin) (vals) val)
  (lambda (xs) (if (null? xs) nil (cons (car xs) (vals->val (cdr xs))))))
(define* list->val (subr (maxeff (read @globals) (read @x) (alloc @v) spin) ((listof val @x)) val)
  (lambda (xs) (if (null? xs) nil (cons (car xs) (list->val (cdr xs))))))
;; A list value's elements, as the arguments `apply` gives: a list of its
;; own, which nothing else can write (F11), as the machines copy it. With
;; no `eq?` to find a cycle by, a cyclic list is not ended: the machines'
;; is an error (`programs/native/apply-cyclic.fx`, which this never runs).
(define* val->vals (subr (maxeff (read @globals) (read @v) (alloc @v) spin) (val) vals)
  (lambda (v) (if (pair? v) (cons (car v) (val->vals (cdr v))) nil)))

;; Argument `i` of `xs`.
(define* ev-arg (subr (maxeff evals spin) (vals int) val)
  (lambda (xs i)
    (cond ((null? xs) (efail "too few arguments"))
          ((= i 0) (car xs))
          (else (ev-arg (cdr xs) (- i 1))))))

;;; ------------------------------------------------------------- applying

;; `f` applied to `xs`: a procedure called; a continuation resumed.
(define* apply-val (subr (maxeff evals spin) (val vals) val)
  (lambda (f xs)
    (typecase f
      (procedure p (p xs))
      (sum o
        (tagcase o
          (o-cont (k) (k (ev-arg xs 0)))
          (o-esc (k) (k (ev-arg xs 0)))
          (else y (efail "not a subroutine"))))
      (else (efail "not a subroutine")))))
(define* apply1 (subr (maxeff evals spin) (val val) val)
  (lambda (f x) (apply-val f (the vals (cons x nil)))))

;;; ------------------------------------------------------------- identity

;; `eq?` of two `other`s: unit is unit, and a mutable one is itself; any
;; other (a product, a sum, the control) #f, which `eq?` allows of
;; immutable data.
(define* ev-other-eq? (subr pure (other other) bool)
  (lambda (a b)
    (tagcase a
      (o-unit () (tagcase b (o-unit () #t) (else y #f)))
      (o-icell (f c) (tagcase b (o-icell (g d) (eq? f g)) (else y #f)))
      (o-blob (fs bs) (tagcase b (o-blob (gs cs) (eq? fs gs)) (else y #f)))
      (else y #f))))
;; `eq?` of two values, as the machines have it: the same mutable object;
;; atoms the same word; not a procedure, an `f64` or an `f32`.
(define* ev-eq? (subr pure (val val) bool)
  (lambda (a b)
    (typecase a
      (procedure f #f) (f64 x #f) (f32 x #f)
      (sum o (typecase b (sum p (ev-other-eq? o p)) (else #f)))
      (else (eq? a b)))))

;; Quoted data interned (TODO §51), as the heap interns them
;; (`Heap::intern_datum`): a pair found by its interned parts, a string by
;; its characters; so a quote is one value each time, and equal quotes one.
(define ev-interned (ref vals @v) (new nil))
;; Whether `a`, interned, is what `b`, its parts interned, is.
(define* ev-same-datum? (subr (maxeff (read @v) (alloc @v)) (val val) bool)
  (lambda (a b)
    (cond ((pair? a)
           (and (pair? b) (ev-eq? (car a) (car b)) (ev-eq? (cdr a) (cdr b))))
          ((string? a) (and (string? b) (string=? a b)))
          (else #f))))
;; The interned value of `is` that `c` is, or none.
(define* ev-interned-as (subr (maxeff (read @globals) (read @v) (alloc @v) spin) (vals val) vals)
  (lambda (is c)
    (cond ((null? is) nil)
          ((ev-same-datum? (car is) c) (the vals (cons (car is) nil)))
          (else (ev-interned-as (cdr is) c)))))
;; `c` interned: the value equal to it, or it, interned from now on.
(define* ev-intern-as (subr (maxeff stores spin) (val) val)
  (lambda (c)
    (let ((found (ev-interned-as (get ev-interned) c)))
      (if (null? found) (begin (set ev-interned (cons c (get ev-interned))) c) (car found)))))
(define* ev-intern (subr (maxeff stores spin) (val) val)
  (lambda (v)
    (cond ((pair? v)
           (let ((a (ev-intern (car v))) (d (ev-intern (cdr v))))
             (ev-intern-as (if (and (ev-eq? a (car v)) (ev-eq? d (cdr v))) v (cons a d)))))
          ((string? v) (ev-intern-as v))
          (else v))))

;;; ------------------------------------------------------------- showing
;;; As Scheme's writer shows what the lowered program computes.

;; How many fields `fs` has.
(define* ev-count (subr (maxeff (read @v) spin) (vfields) int)
  (lambda (fs) (if (null? fs) 0 (+ 1 (ev-count (cdr fs))))))
;; How Scheme writes a bloblet of `n` fields and `m` bytes.
(define* show-bloblet (subr (read @globals) (int int) string)
  (lambda (n m) (k-cat5 "#<bloblet " (int->string n) " fields " (int->string m) " bytes>")))
(define* show-other (subr (maxeff (read @globals) (read @v) spin) (other) string)
  (lambda (o)
    (tagcase o
      (o-unit () "#u")
      (o-product (fs) (k-cat3 "#<product of " (int->string (ev-count fs)) ">"))
      (o-sum (t x) (k-cat3 "#<sum " (symbol->string t) ">"))
      (o-icell (f c) "#<bloblet 3 fields 0 bytes>")
      (o-blob (fs bs) (show-bloblet (+ 1 (array-length fs)) (array-length bs)))
      (o-tag (t) "#<prompt-tag>")
      (o-cont (k) "#<continuation>")
      (o-esc (k) "#<continuation>")
      (o-key (k) "#<mark-key>"))))
;; A value as Scheme would write it. A list may be cyclic (built with
;; `set-cdr!`), so the walk has fuel: past it, `…`. The car of a pair gets
;; half what is left, so a cycle through cars and cdrs alike stays bounded.
(define-rec
  (show-val (subr (maxeff (read @globals) (read @v) (alloc @v) spin) (val) string)
    (lambda (v) (show-val-in v 10000)))
  (show-val-in (subr (maxeff (read @globals) (read @v) (alloc @v) spin) (val int) string)
    (lambda (v fuel)
      (typecase v
        (int n (int->string n))
        (bool b (if b "#t" "#f"))
        (string s (k-cat3 "\"" s "\""))
        (char c (string-append "#\\" (char->string c)))
        (symbol s (symbol->string s))
        (nil z "()")
        (pair p (if (<= fuel 0) "…" (k-cat3 "(" (show-items p fuel) ")")))
        (procedure f "#<procedure>")
        (bloblet a (show-bloblet (+ 1 (array-length a)) 0))
        (f64 x (f64->string x))
        (f32 x (f32->string x))
        (box r "#<box>")
        (sum o (show-other o))
        (else "?"))))
  ;; A list's elements, space-separated, and a dotted tail.
  (show-items (subr (maxeff (read @globals) (read @v) (alloc @v) spin) ((pairof val val @v) int)
                    string)
    (lambda (p fuel)
      (let ((head (show-val-in (car p) (quotient fuel 2))) (tail (cdr p)))
        (cond ((null? tail) head)
              ((pair? tail)
               (if (<= fuel 1)
                   (string-append head " …")
                   (k-cat3 head " " (show-items tail (- fuel 1)))))
              (else (k-cat3 head " . " (show-val-in tail (- fuel 1)))))))))
