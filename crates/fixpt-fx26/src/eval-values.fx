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
;;; A file of one expression (`load-input`, `TODO.md` §68): what makes the
;;; module, which the conductor (`conductor.fx`) applies to the checker's
;;; types module.

;; Its types, and the signatures of what it is given (`eval-types.fx`).
(let* ((eval-types (load-module "fx26:eval-types.fx"))
       (check-types-types (load-module "fx26:check-types-types.fx")))
  ;; What it is given: the checker's types module (`check-types.fx`).
  (lambda ((check-types (select check-types-types check-types-sig)))
    (module
(hide (include eval-types))
;; What it uses of the modules it is given: all of each, hidden.
(hide (include check-types))

;; Unit: one value, made once.
(define the-unit val (o-unit))

(define eval-tag (prompt-tag eresult eresult (maxeff runs spin) @x)
  (make-continuation-prompt-tag))

(define efail (->* (string) void)
  (lambda (message)
    ;; A task of a monitored process: the failure its watcher's, the task
    ;; left by an abort to the scheduler's prompt (`TASK_FAILED`).
    (typecase ((proj %sched string unit val) 38 message #u)
      (sum o
        (tagcase o
          (o-tag (g) (abort-current-continuation g the-unit))
          (else y (abort-current-continuation eval-tag (ev-err message)))))
      (else (abort-current-continuation eval-tag (ev-err message))))))

;; Fails: `what` is expected.
(define efail-expected (->* (string) void)
  (lambda (what) (efail (string-append what " is expected"))))

;; `v`, a bytevector; or fails.
(define as-bytes (->* (val) (bytevectorof @v))
  (lambda (v)
    (tagcase (as-other v "a bytevector") (o-bytes (b) b) (else y (efail-expected "a bytevector")))))

;; `v`, an `other`; or fails, `what` being expected.
(define as-other (->* (val string) other)
  (lambda (v what) (typecase v (sum o o) (else (efail-expected what)))))

(define as-int (->* (val) int)
  (lambda (v) (if (int? v) v (efail-expected "an int"))))

(define as-bool (->* (val) bool)
  (lambda (v) (if (bool? v) v (efail-expected "a bool"))))

;; `v`, a string: one made at a region copied, to be read as a `string`.
(define as-str (->* (val) string)
  (lambda (v)
    (if (string? v)
        v
        (tagcase (as-other v "a string")
          (o-mstr (m) (list->string (string->list m)))
          (else y (efail-expected "a string"))))))

;; `v`, a string made at a region, to be written; or fails.
(define as-mstr (->* (val) (stringof @v))
  (lambda (v)
    (tagcase (as-other v "a string") (o-mstr (m) m) (else y (efail-expected "a string")))))

(define as-char (->* (val) char)
  (lambda (v) (if (char? v) v (efail-expected "a char"))))

(define as-f64 (->* (val) f64)
  (lambda (v) (if (f64? v) v (efail-expected "an f64"))))

(define as-sym (->* (val) symbol)
  (lambda (v) (if (symbol? v) v (efail-expected "a symbol"))))

(define as-keyword (->* (val) keyword)
  (lambda (v) (if (keyword? v) v (efail-expected "a keyword"))))

;; `v`, a pair; or fails, as the machines say a `car` or `cdr` of a
;; non-pair does (`DONE.md` §85).
(define as-pair (->* (val) (pairof val val @v))
  (lambda (v) (if (pair? v) v (efail "car or cdr of a non-pair"))))

(define as-array (->* (val) (arrayof val @v))
  (lambda (v) (if (array? v) v (efail-expected "an array"))))

(define as-f32 (->* (val) f32)
  (lambda (v) (if (f32? v) v (efail-expected "an f32"))))

(define as-ref (->* (val) vcell)
  (lambda (v) (if (ref? v) v (efail-expected "a reference"))))

(define as-tag (->* (val) vtag)
  (lambda (v)
    (tagcase (as-other v "a prompt tag") (o-tag (t) t) (else y (efail-expected "a prompt tag")))))

(define as-key (->* (val) (mark-key val @x))
  (lambda (v)
    (tagcase (as-other v "a mark key") (o-key (k) k) (else y (efail-expected "a mark key")))))

(define as-cont (->* (val) vcont)
  (lambda (v)
    (let ((what "a composable continuation"))
      (tagcase (as-other v what) (o-cont (k) k) (else y (efail-expected what))))))

;; A product's fields, by label.
(define as-fields (->* (val string) vfields)
  (lambda (v what)
    (tagcase (as-other v what) (o-product (fs) fs) (else y (efail-expected what)))))

;; The arguments of a call, as the list value a `vlambda` is given.
(define vals->val (->* (vals) val)
  (lambda (xs) (if (null? xs) nil (cons (car xs) (vals->val (cdr xs))))))

(define list->val (->* ((listof val @x)) val)
  (lambda (xs) (if (null? xs) nil (cons (car xs) (list->val (cdr xs))))))

;; A list value's elements, as the arguments `apply` gives: a list of its
;; own, which nothing else can write (F11), as the machines copy it. With
;; no `eq?` to find a cycle by, a cyclic list is not ended: the machines'
;; is an error (`programs/native/apply-cyclic.fx`, which this never runs).
(define val->vals (->* (val) vals)
  (lambda (v) (if (pair? v) (cons (car v) (val->vals (cdr v))) nil)))

;; Argument `i` of `xs`.
(define ev-arg (->* (vals int) val)
  (lambda (xs i)
    (cond ((null? xs) (efail "too few arguments"))
          ((= i 0) (car xs))
          (else (ev-arg (cdr xs) (- i 1))))))

;; `f` applied to `xs`: a procedure called; a continuation resumed.
(define apply-val (->* (val vals) val)
  (lambda (f xs)
    (typecase f
      (procedure p (p xs))
      (sum o
        (tagcase o
          (o-cont (k) (k (ev-arg xs 0)))
          (o-once (k spent)
            (if (get spent)
                (efail "a one-shot continuation resumed twice")
                (begin (set spent #t) (k (ev-arg xs 0)))))
          (o-esc (k) (k (ev-arg xs 0)))
          (else y (efail "not a subroutine"))))
      (else (efail "not a subroutine")))))

(define apply1 (->* (val val) val)
  (lambda (f x) (apply-val f (the vals (cons x nil)))))

;; Whether `o` and `p` are the same bloblet, a blobref's owner.
(define ev-same-blob? (->* (val val) bool)
  (lambda (o p)
    (typecase o
      (sum x
        (typecase p
          (sum y
            (tagcase x
              (o-blob (fs bs) (tagcase y (o-blob (gs cs) (eq? fs gs)) (else z #f)))
              (else z #f)))
          (else #f)))
      (else #f))))
;; `eq?` of two `other`s: unit is unit, and a mutable one is itself; any
;; other (a product, a sum, the control) #f, which `eq?` allows of
;; immutable data.
(define ev-other-eq? (->* (other other) bool)
  (lambda (a b)
    (tagcase a
      (o-unit () (tagcase b (o-unit () #t) (else y #f)))
      (o-icell (c) (tagcase b (o-icell (d) (eq? c d)) (else y #f)))
      (o-blob (fs bs) (tagcase b (o-blob (gs cs) (eq? fs gs)) (else y #f)))
      ;; Owner and offset, as the machines' one word.
      (o-bref (o i) (tagcase b (o-bref (p j) (and (= i j) (ev-same-blob? o p))) (else y #f)))
      (o-bytes (x) (tagcase b (o-bytes (y) (eq? x y)) (else y #f)))
      (o-vec (x) (tagcase b (o-vec (y) (eq? x y)) (else y #f)))
      (o-eqt (x) (tagcase b (o-eqt (y) (eq? x y)) (else y #f)))
      (o-mstr (x) (tagcase b (o-mstr (y) (eq? x y)) (else y #f)))
      (o-host (x) (tagcase b (o-host (y) (eq? x y)) (else y #f)))
      (else y #f))))

;; `eq?` of two values, as the machines have it: the same mutable object;
;; atoms the same word; not a procedure, an `f64` or an `f32`.
(define ev-eq? (->* (val val) bool)
  (lambda (a b)
    (typecase a
      (procedure f #f) (f64 x #f) (f32 x #f)
      (sum o (typecase b (sum p (ev-other-eq? o p)) (else #f)))
      (else (eq? a b)))))

;; The program's scheduler's `preempt` (`fx26:processes.fx`), one of the
;; evaluator's values, which this evaluator calls at its own polls: kept
;; here, not given to the runtime, whose machines would call it as theirs
;; (`ev-sched`). And how many applications until the next poll.
(define ev-preempt (ref val @v) (new #f))
(define ev-ticks (ref int @v) (new 0))
(define ev-preempt-set! (->* (val) unit)
  (lambda (f) (set ev-preempt f)))
;; A poll, at each application: every 4096th, the program's `preempt`
;; called, if the runtime says the scheduler would have another task run
;; (`fixpt_runtime::sched`, operation 31).
(define ev-poll (->* () unit)
  (lambda ()
    (let ((t (- (get ev-ticks) 1)))
      (if (> t 0)
          (set ev-ticks t)
          (begin
            (set ev-ticks 4096)
            (if (and (procedure? (get ev-preempt)) ((proj %sched val val bool) 31 #f #f))
                (begin (apply-val (get ev-preempt) nil) ((proj %sched val val val) 32 #f #f) #u)
                #u))))))

;; Quoted data interned (TODO §51), as the heap interns them
;; (`Heap::intern_datum`): a pair found by its interned parts, a string by
;; its characters, a float by its bits and a vector by its elements; so a
;; quote is one value each time, and equal quotes one. A table, as the
;; heap's: buckets by a hash of each datum's parts, each entry a hash and
;; its value, so that interning takes time in proportion to what is
;; interned (TODO §229).
(define-type ev-entries (listof (pairof int val @v) @v))
(define ev-interned (ref (arrayof ev-entries @v) @v)
  (new (the (arrayof ev-entries @v) (make-array 64 (the ev-entries nil)))))
(define ev-interned-count (ref int @v) (new 0))
(define ev-mix (->* (int int) int)
  (lambda (h x) (modulo (+ (* h 31) (modulo x 1073741789)) 1073741789)))
;; An atom's hash, by what it is: what interning is keyed by.
(define ev-atom-hash (->* (val) int)
  (lambda (v)
    (typecase v
      (int n (ev-mix 2 n)) (char c (ev-mix 3 (char->integer c))) (bool b (if b 5 7))
      (string s (ev-mix 11 (string-hash s))) (symbol s (ev-mix 13 (symbol-name-hash s)))
      (keyword k (ev-mix 17 (symbol-name-hash (keyword->symbol k))))
      (f64 x (ev-mix 19 (string-hash (f64->string x))))
      (else 0))))

;; Whether parts `a` and `b`, interned, are one: the same object, or a
;; float of the same bits, as the heap keeps one of each.
(define ev-same-part? (->* (val val) bool)
  (lambda (a b)
    (typecase a
      (f64 x (typecase b (f64 y (u64= (f64->bits x) (f64->bits y))) (else #f)))
      (else (ev-eq? a b)))))
;; Whether vectors `xs` and `ys`, their elements interned, are one, from `i`.
(define ev-same-elements? (->* ((arrayof val @v) (arrayof val @v) int) bool)
  (lambda (xs ys i)
    (or (< i 0)
        (and (ev-same-part? (array-ref xs i) (array-ref ys i)) (ev-same-elements? xs ys (- i 1))))))

;; Whether `a`, interned, is what `b`, its parts interned, is.
(define ev-same-datum? (->* (val val) bool)
  (lambda (a b)
    (cond ((pair? a)
           (and (pair? b) (ev-same-part? (car a) (car b)) (ev-same-part? (cdr a) (cdr b))))
          ((string? a) (and (string? b) (string=? a b)))
          ((f64? a) (ev-same-part? a b))
          (else
            (typecase a
              (sum o
                (tagcase o
                  (o-vec (xs)
                    (typecase b
                      (sum p (tagcase p
                               (o-vec (ys) (and (= (array-length xs) (array-length ys))
                                                (ev-same-elements? xs ys (- (array-length xs) 1))))
                               (else y #f)))
                      (else #f)))
                  (else y #f)))
              (else #f))))))

;; The entry of `es` that is `c`, of hash `h`, or none.
(define ev-entry-of (->* (ev-entries val int) ev-entries)
  (lambda (es c h)
    (cond ((null? es) nil)
          ((and (= (car (car es)) h) (ev-same-datum? (cdr (car es)) c)) es)
          (else (ev-entry-of (cdr es) c h)))))
;; Entries `es` into buckets `bs`.
(define ev-rebucket! (->* (ev-entries (arrayof ev-entries @v)) unit)
  (lambda (es bs)
    (if (null? es)
        #u
        (let ((i (modulo (car (car es)) (array-length bs))))
          (begin (array-set! bs i (cons (car es) (array-ref bs i))) (ev-rebucket! (cdr es) bs))))))
;; The table's buckets from `i` down into `bs`.
(define ev-rebucket-all! (->* ((arrayof ev-entries @v) int (arrayof ev-entries @v)) unit)
  (lambda (old i bs)
    (if (< i 0) #u (begin (ev-rebucket! (array-ref old i) bs) (ev-rebucket-all! old (- i 1) bs)))))

;; `c`, of hash `h`, interned: the value equal to it, or it, interned from
;; now on; with its hash.
(define ev-intern-as (->* (val int) (pairof val int @v))
  (lambda (c h)
    (let* ((bs (get ev-interned))
           (i (modulo h (array-length bs)))
           (found (ev-entry-of (array-ref bs i) c h)))
      (if (not (null? found))
          (cons (cdr (car found)) h)
          (begin
            (array-set! bs i (cons (cons h c) (array-ref bs i)))
            (set ev-interned-count (+ (get ev-interned-count) 1))
            (if (> (get ev-interned-count) (* 2 (array-length bs)))
                (let ((more (the (arrayof ev-entries @v)
                                 (make-array (* 4 (array-length bs)) (the ev-entries nil)))))
                  (begin (ev-rebucket-all! bs (- (array-length bs) 1) more) (set ev-interned more)))
                #u)
            (cons c h))))))

;; A list's pairs from `v` on, the last first, onto `acc`; and what ends
;; it.
(define ev-spine (->* (val (listof (pairof val val @v) @v)) (listof (pairof val val @v) @v))
  (lambda (v acc) (if (pair? v) (ev-spine (cdr v) (cons v acc)) acc)))
(define ev-spine-end (->* (val) val)
  (lambda (v) (if (pair? v) (ev-spine-end (cdr v)) v)))
;; Pairs `ps`, the last first, interned over `dh`, the rest interned with
;; its hash: a loop down a list's spine, as the heap's, so that a long list
;; takes no stack.
(define ev-intern-spine
  (->* ((listof (pairof val val @v) @v) (pairof val int @v)) (pairof val int @v))
  (lambda (ps dh)
    (if (null? ps)
        dh
        (let* ((p (car ps)) (ah (ev-interned-h (car p))) (a (car ah)) (d (car dh)))
          (ev-intern-spine
            (cdr ps)
            (ev-intern-as
              (if (and (ev-same-part? a (car p)) (ev-same-part? d (cdr p))) p (cons a d))
              (ev-mix (ev-mix 23 (cdr ah)) (cdr dh))))))))
;; Vector `xs`'s elements, interned, from `i`, into `ys`; the hash of all
;; from `i` on, from `h`.
(define ev-intern-elements! (->* ((arrayof val @v) (arrayof val @v) int int) int)
  (lambda (xs ys i h)
    (if (< i 0)
        h
        (let ((yh (ev-interned-h (array-ref xs i))))
          (begin (array-set! ys i (car yh))
                 (ev-intern-elements! xs ys (- i 1) (ev-mix h (cdr yh))))))))

;; `v` interned, with its hash.
(define ev-interned-h (->* (val) (pairof val int @v))
  (lambda (v)
    (cond ((pair? v) (ev-intern-spine (ev-spine v nil) (ev-interned-h (ev-spine-end v))))
          ((or (string? v) (f64? v)) (ev-intern-as v (ev-atom-hash v)))
          (else
            (typecase v
              (sum o
                (tagcase o
                  (o-vec (xs)
                    (let* ((n (array-length xs))
                           (ys (the (arrayof val @v) (make-array n (the val #f))))
                           (h (ev-intern-elements! xs ys (- n 1) 29)))
                      (ev-intern-as
                        (if (ev-same-elements? xs ys (- n 1)) v (the val (o-vec ys))) h)))
                  (else y (cons v 0))))
              (else (cons v (ev-atom-hash v))))))))
(define ev-intern (->* (val) val) (lambda (v) (car (ev-interned-h v))))

;; How many fields `fs` has.
(define ev-count (->* (vfields) int)
  (lambda (fs) (if (null? fs) 0 (+ 1 (ev-count (cdr fs))))))

;; A bytevector's bytes up to `i`, space-separated as Scheme writes them,
;; before `acc`, those after.
(define show-bytes
  (->* ((bytevectorof @v) int string) string)
  (lambda (b i acc)
    (if (< i 0)
        acc
        (let ((x (int->string (bytevector-u8-ref b i))))
          (show-bytes b (- i 1) (if (string=? acc "") x (k-cat3 x " " acc)))))))

;; A vector's elements up to `i`, space-separated, before `acc`, those after.
(define show-vec (->* ((arrayof val @v) int string) string)
  (lambda (xs i acc)
    (if (< i 0)
        acc
        (let ((x (show-val (array-ref xs i))))
          (show-vec xs (- i 1) (if (string=? acc "") x (k-cat3 x " " acc)))))))

;; How Scheme writes a bloblet of `n` fields and `m` bytes.
(define show-bloblet (->* (int int) string)
  (lambda (n m) (k-cat5 "#<bloblet " (int->string n) " fields " (int->string m) " bytes>")))

(define show-other (->* (other) string)
  (lambda (o)
    (tagcase o
      (o-unit () "#u")
      (o-product (fs) (k-cat3 "#<product of " (int->string (ev-count fs)) ">"))
      (o-sum (t x) (k-cat3 "#<sum " (symbol->string t) ">"))
      (o-icell (c) "#<icell 4 fields 0 bytes>")
      (o-blob (fs bs) (show-bloblet (+ 1 (array-length fs)) (array-length bs)))
      (o-bref (o i) (k-cat3 "#<suffix-ref bloblet +" (int->string i) ">"))
      (o-bytes (b) (k-cat3 "#u8(" (show-bytes b (- (bytevector-length b) 1) "") ")"))
      (o-vec (xs) (k-cat3 "#(" (show-vec xs (- (array-length xs) 1) "") ")"))
      (o-eqt (es) "#<eqtable>")
      (o-mstr (m) (k-cat3 "\"" (list->string (string->list m)) "\""))
      (o-tag (t) "#<prompt-tag>")
      (o-cont (k) "#<continuation>")
      (o-once (k s) "#<continuation>")
      (o-esc (k) "#<continuation>")
      (o-key (k) "#<mark-key>")
      (o-host (h) "#<session>"))))

;; A value as Scheme would write it. A list may be cyclic (built with
;; `set-cdr!`), so the walk has fuel: past it, `…`. The car of a pair gets
;; half what is left, so a cycle through cars and cdrs alike stays bounded.
(define-rec
  (show-val (->* (val) string)
    (lambda (v) (show-val-in v 10000)))
  (show-val-in (->* (val int) string)
    (lambda (v fuel)
      (typecase v
        (int n (int->string n))
        (bool b (if b "#t" "#f"))
        (string s (k-cat3 "\"" s "\""))
        (char c (string-append "#\\" (char->string c)))
        (symbol s (symbol->string s))
        (keyword k (string-append "#:" (symbol->string (keyword->symbol k))))
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
  (show-items (->* ((pairof val val @v) int) string)
    (lambda (p fuel)
      (let ((head (show-val-in (car p) (quotient fuel 2))) (tail (cdr p)))
        (cond ((null? tail) head)
              ((pair? tail)
               (if (<= fuel 1)
                   (string-append head " …")
                   (k-cat3 head " " (show-items tail (- fuel 1)))))
              (else (k-cat3 head " . " (show-val-in tail (- fuel 1))))))))))))
