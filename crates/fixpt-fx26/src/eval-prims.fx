;;; The FX-26 evaluator's primitives: each standard name the evaluator has,
;;; a procedure of the list of its arguments, in a table by its symbol.
;;; After `eval-values.fx`; `eval-core.fx` looks names up here.
;;; A file of one expression (`load-input`, `TODO.md` §68): what makes the
;;; module, which the conductor (`conductor.fx`) applies to the evaluator's
;;; values, the tables and the checker's types module.

;; Its types, and the signatures of what it is given (`eval-types.fx`).
(let* ((eval-types (load-module "fx26:eval-types.fx"))
       (table-types (load-module "fx26:table-types.fx"))
       (check-types-types (load-module "fx26:check-types-types.fx"))
       (parser-types ((proj (load-module "fx26:parser-types.fx") @s @e @m @c @p))))
  ;; What it is given: the evaluator's values, the tables (`table.fx`) and
  ;; the checker's types module.
  (lambda ((values (select eval-types eval-values-sig))
           (tables (select table-types tables-sig))
           (check-types (select check-types-types check-types-sig)))
    (module
(hide (include eval-types))
(define-type table (select table-types table))
;; A flat array's operand taken apart (`k-array-operand`).
(import parser-types k-array-length k-array-size)
;; What it uses of the modules it is given.
(import values apply-val apply1 as-array as-bool as-bytes ev-preempt-set! as-char as-cont as-f32
        as-f64 as-int as-key as-keyword as-other as-pair as-ref as-str as-sym as-tag efail
        efail-expected
        ev-arg as-mstr ev-eq? ev-intern list->val the-unit val->vals vals->val)
;; What it uses of the modules it is given: all of each, hidden.
(hide (include tables) (include check-types))

(define ev-prims (table symbol val @v) (make-table symbol-hash symbol=?))

;; Primitive `n` is `f`.
(define prim! (->* (symbol vproc) unit)
  (lambda (n f) (table-set! ev-prims n f)))

(define int2 (->* (vals (subr pure (int int) int)) val)
  (lambda (xs f) (f (as-int (ev-arg xs 0)) (as-int (ev-arg xs 1)))))

(define int-cmp (->* (vals (subr pure (int int) bool)) val)
  (lambda (xs f) (f (as-int (ev-arg xs 0)) (as-int (ev-arg xs 1)))))

(define char-cmp (->* (vals (subr pure (char char) bool)) val)
  (lambda (xs f) (f (as-char (ev-arg xs 0)) (as-char (ev-arg xs 1)))))

(define str-cmp (->* (vals (subr pure (string string) bool)) val)
  (lambda (xs f) (f (as-str (ev-arg xs 0)) (as-str (ev-arg xs 1)))))

(define f64-2 (->* (vals (subr pure (f64 f64) f64)) val)
  (lambda (xs f) (f (as-f64 (ev-arg xs 0)) (as-f64 (ev-arg xs 1)))))

(define f64-1 (->* (vals (subr pure (f64) f64)) val)
  (lambda (xs f) (f (as-f64 (ev-arg xs 0)))))

(define f64-cmp (->* (vals (subr pure (f64 f64) bool)) val)
  (lambda (xs f) (f (as-f64 (ev-arg xs 0)) (as-f64 (ev-arg xs 1)))))

(define f64-test (->* (vals (subr pure (f64) bool)) val)
  (lambda (xs f) (f (as-f64 (ev-arg xs 0)))))

(define f32-2 (->* (vals (subr pure (f32 f32) f32)) val)
  (lambda (xs f) (f (as-f32 (ev-arg xs 0)) (as-f32 (ev-arg xs 1)))))

(define f32-1 (->* (vals (subr pure (f32) f32)) val)
  (lambda (xs f) (f (as-f32 (ev-arg xs 0)))))

(define f32-cmp (->* (vals (subr pure (f32 f32) bool)) val)
  (lambda (xs f) (f (as-f32 (ev-arg xs 0)) (as-f32 (ev-arg xs 1)))))

(define f32-test (->* (vals (subr pure (f32) bool)) val)
  (lambda (xs f) (f (as-f32 (ev-arg xs 0)))))

;; `modulo`, `quotient` or `remainder` of `int`s; by zero, the program's
;; failure, as on the machines, not the evaluator's own.
(define int-div (->* (vals (subr pure (int int) int)) val)
  (lambda (xs f) (if (zero? (as-int (ev-arg xs 1))) (efail "division by zero") (int2 xs f))))

(define* ev-int-prims! (subr (maxeff stores spin) () unit)
  (lambda ()
    (begin
      (prim! '+ (lambda (xs) (int2 xs (lambda (a b) (+ a b)))))
      (prim! '- (lambda (xs) (int2 xs (lambda (a b) (- a b)))))
      (prim! '* (lambda (xs) (int2 xs (lambda (a b) (* a b)))))
      (prim! 'modulo (lambda (xs) (int-div xs (lambda (a b) (modulo a b)))))
      (prim! 'quotient (lambda (xs) (int-div xs (lambda (a b) (quotient a b)))))
      (prim! 'remainder (lambda (xs) (int-div xs (lambda (a b) (remainder a b)))))
      (prim! 'max (lambda (xs) (int2 xs (lambda (a b) (max a b)))))
      (prim! 'min (lambda (xs) (int2 xs (lambda (a b) (min a b)))))
      (prim! '= (lambda (xs) (int-cmp xs (lambda (a b) (= a b)))))
      (prim! '< (lambda (xs) (int-cmp xs (lambda (a b) (< a b)))))
      (prim! '> (lambda (xs) (int-cmp xs (lambda (a b) (> a b)))))
      (prim! '<= (lambda (xs) (int-cmp xs (lambda (a b) (<= a b)))))
      (prim! '>= (lambda (xs) (int-cmp xs (lambda (a b) (>= a b)))))
      (prim! 'zero? (lambda (xs) (zero? (as-int (ev-arg xs 0)))))
      (prim! 'bitwise-and (lambda (xs) (int2 xs (lambda (a b) (bitwise-and a b)))))
      (prim! 'bitwise-ior (lambda (xs) (int2 xs (lambda (a b) (bitwise-ior a b)))))
      (prim! 'bitwise-xor (lambda (xs) (int2 xs (lambda (a b) (bitwise-xor a b)))))
      (prim! 'bitwise-not (lambda (xs) (bitwise-not (as-int (ev-arg xs 0)))))
      (prim! 'arithmetic-shift (lambda (xs) (int2 xs (lambda (a b) (arithmetic-shift a b)))))
      (prim! 'int->string (lambda (xs) (int->string (as-int (ev-arg xs 0))))))))

;; `x` wrapped to `bits` bits, two's complement if `signed` (`Width::wrap`).
(define fw-wrap (->* (int bool int) int)
  (lambda (bits signed x)
    (let ((low (bitwise-and x (- (arithmetic-shift 1 bits) 1))))
      (if (and signed (>= low (arithmetic-shift 1 (- bits 1))))
          (- low (arithmetic-shift 1 bits))
          low))))

(define fw-2 (->* (vals int bool (subr pure (int int) int)) val)
  (lambda (xs bits signed f)
    (fw-wrap bits signed (f (as-int (ev-arg xs 0)) (as-int (ev-arg xs 1))))))

;; `quotient` or `remainder`, which truncate as the runtime's do; by zero, a
;; failure, as there.
(define fw-div (->* (vals int bool (subr pure (int int) int)) val)
  (lambda (xs bits signed f)
    (if (zero? (as-int (ev-arg xs 1))) (efail "division by zero") (fw-2 xs bits signed f))))

;; A shift by the count's low bits; right, arithmetic (an unsigned value is
;; not negative, so logical too).
(define fw-shift (->* (vals int bool bool) val)
  (lambda (xs bits signed left)
    (let ((x (as-int (ev-arg xs 0))) (k (bitwise-and (as-int (ev-arg xs 1)) (- bits 1))))
      (fw-wrap bits signed (arithmetic-shift x (if left k (- 0 k)))))))

;; The operation `op` of width `w`: `w` and `op` run together.
(define fw-name (->* (string string) symbol)
  (lambda (w op) (string->symbol (string-append w op))))

(define* ev-width-prims! (subr (maxeff stores spin) (string int bool) unit)
  (lambda (w bits signed)
    (let ((n (lambda ((op string)) (fw-name w op))))
      (begin
        (prim! (n "+") (lambda (xs) (fw-2 xs bits signed (lambda (a b) (+ a b)))))
        (prim! (n "-") (lambda (xs) (fw-2 xs bits signed (lambda (a b) (- a b)))))
        (prim! (n "*") (lambda (xs) (fw-2 xs bits signed (lambda (a b) (* a b)))))
        (prim! (n "-quotient") (lambda (xs) (fw-div xs bits signed (lambda (a b) (quotient a b)))))
        (prim! (n "-remainder")
               (lambda (xs) (fw-div xs bits signed (lambda (a b) (remainder a b)))))
        (prim! (n "-and") (lambda (xs) (fw-2 xs bits signed (lambda (a b) (bitwise-and a b)))))
        (prim! (n "-or") (lambda (xs) (fw-2 xs bits signed (lambda (a b) (bitwise-ior a b)))))
        (prim! (n "-xor") (lambda (xs) (fw-2 xs bits signed (lambda (a b) (bitwise-xor a b)))))
        (prim! (n "<") (lambda (xs) (int-cmp xs (lambda (a b) (< a b)))))
        (prim! (n "<=") (lambda (xs) (int-cmp xs (lambda (a b) (<= a b)))))
        (prim! (n ">") (lambda (xs) (int-cmp xs (lambda (a b) (> a b)))))
        (prim! (n ">=") (lambda (xs) (int-cmp xs (lambda (a b) (>= a b)))))
        (prim! (n "=") (lambda (xs) (int-cmp xs (lambda (a b) (= a b)))))
        (prim! (n "-shl") (lambda (xs) (fw-shift xs bits signed #t)))
        (prim! (n "-shr") (lambda (xs) (fw-shift xs bits signed #f)))
        (prim! (n "-not") (lambda (xs) (fw-wrap bits signed (bitwise-not (as-int (ev-arg xs 0))))))
        (prim! (fw-name "int->" w) (lambda (xs) (fw-wrap bits signed (as-int (ev-arg xs 0)))))
        (prim! (n "->int") (lambda (xs) (as-int (ev-arg xs 0))))))))

;; `string-append`: the strings `xs`, one after another.
(define ev-string-append (->* (vals) string)
  (lambda (xs) (if (null? xs) "" (string-append (as-str (car xs)) (ev-string-append (cdr xs))))))
(define* ev-text-prims! (subr (maxeff stores spin) () unit)
  (lambda ()
    (begin
      (prim! 'not (lambda (xs) (not (as-bool (ev-arg xs 0)))))
      (prim! 'bool=? (lambda (xs) (bool=? (as-bool (ev-arg xs 0)) (as-bool (ev-arg xs 1)))))
      (prim! 'char=? (lambda (xs) (char-cmp xs (lambda (a b) (char=? a b)))))
      (prim! 'char<? (lambda (xs) (char-cmp xs (lambda (a b) (char<? a b)))))
      (prim! 'char<=? (lambda (xs) (char-cmp xs (lambda (a b) (char<=? a b)))))
      (prim! 'char>? (lambda (xs) (char-cmp xs (lambda (a b) (char>? a b)))))
      (prim! 'char>=? (lambda (xs) (char-cmp xs (lambda (a b) (char>=? a b)))))
      (prim! 'char-upcase (lambda (xs) (char-upcase (as-char (ev-arg xs 0)))))
      (prim! 'char->integer (lambda (xs) (char->integer (as-char (ev-arg xs 0)))))
      (prim! 'char-numeric? (lambda (xs) (char-numeric? (as-char (ev-arg xs 0)))))
      (prim! 'integer->char (lambda (xs) (integer->char (as-int (ev-arg xs 0)))))
      (prim! 'char->string (lambda (xs) (char->string (as-char (ev-arg xs 0)))))
      (prim! 'string-append (lambda (xs) (ev-string-append xs)))
      (prim! 'string-length (lambda (xs) (ev-string-length (ev-arg xs 0))))
      (prim! 'string-ref (lambda (xs) (ev-string-ref (ev-arg xs 0) (as-int (ev-arg xs 1)))))
      (prim! 'substring
             (lambda (xs)
               (substring (as-str (ev-arg xs 0)) (as-int (ev-arg xs 1)) (as-int (ev-arg xs 2)))))
      (prim! 'string=? (lambda (xs) (str-cmp xs (lambda (a b) (string=? a b)))))
      (prim! 'string<? (lambda (xs) (str-cmp xs (lambda (a b) (string<? a b)))))
      (prim! 'string<=? (lambda (xs) (str-cmp xs (lambda (a b) (string<=? a b)))))
      (prim! 'string>? (lambda (xs) (str-cmp xs (lambda (a b) (string>? a b)))))
      (prim! 'string>=? (lambda (xs) (str-cmp xs (lambda (a b) (string>=? a b)))))
      (prim! 'string-hash (lambda (xs) (string-hash (as-str (ev-arg xs 0)))))
      (prim! 'string->symbol (lambda (xs) (string->symbol (as-str (ev-arg xs 0)))))
      (prim! 'symbol->string (lambda (xs) (symbol->string (as-sym (ev-arg xs 0)))))
      (prim! 'symbol=? (lambda (xs) (symbol=? (as-sym (ev-arg xs 0)) (as-sym (ev-arg xs 1)))))
      (prim! 'symbol->keyword (lambda (xs) (symbol->keyword (as-sym (ev-arg xs 0)))))
      (prim! 'keyword->symbol (lambda (xs) (keyword->symbol (as-keyword (ev-arg xs 0)))))
      (prim! 'symbol-name-hash (lambda (xs) (symbol-name-hash (as-sym (ev-arg xs 0)))))
      (prim! 'eq? (lambda (xs) (ev-eq? (ev-arg xs 0) (ev-arg xs 1))))
      (prim! 'error (lambda (xs) (efail (as-str (ev-arg xs 0)))))
      (prim! 'assert (lambda (xs) (if (as-bool (ev-arg xs 0)) the-unit (efail "assertion failed"))))
      (prim! 'assume
             (lambda (xs) (if (as-bool (ev-arg xs 0)) the-unit (efail "assumption not met"))))
      (prim! '%quote (lambda (xs) (ev-intern (ev-arg xs 0)))))))

(define ev-symbol? (->* (val) bool)
  (lambda (v) (typecase v (symbol s #t) (sum o (tagcase o (o-unit () #t) (else y #f))) (else #f))))

(define ev-procedure? (->* (val) bool)
  (lambda (v)
    (typecase v
      (procedure p #t)
      (sum o (tagcase o (o-cont (k) #t) (o-once (k s) #t) (o-esc (k) #t) (else y #f)))
      (else #f))))

(define ev-array? (->* (val) bool)
  (lambda (v)
    (typecase v (bloblet a #t) (sum o (tagcase o (o-blob (fs bs) #t) (else y #f))) (else #f))))

(define ev-sum? (->* (val) bool)
  (lambda (v) (typecase v (sum o (tagcase o (o-sum (t x) #t) (else y #f))) (else #f))))

(define ev-product? (->* (val) bool)
  (lambda (v) (typecase v (sum o (tagcase o (o-product (fs) #t) (else y #f))) (else #f))))

(define* ev-shape-prims! (subr (maxeff stores spin) () unit)
  (lambda ()
    (begin
      (prim! 'int? (lambda (xs) (int? (ev-arg xs 0))))
      (prim! 'f64? (lambda (xs) (f64? (ev-arg xs 0))))
      (prim! 'f32? (lambda (xs) (f32? (ev-arg xs 0))))
      (prim! 'char? (lambda (xs) (char? (ev-arg xs 0))))
      (prim! 'bool? (lambda (xs) (bool? (ev-arg xs 0))))
      (prim! 'null? (lambda (xs) (null? (ev-arg xs 0))))
      (prim! 'pair? (lambda (xs) (pair? (ev-arg xs 0))))
      (prim! 'string? (lambda (xs) (ev-string? (ev-arg xs 0))))
      (prim! 'symbol? (lambda (xs) (ev-symbol? (ev-arg xs 0))))
      (prim! 'keyword? (lambda (xs) (keyword? (ev-arg xs 0))))
      (prim! 'procedure? (lambda (xs) (ev-procedure? (ev-arg xs 0))))
      (prim! 'array? (lambda (xs) (ev-array? (ev-arg xs 0))))
      (prim! 'ref? (lambda (xs) (ref? (ev-arg xs 0))))
      (prim! 'sum? (lambda (xs) (ev-sum? (ev-arg xs 0))))
      (prim! 'product? (lambda (xs) (ev-product? (ev-arg xs 0)))))))

;; An i-cell, the machines' own.
(define as-icell (->* (val) (icell val @v))
  (lambda (v)
    (tagcase (as-other v "an i-cell")
      (o-icell (c) c)
      (else y (efail-expected "an i-cell")))))

(define ev-make-icell (->* () val)
  (lambda () (o-icell (the (icell val @v) (make-icell)))))

;; What the scheduler (`fx26:processes.fx`, which a program's processes
;; and `par` load, and this runs) asks of the runtime, `%sched`'s operation
;; `n`: given the machines' i-cell where one is taken, and the one sum an
;; operation makes, the scheduler's prompt tag or none, made one of the
;; program's.
(define ev-sched (->* (vals) val)
  (lambda (xs)
    (let ((n (as-int (ev-arg xs 0))) (a (ev-arg xs 1)) (b (ev-arg xs 2)))
      (cond ((and (= n 14) ((proj %sched (icell val @v) val bool) 10 (as-icell a) b))
             (efail "an i-cell written twice"))
            ((or (= n 10) (= n 11) (= n 14) (= n 15) (= n 22) (= n 34))
             ((proj %sched (icell val @v) val val) n (as-icell a) b))
            ((= n 26) (begin (ev-preempt-set! a) the-unit))
            ((= n 12)
             (tagcase ((proj %sched val val (sumof (some val) (none unit))) n a b)
               (some t (o-sum 'some t))
               (none u (o-sum 'none the-unit))))
            (else ((proj %sched val val val) n a b))))))

(define ev-array-set! (->* (vals) val)
  (lambda (xs)
    (begin (array-set! (as-array (ev-arg xs 0)) (as-int (ev-arg xs 1)) (ev-arg xs 2)) the-unit)))

(define ev-set-car! (->* (vals) val)
  (lambda (xs) (begin (set-car! (as-pair (ev-arg xs 0)) (ev-arg xs 1)) the-unit)))

(define ev-set-cdr! (->* (vals) val)
  (lambda (xs) (begin (set-cdr! (as-pair (ev-arg xs 0)) (ev-arg xs 1)) the-unit)))

(define ev-make-array (->* (val val) val)
  (lambda (n x) (the (arrayof val @v) (make-array (as-int n) x))))

;; Strings at a region (`(stringof r)`): made, read and written in place,
;; a `string` read as it is.
(define ev-make-string (->* (val val) val)
  (lambda (n c) (the val (o-mstr (make-string (as-int n) (as-char c))))))
(define ev-string? (->* (val) bool)
  (lambda (v)
    (or (string? v) (typecase v (sum o (tagcase o (o-mstr (m) #t) (else y #f))) (else #f)))))
(define ev-string-length (->* (val) int)
  (lambda (v) (if (string? v) (string-length v) (string-length (as-mstr v)))))
(define ev-string-ref (->* (val int) char)
  (lambda (v i) (if (string? v) (string-ref v i) (string-ref (as-mstr v) i))))
;; The characters of string `v` before `i` and up to it, onto `acc`, as a
;; list value; and a list value of characters, as a list.
(define ev-chars (->* (val int val) val)
  (lambda (v i acc) (if (< i 0) acc (ev-chars v (- i 1) (cons (ev-string-ref v i) acc)))))
(define ev-char-list (->* (val) (listof char @v))
  (lambda (v) (if (pair? v) (cons (as-char (car v)) (ev-char-list (cdr v))) nil)))
(define* ev-mstring-prims! (subr (maxeff stores spin) () unit)
  (lambda ()
    (let ((n (lambda ((xs vals) (i int)) (as-int (ev-arg xs i))))
          (m (lambda ((xs vals) (i int)) (as-mstr (ev-arg xs i)))))
      (begin
        (prim! 'make-string (lambda (xs) (ev-make-string (ev-arg xs 0) (ev-arg xs 1))))
        (prim! 'string->list
               (lambda (xs) (let ((v (ev-arg xs 0))) (ev-chars v (- (ev-string-length v) 1) nil))))
        (prim! 'list->string (lambda (xs) (list->string (ev-char-list (ev-arg xs 0)))))
        (prim! 'string-set!
               (lambda (xs)
                 (begin (string-set! (m xs 0) (n xs 1) (as-char (ev-arg xs 2))) the-unit)))
        (prim! 'string-fill!
               (lambda (xs) (begin (string-fill! (m xs 0) (as-char (ev-arg xs 1))) the-unit)))
        ;; A copy from either kind.
        (prim! 'string-copy
               (lambda (xs)
                 (let ((from (ev-arg xs 0)))
                   (the val (o-mstr (if (string? from)
                                        (string-copy from (n xs 1) (n xs 2))
                                        (string-copy (as-mstr from) (n xs 1) (n xs 2))))))))
        (prim! 'string-copy!
               (lambda (xs)
                 (let ((from (ev-arg xs 2)))
                   (begin
                     (if (string? from)
                         (string-copy! (m xs 0) (n xs 1) from (n xs 3) (n xs 4))
                         (string-copy! (m xs 0) (n xs 1) (as-mstr from) (n xs 3) (n xs 4)))
                     the-unit))))))))

;; Bytevectors (`TODO.md` §84), the machines' own, with the operations
;; the program has: an `i8` or `u8` is the int it stands for.
(define* ev-bytes-prims! (subr (maxeff stores spin) () unit)
  (lambda ()
    (let ((b (lambda ((xs vals) (i int)) (as-bytes (ev-arg xs i))))
          (n (lambda ((xs vals) (i int)) (as-int (ev-arg xs i))))
          (made (lambda ((b (bytevectorof @v))) (the val (o-bytes b)))))
      (begin
        (prim! 'make-bytevector
               (lambda (xs) (made (make-bytevector (n xs 0) (int->u8 (n xs 1))))))
        (prim! 'bytevector-length (lambda (xs) (bytevector-length (b xs 0))))
        (prim! 'bytevector-u8-ref (lambda (xs) (u8->int (bytevector-u8-ref (b xs 0) (n xs 1)))))
        (prim! 'bytevector-u8-set!
               (lambda (xs)
                 (begin (bytevector-u8-set! (b xs 0) (n xs 1) (int->u8 (n xs 2))) the-unit)))
        (prim! 'bytevector-copy
               (lambda (xs) (made (bytevector-copy (b xs 0) (n xs 1) (n xs 2)))))
        (prim! 'bytevector-copy!
               (lambda (xs)
                 (begin (bytevector-copy! (b xs 0) (n xs 1) (b xs 2) (n xs 3) (n xs 4)) the-unit)))
        (prim! 'bytevector=? (lambda (xs) (bytevector=? (b xs 0) (b xs 1))))
        (prim! 'string->utf8 (lambda (xs) (made (string->utf8 (as-str (ev-arg xs 0))))))
        (prim! 'utf8->string
               (lambda (xs)
                 (tagcase (utf8->string (b xs 0))
                   (text s (the val (o-sum 'text s)))
                   (bad k (the val (o-sum 'bad k))))))))))

;; `(sum failed e)`, `e` an `io-error`, as the evaluator's value: a
;; product of its kind and detail.
(define ev-io-failed (->* (io-error) val)
  (lambda (e)
    (let ((kind (tagcase (extract e kind)
                  (not-found u 'not-found) (permission-denied u 'permission-denied)
                  (already-exists u 'already-exists) (not-a-directory u 'not-a-directory)
                  (is-a-directory u 'is-a-directory) (broken-pipe u 'broken-pipe)
                  (invalid-data u 'invalid-data) (other u 'other))))
      (the val
        (o-sum 'failed
               (o-product (list (cons 'kind (the val (o-sum kind the-unit)))
                                (cons 'detail (the val (extract e detail))))))))))
;; What an I/O primitive gave, as the evaluator's value: `(sum done #u)`,
;; or a failure.
(define ev-io-result (->* ((sumof (done unit) (failed io-error))) val)
  (lambda (r) (tagcase r (done u (the val (o-sum 'done the-unit))) (failed e (ev-io-failed e)))))
;; What a terminal's primitive gave, as the evaluator's value.
(define ev-terminal-result
  (->* ((sumof (done unit) (not-a-terminal unit) (failed io-error))) val)
  (lambda (r)
    (tagcase r
      (done u (the val (o-sum 'done the-unit)))
      (not-a-terminal u (the val (o-sum 'not-a-terminal the-unit)))
      (failed e (ev-io-failed e)))))
;; A terminal's size, `(productof (rows int) (columns int))`, as the
;; evaluator's value.
(define ev-size (->* (int int) val)
  (lambda (rows columns)
    (the val (o-product (list (cons 'rows (the val rows)) (cons 'columns (the val columns)))))))
;; What `file-info` gave (Heist's F5), as the evaluator's value.
(define-type ev-file-kind (sumof (file unit) (directory unit) (symlink unit) (other unit)))
(define ev-file-info
  (->* ((productof (kind ev-file-kind) (size int) (modified int) (mode int))) val)
  (lambda (i)
    (let ((kind (tagcase (extract i kind)
                  (file u 'file) (directory u 'directory) (symlink u 'symlink) (other u 'other))))
      (the val (o-product (list (cons 'kind (the val (o-sum kind the-unit)))
                                (cons 'size (the val (extract i size)))
                                (cons 'modified (the val (extract i modified)))
                                (cons 'mode (the val (extract i mode)))))))))
;; A `stage-failure` refusing, with `message`, as the evaluator's value.
(define ev-stage-refused (->* (string) val)
  (lambda (message)
    (the val (o-product (list (cons 'kind (the val (o-sum 'refused the-unit)))
                              (cons 'message (the val message))
                              (cons 'start (the val 0))
                              (cons 'end (the val 0)))))))
;; Strings `ns`, as the evaluator's list of them.
(define ev-strings (->* ((listof string @v)) val)
  (lambda (ns) (if (null? ns) nil (cons (car ns) (ev-strings (cdr ns))))))

;; The evaluator's list of strings `v`, as one of strings.
(define ev-string-list (->* (val) (listof string @v))
  (lambda (v)
    (if (null? v) nil (cons (as-str (car (as-pair v))) (ev-string-list (cdr (as-pair v)))))))

;; The program's I/O (`TODO.md` §84), done by the primitives themselves.
;; Syscalls (`docs/research/syscalls.md`): this evaluator's own, a runtime
;; of its own, has the four Fixpt's runtime has, as it has them
;; (`fixpt_runtime::syscall`): each host name's type in canonical form, ""
;; for one it has not.
(define ev-sys-type (->* (string) string)
  (lambda (h)
    (cond ((string=? h "code:exec-view/1")
           (string-append "(poly ((r1 region)) (subr (maxeff (io sys) (write r1)) "
                          "((flatarrayof i64 r1) int int) int))"))
          ((string=? h "code:page-words/1") "(subr (io sys) () int)")
          ((string=? h "code:flush/1")
           (string-append "(poly ((r1 region)) (subr (maxeff (io sys) (read r1)) "
                          "((flatarrayof i64 r1) int int) unit))"))
          ((string=? h "kayak:string-utf8-length/1") "(subr pure (string) int)")
          (else ""))))
(define ev-sys-has? (->* (string string) bool)
  (lambda (h t) (let ((u (ev-sys-type h))) (and (not (string=? u "")) (string=? u t)))))
;; A required one's check, `label` naming it: `syscall NAME ("HOST")`.
(define ev-sys-require (->* (string string string) val)
  (lambda (label h t)
    (let ((u (ev-sys-type h)))
      (cond ((string=? u "") (efail (string-append label ": this runtime has none")))
            ((string=? u t) the-unit)
            (else (efail (string-append label ": declared " t "; this runtime's is " u)))))))
;; A call, its label, host name and type first: the page's words, and a
;; string's length in UTF-8, asked of the runtime this runs on; no view of
;; an array, which moves (-1); nothing to flush.
(define ev-syscall (->* (vals) val)
  (lambda (xs)
    (let ((label (as-str (ev-arg xs 0))) (h (as-str (ev-arg xs 1))) (t (as-str (ev-arg xs 2))))
      (cond ((not (ev-sys-has? h t))
             (efail (string-append label ": not available on this runtime")))
            ((string=? h "code:page-words/1") (the int (%syscall0 label h t)))
            ((string=? h "kayak:string-utf8-length/1")
             ((the (subr pure (string string string string) int) %syscall1)
              label h t (as-str (ev-arg xs 3))))
            ((string=? h "code:exec-view/1") -1)
            (else the-unit)))))

(define* ev-io-prims! (subr (maxeff stores spin) () unit)
  (lambda ()
    (begin
      (prim! 'write-out (lambda (xs) (ev-io-result (write-out (as-str (ev-arg xs 0))))))
      (prim! 'write-err (lambda (xs) (ev-io-result (write-err (as-str (ev-arg xs 0))))))
      (prim! 'exit (lambda (xs) (exit (as-int (ev-arg xs 0)))))
      (prim! 'read-line
             (lambda (xs)
               (tagcase (read-line)
                 (line s (the val (o-sum 'line s)))
                 (eof u (the val (o-sum 'eof the-unit)))
                 (failed e (ev-io-failed e)))))
      (prim! 'read-byte
             (lambda (xs)
               (tagcase (read-byte)
                 (byte k (the val (o-sum 'byte (u8->int k))))
                 (eof u (the val (o-sum 'eof the-unit)))
                 (failed e (ev-io-failed e)))))
      (prim! 'read-bytes
             (lambda (xs)
               (tagcase (read-bytes (as-bytes (ev-arg xs 0)) (as-int (ev-arg xs 1))
                                    (as-int (ev-arg xs 2)))
                 (count k (the val (o-sum 'count k)))
                 (eof u (the val (o-sum 'eof the-unit)))
                 (failed e (ev-io-failed e)))))
      (prim! 'stdin-ready? (lambda (xs) (stdin-ready?)))
      (prim! 'terminal-raw (lambda (xs) (ev-terminal-result (terminal-raw))))
      (prim! 'terminal-restore (lambda (xs) (ev-terminal-result (terminal-restore))))
      (prim! 'terminal-size
             (lambda (xs)
               (tagcase (terminal-size)
                 (size z (the val (o-sum 'size (ev-size (extract z rows) (extract z columns)))))
                 (not-a-terminal u (the val (o-sum 'not-a-terminal the-unit)))
                 (failed e (ev-io-failed e)))))
      ;; Code a program makes (`TODO.md` §97): none here, so none runs.
      (prim! 'native-code? (lambda (xs) #f))
      (prim! '%syscall-available?
             (lambda (xs) (ev-sys-has? (as-str (ev-arg xs 0)) (as-str (ev-arg xs 1)))))
      (prim! '%syscall-require
             (lambda (xs)
               (ev-sys-require (as-str (ev-arg xs 0)) (as-str (ev-arg xs 1))
                               (as-str (ev-arg xs 2)))))
      (prim! '%syscall0 ev-syscall) (prim! '%syscall1 ev-syscall) (prim! '%syscall2 ev-syscall)
      (prim! '%syscall3 ev-syscall) (prim! '%syscall4 ev-syscall) (prim! '%syscall5 ev-syscall)
      (prim! '%syscall6 ev-syscall)
      (prim! 'native-convention
             (lambda (xs) (ev-strings (the (listof string @v) (native-convention)))))
      (prim! 'seal-code (lambda (xs) (efail "seal-code: this machine runs no native code")))
      (prim! 'native-procedure
             (lambda (xs) (efail "native-procedure: this machine runs no native code")))
      ;; `stage` (`docs/research/eval.md`) is run by the evaluator itself, at
      ;; the form (`eval-core.fx`'s `ev-stage`); `%stage` is named only as
      ;; its operator, so this is never reached.
      (prim! '%stage
             (lambda (xs)
               (the val (o-sum 'failed (ev-stage-refused "`%stage` is called only as `stage`")))))
      ;; A bound made of exact evidence (`docs/fx26.md`, "Evidence"): the
      ;; same text.
      (prim! 'effect-bound (lambda (xs) (ev-arg xs 0)))
      (prim! 'type-bound (lambda (xs) (ev-arg xs 0)))
      ;; Sessions: `eval-core.fx`'s, but `%session-check`, named only as
      ;; `session-check`'s operator (`ev-session-check`).
      (prim! '%session-check
             (lambda (xs)
               (the val (o-sum 'failed (ev-stage-refused
                                        "`%session-check` is called only as `session-check`")))))
      (prim! 'clock (lambda (xs) (clock)))
      (prim! 'sleep-until
             (lambda (xs) (begin (sleep-until (int->i64 (as-int (ev-arg xs 0)))) the-unit)))
      (prim! 'args (lambda (xs) (ev-strings (the (listof string @v) (args)))))
      (prim! 'read-file
             (lambda (xs)
               (tagcase (the (sumof (data (bytevectorof @v)) (failed io-error))
                             (read-file (as-str (ev-arg xs 0))))
                 (data b (the val (o-sum 'data (o-bytes b))))
                 (failed e (ev-io-failed e)))))
      (prim! 'type-at
             (lambda (xs) (type-at (as-str (ev-arg xs 0)) (as-int (ev-arg xs 1)))))
      (prim! 'list-dir
             (lambda (xs)
               (tagcase (the (sumof (names (listof string @v)) (failed io-error))
                             (list-dir (as-str (ev-arg xs 0))))
                 (names ns (the val (o-sum 'names (ev-strings ns))))
                 (failed e (ev-io-failed e)))))
      (prim! 'write-file
             (lambda (xs)
               (ev-io-result (write-file (as-str (ev-arg xs 0)) (as-bytes (ev-arg xs 1))))))
      ;; The evaluator's heap is no program's a resumed run could start
      ;; (`TODO.md` §189): a dump fails here.
      (prim! 'dump-heap!
             (lambda (xs)
               (the val
                 (o-sum 'failed
                        (o-product (list (cons 'kind (the val (o-sum 'other the-unit)))
                                         (cons 'detail
                                               (the val "this machine cannot dump its heap"))))))))
      ;; Heist's (`FIXPT-CHANGES.md` F4).
      (prim! 'process-start
             (lambda (xs)
               (tagcase (the (sumof (started int) (failed io-error))
                             (process-start (ev-string-list (ev-arg xs 0)) (as-str (ev-arg xs 1))))
                 (started p (the val (o-sum 'started p)))
                 (failed e (ev-io-failed e)))))
      (prim! 'process-output (lambda (xs) (process-output (as-int (ev-arg xs 0)))))
      (prim! 'process-status
             (lambda (xs)
               (tagcase (process-status (as-int (ev-arg xs 0)))
                 (running u (the val (o-sum 'running the-unit)))
                 (exited c (the val (o-sum 'exited c)))
                 (signalled c (the val (o-sum 'signalled c)))
                 (unknown u (the val (o-sum 'unknown the-unit))))))
      (prim! 'process-write
             (lambda (xs)
               (ev-io-result (process-write (as-int (ev-arg xs 0)) (as-str (ev-arg xs 1))))))
      (prim! 'process-close-input
             (lambda (xs) (begin (process-close-input (as-int (ev-arg xs 0))) the-unit)))
      (prim! 'process-signal
             (lambda (xs)
               (begin (process-signal (as-int (ev-arg xs 0)) (as-int (ev-arg xs 1))) the-unit)))
      (prim! 'process-news (lambda (xs) (process-news)))
      (prim! 'process-exit
             (lambda (xs)
               (tagcase (process-exit (as-int (ev-arg xs 0)))
                 (exited c (the val (o-sum 'exited (the val c))))
                 (signalled c (the val (o-sum 'signalled (the val c))))
                 (unknown u (the val (o-sum 'unknown the-unit))))))
      ;; Heist's (`FIXPT-CHANGES.md` F5).
      (prim! 'file-info
             (lambda (xs)
               (tagcase (file-info (as-str (ev-arg xs 0)))
                 (info i (the val (o-sum 'info (ev-file-info i))))
                 (failed e (ev-io-failed e)))))
      (prim! 'read-symlink
             (lambda (xs)
               (tagcase (read-symlink (as-str (ev-arg xs 0)))
                 (target t (the val (o-sum 'target (the val t))))
                 (failed e (ev-io-failed e))))))))

;; `append`: the lists `xs`, all but the last copied, in front of it.
(define ev-append (->* (vals) val)
  (lambda (xs)
    (cond ((null? xs) nil)
          ((null? (cdr xs)) (car xs))
          (else (ev-onto (car xs) (ev-append (cdr xs)))))))
;; List `v`'s elements, copied, in front of `tail`.
(define ev-onto (->* (val val) val)
  (lambda (v tail) (if (null? v) tail (cons (car (as-pair v)) (ev-onto (cdr (as-pair v)) tail)))))
;; How many pairs list `v` has, `n` so far: `length`'s and `list-length`'s.
(define ev-list-length (->* (val int) int)
  (lambda (v n) (if (null? v) n (ev-list-length (cdr (as-pair v)) (+ n 1)))))
(define* ev-data-prims! (subr (maxeff stores spin) () unit)
  (lambda ()
    (begin
      (prim! 'cons (lambda (xs) (cons (ev-arg xs 0) (ev-arg xs 1))))
      (prim! 'car (lambda (xs) (car (as-pair (ev-arg xs 0)))))
      (prim! 'cdr (lambda (xs) (cdr (as-pair (ev-arg xs 0)))))
      (prim! 'length (lambda (xs) (ev-list-length (ev-arg xs 0) 0)))
      (prim! 'list-length (lambda (xs) (ev-list-length (ev-arg xs 0) 0)))
      (prim! 'set-car! (lambda (xs) (ev-set-car! xs)))
      (prim! 'set-cdr! (lambda (xs) (ev-set-cdr! xs)))
      (prim! 'list (lambda (xs) (vals->val xs)))
      ;; The native convention's mark, nothing to the evaluator.
      (prim! 'stay-cellular (lambda (xs) (ev-arg xs 0)))
      (prim! 'append (lambda (xs) (ev-append xs)))
      (prim! 'new (lambda (xs) (the vcell (new (ev-arg xs 0)))))
      (prim! 'get (lambda (xs) (get (as-ref (ev-arg xs 0)))))
      (prim! 'set (lambda (xs) (begin (set (as-ref (ev-arg xs 0)) (ev-arg xs 1)) the-unit)))
      (prim! 'make-icell (lambda (xs) (ev-make-icell)))
      (prim! '%sched (lambda (xs) (ev-sched xs)))
      (prim! 'make-array (lambda (xs) (ev-make-array (ev-arg xs 0) (ev-arg xs 1))))
      (prim! 'array-ref (lambda (xs) (array-ref (as-array (ev-arg xs 0)) (as-int (ev-arg xs 1)))))
      (prim! 'array-set! (lambda (xs) (ev-array-set! xs)))
      (prim! 'array-length (lambda (xs) (array-length (as-array (ev-arg xs 0)))))
      ;; Allocating in a region it is given: the region erased, its place
      ;; the first argument.
      (prim! 'rcons (lambda (xs) (cons (ev-arg xs 1) (ev-arg xs 2))))
      (prim! 'rnew (lambda (xs) (the vcell (new (ev-arg xs 1)))))
      (prim! 'rmake-array (lambda (xs) (ev-make-array (ev-arg xs 1) (ev-arg xs 2))))
      (prim! 'rmake-string (lambda (xs) (ev-make-string (ev-arg xs 1) (ev-arg xs 2))))
      (prim! 'rmake-icell (lambda (xs) (ev-make-icell)))
      ;; Flat arrays: here, arrays of their values; a layout, its number.
      (prim! 'make-flatarray (lambda (xs) (ev-make-array (ev-arg xs 1) (ev-arg xs 2))))
      (prim! 'flatarray-ref
             (lambda (xs) (array-ref (as-array (ev-arg xs 0)) (as-int (ev-arg xs 1)))))
      (prim! 'flatarray-set! (lambda (xs) (ev-array-set! xs)))
      (prim! 'flatarray-length (lambda (xs) (array-length (as-array (ev-arg xs 0)))))
      (prim! 'i32-flat (lambda (xs) 0)) (prim! 'u32-flat (lambda (xs) 1))
      (prim! 'i64-flat (lambda (xs) 2)) (prim! 'u64-flat (lambda (xs) 3))
      (prim! 'f32-flat (lambda (xs) 4)) (prim! 'f64-flat (lambda (xs) 5)))))

;; `string->f64`'s: a list of the number, or none.
(define ev-string->f64 (->* (vals) val)
  (lambda (xs)
    (let ((l (string->f64 (as-str (ev-arg xs 0)))))
      (if (null? l) nil (cons (the val (car l)) (the val nil))))))

(define* ev-f64-prims! (subr (maxeff stores spin) () unit)
  (lambda ()
    (begin
      (prim! 'f64+ (lambda (xs) (f64-2 xs f64+))) (prim! 'f64- (lambda (xs) (f64-2 xs f64-)))
      (prim! 'f64* (lambda (xs) (f64-2 xs f64*))) (prim! 'f64/ (lambda (xs) (f64-2 xs f64/)))
      (prim! 'f64-min (lambda (xs) (f64-2 xs f64-min)))
      (prim! 'f64-max (lambda (xs) (f64-2 xs f64-max)))
      (prim! 'f64-atan2 (lambda (xs) (f64-2 xs f64-atan2)))
      (prim! 'f64-expt (lambda (xs) (f64-2 xs f64-expt)))
      (prim! 'f64< (lambda (xs) (f64-cmp xs f64<))) (prim! 'f64<= (lambda (xs) (f64-cmp xs f64<=)))
      (prim! 'f64> (lambda (xs) (f64-cmp xs f64>))) (prim! 'f64>= (lambda (xs) (f64-cmp xs f64>=)))
      (prim! 'f64= (lambda (xs) (f64-cmp xs f64=)))
      (prim! 'f64-nan? (lambda (xs) (f64-test xs f64-nan?)))
      (prim! 'f64-infinite? (lambda (xs) (f64-test xs f64-infinite?)))
      (prim! 'f64-finite? (lambda (xs) (f64-test xs f64-finite?)))
      (prim! 'f64-abs (lambda (xs) (f64-1 xs f64-abs)))
      (prim! 'f64-neg (lambda (xs) (f64-1 xs f64-neg)))
      (prim! 'f64-sqrt (lambda (xs) (f64-1 xs f64-sqrt)))
      (prim! 'f64-floor (lambda (xs) (f64-1 xs f64-floor)))
      (prim! 'f64-ceiling (lambda (xs) (f64-1 xs f64-ceiling)))
      (prim! 'f64-truncate (lambda (xs) (f64-1 xs f64-truncate)))
      (prim! 'f64-round (lambda (xs) (f64-1 xs f64-round)))
      (prim! 'f64-exp (lambda (xs) (f64-1 xs f64-exp)))
      (prim! 'f64-log (lambda (xs) (f64-1 xs f64-log)))
      (prim! 'f64-sin (lambda (xs) (f64-1 xs f64-sin)))
      (prim! 'f64-cos (lambda (xs) (f64-1 xs f64-cos)))
      (prim! 'f64-tan (lambda (xs) (f64-1 xs f64-tan)))
      (prim! 'f64-asin (lambda (xs) (f64-1 xs f64-asin)))
      (prim! 'f64-acos (lambda (xs) (f64-1 xs f64-acos)))
      (prim! 'f64-atan (lambda (xs) (f64-1 xs f64-atan)))
      (prim! 'int->f64 (lambda (xs) (int->f64 (as-int (ev-arg xs 0)))))
      (prim! 'f64->int (lambda (xs) (f64->int (as-f64 (ev-arg xs 0)))))
      (prim! 'f64->string (lambda (xs) (f64->string (as-f64 (ev-arg xs 0)))))
      (prim! 'string->f64 (lambda (xs) (ev-string->f64 xs))))))

(define* ev-f32-prims! (subr (maxeff stores spin) () unit)
  (lambda ()
    (begin
      (prim! 'f32+ (lambda (xs) (f32-2 xs f32+))) (prim! 'f32- (lambda (xs) (f32-2 xs f32-)))
      (prim! 'f32* (lambda (xs) (f32-2 xs f32*))) (prim! 'f32/ (lambda (xs) (f32-2 xs f32/)))
      (prim! 'f32-min (lambda (xs) (f32-2 xs f32-min)))
      (prim! 'f32-max (lambda (xs) (f32-2 xs f32-max)))
      (prim! 'f32< (lambda (xs) (f32-cmp xs f32<))) (prim! 'f32<= (lambda (xs) (f32-cmp xs f32<=)))
      (prim! 'f32> (lambda (xs) (f32-cmp xs f32>))) (prim! 'f32>= (lambda (xs) (f32-cmp xs f32>=)))
      (prim! 'f32= (lambda (xs) (f32-cmp xs f32=)))
      (prim! 'f32-nan? (lambda (xs) (f32-test xs f32-nan?)))
      (prim! 'f32-infinite? (lambda (xs) (f32-test xs f32-infinite?)))
      (prim! 'f32-finite? (lambda (xs) (f32-test xs f32-finite?)))
      (prim! 'f32-abs (lambda (xs) (f32-1 xs f32-abs)))
      (prim! 'f32-neg (lambda (xs) (f32-1 xs f32-neg)))
      (prim! 'f32-sqrt (lambda (xs) (f32-1 xs f32-sqrt)))
      (prim! 'f32-floor (lambda (xs) (f32-1 xs f32-floor)))
      (prim! 'f32-ceiling (lambda (xs) (f32-1 xs f32-ceiling)))
      (prim! 'f32-truncate (lambda (xs) (f32-1 xs f32-truncate)))
      (prim! 'f32-round (lambda (xs) (f32-1 xs f32-round)))
      (prim! 'int->f32 (lambda (xs) (int->f32 (as-int (ev-arg xs 0)))))
      (prim! 'f32->int (lambda (xs) (f32->int (as-f32 (ev-arg xs 0)))))
      (prim! 'f32->string (lambda (xs) (f32->string (as-f32 (ev-arg xs 0)))))
      (prim! 'f32->f64 (lambda (xs) (f32->f64 (as-f32 (ev-arg xs 0)))))
      (prim! 'f64->f32 (lambda (xs) (f64->f32 (as-f64 (ev-arg xs 0)))))
      (prim! 'f64->bits (lambda (xs) (u64->int (f64->bits (as-f64 (ev-arg xs 0))))))
      (prim! 'bits->f64 (lambda (xs) (bits->f64 (int->u64 (as-int (ev-arg xs 0))))))
      (prim! 'f32->bits (lambda (xs) (u32->int (f32->bits (as-f32 (ev-arg xs 0))))))
      (prim! 'bits->f32 (lambda (xs) (bits->f32 (int->u32 (as-int (ev-arg xs 0)))))))))

;; `cwcc` of `f`, at @x, which nothing here would infer: the escape kept.
(define ev-cwcc (->* (val) val)
  (lambda (f)
    ((proj (proj (proj cwcc @x) val) (maxeff evals spin)) (lambda (k) (apply1 f (o-esc k))))))

(define ev-ccc (->* (vals) val)
  (lambda (xs)
    (let ((f (ev-arg xs 0)))
      (call-with-composable-continuation
       (lambda (k) (apply1 f (o-cont k)))
       (as-tag (ev-arg xs 1))))))
;; The same, one-shot: the machine's own one-shot continuation, which fails
;; when resumed twice as the machine does.
(define ev-cone (->* (vals) val)
  (lambda (xs)
    (let ((f (ev-arg xs 0)))
      (call-with-oneshot-continuation
       (lambda (k) (apply1 f (o-once k (new #f))))
       (as-tag (ev-arg xs 1))))))

(define ev-with-mark (->* (vals) val)
  (lambda (xs)
    (let ((thunk (ev-arg xs 2)) (key (as-key (ev-arg xs 0))))
      (with-mark key (ev-arg xs 1) (lambda () (apply-val thunk (the vals nil)))))))

;; `apply`: `f` of the elements of a list value, which its procedure gets
;; as a list of its own (F11).
(define ev-apply (->* (vals) val)
  (lambda (xs) (apply-val (ev-arg xs 0) (val->vals (ev-arg xs 1)))))

(define* ev-control-prims! (subr (maxeff stores spin) () unit)
  (lambda ()
    (begin
      (prim! '%vlambda
             (lambda (xs) (let ((f (ev-arg xs 0))) (lambda ((ys vals)) (apply1 f (vals->val ys))))))
      (prim! 'apply (lambda (xs) (ev-apply xs)))
      (prim! 'make-continuation-prompt-tag (lambda (xs) (o-tag (make-continuation-prompt-tag))))
      ;; An escape-only tag is a prompt tag at run time (`TODO.md` §89).
      (prim! 'make-escape-tag (lambda (xs) (o-tag (make-continuation-prompt-tag))))
      (prim! 'escape
             (lambda (xs) (abort-current-continuation (as-tag (ev-arg xs 0)) (ev-arg xs 1))))
      (prim! 'abort-current-continuation
             (lambda (xs) (abort-current-continuation (as-tag (ev-arg xs 0)) (ev-arg xs 1))))
      (prim! 'call-with-composable-continuation (lambda (xs) (ev-ccc xs)))
      (prim! 'call-with-oneshot-continuation (lambda (xs) (ev-cone xs)))
      (prim! 'cwcc (lambda (xs) (ev-cwcc (ev-arg xs 0))))
      (prim! 'make-continuation-mark-key (lambda (xs) (o-key (make-continuation-mark-key))))
      (prim! 'with-mark (lambda (xs) (ev-with-mark xs)))
      (prim! 'first-mark (lambda (xs) (first-mark (as-key (ev-arg xs 0)) (ev-arg xs 1))))
      (prim! 'current-marks (lambda (xs) (list->val (current-marks (as-key (ev-arg xs 0))))))
      (prim! 'marks-of
             (lambda (xs) (list->val (marks-of (as-cont (ev-arg xs 0)) (as-key (ev-arg xs 1)))))))))

;;; The standard procedures found missing here (Heist's R4, `TODO.md` §211):
;;; characters and strings, lists and arrays, data as read, and tables by
;;; identity, each as the machines have it.

;; List `v` reversed onto `acc`.
(define ev-reverse (->* (val val) val)
  (lambda (v acc)
    (if (null? v) acc (ev-reverse (cdr (as-pair v)) (cons (car (as-pair v)) acc)))))
;; Array `a`'s elements up to `i`, in order, in front of `acc`.
(define ev-array-list (->* ((arrayof val @v) int val) val)
  (lambda (a i acc) (if (< i 0) acc (ev-array-list a (- i 1) (cons (array-ref a i) acc)))))
;; List `v`'s elements, from place `i` of `a`.
(define ev-fill (->* ((arrayof val @v) val int) unit)
  (lambda (a v i)
    (if (null? v)
        #u
        (begin (array-set! a i (car (as-pair v))) (ev-fill a (cdr (as-pair v)) (+ i 1))))))
(define ev-list-array (->* (val) (arrayof val @v))
  (lambda (v)
    (let ((a (the (arrayof val @v) (make-array (ev-list-length v 0) nil))))
      (begin (ev-fill a v 0) a))))
;; Whether `v` is a list of exactly `n` elements.
(define ev-length-is? (->* (val int) bool)
  (lambda (v n)
    (cond ((null? v) (= n 0))
          ((pair? v) (and (> n 0) (ev-length-is? (cdr v) (- n 1))))
          (else #f))))
(define ev-proper? (->* (val) bool)
  (lambda (v) (cond ((null? v) #t) ((pair? v) (ev-proper? (cdr v))) (else #f))))
;; Whether `v` reaches no part of itself, the parts on `path` its own way
;; there, as `%fx26-acyclic?` walks pairs, arrays and vectors.
(define-rec
  (ev-acyclic? (->* (val vals) bool)
    (lambda (v path)
      (if (ev-on-path? v path)
          #f
          (typecase v
            (pair p (let ((in (the vals (cons v path))))
                      (and (ev-acyclic? (car p) in) (ev-acyclic? (cdr p) in))))
            (bloblet a (ev-all-acyclic? a 0 (cons v path)))
            (sum o (tagcase o
                     (o-vec (xs) (ev-all-acyclic? xs 0 (cons v path)))
                     (else y #t)))
            (else #t)))))
  (ev-all-acyclic? (->* ((arrayof val @v) int vals) bool)
    (lambda (a i path)
      (or (>= i (array-length a))
          (and (ev-acyclic? (array-ref a i) path) (ev-all-acyclic? a (+ i 1) path)))))
  (ev-on-path? (->* (val vals) bool)
    (lambda (v path)
      (and (not (null? path)) (or (ev-eq? v (car path)) (ev-on-path? v (cdr path)))))))
;; A list of bytes, `datum-list->bytevector`'s, from place `i`.
(define ev-fill-bytes (->* ((bytevectorof @v) val int) unit)
  (lambda (b v i)
    (if (null? v)
        #u
        (begin (bytevector-u8-set! b i (int->u8 (as-int (car (as-pair v)))))
               (ev-fill-bytes b (cdr (as-pair v)) (+ i 1))))))
;; The numbers `parse-number` read, as values.
(define ev-numbers (->* ((listof datum @v)) val)
  (lambda (ds)
    (if (null? ds)
        nil
        (cons (typecase (car ds) (int n n) (f64 x x) (else (efail "not a number")))
              (ev-numbers (cdr ds))))))
;; A table by identity's entries, and the one of key `k`, or none.
(define-type entries (listof (pairof val val @v) @v))
(define as-eqt (->* (val) (ref entries @v))
  (lambda (v)
    (tagcase (as-other v "an eqtable") (o-eqt (es) es) (else y (efail-expected "an eqtable")))))
(define ev-entry (->* (entries val) entries)
  (lambda (es k)
    (cond ((null? es) nil) ((ev-eq? (car (car es)) k) es) (else (ev-entry (cdr es) k)))))
;; How many entries `es` has, `n` so far.
(define ev-count-entries (->* (entries int) int)
  (lambda (es n) (if (null? es) n (ev-count-entries (cdr es) (+ n 1)))))
(define ev-without (->* (entries val) entries)
  (lambda (es k)
    (cond ((null? es) nil)
          ((ev-eq? (car (car es)) k) (cdr es))
          (else (cons (car es) (ev-without (cdr es) k))))))
(define ev-eqt-set! (->* (val val val) val)
  (lambda (t k v)
    (let* ((es (as-eqt t)) (e (ev-entry (get es) k)))
      (begin (if (null? e) (set es (cons (cons k v) (get es))) (set-cdr! (car e) v))
             the-unit))))

(define* ev-more-prims! (subr (maxeff stores spin) () unit)
  (lambda ()
    (let ((char1 (lambda ((f (subr pure (char) bool)))
                   (lambda ((xs vals)) (f (as-char (ev-arg xs 0)))))))
      (begin
        (prim! 'char-alphabetic? (char1 (lambda ((c char)) (char-alphabetic? c))))
        (prim! 'char-whitespace? (char1 (lambda ((c char)) (char-whitespace? c))))
        (prim! 'char-downcase (lambda (xs) (char-downcase (as-char (ev-arg xs 0)))))
        (prim! 'char-in? (lambda (xs) (char-in? (as-char (ev-arg xs 0)) (as-str (ev-arg xs 1)))))
        (prim! 'string-downcase (lambda (xs) (string-downcase (as-str (ev-arg xs 0)))))
        (prim! 'string-ci=?
               (lambda (xs) (string-ci=? (as-str (ev-arg xs 0)) (as-str (ev-arg xs 1)))))
        (prim! 'string-compare
               (lambda (xs) (string-compare (as-str (ev-arg xs 0)) (as-str (ev-arg xs 1)))))
        (prim! 'string-search
               (lambda (xs)
                 (string-search (as-str (ev-arg xs 0)) (as-str (ev-arg xs 1))
                                (as-int (ev-arg xs 2)))))
        (prim! 'symbol-compare
               (lambda (xs) (symbol-compare (as-sym (ev-arg xs 0)) (as-sym (ev-arg xs 1)))))
        (prim! 'nat? (lambda (xs) (nat? (as-int (ev-arg xs 0)))))
        (prim! 'parse-nat
               (lambda (xs) (parse-nat (as-str (ev-arg xs 0)) (as-int (ev-arg xs 1)))))
        (prim! 'parse-number
               (lambda (xs)
                 (ev-numbers ((proj parse-number @v) (as-str (ev-arg xs 0))
                                                     (as-int (ev-arg xs 1))))))
        (prim! 'reverse (lambda (xs) (ev-reverse (ev-arg xs 0) nil)))
        (prim! 'array->list
               (lambda (xs)
                 (let ((a (as-array (ev-arg xs 0)))) (ev-array-list a (- (array-length a) 1) nil))))
        (prim! 'list->array (lambda (xs) (ev-list-array (ev-arg xs 0))))
        (prim! 'length-is? (lambda (xs) (ev-length-is? (ev-arg xs 0) (as-int (ev-arg xs 1)))))
        (prim! 'acyclic? (lambda (xs) (ev-acyclic? (ev-arg xs 0) nil)))
        (prim! 'vector?
               (lambda (xs)
                 (typecase (ev-arg xs 0)
                   (sum o (tagcase o (o-vec (v) #t) (else y #f)))
                   (else #f))))
        (prim! 'bytevector?
               (lambda (xs)
                 (typecase (ev-arg xs 0)
                   (sum o (tagcase o (o-bytes (b) #t) (else y #f)))
                   (else #f))))
        (prim! 'datum-int? (lambda (xs) (int? (ev-arg xs 0))))
        (prim! 'datum-byte?
               (lambda (xs) (typecase (ev-arg xs 0) (int n (and (>= n 0) (<= n 255))) (else #f))))
        (prim! 'datum-proper-list? (lambda (xs) (ev-proper? (ev-arg xs 0))))
        (prim! 'datum-list (lambda (xs) (ev-onto (ev-arg xs 0) nil)))
        (prim! 'datum-dotted (lambda (xs) (ev-onto (ev-arg xs 0) (ev-arg xs 1))))
        (prim! 'datum-list->vector
               (lambda (xs) (the val (o-vec (ev-list-array (ev-arg xs 0))))))
        (prim! 'datum-list->bytevector
               (lambda (xs)
                 (let* ((v (ev-arg xs 0))
                        (b (the (bytevectorof @v)
                                (make-bytevector (ev-list-length v 0) (int->u8 0)))))
                   (begin (ev-fill-bytes b v 0) (the val (o-bytes b))))))
        ;; Tables by identity: each an association list here, by `eq?`.
        (prim! 'make-eqtable (lambda (xs) (the val (o-eqt (the (ref entries @v) (new nil))))))
        (prim! 'eqtable-ref
               (lambda (xs)
                 (let ((e (ev-entry (get (as-eqt (ev-arg xs 0))) (ev-arg xs 1))))
                   (if (null? e) (ev-arg xs 2) (cdr (car e))))))
        (prim! 'eqtable-has?
               (lambda (xs) (not (null? (ev-entry (get (as-eqt (ev-arg xs 0))) (ev-arg xs 1))))))
        (prim! 'eqtable-set! (lambda (xs) (ev-eqt-set! (ev-arg xs 0) (ev-arg xs 1) (ev-arg xs 2))))
        (prim! 'eqtable-delete!
               (lambda (xs)
                 (let ((es (as-eqt (ev-arg xs 0))))
                   (begin (set es (ev-without (get es) (ev-arg xs 1))) the-unit))))
        (prim! 'eqtable-count
               (lambda (xs) (ev-count-entries (get (as-eqt (ev-arg xs 0))) 0)))
        ;; What `make-eqtable` is given, which says its keys are compared by
        ;; identity: nothing to look at here.
        (prim! 'pair-identity (lambda (xs) the-unit))
        (prim! 'ref-identity (lambda (xs) the-unit))
        (prim! 'array-identity (lambda (xs) the-unit))
        (prim! 'icell-identity (lambda (xs) the-unit))))))

;; The standard names the compilers written in FX-26 use, of machine code
;; and words, which the evaluator has none of.
(define ev-compilers-own? (->* (string) bool)
  (lambda (n)
    (let ((starts (lambda ((p string))
                    (and (>= (string-length n) (string-length p))
                         (string=? (substring n 0 (string-length p)) p)))))
      (or (starts "tword-") (starts "wcell-") (starts "wglobal") (starts "rep-")
          (starts "runtime-primitive") (starts "set-register-twin")
          (string=? n "make-word") (string=? n "make-global") (string=? n "close-over-word!")
          (string=? n "disassemble")))))

(define ev-prims-made unit
  (begin (ev-int-prims!) (ev-text-prims!) (ev-shape-prims!) (ev-data-prims!) (ev-f64-prims!)
         (ev-f32-prims!) (ev-control-prims!) (ev-bytes-prims!) (ev-mstring-prims!)
         (ev-io-prims!) (ev-more-prims!)
         (ev-width-prims! "i8" 8 #t) (ev-width-prims! "u8" 8 #f)
         (ev-width-prims! "i32" 32 #t) (ev-width-prims! "u32" 32 #f)
         (ev-width-prims! "i64" 64 #t) (ev-width-prims! "u64" 64 #f)))

;; A standard name's value: `nil`, or a primitive.
(define standard (->* (symbol) val)
  (lambda (name)
    (if (std-nil-name? (symbol->string name))
        nil
        (let ((p (table-ref ev-prims name nil)) (n (symbol->string name)))
          (cond ((not (null? p)) p)
                ((ev-compilers-own? n)
                 (efail (k-cat3 "`" n (string-append "` is the compilers', of machine code and "
                                                     "words, which the evaluator has none of"))))
                (else (efail (k-cat3 "unbound variable `" n "`")))))))))))
