;;; The FX-26 evaluator's primitives: each standard name the evaluator has,
;;; a procedure of the list of its arguments, in a table by its symbol.
;;; After `eval-values.fx`; `eval-core.fx` looks names up here.
;;; A file of one expression (`load-input`, `TODO.md` §68): what makes the
;;; module, which the conductor (`conductor.fx`) applies to the evaluator's
;;; values, the tables and the checker's types module.

;; Its types, and the signatures of what it is given (`eval-types.fx`).
(let* ((eval-types (load-module "fx26:eval-types.fx"))
       (table-types (load-module "fx26:table-types.fx"))
       (check-types-types (load-module "fx26:check-types-types.fx")))
  ;; What it is given: the evaluator's values, the tables (`table.fx`) and
  ;; the checker's types module.
  (lambda ((values (select eval-types eval-values-sig))
           (tables (select table-types tables-sig))
           (check-types (select check-types-types check-types-sig)))
    (module
(define-effect stores (select eval-types stores))
(define-effect evals (select eval-types evals))
(define-type val (select eval-types val))
(define-type vals (select eval-types vals))
(define-type vproc (select eval-types vproc))
(define-type vcell (select eval-types vcell))
(define o-unit (with eval-types o-unit))
(define o-product (with eval-types o-product))
(define o-sum (with eval-types o-sum))
(define o-icell (with eval-types o-icell))
(define o-blob (with eval-types o-blob))
(define o-tag (with eval-types o-tag))
(define o-cont (with eval-types o-cont))
(define o-esc (with eval-types o-esc))
(define o-key (with eval-types o-key))
(define-type table (select table-types table))
;; What it uses of the modules it is given.
(define apply-val (with values apply-val))
(define apply1 (with values apply1))
(define as-array (with values as-array))
(define as-bool (with values as-bool))
(define as-char (with values as-char))
(define as-cont (with values as-cont))
(define as-f32 (with values as-f32))
(define as-f64 (with values as-f64))
(define as-int (with values as-int))
(define as-key (with values as-key))
(define as-other (with values as-other))
(define as-pair (with values as-pair))
(define as-ref (with values as-ref))
(define as-str (with values as-str))
(define as-sym (with values as-sym))
(define as-tag (with values as-tag))
(define efail (with values efail))
(define efail-expected (with values efail-expected))
(define ev-arg (with values ev-arg))
(define ev-eq? (with values ev-eq?))
(define ev-intern (with values ev-intern))
(define list->val (with values list->val))
(define the-unit (with values the-unit))
(define val->vals (with values val->vals))
(define vals->val (with values vals->val))
(define make-table (with tables make-table))
(define std-nil-name? (with tables std-nil-name?))
(define symbol-hash (with tables symbol-hash))
(define table-ref (with tables table-ref))
(define table-set! (with tables table-set!))
(define k-cat3 (with check-types k-cat3))

(define ev-prims (table symbol val @v) (make-table symbol-hash symbol=?))

;; Primitive `n` is `f`.
(define* prim! (subr (maxeff stores spin) (symbol vproc) unit)
  (lambda (n f) (table-set! ev-prims n f)))

(define* int2 (subr (maxeff evals spin) (vals (subr pure (int int) int)) val)
  (lambda (xs f) (f (as-int (ev-arg xs 0)) (as-int (ev-arg xs 1)))))

(define* int-cmp (subr (maxeff evals spin) (vals (subr pure (int int) bool)) val)
  (lambda (xs f) (f (as-int (ev-arg xs 0)) (as-int (ev-arg xs 1)))))

(define* char-cmp (subr (maxeff evals spin) (vals (subr pure (char char) bool)) val)
  (lambda (xs f) (f (as-char (ev-arg xs 0)) (as-char (ev-arg xs 1)))))

(define* str-cmp (subr (maxeff evals spin) (vals (subr pure (string string) bool)) val)
  (lambda (xs f) (f (as-str (ev-arg xs 0)) (as-str (ev-arg xs 1)))))

(define* f64-2 (subr (maxeff evals spin) (vals (subr pure (f64 f64) f64)) val)
  (lambda (xs f) (f (as-f64 (ev-arg xs 0)) (as-f64 (ev-arg xs 1)))))

(define* f64-1 (subr (maxeff evals spin) (vals (subr pure (f64) f64)) val)
  (lambda (xs f) (f (as-f64 (ev-arg xs 0)))))

(define* f64-cmp (subr (maxeff evals spin) (vals (subr pure (f64 f64) bool)) val)
  (lambda (xs f) (f (as-f64 (ev-arg xs 0)) (as-f64 (ev-arg xs 1)))))

(define* f64-test (subr (maxeff evals spin) (vals (subr pure (f64) bool)) val)
  (lambda (xs f) (f (as-f64 (ev-arg xs 0)))))

(define* f32-2 (subr (maxeff evals spin) (vals (subr pure (f32 f32) f32)) val)
  (lambda (xs f) (f (as-f32 (ev-arg xs 0)) (as-f32 (ev-arg xs 1)))))

(define* f32-1 (subr (maxeff evals spin) (vals (subr pure (f32) f32)) val)
  (lambda (xs f) (f (as-f32 (ev-arg xs 0)))))

(define* f32-cmp (subr (maxeff evals spin) (vals (subr pure (f32 f32) bool)) val)
  (lambda (xs f) (f (as-f32 (ev-arg xs 0)) (as-f32 (ev-arg xs 1)))))

(define* f32-test (subr (maxeff evals spin) (vals (subr pure (f32) bool)) val)
  (lambda (xs f) (f (as-f32 (ev-arg xs 0)))))

(define* ev-int-prims! (subr (maxeff stores spin) () unit)
  (lambda ()
    (begin
      (prim! '+ (lambda (xs) (int2 xs (lambda (a b) (+ a b)))))
      (prim! '- (lambda (xs) (int2 xs (lambda (a b) (- a b)))))
      (prim! '* (lambda (xs) (int2 xs (lambda (a b) (* a b)))))
      (prim! 'modulo (lambda (xs) (int2 xs (lambda (a b) (modulo a b)))))
      (prim! 'quotient (lambda (xs) (int2 xs (lambda (a b) (quotient a b)))))
      (prim! 'remainder (lambda (xs) (int2 xs (lambda (a b) (remainder a b)))))
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
(define* fw-wrap (subr pure (int bool int) int)
  (lambda (bits signed x)
    (let ((low (bitwise-and x (- (arithmetic-shift 1 bits) 1))))
      (if (and signed (>= low (arithmetic-shift 1 (- bits 1))))
          (- low (arithmetic-shift 1 bits))
          low))))

(define* fw-2 (subr (maxeff evals spin) (vals int bool (subr pure (int int) int)) val)
  (lambda (xs bits signed f)
    (fw-wrap bits signed (f (as-int (ev-arg xs 0)) (as-int (ev-arg xs 1))))))

;; `quotient` or `remainder`, which truncate as the runtime's do; by zero, a
;; failure, as there.
(define* fw-div (subr (maxeff evals spin) (vals int bool (subr pure (int int) int)) val)
  (lambda (xs bits signed f)
    (if (zero? (as-int (ev-arg xs 1))) (efail "division by zero") (fw-2 xs bits signed f))))

;; A shift by the count's low bits; right, arithmetic (an unsigned value is
;; not negative, so logical too).
(define* fw-shift (subr (maxeff evals spin) (vals int bool bool) val)
  (lambda (xs bits signed left)
    (let ((x (as-int (ev-arg xs 0))) (k (bitwise-and (as-int (ev-arg xs 1)) (- bits 1))))
      (fw-wrap bits signed (arithmetic-shift x (if left k (- 0 k)))))))

;; The operation `op` of width `w`: `w` and `op` run together.
(define* fw-name (subr (read @globals) (string string) symbol)
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
      (prim! 'integer->char (lambda (xs) (integer->char (as-int (ev-arg xs 0)))))
      (prim! 'char->string (lambda (xs) (char->string (as-char (ev-arg xs 0)))))
      (prim! 'string-append
             (lambda (xs) (string-append (as-str (ev-arg xs 0)) (as-str (ev-arg xs 1)))))
      (prim! 'string-length (lambda (xs) (string-length (as-str (ev-arg xs 0)))))
      (prim! 'string-ref
             (lambda (xs) (string-ref (as-str (ev-arg xs 0)) (as-int (ev-arg xs 1)))))
      (prim! 'string=? (lambda (xs) (str-cmp xs (lambda (a b) (string=? a b)))))
      (prim! 'string<? (lambda (xs) (str-cmp xs (lambda (a b) (string<? a b)))))
      (prim! 'string<=? (lambda (xs) (str-cmp xs (lambda (a b) (string<=? a b)))))
      (prim! 'string>? (lambda (xs) (str-cmp xs (lambda (a b) (string>? a b)))))
      (prim! 'string>=? (lambda (xs) (str-cmp xs (lambda (a b) (string>=? a b)))))
      (prim! 'string-hash (lambda (xs) (string-hash (as-str (ev-arg xs 0)))))
      (prim! 'string->symbol (lambda (xs) (string->symbol (as-str (ev-arg xs 0)))))
      (prim! 'symbol->string (lambda (xs) (symbol->string (as-sym (ev-arg xs 0)))))
      (prim! 'symbol=? (lambda (xs) (symbol=? (as-sym (ev-arg xs 0)) (as-sym (ev-arg xs 1)))))
      (prim! 'symbol-name-hash (lambda (xs) (symbol-name-hash (as-sym (ev-arg xs 0)))))
      (prim! 'eq? (lambda (xs) (ev-eq? (ev-arg xs 0) (ev-arg xs 1))))
      (prim! 'error (lambda (xs) (efail (as-str (ev-arg xs 0)))))
      (prim! '%quote (lambda (xs) (ev-intern (ev-arg xs 0)))))))

(define* ev-symbol? (subr pure (val) bool)
  (lambda (v) (typecase v (symbol s #t) (sum o (tagcase o (o-unit () #t) (else y #f))) (else #f))))

(define* ev-procedure? (subr pure (val) bool)
  (lambda (v)
    (typecase v
      (procedure p #t)
      (sum o (tagcase o (o-cont (k) #t) (o-esc (k) #t) (else y #f)))
      (else #f))))

(define* ev-array? (subr pure (val) bool)
  (lambda (v)
    (typecase v (bloblet a #t) (sum o (tagcase o (o-blob (fs bs) #t) (else y #f))) (else #f))))

(define* ev-sum? (subr pure (val) bool)
  (lambda (v) (typecase v (sum o (tagcase o (o-sum (t x) #t) (else y #f))) (else #f))))

(define* ev-product? (subr pure (val) bool)
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
      (prim! 'string? (lambda (xs) (string? (ev-arg xs 0))))
      (prim! 'symbol? (lambda (xs) (ev-symbol? (ev-arg xs 0))))
      (prim! 'procedure? (lambda (xs) (ev-procedure? (ev-arg xs 0))))
      (prim! 'array? (lambda (xs) (ev-array? (ev-arg xs 0))))
      (prim! 'ref? (lambda (xs) (ref? (ev-arg xs 0))))
      (prim! 'sum? (lambda (xs) (ev-sum? (ev-arg xs 0))))
      (prim! 'product? (lambda (xs) (ev-product? (ev-arg xs 0)))))))

;; An i-cell: whether it is full, and its value.
(define* as-icell (subr (maxeff evals spin) (val) (pairof (ref bool @v) vcell @v))
  (lambda (v)
    (tagcase (as-other v "an i-cell")
      (o-icell (full c) (cons full c))
      (else y (efail-expected "an i-cell")))))

(define* ev-make-icell (subr (maxeff (alloc @v) spin) () val)
  (lambda () (o-icell (new #f) (new the-unit))))

(define* ev-icell-put! (subr (maxeff evals spin) (vals) val)
  (lambda (xs)
    (let ((c (as-icell (ev-arg xs 0))))
      (if (get (car c))
          (efail "an i-cell written twice")
          (begin (set (cdr c) (ev-arg xs 1)) (set (car c) #t) the-unit)))))

(define* ev-icell-get (subr (maxeff evals spin) (vals) val)
  (lambda (xs)
    (let ((c (as-icell (ev-arg xs 0))))
      (if (get (car c)) (get (cdr c)) (efail "an i-cell read before it was written")))))

(define* ev-array-set! (subr (maxeff evals spin) (vals) val)
  (lambda (xs)
    (begin (array-set! (as-array (ev-arg xs 0)) (as-int (ev-arg xs 1)) (ev-arg xs 2)) the-unit)))

(define* ev-set-car! (subr (maxeff evals spin) (vals) val)
  (lambda (xs) (begin (set-car! (as-pair (ev-arg xs 0)) (ev-arg xs 1)) the-unit)))

(define* ev-set-cdr! (subr (maxeff evals spin) (vals) val)
  (lambda (xs) (begin (set-cdr! (as-pair (ev-arg xs 0)) (ev-arg xs 1)) the-unit)))

(define* ev-make-array (subr (maxeff evals spin) (val val) val)
  (lambda (n x) (the (arrayof val @v) (make-array (as-int n) x))))

(define* ev-data-prims! (subr (maxeff stores spin) () unit)
  (lambda ()
    (begin
      (prim! 'cons (lambda (xs) (cons (ev-arg xs 0) (ev-arg xs 1))))
      (prim! 'car (lambda (xs) (car (as-pair (ev-arg xs 0)))))
      (prim! 'cdr (lambda (xs) (cdr (as-pair (ev-arg xs 0)))))
      (prim! 'set-car! (lambda (xs) (ev-set-car! xs)))
      (prim! 'set-cdr! (lambda (xs) (ev-set-cdr! xs)))
      (prim! 'list (lambda (xs) (vals->val xs)))
      (prim! 'new (lambda (xs) (the vcell (new (ev-arg xs 0)))))
      (prim! 'get (lambda (xs) (get (as-ref (ev-arg xs 0)))))
      (prim! 'set (lambda (xs) (begin (set (as-ref (ev-arg xs 0)) (ev-arg xs 1)) the-unit)))
      (prim! 'make-icell (lambda (xs) (ev-make-icell)))
      (prim! 'icell-put! (lambda (xs) (ev-icell-put! xs)))
      (prim! 'icell-get (lambda (xs) (ev-icell-get xs)))
      (prim! 'make-array (lambda (xs) (ev-make-array (ev-arg xs 0) (ev-arg xs 1))))
      (prim! 'array-ref (lambda (xs) (array-ref (as-array (ev-arg xs 0)) (as-int (ev-arg xs 1)))))
      (prim! 'array-set! (lambda (xs) (ev-array-set! xs)))
      (prim! 'array-length (lambda (xs) (array-length (as-array (ev-arg xs 0)))))
      ;; Allocating in a region it is given: the region erased, its place
      ;; the first argument.
      (prim! 'rcons (lambda (xs) (cons (ev-arg xs 1) (ev-arg xs 2))))
      (prim! 'rnew (lambda (xs) (the vcell (new (ev-arg xs 1)))))
      (prim! 'rmake-array (lambda (xs) (ev-make-array (ev-arg xs 1) (ev-arg xs 2))))
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
(define* ev-string->f64 (subr (maxeff evals spin) (vals) val)
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
      (prim! 'f64->f32 (lambda (xs) (f64->f32 (as-f64 (ev-arg xs 0))))))))

;; `cwcc` of `f`, at @x, which nothing here would infer: the escape kept.
(define* ev-cwcc (subr (maxeff evals spin) (val) val)
  (lambda (f)
    ((proj (proj (proj cwcc @x) val) (maxeff evals spin)) (lambda (k) (apply1 f (o-esc k))))))

(define* ev-ccc (subr (maxeff evals spin) (vals) val)
  (lambda (xs)
    (let ((f (ev-arg xs 0)))
      (call-with-composable-continuation
       (lambda (k) (apply1 f (o-cont k)))
       (as-tag (ev-arg xs 1))))))

(define* ev-with-mark (subr (maxeff evals spin) (vals) val)
  (lambda (xs)
    (let ((thunk (ev-arg xs 2)) (key (as-key (ev-arg xs 0))))
      (with-mark key (ev-arg xs 1) (lambda () (apply-val thunk (the vals nil)))))))

;; `apply`: `f` of the elements of a list value, which its procedure gets
;; as a list of its own (F11).
(define* ev-apply (subr (maxeff evals spin) (vals) val)
  (lambda (xs) (apply-val (ev-arg xs 0) (val->vals (ev-arg xs 1)))))

(define* ev-control-prims! (subr (maxeff stores spin) () unit)
  (lambda ()
    (begin
      (prim! '%vlambda
             (lambda (xs) (let ((f (ev-arg xs 0))) (lambda ((ys vals)) (apply1 f (vals->val ys))))))
      (prim! 'apply (lambda (xs) (ev-apply xs)))
      (prim! 'make-continuation-prompt-tag (lambda (xs) (o-tag (make-continuation-prompt-tag))))
      (prim! 'abort-current-continuation
             (lambda (xs) (abort-current-continuation (as-tag (ev-arg xs 0)) (ev-arg xs 1))))
      (prim! 'call-with-composable-continuation (lambda (xs) (ev-ccc xs)))
      (prim! 'cwcc (lambda (xs) (ev-cwcc (ev-arg xs 0))))
      (prim! 'make-continuation-mark-key (lambda (xs) (o-key (make-continuation-mark-key))))
      (prim! 'with-mark (lambda (xs) (ev-with-mark xs)))
      (prim! 'first-mark (lambda (xs) (first-mark (as-key (ev-arg xs 0)) (ev-arg xs 1))))
      (prim! 'current-marks (lambda (xs) (list->val (current-marks (as-key (ev-arg xs 0))))))
      (prim! 'marks-of
             (lambda (xs) (list->val (marks-of (as-cont (ev-arg xs 0)) (as-key (ev-arg xs 1)))))))))

;; How many `xs` there are.
(define* ev-vals-count (subr (maxeff (read @v) spin) (vals) int)
  (lambda (xs) (if (null? xs) 0 (+ 1 (ev-vals-count (cdr xs))))))

;; Elements `i` on of `a`, from `xs`.
(define* ev-fill-array (subr (maxeff stores spin) ((arrayof val @v) vals int) unit)
  (lambda (a xs i)
    (if (null? xs) #u (begin (array-set! a i (car xs)) (ev-fill-array a (cdr xs) (+ i 1))))))

;; A bloblet of `n` bytes, its fields `xs`.
(define* ev-make-bloblet (subr (maxeff evals spin) (vals) val)
  (lambda (xs)
    (let* ((n (as-int (ev-arg xs 0))) (fields (cdr xs))
           (fs (the (arrayof val @v) (make-array (ev-vals-count fields) the-unit))))
      (begin (ev-fill-array fs fields 0)
             (o-blob fs (the (arrayof int @v) (make-array n 0)))))))

;; Bloblet operation `op`, at field `i`, of `xs`.
(define* ev-bloblet (subr (maxeff evals spin) (symbol int vals) val)
  (lambda (op i xs)
    (case op
      ((rmake-bloblet) (ev-make-bloblet (cdr xs)))
      ((make-bloblet) (ev-make-bloblet xs))
      (else
       (tagcase (as-other (ev-arg xs 0) "a bloblet")
         (o-blob (fs bs)
           (case op
             ((bloblet-ref) (array-ref fs i))
             ((bloblet-set!) (begin (array-set! fs i (ev-arg xs 1)) the-unit))
             ((bloblet-freeze) (ev-arg xs 0))
             ((bloblet-byte) (array-ref bs (as-int (ev-arg xs 1))))
             ((bloblet-set-byte!)
              (begin (array-set! bs (as-int (ev-arg xs 1)) (as-int (ev-arg xs 2))) the-unit))
             (else (array-length bs))))
         (else y (efail-expected "a bloblet")))))))

(define ev-prims-made unit
  (begin (ev-int-prims!) (ev-text-prims!) (ev-shape-prims!) (ev-data-prims!) (ev-f64-prims!)
         (ev-f32-prims!) (ev-control-prims!)
         (ev-width-prims! "i32" 32 #t) (ev-width-prims! "u32" 32 #f)
         (ev-width-prims! "i64" 64 #t) (ev-width-prims! "u64" 64 #f)))

;; A standard name's value: `nil`, or a primitive.
(define* standard (subr (maxeff evals spin) (symbol) val)
  (lambda (name)
    (if (std-nil-name? (symbol->string name))
        nil
        (let ((p (table-ref ev-prims name nil)))
          (if (null? p) (efail (k-cat3 "unbound variable `" (symbol->string name) "`")) p))))))))
