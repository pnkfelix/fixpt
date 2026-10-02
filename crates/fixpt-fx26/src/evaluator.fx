;;; An FX-26 evaluator, in FX-26 (PLAN.md §11, step 9b).
;;;
;;; FX-26's meaning, written in FX-26: the trees `parser.fx` makes, run
;;; directly. It is the reference the compiler to cellular code (step 9d) is
;;; checked against, beside the lowering to Scheme.
;;;
;;; Values are one datatype, `val`. What a program can change is kept in the
;;; evaluator's own region @v: a pair or a reference is a bloblet there, an
;;; array an array there. A product keeps its labels, since `extract` names
;;; one. A closure keeps its parameters and body, as parsed, and the
;;; variables it closed over, globals included: a top-level form runs in the
;;; global environment as it stands then, so a second `define` of a name
;;; shadows the first, and code before it keeps the first, as the lowering
;;; to Scheme does (`lower::Globals`).
;;; Descriptions are not needed to run a program, so they are passed over.
;;;
;;; **Control** is the evaluator's own. A prompt tag the program makes is a
;;; prompt tag of the evaluator's, so `prompt`, aborting and capturing are
;;; FX-26's, one level up, many tags and all; a captured continuation is the
;;; evaluator's own, and so are mark keys and `cwcc`'s escapes. All of it is
;;; in @x.
;;;
;;; Not yet: bloblets' frozen flags.

(private-regions @v @x)

;; What changing the program's store on @v may do, and what a delimited
;; part of the program may do, besides control on @x.
(define-effect stores (maxeff (read @globals) (read @v) (write @v) (alloc @v)))
(define-effect runs (maxeff stores (read @x) (write @x) (alloc @x)))

(define-datatype val
  (v-int int)
  (v-bool bool)
  (v-str string)
  (v-char char)
  (v-f64 f64)
  (v-f32 f32)
  (v-sym symbol)
  (v-unit)
  (v-nil)
  (v-pair (bloblet (fields val val) @v))
  (v-ref (bloblet (fields val) @v))
  (v-array (arrayof val @v))
  ;; An I-cell: whether it is full, and its value, as the runtime has it.
  (v-icell (bloblet (fields val val) @v))
  ;; A bloblet: its fields, and its suffix's bytes.
  (v-blob (arrayof val @v) (arrayof int @v))
  (v-product (listof (pairof symbol val @v) @v))
  (v-sum symbol val)
  (v-clo exp-params exp (listof (pairof symbol (bloblet (fields val) @v) @v) @v))
  (v-prim symbol)
  ;; A variadic procedure (`vlambda`): the procedure of the list of its
  ;; arguments.
  (v-vsubr val)
  (v-tag (prompt-tag val val (maxeff runs spin) @x))
  (v-cont (composable val val (maxeff runs spin) @x))
  (v-esc (subr (goto @x) (val) void))
  (v-key (mark-key val @x)))

;; Local variables: each name and the cell that holds its value.
(define-type vcell (bloblet (fields val) @v))
(define-type vpair (bloblet (fields val val) @v))
(define-type env (listof (pairof symbol vcell @v) @v))
(define-type vals (listof val @v))
;; A product's fields, by label; cells, as a `define-rec` makes them.
(define-type vfields (listof (pairof symbol val @v) @v))
(define-type vcells (listof vcell @v))
;; The program's prompt tags and continuations.
(define-type vtag (prompt-tag val val (maxeff runs spin) @x))
(define-type vcont (composable val val (maxeff runs spin) @x))
;; What evaluating may do: read the trees, run the program on @v, mark and
;; transfer control on @x, and stop with an error.
(define-effect evals (maxeff runs (goto @x) (comefrom @x)))

(define-datatype eresult (ev-ok val) (ev-err string))
(define eval-tag (prompt-tag eresult eresult (maxeff runs spin) @x)
  (make-continuation-prompt-tag))
(define efail (subr evals (string) void)
  (lambda (message) (abort-current-continuation eval-tag (ev-err message))))

;; The global environment, newest first.
(define genv (ref env @v) (new nil))

;;; ---------------------------------------------------------------- values

(define cell (subr (alloc @v) (val) vcell)
  (lambda (v) (make-bloblet 0 v)))
;; `e` with `n` bound to a new cell holding `v`.
(define extend (subr (maxeff (read @globals) (alloc @v)) (symbol val env) env)
  (lambda (n v e) (cons (cons n (cell v)) e)))
;; A pair value.
(define v-cons (subr (maxeff (read @globals) (alloc @v)) (val val) val)
  (lambda (a d) (v-pair (make-bloblet 0 a d))))

;; Fails: `what` is expected.
(define efail-expected (subr evals (string) void)
  (lambda (what) (efail (string-append what " is expected"))))

(define as-int (subr evals (val) int)
  (lambda (v) (tagcase v (v-int (n) n) (else x (efail-expected "an int")))))
(define as-bool (subr evals (val) bool)
  (lambda (v) (tagcase v (v-bool (b) b) (else x (efail-expected "a bool")))))
(define as-str (subr evals (val) string)
  (lambda (v) (tagcase v (v-str (s) s) (else x (efail-expected "a string")))))
(define as-char (subr evals (val) char)
  (lambda (v) (tagcase v (v-char (c) c) (else x (efail-expected "a char")))))
(define as-f64 (subr evals (val) f64)
  (lambda (v) (tagcase v (v-f64 (x) x) (else y (efail-expected "an f64")))))
(define as-f32 (subr evals (val) f32)
  (lambda (v) (tagcase v (v-f32 (x) x) (else y (efail-expected "an f32")))))
(define as-sym (subr evals (val) symbol)
  (lambda (v) (tagcase v (v-sym (s) s) (else x (efail-expected "a symbol")))))
(define as-pair (subr evals (val) vpair)
  (lambda (v) (tagcase v (v-pair (p) p) (else x (efail-expected "a pair")))))
(define as-ref (subr evals (val) vcell)
  (lambda (v) (tagcase v (v-ref (r) r) (else x (efail-expected "a reference")))))
(define as-array (subr evals (val) (arrayof val @v))
  (lambda (v) (tagcase v (v-array (a) a) (else x (efail-expected "an array")))))
(define as-icell (subr evals (val) vpair)
  (lambda (v) (tagcase v (v-icell (c) c) (else x (efail-expected "an i-cell")))))
(define icell-full? (subr (read @v) (vpair) bool)
  (lambda (c) (tagcase (bloblet-ref c 0) (v-bool (b) b) (else x #f))))

(define as-tag (subr (maxeff (read @globals) evals) (val) vtag)
  (lambda (v) (tagcase v (v-tag (t) t) (else x (efail-expected "a prompt tag")))))
(define as-key (subr evals (val) (mark-key val @x))
  (lambda (v) (tagcase v (v-key (k) k) (else x (efail-expected "a mark key")))))
(define as-cont (subr evals (val) vcont)
  (lambda (v) (tagcase v (v-cont (k) k) (else x (efail-expected "a composable continuation")))))

;; The evaluator's list of values, as the program's.
;; The arguments of a call, as the list value a `vlambda` is given.
(define vals->val (subr (maxeff (read @globals) (read @v) (alloc @v) spin) (vals) val)
  (lambda (xs) (if (null? xs) (v-nil) (v-cons (car xs) (vals->val (cdr xs))))))
(define list->val (subr (maxeff (read @globals) (read @x) (alloc @v) spin) ((listof val @x)) val)
  (lambda (xs) (if (null? xs) (v-nil) (v-cons (car xs) (list->val (cdr xs))))))
;; A list value's pairs, copied: `apply`'s, whose variadic procedure's list
;; must be one nothing else can write (F11), as the machines copy it. With
;; no `eq?` to find a cycle by, a cyclic list is not ended: the machines'
;; is an error (`programs/native/apply-cyclic.fx`, which this never runs).
(define* val-list-copy (subr (maxeff (read (globals v-cons)) (read @v) (alloc @v) spin) (val) val)
  (lambda (v)
    (tagcase v
      (v-pair (p) (v-cons (bloblet-ref p 0) (val-list-copy (bloblet-ref p 1))))
      (else y v))))

(define arg (subr (maxeff evals spin) (vals int) val)
  (lambda (xs i)
    (cond ((null? xs) (efail "too few arguments"))
          ((= i 0) (car xs))
          (else (arg (cdr xs) (- i 1))))))

;;; ------------------------------------------------------------ primitives

;; The primitives the evaluator has, between spaces.
(define primitive-names string
  (k-cat4 " + - * = < > <= >= not modulo quotient "
          (k-cat3 "cons rcons rnew rmake-array rmake-icell car cdr null? set-car! set-cdr! "
                  "new get set make-icell icell-put! icell-get char=? char->integer integer->char "
                  "string-append string-length string-ref string=? string->symbol symbol->string ")
          "symbol=? eq? char->string make-array array-ref array-set! array-length "
          (k-cat3 "make-continuation-prompt-tag abort-current-continuation "
                  "call-with-composable-continuation make-continuation-mark-key with-mark "
                  "first-mark current-marks marks-of cwcc %vlambda apply list ")))
;; What the ports wrote themselves, as `ev-std-prim` does them.
(define std-primitive-names string
  (string-append " remainder zero? max min bool=? char<? char<=? char>? char>=? char-upcase "
                 "string<? string<=? string>? string>=? error "))
;; `f64`'s, as `ev-f64-prim` does them.
(define f64-primitive-names string
  (k-cat4 " f64+ f64- f64* f64/ f64-min f64-max f64-atan2 f64-expt f64< f64<= f64> f64>= f64= "
          "f64-nan? f64-infinite? f64-finite? int->f64 f64->int f64->string string->f64 "
          "f64-abs f64-neg f64-sqrt f64-floor f64-ceiling f64-truncate f64-round "
          "f64-exp f64-log f64-sin f64-cos f64-tan f64-asin f64-acos f64-atan "))
;; `f32`'s, as `ev-f32-prim` does them.
(define f32-primitive-names string
  (k-cat4 " f32+ f32- f32* f32/ f32-min f32-max f32< f32<= f32> f32>= f32= "
          "f32-abs f32-neg f32-sqrt f32-floor f32-ceiling f32-truncate f32-round "
          "f32-nan? f32-infinite? f32-finite? "
          (k-cat3 "int->f32 f32->int f32->string f32->f64 f64->f32 int->string "
                  "make-flatarray flatarray-ref flatarray-set! flatarray-length "
                  "i32-flat u32-flat i64-flat u64-flat f32-flat f64-flat ")))
;; `f32`'s, as `ev-f32-prim` does them.

;; Whether `needle` occurs in `hay` from position `i` on.
(define occurs? (subr (maxeff (read @globals) spin) (string string int) bool)
  (lambda (needle hay i)
    (and (<= (+ i (string-length needle)) (string-length hay))
         (or (string=? (substring hay i (+ i (string-length needle))) needle)
             (occurs? needle hay (+ i 1))))))

(define primitive? (subr (maxeff (read @globals) spin) (string) bool)
  (lambda (n)
    (let ((padded (string-append " " (string-append n " "))))
      (or (occurs? padded primitive-names 0)
          (or (occurs? padded f64-primitive-names 0)
              (or (occurs? padded f32-primitive-names 0)
                  (occurs? padded std-primitive-names 0)))))))

;; A standard name: a primitive, or `nil`.
(define standard (subr (maxeff evals spin) (symbol) val)
  (lambda (name)
    (let ((s (symbol->string name)))
      (cond ((std-nil-name? s) (v-nil))
            ((primitive? s) (v-prim name))
            (else (efail (k-cat3 "unbound variable `" s "`")))))))

(define lookup (subr (maxeff evals spin) (env symbol) val)
  (lambda (e name)
    (cond ((null? e) (standard name))
          ((symbol=? (car (car e)) name) (bloblet-ref (cdr (car e)) 0))
          (else (lookup (cdr e) name)))))

(define int2 (subr (maxeff evals spin) (vals (subr pure (int int) int)) val)
  (lambda (xs f) (v-int (f (as-int (arg xs 0)) (as-int (arg xs 1))))))
(define cmp2 (subr (maxeff evals spin) (vals (subr pure (int int) bool)) val)
  (lambda (xs f) (v-bool (f (as-int (arg xs 0)) (as-int (arg xs 1))))))

;;; ------------------------------------------------------------- evaluating

(define bind (subr evals (exp-params vals env) env)
  (lambda (ps xs e)
    (cond ((and (null? ps) (null? xs)) e)
          ((or (null? ps) (null? xs)) (efail "the wrong number of arguments"))
          (else (let ((c (cell (car xs))))
                  (cons (cons (extract (car ps) 1) c) (bind (cdr ps) (cdr xs) e)))))))

(define find-cell (subr (maxeff evals spin) (env symbol) vcell)
  (lambda (e n)
    (cond ((null? e) (efail "no such local"))
          ((symbol=? (car (car e)) n) (cdr (car e)))
          (else (find-cell (cdr e) n)))))

(define field-of (subr (maxeff evals spin) (val symbol) val)
  (lambda (p l)
    (letrec ((find (subr (maxeff (read @globals) evals spin) (vfields) val)
               (lambda (fs)
                 (cond ((null? fs) (efail "no such label"))
                       ((symbol=? (car (car fs)) l) (cdr (car fs)))
                       (else (find (cdr fs)))))))
      (tagcase p (v-product (fs) (find fs)) (else x (efail-expected "a product"))))))

;; An arm's names, bound to a product's fields in order.
(define bind-fields (subr evals (names val env) env)
  (lambda (ns p e)
    (letrec ((go (subr (maxeff (read @globals) evals) (names vfields env) env)
               (lambda (ns fs e)
                 (cond ((and (null? ns) (null? fs)) e)
                       ((or (null? ns) (null? fs)) (efail "the wrong number of fields"))
                       (else (go (cdr ns) (cdr fs) (extend (car ns) (cdr (car fs)) e)))))))
      (tagcase p (v-product (fs) (go ns fs e)) (else x (efail-expected "a product"))))))

(define length-of (subr (maxeff (read @globals) (read @v) spin) (vals) int)
  (lambda (xs) (if (null? xs) 0 (+ 1 (length-of (cdr xs))))))
;; Elements `i` on of `a`, from `xs`.
(define fill-array (subr (maxeff stores spin) ((arrayof val @v) vals int) unit)
  (lambda (a xs i)
    (if (null? xs)
        #u
        (begin (array-set! a i (car xs))
               (fill-array a (cdr xs) (+ i 1))))))

;; `bloblet-set-byte!` of the bytes `bs`, as the arguments `xs` say.
(define ev-set-byte! (subr (maxeff evals spin) ((arrayof int @v) vals) val)
  (lambda (bs xs) (begin (array-set! bs (as-int (arg xs 1)) (as-int (arg xs 2))) (v-unit))))

(define eval-bloblet (subr (maxeff evals spin) (string int vals) val)
  (lambda (op i xs)
    (cond ((string=? op "rmake-bloblet") (eval-bloblet "make-bloblet" i (cdr xs)))
          ((string=? op "make-bloblet")
           (let* ((n (as-int (arg xs 0))) (fields (cdr xs)) (count (length-of fields))
                  (fs (the (arrayof val @v) (make-array count (v-unit)))))
             (begin (fill-array fs fields 0)
                    (v-blob fs (the (arrayof int @v) (make-array n 0))))))
          (else
           (tagcase (arg xs 0)
             (v-blob (fs bs)
               (cond ((string=? op "bloblet-ref") (array-ref fs i))
                     ((string=? op "bloblet-set!") (begin (array-set! fs i (arg xs 1)) (v-unit)))
                     ((string=? op "bloblet-freeze") (arg xs 0))
                     ((string=? op "bloblet-byte") (v-int (array-ref bs (as-int (arg xs 1)))))
                     ((string=? op "bloblet-set-byte!") (ev-set-byte! bs xs))
                     (else (v-int (array-length bs)))))
             (else x (efail-expected "a bloblet")))))))

;; Whether `n` allocates in a region it is given: `rcons` and the like.
(define region-prim? (subr pure (string) bool)
  (lambda (n)
    (or (string=? n "rcons") (string=? n "rnew") (string=? n "rmake-array")
        (string=? n "rmake-icell"))))
;; The primitives `array-set!` and aborting, as the arguments `xs` say.
(define ev-array-set! (subr (maxeff evals spin) (vals) val)
  (lambda (xs) (begin (array-set! (as-array (arg xs 0)) (as-int (arg xs 1)) (arg xs 2)) (v-unit))))
(define ev-abort (subr (maxeff (read @globals) evals spin) (vals) val)
  (lambda (xs) (abort-current-continuation (as-tag (arg xs 0)) (arg xs 1))))

;; `f64`'s operations, by shape, on the arguments `xs`.
(define f64-2 (subr (maxeff evals spin) (vals (subr pure (f64 f64) f64)) val)
  (lambda (xs f) (v-f64 (f (as-f64 (arg xs 0)) (as-f64 (arg xs 1))))))
(define f64-1 (subr (maxeff evals spin) (vals (subr pure (f64) f64)) val)
  (lambda (xs f) (v-f64 (f (as-f64 (arg xs 0))))))
(define f64-cmp (subr (maxeff evals spin) (vals (subr pure (f64 f64) bool)) val)
  (lambda (xs f) (v-bool (f (as-f64 (arg xs 0)) (as-f64 (arg xs 1))))))
(define f64-test (subr (maxeff evals spin) (vals (subr pure (f64) bool)) val)
  (lambda (xs f) (v-bool (f (as-f64 (arg xs 0))))))
;; What the benchmark ports wrote for themselves (PLAN.md Q11), as the
;; machines have them: each by the standard operation of the same name.
(define* ev-std-prim (subr (maxeff evals spin) (string vals) val)
  (lambda (n xs)
    (let ((is (lambda ((s string)) (string=? n s)))
          (c2 (lambda ((f (subr pure (char char) bool)))
                (v-bool (f (as-char (arg xs 0)) (as-char (arg xs 1))))))
          (s2 (lambda ((f (subr pure (string string) bool)))
                (v-bool (f (as-str (arg xs 0)) (as-str (arg xs 1)))))))
      (cond ((is "remainder") (int2 xs (lambda (a b) (remainder a b))))
            ((is "zero?") (v-bool (zero? (as-int (arg xs 0)))))
            ((is "max") (int2 xs (lambda (a b) (max a b))))
            ((is "min") (int2 xs (lambda (a b) (min a b))))
            ((is "bool=?") (v-bool (bool=? (as-bool (arg xs 0)) (as-bool (arg xs 1)))))
            ((is "char<?") (c2 (lambda (a b) (char<? a b))))
            ((is "char<=?") (c2 (lambda (a b) (char<=? a b))))
            ((is "char>?") (c2 (lambda (a b) (char>? a b))))
            ((is "char>=?") (c2 (lambda (a b) (char>=? a b))))
            ((is "char-upcase") (v-char (char-upcase (as-char (arg xs 0)))))
            ((is "string<?") (s2 (lambda (a b) (string<? a b))))
            ((is "string<=?") (s2 (lambda (a b) (string<=? a b))))
            ((is "string>?") (s2 (lambda (a b) (string>? a b))))
            ((is "string>=?") (s2 (lambda (a b) (string>=? a b))))
            ((is "error") (efail (as-str (arg xs 0))))
            (else (efail (string-append "not in the evaluator yet: " n)))))))
;; Flat arrays: here, arrays of their values; a layout, its number.
(define* ev-flat-prim (subr (maxeff evals spin) (string vals) val)
  (lambda (n xs)
    (let ((is (lambda ((s string)) (string=? n s))))
      (cond ((is "make-flatarray") (v-array (make-array (as-int (arg xs 1)) (arg xs 2))))
            ((is "flatarray-ref") (array-ref (as-array (arg xs 0)) (as-int (arg xs 1))))
            ((is "flatarray-set!") (ev-array-set! xs))
            ((is "flatarray-length") (v-int (array-length (as-array (arg xs 0)))))
            ((is "i32-flat") (v-int 0)) ((is "u32-flat") (v-int 1)) ((is "i64-flat") (v-int 2))
            ((is "u64-flat") (v-int 3)) ((is "f32-flat") (v-int 4)) ((is "f64-flat") (v-int 5))
            (else (ev-std-prim n xs))))))
;; `f32`'s operations, by shape.
(define f32-2 (subr (maxeff evals spin) (vals (subr pure (f32 f32) f32)) val)
  (lambda (xs f) (v-f32 (f (as-f32 (arg xs 0)) (as-f32 (arg xs 1))))))
(define f32-1 (subr (maxeff evals spin) (vals (subr pure (f32) f32)) val)
  (lambda (xs f) (v-f32 (f (as-f32 (arg xs 0))))))
(define f32-cmp (subr (maxeff evals spin) (vals (subr pure (f32 f32) bool)) val)
  (lambda (xs f) (v-bool (f (as-f32 (arg xs 0)) (as-f32 (arg xs 1))))))
(define f32-test (subr (maxeff evals spin) (vals (subr pure (f32) bool)) val)
  (lambda (xs f) (v-bool (f (as-f32 (arg xs 0))))))
;; The `f32` operation named `n`, on `xs`; or none such.
(define* ev-f32-prim (subr (maxeff evals spin) (string vals) val)
  (lambda (n xs)
    (let ((is (lambda ((s string)) (string=? n s))) (x (lambda () (arg xs 0))))
      (cond ((is "f32+") (f32-2 xs f32+)) ((is "f32-") (f32-2 xs f32-))
            ((is "f32*") (f32-2 xs f32*)) ((is "f32/") (f32-2 xs f32/))
            ((is "f32-min") (f32-2 xs f32-min)) ((is "f32-max") (f32-2 xs f32-max))
            ((is "f32<") (f32-cmp xs f32<)) ((is "f32<=") (f32-cmp xs f32<=))
            ((is "f32>") (f32-cmp xs f32>)) ((is "f32>=") (f32-cmp xs f32>=))
            ((is "f32=") (f32-cmp xs f32=)) ((is "f32-abs") (f32-1 xs f32-abs))
            ((is "f32-neg") (f32-1 xs f32-neg)) ((is "f32-sqrt") (f32-1 xs f32-sqrt))
            ((is "f32-floor") (f32-1 xs f32-floor)) ((is "f32-ceiling") (f32-1 xs f32-ceiling))
            ((is "f32-truncate") (f32-1 xs f32-truncate)) ((is "f32-round") (f32-1 xs f32-round))
            ((is "f32-nan?") (f32-test xs f32-nan?))
            ((is "f32-infinite?") (f32-test xs f32-infinite?))
            ((is "f32-finite?") (f32-test xs f32-finite?))
            ((is "int->f32") (v-f32 (int->f32 (as-int (x)))))
            ((is "f32->int") (v-int (f32->int (as-f32 (x)))))
            ((is "f32->string") (v-str (f32->string (as-f32 (x)))))
            ((is "int->string") (v-str (int->string (as-int (x)))))
            ((is "f32->f64") (v-f64 (f32->f64 (as-f32 (x)))))
            ((is "f64->f32") (v-f32 (f64->f32 (as-f64 (x)))))
            (else (ev-flat-prim n xs))))))
(define* ev-f64-unary (subr (maxeff evals spin) (string vals) val)
  (lambda (n xs)
    (let ((is (lambda ((s string)) (string=? n s))))
      (cond ((is "f64-abs") (f64-1 xs f64-abs)) ((is "f64-neg") (f64-1 xs f64-neg))
            ((is "f64-sqrt") (f64-1 xs f64-sqrt)) ((is "f64-floor") (f64-1 xs f64-floor))
            ((is "f64-ceiling") (f64-1 xs f64-ceiling))
            ((is "f64-truncate") (f64-1 xs f64-truncate))
            ((is "f64-round") (f64-1 xs f64-round)) ((is "f64-exp") (f64-1 xs f64-exp))
            ((is "f64-log") (f64-1 xs f64-log)) ((is "f64-sin") (f64-1 xs f64-sin))
            ((is "f64-cos") (f64-1 xs f64-cos)) ((is "f64-tan") (f64-1 xs f64-tan))
            ((is "f64-asin") (f64-1 xs f64-asin)) ((is "f64-acos") (f64-1 xs f64-acos))
            ((is "f64-atan") (f64-1 xs f64-atan))
            (else (ev-f32-prim n xs))))))
;; The `f64` operation named `n`, on `xs`; or none such.
(define* ev-f64-prim (subr (maxeff evals spin) (string vals) val)
  (lambda (n xs)
    (let ((is (lambda ((s string)) (string=? n s))))
      (cond ((is "f64+") (f64-2 xs f64+)) ((is "f64-") (f64-2 xs f64-))
            ((is "f64*") (f64-2 xs f64*)) ((is "f64/") (f64-2 xs f64/))
            ((is "f64-min") (f64-2 xs f64-min)) ((is "f64-max") (f64-2 xs f64-max))
            ((is "f64-atan2") (f64-2 xs f64-atan2)) ((is "f64-expt") (f64-2 xs f64-expt))
            ((is "f64<") (f64-cmp xs f64<)) ((is "f64<=") (f64-cmp xs f64<=))
            ((is "f64>") (f64-cmp xs f64>)) ((is "f64>=") (f64-cmp xs f64>=))
            ((is "f64=") (f64-cmp xs f64=))
            ((is "f64-nan?") (f64-test xs f64-nan?))
            ((is "f64-infinite?") (f64-test xs f64-infinite?))
            ((is "f64-finite?") (f64-test xs f64-finite?))
            ((is "int->f64") (v-f64 (int->f64 (as-int (arg xs 0)))))
            ((is "f64->int") (v-int (f64->int (as-f64 (arg xs 0)))))
            ((is "f64->string") (v-str (f64->string (as-f64 (arg xs 0)))))
            ((is "string->f64")
             (let ((l (string->f64 (as-str (arg xs 0)))))
               (if (null? l) (v-nil) (v-cons (v-f64 (car l)) (v-nil)))))
            (else (ev-f64-unary n xs))))))
;; `e` with each binding's name bound, holding #u.
;; The modules to reshape (`k-reshapes`), as `run-checked` was given them.
(define ev-reshapes (ref k-reshape-list @v) (new nil))
;; The positions a module reshaped from `a` to `b` keeps, in a list of one;
;; none if it is not reshaped.
(define-type ev-at (listof k-ids @v))
(define ev-reshape-in
  (subr (maxeff (read @globals) (read @v) (alloc @v) spin) (k-reshape-list int int) ev-at)
  (lambda (rs a b)
    (cond ((null? rs) nil)
          ((and (= (extract (car rs) 1) a) (= (extract (car rs) 2) b))
           (the ev-at (cons (extract (car rs) 3) nil)))
          (else (ev-reshape-in (cdr rs) a b)))))
(define nth-field (subr (maxeff evals spin) (vfields int) (pairof symbol val @v))
  (lambda (fs i)
    (cond ((null? fs) (efail "no such field"))
          ((= i 0) (car fs))
          (else (nth-field (cdr fs) (- i 1))))))
;; Module `v` as `at` (in a list of one) reshapes it: its values at those
;; positions; as it is, if none.
(define reshape-val (subr (maxeff (read @globals) evals spin) (val (listof k-ids @v)) val)
  (lambda (v at)
    (if (null? at)
        v
        (tagcase v
          (v-product (fs)
            (letrec ((pick (subr (maxeff (read @globals) evals spin) (k-ids) vfields)
                       (lambda (ks)
                         (if (null? ks) nil (cons (nth-field fs (car ks)) (pick (cdr ks)))))))
              (v-product (pick (car at)))))
          (else x (efail-expected "a module"))))))
;; `fs` reversed, onto `acc`.
(define reverse-fields
  (subr (maxeff (read @globals) (read @v) (alloc @v) spin) (vfields vfields) vfields)
  (lambda (fs acc) (if (null? fs) acc (reverse-fields (cdr fs) (cons (car fs) acc)))))
;; A module's `define-rec` item as a `letrec`'s bindings.
(define rec-bindings (subr (maxeff (read @globals) spin) (names syns-a exp-list) exp-letrec-bs)
  (lambda (ns ts xs)
    (if (null? ns)
        nil
        (let ((rest (rec-bindings (cdr ns) (cdr ts) (cdr xs))))
          (cons (product (1 (car ns)) (2 (car ts)) (3 (car xs))) rest)))))
;; The values of `ns`, in `e`, onto `vs`, newest first.
(define rec-values (subr (maxeff evals spin) (names env vfields) vfields)
  (lambda (ns e vs)
    (if (null? ns)
        vs
        (rec-values (cdr ns) e (cons (cons (car ns) (bloblet-ref (find-cell e (car ns)) 0)) vs)))))
;; `e` with each of module `m`'s values bound to its name, in order.
(define bind-module (subr (maxeff evals spin) (val env) env)
  (lambda (m e)
    (letrec ((go (subr (maxeff (read @globals) evals spin) (vfields env) env)
               (lambda (fs e)
                 (if (null? fs) e (go (cdr fs) (extend (car (car fs)) (cdr (car fs)) e))))))
      (tagcase m (v-product (fs) (go fs e)) (else x (efail-expected "a module"))))))
(define open-letrec (subr (maxeff (read @globals) evals) (exp-letrec-bs env) env)
  (lambda (bs e) (if (null? bs) e (open-letrec (cdr bs) (extend (extract (car bs) 1) (v-unit) e)))))

;; `eq?` of two values, as the machines have it: the same mutable object; atoms the same word;
;; anything else (products, sums, procedures) #f, which `eq?` allows of immutable data.
(define ev-eq? (subr pure (val val) bool)
  (lambda (a b)
    (tagcase a
      (v-int (x) (tagcase b (v-int (y) (eq? x y)) (else o #f)))
      (v-bool (x) (tagcase b (v-bool (y) (eq? x y)) (else o #f)))
      (v-char (x) (tagcase b (v-char (y) (eq? x y)) (else o #f)))
      (v-sym (x) (tagcase b (v-sym (y) (eq? x y)) (else o #f)))
      (v-str (x) (tagcase b (v-str (y) (eq? x y)) (else o #f)))
      (v-unit () (tagcase b (v-unit () #t) (else o #f)))
      (v-nil () (tagcase b (v-nil () #t) (else o #f)))
      (v-pair (x) (tagcase b (v-pair (y) (eq? x y)) (else o #f)))
      (v-ref (x) (tagcase b (v-ref (y) (eq? x y)) (else o #f)))
      (v-array (x) (tagcase b (v-array (y) (eq? x y)) (else o #f)))
      (v-icell (x) (tagcase b (v-icell (y) (eq? x y)) (else o #f)))
      (v-blob (x bytes) (tagcase b (v-blob (y ybytes) (eq? x y)) (else o #f)))
      (else o #f))))

(define-rec
  (apply-prim (subr (maxeff (read @globals) evals spin) (string vals) val)
    (lambda (n xs)
      (cond ((string=? n "+") (int2 xs (lambda (a b) (+ a b))))
            ((string=? n "-") (int2 xs (lambda (a b) (- a b))))
            ((string=? n "*") (int2 xs (lambda (a b) (* a b))))
            ((string=? n "modulo") (int2 xs (lambda (a b) (modulo a b))))
            ((string=? n "quotient") (int2 xs (lambda (a b) (quotient a b))))
            ((string=? n "=") (cmp2 xs (lambda (a b) (= a b))))
            ((string=? n "<") (cmp2 xs (lambda (a b) (< a b))))
            ((string=? n ">") (cmp2 xs (lambda (a b) (> a b))))
            ((string=? n "<=") (cmp2 xs (lambda (a b) (<= a b))))
            ((string=? n ">=") (cmp2 xs (lambda (a b) (>= a b))))
            ((string=? n "not") (v-bool (not (as-bool (arg xs 0)))))
            ((string=? n "cons") (v-cons (arg xs 0) (arg xs 1)))
            ((string=? n "%vlambda") (v-vsubr (arg xs 0)))
            ((string=? n "list") (vals->val xs))
            ((string=? n "apply")
             (let ((fresh (val-list-copy (arg xs 1))))
               (tagcase (arg xs 0)
                 (v-vsubr (g) (apply1 g fresh))
                 ;; `list`, whose one list is its value.
                 (v-prim (p) (if (string=? (symbol->string p) "list")
                                 fresh
                                 (efail "apply: not a variadic procedure")))
                 (else y (efail "apply: not a variadic procedure")))))
            ;; Regions are erased: an allocation in one is the heap's.
            ((region-prim? n)
             (apply-prim (substring n 1 (string-length n)) (cdr xs)))
            ((string=? n "car") (bloblet-ref (as-pair (arg xs 0)) 0))
            ((string=? n "cdr") (bloblet-ref (as-pair (arg xs 0)) 1))
            ((string=? n "null?") (v-bool (tagcase (arg xs 0) (v-nil () #t) (else x #f))))
            ((string=? n "set-car!")
             (begin (bloblet-set! (as-pair (arg xs 0)) 0 (arg xs 1)) (v-unit)))
            ((string=? n "set-cdr!")
             (begin (bloblet-set! (as-pair (arg xs 0)) 1 (arg xs 1)) (v-unit)))
            ((string=? n "new") (v-ref (cell (arg xs 0))))
            ((string=? n "get") (bloblet-ref (as-ref (arg xs 0)) 0))
            ((string=? n "set") (begin (bloblet-set! (as-ref (arg xs 0)) 0 (arg xs 1)) (v-unit)))
            ((string=? n "make-icell") (v-icell (make-bloblet 0 (v-bool #f) (v-bool #f))))
            ((string=? n "icell-put!")
             (let ((c (as-icell (arg xs 0))))
               (if (icell-full? c)
                   (efail "an i-cell written twice")
                   (begin (bloblet-set! c 1 (arg xs 1)) (bloblet-set! c 0 (v-bool #t)) (v-unit)))))
            ((string=? n "icell-get")
             (let ((c (as-icell (arg xs 0))))
               (if (icell-full? c)
                   (bloblet-ref c 1)
                   (efail "an i-cell read before it was written"))))
            ((string=? n "char=?") (v-bool (char=? (as-char (arg xs 0)) (as-char (arg xs 1)))))
            ((string=? n "char->integer") (v-int (char->integer (as-char (arg xs 0)))))
            ((string=? n "integer->char") (v-char (integer->char (as-int (arg xs 0)))))
            ((string=? n "char->string") (v-str (char->string (as-char (arg xs 0)))))
            ((string=? n "string-append")
             (v-str (string-append (as-str (arg xs 0)) (as-str (arg xs 1)))))
            ((string=? n "string-length") (v-int (string-length (as-str (arg xs 0)))))
            ((string=? n "string-ref")
             (v-char (string-ref (as-str (arg xs 0)) (as-int (arg xs 1)))))
            ((string=? n "string=?") (v-bool (string=? (as-str (arg xs 0)) (as-str (arg xs 1)))))
            ((string=? n "string->symbol") (v-sym (string->symbol (as-str (arg xs 0)))))
            ((string=? n "symbol->string") (v-str (symbol->string (as-sym (arg xs 0)))))
            ((string=? n "symbol=?") (v-bool (symbol=? (as-sym (arg xs 0)) (as-sym (arg xs 1)))))
            ((string=? n "eq?") (v-bool (ev-eq? (arg xs 0) (arg xs 1))))
            ((string=? n "make-array") (v-array (make-array (as-int (arg xs 0)) (arg xs 1))))
            ((string=? n "array-ref") (array-ref (as-array (arg xs 0)) (as-int (arg xs 1))))
            ((string=? n "array-set!") (ev-array-set! xs))
            ((string=? n "array-length") (v-int (array-length (as-array (arg xs 0)))))
            ((string=? n "make-continuation-prompt-tag") (v-tag (make-continuation-prompt-tag)))
            ((string=? n "abort-current-continuation") (ev-abort xs))
            ((string=? n "call-with-composable-continuation")
             (let ((f (arg xs 0)))
               (call-with-composable-continuation
                (lambda (k) (apply1 f (v-cont k)))
                (as-tag (arg xs 1)))))
            ((string=? n "cwcc") (apply-cwcc (arg xs 0)))
            ((string=? n "make-continuation-mark-key") (v-key (make-continuation-mark-key)))
            ((string=? n "with-mark")
             (let ((thunk (arg xs 2)) (key (as-key (arg xs 0))))
               (with-mark key (arg xs 1) (lambda () (apply-val thunk (the vals nil))))))
            ((string=? n "first-mark") (first-mark (as-key (arg xs 0)) (arg xs 1)))
            ((string=? n "current-marks") (list->val (current-marks (as-key (arg xs 0)))))
            ((string=? n "marks-of")
             (list->val (marks-of (as-cont (arg xs 0)) (as-key (arg xs 1)))))
            (else (ev-f64-prim n xs)))))
  ;; `f` applied to `x` alone.
  (apply1 (subr (maxeff (read @globals) evals spin) (val val) val)
    (lambda (f x) (apply-val f (the vals (cons x nil)))))
  ;; `cwcc` of `f`, at @x, which nothing here would infer: the escape is
  ;; kept.
  (apply-cwcc (subr (maxeff (read @globals) evals spin) (val) val)
    (lambda (f)
      ((proj (proj (proj cwcc @x) val) (maxeff evals spin)) (lambda (k) (apply1 f (v-esc k))))))
  (apply-val (subr (maxeff (read @globals) evals spin) (val vals) val)
    (lambda (f xs)
      (tagcase f
        (v-clo (ps body e) (eval body (bind ps xs e)))
        (v-prim (n) (apply-prim (symbol->string n) xs))
        (v-vsubr (g) (apply1 g (vals->val xs)))
        (v-cont (k) (k (arg xs 0)))
        (v-esc (k) (k (arg xs 0)))
        (else x (efail "not a subroutine")))))
  (eval-all (subr (maxeff (read @globals) evals spin) ((listof exp acyclic) env) vals)
    (lambda (es e)
      (if (null? es)
          nil
          (let ((v (eval (car es) e)))
            (cons v (eval-all (cdr es) e))))))
  (eval-begin (subr (maxeff (read @globals) evals spin) ((listof exp acyclic) env) val)
    (lambda (es e)
      (cond ((null? es) (v-unit))
            ((null? (cdr es)) (eval (car es) e))
            (else (begin (eval (car es) e) (eval-begin (cdr es) e))))))
  ;; `x`'s value; a module reshaped where the checker said so
  ;; (`k-reshape-at`), a product of the values its type wanted, by position.
  (eval (subr (maxeff (read @globals) evals spin) (exp env) val)
    (lambda (x e)
      (let ((v (eval-node x e)) (rs (get ev-reshapes)))
        (if (null? rs) v (reshape-val v (ev-reshape-in rs (exp-start x) (exp-end x)))))))
  (eval-node (subr (maxeff (read @globals) evals spin) (exp env) val)
    (lambda (x e)
      (tagcase x
        (e-var (n a b) (lookup e n))
        (e-int (n a b) (v-int n))
        (e-bool (v a b) (v-bool v))
        (e-str (s a b) (v-str s))
        (e-char (c a b) (v-char c))
        (e-float (x a b) (v-f64 x))
        (e-sym (s a b) (v-sym s))
        (e-unit (a b) (v-unit))
        (e-lambda (ps body a b) (v-clo ps body e))
        (e-app (f args a b) (let* ((fv (eval f e)) (xs (eval-all args e))) (apply-val fv xs)))
        (e-plambda (d body a b) (eval body e))
        ;; Regions and places are erased: a `letrena`'s or `letreap`'s
        ;; allocation is the heap's, and its name, the place as a value, is
        ;; unit.
        (e-letregion (k r i body a b) (eval body (cons (cons r (cell (v-unit))) e)))
        (e-rlambda (r l a b) (eval l e))
        (e-proj (body ds a b) (eval body e))
        (e-the (d body a b) (eval body e))
        (e-convention (cnv body a b) (eval body e))
        (e-if (t th el a b) (if (as-bool (eval t e)) (eval th e) (eval el e)))
        (e-letrec (bs body a b) (eval-letrec bs body e))
        (e-let (bs body a b) (eval body (eval-let bs e e)))
        (e-begin (es a b) (eval-begin es e))
        (e-prompt (t body h a b)
          (let* ((tag (as-tag (eval t e))) (hv (eval h e)))
            (prompt tag (eval body e) (lambda (v) (apply1 hv v)))))
        (e-bloblet (op i args a b) (eval-bloblet (symbol->string op) i (eval-all args e)))
        (e-product (fs a b) (v-product (eval-fields fs e)))
        (e-extract (p l a b) (field-of (eval p e) l))
        (e-sum (t v a b) (v-sum t (eval v e)))
        (e-tagcase (s arms els a b) (eval-tagcase (eval s e) arms els e))
        ;; Not yet (`docs/research/first-class-modules.md`, M3).
        ;; A module: a product of its values, in order, each labelled by its
        ;; name; its abstract types' conversions the identity.
        (e-module (items a b) (eval-module items e nil))
        ;; `with`: the module's values, by position, bound by their names.
        (e-with (m body a b) (eval body (bind-module (lookup e m) e))))))
  ;; A module's items, each in the scope of those before it, `vs` its
  ;; values so far (newest first).
  (eval-module (subr (maxeff (read @globals) evals spin) (mod-items env vfields) val)
    (lambda (items e vs)
      (if (null? items)
          (v-product (reverse-fields vs nil))
          (let* ((it (car items)) (k (extract it 1)) (ns (extract it 2)) (xs (extract it 4)))
            (cond
              ((or (= k 1) (< k 0) (> k 3)) (eval-module (cdr items) e vs))
              ((= k 0)
               (let* ((n (symbol->string (car ns)))
                      (up (extend (string->symbol (string-append "up-" n)) (eval (car xs) e) e))
                      (down (string->symbol (string-append "down-" n))))
                 (eval-module (cdr items) (extend down (eval (car (cdr xs)) up) up) vs)))
              ((= k 2)
               (let ((v (eval (car xs) e)))
                 (eval-module (cdr items) (extend (car ns) v e) (cons (cons (car ns) v) vs))))
              (else
               (let* ((bs (rec-bindings ns (extract it 3) xs)) (inner (open-letrec bs e)))
                 (begin (fill-letrec bs inner)
                        (eval-module (cdr items) inner (rec-values ns inner vs))))))))))
  (eval-let (subr (maxeff (read @globals) evals spin) (exp-let-bs env env) env)
    (lambda (bs outer e)
      (if (null? bs)
          e
          (let ((v (eval (extract (car bs) 2) outer)))
            (eval-let (cdr bs) outer (extend (extract (car bs) 1) v e))))))
  ;; Every name first, holding #u; then each value, in the scope of all.
  (eval-letrec (subr (maxeff (read @globals) evals spin) (exp-letrec-bs exp env) val)
    (lambda (bs body e)
      (let ((inner (open-letrec bs e)))
        (begin (fill-letrec bs inner) (eval body inner)))))
  ;; Each binding's value, into its name's cell in `inner`.
  (fill-letrec (subr (maxeff (read @globals) evals spin) (exp-letrec-bs env) unit)
    (lambda (bs inner)
      (if (null? bs)
          #u
          (let ((c (find-cell inner (extract (car bs) 1))))
            (begin (bloblet-set! c 0 (eval (extract (car bs) 3) inner))
                   (fill-letrec (cdr bs) inner))))))
  (eval-fields (subr (maxeff (read @globals) evals spin) (exp-let-bs env) vfields)
    (lambda (fs e)
      (if (null? fs)
          nil
          (let ((v (eval (extract (car fs) 2) e)))
            (cons (cons (extract (car fs) 1) v) (eval-fields (cdr fs) e))))))
  (eval-tagcase
    (subr (maxeff (read @globals) evals spin) (val exp-arms exp-let-bs env) val)
    (lambda (s arms els e)
      (tagcase s
        (v-sum (tag v)
          (letrec ((try (subr (maxeff (read @globals) evals spin) (exp-arms) val)
                     (lambda (as)
                       (cond ((null? as)
                              (if (null? els)
                                  (efail "no arm for this value")
                                  (eval (extract (car els) 2) (extend (extract (car els) 1) s e))))
                             ((symbol=? (extract (car as) 1) tag)
                              (eval (extract (car as) 4)
                                    (if (extract (car as) 2)
                                        (bind-fields (extract (car as) 3) v e)
                                        (extend (car (extract (car as) 3)) v e))))
                             (else (try (cdr as)))))))
            (try arms)))
        (else x (efail-expected "a sum"))))))

;;; ------------------------------------------------------------- programs

(define bound? (subr (maxeff (read @globals) (read @v) spin) (env symbol) bool)
  (lambda (e n) (and (not (null? e)) (or (symbol=? (car (car e)) n) (bound? (cdr e) n)))))

;; Names whose next definition keeps the cell they have: definitions that
;; assign their globals (`checked-tops`, under redefinition).
(define ev-keep (ref (listof symbol acyclic) @v) (new nil))
(define ev-kept? (subr (read @globals) ((listof symbol acyclic) symbol) bool)
  (lambda (ks n) (and (not (null? ks)) (or (symbol=? (car ks) n) (ev-kept? (cdr ks) n)))))
(define ev-unkeep (subr (read @globals) ((listof symbol acyclic) symbol) (listof symbol acyclic))
  (lambda (ks n)
    (cond ((null? ks) ks)
          ((symbol=? (car ks) n) (ev-unkeep (cdr ks) n))
          (else (the (listof symbol acyclic) (cons (car ks) (ev-unkeep (cdr ks) n)))))))
(define ev-new-global (subr stores (symbol) vcell)
  (lambda (n) (let ((c (cell (v-unit)))) (begin (set genv (cons (cons n c) (get genv))) c))))
;; The cell global `n` has; a new one, if it has none.
(define ev-cell-of (subr (maxeff stores spin) (env symbol) vcell)
  (lambda (e n)
    (cond ((null? e) (ev-new-global n))
          ((symbol=? (car (car e)) n) (cdr (car e)))
          (else (ev-cell-of (cdr e) n)))))
;; The cell a definition of `n` sets: the one it has, if kept; else new.
(define push-global (subr (maxeff stores spin) (symbol) vcell)
  (lambda (n)
    (if (ev-kept? (get ev-keep) n)
        (begin (set ev-keep (ev-unkeep (get ev-keep) n)) (ev-cell-of (get genv) n))
        (ev-new-global n))))


;; The cells of a `define-rec`'s names, and its values put in them.
(define rec-cells (subr (maxeff stores spin) (exp-letrec-bs) vcells)
  (lambda (bs)
    (if (null? bs)
        nil
        (let ((c (push-global (extract (car bs) 1))))
          (cons c (rec-cells (cdr bs)))))))
(define rec-fill (subr (maxeff evals spin) (exp-letrec-bs vcells) unit)
  (lambda (bs cells)
    (if (null? bs)
        #u
        (begin (bloblet-set! (car cells) 0 (eval (extract (car bs) 3) (get genv)))
               (rec-fill (cdr bs) (cdr cells))))))

;; Whether `x` is a lambda, under any type abstractions and ascriptions.
(define lambda-exp? (subr (read @globals) (exp) bool)
  (lambda (x)
    (tagcase x
      (e-lambda (ps body a b) #t)
      (e-plambda (d body a b) (lambda-exp? body))
      (e-the (d body a b) (lambda-exp? body))
      (e-convention (cnv body a b) (lambda-exp? body))
      (else y #f))))

;; Defines `n` as `x`'s value, run in the scope before it.
(define ev-define (subr (maxeff evals spin) (symbol exp) val)
  (lambda (n x)
    (let ((v (eval x (get genv))))
      (begin (bloblet-set! (push-global n) 0 v) (v-unit)))))

(define eval-top (subr (maxeff evals spin) (top) val)
  (lambda (t)
    (tagcase t
      (t-define (n ty x a b)
        (if (null? ty)
            ;; Not recursive: the value first, in the scope before it.
            (ev-define n x)
            (if (lambda-exp? x)
                ;; A lambda: the cell first, so that it can call itself.
                (let ((c (push-global n))) (begin (bloblet-set! c 0 (eval x (get genv))) (v-unit)))
                (ev-define n x))))
      ;; Every name's cell first; then each lambda, which runs nothing.
      (t-define-rec (bs a b) (begin (rec-fill bs (rec-cells bs)) (v-unit)))
      (t-exp (x) (eval x (get genv)))
      (else x (v-unit)))))

;; The value so far, after top-level form `t` gave `v`: `v` if `t` is an
;; expression, else `last`, as before.
(define ev-last (subr pure (top val val) val)
  (lambda (t v last) (tagcase t (t-exp (x) v) (else y last))))

;; The value of the last form, or the first error.
(define eval-program (subr (maxeff evals spin) ((listof top acyclic)) eresult)
  (lambda (tops)
    (prompt eval-tag
      (letrec ((go (subr (maxeff (read @globals) evals spin) ((listof top acyclic) val) val)
                 (lambda (ts last)
                   (if (null? ts)
                       last
                       (let ((v (eval-top (car ts))))
                         (go (cdr ts) (ev-last (car ts) v last)))))))
        (ev-ok (go tops (v-unit))))
      (lambda (r) r))))

;; Name `n`, and a `define-rec`'s names, to keep their cells.
(define ev-keep! (subr (maxeff (read @globals) (read @v) (write @v)) (symbol) unit)
  (lambda (n) (set ev-keep (the (listof symbol acyclic) (cons n (get ev-keep))))))
(define ev-keep-all (subr (maxeff (read @globals) (read @v) (write @v)) (exp-letrec-bs) unit)
  (lambda (bs) (if (null? bs) #u (begin (ev-keep! (extract (car bs) 1)) (ev-keep-all (cdr bs))))))

;; Before a run that assigns its names' globals: each keeps its cell.
(define ev-keep-names (subr (maxeff (read @globals) (read @v) (write @v)) (top) unit)
  (lambda (t)
    (tagcase t
      (t-define (n ty x a b) (ev-keep! n))
      (t-define-rec (bs a b) (ev-keep-all bs))
      (else y #u))))

;; What a checked program runs (`checked-tops`), each in turn: the value of
;; the last expression, or the first error.
(define eval-runs (subr (maxeff evals spin) ((listof k-run acyclic)) eresult)
  (lambda (runs)
    (prompt eval-tag
      (letrec ((go (subr (maxeff (read @globals) evals spin) ((listof k-run acyclic) val) val)
                 (lambda (rs last)
                   (if (null? rs)
                       last
                       (let* ((r (car rs))
                              (kept (if (extract r 2) (ev-keep-names (extract r 1)) #u))
                              (v (eval-top (extract r 1))))
                         (go (cdr rs) (ev-last (extract r 1) v last)))))))
        (ev-ok (go runs (v-unit))))
      (lambda (r) r))))

(define length-pairs (subr (maxeff (read @globals) (read @v) spin) (vfields) int)
  (lambda (xs) (if (null? xs) 0 (+ 1 (length-pairs (cdr xs))))))

;;; --------------------------------------------------------------- showing
;;; As Scheme's writer shows what the lowered program computes.

;; How Scheme writes a bloblet of `n` fields and `m` bytes.
(define show-bloblet (subr (read @globals) (int int) string)
  (lambda (n m) (k-cat5 "#<bloblet " (int->string n) " fields " (int->string m) " bytes>")))

;; A value as Scheme would write it. A list may be cyclic (built with
;; `set-cdr!`), and values have no identity to compare here, so the walk
;; has fuel: past it, `…`. The car of a pair gets half what is left, so a
;; cycle through cars and cdrs alike stays bounded too.
(define-rec
  (show-val (subr (maxeff (read @globals) (read @v) spin) (val) string)
    (lambda (v) (show-val-in v 10000)))
  (show-val-in (subr (maxeff (read @globals) (read @v) spin) (val int) string)
    (lambda (v fuel)
      (tagcase v
        (v-int (n) (int->string n))
        (v-bool (b) (if b "#t" "#f"))
        (v-str (s) (string-append "\"" (string-append s "\"")))
        (v-char (c) (string-append "#\\" (char->string c)))
        (v-f64 (x) (f64->string x))
        (v-f32 (x) (f32->string x))
        (v-sym (s) (symbol->string s))
        (v-unit () "#u")
        (v-nil () "()")
        (v-pair (p) (if (<= fuel 0) "…" (k-cat3 "(" (show-items p fuel) ")")))
        (v-ref (r) "#<box>")
        (v-icell (c) "#<bloblet 3 fields 0 bytes>")
        (v-array (a) (show-bloblet (+ 1 (array-length a)) 0))
        (v-blob (fs bs) (show-bloblet (+ 1 (array-length fs)) (array-length bs)))
        (v-product (fs) (k-cat3 "#<product of " (int->string (length-pairs fs)) ">"))
        (v-sum (t x) (k-cat3 "#<sum " (symbol->string t) ">"))
        (v-clo (ps body e) "#<procedure>")
        (v-vsubr (g) "#<procedure>")
        (v-prim (n) "#<procedure>")
        (v-tag (t) "#<prompt-tag>")
        (v-cont (k) "#<continuation>")
        (v-esc (k) "#<continuation>")
        (v-key (k) "#<mark-key>"))))
  ;; A list's elements, space-separated, and a dotted tail.
  (show-items (subr (maxeff (read @globals) (read @v) spin) (vpair int) string)
    (lambda (p fuel)
      (let ((head (show-val-in (bloblet-ref p 0) (quotient fuel 2))) (tail (bloblet-ref p 1)))
        (tagcase tail
          (v-nil () head)
          (v-pair (q)
            (if (<= fuel 1)
                (string-append head " …")
                (k-cat3 head " " (show-items q (- fuel 1)))))
          (else x (k-cat3 head " . " (show-val-in tail (- fuel 1)))))))))

;; A whole program begins with no globals, and no names kept.
(define ev-begin! (subr stores (k-reshape-list) unit)
  (lambda (rs) (begin (set genv nil) (set ev-keep nil) (set ev-reshapes rs))))
;; The entry point for a program the checker written in FX-26 checked: what
;; it runs (`checked-tops`, under redefinition), run; its value shown, or
;; its error. A whole program, as each is.
(define run-checked (subr (maxeff evals (read @t) spin) ((listof k-run acyclic)) string)
  (lambda (runs)
    (tagcase (begin (ev-begin! (get k-reshapes)) (eval-runs runs))
      (ev-ok (v) (show-val v))
      (ev-err (m) (string-append "!! " m)))))

;; The entry point: a program's trees, run; its value shown, or its error.
(define run-program (subr (maxeff evals spin) ((listof top acyclic)) string)
  (lambda (tops)
    (tagcase (begin (ev-begin! nil) (eval-program tops))
      (ev-ok (v) (show-val v))
      (ev-err (m) (string-append "!! " m)))))
