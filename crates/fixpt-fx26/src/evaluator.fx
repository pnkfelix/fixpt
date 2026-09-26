;;; An FX-26 evaluator, in FX-26 (PLAN.md §11, step 9b).
;;;
;;; FX-26's meaning, written in FX-26: the trees `parser.fx` makes, run
;;; directly. It is the reference the compiler to threaded code (step 9d) is
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

(define-datatype val
  (v-int int)
  (v-bool bool)
  (v-str string)
  (v-char char)
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
  (v-clo (listof (productof (1 symbol) (2 syns-a)) @a) exp (listof (pairof symbol (bloblet (fields val) @v) @v) @v))
  (v-prim symbol)
  (v-tag (prompt-tag val val (maxeff (read @a) (read @v) (write @v) (alloc @v) (read @x) (write @x) (alloc @x)) @x))
  (v-cont (composable val val (maxeff (read @a) (read @v) (write @v) (alloc @v) (read @x) (write @x) (alloc @x)) @x))
  (v-esc (subr (goto @x) (val) void))
  (v-key (mark-key val @x)))

;; Local variables: each name and the cell that holds its value.
(define-type env (listof (pairof symbol (bloblet (fields val) @v) @v) @v))
(define-type vals (listof val @v))

;; What a delimited part of the program may do, besides control on @x.
(define-effect runs (maxeff (read @a) (read @v) (write @v) (alloc @v) (read @x) (write @x) (alloc @x)))
;; What evaluating may do: read the trees, run the program on @v, mark and
;; transfer control on @x, and stop with an error.
(define-effect evals (maxeff runs (goto @x) (comefrom @x)))

(define-datatype eresult (ev-ok val) (ev-err string))
(define eval-tag (prompt-tag eresult eresult runs @x)
  (make-continuation-prompt-tag))
(define efail (subr evals (string) void)
  (lambda (message) (abort-current-continuation eval-tag (ev-err message))))

;; The global environment, newest first.
(define genv (ref env @v) (new nil))

;;; ---------------------------------------------------------------- values

(define cell (subr (alloc @v) (val) (bloblet (fields val) @v))
  (lambda (v) (make-bloblet 0 v)))

(define as-int (subr evals (val) int)
  (lambda (v) (tagcase v (v-int (n) n) (else x (efail "an int is expected")))))
(define as-bool (subr evals (val) bool)
  (lambda (v) (tagcase v (v-bool (b) b) (else x (efail "a bool is expected")))))
(define as-str (subr evals (val) string)
  (lambda (v) (tagcase v (v-str (s) s) (else x (efail "a string is expected")))))
(define as-char (subr evals (val) char)
  (lambda (v) (tagcase v (v-char (c) c) (else x (efail "a char is expected")))))
(define as-sym (subr evals (val) symbol)
  (lambda (v) (tagcase v (v-sym (s) s) (else x (efail "a symbol is expected")))))
(define as-pair (subr evals (val) (bloblet (fields val val) @v))
  (lambda (v) (tagcase v (v-pair (p) p) (else x (efail "a pair is expected")))))
(define as-ref (subr evals (val) (bloblet (fields val) @v))
  (lambda (v) (tagcase v (v-ref (r) r) (else x (efail "a reference is expected")))))
(define as-array (subr evals (val) (arrayof val @v))
  (lambda (v) (tagcase v (v-array (a) a) (else x (efail "an array is expected")))))
(define as-icell (subr evals (val) (bloblet (fields val val) @v))
  (lambda (v) (tagcase v (v-icell (c) c) (else x (efail "an i-cell is expected")))))
(define icell-full? (subr (read @v) ((bloblet (fields val val) @v)) bool)
  (lambda (c) (tagcase (bloblet-ref c 0) (v-bool (b) b) (else x #f))))

(define as-tag (subr evals (val) (prompt-tag val val runs @x))
  (lambda (v) (tagcase v (v-tag (t) t) (else x (efail "a prompt tag is expected")))))
(define as-key (subr evals (val) (mark-key val @x))
  (lambda (v) (tagcase v (v-key (k) k) (else x (efail "a mark key is expected")))))
(define as-cont (subr evals (val) (composable val val runs @x))
  (lambda (v) (tagcase v (v-cont (k) k) (else x (efail "a composable continuation is expected")))))

;; The evaluator's list of values, as the program's.
(define list->val (subr (maxeff (read @x) (alloc @v)) ((listof val @x)) val)
  (lambda (xs) (if (null? xs) (v-nil) (v-pair (make-bloblet 0 (car xs) (list->val (cdr xs)))))))

(define arg (subr evals (vals int) val)
  (lambda (xs i)
    (cond ((null? xs) (efail "too few arguments"))
          ((= i 0) (car xs))
          (else (arg (cdr xs) (- i 1))))))

;;; ------------------------------------------------------------ primitives

;; The primitives the evaluator has, between spaces.
(define primitive-names string
  " + - * = < > <= >= not modulo quotient cons car cdr null? set-car! set-cdr! new get set make-icell icell-put! icell-get char=? char->integer integer->char string-append string-length string-ref string=? string->symbol symbol->string symbol=? char->string make-array array-ref array-set! array-length make-continuation-prompt-tag abort-current-continuation call-with-composable-continuation make-continuation-mark-key with-mark first-mark current-marks marks-of cwcc ")

;; Whether `needle` occurs in `hay` from position `i` on.
(define occurs? (subr pure (string string int) bool)
  (lambda (needle hay i)
    (and (<= (+ i (string-length needle)) (string-length hay))
         (or (string=? (substring hay i (+ i (string-length needle))) needle)
             (occurs? needle hay (+ i 1))))))

(define primitive? (subr pure (string) bool)
  (lambda (n) (occurs? (string-append " " (string-append n " ")) primitive-names 0)))

;; A standard name: a primitive, or `nil`.
(define standard (subr evals (symbol) val)
  (lambda (name)
    (if (string=? (symbol->string name) "nil")
        (v-nil)
        (if (primitive? (symbol->string name))
            (v-prim name)
            (efail (string-append "unbound variable `" (string-append (symbol->string name) "`")))))))

(define lookup (subr evals (env symbol) val)
  (lambda (e name)
    (cond ((null? e) (standard name))
          ((symbol=? (car (car e)) name) (bloblet-ref (cdr (car e)) 0))
          (else (lookup (cdr e) name)))))

(define int2 (subr evals (vals (subr pure (int int) int)) val)
  (lambda (xs f) (v-int (f (as-int (arg xs 0)) (as-int (arg xs 1))))))
(define cmp2 (subr evals (vals (subr pure (int int) bool)) val)
  (lambda (xs f) (v-bool (f (as-int (arg xs 0)) (as-int (arg xs 1))))))

;;; ------------------------------------------------------------- evaluating

(define bind (subr evals ((listof (productof (1 symbol) (2 syns-a)) @a) vals env) env)
  (lambda (ps xs e)
    (cond ((and (null? ps) (null? xs)) e)
          ((or (null? ps) (null? xs)) (efail "the wrong number of arguments"))
          (else (cons (cons (extract (car ps) 1) (cell (car xs))) (bind (cdr ps) (cdr xs) e))))))

(define find-cell (subr evals (env symbol) (bloblet (fields val) @v))
  (lambda (e n)
    (cond ((null? e) (efail "no such local"))
          ((symbol=? (car (car e)) n) (cdr (car e)))
          (else (find-cell (cdr e) n)))))

(define field-of (subr evals (val symbol) val)
  (lambda (p l)
    (letrec ((find (subr evals ((listof (pairof symbol val @v) @v)) val)
               (lambda (fs)
                 (cond ((null? fs) (efail "no such label"))
                       ((symbol=? (car (car fs)) l) (cdr (car fs)))
                       (else (find (cdr fs)))))))
      (tagcase p (v-product (fs) (find fs)) (else x (efail "a product is expected"))))))

;; An arm's names, bound to a product's fields in order.
(define bind-fields (subr evals (names val env) env)
  (lambda (ns p e)
    (letrec ((go (subr evals (names (listof (pairof symbol val @v) @v) env) env)
               (lambda (ns fs e)
                 (cond ((and (null? ns) (null? fs)) e)
                       ((or (null? ns) (null? fs)) (efail "the wrong number of fields"))
                       (else (go (cdr ns) (cdr fs) (cons (cons (car ns) (cell (cdr (car fs)))) e)))))))
      (tagcase p (v-product (fs) (go ns fs e)) (else x (efail "a product is expected"))))))

(define length-of (subr (read @v) (vals) int)
  (lambda (xs) (if (null? xs) 0 (+ 1 (length-of (cdr xs))))))
(define fill-array (subr (maxeff (read @v) (write @v)) ((arrayof val @v) vals int) unit)
  (lambda (a xs i) (if (null? xs) #u (begin (array-set! a i (car xs)) (fill-array a (cdr xs) (+ i 1))))))

(define eval-bloblet (subr evals (string int vals) val)
  (lambda (op i xs)
    (cond ((string=? op "make-bloblet")
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
                     ((string=? op "bloblet-set-byte!") (begin (array-set! bs (as-int (arg xs 1)) (as-int (arg xs 2))) (v-unit)))
                     (else (v-int (array-length bs)))))
             (else x (efail "a bloblet is expected")))))))

(define-rec
  (apply-prim (subr evals (string vals) val)
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
            ((string=? n "cons") (v-pair (make-bloblet 0 (arg xs 0) (arg xs 1))))
            ((string=? n "car") (bloblet-ref (as-pair (arg xs 0)) 0))
            ((string=? n "cdr") (bloblet-ref (as-pair (arg xs 0)) 1))
            ((string=? n "null?") (v-bool (tagcase (arg xs 0) (v-nil () #t) (else x #f))))
            ((string=? n "set-car!") (begin (bloblet-set! (as-pair (arg xs 0)) 0 (arg xs 1)) (v-unit)))
            ((string=? n "set-cdr!") (begin (bloblet-set! (as-pair (arg xs 0)) 1 (arg xs 1)) (v-unit)))
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
               (if (icell-full? c) (bloblet-ref c 1) (efail "an i-cell read before it was written"))))
            ((string=? n "char=?") (v-bool (char=? (as-char (arg xs 0)) (as-char (arg xs 1)))))
            ((string=? n "char->integer") (v-int (char->integer (as-char (arg xs 0)))))
            ((string=? n "integer->char") (v-char (integer->char (as-int (arg xs 0)))))
            ((string=? n "char->string") (v-str (char->string (as-char (arg xs 0)))))
            ((string=? n "string-append") (v-str (string-append (as-str (arg xs 0)) (as-str (arg xs 1)))))
            ((string=? n "string-length") (v-int (string-length (as-str (arg xs 0)))))
            ((string=? n "string-ref") (v-char (string-ref (as-str (arg xs 0)) (as-int (arg xs 1)))))
            ((string=? n "string=?") (v-bool (string=? (as-str (arg xs 0)) (as-str (arg xs 1)))))
            ((string=? n "string->symbol") (v-sym (string->symbol (as-str (arg xs 0)))))
            ((string=? n "symbol->string") (v-str (symbol->string (as-sym (arg xs 0)))))
            ((string=? n "symbol=?") (v-bool (symbol=? (as-sym (arg xs 0)) (as-sym (arg xs 1)))))
            ((string=? n "make-array") (v-array (make-array (as-int (arg xs 0)) (arg xs 1))))
            ((string=? n "array-ref") (array-ref (as-array (arg xs 0)) (as-int (arg xs 1))))
            ((string=? n "array-set!") (begin (array-set! (as-array (arg xs 0)) (as-int (arg xs 1)) (arg xs 2)) (v-unit)))
            ((string=? n "array-length") (v-int (array-length (as-array (arg xs 0)))))
            ((string=? n "make-continuation-prompt-tag") (v-tag (make-continuation-prompt-tag)))
            ((string=? n "abort-current-continuation") (abort-current-continuation (as-tag (arg xs 0)) (arg xs 1)))
            ((string=? n "call-with-composable-continuation")
             (let ((f (arg xs 0)))
               (call-with-composable-continuation
                (lambda (k) (apply-val f (the vals (cons (v-cont k) nil))))
                (as-tag (arg xs 1)))))
            ((string=? n "cwcc")
             (let ((f (arg xs 0)))
               ;; At @x, which nothing here would infer: the escape is kept.
               ((proj (proj (proj cwcc @x) val) evals) (lambda (k) (apply-val f (the vals (cons (v-esc k) nil)))))))
            ((string=? n "make-continuation-mark-key") (v-key (make-continuation-mark-key)))
            ((string=? n "with-mark")
             (let ((thunk (arg xs 2)))
               (with-mark (as-key (arg xs 0)) (arg xs 1) (lambda () (apply-val thunk (the vals nil))))))
            ((string=? n "first-mark") (first-mark (as-key (arg xs 0)) (arg xs 1)))
            ((string=? n "current-marks") (list->val (current-marks (as-key (arg xs 0)))))
            ((string=? n "marks-of") (list->val (marks-of (as-cont (arg xs 0)) (as-key (arg xs 1)))))
            (else (efail (string-append "not in the evaluator yet: " n))))))
  (apply-val (subr evals (val vals) val)
    (lambda (f xs)
      (tagcase f
        (v-clo (ps body e) (eval body (bind ps xs e)))
        (v-prim (n) (apply-prim (symbol->string n) xs))
        (v-cont (k) (k (arg xs 0)))
        (v-esc (k) (k (arg xs 0)))
        (else x (efail "not a subroutine")))))
  (eval-all (subr evals ((listof exp @a) env) vals)
    (lambda (es e) (if (null? es) nil (let ((v (eval (car es) e))) (cons v (eval-all (cdr es) e))))))
  (eval-begin (subr evals ((listof exp @a) env) val)
    (lambda (es e)
      (cond ((null? es) (v-unit))
            ((null? (cdr es)) (eval (car es) e))
            (else (begin (eval (car es) e) (eval-begin (cdr es) e))))))
  (eval (subr evals (exp env) val)
    (lambda (x e)
      (tagcase x
        (e-var (n a b) (lookup e n))
        (e-int (n a b) (v-int n))
        (e-bool (v a b) (v-bool v))
        (e-str (s a b) (v-str s))
        (e-char (c a b) (v-char c))
        (e-sym (s a b) (v-sym s))
        (e-unit (a b) (v-unit))
        (e-lambda (ps body a b) (v-clo ps body e))
        (e-app (f args a b) (let* ((fv (eval f e)) (xs (eval-all args e))) (apply-val fv xs)))
        (e-plambda (d body a b) (eval body e))
        ;; Regions are erased: a `letrena`'s or `letreap`'s allocation is the heap's.
        (e-letregion (k r body a b) (eval body e))
        (e-proj (body ds a b) (eval body e))
        (e-the (d body a b) (eval body e))
        (e-if (t th el a b) (if (as-bool (eval t e)) (eval th e) (eval el e)))
        (e-letrec (bs body a b) (eval-letrec bs body e))
        (e-let (bs body a b) (eval body (eval-let bs e e)))
        (e-begin (es a b) (eval-begin es e))
        (e-prompt (t body h a b)
          (let* ((tag (as-tag (eval t e))) (hv (eval h e)))
            (prompt tag (eval body e) (lambda (v) (apply-val hv (the vals (cons v nil)))))))
        (e-bloblet (op i args a b) (eval-bloblet (symbol->string op) i (eval-all args e)))
        (e-product (fs a b) (v-product (eval-fields fs e)))
        (e-extract (p l a b) (field-of (eval p e) l))
        (e-sum (t v a b) (v-sum t (eval v e)))
        (e-tagcase (s arms els a b) (eval-tagcase (eval s e) arms els e)))))
  (eval-let (subr evals ((listof (productof (1 symbol) (2 exp)) @a) env env) env)
    (lambda (bs outer e)
      (if (null? bs)
          e
          (let ((v (eval (extract (car bs) 2) outer)))
            (eval-let (cdr bs) outer (cons (cons (extract (car bs) 1) (cell v)) e))))))
  ;; Every name first, holding #u; then each value, in the scope of all.
  (eval-letrec (subr evals ((listof (productof (1 symbol) (2 syn) (3 exp)) @a) exp env) val)
    (lambda (bs body e)
      (letrec ((open (subr evals ((listof (productof (1 symbol) (2 syn) (3 exp)) @a) env) env)
                 (lambda (bs e) (if (null? bs) e (open (cdr bs) (cons (cons (extract (car bs) 1) (cell (v-unit))) e)))))
               (fill (subr evals ((listof (productof (1 symbol) (2 syn) (3 exp)) @a) env) unit)
                 (lambda (bs inner)
                   (if (null? bs)
                       #u
                       (begin (bloblet-set! (find-cell inner (extract (car bs) 1)) 0 (eval (extract (car bs) 3) inner))
                              (fill (cdr bs) inner))))))
        (let ((inner (open bs e)))
          (begin (fill bs inner) (eval body inner))))))
  (eval-fields (subr evals ((listof (productof (1 symbol) (2 exp)) @a) env) (listof (pairof symbol val @v) @v))
    (lambda (fs e)
      (if (null? fs)
          nil
          (let ((v (eval (extract (car fs) 2) e)))
            (cons (cons (extract (car fs) 1) v) (eval-fields (cdr fs) e))))))
  (eval-tagcase
    (subr evals (val (listof (productof (1 symbol) (2 bool) (3 names) (4 exp)) @a) (listof (productof (1 symbol) (2 exp)) @a) env) val)
    (lambda (s arms els e)
      (tagcase s
        (v-sum (tag v)
          (letrec ((try (subr evals ((listof (productof (1 symbol) (2 bool) (3 names) (4 exp)) @a)) val)
                     (lambda (as)
                       (cond ((null? as)
                              (if (null? els)
                                  (efail "no arm for this value")
                                  (eval (extract (car els) 2) (cons (cons (extract (car els) 1) (cell s)) e))))
                             ((symbol=? (extract (car as) 1) tag)
                              (eval (extract (car as) 4)
                                    (if (extract (car as) 2)
                                        (bind-fields (extract (car as) 3) v e)
                                        (cons (cons (car (extract (car as) 3)) (cell v)) e))))
                             (else (try (cdr as)))))))
            (try arms)))
        (else x (efail "a sum is expected"))))))

;;; ------------------------------------------------------------- programs

(define bound? (subr (read @v) (env symbol) bool)
  (lambda (e n) (and (not (null? e)) (or (symbol=? (car (car e)) n) (bound? (cdr e) n)))))

(define push-global (subr (maxeff (read @v) (write @v) (alloc @v)) (symbol) (bloblet (fields val) @v))
  (lambda (n) (let ((c (cell (v-unit)))) (begin (set genv (cons (cons n c) (get genv))) c))))


(define rec-cells (subr (maxeff (read @a) (read @v) (write @v) (alloc @v)) ((listof (productof (1 symbol) (2 syn) (3 exp)) @a)) (listof (bloblet (fields val) @v) @v))
  (lambda (bs) (if (null? bs) nil (let ((c (push-global (extract (car bs) 1)))) (cons c (rec-cells (cdr bs)))))))
(define rec-fill (subr evals ((listof (productof (1 symbol) (2 syn) (3 exp)) @a) (listof (bloblet (fields val) @v) @v)) unit)
  (lambda (bs cells)
    (if (null? bs)
        #u
        (begin (bloblet-set! (car cells) 0 (eval (extract (car bs) 3) (get genv))) (rec-fill (cdr bs) (cdr cells))))))

;; Whether `x` is a lambda, under any type abstractions and ascriptions.
(define lambda-exp? (subr (read @a) (exp) bool)
  (lambda (x)
    (tagcase x
      (e-lambda (ps body a b) #t)
      (e-plambda (d body a b) (lambda-exp? body))
      (e-the (d body a b) (lambda-exp? body))
      (else y #f))))

(define eval-top (subr evals (top) val)
  (lambda (t)
    (tagcase t
      (t-define (n ty x a b)
        (if (null? ty)
            ;; Not recursive: the value first, in the scope before it.
            (let ((v (eval x (get genv)))) (begin (bloblet-set! (push-global n) 0 v) (v-unit)))
            (if (lambda-exp? x)
                ;; A lambda: the cell first, so that it can call itself.
                (let ((c (push-global n))) (begin (bloblet-set! c 0 (eval x (get genv))) (v-unit)))
                (let ((v (eval x (get genv)))) (begin (bloblet-set! (push-global n) 0 v) (v-unit))))))
      ;; Every name's cell first; then each lambda, which runs nothing.
      (t-define-rec (bs a b) (begin (rec-fill bs (rec-cells bs)) (v-unit)))
      (t-exp (x) (eval x (get genv)))
      (else x (v-unit)))))

;; The value of the last form, or the first error.
(define eval-program (subr evals ((listof top @a)) eresult)
  (lambda (tops)
    (prompt eval-tag
      (letrec ((go (subr evals ((listof top @a) val) val)
                 (lambda (ts last)
                   (if (null? ts) last (let ((v (eval-top (car ts)))) (go (cdr ts) (tagcase (car ts) (t-exp (x) v) (else y last))))))))
        (ev-ok (go tops (v-unit))))
      (lambda (r) r))))

(define length-pairs (subr (read @v) ((listof (pairof symbol val @v) @v)) int)
  (lambda (xs) (if (null? xs) 0 (+ 1 (length-pairs (cdr xs))))))

;;; --------------------------------------------------------------- showing
;;; As Scheme's writer shows what the lowered program computes.

(define-rec
  (show-val (subr (read @v) (val) string)
    (lambda (v)
      (tagcase v
        (v-int (n) (int->string n))
        (v-bool (b) (if b "#t" "#f"))
        (v-str (s) (string-append "\"" (string-append s "\"")))
        (v-char (c) (string-append "#\\" (char->string c)))
        (v-sym (s) (symbol->string s))
        (v-unit () "#u")
        (v-nil () "()")
        (v-pair (p) (string-append "(" (string-append (show-items p) ")")))
        (v-ref (r) "#<box>")
        (v-icell (c) "#<bloblet 3 fields 0 bytes>")
        (v-array (a) (string-append "#<bloblet " (string-append (int->string (+ 1 (array-length a))) " fields 0 bytes>")))
        (v-blob (fs bs)
          (string-append "#<bloblet "
            (string-append (int->string (+ 1 (array-length fs)))
              (string-append " fields " (string-append (int->string (array-length bs)) " bytes>")))))
        (v-product (fs) (string-append "#<product of " (string-append (int->string (length-pairs fs)) ">")))
        (v-sum (t x) (string-append "#<sum " (string-append (symbol->string t) ">")))
        (v-clo (ps body e) "#<procedure>")
        (v-prim (n) "#<procedure>")
        (v-tag (t) "#<prompt-tag>")
        (v-cont (k) "#<continuation>")
        (v-esc (k) "#<continuation>")
        (v-key (k) "#<mark-key>"))))
  ;; A list's elements, space-separated, and a dotted tail.
  (show-items (subr (read @v) ((bloblet (fields val val) @v)) string)
    (lambda (p)
      (let ((head (show-val (bloblet-ref p 0))) (tail (bloblet-ref p 1)))
        (tagcase tail
          (v-nil () head)
          (v-pair (q) (string-append head (string-append " " (show-items q))))
          (else x (string-append head (string-append " . " (show-val tail)))))))))

;; The entry point: a program's trees, run; its value shown, or its error.
(define run-program (subr evals ((listof top @a)) string)
  (lambda (tops)
    (tagcase (eval-program tops)
      (ev-ok (v) (show-val v))
      (ev-err (m) (string-append "!! " m)))))
