;;; SCHEME -- A Scheme interpreter evaluating a sort, written by Marc Feeley.
;;;
;;; From Larceny's R7RS benchmarks (test/Benchmarking/R7RS/src/scheme.scm),
;;; ported to FX-26. Larceny's input: 100000 iterations of (scheme-eval
;;; EXPR), EXPR a merge sort of thirty number names by string<?.
;;; Answer: ("eight" "eighteen" "eleven" "fifteen" "five" "four" "fourteen"
;;; "nine" "nineteen" "one" "seven" "seventeen" "six" "sixteen" "ten"
;;; "thirteen" "thirty" "three" "twelve" "twenty" "twentyeight" "twentyfive"
;;; "twentyfour" "twentynine" "twentyone" "twentyseven" "twentysix"
;;; "twentythree" "twentytwo" "two").
;;;
;;; What changed:
;;; - The interpreted program's values, and the expressions it compiles,
;;;   are one datatype, `obj`: Scheme's own data, the interpreter's
;;;   environments (vectors whose slot 0 is the enclosing one, as in the
;;;   original) and its procedures. Pairs are mutable host pairs.
;;; - An interpreted procedure is one host procedure taking the argument
;;;   count, the first three arguments and a list of the rest (a calling
;;;   convention's argc register and spill list): `(f a b)` is `(p 2 a b _ _)`.
;;;   Where the original's closures are `(lambda (a b) ...)`,
;;;   `(lambda (a . b) ...)` or `(lambda (a b c . d) ...)`, these check the
;;;   count and cons the same rest lists; `apply` spreads a list the same way.
;;; - EXPR, which Larceny reads before timing, is read here from a string,
;;;   by a small reader in this file, before timing too.
;;; - Constants `(lambda (rte) 0)` and the like return preallocated objects;
;;;   the symbols the compiler builds forms with (`'lambda`, `'letrec`, ...)
;;;   are global objects, as Scheme's symbols are constants.
;;; - `eq?`, `eqv?` and `memq` compare atoms by value; FX-26 has no identity
;;;   test, so on pairs, strings, vectors and procedures they answer #f. The
;;;   interpreter only ever compares symbols.
;;; - The global table has all of the original's 151 entries, in its order,
;;;   so that looking names up costs what it did. Those FX-26 cannot provide
;;;   (floating point and rationals: `/`, `exp` ... `sqrt`, `exact->inexact`;
;;;   `string->number`; `string-set!`, strings being immutable; and every
;;;   port operation) are procedures that fail when called; nothing calls
;;;   them. Comparisons that are variadic in Scheme take two arguments.
;;;   `char-upcase` and `char-lower-case?` know ASCII only.
;;; - `vector-set!` and friends return '() where Scheme's value is
;;;   unspecified. `scheme-error` stops the run with an error, an index out
;;;   of range: FX-26 has no `error`, and natively `(car nil)` crashes the
;;;   process (signal 11) rather than failing.
;;; - `char-downcase`, passed as a value, is wrapped in a lambda
;;;   (`char-down`): the native compiler takes a primitive only as an
;;;   operator ("not yet compiled as a value").

(define-effect ev (maxeff (read @heap) (write @heap) (alloc @heap) spin (read @globals)))

(define-datatype obj
  (onull)
  (obool bool)
  (oint int)
  (ochar char)
  (ostr string)
  (osym symbol)
  (opair (pairof obj obj @heap))
  (ovec (arrayof obj @heap))
  (oproc (subr ev (int obj obj obj obj) obj)))

(define-type objs (listof obj @heap))
(define-type code (subr ev (obj) obj))
(define-type codes (listof code @heap))
(define-type case-code (subr ev (obj obj) obj))
;; The environment chain: '() or (enclosing-chain . frame).
(define-type chain (union nil (pairof chain objs @heap)))
(define-type macros (listof (pairof obj obj @heap) @heap))
(define-type env (pairof chain macros @heap))
(define-type cell (pairof obj obj @heap))

(define obj-null obj (onull))
(define obj-false obj (obool #f))
(define obj-true obj (obool #t))
(define obj-m2 obj (oint -2))
(define obj-m1 obj (oint -1))
(define obj-0 obj (oint 0))
(define obj-1 obj (oint 1))
(define obj-2 obj (oint 2))
(define no-objects (arrayof obj @heap) (make-array 0 obj-null))

(define* scheme-error (subr (read @heap) (string obj) obj)
  (lambda (msg x) (array-ref no-objects 0)))

(define* true? (subr pure (obj) bool)
  (lambda (x) (tagcase x (obool (b) b) (else y #t))))
(define* bool->obj (subr pure (bool) obj)
  (lambda (b) (if b obj-true obj-false)))

(define* ocons (subr (alloc @heap) (obj obj) obj)
  (lambda (a d) (opair (cons a d))))
(define* olist1 (subr (alloc @heap) (obj) obj)
  (lambda (a) (ocons a obj-null)))
(define* olist2 (subr (alloc @heap) (obj obj) obj)
  (lambda (a b) (ocons a (ocons b obj-null))))
(define* olist3 (subr (alloc @heap) (obj obj obj) obj)
  (lambda (a b c) (ocons a (ocons b (ocons c obj-null)))))

(define* is-pair? (subr pure (obj) bool)
  (lambda (x) (tagcase x (opair (p) #t) (else y #f))))
(define* is-null? (subr pure (obj) bool)
  (lambda (x) (tagcase x (onull () #t) (else y #f))))
(define* is-symbol? (subr pure (obj) bool)
  (lambda (x) (tagcase x (osym (s) #t) (else y #f))))
(define* is-vector? (subr pure (obj) bool)
  (lambda (x) (tagcase x (ovec (v) #t) (else y #f))))
(define* is-sym? (subr pure (obj symbol) bool)
  (lambda (x s) (tagcase x (osym (t) (symbol=? t s)) (else y #f))))

(define* obj-car (subr (read @heap) (obj) obj)
  (lambda (x) (tagcase x (opair (p) (car p)) (else y (scheme-error "car: not a pair" x)))))
(define* obj-cdr (subr (read @heap) (obj) obj)
  (lambda (x) (tagcase x (opair (p) (cdr p)) (else y (scheme-error "cdr: not a pair" x)))))
(define* obj-cadr (subr (read @heap) (obj) obj) (lambda (x) (obj-car (obj-cdr x))))
(define* obj-cddr (subr (read @heap) (obj) obj) (lambda (x) (obj-cdr (obj-cdr x))))
(define* obj-caddr (subr (read @heap) (obj) obj) (lambda (x) (obj-car (obj-cddr x))))
(define* obj-cdddr (subr (read @heap) (obj) obj) (lambda (x) (obj-cdr (obj-cddr x))))
(define* obj-cadddr (subr (read @heap) (obj) obj) (lambda (x) (obj-car (obj-cdddr x))))
(define* obj-int (subr (read @heap) (obj) int)
  (lambda (x) (tagcase x (oint (n) n) (else y (begin (scheme-error "not an integer" x) 0)))))

;; eq? and eqv?: atoms by value (see the header).
(define* obj-eq? (subr pure (obj obj) bool)
  (lambda (x y)
    (tagcase x
      (osym (a) (tagcase y (osym (b) (symbol=? a b)) (else z #f)))
      (onull () (tagcase y (onull () #t) (else z #f)))
      (obool (a) (tagcase y (obool (b) (if a b (not b))) (else z #f)))
      (oint (a) (tagcase y (oint (b) (= a b)) (else z #f)))
      (ochar (a) (tagcase y (ochar (b) (char=? a b)) (else z #f)))
      (else z #f))))

(define* obj-length (subr (maxeff (read @heap) spin) (obj) int)
  (lambda (l) (tagcase l (opair (p) (+ 1 (obj-length (cdr p)))) (else y 0))))
(define* obj-append (subr (maxeff (read @heap) (alloc @heap) spin) (obj obj) obj)
  (lambda (xs ys)
    (tagcase xs (opair (p) (ocons (car p) (obj-append (cdr p) ys))) (else y ys))))
(define* obj-memv (subr (maxeff (read @heap) spin (read @globals)) (obj obj) bool)
  (lambda (x l)
    (tagcase l
      (opair (p) (if (obj-eq? x (car p)) #t (obj-memv x (cdr p))))
      (else y #f))))
(define* frame-length (subr (maxeff (read @heap) spin) (objs) int)
  (lambda (l) (if (null? l) 0 (+ 1 (frame-length (cdr l))))))
(define* codes-length (subr (maxeff (read @heap) spin) (codes) int)
  (lambda (l) (if (null? l) 0 (+ 1 (codes-length (cdr l))))))

(define* vector2 (subr (maxeff (alloc @heap) (write @heap)) (obj obj) obj)
  (lambda (a b)
    (let ((v (the (arrayof obj @heap) (make-array 2 a))))
      (begin (array-set! v 1 b) (ovec v)))))
(define* vector3 (subr (maxeff (alloc @heap) (write @heap)) (obj obj obj) obj)
  (lambda (a b c)
    (let ((v (the (arrayof obj @heap) (make-array 3 a))))
      (begin (array-set! v 1 b) (array-set! v 2 c) (ovec v)))))
(define* vector4 (subr (maxeff (alloc @heap) (write @heap)) (obj obj obj obj) obj)
  (lambda (a b c d)
    (let ((v (the (arrayof obj @heap) (make-array 4 a))))
      (begin (array-set! v 1 b) (array-set! v 2 c) (array-set! v 3 d) (ovec v)))))
(define* make-vec (subr (alloc @heap) (int obj) obj)
  (lambda (n fill) (ovec (make-array n fill))))
(define* vec-ref (subr (read @heap) (obj int) obj)
  (lambda (v i)
    (tagcase v (ovec (a) (array-ref a i)) (else y (scheme-error "vector-ref: not a vector" v)))))
(define* vec-set! (subr (maxeff (read @heap) (write @heap)) (obj int obj) obj)
  (lambda (v i x)
    (tagcase v
      (ovec (a) (begin (array-set! a i x) obj-null))
      (else y (scheme-error "vector-set!: not a vector" v)))))

; - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -

(define* lst->vector (subr (maxeff (read @heap) (write @heap) (alloc @heap) spin) (obj) obj)
  (lambda (l)
    (let* ((n (obj-length l))
           (v (the (arrayof obj @heap) (make-array n obj-false))))
      (letrec ((loop (subr (maxeff (read @heap) (write @heap) (alloc @heap) spin (read @globals)) (obj int) obj)
                 (lambda (l i)
                   (tagcase l
                     (opair (p) (begin (array-set! v i (car p)) (loop (cdr p) (+ i 1))))
                     (else y (ovec v))))))
        (loop l 0)))))

(define* vector->lst (subr (maxeff (read @heap) (alloc @heap) spin) (obj) obj)
  (lambda (v)
    (tagcase v
      (ovec (a)
        (letrec ((loop (subr (maxeff (read @heap) (alloc @heap) spin (read @globals)) (obj int) obj)
                   (lambda (l i) (if (< i 0) l (loop (ocons (array-ref a i) l) (- i 1))))))
          (loop obj-null (- (array-length a) 1))))
      (else y (scheme-error "vector->lst: not a vector" v)))))

; - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -

(define* symbols (subr (maxeff (read @heap) (alloc @heap) spin) ((listof symbol @heap)) objs)
  (lambda (l) (if (null? l) nil (cons (osym (car l)) (symbols (cdr l))))))

(define scheme-syntactic-keywords objs
  (symbols
    (list 'quote 'quasiquote 'unquote 'unquote-splicing
          'lambda 'if 'set! 'cond '=> 'else 'and 'or
          'case 'let 'let* 'letrec 'begin 'do 'define
          'define-macro)))

;; The symbols the compiler makes forms with.
(define s-quasiquote obj (osym 'quasiquote))
(define s-unquote obj (osym 'unquote))
(define s-unquote-splicing obj (osym 'unquote-splicing))
(define s-lambda obj (osym 'lambda))
(define s-let obj (osym 'let))
(define s-let* obj (osym 'let*))
(define s-letrec obj (osym 'letrec))
(define pair-0-1 obj (ocons (oint 0) (oint 1)))
(define pair-1-1 obj (ocons (oint 1) (oint 1)))

; - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -

(define* push-frame (subr (maxeff (read @heap) (alloc @heap)) (objs env) env)
  (lambda (frame env)
    (if (null? frame)
      env
      (cons (cons (car env) frame) (cdr env)))))

(define* lookup-var (subr (maxeff (read @heap) (alloc @heap) spin) (obj env) obj)
  (lambda (name env)
    (letrec ((loop1 (subr (maxeff (read @heap) (alloc @heap) spin (read @globals)) (chain int) obj)
               (lambda (chain up)
                 (if (null? chain)
                   name
                   (loop2 chain up (cdr chain) 1))))
             (loop2 (subr (maxeff (read @heap) (alloc @heap) spin (read @globals)) (chain int objs int) obj)
               (lambda (chain up frame over)
                 (cond ((null? frame)
                        (loop1 (car chain) (+ up 1)))
                       ((obj-eq? (car frame) name)
                        (ocons (oint up) (oint over)))
                       (else
                        (loop2 chain up (cdr frame) (+ over 1)))))))
      (loop1 (car env) 0))))

(define* assq-macro (subr (maxeff (read @heap) spin) (obj macros) macros)
  (lambda (name l)
    (cond ((null? l) l)
          ((obj-eq? (car (car l)) name) l)
          (else (assq-macro name (cdr l))))))

(define* macro? (subr (maxeff (read @heap) spin) (obj env) bool)
  (lambda (name env)
    (not (null? (assq-macro name (cdr env))))))

(define* push-macro (subr (maxeff (read @heap) (alloc @heap)) (obj obj env) env)
  (lambda (name proc env)
    (cons (car env) (cons (cons name proc) (cdr env)))))

(define* lookup-macro (subr (maxeff (read @heap) spin) (obj env) obj)
  (lambda (name env)
    (cdr (car (assq-macro name (cdr env))))))

; - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -

(define* memq-keyword (subr (maxeff (read @heap) spin) (obj objs) bool)
  (lambda (x l) (if (null? l) #f (if (obj-eq? (car l) x) #t (memq-keyword x (cdr l))))))

(define* variable (subr (maxeff (read @heap) spin) (obj) obj)
  (lambda (x)
    (begin
      (if (not (is-symbol? x))
        (scheme-error "Identifier expected" x)
        obj-null)
      (if (memq-keyword x scheme-syntactic-keywords)
        (scheme-error "Variable name can not be a syntactic keyword" x)
        obj-null))))

(define* shape (subr (maxeff (read @heap) spin) (obj int) obj)
  (lambda (form n)
    (letrec ((loop (subr (maxeff (read @heap) spin (read @globals)) (obj int obj) obj)
               (lambda (form n l)
                 (cond ((<= n 0) obj-true)
                       ((is-pair? l)
                        (loop form (- n 1) (obj-cdr l)))
                       (else
                        (scheme-error "Ill-constructed form" form))))))
      (loop form n form))))

;------------------------------------------------------------------------------
;; Calling an interpreted procedure.

(define* not-procedure (subr (read @heap) (obj) obj)
  (lambda (f) (scheme-error "not a procedure" f)))

(define* call0 (subr ev (obj) obj)
  (lambda (f) (tagcase f (oproc (p) (p 0 obj-null obj-null obj-null obj-null)) (else x (not-procedure f)))))
(define* call1 (subr ev (obj obj) obj)
  (lambda (f a) (tagcase f (oproc (p) (p 1 a obj-null obj-null obj-null)) (else x (not-procedure f)))))
(define* call2 (subr ev (obj obj obj) obj)
  (lambda (f a b) (tagcase f (oproc (p) (p 2 a b obj-null obj-null)) (else x (not-procedure f)))))
(define* call3 (subr ev (obj obj obj obj) obj)
  (lambda (f a b c) (tagcase f (oproc (p) (p 3 a b c obj-null)) (else x (not-procedure f)))))

(define* obj-apply (subr ev (obj obj) obj)
  (lambda (f l)
    (tagcase f
      (oproc (p)
        (let ((n (obj-length l)))
          (cond ((= n 0) (p 0 obj-null obj-null obj-null obj-null))
                ((= n 1) (p 1 (obj-car l) obj-null obj-null obj-null))
                ((= n 2) (p 2 (obj-car l) (obj-cadr l) obj-null obj-null))
                (else (p n (obj-car l) (obj-cadr l) (obj-caddr l) (obj-cdddr l))))))
      (else x (not-procedure f)))))

;; The arguments of a call, from the first, the second or the third, as the
;; list a rest parameter gets.
(define* args-from-1 (subr (alloc @heap) (int obj obj obj obj) obj)
  (lambda (n a b c d)
    (cond ((= n 0) obj-null)
          ((= n 1) (ocons a obj-null))
          ((= n 2) (ocons a (ocons b obj-null)))
          (else (ocons a (ocons b (ocons c d)))))))
(define* args-from-2 (subr (alloc @heap) (int obj obj obj) obj)
  (lambda (n b c d)
    (cond ((= n 1) obj-null)
          ((= n 2) (ocons b obj-null))
          (else (ocons b (ocons c d))))))
(define* args-from-3 (subr (alloc @heap) (int obj obj) obj)
  (lambda (n c d)
    (if (= n 2) obj-null (ocons c d))))

(define* arity-error (subr (read @heap) (int) obj)
  (lambda (n) (scheme-error "wrong number of arguments" (oint n))))

;------------------------------------------------------------------------------

(define scheme-global-variables (ref (listof cell @heap) @heap) (new nil))

(define* scheme-global-var (subr (maxeff (read @heap) (write @heap) (alloc @heap) spin) (obj) cell)
  (lambda (name)
    (letrec ((assq (subr (maxeff (read @heap) spin (read @globals)) ((listof cell @heap)) (listof cell @heap))
               (lambda (l) (cond ((null? l) l) ((obj-eq? (car (car l)) name) l) (else (assq (cdr l)))))))
      (let ((x (assq (get scheme-global-variables))))
        (if (not (null? x))
          (car x)
          (let ((y (the cell (cons name obj-null))))
            (begin
              (set scheme-global-variables (cons y (get scheme-global-variables)))
              y)))))))

(define* scheme-global-var-ref (subr (read @heap) (cell) obj)
  (lambda (i) (cdr i)))

(define* scheme-global-var-set! (subr (write @heap) (cell obj) obj)
  (lambda (i val)
    (begin (set-cdr! i val) obj-null)))

;------------------------------------------------------------------------------

(define* gen-slot-ref-0 (subr pure (int) code)
  (lambda (i)
    (cond ((= i 0) (lambda (rte) (vec-ref rte 0)))
          ((= i 1) (lambda (rte) (vec-ref rte 1)))
          ((= i 2) (lambda (rte) (vec-ref rte 2)))
          ((= i 3) (lambda (rte) (vec-ref rte 3)))
          (else (lambda (rte) (vec-ref rte i))))))

(define* gen-slot-ref-1 (subr pure (int) code)
  (lambda (i)
    (cond ((= i 0) (lambda (rte) (vec-ref (vec-ref rte 0) 0)))
          ((= i 1) (lambda (rte) (vec-ref (vec-ref rte 0) 1)))
          ((= i 2) (lambda (rte) (vec-ref (vec-ref rte 0) 2)))
          ((= i 3) (lambda (rte) (vec-ref (vec-ref rte 0) 3)))
          (else (lambda (rte) (vec-ref (vec-ref rte 0) i))))))

(define* gen-slot-ref-up-2 (subr pure (code) code)
  (lambda (code)
    (lambda (rte) (code (vec-ref (vec-ref rte 0) 0)))))

(define* gen-rte-ref (subr spin (int int) code)
  (lambda (up over)
    (cond ((= up 0) (gen-slot-ref-0 over))
          ((= up 1) (gen-slot-ref-1 over))
          (else (gen-slot-ref-up-2 (gen-rte-ref (- up 2) over))))))

(define* gen-glo-ref (subr pure (cell) code)
  (lambda (i)
    (lambda (rte) (scheme-global-var-ref i))))

(define* gen-var-ref (subr (maxeff (read @heap) (write @heap) (alloc @heap) spin) (obj) code)
  (lambda (var)
    (if (is-pair? var)
      (gen-rte-ref (obj-int (obj-car var)) (obj-int (obj-cdr var)))
      (gen-glo-ref (scheme-global-var var)))))

; - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -

(define* gen-cst (subr pure (obj) code)
  (lambda (val)
    (tagcase val
      (onull () (lambda (rte) obj-null))
      (obool (b) (if b (lambda (rte) obj-true) (lambda (rte) obj-false)))
      (oint (n)
        (cond ((= n -2) (lambda (rte) obj-m2))
              ((= n -1) (lambda (rte) obj-m1))
              ((= n 0) (lambda (rte) obj-0))
              ((= n 1) (lambda (rte) obj-1))
              ((= n 2) (lambda (rte) obj-2))
              (else (lambda (rte) val))))
      (else x (lambda (rte) val)))))

; - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -

(define* gen-append-form (subr pure (code code) code)
  (lambda (code1 code2)
    (lambda (rte) (obj-append (code1 rte) (code2 rte)))))

(define* gen-cons-form (subr pure (code code) code)
  (lambda (code1 code2)
    (lambda (rte) (ocons (code1 rte) (code2 rte)))))

(define* gen-vector-form (subr pure (code) code)
  (lambda (code)
    (lambda (rte) (lst->vector (code rte)))))

; - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -

(define* gen-slot-set-0 (subr pure (int code) code)
  (lambda (i code)
    (cond ((= i 0) (lambda (rte) (vec-set! rte 0 (code rte))))
          ((= i 1) (lambda (rte) (vec-set! rte 1 (code rte))))
          ((= i 2) (lambda (rte) (vec-set! rte 2 (code rte))))
          ((= i 3) (lambda (rte) (vec-set! rte 3 (code rte))))
          (else (lambda (rte) (vec-set! rte i (code rte)))))))

(define* gen-slot-set-1 (subr pure (int code) code)
  (lambda (i code)
    (cond ((= i 0) (lambda (rte) (vec-set! (vec-ref rte 0) 0 (code rte))))
          ((= i 1) (lambda (rte) (vec-set! (vec-ref rte 0) 1 (code rte))))
          ((= i 2) (lambda (rte) (vec-set! (vec-ref rte 0) 2 (code rte))))
          ((= i 3) (lambda (rte) (vec-set! (vec-ref rte 0) 3 (code rte))))
          (else (lambda (rte) (vec-set! (vec-ref rte 0) i (code rte)))))))

(define* gen-slot-set-n (subr pure (code int code) code)
  (lambda (up i code)
    (cond ((= i 0) (lambda (rte) (vec-set! (up (vec-ref rte 0)) 0 (code rte))))
          ((= i 1) (lambda (rte) (vec-set! (up (vec-ref rte 0)) 1 (code rte))))
          ((= i 2) (lambda (rte) (vec-set! (up (vec-ref rte 0)) 2 (code rte))))
          ((= i 3) (lambda (rte) (vec-set! (up (vec-ref rte 0)) 3 (code rte))))
          (else (lambda (rte) (vec-set! (up (vec-ref rte 0)) i (code rte)))))))

(define* gen-rte-set (subr spin (int int code) code)
  (lambda (up over code)
    (cond ((= up 0) (gen-slot-set-0 over code))
          ((= up 1) (gen-slot-set-1 over code))
          (else (gen-slot-set-n (gen-rte-ref (- up 2) 0) over code)))))

(define* gen-glo-set (subr pure (cell code) code)
  (lambda (i code)
    (lambda (rte) (scheme-global-var-set! i (code rte)))))

(define* gen-var-set (subr (maxeff (read @heap) (write @heap) (alloc @heap) spin) (obj code) code)
  (lambda (var code)
    (if (is-pair? var)
      (gen-rte-set (obj-int (obj-car var)) (obj-int (obj-cdr var)) code)
      (gen-glo-set (scheme-global-var var) code))))

; - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -

(define* gen-lambda-1-rest (subr pure (code) code)
  (lambda (body)
    (lambda (rte)
      (oproc (lambda (n a b c d)
               (body (vector2 rte (args-from-1 n a b c d))))))))

(define* gen-lambda-2-rest (subr pure (code) code)
  (lambda (body)
    (lambda (rte)
      (oproc (lambda (n a b c d)
               (if (< n 1)
                 (arity-error n)
                 (body (vector3 rte a (args-from-2 n b c d)))))))))

(define* gen-lambda-3-rest (subr pure (code) code)
  (lambda (body)
    (lambda (rte)
      (oproc (lambda (n a b c d)
               (if (< n 2)
                 (arity-error n)
                 (body (vector4 rte a b (args-from-3 n c d)))))))))

(define* gen-lambda-n-rest (subr pure (int code) code)
  (lambda (nb-vars body)
    (lambda (rte)
      (oproc (lambda (n a b c d)
               (if (< n 3)
                 (arity-error n)
                 (let ((x (make-vec (+ nb-vars 1) obj-false)))
                   (letrec ((loop (subr ev (int obj int obj) obj)
                              (lambda (n x i l)
                                (if (< i n)
                                  (begin (vec-set! x i (obj-car l)) (loop n x (+ i 1) (obj-cdr l)))
                                  (vec-set! x i l)))))
                     (begin
                       (vec-set! x 0 rte)
                       (vec-set! x 1 a)
                       (vec-set! x 2 b)
                       (vec-set! x 3 c)
                       (loop nb-vars x 4 d)
                       (body x))))))))))

(define* gen-lambda-rest (subr pure (int code) code)
  (lambda (nb-vars body)
    (cond ((= nb-vars 1) (gen-lambda-1-rest body))
          ((= nb-vars 2) (gen-lambda-2-rest body))
          ((= nb-vars 3) (gen-lambda-3-rest body))
          (else (gen-lambda-n-rest nb-vars body)))))

(define* gen-lambda-0 (subr pure (code) code)
  (lambda (body)
    (lambda (rte)
      (oproc (lambda (n a b c d)
               (if (= n 0) (body rte) (arity-error n)))))))

(define* gen-lambda-1 (subr pure (code) code)
  (lambda (body)
    (lambda (rte)
      (oproc (lambda (n a b c d)
               (if (= n 1) (body (vector2 rte a)) (arity-error n)))))))

(define* gen-lambda-2 (subr pure (code) code)
  (lambda (body)
    (lambda (rte)
      (oproc (lambda (n a b c d)
               (if (= n 2) (body (vector3 rte a b)) (arity-error n)))))))

(define* gen-lambda-3 (subr pure (code) code)
  (lambda (body)
    (lambda (rte)
      (oproc (lambda (n a b c d)
               (if (= n 3) (body (vector4 rte a b c)) (arity-error n)))))))

(define* gen-lambda-n (subr pure (int code) code)
  (lambda (nb-vars body)
    (lambda (rte)
      (oproc (lambda (n a b c d)
               (if (< n 3)
                 (arity-error n)
                 (let ((x (make-vec (+ nb-vars 1) obj-false)))
                   (letrec ((loop (subr ev (int obj int obj) obj)
                              (lambda (n x i l)
                                (if (<= i n)
                                  (begin (vec-set! x i (obj-car l)) (loop n x (+ i 1) (obj-cdr l)))
                                  obj-null))))
                     (begin
                       (vec-set! x 0 rte)
                       (vec-set! x 1 a)
                       (vec-set! x 2 b)
                       (vec-set! x 3 c)
                       (loop nb-vars x 4 d)
                       (body x))))))))))

(define* gen-lambda (subr pure (int code) code)
  (lambda (nb-vars body)
    (cond ((= nb-vars 0) (gen-lambda-0 body))
          ((= nb-vars 1) (gen-lambda-1 body))
          ((= nb-vars 2) (gen-lambda-2 body))
          ((= nb-vars 3) (gen-lambda-3 body))
          (else (gen-lambda-n nb-vars body)))))

; - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -

(define* gen-sequence (subr pure (code code) code)
  (lambda (code1 code2)
    (lambda (rte) (begin (code1 rte) (code2 rte)))))

; - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -

(define* gen-when (subr pure (code code) code)
  (lambda (code1 code2)
    (lambda (rte)
      (if (true? (code1 rte))
        (code2 rte)
        obj-null))))

(define* gen-if (subr pure (code code code) code)
  (lambda (code1 code2 code3)
    (lambda (rte)
      (if (true? (code1 rte))
        (code2 rte)
        (code3 rte)))))

; - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -

(define* gen-cond-send (subr pure (code code code) code)
  (lambda (code1 code2 code3)
    (lambda (rte)
      (let ((temp (code1 rte)))
        (if (true? temp)
          (call1 (code2 rte) temp)
          (code3 rte))))))

; - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -

(define* gen-and (subr pure (code code) code)
  (lambda (code1 code2)
    (lambda (rte)
      (let ((temp (code1 rte)))
        (if (true? temp)
          (code2 rte)
          temp)))))

; - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -

(define* gen-or (subr pure (code code) code)
  (lambda (code1 code2)
    (lambda (rte)
      (let ((temp (code1 rte)))
        (if (true? temp)
          temp
          (code2 rte))))))

; - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -

(define* gen-case (subr pure (code case-code) code)
  (lambda (code1 code2)
    (lambda (rte) (code2 rte (code1 rte)))))

(define* gen-case-clause (subr pure (obj code case-code) case-code)
  (lambda (datums code1 code2)
    (lambda (rte key) (if (obj-memv key datums) (code1 rte) (code2 rte key)))))

(define* gen-case-else (subr pure (code) case-code)
  (lambda (code)
    (lambda (rte key) (code rte))))

; - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -

(define* gen-letrec-1 (subr pure (code code) code)
  (lambda (val1 body)
    (lambda (rte)
      (let ((x (vector2 rte obj-false)))
        (begin
          (vec-set! x 1 (val1 x))
          (body x))))))

(define* gen-letrec-2 (subr pure (code code code) code)
  (lambda (val1 val2 body)
    (lambda (rte)
      (let ((x (vector3 rte obj-false obj-false)))
        (begin
          (vec-set! x 1 (val1 x))
          (vec-set! x 2 (val2 x))
          (body x))))))

(define* gen-letrec-3 (subr pure (code code code code) code)
  (lambda (val1 val2 val3 body)
    (lambda (rte)
      (let ((x (vector4 rte obj-false obj-false obj-false)))
        (begin
          (vec-set! x 1 (val1 x))
          (vec-set! x 2 (val2 x))
          (vec-set! x 3 (val3 x))
          (body x))))))

(define* gen-letrec-n (subr pure (int codes code) code)
  (lambda (nb-vals vals body)
    (lambda (rte)
      (let ((x (make-vec (+ nb-vals 1) obj-false)))
        (letrec ((loop (subr ev (obj int codes) obj)
                   (lambda (x i l)
                     (if (not (null? l))
                       (begin (vec-set! x i ((car l) x)) (loop x (+ i 1) (cdr l)))
                       obj-null))))
          (begin
            (vec-set! x 0 rte)
            (loop x 1 vals)
            (body x)))))))

(define* gen-letrec (subr (maxeff (read @heap) spin) (codes code) code)
  (lambda (vals body)
    (let ((nb-vals (codes-length vals)))
      (cond ((= nb-vals 1) (gen-letrec-1 (car vals) body))
            ((= nb-vals 2) (gen-letrec-2 (car vals) (car (cdr vals)) body))
            ((= nb-vals 3) (gen-letrec-3 (car vals) (car (cdr vals)) (car (cdr (cdr vals))) body))
            (else (gen-letrec-n nb-vals vals body))))))

; - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -

(define scheme-global-environment env
  (cons (the chain no-pair)    ; environment chain
        (the macros nil))) ; macros

(define* scheme-add-macro (subr (maxeff (read @heap) (write @heap) (alloc @heap)) (obj obj) obj)
  (lambda (name proc)
    (begin
      (set-cdr! scheme-global-environment
        (cons (cons name proc) (cdr scheme-global-environment)))
      name)))

(define* gen-macro (subr pure (obj obj) code)
  (lambda (name proc)
    (lambda (rte) (scheme-add-macro name proc))))

; - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -

(define* gen-combination-0 (subr pure (code) code)
  (lambda (oper)
    (lambda (rte) (call0 (oper rte)))))

(define* gen-combination-1 (subr pure (code code) code)
  (lambda (oper arg1)
    (lambda (rte) (call1 (oper rte) (arg1 rte)))))

(define* gen-combination-2 (subr pure (code code code) code)
  (lambda (oper arg1 arg2)
    (lambda (rte) (call2 (oper rte) (arg1 rte) (arg2 rte)))))

(define* gen-combination-3 (subr pure (code code code code) code)
  (lambda (oper arg1 arg2 arg3)
    (lambda (rte) (call3 (oper rte) (arg1 rte) (arg2 rte) (arg3 rte)))))

(define* gen-combination-n (subr pure (code codes) code)
  (lambda (oper args)
    (lambda (rte)
      (letrec ((evaluate (subr ev (codes obj) obj)
                 (lambda (l rte)
                   (if (not (null? l))
                     (ocons ((car l) rte) (evaluate (cdr l) rte))
                     obj-null))))
        (obj-apply (oper rte) (evaluate args rte))))))

(define* gen-combination (subr (maxeff (read @heap) spin) (code codes) code)
  (lambda (oper args)
    (let ((n (codes-length args)))
      (cond ((= n 0) (gen-combination-0 oper))
            ((= n 1) (gen-combination-1 oper (car args)))
            ((= n 2) (gen-combination-2 oper (car args) (car (cdr args))))
            ((= n 3) (gen-combination-3 oper (car args) (car (cdr args)) (car (cdr (cdr args)))))
            (else (gen-combination-n oper args))))))

;------------------------------------------------------------------------------
;; The compiler: its procedures call each other, so they are one group.

(define* unquote-splicing? (subr (read @heap) (obj) bool)
  (lambda (x)
    (if (is-pair? x)
      (if (is-sym? (obj-car x) 'unquote-splicing) #t #f)
      #f)))

(define* parms->frame (subr (maxeff (read @heap) (alloc @heap) spin) (obj) objs)
  (lambda (parms)
    (cond ((is-null? parms)
           nil)
          ((is-pair? parms)
           (let ((x (obj-car parms)))
             (begin
               (variable x)
               (cons x (parms->frame (obj-cdr parms))))))
          (else
           (begin
             (variable parms)
             (cons parms nil))))))

(define* rest-param? (subr (maxeff (read @heap) spin) (obj) bool)
  (lambda (parms)
    (cond ((is-pair? parms)
           (rest-param? (obj-cdr parms)))
          ((is-null? parms)
           #f)
          (else
           #t))))

(define* definition-name (subr (maxeff (read @heap) spin) (obj) obj)
  (lambda (expr)
    (begin
      (shape expr 3)
      (let ((pattern (obj-cadr expr)))
        (let ((name (if (is-pair? pattern) (obj-car pattern) pattern)))
          (begin
            (if (not (is-symbol? name))
              (scheme-error "Identifier expected" name)
              obj-null)
            name))))))

(define* definition-value (subr (maxeff (read @heap) (alloc @heap)) (obj) obj)
  (lambda (expr)
    (let ((pattern (obj-cadr expr)))
      (if (is-pair? pattern)
        (ocons s-lambda (ocons (obj-cdr pattern) (obj-cddr expr)))
        (obj-caddr expr)))))

(define* bindings->vars (subr (maxeff (read @heap) (alloc @heap) spin) (obj) objs)
  (lambda (bindings)
    (if (is-pair? bindings)
      (let ((binding (obj-car bindings)))
        (begin
          (shape binding 2)
          (let ((x (obj-car binding)))
            (begin
              (variable x)
              (cons x (bindings->vars (obj-cdr bindings)))))))
      nil)))

(define* bindings->vals (subr (maxeff (read @heap) (alloc @heap) spin) (obj) objs)
  (lambda (bindings)
    (if (is-pair? bindings)
      (let ((binding (obj-car bindings)))
        (cons (obj-cadr binding) (bindings->vals (obj-cdr bindings))))
      nil)))

(define* bindings->steps (subr (maxeff (read @heap) (alloc @heap) spin) (obj) objs)
  (lambda (bindings)
    (if (is-pair? bindings)
      (let ((binding (obj-car bindings)))
        (cons (if (is-pair? (obj-cddr binding)) (obj-caddr binding) (obj-car binding))
              (bindings->steps (obj-cdr bindings))))
      nil)))

;; The host lists of expressions these make are the interpreter's own:
;; `(bindings->vars y)` goes into a form as an interpreted list.
(define* objs->obj (subr (maxeff (read @heap) (alloc @heap) spin) (objs) obj)
  (lambda (l) (if (null? l) obj-null (ocons (car l) (objs->obj (cdr l))))))

(define-rec
  (scheme-eval (subr ev (obj) obj)
    (lambda (expr)
      (let ((code (scheme-comp expr scheme-global-environment)))
        (code obj-false))))

  (macro-expand (subr ev (obj env) obj)
    (lambda (expr env)
      (obj-apply (lookup-macro (obj-car expr) env) (obj-cdr expr))))

  (comp-var (subr ev (obj env) code)
    (lambda (expr env)
      (begin
        (variable expr)
        (gen-var-ref (lookup-var expr env)))))

  (comp-self-eval (subr ev (obj env) code)
    (lambda (expr env)
      (gen-cst expr)))

  (comp-quote (subr ev (obj env) code)
    (lambda (expr env)
      (begin
        (shape expr 2)
        (gen-cst (obj-cadr expr)))))

  (comp-quasiquote (subr ev (obj env) code)
    (lambda (expr env)
      (comp-quasiquotation (obj-cadr expr) 1 env)))

  (comp-quasiquotation (subr ev (obj int env) code)
    (lambda (form level env)
      (cond ((= level 0)
             (scheme-comp form env))
            ((is-pair? form)
             (cond
               ((is-sym? (obj-car form) 'quasiquote)
                (comp-quasiquotation-list form (+ level 1) env))
               ((is-sym? (obj-car form) 'unquote)
                (if (= level 1)
                  (scheme-comp (obj-cadr form) env)
                  (comp-quasiquotation-list form (- level 1) env)))
               ((is-sym? (obj-car form) 'unquote-splicing)
                (begin
                  (if (= level 1)
                    (scheme-error "Ill-placed 'unquote-splicing'" form)
                    obj-null)
                  (comp-quasiquotation-list form (- level 1) env)))
               (else
                (comp-quasiquotation-list form level env))))
            ((is-vector? form)
             (gen-vector-form
               (comp-quasiquotation-list (vector->lst form) level env)))
            (else
             (gen-cst form)))))

  (comp-quasiquotation-list (subr ev (obj int env) code)
    (lambda (l level env)
      (if (is-pair? l)
        (let ((first (obj-car l)))
          (if (= level 1)
            (if (unquote-splicing? first)
              (begin
                (shape first 2)
                (gen-append-form (scheme-comp (obj-cadr first) env)
                                 (comp-quasiquotation (obj-cdr l) 1 env)))
              (gen-cons-form (comp-quasiquotation first level env)
                             (comp-quasiquotation (obj-cdr l) level env)))
            (gen-cons-form (comp-quasiquotation first level env)
                           (comp-quasiquotation (obj-cdr l) level env))))
        (comp-quasiquotation l level env))))

  (comp-unquote (subr ev (obj env) code)
    (lambda (expr env)
      (let ((x (scheme-error "Ill-placed 'unquote'" expr))) (gen-cst x))))

  (comp-unquote-splicing (subr ev (obj env) code)
    (lambda (expr env)
      (let ((x (scheme-error "Ill-placed 'unquote-splicing'" expr))) (gen-cst x))))

  (comp-set! (subr ev (obj env) code)
    (lambda (expr env)
      (begin
        (shape expr 3)
        (variable (obj-cadr expr))
        (gen-var-set (lookup-var (obj-cadr expr) env) (scheme-comp (obj-caddr expr) env)))))

  (comp-lambda (subr ev (obj env) code)
    (lambda (expr env)
      (begin
        (shape expr 3)
        (let ((parms (obj-cadr expr)))
          (let ((frame (parms->frame parms)))
            (let ((nb-vars (frame-length frame))
                  (code (comp-body (obj-cddr expr) (push-frame frame env))))
              (if (rest-param? parms)
                (gen-lambda-rest nb-vars code)
                (gen-lambda nb-vars code))))))))

  (comp-body (subr ev (obj env) code)
    (lambda (body env)
      (letrec ((letrec-defines (subr ev (objs objs obj env) code)
                 (lambda (vars vals body env)
                   (if (is-pair? body)

                     (let ((expr (obj-car body)))
                       (cond ((not (is-pair? expr))
                              (letrec-defines* vars vals body env))
                             ((macro? (obj-car expr) env)
                              (letrec-defines vars
                                              vals
                                              (ocons (macro-expand expr env) (obj-cdr body))
                                              env))
                             (else
                              (cond
                                ((is-sym? (obj-car expr) 'begin)
                                 (letrec-defines vars
                                                 vals
                                                 (obj-append (obj-cdr expr) (obj-cdr body))
                                                 env))
                                ((is-sym? (obj-car expr) 'define)
                                 (let ((x (definition-name expr)))
                                   (begin
                                     (variable x)
                                     (letrec-defines (cons x vars)
                                                     (cons (definition-value expr) vals)
                                                     (obj-cdr body)
                                                     env))))
                                ((is-sym? (obj-car expr) 'define-macro)
                                 (let ((x (definition-name expr)))
                                   (letrec-defines vars
                                                   vals
                                                   (obj-cdr body)
                                                   (push-macro
                                                     x
                                                     (scheme-eval (definition-value expr))
                                                     env))))
                                (else
                                 (letrec-defines* vars vals body env))))))

                     (let ((x (scheme-error "Body must contain at least one evaluable expression" body)))
                       (gen-cst x)))))

               (letrec-defines* (subr ev (objs objs obj env) code)
                 (lambda (vars vals body env)
                   (if (null? vars)
                     (comp-sequence body env)
                     (comp-letrec-aux vars vals body env)))))

        (letrec-defines nil nil body env))))

  (comp-if (subr ev (obj env) code)
    (lambda (expr env)
      (begin
        (shape expr 3)
        (let ((code1 (scheme-comp (obj-cadr expr) env))
              (code2 (scheme-comp (obj-caddr expr) env)))
          (if (is-pair? (obj-cdddr expr))
            (gen-if code1 code2 (scheme-comp (obj-cadddr expr) env))
            (gen-when code1 code2))))))

  (comp-cond (subr ev (obj env) code)
    (lambda (expr env)
      (comp-cond-aux (obj-cdr expr) env)))

  (comp-cond-aux (subr ev (obj env) code)
    (lambda (clauses env)
      (if (is-pair? clauses)
        (let ((clause (obj-car clauses)))
          (begin
            (shape clause 1)
            (cond ((is-sym? (obj-car clause) 'else)
                   (begin
                     (shape clause 2)
                     (comp-sequence (obj-cdr clause) env)))
                  ((not (is-pair? (obj-cdr clause)))
                   (gen-or (scheme-comp (obj-car clause) env)
                           (comp-cond-aux (obj-cdr clauses) env)))
                  ((is-sym? (obj-cadr clause) '=>)
                   (begin
                     (shape clause 3)
                     (gen-cond-send (scheme-comp (obj-car clause) env)
                                    (scheme-comp (obj-caddr clause) env)
                                    (comp-cond-aux (obj-cdr clauses) env))))
                  (else
                   (gen-if (scheme-comp (obj-car clause) env)
                           (comp-sequence (obj-cdr clause) env)
                           (comp-cond-aux (obj-cdr clauses) env))))))
        (gen-cst obj-null))))

  (comp-and (subr ev (obj env) code)
    (lambda (expr env)
      (let ((rest (obj-cdr expr)))
        (if (is-pair? rest) (comp-and-aux rest env) (gen-cst obj-true)))))

  (comp-and-aux (subr ev (obj env) code)
    (lambda (l env)
      (let ((code (scheme-comp (obj-car l) env))
            (rest (obj-cdr l)))
        (if (is-pair? rest) (gen-and code (comp-and-aux rest env)) code))))

  (comp-or (subr ev (obj env) code)
    (lambda (expr env)
      (let ((rest (obj-cdr expr)))
        (if (is-pair? rest) (comp-or-aux rest env) (gen-cst obj-false)))))

  (comp-or-aux (subr ev (obj env) code)
    (lambda (l env)
      (let ((code (scheme-comp (obj-car l) env))
            (rest (obj-cdr l)))
        (if (is-pair? rest) (gen-or code (comp-or-aux rest env)) code))))

  (comp-case (subr ev (obj env) code)
    (lambda (expr env)
      (begin
        (shape expr 3)
        (gen-case (scheme-comp (obj-cadr expr) env)
                  (comp-case-aux (obj-cddr expr) env)))))

  (comp-case-aux (subr ev (obj env) case-code)
    (lambda (clauses env)
      (if (is-pair? clauses)
        (let ((clause (obj-car clauses)))
          (begin
            (shape clause 2)
            (if (is-sym? (obj-car clause) 'else)
              (gen-case-else (comp-sequence (obj-cdr clause) env))
              (gen-case-clause (obj-car clause)
                               (comp-sequence (obj-cdr clause) env)
                               (comp-case-aux (obj-cdr clauses) env)))))
        (gen-case-else (gen-cst obj-null)))))

  (comp-let (subr ev (obj env) code)
    (lambda (expr env)
      (begin
        (shape expr 3)
        (let ((x (obj-cadr expr)))
          (cond ((is-symbol? x)
                 (begin
                   (shape expr 4)
                   (let ((y (obj-caddr expr)))
                     (let ((proc (ocons s-lambda (ocons (objs->obj (bindings->vars y)) (obj-cdddr expr)))))
                       (scheme-comp (ocons (olist3 s-letrec (olist1 (olist2 x proc)) x)
                                           (objs->obj (bindings->vals y)))
                                    env)))))
                ((is-pair? x)
                 (scheme-comp (ocons (ocons s-lambda (ocons (objs->obj (bindings->vars x)) (obj-cddr expr)))
                                     (objs->obj (bindings->vals x)))
                              env))
                (else
                 (comp-body (obj-cddr expr) env)))))))

  (comp-let* (subr ev (obj env) code)
    (lambda (expr env)
      (begin
        (shape expr 3)
        (let ((bindings (obj-cadr expr)))
          (if (is-pair? bindings)
            (scheme-comp (olist3 s-let
                                 (olist1 (obj-car bindings))
                                 (ocons s-let* (ocons (obj-cdr bindings) (obj-cddr expr))))
                         env)
            (comp-body (obj-cddr expr) env))))))

  (comp-letrec (subr ev (obj env) code)
    (lambda (expr env)
      (begin
        (shape expr 3)
        (let ((bindings (obj-cadr expr)))
          (comp-letrec-aux (bindings->vars bindings)
                           (bindings->vals bindings)
                           (obj-cddr expr)
                           env)))))

  (comp-letrec-aux (subr ev (objs objs obj env) code)
    (lambda (vars vals body env)
      (if (not (null? vars))
        (let ((new-env (push-frame vars env)))
          (gen-letrec (comp-vals vals new-env)
                      (comp-body body new-env)))
        (comp-body body env))))

  (comp-vals (subr ev (objs env) codes)
    (lambda (l env)
      (if (not (null? l))
        (cons (scheme-comp (car l) env) (comp-vals (cdr l) env))
        nil)))

  (comp-begin (subr ev (obj env) code)
    (lambda (expr env)
      (begin
        (shape expr 2)
        (comp-sequence (obj-cdr expr) env))))

  (comp-sequence (subr ev (obj env) code)
    (lambda (exprs env)
      (if (is-pair? exprs)
        (comp-sequence-aux exprs env)
        (gen-cst obj-null))))

  (comp-sequence-aux (subr ev (obj env) code)
    (lambda (exprs env)
      (let ((code (scheme-comp (obj-car exprs) env))
            (rest (obj-cdr exprs)))
        (if (is-pair? rest) (gen-sequence code (comp-sequence-aux rest env)) code))))

  (comp-do (subr ev (obj env) code)
    (lambda (expr env)
      (begin
        (shape expr 3)
        (let ((bindings (obj-cadr expr))
              (exit (obj-caddr expr)))
          (begin
            (shape exit 1)
            (let* ((vars (bindings->vars bindings))
                   (new-env1 (push-frame (cons obj-false nil) env))
                   (new-env2 (push-frame vars new-env1)))
              (gen-letrec
                (cons
                  (gen-lambda
                    (frame-length vars)
                    (gen-if
                      (scheme-comp (obj-car exit) new-env2)
                      (comp-sequence (obj-cdr exit) new-env2)
                      (gen-sequence
                        (comp-sequence (obj-cdddr expr) new-env2)
                        (gen-combination
                          (gen-var-ref pair-1-1)
                          (comp-vals (bindings->steps bindings) new-env2)))))
                  nil)
                (gen-combination
                  (gen-var-ref pair-0-1)
                  (comp-vals (bindings->vals bindings) new-env1)))))))))

  (comp-define (subr ev (obj env) code)
    (lambda (expr env)
      (begin
        (shape expr 3)
        (let ((pattern (obj-cadr expr)))
          (let ((x (if (is-pair? pattern) (obj-car pattern) pattern)))
            (begin
              (variable x)
              (gen-sequence
                (gen-var-set (lookup-var x env)
                             (scheme-comp (if (is-pair? pattern)
                                            (ocons s-lambda (ocons (obj-cdr pattern) (obj-cddr expr)))
                                            (obj-caddr expr))
                                          env))
                (gen-cst x))))))))

  (comp-define-macro (subr ev (obj env) code)
    (lambda (expr env)
      (let ((x (definition-name expr)))
        (gen-macro x (scheme-eval (definition-value expr))))))

  (comp-combination (subr ev (obj env) code)
    (lambda (expr env)
      (gen-combination (scheme-comp (obj-car expr) env) (comp-vals-obj (obj-cdr expr) env))))

  ;; comp-vals, of the interpreted list of a combination's arguments.
  (comp-vals-obj (subr ev (obj env) codes)
    (lambda (l env)
      (if (is-pair? l)
        (cons (scheme-comp (obj-car l) env) (comp-vals-obj (obj-cdr l) env))
        nil)))

  (scheme-comp (subr ev (obj env) code)
    (lambda (expr env)
      (cond ((is-symbol? expr)
             (comp-var expr env))
            ((not (is-pair? expr))
             (comp-self-eval expr env))
            ((macro? (obj-car expr) env)
             (scheme-comp (macro-expand expr env) env))
            (else
             (cond
               ((is-sym? (obj-car expr) 'quote)            (comp-quote expr env))
               ((is-sym? (obj-car expr) 'quasiquote)       (comp-quasiquote expr env))
               ((is-sym? (obj-car expr) 'unquote)          (comp-unquote expr env))
               ((is-sym? (obj-car expr) 'unquote-splicing) (comp-unquote-splicing expr env))
               ((is-sym? (obj-car expr) 'set!)             (comp-set! expr env))
               ((is-sym? (obj-car expr) 'lambda)           (comp-lambda expr env))
               ((is-sym? (obj-car expr) 'if)               (comp-if expr env))
               ((is-sym? (obj-car expr) 'cond)             (comp-cond expr env))
               ((is-sym? (obj-car expr) 'and)              (comp-and expr env))
               ((is-sym? (obj-car expr) 'or)               (comp-or expr env))
               ((is-sym? (obj-car expr) 'case)             (comp-case expr env))
               ((is-sym? (obj-car expr) 'let)              (comp-let expr env))
               ((is-sym? (obj-car expr) 'let*)             (comp-let* expr env))
               ((is-sym? (obj-car expr) 'letrec)           (comp-letrec expr env))
               ((is-sym? (obj-car expr) 'begin)            (comp-begin expr env))
               ((is-sym? (obj-car expr) 'do)               (comp-do expr env))
               ((is-sym? (obj-car expr) 'define)           (comp-define expr env))
               ((is-sym? (obj-car expr) 'define-macro)     (comp-define-macro expr env))
               (else                                       (comp-combination expr env))))))))

; - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
;; The primitives the interpreted program sees.

(define* def-proc (subr (maxeff (read @heap) (write @heap) (alloc @heap) spin) (symbol obj) obj)
  (lambda (name value)
    (scheme-global-var-set!
      (scheme-global-var (osym name))
      value)))

;; A primitive this port cannot give (see the header).
(define* unsupported (subr pure (symbol) obj)
  (lambda (name)
    (oproc (lambda (n a b c d) (scheme-error "not supported in FX-26" (osym name))))))

(define* int-of (subr (read @heap) (obj) int) (lambda (x) (obj-int x)))
(define* char-of (subr (read @heap) (obj) char)
  (lambda (x) (tagcase x (ochar (c) c) (else y (begin (scheme-error "not a character" x) #\space)))))
(define* string-of (subr (read @heap) (obj) string)
  (lambda (x) (tagcase x (ostr (s) s) (else y (begin (scheme-error "not a string" x) "")))))
(define* symbol-of (subr (read @heap) (obj) symbol)
  (lambda (x) (tagcase x (osym (s) s) (else y (begin (scheme-error "not a symbol" x) 'error)))))

(define* obj-equal? (subr (maxeff (read @heap) spin (read @globals)) (obj obj) bool)
  (lambda (x y)
    (tagcase x
      (opair (p) (tagcase y
                   (opair (q) (and (obj-equal? (car p) (car q)) (obj-equal? (cdr p) (cdr q))))
                   (else z #f)))
      (ostr (s) (tagcase y (ostr (t) (string=? s t)) (else z #f)))
      (ovec (v) (tagcase y
                  (ovec (w)
                    (and (= (array-length v) (array-length w))
                         (letrec ((loop (subr (maxeff (read @heap) spin (read @globals)) (int) bool)
                                    (lambda (i) (if (= i (array-length v)) #t
                                                    (and (obj-equal? (array-ref v i) (array-ref w i)) (loop (+ i 1)))))))
                           (loop 0))))
                  (else z #f)))
      (else z (obj-eq? x y)))))

;; A comparison of the characters of two strings: -1, 0 or 1.
(define* string-compare (subr spin (string string (subr pure (char) char)) int)
  (lambda (a b f)
    (let ((la (string-length a)) (lb (string-length b)))
      (letrec ((loop (subr spin (int) int)
                 (lambda (i)
                   (cond ((= i la) (if (= i lb) 0 -1))
                         ((= i lb) 1)
                         (else (let ((x (char->integer (f (string-ref a i))))
                                     (y (char->integer (f (string-ref b i)))))
                                 (cond ((< x y) -1)
                                       ((> x y) 1)
                                       (else (loop (+ i 1))))))))))
        (loop 0)))))
(define char-same (subr pure (char) char) (lambda (c) c))
;; char-downcase as a value: the native compiler takes a primitive only as
;; an operator (see the header).
(define char-down (subr pure (char) char) (lambda (c) (char-downcase c)))

(define* prim-string-compare (subr pure ((subr pure (int) bool) (subr pure (char) char)) obj)
  (lambda (test f)
    (oproc (lambda (n a b c d)
             (if (= n 2) (bool->obj (test (string-compare (string-of a) (string-of b) f))) (arity-error n))))))
(define* prim-char-compare (subr pure ((subr pure (int int) bool) (subr pure (char) char)) obj)
  (lambda (test f)
    (oproc (lambda (n a b c d)
             (if (= n 2)
               (bool->obj (test (char->integer (f (char-of a))) (char->integer (f (char-of b)))))
               (arity-error n))))))

;; c[ad]+r: the path's letters, applied from the right.
(define* cxr (subr pure (string) obj)
  (lambda (path)
    (oproc (lambda (n a b c d)
             (if (= n 1)
               (letrec ((walk (subr ev (int obj) obj)
                          (lambda (i x)
                            (if (< i 0)
                              x
                              (walk (- i 1) (if (char=? (string-ref path i) #\a) (obj-car x) (obj-cdr x)))))))
                 (walk (- (string-length path) 1) a))
               (arity-error n))))))

(define* char-upcase (subr pure (char) char)
  (lambda (c)
    (let ((i (char->integer c)))
      (if (and (>= i 97) (<= i 122)) (integer->char (- i 32)) c))))

(define* obj-reverse (subr (maxeff (read @heap) (alloc @heap) spin) (obj obj) obj)
  (lambda (l acc) (tagcase l (opair (p) (obj-reverse (cdr p) (ocons (car p) acc))) (else y acc))))

(define* obj-list? (subr (maxeff (read @heap) spin) (obj) bool)
  (lambda (l) (tagcase l (onull () #t) (opair (p) (obj-list? (cdr p))) (else y #f))))

(define* mem-by (subr (maxeff (read @heap) spin) ((subr (maxeff (read @heap) spin (read @globals)) (obj obj) bool) obj obj) obj)
  (lambda (same x l)
    (tagcase l
      (opair (p) (if (same x (car p)) l (mem-by same x (cdr p))))
      (else y obj-false))))
(define* ass-by (subr (maxeff (read @heap) spin) ((subr (maxeff (read @heap) spin (read @globals)) (obj obj) bool) obj obj) obj)
  (lambda (same x l)
    (tagcase l
      (opair (p) (if (same x (obj-car (car p))) (car p) (ass-by same x (cdr p))))
      (else y obj-false))))
(define eq-test (subr (maxeff (read @heap) spin (read @globals)) (obj obj) bool) (lambda (x y) (obj-eq? x y)))
(define equal-test (subr (maxeff (read @heap) spin (read @globals)) (obj obj) bool) (lambda (x y) (obj-equal? x y)))

(define* int-fold (subr ev ((subr (maxeff spin (read @globals)) (int int) int) int obj) obj)
  (lambda (f acc l)
    (tagcase l
      (opair (p) (int-fold f (f acc (int-of (car p))) (cdr p)))
      (else y (oint acc)))))
(define* gcd2 (subr spin (int int) int)
  (lambda (a b) (if (= b 0) (if (< a 0) (- 0 a) a) (gcd2 b (modulo a b)))))
(define* expt2 (subr spin (int int) int)
  (lambda (a b) (if (= b 0) 1 (* a (expt2 a (- b 1))))))

(define* obj-map1 (subr ev (obj obj) obj)
  (lambda (f l) (tagcase l (opair (p) (let ((x (call1 f (car p)))) (ocons x (obj-map1 f (cdr p))))) (else y obj-null))))
;; map and for-each over several lists: the cars, and the cdrs, of each.
(define* cars (subr ev (obj) obj)
  (lambda (ls) (tagcase ls (opair (p) (ocons (obj-car (car p)) (cars (cdr p)))) (else y obj-null))))
(define* cdrs (subr ev (obj) obj)
  (lambda (ls) (tagcase ls (opair (p) (ocons (obj-cdr (car p)) (cdrs (cdr p)))) (else y obj-null))))
(define* any-null? (subr (maxeff (read @heap) spin) (obj) bool)
  (lambda (ls) (tagcase ls (opair (p) (if (is-pair? (car p)) (any-null? (cdr p)) #t)) (else y #f))))
(define* obj-map (subr ev (obj obj) obj)
  (lambda (f ls)
    (if (any-null? ls)
      obj-null
      (let ((x (obj-apply f (cars ls)))) (ocons x (obj-map f (cdrs ls)))))))

(define* list-chars (subr (maxeff (read @heap) (alloc @heap) spin) (obj) (listof char @heap))
  (lambda (l) (tagcase l (opair (p) (cons (char-of (car p)) (list-chars (cdr p)))) (else y nil))))
(define* repeat-char (subr (maxeff (alloc @heap) spin) (int char) (listof char @heap))
  (lambda (n c) (if (<= n 0) nil (cons c (repeat-char (- n 1) c)))))
(define* string-append-all (subr (maxeff (read @heap) spin) (string obj) string)
  (lambda (acc l) (tagcase l (opair (p) (string-append-all (string-append acc (string-of (car p))) (cdr p))) (else y acc))))

(define-type prim (subr ev (int obj obj obj obj) obj))
(define* p1 (subr pure ((subr ev (obj) obj)) obj)
  (lambda (f) (oproc (lambda (n a b c d) (if (= n 1) (f a) (arity-error n))))))
(define* p2 (subr pure ((subr ev (obj obj) obj)) obj)
  (lambda (f) (oproc (lambda (n a b c d) (if (= n 2) (f a b) (arity-error n))))))
(define* p3 (subr pure ((subr ev (obj obj obj) obj)) obj)
  (lambda (f) (oproc (lambda (n a b c d) (if (= n 3) (f a b c) (arity-error n))))))
(define* pn (subr pure ((subr ev (obj) obj)) obj)
  (lambda (f) (oproc (lambda (n a b c d) (f (args-from-1 n a b c d))))))

(define* install-primitives (subr ev () unit)
  (lambda ()
    (begin
(def-proc 'not                            (oproc (lambda (n x b c d) (if (= n 1) (bool->obj (not (true? x))) (arity-error n)))))
(def-proc 'boolean?                       (p1 (lambda ((x obj)) (bool->obj (tagcase x (obool (b) #t) (else y #f))))))
(def-proc 'eqv?                           (p2 (lambda ((x obj) (y obj)) (bool->obj (obj-eq? x y)))))
(def-proc 'eq?                            (p2 (lambda ((x obj) (y obj)) (bool->obj (obj-eq? x y)))))
(def-proc 'equal?                         (p2 (lambda ((x obj) (y obj)) (bool->obj (obj-equal? x y)))))
(def-proc 'pair?                          (oproc (lambda (n obj b c d) (if (= n 1) (bool->obj (is-pair? obj)) (arity-error n)))))
(def-proc 'cons                           (oproc (lambda (n x y c d) (if (= n 2) (ocons x y) (arity-error n)))))
(def-proc 'car                            (oproc (lambda (n x b c d) (if (= n 1) (obj-car x) (arity-error n)))))
(def-proc 'cdr                            (oproc (lambda (n x b c d) (if (= n 1) (obj-cdr x) (arity-error n)))))
(def-proc 'set-car!                       (p2 (lambda ((x obj) (y obj)) (tagcase x (opair (p) (begin (set-car! p y) obj-null)) (else z (scheme-error "set-car!: not a pair" x))))))
(def-proc 'set-cdr!                       (p2 (lambda ((x obj) (y obj)) (tagcase x (opair (p) (begin (set-cdr! p y) obj-null)) (else z (scheme-error "set-cdr!: not a pair" x))))))
(def-proc 'caar                           (cxr "aa"))
(def-proc 'cadr                           (cxr "ad"))
(def-proc 'cdar                           (cxr "da"))
(def-proc 'cddr                           (cxr "dd"))
(def-proc 'caaar                          (cxr "aaa"))
(def-proc 'caadr                          (cxr "aad"))
(def-proc 'cadar                          (cxr "ada"))
(def-proc 'caddr                          (cxr "add"))
(def-proc 'cdaar                          (cxr "daa"))
(def-proc 'cdadr                          (cxr "dad"))
(def-proc 'cddar                          (cxr "dda"))
(def-proc 'cdddr                          (cxr "ddd"))
(def-proc 'caaaar                         (cxr "aaaa"))
(def-proc 'caaadr                         (cxr "aaad"))
(def-proc 'caadar                         (cxr "aada"))
(def-proc 'caaddr                         (cxr "aadd"))
(def-proc 'cadaar                         (cxr "adaa"))
(def-proc 'cadadr                         (cxr "adad"))
(def-proc 'caddar                         (cxr "adda"))
(def-proc 'cadddr                         (cxr "addd"))
(def-proc 'cdaaar                         (cxr "daaa"))
(def-proc 'cdaadr                         (cxr "daad"))
(def-proc 'cdadar                         (cxr "dada"))
(def-proc 'cdaddr                         (cxr "dadd"))
(def-proc 'cddaar                         (cxr "ddaa"))
(def-proc 'cddadr                         (cxr "ddad"))
(def-proc 'cdddar                         (cxr "ddda"))
(def-proc 'cddddr                         (cxr "dddd"))
(def-proc 'null?                          (oproc (lambda (n x b c d) (if (= n 1) (bool->obj (is-null? x)) (arity-error n)))))
(def-proc 'list?                          (p1 (lambda ((x obj)) (bool->obj (obj-list? x)))))
(def-proc 'list                           (pn (lambda ((l obj)) l)))
(def-proc 'length                         (p1 (lambda ((l obj)) (oint (obj-length l)))))
(def-proc 'append                         (pn (lambda ((ls obj))
                                                (letrec ((app (subr ev (obj) obj)
                                                           (lambda (ls) (tagcase ls
                                                                          (opair (p) (if (is-null? (cdr p)) (car p) (obj-append (car p) (app (cdr p)))))
                                                                          (else y obj-null)))))
                                                  (app ls)))))
(def-proc 'reverse                        (p1 (lambda ((l obj)) (obj-reverse l obj-null))))
(def-proc 'list-ref                       (p2 (lambda ((l obj) (k obj))
                                                (letrec ((ref (subr ev (obj int) obj)
                                                           (lambda (l k) (if (= k 0) (obj-car l) (ref (obj-cdr l) (- k 1))))))
                                                  (ref l (int-of k))))))
(def-proc 'memq                           (p2 (lambda ((x obj) (l obj)) (mem-by eq-test x l))))
(def-proc 'memv                           (p2 (lambda ((x obj) (l obj)) (mem-by eq-test x l))))
(def-proc 'member                         (p2 (lambda ((x obj) (l obj)) (mem-by equal-test x l))))
(def-proc 'assq                           (p2 (lambda ((x obj) (l obj)) (ass-by eq-test x l))))
(def-proc 'assv                           (p2 (lambda ((x obj) (l obj)) (ass-by eq-test x l))))
(def-proc 'assoc                          (p2 (lambda ((x obj) (l obj)) (ass-by equal-test x l))))
(def-proc 'symbol?                        (p1 (lambda ((x obj)) (bool->obj (is-symbol? x)))))
(def-proc 'symbol->string                 (p1 (lambda ((x obj)) (ostr (symbol->string (symbol-of x))))))
(def-proc 'string->symbol                 (p1 (lambda ((x obj)) (osym (string->symbol (string-of x))))))
(def-proc 'number?                        (p1 (lambda ((x obj)) (bool->obj (tagcase x (oint (i) #t) (else y #f))))))
(def-proc 'complex?                       (p1 (lambda ((x obj)) (bool->obj (tagcase x (oint (i) #t) (else y #f))))))
(def-proc 'real?                          (p1 (lambda ((x obj)) (bool->obj (tagcase x (oint (i) #t) (else y #f))))))
(def-proc 'rational?                      (p1 (lambda ((x obj)) (bool->obj (tagcase x (oint (i) #t) (else y #f))))))
(def-proc 'integer?                       (p1 (lambda ((x obj)) (bool->obj (tagcase x (oint (i) #t) (else y #f))))))
(def-proc 'exact?                         (p1 (lambda ((x obj)) (begin (int-of x) obj-true))))
(def-proc 'inexact?                       (p1 (lambda ((x obj)) (begin (int-of x) obj-false))))
(def-proc 'max                            (oproc (lambda (n a b c d) (if (< n 1) (arity-error n) (int-fold (lambda ((x int) (y int)) (if (> x y) x y)) (int-of a) (args-from-2 n b c d))))))
(def-proc 'min                            (oproc (lambda (n a b c d) (if (< n 1) (arity-error n) (int-fold (lambda ((x int) (y int)) (if (< x y) x y)) (int-of a) (args-from-2 n b c d))))))
(def-proc '/                              (unsupported '/))
(def-proc 'abs                            (p1 (lambda ((x obj)) (let ((i (int-of x))) (if (< i 0) (oint (- 0 i)) x)))))
(def-proc 'gcd                            (pn (lambda ((l obj)) (int-fold (lambda ((x int) (y int)) (gcd2 x y)) 0 l))))
(def-proc 'lcm                            (pn (lambda ((l obj)) (int-fold (lambda ((x int) (y int)) (if (or (= x 0) (= y 0)) 0 (let ((m (quotient (* x y) (gcd2 x y)))) (if (< m 0) (- 0 m) m)))) 1 l))))
(def-proc 'floor                          (p1 (lambda ((x obj)) (begin (int-of x) x))))
(def-proc 'ceiling                        (p1 (lambda ((x obj)) (begin (int-of x) x))))
(def-proc 'truncate                       (p1 (lambda ((x obj)) (begin (int-of x) x))))
(def-proc 'round                          (p1 (lambda ((x obj)) (begin (int-of x) x))))
(def-proc 'exp                            (unsupported 'exp))
(def-proc 'log                            (unsupported 'log))
(def-proc 'sin                            (unsupported 'sin))
(def-proc 'cos                            (unsupported 'cos))
(def-proc 'tan                            (unsupported 'tan))
(def-proc 'asin                           (unsupported 'asin))
(def-proc 'acos                           (unsupported 'acos))
(def-proc 'atan                           (unsupported 'atan))
(def-proc 'sqrt                           (unsupported 'sqrt))
(def-proc 'expt                           (p2 (lambda ((x obj) (y obj)) (oint (expt2 (int-of x) (int-of y))))))
(def-proc 'exact->inexact                 (unsupported 'exact->inexact))
(def-proc 'inexact->exact                 (p1 (lambda ((x obj)) (begin (int-of x) x))))
(def-proc 'number->string                 (p1 (lambda ((x obj)) (ostr (int->string (int-of x))))))
(def-proc 'string->number                 (unsupported 'string->number))
(def-proc 'char?                          (p1 (lambda ((x obj)) (bool->obj (tagcase x (ochar (ch) #t) (else y #f))))))
(def-proc 'char=?                         (prim-char-compare (lambda ((x int) (y int)) (= x y)) char-same))
(def-proc 'char<?                         (prim-char-compare (lambda ((x int) (y int)) (< x y)) char-same))
(def-proc 'char>?                         (prim-char-compare (lambda ((x int) (y int)) (> x y)) char-same))
(def-proc 'char<=?                        (prim-char-compare (lambda ((x int) (y int)) (<= x y)) char-same))
(def-proc 'char>=?                        (prim-char-compare (lambda ((x int) (y int)) (>= x y)) char-same))
(def-proc 'char-ci=?                      (prim-char-compare (lambda ((x int) (y int)) (= x y)) char-down))
(def-proc 'char-ci<?                      (prim-char-compare (lambda ((x int) (y int)) (< x y)) char-down))
(def-proc 'char-ci>?                      (prim-char-compare (lambda ((x int) (y int)) (> x y)) char-down))
(def-proc 'char-ci<=?                     (prim-char-compare (lambda ((x int) (y int)) (<= x y)) char-down))
(def-proc 'char-ci>=?                     (prim-char-compare (lambda ((x int) (y int)) (>= x y)) char-down))
(def-proc 'char-alphabetic?               (p1 (lambda ((x obj)) (bool->obj (char-alphabetic? (char-of x))))))
(def-proc 'char-numeric?                  (p1 (lambda ((x obj)) (bool->obj (char-numeric? (char-of x))))))
(def-proc 'char-whitespace?               (p1 (lambda ((x obj)) (bool->obj (char-whitespace? (char-of x))))))
(def-proc 'char-lower-case?               (p1 (lambda ((x obj)) (let ((ch (char-of x))) (bool->obj (and (char-alphabetic? ch) (not (char=? ch (char-upcase ch)))))))))
(def-proc 'char->integer                  (p1 (lambda ((x obj)) (oint (char->integer (char-of x))))))
(def-proc 'integer->char                  (p1 (lambda ((x obj)) (ochar (integer->char (int-of x))))))
(def-proc 'char-upcase                    (p1 (lambda ((x obj)) (ochar (char-upcase (char-of x))))))
(def-proc 'char-downcase                  (p1 (lambda ((x obj)) (ochar (char-downcase (char-of x))))))
(def-proc 'string?                        (p1 (lambda ((x obj)) (bool->obj (tagcase x (ostr (s) #t) (else y #f))))))
(def-proc 'make-string                    (oproc (lambda (n a b c d)
                                                   (cond ((= n 1) (ostr (list->string (repeat-char (int-of a) #\space))))
                                                         ((= n 2) (ostr (list->string (repeat-char (int-of a) (char-of b)))))
                                                         (else (arity-error n))))))
(def-proc 'string                         (pn (lambda ((l obj)) (ostr (list->string (list-chars l))))))
(def-proc 'string-length                  (p1 (lambda ((x obj)) (oint (string-length (string-of x))))))
(def-proc 'string-ref                     (p2 (lambda ((x obj) (k obj)) (ochar (string-ref (string-of x) (int-of k))))))
(def-proc 'string-set!                    (unsupported 'string-set!))
(def-proc 'string=?                       (prim-string-compare (lambda ((i int)) (= i 0)) char-same))
(def-proc 'string<?                       (prim-string-compare (lambda ((i int)) (< i 0)) char-same))
(def-proc 'string>?                       (prim-string-compare (lambda ((i int)) (> i 0)) char-same))
(def-proc 'string<=?                      (prim-string-compare (lambda ((i int)) (<= i 0)) char-same))
(def-proc 'string>=?                      (prim-string-compare (lambda ((i int)) (>= i 0)) char-same))
(def-proc 'string-ci=?                    (prim-string-compare (lambda ((i int)) (= i 0)) char-down))
(def-proc 'string-ci<?                    (prim-string-compare (lambda ((i int)) (< i 0)) char-down))
(def-proc 'string-ci>?                    (prim-string-compare (lambda ((i int)) (> i 0)) char-down))
(def-proc 'string-ci<=?                   (prim-string-compare (lambda ((i int)) (<= i 0)) char-down))
(def-proc 'string-ci>=?                   (prim-string-compare (lambda ((i int)) (>= i 0)) char-down))
(def-proc 'substring                      (p3 (lambda ((s obj) (i obj) (j obj)) (ostr (substring (string-of s) (int-of i) (int-of j))))))
(def-proc 'string-append                  (pn (lambda ((l obj)) (ostr (string-append-all "" l)))))
(def-proc 'vector?                        (p1 (lambda ((x obj)) (bool->obj (is-vector? x)))))
(def-proc 'make-vector                    (oproc (lambda (n a b c d)
                                                   (cond ((= n 1) (make-vec (int-of a) obj-false))
                                                         ((= n 2) (make-vec (int-of a) b))
                                                         (else (arity-error n))))))
(def-proc 'vector                         (pn (lambda ((l obj)) (lst->vector l))))
(def-proc 'vector-length                  (p1 (lambda ((x obj)) (tagcase x (ovec (v) (oint (array-length v))) (else y (scheme-error "vector-length: not a vector" x))))))
(def-proc 'vector-ref                     (p2 (lambda ((x obj) (k obj)) (vec-ref x (int-of k)))))
(def-proc 'vector-set!                    (p3 (lambda ((x obj) (k obj) (v obj)) (vec-set! x (int-of k) v))))
(def-proc 'procedure?                     (p1 (lambda ((x obj)) (bool->obj (tagcase x (oproc (p) #t) (else y #f))))))
(def-proc 'apply                          (oproc (lambda (n f b c d)
                                                   (cond ((= n 2) (obj-apply f b))
                                                         ((= n 3) (obj-apply f (ocons b c)))
                                                         ((> n 3) (obj-apply f (ocons b (ocons c (let ((r (obj-reverse d obj-null)))
                                                                                             (obj-reverse (obj-cdr r) (obj-car r)))))))
                                                         (else (arity-error n))))))
(def-proc 'map                            (oproc (lambda (n f b c d)
                                                   (cond ((= n 2) (obj-map1 f b))
                                                         ((> n 2) (obj-map f (args-from-2 (- n 1) b c d)))
                                                         (else (arity-error n))))))
(def-proc 'for-each                       (oproc (lambda (n f b c d)
                                                   (if (< n 2)
                                                     (arity-error n)
                                                     (begin (obj-map f (args-from-2 (- n 1) b c d)) obj-null)))))
(def-proc 'call-with-input-file           (unsupported 'call-with-input-file))
(def-proc 'call-with-output-file          (unsupported 'call-with-output-file))
(def-proc 'input-port?                    (unsupported 'input-port?))
(def-proc 'output-port?                   (unsupported 'output-port?))
(def-proc 'current-input-port             (unsupported 'current-input-port))
(def-proc 'current-output-port            (unsupported 'current-output-port))
(def-proc 'open-input-file                (unsupported 'open-input-file))
(def-proc 'open-output-file               (unsupported 'open-output-file))
(def-proc 'close-input-port               (unsupported 'close-input-port))
(def-proc 'close-output-port              (unsupported 'close-output-port))
(def-proc 'eof-object?                    (unsupported 'eof-object?))
(def-proc 'read                           (unsupported 'read))
(def-proc 'read-char                      (unsupported 'read-char))
(def-proc 'peek-char                      (unsupported 'peek-char))
(def-proc 'write                          (unsupported 'write))
(def-proc 'display                        (unsupported 'display))
(def-proc 'newline                        (unsupported 'newline))
(def-proc 'write-char                     (unsupported 'write-char))
      #u)))

(install-primitives)

; - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
;; A reader for the input, Larceny's `(read)`: lists, dotted pairs, quote,
;; strings, integers, booleans, symbols and comments.

(define* read-obj (subr ev (string (ref int @heap)) obj)
  (lambda (s pos)
    (letrec ((peek (subr ev () char)
               (lambda () (if (< (get pos) (string-length s)) (string-ref s (get pos)) #\nul)))
             (advance (subr ev () unit)
               (lambda () (set pos (+ (get pos) 1))))
             (skip (subr ev () unit)
               (lambda ()
                 (let ((c (peek)))
                   (cond ((char=? c #\nul) #u)
                         ((char-whitespace? c) (begin (advance) (skip)))
                         ((char=? c #\;) (begin (skip-line) (skip)))
                         (else #u)))))
             (skip-line (subr ev () unit)
               (lambda ()
                 (let ((c (peek)))
                   (if (or (char=? c #\nul) (char=? c #\newline)) #u (begin (advance) (skip-line))))))
             (delimiter? (subr ev (char) bool)
               (lambda (c) (or (char=? c #\nul) (char-whitespace? c) (char-in? c "()\";'"))))
             (token (subr ev ((listof char @heap)) (listof char @heap))
               (lambda (acc)
                 (if (delimiter? (peek)) (reverse acc) (let ((c (peek))) (begin (advance) (token (cons c acc)))))))
             (string-body (subr ev ((listof char @heap)) string)
               (lambda (acc)
                 (let ((c (peek)))
                   (begin
                     (advance)
                     (cond ((char=? c #\") (list->string (reverse acc)))
                           ((char=? c #\\) (let ((e (peek))) (begin (advance) (string-body (cons e acc)))))
                           (else (string-body (cons c acc))))))))
             (digits? (subr ev ((listof char @heap)) bool)
               (lambda (l) (if (null? l) #t (and (char-numeric? (car l)) (digits? (cdr l))))))
             (atom (subr ev (string) obj)
               (lambda (t)
                 (let ((cs (the (listof char @heap) (string->list t))))
                   (cond ((string=? t "#t") obj-true)
                         ((string=? t "#f") obj-false)
                         ((and (digits? cs) (not (null? cs))) (oint (parse-nat t 10)))
                         ((and (char=? (car cs) #\-) (not (null? (cdr cs))) (digits? (cdr cs)))
                          (oint (- 0 (parse-nat (substring t 1 (string-length t)) 10))))
                         (else (osym (string->symbol t)))))))
             (datum (subr ev () obj)
               (lambda ()
                 (begin
                   (skip)
                   (let ((c (peek)))
                     (cond ((char=? c #\() (begin (advance) (rest-of-list)))
                           ((char=? c #\') (begin (advance) (olist2 (osym 'quote) (datum))))
                           ((char=? c #\") (begin (advance) (ostr (string-body nil))))
                           (else (atom (list->string (token nil)))))))))
             (rest-of-list (subr ev () obj)
               (lambda ()
                 (begin
                   (skip)
                   (let ((c (peek)))
                     (cond ((char=? c #\)) (begin (advance) obj-null))
                           ((and (char=? c #\.) (delimiter? (string-ref s (+ (get pos) 1))))
                            (begin (advance)
                                   (let ((x (datum))) (begin (skip) (advance) x))))
                           (else (let ((x (datum))) (ocons x (rest-of-list))))))))))
      (datum))))

(define* obj->datum (subr (maxeff (read @heap) (alloc @heap) spin) (obj) datum)
  (lambda (x)
    (tagcase x
      (onull () nil)
      (obool (b) b)
      (oint (n) n)
      (ochar (c) c)
      (ostr (s) s)
      (osym (s) (string->symbol (symbol->string s)))
      (opair (p) (cons (obj->datum (car p)) (obj->datum (cdr p))))
      (ovec (v) (letrec ((elts (subr (maxeff (read @heap) (alloc @heap) spin (read @globals)) (int (listof datum @heap)) (listof datum @heap))
                               (lambda (i acc) (if (< i 0) acc (elts (- i 1) (cons (obj->datum (array-ref v i)) acc))))))
                  (datum-list->vector (datum-list (elts (- (array-length v) 1) nil)))))
      (oproc (p) (string->symbol "#<procedure>")))))

;; Larceny's input, as its `(read)` sees it.
(define input-text string "
(let ()

  (define (sort-list obj pred)

    (define (loop l)
      (if (and (pair? l) (pair? (cdr l)))
          (split l '() '())
          l))

    (define (split l one two)
      (if (pair? l)
          (split (cdr l) two (cons (car l) one))
          (merge (loop one) (loop two))))

    (define (merge one two)
      (cond ((null? one) two)
            ((pred (car two) (car one))
             (cons (car two)
                   (merge (cdr two) one)))
            (else
             (cons (car one)
                   (merge (cdr one) two)))))

    (loop obj))

  (sort-list '(\"one\" \"two\" \"three\" \"four\" \"five\" \"six\"
               \"seven\" \"eight\" \"nine\" \"ten\" \"eleven\" \"twelve\"
               \"thirteen\" \"fourteen\" \"fifteen\" \"sixteen\"
               \"seventeen\" \"eighteen\" \"nineteen\" \"twenty\"
               \"twentyone\" \"twentytwo\" \"twentythree\" \"twentyfour\"
               \"twentyfive\" \"twentysix\" \"twentyseven\" \"twentyeight\"
               \"twentynine\" \"thirty\")
             string<?))
")

;; The inputs, where no compiler can fold them (Larceny's `hide`): globals,
;; which a later definition may replace.
(define input1 obj (read-obj input-text (new 0)))
(define iterations int 100000)

(define* run (subr ev (int obj) obj)
  (lambda (i result) (if (= i 0) result (run (- i 1) (scheme-eval input1)))))
(obj->datum (run iterations obj-null))
