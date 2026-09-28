;;; The FX-91 run-time environment.
;;;
;;; `standard.scm` registers these with ADD-RUN-TIME and `top.scm` wraps the
;;; generated code in a `let` over them; here they are ordinary top-level
;;; definitions in the Scheme session the generated code runs in, which is the
;;; same thing with less plumbing. The exact set is listed by
;;; `reference/fx91-runtime.rkt`.
;;;
;;; Anything the reference leaves as a bare fall-through to the host Scheme's
;;; own procedure of the same name — `+`, `car`, `length`, `string-length`, the
;;; comparisons — is deliberately *absent* here, so it falls through the same
;;; way. That includes int `/`, which the report says truncates but which the
;;; reference never rebinds, so it yields an exact rational in both.

;;; ---- literals ----------------------------------------------------------
;;; `code-of-variable` splices a literal's cached value straight into the
;;; generated code, so the unit symbol has to evaluate to itself.
(define |#U| (string->symbol "#U"))
(define nil '())
(define (unspecified) (if #f #f))
;;; The built-in module's value. `code-of-with` tests for this marker and, on
;;; finding it, uses its body directly: `fx`'s bindings are already global.
(define fx (list '*module* 'fx))

;;; ---- bool --------------------------------------------------------------
(define (not? x) (not x))
(define (and? x y) (and x y))
(define (or? x y) (or x y))
(define (equiv? x y) (or (and x y) (and (not x) (not y))))

;;; ---- refof -------------------------------------------------------------
(define (new x) (list '*loc* x))
(define ref new)
(define (get r) (cadr r))
(define ^ get)
;;; FX's `set!` is renamed by the code generator, since Scheme's is syntax.
(define (set!-1 r x) (set-car! (cdr r) x) |#U|)
(define := set!-1)

;;; ---- int and float -----------------------------------------------------
(define (neg x) (- x))
(define (absolute x) (abs x))
(define fl+ +)
(define fl- -)
(define fl* *)
(define fl/ /)
(define fl= =)
(define fl< <)
(define fl> >)
(define fl<= <=)
(define fl>= >=)
(define (flabs x) (abs x))
(define (flneg x) (- x))
(define (int->float x) (inexact x))
;;; `floor`, `ceiling`, `truncate` and `round` are typed `(float) int`, as in
;;; the originals; FX-87's Common Lisp host gave an exact integer, but
;;; Scheme's keep the argument's exactness, so `(floor 2.3)` would be the
;;; inexact 2.0, typed `int`, and fail where an exact integer is needed (an
;;; index). So here they give an exact integer, as their type says; an
;;; infinity or a NaN, which is no integer, is an error.
(define %floor floor)
(define %ceiling ceiling)
(define %truncate truncate)
(define %round round)
(define (floor x) (exact (%floor x)))
(define (ceiling x) (exact (%ceiling x)))
(define (truncate x) (exact (%truncate x)))
(define (round x) (exact (%round x)))

;;; ---- char --------------------------------------------------------------
(define (char->int c) (char->integer c))
(define (int->char n) (integer->char n))
(define (char-ci=? a b) (char=? (char-downcase a) (char-downcase b)))
(define (char-ci<? a b) (char<? (char-downcase a) (char-downcase b)))
(define (char-ci>? a b) (char>? (char-downcase a) (char-downcase b)))
(define (char-ci<=? a b) (char<=? (char-downcase a) (char-downcase b)))
(define (char-ci>=? a b) (char>=? (char-downcase a) (char-downcase b)))

;;; ---- string and sym ----------------------------------------------------
(define (string->sym s) (string->symbol s))
(define (sym->string s) (symbol->string s))
(define (sym=? a b) (equal? a b))
(define (string-ci=? a b) (string=? a b))
(define (string-ci<? a b) (string<? a b))
(define (string-ci>? a b) (string>? a b))
(define (string-ci<=? a b) (string<=? a b))
(define (string-ci>=? a b) (string>=? a b))
(define %string-set! string-set!)
(define (string-set! s i c) (%string-set! s i c) |#U|)
(define (string-fill! s c)
  (let loop ((i 0))
    (if (< i (string-length s))
        (begin (%string-set! s i c) (loop (+ i 1)))
        |#U|)))
(define (error s) (raise (list '*error* s)))

;;; ---- permutation -------------------------------------------------------
;;; A permutation is its index mapping, kept as a procedure.
(define (make-permutation to ignore) (list '*permutation* to))
(define (identity l) (make-permutation (lambda (x) x) l))
(define (cshift l o)
  (make-permutation
   (lambda (x) (if (positive? o) (modulo (+ x o) l) (modulo (- x o) l)))
   l))
(define (eoshift l o)
  (make-permutation (lambda (x) (+ x o)) l))

;;; ---- uniqueof ----------------------------------------------------------
(define (unique x) (list '*unique* x))
(define (value x) (cadr x))

;;; ---- listof ------------------------------------------------------------
;;; FX's lists are mutable pairs, which is why `set-car!`/`set-cdr!` were kept
;;; in the Scheme core rather than dropped with R7RS.
(define (null) '())
(define (reduce f l s)
  (let loop ((l l))
    (if (null? l) s (f (car l) (loop (cdr l))))))
(define (for-each f l)
  (let loop ((l l))
    (if (null? l) |#U| (begin (f (car l)) (loop (cdr l))))))

;;; The two the archive declares and never binds; see docs/divergences.md.
(define (cons~ x s f) (if (pair? x) (s (car x) (cdr x)) (f x)))
(define (nil~ x s f) (if (pair? x) (f x) (s)))

;;; ---- vectorof ----------------------------------------------------------
;;; FX's mutators return unit, so they wrap the host's. The host procedure is
;;; captured *before* the name is rebound -- rebinding first and then calling
;;; the name would be an infinite recursion, and one that only shows up as a
;;; step-limit timeout rather than as a stack overflow.
(define %vector-set! vector-set!)
(define (vector-set! v i x) (%vector-set! v i x) |#U|)
(define (vector-fill! v x)
  (let loop ((i 0))
    (if (< i (vector-length v))
        (begin (%vector-set! v i x) (loop (+ i 1)))
        |#U|)))
(define (vector-map f v)
  (let* ((l (vector-length v)) (new (make-vector l)))
    (let loop ((i 0))
      (if (= i l) new (begin (%vector-set! new i (f (vector-ref v i))) (loop (+ i 1)))))))
(define (vector-map2 f v1 v2)
  (let* ((l (vector-length v1)) (new (make-vector l)))
    (let loop ((i 0))
      (if (= i l)
          new
          (begin (%vector-set! new i (f (vector-ref v1 i) (vector-ref v2 i)))
                 (loop (+ i 1)))))))
(define (vector-reduce f v s)
  (let loop ((i (- (vector-length v) 1)) (s s))
    (if (negative? i) s (loop (- i 1) (f (vector-ref v i) s)))))

;;; ---- the parallel vector operators -------------------------------------
(define (scan f v)
  (let* ((l (vector-length v)) (new (make-vector l)))
    (if (= l 0)
        new
        (let loop ((i 1) (r (vector-ref v 0)))
          (%vector-set! new (- i 1) r)
          (if (= i l)
              new
              (let ((r (f (vector-ref v i) r)))
                (loop (+ i 1) r)))))))
(define (segmented-scan f flags v)
  (let* ((l (vector-length v)) (new (make-vector l)))
    (let loop ((i 0) (r #f) (started #f))
      (if (= i l)
          new
          (let* ((restart (or (not started) (vector-ref flags i)))
                 (r (if restart (vector-ref v i) (f (vector-ref v i) r))))
            (%vector-set! new i r)
            (loop (+ i 1) r #t))))))
(define (permute m v)
  (let* ((l (vector-length v)) (new (make-vector l)))
    (let loop ((i 0))
      (if (= i l)
          new
          (begin (%vector-set! new ((cadr m) i) (vector-ref v i)) (loop (+ i 1)))))))
(define (compress flags v)
  (let loop ((i (- (vector-length v) 1)) (acc '()))
    (if (negative? i)
        (list->vector acc)
        (loop (- i 1) (if (vector-ref flags i) (cons (vector-ref v i) acc) acc)))))
(define (expand flags v)
  (let* ((l (vector-length flags)) (new (make-vector l)))
    (let loop ((i 0) (j 0))
      (if (= i l)
          new
          (if (vector-ref flags i)
              (begin (%vector-set! new i (vector-ref v j)) (loop (+ i 1) (+ j 1)))
              (loop (+ i 1) j))))))

;;; ---- sexp --------------------------------------------------------------
;;; `sexp` is a tagged union over the other types; `->sexp` injects and
;;; `->sexp~` is the matching CPS destructor.
(define (%->sexp tag) (lambda (u) (list '*sum* tag (list '*product* (vector u)))))
(define (%->sexp~ tag)
  (lambda (val succ fail)
    (if (equal? (cadr val) tag)
        (succ (vector-ref (cadr (caddr val)) 0))
        (fail val))))
(define unit->sexp (%->sexp 'unit->sexp))
(define bool->sexp (%->sexp 'bool->sexp))
(define sym->sexp (%->sexp 'sym->sexp))
(define int->sexp (%->sexp 'int->sexp))
(define float->sexp (%->sexp 'float->sexp))
(define char->sexp (%->sexp 'char->sexp))
(define string->sexp (%->sexp 'string->sexp))
(define list->sexp (%->sexp 'list->sexp))
(define vector->sexp (%->sexp 'vector->sexp))
(define unit->sexp~ (%->sexp~ 'unit->sexp))
(define bool->sexp~ (%->sexp~ 'bool->sexp))
(define sym->sexp~ (%->sexp~ 'sym->sexp))
(define int->sexp~ (%->sexp~ 'int->sexp))
(define float->sexp~ (%->sexp~ 'float->sexp))
(define char->sexp~ (%->sexp~ 'char->sexp))
(define string->sexp~ (%->sexp~ 'string->sexp))
(define list->sexp~ (%->sexp~ 'list->sexp))
(define vector->sexp~ (%->sexp~ 'vector->sexp))
(define (sexp=? a b) (equal? a b))

;;; ---- streams -----------------------------------------------------------
;;; FX's streams over the Scheme core's textual ports. `stream-read-sexp` must
;;; yield a value of type `sexp`, so a datum read from the file is converted
;;; into the same tagged representation the code generator emits for a quoted
;;; literal -- `quoted-to-sexp`, at run time.
(define (open-input-stream name) (%open-input-file name))
(define (open-output-stream name) (%standard-output))
(define standard-input #f)
(define standard-output (%standard-output))
(define (close-stream s) (%close-port s) |#U|)
(define (stream-char-eof? s) (%port-at-eof? s))
(define (stream-sexp-eof? s) (%port-at-eof? s))
(define (stream-read-char s) (%port-read-char s))
(define (stream-write-char s c) (%port-write-string s (string c)) |#U|)
(define (read-char) (%port-read-char standard-input))

(define (datum->sexp x)
  (cond ((null? x) (list->sexp '()))
        ((pair? x) (list->sexp (map datum->sexp x)))
        ((vector? x) (vector->sexp (list->vector (map datum->sexp (vector->list x)))))
        ((boolean? x) (bool->sexp x))
        ((symbol? x) (sym->sexp x))
        ((string? x) (string->sexp x))
        ((char? x) (char->sexp x))
        ((and (number? x) (integer? x)) (int->sexp x))
        ((number? x) (float->sexp x))
        (else (error "unknown datum in datum->sexp"))))

;;; The inverse, for writing: strip the tags back off.
(define (sexp->datum x)
  (let ((tag (cadr x)) (v (vector-ref (cadr (caddr x)) 0)))
    (cond ((eq? tag 'list->sexp) (map sexp->datum v))
          ((eq? tag 'vector->sexp) (list->vector (map sexp->datum (vector->list v))))
          (else v))))

;;; `fx-read` folds symbol case, so reading a stream does too.
(define (stream-read-sexp s) (datum->sexp (%port-read-datum s #t)))
(define (read-sexp) (stream-read-sexp standard-input))
(define (stream-write-sexp s x) (%port-write-string s (%datum->string (sexp->datum x))) |#U|)
(define (write-sexp x) (stream-write-sexp standard-output x))
(define (write-char c) (stream-write-char standard-output c))
