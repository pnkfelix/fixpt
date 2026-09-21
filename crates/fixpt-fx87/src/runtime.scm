;;; The FX-87 run-time environment, as Scheme.
;;;
;;; Erasure emits FX-87 names directly, and most of them are already Scheme:
;;; `car`, `cons`, `+`, `map` and the rest need no help. Defined here are only
;;; the names where FX-87 and Scheme differ — which is itself informative about
;;; how little of FX-87 is not Scheme underneath.
;;;
;;; The representations are the ones `erase-standard-type` commits to, so they
;;; are not free choices: a `oneof` is a tagged pair, a `recordof` an
;;; association list, a `ref` a box.

;;; ---- unit ----
;;; FX-87 writes it `#u`, which is not Scheme syntax. The archive's own runtime
;;; returns the symbol `|#u|` from `fx-set`, so that is what it is here.
(define %fx-unit (string->symbol "#u"))

;;; ---- references ----
;;; `(ref t r)` is a box. `%make-box` and friends are primitives rather than
;;; library procedures precisely so that redefining a vector operation cannot
;;; disturb them.
(define (new v) (%make-box v))
(define (get r) (%box-ref r))
(define (set r v) (%box-set! r v) %fx-unit)

;;; ---- booleans ----
;;; FX-87 spells these with a trailing `?` because `and` and `or` are not
;;; special forms there: they are ordinary subroutines, so both arguments are
;;; always evaluated.
(define (equiv? a b) (eq? a b))
(define (and? a b) (if a b #f))
(define (or? a b) (if a #t b))
(define (not? a) (if a #f #t))

;;; ---- numbers ----
;;; `/` is the INT operation — `int` and `float` are separate types with
;;; separate operators — so it truncates rather than producing a rational.
;;; `(/ 7 2)` is 3.
(define (/ a b) (quotient a b))
;;; The float operations are separate names in FX-87 because `int` and `float`
;;; are separate types with no subtyping between them — `(fl+ 1 2.5)` is a type
;;; error. Underneath they are the same arithmetic.
;;; Identity, which is not a shortcut. FX-87 separates `int` and `float` in the
;;; TYPE system only; underneath they are the same numbers, which is exactly why
;;; `integer?` is true of `1.0` and that literal type-checks as an `int`.
(define (int->float n) n)
(define (float->int f) f)
(define (int->char n) (integer->char n))
(define (char->int c) (char->integer c))
(define (fl+ a b) (+ a b))
(define (fl- a b) (- a b))
(define (fl* a b) (* a b))
(define (fl/ a b) (/ a b))
(define (fl= a b) (= a b))
(define (fl< a b) (< a b))
(define (fl> a b) (> a b))
(define (fl<= a b) (<= a b))
(define (fl>= a b) (>= a b))

;;; ---- lists ----
(define (reduce f l init)
  (if (null? l) init (reduce f (cdr l) (f (car l) init))))

;;; ---- uniqueof ----
;;; `(uniqueof t)` wraps a value so that two of them are distinguishable even
;;; when the values are equal — which is what `(alloc @uniqueof)` in its type is
;;; recording.
(define (unique v) (cons '%unique v))
(define (value u) (cdr u))
