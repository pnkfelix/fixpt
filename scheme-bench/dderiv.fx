;;; DDERIV -- Table-driven symbolic derivation.
;;;
;;; From Larceny's R7RS benchmarks (test/Benchmarking/R7RS/src/dderiv.scm),
;;; ported to FX-26. Larceny's input: 10000000 iterations of
;;; (dderiv '(+ (* 3 x x) (* a x x) (* b x) 5)).
;;; Answer: (+ (* (* 3 x x) (+ (/ 0 3) (/ 1 x) (/ 1 x)))
;;;            (* (* a x x) (+ (/ 0 a) (/ 1 x) (/ 1 x)))
;;;            (* (* b x) (+ (/ 0 b) (/ 1 x)))
;;;            0)
;;;
;;; The expressions are FX-26 `datum`s, Scheme's own data, a union: built
;;; with `cons` and taken apart with `pair?`, `car` and `cdr` as Scheme's are
;;; (until 2026-10-08 by `datum-` operations, 3.38 s native, now 1.65);
;;; `eq?` on symbols is `symbol=?`.
;;; Scheme's `map` over the operands is written out, once for `dderiv` and
;;; once for the lambda of the `*` case. The input is built in the file.
;;; Larceny checks the result with `equal?` against its input file; here
;;; the result is the program's value, printed as Scheme prints it.
;;;
;;; The property table is a hash table of R7RS-large's `(scheme
;;; hash-table)` in the original, keyed by symbols with `symbol-hash`; here
;;; it is a small one written in the port: an array of 8 buckets, each an
;;; association list, indexed by `symbol-name-hash`, which never grows (it
;;; holds 4 keys). Its values are the association lists of the original.
;;; `get` takes a default where the original returns `#f`: a procedure
;;; that stands for the original's `error` (FX-26 has none), never
;;; reached, returning the symbol `no-derivation-method`.

;;; Returns the wrong answer for quotients.
;;; Fortunately these aren't used in the benchmark.

(define* sym (subr pure (string) datum) (lambda (s) (string->symbol s)))
(define* is? (subr pure (datum symbol) bool)
  (lambda (a s) (and (symbol? a) (symbol=? a s))))
(define* list2 (subr pure (datum datum) datum)
  (lambda (a b) (cons a (cons b nil))))
(define* list3 (subr pure (datum datum datum) datum)
  (lambda (a b c) (cons a (list2 b c))))
(define* list4 (subr pure (datum datum datum datum) datum)
  (lambda (a b c d) (cons a (list3 b c d))))

;; The quoted symbols, made once as Scheme's quoted constants are.
(define plus-sym datum (sym "+"))
(define minus-sym datum (sym "-"))
(define times-sym datum (sym "*"))
(define quotient-sym datum (sym "/"))

;; What a derivation method may do: read and change the table, read the
;; globals of the group, and recurse through the table.
(define-effect derives (maxeff (read @heap) (write @heap) (alloc @heap) (read @globals) spin))
(define-type method (subr derives (datum) datum))
(define-type plist (listof (pairof symbol method @heap) @heap))

(define* lookup (subr (maxeff (read @heap) spin) (symbol plist) (union nil (pairof symbol method @heap)))
  (lambda (key table)
    (letrec ((loop (subr (maxeff (read @heap) spin) (plist) (union nil (pairof symbol method @heap)))
               (lambda (x)
                 (if (null? x)
                     no-pair
                     (let ((pair (car x)))
                       (if (symbol=? (car pair) key)
                           pair
                           (loop (cdr x))))))))
      (loop table))))

;; The hash table: symbols to property lists.
(define-type bucket (listof (pairof symbol plist @heap) @heap))
(define properties (arrayof bucket @heap) (make-array 8 nil))
(define* bucket-of (subr pure (symbol) int)
  (lambda (key) (modulo (symbol-name-hash key) 8)))
(define* hash-table-ref/default (subr (maxeff (read @heap) spin) (symbol) plist)
  (lambda (key)
    (letrec ((loop (subr (maxeff (read @heap) spin) (bucket) plist)
               (lambda (b)
                 (cond ((null? b) nil)
                       ((symbol=? (car (car b)) key) (cdr (car b)))
                       (else (loop (cdr b)))))))
      (loop (array-ref properties (bucket-of key))))))
(define* hash-table-set! (subr (maxeff (read @heap) (write @heap) (alloc @heap)) (symbol plist) unit)
  (lambda (key val)
    (let ((i (bucket-of key)))
      (array-set! properties i (cons (cons key val) (array-ref properties i))))))

(define* get (subr (maxeff (read @heap) spin) (symbol symbol method) method)
  (lambda (key1 key2 default)
    (let ((x (hash-table-ref/default key1)))
      (if (not (null? x))
          (let ((y (lookup key2 x)))
            (if (not (null? y))
                (cdr y)
                default))
          default))))

(define* put (subr (maxeff (read @heap) (write @heap) (alloc @heap) spin) (symbol symbol method) unit)
  (lambda (key1 key2 val)
    (let ((x (hash-table-ref/default key1)))
      (if (not (null? x))
          (let ((y (lookup key2 x)))
            (if (not (null? y))
                (set-cdr! y val)
                (set-cdr! x (cons (cons key2 val) (cdr x)))))
          (hash-table-set! key1 (cons (cons key2 val) nil))))))

(define no-method method
  (lambda (a) (sym "no-derivation-method")))

(define* dderiv (subr derives (datum) datum)
  (lambda (a)
    (if (not (pair? a))
        (if (is? a 'x) 1 0)
        (typecase (car a)
          (symbol h ((get h 'dderiv no-method) a))
          (else e (no-method a))))))

;; (map dderiv l)
(define* map-dderiv (subr derives (datum) datum)
  (lambda (l)
    (if (null? l)
        l
        (cons (dderiv (car l)) (map-dderiv (cdr l))))))

;; (map (lambda (a) (list '/ (dderiv a) a)) l)
(define* map-quotient (subr derives (datum) datum)
  (lambda (l)
    (if (null? l)
        l
        (cons (list3 quotient-sym (dderiv (car l)) (car l))
              (map-quotient (cdr l))))))

(define* my+dderiv method
  (lambda (a)
    (cons plus-sym
          (map-dderiv (cdr a)))))

(define* my-dderiv method
  (lambda (a)
    (cons minus-sym
          (map-dderiv (cdr a)))))

(define* *dderiv method
  (lambda (a)
    (list3 times-sym
           a
           (cons plus-sym
                 (map-quotient (cdr a))))))

(define* /dderiv method
  (lambda (a)
    (list3 minus-sym
           (list3 quotient-sym
                  (dderiv (car (cdr a)))
                  (car (cdr (cdr a))))
           (list3 quotient-sym
                  (car (cdr a))
                  (list4 times-sym
                         (car (cdr (cdr a)))
                         (car (cdr (cdr a)))
                         (dderiv (car (cdr (cdr a)))))))))

(put '+ 'dderiv my+dderiv)
(put '- 'dderiv my-dderiv)
(put '* 'dderiv *dderiv)
(put '/ 'dderiv /dderiv)

;; The inputs, where no compiler can fold them (Larceny's `hide`): globals,
;; which a later definition may replace.
;; (+ (* 3 x x) (* a x x) (* b x) 5)
(define input1 datum
  (let ((x (sym "x")) (*s (sym "*")))
    (cons (sym "+")
          (list4 (list4 *s 3 x x)
                 (list4 *s (sym "a") x x)
                 (list3 *s (sym "b") x)
                 5))))
(define iterations int 10000000)

(define* run (subr derives (int datum) datum)
  (lambda (i result) (if (= i 0) result (run (- i 1) (dderiv input1)))))
(run iterations 0)
