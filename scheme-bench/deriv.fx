;;; DERIV -- Symbolic derivation.
;;;
;;; From Larceny's R7RS benchmarks (test/Benchmarking/R7RS/src/deriv.scm),
;;; ported to FX-26. Larceny's input: 10000000 iterations of
;;; (deriv '(+ (* 3 x x) (* a x x) (* b x) 5)).
;;; Answer: (+ (* (* 3 x x) (+ (/ 0 3) (/ 1 x) (/ 1 x)))
;;;            (* (* a x x) (+ (/ 0 a) (/ 1 x) (/ 1 x)))
;;;            (* (* b x) (+ (/ 0 b) (/ 1 x)))
;;;            0)
;;;
;;; The expressions are FX-26 `datum`s, Scheme's own data, a union: built
;;; with `cons` and taken apart with `pair?`, `car` and `cdr` as Scheme's are
;;; (until 2026-10-08 by `datum-` operations, 2.69 s native, now 0.92);
;;; `eq?` on symbols is `symbol=?`.
;;; Scheme's `map` over the operands is written out, once for `deriv` and
;;; once for the lambda of the `*` case. The input is built in the file.
;;; Larceny checks the result with `equal?` against its input file; here
;;; the result is the program's value, printed as Scheme prints it.
;;; `error` (no derivation method), never reached, returns the symbol
;;; `no-derivation-method`: FX-26 has no `error`.

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

;; What the group below reads: itself, the helpers and the constants.
(define-effect derives
  (maxeff spin (read (globals deriv map-deriv map-quotient is? list2 list3 list4 sym
                              plus-sym minus-sym times-sym quotient-sym))))

(define-rec
  (deriv (subr derives (datum) datum)
    (lambda (a)
      (cond ((not (pair? a))
             (if (is? a 'x) 1 0))
            ((is? (car a) '+)
             (cons plus-sym
                   (map-deriv (cdr a))))
            ((is? (car a) '-)
             (cons minus-sym
                   (map-deriv (cdr a))))
            ((is? (car a) '*)
             (list3 times-sym
                    a
                    (cons plus-sym
                          (map-quotient (cdr a)))))
            ((is? (car a) '/)
             (list3 minus-sym
                    (list3 quotient-sym
                           (deriv (car (cdr a)))
                           (car (cdr (cdr a))))
                    (list3 quotient-sym
                           (car (cdr a))
                           (list4 times-sym
                                  (car (cdr (cdr a)))
                                  (car (cdr (cdr a)))
                                  (deriv (car (cdr (cdr a))))))))
            (else
             (sym "no-derivation-method")))))
  ;; (map deriv l)
  (map-deriv (subr derives (datum) datum)
    (lambda (l)
      (if (null? l)
          l
          (cons (deriv (car l)) (map-deriv (cdr l))))))
  ;; (map (lambda (a) (list '/ (deriv a) a)) l)
  (map-quotient (subr derives (datum) datum)
    (lambda (l)
      (if (null? l)
          l
          (cons (list3 quotient-sym (deriv (car l)) (car l))
                (map-quotient (cdr l)))))))

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

(define* run (subr spin (int datum) datum)
  (lambda (i result) (if (= i 0) result (run (- i 1) (deriv input1)))))
(run iterations 0)
