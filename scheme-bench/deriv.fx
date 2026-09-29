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
;;; The expressions are FX-26 `datum`s, Scheme's own data, built and taken
;;; apart by the `datum-` operations; `eq?` on symbols is `symbol=?`.
;;; Scheme's `map` over the operands is written out, once for `deriv` and
;;; once for the lambda of the `*` case. The input is built in the file.
;;; Larceny checks the result with `equal?` against its input file; here
;;; the result is the program's value, printed as Scheme prints it.
;;; `error` (no derivation method), never reached, returns the symbol
;;; `no-derivation-method`: FX-26 has no `error`.

;;; Returns the wrong answer for quotients.
;;; Fortunately these aren't used in the benchmark.

(define* sym (subr pure (string) datum) (lambda (s) (datum-symbol s)))
(define* is? (subr pure (datum symbol) bool)
  (lambda (a s) (and (datum-symbol? a) (symbol=? (datum->symbol a) s))))
(define* list2 (subr pure (datum datum) datum)
  (lambda (a b) (datum-cons a (datum-cons b (datum-list (the (listof datum @heap) nil))))))
(define* list3 (subr pure (datum datum datum) datum)
  (lambda (a b c) (datum-cons a (list2 b c))))
(define* list4 (subr pure (datum datum datum datum) datum)
  (lambda (a b c d) (datum-cons a (list3 b c d))))

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
      (cond ((not (datum-pair? a))
             (if (is? a 'x) (datum-int 1) (datum-int 0)))
            ((is? (datum-car a) '+)
             (datum-cons plus-sym
                         (map-deriv (datum-cdr a))))
            ((is? (datum-car a) '-)
             (datum-cons minus-sym
                         (map-deriv (datum-cdr a))))
            ((is? (datum-car a) '*)
             (list3 times-sym
                    a
                    (datum-cons plus-sym
                                (map-quotient (datum-cdr a)))))
            ((is? (datum-car a) '/)
             (list3 minus-sym
                    (list3 quotient-sym
                           (deriv (datum-car (datum-cdr a)))
                           (datum-car (datum-cdr (datum-cdr a))))
                    (list3 quotient-sym
                           (datum-car (datum-cdr a))
                           (list4 times-sym
                                  (datum-car (datum-cdr (datum-cdr a)))
                                  (datum-car (datum-cdr (datum-cdr a)))
                                  (deriv (datum-car (datum-cdr (datum-cdr a))))))))
            (else
             (sym "no-derivation-method")))))
  ;; (map deriv l)
  (map-deriv (subr derives (datum) datum)
    (lambda (l)
      (if (datum-null? l)
          l
          (datum-cons (deriv (datum-car l)) (map-deriv (datum-cdr l))))))
  ;; (map (lambda (a) (list '/ (deriv a) a)) l)
  (map-quotient (subr derives (datum) datum)
    (lambda (l)
      (if (datum-null? l)
          l
          (datum-cons (list3 quotient-sym (deriv (datum-car l)) (datum-car l))
                      (map-quotient (datum-cdr l)))))))

;; The inputs, where no compiler can fold them (Larceny's `hide`): globals,
;; which a later definition may replace.
;; (+ (* 3 x x) (* a x x) (* b x) 5)
(define input1 datum
  (let ((x (sym "x")) (*s (sym "*")))
    (datum-cons (sym "+")
                (list4 (list4 *s (datum-int 3) x x)
                       (list4 *s (sym "a") x x)
                       (list3 *s (sym "b") x)
                       (datum-int 5)))))
(define iterations int 10000000)

(define* run (subr spin (int datum) datum)
  (lambda (i result) (if (= i 0) result (run (- i 1) (deriv input1)))))
(run iterations (datum-int 0))
