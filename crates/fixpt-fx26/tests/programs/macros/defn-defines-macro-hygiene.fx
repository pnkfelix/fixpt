;; => (2 100 15)
;; The defined macro's names mean what they do where the template's macro
;; is defined: one the template binds, its fresh one (`count`); any other
;; the top level's there (`+`), whatever binds it where the defined macro is
;; used.
(define-syntax def-counter
  (macro (_ bvar) defn)
  (syntax-rules
    ((_ name)
     (begin (define count (new 0))
            (define-syntax name
              (syntax-rules ((_) (begin (set count (+ (get count) 1)) (get count)))))))))
(define-syntax def-adder
  (macro (_ bvar (many expr)) defn)
  (syntax-rules
    ((_ name k) (define-syntax name (syntax-rules ((_ e) (+ e k)))))))
(define count 100)
(def-counter tick)
(def-adder add5 5)
(tick)
(list (tick) count (let ((+ (lambda ((a int) (b int)) 0))) (add5 10)))
