;; => 103
;; A definition the template writes is made fresh, as its other binders
;; are: the counter's `count` is its own, not the program's.
(define-syntax define-counter
  (-> (bvar) defn)
  (syntax-rules ()
    ((_ name)
     (begin (define count (new 0))
            (define name (lambda () (begin (set count (+ (get count) 1)) (get count))))))))
(define count 100)
(define-counter tick)
(tick)
(tick)
(+ (tick) count)
