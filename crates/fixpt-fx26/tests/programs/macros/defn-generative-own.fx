;; => 2
;; A template's own generative type and conversions, made fresh: what the
;; use names is all the program sees of them.
(define-syntax define-counter
  (-> (bvar bvar bvar) defn)
  (syntax-rules
    ((_ zero inc value)
     (begin (define-generative c int #:seal mk #:unseal get)
            (define zero c (mk 0))
            (define inc (->* (c) c) (lambda (x) (mk (+ (get x) 1))))
            (define value (->* (c) int) (lambda (x) (get x)))))))
(define-counter z next count)
(count (next (next z)))
