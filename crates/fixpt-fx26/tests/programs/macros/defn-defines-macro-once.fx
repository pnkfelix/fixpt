;; ! `k` is placed where it may be placed more than once (a `many` part)
;; A use's expression placed in the defined macro, which may run it at each
;; of its uses: its signature says `many` if it may.
(define-syntax def-adder
  (macro (bvar expr) defn)
  (syntax-rules
    ((_ name k) (define-syntax name (syntax-rules ((_ e) (+ e k)))))))
