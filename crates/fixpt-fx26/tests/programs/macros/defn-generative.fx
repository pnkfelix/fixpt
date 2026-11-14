;; => 5
;; A macro that makes a generative type and its conversions, each named by
;; the use (`docs/research/generative-types.md` §7).
(define-syntax define-unit
  (-> (dvar bvar bvar) defn)
  (syntax-rules
    ((_ name to from) (define-generative name int #:seal to #:unseal from))))
(define-unit meters to-m from-m)
(define d meters (to-m 5))
(from-m d)
