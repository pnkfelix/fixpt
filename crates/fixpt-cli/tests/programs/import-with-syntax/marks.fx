;; A file's trailmark, and its macros that match it and write it.
(define-syntax via (trailmark))
(define-syntax pick
  (syntax-rules #:trailmarks (via)
    ((_ e via d) (if e 1 d))
    ((_ e) e)))
(define-syntax pick-or-7 (syntax-rules ((_ e) (pick e via 7))))
