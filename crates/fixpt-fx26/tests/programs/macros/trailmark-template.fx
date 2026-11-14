;; => (1 7)
;; A template that writes a trailmark another macro's pattern matches: the
;; definition's, whatever the use writes.
(define-syntax via (trailmark "a `pick`'s second, before the default"))
(define-syntax pick
  (syntax-rules #:trailmarks (via)
    ((_ e via d) (if e 1 d))
    ((_ e) e)))
(define-syntax pick-or-7 (syntax-rules ((_ e) (pick e via 7))))
(list (pick-or-7 #t) (pick-or-7 #f))
