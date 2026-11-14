;; => 4
;; A module parameter typed by a `moduleof` whose labels are keywords: its
;; names known by their labels, for a `with` of it.
(define h (lambda ((m (moduleof (abs #:t u type) (val #:zero u) (val #:size (subr pure (u) int)))))
            (with m (size zero))))
(define m (module (define-generative t int #:seal mk #:unseal un)
                  (define zero t (mk 4))
                  (define size (subr pure (t) int) un)))
(h m)
