;; => 6
;; A head a template writes is its macro wherever the use is: a binder of
;; the name around the use does not capture it (TODO.md §295).
(define-syntax loop (macro (_ expr) expr) (syntax-rules ((_ e) e)))
(define-syntax plus-one (macro (_ expr) expr) (syntax-rules ((_ e) (+ e (loop 1)))))
(let ((loop (lambda ((i int)) (* i 3)))) (plus-one 5))
