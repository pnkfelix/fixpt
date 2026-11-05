;; => (7 1 0)
;; `car` of a union of lists neither above the other: taken apart member by
;; member (logical-types.md §8.5, rule 5), its type the union of what each
;; gives.
(define-type ib (anyof (listof int acyclic) (listof bool acyclic)))
(define first (subr pure (ib) int)
  (lambda (l) (if (null? l) 0 (let ((h (car l))) (if (int? h) h (if h 1 2))))))
(list (first (list 7 8)) (first (list #t)) (first nil))
