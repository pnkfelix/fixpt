;; => (4 -1)
;; Of an `anyof`'s pair members, the greatest is the one `car` takes apart
;; and `cons` builds (logical-types.md §8.8): a list of `nat`s is a list of
;; `int`s, never written.
(define-type ns (anyof (listof nat acyclic) (listof int acyclic)))
(define first (subr pure (ns) int) (lambda (l) (if (null? l) 0 (car l))))
(define v ns (list 4 5))
(define w ns (cons -1 nil))
(list (first v) (first w))
