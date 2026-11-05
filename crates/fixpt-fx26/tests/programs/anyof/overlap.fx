;; => (3 2 5)
;; Members that overlap, immutable: two lists `acyclic`. A test that keeps
;; both keeps their union, which is below a list of either's elements.
(define-type ns (anyof (listof int acyclic) (listof bool acyclic) string))
(define count (subr pure ((listof (oneof int bool) acyclic)) int)
  (letrec ((go (subr pure ((listof (oneof int bool) acyclic)) int)
             (lambda (l) (if (null? l) 0 (+ 1 (go (cdr l)))))))
    go))
(define* size (subr pure (ns) int)
  (lambda (v) (if (string? v) (string-length v) (count v))))
(define is ns (list 1 2 3))
(define bs ns (list #t #f))
(list (size is) (size bs) (size "hello"))
