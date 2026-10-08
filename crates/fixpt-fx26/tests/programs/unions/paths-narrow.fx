; Accepted: a test narrows a path from a variable, `(car x)`, `(extract p a)`,
; as it does a variable, while nothing may have changed what the path reads
; (`TODO.md` §54): a write to another region leaves it; frozen data, and a
; product's fields, nothing writes.
(define-type v (union int string))
(define-type cell (pairof v int @r))
(define-type frozen (pairof v int (const heap)))
(define* plus (subr (read @r) (cell) int)
  (lambda (x) (if (int? (car x)) (+ (car x) 1) 0)))
(define* otherwise (subr (read @r) (cell) int)
  (lambda (x) (if (string? (car x)) 0 (+ (car x) 1))))
(define* elsewhere (subr (maxeff (read @r) (write @s)) (cell (ref int @s)) int)
  (lambda (x b) (if (int? (car x)) (begin (set b 1) (+ (car x) 1)) 0)))
(define* through-heap (subr (write @heap) (frozen (ref int @heap)) int)
  (lambda (x b) (if (int? (car x)) (begin (set b 1) (+ (car x) 1)) 0)))
(define* field (subr pure ((productof (a v))) int)
  (lambda (p) (if (int? (extract p a)) (+ (extract p a) 1) 0)))
(field (product (a 41)))
