; A bytevector as every machine prints one (TODO.md §84): R7RS's `#u8(…)`.
(define made (subr (alloc @heap) () (bytevectorof @heap))
  (lambda () (string->utf8 "Aé\x0;")))
(made)
