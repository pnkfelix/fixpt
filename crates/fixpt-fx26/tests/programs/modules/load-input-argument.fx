;; => 42
;; A file's module, loaded where a narrower module is expected: the load is
;; a hidden global, defined first, and only the use is narrowed. The two
;; compilers once disagreed here, as the FX-26 one finds what a place is
;; narrowed to by the place, and the hidden definition had the use's.
(define half-of (lambda ((m (moduleof (val half int)))) (with m half)))
(define r (let* ((h (half-of (load-input "../module-files/answer.fx")))) (* 2 h)))
r
