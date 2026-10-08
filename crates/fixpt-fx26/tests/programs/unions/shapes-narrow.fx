; Accepted: a union of members of shapes that differ at run time, each
; standard shape predicate narrowing it, where it holds to its member, and
; where it does not to the rest (`docs/research/logical-types.md`, L1).
(define-type v (union int string bool char symbol (listof int @r) (subr pure (int) int)
                      (arrayof int @r)))
(define* f (subr (read @r) (v) int)
  (lambda (x)
    (cond ((int? x) (+ x 1)) ((string? x) (string-length x)) ((bool? x) (if x 1 0))
          ((char? x) (char->integer x)) ((symbol? x) 0) ((array? x) (array-ref x 0))
          ((procedure? x) (x 5)) ((null? x) -1) (else (car x)))))
(f 41)
