;; => 32
;; `(hide item …)` (`TODO.md` §69): its items seen by the module's own, not in
;; its type: here a datatype, a `define-rec` and a module included are
;; hidden, and `m` is `(moduleof (val three int) (val total int))`.
(define helpers (module (define twice (subr pure (int) int) (lambda (n) (* 2 n)))))
(define more (module (define three int 3)))
(define m
  (module
    (hide (define-datatype shape (sq int) (rect int int))
          (define-rec
            (area (subr pure (shape) int)
              (lambda (s) (tagcase s (sq (n) (* n n)) (rect (w h) (* w h))))))
          (include helpers))
    (include more)
    (define total int (+ (area (sq three)) (twice (area (rect 2 5)))))))
(+ (with m total) (with m three))
