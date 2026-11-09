;; => 4
;; Ellipses two deep: groups, and the parts of each.
(define-syntax groups
  ((expr ...) ...)
  (syntax-rules ()
    ((_ (e ...) ...) (let ((xs (list (list e ...) ...))) (+ (length xs) (car (car xs)))))))
(groups (1 2) (3) ())
