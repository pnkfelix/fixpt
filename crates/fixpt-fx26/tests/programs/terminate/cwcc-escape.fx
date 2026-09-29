;;; A continuation only called while `cwcc` runs can only leave it: no
;;; `spin`.
(define early (subr pure (int) int)
  (lambda (n)
    ((proj (proj (proj cwcc @k) int) (goto @k))
     (lambda ((k (subr (goto @k) (int) void))) (if (= n 0) (k 7) n)))))
(early 0)
