;;; A loop with no recursion: a continuation kept in a reference, and called
;;; again each time it returns. Run, it must stop at the step limit.
(define ks (ref (listof (subr (goto @k) (int) void) @b) @b) (new nil))
(let ((n ((proj (proj (proj cwcc @k) int) (maxeff (write @b) (alloc @b) (read (globals ks))))
          (lambda ((k (subr (goto @k) (int) void))) (begin (set ks (cons k nil)) 0)))))
  ((car (get ks)) (+ n 1)))
