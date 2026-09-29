;;; A large array in a frame's slot, live across one call and dead across
;;; the next, which collects: the frame's stack map leaves it untraced
;;; there (`docs/research/generational-gc.md`), and `keep` holds it live.
(define* h (subr (maxeff spin (read @heap)) ((arrayof int @heap) int) int)
  (lambda (a k) (if (= k 0) (array-length a) (h a (- k 1)))))
(define* g (subr (maxeff spin (alloc @heap)) (int) int)
  (lambda (n) (if (= n 0) 0 (begin (cons n (the (listof int @heap) nil)) (g (- n 1))))))
(define drop (subr (maxeff spin (alloc @heap) (read @heap) (read @globals)) () int)
  (lambda () (let ((a (the (arrayof int @heap) (make-array 100000 0)))) (let ((n (h a 1))) (+ (g 3000) n)))))
(define keep (subr (maxeff spin (alloc @heap) (read @heap) (read @globals)) () int)
  (lambda () (let ((a (the (arrayof int @heap) (make-array 100000 0)))) (let ((n (h a 1))) (+ (g 3000) (+ n (array-length a)))))))
(drop)
(keep)
