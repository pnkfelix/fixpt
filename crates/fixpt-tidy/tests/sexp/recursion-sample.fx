;;; Cases for the lint on self-calls not in tail position that step an index.

;; Flagged: a loop written as recursion, one frame per index.
(define upto (subr spin (int int) (listof int @l))
  (lambda (i n) (if (= i n) nil (cons i (upto (+ i 1) n)))))

;; Flagged: the same, in a `letrec`.
(define count (subr spin (int) int)
  (lambda (n)
    (letrec ((go (subr spin (int) int) (lambda (i) (if (= i 0) 0 (+ 1 (go (- i 1)))))))
      (go n))))

;; Not flagged: the same in tail position, with an accumulator.
(define upto-acc (subr spin (int int (listof int @l)) (listof int @l))
  (lambda (i n acc) (if (< i n) (upto-acc (+ i 1) n (cons i acc)) acc)))

;; Not flagged: a tree walked, keeping a depth; the data changes too.
(define depth (subr spin (tree int) int)
  (lambda (t d) (tagcase t (leaf n d) (node (l r) (+ (depth l (+ d 1)) (depth r (+ d 1)))))))
