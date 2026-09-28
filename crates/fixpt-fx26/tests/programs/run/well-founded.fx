;;; Well-founded recursion needs no `spin`: over the parts of finite data
;;; (a list at a `finite` region, a tree of sums and products), and over
;;; integers counting down to a bound below or up to one above
;;; (size-change termination: `src/terminate.rs`).
(define* len (subr pure ((listof int finite) int) int)
  (lambda (xs n) (if (null? xs) n (len (cdr xs) (+ n 1)))))
(define* count (subr pure (int) int)
  (lambda (n) (if (> n 0) (+ 1 (count (- n 1))) 0)))
(define* up (subr pure (int int) int)
  (lambda (i acc) (if (< i 10) (up (+ i 1) (+ acc i)) acc)))
(define-type tree (sumof (leaf int) (node (productof (l tree) (r tree)))))
(define* total (subr pure (tree) int)
  (lambda (t) (tagcase t (leaf n n) (node (a b) (+ (total a) (total b))))))
(define-rec (ev (subr (read @globals) (int) bool) (lambda (n) (if (<= n 0) #t (od (- n 1)))))
            (od (subr (read @globals) (int) bool) (lambda (n) (if (<= n 0) #f (ev (- n 1))))))
(define* ack (subr pure (int int) int)
  (lambda (m n) (cond ((<= m 0) (+ n 1)) ((<= n 0) (ack (- m 1) 1)) (else (ack (- m 1) (ack m (- n 1)))))))
(define built (subr pure (int) (listof int finite))
  (lambda (n) (letfreeze r (the (listof int r) (cons n (cons (+ n 1) nil))))))
(+ (len (built 3) 0) (+ (count 5) (+ (up 0 0) (+ (total (sum node (product (l (sum leaf 1)) (r (sum leaf 2))))) (+ (if (ev 10) 1 0) (ack 2 2))))))
