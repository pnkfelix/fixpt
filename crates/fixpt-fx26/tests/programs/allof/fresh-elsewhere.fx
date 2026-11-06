;; => (1 2)
;; A call that allocates, but not where its results' types say: what it
;; makes no procedure kept can reach, so the closures' meet is one value.
;; `ab` and `ac` share the tag `a`: `(sum a 1)` is both.
(define-type ab (sumof (a int) (b int)))
(define-type ac (sumof (a int) (c int)))
(define mk (allof (subr (maxeff (alloc @h) (read @h)) (ab) (subr pure () ab))
                  (subr (maxeff (alloc @h) (read @h)) (ac) (subr pure () ac)))
  (lambda (x) (let* ((c ((proj new @h) x)) (v (get c))) (lambda () v))))
(define g (mk (sum a 1)))
(define as-ab (subr pure () ab) g)
(define as-ac (subr pure () ac) g)
(list (tagcase (as-ab) (a i i) (b j j)) (tagcase (as-ac) (a i (+ i 1)) (c k k)))
