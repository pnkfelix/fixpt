;;; References and arrays the native convention makes in line (`direct/x64.rs`,
;;; `box_at` and `array_at`): arrays of every length either side of the most
;;; made so (16), in the heap and in a region, each field read back; and so
;;; many that a region's chunks fill.
(define* sum-from (subr (maxeff spin (read @h)) ((arrayof int @h) int int) int)
  (lambda (xs i acc)
    (if (= i (array-length xs)) acc (sum-from xs (+ i 1) (+ acc (array-ref xs i))))))

;; Arrays of lengths 0 to 20, each filled with its length, `rounds` times
;; over: the sum of their fields, and of the references' contents.
(define* in-heap (subr (maxeff spin (alloc @h) (read @h)) (int int int) int)
  (lambda (rounds n acc)
    (if (= rounds 0)
        acc
        (let* ((xs (the (arrayof int @h) (make-array n n)))
               (r (the (ref int @h) (new n))))
          (in-heap (if (= n 20) (- rounds 1) rounds) (if (= n 20) 0 (+ n 1))
                   (+ acc (+ (sum-from xs 0 0) (get r))))))))

(define in-region (subr spin (int) int)
  (lambda (rounds)
    (letrena r
      (letrec ((sum-at (subr (maxeff spin (read r)) ((arrayof int r) int int) int)
                 (lambda (xs i acc)
                   (if (= i (array-length xs)) acc (sum-at xs (+ i 1) (+ acc (array-ref xs i))))))
               (go (subr (maxeff spin (alloc r) (read r)) (int int int) int)
                 (lambda (rounds n acc)
                   (if (= rounds 0)
                       acc
                       (let* ((xs (the (arrayof int r) (rmake-array r n n)))
                              (b (the (ref int r) (rnew r n))))
                         (go (if (= n 20) (- rounds 1) rounds) (if (= n 20) 0 (+ n 1))
                             (+ acc (+ (sum-at xs 0 0) (get b)))))))))
        (go rounds 0 0)))))

(the (listof int @l) (list (in-heap 1 0 0) (in-heap 300 0 0) (in-region 1) (in-region 300)))
