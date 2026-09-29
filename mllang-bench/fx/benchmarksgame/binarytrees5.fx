;;; BINARYTREES5 -- allocate and walk many binary trees, some short-lived,
;;; one long-lived (the Computer Language Benchmarks Game's binary-trees).
;;;
;;; From Sandmark's Benchmarks Game programs (benchmarks/benchmarksgame/
;;; binarytrees5.ml, sandmark commit 5605805954a0), ported to FX-26;
;;; "Contributed by Troestler Christophe, Modified by Fabrice Le Fessant".
;;; The original's depth is its first argument (default 10); the port's is
;;; `max-depth-input` = 16. The original prints a line per depth, each with
;;; a check (a node count); the port's value is the sum of the checks it
;;; would print: the stretch tree's, each depth's total, and the long-lived
;;; tree's. Answer: 14985902, the sum of the checks in
;;;   stretch tree of depth 17	 check: 262143
;;;   65536	 trees of depth 4	 check: 2031616
;;;   16384	 trees of depth 6	 check: 2080768
;;;   4096	 trees of depth 8	 check: 2093056
;;;   1024	 trees of depth 10	 check: 2096128
;;;   256	 trees of depth 12	 check: 2096896
;;;   64	 trees of depth 14	 check: 2097088
;;;   16	 trees of depth 16	 check: 2097136
;;;   long lived tree of depth 16	 check: 131071
;;; (With the default depth 10, 135854.) Printing a check is adding it to
;;; the total, `print-check`.
;;; `Empty` is made once, as a global, where OCaml's constant constructor
;;; is an immediate; `for` loops are local recursive procedures; `1 lsl k`
;;; is `(exp2 k)`.

(define-datatype tree (empty) (node tree tree))
(define the-empty tree (empty))

(define* make (subr (maxeff (alloc @heap) spin) (int) tree)
  (lambda (d)
    ;; if d = 0 then Empty
    (if (= d 0)
        (node the-empty the-empty)
        (let ((d (- d 1))) (node (make d) (make d))))))

(define* check (subr spin (tree) int)
  (lambda (t) (tagcase t (empty () 0) (node (l r) (+ 1 (+ (check l) (check r)))))))

(define min-depth int 4)

;; The input, where no compiler can fold it: a global.
(define max-depth-input int 16)

(define-effect bt (maxeff (read @heap) (write @heap) (alloc @heap) spin))

(define* main (subr bt () int)
  (lambda ()
    (let* ((max-depth (if (> (+ min-depth 2) max-depth-input) (+ min-depth 2) max-depth-input))
           (stretch-depth (+ max-depth 1))
           (total (the (ref int @heap) (new 0)))
           (print-check (lambda ((c int)) (set total (+ (get total) c)))))
      (begin
        (print-check (check (make stretch-depth)))
        (let ((long-lived-tree (make max-depth)))
          (letrec ((exp2 (subr spin (int) int)
                     (lambda (k) (if (<= k 0) 1 (* 2 (exp2 (- k 1))))))
                   (loop-depths (subr (maxeff bt (read (globals check make min-depth node the-empty))) (int int) unit)
                     (lambda (d0 i)
                       (if (<= i (- (+ (quotient (- max-depth d0) 2) 1) 1))
                           (let* ((d (+ d0 (* i 2)))
                                  (niter (exp2 (+ (- max-depth d) min-depth)))
                                  (c (the (ref int @heap) (new 0))))
                             (letrec ((iter (subr (maxeff bt (read (globals check make node the-empty))) (int) unit)
                                        (lambda (j)
                                          (if (<= j niter)
                                              (begin (set c (+ (get c) (check (make d)))) (iter (+ j 1)))
                                              #u))))
                               (begin
                                 (iter 1)
                                 (print-check (get c))
                                 (loop-depths d0 (+ i 1)))))
                           #u))))
            (begin
              (loop-depths min-depth 0)
              (print-check (check long-lived-tree))
              (get total))))))))
(main)
