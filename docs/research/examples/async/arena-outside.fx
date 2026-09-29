;;; Structured concurrency meeting a region: the arena `r` encloses the
;;; loop, whose region `s` is bound by `letregion`, and every task writes
;;; the arena. Accepted: the continuations mention `s`, not `r`, and
;;; `letregion s` masks their control effects before `letrena r` looks.
;;; `squares` is pure apart from `spin`.
(define-type (stask (s region) (r region))
  (composable unit unit (maxeff spin (read s) (write s) (alloc s) (write r)) s))

(define squares (subr spin (int) int)
  (lambda (k)
    (letrena r
      (let ((out (the (arrayof int r) (rmake-array r k 0))))
        (begin
          (letregion s
            (let* ((sched (the (prompt-tag unit (stask s r) (maxeff spin (read s) (write s) (alloc s) (write r)) s)
                               (make-continuation-prompt-tag)))
                   (queue (the (ref (listof (stask s r) s) s) (new nil)))
                   (park! (lambda ((k (stask s r))) (set queue (cons k (get queue)))))  ; LIFO: order is no matter here
                   (yield! (the (subr (maxeff (goto s) (comefrom s)) () unit)
                             (lambda ()
                               (call-with-composable-continuation
                                 (lambda (k) (abort-current-continuation sched k)) sched)))))
              (letrec ((spawn-all (subr (maxeff spin (read s) (write s) (alloc s) (write r) (goto s) (comefrom s)) (int) unit)
                         (lambda (i)
                           (if (= i k)
                               #u
                               (begin (prompt sched (begin (yield!) (array-set! out i (* i i))) park!)
                                      (spawn-all (+ i 1))))))
                       (run! (subr (maxeff spin (read s) (write s) (alloc s) (write r) (goto s) (comefrom s)) () unit)
                         (lambda ()
                           (let ((q (get queue)))
                             (if (null? q)
                                 #u
                                 (begin (set queue (cdr q))
                                        (prompt sched ((car q) #u) park!)
                                        (run!)))))))
                (begin (spawn-all 0) (run!)))))
          (letrec ((sum-from (subr (maxeff spin (read r)) (int int) int)
                     (lambda (i acc) (if (= i k) acc (sum-from (+ i 1) (+ acc (array-ref out i)))))))
            (sum-from 0 0)))))))

(squares 5)   ; 0+1+4+9+16 = 30
