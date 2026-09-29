;;; A promise and `await`, over one primitive, `suspend!` (as Guile Fibers'
;;; `suspend-current-task`, or Rust's `Waker`). The abort carries a thunk
;;; that files the suspended task somewhere: `yield!` files it on the run
;;; queue, `await!` among the promise's waiters. Every suspension resumes
;;; with unit; the value awaited is read from the promise.
(define-effect Q (maxeff (read @q) (write @q) (alloc @q) (read (globals queue log))))
(define-effect D (maxeff spin Q (read (globals sched queue log suspend! enqueue! yield! await! resolve! enqueue-all! note! fut))))
(define-type task (composable unit unit D @p))
(define-type promise (ref (sumof (pending (listof task @q)) (resolved int)) @q))
(define sched (prompt-tag unit (subr Q () unit) D @p) (make-continuation-prompt-tag))
(define queue (ref (listof task @q) @q) (new nil))
(define log (ref (listof int @q) @q) (new nil))

(define* enqueue! (subr Q (task) unit)
  (lambda (k)
    (let ((back (the (listof task @q) (reverse (get queue)))))
      (set queue (reverse (the (listof task @q) (cons k back)))))))

(define* suspend! (subr (maxeff (goto @p) (comefrom @p)) ((subr Q (task) unit)) unit)
  (lambda (file)
    (call-with-composable-continuation
      (lambda (k) (abort-current-continuation sched (lambda () (file k))))
      sched)))

(define* yield! (subr (maxeff (goto @p) (comefrom @p)) () unit)
  (lambda () (suspend! enqueue!)))

(define* await! (subr (maxeff D (goto @p) (comefrom @p)) (promise) int)
  (lambda (pr)
    (tagcase (get pr)
      (resolved v v)
      (pending ws (begin (suspend! (lambda (k) (set pr (sum pending (cons k ws)))))
                         (await! pr))))))

(define* enqueue-all! (subr (maxeff Q spin) ((listof task @q)) unit)
  (lambda (ks)
    (if (null? ks) #u (begin (enqueue! (car ks)) (enqueue-all! (cdr ks))))))

(define* resolve! (subr (maxeff Q spin) (promise int) unit)
  (lambda (pr v)
    (tagcase (get pr)
      (resolved u #u)                     ; already resolved: ignored here
      (pending ws (begin (set pr (sum resolved v))
                         (enqueue-all! (reverse ws)))))))

(define* run! (subr (maxeff D (goto @p) (comefrom @p)) () unit)
  (lambda ()
    (let ((q (get queue)))
      (if (null? q)
          #u
          (begin (set queue (cdr q))
                 (prompt sched ((car q) #u) (lambda (file) (file)))
                 (run!))))))

(define* spawn! (subr (maxeff D (goto @p) (comefrom @p))
                      ((subr (maxeff D (goto @p) (comefrom @p)) () unit)) unit)
  (lambda (thunk) (prompt sched (begin (yield!) (thunk)) (lambda (file) (file)))))

(define fut promise (new (sum pending nil)))
(define* note! (subr Q (int) unit) (lambda (x) (set log (cons x (get log)))))

(spawn! (lambda () (begin (note! 1) (note! (await! fut)))))
(spawn! (lambda () (begin (note! 2) (yield!) (note! 3) (resolve! fut 42))))
(run!)
(the (listof int @q) (reverse (get log)))   ; (1 2 3 42)

