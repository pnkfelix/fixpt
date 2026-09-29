;;; Two tasks taking turns: a round-robin scheduler over one prompt tag.
;;; `yield!` captures the rest of the running task up to `sched`'s prompt
;;; and aborts to the scheduler with it; the scheduler puts it at the back
;;; of the run queue, and `run!` resumes queued tasks until none is left.
(define-effect D (maxeff spin (read @q) (write @q) (alloc @q)
                         (read (globals sched queue log yield! pinger))))
(define-type task (composable unit unit D @p))
(define sched (prompt-tag unit task D @p) (make-continuation-prompt-tag))
(define queue (ref (listof task @q) @q) (new nil))
(define log (ref (listof int @q) @q) (new nil))

(define* yield! (subr (maxeff (goto @p) (comefrom @p)) () unit)
  (lambda ()
    (call-with-composable-continuation
      (lambda (k) (abort-current-continuation sched k))
      sched)))

(define* enqueue! (subr (maxeff (read @q) (write @q) (alloc @q)) (task) unit)
  (lambda (k)
    (let ((back (the (listof task @q) (reverse (get queue)))))
      (set queue (reverse (the (listof task @q) (cons k back)))))))

;; Start a task: it yields at once, so its first step runs from `run!`.
(define* spawn! (subr (maxeff D (goto @p) (comefrom @p))
                      ((subr (maxeff D (goto @p) (comefrom @p)) () unit)) unit)
  (lambda (thunk) (prompt sched (begin (yield!) (thunk)) (lambda (k) (enqueue! k)))))

(define* run! (subr (maxeff D (goto @p) (comefrom @p)) () unit)
  (lambda ()
    (let ((q (get queue)))
      (if (null? q)
          #u
          (begin
            (set queue (cdr q))
            (prompt sched ((car q) #u) (lambda (k) (enqueue! k)))
            (run!))))))

(define* pinger (subr (maxeff D (goto @p) (comefrom @p)) (int int) unit)
  (lambda (who n)
    (if (= n 0)
        #u
        (begin (set log (cons (+ who n) (get log)))
               (yield!)
               (pinger who (- n 1))))))

(spawn! (lambda () (pinger 100 3)))
(spawn! (lambda () (pinger 200 3)))
(run!)
(the (listof int @q) (reverse (get log)))   ; (103 203 102 202 101 201)
