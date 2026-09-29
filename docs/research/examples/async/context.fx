;;; Task-local context from continuation marks (`contextvars`,
;;; `AsyncLocalStorage`). The scheduler is `ping-pong.fx`'s. Each task
;;; runs under a mark of its own for `who`; a suspension captures the
;;; mark with the frames, so after every `yield!` each task still reads
;;; its own value, though the two interleave.
(define-effect D (maxeff spin (read @q) (write @q) (alloc @q)
                         (read @m) (write @m)
                         (read (globals sched queue log yield! who worker))))
(define-type task (composable unit unit D @p))
(define sched (prompt-tag unit task D @p) (make-continuation-prompt-tag))
(define queue (ref (listof task @q) @q) (new nil))
(define log (ref (listof int @q) @q) (new nil))
(define who (mark-key int @m) (make-continuation-mark-key))

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

(define* worker (subr (maxeff D (goto @p) (comefrom @p)) (int) unit)
  (lambda (i)
    (if (= i 0)
        #u
        (begin (set log (cons (+ (first-mark who 0) i) (get log)))
               (yield!)
               (worker (- i 1))))))

(spawn! (lambda () (with-mark who 100 (lambda () (worker 3)))))
(spawn! (lambda () (with-mark who 200 (lambda () (worker 3)))))
(run!)
(the (listof int @q) (reverse (get log)))   ; (103 203 102 202 101 201)
