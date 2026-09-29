;;; REJECTED, rightly: a task that opens an arena of its own and suspends
;;; inside it (`ping-pong.fx`'s scheduler). The suspension's `comefrom @p`
;;; would escape the `letrena`: the abort to `sched` ends the arena while
;;; the continuation that still uses `x` sits in the run queue.
(define-effect D (maxeff spin (read @q) (write @q) (alloc @q)
                         (read (globals sched queue log yield! holder))))
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

(define* holder (subr (maxeff D (goto @p) (comefrom @p)) () int)
  (lambda ()
    (letrena r
      (let ((x (the (ref int r) (rnew r 1))))
        (begin (yield!) (get x))))))
