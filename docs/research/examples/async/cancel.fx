;;; A cancel scope (trio's `CancelScope`), with `ping-pong.fx`'s scheduler.
;;; The scope is a prompt of a second tag, `scope`, inside the task, and a
;;; flag. `checkpoint!` suspends; when the task is resumed, it aborts to the
;;; scope if the flag is set, and it will again at every later checkpoint
;;; inside it (level-triggered). The captured continuation holds the
;;; scope's prompt, so the abort finds it after any number of suspensions.
(define-effect D (maxeff spin (read @q) (write @q) (alloc @q)
                         (goto @c) (comefrom @c)
                         (read (globals sched queue log yield! scope stop? checkpoint! ticker))))
(define-type task (composable unit unit D @p))
(define sched (prompt-tag unit task D @p) (make-continuation-prompt-tag))
(define queue (ref (listof task @q) @q) (new nil))
(define log (ref (listof int @q) @q) (new nil))
(define-type outcome (sumof (done int) (cancelled unit)))
(define scope (prompt-tag outcome unit (maxeff D (goto @p) (comefrom @p)) @c)
  (make-continuation-prompt-tag))
(define stop? (ref bool @q) (new #f))

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

(define* checkpoint! (subr (maxeff D (goto @p) (comefrom @p)) () unit)
  (lambda ()
    (begin (yield!)
           (if (get stop?) (abort-current-continuation scope #u) #u))))

(define* ticker (subr (maxeff D (goto @p) (comefrom @p)) (int) int)
  (lambda (i) (begin (set log (cons i (get log))) (checkpoint!) (ticker (+ i 1)))))

(spawn! (lambda ()
          (tagcase (prompt scope (sum done (ticker 0)) (lambda (u) (sum cancelled u)))
            (done n (set log (cons n (get log))))
            (cancelled u (set log (cons -1 (get log)))))))
(spawn! (lambda () (begin (yield!) (yield!) (set stop? #t))))
(run!)
(the (listof int @q) (reverse (get log)))   ; (0 1 2 -1)
