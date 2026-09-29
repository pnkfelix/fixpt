;;; `asyncio.run` as masking: the ping-pong of `ping-pong.fx`, with the
;;; tag, the run queue and the log made inside one procedure. Nothing
;;; outside names @s, so the checker masks every effect on it, the control
;;; effects included: `interleave` says only `spin` and what it does to @l.
(define-effect L (maxeff spin (read @s) (write @s) (alloc @s) (alloc @l)))
(define-type ltask (composable unit unit L @s))

(define interleave (subr (maxeff spin (alloc @l) (read @l)) (int) (listof int @l))
  (lambda (n)
    (let* ((sched (the (prompt-tag unit ltask L @s) (make-continuation-prompt-tag)))
           (queue (the (ref (listof ltask @s) @s) (new nil)))
           (log (the (ref (listof int @l) @s) (new nil)))
           (yield! (the (subr (maxeff (goto @s) (comefrom @s)) () unit)
                     (lambda ()
                       (call-with-composable-continuation
                         (lambda (k) (abort-current-continuation sched k))
                         sched))))
           (enqueue! (lambda ((k ltask))
                       (let ((back (the (listof ltask @s) (reverse (get queue)))))
                         (set queue (reverse (the (listof ltask @s) (cons k back))))))))
      (letrec ((pinger (subr (maxeff L (goto @s) (comefrom @s)) (int int) unit)
                 (lambda (who i)
                   (if (= i 0)
                       #u
                       (begin (set log (cons (+ who i) (get log)))
                              (yield!)
                              (pinger who (- i 1))))))
               (run! (subr (maxeff L (goto @s) (comefrom @s)) () unit)
                 (lambda ()
                   (let ((q (get queue)))
                     (if (null? q)
                         #u
                         (begin (set queue (cdr q))
                                (prompt sched ((car q) #u) (lambda (k) (enqueue! k)))
                                (run!)))))))
        (begin
          (prompt sched (pinger 100 n) (lambda (k) (enqueue! k)))
          (prompt sched (pinger 200 n) (lambda (k) (enqueue! k)))
          (run!)
          (the (listof int @l) (reverse (get log))))))))

(interleave 3)   ; (103 203 102 202 101 201)
