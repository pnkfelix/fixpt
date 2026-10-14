;; The scheduler of processes and `par` (`docs/fx26.md`, "Processes and
;; `par`"): a module file built in, which the forms `spawn`, `send`,
;; `receive`, `par`, `icell-get` and `icell-put!` call, each through this
;; file's one value, loaded once. The checkers give those forms types of their own
;; (`Checker::library_type`); the types written here are this file's, in
;; which a task may do anything (`any`): what a program that loads this
;; file itself sees, which lets it do nothing a form could not.
;;
;; A task is a thunk the scheduler runs under its prompt (`run-task`). It
;; waits by capturing the rest of itself up to the prompt, handing a thunk
;; that resumes it to what it waits for, and aborting (`suspend`). Only the
;; first task, the program's own, runs the scheduler (`drain`): when it
;; waits, and after each `spawn`, `send` or `icell-put!` it makes, so that
;; whatever can run has run before the form that made it so ends. Each
;; task has a stack of places of its own (`fixpt_heap`'s tasks), and the
;; scheduler runs as the first. The runtime's part is `%sched`'s
;; operations (`fixpt_runtime::sched`), by number.
(hide
  (define-effect sched (maxeff (read @sched) (write @sched) (alloc @sched) (alloc @run) spin))
  (define-effect any (maxeff sched (goto @run) (comefrom @run)))
  (define-type thunk (subr any () unit))
  (define-type tag (prompt-tag unit unit sched @run))
  ;; A mailbox, as the runtime makes it; nothing here looks inside.
  (define-type mbox (ref unit @sched))
  (define task-new (subr sched () int) (lambda () ((proj %sched unit unit int) 0 #u #u)))
  (define task-switch (subr sched (int) int) (lambda (t) ((proj %sched int unit int) 1 t #u)))
  (define task-end (subr sched (int) unit) (lambda (t) ((proj %sched int unit unit) 2 t #u)))
  (define task-current (subr sched () int) (lambda () ((proj %sched unit unit int) 3 #u #u)))
  (define main? (subr sched () bool) (lambda () (= (task-current) 0)))
  (define push (subr sched (thunk) unit) (lambda (t) ((proj %sched thunk unit unit) 4 t #u)))
  (define pop (subr sched () (union false thunk))
    (lambda () ((proj %sched unit unit (union false thunk)) 5 #u #u)))
  ;; The scheduler's prompt tag, made the first time.
  (define the-tag (subr sched () tag)
    (lambda ()
      (tagcase ((proj %sched unit unit (sumof (some tag) (none unit))) 12 #u #u)
        (some t t)
        (none u (let ((t (the tag (make-continuation-prompt-tag))))
                  (begin ((proj %sched tag unit unit) 13 t #u) t))))))
  ;; Task `t`, run under the scheduler's prompt, until it ends or waits.
  (define run-task (subr any (thunk) unit)
    (lambda (t) (prompt (the-tag) (t) (lambda ((u unit)) u))))
  ;; Every task that can run, run, until none can.
  (define drain (subr any () unit)
    (lambda ()
      (letrec ((go (subr any () unit)
                 (lambda ()
                   (let ((t (pop))) (if (procedure? t) (begin (run-task t) (go)) #u)))))
        (go))))
  ;; Drained, if the first task asks.
  (define settle (subr any () unit) (lambda () (if (main?) (drain) #u)))
  ;; The current task waits: the rest of it, captured, is handed to
  ;; `register` as a thunk that resumes it, as this task, and the scheduler
  ;; goes on. Made the first task first, so that the abort ends none of
  ;; this task's places.
  (define suspend (subr any ((subr sched (thunk) unit)) unit)
    (lambda (register)
      (let ((tag (the-tag)))
        (call-with-composable-continuation
          (lambda ((k (composable unit unit sched @run)))
            (let ((me (task-current)))
              (begin
                (register (lambda () (begin (task-switch me) (k #u))))
                (task-switch 0)
                (abort-current-continuation tag #u))))
          tag))))
  ;; Wait until `ready?`, `register` handing over the waker. The first
  ;; task runs the others until then; if none can make it so, the program
  ;; is deadlocked, and `stuck` says on what.
  (define wait-until (subr any ((subr sched () bool) (subr sched (thunk) unit) string) unit)
    (lambda (ready? register stuck)
      (letrec ((go (subr any () unit)
                 (lambda ()
                   (cond ((ready?) #u)
                         ((main?) (begin (drain) (if (ready?) #u (error stuck))))
                         (else (begin (suspend register) (go)))))))
        (go))))
  ;; Waker `w`, made to run at most once, however many wake it.
  (define once (subr sched (thunk) thunk)
    (lambda (w)
      (let ((fired (the (ref bool @sched) (new #f))))
        (lambda () (if (get fired) #u (begin (set fired #t) (w)))))))
  ;; A new task of `body`, runnable.
  (define fork (subr sched (thunk) unit)
    (lambda (body)
      (let ((t (task-new)))
        (push (lambda () (begin (task-switch t) (body) (task-end t)))))))
  ;; The value of I-cell `c`, once it has one.
  (define await (poly ((r region)) (poly ((t type)) (subr any ((icell t r)) t)))
    (plambda ((r region))
      (plambda ((t type))
        (lambda (c)
          (begin
            (wait-until (lambda () ((proj %sched (icell t r) unit bool) 10 c #u))
                        (lambda (w) ((proj %sched (icell t r) thunk unit) 11 c w))
                        (string-append "an i-cell read before it was written, "
                                       "and no task is left to write it: a deadlock"))
            ((proj %sched (icell t r) unit t) 15 c #u))))))
  ;; I-cell `c` given `v`; whoever waits for it may run.
  (define fill (poly ((r region)) (poly ((t type)) (subr sched ((icell t r) t) unit)))
    (plambda ((r region))
      (plambda ((t type)) (lambda (c v) ((proj %sched (icell t r) t unit) 14 c v))))))

;; A process of `body`: a new task, which runs `body` with a mailbox of its
;; own and a reap of its own, its place, until it ends.
(define spawn-process (subr any ((poly ((r place)) (subr any (mbox (place r)) unit))) mbox)
  (lambda (body)
    (let ((mb ((proj %sched unit unit mbox) 6 #u #u)))
      (begin
        (fork (lambda () ((proj body heap) mb ((proj %sched unit unit (place heap)) 16 #u #u))))
        (settle)
        mb))))
;; Message `v` to the mailbox `mb`, a copy of it.
(define send (poly ((m type)) (subr any (mbox m) unit))
  (plambda ((m type))
    (lambda (mb v) (begin ((proj %sched mbox m unit) 7 mb v) (settle)))))
;; The oldest message in `mb`, once there is one.
(define receive (poly ((m type)) (subr any (mbox) m))
  (plambda ((m type))
    (lambda (mb)
      (begin
        (wait-until (lambda () ((proj %sched mbox unit bool) 17 mb #u))
                    (lambda (w) ((proj %sched mbox thunk unit) 9 mb w))
                    "a message no task is left to send: a deadlock")
        ((proj %sched mbox unit m) 8 mb #u)))))
(define icell-get await)
(define icell-put! (poly ((r region)) (poly ((t type)) (subr any ((icell t r) t) unit)))
  (plambda ((r region))
    (plambda ((t type)) (lambda (c v) (begin ((proj (proj fill r) t) c v) (settle))))))
;; An event, what `pselect` waits for: each of its parts, in order, whether
;; it is ready, and how to give it a waker (`or-event` joins two).
(define-type event (listof (pairof (subr sched () bool) (subr sched (thunk) unit) @sched) @sched))
(define cell-event (poly ((r region)) (poly ((t type)) (subr sched ((icell t r)) event)))
  (plambda ((r region))
    (plambda ((t type))
      (lambda (c)
        (the event (list (cons (lambda () ((proj %sched (icell t r) unit bool) 10 c #u))
                               (lambda (w) ((proj %sched (icell t r) thunk unit) 11 c w)))))))))
(define mailbox-event (subr sched (mbox) event)
  (lambda (mb)
    (the event (list (cons (lambda () ((proj %sched mbox unit bool) 17 mb #u))
                           (lambda (w) ((proj %sched mbox thunk unit) 9 mb w)))))))
(define or-event (subr sched (event event) event)
  (lambda (a b) (if (null? a) b (the event (cons (car a) (or-event (cdr a) b))))))
;; The first of `e`'s parts that is ready, by its place from `i`; -1 if none.
(define-rec
  (first-ready (subr sched (event int) int)
    (lambda (e i)
      (cond ((null? e) -1) (((car (car e))) i) (else (first-ready (cdr e) (+ i 1))))))
  ;; Waker `w` given to each of `e`'s parts.
  (give-all (subr sched (event thunk) unit)
    (lambda (e w) (if (null? e) #u (begin ((cdr (car e)) w) (give-all (cdr e) w))))))
;; What a `pselect` says when nothing can make any of its events ready.
(define stuck-select "a `pselect` whose events no task is left to make ready: a deadlock")
;; The place in `e` of a part that is ready, waiting for one: the first in
;; order of those ready when the task looks. The waker given to every part
;; runs once, the first time one of them is ready; the rest do nothing.
(define sync (subr any (event) int)
  (lambda (e)
    (letrec ((go (subr any () int)
               (lambda ()
                 (let ((i (first-ready e 0)))
                   (cond ((>= i 0) i)
                         ((main?)
                          (begin (drain)
                                 (let ((j (first-ready e 0)))
                                   (if (>= j 0) j (error stuck-select)))))
                         (else (begin (suspend (lambda (w) (give-all e (once w)))) (go))))))))
      (go))))
;; `f` and `g`, each a task, and both their values.
(define par2
  (poly ((a type) (b type))
    (subr any ((subr any () a) (subr any () b)) (productof (1 a) (2 b))))
  (plambda ((a type) (b type))
    (lambda (f g)
      (let ((ca (the (icell a @par) (make-icell))) (cb (the (icell b @par) (make-icell))))
        (begin
          (fork (lambda () ((proj (proj fill @par) a) ca (f))))
          (fork (lambda () ((proj (proj fill @par) b) cb (g))))
          (product (1 ((proj (proj await @par) a) ca)) (2 ((proj (proj await @par) b) cb))))))))
