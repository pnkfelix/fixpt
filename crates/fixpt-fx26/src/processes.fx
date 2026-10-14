;; The scheduler of processes and `par` (`docs/fx26.md`, "Processes and
;; `par`"): a module file built in, which the forms `spawn`, `send`,
;; `receive`, `self`, `par`, `race`, `pselect`, `icell-get` and
;; `icell-put!` call, each through this file's one value, loaded once. The checkers give those
;; forms types of their own (`Checker::library_type`); the types written
;; here are this file's, in which a task may do anything (`any`): what a
;; program that loads this file itself sees, which lets it do nothing a
;; form could not.
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
  ;; Task `t` cancelled (a `race`'s loser), and whether it is: it ends
  ;; instead of running the next time it would, its places with it.
  (define cancel (subr sched (int) unit) (lambda (t) ((proj %sched int unit unit) 24 t #u)))
  (define cancelled? (subr sched (int) bool) (lambda (t) ((proj %sched int unit bool) 25 t #u)))
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
  ;; What resumes task `me` at `k`, as `me`; or, if it was cancelled, ends it.
  (define resumer (subr sched (int (composable unit unit sched @run)) thunk)
    (lambda (me k) (lambda () (if (cancelled? me) (task-end me) (begin (task-switch me) (k #u))))))
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
                (register (resumer me k))
                (task-switch 0)
                (abort-current-continuation tag #u))))
          tag))))
  ;; The first task, waiting until `ready` gives a place (0 or more): the
  ;; others run, one at a time until it does, and, when none can, the clock
  ;; is waited for, if a task waits for it; if nothing is left that could
  ;; make it so, the program is deadlocked, and `stuck` says on what.
  (define main-wait (subr any ((subr sched () int) string) int)
    (lambda (ready stuck)
      (letrec ((go (subr any () int)
                 (lambda ()
                   (let ((i (ready)))
                     (if (>= i 0)
                         i
                         (let ((t (pop)))
                           (cond ((procedure? t) (begin (run-task t) (go)))
                                 (((proj %sched unit unit bool) 21 #u #u) (go))
                                 (else (error stuck)))))))))
        (go))))
  ;; Wait until `ready?`, `register` handing over the waker. The first
  ;; task runs the others until then (`main-wait`).
  (define wait-until (subr any ((subr sched () bool) (subr sched (thunk) unit) string) unit)
    (lambda (ready? register stuck)
      (letrec ((go (subr any () unit)
                 (lambda ()
                   (cond ((ready?) #u)
                         ((main?) (begin (main-wait (lambda () (if (ready?) 0 -1)) stuck) #u))
                         (else (begin (suspend register) (go)))))))
        (go))))
  ;; Waker `w`, made to run at most once, however many wake it.
  (define once (subr sched (thunk) thunk)
    (lambda (w)
      (let ((fired (the (ref bool @sched) (new #f))))
        (lambda () (if (get fired) #u (begin (set fired #t) (w)))))))
  ;; A new task of `body`, runnable: its number. Cancelled before it
  ;; starts, it ends at once.
  (define fork (subr sched (thunk) int)
    (lambda (body)
      (let ((t (task-new)))
        (begin
          (push (lambda () (begin (task-switch t) (if (cancelled? t) #u (body)) (task-end t))))
          t))))
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
;; The process's own address: its mailbox, which others send to.
(define self (subr sched (mbox) mbox) (lambda (mb) mb))
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
;; it is ready, and how to give it a waker, which gives back how to take
;; the waker away again (`or-event` joins two).
(define-type undo (subr sched () unit))
(define-type event (listof (pairof (subr sched () bool) (subr sched (thunk) undo) @sched) @sched))
(define cell-event (poly ((r region)) (poly ((t type)) (subr sched ((icell t r)) event)))
  (plambda ((r region))
    (plambda ((t type))
      (lambda (c)
        (the event
          (list (cons (lambda () ((proj %sched (icell t r) unit bool) 10 c #u))
                      (lambda (w)
                        (begin ((proj %sched (icell t r) thunk unit) 11 c w)
                               (lambda () ((proj %sched (icell t r) thunk unit) 22 c w)))))))))))
(define mailbox-event (subr sched (mbox) event)
  (lambda (mb)
    (the event (list (cons (lambda () ((proj %sched mbox unit bool) 17 mb #u))
                           (lambda (w)
                             (begin ((proj %sched mbox thunk unit) 9 mb w)
                                    (lambda () ((proj %sched mbox thunk unit) 23 mb w)))))))))
;; Ready once the clock reaches `t`.
(define clock-event (subr sched (i64) event)
  (lambda (t)
    (the event (list (cons (lambda () ((proj %sched i64 unit bool) 19 t #u))
                           (lambda (w)
                             (begin ((proj %sched i64 thunk unit) 18 t w)
                                    (lambda () ((proj %sched thunk unit unit) 20 w #u)))))))))
(define or-event (subr sched (event event) event)
  (lambda (a b) (if (null? a) b (the event (cons (car a) (or-event (cdr a) b))))))
;; The first of `e`'s parts that is ready, by its place from `i`; -1 if none.
(define-rec
  (first-ready (subr sched (event int) int)
    (lambda (e i)
      (cond ((null? e) -1) (((car (car e))) i) (else (first-ready (cdr e) (+ i 1))))))
  ;; Waker `w` given to each of `e`'s parts, and how to take it from each.
  (give-all (subr sched (event thunk) (listof undo @sched))
    (lambda (e w) (if (null? e) nil (let ((u ((cdr (car e)) w))) (cons u (give-all (cdr e) w))))))
  (undo-all (subr sched ((listof undo @sched)) unit)
    (lambda (us) (if (null? us) #u (begin ((car us)) (undo-all (cdr us)))))))
;; What a `pselect` says when nothing can make any of its events ready.
(define stuck-select "a `pselect` whose events no task is left to make ready: a deadlock")
;; The place in `e` of a part that is ready, waiting for one: the first in
;; order of those ready when the task looks. The waker given to every part
;; runs once, the first time one of them is ready, and is then taken from
;; them all. The first task gives them one that does nothing, so that the
;; clock is waited for if one is a deadline (`main-wait`).
(define sync (subr any (event) int)
  (lambda (e)
    (letrec ((go (subr any () int)
               (lambda ()
                 (let ((i (first-ready e 0)))
                   (cond ((>= i 0) i)
                         ((main?)
                          (let* ((us (give-all e (lambda () #u)))
                                 (j (main-wait (lambda () (first-ready e 0)) stuck-select)))
                            (begin (undo-all us) j)))
                         (else
                          (let ((us (the (ref (listof undo @sched) @sched) (new nil))))
                            (begin (suspend (lambda (w) (set us (give-all e (once w)))))
                                   (undo-all (get us))
                                   (go)))))))))
      (go))))
;; `f` and `g`, each a task, and the value of the first to finish (`race`,
;; best effort): the other, cancelled, ends at its next wait, or before it
;; starts; one that computes without waiting runs to its end. Each
;; branch's `done` says it has finished, after which its task's number may
;; be another's, so it is not cancelled.
(define race2 (poly ((a type)) (subr any ((subr any () a) (subr any () a)) a))
  (plambda ((a type))
    (lambda (f g)
      (let* ((won (the (icell a @par) (make-icell)))
             (branch (lambda ((h (subr any () a)) (done (ref bool @sched)))
                       (lambda ()
                         (let ((v (h)))
                           (begin
                             (set done #t)
                             (if ((proj %sched (icell a @par) unit bool) 10 won #u)
                                 #u
                                 ((proj (proj fill @par) a) won v)))))))
             (d1 (the (ref bool @sched) (new #f)))
             (d2 (the (ref bool @sched) (new #f)))
             (t1 (fork (branch f d1)))
             (t2 (fork (branch g d2)))
             (v ((proj (proj await @par) a) won)))
        (begin
          (if (get d1) #u (cancel t1))
          (if (get d2) #u (cancel t2))
          v)))))
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
