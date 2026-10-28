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
  ;; A monitored group's failure handler (a process's, a `race` branch's),
  ;; and a failure, as the runtime keeps it: its message, and the handler.
  (define-type handler (subr any (string) unit))
  (define-type failure (union false (pairof string handler @sched)))
  (define task-new (subr sched () int) (lambda () ((proj %sched unit unit int) 0 #u #u)))
  (define task-switch (subr sched (int) int) (lambda (t) ((proj %sched int unit int) 1 t #u)))
  (define task-end (subr sched (int) unit) (lambda (t) ((proj %sched int unit unit) 2 t #u)))
  (define task-current (subr sched () int) (lambda () ((proj %sched unit unit int) 3 #u #u)))
  ;; How a task that waits stops waiting: its waker taken back.
  (define-type stop (subr sched () unit))
  (define-type stops (listof (pairof int stop @sched) @sched))
  ;; Each cancelled task that waits, ended now, its waker taken back (42),
  ;; so that none is left waiting for what may never come. Not preempted
  ;; meanwhile (33, 32): a waker that fired already would run its task's
  ;; resumer between, which would end the task first.
  (define reap (subr sched () unit)
    (lambda ()
      (letrec ((go (subr sched (stops) unit)
                 (lambda (ws)
                   (if (null? ws)
                       #u
                       (begin ((cdr (car ws))) (task-end (car (car ws))) (go (cdr ws)))))))
        (begin
          ((proj %sched unit unit unit) 33 #u #u)
          (go ((proj %sched unit unit stops) 42 #u #u))
          ((proj %sched unit unit unit) 32 #u #u)))))
  ;; Task `t` cancelled (a `race`'s loser), and whether it is: it ends
  ;; instead of running the next time it would, its places with it; at
  ;; once, if it waits.
  (define cancel (subr sched (int) unit)
    (lambda (t) (begin ((proj %sched int unit unit) 24 t #u) (reap))))
  (define cancelled? (subr sched (int) bool) (lambda (t) ((proj %sched int unit bool) 25 t #u)))
  (define main? (subr sched () bool) (lambda () (= (task-current) 0)))
  (define push (subr sched (thunk) unit) (lambda (t) ((proj %sched thunk unit unit) 4 t #u)))
  (define pop (subr sched () (union false thunk))
    (lambda () ((proj %sched unit unit (union false thunk)) 5 #u #u)))
  ;; The scheduler's prompt tag, made the first time.
  (define the-tag (subr sched () tag)
    (lambda ()
      (tagcase ((proj %sched unit unit (oneof (some tag) (none unit))) 12 #u #u)
        (some t t)
        (none u (let ((t (the tag (make-continuation-prompt-tag))))
                  (begin ((proj %sched tag unit unit) 13 t #u) t))))))
  ;; Task `t`, run under the scheduler's prompt, until it ends, waits, or
  ;; is preempted; the runtime told, so that the first task is not
  ;; preempted meanwhile (`fixpt_runtime::sched::preempt_due`).
  ;; A task of a monitored group that fails aborts to the prompt, the
  ;; failure kept (`sched::task_failed`): its handler called here with the
  ;; message, before the first task may be preempted again.
  (define run-task (subr any (thunk) unit)
    (lambda (t)
      (begin
        ((proj %sched int unit unit) 29 1 #u)
        (prompt (the-tag) (t) (lambda ((u unit)) u))
        (let ((f ((proj %sched unit unit failure) 37 #u #u)))
          (if (pair? f) (begin ((cdr f) (car f)) (reap)) #u))
        ((proj %sched int unit unit) 29 -1 #u))))
  ;; Every task that can run, run, until none can.
  (define drain (subr any () unit)
    (lambda ()
      (letrec ((go (subr any () unit)
                 (lambda ()
                   (let ((t (pop))) (if (procedure? t) (begin (run-task t) (go)) #u)))))
        (go))))
  ;; Drained, if the first task asks.
  (define settle (subr any () unit) (lambda () (if (main?) (drain) #u)))
  ;; What resumes task `me` at `k`, as `me`, waiting no more (41); or, if
  ;; it was cancelled, ends it; or nothing, if it was ended already (`reap`,
  ;; `alive` cleared), its number perhaps another task's now. `k` is
  ;; one-shot (`TODO.md` §98): a task is resumed once from each wait.
  (define resumer (subr sched (int (oneshot unit unit sched @run) (ref bool @sched)) thunk)
    (lambda (me k alive)
      (lambda ()
        (if (get alive)
            (begin
              ((proj %sched int unit unit) 41 me #u)
              (if (cancelled? me) (task-end me) (begin (task-switch me) (k #u))))
            #u))))
  ;; The current task waits: the rest of it, captured, is handed to
  ;; `register` as a thunk that resumes it, as this task, and the scheduler
  ;; goes on; how to take that back, kept, should it be cancelled (40).
  ;; Made the first task first, so that the abort ends none of this task's
  ;; places. Not preempted from the capture until resumed (33, 32): a
  ;; preemption between would leave two ways to resume it.
  (define suspend (subr any ((subr sched (thunk) stop)) unit)
    (lambda (register)
      (let ((tag (the-tag)))
        (begin
          ((proj %sched unit unit unit) 33 #u #u)
          (call-with-oneshot-continuation
            (lambda ((k (oneshot unit unit sched @run)))
              (let* ((me (task-current))
                     (alive (the (ref bool @sched) (new #t)))
                     (undo (register (resumer me k alive))))
                (begin
                  ((proj %sched int stop unit) 40 me (lambda () (begin (set alive #f) (undo))))
                  (task-switch 0)
                  (abort-current-continuation tag #u))))
            tag)
          ((proj %sched unit unit unit) 32 #u #u)))))
  ;; The next task to run, or, with none, the oldest parked.
  (define pop-any (subr sched () (union false thunk))
    (lambda () ((proj %sched unit unit (union false thunk)) 28 #u #u)))
  ;; What a machine calls at a poll whose time slice is spent, when another
  ;; task could run (`preempt_due`): a task parks itself, resumable, and the
  ;; scheduler goes on; the first task fires the deadlines due and runs one
  ;; other task, the oldest queued, else the oldest parked. Parked tasks are
  ;; apart from the queue, so that `drain` ends: they run when the first
  ;; task waits or is preempted.
  ;; Until the call has returned, the runtime preempts the task no more:
  ;; the machine that called it says so (`sched::preempt_done`).
  (define preempt (subr any () unit)
    (lambda ()
      (if (main?)
          (begin
            ((proj %sched unit unit bool) 30 #u #u)
            (let ((t (pop-any))) (if (procedure? t) (run-task t) #u)))
          (suspend (lambda (w) (begin ((proj %sched thunk unit unit) 27 w #u) (lambda () #u)))))))
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
                         (let ((t (pop-any)))
                           (cond ((procedure? t) (begin (run-task t) (go)))
                                 (((proj %sched unit unit bool) 21 #u #u) (go))
                                 ;; Preempted since it looked, it may have
                                 ;; run the task that made it so.
                                 ((>= (ready) 0) (go))
                                 (else (error stuck)))))))))
        (go))))
  ;; Wait until `ready?`, `register` handing over the waker. The first
  ;; task runs the others until then (`main-wait`).
  (define wait-until (subr any ((subr sched () bool) (subr sched (thunk) stop) string) unit)
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
  ;; A new task of `body`, runnable: its number, given to `first` before
  ;; it can run. Cancelled before it starts, it ends at once.
  (define fork-as (subr sched (thunk (subr sched (int) unit)) int)
    (lambda (body first)
      (let ((t (task-new)))
        (begin
          ((proj %sched (subr any () unit) unit unit) 26 preempt #u)
          (first t)
          (push (lambda () (begin (task-switch t) (if (cancelled? t) #u (body)) (task-end t))))
          t))))
  (define fork (subr sched (thunk) int) (lambda (body) (fork-as body (lambda (t) #u))))
  ;; The first task of a monitored group, whose failure `h` handles (35).
  (define fork-group (subr sched (thunk handler) int)
    (lambda (body h) (fork-as body (lambda (t) ((proj %sched int handler unit) 35 t h)))))
  ;; The same for a `race` branch, whose group is inside the current task's:
  ;; should that one fail, the branch is cancelled with it (39).
  (define fork-race-branch (subr sched (thunk handler) int)
    (lambda (body h) (fork-as body (lambda (t) ((proj %sched int handler unit) 39 t h)))))
  ;; A branch of the current task (`par`, `race`): of its process's group,
  ;; if it is monitored, so that the branch's failure is the process's.
  (define fork-branch (subr sched (thunk) int)
    (lambda (body) (fork-as body (lambda (t) ((proj %sched int unit unit) 36 t #u)))))
  ;; The value of I-cell `c`, once it has one.
  (define await (poly ((r region)) (poly ((t type)) (subr any ((icell t r)) t)))
    (plambda ((r region))
      (plambda ((t type))
        (lambda (c)
          (begin
            (wait-until (lambda () ((proj %sched (icell t r) unit bool) 10 c #u))
                        (lambda (w)
                          (begin ((proj %sched (icell t r) thunk unit) 11 c w)
                                 (lambda () ((proj %sched (icell t r) thunk unit) 22 c w))))
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
;; A process's body, as `spawn` makes it, and the task that runs it with
;; mailbox `mb` and a reap of its own.
(define-type process-body (poly ((r place)) (subr any (mbox (place r)) unit)))
(define process-task (subr sched (process-body mbox) thunk)
  (lambda (body mb)
    (lambda () ((proj body heap) mb ((proj %sched unit unit (place heap)) 16 #u #u)))))
;; A process of `body`, as `spawn-process` makes one, monitored: should it
;; fail, `watcher` is sent `(on-fail message)` instead of the form failing
;; (`docs/fx26.md`, "Monitors"), the monitor set (35) before it can run.
(define spawn-monitored
  (poly ((w type)) (subr any (mbox (subr any (string) w) process-body) mbox))
  (plambda ((w type))
    (lambda (watcher on-fail body)
      (let ((mb ((proj %sched unit unit mbox) 6 #u #u)))
        (begin
          (fork-group (process-task body mb)
                      (lambda ((m string)) ((proj %sched mbox w unit) 7 watcher (on-fail m))))
          (settle)
          mb)))))
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
                    (lambda (w)
                      (begin ((proj %sched mbox thunk unit) 9 mb w)
                             (lambda () ((proj %sched mbox thunk unit) 23 mb w))))
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
;; Ready once a read of the standard input would not wait: a byte has
;; come, or it is at its end (43-45; `TODO.md` §95). Its operand is unit,
;; as a `pselect` arm `((read-byte) b body …)` has none.
(define stdin-event (subr sched (unit) event)
  (lambda (u)
    (the event (list (cons (lambda () ((proj %sched unit unit bool) 43 #u #u))
                           (lambda (w)
                             (begin ((proj %sched thunk unit unit) 44 w #u)
                                    (lambda () ((proj %sched thunk unit unit) 45 w #u)))))))))
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
                            (begin (suspend (lambda (w)
                                              (begin (set us (give-all e (once w)))
                                                     (lambda () (undo-all (get us))))))
                                   (undo-all (get us))
                                   (go)))))))))
      (go))))
;; How a `race` came out: a branch's value, or, every branch failed, the
;; last failure's message.
(define-type (outcome (a type)) (oneof (won a) (lost string)))
;; Cell `c` given `o`, if it has no value yet, in one step (34).
(define-type (outcomes (a type) (r region)) (icell (outcome a) r))
(define offer-outcome
  (poly ((r region)) (poly ((a type)) (subr sched ((outcomes a r) (outcome a)) unit)))
  (plambda ((r region))
    (plambda ((a type)) (lambda (c o) ((proj %sched (outcomes a r) (outcome a) unit) 34 c o)))))
;; `f` and `g`, each a task, and the value of the first to finish (`race`,
;; best effort): the other, cancelled, ends at once if it waits (`reap`),
;; else at its next wait, or when it is next preempted, or before it
;; starts. A branch that fails is lost, a monitored group of its own
;; (`fork-race-branch`), inside the current task's, which cancels it should
;; it fail; if both are, the race fails as the last did. Each branch's
;; `done` says it has finished or failed, after which its task's number
;; may be another's, so it is not cancelled.
(define race2 (poly ((a type)) (subr any ((subr any () a) (subr any () a)) a))
  (plambda ((a type))
    (lambda (f g)
      (let* ((res (the (icell (outcome a) @par) (make-icell)))
             (lost (the (ref int @sched) (new 0)))
             (offer (lambda ((o (outcome a))) ((proj (proj offer-outcome @par) a) res o)))
             (branch (lambda ((h (subr any () a)) (done (ref bool @sched)))
                       (lambda () (let ((v (h))) (begin (set done #t) (offer (one won v)))))))
             (loser (lambda ((done (ref bool @sched)))
                      (lambda ((m string))
                        (begin
                          (set done #t)
                          (set lost (+ (get lost) 1))
                          (if (= (get lost) 2) (offer (one lost m)) #u)))))
             (d1 (the (ref bool @sched) (new #f)))
             (d2 (the (ref bool @sched) (new #f)))
             (t1 (fork-race-branch (branch f d1) (loser d1)))
             (t2 (fork-race-branch (branch g d2) (loser d2)))
             (r ((proj (proj await @par) (outcome a)) res)))
        (begin
          (if (get d1) #u (cancel t1))
          (if (get d2) #u (cancel t2))
          (tagcase r (won v v) (lost m (error m))))))))
;; `f` and `g`, each a task, and both their values.
(define par2
  (poly ((a type) (b type))
    (subr any ((subr any () a) (subr any () b)) (tupof (1 a) (2 b))))
  (plambda ((a type) (b type))
    (lambda (f g)
      (let ((ca (the (icell a @par) (make-icell))) (cb (the (icell b @par) (make-icell))))
        (begin
          (fork-branch (lambda () ((proj (proj fill @par) a) ca (f))))
          (fork-branch (lambda () ((proj (proj fill @par) b) cb (g))))
          (tup (1 ((proj (proj await @par) a) ca)) (2 ((proj (proj await @par) b) cb))))))))
;; `f`'s value, `f` a task, a monitored group as a `race` branch is; should
;; it fail, `(h message)` instead (`attempt`; Heist's, `FIXPT-CHANGES.md`
;; F1). `f` is cancellable, so a failure half way leaves nothing another
;; could see; `h` runs in the current task, after.
(define attempt1 (poly ((a type)) (subr any ((subr any () a) (subr any (string) a)) a))
  (plambda ((a type))
    (lambda (f h)
      (let* ((res (the (icell (outcome a) @par) (make-icell)))
             (offer (lambda ((o (outcome a))) ((proj (proj offer-outcome @par) a) res o))))
        (begin
          (fork-race-branch (lambda () (offer (one won (f))))
                            (lambda ((m string)) (offer (one lost m))))
          (tagcase ((proj (proj await @par) (outcome a)) res)
            (won v v)
            (lost m (h m))))))))
