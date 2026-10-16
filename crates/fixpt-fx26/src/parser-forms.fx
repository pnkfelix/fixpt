;;; The forms of processes and `par` (`docs/fx26.md`, "Processes"), as the
;;; Rust parser's `parse_process_form` expands them, into syntax the parser
;;; then parses (`parser-exps.fx`): each a call of a procedure of the
;;; scheduler's, `fx26:processes.fx`, through `lib`, the hidden global of
;;; its load.
;;; - `(spawn (box M r) body …)`: `((with lib spawn-process) (plambda ((r
;;;   place)) (lambda ((box (inbox M r)) (r (place r))) body … #u)))`;
;;; - `(send a v)`, `(receive box)`, `(self box)`, `(icell-get c)`,
;;;   `(icell-put! c v)`: `((with lib name) …)`;
;;; - `(par ((x1 e1) … (xn en)) body …)`: `par2` of the first branch and
;;;   the `par` of the rest, as thunks, the parts bound by `let`;
;;; - `(pselect (W x body …) …)`: `sync` of its arms' events, and the arm
;;;   of the one ready (`select-form`).
(module-parameters ((rs region) (re region) (rm region) (rc region) (rp region)))
(define parser-module ((proj (load-module "fx26:parser.fx") rs re rm rc rp)))
(define reader-types (with parser-module reader-types))
(import reader-types atom (type syn))
(import parser-module syn-symbol? syn-head syn-start syn-end len nth drop (type syns-a exp)
        (effect parses))

;; How a form here fails: the caller's `pfail-at`, as this file's instance
;; of `parser.fx` is not the caller's, and its prompt tag no prompt's.
(define-type fails (subr parses (string int int) void))
;; `items` as long as `n`, or at least `n`; else `shape` said, through `fail`.
(define arity (subr parses (fails syns-a int string int int) unit)
  (lambda (fail items n shape a b) (if (= (len items) n) #u (fail shape a b))))
(define at-least (subr parses (fails syns-a int string int int) unit)
  (lambda (fail items n shape a b) (if (< (len items) n) (fail shape a b) #u)))
;; `message`, said of `s`, through `fail`.
(define fail-at-syn (subr parses (fails string syn) void)
  (lambda (fail message s) (fail message (syn-start s) (syn-end s))))
(import parser-module mk-symbol mk-list mk-int)

;; The scheduler's module file, which each form loads.
(define processes string "fx26:processes.fx")
;; Form `items`, as a call through the scheduler's load,
;; `load` (its hidden global), at `a`..`b`.
(define process-form (subr (maxeff parses spin) (fails syns-a exp int int) syn)
  (lambda (fail items load a b)
    (let* ((lib (tagcase load (e-var (n c d cdk) n) (else y '%none)))
           (call (lambda ((name string) (args syns-a))
                  (mk-list (cons (mk-list (the syns-a (list (mk-symbol "with" a b) (atom lib a b)
                                                            (mk-symbol name a b)))
                                          a b)
                                 args)
                           a b)))
           ;; `(name x …)`, of `n` items, said as `shape`.
           (fixed (lambda ((n int) (shape string) (name string))
                    (begin (arity fail items n shape a b) (call name (cdr items))))))
      (case (syn-head (car items))
        ((send) (fixed 3 "`(send address message)`" "send"))
        ((receive) (fixed 2 "`(receive mailbox)`" "receive"))
        ((self) (fixed 2 "`(self mailbox)`" "self"))
        ((icell-get) (fixed 2 "`(icell-get i-cell)`" "icell-get"))
        ((icell-put!) (fixed 3 "`(icell-put! i-cell value)`" "icell-put!"))
        ((spawn) (call "spawn-process" (the syns-a (list (spawn-body fail items a b)))))
        ((spawn-monitored) (spawn-monitored-form fail items call a b))
        ((pselect) (select-form fail items lib a b))
        ((race) (race-form fail items lib a b))
        (else (par-form fail items lib a b))))))

;; How `process-form` makes a call of the scheduler's procedure, by name.
(define-type calls (subr (maxeff parses spin) (string syns-a) syn))
;; `(spawn-monitored w f (box M r) body …)`: `((with lib spawn-monitored) w
;; f (plambda …))`, the body as `spawn`'s (`spawn-body`).
(define spawn-monitored-form (subr (maxeff parses spin) (fails syns-a calls int int) syn)
  (lambda (fail items call a b)
    (let ((usage "`(spawn-monitored watcher on-failure (mailbox message-type place) body …)`"))
      (begin
        (at-least fail items 5 usage a b)
        (call "spawn-monitored"
              (the syns-a (list (nth items 1) (nth items 2)
                                (spawn-body fail (cons (car items) (drop items 3)) a b))))))))
;; `(x y)`, at `a`..`b`.
(define pair-syn (subr (maxeff (read @globals) (read rs)) (syn syn int int) syn)
  (lambda (x y a b) (mk-list (the syns-a (list x y)) a b)))
;; A list's items, or none.
(define items-of (subr (read @globals) (syn) syns-a)
  (lambda (s) (tagcase s (lst (xs d c e) xs) (else y nil))))

;; `(spawn (box M r) body …)`'s body: `(plambda ((r place)) (lambda ((box
;; (inbox M r)) (r (place r))) body … #u))`.
(define spawn-body (subr (maxeff parses spin) (fails syns-a int int) syn)
  (lambda (fail items a b)
    (let ((usage "`(spawn (mailbox message-type place) body …)`"))
      (begin
        (at-least fail items 3 usage a b)
        (let ((h (items-of (nth items 1))))
          (if (and (= (len h) 3) (syn-symbol? (car h)) (syn-symbol? (nth h 2)))
              (let* ((r (nth h 2))
                     (place (mk-symbol "place" a b))
                     (inbox-t (mk-list (the syns-a (list (mk-symbol "inbox" a b) (nth h 1) r)) a b))
                     (place-t (mk-list (the syns-a (list place r)) a b))
                     (params (mk-list (the syns-a (list (pair-syn (car h) inbox-t a b)
                                                        (pair-syn r place-t a b)))
                                      a b))
                     (body (snoc (drop items 2) (mk-symbol "#u" a b)))
                     (lam (mk-list (cons (mk-symbol "lambda" a b) (cons params body)) a b))
                     (binder (mk-list (the syns-a (list (pair-syn r place a b))) a b)))
                (mk-list (the syns-a (list (mk-symbol "plambda" a b) binder lam)) a b))
              (fail usage a b)))))))
(define snoc (subr (maxeff (read @globals) (read rs)) (syns-a syn) syns-a)
  (lambda (xs x) (if (null? xs) (the syns-a (list x)) (cons (car xs) (snoc (cdr xs) x)))))

;; `(par ((x1 e1) … (xn en)) body …)`: `(let ((%par tree)) (let ((x1
;; (extract %par 1)) (%par (extract %par 2))) … (let ((xn-1 (extract %par
;; 1)) (xn (extract %par 2))) body …)))`, `tree` the branches as nested
;; `par2`s (`par-tree`). What is made for a binding (its thunk, its
;; `extract`s) is at the binding; the rest at the form (the Rust parser's
;; `par_expansion`).
(define par-form (subr (maxeff parses spin) (fails syns-a symbol int int) syn)
  (lambda (fail items lib a b)
    (let ((usage "`(par ((name expression) …) body …)`"))
      (begin
        (at-least fail items 3 usage a b)
        (let ((bs (tagcase (nth items 1) (lst (xs d c e) xs) (else y (fail usage a b)))))
          (begin
            (par-check fail bs)
            (if (< (len bs) 2) (fail par-two a b) #u)
            (let* ((p (mk-symbol "%par" a b))
                   (first (mk-list (the syns-a (list (pair-syn p (par-tree bs lib a b) a b))) a b))
                   (lets (par-lets bs p (drop items 2) a b)))
              (mk-list (the syns-a (list (mk-symbol "let" a b) first lets)) a b))))))))
;; What `par` is short of, said.
(define par-two string "`par` runs two branches or more: `(par ((name expression) …) body …)`")
;; Each binding `(name expression)`.
(define par-check (subr parses (fails syns-a) unit)
  (lambda (fail bs)
    (if (null? bs)
        #u
        (let ((x (items-of (car bs))))
          (if (and (= (len x) 2) (syn-symbol? (car x)))
              (par-check fail (cdr bs))
              (fail-at-syn fail "a `par` binding is `(name expression)`" (car bs)))))))
;; A binding's name, and its expression.
(define par-name (subr parses (syn) syn) (lambda (bnd) (car (items-of bnd))))
(define par-exp (subr parses (syn) syn) (lambda (bnd) (nth (items-of bnd) 1)))
;; The branches of `bs` as `((with lib par2) (lambda () e1) rest)`, `rest`
;; the thunk of the last's expression, or of the rest's tree.
(define par-tree (subr (maxeff parses spin) (syns-a symbol int int) syn)
  (lambda (bs lib a b)
    (let* ((bnd (car bs)) (sa (syn-start bnd)) (sb (syn-end bnd)))
      (if (null? (cdr bs))
          (thunk-syn (par-exp bnd) sa sb)
          (let* ((op (mk-list (the syns-a (list (mk-symbol "with" a b) (atom lib a b)
                                                (mk-symbol "par2" a b)))
                              a b))
                 (rest (if (null? (cdr (cdr bs)))
                           (par-tree (cdr bs) lib a b)
                           (thunk-syn (par-tree (cdr bs) lib a b) a b))))
            (mk-list (the syns-a (list op (thunk-syn (par-exp bnd) sa sb) rest)) a b))))))
;; `(lambda () x)`, at `a`..`b`.
(define thunk-syn (subr (maxeff (read @globals) (read rs)) (syn int int) syn)
  (lambda (x a b) (mk-list (the syns-a (list (mk-symbol "lambda" a b) (mk-list nil a b) x)) a b)))
;; `(extract p k)`, at `a`..`b`.
(define extract-syn (subr (maxeff (read @globals) (read rs)) (syn int int int) syn)
  (lambda (p k a b)
    (mk-list (the syns-a (list (mk-symbol "extract" a b) p (mk-int k a b))) a b)))
;; The `let`s binding each branch's value from `p`, the innermost the last
;; two's, around `body`.
(define par-lets (subr (maxeff parses spin) (syns-a syn syns-a int int) syn)
  (lambda (bs p body a b)
    (let* ((bnd (car bs)) (sa (syn-start bnd)) (sb (syn-end bnd))
           (mine (pair-syn (par-name bnd) (extract-syn p 1 sa sb) a b))
           (last? (null? (cdr (cdr bs))))
           (next (if last?
                     (pair-syn (par-name (car (cdr bs))) (extract-syn p 2 sa sb) a b)
                     (pair-syn p (extract-syn p 2 sa sb) a b)))
           (binds (mk-list (the syns-a (list mine next)) a b))
           (inside (if last? body (the syns-a (list (par-lets (cdr bs) p body a b))))))
      (mk-list (cons (mk-symbol "let" a b) (cons binds inside)) a b))))
;;; -------------------------------------------------------------- race

;; `(race e1 … en)`: `((with lib race2) (lambda () e1) (lambda () ((with
;; lib race2) (lambda () e2) … (lambda () en))))`: a branch's thunk at its
;; expression, the rest at the form (the Rust parser's `race_expansion`).
(define race-form (subr (maxeff parses spin) (fails syns-a symbol int int) syn)
  (lambda (fail items lib a b)
    (begin
      (at-least fail items 3 "`(race expression expression …)`" a b)
      (race-tree (cdr items) lib a b))))
;; The branches `es` as nested `race2`s.
(define race-tree (subr (maxeff parses spin) (syns-a symbol int int) syn)
  (lambda (es lib a b)
    (let* ((e (car es)) (sa (syn-start e)) (sb (syn-end e)))
      (if (null? (cdr es))
          (thunk-syn e sa sb)
          (let* ((op (mk-list (the syns-a (list (mk-symbol "with" a b) (atom lib a b)
                                                (mk-symbol "race2" a b)))
                              a b))
                 (inner (race-tree (cdr es) lib a b))
                 (rest (if (null? (cdr (cdr es))) inner (thunk-syn inner a b))))
            (mk-list (the syns-a (list op (thunk-syn e sa sb) rest)) a b))))))
;;; ----------------------------------------------------------- pselect

;; `(pselect (W0 x0 body0 …) … (Wn xn bodyn …))`, each `W` `(icell-get c)`,
;; `(receive box)`, `(sleep-until t)` or `(read-byte)` (whose `c` is `#u`,
;; at `W`, and which is called with none): `(let ((%sel-0 c0) … (%sel-n cn)) (let ((%sel (sync
;; (or-event E0 (or-event E1 … En))))) (if (= %sel 0) (let ((x0
;; (icell-get %sel-0))) body0 …) … (let ((xn …)) bodyn …))))`, each `E`
;; `(cell-event %sel-i)`, `(mailbox-event %sel-i)`, `(clock-event %sel-i)` or
;; `(stdin-event %sel-i)`, through `lib`. An arm's event, test and `let` at
;; the arm, its `W` at the `W`; the rest at the form (the Rust parser's
;; `select_expansion`).
(define select-form (subr (maxeff parses spin) (fails syns-a symbol int int) syn)
  (lambda (fail items lib a b)
    (let ((arms (cdr items)))
      (begin
        (if (null? arms) (fail select-usage a b) #u)
        (select-check fail arms)
        (let* ((sel (mk-symbol "%sel" a b))
               (sync (mk-list (the syns-a (list (lib-op lib "sync" a b)
                                                (select-events arms 0 lib a b)))
                              a b))
               (bind (mk-list (the syns-a (list (pair-syn sel sync a b))) a b))
               (inner (mk-list (the syns-a (list (mk-symbol "let" a b) bind
                                                 (select-arms arms 0 sel a b)))
                               a b)))
          (mk-list (the syns-a (list (mk-symbol "let" a b) (mk-list (select-binds arms 0 a b) a b)
                                     inner))
                   a b))))))
;; What `pselect` is short of, said.
(define select-usage string
  (string-append "`(pselect ((icell-get i-cell) name body …) ((receive mailbox) name body …) "
                 "((sleep-until time) name body …) ((read-byte) name body …) …)`"))
(define select-arm-usage string
  (string-append "a `pselect` arm is `((icell-get i-cell) name body …)`, "
                 "`((receive mailbox) name body …)`, `((sleep-until time) name body …)` "
                 "or `((read-byte) name body …)`"))
;; The event of a `pselect` arm whose wait is named `w`, or "" if none.
(define wait-event (subr pure (symbol) string)
  (lambda (w)
    (cond ((symbol=? w 'icell-get) "cell-event")
          ((symbol=? w 'receive) "mailbox-event")
          ((symbol=? w 'sleep-until) "clock-event")
          ((symbol=? w 'read-byte) "stdin-event")
          (else ""))))
;; How many items a `pselect` arm's wait named `w` has: `(read-byte)` one.
(define wait-length (subr pure (symbol) int) (lambda (w) (if (symbol=? w 'read-byte) 1 2)))
;; Each arm `(W x body …)`, `W` `(icell-get c)`, `(receive box)`,
;; `(sleep-until t)` or `(read-byte)`.
(define select-check (subr parses (fails syns-a) unit)
  (lambda (fail arms)
    (if (null? arms)
        #u
        (let* ((x (items-of (car arms)))
               (w (if (null? x) nil (items-of (car x)))))
          (if (and (>= (len x) 3) (syn-symbol? (nth x 1)) (not (null? w))
                   (= (len w) (wait-length (syn-head (car w))))
                   (not (string=? (wait-event (syn-head (car w))) "")))
              (select-check fail (cdr arms))
              (fail-at-syn fail select-arm-usage (car arms)))))))
;; An arm's `W`, and its `W`'s items.
(define arm-wait (subr parses (syn) syn) (lambda (arm) (car (items-of arm))))
(define arm-wait-items (subr parses (syn) syns-a) (lambda (arm) (items-of (arm-wait arm))))
;; An arm's `c`: its `W`'s operand, or, `(read-byte)` having none, `#u` at
;; its `W`.
(define arm-operand (subr parses (syn) syn)
  (lambda (arm)
    (let ((w (arm-wait-items arm)))
      (if (null? (cdr w))
          (mk-symbol "#u" (syn-start (arm-wait arm)) (syn-end (arm-wait arm)))
          (nth w 1)))))
;; `%sel-i`, at `a`..`b`.
(define sel-name (subr (maxeff (read @globals) (read rs)) (int int int) syn)
  (lambda (i a b) (mk-symbol (string-append "%sel-" (int->string i)) a b)))
;; `(with lib name)`, at `a`..`b`.
(define lib-op (subr (maxeff (read @globals) (read rs)) (symbol string int int) syn)
  (lambda (lib name a b)
    (mk-list (the syns-a (list (mk-symbol "with" a b) (atom lib a b) (mk-symbol name a b))) a b)))
;; `((%sel-i c) …)`'s items, from arm `i` of `arms`.
(define select-binds (subr (maxeff parses spin) (syns-a int int int) syns-a)
  (lambda (arms i a b)
    (if (null? arms)
        nil
        (cons (pair-syn (sel-name i a b) (arm-operand (car arms)) a b)
              (select-binds (cdr arms) (+ i 1) a b)))))
;; The events of `arms`, from arm `i`, joined by `or-event`s.
(define select-events (subr (maxeff parses spin) (syns-a int symbol int int) syn)
  (lambda (arms i lib a b)
    (let* ((arm (car arms)) (sa (syn-start arm)) (sb (syn-end arm))
           (op (wait-event (syn-head (car (arm-wait-items arm)))))
           (e (mk-list (the syns-a (list (lib-op lib op sa sb) (sel-name i a b))) sa sb)))
      (if (null? (cdr arms))
          e
          (mk-list (the syns-a (list (lib-op lib "or-event" a b) e
                                     (select-events (cdr arms) (+ i 1) lib a b)))
                   a b)))))
;; The arms of `arms`, from arm `i`, each chosen when `sel` is its number.
(define select-arms (subr (maxeff parses spin) (syns-a int syn int int) syn)
  (lambda (arms i sel a b)
    (let* ((arm (car arms)) (sa (syn-start arm)) (sb (syn-end arm)) (x (items-of arm))
           (w (arm-wait arm))
           (get (mk-list (if (null? (cdr (items-of w)))
                             (the syns-a (list (car (items-of w))))
                             (the syns-a (list (car (items-of w)) (sel-name i a b))))
                         (syn-start w) (syn-end w)))
           (bind (mk-list (the syns-a (list (pair-syn (nth x 1) get sa sb))) sa sb))
           (this (mk-list (cons (mk-symbol "let" sa sb) (cons bind (drop x 2))) sa sb)))
      (if (null? (cdr arms))
          this
          (let ((test (mk-list (the syns-a (list (mk-symbol "=" sa sb) sel (mk-int i sa sb)))
                               sa sb)))
            (mk-list (the syns-a (list (mk-symbol "if" a b) test this
                                       (select-arms (cdr arms) (+ i 1) sel a b)))
                     a b))))))
