;;; The checker, in FX-26: programs, form by form, and proofs.
;;; Part of the checker, `check-types.fx` first (PLAN.md §11, step 10).

;;; ------------------------------------------------------------ programs

;; Its types, those it uses of the files before it, and the signatures of
;; what it is given.
(let* ((check-program-types (load-module "fx26:check-program-types.fx"))
       (check-types-types (load-module "fx26:check-types-types.fx"))
       (parser-types ((proj (load-module "fx26:parser-types.fx") @s @e @m @c @p)))
       (eager-reader-types ((proj (load-module "fx26:eager-reader-types.fx") @s @e @m @c)))
       (check-env-types (load-module "fx26:check-env-types.fx"))
       (check-resolve-types (load-module "fx26:check-resolve-types.fx"))
       (check-terminate-types (load-module "fx26:check-terminate-types.fx"))
       (check-subst-types (load-module "fx26:check-subst-types.fx"))
       (check-print-types (load-module "fx26:check-print-types.fx"))
       (check-print-parts-types (load-module "fx26:check-print-parts-types.fx"))
       (check-syntax-types (load-module "fx26:check-syntax-types.fx"))
       (check-effects-types (load-module "fx26:check-effects-types.fx"))
       (check-proofs-types (load-module "fx26:check-proofs-types.fx"))
       (check-rules-types (load-module "fx26:check-rules-types.fx"))
       (check-generative-types (load-module "fx26:check-generative-types.fx"))
       (check-read-descs-types (load-module "fx26:check-read-descs-types.fx"))
       (check-errors-types (load-module "fx26:check-errors-types.fx"))
       (check-letrec-types (load-module "fx26:check-letrec-types.fx"))
       (check-read-types (load-module "fx26:check-read-types.fx"))
       (check-expect-types (load-module "fx26:check-expect-types.fx"))
       (check-modules-types (load-module "fx26:check-modules-types.fx"))
       (check-modules-read-types (load-module "fx26:check-modules-read-types.fx"))
       (check-modorder-types (load-module "fx26:check-modorder-types.fx"))
       (check-synth-types (load-module "fx26:check-synth-types.fx"))
       (check-module-rules-types (load-module "fx26:check-module-rules-types.fx"))
       (check-subtype-types (load-module "fx26:check-subtype-types.fx"))
       (reader-types (load-module "fx26:reader-types.fx"))
       (check-reps-types (load-module "fx26:check-reps-types.fx")))
  ;; What it is given: the modules of the files before it that it uses.
  (lambda ((check-types (select check-types-types check-types-sig))
           (check-syntax (select check-syntax-types check-syntax-sig))
           (check-effects (select check-effects-types check-effects-sig))
           (check-env (select check-env-types check-env-sig))
           (check-proofs (select check-proofs-types check-proofs-sig))
           (check-rules (select check-rules-types check-rules-sig))
           (check-generative (select check-generative-types check-generative-sig))
           (check-read-descs (select check-read-descs-types check-read-descs-sig))
           (check-resolve (select check-resolve-types check-resolve-sig))
           (check-errors (select check-errors-types check-errors-sig))
           (check-terminate (select check-terminate-types check-terminate-sig))
           (check-print (select check-print-types check-print-sig))
           (check-letrec (select check-letrec-types check-letrec-sig))
           (check-read (select check-read-types check-read-sig))
           (check-expect (select check-expect-types check-expect-sig))
           (check-modules (select check-modules-types check-modules-sig))
           (check-modorder (select check-modorder-types check-modorder-sig))
           (check-subst (select check-subst-types check-subst-sig))
           (check-synth (select check-synth-types check-synth-sig))
           (check-module-rules (select check-module-rules-types check-module-rules-sig))
           (check-subtype (select check-subtype-types check-subtype-sig))
           (parser (select reader-types parser-sig))
           (check-modules-read (select check-modules-read-types check-modules-read-sig))
           (check-print-parts (select check-print-parts-types check-print-parts-sig))
           ;; Its types as reps (`check-reps.fx`).
           (check-reps (select check-reps-types check-reps-sig)))
    ;; Part of it in a file of its own (`check-program-defs.fx`), made of what
    ;; it is given.
    (let ((check-program-defs
           ((load-input "fx26:check-program-defs.fx")
            check-types check-syntax check-effects check-env check-proofs check-rules
            check-generative check-read-descs check-resolve check-errors check-terminate
            check-print check-letrec check-read check-expect check-modules check-modorder
            check-subst check-synth check-module-rules check-subtype parser check-modules-read
            check-print-parts)))
      (module
(hide (include check-program-types) (include check-types-types) (include parser-types)
      (include eager-reader-types) (include check-env-types) (include check-resolve-types)
      (include check-terminate-types) (include check-subst-types) (include check-print-types))
;; The types it uses of the files before it.
;; What it uses of the modules it is given: all of each, hidden.
(hide (include check-types) (include check-syntax) (include check-env) (include check-proofs)
      (include check-rules) (include check-generative) (include check-read-descs)
      (include check-errors) (include check-terminate) (include check-print-parts)
      (include check-print) (include check-letrec) (include check-expect) (include check-modules)
      (include check-modules-read) (include check-subst) (include check-synth)
      (include check-module-rules) (include check-subtype) (include parser))
(import check-effects k-atom-region k-one k-insert)
(import check-resolve k-defs k-free-into k-has-region-in? k-last-uses k-reset k-runs exp-reading)
(import check-read k-items k-name-of k-sfail k-symbol-head)
(define k-names-onto (with check-modorder k-names-onto))

;; Given on, all `check-program-defs.fx` defines.
(import check-program-defs k-take-inside k-conv-atoms k-conv-name? k-conv-text k-conv-texts
        k-conv-insert k-conv-ours k-conv-role-end k-conv-theirs k-conv-older k-conv-twice
        k-conv-compare k-check-convention k-prefixed k-declare k-declare-each k-types-again k-ahead
        k-show-lines k-line k-define-line k-push-lines k-bind-named-global k-rec-types k-rec-lambdas
        k-rec-check k-note-recursive k-group-free k-rebind-each k-note-rec-ending k-rec-found
        k-define-rec k-rev-runs checked-tops k-rev-defs k-rec-names k-top-names k-defined?
        k-old-types k-fits-its-old? k-fits-old? k-names-without k-defs-without k-record k-users-of
        k-shown k-break-all k-lines-append k-star-subr k-star-lambda k-note-alone k-lemma-as
        k-note-lemma k-arrow-star-alone k-arrow-star-lambda k-arrow-star-spins k-define-typed
        k-reads-globals-only? k-shared-impure-why k-shared-impure k-define-untyped k-top-lines
        k-lines-append-names k-defs-names k-names-within k-has-spin? k-type-spins? k-names-spin?
        k-top-start k-top-end)

(define k-atoms-globals (->* (k-eff) k-regions)
  (lambda (e)
    (cond ((null? e) nil)
          ((k-globals-atom? (car e))
           (the k-regions (cons (k-atom-region (car e)) (k-atoms-globals (cdr e)))))
          (else (k-atoms-globals (cdr e))))))
;; The globals calling a value of type `t` reads: its latent effect's, under
;; any `poly`; none, if it is not a procedure.
(define k-latent-globals (->* (int) k-regions)
  (lambda (t)
    (tagcase (k-get (k-resolve t))
      (ty-poly (bs body) (k-latent-globals body))
      (ty-subr (e ps r cv spc) (k-atoms-globals e))
      (else y nil))))
;; The first of `ns` whose global `rs` has, if any.
(define k-first-read (->* (k-regions k-names) k-names)
  (lambda (rs ns)
    (cond ((null? ns) nil)
          ((k-has-region-in? rs (r-global (car ns))) (the k-names (cons (car ns) nil)))
          (else (k-first-read rs (cdr ns))))))
;; What a procedure that may reach itself through a global must do.
(define k-must-spin string "` may reach itself through a global: its type must say `spin`")
;; Why calling `name`, which reads the global `m`, may reach itself.
(define k-reads-itself (->* (string string) string)
  (lambda (name m)
    (k-cat4 (k-cat5 "calling `" name "` reads `" m "`, so `") name k-must-spin
            " (or, to call itself directly, it binds itself with a local `letrec`)")))
;; Why calling `name`, which may read any global, may reach itself.
(define k-reads-any (->* (string) string)
  (lambda (name)
    (let ((so (k-cat5 "calling `" name "` may read any global, `" name "` too, so `")))
      (k-cat3 so name k-must-spin))))
;; An error at `form` if calling the procedure `name`, of type `t`, may
;; reach itself through a global: if it reads one of `ns`, or any global.
(define k-not-reaching (->* (top string int k-names) unit)
  (lambda (form name t ns)
    (let* ((reads (k-latent-globals t))
           (m (k-first-read reads ns))
           (a (k-top-start form))
           (b (k-top-end form)))
      (cond ((not (null? m)) (k-fail (k-reads-itself name (symbol->string (car m))) a b))
            ((k-has-region-in? reads (r-globals)) (k-fail (k-reads-any name) a b))
            (else #u)))))
;; Defining a global writes it: a procedure stored in global `f` whose calls
;; read `f` may reach itself through the global, which termination checking,
;; trusting every procedure of a type without `spin` to end, has not seen.
;; So it must say `spin`, as a procedure kept in a ref must, however it
;; reads `f`; one that stays `pure` binds itself with a local `letrec`. A
;; group's members read each other so. Reading `@globals` reads `f` too, at
;; its first definition as at any other (`top.rs`, `no_reaching_itself`).
(define k-no-reaching-itself (->* (top k-names) unit)
  (lambda (form ns)
    (letrec ((each (subr (maxeff checks spin) (k-names) unit)
               (lambda (ms)
                 (if (null? ms)
                     #u
                     (let* ((n (car ms)) (t (k-lookup-raw n)))
                       (if (k-type-spins? t)
                           (each (cdr ms))
                           (begin (k-not-reaching form (symbol->string n) t ns)
                                  (each (cdr ms))))))))
             ;; What a global that is no procedure holds (`no_reaching_itself`).
             (kept (subr (maxeff checks spin) (k-names) unit)
               (lambda (ms)
                 (if (null? ms)
                     #u
                     (let* ((n (car ms)) (t (k-lookup-raw n))
                            (found (if (k-procedure? t) nil (k-kept-reading t ns nil))))
                       (if (null? found)
                           (kept (cdr ms))
                           (k-fail (k-kept-message (symbol->string n) (extract (car found) 2)
                                                   (k-show-ty (extract (car found) 1)))
                                   (k-top-start form) (k-top-end form))))))))
      (begin (each ns) (kept ns)))))
;; Whether `t` is a procedure, under any `poly`.
(define k-procedure? (->* (int) bool)
  (lambda (t)
    (tagcase (k-get (k-resolve t))
      (ty-poly (bs body) (k-procedure? body))
      (ty-subr (e ps r cv spc) #t)
      (else y #f))))
;; Why global `name`, keeping a procedure of type `t` that reads `read`,
;; may reach itself.
(define k-kept-message (->* (string string string) string)
  (lambda (name read t)
    (k-cat5 "`" name "` keeps a procedure that reads `" read
            (string-append "`, so it could reach itself through a global: "
                           (string-append "it must say `spin`, and it is a " t)))))
;; What reaches itself through a global and says nothing of it.
(define-type k-kept-found (listof (productof (1 int) (2 string)) acyclic))
;; A procedure a value of type `t` keeps, kept in a global (a product's field,
;; a list's element, a module's value, what a ref holds, …), whose calls read
;; one of `ns`, or `@globals`, and that does not say `spin`: its
;; type and what it reads; none or one. Not what a procedure takes or gives,
;; kept nowhere yet. `path`, the types walked to here (`kept_reading`).
(define-rec
  (k-kept-reading (->* (int k-names k-ids) k-kept-found)
    (lambda (t ns path)
      (let ((t (k-resolve t)))
        (if (k-has-id? path t)
            (the k-kept-found nil)
            (let ((path (the k-ids (cons t path)))
                  (one (lambda ((x int)) (the k-ids (cons x nil)))))
              (tagcase (k-get t)
                (ty-subr (e ps r cv spc) (k-kept-read t e ns))
                (ty-poly (bs body) (k-kept-reading body ns path))
                (ty-ref (a r) (k-kept-reading a ns path))
                (ty-array (a z r) (k-kept-reading a ns path))
                (ty-icell (a r) (k-kept-reading a ns path))
                (ty-markkey (a r) (k-kept-reading a ns path))
                (ty-nlist (a z r) (k-kept-reading a ns path))
                (ty-pair (a b r nl) (k-kept-in (the k-ids (cons a (one b))) ns path))
                (ty-bloblet (fs z r) (k-kept-in fs ns path))
                (ty-product (ps) (k-kept-in (k-parts-types ps) ns path))
                (ty-sum (ps) (k-kept-in (k-parts-types ps) ns path))
                (ty-union (ms) (k-kept-in ms ns path))
                (ty-allof (ms) (k-kept-in ms ns path))
                (ty-module (abs ds vs) (k-kept-in (k-parts-types vs) ns path))
                (ty-named (g ds)
                  (k-kept-in (the k-ids (cons (extract (k-gen-of g) 4) (k-desc-types ds)))
                             ns path))
                (ty-app (f ds) (k-kept-in (k-desc-types ds) ns path))
                (else y (the k-kept-found nil))))))))
  (k-kept-in (->* (k-ids k-names k-ids) k-kept-found)
    (lambda (ts ns path)
      (if (null? ts)
          (the k-kept-found nil)
          (let ((x (k-kept-reading (car ts) ns path)))
            (if (null? x) (k-kept-in (cdr ts) ns path) x))))))
;; Procedure type `t`, of effect `e`, kept in a global: what of `ns` it reads,
;; or `@globals`, unless it says `spin`.
(define k-kept-read (->* (int k-eff k-names) k-kept-found)
  (lambda (t e ns)
    (if (k-has-spin? e)
        (the k-kept-found nil)
        (let* ((reads (k-atoms-globals e)) (m (k-first-read reads ns)))
          (cond ((not (null? m)) (list (product (1 t) (2 (symbol->string (car m))))))
                ((k-has-region-in? reads (r-globals))
                 (list (product (1 t) (2 "@globals"))))
                (else (the k-kept-found nil)))))))
;; The types of parts `ps`, in order.
(define k-parts-types (->* (k-parts) k-ids)
  (lambda (ps)
    (if (null? ps) nil (the k-ids (cons (extract (car ps) 2) (k-parts-types (cdr ps)))))))
;; Note that `form` runs, assigning the globals it defines (`assigns`) or
;; making them new.
(define k-note-run (->* (top bool) unit)
  (lambda (form assigns)
    (set k-runs (the k-run-list (cons (product (1 form) (2 assigns)) (get k-runs))))))
;; The reading form `x` was read at (`parser-ids.fx`): its expressions'.
(define k-top-reading (->* (top) int)
  (lambda (x)
    (tagcase x
      (t-define (n ty e a b) (exp-reading e))
      (t-define-rec (bs a b) (if (null? bs) 0 (exp-reading (extract (car bs) 3))))
      (t-exp (e) (exp-reading e))
      (else y 0))))
;; Each of `users` checked again after the redefinition of `ns`: defined
;; again if it checks, broken if not. Each read again first, in the state
;; the session is in now (`read-again`): what this check finds is of keys
;; of its own, never taken for what the first check of it found.
(define k-rerun (->* (k-def-list k-names k-out) k-out)
  (lambda (users ns lines)
    (if (null? users)
        lines
        (let* ((u (car users))
               (form ((with parser read-again) (k-top-reading (extract u 2)) (extract u 2)))
               (olds (k-old-types (extract u 1)))
               (m (k-mark))
               (reset (set k-last-uses nil))
               (r (prompt k-tag
                    (let ((ls (k-top-lines form)))
                      (begin (k-no-reaching-itself form (extract u 1)) (k-ok ls)))
                    (lambda (r) r))))
          (tagcase r
            (k-ok (ls)
              (let* ((assigns (k-fits-old? olds))
                     (recorded (k-record form (extract u 1)))
                     (ran (k-note-run form assigns)))
                (k-rerun (cdr users) ns (k-lines-append lines ls))))
            (k-err (msg a b)
              (begin (k-unbind-to m)
                     (let ((why (k-cat5 "since " (k-shown ns) " was redefined (" msg ")")))
                       (k-break-all (extract u 1) why))
                     (k-rerun (cdr users) ns lines)))
            (else y (k-rerun (cdr users) ns lines)))))))
;; Whether a redefinition that makes a new global leaves the definitions
;; that use the name as they are, out of date, rather than checking them
;; again (`k-rerun`): what the REPL asks for, re-running them when told
;; (`,rerun-outdated`), as the Rust checker's `defer_reruns`.
(define k-defer-reruns (ref bool @t) (new #f))
;; For a driver: whether re-runs wait.
;; For a driver: whether a form's lines are made (`k-show-lines`).
(define check-lines! (->* (bool) unit)
  (lambda (on) (set k-show-lines on)))
(define check-defer-reruns! (->* (bool) unit)
  (lambda (on) (set k-defer-reruns on)))
;; The switches a driver set that change what a check finds, as text:
;; folded into each reading (`readings.fx`), as the session's state is, so
;; that a text read under other switches is another reading. As `ids.rs`'s
;; `settings` writes them: the program's convention, then each switch on.
(define checked-settings (->* () string)
  (lambda ()
    (k-cat5 (k-conv-show (get k-conv-default))
            (if (get k-globals-effects) " globals-effects" "")
            (if (get k-defer-reruns) " defer-reruns" "")
            (if (get k-syscalls) " syscalls" "")
            (if (> (get k-in-built-in) 0) " built-in" ""))))
;; The breaks as the last check began (`k-broken`, which only grows, newest
;; first); and, while they are held (`check-hold-breaks!`), those the check
;; made, set aside, and the breaks as it began.
(define k-broken-began (ref (listof k-break acyclic) @t) (new nil))
(define k-broken-held (ref (listof k-break acyclic) @t) (new nil))
(define k-broken-under (ref (listof k-break acyclic) @t) (new nil))
(define k-holding-breaks (ref bool @t) (new #f))
(define k-breaks-count (->* ((listof k-break acyclic)) int)
  (lambda (bs) (if (null? bs) 0 (+ 1 (k-breaks-count (cdr bs))))))
;; The first `n` of `bs`, onto `rest`.
(define k-breaks-onto
  (->* ((listof k-break acyclic) int (listof k-break acyclic)) (listof k-break acyclic))
  (lambda (bs n rest)
    (if (= n 0)
        rest
        (the (listof k-break acyclic) (cons (car bs) (k-breaks-onto (cdr bs) (- n 1) rest))))))
;; The breaks made since `k-broken` was `under`, newest first.
(define k-breaks-since
  (->* ((listof k-break acyclic)) (listof k-break acyclic))
  (lambda (under)
    (let ((now (get k-broken)))
      (k-breaks-onto now (- (k-breaks-count now) (k-breaks-count under)) nil))))
;; For a driver (the native convention's definition, `Session::native_define`,
;; which checks the definition, then its value again, as an expression): on,
;; the breaks the last check made set aside, the broken as it began, so that
;; the value's check sees the definitions it uses as the definition's did;
;; off, put back, after those the checks between made.
(define check-hold-breaks!
  (->* (bool) unit)
  (lambda (on)
    (cond ((and on (not (get k-holding-breaks)))
           (let ((under (get k-broken-began)))
             (begin (set k-broken-held (k-breaks-since under))
                    (set k-broken-under under)
                    (set k-broken under)
                    (set k-holding-breaks #t))))
          ((and (not on) (get k-holding-breaks))
           (let* ((under (get k-broken-under))
                  (held (get k-broken-held))
                  (between (k-breaks-since under)))
             (begin (set k-broken (k-breaks-onto between (k-breaks-count between)
                                                 (k-breaks-onto held (k-breaks-count held) under)))
                    (set k-broken-held nil)
                    (set k-holding-breaks #f))))
          (else #u))))
;; A top-level form, checked under redefinition: its lines, and those of
;; the definitions it has run again.
(define k-defining (->* (top) k-out)
  (lambda (form)
    (let* ((ns (k-top-names form))
           (olds (k-old-types ns))
           (defer (get k-defer-reruns))
           (users (if (or (null? olds) defer) (the k-def-list nil) (k-users-of ns)))
           (reset (set k-last-uses nil))
           (kept (if (get k-show-lines) (k-keep-atree!) #u))
           (lines (k-top-lines form))
           (knot (k-no-reaching-itself form ns))
           (assigns (and (not (null? olds)) (k-fits-old? olds)))
           (recorded (k-record form ns))
           (ran (k-note-run form assigns)))
      (if (or (null? olds) assigns defer) lines (k-rerun users ns lines)))))

;;; Syscalls (`docs/research/syscalls.md`; `syscall.rs`, word for word): a
;;; declaration checked alone, then expanded into two definitions, each
;;; checked as any is: `%syscall-available:NAME`, whether the runtime has
;;; it, its line not shown, and `NAME`, which may name what a module file
;;; built in may.
(define k-sys-host-msg string "a syscall's host name is a string, `namespace:name/version`")
(define k-sys-part-char? (->* (char) bool)
  (lambda (c)
    (or (and (char>=? c #\a) (char<=? c #\z)) (and (char>=? c #\0) (char<=? c #\9))
        (char=? c #\-))))
;; Whether `h` from `i` is the rest of a host name, in part `p` (0 the
;; namespace, 1 the name, 2 the version) of which `n` characters are read.
(define k-sys-host-from? (->* (string int int int) bool)
  (lambda (h i p n)
    (if (= i (string-length h))
        (and (= p 2) (> n 0))
        (let ((c (string-ref h i)))
          (cond ((and (= p 0) (char=? c #\:)) (and (> n 0) (k-sys-host-from? h (+ i 1) 1 0)))
                ((and (= p 1) (char=? c #\/)) (and (> n 0) (k-sys-host-from? h (+ i 1) 2 0)))
                ((= p 2) (and (char>=? c #\0) (char<=? c #\9)
                              (not (and (= n 0) (char=? c #\0)))
                              (k-sys-host-from? h (+ i 1) 2 (+ n 1))))
                (else (and (k-sys-part-char? c) (k-sys-host-from? h (+ i 1) p (+ n 1)))))))))
(define k-sys-host-of (->* (syn) string)
  (lambda (s)
    (tagcase s
      (atom (d a b)
        (typecase d
          (string h (if (k-sys-host-from? h 0 0 0) h (k-sfail k-sys-host-msg s)))
          (else x (k-sfail k-sys-host-msg s))))
      (else x (k-sfail k-sys-host-msg s)))))
(define k-sys-str (->* (string int int int int) exp) (lambda (v a b k r) (e-str v a b k r)))
;; `x1` … `xi`, onto `acc`, the `i`th's identity `k`+`i` in reading `r`.
(define k-sys-xs (->* (int int int int int (listof exp acyclic)) (listof exp acyclic))
  (lambda (i a b k r acc)
    (if (= i 0)
        acc
        (k-sys-xs (- i 1) a b k r
                  (cons (e-var (string->symbol (string-append "x" (int->string i))) a b (+ k i) r)
                        acc)))))
(define k-sys-params (->* (int (listof syn acyclic)) param-list)
  (lambda (i ps)
    (if (null? ps)
        nil
        (cons (product (1 (string->symbol (string-append "x" (int->string i))))
                       (2 (the syns-a (list (car ps)))))
              (k-sys-params (+ i 1) (cdr ps))))))
(define k-sys-items (->* (syn) (listof syn acyclic))
  (lambda (s) (tagcase s (lst (items d a b) items) (else x nil))))
;; A reading's digest (`readings.fx`).
(define readings ((proj (load-module "fx26:readings.fx") @s @e @m @c)))
;; The two definitions declaration `name` at `a`..`b` is, its type
;; `canonical`, `text` printed: whether the runtime has it, for a required
;; one checked as it is made; and itself, each of its expressions an
;; identity of its own. A `poly`'s binders are in scope in its definition,
;; which is checked against its body.
(define k-sys-defs (->* (symbol string syn string bool int int) (productof (1 top) (2 top)))
  (lambda (name host canonical text required a b)
    (let*
     ((label (string-append "syscall " (symbol->string name) " (\"" host "\")"))
           ;; A reading of their own, what they are made of, in no session's
           ;; state (-1: apart from every text read).
           (r ((with readings text-reading-of) -1
               (string-append label " " text (if required " required" " optional"))))
           (asks (lambda ((f symbol) (k int))
                   (e-app (e-var f a b k r)
                          (list (k-sys-str label a b (+ k 1) r) (k-sys-str host a b (+ k 2) r)
                                (k-sys-str text a b (+ k 3) r))
                          a b (+ k 4) r)))
           (cs (k-sys-items canonical))
           (poly? (string=? (syn-name (car cs)) "poly"))
           (subr (if poly? (car (cdr (cdr cs))) canonical))
           (ss (k-sys-items subr))
           (ps (k-sys-items (car (cdr (cdr ss)))))
           (n (length ps))
           ;; The call at the declared effect: `%syscallN`'s, a binder, so given.
           (str (atom 'string a b))
           (at (lst (list (atom 'subr a b) (car (cdr ss))
                          (lst (cons str (cons str (cons str ps))) nil a b)
                          (car (cdr (cdr (cdr ss)))))
                    nil a b))
           (call (tagcase (asks (string->symbol (string-append "%syscall" (int->string n))) 1010)
                   (e-app (f xs a2 b2 k2 k2r)
                     (e-app (e-the at f a b 1016 r) (append xs (k-sys-xs n a b 1020 r nil)) a b k2
                            k2r))
                   (else x x)))
           (body (e-lambda (k-sys-params 1 ps) (e-the (car (cdr (cdr (cdr ss)))) call a b 1030 r)
                           a b 1031 r))
           (available
            (if required
                (e-begin (list (asks '%syscall-require 1040) (e-bool #t a b 1045 r)) a b 1046 r)
                (e-app (e-var '%syscall-available? a b 1050 r)
                       (list (k-sys-str host a b 1051 r) (k-sys-str text a b 1052 r)) a b 1053 r)))
           (companion (string->symbol (string-append "%syscall-available:" (symbol->string name)))))
      (product (1 (t-define companion (the syns-a (list (atom 'bool a b))) available a b))
               (2 (t-define name (the syns-a (list canonical)) body a b))))))
;; `(define-syscall name "host" type)` (`required`), or
;; `(define-optional-syscall …)`, at `a`..`b`: its line, its definition's.
(define k-define-syscall (->* (bool syn int int) k-out)
  (lambda (required s a b)
    (let* ((what (if required "define-syscall" "define-optional-syscall"))
           (allowed (if (or (> (get k-in-built-in) 0) (get k-syscalls))
                        #u
                        (k-fail "syscalls are declared only by a runtime's own code" a b)))
           (items (k-sys-items s))
           (shape (if (= (length items) 4)
                      #u
                      (k-fail (string-append "`(" what " name \"host-name\" type)`") a b)))
           (name (k-name-of (car (cdr items)) "expected a name"))
           (host (k-sys-host-of (car (cdr (cdr items)))))
           (ty (car (cdr (cdr (cdr items)))))
           (t (k-parse-type ty))
           (canonical (k-syscall-canonical t a b (syn-start ty) (syn-end ty)))
           (defs (k-sys-defs name host canonical (k-syn-text canonical) required a b)))
      (begin (set k-syscall-expanding (+ (get k-syscall-expanding) 1))
             (k-defining (extract defs 1))
             (let ((lines (k-defining (extract defs 2))))
               (begin (set k-syscall-expanding (- (get k-syscall-expanding) 1)) lines))))))
(define k-defining-form (->* (top) k-out)
  (lambda (form)
    (tagcase form
      (t-define-syscall (required s a b) (k-define-syscall required s a b))
      ;; A type naming a file, or after an `include`, declared in order.
      (else y (begin (if (k-declared-later? form) (k-declare form) #u) (k-defining form))))))

;; The second pass: definitions and expressions, in order, each under
;; redefinition (`k-defining`).
(define k-forms (->* (k-tops k-out) k-out)
  (lambda (forms out)
    (if (null? forms)
        (reverse out)
        (k-forms (cdr forms) (k-push-lines (k-defining-form (car forms)) out)))))

;; The entry point: check a program's trees, in the initial environment
;; written `standard`. What each definition and expression is, in order,
;; or the first error.
(define check-program (->* (syns-a k-tops) k-result)
  (lambda (standard forms)
    (check-staged-program standard forms (the (bytevectorof @t) (make-bytevector 0 0)))))
;; Names, each with a rep, in its binary form.
(define-type k-named-reps (listof (productof (1 symbol) (2 (bytevectorof @t))) acyclic))
;; A session's step's names, each its type or effect as a rep (`stage.rs`'s
;; `step_reps`; `docs/research/heap-types.md`, step 6), bound for its check
;; (`k-stage-type!`), as `session-step` sets them.
(define k-step-named (ref k-named-reps @t) (new nil))
(define set-step-named! (->* (k-named-reps) unit) (lambda (ns) (set k-step-named ns)))
(define k-bind-step-named! (->* (k-named-reps) unit)
  (lambda (ns)
    (if (null? ns)
        #u
        (let ((d ((with check-reps k-rep-desc) (extract (car ns) 2))))
          (begin (k-push-desc (extract (car ns) 1)
                              (tagcase d
                                (de (e) (ds-eff e))
                                (dt (t) (ds-rec t))
                                (else y (ds-rec 0))))
                 (k-bind-step-named! (cdr ns)))))))
(define k-unbind-step-named! (->* (k-named-reps) unit)
  (lambda (ns)
    (letrec ((named? (->* (symbol k-named-reps) bool)
                     (lambda (s ns)
                       (and (not (null? ns))
                            (or (symbol=? s (extract (car ns) 1)) (named? s (cdr ns))))))
             (drop (->* (k-scope) k-scope)
                   (lambda (ds)
                     (cond ((null? ds) nil)
                           ((named? (car (car ds)) ns) (drop (cdr ds)))
                           (else (cons (car ds) (drop (cdr ds))))))))
      (if (null? ns) #u (set k-dscope (drop (get k-dscope)))))))
;; For `stage` (`stage.rs`, `docs/research/heap-types.md`, step 3): `forms`
;; checked as `check-program` checks them, the name `%stage-type` the type of
;; `rep` imported (`k-rep-ty`), what the code is checked as, which the text
;; then names, not spells out; nothing bound if `rep` is empty.
(define check-staged-program (->* (syns-a k-tops (bytevectorof @t)) k-result)
  (lambda (standard forms rep)
    (let ((r (prompt k-tag
               (begin (k-reset) (set k-broken-began (get k-broken)) (set k-syscall-expanding 0)
                      (k-standard standard)
                      (set k-std-dscope (get k-dscope))
                      (k-stage-type! rep)
                      (k-ahead forms)
                      (k-ok (k-forms forms (k-types-again forms))))
               (lambda (r) r))))
      (begin (k-stage-type-gone! rep) r))))

;; The entry point for more of a program, form by form, as the REPL gives
;; them: checked in the environment the forms before left, which
;; `check-program` began. The facts for the compiler are only the new
;; forms', whose positions are in their own text.
(define check-more (->* (k-tops) k-result)
  (lambda (forms) (check-more-with forms (the (bytevectorof @t) (make-bytevector 0 0)))))
;; The same, the name `%stage-type` first the type of rep `rep` imported
;; (`k-rep-ty`), if not empty: as `check-staged-program` binds it.
(define check-more-with (->* (k-tops (bytevectorof @t)) k-result)
  (lambda (forms rep)
    (let ((r (prompt k-tag
               (begin (set k-extracts nil)
                      (set k-syscall-expanding 0)
                      (set k-broken-began (get k-broken))
                      (set k-effect-notes nil)
                      (k-forget-withs)
                      (set k-reshapes nil)
                      (set k-reshape-bases nil)
                      (set k-runs nil)
                      (k-stage-type! rep)
                      (k-ahead forms)
                      (k-ok (k-forms forms nil)))
               (lambda (r) r))))
      ;; Kept or not, the name gone after: a session's next step binds its own.
      (begin (k-stage-type-gone! rep) r))))
;; For a load of a `.fasl` (`session.rs`'s `run_program_def`,
;; `docs/research/heap-types.md`, step 5): the types of a rep of several,
;; the file's definitions', imported once, in order, each finding the
;; generative types it names here (none made); or none, if it cannot be.
;; What `import-types` imported last; none if it could not.
(define k-imported (ref k-ids @t) (new nil))
(define import-types (->* ((bytevectorof @t)) k-ids)
  (lambda (bytes)
    (begin
      (set k-imported nil)
      (prompt k-tag
        (begin ((with check-reps k-rep-making!) #f)
               (set k-imported ((with check-reps k-rep-tys) bytes))
               (k-ok nil))
        (lambda (r) r))
      ((with check-reps k-rep-making!) #t)
      (get k-imported))))
;; `forms` checked as `check-more` checks them, each of `named` its name
;; bound to a type of this checker's, by its id (`import-types`); the
;; names unbound after.
(define-type k-named-ids (listof (productof (1 symbol) (2 int)) acyclic))
(define check-more-typed (->* (k-tops k-named-ids) k-result)
  (lambda (forms named)
    (letrec ((bind (->* (k-named-ids) unit)
                   (lambda (ns)
                     (if (null? ns)
                         #u
                         (begin (k-push-desc (extract (car ns) 1) (ds-rec (extract (car ns) 2)))
                                (bind (cdr ns))))))
             (named? (->* (symbol k-named-ids) bool)
                     (lambda (s ns)
                       (and (not (null? ns))
                            (or (symbol=? s (extract (car ns) 1)) (named? s (cdr ns))))))
             (gone (->* (k-scope) k-scope)
                   (lambda (ds)
                     (cond ((null? ds) nil)
                           ((named? (car (car ds)) named) (gone (cdr ds)))
                           (else (cons (car ds) (gone (cdr ds))))))))
      (let ((r (begin (bind named) (check-more forms))))
        (begin (set k-dscope (gone (get k-dscope))) r)))))
;; `%stage-type` bound to rep `rep` imported, if it is not empty.
(define k-stage-type! (->* ((bytevectorof @t)) unit)
  (lambda (rep)
    (begin
      (if (= (bytevector-length rep) 0)
          #u
          (k-push-desc '%stage-type (ds-rec ((with check-reps k-rep-ty) rep nil))))
      (k-bind-step-named! (get k-step-named)))))
;; And unbound again, its innermost binding taken out of the description
;; scope (what a session's definition bound after it stays); and the
;; step's names (`set-step-named!`).
(define k-stage-type-gone! (->* ((bytevectorof @t)) unit)
  (lambda (rep)
    (letrec ((drop (->* (k-scope) k-scope)
                   (lambda (ds)
                     (cond ((null? ds) nil)
                           ((symbol=? (car (car ds)) '%stage-type) (cdr ds))
                           (else (cons (car ds) (drop (cdr ds))))))))
      (begin (if (= (bytevector-length rep) 0) #u (set k-dscope (drop (get k-dscope))))
             (k-unbind-step-named! (get k-step-named))))))

;; For a driver (a session's pending definition, `sessions26.rs`): `forms`
;; checked as `check-more` checks them, and the type global `n` then has,
;; printed whole (no `define-type` named; "" if none); then the checker
;; left as it was: the bindings they made undone, and the definitions and
;; breaks they noted let go, as the Rust checker's `try_top`. Re-runs wait
;; meanwhile, so that nothing but their own names is bound.
(define check-try
  (->* (k-tops symbol (bytevectorof @t)) (productof (1 k-result) (2 string) (3 (bytevectorof @t))))
  (lambda (forms n rep)
    (let* ((mark (k-mark)) (defs (get k-defs)) (broken (get k-broken)) (runs (get k-runs))
           (uses (get k-last-uses)) (deferring (get k-defer-reruns))
           (r (begin (set k-defer-reruns #t) (check-more-with forms rep)))
           (found (tagcase r (k-ok (ls) (k-lookup n)) (else y -1)))
           (t (if (< found 0) "" (k-show-ty-whole found)))
           ;; And as a rep, for the steps after to name, not read
           ;; (`docs/research/heap-types.md`, step 4); empty if none.
           (tr (if (< found 0) (the (bytevectorof @t) (make-bytevector 0 0)) (k-try-rep found))))
      (begin (k-unbind-to mark) (set k-defs defs) (set k-broken broken) (set k-runs runs)
             (set k-last-uses uses) (set k-defer-reruns deferring)
             (product (1 r) (2 t) (3 tr))))))
;; Type `t` as a rep, if a rep takes it and it names no variable; else
;; empty.
(define k-try-rep (->* (int) (bytevectorof @t))
  (lambda (t)
    (let ((bytes ((with check-reps k-ty-rep) t)))
      (if (or ((with check-reps k-rep-declined?)) (not (null? ((with check-reps k-rep-holes)))))
          (the (bytevectorof @t) (make-bytevector 0 0))
          bytes))))

;; `stage`'s (`stage.rs`; `docs/research/heap-types.md`, step 3): the
;; standard environment entered once, by the first stage, and kept; each
;; stage's forms checked as `check-more-with` checks them, then, once
;; compiled, what they bound undone (`check-staged-undo!`), as `check-try`
;; undoes a try's. The types a stage makes stay in the store, so once the
;; stages have made it `k-stage-growth` times what the standard environment
;; made, the next stage enters it again: the store stays bounded.
(define k-stage-base (ref int @t) (new 0))
(define k-stage-growth int 4)
(define k-stage-mark (ref int @t) (new 0))
(define k-stage-defs (ref (listof k-def acyclic) @t) (new nil))
(define k-stage-broken (ref (listof k-break acyclic) @t) (new nil))
(define k-stage-uses (ref k-names @t) (new nil))
(define k-stage-dscope (ref k-scope @t) (new nil))
(define check-staged (->* (syns-a k-tops (bytevectorof @t)) k-result)
  (lambda (standard forms rep)
    (begin
      (if (and (> (get k-stage-base) 0) (< (get k-ntys) (* k-stage-growth (get k-stage-base))))
          #u
          (begin (check-staged-program standard nil (the (bytevectorof @t) (make-bytevector 0 0)))
                 (set k-stage-base (get k-ntys))))
      (set k-stage-mark (k-mark)) (set k-stage-defs (get k-defs))
      (set k-stage-broken (get k-broken)) (set k-stage-uses (get k-last-uses))
      (set k-stage-dscope (get k-dscope))
      (check-more-with forms rep))))
;; What the stage `check-staged` checked last bound, undone.
(define check-staged-undo! (->* () unit)
  (lambda ()
    (begin (k-unbind-to (get k-stage-mark)) (set k-defs (get k-stage-defs))
           (set k-broken (get k-stage-broken)) (set k-runs nil)
           (set k-last-uses (get k-stage-uses)) (set k-dscope (get k-stage-dscope)))))

;; For a driver (a session on the evaluator, `sessions26.rs`): what the
;; last check runs (`checked-tops`), each by the first name it defines
;; ("" for none), and whether it assigns its names' globals.
;; Each name the program checked last defines, in order, and its type as a
;; rep, in its binary form (`check-reps.fx`): for the two checkers to be
;; compared by reps (`docs/research/heap-types.md`, step 2).
(define checked-reps (->* () (listof (productof (1 symbol) (2 (bytevectorof @t))) acyclic))
  (lambda ()
    (letrec ((names (->* (k-names (listof (productof (1 symbol) (2 (bytevectorof @t))) acyclic))
                         (listof (productof (1 symbol) (2 (bytevectorof @t))) acyclic))
                   (lambda (ns acc)
                     (if (null? ns)
                         acc
                         (let* ((t (k-lookup-raw (car ns)))
                                (r (if (< t 0)
                                       (the (bytevectorof @t) (make-bytevector 0 0))
                                       ((with check-reps k-ty-rep) t))))
                           (names (cdr ns)
                                  (if (or (< t 0) ((with check-reps k-rep-declined?)))
                                      acc
                                      (cons (product (1 (car ns)) (2 r)) acc)))))))
             (defs (->* (k-def-list (listof (productof (1 symbol) (2 (bytevectorof @t))) acyclic))
                        (listof (productof (1 symbol) (2 (bytevectorof @t))) acyclic))
                   (lambda (ds acc)
                     (if (null? ds)
                         acc
                         (defs (cdr ds) (names (reverse (extract (car ds) 1)) acc))))))
      (defs (get k-defs) nil))))
;; The same, each rep imported (`k-rep-ty`) and exported again: what the
;; FX-26 checker's import is tested by (it gives back the rep it took).
(define checked-reps-again
  (->* () (listof (productof (1 symbol) (2 (bytevectorof @t)) (3 (bytevectorof @t))) acyclic))
  (lambda ()
    (letrec ((go (->* ((listof (productof (1 symbol) (2 (bytevectorof @t))) acyclic))
                      (listof (productof (1 symbol) (2 (bytevectorof @t)) (3 (bytevectorof @t)))
                              acyclic))
                   (lambda (xs)
                     (if (null? xs)
                         nil
                         (let* ((n (extract (car xs) 1))
                                (t (k-lookup-raw n))
                                (r ((with check-reps k-ty-rep) t))
                                (holes ((with check-reps k-rep-holes)))
                                (back ((with check-reps k-rep-ty) r holes))
                                (again ((with check-reps k-ty-rep) back)))
                           (cons (product (1 n) (2 r) (3 again)) (go (cdr xs))))))))
      (go (checked-reps)))))
(define checked-run-names (->* () (listof (productof (1 string) (2 bool)) acyclic))
  (lambda ()
    (letrec ((go (subr kreads ((listof k-run acyclic))
                       (listof (productof (1 string) (2 bool)) acyclic))
                   (lambda (rs)
                     (if (null? rs)
                         nil
                         (let ((ns (k-top-names (extract (car rs) 1))))
                           (cons (product (1 (if (null? ns) "" (symbol->string (car ns))))
                                          (2 (extract (car rs) 2)))
                                 (go (cdr rs))))))))
      (go (checked-tops)))))

;; For a driver (`session-redefines`): global `n`'s type now, printed whole
;; (no `define-type` named), and the definitions that use it, their names;
;; none if `n` is no global.
(define check-redefines
  (->* (symbol) (listof (productof (1 string) (2 (listof string acyclic))) acyclic))
  (lambda (n)
    (let ((t (k-lookup n)))
      (if (or (< t 0) (not (k-global? n)))
          nil
          (list (product (1 (k-show-ty-whole t)) (2 (k-direct-users n (get k-defs)))))))))
;; The names of the definitions of `ds` that use `n` and do not define it:
;; its users themselves, not theirs (`k-users-of`).
(define k-direct-users (->* (symbol (listof k-def acyclic)) (listof string acyclic))
  (lambda (n ds)
    (cond ((null? ds) nil)
          ((and (k-name-in? n (extract (car ds) 3)) (not (k-name-in? n (extract (car ds) 1))))
           (k-names-strings (extract (car ds) 1) (k-direct-users n (cdr ds))))
          (else (k-direct-users n (cdr ds))))))
(define k-name-in? (->* (symbol k-names) bool)
  (lambda (n ns) (and (not (null? ns)) (or (symbol=? (car ns) n) (k-name-in? n (cdr ns))))))
(define k-names-strings (->* (k-names (listof string acyclic)) (listof string acyclic))
  (lambda (ns rest)
    (if (null? ns) rest (cons (symbol->string (car ns)) (k-names-strings (cdr ns) rest)))))))))
