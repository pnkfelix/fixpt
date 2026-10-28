;;; The checker, in FX-26: its environment. The base types; what is in
;;; scope, value variables and description names; and what checking proves
;;; that running needs.
;;; Part of the checker, `check-types.fx` first (PLAN.md §11, step 10).

;; Its types, those it uses of the files before it, and the signatures of
;; what it is given.
;; Its types (`check-env-types.fx`), loaded before the module so that they are not
;; among its values; the module names what it uses of them.
(let* ((check-env-types (load-module "fx26:check-env-types.fx"))
       (check-types-types (load-module "fx26:check-types-types.fx"))
       (table-types (load-module "fx26:table-types.fx"))
       (check-subtype-types (load-module "fx26:check-subtype-types.fx")))
  ;; What it is given: the modules of the files before it that it uses.
  (lambda ((check-types (select check-types-types check-types-sig))
           (tables (select table-types tables-sig)))
    (module
(hide (include check-env-types) (include check-types-types))
;; The types it uses of the files before it.
(define-type table (select table-types table))
(define-type k-trail (select check-subtype-types k-trail))
;; What it uses of the modules it is given: all of each, hidden.
(hide (include check-types) (include tables))

;; The base types, made first, in this order, so their indexes are known.
(define k-int int 0)
(define k-bool int 1)
(define k-string int 2)
(define k-unit int 3)
(define k-char int 4)
(define k-f64 int 14)
(define k-symbol int 6)
(define k-void int 16)
(define k-base (ref (listof (pairof symbol int @t) acyclic) @t) (new nil))
(define k-basic (->* (string) unit)
  (lambda (name)
    (let* ((s (string->symbol name)) (t (k-ty-new (ty-base s))))
      (set k-base (cons (cons s t) (get k-base))))))

(define k-find (->* (k-bindings symbol) int)
  (lambda (bs s)
    (cond ((null? bs) -1) ((symbol=? (car (car bs)) s) (cdr (car bs))) (else (k-find (cdr bs) s)))))

(define k-env (ref (table symbol k-stack @t) @t) (new (make-table symbol-hash symbol=?)))
(define k-trail (ref k-names @t) (new nil))
(define k-depth (ref int @t) (new 0))
;; Each name's bindings, innermost first: the depth each was made at, so
;; that whether one is newer than a mark is one look (`k-lookup`), not a
;; walk back along the trail.
(define k-depths (ref (table symbol k-stack @t) @t) (new (make-table symbol-hash symbol=?)))
(define k-known k-flags (new (make-table symbol-hash symbol=?)))
;; Whether each binding in `k-env` is a global: one a top-level definition
;; made. Naming one reads it, `(read (globals g))`, when
;; `k-globals-effects` says so, as the language will once every program
;; says what it reads (off until then).
(define k-global k-flags (new (make-table symbol-hash symbol=?)))
;; Each binding's flag: a module's item checked before the rest
;; (`k-early-modules`), bound once for all of the module, so that a `select`
;; of it is linked as a global's is (`k-link-global-select`).
(define k-fixed k-flags (new (make-table symbol-hash symbol=?)))
(define k-globals-effects (ref bool @t) (new #t))
;; The latent effect of the lambda checked last: for `define*`, what the
;; globals its lambda reads are.
(define k-last-latent (ref k-eff @t) (new nil))
;; For a driver: whether naming a global reads it.
(define check-globals-effects! (->* (bool) unit)
  (lambda (on) (set k-globals-effects on)))
(define k-broken (ref (listof k-break acyclic) @t) (new nil))
;; How many bindings `s` has now.
(define k-name-depth (->* (symbol) int)
  (lambda (s) (k-length (table-ref (get k-env) s nil))))
;; Why `s`'s binding now is broken, if it is.
;; Whether `b` breaks the `d`th binding of `s`.
(define k-breaks? (->* (k-break symbol int) bool)
  (lambda (b s d) (and (symbol=? (extract b 1) s) (= (extract b 2) d))))
(define k-broken-why (->* (symbol) k-strings)
  (lambda (s)
    (let ((d (k-name-depth s)))
      (letrec ((go (subr (read @globals) ((listof k-break acyclic)) k-strings)
                 (lambda (bs)
                   (cond ((null? bs) nil)
                         ((k-breaks? (car bs) s d) (the k-strings (cons (extract (car bs) 3) nil)))
                         (else (go (cdr bs)))))))
        (go (get k-broken))))))
;; While a module read from a file is checked (`load-module`, M7): how many
;; bindings there were as it began, of which it sees only the standard
;; ones; -1 otherwise. And the standard description names.
(define k-hide-mark (ref int @t) (new -1))
(define k-std-dscope (ref k-scope @t) (new nil))
;; How deep the module files built in being checked are; and whether `s`
;; is a standard name only they may name: what the scheduler needs of the
;; runtime, and its procedures' types as the forms see them (the Rust
;; checker's `built_in_only`).
(define k-in-built-in (ref int @t) (new 0))
;; For a driver (`Session::native_define` of a module file built in, given
;; as its text, `built_in_load`): while on, that text sees what a module
;; file built in sees.
(define check-built-in! (->* (bool) unit)
  (lambda (on) (set k-in-built-in (+ (get k-in-built-in) (if on 1 -1)))))
;; Whether the program is a runtime's, whose driver was told so
;; (`--syscalls`): it may declare syscalls, as a module file built in may
;; (`docs/research/syscalls.md`, "Containment"). For a driver, to set.
(define k-syscalls (ref bool @t) (new #f))
(define check-syscalls! (->* (bool) unit) (lambda (on) (set k-syscalls on)))
;; While a syscall's declaration expands (`k-define-syscall`), what it
;; expands into names what a module file built in may: more than 0. Each
;; check's entry point sets it to 0, so that a check that failed half way
;; leaves nothing named so.
(define k-syscall-expanding (ref int @t) (new 0))
;; The standard names only a module file built in may name, in a table:
;; every lookup of a name asks (`k-hidden-standard?`).
(define k-built-in-only-table (table symbol bool @t) (make-table symbol-hash symbol=?))
(define k-built-in-only-fill!
  (subr (maxeff (read @globals) (read @t) (write @t) (alloc @t)) ((listof symbol acyclic)) unit)
  (lambda (ns)
    (if (null? ns)
        #u
        (begin (table-set! k-built-in-only-table (car ns) #t) (k-built-in-only-fill! (cdr ns))))))
(define k-built-in-only-filled unit
  (k-built-in-only-fill!
   (list '%sched '%processes:spawn-process '%processes:send '%processes:receive
         '%processes:icell-get '%processes:icell-put! '%processes:par2 '%processes:cell-event
         '%processes:mailbox-event '%processes:or-event '%processes:sync
         '%processes:clock-event '%processes:stdin-event '%processes:race2 '%processes:attempt1
         '%processes:self
         '%processes:spawn-monitored
         ;; What a syscall's declaration expands into
         ;; (`docs/research/syscalls.md`).
         '%syscall-require '%syscall0 '%syscall1 '%syscall2 '%syscall3 '%syscall4 '%syscall5
         '%syscall6)))
(define k-built-in-only? (->* (symbol) bool)
  (lambda (s) (table-ref k-built-in-only-table s #f)))
;; Whether the innermost binding of `s` was made at depth `mark` or after.
(define k-bound-since? (->* (symbol int) bool)
  (lambda (s mark)
    (let ((ds (table-ref (get k-depths) s nil))) (and (not (null? ds)) (>= (car ds) mark)))))
;; Of names `ns`, those whose innermost binding is older than `mark`.
(define k-bound-before (->* (k-names int) k-names)
  (lambda (ns mark)
    (cond ((null? ns) nil)
          ((k-bound-since? (car ns) mark) (k-bound-before (cdr ns) mark))
          (else (the k-names (cons (car ns) (k-bound-before (cdr ns) mark)))))))
;; `free`, the names a `(with m …)`'s body uses, less those bound since `m`
;; is, where `m` is `%include`: an include's names are the module's own,
;; and the item's lambda's parameter shadows them (`TODO.md` §69).
(define k-include-free (->* (symbol k-names) k-names)
  (lambda (m free)
    (let ((ds (table-ref (get k-depths) m nil)))
      (if (or (null? ds) (not (symbol=? m '%include)))
          free
          (k-bound-before free (+ (car ds) 1))))))
;; The type a test narrowed binding `d` of `s` to (the innermost), or `t`.
(define k-narrowed-of (->* (k-narrows symbol int int) int)
  (lambda (ns s d t)
    (cond ((null? ns) t)
          ((and (symbol=? (extract (car ns) 1) s) (= (extract (car ns) 2) d)) (extract (car ns) 3))
          (else (k-narrowed-of (cdr ns) s d t)))))
;; Whether `name` is the hidden global every load of a file is
;; (`parse-loaded`; `TODO.md` §68).
(define k-shared-name? (->* (symbol) bool)
  (lambda (name)
    (let ((n (symbol->string name)))
      (and (>= (string-length n) 8) (string=? (substring n 0 8) "%shared:")))))
;; What `s` is where it is used: its innermost binding, as a test may have
;; narrowed it; none, if that is broken. While a module read from a file is
;; checked, a binding made before it began only if it is a standard one, or
;; the hidden global of a file loaded (`k-shared-name?`).
(define k-lookup (->* (symbol) int)
  (lambda (s)
    (let ((t (k-lookup-seen s)))
      (if (and (>= t 0) (k-hidden-standard? s t)) -1 t))))
;; What `s` is where it is used as a value: as `k-lookup` says, a load's
;; module type with each abstract type a description of the hidden global's
;; own, so that every binding of a load of the file has the same types
;; (`strengthened`); -1 if unbound.
(define k-lookup-used (->* (symbol) int)
  (lambda (s)
    (let ((t (k-lookup s)))
      (if (< t 0) t (k-strengthened s t)))))
;; Only a module's type with abstract types, of a load, is: the name looked
;; at last, as most are of no module.
(define k-strengthened (->* (symbol int) int)
  (lambda (s t)
    (tagcase (k-get (k-resolve t))
      (ty-module (abs ds vs)
        (if (or (null? abs) (not (k-shared-name? s)))
            t
            (k-ty-new (ty-module nil (k-abs-shown abs ds) vs))))
      (else y t))))
(define k-abs-shown (->* (k-parts k-parts) k-parts)
  (lambda (abs ds)
    (if (null? abs)
        ds
        (cons (tup (1 (extract (car abs) 1)) (2 (k-ty-new (ty-var (extract (car abs) 2)))))
              (k-abs-shown (cdr abs) ds)))))
;; Whether `s`, bound at `t`, is a standard name only the module files built
;; in may name, named elsewhere.
(define k-hidden-standard? (->* (symbol int) bool)
  (lambda (s t)
    (and (k-built-in-only? s) (= (get k-in-built-in) 0) (= (get k-syscall-expanding) 0)
         (= t (k-std-type s)))))
(define k-lookup-seen (->* (symbol) int)
  (lambda (s)
    (let ((st (table-ref (get k-env) s nil)) (mark (get k-hide-mark)))
      (cond ((or (null? st) (not (null? (k-broken-why s)))) -1)
            ((or (< mark 0) (k-bound-since? s mark)
                 (k-shared-name? s))
             (k-narrowed-of (get k-narrowed) s (k-length st) (car st)))
            (else (k-std-type s))))))
;; The same, broken or not.
(define k-lookup-raw (->* (symbol) int)
  (lambda (s) (let ((st (table-ref (get k-env) s nil))) (if (null? st) -1 (car st)))))
;; What an unbound name's use says: why, if it is broken.
(define k-unbound (->* (symbol) string)
  (lambda (s)
    (let ((why (k-broken-why s)) (n (symbol->string s)))
      (if (null? why)
          (if (or (string=? n "syscall-available?")
                  (and (>= (string-length n) 19)
                   (string=? (substring n 0 19) "%syscall-available:")))
              "`syscall-available?` takes the name of a syscall declared"
              (k-cat3 "unbound variable `" n "`"))
          (k-cat5 "`" n "` is broken, " (car why) ": define it again to use it")))))
;; Whether `at` is the identity `a`, `b`, `k`.
(define k-at-is? (->* (k-at int int int) bool)
  (lambda (at a b k) (and (= (extract at 1) a) (= (extract at 2) b) (= (extract at 3) k))))
(define k-no-operator k-op-mark (tup (1 '||) (2 (tup (1 -1) (2 -1) (3 -1)))))
(define k-operator (ref k-op-mark @t) (new k-no-operator))
;; The standard operations a rule checks at each call, by their name there:
;; named only as a call's operator, so that no other name, and no procedure
;; given one, can call them unchecked.
(define k-second-class? (->* (symbol) bool)
  (lambda (s)
    (let ((n (symbol->string s)))
      (or (string=? n "cwcc") (string=? n "certify-length") (string=? n "certify-acyclic")
          (string=? n "certify-nat") (string=? n "native-procedure")))))
(define k-operator? (->* (symbol int int int) bool)
  (lambda (s a b k)
    (let ((o (get k-operator)))
      (and (symbol=? (extract o 1) s) (k-at-is? (extract o 2) a b k)))))
(define k-named-only (->* (symbol) string)
  (lambda (s)
    (string-append "`" (symbol->string s)
                   "` is named only to call it: its calls are checked where it is named")))
;; Whether `m` is `#%fx`, the module of the standard bindings, which
;; nothing binds: `(with #%fx n)` is the standard `n` wherever it is,
;; shadowed or redefined (`TODO.md` §46).
(define k-fx-module? (->* (symbol) bool)
  (lambda (m) (string=? (symbol->string m) "#%fx")))
;; The name a `(with #%fx n)`'s body names, `||` if none.
(define k-fx-name (->* (kx) symbol)
  (lambda (body) (tagcase body (x-var (n c d cdk) n) (else y '||))))
;; An operator's mark: its variable's name and identity, past `proj` and
;; `the`.
(define k-operator-mark (->* (kx) k-op-mark)
  (lambda (f)
    (tagcase f
      (x-var (s a b abk) (tup (1 s) (2 (tup (1 a) (2 b) (3 abk)))))
      (x-proj (body ds a b abk) (k-operator-mark body))
      (x-the (t e a b abk) (k-operator-mark e))
      ;; `(with #%fx n)`: `n`, as the `with`.
      (x-with (m body a b abk)
        (tagcase body
          (x-var (n c d cdk)
            (if (k-fx-module? m) (tup (1 n) (2 (tup (1 a) (2 b) (3 abk)))) k-no-operator))
          (else y k-no-operator)))
      (else y k-no-operator))))
;; A flag, off, for a new innermost binding of `s`.
(define k-push-flag (->* (k-flags symbol) unit)
  (lambda (flags s)
    (table-set! (get flags) s (the (listof bool acyclic) (cons #f (table-ref (get flags) s nil))))))
;; The depth of a new innermost binding of `s`, the next.
(define k-push-depth (->* (symbol) unit)
  (lambda (s)
    (let ((ds (table-ref (get k-depths) s nil)))
      (table-set! (get k-depths) s (the k-stack (cons (get k-depth) ds))))))
(define k-bind (->* (symbol int) unit)
  (lambda (s t)
    (begin
      (table-set! (get k-env) s (cons t (table-ref (get k-env) s nil)))
      (k-push-depth s)
      (k-push-flag k-known s)
      (k-push-flag k-global s)
      (k-push-flag k-fixed s)
      (set k-trail (cons s (get k-trail)))
      (set k-depth (+ (get k-depth) 1)))))
(define k-mark (->* () int) (lambda () (get k-depth)))
;; `s`'s innermost binding, now of type `t`.
(define k-rebind (->* (symbol int) unit)
  (lambda (s t) (table-set! (get k-env) s (cons t (cdr (table-ref (get k-env) s nil))))))
(define k-unbind-to (->* (int) unit)
  (lambda (m)
    (if (<= (get k-depth) m)
        #u
        (let ((s (car (get k-trail))))
          (begin
            (table-set! (get k-env) s (cdr (table-ref (get k-env) s nil)))
            (table-set! (get k-depths) s (cdr (table-ref (get k-depths) s nil)))
            (table-set! (get k-known) s (cdr (table-ref (get k-known) s nil)))
            (table-set! (get k-global) s (cdr (table-ref (get k-global) s nil)))
            (table-set! (get k-fixed) s (cdr (table-ref (get k-fixed) s nil)))
            (set k-trail (cdr (get k-trail)))
            (set k-depth (- (get k-depth) 1))
            (k-unbind-to m))))))

;; Note the binding of `n` that many from the innermost as known.
(define k-set-nth-true (->* ((listof bool acyclic) int) (listof bool acyclic))
  (lambda (bs i)
    (cond ((null? bs) bs)
          ((= i 0) (the (listof bool acyclic) (cons #t (cdr bs))))
          (else (the (listof bool acyclic) (cons (car bs) (k-set-nth-true (cdr bs) (- i 1))))))))
(define k-note-known (->* (symbol int) unit)
  (lambda (n i) (table-set! (get k-known) n (k-set-nth-true (table-ref (get k-known) n nil) i))))
;; Whether the binding `n` names is of a known procedure.
(define k-known? (->* (symbol) bool)
  (lambda (n) (let ((st (table-ref (get k-known) n nil))) (and (not (null? st)) (car st)))))
;; Note the innermost binding of `n` as a global.
(define k-note-global (->* (symbol) unit)
  (lambda (n) (table-set! (get k-global) n (k-set-nth-true (table-ref (get k-global) n nil) 0))))
;; Bind `n`, at top level, to a value of type `t`: a global.
(define k-bind-global (->* (symbol int) unit)
  (lambda (n t) (begin (k-bind n t) (k-note-global n))))
;; Whether the binding `n` names is a global's.
(define k-global? (->* (symbol) bool)
  (lambda (n) (let ((st (table-ref (get k-global) n nil))) (and (not (null? st)) (car st)))))
(define k-note-fixed (->* (symbol) unit)
  (lambda (n) (table-set! (get k-fixed) n (k-set-nth-true (table-ref (get k-fixed) n nil) 0))))
(define k-fixed? (->* (symbol) bool)
  (lambda (n) (let ((st (table-ref (get k-fixed) n nil))) (and (not (null? st)) (car st)))))

(define k-dscope (ref k-scope @t) (new nil))
(define k-find-desc (->* (k-scope symbol) (listof k-ds acyclic))
  (lambda (ds s)
    (cond ((null? ds) nil)
          ((symbol=? (car (car ds)) s) (cons (cdr (car ds)) nil))
          (else (k-find-desc (cdr ds) s)))))
;; What `s` means as a description: none or one.
(define k-lookup-desc (->* (symbol) (listof k-ds acyclic))
  (lambda (s) (k-find-desc (get k-dscope) s)))
(define k-push-desc (->* (symbol k-ds) unit)
  (lambda (n d) (set k-dscope (cons (cons n d) (get k-dscope)))))

;; How many `with` bodies are being read (`k-with-mark`): where none is, no
;; type name is looked for among `with`s' modules.
(define k-with-depth (ref int @t) (new 0))
;; In a `(with m …)` body, a mark in the description scope, `%with:m`, so
;; that a type name bound before it is `m`'s, if `m` gives it: `with`
;; shadows (FX-91 §2.3.19). `#%fx`'s are the standard's.
(define k-with-mark (->* (symbol) unit)
  (lambda (m)
    (if (k-fx-module? m)
        #u
        (begin (set k-with-depth (+ (get k-with-depth) 1))
               (k-push-desc (string->symbol (string-append "%with:" (symbol->string m)))
                            (ds-var -1 0))))))
;; The end of a `with` body that `k-with-mark` marked (its scope restored by
;; the caller).
(define k-with-unmark (->* (symbol) unit)
  (lambda (m)
    (if (k-fx-module? m) #u (set k-with-depth (- (get k-with-depth) 1)))))
;; The modules of the `with`s whose bodies `s` is read in since it was last
;; bound, innermost first: each shadows what `s` was before it. As
;; `parse.rs`'s `withs_over`.
(define k-withs-over (->* (symbol) k-names)
  (lambda (s)
    (letrec ((walk (subr (maxeff kreads (alloc @t)) (k-scope) k-names)
                (lambda (ds)
                  (if (null? ds)
                      nil
                      (let ((n (symbol->string (car (car ds)))))
                        (cond ((symbol=? (car (car ds)) s) nil)
                              ((and (> (string-length n) 6) (string=? (substring n 0 6) "%with:"))
                               (cons (string->symbol (substring n 6 (string-length n)))
                                     (walk (cdr ds))))
                              (else (walk (cdr ds)))))))))
      (if (= (get k-with-depth) 0) nil (walk (get k-dscope))))))
;; Each `select` node a type name in a `with` body was read as, and what the
;; name meant outside, should the module not give it: a type, or -1.
(define k-with-fallbacks (ref k-fallbacks @t) (new nil))
;; Type name `sym`, read in the bodies of `with`s of modules `withs`
;; (innermost first): `(select m sym)` of the innermost, which, where `m`
;; does not give it, is the next's, and so on out to `outer`, what `sym`
;; means here otherwise, or -1. As `parse.rs`'s `with_selected`.
(define k-with-selected (->* (k-names symbol int) int)
  (lambda (withs sym outer)
    (if (null? withs)
        outer
        (let* ((t (k-with-selected (cdr withs) sym outer))
               (node (k-ty-new (ty-select (car withs) sym))))
          (begin (set k-with-fallbacks (cons (tup (1 node) (2 t)) (get k-with-fallbacks)))
                 node)))))
;; Of those, each applied, `(f d …)`: its `select` node and the application,
;; which is what falls back (`k-with-applied`).
(define k-with-apps (ref k-fallbacks @t) (new nil))
;; The entry of `fs` for node `node`, or `none`.
(define k-fallback-in (->* (k-fallbacks int int) int)
  (lambda (fs node none)
    (letrec ((find (subr kreads (k-fallbacks) int)
                (lambda (fs)
                  (cond ((null? fs) none)
                        ((= (extract (car fs) 1) node) (extract (car fs) 2))
                        (else (find (cdr fs)))))))
      (find fs))))
;; What `select` node `node`, a `with`'s, falls back to (`k-with-selected`):
;; a type, or -1 if nothing; -2 if it is not a `with`'s.
(define k-with-fallback (->* (int) int)
  (lambda (node) (k-fallback-in (get k-with-fallbacks) node -2)))
;; The application whose `select` node, a `with`'s, is `node`, or -1
;; (`k-with-applied`).
(define k-with-app-of (->* (int) int)
  (lambda (node) (k-fallback-in (get k-with-apps) node -1)))

;; How many fresh regions have been made, for naming the next.
(define k-fresh (ref int @t) (new 0))
(define k-fresh-region (->* (string) k-region)
  (lambda (base)
    (let ((n (+ (get k-fresh) 1)))
      (begin (set k-fresh n) (r-fresh n (k-cat3 base "." (int->string n)))))))

;; How deep in abbreviations' expansions reading is.
(define k-expanding (ref int @t) (new 0))

(define k-extracts (ref k-facts @t) (new nil))
;; Each expression synthesized: where it starts and ends, and a summary of
;; its effect for a compiler, each a stronger claim on what the code may do
;; than the one before, so that the greater of two is the safe one: 0 pure
;; (no atom at all, so no `spin` either); 1 reads only; 2 anything else; 3
;; anything else that may also keep its continuation for later, write a
;; global, or do what an effect variable stands for, which a global's value
;; may change across. Newest first. The Rust checker's `effect_summaries` is
;; the same.
(define k-effect-notes (ref k-facts @t) (new nil))
;; `notes` onto `acc`.
(define k-add-effect-facts (->* (k-facts k-facts) k-facts)
  (lambda (notes acc)
    (if (null? notes)
        acc
        (k-add-effect-facts (cdr notes) (the k-facts (cons (car notes) acc))))))
;; What checking found, for a compiler and the evaluator (`k-noted`): the
;; facts, and each expression's effect summary (`k-effect-notes`).
(define checked-extracts (->* () k-facts)
  (lambda () (k-add-effect-facts (get k-effect-notes) (get k-extracts))))
(define checked-effects (->* () k-facts) (lambda () (get k-effect-notes)))
;; Whether `r` is a global's binding, or every global's.
(define k-globals-region? (->* (k-region) bool)
  (lambda (r) (tagcase r (r-global (g) #t) (r-globals () #t) (else y #f))))
;; Whether `e` may keep its continuation for later, write a global, or do
;; what an effect variable stands for.
(define k-disrupts? (->* (k-eff) bool)
  (lambda (e)
    (and (not (null? e))
         (or (tagcase (car e)
               (a-comefrom (r) #t)
               (a-var (v) #t)
               (a-app (v ds) #t)
               (a-write (r) (k-globals-region? r))
               (else y #f))
             (k-disrupts? (cdr e))))))
;; Whether `a` reads.
(define k-read-atom? (->* (k-atom) bool)
  (lambda (a) (tagcase a (a-read (r) #t) (else y #f))))
(define k-reads-only? (->* (k-eff) bool)
  (lambda (e) (or (null? e) (and (k-read-atom? (car e)) (k-reads-only? (cdr e))))))
(define k-summary (->* (k-eff) int)
  (lambda (e) (cond ((null? e) 0) ((k-reads-only? e) 1) ((k-disrupts? e) 3) (else 2))))

(define k-with-vals (ref k-with-list @t) (new nil))
;; The same, by where each starts: a converted file's imports are `with`s,
;; hundreds of them, and each is looked up (`k-with-names`).
(define k-with-index (ref (table int k-with-list @t) @t)
  (new (make-table (lambda ((n int)) n) (lambda ((m int) (n int)) (= m n)))))
(define k-with-names-in
  (->* (k-with-list int int int) k-names)
  (lambda (ws a b k)
    (cond ((null? ws) nil)
          ((k-at-is? (extract (car ws) 1) a b k) (extract (car ws) 2))
          (else (k-with-names-in (cdr ws) a b k)))))
(define k-with-names (->* (int int int) k-names)
  (lambda (a b k) (k-with-names-in (table-ref (get k-with-index) a nil) a b k)))
;; Note `with` `w`, in the list and by where it starts.
(define k-note-with (->* (k-with-noted) unit)
  (lambda (w)
    (let ((a (extract (extract w 1) 1)))
      (begin (set k-with-vals (the k-with-list (cons w (get k-with-vals))))
             (table-set! (get k-with-index) a
                         (the k-with-list (cons w (table-ref (get k-with-index) a nil))))))))
;; Forget the `with`s noted.
(define k-forget-withs (->* () unit)
  (lambda ()
    (begin (set k-with-vals nil)
           (set k-with-index
                (make-table (lambda ((n int)) n) (lambda ((m int) (n int)) (= m n)))))))
(define k-hazard-mods (ref k-hazard-list @t) (new nil))
(define k-hazard-names-in (->* (k-hazard-list symbol) k-names)
  (lambda (hs m)
    (cond ((null? hs) nil)
          ((symbol=? (extract (car hs) 1) m) (extract (car hs) 2))
          (else (k-hazard-names-in (cdr hs) m)))))
(define k-reshapes (ref k-reshape-list @t) (new nil))
;; For a driver: the same as another checker found them.
(define checked-reshapes! (->* (k-reshape-list) unit)
  (lambda (rs) (set k-reshapes rs)))
;; For a driver: what `with`s another checker saw, as `k-with-vals` keeps
;; them, for a compiler given that checker's facts.
(define checked-withs! (->* (k-with-list) unit)
  (lambda (ws)
    (letrec ((each (subr kstate (k-with-list) unit)
                     (lambda (ws)
                       (if (null? ws) #u (begin (k-note-with (car ws)) (each (cdr ws)))))))
      (begin (k-forget-withs) (each (the k-with-list (reverse ws)))))))
;; The type variables made for modules' abstract types as each module was
;; bound (`k-name-module`): not forgotten, but kept from leaving.
(define k-module-vars (ref k-ids @t) (new nil))
(define k-select-map (ref k-selects @t) (new nil))
(define k-select-in (->* (k-selects symbol symbol int) int)
  (lambda (ss m n t)
    (cond ((null? ss) t)
          ((and (symbol=? (extract (car ss) 1) m) (symbol=? (extract (car ss) 2) n))
           (extract (car ss) 3))
          (else (k-select-in (cdr ss) m n t)))))
;; What `(select m n)`, node `t`, is while selects are resolved; else `t`.
(define k-select-of (->* (symbol symbol int) int)
  (lambda (m n t) (k-select-in (get k-select-map) m n t)))
(define k-param-map (ref k-params-given @t) (new nil))
(define k-param-in (->* (k-params-given int symbol int) int)
  (lambda (ps k n t)
    (cond ((null? ps) t)
          ((and (= (extract (car ps) 1) k) (symbol=? (extract (car ps) 2) n)) (extract (car ps) 3))
          (else (k-param-in (cdr ps) k n t)))))
;; What `(select $k n)`, node `t`, is while parameters are given; else `t`.
(define k-param-sel-of (->* (int symbol int) int)
  (lambda (k n t) (k-param-in (get k-param-map) k n t)))
;; `ts` but its last; and its last (-1 if none).
(define k-ids-but-last (->* (k-ids) k-ids)
  (lambda (ts) (if (or (null? ts) (null? (cdr ts))) nil (cons (car ts) (k-ids-but-last (cdr ts))))))
(define k-ids-last (->* (k-ids) int)
  (lambda (ts) (cond ((null? ts) -1) ((null? (cdr ts)) (car ts)) (else (k-ids-last (cdr ts)))))))))
