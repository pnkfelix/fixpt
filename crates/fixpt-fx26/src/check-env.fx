;;; The checker, in FX-26: its environment. The base types; what is in
;;; scope, value variables and description names; and what checking proves
;;; that running needs.
;;; Part of the checker, `check-types.fx` first (PLAN.md §11, step 10).

;; A module (`TODO.md` §34: the front end into modules, a file at a time);
;; what other files use re-exported after it.
(define check-env-module (module
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
(define k-basic (subr (maxeff kstate spin) (string) unit)
  (lambda (name)
    (let* ((s (string->symbol name)) (t (k-ty-new (ty-base s))))
      (set k-base (cons (cons s t) (get k-base))))))

;; Bindings, as lists of them are passed around.
(define-type k-bindings (listof (pairof symbol int @t) acyclic))
(define k-find (subr (maxeff (read @globals) (read @t)) (k-bindings symbol) int)
  (lambda (bs s)
    (cond ((null? bs) -1) ((symbol=? (car (car bs)) s) (cdr (car bs))) (else (k-find (cdr bs) s)))))

;; Value variables in scope: for each name, the types it is bound to,
;; innermost first; and the names bound, newest first, so that a scope is
;; left by unbinding back to a mark (`k-mark`, `k-unbind-to`). A lookup is
;; a table's, not a walk down every binding in scope.
(define-type k-stack (listof int acyclic))
(define k-env (ref (table symbol k-stack @t) @t) (new (make-table symbol-hash symbol=?)))
(define k-trail (ref k-names @t) (new nil))
(define k-depth (ref int @t) (new 0))
;; Whether each binding in `k-env` is of a known procedure: one a `define`,
;; `letrec`, `define-rec`, or a `let` of a `lambda` made. A call of one runs
;; code the checker has seen; a call of anything else might run a closure
;; fetched from the store. By binding, in step with `k-env`, not by name and
;; type, so a parameter that shadows one is not taken for it
;; (`docs/research/soundness-findings.md`, F1).
;; For each name, a flag for each of its bindings in `k-env`, innermost
;; first.
(define-type k-flags (ref (table symbol (listof bool acyclic) @t) @t))
(define k-known k-flags (new (make-table symbol-hash symbol=?)))
;; Whether each binding in `k-env` is a global: one a top-level definition
;; made. Naming one reads it, `(read (globals g))`, when
;; `k-globals-effects` says so, as the language will once every program
;; says what it reads (off until then).
(define k-global k-flags (new (make-table symbol-hash symbol=?)))
(define k-globals-effects (ref bool @t) (new #t))
;; The latent effect of the lambda checked last: for `define*`, what the
;; globals its lambda reads are.
(define k-last-latent (ref k-eff @t) (new nil))
;; For a driver: whether naming a global reads it.
(define check-globals-effects! (subr (maxeff (read @globals) (write @t)) (bool) unit)
  (lambda (on) (set k-globals-effects on)))
;; The type `s` is bound to, or -1.
;; Globals broken by a redefinition (`k-defining`): the name, how many
;; bindings it had then (so which one is broken), and why. A use of a broken
;; binding is an error saying why, until the name is defined again.
(define-type k-break (productof (1 symbol) (2 int) (3 string)))
(define k-broken (ref (listof k-break acyclic) @t) (new nil))
;; How many bindings `s` has now.
(define k-name-depth (subr (maxeff (read @globals) (read @t) spin) (symbol) int)
  (lambda (s) (k-length (table-ref (get k-env) s nil))))
;; Why `s`'s binding now is broken, if it is.
;; Whether `b` breaks the `d`th binding of `s`.
(define k-breaks? (subr (read @globals) (k-break symbol int) bool)
  (lambda (b s d) (and (symbol=? (extract b 1) s) (= (extract b 2) d))))
(define k-broken-why (subr (maxeff kreads spin) (symbol) k-strings)
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
;; How many of the newest `n` names bound, `ns`, are `s`.
(define k-bound-since (subr (maxeff (read @globals) (read @t) spin) (k-names symbol int) int)
  (lambda (ns s n)
    (cond ((or (null? ns) (<= n 0)) 0)
          ((symbol=? (car ns) s) (+ 1 (k-bound-since (cdr ns) s (- n 1))))
          (else (k-bound-since (cdr ns) s (- n 1))))))
;; What `s` is where it is used: its innermost binding; none, if that is
;; broken. While a module read from a file is checked, a binding made
;; before it began only if it is a standard one.
(define k-lookup (subr (maxeff (read @globals) (read @t) spin) (symbol) int)
  (lambda (s)
    (let ((st (table-ref (get k-env) s nil)) (mark (get k-hide-mark)))
      (cond ((or (null? st) (not (null? (k-broken-why s)))) -1)
            ((or (< mark 0) (> (k-bound-since (get k-trail) s (- (get k-depth) mark)) 0)) (car st))
            (else (k-find (get k-std) s))))))
;; The same, broken or not.
(define k-lookup-raw (subr (maxeff (read @globals) (read @t) spin) (symbol) int)
  (lambda (s) (let ((st (table-ref (get k-env) s nil))) (if (null? st) -1 (car st)))))
;; What an unbound name's use says: why, if it is broken.
(define k-unbound (subr (maxeff (read @globals) (read @t) (alloc @t) spin) (symbol) string)
  (lambda (s)
    (let ((why (k-broken-why s)) (n (symbol->string s)))
      (if (null? why)
          (k-cat3 "unbound variable `" n "`")
          (k-cat5 "`" n "` is broken, " (car why) ": define it again to use it")))))
;; A flag, off, for a new innermost binding of `s`.
(define k-push-flag (subr (maxeff kstate spin) (k-flags symbol) unit)
  (lambda (flags s)
    (table-set! (get flags) s (the (listof bool acyclic) (cons #f (table-ref (get flags) s nil))))))
(define k-bind (subr (maxeff kstate spin) (symbol int) unit)
  (lambda (s t)
    (begin
      (table-set! (get k-env) s (cons t (table-ref (get k-env) s nil)))
      (k-push-flag k-known s)
      (k-push-flag k-global s)
      (set k-trail (cons s (get k-trail)))
      (set k-depth (+ (get k-depth) 1)))))
(define k-mark (subr (maxeff (read @globals) (read @t)) () int) (lambda () (get k-depth)))
(define k-unbind-to (subr (maxeff kstate spin) (int) unit)
  (lambda (m)
    (if (<= (get k-depth) m)
        #u
        (let ((s (car (get k-trail))))
          (begin
            (table-set! (get k-env) s (cdr (table-ref (get k-env) s nil)))
            (table-set! (get k-known) s (cdr (table-ref (get k-known) s nil)))
            (table-set! (get k-global) s (cdr (table-ref (get k-global) s nil)))
            (set k-trail (cdr (get k-trail)))
            (set k-depth (- (get k-depth) 1))
            (k-unbind-to m))))))

;; Note the binding of `n` that many from the innermost as known.
(define k-set-nth-true (subr (read @globals) ((listof bool acyclic) int) (listof bool acyclic))
  (lambda (bs i)
    (cond ((null? bs) bs)
          ((= i 0) (the (listof bool acyclic) (cons #t (cdr bs))))
          (else (the (listof bool acyclic) (cons (car bs) (k-set-nth-true (cdr bs) (- i 1))))))))
(define k-note-known (subr (maxeff kstate spin) (symbol int) unit)
  (lambda (n i) (table-set! (get k-known) n (k-set-nth-true (table-ref (get k-known) n nil) i))))
;; Whether the binding `n` names is of a known procedure.
(define k-known? (subr (maxeff (read @globals) (read @t) spin) (symbol) bool)
  (lambda (n) (let ((st (table-ref (get k-known) n nil))) (and (not (null? st)) (car st)))))
;; Note the innermost binding of `n` as a global.
(define k-note-global (subr (maxeff kstate spin) (symbol) unit)
  (lambda (n) (table-set! (get k-global) n (k-set-nth-true (table-ref (get k-global) n nil) 0))))
;; Bind `n`, at top level, to a value of type `t`: a global.
(define k-bind-global (subr (maxeff kstate spin) (symbol int) unit)
  (lambda (n t) (begin (k-bind n t) (k-note-global n))))
;; Whether the binding `n` names is a global's.
(define k-global? (subr (maxeff (read @globals) (read @t) spin) (symbol) bool)
  (lambda (n) (let ((st (table-ref (get k-global) n nil))) (and (not (null? st)) (car st)))))

;; Description names in scope, innermost first.
(define-type k-scope (listof (pairof symbol k-ds @t) acyclic))
(define k-dscope (ref k-scope @t) (new nil))
(define k-find-desc (subr (maxeff kreads (alloc @t)) (k-scope symbol) (listof k-ds acyclic))
  (lambda (ds s)
    (cond ((null? ds) nil)
          ((symbol=? (car (car ds)) s) (cons (cdr (car ds)) nil))
          (else (k-find-desc (cdr ds) s)))))
;; What `s` means as a description: none or one.
(define k-lookup-desc (subr (maxeff kreads (alloc @t)) (symbol) (listof k-ds acyclic))
  (lambda (s) (k-find-desc (get k-dscope) s)))
(define k-push-desc (subr kstate (symbol k-ds) unit)
  (lambda (n d) (set k-dscope (cons (cons n d) (get k-dscope)))))

;; How many fresh regions have been made, for naming the next.
(define k-fresh (ref int @t) (new 0))
(define k-fresh-region (subr kstate (string) k-region)
  (lambda (base)
    (let ((n (+ (get k-fresh) 1)))
      (begin (set k-fresh n) (r-fresh n (k-cat3 base "." (int->string n)))))))

;; How deep in abbreviations' expansions reading is.
(define k-expanding (ref int @t) (new 0))

;; What checking proved that running needs: each `extract`'s field, by
;; position, keyed by where the `extract` is. Only the product's type says.
(define-type k-fact (productof (1 int) (2 int) (3 int)))
(define-type k-facts (listof k-fact acyclic))
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
;; An effect note as `checked-extracts` gives it: its summary n as -1 - n.
(define k-note-as-fact (subr (read @globals) (k-fact) k-fact)
  (lambda (n) (product (1 (extract n 1)) (2 (extract n 2)) (3 (- -1 (extract n 3))))))
(define k-add-effect-facts (subr (read @globals) (k-facts k-facts) k-facts)
  (lambda (notes acc)
    (if (null? notes)
        acc
        (k-add-effect-facts (cdr notes) (the k-facts (cons (k-note-as-fact (car notes)) acc))))))
;; What checking found, for a compiler: each `extract`'s field, `(a b i)`;
;; and each expression's effect summary (`k-effect-notes`), `(a b n)` with n
;; negative, the summary -1 - n.
(define checked-extracts (subr kreads () k-facts)
  (lambda () (k-add-effect-facts (get k-effect-notes) (get k-extracts))))
(define checked-effects (subr kreads () k-facts) (lambda () (get k-effect-notes)))
;; Whether `r` is a global's binding, or every global's.
(define k-globals-region? (subr pure (k-region) bool)
  (lambda (r) (tagcase r (r-global (g) #t) (r-globals () #t) (else y #f))))
;; Whether `e` may keep its continuation for later, write a global, or do
;; what an effect variable stands for.
(define k-disrupts? (subr (read @globals) (k-eff) bool)
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
(define k-read-atom? (subr pure (k-atom) bool)
  (lambda (a) (tagcase a (a-read (r) #t) (else y #f))))
(define k-reads-only? (subr (read @globals) (k-eff) bool)
  (lambda (e) (or (null? e) (and (k-read-atom? (car e)) (k-reads-only? (cdr e))))))
(define k-summary (subr (read @globals) (k-eff) int)
  (lambda (e) (cond ((null? e) 0) ((k-reads-only? e) 1) ((k-disrupts? e) 3) (else 2))))

;; Each `with` checked, where it is, and its module's values' names, newest
;; first: a `with`'s body sees them, once checking has found them.
(define-type k-with-noted (productof (1 int) (2 int) (3 k-names)))
(define-type k-with-list (listof k-with-noted acyclic))
(define k-with-vals (ref k-with-list @t) (new nil))
(define k-with-names-in (subr (maxeff (read @globals) (read @t)) (k-with-list int int) k-names)
  (lambda (ws a b)
    (cond ((null? ws) nil)
          ((and (= (extract (car ws) 1) a) (= (extract (car ws) 2) b)) (extract (car ws) 3))
          (else (k-with-names-in (cdr ws) a b)))))
(define k-with-names (subr (maxeff (read @globals) (read @t)) (int int) k-names)
  (lambda (a b) (k-with-names-in (get k-with-vals) a b)))
;; Each module given where a type of fewer values, or the same in another
;; order, is wanted (`k-reshape-at`): where, and for each value that type
;; has, its position in the module given. Made into a module of that layout.
(define-type k-reshaped (productof (1 int) (2 int) (3 k-ids)))
(define-type k-reshape-list (listof k-reshaped acyclic))
(define k-reshapes (ref k-reshape-list @t) (new nil))
;; For a driver: the same as another checker found them.
(define checked-reshapes! (subr (maxeff (read @globals) (write @t)) (k-reshape-list) unit)
  (lambda (rs) (set k-reshapes rs)))
;; For a driver: what `with`s another checker saw, as `k-with-vals` keeps
;; them, for a compiler given that checker's facts.
(define checked-withs! (subr (maxeff (read @globals) (write @t)) (k-with-list) unit)
  (lambda (ws) (set k-with-vals ws)))
;; The type variables made for modules' abstract types as each module was
;; bound (`k-name-module`): not forgotten, but kept from leaving.
(define k-module-vars (ref k-ids @t) (new nil))
;; While a type's `select`s are resolved (`k-resolve-selects`): what each
;; is, `(m t)` and the type; none otherwise.
(define-type k-selected (productof (1 symbol) (2 symbol) (3 int)))
(define-type k-selects (listof k-selected acyclic))
(define k-select-map (ref k-selects @t) (new nil))
(define k-select-in (subr (maxeff (read @globals) (read @t)) (k-selects symbol symbol int) int)
  (lambda (ss m n t)
    (cond ((null? ss) t)
          ((and (symbol=? (extract (car ss) 1) m) (symbol=? (extract (car ss) 2) n))
           (extract (car ss) 3))
          (else (k-select-in (cdr ss) m n t)))))
;; What `(select m n)`, node `t`, is while selects are resolved; else `t`.
(define k-select-of (subr (maxeff (read @globals) (read @t)) (symbol symbol int) int)
  (lambda (m n t) (k-select-in (get k-select-map) m n t)))
;; While a dependent procedure's parameters are given (`k-instantiate-params`):
;; what each `(select $k n)` is, `(k n)` and the type; none otherwise.
(define-type k-param-given (productof (1 int) (2 symbol) (3 int)))
(define-type k-params-given (listof k-param-given acyclic))
(define k-param-map (ref k-params-given @t) (new nil))
(define k-param-in (subr (maxeff (read @globals) (read @t)) (k-params-given int symbol int) int)
  (lambda (ps k n t)
    (cond ((null? ps) t)
          ((and (= (extract (car ps) 1) k) (symbol=? (extract (car ps) 2) n)) (extract (car ps) 3))
          (else (k-param-in (cdr ps) k n t)))))
;; What `(select $k n)`, node `t`, is while parameters are given; else `t`.
(define k-param-sel-of (subr (maxeff (read @globals) (read @t)) (int symbol int) int)
  (lambda (k n t) (k-param-in (get k-param-map) k n t)))
;; `ts` but its last; and its last (-1 if none).
(define k-ids-but-last (subr (maxeff (read @globals) (alloc @t) spin) (k-ids) k-ids)
  (lambda (ts) (if (or (null? ts) (null? (cdr ts))) nil (cons (car ts) (k-ids-but-last (cdr ts))))))
(define k-ids-last (subr (maxeff (read @globals) spin) (k-ids) int)
  (lambda (ts) (cond ((null? ts) -1) ((null? (cdr ts)) (car ts)) (else (k-ids-last (cdr ts))))))))

(define k-int (with check-env-module k-int))
(define k-bool (with check-env-module k-bool))
(define k-string (with check-env-module k-string))
(define k-unit (with check-env-module k-unit))
(define k-char (with check-env-module k-char))
(define k-f64 (with check-env-module k-f64))
(define k-symbol (with check-env-module k-symbol))
(define k-void (with check-env-module k-void))
(define k-base (with check-env-module k-base))
(define k-basic (with check-env-module k-basic))
(define-type k-bindings (select check-env-module k-bindings))
(define k-find (with check-env-module k-find))
(define k-env (with check-env-module k-env))
(define k-trail (with check-env-module k-trail))
(define k-depth (with check-env-module k-depth))
(define k-known (with check-env-module k-known))
(define k-global (with check-env-module k-global))
(define k-globals-effects (with check-env-module k-globals-effects))
(define k-last-latent (with check-env-module k-last-latent))
(define check-globals-effects! (with check-env-module check-globals-effects!))
(define-type k-break (select check-env-module k-break))
(define k-broken (with check-env-module k-broken))
(define k-name-depth (with check-env-module k-name-depth))
(define k-hide-mark (with check-env-module k-hide-mark))
(define k-std-dscope (with check-env-module k-std-dscope))
(define k-lookup (with check-env-module k-lookup))
(define k-lookup-raw (with check-env-module k-lookup-raw))
(define k-unbound (with check-env-module k-unbound))
(define k-bind (with check-env-module k-bind))
(define k-mark (with check-env-module k-mark))
(define k-unbind-to (with check-env-module k-unbind-to))
(define k-note-known (with check-env-module k-note-known))
(define k-known? (with check-env-module k-known?))
(define k-bind-global (with check-env-module k-bind-global))
(define k-global? (with check-env-module k-global?))
(define-type k-scope (select check-env-module k-scope))
(define k-dscope (with check-env-module k-dscope))
(define k-lookup-desc (with check-env-module k-lookup-desc))
(define k-push-desc (with check-env-module k-push-desc))
(define k-fresh (with check-env-module k-fresh))
(define k-fresh-region (with check-env-module k-fresh-region))
(define k-expanding (with check-env-module k-expanding))
(define-type k-facts (select check-env-module k-facts))
(define k-extracts (with check-env-module k-extracts))
(define k-effect-notes (with check-env-module k-effect-notes))
(define checked-extracts (with check-env-module checked-extracts))
(define checked-effects (with check-env-module checked-effects))
(define k-globals-region? (with check-env-module k-globals-region?))
(define k-summary (with check-env-module k-summary))
(define-type k-with-list (select check-env-module k-with-list))
(define k-with-vals (with check-env-module k-with-vals))
(define k-with-names (with check-env-module k-with-names))
(define-type k-reshape-list (select check-env-module k-reshape-list))
(define k-reshapes (with check-env-module k-reshapes))
(define checked-reshapes! (with check-env-module checked-reshapes!))
(define checked-withs! (with check-env-module checked-withs!))
(define k-module-vars (with check-env-module k-module-vars))
(define-type k-selects (select check-env-module k-selects))
(define k-select-map (with check-env-module k-select-map))
(define k-select-of (with check-env-module k-select-of))
(define-type k-params-given (select check-env-module k-params-given))
(define k-param-map (with check-env-module k-param-map))
(define k-param-in (with check-env-module k-param-in))
(define k-param-sel-of (with check-env-module k-param-sel-of))
(define k-ids-but-last (with check-env-module k-ids-but-last))
(define k-ids-last (with check-env-module k-ids-last))
