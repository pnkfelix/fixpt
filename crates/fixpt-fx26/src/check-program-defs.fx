;;; The checker, in FX-26: what a program's top-level forms define, as
;;; `check-program.fx` checks them: their clauses (a convention's), the
;;; warnings and the lines a driver reads, the globals they bind, each
;;; `define-rec` group read and its termination noted, `define*` and `->*`
;;; checked, and what a redefinition reaches. Apart from `check-program.fx`
;;; since 2026-10-31 (`TODO.md` §188), which makes it of the modules it is
;;; given and gives on all it defines.
;;; A file of one expression (`load-input`, `TODO.md` §68).


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
       (reader-types (load-module "fx26:reader-types.fx")))
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
           (check-print-parts (select check-print-parts-types check-print-parts-sig)))
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
(import check-effects k-atom-region k-one k-insert k-contains?)
(import check-resolve k-defs k-free-into k-has-region-in? k-last-uses k-reset k-runs)
(import check-read k-items k-name-of k-sfail k-symbol-head)
(define k-names-onto (with check-modorder k-names-onto))

;; The generative type `name` may see inside, as one of its conversions, or
;; -1; no longer, once asked.
(define k-take-inside (->* (symbol) int)
  (lambda (name)
    (letrec ((find (subr kreads (k-named) int)
                   (lambda (xs)
                     (cond ((null? xs) -1)
                           ((symbol=? (car (car xs)) name) (cdr (car xs)))
                           (else (find (cdr xs))))))
             (drop (subr (maxeff kreads (alloc @t)) (k-named) k-named)
                   (lambda (xs)
                     (cond ((null? xs) xs)
                           ((symbol=? (car (car xs)) name) (cdr xs))
                           (else (the k-named (cons (car xs) (drop (cdr xs)))))))))
      (let ((g (find (get k-inside))))
        (begin (if (>= g 0) (set k-inside (drop (get k-inside))) #u) g)))))
;;; `(define-convention name clause …)` (`TODO.md` §97, `docs/research/
;;; declared-conventions.md`): the clauses, each printed canonically and
;;; sorted by role, are those of the convention this implementation
;;; supports, as `native-convention` gives them; `convention.rs`, word for
;;; word.
(define k-conv-atoms string "a convention's clause holds names, integers and lists")
;; A name, not `#t`, `#f` or `#u`, which the Rust reader reads as no name.
(define k-conv-name? (->* (syn) bool)
  (lambda (s)
    (tagcase s
      (atom (d a b)
        (if (symbol? d)
            (let ((n (symbol->string d)))
              (not (and (> (string-length n) 0) (string=? (substring n 0 1) "#"))))
            #f))
      (else x #f))))
;; `s` printed canonically: atoms apart by one space, integers in decimal.
(define k-conv-text (->* (syn) string)
  (lambda (s)
    (tagcase s
      (atom (d a b)
        (if (datum-int? d)
            (int->string d)
            (if (k-conv-name? s) (symbol->string (k-name-of s "a name")) (k-sfail k-conv-atoms s))))
      (lst (items d a b) (string-append "(" (k-conv-texts items) ")"))
      (else x (k-sfail k-conv-atoms s)))))
(define k-conv-texts (->* ((listof syn acyclic)) string)
  (lambda (xs)
    (cond ((null? xs) "")
          ((null? (cdr xs)) (k-conv-text (car xs)))
          (else (string-append (k-conv-text (car xs)) " " (k-conv-texts (cdr xs)))))))
;; A clause, by its role: `cs` sorted by role, `c` after any of its own.
(define k-conv-insert (->* (k-clause k-clauses) k-clauses)
  (lambda (c cs)
    (cond ((null? cs) (the k-clauses (cons c nil)))
          ((string<? (extract c 1) (extract (car cs) 1)) (the k-clauses (cons c cs)))
          (else (the k-clauses (cons (car cs) (k-conv-insert c (cdr cs))))))))
;; A program's clauses, each its role, its text and itself, sorted.
(define k-conv-ours (->* ((listof syn acyclic) k-clauses) k-clauses)
  (lambda (xs acc)
    (if (null? xs)
        acc
        (let* ((c (car xs))
               (role (tagcase c
                       (lst (items d a b)
                         (if (and (not (null? items)) (k-conv-name? (car items)))
                             (symbol->string (k-name-of (car items) "a name"))
                             (k-sfail "a convention's clause is `(role …)`" c)))
                       (else x (k-sfail "a convention's clause is `(role …)`" c)))))
          (k-conv-ours (cdr xs)
                       (k-conv-insert (product (1 role) (2 (k-conv-text c)) (3 c)) acc))))))
;; Where a supported clause's role ends: at its first space or `)`.
(define k-conv-role-end (->* (string int) int)
  (lambda (t i)
    (cond ((= i (string-length t)) i)
          ((or (string=? (substring t i (+ i 1)) " ") (string=? (substring t i (+ i 1)) ")")) i)
          (else (k-conv-role-end t (+ i 1))))))
;; The supported clauses, sorted, `form` standing for where each is.
(define k-conv-theirs (->* ((listof string @t) syn k-clauses) k-clauses)
  (lambda (ts form acc)
    (if (null? ts)
        acc
        (let* ((t (car ts)) (role (substring t 1 (k-conv-role-end t 1))))
          (k-conv-theirs (cdr ts) form (k-conv-insert (product (1 role) (2 t) (3 form)) acc))))))
;; The clause of the convention as it was, accepted still in place of the
;; current one of its role (`fixpt_runtime::NATIVE_CONVENTION_OLDER`).
(define k-conv-older string
  "(closures (kind 41) (code-field 2) (first-free-field 3) (native-when-code-at-least code-lo))")
;; Two clauses of one role, the second.
(define k-conv-twice (->* (k-clauses) unit)
  (lambda (cs)
    (cond ((or (null? cs) (null? (cdr cs))) #u)
          ((string=? (extract (car cs) 1) (extract (car (cdr cs)) 1))
           (k-sfail (string-append "`define-convention`: two `" (extract (car cs) 1) "` clauses")
                    (extract (car (cdr cs)) 3)))
          (else (k-conv-twice (cdr cs))))))
(define k-conv-compare (->* (k-clauses k-clauses syn) unit)
  (lambda (ours theirs form)
    (let ((extra (lambda ((o k-clause))
                   (k-sfail (string-append "`define-convention`: this implementation's convention "
                                           "has no `" (extract o 1) "` clause")
                            (extract o 3))))
          (missing (lambda ((t k-clause))
                     (k-sfail (string-append "`define-convention`: no `" (extract t 1)
                                             "` clause, which this implementation's convention has")
                              form))))
      (cond ((null? ours) (if (null? theirs) #u (missing (car theirs))))
            ((null? theirs) (extra (car ours)))
            ((string=? (extract (car ours) 1) (extract (car theirs) 1))
             (if (or (string=? (extract (car ours) 2) (extract (car theirs) 2))
                     (string=? (extract (car ours) 2) k-conv-older))
                 (k-conv-compare (cdr ours) (cdr theirs) form)
                 (k-sfail (string-append "`define-convention`: the `" (extract (car ours) 1)
                                         "` clause is not this implementation's: "
                                         (extract (car theirs) 2))
                          (extract (car ours) 3))))
            ((string<? (extract (car ours) 1) (extract (car theirs) 1)) (extra (car ours)))
            (else (missing (car theirs)))))))
(define k-check-convention (->* (syn) unit)
  (lambda (form)
    (let* ((ours (k-conv-ours (cdr (cdr (k-items form "a convention's declaration"))) nil))
           (theirs (k-conv-theirs (the (listof string @t) (native-convention)) form nil)))
      (begin (k-conv-twice ours) (k-conv-compare ours theirs form)))))
;; The symbol `prefix` then `n` spells.
(define k-prefixed (->* (string string) symbol)
  (lambda (prefix n) (string->symbol (string-append prefix n))))
(define k-declare (->* (top) unit)
  (lambda (form)
    (tagcase form
      (t-define-type (name def a b)
        (cond
          ;; `(define-type f (dlambda …))`: a name for a description function.
          ((and (syn-symbol? name) (string=? (k-list-head def) "dlambda"))
           (k-push-desc (k-name-of name "expected a name") (ds-fun (k-parse-fun def -1))))
          ((syn-symbol? name)
            (begin (k-define-type (k-name-of name "expected a name") def a b) #u))
          (else
            (let ((items (k-items name "a type definition")))
              (if (null? items)
                  (k-sfail "expected a name" name)
                  (k-define-family (k-name-of (car items) "expected a name") (cdr items) def))))))
      (t-define-effect (name def a b)
        (let* ((n (k-name-of name "expected a name"))
               (e (k-parse-effect def)))
          (k-push-desc n (ds-eff e))))
      (t-define-convention (name form a b)
        (let ((n (k-name-of name "expected a name")))
          (begin (k-check-convention form) (k-push-desc n (ds-conv (cv-native))))))
      (t-define-generative (head rep a b)
        (let* ((name (k-define-generative head rep))
               (g (- (get k-ngens) 1))
               (n (symbol->string name)))
          ;; Only its own conversions, which follow, see inside it.
          (set k-inside (cons (cons (k-prefixed "down-" n) g)
                              (cons (cons (k-prefixed "up-" n) g) (get k-inside))))))
      (else y #u))))

(define k-declare-each (->* (k-tops) unit)
  (lambda (forms)
    (if (null? forms)
        #u
        (if (k-included? (car forms))
            (set k-ahead-stop (k-type-top-start (car forms)))
            (begin (if (k-read-in-order? (car forms)) #u (k-declare (car forms)))
                   (k-declare-each (cdr forms)))))))
;; Those warnings, as `k-forms` keeps lines: the first last.
(define k-types-again (->* (k-tops) k-out)
  (lambda (forms)
    (k-push-lines (k-again-lines (k-given-again (k-ahead-names-of forms nil #f) nil nil)) nil)))
;; The first pass: abbreviations, so that types can refer to each other in
;; any order. Values cannot: a definition sees only those before it. Each
;; abbreviation defined once, by name, is in scope before any is read, and
;; checked grounded once all are.
(define k-ahead (->* (k-tops) unit)
  (lambda (forms)
    (let ((names (k-ahead-names-of forms nil #t)))
      (begin
        (set k-ahead-stop -1)
        (set k-ahead-names nil)
        (set k-ahead-filled nil)
        (k-ahead-declare names names)
        (k-declare-each forms)
        (set k-ahead-names nil)
        (let ((filled (get k-ahead-filled)))
          (begin (set k-ahead-filled nil) (k-ground-filled (k-filled-reversed filled nil))
                 (k-note-closed-filled filled)))))))
;; Whether a form's lines are made: only for a driver that reads them
;; (`fixpt check`, the REPL, the agreement tests). Showing the types of
;; modules is most of the cost of checking a front end of them, which the
;; compile paths never read (`check-lines!`).
(define k-show-lines (ref bool @t) (new #t))
;; The line for a form of type `t` and effect `e`; empty, if none are made.
(define k-line (->* (int k-eff) string)
  (lambda (t e)
    (if (get k-show-lines) (k-cat3 (k-show-ty t) " ! " (k-show-effect e)) "")))
;; The line for a definition of `name`, of type `t` and effect `e`.
(define k-define-line (->* (symbol int k-eff) string)
  (lambda (name t e)
    (if (get k-show-lines)
        ;; Not named by its own module's descriptions (`k-print-self`).
        (let* ((self (k-print-self! name)) (line (k-line t e)) (none (k-print-self! '||)))
          (k-cat4 "define " (symbol->string name) " : " line))
        "")))
(define k-push-lines (->* (k-out k-out) k-out)
  (lambda (lines out) (if (null? lines) out (k-push-lines (cdr lines) (cons (car lines) out)))))
;; Bind `n`, at top level, to a value of type `t`: a global, a module's
;; abstract types named for it.
(define k-bind-named-global (->* (symbol int) unit)
  (lambda (n t) (begin (k-bind-global n (k-name-module n t)) (k-link-aliases n (get k-dscope)))))
(define k-rec-types (->* (k-rec-forms) k-ids)
  (lambda (bs)
    (if (null? bs)
        nil
        (let* ((star (set k-arrow-star (k-written-arrow-star? (extract (car bs) 2))))
               (t0 (k-parse-type (extract (car bs) 2)))
               (t (k-arrow-star-as t0 (k-ty-fresh (k-select-syn t0 (extract (car bs) 2)))))
               (bound (k-bind-named-global (extract (car bs) 1) t))
               (noted (k-note-known (extract (car bs) 1) 0)))
          (cons t (k-rec-types (cdr bs)))))))
;; Each lambda, read under its signature: a lambda, or an error.
(define k-rec-lambdas (->* (k-rec-forms k-ids) k-letrec-bs)
  (lambda (bs ts)
    (if (null? bs)
        nil
        (let* ((name (extract (car bs) 1))
               (t (car ts))
               (saved (get k-dscope))
               (signed (k-bind-signature t))
               (x (k-resolve-exp (extract (car bs) 3)))
               (restored (set k-dscope saved))
               (checked (if (k-lambda? x) #u (k-fail-not-lambda name x))))
          (cons (product (1 name) (2 t) (3 x)) (k-rec-lambdas (cdr bs) (cdr ts)))))))
(define k-rec-check (->* (k-letrec-bs) k-out)
  (lambda (g)
    (if (null? g)
        nil
        (let* ((name (extract (car g) 1))
               (t (extract (car g) 2))
               (e (k-check-declared name t (extract (car g) 3)))
               (line (k-define-line name t e))
               (rest (k-rec-check (cdr g))))
          (cons line rest)))))

;; Each of `g`, by name and type, noted as recursive.
(define k-note-recursive (->* (k-letrec-bs) unit)
  (lambda (g)
    (if (null? g)
        #u
        (let ((m (car g)))
          (begin (set k-recursive (cons (cons (extract m 1) (extract m 2)) (get k-recursive)))
                 (k-note-recursive (cdr g)))))))
;; A `define-rec` group's free variables.
(define k-group-free (->* (k-letrec-bs k-names) k-names)
  (lambda (g out)
    (if (null? g) out (k-group-free (cdr g) (k-free-into (extract (car g) 3) nil out)))))
;; Each of `g`, bound again at its type there.
(define k-rebind-each (->* (k-letrec-bs) unit)
  (lambda (g)
    (if (null? g)
        #u
        (begin (k-rebind-top (extract (car g) 1) (extract (car g) 2)) (k-rebind-each (cdr g))))))
;; Note of the recursive group `g` whether it needs `spin`, and why.
(define k-note-rec-ending (->* (k-letrec-bs) unit)
  (lambda (g)
    (let ((why (k-termination g)))
      (if (string=? why "") #u (begin (k-note-recursive g) (k-note-why g why))))))
;; Group `g`, with members typed `->*`, bound and its termination noted
;; after `rsaved`: at the types found (`k-arrow-star-found`), bound again
;; so and noted again.
(define k-rec-found (->* (k-letrec-bs k-named) k-letrec-bs)
  (lambda (g rsaved)
    (let ((found (k-found-spinning g (k-arrow-star-found k-synth-lambda-as g))))
      (begin (k-rebind-each found) (set k-recursive rsaved) (k-note-rec-ending found) found))))
;; `(define-rec (name type lambda) …)`: every name in scope first, then each
;; lambda checked against its type. A line for each.
(define k-define-rec (->* (k-rec-forms) k-out)
  (lambda (bs)
    (let* ((rsaved (get k-recursive))
           (g0 (k-rec-lambdas bs (k-rec-types bs)))
           (u (set k-last-uses (k-group-free g0 nil)))
           ;; A group whose every run ends needs no `spin`.
           (noted (k-note-rec-ending g0))
           ;; With `->*`, the group at the types found.
           (g (if (k-any-arrow-star? g0) (k-rec-found g0 rsaved) g0))
           (lines (k-rec-check g)))
      (begin (set k-recursive rsaved) lines))))

;;; Redefinition (`top.rs`, `Checker::top_defining`), for files and the REPL
;;; alike: a global's uses always refer to what it is now. A definition of a
;;; name already a global, at a type every use can take (each a subtype of
;;; the old), assigns the global. At any other type it makes a new global,
;;; and every earlier definition that uses the name (and every one that uses
;;; those) is checked again, in order: each that checks is defined again,
;;; by the same rule; each that does not is broken. To keep a value as it
;;; was, a program binds it: `(define d (let ((g g)) …))`.

(define k-rev-runs (->* (k-run-list k-run-list) k-run-list)
  (lambda (xs acc) (if (null? xs) acc (k-rev-runs (cdr xs) (the k-run-list (cons (car xs) acc))))))
;; For a driver: what the program checked runs, in order (`compile-checked`,
;; `run-checked`).
(define checked-tops (->* () (listof k-run acyclic))
  (lambda () (k-rev-runs (get k-runs) nil)))
(define k-rev-defs (->* (k-def-list k-def-list) k-def-list)
  (lambda (xs acc) (if (null? xs) acc (k-rev-defs (cdr xs) (the k-def-list (cons (car xs) acc))))))
(define k-rec-names (->* (k-rec-forms) k-names)
  (lambda (bs)
    (if (null? bs) nil (the k-names (cons (extract (car bs) 1) (k-rec-names (cdr bs)))))))
;; The names a form defines.
(define k-top-names (->* (top) k-names)
  (lambda (form)
    (tagcase form
      (t-define (name ty init a b) (the k-names (cons name nil)))
      (t-define-rec (bs a b) (k-rec-names bs))
      (else y (the k-names nil)))))
;; Whether `n` is a global a definition made.
(define k-defined? (->* (symbol) bool)
  (lambda (n)
    (letrec ((go (subr (maxeff (read @globals) spin (read @t)) (k-def-list) bool)
               (lambda (ds)
                 (and (not (null? ds)) (or (k-has-name? (extract (car ds) 1) n) (go (cdr ds)))))))
      (go (get k-defs)))))
(define k-old-types (->* (k-names) k-olds)
  (lambda (ns)
    (cond ((null? ns) nil)
          ((k-defined? (car ns))
           (the k-olds (cons (cons (car ns) (k-lookup-raw (car ns))) (k-old-types (cdr ns)))))
          (else (k-old-types (cdr ns))))))
;; Whether `o`'s global now has a type its old one's uses can take.
(define k-fits-its-old? (->* ((pairof symbol int acyclic)) bool)
  (lambda (o) (k-subtype (k-lookup-raw (car o)) (cdr o))))
;; Whether each of them now has a type its old one's uses can take.
(define k-fits-old? (->* (k-olds) bool)
  (lambda (os) (or (null? os) (and (k-fits-its-old? (car os)) (k-fits-old? (cdr os))))))
(define k-names-without (->* (k-names k-names) k-names)
  (lambda (xs ns)
    (cond ((null? xs) xs)
          ((k-has-name? ns (car xs)) (k-names-without (cdr xs) ns))
          (else (the k-names (cons (car xs) (k-names-without (cdr xs) ns)))))))
(define k-defs-without (->* (k-def-list k-names) k-def-list)
  (lambda (ds ns)
    (cond ((null? ds) ds)
          ((k-names-meet? (extract (car ds) 1) ns) (k-defs-without (cdr ds) ns))
          (else (the k-def-list (cons (car ds) (k-defs-without (cdr ds) ns)))))))
;; `form`, which defines `ns`, recorded as their definition now.
(define k-record (->* (top k-names) unit)
  (lambda (form ns)
    (if (null? ns)
        #u
        (let ((def (product (1 ns) (2 form) (3 (k-names-without (get k-last-uses) ns)))))
          (set k-defs (the k-def-list (cons def (k-defs-without (get k-defs) ns))))))))
;; The definitions that use `ns`, and those that use them, and so on,
;; oldest first.
(define k-users-of (->* (k-names) k-def-list)
  (lambda (ns)
    (letrec ((go (subr (maxeff kreads (alloc @t)) (k-def-list k-names) k-def-list)
               (lambda (ds used)
                 (cond ((null? ds) nil)
                       ((k-names-meet? (extract (car ds) 1) ns) (go (cdr ds) used))
                       ((k-names-meet? (extract (car ds) 3) used)
                        (let ((more (k-names-onto (extract (car ds) 1) used)))
                          (the k-def-list (cons (car ds) (go (cdr ds) more)))))
                       (else (go (cdr ds) used))))))
      (go (k-rev-defs (get k-defs) nil) ns))))
;; Names as a message shows them: `a`, `b`.
(define k-shown (->* (k-names) string)
  (lambda (ns)
    (letrec ((go (subr (maxeff (read @globals) spin (alloc @t)) (k-names) k-texts)
               (lambda (xs)
                 (if (null? xs)
                     nil
                     (the k-texts (cons (k-quote (symbol->string (car xs))) (go (cdr xs))))))))
      (k-join (go ns) ", "))))
(define k-break-all (->* (k-names string) unit)
  (lambda (ns why)
    (if (null? ns)
        #u
        (let ((b (product (1 (car ns)) (2 (k-name-depth (car ns))) (3 why))))
          (begin (set k-broken (the (listof k-break acyclic) (cons b (get k-broken))))
                 (k-break-all (cdr ns) why))))))
(define k-lines-append (->* (k-out k-out) k-out)
  (lambda (xs ys) (if (null? xs) ys (the k-out (cons (car xs) (k-lines-append (cdr xs) ys))))))
;; An error at `written` unless `tw`, the type `define*` checks at, is a
;; `subr` (≥ 0).
(define k-star-subr (->* (int syn) unit)
  (lambda (tw written)
    (if (< tw 0)
        (k-sfail "`define*` finds what a procedure reads: its type is a `subr`" written)
        #u)))
;; An error at `x` if `define*` (`star`) defines it, and it is not a
;; `lambda`.
(define k-star-lambda (->* (bool kx) unit)
  (lambda (star x)
    (if (and star (not (k-lambda? x)))
        (k-fail-at "`define*` defines a procedure: a `lambda`" x)
        #u)))
;; Note of `name`, the lambda `x` of type `t`, whether its runs may not
;; end, and if so why: then it is recursive, as a group of one, beside
;; those of `rsaved`.
(define k-note-alone (->* (symbol int kx k-named) unit)
  (lambda (name t x rsaved)
    (let* ((g (the k-letrec-bs (cons (product (1 name) (2 t) (3 x)) nil)))
           (why (k-termination g)))
      (if (string=? why "")
          #u
          (begin (set k-recursive (cons (cons name t) rsaved)) (k-note-why g why))))))
;; Lemma `l`, now of the names `named`.
(define k-lemma-as (->* (k-lemma k-named) k-lemma)
  (lambda (l named)
    (product (1 (extract l 1)) (2 (extract l 2)) (3 (extract l 3)) (4 (extract l 4)) (5 named))))
;; `name`, of type `t`, defined as `x`, noted as a proof of `l`, once `x`
;; proves it.
(define k-note-lemma (->* (k-lemma symbol int kx) unit)
  (lambda (l name t x)
    (let ((named (the k-named (cons (cons name t) nil))))
      (begin (k-check-proof l name x)
             (set k-lemmas (cons (k-lemma-as l named) (get k-lemmas)))))))
;; An error at `written` if `define*` (`star`) declares an `->*` (`arrow`).
(define k-arrow-star-alone (->* (bool bool syn) unit)
  (lambda (star arrow written)
    (if (and star arrow)
        (k-sfail "`define*` and `->*` each find what a procedure does: write one" written)
        #u)))
;; An error at `x` if an `->*` (`arrow`) defines it, and it is not a `lambda`.
(define k-arrow-star-lambda (->* (bool kx) unit)
  (lambda (arrow x)
    (if (and arrow (not (tagcase x (x-lambda (ps body a b abk abkr) #t) (else y #f))))
        (k-fail-at "`->*` finds a procedure's effect from its `lambda`: define it as one" x)
        #u)))
;; The effect `->*` finds for `name`, from its body's `e`: with `spin` if it
;; reads `name` itself, as a procedure that may reach itself through a
;; global must say (`k-no-reaching-itself`).
(define k-arrow-star-spins (->* (symbol k-eff) k-eff)
  (lambda (name e)
    (if (or (k-reads-one-of? (cons name nil) e) (k-contains? e (a-read (r-globals))))
        (k-insert (a-spin) e)
        e)))
;; `(define name type init)`, or, if `star` is not empty,
;; `(define* name type init)`: its line.
(define k-define-typed (->* (symbol syn syns-a exp) k-out)
  (lambda (name written star-syns init)
    ;; A lambda is in scope in itself, as a `letrec`
    ;; binding is; anything else is not.
    (let* ((reset (set k-pending-lemma nil))
           ;; `(->* (param …) result)`: its effect found from its body.
           (arrow (k-written-arrow-star? written))
           (star (not (null? star-syns)))
           (both (k-arrow-star-alone star arrow written))
           (allowed (set k-arrow-star arrow))
           (t (k-select-syn (k-parse-type written) written))
           ;; `define*`: checked as though its type read
           ;; `@globals`, which finds what it reads.
           (tw (if star (k-with-latent t (k-one (a-read (r-globals)))) t))
           (subr-ok (k-star-subr tw written))
           ;; A `proves` type: a lemma, once the body proves it.
           (lemma (get k-pending-lemma))
           (taken (set k-pending-lemma nil))
           (saved (get k-dscope))
           (signed (k-bind-signature t))
           (x (k-resolve-exp init))
           (lambda-ok (k-star-lambda star x))
           (arrow-ok (k-arrow-star-lambda arrow x))
           (u (set k-last-uses (k-free-into x nil nil)))
           (restored (set k-dscope saved))
           (bound (if (k-lambda? x) (k-bind-named-global name t) #u))
           (rsaved (get k-recursive))
           ;; A lambda whose every run ends needs no `spin`.
           (noted (if (k-lambda? x)
                      (begin (k-note-known name 0) (k-note-alone name tw x rsaved))
                      #u))
           ;; A generative type's own `up-` and `down-` see
           ;; inside it.
           (inside (k-take-inside name))
           (opened (if (>= inside 0) (set k-transparent (cons inside (get k-transparent))) #u))
           ;; With `->*`, the `lambda` told its parameters and result and
           ;; its effect found, a call of itself standing for nothing more:
           ;; that effect already holds what such a call does, so it is the
           ;; least the procedure can have.
           (e0 (if arrow (k-arrow-star-latent k-synth-lambda-as t x) (k-check-declared name tw x)))
           ;; With `define*`, the globals the lambda read,
           ;; found, are its type's; and it is checked again
           ;; at that type, bound to it: one that fails is
           ;; the checker's mistake, not the program's.
           (tf (cond (star (k-with-latent t (k-globals-of (get k-last-latent))))
                     (arrow (k-with-latent t (k-arrow-star-spins name e0)))
                     (else tw)))
           (refound (if (or star arrow)
                        (begin (k-rebind-top name tf)
                               (set k-recursive rsaved)
                               (k-note-alone name tf x rsaved))
                        #u))
           ;; One that names not itself saw no placeholder: settled.
           (settled (if (and arrow (not (k-has-name? (get k-last-uses) name)))
                        (k-arrow-star-settle tf x)
                        #u))
           (e (if (or star arrow) (k-star-checked (if star "`define*`" "`->*`") name tf x) e0))
           (frozen (k-note-frozen-define tf x))
           (closed (if (>= inside 0)
                       (begin (set k-transparent (cdr (get k-transparent)))
                              (set k-conversions (cons (cons name t) (get k-conversions))))
                       #u))
           (popped (set k-recursive rsaved))
           (proved (if (null? lemma) #u (k-note-lemma (car lemma) name t x)))
           (after (if (k-lambda? x) #u (k-bind-named-global name tf))))
      (cons (k-define-line name tf e) nil))))
;; Whether effect `e` only reads globals.
(define k-reads-globals-only? (->* (k-eff) bool)
  (lambda (e)
    (or (null? e)
        (and (tagcase (car e)
               (a-read (r) (tagcase r (r-global (g) #t) (r-globals () #t) (else y #f)))
               (else y #f))
             (k-reads-globals-only? (cdr e))))))
;; The error that making a loaded file has effect `e`, and what to do.
(define k-shared-impure-why string
  (string-append "a file whose definitions make state as it is made is a program's: run it "
                 "with `,load FILE` or `fixpt run`; or, a module, give its state in a "
                 "`lambda` it gives, which each caller applies"))
(define k-shared-impure (->* (k-eff) string)
  (lambda (e)
    (k-cat3 (string-append "a loaded file is one value for all its loads, made once, "
                           "so making it must be pure, and this one has ")
            (k-show-effect e)
            (k-cat3 (char->string (integer->char 10)) "  " k-shared-impure-why))))
;; `(define name init)`, of no type written: its line. A loaded file's, made
;; once for all its loads, must be pure but for reading globals, and has
;; none; the definition is at `a`..`b`, the form that loads it.
(define k-define-untyped (->* (symbol exp int int) k-out)
  (lambda (name init a b)
    (let* ((x (k-resolve-exp init))
           (u (set k-last-uses (k-free-into x nil nil)))
           (r (k-synth x)))
      (begin (if (and (k-shared-name? name) (not (k-reads-globals-only? (extract r 2))))
                 (k-fail (k-shared-impure (extract r 2)) a b)
                 #u)
             (k-bind-named-global name (extract r 1))
             (if (k-lambda? x) (k-note-known name 0) #u)
             ;; No line for a file's hidden global, which the program does
             ;; not name.
             (if (k-shared-name? name)
                 nil
                 (cons (k-define-line name (extract r 1) (extract r 2)) nil))))))
;; One top-level form's lines: what each definition and expression is.
(define k-top-lines (->* (top) k-out)
  (lambda (form)
    (the k-out (tagcase form
                 (t-define (name ty init a b)
                   (if (null? ty)
                       (k-define-untyped name init a b)
                       (k-define-typed name (car ty) (cdr ty) init)))
                 (t-define-rec (bs a b) (k-define-rec bs))
                 (t-exp (e)
                   (let* ((x (k-resolve-exp e)) (r (k-synth x)))
                     (cons (k-line (extract r 1) (extract r 2)) nil)))
                 (else y nil)))))
(define k-lines-append-names (->* (k-names k-names) k-names)
  (lambda (xs ys)
    (if (null? xs) ys (the k-names (cons (car xs) (k-lines-append-names (cdr xs) ys))))))
;; The names `defs` define, in order.
(define k-defs-names (->* (k-def-list) k-names)
  (lambda (ds)
    (if (null? ds) nil (k-lines-append-names (extract (car ds) 1) (k-defs-names (cdr ds))))))
;; Those of `xs` that are in `ys`, in `xs`'s order.
(define k-names-within (->* (k-names k-names) k-names)
  (lambda (xs ys)
    (cond ((null? xs) xs)
          ((k-has-name? ys (car xs)) (the k-names (cons (car xs) (k-names-within (cdr xs) ys))))
          (else (k-names-within (cdr xs) ys)))))
;; Whether effect `e` has `spin`.
(define k-has-spin? (->* (k-eff) bool)
  (lambda (e)
    (and (not (null? e)) (or (tagcase (car e) (a-spin () #t) (else y #f)) (k-has-spin? (cdr e))))))
;; Whether `t` is a procedure whose calls may not end: `spin` in its latent
;; effect, under any `poly`.
(define k-type-spins? (->* (int) bool)
  (lambda (t)
    (tagcase (k-get (k-resolve t))
      (ty-poly (bs body) (k-type-spins? body))
      (ty-subr (e ps r cv spc) (k-has-spin? e))
      (else y #f))))
(define k-names-spin? (->* (k-names) bool)
  (lambda (ns)
    (and (not (null? ns)) (or (k-type-spins? (k-lookup-raw (car ns))) (k-names-spin? (cdr ns))))))
(define k-top-start (->* (top) int)
  (lambda (form)
    (tagcase form (t-define (name ty init a b) a) (t-define-rec (bs a b) a) (else y 0))))
(define k-top-end (->* (top) int)
  (lambda (form)
    (tagcase form (t-define (name ty init a b) b) (t-define-rec (bs a b) b) (else y 0)))))))
