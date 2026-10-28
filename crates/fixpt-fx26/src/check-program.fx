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
(import check-effects k-atom-region k-one k-insert)
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
    (if (get k-show-lines) (k-cat4 "define " (symbol->string name) " : " (k-line t e)) "")))
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
    (let ((found (k-arrow-star-found k-synth-lambda-as g)))
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
    (letrec ((go (subr (maxeff (read @globals) (read @t)) (k-def-list) bool)
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
    (letrec ((go (subr (maxeff (read @globals) (alloc @t)) (k-names) k-texts)
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
    (if (and arrow (not (tagcase x (x-lambda (ps body a b abk) #t) (else y #f))))
        (k-fail-at "`->*` finds a procedure's effect from its `lambda`: define it as one" x)
        #u)))
;; The effect `->*` finds for `name`, from its body's `e`: with `spin` if it
;; reads `name` itself, as a procedure that may reach itself through a
;; global must say (`k-no-reaching-itself`).
(define k-arrow-star-spins (->* (symbol k-eff) k-eff)
  (lambda (name e) (if (k-reads-one-of? (cons name nil) e) (k-insert (a-spin) e) e)))
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
    (tagcase form (t-define (name ty init a b) b) (t-define-rec (bs a b) b) (else y 0))))
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
;; reach itself through a global: if it reads one of `ns`, or, if
;; `redefining`, any global.
(define k-not-reaching (->* (top string int k-names bool) unit)
  (lambda (form name t ns redefining)
    (let* ((reads (k-latent-globals t))
           (m (k-first-read reads ns))
           (a (k-top-start form))
           (b (k-top-end form)))
      (cond ((not (null? m)) (k-fail (k-reads-itself name (symbol->string (car m))) a b))
            ((and redefining (k-has-region-in? reads (r-globals))) (k-fail (k-reads-any name) a b))
            (else #u)))))
;; Defining a global writes it: a procedure stored in global `f` whose calls
;; read `f` may reach itself through the global, which termination checking,
;; trusting every procedure of a type without `spin` to end, has not seen.
;; So it must say `spin`, as a procedure kept in a ref must, however it
;; reads `f`; one that stays `pure` binds itself with a local `letrec`. A
;; group's members read each other so. Reading `@globals` may read `f` only
;; once `f` is a global (`top.rs`, `no_reaching_itself`).
(define k-no-reaching-itself (->* (top k-names bool) unit)
  (lambda (form ns redefining)
    (letrec ((each (subr (maxeff checks spin) (k-names) unit)
               (lambda (ms)
                 (if (null? ms)
                     #u
                     (let* ((n (car ms)) (t (k-lookup-raw n)))
                       (if (k-type-spins? t)
                           (each (cdr ms))
                           (begin (k-not-reaching form (symbol->string n) t ns redefining)
                                  (each (cdr ms)))))))))
      (each ns))))
;; Note that `form` runs, assigning the globals it defines (`assigns`) or
;; making them new.
(define k-note-run (->* (top bool) unit)
  (lambda (form assigns)
    (set k-runs (the k-run-list (cons (product (1 form) (2 assigns)) (get k-runs))))))
;; Each of `users` checked again after the redefinition of `ns`: defined
;; again if it checks, broken if not.
(define k-rerun (->* (k-def-list k-names k-out) k-out)
  (lambda (users ns lines)
    (if (null? users)
        lines
        (let* ((u (car users))
               (olds (k-old-types (extract u 1)))
               (m (k-mark))
               (reset (set k-last-uses nil))
               (r (prompt k-tag
                    (let ((ls (k-top-lines (extract u 2))))
                      (begin (k-no-reaching-itself (extract u 2) (extract u 1) #t) (k-ok ls)))
                    (lambda (r) r))))
          (tagcase r
            (k-ok (ls)
              (let* ((assigns (k-fits-old? olds))
                     (recorded (k-record (extract u 2) (extract u 1)))
                     (ran (k-note-run (extract u 2) assigns)))
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
           (knot (k-no-reaching-itself form ns (not (null? olds))))
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
(define k-sys-str (->* (string int int int) exp) (lambda (v a b k) (e-str v a b k)))
;; `x1` … `xi`, onto `acc`, the `i`th's identity `k`+`i`.
(define k-sys-xs (->* (int int int int (listof exp acyclic)) (listof exp acyclic))
  (lambda (i a b k acc)
    (if (= i 0)
        acc
        (k-sys-xs (- i 1) a b k
                  (cons (e-var (string->symbol (string-append "x" (int->string i))) a b (+ k i))
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
;; The two definitions declaration `name` at `a`..`b` is, its type
;; `canonical`, `text` printed: whether the runtime has it, for a required
;; one checked as it is made; and itself, each of its expressions an
;; identity of its own. A `poly`'s binders are in scope in its definition,
;; which is checked against its body.
(define k-sys-defs (->* (symbol string syn string bool int int) (productof (1 top) (2 top)))
  (lambda (name host canonical text required a b)
    (let* ((label (string-append "syscall " (symbol->string name) " (\"" host "\")"))
           (asks (lambda ((f symbol) (k int))
                   (e-app (e-var f a b k)
                          (list (k-sys-str label a b (+ k 1)) (k-sys-str host a b (+ k 2))
                                (k-sys-str text a b (+ k 3)))
                          a b (+ k 4))))
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
                   (e-app (f xs a2 b2 k2)
                     (e-app (e-the at f a b 1016) (append xs (k-sys-xs n a b 1020 nil)) a b k2))
                   (else x x)))
           (body (e-lambda (k-sys-params 1 ps) (e-the (car (cdr (cdr (cdr ss)))) call a b 1030)
                           a b 1031))
           (available
            (if required
                (e-begin (list (asks '%syscall-require 1040) (e-bool #t a b 1045)) a b 1046)
                (e-app (e-var '%syscall-available? a b 1050)
                       (list (k-sys-str host a b 1051) (k-sys-str text a b 1052)) a b 1053)))
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
    (prompt k-tag
      (begin (k-reset) (set k-broken-began (get k-broken)) (set k-syscall-expanding 0)
             (k-standard standard)
             (set k-std-dscope (get k-dscope))
             (k-ahead forms)
             (k-ok (k-forms forms (k-types-again forms))))
      (lambda (r) r))))

;; The entry point for more of a program, form by form, as the REPL gives
;; them: checked in the environment the forms before left, which
;; `check-program` began. The facts for the compiler are only the new
;; forms', whose positions are in their own text.
(define check-more (->* (k-tops) k-result)
  (lambda (forms)
    (prompt k-tag
      (begin (set k-extracts nil)
             (set k-syscall-expanding 0)
             (set k-broken-began (get k-broken))
             (set k-effect-notes nil)
             (k-forget-withs)
             (set k-reshapes nil)
             (set k-runs nil)
             (k-ahead forms)
             (k-ok (k-forms forms nil)))
      (lambda (r) r)))))))
