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
(define-type k-out (select check-program-types k-out))
(define-type k-pos (select check-program-types k-pos))
(define-type k-proving (select check-program-types k-proving))
(define-type k-case-arm (select check-program-types k-case-arm))
(define-type k-tops (select check-program-types k-tops))
(define-type k-rec-forms (select check-program-types k-rec-forms))
(define-type k-run-list (select check-program-types k-run-list))
(define-type k-def-list (select check-program-types k-def-list))
(define-type k-olds (select check-program-types k-olds))
;; The types it uses of the files before it.
(define a-read (with check-types-types a-read))
(define a-spin (with check-types-types a-spin))
(define-effect checks (select check-types-types checks))
(define ds-eff (with check-types-types ds-eff))
(define ds-fun (with check-types-types ds-fun))
(define-type k-eff (select check-types-types k-eff))
(define k-err (with check-types-types k-err))
(define-type k-ids (select check-types-types k-ids))
(define-type k-lemma (select check-types-types k-lemma))
(define-type k-named (select check-types-types k-named))
(define-type k-names (select check-types-types k-names))
(define k-ok (with check-types-types k-ok))
(define-type k-regions (select check-types-types k-regions))
(define-type k-result (select check-types-types k-result))
(define-effect kreads (select check-types-types kreads))
(define-effect kstate (select check-types-types kstate))
(define-type kx (select check-types-types kx))
(define r-global (with check-types-types r-global))
(define r-globals (with check-types-types r-globals))
(define ty-poly (with check-types-types ty-poly))
(define ty-subr (with check-types-types ty-subr))
(define-type k-items (select check-types-types k-items))
(define-type exp (select parser-types exp))
(define-type names (select parser-types names))
(define-type syn (select parser-types syn))
(define-type syns-a (select parser-types syns-a))
(define t-define (with parser-types t-define))
(define t-define-effect (with parser-types t-define-effect))
(define t-define-generative (with parser-types t-define-generative))
(define t-define-rec (with parser-types t-define-rec))
(define t-define-type (with parser-types t-define-type))
(define t-exp (with parser-types t-exp))
(define-type top (select parser-types top))
(define-effect reads (select eager-reader-types reads))
(define-type k-break (select check-env-types k-break))
(define-type k-letrec-bs (select check-resolve-types k-letrec-bs))
(define-type k-run (select check-resolve-types k-run))
(define-type k-texts (select check-terminate-types k-texts))
(define-effect kmakes (select check-subst-types kmakes))
(define-type k-shown (select check-print-types k-shown))
;; What it uses of the modules it is given.
(define k-cat3 (with check-types k-cat3))
(define k-cat4 (with check-types k-cat4))
(define k-cat5 (with check-types k-cat5))
(define k-conversions (with check-types k-conversions))
(define k-fail (with check-types k-fail))
(define k-get (with check-types k-get))
(define k-has-name? (with check-types k-has-name?))
(define k-inside (with check-types k-inside))
(define k-join (with check-types k-join))
(define k-lemmas (with check-types k-lemmas))
(define k-ngens (with check-types k-ngens))
(define k-pending-lemma (with check-types k-pending-lemma))
(define k-quote (with check-types k-quote))
(define k-recursive (with check-types k-recursive))
(define k-resolve (with check-types k-resolve))
(define k-tag (with check-types k-tag))
(define k-transparent (with check-types k-transparent))
(define k-ahead-declare (with check-syntax k-ahead-declare))
(define k-ahead-filled (with check-syntax k-ahead-filled))
(define k-ahead-names (with check-syntax k-ahead-names))
(define k-define-family (with check-syntax k-define-family))
(define k-filled-reversed (with check-syntax k-filled-reversed))
(define k-ground-filled (with check-syntax k-ground-filled))
(define k-list-head (with check-syntax k-list-head))
(define k-atom-region (with check-effects k-atom-region))
(define k-one (with check-effects k-one))
(define k-bind-global (with check-env k-bind-global))
(define k-broken (with check-env k-broken))
(define k-dscope (with check-env k-dscope))
(define k-effect-notes (with check-env k-effect-notes))
(define k-extracts (with check-env k-extracts))
(define k-forget-withs (with check-env k-forget-withs))
(define k-last-latent (with check-env k-last-latent))
(define k-lookup-raw (with check-env k-lookup-raw))
(define k-mark (with check-env k-mark))
(define k-name-depth (with check-env k-name-depth))
(define k-note-known (with check-env k-note-known))
(define k-push-desc (with check-env k-push-desc))
(define k-reshapes (with check-env k-reshapes))
(define k-shared-name? (with check-env k-shared-name?))
(define k-std-dscope (with check-env k-std-dscope))
(define k-unbind-to (with check-env k-unbind-to))
(define k-bind-signature (with check-proofs k-bind-signature))
(define k-check-proof (with check-proofs k-check-proof))
(define k-names-meet? (with check-proofs k-names-meet?))
(define k-standard (with check-proofs k-standard))
(define k-check-declared (with check-rules k-check-declared))
(define k-star-checked (with check-rules k-star-checked))
(define k-synth (with check-rules k-synth))
(define k-define-generative (with check-generative k-define-generative))
(define k-define-type (with check-read-descs k-define-type))
(define k-parse-effect (with check-read-descs k-parse-effect))
(define k-parse-fun (with check-read-descs k-parse-fun))
(define k-parse-type (with check-read-descs k-parse-type))
(define k-defs (with check-resolve k-defs))
(define k-free-into (with check-resolve k-free-into))
(define k-has-region-in? (with check-resolve k-has-region-in?))
(define k-last-uses (with check-resolve k-last-uses))
(define k-reset (with check-resolve k-reset))
(define k-runs (with check-resolve k-runs))
(define k-fail-at (with check-errors k-fail-at))
(define k-fail-not-lambda (with check-terminate k-fail-not-lambda))
(define k-note-why (with check-terminate k-note-why))
(define k-termination (with check-terminate k-termination))
(define k-globals-atom? (with check-print-parts k-globals-atom?))
(define k-keep-atree! (with check-print k-keep-atree!))
(define k-show-effect (with check-print-parts k-show-effect))
(define k-show-ty (with check-print k-show-ty))
(define k-globals-of (with check-letrec k-globals-of))
(define k-with-latent (with check-letrec k-with-latent))
(define k-items (with check-read k-items))
(define k-name-of (with check-read k-name-of))
(define k-sfail (with check-read k-sfail))
(define k-lambda? (with check-expect k-lambda?))
(define k-link-aliases (with check-modules k-link-aliases))
(define k-name-module (with check-modules k-name-module))
(define k-resolve-exp (with check-modules-read k-resolve-exp))
(define k-select-syn (with check-modules k-select-syn))
(define k-names-onto (with check-modorder k-names-onto))
(define k-note-closed-filled (with check-subst k-note-closed-filled))
(define k-note-frozen-define (with check-synth k-note-frozen-define))
(define k-rebind-top (with check-module-rules k-rebind-top))
(define k-subtype (with check-subtype k-subtype))
(define drop (with parser drop))
(define syn-name (with parser syn-name))
(define syn-symbol? (with parser syn-symbol?))

;; The generative type `name` may see inside, as one of its conversions, or
;; -1; no longer, once asked.
(define k-take-inside (subr kstate (symbol) int)
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
;; The symbol `prefix` then `n` spells.
(define k-prefixed (subr (read @globals) (string string) symbol)
  (lambda (prefix n) (string->symbol (string-append prefix n))))
(define k-declare (subr (maxeff checks spin) (top) unit)
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
      (t-define-generative (head rep a b)
        (let* ((name (k-define-generative head rep))
               (g (- (get k-ngens) 1))
               (n (symbol->string name)))
          ;; Only its own conversions, which follow, see inside it.
          (set k-inside (cons (cons (k-prefixed "down-" n) g)
                              (cons (cons (k-prefixed "up-" n) g) (get k-inside))))))
      (else y #u))))

(define k-declare-each (subr (maxeff checks spin) (k-tops) unit)
  (lambda (forms)
    (if (null? forms)
        #u
        (begin (k-declare (car forms)) (k-declare-each (cdr forms))))))
(define k-names-reversed (subr (read @globals) (k-names k-names) k-names)
  (lambda (xs acc) (if (null? xs) acc (k-names-reversed (cdr xs) (cons (car xs) acc)))))
;; The names simple `define-type`s give, in order, each as often as given.
(define k-ahead-names-of (subr (maxeff (read @globals) (read @s) spin) (k-tops k-names) k-names)
  (lambda (forms acc)
    (if (null? forms)
        (k-names-reversed acc nil)
        (k-ahead-names-of
         (cdr forms)
         (tagcase (car forms)
           (t-define-type (name def a b)
             (if (and (syn-symbol? name) (not (string=? (k-list-head def) "dlambda")))
                 (cons (string->symbol (syn-name name)) acc)
                 acc))
           (else y acc))))))
;; The first pass: abbreviations, so that types can refer to each other in
;; any order. Values cannot: a definition sees only those before it. Each
;; abbreviation defined once, by name, is in scope before any is read, and
;; checked grounded once all are.
(define* k-ahead (subr (maxeff checks spin) (k-tops) unit)
  (lambda (forms)
    (let ((names (k-ahead-names-of forms nil)))
      (begin
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
(define k-line (subr (maxeff (read @globals) (read @t) (alloc @t) spin) (int k-eff) string)
  (lambda (t e)
    (if (get k-show-lines) (k-cat3 (k-show-ty t) " ! " (k-show-effect e)) "")))
;; The line for a definition of `name`, of type `t` and effect `e`.
(define k-define-line (subr (maxeff kreads (alloc @t) spin) (symbol int k-eff) string)
  (lambda (name t e)
    (if (get k-show-lines) (k-cat4 "define " (symbol->string name) " : " (k-line t e)) "")))
(define k-push-lines (subr (maxeff kreads (alloc @t)) (k-out k-out) k-out)
  (lambda (lines out) (if (null? lines) out (k-push-lines (cdr lines) (cons (car lines) out)))))
;; Bind `n`, at top level, to a value of type `t`: a global, a module's
;; abstract types named for it.
(define k-bind-named-global (subr (maxeff kstate spin) (symbol int) unit)
  (lambda (n t) (begin (k-bind-global n (k-name-module n t)) (k-link-aliases n (get k-dscope)))))
(define k-rec-types (subr (maxeff checks spin) (k-rec-forms) k-ids)
  (lambda (bs)
    (if (null? bs)
        nil
        (let* ((t (k-select-syn (k-parse-type (extract (car bs) 2)) (extract (car bs) 2)))
               (bound (k-bind-named-global (extract (car bs) 1) t))
               (noted (k-note-known (extract (car bs) 1) 0)))
          (cons t (k-rec-types (cdr bs)))))))
;; Each lambda, read under its signature: a lambda, or an error.
(define k-rec-lambdas (subr (maxeff checks spin) (k-rec-forms k-ids) k-letrec-bs)
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
(define k-rec-check (subr (maxeff checks spin) (k-letrec-bs) k-out)
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
(define k-note-recursive (subr kstate (k-letrec-bs) unit)
  (lambda (g)
    (if (null? g)
        #u
        (let ((m (car g)))
          (begin (set k-recursive (cons (cons (extract m 1) (extract m 2)) (get k-recursive)))
                 (k-note-recursive (cdr g)))))))
;; A `define-rec` group's free variables.
(define k-group-free (subr kmakes (k-letrec-bs k-names) k-names)
  (lambda (g out)
    (if (null? g) out (k-group-free (cdr g) (k-free-into (extract (car g) 3) nil out)))))
;; `(define-rec (name type lambda) …)`: every name in scope first, then each
;; lambda checked against its type. A line for each.
(define k-define-rec (subr (maxeff checks spin) (k-rec-forms) k-out)
  (lambda (bs)
    (let* ((rsaved (get k-recursive))
           (g (k-rec-lambdas bs (k-rec-types bs)))
           (u (set k-last-uses (k-group-free g nil)))
           ;; A group whose every run ends needs no `spin`.
           (why (k-termination g))
           (noted (if (string=? why "") #u (begin (k-note-recursive g) (k-note-why g why))))
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

(define k-rev-runs (subr (read @globals) (k-run-list k-run-list) k-run-list)
  (lambda (xs acc) (if (null? xs) acc (k-rev-runs (cdr xs) (the k-run-list (cons (car xs) acc))))))
;; For a driver: what the program checked runs, in order (`compile-checked`,
;; `run-checked`).
(define checked-tops (subr (maxeff (read @globals) (read @t)) () (listof k-run acyclic))
  (lambda () (k-rev-runs (get k-runs) nil)))
(define k-rev-defs (subr (read @globals) (k-def-list k-def-list) k-def-list)
  (lambda (xs acc) (if (null? xs) acc (k-rev-defs (cdr xs) (the k-def-list (cons (car xs) acc))))))
(define k-rec-names (subr (read @globals) (k-rec-forms) k-names)
  (lambda (bs)
    (if (null? bs) nil (the k-names (cons (extract (car bs) 1) (k-rec-names (cdr bs)))))))
;; The names a form defines.
(define k-top-names (subr (read @globals) (top) k-names)
  (lambda (form)
    (tagcase form
      (t-define (name ty init a b) (the k-names (cons name nil)))
      (t-define-rec (bs a b) (k-rec-names bs))
      (else y (the k-names nil)))))
;; Whether `n` is a global a definition made.
(define k-defined? (subr (maxeff (read @globals) (read @t)) (symbol) bool)
  (lambda (n)
    (letrec ((go (subr (maxeff (read @globals) (read @t)) (k-def-list) bool)
               (lambda (ds)
                 (and (not (null? ds)) (or (k-has-name? (extract (car ds) 1) n) (go (cdr ds)))))))
      (go (get k-defs)))))
(define k-old-types (subr (maxeff (read @globals) (read @t) spin) (k-names) k-olds)
  (lambda (ns)
    (cond ((null? ns) nil)
          ((k-defined? (car ns))
           (the k-olds (cons (cons (car ns) (k-lookup-raw (car ns))) (k-old-types (cdr ns)))))
          (else (k-old-types (cdr ns))))))
;; Whether `o`'s global now has a type its old one's uses can take.
(define k-fits-its-old? (subr (maxeff kstate spin) ((pairof symbol int acyclic)) bool)
  (lambda (o) (k-subtype (k-lookup-raw (car o)) (cdr o))))
;; Whether each of them now has a type its old one's uses can take.
(define k-fits-old? (subr (maxeff kstate spin) (k-olds) bool)
  (lambda (os) (or (null? os) (and (k-fits-its-old? (car os)) (k-fits-old? (cdr os))))))
(define k-names-without (subr (maxeff (read @globals) (read @t)) (k-names k-names) k-names)
  (lambda (xs ns)
    (cond ((null? xs) xs)
          ((k-has-name? ns (car xs)) (k-names-without (cdr xs) ns))
          (else (the k-names (cons (car xs) (k-names-without (cdr xs) ns)))))))
(define k-defs-without (subr kreads (k-def-list k-names) k-def-list)
  (lambda (ds ns)
    (cond ((null? ds) ds)
          ((k-names-meet? (extract (car ds) 1) ns) (k-defs-without (cdr ds) ns))
          (else (the k-def-list (cons (car ds) (k-defs-without (cdr ds) ns)))))))
;; `form`, which defines `ns`, recorded as their definition now.
(define k-record (subr kstate (top k-names) unit)
  (lambda (form ns)
    (if (null? ns)
        #u
        (let ((def (product (1 ns) (2 form) (3 (k-names-without (get k-last-uses) ns)))))
          (set k-defs (the k-def-list (cons def (k-defs-without (get k-defs) ns))))))))
;; The definitions that use `ns`, and those that use them, and so on,
;; oldest first.
(define k-users-of (subr (maxeff kreads (alloc @t)) (k-names) k-def-list)
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
(define k-shown (subr (maxeff (read @globals) (read @t) (alloc @t)) (k-names) string)
  (lambda (ns)
    (letrec ((go (subr (maxeff (read @globals) (alloc @t)) (k-names) k-texts)
               (lambda (xs)
                 (if (null? xs)
                     nil
                     (the k-texts (cons (k-quote (symbol->string (car xs))) (go (cdr xs))))))))
      (k-join (go ns) ", "))))
(define k-break-all (subr (maxeff kstate spin) (k-names string) unit)
  (lambda (ns why)
    (if (null? ns)
        #u
        (let ((b (product (1 (car ns)) (2 (k-name-depth (car ns))) (3 why))))
          (begin (set k-broken (the (listof k-break acyclic) (cons b (get k-broken))))
                 (k-break-all (cdr ns) why))))))
(define k-lines-append (subr (read @globals) (k-out k-out) k-out)
  (lambda (xs ys) (if (null? xs) ys (the k-out (cons (car xs) (k-lines-append (cdr xs) ys))))))
;; An error at `written` unless `tw`, the type `define*` checks at, is a
;; `subr` (≥ 0).
(define k-star-subr (subr checks (int syn) unit)
  (lambda (tw written)
    (if (< tw 0)
        (k-sfail "`define*` finds what a procedure reads: its type is a `subr`" written)
        #u)))
;; An error at `x` if `define*` (`star`) defines it, and it is not a
;; `lambda`.
(define k-star-lambda (subr checks (bool kx) unit)
  (lambda (star x)
    (if (and star (not (k-lambda? x)))
        (k-fail-at "`define*` defines a procedure: a `lambda`" x)
        #u)))
;; Note of `name`, the lambda `x` of type `t`, whether its runs may not
;; end, and if so why: then it is recursive, as a group of one, beside
;; those of `rsaved`.
(define k-note-alone (subr (maxeff kstate spin) (symbol int kx k-named) unit)
  (lambda (name t x rsaved)
    (let* ((g (the k-letrec-bs (cons (product (1 name) (2 t) (3 x)) nil)))
           (why (k-termination g)))
      (if (string=? why "")
          #u
          (begin (set k-recursive (cons (cons name t) rsaved)) (k-note-why g why))))))
;; Lemma `l`, now of the names `named`.
(define k-lemma-as (subr pure (k-lemma k-named) k-lemma)
  (lambda (l named)
    (product (1 (extract l 1)) (2 (extract l 2)) (3 (extract l 3)) (4 (extract l 4)) (5 named))))
;; `name`, of type `t`, defined as `x`, noted as a proof of `l`, once `x`
;; proves it.
(define k-note-lemma (subr (maxeff checks spin) (k-lemma symbol int kx) unit)
  (lambda (l name t x)
    (let ((named (the k-named (cons (cons name t) nil))))
      (begin (k-check-proof l name x)
             (set k-lemmas (cons (k-lemma-as l named) (get k-lemmas)))))))
;; `(define name type init)`, or, if `star` is not empty,
;; `(define* name type init)`: its line.
(define k-define-typed (subr (maxeff checks spin) (symbol syn syns-a exp) k-out)
  (lambda (name written star-syns init)
    ;; A lambda is in scope in itself, as a `letrec`
    ;; binding is; anything else is not.
    (let* ((reset (set k-pending-lemma nil))
           (t (k-select-syn (k-parse-type written) written))
           ;; `define*`: checked as though its type read
           ;; `@globals`, which finds what it reads.
           (star (not (null? star-syns)))
           (tw (if star (k-with-latent t (k-one (a-read (r-globals)))) t))
           (subr-ok (k-star-subr tw written))
           ;; A `proves` type: a lemma, once the body proves it.
           (lemma (get k-pending-lemma))
           (taken (set k-pending-lemma nil))
           (saved (get k-dscope))
           (signed (k-bind-signature t))
           (x (k-resolve-exp init))
           (lambda-ok (k-star-lambda star x))
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
           (e0 (k-check-declared name tw x))
           ;; With `define*`, the globals the lambda read,
           ;; found, are its type's; and it is checked again
           ;; at that type, bound to it: one that fails is
           ;; the checker's mistake, not the program's.
           (tf (if star (k-with-latent t (k-globals-of (get k-last-latent))) tw))
           (refound (if star
                        (begin (k-rebind-top name tf)
                               (set k-recursive rsaved)
                               (k-note-alone name tf x rsaved))
                        #u))
           (e (if star (k-star-checked name tf x) e0))
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
(define k-reads-globals-only? (subr (read @globals) (k-eff) bool)
  (lambda (e)
    (or (null? e)
        (and (tagcase (car e)
               (a-read (r) (tagcase r (r-global (g) #t) (r-globals () #t) (else y #f)))
               (else y #f))
             (k-reads-globals-only? (cdr e))))))
;; The error that making a loaded file has effect `e`.
(define k-shared-impure (subr (maxeff (read @globals) (read @t)) (k-eff) string)
  (lambda (e)
    (k-cat3 (string-append "a loaded file is one value for all its loads, made once, "
                           "so making it must be pure, and this one has ")
            (k-show-effect e)
            ": make its state in a `lambda` it gives, which each caller applies")))
;; `(define name init)`, of no type written: its line. A loaded file's, made
;; once for all its loads, must be pure but for reading globals, and has
;; none; the definition is at `a`..`b`, the form that loads it.
(define k-define-untyped (subr (maxeff checks spin) (symbol exp int int) k-out)
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
(define k-top-lines (subr (maxeff checks spin) (top) k-out)
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
(define k-lines-append-names (subr (read @globals) (k-names k-names) k-names)
  (lambda (xs ys)
    (if (null? xs) ys (the k-names (cons (car xs) (k-lines-append-names (cdr xs) ys))))))
;; The names `defs` define, in order.
(define k-defs-names (subr (maxeff kreads (alloc @t)) (k-def-list) k-names)
  (lambda (ds)
    (if (null? ds) nil (k-lines-append-names (extract (car ds) 1) (k-defs-names (cdr ds))))))
;; Those of `xs` that are in `ys`, in `xs`'s order.
(define k-names-within (subr (maxeff (read @globals) (read @t)) (k-names k-names) k-names)
  (lambda (xs ys)
    (cond ((null? xs) xs)
          ((k-has-name? ys (car xs)) (the k-names (cons (car xs) (k-names-within (cdr xs) ys))))
          (else (k-names-within (cdr xs) ys)))))
;; Whether effect `e` has `spin`.
(define k-has-spin? (subr (read @globals) (k-eff) bool)
  (lambda (e)
    (and (not (null? e)) (or (tagcase (car e) (a-spin () #t) (else y #f)) (k-has-spin? (cdr e))))))
;; Whether `t` is a procedure whose calls may not end: `spin` in its latent
;; effect, under any `poly`.
(define k-type-spins? (subr (maxeff (read @globals) (read @t) spin) (int) bool)
  (lambda (t)
    (tagcase (k-get (k-resolve t))
      (ty-poly (bs body) (k-type-spins? body))
      (ty-subr (e ps r cv) (k-has-spin? e))
      (else y #f))))
(define k-names-spin? (subr (maxeff (read @globals) (read @t) spin) (k-names) bool)
  (lambda (ns)
    (and (not (null? ns)) (or (k-type-spins? (k-lookup-raw (car ns))) (k-names-spin? (cdr ns))))))
(define k-top-start (subr pure (top) int)
  (lambda (form)
    (tagcase form (t-define (name ty init a b) a) (t-define-rec (bs a b) a) (else y 0))))
(define k-top-end (subr pure (top) int)
  (lambda (form)
    (tagcase form (t-define (name ty init a b) b) (t-define-rec (bs a b) b) (else y 0))))
(define k-atoms-globals (subr (maxeff (read @globals) (alloc @t)) (k-eff) k-regions)
  (lambda (e)
    (cond ((null? e) nil)
          ((k-globals-atom? (car e))
           (the k-regions (cons (k-atom-region (car e)) (k-atoms-globals (cdr e)))))
          (else (k-atoms-globals (cdr e))))))
;; The globals calling a value of type `t` reads: its latent effect's, under
;; any `poly`; none, if it is not a procedure.
(define k-latent-globals (subr (maxeff (read @globals) (read @t) (alloc @t) spin) (int) k-regions)
  (lambda (t)
    (tagcase (k-get (k-resolve t))
      (ty-poly (bs body) (k-latent-globals body))
      (ty-subr (e ps r cv) (k-atoms-globals e))
      (else y nil))))
;; The first of `ns` whose global `rs` has, if any.
(define k-first-read (subr (maxeff kreads (alloc @t) spin) (k-regions k-names) k-names)
  (lambda (rs ns)
    (cond ((null? ns) nil)
          ((k-has-region-in? rs (r-global (car ns))) (the k-names (cons (car ns) nil)))
          (else (k-first-read rs (cdr ns))))))
;; What a procedure that may reach itself through a global must do.
(define k-must-spin string "` may reach itself through a global: its type must say `spin`")
;; Why calling `name`, which reads the global `m`, may reach itself.
(define k-reads-itself (subr (read @globals) (string string) string)
  (lambda (name m)
    (k-cat4 (k-cat5 "calling `" name "` reads `" m "`, so `") name k-must-spin
            " (or, to call itself directly, it binds itself with a local `letrec`)")))
;; Why calling `name`, which may read any global, may reach itself.
(define k-reads-any (subr (read @globals) (string) string)
  (lambda (name)
    (let ((so (k-cat5 "calling `" name "` may read any global, `" name "` too, so `")))
      (k-cat3 so name k-must-spin))))
;; An error at `form` if calling the procedure `name`, of type `t`, may
;; reach itself through a global: if it reads one of `ns`, or, if
;; `redefining`, any global.
(define k-not-reaching (subr (maxeff checks spin) (top string int k-names bool) unit)
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
(define k-no-reaching-itself (subr (maxeff checks spin) (top k-names bool) unit)
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
(define k-note-run (subr kstate (top bool) unit)
  (lambda (form assigns)
    (set k-runs (the k-run-list (cons (product (1 form) (2 assigns)) (get k-runs))))))
;; Each of `users` checked again after the redefinition of `ns`: defined
;; again if it checks, broken if not.
(define k-rerun (subr (maxeff (read @globals) checks spin) (k-def-list k-names k-out) k-out)
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
(define check-lines! (subr (maxeff (read @globals) (write @t)) (bool) unit)
  (lambda (on) (set k-show-lines on)))
(define check-defer-reruns! (subr (maxeff (read @globals) (write @t)) (bool) unit)
  (lambda (on) (set k-defer-reruns on)))
;; A top-level form, checked under redefinition: its lines, and those of
;; the definitions it has run again.
(define k-defining (subr (maxeff checks spin) (top) k-out)
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

;; The second pass: definitions and expressions, in order, each under
;; redefinition (`k-defining`).
(define k-forms (subr (maxeff checks spin) (k-tops k-out) k-out)
  (lambda (forms out)
    (if (null? forms)
        (reverse out)
        (k-forms (cdr forms) (k-push-lines (k-defining (car forms)) out)))))

;; The entry point: check a program's trees, in the initial environment
;; written `standard`. What each definition and expression is, in order,
;; or the first error.
(define check-program (subr (maxeff (read @globals) checks spin) (syns-a k-tops) k-result)
  (lambda (standard forms)
    (prompt k-tag
      (begin (k-reset) (k-standard standard) (set k-std-dscope (get k-dscope))
             (k-ahead forms) (k-ok (k-forms forms nil)))
      (lambda (r) r))))

;; The entry point for more of a program, form by form, as the REPL gives
;; them: checked in the environment the forms before left, which
;; `check-program` began. The facts for the compiler are only the new
;; forms', whose positions are in their own text.
(define check-more (subr (maxeff (read @globals) checks spin) (k-tops) k-result)
  (lambda (forms)
    (prompt k-tag
      (begin (set k-extracts nil)
             (set k-effect-notes nil)
             (k-forget-withs)
             (set k-reshapes nil)
             (set k-runs nil)
             (k-ahead forms)
             (k-ok (k-forms forms nil)))
      (lambda (r) r)))))))
