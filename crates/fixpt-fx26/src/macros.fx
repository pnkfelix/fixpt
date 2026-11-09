;;; Typed hygienic macros, in FX-26: the expander of the front end written
;;; in FX-26, as the Rust one is (`macros.rs`, `docs/research/typed-macros.md`):
;;; a `define-syntax` checked against its signature (Herman's rules) and
;;; defined, and each use of a macro expanded by transcription, the
;;; template's binders made fresh, its free names the top level's, through
;;; `#%toplevel`. Its parts: `macros-types.fx`, the syntax types;
;;; `macros-align.fx`, syntax aligned with them and the macros defined;
;;; `macros-files.fx`, what it reads of files and the forms ahead. The
;;; parser runs it on each top-level form before anything else sees it
;;; (`parse-tops`); how it fails is the parser's (`fails`).

(module-parameters ((rs region) (re region) (rm region) (rc region) (rp region)))
;; Signatures inferred (`macros-solve.fx`, on `macros-infer.fx`), which
;; loads the rest.
(define procedural-module ((proj (load-module "fx26:macros-procedural.fx") rs re rm rc rp)))
(define solve-module (with procedural-module solve-module))
(define infer-module (with solve-module infer-module))
(define files-module (with infer-module files-module))
(define exports-module (with files-module exports-module))
(define match-module (with exports-module match-module))
(define scopes-module (with exports-module scopes-module))
(define align-module (with files-module align-module))
(define types-module (with align-module types-module))
(define parser-module (with types-module parser-module))
(define reader-types (with parser-module reader-types))
(import reader-types atom lst dotted vec (type syn))
(import parser-module syn-start syn-end syn-symbol? syn-name syn-symbol syn-datums syn-expansion
        syn->datum len nth mk-list mk-symbol datatype? expand-datatype in-loaded-as load-base
        (type syns-a names loaded-file) (effect parses))
;; The module files' forms (`parser-forms.fx`): whether a file takes modules.
(define forms-module ((proj (load-module "fx26:parser-forms.fx") rs re rm rc rp)))
(import types-module fail-at split syn-nil? reserved? reserved-syn? read-sty s-expr s-defn s-type
        signature-made pure-hole? affine-kind? int-in? ellipsis? ellipsis-of proper-items
        name-kind?
        (type fails addr sty))
(import match-module bound-of matched pattern-names list-items odd-length nth-name nth-list
        len-ints addr-under? ints=? all-ints? ints-prefix (type binds))
(import scopes-module walk placed evaluate levels-of binder-of)
(import align-module defined macro-of macro? makes-defns? makes-top-defns? nodes-reset! align
        node-at node-syn node-path node-core node-kids pvar-of pvar? nnodes act-rename act-toplevel
        seq-depths
        act-qualified act-standard act-module act-module-type act-standard-type desc-roots under
        act-macro-head atm-lit lv-rib k-pvar k-binder k-ref k-form k-other
        node-hole s-typed
        (type action actions clause clauses macro macro-env scope scopes pinfo pvars
              found levels
              atms kids contracts holes))
(import exports-module exports-of exports=? shown-exports nested-binders unsaid-nested
        drivers-of renames-under with-uses with-uses-given note-projection note-uses
        (type exported nested))
(import solve-module infer sig-text)
(import procedural-module procedural-of procedural-form define-procedural expand-procedural
        source-key source-of)
(import infer-module (type unsigned unsigneds))
(import files-module written-of signature-of written-names literals-said binder-names names-any?
        said-fail signed-each syntax-names
        (type written writtens signed signed-opt))
(import files-module proper name-in? defines-syntax? head-name load-path without-load load-of
        internal-of
        imports-syntax? import-usage name-filter all-names listed? not-macros loaded-path
        file-syntax hidden-syntax hide-form? file-items names-shown defined-name rec-names
        generative-values macro-names internal-names taken? shown-names macro-sites load-noted
        brings? shown-syntax lenient-filter names-only
        (type load-defs filter files mades file-macro places))

;;; ------------------------------------------------------------ clauses

(define clause-usage string "a clause is `((_ . pattern) template)`")
;; Clause `c` checked against signature `sig` (Herman's rules), in a
;; file's scope if `file` has one: its pattern fits the signature, each of
;; the pattern's variables is placed in the template where the signature
;; says what is in scope there, and a reference to a pattern's binder is
;; where no other pattern binder may shadow it. `lits`, its `syntax-rules`'
;; literals.
(define check-clause (->* (fails syn sty int syns-a names scopes) clause)
  (lambda (fail c sig defn poly lits file)
    (let ((two (proper c)))
      (if (not (= (len two) 2))
          (begin (fail-at fail clause-usage c) (stub c))
          (let ((whole (split (car two))))
            (if (null? whole)
                (begin (fail-at fail clause-usage (car two)) (stub c))
                (let* ((pattern (nth whole 1))
                       (pv (pattern-vars fail sig pattern defn lits)) (ps (extract pv 1))
                       (template (nth two 1)))
                  (tuple pattern template
                         (template-actions fail ps template defn (extract pv 2) file) ps
                         (contracts-of ps (binder-names poly) file)))))))))
(define stub (->* (syn) clause)
  (lambda (c) (tuple c c (the actions nil) (the pvars nil) (the contracts nil))))
;; Each typed hole's contract, its type read as a use reads the template's
;; types; none where it names the macro's own binders, which no use can
;; write.
(define contracts-of (->* (pvars names scopes) contracts)
  (lambda (ps binders file)
    (if (null? ps)
        nil
        (let* ((n (extract (car ps) 1)) (info (extract (car ps) 2)) (h (extract info 4))
               (rest (contracts-of (cdr ps) binders file)))
          (if (or (null? h) (null? (extract (car h) 1)) (not (expr-kind? (extract info 1)))
                  (names-any? (car (extract (car h) 1)) binders))
              rest
              (let* ((ty (car (extract (car h) 1))) (a (syn-start ty)) (b (syn-end ty))
                     (m (cond ((null? file) "#%toplevel")
                              ((and (syn-symbol? ty)
                                    (not (name-in? (syn-symbol ty) (extract (car file) 3))))
                               "#%fx")
                              (else (symbol->string (extract (car file) 1))))))
                (cons (tuple n (mk-list (list (mk-symbol "select" a b) (mk-symbol m a b) ty) a b))
                      rest)))))))
(define expr-kind? (->* (sty) bool)
  (lambda (t) (= ((with types-module kind-of) t) 0)))
;; The pattern, aligned with the signature: each variable's type and
;; declared environment. A macro that makes definitions (`defn`) has no
;; typed parts: what each use defines is checked where it is. And what
;; such a macro's uses define, if its signature says (`(-> (export σ β)
;; defn)`), in a list of one: what a template using it sees, and what its
;; own template is held to.
(define pattern-vars (->* (fails sty syn int names) (tupleof pvars (listof exported acyclic)))
  (lambda (fail sig pattern defn lits)
    (begin
      (nodes-reset!)
      (let* ((root (align fail 0 (the pvars nil) sig pattern -1 nil))
             (said (literals-said fail lits 0))
             (found (walk fail root nil #f 0))
             (e (extract (node-at root) 5))
             (declared (if (and (= defn 1) (not (null? e)))
                           (the (listof exported acyclic)
                                (list (exports-of (evaluate fail (extract (car e) 1)
                                                            (extract (car e) 2) pattern))))
                           nil)))
        (tuple (pvars-of fail found nil defn) declared)))))
;; What pattern variable `at` is, as the walk found it (`f`).
(define pinfo-at (->* (int (tupleof int levels bool int)) pinfo)
  (lambda (at f)
    (tuple (node-core at) (extract f 2) (extract f 3) (node-hole at) (extract f 4))))
(define pvars-of (->* (fails found pvars int) pvars)
  (lambda (fail fs ps defn)
    (if (null? fs)
        ps
        (let ((at (extract (car fs) 1)))
          (tagcase (node-kids at)
            (k-pvar (n)
              (cond
                ((and (> (extract (car fs) 4) 0) (not (null? (node-hole at))))
                 (begin (fail-at fail "a typed part under an ellipsis: not yet" (node-syn at)) ps))
                ((pvar? n ps)
                  (begin (fail-at fail (string-append "`" (symbol->string n) "` is a pattern "
                                                      "variable twice")
                                  (node-syn at))
                         ps))
                (else
                  (cond
                    ((and (= defn 1) (not (null? (node-hole at))))
                      (begin (fail-at fail (string-append "a macro that makes definitions has no "
                                                          "typed parts, not yet: what each use "
                                                          "defines is checked where it is")
                                      (node-syn at))
                             ps))
                    ((and (= defn 2) (not (null? (node-hole at))))
                     (begin (fail-at fail "a macro that makes a description has no typed parts"
                                     (node-syn at))
                            ps))
                    (else
                      (pvars-of fail (cdr fs)
                                (append ps (the pvars (list (tuple n (pinfo-at at (car fs))))))
                                defn))))))
            (else y (pvars-of fail (cdr fs) ps defn)))))))
;; The template, an expression or definitions (`defn`), aligned with the
;; kernel's forms' signatures and the macros', its pattern variables placed
;; by the rules, and what is done to each of its names where it is
;; transcribed.
(define template-actions
  (->* (fails pvars syn int (listof exported acyclic) scopes) actions)
  (lambda (fail ps template defn declared file)
    (begin
      (nodes-reset!)
      (let* ((made (cond ((= defn 1) (s-defn)) ((= defn 2) (s-type)) (else (s-expr))))
             (root (align fail 1 ps made template -1 nil))
             (found (walk fail root nil #f 0))
             (nested (nested-binders 0 (get nnodes) ps))
             (named (name-actions fail ps found file nil nil nested (binder-depths found))))
        (begin
          ;; Each part a template repeats says how many times: a pattern
          ;; variable in it that the pattern has under as many ellipses, or
          ;; a reference to a binder of the template's repeated as deep.
          (repeats-said fail (the (listof (tupleof int int) acyclic) (reverse (get seq-depths)))
                        ps named)
          ;; What the template defines of what its uses give, what its
          ;; signature says.
          (if (null? declared)
              #u
              (let ((made (exports-of (levels-of fail root template))))
                (if (exports=? made (car declared))
                    #u
                    (fail-at fail (string-append "this template defines " (shown-exports made)
                                                 ", and its signature says its uses define "
                                                 (shown-exports (car declared)))
                             template))))
          (type-actions fail 0 (get nnodes) file named))))))
;; Each part a template repeats, `rs`, with how many ellipses it is under:
;; refused if nothing in it says how many times (`actions`, what is done to
;; its names).
(define repeats-said (->* (fails (listof (tupleof int int) acyclic) pvars actions) unit)
  (lambda (fail rs ps acts)
    (cond ((null? rs) #u)
          ((says-times? (under (extract (car rs) 1)) (extract (car rs) 2) ps acts)
           (repeats-said fail (cdr rs) ps acts))
          (else (fail-at fail (string-append "`...` follows a part with no pattern variable in "
                                             "it under as many ellipses in the pattern, nor a "
                                             "binder repeated as deep, to say how many times")
                         (node-syn (extract (car rs) 1)))))))
(define says-times? (->* ((listof int acyclic) int pvars actions) bool)
  (lambda (ks depth ps acts)
    (and (not (null? ks))
         (or (tagcase (node-kids (car ks))
               (k-pvar (n) (>= (extract (car (pvar-of n ps)) 5) depth))
               (k-ref (n d free)
                 (let ((a (action-at (node-path (car ks)) acts)))
                   (and (not (null? a)) (tagcase (car a) (act-rename (p e) (>= e depth))
                                                 (else z #f)))))
               (else y #f))
             (says-times? (cdr ks) depth ps acts)))))
;; Each template binder the walk found, with how many ellipses it is under.
(define-type depths (listof (tupleof int int) acyclic))
(define binder-depths (->* (found) depths)
  (lambda (fs)
    (cond ((null? fs) nil)
          ((tagcase (node-kids (extract (car fs) 1)) (k-binder (n d) #t) (else y #f))
           (cons (tuple (extract (car fs) 1) (extract (car fs) 4)) (binder-depths (cdr fs))))
          (else (binder-depths (cdr fs))))))
(define depth-of (->* (int depths) int)
  (lambda (b ds)
    (cond ((null? ds) 0) ((= b (extract (car ds) 1)) (extract (car ds) 2))
          (else (depth-of b (cdr ds))))))
;; The actions for what the walk found, onto `out`; `uses`, the affine
;; pattern variables placed so far; `bd`, the binders' depths.
(define name-actions (->* (fails pvars found scopes actions names nested depths) actions)
  (lambda (fail ps fs file out uses nested bd)
    (if (null? fs)
        out
        (let* ((at (extract (car fs) 1)) (env (extract (car fs) 2)) (many (extract (car fs) 3))
               (depth (extract (car fs) 4)) (s (node-syn at)) (path (node-path at)))
          (tagcase (node-kids at)
            (k-pvar (n)
              (let* ((info (car (pvar-of n ps))) (name (symbol->string n))
                     ;; Anything with an expression in it, placed twice, runs
                     ;; twice: placed once, unless its signature says `many`,
                     ;; or it is a typed hole of no effect, `pure`.
                     (affine (and (not (extract info 3)) (not (pure-hole? (extract info 4)))
                                  (affine-kind? (extract info 1)))))
                (begin
                  (placed fail n info (node-core at) env s ps)
                  (if (< depth (extract info 5))
                      (fail-at fail (string-append "`" name "` is placed under " (int->string depth)
                                                   " ellipses, and the pattern has it under "
                                                   (int->string (extract info 5)))
                               s)
                      #u)
                  (if (and affine (> depth (extract info 5)))
                      (fail-at fail (string-append "`" name "` is placed under more ellipses than "
                                                   "the pattern has it, so in each repetition, and "
                                                   "an expression in it may do something each "
                                                   "time it runs: its signature says `(many …)` "
                                                   "if it may")
                               s)
                      #u)
                  (if (and affine many)
                      (fail-at fail (string-append "`" name "` is placed where it may be placed "
                                                   "more than once (a `many` part), and an "
                                                   "expression in it may do something each time "
                                                   "it runs: its signature says `(many …)` if it "
                                                   "may")
                               s)
                      #u)
                  (if (and affine (name-in? n uses))
                      (fail-at fail (string-append "`" name "` is placed twice, and an expression "
                                                   "in it may do something each time it runs: its "
                                                   "signature says `(many …)` if it may")
                               s)
                      #u)
                  (name-actions fail ps (cdr fs) file out
                                (if affine (the names (cons n uses)) uses) nested bd))))
            (k-binder (n d)
              (name-actions fail ps (cdr fs) file (cons (tuple path (act-rename path depth)) out)
                            uses nested bd))
            (k-ref (n d free)
              (let ((b (binder-of fail n d env s)))
                (begin
                  (if d #u (unsaid-nested fail n b nested s))
                  (repeated-ref fail n b depth bd s)
                  (let ((act (ref-action fail n b free file s bd)))
                    (name-actions fail ps (cdr fs) file
                                  (if (null? act) out (cons (tuple path (car act)) out)) uses
                                  nested bd)))))
            (else y (name-actions fail ps (cdr fs) file out uses nested bd)))))))
;; A reference to `n`: the template's binder of it, if one binds it in
;; `env` (its node, in a list of one), made fresh with it; else, as `free`
;; says (`k-ref`'s), the top level's, a file's own or a standard name, the
;; top level's qualified, or none (written as it is). In a list of one.
(define ref-action
  (->* (fails symbol (listof int acyclic) int scopes syn depths) (listof action acyclic))
  (lambda (fail n b free file s bd)
    (cond ((not (null? b)) (list (act-rename (node-path (car b)) (depth-of (car b) bd))))
          ((= free 2) nil)
          ((= free 3)
           (begin
             (fail-at fail (string-append "`" (symbol->string n) "`, the module a template's "
                                          "`(with module name)` takes from, is bound by the "
                                          "template or given by a use: a top level's, not yet")
                      s)
             nil))
          ;; A file's macro's description is read through the file's module
          ;; whole (`type-actions`).
          ((= free 1) (if (null? file) (list (act-qualified)) nil))
          ((null? file) (list (act-toplevel)))
          ((name-in? n (extract (car file) 2)) (list (act-module (extract (car file) 1))))
          ((name-in? n (extract (car file) 5)) (list (act-standard)))
          (else
           (begin
             (fail-at fail (string-append "`" (symbol->string n) "` is neither a value the file's "
                                          "module shows nor a standard binding: a file's macro "
                                          "names only those, as they are where it is imported")
                      s)
             (list (act-toplevel)))))))
;; A binder `b` (none or one) repeated, referred to under `depth`, fewer
;; ellipses than it is under: which repetition's is not said.
(define repeated-ref (->* (fails symbol (listof int acyclic) int depths syn) unit)
  (lambda (fail n b depth bd s)
    (if (and (not (null? b)) (> (depth-of (car b) bd) depth))
        (fail-at fail (string-append "`" (symbol->string n) "` is bound in each repetition of a "
                                     "part, and referred to under fewer ellipses than it is "
                                     "bound: which repetition's it is is not said")
                 s)
        #u)))
;; A file's macro's descriptions, from node `i` to `n`, each read whole
;; through the file's module or the standard environment, of those the
;; template writes alone, with no binder of its own or part of a use's in
;; them, for now; and a file's macro's use of another of its own.
(define type-actions (->* (fails int int scopes actions) actions)
  (lambda (fail i n file out)
    (if (= i n)
        out
        (let* ((path (node-path i)) (kids (node-kids i))
               (out2 (if (and (not (null? file)) (int-in? i (get desc-roots)))
                         (cons (tuple path (type-action fail i file out)) out)
                         out))
               (head (form-head-of i)))
          (type-actions fail (+ i 1) n file
                        (if (and (not (null? file)) (tagcase kids (k-form (x) #t) (else y #f))
                                 (not (null? head))
                                 (not (null? (internal-of (car head) (extract (car file) 4)))))
                            (let ((h (car (internal-of (car head) (extract (car file) 4)))))
                              (cons (tuple path (act-macro-head h)) out2))
                            out2))))))
;; The description at node `i`, a file's macro's, read whole: refused if it
;; has a binder of the template's or a part a use gives in it (`out`'s).
(define type-action (->* (fails int scopes actions) action)
  (lambda (fail i file out)
    (let ((s (node-syn i)) (open (open-node (under i) out)))
      (begin
        (if (null? open)
            #u
            (fail-at fail (string-append "a file's macro's description with a binder of its own "
                                         "or a part a use gives in it: not yet")
                     (node-syn (car open))))
        (if (and (syn-symbol? s) (not (name-in? (syn-symbol s) (extract (car file) 3))))
            (act-standard-type)
            (act-module-type (extract (car file) 1)))))))
(define open-node (->* ((listof int acyclic) actions) (listof int acyclic))
  (lambda (ks out)
    (cond ((null? ks) nil)
          ((or (tagcase (node-kids (car ks)) (k-pvar (n) #t) (k-binder (n d) #t) (else y #f))
               (let ((a (action-at (node-path (car ks)) out)))
                 (and (not (null? a)) (tagcase (car a) (act-rename (p e) #t) (else z #f)))))
           (list (car ks)))
          (else (open-node (cdr ks) out)))))
;; The name at the head of node `i`'s list, in a list of one.
(define form-head-of (->* (int) (listof symbol acyclic))
  (lambda (i)
    (let ((items (proper (node-syn i))))
      (if (and (not (null? items)) (syn-symbol? (car items)))
          (list (syn-symbol (car items)))
          nil))))

;;; ------------------------------------------------------------ defining

;; `(define-syntax name [σ] (syntax-rules (literal …) ((_ . pattern)
;; template) …))`, its signature written or inferred, or a
;; `define-syntax-rec` of them, checked, in a file's scope if `file` has
;; one, and defined: their names. A template's free name is the top level's
;; where the macro is used (`act-toplevel`). Each defined first, with its
;; signature, so that a template may use it or another of its
;; `define-syntax-rec`; what was defined before put back if one fails.
(define define-macro (->* (fails syn scopes) names)
  (lambda (fail form file)
    (let* ((before (get defined))
           (undo (lambda ((m string) (a int) (b int))
                   (begin (set defined before) (fail m a b)))))
      (if (null? (procedural-form form))
          (define-written undo (written-of undo form) file before)
          (define-procedural fail form)))))
;; Each signature, written, or inferred together for those not written,
;; each defined first; then each macro's clauses checked, and defined.
(define define-written (->* (fails writtens scopes macro-env) names)
  (lambda (fail ws file before)
    (let* ((written (signed-each fail ws))
           (us (unsigned-of ws))
           (inferred (if (null? us) nil (infer fail us)))
           (sigs (inferred-each fail ws written inferred))
           (made (checked-each fail ws sigs file)))
      (begin
        (set defined (append made before))
        (written-names ws)))))
(define-type said (tupleof signed-opt (listof string acyclic)))
(define unsigned-of (->* (writtens) unsigneds)
  (lambda (ws)
    (cond ((null? ws) nil)
          ((null? (extract (car ws) 2))
           (cons (tuple (extract (car ws) 1) (extract (car ws) 3) (extract (car ws) 4)
                        (extract (car ws) 5))
                 (unsigned-of (cdr ws))))
          (else (unsigned-of (cdr ws))))))
;; Each signature, the written one's, or the inferred one read, with how
;; it is said where its macro is refused.
(define inferred-each
  (->* (fails writtens (listof signed-opt acyclic) syns-a) (listof said acyclic))
  (lambda (fail ws written inferred)
    (cond
      ((null? ws) nil)
      ((not (null? (car written)))
       (cons (tuple (car written) (the (listof string acyclic) nil))
             (inferred-each fail (cdr ws) (cdr written) inferred)))
      (else
       (let* ((n (symbol->string (extract (car ws) 1))) (shown (sig-text (car inferred)))
              (s (signature-of (said-fail fail n shown) (car inferred))))
         (begin
           (set defined (cons (tuple (extract (car ws) 1) (tuple (extract s 2) (the clauses nil)
                                                                  (the syns-a nil) (extract s 3)))
                              (get defined)))
           (cons (tuple (the signed-opt (list s)) (the (listof string acyclic) (list shown)))
                 (inferred-each fail (cdr ws) (cdr written) (cdr inferred)))))))))
(define checked-each (->* (fails writtens (listof said acyclic) scopes) macro-env)
  (lambda (fail ws sigs file)
    (if (null? ws)
        nil
        (let* ((w (car ws)) (s (car (extract (car sigs) 1))) (shown (extract (car sigs) 2))
               (f (if (null? shown) fail (said-fail fail (symbol->string (extract w 1))
                                                    (car shown))))
               (cs (if (null? (extract w 4))
                       (begin (fail-at fail "a macro has at least one clause" (extract w 5))
                              (the clauses nil))
                       (check-each f (extract w 4) (extract s 2) (extract s 3) (extract s 1)
                                   (extract w 3) file))))
          (cons (tuple (extract w 1) (tuple (extract s 2) cs (extract s 1) (extract s 3)))
                (checked-each fail (cdr ws) (cdr sigs) file))))))
(define check-each (->* (fails syns-a sty int syns-a names scopes) clauses)
  (lambda (fail cs sig defn poly lits file)
    (if (null? cs)
        nil
        (let ((c (check-clause fail (car cs) sig defn poly lits file)))
          (cons c (check-each fail (cdr cs) sig defn poly lits file))))))

;;; ------------------------------------------------------------ the session

(define loads (ref load-defs rs) (new nil))
;; The macros defined after each form, and the load definitions, by the
;; session's state the form left (`form-reading`), which folds in every
;; form before it: so what a form is read with is what its state says, for
;; a program begun in the standard environment's (none), an entry in a
;; session's, or anything read again (`typed-macros.md`, the port's
;; decision 3). Only where there are some.
;; And the globals defined, which no macro may be named (`globals`).
;; And the count of fresh names, so that a program begun in the standard
;; environment's state makes them as the Rust expander, begun anew, does.
(define-type by-states (listof (tupleof int macro-env load-defs names int) acyclic))
;; Fresh names' count.
(define fresh-count (ref int rs) (new 0))
(define by-state (ref by-states rs) (new nil))
;; The globals the forms read so far define, and those the forms before
;; this parse did (`Checker::global_type` as a program is expanded, before
;; any of its own is checked).
(define globals (ref names rs) (new nil))
(define globals-before (ref names rs) (new nil))
(define macros-at! (->* (int) unit)
  (lambda (s)
    (let ((at (state-at s (get by-state))))
      (begin
        (set with-uses nil)
        (if (null? at)
            (begin (set defined nil) (set loads nil) (set globals nil) (set fresh-count 0))
            (begin (set defined (extract (car at) 2)) (set loads (extract (car at) 3))
                   (set globals (extract (car at) 4)) (set fresh-count (extract (car at) 5))))
        (set globals-before (get globals))))))
(define state-at (->* (int by-states) by-states)
  (lambda (s xs)
    (cond ((null? xs) nil)
          ((= s (extract (car xs) 1)) (the by-states (list (car xs))))
          (else (state-at s (cdr xs))))))
(define macros-after! (->* (int) unit)
  (lambda (s)
    (if (and (null? (get defined)) (null? (get loads)) (null? (get globals))
             (= (get fresh-count) 0))
        #u
        (set by-state (cons (tuple s (get defined) (get loads) (get globals) (get fresh-count))
                            (get by-state))))))
;; Names `ns` defined as globals.
(define globals! (->* (names) unit) (lambda (ns) (set globals (append ns (get globals)))))
;; Whether `n` was a global before this parse.
(define global-before? (->* (symbol) bool) (lambda (n) (name-in? n (get globals-before))))

;;; ------------------------------------------------------------ expanding

;; Each expansion made, the last first: its number, its macro's name, and
;; where its use is; `syn-expansion` says which made a part.
(define-type expansions-made (listof (tupleof int symbol int int) acyclic))
(define expansions (ref expansions-made rs) (new nil))
(define nexpansions (ref int rs) (new 0))
(define record-expansion (->* (symbol syn) int)
  (lambda (name s)
    (let ((n (+ (get nexpansions) 1)))
      (begin
        (set nexpansions n)
        (set expansions (cons (tuple n name (syn-start s) (syn-end s)) (get expansions)))
        n))))
;; For the driver, which says an error in an expansion at each use.
(define expansions-given (->* () expansions-made) (lambda () (get expansions)))

;; The expansions left before one does not end.
(define budget (ref int rs) (new 0))

;; `form` with each use of a macro in it expanded, as each expands, until
;; none is left; quoted data left as it is. A form of the program's is at
;; the place written for it, whatever a use made of it.
(define expand (->* (fails syn) syn)
  (lambda (fail form)
    (if (null? (get defined))
        form
        (begin
          (set budget 10000)
          (at-place (expand-in fail form nil) (syn-start form) (syn-end form) 0)))))
;; Top-level form `form` expanded: a use of a macro that makes definitions,
;; the definitions it makes, in order, a `begin` of them spliced (as R7RS's
;; at the top level); each at `form`'s place, as `expand`'s, as a top-level
;; `include`'s forms are (`Macros::expand_top`). Else `expand`'s, alone.
(define expand-top (->* (fails syn) syns-a)
  (lambda (fail form)
    (let ((items (list-items form)))
      (if (and (not (null? items)) (syn-symbol? (car items))
               (makes-top-defns? (syn-symbol (car items))))
          (begin
            (set budget 10000)
            (at-places (expand-defn fail form) (syn-start form) (syn-end form)))
          (list (expand fail form))))))
;; `s`, where a definition is: a use of a macro that makes definitions, what
;; it makes; a `begin`, each of its; a definition, as `expand-in` expands
;; it.
(define expand-defn (->* (fails syn) syns-a)
  (lambda (fail s)
    (let* ((items (list-items s)) (hd (if (null? items) s (car items)))
           (head (if (syn-symbol? hd) (syn-name hd) "")))
      (cond
        ((and (syn-symbol? hd) (macro? (syn-symbol hd)))
         (if (= (get budget) 0)
             (begin (fail-at fail "this macro's expansion does not end" s) nil)
             (begin
               (set budget (- (get budget) 1))
               (expand-defn fail (expand-use fail (syn-symbol hd) s)))))
        ((string=? head "begin") (expand-defns fail (cdr items)))
        (else (list (expand-in fail s nil)))))))
(define expand-defns (->* (fails syns-a) syns-a)
  (lambda (fail xs)
    (if (null? xs) nil (append (expand-defn fail (car xs)) (expand-defns fail (cdr xs))))))
(define at-places (->* (syns-a int int) syns-a)
  (lambda (xs a b) (if (null? xs) nil (cons (at-place (car xs) a b 0) (at-places (cdr xs) a b)))))
;; `s` at `a`..`b`, of expansion `x`.
(define at-place (->* (syn int int int) syn)
  (lambda (s a b x)
    (tagcase s
      (atom (d c e y) (atom d a b x))
      (lst (items d c e y) (lst items d a b x))
      (dotted (items tail d c e y) (dotted items tail d a b x))
      (vec (items d c e y) (vec items d a b x)))))
(define expand-in (->* (fails syn places) syn)
  (lambda (fail s withs)
    (let* ((items (list-items s)) (hd (if (null? items) s (car items)))
           (head (if (syn-symbol? hd) (syn-name hd) ""))
           (noted (if (string=? head "with") (note-projection s items hd) #u)))
      (cond
        ((null? items) s)
        ((string=? head "quote") s)
        ((and (syn-symbol? hd) (makes-defns? (syn-symbol hd)))
         (begin (fail-at fail (string-append "`" head "` makes definitions, which are made at the "
                                             "top level, not where an expression is")
                         s)
                s))
        ((and (syn-symbol? hd) (macro? (syn-symbol hd)))
         (if (= (get budget) 0)
             (begin (fail-at fail "this macro's expansion does not end" s) s)
             (begin
               (set budget (- (get budget) 1))
               ;; A name the program wrote (a template's is the macro, by
               ;; hygiene), in a `with`'s body.
               (if (= (syn-expansion hd) 0) (note-uses (syn-symbol hd) hd withs) #u)
               (expand-in fail (expand-use fail (syn-symbol hd) s) withs))))
        ;; A definition of a macro's name: refused, as a form's is.
        ((and (or (string=? head "define") (string=? head "define*"))
              (not (null? (cdr items))) (syn-symbol? (nth items 1))
              (macro? (syn-symbol (nth items 1))))
         (begin (fail-at fail (string-append "`" (syn-name (nth items 1)) "` is a macro's name, "
                                             "which is not defined again")
                         (nth items 1))
                s))
        (else (rebuilt s (expand-items fail items 0 (string=? head "with") s withs)
                       (expand-tail fail s withs)))))))
;; Items from the `k`th, each expanded; in a `with`'s body (from the third)
;; noted as in it.
(define expand-items (->* (fails syns-a int bool syn places) syns-a)
  (lambda (fail xs k with s withs)
    (if (null? xs)
        nil
        (let ((x (expand-in fail (car xs)
                            (if (and with (>= k 2))
                                (cons (tuple (syn-start s) (syn-end s)) withs)
                                withs))))
          (cons x (expand-items fail (cdr xs) (+ k 1) with s withs))))))
(define expand-tail (->* (fails syn places) syns-a)
  (lambda (fail s withs)
    (tagcase s (dotted (items t d a b x) (list (expand-in fail t withs))) (else y nil))))
;; `s`, a list, with items `xs` and, if it is dotted, tail `t`.
(define rebuilt (->* (syn syns-a syns-a) syn)
  (lambda (s xs t)
    (list-at (syn-start s) (syn-end s) (syn-expansion s) xs t)))
;; Items `xs` and a tail (none, or one), as one list at `a`..`b` of
;; expansion `x`: a tail that is a list joined to it, an empty one dropped.
(define list-at (->* (int int int syns-a syns-a) syn)
  (lambda (a b x xs t)
    (cond
      ;; `()`, as the reader reads it: a list of none.
      ((and (null? t) (null? xs)) (lst nil '() a b x))
      ((null? t) (lst xs (syn-datums xs) a b x))
      ((syn-nil? (car t)) (list-at a b x xs nil))
      (else
       (tagcase (car t)
         (lst (more d c e y) (list-at a b x (append xs more) nil))
         (dotted (more tail d c e y) (list-at a b x (append xs more) (list tail)))
         (else z
           (if (null? xs)
               (car t)
               (dotted xs (car t) (datum-dotted (syn-datums xs) (syn->datum (car t)))
                       a b x))))))))

;; A use of macro `name`, `s`, parsed by its signature, then the first
;; clause whose pattern matches it transcribed.
(define expand-use (->* (fails symbol syn) syn)
  (lambda (fail name s)
    (let* ((m (car (macro-of name (get defined))))
           (operands (nth (split s) 1))
           (shown (symbol->string name))
           (in-use (lambda ((msg string) (a int) (b int))
                     (fail (string-append "a use of `" shown "`: " msg) a b))))
      (if (not (null? (procedural-of name)))
          (expand-procedural fail name s (record-expansion name s))
          (begin
            (nodes-reset!)
            (align in-use 2 (the pvars nil) (extract m 1) operands -1 nil)
            (first-match fail name s operands (extract m 2)))))))
;; The pattern variables of `ps` that are names (`bvar`, `dvar`, `id`),
;; which match a name alone (a `label` may be a keyword).
(define name-pvars (->* (pvars) names)
  (lambda (ps)
    (cond ((null? ps) nil)
          ((let ((k ((with types-module kind-of) (extract (extract (car ps) 2) 1))))
             (and (name-kind? k) (not (= k 5))))
           (cons (extract (car ps) 1) (name-pvars (cdr ps))))
          (else (name-pvars (cdr ps))))))
(define first-match (->* (fails symbol syn syn clauses) syn)
  (lambda (fail name s operands cs)
    (if (null? cs)
        (begin (fail-at fail (string-append "a use of `" (symbol->string name) "` that no clause "
                                            "of it matches")
                        s)
               s)
        (let ((binds (matched (extract (car cs) 1) operands (name-pvars (extract (car cs) 4)) nil)))
          (if (null? binds)
              (first-match fail name s operands (cdr cs))
              (let* ((made (record-expansion name s)) (shown (symbol->string name))
                     (in-use (lambda ((msg string) (a int) (b int))
                               (fail (string-append "a use of `" shown "`: " msg)
                                     (syn-start s) (syn-end s)))))
                (transcribe in-use (car cs) (extract (car cs) 2) nil (car binds) made)))))))


;; Each binder's fresh name, by its path and the repetitions it is in; how
;; many times each repeated binder was repeated, by its path and the
;; repetitions around that; and the repetition of each ellipsis
;; transcription is under, outermost first (`macros.rs`'s `Made`).
(define-type freshes (listof (tupleof addr (listof int acyclic) symbol) acyclic))
(define fresh (ref freshes rs) (new nil))
(define-type counts (listof (tupleof addr (listof int acyclic) int) acyclic))
(define counts (ref counts rs) (new nil))
(define iters (ref (listof int acyclic) rs) (new nil))
(define action-at (->* (addr actions) (listof action acyclic))
  (lambda (path as)
    (cond ((null? as) nil)
          (((with types-module addr=?) path (extract (car as) 1)) (list (extract (car as) 2)))
          (else (action-at path (cdr as))))))
;; Template `t` of clause `c`, at `path` in it, transcribed by expansion
;; `made`: each part the template makes at its own place in the
;; `define-syntax`, of that expansion, each pattern variable's what the
;; use gave.
(define transcribe (->* (fails clause syn addr binds int) syn)
  (lambda (fail c t path bs made)
    (begin
      (if (null? path) (begin (set fresh nil) (set counts nil) (set iters nil)) #u)
      (transcribe-at fail c t path bs made))))
(define transcribe-at (->* (fails clause syn addr binds int) syn)
  (lambda (fail c t path bs made)
    (let* ((ta (syn-start t)) (tb (syn-end t)) (act (action-at path (extract c 3)))
           (typed (if (null? act)
                      ""
                      (tagcase (car act)
                        (act-standard-type () "#%fx")
                        (act-module-type (m) (symbol->string m))
                        (else y "")))))
      (cond
        ((not (string=? typed "")) (selected (string->symbol typed) t made))
        ((syn-symbol? t)
         (let* ((a (source-key ta made)) (b (source-key tb made)))
           (transcribe-name c t (syn-symbol t) a b act bs made)))
        ((not (null? (list-items t)))
         (let* ((a (source-key ta made))
                (xs (transcribe-items fail c (list-items t) path bs made))
                (rest (tagcase t
                        (dotted (items tail d c2 e x)
                          (let ((at (append path (falses (len items) nil))))
                            (list (transcribe-at fail c tail at bs made))))
                        (else y nil)))
                (head (if (null? act)
                          nil
                          (tagcase (car act) (act-macro-head (h) (list h)) (else y nil))))
                (xs2 (if (null? head)
                         xs
                         (cons (atom (car head) (syn-start (car xs)) (syn-end (car xs))
                                     (syn-expansion (car xs)))
                               (cdr xs))))
                (b (source-key tb made)))
           (list-at a b made xs2 rest)))
        (else (let* ((a (source-key ta made)) (b (source-key tb made))) (at-place t a b made)))))))
;; The `r`th to the `n`th repetitions of `x`, `drivers` bound to each's
;; element of `lists`, onto `out` (the last made first).
(define repeat-each
  (->* (fails clause syn addr binds int names (listof syns-a acyclic) int int syns-a) syns-a)
  (lambda (fail c x p bs made drivers lists r n out)
    (if (= r n)
        (the syns-a (reverse out))
        (let* ((each (bind-nth drivers lists r bs))
               (was (get iters))
               (one (begin (set iters (append was (the (listof int acyclic) (list r))))
                           (transcribe-at fail c x p each made))))
          (begin (set iters was)
                 (repeat-each fail c x p bs made drivers lists (+ r 1) n (cons one out)))))))
(define bind-nth (->* (names (listof syns-a acyclic) int binds) binds)
  (lambda (ns ls r bs)
    (if (null? ns)
        bs
        (bind-nth (cdr ns) (cdr ls) r (cons (tuple (car ns) (nth (car ls) r)) bs)))))
(define driver-lists (->* (names binds) (listof syns-a acyclic))
  (lambda (ns bs)
    (if (null? ns)
        nil
        (let ((b (car (bound-of (car ns) bs))))
          (cons (if (syn-nil? b) (the syns-a nil) (proper-items b)) (driver-lists (cdr ns) bs))))))
;; The counts known of the binders `under`, as repeated in `is`.
(define known-counts (->* ((listof (tupleof addr bool) acyclic) (listof int acyclic))
                          (listof int acyclic))
  (lambda (under is)
    (if (null? under)
        nil
        (let ((k (count-of (extract (car under) 1) is (get counts))))
          (if (< k 0) (known-counts (cdr under) is) (cons k (known-counts (cdr under) is)))))))
(define count-of (->* (addr (listof int acyclic) counts) int)
  (lambda (b is cs)
    (cond ((null? cs) -1)
          ((and ((with types-module addr=?) b (extract (car cs) 1))
                (ints=? is (extract (car cs) 2)))
           (extract (car cs) 3))
          (else (count-of b is (cdr cs))))))
;; Each binder of `under` that is the binder itself repeated `n` times here.
(define note-counts (->* ((listof (tupleof addr bool) acyclic) int) unit)
  (lambda (under n)
    (if (null? under)
        #u
        (begin
          (if (extract (car under) 2)
              (set counts (cons (tuple (extract (car under) 1) (get iters) n) (get counts)))
              #u)
          (note-counts (cdr under) n)))))
;; Type `t`, which a template writes, read in module `m` (`#%toplevel`,
;; `#%fx` or a file's), in expansion `made`: `(select m t)`; of a
;; definition's `(->* (param …) result)`, which is no type, each of its
;; types so (`macros.rs`'s `selected`).
(define selected (->* (symbol syn int) syn)
  (lambda (m t made)
    (let ((items (proper t)) (a (source-key (syn-start t) made)))
      (if (and (= (len items) 3) (syn-symbol? (car items)) (string=? (syn-name (car items)) "->*")
               (or (syn-nil? (nth items 1)) (not (null? (proper (nth items 1))))))
          (let* ((h (in-expansion (car items) made)) (params (nth items 1))
                 (pa (source-key (syn-start params) made))
                 (ps (selected-each m (proper params) made))
                 (pb (source-key (syn-end params) made))
                 (r (selected m (nth items 2) made)) (b (source-key (syn-end t) made)))
            (list-at a b made (list h (list-at pa pb made ps nil) r) nil))
          (let* ((ty (in-expansion t made)) (b (source-key (syn-end t) made)))
            (list-at a b made (list (atom 'select a b made) (atom m a b made) ty) nil))))))
(define selected-each (->* (symbol syns-a int) syns-a)
  (lambda (m ts made)
    (if (null? ts) nil (cons (selected m (car ts) made) (selected-each m (cdr ts) made)))))
;; `n` `#f`s, onto `out`.
(define falses (->* (int addr) addr)
  (lambda (n out) (if (= n 0) out (falses (- n 1) (cons #f out)))))
;; The items of a template's list, the `k`th at `path`, `k` `#f`s and a `#t`
;; past it.
(define transcribe-items (->* (fails clause syns-a addr binds int) syns-a)
  (lambda (fail c xs path bs made)
    (cond
      ((null? xs) nil)
      ;; `p ...`: `p` once for each element of what the use gave of the
      ;; pattern variables in it under more ellipses than this, together.
      ((and (not (null? (cdr xs))) (ellipsis? (car (cdr xs))))
       (let ((reps (repeated fail c (car xs) (append path (the addr (list #t))) bs made)))
         (append reps (transcribe-items fail c (cdr (cdr xs)) (append path (the addr (list #f #f)))
                                        bs made))))
      (else
       (let ((first (transcribe-at fail c (car xs) (append path (the addr (list #t))) bs made)))
         (cons first (transcribe-items fail c (cdr xs) (append path (the addr (list #f))) bs
                                       made)))))))
;; `x`, at `p`, repeated: as many times as every count it is repeated by
;; says, the pattern variables' and the repeated binders' it refers to.
(define repeated (->* (fails clause syn addr binds int) syns-a)
  (lambda (fail c x p bs made)
    (let* ((level (len-ints (get iters)))
           (drivers (drivers-of (extract c 4) x level))
           (lists (driver-lists drivers bs))
           (odd (odd-length lists 0))
           (under (renames-under (extract c 3) p level))
           (known (append (known-counts under (get iters))
                          (if (null? lists) (the (listof int acyclic) nil)
                              (list (len (car lists)))))))
      (cond
        ((>= odd 0)
         (begin (fail-at fail (string-append "`" (symbol->string (car drivers)) "` and `"
                                             (symbol->string (nth-name drivers odd))
                                             "`, repeated together, are given "
                                             (int->string (len (car lists))) " and "
                                             (int->string (len (nth-list lists odd))) " times")
                         x)
                nil))
        ((null? known)
         (begin (fail-at fail (string-append "this part is repeated before the repetition that "
                                             "binds what it refers to")
                         x)
                nil))
        ((not (all-ints? known (car known)))
         (begin (fail-at fail (string-append "this part repeats binders and parts that were "
                                             "repeated, or given, different numbers of times")
                         x)
                nil))
        (else
         (begin (note-counts under (car known))
                (repeat-each fail c x p bs made drivers lists 0 (car known) nil)))))))
(define transcribe-name
  (->* (clause syn symbol int int (listof action acyclic) binds int) syn)
  (lambda (c t n a b act bs made)
    (let ((given (bound-of n bs)) (contract (contract-of n (extract c 5))))
      (if (not (null? given))
          ;; A typed hole's expression, held to its type; in a template's
          ;; check, its call, where the template has it.
          (cond ((get checking) (respanned (car given) a b made))
                ((null? contract) (car given))
                (else
                 (let* ((g (car given)) (ga (syn-start g)) (gb (syn-end g)) (gx (syn-expansion g)))
                   (list-at ga gb gx
                            (list (atom 'the ga gb gx) (in-expansion (car contract) made) g) nil))))
          (if (null? act)
              (atom n a b made)
              (tagcase (car act)
                (act-rename (binder d) (atom (fresh-name n binder d) a b made))
                (act-toplevel () (with-name "#%toplevel" n a b made))
                (act-qualified ()
                  (atom (string->symbol (string-append "#%toplevel:" (symbol->string n))) a b made))
                (act-standard () (with-name "#%fx" n a b made))
                (act-module (m) (with-name (symbol->string m) n a b made))
                (else y (atom n a b made))))))))
(define with-name (->* (string symbol int int int) syn)
  (lambda (m n a b made)
    (list-at a b made (list (atom 'with a b made) (atom (string->symbol m) a b made)
                            (atom n a b made))
             nil)))
;; The fresh name of the binder at `binder`, under `d` ellipses, in the
;; repetitions it is in, made the first time.
(define fresh-name (->* (symbol addr int) symbol)
  (lambda (n binder d)
    (let* ((is (ints-prefix (get iters) d)) (known (fresh-of binder is (get fresh))))
      (if (null? known)
          (begin
            (set fresh-count (+ (get fresh-count) 1))
            (let ((f (string->symbol (string-append "%" (symbol->string n) ":"
                                                    (int->string (get fresh-count))))))
              (begin (set fresh (cons (tuple binder is f) (get fresh))) f)))
          (car known)))))
(define fresh-of (->* (addr (listof int acyclic) freshes) (listof symbol acyclic))
  (lambda (p is fs)
    (cond ((null? fs) nil)
          ((and ((with types-module addr=?) p (extract (car fs) 1))
                (ints=? is (extract (car fs) 2)))
           (list (extract (car fs) 3)))
          (else (fresh-of p is (cdr fs))))))
;; Each typed hole's contract, by its pattern variable, in a list of one.
(define contract-of (->* (symbol contracts) syns-a)
  (lambda (n cs)
    (cond ((null? cs) nil)
          ((symbol=? n (extract (car cs) 1)) (list (extract (car cs) 2)))
          (else (contract-of n (cdr cs))))))
;; Whether a template is being transcribed for its check, its holes' calls
;; in place of a use's expressions (`template-checks`).
(define checking (ref bool rs) (new #f))
;; `s`, each part at `a`..`b` of expansion `x`: a hole's call, where the
;; template has the hole.
(define respanned (->* (syn int int int) syn)
  (lambda (s a b x)
    (tagcase s
      (lst (items d c e y) (lst (respanned-each items a b x) d a b x))
      (dotted (items tail d c e y)
        (dotted (respanned-each items a b x) (respanned tail a b x) d a b x))
      (vec (items d c e y) (vec (respanned-each items a b x) d a b x))
      (atom (d c e y) (atom d a b x)))))
(define respanned-each (->* (syns-a int int int) syns-a)
  (lambda (xs a b x)
    (if (null? xs) nil (cons (respanned (car xs) a b x) (respanned-each (cdr xs) a b x)))))
;; `s`, each part of it at a key of its own for its place, in expansion
;; `made`.
(define in-expansion (->* (syn int) syn)
  (lambda (s made)
    (let ((a (source-key (syn-start s) made)))
      (tagcase s
        (lst (items d c e x)
          (let* ((xs (each-in items made)) (b (source-key e made))) (lst xs d a b made)))
        (dotted (items tail d c e x)
          (let* ((xs (each-in items made)) (tl (in-expansion tail made)) (b (source-key e made)))
            (dotted xs tl d a b made)))
        (vec (items d c e x)
          (let* ((xs (each-in items made)) (b (source-key e made))) (vec xs d a b made)))
        (atom (d c e x) (atom d a (source-key e made) made))))))
(define each-in (->* (syns-a int) syns-a)
  (lambda (xs made)
    (if (null? xs) nil (cons (in-expansion (car xs) made) (each-in (cdr xs) made)))))

;;; ------------------------------------------------------------ macros' names

;; Where the last of forms `xs` after this one makes `n` a macro, by
;; `define-syntax` or `import-with-syntax`, in a list of one: as the Rust
;; checker sees it, every macro of the program defined before any
;; definition is checked (`Macros::defined_before`). `fs`, the files read.
(define later-macro-site (->* (symbol syns-a files) places)
  (lambda (n xs fs) (macro-sites n xs fs (get loads) nil)))
