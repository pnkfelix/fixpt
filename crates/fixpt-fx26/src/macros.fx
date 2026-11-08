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
(define files-module ((proj (load-module "fx26:macros-files.fx") rs re rm rc rp)))
(define exports-module (with files-module exports-module))
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
(import types-module fail-at split syn-nil? reserved? reserved-syn? read-sty s-expr s-defn
        signature-made pure-hole? affine-kind? int-in?
        (type fails addr sty))
(import align-module defined macro-of macro? makes-defns? nodes-reset! align walk placed node-at
        node-syn node-path node-core node-kids pvar-of pvar? nnodes act-rename act-toplevel
        act-qualified act-standard act-module act-module-type act-standard-type desc-roots under
        act-macro-head atm-lit lv-rib k-pvar k-binder k-ref k-form k-other
        node-hole s-typed evaluate levels-of
        (type action actions clause clauses macro macro-env scope scopes pinfo pvars
              found levels
              atms kids contracts holes))
(import exports-module exports-of exports=? shown-exports nested-binders unsaid-nested
        (type exported nested))
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
;; where no other pattern binder may shadow it.
(define check-clause (->* (fails syn sty bool syns-a scopes) clause)
  (lambda (fail c sig defn poly file)
    (let ((two (proper c)))
      (if (not (= (len two) 2))
          (begin (fail-at fail clause-usage c) (stub c))
          (let ((whole (split (car two))))
            (if (null? whole)
                (begin (fail-at fail clause-usage (car two)) (stub c))
                (let* ((pattern (nth whole 1))
                       (pv (pattern-vars fail sig pattern defn)) (ps (extract pv 1))
                       (template (nth two 1)))
                  (tuple pattern template
                         (template-actions fail ps template defn (extract pv 2) file) ps
                         (contracts-of ps (binder-names poly) file)))))))))
(define stub (->* (syn) clause)
  (lambda (c) (tuple c c (the actions nil) (the pvars nil) (the contracts nil))))
;; The names `poly`'s binders bind.
(define binder-names (->* (syns-a) names)
  (lambda (bs)
    (cond ((null? bs) nil)
          ((and (not (null? (proper (car bs)))) (syn-symbol? (car (proper (car bs)))))
           (cons (syn-symbol (car (proper (car bs)))) (binder-names (cdr bs))))
          (else (binder-names (cdr bs))))))
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
;; Whether syntax `s` names one of `ns`.
(define names-any? (->* (syn names) bool)
  (lambda (s ns)
    (cond ((syn-symbol? s) (name-in? (syn-symbol s) ns))
          ((null? (split s)) #f)
          (else (or (names-any? (car (split s)) ns) (names-any? (nth (split s) 1) ns))))))
;; The pattern, aligned with the signature: each variable's type and
;; declared environment. A macro that makes definitions (`defn`) has no
;; typed parts: what each use defines is checked where it is. And what
;; such a macro's uses define, if its signature says (`(-> (export σ β)
;; defn)`), in a list of one: what a template using it sees, and what its
;; own template is held to.
(define pattern-vars (->* (fails sty syn bool) (tupleof pvars (listof exported acyclic)))
  (lambda (fail sig pattern defn)
    (begin
      (nodes-reset!)
      (let* ((root (align fail 0 (the pvars nil) sig pattern -1 nil))
             (found (walk fail root nil #f))
             (e (extract (node-at root) 5))
             (declared (if (and defn (not (null? e)))
                           (the (listof exported acyclic)
                                (list (exports-of (evaluate fail (extract (car e) 1)
                                                            (extract (car e) 2) pattern))))
                           nil)))
        (tuple (pvars-of fail found nil defn) declared)))))
(define pvars-of (->* (fails found pvars bool) pvars)
  (lambda (fail fs ps defn)
    (if (null? fs)
        ps
        (let ((at (extract (car fs) 1)))
          (tagcase (node-kids at)
            (k-pvar (n)
              (if (pvar? n ps)
                  (begin (fail-at fail (string-append "`" (symbol->string n) "` is a pattern "
                                                      "variable twice")
                                  (node-syn at))
                         ps)
                  (if (and defn (not (null? (node-hole at))))
                      (begin (fail-at fail (string-append "a macro that makes definitions has no "
                                                          "typed parts, not yet: what each use "
                                                          "defines is checked where it is")
                                      (node-syn at))
                             ps)
                      (pvars-of fail (cdr fs)
                                (append ps (the pvars (list (tuple n (tuple (node-core at)
                                                                            (extract (car fs) 2)
                                                                            (extract (car fs) 3)
                                                                            (node-hole at))))))
                                defn))))
            (else y (pvars-of fail (cdr fs) ps defn)))))))
;; The template, an expression or definitions (`defn`), aligned with the
;; kernel's forms' signatures and the macros', its pattern variables placed
;; by the rules, and what is done to each of its names where it is
;; transcribed.
(define template-actions
  (->* (fails pvars syn bool (listof exported acyclic) scopes) actions)
  (lambda (fail ps template defn declared file)
    (begin
      (nodes-reset!)
      (let* ((root (align fail 1 ps (if defn (s-defn) (s-expr)) template -1 nil))
             (found (walk fail root nil #f))
             (nested (nested-binders 0 (get nnodes) ps))
             (named (name-actions fail ps found file nil nil nested)))
        (begin
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
;; The actions for what the walk found, onto `out`; `uses`, the affine
;; pattern variables placed so far.
(define name-actions (->* (fails pvars found scopes actions names nested) actions)
  (lambda (fail ps fs file out uses nested)
    (if (null? fs)
        out
        (let* ((at (extract (car fs) 1)) (env (extract (car fs) 2)) (many (extract (car fs) 3))
               (s (node-syn at)) (path (node-path at)))
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
                                (if affine (the names (cons n uses)) uses) nested))))
            (k-binder (n d)
              (name-actions fail ps (cdr fs) file (cons (tuple path (act-rename path)) out) uses
                            nested))
            (k-ref (n d free)
              (let ((b (binder-of n d env)))
                (begin
                  (if d #u (unsaid-nested fail n b nested s))
                  (let ((act (ref-action fail n b free file s)))
                    (name-actions fail ps (cdr fs) file
                                  (if (null? act) out (cons (tuple path (car act)) out)) uses
                                  nested)))))
            (else y (name-actions fail ps (cdr fs) file out uses nested)))))))
;; A reference to `n`: the template's binder of it, if one binds it in
;; `env` (its node, in a list of one), made fresh with it; else, as `free`
;; says (`k-ref`'s), the top level's, a file's own or a standard name, the
;; top level's qualified, or none (written as it is). In a list of one.
(define ref-action (->* (fails symbol (listof int acyclic) int scopes syn) (listof action acyclic))
  (lambda (fail n b free file s)
    (cond ((not (null? b)) (list (act-rename (node-path (car b)))))
          ((= free 2) nil)
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
;; The template's binder of `n` in `env`, innermost first, in a
;; description's namespace if `d`, else a value's: its node.
(define binder-of (->* (symbol bool levels) (listof int acyclic))
  (lambda (n d env)
    (if (null? env)
        nil
        (let ((here (tagcase (car env) (lv-rib (as) (lit-binding n d as)) (else y nil))))
          (if (null? here) (binder-of n d (cdr env)) here)))))
(define lit-binding (->* (symbol bool atms) (listof int acyclic))
  (lambda (n d as)
    (if (null? as)
        nil
        (let ((rest (lit-binding n d (cdr as))))
          (tagcase (car as)
            (atm-lit (t e)
              (tagcase (node-kids t)
                (k-binder (m f) (if (and (symbol=? m n) (eq? e d)) (list t) rest))
                (else y rest)))
            (else y rest))))))
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
                 (and (not (null? a)) (tagcase (car a) (act-rename (p) #t) (else z #f)))))
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

(define define-usage string "`(define-syntax name signature ((_ . pattern) template) …)`")
;; `(define-syntax name σ ((_ . pattern) template) …)`, checked, in a file's
;; scope if `file` has one, and defined: its name. A template's free name
;; is the top level's where the macro is used (`act-toplevel`). Defined
;; first, so that a template may use the macro itself; what was defined
;; before put back if a clause fails.
(define define-macro (->* (fails syn scopes) symbol)
  (lambda (fail form file)
    (let ((items (proper form)))
      (if (< (len items) 3)
          (begin (fail-at fail define-usage form) (string->symbol ""))
          (let ((name (nth items 1)))
            (if (or (not (syn-symbol? name)) (reserved-syn? name))
                (begin (fail-at fail (string-append define-usage ": a macro's name, not a form's")
                                name)
                       (string->symbol ""))
                (if (null? (cdr (cdr (cdr items))))
                    (begin (fail-at fail (string-append define-usage ": at least one clause") form)
                           (string->symbol ""))
                    (let* ((n (syn-symbol name))
                           ;; `(poly (binder …) σ)`: the binders its typed holes
                           ;; may name.
                           (poly (signature-poly fail (nth items 2)))
                           ;; `(-> σ defn)`: of what it makes, definitions.
                           (made (signature-made fail (extract poly 2)))
                           (defn (extract made 2))
                           (sig (read-sty fail (extract made 1) nil nil))
                           (before (get defined))
                           (undo (lambda ((m string) (a int) (b int))
                                   (begin (set defined before) (fail m a b)))))
                      (begin
                        (set defined (cons (tuple n (tuple sig (the clauses nil) (extract poly 1)
                                                           defn))
                                           before))
                        (let ((cs (check-each undo (cdr (cdr (cdr items))) sig defn
                                              (extract poly 1) file)))
                          (begin
                            (set defined (cons (tuple n (tuple sig cs (extract poly 1) defn))
                                               before))
                            n)))))))))))
;; A signature's `(poly ((name kind) …) σ)`: its binders and `σ`; else none
;; and itself.
(define signature-poly (->* (fails syn) (tupleof syns-a syn))
  (lambda (fail s)
    (let ((items (proper s)))
      (if (and (= (len items) 3) (syn-symbol? (car items)) (string=? (syn-name (car items)) "poly"))
          (if (or (syn-nil? (nth items 1)) (not (null? (proper (nth items 1)))))
              (tuple (proper (nth items 1)) (nth items 2))
              (begin (fail-at fail "a signature's `(poly ((name kind) …) σ)`" (nth items 1))
                     (tuple (the syns-a nil) s)))
          (tuple (the syns-a nil) s)))))
(define check-each (->* (fails syns-a sty bool syns-a scopes) clauses)
  (lambda (fail cs sig defn poly file)
    (if (null? cs)
        nil
        (let ((c (check-clause fail (car cs) sig defn poly file)))
          (cons c (check-each fail (cdr cs) sig defn poly file))))))

;;; ------------------------------------------------------------ the session

;; By each `with` form's place, the macros used in its body by names the
;; program wrote, each with the use's place (`Macros::with_uses`): the
;; checker refuses the `with` if its module gives a value of the name.
(define-type uses (listof (tupleof int int symbol int int) acyclic))
(define with-uses (ref uses rs) (new nil))
;; For the checker: this parse's, in the order the expander met them.
(define with-uses-given (->* () uses) (lambda () (reverse (get with-uses))))

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

;; Where a part a template made is: a key of its own, which no other part
;; and no text has, a place past every text's (`source-base`, above the
;; positions of every file loaded, `load-base` apart), so that two
;; expansions' copies of one part of the template are apart; and, by its
;; key, where the template wrote it and which expansion made it, for what
;; is said of it (`source-of`; the driver's `fx26_span`), as the Rust front
;; end's `Span` has a template's place and its `expansion`. Keys are made
;; in order, a list's start before its parts' and its end after, so that
;; a part is within its list. One table for the session, so that no key is
;; given twice.
(define source-base int 1125899906842624)
(define sources (ref (arrayof (tupleof int int) rs) rs) (new (make-array 1024 (tuple 0 0))))
(define nsources (ref int rs) (new 0))
;; A new key, for template place `p`, of expansion `made`; none in a
;; template's check (`made` 0), whose places are the template's.
(define source-key (->* (int int) int)
  (lambda (p made)
    (if (= made 0) p (new-source-key p made))))
(define new-source-key (->* (int int) int)
  (lambda (p made)
    (let ((i (get nsources)))
      (begin
        (if (= i (array-length (get sources)))
            (let ((bigger (the (arrayof (tupleof int int) rs) (make-array (* 2 i) (tuple 0 0)))))
              (begin (copy-sources (get sources) bigger 0) (set sources bigger)))
            #u)
        (array-set! (get sources) i (tuple p made))
        (set nsources (+ i 1))
        (+ source-base i)))))
(define copy-sources (->* ((arrayof (tupleof int int) rs) (arrayof (tupleof int int) rs) int) unit)
  (lambda (from to i)
    (if (= i (array-length from))
        #u
        (begin (array-set! to i (array-ref from i)) (copy-sources from to (+ i 1))))))
;; Key `k`'s template place and expansion; a place that is no key, itself
;; and 0.
(define source-of (->* (int) (tupleof int int))
  (lambda (k)
    (let ((i (- k source-base)))
      (if (and (>= i 0) (< i (get nsources))) (array-ref (get sources) i) (tuple k 0)))))
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
               (makes-defns? (syn-symbol (car items))))
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
           (head (if (syn-symbol? hd) (syn-name hd) "")))
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
;; The uses of macro `n`, at `hd`, noted in each `with` around it.
(define note-uses (->* (symbol syn places) unit)
  (lambda (n hd withs)
    (if (null? withs)
        #u
        (begin
          (set with-uses (cons (tuple (extract (car withs) 1) (extract (car withs) 2) n
                                      (syn-start hd) (syn-end hd))
                               (get with-uses)))
          (note-uses n hd (cdr withs))))))
;; A list's items (a dotted list's before its tail); none if `s` is no list.
(define list-items (->* (syn) syns-a)
  (lambda (s)
    (tagcase s (lst (items d a b x) items) (dotted (items t d a b x) items) (else y nil))))
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
      (begin
        (nodes-reset!)
        (align in-use 2 (the pvars nil) (extract m 1) operands -1 nil)
        (first-match fail name s operands (extract m 2))))))
(define first-match (->* (fails symbol syn syn clauses) syn)
  (lambda (fail name s operands cs)
    (if (null? cs)
        (begin (fail-at fail (string-append "a use of `" (symbol->string name) "` that no clause "
                                            "of it matches")
                        s)
               s)
        (let ((binds (matched (extract (car cs) 1) operands nil)))
          (if (null? binds)
              (first-match fail name s operands (cdr cs))
              (let ((made (record-expansion name s)))
                (transcribe (car cs) (extract (car cs) 2) nil (car binds) made)))))))

;; Pattern variables' syntax, by name.
(define-type binds (listof (tupleof symbol syn) acyclic))
;; Whether `s` matches pattern `p`, onto `bs`: its bindings, in a list of
;; one; none if not. A name is a pattern variable (`_` anything), a form's
;; name or a keyword itself.
(define matched (->* (syn syn binds) (listof binds acyclic))
  (lambda (p s bs)
    (cond
      ((syn-symbol? p)
       (cond ((string=? (syn-name p) "_") (list bs))
             ((reserved-syn? p)
              (if (and (syn-symbol? s) (symbol=? (syn-symbol s) (syn-symbol p))) (list bs) nil))
             (else (list (cons (tuple (syn-symbol p) s) bs)))))
      ((syn-nil? p) (if (syn-nil? s) (list bs) nil))
      ((not (null? (split p)))
       (let ((ps (split p)) (ss (split s)))
         (if (null? ss)
             nil
             (let ((first (matched (car ps) (car ss) bs)))
               (if (null? first) nil (matched (nth ps 1) (nth ss 1) (car first)))))))
      ((same-atom? p s) (list bs))
      (else nil))))
;; Whether two atoms are the same datum.
(define same-atom? (->* (syn syn) bool)
  (lambda (p s)
    (tagcase p
      (atom (d a b x)
        (tagcase s
          (atom (e c f y)
            (cond ((keyword? d)
                   (and (keyword? e) (symbol=? (keyword->symbol d) (keyword->symbol e))))
                  ((string? d) (and (string? e) (string=? d e)))
                  ((int? d) (and (int? e) (= d e)))
                  ((char? d) (and (char? e) (char=? d e)))
                  ((bool? d) (and (bool? e) (eq? d e)))
                  (else #f)))
          (else z #f)))
      (else y #f))))
(define bound-of (->* (symbol binds) (listof syn acyclic))
  (lambda (n bs)
    (cond ((null? bs) nil)
          ((symbol=? n (extract (car bs) 1)) (list (extract (car bs) 2)))
          (else (bound-of n (cdr bs))))))

;; Each binder's fresh name, by its path.
(define-type freshes (listof (tupleof addr symbol) acyclic))
(define fresh (ref freshes rs) (new nil))
(define action-at (->* (addr actions) (listof action acyclic))
  (lambda (path as)
    (cond ((null? as) nil)
          (((with types-module addr=?) path (extract (car as) 1)) (list (extract (car as) 2)))
          (else (action-at path (cdr as))))))
;; Template `t` of clause `c`, at `path` in it, transcribed by expansion
;; `made`: each part the template makes at its own place in the
;; `define-syntax`, of that expansion, each pattern variable's what the
;; use gave.
(define transcribe (->* (clause syn addr binds int) syn)
  (lambda (c t path bs made)
    (begin
      (if (null? path) (set fresh nil) #u)
      (transcribe-at c t path bs made))))
(define transcribe-at (->* (clause syn addr binds int) syn)
  (lambda (c t path bs made)
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
                (xs (transcribe-items c (list-items t) path bs made))
                (rest (tagcase t
                        (dotted (items tail d c2 e x)
                          (let ((at (append path (falses (len items) nil))))
                            (list (transcribe-at c tail at bs made))))
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
(define transcribe-items (->* (clause syns-a addr binds int) syns-a)
  (lambda (c xs path bs made)
    (if (null? xs)
        nil
        (cons (transcribe-at c (car xs) (append path (the addr (list #t))) bs made)
              (transcribe-items c (cdr xs) (append path (the addr (list #f))) bs made)))))
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
                (act-rename (binder) (atom (fresh-name n binder) a b made))
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
;; The fresh name of the binder at `binder`, made the first time.
(define fresh-name (->* (symbol addr) symbol)
  (lambda (n binder)
    (let ((known (fresh-of binder (get fresh))))
      (if (null? known)
          (begin
            (set fresh-count (+ (get fresh-count) 1))
            (let ((f (string->symbol (string-append "%" (symbol->string n) ":"
                                                    (int->string (get fresh-count))))))
              (begin (set fresh (cons (tuple binder f) (get fresh))) f)))
          (car known)))))
(define fresh-of (->* (addr freshes) (listof symbol acyclic))
  (lambda (p fs)
    (cond ((null? fs) nil)
          (((with types-module addr=?) p (extract (car fs) 1)) (list (extract (car fs) 2)))
          (else (fresh-of p (cdr fs))))))
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

;;; ------------------------------------------------------------ a file's macros


;; Notes a top-level `(define name (load-module "path"))`, the file
;; `import-with-syntax` of `name` reads; any other definition of `name`
;; forgets it (`Checker::note_load_def`).
(define note-load-def! (->* (syn) unit)
  (lambda (form)
    (let ((items (proper form)))
      (if (and (>= (len items) 3) (string=? (head-name form) "define") (syn-symbol? (nth items 1)))
          (let* ((n (syn-symbol (nth items 1)))
                 (path (load-path (nth items (- (len items) 1))))
                 (kept (without-load n (get loads))))
            (set loads (if (and (not (null? path)) (<= (len items) 4))
                           (cons (tuple n (car path)) kept)
                           kept)))
          #u))))

;; The standard bindings' names, which a file's macro may name: what the
;; driver says, as the Rust checker has them (`standard-names!`).
(define standard-names (ref names rs) (new nil))
(define standard-names! (->* (names) unit) (lambda (ns) (set standard-names ns)))


;; `(import-with-syntax lib)`, `lib` a name defined as `(load-module
;; "path")`: the file's macros defined, each as the file means it, and the
;; rest of what it gives as `(include lib)` gives it: that `include`'s form,
;; in a list of one; none if `(only …)` names macros alone. Of `fs`, the
;; files the driver read (`Checker::import_file_macros`).
(define import-file-macros (->* (fails syn files) syns-a)
  (lambda (fail form fs)
    (let* ((items (proper form)) (a (syn-start form)) (b (syn-end form)))
      (if (not (and (or (= (len items) 2) (= (len items) 3)) (syn-symbol? (nth items 1))))
          (begin (fail-at fail import-usage form) nil)
          (let* ((lib (syn-symbol (nth items 1)))
                 (filter (if (= (len items) 3)
                             (the (listof filter acyclic) (list (name-filter fail (nth items 2))))
                             nil))
                 (path (load-of lib (get loads))))
            (if (null? path)
                (begin (fail-at fail (string-append "`import-with-syntax` takes a name defined as "
                                                    "`(load-module \"path\")`, and `"
                                                    (symbol->string lib) "` is not one")
                                form)
                       nil)
                (let ((exported (file-macros fail form (car path) filter fs)))
                  (include-of lib filter exported a b))))))))
;; The `include` that gives the rest: of the names `filter` lists, those
;; not macros.
(define include-of (->* (symbol (listof filter acyclic) names int int) syns-a)
  (lambda (lib filter exported a b)
    (let ((head (list (mk-symbol "include" a b) (mk-symbol (symbol->string lib) a b))))
      (if (null? filter)
          (list (mk-list head a b))
          (let ((rest (not-macros (extract (car filter) 2) exported)))
            (if (and (extract (car filter) 1) (null? rest))
                nil
                (list (mk-list (append head
                                       (list (mk-list (cons (mk-symbol (if (extract (car filter) 1)
                                                                           "only"
                                                                           "except")
                                                                       a b)
                                                            rest)
                                                      a b)))
                               a b))))))))

;; The macros of the file at `path`, defined (`define-file`): the names of
;; those not hidden.
(define file-macros (->* (fails syn string (listof filter acyclic) files) names)
  (lambda (fail form path filter fs)
    (let ((f (loaded-path path fs)))
      (cond
        ((null? f) (begin (fail-at fail (string-append "cannot read `" path "`") form) nil))
        (((with forms-module takes-modules?) (extract (car f) 5))
         (begin (fail-at fail (string-append "`" path "` takes module parameters: its macros "
                                             "cannot be imported, not yet")
                         form)
                nil))
        (else
         (let* ((key (extract (car f) 7)) (base (extract (car f) 2)) (forms (extract (car f) 5))
                ;; An error in the file, said in it, where the form starts.
                (in-file (lambda ((m string) (x int) (y int))
                           (if (and (>= x base) (< x (+ base load-base)))
                               (let ((at (syn-start form)))
                                 (fail (in-loaded-as fs base path m x) at at))
                               (fail m x y))))
                (macros (file-syntax forms))
                (shown (names-shown (file-items forms) nil nil))
                (internal (internal-names key (macro-names macros)))
                (scope (tuple (string->symbol (string-append "%shared:" key)) (extract shown 1)
                              (extract shown 2) internal (get standard-names))))
           (define-file in-file macros scope filter)))))))

;; A file's macros, `ms`, defined as the file means them (`scope`): among
;; themselves first, by their names in it, as its templates name them;
;; then each by the name the importer has it by, and each not hidden that
;; `filter` takes by its own name too. The names of those not hidden.
(define define-file (->* (fails (listof file-macro acyclic) scope (listof filter acyclic)) names)
  (lambda (fail ms scope filter)
    (let ((program (get defined)))
      (begin
        (set defined nil)
        (let* ((made (define-each fail ms scope)) (own (get defined)))
          (begin
            (set defined program)
            (give-each fail made own scope filter
                       (if (null? ms) (atom '() 0 0 0) (extract (car ms) 1)))
            (shown-names made)))))))
(define define-each (->* (fails (listof file-macro acyclic) scope) mades)
  (lambda (fail ms scope)
    (if (null? ms)
        nil
        (let ((n (define-macro fail (extract (car ms) 1) (list scope))))
          (cons (tuple n (extract (car ms) 2)) (define-each fail (cdr ms) scope))))))
(define give-each
  (->* (fails mades macro-env scope (listof filter acyclic) syn) unit)
  (lambda (fail made own scope filter first)
    (if (null? made)
        #u
        (let* ((n (extract (car made) 1)) (m (car (macro-of n own)))
               (internal (car (internal-of n (extract scope 4)))))
          (begin
            (if (and (not (extract (car made) 2)) (taken? n filter))
                (if (macro? n)
                    (fail-at fail (string-append "`" (symbol->string n) "` is a macro defined "
                                                 "already: a file's may not be defined again")
                             first)
                    (set defined (cons (tuple n m) (get defined))))
                #u)
            (set defined (cons (tuple internal m) (get defined)))
            (give-each fail (cdr made) own scope filter first))))))

;;; ------------------------------------------------------------ macros' names

;; Where the last of forms `xs` after this one makes `n` a macro, by
;; `define-syntax` or `import-with-syntax`, in a list of one: as the Rust
;; checker sees it, every macro of the program defined before any
;; definition is checked (`Macros::defined_before`). `fs`, the files read.
(define later-macro-site (->* (symbol syns-a files) places)
  (lambda (n xs fs) (macro-sites n xs fs (get loads) nil)))
