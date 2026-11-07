;;; Typed hygienic macros, in FX-26: the expander of the front end written
;;; in FX-26, as the Rust one is (`macros.rs`, `docs/research/typed-macros.md`):
;;; a `define-syntax` checked against its signature (Herman's rules) and
;;; defined, and each use of a macro expanded by transcription, the
;;; template's binders made fresh, its free names the top level's, through
;;; `#%toplevel`. Its parts: `macros-types.fx`, the syntax types;
;;; `macros-align.fx`, syntax aligned with them and the macros defined. The
;;; parser runs it on each top-level form before anything else sees it
;;; (`parse-tops`); how it fails is the parser's (`fails`).

(module-parameters ((rs region) (re region) (rm region) (rc region) (rp region)))
(define align-module ((proj (load-module "fx26:macros-align.fx") rs re rm rc rp)))
(define types-module (with align-module types-module))
(define parser-module (with types-module parser-module))
(define reader-types (with parser-module reader-types))
(import reader-types atom lst dotted vec (type syn))
(import parser-module syn-start syn-end syn-symbol? syn-name syn-symbol syn-datums syn-expansion
        syn->datum len nth mk-list mk-symbol datatype? expand-datatype in-loaded-as load-base
        (type syns-a names loaded-file) (effect parses))
;; The module files' forms (`parser-forms.fx`): whether a file takes modules.
(define forms-module ((proj (load-module "fx26:parser-forms.fx") rs re rm rc rp)))
(import types-module fail-at split syn-nil? reserved? reserved-syn? read-sty s-expr
        (type fails addr sty))
(import align-module defined macro-of macro? nodes-reset! align walk placed node-at node-syn
        node-path node-core node-kids pvar-of pvar? nnodes act-rename act-toplevel
        act-toplevel-type act-standard act-module act-module-type act-standard-type
        act-macro-head atm-lit lv-rib k-pvar k-binder k-ref k-form k-other
        (type action actions clause clauses macro macro-env scope scopes pinfo pvars found levels
              atms kids))

;;; ------------------------------------------------------------ clauses

(define clause-usage string "a clause is `((_ . pattern) template)`")
;; Clause `c` checked against signature `sig` (Herman's rules), in a
;; file's scope if `file` has one: its pattern fits the signature, each of
;; the pattern's variables is placed in the template where the signature
;; says what is in scope there, and a reference to a pattern's binder is
;; where no other pattern binder may shadow it.
(define check-clause (->* (fails syn sty scopes) clause)
  (lambda (fail c sig file)
    (let ((two (proper c)))
      (if (not (= (len two) 2))
          (begin (fail-at fail clause-usage c) (stub c))
          (let ((whole (split (car two))))
            (if (null? whole)
                (begin (fail-at fail clause-usage (car two)) (stub c))
                (let* ((pattern (nth whole 1))
                       (ps (pattern-vars fail sig pattern))
                       (template (nth two 1)))
                  (tuple pattern template (template-actions fail ps template file)))))))))
(define stub (->* (syn) clause) (lambda (c) (tuple c c (the actions nil))))
(define proper (->* (syn) syns-a)
  (lambda (s) (tagcase s (lst (items d a b x) items) (else y nil))))
;; The pattern, aligned with the signature: each variable's type and
;; declared environment.
(define pattern-vars (->* (fails sty syn) pvars)
  (lambda (fail sig pattern)
    (begin
      (nodes-reset!)
      (let ((root (align fail 0 (the pvars nil) sig pattern -1 nil)))
        (pvars-of fail (walk fail root nil #f) nil)))))
(define pvars-of (->* (fails found pvars) pvars)
  (lambda (fail fs ps)
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
                  (pvars-of fail (cdr fs)
                            (append ps (the pvars (list (tuple n (tuple (node-core at)
                                                                        (extract (car fs) 2)
                                                                        (extract (car fs) 3)))))))))
            (else y (pvars-of fail (cdr fs) ps)))))))
;; The template, an expression, aligned with the kernel's forms' signatures
;; and the macros', its pattern variables placed by the rules, and what is
;; done to each of its names where it is transcribed.
(define template-actions (->* (fails pvars syn scopes) actions)
  (lambda (fail ps template file)
    (begin
      (nodes-reset!)
      (let* ((root (align fail 1 ps (s-expr) template -1 nil))
             (named (name-actions fail ps (walk fail root nil #f) file nil nil)))
        (type-actions 0 (get nnodes) file named)))))
;; The actions for what the walk found, onto `out`; `uses`, the affine
;; pattern variables placed so far.
(define name-actions (->* (fails pvars found scopes actions names) actions)
  (lambda (fail ps fs file out uses)
    (if (null? fs)
        out
        (let* ((at (extract (car fs) 1)) (env (extract (car fs) 2)) (many (extract (car fs) 3))
               (s (node-syn at)) (path (node-path at)))
          (tagcase (node-kids at)
            (k-pvar (n)
              (let* ((info (car (pvar-of n ps))) (name (symbol->string n))
                     ;; Anything with an expression in it, placed twice, runs
                     ;; twice: placed once, unless its signature says `many`.
                     (affine (and (not (extract info 3)) (affine-kind? (extract info 1)))))
                (begin
                  (placed fail n info (node-core at) env s)
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
                                (if affine (the names (cons n uses)) uses)))))
            (k-binder (n)
              (name-actions fail ps (cdr fs) file (cons (tuple path (act-rename path)) out) uses))
            (k-ref (n)
              (let ((b (binder-of n env)))
                (name-actions fail ps (cdr fs) file
                              (cons (tuple path (ref-action fail n b file s)) out) uses)))
            (else y (name-actions fail ps (cdr fs) file out uses)))))))
(define name-in? (->* (symbol names) bool)
  (lambda (n ns) (and (not (null? ns)) (or (symbol=? n (car ns)) (name-in? n (cdr ns))))))
;; Whether a pattern variable of type `t` has an expression in it: not a
;; binder, name, label, datum or type.
(define affine-kind? (->* (sty) bool)
  (lambda (t)
    (let ((k ((with types-module kind-of) t)))
      (not (or (= k 1) (= k 2) (= k 5) (= k 3) (= k 4))))))
;; A reference to `n`: the template's binder of it, if one binds it in
;; `env` (its node, in a list of one), made fresh with it; else the top
;; level's, or a file's own or a standard name.
(define ref-action (->* (fails symbol (listof int acyclic) scopes syn) action)
  (lambda (fail n b file s)
    (cond ((not (null? b)) (act-rename (node-path (car b))))
          ((null? file) (act-toplevel))
          ((name-in? n (extract (car file) 2)) (act-module (extract (car file) 1)))
          ((name-in? n (extract (car file) 5)) (act-standard))
          (else
           (begin
             (fail-at fail (string-append "`" (symbol->string n) "` is neither a value the file's "
                                          "module shows nor a standard binding: a file's macro "
                                          "names only those, as they are where it is imported")
                      s)
             (act-toplevel))))))
;; The template's binder of `n` in `env`, innermost first: its node.
(define binder-of (->* (symbol levels) (listof int acyclic))
  (lambda (n env)
    (if (null? env)
        nil
        (let ((here (tagcase (car env) (lv-rib (as) (lit-binding n as)) (else y nil))))
          (if (null? here) (binder-of n (cdr env)) here)))))
(define lit-binding (->* (symbol atms) (listof int acyclic))
  (lambda (n as)
    (if (null? as)
        nil
        (let ((rest (lit-binding n (cdr as))))
          (tagcase (car as)
            (atm-lit (t)
              (tagcase (node-kids t)
                (k-binder (m) (if (symbol=? m n) (list t) rest))
                (else y rest)))
            (else y rest))))))
;; Each type the template writes, from node `i` to `n` (none of the use's
;; is in it: a pattern variable is placed only whole), read in the top
;; level's, or, a file's macro's, through the file's module or the
;; standard environment; and a file's macro's use of another of its own.
(define type-actions (->* (int int scopes actions) actions)
  (lambda (i n file out)
    (if (= i n)
        out
        (let* ((path (node-path i)) (kids (node-kids i))
               (typed (and (type-core? (node-core i))
                           (tagcase kids (k-other () #t) (else y #f))))
               (out2 (if typed
                         (cons (tuple path (type-action (node-syn i) file)) out)
                         out))
               (head (form-head-of i)))
          (type-actions (+ i 1) n file
                        (if (and (not (null? file)) (tagcase kids (k-form (x) #t) (else y #f))
                                 (not (null? head))
                                 (not (null? (internal-of (car head) (extract (car file) 4)))))
                            (let ((h (car (internal-of (car head) (extract (car file) 4)))))
                              (cons (tuple path (act-macro-head h)) out2))
                            out2))))))
(define type-core? (->* (sty) bool)
  (lambda (t) (= ((with types-module kind-of) t) 4)))
(define type-action (->* (syn scopes) action)
  (lambda (s file)
    (cond ((null? file) (act-toplevel-type))
          ((and (syn-symbol? s) (not (name-in? (syn-symbol s) (extract (car file) 3))))
           (act-standard-type))
          (else (act-module-type (extract (car file) 1))))))
;; The name at the head of node `i`'s list, in a list of one.
(define form-head-of (->* (int) (listof symbol acyclic))
  (lambda (i)
    (let ((items (proper (node-syn i))))
      (if (and (not (null? items)) (syn-symbol? (car items)))
          (list (syn-symbol (car items)))
          nil))))
(define internal-of (->* (symbol (listof (tupleof symbol symbol) acyclic)) (listof symbol acyclic))
  (lambda (n m)
    (cond ((null? m) nil)
          ((symbol=? n (extract (car m) 1)) (list (extract (car m) 2)))
          (else (internal-of n (cdr m))))))

;;; ------------------------------------------------------------ defining

(define define-usage string "`(define-syntax name signature ((_ . pattern) template) …)`")
;; Whether `s` is a `define-syntax`.
(define defines-syntax? (->* (syn) bool)
  (lambda (s)
    (let ((items (proper s)))
      (and (not (null? items)) (syn-symbol? (car items))
           (string=? (syn-name (car items)) "define-syntax")))))
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
                           (sig (read-sty fail (nth items 2) nil nil))
                           (before (get defined))
                           (undo (lambda ((m string) (a int) (b int))
                                   (begin (set defined before) (fail m a b)))))
                      (begin
                        (set defined (cons (tuple n (tuple sig (the clauses nil))) before))
                        (let ((cs (check-each undo (cdr (cdr (cdr items))) sig file)))
                          (begin (set defined (cons (tuple n (tuple sig cs)) before)) n)))))))))))
(define check-each (->* (fails syns-a sty scopes) clauses)
  (lambda (fail cs sig file)
    (if (null? cs)
        nil
        (let ((c (check-clause fail (car cs) sig file)))
          (cons c (check-each fail (cdr cs) sig file))))))

;;; ------------------------------------------------------------ the session

;; By each `with` form's place, the macros used in its body by names the
;; program wrote, each with the use's place (`Macros::with_uses`): the
;; checker refuses the `with` if its module gives a value of the name.
(define-type uses (listof (tupleof int int symbol int int) acyclic))
(define with-uses (ref uses rs) (new nil))
;; For the checker: this parse's, in the order the expander met them.
(define with-uses-given (->* () uses) (lambda () (reverse (get with-uses))))

;; Each top-level `(define name (load-module "path"))` so far, the last
;; first: the files `import-with-syntax` of `name` reads.
(define-type load-defs (listof (tupleof symbol string) acyclic))
(define loads (ref load-defs rs) (new nil))
;; The macros defined after each form, and the load definitions, by the
;; session's state the form left (`form-reading`), which folds in every
;; form before it: so what a form is read with is what its state says, for
;; a program begun in the standard environment's (none), an entry in a
;; session's, or anything read again (`typed-macros.md`, the port's
;; decision 3). Only where there are some.
;; And the globals defined, which no macro may be named (`globals`).
(define-type by-states (listof (tupleof int macro-env load-defs names) acyclic))
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
            (begin (set defined nil) (set loads nil) (set globals nil))
            (begin (set defined (extract (car at) 2)) (set loads (extract (car at) 3))
                   (set globals (extract (car at) 4))))
        (set globals-before (get globals))))))
(define state-at (->* (int by-states) by-states)
  (lambda (s xs)
    (cond ((null? xs) nil)
          ((= s (extract (car xs) 1)) (the by-states (list (car xs))))
          (else (state-at s (cdr xs))))))
(define macros-after! (->* (int) unit)
  (lambda (s)
    (if (and (null? (get defined)) (null? (get loads)) (null? (get globals)))
        #u
        (set by-state (cons (tuple s (get defined) (get loads) (get globals)) (get by-state))))))
;; Names `ns` defined as globals.
(define globals! (->* (names) unit) (lambda (ns) (set globals (append ns (get globals)))))
;; Whether `n` was a global before this parse.
(define global-before? (->* (symbol) bool) (lambda (n) (name-in? n (get globals-before))))

;;; ------------------------------------------------------------ expanding

;; Each expansion made: its macro's name, and the use's place and its own
;; expansion, by its number less one, the last first; `syn-expansion`
;; says which made a part.
(define expansions (ref (listof (tupleof symbol int int int) acyclic) rs) (new nil))
(define nexpansions (ref int rs) (new 0))
(define record-expansion (->* (symbol syn) int)
  (lambda (name s)
    (begin
      (set expansions (cons (tuple name (syn-start s) (syn-end s) (syn-expansion s))
                            (get expansions)))
      (set nexpansions (+ (get nexpansions) 1))
      (get nexpansions))))
;; The expansions left before one does not end.
(define budget (ref int rs) (new 0))
;; Fresh names' count.
(define fresh-count (ref int rs) (new 0))

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
;; `s` at `a`..`b`, of expansion `x`.
(define at-place (->* (syn int int int) syn)
  (lambda (s a b x)
    (tagcase s
      (atom (d c e y) (atom d a b x))
      (lst (items d c e y) (lst items d a b x))
      (dotted (items tail d c e y) (dotted items tail d a b x))
      (vec (items d c e y) (vec items d a b x)))))
;; `withs`: the places of the `with` forms whose bodies `s` is in.
(define-type places (listof (tupleof int int) acyclic))
(define expand-in (->* (fails syn places) syn)
  (lambda (fail s withs)
    (let* ((items (list-items s)) (hd (if (null? items) s (car items)))
           (head (if (syn-symbol? hd) (syn-name hd) "")))
      (cond
        ((null? items) s)
        ((string=? head "quote") s)
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
      ((and (null? t) (null? xs)) (atom '() a b x))
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
    (let* ((a (syn-start t)) (b (syn-end t)) (act (action-at path (extract c 3)))
           (typed (if (null? act)
                      ""
                      (tagcase (car act)
                        (act-toplevel-type () "#%toplevel")
                        (act-standard-type () "#%fx")
                        (act-module-type (m) (symbol->string m))
                        (else y "")))))
      (cond
        ((not (string=? typed ""))
         (list-at a b made (list (atom 'select a b made) (atom (string->symbol typed) a b made)
                                 (in-expansion t made))
                  nil))
        ((syn-symbol? t) (transcribe-name t (syn-symbol t) a b act bs made))
        ((not (null? (list-items t)))
         (let* ((xs (transcribe-items c (list-items t) path bs made))
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
                               (cdr xs)))))
           (list-at a b made xs2 rest)))
        (else (at-place t a b made))))))
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
(define transcribe-name (->* (syn symbol int int (listof action acyclic) binds int) syn)
  (lambda (t n a b act bs made)
    (let ((given (bound-of n bs)))
      (if (not (null? given))
          (car given)
          (if (null? act)
              (atom n a b made)
              (tagcase (car act)
                (act-rename (binder) (atom (fresh-name n binder) a b made))
                (act-toplevel () (with-name "#%toplevel" n a b made))
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
;; `s`, each part of it at its place in expansion `made`.
(define in-expansion (->* (syn int) syn)
  (lambda (s made)
    (tagcase s
      (lst (items d a b x) (lst (each-in items made) d a b made))
      (dotted (items tail d a b x)
        (dotted (each-in items made) (in-expansion tail made) d a b made))
      (vec (items d a b x) (vec (each-in items made) d a b made))
      (atom (d a b x) (atom d a b made)))))
(define each-in (->* (syns-a int) syns-a)
  (lambda (xs made)
    (if (null? xs) nil (cons (in-expansion (car xs) made) (each-in (cdr xs) made)))))

;;; ------------------------------------------------------------ a file's macros

(define-type files (listof loaded-file acyclic))
(define-type mades (listof (tupleof symbol bool) acyclic))
;; The name at the head of list `s`; "" if none.
(define head-name (->* (syn) string)
  (lambda (s)
    (let ((items (proper s)))
      (if (and (not (null? items)) (syn-symbol? (car items))) (syn-name (car items)) ""))))

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
;; `(load-module "path")`'s path, in a list of one.
(define load-path (->* (syn) (listof string acyclic))
  (lambda (s)
    (let ((items (proper s)))
      (if (and (= (len items) 2) (syn-symbol? (car items))
               (string=? (syn-name (car items)) "load-module"))
          (tagcase (nth items 1) (atom (d a b x) (if (string? d) (list d) nil)) (else y nil))
          nil))))
(define without-load (->* (symbol load-defs) load-defs)
  (lambda (n ls)
    (cond ((null? ls) nil)
          ((symbol=? n (extract (car ls) 1)) (without-load n (cdr ls)))
          (else (cons (car ls) (without-load n (cdr ls)))))))
(define load-of (->* (symbol load-defs) (listof string acyclic))
  (lambda (n ls)
    (cond ((null? ls) nil)
          ((symbol=? n (extract (car ls) 1)) (list (extract (car ls) 2)))
          (else (load-of n (cdr ls))))))

;; The standard bindings' names, which a file's macro may name: what the
;; driver says, as the Rust checker has them (`standard-names!`).
(define standard-names (ref names rs) (new nil))
(define standard-names! (->* (names) unit) (lambda (ns) (set standard-names ns)))

;; Whether `s` is an `import-with-syntax`.
(define imports-syntax? (->* (syn) bool)
  (lambda (s)
    (let ((items (proper s)))
      (and (not (null? items)) (syn-symbol? (car items))
           (string=? (syn-name (car items)) "import-with-syntax")))))
(define import-usage string
  (string-append "`(import-with-syntax name)`, the name a module loaded by `load-module`, or "
                 "`(import-with-syntax name (only name …))` or `(except name …)`"))
;; `(only name …)` or `(except name …)`: whether `only`, and the names, in a
;; list of one; none if there is none.
(define-type filter (tupleof bool syns-a))
(define name-filter (->* (fails syn) filter)
  (lambda (fail f)
    (let* ((items (proper f)) (head (if (and (not (null? items)) (syn-symbol? (car items)))
                                       (syn-name (car items))
                                       "")))
      (if (or (string=? head "only") (string=? head "except"))
          (begin (all-names fail (cdr items)) (tuple (string=? head "only") (cdr items)))
          (begin (fail-at fail import-usage f) (tuple #t (the syns-a nil)))))))
(define all-names (->* (fails syns-a) unit)
  (lambda (fail xs)
    (cond ((null? xs) #u)
          ((syn-symbol? (car xs)) (all-names fail (cdr xs)))
          (else (fail-at fail import-usage (car xs))))))
(define listed? (->* (symbol syns-a) bool)
  (lambda (n xs)
    (and (not (null? xs)) (or (symbol=? n (syn-symbol (car xs))) (listed? n (cdr xs))))))

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
(define not-macros (->* (syns-a names) syns-a)
  (lambda (xs ms)
    (cond ((null? xs) nil)
          ((name-in? (syn-symbol (car xs)) ms) (not-macros (cdr xs) ms))
          (else (cons (car xs) (not-macros (cdr xs) ms))))))

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
;; The file read from `path`, in a list of one.
(define loaded-path (->* (string files) files)
  (lambda (path fs)
    (cond ((null? fs) nil)
          ((and (string=? (extract (car fs) 4) path) (> (extract (car fs) 2) 0))
           (the files (list (car fs))))
          (else (loaded-path path (cdr fs))))))
;; A file's macros, each with whether it is hidden, in order.
(define-type file-macro (tupleof syn bool))
(define file-syntax (->* (syns-a) (listof file-macro acyclic))
  (lambda (forms)
    (cond ((null? forms) nil)
          ((defines-syntax? (car forms))
           (cons (tuple (car forms) #f) (file-syntax (cdr forms))))
          ((hide-form? (car forms))
           (append (hidden-syntax (cdr (proper (car forms)))) (file-syntax (cdr forms))))
          (else (file-syntax (cdr forms))))))
(define hidden-syntax (->* (syns-a) (listof file-macro acyclic))
  (lambda (xs)
    (cond ((null? xs) nil)
          ((defines-syntax? (car xs)) (cons (tuple (car xs) #t) (hidden-syntax (cdr xs))))
          (else (hidden-syntax (cdr xs))))))
(define hide-form? (->* (syn) bool)
  (lambda (s)
    (let ((items (proper s)))
      (string=? (head-name s) "hide"))))
;; The file's forms its module shows: neither macros nor hidden.
(define file-items (->* (syns-a) syns-a)
  (lambda (forms)
    (cond ((null? forms) nil)
          ((or (defines-syntax? (car forms)) (hide-form? (car forms))) (file-items (cdr forms)))
          ((datatype? (car forms))
           (append (expand-datatype (car forms)) (file-items (cdr forms))))
          (else (cons (car forms) (file-items (cdr forms)))))))
;; The values and the types and effects `forms` define, onto `vs` and `ts`:
;; what the module shows. An `include`'s are known only once it is
;; checked: none (`Checker::names_shown`).
(define names-shown (->* (syns-a names names) (tupleof names names))
  (lambda (forms vs ts)
    (if (null? forms)
        (tuple vs ts)
        (let* ((items (proper (car forms)))
               (head (head-name (car forms)))
               (named (if (< (len items) 2) nil (defined-name (nth items 1)))))
          (cond
            ((or (string=? head "define") (string=? head "define*"))
             (names-shown (cdr forms) (append named vs) ts))
            ((string=? head "define-rec")
             (names-shown (cdr forms) (append (rec-names (cdr items)) vs) ts))
            ((string=? head "define-generative")
             (names-shown (cdr forms) (append (generative-values named) vs) (append named ts)))
            ((or (string=? head "define-type") (string=? head "define-effect"))
             (names-shown (cdr forms) vs (append named ts)))
            (else (names-shown (cdr forms) vs ts)))))))
;; A definition's name: `name`, or `(name …)`'s.
(define defined-name (->* (syn) names)
  (lambda (s)
    (cond ((syn-symbol? s) (list (syn-symbol s)))
          ((and (not (null? (proper s))) (syn-symbol? (car (proper s))))
           (list (syn-symbol (car (proper s)))))
          (else nil))))
(define rec-names (->* (syns-a) names)
  (lambda (bs)
    (cond ((null? bs) nil)
          ((and (not (null? (proper (car bs)))) (syn-symbol? (car (proper (car bs)))))
           (cons (syn-symbol (car (proper (car bs)))) (rec-names (cdr bs))))
          (else (rec-names (cdr bs))))))
;; A generative type's conversions, `up-name` and `down-name`.
(define generative-values (->* (names) names)
  (lambda (ns)
    (if (null? ns)
        nil
        (let ((n (symbol->string (car ns))))
          (list (string->symbol (string-append "up-" n))
                (string->symbol (string-append "down-" n)))))))
(define macro-names (->* ((listof file-macro acyclic)) names)
  (lambda (ms)
    (if (null? ms)
        nil
        (let ((n (nth (proper (extract (car ms) 1)) 1)))
          (if (syn-symbol? n)
              (cons (syn-symbol n) (macro-names (cdr ms)))
              (macro-names (cdr ms)))))))
;; Each macro's name the importer has it by, which no program writes.
(define internal-names (->* (string names) (listof (tupleof symbol symbol) acyclic))
  (lambda (key ns)
    (if (null? ns)
        nil
        (cons (tuple (car ns) (string->symbol (string-append "%syntax:" key ":"
                                                             (symbol->string (car ns)))))
              (internal-names key (cdr ns))))))

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
(define taken? (->* (symbol (listof filter acyclic)) bool)
  (lambda (n filter)
    (or (null? filter)
        (if (extract (car filter) 1)
            (listed? n (extract (car filter) 2))
            (not (listed? n (extract (car filter) 2)))))))
(define shown-names (->* (mades) names)
  (lambda (made)
    (cond ((null? made) nil)
          ((extract (car made) 2) (shown-names (cdr made)))
          (else (cons (extract (car made) 1) (shown-names (cdr made)))))))

;;; ------------------------------------------------------------ macros' names

;; Where the last of forms `xs` after this one makes `n` a macro, by
;; `define-syntax` or `import-with-syntax`, in a list of one: as the Rust
;; checker sees it, every macro of the program defined before any
;; definition is checked (`Macros::defined_before`). `fs`, the files read.
(define later-macro-site (->* (symbol syns-a files) places)
  (lambda (n xs fs) (macro-sites n xs fs (get loads) nil)))
(define macro-sites (->* (symbol syns-a files load-defs places) places)
  (lambda (n xs fs ls found)
    (if (null? xs)
        found
        (let* ((x (car xs))
               (here (cond ((defines-syntax? x)
                            (let ((items (proper x)))
                              (and (syn-symbol? (nth items 1))
                                   (symbol=? (syn-symbol (nth items 1)) n))))
                           ((imports-syntax? x) (brings? n x fs ls))
                           (else #f)))
               (found2 (if here (the places (list (tuple (syn-start x) (syn-end x)))) found)))
          (macro-sites n (cdr xs) fs (load-noted x ls) found2)))))
;; `ls` with what form `x` says of a load definition (`note-load-def!`).
(define load-noted (->* (syn load-defs) load-defs)
  (lambda (x ls)
    (let ((items (proper x)))
      (if (and (>= (len items) 3) (string=? (head-name x) "define") (syn-symbol? (nth items 1)))
          (let* ((n (syn-symbol (nth items 1)))
                 (path (load-path (nth items (- (len items) 1))))
                 (kept (without-load n ls)))
            (if (and (not (null? path)) (<= (len items) 4)) (cons (tuple n (car path)) kept) kept))
          ls))))
;; Whether `(import-with-syntax lib …)`, `x`, gives macro `n` its name.
(define brings? (->* (symbol syn files load-defs) bool)
  (lambda (n x fs ls)
    (let* ((items (proper x))
           (path (if (and (>= (len items) 2) (syn-symbol? (nth items 1)))
                     (load-of (syn-symbol (nth items 1)) ls)
                     nil))
           (f (if (null? path) nil (loaded-path (car path) fs))))
      (and (not (null? f))
           (name-in? n (macro-names (shown-syntax (file-syntax (extract (car f) 5)))))
           (or (= (len items) 2) (taken? n (list (lenient-filter (nth items 2)))))))))
(define shown-syntax (->* ((listof file-macro acyclic)) (listof file-macro acyclic))
  (lambda (ms)
    (cond ((null? ms) nil)
          ((extract (car ms) 2) (shown-syntax (cdr ms)))
          (else (cons (car ms) (shown-syntax (cdr ms)))))))
;; `(only name …)` or `(except name …)`, its names those that are names.
(define lenient-filter (->* (syn) filter)
  (lambda (f)
    (tuple (string=? (head-name f) "only") (names-only (cdr (proper f))))))
(define names-only (->* (syns-a) syns-a)
  (lambda (xs)
    (cond ((null? xs) nil)
          ((syn-symbol? (car xs)) (cons (car xs) (names-only (cdr xs))))
          (else (names-only (cdr xs))))))
