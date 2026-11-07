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
        syn->datum len nth (type syns-a names) (effect parses))
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

;; The macros defined after each form, by the session's state the form left
;; (`form-reading`), which folds in every `define-syntax` before it: so what
;; a form is read with is what its state says, for a program begun in the
;; standard environment's (none), an entry in a session's, or anything read
;; again (`typed-macros.md`, the port's decision 3). Only where some are.
(define by-state (ref (listof (tupleof int macro-env) acyclic) rs) (new nil))
(define macros-at! (->* (int) unit)
  (lambda (s) (set defined (env-at s (get by-state)))))
(define env-at (->* (int (listof (tupleof int macro-env) acyclic)) macro-env)
  (lambda (s xs)
    (cond ((null? xs) nil)
          ((= s (extract (car xs) 1)) (extract (car xs) 2))
          (else (env-at s (cdr xs))))))
(define macros-after! (->* (int) unit)
  (lambda (s)
    (if (null? (get defined)) #u (set by-state (cons (tuple s (get defined)) (get by-state))))))

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
;; By each `with` form's place, the macros used in its body by names the
;; program wrote, each with the use's place (`Macros::with_uses`): the
;; checker refuses the `with` if its module gives a value of the name.
(define with-uses (ref (listof (tupleof int int symbol int int) acyclic) rs) (new nil))
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
