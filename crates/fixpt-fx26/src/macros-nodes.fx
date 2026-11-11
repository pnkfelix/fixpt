;;; Typed hygienic macros, in FX-26: the macros defined, and the nodes
;;; syntax is aligned into (`macros.rs`'s `Node`, `Kids`, `Level`), with the
;;; types of pattern variables and of environments. Part of the expander:
;;; loaded by `macros-align.fx`, which gives all of it on, and loading
;;; `macros-types.fx`, so that every part of the expander takes one
;;; instance of it (one table of `mu`s) through this file.

(module-parameters ((rs region) (re region) (rm region) (rc region) (rp region)))
(define types-module ((proj (load-module "fx26:macros-types.fx") rs re rm rc rp)))
(define parser-module (with types-module parser-module))
(define reader-types (with parser-module reader-types))
(import reader-types atom (type syn))
(import parser-module syn-start syn-end syn-symbol? syn-name syn-symbol len nth
        (type syns-a names) (effect parses))
(import types-module fail-at split syn-nil? syn-keyword? show-syn reserved-syn? reserved? unfold
        fits? sub? kind-of simple-kind? lambda-shaped? proper? kernel-sigs kernel-definitions
        bind-rib bind-cage bind-direct bind-earlier
        ring-rib ring-at s-expr s-bvar s-id s-dvar s-kind
        s-data s-type s-label s-nil s-literal s-pair s-import s-export s-mu s-many s-union s-typed
        mu-body addr=? name-in? proper-items desc-word? atm-var atm-rib-of atm-lit sorted-strings
        seq-elem seq-cage? peel ellipsis? ellipsis-of name-fit-of name-kind?
        joined
        (type fails addr entries ring rings bind sty stys named hole atm atms strings))

;;; ------------------------------------------------------------ macros

;; What becomes of one of a template's parts where it is transcribed
;; (`macros.rs`'s `Action`): a name made fresh, one for the binder at a
;; path and each reference to it; a free name its alias, `%~N:n`, which
;; the resolution after expansion makes the name where the macro is defined
;; (`macros-shapes.fx`'s `aliases-resolved`); a file's macro's description read whole through
;; the file's module or the standard environment, by `select`; a use of
;; another of the file's macros, by the name the importer has it by.
(define-datatype action
  (act-rename addr int) (act-alias) (act-module-type symbol) (act-standard-type)
  (act-macro-head symbol))
(define-type actions (listof (tupleof addr action) acyclic))
;; Where a macro is defined, what its expansions' aliases are read in
;; (`macros/hygiene.rs`'s `Home`): the top level; a file, its hidden global
;; `%shared:key` and the values its module shows (its other names the
;; standard environment's).
;; None, the top level, or one, a file's: a type of its structure, the
;; same in each instance of the expander's files (`macros.fx`'s `homes`).
(define-type home (listof (tupleof symbol names) acyclic))
(define-type homes (listof (tupleof int home) acyclic))
;; A clause: its pattern (of the operands), its template, and its actions,
;; by their paths in the template, the last made first; its pattern's
;; variables, in the order the pattern has them; each typed hole's type as
;; a use reads it, `(select #%toplevel T)`, which the use's expression is
;; held to; and where its macro is defined (`macros.rs`'s `Clause`).
(define-type contracts (listof (tupleof symbol syn) acyclic))
(define-type clause (tupleof syn syn actions pvars contracts home))
(define-type clauses (listof clause acyclic))
;; A macro defined: its signature, its clauses, the binders of its
;; signature's `(poly (binder …) σ)`, if it has one, and what it makes (0 an
;; expression, 1 definitions, `(-> σ defn)`, 2 a description, `(-> σ type)`).
(define-type macro (tupleof sty clauses syns-a int))
(define-type macro-env (listof (tupleof symbol macro) acyclic))
;; The macros defined, each by the name it is used by, the last defined
;; first (`macros.fx`).
(define defined (ref macro-env rs) (new nil))
(define macro-of (->* (symbol macro-env) (listof macro acyclic))
  (lambda (n env)
    (cond ((null? env) nil)
          ((symbol=? n (extract (car env) 1)) (list (extract (car env) 2)))
          (else (macro-of n (cdr env))))))
(define macro? (->* (symbol) bool) (lambda (n) (not (null? (macro-of n (get defined))))))
;; Whether `n` is a macro that makes definitions.
(define makes-defns? (->* (symbol) bool) (lambda (n) (= (makes n) 1)))
;; Whether `n` is a macro a top level's form may make definitions with: one
;; that makes them, or a procedural one (`macros-procedural.fx`), which no
;; signature says.
(define makes-top-defns? (->* (symbol) bool) (lambda (n) (or (= (makes n) 1) (= (makes n) 3))))
;; Whether `n` is a macro that makes a description.
(define makes-desc? (->* (symbol) bool) (lambda (n) (= (makes n) 2)))
(define makes (->* (symbol) int)
  (lambda (n)
    (let ((m (macro-of n (get defined)))) (if (null? m) -1 (extract (car m) 4)))))

;; What a file's macros are defined in (`macros.rs`'s `FileScope`): the
;; hidden global every load of the file is; the values and the types its
;; module shows; each of its macros' names, and the name the importer has
;; it by; and the standard names. None for a program's own.
(define-type scope
  (tupleof symbol names names (listof (tupleof symbol symbol) acyclic) names))
(define-type scopes (listof scope acyclic))

;;; ------------------------------------------------------------ nodes

;; What is in a node: a pair's two; nothing; a pattern variable (in a
;; pattern, or placed in a template); a template's binder, of a
;; description (`#t`) or a value; a name in a template referred to, in a
;; namespace, and what it is if the template does not bind it (0 the top
;; level's value, 1 the top level's qualified, 2 as written, 3 refused, the
;; module a template's `(with m name)` takes from: `macros.rs`'s `Free`); a
;; form in a template, its operands (or, an application's,
;; itself); a description's parts, a list a template writes; a list given
;; by ellipsis, `(p ...)`, its element, repeated; anything else.
(define-datatype kids
  (k-pair int int) (k-nil) (k-pvar symbol) (k-binder symbol bool) (k-ref symbol bool int)
  (k-form int) (k-desc (listof int acyclic)) (k-seq int) (k-other))
;; Each of a node's imports, outermost first, or its export, with the root
;; its addresses are from.
(define-type rooted (listof (tupleof bind int) acyclic))
;; A node of syntax aligned with a syntax type: the syntax; its path from
;; the root; the type at it, its annotations taken off; its imports; its
;; export (none or one); whether its part of the signature is `(many …)`;
;; what is in it; its part's typed hole, if the signature types it (none or
;; one).
(define-type holes (listof hole acyclic))
(define-type node (tupleof syn addr sty rooted rooted bool kids holes))
(define atom-at (subr pure (int) syn) (lambda (a) (atom '() a a 0)))
(define nodes (ref (arrayof node rs) rs)
  (new (make-array 256 (tuple (atom-at 0) (the addr nil) (s-nil) (the rooted nil) (the rooted nil)
                              #f (k-other) (the holes nil)))))
(define nnodes (ref int rs) (new 0))
(define node-at (->* (int) node) (lambda (i) (array-ref (get nodes) i)))
(define node-set! (->* (int node) unit) (lambda (i n) (array-set! (get nodes) i n)))
(define node-syn (->* (int) syn) (lambda (i) (extract (node-at i) 1)))
(define node-path (->* (int) addr) (lambda (i) (extract (node-at i) 2)))
(define node-core (->* (int) sty) (lambda (i) (extract (node-at i) 3)))
(define node-kids (->* (int) kids) (lambda (i) (extract (node-at i) 7)))
(define node-many? (->* (int) bool) (lambda (i) (extract (node-at i) 6)))
(define node-hole (->* (int) holes) (lambda (i) (extract (node-at i) 8)))
;; A node's fields, one of them changed.
(define with-core (->* (int sty) unit)
  (lambda (i t)
    (let ((n (node-at i)))
      (node-set! i (tuple (extract n 1) (extract n 2) t (extract n 4) (extract n 5) (extract n 6)
                          (extract n 7) (extract n 8))))))
(define with-kids (->* (int kids) unit)
  (lambda (i k)
    (let ((n (node-at i)))
      (node-set! i (tuple (extract n 1) (extract n 2) (extract n 3) (extract n 4) (extract n 5)
                          (extract n 6) k (extract n 8))))))
(define with-import (->* (int bind int) unit)
  (lambda (i b root)
    (let ((n (node-at i)))
      (node-set! i (tuple (extract n 1) (extract n 2) (extract n 3)
                          (append (extract n 4) (the rooted (list (tuple b root))))
                          (extract n 5) (extract n 6) (extract n 7) (extract n 8))))))
(define with-export (->* (int bind int) unit)
  (lambda (i b root)
    (let ((n (node-at i)))
      (node-set! i (tuple (extract n 1) (extract n 2) (extract n 3) (extract n 4)
                          (the rooted (list (tuple b root))) (extract n 6) (extract n 7)
                          (extract n 8))))))
(define with-many (->* (int) unit)
  (lambda (i)
    (let ((n (node-at i)))
      (node-set! i (tuple (extract n 1) (extract n 2) (extract n 3) (extract n 4) (extract n 5)
                          #t (extract n 7) (extract n 8))))))
(define with-hole (->* (int hole) unit)
  (lambda (i h)
    (let ((n (node-at i)))
      (node-set! i (tuple (extract n 1) (extract n 2) (extract n 3) (extract n 4) (extract n 5)
                          (extract n 6) (extract n 7) (the holes (list h)))))))
;; A new node, of `s` at `path`, its type `t`: its number.
(define node-new (->* (syn addr sty) int)
  (lambda (s path t)
    (let ((i (get nnodes)))
      (begin
        (if (= i (array-length (get nodes)))
            (let ((bigger (the (arrayof node rs) (make-array (* 2 i) (node-at 0)))))
              (begin (copy-nodes (get nodes) bigger 0) (set nodes bigger)))
            #u)
        (set nnodes (+ i 1))
        (node-set! i (tuple s path t (the rooted nil) (the rooted nil) #f (k-other)
                            (the holes nil)))
        i))))
(define copy-nodes (->* ((arrayof node rs) (arrayof node rs) int) unit)
  (lambda (from to i)
    (if (= i (array-length from))
        #u
        (begin (array-set! to i (array-ref from i)) (copy-nodes from to (+ i 1))))))
;; Whether a program's form is being aligned, after expansion (`macros.rs`'s
;; `Mode::Program`), not a template: its binders and references found as
;; the checkers will read them (`binding-shapes.md`); and the names its
;; walk cannot place, written where an address reaches no part (inside a
;; quasiquoted vector, a `load-moduleof`'s arguments).
(define program-walk (ref bool rs) (new #f))
(define unplaced (ref names rs) (new nil))
;; The nodes forgotten, for another alignment.
(define nodes-reset! (->* () unit)
  (lambda ()
    (begin (set nnodes 0) (set desc-roots nil) (set repeated nil) (set seq-depths nil)
           (set cage-seqs nil))))
;; The nodes an ellipsis follows, so that each is repeated; and, as a walk
;; finds them, each with how many ellipses it is under, itself counted, the
;; last found first (`macros.rs`'s `Node::repeated`, `walk`'s `seqs`).
(define repeated (ref (listof int acyclic) rs) (new nil))
(define seq-depths (ref (listof (tupleof int int) acyclic) rs) (new nil))
(define repeated? (->* (int) bool)
  (lambda (i) (int-member? i (get repeated))))
;; The lists given by ellipsis whose elements are each in the scope of those
;; before it, a ribcage's (`macros.rs`'s `Kids::Seq`'s flag).
(define cage-seqs (ref (listof int acyclic) rs) (new nil))
(define cage-seq? (->* (int) bool)
  (lambda (i) (int-member? i (get cage-seqs))))
(define int-member? (->* (int (listof int acyclic)) bool)
  (lambda (i is) (and (not (null? is)) (or (= i (car is)) (int-member? i (cdr is))))))
;; The nodes of the descriptions a template writes, whole (`macros.rs`'s
;; `Node::desc`).
(define desc-roots (ref (listof int acyclic) rs) (new nil))

;;; ------------------------------------------------------------ pattern variables

;; A pattern variable: its type, its environment as the signature declares
;; it, whether it may be placed any number of times, its typed hole, if
;; the signature types it, and how many ellipses its pattern has it under.
(define-type pinfo (tupleof sty levels bool holes int))
(define-type pvars (listof (tupleof symbol pinfo) acyclic))
(define pvar-of (->* (symbol pvars) (listof pinfo acyclic))
  (lambda (n ps)
    (cond ((null? ps) nil)
          ((symbol=? n (extract (car ps) 1)) (list (extract (car ps) 2)))
          (else (pvar-of n (cdr ps))))))
(define pvar? (->* (symbol pvars) bool) (lambda (n ps) (not (null? (pvar-of n ps)))))
;; 0 if `n` is no pattern variable of `ps`; 1 if it is a name's (`bvar`,
;; `dvar`, `id`, `label`), which is never a list; else 2.
(define pvar-shape (->* (symbol pvars) int)
  (lambda (n ps)
    (let ((p (pvar-of n ps)))
      (cond ((null? p) 0) ((name-kind? (kind-of (extract (car p) 1))) 1) (else 2)))))


;;; ------------------------------------------------------------ binding

;; One level of an environment: a rib, or a pattern variable's ribcage; or,
;; in a repeated element of a ribcage's list, what the repetitions before
;; it bound, which its own binders' names cannot tell from its own
;; (`macros-scopes.fx`).
;; Or, in a program's walk, what the module at a node gives (`bind-shape`),
;; whose names the walk does not know: a name looked for past it may be one
;; of them (`macros.rs`'s `Level::Shape`).
(define-datatype level (lv-rib atms) (lv-cage symbol) (lv-earlier atms) (lv-shape int))
(define-type levels (listof level acyclic))
;; Each pattern variable, template binder and name referred to, by node,
;; with its environment (innermost first), whether it is in a `many` part,
;; and how many ellipses it is under.
(define-type found (listof (tupleof int levels bool int) acyclic))
