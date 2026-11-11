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
;; The environments the walk resolves names in (`macros-env-types.fx`): their
;; levels, and one implementation of them, whose `env` is abstract outside
;; it (`define-generative`), so that nothing here depends on how it keeps
;; them. The `load-module` below chooses it: `macros-env-indexed.fx`, or
;; `macros-env-list.fx`, which it is held to. Each gives the same
;; operations: none, `env-empty`; `ls`, innermost first, inside `e`,
;; `(env-within e ls name)`; what binds name `n` (a description's if `d`),
;; looked for from place `from` (0, else a `next` of `env-lookup`'s), the
;; first binder in the order of its levels and of each level's atoms;
;; whether a module's names are among its levels; its levels, innermost
;; first, for what compares them by place (a template's checks).
(define env-types ((proj (load-module "fx26:macros-env-types.fx") rs re rm rc rp)))
(import env-types lv-rib lv-cage lv-earlier lv-shape (type level levels namer looked))
(define env-impl ((proj (load-module "fx26:macros-env-indexed.fx") rs re rm rc rp)))
(define-type env (select env-impl env))
(import env-impl env-empty env-within env-lookup env-any-shape? env-levels)

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
;; (`macros/hygiene.rs`'s `DefEnv`), by its kind: the top level (0); a file
;; as its importer has it (1), its hidden global `%shared:key` and the
;; values its module shows (its other names the standard environment's); or
;; a module file's items, as its own macros see them (2). A type of its
;; structure, the same in each instance of the expander's files
;; (`macros.fx`'s `def-envs`).
(define-type def-env (tupleof int symbol names))
(define def-env-top (->* () def-env) (lambda () (tuple 0 'top (the names nil))))
(define-type def-envs (listof (tupleof int def-env) acyclic))
;; A clause: its pattern (of the operands), its template, and its actions,
;; by their paths in the template, the last made first; its pattern's
;; variables, in the order the pattern has them; each typed hole's type as
;; a use reads it, `(select #%toplevel T)`, which the use's expression is
;; held to; and where its macro is defined (`macros.rs`'s `Clause`).
(define-type contracts (listof (tupleof symbol syn) acyclic))
(define-type clause (tupleof syn syn actions pvars contracts def-env))
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
;; The nodes, a field's array each, so that a field set is one store (a
;; program's are a million, each set some times: `TODO.md` §239). `node`,
;; as a tuple, is what a node's fields are, in this order.
(define node-syns (ref (arrayof syn rs) rs) (new (make-array 256 (atom-at 0))))
(define node-paths (ref (arrayof addr rs) rs) (new (make-array 256 (the addr nil))))
(define node-cores (ref (arrayof sty rs) rs) (new (make-array 256 (s-nil))))
(define node-importss (ref (arrayof rooted rs) rs) (new (make-array 256 (the rooted nil))))
(define node-exports (ref (arrayof rooted rs) rs) (new (make-array 256 (the rooted nil))))
(define node-manys (ref (arrayof bool rs) rs) (new (make-array 256 #f)))
(define node-kidss (ref (arrayof kids rs) rs) (new (make-array 256 (k-other))))
(define node-holes (ref (arrayof holes rs) rs) (new (make-array 256 (the holes nil))))
(define nnodes (ref int rs) (new 0))
(define node-syn (->* (int) syn) (lambda (i) (array-ref (get node-syns) i)))
(define node-path (->* (int) addr) (lambda (i) (array-ref (get node-paths) i)))
(define node-core (->* (int) sty) (lambda (i) (array-ref (get node-cores) i)))
(define node-imports (->* (int) rooted) (lambda (i) (array-ref (get node-importss) i)))
(define node-export (->* (int) rooted) (lambda (i) (array-ref (get node-exports) i)))
(define node-many? (->* (int) bool) (lambda (i) (array-ref (get node-manys) i)))
(define node-kids (->* (int) kids) (lambda (i) (array-ref (get node-kidss) i)))
(define node-hole (->* (int) holes) (lambda (i) (array-ref (get node-holes) i)))
;; A node's field, set.
(define with-core (->* (int sty) unit) (lambda (i t) (array-set! (get node-cores) i t)))
(define with-kids (->* (int kids) unit) (lambda (i k) (array-set! (get node-kidss) i k)))
(define with-import (->* (int bind int) unit)
  (lambda (i b root)
    (array-set! (get node-importss) i
                (append (node-imports i) (the rooted (list (tuple b root)))))))
(define with-export (->* (int bind int) unit)
  (lambda (i b root) (array-set! (get node-exports) i (the rooted (list (tuple b root))))))
(define with-many (->* (int) unit) (lambda (i) (array-set! (get node-manys) i #t)))
(define with-hole (->* (int hole) unit)
  (lambda (i h) (array-set! (get node-holes) i (the holes (list h)))))
;; A new node, of `s` at `path`, its type `t`: its number.
(define node-new (->* (syn addr sty) int)
  (lambda (s path t)
    (let ((i (get nnodes)))
      (begin
        (if (= i (array-length (get node-syns))) (nodes-grown!) #u)
        (set nnodes (+ i 1))
        (array-set! (get node-syns) i s)
        (array-set! (get node-paths) i path)
        (array-set! (get node-cores) i t)
        (array-set! (get node-importss) i (the rooted nil))
        (array-set! (get node-exports) i (the rooted nil))
        (array-set! (get node-manys) i #f)
        (array-set! (get node-kidss) i (k-other))
        (array-set! (get node-holes) i (the holes nil))
        (array-set! (get repeated-marks) i #f)
        i))))
;; Each field's array, twice as long.
(define nodes-grown! (->* () unit)
  (lambda ()
    (begin
      (set node-syns (array-grown (get node-syns) (atom-at 0)))
      (set node-paths (array-grown (get node-paths) (the addr nil)))
      (set node-cores (array-grown (get node-cores) (s-nil)))
      (set node-importss (array-grown (get node-importss) (the rooted nil)))
      (set node-exports (array-grown (get node-exports) (the rooted nil)))
      (set node-manys (array-grown (get node-manys) #f))
      (set node-kidss (array-grown (get node-kidss) (k-other)))
      (set node-holes (array-grown (get node-holes) (the holes nil)))
      (set repeated-marks (array-grown (get repeated-marks) #f)))))
;; `a`, in an array twice as long, the rest `fill`.
(define array-grown
  (poly ((t type)) (subr (maxeff (read rs) (write rs) (alloc rs) spin) ((arrayof t rs) t)
                         (arrayof t rs)))
  (plambda ((t type))
    (lambda ((a (arrayof t rs)) (fill t))
      (let ((b (the (arrayof t rs) (make-array (* 2 (array-length a)) fill))))
        (letrec ((copied (subr (maxeff (read rs) (write rs) spin) (int) unit)
                         (lambda (i)
                           (if (= i (array-length a))
                               #u
                               (begin (array-set! b i (array-ref a i)) (copied (+ i 1)))))))
          (begin (copied 0) b))))))
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
;; Each node's whether `repeated` has it, by its number: asked of every
;; node a walk reaches, where the list would be searched each time. Grown
;; with the nodes (`node-new`), which clears each new node's.
(define repeated-marks (ref (arrayof bool rs) rs) (new (make-array 256 #f)))
(define repeated! (->* (int) unit)
  (lambda (e)
    (begin (set repeated (cons e (get repeated))) (array-set! (get repeated-marks) e #t))))
(define repeated? (->* (int) bool)
  (lambda (i) (array-ref (get repeated-marks) i)))
;; The lists given by ellipsis whose elements are each in the scope of those
;; before it, a ribcage's (`macros.rs`'s `Kids::Seq`'s flag).
(define cage-seqs (ref (listof int acyclic) rs) (new nil))
(define cage-seq? (->* (int) bool)
  (lambda (i) (int-member? i (get cage-seqs))))
(define int-member? (->* (int (listof int acyclic)) bool)
  (lambda (i is) (and (not (null? is)) (or (= i (car is)) (int-member? i (cdr is))))))
;; Whether signature `t` binds nothing, as a template may use one of
;; `scope-forms` (`bloblet-ref`'s, `TODO.md` §247): no `import` or `export`
;; in it, so neither a module's item nor its names (`item`, `(shape A)`),
;; which a program's walk alone knows; `mu`s seen through once (`seen`). As
;; `macros.rs`'s `binds_nothing`.
(define binds-nothing? (->* (sty (listof int acyclic)) bool)
  (lambda (t seen)
    (tagcase t
      (s-item () #f)
      (s-import (b x) #f)
      (s-export (b x) #f)
      (s-pair (a d) (and (binds-nothing? a seen) (binds-nothing? d seen)))
      (s-many (b) (binds-nothing? b seen))
      (s-typed (b h) (binds-nothing? b seen))
      (s-union (ms) (all-bind-nothing? ms seen))
      (s-mu (id) (or (int-member? id seen) (binds-nothing? (mu-body id) (cons id seen))))
      (else y #t))))
(define all-bind-nothing? (->* (stys (listof int acyclic)) bool)
  (lambda (ms seen)
    (or (null? ms) (and (binds-nothing? (car ms) seen) (all-bind-nothing? (cdr ms) seen)))))
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

;; The name of the binder at node `b`, in a list of one; none if it is no
;; binder: what an environment is told of its atoms (`namer`).
(define binder-name (->* (int) (listof symbol acyclic))
  (lambda (b) (tagcase (node-kids b) (k-binder (m e) (list m)) (else y nil))))
;; Each pattern variable, template binder and name referred to, by node,
;; with its environment, whether it is in a `many` part, and how many
;; ellipses it is under.
(define-type found (listof (tupleof int env bool int) acyclic))
