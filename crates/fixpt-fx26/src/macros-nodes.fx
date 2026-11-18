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
(import reader-types atom lst dotted vec (type syn))
(import parser-module syn-start syn-end syn-symbol? syn-name syn-symbol len nth
        (type syns-a names) (effect parses))
(import types-module fail-at split syn-nil? syn-keyword? show-syn reserved-syn? reserved? unfold
        sub? kind-of simple-kind? lambda-shaped? proper? kernel-sigs kernel-definitions
        syn-number? s-mark s-lambda s-defn scope-definitions scope-sigs
        bind-rib bind-cage bind-direct bind-earlier
        ring-rib ring-at s-expr s-bvar s-id s-dvar s-kind
        s-data s-type s-label s-nil s-literal s-pair s-import s-export s-mu s-many s-union s-typed
        ring-shape s-rules
        addr=? name-in? proper-items desc-word? atm-var atm-rib-of atm-lit marks mark-in
        seq-elem seq-cage? peel ellipsis? ellipsis-of type-form? syntax-entry?
        (type fails addr entries ring rings bind sty stys named hole atm atms marked))
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
;; path and each reference to it; a free name its alias, `%~K.N:n`, which
;; the resolution after expansion makes the name where the macro is defined
;; (`macros-shapes.fx`'s `aliases-resolved`); a file's macro's description read whole through
;; the file's module or the standard environment, by `select`, or an instance's, its
;; name an alias (`InstanceType`, step 4 (c)); a use of
;; another of the file's macros, by the name the importer has it by.
(define-datatype action
  (act-rename addr int) (act-alias) (act-module-type symbol) (act-instance-type symbol)
  (act-standard-type)
  (act-macro-head symbol)
  ;; A trailmark of a file's a template writes: the name the importer has it by.
  (act-mark symbol))
(define-type actions (listof (tupleof addr action) acyclic))
;; Where a macro is defined, what its expansions' aliases are read in
;; (`macros/hygiene.rs`'s `DefEnv`), by its kind: the top level (0); a file
;; as its importer has it (1), its hidden global `%shared:key` and the
;; values its module shows (its other names the standard environment's); or
;; a module file's items, as its own macros see them (2); or a file as an
;; importer of an instance of it has it (3), the instance's name in place of
;; `%shared:key`, which a binder at a use is kept from capturing. A type of its
;; structure, the same in each instance of the expander's files
;; (`macros.fx`'s `def-envs`).
(define-type def-env (tupleof int symbol names))
(define def-env-top (->* () def-env) (lambda () (tuple 0 'top (the names nil))))
(define-type def-envs (listof (tupleof string def-env) acyclic))
;; A clause: its pattern (of the operands), its template, and its actions,
;; by their paths in the template, the last made first; its pattern's
;; variables, in the order the pattern has them; each typed hole's type as
;; a use reads it, `(select #%toplevel T)`, which the use's expression is
;; held to; where its macro is defined; and its `syntax-rules`'
;; trailmarks, each the binding it is (`macros.rs`'s `Clause`).
(define-type contracts (listof (tupleof symbol syn) acyclic))
;; The last, its template's checked uses, by where each starts
;; (`checked-uses`).
(define-type clause (tupleof syn syn actions pvars contracts def-env marked (listof int acyclic)))
(define-type clauses (listof clause acyclic))
;; A macro defined: its signature, its clauses, the binders of its
;; signature's `(poly (binder …) σ)`, if it has one, and what it makes (0 an
;; expression, 1 definitions, `(macro σ defn)`, 2 a description, `(macro σ desc)`).
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

;; Strings, `xs` sorted onto `out`; and joined, `, ` between.
(define-type strings (listof string acyclic))
(define sorted-strings (->* (strings strings) strings)
  (lambda (xs out) (if (null? xs) out (sorted-strings (cdr xs) (inserted (car xs) out)))))
(define inserted (->* (string strings) strings)
  (lambda (x ys)
    (cond ((null? ys) (list x))
          ((string<? x (car ys)) (cons x ys))
          ((string=? x (car ys)) ys)
          (else (cons (car ys) (inserted x (cdr ys)))))))
(define joined (->* (strings) string)
  (lambda (ss)
    (if (null? (cdr ss)) (car ss) (string-append (car ss) ", " (joined (cdr ss))))))

;;; ------------------------------------------------------------ matching

;; Of union `t`'s members, the one a name is of, in a list of one, if one
;; is; none else, or if `t` is no union.
(define name-fit-of (->* (sty) stys)
  (lambda (t)
    (tagcase t
      (s-union (ms)
        (let ((names (names-of ms))) (if (and (not (null? names)) (null? (cdr names))) names nil)))
      (else y nil))))
(define names-of (->* (stys) stys)
  (lambda (ms)
    (cond ((null? ms) nil)
          ((name-kind? (kind-of (unfold (car ms)))) (cons (car ms) (names-of (cdr ms))))
          (else (names-of (cdr ms))))))
;; Whether kind `k` is a name's: `bvar`, `dvar`, `id`, `label`.
(define name-kind? (->* (int) bool)
  (lambda (k) (or (= k 1) (= k 12) (= k 2) (= k 5))))

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
;; Whether each node is a pending list's (`pending!`), so that a walk asks
;; in one step (`macros.rs`'s `Node::head`).
(define node-heads (ref (arrayof bool rs) rs) (new (make-array 256 #f)))
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
        (array-set! (get node-heads) i #f)
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
      (set repeated-marks (array-grown (get repeated-marks) #f))
      (set node-heads (array-grown (get node-heads) #f)))))
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
;; A program's form read by its scopes (`macros-scopes.fx`'s
;; `program-scoped`; `macros.rs`'s `Aligner::program`, `TODO.md` §295):
;; whether it is, the paths of the lists a macro's name heads read as
;; applications so far, their heads bound around them, and whether any
;; other such list, a use, is aligned no further (where a form is expanded)
;; or by its signature. Each such list pending.
(define scoped-on (ref bool rs) (new #f))
(define scoped-apps (ref (listof addr acyclic) rs) (new nil))
(define scoped-whole (ref bool rs) (new #f))
(define addr-in? (->* (addr (listof addr acyclic)) bool)
  (lambda (p ps) (and (not (null? ps)) (or (addr=? p (car ps)) (addr-in? p (cdr ps))))))
;; The nodes forgotten, for another alignment.
(define nodes-reset! (->* () unit)
  (lambda ()
    (begin (set nnodes 0) (set desc-roots nil) (set repeated nil) (set seq-depths nil)
           (set cage-seqs nil) (set pending nil) (set scoped-on #f))))
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
;; which a program's walk alone knows; a `mu`'s body once, its variable
;; what is around it. As `macros.rs`'s `binds_nothing`.
(define binds-nothing? (->* (sty) bool)
  (lambda (t)
    (tagcase t
      (s-item () #f)
      (s-import (b x) #f)
      (s-export (b x) #f)
      (s-pair (a d) (and (binds-nothing? a) (binds-nothing? d)))
      (s-many (b) (binds-nothing? b))
      (s-typed (b h) (binds-nothing? b))
      (s-union (ms) (all-bind-nothing? ms))
      (s-mu (b r p) (binds-nothing? b))
      (else y #t))))
(define all-bind-nothing? (->* (stys) bool)
  (lambda (ms)
    (or (null? ms) (and (binds-nothing? (car ms)) (all-bind-nothing? (cdr ms))))))
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
;; The trailmark name `n` is bound to, where it is read: its number, or 0
;; (`macros.rs`'s `mark_of`); and so, `ds` the macros and `ms` the
;; trailmarks, for `fits?`, as `pvar-shape`'s are, a trailmark's minus it.
(define mark-now (->* (symbol) int) (lambda (n) (mark-code n (get defined) (get marks))))
(define mark-code (->* (symbol macro-env marked) int)
  (lambda (n ds ms) (if (null? (macro-of n ds)) (mark-in n ms) 0)))
(define union? (->* (sty) bool) (lambda (t) (tagcase t (s-union (ms) #t) (else y #f))))
;; Those of `ms` that `s` fits.
(define fitting (->* (stys syn int pvars) stys)
  (lambda (ms s mode ps)
    (let ((ds (get defined)) (ks (get marks)))
      (cond ((null? ms) nil)
            ((fits? (car ms) s mode
                    (lambda ((n symbol))
                      (let ((p (pvar-shape n ps))) (if (> p 0) p (- 0 (mark-code n ds ks))))))
             (cons (car ms) (fitting (cdr ms) s mode ps)))
            (else (fitting (cdr ms) s mode ps))))))
;; A pattern variable written somewhere inside `s`, in a list of one.
(define pvar-inside (->* (syn pvars) (listof symbol acyclic))
  (lambda (s ps)
    (if (syn-symbol? s)
        (if (pvar? (syn-symbol s) ps) (list (syn-symbol s)) nil)
        (let ((parts (split s)))
          (if (null? parts)
              nil
              (let ((first (pvar-inside (car parts) ps)))
                (if (null? first) (pvar-inside (nth parts 1) ps) first)))))))


;;; ------------------------------------------------------------ binding

;; The name of the binder at node `b`, in a list of one; none if it is no
;; binder: what an environment is told of its atoms (`namer`).
(define binder-name (->* (int) (listof symbol acyclic))
  (lambda (b) (tagcase (node-kids b) (k-binder (m e) (list m)) (else y nil))))
;; Each pattern variable, template binder and name referred to, by node,
;; with its environment, whether it is in a `many` part, and how many
;; ellipses it is under.
(define-type found (listof (tupleof int env bool int) acyclic))

;; Each name in `xs`, onto `out`: names a walk leaves unplaced.
(define symbols-onto (->* (syns-a names) names)
  (lambda (xs out)
    (if (null? xs)
        out
        (symbols-onto (cdr xs)
                      (tagcase (car xs)
                        (lst (items d a b x) (symbols-onto items out))
                        (dotted (items tail d a b x) (symbols-onto (cons tail items) out))
                        (vec (items d a b x) (symbols-onto items out))
                        (else y (if (syn-symbol? (car xs)) (cons (syn-symbol (car xs)) out)
                                  out)))))))
;; Whether `s` is `(with #%fx name)` or `(with #%toplevel name)`.
(define standard-with? (->* (syn) bool)
  (lambda (s)
    (tagcase s
      (lst (items d a b x)
        (and (= (len items) 3) (syn-symbol? (nth items 1)) (syn-symbol? (nth items 2))
             (or (string=? (syn-name (nth items 1)) "#%fx")
                 (string=? (syn-name (nth items 1)) "#%toplevel"))))
      (else y #f))))

;;; ------------------------------------------------------------ module parameters

;; Address `p` and one step more, a car's (`#t`) or a cdr's.
(define addr+ (->* (addr bool) addr) (lambda (p step) (append p (the addr (list step)))))
(define addr-falses (->* (addr int) addr)
  (lambda (a k) (if (= k 0) a (addr-falses (addr+ a #f) (- k 1)))))
;; The binding structure of a program's `module-parameters`' list `bs`:
;; each a value's binder, its type in the scope of those before it, or a
;; description's; each module not `qualified` included in the items, as the
;; checkers make the file (`macros.rs`'s `parameters_sig`).
(define parameters-sig (->* (syn) sty)
  (lambda (bs)
    (let ((ps (proper-items bs)))
      (s-export (s-pair (parameters-list ps) (s-nil))
                (bind-cage (cons (ring-rib (parameter-entries ps 0)) (parameter-shapes ps 0)))))))
(define parameters-list (->* (syns-a) sty)
  (lambda (ps)
    (if (null? ps)
        (s-nil)
        (s-pair (s-union (list (if (binder-is-kind? (car ps))
                                   (s-export (s-pair (s-dvar) (s-data))
                                             (bind-rib (list (tuple (list #t) 4))))
                                   (s-export (s-pair (s-bvar) (s-pair (s-type) (s-data)))
                                             (bind-rib (list (tuple (list #t) 1)))))))
                (parameters-list (cdr ps))))))
(define parameter-entries (->* (syns-a int) entries)
  (lambda (ps k)
    (if (null? ps)
        nil
        (cons (tuple (cons #t (addr+ (addr-falses nil k) #t)) 2)
              (parameter-entries (cdr ps) (+ k 1))))))
(define parameter-shapes (->* (syns-a int) rings)
  (lambda (ps k)
    (cond ((null? ps) nil)
          ((or (binder-is-kind? (car ps)) (not (= (len (proper-items (car ps))) 2)))
           (parameter-shapes (cdr ps) (+ k 1)))
          (else (cons (ring-shape (cons #t (addr+ (addr+ (addr-falses nil k) #t) #t)))
                      (parameter-shapes (cdr ps) (+ k 1)))))))
;; Whether module parameter `b` binds a description, `(name kind)` or `(r
;; region p)`; else it is `(m T)` or `(m T qualified)`, a module
;; (`parse::binder_is_kind`).
(define binder-is-kind? (->* (syn) bool)
  (lambda (b)
    (let ((parts (proper-items b)))
      (cond ((= (len parts) 2) (kind-form? (nth parts 1)))
            ((= (len parts) 3)
             (or (kind-form? (nth parts 1))
                 (not (and (syn-symbol? (nth parts 2)) (string=? (syn-name (nth parts 2))
                                                         "qualified")))))
            (else #t)))))
(define kind-form? (->* (syn) bool)
  (lambda (k)
    (let ((parts (proper-items k)))
      (if (not (null? parts))
          (and (syn-symbol? (car parts)) (string=? (syn-name (car parts)) "=>"))
          (and (syn-symbol? k)
               (name-in? (syn-symbol k)
                         (list 'region 'place 'effect 'type 'data 'sendable 'flat 'size 'conv)))))))

;;; ------------------------------------------------------------ a defined macro's words

;; Whether `n`, in a macro's transformer a template writes, is a word, not a
;; name it refers to: `_`, a form's or a description's word, a macro's
;; definition's, a macro's or a trailmark's name (`Aligner::rules`).
(define rules-word? (->* (fails symbol) bool)
  (lambda (fail n)
    (let ((name (symbol->string n)))
      (or (string=? name "_") (reserved? name)
          (not (null? (sig-of-name n (kernel-sigs fail))))
          (not (null? (sig-of-name n (kernel-definitions fail))))
          (desc-word? name #t) (type-form? name)
          (name-in? n (list 'else '=> 'quote 'quasiquote 'unquote 'unquote-splicing 'syntax-rules
                            'trailmark 'er-macro-transformer 'sc-macro-transformer
                            'rsc-macro-transformer))
          (macro? n) (> (mark-now n) 0)))))
(define sig-of-name (->* (symbol named) (listof sty acyclic))
  (lambda (n ts)
    (cond ((null? ts) nil) ((symbol=? n (extract (car ts) 1)) (list (extract (car ts) 2)))
          (else (sig-of-name n (cdr ts))))))
;; A list's items, a dotted one's before its tail; none of another.
(define rules-items (->* (syn) syns-a)
  (lambda (s)
    (tagcase s (lst (items d a b x) items) (dotted (items t d a b x) items) (else y nil))))
(define any-ellipsis? (->* (syns-a) bool)
  (lambda (xs) (and (not (null? xs)) (or (ellipsis? (car xs)) (any-ellipsis? (cdr xs))))))
(define rules-dots string
  (string-append "`...` in a macro a template defines is the template's (R7RS), and repeats "
                 "nothing here: the defined macro's is written `(... ...)`"))
(define rules-procedural string
  (string-append "a template's `define-syntax` defines a `syntax-rules` macro: a procedural "
                 "one's transformer is phase 1's code, not yet in a template"))
;; `define-syntax`'s operands' binding structure, with a signature if
;; `signed`: `(export (bvar [data] rules) (rho (A var)))`.
(define define-syntax-sig (->* (bool) sty)
  (lambda (signed)
    (let ((rest (s-pair (s-rules) (s-nil))))
      (s-export (s-pair (s-bvar) (if signed (s-pair (s-data) rest) rest))
                (bind-rib (list (tuple (list #t) 1)))))))

;;; ------------------------------------------------------------ shapes

;; Whether `s` has the shape of `t`, in `mode` (0 a pattern, 1 a template,
;; 2 a use, 3 a program's form after expansion): a pattern variable in a
;; template (`pvar?` says 1 for a name's, 2 for another's, 0 for none, and
;; of a trailmark's name minus its number, in any mode) fits
;; anything but, if it is a name, a list's shape; any name in a pattern
;; fits anything. No deeper than `fits-depth` lists: a `union`'s members
;; differ within `overlap?`'s depth, and a long list is not looked through
;; at each of its parts (`macros.rs`'s `FITS_DEPTH`).
(define fits-depth int 8)
(define fits? (->* (sty syn int (subr pure (symbol) int)) bool)
  (lambda (t s mode pvar?) (fits-within? t s mode pvar? fits-depth)))
(define fits-within? (->* (sty syn int (subr pure (symbol) int) int) bool)
  (lambda (t s mode pvar? depth)
    (let ((u (unfold t)) (x (if (>= mode 2) (the syns-a nil) (ellipsis-of s)))
          (program? (= mode 3)))
      (if (not (null? x))
          ;; `(p ...)`, where a list of elements `p` fits may be.
          (let ((e (seq-elem (peel t))))
            (and (not (null? e)) (fits-within? (car e) (car x) mode pvar? depth)))
      (if (and (syn-symbol? s) (< mode 3) (< (pvar? (syn-symbol s)) 0))
          ;; A trailmark, where a use, a pattern or a template writes one:
          ;; itself, a kernel's word of its name, or an `id`.
          (tagcase u
            (s-union (ms) (any-fits? ms s mode pvar? depth))
            (s-mark (n i) (= i (- 0 (pvar? (syn-symbol s)))))
            (s-literal (n) (symbol=? (syn-symbol s) n))
            (s-id () #t)
            (else y #f))
      (if (and (syn-symbol? s)
               (or (and (= mode 0) (not (= (kind-of u) 7)) (not (= (kind-of u) 15))
                        (not (string=? (syn-name s) "_")) (not (string=? (syn-name s) "...")))
                   (and (= mode 1) (> (pvar? (syn-symbol s)) 0)
                        (not (and (= (pvar? (syn-symbol s)) 1)
                                  (or (= (kind-of u) 8) (= (kind-of u) 6) (= (kind-of u) 10)))))))
          #t
          (tagcase u
            (s-union (ms) (any-fits? ms s mode pvar? depth))
            (s-pair (a d)
              (let ((parts (split s)))
                (and (not (null? parts))
                     (or (= depth 0)
                         (and (fits-within? a (car parts) mode pvar? (- depth 1))
                              (fits-within? d (nth parts 1) mode pvar? (- depth 1)))))))
            (s-nil () (syn-nil? s))
            (s-literal (n) (and (syn-symbol? s) (symbol=? (syn-symbol s) n)))
            (s-mark (n i) (and (syn-symbol? s) (= i (- 0 (pvar? (syn-symbol s))))))
            ;; A program's binder: any name the checkers let it bind.
            (s-bvar () (and (syn-symbol? s) (or program? (not (reserved-syn? s)))))
            (s-dvar () (and (syn-symbol? s) (or program? (not (reserved-syn? s)))))
            (s-id () (syn-symbol? s))
            (s-label () (or (syn-keyword? s) (and (>= mode 2) (syn-symbol? s))
                            (and program? (syn-number? s))))
            (s-expr () (and (or program? (not (reserved-syn? s))) (not (syn-nil? s))))
            (s-lambda () (lambda-shaped? s))
            (s-defn () (not (null? (split s))))
            (else y #t))))))))
(define any-fits? (->* (stys syn int (subr pure (symbol) int) int) bool)
  (lambda (ms s mode pvar? depth)
    (and (not (null? ms))
         (or (fits-within? (car ms) s mode pvar? depth) (any-fits? (cdr ms) s mode pvar? depth)))))
;; A `define-syntax` with a signature in a transformer a template writes:
;; its signature a datum.
(define rules-define-sig (->* () sty)
  (lambda ()
    (s-pair (s-rules) (s-pair (s-rules) (s-pair (s-data) (s-pair (s-rules) (s-nil)))))))
;; Whether `s` is a `define-syntax` with a signature.
(define rules-define? (->* (syn) bool)
  (lambda (s)
    (let ((items (proper-items s)))
      (and (= (len items) 4) (syn-symbol? (car items))
           (string=? (syn-name (car items)) "define-syntax")))))
(define rules-escape string "`(... template)` other than `(... ...)`: not yet")

;;; ------------------------------------------------------------ forms' words

(define sig-of (->* (symbol named) stys)
  (lambda (n named)
    (cond ((null? named) nil)
          ((symbol=? n (extract (car named) 1)) (list (extract (car named) 2)))
          (else (sig-of n (cdr named))))))
;; The names of `kernel`'s forms that start with `%`, found once.
(define percent-named (->* (named) names)
  (lambda (kernel)
    (begin
      (if (get percent-found) #u
          (begin (set percent-names (percent-of kernel)) (set percent-found #t)))
      (get percent-names))))
(define percent-found (ref bool rs) (new #f))
(define percent-names (ref names rs) (new nil))
(define percent-of (->* (named) names)
  (lambda (ns)
    (cond ((null? ns) nil)
          ((let ((h (symbol->string (extract (car ns) 1))))
             (and (> (string-length h) 0) (string=? (substring h 0 1) "%")))
           (cons (extract (car ns) 1) (percent-of (cdr ns))))
          (else (percent-of (cdr ns))))))
;; Whether one of `xs` has an `unquote` or `unquote-splicing` in it.
(define any-unquotes? (->* (syns-a) bool)
  (lambda (xs) (and (not (null? xs)) (or (unquotes? (car xs)) (any-unquotes? (cdr xs))))))
(define unquotes? (->* (syn) bool)
  (lambda (s)
    (tagcase s
      (lst (items d a b x) (any-unquotes? items))
      (dotted (items tail d a b x) (or (any-unquotes? items) (unquotes? tail)))
      (vec (items d a b x) (any-unquotes? items))
      (else y (and (syn-symbol? s) (or (string=? (syn-name s) "unquote")
                                       (string=? (syn-name s) "unquote-splicing")))))))
;; Whether a list headed by `hd` constructs: a keyword, or a pattern
;; variable of a `label`.
(define constructs? (->* (syn pvars) bool)
  (lambda (hd ps)
    (or (syn-keyword? hd)
        (and (syn-symbol? hd) (pvar? (syn-symbol hd) ps)
             (= (kind-of (extract (car (pvar-of (syn-symbol hd) ps)) 1)) 5)))))
;; Whether `s` is a definition, by its head: a `begin` one if all it holds
;; are (`macros.rs`'s `defines`).
(define defines? (->* (fails syn) bool)
  (lambda (fail s)
    (let* ((items (proper-items s))
           (head (if (and (not (null? items)) (syn-symbol? (car items))) (syn-name (car items))
                   "")))
      (cond ((string=? head "") #f)
            ((string=? head "begin") (and (not (null? (cdr items))) (all-define? fail (cdr items))))
            (else (let ((n (syn-symbol (car items))))
                    (or (not (null? (sig-of n (kernel-definitions fail))))
                        (not (null? (sig-of n (scope-definitions fail)))))))))))
(define all-define? (->* (fails syns-a) bool)
  (lambda (fail xs) (or (null? xs) (and (defines? fail (car xs)) (all-define? fail (cdr xs))))))

;;; ------------------------------------------------------------ heads read by scope

;; Whether the template being checked uses a macro whose uses define a macro
;; (`Aligner::heads`); how each list read so far as a use of one is, by its
;; place, with that `(macro σ made)` entry's δ; and the lists found pending,
;; each with whether a definition is there, the first found last
;; (`Aligner::pending`). `macros-scopes.fx`'s `aligned-heads` reads them.
(define heads-on (ref bool rs) (new #f))
(define heads (ref (listof (tupleof int int int) acyclic) rs) (new nil))
(define pending (ref (listof (tupleof int bool) acyclic) rs) (new nil))
(define pending! (->* (int bool) unit)
  (lambda (at defn)
    (begin (array-set! (get node-heads) at #t) (set pending (cons (tuple at defn) (get pending))))))
(define pending-node? (->* (int) bool) (lambda (at) (array-ref (get node-heads) at)))
;; How list `s` is read so far: the δ of the `(macro σ made)` entry whose macro
;; it is a use of, in a list of one; none, an application.
(define head-read (->* (syn) (listof int acyclic))
  (lambda (s) (head-at (syn-start s) (syn-end s) (get heads))))
(define head-at (->* (int int (listof (tupleof int int int) acyclic)) (listof int acyclic))
  (lambda (a b hs)
    (cond ((null? hs) nil)
          ((and (= a (extract (car hs) 1)) (= b (extract (car hs) 2))) (list (extract (car hs) 3)))
          (else (head-at a b (cdr hs))))))
;; Each `(macro σ made)` entry's signature, by its δ, read where the signature it
;; is in is (`macros-files.fx`'s `signature-of`): its syntax type, and what
;; it makes.
(define syntax-read (ref (listof (tupleof int sty int) acyclic) rs) (new nil))
(define syntax-read! (->* (int sty int) unit)
  (lambda (d t made) (set syntax-read (cons (tuple d t made) (get syntax-read)))))
(define syntax-sig-read (->* (int) (listof (tupleof sty int) acyclic))
  (lambda (d) (syntax-read-in d (get syntax-read))))
(define syntax-read-in
  (->* (int (listof (tupleof int sty int) acyclic)) (listof (tupleof sty int) acyclic))
  (lambda (d xs)
    (cond ((null? xs) nil)
          ((= d (extract (car xs) 1)) (list (tuple (extract (car xs) 2) (extract (car xs) 3))))
          (else (syntax-read-in d (cdr xs))))))
;; Whether `h`, at a list's head in a template, may be a name a `(macro σ made)`
;; entry binds: no macro's, form's or trailmark's, and no pattern
;; variable's but a binder's (`Aligner::unknown_head`).
(define unknown-head? (->* (fails symbol pvars) bool)
  (lambda (fail h ps)
    (if (pvar? h ps)
        (= (kind-of (extract (car (pvar-of h ps)) 1)) 1)
        (not (or (reserved? (symbol->string h)) (macro? h) (> (mark-now h) 0)
                 (not (null? (sig-of h (kernel-sigs fail))))
                 (not (null? (sig-of h (kernel-definitions fail))))
                 (not (null? (sig-of h (scope-sigs fail))))
                 (not (null? (sig-of h (scope-definitions fail)))))))))
;; Whether template `s` uses a macro whose signature says its uses define a
;; macro, `(ℓ (macro σ made))` (`Macros::uses_syntax_macro`).
(define uses-syntax-macro? (->* (syn) bool)
  (lambda (s)
    (let ((items (proper-items s)))
      (and (not (null? items))
           (or (and (syn-symbol? (car items)) (macro? (syn-symbol (car items)))
                    (tagcase (extract (car (macro-of (syn-symbol (car items)) (get defined))) 1)
                      (s-export (b x) (tagcase x (bind-rib (es) (syntax-entry? es)) (else y #f)))
                      (else y #f)))
               (any-uses-syntax-macro? items))))))
(define any-uses-syntax-macro? (->* (syns-a) bool)
  (lambda (xs)
    (and (not (null? xs)) (or (uses-syntax-macro? (car xs)) (any-uses-syntax-macro? (cdr xs))))))
(define logic-word? (->* (string) bool)
  (lambda (h)
    (or (string=? h "<") (string=? h "<=") (string=? h "=") (string=? h ">") (string=? h ">=")
        (string=? h "not") (string=? h "and") (string=? h "or") (string=? h "implies")
        (string=? h "+") (string=? h "-") (string=? h "*"))))
;; The nodes under node `at`, itself first.
(define under (->* (int) (listof int acyclic))
  (lambda (at)
    (cons at (tagcase (node-kids at)
               (k-pair (x y) (append (under x) (under y)))
               (k-form (x) (under x))
               (k-seq (x) (under x))
               (k-desc (xs) (under-each xs))
               (else y (the (listof int acyclic) nil))))))
(define under-each (->* ((listof int acyclic)) (listof int acyclic))
  (lambda (xs) (if (null? xs) nil (append (under (car xs)) (under-each (cdr xs))))))
;; The `i`th of nodes `ks`.
(define kid (->* ((listof int acyclic) int) int)
  (lambda (ks i) (if (= i 0) (car ks) (kid (cdr ks) (- i 1)))))
(define len-kids (->* ((listof int acyclic)) int)
  (lambda (ks) (if (null? ks) 0 (+ 1 (len-kids (cdr ks))))))
