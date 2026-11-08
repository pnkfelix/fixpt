;;; Typed hygienic macros, in FX-26: syntax aligned with syntax types, as a
;;; tree of nodes, walked for what binds what (Herman's rules), and a
;;; macro's clause checked against its signature, as the Rust expander has
;;; them (`macros.rs`). Part of the expander (`macros.fx`, which loads it,
;;; and takes `types-module`, this file's instance of `macros-types.fx`,
;;; from it, so that both see one table of `mu`s); the macros defined are
;;; here, which aligning a template looks up.

(module-parameters ((rs region) (re region) (rm region) (rc region) (rp region)))
(define types-module ((proj (load-module "fx26:macros-types.fx") rs re rm rc rp)))
(define parser-module (with types-module parser-module))
(define reader-types (with parser-module reader-types))
(import reader-types atom (type syn))
(import parser-module syn-start syn-end syn-symbol? syn-name syn-symbol len nth
        (type syns-a names) (effect parses))
(import types-module fail-at split syn-nil? syn-keyword? show-syn reserved-syn? reserved? unfold
        fits? sub? kind-of simple-kind? lambda-shaped? proper? kernel-sigs kernel-definitions
        bind-rib bind-cage bind-direct
        ring-rib ring-at s-expr s-bvar s-id s-dvar s-kind
        s-data s-type s-label s-nil s-literal s-pair s-import s-export s-mu s-many s-union s-typed
        mu-body addr=? name-in? proper-items desc-word? atm-var atm-rib-of atm-lit sorted-strings
        seq-elem peel ellipsis? ellipsis-of pattern-names addr-under?
        joined
        (type fails addr entries ring rings bind sty stys named hole atm atms strings))

;;; ------------------------------------------------------------ macros

;; What becomes of one of a template's parts where it is transcribed
;; (`macros.rs`'s `Action`): a name made fresh, one for the binder at a
;; path and each reference to it; a free name the top level's, `(with
;; #%toplevel n)`; a description's free name the top level's, qualified,
;; `#%toplevel:n`; a file's macro's free name the file's own, `(with m
;; n)`, or standard, `(with #%fx n)`; its description read whole through
;; the file's module or the standard environment, by `select`; a use of
;; another of the file's macros, by the name the importer has it by.
(define-datatype action
  (act-rename addr int) (act-toplevel) (act-qualified) (act-standard) (act-module symbol)
  (act-module-type symbol) (act-standard-type) (act-macro-head symbol))
(define-type actions (listof (tupleof addr action) acyclic))
;; A clause: its pattern (of the operands), its template, and its actions,
;; by their paths in the template, the last made first; its pattern's
;; variables, in the order the pattern has them; and each typed hole's
;; type as a use reads it, `(select #%toplevel T)`, which the use's
;; expression is held to (`macros.rs`'s `Clause`).
(define-type contracts (listof (tupleof symbol syn) acyclic))
(define-type clause (tupleof syn syn actions pvars contracts))
(define-type clauses (listof clause acyclic))
;; A macro defined: its signature, its clauses, the binders of its
;; signature's `(poly (binder …) σ)`, if it has one, and whether it makes
;; definitions, `(-> σ defn)`.
(define-type macro (tupleof sty clauses syns-a bool))
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
(define makes-defns? (->* (symbol) bool)
  (lambda (n)
    (let ((m (macro-of n (get defined)))) (and (not (null? m)) (extract (car m) 4)))))

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
;; level's value, 1 the top level's qualified, 2 as written: `macros.rs`'s
;; `Free`); a form in a template, its operands (or, an application's,
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
;; The nodes forgotten, for another alignment.
(define nodes-reset! (->* () unit)
  (lambda () (begin (set nnodes 0) (set desc-roots nil) (set repeated nil) (set seq-depths nil))))
;; The nodes an ellipsis follows, so that each is repeated; and, as a walk
;; finds them, each with how many ellipses it is under, itself counted, the
;; last found first (`macros.rs`'s `Node::repeated`, `walk`'s `seqs`).
(define repeated (ref (listof int acyclic) rs) (new nil))
(define seq-depths (ref (listof (tupleof int int) acyclic) rs) (new nil))
(define repeated? (->* (int) bool)
  (lambda (i) (int-member? i (get repeated))))
(define int-member? (->* (int (listof int acyclic)) bool)
  (lambda (i is) (and (not (null? is)) (or (= i (car is)) (int-member? i (cdr is))))))
;; The nodes of the descriptions a template writes, whole (`macros.rs`'s
;; `Node::desc`).
(define desc-roots (ref (listof int acyclic) rs) (new nil))

;;; ------------------------------------------------------------ aligning

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
      (cond ((null? p) 0)
            ((let ((k (kind-of (extract (car p) 1)))) (or (= k 1) (= k 12) (= k 2) (= k 5))) 1)
            (else 2)))))

;; `s`, at `path`, aligned with type `t`, in `mode` (0 a pattern, 1 a
;; template, 2 a use); `root`, the node its addresses are from, if not
;; itself (-1): its node.
(define align (->* (fails int pvars sty syn int addr) int)
  (lambda (fail mode ps t s root path)
    (let ((at (node-new s path t)))
      (begin (fill fail mode ps at t s (if (< root 0) at root)) at))))
(define path+ (->* (addr bool) addr) (lambda (p step) (append p (the addr (list step)))))

(define fill (->* (fails int pvars int sty syn int) unit)
  (lambda (fail mode ps at t s root)
    (tagcase t
      (s-import (body b) (begin (with-import at b root) (fill fail mode ps at body s root)))
      (s-many (body) (begin (with-many at) (fill fail mode ps at body s root)))
      (s-typed (body h) (begin (with-hole at h) (fill fail mode ps at body s root)))
      (s-export (body b)
        (if (null? (extract (node-at at) 5))
            (begin (with-export at b root) (fill fail mode ps at body s root))
            (fail-at fail "two exports at one part" s)))
      (else y (fill-core fail mode ps at t s root)))))
(define fill-core (->* (fails int pvars int sty syn int) unit)
  (lambda (fail mode ps at t s root)
    (begin
      (with-core at t)
      ;; A pattern's variable, or one placed in a template: at any type.
      (cond ((and (syn-symbol? s)
                  (or (and (= mode 0) (not (= (kind-of (unfold t)) 7))
                           (not (string=? (syn-name s) "_")) (not (ellipsis? s)))
                      (and (= mode 1) (pvar? (syn-symbol s) ps))))
             (with-kids at (k-pvar (syn-symbol s))))
            ((and (not (= mode 2)) (not (null? (ellipsis-of s))))
             (fill-seq fail mode ps at t s (car (ellipsis-of s))))
            ((and (not (= mode 2)) (ellipsis? s))
             (fail-at fail "`...` follows the part it repeats, last in a list" s))
            (else (fill-shape fail mode ps at t s root))))))
;; `(x ...)` at `at`, a pattern's or a template's: `x` aligned with the
;; element type of list type `t`, repeated; the list exports what each
;; element does.
(define fill-seq (->* (fails int pvars int sty syn syn) unit)
  (lambda (fail mode ps at t s x)
    (let ((elem (seq-elem t)))
      (if (null? elem)
          (fail-at fail (string-append "`" (show-syn s) "` repeats a part by `...` where the form "
                                       "takes no list of them")
                   s)
          (let ((e (align fail mode ps (car elem) x -1 (path+ (node-path at) #t))))
            (begin
              (set repeated (cons e (get repeated)))
              (tagcase (node-kids e) (k-pvar (n) (seq-member ps e (car elem) x mode)) (else y #u))
              (with-kids at (k-seq e))
              (let ((ex (extract (node-at e) 5)))
                (if (or (not (null? (extract (node-at at) 5))) (null? ex))
                    #u
                    (with-export at (extract (car ex) 1) (extract (car ex) 2))))))))))
;; A pattern variable at `e` where elements of more than one shape may be:
;; the shape it fits, and what that exports.
(define seq-member (->* (pvars int sty syn int) unit)
  (lambda (ps e elem x mode)
    (tagcase elem
      (s-union (ms)
        (let ((fit (fitting ms x mode ps)))
          (if (and (not (null? fit)) (null? (cdr fit)))
              (begin (tagcase (car fit) (s-export (b bd) (with-export e bd e)) (else y #u))
                     (with-core e (peel (car fit))))
              #u)))
      (else y #u))))
(define fill-shape (->* (fails int pvars int sty syn int) unit)
  (lambda (fail mode ps at t s root)
    (let ((said (lambda ((why string)) (fail-at fail why s)))
          (shown (string-append "`" (show-syn s) "`")))
      (tagcase t
        (s-mu (id) (fill fail mode ps at (mu-body id) s at))
        (s-union (ms)
          (let ((fit (fitting ms s mode ps)))
            (cond ((null? fit) (said (string-append shown " is of none of the shapes this part "
                                                    "may have")))
                  ((null? (cdr fit)) (fill fail mode ps at (car fit) s at))
                  (else (said (string-append shown " could be of more than one of this part's "
                                             "shapes"))))))
        (s-pair (a d)
          (let ((parts (split s)))
            (if (null? parts)
                (said (string-append shown " is not a list as this part must be"))
                (let* ((path (node-path at))
                       (x (align fail mode ps a (car parts) root (path+ path #t)))
                       (y (align fail mode ps d (nth parts 1) root (path+ path #f))))
                  (with-kids at (k-pair x y))))))
        (s-nil ()
          (if (syn-nil? s)
              (with-kids at (k-nil))
              (said (string-append shown " is more than this part may have"))))
        (s-literal (n)
          (if (and (syn-symbol? s) (symbol=? (syn-symbol s) n))
              #u
              (said (string-append shown " where `" (symbol->string n) "` is written"))))
        (s-bvar () (fill-binder fail mode at s #f))
        (s-dvar () (fill-binder fail mode at s #t))
        (s-kind () #u)
        (s-id ()
          (if (syn-symbol? s)
              (if (= mode 1) (with-kids at (k-ref (syn-symbol s) #f 0)) #u)
              (said (string-append shown " is not a variable"))))
        (s-label ()
          (cond ((syn-keyword? s) #u)
                ((and (syn-symbol? s) (= mode 2)) #u)
                ((syn-symbol? s)
                 (said (string-append "a tag or label in a template is a keyword: `#:"
                                      (syn-name s) "`, not `" (syn-name s) "`")))
                (else (said (string-append shown " is not a tag or label")))))
        ;; A template writes a lambda (its form aligned as any of the kernel's);
        ;; a use gives one, of the shape the checkers take.
        (s-lambda ()
          (cond ((and (= mode 1) (not (null? (split s))) (syn-symbol? (car (split s)))
                      (string=? (syn-name (car (split s))) "lambda") (proper? s))
                 (form fail ps at s #f))
                ((and (not (= mode 1)) (lambda-shaped? s)) #u)
                (else (said (string-append shown " is not a lambda, as this part must be")))))
        (s-expr ()
          (cond ((reserved-syn? s)
                 (said (string-append "`" (syn-name s) "` is a form's name, not an expression")))
                ;; `#u`, unit: a literal, which the parsers read as a name.
                ((and (syn-symbol? s) (string=? (syn-name s) "#u")) #u)
                ((and (syn-symbol? s) (= mode 1)) (with-kids at (k-ref (syn-symbol s) #f 0)))
                ((and (not (syn-nil? s)) (not (null? (split s))) (= mode 1)) (form fail ps at s #f))
                ((syn-nil? s) (said "`()` is not an expression"))
                (else #u)))
        (s-defn ()
          (if (and (= mode 1) (not (syn-nil? s)) (not (null? (split s))))
              (form fail ps at s #t)
              (said (string-append shown " is not a definition"))))
        ;; A description a template writes, name by name; the binders of the
        ;; `poly`s at its top, what it exports (what a definition's type puts
        ;; in scope in what it is defined as).
        (s-type ()
          (if (= mode 1)
              (begin (set desc-roots (cons at (get desc-roots)))
                     (desc fail ps at s)
                     (if (null? (extract (node-at at) 5))
                         (with-export at (bind-direct (poly-binders at ps)) at)
                         #u))
              #u))
        ;; `data`.
        (else z
          (let ((inside (pvar-inside s ps)))
            (if (and (= mode 1) (not (null? inside)))
                (said (string-append "pattern variable `" (symbol->string (car inside))
                                     "` inside a quoted datum: only a whole one is placed"))
                #u)))))))
;; A binder at `at`, of a description if `d`, else of a value.
(define fill-binder (->* (fails int int syn bool) unit)
  (lambda (fail mode at s d)
    (cond ((and (syn-symbol? s) (macro? (syn-symbol s)))
           (fail-at fail (string-append "`" (syn-name s) "` is a macro's name, which is not bound")
                    s))
          ((and (syn-symbol? s) (not (reserved-syn? s)) (not (and d (desc-word? (syn-name s) #f))))
           (if (= mode 1) (with-kids at (k-binder (syn-symbol s) d)) #u))
          (else (fail-at fail (string-append "`" (show-syn s) "` is not a name that may be bound")
                         s)))))
;; Those of `ms` that `s` fits.
(define fitting (->* (stys syn int pvars) stys)
  (lambda (ms s mode ps)
    (cond ((null? ms) nil)
          ((fits? (car ms) s mode (lambda ((n symbol)) (pvar-shape n ps)))
           (cons (car ms) (fitting (cdr ms) s mode ps)))
          (else (fitting (cdr ms) s mode ps)))))
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

;; A form in a template, at node `at`: a kernel form, a macro's use, or an
;; application, aligned with its signature; a definition's, if `defn`,
;; where a template makes definitions, else an expression's.
(define form (->* (fails pvars int syn bool) unit)
  (lambda (fail ps at s defn)
    (let* ((parts (split s)) (hd (car parts))
           (head (if (and (syn-symbol? hd) (not (pvar? (syn-symbol hd) ps))) (syn-name hd) ""))
           (kernel (kernel-sigs fail)) (defs (kernel-definitions fail))
           (macro (and (not (string=? head "")) (macro? (syn-symbol hd)))))
      (cond
        (defn
         (cond ((and macro (makes-defns? (syn-symbol hd))) (macro-operands fail ps at hd parts))
               (macro (not-definition fail s (string-append "them by a macro that makes "
                                                            "definitions, not an expression's")))
               ((and (not (string=? head "")) (not (null? (sig-of (string->symbol head) defs))))
                (operands fail ps at (car (sig-of (string->symbol head) defs)) (nth parts 1)))
               (else (not-definition fail s (string-append "`define`, `define*`, `define-rec`, a "
                                                           "`begin` of them, or a use of another "
                                                           "such")))))
        ((and macro (makes-defns? (syn-symbol hd)))
         (fail-at fail (string-append "`" head "` makes definitions, which are made at the top "
                                      "level, not where an expression is")
                  s))
        ((and (not (string=? head "")) (not (null? (sig-of (string->symbol head) defs)))
              (null? (sig-of (string->symbol head) kernel)))
         (fail-at fail (string-append "`" head "` makes a definition, made at the top level by a "
                                      "macro that makes definitions, not where an expression is")
                  s))
        ((string=? head "with")
         (if (standard-with? s)
             #u
             (fail-at fail (string-append "a template's `with` is `(with #%fx name)` or `(with "
                                          "#%toplevel name)` (one opening a module waits for "
                                          "scopes of a module's names)")
                      s)))
        (macro (macro-operands fail ps at hd parts))
        ((and (not (string=? head "")) (not (string=? head "%app"))
              (not (null? (sig-of (string->symbol head) kernel))))
         (operands fail ps at (car (sig-of (string->symbol head) kernel)) (nth parts 1)))
        ((and (not (string=? head "")) (reserved? head))
         (fail-at fail (string-append "the prototype does not know `" head "`'s binding "
                                      "structure: not yet in a template")
                  s))
        (else
         (with-kids at (k-form (align fail 1 ps (car (sig-of '%app kernel)) s -1
                                      (node-path at)))))))))
;; The operands of the use of macro `hd` at `at`, aligned with its signature.
(define macro-operands (->* (fails pvars int syn syns-a) unit)
  (lambda (fail ps at hd parts)
    (operands fail ps at (extract (car (macro-of (syn-symbol hd) (get defined))) 1)
              (nth parts 1))))
(define not-definition (->* (fails syn string) unit)
  (lambda (fail s what)
    (fail-at fail (string-append "`" (show-syn s) "` is not a definition: a macro that makes "
                                 "definitions makes " what)
             s)))
;; The operands `rest` of the form at `at`, aligned with its signature.
(define operands (->* (fails pvars int sty syn) unit)
  (lambda (fail ps at sig rest)
    (with-kids at (k-form (align fail 1 ps sig rest -1 (path+ (node-path at) #f))))))
(define sig-of (->* (symbol named) stys)
  (lambda (n named)
    (cond ((null? named) nil)
          ((symbol=? n (extract (car named) 1)) (list (extract (car named) 2)))
          (else (sig-of n (cdr named))))))
;; Whether `s` is `(with #%fx name)` or `(with #%toplevel name)`.
(define standard-with? (->* (syn) bool)
  (lambda (s)
    (tagcase s
      (lst (items d a b x)
        (and (= (len items) 3) (syn-symbol? (nth items 1)) (syn-symbol? (nth items 2))
             (or (string=? (syn-name (nth items 1)) "#%fx")
                 (string=? (syn-name (nth items 1)) "#%toplevel"))))
      (else y #f))))

;;; ------------------------------------------------------------ descriptions

;; The `i`th of nodes `ks`.
(define kid (->* ((listof int acyclic) int) int)
  (lambda (ks i) (if (= i 0) (car ks) (kid (cdr ks) (- i 1)))))
;; Description `s`, which a template writes, at node `at`, aligned name by
;; name (`macros.rs`'s `Aligner::desc`): each name referred to in the
;; description namespace, the top level's if the template does not bind it;
;; but a word of descriptions written as it is, a pattern variable placed,
;; and what `poly`, `dlambda`, `mu` and `dletrec` bind in scope in what
;; follows. Labels, a `restrict`'s names and an `io` effect's kind are
;; written as they are; `(globals g …)`'s names and `(select m n)`'s module
;; are values.
(define desc (->* (fails pvars int syn) unit)
  (lambda (fail ps at s)
    (tagcase s
      (lst (items d a b x) (if (null? items) #u (desc-list fail ps at s items)))
      (dotted (items tail d a b x) (fail-at fail "a description is a list, not a dotted one" s))
      (else y
        (if (syn-symbol? s)
            (let ((n (syn-symbol s)))
              (with-kids at (cond ((pvar? n ps) (k-pvar n))
                                  ((desc-word? (syn-name s) #f) (k-other))
                                  (else (k-ref n #t 1)))))
            #u)))))
(define desc-list (->* (fails pvars int syn syns-a) unit)
  (lambda (fail ps at s items)
    (let* ((kids (desc-kids at items)) (h (car items))
           (head (if (and (syn-symbol? h) (not (pvar? (syn-symbol h) ps))) (syn-name h) ""))
           (not-yet (lambda ((what string))
                      (fail-at fail (string-append what " in a template's description: not yet")
                               s))))
      (cond
        ((or (string=? head "poly") (string=? head "dlambda"))
         (if (= (len items) 3)
             (desc-scoped fail ps (kid kids 2) (nth items 2)
                          (desc-binders fail ps (kid kids 1) (nth items 1)))
             (fail-at fail (string-append "`(" head " ((name kind) …) description)`") s)))
        ((string=? head "mu")
         (if (= (len items) 3)
             (desc-scoped fail ps (kid kids 2) (nth items 2)
                          (list (desc-binder fail ps (kid kids 1) (nth items 1))))
             (fail-at fail "`(mu name type)`" s)))
        ((string=? head "dletrec")
         (if (= (len items) 3)
             (desc-dletrec fail ps kids items)
             (fail-at fail "`(dletrec ((name description) …) description)`" s)))
        ((or (string=? head "productof") (string=? head "sumof"))
         (desc-fields fail ps (cdr kids) (cdr items)))
        ((and (string=? head "restrict") (>= (len items) 2))
         (desc fail ps (kid kids 1) (nth items 1)))
        ((string=? head "io") #u)
        ;; Values: a global's name, written as it is, since no local can
        ;; shadow it; a module's, the top level's.
        ((string=? head "globals") (desc-values fail ps (cdr kids) 2))
        ((string=? head "select")
         (desc-values fail ps (if (null? (cdr kids)) nil (list (kid kids 1))) 1))
        ((string=? head "moduleof") (not-yet "a `moduleof`"))
        ((and (not (string=? head "")) (desc-word? head #t))
         (let ((no (if (or (string=? head "subr") (string=? head "->") (string=? head "->*"))
                       (subr-refused (cdr items))
                       "")))
           (if (string=? no "") (desc-each fail ps (cdr kids) (cdr items)) (not-yet no))))
        ;; A description function applied, its name the head.
        (else (desc-each fail ps kids items))))))
;; What of a `subr`'s parts `xs` the prototype does not take in a template:
;; a specification's clause, or a parameter named; "" if neither.
(define subr-refused (->* (syns-a) string)
  (lambda (xs)
    (if (null? xs)
        ""
        (let* ((parts (proper-items (car xs)))
               (head (if (and (not (null? parts)) (syn-symbol? (car parts)))
                         (syn-name (car parts))
                         "")))
          (cond ((or (string=? head "requires") (string=? head "ensures"))
                 "a specification's clause")
                ((named-param? parts) "a parameter named, `(name : type)`,")
                (else (subr-refused (cdr xs))))))))
(define named-param? (->* (syns-a) bool)
  (lambda (ps)
    (and (not (null? ps))
         (or (let ((q (proper-items (car ps))))
               (and (>= (len q) 2) (syn-symbol? (nth q 1)) (string=? (syn-name (nth q 1)) ":")))
             (named-param? (cdr ps))))))
(define desc-each (->* (fails pvars (listof int acyclic) syns-a) unit)
  (lambda (fail ps ks xs)
    (if (or (null? xs) (null? ks))
        #u
        (begin (desc fail ps (car ks) (car xs)) (desc-each fail ps (cdr ks) (cdr xs))))))
;; A node for each of `items`, the parts of the list at node `at`, at their
;; paths in it: `at`'s kids.
(define desc-kids (->* (int syns-a) (listof int acyclic))
  (lambda (at items)
    ;; `p ...` last: `p` repeated, the `...` no part of its own.
    (let* ((n (len items)) (again (and (>= n 2) (ellipsis? (nth items (- n 1)))))
           (kids (desc-kids-from (if again (the syns-a (reverse (cdr (reverse items)))) items)
                                 (node-path at) nil)))
      (begin
        (if (and again (not (null? kids)))
            (set repeated (cons (car (the (listof int acyclic) (reverse kids))) (get repeated)))
            #u)
        (with-kids at (k-desc kids))
        kids))))
(define desc-kids-from (->* (syns-a addr (listof int acyclic)) (listof int acyclic))
  (lambda (items path out)
    (if (null? items)
        (the (listof int acyclic) (reverse out))
        (let ((k (node-new (car items) (path+ path #t) (s-type))))
          (desc-kids-from (cdr items) (path+ path #f) (cons k out))))))
;; Description `s` at node `at`, in the scope of `as`.
(define desc-scoped (->* (fails pvars int syn atms) unit)
  (lambda (fail ps at s as) (begin (with-import at (bind-direct as) at) (desc fail ps at s))))
;; A description's binder `n`, at node `at`: a pattern variable (a `dvar`
;; the use gives), or a name the template binds; what it binds.
(define desc-binder (->* (fails pvars int syn) atm)
  (lambda (fail ps at n)
    (begin
      (with-core at (s-dvar))
      (cond ((and (syn-symbol? n) (pvar? (syn-symbol n) ps))
             (begin (with-kids at (k-pvar (syn-symbol n))) (atm-var (syn-symbol n) #t)))
            ((and (syn-symbol? n) (not (reserved-syn? n)) (not (desc-word? (syn-name n) #f)))
             (begin (with-kids at (k-binder (syn-symbol n) #t)) (atm-lit at #t)))
            (else (begin (fail-at fail (string-append "`" (show-syn n) "` is not a name that may "
                                                      "be bound")
                                  n)
                         (atm-lit at #t)))))))
;; `((name kind) …)` at node `at`, a binder's place or `distinct` third if
;; any, each in the scope of those before it: what they bind.
(define desc-binders (->* (fails pvars int syn) atms)
  (lambda (fail ps at bs)
    (let ((entries (proper-items bs)))
      (desc-binders-from fail ps (desc-kids at entries) entries nil))))
(define desc-binders-from (->* (fails pvars (listof int acyclic) syns-a atms) atms)
  (lambda (fail ps ks es out)
    (if (or (null? es) (null? ks))
        out
        (let* ((parts (proper-items (car es))) (n (len parts)))
          (if (or (= n 2) (= n 3))
              (let* ((p (desc-kids (car ks) parts))
                     (a (desc-binder fail ps (car p) (car parts))))
                (begin
                  (if (= n 3) (desc-scoped fail ps (kid p 2) (nth parts 2) out) #u)
                  (desc-binders-from fail ps (cdr ks) (cdr es) (append out (the atms (list a))))))
              (begin (fail-at fail "a binder is `(name kind)`" (car es)) out))))))
;; `(dletrec ((name description) …) body)`'s parts: each name in scope in
;; each description and the body.
(define-type dparts (listof (tupleof atm int syn) acyclic))
(define desc-dletrec (->* (fails pvars (listof int acyclic) syns-a) unit)
  (lambda (fail ps kids items)
    (let* ((entries (proper-items (nth items 1)))
           (parts (dletrec-parts fail ps (desc-kids (kid kids 1) entries) entries))
           (as (dparts-atms parts)))
      (begin (dparts-each fail ps parts as) (desc-scoped fail ps (kid kids 2) (nth items 2) as)))))
(define dletrec-parts (->* (fails pvars (listof int acyclic) syns-a) dparts)
  (lambda (fail ps ks es)
    (if (or (null? es) (null? ks))
        nil
        (let ((parts (proper-items (car es))))
          (if (= (len parts) 2)
              (let* ((p (desc-kids (car ks) parts)) (a (desc-binder fail ps (car p) (car parts))))
                (cons (tuple a (kid p 1) (nth parts 1)) (dletrec-parts fail ps (cdr ks) (cdr es))))
              (begin (fail-at fail "`(name description)`" (car es)) (the dparts nil)))))))
(define dparts-atms (->* (dparts) atms)
  (lambda (ds) (if (null? ds) nil (cons (extract (car ds) 1) (dparts-atms (cdr ds))))))
(define dparts-each (->* (fails pvars dparts atms) unit)
  (lambda (fail ps ds as)
    (if (null? ds)
        #u
        (begin (desc-scoped fail ps (extract (car ds) 2) (extract (car ds) 3) as)
               (dparts-each fail ps (cdr ds) as)))))
;; `(label type)`s at nodes `ks`.
(define desc-fields (->* (fails pvars (listof int acyclic) syns-a) unit)
  (lambda (fail ps ks fs)
    (if (or (null? fs) (null? ks))
        #u
        (let ((parts (proper-items (car fs))))
          (if (= (len parts) 2)
              (begin (desc fail ps (kid (desc-kids (car ks) parts) 1) (nth parts 1))
                     (desc-fields fail ps (cdr ks) (cdr fs)))
              (fail-at fail "`(label type)`" (car fs)))))))
;; Names of values at nodes `ks`, each the top level's if free (`free` 1)
;; or as written (2), or a pattern variable placed.
(define desc-values (->* (fails pvars (listof int acyclic) int) unit)
  (lambda (fail ps ks free)
    (if (null? ks)
        #u
        (let ((s (node-syn (car ks))))
          (if (syn-symbol? s)
              (begin
                (with-core (car ks) (s-id))
                (with-kids (car ks) (if (pvar? (syn-symbol s) ps)
                                        (k-pvar (syn-symbol s))
                                        (k-ref (syn-symbol s) #f free)))
                (desc-values fail ps (cdr ks) free))
              (fail-at fail "a name" s))))))
;; The binders of the `poly`s at the top of the description at node `at`,
;; outermost first (`Checker::bind_signature`'s).
(define poly-binders (->* (int pvars) atms)
  (lambda (at ps)
    (let ((items (proper-items (node-syn at))))
      (tagcase (node-kids at)
        (k-desc (kids)
          (if (and (= (len items) 3) (syn-symbol? (car items))
                   (string=? (syn-name (car items)) "poly")
                   (not (pvar? (syn-symbol (car items)) ps)))
              (append (entry-binders (tagcase (node-kids (kid kids 1))
                                       (k-desc (es) es)
                                       (else y (the (listof int acyclic) nil))))
                      (poly-binders (kid kids 2) ps))
              (the atms nil)))
        (else y (the atms nil))))))
(define entry-binders (->* ((listof int acyclic)) atms)
  (lambda (es)
    (if (null? es)
        nil
        (let ((rest (entry-binders (cdr es))))
          (tagcase (node-kids (car es))
            (k-desc (parts)
              (tagcase (node-kids (car parts))
                (k-pvar (n) (cons (atm-var n #t) rest))
                (k-binder (n d) (cons (atm-lit (car parts) #t) rest))
                (else y rest)))
            (else y rest))))))
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

;;; ------------------------------------------------------------ binding

;; One level of an environment: a rib, or a pattern variable's ribcage.
(define-datatype level (lv-rib atms) (lv-cage symbol))
(define-type levels (listof level acyclic))
;; Each pattern variable, template binder and name referred to, by node,
;; with its environment (innermost first), whether it is in a `many` part,
;; and how many ellipses it is under.
(define-type found (listof (tupleof int levels bool int) acyclic))

;; The tree under `at`, walked with environment `env`, under `depth0`
;; ellipses: what it finds, in the order a walk finds them; each node an
;; ellipsis follows noted in `seq-depths`.
(define walk (->* (fails int levels bool int) found)
  (lambda (fail at env many0 depth0)
    (let* ((many (or many0 (node-many? at)))
           (depth (if (repeated? at) (+ depth0 1) depth0))
           (noted (if (repeated? at) (set seq-depths (cons (tuple at depth) (get seq-depths))) #u))
           (env2 (imported fail (extract (node-at at) 4) env (node-syn at))))
      (tagcase (node-kids at)
        (k-pair (x y) (append (walk fail x env2 many depth) (walk fail y env2 many depth)))
        (k-form (x) (walk fail x env2 many depth))
        (k-seq (x) (walk fail x env2 many depth))
        (k-desc (xs) (walk-each fail xs env2 many depth))
        (k-pvar (n) (the found (list (tuple at env2 many depth))))
        (k-binder (n d) (the found (list (tuple at env2 many depth))))
        (k-ref (n d free) (the found (list (tuple at env2 many depth))))
        (else y (the found nil))))))
(define walk-each (->* (fails (listof int acyclic) levels bool int) found)
  (lambda (fail xs env many depth)
    (if (null? xs)
        nil
        (let ((first (walk fail (car xs) env many depth)))
          (append first (walk-each fail (cdr xs) env many depth))))))
;; `env` with what each import binds before it, the last import innermost.
(define imported (->* (fails rooted levels syn) levels)
  (lambda (fail is env s)
    (if (null? is)
        env
        (imported fail (cdr is)
                  (append (evaluate fail (extract (car is) 1) (extract (car is) 2) s) env) s))))
;; What `b` binds, its addresses from `root`: levels, innermost first.
(define evaluate (->* (fails bind int syn) levels)
  (lambda (fail b root s)
    (tagcase b
      (bind-rib (es) (list (lv-rib (rib fail es root s))))
      (bind-cage (rings) (cage fail rings root s))
      (bind-direct (as) (list (lv-rib as))))))
(define cage (->* (fails rings int syn) levels)
  (lambda (fail rings root s)
    (if (null? rings)
        nil
        (append (tagcase (car rings)
                  (ring-rib (es) (the levels (list (lv-rib (rib fail es root s)))))
                  (ring-at (a) (levels-of fail (nav fail root a s) s)))
                (cage fail (cdr rings) root s)))))
(define rib (->* (fails entries int syn) atms)
  (lambda (fail es root s)
    (if (null? es)
        nil
        (let* ((t (nav fail root (extract (car es) 1) s)) (delta (extract (car es) 2))
               (ts (node-syn t)) (rest (rib fail (cdr es) root s)))
          (tagcase (node-kids t)
            (k-pvar (n)
              (cond ((binder-delta? delta) (append (binder-atms fail t delta) rest))
                    ;; A use's description: what its own `poly`s bind is the
                    ;; use's, which nothing the template writes can name.
                    ((and (= delta 2) (= (kind-of (node-core t)) 4)) rest)
                    ((= delta 2) (cons (atm-rib-of n) rest))
                    ((= delta 3) (begin (env-in-rib fail ts) rest))
                    (else rest)))
            (k-binder (n d)
              (cond ((binder-delta? delta) (append (binder-atms fail t delta) rest))
                    ((= delta 2) (append (exported-rib fail t ts s) rest))
                    ((= delta 3) (begin (env-in-rib fail ts) rest))
                    (else rest)))
            (else y
              (cond ((binder-delta? delta) (append (binder-atms fail t delta) rest))
                    ((= delta 2) (append (exported-rib fail t ts s) rest))
                    ((= delta 3) (begin (env-in-rib fail ts) rest))
                    (else rest))))))))
;; Whether δ `delta` binds a variable: a value's, a description's, or both.
(define binder-delta? (->* (int) bool) (lambda (delta) (or (= delta 1) (= delta 4) (= delta 5))))
;; What the binder at node `t` binds, which the signature says binds a value
;; (δ 1), a description (4) or both, a place (5): refused if it binds what
;; the signature does not say.
(define binder-atms (->* (fails int int) atms)
  (lambda (fail t delta)
    (let* ((d (not (= delta 1)))
           (desc? (tagcase (node-kids t)
                    (k-binder (n e) e)
                    (k-pvar (n) (= (kind-of (node-core t)) 12))
                    (else y (not d))))
           (one (lambda ((e bool))
                  (tagcase (node-kids t) (k-pvar (n) (atm-var n e)) (else y (atm-lit t e))))))
      (begin
        (if (eq? desc? d)
            #u
            (fail-at fail (string-append "the signature says a " (if d "description's" "value's")
                                         " binder is here")
                     (node-syn t)))
        (if (= delta 5) (list (one #t) (one #f)) (list (one d)))))))
(define env-in-rib (->* (fails syn) unit)
  (lambda (fail s) (fail-at fail "a ribcage (`env`) in a rib: write it `(at ℓ)` in a `cage`" s)))
;; The rib node `t` exports, its addresses read at `s`'s place, as the
;; import's are: a form's, its operands' (a definition's); none, a use of
;; a macro that makes definitions, which the template sees none of.
(define exported-rib (->* (fails int syn syn) atms)
  (lambda (fail t ts s)
    (let ((e (extract (node-at (exporter t)) 5)))
      (if (null? e)
          (if (form-node? t)
              (the atms nil)
              (begin (fail-at fail (string-append "the signature says what is here exports a rib, "
                                                  "and it exports none")
                              ts)
                     (the atms nil)))
          (tagcase (extract (car e) 1)
            (bind-rib (es) (rib fail es (extract (car e) 2) s))
            (bind-direct (as) as)
            (else y (begin (fail-at fail (string-append "the signature says what is here exports "
                                                        "a rib, and it exports none")
                                    ts)
                           (the atms nil))))))))
(define levels-of (->* (fails int syn) levels)
  (lambda (fail t s)
    (tagcase (node-kids t)
      (k-pvar (n) (list (lv-cage n)))
      (else y
        (let ((e (extract (node-at (exporter t)) 5)))
          (cond ((not (null? e)) (evaluate fail (extract (car e) 1) (extract (car e) 2) s))
                ((form-node? t) (the levels nil))
                (else
                 (begin (fail-at fail (string-append "the signature says what is here exports a "
                                                     "ribcage, and it exports none")
                                 (node-syn t))
                        (the levels nil)))))))))
;; The node whose export is what node `t` exports: a form's operands' (a
;; definition's), else its own.
(define exporter (->* (int) int)
  (lambda (t) (tagcase (node-kids t) (k-form (x) x) (else y t))))
(define form-node? (->* (int) bool)
  (lambda (t) (tagcase (node-kids t) (k-form (x) #t) (else y #f))))
;; The node at `a` from `root`.
(define nav (->* (fails int addr syn) int)
  (lambda (fail root a s)
    (if (null? a)
        root
        (tagcase (node-kids root)
          (k-pair (x y) (nav fail (if (car a) x y) (cdr a) s))
          (k-pvar (n)
            (begin (fail-at fail (string-append "an address into pattern variable `"
                                                (symbol->string n) "`: the prototype names a part "
                                                "only where the pattern names it")
                            s)
                   root))
          (else y (begin (fail-at fail "an address to no part" s) root))))))

;; Pattern variable `n`, of `info`, placed in the template where type
;; `want` is, in environment `env`: Herman's rules. `ps`, the pattern's.
(define placed (->* (fails symbol pinfo sty levels syn pvars) unit)
  (lambda (fail n info want env s ps)
    (let* ((name (symbol->string n)) (have (extract info 1)) (kh (kind-of have))
           (kw (kind-of (unfold want)))
           (said (lambda ((why string)) (fail-at fail (string-append "`" name "` " why) s)))
           (simple? (lambda ((k int)) (simple-kind? k))))
      (cond
        ((or (and (= kh 1) (= kw 1)) (and (= kh 12) (= kw 12))) #u)
        ;; A pattern's binder referred to, a value's or a description's: in
        ;; its scope, and where no other of the pattern's binders of its
        ;; namespace may shadow it (the shadow restriction).
        ((and (or (= kh 1) (= kh 12)) (or (= kw 0) (= kw 2) (and (= kh 12) (= kw 4))))
         (let* ((d (= kw 4)) (i (rib-binding n d env 0)))
           (cond ((< i 0) (said "is referred to where the template does not bind it"))
                 ((shadowing? env i ps d)
                  (said (string-append "is referred to where another of the pattern's binders "
                                       "may shadow it (Herman's shadow restriction): a use "
                                       "giving both one name would change what it refers to")))
                 (else #u))))
        ;; An untyped part where a lambda is wanted: it promises nothing, and
        ;; its uses' expansions are checked; a typed hole says it is a lambda
        ;; (`typed-macros.md`, "Typed holes": two tiers).
        ((and (= kh 0) (= kw 10) (not (null? (extract info 4))))
         (said (string-append "is placed where a lambda is wanted: a typed hole there is a "
                              "lambda, `(lambda #:type T)`")))
        ((or (and (= kh 3) (= kw 3)) (and (= kh 4) (= kw 4)) (and (= kh 5) (= kw 5))) #u)
        (else
         (let ((fits (cond ((and (= kh 0) (= kw 0)) #t)
                           ((and (= kh 10) (or (= kw 10) (= kw 0))) #t)
                           ((and (= kh 0) (= kw 10)) #t)
                           ((and (= kh 2) (or (= kw 0) (= kw 2))) #t)
                           ((or (simple? kh) (simple? kw)) #f)
                           (else (sub? have want nil)))))
           (cond ((not fits)
                  (said "is placed where its syntax type is not one the form takes there"))
                 ((not (levels=? (normal env) (normal (extract info 2))))
                  (said "is placed in the scope of other bindings than its signature says it is"))
                 (else #u))))))))
;; The first level of `env`, from `i`, whose rib binds pattern variable
;; `n`; -1 if none.
(define rib-binding (->* (symbol bool levels int) int)
  (lambda (n d env i)
    (cond ((null? env) -1)
          ((tagcase (car env) (lv-rib (as) (atm-in? (atm-var n d) as)) (else y #f)) i)
          (else (rib-binding n d (cdr env) (+ i 1))))))
;; Whether a level of `env` before the `i`th is a ribcage, or a rib with one
;; of the pattern's binders of a description's namespace if `d`, else a
;; value's: a value's binder never shadows a description's.
(define shadowing? (->* (levels int pvars bool) bool)
  (lambda (env i ps d)
    (and (> i 0)
         (or (tagcase (car env)
               (lv-cage (n) #t)
               (lv-rib (as) (any-pattern-atom? as ps d)))
             (shadowing? (cdr env) (- i 1) ps d)))))
(define any-pattern-atom? (->* (atms pvars bool) bool)
  (lambda (as ps d)
    (and (not (null? as))
         (or (tagcase (car as)
               (atm-lit (t e) #f)
               (atm-var (m e) (eq? e d))
               (else y #t))
             (any-pattern-atom? (cdr as) ps d)))))
(define atm=? (->* (atm atm) bool)
  (lambda (a b)
    (tagcase a
      (atm-var (n d) (tagcase b (atm-var (m e) (and (symbol=? n m) (eq? d e))) (else y #f)))
      (atm-rib-of (n) (tagcase b (atm-rib-of (m) (symbol=? n m)) (else y #f)))
      (atm-lit (t d) (tagcase b (atm-lit (u e) (and (= t u) (eq? d e))) (else y #f))))))
(define atm-in? (->* (atm atms) bool)
  (lambda (a as) (and (not (null? as)) (or (atm=? a (car as)) (atm-in? a (cdr as))))))
;; An environment as compared: the template's own binders left out (made
;; fresh, they bind nothing a use wrote), empty ribs gone.
(define normal (->* (levels) levels)
  (lambda (env)
    (if (null? env)
        nil
        (tagcase (car env)
          (lv-rib (as)
            (let ((kept (pattern-atoms as)))
              (if (null? kept) (normal (cdr env)) (cons (lv-rib kept) (normal (cdr env))))))
          (lv-cage (n) (cons (car env) (normal (cdr env))))))))
(define pattern-atoms (->* (atms) atms)
  (lambda (as)
    (cond ((null? as) nil)
          ((tagcase (car as) (atm-lit (t d) #t) (else y #f)) (pattern-atoms (cdr as)))
          (else (cons (car as) (pattern-atoms (cdr as)))))))
;; Whether two environments are the same, each rib's atoms in any order.
(define levels=? (->* (levels levels) bool)
  (lambda (xs ys)
    (if (null? xs)
        (null? ys)
        (and (not (null? ys))
             (tagcase (car xs)
               (lv-rib (as) (tagcase (car ys) (lv-rib (bs) (same-atoms? as bs)) (else y #f)))
               (lv-cage (n) (tagcase (car ys) (lv-cage (m) (symbol=? n m)) (else y #f))))
             (levels=? (cdr xs) (cdr ys))))))
(define same-atoms? (->* (atms atms) bool)
  (lambda (as bs)
    (if (null? as)
        (null? bs)
        (let ((rest (without (car as) bs)))
          (and (= (len-atms rest) (- (len-atms bs) 1)) (same-atoms? (cdr as) rest))))))
(define without (->* (atm atms) atms)
  (lambda (a bs)
    (cond ((null? bs) nil)
          ((atm=? a (car bs)) (cdr bs))
          (else (cons (car bs) (without a (cdr bs)))))))
(define len-atms (->* (atms) int)
  (lambda (as) (if (null? as) 0 (+ 1 (len-atms (cdr as))))))

;;; ------------------------------------------------------------ repeating

;; The pattern variables in `x` under more ellipses than `level`, in the
;; pattern's order.
(define drivers-of (->* (pvars syn int) names)
  (lambda (ps x level)
    (cond ((null? ps) nil)
          ((and (> (extract (extract (car ps) 2) 5) level)
                (name-in? (extract (car ps) 1) (pattern-names x)))
           (cons (extract (car ps) 1) (drivers-of (cdr ps) x level)))
          (else (drivers-of (cdr ps) x level)))))
;; The renamings in `acts` at paths under `p`, of binders under more
;; ellipses than `level`: each with whether it is at the binder itself.
(define renames-under (->* (actions addr int) (listof (tupleof addr bool) acyclic))
  (lambda (acts p level)
    (if (null? acts)
        nil
        (let ((rest (renames-under (cdr acts) p level)) (at (extract (car acts) 1)))
          (tagcase (extract (car acts) 2)
            (act-rename (b d)
              (if (and (> d level) (addr-under? at p))
                  (cons (tuple b ((with types-module addr=?) at b)) rest)
                  rest))
            (else y rest))))))
