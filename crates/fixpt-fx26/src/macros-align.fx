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
        fits? sub? kind-of simple-kind? lambda-shaped? proper? kernel-sigs bind-rib bind-cage
        ring-rib ring-at s-expr s-bvar s-id
        s-data s-type s-label s-nil s-literal s-pair s-import s-export s-mu s-many s-union s-typed
        mu-body addr=?
        (type fails addr entries ring rings bind sty stys named hole))

;;; ------------------------------------------------------------ macros

;; What becomes of one of a template's parts where it is transcribed
;; (`macros.rs`'s `Action`): a name made fresh, one for the binder at a
;; path and each reference to it; a free name the top level's, `(with
;; #%toplevel n)`; a type the template writes read in the top level's; a
;; file's macro's free name the file's own, `(with m n)`, or standard,
;; `(with #%fx n)`; its type the same, by `select`; a use of another of the
;; file's macros, by the name the importer has it by.
(define-datatype action
  (act-rename addr) (act-toplevel) (act-toplevel-type) (act-standard) (act-module symbol)
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
;; A macro defined: its signature, its clauses, and the binders of its
;; signature's `(poly (binder …) σ)`, if it has one.
(define-type macro (tupleof sty clauses syns-a))
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

;; What a file's macros are defined in (`macros.rs`'s `FileScope`): the
;; hidden global every load of the file is; the values and the types its
;; module shows; each of its macros' names, and the name the importer has
;; it by; and the standard names. None for a program's own.
(define-type scope
  (tupleof symbol names names (listof (tupleof symbol symbol) acyclic) names))
(define-type scopes (listof scope acyclic))

;;; ------------------------------------------------------------ nodes

;; What is in a node: a pair's two; nothing; a pattern variable (in a
;; pattern, or placed in a template); a template's binder; a name in a
;; template referred to; a form in a template, its operands (or, an
;; application's, itself); anything else.
(define-datatype kids
  (k-pair int int) (k-nil) (k-pvar symbol) (k-binder symbol) (k-ref symbol) (k-form int)
  (k-other))
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
(define nodes-reset! (->* () unit) (lambda () (set nnodes 0)))

;;; ------------------------------------------------------------ aligning

;; A pattern variable: its type, its environment as the signature declares
;; it, whether it may be placed any number of times, and its typed hole, if
;; the signature types it.
(define-type pinfo (tupleof sty levels bool holes))
(define-type pvars (listof (tupleof symbol pinfo) acyclic))
(define pvar-of (->* (symbol pvars) (listof pinfo acyclic))
  (lambda (n ps)
    (cond ((null? ps) nil)
          ((symbol=? n (extract (car ps) 1)) (list (extract (car ps) 2)))
          (else (pvar-of n (cdr ps))))))
(define pvar? (->* (symbol pvars) bool) (lambda (n ps) (not (null? (pvar-of n ps)))))

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
      (if (and (syn-symbol? s)
               (or (and (= mode 0) (not (= (kind-of (unfold t)) 7))
                        (not (string=? (syn-name s) "_")))
                   (and (= mode 1) (pvar? (syn-symbol s) ps))))
          (with-kids at (k-pvar (syn-symbol s)))
          (fill-shape fail mode ps at t s root)))))
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
        (s-bvar ()
          (cond ((and (syn-symbol? s) (macro? (syn-symbol s)))
                 (said (string-append "`" (syn-name s) "` is a macro's name, which is not bound")))
                ((and (syn-symbol? s) (not (reserved-syn? s)))
                 (if (= mode 1) (with-kids at (k-binder (syn-symbol s))) #u))
                (else (said (string-append shown " is not a name that may be bound")))))
        (s-id ()
          (if (syn-symbol? s)
              (if (= mode 1) (with-kids at (k-ref (syn-symbol s))) #u)
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
                 (form fail ps at s))
                ((and (not (= mode 1)) (lambda-shaped? s)) #u)
                (else (said (string-append shown " is not a lambda, as this part must be")))))
        (s-expr ()
          (cond ((reserved-syn? s)
                 (said (string-append "`" (syn-name s) "` is a form's name, not an expression")))
                ;; `#u`, unit: a literal, which the parsers read as a name.
                ((and (syn-symbol? s) (string=? (syn-name s) "#u")) #u)
                ((and (syn-symbol? s) (= mode 1)) (with-kids at (k-ref (syn-symbol s))))
                ((and (not (syn-nil? s)) (not (null? (split s))) (= mode 1)) (form fail ps at s))
                ((syn-nil? s) (said "`()` is not an expression"))
                (else #u)))
        ;; `data` and `type`.
        (else z
          (let ((inside (pvar-inside s ps)))
            (if (and (= mode 1) (not (null? inside)))
                (said (string-append "pattern variable `" (symbol->string (car inside))
                                     "` inside a quoted datum or a type: only a whole one is "
                                     "placed"))
                #u)))))))
;; Those of `ms` that `s` fits.
(define fitting (->* (stys syn int pvars) stys)
  (lambda (ms s mode ps)
    (cond ((null? ms) nil)
          ((fits? (car ms) s mode (lambda ((n symbol)) (pvar? n ps)))
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
;; application, aligned with its signature.
(define form (->* (fails pvars int syn) unit)
  (lambda (fail ps at s)
    (let* ((parts (split s)) (hd (car parts))
           (head (if (and (syn-symbol? hd) (not (pvar? (syn-symbol hd) ps))) (syn-name hd) ""))
           (kernel (kernel-sigs fail)))
      (cond
        ((string=? head "with")
         (if (standard-with? s)
             #u
             (fail-at fail (string-append "a template's `with` is `(with #%fx name)` or `(with "
                                          "#%toplevel name)` (one opening a module waits for "
                                          "scopes of a module's names)")
                      s)))
        ((and (not (string=? head "")) (macro? (syn-symbol hd)))
         (operands fail ps at (extract (car (macro-of (syn-symbol hd) (get defined))) 1)
                   (nth parts 1)))
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

;;; ------------------------------------------------------------ binding

;; What an environment is made of: a pattern variable bound (`bvar`), the
;; rib or ribcage a pattern variable exports, a template's own binder (its
;; node).
(define-datatype atm (atm-var symbol) (atm-rib-of symbol) (atm-lit int))
(define-type atms (listof atm acyclic))
;; One level of an environment: a rib, or a pattern variable's ribcage.
(define-datatype level (lv-rib atms) (lv-cage symbol))
(define-type levels (listof level acyclic))
;; Each pattern variable, template binder and name referred to, by node,
;; with its environment (innermost first) and whether it is in a `many`
;; part.
(define-type found (listof (tupleof int levels bool) acyclic))

;; The tree under `at`, walked with environment `env`: what it finds, in
;; the order a walk finds them, before `out`.
(define walk (->* (fails int levels bool) found)
  (lambda (fail at env many0)
    (let* ((many (or many0 (node-many? at)))
           (env2 (imported fail (extract (node-at at) 4) env (node-syn at))))
      (tagcase (node-kids at)
        (k-pair (x y) (append (walk fail x env2 many) (walk fail y env2 many)))
        (k-form (x) (walk fail x env2 many))
        (k-pvar (n) (the found (list (tuple at env2 many))))
        (k-binder (n) (the found (list (tuple at env2 many))))
        (k-ref (n) (the found (list (tuple at env2 many))))
        (else y (the found nil))))))
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
      (bind-cage (rings) (cage fail rings root s)))))
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
              (cond ((= delta 1) (cons (atm-var n) rest))
                    ((= delta 2) (cons (atm-rib-of n) rest))
                    ((= delta 3) (begin (env-in-rib fail ts) rest))
                    (else rest)))
            (k-binder (n)
              (cond ((= delta 1) (cons (atm-lit t) rest))
                    ((= delta 2) (append (exported-rib fail t ts s) rest))
                    ((= delta 3) (begin (env-in-rib fail ts) rest))
                    (else rest)))
            (else y
              (cond ((= delta 1)
                     (begin (fail-at fail "the signature says a binder is here" ts) rest))
                    ((= delta 2) (append (exported-rib fail t ts s) rest))
                    ((= delta 3) (begin (env-in-rib fail ts) rest))
                    (else rest))))))))
(define env-in-rib (->* (fails syn) unit)
  (lambda (fail s) (fail-at fail "a ribcage (`env`) in a rib: write it `(at ℓ)` in a `cage`" s)))
;; The rib node `t` exports, its addresses read at `s`'s place, as the
;; import's are.
(define exported-rib (->* (fails int syn syn) atms)
  (lambda (fail t ts s)
    (let ((e (extract (node-at t) 5)))
      (if (null? e)
          (begin (fail-at fail (string-append "the signature says what is here exports a rib, and "
                                              "it exports none")
                          ts)
                 (the atms nil))
          (tagcase (extract (car e) 1)
            (bind-rib (es) (rib fail es (extract (car e) 2) s))
            (else y (begin (fail-at fail (string-append "the signature says what is here exports "
                                                        "a rib, and it exports none")
                                    ts)
                           (the atms nil))))))))
(define levels-of (->* (fails int syn) levels)
  (lambda (fail t s)
    (tagcase (node-kids t)
      (k-pvar (n) (list (lv-cage n)))
      (else y
        (let ((e (extract (node-at t) 5)))
          (if (null? e)
              (begin (fail-at fail (string-append "the signature says what is here exports a "
                                                  "ribcage, and it exports none")
                              (node-syn t))
                     (the levels nil))
              (evaluate fail (extract (car e) 1) (extract (car e) 2) s)))))))
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
;; `want` is, in environment `env`: Herman's rules.
(define placed (->* (fails symbol pinfo sty levels syn) unit)
  (lambda (fail n info want env s)
    (let* ((name (symbol->string n)) (have (extract info 1)) (kh (kind-of have))
           (kw (kind-of (unfold want)))
           (said (lambda ((why string)) (fail-at fail (string-append "`" name "` " why) s)))
           (simple? (lambda ((k int)) (simple-kind? k))))
      (cond
        ((and (= kh 1) (= kw 1)) #u)
        ;; A pattern's binder referred to: in its scope, and where no other of
        ;; the pattern's binders may shadow it (the shadow restriction).
        ((and (= kh 1) (or (= kw 0) (= kw 2)))
         (let ((i (rib-binding n env 0)))
           (cond ((< i 0) (said "is referred to where the template does not bind it"))
                 ((shadowing? env i)
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
(define rib-binding (->* (symbol levels int) int)
  (lambda (n env i)
    (cond ((null? env) -1)
          ((tagcase (car env) (lv-rib (as) (atm-in? (atm-var n) as)) (else y #f)) i)
          (else (rib-binding n (cdr env) (+ i 1))))))
;; Whether a level of `env` before the `i`th is a ribcage, or a rib with one
;; of the pattern's binders in it.
(define shadowing? (->* (levels int) bool)
  (lambda (env i)
    (and (> i 0)
         (or (tagcase (car env)
               (lv-cage (n) #t)
               (lv-rib (as) (any-pattern-atom? as)))
             (shadowing? (cdr env) (- i 1))))))
(define any-pattern-atom? (->* (atms) bool)
  (lambda (as)
    (and (not (null? as))
         (or (tagcase (car as) (atm-lit (t) #f) (else y #t)) (any-pattern-atom? (cdr as))))))
(define atm=? (->* (atm atm) bool)
  (lambda (a b)
    (tagcase a
      (atm-var (n) (tagcase b (atm-var (m) (symbol=? n m)) (else y #f)))
      (atm-rib-of (n) (tagcase b (atm-rib-of (m) (symbol=? n m)) (else y #f)))
      (atm-lit (t) (tagcase b (atm-lit (u) (= t u)) (else y #f))))))
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
          ((tagcase (car as) (atm-lit (t) #t) (else y #f)) (pattern-atoms (cdr as)))
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
