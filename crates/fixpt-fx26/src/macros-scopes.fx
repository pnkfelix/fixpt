;;; Typed hygienic macros, in FX-26: what binds what in syntax aligned with
;;; syntax types (`macros-align.fx`'s nodes), walked by Herman's rules, and
;;; a pattern variable placed in a template checked against its signature
;;; (`macros.rs`'s `walk`, `eval`, `levels_of` and `placed`). Part of the
;;; expander: loaded by `macros-match.fx`, and loading `macros-align.fx`,
;;; so that `macros.fx` takes one instance of each through it.

(module-parameters ((rs region) (re region) (rm region) (rc region) (rp region)))
(define align-module ((proj (load-module "fx26:macros-align.fx") rs re rm rc rp)))
(define types-module (with align-module types-module))
(define parser-module (with types-module parser-module))
(define reader-types (with parser-module reader-types))
(import reader-types (type syn))
(import types-module fail-at kind-of unfold simple-kind? sub? atm-var atm-rib-of atm-lit
        bind-rib bind-cage bind-direct bind-earlier bind-shape ring-rib ring-at ring-shape
        (type fails addr entries rings bind sty atm atms))
(import align-module node-export node-imports node-syn node-core node-kids node-many? repeated?
        seq-depths
        cage-seq? program-walk lv-rib lv-cage lv-earlier lv-shape k-pair k-pvar k-binder k-ref
        k-form k-desc k-seq
        env-within binder-name
        (type level levels found rooted pinfo pvars env))

;;; ------------------------------------------------------------ binding

;; The tree under `at`, walked with environment `env`, under `depth0`
;; ellipses: what it finds, in the order a walk finds them; each node an
;; ellipsis follows noted in `seq-depths`.
(define walk (->* (fails int env bool int) found)
  (lambda (fail at env many0 depth0)
    (let* ((many (or many0 (node-many? at)))
           (depth (if (repeated? at) (+ depth0 1) depth0))
           (noted (if (repeated? at) (set seq-depths (cons (tuple at depth) (get seq-depths))) #u))
           (env2 (imported fail (node-imports at) env (node-syn at))))
      (tagcase (node-kids at)
        (k-pair (x y) (append (walk fail x env2 many depth) (walk fail y env2 many depth)))
        (k-form (x) (walk fail x env2 many depth))
        ;; An element of a ribcage's list, in the scope of what the
        ;; repetitions before it bound.
        (k-seq (x) (walk fail x (if (cage-seq? at) (earlier fail x env2) env2) many depth))
        (k-desc (xs) (walk-each fail xs env2 many depth))
        (k-pvar (n) (the found (list (tuple at env2 many depth))))
        (k-binder (n d) (the found (list (tuple at env2 many depth))))
        (k-ref (n d free) (the found (list (tuple at env2 many depth))))
        (else y (the found nil))))))
(define walk-each (->* (fails (listof int acyclic) env bool int) found)
  (lambda (fail xs env many depth)
    (if (null? xs)
        nil
        (let ((first (walk fail (car xs) env many depth)))
          (append first (walk-each fail (cdr xs) env many depth))))))
;; `env` with what the repetitions of element `x` before each bound, which
;; its binders' names cannot tell from its own.
(define earlier (->* (fails int env) env)
  (lambda (fail x env)
    (let ((ls (levels-of fail x (node-syn x))))
      (env-within env (cons (lv-earlier (earlier-atoms ls)) (earlier-cages ls)) binder-name))))
(define earlier-atoms (->* (levels) atms)
  (lambda (ls)
    (if (null? ls)
        nil
        (append (tagcase (car ls)
                  (lv-rib (as) as) (lv-earlier (as) as) (lv-cage (n) nil) (lv-shape (m) nil))
                (earlier-atoms (cdr ls))))))
(define earlier-cages (->* (levels) levels)
  (lambda (ls)
    (cond ((null? ls) nil)
          ((tagcase (car ls) (lv-cage (n) #t) (lv-shape (m) #t) (else y #f))
           (cons (car ls) (earlier-cages (cdr ls))))
          (else (earlier-cages (cdr ls))))))
;; `env` with what each import binds before it, the last import innermost.
(define imported (->* (fails rooted env syn) env)
  (lambda (fail is env s)
    (if (null? is)
        env
        (imported fail (cdr is)
                  (env-within env
                              (own-first
                                (evaluate fail (extract (car is) 1) (extract (car is) 2) s))
                              binder-name)
                  s))))
;; In a program's walk, what one import binds of its own before the modules
;; it opens: a module's items before what its `include`s give, as the
;; checkers read them (`macros/shapes.rs`'s `segments_of`).
(define own-first (->* (levels) levels)
  (lambda (ls)
    (if (get program-walk)
        (append (levels-shaped #f ls) (levels-shaped #t ls))
        ls)))
(define levels-shaped (->* (bool levels) levels)
  (lambda (shaped ls)
    (cond ((null? ls) nil)
          ((eq? shaped (tagcase (car ls) (lv-shape (m) #t) (else y #f)))
           (cons (car ls) (levels-shaped shaped (cdr ls))))
          (else (levels-shaped shaped (cdr ls))))))
;; What `b` binds, its addresses from `root`: levels, innermost first.
(define evaluate (->* (fails bind int syn) levels)
  (lambda (fail b root s)
    (tagcase b
      (bind-rib (es) (list (lv-rib (rib fail es root s))))
      (bind-cage (rings) (cage fail rings root s))
      (bind-direct (as) (list (lv-rib as)))
      (bind-earlier (as) (list (lv-earlier as)))
      (bind-shape (a) (list (lv-shape (nav fail root a s)))))))
(define cage (->* (fails rings int syn) levels)
  (lambda (fail rings root s)
    (if (null? rings)
        nil
        (append (tagcase (car rings)
                  (ring-rib (es) (the levels (list (lv-rib (rib fail es root s)))))
                  (ring-at (a) (levels-of fail (nav fail root a s) s))
                  (ring-shape (a) (the levels (list (lv-shape (nav fail root a s))))))
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
                  (tagcase (node-kids t) (k-pvar (n) (atm-var n e 0)) (else y (atm-lit t e))))))
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
    (let ((e (node-export (exporter t))))
      (if (null? e)
          (if (form-node? t)
              (the atms nil)
              (begin (fail-at fail (string-append "the signature says what is here exports a rib, "
                                                  "and it exports none")
                              ts)
                     (the atms nil)))
          (tagcase (extract (car e) 1)
            (bind-rib (es) (gathered t (rib fail es (extract (car e) 2) s)))
            (bind-direct (as) as)
            (else y (begin (fail-at fail (string-append "the signature says what is here exports "
                                                        "a rib, and it exports none")
                                    ts)
                           (the atms nil))))))))
(define levels-of (->* (fails int syn) levels)
  (lambda (fail t s)
    (tagcase (node-kids t)
      (k-pvar (n) (list (lv-cage n)))
      ;; A ribcage's list by ellipsis: what each element exports.
      (k-seq (x)
        (gathered-levels t (if (and (cage-seq? t) (null? (node-export t)))
                               (levels-of fail x s)
                               (exported-levels fail t s))))
      (else y (exported-levels fail t s)))))
(define exported-levels (->* (fails int syn) levels)
  (lambda (fail t s)
    (let ((e (node-export (exporter t))))
      (cond ((not (null? e)) (evaluate fail (extract (car e) 1) (extract (car e) 2) s))
            ((form-node? t) (the levels nil))
            (else
             (begin (fail-at fail (string-append "the signature says what is here exports a "
                                                 "ribcage, and it exports none")
                             (node-syn t))
                    (the levels nil)))))))
;; Atoms `as` node `t` exports: if `t` is a list by ellipsis, what its
;; elements export, every repetition's (`macros.rs`'s `gathered`).
(define gathered (->* (int atms) atms)
  (lambda (t as)
    (tagcase (node-kids t)
      (k-seq (x)
        (let ((e (node-export t)))
          (if (or (null? e) (= (extract (car e) 2) x)) (gathered-each as) as)))
      (else y as))))
(define gathered-each (->* (atms) atms)
  (lambda (as)
    (if (null? as)
        nil
        (cons (tagcase (car as) (atm-var (n d g) (atm-var n d (+ g 1))) (else y (car as)))
              (gathered-each (cdr as))))))
(define gathered-levels (->* (int levels) levels)
  (lambda (t ls)
    (if (null? ls)
        nil
        (cons (tagcase (car ls)
                (lv-rib (as) (lv-rib (gathered t as)))
                (lv-earlier (as) (lv-earlier (gathered t as)))
                (else y (car ls)))
              (gathered-levels t (cdr ls))))))
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
                 ((tagcase (nth-level env i) (lv-earlier (as) #t) (else y #f))
                  (said repeats-said))
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
        ((or (and (= kh 3) (= kw 3)) (and (= kh 4) (= kw 4)) (and (= kh 5) (= kw 5))
             (and (= kh 13) (= kw 13)))
         #u)
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
          ((tagcase (car env)
             (lv-rib (as) (named-in? n d as))
             (lv-earlier (as) (named-in? n d as))
             (else y #f))
           i)
          (else (rib-binding n d (cdr env) (+ i 1))))))
;; Whether `as` binds pattern variable `n` (a description's if `d`), by its
;; name: a reference finds its binder whichever repetitions are gathered.
(define named-in? (->* (symbol bool atms) bool)
  (lambda (n d as)
    (and (not (null? as))
         (or (tagcase (car as) (atm-var (m e g) (and (symbol=? n m) (eq? d e))) (else y #f))
             (named-in? n d (cdr as))))))
(define nth-level (->* (levels int) level)
  (lambda (env i) (if (= i 0) (car env) (nth-level (cdr env) (- i 1)))))
;; Why a name bound by a repeated part (an element of a ribcage's list, a
;; parameter named) is refused where that part refers to it.
(define repeats-said string
  (string-append "is bound by the repetitions before this one, which its name does not tell "
                 "apart: a repeated part refers to no binder it repeats in its own scope"))
;; The template's binder of `n` in `env`, innermost first, in a
;; description's namespace if `d`, else a value's: its node, in a list of
;; one; refused, at `s`, if the repetitions before an element bind it.
(define binder-of (->* (fails symbol bool levels syn) (listof int acyclic))
  (lambda (fail n d env s)
    (if (null? env)
        nil
        (tagcase (car env)
          (lv-rib (as)
            (let ((here (lit-binding n d as)))
              (if (null? here) (binder-of fail n d (cdr env) s) here)))
          (lv-earlier (as)
            (if (null? (lit-binding n d as))
                (binder-of fail n d (cdr env) s)
                (begin (fail-at fail (string-append "`" (symbol->string n) "` " repeats-said) s)
                       nil)))
          (else y (binder-of fail n d (cdr env) s))))))
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
;; Whether a level of `env` before the `i`th is a ribcage, or a rib with one
;; of the pattern's binders of a description's namespace if `d`, else a
;; value's: a value's binder never shadows a description's.
(define shadowing? (->* (levels int pvars bool) bool)
  (lambda (env i ps d)
    (and (> i 0)
         (or (tagcase (car env)
               (lv-cage (n) #t)
               (lv-rib (as) (any-pattern-atom? as ps d))
               (lv-earlier (as) (any-pattern-atom? as ps d))
               (lv-shape (m) #f))
             (shadowing? (cdr env) (- i 1) ps d)))))
(define any-pattern-atom? (->* (atms pvars bool) bool)
  (lambda (as ps d)
    (and (not (null? as))
         (or (tagcase (car as)
               (atm-lit (t e) #f)
               (atm-var (m e g) (eq? e d))
               (else y #t))
             (any-pattern-atom? (cdr as) ps d)))))
(define atm=? (->* (atm atm) bool)
  (lambda (a b)
    (tagcase a
      (atm-var (n d g)
        (tagcase b (atm-var (m e h) (and (symbol=? n m) (eq? d e) (= g h))) (else y #f)))
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
          (lv-earlier (as)
            (let ((kept (pattern-atoms as)))
              (if (null? kept) (normal (cdr env)) (cons (lv-earlier kept) (normal (cdr env))))))
          (lv-cage (n) (cons (car env) (normal (cdr env))))
          (lv-shape (m) (normal (cdr env)))))))
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
               (lv-earlier (as)
                 (tagcase (car ys) (lv-earlier (bs) (same-atoms? as bs)) (else y #f)))
               (lv-cage (n) (tagcase (car ys) (lv-cage (m) (symbol=? n m)) (else y #f)))
               (lv-shape (n) (tagcase (car ys) (lv-shape (m) (= n m)) (else y #f))))
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
