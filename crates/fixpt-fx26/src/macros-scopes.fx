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
(import reader-types atom lst dotted vec (type syn))
(import parser-module syn-start syn-end syn-symbol? syn-symbol syn-expansion syn-name syn-datums
        syn->datum (type syns-a names))
(import types-module fail-at kind-of unfold simple-kind? sub? atm-var atm-rib-of atm-lit show-syn
        split syn-nil? name-in? addr=?
        bind-rib bind-cage bind-direct bind-earlier bind-shape ring-rib ring-at ring-shape
        (type fails addr entries rings bind sty atm atms))
(import align-module node-export node-imports node-syn node-core node-kids node-many? repeated?
        seq-depths
        cage-seq? program-walk lv-rib lv-cage lv-earlier lv-shape k-pair k-pvar k-binder k-ref
        k-form k-desc k-seq
        env-within binder-name align nodes-reset! nnodes heads pending pending-node? head-read
        env-empty env-levels env-lookup unplaced node-path macro? makes-desc? scoped-on scoped-apps
        scoped-whole addr-in?
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
           (env2 (imported fail (node-imports at) env (node-syn at)))
           ;; A pending list's scope, for its head (`Node::head`).
           (head (if (and (not (null? (get pending))) (pending-node? at))
                     (the found (list (tuple at env2 many depth)))
                     nil)))
      (append head (tagcase (node-kids at)
        (k-pair (x y) (append (walk fail x env2 many depth) (walk fail y env2 many depth)))
        (k-form (x) (walk fail x env2 many depth))
        ;; An element of a ribcage's list, in the scope of what the
        ;; repetitions before it bound.
        (k-seq (x) (walk fail x (if (cage-seq? at) (earlier fail x env2) env2) many depth))
        (k-desc (xs) (walk-each fail xs env2 many depth))
        (k-pvar (n) (the found (list (tuple at env2 many depth))))
        (k-binder (n d) (the found (list (tuple at env2 many depth))))
        (k-ref (n d free) (the found (list (tuple at env2 many depth))))
        (else y (the found nil)))))))
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
(define binder-delta? (->* (int) bool)
  (lambda (delta) (or (= delta 1) (= delta 4) (= delta 5) (>= delta 100))))
;; What the binder at node `t` binds, which the signature says binds a value
;; (δ 1), a description (4) or both, a place (5): refused if it binds what
;; the signature does not say.
(define binder-atms (->* (fails int int) atms)
  (lambda (fail t delta)
    (let* ((d (and (not (= delta 1)) (< delta 100)))
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
         ;; In a macro the template defines, whose own check is the defined
         ;; macro's, where it is defined.
         (let ((fits (cond ((= kw 16) #t)
                           ((and (= kh 0) (= kw 0)) #t)
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

;;; ------------------------------------------------------------ heads read by scope

;; Template `template`, of type `made`, aligned and walked, each pending list
;; read by its scope, to a fixed point (`typed-macros.md`, "Decided: a
;; template's heads read by their scope, to a fixed point"; `clause`'s): its
;; root, what the walk found, and each pending list's reading (`heads-read`).
;; Each macro reading kept (`heads`); one an application may become a macro
;; in a later round, never the other way: refused.
(define-type head-reading (tupleof int (listof int acyclic) (listof int acyclic)))
(define-type head-readings (listof head-reading acyclic))
(define aligned-heads (->* (fails pvars sty syn) (tupleof int found head-readings))
  (lambda (fail ps made template)
    (let* ((root (begin (nodes-reset!) (align fail 1 ps made template -1 nil)))
           (found (walk fail root env-empty #f 0))
           (read (if (null? (get pending)) (the head-readings nil) (heads-read fail found)))
           (new (new-heads fail read)))
      (if (null? new)
          (tuple root found read)
          (begin (set heads (append (get heads) new)) (aligned-heads fail ps made template))))))
;; The macro readings of `rs` not yet kept, each by its list's place; a
;; reading kept that is now another, refused.
(define new-heads (->* (fails head-readings) (listof (tupleof int int int) acyclic))
  (lambda (fail rs)
    (if (null? rs)
        nil
        (let* ((s (node-syn (extract (car rs) 1))) (was (head-read s)) (now (extract (car rs) 2))
               (said (lambda ((r (listof int acyclic)))
                       (if (null? r)
                           "an application"
                           "a use of the macro a use before it defines")))
               (rest (new-heads fail (cdr rs))))
          (cond ((and (null? was) (null? now)) rest)
                ((null? was) (cons (tuple (syn-start s) (syn-end s) (car now)) rest))
                ((and (not (null? now)) (= (car was) (car now))) rest)
                (else
                 (begin (fail-at fail (string-append "this template's scopes have no one reading: `"
                                                     (show-syn s) "`, headed by `"
                                                     (symbol->string (syn-symbol (car (split s))))
                                                     "`, is read as " (said was) " and then as "
                                                     (said now))
                                 s)
                        rest)))))))
;; How each pending list is read by the scopes the walk found, `fs`
;; (`Aligner::heads_read`), the first found first: a use of a macro if its
;; head's innermost binder is what a `(macro σ made)` entry binds, a pattern
;; variable or a template's binder at that part of a use (its δ, in a list
;; of one); else an application (none). Each with its node, and its
;; binder, if a template's, in a list of one.
(define heads-read (->* (fails found) head-readings)
  (lambda (fail fs)
    (let ((sx (syntax-binders fail 0 (get nnodes) nil)))
      (readings-of fail (reverse (get pending)) fs sx))))
(define-type syntax-binder (tupleof bool symbol int int))
(define syntax-binders (->* (fails int int (listof syntax-binder acyclic))
                            (listof syntax-binder acyclic))
  (lambda (fail i n out)
    (if (= i n)
        out
        (syntax-binders fail (+ i 1) n
          (let ((ex (node-export i)))
            (if (null? ex)
                out
                (tagcase (extract (car ex) 1)
                  (bind-rib (es) (syntax-entries fail es (extract (car ex) 2) (node-syn i) out))
                  (else y out))))))))
(define syntax-entries (->* (fails entries int syn (listof syntax-binder acyclic))
                            (listof syntax-binder acyclic))
  (lambda (fail es root s out)
    (if (null? es)
        out
        (let ((d (extract (car es) 2)) (rest (syntax-entries fail (cdr es) root s out)))
          (if (< d 100)
              rest
              (let ((t (nav fail root (extract (car es) 1) s)))
                (tagcase (node-kids t)
                  (k-pvar (m) (cons (tuple #t m 0 d) rest))
                  (k-binder (m e) (if e rest (cons (tuple #f m t d) rest)))
                  (else y rest))))))))
(define readings-of (->* (fails (listof (tupleof int bool) acyclic) found
                           (listof syntax-binder acyclic))
                       head-readings)
  (lambda (fail ps fs sx)
    (if (null? ps)
        nil
        (let* ((at (extract (car ps) 1))
               (h (syn-symbol (car (split (node-syn at)))))
               (env (found-env at fs))
               (r (head-binder h (env-levels env) sx)))
          (cons (tuple at (extract r 1) (extract r 2)) (readings-of fail (cdr ps) fs sx))))))
(define found-env (->* (int found) env)
  (lambda (at fs)
    (cond ((null? fs) env-empty) ((= at (extract (car fs) 1)) (extract (car fs) 2))
          (else (found-env at (cdr fs))))))
;; Head `h`'s innermost binder in `ls`: its reading, and its node if a
;; template's binder.
(define head-binder (->* (symbol levels (listof syntax-binder acyclic))
                         (tupleof (listof int acyclic) (listof int acyclic)))
  (lambda (h ls sx)
    (if (null? ls)
        (tuple (the (listof int acyclic) nil) (the (listof int acyclic) nil))
        (let ((as (tagcase (car ls) (lv-rib (as) as) (lv-earlier (as) as) (else y nil))))
          (let ((r (atoms-binder h as sx)))
            (if (null? r) (head-binder h (cdr ls) sx) (car r)))))))
(define atoms-binder (->* (symbol atms (listof syntax-binder acyclic))
                          (listof (tupleof (listof int acyclic) (listof int acyclic)) acyclic))
  (lambda (h as sx)
    (if (null? as)
        nil
        (tagcase (car as)
          (atm-var (m d g)
            (if (and (symbol=? m h) (not d))
                (list (tuple (syntax-of-pvar h sx) (the (listof int acyclic) nil)))
                (atoms-binder h (cdr as) sx)))
          (atm-lit (b d)
            (tagcase (node-kids b)
              (k-binder (m e)
                (if (and (symbol=? m h) (not d))
                    (list (tuple (syntax-of-node b sx) (list b)))
                    (atoms-binder h (cdr as) sx)))
              (else y (atoms-binder h (cdr as) sx))))
          (else y (atoms-binder h (cdr as) sx))))))
(define syntax-of-pvar (->* (symbol (listof syntax-binder acyclic)) (listof int acyclic))
  (lambda (n sx)
    (cond ((null? sx) nil)
          ((and (extract (car sx) 1) (symbol=? n (extract (car sx) 2))) (list (extract (car sx) 4)))
          (else (syntax-of-pvar n (cdr sx))))))
(define syntax-of-node (->* (int (listof syntax-binder acyclic)) (listof int acyclic))
  (lambda (b sx)
    (cond ((null? sx) nil)
          ((and (not (extract (car sx) 1)) (= b (extract (car sx) 3))) (list (extract (car sx) 4)))
          (else (syntax-of-node b (cdr sx))))))

;;; ------------------------------------------------------------ a program read by its scopes

;; Program form `s`, of syntax type `core`, aligned and walked, each list a
;; macro's name heads read by its scope (`macros.rs`'s `Aligner::program`,
;; `TODO.md` §295): an application where the program wrote its head (a
;; template's is its macro, by hygiene), it makes no description, and a
;; binder around it binds the name, or `bound` has it (the macros' names
;; bound around `s`); else a use, whole if `whole` (where a form is
;; expanded), else by its signature. Read to a fixed point: each list read
;; otherwise than it is now, with none such around it, read anew, as what
;; binds a head is read by the lists around it alone; so each round
;; settles one for good, and it ends. Its root, what the walk found, and
;; each such list's node, whether it is read an application, and its
;; environment.
(define-type heads-read (listof (tupleof int bool env) acyclic))
(define program-scoped (->* (fails sty syn bool names) (tupleof int found heads-read))
  (lambda (fail core s whole bound)
    (begin (set scoped-apps nil) (set scoped-whole whole) (program-scoped-from fail core s bound))))
(define program-scoped-from (->* (fails sty syn names) (tupleof int found heads-read))
  (lambda (fail core s bound)
    (let* ((root (begin (nodes-reset!) (set unplaced nil) (set program-walk #t) (set scoped-on #t)
                        (align fail 3 (the pvars nil) core s -1 nil)))
           (found (walk fail root env-empty #f 0))
           (read (begin (set program-walk #f) (set scoped-on #f) (heads-bound found bound nil)))
           (changed (heads-changed read nil)))
      (if (null? changed)
          (tuple root found read)
          (begin (set scoped-apps (apps-toggled changed changed (get scoped-apps)))
                 (program-scoped-from fail core s bound))))))
;; Each pending list the walk found, `fs`: its node, whether its head is
;; bound around it, and its environment.
(define heads-bound (->* (found names heads-read) heads-read)
  (lambda (fs bound out)
    (if (null? fs)
        out
        (heads-bound (cdr fs) bound
                     (let ((at (extract (car fs) 1)) (env (extract (car fs) 2)))
                       (if (pending-node? at)
                           (cons (tuple at (head-bound? at env bound) env) out)
                           out))))))
(define head-bound? (->* (int env names) bool)
  (lambda (at env bound)
    (let* ((hd (car (split (node-syn at)))) (h (syn-symbol hd)))
      (and (= (syn-expansion hd) 0) (not (makes-desc? h))
           (or (name-in? h bound) (bound-in? h env 0))))))
;; Whether value `n` is bound in `env` from its `from`th group on, past any
;; module's names.
(define bound-in? (->* (symbol env int) bool)
  (lambda (n env from)
    (let ((l (env-lookup env n #f from binder-name)))
      (case (extract l 1) ((0) #t) ((1) (bound-in? n env (extract l 3))) (else #f)))))
;; The paths of the lists of `rs` read otherwise than they are now.
(define heads-changed (->* (heads-read (listof addr acyclic)) (listof addr acyclic))
  (lambda (rs out)
    (cond ((null? rs) out)
          ((eq? (extract (car rs) 2) (addr-in? (node-path (extract (car rs) 1)) (get scoped-apps)))
           (heads-changed (cdr rs) out))
          (else (heads-changed (cdr rs) (cons (node-path (extract (car rs) 1)) out))))))
;; `apps`, each of `ps` around which none of `all` is read anew.
(define apps-toggled
  (->* ((listof addr acyclic) (listof addr acyclic) (listof addr acyclic)) (listof addr acyclic))
  (lambda (ps all apps)
    (cond ((null? ps) apps)
          ((around-any? (car ps) all) (apps-toggled (cdr ps) all apps))
          ((addr-in? (car ps) apps) (apps-toggled (cdr ps) all (addr-without (car ps) apps)))
          (else (apps-toggled (cdr ps) all (cons (car ps) apps))))))
(define around-any? (->* (addr (listof addr acyclic)) bool)
  (lambda (p qs) (and (not (null? qs)) (or (addr-around? (car qs) p) (around-any? p (cdr qs))))))
;; Whether the list at path `q` is around another at `p`: a program walk's
;; paths are kept innermost step first, so `q` ends `p`.
(define addr-around? (->* (addr addr) bool)
  (lambda (q p)
    (let ((d (- (addr-len p) (addr-len q)))) (and (> d 0) (addr=? q (addr-drop p d))))))
(define addr-len (->* (addr) int) (lambda (p) (if (null? p) 0 (+ 1 (addr-len (cdr p))))))
(define addr-drop (->* (addr int) addr)
  (lambda (p k) (if (= k 0) p (addr-drop (cdr p) (- k 1)))))
(define addr-without (->* (addr (listof addr acyclic)) (listof addr acyclic))
  (lambda (p ps)
    (cond ((null? ps) nil)
          ((addr=? p (car ps)) (cdr ps))
          (else (cons (car ps) (addr-without p (cdr ps)))))))

;; The uses of macros in `s`, of type `core`, `bound` the macros' names
;; bound around it, as the walk finds them, each whole (`program-scoped`;
;; `Macros::uses_found`): each by its place, the indices of the items it is
;; in, list by list from `s` (`index-path`), in the order they are written,
;; with the macros' names bound around it that the program wrote in it.
;; And each path, `a::b::c`, where a value or a description is named
;; (`TODO.md` §296); none where a name is bound.
(define-type ixs (listof int acyclic))
;; What is found at a place: a use of a macro, with the macros' names bound
;; around it; or a path, naming a description if `#t`, else a value
;; (`macros.rs`'s `Part`).
(define-datatype part (pt-use names) (pt-path bool))
(define-type uses (listof (tupleof ixs part) acyclic))
(define uses-found (->* (fails sty syn names) uses)
  (lambda (fail core s bound)
    (let ((read (extract (program-scoped fail core s #t bound) 3)))
      (uses-sorted (path-parts fail 0 (get nnodes) (uses-of read bound nil))))))
;; Each path from node `i` to `n`, onto `out`: a reference's; a binder's,
;; refused.
(define path-parts (->* (fails int int uses) uses)
  (lambda (fail i n out)
    (if (>= i n)
        out
        (path-parts fail (+ i 1) n
                    (tagcase (node-kids i)
                      (k-ref (x d free)
                        (if (path-named? (symbol->string x))
                            (cons (tuple (index-path (node-path i)) (pt-path d)) out)
                            out))
                      (k-binder (x d)
                        (if (path-named? (symbol->string x))
                            (begin
                              (fail-at fail (string-append "`" (symbol->string x) "` is a path, "
                                                           "`module::name`, not a name that may "
                                                           "be bound")
                                       (node-syn i))
                              out)
                            out))
                      (else y out))))))
;; Whether `n` is a path, `a::b::c`: a program's, not a name of the
;; expander's own (`%…`).
(define path-named? (->* (string) bool)
  (lambda (n)
    (and (> (string-length n) 0) (not (char=? (string-ref n 0) #\%))
         (>= (string-search n "::" 0) 0))))
;; The part found here, of uses `us` from here: in a list of one.
(define part-here (->* (uses) (listof part acyclic))
  (lambda (us)
    (if (and (not (null? us)) (null? (extract (car us) 1)))
        (list (extract (car us) 2))
        nil)))
(define uses-of (->* (heads-read names uses) uses)
  (lambda (rs bound out)
    (if (null? rs)
        out
        (uses-of (cdr rs) bound
                 (if (extract (car rs) 2)
                     out
                     (let ((at (extract (car rs) 1)))
                       (cons (tuple (index-path (node-path at))
                                    (pt-use (names-bound (macro-names-in (node-syn at) nil)
                                                         (extract (car rs) 3) bound)))
                             out)))))))
;; `bound`, and those of `ns` that `env` binds.
(define names-bound (->* (names env names) names)
  (lambda (ns env bound)
    (cond ((null? ns) bound)
          ((and (not (name-in? (car ns) bound)) (bound-in? (car ns) env 0))
           (cons (car ns) (names-bound (cdr ns) env bound)))
          (else (names-bound (cdr ns) env bound)))))
;; The macros' names the program wrote in `s`, onto `out`, each once.
(define macro-names-in (->* (syn names) names)
  (lambda (s out)
    (tagcase s
      (lst (items d a b x) (macro-names-each items out))
      (dotted (items t d a b x) (macro-names-each items (macro-names-in t out)))
      (vec (items d a b x) out)
      (atom (d a b x)
        (if (and (syn-symbol? s) (= x 0) (macro? (syn-symbol s))
                 (not (name-in? (syn-symbol s) out)))
            (cons (syn-symbol s) out)
            out)))))
(define macro-names-each (->* (syns-a names) names)
  (lambda (xs out) (if (null? xs) out (macro-names-each (cdr xs) (macro-names-in (car xs) out)))))
;; Whether a macro's name or a path is written in `s`, outside a quoted
;; datum.
(define names-macro? (->* (syn) bool)
  (lambda (s)
    (tagcase s
      (lst (items d a b x) (and (not (quote-headed? items)) (any-names-macro? items)))
      (dotted (items t d a b x)
        (and (not (quote-headed? items)) (or (any-names-macro? items) (names-macro? t))))
      (vec (items d a b x) #f)
      (atom (d a b x)
        (and (syn-symbol? s)
             (or (macro? (syn-symbol s)) (path-named? (symbol->string (syn-symbol s)))))))))
(define any-names-macro? (->* (syns-a) bool)
  (lambda (xs) (and (not (null? xs)) (or (names-macro? (car xs)) (any-names-macro? (cdr xs))))))
(define quote-headed? (->* (syns-a) bool)
  (lambda (xs)
    (and (not (null? xs)) (syn-symbol? (car xs)) (string=? (syn-name (car xs)) "quote"))))
;; Path `p`, a program walk's (innermost step first), as the indices of the
;; items it goes through, list by list, outermost first; a list's tail
;; after `k` items, `-1 - k`.
(define index-path (->* (addr) ixs) (lambda (p) (indices (reverse p) 0)))
(define indices (->* (addr int) ixs)
  (lambda (steps k)
    (cond ((null? steps) (if (= k 0) nil (list (- -1 k))))
          ((car steps) (cons k (indices (cdr steps) 0)))
          (else (indices (cdr steps) (+ k 1))))))
;; Uses `us` in the order they are written, by their index paths.
(define uses-sorted (->* (uses) uses)
  (lambda (us)
    (if (or (null? us) (null? (cdr us)))
        us
        (let ((h (halves us nil nil)))
          (uses-merged (uses-sorted (extract h 1)) (uses-sorted (extract h 2)))))))
(define halves (->* (uses uses uses) (tupleof uses uses))
  (lambda (us a b) (if (null? us) (tuple a b) (halves (cdr us) b (cons (car us) a)))))
(define uses-merged (->* (uses uses) uses)
  (lambda (a b)
    (cond ((null? a) b)
          ((null? b) a)
          ((ixs<? (extract (car b) 1) (extract (car a) 1)) (cons (car b) (uses-merged a (cdr b))))
          (else (cons (car a) (uses-merged (cdr a) b))))))
(define ixs<? (->* (ixs ixs) bool)
  (lambda (p q)
    (cond ((null? q) #f)
          ((null? p) #t)
          ((= (car p) (car q)) (ixs<? (cdr p) (cdr q)))
          (else (< (ix-order (car p)) (ix-order (car q)))))))
;; An index's place among a list's parts: its items in order, then its tail.
(define ix-order (->* (int) int) (lambda (i) (if (< i 0) (+ (* 2 (- -1 i)) 1) (* 2 i))))
;; Of uses `us`, in order, those in the item of index `k` (or the tail, a
;; negative one) first, each by its path from it; and those after them.
(define uses-in (->* (int uses) uses)
  (lambda (k us)
    (if (uses-at? k us)
        (cons (tuple (cdr (extract (car us) 1)) (extract (car us) 2)) (uses-in k (cdr us)))
        nil)))
(define uses-past (->* (int uses) uses)
  (lambda (k us) (if (uses-at? k us) (uses-past k (cdr us)) us)))
(define uses-at? (->* (int uses) bool)
  (lambda (k us)
    (and (not (null? us)) (not (null? (extract (car us) 1))) (= (car (extract (car us) 1)) k))))
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
