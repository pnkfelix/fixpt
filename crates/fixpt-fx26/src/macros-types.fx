;;; Typed hygienic macros, in FX-26: syntax types (Herman's `σ`), as the
;;; Rust expander has them (`macros.rs`, whose comment says the notation),
;;; read from syntax, and compared: by the shapes of source syntax
;;; (`overlap`, `fits`) and as types (`sub`). Part of the expander
;;; (`macros.fx`, which loads it). How one fails is the caller's (`fails`),
;;; as `parser-forms.fx`'s.

(module-parameters ((rs region) (re region) (rm region) (rc region) (rp region)))
(define parser-module ((proj (load-module "fx26:parser.fx") rs re rm rc rp)))
(define reader-types (with parser-module reader-types))
(import reader-types atom lst dotted vec (type syn))
(import parser-module syn-start syn-end syn-symbol? syn-name syn-symbol len nth mk-list
        (type syns-a names) (effect parses))
(define kernel (load-module "fx26:macros-kernel.fx"))

;; How a part of the expander fails: the caller's `pfail-at`.
(define-type fails (subr parses (string int int) void))
(define fail-at (->* (fails string syn) void)
  (lambda (fail message s) (fail message (syn-start s) (syn-end s))))

;;; ------------------------------------------------------------ the types

;; An address's steps from its root, first first: `#t` the car.
(define-type addr (listof bool acyclic))
;; What a part at an address binds (Herman's `δ`): 0 nothing, 1 a value's
;; variable, 2 a rib, 3 a ribcage, 4 a description's variable, 5 both, a
;; place (`letrena`'s), which is also a value of type `(place r)`.
(define-type entries (listof (tupleof addr int) acyclic))
;; One of a ribcage's: a rib, or the ribcage exported at an address; or, a
;; program's (`scope-forms`), what the module at an address gives (a file's
;; module parameters, each included in its items).
(define-datatype ring (ring-rib entries) (ring-at addr) (ring-shape addr))
(define-type rings (listof ring acyclic))
;; What an environment is made of: a pattern variable bound (`bvar`,
;; `dvar`), the rib or ribcage a pattern variable exports, a template's own
;; binder (its node).
;; Each but a ribcage bound in a namespace: a description's if `#t`, else a
;; value's (Herman's δ, one per namespace). A pattern variable's, with how
;; many lists by ellipsis gathered it: 0 its own repetition's, 1 every
;; repetition's, as a list's export gathers its elements' (`macros.rs`'s
;; `Atom::Var`; `TODO.md` §223).
(define-datatype atm (atm-var symbol bool int) (atm-rib-of symbol) (atm-lit int bool))
(define-type atms (listof atm acyclic))
;; What an annotation binds (Herman's `β`): a rib, or a ribcage; or a rib of
;; what it binds, as found, the binders a template's description writes
;; (`macros.rs`'s `Bind::Direct`), or what the repetitions before a repeated
;; part bound (`Bind::Earlier`).
(define-datatype bind (bind-rib entries) (bind-cage rings) (bind-direct atms) (bind-earlier atms)
  ;; What the module at an address gives, `(shape A)`: what `with` and
  ;; `include` bind, in a program's walk (`scope-forms`).
  (bind-shape addr))
;; What a typed hole says (`macros.rs`'s `Hole`): its type and its effect,
;; each as written, in a list of one, or none if it is left out.
(define-type hole (tupleof syns-a syns-a))
;; A syntax type (`macros.rs`'s `STy`). A `mu`, `(s-mu body round part)`,
;; a value compared by its structure, its variable `(s-var n)` by how many
;; `mu`s are between them (de Bruijn's numbering), 0 the innermost; its
;; round and part, of a signature being inferred (`build`), else -1.
;; `s-typed`, an `expr` or `bvar` with its type or effect written.
(define-datatype sty
  (s-expr) (s-bvar) (s-id) (s-data) (s-type) (s-label) (s-nil)
  (s-literal symbol) (s-pair sty sty) (s-import sty bind) (s-export sty bind) (s-mark symbol int)
  (s-mu sty int int) (s-var int) (s-many sty) (s-union (listof sty acyclic)) (s-typed sty hole)
  ;; An expression that is a lambda, where a form wants one (`letrec`).
  (s-lambda)
  ;; A definition, where a template makes one (the kernel's `begin` of
  ;; them); no part of a signature, for now.
  (s-defn)
  ;; A description's binder; a binder's kind, which names nothing.
  (s-dvar) (s-kind)
  ;; A module's item, as a program's walk takes one (`scope-forms`): a
  ;; definition, a string (a comment), or an expression run as the module
  ;; is made.
  (s-item)
  ;; A macro's transformer a template writes (`macros.rs`'s `STy::Rules`).
  (s-rules))
(define-type stys (listof sty acyclic))

;; Of `t`, under `k` `mu`s more than it is, each variable `j` changed as
;; `op` says, in a list of one; none if none is (what is not is shared). Op
;; 0 raises one `k` or more out by `d`; 1 replaces `k`'s by `x` and lowers
;; those further out, as its `mu` is gone; 2 closes one `k` or more out, by
;; `env`'s `mu`s (closed, the innermost first); 3 finds one that is `k`.
(define vars-map (->* (sty int int int sty stys) stys)
  (lambda (t k op d x env)
    (tagcase t
      (s-var (j)
        (cond ((< j k) nil)
              ((= op 0) (list (s-var (+ j d))))
              ((= op 2) (list (nth-sty env (- j k))))
              ((= op 3) (if (= j k) (list t) nil))
              ((> j k) (list (s-var (- j 1))))
              ((= k 0) (list x))
              (else (list (shift x k 0)))))
      (s-mu (b r p) (one-var (vars-map b (+ k 1) op d x env) (lambda ((c sty)) (s-mu c r p))))
      (s-pair (a b)
        (let ((a2 (vars-map a k op d x env)) (b2 (vars-map b k op d x env)))
          (if (and (null? a2) (null? b2)) nil (list (s-pair (or-same a2 a) (or-same b2 b))))))
      (s-import (b y) (one-var (vars-map b k op d x env) (lambda ((c sty)) (s-import c y))))
      (s-export (b y) (one-var (vars-map b k op d x env) (lambda ((c sty)) (s-export c y))))
      (s-many (b) (one-var (vars-map b k op d x env) (lambda ((c sty)) (s-many c))))
      (s-typed (b h) (one-var (vars-map b k op d x env) (lambda ((c sty)) (s-typed c h))))
      (s-union (ms)
        (let ((c (vars-map-each ms k op d x env))) (if (null? c) nil (list (s-union (car c))))))
      (else y nil))))
(define one-var (->* (stys (-> (sty) sty)) stys)
  (lambda (c f) (if (null? c) nil (list (f (car c))))))
(define or-same (->* (stys sty) sty) (lambda (c t) (if (null? c) t (car c))))
(define vars-map-each (->* (stys int int int sty stys) (listof stys acyclic))
  (lambda (ms k op d x env)
    (if (null? ms)
        nil
        (let ((m (vars-map (car ms) k op d x env)) (r (vars-map-each (cdr ms) k op d x env)))
          (if (and (null? m) (null? r))
              nil
              (list (cons (or-same m (car ms)) (if (null? r) (cdr ms) (car r)))))))))
(define nth-sty (->* (stys int) sty)
  (lambda (xs i) (if (= i 0) (car xs) (nth-sty (cdr xs) (- i 1)))))
;; `t` placed under `d` `mu`s more, its variables `k` or more out raised.
(define shift (->* (sty int int) sty) (lambda (t d k) (or-same (vars-map t k 0 d t nil) t)))
;; `t`, under the `mu` `k` around it, `x` for its variable, that `mu` gone.
(define subst (->* (sty int sty) sty) (lambda (t k x) (or-same (vars-map t k 1 0 x nil) t)))
;; `mu` `t` unfolded once: its body, its variable `t` again.
(define unfold-mu (->* (sty) sty)
  (lambda (t) (tagcase t (s-mu (b r p) (subst b 0 t)) (else y t))))
;; `t` closed by the `mu`s `env` around it, closed, the innermost first.
(define closed-by (->* (sty stys) sty) (lambda (t env) (or-same (vars-map t 0 2 0 t env) t)))
;; Whether `t` refers to a `mu` `k` or more out from it; to the one `k`.
(define free-at? (->* (sty int) bool) (lambda (t k) (not (null? (vars-map t k 0 1 t nil)))))
(define refers? (->* (sty int) bool) (lambda (t k) (not (null? (vars-map t k 3 0 t nil)))))
;; `t`, under one `mu` it does not refer to, without it, in a list of one;
;; none if it refers to it.
(define lowered (->* (sty) stys)
  (lambda (t) (if (refers? t 0) nil (list (subst t 0 (s-nil))))))
;; The trailmarks defined (`macros.rs`'s `Mark`), the last first: each name's
;; number, 0 where a macro of the name hides one; else the standard ones,
;; `else` 1 and `=>` 2, which a file sees too.
(define-type marked (listof (tupleof symbol int) acyclic))
(define marks (ref marked rs) (new nil))
(define mark-count (ref int rs) (new 2))
;; What is said of a name a macro takes for a trailmark that is none.
(define no-trailmark (->* (string) string)
  (lambda (n)
    (string-append "`" n "` names no trailmark here: `(define-syntax " n " (trailmark))`")))
(define mark-in (->* (symbol marked) int)
  (lambda (n ms)
    (cond ((null? ms) (cond ((symbol=? n 'else) 1) ((symbol=? n '=>) 2) (else 0)))
          ((symbol=? n (extract (car ms) 1)) (extract (car ms) 2))
          (else (mark-in n (cdr ms))))))

;; Whether typed hole `h` (none or one) has its effect written `pure`.
(define pure-hole? (->* ((listof hole acyclic)) bool)
  (lambda (h)
    (and (not (null? h)) (not (null? (extract (car h) 2)))
         (syn-symbol? (car (extract (car h) 2)))
         (string=? (syn-name (car (extract (car h) 2))) "pure"))))
;; Whether a pattern variable of type `t` has an expression in it: not a
;; binder, name, label, datum or type.
(define affine-kind? (->* (sty) bool)
  (lambda (t)
    (let ((k (kind-of t)))
      (not (or (= k 1) (= k 2) (= k 5) (= k 3) (= k 4) (= k 12) (= k 13))))))

;;; ------------------------------------------------------------ syntax

(define syntax-module ((proj (load-module "fx26:macros-syntax.fx") rs re rm rc rp)))
(define syn-nil? (with syntax-module syn-nil?))
(define syn-keyword? (with syntax-module syn-keyword?))
(define syn-number? (with syntax-module syn-number?))
(define split (with syntax-module split))
(define show-syn (with syntax-module show-syn))
(define datum->syn (with syntax-module datum->syn))
(define reserved? (with syntax-module reserved?))
(define reserved-sym? (with syntax-module reserved-sym?))
(define desc-word? (with syntax-module desc-word?))
(define type-form? (with syntax-module type-form?))
(define reserved-syn? (with syntax-module reserved-syn?))
(define name-in? (with syntax-module name-in?))
(define int-in? (with syntax-module int-in?))

;;; ------------------------------------------------------------ reading

;; Syntax type `s`, read: `named`'s names (the kernel's abbreviations), and
;; the `mu` variables in scope, innermost first, each `#f` that of a list by
;; ellipsis, which no name refers to.
(define-type named (listof (tupleof symbol sty) acyclic))
(define-type mu-scope (listof (tupleof symbol bool) acyclic))
(define read-sty (->* (fails syn named mu-scope) sty)
  (lambda (fail s named scope)
    (cond
      ((syn-nil? s) (s-nil))
      ((syn-symbol? s) (read-sty-name fail s named scope))
      (else
       (let* ((parts (split s)) (hd (if (null? parts) s (car parts)))
              ;; The forms below are proper lists; a dotted one is a pair.
              (head (if (and (syn-symbol? hd) (proper? s)) (syn-name hd) "")))
         (cond
           ((null? parts) (begin (fail-at fail "a syntax type: not one" s) (s-nil)))
           ;; `(σ … σ ...)`: a list ending in any number of the last `σ`.
           ((let ((items (proper-items s)))
              (and (>= (len items) 2) (ellipsis? (nth items (- (len items) 1)))))
            (read-seq-list fail s (proper-items s) named scope))
           ((or (string=? head "import") (string=? head "export"))
            (let ((args (proper-items s)))
              (if (= (len args) 3)
                  (let ((body (read-sty fail (nth args 1) named scope))
                        (b (read-bind fail (nth args 2))))
                    (cond ((not (string=? head "import")) (s-export body b))
                          ((tagcase b (bind-rib (es) (syntax-entry? es)) (else y #f))
                           (begin (fail-at fail (string-append "a syntax type: a macro's "
                                                               "binder, `(macro …)`, says what a "
                                                               "use defines, in what its "
                                                               "signature makes, `(defn D …)`")
                                           s)
                                  (s-import body b)))
                          (else (s-import body b))))
                  (read-pair fail s parts named scope))))
           ((string=? head "mu") (read-mu fail s named scope))
           ((or (string=? head "union") (string=? head "oneof"))
            (let ((ms (read-each fail (cdr (proper-items s)) named scope)))
              ;; Members that refer to a `mu` around them, checked when it
              ;; is read whole (`mu-read`).
              (begin
                (if (and (not (any-free? ms)) (any-overlap? ms)) (fail-at fail oneof-apart s) #u)
                (s-union ms))))
           ;; `(expr #:type T #:effect E)`, `(bvar #:type T)`: a list whose
           ;; second is a keyword, which no syntax type is.
           ((and (or (string=? head "expr") (string=? head "bvar") (string=? head "lambda"))
                 (> (len (proper-items s)) 1) (syn-keyword? (nth (proper-items s) 1)))
            (s-typed (cond ((string=? head "expr") (s-expr))
                           ((string=? head "bvar") (s-bvar))
                           (else (s-lambda)))
                     (read-hole fail (cdr (proper-items s)) head s nil nil)))
           ((and (string=? head "many") (= (len (proper-items s)) 2))
            (s-many (read-sty fail (nth (proper-items s) 1) named scope)))
           ((and (string=? head "literal") (= (len (proper-items s)) 2))
            (let ((n (nth (proper-items s) 1)))
              (cond ((not (syn-symbol? n))
                     (begin (fail-at fail "a syntax type: `(literal name)`" s) (s-nil)))
                    ;; The kernel's words, as its signatures write them, and
                    ;; a reserved name; a name a macro matches, a trailmark.
                    ((and (null? named) (not (reserved-syn? n)))
                     (begin (fail-at fail (string-append "a syntax type: `(literal " (syn-name n)
                                                         ")` is a kernel form's word; a name a "
                                                         "macro's pattern matches is a "
                                                         "trailmark's, `(trailmark " (syn-name n)
                                                         ")`")
                                     s)
                            (s-nil)))
                    (else (s-literal (syn-symbol n))))))
           ((and (string=? head "trailmark") (= (len (proper-items s)) 2))
            (let ((n (nth (proper-items s) 1)))
              (cond ((not (syn-symbol? n))
                     (begin (fail-at fail "a syntax type: `(trailmark name)`" s) (s-nil)))
                    ((= (mark-in (syn-symbol n) (get marks)) 0)
                     (begin (fail-at fail (string-append "a syntax type: "
                                                         (no-trailmark (syn-name n)))
                                     s)
                            (s-nil)))
                    (else (s-mark (syn-symbol n) (mark-in (syn-symbol n) (get marks)))))))
           (else (read-pair fail s parts named scope))))))))
;; The items of a list type ending in `σ ...`: the last `σ` repeated
;; (`macros.rs`'s `seq`), read under its `mu`, after the ones before it,
;; each once; `s` the whole.
(define read-seq-list (->* (fails syn syns-a named mu-scope) sty)
  (lambda (fail s items named scope)
    (if (null? (cdr (cdr items)))
        (mu-read fail (seq-type (read-sty fail (car items) named
                                          (cons (tuple (string->symbol "") #f) scope)))
                 s scope)
        (let ((first (read-sty fail (car items) named scope)))
          (s-pair first (read-seq-list fail s (cdr items) named scope))))))
;; `mu` `t`, read at `s` under `scope`: if it is closed, each `oneof` in it
;; whose members refer to a `mu` around them, which its reading left, its
;; members closed, told apart by their shapes (`macros.rs`'s `mu_read`).
(define mu-read (->* (fails sty syn mu-scope) sty)
  (lambda (fail t s scope)
    (begin (if (and (null? scope) (not (oneofs-apart? t nil))) (fail-at fail oneof-apart s) #u)
           t)))
(define oneof-apart string
  (string-append "a syntax type: a `oneof`'s members must be told apart by their shapes in the "
                 "source (an `expr` may be anything)"))
;; Whether, of `t` under the `mu`s `env` (closed, the innermost first),
;; each `oneof` whose members refer to one of them has them apart.
(define oneofs-apart? (->* (sty stys) bool)
  (lambda (t env)
    (tagcase t
      (s-mu (b r p) (oneofs-apart? b (cons (closed-by t env) env)))
      (s-union (ms)
        (and (or (not (any-free? ms)) (not (any-overlap? (closed-each ms env))))
             (all-apart? ms env)))
      (s-pair (a d) (and (oneofs-apart? a env) (oneofs-apart? d env)))
      (s-import (b x) (oneofs-apart? b env)) (s-export (b x) (oneofs-apart? b env))
      (s-many (b) (oneofs-apart? b env)) (s-typed (b h) (oneofs-apart? b env))
      (else y #t))))
(define all-apart? (->* (stys stys) bool)
  (lambda (ms env) (or (null? ms) (and (oneofs-apart? (car ms) env) (all-apart? (cdr ms) env)))))
(define any-free? (->* (stys) bool)
  (lambda (ms) (and (not (null? ms)) (or (free-at? (car ms) 0) (any-free? (cdr ms))))))
(define closed-each (->* (stys stys) stys)
  (lambda (ms env) (if (null? ms) nil (cons (closed-by (car ms) env) (closed-each (cdr ms) env)))))
;; `(elem ...)`: `(mu l (union () (elem . l)))`, and if `elem` exports,
;; each element's export together, as a `let`'s bindings do; a binder
;; alone, `bvar` or `dvar`, exports itself.
(define seq-type (->* (sty) sty)
  (lambda (elem0)
    (let ((elem (tagcase elem0
                  (s-bvar () (s-export elem0 (bind-rib (list (tuple (the addr nil) 1)))))
                  (s-dvar () (s-export elem0 (bind-rib (list (tuple (the addr nil) 4)))))
                  (else y elem0))))
      (s-mu (s-union (seq-body elem)) -1 -1))))
;; A list's `mu`'s body, `elem` under it: `()`, and the pair of `elem` and the list; an
;; element exporting a rib, the pair its entries from the pair's root, `(A …)`, then the
;; rest's, `(D rib)`: an element written out is in the pair's region (`macros.rs`'s
;; `seq_members`).
(define seq-body (->* (sty) stys)
  (lambda (elem)
    (let ((none (s-export (s-nil) (bind-rib nil))) (d (tuple (the addr (list #f)) 2)))
      (tagcase elem
        (s-export (e bd)
          (tagcase bd
            (bind-rib (es) (list none (s-export (s-pair e (s-var 0)) (bind-rib (cars-at es d)))))
            (else y (list none (s-export (s-pair elem (s-var 0))
                                         (bind-rib (list (tuple (the addr (list #t)) 2) d)))))))
        (else y (list (s-nil) (s-pair elem (s-var 0))))))))
(define cars-at (->* (entries (tupleof addr int)) entries)
  (lambda (es d)
    (if (null? es) (list d)
        (cons (tuple (the addr (cons #t (extract (car es) 1))) (extract (car es) 2))
              (cars-at (cdr es) d)))))
;; The type of an element of list type `t`, in a list of one, if a template
;; or pattern may give its elements by ellipsis: a `mu` of `()` and of pairs
;; of an element and itself, which binds no more than what each element
;; exports, all of them together (a `let`'s); or each element's in the
;; scope of those after it, the list a ribcage (a `let*`'s, a `begin`'s
;; definitions, `seq-cage?`) (`macros.rs`'s `seq_of`).
(define seq-elem (->* (sty) stys)
  (lambda (t)
    (let ((caged (cage-seq-elem t)))
      (if (null? caged)
          (tagcase t
            (s-mu (b r p)
              (tagcase b (s-union (ms) (out-of-mu (seq-members ms nil #f) t)) (else y nil)))
            (else y nil))
          caged))))
;; Elements `es`, found under list `mu` `t`, in a list of one, outside it.
(define out-of-mu (->* (stys sty) stys)
  (lambda (es t) (if (null? es) nil (list (subst (car es) 0 t)))))
;; Whether `r`, under a list's `mu`, is the list.
(define itself? (->* (sty) bool) (lambda (r) (tagcase r (s-var (j) (= j 0)) (else y #f))))
(define seq-cage? (->* (sty) bool)
  (lambda (t)
    (or (not (null? (cage-seq-elem t))) (and (seq-scoped? t) (not (null? (seq-elem t)))))))
;; A ribcage's list (`macros.rs`'s `cage_seq_of`): `(export () (cage))`, and
;; pairs `(export (e . (import t β)) (cage (at D) β'))`, the rest in the
;; scope of what the element binds, `β`, which is also the list's innermost
;; rib or ribcage, `β'`, after the rest's. The element type, with what it
;; exports, in a list of one.
(define cage-seq-elem (->* (sty) stys)
  (lambda (t)
    (tagcase t
      (s-mu (b r p)
        (tagcase b (s-union (ms) (out-of-mu (cage-members ms nil #f) t)) (else y nil)))
      (else y nil))))
(define cage-members (->* (stys stys bool) stys)
  (lambda (ms es none)
    (if (null? ms)
        (if (and none (not (null? es)) (null? (cdr es))) es nil)
        (tagcase (car ms)
          (s-export (core b)
            (tagcase b
              (bind-cage (rings)
                (cond ((and (null? rings) (= (kind-of core) 6)) (cage-members (cdr ms) es #t))
                      ((null? rings) nil)
                      (else
                       (let ((e (cage-pair core rings)))
                         (if (null? e) nil (cage-members (cdr ms) (cons (car e) es) none))))))
              (else y nil)))
          (else y nil)))))
;; Pair type `core` of a ribcage's list, under its `mu`, which exports `rings`: its
;; element, with what it exports, in a list of one; none if it is not one.
(define cage-pair (->* (sty rings) stys)
  (lambda (core rings)
    (tagcase core
      (s-pair (a d)
        (tagcase d
          (s-import (r inner)
            (if (and (itself? r) (not (null? (cdr rings)))
                     (null? (cdr (cdr rings)))
                     (tagcase (car rings) (ring-at (x) (addr=? x (list #f))) (else y #f)))
                (let ((own (car (cdr rings))))
                  (tagcase own
                    (ring-rib (es)
                      (let ((stripped (cars-of es nil)))
                        (if (and (bind=? inner (bind-rib es)) (not (null? stripped)))
                            (list (s-export a (bind-rib (car stripped))))
                            nil)))
                    (ring-at (x)
                      (if (and (addr=? x (list #t)) (bind=? inner (bind-cage (list own))))
                          (list a)
                          nil))
                    (ring-shape (x) nil)))
                nil))
          (else y nil)))
      (else y nil))))
;; Entries `es`, each at its car's, from the car, onto `out`, in a list of
;; one; none if one is not its car's.
(define cars-of (->* (entries entries) (listof entries acyclic))
  (lambda (es out)
    (cond ((null? es) (list (the entries (reverse out))))
          ((and (not (null? (extract (car es) 1))) (car (extract (car es) 1)))
           (cars-of (cdr es) (cons (tuple (cdr (extract (car es) 1)) (extract (car es) 2)) out)))
          (else nil))))
;; Of members `ms`, from the first: the elements found so far `es`, the last
;; first, and whether `()` is one of them.
(define seq-members (->* (stys stys bool) stys)
  (lambda (ms es none)
    (if (null? ms)
        (cond ((or (null? es) (not none)) nil)
              ((null? (cdr es)) es)
              (else (list (s-union (the stys (reverse es))))))
        (let* ((m (car ms)) (core (tagcase m (s-export (b x) b) (else y m)))
               (own (tagcase m
                      (s-export (b x) (tagcase x (bind-rib (es) (own-entries es nil)) (else z nil)))
                      (s-import (b x) nil)
                      (else y (list (the entries nil))))))
          (cond ((null? own) nil)
                ((= (kind-of core) 6) (seq-members (cdr ms) es #t))
                (else
                 (tagcase core
                   (s-pair (a d)
                     (if (seq-rest? m d)
                         (seq-members (cdr ms) (cons (with-own a (car own)) es) none)
                         nil))
                   (else y nil))))))))
;; Whether `d`, member `m`'s pair's rest, is list `id` itself, perhaps in
;; the scope of what the pair's element binds (a `lambda`'s parameters,
;; each in the later ones' types: `seq-scoped?`).
(define seq-rest? (->* (sty sty) bool)
  (lambda (m d)
    (tagcase d
      (s-var (j) (= j 0))
      (s-import (r b)
        (and (itself? r)
             (tagcase b
               (bind-rib (fs)
                 (tagcase m
                   (s-export (c x)
                     (tagcase x (bind-rib (es) (entries=? fs (car-entries es))) (else y #f)))
                   (else y #f)))
               (else y #f))))
      (else y #f))))
;; Entries `es` at their car's, from the pair's root.
(define car-entries (->* (entries) entries)
  (lambda (es)
    (cond ((null? es) nil)
          ((and (not (null? (extract (car es) 1))) (car (extract (car es) 1)))
           (cons (car es) (car-entries (cdr es))))
          (else (car-entries (cdr es))))))
;; Whether list type `t`'s elements are each in the scope of what those
;; before it bind, its pairs' rests imported.
(define seq-scoped? (->* (sty) bool)
  (lambda (t)
    (tagcase t
      (s-mu (b r p) (tagcase b (s-union (ms) (rest-imported? ms)) (else y #f)))
      (else y #f))))
(define rest-imported? (->* (stys) bool)
  (lambda (ms)
    (and (not (null? ms))
         (or (tagcase (peel-export (car ms))
               (s-pair (a d) (tagcase d (s-import (r b) #t) (else y #f)))
               (else y #f))
             (rest-imported? (cdr ms))))))
(define peel-export (->* (sty) sty)
  (lambda (m) (tagcase m (s-export (c x) c) (else y m))))
;; A pair's export's entries `es` that are its car's, from the car, onto
;; `out`, in a list of one; none if one is neither its car's nor `(D rib)`.
(define own-entries (->* (entries entries) (listof entries acyclic))
  (lambda (es out)
    (if (null? es)
        (list (the entries (reverse out)))
        (let ((a (extract (car es) 1)) (d (extract (car es) 2)))
          (cond ((and (not (null? a)) (car a)) (own-entries (cdr es) (cons (tuple (cdr a) d) out)))
                ((and (not (null? a)) (null? (cdr a)) (= d 2)) (own-entries (cdr es) out))
                (else nil))))))
;; Element `a`, which exports what `own` says of it.
(define with-own (->* (sty entries) sty)
  (lambda (a own)
    (cond ((null? own) a)
          ((and (tagcase a (s-export (b x) #t) (else y #f)) (null? (cdr own))
                (null? (extract (car own) 1)) (= (extract (car own) 2) 2))
           a)
          (else (s-export a (bind-rib own))))))
;; The type at `t`, its annotations seen through, not its `mu`s.
(define peel (->* (sty) sty)
  (lambda (t)
    (tagcase t
      (s-import (b x) (peel b)) (s-export (b x) (peel b)) (s-many (b) (peel b))
      (s-typed (b h) (peel b))
      (else y t))))
;; Whether `s` is the name `...`.
(define ellipsis? (->* (syn) bool)
  (lambda (s) (and (syn-symbol? s) (string=? (syn-name s) "..."))))
;; `x` of `(x ...)`, a part repeated, in a list of one, if `s` is one.
(define ellipsis-of (->* (syn) syns-a)
  (lambda (s)
    (let ((items (proper-items s)))
      (if (and (= (len items) 2) (ellipsis? (nth items 1))) (list (car items)) nil))))
(define read-pair (->* (fails syn syns-a named mu-scope) sty)
  (lambda (fail s parts named scope)
    (s-pair (read-sty fail (car parts) named scope) (read-sty fail (nth parts 1) named scope))))
(define read-each (->* (fails syns-a named mu-scope) stys)
  (lambda (fail xs named scope)
    (if (null? xs)
        nil
        (cons (read-sty fail (car xs) named scope) (read-each fail (cdr xs) named scope)))))
(define read-sty-name (->* (fails syn named mu-scope) sty)
  (lambda (fail s named scope)
    (let ((n (syn-symbol s)))
      (let ((mu (scope-of n scope)))
        (if (>= mu 0)
            (s-var mu)
            (let ((t (named-of n named)))
              (if (null? t)
                  (case n
                    ((expr) (s-expr)) ((bvar) (s-bvar)) ((id) (s-id)) ((data) (s-data))
                    ((lambda) (s-lambda))
                    ;; A description, kinded after expansion as an
                    ;; expression is typed.
                    ((desc) (s-type)) ((label) (s-label)) ((dvar) (s-dvar)) ((kind) (s-kind))
                    ((item) (s-item))
                    ((type)
                     (begin (fail-at fail (string-append "a syntax type: a part that is a "
                                                         "description is written `desc`, not "
                                                         "`type`")
                                     s)
                            (s-nil)))
                    (else
                     (begin
                       (fail-at fail (string-append "a syntax type: `" (symbol->string n) "` is "
                                                    "none (`expr`, `bvar`, `id`, `data`, `desc`, "
                                                    "`label`, `lambda`, `dvar`, `kind`, `item`, "
                                                    "or a `mu`'s variable)")
                                s)
                       (s-nil))))
                  (car t))))))))
(define scope-of (->* (symbol mu-scope) int)
  (lambda (n scope)
    (cond ((null? scope) -1)
          ((and (extract (car scope) 2) (symbol=? n (extract (car scope) 1))) 0)
          (else (let ((i (scope-of n (cdr scope)))) (if (< i 0) i (+ i 1)))))))
(define named-of (->* (symbol named) stys)
  (lambda (n named)
    (cond ((null? named) nil)
          ((symbol=? n (extract (car named) 1)) (list (extract (car named) 2)))
          (else (named-of n (cdr named))))))
;; `(mu v body)`.
(define read-mu (->* (fails syn named mu-scope) sty)
  (lambda (fail s named scope)
    (let ((args (proper-items s)))
      (if (and (= (len args) 3) (syn-symbol? (nth args 1)))
          (let ((body (read-sty fail (nth args 2) named
                                (cons (tuple (syn-symbol (nth args 1)) #t) scope))))
            (begin
              (if (guarded? body 0)
                  #u
                  (fail-at fail (string-append "a syntax type: a `mu`'s variable is used where no "
                                               "pair is around it (Herman's types are "
                                               "contractive)")
                           s))
              (mu-read fail (s-mu body -1 -1) s scope)))
          (begin (fail-at fail "a syntax type: `(mu variable type)`" s) (s-nil))))))
;; Whether `s` is a proper list of one or more.
(define proper? (->* (syn) bool)
  (lambda (s) (tagcase s (lst (items d a b x) (not (null? items))) (else y #f))))

;; A typed hole's keywords and what each says, `#:type T` and, of an `expr`,
;; `#:effect E`, each once: from `parts`, onto `ty` and `eff`; `kind`, the
;; part's.
(define read-hole (->* (fails syns-a string syn syns-a syns-a) hole)
  (lambda (fail parts kind s ty eff)
    (let* ((expr? (string=? kind "expr"))
           (usage (string-append "a syntax type: "
                                 (if expr?
                                     "`(expr #:type T #:effect E)`, either left out"
                                     (string-append "`(" kind " #:type T)`")))))
      (cond
        ((null? parts) (tuple ty eff))
        ((null? (cdr parts)) (begin (fail-at fail usage s) (tuple ty eff)))
        (else
         (let* ((k (car parts)) (word (if (syn-keyword? k) (keyword-name k) "")))
           (cond ((and (string=? word "type") (null? ty))
                  (read-hole fail (cdr (cdr parts)) kind s (list (nth parts 1)) eff))
                 ((and expr? (string=? word "effect") (null? eff))
                  (read-hole fail (cdr (cdr parts)) kind s ty (list (nth parts 1))))
                 ((or (string=? word "type") (and expr? (string=? word "effect")))
                  (begin (fail-at fail (string-append usage ", each once") k) (tuple ty eff)))
                 (else (begin (fail-at fail usage k) (tuple ty eff))))))))))
;; A keyword's name.
(define keyword-name (->* (syn) string)
  (lambda (s)
    (tagcase s
      (atom (d a b x) (if (keyword? d) (symbol->string (keyword->symbol d)) ""))
      (else y ""))))
;; A binding, `(rho (address δ) …)` or `(cage (rho …) (at address) …)`.
(define bind-usage string
  "a binding is `(rho (address δ) …)` or `(cage (rho …) (at address) …)`")
(define read-bind (->* (fails syn) bind)
  (lambda (fail b)
    (let* ((items (proper-items b)) (head (if (and (pair? items) (syn-symbol? (car items)))
                                             (syn-name (car items))
                                             "")))
      (cond ((string=? head "rho") (bind-rib (read-rib fail (cdr items))))
            ((string=? head "cage") (bind-cage (read-rings fail (cdr items))))
            ((and (string=? head "shape") (= (len items) 2))
             (bind-shape (read-addr fail (nth items 1))))
            (else (begin (fail-at fail bind-usage b) (bind-rib nil)))))))
(define read-rings (->* (fails syns-a) rings)
  (lambda (fail rs)
    (if (null? rs)
        nil
        (let* ((parts (proper-items (car rs)))
               (head (if (and (pair? parts) (syn-symbol? (car parts))) (syn-name (car parts)) ""))
               (r (cond ((string=? head "rho") (ring-rib (read-rib fail (cdr parts))))
                        ((and (string=? head "at") (= (len parts) 2))
                         (ring-at (read-addr fail (nth parts 1))))
                        ((and (string=? head "shape") (= (len parts) 2))
                         (ring-shape (read-addr fail (nth parts 1))))
                        (else (begin (fail-at fail bind-usage (car rs)) (ring-rib nil))))))
          (cons r (read-rings fail (cdr rs)))))))
(define read-rib (->* (fails syns-a) entries)
  (lambda (fail es)
    (if (null? es)
        nil
        (let ((parts (proper-items (car es))))
          (if (= (len parts) 2)
              (cons (tuple (read-addr fail (car parts)) (read-delta fail (nth parts 1)))
                    (read-rib fail (cdr es)))
              (begin (fail-at fail bind-usage (car es)) (the entries nil)))))))
;; δ, by number: 0 `none`, 1 `var`, 2 `rib`, 3 `env`, 4 `dvar`, 5 `place`;
;; 100 + k a macro's binder, its signature `(macro σ made)` (`Delta::Syntax`)
;; the `k`th of `syntax-sigs`, as written.
(define read-delta (->* (fails syn) int)
  (lambda (fail d)
    (let ((n (if (syn-symbol? d) (syn-name d) "")) (ds (proper-items d)))
      (cond ((string=? n "none") 0) ((string=? n "var") 1) ((string=? n "rib") 2)
            ((string=? n "env") 3) ((string=? n "dvar") 4) ((string=? n "place") 5)
            ;; A macro's binder: its kind the macro's signature.
            ((and (>= (len ds) 3) (syn-symbol? (car ds))
                  (or (string=? (syn-name (car ds)) "macro/addressed")
                      (string=? (syn-name (car ds)) "macro")))
             (let ((k (len (get syntax-sigs))))
               (begin (set syntax-sigs (append (get syntax-sigs) (list d))) (+ 100 k))))
            ((and (pair? ds) (syn-symbol? (car ds)) (string=? (syn-name (car ds)) "syntax"))
             (begin (fail-at fail (string-append "a macro's binder is written with its signature, "
                                                 "`(macro …)`, not `(syntax …)`")
                             d)
                    0))
            (else (begin (fail-at fail (string-append "δ is `none`, `var`, `dvar`, `place`, "
                                                      "`rib`, `env` or a macro's signature, "
                                                      "`(macro σ made)`")
                                  d)
                         0))))))
(define syntax-sigs (ref syns-a rs) (new nil))
;; The signature a macro's binder's δ `d` says, as written.
(define syntax-sig-of (->* (int) syn) (lambda (d) (nth (get syntax-sigs) (- d 100))))
;; Whether one of entries `es` is a macro's binder's.
(define syntax-entry? (->* (entries) bool)
  (lambda (es) (and (not (null? es)) (or (>= (extract (car es) 2) 100) (syntax-entry? (cdr es))))))
;; An address, `A`s and `D`s read right to left, or `()`, none: its steps,
;; first first.
(define read-addr (->* (fails syn) addr)
  (lambda (fail a)
    (let ((name (if (syn-symbol? a) (syn-name a) "")))
      (cond
        ((syn-nil? a) nil)
        ;; `(path #:a #:d …)`: its steps from the root, first first.
        ((let ((ps (proper-items a))) (and (pair? ps) (syn-symbol? (car ps))
                                           (string=? (syn-name (car ps)) "path")))
         (path-steps fail (cdr (proper-items a))))
        ((and (> (string-length name) 0) (a-or-d? name 0)) (steps name 0 nil))
        (else (begin (fail-at fail path-usage a) (the addr nil)))))))
(define path-usage string
  (string-append "an address is `(path #:a #:d …)`, its steps from the root, `#:a` the car "
                 "and `#:d` the cdr"))
(define path-steps (->* (fails syns-a) addr)
  (lambda (fail ks)
    (if (null? ks)
        nil
        (let ((k (keyword-name (car ks))))
          (cond ((string=? k "a") (cons #t (path-steps fail (cdr ks))))
                ((string=? k "d") (cons #f (path-steps fail (cdr ks))))
                (else (begin (fail-at fail path-usage (car ks)) (the addr nil))))))))
(define a-or-d? (->* (string int) bool)
  (lambda (s i)
    (or (= i (string-length s))
        (and (or (char=? (string-ref s i) #\A) (char=? (string-ref s i) #\D))
             (a-or-d? s (+ i 1))))))
;; The steps of `s`'s letters, the last first: from `j` on, onto `out`.
(define steps (->* (string int addr) addr)
  (lambda (s j out)
    (if (= j (string-length s))
        out
        (steps s (+ j 1) (cons (char=? (string-ref s j) #\A) out)))))
;; Whether `s` is a lambda as the checkers take one: a `lambda`, `rlambda`
;; or `vlambda`, in `plambda`s and `the`s (`macros.rs`'s `lambda_shaped`).
(define lambda-shaped? (->* (syn) bool)
  (lambda (s)
    (let* ((items (proper-items s))
           (head (if (and (not (null? items)) (syn-symbol? (car items)))
                     (syn-name (car items))
                     "")))
      (cond ((or (string=? head "lambda") (string=? head "rlambda") (string=? head "vlambda")) #t)
            ((and (or (string=? head "plambda") (string=? head "the")) (= (len items) 3))
             (lambda-shaped? (nth items 2)))
            (else #f)))))
;; A proper list's elements; none if `s` is not one.
(define proper-items (->* (syn) syns-a)
  (lambda (s) (tagcase s (lst (items d a b x) items) (else y nil))))

;; The kernel's forms' signatures, each by its name, and its definitions'
;; (its `begin` of them not its `begin` of expressions), its abbreviations
;; read on the way, `defn` among them, which no macro's signature names:
;; read once, the first time.
(define kernel-read (ref (tupleof named named named) rs)
  (new (tuple (the named nil) (the named nil) (the named nil))))
(define kernel-sigs (->* (fails) named)
  (lambda (fail) (extract (kernel-tables fail) 1)))
(define kernel-definitions (->* (fails) named)
  (lambda (fail) (extract (kernel-tables fail) 2)))
(define kernel-tables (->* (fails) (tupleof named named named))
  (lambda (fail)
    (begin
      (if (null? (extract (get kernel-read) 1))
          (set kernel-read (read-kernel fail (proper-items (datum->syn (with kernel kernel-forms)))
                                        (list (tuple 'defn (s-defn))) nil nil))
          #u)
      (get kernel-read))))
;; The binding structure of the forms the kernel's list has not, for a
;; program's walk alone (`scope-forms`), its signatures and definitions,
;; read with the kernel's abbreviations: read once, the first time.
(define scope-read (ref (tupleof named named named) rs)
  (new (tuple (the named nil) (the named nil) (the named nil))))
(define scope-sigs (->* (fails) named)
  (lambda (fail) (extract (scope-tables fail) 1)))
(define scope-definitions (->* (fails) named)
  (lambda (fail) (extract (scope-tables fail) 2)))
(define scope-tables (->* (fails) (tupleof named named named))
  (lambda (fail)
    (begin
      (if (null? (extract (get scope-read) 1))
          (set scope-read (read-kernel fail (proper-items (datum->syn (with kernel scope-forms)))
                                       (extract (kernel-tables fail) 3) nil nil))
          #u)
      (get scope-read))))
(define read-kernel (->* (fails syns-a named named named) (tupleof named named named))
  (lambda (fail fs named out defs)
    (if (null? fs)
        (tuple out defs named)
        (let* ((items (proper-items (car fs)))
               (t (read-sty fail (nth items 2) named nil))
               (n (syn-symbol (nth items 1)))
               (what (syn-name (car items))))
          (cond ((string=? what "define")
                 (read-kernel fail (cdr fs) (cons (tuple n t) named) out defs))
                ((string=? what "definition")
                 (read-kernel fail (cdr fs) named out (cons (tuple n t) defs)))
                (else (read-kernel fail (cdr fs) named (cons (tuple n t) out) defs)))))))

;;; ------------------------------------------------------------ comparing

;; The type at `t`, its annotations, `mu`s seen through to what is under
;; them.
(define unfold (->* (sty) sty)
  (lambda (t)
    (tagcase t
      (s-import (b x) (unfold b)) (s-export (b x) (unfold b)) (s-many (b) (unfold b))
      (s-typed (b h) (unfold b))
      (s-mu (b r p) (unfold (unfold-mu t)))
      (else y t))))
;; Whether `t` uses the variable of the `mu` `id` around it only under a
;; pair, a `mu` inside it looked into too: none unfolds to itself.
(define guarded? (->* (sty int) bool)
  (lambda (t id)
    (tagcase t
      (s-var (j) (not (= j id)))
      (s-mu (b r p) (guarded? b (+ id 1)))
      (s-import (b x) (guarded? b id)) (s-export (b x) (guarded? b id)) (s-many (b) (guarded? b id))
      (s-typed (b h) (guarded? b id))
      (s-union (ms) (all-guarded? ms id))
      (else y #t))))
(define all-guarded? (->* (stys int) bool)
  (lambda (ms id) (or (null? ms) (and (guarded? (car ms) id) (all-guarded? (cdr ms) id)))))

;; Whether some source syntax could be of both `a` and `b` (Herman's
;; shapes, §5.2.3): `expr` may be anything but a form's name; looked at to
;; `depth` pairs, past which they are taken to overlap.
(define overlap? (->* (sty sty int) bool)
  (lambda (a0 b0 depth)
    (let ((a (unfold a0)) (b (unfold b0)))
      (tagcase a
        (s-union (ms) (any-overlaps? ms b depth))
        (else y
          (tagcase b
            (s-union (ms) (any-overlaps-of? a ms depth))
            (else z (overlap-base? a b depth))))))))
(define any-overlaps? (->* (stys sty int) bool)
  (lambda (ms b depth)
    (and (not (null? ms)) (or (overlap? (car ms) b depth) (any-overlaps? (cdr ms) b depth)))))
(define any-overlaps-of? (->* (sty stys int) bool)
  (lambda (a ms depth)
    (and (not (null? ms)) (or (overlap? a (car ms) depth) (any-overlaps-of? a (cdr ms) depth)))))
;; A kind's number, for the cases of `overlap-base?`: 0 expr, 1 bvar, 2 id,
;; 3 data, 4 type, 5 label, 6 nil, 7 literal, 8 pair, 9 anything else, 10
;; lambda, 11 defn, 12 dvar, 13 kind, 14 item, 15 trailmark.
(define kind-of (->* (sty) int)
  (lambda (t)
    (tagcase t
      (s-expr () 0) (s-bvar () 1) (s-id () 2) (s-data () 3) (s-type () 4) (s-label () 5)
      (s-nil () 6) (s-literal (n) 7) (s-pair (a d) 8) (s-lambda () 10) (s-defn () 11)
      (s-dvar () 12) (s-kind () 13) (s-item () 14) (s-mark (n i) 15) (s-rules () 16)
      (else y 9))))
;; Whether `k` is a kind of no parts: one of what `(Expr | Id | Data | Type
;; | Label | Bvar | Dvar | Kind | Lambda | Defn)` names in `macros.rs`.
(define simple-kind? (->* (int) bool) (lambda (k) (or (< k 6) (> k 9))))
(define literal-of (->* (sty) symbol)
  (lambda (t) (tagcase t (s-literal (n) n) (else y (string->symbol "")))))
(define mark-of (->* (sty) int) (lambda (t) (tagcase t (s-mark (n i) i) (else y 0))))
(define overlap-base? (->* (sty sty int) bool)
  (lambda (a b depth)
    (let ((ka (kind-of a)) (kb (kind-of b)))
      (cond
        ;; A trailmark is itself: no expression, datum, binder or other
        ;; trailmark; an `id` may be any name.
        ((and (= ka 15) (= kb 15)) (= (mark-of a) (mark-of b)))
        ((or (and (= ka 15) (= kb 2)) (and (= ka 2) (= kb 15))) #t)
        ((or (= ka 15) (= kb 15)) #f)
        ((and (= ka 7) (or (= kb 0) (binder-kind? kb))) #f)
        ((and (= kb 7) (or (= ka 0) (binder-kind? ka))) #f)
        ;; A lambda is a list: no name, `()` or label, and any list.
        ((or (= ka 10) (= kb 10))
         (let ((other (if (= ka 10) kb ka)))
           (not (or (= other 7) (binder-kind? other) (= other 2) (= other 6) (= other 5)))))
        ((and (= ka 7) (= kb 7)) (symbol=? (literal-of a) (literal-of b)))
        ((or (and (= ka 7) (= kb 2)) (and (= ka 2) (= kb 7))) #t)
        ((or (any-kind? ka) (any-kind? kb)) #t)
        ((and (= ka 8) (= kb 8))
         (or (= depth 0)
             (tagcase a
               (s-pair (a1 d1)
                 (tagcase b
                   (s-pair (a2 d2) (and (overlap? a1 a2 (- depth 1)) (overlap? d1 d2 (- depth 1))))
                   (else y #f)))
               (else y #f))))
        ((and (= ka 6) (= kb 6)) #t)
        ((and (= ka 5) (= kb 5)) #t)
        ((or (= ka 5) (= kb 5)) #f)
        ((and (or (binder-kind? ka) (= ka 2)) (or (binder-kind? kb) (= kb 2))) #t)
        (else #f)))))
;; Whether kind `k` is a binder's, `bvar` or `dvar`; one any syntax may be
;; of, `expr`, `data`, `desc`, `kind` or `defn`.
(define binder-kind? (->* (int) bool) (lambda (k) (or (= k 1) (= k 12))))
(define any-kind? (->* (int) bool)
  (lambda (k) (or (= k 0) (= k 3) (= k 4) (= k 11) (= k 13) (= k 14))))
;; Whether two of `ms` overlap.
(define any-overlap? (->* (stys) bool)
  (lambda (ms)
    (and (not (null? ms))
         (or (any-overlaps-of? (car ms) (cdr ms) 6) (any-overlap? (cdr ms))))))

;; Whether two types are the same, structurally.
(define sty=? (->* (sty sty) bool)
  (lambda (a b)
    (tagcase a
      (s-literal (n) (tagcase b (s-literal (m) (symbol=? n m)) (else y #f)))
      (s-mark (n i) (= i (mark-of b)))
      (s-pair (x y) (tagcase b (s-pair (p q) (and (sty=? x p) (sty=? y q))) (else z #f)))
      (s-import (x p) (tagcase b (s-import (y q) (and (sty=? x y) (bind=? p q))) (else z #f)))
      (s-export (x p) (tagcase b (s-export (y q) (and (sty=? x y) (bind=? p q))) (else z #f)))
      (s-mu (x r p) (tagcase b (s-mu (y q o) (and (= r q) (= p o) (sty=? x y))) (else z #f)))
      (s-var (i) (tagcase b (s-var (j) (= i j)) (else y #f)))
      (s-many (x) (tagcase b (s-many (y) (sty=? x y)) (else z #f)))
      (s-typed (x h) (tagcase b (s-typed (y g) (sty=? x y)) (else z #f)))
      (s-union (ms) (tagcase b (s-union (ns) (all-sty=? ms ns)) (else y #f)))
      (else y (and (or (< (kind-of a) 7) (> (kind-of a) 9)) (= (kind-of a) (kind-of b)))))))
(define all-sty=? (->* (stys stys) bool)
  (lambda (ms ns)
    (if (null? ms)
        (null? ns)
        (and (not (null? ns)) (sty=? (car ms) (car ns)) (all-sty=? (cdr ms) (cdr ns))))))
(define bind=? (->* (bind bind) bool)
  (lambda (p q)
    (tagcase p
      (bind-rib (es) (tagcase q (bind-rib (fs) (entries=? es fs)) (else y #f)))
      (bind-cage (rs) (tagcase q (bind-cage (ss) (rings=? rs ss)) (else y #f)))
      ;; Found, never written in a signature.
      (bind-direct (as) #f)
      (bind-earlier (as) #f)
      (bind-shape (a) (tagcase q (bind-shape (b) (addr=? a b)) (else y #f))))))
(define rings=? (->* (rings rings) bool)
  (lambda (rs ss)
    (if (null? rs)
        (null? ss)
        (and (not (null? ss))
             (tagcase (car rs)
               (ring-rib (es) (tagcase (car ss) (ring-rib (fs) (entries=? es fs)) (else y #f)))
               (ring-at (a) (tagcase (car ss) (ring-at (b) (addr=? a b)) (else y #f)))
               (ring-shape (a) (tagcase (car ss) (ring-shape (b) (addr=? a b)) (else y #f))))
             (rings=? (cdr rs) (cdr ss))))))
(define entries=? (->* (entries entries) bool)
  (lambda (es fs)
    (if (null? es)
        (null? fs)
        (and (not (null? fs))
             (addr=? (extract (car es) 1) (extract (car fs) 1))
             (delta=? (extract (car es) 2) (extract (car fs) 2))
             (entries=? (cdr es) (cdr fs))))))
;; Whether two δs say the same: two macros' binders, by what their
;; signatures write (`bind_same`).
(define delta=? (->* (int int) bool)
  (lambda (d e)
    (or (= d e)
        (and (>= d 100) (>= e 100)
             (string=? (show-syn (syntax-sig-of d)) (show-syn (syntax-sig-of e)))))))
(define addr=? (->* (addr addr) bool)
  (lambda (a b)
    (if (null? a)
        (null? b)
        (and (not (null? b)) (eq? (car a) (car b)) (addr=? (cdr a) (cdr b))))))

;; Whether syntax of type `a` is all of type `b`, binding structure alike:
;; coinductive, as FX-26's recursive types are, each pair a `mu` is of
;; assumed (`assumed`) while it is compared, by structure: the types a `mu`
;; unfolds to are finitely many, so the pairs are (`macros.rs`'s `sub`).
(define-type assumed (listof (tupleof sty sty) acyclic))
(define sub? (->* (sty sty assumed) bool)
  (lambda (a b assumed)
    (if (or (sty=? a b) (and (or (mu? a) (mu? b)) (assumed? a b assumed)))
        #t
        (let ((more (if (or (mu? a) (mu? b)) (the assumed (cons (tuple a b) assumed)) assumed)))
          (tagcase a
            (s-many (x) (sub? x b more))
            (s-typed (x h) (sub? x b more))
            (s-mu (x r p) (sub? (unfold-mu a) b more))
            (s-union (ms) (all-sub? ms b more))
            (else y
              (tagcase b
                (s-many (x) (sub? a x more))
                (s-typed (x h) (sub? a x more))
                (s-mu (x r p) (sub? a (unfold-mu b) more))
                (s-union (ms) (any-sub? a ms more))
                (else z (sub-base? a b more)))))))))
(define mu? (->* (sty) bool) (lambda (t) (tagcase t (s-mu (b r p) #t) (else y #f))))
(define sub-base? (->* (sty sty assumed) bool)
  (lambda (a b more)
    (tagcase a
      (s-import (x p) (tagcase b (s-import (y q) (and (bind=? p q) (sub? x y more))) (else z #f)))
      (s-export (x p) (tagcase b (s-export (y q) (and (bind=? p q) (sub? x y more))) (else z #f)))
      (s-pair (a1 d1)
        (tagcase b (s-pair (a2 d2) (and (sub? a1 a2 more) (sub? d1 d2 more))) (else z #f)))
      (else y (or (and (= (kind-of a) 10) (= (kind-of b) 0)) (sty=? a b))))))
(define assumed? (->* (sty sty assumed) bool)
  (lambda (a b xs)
    (and (not (null? xs))
         (or (and (sty=? a (extract (car xs) 1)) (sty=? b (extract (car xs) 2)))
             (assumed? a b (cdr xs))))))
(define all-sub? (->* (stys sty assumed) bool)
  (lambda (ms b more) (or (null? ms) (and (sub? (car ms) b more) (all-sub? (cdr ms) b more)))))
(define any-sub? (->* (sty stys assumed) bool)
  (lambda (a ms more)
    (and (not (null? ms)) (or (sub? a (car ms) more) (any-sub? a (cdr ms) more)))))
