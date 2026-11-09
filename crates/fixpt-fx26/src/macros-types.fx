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
;; One of a ribcage's: a rib, or the ribcage exported at an address.
(define-datatype ring (ring-rib entries) (ring-at addr))
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
(define-datatype bind (bind-rib entries) (bind-cage rings) (bind-direct atms) (bind-earlier atms))
;; What a typed hole says (`macros.rs`'s `Hole`): its type and its effect,
;; each as written, in a list of one, or none if it is left out.
(define-type hole (tupleof syns-a syns-a))
;; A syntax type. A `mu` is by its number in `mus`, its variable the same;
;; `s-typed`, an `expr` or `bvar` with its type or effect written.
(define-datatype sty
  (s-expr) (s-bvar) (s-id) (s-data) (s-type) (s-label) (s-nil)
  (s-literal symbol) (s-pair sty sty) (s-import sty bind) (s-export sty bind)
  (s-mu int) (s-many sty) (s-union (listof sty acyclic)) (s-typed sty hole)
  ;; An expression that is a lambda, where a form wants one (`letrec`).
  (s-lambda)
  ;; A definition, where a template makes one (the kernel's `begin` of
  ;; them); no part of a signature, for now.
  (s-defn)
  ;; A description's binder; a binder's kind, which names nothing.
  (s-dvar) (s-kind))
(define-type stys (listof sty acyclic))

;; Each `mu`'s body, by its number: the program's, and every file's
;; macros', which refer to them by number.
(define mus (ref (arrayof sty rs) rs) (new (make-array 64 (s-nil))))
(define nmus (ref int rs) (new 0))
(define mu-body (->* (int) sty) (lambda (i) (array-ref (get mus) i)))
;; A new `mu`, its body not yet read: its number.
(define mu-new (->* () int)
  (lambda ()
    (let ((n (get nmus)))
      (begin
        (if (= n (array-length (get mus)))
            (let ((bigger (the (arrayof sty rs) (make-array (* 2 n) (s-nil)))))
              (begin (copy-stys (get mus) bigger 0) (set mus bigger)))
            #u)
        (set nmus (+ n 1))
        n))))
(define copy-stys (->* ((arrayof sty rs) (arrayof sty rs) int) unit)
  (lambda (from to i)
    (if (= i (array-length from))
        #u
        (begin (array-set! to i (array-ref from i)) (copy-stys from to (+ i 1))))))
(define mu-set! (->* (int sty) unit) (lambda (i t) (array-set! (get mus) i t)))

;;; ------------------------------------------------------------ names

;; Whether `name` is a form's, `#%fx`, `#%toplevel` or `define-syntax`: never
;; bound, so never a binder or a variable.
(define reserved? (->* (string) bool)
  (lambda (name)
    (or (string=? name "#%fx") (string=? name "#%toplevel") (string=? name "define-syntax")
        (string=? name "define-syntax-rec")
        (word-in? name (with kernel reserved-words)))))
(define word-in? (->* (string datum) bool)
  (lambda (name ws)
    (and (pair? ws)
         (or (and (symbol? (car ws)) (string=? name (symbol->string (car ws))))
             (word-in? name (cdr ws))))))
;; Whether `name` is a word of descriptions (the kernel's): one read
;; anywhere (`pure`, `heap`, a region constant `@r`, or a name already
;; `#%`'s), or, `head`, one a list's head may be (`subr`, `listof`).
(define desc-word? (->* (string bool) bool)
  (lambda (name head)
    (or (and (> (string-length name) 0) (char=? (string-ref name 0) #\@))
        (and (> (string-length name) 1) (string=? (substring name 0 2) "#%"))
        (word-in? name (with kernel description-words))
        (and head (word-in? name (with kernel description-heads))))))
;; Whether `name` is a type form's head (the kernel's `type-forms`), whose
;; template makes a description.
(define type-form? (->* (string) bool)
  (lambda (name) (word-in? name (with kernel type-forms))))
;; Whether `s` is a name, and a reserved one.
(define reserved-syn? (->* (syn) bool)
  (lambda (s) (and (syn-symbol? s) (reserved? (syn-name s)))))
(define name-in? (->* (symbol names) bool)
  (lambda (n ns) (and (not (null? ns)) (or (symbol=? n (car ns)) (name-in? n (cdr ns))))))

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
;; Whether `i` is one of `is`.
(define int-in? (->* (int (listof int acyclic)) bool)
  (lambda (i is) (and (not (null? is)) (or (= i (car is)) (int-in? i (cdr is))))))

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

;;; ------------------------------------------------------------ syntax

;; Whether `s` is `()`.
(define syn-nil? (->* (syn) bool)
  (lambda (s)
    (tagcase s
      (atom (d a b x) (null? d))
      (lst (items d a b x) (null? items))
      (else y #f))))
;; Whether `s` is a keyword, `#:name`.
(define syn-keyword? (->* (syn) bool)
  (lambda (s) (tagcase s (atom (d a b x) (keyword? d)) (else y #f))))
;; A list's car and cdr, the cdr a list of the rest (or the tail), in a list
;; of two; none if `s` is no pair.
(define split (->* (syn) syns-a)
  (lambda (s)
    (tagcase s
      (lst (items d a b x)
        (if (null? items)
            nil
            (list (car items)
                  (if (null? (cdr items))
                      (atom '() a b x)
                      (lst (cdr items) (if (pair? d) (cdr d) d) a b x)))))
      (dotted (items tail d a b x)
        (list (car items)
              (if (null? (cdr items))
                  tail
                  (dotted (cdr items) tail (if (pair? d) (cdr d) d) a b x))))
      (else y nil))))
;; `d`, a datum, as syntax at no place.
(define datum->syn (->* (datum) syn)
  (lambda (d)
    (if (pair? d)
        (let ((parts (datum-parts d)))
          (if (null? (cdr parts))
              (lst (car parts) d 0 0 0)
              (dotted (car parts) (car (car (cdr parts))) d 0 0 0)))
        (atom d 0 0 0))))
;; A pair's elements as syntax, and its tail if it is not `()`, in a list.
(define datum-parts (->* (datum) (listof syns-a acyclic))
  (lambda (d)
    (letrec ((go (subr (maxeff (read @globals) spin) (datum) syns-a)
               (lambda (x) (if (pair? x) (cons (datum->syn (car x)) (go (cdr x))) nil)))
             (end (subr (maxeff (read @globals) spin) (datum) datum)
               (lambda (x) (if (pair? x) (end (cdr x)) x))))
      (let ((e (end d)))
        (if (null? e)
            (list (go d))
            (list (go d) (the syns-a (list (atom e 0 0 0)))))))))

;; `s` written as the Rust front end's `write_syntax` writes it, for what
;; is said of it.
(define show-syn (->* (syn) string)
  (lambda (s)
    (tagcase s
      (lst (items d a b x) (if (null? items) "()" (string-append "(" (show-each items) ")")))
      (dotted (items tail d a b x)
        (string-append "(" (show-each items) " . " (show-syn tail) ")"))
      (vec (items d a b x) (string-append "#(" (show-each items) ")"))
      (atom (d a b x) (show-datum d)))))
(define show-each (->* (syns-a) string)
  (lambda (xs)
    (cond ((null? xs) "")
          ((null? (cdr xs)) (show-syn (car xs)))
          (else (string-append (show-syn (car xs)) " " (show-each (cdr xs)))))))
(define show-datum (->* (datum) string)
  (lambda (d)
    (cond ((null? d) "()")
          ((symbol? d) (symbol->string d))
          ((keyword? d) (string-append "#:" (symbol->string (keyword->symbol d))))
          ((string? d) (string-append "\"" d "\""))
          ((char? d) (string-append "#\\" (char->string d)))
          ((int? d) (int->string d))
          ((f64? d) (f64->string d))
          ((bool? d) (if d "#t" "#f"))
          (else "…"))))

;;; ------------------------------------------------------------ reading

;; Syntax type `s`, read: `named`'s names (the kernel's abbreviations), and
;; the `mu` variables in scope, innermost first.
(define-type named (listof (tupleof symbol sty) acyclic))
(define-type mu-scope (listof (tupleof symbol int) acyclic))
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
            (read-seq-list fail (proper-items s) named scope))
           ((or (string=? head "import") (string=? head "export"))
            (let ((args (proper-items s)))
              (if (= (len args) 3)
                  (let ((body (read-sty fail (nth args 1) named scope))
                        (b (read-bind fail (nth args 2))))
                    (if (string=? head "import") (s-import body b) (s-export body b)))
                  (read-pair fail s parts named scope))))
           ((string=? head "mu") (read-mu fail s named scope))
           ((string=? head "union")
            (let ((ms (read-each fail (cdr (proper-items s)) named scope)))
              (begin (if (any-overlap? ms)
                         (fail-at fail (string-append "a syntax type: a `union`'s members must be "
                                                      "told apart by their shapes in the source "
                                                      "(an `expr` may be anything)")
                                  s)
                         #u)
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
            (if (syn-symbol? (nth (proper-items s) 1))
                (s-literal (syn-symbol (nth (proper-items s) 1)))
                (begin (fail-at fail "a syntax type: `(literal name)`" s) (s-nil))))
           (else (read-pair fail s parts named scope))))))))
;; The items of a list type ending in `σ ...`: the last `σ` repeated
;; (`macros.rs`'s `seq`), after the ones before it, each once.
(define read-seq-list (->* (fails syns-a named mu-scope) sty)
  (lambda (fail items named scope)
    (if (null? (cdr (cdr items)))
        (seq-type (read-sty fail (car items) named scope))
        (let ((first (read-sty fail (car items) named scope)))
          (s-pair first (read-seq-list fail (cdr items) named scope))))))
;; `(elem ...)`: `(mu l (union () (elem . l)))`, and if `elem` exports,
;; each element's export together, as a `let`'s bindings do; a binder
;; alone, `bvar` or `dvar`, exports itself.
(define seq-type (->* (sty) sty)
  (lambda (elem0)
    (let* ((elem (tagcase elem0
                   (s-bvar () (s-export elem0 (bind-rib (list (tuple (the addr nil) 1)))))
                   (s-dvar () (s-export elem0 (bind-rib (list (tuple (the addr nil) 4)))))
                   (else y elem0)))
           (id (mu-new)) (pair (s-pair elem (s-mu id))))
      (begin
        (mu-set! id (s-union (tagcase elem
                               (s-export (b x)
                                 (list (s-export (s-nil) (bind-rib nil))
                                       (s-export pair (bind-rib (list (tuple (the addr (list #t)) 2)
                                                                      (tuple (the addr (list #f))
                                                                             2))))))
                               (else y (list (s-nil) pair)))))
        (s-mu id)))))
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
            (s-mu (id)
              (tagcase (mu-body id) (s-union (ms) (seq-members ms id nil #f)) (else y nil)))
            (else y nil))
          caged))))
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
      (s-mu (id) (tagcase (mu-body id) (s-union (ms) (cage-members ms id nil #f)) (else y nil)))
      (else y nil))))
(define cage-members (->* (stys int stys bool) stys)
  (lambda (ms id es none)
    (if (null? ms)
        (if (and none (not (null? es)) (null? (cdr es))) es nil)
        (tagcase (car ms)
          (s-export (core b)
            (tagcase b
              (bind-cage (rings)
                (cond ((and (null? rings) (= (kind-of core) 6)) (cage-members (cdr ms) id es #t))
                      ((null? rings) nil)
                      (else
                       (let ((e (cage-pair core rings id)))
                         (if (null? e) nil (cage-members (cdr ms) id (cons (car e) es) none))))))
              (else y nil)))
          (else y nil)))))
;; Pair type `core` of a ribcage's list `id`, which exports `rings`: its
;; element, with what it exports, in a list of one; none if it is not one.
(define cage-pair (->* (sty rings int) stys)
  (lambda (core rings id)
    (tagcase core
      (s-pair (a d)
        (tagcase d
          (s-import (r inner)
            (if (and (tagcase r (s-mu (j) (= j id)) (else y #f)) (not (null? (cdr rings)))
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
                          nil))))
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
(define seq-members (->* (stys int stys bool) stys)
  (lambda (ms id es none)
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
                ((= (kind-of core) 6) (seq-members (cdr ms) id es #t))
                (else
                 (tagcase core
                   (s-pair (a d)
                     (if (seq-rest? m d id)
                         (seq-members (cdr ms) id (cons (with-own a (car own)) es) none)
                         nil))
                   (else y nil))))))))
;; Whether `d`, member `m`'s pair's rest, is list `id` itself, perhaps in
;; the scope of what the pair's element binds (a `lambda`'s parameters,
;; each in the later ones' types: `seq-scoped?`).
(define seq-rest? (->* (sty sty int) bool)
  (lambda (m d id)
    (tagcase d
      (s-mu (j) (= j id))
      (s-import (r b)
        (and (tagcase r (s-mu (j) (= j id)) (else y #f))
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
      (s-mu (id) (tagcase (mu-body id) (s-union (ms) (rest-imported? ms)) (else y #f)))
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
            (s-mu mu)
            (let ((t (named-of n named)))
              (if (null? t)
                  (case n
                    ((expr) (s-expr)) ((bvar) (s-bvar)) ((id) (s-id)) ((data) (s-data))
                    ((lambda) (s-lambda))
                    ((type) (s-type)) ((label) (s-label)) ((dvar) (s-dvar)) ((kind) (s-kind))
                    (else
                     (begin
                       (fail-at fail (string-append "a syntax type: `" (symbol->string n) "` is "
                                                    "none (`expr`, `bvar`, `id`, `data`, `type`, "
                                                    "`label`, `lambda`, `dvar`, `kind`, or a "
                                                    "`mu`'s variable)")
                                s)
                       (s-nil))))
                  (car t))))))))
(define scope-of (->* (symbol mu-scope) int)
  (lambda (n scope)
    (cond ((null? scope) -1)
          ((symbol=? n (extract (car scope) 1)) (extract (car scope) 2))
          (else (scope-of n (cdr scope))))))
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
          (let* ((id (mu-new))
                 (body (read-sty fail (nth args 2) named
                                 (cons (tuple (syn-symbol (nth args 1)) id) scope))))
            (begin
              (if (guarded? body id)
                  #u
                  (fail-at fail (string-append "a syntax type: a `mu`'s variable is used where no "
                                               "pair is around it (Herman's types are "
                                               "contractive)")
                           s))
              (mu-set! id body)
              (s-mu id)))
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
(define read-delta (->* (fails syn) int)
  (lambda (fail d)
    (let ((n (if (syn-symbol? d) (syn-name d) "")))
      (cond ((string=? n "none") 0) ((string=? n "var") 1) ((string=? n "rib") 2)
            ((string=? n "env") 3) ((string=? n "dvar") 4) ((string=? n "place") 5)
            (else (begin (fail-at fail "δ is `none`, `var`, `dvar`, `place`, `rib` or `env`" d)
                         0))))))
;; An address, `A`s and `D`s read right to left, or `()`, none: its steps,
;; first first.
(define read-addr (->* (fails syn) addr)
  (lambda (fail a)
    (let ((name (if (syn-symbol? a) (syn-name a) "")))
      (cond
        ((syn-nil? a) nil)
        ((and (> (string-length name) 0) (a-or-d? name 0)) (steps name 0 nil))
        (else
         (begin (fail-at fail (string-append "an address is a word of `A` (car) and `D` (cdr), "
                                             "read right to left")
                         a)
                (the addr nil)))))))
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
(define kernel-read (ref (tupleof named named) rs) (new (tuple (the named nil) (the named nil))))
(define kernel-sigs (->* (fails) named)
  (lambda (fail) (extract (kernel-tables fail) 1)))
(define kernel-definitions (->* (fails) named)
  (lambda (fail) (extract (kernel-tables fail) 2)))
(define kernel-tables (->* (fails) (tupleof named named))
  (lambda (fail)
    (begin
      (if (null? (extract (get kernel-read) 1))
          (set kernel-read (read-kernel fail (proper-items (datum->syn (with kernel kernel-forms)))
                                        (list (tuple 'defn (s-defn))) nil nil))
          #u)
      (get kernel-read))))
(define read-kernel (->* (fails syns-a named named named) (tupleof named named))
  (lambda (fail fs named out defs)
    (if (null? fs)
        (tuple out defs)
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
      (s-mu (id) (unfold (mu-body id)))
      (else y t))))
;; Whether `t` uses `mu` `id`'s variable only under a pair.
(define guarded? (->* (sty int) bool)
  (lambda (t id)
    (tagcase t
      (s-mu (j) (not (= j id)))
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
;; lambda, 11 defn, 12 dvar, 13 kind.
(define kind-of (->* (sty) int)
  (lambda (t)
    (tagcase t
      (s-expr () 0) (s-bvar () 1) (s-id () 2) (s-data () 3) (s-type () 4) (s-label () 5)
      (s-nil () 6) (s-literal (n) 7) (s-pair (a d) 8) (s-lambda () 10) (s-defn () 11)
      (s-dvar () 12) (s-kind () 13) (else y 9))))
;; Whether `k` is a kind of no parts: one of what `(Expr | Id | Data | Type
;; | Label | Bvar | Dvar | Kind | Lambda | Defn)` names in `macros.rs`.
(define simple-kind? (->* (int) bool) (lambda (k) (or (< k 6) (> k 9))))
(define literal-of (->* (sty) symbol)
  (lambda (t) (tagcase t (s-literal (n) n) (else y (string->symbol "")))))
(define overlap-base? (->* (sty sty int) bool)
  (lambda (a b depth)
    (let ((ka (kind-of a)) (kb (kind-of b)))
      (cond
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
;; of, `expr`, `data`, `type`, `kind` or `defn`.
(define binder-kind? (->* (int) bool) (lambda (k) (or (= k 1) (= k 12))))
(define any-kind? (->* (int) bool)
  (lambda (k) (or (= k 0) (= k 3) (= k 4) (= k 11) (= k 13))))
;; Whether two of `ms` overlap.
(define any-overlap? (->* (stys) bool)
  (lambda (ms)
    (and (not (null? ms))
         (or (any-overlaps-of? (car ms) (cdr ms) 6) (any-overlap? (cdr ms))))))

;; Whether `s` has the shape of `t`, in `mode` (0 a pattern, 1 a template,
;; 2 a use): a pattern variable in a template (`pvar?` says 1 for a name's,
;; 2 for another's, 0 for none) fits anything but, if it is a name, a
;; list's shape; any name in a pattern fits anything.
(define fits? (->* (sty syn int (subr pure (symbol) int)) bool)
  (lambda (t s mode pvar?)
    (let ((u (unfold t)) (x (if (= mode 2) (the syns-a nil) (ellipsis-of s))))
      (if (not (null? x))
          ;; `(p ...)`, where a list of elements `p` fits may be.
          (let ((e (seq-elem (peel t)))) (and (not (null? e)) (fits? (car e) (car x) mode pvar?)))
      (if (and (syn-symbol? s)
               (or (and (= mode 0) (not (= (kind-of u) 7)) (not (string=? (syn-name s) "_"))
                        (not (string=? (syn-name s) "...")))
                   (and (= mode 1) (> (pvar? (syn-symbol s)) 0)
                        (not (and (= (pvar? (syn-symbol s)) 1)
                                  (or (= (kind-of u) 8) (= (kind-of u) 6) (= (kind-of u) 10)))))))
          #t
          (tagcase u
            (s-union (ms) (any-fits? ms s mode pvar?))
            (s-pair (a d)
              (let ((parts (split s)))
                (and (not (null? parts))
                     (fits? a (car parts) mode pvar?) (fits? d (nth parts 1) mode pvar?))))
            (s-nil () (syn-nil? s))
            (s-literal (n) (and (syn-symbol? s) (symbol=? (syn-symbol s) n)))
            (s-bvar () (and (syn-symbol? s) (not (reserved-syn? s))))
            (s-dvar () (and (syn-symbol? s) (not (reserved-syn? s))))
            (s-id () (syn-symbol? s))
            (s-label () (or (syn-keyword? s) (and (= mode 2) (syn-symbol? s))))
            (s-expr () (and (not (reserved-syn? s)) (not (syn-nil? s))))
            (s-lambda () (lambda-shaped? s))
            (s-defn () (not (null? (split s))))
            (else y #t)))))))
(define any-fits? (->* (stys syn int (subr pure (symbol) int)) bool)
  (lambda (ms s mode pvar?)
    (and (not (null? ms)) (or (fits? (car ms) s mode pvar?) (any-fits? (cdr ms) s mode pvar?)))))

;; Whether two types are the same, structurally (a `mu` by its number).
(define sty=? (->* (sty sty) bool)
  (lambda (a b)
    (tagcase a
      (s-literal (n) (tagcase b (s-literal (m) (symbol=? n m)) (else y #f)))
      (s-pair (x y) (tagcase b (s-pair (p q) (and (sty=? x p) (sty=? y q))) (else z #f)))
      (s-import (x p) (tagcase b (s-import (y q) (and (sty=? x y) (bind=? p q))) (else z #f)))
      (s-export (x p) (tagcase b (s-export (y q) (and (sty=? x y) (bind=? p q))) (else z #f)))
      (s-mu (i) (tagcase b (s-mu (j) (= i j)) (else y #f)))
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
      (bind-earlier (as) #f))))
(define rings=? (->* (rings rings) bool)
  (lambda (rs ss)
    (if (null? rs)
        (null? ss)
        (and (not (null? ss))
             (tagcase (car rs)
               (ring-rib (es) (tagcase (car ss) (ring-rib (fs) (entries=? es fs)) (else y #f)))
               (ring-at (a) (tagcase (car ss) (ring-at (b) (addr=? a b)) (else y #f))))
             (rings=? (cdr rs) (cdr ss))))))
(define entries=? (->* (entries entries) bool)
  (lambda (es fs)
    (if (null? es)
        (null? fs)
        (and (not (null? fs))
             (addr=? (extract (car es) 1) (extract (car fs) 1))
             (= (extract (car es) 2) (extract (car fs) 2))
             (entries=? (cdr es) (cdr fs))))))
(define addr=? (->* (addr addr) bool)
  (lambda (a b)
    (if (null? a)
        (null? b)
        (and (not (null? b)) (eq? (car a) (car b)) (addr=? (cdr a) (cdr b))))))

;; Whether syntax of type `a` is all of type `b`, binding structure alike:
;; coinductive, as FX-26's recursive types are, each pair compared assumed
;; (`assumed`) while it is, by structure.
(define-type assumed (listof (tupleof sty sty) acyclic))
(define sub? (->* (sty sty assumed) bool)
  (lambda (a b assumed)
    (if (or (sty=? a b) (assumed? a b assumed))
        #t
        (let ((more (the assumed (cons (tuple a b) assumed))))
          (tagcase a
            (s-many (x) (sub? x b more))
            (s-typed (x h) (sub? x b more))
            (s-mu (i) (sub? (mu-body i) b more))
            (s-union (ms) (all-sub? ms b more))
            (else y
              (tagcase b
                (s-many (x) (sub? a x more))
                (s-typed (x h) (sub? a x more))
                (s-mu (j) (sub? a (mu-body j) more))
                (s-union (ms) (any-sub? a ms more))
                (else z (sub-base? a b more)))))))))
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
;; A signature's `(-> σ made)`: `σ`, and what it makes, 0 an expression,
;; `expr`, 1 definitions, `defn`, 2 a description, `type`; else itself, an
;; expression's.
(define signature-made (->* (fails syn) (tupleof syn int))
  (lambda (fail s)
    (let ((items (proper-items s)))
      (if (and (= (len items) 3) (syn-symbol? (car items)) (string=? (syn-name (car items)) "->"))
          (let ((made (if (syn-symbol? (nth items 2)) (syn-name (nth items 2)) "")))
            (cond ((string=? made "defn") (tuple (nth items 1) 1))
                  ((string=? made "type") (tuple (nth items 1) 2))
                  ((string=? made "expr") (tuple (nth items 1) 0))
                  (else (begin (fail-at fail (string-append "a signature `(-> σ made)` makes "
                                                            "`expr`, `defn` or `type`")
                                        (nth items 2))
                               (tuple s 0)))))
          (tuple s 0)))))
