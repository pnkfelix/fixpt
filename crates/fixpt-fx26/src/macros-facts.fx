;;; Typed hygienic macros, in FX-26: a signature in shapes and facts
;;; (`typed-macros.md`, "Decided: signatures in shapes and facts, notation
;;; C revived") elaborated to Herman's form, `(macro/addressed σ made)`,
;;; which the expander reads (`macros/contract.rs`, the same, syntax to
;;; syntax). Part of the expander: loaded by `macros-files.fx`, and loading
;;; `macros-exports.fx`, so that every part sees one instance of each.

(module-parameters ((rs region) (re region) (rm region) (rc region) (rp region)))
(define exports-module ((proj (load-module "fx26:macros-exports.fx") rs re rm rc rp)))
(define align-module (with exports-module align-module))
(define types-module (with align-module types-module))
(define parser-module (with types-module parser-module))
(define reader-types (with parser-module reader-types))
(import reader-types atom lst dotted (type syn))
(import parser-module syn-start syn-end syn-symbol? syn-name syn-symbol syn-datums syn->datum len
        nth mk-list mk-symbol (type syns-a names))
(import types-module fail-at split syn-nil? syn-keyword? proper-items show-syn (type fails))

;; What a labelled part gives a `bind` or an `export` (`contract.rs`'s
;; `Gives`): 0 nothing, 1 a value's binder, 2 a description's, 3 a place's,
;; 4 a rib, 5 a ribcage.
;; A label: its name; 0 here, or 1 a repeated element's; its path (here),
;; or the list's (repeated); its path in the element; what it gives.
(define-type steps (listof bool acyclic))
(define-type label (tupleof symbol int steps steps int))
(define-type labels (listof label acyclic))
;; The named shapes: name, definition, what each exports; those being
;; written, innermost first.
(define named (ref (listof (tupleof symbol syn int) acyclic) rs) (new nil))
(define open (ref names rs) (new nil))

;; Whether signature `s` is one in shapes and facts: `(macro SHAPE …)`, its
;; shape `(_ …)` or `(letrec-shape …)`.
(define contract? (->* (syn) bool)
  (lambda (s)
    (let ((items (proper-items s)))
      (and (>= (len items) 3) (head-is? s "macro")
           (or (head-is? (nth items 1) "_") (head-is? (nth items 1) "letrec-shape"))))))
(define head-is? (->* (syn string) bool)
  (lambda (s h)
    (let ((ps (split s)))
      (and (not (null? ps)) (syn-symbol? (car ps)) (string=? (syn-name (car ps)) h)))))
(define sym-is? (->* (syn string) bool)
  (lambda (s n) (and (syn-symbol? s) (string=? (syn-name s) n))))

;; Signature `s`, in shapes and facts, as Herman's: `(macro/addressed σ made)`.
(define elaborated (->* (fails syn) syn)
  (lambda (fail s)
    (let* ((items (proper-items s)) (a (syn-start s)) (b (syn-end s))
           (saved (get named))
           (top (begin (set named nil) (shape fail (nth items 1))))
           (parts (list-parts top)))
      (if (or (null? (extract parts 1)) (not (sym-is? (car (extract parts 1)) "_")))
          (begin (fail-at fail (string-append "a signature's shape is `(_ part …)`, as a "
                                              "`syntax-rules` pattern is")
                          top)
                 s)
          (let* ((operands (list-with (cdr (extract parts 1)) (extract parts 2) a b))
                 (r (tree fail operands nil nil))
                 ;; What a use defines first: each element's export for a `(v ...)`
                 ;; there before the facts'.
                 (m (made-of fail (nth items 2) (extract r 2)))
                 (sigma (facts fail (extract r 1) (cdr (cdr (cdr items))) (extract r 2) #t
                               (extract m 2)))
                 (made (extract m 1))
                 (out (mk-list (list (mk-symbol "macro/addressed" a b) sigma made) a b)))
            (begin (set named saved) out))))))
;; A list's parts, and its tail (none, or one).
(define list-parts (->* (syn) (tupleof syns-a syns-a))
  (lambda (s)
    (tagcase s
      (lst (items d a b x) (tuple items (the syns-a nil)))
      (dotted (items tail d a b x) (tuple items (list tail)))
      (else y (tuple (the syns-a nil) (the syns-a nil))))))
;; Items `xs` with tail `t` (none, or one) as one list: a tail that is a
;; list joined to it.
(define list-with (->* (syns-a syns-a int int) syn)
  (lambda (xs t a b)
    (cond ((null? t) (mk-list xs a b))
          ;; No items: the tail itself.
          ((null? xs) (car t))
          (else
           (tagcase (car t)
             (lst (ys d c e x) (mk-list (append xs ys) a b))
             (dotted (ys u d c e x) (list-with (append xs ys) (list u) a b))
             (else y (if (syn-nil? (car t))
                         (mk-list xs a b)
                         (dotted xs (car t) (datum-dotted (syn-datums xs) (syn->datum (car t)))
                                 a b 0))))))))

;;; ------------------------------------------------------------ shapes

;; `SHAPE`: a `letrec-shape`'s names noted, its top given back.
(define shape-usage string
  (string-append "`(letrec-shape ((name node) …) (_ part …))`, a node `(node-name tree fact "
                 "…)` or `(union node …)`"))
(define shape (->* (fails syn) syn)
  (lambda (fail s)
    (if (not (head-is? s "letrec-shape"))
        s
        (let ((items (proper-items s)))
          (if (not (= (len items) 3))
              (begin (fail-at fail shape-usage s) s)
              (begin (note-named fail (proper-items (nth items 1)))
                     (set named (named-gives fail (get named)))
                     (nth items 2)))))))
(define note-named (->* (fails syns-a) unit)
  (lambda (fail ds)
    (if (null? ds)
        #u
        (let ((d (proper-items (car ds))))
          (cond ((or (not (= (len d) 2)) (not (syn-symbol? (car d))))
                 (fail-at fail shape-usage (car ds)))
                ((not (null? (named-of (syn-symbol (car d)) (get named))))
                 (fail-at fail (string-append "`" (syn-name (car d)) "` is a shape's name twice")
                          (car d)))
                (else (begin (set named (cons (tuple (syn-symbol (car d)) (nth d 1) 0)
                                              (get named)))
                             (note-named fail (cdr ds)))))))))
(define named-of (->* (symbol (listof (tupleof symbol syn int) acyclic))
                      (listof (tupleof symbol syn int) acyclic))
  (lambda (n xs)
    (cond ((null? xs) nil) ((symbol=? n (extract (car xs) 1)) (list (car xs)))
          (else (named-of n (cdr xs))))))
(define named-gives (->* (fails (listof (tupleof symbol syn int) acyclic))
                         (listof (tupleof symbol syn int) acyclic))
  (lambda (fail xs)
    (if (null? xs)
        nil
        (cons (tuple (extract (car xs) 1) (extract (car xs) 2)
                     (def-gives fail (extract (car xs) 2)))
              (named-gives fail (cdr xs))))))
;; What a node, or each member of a union, exports: 4 an `export`'s rib, 5
;; an `export*`'s ribcage, 0 none.
(define def-gives (->* (fails syn) int)
  (lambda (fail def)
    (let ((items (proper-items def)))
      (if (head-is? def "union")
          (members-gives fail (cdr items) 0)
          (node-gives (if (> (len items) 2) (cdr (cdr items)) nil) 0)))))
(define members-gives (->* (fails syns-a int) int)
  (lambda (fail ms g)
    (if (null? ms)
        g
        (let ((mg (def-gives fail (car ms))))
          (cond ((= mg 0) (members-gives fail (cdr ms) g))
                ((and (not (= g 0)) (not (= g mg)))
                 (begin (fail-at fail (string-append "a union's members export a rib and a "
                                                     "ribcage, `export` and `export*`: one kind")
                                 (car ms))
                        g))
                (else (members-gives fail (cdr ms) mg)))))))
(define node-gives (->* (syns-a int) int)
  (lambda (fs g)
    (cond ((null? fs) g)
          ((head-is? (car fs) "export") (node-gives (cdr fs) 4))
          ((head-is? (car fs) "export*") (node-gives (cdr fs) 5))
          (else (node-gives (cdr fs) g)))))

;;; ------------------------------------------------------------ trees

;; Tree `s` at `path` from its region's root, as a syntax type, with the
;; labels its labelled parts add to `ls` (`contract.rs`'s `tree`).
(define tree (->* (fails syn steps labels) (tupleof syn labels))
  (lambda (fail s path ls)
    (cond ((form? s) (form fail s path ls))
          ((syn-nil? s) (tuple s ls))
          ((not (null? (split s)))
           (let* ((ps (list-parts s)) (r (parts fail (extract ps 1) (extract ps 2) path ls nil)))
             (tuple (list-with (extract r 1) (extract r 2) (syn-start s) (syn-end s))
                    (extract r 3))))
          ((and (syn-symbol? s) (not (null? (named-of (syn-symbol s) (get named)))))
           (tuple (reference fail s (syn-symbol s)) ls))
          ((sym-is? s "place") (tuple (mk-symbol "dvar" (syn-start s) (syn-end s)) ls))
          (else (tuple s ls)))))
;; A list's parts `xs` (its tail `t`) at `p`, onto `out` (the last first):
;; the syntax types, the tail, the labels.
(define parts (->* (fails syns-a syns-a steps labels syns-a) (tupleof syns-a syns-a labels))
  (lambda (fail xs t p ls out)
    (cond
      ((null? xs)
       (if (null? t)
           (tuple (reverse out) (the syns-a nil) ls)
           (let ((r (tree fail (car t) p ls)))
             (tuple (reverse out) (list (extract r 1)) (extract r 2)))))
      ;; A tail labelled: `name @ . σ`.
      ((and (= (len xs) 2) (not (null? t)) (sym-is? (nth xs 1) "@"))
       (let* ((ls2 (labelled fail (car xs) (tuple 0 p (the steps nil) (gives (car t))) ls))
              (r (tree fail (car t) p ls2)))
         (tuple (reverse out) (list (extract r 1)) (extract r 2))))
      (else
       (let* ((lab (and (> (len xs) 2) (sym-is? (nth xs 1) "@")))
              (used (if lab 3 1))
              (t1 (if lab (nth xs 2) (car xs)))
              (rest (list-drop xs used))
              (ap (append p (the steps (list #t)))))
         (if (and (not (null? rest)) (sym-is? (car rest) "..."))
             ;; `part ...`: the element a region of its own, its labels the
             ;; list's, repeated, the list at `p`.
             (let* ((r (tree fail t1 nil nil))
                    (inner (if lab
                               (labelled fail (car xs) (tuple 0 (the steps nil) (the steps nil)
                                                              (gives t1))
                                         (extract r 2))
                               (extract r 2)))
                    (ls2 (repeated-labels fail inner p ls t1)))
               (begin
                 (if (or (not (null? (cdr rest))) (not (null? t)))
                     (fail-at fail "`...` comes last in a list" (car rest))
                     #u)
                 (tuple (reverse (cons (car rest) (cons (extract r 1) out))) (the syns-a nil) ls2)))
             (let* ((ls2 (if lab (labelled fail (car xs) (tuple 0 ap (the steps nil) (gives t1)) ls)
                             ls))
                    (r (tree fail t1 ap ls2)))
               (parts fail rest t (append p (the steps (list #f))) (extract r 2)
                      (cons (extract r 1) out)))))))))
(define list-drop (->* (syns-a int) syns-a)
  (lambda (xs k) (if (or (= k 0) (null? xs)) xs (list-drop (cdr xs) (- k 1)))))
;; Each label of a repeated element, the list's at `p`, onto `ls`.
(define repeated-labels (->* (fails labels steps labels syn) labels)
  (lambda (fail inner p ls t)
    (cond ((null? inner) ls)
          ((= (extract (car inner) 2) 1)
           (begin (fail-at fail "a repeated part in a repeated part: not yet" t) ls))
          (else
           (repeated-labels fail (cdr inner) p
                            (labelled-name fail (extract (car inner) 1)
                                           (tuple 1 p (extract (car inner) 3)
                                                  (extract (car inner) 5))
                                           ls t)
                            t)))))
;; Label `n` (a name), of kind, paths and gives `l`, onto `ls`.
(define labelled (->* (fails syn (tupleof int steps steps int) labels) labels)
  (lambda (fail n l ls)
    (if (not (syn-symbol? n))
        (begin (fail-at fail "a part's label is a name, `name @ σ`" n) ls)
        (labelled-name fail (syn-symbol n) l ls n))))
(define labelled-name (->* (fails symbol (tupleof int steps steps int) labels syn) labels)
  (lambda (fail n l ls at)
    (if (not (null? (label-of n ls)))
        (begin (fail-at fail (string-append "`" (symbol->string n) "` labels two parts") at) ls)
        (cons (tuple n (extract l 1) (extract l 2) (extract l 3) (extract l 4)) ls))))
(define label-of (->* (symbol labels) labels)
  (lambda (n ls)
    (cond ((null? ls) nil) ((symbol=? n (extract (car ls) 1)) (list (car ls)))
          (else (label-of n (cdr ls))))))
;; Whether list `s` is a syntax type's form, not a list of parts.
(define form? (->* (syn) bool)
  (lambda (s)
    (let ((items (proper-items s)))
      (or (head-is? s "many") (head-is? s "literal") (head-is? s "trailmark") (head-is? s "oneof")
          (head-is? s "union")
          (and (or (head-is? s "expr") (head-is? s "bvar") (head-is? s "lambda"))
               (> (len items) 1) (syn-keyword? (nth items 1)))))))
;; A syntax type's form: `(many σ)` its part a tree; a union's members each a
;; region with no labels; the rest as written.
(define form (->* (fails syn steps labels) (tupleof syn labels))
  (lambda (fail s path ls)
    (let ((items (proper-items s)) (a (syn-start s)) (b (syn-end s)))
      (cond ((and (head-is? s "many") (= (len items) 2))
             (let ((r (tree fail (nth items 1) path ls)))
               (tuple (mk-list (list (car items) (extract r 1)) a b) (extract r 2))))
            ((or (head-is? s "union") (head-is? s "oneof"))
             (tuple (mk-list (cons (mk-symbol "oneof" a b) (unlabelled-members fail (cdr items)))
                             a b)
                    ls))
            (else (tuple s ls))))))
(define unlabelled-members (->* (fails syns-a) syns-a)
  (lambda (fail ms)
    (if (null? ms)
        nil
        (let ((r (tree fail (car ms) nil nil)))
          (begin
            (if (null? (extract r 2))
                #u
                (fail-at fail (string-append "a label in a union's member that has no name: name "
                                             "the member, a node in a `letrec-shape`, whose facts "
                                             "may say it")
                         (car ms)))
            (cons (extract r 1) (unlabelled-members fail (cdr ms))))))))
;; What a part of type `t` gives: a binder, itself; a part of a named shape,
;; what its node exports.
(define gives (->* (syn) int)
  (lambda (t)
    (cond ((sym-is? t "bvar") 1) ((sym-is? t "dvar") 2) ((sym-is? t "place") 3)
          ((and (syn-symbol? t) (not (null? (named-of (syn-symbol t) (get named)))))
           (extract (car (named-of (syn-symbol t) (get named))) 3))
          ((head-is? t "bvar") 1)
          (else 0))))
;; A named shape referred to: its node, or union, written once, `(mu name
;; σ)`; inside its own writing, the `mu`'s variable.
(define reference (->* (fails syn symbol) syn)
  (lambda (fail s n)
    (if (name-in? n (get open))
        s
        (let* ((pushed (set open (cons n (get open))))
               (r (def-sigma fail (extract (car (named-of n (get named))) 2)))
               (popped (set open (cdr (get open)))))
          (mk-list (list (mk-symbol "mu" (syn-start s) (syn-end s)) s r)
                   (syn-start s) (syn-end s))))))
(define name-in? (->* (symbol names) bool)
  (lambda (n ns) (and (not (null? ns)) (or (symbol=? n (car ns)) (name-in? n (cdr ns))))))
;; A node's or a union's syntax type: each member a region of its own, its
;; facts its annotations; a union's members exporting one kind, one that
;; says none an empty one.
(define def-sigma (->* (fails syn) syn)
  (lambda (fail def)
    (if (head-is? def "union")
        (let ((kind (def-gives fail def)) (a (syn-start def)) (b (syn-end def)))
          (mk-list (cons (mk-symbol "oneof" a b) (members-sigma fail (cdr (proper-items def)) kind))
                   a b))
        (node-sigma fail def))))
(define members-sigma (->* (fails syns-a int) syns-a)
  (lambda (fail ms kind)
    (if (null? ms)
        nil
        (let* ((t (node-sigma fail (car ms))) (a (syn-start (car ms))) (b (syn-end (car ms)))
               (t2 (if (and (not (= kind 0)) (= (def-gives fail (car ms)) 0))
                       (mk-list (list (mk-symbol "export" a b) t
                                      (mk-list (list (mk-symbol (if (= kind 5) "cage" "rho") a b))
                                               a b))
                                a b)
                       t)))
          (cons t2 (members-sigma fail (cdr ms) kind))))))
(define node-sigma (->* (fails syn) syn)
  (lambda (fail node)
    (let ((items (proper-items node)))
      (if (< (len items) 2)
          (begin (fail-at fail "a node is `(node-name tree fact …)`" node) node)
          (let ((r (tree fail (nth items 1) nil nil)))
            (facts fail (extract r 1) (cdr (cdr items)) (extract r 2) #f nil))))))

;;; ------------------------------------------------------------ facts

;; Facts `fs` of a region whose labels are `ls`, on its syntax type `sigma`
;; (`contract.rs`'s `facts`): each `bind` an import on the part it names,
;; `export`s and `export*`s the region's export (none at a signature's top); `pre`, what
;; repeated elements export for what a use defines, first.
(define-type adds (listof (tupleof steps syn) acyclic))
(define facts (->* (fails syn syns-a labels bool adds) syn)
  (lambda (fail sigma fs ls top pre)
    (let* ((e (each-facts fail fs ls nil nil))
           (r (facts-each fail (extract e 1) ls top nil nil nil nil (reverse pre)))
           (imports (extract r 1)) (rib (extract r 2)) (rings (extract r 3)) (elems (extract r 5))
           (a (syn-start sigma)) (b (syn-end sigma))
           ;; Each repetition's facts, inside its element; then each element
           ;; exporting what a fact says of its labels.
           (s0 (each-annotated fail sigma (reverse (extract e 2))))
           (s1 (elements-annotated fail s0 (reverse elems)))
           (s2 (imports-annotated fail s1 (reverse imports))))
      (cond ((and (not (null? rib)) (not (null? (extract r 4))))
             (begin (fail-at fail (string-append "a node exports one level, `export`, or nested "
                                                 "ones, `export*`, not both")
                             sigma)
                    s2))
            ((not (null? rib))
             (annotate fail s2 nil "export"
                       (mk-list (cons (mk-symbol "rho" a b) (reverse rib)) a b)))
            ((not (null? (extract r 4)))
             (annotate fail s2 nil "export" (mk-list (cons (mk-symbol "cage" a b) rings) a b)))
            (else s2)))))
;; Facts `fs` parted: those of the node, and each repetition's, `(bind v in
;; e) ...` (by the list's path, `e`'s in the element, the binding; the last
;; first), as `contract.rs`'s `facts` parts them.
(define-type eaches (listof (tupleof steps steps syn) acyclic))
(define each-facts (->* (fails syns-a labels syns-a eaches) (tupleof syns-a eaches))
  (lambda (fail fs ls out each)
    (cond ((null? fs) (tuple (reverse out) each))
          ((and (not (null? (cdr fs))) (sym-is? (car (cdr fs)) "..."))
           (begin
             (if (and (not (null? (cdr (cdr fs)))) (sym-is? (car (cdr (cdr fs))) "..."))
                 (fail-at fail "a fact under more than one `...`: not yet" (car (cdr (cdr fs))))
                 #u)
             (let ((e (each-bound fail (car fs) ls)))
               (each-facts fail (cdr (cdr fs)) ls out (if (null? e) each (cons (car e) each))))))
          (else (each-facts fail (cdr fs) ls (cons (car fs) out) each)))))
;; A fact under `...`, `(bind v in e) ...`, each repetition's: `v` and `e`
;; labels of one list's element, each the repetition's own; the list's
;; path, `e`'s in the element, and what it imports there, addressed from the
;; element's root, in a list of one (`contract.rs`'s `each_bound`). One that
;; names what is outside its repetition needs an import from an outer
;; region's root: not yet (§289).
(define each-bound (->* (fails syn labels) eaches)
  (lambda (fail f ls)
    (let ((items (proper-items f)) (a (syn-start f)) (b (syn-end f))
          (outside (string-append "a fact under `...` that names what is outside its "
                                  "repetition: not yet (TODO §289)")))
      (if (not (and (head-is? f "bind") (= (len items) 4) (sym-is? (nth items 2) "in")))
          (begin (fail-at fail (string-append "a fact under `...` is a `bind`, each repetition's: "
                                              "what a list exports is every repetition's, `(export "
                                              "(x ...))`")
                          f)
                 nil)
          (let* ((l (nth items 1)) (m (nth items 3))
                 (ll (if (syn-symbol? l) (label-of (syn-symbol l) ls) nil))
                 (ml (if (syn-symbol? m) (label-of (syn-symbol m) ls) nil)))
            (cond
              ((and (syn-symbol? l) (null? ll))
               (begin (fail-at fail (string-append "`" (syn-name l) "` labels no part of this "
                                                   "node")
                               l)
                      nil))
              ((or (null? ll) (= (extract (car ll) 2) 0)) (begin (fail-at fail outside l) nil))
              ((and (syn-symbol? m) (null? ml))
               (begin (fail-at fail (string-append "`" (syn-name m) "` labels no part of this "
                                                   "node")
                               m)
                      nil))
              ((or (null? ml) (= (extract (car ml) 2) 0)) (begin (fail-at fail outside m) nil))
              ((not (steps=? (extract (car ll) 3) (extract (car ml) 3)))
               (begin (fail-at fail (string-append "a fact under `...` names one list's "
                                                   "repetition: these are of two lists")
                               f)
                      nil))
              ((= (extract (car ll) 5) 0)
               (begin (fail-at fail (string-append "`" (syn-name l) "` labels a part that binds "
                                                   "nothing")
                               l)
                      nil))
              (else
               (let* ((g (extract (car ll) 5)) (ep (extract (car ll) 4))
                      (bd (if (= g 5)
                              (mk-list (list (mk-symbol "cage" a b)
                                             (mk-list (list (mk-symbol "at" a b) (path-syn ep a b))
                                                      a b))
                                       a b)
                              (mk-list (list (mk-symbol "rho" a b) (rib-entry fail a b ep g))
                                       a b))))
                 (list (tuple (extract (car ll) 3) (extract (car ml) 4) bd))))))))))
;; `sigma` with each repetition's facts `xs` made: the part a fact names in
;; the repeated element of the list at its path imported its binding.
(define each-annotated (->* (fails syn eaches) syn)
  (lambda (fail sigma xs)
    (if (null? xs)
        sigma
        (each-annotated fail (in-element fail sigma (extract (car xs) 1) (extract (car xs) 2)
                                         (extract (car xs) 3))
                        (cdr xs)))))
(define in-element (->* (fails syn steps steps syn) syn)
  (lambda (fail sigma lp p bd)
    (let ((ps (split sigma)))
      (cond ((null? ps) (begin (fail-at fail "a repeated part not found in its tree" sigma) sigma))
            ((null? lp) (cons-syn (annotate fail (car ps) p "import" bd) (nth ps 1) sigma))
            ((car lp) (cons-syn (in-element fail (car ps) (cdr lp) p bd) (nth ps 1) sigma))
            (else (cons-syn (car ps) (in-element fail (nth ps 1) (cdr lp) p bd) sigma))))))
;; The facts read: imports (by path, the last first), a rib's entries (the
;; last first), a ribcage's rings (innermost first), whether there is one,
;; each repeated element's entries (by the list's path, the last first).
(define facts-each
  (->* (fails syns-a labels bool adds syns-a syns-a syns-a adds)
       (tupleof adds syns-a syns-a syns-a adds))
  (lambda (fail fs ls top imports rib rings star elems)
    (if (null? fs)
        (tuple imports rib rings star elems)
        (let* ((f (car fs)) (items (proper-items f)))
          (cond
            ((and (head-is? f "bind") (= (len items) 4) (sym-is? (nth items 2) "in"))
             (let* ((m (nth items 3))
                    (target (if (syn-symbol? m) (label-of (syn-symbol m) ls) nil)))
               (cond ((null? target)
                      (begin (fail-at fail "`(bind L in name)`: `name` a label of this node" m)
                             (tuple imports rib rings star elems)))
                     ((= (extract (car target) 2) 1)
                      (begin (fail-at fail (string-append "a fact binding in a repeated part is "
                                                          "each repetition's: followed by `...`")
                                      m)
                             (tuple imports rib rings star elems)))
                     (else
                      (let ((e (bound fail (nth items 1) ls)))
                        (facts-each fail (cdr fs) ls top
                                    (cons (tuple (extract (car target) 3) (extract e 1)) imports)
                                    rib rings star (append (extract e 2) elems)))))))
            ((and (head-is? f "export") (not top))
             (let ((r (entries-of fail (cdr items) ls #f nil elems)))
               (facts-each fail (cdr fs) ls top imports (append (extract r 1) rib) rings star
                           (extract r 2))))
            ((and (head-is? f "export*") (not top))
             (let ((r (entries-of fail (cdr items) ls #t nil elems)))
               ;; Innermost first: the last written.
               (facts-each fail (cdr fs) ls top imports rib (extract r 1) (list f) (extract r 2))))
            ((or (head-is? f "export") (head-is? f "export*"))
             (begin (fail-at fail (string-append "what a use defines is said in what its "
                                                 "signature makes, `(defn label …)`: the top node "
                                                 "exports nothing")
                             f)
                    (tuple imports rib rings star elems)))
            (else
             (begin (fail-at fail (string-append "a fact is `(bind L in name)`, `(export L …)` or "
                                                 "`(export* L …)`")
                             f)
                    (tuple imports rib rings star elems))))))))
;; Each of `L`s `xs` an entry (or a ring), onto `out` (the last first); and
;; what each repeated element must export for it.
(define entries-of (->* (fails syns-a labels bool syns-a adds) (tupleof syns-a adds))
  (lambda (fail xs ls ring out elems)
    (if (null? xs)
        (tuple out elems)
        (let ((e (entry fail (car xs) ls ring)))
          (entries-of fail (cdr xs) ls ring (cons (extract e 1) out)
                      (append (extract e 2) elems))))))
;; What `(bind L in …)` imports: one level of `L`'s, a ribcage if it gives
;; one.
(define bound (->* (fails syn labels) (tupleof syn adds))
  (lambda (fail l ls)
    (let* ((e (entry fail l ls #f)) (a (syn-start l)) (b (syn-end l))
           (cage (head-is? (extract e 1) "at")))
      (tuple (mk-list (list (mk-symbol (if cage "cage" "rho") a b) (extract e 1)) a b)
             (extract e 2)))))
;; `L`, a label or `(label ...)`, as a rib's entry `(path δ)`, or, in a
;; ribcage (`ring`), a ring: `(rho (path δ))` or `(at path)`; and what each
;; repeated element must export for it, by the list's path.
(define entry (->* (fails syn labels bool) (tupleof syn adds))
  (lambda (fail l ls ring)
    (let* ((items (proper-items l))
           (rep (and (= (len items) 2) (sym-is? (nth items 1) "...")))
           (n (if rep (car items) l))
           (a (syn-start l)) (b (syn-end l))
           (none (tuple (mk-list nil a b) (the adds nil))))
      (if (not (syn-symbol? n))
          (begin (fail-at fail "a fact names a label, or `(label ...)`, every repetition's" l) none)
          (let ((found (label-of (syn-symbol n) ls)) (name (syn-name n)))
            (cond
              ((null? found)
               (begin (fail-at fail (string-append "`" name "` labels no part of this node") l)
                      none))
              ((and (= (extract (car found) 2) 0) rep)
               (begin (fail-at fail (string-append "`" name "` is not repeated: named alone, not `("
                                                   name " ...)`")
                               l)
                      none))
              ((and (= (extract (car found) 2) 1) (not rep))
               (begin (fail-at fail (string-append "`" name "` is a repeated part's: `(" name
                                                   " ...)`, every repetition's, or a fact under "
                                                   "`...`, each repetition's")
                               l)
                      none))
              (else
               (let* ((lab (car found)) (p (extract lab 3))
                      (g (if rep 4 (extract lab 5)))
                      (adds (if (and rep (not (= (extract lab 5) 0)))
                                (list (tuple p (rib-entry fail a b (extract lab 4)
                                                          (extract lab 5))))
                                nil)))
                 (cond
                   ((= g 0)
                    (begin (fail-at fail (string-append "`" name "` labels a part that binds "
                                                        "nothing")
                                    l)
                           none))
                   ((= g 5) (tuple (mk-list (list (mk-symbol "at" a b) (path-syn p a b)) a b) adds))
                   (ring (tuple (mk-list (list (mk-symbol "rho" a b) (rib-entry fail a b p g)) a b)
                                adds))
                   (else (tuple (rib-entry fail a b p g) adds)))))))))))
(define rib-entry (->* (fails int int steps int) syn)
  (lambda (fail a b p g)
    (mk-list (list (path-syn p a b)
                   (mk-symbol (cond ((= g 1) "var") ((= g 2) "dvar") ((= g 3) "place")
                                    ((= g 4) "rib") (else "none"))
                              a b))
             a b)))
;; `(path #:a #:d …)`, or `()`.
(define path-syn (->* (steps int int) syn)
  (lambda (p a b)
    (if (null? p) (mk-list nil a b) (mk-list (cons (mk-symbol "path" a b) (path-keys p a b)) a b))))
(define path-keys (->* (steps int int) syns-a)
  (lambda (p a b)
    (if (null? p)
        nil
        (cons (atom (symbol->keyword (if (car p) 'a 'd)) a b 0) (path-keys (cdr p) a b)))))
;; `sigma` with the part at `path` annotated, `(how part b)`.
(define annotate (->* (fails syn steps string syn) syn)
  (lambda (fail sigma path how bd)
    (if (null? path)
        (mk-list (list (mk-symbol how (syn-start sigma) (syn-end sigma)) sigma bd)
                 (syn-start sigma) (syn-end sigma))
        (let ((ps (split sigma)))
          (if (null? ps)
              (begin (fail-at fail "a label's part not found in its tree" sigma) sigma)
              (if (car path)
                  (cons-syn (annotate fail (car ps) (cdr path) how bd) (nth ps 1) sigma)
                  (cons-syn (car ps) (annotate fail (nth ps 1) (cdr path) how bd) sigma)))))))
(define imports-annotated (->* (fails syn adds) syn)
  (lambda (fail sigma xs)
    (if (null? xs)
        sigma
        (imports-annotated fail
                           (annotate fail sigma (extract (car xs) 1) "import" (extract (car xs) 2))
                           (cdr xs)))))
;; `sigma` with each repeated element of the lists at the paths `xs` give
;; exporting their entries, one rib each.
(define elements-annotated (->* (fails syn adds) syn)
  (lambda (fail sigma xs)
    (if (null? xs)
        sigma
        (let* ((p (extract (car xs) 1)) (same (distinct-from (adds-at p xs) nil))
               (rest (adds-not-at p xs)))
          (elements-annotated fail (element-annotated fail sigma p same) rest)))))
;; Entries `xs`, each once, the first kept, past those `seen`: however many
;; facts name `(v ...)`, an element exports `v` once.
(define distinct-from (->* (syns-a syns-a) syns-a)
  (lambda (xs seen)
    (cond ((null? xs) nil)
          ((syn-in? (car xs) seen) (distinct-from (cdr xs) seen))
          (else (cons (car xs) (distinct-from (cdr xs) (cons (car xs) seen)))))))
(define syn-in? (->* (syn syns-a) bool)
  (lambda (x ys)
    (and (not (null? ys))
         (or (string=? (show-syn x) (show-syn (car ys))) (syn-in? x (cdr ys))))))
(define adds-at (->* (steps adds) syns-a)
  (lambda (p xs)
    (cond ((null? xs) nil)
          ((steps=? p (extract (car xs) 1)) (cons (extract (car xs) 2) (adds-at p (cdr xs))))
          (else (adds-at p (cdr xs))))))
(define adds-not-at (->* (steps adds) adds)
  (lambda (p xs)
    (cond ((null? xs) nil)
          ((steps=? p (extract (car xs) 1)) (adds-not-at p (cdr xs)))
          (else (cons (car xs) (adds-not-at p (cdr xs)))))))
(define steps=? (->* (steps steps) bool)
  (lambda (p q)
    (cond ((null? p) (null? q)) ((null? q) #f)
          (else (and (eq? (car p) (car q)) (steps=? (cdr p) (cdr q)))))))
(define element-annotated (->* (fails syn steps syns-a) syn)
  (lambda (fail sigma path es)
    (let ((ps (split sigma)) (a (syn-start sigma)) (b (syn-end sigma)))
      (cond ((null? ps) (begin (fail-at fail "a repeated part not found in its tree" sigma) sigma))
            ;; The list: `(elem ...)`.
            ((null? path)
             (cons-syn (mk-list (list (mk-symbol "export" a b) (car ps)
                                      (mk-list (cons (mk-symbol "rho" a b) es) a b))
                                a b)
                       (nth ps 1) sigma))
            ((car path) (cons-syn (element-annotated fail (car ps) (cdr path) es) (nth ps 1) sigma))
            (else (cons-syn (car ps) (element-annotated fail (nth ps 1) (cdr path) es) sigma))))))
;; `(car . cdr)` at `s`'s place, a list's parts kept a list.
(define cons-syn (->* (syn syn syn) syn)
  (lambda (car-s cdr-s s) (list-with (list car-s) (list cdr-s) (syn-start s) (syn-end s))))

;;; ------------------------------------------------------------ what is made

;; `MADE`: `(defn D …)` Herman's, each label its path, `(label ...)` every repetition's, the
;; list's rib; and what each repeated element must export for it, by the list's path.
(define made-of (->* (fails syn labels) (tupleof syn adds))
  (lambda (fail m ls)
    (if (not (head-is? m "defn"))
        (tuple m (the adds nil))
        (let ((r (made-entries fail (cdr (proper-items m)) ls nil nil)))
          (tuple (mk-list (cons (car (proper-items m)) (extract r 1)) (syn-start m) (syn-end m))
                 (extract r 2))))))
;; Entries `ds` onto `out`, adds onto `adds`, the last first.
(define made-entries (->* (fails syns-a labels syns-a adds) (tupleof syns-a adds))
  (lambda (fail ds ls out adds)
    (if (null? ds)
        (tuple (reverse out) (reverse adds))
        (let* ((d (car ds)) (two (proper-items d)) (pair (= (len two) 2))
               (every (and pair (sym-is? (nth two 1) "...")))
               (n (if pair (car two) d)) (a (syn-start d)) (b (syn-end d))
               (found (if (syn-symbol? n) (label-of (syn-symbol n) ls) nil)))
          (cond
            ((and every (not (syn-symbol? n)))
             (begin (fail-at fail (string-append "every repetition's macro binder, `((label "
                                                 "(macro …)) ...)`: not yet")
                             d)
                    (made-entries fail (cdr ds) ls out adds)))
            ;; `(label ...)`: every repetition's, as a fact names it.
            (every
             (let ((e (entry fail d ls #f)))
               (made-entries fail (cdr ds) ls (cons (extract e 1) out)
                             (append (reverse (extract e 2)) adds))))
            ((not (syn-symbol? n))
             (begin (fail-at fail (string-append "what a use defines is a label, `(label ...)` "
                                                 "or `(label (macro …))`")
                             n)
                    (made-entries fail (cdr ds) ls out adds)))
            ((null? found)
             (begin (fail-at fail (string-append "`" (syn-name n) "` labels no part of this "
                                                 "signature's top")
                             n)
                    (made-entries fail (cdr ds) ls out adds)))
            ((= (extract (car found) 2) 1)
             (begin (fail-at fail (string-append "`" (syn-name n) "` is a repeated part's: `("
                                                 (syn-name n) " ...)`, every repetition's")
                             n)
                    (made-entries fail (cdr ds) ls out adds)))
            (pair
             ;; A macro's binder: its signature as written, read where it is.
             (made-entries fail (cdr ds) ls
                           (cons (mk-list (list (path-syn (extract (car found) 3) a b) (nth two 1))
                                          a b)
                                 out)
                           adds))
            (else (made-entries fail (cdr ds) ls
                                (cons (rib-entry fail a b (extract (car found) 3)
                                                 (extract (car found) 5))
                                      out)
                                adds)))))))
