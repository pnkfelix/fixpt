;;; Typed hygienic macros, in FX-26: what a template's export binds of what
;;; its uses give, compared and said, and the names a template binds in its
;;; uses of macros that make definitions (`macros.rs`'s `exports`,
;;; `shown_exports` and `binders_under`), what says how many times a
;;; template's part is repeated (`transcribe`'s), and what the checker is
;;; told of the `with` forms an expansion made (`Macros::with_uses`,
;;; `projections`). Part of the expander: loaded by `macros-files.fx`, and
;;; loading `macros-match.fx` (and through it `macros-scopes.fx` and
;;; `macros-align.fx`, whose nodes these read), so that `macros.fx` takes one
;;; instance of each through it.

(module-parameters ((rs region) (re region) (rm region) (rc region) (rp region)))
(define match-module ((proj (load-module "fx26:macros-match.fx") rs re rm rc rp)))
(define scopes-module (with match-module scopes-module))
(define align-module (with scopes-module align-module))
(define types-module (with align-module types-module))
(define parser-module (with types-module parser-module))
(define reader-types (with parser-module reader-types))
(import reader-types atom lst (type syn))
(import parser-module syn-start syn-end syn-symbol? syn-symbol syn-name syn-expansion len nth
        syn-datums (type names syns-a))
(import types-module fail-at name-in? proper-items atm-var atm-rib-of
        atm-lit addr=? (type fails atm atms addr))
(import match-module pattern-names addr-under?)
(import scopes-module normal atm-in? (type head-readings))
(import align-module node-kids node-syn pvar? makes-defns? lv-rib lv-cage lv-earlier lv-shape k-pair
        k-form k-desc k-seq k-binder act-rename sorted-strings joined pending node-path
        not-definition
        (type levels pvars actions strings found))

;;; ------------------------------------------------------------ exports

;; What an export binds of what a use gives, as compared (`macros.rs`'s
;; `exports`): its pattern variables' atoms and its ribcages, each once;
;; the template's own binders, made fresh, none of it.
(define-type exported (tupleof atms names))
(define exports-of (->* (levels) exported)
  (lambda (env) (exports-onto (normal env) nil nil)))
(define exports-onto (->* (levels atms names) exported)
  (lambda (ls as ns)
    (if (null? ls)
        (tuple as ns)
        (tagcase (car ls)
          (lv-rib (xs) (exports-onto (cdr ls) (atms-onto xs as) ns))
          (lv-earlier (xs) (exports-onto (cdr ls) (atms-onto xs as) ns))
          (lv-cage (n) (exports-onto (cdr ls) as (if (name-in? n ns) ns (cons n ns))))
          (lv-shape (m) (exports-onto (cdr ls) as ns))))))
(define atms-onto (->* (atms atms) atms)
  (lambda (xs as)
    (cond ((null? xs) as)
          ((atm-in? (car xs) as) (atms-onto (cdr xs) as))
          (else (atms-onto (cdr xs) (cons (car xs) as))))))
(define exports=? (->* (exported exported) bool)
  (lambda (x y)
    (and (atms-within? (extract x 1) (extract y 1)) (atms-within? (extract y 1) (extract x 1))
         (names-within? (extract x 2) (extract y 2)) (names-within? (extract y 2) (extract x 2)))))
(define atms-within? (->* (atms atms) bool)
  (lambda (xs ys) (or (null? xs) (and (atm-in? (car xs) ys) (atms-within? (cdr xs) ys)))))
(define names-within? (->* (names names) bool)
  (lambda (xs ys) (or (null? xs) (and (name-in? (car xs) ys) (names-within? (cdr xs) ys)))))
;; An export's names, as said, in order (`shown_exports`).
(define shown-exports (->* (exported) string)
  (lambda (e)
    (let ((ss (sorted-strings (append (atm-strings (extract e 1)) (cage-strings (extract e 2)))
                              nil)))
      (if (null? ss) "nothing" (joined ss)))))
(define atm-strings (->* (atms) strings)
  (lambda (as)
    (if (null? as)
        nil
        (let ((rest (atm-strings (cdr as))))
          (tagcase (car as)
            (atm-var (n d g) (cons (string-append "`" (symbol->string n) "`") rest))
            (atm-rib-of (n) (cons (string-append "what `" (symbol->string n) "` defines") rest))
            (atm-lit (t d) rest))))))
(define cage-strings (->* (names) strings)
  (lambda (ns)
    (if (null? ns)
        nil
        (cons (string-append "what `" (symbol->string (car ns)) "` defines")
              (cage-strings (cdr ns))))))
;; The names a template binds in its uses of macros that make definitions,
;; nodes `i` to `n`, each with the macro: what their signatures do not say
;; they define, it does not see (`macros.rs`'s `binders_under`).
(define-type nested (listof (tupleof symbol symbol) acyclic))
(define nested-binders (->* (int int pvars) nested)
  (lambda (i n ps) (nested-from i (- n 1) ps nil)))
;; Those of nodes `i` to `j`, before `out`: from the last back, so that
;; they are in the nodes' order.
(define nested-from (->* (int int pvars nested) nested)
  (lambda (i j ps out)
    (if (< j i)
        out
        (let* ((items (proper-items (node-syn j)))
               (h (if (and (not (null? items)) (syn-symbol? (car items))) (list (car items)) nil))
               (here (tagcase (node-kids j)
                       (k-form (x)
                         (if (and (not (null? h)) (not (pvar? (syn-symbol (car h)) ps))
                                  (makes-defns? (syn-symbol (car h))))
                             (binders-under x (syn-symbol (car h)))
                             nil))
                       (else y nil))))
          (nested-from i (- j 1) ps (append here out))))))
(define binders-under (->* (int symbol) nested)
  (lambda (at m)
    (tagcase (node-kids at)
      (k-pair (x y) (append (binders-under x m) (binders-under y m)))
      (k-form (x) (binders-under x m))
      (k-seq (x) (binders-under x m))
      (k-desc (xs) (binders-under-each xs m))
      (k-binder (n d) (if d (the nested nil) (the nested (list (tuple n m)))))
      (else y (the nested nil)))))
(define binders-under-each (->* ((listof int acyclic) symbol) nested)
  (lambda (xs m)
    (if (null? xs) nil (append (binders-under (car xs) m) (binders-under-each (cdr xs) m)))))
;; The macro whose use binds `n`, of `ns`, in a list of one.
(define nested-of (->* (symbol nested) (listof symbol acyclic))
  (lambda (n ns)
    (cond ((null? ns) nil)
          ((symbol=? n (extract (car ns) 1)) (list (extract (car ns) 2)))
          (else (nested-of n (cdr ns))))))
;; A name a nested use binds, `n`, which no binder of the template's binds
;; here (`b`), and the use is not said to define: refused, not read at the
;; top level, which the template would seem to mean by it.
(define unsaid-nested (->* (fails symbol (listof int acyclic) nested syn) unit)
  (lambda (fail n b nested s)
    (let ((m (nested-of n nested)))
      (if (and (null? b) (not (null? m)))
          (let ((n (symbol->string n)))
            (fail-at fail (string-append "`" n "` is bound in a use of `" (symbol->string (car m))
                                         "`, whose signature does not say its uses define it: "
                                         "say so (`(macro σ (defn (ℓ δ) …))`), or write `(with "
                                         "#%toplevel " n ")` for the top level's")
                     s))
          #u))))

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

;;; ------------------------------------------------------------ withs

;; The `with` forms around a part, each by its place.
(define-type places (listof (tupleof int int) acyclic))
;; By each `with` form's place, the macros used in its body by names the
;; program wrote, each with the use's place (`Macros::with_uses`): the
;; checker refuses the `with` if its module gives a value of the name (0
;; last). And, 1 last, a template's `(with m name)`, with the name's place
;; (`Macros::projections`): refused if the module gives no value of it,
;; which would otherwise be what it is where the macro is used; 2, a path's
;; `with`, its path to the name for the name, the same (`TODO.md` §296).
(define-type uses (listof (tupleof int int symbol int int int) acyclic))
(define with-uses (ref uses rs) (new nil))
;; For the checker: this parse's, in the order the expander met them.
(define with-uses-given (->* () uses) (lambda () (reverse (get with-uses))))
;; A template's `(with m name)`, `s`, of items `items` and head `hd`: noted,
;; for the checker to refuse if `m` gives no value `name`.
(define note-projection (->* (syn syns-a syn) unit)
  (lambda (s items hd)
    (if (and (not (= (syn-expansion hd) 0)) (= (len items) 3) (syn-symbol? (nth items 1))
             (syn-symbol? (nth items 2)) (not (string=? (syn-name (nth items 1)) "#%fx"))
             (not (string=? (syn-name (nth items 1)) "#%toplevel")))
        (set with-uses (cons (tuple (syn-start s) (syn-end s) (syn-symbol (nth items 2))
                                    (syn-start (nth items 2)) (syn-end (nth items 2)) 1)
                             (get with-uses)))
        #u)))
;; The uses of macro `n`, at `hd`, noted in each `with` around it.
(define note-uses (->* (symbol syn places) unit)
  (lambda (n hd withs)
    (if (null? withs)
        #u
        (begin
          (set with-uses (cons (tuple (extract (car withs) 1) (extract (car withs) 2) n
                                      (syn-start hd) (syn-end hd) 0)
                               (get with-uses)))
          (note-uses n hd (cdr withs))))))
;; Path `s`, `a::b::c`, a symbol, where a value is (a description, if `d`):
;; `(with (with a b) c)`, or `(select (with a b) c)` (`TODO.md` §296), each
;; `with` at the part of `s` it reads and noted (2, its path to its name for
;; the name), for the checker to refuse if its module gives no value of the
;; name, as a template's: each name of a path is of the module before it,
;; never one bound around it (`Macros::path_written`).
(define path-written (->* (fails syn bool) syn)
  (lambda (fail s d)
    (let ((k (string-search (syn-name s) "::" 0)))
      (if (= k 0)
          (path-refused fail s)
          (path-from fail s d (named-at (substring (syn-name s) 0 k) 0 k s) k)))))
;; `out`, the first `len` characters of path `s` read; the rest read on.
(define path-from (->* (fails syn bool syn int) syn)
  (lambda (fail s d out len)
    (let* ((n (syn-name s)) (start (+ len 2)) (k (string-search n "::" start))
           (end (if (< k 0) (string-length n) k))
           (x (named-at (substring n start end) start end s)))
      (cond ((= start end) (path-refused fail s))
            ((and (< k 0) d) (list-of (list (named-at "select" 0 end s) out x) end s))
            (else
             (let ((f (list-of (list (named-at "with" 0 end s) out x) end s)))
               (begin
                 (set with-uses (cons (tuple (syn-start f) (syn-end f)
                                             (string->symbol (substring n 0 end)) (syn-start x)
                                             (syn-end x) 2)
                                      (get with-uses)))
                 (if (< k 0) f (path-from fail s d f end)))))))))
(define path-refused (->* (fails syn) syn)
  (lambda (fail s)
    (begin (fail-at fail (string-append "`" (syn-name s) "` is not a path: a path is names joined "
                                        "by `::`, `module::name`")
                    s)
           s)))
;; Name `n` at characters `a` to `b` of `s`, of its expansion.
(define named-at (->* (string int int syn) syn)
  (lambda (n a b s)
    (atom (string->symbol n) (+ (syn-start s) a) (+ (syn-start s) b) (syn-expansion s))))
;; Items `xs` as a list at the first `b` characters of `s`.
(define list-of (->* (syns-a int syn) syn)
  (lambda (xs b s) (lst xs (syn-datums xs) (syn-start s) (+ (syn-start s) b) (syn-expansion s))))

;;; ------------------------------------------------------------ binders' depths

;; Each template binder the walk found, with how many ellipses it is under.
(define-type depths (listof (tupleof int int) acyclic))
(define binder-depths (->* (found) depths)
  (lambda (fs)
    (cond ((null? fs) nil)
          ((tagcase (node-kids (extract (car fs) 1)) (k-binder (n d) #t) (else y #f))
           (cons (tuple (extract (car fs) 1) (extract (car fs) 4)) (binder-depths (cdr fs))))
          (else (binder-depths (cdr fs))))))
(define depth-of (->* (int depths) int)
  (lambda (b ds)
    (cond ((null? ds) 0) ((= b (extract (car ds) 1)) (extract (car ds) 2))
          (else (depth-of b (cdr ds))))))
;; A binder `b` (none or one) repeated, referred to under `depth`, fewer
;; ellipses than it is under: which repetition's is not said.
(define repeated-ref (->* (fails symbol (listof int acyclic) int depths syn) unit)
  (lambda (fail n b depth bd s)
    (if (and (not (null? b)) (> (depth-of (car b) bd) depth))
        (fail-at fail (string-append "`" (symbol->string n) "` is bound in each repetition of a "
                                     "part, and referred to under fewer ellipses than it is "
                                     "bound: which repetition's it is is not said")
                 s)
        #u)))

;;; ------------------------------------------------------------ heads read by scope

;; The pending lists' readings `rs` (`macros-scopes.fx`'s `aligned-heads`),
;; done: one where a definition is, read as no macro's use, refused as no
;; definition; each read as a use, checked (`heads-checked`), its head, a
;; template's binder, renamed with it (`clause`'s). `bd`, the binders'
;; depths; the actions to add.
(define heads-checked (ref (listof int acyclic) rs) (new nil))
(define heads-done (->* (fails head-readings depths) actions)
  (lambda (fail rs bd)
    (begin (set heads-checked nil) (heads-done-each fail rs bd))))
(define heads-done-each (->* (fails head-readings depths) actions)
  (lambda (fail rs bd)
    (if (null? rs)
        nil
        (let* ((at (extract (car rs) 1)) (s (node-syn at)) (b (extract (car rs) 3)))
          (cond ((and (null? (extract (car rs) 2)) (pending-defn? at (get pending)))
                 (begin (not-definition fail s (string-append "`define`, `define*`, `define-rec`, "
                                                              "a `begin` of them, or a use of "
                                                              "another such"))
                        nil))
                ((null? (extract (car rs) 2)) (heads-done-each fail (cdr rs) bd))
                (else
                 (begin
                   (set heads-checked (cons (syn-start s) (get heads-checked)))
                   (let ((rest (heads-done-each fail (cdr rs) bd)))
                     (if (null? b)
                         rest
                         (cons (tuple (append (node-path at) (the addr (list #t)))
                                      (act-rename (node-path (car b)) (depth-of (car b) bd)))
                               rest))))))))))
(define pending-defn? (->* (int (listof (tupleof int bool) acyclic)) bool)
  (lambda (at ps)
    (and (not (null? ps))
         (or (and (= at (extract (car ps) 1)) (extract (car ps) 2)) (pending-defn? at (cdr ps))))))
