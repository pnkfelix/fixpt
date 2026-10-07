;;; The checker, in FX-26: what reading descriptions from their syntax into
;;; the arena needs before it (`check-read-types.fx` reads them, by the
;;; pieces `check-read.fx` gives): regions, effects' atoms, labels, `dletrec`
;;; knots, `define-type`'s forward names. Part of the checker,
;;; `check-types.fx` first (PLAN.md §11, step 10).

;; A module (`TODO.md` §34: the front end into modules, a file at a time);
;; what other files use re-exported after it.
(define check-syntax-module (module
(define-rec
  ;; `(head x)`: one atom on region `x`; or, `x` being globals, one for
  ;; each.
  (k-effect-atom (subr (maxeff checks spin) (string syn) k-eff)
    (lambda (head x)
      (let ((gs (k-globals-region x)))
        (cond ((null? gs) (k-one (k-atom-of head (k-parse-region x))))
              ;; Globals' bindings, which are only read and written.
              ((or (string=? head "read") (string=? head "write"))
               (k-atoms-on (string=? head "read") (car gs)))
              (else (k-sfail (k-cat3 "globals are only read and written, not `" head "`") x)))))))

;; A label or tag: a name, or a positive integer, which is its digits.
(define k-syn-label (subr checks (syn) symbol)
  (lambda (s)
    (cond ((syn-symbol? s) (syn-head s))
          ((> (syn-int s) 0) (string->symbol (int->string (syn-int s))))
          (else (k-sfail "a label is a name or a positive integer" s)))))
(define k-has-label? (subr kreads (k-parts symbol) bool)
  (lambda (ps l)
    (cond ((null? ps) #f) ((symbol=? (extract (car ps) 1) l) #t) (else (k-has-label? (cdr ps) l)))))

(define k-shape (subr checks (bool string syn) unit)
  (lambda (ok shape s) (if ok #u (k-sfail shape s))))
(define-type k-slots (listof (pairof int syn @t) acyclic))
(define k-dletrec-slots (subr (maxeff checks spin) (k-syns) k-slots)
  (lambda (bs)
    (if (null? bs)
        nil
        (let ((pair (k-items (car bs) "a dletrec binding")))
          (if (= (k-length pair) 2)
              (let* ((name (k-name-of (car pair) "a name"))
                     (slot (k-slot))
                     (pushed (k-push-desc name (ds-rec slot)))
                     (rest (k-dletrec-slots (cdr bs))))
                (cons (cons slot (k-nth pair 1)) rest))
              (k-sfail "a dletrec binding is `(name type)`" (car bs)))))))
;; Where description variable `v` is among binders `bs`, from `i`, or -1.
(define k-binder-index (subr (read @globals) (k-binders int int) int)
  (lambda (bs v i)
    (cond ((null? bs) -1)
          ((= (extract (car bs) 1) v) i)
          (else (k-binder-index (cdr bs) v (+ i 1))))))
;; The `i`th description of `ds`, none or one.
(define k-desc-at (subr (read @globals) (k-descs int) k-descs)
  (lambda (ds i)
    (cond ((null? ds) nil)
          ((= i 0) (the k-descs (cons (car ds) nil)))
          (else (k-desc-at (cdr ds) (- i 1))))))
;; The `i`th parameter of binders `ps` a type `t` is, or -1.
(define k-param-of (subr (maxeff kreads spin) (k-binders int) int)
  (lambda (ps t) (tagcase (k-get (k-resolve t)) (ty-var (v) (k-binder-index ps v 0)) (else y -1))))
;; What `args` gives for description `d`, if it is one of parameters `ps`:
;; none or one.
(define k-desc-given (subr (maxeff kreads spin) (k-desc k-binders k-descs) k-descs)
  (lambda (d ps args)
    (tagcase d
      (dt (t) (let ((i (k-param-of ps t))) (if (< i 0) (the k-descs nil) (k-desc-at args i))))
      (else y (the k-descs nil)))))
;; Descriptions `inner`, with each that is one of parameters `ps` replaced
;; by what `args` gives for it.
(define k-descs-given (subr (maxeff kreads spin) (k-descs k-binders k-descs) k-descs)
  (lambda (inner ps args)
    (if (null? inner)
        nil
        (let* ((d (car inner))
               (given (k-desc-given d ps args))
               (rest (k-descs-given (cdr inner) ps args)))
          (the k-descs (cons (if (null? given) d (car given)) rest))))))
;; The type description `d` is, alone in a list; none if it is no type.
(define k-desc-type (subr (read @globals) (k-desc) k-ids)
  (lambda (d) (tagcase d (dt (t) (the k-ids (cons t nil))) (else y nil))))
;; The type the `g`th generative type, given `args`, is at its head, if its
;; representation is one of its type parameters, perhaps through other such
;; generative types: what it is given there (none or one). None if its
;; representation has a constructor at its head
;; (`docs/research/soundness-findings.md`, A2).
(define k-named-head (subr (maxeff kreads spin) (int k-descs k-ids) k-ids)
  (lambda (g args seen)
    (if (k-has-id? seen g)
        nil
        (let* ((gen (k-gen-of g)) (ps (extract gen 2)) (rep (extract gen 4)))
          (tagcase (k-get (k-resolve rep))
            (ty-var (v)
              (let ((i (k-param-of ps rep)))
                (if (< i 0)
                    nil
                    (let ((d (k-desc-at args i)))
                      (if (null? d) nil (k-desc-type (car d)))))))
            (ty-named (h inner)
              (k-named-head h (k-descs-given inner ps args) (the k-ids (cons g seen))))
            (else y nil))))))
;; The error of a recursive type built from names alone.
(define k-fail-ungrounded (subr checks (int int) void)
  (lambda (a b)
    (k-fail "a recursive type must be built from a constructor, not only from names" a b)))
(define k-grounded-from (subr (maxeff checks spin) (int k-ids int int) unit)
  (lambda (id seen a b)
    (tagcase (k-raw id)
      (ty-link (to)
        (cond ((null? to) #u)
              ((k-has-id? seen id) (k-fail-ungrounded a b))
              (else (k-grounded-from (car to) (cons id seen) a b))))
      ;; A `poly` is no constructor either: a cycle through `poly`s alone
      ;; describes no type, and unfolding it would never end.
      (ty-poly (bs x)
        (if (k-has-id? seen id)
            (k-fail-ungrounded a b)
            (k-grounded-from x (cons id seen) a b)))
      ;; Nor is a generative type whose representation is one of what it is
      ;; given: it is that.
      (ty-named (g ds)
        (let ((h (k-named-head g ds nil)))
          (cond ((null? h) #u)
                ((k-has-id? seen id) (k-fail-ungrounded a b))
                (else (k-grounded-from (car h) (cons id seen) a b)))))
      (else x #u))))

;; Whether `start` is reached again from `id` through forwarding links,
;; `poly`s and the types given to functions applied: a cycle with no
;; constructor on it.
(define-rec
  (k-through-apps? (subr (maxeff kstate spin) (int int (ref k-ids @t)) bool)
    (lambda (id start seen)
      (if (k-has-id? (get seen) id)
          #f
          (begin
            (set seen (cons id (get seen)))
            (let ((next (tagcase (k-raw id)
                          (ty-link (to) to)
                          (ty-poly (bs x) (the k-ids (cons x nil)))
                          (ty-app (f ds) (k-desc-types ds))
                          (else y (the k-ids nil)))))
              (k-any-reaches? next start seen))))))
  (k-any-reaches? (subr (maxeff kstate spin) (k-ids int (ref k-ids @t)) bool)
    (lambda (xs start seen)
      (and (not (null? xs))
           (or (= (car xs) start) (k-through-apps? (car xs) start seen)
               (k-any-reaches? (cdr xs) start seen))))))
;; A name defined as another name, round a loop, describes nothing.
(define k-grounded (subr (maxeff checks spin) (int int int) unit)
  (lambda (slot a b)
    ;; A description function applied is no constructor either: what it
    ;; gives may be what it was given, so a cycle through applications alone
    ;; may be no type at all once the function is known (Rémy's condition:
    ;; recursion only at the base kind; `check-kinds.fx`).
    (if (k-through-apps? slot slot (the (ref k-ids @t) (new nil)))
        (k-fail-ungrounded a b)
        (k-grounded-from slot nil a b))))
(define k-dletrec-no-knot (subr (maxeff checks spin) (k-slots syn) unit)
  (lambda (ss s)
    (if (null? ss)
        #u
        (begin (k-no-knot (car (car ss)) (syn-start s) (syn-end s))
               (k-dletrec-no-knot (cdr ss) s)))))
(define k-dletrec-grounded (subr (maxeff checks spin) (k-slots syn) unit)
  (lambda (ss s)
    (if (null? ss)
        #u
        (begin (k-grounded (car (car ss)) (syn-start s) (syn-end s))
               (k-dletrec-grounded (cdr ss) s)))))
(define k-family-params (subr (maxeff checks spin) (k-syns) k-params)
  (lambda (ps)
    (if (null? ps)
        nil
        (let ((pair (k-items (car ps) "`(name kind)`")))
          (if (= (k-length pair) 2)
              (let* ((n (k-name-of (car pair) "a parameter's name"))
                     (k (k-parse-kind (k-nth pair 1)))
                     (rest (k-family-params (cdr ps))))
                (cons (product (1 n) (2 k)) rest))
              (k-sfail "a parameter is `(name kind)`" (car ps)))))))

;; `(define-type (name (param kind) …) type)`: nothing is read until it is
;; used.
(define k-define-family (subr (maxeff checks spin) (symbol k-syns syn) unit)
  (lambda (name params body) (k-push-desc name (ds-abbrev (k-family-params params) body))))
;; Push a scope's entries, the first first.
(define k-push-all (subr kstate (k-scope) unit)
  (lambda (bs)
    (if (null? bs) #u (begin (k-push-desc (car (car bs)) (cdr (car bs))) (k-push-all (cdr bs))))))

;; The type families being expanded, each with the descriptions given it
;; and the slot its type will fill: a use inside with the same descriptions
;; is that slot, a knot (regular recursion).
(define-type k-family-knot (productof (1 symbol) (2 k-scope) (3 int)))
(define k-knots (ref (listof k-family-knot acyclic) @t) (new nil))
(define k-ds=? (subr (maxeff kreads spin) (k-ds k-ds) bool)
  (lambda (x y)
    (tagcase x
      (ds-rec (a) (tagcase y (ds-rec (b) (= (k-resolve a) (k-resolve b))) (else z #f)))
      (ds-region (a) (tagcase y (ds-region (b) (k-region=? a b)) (else z #f)))
      (ds-eff (a) (tagcase y (ds-eff (b) (k-eff=? a b)) (else z #f)))
      (ds-size (a) (tagcase y (ds-size (b) (k-size=? a b)) (else z #f)))
      (ds-conv (a) (tagcase y (ds-conv (b) (k-conv=? a b)) (else z #f)))
      (ds-fun (a) (tagcase y (ds-fun (b) (= (k-resolve a) (k-resolve b))) (else z #f)))
      (else z #f))))
(define k-scope=? (subr (maxeff kreads spin) (k-scope k-scope) bool)
  (lambda (xs ys)
    (if (null? xs)
        (null? ys)
        (and (not (null? ys))
             (k-ds=? (cdr (car xs)) (cdr (car ys)))
             (k-scope=? (cdr xs) (cdr ys))))))
;; The head of a list's first item, or "" for anything else.
(define k-list-head (subr (maxeff (read @globals) (read @s)) (syn) string)
  (lambda (s) (tagcase s (lst (items d a b) (k-head items)) (else x ""))))
;; A convention: `cellular`, `native`, `fx`, or a name bound as one.
(define k-parse-conv (subr (maxeff checks spin) (syn) k-conv)
  (lambda (s)
    (if (not (syn-symbol? s))
        (k-sfail "a convention is `cellular`, `native`, `fx`, or a name bound as one" s)
        (let* ((n (syn-name s)) (no (k-cat3 "`" n "` is not a convention")))
          (cond ((string=? n "cellular") (cv-cellular))
                ((string=? n "native") (cv-native))
                ((string=? n "fx") (cv-fx))
                (else
                 (let ((d (k-lookup-desc (string->symbol n))))
                   (if (null? d)
                       (k-sfail no s)
                       (tagcase (car d)
                         (ds-var (v k) (if (= k 6) (cv-var v) (k-sfail no s)))
                         (ds-conv (c) c)
                         (else x (k-sfail no s)))))))))))
;; `(conv C)`: the convention `C`.
(define k-parse-conv-form (subr (maxeff checks spin) (syn) k-conv)
  (lambda (s)
    (let ((items (k-items s "`(conv convention)`")))
      (if (= (k-length items) 2)
          (k-parse-conv (k-nth items 1))
          (k-sfail "`(conv convention)`" s)))))
;; The slot of the expansion of `name` with `bound` in progress, or -1.
(define k-knot-of (subr (maxeff kreads spin) ((listof k-family-knot acyclic) symbol k-scope) int)
  (lambda (ks name bound)
    (cond ((null? ks) -1)
          ((and (symbol=? (extract (car ks) 1) name) (k-scope=? (extract (car ks) 2) bound))
           (extract (car ks) 3))
          (else (k-knot-of (cdr ks) name bound)))))

;; What a label or name given twice says.
(define k-twice (subr (read @globals) (string) string)
  (lambda (name) (string-append (k-quote name) " appears twice")))
;; Whether a type with head `h` is storage written, so that a procedure
;; kept in it could reach itself.
(define k-storage-head? (subr pure (string) bool)
  (lambda (h)
    (or (string=? h "ref") (string=? h "icell") (string=? h "pairof") (string=? h "listof")
        (string=? h "bloblet") (string=? h "arrayof") (string=? h "mark-key") (string=? h "mu"))))
;; Whether kind `k` is `type` or `data`.
(define k-type-kind? (subr pure (int) bool)
  (lambda (k) (or (= k 2) (= k 4))))
;; The size a name stands for: `finite`, or a size variable.
(define k-size-named (subr (maxeff checks spin) (syn string) k-size)
  (lambda (s usage)
    (if (string=? (syn-name s) "finite")
        (sz-finite)
        (let ((d (k-lookup-desc (string->symbol (syn-name s)))))
          (if (null? d)
              (k-sfail usage s)
              (tagcase (car d)
                (ds-var (v k) (if (= k 5) (k-size-var v) (k-sfail usage s)))
                (ds-size (z) z)
                (else x (k-sfail usage s))))))))
;; A lemma stated, `bs` its binders, `conc` its conclusion: pending, no
;; definition proving it yet.
(define k-stated-lemma (subr kreads (k-binders (pairof int int @t) k-hyps) k-lemma)
  (lambda (bs conc hyps)
    (product (1 bs) (2 (car conc)) (3 (cdr conc)) (4 hyps) (5 (the k-named nil)))))
;; The type of the coercion a hypothesis `a <= b` stands for: a procedure
;; from `a` to `b`, of effect `spin`.
(define k-coercion (subr (maxeff kstate spin) ((pairof int int @t) k-eff) int)
  (lambda (h spin)
    (k-ty-new (ty-subr spin (the k-ids (cons (car h) nil)) (cdr h) (get k-conv-default)))))
;; What a use of `name` with `have` descriptions, not `want`, says.
(define k-arity-message (subr (read @globals) (symbol int int) string)
  (lambda (name want have)
    (k-cat5 (k-quote (symbol->string name)) " takes " (int->string want)
            " description(s), and has " (int->string have))))
;; Whether a name meaning `d` stands for a type when applied to
;; descriptions: a type family, or a generative type.
(define k-ds-applied? (subr pure (k-ds) bool)
  (lambda (d)
    (tagcase d
      (ds-abbrev (ps body) #t)
      (ds-gen (g) #t)
      (ds-var (v k) (>= k 100))
      (ds-fun (f) #t)
      (else x #f))))

;; The `select` a name meaning `d` (none or one) is defined as, `(define-type
;; f (select m f))`, if it is: applied, it is that `select` applied, as
;; `((select m f) d …)` is (`TODO.md` §34); else -1.
(define k-select-alias (subr (maxeff kreads spin) ((listof k-ds acyclic)) int)
  (lambda (d)
    (if (null? d)
        -1
        (tagcase (car d)
          (ds-rec (t) (tagcase (k-get t) (ty-select (m n) (k-resolve t)) (else y -1)))
          (else x -1)))))

;; `(moduleof …)` and `(select m t)`, read by `check-modules.fx`, which sets this.
(define k-module-type-head? (subr pure (symbol) bool)
  (lambda (hd) (or (symbol=? hd 'moduleof) (symbol=? hd 'select))))

;; Type family `name`, used at `s`, expanding without end.
(define k-endless (subr (maxeff checks spin) (syn symbol) void)
  (lambda (s name)
    (k-sfail (k-cat3 (k-quote (symbol->string name))
                     " expands without end: "
                     "a type family may mention itself only with the same descriptions")
             s)))
(define-rec
  ;; A size: a natural literal, or `finite`, some number not known.
  (k-parse-size (subr (maxeff checks spin) (syn) k-size)
    (lambda (s)
      (let ((usage (string-append "a size is a natural number, `finite`, a size variable, "
                                  "`(+ size …)` or `(- size k)`")))
        (cond ((>= (syn-int s) 0) (k-size-lit (syn-int s)))
              ((syn-symbol? s) (k-size-named s usage))
              (else (k-parse-size-form s usage))))))
  ;; `(+ size …)` or `(- size k)`.
  (k-parse-size-form (subr (maxeff checks spin) (syn string) k-size)
    (lambda (s usage)
      (let* ((items (k-items s "a size")) (hd (k-symbol-head items)))
        (cond ((and (string=? hd "+") (not (null? (cdr items))))
               (k-parse-size-sum (cdr items) (k-size-lit 0)))
              ((and (string=? hd "-") (= (k-length items) 3))
               (let ((a (k-parse-size (k-nth items 1))) (k (syn-int (k-nth items 2))))
                 (if (>= k 0) (k-size-plus a (- 0 k)) (k-sfail usage (k-nth items 2)))))
              (else (k-sfail usage s))))))
  (k-parse-size-sum (subr (maxeff checks spin) (k-syns k-size) k-size)
    (lambda (xs out)
      (if (null? xs)
          out
          (k-parse-size-sum (cdr xs) (k-size-add-scaled out (k-parse-size (car xs)) 1)))))
  (k-hyp-coercions (subr (maxeff checks spin) (k-hyps k-eff k-ids) k-ids)
    (lambda (hs spin tail)
      (if (null? hs)
          tail
          (let ((c (k-coercion (car hs) spin)))
            (cons c (k-hyp-coercions (cdr hs) spin tail))))))
)

;; `(define-type name type)`: `name` stands for the type from here on, and
;; may appear in its own definition.
;; While a program's types are declared ahead (`k-ahead`): each
;; abbreviation's slot, made before any is read so that they may name each
;; other in any order; and those filled, with where, to check grounded once
;; all are.
(define-type k-ahead-slots (listof (pairof symbol int @t) acyclic))
(define-type k-filled (listof (productof (1 int) (2 int) (3 int)) acyclic))
(define k-ahead-names (ref k-ahead-slots @t) (new nil))
(define k-ahead-filled (ref k-filled @t) (new nil))
;; `xs` less `name`'s entry.
(define k-ahead-drop (subr (maxeff kreads (alloc @t)) (k-ahead-slots symbol) k-ahead-slots)
  (lambda (xs name)
    (cond ((null? xs) nil)
          ((symbol=? (car (car xs)) name) (cdr xs))
          (else (cons (car xs) (k-ahead-drop (cdr xs) name))))))
(define k-ahead-find (subr kreads (k-ahead-slots symbol) int)
  (lambda (xs name)
    (cond ((null? xs) -1)
          ((symbol=? (car (car xs)) name) (cdr (car xs)))
          (else (k-ahead-find (cdr xs) name)))))
;; `name`'s slot declared ahead, taken from those waiting; or -1.
(define* k-ahead-take (subr kstate (symbol) int)
  (lambda (name)
    (let ((found (k-ahead-find (get k-ahead-names) name)))
      (begin
        (if (>= found 0) (set k-ahead-names (k-ahead-drop (get k-ahead-names) name)) #u)
        found))))
;; How many times `n` is among `ns`.
(define k-name-count (subr (read @globals) (k-names symbol) int)
  (lambda (ns n)
    (cond ((null? ns) 0)
          ((symbol=? (car ns) n) (+ 1 (k-name-count (cdr ns) n)))
          (else (k-name-count (cdr ns) n)))))
;; A slot in scope for each of `ns` given once among `all`, first first.
(define* k-ahead-declare (subr (maxeff checks spin) (k-names k-names) unit)
  (lambda (ns all)
    (if (null? ns)
        #u
        (begin
          (if (= (k-name-count all (car ns)) 1)
              (let ((slot (k-slot)))
                (begin (k-push-desc (car ns) (ds-rec slot))
                       (set k-ahead-names (cons (cons (car ns) slot) (get k-ahead-names)))))
              #u)
          (k-ahead-declare (cdr ns) all)))))
(define k-filled-reversed (subr (read @globals) (k-filled k-filled) k-filled)
  (lambda (xs acc) (if (null? xs) acc (k-filled-reversed (cdr xs) (cons (car xs) acc)))))
(define* k-ground-filled (subr (maxeff checks spin) (k-filled) unit)
  (lambda (fs)
    (if (null? fs)
        #u
        (begin (k-grounded (extract (car fs) 1) (extract (car fs) 2) (extract (car fs) 3))
               (k-ground-filled (cdr fs))))))))

(define k-shape (with check-syntax-module k-shape))
(define k-define-family (with check-syntax-module k-define-family))
(define k-knots (with check-syntax-module k-knots))
(define k-list-head (with check-syntax-module k-list-head))
(define k-parse-conv (with check-syntax-module k-parse-conv))
(define k-twice (with check-syntax-module k-twice))
(define k-type-kind? (with check-syntax-module k-type-kind?))
(define k-endless (with check-syntax-module k-endless))
(define k-parse-size (with check-syntax-module k-parse-size))
(define k-ahead-names (with check-syntax-module k-ahead-names))
(define k-ahead-filled (with check-syntax-module k-ahead-filled))
(define k-ahead-declare (with check-syntax-module k-ahead-declare))
(define k-filled-reversed (with check-syntax-module k-filled-reversed))
(define k-ground-filled (with check-syntax-module k-ground-filled))
(define-type k-slots (select check-syntax-module k-slots))
(define k-effect-atom (with check-syntax-module k-effect-atom))
(define k-syn-label (with check-syntax-module k-syn-label))
(define k-has-label? (with check-syntax-module k-has-label?))
(define k-storage-head? (with check-syntax-module k-storage-head?))
(define k-hyp-coercions (with check-syntax-module k-hyp-coercions))
(define k-stated-lemma (with check-syntax-module k-stated-lemma))
(define k-arity-message (with check-syntax-module k-arity-message))
(define k-select-alias (with check-syntax-module k-select-alias))
(define k-ds-applied? (with check-syntax-module k-ds-applied?))
(define k-parse-conv-form (with check-syntax-module k-parse-conv-form))
(define k-module-type-head? (with check-syntax-module k-module-type-head?))
(define k-dletrec-slots (with check-syntax-module k-dletrec-slots))
(define k-dletrec-grounded (with check-syntax-module k-dletrec-grounded))
(define k-dletrec-no-knot (with check-syntax-module k-dletrec-no-knot))
(define k-grounded (with check-syntax-module k-grounded))
(define k-knot-of (with check-syntax-module k-knot-of))
(define k-push-all (with check-syntax-module k-push-all))
(define k-ahead-take (with check-syntax-module k-ahead-take))
