;;; The checker, in FX-26: descriptions read from their syntax into the arena:
;;; effects, regions, types, and the expressions that hold them, reading
;;; them by the pieces `check-read.fx` gives before it. Part of the checker,
;;; `check-types.fx` first (PLAN.md §11, step 10).

(define-rec
  (k-effects (subr (maxeff checks spin) (k-syns) k-eff)
    (lambda (xs)
      (if (null? xs)
          nil
          (let* ((e (k-parse-effect (car xs))) (rest (k-effects (cdr xs)))) (k-union e rest)))))
  (k-parse-effect (subr (maxeff checks spin) (syn) k-eff)
    (lambda (s)
      (if (syn-symbol? s)
          (k-effect-named s)
          (let* ((items (k-items s "an effect"))
                 (head (k-head items))
                 ;; `(select m e)`: module `m`'s effect `e`, found where the
                 ;; type it is in is checked, as a type's `select` is.
                 (selected (if (string=? head "select")
                               (k-effect-selected s items)
                               (the (listof k-eff acyclic) nil)))
                 ;; `(e d …)`: a description function to an effect, applied.
                 (applied (if (null? selected) ((get k-effect-app-reader) s items) selected)))
            (cond ((not (null? selected)) (car selected))
                  ((not (null? applied)) (car applied))
                  ((string=? head "maxeff") (k-effects (cdr items)))
                  ((k-atom-head? head)
                   (if (= (k-length items) 2)
                       (k-effect-atom head (k-nth items 1))
                       (k-sfail (k-cat3 "`(" head " region)`") s)))
                  (else (k-sfail "expected an effect" s)))))))
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
;; A type family's parameters: each one's name and kind.
(define-type k-params (listof (productof (1 symbol) (2 int)) acyclic))
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
(define k-parse-module-type (ref (subr (maxeff checks spin) (syn k-syns symbol) int) @t)
  (new (lambda (s items hd) (k-sfail "expected a type" s))))

;; Type family `name`, used at `s`, expanding without end.
(define k-endless (subr (maxeff checks spin) (syn symbol) void)
  (lambda (s name)
    (k-sfail (k-cat3 (k-quote (symbol->string name))
                     " expands without end: "
                     "a type family may mention itself only with the same descriptions")
             s)))
(define-rec
  (k-parse-types (subr (maxeff checks spin) (k-syns) k-ids)
    (lambda (xs)
      (if (null? xs)
          nil
          (let* ((t (k-parse-type (car xs))) (rest (k-parse-types (cdr xs)))) (cons t rest)))))
  (k-parse-parts (subr (maxeff checks spin) (k-syns k-parts) k-parts)
    (lambda (ps done)
      (if (null? ps)
          (reverse done)
          (let ((pair (k-items (car ps) "`(label type)`")))
            (if (= (k-length pair) 2)
                (let ((l (k-syn-label (car pair))))
                  (if (k-has-label? done l)
                      (k-sfail (k-twice (symbol->string l)) (car ps))
                      (let ((t (k-parse-type (k-nth pair 1))))
                        (k-parse-parts (cdr ps) (cons (product (1 l) (2 t)) done)))))
                (k-sfail "`(label type)`" (car ps)))))))
  ;; Storage written: a procedure kept there may not reach itself unsaid
  ;; (`spin`).
  (k-parse-type (subr (maxeff checks spin) (syn) int)
    (lambda (s)
      (let ((t (k-parse-type-node s)))
        (begin
          (if (and (not (syn-symbol? s)) (k-storage-head? (k-head (k-items s "a type"))))
              (k-no-knot t (syn-start s) (syn-end s))
              #u)
          t))))
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
  ;; What `(proves prop)` states: the type of its proof, with the lemma kept
  ;; pending for the definition it declares.
  (k-parse-proves (subr (maxeff checks spin) (syn string) int)
    (lambda (prop usage)
      (let* ((items (k-items prop "a proposition"))
             (head (k-symbol-head items))
             (poly? (string=? head "poly"))
             (shape (cond (poly? (if (>= (k-length items) 3) #u (k-sfail usage prop)))
                          ((string=? head "<=") #u)
                          (else (k-sfail usage prop))))
             (bs (if poly? (k-parse-binders (k-nth items 1)) (the k-binders nil)))
             (conc (k-le (if poly? (k-nth items 2) prop)))
             (hyps (if poly? (k-les (cdr (cdr (cdr items)))) (the k-hyps nil)))
             (spin (k-one (a-spin)))
             (params (k-hyp-coercions hyps spin (the k-ids (cons (car conc) nil))))
             (body (k-ty-new (ty-subr spin params (cdr conc) (get k-conv-default))))
             (t (if (null? bs) body (k-ty-new (ty-poly bs body)))))
        (begin
          (set k-pending-lemma (cons (k-stated-lemma bs conc hyps) nil))
          t))))
  (k-le (subr (maxeff checks spin) (syn) (pairof int int @t))
    (lambda (s)
      (let ((items (k-items s "a proposition")))
        (if (and (= (k-length items) 3) (string=? (k-symbol-head items) "<="))
            (let* ((a (k-parse-type (k-nth items 1))) (b (k-parse-type (k-nth items 2))))
              (cons a b))
            (k-sfail "a proposition is `(<= type type)`" s)))))
  (k-les (subr (maxeff checks spin) (k-syns) k-hyps)
    (lambda (xs)
      (if (null? xs) nil (let* ((h (k-le (car xs))) (rest (k-les (cdr xs)))) (cons h rest)))))
  (k-hyp-coercions (subr (maxeff checks spin) (k-hyps k-eff k-ids) k-ids)
    (lambda (hs spin tail)
      (if (null? hs)
          tail
          (let ((c (k-coercion (car hs) spin)))
            (cons c (k-hyp-coercions (cdr hs) spin tail))))))
  ;; `(name d …)` for the `g`th generative type: a node, never expanded.
  (k-apply-gen (subr (maxeff checks spin) (syn int k-syns) int)
    (lambda (s g args)
      (let* ((gen (k-gen-of g)) (ps (extract gen 2)))
        (if (not (= (k-length args) (k-length ps)))
            (k-sfail (k-arity-message (extract gen 1) (k-length ps) (k-length args)) s)
            (let ((t (k-ty-new (ty-named g (k-gen-args ps args)))))
              ;; What it holds may keep a procedure that reaches itself.
              (begin (k-no-knot t (syn-start s) (syn-end s)) t))))))
  (k-gen-args (subr (maxeff checks spin) (k-binders k-syns) k-descs)
    (lambda (ps args)
      (if (null? ps)
          nil
          (let* ((k (extract (car ps) 2))
                 (d (cond ((k-type-kind? k) (dt (k-parse-type (car args))))
                          ((= k 0) (dr (k-parse-region (car args))))
                          ((= k 3) (dr (k-parse-place (car args))))
                          ((= k 5) (dz (k-parse-size (car args))))
                          ((= k 6) (dc (k-parse-conv (car args))))
                          ((>= k 100) (df ((get k-fun-reader) (car args) k)))
                          (else (de (k-parse-effect (car args))))))
                 (rest (k-gen-args (cdr ps) (cdr args))))
            (cons d rest)))))
  ;; The type a name stands for.
  (k-type-named (subr (maxeff checks spin) (syn) int)
    (lambda (s)
      (let* ((n (syn-name s)) (sym (string->symbol n)) (base (k-find (get k-base) sym)))
        (cond ((string=? n "void") k-void)
              ((and (string=? n "nat") (null? (k-lookup-desc sym)))
               (k-ty-new (ty-nat (sz-finite))))
              ((>= base 0) base)
              (else
               (let ((d (k-lookup-desc sym))
                     (no (lambda () (string-append (k-quote n) " is not a type"))))
                 (if (null? d)
                     (k-sfail (no) s)
                     (tagcase (car d)
                       (ds-var (v k)
                         (cond ((k-type-kind? k) (k-ty-new (ty-var v)))
                               ((k-arrow-kind? k) (k-sfail (k-not-applied n k) s))
                               (else (k-sfail (no) s))))
                       (ds-fun (f)
                         (let ((k (k-fun-kind f))) (k-sfail (k-not-applied n (if (< k 0) 2 k)) s)))
                       (ds-rec (t) t)
                       (ds-gen (g) (k-apply-gen s g nil))
                       (else x (k-sfail (no) s))))))))))
  (k-parse-type-node (subr (maxeff checks spin) (syn) int)
    (lambda (s)
      (if (syn-symbol? s)
          (k-type-named s)
          (let* ((items (k-items s "a type"))
                 (hd (if (null? items) '|()| (syn-head (car items))))
                 (abbrev (if (symbol=? hd '|()|)
                             (the (listof k-ds acyclic) nil)
                             (k-lookup-desc hd)))
                 (alias (k-select-alias abbrev)))
            (cond ((and (not (null? abbrev)) (k-ds-applied? (car abbrev)))
                   (tagcase (car abbrev)
                     (ds-abbrev (ps body) (k-expand-abbrev s hd ps body (cdr items)))
                     (ds-gen (g) (k-apply-gen s g (cdr items)))
                     ;; A description function applied (`check-kinds.fx`).
                     (ds-var (v k) ((get k-app-reader) s (k-ty-new (ty-var v)) (cdr items)))
                     (ds-fun (f) ((get k-app-reader) s f (cdr items)))
                     (else x (k-sfail "an abbreviation" s))))
                  ((>= alias 0) ((get k-app-reader) s alias (cdr items)))
                  ;; `((dlambda …) d …)` and `((select m f) d …)`.
                  ((and (not (null? items)) (tagcase (car items) (lst (xs d a b) #t) (else x #f)))
                   ((get k-app-reader) s ((get k-fun-reader) (car items) -1) (cdr items)))
                  (else (k-parse-type-form s items hd)))))))
  ;; `(subr effect (param …) result)`, or with a convention first, `(subr
  ;; (conv C) effect (param …) result)`; left out, it is the program's.
  (k-parse-subr (subr (maxeff checks spin) (syn k-syns) int)
    (lambda (s items)
      (let* ((conv? (and (= (k-length items) 5) (string=? (k-list-head (k-nth items 1)) "conv")))
             (cv (if conv? (k-parse-conv-form (k-nth items 1)) (get k-conv-default)))
             (items (if conv? (the k-syns (cons (car items) (cdr (cdr items)))) items)))
        (begin
          (k-shape (= (k-length items) 4) "`(subr effect (param …) result)`" s)
          (let* ((e (k-parse-effect (k-nth items 1)))
                 (ts ((get k-parse-params) (k-items-or-nil (k-nth items 2) "parameter types")
                                           (k-nth items 3))))
            (k-ty-new (ty-subr e (k-ids-but-last ts) (k-ids-last ts) cv)))))))
  ;; `(proves prop)`.
  (k-parse-proves-type (subr (maxeff checks spin) (syn k-syns) int)
    (lambda (s items)
      (let ((usage (string-append "`(proves (<= type type))` or `(proves (poly ((name kind) …) "
                                  "(<= type type) (<= type type) …))`")))
        (begin
          (k-shape (= (k-length items) 2) usage s)
          (let* ((saved (get k-dscope)) (t (k-parse-proves (k-nth items 1) usage)))
            (begin (set k-dscope saved) t))))))
  ;; A type written as a form, `(hd …)`, `hd` no family's name.
  (k-parse-type-form (subr (maxeff checks spin) (syn k-syns symbol) int)
    (lambda (s items hd)
      (let ((n (k-length items)))
        (cond
          ((symbol=? hd 'subr) (k-parse-subr s items))
          ((symbol=? hd 'proves) (k-parse-proves-type s items))
          ((symbol=? hd 'poly)
           (begin
             (k-shape (= n 3) "`(poly ((name kind) …) type)`" s)
             (let* ((saved (get k-dscope))
                    (bs (k-parse-binders (k-nth items 1)))
                    (body (k-parse-type (k-nth items 2))))
               (begin (set k-dscope saved) (k-ty-new (ty-poly bs body))))))
          ((symbol=? hd 'nlist)
           (begin
             (k-shape (or (= n 3) (= n 4)) "`(nlist type size)` or `(nlist type size place)`" s)
             (let* ((e (k-parse-type (k-nth items 1)))
                    (z (k-parse-size (k-nth items 2)))
                    (r (if (= n 4)
                           (k-frozen-into (k-parse-place (k-nth items 3)) #t)
                           (r-frozen -1 #t))))
               (k-ty-new (ty-nlist e z r)))))
          ((symbol=? hd 'nat)
           (begin
             (k-shape (= n 2) "`(nat size)`" s)
             (k-ty-new (ty-nat (k-parse-size (k-nth items 1))))))
          ((symbol=? hd 'ref)
           (begin
             (k-shape (= n 3) "`(ref type region)`" s)
             (let* ((t (k-parse-type (k-nth items 1))) (r (k-parse-region (k-nth items 2))))
               (k-ty-new (ty-ref t r)))))
          ((symbol=? hd 'pairof)
           (begin
             (k-shape (= n 4) "`(pairof type type region)`" s)
             (let* ((a (k-parse-type (k-nth items 1))) (b (k-parse-type (k-nth items 2)))
                    (r (k-parse-region (k-nth items 3))))
               (k-ty-new (ty-pair a b r)))))
          ((symbol=? hd 'dletrec) (k-parse-dletrec s items))
          ((symbol=? hd 'mu) (k-parse-mu s items))
          ((symbol=? hd 'listof)
           (begin
             (k-shape (= n 3) "`(listof type region)`" s)
             (let* ((t (k-parse-type (k-nth items 1))) (r (k-parse-region (k-nth items 2)))
                    (slot (k-slot)) (pair (k-ty-new (ty-pair t slot r))))
               (begin (k-set-link slot pair) slot))))
          ((symbol=? hd 'prompt-tag)
           (begin
             (k-shape (= n 5) "`(prompt-tag answer payload effect region)`" s)
             (let* ((a (k-parse-type (k-nth items 1))) (h (k-parse-type (k-nth items 2)))
                    (e (k-parse-effect (k-nth items 3))) (r (k-parse-region (k-nth items 4))))
               (k-ty-new (ty-tag a h e r)))))
          ((symbol=? hd 'composable)
           (begin
             (k-shape (= n 5) "`(composable argument answer effect region)`" s)
             (let* ((t (k-parse-type (k-nth items 1))) (a (k-parse-type (k-nth items 2)))
                    (e (k-parse-effect (k-nth items 3))) (r (k-parse-region (k-nth items 4))))
               (k-ty-new (ty-comp t a e r)))))
          ((symbol=? hd 'bloblet)
           (begin
             (k-shape (= n 3) "`(bloblet (fields type …) region)`, or `(frozen type …)`" s)
             (let* ((fields (k-nth items 1))
                    (parts (k-items fields "`(fields type …)`"))
                    (which (k-head parts)))
               (if (or (string=? which "fields") (string=? which "frozen"))
                   (let* ((fs (k-parse-types (cdr parts))) (r (k-parse-region (k-nth items 2))))
                     (k-ty-new (ty-bloblet fs (string=? which "frozen") r)))
                   (k-sfail "`(fields type …)` or `(frozen type …)`" fields)))))
          ((k-module-type-head? hd) ((get k-parse-module-type) s items hd))
          ((symbol=? hd 'productof) (k-ty-new (ty-product (k-parse-parts (cdr items) nil))))
          ((symbol=? hd 'sumof) (k-ty-new (ty-sum (k-parse-parts (cdr items) nil))))
          ((symbol=? hd 'arrayof)
           (begin
             (k-shape (= n 3) "`(arrayof type region)`" s)
             (let* ((t (k-parse-type (k-nth items 1))) (r (k-parse-region (k-nth items 2))))
               (k-ty-new (ty-array t r)))))
          ((symbol=? hd 'icell)
           (begin
             (k-shape (= n 3) "`(icell type region)`" s)
             (let* ((t (k-parse-type (k-nth items 1))) (r (k-parse-region (k-nth items 2))))
               (k-ty-new (ty-icell t r)))))
          ((symbol=? hd 'place)
           (begin
             (k-shape (= n 2) "`(place region)`" s)
             (k-ty-new (ty-place (k-parse-place (k-nth items 1))))))
          ((symbol=? hd 'mark-key)
           (begin
             (k-shape (= n 3) "`(mark-key type region)`" s)
             (let* ((t (k-parse-type (k-nth items 1))) (r (k-parse-region (k-nth items 2))))
               (k-ty-new (ty-markkey t r)))))
          (else (k-sfail "expected a type" s))))))
  ;; `(dletrec ((name type) …) type)`: each name gets a forwarding slot
  ;; before any body is read, so the bodies can refer to it and each other.
  (k-parse-dletrec (subr (maxeff checks spin) (syn k-syns) int)
    (lambda (s items)
      (begin
        (k-shape (= (k-length items) 3) "`(dletrec ((name type) …) type)`" s)
        (let* ((saved (get k-dscope))
               (slots (k-dletrec-slots (k-items (k-nth items 1) "dletrec bindings")))
               (filled (k-dletrec-fill slots))
               (grounded (k-dletrec-grounded slots s))
               (unknotted (k-dletrec-no-knot slots s))
               (body (k-parse-type (k-nth items 2))))
          (begin (set k-dscope saved) body)))))
  ;; `(mu name type)`: a recursive type, anonymous; the same as `(dletrec
  ;; ((name type)) name)`.
  (k-parse-mu (subr (maxeff checks spin) (syn k-syns) int)
    (lambda (s items)
      (begin
        (k-shape (= (k-length items) 3) "`(mu name type)`" s)
        (let* ((name (k-name-of (k-nth items 1) "a name"))
               (saved (get k-dscope))
               (slot (k-slot))
               (pushed (k-push-desc name (ds-rec slot)))
               (t (k-parse-type (k-nth items 2)))
               (restored (set k-dscope saved))
               (filled (k-set-link slot t))
               (grounded (k-grounded slot (syn-start s) (syn-end s))))
          slot))))
  (k-dletrec-fill (subr (maxeff checks spin) (k-slots) unit)
    (lambda (ss)
      (if (null? ss)
          #u
          (let ((t (k-parse-type (cdr (car ss)))))
            (begin (k-set-link (car (car ss)) t) (k-dletrec-fill (cdr ss)))))))
  ;; A use of a parametric abbreviation: its body, read with each parameter
  ;; bound to the description given for it.
  (k-expand-abbrev (subr (maxeff checks spin) (syn symbol k-params syn k-syns) int)
    (lambda (s name ps body args)
      (cond
        ((not (= (k-length args) (k-length ps)))
         (k-sfail (k-arity-message name (k-length ps) (k-length args)) s))
        ((> (get k-expanding) 64) (k-endless s name))
        (else (k-expand-bound s name body (k-abbrev-args ps args))))))
  ;; The family `name`'s body, read with its parameters bound as `bound`
  ;; says: a use inside with the same descriptions is the slot its type
  ;; will fill, a knot.
  (k-expand-bound (subr (maxeff checks spin) (syn symbol syn k-scope) int)
    (lambda (s name body bound)
      (let ((knot (k-knot-of (get k-knots) name bound)))
        (if (>= knot 0)
            knot
            (let* ((saved (get k-dscope)) (slot (k-slot)) (kept (get k-knots)))
              (begin
                (set k-knots (cons (product (1 name) (2 bound) (3 slot)) kept))
                (k-push-all bound)
                (set k-expanding (+ (get k-expanding) 1))
                (let ((t (k-parse-type body)))
                  (begin (set k-expanding (- (get k-expanding) 1))
                         (set k-dscope saved)
                         (set k-knots kept)
                         (k-set-link slot t)
                         (k-grounded slot (syn-start s) (syn-end s))
                         slot))))))))
  (k-abbrev-args (subr (maxeff checks spin) (k-params k-syns) k-scope)
    (lambda (ps args)
      (if (null? ps)
          nil
          (let* ((k (extract (car ps) 2))
                 (d (cond ((k-type-kind? k) (ds-rec (k-parse-type (car args))))
                          ((= k 0) (ds-region (k-parse-region (car args))))
                          ((= k 3) (ds-region (k-parse-place (car args))))
                          ((= k 5) (ds-size (k-parse-size (car args))))
                          ((= k 6) (ds-conv (k-parse-conv (car args))))
                          ((>= k 100) (ds-fun ((get k-fun-reader) (car args) k)))
                          (else (ds-eff (k-parse-effect (car args))))))
                 (rest (k-abbrev-args (cdr ps) (cdr args))))
            (cons (cons (extract (car ps) 1) d) rest))))))

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
(define* k-define-type (subr (maxeff checks spin) (symbol syn int int) int)
  (lambda (name def a b)
    (let ((ahead (k-ahead-take name)))
      (if (>= ahead 0)
          ;; Declared ahead: its slot is in scope already; fill it, and check
          ;; it grounded once every slot is filled.
          (let ((t (k-parse-type def)))
            (begin (k-set-link ahead t)
                   (set k-ahead-filled (cons (product (1 ahead) (2 a) (3 b)) (get k-ahead-filled)))
                   ahead))
          (let ((slot (k-slot)))
            (begin
              (k-push-desc name (ds-rec slot))
              (let ((t (k-parse-type def)))
                (begin (k-set-link slot t) (k-grounded slot a b) slot))))))))
