;;; The checker, in FX-26: what reading descriptions from their syntax into
;;; the arena needs before it (`check-read-descs.fx` reads them, by the
;;; pieces `check-read.fx` gives): regions, effects' atoms, labels, `dletrec`
;;; knots, `define-type`'s forward names. Part of the checker,
;;; `check-types.fx` first (PLAN.md §11, step 10).

;; Its types, those it uses of the files before it, and the signatures of
;; what it is given.
;; Its types (`check-syntax-types.fx`), loaded before the module so that they are not
;; among its values; the module names what it uses of them.
(let* ((check-syntax-types (load-module "fx26:check-syntax-types.fx"))
       (check-types-types (load-module "fx26:check-types-types.fx"))
       (check-read-types (load-module "fx26:check-read-types.fx"))
       (check-env-types (load-module "fx26:check-env-types.fx"))
       (eager-reader-types ((proj (load-module "fx26:eager-reader-types.fx") @s @e @m @c)))
       (parser-types ((proj (load-module "fx26:parser-types.fx") @s @e @m @c @p)))
       (check-unions-types (load-module "fx26:check-unions-types.fx"))
       (check-print-types (load-module "fx26:check-print-types.fx"))
       (check-print-parts-types (load-module "fx26:check-print-parts-types.fx"))
       (check-effects-types (load-module "fx26:check-effects-types.fx"))
       (check-holds-types (load-module "fx26:check-holds-types.fx"))
       (reader-types (load-module "fx26:reader-types.fx")))
  ;; What it is given: the modules of the files before it that it uses.
  (lambda ((check-types (select check-types-types check-types-sig))
           (check-read (select check-read-types check-read-sig))
           (check-unions (select check-unions-types check-unions-sig))
           (check-print (select check-print-types check-print-sig))
           (check-effects (select check-effects-types check-effects-sig))
           (check-env (select check-env-types check-env-sig))
           (check-holds (select check-holds-types check-holds-sig))
           (parser (select reader-types parser-sig))
           (check-print-parts (select check-print-parts-types check-print-parts-sig)))
    (module
(define-type k-slots (select check-syntax-types k-slots))
(define-type k-family-knot (select check-syntax-types k-family-knot))
(define-type k-ahead-slots (select check-syntax-types k-ahead-slots))
(define-type k-filled (select check-syntax-types k-filled))
;; The types it uses of the files before it.
(define-effect checks (select check-types-types checks))
(define cv-cellular (with check-types-types cv-cellular))
(define cv-fx (with check-types-types cv-fx))
(define cv-native (with check-types-types cv-native))
(define cv-var (with check-types-types cv-var))
(define ds-abbrev (with check-types-types ds-abbrev))
(define ds-conv (with check-types-types ds-conv))
(define ds-eff (with check-types-types ds-eff))
(define ds-fun (with check-types-types ds-fun))
(define ds-gen (with check-types-types ds-gen))
(define ds-rec (with check-types-types ds-rec))
(define ds-region (with check-types-types ds-region))
(define ds-size (with check-types-types ds-size))
(define ds-var (with check-types-types ds-var))
(define dt (with check-types-types dt))
(define-type k-binders (select check-types-types k-binders))
(define-type k-conv (select check-types-types k-conv))
(define-type k-desc (select check-types-types k-desc))
(define-type k-descs (select check-types-types k-descs))
(define-type k-ds (select check-types-types k-ds))
(define-type k-eff (select check-types-types k-eff))
(define-type k-hyps (select check-types-types k-hyps))
(define-type k-ids (select check-types-types k-ids))
(define-type k-lemma (select check-types-types k-lemma))
(define-type k-named (select check-types-types k-named))
(define-type k-names (select check-types-types k-names))
(define-type k-parts (select check-types-types k-parts))
(define-type k-size (select check-types-types k-size))
(define-effect kreads (select check-types-types kreads))
(define-effect kstate (select check-types-types kstate))
(define sz-finite (with check-types-types sz-finite))
(define ty-app (with check-types-types ty-app))
(define ty-link (with check-types-types ty-link))
(define ty-named (with check-types-types ty-named))
(define ty-poly (with check-types-types ty-poly))
(define ty-select (with check-types-types ty-select))
(define ty-subr (with check-types-types ty-subr))
(define ty-var (with check-types-types ty-var))
(define-type k-items (select check-types-types k-items))
(define-type k-params (select check-read-types k-params))
(define-type k-syns (select check-read-types k-syns))
(define-type k-scope (select check-env-types k-scope))
(define lst (with eager-reader-types lst))
(define-type syn (select parser-types syn))
;; What it uses of the modules it is given.
(define k-cat3 (with check-types k-cat3))
(define k-cat5 (with check-types k-cat5))
(define k-desc-types (with check-types k-desc-types))
(define k-fail (with check-types k-fail))
(define k-gen-of (with check-types k-gen-of))
(define k-get (with check-types k-get))
(define k-has-id? (with check-types k-has-id?))
(define k-length (with check-types k-length))
(define k-nth (with check-types k-nth))
(define k-quote (with check-types k-quote))
(define k-raw (with check-types k-raw))
(define k-resolve (with check-types k-resolve))
(define k-slot (with check-types k-slot))
(define k-ty-new (with check-types k-ty-new))
(define k-atom-of (with check-read k-atom-of))
(define k-atoms-on (with check-read k-atoms-on))
(define k-globals-region (with check-read k-globals-region))
(define k-head (with check-read k-head))
(define k-items (with check-read k-items))
(define k-name-of (with check-read k-name-of))
(define k-parse-kind (with check-read k-parse-kind))
(define k-parse-region (with check-read k-parse-region))
(define k-sfail (with check-read k-sfail))
(define k-symbol-head (with check-read k-symbol-head))
(define k-check-pending-unions (with check-unions k-check-pending-unions))
(define k-conv-default (with check-print-parts k-conv-default))
(define k-conv=? (with check-print-parts k-conv=?))
(define k-size-add-scaled (with check-print-parts k-size-add-scaled))
(define k-size-lit (with check-print-parts k-size-lit))
(define k-size-plus (with check-print-parts k-size-plus))
(define k-size-var (with check-print-parts k-size-var))
(define k-size=? (with check-print-parts k-size=?))
(define k-eff=? (with check-effects k-eff=?))
(define k-one (with check-effects k-one))
(define k-region=? (with check-effects k-region=?))
(define k-lookup-desc (with check-env k-lookup-desc))
(define k-push-desc (with check-env k-push-desc))
(define k-no-knot (with check-holds k-no-knot))
(define syn-end (with parser syn-end))
(define syn-head (with parser syn-head))
(define syn-int (with parser syn-int))
(define syn-name (with parser syn-name))
(define syn-start (with parser syn-start))
(define syn-symbol? (with parser syn-symbol?))

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
    (begin
      (if (k-through-apps? slot slot (the (ref k-ids @t) (new nil)))
          (k-fail-ungrounded a b)
          (k-grounded-from slot nil a b))
      ;; The unions read before it was, checked now their members are known.
      (k-check-pending-unions))))
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
          (case n (("cellular") (cv-cellular))
                  (("native") (cv-native))
                  (("fx") (cv-fx))
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
               (k-ground-filled (cdr fs)))))))))
