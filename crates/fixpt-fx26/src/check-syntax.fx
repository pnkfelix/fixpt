;;; The checker, in FX-26: descriptions read from their syntax into the arena.
;;; Part of the checker, `check-types.fx` first (PLAN.md §11, step 10).

;;; ------------------------------------------------------------ reading syntax

(define-type k-syns (listof syn acyclic))
(define k-sfail (subr checks (string syn) void)
  (lambda (m s) (k-fail m (syn-start s) (syn-end s))))
(define k-items (subr checks (syn string) k-syns)
  (lambda (s what)
    (tagcase s
      (lst (items d a b) items)
      (else x (k-sfail (string-append what ": expected a list") s)))))
(define k-head (subr (maxeff (read @globals) (read @s)) (k-syns) string)
  (lambda (items) (if (null? items) "" (syn-name (car items)))))
;; The name at the head of `items`, or "" if they do not start with one.
(define k-symbol-head (subr (maxeff (read @globals) (read @s)) (k-syns) string)
  (lambda (items)
    (if (and (not (null? items)) (syn-symbol? (car items))) (syn-name (car items)) "")))
(define k-name-of (subr checks (syn string) symbol)
  (lambda (s what) (if (syn-symbol? s) (syn-head s) (k-sfail what s))))
(define k-at-name? (subr pure (string) bool)
  (lambda (n) (and (> (string-length n) 0) (string=? (substring n 0 1) "@"))))
(define k-nil-syn? (subr (read @s) (syn) bool)
  (lambda (s) (tagcase s (lst (items d a b) (null? items)) (else x #f))))
;; The items of a list that may be written `()`.
(define k-items-or-nil (subr checks (syn string) k-syns)
  (lambda (s what) (if (k-nil-syn? s) nil (k-items s what))))

(define k-parse-kind (subr checks (syn) int)
  (lambda (s)
    (let ((n (if (syn-symbol? s) (syn-name s) ""))
          (usage "a kind is `region`, `place`, `effect`, `type`, `data`, `size` or `conv`"))
      (cond ((string=? n "region") 0)
            ((string=? n "place") 3)
            ((string=? n "effect") 1)
            ((string=? n "type") 2)
            ((string=? n "data") 4)
            ((string=? n "size") 5)
            ((string=? n "conv") 6)
            (else (k-sfail usage s))))))

;; `@globals`, or `(globals g …)` as the regions of each `g`, in a list of
;; one; none if `s` is neither.
(define k-global-names (subr (maxeff checks spin) (k-syns) k-regions)
  (lambda (ns)
    (if (null? ns)
        nil
        (let ((g (k-name-of (car ns) "a global's name")))
          (the k-regions (cons (r-global g) (k-global-names (cdr ns))))))))
;; `rs`, alone in a list.
(define k-regions-alone (subr pure (k-regions) (listof k-regions acyclic))
  (lambda (rs) (the (listof k-regions acyclic) (cons rs nil))))
(define k-globals-region (subr (maxeff checks spin) (syn) (listof k-regions acyclic))
  (lambda (s)
    (if (syn-symbol? s)
        (if (string=? (syn-name s) "@globals")
            (k-regions-alone (the k-regions (cons (r-globals) nil)))
            nil)
        (let ((items (k-items-or-nil s "a region")))
          (if (string=? (k-symbol-head items) "globals")
              (if (null? (cdr items))
                  (k-sfail "`(globals name …)`: at least one global" s)
                  (k-regions-alone (k-global-names (cdr items))))
              nil)))))
;; Each of `rs`, read (or written).
(define k-atoms-on (subr kbuilds (bool k-regions) k-eff)
  (lambda (read rs)
    (if (null? rs)
        nil
        (k-insert (if read (a-read (car rs)) (a-write (car rs))) (k-atoms-on read (cdr rs))))))
;; The region `@name` stands for: the program's own, if `private-regions`
;; declared it, and otherwise the constant of that name.
(define k-region-constant (subr (maxeff kreads (alloc @t)) (symbol) k-region)
  (lambda (sym)
    (let ((d (k-lookup-desc sym)))
      (if (null? d) (r-const sym) (tagcase (car d) (ds-private (r) r) (else x (r-const sym)))))))
;; The region a name stands for.
(define k-region-named (subr (maxeff checks spin) (syn) k-region)
  (lambda (s)
    (let* ((n (syn-name s)) (sym (string->symbol n)))
      (cond ((k-at-name? n) (k-region-constant sym))
            ((string=? n "const") (r-frozen -1 #f))
            ((string=? n "acyclic") (r-frozen -1 #t))
            ((string=? n "finite")
             (k-sfail "`finite` is a size; data with no cycle through it is at `acyclic`" s))
            ((string=? n "heap") (r-heap))
            (else
             (let ((d (k-lookup-desc sym))
                   (no (lambda () (string-append (k-quote n) " is not a region"))))
               (if (null? d)
                   (k-sfail (no) s)
                   (tagcase (car d)
                     (ds-var (v k) (if (or (= k 0) (= k 3)) (r-var v) (k-sfail (no) s)))
                     (ds-region (r) r)
                     (else x (k-sfail (no) s))))))))))
;; The region of data frozen into place `p`: `(acyclic p)` if `f`, else
;; `(const p)`.
(define k-frozen-into (subr (read @globals) (k-region bool) k-region)
  (lambda (p f) (tagcase p (r-var (v) (r-frozen v f)) (else y (r-frozen -1 f)))))
;; What a region that is not a place says.
(define k-not-place (subr kreads (k-region) string)
  (lambda (r) (string-append (k-quote (k-region-show r)) " is not a place")))

(define-rec
  (k-parse-region (subr (maxeff checks spin) (syn) k-region)
    (lambda (s)
      (cond ((not (null? (k-globals-region s)))
             (k-sfail (string-append "globals are a region only in effects: "
                                     "`(read @globals)`, `(write (globals g))`")
                      s))
            ((syn-symbol? s) (k-region-named s))
            (else (k-parse-frozen s)))))
  ;; `(const p)`: data frozen into place `p`; `(acyclic p)`, and never
  ;; written, so with no cycle through it.
  (k-parse-frozen (subr (maxeff checks spin) (syn) k-region)
    (lambda (s)
      (let* ((items (k-items-or-nil s "a region")) (head (k-symbol-head items)))
        (if (and (= (k-length items) 2) (or (string=? head "const") (string=? head "acyclic")))
            (let ((p (k-parse-place (k-nth items 1))) (f (string=? head "acyclic")))
              (k-frozen-into p f))
            (k-sfail "expected a region" s)))))
  ;; A place: a region that is one.
  (k-parse-place (subr (maxeff checks spin) (syn) k-region)
    (lambda (s)
      (let ((r (k-parse-region s)))
        (if (k-place? r) r (k-sfail (k-not-place r) s))))))

;; What a binder may be.
(define k-binder-shapes string
  (string-append "a binder is `(name kind)`, `(name region place)` "
                 "or `(name data place)`"))
;; A binder's bound, none or one, from what follows its kind: `(r region
;; p)` is a region that won't outlive `p`, a place bound before it.
(define k-parse-bound (subr (maxeff checks spin) (k-syns int) k-regions)
  (lambda (rest kind)
    (cond ((null? rest) (the k-regions nil))
          ((or (= kind 0) (= kind 4)) (the k-regions (cons (k-parse-place (car rest)) nil)))
          (else (k-sfail (string-append "only a region or data binder has a bound: "
                                        "`(name region place)` or `(name data place)`")
                         (car rest))))))
;; Note region variable `v`'s bound, if it has one.
(define k-note-bound (subr kstate (int k-regions) unit)
  (lambda (v bound)
    (if (null? bound) #u (set k-bounds (cons (cons v (car bound)) (get k-bounds))))))
(define k-binders-each (subr (maxeff checks spin) (k-syns) k-binders)
  (lambda (bs)
    (if (null? bs)
        nil
        (let ((pair (k-items (car bs) "a binder")))
          (if (or (= (k-length pair) 2) (= (k-length pair) 3))
              (let* ((name (k-name-of (car pair) "a binder's name"))
                     (kind (k-parse-kind (k-nth pair 1)))
                     (bound (k-parse-bound (cdr (cdr pair)) kind))
                     (v (k-new-dvar-of name kind))
                     (bounded (k-note-bound v bound))
                     (pushed (k-push-desc name (ds-var v kind)))
                     (rest (k-binders-each (cdr bs))))
                (cons (product (1 v) (2 kind)) rest))
              (k-sfail k-binder-shapes (car bs)))))))

;; `((name kind) …)`, binding each name for the rest of the reading.
(define k-parse-binders (subr (maxeff checks spin) (syn) k-binders)
  (lambda (s) (k-binders-each (k-items s "binders"))))

;; The effect a name stands for.
(define k-effect-named (subr (maxeff checks spin) (syn) k-eff)
  (lambda (s)
    (let ((n (syn-name s)))
      (cond ((string=? n "pure") nil)
            ((string=? n "spin") (k-one (a-spin)))
            (else
             (let ((d (k-lookup-desc (string->symbol n)))
                   (no (lambda () (string-append (k-quote n) " is not an effect"))))
               (if (null? d)
                   (k-sfail (no) s)
                   (tagcase (car d)
                     (ds-var (v k) (if (= k 1) (k-one (a-var v)) (k-sfail (no) s)))
                     (ds-eff (e) e)
                     (else x (k-sfail (no) s))))))))))
;; Whether `h` heads an atom of effect on a region: `(read r)` and so on.
(define k-atom-head? (subr pure (string) bool)
  (lambda (h)
    (or (string=? h "read") (string=? h "write") (string=? h "alloc")
        (string=? h "goto") (string=? h "comefrom") (string=? h "await"))))
;; The atom `(head r)`, `head` one `k-atom-head?` accepts.
(define k-atom-of (subr (read @globals) (string k-region) k-atom)
  (lambda (head r)
    (cond ((string=? head "read") (a-read r))
          ((string=? head "write") (a-write r))
          ((string=? head "alloc") (a-alloc r))
          ((string=? head "goto") (a-goto r))
          ((string=? head "await") (a-await r))
          (else (a-comefrom r)))))

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
          (let* ((items (k-items s "an effect")) (head (k-head items)))
            (cond ((string=? head "maxeff") (k-effects (cdr items)))
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

;; A name defined as another name, round a loop, describes nothing.
(define k-grounded (subr (maxeff checks spin) (int int int) unit)
  (lambda (slot a b) (k-grounded-from slot nil a b)))
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
(define k-family-params (subr checks (k-syns) k-params)
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
(define k-define-family (subr checks (symbol k-syns syn) unit)
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
  (lambda (d) (tagcase d (ds-abbrev (ps body) #t) (ds-gen (g) #t) (else x #f))))

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
                       (ds-var (v k) (if (k-type-kind? k) (k-ty-new (ty-var v)) (k-sfail (no) s)))
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
                             (k-lookup-desc hd))))
            (if (and (not (null? abbrev)) (k-ds-applied? (car abbrev)))
                (tagcase (car abbrev)
                  (ds-abbrev (ps body) (k-expand-abbrev s hd ps body (cdr items)))
                  (ds-gen (g) (k-apply-gen s g (cdr items)))
                  (else x (k-sfail "an abbreviation" s)))
                (k-parse-type-form s items hd))))))
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
                 (ps (k-parse-types (k-items-or-nil (k-nth items 2) "parameter types")))
                 (r (k-parse-type (k-nth items 3))))
            (k-ty-new (ty-subr e ps r cv)))))))
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
        ((> (get k-expanding) 64)
         (k-sfail (k-cat3 (k-quote (symbol->string name))
                          " expands without end: "
                          "a type family may mention itself only with the same descriptions")
                  s))
        (else
         (let* ((bound (k-abbrev-args ps args))
                (knot (k-knot-of (get k-knots) name bound)))
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
                            slot))))))))))
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
                          (else (ds-eff (k-parse-effect (car args))))))
                 (rest (k-abbrev-args (cdr ps) (cdr args))))
            (cons (cons (extract (car ps) 1) d) rest))))))

(define k-all-ints? (subr (read @globals) (k-ids int) bool)
  (lambda (xs n) (or (null? xs) (and (= (car xs) n) (k-all-ints? (cdr xs) n)))))
;; What parameter `v`, declared of variance `want`, says when it occurs
;; where it may not in generative type `name`.
(define k-variance-message (subr kreads (int int symbol) string)
  (lambda (v want name)
    (k-cat4 (k-quote (k-dvar-string v)) " is declared "
            (if (= want 0) "covariant (+)" "contravariant (-)")
            (k-cat3 " in " (k-quote (symbol->string name)) ", but occurs where it may not"))))
;; Whether parameter `v` of `gen`, declared of variance `want` (0 or 1),
;; occurs in its representation only so.
(define k-check-param-variance (subr (maxeff checks spin) (k-gen int int syn) unit)
  (lambda (gen v want s)
    (let ((found (the k-pols-found (new nil))))
      (begin
        (k-polarity (extract gen 4) v 0 (the k-seen-pol (new nil)) found)
        (if (k-all-ints? (get found) want)
            #u
            (k-sfail (k-variance-message v want (extract gen 1)) s))))))
;; Whether the `g`th generative type's representation bears out the variance
;; declared for its parameters.
(define k-check-variance (subr (maxeff checks spin) (int syn) unit)
  (lambda (g s)
    (let ((gen (k-gen-of g)))
      (letrec ((each (subr (maxeff checks spin) (k-binders k-ids) unit)
                     (lambda (bs vs)
                       (if (null? bs)
                           #u
                           (let ((v (extract (car bs) 1)) (want (car vs)))
                             (begin
                               (if (= want 2) #u (k-check-param-variance gen v want s))
                               (each (cdr bs) (cdr vs))))))))
        (each (extract gen 2) (extract gen 3))))))
;; `(define-generative (name (param kind [+|-]) …) rep)`, or with no
;; parameters `(define-generative name rep)`: a new type, equal only to
;; itself, converted by `up-name` and `down-name`.
;; A parameter's variance, from its items `(name kind [+|-])`: 0
;; covariant, 1 contravariant, 2 invariant (none given).
(define k-parse-variance (subr (maxeff checks spin) (k-syns syn) int)
  (lambda (items p)
    (let ((n (k-length items)))
      (cond ((= n 2) 2)
            ((= n 3)
             (let ((x (k-nth items 2)))
               (cond ((and (syn-symbol? x) (string=? (syn-name x) "+")) 0)
                     ((and (syn-symbol? x) (string=? (syn-name x) "-")) 1)
                     (else (k-sfail "a parameter's variance is `+` or `-`" x)))))
            (else
             (k-sfail "a parameter is `(name kind)`, `(name kind +)` or `(name kind -)`" p))))))
;; A region or place parameter `p` of kind `kind` must be invariant
;; (`v` 2): it names where data is.
(define k-check-invariant (subr checks (int int syn) unit)
  (lambda (v kind p)
    (if (and (not (= v 2)) (or (= kind 0) (= kind 3)))
        (k-sfail "a region or place parameter is invariant: it names where data is" p)
        #u)))
(define k-gen-params (subr (maxeff checks spin) (k-syns int) (productof (1 k-binders) (2 k-ids)))
  (lambda (ps depth)
    (if (null? ps)
        (product (1 (the k-binders nil)) (2 (the k-ids nil)))
        (let* ((p (car ps))
               (items (k-items p "a parameter"))
               (v (k-parse-variance items p))
               (name (k-name-of (car items) "a parameter's name"))
               (kind (k-parse-kind (k-nth items 1)))
               (checked (k-check-invariant v kind p))
               (dv (k-new-dvar-of name kind))
               (pushed (k-push-desc name (ds-var dv kind)))
               (rest (k-gen-params (cdr ps) depth)))
          (product (1 (the k-binders (cons (product (1 dv) (2 kind)) (extract rest 1))))
                   (2 (the k-ids (cons v (extract rest 2)))))))))
(define k-define-generative (subr (maxeff checks spin) (syn syn) symbol)
  (lambda (head rep)
    (let* ((hs (tagcase head (lst (items d a b) items) (else x (the k-syns nil))))
           (name-syn (if (null? hs) head (car hs)))
           (ps (if (null? hs) (the k-syns nil) (cdr hs)))
           (name (k-name-of name-syn "a generative type's name"))
           (saved (get k-dscope))
           (params (k-gen-params ps 0))
           (g (get k-ngens))
           (slot (k-slot))
           (gen (product (1 name) (2 (extract params 1)) (3 (extract params 2)) (4 slot))))
      (begin
        (set k-gens (cons gen (get k-gens)))
        (set k-ngens (+ g 1))
        ;; In scope in its own representation: recursion through the name.
        (k-push-desc name (ds-gen g))
        (let ((r (k-parse-type rep)))
          (begin
            (set k-dscope saved)
            (k-set-link slot r)
            (k-check-variance g rep)
            (k-push-desc name (ds-gen g))
            name))))))

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

;; A `proj` argument: which kind it is shows in its shape, or, for a bare
;; name, in how the name is bound.
;; A convention, if name `s` is one of FX-26's own; else a type.
(define k-parse-conv-or-type (subr (maxeff checks spin) (syn) k-desc)
  (lambda (s)
    (let ((n (syn-name s)))
      (if (or (string=? n "cellular") (string=? n "native") (string=? n "fx"))
          (dc (k-parse-conv s))
          (dt (k-parse-type s))))))
;; What name `s`, meaning `d` (none or one), is as a `proj` argument: by how
;; it is bound; if it is not bound as a description, a convention or a type.
(define k-parse-d-bound (subr (maxeff checks spin) (syn (listof k-ds acyclic)) k-desc)
  (lambda (s d)
    (if (null? d)
        (k-parse-conv-or-type s)
        (tagcase (car d)
          (ds-var (v k)
            (cond ((or (= k 0) (= k 3)) (dr (r-var v)))
                  ((= k 1) (de (k-one (a-var v))))
                  ((= k 5) (dz (k-size-var v)))
                  ((= k 6) (dc (cv-var v)))
                  (else (k-parse-conv-or-type s))))
          (ds-eff (e) (de e))
          (ds-size (z) (dz z))
          (ds-conv (c) (dc c))
          (else x (k-parse-conv-or-type s))))))
;; A `proj` argument that is a name.
(define k-parse-d-name (subr (maxeff checks spin) (syn) k-desc)
  (lambda (s)
    (let* ((n (syn-name s)) (sym (string->symbol n)))
      (cond ((k-at-name? n) (dr (k-region-constant sym)))
            ((string=? n "pure") (de nil))
            ((string=? n "spin") (de (k-one (a-spin))))
            ((string=? n "const") (dr (r-frozen -1 #f)))
            ((string=? n "acyclic") (dr (r-frozen -1 #t)))
            ((string=? n "finite") (dz (sz-finite)))
            ((string=? n "heap") (dr (r-heap)))
            (else (k-parse-d-bound s (k-lookup-desc sym)))))))
(define k-parse-d (subr (maxeff checks spin) (syn) k-desc)
  (lambda (s)
    (cond ((tagcase s (atom (d a b) (datum-int? d)) (else x #f))
           ;; A natural number can only be a size.
           (dz (k-parse-size s)))
          ((syn-symbol? s) (k-parse-d-name s))
          (else
           (let ((hd (k-head (k-items s "a description"))))
             (cond ((or (k-atom-head? hd) (string=? hd "maxeff")) (de (k-parse-effect s)))
                   ((or (string=? hd "+") (string=? hd "-")) (dz (k-parse-size s)))
                   (else (dt (k-parse-type s)))))))))
