;;; The checker, in FX-26: which recursive groups need not say `spin` (size-
;;; change termination).
;;; Part of the checker, `check-types.fx` first (PLAN.md §11, step 10).

;;; ------------------------------------------------- well-founded recursion
;;; Which recursive groups need not say `spin`: size-change termination
;;; (Lee, Jones and Ben-Amram, POPL 2001), as `terminate.rs` does it. Each
;;; call within the group is a graph of how the callee's arguments relate to
;;; the caller's parameters; closed under composition, every graph from a
;;; member to itself that is its own composition must have a parameter
;;; strictly smaller. The measures: parts (of sums, products, pairs at a
;;; `acyclic` region, datums), and integers counting down to a bound below or
;;; up to one above. A member named but not called escapes, and fails.

;; A recursive group: names, declared types, lambdas.
(define-type k-group (listof (productof (1 symbol) (2 int) (3 kx)) acyclic))
(define k-note-recursive (subr kstate (k-group) unit)
  (lambda (g)
    (if (null? g)
        #u
        (begin (set k-recursive (cons (cons (extract (car g) 1) (extract (car g) 2)) (get k-recursive)))
               (k-note-recursive (cdr g))))))
;; What is known of a value, relative to a parameter of the member walked:
;; the parameter, or (strictly) a part of it, of a type; or the integer
;; parameter plus an offset.
(define-datatype k-tr (tr-part int bool int) (tr-int int int))
(define-type k-trs (listof k-tr acyclic))
(define-type k-tscope (listof (pairof symbol k-trs @t) acyclic))
;; Bounds that tests have put on parameters: 0 below, 1 above.
(define-type k-guards (listof (pairof int int @t) acyclic))
;; A size-change graph: edges between slots (parameter × 3 + measure: 0
;; parts, 1 down, 2 up), strict or not, in order and each pair once.
(define-type k-edge (productof (1 int) (2 int) (3 bool)))
(define-type k-graph (listof k-edge acyclic))
(define-type k-calls (listof (productof (1 int) (2 int) (3 k-graph)) acyclic))
(define k-sc-members (ref k-names @t) (new nil))
(define k-sc-current (ref int @t) (new 0))
(define k-sc-calls (ref k-calls @t) (new nil))
;; A member named other than as a call's operator: (where . which), or none.
(define k-sc-escapes (ref (listof (pairof int int @t) acyclic) @t) (new nil))
;; For each call, as `k-sc-calls` has them: why it may shrink nothing, or "".
(define k-sc-hints (ref (listof string acyclic) @t) (new nil))
;; Whether the closure of the calls grew past `k-sc-most`.
(define k-sc-too-many (ref bool @t) (new #f))
;; For each call: caller, callee, and each argument as the caller's
;; parameter passed unchanged, or -1.
(define-type k-passed (listof (productof (1 int) (2 int) (3 k-ids)) acyclic))
(define k-sc-passed (ref k-passed @t) (new nil))
;; (member . parameter): passed unchanged by every call in the group, so the
;; same for the whole recursion, and a bound as a literal is.
(define k-sc-invariant (ref k-guards @t) (new nil))

(define k-sc-in? (subr (maxeff (read @globals) (read @t)) (k-tscope symbol) bool)
  (lambda (sc s) (and (not (null? sc)) (or (symbol=? (car (car sc)) s) (k-sc-in? (cdr sc) s)))))
(define k-sc-trs (subr (maxeff (read @globals) (read @t)) (k-tscope symbol) k-trs)
  (lambda (sc s) (cond ((null? sc) nil) ((symbol=? (car (car sc)) s) (cdr (car sc))) (else (k-sc-trs (cdr sc) s)))))
(define k-sc-index (subr (maxeff (read @globals) (read @t)) (k-names symbol int) int)
  (lambda (ns s i) (cond ((null? ns) -1) ((symbol=? (car ns) s) i) (else (k-sc-index (cdr ns) s (+ i 1))))))
;; The member `s` names, or -1 if none, or if something on the way hid it.
(define k-sc-member (subr (maxeff (read @globals) (read @t)) (k-tscope symbol) int)
  (lambda (sc s) (if (k-sc-in? sc s) -1 (k-sc-index (get k-sc-members) s 0))))
;; The standard operation `f` names, or "".
(define k-sc-op (subr (maxeff (read @globals) (read @t) (alloc @t) spin) (kx k-tscope) string)
  (lambda (f sc)
    (tagcase (k-under f)
      (x-var (s a b)
        (let ((t (k-lookup s)))
          (if (and (>= t 0) (not (k-sc-in? sc s)) (< (k-sc-index (get k-sc-members) s 0) 0) (k-named-has? (get k-std) s t))
              (symbol->string s)
              "")))
      (else y ""))))
(define k-sc-literal (subr (maxeff (read @globals) (alloc @t)) (kx) (listof int acyclic))
  (lambda (x) (tagcase x (x-const (t v a b) (if (= t k-int) (the (listof int acyclic) (cons v nil)) nil)) (else y nil))))
(define k-sc-bool? (subr (read @globals) (kx bool) bool)
  (lambda (x want) (tagcase x (x-const (t v a b) (and (= t k-bool) (= v (if want 1 0)))) (else y #f))))
(define k-sc-one? (subr (read @t) (kxs) bool)
  (lambda (xs) (and (not (null? xs)) (null? (cdr xs)))))
(define k-sc-two? (subr (maxeff (read @globals) (read @t)) (kxs) bool)
  (lambda (xs) (and (not (null? xs)) (k-sc-one? (cdr xs)))))

(define k-sc-part-ty (subr (maxeff (read @globals) (read @t)) (k-parts symbol) int)
  (lambda (ps l) (cond ((null? ps) -1) ((symbol=? (extract (car ps) 1) l) (extract (car ps) 2)) (else (k-sc-part-ty (cdr ps) l)))))
(define k-sc-nth-ty (subr (maxeff (read @globals) (read @t)) (k-parts int) int)
  (lambda (ps i) (cond ((null? ps) -1) ((= i 0) (extract (car ps) 2)) (else (k-sc-nth-ty (cdr ps) (- i 1))))))
;; Field `l` of what `ks` knows of products.
;; A part's type, where known (`t` ≥ 0); `void` where not, as past a
;; generative type's conversion.
(define k-ty-known (subr (maxeff (read @globals) (read @t) spin) (int) k-ty) (lambda (t) (if (< t 0) (ty-void) (k-get t))))
;; An `extract` proves a product, and so a part, known here or not.
(define k-sc-fields (subr (maxeff kstate spin) (k-trs symbol) k-trs)
  (lambda (ks l)
    (if (null? ks)
        nil
        (let ((rest (k-sc-fields (cdr ks) l)))
          (tagcase (car ks)
            (tr-part (p s t)
              (let ((f (tagcase (k-ty-known t) (ty-product (ps) (k-sc-part-ty ps l)) (else y -1))))
                (the k-trs (cons (tr-part p #t f) rest))))
            (else y rest))))))
;; What an arm of a `tagcase` on what `ks` knows binds: variant `tag`'s
;; value, or (`i` ≥ 0) its field `i`.
(define k-sc-variant (subr (maxeff kstate spin) (k-trs symbol int) k-trs)
  (lambda (ks tag i)
    (if (null? ks)
        nil
        (let ((rest (k-sc-variant (cdr ks) tag i)))
          (tagcase (car ks)
            ;; A `tagcase` proves a sum, and so a part, known here or not.
            (tr-part (p s t)
              (let ((f (tagcase (k-ty-known t)
                         (ty-sum (vs)
                           (let ((v (k-sc-part-ty vs tag)))
                             (cond ((< v 0) -1)
                                   ((< i 0) v)
                                   (else (tagcase (k-get v) (ty-product (ps) (k-sc-nth-ty ps i)) (else y -1))))))
                         (else y -1))))
                (the k-trs (cons (tr-part p #t f) rest))))
            (else y rest))))))
;; The `car` (`head`) or `cdr` of what `ks` knows of pairs at an `acyclic`
;; region.
(define k-sc-pair-parts (subr (maxeff kstate spin) (k-trs bool) k-trs)
  (lambda (ks head)
    (if (null? ks)
        nil
        (let ((rest (k-sc-pair-parts (cdr ks) head)))
          (tagcase (car ks)
            (tr-part (p s t)
              (tagcase (k-ty-known t)
                ;; A `nlist`'s tail is a `nlist` too: the same type serves.
                (ty-nlist (e z r) (the k-trs (cons (tr-part p #t (if head e t)) rest)))
                (ty-pair (x y r)
                  (tagcase r
                    (r-frozen (q fin) (if fin (the k-trs (cons (tr-part p #t (if head x y)) rest)) rest))
                    (else z rest)))
                (else z rest)))
            (else z rest))))))
(define k-sc-strict (subr kstate (k-trs) k-trs)
  (lambda (ks)
    (if (null? ks)
        nil
        (let ((rest (k-sc-strict (cdr ks))))
          (tagcase (car ks) (tr-part (p s t) (the k-trs (cons (tr-part p #t t) rest))) (else y rest))))))
(define k-sc-parts (subr kstate (k-trs) k-trs)
  (lambda (ks)
    (if (null? ks)
        nil
        (let ((rest (k-sc-parts (cdr ks))))
          (tagcase (car ks) (tr-part (p s t) (the k-trs (cons (car ks) rest))) (else y rest))))))
(define k-sc-shift (subr kstate (k-trs int) k-trs)
  (lambda (ks k)
    (if (null? ks)
        nil
        (let ((rest (k-sc-shift (cdr ks) k)))
          (tagcase (car ks) (tr-int (p o) (the k-trs (cons (tr-int p (+ o k)) rest))) (else y rest))))))
;; What both `ks` and `ls` say, the weaker of the two: what is known of
;; either branch's value.
(define k-sc-meet-one (subr (maxeff (read @globals) (read @t) spin) (k-tr k-trs) k-trs)
  (lambda (k ls)
    (if (null? ls)
        nil
        (let ((m (tagcase k
                   (tr-part (p s t)
                     (tagcase (car ls)
                       (tr-part (q r u)
                         (if (= p q)
                             (let ((same (and (>= t 0) (>= u 0) (= (k-resolve t) (k-resolve u)))))
                               (the k-trs (cons (tr-part p (and s r) (if same t -1)) nil)))
                             (the k-trs nil)))
                       (else y (the k-trs nil))))
                   (tr-int (p o)
                     (tagcase (car ls)
                       (tr-int (q n) (if (and (= p q) (= o n)) (the k-trs (cons k nil)) (the k-trs nil)))
                       (else y (the k-trs nil)))))))
          (if (null? m) (k-sc-meet-one k (cdr ls)) m)))))
(define k-sc-meet (subr (maxeff (read @globals) (read @t) spin) (k-trs k-trs) k-trs)
  (lambda (ks ls)
    (if (null? ks)
        nil
        (let ((m (k-sc-meet-one (car ks) ls)) (rest (k-sc-meet (cdr ks) ls)))
          (if (null? m) rest (the k-trs (cons (car m) rest)))))))
;; Whether `f` names a generative type's `up-` or `down-` conversion, the
;; identity.
(define k-sc-conversion? (subr (maxeff (read @globals) (read @t) (alloc @t) spin) (kx k-tscope) bool)
  (lambda (f sc)
    (tagcase (k-under f)
      (x-var (s a b)
        (let ((t (k-lookup s)))
          (and (>= t 0) (not (k-sc-in? sc s)) (< (k-sc-index (get k-sc-members) s 0) 0) (k-named-has? (get k-conversions) s t))))
      (else y #f))))
(define k-sc-forget-types (subr kstate (k-trs) k-trs)
  (lambda (ks)
    (if (null? ks)
        nil
        (the k-trs (cons (tagcase (car ks) (tr-part (p s t) (tr-part p s -1)) (else y (car ks))) (k-sc-forget-types (cdr ks)))))))
;; What is known of `x`'s value.
(define k-sc-tracked (subr (maxeff kstate spin) (kx k-tscope) k-trs)
  (lambda (x sc)
    (tagcase x
      (x-var (s a b) (k-sc-trs sc s))
      (x-the (t e a b) (k-sc-tracked e sc))
        (x-convention (c e a b) (k-sc-tracked e sc))
      (x-extract (e l a b) (k-sc-fields (k-sc-tracked e sc) l))
      (x-if (p c d a b) (k-sc-meet (k-sc-tracked c sc) (k-sc-tracked d sc)))
      (x-app (f args a b)
        (let ((op (k-sc-op f sc)))
          (cond ((and (k-sc-one? args) (k-sc-conversion? f sc)) (k-sc-forget-types (k-sc-tracked (car args) sc)))
                ((and (k-sc-one? args) (or (string=? op "car") (string=? op "cdr")))
                 (k-sc-pair-parts (k-sc-tracked (car args) sc) (string=? op "car")))
                ((and (k-sc-one? args) (or (string=? op "datum-car") (string=? op "datum-cdr")))
                 (k-sc-strict (k-sc-tracked (car args) sc)))
                ((and (k-sc-two? args) (or (string=? op "+") (string=? op "-")))
                 (let ((ka (k-sc-literal (car args))) (kb (k-sc-literal (car (cdr args)))))
                   (cond ((not (null? kb))
                          (k-sc-shift (k-sc-tracked (car args) sc) (if (string=? op "+") (car kb) (- 0 (car kb)))))
                         ((and (not (null? ka)) (string=? op "+")) (k-sc-shift (k-sc-tracked (car (cdr args)) sc) (car ka)))
                         (else nil))))
                (else nil))))
      (else y nil))))
(define k-sc-guarded? (subr (maxeff (read @globals) (read @t)) (k-guards int int) bool)
  (lambda (gs p b) (and (not (null? gs)) (or (and (= (car (car gs)) p) (= (cdr (car gs)) b)) (k-sc-guarded? (cdr gs) p b)))))
;; The current member's parameters that are `nat`s: bounded below by 0
;; without a test, since every argument passed for one is checked a natural.
(define k-sc-naturals (ref k-ids @t) (new nil))
;; Whether parameter `p` is bounded its way `b` (0 below, 1 above): by a
;; test, or, below, by being a `nat`.
(define k-sc-bounded? (subr (maxeff (read @globals) (read @t)) (k-guards int int) bool)
  (lambda (gs p b) (or (k-sc-guarded? gs p b) (and (= b 0) (k-has-id? (get k-sc-naturals) p)))))
;; Whether `ks` knows a value as a parameter, of the member walked, passed on
;; unchanged by every call.
(define k-sc-invariant-in? (subr (maxeff (read @globals) (read @t)) (k-trs) bool)
  (lambda (ks)
    (and (not (null? ks))
         (or (tagcase (car ks)
               (tr-part (p s t) (and (not s) (k-sc-guarded? (get k-sc-invariant) (get k-sc-current) p)))
               (else y #f))
             (k-sc-invariant-in? (cdr ks))))))
;; Whether `x` is the same at every call of the group: a literal, a
;; variable bound outside it, a parameter passed on unchanged, or the length
;; of a string or the sum or difference of such.
(define-rec
  (k-sc-fixed? (subr (maxeff kstate spin) (kx k-tscope) bool)
    (lambda (x sc)
      (tagcase x
        (x-const (t v a b) (= t k-int))
        (x-var (s a b)
          (if (k-sc-in? sc s) (k-sc-invariant-in? (k-sc-trs sc s)) (< (k-sc-index (get k-sc-members) s 0) 0)))
        (x-the (t e a b) (k-sc-fixed? e sc))
        (x-convention (c e a b) (k-sc-fixed? e sc))
        (x-app (f args a b)
          (let ((op (k-sc-op f sc)))
            ;; An array's length never changes, as a string's does not.
            (and (or (and (or (string=? op "string-length") (string=? op "array-length")) (k-sc-one? args))
                     (and (or (string=? op "+") (string=? op "-")) (k-sc-two? args)))
                 (k-sc-all-fixed? args sc))))
        (else y #f))))
  (k-sc-all-fixed? (subr (maxeff kstate spin) (kxs k-tscope) bool)
    (lambda (xs sc) (or (null? xs) (and (k-sc-fixed? (car xs) sc) (k-sc-all-fixed? (cdr xs) sc))))))
(define k-sc-append (subr kstate (k-guards k-guards) k-guards)
  (lambda (xs ys) (if (null? xs) ys (the k-guards (cons (car xs) (k-sc-append (cdr xs) ys))))))
(define k-sc-with (subr kstate (int k-ids k-guards) k-guards)
  (lambda (p bs rest) (if (null? bs) rest (the k-guards (cons (cons p (car bs)) (k-sc-with p (cdr bs) rest))))))
;; Bounds `bs` on each integer parameter `ks` knows of.
(define k-sc-bounds-on (subr kstate (k-trs k-ids) k-guards)
  (lambda (ks bs)
    (if (null? ks)
        nil
        (let ((rest (k-sc-bounds-on (cdr ks) bs)))
          (tagcase (car ks) (tr-int (p o) (k-sc-with p bs rest)) (else y rest))))))
(define k-sc-flip (subr kstate (k-ids) k-ids)
  (lambda (bs) (if (null? bs) nil (the k-ids (cons (- 1 (car bs)) (k-sc-flip (cdr bs)))))))
;; The bounds on parameters that `x` having the value `holds` shows.
(define k-sc-facts (subr (maxeff kstate spin) (kx k-tscope bool) k-guards)
  (lambda (x sc holds)
    (tagcase x
      (x-app (f args a b)
        (let ((op (k-sc-op f sc)))
          (cond ((and (k-sc-one? args) (string=? op "not")) (k-sc-facts (car args) sc (not holds)))
                ((k-sc-two? args)
                 (let* ((lt (or (string=? op "<") (string=? op "<=")))
                        (gt (or (string=? op ">") (string=? op ">=")))
                        ;; The bounds on the left operand.
                        (left (the k-ids (cond ((or (and lt holds) (and gt (not holds))) (cons 1 nil))
                                               ((or (and lt (not holds)) (and gt holds)) (cons 0 nil))
                                               ((and (string=? op "=") holds) (cons 0 (cons 1 nil)))
                                               (else nil))))
                        (x1 (car args))
                        (x2 (car (cdr args))))
                   (k-sc-append (if (k-sc-fixed? x2 sc) (k-sc-bounds-on (k-sc-tracked x1 sc) left) nil)
                                (if (k-sc-fixed? x1 sc) (k-sc-bounds-on (k-sc-tracked x2 sc) (k-sc-flip left)) nil))))
                (else nil))))
      ;; `(and p c)` and `(or p d)`, as they are parsed.
      (x-if (p c d a b)
        (cond ((and holds (k-sc-bool? d #f)) (k-sc-append (k-sc-facts p sc #t) (k-sc-facts c sc #t)))
              ((and (not holds) (k-sc-bool? c #t)) (k-sc-append (k-sc-facts p sc #f) (k-sc-facts d sc #f)))
              (else nil)))
      (else y nil))))

;; `g` with the edge from slot `f` to slot `t`, strict if `s`.
(define k-sc-add (subr kstate (k-graph int int bool) k-graph)
  (lambda (g f t s)
    (if (null? g)
        (the k-graph (cons (product (1 f) (2 t) (3 s)) nil))
        (let* ((e (car g)) (ef (extract e 1)) (et (extract e 2)))
          (cond ((and (= ef f) (= et t)) (the k-graph (cons (product (1 f) (2 t) (3 (or s (extract e 3)))) (cdr g))))
                ((or (< f ef) (and (= f ef) (< t et))) (the k-graph (cons (product (1 f) (2 t) (3 s)) g)))
                (else (the k-graph (cons e (k-sc-add (cdr g) f t s)))))))))
;; The edges to argument `q` from what `ks` knows of it.
(define k-sc-tr-edges (subr kstate (k-trs int k-guards k-graph) k-graph)
  (lambda (ks q gs g)
    (if (null? ks)
        g
        (k-sc-tr-edges (cdr ks) q gs
          (tagcase (car ks)
            (tr-part (p s t) (k-sc-add g (* 3 p) (* 3 q) s))
            (tr-int (p o)
              (let ((g1 (cond ((and (< o 0) (k-sc-bounded? gs p 0)) (k-sc-add g (+ (* 3 p) 1) (+ (* 3 q) 1) #t))
                              ((<= o 0) (k-sc-add g (+ (* 3 p) 1) (+ (* 3 q) 1) #f))
                              (else g))))
                (cond ((and (> o 0) (k-sc-bounded? gs p 1)) (k-sc-add g1 (+ (* 3 p) 2) (+ (* 3 q) 2) #t))
                      ((>= o 0) (k-sc-add g1 (+ (* 3 p) 2) (+ (* 3 q) 2) #f))
                      (else g1)))))))))
(define k-sc-arg-edges (subr (maxeff kstate spin) (kxs int k-tscope k-guards k-graph) k-graph)
  (lambda (args q sc gs g)
    (if (null? args) g (k-sc-arg-edges (cdr args) (+ q 1) sc gs (k-sc-tr-edges (k-sc-tracked (car args) sc) q gs g)))))
;; A call of member `to` with `args`, from the member walked.
(define k-sc-unchanged (subr kstate (k-trs) int)
  (lambda (ks)
    (cond ((null? ks) -1)
          ((tagcase (car ks) (tr-part (p s t) (not s)) (else y #f)) (tagcase (car ks) (tr-part (p s t) p) (else y -1)))
          (else (k-sc-unchanged (cdr ks))))))
(define k-sc-passing (subr (maxeff kstate spin) (kxs k-tscope) k-ids)
  (lambda (args sc) (if (null? args) nil (the k-ids (cons (k-sc-unchanged (k-sc-tracked (car args) sc)) (k-sc-passing (cdr args) sc))))))
;; Whether `ks` knows of a pair at a region that is not `acyclic`.
(define k-sc-any-written? (subr (maxeff (read @globals) (read @t) spin) (k-trs) bool)
  (lambda (ks)
    (and (not (null? ks))
         (or (tagcase (car ks)
               (tr-part (p s t)
                 (tagcase (k-ty-known t) (ty-pair (x y r) (tagcase r (r-frozen (q fin) (not fin)) (else z #t))) (else z #f)))
               (else z #f))
             (k-sc-any-written? (cdr ks))))))
;; Whether some argument is the `car` or `cdr` of a parameter's part at a
;; region that is not `acyclic`.
(define k-sc-written-arg? (subr (maxeff kstate spin) (kxs k-tscope) bool)
  (lambda (args sc)
    (and (not (null? args))
         (or (tagcase (car args)
               (x-app (f xs a b)
                 (let ((op (k-sc-op f sc)))
                   (and (or (string=? op "car") (string=? op "cdr")) (k-sc-one? xs) (k-sc-any-written? (k-sc-tracked (car xs) sc)))))
               (else y #f))
             (k-sc-written-arg? (cdr args) sc)))))
;; The first count in `ks` with no fixed bound its way, in words, or "".
(define k-sc-count-hint (subr (maxeff (read @globals) (read @t)) (k-trs k-guards) string)
  (lambda (ks gs)
    (if (null? ks)
        ""
        (let ((h (tagcase (car ks)
                   (tr-int (p o)
                     (cond ((and (< o 0) (not (k-sc-bounded? gs p 0))) "it counts down, but nothing fixed bounds the count below")
                           ((and (> o 0) (not (k-sc-bounded? gs p 1))) "it counts up, but nothing fixed bounds the count above")
                           (else "")))
                   (else y ""))))
          (if (string=? h "") (k-sc-count-hint (cdr ks) gs) h)))))
(define k-sc-count-hints (subr (maxeff kstate spin) (kxs k-tscope k-guards) string)
  (lambda (args sc gs)
    (if (null? args)
        ""
        (let ((h (k-sc-count-hint (k-sc-tracked (car args) sc) gs)))
          (if (string=? h "") (k-sc-count-hints (cdr args) sc gs) h)))))
;; Why a call with `args` may shrink nothing, or "".
(define k-sc-hint (subr (maxeff kstate spin) (kxs k-tscope k-guards) string)
  (lambda (args sc gs)
    (if (k-sc-written-arg? args sc)
        "a part of a list that may be written is no smaller: it may be cyclic"
        (k-sc-count-hints args sc gs))))
(define k-sc-call (subr (maxeff kstate spin) (int kxs k-tscope k-guards) unit)
  (lambda (to args sc gs)
    (begin
     (set k-sc-hints (cons (k-sc-hint args sc gs) (get k-sc-hints)))
     (set k-sc-passed (cons (product (1 (get k-sc-current)) (2 to) (3 (k-sc-passing args sc))) (get k-sc-passed)))
     (set k-sc-calls (cons (product (1 (get k-sc-current)) (2 to) (3 (k-sc-arg-edges args 0 sc gs nil))) (get k-sc-calls))))))

(define k-sc-hide-params (subr kstate ((listof (productof (1 symbol) (2 k-ids)) acyclic) k-tscope) k-tscope)
  (lambda (ps sc) (if (null? ps) sc (k-sc-hide-params (cdr ps) (cons (cons (extract (car ps) 1) (the k-trs nil)) sc)))))
(define k-sc-hide-group (subr kstate (k-group k-tscope) k-tscope)
  (lambda (bs sc) (if (null? bs) sc (k-sc-hide-group (cdr bs) (cons (cons (extract (car bs) 1) (the k-trs nil)) sc)))))
(define k-sc-let-scope (subr (maxeff kstate spin) ((listof (productof (1 symbol) (2 kx)) acyclic) k-tscope k-tscope) k-tscope)
  (lambda (bs outer sc)
    (if (null? bs) sc (k-sc-let-scope (cdr bs) outer (cons (cons (extract (car bs) 1) (k-sc-tracked (extract (car bs) 2) outer)) sc)))))
(define k-sc-arm-scope (subr (maxeff kstate spin) (k-names k-trs symbol int k-tscope) k-tscope)
  (lambda (ns whole tag i sc)
    (if (null? ns) sc (k-sc-arm-scope (cdr ns) whole tag (+ i 1) (cons (cons (car ns) (k-sc-variant whole tag i)) sc)))))
(define-rec
  (k-sc-walk-list (subr (maxeff kstate spin) (kxs k-tscope k-guards) unit)
    (lambda (xs sc gs) (if (null? xs) #u (begin (k-sc-walk (car xs) sc gs) (k-sc-walk-list (cdr xs) sc gs)))))
  (k-sc-walk-group (subr (maxeff kstate spin) (k-group k-tscope k-guards) unit)
    (lambda (bs sc gs) (if (null? bs) #u (begin (k-sc-walk (extract (car bs) 3) sc gs) (k-sc-walk-group (cdr bs) sc gs)))))
  (k-sc-walk-lets (subr (maxeff kstate spin) ((listof (productof (1 symbol) (2 kx)) acyclic) k-tscope k-guards) unit)
    (lambda (bs sc gs) (if (null? bs) #u (begin (k-sc-walk (extract (car bs) 2) sc gs) (k-sc-walk-lets (cdr bs) sc gs)))))
  (k-sc-walk-fields (subr (maxeff kstate spin) ((listof (productof (1 symbol) (2 kx)) acyclic) k-tscope k-guards) unit)
    (lambda (fs sc gs) (if (null? fs) #u (begin (k-sc-walk (extract (car fs) 2) sc gs) (k-sc-walk-fields (cdr fs) sc gs)))))
  (k-sc-walk-arms (subr (maxeff kstate spin) (k-arms k-trs k-tscope k-guards) unit)
    (lambda (arms whole sc gs)
      (if (null? arms)
          #u
          (let* ((arm (car arms))
                 (tag (extract arm 1))
                 (inner (if (extract arm 2)
                            (k-sc-arm-scope (extract arm 3) whole tag 0 sc)
                            (the k-tscope (cons (cons (car (extract arm 3)) (k-sc-variant whole tag -1)) sc)))))
            (begin (k-sc-walk (extract arm 4) inner gs) (k-sc-walk-arms (cdr arms) whole sc gs))))))
  (k-sc-walk (subr (maxeff kstate spin) (kx k-tscope k-guards) unit)
    (lambda (x sc gs)
      (tagcase x
        (x-var (s a b)
          (let ((m (k-sc-member sc s)))
            (if (and (>= m 0) (null? (get k-sc-escapes))) (set k-sc-escapes (cons (cons (get k-sc-current) m) nil)) #u)))
        (x-const (t v a b) #u)
        (x-app (f args a b)
          (let ((to (tagcase (k-under f) (x-var (s fa fb) (k-sc-member sc s)) (else y -1))))
            (begin (if (>= to 0) (k-sc-call to args sc gs) (k-sc-walk f sc gs))
                   (k-sc-walk-list args sc gs))))
        (x-lambda (ps body a b) (k-sc-walk body (k-sc-hide-params ps sc) gs))
        (x-plambda (bs body a b) (k-sc-walk body sc gs))
        (x-proj (body ds a b) (k-sc-walk body sc gs))
        (x-the (t body a b) (k-sc-walk body sc gs))
        (x-convention (c body a b) (k-sc-walk body sc gs))
        (x-letregion (k r i body a b) (k-sc-walk body sc gs))
        (x-rlambda (r l a b) (begin (k-sc-walk r sc gs) (k-sc-walk l sc gs)))
        (x-if (p c d a b)
          (begin (k-sc-walk p sc gs)
                 (k-sc-walk c sc (k-sc-append (k-sc-facts p sc #t) gs))
                 (k-sc-walk d sc (k-sc-append (k-sc-facts p sc #f) gs))))
        (x-letrec (bs body a b)
          (let ((inner (k-sc-hide-group bs sc)))
            (begin (k-sc-walk-group bs inner gs) (k-sc-walk body inner gs))))
        (x-let (bs body a b) (begin (k-sc-walk-lets bs sc gs) (k-sc-walk body (k-sc-let-scope bs sc sc) gs)))
        (x-begin (xs a b) (k-sc-walk-list xs sc gs))
        (x-bloblet (n i xs a b) (k-sc-walk-list xs sc gs))
        (x-prompt (t body h a b) (begin (k-sc-walk t sc gs) (k-sc-walk body sc gs) (k-sc-walk h sc gs)))
        (x-product (fs a b) (k-sc-walk-fields fs sc gs))
        (x-extract (e l a b) (k-sc-walk e sc gs))
        (x-sum (tag e a b) (k-sc-walk e sc gs))
        (x-tagcase (e arms els a b)
          (let ((whole (k-sc-tracked e sc)))
            (begin (k-sc-walk e sc gs)
                   (k-sc-walk-arms arms whole sc gs)
                   ;; `else` sees the same value, its type narrowed.
                   (if (null? els)
                       #u
                       (k-sc-walk (extract (car els) 2) (cons (cons (extract (car els) 1) (k-sc-parts whole)) sc) gs)))))))))

(define k-sc-compose-one (subr kstate (k-edge k-graph k-graph) k-graph)
  (lambda (e b out)
    (cond ((null? b) out)
          ((= (extract e 2) (extract (car b) 1))
           (k-sc-compose-one e (cdr b) (k-sc-add out (extract e 1) (extract (car b) 2) (or (extract e 3) (extract (car b) 3)))))
          (else (k-sc-compose-one e (cdr b) out)))))
(define k-sc-compose (subr kstate (k-graph k-graph k-graph) k-graph)
  (lambda (a b out) (if (null? a) out (k-sc-compose (cdr a) b (k-sc-compose-one (car a) b out)))))
(define k-sc-same? (subr (maxeff (read @globals) (read @t)) (k-graph k-graph) bool)
  (lambda (a b)
    (if (null? a)
        (null? b)
        (and (not (null? b))
             (= (extract (car a) 1) (extract (car b) 1))
             (= (extract (car a) 2) (extract (car b) 2))
             (if (extract (car a) 3) (extract (car b) 3) (not (extract (car b) 3)))
             (k-sc-same? (cdr a) (cdr b))))))
(define k-sc-has? (subr (maxeff (read @globals) (read @t)) (k-calls int int k-graph) bool)
  (lambda (cs f h g)
    (and (not (null? cs))
         (or (and (= (extract (car cs) 1) f) (= (extract (car cs) 2) h) (k-sc-same? (extract (car cs) 3) g))
             (k-sc-has? (cdr cs) f h g)))))
(define k-sc-dedup (subr kstate (k-calls k-calls) k-calls)
  (lambda (cs out)
    (cond ((null? cs) out)
          ((k-sc-has? out (extract (car cs) 1) (extract (car cs) 2) (extract (car cs) 3)) (k-sc-dedup (cdr cs) out))
          (else (k-sc-dedup (cdr cs) (cons (car cs) out))))))
(define k-sc-strict-loop? (subr (maxeff (read @globals) (read @t)) (k-graph) bool)
  (lambda (g) (and (not (null? g)) (or (and (= (extract (car g) 1) (extract (car g) 2)) (extract (car g) 3)) (k-sc-strict-loop? (cdr g))))))
;; Whether every graph from a member to itself that is its own composition
;; has a strict loop.
(define k-sc-ok? (subr kstate (k-calls) bool)
  (lambda (cs)
    (or (null? cs)
        (let ((c (car cs)))
          (and (or (not (= (extract c 1) (extract c 2)))
                   (not (k-sc-same? (k-sc-compose (extract c 3) (extract c 3) nil) (extract c 3)))
                   (k-sc-strict-loop? (extract c 3)))
               (k-sc-ok? (cdr cs)))))))
;; A graph's closure may grow; beyond this many, the group does not pass.
(define k-sc-most int 4000)
(define-rec
  (k-sc-close (subr kstate (k-calls k-calls int) bool)
    (lambda (todo all n)
      (if (null? todo)
          (k-sc-ok? all)
          (let ((c (car todo))) (k-sc-extend (extract c 1) (extract c 2) (extract c 3) (get k-sc-calls) (cdr todo) all n)))))
  (k-sc-extend (subr kstate (int int k-graph k-calls k-calls k-calls int) bool)
    (lambda (f g a calls todo all n)
      (cond ((null? calls) (k-sc-close todo all n))
            ((not (= (extract (car calls) 1) g)) (k-sc-extend f g a (cdr calls) todo all n))
            (else
             (let ((cg (k-sc-compose a (extract (car calls) 3) nil)) (h (extract (car calls) 2)))
               (cond ((k-sc-has? all f h cg) (k-sc-extend f g a (cdr calls) todo all n))
                     ((>= n k-sc-most) (begin (set k-sc-too-many #t) #f))
                     (else (let ((new (product (1 f) (2 h) (3 cg))))
                             (k-sc-extend f g a (cdr calls) (cons new todo) (cons new all) (+ n 1)))))))))))

;; A binding's lambda, under `plambda`, `the` and `rlambda`.
(define k-sc-lambda-of (subr (read @globals) (kx) kx)
  (lambda (x)
    (tagcase x
      (x-plambda (bs body a b) (k-sc-lambda-of body))
      (x-the (t body a b) (k-sc-lambda-of body))
      (x-rlambda (r l a b) (k-sc-lambda-of l))
      (else y y))))
;; The parameter types of a declared type, under its binders.
(define k-sc-param-types (subr (maxeff (read @globals) (read @t) spin) (int) k-ids)
  (lambda (t) (tagcase (k-get t) (ty-poly (bs body) (k-sc-param-types body)) (ty-subr (e ps r cv) ps) (else y nil))))
;; The parameters `ps`, the `j`th on, each known as itself.
(define k-sc-param-scope (subr (maxeff kstate spin) ((listof (productof (1 symbol) (2 k-ids)) acyclic) k-ids int k-tscope) k-tscope)
  (lambda (ps ts j sc)
    (if (null? ps)
        sc
        (let* ((t (car ts))
               (natural (tagcase (k-get (k-resolve t)) (ty-nat (z) #t) (else y #f)))
               (noted (if natural (set k-sc-naturals (cons j (get k-sc-naturals))) #u))
               (ks (the k-trs (cons (tr-part j #f t) (if (or natural (= (k-resolve t) (k-resolve k-int))) (the k-trs (cons (tr-int j 0) nil)) nil)))))
          (k-sc-param-scope (cdr ps) (cdr ts) (+ j 1) (cons (cons (extract (car ps) 1) ks) sc))))))
(define k-sc-walk-members (subr (maxeff kstate spin) (k-group int) bool)
  (lambda (bs i)
    (or (null? bs)
        (tagcase (k-sc-lambda-of (extract (car bs) 3))
          (x-lambda (ps body a b)
            (let ((ts (k-sc-param-types (extract (car bs) 2))))
              (and (<= (k-length ps) (k-length ts))
                   (begin (set k-sc-current i)
                          (set k-sc-naturals nil)
                          (k-sc-walk body (k-sc-param-scope ps ts 0 nil) nil)
                          (and (null? (get k-sc-escapes)) (k-sc-walk-members (cdr bs) (+ i 1)))))))
          (else y #f)))))
(define k-sc-names (subr kstate (k-group) k-names)
  (lambda (bs) (if (null? bs) nil (the k-names (cons (extract (car bs) 1) (k-sc-names (cdr bs)))))))
(define k-sc-upto (subr kstate (int int) k-ids)
  (lambda (j n)
    (letrec ((down (subr kstate (int k-ids) k-ids) (lambda (i acc) (if (< i j) acc (down (- i 1) (the k-ids (cons i acc)))))))
      (down (- n 1) nil))))
;; Every (member . parameter) of the group, the `i`th member on.
(define k-sc-all-params (subr kstate (k-group int k-guards) k-guards)
  (lambda (bs i out)
    (if (null? bs)
        out
        (k-sc-all-params (cdr bs) (+ i 1)
          (tagcase (k-sc-lambda-of (extract (car bs) 3))
            (x-lambda (ps body a b) (k-sc-with i (k-sc-upto 0 (k-length ps)) out))
            (else y out))))))
(define k-sc-drop (subr kstate (k-guards int int) k-guards)
  (lambda (gs i j)
    (cond ((null? gs) gs)
          ((and (= (car (car gs)) i) (= (cdr (car gs)) j)) (k-sc-drop (cdr gs) i j))
          (else (the k-guards (cons (car gs) (k-sc-drop (cdr gs) i j)))))))
;; `inv` less what the call from `from` to `to` passing `args` changes.
(define k-sc-keep-args (subr kstate (k-guards int int k-ids int) k-guards)
  (lambda (inv from to args j)
    (if (null? args)
        inv
        (let ((p (car args)))
          (k-sc-keep-args (if (and (>= p 0) (k-sc-guarded? inv from p)) inv (k-sc-drop inv to j)) from to (cdr args) (+ j 1))))))
(define k-sc-keep-all (subr kstate (k-guards k-passed) k-guards)
  (lambda (inv ps)
    (if (null? ps)
        inv
        (let ((c (car ps))) (k-sc-keep-all (k-sc-keep-args inv (extract c 1) (extract c 2) (extract c 3) 0) (cdr ps))))))
;; The invariant parameters: the greatest set every call keeps.
(define k-sc-invariants (subr (maxeff kstate spin) (k-guards) k-guards)
  (lambda (inv)
    (let ((next (k-sc-keep-all inv (get k-sc-passed))))
      (if (= (k-length next) (k-length inv)) inv (k-sc-invariants next)))))
(define k-sc-member-name (subr (maxeff (read @globals) (read @t)) (int) string)
  (lambda (i) (symbol->string (k-nth (get k-sc-members) i))))
(define k-sc-strict-any? (subr (read @globals) (k-graph) bool)
  (lambda (g) (and (not (null? g)) (or (extract (car g) 3) (k-sc-strict-any? (cdr g))))))
(define k-sc-has-string? (subr (read @globals) ((listof string acyclic) string) bool)
  (lambda (xs s) (and (not (null? xs)) (or (string=? (car xs) s) (k-sc-has-string? (cdr xs) s)))))
;; The calls, in the order met, that pass nothing strictly smaller, and
;; either nothing related to the caller's parameters or with a hint why;
;; each once, in words (newest first). One passing its caller's parameters
;; on unchanged is harmless.
(define k-sc-flat (subr kstate (k-calls (listof string acyclic) (listof string acyclic)) (listof string acyclic))
  (lambda (cs hs out)
    (if (null? cs)
        out
        (let* ((c (car cs))
               (s1 (k-cat5 "the call of `" (k-sc-member-name (extract c 2)) "` in `" (k-sc-member-name (extract c 1)) "`"))
               (s (if (string=? (car hs) "") s1 (k-cat4 s1 " (" (car hs) ")"))))
          (k-sc-flat (cdr cs) (cdr hs)
                     (if (or (k-sc-strict-any? (extract c 3))
                             (and (not (null? (extract c 3))) (string=? (car hs) ""))
                             (k-sc-has-string? out s))
                         out
                         (the (listof string acyclic) (cons s out))))))))
(define k-sc-escape-why (subr (maxeff (read @globals) (read @t)) () string)
  (lambda ()
    (let ((e (car (get k-sc-escapes))))
      (k-cat5 "`" (k-sc-member-name (cdr e)) "` is named in `" (k-sc-member-name (car e))
              "` other than as a call's operator: whoever is given it may call it again, with anything"))))
;; Why the walked calls may not end.
(define k-sc-calls-why (subr kstate () string)
  (lambda ()
    (let ((all (k-sc-dedup (get k-sc-calls) nil)))
      (cond ((k-sc-close all all (k-length all)) "")
            ((get k-sc-too-many) "the calls combine in too many ways to follow")
            (else
             (let ((flat (the (listof string acyclic)
                              (reverse (k-sc-flat (the k-calls (reverse (get k-sc-calls)))
                                                  (the (listof string acyclic) (reverse (get k-sc-hints))) nil)))))
               (if (null? flat)
                   "no argument keeps shrinking around every loop of calls"
                   (string-append "nothing smaller, or related, is passed by " (k-join flat ", ")))))))))
;; Whether every run of the group `bs` ends, so that calls within it need
;; not say `spin`: "" if so, and otherwise why not, in words for an error.
;; Walked twice: first to learn which parameters every call passes on
;; unchanged, then with them as bounds.
(define k-termination (subr (maxeff kstate spin) (k-group) string)
  (lambda (bs)
    (begin
      (set k-sc-members (k-sc-names bs))
      (set k-sc-calls nil)
      (set k-sc-hints nil)
      (set k-sc-passed nil)
      (set k-sc-invariant nil)
      (set k-sc-escapes nil)
      (set k-sc-too-many #f)
      (let ((walked (k-sc-walk-members bs 0)))
        (cond ((not (null? (get k-sc-escapes))) (k-sc-escape-why))
              ((not walked) "it is not a lambda")
              (else
               (let ((inv (k-sc-invariants (k-sc-all-params bs 0 nil))))
                 (if (null? inv)
                     (k-sc-calls-why)
                     (begin
                       (set k-sc-invariant inv)
                       (set k-sc-calls nil)
                       (set k-sc-hints nil)
                       (set k-sc-passed nil)
                       (let ((again (k-sc-walk-members bs 0)))
                         (cond ((not (null? (get k-sc-escapes))) (k-sc-escape-why))
                               ((not again) "it is not a lambda")
                               (else (k-sc-calls-why)))))))))))))
;; Note why each of `g` may not end.
(define k-note-why (subr kstate (k-group string) unit)
  (lambda (g why)
    (if (null? g)
        #u
        (begin (set k-spin-why (cons (product (1 (extract (car g) 1)) (2 (extract (car g) 2)) (3 why)) (get k-spin-why)))
               (k-note-why (cdr g) why)))))
(define k-why-of (subr (maxeff (read @globals) (read @t)) ((listof (productof (1 symbol) (2 int) (3 string)) acyclic) symbol int) string)
  (lambda (ws n t)
    (cond ((null? ws) "")
          ((and (symbol=? (extract (car ws) 1) n) (= (extract (car ws) 2) t)) (extract (car ws) 3))
          (else (k-why-of (cdr ws) n t)))))
(define k-text-has? (subr (maxeff (read @globals) spin) (string string int) bool)
  (lambda (hay needle i)
    (and (<= (+ i (string-length needle)) (string-length hay))
         (or (string=? (substring hay i (+ i (string-length needle))) needle) (k-text-has? hay needle (+ i 1))))))
;; `f`, checking what `n` is declared `t`; an error at `a`..`b` itself says
;; so, and, if it is about `spin` and `n`'s group may not end, why not.
(define k-declaring (subr (maxeff (read @globals) checks spin) ((subr (maxeff checks spin) () k-te) int int symbol int) k-te)
  (lambda (f a b n t)
    (let ((r (prompt k-tag (k-done (f)) (lambda (r) r))))
      (tagcase r
        (k-done (te) te)
        (k-err (m ea eb)
          (if (and (= ea a) (= eb b))
              (let* ((why (k-why-of (get k-spin-why) n t))
                     (tail (if (and (not (string=? why "")) (k-text-has? m "spin" 0)) (string-append "; it may not end: " why) "")))
                (k-fail (k-cat4 (k-cat4 (k-quote (symbol->string n)) " is declared a " (k-show-ty t) ": ") m tail "") ea eb))
              (k-fail m ea eb)))
        (k-ok (xs) (k-fail "k-ok inside" a b))))))

;; Every binding of a `letrec` a lambda, or an error at the first that is not.
(define k-letrec-lambdas (subr checks (k-group) unit)
  (lambda (bs)
    (cond ((null? bs) #u)
          ((k-lambda? (extract (car bs) 3)) (k-letrec-lambdas (cdr bs)))
          (else (let ((x (extract (car bs) 3))) (k-fail (k-letrec-not-lambda (extract (car bs) 1)) (k-start x) (k-end x)))))))

;; What a test shows when it holds, and when not.
(define-type k-branch-facts (pairof (listof k-size-fact acyclic) (listof k-size-fact acyclic) acyclic))
(define k-branch-facts-of (subr pure ((listof k-size-fact acyclic) (listof k-size-fact acyclic)) k-branch-facts)
  (lambda (yes no) (the k-branch-facts (cons yes no))))
;; The fact `lin ≥ 0`, alone.
(define k-ge-fact (subr pure (k-size) (listof k-size-fact acyclic))
  (lambda (lin) (the (listof k-size-fact acyclic) (cons (product (1 lin) (2 #f)) nil))))
;; `x < y`, as `y - x - 1 ≥ 0`; `x ≤ y`, as `y - x ≥ 0`.
(define k-lt-fact (subr (read @globals) (k-size k-size) (listof k-size-fact acyclic))
  (lambda (x y) (k-ge-fact (k-size-plus (k-size-add-scaled y x -1) -1))))
(define k-le-fact (subr (read @globals) (k-size k-size) (listof k-size-fact acyclic))
  (lambda (x y) (k-ge-fact (k-size-add-scaled y x -1))))
;; The size an argument is, when a natural literal or a variable of type
;; `(nat s)` (none or one).
(define k-nat-size (subr (maxeff (read @globals) (read @t) spin) (kx) (listof k-size acyclic))
  (lambda (x)
    (tagcase x
      (x-const (ty k a b) (if (and (= ty k-int) (>= k 0)) (the (listof k-size acyclic) (cons (k-size-lit k) nil)) nil))
      (x-var (v a b)
        (let ((t (k-lookup v)))
          (if (< t 0)
              nil
              (tagcase (k-get (k-resolve t)) (ty-nat (z) (the (listof k-size acyclic) (cons z nil))) (else y nil)))))
      (else y nil))))
;; `xs : (nlist T n)` shows `n = 0` when null, and `n - 1 ≥ 0` when not.
(define k-null-facts (subr (maxeff (read @globals) (read @t) (alloc @t) spin) (kx) k-branch-facts)
  (lambda (x)
    (let ((none (k-branch-facts-of nil nil)))
      (tagcase x
        (x-var (v va vb)
          (let ((vt (k-lookup v)))
            (if (< vt 0)
                none
                (tagcase (k-get vt)
                  (ty-nlist (e z r)
                    (tagcase z
                      (sz-lin (k ts)
                        (k-branch-facts-of (the (listof k-size-fact acyclic) (cons (product (1 z) (2 #t)) nil)) (k-ge-fact (k-size-plus z -1))))
                      (else w none)))
                  (else w none)))))
        (else y none)))))
;; What a comparison `(op a b)` of naturals shows, when both have sizes.
(define k-compare-facts (subr (maxeff (read @globals) (read @t) (alloc @t) spin) (string kx kx) k-branch-facts)
  (lambda (op a b)
    (let ((xs (k-nat-size a)) (ys (k-nat-size b)) (none (k-branch-facts-of nil nil)))
      (if (or (null? xs) (null? ys) (tagcase (car xs) (sz-finite () #t) (else w #f)) (tagcase (car ys) (sz-finite () #t) (else w #f)))
          none
          (let ((x (car xs)) (y (car ys)))
            (cond ((string=? op "<") (k-branch-facts-of (k-lt-fact x y) (k-le-fact y x)))
                  ((string=? op "<=") (k-branch-facts-of (k-le-fact x y) (k-lt-fact y x)))
                  ((string=? op ">") (k-branch-facts-of (k-lt-fact y x) (k-le-fact x y)))
                  ((string=? op ">=") (k-branch-facts-of (k-le-fact y x) (k-lt-fact x y)))
                  (else
                   (let ((no (cond ((= (k-size-as-lit y) 0) (k-ge-fact (k-size-plus x -1)))
                                   ((= (k-size-as-lit x) 0) (k-ge-fact (k-size-plus y -1)))
                                   (else (the (listof k-size-fact acyclic) nil)))))
                     (k-branch-facts-of (the (listof k-size-fact acyclic) (cons (product (1 (k-size-add-scaled x y -1)) (2 #t)) nil)) no)))))))))
;; `v` and `k` of `(length-is? v k)` or `(certify-length v k)`: the
;; variable, its binding, and the length, a natural literal or a variable
;; of type `(nat s)` (none or one).
(define k-length-arg (subr (maxeff (read @globals) (read @t) (alloc @t) spin) (kx kx) (listof k-cert-len acyclic))
  (lambda (a n)
    (tagcase a
      (x-var (v va vb)
        (if (tagcase n (x-const (ty k ka kb) #t) (x-var (w wa wb) #t) (else y #f))
            (let ((z (k-nat-size n)))
              (if (null? z) nil (the (listof k-cert-len acyclic) (cons (product (1 v) (2 (k-binding-depth v)) (3 (car z))) nil))))
            nil))
      (else y nil))))
;; What `length-is?` has just confirmed: a variable, its binding, the length.
(define-type k-cert-len (productof (1 symbol) (2 int) (3 k-size)))
(define k-cert-len-has? (subr (maxeff (read @globals) (read @t)) ((listof k-cert-len acyclic) k-cert-len) bool)
  (lambda (cs c)
    (and (not (null? cs))
         (or (and (symbol=? (extract (car cs) 1) (extract c 1)) (= (extract (car cs) 2) (extract c 2)) (k-size=? (extract (car cs) 3) (extract c 3)))
             (k-cert-len-has? (cdr cs) c)))))
;; If `p` is `(length-is? v k)`, the variable, its binding, and the length.
(define k-length-test (subr (maxeff (read @globals) (read @t) (alloc @t) spin) (kx) (listof k-cert-len acyclic))
  (lambda (p)
    (tagcase p
      (x-app (f args a b)
        (tagcase f
          (x-var (op fa fb)
            (let ((t (k-lookup op)))
              (if (and (string=? (symbol->string op) "length-is?") (>= t 0) (k-named-has? (get k-std) op t)
                       (not (null? args)) (not (null? (cdr args))) (null? (cdr (cdr args))))
                  (k-length-arg (car args) (car (cdr args)))
                  nil)))
          (else y nil)))
      (else y nil))))
;; Whether `x` may be a natural of a size without being told what it is: an
;; integer literal, a variable, or a `+`, `-` or `length`.
(define k-natural-by-itself? (subr (maxeff (read @globals) (read @t) spin) (kx) bool)
  (lambda (x)
    (tagcase x
      (x-const (ty k a b) (= ty k-int))
      (x-var (v a b) #t)
      (x-app (f args a b)
        (tagcase f
          (x-var (op fa fb)
            (let ((t (k-lookup op)) (n (symbol->string op)))
              (and (or (string=? n "+") (string=? n "-") (string=? n "length") (string=? n "string-length") (string=? n "array-length"))
                   (>= t 0) (k-named-has? (get k-std) op t))))
          (else y #f)))
      (else y #f))))
;; The size an operand of `+` or `-` of type `t` is: a natural literal's,
;; or a `(nat s)`'s (none or one).
(define k-operand-size (subr (maxeff (read @globals) (read @t) spin) (kx int) (listof k-size acyclic))
  (lambda (x t)
    (let ((lit (tagcase x (x-const (ty k a b) (if (and (= ty k-int) (>= k 0)) k -1)) (else y -1))))
      (if (>= lit 0)
          (the (listof k-size acyclic) (cons (k-size-lit lit) nil))
          (tagcase (k-get (k-resolve t)) (ty-nat (z) (the (listof k-size acyclic) (cons z nil))) (else y nil))))))
;; `(+ a b)` and `(- a b)` of naturals: the sum, and the difference where
;; the facts show it no less than 0 (none or one).
(define k-nat-arith-size (subr (maxeff (read @globals) (read @t)) (string k-size k-size) (listof k-size acyclic))
  (lambda (op a b)
    (cond ((string=? op "+") (the (listof k-size acyclic) (cons (k-size-add-scaled a b 1) nil)))
          ((and (tagcase a (sz-finite () #f) (else w #t)) (k-size-nonneg? (k-size-add-scaled a b -1)))
           (the (listof k-size acyclic) (cons (k-size-add-scaled a b -1) nil)))
          (else nil))))
;; What `p` shows about sizes when it holds, and when not (each none or
;; one): `(null? xs)`, `xs : (nlist T n)`, shows `n = 0`, or `n - 1 ≥ 0`.
;; What `p` shows about sizes when it holds, and when not (each none or
;; one). `(null? xs)`, `xs : (nlist T n)`: `n = 0`, or `n - 1 ≥ 0`. A
;; comparison of naturals: `(< a b)`, `b - a - 1 ≥ 0`, or `a - b ≥ 0`;
;; `(= a 0)`, `a = 0`, or, a natural not 0, `a - 1 ≥ 0`.
(define k-test-facts (subr (maxeff (read @globals) (read @t) (alloc @t) spin) (kx) k-branch-facts)
  (lambda (p)
    (let ((none (k-branch-facts-of nil nil)))
      (tagcase p
        (x-app (f args a b)
          (tagcase f
            (x-var (op fa fb)
              (let ((t (k-lookup op)) (name (symbol->string op)))
                (cond ((not (and (>= t 0) (k-named-has? (get k-std) op t))) none)
                      ((string=? name "null?") (if (k-sc-one-arg? args) (k-null-facts (car args)) none))
                      ((and (or (string=? name "<") (string=? name "<=") (string=? name ">") (string=? name ">=") (string=? name "="))
                            (not (null? args)) (not (null? (cdr args))) (null? (cdr (cdr args))))
                       (k-compare-facts name (car args) (car (cdr args))))
                      (else none))))
            (else y none)))
        (else y none)))))
(define k-with-fact (subr (alloc @t) ((listof k-size-fact acyclic) (listof k-size-fact acyclic)) (listof k-size-fact acyclic))
  (lambda (f fs) (if (null? f) fs (the (listof k-size-fact acyclic) (cons (car f) fs)))))
;; If `p` is `(name v)`, `name` standard, the variable, as the binding it is
;; (none or one).
(define k-certifying-test (subr (maxeff (read @globals) (read @t) (alloc @t) spin) (kx string) (listof (pairof symbol int @t) acyclic))
  (lambda (p name)
    (tagcase p
      (x-app (f args a b)
        (tagcase (k-under f)
          (x-var (op fa fb)
            (let ((t (k-lookup op)))
              (if (and (string=? (symbol->string op) name) (>= t 0) (k-named-has? (get k-std) op t) (k-sc-one-arg? args))
                  (tagcase (car args)
                    (x-var (v va vb) (the (listof (pairof symbol int @t) acyclic) (cons (cons v (k-binding-depth v)) nil)))
                    (else y nil))
                  nil)))
          (else y nil)))
      (else y nil))))
;; If `p` is `(acyclic? v)`, the variable, as the binding it is (none or one).
(define k-acyclic-test (subr (maxeff (read @globals) (read @t) (alloc @t) spin) (kx) (listof (pairof symbol int @t) acyclic))
  (lambda (p) (k-certifying-test p "acyclic?")))
;; If `p` is `(nat? v)`, the variable, as the binding it is (none or one).
(define k-nat-test (subr (maxeff (read @globals) (read @t) (alloc @t) spin) (kx) (listof (pairof symbol int @t) acyclic))
  (lambda (p) (k-certifying-test p "nat?")))
