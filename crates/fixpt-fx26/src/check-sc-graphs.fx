;;; The checker, in FX-26: size-change graphs. What each call within a
;;; recursive group says of how its arguments relate to the caller's
;;; parameters: parts known of sums, products, pairs and datums, and integer
;;; bounds. After `check-holds.fx`; `check-terminate.fx` closes them under
;;; composition (split from that file, `TODO.md` §68).

;; Its types (`check-terminate-types.fx`, its file's after it), loaded before the
;; module so that they are not among its values; the module names what it
;; uses of them.
(define check-terminate-types (load-module "fx26:check-terminate-types.fx"))
;; A module (`TODO.md` §34: the front end into modules, a file at a time);
;; what other files use re-exported after it.
(define check-sc-graphs-module (module
(define-type k-tr (select check-terminate-types k-tr))
(define tr-part (with check-terminate-types tr-part))
(define tr-int (with check-terminate-types tr-int))
(define-type k-trs (select check-terminate-types k-trs))
(define-type k-tscope (select check-terminate-types k-tscope))
(define-type k-guards (select check-terminate-types k-guards))
(define-type k-edge (select check-terminate-types k-edge))
(define-type k-graph (select check-terminate-types k-graph))
(define-type k-calls (select check-terminate-types k-calls))
(define-type k-passed (select check-terminate-types k-passed))

(define k-sc-members (ref k-names @t) (new nil))
(define k-sc-current (ref int @t) (new 0))
(define k-sc-calls (ref k-calls @t) (new nil))
;; A member named other than as a call's operator: (where . which), or none.
(define k-sc-escapes (ref (listof (pairof int int @t) acyclic) @t) (new nil))
;; For each call, as `k-sc-calls` has them: why it may shrink nothing, or "".
(define k-sc-hints (ref (listof string acyclic) @t) (new nil))
;; Whether the closure of the calls grew past `k-sc-most`.
(define k-sc-too-many (ref bool @t) (new #f))
(define k-sc-passed (ref k-passed @t) (new nil))
;; (member . parameter): passed unchanged by every call in the group, so the
;; same for the whole recursion, and a bound as a literal is.
(define k-sc-invariant (ref k-guards @t) (new nil))

(define k-sc-in? (subr (maxeff (read @globals) (read @t)) (k-tscope symbol) bool)
  (lambda (sc s) (and (not (null? sc)) (or (symbol=? (car (car sc)) s) (k-sc-in? (cdr sc) s)))))
(define k-sc-trs (subr kreads (k-tscope symbol) k-trs)
  (lambda (sc s)
    (cond ((null? sc) nil)
          ((symbol=? (car (car sc)) s) (cdr (car sc)))
          (else (k-sc-trs (cdr sc) s)))))
(define k-sc-index (subr kreads (k-names symbol int) int)
  (lambda (ns s i)
    (cond ((null? ns) -1) ((symbol=? (car ns) s) i) (else (k-sc-index (cdr ns) s (+ i 1))))))
;; Whether `s` names no member of the group.
(define k-sc-nonmember? (subr kreads (symbol) bool)
  (lambda (s) (< (k-sc-index (get k-sc-members) s 0) 0)))
;; The member `s` names, or -1 if none, or if something on the way hid it.
(define k-sc-member (subr (maxeff (read @globals) (read @t)) (k-tscope symbol) int)
  (lambda (sc s) (if (k-sc-in? sc s) -1 (k-sc-index (get k-sc-members) s 0))))
;; Whether `s`, of type `t`, names a binding of `named`'s, not hidden in `sc` by the group.
(define k-sc-named-in? (subr kreads (k-named k-tscope symbol int) bool)
  (lambda (named sc s t)
    (and (>= t 0) (not (k-sc-in? sc s)) (k-sc-nonmember? s) (k-named-has? named s t))))
;; The standard operation `f` names, or "".
(define k-sc-op (subr (maxeff kreads (alloc @t) spin) (kx k-tscope) string)
  (lambda (f sc)
    (tagcase (k-under f)
      (x-var (s a b)
        (let ((t (k-lookup s)))
          (if (and (k-std-binding? s t) (not (k-sc-in? sc s)) (k-sc-nonmember? s))
              (symbol->string s)
              "")))
      (else y ""))))
;; Whether `op` is `a` or `b`.
(define k-op-either? (subr pure (string string string) bool)
  (lambda (op a b) (or (string=? op a) (string=? op b))))
(define k-sc-literal (subr (maxeff (read @globals) (alloc @t)) (kx) k-ids)
  (lambda (x)
    (tagcase x (x-const (t v a b) (if (= t k-int) (the k-ids (cons v nil)) nil)) (else y nil))))
(define k-sc-bool? (subr (read @globals) (kx bool) bool)
  (lambda (x want)
    (tagcase x (x-const (t v a b) (and (= t k-bool) (= v (if want 1 0)))) (else y #f))))
(define k-sc-one? (subr (read @t) (kxs) bool)
  (lambda (xs) (and (not (null? xs)) (null? (cdr xs)))))
(define k-sc-two? (subr (maxeff (read @globals) (read @t)) (kxs) bool)
  (lambda (xs) (and (not (null? xs)) (k-sc-one? (cdr xs)))))

(define k-sc-part-ty (subr kreads (k-parts symbol) int)
  (lambda (ps l)
    (cond ((null? ps) -1)
          ((symbol=? (extract (car ps) 1) l) (extract (car ps) 2))
          (else (k-sc-part-ty (cdr ps) l)))))
(define k-sc-nth-ty (subr kreads (k-parts int) int)
  (lambda (ps i)
    (cond ((null? ps) -1) ((= i 0) (extract (car ps) 2)) (else (k-sc-nth-ty (cdr ps) (- i 1))))))
;; A part's type, where known (`t` ≥ 0); `void` where not, as past a
;; generative type's conversion.
(define k-ty-known (subr (maxeff kreads spin) (int) k-ty)
  (lambda (t) (if (< t 0) (ty-void) (k-get t))))
;; A union's member that is a pair, of members `ms`; or -1.
(define k-union-pair (subr (maxeff kreads spin) (k-ids) int)
  (lambda (ms)
    (cond ((null? ms) -1)
          ((tagcase (k-get (k-resolve (car ms))) (ty-pair (x d r nl) #t) (else y #f)) (car ms))
          (else (k-union-pair (cdr ms))))))
;; The same of a value taken apart as a pair: of a union, its pair member,
;; which any value `car` or `cdr` returns from is.
(define k-ty-known-pair (subr (maxeff kreads spin) (int) k-ty)
  (lambda (t)
    (if (< t 0)
        (ty-void)
        (let ((u (k-get (k-resolve t))))
          (tagcase u (ty-union (ms) (k-ty-known (k-union-pair ms))) (else y u))))))
;; `rest`, with a strict part of parameter `p`, of type `t` (-1 if not known).
(define k-sc-smaller (subr kstate (int int k-trs) k-trs)
  (lambda (p t rest) (the k-trs (cons (tr-part p #t t) rest))))
;; The type of field `l` of a part of type `t`, where known; -1 where not.
(define k-sc-field-ty (subr (maxeff kreads spin) (int symbol) int)
  (lambda (t l) (tagcase (k-ty-known t) (ty-product (ps) (k-sc-part-ty ps l)) (else y -1))))
;; Field `l` of what `ks` knows of products.
;; An `extract` proves a product, and so a part, known here or not.
(define k-sc-fields (subr (maxeff kstate spin) (k-trs symbol) k-trs)
  (lambda (ks l)
    (if (null? ks)
        nil
        (let ((rest (k-sc-fields (cdr ks) l)))
          (tagcase (car ks)
            (tr-part (p s t) (k-sc-smaller p (k-sc-field-ty t l) rest))
            (else y rest))))))
;; The type of variant `tag` of a part of type `t`, or of its field `i` (≥ 0); -1 if not known.
(define k-sc-variant-ty (subr (maxeff kreads spin) (int symbol int) int)
  (lambda (t tag i)
    (tagcase (k-ty-known t)
      (ty-sum (vs)
        (let ((v (k-sc-part-ty vs tag)))
          (cond ((< v 0) -1)
                ((< i 0) v)
                (else (tagcase (k-get v) (ty-product (ps) (k-sc-nth-ty ps i)) (else y -1))))))
      (else y -1))))
;; What an arm of a `tagcase` on what `ks` knows binds: variant `tag`'s
;; value, or (`i` ≥ 0) its field `i`.
(define k-sc-variant (subr (maxeff kstate spin) (k-trs symbol int) k-trs)
  (lambda (ks tag i)
    (if (null? ks)
        nil
        (let ((rest (k-sc-variant (cdr ks) tag i)))
          (tagcase (car ks)
            ;; A `tagcase` proves a sum, and so a part, known here or not.
            (tr-part (p s t) (k-sc-smaller p (k-sc-variant-ty t tag i) rest))
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
              (tagcase (k-ty-known-pair t)
                ;; A `nlist`'s tail is a `nlist` too: the same type serves.
                (ty-nlist (e z r) (k-sc-smaller p (if head e t) rest))
                (ty-pair (x y r nl)
                  (tagcase r
                    (r-frozen (q fin) (if fin (k-sc-smaller p (if head x y) rest) rest))
                    (else z rest)))
                (else z rest)))
            (else z rest))))))
(define k-sc-parts (subr kstate (k-trs) k-trs)
  (lambda (ks)
    (if (null? ks)
        nil
        (let ((rest (k-sc-parts (cdr ks))))
          (tagcase (car ks)
            (tr-part (p s t) (the k-trs (cons (car ks) rest)))
            (else y rest))))))
(define k-sc-shift (subr kstate (k-trs int) k-trs)
  (lambda (ks k)
    (if (null? ks)
        nil
        (let ((rest (k-sc-shift (cdr ks) k)))
          (tagcase (car ks)
            (tr-int (p o) (the k-trs (cons (tr-int p (+ o k)) rest)))
            (else y rest))))))
;; Whether `t` and `u` are both known, and the same type.
(define k-sc-same-ty? (subr (maxeff kreads spin) (int int) bool)
  (lambda (t u) (and (>= t 0) (>= u 0) (= (k-resolve t) (k-resolve u)))))
;; What both `k` and `l` say, the weaker of the two (none or one).
(define k-sc-meet-two (subr (maxeff kreads spin) (k-tr k-tr) k-trs)
  (lambda (k l)
    (tagcase k
      (tr-part (p s t)
        (tagcase l
          (tr-part (q r u)
            (if (= p q)
                (the k-trs (cons (tr-part p (and s r) (if (k-sc-same-ty? t u) t -1)) nil))
                (the k-trs nil)))
          (else y (the k-trs nil))))
      (tr-int (p o)
        (tagcase l
          (tr-int (q n) (if (and (= p q) (= o n)) (the k-trs (cons k nil)) (the k-trs nil)))
          (else y (the k-trs nil)))))))
;; What both `ks` and `ls` say, the weaker of the two: what is known of
;; either branch's value.
(define k-sc-meet-one (subr (maxeff (read @globals) (read @t) spin) (k-tr k-trs) k-trs)
  (lambda (k ls)
    (if (null? ls)
        nil
        (let ((m (k-sc-meet-two k (car ls))))
          (if (null? m) (k-sc-meet-one k (cdr ls)) m)))))
(define k-sc-meet (subr (maxeff (read @globals) (read @t) spin) (k-trs k-trs) k-trs)
  (lambda (ks ls)
    (if (null? ks)
        nil
        (let ((m (k-sc-meet-one (car ks) ls)) (rest (k-sc-meet (cdr ks) ls)))
          (if (null? m) rest (the k-trs (cons (car m) rest)))))))
;; Whether `f` names a generative type's `up-` or `down-` conversion, the
;; identity.
(define k-sc-conversion? (subr (maxeff kreads (alloc @t) spin) (kx k-tscope) bool)
  (lambda (f sc)
    (tagcase (k-under f)
      (x-var (s a b) (k-sc-named-in? (get k-conversions) sc s (k-lookup s)))
      (else y #f))))
(define k-sc-forget-types (subr kstate (k-trs) k-trs)
  (lambda (ks)
    (if (null? ks)
        nil
        (let ((k (tagcase (car ks) (tr-part (p s t) (tr-part p s -1)) (else y (car ks)))))
          (the k-trs (cons k (k-sc-forget-types (cdr ks))))))))
(define-rec
  ;; What is known of `x`'s value.
  (k-sc-tracked (subr (maxeff kstate spin) (kx k-tscope) k-trs)
    (lambda (x sc)
      (tagcase x
        (x-var (s a b) (k-sc-trs sc s))
        (x-the (t e a b) (k-sc-tracked e sc))
        (x-convention (c e a b) (k-sc-tracked e sc))
        (x-extract (e l a b) (k-sc-fields (k-sc-tracked e sc) l))
        (x-if (p c d a b) (k-sc-meet (k-sc-tracked c sc) (k-sc-tracked d sc)))
        (x-app (f args a b) (k-sc-tracked-call f args sc))
        (else y nil))))
  ;; What is known of the value of a call of `f` with `args`.
  (k-sc-tracked-call (subr (maxeff kstate spin) (kx kxs k-tscope) k-trs)
    (lambda (f args sc)
      (let ((op (k-sc-op f sc)))
        (cond ((and (k-sc-one? args) (k-sc-conversion? f sc))
               (k-sc-forget-types (k-sc-tracked (car args) sc)))
              ((and (k-sc-one? args) (k-op-either? op "car" "cdr"))
               (k-sc-pair-parts (k-sc-tracked (car args) sc) (string=? op "car")))
              ((and (k-sc-two? args) (k-op-either? op "+" "-"))
               (k-sc-tracked-shift op (car args) (car (cdr args)) sc))
              (else nil)))))
  ;; What is known of `(op x1 x2)`, `op` `+` or `-`: an operand, counted on by a literal other.
  (k-sc-tracked-shift (subr (maxeff kstate spin) (string kx kx k-tscope) k-trs)
    (lambda (op x1 x2 sc)
      (let ((ka (k-sc-literal x1)) (kb (k-sc-literal x2)))
        (cond ((not (null? kb))
               (k-sc-shift (k-sc-tracked x1 sc) (if (string=? op "+") (car kb) (- 0 (car kb)))))
              ((and (not (null? ka)) (string=? op "+")) (k-sc-shift (k-sc-tracked x2 sc) (car ka)))
              (else nil))))))
(define k-sc-guarded? (subr kreads (k-guards int int) bool)
  (lambda (gs p b)
    (and (not (null? gs))
         (or (and (= (car (car gs)) p) (= (cdr (car gs)) b)) (k-sc-guarded? (cdr gs) p b)))))
;; The current member's parameters that are `nat`s: bounded below by 0
;; without a test, since every argument passed for one is checked a natural.
(define k-sc-naturals (ref k-ids @t) (new nil))
;; Whether parameter `p` is bounded its way `b` (0 below, 1 above): by a
;; test, or, below, by being a `nat`.
(define k-sc-bounded? (subr (maxeff (read @globals) (read @t)) (k-guards int int) bool)
  (lambda (gs p b) (or (k-sc-guarded? gs p b) (and (= b 0) (k-has-id? (get k-sc-naturals) p)))))
;; Whether parameter `p`, of the member walked, is passed on unchanged by every call.
(define k-sc-invariant? (subr kreads (int) bool)
  (lambda (p) (k-sc-guarded? (get k-sc-invariant) (get k-sc-current) p)))
;; Whether `ks` knows a value as a parameter, of the member walked, passed on
;; unchanged by every call.
(define k-sc-invariant-in? (subr (maxeff (read @globals) (read @t)) (k-trs) bool)
  (lambda (ks)
    (and (not (null? ks))
         (or (tagcase (car ks) (tr-part (p s t) (and (not s) (k-sc-invariant? p))) (else y #f))
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
          (if (k-sc-in? sc s) (k-sc-invariant-in? (k-sc-trs sc s)) (k-sc-nonmember? s)))
        (x-the (t e a b) (k-sc-fixed? e sc))
        (x-convention (c e a b) (k-sc-fixed? e sc))
        (x-app (f args a b)
          (let ((op (k-sc-op f sc)))
            ;; An array's length never changes, as a string's does not.
            (and (or (and (k-op-either? op "string-length" "array-length") (k-sc-one? args))
                     (and (k-op-either? op "+" "-") (k-sc-two? args)))
                 (k-sc-all-fixed? args sc))))
        (else y #f))))
  (k-sc-all-fixed? (subr (maxeff kstate spin) (kxs k-tscope) bool)
    (lambda (xs sc) (or (null? xs) (and (k-sc-fixed? (car xs) sc) (k-sc-all-fixed? (cdr xs) sc))))))
(define k-sc-append (subr kstate (k-guards k-guards) k-guards)
  (lambda (xs ys) (if (null? xs) ys (the k-guards (cons (car xs) (k-sc-append (cdr xs) ys))))))
(define k-sc-with (subr kstate (int k-ids k-guards) k-guards)
  (lambda (p bs rest)
    (if (null? bs) rest (the k-guards (cons (cons p (car bs)) (k-sc-with p (cdr bs) rest))))))
;; Bounds `bs` on each integer parameter `ks` knows of.
(define k-sc-bounds-on (subr kstate (k-trs k-ids) k-guards)
  (lambda (ks bs)
    (if (null? ks)
        nil
        (let ((rest (k-sc-bounds-on (cdr ks) bs)))
          (tagcase (car ks) (tr-int (p o) (k-sc-with p bs rest)) (else y rest))))))
(define k-sc-flip (subr kstate (k-ids) k-ids)
  (lambda (bs) (if (null? bs) nil (the k-ids (cons (- 1 (car bs)) (k-sc-flip (cdr bs)))))))
;; The bounds on `x1` that `(op x1 x2)`, `x2` fixed, having the value `holds` shows.
(define k-sc-left-bounds (subr kstate (string bool) k-ids)
  (lambda (op holds)
    (let ((lt (k-op-either? op "<" "<=")) (gt (k-op-either? op ">" ">=")))
      (the k-ids (cond ((or (and lt holds) (and gt (not holds))) (cons 1 nil))
                       ((or (and lt (not holds)) (and gt holds)) (cons 0 nil))
                       ((and (string=? op "=") holds) (list 0 1))
                       (else nil))))))
;; Bounds `bs` on each integer parameter known of `x`, if `other`, compared with it, is fixed.
(define k-sc-compared (subr (maxeff kstate spin) (kx kx k-tscope k-ids) k-guards)
  (lambda (x other sc bs) (if (k-sc-fixed? other sc) (k-sc-bounds-on (k-sc-tracked x sc) bs) nil)))
;; The bounds on parameters that `x` having the value `holds` shows.
(define k-sc-facts (subr (maxeff kstate spin) (kx k-tscope bool) k-guards)
  (lambda (x sc holds)
    (tagcase x
      (x-app (f args a b)
        (let ((op (k-sc-op f sc)))
          (cond ((and (k-sc-one? args) (string=? op "not")) (k-sc-facts (car args) sc (not holds)))
                ((k-sc-two? args)
                 (let ((left (k-sc-left-bounds op holds)) (x1 (car args)) (x2 (car (cdr args))))
                   (k-sc-append (k-sc-compared x1 x2 sc left)
                                (k-sc-compared x2 x1 sc (k-sc-flip left)))))
                (else nil))))
      ;; `(and p c)` and `(or p d)`, as they are parsed.
      (x-if (p c d a b)
        (cond ((and holds (k-sc-bool? d #f))
               (k-sc-append (k-sc-facts p sc #t) (k-sc-facts c sc #t)))
              ((and (not holds) (k-sc-bool? c #t))
               (k-sc-append (k-sc-facts p sc #f) (k-sc-facts d sc #f)))
              (else nil)))
      (else y nil))))

;; An edge from slot `f` to slot `t`, strict if `s`.
(define k-sc-edge (subr kstate (int int bool) k-edge) (lambda (f t s) (product (1 f) (2 t) (3 s))))
;; `g` with the edge from slot `f` to slot `t`, strict if `s`.
(define k-sc-add (subr kstate (k-graph int int bool) k-graph)
  (lambda (g f t s)
    (if (null? g)
        (the k-graph (cons (k-sc-edge f t s) nil))
        (let* ((e (car g)) (ef (extract e 1)) (et (extract e 2)))
          (cond ((and (= ef f) (= et t))
                 (the k-graph (cons (k-sc-edge f t (or s (extract e 3))) (cdr g))))
                ((or (< f ef) (and (= f ef) (< t et))) (the k-graph (cons (k-sc-edge f t s) g)))
                (else (the k-graph (cons e (k-sc-add (cdr g) f t s)))))))))
;; `g` with the edge from `p`'s measure `m` (1 down, 2 up) to `q`'s, for a count moved `d` that way.
(define k-sc-count-edge (subr kstate (k-graph int int int int bool) k-graph)
  (lambda (g p q m d bounded)
    (cond ((and (> d 0) bounded) (k-sc-add g (+ (* 3 p) m) (+ (* 3 q) m) #t))
          ((>= d 0) (k-sc-add g (+ (* 3 p) m) (+ (* 3 q) m) #f))
          (else g))))
;; The edges to argument `q` from what `ks` knows of it.
(define k-sc-tr-edges (subr kstate (k-trs int k-guards k-graph) k-graph)
  (lambda (ks q gs g)
    (if (null? ks)
        g
        (k-sc-tr-edges (cdr ks) q gs
          (tagcase (car ks)
            (tr-part (p s t) (k-sc-add g (* 3 p) (* 3 q) s))
            (tr-int (p o)
              (let ((g1 (k-sc-count-edge g p q 1 (- 0 o) (k-sc-bounded? gs p 0))))
                (k-sc-count-edge g1 p q 2 o (k-sc-bounded? gs p 1)))))))))
(define k-sc-arg-edges (subr (maxeff kstate spin) (kxs int k-tscope k-guards k-graph) k-graph)
  (lambda (args q sc gs g)
    (if (null? args)
        g
        (let ((g1 (k-sc-tr-edges (k-sc-tracked (car args) sc) q gs g)))
          (k-sc-arg-edges (cdr args) (+ q 1) sc gs g1)))))
;; The parameter `ks` knows a value as, passed on unchanged, or -1.
(define k-sc-unchanged (subr kstate (k-trs) int)
  (lambda (ks)
    (if (null? ks)
        -1
        (tagcase (car ks)
          (tr-part (p s t) (if s (k-sc-unchanged (cdr ks)) p))
          (else y (k-sc-unchanged (cdr ks)))))))
(define k-sc-passing (subr (maxeff kstate spin) (kxs k-tscope) k-ids)
  (lambda (args sc)
    (if (null? args)
        nil
        (let ((p (k-sc-unchanged (k-sc-tracked (car args) sc))))
          (the k-ids (cons p (k-sc-passing (cdr args) sc)))))))
;; Whether `t` is known, a pair at a region that is not `acyclic`.
(define k-sc-written-pair? (subr (maxeff kreads spin) (int) bool)
  (lambda (t)
    (tagcase (k-ty-known t)
      (ty-pair (x y r nl) (tagcase r (r-frozen (q fin) (not fin)) (else z #t)))
      (else z #f))))
;; Whether `ks` knows of a pair at a region that is not `acyclic`.
(define k-sc-any-written? (subr (maxeff (read @globals) (read @t) spin) (k-trs) bool)
  (lambda (ks)
    (and (not (null? ks))
         (or (tagcase (car ks) (tr-part (p s t) (k-sc-written-pair? t)) (else z #f))
             (k-sc-any-written? (cdr ks))))))
;; Whether some argument is the `car` or `cdr` of a parameter's part at a
;; region that is not `acyclic`.
(define k-sc-written-arg? (subr (maxeff kstate spin) (kxs k-tscope) bool)
  (lambda (args sc)
    (and (not (null? args))
         (or (tagcase (car args)
               (x-app (f xs a b)
                 (let ((op (k-sc-op f sc)))
                   (and (k-op-either? op "car" "cdr") (k-sc-one? xs)
                        (k-sc-any-written? (k-sc-tracked (car xs) sc)))))
               (else y #f))
             (k-sc-written-arg? (cdr args) sc)))))
;; Why a count of parameter `p`, moved `o`, has no fixed bound that way, in words; or "".
(define k-sc-unbounded-why (subr kreads (int int k-guards) string)
  (lambda (p o gs)
    (cond ((and (< o 0) (not (k-sc-bounded? gs p 0)))
           "it counts down, but nothing fixed bounds the count below")
          ((and (> o 0) (not (k-sc-bounded? gs p 1)))
           "it counts up, but nothing fixed bounds the count above")
          (else ""))))
;; The first count in `ks` with no fixed bound its way, in words, or "".
(define k-sc-count-hint (subr (maxeff (read @globals) (read @t)) (k-trs k-guards) string)
  (lambda (ks gs)
    (if (null? ks)
        ""
        (let ((h (tagcase (car ks) (tr-int (p o) (k-sc-unbounded-why p o gs)) (else y ""))))
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
;; A call of member `to` with `args`, from the member walked.
(define k-sc-call (subr (maxeff kstate spin) (int kxs k-tscope k-guards) unit)
  (lambda (to args sc gs)
    (let ((from (get k-sc-current)) (passing (k-sc-passing args sc)))
      (begin
        (set k-sc-hints (cons (k-sc-hint args sc gs) (get k-sc-hints)))
        (set k-sc-passed (cons (product (1 from) (2 to) (3 passing)) (get k-sc-passed)))
        (let ((g (k-sc-arg-edges args 0 sc gs nil)))
          (set k-sc-calls (cons (product (1 from) (2 to) (3 g)) (get k-sc-calls))))))))

;; `sc` with `s` bound, known as what `ks` says.
(define k-sc-bind (subr kstate (symbol k-trs k-tscope) k-tscope)
  (lambda (s ks sc) (the k-tscope (cons (cons s ks) sc))))
(define k-sc-hide-params (subr kstate (k-typed-params k-tscope) k-tscope)
  (lambda (ps sc)
    (if (null? ps) sc (k-sc-hide-params (cdr ps) (k-sc-bind (extract (car ps) 1) nil sc)))))
(define k-sc-hide-group (subr kstate (k-letrec-bs k-tscope) k-tscope)
  (lambda (bs sc)
    (if (null? bs) sc (k-sc-hide-group (cdr bs) (k-sc-bind (extract (car bs) 1) nil sc)))))
(define k-sc-let-scope (subr (maxeff kstate spin) (k-let-bs k-tscope k-tscope) k-tscope)
  (lambda (bs outer sc)
    (if (null? bs)
        sc
        (let ((ks (k-sc-tracked (extract (car bs) 2) outer)))
          (k-sc-let-scope (cdr bs) outer (k-sc-bind (extract (car bs) 1) ks sc))))))
(define k-sc-arm-scope (subr (maxeff kstate spin) (k-names k-trs symbol int k-tscope) k-tscope)
  (lambda (ns whole tag i sc)
    (if (null? ns)
        sc
        (let ((ks (k-sc-variant whole tag i)))
          (k-sc-arm-scope (cdr ns) whole tag (+ i 1) (k-sc-bind (car ns) ks sc))))))
;; Note member `m` named other than as a call's operator, unless one has been already.
(define k-sc-escape (subr kstate (int) unit)
  (lambda (m)
    (if (null? (get k-sc-escapes)) (set k-sc-escapes (cons (cons (get k-sc-current) m) nil)) #u)))
;; `sc` with `ns` hidden: bound, and none of the group's.
(define k-sc-hide-names (subr kstate (k-names k-tscope) k-tscope)
  (lambda (ns sc) (if (null? ns) sc (k-sc-hide-names (cdr ns) (k-sc-bind (car ns) nil sc)))))
(define-rec
  ;; A module's values made, each as any expression is, every item's names
  ;; in scope, as a `letrec*`'s.
  (k-sc-walk-values (subr (maxeff kstate spin) (k-items k-tscope k-guards) unit)
    (lambda (items sc gs)
      (if (null? items)
          #u
          (let ((k (extract (car items) 1)))
            (begin (if (or (= k 2) (= k 3)) (k-sc-walk-list (extract (car items) 5) sc gs) #u)
                   (k-sc-walk-values (cdr items) sc gs))))))
  (k-sc-walk-items (subr (maxeff kstate spin) (k-items k-tscope k-guards) unit)
    (lambda (items sc gs)
      (k-sc-walk-values items (k-sc-hide-names (k-items-bound items nil) sc) gs)))
  ;; A module's values made, and a `with`'s module named, each as any
  ;; expression or variable is.
  (k-sc-walk-modular (subr (maxeff kstate spin) (kx k-tscope k-guards) unit)
    (lambda (x sc gs)
      (tagcase x
        (x-module (items a b) (k-sc-walk-items items sc gs))
        (x-with (m body a b)
          (let ((member (k-sc-member sc m)))
            (begin (if (>= member 0) (k-sc-escape member) #u)
                   (k-sc-walk body (k-sc-hide-names (k-with-names a b) sc) gs))))
        (else y #u))))
  (k-sc-walk-list (subr (maxeff kstate spin) (kxs k-tscope k-guards) unit)
    (lambda (xs sc gs)
      (if (null? xs) #u (begin (k-sc-walk (car xs) sc gs) (k-sc-walk-list (cdr xs) sc gs)))))
  (k-sc-walk-group (subr (maxeff kstate spin) (k-letrec-bs k-tscope k-guards) unit)
    (lambda (bs sc gs)
      (if (null? bs)
          #u
          (begin (k-sc-walk (extract (car bs) 3) sc gs) (k-sc-walk-group (cdr bs) sc gs)))))
  ;; A `let`'s inits, or a product's fields.
  (k-sc-walk-labeled (subr (maxeff kstate spin) (k-let-bs k-tscope k-guards) unit)
    (lambda (bs sc gs)
      (if (null? bs)
          #u
          (begin (k-sc-walk (extract (car bs) 2) sc gs) (k-sc-walk-labeled (cdr bs) sc gs)))))
  (k-sc-walk-arms (subr (maxeff kstate spin) (k-arms k-trs k-tscope k-guards) unit)
    (lambda (arms whole sc gs)
      (if (null? arms)
          #u
          (let* ((arm (car arms))
                 (tag (extract arm 1))
                 (inner (if (extract arm 2)
                            (k-sc-arm-scope (extract arm 3) whole tag 0 sc)
                            (k-sc-bind (car (extract arm 3)) (k-sc-variant whole tag -1) sc))))
            (begin (k-sc-walk (extract arm 4) inner gs) (k-sc-walk-arms (cdr arms) whole sc gs))))))
  ;; A `tagcase`'s `else`, if any, which sees the same value, its type narrowed.
  (k-sc-walk-else (subr (maxeff kstate spin) (k-let-bs k-trs k-tscope k-guards) unit)
    (lambda (els whole sc gs)
      (if (null? els)
          #u
          (let ((y (extract (car els) 1)) (body (extract (car els) 2)))
            (k-sc-walk body (k-sc-bind y (k-sc-parts whole) sc) gs)))))
  (k-sc-walk (subr (maxeff kstate spin) (kx k-tscope k-guards) unit)
    (lambda (x sc gs)
      (tagcase x
        (x-var (s a b)
          (let ((m (k-sc-member sc s)))
            (if (>= m 0) (k-sc-escape m) #u)))
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
        (x-let (bs body a b)
          (begin (k-sc-walk-labeled bs sc gs) (k-sc-walk body (k-sc-let-scope bs sc sc) gs)))
        (x-begin (xs a b) (k-sc-walk-list xs sc gs))
        (x-bloblet (n i xs a b) (k-sc-walk-list xs sc gs))
        (x-prompt (t body h a b)
          (begin (k-sc-walk t sc gs) (k-sc-walk body sc gs) (k-sc-walk h sc gs)))
        (x-product (fs a b) (k-sc-walk-labeled fs sc gs))
        (x-extract (e l a b) (k-sc-walk e sc gs))
        (x-sum (tag e a b) (k-sc-walk e sc gs))
        (x-tagcase (e arms els a b)
          (let ((whole (k-sc-tracked e sc)))
            (begin (k-sc-walk e sc gs)
                   (k-sc-walk-arms arms whole sc gs)
                   (k-sc-walk-else els whole sc gs))))
        (x-module (items a b) (k-sc-walk-modular x sc gs))
        (x-with (m body a b) (k-sc-walk-modular x sc gs))))))))

(define k-op-either? (with check-sc-graphs-module k-op-either?))
(define k-sc-add (with check-sc-graphs-module k-sc-add))
(define k-sc-bind (with check-sc-graphs-module k-sc-bind))
(define k-sc-calls (with check-sc-graphs-module k-sc-calls))
(define k-sc-current (with check-sc-graphs-module k-sc-current))
(define k-sc-escape (with check-sc-graphs-module k-sc-escape))
(define k-sc-escapes (with check-sc-graphs-module k-sc-escapes))
(define k-sc-guarded? (with check-sc-graphs-module k-sc-guarded?))
(define k-sc-hints (with check-sc-graphs-module k-sc-hints))
(define k-sc-invariant (with check-sc-graphs-module k-sc-invariant))
(define k-sc-member (with check-sc-graphs-module k-sc-member))
(define k-sc-members (with check-sc-graphs-module k-sc-members))
(define k-sc-naturals (with check-sc-graphs-module k-sc-naturals))
(define k-sc-one? (with check-sc-graphs-module k-sc-one?))
(define k-sc-passed (with check-sc-graphs-module k-sc-passed))
(define k-sc-too-many (with check-sc-graphs-module k-sc-too-many))
(define k-sc-two? (with check-sc-graphs-module k-sc-two?))
(define k-sc-walk (with check-sc-graphs-module k-sc-walk))
(define k-sc-walk-list (with check-sc-graphs-module k-sc-walk-list))
(define k-sc-with (with check-sc-graphs-module k-sc-with))
