;;; The checker, in FX-26: calls that may not end, and what is only called.
;;; Part of the checker, `check-types.fx` first (moved out of
;;; `check-subtype.fx`, 2026-10-04).

;;; ------------------------------------------------------------ calls that may not end

;; Its types, those it uses of the files before it, and the signatures of
;; what it is given.
(let* ((check-calls-types (load-module "fx26:check-calls-types.fx"))
       (check-types-types (load-module "fx26:check-types-types.fx"))
       (check-resolve-types (load-module "fx26:check-resolve-types.fx"))
       (check-subst-types (load-module "fx26:check-subst-types.fx"))
       (check-holds-types (load-module "fx26:check-holds-types.fx"))
       (check-env-types (load-module "fx26:check-env-types.fx"))
       (check-expect-types (load-module "fx26:check-expect-types.fx"))
       (check-effects-types (load-module "fx26:check-effects-types.fx"))
       (check-modules-types (load-module "fx26:check-modules-types.fx"))
       (check-read-helpers-types (load-module "fx26:check-read-helpers-types.fx")))
  ;; What it is given: the modules of the files before it that it uses.
  (lambda ((check-types (select check-types-types check-types-sig))
           (check-resolve (select check-resolve-types check-resolve-sig))
           (check-holds (select check-holds-types check-holds-sig))
           (check-env (select check-env-types check-env-sig))
           (check-expect (select check-expect-types check-expect-sig))
           (check-effects (select check-effects-types check-effects-sig))
           (check-modules (select check-modules-types check-modules-sig))
           (check-read-helpers (select check-read-helpers-types check-read-helpers-sig)))
    (module
(hide (include check-calls-types) (include check-types-types) (include check-resolve-types)
      (include check-subst-types))
;; The types it uses of the files before it.
;; What it uses of the modules it is given: all of each, hidden.
(hide (include check-types) (include check-resolve) (include check-holds) (include check-env)
      (include check-expect) (include check-effects) (include check-modules)
      (include check-read-helpers))

(define k-on-path? (subr kreads (k-cpath int) bool)
  (lambda (path t) (and (not (null? path)) (or (= (car (car path)) t) (k-on-path? (cdr path) t)))))
;; Whether a node newer than `t` on the path was reached through a parameter.
(define k-newer-param? (subr kreads (k-cpath int) bool)
  (lambda (path t)
    (and (not (= (car (car path)) t)) (or (cdr (car path)) (k-newer-param? (cdr path) t)))))
(define-rec
  (k-cyclic-from? (subr (maxeff kstate spin) (int bool k-cpath) bool)
    (lambda (t by path)
      (let ((t (k-resolve t)))
        (cond ((k-on-path? path t) (or by (k-newer-param? path t)))
              ;; Too deep to follow: it may loop, the cautious answer.
              ((> (k-length path) 64) #t)
              (else
               (let ((p (the k-cpath (cons (cons t by) path))))
                 (tagcase (k-get t)
                   (ty-subr (e ps r cv) (or (k-cyclic-list? ps #t p) (k-cyclic-from? r #f p)))
                   (ty-comp (x a e r) (or (k-cyclic-from? x #t p) (k-cyclic-from? a #f p)))
                   (ty-tag (a h e r) (or (k-cyclic-from? a #f p) (k-cyclic-from? h #f p)))
                   (ty-poly (bs x) (k-cyclic-from? x #f p))
                   (ty-ref (a r) (k-cyclic-from? a #f p))
                   (ty-array (a nz r) (k-cyclic-from? a #f p))
                   (ty-icell (a r) (k-cyclic-from? a #f p))
                   (ty-markkey (a r) (k-cyclic-from? a #f p))
                   (ty-pair (a b r nl) (or (k-cyclic-from? a #f p) (k-cyclic-from? b #f p)))
                   (ty-bloblet (fs z r) (k-cyclic-list? fs #f p))
                   (ty-product (ps) (k-cyclic-parts? ps p))
                   (ty-sum (ps) (k-cyclic-parts? ps p))
                   (ty-union (ms) (k-cyclic-list? ms #f p))
                   ;; Through its representation; what it was given,
                   ;; cautiously, as if taken as a parameter.
                   (ty-named (g ds)
                     (or (k-cyclic-from? (extract (k-gen-of g) 4) #f p)
                         (k-cyclic-list? (k-ds-types ds) #t p)))
                   ;; A description function applied, unseen: what it was
                   ;; given, cautiously, as if taken as a parameter.
                   (ty-app (f ds) (k-cyclic-list? (k-ds-types ds) #t p))
                   (ty-nlist (e z r) (k-cyclic-from? e #f p))
                   (else x #f))))))))
  (k-cyclic-list? (subr (maxeff kstate spin) (k-ids bool k-cpath) bool)
    (lambda (ts by path)
      (and (not (null? ts))
           (or (k-cyclic-from? (car ts) by path) (k-cyclic-list? (cdr ts) by path)))))
  (k-cyclic-parts? (subr (maxeff kstate spin) (k-parts k-cpath) bool)
    (lambda (ps path)
      (and (not (null? ps))
           (or (k-cyclic-from? (extract (car ps) 2) #f path) (k-cyclic-parts? (cdr ps) path))))))
(define k-cyclic? (subr (maxeff kstate spin) (int) bool)
  (lambda (t) (k-cyclic-from? t #f nil)))
;; Whether `t` mentions any of `vs`.
(define k-mentions-any? (subr (maxeff kstate spin) (int k-ids) bool)
  (lambda (t vs)
    (and (not (null? vs)) (or (k-mentions-var? t (car vs)) (k-mentions-any? t (cdr vs))))))
;; Whether `t` has, below its top (`top`), a procedure type that mentions
;; one of `vs`: what code of type `t` could call. `seen`, the nodes walked.
(define-rec
  (k-calls-through? (subr (maxeff kstate spin) (int k-ids bool (ref k-ids @t)) bool)
    (lambda (t vs top seen)
      (let ((t (k-resolve t)))
        (and (not (k-has-id? (get seen) t))
             (begin
               (set seen (cons t (get seen)))
               (tagcase (k-get t)
                 (ty-subr (e ps r cv)
                   (or (and (not top) (k-mentions-any? t vs))
                       (k-calls-through-list? (k-ty-kids t) vs seen)))
                 (ty-comp (x a e r)
                   (or (k-mentions-any? t vs) (k-calls-through-list? (k-ty-kids t) vs seen)))
                 (ty-named (g ds)
                   (k-calls-through-list?
                    (the k-ids (cons (extract (k-gen-of g) 4) (k-ds-types ds))) vs seen))
                 (ty-app (f ds) (k-calls-through-list? (k-ds-types ds) vs seen))
                 (ty-lam (bs x) #f)
                 (ty-module (abs ds xs) #f)
                 (else y (k-calls-through-list? (k-ty-kids t) vs seen))))))))
  (k-calls-through-list? (subr (maxeff kstate spin) (k-ids k-ids (ref k-ids @t)) bool)
    (lambda (ts vs seen)
      (and (not (null? ts))
           (or (k-calls-through? (car ts) vs #f seen) (k-calls-through-list? (cdr ts) vs seen))))))
;; `t` with `spin` in the latent effect of each procedure it gives: itself,
;; what it returns, those in products and sums (not in what may be written,
;; a pair's or a reference's). `done`: each node made so far, as a slot
;; linked once made, so a cycle is made a cycle.
(define-rec
  (k-spin-positive (subr (maxeff kstate spin) (int (ref k-spun @t)) int)
    (lambda (t done)
      (let* ((t (k-resolve t)) (old (k-spun-of (get done) t)))
        (cond ((>= old 0) old)
              ((not (tagcase (k-get t)
                      (ty-subr (e ps r cv) #t) (ty-poly (bs x) #t)
                      (ty-product (ps) #t) (ty-sum (ps) #t) (else y #f)))
               t)
              (else
               (let ((slot (k-slot)))
                 (begin
                   (set done (cons (cons t slot) (get done)))
                   (k-set-link slot (k-ty-new (k-spin-node t done)))
                   slot)))))))
  ;; Node `t`, a procedure, poly, product or sum, made with `spin`.
  (k-spin-node (subr (maxeff kstate spin) (int (ref k-spun @t)) k-ty)
    (lambda (t done)
      (tagcase (k-get t)
        (ty-subr (e ps r cv) (ty-subr (k-insert (a-spin) e) ps (k-spin-positive r done) cv))
        (ty-poly (bs x) (ty-poly bs (k-spin-positive x done)))
        (ty-product (ps) (ty-product (k-spin-parts ps done)))
        (ty-sum (ps) (ty-sum (k-spin-parts ps done)))
        (else y (k-get t)))))
  (k-spin-parts (subr (maxeff kstate spin) (k-parts (ref k-spun @t)) k-parts)
    (lambda (ps done)
      (if (null? ps)
          nil
          (let* ((x (k-spin-positive (extract (car ps) 2) done))
                 (rest (k-spin-parts (cdr ps) done)))
            (cons (product (1 (extract (car ps) 1)) (2 x)) rest))))))
;; What `t` is made into, in `done`, or -1.
(define k-spun-of (subr kreads (k-spun int) int)
  (lambda (done t)
    (cond ((null? done) -1)
          ((= (car (car done)) t) (cdr (car done)))
          (else (k-spun-of (cdr done) t)))))
;; The binders of `m` given a cyclic type (`k-cyclic?`).
(define k-cyclic-binders (subr (maxeff kstate spin) (k-map) k-ids)
  (lambda (m)
    (cond ((null? m) nil)
          ((k-any-cyclic? (k-d-types (cdr (car m))))
           (the k-ids (cons (car (car m)) (k-cyclic-binders (cdr m)))))
          (else (k-cyclic-binders (cdr m))))))
(define k-any-cyclic? (subr (maxeff kstate spin) (k-ids) bool)
  (lambda (ts) (and (not (null? ts)) (or (k-cyclic? (car ts)) (k-any-cyclic? (cdr ts))))))
;; A polymorphic value of type `inner`, instantiated by `m` as `t`: if a
;; type it was given is cyclic (a procedure of it could be given itself) and
;; the value is given a procedure whose type mentions that binder, its code
;; may call that procedure on what it is given, a self-application its body
;; could not see. So each procedure it gives says `spin`
;; (`docs/research/soundness-findings.md`). In both checkers
;; (`Checker::spin_for_cyclic`).
(define k-spin-for-cyclic (subr (maxeff kstate spin) (int int k-map) int)
  (lambda (inner t m)
    (let ((vs (k-cyclic-binders m)))
      (if (or (null? vs) (not (k-calls-through? inner vs #t (the (ref k-ids @t) (new nil)))))
          t
          (k-spin-positive t (the (ref k-spun @t) (new nil)))))))
;; A prompt tag's parts: what its prompts deliver, what its aborts carry,
;; its bodies' bound and its region, and whether it has a bound. One of a
;; `prompt-tag`, or of an escape-only tag (generative type 9, `TODO.md`
;; §89), which is never captured and so bounds nothing; none of anything
;; else.
(define k-tag-parts (subr (maxeff kreads (alloc @t) spin) (int) k-tag-parts)
  (lambda (tt)
    (tagcase (k-get tt)
      (ty-tag (a h e r) (the k-tag-parts (cons (product (1 a) (2 h) (3 e) (4 r) (5 #t)) nil)))
      (ty-named (g ds)
        (if (and (= g 9) (= (k-length ds) 3))
            (tagcase (car ds)
              (dt (a)
                (tagcase (car (cdr ds))
                  (dt (h)
                    (tagcase (car (cdr (cdr ds)))
                      (dr (r)
                        (the k-tag-parts (cons (product (1 a) (2 h) (3 nil) (4 r) (5 #f)) nil)))
                      (else z nil)))
                  (else z nil)))
              (else z nil))
            nil))
      (else y nil))))
;; `f` under any projections and ascriptions.
(define k-under (subr (read @globals) (kx) kx)
  (lambda (f)
    (tagcase f
      (x-proj (body ds a b abk) (k-under body))
      (x-the (t body a b abk) (k-under body))
      (else y f))))
;; Whether `k` is named in `x` only as the operator of calls, evaluated as
;; `x` is: not under a `lambda` (which could be called later) or a prompt
;; (whose captures could be composed later).
(define-rec
  (k-only-called? (subr kmakes (kx symbol) bool)
    (lambda (x k)
      (tagcase x
        (x-var (s a b abk) (not (symbol=? s k)))
        (x-const (t v a b abk) #t)
        (x-app (f args a b abk)
          (and (or (tagcase f (x-var (s fa fb fafbk) (symbol=? s k)) (else y #f))
                   (k-only-called? f k))
               (k-only-called-list? args k)))
        (x-lambda (ps body a b abk) (not (k-has-name? (k-free-vars x) k)))
        (x-plambda (bs body a b abk) (not (k-has-name? (k-free-vars x) k)))
        (x-rlambda (r l a b abk) (not (k-has-name? (k-free-vars x) k)))
        (x-letrec (bs body a b abk) (not (k-has-name? (k-free-vars x) k)))
        (x-prompt (t body h a b abk) (not (k-has-name? (k-free-vars x) k)))
        (x-let (bs body a b abk)
          (and (k-only-called-lets? bs k)
               (or (k-has-name? (k-let-names bs nil) k) (k-only-called? body k))))
        (x-letregion (m r i body a b abk) (or (symbol=? (k-dvar-name r) k) (k-only-called? body k)))
        (x-tagcase (s arms els a b abk)
          (and (k-only-called? s k)
               (k-only-called-arms? arms k)
               (k-only-called-else? els k)))
        (x-proj (body ds a b abk) (k-only-called? body k))
        (x-the (t body a b abk) (k-only-called? body k))
        (x-convention (c body a b abk) (k-only-called? body k))
        (x-extract (body l a b abk) (k-only-called? body k))
        (x-sum (l body a b abk) (k-only-called? body k))
        (x-if (p c d a b abk) (and (k-only-called? p k) (k-only-called? c k) (k-only-called? d k)))
        (x-begin (xs a b abk) (k-only-called-list? xs k))
        (x-bloblet (o i xs a b abk) (k-only-called-list? xs k))
        (x-product (fs a b abk) (k-only-called-lets? fs k))
        (x-module (items a b abk) (not (k-has-name? (k-free-vars x) k)))
        (x-with (m body a b abk) (not (k-has-name? (k-free-vars x) k))))))
  (k-only-called-list? (subr kmakes (kxs symbol) bool)
    (lambda (xs k)
      (or (null? xs) (and (k-only-called? (car xs) k) (k-only-called-list? (cdr xs) k)))))
  (k-only-called-lets? (subr kmakes (k-let-bs symbol) bool)
    (lambda (bs k)
      (or (null? bs)
          (and (k-only-called? (extract (car bs) 2) k) (k-only-called-lets? (cdr bs) k)))))
  (k-only-called-arms? (subr kmakes (k-arms symbol) bool)
    (lambda (arms k)
      (or (null? arms)
          (and (or (k-has-name? (extract (car arms) 3) k) (k-only-called? (extract (car arms) 4) k))
               (k-only-called-arms? (cdr arms) k)))))
  ;; A `tagcase`'s `else` arm, if any, unless its variable is `k`.
  (k-only-called-else? (subr kmakes (k-let-bs symbol) bool)
    (lambda (els k)
      (or (null? els)
          (symbol=? (extract (car els) 1) k)
          (k-only-called? (extract (car els) 2) k)))))
;; Whether an effect has a `comefrom`.
(define k-has-comefrom? (subr kreads (k-eff) bool)
  (lambda (e)
    (and (not (null? e))
         (or (tagcase (car e) (a-comefrom (r) #t) (else y #f)) (k-has-comefrom? (cdr e))))))
;; Whether the receiver of `cwcc` at type `ft` may capture a continuation:
;; its latent effect has a `comefrom`. Unknown counts as may.
(define k-receiver-captures? (subr (maxeff kmakes spin) (int) bool)
  (lambda (ft)
    (let ((c (k-as-subr ft)))
      (or (null? c) (null? (extract (car c) 2))
          (let ((r (k-as-subr (k-resolve (car (extract (car c) 2))))))
            (or (null? r) (k-has-comefrom? (extract (car r) 1))))))))
;; Whether `r`, given to `cwcc`, is a `lambda` whose continuation can only
;; be called while `cwcc` runs, so can only leave it
;; (`docs/research/soundness-findings.md`, F3).
(define k-escape-only? (subr kmakes (kx) bool)
  (lambda (r)
    (tagcase r
      (x-the (t body a b abk) (k-escape-only? body))
      (x-lambda (ps body a b abk)
        (and (not (null? ps)) (null? (cdr ps)) (k-only-called? body (extract (car ps) 1))))
      (else y #f))))
;; The name `f` is, under any projections and ascriptions, if a variable.
(define k-callee-name (subr (maxeff (read @globals) (alloc @t)) (kx) (listof symbol acyclic))
  (lambda (f)
    (tagcase f
      (x-proj (body ds a b abk) (k-callee-name body))
      (x-the (t body a b abk) (k-callee-name body))
      (x-var (n a b abk) (the (listof symbol acyclic) (cons n nil)))
      (else y (the (listof symbol acyclic) nil)))))
;; The standard name `x` refers to, "" if none: a variable that is the
;; standard binding where it is used, or `(with #%fx n)` (`TODO.md` §46).
;; Every rule for a standard operation asks this.
(define k-std-op (subr (maxeff kreads spin) (kx) string)
  (lambda (x)
    (tagcase x
      (x-var (s a b abk)
        (let ((t (k-lookup s)))
          (if (k-std-binding? s t) (symbol->string s) "")))
      (x-with (m body a b abk)
        (tagcase body
          (x-var (n c d cdk)
            (if (and (k-fx-module? m) (>= (k-std-type n) 0)) (symbol->string n) ""))
          (else y "")))
      (else y ""))))
;; Whether `f` names a known procedure.
(define k-known-callee? (subr (maxeff kstate spin) (kx) bool)
  (lambda (f)
    (let ((s (k-callee-name f)))
      (and (not (null? s)) (let ((t (k-lookup (car s)))) (and (>= t 0) (k-known? (car s))))))))
;; Whether a call of `f` (instantiated to `ft`) may run for an unbounded
;; time beyond what its latent effect says: a call, in a recursive group's
;; lambdas, of the group; or a call through a recursive type of anything but
;; known code (self-application loops with no store at all). A knot through
;; the store needs nothing here: `k-no-knot` makes its type say `spin`.
(define k-may-spin? (subr (maxeff kstate spin) (kx int kxs) bool)
  (lambda (f ft args)
    (let* ((s (k-callee-name f))
           (t (if (null? s) -1 (k-lookup (car s))))
           (std (k-std-op (k-under f))))
      (cond ;; A continuation called after `cwcc` has returned comes back to
            ;; it again, as often as it is called: only one that can only
            ;; leave needs no `spin`.
            ;; And the receiver must capture no continuation, which could
            ;; hold a call of `k` and be run after `cwcc` returns (F9): a
            ;; `comefrom` in its latent effect, `cwcc`'s `e` as solved.
            ;; `cwcc` is named nowhere else (F15), so every call of it is here.
            ((string=? std "cwcc")
             (or (k-receiver-captures? ft)
                 (not (and (not (null? args)) (null? (cdr args)) (k-escape-only? (car args))))))
            ((and (>= t 0) (k-named-has? (get k-recursive) (car s) t)) #t)
            ((and (>= t 0) (or (k-known? (car s)) (k-std-binding? (car s) t))) #f)
            ((not (string=? std "")) #f)
            ((k-lambda? (k-under f)) #f)
            (else (k-cyclic? ft)))))))))
