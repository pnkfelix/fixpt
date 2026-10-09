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
       (check-expect-types (load-module "fx26:check-expect-types.fx")))
  ;; What it is given: the modules of the files before it that it uses.
  (lambda ((check-types (select check-types-types check-types-sig))
           (check-resolve (select check-resolve-types check-resolve-sig))
           (check-holds (select check-holds-types check-holds-sig))
           (check-env (select check-env-types check-env-sig))
           (check-expect (select check-expect-types check-expect-sig)))
    (module
(define-type k-cpath (select check-calls-types k-cpath))
;; The types it uses of the files before it.
(define a-comefrom (with check-types-types a-comefrom))
(define-type k-eff (select check-types-types k-eff))
(define-type k-ids (select check-types-types k-ids))
(define-type k-parts (select check-types-types k-parts))
(define-effect kreads (select check-types-types kreads))
(define-effect kstate (select check-types-types kstate))
(define-type kx (select check-types-types kx))
(define-type kxs (select check-types-types kxs))
(define ty-app (with check-types-types ty-app))
(define ty-array (with check-types-types ty-array))
(define ty-bloblet (with check-types-types ty-bloblet))
(define ty-comp (with check-types-types ty-comp))
(define ty-icell (with check-types-types ty-icell))
(define ty-markkey (with check-types-types ty-markkey))
(define ty-named (with check-types-types ty-named))
(define ty-nlist (with check-types-types ty-nlist))
(define ty-pair (with check-types-types ty-pair))
(define ty-poly (with check-types-types ty-poly))
(define ty-product (with check-types-types ty-product))
(define ty-ref (with check-types-types ty-ref))
(define ty-subr (with check-types-types ty-subr))
(define ty-sum (with check-types-types ty-sum))
(define ty-tag (with check-types-types ty-tag))
(define ty-union (with check-types-types ty-union))
(define x-app (with check-types-types x-app))
(define x-begin (with check-types-types x-begin))
(define x-bloblet (with check-types-types x-bloblet))
(define x-const (with check-types-types x-const))
(define x-convention (with check-types-types x-convention))
(define x-extract (with check-types-types x-extract))
(define x-if (with check-types-types x-if))
(define x-lambda (with check-types-types x-lambda))
(define x-let (with check-types-types x-let))
(define x-letrec (with check-types-types x-letrec))
(define x-letregion (with check-types-types x-letregion))
(define x-module (with check-types-types x-module))
(define x-plambda (with check-types-types x-plambda))
(define x-product (with check-types-types x-product))
(define x-proj (with check-types-types x-proj))
(define x-prompt (with check-types-types x-prompt))
(define x-rlambda (with check-types-types x-rlambda))
(define x-sum (with check-types-types x-sum))
(define x-tagcase (with check-types-types x-tagcase))
(define x-the (with check-types-types x-the))
(define x-var (with check-types-types x-var))
(define x-with (with check-types-types x-with))
(define-type k-arms (select check-resolve-types k-arms))
(define-type k-let-bs (select check-resolve-types k-let-bs))
(define-effect kmakes (select check-subst-types kmakes))
;; What it uses of the modules it is given.
(define k-dvar-name (with check-types k-dvar-name))
(define k-gen-of (with check-types k-gen-of))
(define k-get (with check-types k-get))
(define k-has-name? (with check-types k-has-name?))
(define k-length (with check-types k-length))
(define k-named-has? (with check-types k-named-has?))
(define k-recursive (with check-types k-recursive))
(define k-resolve (with check-types k-resolve))
(define k-std-binding? (with check-types k-std-binding?))
(define k-std-type (with check-types k-std-type))
(define k-as-subr (with check-resolve k-as-subr))
(define k-free-vars (with check-resolve k-free-vars))
(define k-let-names (with check-resolve k-let-names))
(define k-ds-types (with check-holds k-ds-types))
(define k-fx-module? (with check-env k-fx-module?))
(define k-known? (with check-env k-known?))
(define k-lookup (with check-env k-lookup))
(define k-lambda? (with check-expect k-lambda?))

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
                   (ty-array (a r) (k-cyclic-from? a #f p))
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
;; `f` under any projections and ascriptions.
(define k-under (subr (read @globals) (kx) kx)
  (lambda (f)
    (tagcase f
      (x-proj (body ds a b) (k-under body))
      (x-the (t body a b) (k-under body))
      (else y f))))
;; Whether `k` is named in `x` only as the operator of calls, evaluated as
;; `x` is: not under a `lambda` (which could be called later) or a prompt
;; (whose captures could be composed later).
(define-rec
  (k-only-called? (subr kmakes (kx symbol) bool)
    (lambda (x k)
      (tagcase x
        (x-var (s a b) (not (symbol=? s k)))
        (x-const (t v a b) #t)
        (x-app (f args a b)
          (and (or (tagcase f (x-var (s fa fb) (symbol=? s k)) (else y #f)) (k-only-called? f k))
               (k-only-called-list? args k)))
        (x-lambda (ps body a b) (not (k-has-name? (k-free-vars x) k)))
        (x-plambda (bs body a b) (not (k-has-name? (k-free-vars x) k)))
        (x-rlambda (r l a b) (not (k-has-name? (k-free-vars x) k)))
        (x-letrec (bs body a b) (not (k-has-name? (k-free-vars x) k)))
        (x-prompt (t body h a b) (not (k-has-name? (k-free-vars x) k)))
        (x-let (bs body a b)
          (and (k-only-called-lets? bs k)
               (or (k-has-name? (k-let-names bs nil) k) (k-only-called? body k))))
        (x-letregion (m r i body a b) (or (symbol=? (k-dvar-name r) k) (k-only-called? body k)))
        (x-tagcase (s arms els a b)
          (and (k-only-called? s k)
               (k-only-called-arms? arms k)
               (k-only-called-else? els k)))
        (x-proj (body ds a b) (k-only-called? body k))
        (x-the (t body a b) (k-only-called? body k))
        (x-convention (c body a b) (k-only-called? body k))
        (x-extract (body l a b) (k-only-called? body k))
        (x-sum (l body a b) (k-only-called? body k))
        (x-if (p c d a b) (and (k-only-called? p k) (k-only-called? c k) (k-only-called? d k)))
        (x-begin (xs a b) (k-only-called-list? xs k))
        (x-bloblet (o i xs a b) (k-only-called-list? xs k))
        (x-product (fs a b) (k-only-called-lets? fs k))
        (x-module (items a b) (not (k-has-name? (k-free-vars x) k)))
        (x-with (m body a b) (not (k-has-name? (k-free-vars x) k))))))
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
      (x-the (t body a b) (k-escape-only? body))
      (x-lambda (ps body a b)
        (and (not (null? ps)) (null? (cdr ps)) (k-only-called? body (extract (car ps) 1))))
      (else y #f))))
;; The name `f` is, under any projections and ascriptions, if a variable.
(define k-callee-name (subr (maxeff (read @globals) (alloc @t)) (kx) (listof symbol acyclic))
  (lambda (f)
    (tagcase f
      (x-proj (body ds a b) (k-callee-name body))
      (x-the (t body a b) (k-callee-name body))
      (x-var (n a b) (the (listof symbol acyclic) (cons n nil)))
      (else y (the (listof symbol acyclic) nil)))))
;; The standard name `x` refers to, "" if none: a variable that is the
;; standard binding where it is used, or `(with #%fx n)` (`TODO.md` §46).
;; Every rule for a standard operation asks this.
(define k-std-op (subr (maxeff kreads spin) (kx) string)
  (lambda (x)
    (tagcase x
      (x-var (s a b)
        (let ((t (k-lookup s)))
          (if (k-std-binding? s t) (symbol->string s) "")))
      (x-with (m body a b)
        (tagcase body
          (x-var (n c d)
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
