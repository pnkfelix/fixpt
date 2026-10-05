;;; The checker, in FX-26: calls that may not end, and what is only called.
;;; Part of the checker, `check-types.fx` first (moved out of
;;; `check-subtype.fx`, 2026-10-04).

;;; ------------------------------------------------------------ calls that may not end

;; A module (`TODO.md` §34: the front end into modules, a file at a time);
;; what other files use re-exported after it.
(define check-calls-module (module
;; Whether a procedure of type `t` could be given itself: a cycle in `t`
;; runs through a parameter of a procedure (or the argument of a
;; continuation). A type that is merely recursive, as a list is, does not let
;; anything loop. `path`: the nodes on the way down, newest first, each with
;; whether it was reached through a parameter.
(define-type k-cpath (listof (pairof int bool @t) acyclic))
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
                   (ty-pair (a b r) (or (k-cyclic-from? a #f p) (k-cyclic-from? b #f p)))
                   (ty-bloblet (fs z r) (k-cyclic-list? fs #f p))
                   (ty-product (ps) (k-cyclic-parts? ps p))
                   (ty-sum (ps) (k-cyclic-parts? ps p))
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
           (t (if (null? s) -1 (k-lookup (car s)))))
      (cond ;; A continuation called after `cwcc` has returned comes back to
            ;; it again, as often as it is called: only one that can only
            ;; leave needs no `spin`.
            ;; And the receiver must capture no continuation, which could
            ;; hold a call of `k` and be run after `cwcc` returns (F9): a
            ;; `comefrom` in its latent effect, `cwcc`'s `e` as solved.
            ((and (>= t 0) (string=? (symbol->string (car s)) "cwcc")
                  (k-named-has? (get k-std) (car s) t))
             (or (k-receiver-captures? ft)
                 (not (and (not (null? args)) (null? (cdr args)) (k-escape-only? (car args))))))
            ((and (>= t 0) (k-named-has? (get k-recursive) (car s) t)) #t)
            ((and (>= t 0) (or (k-known? (car s)) (k-named-has? (get k-std) (car s) t))) #f)
            ((k-lambda? (k-under f)) #f)
            (else (k-cyclic? ft))))))))

(define k-under (with check-calls-module k-under))
(define k-has-comefrom? (with check-calls-module k-has-comefrom?))
(define k-callee-name (with check-calls-module k-callee-name))
(define k-may-spin? (with check-calls-module k-may-spin?))
