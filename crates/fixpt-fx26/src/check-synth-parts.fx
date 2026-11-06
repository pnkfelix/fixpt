;;; The checker, in FX-26: parts of the rules (`check-synth.fx`): what it
;;; notes for the compilers (definitions, calls, `extract`s), the joins of
;;; branches' types, a `lambda`'s body against its specification, regions
;;; bound, and what tests certify and narrow on a path. Apart from
;;; `check-synth.fx` since 2026-10-31 (`TODO.md` §188), which makes it of the
;;; modules it is given and gives on all it defines.
;;; A file of one expression (`load-input`, `TODO.md` §68).


;; Its types, those it uses of the files before it, and the signatures of
;; what it is given.
(let* ((check-synth-types (load-module "fx26:check-synth-types.fx"))
       (check-types-types (load-module "fx26:check-types-types.fx"))
       (check-resolve-types (load-module "fx26:check-resolve-types.fx"))
       (check-infer-types (load-module "fx26:check-infer-types.fx"))
       (check-binders-types (load-module "fx26:check-binders-types.fx"))
       (check-subtype-types (load-module "fx26:check-subtype-types.fx"))
       (check-sub-env-types (load-module "fx26:check-sub-env-types.fx"))
       (parser-types ((proj (load-module "fx26:parser-types.fx") @s @e @m @c @p)))
       (eager-reader-types ((proj (load-module "fx26:eager-reader-types.fx") @s @e @m @c)))
       (check-test-facts-types (load-module "fx26:check-test-facts-types.fx"))
       (check-env-types (load-module "fx26:check-env-types.fx"))
       (check-facts-types (load-module "fx26:check-facts-types.fx"))
       (check-print-types (load-module "fx26:check-print-types.fx"))
       (check-print-parts-types (load-module "fx26:check-print-parts-types.fx"))
       (check-bounds-types (load-module "fx26:check-bounds-types.fx"))
       (check-expect-types (load-module "fx26:check-expect-types.fx"))
       (check-errors-types (load-module "fx26:check-errors-types.fx"))
       (check-effects-types (load-module "fx26:check-effects-types.fx"))
       (check-mask-types (load-module "fx26:check-mask-types.fx"))
       (check-unions-types (load-module "fx26:check-unions-types.fx"))
       (check-terminate-types (load-module "fx26:check-terminate-types.fx"))
       (check-holds-types (load-module "fx26:check-holds-types.fx"))
       (check-calls-types (load-module "fx26:check-calls-types.fx"))
       (check-subst-types (load-module "fx26:check-subst-types.fx"))
       (check-read-helpers-types (load-module "fx26:check-read-helpers-types.fx"))
       (check-blobrefs-types (load-module "fx26:check-blobrefs-types.fx")))
  ;; What it is given: the modules of the files before it that it uses.
  (lambda ((check-types (select check-types-types check-types-sig))
           (check-test-facts (select check-test-facts-types check-test-facts-sig))
           (check-resolve (select check-resolve-types check-resolve-sig))
           (check-env (select check-env-types check-env-sig))
           (check-infer (select check-infer-types check-infer-sig))
           (check-facts (select check-facts-types check-facts-sig))
           (check-print (select check-print-types check-print-sig))
           (check-bounds (select check-bounds-types check-bounds-sig))
           (check-expect (select check-expect-types check-expect-sig))
           (check-errors (select check-errors-types check-errors-sig))
           (check-effects (select check-effects-types check-effects-sig))
           (check-mask (select check-mask-types check-mask-sig))
           (check-unions (select check-unions-types check-unions-sig))
           (check-terminate (select check-terminate-types check-terminate-sig))
           (check-holds (select check-holds-types check-holds-sig))
           (check-subtype (select check-subtype-types check-subtype-sig))
           (check-calls (select check-calls-types check-calls-sig))
           (check-subst (select check-subst-types check-subst-sig))
           (check-binders (select check-binders-types check-binders-sig))
           (check-sub-env (select check-sub-env-types check-sub-env-sig))
           (check-print-parts (select check-print-parts-types check-print-parts-sig))
           (check-read-helpers (select check-read-helpers-types check-read-helpers-sig))
           (check-blobrefs (select check-blobrefs-types check-blobrefs-sig)))
    (module
(hide (include check-synth-types) (include check-types-types) (include check-resolve-types)
      (include check-infer-types) (include check-subtype-types) (include parser-types)
      (include eager-reader-types) (include check-env-types))
;; The types it uses of the files before it.
;; What it uses of the modules it is given: all of each, hidden.
(hide (include check-types) (include check-env) (include check-test-facts) (include check-resolve)
      (include check-binders) (include check-infer) (include check-facts)
      (include check-print-parts) (include check-print) (include check-bounds)
      (include check-expect) (include check-errors) (include check-read-helpers)
      (include check-blobrefs)
      (include check-effects) (include check-mask) (include check-unions)
      (include check-terminate) (include check-holds) (include check-sub-env)
      (include check-subtype) (include check-calls) (include check-subst))

;; The error that a `tagcase`, `x`, has no arm for the variants `rest`.
(define k-fail-no-arm (->* (k-parts kx) void)
  (lambda (rest x)
    (let ((names (k-join (k-part-names rest) ", ")))
      (k-fail-at (string-append "this `tagcase` has no arm for " names) x))))
;; Whether `t` is a list at `acyclic`: a pair's type, its region frozen and
;; never written.
(define k-acyclic-list? (->* (int) bool)
  (lambda (t)
    (tagcase (k-get t)
      (ty-pair (a d r nl) (tagcase r (r-frozen (p finite) finite) (else y #f)))
      (else y #f))))
;; Note, for the compilers, that a top-level definition's value `x`, of
;; type `t`, is a list in a frozen region (`acyclic` or `const`): data
;; nothing writes, which they may make once if it is made of literals; the
;; fact `n-frozen-define` (`c-fill-facts`). As the Rust checker's
;; `frozen_defines`.
(define k-note-frozen-define (->* (int kx) unit)
  (lambda (t x)
    (if (tagcase (k-get t)
          (ty-pair (a d r nl) (tagcase r (r-frozen (p finite) #t) (else y #f)))
          (else y #f))
        (set k-extracts (cons (product (1 (k-at-of x)) (2 (n-frozen-define))) (get k-extracts)))
        #u)))
;; Note, for the compilers, call `x` of `f`, of type `ft` (on parameters
;; `params`): its callee's convention, which the call is compiled in, noted
;; at `f` (`n-call`; the Rust checker's `call_convs`); and whether it is `apply` of a
;; list at `acyclic` (below).
(define k-note-call (->* (kx kx int k-ids) unit)
  (lambda (x f ft params)
    (begin (tagcase (k-get (k-resolve ft))
             (ty-subr (e ps r cv spc)
               (set k-extracts (cons (product (1 (k-at-of f)) (2 (n-call cv))) (get k-extracts))))
             (else y #u))
           (k-note-apply-shares x f params))))
;; Note, for the compilers, that the call `x` of `f` (on parameters
;; `params`) is `apply` of a list at `acyclic`, which it need not copy: the
;; fact `n-apply-shares` (`c-fill-facts`). Every other `apply` copies its
;; list, so that
;; the variadic procedure's is one nothing else can write.
(define k-note-apply-shares (->* (kx kx k-ids) unit)
  (lambda (x f params)
    (let ((apply? (string=? (k-std-op f) "apply")))
      (if (and apply? (and (= (k-length params) 2) (k-acyclic-list? (car (cdr params)))))
          (set k-extracts (cons (product (1 (k-at-of x)) (2 (n-apply-shares))) (get k-extracts)))
          #u))))
;; `car` or `cdr` of a union with a pair member (a `datum`, say) takes that
;; member apart, of several the greatest: every machine's `car` checks its
;; argument is a pair, and traps if not, as it does on `nil` (TODO §51).
(define k-partial-pair-arg
  (->* (kx (arrayof int @t) k-ids k-binders k-solved) unit)
  (lambda (f types ps kinds solved)
    (let* ((op (k-std-op f)) (t (if (> (array-length types) 0) (array-ref types 0) -1)))
      (if (and (or (string=? op "car") (string=? op "cdr")) (>= t 0))
          (tagcase (k-get (k-resolve t))
            (ty-union (ms)
              (let* ((pairs (k-union-pairs ms)) (m (k-upper-bound pairs pairs)))
                (if (>= m 0)
                    (begin (k-unify (car ps) m kinds solved (k-new-trail)) (array-set! types 0 m))
                    #u)))
            (else y #u))
          #u))))
;; A union's members that are pairs, of members `ms`.
(define k-union-pairs (->* (k-ids) k-ids)
  (lambda (ms)
    (cond ((null? ms) nil)
          ((tagcase (k-get (k-resolve (car ms))) (ty-pair (x d r nl) #t) (else y #f))
           (the k-ids (cons (car ms) (k-union-pairs (cdr ms)))))
          (else (k-union-pairs (cdr ms))))))
;; Type `t` and effect `e` of `x`, or `r`, both, with what `x` masks masked.
(define k-te-masked (->* (kx int k-eff) k-te)
  (lambda (x t e) (k-te t (k-mask x e t))))
(define k-masked (->* (kx k-te) k-te)
  (lambda (x r) (k-te-masked x (extract r 1) (extract r 2))))
;; `r`'s type onto `rest`'s types, and the effects of both.
(define k-te-onto (->* (k-te k-types-eff) k-types-eff)
  (lambda (r rest)
    (let ((ts (the k-ids (cons (extract r 1) (extract rest 1)))))
      (product (1 ts) (2 (k-union (extract r 2) (extract rest 2)))))))
;; The effect `r` says `x` has, once the type it says is found one `expected` takes.
(define k-as-expected (->* (kx k-te int) k-eff)
  (lambda (x r expected) (begin (k-expect x (extract r 1) expected) (extract r 2))))
;; A `lambda`'s body, `x`, checked: if its specification `sp` says what a
;; test proves, an error (`k-claimed`).
(define k-claims-proved (->* (k-specs kx) unit)
  (lambda (sp x) (let ((m (k-claimed sp))) (if (string=? m "") #u (k-fail-at m x)))))
;; A new `subr` type, of the default convention; and one with a
;; specification, none or one.
(define k-new-subr (->* (k-eff k-ids int) int)
  (lambda (e ps res) (k-ty-new (ty-subr e ps res (get k-conv-default) nil))))
(define k-new-subr-spec (->* (k-eff k-ids int k-specs) int)
  (lambda (e ps res sp) (k-ty-new (ty-subr e ps res (get k-conv-default) sp))))
;; A `(nlist e k R)`, `R` the region `rg` made finite, and effect `eff`.
(define k-nlist-te (->* (int k-size k-region k-eff) k-te)
  (lambda (e k rg eff) (k-te (k-ty-new (ty-nlist e k (k-fin-region rg))) eff)))
;; A fresh trail, for `k-unify`.
(define k-new-trail (->* () k-trail) (lambda () (the k-trail (new nil))))
;; The region `r` names, bound as a variable of type `(place r)`.
(define k-bind-place (->* (int) unit)
  (lambda (r) (k-bind (k-dvar-name r) (k-ty-new (ty-place (r-var r))))))
;; The form a `letregion` of kind `k` is written as.
(define k-region-form (->* (int) string)
  (lambda (k)
    (case k ((0) "letregion") ((1) "letrena") ((2) "letreap") (else "letfreeze"))))
;; Note, for the compiler, what the `extract` `at` takes, `d`; or its field,
;; `i`, by position.
(define k-note-extract (->* (k-at k-datum) unit)
  (lambda (at d) (set k-extracts (cons (product (1 at) (2 (n-datum d))) (get k-extracts)))))
(define k-note-field (->* (k-at int) unit)
  (lambda (at i) (k-note-extract at (datum-field i))))
;; `inner`, under binders `bs`, with `m` for them, each within its bound and finite if need be.
(define k-subst-checked (->* (k-binders k-map int int int) int)
  (lambda (bs m inner a b)
    (begin (k-check-bounds bs m a b) (k-check-distinct bs m inner a b)
           (k-check-finite-sizes bs m inner a b) (k-spin-for-cyclic inner (k-subst inner m) m))))
;; `inner`, under binders `bs`, projected with `ds`: an error where they do not fit, or knot.
(define k-projected (->* (k-binders (listof k-desc acyclic) int int int) int)
  (lambda (bs ds inner a b)
    (let ((inst (k-subst-checked bs (k-proj-map bs ds a b) inner a b)))
      (begin (k-no-knot inst a b) inst))))
;; `t`, or, if a list of any elements (`nil`), the type `nil`.
(define k-nil-if-any (->* (int) int)
  (lambda (t) (if (k-list-of-any? t) (k-ty-new (ty-nil)) t)))
;; `ts`, each `nil` the type `nil`: what other arms are, as in an `if`.
(define k-nils-if-any (->* (k-ids) k-ids)
  (lambda (ts) (if (null? ts) nil (cons (k-nil-if-any (car ts)) (k-nils-if-any (cdr ts))))))
;; Branches' types, each `nil` the type `nil`, and, if one is, each pair one
;; that may be `nil`: their join, if they have one, is then one of them.
(define k-nil-pair (->* (int) int)
  (lambda (t)
    (tagcase (k-get (k-resolve t)) (ty-pair (a d r nl) (k-ty-new (ty-pair a d r #t))) (else y t))))
(define k-nil-pairs (->* (k-ids) k-ids)
  (lambda (ts) (if (null? ts) nil (cons (k-nil-pair (car ts)) (k-nil-pairs (cdr ts))))))
(define k-any-nil? (->* (k-ids) bool)
  (lambda (ts)
    (and (not (null? ts))
         (or (tagcase (k-get (k-resolve (car ts))) (ty-nil () #t) (else y #f))
             (k-any-nil? (cdr ts))))))
(define k-join-with-nil (->* (k-ids) k-ids)
  (lambda (ts0)
    (let ((ts (k-nils-if-any ts0))) (if (k-any-nil? ts) (k-nil-pairs ts) ts))))
;; The least type above two branches' `t` and `u`, or -1: the wider, if one
;; is within the other; a `nat`, of two naturals of sizes not shown equal;
;; of two sums, the sum of each's variants, a tag both have carrying its
;; payloads' join: `t`'s variants in order, then `u`'s that `t` has not (as
;; `check.rs`'s `branch_join`). `depth` bounds the descent through
;; recursive sums.
(define-rec
  (k-branch-join (->* (int int int) int)
    (lambda (t u depth)
      (cond ((k-subtype t u) u)
            ((k-subtype u t) t)
            ((and (k-nat-ty? t) (k-nat-ty? u)) (k-ty-new (ty-nat (sz-finite))))
            ((> depth 32) -1)
            (else
             (tagcase (k-get (k-resolve t))
               (ty-sum (ps)
                 (tagcase (k-get (k-resolve u))
                   (ty-sum (qs)
                     (let ((joined (k-join-parts ps qs depth)))
                       (if (k-parts-known? joined) (k-ty-new (ty-sum joined)) -1)))
                   (else y -1)))
               (else y -1))))))
  ;; `ps` with each of `qs` added: a tag `ps` has, its payload joined (-1 if
  ;; none), else at the end.
  (k-join-parts (->* (k-parts k-parts int) k-parts)
    (lambda (ps qs depth)
      (if (null? qs)
          ps
          (k-join-parts (k-join-part ps (extract (car qs) 1) (extract (car qs) 2) depth)
                        (cdr qs) depth))))
  (k-join-part (->* (k-parts symbol int int) k-parts)
    (lambda (ps l t depth)
      (cond ((null? ps) (the k-parts (cons (product (1 l) (2 t)) nil)))
            ((symbol=? (extract (car ps) 1) l)
             (let ((j (k-branch-join (extract (car ps) 2) t (+ depth 1))))
               (the k-parts (cons (product (1 l) (2 j)) (cdr ps)))))
            (else (the k-parts (cons (car ps) (k-join-part (cdr ps) l t depth))))))))
;; Whether every part's type is known (≥ 0).
(define k-parts-known? (->* (k-parts) bool)
  (lambda (ps) (or (null? ps) (and (>= (extract (car ps) 2) 0) (k-parts-known? (cdr ps))))))
;; Of `ts`, their join, one pair at a time from the first; -1 if none.
(define k-fold-join (->* (int k-ids) int)
  (lambda (t ts)
    (cond ((< t 0) -1)
          ((null? ts) t)
          (else (k-fold-join (k-branch-join t (car ts) 0) (cdr ts))))))
;; An `if`'s type, its branches a `tc` and a `td`: their join; an error if they have none.
(define k-join-known (->* (int int int int) int)
  (lambda (tc td a b)
    (let ((t (k-branch-join tc td 0)))
      (if (< t 0)
          (k-fail (k-cat4 "the branches are a " (k-show-ty tc) " and a " (k-show-ty td)) a b)
          t))))
;; The same, `nil`, beside another branch, what that is if `nil` is one
;; (`TODO.md` §48); beside `nil`, the type `nil`; beside a pair, the pair
;; that may be `nil`.
(define k-join-branches (->* (int int int int) int)
  (lambda (tc td a b)
    (let ((ts (k-join-with-nil (list tc td)))) (k-join-known (car ts) (car (cdr ts)) a b))))
;; If `p` certifies a variable acyclic (`acyclic?`, `(acyclic i)`), it, as
;; the binding it is (none or one).
(define k-acyclic-test (->* (kx) k-named)
  (lambda (p) (k-latent-cert p 0)))
;; If `p` certifies a variable a natural (`nat?`, `(nat i)`), it.
(define k-nat-test (->* (kx) k-named)
  (lambda (p) (k-latent-cert p 1)))
(define k-certs-now (->* () k-certs)
  (lambda ()
    (product (1 (get k-certified)) (2 (get k-certified-lengths)) (3 (get k-certified-nats)))))
;; Note what test `p` certifies, if anything: a variable acyclic, of a length, or natural.
(define k-push-certified (->* (kx) unit)
  (lambda (p)
    (let ((cert (k-acyclic-test p)) (lens (k-length-test p)) (nats (k-nat-test p)))
      (begin
        (if (null? cert) #u (set k-certified (cons (car cert) (get k-certified))))
        (if (null? lens) #u (set k-certified-lengths (cons (car lens) (get k-certified-lengths))))
        (if (null? nats) #u (set k-certified-nats (cons (car nats) (get k-certified-nats))))))))
(define k-nars-append (->* (k-nars k-nars) k-nars)
  (lambda (xs ys)
    (if (null? xs) ys (the k-nars (cons (car xs) (k-nars-append (cdr xs) ys))))))
(define k-step=? (->* (k-step k-step) bool)
  (lambda (s u)
    (tagcase s
      (st-car () (tagcase u (st-car () #t) (else y #f)))
      (st-cdr () (tagcase u (st-cdr () #t) (else y #f)))
      (st-field (l) (tagcase u (st-field (m) (symbol=? l m)) (else y #f))))))
(define k-steps=? (->* (k-steps k-steps) bool)
  (lambda (xs ys)
    (if (null? xs)
        (null? ys)
        (and (not (null? ys)) (k-step=? (car xs) (car ys)) (k-steps=? (cdr xs) (cdr ys))))))
(define k-steps-snoc (->* (k-steps k-step) k-steps)
  (lambda (xs s)
    (if (null? xs)
        (the k-steps (cons s nil))
        (the k-steps (cons (car xs) (k-steps-snoc (cdr xs) s))))))
(define k-path-step (->* (k-paths k-step) k-paths)
  (lambda (ps s)
    (if (null? ps)
        (the k-paths nil)
        (let* ((p (car ps)) (steps (k-steps-snoc (extract p 3) s)))
          (the k-paths (cons (product (1 (extract p 1)) (2 (extract p 2)) (3 steps)) nil))))))
(define k-path-of (->* (kx) k-paths)
  (lambda (x)
    (tagcase x
      (x-var (v a b abk abkr)
             (the k-paths (cons (product (1 v) (2 (k-binding-depth v)) (3 nil)) nil)))
      (x-app (f args a b abk abkr)
        (let ((op (k-std-op f)))
          (if (and (k-sc-one-arg? args) (or (string=? op "car") (string=? op "cdr")))
              (k-path-step (k-path-of (car args)) (if (string=? op "car") (st-car) (st-cdr)))
              (the k-paths nil))))
      (x-extract (e l a b abk abkr) (k-path-step (k-path-of e) (st-field l)))
      (else y (the k-paths nil)))))
;; The type the fact in force of the path from `v` at `d` by `steps` gives,
;; or -1.
(define k-path-fact-in (->* (k-path-facts symbol int k-steps int) int)
  (lambda (fs v d steps depth)
    (cond ((null? fs) -1)
          ((let ((f (car fs)))
             (and (not (extract f 7)) (= (extract f 6) depth) (symbol=? (extract f 1) v)
                  (= (extract f 2) d) (k-steps=? (extract f 3) steps)))
           (extract (car fs) 5))
          (else (k-path-fact-in (cdr fs) v d steps depth)))))
(define k-path-fact-ty (->* (symbol int k-steps) int)
  (lambda (v d steps) (k-path-fact-in (get k-path-narrowed) v d steps (get k-closure-depth))))
(define k-reached-of (->* (int k-regions) k-reached)
  (lambda (t rs) (the k-reached (cons (product (1 t) (2 rs)) nil))))
;; The path from `v` at `d`, `done` taken and `rest` to go, at type `t`
;; having read through `rs`: as the types say and the facts in force
;; narrow it (`check.rs`'s `path_type`).
(define k-path-walk
  (->* (symbol int k-steps k-steps int k-regions) k-reached)
  (lambda (v d done rest t rs)
    (if (null? rest)
        (k-reached-of t rs)
        (let* ((s (car rest))
               (next (tagcase s
                       (st-car ()
                         (tagcase (k-get t)
                           (ty-pair (a b r nl) (k-reached-of a (cons r rs)))
                           (else y (the k-reached nil))))
                       (st-cdr ()
                         (tagcase (k-get t)
                           (ty-pair (a b r nl) (k-reached-of b (cons r rs)))
                           (else y (the k-reached nil))))
                       (st-field (l)
                         (tagcase (k-get t)
                           (ty-product (ps)
                             (let ((f (k-part-find ps l)))
                               (if (< f 0) (the k-reached nil) (k-reached-of f rs))))
                           (else y (the k-reached nil)))))))
          (if (null? next)
              (the k-reached nil)
              (let* ((now (k-steps-snoc done s))
                     (fact (k-path-fact-ty v d now))
                     (t2 (k-resolve (if (>= fact 0) fact (extract (car next) 1)))))
                (k-path-walk v d now (cdr rest) t2 (extract (car next) 2))))))))
(define k-path-type (->* (symbol int k-steps) k-reached)
  (lambda (v d steps)
    (let ((t (k-lookup v)))
      (if (< t 0) (the k-reached nil) (k-path-walk v d nil steps (k-resolve t) nil)))))
;; `x`'s type `t`, or, `x` a path a fact in force narrows, its type there.
(define k-path-ty (->* (kx int) int)
  (lambda (x t)
    (if (null? (get k-path-narrowed))
        t
        (let ((ps (k-path-of x)))
          (if (or (null? ps) (null? (extract (car ps) 3)))
              t
              (let* ((p (car ps)) (f (k-path-fact-ty (extract p 1) (extract p 2) (extract p 3))))
                (if (< f 0) t f)))))))
(define k-path-te (->* (kx k-te) k-te)
  (lambda (x te)
    (let ((p (k-pinned-of (k-at-of x))))
      (k-te (if (>= p 0) p (k-path-ty x (extract te 1))) (extract te 2)))))
;; What `out` narrows the path from `v` at `d` by `steps` to (none or one).
(define k-nars-of (->* (k-nars symbol int k-steps) k-reached)
  (lambda (out v d steps)
    (cond ((null? out) (the k-reached nil))
          ((let ((n (car out)))
             (and (symbol=? (extract n 1) v) (= (extract n 2) d) (k-steps=? (extract n 3) steps)))
           (k-reached-of (extract (car out) 5) (extract (car out) 4)))
          (else (k-nars-of (cdr out) v d steps)))))
;; `out` with that path narrowed to `t`, in place of what it had.
(define k-nars-put
  (->* (k-nars symbol int k-steps k-regions int) k-nars)
  (lambda (out v d steps rs t)
    (let ((one (product (1 v) (2 d) (3 steps) (4 rs) (5 t))))
      (cond ((null? out) (the k-nars (cons one nil)))
            ((let ((n (car out)))
               (and (symbol=? (extract n 1) v) (= (extract n 2) d) (k-steps=? (extract n 3) steps)))
             (the k-nars (cons one (cdr out))))
            (else (the k-nars (cons (car out) (k-nars-put (cdr out) v d steps rs t))))))))
;; What a shape test narrows a `t` to, `to` (-1, nothing): checked against a
;; member of an `allof`, where `t` cannot pass it (or fail it, `negated`),
;; `void`, and its branch is skipped (`k-dead-branch?`). As `props_narrow`.
(define k-narrowed-or-void (->* (int int bool int) int)
  (lambda (t k negated to)
    (if (or (>= to 0) (null? (get k-dead-arms)))
        to
        (let ((s (k-run-shape t)) (bit (k-shape-bit k)))
          (cond ((<= s 0) to)
                ((and (not negated) (= (bitwise-and s bit) 0)) k-void)
                ((and negated (= (bitwise-and s bit) s)) k-void)
                (else to))))))
;; The variables and paths among `args` narrowed by `props`, a conjunction:
;; each proposition of a shape, in turn.
(define k-props-narrow (->* (k-props kxs k-nars) k-nars)
  (lambda (props args out)
    (if (null? props)
        out
        (let* ((p (car props))
               (i (tagcase p (pr-shape (i k f) i) (else y -1)))
               (x (if (< i 0) (the kxs nil) (k-arg-at args i)))
               (path (if (null? x) (the k-paths nil) (k-path-of (car x)))))
          (if (null? path)
              (k-props-narrow (cdr props) args out)
              (let* ((pt (car path)) (n (extract pt 1)) (d (extract pt 2)) (steps (extract pt 3))
                     (had (k-nars-of out n d steps))
                     (tr (if (null? had) (k-path-type n d steps) had)))
                (if (null? tr)
                    (k-props-narrow (cdr props) args out)
                    (let* ((shape (tagcase p (pr-shape (i k f) k) (else y 0)))
                           (negated (tagcase p (pr-shape (i k f) f) (else y #f)))
                           (split (k-narrowed-by (k-resolve (extract (car tr) 1)) shape))
                           (to (k-narrowed-or-void
                                (k-resolve (extract (car tr) 1)) shape negated
                                (if negated (extract split 2) (extract split 1)))))
                      (k-props-narrow
                       (cdr props) args
                       (if (< to 0) out (k-nars-put out n d steps (extract (car tr) 2) to)))))))))))
;; A test: what its callee's type says it proves (its `ensures`), of those of
;; its arguments that are variables or paths, where it holds and where not.
(define k-latent-narrowing (->* (kx) k-narrowing)
  (lambda (p)
    (let ((l (k-latent-props p)))
      (if (null? l)
          (the k-narrowing (cons nil nil))
          (let ((x (car l)))
            (cons (k-props-narrow (extract x 1) (extract x 3) nil)
                  (k-props-narrow (extract x 2) (extract x 3) nil)))))))
(define k-narrowings (->* (kx) k-narrowing)
  (lambda (p)
    (let ((none (the k-narrowing (cons nil nil))))
      (tagcase p
        (x-if (q c d a b abk abkr)
          (let ((nq (k-narrowings q)))
            (cond ((k-bool-lit? c #t) (cons nil (k-nars-append (cdr nq) (cdr (k-narrowings d)))))
                  ((k-bool-lit? d #f) (cons (k-nars-append (car nq) (car (k-narrowings c))) nil))
                  (else none))))
        (x-app (f args a b abk abkr)
          (if (and (string=? (k-std-op f) "not") (k-sc-one-arg? args))
              (let ((ns (k-narrowings (car args)))) (cons (cdr ns) (car ns)))
              (k-latent-narrowing p)))
        (else y none)))))
;; The variables' narrowings among `ns`, as `k-narrowed` keeps them.
(define k-var-narrows (->* (k-nars) k-narrows)
  (lambda (ns)
    (cond ((null? ns) nil)
          ((null? (extract (car ns) 3))
           (let ((n (car ns)))
             (the k-narrows
                  (cons (product (1 (extract n 1)) (2 (extract n 2)) (3 (extract n 5)))
                        (k-var-narrows (cdr ns))))))
          (else (k-var-narrows (cdr ns))))))
;; The paths' narrowings among `ns` put in force, in turn.
(define k-push-paths (->* (k-nars) unit)
  (lambda (ns)
    (if (null? ns)
        #u
        (let ((n (car ns)))
          (begin
            (if (null? (extract n 3))
                #u
                (set k-path-narrowed
                     (cons (product (1 (extract n 1)) (2 (extract n 2)) (3 (extract n 3))
                                    (4 (extract n 4)) (5 (extract n 5))
                                    (6 (get k-closure-depth)) (7 #f))
                           (get k-path-narrowed))))
            (k-push-paths (cdr ns)))))))
;; Narrowings `ns` put in force, the variables' onto `saved`.
(define k-put-narrowing (->* (k-nars k-narrows) unit)
  (lambda (ns saved)
    (begin (set k-narrowed (k-narrows-append (k-var-narrows ns) saved)) (k-push-paths ns))))
(define k-drop-facts (->* (k-path-facts int) k-path-facts)
  (lambda (fs m) (if (or (<= m 0) (null? fs)) fs (k-drop-facts (cdr fs) (- m 1)))))
;; The paths' facts cut back to the `n` oldest, as they are now (one an
;; effect has ended since stays ended).
(define k-cut-paths (->* (int) unit)
  (lambda (n)
    (let ((fs (get k-path-narrowed)))
      (set k-path-narrowed (k-drop-facts fs (- (k-length fs) n))))))
(define k-narrows-append (->* (k-narrows k-narrows) k-narrows)
  (lambda (xs ys)
    (if (null? xs) ys (the k-narrows (cons (car xs) (k-narrows-append (cdr xs) ys))))))
;; What effect `e`, of an expression just checked, ends of the paths' facts
;; at this closure depth (`check.rs`'s `kill_paths`): a write to a region
;; a path reads through, or to one that may be it (a region variable may be
;; any region), and any transfer of control or effect not known. A path
;; through frozen data, or products' fields alone, is never written.
(define k-may-alias? (->* (k-region k-region) bool)
  (lambda (w r)
    (and (not (k-regions-distinct? w r))
         (or (k-region=? w r)
             (tagcase w (r-var (v) #t) (else y #f))
             (tagcase r (r-var (v) #t) (else y #f))))))
(define k-hits? (->* (k-region k-regions) bool)
  (lambda (w rs)
    (and (not (null? rs)) (or (k-may-alias? w (car rs)) (k-hits? w (cdr rs))))))
(define k-open-regions (->* (k-regions) k-regions)
  (lambda (rs)
    (cond ((null? rs) nil)
          ((tagcase (car rs) (r-frozen (p f) #t) (else y #f)) (k-open-regions (cdr rs)))
          (else (the k-regions (cons (car rs) (k-open-regions (cdr rs))))))))
(define k-kills? (->* (k-eff k-regions) bool)
  (lambda (e open)
    (and (not (null? e))
         (or (tagcase (car e)
               (a-write (w) (k-hits? w open))
               (a-init (w) (k-hits? w open))
               ;; A process waits at each.
               (a-send (r) #t) (a-receive (r) #t)
               (a-goto (r) #t) (a-comefrom (r) #t) (a-await (r) #t) (a-var (v) #t)
               (a-app (v ds) #t)
               (else y #f))
             (k-kills? (cdr e) open)))))
(define k-kill-each
  (->* (k-path-facts k-eff int) k-path-facts)
  (lambda (fs e depth)
    (if (null? fs)
        nil
        (let* ((f (car fs))
               (open (k-open-regions (extract f 4)))
               (ends (and (not (extract f 7)) (= (extract f 6) depth) (not (null? open))
                          (k-kills? e open)))
               (g (if ends
                      (product (1 (extract f 1)) (2 (extract f 2)) (3 (extract f 3))
                               (4 (extract f 4)) (5 (extract f 5)) (6 (extract f 6)) (7 #t))
                      f)))
          (the k-path-facts (cons g (k-kill-each (cdr fs) e depth)))))))
(define k-all-dead? (->* (k-path-facts) bool)
  (lambda (fs) (or (null? fs) (and (extract (car fs) 7) (k-all-dead? (cdr fs))))))
(define k-kill-paths (->* (k-eff) unit)
  (lambda (e)
    (let ((fs (get k-path-narrowed)))
      (if (k-all-dead? fs) #u (set k-path-narrowed (k-kill-each fs e (get k-closure-depth)))))))
;; Before the branch where `p` holds: what it certifies, and the facts it shows, in force.
(define k-enter-then (->* (kx) k-tested)
  (lambda (p)
    (let* ((certs (k-certs-now))
           (pushed (k-push-certified p))
           (facts (k-test-facts p))
           (narrowing (k-narrowings p))
           (fsaved (get k-size-facts))
           (nsaved (get k-narrowed))
           (psaved (k-length (get k-path-narrowed)))
           (fyes (set k-size-facts (k-with-facts (car facts) fsaved)))
           (nyes (k-put-narrowing (car narrowing) nsaved)))
      (product (1 certs) (2 fsaved) (3 facts) (4 nsaved) (5 narrowing) (6 psaved)))))
;; After it, before the branch where `p` does not: nothing certified, and what `p` shows so.
(define k-enter-else (->* (k-tested) unit)
  (lambda (tested)
    (let ((certs (extract tested 1)) (fsaved (extract tested 2)))
      (begin
        (set k-certified (extract certs 1))
        (set k-certified-lengths (extract certs 2))
        (set k-certified-nats (extract certs 3))
        (set k-size-facts (k-with-facts (cdr (extract tested 3)) fsaved))
        (k-cut-paths (extract tested 6))
        (k-put-narrowing (cdr (extract tested 5)) (extract tested 4))))))
;; After both: the facts, and what was narrowed, as they were.
(define k-leave-test (->* (k-tested) unit)
  (lambda (t)
    (begin (set k-size-facts (extract t 2)) (set k-narrowed (extract t 4))
           (k-cut-paths (extract t 6)))))
;; Whether `args` are one variable, as the binding it is, among `cs`.
(define k-certified-arg? (->* (k-named kxs) bool)
  (lambda (cs args)
    (and (k-sc-one-arg? args)
         (tagcase (car args)
           (x-var (v va vb vavbk vavbkr) (k-certified-has? cs v (k-binding-depth v)))
           (else y #f))))))))
