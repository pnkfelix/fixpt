;;; The checker, in FX-26: the rules, each expression's type and effect.
;;; Part of the checker, `check-types.fx` first (PLAN.md §11, step 10).

;; A module (`TODO.md` §34: the front end into modules, a file at a time);
;; what other files use re-exported after it.
(define check-synth-module (module
;; The error that a `tagcase`, `x`, has no arm for the variants `rest`.
(define k-fail-no-arm (subr (maxeff checks spin) (k-parts kx) void)
  (lambda (rest x)
    (let ((names (k-join (k-part-names rest) ", ")))
      (k-fail-at (string-append "this `tagcase` has no arm for " names) x))))
;; Whether `t` is a list at `acyclic`: a pair's type, its region frozen and
;; never written.
(define k-acyclic-list? (subr (maxeff kreads spin) (int) bool)
  (lambda (t)
    (tagcase (k-get t)
      (ty-pair (a d r) (tagcase r (r-frozen (p finite) finite) (else y #f)))
      (else y #f))))
;; Note, for the compilers, that a top-level definition's value `x`, of
;; type `t`, is a list in a frozen region (`acyclic` or `const`): data
;; nothing writes, which they may make once if it is made of literals; the
;; fact -501 (`c-fill-facts`). As the Rust checker's `frozen_defines`.
(define k-note-frozen-define (subr (maxeff checks spin) (int kx) unit)
  (lambda (t x)
    (if (tagcase (k-get t)
          (ty-pair (a d r) (tagcase r (r-frozen (p finite) #t) (else y #f)))
          (else y #f))
        (set k-extracts (cons (product (1 (k-start x)) (2 (k-end x)) (3 -501)) (get k-extracts)))
        #u)))
;; Note, for the compilers, that the call `x` of `f` (on parameters
;; `params`) is `apply` of a list at `acyclic`, which it need not copy: the
;; fact -500 (`c-fill-facts`). Every other `apply` copies its list, so that
;; the variadic procedure's is one nothing else can write.
(define k-note-apply-shares (subr (maxeff checks spin) (kx kx k-ids) unit)
  (lambda (x f params)
    (let ((apply? (string=? (k-std-op f) "apply")))
      (if (and apply? (and (= (k-length params) 2) (k-acyclic-list? (car (cdr params)))))
          (set k-extracts (cons (product (1 (k-start x)) (2 (k-end x)) (3 -500)) (get k-extracts)))
          #u))))
;; Types, and the effect of all.
(define-type k-types-eff (productof (1 k-ids) (2 k-eff)))
;; What a call's arguments were found to be before they are checked: types (or -1), effects.
(define-type k-done (productof (1 (arrayof int @t)) (2 (arrayof k-eff @t))))
;; Type `t` and effect `e` of `x`, or `r`, both, with what `x` masks masked.
(define k-te-masked (subr (maxeff kstate spin) (kx int k-eff) k-te)
  (lambda (x t e) (k-te t (k-mask x e t))))
(define k-masked (subr (maxeff kstate spin) (kx k-te) k-te)
  (lambda (x r) (k-te-masked x (extract r 1) (extract r 2))))
;; `r`'s type onto `rest`'s types, and the effects of both.
(define k-te-onto (subr (maxeff kreads (alloc @t) spin) (k-te k-types-eff) k-types-eff)
  (lambda (r rest)
    (let ((ts (the k-ids (cons (extract r 1) (extract rest 1)))))
      (product (1 ts) (2 (k-union (extract r 2) (extract rest 2)))))))
;; The effect `r` says `x` has, once the type it says is found one `expected` takes.
(define k-as-expected (subr (maxeff checks spin) (kx k-te int) k-eff)
  (lambda (x r expected) (begin (k-expect x (extract r 1) expected) (extract r 2))))
;; A new `subr` type, of the default convention.
(define k-new-subr (subr (maxeff kstate spin) (k-eff k-ids int) int)
  (lambda (e ps res) (k-ty-new (ty-subr e ps res (get k-conv-default)))))
;; A `(nlist e k R)`, `R` the region `rg` made finite, and effect `eff`.
(define k-nlist-te (subr (maxeff kstate spin) (int k-size k-region k-eff) k-te)
  (lambda (e k rg eff) (k-te (k-ty-new (ty-nlist e k (k-fin-region rg))) eff)))
;; A fresh trail, for `k-unify`.
(define k-new-trail (subr (alloc @t) () k-trail) (lambda () (the k-trail (new nil))))
;; The region `r` names, bound as a variable of type `(place r)`.
(define k-bind-place (subr (maxeff kstate spin) (int) unit)
  (lambda (r) (k-bind (k-dvar-name r) (k-ty-new (ty-place (r-var r))))))
;; The form a `letregion` of kind `k` is written as.
(define k-region-form (subr pure (int) string)
  (lambda (k)
    (cond ((= k 0) "letregion") ((= k 1) "letrena") ((= k 2) "letreap") (else "letfreeze"))))
;; Note, for the compiler, that the `extract` at `a`..`b` takes part `i`.
(define k-note-extract (subr kstate (int int int) unit)
  (lambda (a b i) (set k-extracts (cons (product (1 a) (2 b) (3 i)) (get k-extracts)))))
;; `inner`, under binders `bs`, with `m` for them, each within its bound and finite if need be.
(define k-subst-checked (subr (maxeff checks spin) (k-binders k-map int int int) int)
  (lambda (bs m inner a b)
    (begin (k-check-bounds bs m a b) (k-check-finite-sizes bs m inner a b) (k-subst inner m))))
;; `inner`, under binders `bs`, projected with `ds`: an error where they do not fit, or knot.
(define k-projected (subr (maxeff checks spin) (k-binders (listof k-desc acyclic) int int int) int)
  (lambda (bs ds inner a b)
    (let ((inst (k-subst-checked bs (k-proj-map bs ds a b) inner a b)))
      (begin (k-no-knot inst a b) inst))))
;; An `if`'s type, its branches a `tc` and a `td`: the greater; an error if neither is.
(define k-join-branches (subr (maxeff checks spin) (int int int int) int)
  (lambda (tc td a b)
    (cond ((k-subtype tc td) td)
          ((k-subtype td tc) tc)
          ;; Naturals of sizes not shown equal: a `nat`.
          ((and (k-nat-ty? tc) (k-nat-ty? td)) (k-ty-new (ty-nat (sz-finite))))
          (else
           (k-fail (k-cat4 "the branches are a " (k-show-ty tc) " and a " (k-show-ty td)) a b)))))
;; If `p` is `(name v)`, `name` standard, the variable, as the binding it is
;; (none or one).
(define k-certifying-test (subr (maxeff kreads (alloc @t) spin) (kx string) k-named)
  (lambda (p name)
    (tagcase p
      (x-app (f args a b)
        (if (and (string=? (k-std-op (k-under f)) name) (k-sc-one-arg? args))
            (tagcase (car args)
              (x-var (v va vb) (the k-named (cons (cons v (k-binding-depth v)) nil)))
              (else y nil))
            nil))
      (else y nil))))
;; If `p` is `(acyclic? v)`, the variable, as the binding it is (none or one).
(define k-acyclic-test (subr (maxeff kreads (alloc @t) spin) (kx) k-named)
  (lambda (p) (k-certifying-test p "acyclic?")))
;; If `p` is `(nat? v)`, the variable, as the binding it is (none or one).
(define k-nat-test (subr (maxeff kreads (alloc @t) spin) (kx) k-named)
  (lambda (p) (k-certifying-test p "nat?")))
;; What is certified so far: variables acyclic, of lengths, and natural.
(define-type k-certs (productof (1 k-named) (2 k-cert-lens) (3 k-named)))
(define k-certs-now (subr kreads () k-certs)
  (lambda ()
    (product (1 (get k-certified)) (2 (get k-certified-lengths)) (3 (get k-certified-nats)))))
;; Note what test `p` certifies, if anything: a variable acyclic, of a length, or natural.
(define k-push-certified (subr (maxeff kstate spin) (kx) unit)
  (lambda (p)
    (let ((cert (k-acyclic-test p)) (lens (k-length-test p)) (nats (k-nat-test p)))
      (begin
        (if (null? cert) #u (set k-certified (cons (car cert) (get k-certified))))
        (if (null? lens) #u (set k-certified-lengths (cons (car lens) (get k-certified-lengths))))
        (if (null? nats) #u (set k-certified-nats (cons (car nats) (get k-certified-nats))))))))
;; What checking an `if`'s branches puts back as it goes: what was certified, and the size
;; facts, before; and what its test shows when it holds, and when not.
(define-type k-tested (productof (1 k-certs) (2 k-fact-list) (3 k-branch-facts)))
;; Before the branch where `p` holds: what it certifies, and the facts it shows, in force.
(define k-enter-then (subr (maxeff kstate spin) (kx) k-tested)
  (lambda (p)
    (let* ((certs (k-certs-now))
           (pushed (k-push-certified p))
           (facts (k-test-facts p))
           (fsaved (get k-size-facts))
           (fyes (set k-size-facts (k-with-facts (car facts) fsaved))))
      (product (1 certs) (2 fsaved) (3 facts)))))
;; After it, before the branch where `p` does not: nothing certified, and what `p` shows so.
(define k-enter-else (subr kstate (k-tested) unit)
  (lambda (tested)
    (let ((certs (extract tested 1)) (fsaved (extract tested 2)))
      (begin
        (set k-certified (extract certs 1))
        (set k-certified-lengths (extract certs 2))
        (set k-certified-nats (extract certs 3))
        (set k-size-facts (k-with-facts (cdr (extract tested 3)) fsaved))))))
;; After both: the facts as they were.
(define k-leave-test (subr kstate (k-tested) unit) (lambda (t) (set k-size-facts (extract t 2))))
;; Whether `args` are one variable, as the binding it is, among `cs`.
(define k-certified-arg? (subr (maxeff kreads spin) (k-named kxs) bool)
  (lambda (cs args)
    (and (k-sc-one-arg? args)
         (tagcase (car args)
           (x-var (v va vb) (k-certified-has? cs v (k-binding-depth v)))
           (else y #f)))))
;; Whether `x` is a `lambda` of no parameters.
(define k-thunk-lambda? (subr (read @globals) (kx) bool)
  (lambda (x) (tagcase x (x-lambda (ps body a b) (null? ps)) (else y #f))))
;; Note argument `i` found to be a `t`, of effect `e`.
(define k-arg-found (subr kstate (k-done int int k-eff) unit)
  (lambda (done i t e) (begin (array-set! (extract done 1) i t) (array-set! (extract done 2) i e))))
;; Note argument `i` found to be what `r` says, and what that solves of its parameter's type `p`.
(define k-arg-unified (subr (maxeff kstate spin) (int k-binders k-solved k-done int k-te) unit)
  (lambda (p kinds solved done i r)
    (begin (k-unify p (extract r 1) kinds solved (k-new-trail))
           (k-arg-found done i (extract r 1) (extract r 2)))))
;; Variable `s`, of polymorphic type `t`, at `a`..`b`: `t` instantiated at
;; `p`, and the effect of naming `s`.
(define k-poly-instance (subr (maxeff checks spin) (symbol int int int int) k-te)
  (lambda (s t p a b) (k-te (k-instantiate-against t p a b) (k-naming-effect s t))))
;; `x`, if a variable of a polymorphic type (a standard `list`): its type
;; instantiated at `p`, and the effect of naming it; else none.
(define k-poly-var-at (subr (maxeff checks spin) (kx int) (listof k-te @t))
  (lambda (x p)
    (tagcase x
      (x-var (s a b)
        (let ((t (k-lookup s)))
          (if (and (>= t 0) (tagcase (k-get t) (ty-poly (bs body) #t) (else y #f)))
              (the (listof k-te @t) (cons (k-poly-instance s t p a b) nil))
              (the (listof k-te @t) nil))))
      (else y (the (listof k-te @t) nil)))))
;; Whether `et` is a `(nat z)` that natural literal `k` is one of.
(define k-literal-within? (subr kreads (k-ty int) bool)
  (lambda (et k) (tagcase et (ty-nat (z) (k-size-le? (k-size-lit k) z)) (else w #f))))
;; Whether `et` is a `nlist` of no elements, or of any number.
(define k-may-be-empty? (subr kreads (k-ty) bool)
  (lambda (et)
    (tagcase et
      (ty-nlist (e z r) (or (k-size-any? z) (k-size-eq? z (k-size-lit 0))))
      (else w #f))))
;; A `tagcase`'s type, its arms of `types`: `expected` if given (≥ 0), or the least they all are.
(define k-arms-type (subr (maxeff checks spin) (kx k-ids int) int)
  (lambda (x types expected)
    (if (>= expected 0)
        expected
        (let ((found (k-upper-bound types types)))
          (if (< found 0)
              (let ((shown (k-join (k-show-list types k-printing-none) ", ")))
                (k-fail-at (string-append "the arms are " shown) x))
              found)))))
;; The region a place of type `t` is at; an error at `a`..`b` if `t` is not a place.
(define k-place-region (subr (maxeff checks spin) (int int int) k-region)
  (lambda (t a b)
    (tagcase (k-get t)
      (ty-place (r) r)
      (else y (k-fail-ty "a region is expected here, and this is a " t a b)))))
;; A type, or none: none or one.
(define-type k-maybe-ty (listof k-ty acyclic))
;; What a `make-bloblet` of `fields`, checked against `expected` (≥ 0), is told: that type, if a
;; bloblet not frozen, of as many fields, at the region `given` (if any).
(define k-bloblet-want (subr (maxeff kreads (alloc @t) spin) (int kxs k-regions) k-maybe-ty)
  (lambda (expected fields given)
    (if (< expected 0)
        nil
        (tagcase (k-get expected)
          (ty-bloblet (fs z r)
            (if (and (not z) (= (k-length fs) (k-length fields))
                     (or (null? given) (k-region=? r (car given))))
                (cons (k-get expected) nil)
                nil))
          (else y nil)))))
;; Field `i`'s type, of a bloblet of type `bt` whose fields are `fields`; an error if none.
(define k-bloblet-field (subr (maxeff checks spin) (int k-ids int int int) int)
  (lambda (bt fields i a b)
    (if (< i (k-length fields))
        (k-nth fields i)
        (let ((last (- (k-length fields) 1)))
          (k-fail (k-cat5 "a " (k-show-ty bt) " has no field " (int->string i)
                          (string-append ": its fields are 0 to " (int->string last))) a b)))))
;; Type `t` and effect `e`, with `region` read, or written.
(define k-te-reading (subr (maxeff kreads (alloc @t) spin) (int k-region k-eff) k-te)
  (lambda (t region e) (k-te t (k-insert (a-read region) e))))
(define k-te-writing (subr (maxeff kreads (alloc @t) spin) (int k-region k-eff) k-te)
  (lambda (t region e) (k-te t (k-insert (a-write region) e))))
;; Whether a handler that is a `c` takes a `payload` to an `answer`.
(define k-handles? (subr (maxeff kstate spin) (k-callable int int) bool)
  (lambda (c payload answer)
    (let ((ps (extract c 2)))
      (and (= (k-length ps) 1) (k-subtype payload (car ps)) (k-subtype (extract c 3) answer)))))
;; What a handler of type `ht` is called as, taking a `payload` to an `answer`; or an error.
(define k-handler-callable (subr (maxeff checks spin) (kx int int int) k-callable)
  (lambda (handler ht payload answer)
    (let ((c (k-as-subr ht)))
      (cond ((null? c) (k-fail-ty-at "a handler is a subroutine, not a " ht handler))
            ((k-handles? (car c) payload answer) (car c))
            (else
             (let ((wants (k-handler-wants payload answer)))
               (k-fail-at (k-cat4 wants "; it is a " (k-show-ty ht) "") handler)))))))

))

(define k-note-apply-shares (with check-synth-module k-note-apply-shares))
(define k-note-frozen-define (with check-synth-module k-note-frozen-define))
(define-type k-done (select check-synth-module k-done))
(define k-te-masked (with check-synth-module k-te-masked))
(define k-new-subr (with check-synth-module k-new-subr))
(define-type k-types-eff (select check-synth-module k-types-eff))
(define k-projected (with check-synth-module k-projected))
(define k-enter-then (with check-synth-module k-enter-then))
(define k-enter-else (with check-synth-module k-enter-else))
(define k-leave-test (with check-synth-module k-leave-test))
(define k-join-branches (with check-synth-module k-join-branches))
(define k-bind-place (with check-synth-module k-bind-place))
(define k-region-form (with check-synth-module k-region-form))
(define k-note-extract (with check-synth-module k-note-extract))
(define k-masked (with check-synth-module k-masked))
(define k-place-region (with check-synth-module k-place-region))
(define k-nlist-te (with check-synth-module k-nlist-te))
(define k-certified-arg? (with check-synth-module k-certified-arg?))
(define k-new-trail (with check-synth-module k-new-trail))
(define k-subst-checked (with check-synth-module k-subst-checked))
(define k-arg-found (with check-synth-module k-arg-found))
(define k-arg-unified (with check-synth-module k-arg-unified))
(define k-thunk-lambda? (with check-synth-module k-thunk-lambda?))
(define k-poly-var-at (with check-synth-module k-poly-var-at))
(define k-as-expected (with check-synth-module k-as-expected))
(define k-literal-within? (with check-synth-module k-literal-within?))
(define k-may-be-empty? (with check-synth-module k-may-be-empty?))
(define k-arms-type (with check-synth-module k-arms-type))
(define k-fail-no-arm (with check-synth-module k-fail-no-arm))
(define k-te-onto (with check-synth-module k-te-onto))
(define k-bloblet-want (with check-synth-module k-bloblet-want))
(define k-bloblet-field (with check-synth-module k-bloblet-field))
(define k-te-reading (with check-synth-module k-te-reading))
(define k-te-writing (with check-synth-module k-te-writing))
(define k-handler-callable (with check-synth-module k-handler-callable))
