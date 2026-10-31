;;; The checker, in FX-26: the rules, each expression's type and effect.
;;; Part of the checker, `check-types.fx` first (PLAN.md §11, step 10).

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
    ;; Part of it in a file of its own (`check-synth-parts.fx`), made of what it is
    ;; given.
    (let ((check-synth-parts
           ((load-input "fx26:check-synth-parts.fx")
            check-types check-test-facts check-resolve check-env check-infer check-facts
            check-print check-bounds check-expect check-errors check-effects check-mask check-unions
            check-terminate check-holds check-subtype check-calls check-subst check-binders
            check-sub-env check-print-parts check-read-helpers check-blobrefs)))
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

;; Given on, all `check-synth-parts.fx` defines.
(import check-synth-parts k-fail-no-arm k-acyclic-list? k-note-frozen-define k-note-call
        k-note-apply-shares k-partial-pair-arg k-union-pair-member k-te-masked k-masked k-te-onto
        k-as-expected k-claims-proved k-new-subr k-new-subr-spec k-nlist-te k-new-trail k-bind-place
        k-region-form k-note-extract k-note-field k-subst-checked k-projected k-nil-if-any
        k-nils-if-any k-nil-pair k-nil-pairs k-any-nil? k-join-with-nil k-parts-known? k-fold-join
        k-join-known k-join-branches k-acyclic-test k-nat-test k-certs-now k-push-certified
        k-nars-append k-step=? k-steps=? k-steps-snoc k-path-step k-path-of k-path-fact-in
        k-path-fact-ty k-reached-of k-path-walk k-path-type k-path-ty k-path-te k-nars-of k-nars-put
        k-props-narrow k-latent-narrowing k-narrowings k-var-narrows k-push-paths k-put-narrowing
        k-drop-facts k-cut-paths k-narrows-append k-may-alias? k-hits? k-open-regions k-kills?
        k-kill-each k-all-dead? k-kill-paths k-enter-then k-enter-else k-leave-test k-certified-arg?
        k-branch-join k-join-parts k-join-part)

;; Whether `x` is a `lambda` of no parameters.
;; `(certify-nat v)`: `v`'s value as a `nat`, where `nat?` has just found
;; `v` no less than 0; nowhere else. `synth` the checker's knot.
(define k-certify-nat (->* (kx kxs k-synther) k-te)
  (lambda (x args synth)
    (if (not (k-certified-arg? (get k-certified-nats) args))
        (k-fail-at "`certify-nat` takes only a variable `nat?` has just found no less than 0" x)
        (let ((r (synth (car args))))
          (begin (k-expect (car args) (extract r 1) k-int)
                 (k-te (k-ty-new (ty-nat (sz-finite))) (extract r 2)))))))
(define k-thunk-lambda? (->* (kx) bool)
  (lambda (x) (tagcase x (x-lambda (ps body a b abk) (null? ps)) (else y #f))))
;; Note argument `i` found to be a `t`, of effect `e`.
(define k-arg-found (->* (k-done int int k-eff) unit)
  (lambda (done i t e) (begin (array-set! (extract done 1) i t) (array-set! (extract done 2) i e))))
;; Note argument `i` found to be what `r` says, and what that solves of its parameter's type `p`.
(define k-arg-unified (->* (int k-binders k-solved k-done int k-te) unit)
  (lambda (p kinds solved done i r)
    (begin (k-unify p (extract r 1) kinds solved (k-new-trail))
           (k-arg-found done i (extract r 1) (extract r 2)))))
(define k-no-call k-call-checked (product (1 (product (1 -1) (2 -1) (3 -1))) (2 -1)))
(define k-checked-call (ref k-call-checked @t) (new k-no-call))
;; Call `x`, found `r`, as `expected`: its effect, and its type noted.
(define k-as-expected-call (->* (kx k-te int) k-eff)
  (lambda (x r expected)
    (let ((e (if (k-fixed-literal? x expected (k-start x) (k-end x))
                 (extract r 2)
                 (k-as-expected x r expected))))
      (begin (set k-checked-call (product (1 (k-at-of x)) (2 (extract r 1)))) e))))
;; `k-unify` of a call's `result` against what is `expected` of it: bounds
;; from above.
(define k-unify-above (->* (int int k-binders k-solved) unit)
  (lambda (result expected kinds solved)
    (k-from-above (lambda () (k-unify result expected kinds solved (k-new-trail))))))
;; The instance `kinds` solved make of `inner`, and `solved`'s bounds
;; dropped.
(define k-solved-instance (->* (k-binders k-solved int int int int) int)
  (lambda (kinds solved a b ft inner)
    (k-drop-bounds solved (k-subst-checked kinds (k-finish kinds solved a b ft) inner a b))))
;; Whether `param` mentions a type binder whose bounds have not met: one
;; open once those binders' solutions are set aside.
(define k-mentions-unsettled? (->* (int k-binders k-solved) bool)
  (lambda (param kinds solved)
    (let ((without (the k-solved (new (k-map-unsettled solved (get solved) #f)))))
      (k-mentions-unknown-type? param kinds without))))
;; `param` with each binder whose bounds have not met at its upper bound,
;; where it has one.
(define k-at-most (->* (int k-solved) int)
  (lambda (param solved) (k-subst param (k-map-unsettled solved (get solved) #t))))
;; Where `param` is a type binder bounded only from below, by a sum: that
;; sum; else -1 (`infer.rs`'s `sum_lower_only`).
(define k-sum-lower-only (->* (int k-solved) int)
  (lambda (param solved)
    (tagcase (k-get (k-resolve param))
      (ty-var (v)
        (let ((lo (k-lower-only solved v)))
          (if (and (>= lo 0) (tagcase (k-get (k-resolve lo)) (ty-sum (ps) #t) (else y #f))) lo -1)))
      (else y -1))))
;; Whether `x` is a variable of a type not polymorphic.
(define k-mono-var? (->* (kx) bool)
  (lambda (x)
    (tagcase x
      (x-var (s a b abk)
        (let ((t (k-lookup s)))
          (and (>= t 0) (tagcase (k-get t) (ty-poly (bs body) #f) (else y #t)))))
      (else y #f))))
;; Argument `i`, `arg`, of parameter type `param`, `p` as solved so far:
;; checked against `p`, its type and effect noted. Where `param` mentions a
;; type binder whose bounds have not met, what the argument is bounds it
;; too, rather than being told (the Rust checker's `bounded_argument`): a
;; variable says its own type; a call, checked against the binders' upper
;; bounds where they have them (else what they are so far), its own result
;; there; anything else, checked so, is what it was checked against.
;; `check` and `synth`, the rules'.
(define k-bounded-arg
  (->* (kx int int k-binders k-solved k-done int (subr (maxeff checks spin) (kx int) k-eff)
            (subr (maxeff checks spin) (kx) k-te))
       unit)
  (lambda (arg param p kinds solved done i check synth)
    (cond ((not (k-mentions-unsettled? param kinds solved))
           (k-arg-found done i p (check arg p)))
          ;; A binder at least a sum, and bounded no other way: what the
          ;; argument is raises it to the two's join (`k-branch-join`), as an
          ;; `if`'s branches join; with no join, it stays, and the argument
          ;; is refused at the end, as before.
          ((>= (k-sum-lower-only param solved) 0)
           (let* ((r (synth arg))
                  (j (k-branch-join (k-sum-lower-only param solved) (extract r 1) 0)))
             (begin (k-unify param (if (>= j 0) j (extract r 1)) kinds solved (k-new-trail))
                    (k-arg-found done i (extract r 1) (extract r 2)))))
          ;; A variable's type is its own; a call, told what it is, is told
          ;; its regions too.
          ((k-mono-var? arg) (k-arg-unified param kinds solved done i (synth arg)))
          (else
           (let ((q (k-at-most param solved)))
             (begin
               (set k-checked-call k-no-call)
               (let* ((e (check arg q)) (c (get k-checked-call))
                      (t (if (k-at-is? (extract c 1) (k-start arg) (k-end arg) (k-kth arg))
                             (extract c 2)
                             q)))
                 (begin (k-unify param t kinds solved (k-new-trail))
                        (k-arg-found done i t e)))))))))
;; Variable `s`, of polymorphic type `t`, at `a`..`b`: `t` instantiated at
;; `p`, and the effect of naming `s`.
(define k-poly-instance (->* (symbol int int int int) k-te)
  (lambda (s t p a b) (k-te (k-instantiate-against t p a b) (k-naming-effect s t))))
;; `x`, if a variable of a polymorphic type (a standard `list`): its type
;; instantiated at `p`, and the effect of naming it; else none.
(define k-poly-var-at (->* (kx int) (listof k-te @t))
  (lambda (x p)
    (tagcase x
      (x-var (s a b abk)
        (let ((t (k-lookup s)))
          (if (and (>= t 0) (tagcase (k-get t) (ty-poly (bs body) #t) (else y #f)))
              (the (listof k-te @t) (cons (k-poly-instance s t p a b) nil))
              (the (listof k-te @t) nil))))
      (else y (the (listof k-te @t) nil)))))
;; `nil` (a variable of a list of any elements), argument `i`, where its
;; parameter `q`, `p` so far, is not yet known: the type `nil` (`TODO.md`
;; §48), heard last, after what the context expects and every other
;; argument; anything else, the error.
(define k-nil-told (->* (kx int int int k-binders k-solved k-done) unit)
  (lambda (arg i p q kinds solved done)
    (tagcase arg
      (x-var (s a b abk)
        (let ((t (k-lookup s)))
          (if (and (>= t 0) (k-list-of-any? t))
              (let ((nil-ty (k-ty-new (ty-nil))))
                (begin
                  (k-unify q nil-ty kinds solved (k-new-trail))
                  (if (k-mentions-unknown-type? q kinds solved) (k-fail-not-known arg i p) #u)
                  (k-arg-found done i nil-ty (k-naming-effect s t))))
              (k-fail-not-known arg i p))))
      (else y (k-fail-not-known arg i p)))))
;; The parts of `ps`, from position `i`, that `free` names, and their
;; positions: what a `with` binds.
(define k-with-used (->* (k-parts k-names int) (productof (1 k-parts) (2 k-ids)))
  (lambda (ps free i)
    (if (null? ps)
        (product (1 (the k-parts nil)) (2 (the k-ids nil)))
        (let ((rest (k-with-used (cdr ps) free (+ i 1))))
          (if (k-has-name? free (extract (car ps) 1))
              (product (1 (the k-parts (cons (car ps) (extract rest 1))))
                       (2 (the k-ids (cons i (extract rest 2)))))
              rest)))))
;; A result `(pairof A v R)`, `v` solved to `nil` and nothing expected of
;; it, has `v` a `(listof A R)` instead (`DONE.md` §48): the pair is new, so
;; no alias sees its tail as `nil` alone, and `(cons 1 nil)` is a list. Each
;; argument is checked against what its parameter then is.
(define k-widen-nil-tail (->* (int k-binders k-solved) unit)
  (lambda (result kinds solved)
    (tagcase (k-get (k-resolve result))
      (ty-pair (h tl r nl)
        (tagcase (k-get (k-resolve tl))
          (ty-var (v) (if (k-binder-has? kinds v) (k-widen-tail-at v h r kinds solved) #u))
          (else y #u)))
      (else y #u))))
(define k-widen-tail-at (->* (int int k-region k-binders k-solved) unit)
  (lambda (v h r kinds solved)
    (let ((f (k-map-find (get solved) v)) (head (k-subst h (get solved))))
      (if (and (not (null? f))
               (tagcase (cdr (car f))
                 (dt (t) (tagcase (k-get (k-resolve t)) (ty-nil () #t) (else y #f)))
                 (else y #f))
               (not (k-mentions-unknown-type? head kinds solved)))
          (let* ((slot (k-slot)) (pair (k-ty-new (ty-pair head slot r #t))))
            (begin
              (k-set-link slot pair)
              (set solved (cons (cons v (dt (k-subst slot (get solved)))) (get solved)))))
          #u))))
;; `(with m body)` checked as a `expected`, if `m` is `#%fx` and `body` a
;; standard name of a polymorphic type: instantiated as the plain name is
;; (`TODO.md` §46); its effect, in a list of one, or none.
(define k-fx-poly-check (->* (kx symbol kx int) (listof k-eff @t))
  (lambda (x m body expected)
    (let ((t (tagcase body
               (x-var (n a b abk) (if (k-fx-module? m) (k-std-type n) -1))
               (else y -1))))
      (if (and (>= t 0) (tagcase (k-get t) (ty-poly (bs pb) #t) (else y #f)))
          (begin (k-expect x (k-instantiate-against t expected (k-start x) (k-end x)) expected)
                 (the (listof k-eff @t) (cons nil nil)))
          (the (listof k-eff @t) nil)))))
;; Whether `et` is a `(nat z)` that literal `k` is one of, or a fixed-width
;; integer type whose range it is in: refused, the range said, if out of
;; it (`k-in-fixed-range?`).
(define k-literal-within? (->* (k-ty int kx) bool)
  (lambda (et k x)
    (tagcase et
      (ty-nat (z) (and (>= k 0) (k-size-le? (k-size-lit k) z)))
      (ty-base (b) (k-in-fixed-range? b k (k-start x) (k-end x)))
      (else w #f))))
;; Whether `et` is a `nlist` of no elements, or of any number.
(define k-may-be-empty? (->* (k-ty) bool)
  (lambda (et)
    (tagcase et
      (ty-nlist (e z r) (or (k-size-any? z) (k-size-eq? z (k-size-lit 0))))
      (else w #f))))
;; A `tagcase`'s type, its arms of `types`: `expected` if given (≥ 0), or the least they all are.
(define k-arms-type (->* (kx k-ids int) int)
  (lambda (x types expected)
    (if (>= expected 0)
        expected
        (let* ((ts (k-join-with-nil types))
               (bound (k-upper-bound ts ts))
               ;; One the others are within; else, of sums, their join.
               (found (if (or (>= bound 0) (null? ts)) bound (k-fold-join (car ts) (cdr ts)))))
          (if (< found 0)
              (let ((shown (k-join (k-show-list types k-printing-none) ", ")))
                (k-fail-at (string-append "the arms are " shown) x))
              found)))))
;; The region a place of type `t` is at; an error at `a`..`b` if `t` is not a place.
(define k-place-region (->* (int int int) k-region)
  (lambda (t a b)
    (tagcase (k-get t)
      (ty-place (r) r)
      (else y (k-fail-ty "a region is expected here, and this is a " t a b)))))
;; What a `make-bloblet` of `fields`, checked against `expected` (≥ 0), is told: that type, if a
;; bloblet not frozen, of as many fields, at the region `given` (if any).
(define k-bloblet-want (->* (int kxs k-regions) k-maybe-ty)
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
(define k-bloblet-field (->* (int k-ids int int int) int)
  (lambda (bt fields i a b)
    (if (< i (k-length fields))
        (k-nth fields i)
        (let ((last (- (k-length fields) 1)))
          (k-fail (k-cat5 "a " (k-show-ty bt) " has no field " (int->string i)
                          (string-append ": its fields are 0 to " (int->string last))) a b)))))
;; Type `t` and effect `e`, with `region` read, or written.
(define k-te-reading (->* (int k-region k-eff) k-te)
  (lambda (t region e) (k-te t (k-insert (a-read region) e))))
(define k-te-writing (->* (int k-region k-eff) k-te)
  (lambda (t region e) (k-te t (k-insert (a-write region) e))))
;; Whether a handler that is a `c` takes a `payload` to an `answer`.
(define k-handles? (->* (k-callable int int) bool)
  (lambda (c payload answer)
    (let ((ps (extract c 2)))
      (and (= (k-length ps) 1) (k-subtype payload (car ps)) (k-subtype (extract c 3) answer)))))
;; What a handler of type `ht` is called as, taking a `payload` to an `answer`; or an error.
(define k-handler-callable (->* (kx int int int) k-callable)
  (lambda (handler ht payload answer)
    (let ((c (k-as-subr ht)))
      (cond ((null? c) (k-fail-ty-at "a handler is a subroutine, not a " ht handler))
            ((k-handles? (car c) payload answer) (car c))
            (else
             (let ((wants (k-handler-wants payload answer)))
               (k-fail-at (k-cat4 wants "; it is a " (k-show-ty ht) "") handler)))))))

;;; ------------------------------------------------------------ blobrefs
;; The `blobref` forms (`Checker::synth_blobref`), first operand `ox` of
;; type `xt`: what the second, if any, is checked against (an `int`, or the
;; scalar's type; -1 for none), failing in the Rust checker's order.
(define k-blobref-arg (->* (kx string kx int) int)
  (lambda (x name ox xt)
    (if (string=? name "blobref-at")
        (tagcase (k-get (k-resolve xt))
          (ty-bloblet (fs z r) k-int)
          (else y (k-fail-ty-at "a bloblet is expected here, and this is a " xt ox)))
        (let ((p (k-blobref-parts xt)))
          (cond ((null? p) (k-fail-ty-at "a blobref is expected here, and this is a " xt ox))
                ((string=? name "blobref+") k-int)
                ((string=? name "blobref-set!")
                 (let ((r (k-blobref-region (k-start x) (k-end x) (k-kth x) xt (car (car p))
                                            (cdr (car p)) #f)))
                   (cdr (car p))))
                ((or (string=? name "blobref-index") (string=? name "blobref-length"))
                 (cond ((< (car (k-flat-array-parts (cdr (car p)))) 0)
                        (k-fail-ty-at "a blobref to a flat array is expected here, and this is a "
                                      xt ox))
                       ;; A length takes no second operand.
                       ((string=? name "blobref-length") -1)
                       (else k-int)))
                ((and (string=? name "blobref-variant!")
                      (< (car (k-flat-sum-size (cdr (car p)))) 0))
                 (k-fail-ty-at "a blobref to a flat sum is expected here, and this is a " xt ox))
                (else -1))))))
;; Its type and effect, `e` its operands', `args` them.
(define k-blobref-result (->* (kx string int k-eff int kxs) k-te)
  (lambda (x name xt e expected args)
    (let ((a (k-start x)) (z (k-end x)) (zk (k-kth x)))
      (if (string=? name "blobref-at")
          (k-te (k-blobref-of xt (k-blobref-wanted a z zk expected)) e)
          (let* ((p (car (k-blobref-parts xt))) (b (car p)) (f (cdr p)))
            (case name
              (("blobref+") (k-te (k-blobref-of b (k-blobref-wanted a z zk expected)) e))
              (("blobref-owner") (k-te b e))
              (("blobref-offset") (k-te k-int e))
              (("blobref-index") (k-te (k-blobref-of b (k-blobref-element a z zk f)) e))
              (("blobref-length") (k-te (k-blobref-length a z zk f) e))
              (("blobref-get") (k-te-reading f (k-blobref-region a z zk xt b f #t) e))
              (("blobref-variant!")
               (let ((lx (car (cdr args))))
                 (k-blobref-variant a z zk xt b f lx (k-start lx) (k-end lx) e)))
              (else (k-te-writing k-unit (k-blobref-region a z zk xt b f #t) e))))))))
;; `(extract ex l)`, `ex` of type `pt` and effect in `r`, not a product: a
;; blobref to a flat product's field (`Checker`'s `Exp::Extract`).
(define k-extract-blobref (->* (kx int kx symbol k-te) k-te)
  (lambda (x pt ex l r)
    (let ((p (k-blobref-parts pt)) (a (k-start x)) (z (k-end x)))
      (if (null? p)
          (k-fail-ty-at "a product is expected here, and this is a " pt ex)
          (let ((fld (k-flat-field (cdr (car p)) l)))
            (if (< (car fld) 0)
                (k-fail (k-cat5 "a " (k-show-ty pt) " has no `" (symbol->string l) "` laid out")
                        a z)
                (begin (k-note-extract (k-at-of x) (datum-blobref-field (car fld)))
                       (k-te-masked x (k-blobref-of (car (car p)) (cdr fld)) (extract r 2)))))))))


;; The checker's knot, `check-rules.fx`'s, given to what checks forms here.
(define-type k-synther (subr (maxeff checks spin) (kx) k-te))
(define-type k-checker (subr (maxeff checks spin) (kx int) k-eff))
;; `(name bx i rest …)`: a bloblet's field `i` read or written, it frozen,
;; or a byte of it; `synth` and `check` the knot's.
(define k-bloblet-op (->* (kx string int kxs k-synther k-checker) k-te)
  (lambda (x name i args synth check)
    (let* ((a (k-start x)) (b (k-end x))
           (bx (car args)) (rest (cdr args)) (rb (synth bx)) (bt (extract rb 1)))
      (tagcase (k-get bt)
        (ty-bloblet (fields frozen region)
          (let* ((e (extract rb 2))
                 (te
                  (case name
                    (("bloblet-ref")
                     (let ((t (k-bloblet-field bt fields i a b)))
                       (if frozen (k-te t e) (k-te-reading t region e))))
                    (("bloblet-set!")
                     (let ((t (k-bloblet-field bt fields i a b)))
                       (if frozen
                           (k-fail-frozen bt a b)
                           (k-te-writing k-unit region (k-union e (check (car rest) t))))))
                    (("bloblet-freeze")
                     (k-te-writing (k-ty-new (ty-bloblet fields #t region)) region e))
                    (("bloblet-byte")
                     (k-te-reading k-int region (k-union e (check (car rest) k-int))))
                    (("bloblet-set-byte!")
                     (let* ((e1 (check (car rest) k-int)) (e2 (check (car (cdr rest)) k-int)))
                       (k-te-writing k-unit region (k-union e (k-union e1 e2)))))
                    (else (k-te k-int e)))))
            (k-masked x te)))
        (else y (k-fail-ty-at "a bloblet is expected here, and this is a " bt bx))))))
;; The `blobref` forms (`k-blobref-arg`, `k-blobref-result`).
(define k-blobref-op (->* (kx string kxs int k-synther k-checker) k-te)
  (lambda (x name args expected synth check)
    (let* ((rx (synth (car args))) (xt (extract rx 1))
           (want (k-blobref-arg x name (car args) xt))
           (e (if (< want 0)
                  (extract rx 2)
                  (k-union (extract rx 2) (check (car (cdr args)) want)))))
      (k-masked x (k-blobref-result x name xt e expected args)))))
;; An `rlambda`'s type: its `lambda`'s, told `expected`'s parameter and
;; result types if it is a subroutine's, and its specification `sp`, with
;; `(read R)` in its latent effect, since calling it reads the closure;
;; making it allocates in `R`, the region `r` names. `synth` and
;; `lambda-as` are the checker's knot's (`check-rules.fx`).
(define k-synth-rlambda-by (->* (kx kx kx int k-specs k-synther k-lambda-as) k-te)
  (lambda (x r l expected sp synth lambda-as)
    (let* ((rr (synth r))
           (rt (extract rr 1))
           (g (k-place-region rt (k-start r) (k-end r)))
           (c (if (< expected 0) (the (listof k-callable acyclic) nil) (k-as-subr expected)))
           (n (tagcase l (x-lambda (ps body a b abk) (k-length ps)) (else y 0)))
           (lt (cond
                 ((null? c) (lambda-as l nil -1 nil))
                 ((not (= (k-length (extract (car c) 2)) n))
                  (k-fail-arity (k-length (extract (car c) 2)) "rlambda" n (k-start x) (k-end x)))
                 (else (lambda-as l (extract (car c) 2) (extract (car c) 3) sp))))
           (t (tagcase (k-get (extract lt 1))
                (ty-subr (e ps res cv spc)
                  (k-ty-new (ty-subr (k-insert (a-read g) e) ps res cv spc)))
                (else y (k-fail-at "a lambda" x))))
           (e (k-insert (a-alloc g) (extract rr 2))))
      (k-te-masked x t e))))
))))
