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
      (ty-pair (a d r nl) (tagcase r (r-frozen (p finite) finite) (else y #f)))
      (else y #f))))
;; Note, for the compilers, that a top-level definition's value `x`, of
;; type `t`, is a list in a frozen region (`acyclic` or `const`): data
;; nothing writes, which they may make once if it is made of literals; the
;; fact -501 (`c-fill-facts`). As the Rust checker's `frozen_defines`.
(define k-note-frozen-define (subr (maxeff checks spin) (int kx) unit)
  (lambda (t x)
    (if (tagcase (k-get t)
          (ty-pair (a d r nl) (tagcase r (r-frozen (p finite) #t) (else y #f)))
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
    (case k ((0) "letregion") ((1) "letrena") ((2) "letreap") (else "letfreeze"))))
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
;; `t`, or, if a list of any elements (`nil`), the type `nil`.
(define k-nil-if-any (subr (maxeff kstate spin) (int) int)
  (lambda (t) (if (k-list-of-any? t) (k-ty-new (ty-nil)) t)))
;; `ts`, each `nil` the type `nil`: what other arms are, as in an `if`.
(define k-nils-if-any (subr (maxeff kstate spin) (k-ids) k-ids)
  (lambda (ts) (if (null? ts) nil (cons (k-nil-if-any (car ts)) (k-nils-if-any (cdr ts))))))
;; Branches' types, each `nil` the type `nil`, and, if one is, each pair one
;; that may be `nil`: their join, if they have one, is then one of them.
(define k-nil-pair (subr (maxeff kstate spin) (int) int)
  (lambda (t)
    (tagcase (k-get (k-resolve t)) (ty-pair (a d r nl) (k-ty-new (ty-pair a d r #t))) (else y t))))
(define k-nil-pairs (subr (maxeff kstate spin) (k-ids) k-ids)
  (lambda (ts) (if (null? ts) nil (cons (k-nil-pair (car ts)) (k-nil-pairs (cdr ts))))))
(define k-any-nil? (subr (maxeff kreads spin) (k-ids) bool)
  (lambda (ts)
    (and (not (null? ts))
         (or (tagcase (k-get (k-resolve (car ts))) (ty-nil () #t) (else y #f))
             (k-any-nil? (cdr ts))))))
(define k-join-with-nil (subr (maxeff kstate spin) (k-ids) k-ids)
  (lambda (ts0)
    (let ((ts (k-nils-if-any ts0))) (if (k-any-nil? ts) (k-nil-pairs ts) ts))))
;; An `if`'s type, its branches a `tc` and a `td`: the greater; an error if neither is.
(define k-join-known (subr (maxeff checks spin) (int int int int) int)
  (lambda (tc td a b)
    (cond ((k-subtype tc td) td)
          ((k-subtype td tc) tc)
          ;; Naturals of sizes not shown equal: a `nat`.
          ((and (k-nat-ty? tc) (k-nat-ty? td)) (k-ty-new (ty-nat (sz-finite))))
          (else
           (k-fail (k-cat4 "the branches are a " (k-show-ty tc) " and a " (k-show-ty td)) a b)))))
;; The same, `nil`, beside another branch, what that is if `nil` is one
;; (`TODO.md` §48); beside `nil`, the type `nil`; beside a pair, the pair
;; that may be `nil`.
(define k-join-branches (subr (maxeff checks spin) (int int int int) int)
  (lambda (tc td a b)
    (let ((ts (k-join-with-nil (list tc td)))) (k-join-known (car ts) (car (cdr ts)) a b))))
;; If `p` certifies a variable acyclic (`acyclic?`, `(acyclic i)`), it, as
;; the binding it is (none or one).
(define k-acyclic-test (subr (maxeff kreads (alloc @t) spin) (kx) k-named)
  (lambda (p) (k-latent-cert p 0)))
;; If `p` certifies a variable a natural (`nat?`, `(nat i)`), it.
(define k-nat-test (subr (maxeff kreads (alloc @t) spin) (kx) k-named)
  (lambda (p) (k-latent-cert p 1)))
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
;; What `p` narrows where it holds (`car`) and where not (`cdr`): the Rust
;; checker's `narrowings`. Each narrowing (`check.rs`'s `Narrowed`): a
;; variable, its binding's depth, the steps of a path from it (none for the
;; variable), the regions they read through, and the type there. Through
;; `not`, and through `and` and `or` (`(if a b #f)`, `(if a #t b)`) as
;; `k-test-facts` goes.
(define-type k-nar (productof (1 symbol) (2 int) (3 k-steps) (4 k-regions) (5 int)))
(define-type k-nars (listof k-nar acyclic))
(define-type k-narrowing (pairof k-nars k-nars acyclic))
(define k-nars-append (subr (read @globals) (k-nars k-nars) k-nars)
  (lambda (xs ys)
    (if (null? xs) ys (the k-nars (cons (car xs) (k-nars-append (cdr xs) ys))))))
(define k-step=? (subr (read @globals) (k-step k-step) bool)
  (lambda (s u)
    (tagcase s
      (st-car () (tagcase u (st-car () #t) (else y #f)))
      (st-cdr () (tagcase u (st-cdr () #t) (else y #f)))
      (st-field (l) (tagcase u (st-field (m) (symbol=? l m)) (else y #f))))))
(define k-steps=? (subr (read @globals) (k-steps k-steps) bool)
  (lambda (xs ys)
    (if (null? xs)
        (null? ys)
        (and (not (null? ys)) (k-step=? (car xs) (car ys)) (k-steps=? (cdr xs) (cdr ys))))))
(define k-steps-snoc (subr (maxeff (read @globals) (alloc @t)) (k-steps k-step) k-steps)
  (lambda (xs s)
    (if (null? xs)
        (the k-steps (cons s nil))
        (the k-steps (cons (car xs) (k-steps-snoc (cdr xs) s))))))
;; `x` as a path from a variable: the variable, its binding's depth, and
;; the steps, `car`s, `cdr`s and products' fields (none or one).
(define-type k-path (productof (1 symbol) (2 int) (3 k-steps)))
(define-type k-paths (listof k-path acyclic))
(define k-path-step (subr (maxeff (read @globals) (alloc @t)) (k-paths k-step) k-paths)
  (lambda (ps s)
    (if (null? ps)
        (the k-paths nil)
        (let* ((p (car ps)) (steps (k-steps-snoc (extract p 3) s)))
          (the k-paths (cons (product (1 (extract p 1)) (2 (extract p 2)) (3 steps)) nil))))))
(define k-path-of (subr (maxeff kreads (alloc @t) spin) (kx) k-paths)
  (lambda (x)
    (tagcase x
      (x-var (v a b) (the k-paths (cons (product (1 v) (2 (k-binding-depth v)) (3 nil)) nil)))
      (x-app (f args a b)
        (let ((op (k-std-op f)))
          (if (and (k-sc-one-arg? args) (or (string=? op "car") (string=? op "cdr")))
              (k-path-step (k-path-of (car args)) (if (string=? op "car") (st-car) (st-cdr)))
              (the k-paths nil))))
      (x-extract (e l a b) (k-path-step (k-path-of e) (st-field l)))
      (else y (the k-paths nil)))))
;; The type the fact in force of the path from `v` at `d` by `steps` gives,
;; or -1.
(define k-path-fact-in (subr (maxeff kreads spin) (k-path-facts symbol int k-steps int) int)
  (lambda (fs v d steps depth)
    (cond ((null? fs) -1)
          ((let ((f (car fs)))
             (and (not (extract f 7)) (= (extract f 6) depth) (symbol=? (extract f 1) v)
                  (= (extract f 2) d) (k-steps=? (extract f 3) steps)))
           (extract (car fs) 5))
          (else (k-path-fact-in (cdr fs) v d steps depth)))))
(define k-path-fact-ty (subr (maxeff kreads spin) (symbol int k-steps) int)
  (lambda (v d steps) (k-path-fact-in (get k-path-narrowed) v d steps (get k-closure-depth))))
;; A type and the regions read to reach it (none or one).
(define-type k-reached (listof (productof (1 int) (2 k-regions)) acyclic))
(define k-reached-of (subr (alloc @t) (int k-regions) k-reached)
  (lambda (t rs) (the k-reached (cons (product (1 t) (2 rs)) nil))))
;; The path from `v` at `d`, `done` taken and `rest` to go, at type `t`
;; having read through `rs`: as the types say and the facts in force
;; narrow it (`check.rs`'s `path_type`).
(define k-path-walk
  (subr (maxeff kreads (alloc @t) spin) (symbol int k-steps k-steps int k-regions) k-reached)
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
(define k-path-type (subr (maxeff kreads (alloc @t) spin) (symbol int k-steps) k-reached)
  (lambda (v d steps)
    (let ((t (k-lookup v)))
      (if (< t 0) (the k-reached nil) (k-path-walk v d nil steps (k-resolve t) nil)))))
;; `x`'s type `t`, or, `x` a path a fact in force narrows, its type there.
(define k-path-ty (subr (maxeff kreads (alloc @t) spin) (kx int) int)
  (lambda (x t)
    (if (null? (get k-path-narrowed))
        t
        (let ((ps (k-path-of x)))
          (if (or (null? ps) (null? (extract (car ps) 3)))
              t
              (let* ((p (car ps)) (f (k-path-fact-ty (extract p 1) (extract p 2) (extract p 3))))
                (if (< f 0) t f)))))))
(define k-path-te (subr (maxeff kreads (alloc @t) spin) (kx k-te) k-te)
  (lambda (x te) (k-te (k-path-ty x (extract te 1)) (extract te 2))))
;; What `out` narrows the path from `v` at `d` by `steps` to (none or one).
(define k-nars-of (subr (maxeff kreads (alloc @t) spin) (k-nars symbol int k-steps) k-reached)
  (lambda (out v d steps)
    (cond ((null? out) (the k-reached nil))
          ((let ((n (car out)))
             (and (symbol=? (extract n 1) v) (= (extract n 2) d) (k-steps=? (extract n 3) steps)))
           (k-reached-of (extract (car out) 5) (extract (car out) 4)))
          (else (k-nars-of (cdr out) v d steps)))))
;; `out` with that path narrowed to `t`, in place of what it had.
(define k-nars-put
  (subr (maxeff (read @globals) (alloc @t) spin) (k-nars symbol int k-steps k-regions int) k-nars)
  (lambda (out v d steps rs t)
    (let ((one (product (1 v) (2 d) (3 steps) (4 rs) (5 t))))
      (cond ((null? out) (the k-nars (cons one nil)))
            ((let ((n (car out)))
               (and (symbol=? (extract n 1) v) (= (extract n 2) d) (k-steps=? (extract n 3) steps)))
             (the k-nars (cons one (cdr out))))
            (else (the k-nars (cons (car out) (k-nars-put (cdr out) v d steps rs t))))))))
;; The variables and paths among `args` narrowed by `props`, a conjunction:
;; each proposition of a shape, in turn.
(define k-props-narrow (subr (maxeff kstate spin) (k-props kxs k-nars) k-nars)
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
                           (to (if negated (extract split 2) (extract split 1))))
                      (k-props-narrow
                       (cdr props) args
                       (if (< to 0) out (k-nars-put out n d steps (extract (car tr) 2) to)))))))))))
;; A test: what its callee's type says it proves (`ty-proving`), of those of
;; its arguments that are variables or paths, where it holds and where not.
(define k-latent-narrowing (subr (maxeff kstate spin) (kx) k-narrowing)
  (lambda (p)
    (let ((l (k-latent-props p)))
      (if (null? l)
          (the k-narrowing (cons nil nil))
          (let ((x (car l)))
            (cons (k-props-narrow (extract x 1) (extract x 3) nil)
                  (k-props-narrow (extract x 2) (extract x 3) nil)))))))
(define k-narrowings (subr (maxeff kstate spin) (kx) k-narrowing)
  (lambda (p)
    (let ((none (the k-narrowing (cons nil nil))))
      (tagcase p
        (x-if (q c d a b)
          (let ((nq (k-narrowings q)))
            (cond ((k-bool-lit? c #t) (cons nil (k-nars-append (cdr nq) (cdr (k-narrowings d)))))
                  ((k-bool-lit? d #f) (cons (k-nars-append (car nq) (car (k-narrowings c))) nil))
                  (else none))))
        (x-app (f args a b)
          (if (and (string=? (k-std-op f) "not") (k-sc-one-arg? args))
              (let ((ns (k-narrowings (car args)))) (cons (cdr ns) (car ns)))
              (k-latent-narrowing p)))
        (else y none)))))
;; The variables' narrowings among `ns`, as `k-narrowed` keeps them.
(define k-var-narrows (subr (maxeff (read @globals) (alloc @t)) (k-nars) k-narrows)
  (lambda (ns)
    (cond ((null? ns) nil)
          ((null? (extract (car ns) 3))
           (let ((n (car ns)))
             (the k-narrows
                  (cons (product (1 (extract n 1)) (2 (extract n 2)) (3 (extract n 5)))
                        (k-var-narrows (cdr ns))))))
          (else (k-var-narrows (cdr ns))))))
;; The paths' narrowings among `ns` put in force, in turn.
(define k-push-paths (subr kstate (k-nars) unit)
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
(define k-put-narrowing (subr kstate (k-nars k-narrows) unit)
  (lambda (ns saved)
    (begin (set k-narrowed (k-narrows-append (k-var-narrows ns) saved)) (k-push-paths ns))))
(define k-drop-facts (subr (read @globals) (k-path-facts int) k-path-facts)
  (lambda (fs m) (if (or (<= m 0) (null? fs)) fs (k-drop-facts (cdr fs) (- m 1)))))
;; The paths' facts cut back to the `n` oldest, as they are now (one an
;; effect has ended since stays ended).
(define k-cut-paths (subr kstate (int) unit)
  (lambda (n)
    (let ((fs (get k-path-narrowed)))
      (set k-path-narrowed (k-drop-facts fs (- (k-length fs) n))))))
(define k-narrows-append (subr (read @globals) (k-narrows k-narrows) k-narrows)
  (lambda (xs ys)
    (if (null? xs) ys (the k-narrows (cons (car xs) (k-narrows-append (cdr xs) ys))))))
;; What effect `e`, of an expression just checked, ends of the paths' facts
;; at this closure depth (`check.rs`'s `kill_paths`): a write to a region
;; a path reads through, or to one that may be it (a region variable may be
;; any region), and any transfer of control or effect not known. A path
;; through frozen data, or products' fields alone, is never written.
(define k-may-alias? (subr (maxeff (read @globals) spin) (k-region k-region) bool)
  (lambda (w r)
    (or (k-region=? w r)
        (tagcase w (r-var (v) #t) (else y #f))
        (tagcase r (r-var (v) #t) (else y #f)))))
(define k-hits? (subr (maxeff (read @globals) spin) (k-region k-regions) bool)
  (lambda (w rs)
    (and (not (null? rs)) (or (k-may-alias? w (car rs)) (k-hits? w (cdr rs))))))
(define k-open-regions (subr (maxeff (read @globals) (alloc @t)) (k-regions) k-regions)
  (lambda (rs)
    (cond ((null? rs) nil)
          ((tagcase (car rs) (r-frozen (p f) #t) (else y #f)) (k-open-regions (cdr rs)))
          (else (the k-regions (cons (car rs) (k-open-regions (cdr rs))))))))
(define k-kills? (subr (maxeff (read @globals) spin) (k-eff k-regions) bool)
  (lambda (e open)
    (and (not (null? e))
         (or (tagcase (car e)
               (a-write (w) (k-hits? w open))
               (a-goto (r) #t) (a-comefrom (r) #t) (a-await (r) #t) (a-var (v) #t)
               (a-app (v ds) #t)
               (else y #f))
             (k-kills? (cdr e) open)))))
(define k-kill-each
  (subr (maxeff (read @globals) (alloc @t) spin) (k-path-facts k-eff int) k-path-facts)
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
(define k-all-dead? (subr (read @globals) (k-path-facts) bool)
  (lambda (fs) (or (null? fs) (and (extract (car fs) 7) (k-all-dead? (cdr fs))))))
(define k-kill-paths (subr (maxeff kstate spin) (k-eff) unit)
  (lambda (e)
    (let ((fs (get k-path-narrowed)))
      (if (k-all-dead? fs) #u (set k-path-narrowed (k-kill-each fs e (get k-closure-depth)))))))
;; What checking an `if`'s branches puts back as it goes: what was certified, the size
;; facts, and what was narrowed, before; what its test shows when it holds, and when not;
;; what it narrows so; and how many paths' facts there were.
(define-type k-tested
  (productof (1 k-certs) (2 k-fact-list) (3 k-branch-facts) (4 k-narrows) (5 k-narrowing)
             (6 int)))
;; Before the branch where `p` holds: what it certifies, and the facts it shows, in force.
(define k-enter-then (subr (maxeff kstate spin) (kx) k-tested)
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
(define k-enter-else (subr kstate (k-tested) unit)
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
(define k-leave-test (subr kstate (k-tested) unit)
  (lambda (t)
    (begin (set k-size-facts (extract t 2)) (set k-narrowed (extract t 4))
           (k-cut-paths (extract t 6)))))
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
;; `nil` (a variable of a list of any elements), argument `i`, where its
;; parameter `q`, `p` so far, is not yet known: the type `nil` (`TODO.md`
;; §48), heard last, after what the context expects and every other
;; argument; anything else, the error.
(define k-nil-told (subr (maxeff checks spin) (kx int int int k-binders k-solved k-done) unit)
  (lambda (arg i p q kinds solved done)
    (tagcase arg
      (x-var (s a b)
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
(define k-with-used (subr (maxeff kreads (alloc @t)) (k-parts k-names int)
                   (productof (1 k-parts) (2 k-ids)))
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
(define k-widen-nil-tail (subr (maxeff kstate spin) (int k-binders k-solved) unit)
  (lambda (result kinds solved)
    (tagcase (k-get (k-resolve result))
      (ty-pair (h tl r nl)
        (tagcase (k-get (k-resolve tl))
          (ty-var (v) (if (k-binder-has? kinds v) (k-widen-tail-at v h r kinds solved) #u))
          (else y #u)))
      (else y #u))))
(define k-widen-tail-at (subr (maxeff kstate spin) (int int k-region k-binders k-solved) unit)
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
        (let* ((ts (k-join-with-nil types)) (found (k-upper-bound ts ts)))
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
(define k-path-te (with check-synth-module k-path-te))
(define k-kill-paths (with check-synth-module k-kill-paths))
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
(define k-nil-told (with check-synth-module k-nil-told))
(define k-widen-nil-tail (with check-synth-module k-widen-nil-tail))
(define k-with-used (with check-synth-module k-with-used))
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
