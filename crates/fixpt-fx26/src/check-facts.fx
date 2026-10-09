;;; What a test shows about sizes, when it holds and when not: the Rust
;;; checker's `test_facts`, rule for rule.

;; Its types, those it uses of the files before it, and the signatures of
;; what it is given.
(let* ((check-test-facts-types (load-module "fx26:check-test-facts-types.fx"))
       (check-types-types (load-module "fx26:check-types-types.fx"))
       (check-env-types (load-module "fx26:check-env-types.fx"))
       (check-infer-types (load-module "fx26:check-infer-types.fx"))
       (check-binders-types (load-module "fx26:check-binders-types.fx"))
       (check-calls-types (load-module "fx26:check-calls-types.fx")))
  ;; What it is given: the modules of the files before it that it uses.
  (lambda ((check-env (select check-env-types check-env-sig))
           (check-test-facts (select check-test-facts-types check-test-facts-sig))
           (check-infer (select check-infer-types check-infer-sig))
           (check-calls (select check-calls-types check-calls-sig))
           (check-binders (select check-binders-types check-binders-sig)))
    (module

;; The types it uses of the files before it.
(define-type k-branch-facts (select check-test-facts-types k-branch-facts))
(define-type k-fact-list (select check-test-facts-types k-fact-list))
(define-effect kreads (select check-types-types kreads))
(define-type kx (select check-types-types kx))
(define x-app (with check-types-types x-app))
(define x-const (with check-types-types x-const))
(define x-if (with check-types-types x-if))
;; What it uses of the modules it is given.
(define k-bool (with check-env k-bool))
(define k-branch-facts-of (with check-test-facts k-branch-facts-of))
(define k-latent-facts (with check-test-facts k-latent-facts))
(define k-sc-one-arg? (with check-binders k-sc-one-arg?))
(define k-std-op (with check-calls k-std-op))

  ;; Whether `x` is the literal boolean `v`.
  (define k-bool-lit? (subr (read @globals) (kx bool) bool)
    (lambda (x v) (tagcase x (x-const (t n a b) (and (= t k-bool) (= n (if v 1 0)))) (else y #f))))
  (define k-facts-append (subr (read @globals) (k-fact-list k-fact-list) k-fact-list)
    (lambda (xs ys)
      (if (null? xs) ys (the k-fact-list (cons (car xs) (k-facts-append (cdr xs) ys))))))
  ;; What `p` shows about sizes when it holds, and when not. `(null? xs)`,
  ;; `xs : (nlist T n)`: `n = 0`, or `n - 1 ≥ 0`. A comparison of naturals:
  ;; `(< a b)`, `b - a - 1 ≥ 0`, or `a - b ≥ 0`; `(= a 0)`, `a = 0`, or, a
  ;; natural not 0, `a - 1 ≥ 0`. An `or`, `(if a #t b)`, shows when it does
  ;; not hold what `a` and `b` both show so; an `and`, `(if a b #f)`, when it
  ;; holds what both show then; `(not x)` what `x` shows, swapped. Only these
  ;; conjunctions: what an `or` shows when it holds is a disjunction, which
  ;; facts cannot say (that waits on logical types, PLAN.md Q7).
  (define k-test-facts (subr (maxeff kreads (alloc @t) spin) (kx) k-branch-facts)
    (lambda (p)
      (let ((none (k-branch-facts-of nil nil)))
        (tagcase p
          (x-if (q c d a b)
            (let ((fq (k-test-facts q)))
              (cond ((k-bool-lit? c #t)
                     (k-branch-facts-of nil (k-facts-append (cdr fq) (cdr (k-test-facts d)))))
                    ((k-bool-lit? d #f)
                     (k-branch-facts-of (k-facts-append (car fq) (car (k-test-facts c))) nil))
                    (else none))))
          (x-app (f args a b)
            (let ((op (k-std-op f)))
              (if (and (string=? op "not") (k-sc-one-arg? args))
                  (let ((fs (k-test-facts (car args)))) (k-branch-facts-of (cdr fs) (car fs)))
                  ;; What the callee's type says it proves of sizes.
                  (k-latent-facts p))))
          (else y none)))))
  ;; `fs`, in order, onto `acc`, newest first: as the Rust checker's
  ;; `size_facts.extend`.
  (define k-with-facts (subr (read @globals) (k-fact-list k-fact-list) k-fact-list)
    (lambda (fs acc)
      (if (null? fs) acc (k-with-facts (cdr fs) (the k-fact-list (cons (car fs) acc)))))))))
