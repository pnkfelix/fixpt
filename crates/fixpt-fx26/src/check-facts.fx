;;; What a test shows about sizes, when it holds and when not: the Rust
;;; checker's `test_facts`, rule for rule.

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
          (tagcase f
            (x-var (op fa fb)
              (cond ((not (k-std? op)) none)
                    ((and (string=? (symbol->string op) "not") (k-sc-one-arg? args))
                     (let ((fs (k-test-facts (car args)))) (k-branch-facts-of (cdr fs) (car fs))))
                    (else (k-std-test-facts (symbol->string op) args))))
            (else y none)))
        (else y none)))))
;; `fs`, in order, onto `acc`, newest first: as the Rust checker's
;; `size_facts.extend`.
(define k-with-facts (subr (read @globals) (k-fact-list k-fact-list) k-fact-list)
  (lambda (fs acc)
    (if (null? fs) acc (k-with-facts (cdr fs) (the k-fact-list (cons (car fs) acc))))))
