;;; The checker, in FX-26: what a test says of sizes, in each branch of an
;;; `if` on a comparison, a `null?` or a length (`sizes.rs`).
;;; Part of the checker, `check-types.fx` first (PLAN.md §11, step 10).

;; A module (`TODO.md` §34: the front end into modules, a file at a time);
;; what other files use re-exported after it.
(define check-test-facts-module (module
;; What a test shows when it holds, and when not.
(define-type k-fact-list (listof k-size-fact acyclic))
(define-type k-branch-facts (pairof k-fact-list k-fact-list acyclic))
(define k-branch-facts-of (subr pure (k-fact-list k-fact-list) k-branch-facts)
  (lambda (yes no) (the k-branch-facts (cons yes no))))
;; The fact `lin ≥ 0`, or `lin = 0`, alone.
(define k-ge-fact (subr pure (k-size) k-fact-list)
  (lambda (lin) (the k-fact-list (cons (product (1 lin) (2 #f)) nil))))
(define k-eq-fact (subr pure (k-size) k-fact-list)
  (lambda (lin) (the k-fact-list (cons (product (1 lin) (2 #t)) nil))))
;; `x < y`, as `y - x - 1 ≥ 0`; `x ≤ y`, as `y - x ≥ 0`.
(define k-lt-fact (subr (read @globals) (k-size k-size) k-fact-list)
  (lambda (x y) (k-ge-fact (k-size-plus (k-size-add-scaled y x -1) -1))))
(define k-le-fact (subr (read @globals) (k-size k-size) k-fact-list)
  (lambda (x y) (k-ge-fact (k-size-add-scaled y x -1))))
;; A size, or none: none or one.
(define-type k-maybe-size (listof k-size acyclic))
;; Whether `z` is no size in particular: a plain `nat`'s.
(define k-size-any? (subr pure (k-size) bool)
  (lambda (z) (tagcase z (sz-finite () #t) (else w #f))))
(define k-one-size (subr pure (k-size) k-maybe-size) (lambda (z) (the k-maybe-size (cons z nil))))
;; The size of a natural of type `t`, if it is one (none or one).
(define k-nat-ty-size (subr (maxeff kreads spin) (int) k-maybe-size)
  (lambda (t) (tagcase (k-get (k-resolve t)) (ty-nat (z) (k-one-size z)) (else y nil))))
;; The size an argument is, when a natural literal or a variable of type
;; `(nat s)` (none or one).
(define k-nat-size (subr (maxeff kreads spin) (kx) k-maybe-size)
  (lambda (x)
    (tagcase x
      (x-const (ty k a b) (if (and (= ty k-int) (>= k 0)) (k-one-size (k-size-lit k)) nil))
      (x-var (v a b)
        (let ((t (k-lookup v)))
          (if (< t 0) nil (k-nat-ty-size t))))
      (else y nil))))
;; `xs : (nlist T n)` shows `n = 0` when null, and `n - 1 ≥ 0` when not.
(define k-null-facts (subr (maxeff (read @globals) (read @t) (alloc @t) spin) (kx) k-branch-facts)
  (lambda (x)
    (let ((none (k-branch-facts-of nil nil))
          (vt (tagcase x (x-var (v va vb) (k-lookup v)) (else y -1))))
      (if (< vt 0)
          none
          (tagcase (k-get vt)
            (ty-nlist (e z r)
              (tagcase z
                (sz-lin (k ts) (k-branch-facts-of (k-eq-fact z) (k-ge-fact (k-size-plus z -1))))
                (else w none)))
            (else w none))))))
;; What a comparison `(op a b)` of naturals shows, when both have sizes.
(define k-compare-facts (subr (maxeff kreads (alloc @t) spin) (string kx kx) k-branch-facts)
  (lambda (op a b)
    (let ((xs (k-nat-size a)) (ys (k-nat-size b)) (none (k-branch-facts-of nil nil)))
      (if (or (null? xs) (null? ys) (k-size-any? (car xs)) (k-size-any? (car ys)))
          none
          (let ((x (car xs)) (y (car ys)))
            (case op (("<") (k-branch-facts-of (k-lt-fact x y) (k-le-fact y x)))
                     (("<=") (k-branch-facts-of (k-le-fact x y) (k-lt-fact y x)))
                     ((">") (k-branch-facts-of (k-lt-fact y x) (k-le-fact x y)))
                     ((">=") (k-branch-facts-of (k-le-fact y x) (k-lt-fact x y)))
                     (else
                      (let ((no (cond ((= (k-size-as-lit y) 0) (k-ge-fact (k-size-plus x -1)))
                                      ((= (k-size-as-lit x) 0) (k-ge-fact (k-size-plus y -1)))
                                      (else (the k-fact-list nil)))))
                        (k-branch-facts-of (k-eq-fact (k-size-add-scaled x y -1)) no)))))))))
(define-type k-cert-lens (listof k-cert-len acyclic))
;; `v` and `k` of `(length-is? v k)` or `(certify-length v k)`: the
;; variable, its binding, and the length, a natural literal or a variable
;; of type `(nat s)` (none or one).
(define k-length-arg (subr (maxeff kreads (alloc @t) spin) (kx kx) k-cert-lens)
  (lambda (a n)
    (tagcase a
      (x-var (v va vb)
        (if (tagcase n (x-const (ty k ka kb) #t) (x-var (w wa wb) #t) (else y #f))
            (let ((z (k-nat-size n)))
              (if (null? z)
                  nil
                  (the k-cert-lens (cons (product (1 v) (2 (k-binding-depth v)) (3 (car z))) nil))))
            nil))
      (else y nil))))
;; Whether `c` and `d` confirm the same.
(define k-cert-len=? (subr kreads (k-cert-len k-cert-len) bool)
  (lambda (c d)
    (and (symbol=? (extract c 1) (extract d 1))
         (= (extract c 2) (extract d 2))
         (k-size=? (extract c 3) (extract d 3)))))
(define k-cert-len-has? (subr kreads (k-cert-lens k-cert-len) bool)
  (lambda (cs c)
    (and (not (null? cs))
         (or (k-cert-len=? (car cs) c) (k-cert-len-has? (cdr cs) c)))))
;; If `p` is `(length-is? v k)`, the variable, its binding, and the length.
(define k-length-test (subr (maxeff kreads (alloc @t) spin) (kx) k-cert-lens)
  (lambda (p)
    (tagcase p
      (x-app (f args a b)
        (if (and (string=? (k-std-op f) "length-is?") (k-sc-two? args))
            (k-length-arg (car args) (car (cdr args)))
            nil))
      (else y nil))))
;; Whether operation `n` may give a natural of a size by itself: `+`, `-` or a length.
(define k-sizing-op? (subr (read @globals) (string) bool)
  (lambda (n)
    (or (k-op-either? n "+" "-")
        (string=? n "length")
        (k-op-either? n "string-length" "array-length"))))
;; Whether `x` may be a natural of a size without being told what it is: an
;; integer literal, a variable, or a `+`, `-` or `length`.
(define k-natural-by-itself? (subr (maxeff (read @globals) (read @t) spin) (kx) bool)
  (lambda (x)
    (tagcase x
      (x-const (ty k a b) (= ty k-int))
      (x-var (v a b) #t)
      (x-app (f args a b) (k-sizing-op? (k-std-op f)))
      (else y #f))))
;; The size an operand of `+` or `-` of type `t` is: a natural literal's,
;; or a `(nat s)`'s (none or one).
(define k-operand-size (subr (maxeff kreads spin) (kx int) k-maybe-size)
  (lambda (x t)
    (let ((lit (tagcase x (x-const (ty k a b) (if (and (= ty k-int) (>= k 0)) k -1)) (else y -1))))
      (if (>= lit 0) (k-one-size (k-size-lit lit)) (k-nat-ty-size t)))))
;; `(+ a b)` and `(- a b)` of naturals of sizes `za` and `zb`, where known: the sum, and the
;; difference where the facts show it no less than 0 (none or one).
(define k-nat-arith-size (subr kreads (string k-maybe-size k-maybe-size) k-maybe-size)
  (lambda (op za zb)
    (if (or (null? za) (null? zb))
        nil
        (let ((a (car za)) (b (car zb)))
          (cond ((string=? op "+") (k-one-size (k-size-add-scaled a b 1)))
                ((and (not (k-size-any? a)) (k-size-nonneg? (k-size-add-scaled a b -1)))
                 (k-one-size (k-size-add-scaled a b -1)))
                (else nil))))))
;; Whether `n` is a comparison: `<`, `<=`, `>`, `>=` or `=`.
(define k-comparison? (subr (read @globals) (string) bool)
  (lambda (n) (or (k-op-either? n "<" "<=") (k-op-either? n ">" ">=") (string=? n "="))))
;; What a test `(name args …)`, `name` standard, shows about sizes.
(define k-std-test-facts (subr (maxeff kreads (alloc @t) spin) (string kxs) k-branch-facts)
  (lambda (name args)
    (let ((none (k-branch-facts-of nil nil)))
      (cond ((string=? name "null?") (if (k-sc-one-arg? args) (k-null-facts (car args)) none))
            ((and (k-comparison? name) (k-sc-two? args))
             (k-compare-facts name (car args) (car (cdr args))))
            (else none)))))))

(define-type k-fact-list (select check-test-facts-module k-fact-list))
(define-type k-branch-facts (select check-test-facts-module k-branch-facts))
(define k-branch-facts-of (with check-test-facts-module k-branch-facts-of))
(define-type k-maybe-size (select check-test-facts-module k-maybe-size))
(define k-size-any? (with check-test-facts-module k-size-any?))
(define-type k-cert-lens (select check-test-facts-module k-cert-lens))
(define k-length-arg (with check-test-facts-module k-length-arg))
(define k-cert-len-has? (with check-test-facts-module k-cert-len-has?))
(define k-length-test (with check-test-facts-module k-length-test))
(define k-natural-by-itself? (with check-test-facts-module k-natural-by-itself?))
(define k-operand-size (with check-test-facts-module k-operand-size))
(define k-nat-arith-size (with check-test-facts-module k-nat-arith-size))
(define k-std-test-facts (with check-test-facts-module k-std-test-facts))
