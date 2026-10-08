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
;; If `p` is a call of a procedure whose type's result is `(bool (then …)
;; (else …))`, what it proves where true and where false, and its arguments
;; (none or one): the Rust checker's `latent_props`.
(define-type k-latent (listof (productof (1 k-props) (2 k-props) (3 kxs)) acyclic))
(define k-latent-props (subr (maxeff kmakes spin) (kx) k-latent)
  (lambda (p)
    (tagcase p
      (x-app (f args a b)
        (let* ((g (k-under f)) (op (k-std-op g))
               (t (if (string=? op "")
                      (tagcase g (x-var (s sa sb) (k-lookup s)) (else y -1))
                      (k-std-type (string->symbol op)))))
          (if (< t 0)
              nil
              (tagcase (k-get (extract (k-binders-of t) 2))
                (ty-subr (e ps r cv)
                  (tagcase (k-get r)
                    (ty-proving (th el)
                      (the k-latent (cons (product (1 th) (2 el) (3 args)) nil)))
                    (else y nil)))
                (else y nil)))))
      (else y nil))))
;; Argument `i` of `args` (none or one).
(define k-arg-at (subr (read @globals) (kxs int) kxs)
  (lambda (args i)
    (cond ((null? args) nil)
          ((= i 0) (the kxs (cons (car args) nil)))
          (else (k-arg-at (cdr args) (- i 1))))))
;; The type of argument `i` of `args`, if a variable, or -1.
(define k-arg-type (subr (maxeff kreads spin) (kxs int) int)
  (lambda (args i)
    (let ((x (k-arg-at args i)))
      (if (null? x) -1 (tagcase (car x) (x-var (v va vb) (k-lookup v)) (else y -1))))))
;; A term's size, of `args`, if known and not just `finite` (none or one):
;; an argument's as a natural, its `nlist`'s length, a natural.
(define k-term-size (subr (maxeff kreads (alloc @t) spin) (k-term kxs) k-maybe-size)
  (lambda (t args)
    (let ((z (tagcase t
               (tm-lit (k) (k-one-size (k-size-lit k)))
               (tm-param (i)
                 (let ((x (k-arg-at args i)))
                   (if (null? x) (the k-maybe-size nil) (k-nat-size (car x)))))
               (tm-length (i)
                 (let ((vt (k-arg-type args i)))
                   (if (< vt 0)
                       (the k-maybe-size nil)
                       (tagcase (k-get (k-resolve vt))
                         (ty-nlist (e z r) (k-one-size z))
                         (else y (the k-maybe-size nil)))))))))
      (if (or (null? z) (k-size-any? (car z))) nil z))))
(define k-facts-then (subr (read @globals) (k-fact-list k-fact-list) k-fact-list)
  (lambda (xs ys) (if (null? xs) ys (the k-fact-list (cons (car xs) (k-facts-then (cdr xs) ys))))))
;; The fact relation `o` of sizes `xs` and `ys` is, if both are known:
;; `x < y`, `x ≤ y`, `x = y`, or `x ≠ y` of a natural and 0.
(define k-rel-fact
  (subr (maxeff kreads (alloc @t) spin) (int k-maybe-size k-maybe-size) k-fact-list)
  (lambda (o xs ys)
    (if (or (null? xs) (null? ys))
        nil
        (let ((x (car xs)) (y (car ys)))
          (case o
            ((0) (k-lt-fact x y))
            ((1) (k-le-fact x y))
            ((2) (k-eq-fact (k-size-add-scaled x y -1)))
            (else (cond ((= (k-size-as-lit y) 0) (k-ge-fact (k-size-plus x -1)))
                        ((= (k-size-as-lit x) 0) (k-ge-fact (k-size-plus y -1)))
                        (else nil))))))))
;; The size facts relations `props` are, of `args` (`sizes.rs`'s `rel_facts`).
(define k-rel-facts (subr (maxeff kreads (alloc @t) spin) (k-props kxs) k-fact-list)
  (lambda (props args)
    (if (null? props)
        nil
        (let ((here (tagcase (car props)
                      (pr-rel (o a b) (k-rel-fact o (k-term-size a args) (k-term-size b args)))
                      (else y (the k-fact-list nil)))))
          (k-facts-then here (k-rel-facts (cdr props) args))))))
;; What `p` shows of sizes where it holds and where not, as its callee's
;; type says.
(define k-latent-facts (subr (maxeff kmakes spin) (kx) k-branch-facts)
  (lambda (p)
    (let ((l (k-latent-props p)))
      (if (null? l)
          (k-branch-facts-of nil nil)
          (let* ((x (car l)) (args (extract x 3)))
            (k-branch-facts-of (k-rel-facts (extract x 1) args)
                               (k-rel-facts (extract x 2) args)))))))
;; Argument `i` of `args`, if a variable, as the binding it is (none or one).
(define k-arg-binding (subr (maxeff kreads (alloc @t) spin) (kxs int) k-named)
  (lambda (args i)
    (let ((x (k-arg-at args i)))
      (if (null? x)
          nil
          (tagcase (car x)
            (x-var (v va vb) (the k-named (cons (cons v (k-binding-depth v)) nil)))
            (else y nil))))))
(define k-cert-in (subr (maxeff kreads (alloc @t) spin) (k-props int kxs) k-named)
  (lambda (ps which args)
    (if (null? ps)
        nil
        (let* ((i (tagcase (car ps)
                    (pr-acyclic (i) (if (= which 0) i -1))
                    (pr-nat (i) (if (= which 1) i -1))
                    (else y -1)))
               (v (if (< i 0) (the k-named nil) (k-arg-binding args i))))
          (if (null? v) (k-cert-in (cdr ps) which args) v)))))
;; What `p` certifies where it holds, as its callee's type says: the first
;; `(acyclic i)` (`which` 0) or `(nat i)` (1) of its, as the binding it is.
(define k-latent-cert (subr (maxeff kmakes spin) (kx int) k-named)
  (lambda (p which)
    (let ((l (k-latent-props p)))
      (if (null? l) nil (k-cert-in (extract (car l) 1) which (extract (car l) 3))))))
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
(define k-length-in (subr (maxeff kreads (alloc @t) spin) (k-props kxs) k-cert-lens)
  (lambda (ps args)
    (if (null? ps)
        nil
        (let ((found (tagcase (car ps)
                       (pr-length (i j)
                         (let ((a (k-arg-at args i)) (n (k-arg-at args j)))
                           (if (or (null? a) (null? n))
                               (the k-cert-lens nil)
                               (k-length-arg (car a) (car n)))))
                       (else y (the k-cert-lens nil)))))
          (if (null? found) (k-length-in (cdr ps) args) found)))))
;; What `p` certifies of a length where it holds, as its callee's type
;; says (`(length i j)`, `length-is?`): the variable, its binding, and the
;; length (none or one).
(define k-length-test (subr (maxeff kmakes spin) (kx) k-cert-lens)
  (lambda (p)
    (let ((l (k-latent-props p)))
      (if (null? l) nil (k-length-in (extract (car l) 1) (extract (car l) 3))))))
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
                (else nil))))))))

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
(define k-latent-props (with check-test-facts-module k-latent-props))
(define k-arg-at (with check-test-facts-module k-arg-at))
(define k-latent-facts (with check-test-facts-module k-latent-facts))
(define k-latent-cert (with check-test-facts-module k-latent-cert))
