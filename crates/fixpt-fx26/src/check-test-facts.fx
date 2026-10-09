;;; The checker, in FX-26: what a test says of sizes, in each branch of an
;;; `if` on a comparison, a `null?` or a length (`sizes.rs`).
;;; Part of the checker, `check-types.fx` first (PLAN.md §11, step 10).

;; Its types, those it uses of the files before it, and the signatures of
;; what it is given.
(let* ((check-test-facts-types (load-module "fx26:check-test-facts-types.fx"))
       (check-types-types (load-module "fx26:check-types-types.fx"))
       (check-subst-types (load-module "fx26:check-subst-types.fx"))
       (check-infer-types (load-module "fx26:check-infer-types.fx"))
       (check-binders-types (load-module "fx26:check-binders-types.fx"))
       (check-env-types (load-module "fx26:check-env-types.fx"))
       (check-terminate-types (load-module "fx26:check-terminate-types.fx"))
       (check-sc-graphs-types (load-module "fx26:check-sc-graphs-types.fx"))
       (check-print-types (load-module "fx26:check-print-types.fx"))
       (check-print-parts-types (load-module "fx26:check-print-parts-types.fx"))
       (check-calls-types (load-module "fx26:check-calls-types.fx")))
  ;; What it is given: the modules of the files before it that it uses.
  (lambda ((check-infer (select check-infer-types check-infer-sig))
           (check-types (select check-types-types check-types-sig))
           (check-env (select check-env-types check-env-sig))
           (check-terminate (select check-terminate-types check-terminate-sig))
           (check-print (select check-print-types check-print-sig))
           (check-calls (select check-calls-types check-calls-sig))
           (check-sc-graphs (select check-sc-graphs-types check-sc-graphs-sig))
           (check-binders (select check-binders-types check-binders-sig))
           (check-print-parts (select check-print-parts-types check-print-parts-sig)))
    (module
(define-type k-fact-list (select check-test-facts-types k-fact-list))
(define-type k-branch-facts (select check-test-facts-types k-branch-facts))
(define-type k-maybe-size (select check-test-facts-types k-maybe-size))
(define-type k-latent (select check-test-facts-types k-latent))
(define-type k-cert-lens (select check-test-facts-types k-cert-lens))
;; The types it uses of the files before it.
(define-type k-cert-len (select check-types-types k-cert-len))
(define-type k-named (select check-types-types k-named))
(define-type k-props (select check-types-types k-props))
(define-type k-size (select check-types-types k-size))
(define-type k-term (select check-types-types k-term))
(define-effect kreads (select check-types-types kreads))
(define-type kx (select check-types-types kx))
(define-type kxs (select check-types-types kxs))
(define pr-acyclic (with check-types-types pr-acyclic))
(define pr-length (with check-types-types pr-length))
(define pr-nat (with check-types-types pr-nat))
(define pr-rel (with check-types-types pr-rel))
(define sz-finite (with check-types-types sz-finite))
(define tm-length (with check-types-types tm-length))
(define tm-lit (with check-types-types tm-lit))
(define tm-param (with check-types-types tm-param))
(define ty-nat (with check-types-types ty-nat))
(define ty-nlist (with check-types-types ty-nlist))
(define ty-proving (with check-types-types ty-proving))
(define ty-subr (with check-types-types ty-subr))
(define x-app (with check-types-types x-app))
(define x-const (with check-types-types x-const))
(define x-var (with check-types-types x-var))
(define-effect kmakes (select check-subst-types kmakes))
;; What it uses of the modules it is given.
(define k-binders-of (with check-binders k-binders-of))
(define k-binding-depth (with check-binders k-binding-depth))
(define k-get (with check-types k-get))
(define k-resolve (with check-types k-resolve))
(define k-std-type (with check-types k-std-type))
(define k-int (with check-env k-int))
(define k-lookup (with check-env k-lookup))
(define k-op-either? (with check-sc-graphs k-op-either?))
(define k-size-add-scaled (with check-print-parts k-size-add-scaled))
(define k-size-as-lit (with check-print-parts k-size-as-lit))
(define k-size-lit (with check-print-parts k-size-lit))
(define k-size-nonneg? (with check-print-parts k-size-nonneg?))
(define k-size-plus (with check-print-parts k-size-plus))
(define k-size=? (with check-print-parts k-size=?))
(define k-std-op (with check-calls k-std-op))
(define k-under (with check-calls k-under))

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
                (else nil)))))))))
