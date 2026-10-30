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
       (check-calls-types (load-module "fx26:check-calls-types.fx"))
       (check-logic-types (load-module "fx26:check-logic-types.fx"))
       (check-resolve-types (load-module "fx26:check-resolve-types.fx")))
  ;; What it is given: the modules of the files before it that it uses.
  (lambda ((check-infer (select check-infer-types check-infer-sig))
           (check-types (select check-types-types check-types-sig))
           (check-env (select check-env-types check-env-sig))
           (check-terminate (select check-terminate-types check-terminate-sig))
           (check-print (select check-print-types check-print-sig))
           (check-calls (select check-calls-types check-calls-sig))
           (check-sc-graphs (select check-sc-graphs-types check-sc-graphs-sig))
           (check-binders (select check-binders-types check-binders-sig))
           (check-print-parts (select check-print-parts-types check-print-parts-sig))
           (check-logic (select check-logic-types check-logic-sig))
           (check-resolve (select check-resolve-types check-resolve-sig)))
    (module
(hide (include check-test-facts-types) (include check-types-types) (include check-subst-types))
;; The types it uses of the files before it.
;; What it uses of the modules it is given: all of each, hidden.
(hide (include check-binders) (include check-types) (include check-env) (include check-sc-graphs)
      (include check-print-parts) (include check-calls) (include check-logic))
(import check-resolve k-at-of k-start k-end)
(import check-env-types n-staged)

(define k-branch-facts-of (->* (k-fact-list k-fact-list) k-branch-facts)
  (lambda (yes no) (the k-branch-facts (cons yes no))))
;; The fact `lin ≥ 0`, or `lin = 0`, alone.
(define k-ge-fact (->* (k-size) k-fact-list)
  (lambda (lin) (the k-fact-list (cons (product (1 lin) (2 #f)) nil))))
(define k-eq-fact (->* (k-size) k-fact-list)
  (lambda (lin) (the k-fact-list (cons (product (1 lin) (2 #t)) nil))))
;; `x < y`, as `y - x - 1 ≥ 0`; `x ≤ y`, as `y - x ≥ 0`.
(define k-lt-fact (->* (k-size k-size) k-fact-list)
  (lambda (x y) (k-ge-fact (k-size-plus (k-size-add-scaled y x -1) -1))))
(define k-le-fact (->* (k-size k-size) k-fact-list)
  (lambda (x y) (k-ge-fact (k-size-add-scaled y x -1))))
;; Whether `z` is no size in particular: a plain `nat`'s.
(define k-size-any? (->* (k-size) bool)
  (lambda (z) (tagcase z (sz-finite () #t) (else w #f))))
(define k-one-size (->* (k-size) k-maybe-size) (lambda (z) (the k-maybe-size (cons z nil))))
;; The size of a natural of type `t`, if it is one (none or one).
(define k-nat-ty-size (->* (int) k-maybe-size)
  (lambda (t) (tagcase (k-get (k-resolve t)) (ty-nat (z) (k-one-size z)) (else y nil))))
;; The size an argument is, when a natural literal or a variable of type
;; `(nat s)` (none or one).
(define k-nat-size (->* (kx) k-maybe-size)
  (lambda (x)
    (tagcase x
      (x-const (ty k a b abk) (if (and (= ty k-int) (>= k 0)) (k-one-size (k-size-lit k)) nil))
      (x-var (v a b abk)
        (let ((t (k-lookup v)))
          (if (< t 0) nil (k-nat-ty-size t))))
      ;; A variable's array's length (`TODO.md` §77): its size, where known.
      (x-app (f args a b abk)
        (if (and (string=? (k-std-op f) "array-length") (= (k-length args) 1))
            (tagcase (car args)
              (x-var (v va vb vavbk) (let ((t (k-lookup v))) (if (< t 0) nil (k-array-size t))))
              (else y nil))
            nil))
      ;; A variable's flat array's length (`TODO.md` §77): its size, where it
      ;; is one array's, not `finite`.
      (x-bloblet (o i xs a b abk)
        (if (and (symbol=? o 'blobref-length) (= (k-length xs) 1))
            (tagcase (car xs)
              (x-var (v va vb vavbk)
                (let ((t (k-lookup v))) (if (< t 0) nil (k-blobref-array-size t))))
              (else y nil))
            nil))
      (else y nil))))
;; The length of an array of type `t`, where it is not `finite` (none or
;; one).
(define k-array-size (->* (int) k-maybe-size)
  (lambda (t)
    (tagcase (k-get (k-resolve t))
      (ty-array (e z r) (tagcase z (sz-finite () nil) (else y (k-one-size z))))
      (else y nil))))
;; Call `op` on `args`, its type and effect `te`, as arrays' lengths say
;; (`Checker::array_sized`): a `make-array` of a natural's length is an
;; array of that length.
(define k-array-sized (->* (string kxs k-te) k-te)
  (lambda (op args te)
    (cond ((and (string=? op "make-array") (= (k-length args) 2)) (k-array-of-length (car args) te))
          ((and (string=? op "rmake-array") (= (k-length args) 3))
           (k-array-of-length (car (cdr args)) te))
          (else te))))
(define k-array-of-length (->* (kx k-te) k-te)
  (lambda (n te)
    (let ((z (k-nat-size n)))
      (if (null? z)
          te
          (tagcase (k-get (k-resolve (extract te 1)))
            (ty-array (e nz r)
              (tagcase nz
                (sz-finite () (k-te (k-ty-new (ty-array e (car z) r)) (extract te 2)))
                (else y te)))
            (else y te))))))
;; `x`, of type and effect `te`, as arrays' lengths say, if a call; of a
;; call, and of `(the t x)`, which keeps a `make-array`'s length. And a
;; call of `native-procedure` (`TODO.md` §97), which makes a native
;; closure: the type stated is of the native convention, or `fx`. And
;; `stage`'s (`k-staged`).
(define k-sized (->* (kx k-te) k-te)
  (lambda (x te)
    (tagcase x
      (x-app (f args a b abk)
        (let ((op (k-std-op f)))
          (cond ((string=? op "native-procedure") (k-made-native te a b))
                ((k-stage-op? f) (k-staged args te))
                (else (k-array-sized op args te)))))
      (else y te))))
;; Whether `f` is `stage`'s operator, `(proj %stage E R)`.
(define k-stage-op? (->* (kx) bool)
  (lambda (f)
    (tagcase f
      (x-proj (body ds a b abk) (string=? (k-std-op body) "%stage"))
      (else y (string=? (k-std-op f) "%stage")))))
;; `stage` (`docs/research/eval.md`): `((proj %stage E R) m code)`, `m` a
;; module's name, its call's type `te`, `(sumof (ok (subr E () R)) …)`.
;; `m`'s type, `E` and `R` noted at the code, printed with no `define-type`
;; named, for the compilers to give the checker that runs then
;; (`n-staged`).
(define k-staged (->* (kxs k-te) k-te)
  (lambda (args te)
    (let ((m (car args)) (code (car (cdr args))))
      (tagcase m
        (x-var (n a b abk)
          (let ((mt (k-resolve (k-lookup n))))
            (tagcase (k-get mt)
              (ty-module (abs ds vs)
                (begin (k-note-staged (k-at-of code) mt (extract te 1)) te))
              (else y (k-fail (string-append "`stage` takes a module, not a "
                                             ((with check-print k-show-ty) mt))
                              a b)))))
        (else y (k-fail "`stage` takes a module by its name" (k-start m) (k-end m)))))))
(define k-note-staged (->* (k-at int int) unit)
  (lambda (at mt t)
    (tagcase (k-get (k-resolve t))
      (ty-sum (parts)
        (let ((ok (k-get (k-resolve (k-staged-ok parts)))))
          (tagcase ok
            (ty-subr (e ps r cv spc)
              (let* ((show (with check-print k-show-ty-whole))
                     (n (n-staged (show mt) (k-show-effect e) (show r))))
                (set k-extracts (cons (product (1 at) (2 n)) (get k-extracts)))))
            (else y #u))))
      (else y #u))))
;; The type of the `ok` of `stage`'s sum.
(define k-staged-ok (->* (k-parts) int)
  (lambda (ps)
    (cond ((null? ps) -1)
          ((symbol=? (extract (car ps) 1) 'ok) (extract (car ps) 2))
          (else (k-staged-ok (cdr ps))))))
(define k-made-native (->* (k-te int int) k-te)
  (lambda (te a b)
    (tagcase (k-get (extract te 1))
      (ty-subr (e ps res cv spc)
        (tagcase cv
          (cv-native () te)
          (cv-fx () te)
          (else z (k-fail (string-append "`native-procedure` makes a native procedure: "
                                         "state `(conv native)` in its type")
                          a b))))
      (else y (k-fail (string-append "`native-procedure` makes a procedure, of the type stated: "
                                     "`(the (subr …) (native-procedure c))`")
                      a b)))))
;; The length of the flat array a blobref of type `t` points to (generative
;; types 5 and 6), where it is one array's, not `finite` (none or one).
(define k-blobref-array-size (->* (int) k-maybe-size)
  (lambda (t)
    (tagcase (k-get (k-resolve t))
      (ty-named (g ds)
        (if (and (= g 5) (= (k-length ds) 2))
            (tagcase (car (cdr ds))
              (dt (f)
                (tagcase (k-get (k-resolve f))
                  (ty-named (h es)
                    (if (and (= h 6) (= (k-length es) 2))
                        (tagcase (car (cdr es))
                          (dz (z) (tagcase z (sz-finite () nil) (else y (k-one-size z))))
                          (else y nil))
                        nil))
                  (else y nil)))
              (else y nil))
            nil))
      (else y nil))))
;; What a specification says a test proves, which a branch on it trusts:
;; why a `lambda`, whose body is not checked to prove it, may not claim it,
;; or nothing.
(define k-claimed (->* (k-specs) string)
  (lambda (sp)
    (if (null? sp)
        ""
        (let* ((ens (extract (car sp) 4))
               (th (k-ensures-latent ens #t)) (el (k-ensures-latent ens #f)))
          (if (and (null? th) (null? el))
              ""
              (k-cat5 "what a test proves, " (k-show-props "then" th) " "
                      (k-show-props "else" el) ", a `lambda` is not checked to prove"))))))
(define k-latent-props (->* (kx) k-latent)
  (lambda (p)
    (tagcase p
      (x-app (f args a b abk)
        (let* ((g (k-under f)) (op (k-std-op g))
               (t (if (string=? op "")
                      (tagcase g (x-var (s sa sb sasbk) (k-lookup s)) (else y -1))
                      (k-std-type (string->symbol op)))))
          (if (< t 0)
              nil
              (tagcase (k-get (extract (k-binders-of t) 2))
                (ty-subr (e ps r cv spc)
                  (if (null? spc)
                      nil
                      (let* ((ens (extract (car spc) 4))
                             (th (k-ensures-latent ens #t)) (el (k-ensures-latent ens #f)))
                        (if (and (null? th) (null? el))
                            nil
                            (the k-latent (cons (product (1 th) (2 el) (3 args)) nil))))))
                (else y nil)))))
      (else y nil))))
;; Argument `i` of `args` (none or one).
(define k-arg-at (->* (kxs int) kxs)
  (lambda (args i)
    (cond ((null? args) nil)
          ((= i 0) (the kxs (cons (car args) nil)))
          (else (k-arg-at (cdr args) (- i 1))))))
;; The type of argument `i` of `args`, if a variable, or -1.
(define k-arg-type (->* (kxs int) int)
  (lambda (args i)
    (let ((x (k-arg-at args i)))
      (if (null? x) -1 (tagcase (car x) (x-var (v va vb vavbk) (k-lookup v)) (else y -1))))))
;; A term's size, of `args`, if known and not just `finite` (none or one):
;; an argument's as a natural, its `nlist`'s length, a natural.
(define k-term-size (->* (k-term kxs) k-maybe-size)
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
(define k-facts-then (->* (k-fact-list k-fact-list) k-fact-list)
  (lambda (xs ys) (if (null? xs) ys (the k-fact-list (cons (car xs) (k-facts-then (cdr xs) ys))))))
;; The fact relation `o` of sizes `xs` and `ys` is, if both are known:
;; `x < y`, `x ≤ y`, `x = y`, or `x ≠ y` of a natural and 0.
(define k-rel-fact
  (->* (int k-maybe-size k-maybe-size) k-fact-list)
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
(define k-rel-facts (->* (k-props kxs) k-fact-list)
  (lambda (props args)
    (if (null? props)
        nil
        (let ((here (tagcase (car props)
                      (pr-rel (o a b) (k-rel-fact o (k-term-size a args) (k-term-size b args)))
                      (else y (the k-fact-list nil)))))
          (k-facts-then here (k-rel-facts (cdr props) args))))))
;; What `p` shows of sizes where it holds and where not, as its callee's
;; type says.
(define k-latent-facts (->* (kx) k-branch-facts)
  (lambda (p)
    (let ((l (k-latent-props p)))
      (if (null? l)
          (k-branch-facts-of nil nil)
          (let* ((x (car l)) (args (extract x 3)))
            (k-branch-facts-of (k-rel-facts (extract x 1) args)
                               (k-rel-facts (extract x 2) args)))))))
;; Argument `i` of `args`, if a variable, as the binding it is (none or one).
(define k-arg-binding (->* (kxs int) k-named)
  (lambda (args i)
    (let ((x (k-arg-at args i)))
      (if (null? x)
          nil
          (tagcase (car x)
            (x-var (v va vb vavbk) (the k-named (cons (cons v (k-binding-depth v)) nil)))
            (else y nil))))))
(define k-cert-in (->* (k-props int kxs) k-named)
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
(define k-latent-cert (->* (kx int) k-named)
  (lambda (p which)
    (let ((l (k-latent-props p)))
      (if (null? l) nil (k-cert-in (extract (car l) 1) which (extract (car l) 3))))))
;; `v` and `k` of `(length-is? v k)` or `(certify-length v k)`: the
;; variable, its binding, and the length, a natural literal or a variable
;; of type `(nat s)` (none or one).
(define k-length-arg (->* (kx kx) k-cert-lens)
  (lambda (a n)
    (tagcase a
      (x-var (v va vb vavbk)
        (if (tagcase n (x-const (ty k ka kb kakbk) #t) (x-var (w wa wb wawbk) #t) (else y #f))
            (let ((z (k-nat-size n)))
              (if (null? z)
                  nil
                  (the k-cert-lens (cons (product (1 v) (2 (k-binding-depth v)) (3 (car z))) nil))))
            nil))
      (else y nil))))
;; Whether `c` and `d` confirm the same.
(define k-cert-len=? (->* (k-cert-len k-cert-len) bool)
  (lambda (c d)
    (and (symbol=? (extract c 1) (extract d 1))
         (= (extract c 2) (extract d 2))
         (k-size=? (extract c 3) (extract d 3)))))
(define k-cert-len-has? (->* (k-cert-lens k-cert-len) bool)
  (lambda (cs c)
    (and (not (null? cs))
         (or (k-cert-len=? (car cs) c) (k-cert-len-has? (cdr cs) c)))))
(define k-length-in (->* (k-props kxs) k-cert-lens)
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
(define k-length-test (->* (kx) k-cert-lens)
  (lambda (p)
    (let ((l (k-latent-props p)))
      (if (null? l) nil (k-length-in (extract (car l) 1) (extract (car l) 3))))))
;; Whether operation `n` may give a natural of a size by itself: `+`, `-` or a length.
(define k-sizing-op? (->* (string) bool)
  (lambda (n)
    (or (k-op-either? n "+" "-")
        (string=? n "length")
        (k-op-either? n "string-length" "array-length"))))
;; Whether `x` may be a natural of a size without being told what it is: an
;; integer literal, a variable, or a `+`, `-` or `length`.
(define k-natural-by-itself? (->* (kx) bool)
  (lambda (x)
    (tagcase x
      (x-const (ty k a b abk) (= ty k-int))
      (x-var (v a b abk) #t)
      (x-app (f args a b abk) (k-sizing-op? (k-std-op f)))
      (else y #f))))
;; The size an operand of `+` or `-` of type `t` is: a natural literal's,
;; or a `(nat s)`'s (none or one).
(define k-operand-size (->* (kx int) k-maybe-size)
  (lambda (x t)
    (let ((lit (tagcase x
                 (x-const (ty k a b abk) (if (and (= ty k-int) (>= k 0)) k -1))
                 (else y -1))))
      (if (>= lit 0) (k-one-size (k-size-lit lit)) (k-nat-ty-size t)))))
;; `(+ a b)` and `(- a b)` of naturals of sizes `za` and `zb`, where known: the sum, and the
;; difference where the facts show it no less than 0 (none or one).
(define k-nat-arith-size (->* (string k-maybe-size k-maybe-size) k-maybe-size)
  (lambda (op za zb)
    (if (or (null? za) (null? zb))
        nil
        (let ((a (car za)) (b (car zb)))
          (cond ((string=? op "+") (k-one-size (k-size-add-scaled a b 1)))
                ((and (not (k-size-any? a)) (k-size-nonneg? (k-size-add-scaled a b -1)))
                 (k-one-size (k-size-add-scaled a b -1)))
                (else nil)))))))))
