;;; The checker, in FX-26: specifications' propositions (`logic.rs`), shown,
;;; compared, and the prover both checkers ask of them: whether one
;;; procedure's specification is within another's (behavioural subtyping).
;;; Step for step as `logic.rs`'s, atoms numbered as it numbers them, so
;;; that the two checkers decide alike. After `check-print-parts.fx`, whose
;;; sizes and Fourier–Motzkin elimination it reckons with.

;; Its types, those it uses of the files before it, and the signatures of
;; what it is given.
(let* ((check-types-types (load-module "fx26:check-types-types.fx"))
       (check-print-types (load-module "fx26:check-print-types.fx"))
       (check-print-parts-types (load-module "fx26:check-print-parts-types.fx")))
  ;; What it is given: the modules of the files before it that it uses.
  (lambda ((check-types (select check-types-types check-types-sig))
           (check-print-parts (select check-print-parts-types check-print-parts-sig)))
    (module
;; The types it uses of the files before it.
(hide (include check-types-types) (include check-print-types))
;; What it uses of the modules it is given: all of each, hidden.
(hide (include check-types) (include check-print-parts))

;;; ------------------------------------------------------------ alike

(define k-sx=? (->* (k-sx k-sx) bool)
  (lambda (a b)
    (tagcase a
      (sx-param (i) (tagcase b (sx-param (j) (= i j)) (else z #f)))
      (sx-result () (tagcase b (sx-result () #t) (else z #f)))
      (sx-lit (i) (tagcase b (sx-lit (j) (= i j)) (else z #f)))
      (sx-add (x y) (tagcase b (sx-add (u v) (and (k-sx=? x u) (k-sx=? y v))) (else z #f)))
      (sx-sub (x y) (tagcase b (sx-sub (u v) (and (k-sx=? x u) (k-sx=? y v))) (else z #f)))
      (sx-mul (x y) (tagcase b (sx-mul (u v) (and (k-sx=? x u) (k-sx=? y v))) (else z #f)))
      (sx-length (i) (tagcase b (sx-length (j) (= i j)) (else z #f)))
      (sx-shape (i k) (tagcase b (sx-shape (j l) (and (= i j) (= k l))) (else z #f)))
      (sx-acyclic (i) (tagcase b (sx-acyclic (j) (= i j)) (else z #f)))
      (sx-nat (i) (tagcase b (sx-nat (j) (= i j)) (else z #f)))
      (sx-length-is (i k) (tagcase b (sx-length-is (j l) (and (= i j) (= k l))) (else z #f)))
      (sx-call (f xs)
        (tagcase b (sx-call (g ys) (and (symbol=? f g) (k-sxs=? xs ys))) (else z #f))))))
(define k-sxs=? (->* (k-sxs k-sxs) bool)
  (lambda (xs ys)
    (if (null? xs)
        (null? ys)
        (and (not (null? ys)) (k-sx=? (car xs) (car ys)) (k-sxs=? (cdr xs) (cdr ys))))))
(define k-sf=? (->* (k-sf k-sf) bool)
  (lambda (p q)
    (tagcase p
      (sf-true () (tagcase q (sf-true () #t) (else z #f)))
      (sf-false () (tagcase q (sf-false () #t) (else z #f)))
      (sf-rel (r x y)
        (tagcase q (sf-rel (s u v) (and (= r s) (k-sx=? x u) (k-sx=? y v))) (else z #f)))
      (sf-holds (a) (tagcase q (sf-holds (b) (k-sx=? a b)) (else z #f)))
      (sf-not (a) (tagcase q (sf-not (b) (k-sf=? a b)) (else z #f)))
      (sf-and (ps) (tagcase q (sf-and (qs) (k-sfs=? ps qs)) (else z #f)))
      (sf-or (ps) (tagcase q (sf-or (qs) (k-sfs=? ps qs)) (else z #f)))
      (sf-implies (a b)
        (tagcase q (sf-implies (c d) (and (k-sf=? a c) (k-sf=? b d))) (else z #f))))))
(define k-sfs=? (->* (k-sfs k-sfs) bool)
  (lambda (ps qs)
    (if (null? ps)
        (null? qs)
        (and (not (null? qs)) (k-sf=? (car ps) (car qs)) (k-sfs=? (cdr ps) (cdr qs))))))
(define k-sf-in? (->* (k-sf k-sfs) bool)
  (lambda (p qs) (and (not (null? qs)) (or (k-sf=? p (car qs)) (k-sf-in? p (cdr qs))))))
(define k-symbols=? (->* (k-names k-names) bool)
  (lambda (xs ys)
    (if (null? xs)
        (null? ys)
        (and (not (null? ys)) (symbol=? (car xs) (car ys)) (k-symbols=? (cdr xs) (cdr ys))))))
;; Two specifications alike, their names too (`ast::Spec`'s equality).
(define k-specs=? (->* (k-specs k-specs) bool)
  (lambda (a b)
    (if (null? a)
        (null? b)
        (and (not (null? b))
             (let ((x (car a)) (y (car b)))
               (and (k-symbols=? (extract x 1) (extract y 1)) (symbol=? (extract x 2) (extract y 2))
                    (k-sf=? (extract x 3) (extract y 3)) (k-sf=? (extract x 4) (extract y 4))))))))
;; Whether `f` says nothing: `#t`, or a conjunction of nothing else.
(define k-sf-trivial? (->* (k-sf) bool)
  (lambda (f) (tagcase f (sf-true () #t) (sf-and (ps) (k-sfs-trivial? ps)) (else z #f))))
(define k-sfs-trivial? (->* (k-sfs) bool)
  (lambda (ps) (or (null? ps) (and (k-sf-trivial? (car ps)) (k-sfs-trivial? (cdr ps))))))

;;; ------------------------------------------------------------ shown

;; A parameter's name: as named, else `$i`.
(define k-spec-param (->* (k-spec int) string)
  (lambda (spec i)
    (let ((n (if (< i (k-length (extract spec 1))) (k-nth (extract spec 1) i) '||)))
      (if (symbol=? n '||) (string-append "$" (int->string i)) (symbol->string n)))))
;; An atom's name: a parameter's, the result's (as named, else `result`),
;; or what a test proves, of parameters named.
(define k-spec-name (->* (k-spec k-sx) string)
  (lambda (spec a)
    (tagcase a
      (sx-param (i) (k-spec-param spec i))
      (sx-length (i) (k-cat3 "(length " (k-spec-param spec i) ")"))
      (sx-shape (i k) (k-cat5 "(shape " (k-spec-param spec i) " " (k-shape-name k) ")"))
      (sx-acyclic (i) (k-cat3 "(acyclic " (k-spec-param spec i) ")"))
      (sx-nat (i) (k-cat3 "(nat " (k-spec-param spec i) ")"))
      (sx-length-is (i j)
        (k-cat5 "(length-is " (k-spec-param spec i) " " (k-spec-param spec j) ")"))
      (sx-call (f xs) (k-cat3 "(" (symbol->string f) (string-append (k-show-args spec xs) ")")))
      (else z
        (if (symbol=? (extract spec 2) '||) "result" (symbol->string (extract spec 2)))))))
(define k-show-sx (->* (k-spec k-sx) string)
  (lambda (spec x)
    (tagcase x
      (sx-lit (k) (int->string k))
      (sx-add (a b) (k-show-op spec "+ " a b))
      (sx-sub (a b) (k-show-op spec "- " a b))
      (sx-mul (a b) (k-show-op spec "* " a b))
      (else z (k-spec-name spec x)))))
;; Each of `xs`, after a space.
(define k-show-args (->* (k-spec k-sxs) string)
  (lambda (spec xs)
    (if (null? xs)
        ""
        (k-cat3 " " (k-show-sx spec (car xs)) (k-show-args spec (cdr xs))))))
(define k-show-op (->* (k-spec string k-sx k-sx) string)
  (lambda (spec op a b)
    (k-cat5 "(" op (k-show-sx spec a) " " (string-append (k-show-sx spec b) ")"))))
(define k-rel-op (->* (int) string)
  (lambda (r) (case r ((0) "<") ((1) "<=") (else "="))))
(define k-show-sfs (->* (k-spec k-sfs) string)
  (lambda (spec ps)
    (if (null? ps) "" (k-cat3 " " (k-show-sf spec (car ps)) (k-show-sfs spec (cdr ps))))))
(define k-show-sf (->* (k-spec k-sf) string)
  (lambda (spec f)
    (tagcase f
      (sf-true () "#t")
      (sf-false () "#f")
      (sf-rel (r x y)
        (let ((xy (k-cat3 (k-show-sx spec x) " " (k-show-sx spec y))))
          (if (= r 3) (k-cat3 "(not (= " xy "))") (k-cat5 "(" (k-rel-op r) " " xy ")"))))
      (sf-holds (a) (k-spec-name spec a))
      (sf-not (p) (k-cat3 "(not " (k-show-sf spec p) ")"))
      (sf-and (ps) (k-cat3 "(and" (k-show-sfs spec ps) ")"))
      (sf-or (ps) (k-cat3 "(or" (k-show-sfs spec ps) ")"))
      (sf-implies (p q) (k-cat5 "(implies " (k-show-sf spec p) " " (k-show-sf spec q) ")")))))
;; A specification's clauses, each after a space, those not `#t`
;; (`Checker::show_spec`).
(define k-show-spec (->* (k-spec) string)
  (lambda (spec)
    (let ((req (if (k-sf-trivial? (extract spec 3))
                   ""
                   (k-cat3 " (requires " (k-show-sf spec (extract spec 3)) ")")))
          (ens (if (k-sf-trivial? (extract spec 4))
                   ""
                   (k-cat5 " (ensures " (k-spec-name spec (sx-result)) " "
                           (k-show-sf spec (extract spec 4)) ")"))))
      (string-append req ens))))

;;; ------------------------------------------------------------ latent

;; What a test proves (`check-proving.fx`'s `k-latent`), read back
;; (`specs.rs`). A proposition of a test's, as the `k-prop` it is; `(not (=
;; a b))` too: none or one.
(define k-sx-term (->* (k-sx) (listof k-term acyclic))
  (lambda (x)
    (tagcase x
      (sx-param (i) (list (tm-param i)))
      (sx-length (i) (list (tm-length i)))
      (sx-lit (k) (list (tm-lit k)))
      (else z nil))))
(define k-rel-prop (->* (int k-sx k-sx) k-props)
  (lambda (o a b)
    (let ((x (k-sx-term a)) (y (k-sx-term b)))
      (if (or (null? x) (null? y)) nil (list (pr-rel o (car x) (car y)))))))
(define k-sf-prop (->* (k-sf) k-props)
  (lambda (f)
    (tagcase f
      (sf-holds (a)
        (tagcase a
          (sx-shape (i k) (list (pr-shape i k #f)))
          (sx-acyclic (i) (list (pr-acyclic i)))
          (sx-nat (i) (list (pr-nat i)))
          (sx-length-is (i j) (list (pr-length i j)))
          (else z nil)))
      (sf-not (g)
        (tagcase g
          (sf-holds (a) (tagcase a (sx-shape (i k) (list (pr-shape i k #t))) (else z nil)))
          (sf-rel (r x y) (if (= r 2) (k-rel-prop 3 x y) nil))
          (else z nil)))
      (sf-rel (r x y) (k-rel-prop r x y))
      (else z nil))))
;; Each of `fs` as a `k-prop`, if each is one (none or one list).
(define k-sfs-props (->* (k-sfs) (listof k-props acyclic))
  (lambda (fs)
    (if (null? fs)
        (list nil)
        (let ((p (k-sf-prop (car fs))) (rest (k-sfs-props (cdr fs))))
          (if (or (null? p) (null? rest)) nil (list (cons (car p) (car rest))))))))
(define k-sf-result? (->* (k-sf) bool)
  (lambda (f) (tagcase f (sf-holds (a) (tagcase a (sx-result () #t) (else z #f))) (else z #f))))
(define k-sf-not-result? (->* (k-sf) bool)
  (lambda (f) (tagcase f (sf-not (g) (k-sf-result? g)) (else z #f))))
;; A conjunction's propositions, if each is one (none or one list).
(define k-and-props (->* (k-sf) (listof k-props acyclic))
  (lambda (f) (tagcase f (sf-and (ps) (k-sfs-props ps)) (else z nil))))
;; An `ensures` as `k-latent` writes one, alone or the first of two
;; conjuncts: what it proves where true and where false, and the rest
;; (`specs::latent_split`).
(define k-latent-split (->* (k-sf) k-latents)
  (lambda (f)
    (let* ((two (tagcase f
                  (sf-and (ps)
                    (and (= (k-length ps) 2) (tagcase (car ps) (sf-and (qs) #t) (else z #f))))
                  (else z #f)))
           (l (if two (tagcase f (sf-and (ps) (car ps)) (else z f)) f))
           (rest (if two (tagcase f (sf-and (ps) (k-nth ps 1)) (else z f)) (sf-true))))
      (tagcase l
        (sf-and (sides)
          (if (= (k-length sides) 2)
              (tagcase (car sides)
                (sf-implies (r then)
                  (tagcase (k-nth sides 1)
                    (sf-implies (nr els)
                      (let ((t (k-and-props then)) (e (k-and-props els)))
                        (if (and (k-sf-result? r) (k-sf-not-result? nr)
                                 (not (null? t)) (not (null? e)))
                            (list (product (1 (car t)) (2 (car e)) (3 rest)))
                            nil)))
                    (else z nil)))
                (else z nil))
              nil))
        (else z nil)))))
;; What an `ensures` proves of the arguments where its result is true
;; (`yes`) or false: the propositions of each conjunct `(implies r p)`
;; (`(implies (not r) p)`) (`specs::latent_facts`).
(define k-ensures-latent (->* (k-sf bool) k-props)
  (lambda (f yes)
    (tagcase f
      (sf-and (ps) (k-ensures-latent-each ps yes))
      (sf-implies (r q)
        (if (if yes (k-sf-result? r) (k-sf-not-result? r)) (k-conjunct-props q) nil))
      (else z nil))))
(define k-ensures-latent-each (->* (k-sfs bool) k-props)
  (lambda (ps yes)
    (if (null? ps)
        nil
        (k-props-append (k-ensures-latent (car ps) yes) (k-ensures-latent-each (cdr ps) yes)))))
(define k-conjunct-props (->* (k-sf) k-props)
  (lambda (q) (tagcase q (sf-and (ps) (k-conjuncts-props ps)) (else z (k-sf-prop q)))))
(define k-conjuncts-props (->* (k-sfs) k-props)
  (lambda (ps)
    (if (null? ps)
        nil
        (k-props-append (k-conjunct-props (car ps)) (k-conjuncts-props (cdr ps))))))
(define k-props-append (->* (k-props k-props) k-props)
  (lambda (a b) (if (null? a) b (cons (car a) (k-props-append (cdr a) b)))))

;;; ------------------------------------------------------------ the prover

;; The atoms met, numbered by their places, and the booleans; how many
;; cases have been looked at (`logic.rs`'s `Prover`).
(define k-logic-atoms (ref k-sxs @t) (new nil))
(define k-logic-flags (ref k-sxs @t) (new nil))
(define k-logic-cases (ref int @t) (new 0))
(define k-sxs-snoc (->* (k-sxs k-sx) k-sxs)
  (lambda (xs x) (if (null? xs) (cons x nil) (cons (car xs) (k-sxs-snoc (cdr xs) x)))))
;; `x`'s place among `xs`, from `i`, or -1.
(define k-sx-place (->* (k-sxs k-sx int) int)
  (lambda (xs x i)
    (cond ((null? xs) -1) ((k-sx=? (car xs) x) i) (else (k-sx-place (cdr xs) x (+ i 1))))))
;; `x`'s number among those `r` holds, it put last if new.
(define k-logic-number (->* ((ref k-sxs @t) k-sx) int)
  (lambda (r x)
    (let ((i (k-sx-place (get r) x 0)))
      (if (>= i 0)
          i
          (begin (set r (k-sxs-snoc (get r) x)) (- (k-length (get r)) 1))))))
(define k-lin-const? (->* (k-size) bool)
  (lambda (z) (tagcase z (sz-lin (k ts) (null? ts)) (else y #f))))
(define k-lin-k (->* (k-size) int) (lambda (z) (tagcase z (sz-lin (k ts) k) (else y 0))))
;; `x` as a linear form over the atoms' numbers.
(define k-linear (->* (k-sx) k-size)
  (lambda (x)
    (tagcase x
      (sx-lit (k) (k-size-lit k))
      (sx-add (a b) (let* ((la (k-linear a)) (lb (k-linear b))) (k-size-add-scaled la lb 1)))
      (sx-sub (a b) (let* ((la (k-linear a)) (lb (k-linear b))) (k-size-add-scaled la lb -1)))
      (sx-mul (a b)
        (let* ((la (k-linear a)) (lb (k-linear b)))
          (cond ((k-lin-const? la) (k-size-add-scaled (k-size-lit 0) lb (k-lin-k la)))
                ((k-lin-const? lb) (k-size-add-scaled (k-size-lit 0) la (k-lin-k lb)))
                (else (k-size-var (k-logic-number k-logic-atoms x))))))
      (else z (k-size-var (k-logic-number k-logic-atoms x))))))

;; Fourier–Motzkin over `eqs` (each `= 0`) and `ges` (each `≥ 0`), as
;; `logic.rs`'s `fm_refutes`: each equality with a variable of coefficient
;; ±1 first used to rewrite it away, the first such each time; the rest two
;; inequalities each; then each variable eliminated, lowest first.
(define k-lins-snoc (->* (k-lins k-size) k-lins)
  (lambda (xs x) (if (null? xs) (cons x nil) (cons (car xs) (k-lins-snoc (cdr xs) x)))))
(define k-lins-without (->* (k-lins int) k-lins)
  (lambda (xs i) (if (= i 0) (cdr xs) (cons (car xs) (k-lins-without (cdr xs) (- i 1))))))
(define k-lin-terms (->* (k-size) k-terms) (lambda (z) (tagcase z (sz-lin (k ts) ts) (else y nil))))
;; The place of the first of `es` with a coefficient ±1, from `i`, or -1.
(define k-first-unit (->* (k-lins int) int)
  (lambda (es i)
    (cond ((null? es) -1)
          ((not (null? (k-unit-terms (k-lin-terms (car es))))) i)
          (else (k-first-unit (cdr es) (+ i 1))))))
;; Each of `xs` with `v` rewritten away by `e`, `c·v + rest = 0` (`c` ±1).
(define k-lins-rewritten (->* (k-lins int int k-size) k-lins)
  (lambda (xs v c e)
    (if (null? xs)
        nil
        (let* ((d (k-coef-of (k-lin-terms (car xs)) v))
               (x (if (= d 0) (car xs) (k-size-add-scaled (car xs) e (- 0 (* d c))))))
          (cons x (k-lins-rewritten (cdr xs) v c e))))))
;; The equalities left: none without an integer solution, each made two
;; inequalities after `ges`.
(define k-fm-equalities (->* (k-lins k-lins) bool)
  (lambda (eqs ges)
    (if (null? eqs)
        (let ((vs (k-lins-vars ges nil))) (k-fm-eliminate ges vs))
        (let* ((e (car eqs)) (g (k-terms-gcd (k-lin-terms e) 0)) (k (k-lin-k e)))
          (or (and (= g 0) (not (= k 0)))
              (and (> g 1) (not (= (remainder k g) 0)))
              (let ((neg (k-size-add-scaled (k-size-lit 0) e -1)))
                (k-fm-equalities (cdr eqs) (k-lins-snoc (k-lins-snoc ges e) neg))))))))
(define k-fm-refutes? (->* (k-lins k-lins) bool)
  (lambda (eqs ges)
    (let ((i (k-first-unit eqs 0)))
      (if (< i 0)
          (k-fm-equalities eqs ges)
          (let* ((e (k-nth eqs i)) (u (car (k-unit-terms (k-lin-terms e))))
                 (rest (k-lins-without eqs i)))
            (k-fm-refutes? (k-lins-rewritten rest (car u) (cdr u) e)
                           (k-lins-rewritten ges (car u) (cdr u) e)))))))

;; A case: its equalities, inequalities, disequalities, and booleans (each
;; flag's number and whether it holds).
(define-type k-flags (listof (productof (1 int) (2 bool)) acyclic))
(define-type k-case (productof (1 k-lins) (2 k-lins) (3 k-lins) (4 k-flags)))
;; What is left to take apart: each formula, and whether it is to hold.
(define-type k-todo (listof (productof (1 k-sf) (2 bool)) acyclic))
(define k-todo-snoc (->* (k-todo k-sf bool) k-todo)
  (lambda (xs f yes)
    (if (null? xs)
        (cons (product (1 f) (2 yes)) nil)
        (cons (car xs) (k-todo-snoc (cdr xs) f yes)))))
(define k-todo-onto (->* (k-todo k-sfs bool) k-todo)
  (lambda (xs ps yes) (if (null? ps) xs (k-todo-onto (k-todo-snoc xs (car ps) yes) (cdr ps) yes))))
(define k-todo-without (->* (k-todo int) k-todo)
  (lambda (xs i) (if (= i 0) (cdr xs) (cons (car xs) (k-todo-without (cdr xs) (- i 1))))))
(define k-splits? (->* (k-sf bool) bool)
  (lambda (f yes)
    (tagcase f (sf-or (ps) yes) (sf-and (ps) (not yes)) (sf-implies (p q) yes) (else z #f))))
;; The place of the first of `todo` that does not split, from `i`, or -1.
(define k-first-plain (->* (k-todo int) int)
  (lambda (todo i)
    (cond ((null? todo) -1)
          ((not (k-splits? (extract (car todo) 1) (extract (car todo) 2))) i)
          (else (k-first-plain (cdr todo) (+ i 1))))))
(define k-flag-in? (->* (int bool k-flags) bool)
  (lambda (k yes fs)
    (and (not (null? fs))
         (or (and (= (extract (car fs) 1) k) (bool=? (extract (car fs) 2) yes))
             (k-flag-in? k yes (cdr fs))))))
(define k-flags-snoc (->* (k-flags int bool) k-flags)
  (lambda (fs k yes)
    (if (null? fs)
        (cons (product (1 k) (2 yes)) nil)
        (cons (car fs) (k-flags-snoc (cdr fs) k yes)))))
;; `c` with a relation, `r` (0 `<`, 1 `<=`, 2 `=`, 3 not `=`) of `x` and
;; `y`, holding or not: of `d = y - x`.
(define k-case-rel (->* (k-case int k-sx k-sx bool) k-case)
  (lambda (c r x y yes)
    (let* ((lx (k-linear x)) (ly (k-linear y))
           (d (k-size-add-scaled ly lx -1)) (neg (k-size-add-scaled (k-size-lit 0) d -1))
           (eqs (extract c 1)) (ges (extract c 2)) (nes (extract c 3)) (fs (extract c 4))
           (eq (or (and (= r 2) yes) (and (= r 3) (not yes)))))
      (cond ((and (= r 0) yes) (k-case-ge c (k-size-plus d -1)))
            ((= r 0) (k-case-ge c neg))
            ((and (= r 1) yes) (k-case-ge c d))
            ((= r 1) (k-case-ge c (k-size-plus neg -1)))
            (eq (product (1 (k-lins-snoc eqs d)) (2 ges) (3 nes) (4 fs)))
            (else (product (1 eqs) (2 ges) (3 (k-lins-snoc nes d)) (4 fs)))))))
;; `c` with `g ≥ 0`, its disequalities `nes`.
(define k-case-ge-of (->* (k-case k-size k-lins) k-case)
  (lambda (c g nes)
    (product (1 (extract c 1)) (2 (k-lins-snoc (extract c 2) g)) (3 nes) (4 (extract c 4)))))
(define k-case-ge (->* (k-case k-size) k-case)
  (lambda (c g) (k-case-ge-of c g (extract c 3))))
;; Whether no case of `c` with `todo` is possible (`Prover::refute`).
(define k-refute (->* (k-case k-todo) bool)
  (lambda (c todo)
    (begin
      (set k-logic-cases (+ (get k-logic-cases) 1))
      (and (<= (get k-logic-cases) 512) (k-refute-plain c todo)))))
;; The formulas that do not split, the first of them each time.
(define k-refute-plain (->* (k-case k-todo) bool)
  (lambda (c todo)
    (let ((i (k-first-plain todo 0)))
      (if (< i 0)
          (k-refute-split c todo)
          (let* ((item (k-nth todo i)) (rest (k-todo-without todo i))
                 (f (extract item 1)) (yes (extract item 2)))
            (tagcase f
              (sf-true () (or (not yes) (k-refute-plain c rest)))
              (sf-false () (or yes (k-refute-plain c rest)))
              (sf-not (p) (k-refute-plain c (k-todo-snoc rest p (not yes))))
              (sf-and (ps) (k-refute-plain c (k-todo-onto rest ps yes)))
              (sf-or (ps) (k-refute-plain c (k-todo-onto rest ps yes)))
              (sf-implies (p q) (k-refute-plain c (k-todo-snoc (k-todo-snoc rest p #t) q #f)))
              (sf-holds (a)
                (let ((k (k-logic-number k-logic-flags a)))
                  (or (k-flag-in? k (not yes) (extract c 4))
                      (k-refute-plain (product (1 (extract c 1)) (2 (extract c 2)) (3 (extract c 3))
                                               (4 (k-flags-snoc (extract c 4) k yes)))
                                      rest))))
              (sf-rel (r x y) (k-refute-plain (k-case-rel c r x y yes) rest))))))))
;; Each of `ps`, holding or not, a way after `rest`: each refuted.
(define k-refute-ways (->* (k-case k-todo k-sfs bool) bool)
  (lambda (c rest ps yes)
    (or (null? ps)
        (and (k-refute c (k-todo-snoc rest (car ps) yes)) (k-refute-ways c rest (cdr ps) yes)))))
;; Only splits left: the case refuted by Fourier–Motzkin, or split on the
;; first, or on a disequality, below or above.
(define k-refute-split (->* (k-case k-todo) bool)
  (lambda (c todo)
    (cond ((k-fm-refutes? (extract c 1) (extract c 2)) #t)
          ((not (null? todo))
           (let ((f (extract (car todo) 1)) (rest (cdr todo)))
             (tagcase f
               (sf-or (ps) (k-refute-ways c rest ps #t))
               (sf-and (ps) (k-refute-ways c rest ps #f))
               (sf-implies (p q)
                 (and (k-refute c (k-todo-snoc rest p #f)) (k-refute c (k-todo-snoc rest q #t))))
               (else z #f))))
          ((not (null? (extract c 3)))
           (let ((d (car (extract c 3))) (nes (cdr (extract c 3))))
             (and (k-refute (k-case-ge-of c (k-size-add-scaled (k-size-lit -1) d -1) nes) nil)
                  (k-refute (k-case-ge-of c (k-size-plus d -1) nes) nil))))
          (else #f))))
;; Whether `hyps` entail `goal`, as far as the prover shows
;; (`logic::entails`).
(define k-entails? (->* (k-sfs k-sf) bool)
  (lambda (hyps goal)
    (or (k-sf-trivial? goal)
        (k-sf-in? goal hyps)
        (begin
          (set k-logic-atoms nil)
          (set k-logic-flags nil)
          (set k-logic-cases 0)
          (k-refute (product (1 nil) (2 nil) (3 nil) (4 nil))
                    (k-todo-snoc (k-todo-onto nil hyps #t) goal #f))))))
(define k-spec-requires (->* (k-specs) k-sf)
  (lambda (s) (if (null? s) (sf-true) (extract (car s) 3))))
(define k-spec-ensures (->* (k-specs) k-sf)
  (lambda (s) (if (null? s) (sf-true) (extract (car s) 4))))
;; Behavioural subtyping (`logic::spec_within`): `a` requires no more than
;; `b`, and, with `b`'s `requires`, ensures no less.
(define k-spec-within? (->* (k-specs k-specs) bool)
  (lambda (a b)
    (or (k-specs=? a b)
        (let ((rb (k-spec-requires b)))
          (and (k-entails? (cons rb nil) (k-spec-requires a))
               (k-entails? (list rb (k-spec-ensures a)) (k-spec-ensures b)))))))
;; The specification of `t`, a `subr`, none or one (`Checker::spec_of`).
(define k-spec-of (->* (int) k-specs)
  (lambda (t)
    (if (< t 0) nil (tagcase (k-get (k-resolve t)) (ty-subr (e ps r cv sp) sp) (else y nil)))))
;; Why procedure type `got` is not within `want`, if its specification is
;; why: a line saying so, or nothing (`Checker::spec_delta`).
(define k-spec-delta (->* (int int) string)
  (lambda (got want)
    (let ((g (k-spec-of got)) (w (k-spec-of want)))
      (if (and (or (not (null? g)) (not (null? w))) (not (k-spec-within? g w)))
          (string-append (char->string (integer->char 10))
                         (string-append "  it requires more, or ensures less, than is expected, "
                                        "as far as the prover can tell"))
          ""))))
;; The module, the lambda given its modules, and the loads, closed.
)))
