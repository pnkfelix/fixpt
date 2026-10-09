;;; The checker, in FX-26: what a test proves (`ty-proving`), as `parse.rs`
;;; and `check.rs` have it: reading `(bool (then P …) (else Q …))`, a
;;; procedure's result, and the call's own type, a `bool`. After
;;; `check-subst.fx`, before the types' reader, which reads with it; part of
;;; the checker, `check-types.fx` first.

;; Its types, those it uses of the files before it, and the signatures of
;; what it is given.
(let* ((eager-reader-types ((proj (load-module "fx26:eager-reader-types.fx") @s @e @m @c)))
       (parser-types ((proj (load-module "fx26:parser-types.fx") @s @e @m @c @p)))
       (check-types-types (load-module "fx26:check-types-types.fx"))
       (check-read-types (load-module "fx26:check-read-types.fx"))
       (check-env-types (load-module "fx26:check-env-types.fx"))
       (check-syntax-types (load-module "fx26:check-syntax-types.fx"))
       (reader-types (load-module "fx26:reader-types.fx")))
  ;; What it is given: the modules of the files before it that it uses.
  (lambda ((check-types (select check-types-types check-types-sig))
           (check-env (select check-env-types check-env-sig))
           (check-read (select check-read-types check-read-sig))
           (check-syntax (select check-syntax-types check-syntax-sig))
           (parser (select reader-types parser-sig)))
    (module

;; The types it uses of the files before it.
(define atom (with eager-reader-types atom))
(define-type syn (select parser-types syn))
(define-effect checks (select check-types-types checks))
(define-type k-names (select check-types-types k-names))
(define-type k-prop (select check-types-types k-prop))
(define-type k-props (select check-types-types k-props))
(define-type k-te (select check-types-types k-te))
(define-type k-term (select check-types-types k-term))
(define-effect kreads (select check-types-types kreads))
(define pr-acyclic (with check-types-types pr-acyclic))
(define pr-length (with check-types-types pr-length))
(define pr-nat (with check-types-types pr-nat))
(define pr-rel (with check-types-types pr-rel))
(define pr-shape (with check-types-types pr-shape))
(define tm-length (with check-types-types tm-length))
(define tm-lit (with check-types-types tm-lit))
(define tm-param (with check-types-types tm-param))
(define ty-proving (with check-types-types ty-proving))
(define-type k-items (select check-types-types k-items))
(define-type k-syns (select check-read-types k-syns))
;; What it uses of the modules it is given.
(define k-cat3 (with check-types k-cat3))
(define k-get (with check-types k-get))
(define k-length (with check-types k-length))
(define k-nth (with check-types k-nth))
(define k-te (with check-types k-te))
(define k-ty-new (with check-types k-ty-new))
(define k-bool (with check-env k-bool))
(define k-items (with check-read k-items))
(define k-sfail (with check-read k-sfail))
(define k-list-head (with check-syntax k-list-head))
(define k-shape (with check-syntax k-shape))
(define syn-int (with parser syn-int))
(define syn-name (with parser syn-name))
(define syn-symbol? (with parser syn-symbol?))

;; Shape `n`'s number (`check-unions.fx`), or -1.
(define k-shape-named (subr (read @globals) (string) int)
  (lambda (n)
    (case n
      (("int") 0) (("f64") 1) (("f32") 2) (("char") 3) (("bool") 4) (("nil") 5) (("pair") 6)
      (("string") 7) (("symbol") 8) (("procedure") 9) (("bloblet") 10) (("box") 11)
      (("sum") 12) (("product") 13) (("vector") 14) (("bytevector") 15) (else -1))))
(define k-prop-usage string
  (string-append "a proposition: `(shape i shape)`, `(acyclic i)`, `(nat i)`, `(length i j)`, "
                 "`(< a b)`, `(<= a b)`, `(= a b)`, or `(not …)` of a shape or an `=`"))
(define k-shapes-usage string
  (string-append "a shape, one of int, f64, f32, char, bool, nil, pair, string, "
                 "symbol, procedure, bloblet, box, sum, product, vector, bytevector"))
(define k-term-usage string "a size: a parameter's number, `(length i)`, or `(lit k)`")
;; Whether `s` is an integer literal.
(define k-int-lit? (subr (read @globals) (syn) bool)
  (lambda (s) (tagcase s (atom (d a b) (datum-int? d)) (else x #f))))
;; A parameter's number, from 0, of a procedure of `n`.
(define k-prop-param (subr (maxeff checks spin) (syn int) int)
  (lambda (i n)
    (let ((k (if (k-int-lit? i) (syn-int i) -1)))
      (if (and (>= k 0) (< k n))
          k
          (k-sfail (string-append "a parameter's number, from 0 to " (int->string (- n 1))) i)))))
;; A size in a proposition: a parameter's number, `(length i)` or `(lit k)`.
(define k-prop-term (subr (maxeff checks spin) (syn int) k-term)
  (lambda (x n)
    (if (k-int-lit? x)
        (tm-param (k-prop-param x n))
        (let* ((parts (k-items x k-term-usage)) (hd (k-list-head x)))
          (cond ((and (= (k-length parts) 2) (string=? hd "length"))
                 (tm-length (k-prop-param (k-nth parts 1) n)))
                ((and (= (k-length parts) 2) (string=? hd "lit"))
                 (let ((k (k-nth parts 1)))
                   (if (and (k-int-lit? k) (>= (syn-int k) 0))
                       (tm-lit (syn-int k))
                       (k-sfail "a natural" k))))
                (else (k-sfail k-term-usage x)))))))
;; The shape named `k`, or the error.
(define k-prop-shape (subr (maxeff checks spin) (syn) int)
  (lambda (k)
    (let ((shape (if (syn-symbol? k) (k-shape-named (syn-name k)) -1)))
      (if (< shape 0) (k-sfail k-shapes-usage k) shape))))
;; `form`, a proposition, `negated` if under a `not`, of a procedure of `n`.
(define k-parse-prop-form (subr (maxeff checks spin) (syn int bool) k-prop)
  (lambda (form n negated)
    (let* ((parts (k-items form k-prop-usage)) (hd (k-list-head form)) (m (- (k-length parts) 1)))
      (cond ((and (string=? hd "shape") (= m 2))
             (let* ((i (k-prop-param (k-nth parts 1) n)) (k (k-prop-shape (k-nth parts 2))))
               (pr-shape i k negated)))
            ((and (string=? hd "acyclic") (= m 1) (not negated))
             (pr-acyclic (k-prop-param (k-nth parts 1) n)))
            ((and (string=? hd "nat") (= m 1) (not negated))
             (pr-nat (k-prop-param (k-nth parts 1) n)))
            ((and (string=? hd "length") (= m 2) (not negated))
             (let* ((i (k-prop-param (k-nth parts 1) n)) (j (k-prop-param (k-nth parts 2) n)))
               (pr-length i j)))
            ((and (= m 2)
                  (or (string=? hd "=")
                      (and (not negated) (or (string=? hd "<") (string=? hd "<=")))))
             (let* ((a (k-prop-term (k-nth parts 1) n)) (b (k-prop-term (k-nth parts 2) n)))
               (pr-rel (cond ((string=? hd "<") 0) ((string=? hd "<=") 1) (negated 3) (else 2))
                       a b)))
            (else (k-sfail k-prop-usage form))))))
(define k-parse-prop (subr (maxeff checks spin) (syn int) k-prop)
  (lambda (p n)
    (let ((parts (k-items p k-prop-usage)))
      (if (and (= (k-length parts) 2) (syn-symbol? (car parts))
               (string=? (syn-name (car parts)) "not"))
          (k-parse-prop-form (k-nth parts 1) n #t)
          (k-parse-prop-form p n #f)))))
(define k-parse-prop-list (subr (maxeff checks spin) (k-syns int) k-props)
  (lambda (ps n)
    (if (null? ps)
        nil
        (let* ((p (k-parse-prop (car ps) n)) (rest (k-parse-prop-list (cdr ps) n)))
          (the k-props (cons p rest))))))
;; `(which proposition …)`.
(define k-parse-props (subr (maxeff checks spin) (syn string int) k-props)
  (lambda (s which n)
    (let* ((usage (k-cat3 "`(" which " proposition …)`")) (items (k-items s usage)))
      (begin
        (k-shape (and (not (null? items)) (syn-symbol? (car items))
                      (string=? (syn-name (car items)) which))
                 usage s)
        (k-parse-prop-list (cdr items) n)))))
;; `(bool (then P …) (else Q …))`, the result of a procedure of `n`
;; parameters.
(define k-parse-proving (subr (maxeff checks spin) (syn int) int)
  (lambda (s n)
    (let* ((usage "`(bool (then proposition …) (else proposition …))`")
           (items (k-items s usage)))
      (begin
        (k-shape (= (k-length items) 3) usage s)
        (let* ((then (k-parse-props (k-nth items 1) "then" n))
               (els (k-parse-props (k-nth items 2) "else" n)))
          (k-ty-new (ty-proving then els)))))))
;; `names` with `n` last.
(define k-names-snoc (subr (maxeff (read @globals) (alloc @t) spin) (k-names symbol) k-names)
  (lambda (ns n) (if (null? ns) (cons n nil) (cons (car ns) (k-names-snoc (cdr ns) n)))))
;; Whether proposition lists are equal; whether each of `ps` is one of `qs`.
(define k-term=? (subr pure (k-term k-term) bool)
  (lambda (s u)
    (tagcase s
      (tm-param (i) (tagcase u (tm-param (j) (= i j)) (else y #f)))
      (tm-length (i) (tagcase u (tm-length (j) (= i j)) (else y #f)))
      (tm-lit (i) (tagcase u (tm-lit (j) (= i j)) (else y #f))))))
(define k-prop=? (subr (read @globals) (k-prop k-prop) bool)
  (lambda (p q)
    (tagcase p
      (pr-shape (i k f)
        (tagcase q (pr-shape (j l g) (and (= i j) (= k l) (bool=? f g))) (else y #f)))
      (pr-acyclic (i) (tagcase q (pr-acyclic (j) (= i j)) (else y #f)))
      (pr-nat (i) (tagcase q (pr-nat (j) (= i j)) (else y #f)))
      (pr-length (i k) (tagcase q (pr-length (j l) (and (= i j) (= k l))) (else y #f)))
      (pr-rel (o a b) (tagcase q (pr-rel (r c d) (and (= o r) (k-term=? a c) (k-term=? b d)))
                               (else y #f))))))
(define k-prop-in? (subr (maxeff (read @globals) spin) (k-prop k-props) bool)
  (lambda (p qs) (and (not (null? qs)) (or (k-prop=? p (car qs)) (k-prop-in? p (cdr qs))))))
(define k-props-within? (subr (maxeff (read @globals) spin) (k-props k-props) bool)
  (lambda (ps qs) (or (null? ps) (and (k-prop-in? (car ps) qs) (k-props-within? (cdr ps) qs)))))
(define k-props=? (subr (maxeff (read @globals) spin) (k-props k-props) bool)
  (lambda (ps qs)
    (if (null? ps)
        (null? qs)
        (and (not (null? qs)) (k-prop=? (car ps) (car qs)) (k-props=? (cdr ps) (cdr qs))))))
;; A call's type and effect: a test's result, `bool`; what it proves is of
;; the call's arguments, there (`k-latent-narrowing`), and nowhere else.
(define k-call-te (subr (maxeff kreads spin) (k-te) k-te)
  (lambda (te)
    (tagcase (k-get (extract te 1)) (ty-proving (t e) (k-te k-bool (extract te 2))) (else y te))))
;; The module, the lambda given its modules, and the loads, closed.
)))
