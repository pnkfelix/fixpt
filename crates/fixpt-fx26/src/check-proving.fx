;;; The checker, in FX-26: what a test proves, as `parse.rs` and `specs.rs`
;;; have it: reading `(bool (then P …) (else Q …))`, a procedure's result,
;;; an `ensures` of it. After
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
(hide (include eager-reader-types) (include parser-types) (include check-types-types)
      (include check-read-types))
;; What it uses of the modules it is given: all of each, hidden.
(hide (include check-types) (include check-env) (include check-read) (include check-syntax)
      (include parser))

;; Shape `n`'s number (`check-unions.fx`), or -1.
(define k-shape-named (->* (string) int)
  (lambda (n)
    (case n
      (("int") 0) (("f64") 1) (("f32") 2) (("char") 3) (("bool") 4) (("nil") 5) (("pair") 6)
      (("string") 7) (("symbol") 8) (("procedure") 9) (("bloblet") 10) (("box") 11)
      (("sum") 12) (("product") 13) (("vector") 14) (("bytevector") 15) (("keyword") 16)
      (else -1))))
(define k-prop-usage string
  (string-append "a proposition: `(shape i shape)`, `(acyclic i)`, `(nat i)`, `(length i j)`, "
                 "`(< a b)`, `(<= a b)`, `(= a b)`, or `(not …)` of a shape or an `=`"))
(define k-shapes-usage string
  (string-append "a shape, one of int, f64, f32, char, bool, nil, pair, string, "
                 "symbol, procedure, bloblet, box, sum, product, vector, bytevector, keyword"))
(define k-term-usage string "a size: a parameter's number, `(length i)`, or `(lit k)`")
;; Whether `s` is an integer literal.
(define k-int-lit? (->* (syn) bool)
  (lambda (s) (tagcase s (atom (d a b) (datum-int? d)) (else x #f))))
;; A parameter's number, from 0, of a procedure of `n`.
(define k-prop-param (->* (syn int) int)
  (lambda (i n)
    (let ((k (if (k-int-lit? i) (syn-int i) -1)))
      (if (and (>= k 0) (< k n))
          k
          (k-sfail (string-append "a parameter's number, from 0 to " (int->string (- n 1))) i)))))
;; A size in a proposition: a parameter's number, `(length i)` or `(lit k)`.
(define k-prop-term (->* (syn int) k-term)
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
(define k-prop-shape (->* (syn) int)
  (lambda (k)
    (let ((shape (if (syn-symbol? k) (k-shape-named (syn-name k)) -1)))
      (if (< shape 0) (k-sfail k-shapes-usage k) shape))))
;; `form`, a proposition, `negated` if under a `not`, of a procedure of `n`.
(define k-parse-prop-form (->* (syn int bool) k-prop)
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
(define k-parse-prop (->* (syn int) k-prop)
  (lambda (p n)
    (let ((parts (k-items p k-prop-usage)))
      (if (and (= (k-length parts) 2) (syn-symbol? (car parts))
               (string=? (syn-name (car parts)) "not"))
          (k-parse-prop-form (k-nth parts 1) n #t)
          (k-parse-prop-form p n #f)))))
(define k-parse-prop-list (->* (k-syns int) k-props)
  (lambda (ps n)
    (if (null? ps)
        nil
        (let* ((p (k-parse-prop (car ps) n)) (rest (k-parse-prop-list (cdr ps) n)))
          (the k-props (cons p rest))))))
;; `(which proposition …)`.
(define k-parse-props (->* (syn string int) k-props)
  (lambda (s which n)
    (let* ((usage (k-cat3 "`(" which " proposition …)`")) (items (k-items s usage)))
      (begin
        (k-shape (and (not (null? items)) (syn-symbol? (car items))
                      (string=? (syn-name (car items)) which))
                 usage s)
        (k-parse-prop-list (cdr items) n)))))
;; `(bool (then P …) (else Q …))`, the result of a procedure of `n`
;; parameters: what it ensures (`specs::latent`).
(define k-parse-proving (->* (syn int) k-sf)
  (lambda (s n)
    (let* ((usage "`(bool (then proposition …) (else proposition …))`")
           (items (k-items s usage)))
      (begin
        (k-shape (= (k-length items) 3) usage s)
        (let* ((then (k-parse-props (k-nth items 1) "then" n))
               (els (k-parse-props (k-nth items 2) "else" n)))
          (k-latent then els))))))
;; What a test proves, `(bool (then P …) (else Q …))`, as an `ensures` of
;; its result: `(and (implies r (and P …)) (implies (not r) (and Q …)))`.
(define k-latent (->* (k-props k-props) k-sf)
  (lambda (then els)
    (let ((r (sf-holds (sx-result))))
      (sf-and (list (sf-implies r (sf-and (k-props-sfs then)))
                    (sf-implies (sf-not r) (sf-and (k-props-sfs els))))))))
(define k-props-sfs (->* (k-props) k-sfs)
  (lambda (ps) (if (null? ps) nil (cons (k-prop-sf (car ps)) (k-props-sfs (cdr ps))))))
(define k-term-sx (->* (k-term) k-sx)
  (lambda (t)
    (tagcase t (tm-param (i) (sx-param i)) (tm-length (i) (sx-length i)) (tm-lit (k) (sx-lit k)))))
(define k-prop-sf (->* (k-prop) k-sf)
  (lambda (p)
    (tagcase p
      (pr-shape (i k f) (if f (sf-not (sf-holds (sx-shape i k))) (sf-holds (sx-shape i k))))
      (pr-acyclic (i) (sf-holds (sx-acyclic i)))
      (pr-nat (i) (sf-holds (sx-nat i)))
      (pr-length (i j) (sf-holds (sx-length-is i j)))
      (pr-rel (o a b) (sf-rel o (k-term-sx a) (k-term-sx b))))))
;; `names` with `n` last.
(define k-names-snoc (->* (k-names symbol) k-names)
  (lambda (ns n) (if (null? ns) (cons n nil) (cons (car ns) (k-names-snoc (cdr ns) n)))))
;; The module, the lambda given its modules, and the loads, closed.
)))
