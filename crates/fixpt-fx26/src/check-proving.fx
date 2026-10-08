;;; The checker, in FX-26: what a test proves (`ty-proving`), as `parse.rs`
;;; and `check.rs` have it: reading `(bool (then P …) (else Q …))`, a
;;; procedure's result, and the call's own type, a `bool`. After
;;; `check-subst.fx`, before the types' reader, which reads with it; part of
;;; the checker, `check-types.fx` first.

;; A module (`TODO.md` §34: the front end into modules, a file at a time);
;; what other files use re-exported after it.
(define check-proving-module (module
;; Shape `n`'s number (`check-unions.fx`), or -1.
(define k-shape-named (subr (read @globals) (string) int)
  (lambda (n)
    (case n
      (("int") 0) (("f64") 1) (("f32") 2) (("char") 3) (("bool") 4) (("nil") 5) (("pair") 6)
      (("string") 7) (("symbol") 8) (("procedure") 9) (("bloblet") 10) (("box") 11)
      (("sum") 12) (("product") 13) (else -1))))
(define k-prop-usage string
  "a proposition, `(shape parameter shape)` or `(not (shape parameter shape))`")
(define k-shapes-usage string
  (string-append "a shape, one of int, f64, f32, char, bool, nil, pair, string, "
                 "symbol, procedure, bloblet, box, sum, product"))
(define-type k-prop (productof (1 int) (2 int) (3 bool)))
;; `(shape i shape)`, of a procedure of `n` parameters, `negated` if under
;; a `not`.
(define k-parse-shape-prop (subr (maxeff checks spin) (syn int bool) k-prop)
  (lambda (form n negated)
    (let ((parts (k-items form k-prop-usage)))
      (begin
        (k-shape (and (= (k-length parts) 3) (syn-symbol? (car parts))
                      (string=? (syn-name (car parts)) "shape"))
                 k-prop-usage form)
        (let* ((i (k-nth parts 1)) (k (k-nth parts 2)) (param (syn-int i))
               (in-range (if (and (>= param 0) (< param n))
                             #u
                             (k-sfail (string-append "a parameter's number, from 0 to "
                                                     (int->string (- n 1)))
                                      i)))
               (shape (if (syn-symbol? k) (k-shape-named (syn-name k)) -1)))
          (if (< shape 0)
              (k-sfail k-shapes-usage k)
              (product (1 param) (2 shape) (3 negated))))))))
(define k-parse-prop (subr (maxeff checks spin) (syn int) k-prop)
  (lambda (p n)
    (let ((parts (k-items p k-prop-usage)))
      (if (and (= (k-length parts) 2) (syn-symbol? (car parts))
               (string=? (syn-name (car parts)) "not"))
          (k-parse-shape-prop (k-nth parts 1) n #t)
          (k-parse-shape-prop p n #f)))))
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
(define k-prop=? (subr pure (k-prop k-prop) bool)
  (lambda (p q)
    (and (= (extract p 1) (extract q 1)) (= (extract p 2) (extract q 2))
         (bool=? (extract p 3) (extract q 3)))))
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
))

(define k-parse-proving (with check-proving-module k-parse-proving))
(define k-call-te (with check-proving-module k-call-te))
(define k-names-snoc (with check-proving-module k-names-snoc))
(define k-props-within? (with check-proving-module k-props-within?))
(define k-props=? (with check-proving-module k-props=?))
