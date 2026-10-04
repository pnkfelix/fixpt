;;; The checker, in FX-26: higher kinds (`docs/research/higher-kinds.md`),
;;; the Rust checker's `kinds.rs`. Description functions, of arrow kinds
;;; `(=> (k1 … kn) k)`, made by `dlambda` and applied to descriptions: a
;;; `dlambda` applied is reduced (beta), one that only applies a function to
;;; its parameters is that function (eta), and a variable applied is an
;;; application, `ty-app`, equal only to one of the same function to equal
;;; descriptions. To an effect, an application is an atom, `a-app`.
;;; Part of the checker, `check-types.fx` first.

;;; ------------------------------------------------------------ arrow kinds

;;; ------------------------------------------------------------ description functions

;; Whether description `d` is of kind `k`, as a binder of that kind takes; a
;; function whose kind is not known yet, a `select`, is let through.
(define k-desc-of-kind? (subr (maxeff kstate spin) (k-desc int) bool)
  (lambda (d k)
    (tagcase d
      (dr (r) (or (= k 0) (and (= k 3) (k-place? r))))
      (de (e) (= k 1))
      (dt (t) (or (= k 2) (= k 4)))
      (dz (z) (= k 5))
      (dc (c) (= k 6))
      (df (f) (and (k-arrow-kind? k) (let ((g (k-fun-kind f))) (or (< g 0) (= g k))))))))
;; Whether effect `e` is variable `v` alone.
(define k-eff-is-var? (subr (read @globals) (k-eff int) bool)
  (lambda (e v)
    (and (not (null? e)) (null? (cdr e)) (tagcase (car e) (a-var (w) (= w v)) (else y #f)))))
;; Whether `d` is variable `v` and nothing more.
(define k-is-the-var? (subr (maxeff kreads spin) (k-desc int) bool)
  (lambda (d v)
    (tagcase d
      (dr (r) (tagcase r (r-var (w) (= w v)) (else y #f)))
      (de (e) (k-eff-is-var? e v))
      (dz (z)
        (tagcase z
          (sz-lin (k ts)
            (and (= k 0) (not (null? ts)) (null? (cdr ts))
                 (= (car (car ts)) v) (= (cdr (car ts)) 1)))
          (else y #f)))
      (dc (c) (tagcase c (cv-var (w) (= w v)) (else y #f)))
      (dt (t) (k-type-is-var? t v))
      (df (t) (k-type-is-var? t v)))))
;; Whether `ds` are `bs`'s variables, in order.
(define k-the-vars? (subr (maxeff kreads spin) (k-descs k-binders) bool)
  (lambda (ds bs)
    (cond ((null? ds) (null? bs))
          ((null? bs) #f)
          ((k-is-the-var? (car ds) (extract (car bs) 1)) (k-the-vars? (cdr ds) (cdr bs)))
          (else #f))))
;; Whether `f` is one of `bs`'s variables.
(define k-param-head? (subr (maxeff kreads spin) (int k-binders) bool)
  (lambda (f bs) (tagcase (k-get f) (ty-var (v) (k-binder-has? bs v)) (else y #f))))
;; `(dlambda bs body)`, or, where `body` only applies a function to the
;; parameters in order, that function (eta).
(define k-lam (subr (maxeff kstate spin) (k-binders k-desc) int)
  (lambda (bs body)
    (let ((eta (tagcase body
                 (dt (t)
                   (tagcase (k-get t)
                     (ty-app (f ds)
                       (if (and (k-the-vars? ds bs) (not (k-param-head? f bs))) f -1))
                     (else y -1)))
                 (else y -1))))
      (if (>= eta 0) eta (k-ty-new (ty-lam bs body))))))


;; Binders `ps` made again: fresh variables of the same names and kinds.
(define k-fresh-binders (subr (maxeff kstate spin) (k-binders) k-binders)
  (lambda (ps)
    (if (null? ps)
        nil
        (let* ((v (extract (car ps) 1)) (k (extract (car ps) 2))
               (w (k-new-dvar-of (k-dvar-name v) k))
               (rest (k-fresh-binders (cdr ps))))
          (the k-binders (cons (product (1 w) (2 k)) rest))))))
;; Each of binders `bs`, as a description.
(define k-binders-as-descs (subr (maxeff kstate spin) (k-binders) k-descs)
  (lambda (bs)
    (if (null? bs)
        nil
        (let* ((d (k-binder-desc (extract (car bs) 2) (extract (car bs) 1)))
               (rest (k-binders-as-descs (cdr bs))))
          (the k-descs (cons d rest))))))
;; The `g`th generative type as a description function of kind `want`,
;; `(dlambda ((p k) …) (name p …))`; -1 if it is not of that kind.
(define k-generative-fun (subr (maxeff kstate spin) (int int) int)
  (lambda (g want)
    (let ((ps (extract (k-gen-of g) 2)))
      (if (not (= (k-arrow (k-binder-kinds ps) 2) want))
          -1
          (let* ((fresh (k-fresh-binders ps))
                 (body (k-ty-new (ty-named g (k-binders-as-descs fresh)))))
            (k-lam fresh (dt body)))))))

;;; ------------------------------------------------------------ reading

;; "`f` takes n description(s), and has m", `f` shown.
(define k-fun-arity-message (subr kbuilds (int int int) string)
  (lambda (f want have)
    (k-cat5 (k-quote (k-show-ty f)) " takes " (int->string want)
            " description(s), and has " (int->string have))))
;; Binders of `kinds`, each a fresh variable named as `names`.
(define k-fresh-named (subr (maxeff kstate spin) (k-names k-ids) k-binders)
  (lambda (ns ks)
    (if (null? ns)
        nil
        (let* ((v (k-new-dvar-of (car ns) (car ks))) (rest (k-fresh-named (cdr ns) (cdr ks))))
          (the k-binders (cons (product (1 v) (2 (car ks))) rest))))))
;; Each binder, as a type family's parameter is bound to what it is given.
(define k-binders-as-scope (subr (maxeff kstate spin) (k-binders) k-scope)
  (lambda (bs)
    (if (null? bs)
        nil
        (let* ((v (extract (car bs) 1)) (k (extract (car bs) 2))
               (d (cond ((k-type-kind? k) (ds-rec (k-ty-new (ty-var v))))
                        ((or (= k 0) (= k 3)) (ds-region (r-var v)))
                        ((= k 1) (ds-eff (k-one (a-var v))))
                        ((= k 5) (ds-size (k-size-var v)))
                        ((= k 6) (ds-conv (cv-var v)))
                        (else (ds-fun (k-ty-new (ty-var v))))))
               (rest (k-binders-as-scope (cdr bs))))
          (the k-scope (cons (cons (k-dvar-name v) d) rest))))))
;; Type form `n`, `listof` and kin, of `ts`, given `t` and `r`.
(define k-ctor-type (subr (maxeff kstate spin) (string k-binders) int)
  (lambda (n bs)
    (let* ((t (k-ty-new (ty-var (extract (car bs) 1))))
           (second (extract (car (cdr bs)) 1))
           (r (r-var (if (null? (cdr (cdr bs))) second (extract (car (cdr (cdr bs))) 1)))))
      (cond ((string=? n "ref") (k-ty-new (ty-ref t r)))
            ((string=? n "icell") (k-ty-new (ty-icell t r)))
            ((string=? n "arrayof") (k-ty-new (ty-array t r)))
            ((string=? n "mark-key") (k-ty-new (ty-markkey t r)))
            ((string=? n "pairof") (k-ty-new (ty-pair t (k-ty-new (ty-var second)) r)))
            (else (let* ((slot (k-slot)) (pair (k-ty-new (ty-pair t slot r))))
                    (begin (k-set-link slot pair) slot)))))))
(define k-params-names (subr (read @globals) (k-params) k-names)
  (lambda (ps) (if (null? ps) nil (cons (extract (car ps) 1) (k-params-names (cdr ps))))))
(define k-params-kinds (subr (read @globals) (k-params) k-ids)
  (lambda (ps) (if (null? ps) nil (cons (extract (car ps) 2) (k-params-kinds (cdr ps))))))
;; A `dlambda` of no parameters, as an error says.
(define k-dlambda-empty string "a `dlambda` takes at least one description")
;; Whether `n` is bound to a description function.
(define k-fun-bound? (subr (maxeff kreads (alloc @t)) (string) bool)
  (lambda (n)
    (let ((d (k-lookup-desc (string->symbol n))))
      (and (not (null? d))
           (tagcase (car d) (ds-var (v k) (k-arrow-kind? k)) (ds-fun (f) #t) (else y #f))))))
;; Binder `b`'s name.
(define k-binder-name (subr kreads ((productof (1 int) (2 int))) symbol)
  (lambda (b) (k-dvar-name (extract b 1))))
(define k-binder-names (subr (maxeff kreads spin) (k-binders) k-names)
  (lambda (bs) (if (null? bs) nil (cons (k-binder-name (car bs)) (k-binder-names (cdr bs))))))

;; `(select m t)`: as written, for checking to resolve where `m` is bound.
(define k-parse-select (subr (maxeff checks spin) (syn k-syns) int)
  (lambda (s items)
    (cond ((not (= (k-length items) 3)) (k-sfail "`(select module name)`" s))
          ((and (syn-symbol? (k-nth items 1)) (syn-symbol? (k-nth items 2)))
           (k-ty-new (ty-select (syn-head (k-nth items 1)) (syn-head (k-nth items 2)))))
          (else (k-sfail "`(select module name)`: a module's name, and a component's" s)))))
;; Function `f`, given `have` descriptions at `s`, where it takes `want`.
(define k-arity-fail (subr (maxeff checks spin) (int int int syn) void)
  (lambda (f want have s) (k-sfail (k-fun-arity-message f want have) s)))
;; Function `f`, at `s`, giving a `result` where a `wanted` is.
(define k-gives-fail (subr (maxeff checks spin) (int int string syn) void)
  (lambda (f result wanted s)
    (k-sfail (k-cat5 (k-quote (k-show-ty f)) " gives a description of kind " (k-kind-text result)
                     ", not " wanted)
             s)))
;; Function `f`, at `s`, not giving a `wanted`.
(define k-not-giving (subr (maxeff checks spin) (int string syn) void)
  (lambda (f wanted s) (k-sfail (k-cat3 (k-quote (k-show-ty f)) " does not give " wanted) s)))

(define-rec
  ;; A description of kind `k`, as written.
  (k-parse-desc-at (subr (maxeff checks spin) (syn int) k-desc)
    (lambda (s k)
      (cond ((k-type-kind? k) (dt (k-parse-type s)))
            ((= k 0) (dr (k-parse-region s)))
            ((= k 3) (dr (k-parse-place s)))
            ((= k 1) (de (k-parse-effect s)))
            ((= k 5) (dz (k-parse-size s)))
            ((= k 6) (dc (k-parse-conv s)))
            (else (df (k-parse-fun s k))))))
  ;; Descriptions `xs`, each of its kind in `ks`.
  (k-parse-descs-at (subr (maxeff checks spin) (k-syns k-ids) k-descs)
    (lambda (xs ks)
      (if (null? xs)
          nil
          (let ((d (k-parse-desc-at (car xs) (car ks))))
            (cons d (k-parse-descs-at (cdr xs) (cdr ks)))))))
  ;; Description `s`, of kind `k` if that is known (not -1).
  (k-parse-desc-of (subr (maxeff checks spin) (syn int) k-desc)
    (lambda (s k) (if (>= k 0) (k-parse-desc-at s k) (k-parse-d s))))
  ;; A description function, as written where one of kind `want` (-1 if not
  ;; known) is wanted.
  (k-parse-fun (subr (maxeff checks spin) (syn int) int)
    (lambda (s want)
      (let* ((f (k-parse-fun-node s want)) (got (k-fun-kind f)))
        (if (and (>= want 0) (>= got 0) (not (= got want)))
            (k-sfail (k-cat4 "a description function of kind " (k-kind-text want)
                             " is wanted, and this is of kind " (k-kind-text got))
                     s)
            f))))
  (k-parse-fun-node (subr (maxeff checks spin) (syn int) int)
    (lambda (s want)
      (if (syn-symbol? s)
          (k-fun-named s)
          (let ((usage (string-append "a description function: a name, `(dlambda ((name kind) …) "
                                      "description)` or `(select module name)`")))
            (tagcase s
              (lst (items d a b)
                (let ((hd (k-symbol-head items)))
                  (cond ((string=? hd "dlambda") (k-parse-dlambda s items want))
                        ((string=? hd "select") (k-parse-select s items))
                        ((k-fun-bound? hd) (k-parse-fun-app s items))
                        (else (k-sfail usage s)))))
              (else x (k-sfail usage s)))))))
  ;; `(dlambda ((x k) …) d)`.
  (k-parse-dlambda (subr (maxeff checks spin) (syn k-syns int) int)
    (lambda (s items want)
      (if (not (= (k-length items) 3))
          (k-sfail "`(dlambda ((name kind) …) description)`" s)
          (let* ((result (if (>= want 0) (k-arrow-result want) -1))
                 (saved (get k-dscope))
                 (bs (k-parse-binders (k-nth items 1)))
                 (none (if (null? bs) (k-sfail k-dlambda-empty (k-nth items 1)) #u))
                 (body (k-parse-desc-of (k-nth items 2) result)))
            (begin (set k-dscope saved) (k-lam bs body))))))
  ;; `(g d …)`, where `g` gives a description function.
  (k-parse-fun-app (subr (maxeff checks spin) (syn k-syns) int)
    (lambda (s items)
      (let* ((g (k-parse-fun (car items) -1))
             (shown (k-quote (k-show-ty g)))
             (parts (k-arrow-parts (k-fun-kind g)))
             (no (k-cat3 shown " does not give a description function" "")))
        (cond ((or (null? parts) (not (k-arrow-kind? (cdr (car parts))))) (k-sfail no s))
              ((not (= (k-length (cdr items)) (k-length (car (car parts)))))
               (k-arity-fail g (k-length (car (car parts))) (k-length (cdr items)) s))
              (else
               (let ((d (k-apply-fun g (k-parse-descs-at (cdr items) (car (car parts))))))
                 (tagcase d (df (f) f) (else y (k-sfail no s)))))))))
  ;; A description function named.
  (k-fun-named (subr (maxeff checks spin) (syn) int)
    (lambda (s)
      (let* ((n (syn-name s)) (sym (string->symbol n)) (d (k-lookup-desc sym))
             (no (k-cat3 (k-quote n) " is not a description function" "")))
        (if (null? d)
            (let ((ctor (k-ctor-params n)))
              (if (null? ctor) (k-sfail no s) (k-ctor-eta n (car ctor))))
            (tagcase (car d)
              (ds-var (v k) (if (k-arrow-kind? k) (k-ty-new (ty-var v)) (k-sfail no s)))
              (ds-fun (f) f)
              (ds-abbrev (ps body) (if (null? ps) (k-sfail no s) (k-abbrev-eta s sym ps body)))
              (ds-gen (g)
                (let ((ps (extract (k-gen-of g) 2)))
                  (if (null? ps) (k-sfail no s) (k-gen-eta g ps))))
              (else x (k-sfail no s)))))))
  ;; A type family as a description function: `(dlambda ((p k) …) (name p …))`.
  (k-abbrev-eta (subr (maxeff checks spin) (syn symbol k-params syn) int)
    (lambda (s name ps body)
      (let* ((bs (k-fresh-named (k-params-names ps) (k-params-kinds ps)))
             (t (if (> (get k-expanding) 64)
                    (k-endless s name)
                    (k-expand-bound s name body (k-binders-as-scope bs)))))
        (k-lam bs (dt t)))))
  ;; A generative type as one.
  (k-gen-eta (subr (maxeff checks spin) (int k-binders) int)
    (lambda (g ps)
      (let* ((bs (k-fresh-named (k-binder-names ps) (k-binder-kinds ps)))
             (t (k-ty-new (ty-named g (k-binders-as-descs bs)))))
        (k-lam bs (dt t)))))
  ;; A type form, `listof` and kin, as one.
  (k-ctor-eta (subr (maxeff checks spin) (string k-params) int)
    (lambda (n ps)
      (let ((bs (k-fresh-named (k-params-names ps) (k-params-kinds ps))))
        (k-lam bs (dt (k-ctor-type n bs))))))
  ;; `(f d …)` as a type: `f` given the descriptions `args` are, of the
  ;; kinds it takes; reduced, if it is a `dlambda`. Where `f`'s kind is not
  ;; known yet (a `select`), what it is given is read by its shape, and
  ;; checked once it is resolved.
  (k-parse-app (subr (maxeff checks spin) (syn int k-syns) int)
    (lambda (s f args)
      (let ((parts (k-arrow-parts (k-fun-kind f))))
        (if (null? parts)
            (k-ty-new (ty-app f (k-parse-ds args)))
            (let ((ps (car (car parts))) (result (cdr (car parts))))
              (cond ((not (= (k-length args) (k-length ps)))
                     (k-arity-fail f (k-length ps) (k-length args) s))
                    ((not (k-type-kind? result)) (k-gives-fail f result "a type" s))
                    (else
                     (tagcase (k-apply-fun f (k-parse-descs-at args ps))
                       (dt (t) t)
                       (else y (k-not-giving f "a type" s))))))))))
  (k-parse-ds (subr (maxeff checks spin) (k-syns) k-descs)
    (lambda (xs)
      (if (null? xs) nil (let ((d (k-parse-d (car xs)))) (cons d (k-parse-ds (cdr xs)))))))
  ;; `(e d …)` in an effect, where `e` is a description function to an
  ;; effect: its effect, reduced if it is a `dlambda`; none if `items` are
  ;; no such application.
  (k-parse-effect-app (subr (maxeff checks spin) (syn k-syns) (listof k-eff acyclic))
    (lambda (s items)
      (let ((f (if (null? items)
                   -1
                   (let ((head (car items)))
                     (if (syn-symbol? head)
                         (if (k-fun-bound? (syn-name head)) (k-fun-named head) -1)
                         (if (string=? (k-list-head head) "dlambda") (k-parse-fun head -1) -1))))))
        (if (< f 0)
            nil
            (let ((parts (k-arrow-parts (k-fun-kind f))))
              (if (null? parts)
                  nil
                  (let ((ps (car (car parts))) (result (cdr (car parts))))
                    (cond ((not (= result 1)) (k-gives-fail f result "an effect" s))
                          ((not (= (k-length (cdr items)) (k-length ps)))
                           (k-arity-fail f (k-length ps) (k-length (cdr items)) s))
                          (else
                           (tagcase (k-apply-fun f (k-parse-descs-at (cdr items) ps))
                             (de (e) (the (listof k-eff acyclic) (cons e nil)))
                             (else y (k-not-giving f "an effect" s)))))))))))))
(set k-fun-reader k-parse-fun)
(set k-app-reader k-parse-app)
(set k-effect-app-reader k-parse-effect-app)
