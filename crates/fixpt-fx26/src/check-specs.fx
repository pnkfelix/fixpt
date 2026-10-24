;;; The checker, in FX-26: specifications in procedure types, read, as
;;; `specs.rs` reads them: `(subr E ((x int) …) Q (requires p) (ensures r
;;; q))`, propositions of the procedure's own `int`s, `nat`s and `bool`s.
;;; After `check-read-helpers.fx`, before the types' reader, which reads
;;; with it; `check-logic.fx` shows and compares them.

;; Its types, those it uses of the files before it, and the signatures of
;; what it is given.
(let* ((eager-reader-types ((proj (load-module "fx26:eager-reader-types.fx") @s @e @m @c)))
       (parser-types ((proj (load-module "fx26:parser-types.fx") @s @e @m @c @p)))
       (check-types-types (load-module "fx26:check-types-types.fx"))
       (check-read-types (load-module "fx26:check-read-types.fx"))
       (check-env-types (load-module "fx26:check-env-types.fx"))
       (check-syntax-types (load-module "fx26:check-syntax-types.fx"))
       (check-read-helpers-types (load-module "fx26:check-read-helpers-types.fx"))
       (reader-types (load-module "fx26:reader-types.fx")))
  ;; What it is given: the modules of the files before it that it uses.
  (lambda ((check-types (select check-types-types check-types-sig))
           (check-env (select check-env-types check-env-sig))
           (check-read (select check-read-types check-read-sig))
           (check-syntax (select check-syntax-types check-syntax-sig))
           (check-read-helpers (select check-read-helpers-types check-read-helpers-sig))
           (parser (select reader-types parser-sig)))
    (module

;; The types it uses of the files before it.
(hide (include eager-reader-types) (include parser-types) (include check-types-types)
      (include check-read-types))
;; What it uses of the modules it is given: all of each, hidden.
(hide (include check-types) (include check-env) (include check-read) (include check-syntax)
      (include parser))
(import check-read-helpers k-param-name k-no-name)

;; `#t`, `#f` and `#u`, as the FX-26 reader gives them: symbols.
(define k-sym-true symbol (string->symbol "#t"))
(define k-sym-false symbol (string->symbol "#f"))
(define k-sym-unit symbol (string->symbol "#u"))
;; What a proposition may name: each name, what it names (`sx-param i`,
;; `sx-result`), and its type.
(define-type k-snames (listof (productof (1 symbol) (2 k-sx) (3 int)) acyclic))
(define k-sprop-usage string
  (string-append "a proposition: `(< a b)`, `(<= a b)`, `(= a b)`, `(> a b)`, `(>= a b)`, "
                 "`(not p)`, `(and p …)`, `(or p …)`, `(implies p q)`, `#t`, `#f`, "
                 "or a `bool` named"))
(define k-sexpr-usage string
  (string-append "an integer: a literal, an `int` or `nat` named, `(+ a …)`, `(- a b …)` "
                 "or `(* a …)`"))
;; What the clauses say: the `requires` and the `ensures` (none or one each),
;; the result's name.
(define-type k-spec-parts (productof (1 k-sfs) (2 k-sfs) (3 symbol)))
(define k-clauses-usage string
  (string-append "a specification is `(requires proposition)`, then "
                 "`(ensures name proposition)`, each at most once"))

;; Whether `s` is a specification's clause: `(requires …)` or `(ensures …)`.
(define k-spec-clause? (->* (syn) bool)
  (lambda (s)
    (tagcase s
      (lst (items d a b)
        (and (not (null? items)) (syn-symbol? (car items))
             (or (string=? (syn-name (car items)) "requires")
                 (string=? (syn-name (car items)) "ensures"))))
      (else x #f))))
(define k-spec-int? (->* (int) bool)
  (lambda (t)
    (let ((r (k-resolve t))) (or (= r k-int) (tagcase (k-get r) (ty-nat (n) #t) (else y #f))))))
(define k-spec-bool? (->* (int) bool)
  (lambda (t)
    (= (k-resolve t) k-bool)))
;; The first of `names` named `x`, or none.
(define k-sname-find (->* (k-snames symbol) k-snames)
  (lambda (ns x)
    (cond ((null? ns) nil)
          ((symbol=? (extract (car ns) 1) x) ns)
          (else (k-sname-find (cdr ns) x)))))
(define k-sname-missing (->* (syn) void)
  (lambda (s) (k-sfail (k-cat3 "`" (syn-name s) "` names no parameter or result here") s)))
;; Whether `s` is `#t`, `#f` or `#u`, which the FX-26 reader gives as symbols
;; and the Rust one as literals.
(define k-syn-literal-symbol? (->* (syn) bool)
  (lambda (s)
    (and (syn-symbol? s)
         (or (symbol=? (syn-head s) k-sym-true) (symbol=? (syn-head s) k-sym-false)
             (symbol=? (syn-head s) k-sym-unit)))))
;; `s` as a boolean literal, read as one or as `#t` or `#f`: 1, 0, or -1 if
;; it is none (the parser's `case-bool`).
(define k-syn-bool (->* (syn) int)
  (lambda (s)
    (tagcase s
      (atom (d a b)
        (typecase d
          (bool x (if x 1 0))
          (symbol n (cond ((symbol=? n k-sym-true) 1) ((symbol=? n k-sym-false) 0) (else -1)))
          (else y -1)))
      (else x -1))))
(define k-syn-literal-int? (->* (syn) bool)
  (lambda (s) (tagcase s (atom (d a b) (datum-int? d)) (else x #f))))
(define k-syn-literal-int (->* (syn) int)
  (lambda (s) (tagcase s (atom (d a b) (if (datum-int? d) d 0)) (else x 0))))
;; The items of `s`, a list, or the error `usage`.
(define k-spec-items (->* (syn string) k-syns)
  (lambda (s usage) (tagcase s (lst (items d a b) items) (else x (k-sfail usage s)))))
;; The name a list's first item is, or "".
(define k-spec-head (->* (k-syns) string)
  (lambda (items)
    (if (and (not (null? items)) (syn-symbol? (car items))) (syn-name (car items)) "")))

;; An integer: a literal, a name of an `int` or a `nat`, `(+ a …)`, `(- a)`,
;; `(- a b …)`, `(* a …)`.
(define k-spec-expr (->* (syn k-snames) k-sx)
  (lambda (s names)
    (cond ((k-syn-literal-int? s) (sx-lit (k-syn-literal-int s)))
          ((k-syn-literal-symbol? s) (k-sfail k-sexpr-usage s))
          ((syn-symbol? s)
           (let ((found (k-sname-find names (syn-head s))))
             (cond ((null? found) (k-sname-missing s))
                   ((k-spec-int? (extract (car found) 3)) (extract (car found) 2))
                   (else (k-sfail (k-cat3 "`" (syn-name s) "` is not an `int`") s)))))
          ((k-spec-calls? (k-spec-items s k-sexpr-usage))
           (k-spec-call s (k-spec-items s k-sexpr-usage) names #f))
          (else
           (let* ((items (k-spec-items s k-sexpr-usage)) (hd (k-spec-head items))
                  (args (k-spec-exprs (if (null? items) nil (cdr items)) names))
                  (n (k-length args)))
             (cond ((and (string=? hd "+") (>= n 1)) (k-sx-fold args 0))
                   ((and (string=? hd "*") (>= n 1)) (k-sx-fold args 2))
                   ((and (string=? hd "-") (= n 1)) (sx-sub (sx-lit 0) (car args)))
                   ((and (string=? hd "-") (>= n 2)) (k-sx-fold args 1))
                   (else (k-sfail k-sexpr-usage s))))))))
(define k-spec-exprs (->* (k-syns k-snames) k-sxs)
  (lambda (xs names)
    (if (null? xs)
        nil
        (let* ((x (k-spec-expr (car xs) names)) (rest (k-spec-exprs (cdr xs) names)))
          (cons x rest)))))
;; `xs` folded from the left by `+` (0), `-` (1) or `*` (2).
(define k-sx-fold (->* (k-sxs int) k-sx)
  (lambda (xs op) (k-sx-fold-onto (car xs) (cdr xs) op)))
(define k-sx-fold-onto (->* (k-sx k-sxs int) k-sx)
  (lambda (a xs op)
    (if (null? xs)
        a
        (k-sx-fold-onto (case op ((0) (sx-add a (car xs))) ((1) (sx-sub a (car xs)))
                          (else (sx-mul a (car xs))))
                        (cdr xs) op))))

;; A proposition: `(< a b)`, `(<= a b)`, `(= a b)`, `(> a b)`, `(>= a b)` of
;; integers; `(not p)`, `(and p …)`, `(or p …)`, `(implies p q)`; `#t`,
;; `#f`; or a name of a `bool`.
(define k-spec-prop (->* (syn k-snames) k-sf)
  (lambda (s names)
    (cond ((= (k-syn-bool s) 1) (sf-true))
          ((= (k-syn-bool s) 0) (sf-false))
          ((k-syn-literal-symbol? s) (k-sfail k-sprop-usage s))
          ((syn-symbol? s)
           (let ((found (k-sname-find names (syn-head s))))
             (cond ((null? found) (k-sname-missing s))
                   ((k-spec-bool? (extract (car found) 3)) (sf-holds (extract (car found) 2)))
                   (else
                    (k-sfail (k-cat3 "`" (syn-name s) "` is not a `bool`, so not a proposition")
                             s)))))
          (else
           (let* ((items (k-spec-items s k-sprop-usage)) (hd (k-spec-head items))
                  (args (if (null? items) nil (cdr items))) (n (k-length args)))
             (cond ((string=? hd "<") (k-spec-rel s hd args names 0 #f))
                   ((string=? hd "<=") (k-spec-rel s hd args names 1 #f))
                   ((string=? hd "=") (k-spec-rel s hd args names 2 #f))
                   ((string=? hd ">") (k-spec-rel s hd args names 0 #t))
                   ((string=? hd ">=") (k-spec-rel s hd args names 1 #t))
                   ((string=? hd "not")
                    (begin (k-shape (= n 1) "`(not p)`" s) (sf-not (k-spec-prop (car args) names))))
                   ((string=? hd "and") (sf-and (k-spec-props args names)))
                   ((string=? hd "or") (sf-or (k-spec-props args names)))
                   ((string=? hd "implies")
                    (begin
                      (k-shape (= n 2) "`(implies p q)`" s)
                      (let* ((p (k-spec-prop (car args) names))
                             (q (k-spec-prop (k-nth args 1) names)))
                        (sf-implies p q))))
                   ((k-spec-callee? items) (sf-holds (k-spec-call s items names #t)))
                   (else (k-sfail k-sprop-usage s))))))))
;; Of an integer's `(f a …)`, whether it is a call: `f` no arithmetic.
(define k-spec-calls? (->* (k-syns) bool)
  (lambda (items)
    (let ((hd (k-spec-head items)))
      (and (not (string=? hd "+")) (not (string=? hd "-")) (not (string=? hd "*"))
           (k-spec-callee? items)))))
;; Of `(f a …)`, whether `f`'s innermost binding is a global's (a top-level
;; definition's) (`Checker::spec_callee`).
(define k-spec-callee? (->* (k-syns) bool)
  (lambda (items)
    (and (not (null? items)) (syn-symbol? (car items)) (not (k-syn-literal-symbol? (car items)))
         (>= (k-lookup-raw (syn-head (car items))) 0) (k-global? (syn-head (car items))))))
;; `(f a …)`, a logic function's value at its arguments (`Checker::spec_call`):
;; `f` a global procedure, `pure`, of a `bool` result (`want-bool`) or an
;; `int`'s or `nat`'s; each argument an integer, where `f` takes one, or else
;; a parameter or the result, named.
(define k-spec-call (->* (syn k-syns k-snames bool) k-sx)
  (lambda (s items names want-bool)
    (let* ((f (syn-head (car items))) (fname (symbol->string f)) (args (cdr items)))
      (tagcase (k-get (k-resolve (k-lookup-raw f)))
        (ty-subr (e ps r cv sp)
          (begin
            (k-shape (null? e)
                     (k-cat3 "`" fname "` is called in a specification, so must be `pure`") s)
            (if want-bool
                (k-shape (k-spec-bool? r)
                         (k-cat3 "`" fname "` gives no `bool`, so is no proposition") s)
                (k-shape (k-spec-int? r)
                         (k-cat3 "`" fname "` gives no `int` or `nat`, so is no integer") s))
            (k-shape (= (k-length ps) (k-length args))
                     (k-cat5 "`" fname "` takes " (int->string (k-length ps))
                             (string-append " arguments, not " (int->string (k-length args))))
                     s)
            (sx-call f (k-spec-args args ps names fname))))
        (else y
          (k-sfail (k-cat3 "`" fname "` is called in a specification, and is no procedure") s))))))
(define k-spec-args (->* (k-syns k-ids k-snames string) k-sxs)
  (lambda (xs ps names fname)
    (if (null? xs)
        nil
        (let* ((x (k-spec-arg (car xs) (car ps) names fname))
               (rest (k-spec-args (cdr xs) (cdr ps) names fname)))
          (cons x rest)))))
(define k-spec-arg (->* (syn int k-snames string) k-sx)
  (lambda (a p names fname)
    (if (k-spec-int? p)
        (k-spec-expr a names)
        (let ((found (if (and (syn-symbol? a) (not (k-syn-literal-symbol? a)))
                         (k-sname-find names (syn-head a))
                         nil)))
          (if (null? found)
              (k-sfail (k-cat3 "an argument of `" fname
                               "` in a specification: a parameter or the result, named")
                       a)
              (extract (car found) 2))))))
(define k-spec-props (->* (k-syns k-snames) k-sfs)
  (lambda (ps names)
    (if (null? ps)
        nil
        (let* ((p (k-spec-prop (car ps) names)) (rest (k-spec-props (cdr ps) names)))
          (cons p rest)))))
;; `(hd a b)`, relation `r`, its operands the other way round if `swap`.
(define k-spec-rel (->* (syn string k-syns k-snames int bool) k-sf)
  (lambda (s hd args names r swap)
    (begin
      (k-shape (= (k-length args) 2) (k-cat3 "`(" hd " a b)`") s)
      (let* ((x (k-spec-expr (car args) names)) (y (k-spec-expr (k-nth args 1) names)))
        (if swap (sf-rel r y x) (sf-rel r x y))))))

;; Each written parameter's name, `k-no-name` for one not named.
(define k-spec-pnames (->* (k-syns) k-names)
  (lambda (ps)
    (if (null? ps)
        nil
        (let ((n (k-param-name (car ps))))
          (cons (if (null? n) k-no-name (car n)) (k-spec-pnames (cdr ps)))))))
;; The parameters named, from `i`, with their types `ts`.
(define k-spec-snames (->* (k-names k-ids int) k-snames)
  (lambda (ns ts i)
    (cond ((or (null? ns) (null? ts)) nil)
          ((symbol=? (car ns) k-no-name) (k-spec-snames (cdr ns) (cdr ts) (+ i 1)))
          (else (cons (product (1 (car ns)) (2 (sx-param i)) (3 (car ts)))
                      (k-spec-snames (cdr ns) (cdr ts) (+ i 1)))))))
(define k-snames-snoc (->* (k-snames symbol int) k-snames)
  (lambda (ns r t)
    (if (null? ns)
        (cons (product (1 r) (2 (sx-result)) (3 t)) nil)
        (cons (car ns) (k-snames-snoc (cdr ns) r t)))))
;; The clauses `cs` read, onto what is read so far: `req` and `ens` (none
;; or one each), the result's name `rn`.
(define k-spec-clauses (->* (k-syns k-snames int k-sfs k-sfs symbol) k-spec-parts)
  (lambda (cs names result req ens rn)
    (if (null? cs)
        (product (1 req) (2 ens) (3 rn))
        (let* ((c (car cs)) (items (k-spec-items c k-clauses-usage)) (hd (k-spec-head items))
               (n (- (k-length items) 1)))
          (cond ((and (string=? hd "requires") (= n 1) (null? req) (null? ens))
                 (let ((p (k-spec-prop (k-nth items 1) names)))
                   (k-spec-clauses (cdr cs) names result (cons p nil) ens rn)))
                ((and (string=? hd "ensures") (= n 2) (null? ens))
                 (let ((r (k-nth items 1)))
                   (if (and (syn-symbol? r) (not (k-syn-literal-symbol? r)))
                       (let* ((named (k-snames-snoc names (syn-head r) result))
                              (q (k-spec-prop (k-nth items 2) named)))
                         (k-spec-clauses (cdr cs) names result req (cons q nil) (syn-head r)))
                       (k-sfail "the result's name: `(ensures name proposition)`" r))))
                (else (k-sfail k-clauses-usage c)))))))
;; The one of `fs`, none or one, or `#t`.
(define k-sf-one (->* (k-sfs) k-sf) (lambda (fs) (if (null? fs) (sf-true) (car fs))))
;; `t`, a `subr` type just read from `params` (its parameters as written)
;; and `clauses`, with the specification they say (`Checker::specified`).
(define k-specified (->* (int syn k-syns) int)
  (lambda (t params clauses)
    (tagcase (k-get t)
      (ty-subr (e ps r cv sp)
        (let* ((pnames (k-spec-pnames (k-items-or-nil params "parameter types")))
               (got (k-spec-clauses clauses (k-spec-snames pnames ps 0) r nil nil k-no-name))
               ;; What a `(bool …)` result proves, first.
               (ens (cond ((null? sp) (k-sf-one (extract got 2)))
                          ((null? (extract got 2)) (extract (car sp) 4))
                          (else (sf-and (list (extract (car sp) 4) (car (extract got 2)))))))
               (spec (product (1 pnames) (2 (extract got 3)) (3 (k-sf-one (extract got 1)))
                              (4 ens))))
          (k-ty-new (ty-subr e ps r cv (cons spec nil)))))
      (else y t))))
;; The module, the lambda given its modules, and the loads, closed.
)))
