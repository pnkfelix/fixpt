;;; The compiler from FX-26 to cellular words, in FX-26: what the checker
;;; found of the program being compiled, by expression, in tables: each
;;; datum's layout, each conversion, reshaping, `with`, `stage`, call's
;;; convention and effect summary (`checked-extracts`). Apart from
;;; `compile.fx` since 2026-10-31 (`TODO.md` §188): `compile.fx` makes it, of
;;; the modules it is given, and gives on what it defines.


;; Its types, those it uses of the files before it, and the signatures of
;; what it is given.
(let* ((compile-types (load-module "fx26:compile-types.fx"))
       (parser-types ((proj (load-module "fx26:parser-types.fx") @s @e @m @c @p)))
       (check-env-types (load-module "fx26:check-env-types.fx"))
       (check-types-types (load-module "fx26:check-types-types.fx"))
       (table-types (load-module "fx26:table-types.fx"))
       (layout-types (load-module "fx26:layout-types.fx"))
       (check-resolve-types (load-module "fx26:check-resolve-types.fx")))
  ;; What it is given: the modules of the files before it that it uses.
  (lambda ((layout (select layout-types layout-sig))
           (check-resolve (select check-resolve-types check-resolve-sig))
           (check-env (select check-env-types check-env-sig))
           (tables (select table-types tables-sig))
           ;; The parser's module, for where loaded files' places begin.
           (parser (moduleof (val load-base int))))
    (module
(hide (include compile-types) (include parser-types) (include check-env-types)
      (include check-types-types))
;; The types it uses of the files before it.
(define-type table (select table-types table))
;; What it uses of the modules it is given.
(define load-base (with parser load-base))
;; What it uses of the modules it is given: all of each, hidden.
(hide (include layout) (include check-resolve) (include check-env) (include tables))

;; The checker's facts for the program being compiled.
(define c-facts (ref k-facts @k) (new nil))

;; The same, by expression (`k-at`, an expression's identity): each
;; `extract`'s field. A table, so that a program's facts are not searched
;; from the start for each `extract` compiled.
(define c-int-hash (subr pure (int) int) (lambda (a) a))

(define c-int=? (subr pure (int int) bool) (lambda (a b) (= a b)))

;; An expression's identity, as a table's key: where it starts and ends, and
;; which of the expressions there it is. For tables asked once a lambda or
;; a `letrec`; those asked of every expression are by where it starts
;; (`c-by-at`), so that asking makes nothing.
(define c-span-key (->* (int int int) k-at)
  (lambda (a b k) (product (1 a) (2 b) (3 k))))
(define c-at-hash (subr pure (k-at) int) (lambda (x) (extract x 1)))
(define c-at-is? (->* (k-at int int int) bool) (lambda (x a b k) (k-at-is? x a b k)))
(define c-at=? (subr pure (k-at k-at) bool)
  (lambda (x y) (k-at-is? x (extract y 1) (extract y 2) (extract y 3))))

;; What `t` notes of `a` `b` `k`, the newest; or `none`.
(define c-noted-in
  (->* ((listof c-noted acyclic) int int int int) int)
  (lambda (ns a b k none)
    (cond ((null? ns) none)
          ((k-at-is? (extract (car ns) 1) a b k) (extract (car ns) 2))
          (else (c-noted-in (cdr ns) a b k none)))))
(define c-noted-at (->* (c-by-at int int int int) int)
  (lambda (t a b k none) (c-noted-in (table-ref t a nil) a b k none)))
;; The same of expression `x`: where it ends, and which it is there, found
;; only if something is noted where it starts, as little is.
(define c-noted-of (->* (c-by-at exp int) int)
  (lambda (t x none)
    (let ((ns (table-ref t (exp-start x) nil)))
      (if (null? ns) none (c-noted-in ns (exp-start x) (exp-end x) (exp-kth x) none)))))
;; `t` noting `n` of `at`, over what it noted before.
(define c-note! (->* (c-by-at k-at int) unit)
  (lambda (t at n)
    (let ((a (extract at 1)))
      (table-set! t a (the (listof c-noted acyclic)
                        (cons (product (1 at) (2 n)) (table-ref t a nil)))))))
(define c-new-by-at (subr (alloc @k) () c-by-at) (lambda () (make-table c-int-hash c-int=?)))

(define c-fact-table (ref c-datums-at @k) (new (make-table c-int-hash c-int=?)))

;; The procedures lambda-lifted, by index; and, by where each `letrec` is
;; (`c-span-key`), its members' (none if it is not lifted), so that its
;; register code lifts it as its stack code did, with the same words.
(define c-lifts (ref (table int c-lift @k) @k) (new (make-table c-int-hash c-int=?)))

(define c-lift-count (ref int @k) (new 0))

(define c-lifted (ref (table k-at c-lifting @k) @k) (new (make-table c-at-hash c-at=?)))

;; The parameters a lifting added to the lambda about to be compiled.
(define c-lifting-added (ref int @k) (new 0))

;; Each expression's effect summary, the greatest noted of it.
(define c-summary-table (ref c-by-at @k) (new (c-new-by-at)))

;; Each procedure converted to a convention (`k-convert-at`): what
;; `%fx26-convert` is given for it.
(define c-convert-table (ref c-by-at @k) (new (c-new-by-at)))

;; What `%fx26-convert` is given for `x`, if it is converted; or -1.
(define c-conversion-at (->* (exp) int)
  (lambda (x) (c-noted-of (get c-convert-table) x -1)))

;; Each `stage`'s code, few (`n-staged`); what `x` is checked against, if
;; it is one: a list of one.
(define c-staged-texts (ref c-staged-list @k) (new nil))
(define c-staged-at (->* (exp) c-staged-list)
  (lambda (x) (c-staged-find (get c-staged-texts) (exp-start x) (exp-end x) (exp-kth x))))
(define c-staged-find (->* (c-staged-list int int int) c-staged-list)
  (lambda (l a b k)
    (cond ((null? l) nil)
          ((c-at-is? (extract (car l) 1) a b k) (the c-staged-list (cons (car l) nil)))
          (else (c-staged-find (cdr l) a b k)))))
;; Each `apply` whose list the checker found at `acyclic` (`n-apply-shares`,
;; `k-note-apply-shares`). Every other `apply` copies its list.
(define c-shares-table (ref c-by-at @k) (new (c-new-by-at)))
;; Each definition's value that is a list nothing writes (`n-frozen-define`,
;; `k-note-frozen-define`).
(define c-frozen-table (ref c-by-at @k) (new (c-new-by-at)))
;; Each `(with #%fx n)` that is the plain `n` (`n-plain-fx`, `k-synth-fx`).
(define c-plain-table (ref c-by-at @k) (new (c-new-by-at)))
(define c-plain-fx-at (->* (int int int) bool)
  (lambda (a b k) (>= (c-noted-at (get c-plain-table) a b k -1) 0)))
;; Whether the definition's value `a` `b` `k` is such a list.
(define c-frozen-define-at (->* (int int int) bool)
  (lambda (a b k) (>= (c-noted-at (get c-frozen-table) a b k -1) 0)))

;; Whether the `apply` `a` `b` `k` may give its list itself.
(define c-apply-shares-at (->* (int int int) bool)
  (lambda (a b k) (>= (c-noted-at (get c-shares-table) a b k -1) 0)))

;; Each call's callee's convention (`n-call`), by where it starts.
(define c-call-table (ref c-convs-at @k) (new (make-table c-int-hash c-int=?)))
(define c-conv-in
  (->* ((listof c-conv-noted acyclic) int int int) k-conv)
  (lambda (ns a b k)
    (cond ((null? ns) (cv-fx))
          ((k-at-is? (extract (car ns) 1) a b k) (extract (car ns) 2))
          (else (c-conv-in (cdr ns) a b k)))))
;; The convention the call whose operator is `x` is compiled in (noted at
;; the operator, which every place a compiler makes the call has): its
;; callee's, `cellular` or `native`; or `fx`, which looks at the callee's kind, where its type says
;; `fx` or a convention binder, or nothing was noted (Rust's
;; `NodeFacts::call_conv`).
(define c-call-conv-at (->* (int int int) k-conv)
  (lambda (a b k)
    (let ((ns (table-ref (get c-call-table) a nil)))
      (if (null? ns)
          (cv-fx)
          (tagcase (c-conv-in ns a b k)
            (cv-cellular () (cv-cellular)) (cv-native () (cv-native)) (else y (cv-fx)))))))
(define c-call-conv (->* (exp) k-conv)
  (lambda (x) (c-call-conv-at (exp-start x) (exp-end x) (exp-kth x))))
;; What the checker found the operation `a` `b` `k` takes (`k-datum`), in a
;; list of one; none if nothing.
(define c-datum-in
  (->* ((listof c-datum-noted acyclic) int int int) k-datums)
  (lambda (ns a b k)
    (cond ((null? ns) nil)
          ((k-at-is? (extract (car ns) 1) a b k) (the k-datums (cons (extract (car ns) 2) nil)))
          (else (c-datum-in (cdr ns) a b k)))))
(define c-datum-at (->* (int int int) k-datums)
  (lambda (a b k) (c-datum-in (table-ref (get c-fact-table) a nil) a b k)))
;; The same of an operation that holds `got`, if any: a form kept to be
;; inlined holds it (`c-resolve-extracts`).
(define c-datum-of (->* (k-datums int int int) k-datums)
  (lambda (got a b k) (if (null? got) (c-datum-at a b k) got)))

;; Each `with` the checker saw (its `k-with-vals`, as `c-set-facts!` took
;; them), by expression: its module's values' names, in order, and their
;; positions in the module.
;; And each module reshaped (`k-reshapes`), as `c-set-facts!` took them, by
;; expression: the positions of the values it keeps. A module given through
;; a signature is reshaped, so there are many, and every expression is asked
;; after (`c-changed?`).
(define c-reshape-index (ref c-reshape-table @k) (new (make-table c-int-hash c-int=?)))
(define c-index-reshapes! (->* (k-reshape-list) unit)
  (lambda (rs)
    (if (null? rs)
        #u
        (let ((a (extract (extract (car rs) 1) 1)))
          (begin (c-index-reshapes! (cdr rs))
                 (table-set! (get c-reshape-index) a
                             (the k-reshape-list
                               (cons (car rs) (table-ref (get c-reshape-index) a nil)))))))))
(define c-with-index (ref c-with-table @k) (new (make-table c-int-hash c-int=?)))
(define c-index-withs! (->* (k-with-list) unit)
  (lambda (ws)
    (if (null? ws)
        #u
        (let ((a (extract (extract (car ws) 1) 1)))
          (begin (c-index-withs! (cdr ws))
                 (table-set! (get c-with-index) a
                             (the k-with-list
                               (cons (car ws) (table-ref (get c-with-index) a nil)))))))))
;; The `with` `a` `b` `k`, in a list of one; none if the checker did not see
;; it.
(define c-with-in
  (->* (k-with-list int int int) k-with-list)
  (lambda (ws a b k)
    (cond ((null? ws) nil)
          ((k-at-is? (extract (car ws) 1) a b k) ws)
          (else (c-with-in (cdr ws) a b k)))))
;; Its module's values' names, in a list of one; none if it was not seen.
(define c-with-at
  (->* (int int int) c-with-names)
  (lambda (a b k)
    (let ((ws (c-with-in (table-ref (get c-with-index) a nil) a b k)))
      (if (null? ws) nil (the c-with-names (cons (extract (car ws) 2) nil))))))
;; Their positions in the module, likewise.
(define c-with-places-at
  (->* (int int int) (listof k-ids @k))
  (lambda (a b k)
    (let ((ws (c-with-in (table-ref (get c-with-index) a nil) a b k)))
      (if (null? ws) nil (the (listof k-ids @k) (cons (extract (car ws) 3) nil))))))
;; Module `x` reshaped, in a list of one; none if it is not.
(define c-reshape-in
  (->* (k-reshape-list int int int) k-reshape-list)
  (lambda (rs a b k)
    (cond ((null? rs) nil)
          ((k-at-is? (extract (car rs) 1) a b k) rs)
          (else (c-reshape-in (cdr rs) a b k)))))
(define c-reshape-of (->* (exp) k-reshape-list)
  (lambda (x)
    (let* ((a (exp-start x)) (rs (table-ref (get c-reshape-index) a nil)))
      (if (null? rs) rs (c-reshape-in rs a (exp-end x) (exp-kth x))))))
;; The positions of the values the module `x` reshaped keeps, in a list of
;; one; none if it is not reshaped.
(define c-reshape-at (->* (exp) (listof k-picks @k))
  (lambda (x)
    (let ((rs (c-reshape-of x)))
      (if (null? rs) nil (the (listof k-picks @k) (cons (extract (car rs) 2) nil))))))
;; Whether the module `x` is reshaped.
(define c-reshaped-at? (->* (exp) bool)
  (lambda (x) (not (null? (c-reshape-of x)))))
;; Whether `x`'s value is changed as it is given: converted to a
;; convention, or a module reshaped.
(define c-changed? (->* (exp) bool)
  (lambda (x)
    (or (>= (c-conversion-at x) 0) (c-reshaped-at? x) (not (null? (c-staged-at x)))))))))
