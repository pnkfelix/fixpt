;;; The checker, in FX-26: reading types, one knot (a module's `letrec*`):
;;; type forms and effects (`check-syntax.fx`'s), descriptions and their
;;; functions and kinds (`check-kinds.fx`'s and `check-args.fx`'s), module
;;; types (`check-modules.fx`'s) and dependent parameters
;;; (`check-dependent.fx`'s), each reading the others. After
;;; `check-subst.fx`; part of the checker, `check-types.fx` first.

;; Its types, those it uses of the files before it, and the signatures of
;; what it is given.
(let* ((check-types-types (load-module "fx26:check-types-types.fx"))
       (eager-reader-types ((proj (load-module "fx26:eager-reader-types.fx") @s @e @m @c)))
       (parser-types ((proj (load-module "fx26:parser-types.fx") @s @e @m @c @p)))
       (check-syntax-types (load-module "fx26:check-syntax-types.fx"))
       (check-read-types (load-module "fx26:check-read-types.fx"))
       (check-env-types (load-module "fx26:check-env-types.fx"))
       (check-holds-types (load-module "fx26:check-holds-types.fx"))
       (check-read-helpers-types (load-module "fx26:check-read-helpers-types.fx"))
       (check-subst-types (load-module "fx26:check-subst-types.fx"))
       (check-print-types (load-module "fx26:check-print-types.fx"))
       (check-print-parts-types (load-module "fx26:check-print-parts-types.fx"))
       (check-proving-types (load-module "fx26:check-proving-types.fx"))
       (check-effects-types (load-module "fx26:check-effects-types.fx"))
       (check-unions-types (load-module "fx26:check-unions-types.fx"))
       (reader-types (load-module "fx26:reader-types.fx")))
  ;; What it is given: the modules of the files before it that it uses.
  (lambda ((check-types (select check-types-types check-types-sig))
           (check-read-helpers (select check-read-helpers-types check-read-helpers-sig))
           (check-syntax (select check-syntax-types check-syntax-sig))
           (check-read (select check-read-types check-read-sig))
           (check-subst (select check-subst-types check-subst-sig))
           (check-env (select check-env-types check-env-sig))
           (check-print (select check-print-types check-print-sig))
           (check-holds (select check-holds-types check-holds-sig))
           (check-proving (select check-proving-types check-proving-sig))
           (check-effects (select check-effects-types check-effects-sig))
           (check-unions (select check-unions-types check-unions-sig))
           (parser (select reader-types parser-sig))
           (check-print-parts (select check-print-parts-types check-print-parts-sig)))
    (module

;; The types it uses of the files before it.
(hide (include check-types-types) (include eager-reader-types) (include parser-types)
      (include check-syntax-types) (include check-read-types) (include check-env-types)
      (include check-holds-types))
;; What it uses of the modules it is given: all of each, hidden.
(hide (include check-types) (include check-read-helpers) (include check-syntax)
      (include check-subst) (include check-env) (include check-print-parts) (include check-print)
      (include check-holds) (include check-proving) (include check-unions) (include parser))
(import check-read k-at-name? k-atom-head? k-ctor-params k-effect-desc k-effect-named
        k-effect-selected k-frozen-into k-head k-items k-items-or-nil k-name-of k-not-applied
        k-parse-binders k-parse-place k-parse-region k-region-constant k-sfail k-symbol-head)
(import check-effects k-one k-union)

(define k-effects (->* (k-syns) k-eff)
  (lambda (xs)
    (if (null? xs)
        nil
        (let* ((e (k-parse-effect (car xs))) (rest (k-effects (cdr xs)))) (k-union e rest)))))
(define k-parse-effect (->* (syn) k-eff)
  (lambda (s)
    (if (syn-symbol? s)
        (k-effect-named s)
        (let* ((items (k-items s "an effect"))
               (head (k-head items))
               ;; `(select m e)`: module `m`'s effect `e`, found where the
               ;; type it is in is checked, as a type's `select` is.
               (selected (if (string=? head "select")
                             (k-effect-selected s items)
                             (the (listof k-eff acyclic) nil)))
               ;; `(e d …)`: a description function to an effect, applied.
               (applied (if (null? selected) (k-parse-effect-app s items) selected)))
          (cond ((not (null? selected)) (car selected))
                ((not (null? applied)) (car applied))
                ((string=? head "maxeff") (k-effects (cdr items)))
                ((string=? head "io") (k-io-atom s items))
                ((k-atom-head? head)
                 (if (= (k-length items) 2)
                     (k-effect-atom head (k-nth items 1))
                     (k-sfail (k-cat3 "`(" head " region)`") s)))
                (else (k-sfail "expected an effect" s)))))))
;; `(io k)`, `k` a kind of the fixed family (`TODO.md` §84).
(define k-io-atom (->* (syn k-syns) k-eff)
  (lambda (s items)
    (if (= (k-length items) 2)
        (let* ((x (k-nth items 1)) (k (if (syn-symbol? x) (k-io-kind-code (syn-name x)) -1)))
          (if (< k 0)
              (k-sfail (string-append "an I/O effect's kind is one of " k-io-kinds-shown) x)
              (k-one (a-io k))))
        (k-sfail (string-append "`(io kind)`, the kind one of " k-io-kinds-shown) s))))
;; Whether `s` is written as a size, not a region (`Checker::size_written`):
;; a natural literal, `finite`, a size variable or value, `(+ …)`, `(- …)`.
(define k-size-written? (->* (syn) bool)
  (lambda (s)
    (cond ((>= (syn-int s) 0) #t)
          ((syn-symbol? s)
           (or (string=? (syn-name s) "finite")
               (let ((d (k-lookup-desc (syn-head s))))
                 (and (not (null? d))
                      (tagcase (car d) (ds-var (v k) (= k 5)) (ds-size (z) #t) (else x #f))))))
          (else
           (let ((items (tagcase s
                          (lst (items d a b) items)
                          (else x (the k-syns nil)))))
             (and (not (null? items)) (syn-symbol? (car items))
                  (case (syn-name (car items)) (("+" "-") #t) (else #f))))))))
(define k-parse-types (->* (k-syns) k-ids)
  (lambda (xs)
    (if (null? xs)
        nil
        (let* ((t (k-parse-type (car xs))) (rest (k-parse-types (cdr xs)))) (cons t rest)))))
(define k-parse-parts (->* (k-syns k-parts) k-parts)
  (lambda (ps done)
    (if (null? ps)
        (reverse done)
        (let ((pair (k-items (car ps) "`(label type)`")))
          (if (= (k-length pair) 2)
              (let ((l (k-syn-label (car pair))))
                (if (k-has-label? done l)
                    (k-sfail (k-twice (symbol->string l)) (car ps))
                    (let ((t (k-parse-type (k-nth pair 1))))
                      (k-parse-parts (cdr ps) (cons (product (1 l) (2 t)) done)))))
              (k-sfail "`(label type)`" (car ps)))))))
;; Storage written: a procedure kept there may not reach itself unsaid
;; (`spin`).
(define k-parse-type (->* (syn) int)
  (lambda (s)
    (let* ((star (get k-arrow-star))
           (taken (set k-arrow-star #f))
           (t (if star (k-parse-arrow-star s) (k-parse-type-node s)))
           (marked (if star (set k-arrow-star-tys (cons t (get k-arrow-star-tys))) #u)))
      (begin
        (if (and (not (syn-symbol? s)) (k-storage-head? (k-head (k-items s "a type"))))
            (k-no-knot t (syn-start s) (syn-end s))
            #u)
        t))))
;; What `(proves prop)` states: the type of its proof, with the lemma kept
;; pending for the definition it declares.
(define k-parse-proves (->* (syn string) int)
  (lambda (prop usage)
    (let* ((items (k-items prop "a proposition"))
           (head (k-symbol-head items))
           (poly? (string=? head "poly"))
           (shape (cond (poly? (if (>= (k-length items) 3) #u (k-sfail usage prop)))
                        ((string=? head "<=") #u)
                        (else (k-sfail usage prop))))
           (bs (if poly? (k-parse-binders (k-nth items 1)) (the k-binders nil)))
           (conc (k-le (if poly? (k-nth items 2) prop)))
           (hyps (if poly? (k-les (cdr (cdr (cdr items)))) (the k-hyps nil)))
           (spin (k-one (a-spin)))
           (params (k-hyp-coercions hyps spin (the k-ids (cons (car conc) nil))))
           (body (k-ty-new (ty-subr spin params (cdr conc) (get k-conv-default))))
           (t (if (null? bs) body (k-ty-new (ty-poly bs body)))))
      (begin
        (set k-pending-lemma (cons (k-stated-lemma bs conc hyps) nil))
        t))))
(define k-le (->* (syn) (pairof int int @t))
  (lambda (s)
    (let ((items (k-items s "a proposition")))
      (if (and (= (k-length items) 3) (string=? (k-symbol-head items) "<="))
          (let* ((a (k-parse-type (k-nth items 1))) (b (k-parse-type (k-nth items 2))))
            (cons a b))
          (k-sfail "a proposition is `(<= type type)`" s)))))
(define k-les (->* (k-syns) k-hyps)
  (lambda (xs)
    (if (null? xs) nil (let* ((h (k-le (car xs))) (rest (k-les (cdr xs)))) (cons h rest)))))
;; `(name d …)` for the `g`th generative type: a node, never expanded.
(define k-apply-gen (->* (syn int k-syns) int)
  (lambda (s g args)
    (let* ((gen (k-gen-of g)) (ps (extract gen 2)))
      (if (not (= (k-length args) (k-length ps)))
          (k-sfail (k-arity-message (extract gen 1) (k-length ps) (k-length args)) s)
          (let ((t (k-ty-new (ty-named g (k-gen-args ps args)))))
            ;; What it holds may keep a procedure that reaches itself.
            (begin (k-no-knot t (syn-start s) (syn-end s)) t))))))
(define k-gen-args (->* (k-binders k-syns) k-descs)
  (lambda (ps args)
    (if (null? ps)
        nil
        (let* ((k (extract (car ps) 2))
               (d (cond ((k-type-kind? k) (dt (k-parse-type (car args))))
                        ((= k 7) (dt (k-parse-flat (car args))))
                        ((= k 0) (dr (k-parse-region (car args))))
                        ((= k 3) (dr (k-parse-place (car args))))
                        ((= k 5) (dz (k-parse-size (car args))))
                        ((= k 6) (dc (k-parse-conv (car args))))
                        ((>= k 100) (df (k-parse-fun (car args) k)))
                        (else (de (k-parse-effect (car args))))))
               (rest (k-gen-args (cdr ps) (cdr args))))
          (cons d rest)))))
;; A type name nothing defines: in a module with `include`s (marked by
;; `k-include-mark`), the modules included's, found when they are typed (`TODO.md`
;; §69), as `parse.rs`; else what `no` says.
(define k-type-unknown
  (->* (symbol syn (subr (maxeff checks spin) () string)) int)
  (lambda (sym s no)
    (if (not (null? (k-lookup-desc '%include-scope)))
        (k-ty-new (ty-select '%include sym))
        (k-sfail (no) s))))
;; The type a name stands for.
(define k-type-named (->* (syn) int)
  (lambda (s)
    (let* ((n (syn-name s)) (sym (string->symbol n)) (base (k-find (get k-base) sym)))
      (cond ((string=? n "void") k-void)
            ;; The empty list's own type (`docs/research/logical-types.md`, L1).
            ((and (string=? n "nil") (null? (k-lookup-desc sym))) (k-ty-new (ty-nil)))
            ((and (string=? n "false") (null? (k-lookup-desc sym))) (k-ty-new (ty-false)))
            ((and (string=? n "nat") (null? (k-lookup-desc sym)))
             (k-ty-new (ty-nat (sz-finite))))
            ;; A standard type, unless the program defines the name itself
            ;; (`TODO.md` §88), as it may `nil` and the rest above.
            ((and (>= base 0) (null? (k-lookup-desc sym))) base)
            (else
             ;; In `with` bodies, the modules' names first (`k-with-selected`).
             (let ((withs (k-withs-over sym)))
               (if (null? withs)
                   (k-type-name-read s n sym)
                   (k-with-selected
                     withs sym
                     (if (or (not (null? (k-lookup-desc sym)))
                             (not (null? (k-lookup-desc '%include-scope))))
                         (k-type-name-read s n sym)
                         -1)))))))))
;; Type name `n`, `sym`, written `s`, as the description scope and
;; `include`s say.
(define k-type-name-read (->* (syn string symbol) int)
  (lambda (s n sym)
    (let ((d (k-lookup-desc sym))
          (no (lambda () (string-append (k-quote n) " is not a type"))))
      (if (null? d)
          (k-type-unknown sym s no)
          (tagcase (car d)
            (ds-var (v k)
              (cond ((k-type-kind? k) (k-ty-new (ty-var v)))
                    ((= k 7) (k-sfail (k-flat-not-type n) s))
                    ((k-arrow-kind? k) (k-sfail (k-not-applied n k) s))
                    (else (k-sfail (no) s))))
            (ds-fun (f)
              (let ((k (k-fun-kind f))) (k-sfail (k-not-applied n (if (< k 0) 2 k)) s)))
            (ds-rec (t) (if (k-flat-var-type? t) (k-sfail (k-flat-not-type n) s) t))
            (ds-gen (g) (k-apply-gen s g nil))
            (else x (k-sfail (no) s)))))))
(define k-parse-type-node (->* (syn) int)
  (lambda (s)
    (if (syn-symbol? s)
        (k-type-named s)
        (let* ((items (k-items s "a type"))
               (hd (if (null? items) '|()| (syn-head (car items))))
               ;; In `with` bodies, `(f d …)` is the modules' `f` first.
               (withs (if (or (symbol=? hd '|()|) (k-type-form? hd)) nil (k-withs-over hd))))
          (cond ((null? withs) (k-parse-type-list s items hd))
                ((null? (k-lookup-desc hd)) (k-with-applied withs hd (cdr items) -1))
                (else (k-with-applied withs hd (cdr items) (k-parse-type-list s items hd))))))))
;; Type `s`, `(hd …)`, of `items`, as the description scope says.
(define k-parse-type-list (->* (syn k-syns symbol) int)
  (lambda (s items hd)
    (let* ((abbrev (if (symbol=? hd '|()|)
                       (the (listof k-ds acyclic) nil)
                       (k-lookup-desc hd)))
           (alias (k-select-alias abbrev)))
      (cond ((and (not (null? abbrev)) (k-ds-applied? (car abbrev)))
             (tagcase (car abbrev)
               (ds-abbrev (ps body) (k-expand-abbrev s hd ps body (cdr items)))
               (ds-gen (g) (k-apply-gen s g (cdr items)))
               ;; A description function applied (`check-kinds.fx`).
               (ds-var (v k) (k-parse-app s (k-ty-new (ty-var v)) (cdr items)))
               (ds-fun (f) (k-parse-app s f (cdr items)))
               (else x (k-sfail "an abbreviation" s))))
            ((>= alias 0) (k-parse-app s alias (cdr items)))
            ;; `((dlambda …) d …)` and `((select m f) d …)`.
            ((and (not (null? items)) (tagcase (car items) (lst (xs d a b) #t) (else x #f)))
             (k-parse-app s (k-parse-fun (car items) -1) (cdr items)))
            (else (k-parse-type-form s items hd))))))
;; `(f d …)`, its descriptions `args`, read in the bodies of `with`s of
;; modules `withs` (innermost first): `((select m f) d …)` of the innermost,
;; which, where `m` does not give `f`, is the next's, and so on out to
;; `outer`, what it means here otherwise, or -1. As `parse.rs`'s
;; `with_applied`.
(define k-with-applied (->* (k-names symbol k-syns int) int)
  (lambda (withs f args outer)
    (if (null? withs)
        outer
        (let* ((t (k-with-applied (cdr withs) f args outer))
               (fun (k-ty-new (ty-select (car withs) f)))
               (app (k-ty-new (ty-app fun (k-parse-ds args)))))
          (begin (set k-with-fallbacks (cons (product (1 fun) (2 t)) (get k-with-fallbacks)))
                 (set k-with-apps (cons (product (1 fun) (2 app)) (get k-with-apps)))
                 app)))))
;; A procedure type's parameters and result, after its effect, with its
;; convention: `(subr …)`'s and `(-> …)`'s.
(define k-subr-type (->* (k-eff syn syn k-conv) int)
  (lambda (e params result cv)
    (let ((ts (k-read-params (k-items-or-nil params "parameter types") result)))
      (k-ty-new (ty-subr e (k-ids-but-last ts) (k-ids-last ts) cv)))))
;; `(subr effect (param …) result)`, or with a convention first, `(subr
;; (conv C) effect (param …) result)`; left out, it is the program's.
(define k-parse-subr (->* (syn k-syns) int)
  (lambda (s items)
    (let* ((conv? (and (= (k-length items) 5) (string=? (k-list-head (k-nth items 1)) "conv")))
           (cv (if conv? (k-parse-conv-form (k-nth items 1)) (get k-conv-default)))
           (items (if conv? (the k-syns (cons (car items) (cdr (cdr items)))) items)))
      (begin
        (k-shape (= (k-length items) 4) "`(subr effect (param …) result)`" s)
        (k-subr-type (k-parse-effect (k-nth items 1)) (k-nth items 2) (k-nth items 3) cv)))))
;; Whether signature `s` is `(->* …)`, under any `poly`s.
(define k-written-arrow-star? (->* (syn) bool)
  (lambda (s)
    (tagcase s
      (lst (xs d a b)
        (let ((head (k-symbol-head xs)))
          (or (string=? head "->*")
              (and (string=? head "poly") (= (k-length xs) 3)
                   (k-written-arrow-star? (k-nth xs 2))))))
      (else y #f))))
;; A definition's signature that may be `(->* (param …) result)`, under any
;; `poly`s: read as `(subr pure (param …) result)`, the effect the
;; definition then finds standing in for its own (`check-program.fx`).
(define k-parse-arrow-star (->* (syn) int)
  (lambda (s)
    (let* ((items (k-items s "a type")) (head (k-symbol-head items)))
      (cond ((string=? head "->*")
             (begin
               (k-shape (= (k-length items) 3) "`(->* (param …) result)`" s)
               (k-subr-type nil (k-nth items 1) (k-nth items 2) (get k-conv-default))))
            ((string=? head "poly")
             (begin (set k-arrow-star #t)
                    (let ((t (k-parse-type-node s))) (begin (set k-arrow-star #f) t))))
            (else (k-parse-type-node s))))))
;; `(-> (param …) result)`: `(subr pure (param …) result)`.
(define k-parse-arrow (->* (syn k-syns) int)
  (lambda (s items)
    (begin
      (k-shape (= (k-length items) 3) "`(-> (param …) result)`" s)
      (k-subr-type nil (k-nth items 1) (k-nth items 2) (get k-conv-default)))))
;; `(proves prop)`.
(define k-parse-proves-type (->* (syn k-syns) int)
  (lambda (s items)
    (let ((usage (string-append "`(proves (<= type type))` or `(proves (poly ((name kind) …) "
                                "(<= type type) (<= type type) …))`")))
      (begin
        (k-shape (= (k-length items) 2) usage s)
        (let* ((saved (get k-dscope)) (t (k-parse-proves (k-nth items 1) usage)))
          (begin (set k-dscope saved) t))))))
;; A type written as a form, `(hd …)`, `hd` no family's name.
(define k-parse-type-form (->* (syn k-syns symbol) int)
  (lambda (s items hd)
    (let ((n (k-length items)))
      (case hd
        ((subr) (k-parse-subr s items))
        ((->) (k-parse-arrow s items))
        ((->*) (k-sfail k-arrow-star-only s))
        ((proves) (k-parse-proves-type s items))
        ((bool) (k-sfail "`(bool …)` is a procedure's result, and only that" s))
        ((poly)
         (begin
           (k-shape (= n 3) "`(poly ((name kind) …) type)`" s)
           (let* ((saved (get k-dscope))
                  (bs (k-parse-binders (k-nth items 1)))
                  (body (k-parse-type (k-nth items 2))))
             (begin (set k-dscope saved) (k-ty-new (ty-poly bs body))))))
        ((nlist)
         (begin
           (k-shape (or (= n 3) (= n 4)) "`(nlist type size)` or `(nlist type size place)`" s)
           (let* ((e (k-parse-type (k-nth items 1)))
                  (z (k-parse-size (k-nth items 2)))
                  (r (if (= n 4)
                         (k-frozen-into (k-parse-place (k-nth items 3)) #t)
                         (r-frozen -1 #t))))
             (k-ty-new (ty-nlist e z r)))))
        ((nat)
         (begin
           (k-shape (= n 2) "`(nat size)`" s)
           (k-ty-new (ty-nat (k-parse-size (k-nth items 1))))))
        ((ref)
         (begin
           (k-shape (= n 3) "`(ref type region)`" s)
           (let* ((t (k-parse-type (k-nth items 1))) (r (k-parse-region (k-nth items 2))))
             (k-ty-new (ty-ref t r)))))
        ((pairof)
         (begin
           (k-shape (= n 4) "`(pairof type type region)`" s)
           (let* ((a (k-parse-type (k-nth items 1))) (b (k-parse-type (k-nth items 2)))
                  (r (k-parse-region (k-nth items 3))))
             (k-ty-new (ty-pair a b r #f)))))
        ((union) (k-parse-union s items))
        ((dletrec) (k-parse-dletrec s items))
        ((mu) (k-parse-mu s items))
        ((listof)
         (begin
           (k-shape (= n 3) "`(listof type region)`" s)
           (let* ((t (k-parse-type (k-nth items 1))) (r (k-parse-region (k-nth items 2)))
                  (slot (k-slot)) (pair (k-ty-new (ty-pair t slot r #t))))
             (begin (k-set-link slot pair) slot))))
        ((prompt-tag)
         (begin
           (k-shape (= n 5) "`(prompt-tag answer payload effect region)`" s)
           (let* ((a (k-parse-type (k-nth items 1))) (h (k-parse-type (k-nth items 2)))
                  (e (k-parse-effect (k-nth items 3))) (r (k-parse-region (k-nth items 4))))
             (k-ty-new (ty-tag a h e r)))))
        ((composable oneshot)
         (let ((once (symbol=? hd 'oneshot)))
           (begin
             (k-shape (= n 5) (if once
                                  "`(oneshot argument answer effect region)`"
                                  "`(composable argument answer effect region)`")
                      s)
             (let* ((t (k-parse-type (k-nth items 1))) (a (k-parse-type (k-nth items 2)))
                    (e (k-parse-effect (k-nth items 3))) (r (k-parse-region (k-nth items 4))))
               (k-ty-new (ty-comp t a e r once))))))
        ((bloblet)
         (begin
           (k-shape (= n 3) "`(bloblet (fields type …) region)`, or `(frozen type …)`" s)
           (let* ((fields (k-nth items 1))
                  (parts (k-items fields "`(fields type …)`"))
                  (which (k-head parts)))
             (if (or (string=? which "fields") (string=? which "frozen"))
                 (let* ((fs (k-parse-types (cdr parts))) (r (k-parse-region (k-nth items 2))))
                   (k-ty-new (ty-bloblet fs (string=? which "frozen") r)))
                 (k-sfail "`(fields type …)` or `(frozen type …)`" fields)))))
        ((productof) (k-ty-new (ty-product (k-parse-parts (cdr items) nil))))
        ;; With a key, a flat sum (`TODO.md` §77).
        ((sumof) (if (and (> n 1) (syn-symbol? (k-nth items 1)))
                     (k-parse-flat s)
                     (k-ty-new (ty-sum (k-parse-parts (cdr items) nil)))))
        ((arrayof)
         (begin
           (k-shape (= n 3) "`(arrayof type region)`" s)
           ;; With a length, a literal or a size, a flat array (`TODO.md` §77).
           (if (k-size-written? (k-nth items 2))
               (k-parse-flat s)
               (let* ((t (k-parse-type (k-nth items 1))) (r (k-parse-region (k-nth items 2))))
                 (k-ty-new (ty-array t (sz-finite) r))))))
        ;; `(narrayof type size region)`: an array of `size` elements.
        ((narrayof)
         (begin
           (k-shape (= n 4) "`(narrayof type size region)`" s)
           (let* ((t (k-parse-type (k-nth items 1)))
                  (z (k-parse-size (k-nth items 2)))
                  (r (k-parse-region (k-nth items 3))))
             (k-ty-new (ty-array t z r)))))
        ((icell)
         (begin
           (k-shape (= n 3) "`(icell type region)`" s)
           (let* ((t (k-parse-type (k-nth items 1))) (r (k-parse-region (k-nth items 2))))
             (k-ty-new (ty-icell t r)))))
        ((place)
         (begin
           (k-shape (= n 2) "`(place region)`" s)
           (k-ty-new (ty-place (k-parse-place (k-nth items 1))))))
        ((mark-key)
         (begin
           (k-shape (= n 3) "`(mark-key type region)`" s)
           (let* ((t (k-parse-type (k-nth items 1))) (r (k-parse-region (k-nth items 2))))
             (k-ty-new (ty-markkey t r)))))
        (else
         (cond ((k-module-type-head? hd) (k-read-module-type s items hd))
               ;; In a module with `include`s, an unbound name applied: the
               ;; modules included's family (`TODO.md` §69), as `parse.rs`.
               ((and (not (symbol=? hd '|()|)) (not (null? (k-lookup-desc '%include-scope)))
                     (null? (k-lookup-desc hd)))
                (k-parse-app s (k-ty-new (ty-select '%include hd)) (cdr items)))
               (else (k-sfail (k-not-type-list hd) s))))))))
;; `(dletrec ((name type) …) type)`: each name gets a forwarding slot
;; before any body is read, so the bodies can refer to it and each other.
(define k-parse-dletrec (->* (syn k-syns) int)
  (lambda (s items)
    (begin
      (k-shape (= (k-length items) 3) "`(dletrec ((name type) …) type)`" s)
      (let* ((saved (get k-dscope))
             (slots (k-dletrec-slots (k-items (k-nth items 1) "dletrec bindings")))
             (filled (k-dletrec-fill slots))
             (grounded (k-dletrec-grounded slots s))
             (unknotted (k-dletrec-no-knot slots s))
             (body (k-parse-type (k-nth items 2))))
        (begin (set k-dscope saved) body)))))
;; `(mu name type)`: a recursive type, anonymous; the same as `(dletrec
;; ((name type)) name)`.
;; A union of members of disjoint shapes at run time
;; (`docs/research/logical-types.md`, L1), normalized.
(define k-parse-union (->* (syn k-syns) int)
  (lambda (s items)
    (begin
      (k-shape (>= (k-length items) 3) "`(union type type …)`" s)
      (k-union-of (k-parse-types (cdr items)) (syn-start s) (syn-end s)))))
(define k-parse-mu (->* (syn k-syns) int)
  (lambda (s items)
    (begin
      (k-shape (= (k-length items) 3) "`(mu name type)`" s)
      (let* ((name (k-name-of (k-nth items 1) "a name"))
             (saved (get k-dscope))
             (slot (k-slot))
             (pushed (k-push-desc name (ds-rec slot)))
             (t (k-parse-type (k-nth items 2)))
             (restored (set k-dscope saved))
             (filled (k-set-link slot t))
             (grounded (k-grounded slot (syn-start s) (syn-end s))))
        slot))))
(define k-dletrec-fill (->* (k-slots) unit)
  (lambda (ss)
    (if (null? ss)
        #u
        (let ((t (k-parse-type (cdr (car ss)))))
          (begin (k-set-link (car (car ss)) t) (k-dletrec-fill (cdr ss)))))))
;; A use of a parametric abbreviation: its body, read with each parameter
;; bound to the description given for it.
(define k-expand-abbrev (->* (syn symbol k-params syn k-syns) int)
  (lambda (s name ps body args)
    (cond
      ((not (= (k-length args) (k-length ps)))
       (k-sfail (k-arity-message name (k-length ps) (k-length args)) s))
      ((> (get k-expanding) 64) (k-endless s name))
      (else (k-expand-bound s name body (k-abbrev-args ps args))))))
;; The family `name`'s body, read with its parameters bound as `bound`
;; says: a use inside with the same descriptions is the slot its type
;; will fill, a knot.
(define k-expand-bound (->* (syn symbol syn k-scope) int)
  (lambda (s name body bound)
    (let ((knot (k-knot-of (get k-knots) name bound)))
      (if (>= knot 0)
          knot
          (let* ((saved (get k-dscope)) (slot (k-slot)) (kept (get k-knots)))
            (begin
              (set k-knots (cons (product (1 name) (2 bound) (3 slot)) kept))
              (k-push-all bound)
              (set k-expanding (+ (get k-expanding) 1))
              (let ((t (k-parse-type body)))
                (begin (set k-expanding (- (get k-expanding) 1))
                       (set k-dscope saved)
                       (set k-knots kept)
                       (k-set-link slot t)
                       (k-grounded slot (syn-start s) (syn-end s))
                       slot))))))))
(define k-abbrev-args (->* (k-params k-syns) k-scope)
  (lambda (ps args)
    (if (null? ps)
        nil
        (let* ((k (extract (car ps) 2))
               (d (cond ((k-type-kind? k) (ds-rec (k-parse-type (car args))))
                        ((= k 7) (ds-rec (k-parse-flat (car args))))
                        ((= k 0) (ds-region (k-parse-region (car args))))
                        ((= k 3) (ds-region (k-parse-place (car args))))
                        ((= k 5) (ds-size (k-parse-size (car args))))
                        ((= k 6) (ds-conv (k-parse-conv (car args))))
                        ((>= k 100) (ds-fun (k-parse-fun (car args) k)))
                        (else (ds-eff (k-parse-effect (car args))))))
               (rest (k-abbrev-args (cdr ps) (cdr args))))
          (cons (cons (extract (car ps) 1) d) rest)))))
(define k-define-type (->* (symbol syn int int) int)
  (lambda (name def a b)
    (let ((ahead (k-ahead-take name)))
      (if (>= ahead 0)
          ;; Declared ahead: its slot is in scope already; fill it, and check
          ;; it grounded once every slot is filled.
          (let ((t (k-parse-type def)))
            (begin (k-set-link ahead t)
                   (set k-ahead-filled (cons (product (1 ahead) (2 a) (3 b)) (get k-ahead-filled)))
                   ahead))
          (let ((slot (k-slot)))
            (begin
              (k-push-desc name (ds-rec slot))
              (let ((t (k-parse-type def)))
                (begin (k-set-link slot t) (k-grounded slot a b) (k-note-closed slot)))))))))
;; Name or `dlambda` `s`, a description function.
(define k-fun-d (->* (syn) k-desc)
  (lambda (s) (df (k-parse-fun s -1))))
;; A `proj` argument: which kind it is shows in its shape, or, for a bare
;; name, in how the name is bound.
;; A convention, if name `s` is one of FX-26's own; else a type.
(define k-parse-conv-or-type (->* (syn) k-desc)
  (lambda (s)
    (let ((n (syn-name s)))
      (if (or (string=? n "cellular") (string=? n "native") (string=? n "fx"))
          (dc (k-parse-conv s))
          (dt (k-parse-type s))))))
;; What name `s`, meaning `d` (none or one), is as a `proj` argument: by how
;; it is bound; if it is not bound as a description, a convention or a type.
(define k-parse-d-bound (->* (syn (listof k-ds acyclic)) k-desc)
  (lambda (s d)
    (if (null? d)
        (if (null? (k-ctor-params (syn-name s))) (k-parse-conv-or-type s) (k-fun-d s))
        (tagcase (car d)
          (ds-fun (f) (k-fun-d s))
          (ds-abbrev (ps body) (if (null? ps) (k-parse-conv-or-type s) (k-fun-d s)))
          (ds-gen (g)
            (if (null? (extract (k-gen-of g) 2)) (k-parse-conv-or-type s) (k-fun-d s)))
          (ds-var (v k)
            (cond ((>= k 100) (k-fun-d s))
                  ((or (= k 0) (= k 3)) (dr (r-var v)))
                  ((= k 1) (de (k-one (a-var v))))
                  ((= k 5) (dz (k-size-var v)))
                  ((= k 6) (dc (cv-var v)))
                  (else (k-parse-conv-or-type s))))
          (ds-region (r) (dr r))
          (ds-eff (e) (de e))
          (ds-size (z) (dz z))
          (ds-conv (c) (dc c))
          (else x (k-parse-conv-or-type s))))))
;; A `proj` argument that is a name.
(define k-parse-d-name (->* (syn) k-desc)
  (lambda (s)
    (let* ((n (syn-name s)) (sym (string->symbol n)))
      (cond ((k-at-name? n) (dr (k-region-constant sym)))
            ((string=? n "pure") (de nil))
            ((string=? n "spin") (de (k-one (a-spin))))
            ((string=? n "nondet") (de (k-one (a-nondet))))
            ((string=? n "const") (dr (r-frozen -1 #f)))
            ((string=? n "acyclic") (dr (r-frozen -1 #t)))
            ((string=? n "finite") (dz (sz-finite)))
            ((string=? n "heap") (dr (r-heap)))
            (else (k-parse-d-bound s (k-lookup-desc sym)))))))
(define k-parse-d (->* (syn) k-desc)
  (lambda (s)
    (cond ((tagcase s (atom (d a b) (datum-int? d)) (else x #f))
           ;; A natural number can only be a size.
           (dz (k-parse-size s)))
          ((syn-symbol? s) (k-parse-d-name s))
          (else
           (let ((hd (k-head (k-items s "a description"))))
             (cond ((string=? hd "dlambda") (k-fun-d s))
                   ((or (k-atom-head? hd) (string=? hd "maxeff")) (de (k-parse-effect s)))
                   ((or (string=? hd "+") (string=? hd "-")) (dz (k-parse-size s)))
                   (else (dt (k-parse-type s)))))))))
;; A description of kind `k`, as written.
(define k-parse-desc-at (->* (syn int) k-desc)
  (lambda (s k)
    (cond ((k-type-kind? k) (dt (k-parse-type s)))
          ((= k 7) (dt (k-parse-flat s)))
          ((= k 0) (dr (k-parse-region s)))
          ((= k 3) (dr (k-parse-place s)))
          ((= k 1) (de (k-parse-effect s)))
          ((= k 5) (dz (k-parse-size s)))
          ((= k 6) (dc (k-parse-conv s)))
          (else (df (k-parse-fun s k))))))
;; Descriptions `xs`, each of its kind in `ks`.
(define k-parse-descs-at (->* (k-syns k-ids) k-descs)
  (lambda (xs ks)
    (if (null? xs)
        nil
        (let ((d (k-parse-desc-at (car xs) (car ks))))
          (cons d (k-parse-descs-at (cdr xs) (cdr ks)))))))
;; Description `s`, of kind `k` if that is known (not -1).
(define k-parse-desc-of (->* (syn int) k-desc)
  (lambda (s k) (if (>= k 0) (k-parse-desc-at s k) (k-parse-d s))))
;; A description function, as written where one of kind `want` (-1 if not
;; known) is wanted.
(define k-parse-fun (->* (syn int) int)
  (lambda (s want)
    (let* ((f (k-parse-fun-node s want)) (got (k-fun-kind f)))
      (if (and (>= want 0) (>= got 0) (not (= got want)))
          (k-sfail (k-cat4 "a description function of kind " (k-kind-text want)
                           " is wanted, and this is of kind " (k-kind-text got))
                   s)
          f))))
(define k-parse-fun-node (->* (syn int) int)
  (lambda (s want)
    (if (syn-symbol? s)
        (k-fun-named s)
        (let ((usage (string-append "a description function: a name, `(dlambda ((name kind) …) "
                                    "description)` or `(select module name)`")))
          (tagcase s
            (lst (items d a b)
              (let ((hd (k-symbol-head items)))
                (case hd (("dlambda") (k-parse-dlambda s items want))
                         (("select") (k-parse-select s items))
                         (else
                          (cond ((k-fun-bound? hd) (k-parse-fun-app s items))
                                (else (k-sfail usage s)))))))
            (else x (k-sfail usage s)))))))
;; `(dlambda ((x k) …) d)`.
(define k-parse-dlambda (->* (syn k-syns int) int)
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
(define k-parse-fun-app (->* (syn k-syns) int)
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
(define k-fun-named (->* (syn) int)
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
(define k-abbrev-eta (->* (syn symbol k-params syn) int)
  (lambda (s name ps body)
    (let* ((bs (k-fresh-named (k-params-names ps) (k-params-kinds ps)))
           (t (if (> (get k-expanding) 64)
                  (k-endless s name)
                  (k-expand-bound s name body (k-binders-as-scope bs)))))
      (k-lam bs (dt t)))))
;; `(f d …)` as a type: `f` given the descriptions `args` are, of the
;; kinds it takes; reduced, if it is a `dlambda`. Where `f`'s kind is not
;; known yet (a `select`), what it is given is read by its shape, and
;; checked once it is resolved.
(define k-parse-app (->* (syn int k-syns) int)
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
(define k-parse-ds (->* (k-syns) k-descs)
  (lambda (xs)
    (if (null? xs) nil (let ((d (k-parse-d (car xs)))) (cons d (k-parse-ds (cdr xs)))))))
;; `(e d …)` in an effect, where `e` is a description function to an
;; effect: its effect, reduced if it is a `dlambda`; none if `items` are
;; no such application.
(define k-parse-effect-app (->* (syn k-syns) (listof k-eff acyclic))
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
                           (else y (k-not-giving f "an effect" s))))))))))))
;; A `moduleof`'s description `what` of `name`, in scope in what follows it:
;; `(desc e E)`, an effect, as a module's `define-effect` gives; a description
;; function; or a type.
(define k-moduleof-desc (->* (symbol syn) int)
  (lambda (name what)
    (cond ((k-effect-shaped? what)
           (let* ((e (k-parse-effect what)) (d (k-effect-desc e)))
             (begin (k-push-desc name (ds-eff e)) d)))
          ((string=? (k-list-head what) "dlambda")
           (let ((f (k-parse-fun what -1))) (begin (k-push-desc name (ds-fun f)) f)))
          (else (let ((t (k-parse-type what))) (begin (k-push-desc name (ds-rec t)) t))))))
;; A `moduleof`'s components `cs`, those before them read into `abs`, `ds`
;; and `vs` (newest first), their names `seen` (types and effects) and `vseen`
;; (values): a value may have a type's name.
(define k-moduleof-comps
  (->* (k-syns k-parts k-parts k-parts k-names k-names) int)
  (lambda (cs abs ds vs seen vseen)
    (if (null? cs)
        (let ((ds (k-parts-reversed ds nil)) (vs (k-parts-reversed vs nil)))
          (k-ty-new (ty-module (k-parts-reversed abs nil) ds vs)))
        (let* ((c (car cs))
               (parts (k-items c "a module component"))
               (shaped (k-shape (= (k-length parts) 3) k-moduleof-usage c))
               (head (k-symbol-head parts))
               (names (k-component-names (k-nth parts 1) head))
               (val? (string=? head "val"))
               (seen (if val? seen (k-names-once names seen c)))
               (vseen (if val? (k-names-once names vseen c) vseen))
               (what (k-nth parts 2)))
          (case head
            (("abs")
             (let ((k (k-abs-kind (k-nth parts 1) what)))
               (if (or (= k 2) (and (k-arrow-kind? k) (= (k-arrow-result k) 2)))
                   (k-moduleof-comps (cdr cs) (k-abs-bound names k abs) ds vs seen vseen)
                   (k-sfail k-abs-usage what))))
            (("desc")
             (let ((d (k-moduleof-desc (car names) what)))
               (k-moduleof-comps (cdr cs) abs (k-part-onto (car names) d ds) vs seen vseen)))
            (("val")
             (let ((t (k-parse-type what)))
               (k-moduleof-comps (cdr cs) abs ds (k-part-onto (car names) t vs) seen vseen)))
            (else (k-sfail k-moduleof-usage (car parts))))))))
;; `(moduleof …)`, each abstract type a binder in scope in what follows it;
;; or `(select m t)`.
(define k-read-module-type (->* (syn k-syns symbol) int)
  (lambda (s items hd)
    (if (symbol=? hd 'select)
        (k-parse-select s items)
        (let* ((saved (get k-dscope)) (t (k-moduleof-comps (cdr items) nil nil nil nil nil)))
          (begin (set k-dscope saved) t)))))
(define k-selects-from (->* (int k-seen (ref k-selects @t)) unit)
  (lambda (t seen out)
    (let ((t (k-resolve t)))
      (if (k-seen? seen t)
          #u
          (begin
            (tagcase (k-get t)
              (ty-select (m n) (set out (cons (product (1 m) (2 n) (3 t)) (get out))))
              (else y (k-selects-each (k-ty-kids t) seen out))))))))
(define k-selects-each (->* (k-ids k-seen (ref k-selects @t)) unit)
  (lambda (ts seen out)
    (if (null? ts)
        #u
        (begin (k-selects-from (car ts) seen out) (k-selects-each (cdr ts) seen out)))))
;; The `select`s in `t`, in the order first met.
(define k-selects-in (->* (int) k-selects)
  (lambda (t)
    (let ((out (the (ref k-selects @t) (new nil))))
      (begin (k-selects-from t (k-new-seen) out)
             (k-selects-reversed (get out) nil)))))
;; `t` with each `(select m x)` of a parameter named before it, the `k`th,
;; made `(select $k x)`.
(define k-select-params (->* (int k-names) int)
  (lambda (t names)
    (let ((sel (if (k-all-unnamed? names)
                   (the k-selects nil)
                   (k-param-selects (k-selects-in t) names))))
      (if (null? sel)
          t
          (let ((outer (get k-select-map)))
            (begin (set k-select-map sel)
                   (let ((r (k-subst t nil))) (begin (set k-select-map outer) r))))))))
;; A `subr` type's parameters `ps` (from those named `names`) and its
;; result `r`, read: their types, the result last.
(define k-read-params-from (->* (k-syns syn k-names) k-ids)
  (lambda (ps r names)
    (if (null? ps)
        ;; A test's result, `(bool …)`: here, and only here.
        (let ((t (if (string=? (k-list-head r) "bool")
                     (k-parse-proving r (k-length names))
                     (k-parse-type r))))
          (cons (k-select-params t names) nil))
        (let* ((named (k-param-name (car ps)))
               (written (if (null? named) (car ps) (k-nth (k-items (car ps) "a parameter") 1)))
               (t (k-select-params (k-parse-type written) names))
               (name (if (null? named) k-no-name (car named)))
               (rest (k-read-params-from (cdr ps) r (k-names-snoc names name))))
          (cons t rest)))))
(define k-read-params (->* (k-syns syn) k-ids)
  (lambda (ps r) (k-read-params-from ps r nil))))))
