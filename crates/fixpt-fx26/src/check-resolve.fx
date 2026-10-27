;;; The checker, in FX-26: resolving the trees' descriptions, callables,
;;; regions of types, and masking (substitution is `check-subst.fx`'s).
;;; Part of the checker, `check-types.fx` first (PLAN.md §11, step 10).

;;; ------------------------------------------------------------ resolving
;;; The parser's trees to `kx`, reading descriptions where the Rust parser
;;; does.

;; Its types, those it uses of the files before it, and the signatures of
;; what it is given.
;; Its types (`check-resolve-types.fx`), loaded before the module so that they are not
;; among its values; the module names what it uses of them.
(let* ((check-resolve-types (load-module "fx26:check-resolve-types.fx"))
       (check-types-types (load-module "fx26:check-types-types.fx"))
       (check-modorder-types (load-module "fx26:check-modorder-types.fx"))
       (parser-types ((proj (load-module "fx26:parser-types.fx") @s @e @m @c @p)))
       (check-subst-types (load-module "fx26:check-subst-types.fx"))
       (check-subtype-types (load-module "fx26:check-subtype-types.fx"))
       (check-effects-types (load-module "fx26:check-effects-types.fx"))
       (check-env-types (load-module "fx26:check-env-types.fx"))
       (check-read-types (load-module "fx26:check-read-types.fx"))
       (check-syntax-types (load-module "fx26:check-syntax-types.fx"))
       (check-print-types (load-module "fx26:check-print-types.fx"))
       (check-print-parts-types (load-module "fx26:check-print-parts-types.fx"))
       (check-read-descs-types (load-module "fx26:check-read-descs-types.fx"))
       (table-types (load-module "fx26:table-types.fx")))
  ;; What it is given: the modules of the files before it that it uses.
  (lambda ((check-types (select check-types-types check-types-sig))
           (check-subst (select check-subst-types check-subst-sig))
           (check-effects (select check-effects-types check-effects-sig))
           (check-env (select check-env-types check-env-sig))
           (check-read (select check-read-types check-read-sig))
           (check-syntax (select check-syntax-types check-syntax-sig))
           (check-print (select check-print-types check-print-sig))
           (check-read-descs (select check-read-descs-types check-read-descs-sig))
           (tables (select table-types tables-sig))
           (check-print-parts (select check-print-parts-types check-print-parts-sig)))
    (module
(hide (include check-resolve-types) (include check-types-types) (include check-modorder-types)
      (include parser-types) (include check-subst-types) (include check-subtype-types))
;; The types it uses of the files before it.
;; What it uses of the modules it is given: all of each, hidden.
(hide (include check-types) (include check-subst) (include check-env) (include check-syntax)
      (include check-print-parts) (include check-read-descs) (include tables))
(import check-effects k-atom-region k-has-region? k-insert k-region=?)
(import check-read k-effect-selects k-with-effect-falls k-items)

(define k-start (->* (kx) int)
  (lambda (x)
    (tagcase x
      (x-var (s a b abk) a) (x-const (t v a b abk) a) (x-lambda (ps e a b abk) a)
      (x-app (f xs a b abk) a) (x-plambda (bs e a b abk) a) (x-proj (e ds a b abk) a)
      (x-if (p c d a b abk) a) (x-letrec (bs e a b abk) a) (x-let (bs e a b abk) a)
      (x-begin (xs a b abk) a) (x-prompt (t e h a b abk) a) (x-the (t e a b abk) a)
      (x-convention (c e a b abk) a) (x-bloblet (o i xs a b abk) a) (x-product (fs a b abk) a)
      (x-extract (e l a b abk) a) (x-sum (l e a b abk) a) (x-tagcase (e arms els a b abk) a)
      (x-letregion (k r i e a b abk) a) (x-rlambda (r l a b abk) a) (x-module (items a b abk) a)
      (x-with (m e a b abk) a))))
(define k-end (->* (kx) int)
  (lambda (x)
    (tagcase x
      (x-var (s a b abk) b) (x-const (t v a b abk) b) (x-lambda (ps e a b abk) b)
      (x-app (f xs a b abk) b) (x-plambda (bs e a b abk) b) (x-proj (e ds a b abk) b)
      (x-if (p c d a b abk) b) (x-letrec (bs e a b abk) b) (x-let (bs e a b abk) b)
      (x-begin (xs a b abk) b) (x-prompt (t e h a b abk) b) (x-the (t e a b abk) b)
      (x-convention (c e a b abk) b) (x-bloblet (o i xs a b abk) b) (x-product (fs a b abk) b)
      (x-extract (e l a b abk) b) (x-sum (l e a b abk) b) (x-tagcase (e arms els a b abk) b)
      (x-letregion (k r i e a b abk) b) (x-rlambda (r l a b abk) b) (x-module (items a b abk) b)
      (x-with (m e a b abk) b))))
(define k-kth (->* (kx) int)
  (lambda (x)
    (tagcase x
      (x-var (s a b abk) abk) (x-const (t v a b abk) abk) (x-lambda (ps e a b abk) abk)
      (x-app (f xs a b abk) abk) (x-plambda (bs e a b abk) abk) (x-proj (e ds a b abk) abk)
      (x-if (p c d a b abk) abk) (x-letrec (bs e a b abk) abk) (x-let (bs e a b abk) abk)
      (x-begin (xs a b abk) abk) (x-prompt (t e h a b abk) abk) (x-the (t e a b abk) abk)
      (x-convention (c e a b abk) abk) (x-bloblet (o i xs a b abk) abk)
      (x-product (fs a b abk) abk) (x-extract (e l a b abk) abk) (x-sum (l e a b abk) abk)
      (x-tagcase (e arms els a b abk) abk) (x-letregion (k r i e a b abk) abk)
      (x-rlambda (r l a b abk) abk) (x-module (items a b abk) abk) (x-with (m e a b abk) abk))))
;; `x`'s identity.
(define k-at-of (->* (kx) k-at)
  (lambda (x) (product (1 (k-start x)) (2 (k-end x)) (3 (k-kth x)))))
(define k-same-span? (->* (kx int int) bool)
  (lambda (x a b) (and (= (k-start x) a) (= (k-end x) b))))

(define k-resolve-params (->* (exp-params) k-typed-params)
  (lambda (ps)
    (if (null? ps)
        nil
        (let* ((ty (extract (car ps) 2))
               (t (if (null? ty) (the k-ids nil) (the k-ids (cons (k-parse-type (car ty)) nil))))
               (rest (k-resolve-params (cdr ps))))
          (cons (product (1 (extract (car ps) 1)) (2 t)) rest)))))
(define k-resolve-descs (->* (syns-a) k-descs)
  (lambda (ds)
    (if (null? ds)
        nil
        (let* ((d (k-parse-d (car ds))) (rest (k-resolve-descs (cdr ds))))
          (cons d rest)))))
(define k-copy-names (->* (names) k-names)
  (lambda (ns) (if (null? ns) nil (cons (car ns) (k-copy-names (cdr ns))))))

;; Where a parser's tree starts and ends, and which of the expressions there
;; it is.
(define exp-start (->* (exp) int)
  (lambda (e)
    (tagcase e
      (e-var (s a b abk) a) (e-int (n a b abk) a) (e-bool (v a b abk) a) (e-str (v a b abk) a)
      (e-char (v a b abk) a) (e-float (v a b abk) a) (e-sym (v a b abk) a) (e-unit (a b abk) a)
      (e-lambda (ps x a b abk) a) (e-app (f xs a b abk) a) (e-plambda (bs x a b abk) a)
      (e-proj (x ds a b abk) a) (e-if (p c d a b abk) a) (e-letrec (bs x a b abk) a)
      (e-let (bs x a b abk) a) (e-begin (xs a b abk) a) (e-prompt (t x h a b abk) a)
      (e-the (t x a b abk) a) (e-convention (c x a b abk) a) (e-bloblet (o i xs got a b abk) a)
      (e-product (fs a b abk) a) (e-extract (x l got a b abk) a) (e-sum (l x a b abk) a)
      (e-tagcase (x arms els got a b abk) a) (e-letregion (k r i x a b abk) a)
      (e-rlambda (r l a b abk) a) (e-module (items a b abk) a) (e-with (m x a b abk) a))))
(define exp-end (->* (exp) int)
  (lambda (e)
    (tagcase e
      (e-var (s a b abk) b) (e-int (n a b abk) b) (e-bool (v a b abk) b) (e-str (v a b abk) b)
      (e-char (v a b abk) b) (e-float (v a b abk) b) (e-sym (v a b abk) b) (e-unit (a b abk) b)
      (e-lambda (ps x a b abk) b) (e-app (f xs a b abk) b) (e-plambda (bs x a b abk) b)
      (e-proj (x ds a b abk) b) (e-if (p c d a b abk) b) (e-letrec (bs x a b abk) b)
      (e-let (bs x a b abk) b) (e-begin (xs a b abk) b) (e-prompt (t x h a b abk) b)
      (e-the (t x a b abk) b) (e-convention (c x a b abk) b) (e-bloblet (o i xs got a b abk) b)
      (e-product (fs a b abk) b) (e-extract (x l got a b abk) b) (e-sum (l x a b abk) b)
      (e-tagcase (x arms els got a b abk) b) (e-letregion (k r i x a b abk) b)
      (e-rlambda (r l a b abk) b) (e-module (items a b abk) b) (e-with (m x a b abk) b))))
(define exp-kth (->* (exp) int)
  (lambda (e)
    (tagcase e
      (e-var (s a b abk) abk) (e-int (n a b abk) abk) (e-bool (v a b abk) abk)
      (e-str (v a b abk) abk) (e-char (v a b abk) abk) (e-float (v a b abk) abk)
      (e-sym (v a b abk) abk) (e-unit (a b abk) abk) (e-lambda (ps x a b abk) abk)
      (e-app (f xs a b abk) abk) (e-plambda (bs x a b abk) abk) (e-proj (x ds a b abk) abk)
      (e-if (p c d a b abk) abk) (e-letrec (bs x a b abk) abk) (e-let (bs x a b abk) abk)
      (e-begin (xs a b abk) abk) (e-prompt (t x h a b abk) abk) (e-the (t x a b abk) abk)
      (e-convention (c x a b abk) abk) (e-bloblet (o i xs got a b abk) abk)
      (e-product (fs a b abk) abk) (e-extract (x l got a b abk) abk) (e-sum (l x a b abk) abk)
      (e-tagcase (x arms els got a b abk) abk) (e-letregion (k r i x a b abk) abk)
      (e-rlambda (r l a b abk) abk) (e-module (items a b abk) abk) (e-with (m x a b abk) abk))))
;; `x`'s identity.
(define exp-at (->* (exp) k-at)
  (lambda (x) (product (1 (exp-start x)) (2 (exp-end x)) (3 (exp-kth x)))))

;; A `plambda`'s region and place binders: each won't outlive what is bound
;; around it (`lives`), and each is around what its body binds.
(define k-order-binders (->* (k-binders k-ids) unit)
  (lambda (bs lives)
    (if (null? bs)
        #u
        (let ((v (extract (car bs) 1)) (k (extract (car bs) 2)))
          (begin
            (if (or (= k 0) (= k 3))
                (begin (k-set-outer v lives) (set k-lifetimes (cons v (get k-lifetimes))))
                #u)
            (k-order-binders (cdr bs) lives))))))

;; The place a `letfreeze` names: `heap`, or a place in scope.
(define k-resolve-place (->* (symbol int int) k-region)
  (lambda (n a b)
    (if (symbol=? n 'heap)
        (r-heap)
        (let ((d (k-lookup-desc n)))
          (if (null? d)
              (k-fail (k-cat3 "`" (symbol->string n) "` is not a region") a b)
              (tagcase (car d)
                (ds-var (v k)
                  (case k ((3) (r-var v))
                          ((0) (k-fail (k-cat3 "`" (symbol->string n) "` is not a place") a b))
                          (else (k-fail (k-cat3 "`" (symbol->string n) "` is not a region") a b))))
                (else x (k-fail (k-cat3 "`" (symbol->string n) "` is not a region") a b))))))))
;; What a `letfreeze` into `place` freezes into: `(const p)` for its
;; place `p`, and for the heap, -1.
(define k-freeze-into (->* (k-region) k-region)
  (lambda (place) (tagcase place (r-var (p) (r-frozen p #f)) (else y (r-frozen -1 #f)))))
;; What a `letfreeze` into `place` won't outlive: the place, and what it
;; won't.
(define k-place-lives (->* (k-region) k-ids)
  (lambda (place) (tagcase place (r-var (p) (cons p (k-outer-of p))) (else y nil))))

(define k-as-subr (->* (int) (listof k-callable acyclic))
  (lambda (t)
    (tagcase (k-get t)
      (ty-subr (e ps r cv spc) (cons (product (1 e) (2 ps) (3 r)) nil))
      (ty-comp (arg answer e r once)
        (let ((control (k-insert (a-goto r) (k-insert (a-comefrom r) e))))
          (cons (product (1 control) (2 (the k-ids (cons arg nil))) (3 answer)) nil)))
      (else x nil))))
;; No `vsubr`; one, of latent effect `e`, arguments of type `a`, result `r`.
(define k-vsub-none k-vsub nil)
(define k-vsub-one (->* (k-eff int int) k-vsub)
  (lambda (e a r) (cons (product (1 e) (2 a) (3 r)) nil)))
;; `vsubr`'s three descriptions, an effect and two types, as `k-vsubr-parts`
;; gives them.
(define k-vsubr-descs (->* (k-desc k-desc k-desc) k-vsub)
  (lambda (e a r)
    (tagcase e
      (de (le)
        (tagcase a
          (dt (at) (tagcase r (dt (rt) (k-vsub-one le at rt)) (else z k-vsub-none)))
          (else z k-vsub-none)))
      (else z k-vsub-none))))
;; A `vsubr` (generative type 0), taken apart: its latent effect, the type of
;; each argument, and the result's, in a list; none for any other type.
(define k-vsubr-parts (->* (int) k-vsub)
  (lambda (t)
    (tagcase (k-get t)
      (ty-named (g ds)
        (if (and (= g 0) (= (k-length ds) 3))
            (k-vsubr-descs (car ds) (car (cdr ds)) (car (cdr (cdr ds))))
            k-vsub-none))
      (else y k-vsub-none))))
;; `n` copies of type `t`, onto `acc`.
(define k-repeat-id (->* (int int k-ids) k-ids)
  (lambda (t n acc) (if (<= n 0) acc (k-repeat-id t (- n 1) (cons t acc)))))
;; What `t` is called as, with `n` arguments: a subroutine; a `vsubr` (a
;; standard `list`), as one of `n` parameters, each of its argument type;
;; or none.
(define k-callee-of (->* (int int) (listof k-callable acyclic))
  (lambda (t n)
    (let ((v (k-vsubr-parts t)))
      (if (null? v)
          (k-as-subr t)
          (let* ((p (car v)) (ps (k-repeat-id (extract p 2) n (the k-ids nil))))
            (cons (product (1 (extract p 1)) (2 ps) (3 (extract p 3))) nil))))))

;;; ------------------------------------------------------------ regions of types

(define k-has-region-in? (->* (k-regions k-region) bool)
  (lambda (rs r)
    (cond ((null? rs) #f)
          ((k-region=? (car rs) r) #t)
          (else (k-has-region-in? (cdr rs) r)))))
(define k-add-region (->* (k-regions k-region) k-regions)
  (lambda (rs r) (if (k-has-region-in? rs r) rs (cons r rs))))
;; `out` and each of `rs` that is not a generative type's parameter.
(define k-add-non-gen (->* (k-regions k-regions) k-regions)
  (lambda (out rs)
    (cond ((null? rs) out)
          ((k-gen-region? (car rs)) (k-add-non-gen out (cdr rs)))
          (else (k-add-non-gen (k-add-region out (car rs)) (cdr rs))))))
(define k-add-eff-regions (->* (k-regions k-eff) k-regions)
  (lambda (rs e)
    (cond ((null? e) rs)
          ((k-has-region? (car e))
           (k-add-eff-regions (k-add-region rs (k-atom-region (car e))) (cdr e)))
          (else (k-add-eff-regions rs (cdr e))))))

(define k-regions-memo (ref k-region-lists @t) (new (make-array 512 nil)))

;; The definitions checked so far, newest first, each the latest of its
;; names.
(define k-defs (ref (listof k-def acyclic) @t) (new nil))
;; The free variables of the definition being checked, for `k-record`.
(define k-last-uses (ref k-names @t) (new nil))
(define k-runs (ref (listof k-run acyclic) @t) (new nil))
;; For `k-reset`: forget the description variables, and what is known of
;; the regions and places among them.
(define k-reset-regions (->* () unit)
  (lambda ()
    (begin
      (set k-dvars nil) (set k-ndvars 0) (set k-places nil) (set k-bounds nil) (set k-outers nil)
      (set k-distincts nil)
      (set k-lifetimes nil) (set k-freezing nil) (set k-written nil)
      (set k-arrow-vars nil) (set k-abstract-funs nil))))
;; Forget the names bound, and what is known of them.
(define k-reset-names (->* () unit)
  (lambda ()
    (begin
      (set k-known (make-table symbol-hash symbol=?))
      (set k-global (make-table symbol-hash symbol=?))
      (set k-recursive nil) (set k-std nil) (set k-env (make-table symbol-hash symbol=?))
      (set k-depths (make-table symbol-hash symbol=?))
      (set k-std-table (make-table symbol-hash symbol=?))
      (set k-trail nil) (set k-depth 0))))
;; Forget the lemmas, and the facts learned of data and sizes.
(define k-reset-facts (->* () unit)
  (lambda ()
    (begin
      (set k-lemmas nil) (set k-pending-lemma nil) (set k-datas nil) (set k-certified nil)
      (set k-arrow-star #f)
      (set k-flats nil)
      (set k-narrowed nil) (set k-path-narrowed nil) (set k-closure-depth 0)
      (set k-certified-lengths nil) (set k-certified-nats nil) (set k-size-facts nil)
      (set k-skolems nil))))
(define k-reset (->* () unit)
  (lambda ()
    (begin
      (set k-extracts nil) (set k-effect-notes nil)
      (set k-ntys 0) (set k-links (+ (get k-links) 1)) (k-reset-regions) (k-reset-names)
      (set k-arrow-star-tys nil) (set k-arrow-star-settled nil)
      (set k-regions-memo (make-array 512 nil)) (set k-dscope nil)
      (set k-with-depth 0) (set k-with-fallbacks nil) (set k-with-apps nil)
      (set k-fresh 0) (set k-base nil) (set k-expanding 0) (set k-knots nil) (set k-spin-why nil)
      (k-forget-closed-named)
      (set k-gens nil) (set k-ngens 0) (set k-transparent nil) (set k-inside nil)
      (set k-conversions nil) (k-reset-facts)
      (set k-broken nil) (set k-defs nil) (set k-runs nil) (set k-last-uses nil)
      (k-forget-withs) (set k-module-vars nil) (set k-select-map nil) (set k-reshapes nil)
      (set k-hide-mark -1) (set k-param-map nil) (set k-effect-selects nil)
      (set k-with-effect-falls nil)
      (set k-operator k-no-operator)
      (k-basic "int") (k-basic "bool") (k-basic "string") (k-basic "unit") (k-basic "char")
      (k-basic "%datum") (k-basic "symbol") (k-basic "tword") (k-basic "wcell") (k-basic "wglobal")
      ;; 10 to 15; `void` 16, `k-void`.
      (k-basic "i32") (k-basic "u32") (k-basic "i64") (k-basic "u64")
      (k-basic "f64") (k-basic "f32")
      (k-ty-new (ty-void))
      ;; 17 and 18, after `void`: as `check.rs` makes them.
      (k-basic "vector") (k-basic "bytevector")
      ;; 19 and 20, last, so no type made before them moved (`TODO.md` §84).
      (k-basic "i8") (k-basic "u8")
      #u)))
(define n-copy-memo (->* (k-region-lists k-region-lists int) unit)
  (lambda (from to i)
    (if (= i (array-length from))
        #u
        (begin (array-set! to i (array-ref from i)) (n-copy-memo from to (+ i 1))))))
(define k-remember-regions (->* (int k-regions) unit)
  (lambda (t rs)
    (begin
      (if (>= t (array-length (get k-regions-memo)))
          (let ((bigger (the k-region-lists (make-array (* 2 (array-length (get k-tys))) nil))))
            (begin (n-copy-memo (get k-regions-memo) bigger 0) (set k-regions-memo bigger)))
          #u)
      (array-set! (get k-regions-memo) t (cons rs nil)))))
;; Add to `out` the regions of `e`'s atoms.
(define k-note-eff-regions (->* ((ref k-regions @t) k-eff) unit)
  (lambda (out e) (set out (k-add-eff-regions (get out) e))))

(define-rec
  (k-regions-walk (->* (int int (ref k-regions @t)) unit)
    (lambda (t seen out)
      (let ((t (k-resolve t)))
        (if (k-visit? t seen)
            #u
            (letrec ((add (subr (maxeff kstate spin) (k-region) unit)
                          (lambda (r) (set out (k-add-region (get out) r))))
                     (walk (subr (maxeff kstate spin) (int) unit)
                           (lambda (x) (k-regions-walk x seen out)))
                     (walks (subr (maxeff kstate spin) (k-ids) unit)
                            (lambda (xs) (k-regions-walks xs seen out))))
              (begin
                (tagcase (k-get t)
                  (ty-subr (e ps r cv spc) (begin (k-note-eff-regions out e) (walks ps) (walk r)))
                  (ty-poly (bs body) (walk body))
                  (ty-ref (a r) (begin (add r) (walk a)))
                  (ty-array (a nz r) (begin (add r) (walk a)))
                  (ty-icell (a r) (begin (add r) (walk a)))
                  (ty-place (r) (add r))
                  (ty-pair (a b r nl) (begin (add r) (walk a) (walk b)))
                  (ty-tag (a h e r) (begin (add r) (k-note-eff-regions out e) (walk a) (walk h)))
                  (ty-comp (b a e r once)
                    (begin (add r) (k-note-eff-regions out e) (walk a) (walk b)))
                  (ty-markkey (a r) (begin (add r) (walk a)))
                  (ty-bloblet (fs z r) (begin (add r) (walks fs)))
                  (ty-product (ps) (k-regions-parts ps seen out))
                  (ty-sum (ps) (k-regions-parts ps seen out))
                  (ty-union (ms) (walks ms))
                  (ty-nlist (e z r) (begin (add r) (walk e)))
                  (ty-module (abs ds vs)
                    (begin (k-regions-parts ds seen out) (k-regions-parts vs seen out)))
                  ;; Transparent to safety: what its representation holds,
                  ;; its parameters' regions standing for what it was given.
                  (ty-named (g ds)
                    (let ((inner (the (ref k-regions @t) (new nil))))
                      (begin (k-regions-walk (extract (k-gen-of g) 4) seen inner)
                             (set out (k-add-non-gen (get out) (get inner)))
                             (k-regions-descs ds seen out))))
                  ;; A description function applied, which cannot be looked
                  ;; into: what it was given; a function, its body.
                  (ty-app (g ds) (k-regions-descs ds seen out))
                  (ty-lam (bs body) (k-regions-descs (the k-descs (cons body nil)) seen out))
                  (else x #u))))))))
  (k-regions-descs (->* (k-descs int (ref k-regions @t)) unit)
    (lambda (ds seen out)
      (if (null? ds)
          #u
          (begin (tagcase (car ds)
                   (dt (x) (k-regions-walk x seen out))
                   (dr (r) (set out (k-add-region (get out) r)))
                   (de (e) (k-note-eff-regions out e))
                   (dz (z) #u)
                   (dc (c) #u)
                   (df (f)
                     (tagcase (k-get f)
                       (ty-lam (bs body) (k-regions-descs (the k-descs (cons body nil)) seen out))
                       (else y #u))))
                 (k-regions-descs (cdr ds) seen out)))))
  (k-regions-walks (->* (k-ids int (ref k-regions @t)) unit)
    (lambda (ts seen out)
      (if (null? ts)
          #u
          (begin (k-regions-walk (car ts) seen out) (k-regions-walks (cdr ts) seen out)))))
  (k-regions-parts (->* (k-parts int (ref k-regions @t)) unit)
    (lambda (ps seen out)
      (if (null? ps)
          #u
          (begin (k-regions-walk (extract (car ps) 2) seen out)
                 (k-regions-parts (cdr ps) seen out))))))
(define k-frozen-places (->* (k-regions k-regions) k-regions)
  (lambda (rs out)
    (if (null? rs)
        out
        (let ((out (tagcase (car rs)
                     (r-frozen (p f) (if (< p 0) out (k-add-region out (r-var p))))
                     (else y out))))
          (k-frozen-places (cdr rs) out)))))
(define k-regions-in (->* (int) k-regions)
  (lambda (t)
    (let* ((t (k-resolve t)) (memo (get k-regions-memo)))
      (if (and (< t (array-length memo)) (not (null? (array-ref memo t))))
          (car (array-ref memo t))
          (let ((out (the (ref k-regions @t) (new nil))))
            (begin
              (k-regions-walk t (k-new-epoch) out)
              ;; Frozen data mentions the place it is in.
              (set out (k-frozen-places (get out) (get out)))
              (k-remember-regions t (get out))
              (get out)))))))
(define k-note (->* (symbol k-names k-names) k-names)
  (lambda (s bound out) (if (or (k-has-name? bound s) (k-has-name? out s)) out (cons s out))))
(define k-names-onto (->* (k-names k-names) k-names)
  (lambda (ns bound) (if (null? ns) bound (k-names-onto (cdr ns) (cons (car ns) bound)))))
;; `bound`, and the names `ps`, `bs` bind.
(define k-param-names (->* (k-typed-params k-names) k-names)
  (lambda (ps bound)
    (if (null? ps) bound (k-param-names (cdr ps) (cons (extract (car ps) 1) bound)))))
(define k-letrec-names (->* (k-letrec-bs k-names) k-names)
  (lambda (bs bound)
    (if (null? bs) bound (k-letrec-names (cdr bs) (cons (extract (car bs) 1) bound)))))
(define k-let-names (->* (k-let-bs k-names) k-names)
  (lambda (bs bound)
    (if (null? bs) bound (k-let-names (cdr bs) (cons (extract (car bs) 1) bound)))))

;; `up-t` and `down-t`, an abstract type `t`'s conversions, onto `bound`.
(define k-conversion-name (->* (string symbol) symbol)
  (lambda (prefix n) (string->symbol (string-append prefix (symbol->string n)))))
(define k-conversions-onto (->* (symbol k-names) k-names)
  (lambda (n bound)
    (cons (k-conversion-name "down-" n) (cons (k-conversion-name "up-" n) bound))))
;; The names an item binds for those after it, onto `bound`: an abstract
;; type's conversions, a value's name, a group's.
(define k-item-bound (->* (k-item k-names) k-names)
  (lambda (it bound)
    (let ((k (extract it 1)) (ns (extract it 2)))
      (cond ((= k 0) (k-conversions-onto (car ns) bound))
            ((or (= k 1) (< k 0) (> k 3)) bound)
            (else (k-names-onto ns bound))))))
;; Every name `items` define, onto `bound`.
(define k-items-bound (->* (k-items k-names) k-names)
  (lambda (items bound)
    (if (null? items) bound (k-items-bound (cdr items) (k-item-bound (car items) bound)))))

;; The names a `with` of `m`, `a` `b` `k`, binds for its body, bound inside
;; `bound`: its module's values the body names, once checked; before, if
;; `m` is not bound inside, those of an earlier item of a module being
;; ordered whose value is a module as written (`k-hazard-mods`).
(define k-with-bound (->* (symbol int int int k-names) k-names)
  (lambda (m a b k bound)
    (let ((ns (k-with-names a b k)))
      (if (and (null? ns) (not (k-has-name? bound m)))
          (k-hazard-names-in (get k-hazard-mods) m)
          ns))))

;; The names in `bound` (each by how many names are from it to the
;; outermost) that a `let` binds to a module written there, with the values
;; it gives: what a `with` of one binds in its body before it is checked
;; (`free_into_in`).
(define-type k-wlocals (listof (productof (1 int) (2 k-names)) acyclic))
;; How many names are from `m`'s innermost binding in `bound` to the
;; outermost, or 0.
(define k-bound-at (->* (k-names symbol) int)
  (lambda (bound m)
    (cond ((null? bound) 0)
          ((symbol=? (car bound) m) (k-length bound))
          (else (k-bound-at (cdr bound) m)))))
(define k-wlocal-vals (->* (k-wlocals int) k-names)
  (lambda (ls at)
    (cond ((or (null? ls) (= at 0)) nil)
          ((= (extract (car ls) 1) at) (extract (car ls) 2))
          (else (k-wlocal-vals (cdr ls) at)))))
;; The `let`'s bindings `bs`, the `k`th from `n` names out, onto `ls`.
(define k-wlocals-let (->* (k-let-bs int k-wlocals) k-wlocals)
  (lambda (bs n ls)
    (if (null? bs)
        ls
        (let ((vals (k-written-module-values (extract (car bs) 2))))
          (k-wlocals-let (cdr bs) (+ n 1)
                         (if (null? vals) ls (cons (product (1 n) (2 (car vals))) ls)))))))
;; The values a module written as `x`, `(module item …)`, gives, as its type
;; will say: its definitions not hidden; none known if it includes others.
(define k-written-module-values (->* (kx) (listof k-names acyclic))
  (lambda (x)
    (tagcase x
      (x-module (items a b abk)
        (let ((hidden (k-hidden-values items nil)))
          (if (k-items-include? items) nil (cons (k-shown-values items hidden nil) nil))))
      (else y nil))))
(define k-hidden-values (->* (k-items k-names) k-names)
  (lambda (items out)
    (if (null? items)
        out
        (let* ((it (car items)) (n (symbol->string (car (extract it 2)))))
          (k-hidden-values (cdr items)
                           (if (and (= (extract it 1) 1) (> (string-length n) 9)
                                    (string=? (substring n 0 9) "%hiddenv:"))
                               (cons (string->symbol (substring n 9 (string-length n))) out)
                               out))))))
;; Whether item `it` defines values: a `define` or a `define-rec`.
(define k-value-item? (->* (k-item) bool)
  (lambda (it) (or (= (extract it 1) 2) (= (extract it 1) 3))))
(define k-items-include? (->* (k-items) bool)
  (lambda (items)
    (and (not (null? items))
         (or (and (k-value-item? (car items)) (k-include-name? (extract (car items) 2)))
             (k-items-include? (cdr items))))))
(define k-include-name? (->* (k-names) bool)
  (lambda (ns)
    (and (not (null? ns))
         (let ((n (symbol->string (car ns))))
           (or (and (>= (string-length n) 8) (string=? (substring n 0 8) "%include"))
               (k-include-name? (cdr ns)))))))
(define k-shown-values (->* (k-items k-names k-names) k-names)
  (lambda (items hidden out)
    (if (null? items)
        out
        (k-shown-values (cdr items) hidden
                        (if (k-value-item? (car items))
                            (k-shown-onto (extract (car items) 2) hidden out)
                            out)))))
(define k-shown-onto (->* (k-names k-names k-names) k-names)
  (lambda (ns hidden out)
    (if (null? ns)
        out
        (k-shown-onto (cdr ns) hidden
                      (if (or (k-has-name? hidden (car ns))
                              (string=? (substring (symbol->string (car ns)) 0 1) "%"))
                          out
                          (cons (car ns) out))))))

(define-rec
  (k-free-list (->* (kxs k-names k-wlocals k-names) k-names)
    (lambda (xs bound ls out)
      (if (null? xs) out (k-free-list (cdr xs) bound ls (k-free-in (car xs) bound ls out)))))
  (k-free-in (->* (kx k-names k-wlocals k-names) k-names)
    (lambda (x bound ls out)
      (tagcase x
        (x-var (s a b abk) (k-note s bound out))
        (x-const (t v a b abk) out)
        (x-lambda (ps body a b abk) (k-free-in body (k-param-names ps bound) ls out))
        (x-app (f args a b abk) (k-free-list args bound ls (k-free-in f bound ls out)))
        (x-plambda (bs body a b abk) (k-free-in body bound ls out))
        (x-letregion (k r i body a b abk) (k-free-in body (cons (k-dvar-name r) bound) ls out))
        (x-rlambda (r l a b abk) (k-free-in l bound ls (k-free-in r bound ls out)))
        (x-proj (body ds a b abk) (k-free-in body bound ls out))
        (x-if (p c d a b abk)
          (k-free-in d bound ls (k-free-in c bound ls (k-free-in p bound ls out))))
        (x-letrec (bs body a b abk)
          (let ((inner (k-letrec-names bs bound)))
            (k-free-in body inner ls (k-free-letrec bs inner ls out))))
        (x-let (bs body a b abk)
          (k-free-in body (k-let-names bs bound) (k-wlocals-let bs (+ (k-length bound) 1) ls)
                     (k-free-let bs bound ls out)))
        (x-begin (xs a b abk) (k-free-list xs bound ls out))
        (x-prompt (t body h a b abk)
          (k-free-in h bound ls (k-free-in body bound ls (k-free-in t bound ls out))))
        (x-the (t body a b abk) (k-free-in body bound ls out))
        (x-convention (c body a b abk) (k-free-in body bound ls out))
        (x-bloblet (o i xs a b abk) (k-free-list xs bound ls out))
        ;; A product's fields are as a `let`'s bindings.
        (x-product (fs a b abk) (k-free-let fs bound ls out))
        (x-extract (body l a b abk) (k-free-in body bound ls out))
        (x-sum (l body a b abk) (k-free-in body bound ls out))
        (x-tagcase (s arms els a b abk)
          (let ((o (k-free-arms arms bound ls (k-free-in s bound ls out))))
            (k-free-else els bound ls o)))
        (x-module (items a b abk) (k-free-module items bound ls out))
        ;; The module, and the body, which sees its values once checked (or, an
        ;; earlier item's of a module being ordered, `k-with-bound`; or a
        ;; module a `let` binds to one written there, `ls`'s).
        ;; `(with #%fx n)`, the standard `n`: nothing free.
        (x-with (m body a b abk)
          (if (k-fx-module? m)
              out
              (k-free-in body
                         (k-names-onto (k-with-bound m a b abk bound)
                                       (k-names-onto (k-wlocal-vals ls (k-bound-at bound m))
                                                     bound))
                         ls (k-note m bound out)))))))
  ;; A module's free variables, onto `out`: each item's, every item's names
  ;; bound, as a `letrec*`'s (`check-modorder.fx`).
  (k-free-module (->* (k-items k-names k-wlocals k-names) k-names)
    (lambda (items bound ls out) (k-free-items items (k-items-bound items bound) ls out)))
  (k-free-items (->* (k-items k-names k-wlocals k-names) k-names)
    (lambda (items bound ls out)
      (if (null? items)
          out
          (k-free-items (cdr items) bound ls (k-free-list (extract (car items) 5) bound ls out)))))
  (k-free-letrec (->* (k-letrec-bs k-names k-wlocals k-names) k-names)
    (lambda (bs bound ls out)
      (if (null? bs)
          out
          (k-free-letrec (cdr bs) bound ls (k-free-in (extract (car bs) 3) bound ls out)))))
  (k-free-let (->* (k-let-bs k-names k-wlocals k-names) k-names)
    (lambda (bs bound ls out)
      (if (null? bs)
          out
          (k-free-let (cdr bs) bound ls (k-free-in (extract (car bs) 2) bound ls out)))))
  (k-free-arms (->* (k-arms k-names k-wlocals k-names) k-names)
    (lambda (arms bound ls out)
      (if (null? arms)
          out
          (let ((arm (car arms)))
            (k-free-arms (cdr arms) bound ls
                         (k-free-in (extract arm 4) (k-names-onto (extract arm 3) bound)
                                    ls out))))))
  ;; A `tagcase`'s `else` arm, if any: its body's, its variable bound.
  (k-free-else (->* (k-let-bs k-names k-wlocals k-names) k-names)
    (lambda (els bound ls out)
      (if (null? els)
          out
          (k-free-in (extract (car els) 2) (cons (extract (car els) 1) bound) ls out)))))
(define k-free-into (->* (kx k-names k-names) k-names)
  (lambda (x bound out) (k-free-in x bound nil out)))

;;; ------------------------------------------------------------ free variables

(define k-free-vars (->* (kx) k-names)
  (lambda (x) (k-free-into x nil nil)))

;;; ------------------------------------------------------------ substitution

(define k-ty-rank (->* (int) int)
  (lambda (t)
    (tagcase (k-get t)
      (ty-base (s) 0) (ty-void () 1) (ty-var (v) 2) (ty-subr (e ps r cv spc) 3) (ty-poly (bs x) 4)
      (ty-ref (x r) 5) (ty-pair (x y r nl) 6) (ty-tag (x y e r) 7) (ty-comp (x y e r once) 8)
      (ty-markkey (x r) 9) (ty-product (ps) 10) (ty-sum (ps) 11) (ty-array (x nz r) 12)
      (ty-bloblet (fs z r) 13) (ty-link (x) 14) (ty-icell (x r) 15) (ty-place (r) 16)
      (ty-named (g ds) 17) (ty-nlist (e z r) 18) (ty-nat (z) 19)
      (ty-module (abs ds vs) 20) (ty-select (m n) 21) (ty-param (k n) 22)
      (ty-lam (bs x) 23) (ty-app (f ds) 24) (ty-nil () 25) (ty-union (ms) 26)
      (ty-false () 28))))
;; Whether no instantiation of `pattern` could fit `actual`.
;; Whether a lemma's side `pat` could fit `t`, by their outermost shapes.
(define k-lemma-head? (->* (k-binders int int) bool)
  (lambda (bs pat t)
    (let ((p (k-resolve pat)))
      (tagcase (k-get p)
        (ty-var (v) (or (k-binder-has? bs v) (= (k-ty-rank p) (k-ty-rank t))))
        (ty-named (g xs) (tagcase (k-get t) (ty-named (h ys) (= g h)) (else z #f)))
        (else z (= (k-ty-rank p) (k-ty-rank t)))))))
;; Whether lemma `l`'s two sides could fit `a` and `b`, by their outermost
;; shapes.
(define k-lemma-heads? (->* (k-lemma int int) bool)
  (lambda (l a b)
    (let ((bs (extract l 1)))
      (and (k-lemma-head? bs (extract l 2) a) (k-lemma-head? bs (extract l 3) b)))))
(define k-lemma-may-apply? (->* ((listof k-lemma acyclic) int int) bool)
  (lambda (ls a b)
    (and (not (null? ls))
         (or (k-lemma-heads? (car ls) a b)
             (k-lemma-may-apply? (cdr ls) a b)))))
(define k-pair-seen? (->* (k-pairs int int) bool)
  (lambda (xs a b)
    (and (not (null? xs))
         (or (and (= (car (car xs)) a) (= (cdr (car xs)) b)) (k-pair-seen? (cdr xs) a b)))))
(define k-all-bound? (->* (k-binders k-map) bool)
  (lambda (bs m)
    (or (null? bs)
        (and (not (null? (k-map-find m (extract (car bs) 1)))) (k-all-bound? (cdr bs) m)))))
(define k-subst-hyps (->* (k-hyps k-map) k-hyps)
  (lambda (hs m)
    (if (null? hs)
        nil
        (let* ((x (k-subst (car (car hs)) m)) (y (k-subst (cdr (car hs)) m)))
          (the k-hyps (cons (cons x y) (k-subst-hyps (cdr hs) m)))))))
;; The `g`th generative type's representation, for `ds`.
(define k-unfold (->* (int k-descs) int)
  (lambda (g ds)
    (let ((gen (k-gen-of g))) (k-subst (extract gen 4) (k-gen-map (extract gen 2) ds)))))

;; `b`'s binders renamed to `a`'s, for comparing under them.
(define k-rename (->* (k-binders k-binders) k-map)
  (lambda (bs as)
    (if (null? bs)
        nil
        (let* ((vb (extract (car bs) 1)) (k (extract (car bs) 2)) (va (extract (car as) 1))
               (d (k-binder-desc k va))
               (rest (k-rename (cdr bs) (cdr as))))
          (cons (cons vb d) rest)))))
(define k-same-kinds? (->* (k-binders k-binders) bool)
  (lambda (xs ys)
    (cond ((null? xs) (null? ys))
          ((null? ys) #f)
          (else (and (= (extract (car xs) 2) (extract (car ys) 2))
                     (k-same-kinds? (cdr xs) (cdr ys))))))))))
