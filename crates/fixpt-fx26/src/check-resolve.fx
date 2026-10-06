;;; The checker, in FX-26: resolving the trees' descriptions, callables,
;;; regions of types, masking and substitution.
;;; Part of the checker, `check-types.fx` first (PLAN.md §11, step 10).

;;; ------------------------------------------------------------ resolving
;;; The parser's trees to `kx`, reading descriptions where the Rust parser
;;; does.

;; A module (`TODO.md` §34: the front end into modules, a file at a time);
;; what other files use re-exported after it.
(define check-resolve-module (module
;; The parts of a resolved tree, as `kx`'s constructors hold them: a
;; `lambda`'s parameters, a `letrec`'s and a `let`'s bindings (a product's
;; fields are as a `let`'s), and a `tagcase`'s arms.
(define-type k-typed-params (listof (productof (1 symbol) (2 k-ids)) acyclic))
(define-type k-letrec-bs (listof (productof (1 symbol) (2 int) (3 kx)) acyclic))
(define-type k-let-bs (listof (productof (1 symbol) (2 kx)) acyclic))
(define-type k-arms (listof (productof (1 symbol) (2 bool) (3 k-names) (4 kx)) acyclic))
;; The same, of the parser's trees.
(define-type exp-params (listof (productof (1 symbol) (2 syns-a)) acyclic))
(define-type exp-letrec-bs (listof (productof (1 symbol) (2 syn) (3 exp)) acyclic))
(define-type exp-let-bs (listof (productof (1 symbol) (2 exp)) acyclic))
(define-type exp-arms (listof (productof (1 symbol) (2 bool) (3 names) (4 exp)) acyclic))
;; Looking at the checker's tables (`kreads`), and building more in their
;; region.
(define-effect kmakes (maxeff kreads (alloc @t)))

(define k-start (subr pure (kx) int)
  (lambda (x)
    (tagcase x
      (x-var (s a b) a) (x-const (t v a b) a) (x-lambda (ps e a b) a) (x-app (f xs a b) a)
      (x-plambda (bs e a b) a) (x-proj (e ds a b) a) (x-if (p c d a b) a) (x-letrec (bs e a b) a)
      (x-let (bs e a b) a) (x-begin (xs a b) a) (x-prompt (t e h a b) a) (x-the (t e a b) a)
      (x-convention (c e a b) a) (x-bloblet (o i xs a b) a) (x-product (fs a b) a)
      (x-extract (e l a b) a) (x-sum (l e a b) a) (x-tagcase (e arms els a b) a)
      (x-letregion (k r i e a b) a) (x-rlambda (r l a b) a)
      (x-module (items a b) a) (x-with (m e a b) a))))
(define k-end (subr pure (kx) int)
  (lambda (x)
    (tagcase x
      (x-var (s a b) b) (x-const (t v a b) b) (x-lambda (ps e a b) b) (x-app (f xs a b) b)
      (x-plambda (bs e a b) b) (x-proj (e ds a b) b) (x-if (p c d a b) b) (x-letrec (bs e a b) b)
      (x-let (bs e a b) b) (x-begin (xs a b) b) (x-prompt (t e h a b) b) (x-the (t e a b) b)
      (x-convention (c e a b) b) (x-bloblet (o i xs a b) b) (x-product (fs a b) b)
      (x-extract (e l a b) b) (x-sum (l e a b) b) (x-tagcase (e arms els a b) b)
      (x-letregion (k r i e a b) b) (x-rlambda (r l a b) b)
      (x-module (items a b) b) (x-with (m e a b) b))))
(define k-same-span? (subr (read @globals) (kx int int) bool)
  (lambda (x a b) (and (= (k-start x) a) (= (k-end x) b))))

(define k-resolve-params (subr (maxeff checks spin) (exp-params) k-typed-params)
  (lambda (ps)
    (if (null? ps)
        nil
        (let* ((ty (extract (car ps) 2))
               (t (if (null? ty) (the k-ids nil) (the k-ids (cons (k-parse-type (car ty)) nil))))
               (rest (k-resolve-params (cdr ps))))
          (cons (product (1 (extract (car ps) 1)) (2 t)) rest)))))
(define k-resolve-descs (subr (maxeff checks spin) (syns-a) k-descs)
  (lambda (ds)
    (if (null? ds)
        nil
        (let* ((d (k-parse-d (car ds))) (rest (k-resolve-descs (cdr ds))))
          (cons d rest)))))
(define k-copy-names (subr (maxeff (read @globals) (alloc @t)) (names) k-names)
  (lambda (ns) (if (null? ns) nil (cons (car ns) (k-copy-names (cdr ns))))))

;; Where a parser's tree starts and ends.
(define exp-start (subr pure (exp) int)
  (lambda (e)
    (tagcase e
      (e-var (s a b) a) (e-int (n a b) a) (e-bool (v a b) a) (e-str (v a b) a) (e-char (v a b) a)
      (e-float (v a b) a)
      (e-sym (v a b) a) (e-unit (a b) a) (e-lambda (ps x a b) a) (e-app (f xs a b) a)
      (e-plambda (bs x a b) a) (e-proj (x ds a b) a) (e-if (p c d a b) a) (e-letrec (bs x a b) a)
      (e-let (bs x a b) a) (e-begin (xs a b) a) (e-prompt (t x h a b) a) (e-the (t x a b) a)
      (e-convention (c x a b) a) (e-bloblet (o i xs a b) a) (e-product (fs a b) a)
      (e-extract (x l a b) a) (e-sum (l x a b) a) (e-tagcase (x arms els a b) a)
      (e-letregion (k r i x a b) a) (e-rlambda (r l a b) a)
      (e-module (items a b) a) (e-with (m x a b) a))))
(define exp-end (subr pure (exp) int)
  (lambda (e)
    (tagcase e
      (e-var (s a b) b) (e-int (n a b) b) (e-bool (v a b) b) (e-str (v a b) b) (e-char (v a b) b)
      (e-float (v a b) b)
      (e-sym (v a b) b) (e-unit (a b) b) (e-lambda (ps x a b) b) (e-app (f xs a b) b)
      (e-plambda (bs x a b) b) (e-proj (x ds a b) b) (e-if (p c d a b) b) (e-letrec (bs x a b) b)
      (e-let (bs x a b) b) (e-begin (xs a b) b) (e-prompt (t x h a b) b) (e-the (t x a b) b)
      (e-convention (c x a b) b) (e-bloblet (o i xs a b) b) (e-product (fs a b) b)
      (e-extract (x l a b) b) (e-sum (l x a b) b) (e-tagcase (x arms els a b) b)
      (e-letregion (k r i x a b) b) (e-rlambda (r l a b) b)
      (e-module (items a b) b) (e-with (m x a b) b))))

;; A `plambda`'s region and place binders: each won't outlive what is bound
;; around it (`lives`), and each is around what its body binds.
(define k-order-binders (subr kstate (k-binders k-ids) unit)
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
(define k-resolve-place (subr checks (symbol int int) k-region)
  (lambda (n a b)
    (if (symbol=? n 'heap)
        (r-heap)
        (let ((d (k-lookup-desc n)))
          (if (null? d)
              (k-fail (k-cat3 "`" (symbol->string n) "` is not a region") a b)
              (tagcase (car d)
                (ds-var (v k)
                  (cond ((= k 3) (r-var v))
                        ((= k 0) (k-fail (k-cat3 "`" (symbol->string n) "` is not a place") a b))
                        (else (k-fail (k-cat3 "`" (symbol->string n) "` is not a region") a b))))
                (else x (k-fail (k-cat3 "`" (symbol->string n) "` is not a region") a b))))))))
;; What a `letfreeze` into `place` freezes into: `(const p)` for its
;; place `p`, and for the heap, -1.
(define* k-freeze-into (subr pure (k-region) k-region)
  (lambda (place) (tagcase place (r-var (p) (r-frozen p #f)) (else y (r-frozen -1 #f)))))
;; What a `letfreeze` into `place` won't outlive: the place, and what it
;; won't.
(define k-place-lives (subr kmakes (k-region) k-ids)
  (lambda (place) (tagcase place (r-var (p) (cons p (k-outer-of p))) (else y nil))))

;; A `module`'s items read, by `check-modules.fx`, which sets this.
(define k-resolve-module (ref (subr (maxeff checks spin) (mod-items int int) kx) @t)
  (new (lambda (items a b) (k-fail "a module" a b))))

(define-rec
  (k-resolve-all (subr (maxeff checks spin) ((listof exp acyclic)) kxs)
    (lambda (es)
      (if (null? es)
          nil
          (let* ((x (k-resolve-exp (car es))) (rest (k-resolve-all (cdr es))))
            (cons x rest)))))
  (k-resolve-exp (subr (maxeff checks spin) (exp) kx)
    (lambda (e)
      (tagcase e
        (e-var (s a b) (x-var s a b))
        (e-int (n a b) (x-const k-int n a b))
        (e-bool (v a b) (x-const k-bool (if v 1 0) a b))
        (e-str (v a b) (x-const k-string 0 a b))
        (e-char (v a b) (x-const k-char 0 a b))
        (e-float (v a b) (x-const k-f64 0 a b))
        (e-sym (v a b) (x-const k-symbol 0 a b))
        (e-unit (a b) (x-const k-unit 0 a b))
        (e-lambda (ps body a b)
          (let* ((params (k-resolve-params ps)) (x (k-resolve-exp body))) (x-lambda params x a b)))
        (e-app (f args a b)
          (let* ((fx (k-resolve-exp f)) (xs (k-resolve-all args))) (x-app fx xs a b)))
        (e-plambda (binders body a b)
          (let* ((saved (get k-dscope))
                 (lives (get k-lifetimes))
                 (bs (k-parse-binders binders))
                 ;; A procedure's regions and places outlive whatever its
                 ;; body binds.
                 (ordered (k-order-binders bs lives))
                 (x (k-resolve-exp body)))
            (begin (set k-dscope saved) (set k-lifetimes lives) (x-plambda bs x a b))))
        (e-rlambda (r l a b)
          (let* ((rx (k-resolve-exp r)) (lx (k-resolve-exp l))) (x-rlambda rx lx a b)))
        (e-letregion (k name into body a b)
          (let* ((saved (get k-dscope))
                 ;; `letrena` and `letreap` make a place (which is also a
                 ;; region), `letregion` a region only.
                 (kind (if (or (= k 0) (= k 3)) 0 3))
                 (place (if (= k 3) (k-resolve-place into a b) (r-heap)))
                 (v (k-new-dvar-of name kind))
                 (lives (get k-lifetimes))
                 ;; A `letfreeze`'s data leaves in the place it freezes into,
                 ;; so it may be allocated only in that place or one outliving
                 ;; it: those are all it won't outlive.
                 (ordered (begin
                            (k-set-outer v (if (= k 3) (k-place-lives place) lives))
                            (set k-lifetimes (cons v lives))))
                 (pushed (k-push-desc name (ds-var v kind)))
                 (x (k-resolve-exp body)))
            (begin (set k-dscope saved) (set k-lifetimes lives)
                   (x-letregion k v (k-freeze-into place) x a b))))
        (e-proj (body ds a b)
          (let* ((x (k-resolve-exp body)) (descs (k-resolve-descs ds))) (x-proj x descs a b)))
        (e-if (p c d a b)
          (let* ((px (k-resolve-exp p)) (cx (k-resolve-exp c)) (dx (k-resolve-exp d)))
            (x-if px cx dx a b)))
        (e-letrec (bs body a b)
          (let* ((rbs (k-resolve-letrec bs)) (x (k-resolve-exp body))) (x-letrec rbs x a b)))
        (e-let (bs body a b)
          (let* ((rbs (k-resolve-let bs)) (x (k-resolve-exp body))) (x-let rbs x a b)))
        (e-begin (es a b) (x-begin (k-resolve-all es) a b))
        (e-prompt (t body h a b)
          (let* ((tx (k-resolve-exp t)) (bx (k-resolve-exp body)) (hx (k-resolve-exp h)))
            (x-prompt tx bx hx a b)))
        (e-the (ty body a b)
          (let* ((t (k-parse-type ty)) (x (k-resolve-exp body))) (x-the t x a b)))
        (e-convention (c body a b)
          (let* ((cv (k-parse-conv c)) (x (k-resolve-exp body))) (x-convention cv x a b)))
        (e-bloblet (op i args a b) (x-bloblet op i (k-resolve-all args) a b))
        (e-product (fs a b) (x-product (k-resolve-fields fs nil a b) a b))
        (e-extract (body l a b) (x-extract (k-resolve-exp body) l a b))
        (e-sum (l body a b) (x-sum l (k-resolve-exp body) a b))
        (e-tagcase (s arms els a b)
          ;; The `else` arm, if any, is resolved as a `let` binding is.
          (let* ((sx (k-resolve-exp s))
                 (rarms (k-resolve-arms arms nil))
                 (rels (k-resolve-let els)))
            (x-tagcase sx rarms rels a b)))
        (e-module (items a b) ((get k-resolve-module) items a b))
        (e-with (m body a b) (x-with m (k-resolve-exp body) a b)))))
  (k-resolve-letrec (subr (maxeff checks spin) (exp-letrec-bs) k-letrec-bs)
    (lambda (bs)
      (if (null? bs)
          nil
          (let* ((t (k-parse-type (extract (car bs) 2)))
                 (x (k-resolve-exp (extract (car bs) 3)))
                 (rest (k-resolve-letrec (cdr bs))))
            (cons (product (1 (extract (car bs) 1)) (2 t) (3 x)) rest)))))
  (k-resolve-let (subr (maxeff checks spin) (exp-let-bs) k-let-bs)
    (lambda (bs)
      (if (null? bs)
          nil
          (let* ((x (k-resolve-exp (extract (car bs) 2))) (rest (k-resolve-let (cdr bs))))
            (cons (product (1 (extract (car bs) 1)) (2 x)) rest)))))
  (k-resolve-fields (subr (maxeff checks spin) (exp-let-bs k-names int int) k-let-bs)
    (lambda (fs seen a b)
      (if (null? fs)
          nil
          (let ((l (extract (car fs) 1)))
            (if (k-has-name? seen l)
                (k-fail (string-append (k-quote (symbol->string l)) " appears twice") a b)
                (let* ((x (k-resolve-exp (extract (car fs) 2)))
                       (rest (k-resolve-fields (cdr fs) (cons l seen) a b)))
                  (cons (product (1 l) (2 x)) rest)))))))
  (k-resolve-arms (subr (maxeff checks spin) (exp-arms k-names) k-arms)
    (lambda (arms seen)
      (if (null? arms)
          nil
          (let* ((arm (car arms)) (tag (extract arm 1)))
            (if (k-has-name? seen tag)
                (k-fail (string-append (k-quote (symbol->string tag)) " has two arms")
                        (exp-start (extract arm 4)) (exp-end (extract arm 4)))
                (let* ((x (k-resolve-exp (extract arm 4)))
                       (rest (k-resolve-arms (cdr arms) (cons tag seen)))
                       (names (k-copy-names (extract arm 3))))
                  (cons (product (1 tag) (2 (extract arm 2)) (3 names) (4 x)) rest))))))))

;;; ------------------------------------------------------------ callables

;; What calling a value of type `t` does: its latent effect, parameters and
;; result, as none or one. A composable continuation runs the rest of its
;; prompt's body, with control effects on the tag's region.
(define-type k-callable (productof (1 k-eff) (2 k-ids) (3 int)))
(define k-as-subr (subr (maxeff kmakes spin) (int) (listof k-callable acyclic))
  (lambda (t)
    (tagcase (k-get t)
      (ty-subr (e ps r cv) (cons (product (1 e) (2 ps) (3 r)) nil))
      (ty-comp (arg answer e r)
        (let ((control (k-insert (a-goto r) (k-insert (a-comefrom r) e))))
          (cons (product (1 control) (2 (the k-ids (cons arg nil))) (3 answer)) nil)))
      (else x nil))))
;; No `vsubr`; one, of latent effect `e`, arguments of type `a`, result `r`.
(define k-vsub-none k-vsub nil)
(define k-vsub-one (subr (alloc @t) (k-eff int int) k-vsub)
  (lambda (e a r) (cons (product (1 e) (2 a) (3 r)) nil)))
;; `vsubr`'s three descriptions, an effect and two types, as `k-vsubr-parts`
;; gives them.
(define* k-vsubr-descs (subr (alloc @t) (k-desc k-desc k-desc) k-vsub)
  (lambda (e a r)
    (tagcase e
      (de (le)
        (tagcase a
          (dt (at) (tagcase r (dt (rt) (k-vsub-one le at rt)) (else z k-vsub-none)))
          (else z k-vsub-none)))
      (else z k-vsub-none))))
;; A `vsubr` (generative type 0), taken apart: its latent effect, the type of
;; each argument, and the result's, in a list; none for any other type.
(define k-vsubr-parts (subr (maxeff kmakes spin) (int) k-vsub)
  (lambda (t)
    (tagcase (k-get t)
      (ty-named (g ds)
        (if (and (= g 0) (= (k-length ds) 3))
            (k-vsubr-descs (car ds) (car (cdr ds)) (car (cdr (cdr ds))))
            k-vsub-none))
      (else y k-vsub-none))))
;; `n` copies of type `t`, onto `acc`.
(define* k-repeat-id (subr (maxeff (alloc @t) spin) (int int k-ids) k-ids)
  (lambda (t n acc) (if (<= n 0) acc (k-repeat-id t (- n 1) (cons t acc)))))
;; What `t` is called as, with `n` arguments: a subroutine; a `vsubr` (a
;; standard `list`), as one of `n` parameters, each of its argument type;
;; or none.
(define k-callee-of (subr (maxeff kmakes spin) (int int) (listof k-callable acyclic))
  (lambda (t n)
    (let ((v (k-vsubr-parts t)))
      (if (null? v)
          (k-as-subr t)
          (let* ((p (car v)) (ps (k-repeat-id (extract p 2) n (the k-ids nil))))
            (cons (product (1 (extract p 1)) (2 ps) (3 (extract p 3))) nil))))))

;;; ------------------------------------------------------------ regions of types

(define k-has-region-in? (subr (maxeff kreads spin) (k-regions k-region) bool)
  (lambda (rs r)
    (cond ((null? rs) #f)
          ((k-region=? (car rs) r) #t)
          (else (k-has-region-in? (cdr rs) r)))))
(define k-add-region (subr (maxeff kmakes spin) (k-regions k-region) k-regions)
  (lambda (rs r) (if (k-has-region-in? rs r) rs (cons r rs))))
;; `out` and each of `rs` that is not a generative type's parameter.
(define k-add-non-gen (subr (maxeff kmakes spin) (k-regions k-regions) k-regions)
  (lambda (out rs)
    (cond ((null? rs) out)
          ((k-gen-region? (car rs)) (k-add-non-gen out (cdr rs)))
          (else (k-add-non-gen (k-add-region out (car rs)) (cdr rs))))))
(define k-add-eff-regions (subr (maxeff kmakes spin) (k-regions k-eff) k-regions)
  (lambda (rs e)
    (cond ((null? e) rs)
          ((k-has-region? (car e))
           (k-add-eff-regions (k-add-region rs (k-atom-region (car e))) (cdr e)))
          (else (k-add-eff-regions rs (cdr e))))))

;; Every region mentioned in type `t`, following recursive types once.
;; Kept once found, by type: a type does not change once built.
(define-type k-region-lists (arrayof (listof k-regions acyclic) @t))
(define k-regions-memo (ref k-region-lists @t) (new (make-array 512 nil)))

;; A definition checked, as a redefinition finds it: the names it defines,
;; its tree, and the globals it uses (its expressions' free variables).
(define-type k-def (productof (1 k-names) (2 top) (3 k-names)))
;; The definitions checked so far, newest first, each the latest of its
;; names.
(define k-defs (ref (listof k-def acyclic) @t) (new nil))
;; The free variables of the definition being checked, for `k-record`.
(define k-last-uses (ref k-names @t) (new nil))
;; What the program runs, newest first: each top-level form, and the
;; definitions run again for a redefinition, each with whether it assigns
;; its names' globals rather than making new ones.
(define-type k-run (productof (1 top) (2 bool)))
(define k-runs (ref (listof k-run acyclic) @t) (new nil))
;; For `k-reset`: forget the description variables, and what is known of
;; the regions and places among them.
(define k-reset-regions (subr kstate () unit)
  (lambda ()
    (begin
      (set k-dvars nil) (set k-ndvars 0) (set k-places nil) (set k-bounds nil) (set k-outers nil)
      (set k-lifetimes nil) (set k-freezing nil) (set k-written nil)
      (set k-arrow-vars nil) (set k-abstract-funs nil))))
;; Forget the names bound, and what is known of them.
(define k-reset-names (subr kstate () unit)
  (lambda ()
    (begin
      (set k-known (make-table symbol-hash symbol=?))
      (set k-global (make-table symbol-hash symbol=?))
      (set k-recursive nil) (set k-std nil) (set k-env (make-table symbol-hash symbol=?))
      (set k-trail nil) (set k-depth 0))))
;; Forget the lemmas, and the facts learned of data and sizes.
(define k-reset-facts (subr kstate () unit)
  (lambda ()
    (begin
      (set k-lemmas nil) (set k-pending-lemma nil) (set k-datas nil) (set k-certified nil)
      (set k-certified-lengths nil) (set k-certified-nats nil) (set k-size-facts nil)
      (set k-skolems nil))))
(define k-reset (subr (maxeff kstate spin) () unit)
  (lambda ()
    (begin
      (set k-extracts nil) (set k-effect-notes nil)
      (set k-ntys 0) (k-reset-regions) (k-reset-names)
      (set k-regions-memo (make-array 512 nil)) (set k-dscope nil)
      (set k-fresh 0) (set k-base nil) (set k-expanding 0) (set k-knots nil) (set k-spin-why nil)
      (set k-gens nil) (set k-ngens 0) (set k-transparent nil) (set k-inside nil)
      (set k-conversions nil) (k-reset-facts)
      (set k-broken nil) (set k-defs nil) (set k-runs nil) (set k-last-uses nil)
      (set k-with-vals nil) (set k-module-vars nil) (set k-select-map nil) (set k-reshapes nil)
      (set k-hide-mark -1) (set k-param-map nil) (set k-effect-selects nil)
      (k-basic "int") (k-basic "bool") (k-basic "string") (k-basic "unit") (k-basic "char")
      (k-basic "datum") (k-basic "symbol") (k-basic "tword") (k-basic "wcell") (k-basic "wglobal")
      ;; 10 to 15; `void` 16, `k-void`.
      (k-basic "i32") (k-basic "u32") (k-basic "i64") (k-basic "u64")
      (k-basic "f64") (k-basic "f32")
      (k-ty-new (ty-void))
      #u)))
(define n-copy-memo (subr (maxeff kreads (write @t) spin) (k-region-lists k-region-lists int) unit)
  (lambda (from to i)
    (if (= i (array-length from))
        #u
        (begin (array-set! to i (array-ref from i)) (n-copy-memo from to (+ i 1))))))
(define k-remember-regions (subr (maxeff kstate spin) (int k-regions) unit)
  (lambda (t rs)
    (begin
      (if (>= t (array-length (get k-regions-memo)))
          (let ((bigger (the k-region-lists (make-array (* 2 (array-length (get k-tys))) nil))))
            (begin (n-copy-memo (get k-regions-memo) bigger 0) (set k-regions-memo bigger)))
          #u)
      (array-set! (get k-regions-memo) t (cons rs nil)))))
;; Add to `out` the regions of `e`'s atoms.
(define k-note-eff-regions (subr (maxeff kstate spin) ((ref k-regions @t) k-eff) unit)
  (lambda (out e) (set out (k-add-eff-regions (get out) e))))

(define-rec
  (k-regions-walk (subr (maxeff kstate spin) (int int (ref k-regions @t)) unit)
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
                  (ty-subr (e ps r cv) (begin (k-note-eff-regions out e) (walks ps) (walk r)))
                  (ty-poly (bs body) (walk body))
                  (ty-ref (a r) (begin (add r) (walk a)))
                  (ty-array (a r) (begin (add r) (walk a)))
                  (ty-icell (a r) (begin (add r) (walk a)))
                  (ty-place (r) (add r))
                  (ty-pair (a b r) (begin (add r) (walk a) (walk b)))
                  (ty-tag (a h e r) (begin (add r) (k-note-eff-regions out e) (walk a) (walk h)))
                  (ty-comp (b a e r) (begin (add r) (k-note-eff-regions out e) (walk a) (walk b)))
                  (ty-markkey (a r) (begin (add r) (walk a)))
                  (ty-bloblet (fs z r) (begin (add r) (walks fs)))
                  (ty-product (ps) (k-regions-parts ps seen out))
                  (ty-sum (ps) (k-regions-parts ps seen out))
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
  (k-regions-descs (subr (maxeff kstate spin) (k-descs int (ref k-regions @t)) unit)
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
  (k-regions-walks (subr (maxeff kstate spin) (k-ids int (ref k-regions @t)) unit)
    (lambda (ts seen out)
      (if (null? ts)
          #u
          (begin (k-regions-walk (car ts) seen out) (k-regions-walks (cdr ts) seen out)))))
  (k-regions-parts (subr (maxeff kstate spin) (k-parts int (ref k-regions @t)) unit)
    (lambda (ps seen out)
      (if (null? ps)
          #u
          (begin (k-regions-walk (extract (car ps) 2) seen out)
                 (k-regions-parts (cdr ps) seen out))))))
(define k-frozen-places (subr (maxeff kmakes spin) (k-regions k-regions) k-regions)
  (lambda (rs out)
    (if (null? rs)
        out
        (let ((out (tagcase (car rs)
                     (r-frozen (p f) (if (< p 0) out (k-add-region out (r-var p))))
                     (else y out))))
          (k-frozen-places (cdr rs) out)))))
(define k-regions-in (subr (maxeff kstate spin) (int) k-regions)
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
(define k-note (subr kmakes (symbol k-names k-names) k-names)
  (lambda (s bound out) (if (or (k-has-name? bound s) (k-has-name? out s)) out (cons s out))))
(define k-names-onto (subr kmakes (k-names k-names) k-names)
  (lambda (ns bound) (if (null? ns) bound (k-names-onto (cdr ns) (cons (car ns) bound)))))
;; `bound`, and the names `ps`, `bs` bind.
(define k-param-names (subr kmakes (k-typed-params k-names) k-names)
  (lambda (ps bound)
    (if (null? ps) bound (k-param-names (cdr ps) (cons (extract (car ps) 1) bound)))))
(define k-letrec-names (subr kmakes (k-letrec-bs k-names) k-names)
  (lambda (bs bound)
    (if (null? bs) bound (k-letrec-names (cdr bs) (cons (extract (car bs) 1) bound)))))
(define k-let-names (subr kmakes (k-let-bs k-names) k-names)
  (lambda (bs bound)
    (if (null? bs) bound (k-let-names (cdr bs) (cons (extract (car bs) 1) bound)))))

;; `up-t` and `down-t`, an abstract type `t`'s conversions, onto `bound`.
(define k-conversion-name (subr (read @globals) (string symbol) symbol)
  (lambda (prefix n) (string->symbol (string-append prefix (symbol->string n)))))
(define k-conversions-onto (subr kmakes (symbol k-names) k-names)
  (lambda (n bound)
    (cons (k-conversion-name "down-" n) (cons (k-conversion-name "up-" n) bound))))
;; The names an item binds for those after it, onto `bound`: an abstract
;; type's conversions, a value's name, a group's.
(define k-item-bound (subr kmakes (k-item k-names) k-names)
  (lambda (it bound)
    (let ((k (extract it 1)) (ns (extract it 2)))
      (cond ((= k 0) (k-conversions-onto (car ns) bound))
            ((or (= k 1) (< k 0) (> k 3)) bound)
            (else (k-names-onto ns bound))))))
;; Every name `items` define, onto `bound`.
(define k-items-bound (subr kmakes (k-items k-names) k-names)
  (lambda (items bound)
    (if (null? items) bound (k-items-bound (cdr items) (k-item-bound (car items) bound)))))

(define-rec
  (k-free-list (subr kmakes (kxs k-names k-names) k-names)
    (lambda (xs bound out)
      (if (null? xs) out (k-free-list (cdr xs) bound (k-free-into (car xs) bound out)))))
  (k-free-into (subr kmakes (kx k-names k-names) k-names)
    (lambda (x bound out)
      (tagcase x
        (x-var (s a b) (k-note s bound out))
        (x-const (t v a b) out)
        (x-lambda (ps body a b) (k-free-into body (k-param-names ps bound) out))
        (x-app (f args a b) (k-free-list args bound (k-free-into f bound out)))
        (x-plambda (bs body a b) (k-free-into body bound out))
        (x-letregion (k r i body a b) (k-free-into body (cons (k-dvar-name r) bound) out))
        (x-rlambda (r l a b) (k-free-into l bound (k-free-into r bound out)))
        (x-proj (body ds a b) (k-free-into body bound out))
        (x-if (p c d a b) (k-free-into d bound (k-free-into c bound (k-free-into p bound out))))
        (x-letrec (bs body a b)
          (let ((inner (k-letrec-names bs bound)))
            (k-free-into body inner (k-free-letrec bs inner out))))
        (x-let (bs body a b) (k-free-into body (k-let-names bs bound) (k-free-let bs bound out)))
        (x-begin (xs a b) (k-free-list xs bound out))
        (x-prompt (t body h a b)
          (k-free-into h bound (k-free-into body bound (k-free-into t bound out))))
        (x-the (t body a b) (k-free-into body bound out))
        (x-convention (c body a b) (k-free-into body bound out))
        (x-bloblet (o i xs a b) (k-free-list xs bound out))
        ;; A product's fields are as a `let`'s bindings.
        (x-product (fs a b) (k-free-let fs bound out))
        (x-extract (body l a b) (k-free-into body bound out))
        (x-sum (l body a b) (k-free-into body bound out))
        (x-tagcase (s arms els a b)
          (let ((o (k-free-arms arms bound (k-free-into s bound out))))
            (k-free-else els bound o)))
        (x-module (items a b) (k-free-module items bound out))
        ;; The module, and the body, which sees its values once checked.
        (x-with (m body a b) (k-free-into body (k-names-onto (k-with-names a b) bound)
                                          (k-note m bound out))))))
  ;; A module's free variables, onto `out`: each item's, every item's names
  ;; bound, as a `letrec*`'s (`check-modorder.fx`).
  (k-free-module (subr kmakes (k-items k-names k-names) k-names)
    (lambda (items bound out) (k-free-items items (k-items-bound items bound) out)))
  (k-free-items (subr kmakes (k-items k-names k-names) k-names)
    (lambda (items bound out)
      (if (null? items)
          out
          (k-free-items (cdr items) bound (k-free-list (extract (car items) 5) bound out)))))
  (k-free-letrec (subr kmakes (k-letrec-bs k-names k-names) k-names)
    (lambda (bs bound out)
      (if (null? bs)
          out
          (k-free-letrec (cdr bs) bound (k-free-into (extract (car bs) 3) bound out)))))
  (k-free-let (subr kmakes (k-let-bs k-names k-names) k-names)
    (lambda (bs bound out)
      (if (null? bs)
          out
          (k-free-let (cdr bs) bound (k-free-into (extract (car bs) 2) bound out)))))
  (k-free-arms (subr kmakes (k-arms k-names k-names) k-names)
    (lambda (arms bound out)
      (if (null? arms)
          out
          (let ((arm (car arms)))
            (k-free-arms (cdr arms) bound
                         (k-free-into (extract arm 4) (k-names-onto (extract arm 3) bound) out))))))
  ;; A `tagcase`'s `else` arm, if any: its body's, its variable bound.
  (k-free-else (subr kmakes (k-let-bs k-names k-names) k-names)
    (lambda (els bound out)
      (if (null? els)
          out
          (k-free-into (extract (car els) 2) (cons (extract (car els) 1) bound) out)))))

;;; ------------------------------------------------------------ free variables

(define k-free-vars (subr kmakes (kx) k-names)
  (lambda (x) (k-free-into x nil nil)))

;;; ------------------------------------------------------------ substitution

(define k-gen-map (subr (maxeff (read @globals) (alloc @t)) (k-binders k-descs) k-map)
  (lambda (bs ds)
    (if (null? bs)
        nil
        (the k-map (cons (cons (extract (car bs) 1) (car ds)) (k-gen-map (cdr bs) (cdr ds)))))))
(define k-subst-conv (subr kreads (k-conv k-map) k-conv)
  (lambda (c m)
    (tagcase c
      (cv-var (v)
        (let ((f (k-map-find m v)))
          (if (null? f) c (tagcase (cdr (car f)) (dc (x) x) (else y c)))))
      (else y c))))
(define k-subst-region (subr kreads (k-region k-map) k-region)
  (lambda (r m)
    (tagcase r
      (r-var (v)
        (let ((f (k-map-find m v)))
          (if (null? f) r (tagcase (cdr (car f)) (dr (x) x) (else y r)))))
      ;; Frozen data's place too.
      (r-frozen (p fin)
        (let ((f (if (< p 0) (the k-map nil) (k-map-find m p))))
          (if (null? f)
              r
              (tagcase (cdr (car f))
                (dr (x)
                  (tagcase x (r-var (q) (r-frozen q fin)) (r-heap () (r-frozen -1 fin)) (else z r)))
                (else y r)))))
      (else y r))))
;; Atom `a`, not a variable, substituted into: none if it reads, allocates
;; or awaits at data frozen into the heap, which is pure (`k-frozen`), so
;; that a region variable instantiated at `acyclic` or `const` leaves none.
(define k-subst-atom (subr (maxeff kmakes spin) (k-atom k-map) k-eff)
  (lambda (a m)
    (let* ((r (k-subst-region (k-atom-region a) m))
           (heap-frozen (tagcase r (r-frozen (p f) (< p 0)) (else y #f)))
           (pure-there (tagcase a (a-read (x) #t) (a-alloc (x) #t) (a-await (x) #t) (else y #f))))
      (if (and heap-frozen pure-there) nil (k-one (k-atom-with a r))))))
(define-rec
  (k-subst-effect (subr (maxeff kmakes spin) (k-eff k-map) k-eff)
    (lambda (e m)
      (if (null? e)
          nil
          (let* ((a (car e))
                 (rest (k-subst-effect (cdr e) m))
                 (piece (tagcase a
                          (a-var (v)
                            (let ((f (k-map-find m v)))
                              (if (null? f)
                                  (k-one a)
                                  (tagcase (cdr (car f)) (de (x) x) (else y (k-one a))))))
                          (a-app (v ds) (k-subst-eff-app v (k-subst-eargs ds m) m))
                          (else y (k-subst-atom a m)))))
            (k-union piece rest)))))
  ;; What an effect function is given, substituted into.
  (k-subst-eargs (subr (maxeff kmakes spin) (k-descs k-map) k-descs)
    (lambda (ds m)
      (if (null? ds)
          nil
          (let* ((d (tagcase (car ds)
                      (dr (r) (dr (k-subst-region r m)))
                      (de (e) (de (k-subst-effect e m)))
                      (dz (z) (dz (k-subst-size z m)))
                      (dc (c) (dc (k-subst-conv c m)))
                      (else y (car ds))))
                 (rest (k-subst-eargs (cdr ds) m)))
            (the k-descs (cons d rest))))))
  ;; Effect function `v` applied to `ds`, given what `v` is substituted by:
  ;; reduced, if it is a `dlambda` now (`check-kinds.fx`).
  (k-subst-eff-app (subr (maxeff kmakes spin) (int k-descs k-map) k-eff)
    (lambda (v ds m)
      (let ((f (k-map-find m v)))
        (if (null? f)
            (k-one (a-app v ds))
            (tagcase (cdr (car f))
              (df (g)
                (tagcase (k-get g)
                  (ty-var (w) (k-one (a-app w ds)))
                  (ty-lam (bs body)
                    (tagcase body
                      (de (e)
                        (if (= (k-length bs) (k-length ds))
                            (k-subst-effect e (k-gen-map bs ds))
                            (k-one (a-app v ds))))
                      (else z (k-one (a-app v ds)))))
                  (else z (k-one (a-app v ds)))))
              (else y (k-one (a-app v ds)))))))))
;; What an effect function is given, of `ds`: no types.
(define k-eargs (subr (read @globals) (k-descs) k-descs)
  (lambda (ds)
    (cond ((null? ds) nil)
          ((tagcase (car ds) (dt (t) #t) (df (f) #t) (else y #f)) (k-eargs (cdr ds)))
          (else (the k-descs (cons (car ds) (k-eargs (cdr ds))))))))
;; `f` applied to `ds`, which cannot be reduced: an effect, an atom of its
;; own; a function; or a type.
(define k-apply-stuck (subr (maxeff kstate spin) (int k-descs) k-desc)
  (lambda (f ds)
    (let ((r (k-arrow-result (k-fun-kind f))))
      (cond ((= r 1)
             (tagcase (k-get f)
               (ty-var (v) (de (k-one (a-app v (k-eargs ds)))))
               (else y (de nil))))
            ((k-arrow-kind? r) (df (k-ty-new (ty-app f ds))))
            (else (dt (k-ty-new (ty-app f ds))))))))
;; What an application reduced gives as a type: a type, or else the
;; application `t` as it was.
(define k-applied-type (subr pure (k-desc int) int)
  (lambda (d t) (tagcase d (dt (x) x) (else y t))))
(define k-memo-find (subr kreads (k-pairs int) int)
  (lambda (ms t)
    (cond ((null? ms) -1)
          ((= (car (car ms)) t) (cdr (car ms)))
          (else (k-memo-find (cdr ms) t)))))

(define k-ty-rank (subr (maxeff kreads spin) (int) int)
  (lambda (t)
    (tagcase (k-get t)
      (ty-base (s) 0) (ty-void () 1) (ty-var (v) 2) (ty-subr (e ps r cv) 3) (ty-poly (bs x) 4)
      (ty-ref (x r) 5) (ty-pair (x y r) 6) (ty-tag (x y e r) 7) (ty-comp (x y e r) 8)
      (ty-markkey (x r) 9) (ty-product (ps) 10) (ty-sum (ps) 11) (ty-array (x r) 12)
      (ty-bloblet (fs z r) 13) (ty-link (x) 14) (ty-icell (x r) 15) (ty-place (r) 16)
      (ty-named (g ds) 17) (ty-nlist (e z r) 18) (ty-nat (z) 19)
      (ty-module (abs ds vs) 20) (ty-select (m n) 21) (ty-param (k n) 22)
      (ty-lam (bs x) 23) (ty-app (f ds) 24))))
;; Whether no instantiation of `pattern` could fit `actual`.
;; Whether a lemma's side `pat` could fit `t`, by their outermost shapes.
(define k-lemma-head? (subr (maxeff kreads spin) (k-binders int int) bool)
  (lambda (bs pat t)
    (let ((p (k-resolve pat)))
      (tagcase (k-get p)
        (ty-var (v) (or (k-binder-has? bs v) (= (k-ty-rank p) (k-ty-rank t))))
        (ty-named (g xs) (tagcase (k-get t) (ty-named (h ys) (= g h)) (else z #f)))
        (else z (= (k-ty-rank p) (k-ty-rank t)))))))
;; Whether lemma `l`'s two sides could fit `a` and `b`, by their outermost
;; shapes.
(define k-lemma-heads? (subr (maxeff kreads spin) (k-lemma int int) bool)
  (lambda (l a b)
    (let ((bs (extract l 1)))
      (and (k-lemma-head? bs (extract l 2) a) (k-lemma-head? bs (extract l 3) b)))))
(define k-lemma-may-apply? (subr (maxeff kreads spin) ((listof k-lemma acyclic) int int) bool)
  (lambda (ls a b)
    (and (not (null? ls))
         (or (k-lemma-heads? (car ls) a b)
             (k-lemma-may-apply? (cdr ls) a b)))))
(define k-pair-seen? (subr kreads (k-pairs int int) bool)
  (lambda (xs a b)
    (and (not (null? xs))
         (or (and (= (car (car xs)) a) (= (cdr (car xs)) b)) (k-pair-seen? (cdr xs) a b)))))
(define k-all-bound? (subr kreads (k-binders k-map) bool)
  (lambda (bs m)
    (or (null? bs)
        (and (not (null? (k-map-find m (extract (car bs) 1)))) (k-all-bound? (cdr bs) m)))))
(define-rec
  (k-subst-memo (subr (maxeff kstate spin) (int k-map (ref k-pairs @t)) int)
    (lambda (t m memo)
      (let* ((t (k-resolve t))
             (kept (and (>= (get k-subst-keep) 0) (= (k-keep-at t) (get k-subst-keep))))
             (done (if kept t (k-memo-find (get memo) t))))
        (if (>= done 0)
            done
            (tagcase (k-get t)
              (ty-base (s) t)
              (ty-void () t)
              (ty-link (x) t)
              (ty-var (v)
                (let ((f (k-map-find m v)))
                  (if (null? f) t (tagcase (cdr (car f)) (dt (x) x) (df (x) x) (else y t)))))
              (ty-select (mod n) (k-select-of mod n t))
              (ty-param (k n) (k-param-sel-of k n t))
              ;; A function applied, given what it is substituted by:
              ;; reduced, if it is a `dlambda` now (`check-kinds.fx`).
              (ty-app (g ds)
                (let ((slot (k-slot)))
                  (begin
                    (set memo (cons (cons t slot) (get memo)))
                    (let* ((g2 (k-subst-memo g m memo)) (ds2 (k-subst-descs ds m memo)))
                      (begin (k-set-link slot (k-applied-type (k-apply-fun g2 ds2) t)) slot)))))
              (else y
                (let ((slot (k-slot)))
                  (begin
                    (set memo (cons (cons t slot) (get memo)))
                    (let ((id (k-ty-new (k-subst-node t m memo))))
                      (begin (k-set-link slot id) slot))))))))))
  ;; Node `t`, of a type other than a variable, with its parts substituted.
  (k-subst-node (subr (maxeff kstate spin) (int k-map (ref k-pairs @t)) k-ty)
    (lambda (t m memo)
      (letrec ((sub (subr (maxeff kstate spin) (int) int)
                    (lambda (x) (k-subst-memo x m memo)))
               (subs (subr (maxeff kstate spin) (k-ids) k-ids)
                     (lambda (xs) (k-subst-list xs m memo)))
               (reg (subr kreads (k-region) k-region)
                    (lambda (r) (k-subst-region r m))))
        (tagcase (k-get t)
          (ty-subr (e ps r cv)
            (let* ((e2 (k-subst-effect e m)) (ps2 (subs ps)) (r2 (sub r)))
              (ty-subr e2 ps2 r2 (k-subst-conv cv m))))
          (ty-poly (bs body) (ty-poly bs (sub body)))
          (ty-ref (a r) (ty-ref (sub a) (reg r)))
          (ty-array (a r) (ty-array (sub a) (reg r)))
          (ty-icell (a r) (ty-icell (sub a) (reg r)))
          (ty-place (r) (ty-place (reg r)))
          (ty-pair (a b r) (let* ((a2 (sub a)) (b2 (sub b))) (ty-pair a2 b2 (reg r))))
          (ty-tag (a h e r)
            (let* ((a2 (sub a)) (h2 (sub h))) (ty-tag a2 h2 (k-subst-effect e m) (reg r))))
          (ty-comp (b a e r)
            (let* ((b2 (sub b)) (a2 (sub a))) (ty-comp b2 a2 (k-subst-effect e m) (reg r))))
          (ty-markkey (a r) (ty-markkey (sub a) (reg r)))
          (ty-product (ps) (ty-product (k-subst-parts ps m memo)))
          (ty-sum (ps) (ty-sum (k-subst-parts ps m memo)))
          (ty-bloblet (fs z r) (ty-bloblet (subs fs) z (reg r)))
          (ty-named (g ds) (ty-named g (k-subst-descs ds m memo)))
          (ty-lam (bs body) (ty-lam bs (car (k-subst-descs (the k-descs (cons body nil)) m memo))))
          (ty-nlist (e z r) (ty-nlist (sub e) (k-subst-size z m) (reg r)))
          (ty-nat (z) (ty-nat (k-subst-size z m)))
          (ty-module (abs ds vs)
            (let* ((ds2 (k-subst-parts ds m memo)) (vs2 (k-subst-parts vs m memo)))
              (ty-module abs ds2 vs2)))
          (else z (k-get t))))))
  (k-subst-descs (subr (maxeff kstate spin) (k-descs k-map (ref k-pairs @t)) k-descs)
    (lambda (ds m memo)
      (if (null? ds)
          nil
          (let* ((d (tagcase (car ds)
                      (dt (x) (dt (k-subst-memo x m memo)))
                      (dr (r) (dr (k-subst-region r m)))
                      (de (e) (de (k-subst-effect e m)))
                      (dz (z) (dz (k-subst-size z m)))
                      (dc (c) (dc (k-subst-conv c m)))
                      (df (x) (df (k-subst-memo x m memo)))))
                 (rest (k-subst-descs (cdr ds) m memo)))
            (cons d rest)))))
  (k-subst-list (subr (maxeff kstate spin) (k-ids k-map (ref k-pairs @t)) k-ids)
    (lambda (ts m memo)
      (if (null? ts)
          nil
          (let* ((x (k-subst-memo (car ts) m memo)) (rest (k-subst-list (cdr ts) m memo)))
            (cons x rest)))))
  (k-subst-parts (subr (maxeff kstate spin) (k-parts k-map (ref k-pairs @t)) k-parts)
    (lambda (ps m memo)
      (if (null? ps)
          nil
          (let* ((x (k-subst-memo (extract (car ps) 2) m memo))
                 (rest (k-subst-parts (cdr ps) m memo)))
            (cons (product (1 (extract (car ps) 1)) (2 x)) rest)))))
    ;; Description `d` substituted into.
    (k-subst-desc (subr (maxeff kstate spin) (k-desc k-map) k-desc)
      (lambda (d m)
        (car (k-subst-descs (the k-descs (cons d nil)) m (the (ref k-pairs @t) (new nil))))))
    ;; Function `f` applied to `ds`: what a `dlambda` reduces to, or an
    ;; application that cannot be reduced. `ds` fit `f`'s kind, which the
    ;; caller has made sure of.
    (k-apply-fun (subr (maxeff kstate spin) (int k-descs) k-desc)
      (lambda (f ds)
        (tagcase (k-get f)
          (ty-lam (bs body)
            (if (= (k-length bs) (k-length ds))
                (k-subst-desc body (k-gen-map bs ds))
                (k-apply-stuck f ds)))
          (else y (k-apply-stuck f ds))))))

;; `t` with each binder in `m` replaced. Recursive types are copied as
;; cycles: each node gets its slot before its children are built.
;; A substitution of its own (a `dlambda` reduced inside another) keeps
;; nothing of another's.
(define k-subst (subr (maxeff kstate spin) (int k-map) int)
  (lambda (t m)
    (let* ((keep (get k-subst-keep))
           (off (set k-subst-keep -1))
           (r (k-subst-memo t m (the (ref k-pairs @t) (new nil)))))
      (begin (set k-subst-keep keep) r))))
(define k-subst-hyps (subr (maxeff kstate spin) (k-hyps k-map) k-hyps)
  (lambda (hs m)
    (if (null? hs)
        nil
        (let* ((x (k-subst (car (car hs)) m)) (y (k-subst (cdr (car hs)) m)))
          (the k-hyps (cons (cons x y) (k-subst-hyps (cdr hs) m)))))))
;; The `g`th generative type's representation, for `ds`.
(define k-unfold (subr (maxeff kstate spin) (int k-descs) int)
  (lambda (g ds)
    (let ((gen (k-gen-of g))) (k-subst (extract gen 4) (k-gen-map (extract gen 2) ds)))))

;; The description of kind `k` that names binder `v`.
(define k-binder-desc (subr (maxeff kstate spin) (int int) k-desc)
  (lambda (k v)
    (cond ((or (= k 0) (= k 3)) (dr (r-var v)))
          ((= k 1) (de (k-one (a-var v))))
          ((= k 5) (dz (k-size-var v)))
          ((= k 6) (dc (cv-var v)))
          ((>= k 100) (df (k-ty-new (ty-var v))))
          (else (dt (k-ty-new (ty-var v)))))))
;; `b`'s binders renamed to `a`'s, for comparing under them.
(define k-rename (subr (maxeff kstate spin) (k-binders k-binders) k-map)
  (lambda (bs as)
    (if (null? bs)
        nil
        (let* ((vb (extract (car bs) 1)) (k (extract (car bs) 2)) (va (extract (car as) 1))
               (d (k-binder-desc k va))
               (rest (k-rename (cdr bs) (cdr as))))
          (cons (cons vb d) rest)))))
(define k-same-kinds? (subr kreads (k-binders k-binders) bool)
  (lambda (xs ys)
    (cond ((null? xs) (null? ys))
          ((null? ys) #f)
          (else (and (= (extract (car xs) 2) (extract (car ys) 2))
                     (k-same-kinds? (cdr xs) (cdr ys)))))))))

(define-type k-typed-params (select check-resolve-module k-typed-params))
(define-type k-letrec-bs (select check-resolve-module k-letrec-bs))
(define-type k-let-bs (select check-resolve-module k-let-bs))
(define-type k-arms (select check-resolve-module k-arms))
(define-type exp-params (select check-resolve-module exp-params))
(define-type exp-letrec-bs (select check-resolve-module exp-letrec-bs))
(define-type exp-let-bs (select check-resolve-module exp-let-bs))
(define-type exp-arms (select check-resolve-module exp-arms))
(define-effect kmakes (select check-resolve-module kmakes))
(define k-start (with check-resolve-module k-start))
(define k-end (with check-resolve-module k-end))
(define k-copy-names (with check-resolve-module k-copy-names))
(define exp-start (with check-resolve-module exp-start))
(define exp-end (with check-resolve-module exp-end))
(define k-resolve-module (with check-resolve-module k-resolve-module))
(define k-resolve-all (with check-resolve-module k-resolve-all))
(define k-resolve-exp (with check-resolve-module k-resolve-exp))
(define-type k-callable (select check-resolve-module k-callable))
(define k-as-subr (with check-resolve-module k-as-subr))
(define k-vsubr-parts (with check-resolve-module k-vsubr-parts))
(define k-callee-of (with check-resolve-module k-callee-of))
(define k-has-region-in? (with check-resolve-module k-has-region-in?))
(define k-add-region (with check-resolve-module k-add-region))
(define-type k-def (select check-resolve-module k-def))
(define k-defs (with check-resolve-module k-defs))
(define k-last-uses (with check-resolve-module k-last-uses))
(define-type k-run (select check-resolve-module k-run))
(define k-runs (with check-resolve-module k-runs))
(define k-reset (with check-resolve-module k-reset))
(define k-regions-in (with check-resolve-module k-regions-in))
(define k-names-onto (with check-resolve-module k-names-onto))
(define k-param-names (with check-resolve-module k-param-names))
(define k-letrec-names (with check-resolve-module k-letrec-names))
(define k-let-names (with check-resolve-module k-let-names))
(define k-conversion-name (with check-resolve-module k-conversion-name))
(define k-items-bound (with check-resolve-module k-items-bound))
(define k-free-into (with check-resolve-module k-free-into))
(define k-free-vars (with check-resolve-module k-free-vars))
(define k-subst-region (with check-resolve-module k-subst-region))
(define k-memo-find (with check-resolve-module k-memo-find))
(define k-ty-rank (with check-resolve-module k-ty-rank))
(define k-lemma-may-apply? (with check-resolve-module k-lemma-may-apply?))
(define k-pair-seen? (with check-resolve-module k-pair-seen?))
(define k-all-bound? (with check-resolve-module k-all-bound?))
(define k-subst-memo (with check-resolve-module k-subst-memo))
(define k-apply-fun (with check-resolve-module k-apply-fun))
(define k-subst (with check-resolve-module k-subst))
(define k-subst-hyps (with check-resolve-module k-subst-hyps))
(define k-unfold (with check-resolve-module k-unfold))
(define k-binder-desc (with check-resolve-module k-binder-desc))
(define k-rename (with check-resolve-module k-rename))
(define k-same-kinds? (with check-resolve-module k-same-kinds?))
