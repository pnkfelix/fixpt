;;; The checker, in FX-26: resolving the trees' descriptions, callables,
;;; regions of types, masking and substitution.
;;; Part of the checker, `check-types.fx` first (PLAN.md §11, step 10).

;;; ------------------------------------------------------------ resolving
;;; The parser's trees to `kx`, reading descriptions where the Rust parser
;;; does.

(define k-start (subr pure (kx) int)
  (lambda (x)
    (tagcase x
      (x-var (s a b) a) (x-const (t v a b) a) (x-lambda (ps e a b) a) (x-app (f xs a b) a)
      (x-plambda (bs e a b) a) (x-proj (e ds a b) a) (x-if (p c d a b) a) (x-letrec (bs e a b) a)
      (x-let (bs e a b) a) (x-begin (xs a b) a) (x-prompt (t e h a b) a) (x-the (t e a b) a) (x-convention (c e a b) a)
      (x-bloblet (o i xs a b) a) (x-product (fs a b) a) (x-extract (e l a b) a) (x-sum (l e a b) a)
      (x-tagcase (e arms els a b) a) (x-letregion (k r i e a b) a) (x-rlambda (r l a b) a))))
(define k-end (subr pure (kx) int)
  (lambda (x)
    (tagcase x
      (x-var (s a b) b) (x-const (t v a b) b) (x-lambda (ps e a b) b) (x-app (f xs a b) b)
      (x-plambda (bs e a b) b) (x-proj (e ds a b) b) (x-if (p c d a b) b) (x-letrec (bs e a b) b)
      (x-let (bs e a b) b) (x-begin (xs a b) b) (x-prompt (t e h a b) b) (x-the (t e a b) b) (x-convention (c e a b) b)
      (x-bloblet (o i xs a b) b) (x-product (fs a b) b) (x-extract (e l a b) b) (x-sum (l e a b) b)
      (x-tagcase (e arms els a b) b) (x-letregion (k r i e a b) b) (x-rlambda (r l a b) b))))
(define k-same-span? (subr (read @globals) (kx int int) bool)
  (lambda (x a b) (and (= (k-start x) a) (= (k-end x) b))))

(define k-resolve-params (subr (maxeff checks spin) ((listof (productof (1 symbol) (2 syns-a)) acyclic)) (listof (productof (1 symbol) (2 k-ids)) acyclic))
  (lambda (ps)
    (if (null? ps)
        nil
        (let* ((ty (extract (car ps) 2))
               (t (if (null? ty) (the k-ids nil) (the k-ids (cons (k-parse-type (car ty)) nil))))
               (rest (k-resolve-params (cdr ps))))
          (cons (product (1 (extract (car ps) 1)) (2 t)) rest)))))
(define k-resolve-descs (subr (maxeff checks spin) (syns-a) (listof k-desc acyclic))
  (lambda (ds) (if (null? ds) nil (let* ((d (k-parse-d (car ds))) (rest (k-resolve-descs (cdr ds)))) (cons d rest)))))
(define k-copy-names (subr (maxeff (read @globals) (alloc @t)) (names) k-names)
  (lambda (ns) (if (null? ns) nil (cons (car ns) (k-copy-names (cdr ns))))))

;; Where a parser's tree starts and ends.
(define exp-start (subr pure (exp) int)
  (lambda (e)
    (tagcase e
      (e-var (s a b) a) (e-int (n a b) a) (e-bool (v a b) a) (e-str (v a b) a) (e-char (v a b) a) (e-sym (v a b) a)
      (e-unit (a b) a) (e-lambda (ps x a b) a) (e-app (f xs a b) a) (e-plambda (bs x a b) a) (e-proj (x ds a b) a)
      (e-if (p c d a b) a) (e-letrec (bs x a b) a) (e-let (bs x a b) a) (e-begin (xs a b) a) (e-prompt (t x h a b) a)
      (e-the (t x a b) a) (e-convention (c x a b) a) (e-bloblet (o i xs a b) a) (e-product (fs a b) a) (e-extract (x l a b) a) (e-sum (l x a b) a)
      (e-tagcase (x arms els a b) a) (e-letregion (k r i x a b) a) (e-rlambda (r l a b) a))))
(define exp-end (subr pure (exp) int)
  (lambda (e)
    (tagcase e
      (e-var (s a b) b) (e-int (n a b) b) (e-bool (v a b) b) (e-str (v a b) b) (e-char (v a b) b) (e-sym (v a b) b)
      (e-unit (a b) b) (e-lambda (ps x a b) b) (e-app (f xs a b) b) (e-plambda (bs x a b) b) (e-proj (x ds a b) b)
      (e-if (p c d a b) b) (e-letrec (bs x a b) b) (e-let (bs x a b) b) (e-begin (xs a b) b) (e-prompt (t x h a b) b)
      (e-the (t x a b) b) (e-convention (c x a b) b) (e-bloblet (o i xs a b) b) (e-product (fs a b) b) (e-extract (x l a b) b) (e-sum (l x a b) b)
      (e-tagcase (x arms els a b) b) (e-letregion (k r i x a b) b) (e-rlambda (r l a b) b))))

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

(define-rec
  (k-resolve-all (subr (maxeff checks spin) ((listof exp acyclic)) kxs)
    (lambda (es) (if (null? es) nil (let* ((x (k-resolve-exp (car es))) (rest (k-resolve-all (cdr es)))) (cons x rest)))))
  (k-resolve-exp (subr (maxeff checks spin) (exp) kx)
    (lambda (e)
      (tagcase e
        (e-var (s a b) (x-var s a b))
        (e-int (n a b) (x-const k-int n a b))
        (e-bool (v a b) (x-const k-bool (if v 1 0) a b))
        (e-str (v a b) (x-const k-string 0 a b))
        (e-char (v a b) (x-const k-char 0 a b))
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
                            (k-set-outer v (if (= k 3)
                                               (tagcase place (r-var (p) (cons p (k-outer-of p))) (else y nil))
                                               lives))
                            (set k-lifetimes (cons v lives))))
                 (pushed (k-push-desc name (ds-var v kind)))
                 (x (k-resolve-exp body)))
            (begin (set k-dscope saved) (set k-lifetimes lives)
                   (x-letregion k v (tagcase place (r-var (p) (r-frozen p #f)) (else y (r-frozen -1 #f))) x a b))))
        (e-proj (body ds a b)
          (let* ((x (k-resolve-exp body)) (descs (k-resolve-descs ds))) (x-proj x descs a b)))
        (e-if (p c d a b)
          (let* ((px (k-resolve-exp p)) (cx (k-resolve-exp c)) (dx (k-resolve-exp d))) (x-if px cx dx a b)))
        (e-letrec (bs body a b)
          (let* ((rbs (k-resolve-letrec bs)) (x (k-resolve-exp body))) (x-letrec rbs x a b)))
        (e-let (bs body a b)
          (let* ((rbs (k-resolve-let bs)) (x (k-resolve-exp body))) (x-let rbs x a b)))
        (e-begin (es a b) (x-begin (k-resolve-all es) a b))
        (e-prompt (t body h a b)
          (let* ((tx (k-resolve-exp t)) (bx (k-resolve-exp body)) (hx (k-resolve-exp h))) (x-prompt tx bx hx a b)))
        (e-the (ty body a b)
          (let* ((t (k-parse-type ty)) (x (k-resolve-exp body))) (x-the t x a b)))
        (e-convention (c body a b)
          (let* ((cv (k-parse-conv c)) (x (k-resolve-exp body))) (x-convention cv x a b)))
        (e-bloblet (op i args a b) (x-bloblet op i (k-resolve-all args) a b))
        (e-product (fs a b) (x-product (k-resolve-fields fs nil a b) a b))
        (e-extract (body l a b) (x-extract (k-resolve-exp body) l a b))
        (e-sum (l body a b) (x-sum l (k-resolve-exp body) a b))
        (e-tagcase (s arms els a b)
          (let* ((sx (k-resolve-exp s)) (rarms (k-resolve-arms arms nil)) (rels (k-resolve-else els)))
            (x-tagcase sx rarms rels a b))))))
  (k-resolve-letrec (subr (maxeff checks spin) ((listof (productof (1 symbol) (2 syn) (3 exp)) acyclic)) (listof (productof (1 symbol) (2 int) (3 kx)) acyclic))
    (lambda (bs)
      (if (null? bs)
          nil
          (let* ((t (k-parse-type (extract (car bs) 2)))
                 (x (k-resolve-exp (extract (car bs) 3)))
                 (rest (k-resolve-letrec (cdr bs))))
            (cons (product (1 (extract (car bs) 1)) (2 t) (3 x)) rest)))))
  (k-resolve-let (subr (maxeff checks spin) ((listof (productof (1 symbol) (2 exp)) acyclic)) (listof (productof (1 symbol) (2 kx)) acyclic))
    (lambda (bs)
      (if (null? bs)
          nil
          (let* ((x (k-resolve-exp (extract (car bs) 2))) (rest (k-resolve-let (cdr bs))))
            (cons (product (1 (extract (car bs) 1)) (2 x)) rest)))))
  (k-resolve-fields (subr (maxeff checks spin) ((listof (productof (1 symbol) (2 exp)) acyclic) k-names int int) (listof (productof (1 symbol) (2 kx)) acyclic))
    (lambda (fs seen a b)
      (if (null? fs)
          nil
          (let ((l (extract (car fs) 1)))
            (if (k-has-name? seen l)
                (k-fail (string-append (k-quote (symbol->string l)) " appears twice") a b)
                (let* ((x (k-resolve-exp (extract (car fs) 2))) (rest (k-resolve-fields (cdr fs) (cons l seen) a b)))
                  (cons (product (1 l) (2 x)) rest)))))))
  (k-resolve-arms (subr (maxeff checks spin) ((listof (productof (1 symbol) (2 bool) (3 names) (4 exp)) acyclic) k-names)
                          (listof (productof (1 symbol) (2 bool) (3 k-names) (4 kx)) acyclic))
    (lambda (arms seen)
      (if (null? arms)
          nil
          (let* ((arm (car arms)) (tag (extract arm 1)))
            (if (k-has-name? seen tag)
                (k-fail (string-append (k-quote (symbol->string tag)) " has two arms")
                        (exp-start (extract arm 4)) (exp-end (extract arm 4)))
                (let* ((x (k-resolve-exp (extract arm 4))) (rest (k-resolve-arms (cdr arms) (cons tag seen))))
                  (cons (product (1 tag) (2 (extract arm 2)) (3 (k-copy-names (extract arm 3))) (4 x)) rest)))))))
  (k-resolve-else (subr (maxeff checks spin) ((listof (productof (1 symbol) (2 exp)) acyclic)) (listof (productof (1 symbol) (2 kx)) acyclic))
    (lambda (els)
      (if (null? els) nil (cons (product (1 (extract (car els) 1)) (2 (k-resolve-exp (extract (car els) 2)))) nil)))))

;;; ------------------------------------------------------------ callables

;; What calling a value of type `t` does: its latent effect, parameters and
;; result, as none or one. A composable continuation runs the rest of its
;; prompt's body, with control effects on the tag's region.
(define-type k-callable (productof (1 k-eff) (2 k-ids) (3 int)))
(define k-as-subr (subr (maxeff (read @globals) (read @t) (alloc @t) spin) (int) (listof k-callable acyclic))
  (lambda (t)
    (tagcase (k-get t)
      (ty-subr (e ps r cv) (cons (product (1 e) (2 ps) (3 r)) nil))
      (ty-comp (arg answer e r)
        (cons (product (1 (k-insert (a-goto r) (k-insert (a-comefrom r) e))) (2 (the k-ids (cons arg nil))) (3 answer)) nil))
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
(define k-vsubr-parts (subr (maxeff (read @globals) (read @t) (alloc @t) spin) (int) k-vsub)
  (lambda (t)
    (tagcase (k-get t)
      (ty-named (g ds)
        (if (and (= g 0) (= (k-length ds) 3))
            (k-vsubr-descs (car ds) (car (cdr ds)) (car (cdr (cdr ds))))
            k-vsub-none))
      (else y k-vsub-none))))

;;; ------------------------------------------------------------ regions of types

(define-type k-regions (listof k-region acyclic))
(define k-has-region-in? (subr (maxeff (read @globals) (read @t) spin) (k-regions k-region) bool)
  (lambda (rs r) (cond ((null? rs) #f) ((k-region=? (car rs) r) #t) (else (k-has-region-in? (cdr rs) r)))))
(define k-add-region (subr (maxeff (read @globals) (read @t) (alloc @t) spin) (k-regions k-region) k-regions)
  (lambda (rs r) (if (k-has-region-in? rs r) rs (cons r rs))))
;; `out` and each of `rs` that is not a generative type's parameter.
(define k-add-non-gen (subr (maxeff (read @globals) (read @t) (alloc @t) spin) (k-regions k-regions) k-regions)
  (lambda (out rs)
    (cond ((null? rs) out)
          ((k-gen-region? (car rs)) (k-add-non-gen out (cdr rs)))
          (else (k-add-non-gen (k-add-region out (car rs)) (cdr rs))))))
(define k-add-eff-regions (subr (maxeff (read @globals) (read @t) (alloc @t) spin) (k-regions k-eff) k-regions)
  (lambda (rs e)
    (cond ((null? e) rs)
          ((k-has-region? (car e)) (k-add-eff-regions (k-add-region rs (k-atom-region (car e))) (cdr e)))
          (else (k-add-eff-regions rs (cdr e))))))

;; Every region mentioned in type `t`, following recursive types once.
;; Kept once found, by type: a type does not change once built.
(define k-regions-memo (ref (arrayof (listof k-regions acyclic) @t) @t) (new (make-array 512 nil)))

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
(define k-reset (subr (maxeff kstate spin) () unit)
  (lambda ()
    (begin
      (set k-extracts nil) (set k-effect-notes nil)
      (set k-ntys 0) (set k-dvars nil) (set k-ndvars 0) (set k-places nil) (set k-bounds nil) (set k-outers nil) (set k-lifetimes nil) (set k-freezing nil) (set k-written nil) (set k-known (make-table symbol-hash symbol=?)) (set k-global (make-table symbol-hash symbol=?)) (set k-recursive nil) (set k-std nil) (set k-env (make-table symbol-hash symbol=?)) (set k-trail nil) (set k-depth 0)
      (set k-regions-memo (make-array 512 nil)) (set k-dscope nil)
      (set k-fresh 0) (set k-base nil) (set k-expanding 0) (set k-knots nil) (set k-spin-why nil)
      (set k-gens nil) (set k-ngens 0) (set k-transparent nil) (set k-inside nil) (set k-conversions nil)
      (set k-lemmas nil) (set k-pending-lemma nil) (set k-datas nil) (set k-certified nil) (set k-certified-lengths nil) (set k-certified-nats nil) (set k-size-facts nil) (set k-skolems nil)
      (set k-broken nil) (set k-defs nil) (set k-runs nil) (set k-last-uses nil)
      (k-basic "int") (k-basic "bool") (k-basic "string") (k-basic "unit") (k-basic "char")
      (k-basic "datum") (k-basic "symbol") (k-basic "tword") (k-basic "wcell") (k-basic "wglobal")
      (k-basic "i32") (k-basic "u32") (k-basic "i64") (k-basic "u64")  ; 10 to 13; `void` 14, `k-void`
      (k-ty-new (ty-void))
      #u)))
(define n-copy-memo (subr (maxeff (read @globals) (read @t) (write @t) spin) ((arrayof (listof k-regions acyclic) @t) (arrayof (listof k-regions acyclic) @t) int) unit)
  (lambda (from to i)
    (if (= i (array-length from)) #u (begin (array-set! to i (array-ref from i)) (n-copy-memo from to (+ i 1))))))
(define k-remember-regions (subr (maxeff (read @globals) (read @t) (write @t) (alloc @t) spin) (int k-regions) unit)
  (lambda (t rs)
    (begin
      (if (>= t (array-length (get k-regions-memo)))
          (let ((bigger (the (arrayof (listof k-regions acyclic) @t) (make-array (* 2 (array-length (get k-tys))) nil))))
            (begin (n-copy-memo (get k-regions-memo) bigger 0) (set k-regions-memo bigger)))
          #u)
      (array-set! (get k-regions-memo) t (cons rs nil)))))

(define-rec
  (k-regions-walk (subr (maxeff (read @globals) (read @t) (write @t) (alloc @t) spin) (int int (ref k-regions @t)) unit)
    (lambda (t seen out)
      (let ((t (k-resolve t)))
        (if (k-visit? t seen)
            #u
            (letrec ((add (subr (maxeff (read @globals) (read @t) (write @t) (alloc @t) spin) (k-region) unit)
                         (lambda (r) (set out (k-add-region (get out) r))))
                  (walk (subr (maxeff (read @globals) (read @t) (write @t) (alloc @t) spin) (int) unit) (lambda (x) (k-regions-walk x seen out)))
                  (walks (subr (maxeff (read @globals) (read @t) (write @t) (alloc @t) spin) (k-ids) unit) (lambda (xs) (k-regions-walks xs seen out))))
              (begin
                (tagcase (k-get t)
                  (ty-subr (e ps r cv) (begin (set out (k-add-eff-regions (get out) e)) (walks ps) (walk r)))
                  (ty-poly (bs body) (walk body))
                  (ty-ref (a r) (begin (add r) (walk a)))
                  (ty-array (a r) (begin (add r) (walk a)))
                  (ty-icell (a r) (begin (add r) (walk a)))
                  (ty-place (r) (add r))
                  (ty-pair (a b r) (begin (add r) (walk a) (walk b)))
                  (ty-tag (a h e r) (begin (add r) (set out (k-add-eff-regions (get out) e)) (walk a) (walk h)))
                  (ty-comp (b a e r) (begin (add r) (set out (k-add-eff-regions (get out) e)) (walk a) (walk b)))
                  (ty-markkey (a r) (begin (add r) (walk a)))
                  (ty-bloblet (fs z r) (begin (add r) (walks fs)))
                  (ty-product (ps) (k-regions-parts ps seen out))
                  (ty-sum (ps) (k-regions-parts ps seen out))
                  (ty-nlist (e z r) (begin (add r) (walk e)))
                  ;; Transparent to safety: what its representation holds,
                  ;; its parameters' regions standing for what it was given.
                  (ty-named (g ds)
                    (let ((inner (the (ref k-regions @t) (new nil))))
                      (begin (k-regions-walk (extract (k-gen-of g) 4) seen inner)
                             (set out (k-add-non-gen (get out) (get inner)))
                             (k-regions-descs ds seen out))))
                  (else x #u))))))))
  (k-regions-descs (subr (maxeff (read @globals) (read @t) (write @t) (alloc @t) spin) ((listof k-desc acyclic) int (ref k-regions @t)) unit)
    (lambda (ds seen out)
      (if (null? ds)
          #u
          (begin (tagcase (car ds)
                   (dt (x) (k-regions-walk x seen out))
                   (dr (r) (set out (k-add-region (get out) r)))
                   (de (e) (set out (k-add-eff-regions (get out) e)))
                   (dz (z) #u)
                   (dc (c) #u))
                 (k-regions-descs (cdr ds) seen out)))))
  (k-regions-walks (subr (maxeff (read @globals) (read @t) (write @t) (alloc @t) spin) (k-ids int (ref k-regions @t)) unit)
    (lambda (ts seen out) (if (null? ts) #u (begin (k-regions-walk (car ts) seen out) (k-regions-walks (cdr ts) seen out)))))
  (k-regions-parts (subr (maxeff (read @globals) (read @t) (write @t) (alloc @t) spin) (k-parts int (ref k-regions @t)) unit)
    (lambda (ps seen out)
      (if (null? ps) #u (begin (k-regions-walk (extract (car ps) 2) seen out) (k-regions-parts (cdr ps) seen out))))))
(define k-frozen-places (subr (maxeff (read @globals) (read @t) (alloc @t) spin) (k-regions k-regions) k-regions)
  (lambda (rs out)
    (if (null? rs)
        out
        (k-frozen-places (cdr rs)
                         (tagcase (car rs) (r-frozen (p f) (if (< p 0) out (k-add-region out (r-var p)))) (else y out))))))
(define k-regions-in (subr (maxeff (read @globals) (read @t) (write @t) (alloc @t) spin) (int) k-regions)
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
(define k-note (subr (maxeff (read @globals) (read @t) (alloc @t)) (symbol k-names k-names) k-names)
  (lambda (s bound out) (if (or (k-has-name? bound s) (k-has-name? out s)) out (cons s out))))
(define k-names-onto (subr (maxeff (read @globals) (read @t) (alloc @t)) (k-names k-names) k-names)
  (lambda (ns bound) (if (null? ns) bound (k-names-onto (cdr ns) (cons (car ns) bound)))))
(define k-param-names (subr (maxeff (read @globals) (read @t) (alloc @t)) ((listof (productof (1 symbol) (2 k-ids)) acyclic) k-names) k-names)
  (lambda (ps bound) (if (null? ps) bound (k-param-names (cdr ps) (cons (extract (car ps) 1) bound)))))
(define k-letrec-names (subr (maxeff (read @globals) (read @t) (alloc @t)) ((listof (productof (1 symbol) (2 int) (3 kx)) acyclic) k-names) k-names)
  (lambda (bs bound) (if (null? bs) bound (k-letrec-names (cdr bs) (cons (extract (car bs) 1) bound)))))
(define k-let-names (subr (maxeff (read @globals) (read @t) (alloc @t)) ((listof (productof (1 symbol) (2 kx)) acyclic) k-names) k-names)
  (lambda (bs bound) (if (null? bs) bound (k-let-names (cdr bs) (cons (extract (car bs) 1) bound)))))

(define-rec
  (k-free-list (subr (maxeff (read @globals) (read @t) (alloc @t)) (kxs k-names k-names) k-names)
    (lambda (xs bound out) (if (null? xs) out (k-free-list (cdr xs) bound (k-free-into (car xs) bound out)))))
  (k-free-into (subr (maxeff (read @globals) (read @t) (alloc @t)) (kx k-names k-names) k-names)
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
        (x-prompt (t body h a b) (k-free-into h bound (k-free-into body bound (k-free-into t bound out))))
        (x-the (t body a b) (k-free-into body bound out))
        (x-convention (c body a b) (k-free-into body bound out))
        (x-bloblet (o i xs a b) (k-free-list xs bound out))
        (x-product (fs a b) (k-free-fields fs bound out))
        (x-extract (body l a b) (k-free-into body bound out))
        (x-sum (l body a b) (k-free-into body bound out))
        (x-tagcase (s arms els a b)
          (let ((o (k-free-arms arms bound (k-free-into s bound out))))
            (if (null? els) o (k-free-into (extract (car els) 2) (cons (extract (car els) 1) bound) o)))))))
  (k-free-letrec (subr (maxeff (read @globals) (read @t) (alloc @t)) ((listof (productof (1 symbol) (2 int) (3 kx)) acyclic) k-names k-names) k-names)
    (lambda (bs bound out) (if (null? bs) out (k-free-letrec (cdr bs) bound (k-free-into (extract (car bs) 3) bound out)))))
  (k-free-let (subr (maxeff (read @globals) (read @t) (alloc @t)) ((listof (productof (1 symbol) (2 kx)) acyclic) k-names k-names) k-names)
    (lambda (bs bound out) (if (null? bs) out (k-free-let (cdr bs) bound (k-free-into (extract (car bs) 2) bound out)))))
  (k-free-fields (subr (maxeff (read @globals) (read @t) (alloc @t)) ((listof (productof (1 symbol) (2 kx)) acyclic) k-names k-names) k-names)
    (lambda (fs bound out) (if (null? fs) out (k-free-fields (cdr fs) bound (k-free-into (extract (car fs) 2) bound out)))))
  (k-free-arms (subr (maxeff (read @globals) (read @t) (alloc @t))
                        ((listof (productof (1 symbol) (2 bool) (3 k-names) (4 kx)) acyclic) k-names k-names) k-names)
    (lambda (arms bound out)
      (if (null? arms)
          out
          (k-free-arms (cdr arms) bound
                       (k-free-into (extract (car arms) 4) (k-names-onto (extract (car arms) 3) bound) out))))))

;;; ------------------------------------------------------------ free variables

(define k-free-vars (subr (maxeff (read @globals) (read @t) (alloc @t)) (kx) k-names)
  (lambda (x) (k-free-into x nil nil)))

;;; ------------------------------------------------------------ masking
;;; What cannot be observed outside `x`, whose type is `result`, is removed:
;;; everything on a region that no free variable's type mentions, except
;;; that `alloc`, `goto` and `comefrom` on a region the result mentions stay
;;; (ranks 2 to 4; `await`, like `read`, does not).

;; Whether an atom is on `const`, the frozen region.
(define k-frozen-atom? (subr (read @globals) (k-atom) bool)
  (lambda (a) (and (k-has-region? a) (tagcase (k-atom-region a) (r-frozen (p f) #t) (else y #f)))))
;; Whether an atom is on data frozen into a place, other than a write: it is
;; masked as what is done to the place is
;; (`docs/research/soundness-findings.md`, F2).
(define k-place-frozen-atom? (subr (read @globals) (k-atom) bool)
  (lambda (a)
    (and (k-has-region? a) (not (= (k-atom-rank a) 1))
         (tagcase (k-atom-region a) (r-frozen (p f) (>= p 0)) (else y #f)))))
;; The region an atom is masked by: a place-frozen atom's place.
(define k-mask-region (subr (read @globals) (k-atom) k-region)
  (lambda (a)
    (if (k-place-frozen-atom? a)
        (tagcase (k-atom-region a) (r-frozen (p f) (r-var p)) (else y (k-atom-region a)))
        (k-atom-region a))))
;; Whether an atom stays because the result mentions its region: `alloc`,
;; `goto` and `comefrom` (ranks 2 to 4); only `alloc`, for a place-frozen
;; one.
(define k-result-keeps? (subr (read @globals) (k-atom) bool)
  (lambda (a) (if (k-place-frozen-atom? a) (= (k-atom-rank a) 2) (and (> (k-atom-rank a) 1) (< (k-atom-rank a) 5)))))
;; The regions of `e`'s atoms that stay only if a free variable sees them.
(define k-sought (subr (maxeff (read @globals) (read @t) (alloc @t) spin) (k-eff k-regions k-regions) k-regions)
  (lambda (e in-result out)
    (if (null? e)
        out
        (let ((a (car e)))
          (k-sought (cdr e) in-result
                    (if (and (k-has-region? a) (and (not (k-globals-atom? a)) (or (not (k-frozen-atom? a)) (k-place-frozen-atom? a)))
                             (not (and (k-has-region-in? in-result (k-mask-region a)) (k-result-keeps? a))))
                        (k-add-region out (k-mask-region a))
                        out))))))
(define k-drop-regions (subr (maxeff (read @globals) (read @t) (alloc @t) spin) (k-regions k-regions) k-regions)
  (lambda (rs seen)
    (cond ((null? rs) nil)
          ((k-has-region-in? seen (car rs)) (k-drop-regions (cdr rs) seen))
          (else (cons (car rs) (k-drop-regions (cdr rs) seen))))))

;; Of the regions `rs`, those no variable free in `x` sees: a walk of `x`
;; as `k-free-into`'s, that stops once each has been seen, as most are.
(define-rec
  (k-unseen-list (subr (maxeff (read @globals) (read @t) (write @t) (alloc @t) spin) (kxs k-names k-regions) k-regions)
    (lambda (xs bound rs) (if (or (null? xs) (null? rs)) rs (k-unseen-list (cdr xs) bound (k-unseen (car xs) bound rs)))))
  (k-unseen (subr (maxeff (read @globals) (read @t) (write @t) (alloc @t) spin) (kx k-names k-regions) k-regions)
    (lambda (x bound rs)
      (if (null? rs)
          rs
          (tagcase x
            (x-var (s a b)
              (let ((t (if (k-has-name? bound s) -1 (k-lookup s))))
                (if (< t 0) rs (k-drop-regions rs (k-regions-in t)))))
            (x-const (t v a b) rs)
            (x-lambda (ps body a b) (k-unseen body (k-param-names ps bound) rs))
            (x-app (f args a b) (k-unseen-list args bound (k-unseen f bound rs)))
            (x-plambda (bs body a b) (k-unseen body bound rs))
            (x-letregion (k r i body a b) (k-unseen body (cons (k-dvar-name r) bound) rs))
            (x-rlambda (r l a b) (k-unseen l bound (k-unseen r bound rs)))
            (x-proj (body ds a b) (k-unseen body bound rs))
            (x-if (p c d a b) (k-unseen d bound (k-unseen c bound (k-unseen p bound rs))))
            (x-letrec (bs body a b)
              (let ((inner (k-letrec-names bs bound)))
                (k-unseen body inner (k-unseen-letrec bs inner rs))))
            (x-let (bs body a b) (k-unseen body (k-let-names bs bound) (k-unseen-let bs bound rs)))
            (x-begin (xs a b) (k-unseen-list xs bound rs))
            (x-prompt (t body h a b) (k-unseen h bound (k-unseen body bound (k-unseen t bound rs))))
            (x-the (t body a b) (k-unseen body bound rs))
            (x-convention (c body a b) (k-unseen body bound rs))
            (x-bloblet (o i xs a b) (k-unseen-list xs bound rs))
            (x-product (fs a b) (k-unseen-fields fs bound rs))
            (x-extract (body l a b) (k-unseen body bound rs))
            (x-sum (l body a b) (k-unseen body bound rs))
            (x-tagcase (s arms els a b)
              (let ((o (k-unseen-arms arms bound (k-unseen s bound rs))))
                (if (null? els) o (k-unseen (extract (car els) 2) (cons (extract (car els) 1) bound) o))))))))
  (k-unseen-letrec (subr (maxeff (read @globals) (read @t) (write @t) (alloc @t) spin) ((listof (productof (1 symbol) (2 int) (3 kx)) acyclic) k-names k-regions) k-regions)
    (lambda (bs bound rs) (if (null? bs) rs (k-unseen-letrec (cdr bs) bound (k-unseen (extract (car bs) 3) bound rs)))))
  (k-unseen-let (subr (maxeff (read @globals) (read @t) (write @t) (alloc @t) spin) ((listof (productof (1 symbol) (2 kx)) acyclic) k-names k-regions) k-regions)
    (lambda (bs bound rs) (if (null? bs) rs (k-unseen-let (cdr bs) bound (k-unseen (extract (car bs) 2) bound rs)))))
  (k-unseen-fields (subr (maxeff (read @globals) (read @t) (write @t) (alloc @t) spin) ((listof (productof (1 symbol) (2 kx)) acyclic) k-names k-regions) k-regions)
    (lambda (fs bound rs) (if (null? fs) rs (k-unseen-fields (cdr fs) bound (k-unseen (extract (car fs) 2) bound rs)))))
  (k-unseen-arms (subr (maxeff (read @globals) (read @t) (write @t) (alloc @t) spin)
                        ((listof (productof (1 symbol) (2 bool) (3 k-names) (4 kx)) acyclic) k-names k-regions) k-regions)
    (lambda (arms bound rs)
      (if (null? arms)
          rs
          (k-unseen-arms (cdr arms) bound
                         (k-unseen (extract (car arms) 4) (k-names-onto (extract (car arms) 3) bound) rs))))))

;; What stays of `e`: an atom on a region no free variable sees goes.
(define k-keep (subr (maxeff (read @globals) (read @t) (alloc @t) spin) (k-eff k-regions k-regions) k-eff)
  (lambda (e unseen in-result)
    (if (null? e)
        nil
        (let* ((a (car e)) (rest (k-keep (cdr e) unseen in-result)))
          (cond ((not (k-has-region? a)) (cons a rest))
                ((and (k-frozen-atom? a) (not (k-place-frozen-atom? a))) (cons a rest))
                ((not (k-has-region-in? unseen (k-mask-region a))) (cons a rest))
                ((and (k-has-region-in? in-result (k-mask-region a)) (k-result-keeps? a)) (cons a rest))
                (else rest))))))

;; A write to a region a `letfreeze` is freezing, noted before masking could
;; hide it: that region's data may be cyclic.
(define k-note-writes (subr kstate (k-eff) unit)
  (lambda (e)
    (if (null? e)
        #u
        (begin
          (tagcase (car e)
            (a-write (r)
              (tagcase r
                (r-var (v) (if (and (k-has-id? (get k-freezing) v) (not (k-has-id? (get k-written) v)))
                               (set k-written (cons v (get k-written)))
                               #u))
                (else y #u)))
            (else x #u))
          (k-note-writes (cdr e))))))
(define k-mask (subr (maxeff (read @globals) (read @t) (write @t) (alloc @t) spin) (kx k-eff int) k-eff)
  (lambda (x e result)
    (if (begin (k-note-writes e) (null? e))
        e
        (let* ((in-result (k-regions-in result))
               (sought (k-sought e in-result nil)))
          (if (null? sought)
              e
              (k-keep e (k-unseen x nil sought) in-result))))))

;;; ------------------------------------------------------------ substitution

(define k-subst-conv (subr (maxeff (read @globals) (read @t)) (k-conv k-map) k-conv)
  (lambda (c m)
    (tagcase c
      (cv-var (v) (let ((f (k-map-find m v))) (if (null? f) c (tagcase (cdr (car f)) (dc (x) x) (else y c)))))
      (else y c))))
(define k-subst-region (subr (maxeff (read @globals) (read @t)) (k-region k-map) k-region)
  (lambda (r m)
    (tagcase r
      (r-var (v) (let ((f (k-map-find m v))) (if (null? f) r (tagcase (cdr (car f)) (dr (x) x) (else y r)))))
      ;; Frozen data's place too.
      (r-frozen (p fin)
        (let ((f (if (< p 0) (the k-map nil) (k-map-find m p))))
          (if (null? f)
              r
              (tagcase (cdr (car f))
                (dr (x) (tagcase x (r-var (q) (r-frozen q fin)) (r-heap () (r-frozen -1 fin)) (else z r)))
                (else y r)))))
      (else y r))))
(define k-subst-effect (subr (maxeff (read @globals) (read @t) (alloc @t) spin) (k-eff k-map) k-eff)
  (lambda (e m)
    (if (null? e)
        nil
        (let* ((a (car e))
               (rest (k-subst-effect (cdr e) m))
               (piece (tagcase a
                        (a-var (v)
                          (let ((f (k-map-find m v)))
                            (if (null? f) (k-one a) (tagcase (cdr (car f)) (de (x) x) (else y (k-one a))))))
                        (else y (k-one (k-atom-with a (k-subst-region (k-atom-region a) m)))))))
          (k-union piece rest)))))
(define k-memo-find (subr (maxeff (read @globals) (read @t)) ((listof (pairof int int @t) acyclic) int) int)
  (lambda (ms t) (cond ((null? ms) -1) ((= (car (car ms)) t) (cdr (car ms))) (else (k-memo-find (cdr ms) t)))))

(define k-ty-rank (subr (maxeff (read @globals) (read @t) spin) (int) int)
  (lambda (t)
    (tagcase (k-get t)
      (ty-base (s) 0) (ty-void () 1) (ty-var (v) 2) (ty-subr (e ps r cv) 3) (ty-poly (bs x) 4) (ty-ref (x r) 5)
      (ty-pair (x y r) 6) (ty-tag (x y e r) 7) (ty-comp (x y e r) 8) (ty-markkey (x r) 9) (ty-product (ps) 10)
      (ty-sum (ps) 11) (ty-array (x r) 12) (ty-bloblet (fs z r) 13) (ty-link (x) 14) (ty-icell (x r) 15) (ty-place (r) 16)
      (ty-named (g ds) 17) (ty-nlist (e z r) 18) (ty-nat (z) 19))))
;; Whether no instantiation of `pattern` could fit `actual`.
;; Whether a lemma's side `pat` could fit `t`, by their outermost shapes.
(define k-lemma-head? (subr (maxeff (read @globals) (read @t) spin) (k-binders int int) bool)
  (lambda (bs pat t)
    (let ((p (k-resolve pat)))
      (tagcase (k-get p)
        (ty-var (v) (or (k-binder-has? bs v) (= (k-ty-rank p) (k-ty-rank t))))
        (ty-named (g xs) (tagcase (k-get t) (ty-named (h ys) (= g h)) (else z #f)))
        (else z (= (k-ty-rank p) (k-ty-rank t)))))))
(define k-lemma-may-apply? (subr (maxeff (read @globals) (read @t) spin) ((listof k-lemma acyclic) int int) bool)
  (lambda (ls a b)
    (and (not (null? ls))
         (or (let ((l (car ls))) (and (k-lemma-head? (extract l 1) (extract l 2) a) (k-lemma-head? (extract l 1) (extract l 3) b)))
             (k-lemma-may-apply? (cdr ls) a b)))))
(define k-pair-seen? (subr (maxeff (read @globals) (read @t)) ((listof (pairof int int @t) acyclic) int int) bool)
  (lambda (xs a b) (and (not (null? xs)) (or (and (= (car (car xs)) a) (= (cdr (car xs)) b)) (k-pair-seen? (cdr xs) a b)))))
(define k-all-bound? (subr (maxeff (read @globals) (read @t)) (k-binders k-map) bool)
  (lambda (bs m) (or (null? bs) (and (not (null? (k-map-find m (extract (car bs) 1)))) (k-all-bound? (cdr bs) m)))))
(define-rec
  (k-subst-memo (subr (maxeff kstate spin) (int k-map (ref (listof (pairof int int @t) acyclic) @t)) int)
    (lambda (t m memo)
      (let* ((t (k-resolve t)) (done (k-memo-find (get memo) t)))
        (if (>= done 0)
            done
            (tagcase (k-get t)
              (ty-base (s) t)
              (ty-void () t)
              (ty-link (x) t)
              (ty-var (v) (let ((f (k-map-find m v))) (if (null? f) t (tagcase (cdr (car f)) (dt (x) x) (else y t)))))
              (else y
                (let ((slot (k-slot)))
                  (begin
                    (set memo (cons (cons t slot) (get memo)))
                    (letrec ((sub (subr (maxeff (read @globals) kstate spin) (int) int) (lambda (x) (k-subst-memo x m memo)))
                             (subs (subr (maxeff (read @globals) kstate spin) (k-ids) k-ids) (lambda (xs) (k-subst-list xs m memo)))
                             (reg (subr (maxeff (read @globals) (read @t)) (k-region) k-region) (lambda (r) (k-subst-region r m))))
                    (let* ((new-ty
                            (tagcase (k-get t)
                              (ty-subr (e ps r cv) (let* ((e2 (k-subst-effect e m)) (ps2 (subs ps)) (r2 (sub r))) (ty-subr e2 ps2 r2 (k-subst-conv cv m))))
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
                              (ty-nlist (e z r) (ty-nlist (sub e) (k-subst-size z m) (reg r)))
                              (ty-nat (z) (ty-nat (k-subst-size z m)))
                              (else z (k-get t))))
                           (id (k-ty-new new-ty)))
                      (begin (k-set-link slot id) slot)))))))))))
  (k-subst-descs (subr (maxeff kstate spin) ((listof k-desc acyclic) k-map (ref (listof (pairof int int @t) acyclic) @t)) (listof k-desc acyclic))
    (lambda (ds m memo)
      (if (null? ds)
          nil
          (let* ((d (tagcase (car ds)
                      (dt (x) (dt (k-subst-memo x m memo)))
                      (dr (r) (dr (k-subst-region r m)))
                      (de (e) (de (k-subst-effect e m)))
                      (dz (z) (dz (k-subst-size z m)))
                      (dc (c) (dc (k-subst-conv c m)))))
                 (rest (k-subst-descs (cdr ds) m memo)))
            (cons d rest)))))
  (k-subst-list (subr (maxeff kstate spin) (k-ids k-map (ref (listof (pairof int int @t) acyclic) @t)) k-ids)
    (lambda (ts m memo)
      (if (null? ts) nil (let* ((x (k-subst-memo (car ts) m memo)) (rest (k-subst-list (cdr ts) m memo))) (cons x rest)))))
  (k-subst-parts (subr (maxeff kstate spin) (k-parts k-map (ref (listof (pairof int int @t) acyclic) @t)) k-parts)
    (lambda (ps m memo)
      (if (null? ps)
          nil
          (let* ((x (k-subst-memo (extract (car ps) 2) m memo)) (rest (k-subst-parts (cdr ps) m memo)))
            (cons (product (1 (extract (car ps) 1)) (2 x)) rest))))))

;; `t` with each binder in `m` replaced. Recursive types are copied as
;; cycles: each node gets its slot before its children are built.
(define k-subst (subr (maxeff kstate spin) (int k-map) int)
  (lambda (t m) (k-subst-memo t m (the (ref (listof (pairof int int @t) acyclic) @t) (new nil)))))
;; The `g`th generative type's representation, for `ds`.
(define k-subst-hyps (subr (maxeff kstate spin) (k-hyps k-map) k-hyps)
  (lambda (hs m)
    (if (null? hs) nil (let* ((x (k-subst (car (car hs)) m)) (y (k-subst (cdr (car hs)) m))) (the k-hyps (cons (cons x y) (k-subst-hyps (cdr hs) m)))))))
(define k-gen-map (subr (maxeff (read @globals) (alloc @t)) (k-binders (listof k-desc acyclic)) k-map)
  (lambda (bs ds) (if (null? bs) nil (the k-map (cons (cons (extract (car bs) 1) (car ds)) (k-gen-map (cdr bs) (cdr ds)))))))
(define k-unfold (subr (maxeff kstate spin) (int (listof k-desc acyclic)) int)
  (lambda (g ds) (let ((gen (k-gen-of g))) (k-subst (extract gen 4) (k-gen-map (extract gen 2) ds)))))

;; `b`'s binders renamed to `a`'s, for comparing under them.
(define k-rename (subr (maxeff kstate spin) (k-binders k-binders) k-map)
  (lambda (bs as)
    (if (null? bs)
        nil
        (let* ((vb (extract (car bs) 1)) (k (extract (car bs) 2)) (va (extract (car as) 1))
               (d (cond ((or (= k 0) (= k 3)) (dr (r-var va))) ((= k 1) (de (k-one (a-var va)))) ((= k 5) (dz (k-size-var va)))
                        ((= k 6) (dc (cv-var va)))
                        (else (dt (k-ty-new (ty-var va))))))
               (rest (k-rename (cdr bs) (cdr as))))
          (cons (cons vb d) rest)))))
(define k-same-kinds? (subr (maxeff (read @globals) (read @t)) (k-binders k-binders) bool)
  (lambda (xs ys)
    (cond ((null? xs) (null? ys))
          ((null? ys) #f)
          (else (and (= (extract (car xs) 2) (extract (car ys) 2)) (k-same-kinds? (cdr xs) (cdr ys)))))))
