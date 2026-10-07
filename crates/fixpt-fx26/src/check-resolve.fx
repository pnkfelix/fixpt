;;; The checker, in FX-26: resolving the trees' descriptions, callables,
;;; regions of types, and masking (substitution is `check-subst.fx`'s).
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
(define-type exp-letrec-bs (listof (productof (1 symbol) (2 syn) (3 exp)) acyclic))
(define-type exp-let-bs (listof (productof (1 symbol) (2 exp)) acyclic))
(define-type exp-arms (listof (productof (1 symbol) (2 bool) (3 names) (4 exp)) acyclic))

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
      (set k-operator (product (1 '||) (2 -1) (3 -1)))
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
        ;; `(with #%fx n)`, the standard `n`: nothing free.
        (x-with (m body a b)
          (if (k-fx-module? m)
              out
              (k-free-into body (k-names-onto (k-with-names a b) bound) (k-note m bound out)))))))
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
(define-type exp-letrec-bs (select check-resolve-module exp-letrec-bs))
(define-type exp-let-bs (select check-resolve-module exp-let-bs))
(define-type exp-arms (select check-resolve-module exp-arms))
(define k-start (with check-resolve-module k-start))
(define k-end (with check-resolve-module k-end))
(define k-copy-names (with check-resolve-module k-copy-names))
(define exp-start (with check-resolve-module exp-start))
(define exp-end (with check-resolve-module exp-end))
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
(define k-ty-rank (with check-resolve-module k-ty-rank))
(define k-lemma-may-apply? (with check-resolve-module k-lemma-may-apply?))
(define k-pair-seen? (with check-resolve-module k-pair-seen?))
(define k-all-bound? (with check-resolve-module k-all-bound?))
(define k-subst-hyps (with check-resolve-module k-subst-hyps))
(define k-unfold (with check-resolve-module k-unfold))
(define k-rename (with check-resolve-module k-rename))
(define k-same-kinds? (with check-resolve-module k-same-kinds?))
(define k-resolve-params (with check-resolve-module k-resolve-params))
(define k-order-binders (with check-resolve-module k-order-binders))
(define k-resolve-place (with check-resolve-module k-resolve-place))
(define k-place-lives (with check-resolve-module k-place-lives))
(define k-freeze-into (with check-resolve-module k-freeze-into))
(define k-resolve-descs (with check-resolve-module k-resolve-descs))
