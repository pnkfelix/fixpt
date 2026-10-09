;;; The checker, in FX-26 (PLAN.md §11, step 10).
;;;
;;; The Rust checker's rules (`check.rs`, `infer.rs`) and its reading of
;;; descriptions (`parse.rs`, `top.rs`), over the parser's trees, rule for
;;; rule and message for message, so the two can be compared: for each
;;; top-level form, what it defines or what type and effect it has; or the
;;; first error, and where it is.
;;;
;;; Types live in an arena, as in Rust: a type is an index, and a recursive
;;; type is a cycle of indexes through forwarding links. Effects are sets of
;;; atoms kept sorted, so `(maxeff e (maxeff e pure))` and `e` are one list;
;;; the order is this file's own, and printing follows it.
;;;
;;; The parser keeps descriptions as the syntax they were written in. A
;;; first pass, `k-resolve`, reads them into the arena, in the order the Rust
;;; parser does (a `lambda`'s parameter types before its body, a `letrec`'s
;;; type before its initialiser), so the first error is the same one.
;;;
;;; Compiled with the reader and the parser, as one program. Its store is
;;; @t and its failures abort to a prompt in @z.

;; Its types, those it uses of the files before it, and the signatures of
;; what it is given.
;; Its types (`check-types-types.fx`), loaded before the module so that they are not
;; among its values; the module names what it uses of them.
(let* ((check-types-types (load-module "fx26:check-types-types.fx"))
       (eager-reader-types ((proj (load-module "fx26:eager-reader-types.fx") @s @e @m @c)))
       (table-types (load-module "fx26:table-types.fx"))
       (check-modorder-types (load-module "fx26:check-modorder-types.fx")))
  ;; What it is given: the modules of the files before it that it uses.
  (lambda ((tables (select table-types tables-sig)))
    (module
(define-effect kstate (select check-types-types kstate))
(define-effect checks (select check-types-types checks))
(define-effect kreads (select check-types-types kreads))
(define-effect kbuilds (select check-types-types kbuilds))
(define-type k-region (select check-types-types k-region))
(define r-const (with check-types-types r-const))
(define r-fresh (with check-types-types r-fresh))
(define r-var (with check-types-types r-var))
(define r-frozen (with check-types-types r-frozen))
(define r-heap (with check-types-types r-heap))
(define r-global (with check-types-types r-global))
(define r-globals (with check-types-types r-globals))
(define-type k-atom (select check-types-types k-atom))
(define a-read (with check-types-types a-read))
(define a-write (with check-types-types a-write))
(define a-alloc (with check-types-types a-alloc))
(define a-goto (with check-types-types a-goto))
(define a-comefrom (with check-types-types a-comefrom))
(define a-await (with check-types-types a-await))
(define a-spin (with check-types-types a-spin))
(define a-var (with check-types-types a-var))
(define a-app (with check-types-types a-app))
(define-type k-eff (select check-types-types k-eff))
(define-type k-vsub (select check-types-types k-vsub))
(define-type k-ids (select check-types-types k-ids))
(define-type k-term (select check-types-types k-term))
(define tm-param (with check-types-types tm-param))
(define tm-length (with check-types-types tm-length))
(define tm-lit (with check-types-types tm-lit))
(define-type k-prop (select check-types-types k-prop))
(define pr-shape (with check-types-types pr-shape))
(define pr-acyclic (with check-types-types pr-acyclic))
(define pr-nat (with check-types-types pr-nat))
(define pr-length (with check-types-types pr-length))
(define pr-rel (with check-types-types pr-rel))
(define-type k-props (select check-types-types k-props))
(define-type k-binders (select check-types-types k-binders))
(define-type k-parts (select check-types-types k-parts))
(define-type k-names (select check-types-types k-names))
(define-type k-strings (select check-types-types k-strings))
(define-type k-conv (select check-types-types k-conv))
(define cv-cellular (with check-types-types cv-cellular))
(define cv-native (with check-types-types cv-native))
(define cv-fx (with check-types-types cv-fx))
(define cv-var (with check-types-types cv-var))
(define-type k-terms (select check-types-types k-terms))
(define-type k-size (select check-types-types k-size))
(define sz-finite (with check-types-types sz-finite))
(define sz-lin (with check-types-types sz-lin))
(define-type k-desc (select check-types-types k-desc))
(define dr (with check-types-types dr))
(define de (with check-types-types de))
(define dt (with check-types-types dt))
(define dz (with check-types-types dz))
(define dc (with check-types-types dc))
(define df (with check-types-types df))
(define-type k-descs (select check-types-types k-descs))
(define-type k-ty (select check-types-types k-ty))
(define ty-base (with check-types-types ty-base))
(define ty-void (with check-types-types ty-void))
(define ty-var (with check-types-types ty-var))
(define ty-subr (with check-types-types ty-subr))
(define ty-poly (with check-types-types ty-poly))
(define ty-ref (with check-types-types ty-ref))
(define ty-pair (with check-types-types ty-pair))
(define ty-tag (with check-types-types ty-tag))
(define ty-comp (with check-types-types ty-comp))
(define ty-markkey (with check-types-types ty-markkey))
(define ty-product (with check-types-types ty-product))
(define ty-sum (with check-types-types ty-sum))
(define ty-array (with check-types-types ty-array))
(define ty-icell (with check-types-types ty-icell))
(define ty-place (with check-types-types ty-place))
(define ty-bloblet (with check-types-types ty-bloblet))
(define ty-link (with check-types-types ty-link))
(define ty-named (with check-types-types ty-named))
(define ty-nlist (with check-types-types ty-nlist))
(define ty-nat (with check-types-types ty-nat))
(define ty-module (with check-types-types ty-module))
(define ty-select (with check-types-types ty-select))
(define ty-param (with check-types-types ty-param))
(define ty-lam (with check-types-types ty-lam))
(define ty-app (with check-types-types ty-app))
(define ty-nil (with check-types-types ty-nil))
(define ty-union (with check-types-types ty-union))
(define ty-proving (with check-types-types ty-proving))
(define ty-false (with check-types-types ty-false))
(define-type k-map (select check-types-types k-map))
(define-type k-ds (select check-types-types k-ds))
(define ds-gen (with check-types-types ds-gen))
(define ds-size (with check-types-types ds-size))
(define ds-var (with check-types-types ds-var))
(define ds-rec (with check-types-types ds-rec))
(define ds-abbrev (with check-types-types ds-abbrev))
(define ds-region (with check-types-types ds-region))
(define ds-eff (with check-types-types ds-eff))
(define ds-conv (with check-types-types ds-conv))
(define ds-fun (with check-types-types ds-fun))
(define-type kx (select check-types-types kx))
(define x-var (with check-types-types x-var))
(define x-const (with check-types-types x-const))
(define x-lambda (with check-types-types x-lambda))
(define x-app (with check-types-types x-app))
(define x-plambda (with check-types-types x-plambda))
(define x-letregion (with check-types-types x-letregion))
(define x-rlambda (with check-types-types x-rlambda))
(define x-proj (with check-types-types x-proj))
(define x-if (with check-types-types x-if))
(define x-letrec (with check-types-types x-letrec))
(define x-let (with check-types-types x-let))
(define x-begin (with check-types-types x-begin))
(define x-prompt (with check-types-types x-prompt))
(define x-the (with check-types-types x-the))
(define x-convention (with check-types-types x-convention))
(define x-bloblet (with check-types-types x-bloblet))
(define x-product (with check-types-types x-product))
(define x-extract (with check-types-types x-extract))
(define x-sum (with check-types-types x-sum))
(define x-tagcase (with check-types-types x-tagcase))
(define x-module (with check-types-types x-module))
(define x-with (with check-types-types x-with))
(define-type kxs (select check-types-types kxs))
(define-type k-item (select check-types-types k-item))
(define-type k-items (select check-types-types k-items))
(define-type k-te (select check-types-types k-te))
(define-type k-result (select check-types-types k-result))
(define k-ok (with check-types-types k-ok))
(define k-err (with check-types-types k-err))
(define k-done (with check-types-types k-done))
(define-type k-narrows (select check-types-types k-narrows))
(define-type k-pendings (select check-types-types k-pendings))
(define-type k-cert-len (select check-types-types k-cert-len))
(define-type k-arrow-kind (select check-types-types k-arrow-kind))
(define-type k-bounded (select check-types-types k-bounded))
(define-type k-nesting (select check-types-types k-nesting))
(define-type k-named (select check-types-types k-named))
(define-type k-gen (select check-types-types k-gen))
(define-type k-hyps (select check-types-types k-hyps))
(define-type k-lemma (select check-types-types k-lemma))
(define-type k-regions (select check-types-types k-regions))
(define-type k-step (select check-types-types k-step))
(define st-car (with check-types-types st-car))
(define st-cdr (with check-types-types st-cdr))
(define st-field (with check-types-types st-field))
(define-type k-steps (select check-types-types k-steps))
(define-type k-path-fact (select check-types-types k-path-fact))
(define-type k-path-facts (select check-types-types k-path-facts))
;; The types it uses of the files before it.
(define-type chars (select eager-reader-types chars))
(define-type table (select table-types table))
(define-type k-places (select check-modorder-types k-places))
;; What it uses of the modules it is given.
(define make-table (with tables make-table))
(define symbol-hash (with tables symbol-hash))
(define table-ref (with tables table-ref))

(define k-te (subr pure (int k-eff) k-te) (lambda (t e) (product (1 t) (2 e))))

(define k-tag (prompt-tag k-result k-result (maxeff spin (read @s) kstate) @z)
  (make-continuation-prompt-tag))
(define k-fail (subr checks (string int int) void)
  (lambda (m a b) (abort-current-continuation k-tag (k-err m a b))))

;;; ---------------------------------------------------------------- strings

(define k-cat3 (subr pure (string string string) string)
  (lambda (a b c) (string-append a (string-append b c))))
(define k-cat4 (subr (read @globals) (string string string string) string)
  (lambda (a b c d) (string-append a (k-cat3 b c d))))
(define k-cat5 (subr (read @globals) (string string string string string) string)
  (lambda (a b c d e) (string-append a (k-cat4 b c d e))))
(define k-quote (subr (read @globals) (string) string) (lambda (n) (k-cat3 "`" n "`")))

;; `xs` joined, `sep` between each two: their characters gathered, last to
;; first, into one list in an arena of its own, made a string once; so a long
;; list costs its length, not its length squared, as appending each to the
;; rest did (a module type's components, printed: `docs/performance.md`).
(define k-join (subr (maxeff (read @globals) (read @t)) ((listof string acyclic) string) string)
  (lambda (xs sep)
    (letrena r
      (letrec ((chars (subr (alloc r) (string int (listof char r)) (listof char r))
                 (lambda (s i acc)
                   (if (< i 0) acc (chars s (- i 1) (rcons r (string-ref s i) acc)))))
               (onto (subr (maxeff (alloc r) (read @t)) (string (listof char r)) (listof char r))
                 (lambda (s acc) (chars s (- (string-length s) 1) acc)))
               (all (subr (maxeff (alloc r) (read @t)) (k-strings (listof char r)) (listof char r))
                 (lambda (xs acc)
                   (cond ((null? xs) acc)
                         ((null? (cdr xs)) (onto (car xs) acc))
                         (else (onto (car xs) (onto sep (all (cdr xs) acc))))))))
        (list->string (all xs nil))))))

;; Where `sub` first starts in `s` from `at`, or -1.
(define k-find-sub (subr (maxeff (read @globals) spin) (string string int) int)
  (lambda (s sub at) (string-search s sub at)))

(define k-str-cmp (subr (maxeff (read @globals) spin) (string string int) int)
  (lambda (a b i) (string-compare a b)))
(define k-int-cmp (subr pure (int int) int)
  (lambda (x y) (cond ((< x y) -1) ((> x y) 1) (else 0))))

;;; ------------------------------------------------------------ lists

;; Over finite lists, which every list here is: so they end.
(define k-length
  (poly ((t type)) (subr (read @globals) ((listof t acyclic)) int))
  (plambda ((t type))
    (lambda ((xs (listof t acyclic))) (if (null? xs) 0 (+ 1 (k-length (cdr xs)))))))
(define k-nth
  (poly ((t type)) (subr (read @globals) ((listof t acyclic) int) t))
  (plambda ((t type))
    (lambda ((xs (listof t acyclic)) (i int)) (if (= i 0) (car xs) (k-nth (cdr xs) (- i 1))))))
(define k-has-name? (subr (maxeff (read @globals) (read @t)) (k-names symbol) bool)
  (lambda (xs s) (cond ((null? xs) #f) ((symbol=? (car xs) s) #t) (else (k-has-name? (cdr xs) s)))))
(define k-has-id? (subr (maxeff (read @globals) (read @t)) (k-ids int) bool)
  (lambda (xs s) (cond ((null? xs) #f) ((= (car xs) s) #t) (else (k-has-id? (cdr xs) s)))))

;;; ------------------------------------------------------------ the arena

(define k-tys (ref (arrayof k-ty @t) @t) (new (make-array 512 (ty-void))))
(define k-ntys (ref int @t) (new 0))

;; Copy `from`, from its `i`th element on, into the bigger array `to`.
(define k-copy-array
  (poly ((t type)) (subr (maxeff kreads (write @t) spin) ((arrayof t @t) (arrayof t @t) int) unit))
  (plambda ((t type))
    (lambda ((from (arrayof t @t)) (to (arrayof t @t)) (i int))
      (if (= i (array-length from))
          #u
          (begin (array-set! to i (array-ref from i)) (k-copy-array from to (+ i 1)))))))

(define k-ty-new (subr (maxeff kstate spin) (k-ty) int)
  (lambda (t)
    (let ((n (get k-ntys)))
      (begin
        (if (= n (array-length (get k-tys)))
            (let ((bigger (the (arrayof k-ty @t) (make-array (* 2 n) (ty-void)))))
              (begin (k-copy-array (get k-tys) bigger 0) (set k-tys bigger)))
            #u)
        (array-set! (get k-tys) n t)
        (set k-ntys (+ n 1))
        n))))

(define k-raw (subr kreads (int) k-ty) (lambda (id) (array-ref (get k-tys) id)))
;; Follow forwarding links to the type itself.
(define k-resolve (subr (maxeff kreads spin) (int) int)
  (lambda (id)
    (tagcase (k-raw id)
      (ty-link (to) (if (null? to) id (k-resolve (car to))))
      (else x id))))
(define k-get (subr (maxeff kreads spin) (int) k-ty) (lambda (id) (k-raw (k-resolve id))))
;; How many links have been made from the types below `k-links-below`, those
;; of the tree of names kept (`k-atree-now`): what one of them resolves to
;; changes only with one. A type made after it is in no tree kept.
(define k-links (ref int @t) (new 0))
(define k-links-below (ref int @t) (new 0))
(define k-set-link (subr kstate (int int) unit)
  (lambda (slot to)
    (begin (if (< slot (get k-links-below)) (set k-links (+ (get k-links) 1)) #u)
           (array-set! (get k-tys) slot (ty-link (cons to nil))))))
(define k-slot (subr (maxeff kstate spin) () int) (lambda () (k-ty-new (ty-link nil))))

;; Which types a walk has seen: a type is seen in walk `e` when its mark
;; is `e`, so each walk takes a new epoch and nothing is cleared.
(define k-marks (ref (arrayof int @t) @t) (new (make-array 512 0)))
(define k-epoch (ref int @t) (new 0))
(define k-new-epoch (subr kstate () int)
  (lambda () (begin (set k-epoch (+ (get k-epoch) 1)) (get k-epoch))))
;; Whether walk `e` has seen `t` already; if not, it has now.
(define k-visit? (subr (maxeff kstate spin) (int int) bool)
  (lambda (t e)
    (begin
      (if (>= t (array-length (get k-marks)))
          (let ((bigger (the (arrayof int @t) (make-array (* 2 (array-length (get k-tys))) 0))))
            (begin (k-copy-array (get k-marks) bigger 0) (set k-marks bigger)))
          #u)
      (if (= (array-ref (get k-marks) t) e)
          #t
          (begin (array-set! (get k-marks) t e) #f)))))

;; Description variables, newest first, for their names.
(define k-dvars (ref k-names @t) (new nil))
(define k-ndvars (ref int @t) (new 0))
(define k-new-dvar (subr kstate (symbol) int)
  (lambda (name)
    (let ((n (get k-ndvars)))
      (begin (set k-dvars (cons name (get k-dvars))) (set k-ndvars (+ n 1)) n))))
;; The description variables bound as places (kind 3), which are regions too.
(define k-places (ref k-ids @t) (new nil))
(define k-datas (ref k-ids @t) (new nil))
;; The variables `acyclic?` has just found acyclic, in the branch where it
;; did: each by name and by which binding it is (how deep its name's stack).
(define k-certified (ref (listof (pairof symbol int @t) acyclic) @t) (new nil))
(define k-narrowed (ref k-narrows @t) (new nil))
;; Whether `k-unify` is inside a pair's contents (the Rust checker's
;; `unify_exact`).
(define k-unify-exact (ref bool @t) (new #f))
(define k-pending-unions (ref k-pendings @t) (new nil))
;; The sizes given to `nat` variables of no known size, newest first
;; (`k-name-nat`).
(define k-skolems (ref k-ids @t) (new nil))
;; The same for `nat?`: the variables it has just found no less than 0.
(define k-certified-nats (ref (listof (pairof symbol int @t) acyclic) @t) (new nil))
(define k-certified-lengths (ref (listof k-cert-len acyclic) @t) (new nil))
(define k-arrows (ref (listof k-arrow-kind acyclic) @t) (new nil))
(define k-narrows (ref int @t) (new 0))
(define k-ids=? (subr (read @globals) (k-ids k-ids) bool)
  (lambda (xs ys)
    (cond ((null? xs) (null? ys))
          ((null? ys) #f)
          (else (and (= (car xs) (car ys)) (k-ids=? (cdr xs) (cdr ys)))))))
;; The kind of the arrow `ps` to `r` among `as`, `n` of them, newest first;
;; or -1.
(define k-arrow-find (subr kreads ((listof k-arrow-kind acyclic) k-ids int int) int)
  (lambda (as ps r n)
    (cond ((null? as) -1)
          ((and (= (cdr (car as)) r) (k-ids=? (car (car as)) ps)) (+ 100 (- n 1)))
          (else (k-arrow-find (cdr as) ps r (- n 1))))))
;; The arrow kind `(=> (ps …) r)`, interned.
(define k-arrow (subr (maxeff kstate spin) (k-ids int) int)
  (lambda (ps r)
    (let ((found (k-arrow-find (get k-arrows) ps r (get k-narrows))))
      (if (>= found 0)
          found
          (let ((n (get k-narrows)))
            (begin
              (set k-arrows (cons (cons ps r) (get k-arrows)))
              (set k-narrows (+ n 1))
              (+ 100 n)))))))
;; An arrow kind's parameters' kinds and result's, none or one: none for a
;; base kind, or none known (-1).
(define k-arrow-parts (subr kreads (int) (listof k-arrow-kind acyclic))
  (lambda (k)
    (if (< k 100)
        nil
        (cons (k-nth (get k-arrows) (- (- (get k-narrows) 1) (- k 100))) nil))))
(define k-arrow-kind? (subr pure (int) bool) (lambda (k) (>= k 100)))
;; The kind an arrow kind gives, or -1 for any other.
(define k-arrow-result (subr kreads (int) int)
  (lambda (k) (let ((a (k-arrow-parts k))) (if (null? a) -1 (cdr (car a))))))
;; The kinds an arrow kind takes, or none for any other.
(define k-arrow-params (subr kreads (int) k-ids)
  (lambda (k) (let ((a (k-arrow-parts k))) (if (null? a) nil (car (car a))))))
;; Binders' kinds.
(define k-binder-kinds (subr (read @globals) (k-binders) k-ids)
  (lambda (bs) (if (null? bs) nil (cons (extract (car bs) 2) (k-binder-kinds (cdr bs))))))
;; Each description variable of an arrow kind, with its kind (`check-kinds.fx`).
(define k-arrow-vars (ref (listof (pairof int int @t) acyclic) @t) (new nil))
;; The description-function variables that are a module's abstract type
;; constructors, whose representations no one outside can see: what is
;; given to one is kept, cautiously, everywhere (`k-knot-in`).
(define k-abstract-funs (ref k-ids @t) (new nil))
(define k-new-dvar-of (subr kstate (symbol int) int)
  (lambda (name kind)
    (let ((v (k-new-dvar name)))
      (begin (if (= kind 3) (set k-places (cons v (get k-places))) #u)
             (if (= kind 4) (set k-datas (cons v (get k-datas))) #u)
             (if (>= kind 100) (set k-arrow-vars (cons (cons v kind) (get k-arrow-vars))) #u)
             v))))
;; Which description variables are of kind `data`.
(define k-data-var? (subr (maxeff (read @globals) (read @t)) (int) bool)
  (lambda (v) (k-has-id? (get k-datas) v)))
(define k-place-var? (subr (maxeff (read @globals) (read @t)) (int) bool)
  (lambda (v) (k-has-id? (get k-places) v)))
;; Each description variable of an arrow kind, with its kind
;; (`k-new-dvar-of` notes them).
(define k-dvar-kind (subr kreads (int) int)
  (lambda (v)
    (letrec ((find (subr kreads ((listof (pairof int int @t) acyclic)) int)
                     (lambda (xs)
                       (cond ((null? xs) -1)
                             ((= (car (car xs)) v) (cdr (car xs)))
                             (else (find (cdr xs)))))))
      (let ((a (find (get k-arrow-vars))))
        (cond ((>= a 0) a) ((k-place-var? v) 3) ((k-data-var? v) 4) (else 2))))))
(define k-bounds (ref k-bounded @t) (new nil))
(define k-outers (ref k-nesting @t) (new nil))
;; The region and place variables bound around what is being read, by
;; expressions (not types), innermost first.
(define k-lifetimes (ref k-ids @t) (new nil))
;; The regions `letfreeze`s are freezing, and those of them anything has
;; written: data never written is finite.
(define k-freezing (ref k-ids @t) (new nil))
(define k-written (ref k-ids @t) (new nil))
(define k-recursive (ref k-named @t) (new nil))
(define k-std (ref k-named @t) (new nil))
;; The same, a table: each standard name's binding, newest (`k-bind-std`).
(define k-std-table (ref (table symbol int @t) @t) (new (make-table symbol-hash symbol=?)))
;; The standard binding of `s`, -1 if none.
(define k-std-type (subr (maxeff (read @globals) (read @t)) (symbol) int)
  (lambda (s) (table-ref (get k-std-table) s -1)))
;; Whether binding `t` of `s` is the standard one.
(define k-std-binding? (subr (maxeff (read @globals) (read @t)) (symbol int) bool)
  (lambda (s t) (and (>= t 0) (= (k-std-type s) t))))
(define k-gens (ref (listof k-gen acyclic) @t) (new nil))
(define k-ngens (ref int @t) (new 0))
(define k-gen-of (subr kreads (int) k-gen)
  (lambda (g) (k-nth (get k-gens) (- (- (get k-ngens) 1) g))))
;; The generative types whose insides the definition being checked may see;
;; the definitions still to come that may see inside one; and the bindings
;; of their conversions, which are the identity.
(define k-transparent (ref k-ids @t) (new nil))
(define k-inside (ref (listof (pairof symbol int @t) acyclic) @t) (new nil))
(define k-conversions (ref k-named @t) (new nil))
(define k-lemmas (ref (listof k-lemma acyclic) @t) (new nil))
(define k-pending-lemma (ref (listof k-lemma acyclic) @t) (new nil))
(define k-binder-has? (subr kreads (k-binders int) bool)
  (lambda (bs v) (and (not (null? bs)) (or (= (extract (car bs) 1) v) (k-binder-has? (cdr bs) v)))))
;; Whether one of generative types `gs` has `v` among its parameters.
(define k-gens-bind? (subr kreads ((listof k-gen acyclic) int) bool)
  (lambda (gs v)
    (and (not (null? gs)) (or (k-binder-has? (extract (car gs) 2) v) (k-gens-bind? (cdr gs) v)))))
;; Whether `v` is a generative type's parameter, and `r` one or frozen into one.
(define k-gen-param? (subr kreads (int) bool)
  (lambda (v) (k-gens-bind? (get k-gens) v)))
;; The types among descriptions, and the regions.
(define k-desc-types (subr (maxeff (read @globals) (alloc @t)) (k-descs) k-ids)
  (lambda (ds)
    (if (null? ds)
        nil
        (let ((rest (k-desc-types (cdr ds))))
          (tagcase (car ds) (dt (x) (the k-ids (cons x rest))) (else y rest))))))
(define k-path-narrowed (ref k-path-facts @t) (new nil))
;; How many closures' bodies are being checked.
(define k-closure-depth (ref int @t) (new 0))
(define k-desc-regions (subr (maxeff (read @globals) (alloc @t)) (k-descs) k-regions)
  (lambda (ds)
    (if (null? ds)
        nil
        (let ((rest (k-desc-regions (cdr ds))))
          (tagcase (car ds) (dr (r) (the k-regions (cons r rest))) (else y rest))))))
;; The description variable a region is, or is frozen into; -1 if none.
(define k-region-var (subr pure (k-region) int)
  (lambda (r) (tagcase r (r-var (v) v) (r-frozen (p f) p) (else x -1))))
(define k-gen-region? (subr kreads (k-region) bool)
  (lambda (r) (let ((v (k-region-var r))) (and (>= v 0) (k-gen-param? v)))))
;; Why each member of a recursive group that may not end may not.
(define k-spin-why (ref (listof (productof (1 symbol) (2 int) (3 string)) acyclic) @t) (new nil))
(define k-named-has? (subr kreads (k-named symbol int) bool)
  (lambda (ns n t)
    (and (not (null? ns))
         (or (and (symbol=? (car (car ns)) n) (= (cdr (car ns)) t)) (k-named-has? (cdr ns) n t)))))
;; The bound given region variable `v` among `bs`: none or one.
(define k-bound-in (subr (maxeff kreads (alloc @t)) (k-bounded int) k-regions)
  (lambda (bs v)
    (cond ((null? bs) nil)
          ((= (car (car bs)) v) (the k-regions (cons (cdr (car bs)) nil)))
          (else (k-bound-in (cdr bs) v)))))
(define k-bound-of (subr (maxeff kreads (alloc @t)) (int) k-regions)
  (lambda (v) (k-bound-in (get k-bounds) v)))
;; The variables bound around `v`'s binder, among `os`.
(define k-outer-in (subr kreads (k-nesting int) k-ids)
  (lambda (os v)
    (cond ((null? os) nil) ((= (car (car os)) v) (cdr (car os))) (else (k-outer-in (cdr os) v)))))
(define k-outer-of (subr kreads (int) k-ids)
  (lambda (v) (k-outer-in (get k-outers) v)))
(define k-set-outer (subr kstate (int k-ids) unit)
  (lambda (v outer) (set k-outers (cons (cons v outer) (get k-outers)))))
(define k-dvar-name (subr (maxeff (read @globals) (read @t)) (int) symbol)
  (lambda (v) (k-nth (get k-dvars) (- (- (get k-ndvars) 1) v)))))))
