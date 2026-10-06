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
;;; @t and its failures abort to a prompt in @z, both its own.

(private-regions @t @z)

;; The checker's state, and everything checking may do.
(define-effect kstate (maxeff (read @globals) (read @t) (write @t) (alloc @t)))
(define-effect checks (maxeff (read @s) kstate (goto @z)))
;; Reading the checker's state; and that, allocating in it, and perhaps not
;; ending, as reading and showing descriptions do.
(define-effect kreads (maxeff (read @globals) (read @t)))
(define-effect kbuilds (maxeff kreads (alloc @t) spin))

;;; ------------------------------------------------------------ descriptions

;; A region: a constant `@name`, a fresh one (made by inference, a bloblet,
;; or `private-regions`, which no program can name), or a binder.
;; `(r-frozen p #f)` is `(const p)`, and `(r-frozen p #t)` `(acyclic p)`
;; (frozen data never written, only built, and so finite); in both, the
;; region of data frozen into place `p` (a
;; place variable, or -1 for the heap: `const`), which nothing may write;
;; `r-heap` is `heap`, the place that never ends
;; (`docs/research/places-and-regions.md`). `(r-global g)` is `(globals g)`,
;; the binding of global `g`, and `r-globals` is `@globals`, every global's:
;; only in effects, only read and written, never masked.
(define-datatype k-region
  (r-const symbol) (r-fresh int string) (r-var int) (r-frozen int bool) (r-heap)
  (r-global symbol) (r-globals))

(define-datatype k-atom
  (a-read k-region) (a-write k-region) (a-alloc k-region)
  (a-goto k-region) (a-comefrom k-region) (a-await k-region) (a-spin) (a-var int)
  ;; `(e d …)`: a description function to an effect, a variable, applied
  ;; to descriptions, none a type (`check-kinds.fx`): an unknown effect, as
  ;; a variable is.
  (a-app int (listof k-desc acyclic)))
(define-type k-eff (listof k-atom acyclic))
;; A `vsubr`'s effect, element and result, in a list: one or none.
(define-type k-vsub (listof (productof (1 k-eff) (2 int) (3 int)) acyclic))

(define-type k-ids (listof int acyclic))
;; A binder: a description variable and its kind, 0 region, 1 effect, 2 type.
(define-type k-binders (listof (productof (1 int) (2 int)) acyclic))
(define-type k-parts (listof (productof (1 symbol) (2 int)) acyclic))
(define-type k-names (listof symbol acyclic))
(define-type k-strings (listof string acyclic))

;; A description in argument position, what `proj` supplies.
;; A list's length, as far as it is known: `finite`, some number; or a
;; constant and terms (variable . coefficient), in variable order.
;; A procedure's convention (`docs/research/native-conventions.md`):
;; `cellular`, `native`, `fx`, or a binder.
(define-datatype k-conv (cv-cellular) (cv-native) (cv-fx) (cv-var int))

;; A size's terms: each a variable and its coefficient.
(define-type k-terms (listof (pairof int int acyclic) acyclic))
(define-datatype k-size (sz-finite) (sz-lin int k-terms))

(define-datatype k-desc (dr k-region) (de k-eff) (dt int) (dz k-size) (dc k-conv)
  ;; A description function: a `dlambda`, a variable of an arrow kind, or a
  ;; `select` of a module's (`check-kinds.fx`).
  (df int))
(define-type k-descs (listof k-desc acyclic))

(define-datatype k-ty
  (ty-base symbol)
  (ty-void)
  (ty-var int)
  ;; effect, parameters, result, convention
  (ty-subr k-eff k-ids int k-conv)
  (ty-poly k-binders int)
  (ty-ref int k-region)
  (ty-pair int int k-region)
  ;; answer, payload, bound, region
  (ty-tag int int k-eff k-region)
  ;; argument, answer, effect, region
  (ty-comp int int k-eff k-region)
  (ty-markkey int k-region)
  (ty-product k-parts)
  (ty-sum k-parts)
  (ty-array int k-region)
  (ty-icell int k-region)
  ;; The place a region is allocated in, as a value: what `letrena` and
  ;; `letreap` bind.
  (ty-place k-region)
  (ty-bloblet k-ids bool k-region)
  ;; A forwarding slot: none or one.
  (ty-link k-ids)
  ;; A generative type applied to its descriptions: the `n`th
  ;; `define-generative`. Equal only to itself, by its variance; looked
  ;; through by every analysis of what a value holds.
  (ty-named int (listof k-desc acyclic))
  ;; `(nlist T size)`: a list frozen at the region (always finite) with `size`
  ;; elements, or some number (`docs/research/sizes.md`).
  (ty-nlist int k-size k-region)
  ;; `(nat size)`: a natural, exactly `size`; `nat` is `(nat finite)`.
  ;; Every one is an `int` (`docs/research/sizes.md`, N5d).
  (ty-nat k-size)
  ;; `(moduleof (abs t type) … (desc d T) … (val x T) …)`: a module's type
  ;; (`docs/research/first-class-modules.md`): its abstract types, each a
  ;; name and a type variable, binders in its descriptions and values.
  (ty-module k-parts k-parts k-parts)
  ;; `(select m t)` as written, resolved where it is checked
  ;; (`k-resolve-selects`).
  (ty-select symbol symbol)
  ;; `(select $k t)`: in a procedure's type, the type `t` of its `k`th
  ;; parameter (from 0), a module: a dependent procedure, a functor
  ;; (`first-class-modules.md`, M5). A call puts the argument's for it.
  (ty-param int symbol)
  ;; `(dlambda ((x k) …) d)`: a description function; and `(f d …)`, one
  ;; applied that cannot be reduced, `f` a variable or a `select`
  ;; (`check-kinds.fx`).
  (ty-lam k-binders k-desc)
  (ty-app int (listof k-desc acyclic)))

(define-type k-map (listof (pairof int k-desc @t) acyclic))

;; What a description name means where it is used.
(define-datatype k-ds
  ;; A name `define-generative` bound: the `n`th generative type.
  (ds-gen int)
  ;; A size given for a type family's size parameter.
  (ds-size k-size)
  (ds-var int int)
  (ds-rec int)
  (ds-abbrev (listof (productof (1 symbol) (2 int)) acyclic) syn)
  (ds-region k-region)
  (ds-eff k-eff)
  (ds-private k-region)
  ;; A convention given for an abbreviation's convention parameter.
  (ds-conv k-conv)
  ;; A name for a description function: `define-type` of a `dlambda`, or a
  ;; type family's parameter of an arrow kind given one.
  (ds-fun int))

;;; ------------------------------------------------------------ expressions
;;; The parser's trees with their descriptions read. Each ends with where it
;;; starts and ends.

(define-datatype kx
  (x-var symbol int int)
  ;; A literal: its type, and its value if an integer (a boolean's is 1
  ;; or 0), which the termination check reads.
  (x-const int int int int)
  (x-lambda (listof (productof (1 symbol) (2 k-ids)) acyclic) kx int int)
  (x-app kx (listof kx acyclic) int int)
  (x-plambda k-binders kx int int)
  ;; `letregion`, `letrena`, `letreap` or `letfreeze`: what it makes besides
  ;; the region (0 nothing, 1 an arena, 2 a reap, 3 nothing, frozen as it
  ;; ends), the region variable, what a `letfreeze` freezes into (`(const
  ;; p)`), and the body.
  (x-letregion int int k-region kx int int)
  ;; `rlambda`: the region, and the `lambda`.
  (x-rlambda kx kx int int)
  (x-proj kx (listof k-desc acyclic) int int)
  (x-if kx kx kx int int)
  (x-letrec (listof (productof (1 symbol) (2 int) (3 kx)) acyclic) kx int int)
  (x-let (listof (productof (1 symbol) (2 kx)) acyclic) kx int int)
  (x-begin (listof kx acyclic) int int)
  (x-prompt kx kx kx int int)
  (x-the int kx int int)
  ;; `(convention C e)`: the procedure converted to `C`.
  (x-convention k-conv kx int int)
  (x-bloblet symbol int (listof kx acyclic) int int)
  (x-product (listof (productof (1 symbol) (2 kx)) acyclic) int int)
  (x-extract kx symbol int int)
  (x-sum symbol kx int int)
  (x-tagcase kx (listof (productof (1 symbol) (2 bool) (3 k-names) (4 kx)) acyclic)
             (listof (productof (1 symbol) (2 kx)) acyclic) int int)
  ;; `module`: each item what it is (as `e-module`'s), its names, an
  ;; abstract type's variable (else -1), its types, and its expressions.
  (x-module (listof (productof (1 int) (2 k-names) (3 int) (4 k-ids) (5 (listof kx acyclic)))
                    acyclic)
            int int)
  (x-with symbol kx int int))
(define-type kxs (listof kx acyclic))
(define-type k-item (productof (1 int) (2 k-names) (3 int) (4 k-ids) (5 kxs)))
(define-type k-items (listof k-item acyclic))

;; A type and an effect.
(define-type k-te (productof (1 int) (2 k-eff)))
(define k-te (subr pure (int k-eff) k-te) (lambda (t e) (product (1 t) (2 e))))

;; What checking a program found, or the first error; and, inside, what a
;; computation whose errors are being rewritten produced.
(define-datatype k-result
  (k-ok (listof string acyclic))
  (k-err string int int)
  (k-done k-te))

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

(define k-join (subr (maxeff (read @globals) (read @t)) ((listof string acyclic) string) string)
  (lambda (xs sep)
    (cond ((null? xs) "")
          ((null? (cdr xs)) (car xs))
          (else (k-cat3 (car xs) sep (k-join (cdr xs) sep))))))

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
(define k-set-link (subr kstate (int int) unit)
  (lambda (slot to) (array-set! (get k-tys) slot (ty-link (cons to nil)))))
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
;; The sizes given to `nat` variables of no known size, newest first
;; (`k-name-nat`).
(define k-skolems (ref k-ids @t) (new nil))
;; The same for `nat?`: the variables it has just found no less than 0.
(define k-certified-nats (ref (listof (pairof symbol int @t) acyclic) @t) (new nil))
;; What `length-is?` has just confirmed: a variable, its binding, the length.
(define-type k-cert-len (productof (1 symbol) (2 int) (3 k-size)))
(define k-certified-lengths (ref (listof k-cert-len acyclic) @t) (new nil))
;; The arrow kinds made so far, newest first: each its parameters' kinds and
;; its result's. Kind 100 + n is the nth; kinds below are the
;; base kinds (0 region, 1 effect, 2 type, 3 place, 4 data, 5 size, 6 conv).
(define-type k-arrow-kind (pairof k-ids int @t))
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
;; Each bounded region binder's bound: `(r region p)`, a region that won't
;; outlive `p` (`docs/research/places-and-regions.md`).
(define-type k-bounded (listof (pairof int k-region @t) acyclic))
(define k-bounds (ref k-bounded @t) (new nil))
;; The region and place variables bound around each one's binder, which it
;; won't outlive: the order of lifetimes, by nesting.
(define-type k-nesting (listof (pairof int k-ids @t) acyclic))
(define k-outers (ref k-nesting @t) (new nil))
;; The region and place variables bound around what is being read, by
;; expressions (not types), innermost first.
(define k-lifetimes (ref k-ids @t) (new nil))
;; The regions `letfreeze`s are freezing, and those of them anything has
;; written: data never written is finite.
(define k-freezing (ref k-ids @t) (new nil))
(define k-written (ref k-ids @t) (new nil))
;; The recursive groups whose lambdas are being checked, a call of which
;; there is recursion; and the standard bindings. (Known procedures are
;; kept with the bindings: `k-known`.)
(define-type k-named (listof (pairof symbol int @t) acyclic))
(define k-recursive (ref k-named @t) (new nil))
(define k-std (ref k-named @t) (new nil))
;; Every `define-generative`, newest first: its name, parameters, their
;; variance (0 covariant, 1 contravariant, 2 invariant), and representation.
(define-type k-gen (productof (1 symbol) (2 k-binders) (3 k-ids) (4 int)))
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
;; The lemmas proved so far (`src/lemma.rs`), oldest last: binders, the
;; two sides, the hypotheses, and the definition that proves it (none or
;; one); and the one a `proves` type being read states.
(define-type k-hyps (listof (pairof int int @t) acyclic))
(define-type k-lemma (productof (1 k-binders) (2 int) (3 int) (4 k-hyps) (5 k-named)))
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
(define-type k-regions (listof k-region acyclic))
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
  (lambda (v) (k-nth (get k-dvars) (- (- (get k-ndvars) 1) v))))

;; The base types, made first, in this order, so their indexes are known.
(define k-int int 0)
(define k-bool int 1)
(define k-string int 2)
(define k-unit int 3)
(define k-char int 4)
(define k-f64 int 14)
(define k-symbol int 6)
(define k-void int 16)
(define k-base (ref (listof (pairof symbol int @t) acyclic) @t) (new nil))
(define k-basic (subr (maxeff kstate spin) (string) unit)
  (lambda (name)
    (let* ((s (string->symbol name)) (t (k-ty-new (ty-base s))))
      (set k-base (cons (cons s t) (get k-base))))))

;; Bindings, as lists of them are passed around.
(define-type k-bindings (listof (pairof symbol int @t) acyclic))
(define k-find (subr (maxeff (read @globals) (read @t)) (k-bindings symbol) int)
  (lambda (bs s)
    (cond ((null? bs) -1) ((symbol=? (car (car bs)) s) (cdr (car bs))) (else (k-find (cdr bs) s)))))

;; Value variables in scope: for each name, the types it is bound to,
;; innermost first; and the names bound, newest first, so that a scope is
;; left by unbinding back to a mark (`k-mark`, `k-unbind-to`). A lookup is
;; a table's, not a walk down every binding in scope.
(define-type k-stack (listof int acyclic))
(define k-env (ref (table symbol k-stack @t) @t) (new (make-table symbol-hash symbol=?)))
(define k-trail (ref k-names @t) (new nil))
(define k-depth (ref int @t) (new 0))
;; Whether each binding in `k-env` is of a known procedure: one a `define`,
;; `letrec`, `define-rec`, or a `let` of a `lambda` made. A call of one runs
;; code the checker has seen; a call of anything else might run a closure
;; fetched from the store. By binding, in step with `k-env`, not by name and
;; type, so a parameter that shadows one is not taken for it
;; (`docs/research/soundness-findings.md`, F1).
;; For each name, a flag for each of its bindings in `k-env`, innermost
;; first.
(define-type k-flags (ref (table symbol (listof bool acyclic) @t) @t))
(define k-known k-flags (new (make-table symbol-hash symbol=?)))
;; Whether each binding in `k-env` is a global: one a top-level definition
;; made. Naming one reads it, `(read (globals g))`, when
;; `k-globals-effects` says so, as the language will once every program
;; says what it reads (off until then).
(define k-global k-flags (new (make-table symbol-hash symbol=?)))
(define k-globals-effects (ref bool @t) (new #t))
;; The latent effect of the lambda checked last: for `define*`, what the
;; globals its lambda reads are.
(define k-last-latent (ref k-eff @t) (new nil))
;; For a driver: whether naming a global reads it.
(define check-globals-effects! (subr (maxeff (read @globals) (write @t)) (bool) unit)
  (lambda (on) (set k-globals-effects on)))
;; The type `s` is bound to, or -1.
;; Globals broken by a redefinition (`k-defining`): the name, how many
;; bindings it had then (so which one is broken), and why. A use of a broken
;; binding is an error saying why, until the name is defined again.
(define-type k-break (productof (1 symbol) (2 int) (3 string)))
(define k-broken (ref (listof k-break acyclic) @t) (new nil))
;; How many bindings `s` has now.
(define k-name-depth (subr (maxeff (read @globals) (read @t) spin) (symbol) int)
  (lambda (s) (k-length (table-ref (get k-env) s nil))))
;; Why `s`'s binding now is broken, if it is.
;; Whether `b` breaks the `d`th binding of `s`.
(define k-breaks? (subr (read @globals) (k-break symbol int) bool)
  (lambda (b s d) (and (symbol=? (extract b 1) s) (= (extract b 2) d))))
(define k-broken-why (subr (maxeff kreads spin) (symbol) k-strings)
  (lambda (s)
    (let ((d (k-name-depth s)))
      (letrec ((go (subr (read @globals) ((listof k-break acyclic)) k-strings)
                 (lambda (bs)
                   (cond ((null? bs) nil)
                         ((k-breaks? (car bs) s d) (the k-strings (cons (extract (car bs) 3) nil)))
                         (else (go (cdr bs)))))))
        (go (get k-broken))))))
;; While a module read from a file is checked (`load-module`, M7): how many
;; bindings there were as it began, of which it sees only the standard
;; ones; -1 otherwise. And the standard description names.
(define k-hide-mark (ref int @t) (new -1))
(define k-std-dscope (ref k-scope @t) (new nil))
;; How many of the newest `n` names bound, `ns`, are `s`.
(define k-bound-since (subr (maxeff (read @globals) (read @t) spin) (k-names symbol int) int)
  (lambda (ns s n)
    (cond ((or (null? ns) (<= n 0)) 0)
          ((symbol=? (car ns) s) (+ 1 (k-bound-since (cdr ns) s (- n 1))))
          (else (k-bound-since (cdr ns) s (- n 1))))))
;; What `s` is where it is used: its innermost binding; none, if that is
;; broken. While a module read from a file is checked, a binding made
;; before it began only if it is a standard one.
(define k-lookup (subr (maxeff (read @globals) (read @t) spin) (symbol) int)
  (lambda (s)
    (let ((st (table-ref (get k-env) s nil)) (mark (get k-hide-mark)))
      (cond ((or (null? st) (not (null? (k-broken-why s)))) -1)
            ((or (< mark 0) (> (k-bound-since (get k-trail) s (- (get k-depth) mark)) 0)) (car st))
            (else (k-find (get k-std) s))))))
;; The same, broken or not.
(define k-lookup-raw (subr (maxeff (read @globals) (read @t) spin) (symbol) int)
  (lambda (s) (let ((st (table-ref (get k-env) s nil))) (if (null? st) -1 (car st)))))
;; What an unbound name's use says: why, if it is broken.
(define k-unbound (subr (maxeff (read @globals) (read @t) (alloc @t) spin) (symbol) string)
  (lambda (s)
    (let ((why (k-broken-why s)) (n (symbol->string s)))
      (if (null? why)
          (k-cat3 "unbound variable `" n "`")
          (k-cat5 "`" n "` is broken, " (car why) ": define it again to use it")))))
;; A flag, off, for a new innermost binding of `s`.
(define k-push-flag (subr (maxeff kstate spin) (k-flags symbol) unit)
  (lambda (flags s)
    (table-set! (get flags) s (the (listof bool acyclic) (cons #f (table-ref (get flags) s nil))))))
(define k-bind (subr (maxeff kstate spin) (symbol int) unit)
  (lambda (s t)
    (begin
      (table-set! (get k-env) s (cons t (table-ref (get k-env) s nil)))
      (k-push-flag k-known s)
      (k-push-flag k-global s)
      (set k-trail (cons s (get k-trail)))
      (set k-depth (+ (get k-depth) 1)))))
(define k-mark (subr (maxeff (read @globals) (read @t)) () int) (lambda () (get k-depth)))
(define k-unbind-to (subr (maxeff kstate spin) (int) unit)
  (lambda (m)
    (if (<= (get k-depth) m)
        #u
        (let ((s (car (get k-trail))))
          (begin
            (table-set! (get k-env) s (cdr (table-ref (get k-env) s nil)))
            (table-set! (get k-known) s (cdr (table-ref (get k-known) s nil)))
            (table-set! (get k-global) s (cdr (table-ref (get k-global) s nil)))
            (set k-trail (cdr (get k-trail)))
            (set k-depth (- (get k-depth) 1))
            (k-unbind-to m))))))

;; Note the binding of `n` that many from the innermost as known.
(define k-set-nth-true (subr (read @globals) ((listof bool acyclic) int) (listof bool acyclic))
  (lambda (bs i)
    (cond ((null? bs) bs)
          ((= i 0) (the (listof bool acyclic) (cons #t (cdr bs))))
          (else (the (listof bool acyclic) (cons (car bs) (k-set-nth-true (cdr bs) (- i 1))))))))
(define k-note-known (subr (maxeff kstate spin) (symbol int) unit)
  (lambda (n i) (table-set! (get k-known) n (k-set-nth-true (table-ref (get k-known) n nil) i))))
;; Whether the binding `n` names is of a known procedure.
(define k-known? (subr (maxeff (read @globals) (read @t) spin) (symbol) bool)
  (lambda (n) (let ((st (table-ref (get k-known) n nil))) (and (not (null? st)) (car st)))))
;; Note the innermost binding of `n` as a global.
(define k-note-global (subr (maxeff kstate spin) (symbol) unit)
  (lambda (n) (table-set! (get k-global) n (k-set-nth-true (table-ref (get k-global) n nil) 0))))
;; Bind `n`, at top level, to a value of type `t`: a global.
(define k-bind-global (subr (maxeff kstate spin) (symbol int) unit)
  (lambda (n t) (begin (k-bind n t) (k-note-global n))))
;; Whether the binding `n` names is a global's.
(define k-global? (subr (maxeff (read @globals) (read @t) spin) (symbol) bool)
  (lambda (n) (let ((st (table-ref (get k-global) n nil))) (and (not (null? st)) (car st)))))

;; Description names in scope, innermost first.
(define-type k-scope (listof (pairof symbol k-ds @t) acyclic))
(define k-dscope (ref k-scope @t) (new nil))
(define k-find-desc (subr (maxeff kreads (alloc @t)) (k-scope symbol) (listof k-ds acyclic))
  (lambda (ds s)
    (cond ((null? ds) nil)
          ((symbol=? (car (car ds)) s) (cons (cdr (car ds)) nil))
          (else (k-find-desc (cdr ds) s)))))
;; What `s` means as a description: none or one.
(define k-lookup-desc (subr (maxeff kreads (alloc @t)) (symbol) (listof k-ds acyclic))
  (lambda (s) (k-find-desc (get k-dscope) s)))
(define k-push-desc (subr kstate (symbol k-ds) unit)
  (lambda (n d) (set k-dscope (cons (cons n d) (get k-dscope)))))

;; How many fresh regions have been made, for naming the next.
(define k-fresh (ref int @t) (new 0))
(define k-fresh-region (subr kstate (string) k-region)
  (lambda (base)
    (let ((n (+ (get k-fresh) 1)))
      (begin (set k-fresh n) (r-fresh n (k-cat3 base "." (int->string n)))))))

;; How deep in abbreviations' expansions reading is.
(define k-expanding (ref int @t) (new 0))

;; What checking proved that running needs: each `extract`'s field, by
;; position, keyed by where the `extract` is. Only the product's type says.
(define-type k-fact (productof (1 int) (2 int) (3 int)))
(define-type k-facts (listof k-fact acyclic))
(define k-extracts (ref k-facts @t) (new nil))
;; Each expression synthesized: where it starts and ends, and a summary of
;; its effect for a compiler, each a stronger claim on what the code may do
;; than the one before, so that the greater of two is the safe one: 0 pure
;; (no atom at all, so no `spin` either); 1 reads only; 2 anything else; 3
;; anything else that may also keep its continuation for later, write a
;; global, or do what an effect variable stands for, which a global's value
;; may change across. Newest first. The Rust checker's `effect_summaries` is
;; the same.
(define k-effect-notes (ref k-facts @t) (new nil))
;; An effect note as `checked-extracts` gives it: its summary n as -1 - n.
(define k-note-as-fact (subr (read @globals) (k-fact) k-fact)
  (lambda (n) (product (1 (extract n 1)) (2 (extract n 2)) (3 (- -1 (extract n 3))))))
(define k-add-effect-facts (subr (read @globals) (k-facts k-facts) k-facts)
  (lambda (notes acc)
    (if (null? notes)
        acc
        (k-add-effect-facts (cdr notes) (the k-facts (cons (k-note-as-fact (car notes)) acc))))))
;; What checking found, for a compiler: each `extract`'s field, `(a b i)`;
;; and each expression's effect summary (`k-effect-notes`), `(a b n)` with n
;; negative, the summary -1 - n.
(define checked-extracts (subr kreads () k-facts)
  (lambda () (k-add-effect-facts (get k-effect-notes) (get k-extracts))))
(define checked-effects (subr kreads () k-facts) (lambda () (get k-effect-notes)))
;; Whether `r` is a global's binding, or every global's.
(define k-globals-region? (subr pure (k-region) bool)
  (lambda (r) (tagcase r (r-global (g) #t) (r-globals () #t) (else y #f))))
;; Whether `e` may keep its continuation for later, write a global, or do
;; what an effect variable stands for.
(define k-disrupts? (subr (read @globals) (k-eff) bool)
  (lambda (e)
    (and (not (null? e))
         (or (tagcase (car e)
               (a-comefrom (r) #t)
               (a-var (v) #t)
               (a-app (v ds) #t)
               (a-write (r) (k-globals-region? r))
               (else y #f))
             (k-disrupts? (cdr e))))))
;; Whether `a` reads.
(define k-read-atom? (subr pure (k-atom) bool)
  (lambda (a) (tagcase a (a-read (r) #t) (else y #f))))
(define k-reads-only? (subr (read @globals) (k-eff) bool)
  (lambda (e) (or (null? e) (and (k-read-atom? (car e)) (k-reads-only? (cdr e))))))
(define k-summary (subr (read @globals) (k-eff) int)
  (lambda (e) (cond ((null? e) 0) ((k-reads-only? e) 1) ((k-disrupts? e) 3) (else 2))))

;; Each `with` checked, where it is, and its module's values' names, newest
;; first: a `with`'s body sees them, once checking has found them.
(define-type k-with-noted (productof (1 int) (2 int) (3 k-names)))
(define-type k-with-list (listof k-with-noted acyclic))
(define k-with-vals (ref k-with-list @t) (new nil))
(define k-with-names-in (subr (maxeff (read @globals) (read @t)) (k-with-list int int) k-names)
  (lambda (ws a b)
    (cond ((null? ws) nil)
          ((and (= (extract (car ws) 1) a) (= (extract (car ws) 2) b)) (extract (car ws) 3))
          (else (k-with-names-in (cdr ws) a b)))))
(define k-with-names (subr (maxeff (read @globals) (read @t)) (int int) k-names)
  (lambda (a b) (k-with-names-in (get k-with-vals) a b)))
;; Each module given where a type of fewer values, or the same in another
;; order, is wanted (`k-reshape-at`): where, and for each value that type
;; has, its position in the module given. Made into a module of that layout.
(define-type k-reshaped (productof (1 int) (2 int) (3 k-ids)))
(define-type k-reshape-list (listof k-reshaped acyclic))
(define k-reshapes (ref k-reshape-list @t) (new nil))
;; For a driver: the same as another checker found them.
(define checked-reshapes! (subr (maxeff (read @globals) (write @t)) (k-reshape-list) unit)
  (lambda (rs) (set k-reshapes rs)))
;; For a driver: what `with`s another checker saw, as `k-with-vals` keeps
;; them, for a compiler given that checker's facts.
(define checked-withs! (subr (maxeff (read @globals) (write @t)) (k-with-list) unit)
  (lambda (ws) (set k-with-vals ws)))
;; The type variables made for modules' abstract types as each module was
;; bound (`k-name-module`): not forgotten, but kept from leaving.
(define k-module-vars (ref k-ids @t) (new nil))
;; While a type's `select`s are resolved (`k-resolve-selects`): what each
;; is, `(m t)` and the type; none otherwise.
(define-type k-selected (productof (1 symbol) (2 symbol) (3 int)))
(define-type k-selects (listof k-selected acyclic))
(define k-select-map (ref k-selects @t) (new nil))
(define k-select-in (subr (maxeff (read @globals) (read @t)) (k-selects symbol symbol int) int)
  (lambda (ss m n t)
    (cond ((null? ss) t)
          ((and (symbol=? (extract (car ss) 1) m) (symbol=? (extract (car ss) 2) n))
           (extract (car ss) 3))
          (else (k-select-in (cdr ss) m n t)))))
;; What `(select m n)`, node `t`, is while selects are resolved; else `t`.
(define k-select-of (subr (maxeff (read @globals) (read @t)) (symbol symbol int) int)
  (lambda (m n t) (k-select-in (get k-select-map) m n t)))
;; While a dependent procedure's parameters are given (`k-instantiate-params`):
;; what each `(select $k n)` is, `(k n)` and the type; none otherwise.
(define-type k-param-given (productof (1 int) (2 symbol) (3 int)))
(define-type k-params-given (listof k-param-given acyclic))
(define k-param-map (ref k-params-given @t) (new nil))
(define k-param-in (subr (maxeff (read @globals) (read @t)) (k-params-given int symbol int) int)
  (lambda (ps k n t)
    (cond ((null? ps) t)
          ((and (= (extract (car ps) 1) k) (symbol=? (extract (car ps) 2) n)) (extract (car ps) 3))
          (else (k-param-in (cdr ps) k n t)))))
;; What `(select $k n)`, node `t`, is while parameters are given; else `t`.
(define k-param-sel-of (subr (maxeff (read @globals) (read @t)) (int symbol int) int)
  (lambda (k n t) (k-param-in (get k-param-map) k n t)))
;; A `subr` type's parameter types and result, read (`check-modules.fx`'s
;; `k-read-params`, which sets this): its types, the result last.
(define k-parse-params (ref (subr (maxeff checks spin) ((listof syn acyclic) syn) k-ids) @t)
  (new (lambda (ps r) nil)))
;; `ts` but its last; and its last (-1 if none).
(define k-ids-but-last (subr (maxeff (read @globals) (alloc @t) spin) (k-ids) k-ids)
  (lambda (ts) (if (or (null? ts) (null? (cdr ts))) nil (cons (car ts) (k-ids-but-last (cdr ts))))))
(define k-ids-last (subr (maxeff (read @globals) spin) (k-ids) int)
  (lambda (ts) (cond ((null? ts) -1) ((null? (cdr ts)) (car ts)) (else (k-ids-last (cdr ts))))))

;;; ------------------------------------------------------------ effects

;; Booleans in order, false first.
(define k-bool-cmp (subr (read @globals) (bool bool) int)
  (lambda (f g) (k-int-cmp (if f 1 0) (if g 1 0))))
(define k-region-rank (subr pure (k-region) int)
  (lambda (r)
    (tagcase r
      (r-const (n) 0) (r-fresh (i n) 1) (r-var (v) 2) (r-frozen (p f) 3) (r-heap () 4)
      (r-global (g) 5) (r-globals () 6))))
(define k-region-cmp (subr (maxeff (read @globals) spin) (k-region k-region) int)
  (lambda (r s)
    (let ((c (k-int-cmp (k-region-rank r) (k-region-rank s))))
      (if (= c 0)
          (tagcase r
            (r-const (n) (tagcase s (r-const (m) (symbol-compare n m)) (else y 0)))
            (r-fresh (i n) (tagcase s (r-fresh (j m) (k-int-cmp i j)) (else y 0)))
            (r-var (v) (tagcase s (r-var (w) (k-int-cmp v w)) (else y 0)))
            (r-frozen (p f)
              (tagcase s
                (r-frozen (q g) (let ((c (k-int-cmp p q))) (if (= c 0) (k-bool-cmp f g) c)))
                (else y 0)))
            (r-heap () 0)
            (r-global (g) (tagcase s (r-global (h) (symbol-compare g h)) (else y 0)))
            (r-globals () 0))
          c))))
(define k-region=? (subr (maxeff (read @globals) spin) (k-region k-region) bool)
  (lambda (r s) (= (k-region-cmp r s) 0)))

(define k-atom-rank (subr pure (k-atom) int)
  (lambda (a)
    (tagcase a
      (a-read (r) 0) (a-write (r) 1) (a-alloc (r) 2)
      (a-goto (r) 3) (a-comefrom (r) 4) (a-await (r) 5)
      (a-spin () 6) (a-var (v) 7) (a-app (v ds) 8))))
;; The atom's region; a variable's is none, shown as a binder -1.
(define k-atom-region (subr (read @globals) (k-atom) k-region)
  (lambda (a)
    (tagcase a
      (a-read (r) r) (a-write (r) r) (a-alloc (r) r)
      (a-goto (r) r) (a-comefrom (r) r) (a-await (r) r)
      (a-spin () (r-var -1)) (a-var (v) (r-var -1)) (a-app (v ds) (r-var -1)))))
(define k-has-region? (subr (read @globals) (k-atom) bool) (lambda (a) (< (k-atom-rank a) 6)))
;; The effect variable an atom is, or -1.
(define k-atom-var (subr pure (k-atom) int)
  (lambda (a) (tagcase a (a-var (v) v) (else y -1))))
;; What orders two atoms of one rank with no region: a variable's number,
;; or an effect application's.
(define k-atom-key (subr pure (k-atom) int)
  (lambda (a) (tagcase a (a-var (v) v) (a-app (v ds) v) (else y -1))))
;; A convention as a number: one of FX-26's own, or its binder.
(define k-conv-code (subr pure (k-conv) int)
  (lambda (c) (tagcase c (cv-cellular () -1) (cv-native () -2) (cv-fx () -3) (cv-var (v) v))))
;; What an effect application was given; none for any other atom.
(define k-atom-args (subr pure (k-atom) (listof k-desc acyclic))
  (lambda (a) (tagcase a (a-app (v ds) ds) (else y nil))))
;; Descriptions given an effect function, ranked by kind.
(define k-earg-rank (subr pure (k-desc) int)
  (lambda (d) (tagcase d (dr (r) 0) (de (e) 1) (dz (z) 2) (dc (c) 3) (else y 4))))
(define k-terms-cmp (subr (maxeff (read @globals) spin) (k-terms k-terms) int)
  (lambda (ts us)
    (cond ((null? ts) (if (null? us) 0 -1))
          ((null? us) 1)
          (else
           (let ((c (k-int-cmp (car (car ts)) (car (car us)))))
             (cond ((not (= c 0)) c)
                   ((not (= (cdr (car ts)) (cdr (car us))))
                    (k-int-cmp (cdr (car ts)) (cdr (car us))))
                   (else (k-terms-cmp (cdr ts) (cdr us)))))))))
;; Sizes in order: `finite` first, then by constant and terms.
(define k-size-cmp (subr (maxeff (read @globals) spin) (k-size k-size) int)
  (lambda (m n)
    (tagcase m
      (sz-finite () (tagcase n (sz-finite () 0) (else y -1)))
      (sz-lin (k ts)
        (tagcase n
          (sz-finite () 1)
          (sz-lin (j us)
            (let ((c (k-int-cmp k j)))
              (if (= c 0) (k-terms-cmp ts us) c))))))))
;; Atoms in order: by rank; then by region, or by variable, an effect
;; application by what it was given after its variable.
(define-rec
  (k-atom-cmp (subr (maxeff (read @globals) spin) (k-atom k-atom) int)
    (lambda (a b)
      (let ((c (k-int-cmp (k-atom-rank a) (k-atom-rank b))))
        (cond ((not (= c 0)) c)
              ((k-has-region? a) (k-region-cmp (k-atom-region a) (k-atom-region b)))
              (else
               (let ((d (k-int-cmp (k-atom-key a) (k-atom-key b))))
                 (if (= d 0) (k-eargs-cmp (k-atom-args a) (k-atom-args b)) d)))))))
  (k-eargs-cmp (subr (maxeff (read @globals) spin) (k-descs k-descs) int)
    (lambda (xs ys)
      (cond ((null? xs) (if (null? ys) 0 -1))
            ((null? ys) 1)
            (else
             (let ((c (k-earg-cmp (car xs) (car ys))))
               (if (= c 0) (k-eargs-cmp (cdr xs) (cdr ys)) c))))))
  (k-earg-cmp (subr (maxeff (read @globals) spin) (k-desc k-desc) int)
    (lambda (x y)
      (let ((c (k-int-cmp (k-earg-rank x) (k-earg-rank y))))
        (if (not (= c 0))
            c
            (tagcase x
              (dr (r) (tagcase y (dr (s) (k-region-cmp r s)) (else z 0)))
              (de (e) (tagcase y (de (f) (k-effs-cmp e f)) (else z 0)))
              (dz (m) (tagcase y (dz (n) (k-size-cmp m n)) (else z 0)))
              (dc (a) (tagcase y (dc (b) (k-int-cmp (k-conv-code a) (k-conv-code b))) (else z 0)))
              (else z 0))))))
  (k-effs-cmp (subr (maxeff (read @globals) spin) (k-eff k-eff) int)
    (lambda (e f)
      (cond ((null? e) (if (null? f) 0 -1))
            ((null? f) 1)
            (else
             (let ((c (k-atom-cmp (car e) (car f))))
               (if (= c 0) (k-effs-cmp (cdr e) (cdr f)) c)))))))
(define k-atom-with (subr (read @globals) (k-atom k-region) k-atom)
  (lambda (a r)
    (tagcase a
      (a-read (x) (a-read r)) (a-write (x) (a-write r)) (a-alloc (x) (a-alloc r))
      (a-goto (x) (a-goto r)) (a-comefrom (x) (a-comefrom r)) (a-await (x) (a-await r))
      (a-spin () a) (a-var (v) a) (a-app (v ds) a))))
;; Whether `a` comes before `b`, and whether they are one atom.
(define k-atom<? (subr (maxeff (read @globals) spin) (k-atom k-atom) bool)
  (lambda (a b) (< (k-atom-cmp a b) 0)))
(define k-atom=? (subr (maxeff (read @globals) spin) (k-atom k-atom) bool)
  (lambda (a b) (= (k-atom-cmp a b) 0)))

(define k-insert (subr (maxeff (read @globals) (read @t) (alloc @t) spin) (k-atom k-eff) k-eff)
  (lambda (a e)
    (if (null? e)
        (cons a nil)
        (let ((c (k-atom-cmp a (car e))))
          (cond ((< c 0) (cons a e)) ((= c 0) e) (else (cons (car e) (k-insert a (cdr e)))))))))
(define k-union-each (subr (maxeff (read @globals) (read @t) (alloc @t) spin) (k-eff k-eff) k-eff)
  (lambda (x y) (if (null? x) y (k-union-each (cdr x) (k-insert (car x) y)))))
(define k-sorted? (subr (maxeff kreads spin) (k-eff) bool)
  (lambda (e)
    (or (null? e) (null? (cdr e)) (and (k-atom<? (car e) (car (cdr e))) (k-sorted? (cdr e))))))
(define k-merge (subr (maxeff (read @globals) (read @t) (alloc @t) spin) (k-eff k-eff) k-eff)
  (lambda (x y)
    (cond ((null? x) y)
          ((null? y) x)
          (else
           (let ((c (k-atom-cmp (car x) (car y))))
             (cond ((< c 0) (cons (car x) (k-merge (cdr x) y)))
                   ((= c 0) (cons (car x) (k-merge (cdr x) (cdr y))))
                   (else (cons (car y) (k-merge x (cdr y))))))))))
;; `x` and `y` together, sorted as `k-insert` keeps an effect: a merge, when
;; `x` is sorted too (as effects made here are), else one atom at a time.
(define k-union (subr (maxeff (read @globals) (read @t) (alloc @t) spin) (k-eff k-eff) k-eff)
  (lambda (x y) (if (k-sorted? x) (k-merge x y) (k-union-each x y))))
(define k-contains? (subr (maxeff kreads spin) (k-eff k-atom) bool)
  (lambda (e a) (cond ((null? e) #f) ((k-atom=? (car e) a) #t) (else (k-contains? (cdr e) a)))))
;; Whether `a` is in `e`, or, reading or writing one global, `e` does so to
;; `@globals`.
(define k-covered? (subr (maxeff (read @globals) (read @t) spin) (k-eff k-atom) bool)
  (lambda (e a)
    (or (k-contains? e a)
        (tagcase a
          (a-read (r) (tagcase r (r-global (g) (k-contains? e (a-read (r-globals)))) (else y #f)))
          (a-write (r) (tagcase r (r-global (g) (k-contains? e (a-write (r-globals)))) (else y #f)))
          (else y #f)))))
(define k-within-each? (subr (maxeff (read @globals) (read @t) spin) (k-eff k-eff) bool)
  (lambda (x y) (or (null? x) (and (k-covered? y (car x)) (k-within-each? (cdr x) y)))))
;; `k-within?` of sorted effects, `rg` and `wg` whether `y` reads and writes
;; `@globals`, which cover reading and writing any one global.
(define k-within-sorted? (subr (maxeff (read @globals) (read @t) spin) (k-eff k-eff bool bool) bool)
  (lambda (x y rg wg)
    (cond ((null? x) #t)
          ((tagcase (car x)
             (a-read (r) (and rg (tagcase r (r-global (g) #t) (else z #f))))
             (a-write (r) (and wg (tagcase r (r-global (g) #t) (else z #f))))
             (else z #f))
           (k-within-sorted? (cdr x) y rg wg))
          ((null? y) #f)
          (else
           (let ((c (k-atom-cmp (car x) (car y))))
             (cond ((< c 0) #f)
                   ((= c 0) (k-within-sorted? (cdr x) (cdr y) rg wg))
                   (else (k-within-sorted? x (cdr y) rg wg))))))))
;; Whether every atom of `x` is covered by `y` (`k-covered?`): both sorted,
;; as effects made here are, by one walk of the two; else atom by atom.
(define k-within? (subr (maxeff (read @globals) (read @t) spin) (k-eff k-eff) bool)
  (lambda (x y)
    (if (and (k-sorted? x) (k-sorted? y))
        (let ((rg (k-contains? y (a-read (r-globals)))) (wg (k-contains? y (a-write (r-globals)))))
          (k-within-sorted? x y rg wg))
        (k-within-each? x y))))
(define k-eff=? (subr (maxeff kreads spin) (k-eff k-eff) bool)
  (lambda (x y) (and (k-within? x y) (k-within? y x))))
(define k-one (subr (alloc @t) (k-atom) k-eff) (lambda (a) (cons a nil)))
(define k-allocates? (subr (maxeff (read @globals) (read @t)) (k-eff) bool)
  (lambda (e) (cond ((null? e) #f) ((= (k-atom-rank (car e)) 2) #t) (else (k-allocates? (cdr e))))))
