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

;; A module (`TODO.md` §34: the front end into modules, a file at a time);
;; what other files use re-exported after it.
(define check-types-module (module
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
;; The same, a table: each standard name's binding, newest (`k-bind-std`).
(define k-std-table (ref (table symbol int @t) @t) (new (make-table symbol-hash symbol=?)))
;; The standard binding of `s`, -1 if none.
(define k-std-type (subr (maxeff (read @globals) (read @t)) (symbol) int)
  (lambda (s) (table-ref (get k-std-table) s -1)))
;; Whether binding `t` of `s` is the standard one.
(define k-std-binding? (subr (maxeff (read @globals) (read @t)) (symbol int) bool)
  (lambda (s t) (and (>= t 0) (= (k-std-type s) t))))
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


;;; ------------------------------------------------------------ effects

;; Booleans in order, false first.
(define k-bool-cmp (subr (read @globals) (bool bool) int)
  (lambda (f g) (k-int-cmp (if f 1 0) (if g 1 0))))
(define k-region-rank (subr pure (k-region) int)
  (lambda (r)
    (tagcase r
      (r-const (n) 0) (r-fresh (i n) 1) (r-var (v) 2) (r-frozen (p f) 3) (r-heap () 4)
      (r-global (g) 5) (r-globals () 6))))
;; Two names in order: the same symbol at once, else by their text.
(define k-name-cmp (subr pure (symbol symbol) int)
  (lambda (n m) (if (symbol=? n m) 0 (symbol-compare n m))))
(define k-region-cmp (subr (maxeff (read @globals) spin) (k-region k-region) int)
  (lambda (r s)
    (let ((c (k-int-cmp (k-region-rank r) (k-region-rank s))))
      (if (= c 0)
          (tagcase r
            (r-const (n) (tagcase s (r-const (m) (k-name-cmp n m)) (else y 0)))
            (r-fresh (i n) (tagcase s (r-fresh (j m) (k-int-cmp i j)) (else y 0)))
            (r-var (v) (tagcase s (r-var (w) (k-int-cmp v w)) (else y 0)))
            (r-frozen (p f)
              (tagcase s
                (r-frozen (q g) (let ((c (k-int-cmp p q))) (if (= c 0) (k-bool-cmp f g) c)))
                (else y 0)))
            (r-heap () 0)
            (r-global (g) (tagcase s (r-global (h) (k-name-cmp g h)) (else y 0)))
            (r-globals () 0))
          c))))
;; The same as `(= (k-region-cmp r s) 0)`, the names compared as symbols:
;; one comparison, where the order compares their names.
(define k-region=? (subr (maxeff (read @globals) spin) (k-region k-region) bool)
  (lambda (r s)
    (tagcase r
      (r-const (n) (tagcase s (r-const (m) (symbol=? n m)) (else y #f)))
      (r-fresh (i n) (tagcase s (r-fresh (j m) (= i j)) (else y #f)))
      (r-var (v) (tagcase s (r-var (w) (= v w)) (else y #f)))
      (r-frozen (p f) (tagcase s (r-frozen (q g) (and (= p q) (bool=? f g))) (else y #f)))
      (r-heap () (tagcase s (r-heap () #t) (else y #f)))
      (r-global (g) (tagcase s (r-global (h) (symbol=? g h)) (else y #f)))
      (r-globals () (tagcase s (r-globals () #t) (else y #f))))))

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
))

(define-effect kstate (select check-types-module kstate))
(define-effect checks (select check-types-module checks))
(define-effect kreads (select check-types-module kreads))
(define-effect kbuilds (select check-types-module kbuilds))
(define-type k-region (select check-types-module k-region))
(define-type k-atom (select check-types-module k-atom))
(define-type k-eff (select check-types-module k-eff))
(define-type k-vsub (select check-types-module k-vsub))
(define-type k-ids (select check-types-module k-ids))
(define-type k-binders (select check-types-module k-binders))
(define-type k-parts (select check-types-module k-parts))
(define-type k-names (select check-types-module k-names))
(define-type k-strings (select check-types-module k-strings))
(define-type k-conv (select check-types-module k-conv))
(define-type k-terms (select check-types-module k-terms))
(define-type k-size (select check-types-module k-size))
(define-type k-desc (select check-types-module k-desc))
(define-type k-descs (select check-types-module k-descs))
(define-type k-ty (select check-types-module k-ty))
(define-type k-map (select check-types-module k-map))
(define-type k-ds (select check-types-module k-ds))
(define-type kx (select check-types-module kx))
(define-type kxs (select check-types-module kxs))
(define-type k-item (select check-types-module k-item))
(define-type k-items (select check-types-module k-items))
(define-type k-te (select check-types-module k-te))
(define k-te (with check-types-module k-te))
(define-type k-result (select check-types-module k-result))
(define k-tag (with check-types-module k-tag))
(define k-fail (with check-types-module k-fail))
(define k-cat3 (with check-types-module k-cat3))
(define k-cat4 (with check-types-module k-cat4))
(define k-cat5 (with check-types-module k-cat5))
(define k-quote (with check-types-module k-quote))
(define k-join (with check-types-module k-join))
(define k-find-sub (with check-types-module k-find-sub))
(define k-length (with check-types-module k-length))
(define k-nth (with check-types-module k-nth))
(define k-has-name? (with check-types-module k-has-name?))
(define k-has-id? (with check-types-module k-has-id?))
(define k-tys (with check-types-module k-tys))
(define k-ntys (with check-types-module k-ntys))
(define k-copy-array (with check-types-module k-copy-array))
(define k-ty-new (with check-types-module k-ty-new))
(define k-raw (with check-types-module k-raw))
(define k-resolve (with check-types-module k-resolve))
(define k-get (with check-types-module k-get))
(define k-set-link (with check-types-module k-set-link))
(define k-slot (with check-types-module k-slot))
(define k-new-epoch (with check-types-module k-new-epoch))
(define k-visit? (with check-types-module k-visit?))
(define k-dvars (with check-types-module k-dvars))
(define k-ndvars (with check-types-module k-ndvars))
(define k-places (with check-types-module k-places))
(define k-datas (with check-types-module k-datas))
(define k-certified (with check-types-module k-certified))
(define k-skolems (with check-types-module k-skolems))
(define k-certified-nats (with check-types-module k-certified-nats))
(define-type k-cert-len (select check-types-module k-cert-len))
(define k-certified-lengths (with check-types-module k-certified-lengths))
(define k-arrow (with check-types-module k-arrow))
(define k-arrow-parts (with check-types-module k-arrow-parts))
(define k-arrow-kind? (with check-types-module k-arrow-kind?))
(define k-arrow-result (with check-types-module k-arrow-result))
(define k-arrow-params (with check-types-module k-arrow-params))
(define k-binder-kinds (with check-types-module k-binder-kinds))
(define k-arrow-vars (with check-types-module k-arrow-vars))
(define k-abstract-funs (with check-types-module k-abstract-funs))
(define k-new-dvar-of (with check-types-module k-new-dvar-of))
(define k-data-var? (with check-types-module k-data-var?))
(define k-place-var? (with check-types-module k-place-var?))
(define k-dvar-kind (with check-types-module k-dvar-kind))
(define k-bounds (with check-types-module k-bounds))
(define k-outers (with check-types-module k-outers))
(define k-lifetimes (with check-types-module k-lifetimes))
(define k-freezing (with check-types-module k-freezing))
(define k-written (with check-types-module k-written))
(define-type k-named (select check-types-module k-named))
(define k-recursive (with check-types-module k-recursive))
(define k-std (with check-types-module k-std))
(define k-std-table (with check-types-module k-std-table))
(define k-std-type (with check-types-module k-std-type))
(define k-std-binding? (with check-types-module k-std-binding?))
(define-type k-gen (select check-types-module k-gen))
(define k-gens (with check-types-module k-gens))
(define k-ngens (with check-types-module k-ngens))
(define k-gen-of (with check-types-module k-gen-of))
(define k-transparent (with check-types-module k-transparent))
(define k-inside (with check-types-module k-inside))
(define k-conversions (with check-types-module k-conversions))
(define-type k-hyps (select check-types-module k-hyps))
(define-type k-lemma (select check-types-module k-lemma))
(define k-lemmas (with check-types-module k-lemmas))
(define k-pending-lemma (with check-types-module k-pending-lemma))
(define k-binder-has? (with check-types-module k-binder-has?))
(define k-gen-param? (with check-types-module k-gen-param?))
(define k-desc-types (with check-types-module k-desc-types))
(define-type k-regions (select check-types-module k-regions))
(define k-desc-regions (with check-types-module k-desc-regions))
(define k-gen-region? (with check-types-module k-gen-region?))
(define k-spin-why (with check-types-module k-spin-why))
(define k-named-has? (with check-types-module k-named-has?))
(define k-bound-of (with check-types-module k-bound-of))
(define k-outer-of (with check-types-module k-outer-of))
(define k-set-outer (with check-types-module k-set-outer))
(define k-dvar-name (with check-types-module k-dvar-name))
(define k-region=? (with check-types-module k-region=?))
(define k-atom-rank (with check-types-module k-atom-rank))
(define k-atom-region (with check-types-module k-atom-region))
(define k-has-region? (with check-types-module k-has-region?))
(define k-atom-var (with check-types-module k-atom-var))
(define k-conv-code (with check-types-module k-conv-code))
(define k-atom-with (with check-types-module k-atom-with))
(define k-insert (with check-types-module k-insert))
(define k-union (with check-types-module k-union))
(define k-contains? (with check-types-module k-contains?))
(define k-covered? (with check-types-module k-covered?))
(define k-within? (with check-types-module k-within?))
(define k-eff=? (with check-types-module k-eff=?))
(define k-one (with check-types-module k-one))
(define r-const (with check-types-module r-const))
(define r-fresh (with check-types-module r-fresh))
(define r-var (with check-types-module r-var))
(define r-frozen (with check-types-module r-frozen))
(define r-heap (with check-types-module r-heap))
(define r-global (with check-types-module r-global))
(define r-globals (with check-types-module r-globals))
(define a-read (with check-types-module a-read))
(define a-write (with check-types-module a-write))
(define a-alloc (with check-types-module a-alloc))
(define a-goto (with check-types-module a-goto))
(define a-comefrom (with check-types-module a-comefrom))
(define a-await (with check-types-module a-await))
(define a-spin (with check-types-module a-spin))
(define a-var (with check-types-module a-var))
(define a-app (with check-types-module a-app))
(define cv-cellular (with check-types-module cv-cellular))
(define cv-native (with check-types-module cv-native))
(define cv-fx (with check-types-module cv-fx))
(define cv-var (with check-types-module cv-var))
(define sz-finite (with check-types-module sz-finite))
(define sz-lin (with check-types-module sz-lin))
(define dr (with check-types-module dr))
(define de (with check-types-module de))
(define dt (with check-types-module dt))
(define dz (with check-types-module dz))
(define dc (with check-types-module dc))
(define df (with check-types-module df))
(define ty-base (with check-types-module ty-base))
(define ty-void (with check-types-module ty-void))
(define ty-var (with check-types-module ty-var))
(define ty-subr (with check-types-module ty-subr))
(define ty-poly (with check-types-module ty-poly))
(define ty-ref (with check-types-module ty-ref))
(define ty-pair (with check-types-module ty-pair))
(define ty-tag (with check-types-module ty-tag))
(define ty-comp (with check-types-module ty-comp))
(define ty-markkey (with check-types-module ty-markkey))
(define ty-product (with check-types-module ty-product))
(define ty-sum (with check-types-module ty-sum))
(define ty-array (with check-types-module ty-array))
(define ty-icell (with check-types-module ty-icell))
(define ty-place (with check-types-module ty-place))
(define ty-bloblet (with check-types-module ty-bloblet))
(define ty-link (with check-types-module ty-link))
(define ty-named (with check-types-module ty-named))
(define ty-nlist (with check-types-module ty-nlist))
(define ty-nat (with check-types-module ty-nat))
(define ty-module (with check-types-module ty-module))
(define ty-select (with check-types-module ty-select))
(define ty-param (with check-types-module ty-param))
(define ty-lam (with check-types-module ty-lam))
(define ty-app (with check-types-module ty-app))
(define ds-gen (with check-types-module ds-gen))
(define ds-size (with check-types-module ds-size))
(define ds-var (with check-types-module ds-var))
(define ds-rec (with check-types-module ds-rec))
(define ds-abbrev (with check-types-module ds-abbrev))
(define ds-region (with check-types-module ds-region))
(define ds-eff (with check-types-module ds-eff))
(define ds-private (with check-types-module ds-private))
(define ds-conv (with check-types-module ds-conv))
(define ds-fun (with check-types-module ds-fun))
(define x-var (with check-types-module x-var))
(define x-const (with check-types-module x-const))
(define x-lambda (with check-types-module x-lambda))
(define x-app (with check-types-module x-app))
(define x-plambda (with check-types-module x-plambda))
(define x-letregion (with check-types-module x-letregion))
(define x-rlambda (with check-types-module x-rlambda))
(define x-proj (with check-types-module x-proj))
(define x-if (with check-types-module x-if))
(define x-letrec (with check-types-module x-letrec))
(define x-let (with check-types-module x-let))
(define x-begin (with check-types-module x-begin))
(define x-prompt (with check-types-module x-prompt))
(define x-the (with check-types-module x-the))
(define x-convention (with check-types-module x-convention))
(define x-bloblet (with check-types-module x-bloblet))
(define x-product (with check-types-module x-product))
(define x-extract (with check-types-module x-extract))
(define x-sum (with check-types-module x-sum))
(define x-tagcase (with check-types-module x-tagcase))
(define x-module (with check-types-module x-module))
(define x-with (with check-types-module x-with))
(define k-ok (with check-types-module k-ok))
(define k-err (with check-types-module k-err))
(define k-done (with check-types-module k-done))
