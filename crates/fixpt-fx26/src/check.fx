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
(define-datatype k-region (r-const symbol) (r-fresh int string) (r-var int) (r-frozen int bool) (r-heap) (r-global symbol) (r-globals))

(define-datatype k-atom
  (a-read k-region) (a-write k-region) (a-alloc k-region)
  (a-goto k-region) (a-comefrom k-region) (a-await k-region) (a-spin) (a-var int))
(define-type k-eff (listof k-atom acyclic))

(define-type k-ids (listof int acyclic))
;; A binder: a description variable and its kind, 0 region, 1 effect, 2 type.
(define-type k-binders (listof (productof (1 int) (2 int)) acyclic))
(define-type k-parts (listof (productof (1 symbol) (2 int)) acyclic))
(define-type k-names (listof symbol acyclic))

;; A description in argument position, what `proj` supplies.
;; A list's length, as far as it is known: `finite`, some number; or a
;; constant and terms (variable . coefficient), in variable order.
;; A procedure's convention (`docs/research/native-conventions.md`):
;; `cellular`, `native`, `fx`, or a binder.
(define-datatype k-conv (cv-cellular) (cv-native) (cv-fx) (cv-var int))

(define-datatype k-size (sz-finite) (sz-lin int (listof (pairof int int acyclic) acyclic)))

(define-datatype k-desc (dr k-region) (de k-eff) (dt int) (dz k-size) (dc k-conv))

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
  (ty-nat k-size))

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
  (ds-conv k-conv))

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
             (listof (productof (1 symbol) (2 kx)) acyclic) int int))
(define-type kxs (listof kx acyclic))

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

(define k-copy-tys (subr (maxeff (read @globals) (read @t) (write @t) spin) ((arrayof k-ty @t) (arrayof k-ty @t) int) unit)
  (lambda (from to i)
    (if (= i (array-length from))
        #u
        (begin (array-set! to i (array-ref from i)) (k-copy-tys from to (+ i 1))))))

(define k-ty-new (subr (maxeff kstate spin) (k-ty) int)
  (lambda (t)
    (let ((n (get k-ntys)))
      (begin
        (if (= n (array-length (get k-tys)))
            (let ((bigger (the (arrayof k-ty @t) (make-array (* 2 n) (ty-void)))))
              (begin (k-copy-tys (get k-tys) bigger 0) (set k-tys bigger)))
            #u)
        (array-set! (get k-tys) n t)
        (set k-ntys (+ n 1))
        n))))

(define k-raw (subr (maxeff (read @globals) (read @t)) (int) k-ty) (lambda (id) (array-ref (get k-tys) id)))
;; Follow forwarding links to the type itself.
(define k-resolve (subr (maxeff (read @globals) (read @t) spin) (int) int)
  (lambda (id) (tagcase (k-raw id) (ty-link (to) (if (null? to) id (k-resolve (car to)))) (else x id))))
(define k-get (subr (maxeff (read @globals) (read @t) spin) (int) k-ty) (lambda (id) (k-raw (k-resolve id))))
(define k-set-link (subr kstate (int int) unit)
  (lambda (slot to) (array-set! (get k-tys) slot (ty-link (cons to nil)))))
(define k-slot (subr (maxeff kstate spin) () int) (lambda () (k-ty-new (ty-link nil))))

;; Which types a walk has seen: a type is seen in walk `e` when its mark
;; is `e`, so each walk takes a new epoch and nothing is cleared.
(define k-marks (ref (arrayof int @t) @t) (new (make-array 512 0)))
(define k-epoch (ref int @t) (new 0))
(define k-new-epoch (subr kstate () int)
  (lambda () (begin (set k-epoch (+ (get k-epoch) 1)) (get k-epoch))))
(define n-copy-marks (subr (maxeff (read @globals) (read @t) (write @t) spin) ((arrayof int @t) (arrayof int @t) int) unit)
  (lambda (from to i)
    (if (= i (array-length from)) #u (begin (array-set! to i (array-ref from i)) (n-copy-marks from to (+ i 1))))))
;; Whether walk `e` has seen `t` already; if not, it has now.
(define k-visit? (subr (maxeff kstate spin) (int int) bool)
  (lambda (t e)
    (begin
      (if (>= t (array-length (get k-marks)))
          (let ((bigger (the (arrayof int @t) (make-array (* 2 (array-length (get k-tys))) 0))))
            (begin (n-copy-marks (get k-marks) bigger 0) (set k-marks bigger)))
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
(define k-certified-lengths (ref (listof (productof (1 symbol) (2 int) (3 k-size)) acyclic) @t) (new nil))
(define k-new-dvar-of (subr kstate (symbol int) int)
  (lambda (name kind)
    (let ((v (k-new-dvar name)))
      (begin (if (= kind 3) (set k-places (cons v (get k-places))) #u)
             (if (= kind 4) (set k-datas (cons v (get k-datas))) #u)
             v))))
;; Which description variables are of kind `data`.
(define k-data-var? (subr (maxeff (read @globals) (read @t)) (int) bool)
  (lambda (v) (k-has-id? (get k-datas) v)))
(define k-place-var? (subr (maxeff (read @globals) (read @t)) (int) bool)
  (lambda (v) (k-has-id? (get k-places) v)))
;; Each bounded region binder's bound: `(r region p)`, a region that won't
;; outlive `p` (`docs/research/places-and-regions.md`).
(define k-bounds (ref (listof (pairof int k-region @t) acyclic) @t) (new nil))
;; The region and place variables bound around each one's binder, which it
;; won't outlive: the order of lifetimes, by nesting.
(define k-outers (ref (listof (pairof int k-ids @t) acyclic) @t) (new nil))
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
(define k-gen-of (subr (maxeff (read @globals) (read @t)) (int) k-gen) (lambda (g) (k-nth (get k-gens) (- (- (get k-ngens) 1) g))))
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
(define k-binder-has? (subr (maxeff (read @globals) (read @t)) (k-binders int) bool)
  (lambda (bs v) (and (not (null? bs)) (or (= (extract (car bs) 1) v) (k-binder-has? (cdr bs) v)))))
;; Whether `v` is a generative type's parameter, and `r` one or frozen into one.
(define k-gen-param? (subr (maxeff (read @globals) (read @t)) (int) bool)
  (lambda (v)
    (letrec ((in-binders (subr (maxeff (read @globals) (read @t)) (k-binders) bool)
                         (lambda (bs) (and (not (null? bs)) (or (= (extract (car bs) 1) v) (in-binders (cdr bs))))))
             (in-gens (subr (maxeff (read @globals) (read @t)) ((listof k-gen acyclic)) bool)
                      (lambda (gs) (and (not (null? gs)) (or (in-binders (extract (car gs) 2)) (in-gens (cdr gs)))))))
      (in-gens (get k-gens)))))
;; The types among descriptions, and the regions.
(define k-desc-types (subr (maxeff (read @globals) (alloc @t)) ((listof k-desc acyclic)) k-ids)
  (lambda (ds)
    (if (null? ds) nil (let ((rest (k-desc-types (cdr ds)))) (tagcase (car ds) (dt (x) (the k-ids (cons x rest))) (else y rest))))))
(define k-desc-regions (subr (maxeff (read @globals) (alloc @t)) ((listof k-desc acyclic)) (listof k-region acyclic))
  (lambda (ds)
    (if (null? ds)
        nil
        (let ((rest (k-desc-regions (cdr ds)))) (tagcase (car ds) (dr (r) (the (listof k-region acyclic) (cons r rest))) (else y rest))))))
(define k-gen-region? (subr (maxeff (read @globals) (read @t)) (k-region) bool)
  (lambda (r) (tagcase r (r-var (v) (k-gen-param? v)) (r-frozen (p f) (and (>= p 0) (k-gen-param? p))) (else x #f))))
;; Why each member of a recursive group that may not end may not.
(define k-spin-why (ref (listof (productof (1 symbol) (2 int) (3 string)) acyclic) @t) (new nil))
(define k-named-has? (subr (maxeff (read @globals) (read @t)) (k-named symbol int) bool)
  (lambda (ns n t) (and (not (null? ns)) (or (and (symbol=? (car (car ns)) n) (= (cdr (car ns)) t)) (k-named-has? (cdr ns) n t)))))
(define k-bound-of (subr (maxeff (read @globals) (read @t) (alloc @t)) (int) (listof k-region acyclic))
  (lambda (v)
    (letrec ((find (subr (maxeff (read @globals) (read @t) (alloc @t)) ((listof (pairof int k-region @t) acyclic)) (listof k-region acyclic))
               (lambda (xs) (cond ((null? xs) nil) ((= (car (car xs)) v) (the (listof k-region acyclic) (cons (cdr (car xs)) nil))) (else (find (cdr xs)))))))
      (find (get k-bounds)))))
(define k-outer-of (subr (maxeff (read @globals) (read @t)) (int) k-ids)
  (lambda (v)
    (letrec ((find (subr (maxeff (read @globals) (read @t)) ((listof (pairof int k-ids @t) acyclic)) k-ids)
               (lambda (xs) (cond ((null? xs) nil) ((= (car (car xs)) v) (cdr (car xs))) (else (find (cdr xs)))))))
      (find (get k-outers)))))
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
(define k-symbol int 6)
(define k-void int 10)
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
(define k-known (ref (table symbol (listof bool acyclic) @t) @t) (new (make-table symbol-hash symbol=?)))
;; Whether each binding in `k-env` is a global: one a top-level definition
;; made. Naming one reads it, `(read (globals g))`, when
;; `k-globals-effects` says so, as the language will once every program
;; says what it reads (off until then).
(define k-global (ref (table symbol (listof bool acyclic) @t) @t) (new (make-table symbol-hash symbol=?)))
(define k-globals-effects (ref bool @t) (new #t))
;; The latent effect of the lambda checked last: for `define*`, what the
;; globals its lambda reads are.
(define k-last-latent (ref k-eff @t) (new nil))
;; For a driver: whether naming a global reads it.
(define check-globals-effects! (subr (maxeff (read @globals) (write @t)) (bool) unit) (lambda (on) (set k-globals-effects on)))
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
(define k-broken-why (subr (maxeff (read @globals) (read @t) spin) (symbol) (listof string acyclic))
  (lambda (s)
    (let ((d (k-name-depth s)))
      (letrec ((go (subr (read @globals) ((listof k-break acyclic)) (listof string acyclic))
                 (lambda (bs)
                   (cond ((null? bs) nil)
                         ((and (symbol=? (extract (car bs) 1) s) (= (extract (car bs) 2) d)) (the (listof string acyclic) (cons (extract (car bs) 3) nil)))
                         (else (go (cdr bs)))))))
        (go (get k-broken))))))
;; What `s` is where it is used: its innermost binding; none, if that is
;; broken.
(define k-lookup (subr (maxeff (read @globals) (read @t) spin) (symbol) int)
  (lambda (s)
    (let ((st (table-ref (get k-env) s nil)))
      (if (or (null? st) (not (null? (k-broken-why s)))) -1 (car st)))))
;; The same, broken or not.
(define k-lookup-raw (subr (maxeff (read @globals) (read @t) spin) (symbol) int)
  (lambda (s) (let ((st (table-ref (get k-env) s nil))) (if (null? st) -1 (car st)))))
;; What an unbound name's use says: why, if it is broken.
(define k-unbound (subr (maxeff (read @globals) (read @t) (alloc @t) spin) (symbol) string)
  (lambda (s)
    (let ((why (k-broken-why s)))
      (if (null? why)
          (k-cat3 "unbound variable `" (symbol->string s) "`")
          (k-cat5 "`" (symbol->string s) "` is broken, " (car why) ": define it again to use it")))))
(define k-bind (subr (maxeff kstate spin) (symbol int) unit)
  (lambda (s t)
    (begin
      (table-set! (get k-env) s (cons t (table-ref (get k-env) s nil)))
      (table-set! (get k-known) s (the (listof bool acyclic) (cons #f (table-ref (get k-known) s nil))))
      (table-set! (get k-global) s (the (listof bool acyclic) (cons #f (table-ref (get k-global) s nil))))
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
(define k-find-desc (subr (maxeff (read @globals) (read @t) (alloc @t)) (k-scope symbol) (listof k-ds acyclic))
  (lambda (ds s)
    (cond ((null? ds) nil) ((symbol=? (car (car ds)) s) (cons (cdr (car ds)) nil)) (else (k-find-desc (cdr ds) s)))))
;; What `s` means as a description: none or one.
(define k-lookup-desc (subr (maxeff (read @globals) (read @t) (alloc @t)) (symbol) (listof k-ds acyclic))
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
(define-type k-facts (listof (productof (1 int) (2 int) (3 int)) acyclic))
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
(define k-add-effect-facts (subr (read @globals) (k-facts k-facts) k-facts)
  (lambda (notes acc)
    (if (null? notes)
        acc
        (k-add-effect-facts (cdr notes)
                            (the k-facts (cons (product (1 (extract (car notes) 1)) (2 (extract (car notes) 2)) (3 (- -1 (extract (car notes) 3)))) acc))))))
;; What checking found, for a compiler: each `extract`'s field, `(a b i)`;
;; and each expression's effect summary (`k-effect-notes`), `(a b n)` with n
;; negative, the summary -1 - n.
(define checked-extracts (subr (maxeff (read @globals) (read @t)) () k-facts)
  (lambda () (k-add-effect-facts (get k-effect-notes) (get k-extracts))))
(define checked-effects (subr (maxeff (read @globals) (read @t)) () k-facts) (lambda () (get k-effect-notes)))
;; Whether `e` may keep its continuation for later, write a global, or do
;; what an effect variable stands for.
(define k-disrupts? (subr (read @globals) (k-eff) bool)
  (lambda (e)
    (and (not (null? e))
         (or (tagcase (car e)
               (a-comefrom (r) #t)
               (a-var (v) #t)
               (a-write (r) (tagcase r (r-global (g) #t) (r-globals () #t) (else y #f)))
               (else y #f))
             (k-disrupts? (cdr e))))))
(define k-reads-only? (subr (read @globals) (k-eff) bool)
  (lambda (e) (or (null? e) (and (tagcase (car e) (a-read (r) #t) (else y #f)) (k-reads-only? (cdr e))))))
(define k-summary (subr (read @globals) (k-eff) int)
  (lambda (e) (cond ((null? e) 0) ((k-reads-only? e) 1) ((k-disrupts? e) 3) (else 2))))

;;; ------------------------------------------------------------ effects

(define k-region-rank (subr pure (k-region) int)
  (lambda (r) (tagcase r (r-const (n) 0) (r-fresh (i n) 1) (r-var (v) 2) (r-frozen (p f) 3) (r-heap () 4) (r-global (g) 5) (r-globals () 6))))
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
                (r-frozen (q g) (let ((c (k-int-cmp p q))) (if (= c 0) (k-int-cmp (if f 1 0) (if g 1 0)) c)))
                (else y 0)))
            (r-heap () 0)
            (r-global (g) (tagcase s (r-global (h) (symbol-compare g h)) (else y 0)))
            (r-globals () 0))
          c))))
(define k-region=? (subr (maxeff (read @globals) spin) (k-region k-region) bool) (lambda (r s) (= (k-region-cmp r s) 0)))

(define k-atom-rank (subr pure (k-atom) int)
  (lambda (a) (tagcase a (a-read (r) 0) (a-write (r) 1) (a-alloc (r) 2) (a-goto (r) 3) (a-comefrom (r) 4) (a-await (r) 5) (a-spin () 6) (a-var (v) 7))))
;; The atom's region; a variable's is none, shown as a binder -1.
(define k-atom-region (subr (read @globals) (k-atom) k-region)
  (lambda (a)
    (tagcase a (a-read (r) r) (a-write (r) r) (a-alloc (r) r) (a-goto (r) r) (a-comefrom (r) r) (a-await (r) r) (a-spin () (r-var -1)) (a-var (v) (r-var -1)))))
(define k-has-region? (subr (read @globals) (k-atom) bool) (lambda (a) (< (k-atom-rank a) 6)))
(define k-atom-cmp (subr (maxeff (read @globals) spin) (k-atom k-atom) int)
  (lambda (a b)
    (let ((c (k-int-cmp (k-atom-rank a) (k-atom-rank b))))
      (cond ((not (= c 0)) c)
            ((k-has-region? a) (k-region-cmp (k-atom-region a) (k-atom-region b)))
            (else (tagcase a (a-var (v) (tagcase b (a-var (w) (k-int-cmp v w)) (else y 0))) (else y 0)))))))
(define k-atom-with (subr (read @globals) (k-atom k-region) k-atom)
  (lambda (a r)
    (tagcase a (a-read (x) (a-read r)) (a-write (x) (a-write r)) (a-alloc (x) (a-alloc r))
      (a-goto (x) (a-goto r)) (a-comefrom (x) (a-comefrom r)) (a-await (x) (a-await r)) (a-spin () a) (a-var (v) a))))

(define k-insert (subr (maxeff (read @globals) (read @t) (alloc @t) spin) (k-atom k-eff) k-eff)
  (lambda (a e)
    (if (null? e)
        (cons a nil)
        (let ((c (k-atom-cmp a (car e))))
          (cond ((< c 0) (cons a e)) ((= c 0) e) (else (cons (car e) (k-insert a (cdr e)))))))))
(define k-union-each (subr (maxeff (read @globals) (read @t) (alloc @t) spin) (k-eff k-eff) k-eff)
  (lambda (x y) (if (null? x) y (k-union-each (cdr x) (k-insert (car x) y)))))
(define k-sorted? (subr (maxeff (read @globals) (read @t) spin) (k-eff) bool)
  (lambda (e) (or (null? e) (null? (cdr e)) (and (< (k-atom-cmp (car e) (car (cdr e))) 0) (k-sorted? (cdr e))))))
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
(define k-contains? (subr (maxeff (read @globals) (read @t) spin) (k-eff k-atom) bool)
  (lambda (e a) (cond ((null? e) #f) ((= (k-atom-cmp (car e) a) 0) #t) (else (k-contains? (cdr e) a)))))
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
        (k-within-sorted? x y (k-contains? y (a-read (r-globals))) (k-contains? y (a-write (r-globals))))
        (k-within-each? x y))))
(define k-eff=? (subr (maxeff (read @globals) (read @t) spin) (k-eff k-eff) bool) (lambda (x y) (and (k-within? x y) (k-within? y x))))
(define k-one (subr (alloc @t) (k-atom) k-eff) (lambda (a) (cons a nil)))
(define k-allocates? (subr (maxeff (read @globals) (read @t)) (k-eff) bool)
  (lambda (e) (cond ((null? e) #f) ((= (k-atom-rank (car e)) 2) #t) (else (k-allocates? (cdr e))))))

;;; ------------------------------------------------------------ printing

(define k-region-show (subr (maxeff (read @globals) (read @t)) (k-region) string)
  (lambda (r) (tagcase r (r-const (n) (symbol->string n)) (r-fresh (i n) n) (r-var (v) (symbol->string (k-dvar-name v))) (r-frozen (p f)
                  (let ((word (if f "acyclic" "const")))
                    (if (< p 0) word (k-cat5 "(" word " " (symbol->string (k-dvar-name p)) ")")))) (r-heap () "heap")
                  (r-global (g) (k-cat3 "(globals " (symbol->string g) ")")) (r-globals () "@globals"))))
(define k-atom-show (subr (maxeff (read @globals) (read @t)) (k-atom) string)
  (lambda (a)
    (letrec ((one (subr (maxeff (read @globals) (read @t)) (string k-region) string) (lambda (op r) (k-cat5 "(" op " " (k-region-show r) ")"))))
      (tagcase a
        (a-read (r) (one "read" r)) (a-write (r) (one "write" r)) (a-alloc (r) (one "alloc" r))
        (a-goto (r) (one "goto" r)) (a-comefrom (r) (one "comefrom" r)) (a-await (r) (one "await" r))
        (a-spin () "spin")
        (a-var (v) (symbol->string (k-dvar-name v)))))))
(define k-atoms-show (subr (maxeff (read @globals) (read @t)) (k-eff) string)
  (lambda (e) (if (null? e) "" (string-append (string-append " " (k-atom-show (car e))) (k-atoms-show (cdr e))))))
(define k-strings-append (subr (read @globals) ((listof string acyclic) (listof string acyclic)) (listof string acyclic))
  (lambda (xs ys) (if (null? xs) ys (the (listof string acyclic) (cons (car xs) (k-strings-append (cdr xs) ys))))))
(define k-strings-spaced (subr (read @globals) ((listof string acyclic)) string)
  (lambda (xs) (if (null? xs) "" (string-append (string-append " " (car xs)) (k-strings-spaced (cdr xs))))))
;; The names of the globals `e` reads (`op` 0) or writes (1), in order, each
;; after a space.
(define k-globals-shown (subr (maxeff (read @globals) (read @t)) (k-eff int) string)
  (lambda (e op)
    (if (null? e)
        ""
        (let ((g (tagcase (car e)
                   (a-read (r) (if (= op 0) (tagcase r (r-global (g) (string-append " " (symbol->string g))) (else y "")) ""))
                   (a-write (r) (if (= op 1) (tagcase r (r-global (g) (string-append " " (symbol->string g))) (else y "")) ""))
                   (else y ""))))
          (string-append g (k-globals-shown (cdr e) op))))))
(define k-one-global? (subr pure (k-atom) bool)
  (lambda (a)
    (tagcase a
      (a-read (r) (tagcase r (r-global (g) #t) (else y #f)))
      (a-write (r) (tagcase r (r-global (g) #t) (else y #f)))
      (else y #f))))
;; Whether `a` is on globals' bindings, which are never masked.
(define k-globals-atom? (subr (read @globals) (k-atom) bool)
  (lambda (a) (and (k-has-region? a) (tagcase (k-atom-region a) (r-global (g) #t) (r-globals () #t) (else y #f)))))
;; The atoms shown, reads, or writes, of several globals being one atom:
;; `(read (globals f g))`.
(define k-atom-strings (subr (maxeff (read @globals) (read @t)) (k-eff) (listof string acyclic))
  (lambda (e)
    (letrec ((others (subr (maxeff (read @globals) (read @t)) (k-eff) (listof string acyclic))
                       (lambda (e)
                         (cond ((null? e) nil)
                               ((k-one-global? (car e)) (others (cdr e)))
                               (else (the (listof string acyclic) (cons (k-atom-show (car e)) (others (cdr e))))))))
             (grouped (subr (maxeff (read @globals) (read @t)) (string string) (listof string acyclic))
                        (lambda (op names) (if (string=? names "") nil (the (listof string acyclic) (cons (k-cat5 "(" op " (globals" names "))") nil))))))
      (k-strings-append (others e) (k-strings-append (grouped "read" (k-globals-shown e 0)) (grouped "write" (k-globals-shown e 1)))))))
;; `pure`, a single atom, or `…`.
(define k-show-effect (subr (maxeff (read @globals) (read @t)) (k-eff) string)
  (lambda (e)
    (let ((xs (k-atom-strings e)))
      (cond ((null? xs) "pure")
            ((null? (cdr xs)) (car xs))
            (else (k-cat3 "(maxeff" (k-strings-spaced xs) ")"))))))

(define k-kind-name (subr pure (int) string)
  (lambda (k) (cond ((= k 0) "region") ((= k 1) "effect") ((= k 3) "place") ((= k 4) "data") ((= k 5) "size") ((= k 6) "conv") (else "type"))))
;; A convention as a program writes it.
(define k-conv-show (subr (maxeff (read @globals) (read @t)) (k-conv) string)
  (lambda (c)
    (tagcase c (cv-cellular () "cellular") (cv-native () "native") (cv-fx () "fx") (cv-var (v) (symbol->string (k-dvar-name v))))))
;; The program's convention: what a subroutine type that names none has,
;; and what a convention nothing solves defaults to. Cellular, unless a
;; driver says otherwise (`--calling-convention`).
(define k-conv-default (ref k-conv @t) (new (cv-cellular)))
;; For a driver: whether the program's convention is native.
(define check-conv-native! (subr (maxeff (read @globals) (write @t)) (bool) unit)
  (lambda (on) (set k-conv-default (if on (cv-native) (cv-cellular)))))
;; A convention as a number: one of FX-26's own, or its binder.
(define k-conv-code (subr pure (k-conv) int)
  (lambda (c) (tagcase c (cv-cellular () -1) (cv-native () -2) (cv-fx () -3) (cv-var (v) v))))
(define k-conv=? (subr (read @globals) (k-conv k-conv) bool)
  (lambda (a b) (= (k-conv-code a) (k-conv-code b))))
;; As Rust's `{:?}` writes a kind.
(define k-kind-debug (subr pure (int) string)
  (lambda (k) (cond ((= k 0) "Region") ((= k 1) "Effect") ((= k 3) "Place") ((= k 4) "Data") ((= k 5) "Size") ((= k 6) "Conv") (else "Type"))))
;; Whether a region is a place: a variable bound as one.
(define k-place? (subr (maxeff (read @globals) (read @t)) (k-region) bool)
  (lambda (r) (tagcase r (r-var (v) (k-place-var? v)) (r-heap () #t) (else x #f))))

;; The name `define-type` gave `t`, innermost first: each name's innermost
;; binding only.
(define k-abbrev-in (subr (maxeff (read @globals) (read @t) (alloc @t) spin) (k-scope k-names int) (listof string acyclic))
  (lambda (ds seen t)
    (if (null? ds)
        nil
        (let ((n (car (car ds))))
          (tagcase (cdr (car ds))
            (ds-rec (d)
              (cond ((k-has-name? seen n) (k-abbrev-in (cdr ds) seen t))
                    ((= (k-resolve d) t) (cons (symbol->string n) nil))
                    (else (k-abbrev-in (cdr ds) (cons n seen) t))))
            (else y (k-abbrev-in (cdr ds) seen t)))))))
(define k-show-binders (subr (maxeff (read @globals) (read @t) (alloc @t)) (k-binders) (listof string acyclic))
  (lambda (bs)
    (if (null? bs)
        nil
        (let* ((v (extract (car bs) 1)) (b (k-bound-of v))
               (named (k-cat3 (symbol->string (k-dvar-name v)) " " (k-kind-name (extract (car bs) 2)))))
          (cons (if (null? b) (k-cat3 "(" named ")") (k-cat5 "(" named " " (k-region-show (car b)) ")"))
                (k-show-binders (cdr bs)))))))

;; How deep `t` is in `path`, newest first: its place from the root, from 1.
(define k-depth-of (subr (maxeff (read @globals) (read @t)) (k-ids int) int)
  (lambda (path t) (if (= (car path) t) (k-length path) (k-depth-of (cdr path) t))))
;; Whether `name` occurs in `s` as a symbol of its own.
(define k-mentions-token? (subr (maxeff (read @globals) spin) (string string) bool)
  (lambda (s name)
    (or (>= (k-find-sub s (k-cat3 " " name " ") 0) 0)
        (or (>= (k-find-sub s (k-cat3 " " name ")") 0) 0)
            (or (>= (k-find-sub s (k-cat3 "(" name " ") 0) 0)
                (>= (k-find-sub s (k-cat3 "(" name ")") 0) 0))))))
;; Sizes: a literal, `finite`, one more or less, and whether one list's
;; size is another's.
(define k-size-lit (subr (read @globals) (int) k-size) (lambda (k) (sz-lin k nil)))
;; The literal a size is, or -1.
(define k-size-as-lit (subr pure (k-size) int)
  (lambda (z) (tagcase z (sz-lin (k ts) (if (null? ts) k -1)) (else y -1))))
(define k-size-plus (subr (read @globals) (k-size int) k-size)
  (lambda (z d) (tagcase z (sz-lin (k ts) (sz-lin (+ k d) ts)) (else y z))))
(define k-terms=? (subr (read @globals) ((listof (pairof int int acyclic) acyclic) (listof (pairof int int acyclic) acyclic)) bool)
  (lambda (xs ys)
    (if (null? xs)
        (null? ys)
        (and (not (null? ys)) (= (car (car xs)) (car (car ys))) (= (cdr (car xs)) (cdr (car ys))) (k-terms=? (cdr xs) (cdr ys))))))
(define k-size=? (subr (read @globals) (k-size k-size) bool)
  (lambda (a b)
    (tagcase a
      (sz-finite () (tagcase b (sz-finite () #t) (else y #f)))
      (sz-lin (k ts) (tagcase b (sz-lin (k2 ts2) (and (= k k2) (k-terms=? ts ts2))) (else y #f))))))

(define k-map-find (subr (maxeff (read @globals) (read @t)) (k-map int) k-map)
  (lambda (m v) (cond ((null? m) nil) ((= (car (car m)) v) m) (else (k-map-find (cdr m) v)))))
;; Linear sizes (`src/sizes.rs`): a variable; `a + c·b`; `v` replaced.
(define-type k-terms (listof (pairof int int acyclic) acyclic))
(define k-size-var (subr (read @globals) (int) k-size) (lambda (v) (sz-lin 0 (the k-terms (cons (cons v 1) nil)))))
;; `xs + c·ys`, terms in variable order, none zero.
(define k-terms-add (subr (read @globals) (k-terms k-terms int) k-terms)
  (lambda (xs ys c)
    (cond ((null? ys) xs)
          ((null? xs) (let ((n (* c (cdr (car ys)))) (rest (k-terms-add xs (cdr ys) c)))
                        (if (= n 0) rest (the k-terms (cons (cons (car (car ys)) n) rest)))))
          ((< (car (car xs)) (car (car ys))) (the k-terms (cons (car xs) (k-terms-add (cdr xs) ys c))))
          ((> (car (car xs)) (car (car ys)))
           (let ((n (* c (cdr (car ys)))) (rest (k-terms-add xs (cdr ys) c)))
             (if (= n 0) rest (the k-terms (cons (cons (car (car ys)) n) rest)))))
          (else (let ((n (+ (cdr (car xs)) (* c (cdr (car ys))))) (rest (k-terms-add (cdr xs) (cdr ys) c)))
                  (if (= n 0) rest (the k-terms (cons (cons (car (car xs)) n) rest))))))))
(define k-size-add-scaled (subr (read @globals) (k-size k-size int) k-size)
  (lambda (a b c)
    (tagcase a
      (sz-lin (k ts) (tagcase b (sz-lin (k2 ts2) (sz-lin (+ k (* c k2)) (k-terms-add ts ts2 c))) (else y (sz-finite))))
      (else y (sz-finite)))))
(define k-coef-of (subr (read @globals) (k-terms int) int)
  (lambda (ts v) (cond ((null? ts) 0) ((= (car (car ts)) v) (cdr (car ts))) (else (k-coef-of (cdr ts) v)))))
(define k-size-replace (subr (read @globals) (k-size int k-size) k-size)
  (lambda (s v by)
    (tagcase s
      (sz-lin (k ts)
        (let ((c (k-coef-of ts v)))
          (if (= c 0) s (k-size-add-scaled (k-size-add-scaled s (k-size-var v) (- 0 c)) by c))))
      (else y (sz-finite)))))
;; What the branches being checked have learned about sizes: `lin = 0`
;; (`#t`) or `lin ≥ 0`, newest first.
(define-type k-size-fact (productof (1 k-size) (2 bool)))
(define k-size-facts (ref (listof k-size-fact acyclic) @t) (new nil))
;; `s` with each variable an equality determines rewritten away, oldest
;; fact first.
(define k-reduced (subr (maxeff (read @globals) (read @t)) (k-size) k-size)
  (lambda (s)
    (letrec ((go (subr (read @globals) (k-size (listof k-size-fact acyclic)) k-size)
                   (lambda (s fs)
                     (if (null? fs)
                         s
                         (go (let ((f (car fs)))
                               (if (not (extract f 2))
                                   s
                                   (tagcase (extract f 1)
                                     (sz-lin (k ts)
                                       (letrec ((unit (subr (read @globals) (k-terms) k-terms)
                                                      (lambda (xs) (cond ((null? xs) xs)
                                                                         ((or (= (cdr (car xs)) 1) (= (cdr (car xs)) -1)) xs)
                                                                         (else (unit (cdr xs)))))))
                                         (let ((u (unit ts)))
                                           (if (null? u)
                                               s
                                               (let* ((v (car (car u))) (c (cdr (car u)))
                                                      (rest (k-size-add-scaled (extract f 1) (k-size-var v) (- 0 c)))
                                                      (by (k-size-add-scaled (k-size-lit 0) rest (- 0 c))))
                                                 (k-size-replace s v by))))))
                                     (else y s))))
                             (cdr fs))))))
      (go s (the (listof k-size-fact acyclic) (reverse (get k-size-facts)))))))
;; Whether a size is plainly non-negative: every size is a natural.
(define k-plainly-nonneg? (subr (read @globals) (k-size) bool)
  (lambda (s)
    (tagcase s
      (sz-lin (k ts) (and (>= k 0) (letrec ((all (subr (read @globals) (k-terms) bool) (lambda (xs) (or (null? xs) (and (>= (cdr (car xs)) 0) (all (cdr xs))))))) (all ts))))
      (else y #f))))
;; Whether the facts show `a ≥ 0`: plainly, or with a fact `f ≥ 0` to spare.
(define k-size-nonneg? (subr (maxeff (read @globals) (read @t)) (k-size) bool)
  (lambda (a0)
    (let ((a (k-reduced a0)))
      (or (k-plainly-nonneg? a)
          (letrec ((any (subr (maxeff (read @globals) (read @t)) ((listof k-size-fact acyclic)) bool)
                        (lambda (fs)
                          (and (not (null? fs))
                               (or (and (not (extract (car fs) 2))
                                        (k-plainly-nonneg? (k-size-add-scaled a (k-reduced (extract (car fs) 1)) -1)))
                                   (any (cdr fs)))))))
            (any (the (listof k-size-fact acyclic) (reverse (get k-size-facts)))))))))
;; Whether the facts show `a = b`.
(define k-size-eq? (subr (maxeff (read @globals) (read @t)) (k-size k-size) bool)
  (lambda (a b)
    (tagcase a
      (sz-finite () (tagcase b (sz-finite () #t) (else y #f)))
      (else y (tagcase b (sz-finite () #f) (else w (k-size=? (k-reduced (k-size-add-scaled a b -1)) (k-size-lit 0))))))))
;; The size of the tail of a list of size `n`: one less, where the facts
;; show `n ≥ 1`; `finite` otherwise.
(define k-tail-size (subr (maxeff (read @globals) (read @t)) (k-size) k-size)
  (lambda (n) (tagcase n (sz-finite () n) (else y (if (k-size-nonneg? (k-size-plus n -1)) (k-size-plus n -1) (sz-finite))))))
;; Whether a list of size `m` is one of size `n`: the facts show them
;; equal, or `n` is `finite`.
(define k-size-le? (subr (maxeff (read @globals) (read @t)) (k-size k-size) bool)
  (lambda (m n) (or (tagcase n (sz-finite () #t) (else y #f)) (k-size-eq? m n))))
;; `s` with `m`'s sizes for its variables.
(define k-subst-size (subr (maxeff (read @globals) (read @t)) (k-size k-map) k-size)
  (lambda (s m)
    (tagcase s
      (sz-lin (k ts)
        (letrec ((go (subr (maxeff (read @globals) (read @t)) (k-size k-terms) k-size)
                       (lambda (out xs)
                         (if (null? xs)
                             out
                             (let ((f (k-map-find m (car (car xs)))))
                               (go (if (null? f) out (tagcase (cdr (car f)) (dz (by) (k-size-replace out (car (car xs)) by)) (else y out)))
                                   (cdr xs)))))))
          (go s ts)))
      (else y s))))
(define k-show-terms (subr (maxeff (read @globals) (read @t) (alloc @t) spin) ((listof (pairof int int acyclic) acyclic)) (listof string acyclic))
  (lambda (ts)
    (if (null? ts)
        nil
        (let* ((n (symbol->string (k-dvar-name (car (car ts)))))
               (c (cdr (car ts)))
               (x (if (= c 1) n (k-cat5 "(* " (int->string c) " " n ")"))))
          (cons x (k-show-terms (cdr ts)))))))
(define k-show-size (subr (maxeff (read @globals) (read @t) (alloc @t) spin) (k-size) string)
  (lambda (z)
    (tagcase z
      (sz-finite () "finite")
      (sz-lin (k ts)
        (let ((parts (k-show-terms ts)))
          (cond ((null? parts) (int->string k))
                ((and (null? (cdr parts)) (= k 0)) (car parts))
                ((and (null? (cdr parts)) (< k 0)) (k-cat5 "(- " (car parts) " " (int->string (- 0 k)) ")"))
                ((= k 0) (k-cat3 "(+ " (k-join parts " ") ")"))
                (else (k-cat5 "(+ " (k-join parts " ") " " (int->string k) ")"))))))))
;; `out`, the type a node shows as, as `(mu name out)` if it mentions itself.
(define k-mu-wrap (subr (maxeff (read @globals) spin) (string string) string)
  (lambda (name out) (if (k-mentions-token? out name) (k-cat5 "(mu " name " " out ")") out)))

(define-rec
  (k-show-on (subr (maxeff (read @globals) (read @t) (alloc @t) spin) (int k-ids) string)
    (lambda (t path)
      (let* ((t (k-resolve t)) (name (k-abbrev-in (get k-dscope) nil t)))
        (if (null? name) (k-show-body t path) (car name)))))
  (k-show-list (subr (maxeff (read @globals) (read @t) (alloc @t) spin) (k-ids k-ids) (listof string acyclic))
    (lambda (ts path) (if (null? ts) nil (cons (k-show-on (car ts) path) (k-show-list (cdr ts) path)))))
  (k-show-parts (subr (maxeff (read @globals) (read @t) (alloc @t) spin) (k-parts k-ids) string)
    (lambda (ps path)
      (if (null? ps)
          ""
          (string-append (k-cat5 " (" (symbol->string (extract (car ps) 1)) " " (k-show-on (extract (car ps) 2) path) ")")
                         (k-show-parts (cdr ps) path)))))
  ;; A node met again on the way down is a cycle: named by its depth, and
  ;; written `(mu %d …)` where the cycle starts.
  (k-show-descs (subr (maxeff (read @globals) (read @t) (alloc @t) spin) ((listof k-desc acyclic) k-ids) (listof string acyclic))
    (lambda (ds p)
      (if (null? ds)
          nil
          (let ((x (tagcase (car ds) (dt (t) (k-show-on t p)) (dr (r) (k-region-show r)) (de (e) (k-show-effect e)) (dz (z) (k-show-size z)) (dc (c) (k-conv-show c)))))
            (cons x (k-show-descs (cdr ds) p))))))
  (k-show-body (subr (maxeff (read @globals) (read @t) (alloc @t) spin) (int k-ids) string)
    (lambda (t path)
      (if (k-has-id? path t)
          (string-append "%" (int->string (k-depth-of path t)))
          (let ((p (the k-ids (cons t path))))
            (k-mu-wrap (string-append "%" (int->string (k-length p)))
            (tagcase (k-get t)
              (ty-base (s) (symbol->string s))
              (ty-void () "void")
              (ty-var (v) (symbol->string (k-dvar-name v)))
              (ty-link (x) "?")
              (ty-subr (e ps r cv)
                ;; The convention only where it is not the program's.
                (k-cat5 (k-cat4 "(subr " (if (k-conv=? cv (get k-conv-default)) "" (k-cat3 "(conv " (k-conv-show cv) ") ")) (k-show-effect e) " (") (k-join (k-show-list ps p) " ") ") " (k-show-on r p) ")"))
              (ty-poly (bs body) (k-cat5 "(poly (" (k-join (k-show-binders bs) " ") ") " (k-show-on body p) ")"))
              (ty-ref (a r) (k-cat5 "(ref " (k-show-on a p) " " (k-region-show r) ")"))
              (ty-product (ps) (k-cat3 "(productof" (k-show-parts ps p) ")"))
              (ty-sum (ps) (k-cat3 "(sumof" (k-show-parts ps p) ")"))
              (ty-array (a r) (k-cat5 "(arrayof " (k-show-on a p) " " (k-region-show r) ")"))
              (ty-icell (a r) (k-cat5 "(icell " (k-show-on a p) " " (k-region-show r) ")"))
              (ty-place (r) (k-cat3 "(place " (k-region-show r) ")"))
              (ty-pair (a b r)
                (if (= (k-resolve b) t)
                    (k-cat5 "(listof " (k-show-on a p) " " (k-region-show r) ")")
                    (k-cat5 (k-cat3 "(pairof " (k-show-on a p) " ") (k-show-on b p) " " (k-region-show r) ")")))
              (ty-tag (a h e r)
                (k-cat5 (k-cat4 "(prompt-tag " (k-show-on a p) " " (k-show-on h p)) " " (k-show-effect e) " "
                        (string-append (k-region-show r) ")")))
              (ty-comp (a h e r)
                (k-cat5 (k-cat4 "(composable " (k-show-on a p) " " (k-show-on h p)) " " (k-show-effect e) " "
                        (string-append (k-region-show r) ")")))
              (ty-markkey (a r) (k-cat5 "(mark-key " (k-show-on a p) " " (k-region-show r) ")"))
              (ty-bloblet (fs z r)
                (k-cat5 (if z "(bloblet (frozen" "(bloblet (fields") (if (null? fs) "" " ") (k-join (k-show-list fs p) " ")
                        ") " (string-append (k-region-show r) ")")))
              (ty-nlist (e z r)
                (tagcase r
                  (r-frozen (q f)
                    (if (>= q 0)
                        (k-cat5 "(nlist " (k-show-on e p) " " (k-show-size z) (k-cat3 " " (symbol->string (k-dvar-name q)) ")"))
                        (k-cat5 "(nlist " (k-show-on e p) " " (k-show-size z) ")")))
                  (else y (k-cat5 "(nlist " (k-show-on e p) " " (k-show-size z) ")"))))
              (ty-nat (z) (tagcase z (sz-finite () "nat") (else y (k-cat3 "(nat " (k-show-size z) ")"))))
              (ty-named (g ds)
                (let ((name (symbol->string (extract (k-gen-of g) 1))))
                  (if (null? ds) name (k-cat5 "(" name " " (k-join (k-show-descs ds p) " ") ")")))))))))))

;; A type. One `define-type` named prints as its name; any other recursive
;; type as `(mu %d …)`, `%d` naming the cycle.
(define k-show-ty (subr (maxeff (read @globals) (read @t) (alloc @t) spin) (int) string)
  (lambda (t) (k-show-on t nil)))

;;; ------------------------------------------------------------ reading syntax

(define k-sfail (subr checks (string syn) void)
  (lambda (m s) (k-fail m (syn-start s) (syn-end s))))
(define k-items (subr checks (syn string) (listof syn acyclic))
  (lambda (s what)
    (tagcase s (lst (items d a b) items) (else x (k-sfail (string-append what ": expected a list") s)))))
(define k-head (subr (maxeff (read @globals) (read @s)) ((listof syn acyclic)) string)
  (lambda (items) (if (null? items) "" (syn-name (car items)))))
(define k-name-of (subr checks (syn string) symbol)
  (lambda (s what) (if (syn-symbol? s) (syn-head s) (k-sfail what s))))
(define k-at-name? (subr pure (string) bool)
  (lambda (n) (and (> (string-length n) 0) (string=? (substring n 0 1) "@"))))
(define k-nil-syn? (subr (read @s) (syn) bool)
  (lambda (s) (tagcase s (lst (items d a b) (null? items)) (else x #f))))
;; The items of a list that may be written `()`.
(define k-items-or-nil (subr checks (syn string) (listof syn acyclic))
  (lambda (s what) (if (k-nil-syn? s) nil (k-items s what))))

(define k-parse-kind (subr checks (syn) int)
  (lambda (s)
    (let ((n (if (syn-symbol? s) (syn-name s) "")))
      (cond ((string=? n "region") 0) ((string=? n "place") 3) ((string=? n "effect") 1) ((string=? n "type") 2)
            ((string=? n "data") 4)
            ((string=? n "size") 5)
            ((string=? n "conv") 6)
            (else (k-sfail "a kind is `region`, `place`, `effect`, `type`, `data`, `size` or `conv`" s))))))

;; `@globals`, or `(globals g …)` as the regions of each `g`, in a list of
;; one; none if `s` is neither.
(define k-global-names (subr (maxeff checks spin) ((listof syn acyclic)) k-regions)
  (lambda (ns) (if (null? ns) nil (the k-regions (cons (r-global (k-name-of (car ns) "a global's name")) (k-global-names (cdr ns)))))))
(define k-globals-region (subr (maxeff checks spin) (syn) (listof k-regions acyclic))
  (lambda (s)
    (if (syn-symbol? s)
        (if (string=? (syn-name s) "@globals") (the (listof k-regions acyclic) (cons (the k-regions (cons (r-globals) nil)) nil)) nil)
        (let ((items (k-items-or-nil s "a region")))
          (if (and (not (null? items)) (and (syn-symbol? (car items)) (string=? (syn-name (car items)) "globals")))
              (if (null? (cdr items))
                  (k-sfail "`(globals name …)`: at least one global" s)
                  (the (listof k-regions acyclic) (cons (k-global-names (cdr items)) nil)))
              nil)))))
;; Each of `rs`, read (or written).
(define k-atoms-on (subr (maxeff (read @globals) (read @t) (alloc @t) spin) (bool k-regions) k-eff)
  (lambda (read rs) (if (null? rs) nil (k-insert (if read (a-read (car rs)) (a-write (car rs))) (k-atoms-on read (cdr rs))))))
;; The region `@name` stands for: the program's own, if `private-regions`
;; declared it, and otherwise the constant of that name.
(define k-region-constant (subr (maxeff (read @globals) (read @t) (alloc @t)) (symbol) k-region)
  (lambda (sym)
    (let ((d (k-lookup-desc sym)))
      (if (null? d) (r-const sym) (tagcase (car d) (ds-private (r) r) (else x (r-const sym)))))))

(define-rec
  (k-parse-region (subr (maxeff checks spin) (syn) k-region)
    (lambda (s)
      (if (not (null? (k-globals-region s)))
          (k-sfail "globals are a region only in effects: `(read @globals)`, `(write (globals g))`" s)
      (if (not (syn-symbol? s))
          ;; `(const p)`: data frozen into place `p`; `(acyclic p)`, and never
          ;; written, so with no cycle through it.
          (let ((items (k-items-or-nil s "a region")))
            (if (and (= (k-length items) 2)
                     (and (syn-symbol? (car items)) (or (string=? (syn-name (car items)) "const") (string=? (syn-name (car items)) "acyclic"))))
                (let ((p (k-parse-region (k-nth items 1))) (f (string=? (syn-name (car items)) "acyclic")))
                  (if (k-place? p)
                      (tagcase p (r-var (v) (r-frozen v f)) (else y (r-frozen -1 f)))
                      (k-sfail (string-append (k-quote (k-region-show p)) " is not a place") (k-nth items 1))))
                (k-sfail "expected a region" s)))
          (let* ((n (syn-name s)) (sym (string->symbol n)))
            (cond ((k-at-name? n) (k-region-constant sym))
                  ((string=? n "const") (r-frozen -1 #f))
                  ((string=? n "acyclic") (r-frozen -1 #t))
                  ((string=? n "finite") (k-sfail "`finite` is a size; data with no cycle through it is at `acyclic`" s))
                  ((string=? n "heap") (r-heap))
                  (else
                   (let ((d (k-lookup-desc sym)) (no (lambda () (string-append (k-quote n) " is not a region"))))
                     (if (null? d)
                         (k-sfail (no) s)
                         (tagcase (car d)
                           (ds-var (v k) (if (or (= k 0) (= k 3)) (r-var v) (k-sfail (no) s)))
                           (ds-region (r) r)
                           (else x (k-sfail (no) s)))))))))))))

;; A place: a region that is one.
(define k-parse-place (subr (maxeff checks spin) (syn) k-region)
  (lambda (s)
    (let ((r (k-parse-region s)))
      (if (k-place? r) r (k-sfail (string-append (k-quote (k-region-show r)) " is not a place") s)))))

(define k-binders-each (subr (maxeff checks spin) ((listof syn acyclic)) k-binders)
  (lambda (bs)
    (if (null? bs)
        nil
        (let ((pair (k-items (car bs) "a binder")))
          (if (or (= (k-length pair) 2) (= (k-length pair) 3))
              (let* ((name (k-name-of (car pair) "a binder's name"))
                     (kind (k-parse-kind (k-nth pair 1)))
                     ;; `(r region p)`: a region that won't outlive `p`, a
                     ;; place bound before it.
                     (bound (cond ((= (k-length pair) 2) (the (listof k-region acyclic) nil))
                                  ((= kind 0) (the (listof k-region acyclic) (cons (k-parse-place (k-nth pair 2)) nil)))
                                  (else (k-sfail "only a region binder has a bound: `(name region place)`" (k-nth pair 2)))))
                     (v (k-new-dvar-of name kind))
                     (bounded (if (null? bound) #u (set k-bounds (cons (cons v (car bound)) (get k-bounds)))))
                     (pushed (k-push-desc name (ds-var v kind)))
                     (rest (k-binders-each (cdr bs))))
                (cons (product (1 v) (2 kind)) rest))
              (k-sfail "a binder is `(name kind)`, or `(name region place)`" (car bs)))))))

;; `((name kind) …)`, binding each name for the rest of the reading.
(define k-parse-binders (subr (maxeff checks spin) (syn) k-binders)
  (lambda (s) (k-binders-each (k-items s "binders"))))

(define-rec
  (k-effects (subr (maxeff checks spin) ((listof syn acyclic)) k-eff)
    (lambda (xs) (if (null? xs) nil (let* ((e (k-parse-effect (car xs))) (rest (k-effects (cdr xs)))) (k-union e rest)))))
  (k-parse-effect (subr (maxeff checks spin) (syn) k-eff)
    (lambda (s)
      (if (syn-symbol? s)
          (let ((n (syn-name s)))
            (if (string=? n "pure")
                nil
                (if (string=? n "spin")
                (k-one (a-spin))
                (let ((d (k-lookup-desc (string->symbol n))) (no (lambda () (string-append (k-quote n) " is not an effect"))))
                  (if (null? d)
                      (k-sfail (no) s)
                      (tagcase (car d)
                        (ds-var (v k) (if (= k 1) (k-one (a-var v)) (k-sfail (no) s)))
                        (ds-eff (e) e)
                        (else x (k-sfail (no) s))))))))
          (let* ((items (k-items s "an effect")) (head (k-head items)))
            (cond ((string=? head "maxeff") (k-effects (cdr items)))
                  ((or (string=? head "read") (string=? head "write") (string=? head "alloc")
                       (string=? head "goto") (string=? head "comefrom") (string=? head "await"))
                   (if (= (k-length items) 2)
                       (let ((gs (k-globals-region (k-nth items 1))))
                        (cond
                         ((null? gs)
                       (let ((r (k-parse-region (k-nth items 1))))
                         (k-one (cond ((string=? head "read") (a-read r)) ((string=? head "write") (a-write r))
                                      ((string=? head "alloc") (a-alloc r)) ((string=? head "goto") (a-goto r))
                                      ((string=? head "await") (a-await r))
                                      (else (a-comefrom r))))))
                         ;; Globals' bindings, which are only read and written.
                         ((or (string=? head "read") (string=? head "write")) (k-atoms-on (string=? head "read") (car gs)))
                         (else (k-sfail (k-cat3 "globals are only read and written, not `" head "`") (k-nth items 1)))))
                       (k-sfail (k-cat3 "`(" head " region)`") s)))
                  (else (k-sfail "expected an effect" s))))))))

;; A label or tag: a name, or a positive integer, which is its digits.
(define k-syn-label (subr checks (syn) symbol)
  (lambda (s)
    (cond ((syn-symbol? s) (syn-head s))
          ((> (syn-int s) 0) (string->symbol (int->string (syn-int s))))
          (else (k-sfail "a label is a name or a positive integer" s)))))
(define k-has-label? (subr (maxeff (read @globals) (read @t)) (k-parts symbol) bool)
  (lambda (ps l) (cond ((null? ps) #f) ((symbol=? (extract (car ps) 1) l) #t) (else (k-has-label? (cdr ps) l)))))

(define k-shape (subr checks (bool string syn) unit)
  (lambda (ok shape s) (if ok #u (k-sfail shape s))))
(define-type k-slots (listof (pairof int syn @t) acyclic))
(define k-dletrec-slots (subr (maxeff checks spin) ((listof syn acyclic)) k-slots)
  (lambda (bs)
    (if (null? bs)
        nil
        (let ((pair (k-items (car bs) "a dletrec binding")))
          (if (= (k-length pair) 2)
              (let* ((name (k-name-of (car pair) "a name"))
                     (slot (k-slot))
                     (pushed (k-push-desc name (ds-rec slot)))
                     (rest (k-dletrec-slots (cdr bs))))
                (cons (cons slot (k-nth pair 1)) rest))
              (k-sfail "a dletrec binding is `(name type)`" (car bs)))))))
;; Regions storage is kept in, for `k-knot-in`.
(define-type k-kept (listof k-region acyclic))
(define k-kept-has? (subr (maxeff (read @globals) (read @t) spin) (k-kept k-region) bool)
  (lambda (rs r) (and (not (null? rs)) (or (k-region=? (car rs) r) (k-kept-has? (cdr rs) r)))))
(define k-kept-add (subr (maxeff (read @globals) (read @t) (alloc @t) spin) (k-kept k-region) k-kept)
  (lambda (rs r) (if (k-kept-has? rs r) rs (cons r rs))))
;; The regions of everything in `t` that can be written: storage a
;; generative type's representation may keep what it was given in.
(define-rec
  (k-storage-walk (subr (maxeff kstate spin) (int int (ref k-kept @t)) unit)
    (lambda (t seen out)
      (let ((t (k-resolve t)))
        (if (k-visit? t seen)
            #u
            (letrec ((add (subr (maxeff (read @globals) kstate spin) (k-region) unit) (lambda (r) (set out (k-kept-add (get out) r))))
                     (walk (subr (maxeff (read @globals) kstate spin) (int) unit) (lambda (x) (k-storage-walk x seen out)))
                     (walks (subr (maxeff (read @globals) kstate spin) (k-ids) unit) (lambda (xs) (k-storage-walks xs seen out))))
              (tagcase (k-get t)
                (ty-ref (a r) (begin (add r) (walk a)))
                (ty-array (a r) (begin (add r) (walk a)))
                (ty-icell (a r) (begin (add r) (walk a)))
                (ty-markkey (a r) (begin (add r) (walk a)))
                (ty-pair (a b r) (begin (tagcase r (r-frozen (q f) #u) (else y (add r))) (walk a) (walk b)))
                (ty-bloblet (fs z r) (begin (if z #u (add r)) (walks fs)))
                (ty-subr (e ps r cv) (begin (walks ps) (walk r)))
                (ty-poly (bs body) (walk body))
                (ty-product (ps) (k-storage-parts ps seen out))
                (ty-sum (ps) (k-storage-parts ps seen out))
                (ty-tag (a h e r) (begin (walk a) (walk h)))
                (ty-comp (b a e r) (begin (walk b) (walk a)))
                (ty-named (g ds) (begin (walk (extract (k-gen-of g) 4)) (walks (k-desc-types ds))))
                (ty-nlist (e z r) (walk e))
                (else x #u)))))))
  (k-storage-walks (subr (maxeff kstate spin) (k-ids int (ref k-kept @t)) unit)
    (lambda (ts seen out) (if (null? ts) #u (begin (k-storage-walk (car ts) seen out) (k-storage-walks (cdr ts) seen out)))))
  (k-storage-parts (subr (maxeff kstate spin) (k-parts int (ref k-kept @t)) unit)
    (lambda (ps seen out) (if (null? ps) #u (begin (k-storage-walk (extract (car ps) 2) seen out) (k-storage-parts (cdr ps) seen out))))))
(define k-storage-regions (subr (maxeff kstate spin) (int) k-kept)
  (lambda (t) (let ((out (the (ref k-kept @t) (new nil)))) (begin (k-storage-walk t (k-new-epoch) out) (get out)))))
;; `kept`, and each of `rs` that is not a generative type's parameter nor
;; frozen.
(define k-kept-extend (subr (maxeff (read @globals) (read @t) (alloc @t) spin) (k-kept (listof k-region acyclic)) k-kept)
  (lambda (kept rs)
    (cond ((null? rs) kept)
          ((or (k-gen-region? (car rs)) (tagcase (car rs) (r-frozen (q f) #t) (else y #f))) (k-kept-extend kept (cdr rs)))
          (else (k-kept-extend (k-kept-add kept (car rs)) (cdr rs))))))
(define k-append-regions (subr (maxeff (read @globals) (alloc @t)) ((listof k-region acyclic) (listof k-region acyclic)) (listof k-region acyclic))
  (lambda (xs ys) (if (null? xs) ys (the (listof k-region acyclic) (cons (car xs) (k-append-regions (cdr xs) ys))))))
;; Whether `t` keeps, in storage at some region `r`, a procedure whose
;; latent effect reads or awaits `r` and does not say `spin`: a knot tied
;; through the store, a loop with no recursive call, which only its type can
;; show. The region and the procedure's type, if so.
(define k-reads-kept (subr (maxeff (read @globals) (read @t) (alloc @t) spin) (k-eff k-kept) (listof k-region acyclic))
  (lambda (e kept)
    (if (k-contains? e (a-spin))
        (the (listof k-region acyclic) nil)
        (letrec ((find (subr (maxeff (read @globals) (read @t) (alloc @t) spin) (k-eff) (listof k-region acyclic))
                   (lambda (xs)
                     (if (null? xs)
                         (the (listof k-region acyclic) nil)
                         (let ((r (tagcase (car xs)
                                    (a-read (r) (if (k-kept-has? kept r) (the (listof k-region acyclic) (cons r nil)) (the (listof k-region acyclic) nil)))
                                    (a-await (r) (if (k-kept-has? kept r) (the (listof k-region acyclic) (cons r nil)) (the (listof k-region acyclic) nil)))
                                    (else y (the (listof k-region acyclic) nil)))))
                           (if (null? r) (find (cdr xs)) r))))))
          (find e)))))
(define k-kept-same? (subr (maxeff (read @globals) (read @t) spin) (k-kept k-kept) bool)
  (lambda (x y)
    (letrec ((within (subr (maxeff (read @globals) (read @t) spin) (k-kept k-kept) bool)
               (lambda (a b) (or (null? a) (and (k-kept-has? b (car a)) (within (cdr a) b))))))
      (and (within x y) (within y x)))))
(define-type k-knot (listof (pairof k-region int @t) acyclic))
(define-type k-kseen (ref (listof (pairof int k-kept @t) acyclic) @t))
(define k-kseen-has? (subr (maxeff (read @globals) (read @t) spin) ((listof (pairof int k-kept @t) acyclic) int k-kept) bool)
  (lambda (xs t kept)
    (and (not (null? xs)) (or (and (= (car (car xs)) t) (k-kept-same? (cdr (car xs)) kept)) (k-kseen-has? (cdr xs) t kept)))))
(define-rec
  (k-knot-in (subr (maxeff kstate spin) (int k-kept k-kseen) k-knot)
    (lambda (t kept seen)
      (let ((t (k-resolve t)))
        (if (k-kseen-has? (get seen) t kept)
            (the k-knot nil)
            (begin
              (set seen (cons (cons t kept) (get seen)))
              (tagcase (k-get t)
                (ty-ref (a r) (k-knot-in a (k-kept-add kept r) seen))
                (ty-array (a r) (k-knot-in a (k-kept-add kept r) seen))
                (ty-icell (a r) (k-knot-in a (k-kept-add kept r) seen))
                (ty-markkey (a r) (k-knot-in a (k-kept-add kept r) seen))
                (ty-pair (a b r)
                  (let ((k (tagcase r (r-frozen (p f) kept) (else y (k-kept-add kept r)))))
                    (let ((x (k-knot-in a k seen))) (if (null? x) (k-knot-in b k seen) x))))
                (ty-bloblet (fs z r) (k-knot-list fs (if z kept (k-kept-add kept r)) seen))
                (ty-product (ps) (k-knot-parts ps kept seen))
                (ty-sum (ps) (k-knot-parts ps kept seen))
                (ty-poly (bs body) (k-knot-in body kept seen))
                ;; A procedure: kept where it is, it may not read there
                ;; unsaid; what it takes and gives is kept nowhere yet.
                (ty-subr (e ps r cv)
                  (let ((found (k-reads-kept e kept)))
                    (if (null? found)
                        (let ((x (k-knot-list ps nil seen))) (if (null? x) (k-knot-in r nil seen) x))
                        (the k-knot (cons (cons (car found) t) nil)))))
                (ty-comp (x a e r)
                  (let ((found (k-reads-kept e kept)))
                    (if (null? found)
                        (let ((y (k-knot-in x nil seen))) (if (null? y) (k-knot-in a nil seen) y))
                        (the k-knot (cons (cons (car found) t) nil)))))
                (ty-tag (a h e r) (let ((y (k-knot-in a nil seen))) (if (null? y) (k-knot-in h nil seen) y)))
                (ty-nlist (e z r) (k-knot-in e kept seen))
                ;; Transparent to safety: its representation, and what it
                ;; was given, kept, cautiously, wherever its representation
                ;; keeps anything and in every region it was given.
                (ty-named (g ds)
                  (let* ((rep (extract (k-gen-of g) 4))
                         (k (k-kept-extend kept (k-append-regions (k-storage-regions rep) (k-desc-regions ds))))
                         (x (k-knot-in rep kept seen)))
                    (if (null? x) (k-knot-list (k-desc-types ds) k seen) x)))
                (else y (the k-knot nil))))))))
  (k-knot-list (subr (maxeff kstate spin) (k-ids k-kept k-kseen) k-knot)
    (lambda (ts kept seen)
      (if (null? ts) (the k-knot nil) (let ((x (k-knot-in (car ts) kept seen))) (if (null? x) (k-knot-list (cdr ts) kept seen) x)))))
  (k-knot-parts (subr (maxeff kstate spin) (k-parts k-kept k-kseen) k-knot)
    (lambda (ps kept seen)
      (if (null? ps) (the k-knot nil) (let ((x (k-knot-in (extract (car ps) 2) kept seen))) (if (null? x) (k-knot-parts (cdr ps) kept seen) x))))))
(define k-no-knot (subr (maxeff checks spin) (int int int) unit)
  (lambda (t a b)
    (let ((found (k-knot-in t nil (the k-kseen (new nil)))))
      (if (null? found)
          #u
          (let ((r (k-region-show (car (car found)))))
            (k-fail (k-cat5 "a procedure kept in `" r "` reads `" r
                            (k-cat3 "`, so it could reach itself: it must say `spin`, and it is a " (k-show-ty (cdr (car found))) ""))
                    a b))))))

;; Where description variable `v` is among binders `bs`, from `i`, or -1.
(define k-binder-index (subr (read @globals) (k-binders int int) int)
  (lambda (bs v i) (cond ((null? bs) -1) ((= (extract (car bs) 1) v) i) (else (k-binder-index (cdr bs) v (+ i 1))))))
;; The `i`th description of `ds`, none or one.
(define k-desc-at (subr (read @globals) ((listof k-desc acyclic) int) (listof k-desc acyclic))
  (lambda (ds i) (cond ((null? ds) nil) ((= i 0) (the (listof k-desc acyclic) (cons (car ds) nil))) (else (k-desc-at (cdr ds) (- i 1))))))
;; The `i`th parameter of binders `ps` a type `t` is, or -1.
(define k-param-of (subr (maxeff (read @globals) (read @t) spin) (k-binders int) int)
  (lambda (ps t) (tagcase (k-get (k-resolve t)) (ty-var (v) (k-binder-index ps v 0)) (else y -1))))
;; Descriptions `inner`, with each that is one of parameters `ps` replaced
;; by what `args` gives for it.
(define k-descs-given (subr (maxeff (read @globals) (read @t) spin) ((listof k-desc acyclic) k-binders (listof k-desc acyclic)) (listof k-desc acyclic))
  (lambda (inner ps args)
    (if (null? inner)
        nil
        (let* ((d (car inner))
               (given (tagcase d (dt (t) (let ((i (k-param-of ps t))) (if (< i 0) (the (listof k-desc acyclic) nil) (k-desc-at args i)))) (else y (the (listof k-desc acyclic) nil))))
               (rest (k-descs-given (cdr inner) ps args)))
          (the (listof k-desc acyclic) (cons (if (null? given) d (car given)) rest))))))
;; The type the `g`th generative type, given `args`, is at its head, if its
;; representation is one of its type parameters, perhaps through other such
;; generative types: what it is given there (none or one). None if its
;; representation has a constructor at its head
;; (`docs/research/soundness-findings.md`, A2).
(define k-named-head (subr (maxeff (read @globals) (read @t) spin) (int (listof k-desc acyclic) k-ids) (listof int acyclic))
  (lambda (g args seen)
    (if (k-has-id? seen g)
        nil
        (let* ((gen (k-gen-of g)) (ps (extract gen 2)) (rep (extract gen 4)))
          (tagcase (k-get (k-resolve rep))
            (ty-var (v)
              (let ((i (k-param-of ps rep)))
                (if (< i 0)
                    nil
                    (let ((d (k-desc-at args i)))
                      (if (null? d) nil (tagcase (car d) (dt (t) (the (listof int acyclic) (cons t nil))) (else y nil)))))))
            (ty-named (h inner) (k-named-head h (k-descs-given inner ps args) (the k-ids (cons g seen))))
            (else y nil))))))
(define k-grounded-from (subr (maxeff checks spin) (int k-ids int int) unit)
  (lambda (id seen a b)
    (tagcase (k-raw id)
      (ty-link (to)
        (cond ((null? to) #u)
              ((k-has-id? seen id) (k-fail "a recursive type must be built from a constructor, not only from names" a b))
              (else (k-grounded-from (car to) (cons id seen) a b))))
      ;; A `poly` is no constructor either: a cycle through `poly`s alone
      ;; describes no type, and unfolding it would never end.
      (ty-poly (bs x)
        (if (k-has-id? seen id)
            (k-fail "a recursive type must be built from a constructor, not only from names" a b)
            (k-grounded-from x (cons id seen) a b)))
      ;; Nor is a generative type whose representation is one of what it is
      ;; given: it is that.
      (ty-named (g ds)
        (let ((h (k-named-head g ds nil)))
          (cond ((null? h) #u)
                ((k-has-id? seen id) (k-fail "a recursive type must be built from a constructor, not only from names" a b))
                (else (k-grounded-from (car h) (cons id seen) a b)))))
      (else x #u))))

;; A name defined as another name, round a loop, describes nothing.
(define k-grounded (subr (maxeff checks spin) (int int int) unit)
  (lambda (slot a b) (k-grounded-from slot nil a b)))
(define k-dletrec-no-knot (subr (maxeff checks spin) (k-slots syn) unit)
  (lambda (ss s)
    (if (null? ss) #u (begin (k-no-knot (car (car ss)) (syn-start s) (syn-end s)) (k-dletrec-no-knot (cdr ss) s)))))
(define k-dletrec-grounded (subr (maxeff checks spin) (k-slots syn) unit)
  (lambda (ss s)
    (if (null? ss) #u (begin (k-grounded (car (car ss)) (syn-start s) (syn-end s)) (k-dletrec-grounded (cdr ss) s)))))
(define k-family-params (subr checks ((listof syn acyclic)) (listof (productof (1 symbol) (2 int)) acyclic))
  (lambda (ps)
    (if (null? ps)
        nil
        (let ((pair (k-items (car ps) "`(name kind)`")))
          (if (= (k-length pair) 2)
              (let* ((n (k-name-of (car pair) "a parameter's name")) (k (k-parse-kind (k-nth pair 1)))
                     (rest (k-family-params (cdr ps))))
                (cons (product (1 n) (2 k)) rest))
              (k-sfail "a parameter is `(name kind)`" (car ps)))))))

;; `(define-type (name (param kind) …) type)`: nothing is read until it is
;; used.
(define k-define-family (subr checks (symbol (listof syn acyclic) syn) unit)
  (lambda (name params body) (k-push-desc name (ds-abbrev (k-family-params params) body))))
;; Push a scope's entries, the first first.
(define k-push-all (subr kstate (k-scope) unit)
  (lambda (bs) (if (null? bs) #u (begin (k-push-desc (car (car bs)) (cdr (car bs))) (k-push-all (cdr bs))))))

;; The type families being expanded, each with the descriptions given it
;; and the slot its type will fill: a use inside with the same descriptions
;; is that slot, a knot (regular recursion).
(define-type k-family-knot (productof (1 symbol) (2 k-scope) (3 int)))
(define k-knots (ref (listof k-family-knot acyclic) @t) (new nil))
(define k-ds=? (subr (maxeff (read @globals) (read @t) spin) (k-ds k-ds) bool)
  (lambda (x y)
    (tagcase x
      (ds-rec (a) (tagcase y (ds-rec (b) (= (k-resolve a) (k-resolve b))) (else z #f)))
      (ds-region (a) (tagcase y (ds-region (b) (k-region=? a b)) (else z #f)))
      (ds-eff (a) (tagcase y (ds-eff (b) (k-eff=? a b)) (else z #f)))
      (ds-size (a) (tagcase y (ds-size (b) (k-size=? a b)) (else z #f)))
      (ds-conv (a) (tagcase y (ds-conv (b) (k-conv=? a b)) (else z #f)))
      (else z #f))))
(define k-scope=? (subr (maxeff (read @globals) (read @t) spin) (k-scope k-scope) bool)
  (lambda (xs ys)
    (if (null? xs)
        (null? ys)
        (and (not (null? ys)) (k-ds=? (cdr (car xs)) (cdr (car ys))) (k-scope=? (cdr xs) (cdr ys))))))
;; The head of a list's first item, or "" for anything else.
(define k-list-head (subr (maxeff (read @globals) (read @s)) (syn) string)
  (lambda (s) (tagcase s (lst (items d a b) (k-head items)) (else x ""))))
;; A convention: `cellular`, `native`, `fx`, or a name bound as one.
(define k-parse-conv (subr (maxeff checks spin) (syn) k-conv)
  (lambda (s)
    (if (not (syn-symbol? s))
        (k-sfail "a convention is `cellular`, `native`, `fx`, or a name bound as one" s)
        (let* ((n (syn-name s)) (no (k-cat3 "`" n "` is not a convention")))
          (cond ((string=? n "cellular") (cv-cellular))
                ((string=? n "native") (cv-native))
                ((string=? n "fx") (cv-fx))
                (else
                 (let ((d (k-lookup-desc (string->symbol n))))
                   (if (null? d)
                       (k-sfail no s)
                       (tagcase (car d)
                         (ds-var (v k) (if (= k 6) (cv-var v) (k-sfail no s)))
                         (ds-conv (c) c)
                         (else x (k-sfail no s)))))))))))
;; `(conv C)`: the convention `C`.
(define k-parse-conv-form (subr (maxeff checks spin) (syn) k-conv)
  (lambda (s)
    (let ((items (k-items s "`(conv convention)`")))
      (if (= (k-length items) 2) (k-parse-conv (k-nth items 1)) (k-sfail "`(conv convention)`" s)))))
;; The slot of the expansion of `name` with `bound` in progress, or -1.
(define k-knot-of (subr (maxeff (read @globals) (read @t) spin) ((listof k-family-knot acyclic) symbol k-scope) int)
  (lambda (ks name bound)
    (cond ((null? ks) -1)
          ((and (symbol=? (extract (car ks) 1) name) (k-scope=? (extract (car ks) 2) bound)) (extract (car ks) 3))
          (else (k-knot-of (cdr ks) name bound)))))

(define-rec
  (k-parse-types (subr (maxeff checks spin) ((listof syn acyclic)) k-ids)
    (lambda (xs) (if (null? xs) nil (let* ((t (k-parse-type (car xs))) (rest (k-parse-types (cdr xs)))) (cons t rest)))))
  (k-parse-parts (subr (maxeff checks spin) ((listof syn acyclic) k-parts) k-parts)
    (lambda (ps done)
      (if (null? ps)
          (reverse done)
          (let ((pair (k-items (car ps) "`(label type)`")))
            (if (= (k-length pair) 2)
                (let ((l (k-syn-label (car pair))))
                  (if (k-has-label? done l)
                      (k-sfail (string-append (k-quote (symbol->string l)) " appears twice") (car ps))
                      (let ((t (k-parse-type (k-nth pair 1))))
                        (k-parse-parts (cdr ps) (cons (product (1 l) (2 t)) done)))))
                (k-sfail "`(label type)`" (car ps)))))))
  ;; Storage written: a procedure kept there may not reach itself unsaid
  ;; (`spin`).
  (k-parse-type (subr (maxeff checks spin) (syn) int)
    (lambda (s)
      (let ((t (k-parse-type-node s)))
        (begin
          (if (and (not (syn-symbol? s))
                   (let ((h (k-head (k-items s "a type"))))
                     (or (string=? h "ref") (or (string=? h "icell") (or (string=? h "pairof") (or (string=? h "listof")
                         (or (string=? h "bloblet") (or (string=? h "arrayof") (or (string=? h "mark-key") (string=? h "mu"))))))))))
              (k-no-knot t (syn-start s) (syn-end s))
              #u)
          t))))
  ;; A size: a natural literal, or `finite`, some number not known.
  (k-parse-size (subr (maxeff checks spin) (syn) k-size)
    (lambda (s)
      (let ((usage "a size is a natural number, `finite`, a size variable, `(+ size …)` or `(- size k)`"))
        (cond ((>= (syn-int s) 0) (k-size-lit (syn-int s)))
              ((syn-symbol? s)
               (if (string=? (syn-name s) "finite")
                   (sz-finite)
                   (let ((d (k-lookup-desc (string->symbol (syn-name s)))))
                     (if (null? d)
                         (k-sfail usage s)
                         (tagcase (car d)
                           (ds-var (v k) (if (= k 5) (k-size-var v) (k-sfail usage s)))
                           (ds-size (z) z)
                           (else x (k-sfail usage s)))))))
              (else
               (let* ((items (k-items s "a size"))
                      (hd (if (and (not (null? items)) (syn-symbol? (car items))) (syn-name (car items)) "")))
                 (cond ((and (string=? hd "+") (not (null? (cdr items)))) (k-parse-size-sum (cdr items) (k-size-lit 0)))
                       ((and (string=? hd "-") (= (k-length items) 3))
                        (let ((a (k-parse-size (k-nth items 1))) (k (syn-int (k-nth items 2))))
                          (if (>= k 0) (k-size-plus a (- 0 k)) (k-sfail usage (k-nth items 2)))))
                       (else (k-sfail usage s)))))))))
  (k-parse-size-sum (subr (maxeff checks spin) ((listof syn acyclic) k-size) k-size)
    (lambda (xs out) (if (null? xs) out (k-parse-size-sum (cdr xs) (k-size-add-scaled out (k-parse-size (car xs)) 1)))))
  ;; What `(proves prop)` states: the type of its proof, with the lemma kept
  ;; pending for the definition it declares.
  (k-parse-proves (subr (maxeff checks spin) (syn string) int)
    (lambda (prop usage)
      (let* ((items (k-items prop "a proposition"))
             (head (if (and (not (null? items)) (syn-symbol? (car items))) (syn-name (car items)) ""))
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
          (set k-pending-lemma (cons (product (1 bs) (2 (car conc)) (3 (cdr conc)) (4 hyps) (5 (the k-named nil))) nil))
          t))))
  (k-le (subr (maxeff checks spin) (syn) (pairof int int @t))
    (lambda (s)
      (let ((items (k-items s "a proposition")))
        (if (and (= (k-length items) 3) (syn-symbol? (car items)) (string=? (syn-name (car items)) "<="))
            (let* ((a (k-parse-type (k-nth items 1))) (b (k-parse-type (k-nth items 2)))) (cons a b))
            (k-sfail "a proposition is `(<= type type)`" s)))))
  (k-les (subr (maxeff checks spin) ((listof syn acyclic)) k-hyps)
    (lambda (xs) (if (null? xs) nil (let* ((h (k-le (car xs))) (rest (k-les (cdr xs)))) (cons h rest)))))
  (k-hyp-coercions (subr (maxeff checks spin) (k-hyps k-eff k-ids) k-ids)
    (lambda (hs spin tail)
      (if (null? hs)
          tail
          (let ((c (k-ty-new (ty-subr spin (the k-ids (cons (car (car hs)) nil)) (cdr (car hs)) (get k-conv-default)))))
            (cons c (k-hyp-coercions (cdr hs) spin tail))))))
  ;; `(name d …)` for the `g`th generative type: a node, never expanded.
  (k-apply-gen (subr (maxeff checks spin) (syn int (listof syn acyclic)) int)
    (lambda (s g args)
      (let* ((gen (k-gen-of g)) (ps (extract gen 2)))
        (if (not (= (k-length args) (k-length ps)))
            (k-sfail (k-cat5 (k-quote (symbol->string (extract gen 1))) " takes " (int->string (k-length ps))
                             " description(s), and has " (int->string (k-length args)))
                     s)
            (let ((t (k-ty-new (ty-named g (k-gen-args ps args)))))
              ;; What it holds may keep a procedure that reaches itself.
              (begin (k-no-knot t (syn-start s) (syn-end s)) t))))))
  (k-gen-args (subr (maxeff checks spin) (k-binders (listof syn acyclic)) (listof k-desc acyclic))
    (lambda (ps args)
      (if (null? ps)
          nil
          (let* ((k (extract (car ps) 2))
                 (d (cond ((or (= k 2) (= k 4)) (dt (k-parse-type (car args))))
                          ((= k 0) (dr (k-parse-region (car args))))
                          ((= k 3) (dr (k-parse-place (car args))))
                          ((= k 5) (dz (k-parse-size (car args))))
                          ((= k 6) (dc (k-parse-conv (car args))))
                          (else (de (k-parse-effect (car args))))))
                 (rest (k-gen-args (cdr ps) (cdr args))))
            (cons d rest)))))
  (k-parse-type-node (subr (maxeff checks spin) (syn) int)
    (lambda (s)
      (if (syn-symbol? s)
          (let* ((n (syn-name s)) (sym (string->symbol n)) (base (k-find (get k-base) sym)))
            (cond ((string=? n "void") k-void)
                  ((and (string=? n "nat") (null? (k-lookup-desc sym))) (k-ty-new (ty-nat (sz-finite))))
                  ((>= base 0) base)
                  (else
                   (let ((d (k-lookup-desc sym)) (no (lambda () (string-append (k-quote n) " is not a type"))))
                     (if (null? d)
                         (k-sfail (no) s)
                         (tagcase (car d)
                           (ds-var (v k) (if (or (= k 2) (= k 4)) (k-ty-new (ty-var v)) (k-sfail (no) s)))
                           (ds-rec (t) t)
                           (ds-gen (g) (k-apply-gen s g nil))
                           (else x (k-sfail (no) s))))))))
          (let* ((items (k-items s "a type"))
                 (hd (if (null? items) '|()| (syn-head (car items))))
                 (abbrev (if (symbol=? hd '|()|) (the (listof k-ds acyclic) nil) (k-lookup-desc hd)))
                 (n (k-length items)))
            (if (and (not (null? abbrev)) (tagcase (car abbrev) (ds-abbrev (ps body) #t) (ds-gen (g) #t) (else x #f)))
                (tagcase (car abbrev)
                  (ds-abbrev (ps body) (k-expand-abbrev s hd ps body (cdr items)))
                  (ds-gen (g) (k-apply-gen s g (cdr items)))
                  (else x (k-sfail "an abbreviation" s)))
                (cond
                  ;; `(subr effect (param …) result)`, or with a convention
                  ;; first, `(subr (conv C) effect (param …) result)`; left
                  ;; out, it is the program's.
                  ((symbol=? hd 'subr)
                   (let* ((conv? (and (= n 5) (string=? (k-list-head (k-nth items 1)) "conv")))
                          (cv (if conv? (k-parse-conv-form (k-nth items 1)) (get k-conv-default)))
                          (items (if conv? (the (listof syn acyclic) (cons (car items) (cdr (cdr items)))) items))
                          (n (if conv? 4 n)))
                     (begin
                       (k-shape (= n 4) "`(subr effect (param …) result)`" s)
                       (let* ((e (k-parse-effect (k-nth items 1)))
                              (ps (k-parse-types (k-items-or-nil (k-nth items 2) "parameter types")))
                              (r (k-parse-type (k-nth items 3))))
                         (k-ty-new (ty-subr e ps r cv))))))
                  ((symbol=? hd 'proves)
                   (let ((usage "`(proves (<= type type))` or `(proves (poly ((name kind) …) (<= type type) (<= type type) …))`"))
                     (begin
                       (k-shape (= n 2) usage s)
                       (let* ((saved (get k-dscope)) (t (k-parse-proves (k-nth items 1) usage)))
                         (begin (set k-dscope saved) t)))))
                  ((symbol=? hd 'poly)
                   (begin
                     (k-shape (= n 3) "`(poly ((name kind) …) type)`" s)
                     (let* ((saved (get k-dscope))
                            (bs (k-parse-binders (k-nth items 1)))
                            (body (k-parse-type (k-nth items 2))))
                       (begin (set k-dscope saved) (k-ty-new (ty-poly bs body))))))
                  ((symbol=? hd 'nlist)
                   (begin
                     (k-shape (or (= n 3) (= n 4)) "`(nlist type size)` or `(nlist type size place)`" s)
                     (let* ((e (k-parse-type (k-nth items 1)))
                            (z (k-parse-size (k-nth items 2)))
                            (r (if (= n 4)
                                   (tagcase (k-parse-place (k-nth items 3)) (r-var (v) (r-frozen v #t)) (else y (r-frozen -1 #t)))
                                   (r-frozen -1 #t))))
                       (k-ty-new (ty-nlist e z r)))))
                  ((symbol=? hd 'nat)
                   (begin
                     (k-shape (= n 2) "`(nat size)`" s)
                     (k-ty-new (ty-nat (k-parse-size (k-nth items 1))))))
                  ((symbol=? hd 'ref)
                   (begin
                     (k-shape (= n 3) "`(ref type region)`" s)
                     (let* ((t (k-parse-type (k-nth items 1))) (r (k-parse-region (k-nth items 2))))
                       (k-ty-new (ty-ref t r)))))
                  ((symbol=? hd 'pairof)
                   (begin
                     (k-shape (= n 4) "`(pairof type type region)`" s)
                     (let* ((a (k-parse-type (k-nth items 1))) (b (k-parse-type (k-nth items 2)))
                            (r (k-parse-region (k-nth items 3))))
                       (k-ty-new (ty-pair a b r)))))
                  ((symbol=? hd 'dletrec) (k-parse-dletrec s items))
                  ((symbol=? hd 'mu) (k-parse-mu s items))
                  ((symbol=? hd 'listof)
                   (begin
                     (k-shape (= n 3) "`(listof type region)`" s)
                     (let* ((t (k-parse-type (k-nth items 1))) (r (k-parse-region (k-nth items 2)))
                            (slot (k-slot)) (pair (k-ty-new (ty-pair t slot r))))
                       (begin (k-set-link slot pair) slot))))
                  ((symbol=? hd 'prompt-tag)
                   (begin
                     (k-shape (= n 5) "`(prompt-tag answer payload effect region)`" s)
                     (let* ((a (k-parse-type (k-nth items 1))) (h (k-parse-type (k-nth items 2)))
                            (e (k-parse-effect (k-nth items 3))) (r (k-parse-region (k-nth items 4))))
                       (k-ty-new (ty-tag a h e r)))))
                  ((symbol=? hd 'composable)
                   (begin
                     (k-shape (= n 5) "`(composable argument answer effect region)`" s)
                     (let* ((t (k-parse-type (k-nth items 1))) (a (k-parse-type (k-nth items 2)))
                            (e (k-parse-effect (k-nth items 3))) (r (k-parse-region (k-nth items 4))))
                       (k-ty-new (ty-comp t a e r)))))
                  ((symbol=? hd 'bloblet)
                   (begin
                     (k-shape (= n 3) "`(bloblet (fields type …) region)`, or `(frozen type …)`" s)
                     (let* ((fields (k-nth items 1))
                            (parts (k-items fields "`(fields type …)`"))
                            (which (k-head parts)))
                       (if (or (string=? which "fields") (string=? which "frozen"))
                           (let* ((fs (k-parse-types (cdr parts))) (r (k-parse-region (k-nth items 2))))
                             (k-ty-new (ty-bloblet fs (string=? which "frozen") r)))
                           (k-sfail "`(fields type …)` or `(frozen type …)`" fields)))))
                  ((symbol=? hd 'productof) (k-ty-new (ty-product (k-parse-parts (cdr items) nil))))
                  ((symbol=? hd 'sumof) (k-ty-new (ty-sum (k-parse-parts (cdr items) nil))))
                  ((symbol=? hd 'arrayof)
                   (begin
                     (k-shape (= n 3) "`(arrayof type region)`" s)
                     (let* ((t (k-parse-type (k-nth items 1))) (r (k-parse-region (k-nth items 2))))
                       (k-ty-new (ty-array t r)))))
                  ((symbol=? hd 'icell)
                   (begin
                     (k-shape (= n 3) "`(icell type region)`" s)
                     (let* ((t (k-parse-type (k-nth items 1))) (r (k-parse-region (k-nth items 2))))
                       (k-ty-new (ty-icell t r)))))
                  ((symbol=? hd 'place)
                   (begin
                     (k-shape (= n 2) "`(place region)`" s)
                     (k-ty-new (ty-place (k-parse-place (k-nth items 1))))))
                  ((symbol=? hd 'mark-key)
                   (begin
                     (k-shape (= n 3) "`(mark-key type region)`" s)
                     (let* ((t (k-parse-type (k-nth items 1))) (r (k-parse-region (k-nth items 2))))
                       (k-ty-new (ty-markkey t r)))))
                  (else (k-sfail "expected a type" s))))))))
  ;; `(dletrec ((name type) …) type)`: each name gets a forwarding slot
  ;; before any body is read, so the bodies can refer to it and each other.
  (k-parse-dletrec (subr (maxeff checks spin) (syn (listof syn acyclic)) int)
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
  (k-parse-mu (subr (maxeff checks spin) (syn (listof syn acyclic)) int)
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
  (k-dletrec-fill (subr (maxeff checks spin) (k-slots) unit)
    (lambda (ss)
      (if (null? ss)
          #u
          (let ((t (k-parse-type (cdr (car ss)))))
            (begin (k-set-link (car (car ss)) t) (k-dletrec-fill (cdr ss)))))))
  ;; A use of a parametric abbreviation: its body, read with each parameter
  ;; bound to the description given for it.
  (k-expand-abbrev (subr (maxeff checks spin) (syn symbol (listof (productof (1 symbol) (2 int)) acyclic) syn (listof syn acyclic)) int)
    (lambda (s name ps body args)
      (cond
        ((not (= (k-length args) (k-length ps)))
         (k-sfail (k-cat5 (k-quote (symbol->string name)) " takes " (int->string (k-length ps)) " description(s), and has "
                          (int->string (k-length args)))
                  s))
        ((> (get k-expanding) 64)
         (k-sfail (string-append (k-quote (symbol->string name)) " expands without end: a type family may mention itself only with the same descriptions") s))
        (else
         (let* ((bound (k-abbrev-args ps args))
                (knot (k-knot-of (get k-knots) name bound)))
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
                            slot))))))))))
  (k-abbrev-args (subr (maxeff checks spin) ((listof (productof (1 symbol) (2 int)) acyclic) (listof syn acyclic)) k-scope)
    (lambda (ps args)
      (if (null? ps)
          nil
          (let* ((k (extract (car ps) 2))
                 (d (cond ((or (= k 2) (= k 4)) (ds-rec (k-parse-type (car args))))
                          ((= k 0) (ds-region (k-parse-region (car args))))
                          ((= k 3) (ds-region (k-parse-place (car args))))
                          ((= k 5) (ds-size (k-parse-size (car args))))
                          ((= k 6) (ds-conv (k-parse-conv (car args))))
                          (else (ds-eff (k-parse-effect (car args))))))
                 (rest (k-abbrev-args (cdr ps) (cdr args))))
            (cons (cons (extract (car ps) 1) d) rest))))))

;; Each polarity (0 covariant, 1 contravariant, 2 invariant) at which `v`
;; occurs in `t`, reached at polarity `at`.
(define k-flip (subr pure (int) int) (lambda (p) (cond ((= p 0) 1) ((= p 1) 0) (else 2))))
(define k-reg-is? (subr pure (k-region int) bool)
  (lambda (r v) (tagcase r (r-var (x) (= x v)) (r-frozen (x f) (= x v)) (else y #f))))
(define k-eff-var? (subr (maxeff (read @globals) (read @t)) (k-eff int) bool)
  (lambda (e v) (and (not (null? e)) (or (tagcase (car e) (a-var (x) (= x v)) (else y #f)) (k-eff-var? (cdr e) v)))))
(define k-eff-region-var? (subr (maxeff (read @globals) (read @t)) (k-eff int) bool)
  (lambda (e v)
    (and (not (null? e))
         (or (tagcase (car e)
               (a-read (r) (k-reg-is? r v)) (a-write (r) (k-reg-is? r v)) (a-alloc (r) (k-reg-is? r v))
               (a-goto (r) (k-reg-is? r v)) (a-comefrom (r) (k-reg-is? r v)) (a-await (r) (k-reg-is? r v))
               (else y #f))
             (k-eff-region-var? (cdr e) v)))))
(define k-pol-seen? (subr (maxeff (read @globals) (read @t)) ((listof (pairof int int @t) acyclic) int int) bool)
  (lambda (xs t at) (and (not (null? xs)) (or (and (= (car (car xs)) t) (= (cdr (car xs)) at)) (k-pol-seen? (cdr xs) t at)))))
(define-rec
  (k-polarity (subr (maxeff kstate spin) (int int int (ref (listof (pairof int int @t) acyclic) @t) (ref k-ids @t)) unit)
    (lambda (t v at seen found)
      (let ((t (k-resolve t)))
        (if (k-pol-seen? (get seen) t at)
            #u
            (letrec ((push (subr (maxeff (read @globals) kstate) (int) unit) (lambda (p) (set found (cons p (get found)))))
                     (reg (subr (maxeff (read @globals) kstate) (k-region) unit) (lambda (r) (if (k-reg-is? r v) (push 2) #u)))
                     (eff (subr (maxeff (read @globals) kstate) (k-eff int) unit)
                          (lambda (e p) (begin (if (k-eff-var? e v) (push p) #u) (if (k-eff-region-var? e v) (push 2) #u))))
                     (go (subr (maxeff (read @globals) kstate spin) (int int) unit) (lambda (x p) (k-polarity x v p seen found)))
                     (gos (subr (maxeff (read @globals) kstate spin) (k-ids int) unit) (lambda (xs p) (k-polarities xs v p seen found))))
              (begin
                (set seen (cons (cons t at) (get seen)))
                (tagcase (k-get t)
                  (ty-var (x) (if (= x v) (push at) #u))
                  (ty-subr (e ps r cv) (begin (eff e at) (gos ps (k-flip at)) (go r at)))
                  (ty-poly (bs body) (go body at))
                  (ty-ref (a r) (begin (reg r) (go a 2)))
                  (ty-array (a r) (begin (reg r) (go a 2)))
                  (ty-icell (a r) (begin (reg r) (go a 2)))
                  (ty-markkey (a r) (begin (reg r) (go a 2)))
                  (ty-pair (a b r)
                    (let ((p (tagcase r (r-frozen (q f) at) (else y 2)))) (begin (reg r) (go a p) (go b p))))
                  (ty-bloblet (fs z r) (begin (reg r) (gos fs (if z at 2))))
                  (ty-product (ps) (k-polarity-parts ps v at seen found))
                  (ty-sum (ps) (k-polarity-parts ps v at seen found))
                  (ty-tag (a h e r) (begin (reg r) (eff e 2) (go a 2) (go h 2)))
                  (ty-comp (a h e r) (begin (reg r) (eff e 2) (go a 2) (go h 2)))
                  (ty-place (r) (reg r))
                  (ty-named (g ds) (k-polarity-descs ds (extract (k-gen-of g) 3) v at seen found))
                  (ty-nlist (e z r) (begin (reg r) (go e at)))
                  (else y #u))))))))
  (k-polarities (subr (maxeff kstate spin) (k-ids int int (ref (listof (pairof int int @t) acyclic) @t) (ref k-ids @t)) unit)
    (lambda (ts v at seen found) (if (null? ts) #u (begin (k-polarity (car ts) v at seen found) (k-polarities (cdr ts) v at seen found)))))
  (k-polarity-parts (subr (maxeff kstate spin) (k-parts int int (ref (listof (pairof int int @t) acyclic) @t) (ref k-ids @t)) unit)
    (lambda (ps v at seen found)
      (if (null? ps) #u (begin (k-polarity (extract (car ps) 2) v at seen found) (k-polarity-parts (cdr ps) v at seen found)))))
  (k-polarity-descs (subr (maxeff kstate spin) ((listof k-desc acyclic) k-ids int int (ref (listof (pairof int int @t) acyclic) @t) (ref k-ids @t)) unit)
    (lambda (ds ws v at seen found)
      (if (null? ds)
          #u
          (let* ((w (car ws))
                 (p (cond ((or (= w 2) (= at 2)) 2) ((= w 0) at) (else (k-flip at)))))
            (begin
              (tagcase (car ds)
                (dt (x) (k-polarity x v p seen found))
                (dr (r) (if (k-reg-is? r v) (set found (cons 2 (get found))) #u))
                (de (e) (begin (if (k-eff-var? e v) (set found (cons p (get found))) #u)
                               (if (k-eff-region-var? e v) (set found (cons 2 (get found))) #u)))
                (dz (z) #u)
                (dc (c) #u))
              (k-polarity-descs (cdr ds) (cdr ws) v at seen found)))))))
(define k-all-ints? (subr (read @globals) (k-ids int) bool)
  (lambda (xs n) (or (null? xs) (and (= (car xs) n) (k-all-ints? (cdr xs) n)))))
;; Whether the `g`th generative type's representation bears out the variance
;; declared for its parameters.
(define k-check-variance (subr (maxeff checks spin) (int syn) unit)
  (lambda (g s)
    (let ((gen (k-gen-of g)))
      (letrec ((each (subr (maxeff (read @globals) checks spin) (k-binders k-ids) unit)
                     (lambda (bs vs)
                       (if (null? bs)
                           #u
                           (let ((v (extract (car bs) 1)) (want (car vs)))
                             (begin
                               (if (= want 2)
                                   #u
                                   (let ((found (the (ref k-ids @t) (new nil))))
                                     (begin
                                       (k-polarity (extract gen 4) v 0 (the (ref (listof (pairof int int @t) acyclic) @t) (new nil)) found)
                                       (if (k-all-ints? (get found) want)
                                           #u
                                           (k-sfail (k-cat5 (k-quote (symbol->string (k-dvar-name v))) " is declared "
                                                            (if (= want 0) "covariant (+)" "contravariant (-)")
                                                            " in " (string-append (k-quote (symbol->string (extract gen 1)))
                                                                                  ", but occurs where it may not"))
                                                    s)))))
                               (each (cdr bs) (cdr vs))))))))
        (each (extract gen 2) (extract gen 3))))))
;; `(define-generative (name (param kind [+|-]) …) rep)`, or with no
;; parameters `(define-generative name rep)`: a new type, equal only to
;; itself, converted by `up-name` and `down-name`.
(define k-gen-params (subr (maxeff checks spin) ((listof syn acyclic) int) (productof (1 k-binders) (2 k-ids)))
  (lambda (ps depth)
    (if (null? ps)
        (product (1 (the k-binders nil)) (2 (the k-ids nil)))
        (let* ((p (car ps))
               (items (k-items p "a parameter"))
               (n (k-length items))
               (v (cond ((= n 2) 2)
                        ((= n 3)
                         (let ((x (k-nth items 2)))
                           (cond ((and (syn-symbol? x) (string=? (syn-name x) "+")) 0)
                                 ((and (syn-symbol? x) (string=? (syn-name x) "-")) 1)
                                 (else (k-sfail "a parameter's variance is `+` or `-`" x)))))
                        (else (k-sfail "a parameter is `(name kind)`, `(name kind +)` or `(name kind -)`" p))))
               (name (k-name-of (car items) "a parameter's name"))
               (kind (k-parse-kind (k-nth items 1)))
               (checked (if (and (not (= v 2)) (or (= kind 0) (= kind 3)))
                            (k-sfail "a region or place parameter is invariant: it names where data is" p)
                            #u))
               (dv (k-new-dvar-of name kind))
               (pushed (k-push-desc name (ds-var dv kind)))
               (rest (k-gen-params (cdr ps) depth)))
          (product (1 (the k-binders (cons (product (1 dv) (2 kind)) (extract rest 1))))
                   (2 (the k-ids (cons v (extract rest 2)))))))))
(define k-define-generative (subr (maxeff checks spin) (syn syn) symbol)
  (lambda (head rep)
    (let* ((hs (tagcase head (lst (items d a b) items) (else x (the (listof syn acyclic) nil))))
           (name-syn (if (null? hs) head (car hs)))
           (ps (if (null? hs) (the (listof syn acyclic) nil) (cdr hs)))
           (name (k-name-of name-syn "a generative type's name"))
           (saved (get k-dscope))
           (params (k-gen-params ps 0))
           (g (get k-ngens))
           (slot (k-slot)))
      (begin
        (set k-gens (cons (product (1 name) (2 (extract params 1)) (3 (extract params 2)) (4 slot)) (get k-gens)))
        (set k-ngens (+ g 1))
        ;; In scope in its own representation: recursion through the name.
        (k-push-desc name (ds-gen g))
        (let ((r (k-parse-type rep)))
          (begin
            (set k-dscope saved)
            (k-set-link slot r)
            (k-check-variance g rep)
            (k-push-desc name (ds-gen g))
            name))))))

;; `(define-type name type)`: `name` stands for the type from here on, and
;; may appear in its own definition.
(define k-define-type (subr (maxeff checks spin) (symbol syn int int) int)
  (lambda (name def a b)
    (let ((slot (k-slot)))
      (begin
        (k-push-desc name (ds-rec slot))
        (let ((t (k-parse-type def)))
          (begin (k-set-link slot t) (k-grounded slot a b) slot))))))

;; A `proj` argument: which kind it is shows in its shape, or, for a bare
;; name, in how the name is bound.
(define k-parse-d (subr (maxeff checks spin) (syn) k-desc)
  (lambda (s)
    (if (tagcase s (atom (d a b) (datum-int? d)) (else x #f))
        ;; A natural number can only be a size.
        (dz (k-parse-size s))
    (if (syn-symbol? s)
        (let* ((n (syn-name s)) (sym (string->symbol n)))
          (cond ((k-at-name? n) (dr (k-region-constant sym)))
                ((string=? n "pure") (de nil))
                ((string=? n "spin") (de (k-one (a-spin))))
                ((string=? n "const") (dr (r-frozen -1 #f)))
                ((string=? n "acyclic") (dr (r-frozen -1 #t)))
                ((string=? n "finite") (dz (sz-finite)))
                ((string=? n "heap") (dr (r-heap)))
                (else
                 (let ((d (k-lookup-desc sym))
                       (conv? (or (string=? n "cellular") (string=? n "native") (string=? n "fx"))))
                   (if (null? d)
                       (if conv? (dc (k-parse-conv s)) (dt (k-parse-type s)))
                       (tagcase (car d)
                         (ds-var (v k)
                           (cond ((or (= k 0) (= k 3)) (dr (r-var v))) ((= k 1) (de (k-one (a-var v)))) ((= k 5) (dz (k-size-var v)))
                                 ((= k 6) (dc (cv-var v)))
                                 (else (if conv? (dc (k-parse-conv s)) (dt (k-parse-type s))))))
                         (ds-eff (e) (de e))
                         (ds-size (z) (dz z))
                         (ds-conv (c) (dc c))
                         (else x (if conv? (dc (k-parse-conv s)) (dt (k-parse-type s))))))))))
        (let ((hd (k-head (k-items s "a description"))))
          (cond ((or (string=? hd "read") (string=? hd "write") (string=? hd "alloc") (string=? hd "goto")
                     (string=? hd "comefrom") (string=? hd "await") (string=? hd "maxeff"))
                 (de (k-parse-effect s)))
                ((or (string=? hd "+") (string=? hd "-")) (dz (k-parse-size s)))
                (else (dt (k-parse-type s))))))))) 

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

;;; ------------------------------------------------------------ subtyping
;;; `a ≤ b`. Recursive types are compared coinductively: a pair already
;;; being compared is assumed to hold.

(define-type k-trail (ref (listof (pairof int int @t) acyclic) @t))
(define k-trail-has? (subr (maxeff (read @globals) (read @t)) ((listof (pairof int int @t) acyclic) int int) bool)
  (lambda (ps a b) (cond ((null? ps) #f) ((and (= (car (car ps)) a) (= (cdr (car ps)) b)) #t) (else (k-trail-has? (cdr ps) a b)))))
(define k-bool=? (subr pure (bool bool) bool) (lambda (x y) (if x y (not y))))
(define k-part-find (subr (maxeff (read @globals) (read @t)) (k-parts symbol) int)
  (lambda (ps l) (cond ((null? ps) -1) ((symbol=? (extract (car ps) 1) l) (extract (car ps) 2)) (else (k-part-find (cdr ps) l)))))

;; A subtype question's binder environment, for one side: each `poly`
;; binder in scope, by the name its pair of binders was given, so bodies are
;; compared as they are, not substituted, and a cycle through a `poly` comes
;; back to a pair, and an environment, already on the trail.
(define-type k-benv (listof (pairof int int @t) acyclic))
(define k-benv-var (subr (maxeff (read @globals) (read @t)) (k-benv int) int)
  (lambda (env v) (cond ((null? env) v) ((= (car (car env)) v) (cdr (car env))) (else (k-benv-var (cdr env) v)))))
;; `env` with `v` named `l`, in place of any name it had: re-entering a scope
;; shadows it, so the environments stay finitely many.
;; Whether a procedure called in convention `a` may be used as one called
;; in `b`: the same, or any of FX-26's own as `fx`; binders by the binders
;; they stand for.
(define k-conv-sub? (subr (maxeff (read @globals) (read @t)) (k-conv k-conv k-benv k-benv) bool)
  (lambda (a b ea eb)
    (tagcase a
      (cv-var (x) (tagcase b (cv-var (y) (= (k-benv-var ea x) (k-benv-var eb y))) (else z #f)))
      (else y (or (k-conv=? a b) (tagcase b (cv-fx () #t) (else z #f)))))))
;; Whether two conventions are the same, binders by what they stand for.
(define k-conv-same? (subr (maxeff (read @globals) (read @t)) (k-conv k-conv k-benv k-benv) bool)
  (lambda (a b ea eb)
    (tagcase a
      (cv-var (x) (tagcase b (cv-var (y) (= (k-benv-var ea x) (k-benv-var eb y))) (else z #f)))
      (else y (k-conv=? a b)))))
(define k-benv-set (subr (maxeff (read @globals) (read @t) (alloc @t)) (k-benv int int) k-benv)
  (lambda (env v l)
    (letrec ((drop (subr (maxeff (read @globals) (read @t) (alloc @t)) (k-benv) k-benv)
               (lambda (e) (cond ((null? e) nil) ((= (car (car e)) v) (cdr e)) (else (cons (car e) (drop (cdr e))))))))
      (the k-benv (cons (the (pairof int int @t) (cons v l)) (drop env))))))
(define k-benv-within? (subr (maxeff (read @globals) (read @t)) (k-benv k-benv) bool)
  (lambda (x y) (or (null? x) (and (= (k-benv-var y (car (car x))) (cdr (car x))) (k-benv-within? (cdr x) y)))))
(define k-benv=? (subr (maxeff (read @globals) (read @t)) (k-benv k-benv) bool)
  (lambda (x y) (and (= (k-length x) (k-length y)) (k-benv-within? x y))))
;; `a ≤ b` for frozen data: the same, or finite data seen as possibly
;; cyclic, in one place.
(define k-frozen-le? (subr (maxeff (read @globals) spin) (k-region k-region) bool)
  (lambda (a b)
    (or (k-region=? a b)
        (tagcase a
          (r-frozen (p f) (and f (tagcase b (r-frozen (q g) (and (= p q) (not g))) (else y #f))))
          (else y #f)))))
(define k-benv-region (subr (maxeff (read @globals) (read @t)) (k-benv k-region) k-region)
  (lambda (env r)
    (if (null? env)
        r
        (tagcase r
          (r-var (v) (r-var (k-benv-var env v)))
          (r-frozen (p f) (if (< p 0) r (r-frozen (k-benv-var env p) f)))
          (else y r)))))
(define k-benv-effect (subr (maxeff (read @globals) (read @t) (alloc @t)) (k-benv k-eff) k-eff)
  (lambda (env e)
    (if (or (null? env) (null? e))
        e
        (let ((x (car e)) (rest (k-benv-effect env (cdr e))))
          (cons (tagcase x
                  (a-read (r) (a-read (k-benv-region env r)))
                  (a-write (r) (a-write (k-benv-region env r)))
                  (a-alloc (r) (a-alloc (k-benv-region env r)))
                  (a-goto (r) (a-goto (k-benv-region env r)))
                  (a-comefrom (r) (a-comefrom (k-benv-region env r)))
                  (a-await (r) (a-await (k-benv-region env r)))
                  (a-spin () x)
                  (a-var (v) (a-var (k-benv-var env v))))
                rest)))))
;; What one subtype question remembers: the pairs assumed (FX-87's trail),
;; each with the environments it was asked under; and the names given to
;; pairs of `poly` binders, by the pair of nodes and the position.
(define-type k-strail (ref (listof (productof (1 int) (2 int) (3 k-benv) (4 k-benv)) acyclic) @t))
(define-type k-labels (ref (listof (productof (1 int) (2 int) (3 int) (4 int)) acyclic) @t))
(define k-strail-has? (subr (maxeff (read @globals) (read @t)) ((listof (productof (1 int) (2 int) (3 k-benv) (4 k-benv)) acyclic) int int k-benv k-benv) bool)
  (lambda (ps a b ea eb)
    (and (not (null? ps))
         (or (and (= (extract (car ps) 1) a) (and (= (extract (car ps) 2) b)
                  (and (k-benv=? (extract (car ps) 3) ea) (k-benv=? (extract (car ps) 4) eb))))
             (k-strail-has? (cdr ps) a b ea eb)))))
(define k-label (subr kstate (k-labels int int int) int)
  (lambda (labels a b i)
    (letrec ((find (subr (maxeff (read @globals) (read @t)) ((listof (productof (1 int) (2 int) (3 int) (4 int)) acyclic)) int)
               (lambda (ls)
                 (cond ((null? ls) 0)
                       ((and (= (extract (car ls) 1) a) (and (= (extract (car ls) 2) b) (= (extract (car ls) 3) i)))
                        (extract (car ls) 4))
                       (else (find (cdr ls)))))))
      (let ((found (find (get labels))))
        (if (< found 0)
            found
            (let ((l (- -1000 (k-length (get labels)))))
              (begin (set labels (cons (product (1 a) (2 b) (3 i) (4 l)) (get labels))) l)))))))

;; Name each pair of binders of two `poly` nodes `a` and `b` by the pair and
;; its position: the environments inside, for each side.
(define k-name-binders (subr kstate (k-binders k-binders int int int k-benv k-benv k-labels) (pairof k-benv k-benv @t))
  (lambda (ba bb a b i ea eb labels)
    (if (null? ba)
        (cons ea eb)
        (let ((l (k-label labels a b i)))
          (k-name-binders (cdr ba) (cdr bb) a b (+ i 1)
                          (k-benv-set ea (extract (car ba) 1) l) (k-benv-set eb (extract (car bb) 1) l) labels)))))
;; Bounded region binders must have the same bounds.
(define k-same-bounds? (subr (maxeff (read @globals) (read @t) (alloc @t) spin) (k-binders k-binders k-benv k-benv) bool)
  (lambda (ba bb ea eb)
    (or (null? ba)
        (let ((x (k-bound-of (extract (car ba) 1))) (y (k-bound-of (extract (car bb) 1))))
          (and (cond ((and (null? x) (null? y)) #t)
                     ((or (null? x) (null? y)) #f)
                     (else (k-region=? (k-benv-region ea (car x)) (k-benv-region eb (car y)))))
               (k-same-bounds? (cdr ba) (cdr bb) ea eb))))))

(define-rec
  (k-subs-contra (subr (maxeff kstate spin) (k-ids k-ids k-benv k-benv k-strail k-labels) bool)
    (lambda (xs ys ea eb trail labels)
      (cond ((null? xs) (null? ys)) ((null? ys) #f)
            (else (and (k-sub (car ys) (car xs) eb ea trail labels) (k-subs-contra (cdr xs) (cdr ys) ea eb trail labels))))))
  (k-inv (subr (maxeff kstate spin) (int int k-benv k-benv k-strail k-labels) bool)
    (lambda (x y ea eb trail labels) (and (k-sub x y ea eb trail labels) (k-sub y x eb ea trail labels))))
  (k-sub-callable (subr (maxeff kstate spin) (k-callable k-callable k-benv k-benv k-strail k-labels) bool)
    (lambda (ca cb ea eb trail labels)
      (and (= (k-length (extract ca 2)) (k-length (extract cb 2)))
           (k-within? (k-benv-effect ea (extract ca 1)) (k-benv-effect eb (extract cb 1)))
           (k-subs-contra (extract ca 2) (extract cb 2) ea eb trail labels)
           (k-sub (extract ca 3) (extract cb 3) ea eb trail labels))))
  ;; `a ≤ b`. Recursive types are compared coinductively: a pair already
  ;; being compared is assumed to hold, which is what makes comparing two
  ;; cycles terminate: FX-87's trail, Amadio and Cardelli's assumption set.
  ;; Every rule is a conjunction, so an assumption left behind by a failed
  ;; comparison is never relied on: the failure is the answer.
  ;; `a ≤ b`: by the rules; failing that, by a lemma. A comparison that
  ;; failed may have left assumptions on the trail, so it is put back as it
  ;; was; a lemma's hypotheses are compared assuming what is being shown.
  (k-sub (subr (maxeff kstate spin) (int int k-benv k-benv k-strail k-labels) bool)
    (lambda (a b ea eb trail labels)
      (if (null? (get k-lemmas))
          (k-sub-rules a b ea eb trail labels)
          (let ((ra (k-resolve a)) (rb (k-resolve b)))
            (if (not (k-lemma-may-apply? (get k-lemmas) ra rb))
                (k-sub-rules a b ea eb trail labels)
                (let ((st (get trail)) (sl (get labels)))
                  (if (k-sub-rules a b ea eb trail labels)
                      #t
                      (begin
                        (set trail st)
                        (set labels sl)
                        (set trail (cons (product (1 ra) (2 rb) (3 ea) (4 eb)) (get trail)))
                        (k-sub-by-lemmas (k-lemma-instances (the (listof k-lemma acyclic) (reverse (get k-lemmas))) ra rb)
                                         ea eb trail labels)))))))))
  (k-sub-by-lemmas (subr (maxeff kstate spin) ((listof k-hyps acyclic) k-benv k-benv k-strail k-labels) bool)
    (lambda (insts ea eb trail labels)
      (and (not (null? insts))
           (let ((st (get trail)) (sl (get labels)))
             (or (k-sub-hyps (car insts) ea eb trail labels)
                 (begin (set trail st) (set labels sl) (k-sub-by-lemmas (cdr insts) ea eb trail labels)))))))
  (k-sub-hyps (subr (maxeff kstate spin) (k-hyps k-benv k-benv k-strail k-labels) bool)
    (lambda (hs ea eb trail labels)
      (or (null? hs) (and (k-sub (car (car hs)) (cdr (car hs)) ea eb trail labels) (k-sub-hyps (cdr hs) ea eb trail labels)))))
  (k-same-ty? (subr (maxeff kstate spin) (int int) bool)
    (lambda (x y)
      (and (k-sub x y (the k-benv nil) (the k-benv nil) (the k-strail (new nil)) (the k-labels (new nil)))
           (k-sub y x (the k-benv nil) (the k-benv nil) (the k-strail (new nil)) (the k-labels (new nil))))))
  ;; Each lemma of `ls` that fits `a` and `b`: its hypotheses, instantiated.
  (k-lemma-instances (subr (maxeff kstate spin) ((listof k-lemma acyclic) int int) (listof k-hyps acyclic))
    (lambda (ls a b)
      (if (null? ls)
          nil
          (let* ((l (car ls))
                 (m (the (ref k-map @t) (new nil)))
                 (seen (the (ref (listof (pairof int int @t) acyclic) @t) (new nil)))
                 (fits (and (k-match-ty l (extract l 2) a m seen) (k-match-ty l (extract l 3) b m seen)
                            (k-all-bound? (extract l 1) (get m))))
                 (mine (if fits (the (listof k-hyps acyclic) (cons (k-subst-hyps (extract l 4) (get m)) nil)) (the (listof k-hyps acyclic) nil)))
                 (rest (k-lemma-instances (cdr ls) a b)))
            (if (null? mine) rest (the (listof k-hyps acyclic) (cons (car mine) rest)))))))
  ;; Whether `t` is `pat` with the lemma's binders standing for something,
  ;; recorded in `m`.
  (k-match-ty (subr (maxeff kstate spin) (k-lemma int int (ref k-map @t) (ref (listof (pairof int int @t) acyclic) @t)) bool)
    (lambda (l pat t m seen)
      (let ((pat (k-resolve pat)) (t (k-resolve t)))
        (if (k-pair-seen? (get seen) pat t)
            #t
            (begin
              (set seen (cons (cons pat t) (get seen)))
              (let ((bs (extract l 1)) (tt (k-get t)))
                (letrec ((mt (subr (maxeff (read @globals) kstate spin) (int int) bool) (lambda (x y) (k-match-ty l x y m seen)))
                         (mr (subr (maxeff (read @globals) kstate spin) (k-region k-region) bool) (lambda (r q) (k-match-region bs r q m)))
                         (same (subr (maxeff (read @globals) kstate spin) () bool) (lambda () (k-same-ty? pat t))))
                  (tagcase (k-get pat)
                    (ty-var (v)
                      (if (k-binder-has? bs v)
                          (let ((f (k-map-find (get m) v)))
                            (if (null? f)
                                (begin (set m (cons (cons v (dt t)) (get m))) #t)
                                (tagcase (cdr (car f)) (dt (u) (k-same-ty? u t)) (else z #f))))
                          (same)))
                    (ty-named (g xs) (tagcase tt (ty-named (h ys) (and (= g h) (k-match-descs l xs ys m seen))) (else z (same))))
                    (ty-pair (a1 b1 r1) (tagcase tt (ty-pair (a2 b2 r2) (and (mr r1 r2) (mt a1 a2) (mt b1 b2))) (else z (same))))
                    (ty-ref (x r) (tagcase tt (ty-ref (y q) (and (mr r q) (mt x y))) (else z (same))))
                    (ty-array (x r) (tagcase tt (ty-array (y q) (and (mr r q) (mt x y))) (else z (same))))
                    (ty-icell (x r) (tagcase tt (ty-icell (y q) (and (mr r q) (mt x y))) (else z (same))))
                    (ty-product (ps) (tagcase tt (ty-product (qs) (k-match-parts l ps qs m seen)) (else z (same))))
                    (ty-sum (ps) (tagcase tt (ty-sum (qs) (k-match-parts l ps qs m seen)) (else z (same))))
                    (ty-subr (e1 p1 r1 c1)
                      (tagcase tt
                        (ty-subr (e2 p2 r2 c2)
                          (and (k-conv=? c1 c2) (k-eff=? e1 e2) (= (k-length p1) (k-length p2)) (k-match-list l p1 p2 m seen) (mt r1 r2)))
                        (else z (same))))
                    (else z (same))))))))))
  (k-match-list (subr (maxeff kstate spin) (k-lemma k-ids k-ids (ref k-map @t) (ref (listof (pairof int int @t) acyclic) @t)) bool)
    (lambda (l xs ys m seen) (or (null? xs) (and (k-match-ty l (car xs) (car ys) m seen) (k-match-list l (cdr xs) (cdr ys) m seen)))))
  (k-match-parts (subr (maxeff kstate spin) (k-lemma k-parts k-parts (ref k-map @t) (ref (listof (pairof int int @t) acyclic) @t)) bool)
    (lambda (l ps qs m seen)
      (and (= (k-length ps) (k-length qs))
           (letrec ((each (subr (maxeff (read @globals) kstate spin) (k-parts k-parts) bool)
                          (lambda (ps qs)
                            (or (null? ps)
                                (and (symbol=? (extract (car ps) 1) (extract (car qs) 1))
                                     (k-match-ty l (extract (car ps) 2) (extract (car qs) 2) m seen)
                                     (each (cdr ps) (cdr qs)))))))
             (each ps qs)))))
  (k-match-descs (subr (maxeff kstate spin) (k-lemma (listof k-desc acyclic) (listof k-desc acyclic) (ref k-map @t) (ref (listof (pairof int int @t) acyclic) @t)) bool)
    (lambda (l xs ys m seen)
      (or (null? xs)
          (and (tagcase (car xs)
                 (dt (a) (tagcase (car ys) (dt (b) (k-match-ty l a b m seen)) (else z #f)))
                 (dr (r) (tagcase (car ys) (dr (q) (k-match-region (extract l 1) r q m)) (else z #f)))
                 (de (d) (tagcase (car ys) (de (e) (k-match-effect (extract l 1) d e m)) (else z #f)))
                 (dz (a) (tagcase (car ys) (dz (b) (k-size=? a b)) (else z #f)))
                 (dc (a) (tagcase (car ys) (dc (b) (k-conv=? a b)) (else z #f))))
               (k-match-descs l (cdr xs) (cdr ys) m seen)))))
  (k-match-region (subr (maxeff kstate spin) (k-binders k-region k-region (ref k-map @t)) bool)
    (lambda (bs r q m)
      (tagcase r
        (r-var (v)
          (if (k-binder-has? bs v)
              (let ((f (k-map-find (get m) v)))
                (if (null? f) (begin (set m (cons (cons v (dr q)) (get m))) #t) (tagcase (cdr (car f)) (dr (x) (k-region=? x q)) (else z #f))))
              (k-region=? r q)))
        (else z (k-region=? r q)))))
  (k-match-effect (subr (maxeff kstate spin) (k-binders k-eff k-eff (ref k-map @t)) bool)
    (lambda (bs d e m)
      (let ((v (if (and (not (null? d)) (null? (cdr d))) (tagcase (car d) (a-var (x) (if (k-binder-has? bs x) x -1)) (else z -1)) -1)))
        (if (< v 0)
            (k-eff=? d e)
            (let ((f (k-map-find (get m) v)))
              (if (null? f) (begin (set m (cons (cons v (de e)) (get m))) #t) (tagcase (cdr (car f)) (de (x) (k-eff=? x e)) (else z #f))))))))
  ;; `a ≤ b` by the rules alone.
  (k-sub-rules (subr (maxeff kstate spin) (int int k-benv k-benv k-strail k-labels) bool)
    (lambda (a b ea eb trail labels)
      (let ((a (k-resolve a)) (b (k-resolve b)))
        (cond
          ((and (= a b) (and (null? ea) (null? eb))) #t)
          ((k-strail-has? (get trail) a b ea eb) #t)
          (else
           (begin
             (set trail (cons (product (1 a) (2 b) (3 ea) (4 eb)) (get trail)))
             (let* ((ta (k-get a)) (tb (k-get b))
                    (same-named (tagcase ta (ty-named (g xs) (tagcase tb (ty-named (h ys) (= g h)) (else z #f))) (else z #f)))
                    (a-void (tagcase ta (ty-void () #t) (else z #f)))
                    ;; Inside a generative type's own conversions, its name
                    ;; is its representation; everywhere else only itself.
                    (a-open (tagcase ta (ty-named (g xs) (k-has-id? (get k-transparent) g)) (else z #f)))
                    (b-open (tagcase tb (ty-named (g xs) (k-has-id? (get k-transparent) g)) (else z #f))))
               (cond
                ((and (not same-named) (not a-void) a-open)
                 (tagcase ta (ty-named (g xs) (k-sub (k-unfold g xs) b ea eb trail labels)) (else z #f)))
                ((and (not same-named) (not a-void) b-open)
                 (tagcase tb (ty-named (g ys) (k-sub a (k-unfold g ys) ea eb trail labels)) (else z #f)))
                (else
               (if (and (tagcase ta (ty-comp (x y e r) #t) (else z #f)) (tagcase tb (ty-subr (e ps r cv) #t) (else z #f)))
                   (k-sub-callable (car (k-as-subr a)) (car (k-as-subr b)) ea eb trail labels)
                   (tagcase ta
                     (ty-void () #t)
                     (ty-base (x) (tagcase tb (ty-base (y) (symbol=? x y)) (else z #f)))
                     ;; A natural is an integer; one of a known size, a natural.
                     (ty-nat (m) (tagcase tb (ty-base (y) (symbol=? y 'int)) (ty-nat (n) (k-size-le? m n)) (else z #f)))
                     (ty-var (x) (tagcase tb (ty-var (y) (= (k-benv-var ea x) (k-benv-var eb y))) (else z #f)))
                     (ty-subr (e ps r cv)
                       (tagcase tb
                         (ty-subr (e2 ps2 r2 cv2)
                           (and (k-conv-sub? cv cv2 ea eb) (k-sub-callable (car (k-as-subr a)) (car (k-as-subr b)) ea eb trail labels)))
                         (else z #f)))
                     (ty-ref (x r) (tagcase tb (ty-ref (y s) (and (k-region=? (k-benv-region ea r) (k-benv-region eb s)) (k-inv x y ea eb trail labels))) (else z #f)))
                     (ty-array (x r) (tagcase tb (ty-array (y s) (and (k-region=? (k-benv-region ea r) (k-benv-region eb s)) (k-inv x y ea eb trail labels))) (else z #f)))
                     (ty-icell (x r) (tagcase tb (ty-icell (y s) (and (k-region=? (k-benv-region ea r) (k-benv-region eb s)) (k-inv x y ea eb trail labels))) (else z #f)))
                     (ty-place (r) (tagcase tb (ty-place (s) (k-region=? (k-benv-region ea r) (k-benv-region eb s))) (else z #f)))
                     (ty-pair (x1 x2 r)
                       (tagcase tb
                         (ty-pair (y1 y2 s)
                           (and (k-frozen-le? (k-benv-region ea r) (k-benv-region eb s))
                                ;; Frozen pairs cannot be written, so, as a
                                ;; frozen bloblet's fields, their contents are
                                ;; covariant; and finite data may be seen as
                                ;; possibly cyclic.
                                (if (tagcase r (r-frozen (p f) #t) (else z #f))
                                    (and (k-sub x1 y1 ea eb trail labels) (k-sub x2 y2 ea eb trail labels))
                                    (and (k-inv x1 y1 ea eb trail labels) (k-inv x2 y2 ea eb trail labels)))))
                         ;; A finite list is a `nlist` of some length.
                         (ty-nlist (y sz s)
                           (and (tagcase sz (sz-finite () #t) (else z #f))
                                (tagcase r (r-frozen (p f) f) (else z #f))
                                (k-frozen-le? (k-benv-region ea r) (k-benv-region eb s))
                                (k-sub x1 y ea eb trail labels)
                                (k-sub x2 b ea eb trail labels)))
                         (else z #f)))
                     (ty-tag (a1 h1 d1 r1)
                       (tagcase tb
                         (ty-tag (a2 h2 d2 r2)
                           (and (k-region=? (k-benv-region ea r1) (k-benv-region eb r2)) (k-eff=? (k-benv-effect ea d1) (k-benv-effect eb d2))
                                (k-inv a1 a2 ea eb trail labels) (k-inv h1 h2 ea eb trail labels)))
                         (else z #f)))
                     (ty-comp (t1 a1 d1 r1)
                       (tagcase tb
                         (ty-comp (t2 a2 d2 r2)
                           (and (k-region=? (k-benv-region ea r1) (k-benv-region eb r2)) (k-within? (k-benv-effect ea d1) (k-benv-effect eb d2))
                                (k-sub t2 t1 eb ea trail labels) (k-sub a1 a2 ea eb trail labels)))
                         (else z #f)))
                     (ty-markkey (x r) (tagcase tb (ty-markkey (y s) (and (k-region=? (k-benv-region ea r) (k-benv-region eb s)) (k-inv x y ea eb trail labels))) (else z #f)))
                     (ty-bloblet (fa za r)
                       (tagcase tb
                         (ty-bloblet (fb zb s)
                           (and (if za (k-frozen-le? (k-benv-region ea r) (k-benv-region eb s)) (k-region=? (k-benv-region ea r) (k-benv-region eb s)))
                                (k-bool=? za zb) (= (k-length fa) (k-length fb))
                                (k-sub-fields fa fb za ea eb trail labels)))
                         (else z #f)))
                     (ty-product (pa)
                       (tagcase tb (ty-product (pb) (and (= (k-length pa) (k-length pb)) (k-sub-product pa pb ea eb trail labels))) (else z #f)))
                     (ty-sum (sa) (tagcase tb (ty-sum (sb) (k-sub-sum sa sb ea eb trail labels)) (else z #f)))
                     (ty-poly (ba xa)
                       (tagcase tb
                         (ty-poly (bb xb)
                           (and (= (k-length ba) (k-length bb)) (k-same-kinds? ba bb)
                                (let* ((named (k-name-binders ba bb a b 0 ea eb labels))
                                       (ia (car named)) (ib (cdr named)))
                                  (and (k-same-bounds? ba bb ia ib)
                                       (k-sub xa xb ia ib trail labels)))))
                         (else z #f)))
                     ;; A `nlist` is frozen, so covariant in its elements, and
                     ;; forgets its size to `finite`; any `nlist` is a finite
                     ;; list, and a finite list a `nlist` of some length.
                     (ty-nlist (x m r)
                       (tagcase tb
                         (ty-nlist (y n s)
                           (and (k-frozen-le? (k-benv-region ea r) (k-benv-region eb s)) (k-size-le? m n) (k-sub x y ea eb trail labels)))
                         (ty-pair (y tail s)
                           (let ((k (k-size-as-lit m)))
                             (and (k-frozen-le? (k-benv-region ea r) (k-benv-region eb s))
                                  (k-sub x y ea eb trail labels)
                                  (tagcase m
                                    ;; A `nlist` of some length has for its tail the same type.
                                    (sz-finite () (k-sub a tail ea eb trail labels))
                                    (else w (or (= k 0) (k-sub (k-ty-new (ty-nlist x (k-tail-size m) r)) tail ea eb trail labels)))))))
                         (else z #f)))
                     ;; A generative type is related only to itself, argument
                     ;; by argument, as its variance says.
                     (ty-named (g xs)
                       (tagcase tb
                         (ty-named (h ys) (and (= g h) (k-sub-descs xs ys (extract (k-gen-of g) 3) ea eb trail labels)))
                         (else z #f)))
                     (else z #f))))))))))))
  (k-sub-descs (subr (maxeff kstate spin) ((listof k-desc acyclic) (listof k-desc acyclic) k-ids k-benv k-benv k-strail k-labels) bool)
    (lambda (xs ys vs ea eb trail labels)
      (or (null? xs)
          (and (let ((v (car vs)))
                 (tagcase (car xs)
                   (dt (x)
                     (tagcase (car ys)
                       (dt (y) (cond ((= v 0) (k-sub x y ea eb trail labels))
                                     ((= v 1) (k-sub y x eb ea trail labels))
                                     (else (k-inv x y ea eb trail labels))))
                       (else z #f)))
                   (dr (r) (tagcase (car ys) (dr (q) (k-region=? (k-benv-region ea r) (k-benv-region eb q))) (else z #f)))
                   (de (d)
                     (tagcase (car ys)
                       (de (e) (let ((d2 (k-benv-effect ea d)) (e2 (k-benv-effect eb e)))
                                 (cond ((= v 0) (k-within? d2 e2)) ((= v 1) (k-within? e2 d2)) (else (k-eff=? d2 e2)))))
                       (else z #f)))
                   (dz (m) (tagcase (car ys) (dz (n) (k-size-eq? m n)) (else z #f)))
                   (dc (c) (tagcase (car ys) (dc (d) (k-conv-same? c d ea eb)) (else z #f)))))
               (k-sub-descs (cdr xs) (cdr ys) (cdr vs) ea eb trail labels)))))
  (k-sub-fields (subr (maxeff kstate spin) (k-ids k-ids bool k-benv k-benv k-strail k-labels) bool)
    (lambda (fa fb frozen ea eb trail labels)
      (cond ((null? fa) #t)
            (else (and (k-sub (car fa) (car fb) ea eb trail labels) (or frozen (k-sub (car fb) (car fa) eb ea trail labels))
                       (k-sub-fields (cdr fa) (cdr fb) frozen ea eb trail labels))))))
  (k-sub-product (subr (maxeff kstate spin) (k-parts k-parts k-benv k-benv k-strail k-labels) bool)
    (lambda (pa pb ea eb trail labels)
      (cond ((null? pa) #t)
            (else (and (symbol=? (extract (car pa) 1) (extract (car pb) 1))
                       (k-sub (extract (car pa) 2) (extract (car pb) 2) ea eb trail labels)
                       (k-sub-product (cdr pa) (cdr pb) ea eb trail labels))))))
  (k-sub-sum (subr (maxeff kstate spin) (k-parts k-parts k-benv k-benv k-strail k-labels) bool)
    (lambda (sa sb ea eb trail labels)
      (cond ((null? sa) #t)
            (else (let ((y (k-part-find sb (extract (car sa) 1))))
                    (and (>= y 0) (k-sub (extract (car sa) 2) y ea eb trail labels) (k-sub-sum (cdr sa) sb ea eb trail labels))))))))
(define k-subtype (subr (maxeff kstate spin) (int int) bool)
  (lambda (a b)
    (k-sub a b (the k-benv nil) (the k-benv nil)
           (the k-strail (new nil)) (the k-labels (new nil)))))
(define k-part-index (subr (maxeff (read @globals) (read @t)) (k-parts symbol int) int)
  (lambda (ps l i) (cond ((null? ps) -1) ((symbol=? (extract (car ps) 1) l) i) (else (k-part-index (cdr ps) l (+ i 1))))))

;;; ------------------------------------------------------------ errors

;; Run `f`, and if it fails at `a`..`b` with "a W is expected here, and
;; this is a G", fail instead with what `say` makes of W and G.
(define k-expected-split (subr (maxeff (read @globals) spin) (string) string)
  (lambda (m) (if (= (string-search m "a " 0) 0) (substring m 2 (string-length m)) "")))
(define k-sep string " is expected here, and this is a ")

(define k-rewriting (subr (maxeff (read @globals) checks spin) ((subr (maxeff checks spin) () k-te) int int (subr (maxeff checks spin) (string string string) string)) k-te)
  (lambda (f a b say)
    (let ((r (prompt k-tag (k-done (f)) (lambda (r) r))))
      (tagcase r
        (k-done (te) te)
        (k-err (m ea eb)
          (let* ((rest (k-expected-split m)) (at (k-find-sub rest k-sep 0)))
            (if (and (= ea a) (= eb b) (not (string=? rest "")) (>= at 0))
                (k-fail (say m (substring rest 0 at) (substring rest (+ at (string-length k-sep)) (string-length rest))) ea eb)
                (k-fail m ea eb))))
        (k-ok (xs) (k-fail "k-ok inside" a b))))))
;; The same, for any error at `a`..`b`.
(define k-prefixing (subr (maxeff (read @globals) checks) ((subr checks () k-te) int int (subr checks () string)) k-te)
  (lambda (f a b prefix)
    (let ((r (prompt k-tag (k-done (f)) (lambda (r) r))))
      (tagcase r
        (k-done (te) te)
        (k-err (m ea eb) (if (and (= ea a) (= eb b)) (k-fail (string-append (prefix) m) ea eb) (k-fail m ea eb)))
        (k-ok (xs) (k-fail "k-ok inside" a b))))))

;; The convention `want` asks of `got`, where a procedure differs from what
;; is expected only in its convention, so that a conversion makes it one
;; (`docs/research/native-conventions.md`).
(define k-conversion (subr (maxeff checks spin) (int int) (listof k-conv acyclic))
  (lambda (got want)
    (tagcase (k-get (k-resolve got))
      (ty-subr (e ps r from)
        (tagcase (k-get (k-resolve want))
          (ty-subr (e2 ps2 r2 to)
            (if (and (not (k-conv=? from to)) (k-subtype (k-ty-new (ty-subr e ps r to)) want)) (cons to nil) nil))
          (else y nil)))
      (else y nil))))
;; Conversion `code` at `x`'s span, among the facts `checked-extracts` gives.
(define k-note-conversion (subr (maxeff checks spin) (kx int) unit)
  (lambda (x code)
    (set k-extracts (cons (product (1 (k-start x)) (2 (k-end x)) (3 (- -1000 code))) (get k-extracts)))))
;; A conversion of `x`'s procedure, of type `t`, to `to`. To `fx` or to a
;; convention binder it does nothing at run time; to `cellular` or `native`
;; it is `%fx26-convert`, which gives the value if it is already one of
;; those, and otherwise an adapter: a procedure of the convention asked
;; for that calls it. The compiler learns of it as a fact at `x`'s span:
;; -1000 less the arity times 4, plus 1 for `cellular` or 2 for `native`.
(define k-convert-at (subr (maxeff checks spin) (kx int k-conv) unit)
  (lambda (x t to)
    (let ((n (tagcase (k-get (k-resolve t)) (ty-subr (e ps r cv) (* 4 (k-length ps))) (else y 0))))
      (tagcase to
        (cv-cellular () (k-note-conversion x (+ n 1)))
        (cv-native () (k-note-conversion x (+ n 2)))
        (else y #u)))))
;; `got ≤ want`, or an error at `x` saying so.
(define k-expect (subr (maxeff checks spin) (kx int int) unit)
  (lambda (x got want)
    (if (k-subtype got want)
        #u
        (let ((c (k-conversion got want)))
          (if (null? c)
              (k-fail (k-cat4 "a " (k-show-ty want) " is expected here, and this is a " (k-show-ty got)) (k-start x) (k-end x))
              (k-convert-at x got (car c)))))))
;; Bind each, the first first.
(define k-bind-all (subr (maxeff kstate spin) (k-bindings) unit)
  (lambda (bs) (if (null? bs) #u (begin (k-bind (car (car bs)) (cdr (car bs))) (k-bind-all (cdr bs))))))
;; `t` for a variable being bound to it: a `nat` of no known size is given
;; one, a variable of its own named after the variable, so that tests of it
;; can teach facts.
(define k-name-nat (subr (maxeff kstate spin) (symbol int) int)
  (lambda (name t)
    (tagcase (k-get (k-resolve t))
      (ty-nat (z)
        (tagcase z
          (sz-finite ()
            (let ((v (k-new-dvar-of name 5)))
              (begin (set k-skolems (cons v (get k-skolems))) (k-ty-new (ty-nat (k-size-var v))))))
          (else w t)))
      (else y t))))
;; Bind each, the first first, a `nat` of no known size given one.
(define k-bind-named (subr (maxeff kstate spin) (k-bindings) unit)
  (lambda (bs)
    (if (null? bs)
        #u
        (begin (k-bind (car (car bs)) (k-name-nat (car (car bs)) (cdr (car bs)))) (k-bind-named (cdr bs))))))
(define k-note-letrec (subr (maxeff kstate spin) ((listof (productof (1 symbol) (2 int) (3 kx)) acyclic) bool) unit)
  (lambda (bs spins)
    (if (null? bs)
        #u
        (let ((n (extract (car bs) 1)) (t (extract (car bs) 2)))
          (begin (k-note-known n 0)
                 (if spins (set k-recursive (cons (cons n t) (get k-recursive))) #u)
                 (k-note-letrec (cdr bs) spins))))))
;; The group's members are recursion that says `spin`, if `why` says it may
;; not end, and why is kept for an error.
;; Naming `s`: pure, but for a member of a recursive group that may not
;; end, named in the group. Called, the call says `spin`; given away,
;; whoever calls it could loop through it, so naming it does.
(define k-naming-effect (subr (maxeff (read @globals) (read @t) (alloc @t) spin) (symbol int) k-eff)
  (lambda (s t)
    (let ((spins (if (k-named-has? (get k-recursive) s t) (the k-eff (cons (a-spin) nil)) (the k-eff nil))))
      (if (and (get k-globals-effects) (k-global? s)) (k-insert (a-read (r-global s)) spins) spins))))
(define k-bind-letrec (subr (maxeff kstate spin) ((listof (productof (1 symbol) (2 int) (3 kx)) acyclic)) unit)
  (lambda (bs) (if (null? bs) #u (begin (k-bind (extract (car bs) 1) (extract (car bs) 2)) (k-bind-letrec (cdr bs))))))
;; Whether `x` is a lambda, under any type abstractions and ascriptions.
(define k-lambda? (subr (read @globals) (kx) bool)
  (lambda (x)
    (tagcase x
      (x-lambda (ps body a b) #t)
      (x-rlambda (r l a b) #t)
      (x-plambda (bs e a b) (k-lambda? e))
      (x-the (t e a b) (k-lambda? e))
      (else y #f))))
;; How many of `ns` are `n`.
(define k-count-name (subr (read @globals) (k-names symbol) int)
  (lambda (ns n) (cond ((null? ns) 0) ((symbol=? (car ns) n) (+ 1 (k-count-name (cdr ns) n))) (else (k-count-name (cdr ns) n)))))
;; Note each `let` binding of a lambda as known, once bound: of several of
;; one name, each is as many from the innermost as come after it. The
;; names, in order.
(define k-note-let-lambdas (subr (maxeff kstate spin) ((listof (productof (1 symbol) (2 kx)) acyclic)) k-names)
  (lambda (bs)
    (if (null? bs)
        nil
        (let* ((later (k-note-let-lambdas (cdr bs)))
               (n (extract (car bs) 1))
               (noted (if (k-lambda? (extract (car bs) 2)) (k-note-known n (k-count-name later n)) #u)))
          (the k-names (cons n later))))))
;; Whether a `plambda` body `x` with effect `e` may be generalized: pure, as
;; the value restriction has it; or an `rlambda`, under ascriptions and other
;; `plambda`s, whose effect only allocates. Making a closure makes no mutable
;; data a type could be generalized over: it holds only variables bound
;; outside.
(define k-rlambda-under? (subr (read @globals) (kx) bool)
  (lambda (x)
    (tagcase x
      (x-rlambda (r l a b) #t)
      (x-plambda (bs e a b) (k-rlambda-under? e))
      (x-the (t e a b) (k-rlambda-under? e))
      (else y #f))))
(define k-only-alloc? (subr (maxeff (read @globals) (read @t)) (k-eff) bool)
  (lambda (e) (or (null? e) (and (tagcase (car e) (a-alloc (r) #t) (else y #f)) (k-only-alloc? (cdr e))))))
(define k-generalizable? (subr (maxeff (read @globals) (read @t)) (kx k-eff) bool)
  (lambda (x e) (or (null? e) (and (k-rlambda-under? x) (k-only-alloc? e)))))
(define k-letrec-not-lambda (subr (read @globals) (symbol) string)
  (lambda (n)
    (string-append (k-quote (symbol->string n))
                   " is bound recursively, so it must be a lambda: nothing may run before every binding exists")))

(define k-proj-map (subr checks (k-binders (listof k-desc acyclic) int int) k-map)
  (lambda (bs ds a b)
    (if (null? bs)
        nil
        (let* ((v (extract (car bs) 1)) (k (extract (car bs) 2))
               (d (car ds))
               (ok (tagcase d (dr (r) (or (= k 0) (and (= k 3) (k-place? r)))) (de (e) (= k 1)) (dt (t) (or (= k 2) (= k 4))) (dz (z) (= k 5)) (dc (c) (= k 6)))))
          (if ok
              (cons (cons v d) (k-proj-map (cdr bs) (cdr ds) a b))
              (k-fail (k-cat4 (k-quote (symbol->string (k-dvar-name v))) " is bound as a " (k-kind-debug k)
                              ", and the description given is not one")
                      a b))))))
(define k-param-types (subr checks ((listof (productof (1 symbol) (2 k-ids)) acyclic) k-ids int int) k-bindings)
  (lambda (ps hint a b)
    (if (null? ps)
        nil
        (let* ((n (extract (car ps) 1)) (t (extract (car ps) 2))
               (ty (cond ((not (null? t)) (car t))
                         ((not (null? hint)) (car hint))
                         (else (k-fail (k-cat5 "the type of parameter " (k-quote (symbol->string n))
                                               " cannot be known here: write `(" (symbol->string n)
                                               " type)`, or check the `lambda` against a type")
                                       a b))))
               (rest (k-param-types (cdr ps) (if (null? hint) hint (cdr hint)) a b)))
          (cons (cons n ty) rest)))))
(define k-binding-types (subr (maxeff (read @globals) (read @t) (alloc @t)) (k-bindings) k-ids)
  (lambda (bs) (if (null? bs) nil (cons (cdr (car bs)) (k-binding-types (cdr bs))))))
(define k-some-untyped? (subr (maxeff (read @globals) (read @t)) ((listof (productof (1 symbol) (2 k-ids)) acyclic)) bool)
  (lambda (ps) (cond ((null? ps) #f) ((null? (extract (car ps) 2)) #t) (else (k-some-untyped? (cdr ps))))))

(define k-unannotated? (subr (maxeff (read @globals) (read @t)) (kx) bool)
  (lambda (x) (tagcase x (x-lambda (ps body a b) (k-some-untyped? ps)) (else y #f))))
;; A `lambda` missing parameter types, or a thunk: better told than asked.
(define k-needs-telling? (subr (maxeff (read @globals) (read @t)) (kx) bool)
  (lambda (x) (tagcase x (x-lambda (ps body a b) (or (null? ps) (k-some-untyped? ps))) (else y #f))))

;;; ------------------------------------------------------------ instantiation
;;; A projection left out: the binders of a `poly` solved by matching (local
;;; type inference). A type binder must be solved; an effect binder nothing
;;; constrains is `pure`; a region binder nothing constrains is a fresh
;;; region.

(define-type k-solved (ref k-map @t))
(define k-append-binders (subr (maxeff (read @globals) (read @t) (alloc @t)) (k-binders k-binders) k-binders)
  (lambda (xs ys) (if (null? xs) ys (cons (car xs) (k-append-binders (cdr xs) ys)))))
(define k-binders-from (subr (maxeff (read @globals) (read @t) (alloc @t) spin) (int k-binders) (productof (1 k-binders) (2 int)))
  (lambda (t acc)
    (tagcase (k-get t)
      (ty-poly (bs body) (k-binders-from (k-resolve body) (k-append-binders acc bs)))
      (else y (product (1 acc) (2 t))))))

;; The binders of `t` through every nested `poly`, and the type under them.
(define k-binders-of (subr (maxeff (read @globals) (read @t) (alloc @t) spin) (int) (productof (1 k-binders) (2 int)))
  (lambda (t) (k-binders-from (k-resolve t) nil)))

(define k-unknown? (subr (maxeff (read @globals) (read @t)) (k-binders int) bool)
  (lambda (kinds v) (cond ((null? kinds) #f) ((= (extract (car kinds) 1) v) #t) (else (k-unknown? (cdr kinds) v)))))
(define k-open? (subr (maxeff (read @globals) (read @t)) (k-binders k-solved int) bool)
  (lambda (kinds solved v) (and (k-unknown? kinds v) (null? (k-map-find (get solved) v)))))
(define k-solve (subr kstate (k-solved int k-desc) unit)
  (lambda (solved v d) (set solved (cons (cons v d) (get solved)))))

;; `a ≤ b`: region `a` won't outlive region `b`. The same; `b` a constant
;; (which never ends: `@name`, a fresh region, `const`); `b` bound around
;; `a`'s binder; or `a`'s bound won't outlive `b`.
(define k-outlived? (subr (maxeff (read @globals) (read @t) (alloc @t) spin) (k-region k-region) bool)
  (lambda (a b)
    (or (k-region=? a b)
        (tagcase b
          (r-var (w)
            (tagcase a
              (r-frozen (p f) (and (>= p 0) (k-outlived? (r-var p) b)))
              (r-var (v)
                (or (k-has-id? (k-outer-of v) w)
                    (let ((c (k-bound-of v)))
                      (and (not (null? c)) (and (not (k-region=? (car c) a)) (k-outlived? (car c) b))))))
              (else x #f)))
          (else y #t)))))

;; Each region binder nothing has solved gets a fresh region of its own,
;; named after it; or, if it has a bound, its bound, as solved (so `(rcons p
;; x y)`, with nothing else saying, allocates at `p`'s own region). A bounded
;; binder waits for its bound to be solved.
(define k-default-bounded (subr kstate (k-binders k-binders k-solved) unit)
  (lambda (all kinds solved)
    (if (null? kinds)
        #u
        (let* ((v (extract (car kinds) 1)) (bd (k-bound-of v)))
          (begin
            (if (and (= (extract (car kinds) 2) 0) (and (null? (k-map-find (get solved) v)) (not (null? bd))))
                (tagcase (car bd)
                  (r-var (w)
                    (let ((f (k-map-find (get solved) w)))
                      (cond ((not (null? f)) (tagcase (cdr (car f)) (dr (x) (k-solve solved v (dr x))) (else y #u)))
                            ((k-unknown? all w) #u)
                            (else (k-solve solved v (dr (car bd)))))))
                  (else y (k-solve solved v (dr (car bd)))))
                #u)
            (k-default-bounded all (cdr kinds) solved))))))
(define k-default-free (subr kstate (k-binders k-binders k-solved) unit)
  (lambda (all kinds solved)
    (if (null? kinds)
        #u
        (let* ((v (extract (car kinds) 1)) (bd (k-bound-of v))
               (waits (and (not (null? bd)) (tagcase (car bd) (r-var (w) (k-unknown? all w)) (else y #f)))))
          (begin
            (if (and (= (extract (car kinds) 2) 0) (and (null? (k-map-find (get solved) v)) (not waits)))
                (k-solve solved v (dr (k-fresh-region (string-append "@" (symbol->string (k-dvar-name v))))))
                #u)
            (k-default-free all (cdr kinds) solved))))))

(define k-default-regions (subr kstate (k-binders k-solved) unit)
  (lambda (kinds solved)
    (begin (k-default-bounded kinds kinds solved) (k-default-free kinds kinds solved))))

;; Each bounded region binder, as solved, won't outlive its bound, as solved;
;; or an error saying which would.
;; Whether `t` is data: built only from base types, `datum`, products and
;; sums, and pairs and bloblets that are frozen, of data; and type variables
;; of kind `data`.
(define-rec
  (k-data-walk (subr (maxeff kstate spin) (int int) bool)
    (lambda (t seen)
      (let ((t (k-resolve t)))
        (if (k-visit? t seen)
            #t
            (tagcase (k-get t)
              (ty-base (s) #t)
              (ty-void () #t)
              (ty-var (v) (k-data-var? v))
              (ty-product (ps) (k-data-parts ps seen))
              (ty-sum (ps) (k-data-parts ps seen))
              (ty-pair (a b r) (and (tagcase r (r-frozen (p f) #t) (else y #f)) (k-data-walk a seen) (k-data-walk b seen)))
              (ty-bloblet (fs z r) (and z (k-data-list fs seen)))
              (ty-nlist (e z r) (k-data-walk e seen))
              (ty-nat (z) #t)
              (else y #f))))))
  (k-data-parts (subr (maxeff kstate spin) (k-parts int) bool)
    (lambda (ps seen) (or (null? ps) (and (k-data-walk (extract (car ps) 2) seen) (k-data-parts (cdr ps) seen)))))
  (k-data-list (subr (maxeff kstate spin) (k-ids int) bool)
    (lambda (ts seen) (or (null? ts) (and (k-data-walk (car ts) seen) (k-data-list (cdr ts) seen))))))
(define k-is-data? (subr (maxeff kstate spin) (int) bool)
  (lambda (t) (k-data-walk t (k-new-epoch))))
;; `t` with its frozen regions made acyclic: what data `acyclic?` has found
;; acyclic is.
(define k-fin-region (subr (read @globals) (k-region) k-region)
  (lambda (r) (tagcase r (r-frozen (p f) (r-frozen p #t)) (else y r))))
(define-rec
  (k-finitize (subr (maxeff kstate spin) (int (ref (listof (pairof int int @t) acyclic) @t)) int)
    (lambda (t memo)
      (let* ((t (k-resolve t)) (done (k-memo-find (get memo) t)))
        (if (>= done 0)
            done
            (if (not (tagcase (k-get t) (ty-pair (a b r) #t) (ty-product (ps) #t) (ty-sum (ps) #t) (ty-bloblet (fs z r) #t) (else y #f)))
                t
                (let ((slot (k-slot)))
                  (begin
                    (set memo (cons (cons t slot) (get memo)))
                    (let ((new (tagcase (k-get t)
                                 (ty-pair (a b r) (let* ((a2 (k-finitize a memo)) (b2 (k-finitize b memo))) (ty-pair a2 b2 (k-fin-region r))))
                                 (ty-product (ps) (ty-product (k-finitize-parts ps memo)))
                                 (ty-sum (ps) (ty-sum (k-finitize-parts ps memo)))
                                 (ty-bloblet (fs z r) (ty-bloblet (k-finitize-list fs memo) z (k-fin-region r)))
                                 (else y (k-get t)))))
                      (begin (k-set-link slot (k-ty-new new)) slot)))))))))
  (k-finitize-parts (subr (maxeff kstate spin) (k-parts (ref (listof (pairof int int @t) acyclic) @t)) k-parts)
    (lambda (ps memo)
      (if (null? ps)
          nil
          (let* ((x (k-finitize (extract (car ps) 2) memo)) (rest (k-finitize-parts (cdr ps) memo)))
            (cons (product (1 (extract (car ps) 1)) (2 x)) rest)))))
  (k-finitize-list (subr (maxeff kstate spin) (k-ids (ref (listof (pairof int int @t) acyclic) @t)) k-ids)
    (lambda (ts memo) (if (null? ts) nil (let* ((x (k-finitize (car ts) memo)) (rest (k-finitize-list (cdr ts) memo))) (cons x rest))))))
(define k-finitized (subr (maxeff kstate spin) (int) int)
  (lambda (t) (k-finitize t (the (ref (listof (pairof int int @t) acyclic) @t) (new nil)))))
;; Which binding of `s` is in scope: how deep its name's stack is.
(define k-binding-depth (subr (maxeff (read @globals) (read @t) spin) (symbol) int)
  (lambda (s) (k-length (table-ref (get k-env) s nil))))
(define k-certified-has? (subr (maxeff (read @globals) (read @t)) ((listof (pairof symbol int @t) acyclic) symbol int) bool)
  (lambda (cs s d) (and (not (null? cs)) (or (and (symbol=? (car (car cs)) s) (= (cdr (car cs)) d)) (k-certified-has? (cdr cs) s d)))))
(define k-sc-one-arg? (subr (read @t) (kxs) bool) (lambda (xs) (and (not (null? xs)) (null? (cdr xs)))))
(define k-check-bounds (subr (maxeff checks spin) (k-binders k-map int int) unit)
  (lambda (kinds m a b)
    (if (null? kinds)
        #u
        (let* ((v (extract (car kinds) 1)) (bd (k-bound-of v)))
          (begin
            ;; A `data` binder takes only data.
            (if (= (extract (car kinds) 2) 4)
                (let ((f (k-map-find m v)))
                  (if (null? f)
                      #u
                      (tagcase (cdr (car f))
                        (dt (t) (if (k-is-data? t)
                                    #u
                                    (k-fail (k-cat5 (k-quote (symbol->string (k-dvar-name v))) " is bound as data, and a " (k-show-ty t) " is not data" "")
                                            a b)))
                        (else z #u))))
                #u)
            (if (null? bd)
                #u
                (let ((r (k-subst-region (r-var v) m)) (c (k-subst-region (car bd) m)))
                  (if (k-outlived? r c)
                      #u
                      (k-fail (k-cat5 (k-quote (symbol->string (k-dvar-name v))) " must not outlive "
                                      (k-quote (k-region-show (car bd)))
                                      ", and " (k-cat3 (k-region-show r) " could outlive " (k-region-show c)))
                              a b))))
            (k-check-bounds (cdr kinds) m a b))))))
;; A size binder instantiated as `finite` is sound only where it stands for
;; one size a caller supplies (`docs/research/soundness-findings.md`, F4): as
;; the size of at most one parameter, that parameter's own `(nlist T v)` or
;; `(nat v)` (less a constant, perhaps), and nowhere else a caller supplies
;; or can write. Its occurrences in what the callee gives back only forget a
;; size. Polarity: 1 given back, -1 supplied by a caller, 0 both, as in
;; anything that can be written.
(define k-size-alone? (subr pure (k-size int) bool)
  (lambda (z v)
    (tagcase z
      (sz-lin (k ts) (and (<= k 0) (not (null? ts)) (null? (cdr ts)) (= (car (car ts)) v) (= (cdr (car ts)) 1)))
      (else y #f))))
(define k-size-bad (subr (read @globals) (k-size int int) int)
  (lambda (z pol v)
    (if (and (not (= pol 1)) (tagcase z (sz-lin (k ts) (not (= (k-coef-of ts v) 0))) (else y #f))) 1 0)))
(define-type k-seen-pol (ref (listof (pairof int int @t) acyclic) @t))
;; How many occurrences of size variable `v` in `t` a caller supplies or
;; can write.
(define-rec
  (k-size-walk (subr (maxeff kstate spin) (int int int k-seen-pol) int)
    (lambda (t0 pol v seen)
      (let ((t (k-resolve t0)))
        (if (k-pair-seen? (get seen) t pol)
            0
            (begin
              (set seen (cons (cons t pol) (get seen)))
              (tagcase (k-get t)
                (ty-nat (z) (k-size-bad z pol v))
                (ty-nlist (e z r) (+ (k-size-bad z pol v) (k-size-walk e pol v seen)))
                (ty-named (g ds) (k-size-walk-descs ds v seen))
                (ty-subr (e ps r cv) (+ (k-size-walk-list ps (- 0 pol) v seen) (k-size-walk r pol v seen)))
                (ty-poly (bs body) (k-size-walk body pol v seen))
                (ty-pair (x y r)
                  (let ((p (tagcase r (r-frozen (q f) pol) (else w 0))))
                    (+ (k-size-walk x p v seen) (k-size-walk y p v seen))))
                (ty-bloblet (fs z r) (k-size-walk-list fs (if z pol 0) v seen))
                (ty-product (ps) (k-size-walk-parts ps pol v seen))
                (ty-sum (ps) (k-size-walk-parts ps pol v seen))
                (ty-ref (x r) (k-size-walk x 0 v seen))
                (ty-array (x r) (k-size-walk x 0 v seen))
                (ty-icell (x r) (k-size-walk x 0 v seen))
                (ty-markkey (x r) (k-size-walk x 0 v seen))
                (ty-tag (x y e r) (+ (k-size-walk x 0 v seen) (k-size-walk y 0 v seen)))
                (ty-comp (x y e r) (+ (k-size-walk x 0 v seen) (k-size-walk y 0 v seen)))
                (else y 0)))))))
  (k-size-walk-list (subr (maxeff kstate spin) (k-ids int int k-seen-pol) int)
    (lambda (ts pol v seen)
      (if (null? ts) 0 (let ((here (k-size-walk (car ts) pol v seen))) (+ here (k-size-walk-list (cdr ts) pol v seen))))))
  (k-size-walk-parts (subr (maxeff kstate spin) (k-parts int int k-seen-pol) int)
    (lambda (ps pol v seen)
      (if (null? ps) 0 (let ((here (k-size-walk (extract (car ps) 2) pol v seen))) (+ here (k-size-walk-parts (cdr ps) pol v seen))))))
  (k-size-walk-descs (subr (maxeff kstate spin) ((listof k-desc acyclic) int k-seen-pol) int)
    (lambda (ds v seen)
      (if (null? ds)
          0
          (let ((here (tagcase (car ds) (dz (z) (k-size-bad z 0 v)) (dt (x) (k-size-walk x 0 v seen)) (else y 0))))
            (+ here (k-size-walk-descs (cdr ds) v seen)))))))
;; Each parameter's count of such occurrences, and how many parameters are
;; sized by `v` alone.
(define k-size-params (subr (maxeff kstate spin) (k-ids int k-seen-pol) (productof (1 int) (2 int)))
  (lambda (ps v seen)
    (if (null? ps)
        (product (1 0) (2 0))
        (let* ((p (k-resolve (car ps)))
               (here (tagcase (k-get p)
                       (ty-nat (z) (if (k-size-alone? z v) (product (1 0) (2 1)) (product (1 (k-size-walk p -1 v seen)) (2 0))))
                       (ty-nlist (e z r)
                         (if (k-size-alone? z v) (product (1 (k-size-walk e -1 v seen)) (2 1)) (product (1 (k-size-walk p -1 v seen)) (2 0))))
                       (else y (product (1 (k-size-walk p -1 v seen)) (2 0)))))
               (rest (k-size-params (cdr ps) v seen)))
          (product (1 (+ (extract here 1) (extract rest 1))) (2 (+ (extract here 2) (extract rest 2))))))))
(define k-finite-size-ok? (subr (maxeff kstate spin) (int int) bool)
  (lambda (body v)
    (let ((seen (the k-seen-pol (new nil))))
      (tagcase (k-get (k-resolve body))
        (ty-subr (e ps r cv)
          (let* ((counts (k-size-params ps v seen)) (res (k-size-walk r 1 v seen)))
            (and (= (+ (extract counts 1) res) 0) (<= (extract counts 2) 1))))
        (else y (= (k-size-walk body 1 v seen) 0))))))
;; `t` with the sizes named since `saved` forgotten, as `finite`: they mean
;; nothing outside the scope that named them. Pops them.
;; `t` with the sizes named since `saved` forgotten, as `finite`: they mean
;; nothing outside the scope that named them. Pops them. Each stands for one
;; value's size, which no caller chooses, so it may be forgotten only where
;; `t` gives it back: where a caller would supply something of that size,
;; forgetting it would let any size in (`docs/research/soundness-findings.md`,
;; F8), and that is an error at `a`–`b`.
(define k-forget-nats (subr (maxeff checks spin) (k-ids int int int) int)
  (lambda (saved t a b)
    (letrec ((named (subr (maxeff (read @globals) kstate spin) (k-ids k-ids) k-ids)
                      (lambda (vs out) (if (= (k-length vs) (k-length saved)) out (named (cdr vs) (the k-ids (cons (car vs) out))))))
             (check (subr (maxeff (read @globals) checks spin) (k-ids) unit)
                      (lambda (vs)
                        (cond ((null? vs) #u)
                              ((> (k-size-walk t 1 (car vs) (the k-seen-pol (new nil))) 0)
                               (let ((name (k-quote (symbol->string (k-dvar-name (car vs))))))
                                 (k-fail (k-cat5 (k-cat3 "this is a " (k-show-ty t) ", which takes something of the size of ") name
                                                 ", and that size is not known outside " name "'s scope")
                                         a b)))
                              (else (check (cdr vs))))))
             (go (subr (maxeff (read @globals) kstate spin) (k-ids k-map) k-map)
                   (lambda (vs m) (if (null? vs) m (go (cdr vs) (cons (cons (car vs) (dz (sz-finite))) m))))))
      (let ((vs (named (get k-skolems) nil)))
        (begin (set k-skolems saved)
               (check vs)
               (if (null? vs) t (k-subst t (go vs nil))))))))
(define k-check-finite-sizes (subr (maxeff checks spin) (k-binders k-map int int int) unit)
  (lambda (kinds m body a b)
    (if (null? kinds)
        #u
        (let* ((v (extract (car kinds) 1)) (f (k-map-find m v))
               (fin (and (= (extract (car kinds) 2) 5) (not (null? f))
                         (tagcase (cdr (car f)) (dz (z) (tagcase z (sz-finite () #t) (else w #f))) (else y #f)))))
          (if (and (= (extract (car kinds) 2) 5) (not (null? f))
                   (tagcase (cdr (car f)) (dz (z) (tagcase z (sz-finite () #f) (else w (not (k-size-nonneg? z))))) (else y #f)))
              ;; A size binder solved from `v + k` against a size is that
              ;; size less `k`: a natural only where the facts here show it.
              (let ((name (k-quote (symbol->string (k-dvar-name v))))
                    (z (tagcase (cdr (car f)) (dz (z) z) (else y (sz-finite)))))
                (k-fail (k-cat5 "the size " name " would be " (k-show-size z)
                                ", which is not known here to be no less than 0: an argument may be shorter than this procedure's type needs")
                        a b))
          (if (and fin (not (k-finite-size-ok? body v)))
              (let ((name (k-quote (symbol->string (k-dvar-name v)))))
                (k-fail (k-cat5 "the size " name " cannot be `finite` here: " name
                                " is the size of more than one argument, or of something inside one, and `finite` would not keep them the same")
                        a b))
              (k-check-finite-sizes (cdr kinds) m body a b)))))))
(define k-finish-each (subr (maxeff checks spin) (k-binders k-map int int int) k-map)
  (lambda (kinds m a b ft)
    (if (null? kinds)
        m
        (let ((v (extract (car kinds) 1)) (k (extract (car kinds) 2)))
          (cond ((not (null? (k-map-find m v))) (k-finish-each (cdr kinds) m a b ft))
                ((= k 1) (k-finish-each (cdr kinds) (cons (cons v (de nil)) m) a b ft))
                ;; A convention nothing says is the program's.
                ((= k 6) (k-finish-each (cdr kinds) (cons (cons v (dc (get k-conv-default))) m) a b ft))
                ;; A size nothing says is some size.
                ((= k 5) (k-finish-each (cdr kinds) (cons (cons v (dz (sz-finite))) m) a b ft))
                (else (k-fail (k-cat5 (k-quote (symbol->string (k-dvar-name v))) " cannot be inferred for " (k-show-ty ft)
                                      ": nothing here says what it is. Use `proj`, or `the`" "")
                              a b)))))))

;; The whole solution: every type binder solved, effects defaulting to pure.
(define k-finish (subr (maxeff checks spin) (k-binders k-solved int int int) k-map)
  (lambda (kinds solved a b ft) (k-finish-each kinds (get solved) a b ft)))

;; Solve a size binder: a pattern `v + k` against a size `s` gives
;; `v = s - k` (`finite` stays `finite`).
(define k-unify-size (subr (maxeff kstate spin) (k-size k-size k-binders k-solved) unit)
  (lambda (p a kinds solved)
    (tagcase p
      (sz-lin (k ts)
        (if (and (not (null? ts)) (null? (cdr ts)) (= (cdr (car ts)) 1))
            (let ((v (car (car ts))))
              (if (and (k-unknown? kinds v) (null? (k-map-find (get solved) v)))
                  (k-solve solved v (dz (k-size-plus a (- 0 k))))
                  #u))
            #u))
      (else y #u))))
(define k-wrong-shape? (subr (maxeff (read @globals) (read @t) (alloc @t) spin) (int int) bool)
  (lambda (pattern actual)
    (let ((p (k-ty-rank pattern)) (a (k-ty-rank actual)))
      (cond ((or (= p 2) (= a 1)) #f)
            ((= p 3) (null? (k-as-subr actual)))
            ((and (= p 6) (= a 18)) #f)
            ;; A `nat` is an `int`.
            ((and (= p 0) (= a 19)) #f)
            (else (not (= p a)))))))

;; An argument of the wrong shape altogether is the error to report, before
;; any binder it left unsolved.
(define k-inst-shapes (subr (maxeff checks spin) (kxs k-ids int k-solved (arrayof int @t)) unit)
  (lambda (args params i solved done-t)
    (if (null? args)
        #u
        (let ((t (array-ref done-t i)))
          (if (and (>= t 0) (k-wrong-shape? (car params) t))
              (let ((p (k-subst (car params) (get solved))))
                (k-fail (k-cat5 "argument " (int->string (+ i 1)) " is a " (k-show-ty t) (k-cat3 ", where a " (k-show-ty p) " is expected"))
                        (k-start (car args)) (k-end (car args))))
              (k-inst-shapes (cdr args) (cdr params) (+ i 1) solved done-t))))))

;; Whether `t` mentions a binder of any kind not yet solved.
(define k-open-region? (subr (maxeff (read @globals) (read @t)) (k-region k-binders k-solved) bool)
  (lambda (r kinds solved)
    (tagcase r
      (r-var (v) (k-open? kinds solved v))
      (r-frozen (p f) (and (>= p 0) (k-open? kinds solved p)))
      (else y #f))))
(define k-open-conv? (subr (maxeff (read @globals) (read @t)) (k-conv k-binders k-solved) bool)
  (lambda (c kinds solved) (tagcase c (cv-var (v) (k-open? kinds solved v)) (else y #f))))
(define k-open-effect? (subr (maxeff (read @globals) (read @t)) (k-eff k-binders k-solved) bool)
  (lambda (e kinds solved)
    (cond ((null? e) #f)
          ((tagcase (car e) (a-var (v) (k-open? kinds solved v)) (else y (k-open-region? (k-atom-region (car e)) kinds solved))) #t)
          (else (k-open-effect? (cdr e) kinds solved)))))
(define k-push-ids (subr (maxeff (read @globals) (read @t) (alloc @t)) (k-ids k-ids) k-ids)
  (lambda (xs onto) (if (null? xs) onto (cons (car xs) (k-push-ids (cdr xs) onto)))))
(define k-push-parts (subr (maxeff (read @globals) (read @t) (alloc @t)) (k-parts k-ids) k-ids)
  (lambda (ps onto) (if (null? ps) onto (cons (extract (car ps) 2) (k-push-parts (cdr ps) onto)))))
(define k-descs-open? (subr (maxeff (read @globals) (read @t)) ((listof k-desc acyclic) k-binders k-solved) bool)
  (lambda (ds kinds solved)
    (and (not (null? ds))
         (or (tagcase (car ds)
               (dr (r) (k-open-region? r kinds solved))
               (de (e) (k-open-effect? e kinds solved))
               (dc (c) (k-open-conv? c kinds solved))
               (else y #f))
             (k-descs-open? (cdr ds) kinds solved)))))
;; Whether a size mentions a variable still to be solved.
(define k-size-open? (subr (maxeff kstate spin) (k-size k-binders k-solved) bool)
  (lambda (z kinds solved)
    (tagcase z
      (sz-lin (k ts) (letrec ((any (subr (maxeff (read @globals) kstate spin) (k-terms) bool)
                                   (lambda (xs) (and (not (null? xs)) (or (k-open? kinds solved (car (car xs))) (any (cdr xs)))))))
                       (any ts)))
      (else w #f))))
(define k-any-walk (subr (maxeff kstate spin) (k-ids int k-binders k-solved) bool)
  (lambda (stack seen kinds solved)
    (if (null? stack)
        #f
        (let ((t (k-resolve (car stack))) (rest (cdr stack)))
          (if (k-visit? t seen)
              (k-any-walk rest seen kinds solved)
              (let ((seen seen))
               (letrec ((reg (subr (maxeff (read @globals) (read @t)) (k-region) bool) (lambda (r) (k-open-region? r kinds solved)))
                        (go (subr (maxeff (read @globals) kstate spin) (k-ids) bool) (lambda (s) (k-any-walk s seen kinds solved))))
                (tagcase (k-get t)
                  (ty-var (v) (or (k-open? kinds solved v) (go rest)))
                  (ty-subr (e ps r cv) (or (k-open-effect? e kinds solved) (k-open-conv? cv kinds solved) (go (k-push-ids ps (cons r rest)))))
                  (ty-poly (bs body) (go (cons body rest)))
                  (ty-ref (x r) (or (reg r) (go (cons x rest))))
                  (ty-markkey (x r) (or (reg r) (go (cons x rest))))
                  (ty-array (x r) (or (reg r) (go (cons x rest))))
                  (ty-icell (x r) (or (reg r) (go (cons x rest))))
                  (ty-place (r) (or (reg r) (go rest)))
                  (ty-pair (x y r) (or (reg r) (go (cons x (cons y rest)))))
                  (ty-bloblet (fs z r) (or (reg r) (go (k-push-ids fs rest))))
                  (ty-product (ps) (go (k-push-parts ps rest)))
                  (ty-sum (ps) (go (k-push-parts ps rest)))
                  (ty-tag (x y e r) (or (reg r) (k-open-effect? e kinds solved) (go (cons x (cons y rest)))))
                  (ty-comp (x y e r) (or (reg r) (k-open-effect? e kinds solved) (go (cons x (cons y rest)))))
                  (ty-named (g ds) (or (k-descs-open? ds kinds solved) (go (k-push-ids (k-desc-types ds) rest))))
                  (ty-nlist (e z r) (or (reg r) (k-size-open? z kinds solved) (go (cons e rest))))
                  (ty-nat (z) (or (k-size-open? z kinds solved) (go rest)))
                  (else y (go rest))))))))))
(define k-mentions-any-unknown? (subr (maxeff kstate spin) (int k-binders k-solved) bool)
  (lambda (t kinds solved) (k-any-walk (cons t nil) (k-new-epoch) kinds solved)))

(define-rec
  (k-vars-walk (subr (maxeff (read @globals) (read @t) (write @t) (alloc @t) spin) (int int k-binders k-solved) bool)
    (lambda (t seen kinds solved)
      (let ((t (k-resolve t)))
        (if (k-visit? t seen)
            #f
            (letrec ((w (subr (maxeff (read @globals) (read @t) (write @t) (alloc @t) spin) (int) bool) (lambda (x) (k-vars-walk x seen kinds solved)))
                  (ws (subr (maxeff (read @globals) (read @t) (write @t) (alloc @t) spin) (k-ids) bool) (lambda (xs) (k-vars-walks xs seen kinds solved))))
              (begin
                (tagcase (k-get t)
                  (ty-var (v) (k-open? kinds solved v))
                  (ty-subr (e ps r cv) (or (ws ps) (w r)))
                  (ty-poly (bs body) (w body))
                  (ty-ref (a r) (w a))
                  (ty-markkey (a r) (w a))
                  (ty-array (a r) (w a))
                  (ty-icell (a r) (w a))
                  (ty-bloblet (fs z r) (ws fs))
                  (ty-product (ps) (ws (k-push-parts ps nil)))
                  (ty-sum (ps) (ws (k-push-parts ps nil)))
                  (ty-pair (a b r) (or (w a) (w b)))
                  (ty-tag (a b e r) (or (w a) (w b)))
                  (ty-comp (a b e r) (or (w a) (w b)))
                  (ty-named (g ds) (ws (k-desc-types ds)))
                  (ty-nlist (e z r) (w e))
                  (else y #f))))))))
  (k-vars-walks (subr (maxeff (read @globals) (read @t) (write @t) (alloc @t) spin) (k-ids int k-binders k-solved) bool)
    (lambda (ts seen kinds solved) (cond ((null? ts) #f) ((k-vars-walk (car ts) seen kinds solved) #t) (else (k-vars-walks (cdr ts) seen kinds solved))))))

;; Whether `t` mentions a type binder not yet solved.
(define k-mentions-unknown-type? (subr (maxeff (read @globals) (read @t) (write @t) (alloc @t) spin) (int k-binders k-solved) bool)
  (lambda (t kinds solved) (k-vars-walk t (k-new-epoch) kinds solved)))
(define k-any-unknown-type? (subr (maxeff (read @globals) (read @t) (write @t) (alloc @t) spin) (k-ids k-binders k-solved) bool)
  (lambda (ts kinds solved)
    (cond ((null? ts) #f) ((k-mentions-unknown-type? (car ts) kinds solved) #t) (else (k-any-unknown-type? (cdr ts) kinds solved)))))
;; A convention binder takes the actual's convention, if nothing has yet.
(define k-unify-conv (subr kstate (k-conv k-conv k-binders k-solved) unit)
  (lambda (pc ac kinds solved)
    (tagcase pc
      (cv-var (v) (if (and (k-unknown? kinds v) (null? (k-map-find (get solved) v))) (k-solve solved v (dc ac)) #u))
      (else y #u))))
;; A region binder takes the actual region; a place frozen into, `(acyclic
;; p)` or `(const p)`, takes the actual's place (the heap, where that is
;; frozen into the heap).
(define k-unify-region (subr kstate (k-region k-region k-binders k-solved) unit)
  (lambda (p a kinds solved)
    (tagcase p
      (r-var (v) (if (k-open? kinds solved v) (k-solve solved v (dr a)) #u))
      (r-frozen (v f)
        (if (and (>= v 0) (k-open? kinds solved v))
            (tagcase a
              (r-frozen (q g) (k-solve solved v (dr (if (< q 0) (r-heap) (r-var q)))))
              (else y #u))
            #u))
      (else y #u))))
(define k-same-kind-regions (subr (maxeff (read @globals) (read @t) (alloc @t)) (k-eff int) k-regions)
  (lambda (e rank)
    (cond ((null? e) nil)
          ((= (k-atom-rank (car e)) rank) (cons (k-atom-region (car e)) (k-same-kind-regions (cdr e) rank)))
          (else (k-same-kind-regions (cdr e) rank)))))
;; An effect binder takes all of `actual`; a region named in an atom is
;; matched against the actual's atoms of that kind when there is only one.
(define k-unify-effect (subr (maxeff kstate spin) (k-eff k-eff k-binders k-solved) unit)
  (lambda (pattern actual kinds solved)
    (if (null? pattern)
        #u
        (let ((atom (car pattern)))
          (begin
            (tagcase atom
              (a-var (v)
                (if (k-unknown? kinds v)
                    (let* ((f (k-map-find (get solved) v))
                           (prev (if (null? f) (the k-eff nil) (tagcase (cdr (car f)) (de (e) e) (else y (the k-eff nil))))))
                      (k-solve solved v (de (k-union prev actual))))
                    #u))
              (else y
                (tagcase (k-atom-region atom)
                  (r-var (v)
                    (if (k-open? kinds solved v)
                        (let ((same (k-same-kind-regions actual (k-atom-rank atom))))
                          (if (and (not (null? same)) (null? (cdr same))) (k-solve solved v (dr (car same))) #u))
                        #u))
                  (else z #u))))
            (k-unify-effect (cdr pattern) actual kinds solved))))))

;;; Matching: solve binders in `pattern` so that `actual` fits it. Never
;;; fails; what cannot be matched is left for the subtype check after.

(define-rec
  (k-unify (subr (maxeff kstate spin) (int int k-binders k-solved k-trail) unit)
    (lambda (pattern actual kinds solved trail)
      (let ((p (k-resolve pattern)) (a (k-resolve actual)))
        (if (k-trail-has? (get trail) p a)
            #u
            (begin
              (set trail (cons (cons p a) (get trail)))
              (let ((pt (k-get p)) (at (k-get a)))
                (if (and (tagcase at (ty-void () #t) (else y #f))
                         (not (tagcase pt (ty-var (v) (k-open? kinds solved v)) (else y #f))))
                    #u
                    (letrec ((u (subr (maxeff (read @globals) kstate spin) (int int) unit) (lambda (x y) (k-unify x y kinds solved trail)))
                          (ur (subr (maxeff (read @globals) kstate) (k-region k-region) unit) (lambda (r s) (k-unify-region r s kinds solved)))
                          (ue (subr (maxeff (read @globals) kstate spin) (k-eff k-eff) unit) (lambda (e f) (k-unify-effect e f kinds solved))))
                      (tagcase pt
                        (ty-var (v)
                          (if (k-unknown? kinds v)
                              (let ((f (k-map-find (get solved) v)))
                                (if (null? f)
                                    (k-solve solved v (dt a))
                                    (tagcase (cdr (car f))
                                      (dt (prev) (if (and (not (k-subtype a prev)) (k-subtype prev a)) (k-solve solved v (dt a)) #u))
                                      (else y #u))))
                              #u))
                        (ty-subr (pe pp pr pc)
                          (let ((c (k-as-subr a)))
                            (if (null? c)
                                #u
                                (begin
                                 ;; A convention binder takes the actual's convention.
                                 (tagcase at (ty-subr (e ps r ac) (k-unify-conv pc ac kinds solved)) (else y #u))
                                 (let ((ap (extract (car c) 2)))
                                   (if (not (= (k-length pp) (k-length ap)))
                                       #u
                                       (begin (k-unify-lists pp ap kinds solved trail)
                                              (u pr (extract (car c) 3))
                                              (ue pe (extract (car c) 1)))))))))
                        (ty-ref (x r) (tagcase at (ty-ref (y s) (begin (ur r s) (u x y))) (else z #u)))
                        (ty-markkey (x r) (tagcase at (ty-markkey (y s) (begin (ur r s) (u x y))) (else z #u)))
                        (ty-array (x r) (tagcase at (ty-array (y s) (begin (ur r s) (u x y))) (else z #u)))
                        (ty-icell (x r) (tagcase at (ty-icell (y s) (begin (ur r s) (u x y))) (else z #u)))
                        (ty-place (r) (tagcase at (ty-place (s) (ur r s)) (else z #u)))
                        (ty-pair (x1 x2 r)
                          (tagcase at
                            (ty-pair (y1 y2 s) (begin (ur r s) (u x1 y1) (u x2 y2)))
                            ;; A `nlist`'s tail is the `nlist` one shorter.
                            (ty-nlist (y sz s)
                              (begin (ur r s) (u x1 y)
                                     (u x2 (tagcase sz (sz-finite () a) (else w (k-ty-new (ty-nlist y (k-tail-size sz) s)))))))
                            (else z #u)))
                        (ty-nlist (x sz r) (tagcase at (ty-nlist (y sz2 s) (begin (ur r s) (u x y) (k-unify-size sz sz2 kinds solved))) (else z #u)))
                        (ty-nat (sz) (tagcase at (ty-nat (sz2) (k-unify-size sz sz2 kinds solved)) (else z #u)))
                        (ty-product (pp) (tagcase at (ty-product (pa) (k-unify-parts pp pa kinds solved trail)) (else z #u)))
                        (ty-sum (pp) (tagcase at (ty-sum (pa) (k-unify-parts pp pa kinds solved trail)) (else z #u)))
                        (ty-bloblet (fp zp r)
                          (tagcase at
                            (ty-bloblet (fa za s)
                              (if (= (k-length fp) (k-length fa)) (begin (ur r s) (k-unify-lists fp fa kinds solved trail)) #u))
                            (else z #u)))
                        (ty-tag (a1 h1 d1 r1)
                          (tagcase at (ty-tag (a2 h2 d2 r2) (begin (ur r1 r2) (u a1 a2) (u h1 h2) (ue d1 d2))) (else z #u)))
                        (ty-comp (h1 a1 d1 r1)
                          (tagcase at (ty-comp (h2 a2 d2 r2) (begin (ur r1 r2) (u a1 a2) (u h1 h2) (ue d1 d2))) (else z #u)))
                        (ty-named (g xs)
                          (tagcase at (ty-named (h ys) (if (= g h) (k-unify-descs xs ys kinds solved trail) #u)) (else z #u)))
                        (else z #u))))))))))
  (k-unify-descs (subr (maxeff kstate spin) ((listof k-desc acyclic) (listof k-desc acyclic) k-binders k-solved k-trail) unit)
    (lambda (xs ys kinds solved trail)
      (if (null? xs)
          #u
          (begin
            (tagcase (car xs)
              (dt (x) (tagcase (car ys) (dt (y) (k-unify x y kinds solved trail)) (else z #u)))
              (dr (r) (tagcase (car ys) (dr (q) (k-unify-region r q kinds solved)) (else z #u)))
              (de (d) (tagcase (car ys) (de (e) (k-unify-effect d e kinds solved)) (else z #u)))
              (dz (m) #u)
              (dc (c) (tagcase (car ys) (dc (d) (k-unify-conv c d kinds solved)) (else z #u))))
            (k-unify-descs (cdr xs) (cdr ys) kinds solved trail)))))
  (k-unify-lists (subr (maxeff kstate spin) (k-ids k-ids k-binders k-solved k-trail) unit)
    (lambda (xs ys kinds solved trail)
      (if (null? xs) #u (begin (k-unify (car xs) (car ys) kinds solved trail) (k-unify-lists (cdr xs) (cdr ys) kinds solved trail)))))
  (k-unify-parts (subr (maxeff kstate spin) (k-parts k-parts k-binders k-solved k-trail) unit)
    (lambda (pp pa kinds solved trail)
      (if (null? pp)
          #u
          (let ((y (k-part-find pa (extract (car pp) 1))))
            (begin (if (>= y 0) (k-unify (extract (car pp) 2) y kinds solved trail) #u)
                   (k-unify-parts (cdr pp) pa kinds solved trail)))))))

;; Instantiate a polymorphic value used, unapplied, where `expected` is
;; wanted.
(define k-instantiate-against (subr (maxeff checks spin) (int int int int) int)
  (lambda (t expected a b)
    (let* ((bo (k-binders-of t)) (kinds (extract bo 1)) (inner (extract bo 2)) (solved (the k-solved (new nil))))
      (begin
        (k-unify inner expected kinds solved (the k-trail (new nil)))
        (k-default-regions kinds solved)
        (let ((m (k-finish kinds solved a b t)))
          (begin (k-check-bounds kinds m a b) (k-check-finite-sizes kinds m inner a b) (let ((inst (k-subst inner m))) (begin (k-no-knot inst a b) inst))))))))
(define k-plambda-matches? (subr (maxeff (read @globals) (read @t)) (kx k-ty) bool)
  (lambda (x et)
    (tagcase x
      (x-plambda (binders body a b)
        (tagcase et (ty-poly (bs want) (and (= (k-length bs) (k-length binders)) (k-same-kinds? bs binders))) (else y #f)))
      (else y #f))))
(define k-same-labels? (subr (maxeff (read @globals) (read @t)) ((listof (productof (1 symbol) (2 kx)) acyclic) k-parts) bool)
  (lambda (fs ps)
    (cond ((null? fs) (null? ps))
          ((null? ps) #f)
          (else (and (symbol=? (extract (car fs) 1) (extract (car ps) 1)) (k-same-labels? (cdr fs) (cdr ps)))))))

;;; ------------------------------------------------------------ tagcase

(define-type k-arms (listof (productof (1 symbol) (2 bool) (3 k-names) (4 kx)) acyclic))
(define k-all-fit? (subr (maxeff kstate spin) (k-ids int) bool)
  (lambda (types t) (cond ((null? types) #t) ((k-subtype (car types) t) (k-all-fit? (cdr types) t)) (else #f))))
;; The first of `candidates` every one of `types` fits, or -1.
(define k-upper-bound (subr (maxeff kstate spin) (k-ids k-ids) int)
  (lambda (candidates types)
    (cond ((null? candidates) -1)
          ((k-all-fit? types (car candidates)) (car candidates))
          (else (k-upper-bound (cdr candidates) types)))))
(define k-part-names (subr (maxeff (read @globals) (read @t) (alloc @t)) (k-parts) (listof string acyclic))
  (lambda (ps) (if (null? ps) nil (cons (symbol->string (extract (car ps) 1)) (k-part-names (cdr ps))))))
(define k-arm-named? (subr (maxeff (read @globals) (read @t)) (k-arms symbol) bool)
  (lambda (arms l) (cond ((null? arms) #f) ((symbol=? (extract (car arms) 1) l) #t) (else (k-arm-named? (cdr arms) l)))))
(define k-variants-not-named (subr (maxeff (read @globals) (read @t) (alloc @t)) (k-parts k-arms) k-parts)
  (lambda (vs arms)
    (cond ((null? vs) nil)
          ((k-arm-named? arms (extract (car vs) 1)) (k-variants-not-named (cdr vs) arms))
          (else (cons (car vs) (k-variants-not-named (cdr vs) arms))))))
(define k-cannot-take-apart (subr (maxeff checks spin) (symbol int k-names kx) k-bindings)
  (lambda (tag t names body)
    (k-fail (k-cat5 (k-quote (symbol->string tag)) " carries a " (k-show-ty t) ", which cannot be taken apart into "
                    (string-append (int->string (k-length names)) " name(s)"))
            (k-start body) (k-end body))))
(define k-zip-fields (subr (maxeff (read @globals) (read @t) (alloc @t)) (k-names k-parts) k-bindings)
  (lambda (ns fs) (if (null? ns) nil (cons (cons (car ns) (extract (car fs) 2)) (k-zip-fields (cdr ns) (cdr fs))))))
;; The atoms of `e` in neither `bound` nor `own`.
(define k-beyond (subr (maxeff (read @globals) (read @t) (alloc @t) spin) (k-eff k-eff k-eff) k-eff)
  (lambda (e bound own)
    (cond ((null? e) nil)
          ((or (k-covered? bound (car e)) (k-contains? own (car e))) (k-beyond (cdr e) bound own))
          (else (cons (car e) (k-beyond (cdr e) bound own))))))
(define k-none-reach? (subr (maxeff (read @globals) (read @t) (write @t) (alloc @t) spin) (k-names k-names k-region) bool)
  (lambda (vs tv r)
    (cond ((null? vs) #t)
          ((k-has-name? tv (car vs)) (k-none-reach? (cdr vs) tv r))
          (else (let ((t (k-lookup (car vs))))
                  (and (or (< t 0) (not (k-has-region-in? (k-regions-in t) r))) (k-none-reach? (cdr vs) tv r)))))))
;; Whether the only way `body` can name anything in region `r` is the
;; variable `tag`, if it is one.
(define k-reaches-only? (subr (maxeff (read @globals) (read @t) (write @t) (alloc @t) spin) (kx kx k-region) bool)
  (lambda (body tag r)
    (let ((tv (the k-names (tagcase tag (x-var (s a b) (cons s nil)) (else y nil)))))
      (k-none-reach? (k-free-vars body) tv r))))

;;; ------------------------------------------------------------ synthesis

(define k-has-comefrom? (subr (maxeff (read @globals) (read @t)) (k-eff) bool)
  (lambda (e) (and (not (null? e)) (or (tagcase (car e) (a-comefrom (r) #t) (else y #f)) (k-has-comefrom? (cdr e))))))
;; `(letrena r …)`'s or `(letreap r …)`'s body, of type `t` and effect `e`,
;; closed: its value
;; may not mention `r`, and no continuation captured in it may outlive it;
;; what it does to `r` is masked, as nothing outside can name `r`.
(define k-close-region (subr (maxeff checks spin) (kx string int int k-eff int int) k-te)
  (lambda (x form r t e a b)
    (let ((name (k-cat3 form " " (symbol->string (k-dvar-name r)))))
      (if (k-has-region-in? (k-regions-in t) (r-var r))
          (k-fail (k-cat4 "the value of `" name "` would outlive its region: its type is " (k-show-ty t)) a b)
          (let ((masked (k-mask x e t)))
            (if (k-has-comefrom? masked)
                (k-fail (k-cat4 "a continuation captured in `" name "` could outlive its region: its effect is "
                                (k-show-effect masked))
                        a b)
                (k-te t masked)))))))

;; Whether an effect writes region `r`.
(define k-eff-writes? (subr (maxeff (read @globals) (read @t) spin) (k-eff k-region) bool)
  (lambda (e r)
    (and (not (null? e))
         (or (tagcase (car e) (a-write (x) (k-region=? x r)) (else y #f)) (k-eff-writes? (cdr e) r)))))
;; A generative type's representation writing one of its parameters writes
;; whatever it was given: cautiously, any region given any. Whether some
;; effect in a walk wrote a parameter, and whether some generative type was
;; given the region.
(define k-wrote-param (ref bool @t) (new #f))
(define k-given (ref bool @t) (new #f))
(define k-eff-writes-param? (subr (maxeff (read @globals) (read @t)) (k-eff) bool)
  (lambda (e)
    (and (not (null? e))
         (or (tagcase (car e) (a-write (x) (k-gen-region? x)) (a-var (v) (k-gen-param? v)) (else y #f))
             (k-eff-writes-param? (cdr e))))))
(define k-eff-writes-noting? (subr (maxeff kstate spin) (k-eff k-region) bool)
  (lambda (e r)
    (begin
      (if (k-eff-writes-param? e) (set k-wrote-param #t) #u)
      (k-eff-writes? e r))))
(define k-note-given (subr (maxeff kstate spin) ((listof k-desc acyclic) k-region) unit)
  (lambda (ds r)
    (if (null? ds)
        #u
        (begin
          (tagcase (car ds)
            (dr (x) (if (k-region=? x r) (set k-given #t) #u))
            (de (e) (if (k-eff-writes? e r) (set k-given #t) #u))
            (else y #u))
          (k-note-given (cdr ds) r)))))
;; Whether a latent effect anywhere in `t` writes `r`: what a `letfreeze`'s
;; value may not do to its region.
(define-rec
  (k-writes-in (subr (maxeff kstate spin) (int k-region int) bool)
    (lambda (t r seen)
      (let ((t (k-resolve t)))
        (if (k-visit? t seen)
            #f
            (tagcase (k-get t)
              (ty-subr (e ps x cv) (or (k-eff-writes-noting? e r) (or (k-writes-list ps r seen) (k-writes-in x r seen))))
              (ty-tag (a h e x) (or (k-eff-writes-noting? e r) (or (k-writes-in a r seen) (k-writes-in h r seen))))
              (ty-comp (b a e x) (or (k-eff-writes-noting? e r) (or (k-writes-in a r seen) (k-writes-in b r seen))))
              (ty-poly (bs body) (k-writes-in body r seen))
              (ty-ref (a x) (k-writes-in a r seen))
              (ty-array (a x) (k-writes-in a r seen))
              (ty-icell (a x) (k-writes-in a r seen))
              (ty-markkey (a x) (k-writes-in a r seen))
              (ty-pair (a b x) (or (k-writes-in a r seen) (k-writes-in b r seen)))
              (ty-bloblet (fs z x) (k-writes-list fs r seen))
              (ty-product (ps) (k-writes-parts ps r seen))
              (ty-sum (ps) (k-writes-parts ps r seen))
              (ty-nlist (e z x) (k-writes-in e r seen))
              (ty-named (g ds)
                (begin (k-note-given ds r)
                       (or (k-writes-in (extract (k-gen-of g) 4) r seen) (k-writes-list (k-desc-types ds) r seen))))
              (else x #f))))))
  (k-writes-list (subr (maxeff kstate spin) (k-ids k-region int) bool)
    (lambda (ts r seen) (and (not (null? ts)) (or (k-writes-in (car ts) r seen) (k-writes-list (cdr ts) r seen)))))
  (k-writes-parts (subr (maxeff kstate spin) (k-parts k-region int) bool)
    (lambda (ps r seen) (and (not (null? ps)) (or (k-writes-in (extract (car ps) 2) r seen) (k-writes-parts (cdr ps) r seen))))))

(define k-any-frozen? (subr (maxeff (read @globals) (read @t)) (k-eff) bool)
  (lambda (e) (and (not (null? e)) (or (k-frozen-atom? (car e)) (k-any-frozen? (cdr e))))))
(define k-writes-frozen? (subr (maxeff (read @globals) (read @t)) (k-eff) bool)
  (lambda (e) (and (not (null? e)) (or (and (k-frozen-atom? (car e)) (= (k-atom-rank (car e)) 1)) (k-writes-frozen? (cdr e))))))
;; `e` without its reads, allocations and awaits on `const`, which are pure.
(define k-drop-frozen (subr (maxeff (read @globals) (read @t) (alloc @t)) (k-eff) k-eff)
  (lambda (e)
    (cond ((null? e) nil)
          ;; Only data frozen in the heap, which never ends; what is done to
          ;; data frozen into a place stays, until masking removes it.
          ((and (k-frozen-atom? (car e)) (let ((k (k-atom-rank (car e)))) (or (= k 0) (or (= k 2) (= k 5))))
                (tagcase (k-atom-region (car e)) (r-frozen (p f) (< p 0)) (else y #f)))
           (k-drop-frozen (cdr e)))
          (else (cons (car e) (k-drop-frozen (cdr e)))))))
;; `x`'s effect `e`, noted.
(define k-note-effect (subr (maxeff (read @globals) (read @t) (write @t) (alloc @t)) (kx k-eff) unit)
  (lambda (x e) (set k-effect-notes (the k-facts (cons (product (1 (k-start x)) (2 (k-end x)) (3 (k-summary e))) (get k-effect-notes))))))
;; `e`, the effect of `x`, with what it does to frozen data taken out; or an
;; error, if it writes it.
(define k-frozen (subr checks (kx k-eff) k-eff)
  (lambda (x e)
    (cond ((not (k-any-frozen? e)) e)
          ((k-writes-frozen? e) (k-fail "this writes frozen data, whose region is `const`" (k-start x) (k-end x)))
          (else (k-drop-frozen e)))))

;; A `letfreeze r`'s value, of type `t`, as it leaves: `r` made `const`,
;; unless something in it could still write `r`.
(define k-frozen-result (subr (maxeff checks spin) (int k-region bool int int int) int)
  (lambda (r into written t a b)
    (if (begin (set k-wrote-param #f) (set k-given #f)
               (or (k-writes-in t (r-var r) (k-new-epoch)) (and (get k-wrote-param) (get k-given))))
        (k-fail (k-cat4 "the value of `letfreeze " (symbol->string (k-dvar-name r))
                        "` could still write its region's data: its type is " (k-show-ty t))
                a b)
        (let ((frozen (tagcase into (r-frozen (p f) (r-frozen p (not written))) (else y into))))
          (k-subst t (the k-map (cons (cons r (dr frozen)) nil)))))))

;; Whether a procedure of type `t` could be given itself: a cycle in `t`
;; runs through a parameter of a procedure (or the argument of a
;; continuation). A type that is merely recursive, as a list is, does not let
;; anything loop. `path`: the nodes on the way down, newest first, each with
;; whether it was reached through a parameter.
(define-type k-cpath (listof (pairof int bool @t) acyclic))
(define k-on-path? (subr (maxeff (read @globals) (read @t)) (k-cpath int) bool)
  (lambda (path t) (and (not (null? path)) (or (= (car (car path)) t) (k-on-path? (cdr path) t)))))
;; Whether a node newer than `t` on the path was reached through a parameter.
(define k-newer-param? (subr (maxeff (read @globals) (read @t)) (k-cpath int) bool)
  (lambda (path t) (and (not (= (car (car path)) t)) (or (cdr (car path)) (k-newer-param? (cdr path) t)))))
(define-rec
  (k-cyclic-from? (subr (maxeff kstate spin) (int bool k-cpath) bool)
    (lambda (t by path)
      (let ((t (k-resolve t)))
        (cond ((k-on-path? path t) (or by (k-newer-param? path t)))
              ;; Too deep to follow: it may loop, the cautious answer.
              ((> (k-length path) 64) #t)
              (else
               (let ((p (the k-cpath (cons (cons t by) path))))
                 (tagcase (k-get t)
                   (ty-subr (e ps r cv) (or (k-cyclic-list? ps #t p) (k-cyclic-from? r #f p)))
                   (ty-comp (x a e r) (or (k-cyclic-from? x #t p) (k-cyclic-from? a #f p)))
                   (ty-tag (a h e r) (or (k-cyclic-from? a #f p) (k-cyclic-from? h #f p)))
                   (ty-poly (bs x) (k-cyclic-from? x #f p))
                   (ty-ref (a r) (k-cyclic-from? a #f p))
                   (ty-array (a r) (k-cyclic-from? a #f p))
                   (ty-icell (a r) (k-cyclic-from? a #f p))
                   (ty-markkey (a r) (k-cyclic-from? a #f p))
                   (ty-pair (a b r) (or (k-cyclic-from? a #f p) (k-cyclic-from? b #f p)))
                   (ty-bloblet (fs z r) (k-cyclic-list? fs #f p))
                   (ty-product (ps) (k-cyclic-parts? ps p))
                   (ty-sum (ps) (k-cyclic-parts? ps p))
                   ;; Through its representation; what it was given,
                   ;; cautiously, as if taken as a parameter.
                   (ty-named (g ds) (or (k-cyclic-from? (extract (k-gen-of g) 4) #f p) (k-cyclic-list? (k-desc-types ds) #t p)))
                   (ty-nlist (e z r) (k-cyclic-from? e #f p))
                   (else x #f))))))))
  (k-cyclic-list? (subr (maxeff kstate spin) (k-ids bool k-cpath) bool)
    (lambda (ts by path) (and (not (null? ts)) (or (k-cyclic-from? (car ts) by path) (k-cyclic-list? (cdr ts) by path)))))
  (k-cyclic-parts? (subr (maxeff kstate spin) (k-parts k-cpath) bool)
    (lambda (ps path) (and (not (null? ps)) (or (k-cyclic-from? (extract (car ps) 2) #f path) (k-cyclic-parts? (cdr ps) path))))))
(define k-cyclic? (subr (maxeff kstate spin) (int) bool)
  (lambda (t) (k-cyclic-from? t #f nil)))
;; `f` under any projections and ascriptions.
(define k-under (subr (read @globals) (kx) kx)
  (lambda (f) (tagcase f (x-proj (body ds a b) (k-under body)) (x-the (t body a b) (k-under body)) (else y f))))
;; Whether `k` is named in `x` only as the operator of calls, evaluated as
;; `x` is: not under a `lambda` (which could be called later) or a prompt
;; (whose captures could be composed later).
(define-rec
  (k-only-called? (subr (maxeff (read @globals) (read @t) (alloc @t)) (kx symbol) bool)
    (lambda (x k)
      (tagcase x
        (x-var (s a b) (not (symbol=? s k)))
        (x-const (t v a b) #t)
        (x-app (f args a b)
          (and (or (tagcase f (x-var (s fa fb) (symbol=? s k)) (else y #f)) (k-only-called? f k))
               (k-only-called-list? args k)))
        (x-lambda (ps body a b) (not (k-has-name? (k-free-vars x) k)))
        (x-plambda (bs body a b) (not (k-has-name? (k-free-vars x) k)))
        (x-rlambda (r l a b) (not (k-has-name? (k-free-vars x) k)))
        (x-letrec (bs body a b) (not (k-has-name? (k-free-vars x) k)))
        (x-prompt (t body h a b) (not (k-has-name? (k-free-vars x) k)))
        (x-let (bs body a b)
          (and (k-only-called-lets? bs k) (or (k-has-name? (k-let-names bs nil) k) (k-only-called? body k))))
        (x-letregion (m r i body a b) (or (symbol=? (k-dvar-name r) k) (k-only-called? body k)))
        (x-tagcase (s arms els a b)
          (and (k-only-called? s k)
               (k-only-called-arms? arms k)
               (or (null? els) (symbol=? (extract (car els) 1) k) (k-only-called? (extract (car els) 2) k))))
        (x-proj (body ds a b) (k-only-called? body k))
        (x-the (t body a b) (k-only-called? body k))
        (x-convention (c body a b) (k-only-called? body k))
        (x-extract (body l a b) (k-only-called? body k))
        (x-sum (l body a b) (k-only-called? body k))
        (x-if (p c d a b) (and (k-only-called? p k) (k-only-called? c k) (k-only-called? d k)))
        (x-begin (xs a b) (k-only-called-list? xs k))
        (x-bloblet (o i xs a b) (k-only-called-list? xs k))
        (x-product (fs a b) (k-only-called-lets? fs k)))))
  (k-only-called-list? (subr (maxeff (read @globals) (read @t) (alloc @t)) (kxs symbol) bool)
    (lambda (xs k) (or (null? xs) (and (k-only-called? (car xs) k) (k-only-called-list? (cdr xs) k)))))
  (k-only-called-lets? (subr (maxeff (read @globals) (read @t) (alloc @t)) ((listof (productof (1 symbol) (2 kx)) acyclic) symbol) bool)
    (lambda (bs k) (or (null? bs) (and (k-only-called? (extract (car bs) 2) k) (k-only-called-lets? (cdr bs) k)))))
  (k-only-called-arms? (subr (maxeff (read @globals) (read @t) (alloc @t)) (k-arms symbol) bool)
    (lambda (arms k)
      (or (null? arms)
          (and (or (k-has-name? (extract (car arms) 3) k) (k-only-called? (extract (car arms) 4) k))
               (k-only-called-arms? (cdr arms) k))))))
;; Whether the receiver of `cwcc` at type `ft` may capture a continuation:
;; its latent effect has a `comefrom`. Unknown counts as may.
(define k-receiver-captures? (subr (maxeff (read @globals) (read @t) (alloc @t) spin) (int) bool)
  (lambda (ft)
    (let ((c (k-as-subr ft)))
      (or (null? c) (null? (extract (car c) 2))
          (let ((r (k-as-subr (k-resolve (car (extract (car c) 2))))))
            (or (null? r)
                (letrec ((any (subr (read @globals) (k-eff) bool)
                              (lambda (e) (and (not (null? e)) (or (tagcase (car e) (a-comefrom (x) #t) (else y #f)) (any (cdr e)))))))
                  (any (extract (car r) 1)))))))))
;; Whether `r`, given to `cwcc`, is a `lambda` whose continuation can only
;; be called while `cwcc` runs, so can only leave it
;; (`docs/research/soundness-findings.md`, F3).
(define k-escape-only? (subr (maxeff (read @globals) (read @t) (alloc @t)) (kx) bool)
  (lambda (r)
    (tagcase r
      (x-the (t body a b) (k-escape-only? body))
      (x-lambda (ps body a b) (and (not (null? ps)) (null? (cdr ps)) (k-only-called? body (extract (car ps) 1))))
      (else y #f))))
;; The name `f` is, under any projections and ascriptions, if a variable.
(define k-callee-name (subr (maxeff (read @globals) (alloc @t)) (kx) (listof symbol acyclic))
  (lambda (f)
    (tagcase f
      (x-proj (body ds a b) (k-callee-name body))
      (x-the (t body a b) (k-callee-name body))
      (x-var (n a b) (the (listof symbol acyclic) (cons n nil)))
      (else y (the (listof symbol acyclic) nil)))))
;; Whether `f` names a known procedure.
(define k-known-callee? (subr (maxeff kstate spin) (kx) bool)
  (lambda (f)
    (let ((s (k-callee-name f)))
      (and (not (null? s)) (let ((t (k-lookup (car s)))) (and (>= t 0) (k-known? (car s))))))))
;; Whether a call of `f` (instantiated to `ft`) may run for an unbounded
;; time beyond what its latent effect says: a call, in a recursive group's
;; lambdas, of the group; or a call through a recursive type of anything but
;; known code (self-application loops with no store at all). A knot through
;; the store needs nothing here: `k-no-knot` makes its type say `spin`.
(define k-may-spin? (subr (maxeff kstate spin) (kx int kxs) bool)
  (lambda (f ft args)
    (let* ((s (k-callee-name f))
           (t (if (null? s) -1 (k-lookup (car s)))))
      (cond ;; A continuation called after `cwcc` has returned comes back to
            ;; it again, as often as it is called: only one that can only
            ;; leave needs no `spin`.
            ;; And the receiver must capture no continuation, which could
            ;; hold a call of `k` and be run after `cwcc` returns (F9): a
            ;; `comefrom` in its latent effect, `cwcc`'s `e` as solved.
            ((and (>= t 0) (string=? (symbol->string (car s)) "cwcc") (k-named-has? (get k-std) (car s) t))
             (or (k-receiver-captures? ft)
                 (not (and (not (null? args)) (null? (cdr args)) (k-escape-only? (car args))))))
            ((and (>= t 0) (k-named-has? (get k-recursive) (car s) t)) #t)
            ((and (>= t 0) (or (k-known? (car s)) (k-named-has? (get k-std) (car s) t))) #f)
            ((k-lambda? (k-under f)) #f)
            (else (k-cyclic? ft))))))

;;; ------------------------------------------------- well-founded recursion
;;; Which recursive groups need not say `spin`: size-change termination
;;; (Lee, Jones and Ben-Amram, POPL 2001), as `terminate.rs` does it. Each
;;; call within the group is a graph of how the callee's arguments relate to
;;; the caller's parameters; closed under composition, every graph from a
;;; member to itself that is its own composition must have a parameter
;;; strictly smaller. The measures: parts (of sums, products, pairs at a
;;; `acyclic` region, datums), and integers counting down to a bound below or
;;; up to one above. A member named but not called escapes, and fails.

;; A recursive group: names, declared types, lambdas.
(define-type k-group (listof (productof (1 symbol) (2 int) (3 kx)) acyclic))
(define k-note-recursive (subr kstate (k-group) unit)
  (lambda (g)
    (if (null? g)
        #u
        (begin (set k-recursive (cons (cons (extract (car g) 1) (extract (car g) 2)) (get k-recursive)))
               (k-note-recursive (cdr g))))))
;; What is known of a value, relative to a parameter of the member walked:
;; the parameter, or (strictly) a part of it, of a type; or the integer
;; parameter plus an offset.
(define-datatype k-tr (tr-part int bool int) (tr-int int int))
(define-type k-trs (listof k-tr acyclic))
(define-type k-tscope (listof (pairof symbol k-trs @t) acyclic))
;; Bounds that tests have put on parameters: 0 below, 1 above.
(define-type k-guards (listof (pairof int int @t) acyclic))
;; A size-change graph: edges between slots (parameter × 3 + measure: 0
;; parts, 1 down, 2 up), strict or not, in order and each pair once.
(define-type k-edge (productof (1 int) (2 int) (3 bool)))
(define-type k-graph (listof k-edge acyclic))
(define-type k-calls (listof (productof (1 int) (2 int) (3 k-graph)) acyclic))
(define k-sc-members (ref k-names @t) (new nil))
(define k-sc-current (ref int @t) (new 0))
(define k-sc-calls (ref k-calls @t) (new nil))
;; A member named other than as a call's operator: (where . which), or none.
(define k-sc-escapes (ref (listof (pairof int int @t) acyclic) @t) (new nil))
;; For each call, as `k-sc-calls` has them: why it may shrink nothing, or "".
(define k-sc-hints (ref (listof string acyclic) @t) (new nil))
;; Whether the closure of the calls grew past `k-sc-most`.
(define k-sc-too-many (ref bool @t) (new #f))
;; For each call: caller, callee, and each argument as the caller's
;; parameter passed unchanged, or -1.
(define-type k-passed (listof (productof (1 int) (2 int) (3 k-ids)) acyclic))
(define k-sc-passed (ref k-passed @t) (new nil))
;; (member . parameter): passed unchanged by every call in the group, so the
;; same for the whole recursion, and a bound as a literal is.
(define k-sc-invariant (ref k-guards @t) (new nil))

(define k-sc-in? (subr (maxeff (read @globals) (read @t)) (k-tscope symbol) bool)
  (lambda (sc s) (and (not (null? sc)) (or (symbol=? (car (car sc)) s) (k-sc-in? (cdr sc) s)))))
(define k-sc-trs (subr (maxeff (read @globals) (read @t)) (k-tscope symbol) k-trs)
  (lambda (sc s) (cond ((null? sc) nil) ((symbol=? (car (car sc)) s) (cdr (car sc))) (else (k-sc-trs (cdr sc) s)))))
(define k-sc-index (subr (maxeff (read @globals) (read @t)) (k-names symbol int) int)
  (lambda (ns s i) (cond ((null? ns) -1) ((symbol=? (car ns) s) i) (else (k-sc-index (cdr ns) s (+ i 1))))))
;; The member `s` names, or -1 if none, or if something on the way hid it.
(define k-sc-member (subr (maxeff (read @globals) (read @t)) (k-tscope symbol) int)
  (lambda (sc s) (if (k-sc-in? sc s) -1 (k-sc-index (get k-sc-members) s 0))))
;; The standard operation `f` names, or "".
(define k-sc-op (subr (maxeff (read @globals) (read @t) (alloc @t) spin) (kx k-tscope) string)
  (lambda (f sc)
    (tagcase (k-under f)
      (x-var (s a b)
        (let ((t (k-lookup s)))
          (if (and (>= t 0) (not (k-sc-in? sc s)) (< (k-sc-index (get k-sc-members) s 0) 0) (k-named-has? (get k-std) s t))
              (symbol->string s)
              "")))
      (else y ""))))
(define k-sc-literal (subr (maxeff (read @globals) (alloc @t)) (kx) (listof int acyclic))
  (lambda (x) (tagcase x (x-const (t v a b) (if (= t k-int) (the (listof int acyclic) (cons v nil)) nil)) (else y nil))))
(define k-sc-bool? (subr (read @globals) (kx bool) bool)
  (lambda (x want) (tagcase x (x-const (t v a b) (and (= t k-bool) (= v (if want 1 0)))) (else y #f))))
(define k-sc-one? (subr (read @t) (kxs) bool)
  (lambda (xs) (and (not (null? xs)) (null? (cdr xs)))))
(define k-sc-two? (subr (maxeff (read @globals) (read @t)) (kxs) bool)
  (lambda (xs) (and (not (null? xs)) (k-sc-one? (cdr xs)))))

(define k-sc-part-ty (subr (maxeff (read @globals) (read @t)) (k-parts symbol) int)
  (lambda (ps l) (cond ((null? ps) -1) ((symbol=? (extract (car ps) 1) l) (extract (car ps) 2)) (else (k-sc-part-ty (cdr ps) l)))))
(define k-sc-nth-ty (subr (maxeff (read @globals) (read @t)) (k-parts int) int)
  (lambda (ps i) (cond ((null? ps) -1) ((= i 0) (extract (car ps) 2)) (else (k-sc-nth-ty (cdr ps) (- i 1))))))
;; Field `l` of what `ks` knows of products.
;; A part's type, where known (`t` ≥ 0); `void` where not, as past a
;; generative type's conversion.
(define k-ty-known (subr (maxeff (read @globals) (read @t) spin) (int) k-ty) (lambda (t) (if (< t 0) (ty-void) (k-get t))))
;; An `extract` proves a product, and so a part, known here or not.
(define k-sc-fields (subr (maxeff kstate spin) (k-trs symbol) k-trs)
  (lambda (ks l)
    (if (null? ks)
        nil
        (let ((rest (k-sc-fields (cdr ks) l)))
          (tagcase (car ks)
            (tr-part (p s t)
              (let ((f (tagcase (k-ty-known t) (ty-product (ps) (k-sc-part-ty ps l)) (else y -1))))
                (the k-trs (cons (tr-part p #t f) rest))))
            (else y rest))))))
;; What an arm of a `tagcase` on what `ks` knows binds: variant `tag`'s
;; value, or (`i` ≥ 0) its field `i`.
(define k-sc-variant (subr (maxeff kstate spin) (k-trs symbol int) k-trs)
  (lambda (ks tag i)
    (if (null? ks)
        nil
        (let ((rest (k-sc-variant (cdr ks) tag i)))
          (tagcase (car ks)
            ;; A `tagcase` proves a sum, and so a part, known here or not.
            (tr-part (p s t)
              (let ((f (tagcase (k-ty-known t)
                         (ty-sum (vs)
                           (let ((v (k-sc-part-ty vs tag)))
                             (cond ((< v 0) -1)
                                   ((< i 0) v)
                                   (else (tagcase (k-get v) (ty-product (ps) (k-sc-nth-ty ps i)) (else y -1))))))
                         (else y -1))))
                (the k-trs (cons (tr-part p #t f) rest))))
            (else y rest))))))
;; The `car` (`head`) or `cdr` of what `ks` knows of pairs at an `acyclic`
;; region.
(define k-sc-pair-parts (subr (maxeff kstate spin) (k-trs bool) k-trs)
  (lambda (ks head)
    (if (null? ks)
        nil
        (let ((rest (k-sc-pair-parts (cdr ks) head)))
          (tagcase (car ks)
            (tr-part (p s t)
              (tagcase (k-ty-known t)
                ;; A `nlist`'s tail is a `nlist` too: the same type serves.
                (ty-nlist (e z r) (the k-trs (cons (tr-part p #t (if head e t)) rest)))
                (ty-pair (x y r)
                  (tagcase r
                    (r-frozen (q fin) (if fin (the k-trs (cons (tr-part p #t (if head x y)) rest)) rest))
                    (else z rest)))
                (else z rest)))
            (else z rest))))))
(define k-sc-strict (subr kstate (k-trs) k-trs)
  (lambda (ks)
    (if (null? ks)
        nil
        (let ((rest (k-sc-strict (cdr ks))))
          (tagcase (car ks) (tr-part (p s t) (the k-trs (cons (tr-part p #t t) rest))) (else y rest))))))
(define k-sc-parts (subr kstate (k-trs) k-trs)
  (lambda (ks)
    (if (null? ks)
        nil
        (let ((rest (k-sc-parts (cdr ks))))
          (tagcase (car ks) (tr-part (p s t) (the k-trs (cons (car ks) rest))) (else y rest))))))
(define k-sc-shift (subr kstate (k-trs int) k-trs)
  (lambda (ks k)
    (if (null? ks)
        nil
        (let ((rest (k-sc-shift (cdr ks) k)))
          (tagcase (car ks) (tr-int (p o) (the k-trs (cons (tr-int p (+ o k)) rest))) (else y rest))))))
;; What both `ks` and `ls` say, the weaker of the two: what is known of
;; either branch's value.
(define k-sc-meet-one (subr (maxeff (read @globals) (read @t) spin) (k-tr k-trs) k-trs)
  (lambda (k ls)
    (if (null? ls)
        nil
        (let ((m (tagcase k
                   (tr-part (p s t)
                     (tagcase (car ls)
                       (tr-part (q r u)
                         (if (= p q)
                             (let ((same (and (>= t 0) (>= u 0) (= (k-resolve t) (k-resolve u)))))
                               (the k-trs (cons (tr-part p (and s r) (if same t -1)) nil)))
                             (the k-trs nil)))
                       (else y (the k-trs nil))))
                   (tr-int (p o)
                     (tagcase (car ls)
                       (tr-int (q n) (if (and (= p q) (= o n)) (the k-trs (cons k nil)) (the k-trs nil)))
                       (else y (the k-trs nil)))))))
          (if (null? m) (k-sc-meet-one k (cdr ls)) m)))))
(define k-sc-meet (subr (maxeff (read @globals) (read @t) spin) (k-trs k-trs) k-trs)
  (lambda (ks ls)
    (if (null? ks)
        nil
        (let ((m (k-sc-meet-one (car ks) ls)) (rest (k-sc-meet (cdr ks) ls)))
          (if (null? m) rest (the k-trs (cons (car m) rest)))))))
;; Whether `f` names a generative type's `up-` or `down-` conversion, the
;; identity.
(define k-sc-conversion? (subr (maxeff (read @globals) (read @t) (alloc @t) spin) (kx k-tscope) bool)
  (lambda (f sc)
    (tagcase (k-under f)
      (x-var (s a b)
        (let ((t (k-lookup s)))
          (and (>= t 0) (not (k-sc-in? sc s)) (< (k-sc-index (get k-sc-members) s 0) 0) (k-named-has? (get k-conversions) s t))))
      (else y #f))))
(define k-sc-forget-types (subr kstate (k-trs) k-trs)
  (lambda (ks)
    (if (null? ks)
        nil
        (the k-trs (cons (tagcase (car ks) (tr-part (p s t) (tr-part p s -1)) (else y (car ks))) (k-sc-forget-types (cdr ks)))))))
;; What is known of `x`'s value.
(define k-sc-tracked (subr (maxeff kstate spin) (kx k-tscope) k-trs)
  (lambda (x sc)
    (tagcase x
      (x-var (s a b) (k-sc-trs sc s))
      (x-the (t e a b) (k-sc-tracked e sc))
        (x-convention (c e a b) (k-sc-tracked e sc))
      (x-extract (e l a b) (k-sc-fields (k-sc-tracked e sc) l))
      (x-if (p c d a b) (k-sc-meet (k-sc-tracked c sc) (k-sc-tracked d sc)))
      (x-app (f args a b)
        (let ((op (k-sc-op f sc)))
          (cond ((and (k-sc-one? args) (k-sc-conversion? f sc)) (k-sc-forget-types (k-sc-tracked (car args) sc)))
                ((and (k-sc-one? args) (or (string=? op "car") (string=? op "cdr")))
                 (k-sc-pair-parts (k-sc-tracked (car args) sc) (string=? op "car")))
                ((and (k-sc-one? args) (or (string=? op "datum-car") (string=? op "datum-cdr")))
                 (k-sc-strict (k-sc-tracked (car args) sc)))
                ((and (k-sc-two? args) (or (string=? op "+") (string=? op "-")))
                 (let ((ka (k-sc-literal (car args))) (kb (k-sc-literal (car (cdr args)))))
                   (cond ((not (null? kb))
                          (k-sc-shift (k-sc-tracked (car args) sc) (if (string=? op "+") (car kb) (- 0 (car kb)))))
                         ((and (not (null? ka)) (string=? op "+")) (k-sc-shift (k-sc-tracked (car (cdr args)) sc) (car ka)))
                         (else nil))))
                (else nil))))
      (else y nil))))
(define k-sc-guarded? (subr (maxeff (read @globals) (read @t)) (k-guards int int) bool)
  (lambda (gs p b) (and (not (null? gs)) (or (and (= (car (car gs)) p) (= (cdr (car gs)) b)) (k-sc-guarded? (cdr gs) p b)))))
;; The current member's parameters that are `nat`s: bounded below by 0
;; without a test, since every argument passed for one is checked a natural.
(define k-sc-naturals (ref k-ids @t) (new nil))
;; Whether parameter `p` is bounded its way `b` (0 below, 1 above): by a
;; test, or, below, by being a `nat`.
(define k-sc-bounded? (subr (maxeff (read @globals) (read @t)) (k-guards int int) bool)
  (lambda (gs p b) (or (k-sc-guarded? gs p b) (and (= b 0) (k-has-id? (get k-sc-naturals) p)))))
;; Whether `ks` knows a value as a parameter, of the member walked, passed on
;; unchanged by every call.
(define k-sc-invariant-in? (subr (maxeff (read @globals) (read @t)) (k-trs) bool)
  (lambda (ks)
    (and (not (null? ks))
         (or (tagcase (car ks)
               (tr-part (p s t) (and (not s) (k-sc-guarded? (get k-sc-invariant) (get k-sc-current) p)))
               (else y #f))
             (k-sc-invariant-in? (cdr ks))))))
;; Whether `x` is the same at every call of the group: a literal, a
;; variable bound outside it, a parameter passed on unchanged, or the length
;; of a string or the sum or difference of such.
(define-rec
  (k-sc-fixed? (subr (maxeff kstate spin) (kx k-tscope) bool)
    (lambda (x sc)
      (tagcase x
        (x-const (t v a b) (= t k-int))
        (x-var (s a b)
          (if (k-sc-in? sc s) (k-sc-invariant-in? (k-sc-trs sc s)) (< (k-sc-index (get k-sc-members) s 0) 0)))
        (x-the (t e a b) (k-sc-fixed? e sc))
        (x-convention (c e a b) (k-sc-fixed? e sc))
        (x-app (f args a b)
          (let ((op (k-sc-op f sc)))
            ;; An array's length never changes, as a string's does not.
            (and (or (and (or (string=? op "string-length") (string=? op "array-length")) (k-sc-one? args))
                     (and (or (string=? op "+") (string=? op "-")) (k-sc-two? args)))
                 (k-sc-all-fixed? args sc))))
        (else y #f))))
  (k-sc-all-fixed? (subr (maxeff kstate spin) (kxs k-tscope) bool)
    (lambda (xs sc) (or (null? xs) (and (k-sc-fixed? (car xs) sc) (k-sc-all-fixed? (cdr xs) sc))))))
(define k-sc-append (subr kstate (k-guards k-guards) k-guards)
  (lambda (xs ys) (if (null? xs) ys (the k-guards (cons (car xs) (k-sc-append (cdr xs) ys))))))
(define k-sc-with (subr kstate (int k-ids k-guards) k-guards)
  (lambda (p bs rest) (if (null? bs) rest (the k-guards (cons (cons p (car bs)) (k-sc-with p (cdr bs) rest))))))
;; Bounds `bs` on each integer parameter `ks` knows of.
(define k-sc-bounds-on (subr kstate (k-trs k-ids) k-guards)
  (lambda (ks bs)
    (if (null? ks)
        nil
        (let ((rest (k-sc-bounds-on (cdr ks) bs)))
          (tagcase (car ks) (tr-int (p o) (k-sc-with p bs rest)) (else y rest))))))
(define k-sc-flip (subr kstate (k-ids) k-ids)
  (lambda (bs) (if (null? bs) nil (the k-ids (cons (- 1 (car bs)) (k-sc-flip (cdr bs)))))))
;; The bounds on parameters that `x` having the value `holds` shows.
(define k-sc-facts (subr (maxeff kstate spin) (kx k-tscope bool) k-guards)
  (lambda (x sc holds)
    (tagcase x
      (x-app (f args a b)
        (let ((op (k-sc-op f sc)))
          (cond ((and (k-sc-one? args) (string=? op "not")) (k-sc-facts (car args) sc (not holds)))
                ((k-sc-two? args)
                 (let* ((lt (or (string=? op "<") (string=? op "<=")))
                        (gt (or (string=? op ">") (string=? op ">=")))
                        ;; The bounds on the left operand.
                        (left (the k-ids (cond ((or (and lt holds) (and gt (not holds))) (cons 1 nil))
                                               ((or (and lt (not holds)) (and gt holds)) (cons 0 nil))
                                               ((and (string=? op "=") holds) (cons 0 (cons 1 nil)))
                                               (else nil))))
                        (x1 (car args))
                        (x2 (car (cdr args))))
                   (k-sc-append (if (k-sc-fixed? x2 sc) (k-sc-bounds-on (k-sc-tracked x1 sc) left) nil)
                                (if (k-sc-fixed? x1 sc) (k-sc-bounds-on (k-sc-tracked x2 sc) (k-sc-flip left)) nil))))
                (else nil))))
      ;; `(and p c)` and `(or p d)`, as they are parsed.
      (x-if (p c d a b)
        (cond ((and holds (k-sc-bool? d #f)) (k-sc-append (k-sc-facts p sc #t) (k-sc-facts c sc #t)))
              ((and (not holds) (k-sc-bool? c #t)) (k-sc-append (k-sc-facts p sc #f) (k-sc-facts d sc #f)))
              (else nil)))
      (else y nil))))

;; `g` with the edge from slot `f` to slot `t`, strict if `s`.
(define k-sc-add (subr kstate (k-graph int int bool) k-graph)
  (lambda (g f t s)
    (if (null? g)
        (the k-graph (cons (product (1 f) (2 t) (3 s)) nil))
        (let* ((e (car g)) (ef (extract e 1)) (et (extract e 2)))
          (cond ((and (= ef f) (= et t)) (the k-graph (cons (product (1 f) (2 t) (3 (or s (extract e 3)))) (cdr g))))
                ((or (< f ef) (and (= f ef) (< t et))) (the k-graph (cons (product (1 f) (2 t) (3 s)) g)))
                (else (the k-graph (cons e (k-sc-add (cdr g) f t s)))))))))
;; The edges to argument `q` from what `ks` knows of it.
(define k-sc-tr-edges (subr kstate (k-trs int k-guards k-graph) k-graph)
  (lambda (ks q gs g)
    (if (null? ks)
        g
        (k-sc-tr-edges (cdr ks) q gs
          (tagcase (car ks)
            (tr-part (p s t) (k-sc-add g (* 3 p) (* 3 q) s))
            (tr-int (p o)
              (let ((g1 (cond ((and (< o 0) (k-sc-bounded? gs p 0)) (k-sc-add g (+ (* 3 p) 1) (+ (* 3 q) 1) #t))
                              ((<= o 0) (k-sc-add g (+ (* 3 p) 1) (+ (* 3 q) 1) #f))
                              (else g))))
                (cond ((and (> o 0) (k-sc-bounded? gs p 1)) (k-sc-add g1 (+ (* 3 p) 2) (+ (* 3 q) 2) #t))
                      ((>= o 0) (k-sc-add g1 (+ (* 3 p) 2) (+ (* 3 q) 2) #f))
                      (else g1)))))))))
(define k-sc-arg-edges (subr (maxeff kstate spin) (kxs int k-tscope k-guards k-graph) k-graph)
  (lambda (args q sc gs g)
    (if (null? args) g (k-sc-arg-edges (cdr args) (+ q 1) sc gs (k-sc-tr-edges (k-sc-tracked (car args) sc) q gs g)))))
;; A call of member `to` with `args`, from the member walked.
(define k-sc-unchanged (subr kstate (k-trs) int)
  (lambda (ks)
    (cond ((null? ks) -1)
          ((tagcase (car ks) (tr-part (p s t) (not s)) (else y #f)) (tagcase (car ks) (tr-part (p s t) p) (else y -1)))
          (else (k-sc-unchanged (cdr ks))))))
(define k-sc-passing (subr (maxeff kstate spin) (kxs k-tscope) k-ids)
  (lambda (args sc) (if (null? args) nil (the k-ids (cons (k-sc-unchanged (k-sc-tracked (car args) sc)) (k-sc-passing (cdr args) sc))))))
;; Whether `ks` knows of a pair at a region that is not `acyclic`.
(define k-sc-any-written? (subr (maxeff (read @globals) (read @t) spin) (k-trs) bool)
  (lambda (ks)
    (and (not (null? ks))
         (or (tagcase (car ks)
               (tr-part (p s t)
                 (tagcase (k-ty-known t) (ty-pair (x y r) (tagcase r (r-frozen (q fin) (not fin)) (else z #t))) (else z #f)))
               (else z #f))
             (k-sc-any-written? (cdr ks))))))
;; Whether some argument is the `car` or `cdr` of a parameter's part at a
;; region that is not `acyclic`.
(define k-sc-written-arg? (subr (maxeff kstate spin) (kxs k-tscope) bool)
  (lambda (args sc)
    (and (not (null? args))
         (or (tagcase (car args)
               (x-app (f xs a b)
                 (let ((op (k-sc-op f sc)))
                   (and (or (string=? op "car") (string=? op "cdr")) (k-sc-one? xs) (k-sc-any-written? (k-sc-tracked (car xs) sc)))))
               (else y #f))
             (k-sc-written-arg? (cdr args) sc)))))
;; The first count in `ks` with no fixed bound its way, in words, or "".
(define k-sc-count-hint (subr (maxeff (read @globals) (read @t)) (k-trs k-guards) string)
  (lambda (ks gs)
    (if (null? ks)
        ""
        (let ((h (tagcase (car ks)
                   (tr-int (p o)
                     (cond ((and (< o 0) (not (k-sc-bounded? gs p 0))) "it counts down, but nothing fixed bounds the count below")
                           ((and (> o 0) (not (k-sc-bounded? gs p 1))) "it counts up, but nothing fixed bounds the count above")
                           (else "")))
                   (else y ""))))
          (if (string=? h "") (k-sc-count-hint (cdr ks) gs) h)))))
(define k-sc-count-hints (subr (maxeff kstate spin) (kxs k-tscope k-guards) string)
  (lambda (args sc gs)
    (if (null? args)
        ""
        (let ((h (k-sc-count-hint (k-sc-tracked (car args) sc) gs)))
          (if (string=? h "") (k-sc-count-hints (cdr args) sc gs) h)))))
;; Why a call with `args` may shrink nothing, or "".
(define k-sc-hint (subr (maxeff kstate spin) (kxs k-tscope k-guards) string)
  (lambda (args sc gs)
    (if (k-sc-written-arg? args sc)
        "a part of a list that may be written is no smaller: it may be cyclic"
        (k-sc-count-hints args sc gs))))
(define k-sc-call (subr (maxeff kstate spin) (int kxs k-tscope k-guards) unit)
  (lambda (to args sc gs)
    (begin
     (set k-sc-hints (cons (k-sc-hint args sc gs) (get k-sc-hints)))
     (set k-sc-passed (cons (product (1 (get k-sc-current)) (2 to) (3 (k-sc-passing args sc))) (get k-sc-passed)))
     (set k-sc-calls (cons (product (1 (get k-sc-current)) (2 to) (3 (k-sc-arg-edges args 0 sc gs nil))) (get k-sc-calls))))))

(define k-sc-hide-params (subr kstate ((listof (productof (1 symbol) (2 k-ids)) acyclic) k-tscope) k-tscope)
  (lambda (ps sc) (if (null? ps) sc (k-sc-hide-params (cdr ps) (cons (cons (extract (car ps) 1) (the k-trs nil)) sc)))))
(define k-sc-hide-group (subr kstate (k-group k-tscope) k-tscope)
  (lambda (bs sc) (if (null? bs) sc (k-sc-hide-group (cdr bs) (cons (cons (extract (car bs) 1) (the k-trs nil)) sc)))))
(define k-sc-let-scope (subr (maxeff kstate spin) ((listof (productof (1 symbol) (2 kx)) acyclic) k-tscope k-tscope) k-tscope)
  (lambda (bs outer sc)
    (if (null? bs) sc (k-sc-let-scope (cdr bs) outer (cons (cons (extract (car bs) 1) (k-sc-tracked (extract (car bs) 2) outer)) sc)))))
(define k-sc-arm-scope (subr (maxeff kstate spin) (k-names k-trs symbol int k-tscope) k-tscope)
  (lambda (ns whole tag i sc)
    (if (null? ns) sc (k-sc-arm-scope (cdr ns) whole tag (+ i 1) (cons (cons (car ns) (k-sc-variant whole tag i)) sc)))))
(define-rec
  (k-sc-walk-list (subr (maxeff kstate spin) (kxs k-tscope k-guards) unit)
    (lambda (xs sc gs) (if (null? xs) #u (begin (k-sc-walk (car xs) sc gs) (k-sc-walk-list (cdr xs) sc gs)))))
  (k-sc-walk-group (subr (maxeff kstate spin) (k-group k-tscope k-guards) unit)
    (lambda (bs sc gs) (if (null? bs) #u (begin (k-sc-walk (extract (car bs) 3) sc gs) (k-sc-walk-group (cdr bs) sc gs)))))
  (k-sc-walk-lets (subr (maxeff kstate spin) ((listof (productof (1 symbol) (2 kx)) acyclic) k-tscope k-guards) unit)
    (lambda (bs sc gs) (if (null? bs) #u (begin (k-sc-walk (extract (car bs) 2) sc gs) (k-sc-walk-lets (cdr bs) sc gs)))))
  (k-sc-walk-fields (subr (maxeff kstate spin) ((listof (productof (1 symbol) (2 kx)) acyclic) k-tscope k-guards) unit)
    (lambda (fs sc gs) (if (null? fs) #u (begin (k-sc-walk (extract (car fs) 2) sc gs) (k-sc-walk-fields (cdr fs) sc gs)))))
  (k-sc-walk-arms (subr (maxeff kstate spin) (k-arms k-trs k-tscope k-guards) unit)
    (lambda (arms whole sc gs)
      (if (null? arms)
          #u
          (let* ((arm (car arms))
                 (tag (extract arm 1))
                 (inner (if (extract arm 2)
                            (k-sc-arm-scope (extract arm 3) whole tag 0 sc)
                            (the k-tscope (cons (cons (car (extract arm 3)) (k-sc-variant whole tag -1)) sc)))))
            (begin (k-sc-walk (extract arm 4) inner gs) (k-sc-walk-arms (cdr arms) whole sc gs))))))
  (k-sc-walk (subr (maxeff kstate spin) (kx k-tscope k-guards) unit)
    (lambda (x sc gs)
      (tagcase x
        (x-var (s a b)
          (let ((m (k-sc-member sc s)))
            (if (and (>= m 0) (null? (get k-sc-escapes))) (set k-sc-escapes (cons (cons (get k-sc-current) m) nil)) #u)))
        (x-const (t v a b) #u)
        (x-app (f args a b)
          (let ((to (tagcase (k-under f) (x-var (s fa fb) (k-sc-member sc s)) (else y -1))))
            (begin (if (>= to 0) (k-sc-call to args sc gs) (k-sc-walk f sc gs))
                   (k-sc-walk-list args sc gs))))
        (x-lambda (ps body a b) (k-sc-walk body (k-sc-hide-params ps sc) gs))
        (x-plambda (bs body a b) (k-sc-walk body sc gs))
        (x-proj (body ds a b) (k-sc-walk body sc gs))
        (x-the (t body a b) (k-sc-walk body sc gs))
        (x-convention (c body a b) (k-sc-walk body sc gs))
        (x-letregion (k r i body a b) (k-sc-walk body sc gs))
        (x-rlambda (r l a b) (begin (k-sc-walk r sc gs) (k-sc-walk l sc gs)))
        (x-if (p c d a b)
          (begin (k-sc-walk p sc gs)
                 (k-sc-walk c sc (k-sc-append (k-sc-facts p sc #t) gs))
                 (k-sc-walk d sc (k-sc-append (k-sc-facts p sc #f) gs))))
        (x-letrec (bs body a b)
          (let ((inner (k-sc-hide-group bs sc)))
            (begin (k-sc-walk-group bs inner gs) (k-sc-walk body inner gs))))
        (x-let (bs body a b) (begin (k-sc-walk-lets bs sc gs) (k-sc-walk body (k-sc-let-scope bs sc sc) gs)))
        (x-begin (xs a b) (k-sc-walk-list xs sc gs))
        (x-bloblet (n i xs a b) (k-sc-walk-list xs sc gs))
        (x-prompt (t body h a b) (begin (k-sc-walk t sc gs) (k-sc-walk body sc gs) (k-sc-walk h sc gs)))
        (x-product (fs a b) (k-sc-walk-fields fs sc gs))
        (x-extract (e l a b) (k-sc-walk e sc gs))
        (x-sum (tag e a b) (k-sc-walk e sc gs))
        (x-tagcase (e arms els a b)
          (let ((whole (k-sc-tracked e sc)))
            (begin (k-sc-walk e sc gs)
                   (k-sc-walk-arms arms whole sc gs)
                   ;; `else` sees the same value, its type narrowed.
                   (if (null? els)
                       #u
                       (k-sc-walk (extract (car els) 2) (cons (cons (extract (car els) 1) (k-sc-parts whole)) sc) gs)))))))))

(define k-sc-compose-one (subr kstate (k-edge k-graph k-graph) k-graph)
  (lambda (e b out)
    (cond ((null? b) out)
          ((= (extract e 2) (extract (car b) 1))
           (k-sc-compose-one e (cdr b) (k-sc-add out (extract e 1) (extract (car b) 2) (or (extract e 3) (extract (car b) 3)))))
          (else (k-sc-compose-one e (cdr b) out)))))
(define k-sc-compose (subr kstate (k-graph k-graph k-graph) k-graph)
  (lambda (a b out) (if (null? a) out (k-sc-compose (cdr a) b (k-sc-compose-one (car a) b out)))))
(define k-sc-same? (subr (maxeff (read @globals) (read @t)) (k-graph k-graph) bool)
  (lambda (a b)
    (if (null? a)
        (null? b)
        (and (not (null? b))
             (= (extract (car a) 1) (extract (car b) 1))
             (= (extract (car a) 2) (extract (car b) 2))
             (if (extract (car a) 3) (extract (car b) 3) (not (extract (car b) 3)))
             (k-sc-same? (cdr a) (cdr b))))))
(define k-sc-has? (subr (maxeff (read @globals) (read @t)) (k-calls int int k-graph) bool)
  (lambda (cs f h g)
    (and (not (null? cs))
         (or (and (= (extract (car cs) 1) f) (= (extract (car cs) 2) h) (k-sc-same? (extract (car cs) 3) g))
             (k-sc-has? (cdr cs) f h g)))))
(define k-sc-dedup (subr kstate (k-calls k-calls) k-calls)
  (lambda (cs out)
    (cond ((null? cs) out)
          ((k-sc-has? out (extract (car cs) 1) (extract (car cs) 2) (extract (car cs) 3)) (k-sc-dedup (cdr cs) out))
          (else (k-sc-dedup (cdr cs) (cons (car cs) out))))))
(define k-sc-strict-loop? (subr (maxeff (read @globals) (read @t)) (k-graph) bool)
  (lambda (g) (and (not (null? g)) (or (and (= (extract (car g) 1) (extract (car g) 2)) (extract (car g) 3)) (k-sc-strict-loop? (cdr g))))))
;; Whether every graph from a member to itself that is its own composition
;; has a strict loop.
(define k-sc-ok? (subr kstate (k-calls) bool)
  (lambda (cs)
    (or (null? cs)
        (let ((c (car cs)))
          (and (or (not (= (extract c 1) (extract c 2)))
                   (not (k-sc-same? (k-sc-compose (extract c 3) (extract c 3) nil) (extract c 3)))
                   (k-sc-strict-loop? (extract c 3)))
               (k-sc-ok? (cdr cs)))))))
;; A graph's closure may grow; beyond this many, the group does not pass.
(define k-sc-most int 4000)
(define-rec
  (k-sc-close (subr kstate (k-calls k-calls int) bool)
    (lambda (todo all n)
      (if (null? todo)
          (k-sc-ok? all)
          (let ((c (car todo))) (k-sc-extend (extract c 1) (extract c 2) (extract c 3) (get k-sc-calls) (cdr todo) all n)))))
  (k-sc-extend (subr kstate (int int k-graph k-calls k-calls k-calls int) bool)
    (lambda (f g a calls todo all n)
      (cond ((null? calls) (k-sc-close todo all n))
            ((not (= (extract (car calls) 1) g)) (k-sc-extend f g a (cdr calls) todo all n))
            (else
             (let ((cg (k-sc-compose a (extract (car calls) 3) nil)) (h (extract (car calls) 2)))
               (cond ((k-sc-has? all f h cg) (k-sc-extend f g a (cdr calls) todo all n))
                     ((>= n k-sc-most) (begin (set k-sc-too-many #t) #f))
                     (else (let ((new (product (1 f) (2 h) (3 cg))))
                             (k-sc-extend f g a (cdr calls) (cons new todo) (cons new all) (+ n 1)))))))))))

;; A binding's lambda, under `plambda`, `the` and `rlambda`.
(define k-sc-lambda-of (subr (read @globals) (kx) kx)
  (lambda (x)
    (tagcase x
      (x-plambda (bs body a b) (k-sc-lambda-of body))
      (x-the (t body a b) (k-sc-lambda-of body))
      (x-rlambda (r l a b) (k-sc-lambda-of l))
      (else y y))))
;; The parameter types of a declared type, under its binders.
(define k-sc-param-types (subr (maxeff (read @globals) (read @t) spin) (int) k-ids)
  (lambda (t) (tagcase (k-get t) (ty-poly (bs body) (k-sc-param-types body)) (ty-subr (e ps r cv) ps) (else y nil))))
;; The parameters `ps`, the `j`th on, each known as itself.
(define k-sc-param-scope (subr (maxeff kstate spin) ((listof (productof (1 symbol) (2 k-ids)) acyclic) k-ids int k-tscope) k-tscope)
  (lambda (ps ts j sc)
    (if (null? ps)
        sc
        (let* ((t (car ts))
               (natural (tagcase (k-get (k-resolve t)) (ty-nat (z) #t) (else y #f)))
               (noted (if natural (set k-sc-naturals (cons j (get k-sc-naturals))) #u))
               (ks (the k-trs (cons (tr-part j #f t) (if (or natural (= (k-resolve t) (k-resolve k-int))) (the k-trs (cons (tr-int j 0) nil)) nil)))))
          (k-sc-param-scope (cdr ps) (cdr ts) (+ j 1) (cons (cons (extract (car ps) 1) ks) sc))))))
(define k-sc-walk-members (subr (maxeff kstate spin) (k-group int) bool)
  (lambda (bs i)
    (or (null? bs)
        (tagcase (k-sc-lambda-of (extract (car bs) 3))
          (x-lambda (ps body a b)
            (let ((ts (k-sc-param-types (extract (car bs) 2))))
              (and (<= (k-length ps) (k-length ts))
                   (begin (set k-sc-current i)
                          (set k-sc-naturals nil)
                          (k-sc-walk body (k-sc-param-scope ps ts 0 nil) nil)
                          (and (null? (get k-sc-escapes)) (k-sc-walk-members (cdr bs) (+ i 1)))))))
          (else y #f)))))
(define k-sc-names (subr kstate (k-group) k-names)
  (lambda (bs) (if (null? bs) nil (the k-names (cons (extract (car bs) 1) (k-sc-names (cdr bs)))))))
(define k-sc-upto (subr kstate (int int) k-ids)
  (lambda (j n)
    (letrec ((down (subr kstate (int k-ids) k-ids) (lambda (i acc) (if (< i j) acc (down (- i 1) (the k-ids (cons i acc)))))))
      (down (- n 1) nil))))
;; Every (member . parameter) of the group, the `i`th member on.
(define k-sc-all-params (subr kstate (k-group int k-guards) k-guards)
  (lambda (bs i out)
    (if (null? bs)
        out
        (k-sc-all-params (cdr bs) (+ i 1)
          (tagcase (k-sc-lambda-of (extract (car bs) 3))
            (x-lambda (ps body a b) (k-sc-with i (k-sc-upto 0 (k-length ps)) out))
            (else y out))))))
(define k-sc-drop (subr kstate (k-guards int int) k-guards)
  (lambda (gs i j)
    (cond ((null? gs) gs)
          ((and (= (car (car gs)) i) (= (cdr (car gs)) j)) (k-sc-drop (cdr gs) i j))
          (else (the k-guards (cons (car gs) (k-sc-drop (cdr gs) i j)))))))
;; `inv` less what the call from `from` to `to` passing `args` changes.
(define k-sc-keep-args (subr kstate (k-guards int int k-ids int) k-guards)
  (lambda (inv from to args j)
    (if (null? args)
        inv
        (let ((p (car args)))
          (k-sc-keep-args (if (and (>= p 0) (k-sc-guarded? inv from p)) inv (k-sc-drop inv to j)) from to (cdr args) (+ j 1))))))
(define k-sc-keep-all (subr kstate (k-guards k-passed) k-guards)
  (lambda (inv ps)
    (if (null? ps)
        inv
        (let ((c (car ps))) (k-sc-keep-all (k-sc-keep-args inv (extract c 1) (extract c 2) (extract c 3) 0) (cdr ps))))))
;; The invariant parameters: the greatest set every call keeps.
(define k-sc-invariants (subr (maxeff kstate spin) (k-guards) k-guards)
  (lambda (inv)
    (let ((next (k-sc-keep-all inv (get k-sc-passed))))
      (if (= (k-length next) (k-length inv)) inv (k-sc-invariants next)))))
(define k-sc-member-name (subr (maxeff (read @globals) (read @t)) (int) string)
  (lambda (i) (symbol->string (k-nth (get k-sc-members) i))))
(define k-sc-strict-any? (subr (read @globals) (k-graph) bool)
  (lambda (g) (and (not (null? g)) (or (extract (car g) 3) (k-sc-strict-any? (cdr g))))))
(define k-sc-has-string? (subr (read @globals) ((listof string acyclic) string) bool)
  (lambda (xs s) (and (not (null? xs)) (or (string=? (car xs) s) (k-sc-has-string? (cdr xs) s)))))
;; The calls, in the order met, that pass nothing strictly smaller, and
;; either nothing related to the caller's parameters or with a hint why;
;; each once, in words (newest first). One passing its caller's parameters
;; on unchanged is harmless.
(define k-sc-flat (subr kstate (k-calls (listof string acyclic) (listof string acyclic)) (listof string acyclic))
  (lambda (cs hs out)
    (if (null? cs)
        out
        (let* ((c (car cs))
               (s1 (k-cat5 "the call of `" (k-sc-member-name (extract c 2)) "` in `" (k-sc-member-name (extract c 1)) "`"))
               (s (if (string=? (car hs) "") s1 (k-cat4 s1 " (" (car hs) ")"))))
          (k-sc-flat (cdr cs) (cdr hs)
                     (if (or (k-sc-strict-any? (extract c 3))
                             (and (not (null? (extract c 3))) (string=? (car hs) ""))
                             (k-sc-has-string? out s))
                         out
                         (the (listof string acyclic) (cons s out))))))))
(define k-sc-escape-why (subr (maxeff (read @globals) (read @t)) () string)
  (lambda ()
    (let ((e (car (get k-sc-escapes))))
      (k-cat5 "`" (k-sc-member-name (cdr e)) "` is named in `" (k-sc-member-name (car e))
              "` other than as a call's operator: whoever is given it may call it again, with anything"))))
;; Why the walked calls may not end.
(define k-sc-calls-why (subr kstate () string)
  (lambda ()
    (let ((all (k-sc-dedup (get k-sc-calls) nil)))
      (cond ((k-sc-close all all (k-length all)) "")
            ((get k-sc-too-many) "the calls combine in too many ways to follow")
            (else
             (let ((flat (the (listof string acyclic)
                              (reverse (k-sc-flat (the k-calls (reverse (get k-sc-calls)))
                                                  (the (listof string acyclic) (reverse (get k-sc-hints))) nil)))))
               (if (null? flat)
                   "no argument keeps shrinking around every loop of calls"
                   (string-append "nothing smaller, or related, is passed by " (k-join flat ", ")))))))))
;; Whether every run of the group `bs` ends, so that calls within it need
;; not say `spin`: "" if so, and otherwise why not, in words for an error.
;; Walked twice: first to learn which parameters every call passes on
;; unchanged, then with them as bounds.
(define k-termination (subr (maxeff kstate spin) (k-group) string)
  (lambda (bs)
    (begin
      (set k-sc-members (k-sc-names bs))
      (set k-sc-calls nil)
      (set k-sc-hints nil)
      (set k-sc-passed nil)
      (set k-sc-invariant nil)
      (set k-sc-escapes nil)
      (set k-sc-too-many #f)
      (let ((walked (k-sc-walk-members bs 0)))
        (cond ((not (null? (get k-sc-escapes))) (k-sc-escape-why))
              ((not walked) "it is not a lambda")
              (else
               (let ((inv (k-sc-invariants (k-sc-all-params bs 0 nil))))
                 (if (null? inv)
                     (k-sc-calls-why)
                     (begin
                       (set k-sc-invariant inv)
                       (set k-sc-calls nil)
                       (set k-sc-hints nil)
                       (set k-sc-passed nil)
                       (let ((again (k-sc-walk-members bs 0)))
                         (cond ((not (null? (get k-sc-escapes))) (k-sc-escape-why))
                               ((not again) "it is not a lambda")
                               (else (k-sc-calls-why)))))))))))))
;; Note why each of `g` may not end.
(define k-note-why (subr kstate (k-group string) unit)
  (lambda (g why)
    (if (null? g)
        #u
        (begin (set k-spin-why (cons (product (1 (extract (car g) 1)) (2 (extract (car g) 2)) (3 why)) (get k-spin-why)))
               (k-note-why (cdr g) why)))))
(define k-why-of (subr (maxeff (read @globals) (read @t)) ((listof (productof (1 symbol) (2 int) (3 string)) acyclic) symbol int) string)
  (lambda (ws n t)
    (cond ((null? ws) "")
          ((and (symbol=? (extract (car ws) 1) n) (= (extract (car ws) 2) t)) (extract (car ws) 3))
          (else (k-why-of (cdr ws) n t)))))
(define k-text-has? (subr (maxeff (read @globals) spin) (string string int) bool)
  (lambda (hay needle i)
    (and (<= (+ i (string-length needle)) (string-length hay))
         (or (string=? (substring hay i (+ i (string-length needle))) needle) (k-text-has? hay needle (+ i 1))))))
;; `f`, checking what `n` is declared `t`; an error at `a`..`b` itself says
;; so, and, if it is about `spin` and `n`'s group may not end, why not.
(define k-declaring (subr (maxeff (read @globals) checks spin) ((subr (maxeff checks spin) () k-te) int int symbol int) k-te)
  (lambda (f a b n t)
    (let ((r (prompt k-tag (k-done (f)) (lambda (r) r))))
      (tagcase r
        (k-done (te) te)
        (k-err (m ea eb)
          (if (and (= ea a) (= eb b))
              (let* ((why (k-why-of (get k-spin-why) n t))
                     (tail (if (and (not (string=? why "")) (k-text-has? m "spin" 0)) (string-append "; it may not end: " why) "")))
                (k-fail (k-cat4 (k-cat4 (k-quote (symbol->string n)) " is declared a " (k-show-ty t) ": ") m tail "") ea eb))
              (k-fail m ea eb)))
        (k-ok (xs) (k-fail "k-ok inside" a b))))))

;; Every binding of a `letrec` a lambda, or an error at the first that is not.
(define k-letrec-lambdas (subr checks (k-group) unit)
  (lambda (bs)
    (cond ((null? bs) #u)
          ((k-lambda? (extract (car bs) 3)) (k-letrec-lambdas (cdr bs)))
          (else (let ((x (extract (car bs) 3))) (k-fail (k-letrec-not-lambda (extract (car bs) 1)) (k-start x) (k-end x)))))))

;; What a test shows when it holds, and when not.
(define-type k-branch-facts (pairof (listof k-size-fact acyclic) (listof k-size-fact acyclic) acyclic))
(define k-branch-facts-of (subr pure ((listof k-size-fact acyclic) (listof k-size-fact acyclic)) k-branch-facts)
  (lambda (yes no) (the k-branch-facts (cons yes no))))
;; The fact `lin ≥ 0`, alone.
(define k-ge-fact (subr pure (k-size) (listof k-size-fact acyclic))
  (lambda (lin) (the (listof k-size-fact acyclic) (cons (product (1 lin) (2 #f)) nil))))
;; `x < y`, as `y - x - 1 ≥ 0`; `x ≤ y`, as `y - x ≥ 0`.
(define k-lt-fact (subr (read @globals) (k-size k-size) (listof k-size-fact acyclic))
  (lambda (x y) (k-ge-fact (k-size-plus (k-size-add-scaled y x -1) -1))))
(define k-le-fact (subr (read @globals) (k-size k-size) (listof k-size-fact acyclic))
  (lambda (x y) (k-ge-fact (k-size-add-scaled y x -1))))
;; The size an argument is, when a natural literal or a variable of type
;; `(nat s)` (none or one).
(define k-nat-size (subr (maxeff (read @globals) (read @t) spin) (kx) (listof k-size acyclic))
  (lambda (x)
    (tagcase x
      (x-const (ty k a b) (if (and (= ty k-int) (>= k 0)) (the (listof k-size acyclic) (cons (k-size-lit k) nil)) nil))
      (x-var (v a b)
        (let ((t (k-lookup v)))
          (if (< t 0)
              nil
              (tagcase (k-get (k-resolve t)) (ty-nat (z) (the (listof k-size acyclic) (cons z nil))) (else y nil)))))
      (else y nil))))
;; `xs : (nlist T n)` shows `n = 0` when null, and `n - 1 ≥ 0` when not.
(define k-null-facts (subr (maxeff (read @globals) (read @t) (alloc @t) spin) (kx) k-branch-facts)
  (lambda (x)
    (let ((none (k-branch-facts-of nil nil)))
      (tagcase x
        (x-var (v va vb)
          (let ((vt (k-lookup v)))
            (if (< vt 0)
                none
                (tagcase (k-get vt)
                  (ty-nlist (e z r)
                    (tagcase z
                      (sz-lin (k ts)
                        (k-branch-facts-of (the (listof k-size-fact acyclic) (cons (product (1 z) (2 #t)) nil)) (k-ge-fact (k-size-plus z -1))))
                      (else w none)))
                  (else w none)))))
        (else y none)))))
;; What a comparison `(op a b)` of naturals shows, when both have sizes.
(define k-compare-facts (subr (maxeff (read @globals) (read @t) (alloc @t) spin) (string kx kx) k-branch-facts)
  (lambda (op a b)
    (let ((xs (k-nat-size a)) (ys (k-nat-size b)) (none (k-branch-facts-of nil nil)))
      (if (or (null? xs) (null? ys) (tagcase (car xs) (sz-finite () #t) (else w #f)) (tagcase (car ys) (sz-finite () #t) (else w #f)))
          none
          (let ((x (car xs)) (y (car ys)))
            (cond ((string=? op "<") (k-branch-facts-of (k-lt-fact x y) (k-le-fact y x)))
                  ((string=? op "<=") (k-branch-facts-of (k-le-fact x y) (k-lt-fact y x)))
                  ((string=? op ">") (k-branch-facts-of (k-lt-fact y x) (k-le-fact x y)))
                  ((string=? op ">=") (k-branch-facts-of (k-le-fact y x) (k-lt-fact x y)))
                  (else
                   (let ((no (cond ((= (k-size-as-lit y) 0) (k-ge-fact (k-size-plus x -1)))
                                   ((= (k-size-as-lit x) 0) (k-ge-fact (k-size-plus y -1)))
                                   (else (the (listof k-size-fact acyclic) nil)))))
                     (k-branch-facts-of (the (listof k-size-fact acyclic) (cons (product (1 (k-size-add-scaled x y -1)) (2 #t)) nil)) no)))))))))
;; `v` and `k` of `(length-is? v k)` or `(certify-length v k)`: the
;; variable, its binding, and the length, a natural literal or a variable
;; of type `(nat s)` (none or one).
(define k-length-arg (subr (maxeff (read @globals) (read @t) (alloc @t) spin) (kx kx) (listof k-cert-len acyclic))
  (lambda (a n)
    (tagcase a
      (x-var (v va vb)
        (if (tagcase n (x-const (ty k ka kb) #t) (x-var (w wa wb) #t) (else y #f))
            (let ((z (k-nat-size n)))
              (if (null? z) nil (the (listof k-cert-len acyclic) (cons (product (1 v) (2 (k-binding-depth v)) (3 (car z))) nil))))
            nil))
      (else y nil))))
;; What `length-is?` has just confirmed: a variable, its binding, the length.
(define-type k-cert-len (productof (1 symbol) (2 int) (3 k-size)))
(define k-cert-len-has? (subr (maxeff (read @globals) (read @t)) ((listof k-cert-len acyclic) k-cert-len) bool)
  (lambda (cs c)
    (and (not (null? cs))
         (or (and (symbol=? (extract (car cs) 1) (extract c 1)) (= (extract (car cs) 2) (extract c 2)) (k-size=? (extract (car cs) 3) (extract c 3)))
             (k-cert-len-has? (cdr cs) c)))))
;; If `p` is `(length-is? v k)`, the variable, its binding, and the length.
(define k-length-test (subr (maxeff (read @globals) (read @t) (alloc @t) spin) (kx) (listof k-cert-len acyclic))
  (lambda (p)
    (tagcase p
      (x-app (f args a b)
        (tagcase f
          (x-var (op fa fb)
            (let ((t (k-lookup op)))
              (if (and (string=? (symbol->string op) "length-is?") (>= t 0) (k-named-has? (get k-std) op t)
                       (not (null? args)) (not (null? (cdr args))) (null? (cdr (cdr args))))
                  (k-length-arg (car args) (car (cdr args)))
                  nil)))
          (else y nil)))
      (else y nil))))
;; Whether `x` may be a natural of a size without being told what it is: an
;; integer literal, a variable, or a `+`, `-` or `length`.
(define k-natural-by-itself? (subr (maxeff (read @globals) (read @t) spin) (kx) bool)
  (lambda (x)
    (tagcase x
      (x-const (ty k a b) (= ty k-int))
      (x-var (v a b) #t)
      (x-app (f args a b)
        (tagcase f
          (x-var (op fa fb)
            (let ((t (k-lookup op)) (n (symbol->string op)))
              (and (or (string=? n "+") (string=? n "-") (string=? n "length") (string=? n "string-length") (string=? n "array-length"))
                   (>= t 0) (k-named-has? (get k-std) op t))))
          (else y #f)))
      (else y #f))))
;; The size an operand of `+` or `-` of type `t` is: a natural literal's,
;; or a `(nat s)`'s (none or one).
(define k-operand-size (subr (maxeff (read @globals) (read @t) spin) (kx int) (listof k-size acyclic))
  (lambda (x t)
    (let ((lit (tagcase x (x-const (ty k a b) (if (and (= ty k-int) (>= k 0)) k -1)) (else y -1))))
      (if (>= lit 0)
          (the (listof k-size acyclic) (cons (k-size-lit lit) nil))
          (tagcase (k-get (k-resolve t)) (ty-nat (z) (the (listof k-size acyclic) (cons z nil))) (else y nil))))))
;; `(+ a b)` and `(- a b)` of naturals: the sum, and the difference where
;; the facts show it no less than 0 (none or one).
(define k-nat-arith-size (subr (maxeff (read @globals) (read @t)) (string k-size k-size) (listof k-size acyclic))
  (lambda (op a b)
    (cond ((string=? op "+") (the (listof k-size acyclic) (cons (k-size-add-scaled a b 1) nil)))
          ((and (tagcase a (sz-finite () #f) (else w #t)) (k-size-nonneg? (k-size-add-scaled a b -1)))
           (the (listof k-size acyclic) (cons (k-size-add-scaled a b -1) nil)))
          (else nil))))
;; What `p` shows about sizes when it holds, and when not (each none or
;; one): `(null? xs)`, `xs : (nlist T n)`, shows `n = 0`, or `n - 1 ≥ 0`.
;; What `p` shows about sizes when it holds, and when not (each none or
;; one). `(null? xs)`, `xs : (nlist T n)`: `n = 0`, or `n - 1 ≥ 0`. A
;; comparison of naturals: `(< a b)`, `b - a - 1 ≥ 0`, or `a - b ≥ 0`;
;; `(= a 0)`, `a = 0`, or, a natural not 0, `a - 1 ≥ 0`.
(define k-test-facts (subr (maxeff (read @globals) (read @t) (alloc @t) spin) (kx) k-branch-facts)
  (lambda (p)
    (let ((none (k-branch-facts-of nil nil)))
      (tagcase p
        (x-app (f args a b)
          (tagcase f
            (x-var (op fa fb)
              (let ((t (k-lookup op)) (name (symbol->string op)))
                (cond ((not (and (>= t 0) (k-named-has? (get k-std) op t))) none)
                      ((string=? name "null?") (if (k-sc-one-arg? args) (k-null-facts (car args)) none))
                      ((and (or (string=? name "<") (string=? name "<=") (string=? name ">") (string=? name ">=") (string=? name "="))
                            (not (null? args)) (not (null? (cdr args))) (null? (cdr (cdr args))))
                       (k-compare-facts name (car args) (car (cdr args))))
                      (else none))))
            (else y none)))
        (else y none)))))
(define k-with-fact (subr (alloc @t) ((listof k-size-fact acyclic) (listof k-size-fact acyclic)) (listof k-size-fact acyclic))
  (lambda (f fs) (if (null? f) fs (the (listof k-size-fact acyclic) (cons (car f) fs)))))
;; If `p` is `(name v)`, `name` standard, the variable, as the binding it is
;; (none or one).
(define k-certifying-test (subr (maxeff (read @globals) (read @t) (alloc @t) spin) (kx string) (listof (pairof symbol int @t) acyclic))
  (lambda (p name)
    (tagcase p
      (x-app (f args a b)
        (tagcase (k-under f)
          (x-var (op fa fb)
            (let ((t (k-lookup op)))
              (if (and (string=? (symbol->string op) name) (>= t 0) (k-named-has? (get k-std) op t) (k-sc-one-arg? args))
                  (tagcase (car args)
                    (x-var (v va vb) (the (listof (pairof symbol int @t) acyclic) (cons (cons v (k-binding-depth v)) nil)))
                    (else y nil))
                  nil)))
          (else y nil)))
      (else y nil))))
;; If `p` is `(acyclic? v)`, the variable, as the binding it is (none or one).
(define k-acyclic-test (subr (maxeff (read @globals) (read @t) (alloc @t) spin) (kx) (listof (pairof symbol int @t) acyclic))
  (lambda (p) (k-certifying-test p "acyclic?")))
;; If `p` is `(nat? v)`, the variable, as the binding it is (none or one).
(define k-nat-test (subr (maxeff (read @globals) (read @t) (alloc @t) spin) (kx) (listof (pairof symbol int @t) acyclic))
  (lambda (p) (k-certifying-test p "nat?")))
(define-rec
  (k-synth (subr (maxeff checks spin) (kx) k-te)
    (lambda (x)
      (let* ((r (k-synth-node x)) (e (k-frozen x (extract r 2))))
        (begin (k-note-effect x e) (k-te (extract r 1) e)))))
  (k-synth-node (subr (maxeff checks spin) (kx) k-te)
    (lambda (x)
      (tagcase x
        (x-var (s a b)
          (let ((t (k-lookup s)))
            (if (< t 0) (k-fail (k-unbound s) a b) (k-te t (k-naming-effect s t)))))
        (x-const (t v a b) (k-te t nil))
        (x-lambda (ps body a b) (k-synth-lambda-as x nil -1))
        (x-app (f args a b) (k-synth-app x f args -1))
        (x-the (t e a b) (k-te t (k-check e t)))
        (x-convention (c e a b)
          (let* ((r (k-synth e)) (t (k-resolve (extract r 1))))
            (tagcase (k-get t)
              (ty-subr (fe ps res from)
                (begin (if (k-conv=? from c) #u (k-convert-at x t c))
                       (k-te (k-ty-new (ty-subr fe ps res c)) (extract r 2))))
              (else y (k-fail (string-append "`convention` takes a procedure, and this is a " (k-show-ty t)) a b)))))
        (x-plambda (bs body a b)
          (let ((r (k-synth body)))
            (if (k-generalizable? body (extract r 2))
                (k-te (k-ty-new (ty-poly bs (extract r 1))) (extract r 2))
                (k-fail (string-append "a `plambda` body must be pure, and this one has " (k-show-effect (extract r 2))) a b))))
        (x-rlambda (r l a b) (k-synth-rlambda x r l -1))
        (x-proj (body ds a b)
          (let* ((r (k-synth body)) (t (extract r 1)))
            (tagcase (k-get t)
              (ty-poly (bs inner)
                (if (not (= (k-length bs) (k-length ds)))
                    (k-fail (k-cat5 "this `poly` binds " (int->string (k-length bs)) " description(s); `proj` gave "
                                    (int->string (k-length ds)) "")
                            a b)
                    (let ((result (let ((m (k-proj-map bs ds a b)))
                                    (begin (k-check-bounds bs m a b) (k-check-finite-sizes bs m inner a b) (let ((inst (k-subst inner m))) (begin (k-no-knot inst a b) inst))))))
                      (k-te result (k-mask x (extract r 2) result)))))
              (else y (k-fail (string-append "`proj` needs a polymorphic value, not a " (k-show-ty t)) a b)))))
        (x-if (p c d a b)
          (let ((rp (k-synth p)))
            (if (not (k-subtype (extract rp 1) k-bool))
                (k-fail "an `if` test must be a bool" (k-start p) (k-end p))
                (let* ((cert (k-acyclic-test p))
                       (saved (get k-certified))
                       (pushed (set k-certified (if (null? cert) saved (the (listof (pairof symbol int @t) acyclic) (cons (car cert) saved)))))
                       (lens (k-length-test p))
                       (lsaved (get k-certified-lengths))
                       (lpushed (set k-certified-lengths (if (null? lens) lsaved (the (listof k-cert-len acyclic) (cons (car lens) lsaved)))))
                   (nats (k-nat-test p))
                   (nsaved (get k-certified-nats))
                   (npushed (set k-certified-nats (if (null? nats) nsaved (the (listof (pairof symbol int @t) acyclic) (cons (car nats) nsaved)))))
                       (facts (k-test-facts p))
                       (fsaved (get k-size-facts))
                       (fyes (set k-size-facts (k-with-fact (car facts) fsaved)))
                       (rc (k-synth c))
                       (fpopped (set k-size-facts fsaved))
                       (popped (set k-certified saved))
                       (lpopped (set k-certified-lengths lsaved)) (npopped (set k-certified-nats nsaved))
                       (fno (set k-size-facts (k-with-fact (cdr facts) fsaved)))
                       (rd (k-synth d))
                       (fdone (set k-size-facts fsaved)) (tc (extract rc 1)) (td (extract rd 1))
                       (t (cond ((k-subtype tc td) td)
                                ((k-subtype td tc) tc)
                                ;; Naturals of sizes not shown equal: a `nat`.
                                ((and (tagcase (k-get (k-resolve tc)) (ty-nat (z) #t) (else w #f))
                                      (tagcase (k-get (k-resolve td)) (ty-nat (z) #t) (else w #f)))
                                 (k-ty-new (ty-nat (sz-finite))))
                                (else (k-fail (k-cat4 "the branches are a " (k-show-ty tc) " and a " (k-show-ty td)) a b)))))
                  (k-te t (k-mask x (k-union (extract rp 2) (k-union (extract rc 2) (extract rd 2))) t))))))
        (x-letrec (bs body a b)
          (let ((saved (k-mark)) (rsaved (get k-recursive)))
            (begin
              (k-bind-letrec bs)
              ;; A group whose every run ends needs no `spin`.
              (k-letrec-lambdas bs)
              (let ((why (k-termination bs)))
                (begin (k-note-letrec bs (not (string=? why ""))) (if (string=? why "") #u (k-note-why bs why))))
              ;; The body's calls of the group are not recursion.
              (let* ((ie (k-check-letrec bs)) (restored (set k-recursive rsaved)) (rb (k-synth body)))
                (begin
                  (k-unbind-to saved)
                  (k-te (extract rb 1) (k-mask x (k-union ie (extract rb 2)) (extract rb 1))))))))
        (x-let (bs body a b)
          (let* ((inits (k-synth-lets bs)) (saved (k-mark)) (named (get k-skolems)))
            (begin
              (k-bind-named (extract inits 1))
              (k-note-let-lambdas bs)
              (let ((rb (k-synth body)))
                (begin
                  (k-unbind-to saved)
                  (let ((t (k-forget-nats named (extract rb 1) a b)))
                    (k-te t (k-mask x (k-union (extract inits 2) (extract rb 2)) t))))))))
        (x-prompt (t body h a b) (k-synth-prompt x t body h))
        ;; The region's name is a variable too, of type `(place r)`, when
        ;; the form makes a place.
        (x-letregion (k r i body a b)
          (let* ((saved (k-mark))
                 (bound (if (or (= k 0) (= k 3)) #u (k-bind (k-dvar-name r) (k-ty-new (ty-place (r-var r))))))
                 (freezing (get k-freezing))
                 (pushed (if (= k 3) (set k-freezing (cons r freezing)) #u))
                 (rb (k-synth body))
                 (written (k-has-id? (get k-written) r))
                 (popped (set k-freezing freezing)))
            (begin
              (k-unbind-to saved)
              (k-close-region x (cond ((= k 0) "letregion") ((= k 1) "letrena") ((= k 2) "letreap") (else "letfreeze"))
                              r (if (= k 3) (k-frozen-result r i written (extract rb 1) a b) (extract rb 1)) (extract rb 2) a b))))
        (x-bloblet (op i args a b) (k-synth-bloblet x op i args -1))
        (x-product (fs a b)
          (let* ((r (k-synth-fields fs)) (t (k-ty-new (ty-product (extract r 1)))))
            (k-te t (k-mask x (extract r 2) t))))
        (x-extract (e l a b)
          (let* ((r (k-synth e)) (pt (extract r 1)))
            (tagcase (k-get pt)
              (ty-product (fs)
                (let ((t (k-part-find fs l)))
                  (if (< t 0)
                      (k-fail (k-cat4 "a " (k-show-ty pt) " has no " (k-quote (symbol->string l))) a b)
                      (begin
                        (set k-extracts (cons (product (1 a) (2 b) (3 (k-part-index fs l 0))) (get k-extracts)))
                        (k-te t (k-mask x (extract r 2) t))))))
              (else y (k-fail (string-append "a product is expected here, and this is a " (k-show-ty pt)) (k-start e) (k-end e))))))
        (x-sum (l e a b)
          (let* ((r (k-synth e)) (t (k-ty-new (ty-sum (cons (product (1 l) (2 (extract r 1))) nil)))))
            (k-te t (k-mask x (extract r 2) t))))
        (x-tagcase (s arms els a b) (k-synth-tagcase x s arms els -1))
        (x-begin (xs a b)
          (let ((r (k-synth-seq xs k-unit nil)))
            (k-te (extract r 1) (k-mask x (extract r 2) (extract r 1))))))))
  (k-synth-seq (subr (maxeff checks spin) (kxs int k-eff) k-te)
    (lambda (xs last e)
      (if (null? xs) (k-te last e) (let ((r (k-synth (car xs)))) (k-synth-seq (cdr xs) (extract r 1) (k-union e (extract r 2)))))))
  (k-synth-fields (subr (maxeff checks spin) ((listof (productof (1 symbol) (2 kx)) acyclic)) (productof (1 k-parts) (2 k-eff)))
    (lambda (fs)
      (if (null? fs)
          (product (1 nil) (2 nil))
          (let* ((r (k-synth (extract (car fs) 2))) (rest (k-synth-fields (cdr fs))))
            (product (1 (cons (product (1 (extract (car fs) 1)) (2 (extract r 1))) (extract rest 1)))
                     (2 (k-union (extract r 2) (extract rest 2))))))))
  (k-synth-lets (subr (maxeff checks spin) ((listof (productof (1 symbol) (2 kx)) acyclic)) (productof (1 k-bindings) (2 k-eff)))
    (lambda (bs)
      (if (null? bs)
          (product (1 nil) (2 nil))
          (let* ((r (k-synth (extract (car bs) 2)))
                 (rest (k-synth-lets (cdr bs))))
            (product (1 (cons (cons (extract (car bs) 1) (extract r 1)) (extract rest 1)))
                     (2 (k-union (extract r 2) (extract rest 2))))))))
  (k-check-letrec (subr (maxeff checks spin) ((listof (productof (1 symbol) (2 int) (3 kx)) acyclic)) k-eff)
    (lambda (bs)
      (if (null? bs)
          nil
          (let* ((n (extract (car bs) 1)) (t (extract (car bs) 2)) (init (extract (car bs) 3))
                 ;; Only lambdas: then nothing runs before every binding
                 ;; exists, and no one sees the knot tied.
                 (e (if (k-lambda? init)
                        (k-check-declared n t init)
                        (k-fail (k-letrec-not-lambda n) (k-start init) (k-end init))))
                 (rest (k-check-letrec (cdr bs))))
            (k-union e rest)))))
  ;; Check `init` against `t`, the type `n` is declared; an error at `init`
  ;; itself says so.
  (k-check-declared (subr (maxeff checks spin) (symbol int kx) k-eff)
    (lambda (n t init)
      (extract (k-declaring (lambda () (k-te t (k-check init t))) (k-start init) (k-end init) n t) 2)))
  ;;; ------------------------------------------------------------ lambda

  ;; A `lambda`'s type. `hint` supplies the types of parameters the program
  ;; left out; `result`, when not -1, is what the body is checked against.
  (k-synth-lambda-as (subr (maxeff checks spin) (kx k-ids int) k-te)
    (lambda (x hint result)
      (tagcase x
        (x-lambda (ps body a b)
          (let* ((typed (k-param-types ps hint a b)) (saved (k-mark)) (named (get k-skolems)))
            (begin
              (k-bind-named typed)
              (let* ((r (if (>= result 0)
                            (let ((e (k-check body result))) (k-te result (k-mask body e result)))
                            (let ((r (k-synth body))) (k-te (extract r 1) (k-mask body (extract r 2) (extract r 1)))))))
                (begin
                  (k-unbind-to saved)
                  (set k-last-latent (extract r 2))
                  (k-te (k-ty-new (ty-subr (extract r 2) (k-binding-types typed) (k-forget-nats named (extract r 1) a b) (get k-conv-default))) nil))))))
        (else y (k-fail "a lambda" (k-start x) (k-end x))))))
  ;; An `rlambda`'s type: its `lambda`'s, told `expected`'s parameter and
  ;; result types if it is a subroutine's, with `(read R)` in its latent
  ;; effect, since calling it reads the closure; making it allocates in `R`,
  ;; the region `r` names.
  (k-synth-rlambda (subr (maxeff checks spin) (kx kx kx int) k-te)
    (lambda (x r l expected)
      (let* ((rr (k-synth r))
             (rt (extract rr 1))
             (g (tagcase (k-get rt)
                  (ty-place (g) g)
                  (else y (k-fail (k-cat3 "a region is expected here, and this is a " (k-show-ty rt) "") (k-start r) (k-end r)))))
             (c (if (< expected 0) (the (listof k-callable acyclic) nil) (k-as-subr expected)))
             (n (tagcase l (x-lambda (ps body a b) (k-length ps)) (else y 0)))
             (lt (cond
                   ((null? c) (k-synth-lambda-as l nil -1))
                   ((not (= (k-length (extract (car c) 2)) n))
                    (k-fail (k-cat4 "a subroutine of " (int->string (k-length (extract (car c) 2))) " parameter(s) is expected, and this `rlambda` has "
                                    (int->string n))
                            (k-start x) (k-end x)))
                   (else (k-synth-lambda-as l (extract (car c) 2) (extract (car c) 3)))))
             (t (tagcase (k-get (extract lt 1))
                  (ty-subr (e ps res cv) (k-ty-new (ty-subr (k-insert (a-read g) e) ps res cv)))
                  (else y (k-fail "a lambda" (k-start x) (k-end x)))))
             (e (k-insert (a-alloc g) (extract rr 2))))
        (k-te t (k-mask x e t)))))
  ;;; ------------------------------------------------------------ application
  (k-synth-app (subr (maxeff checks spin) (kx kx kxs int) k-te)
    (lambda (x f args expected)
      (let ((op (tagcase f
                  (x-var (op fa fb) (let ((t (k-lookup op))) (if (and (>= t 0) (k-named-has? (get k-std) op t)) (symbol->string op) "")))
                  (else y ""))))
        (cond ((string=? op "certify-acyclic") (k-certify x args))
              ((string=? op "certify-length") (k-certify-length x args))
              ((string=? op "certify-nat") (k-certify-nat x args))
              ((and (or (string=? op "+") (string=? op "-")) (not (null? args)) (not (null? (cdr args))) (null? (cdr (cdr args))))
               (k-nat-arith x op args))
              ((string=? op "cons")
               (let ((r (k-nlist-cons x args expected))) (if (null? r) (k-synth-app-plain x f args expected) (car r))))
              (else (k-synth-app-plain x f args expected))))))
  ;; `+` and `-` of naturals: a natural, of a size when both are known. Only
  ;; what has a type of its own is asked for it; anything else is told it
  ;; is an int, as for any call.
  (k-nat-arith (subr (maxeff checks spin) (kx string kxs) k-te)
    (lambda (x op args)
      (let* ((ra (k-nat-operand (car args)))
             (rb (k-nat-operand (car (cdr args))))
             (za (extract ra 2)) (zb (extract rb 2))
             (sz (if (or (null? za) (null? zb)) (the (listof k-size acyclic) nil) (k-nat-arith-size op (car za) (car zb)))))
        (k-te (if (null? sz) k-int (k-ty-new (ty-nat (car sz)))) (k-union (extract ra 1) (extract rb 1))))))
  (k-nat-operand (subr (maxeff checks spin) (kx) (productof (1 k-eff) (2 (listof k-size acyclic))))
    (lambda (x)
      (if (not (k-natural-by-itself? x))
          (product (1 (k-check x k-int)) (2 (the (listof k-size acyclic) nil)))
          (let* ((r (k-synth x)) (t (extract r 1)))
            (begin (k-expect x t k-int) (product (1 (extract r 2)) (2 (k-operand-size x t))))))))
  ;; `(certify-length v k)`: `v`'s value as a `(nlist T k)`, where `length-is?`
  ;; has just found it so; nowhere else.
  (k-certify-length (subr (maxeff checks spin) (kx kxs) k-te)
    (lambda (x args)
      (let* ((none (the (listof k-cert-len acyclic) nil))
             (found (if (and (not (null? args)) (not (null? (cdr args))) (null? (cdr (cdr args))))
                        (k-length-arg (car args) (car (cdr args)))
                        none))
             (ok (and (not (null? found)) (k-cert-len-has? (get k-certified-lengths) (car found)))))
        (if (not ok)
            (k-fail "`certify-length` takes only a variable and a length `length-is?` has just confirmed" (k-start x) (k-end x))
            (let* ((r (k-synth (car args))) (t (k-resolve (extract r 1))) (k (extract (car found) 3)))
              (tagcase (k-get t)
                (ty-pair (e tail rg)
                  (if (and (= (k-resolve tail) t) (tagcase rg (r-frozen (p f) #t) (else y #f)))
                      (k-te (k-ty-new (ty-nlist e k (k-fin-region rg))) (extract r 2))
                      (k-fail (k-cat3 "`certify-length` takes a frozen list, and this is a " (k-show-ty t) "") (k-start x) (k-end x))))
                (ty-nlist (e z rg) (k-te (k-ty-new (ty-nlist e k (k-fin-region rg))) (extract r 2)))
                (else y (k-fail (k-cat3 "`certify-length` takes a frozen list, and this is a " (k-show-ty t) "") (k-start x) (k-end x)))))))))
  ;; `cons` onto a `nlist`: one more element. Where a `nlist` is expected, the
  ;; tail is checked as one shorter; otherwise, a tail that is a variable of
  ;; `nlist` type gives a `nlist` one longer. None if neither.
  (k-nlist-cons (subr (maxeff checks spin) (kx kxs int) (listof k-te acyclic))
    (lambda (x args expected)
      (if (not (and (not (null? args)) (not (null? (cdr args))) (null? (cdr (cdr args)))))
          nil
          (let ((hd (car args)) (tl (car (cdr args))))
            (let ((want (if (< expected 0) (ty-void) (k-get expected))))
              (tagcase want
                (ty-nlist (e z r)
                  (if (not (or (tagcase z (sz-finite () #t) (else w #f)) (k-size-nonneg? (k-size-plus z -1))))
                      (k-nlist-cons-tail hd tl)
                      (let* ((tail-ty (k-ty-new (ty-nlist e (k-size-plus z -1) r)))
                             (xe (k-check hd e))
                             (te (k-check tl tail-ty)))
                        (the (listof k-te acyclic) (cons (k-te expected (k-union xe te)) nil)))))
                (else y (k-nlist-cons-tail hd tl))))))))
  (k-nlist-cons-tail (subr (maxeff checks spin) (kx kx) (listof k-te acyclic))
    (lambda (hd tl)
      (tagcase tl
        (x-var (v va vb)
          (let ((t (k-lookup v)))
            (if (< t 0)
                nil
                (tagcase (k-get t)
                  (ty-nlist (e z r)
                    (let* ((xe (k-check hd e)) (rt (k-synth tl)))
                      (the (listof k-te acyclic) (cons (k-te (k-ty-new (ty-nlist e (k-size-plus z 1) r)) (k-union xe (extract rt 2))) nil))))
                  (else y nil)))))
        (else y nil))))
  ;; `(certify-nat v)`: `v`'s value as a `nat`, where `nat?` has just found
  ;; `v` no less than 0; nowhere else.
  (k-certify-nat (subr (maxeff checks spin) (kx kxs) k-te)
    (lambda (x args)
      (let ((ok (and (k-sc-one-arg? args)
                     (tagcase (car args) (x-var (v va vb) (k-certified-has? (get k-certified-nats) v (k-binding-depth v))) (else y #f)))))
        (if (not ok)
            (k-fail "`certify-nat` takes only a variable `nat?` has just found no less than 0" (k-start x) (k-end x))
            (let ((r (k-synth (car args))))
              (begin (k-expect (car args) (extract r 1) k-int)
                     (k-te (k-ty-new (ty-nat (sz-finite))) (extract r 2))))))))
  ;; `(certify-acyclic v)`: `v`'s value at `acyclic`, where `acyclic?` has
  ;; just found `v` acyclic; nowhere else.
  (k-certify (subr (maxeff checks spin) (kx kxs) k-te)
    (lambda (x args)
      (let ((ok (and (k-sc-one-arg? args)
                     (tagcase (car args) (x-var (v va vb) (k-certified-has? (get k-certified) v (k-binding-depth v))) (else y #f)))))
        (if (not ok)
            (k-fail "`certify-acyclic` takes only a variable `acyclic?` has just found acyclic" (k-start x) (k-end x))
            (let* ((r (k-synth (car args))) (t (extract r 1)))
              (if (k-is-data? t)
                  (k-te (k-finitized t) (extract r 2))
                  (k-fail (k-cat3 "`certify-acyclic` takes data, and a " (k-show-ty t) " is not data") (k-start x) (k-end x))))))))
  (k-synth-app-plain (subr (maxeff checks spin) (kx kx kxs int) k-te)
    (lambda (x f args expected)
      (let* ((a (k-start x)) (b (k-end x))
             (rf (k-synth f))
             (n (k-length args))
             (done-t (the (arrayof int @t) (make-array n -1)))
             (done-e (the (arrayof k-eff @t) (make-array n nil)))
             (ft (tagcase (k-get (extract rf 1))
                   (ty-poly (bs body)
                     (let ((inst (k-instantiate (extract rf 1) args expected a b done-t done-e)))
                       (begin (k-no-knot inst a b) inst)))
                   (else y (extract rf 1))))
             (callee (k-as-subr ft)))
        (if (null? callee)
            (k-fail (string-append "not a subroutine: " (k-show-ty ft)) a b)
            (let ((params (extract (car callee) 2)))
              (if (not (= (k-length params) n))
                  (k-fail (k-cat4 "expected " (int->string (k-length params)) " argument(s), got " (int->string n)) a b)
                  (let* ((e (k-app-args args params 0 done-t done-e (extract rf 2)))
                         (e (k-union e (extract (car callee) 1)))
                         (e (if (k-may-spin? f ft args) (k-insert (a-spin) e) e))
                         (result (extract (car callee) 3)))
                    (k-te result (k-mask x e result)))))))))
  (k-app-args (subr (maxeff checks spin) (kxs k-ids int (arrayof int @t) (arrayof k-eff @t) k-eff) k-eff)
    (lambda (args params i done-t done-e e)
      (if (null? args)
          e
          (let* ((arg (car args)) (p (car params)) (t (array-ref done-t i))
                 (ae (if (>= t 0)
                         (if (k-subtype t p)
                             (array-ref done-e i)
                             (let ((c (k-conversion t p)))
                               (if (null? c)
                                   (k-fail (k-cat5 "argument " (int->string (+ i 1)) " is a " (k-show-ty t)
                                                   (k-cat3 ", where a " (k-show-ty p) " is expected"))
                                           (k-start arg) (k-end arg))
                                   (begin (k-convert-at arg t (car c)) (array-ref done-e i)))))
                         (k-check-argument arg p i))))
            (k-app-args (cdr args) (cdr params) (+ i 1) done-t done-e (k-union e ae))))))
  ;; An argument that failed to check is reported as that argument.
  (k-check-argument (subr (maxeff checks spin) (kx int int) k-eff)
    (lambda (arg p i)
      (extract (k-rewriting (lambda () (k-te p (k-check arg p))) (k-start arg) (k-end arg)
                            (lambda (m want got) (k-cat5 "argument " (int->string (+ i 1)) " is a " got
                                                         (k-cat3 ", where a " want " is expected"))))
               2)))
  (k-instantiate (subr (maxeff checks spin) (int kxs int int int (arrayof int @t) (arrayof k-eff @t)) int)
    (lambda (ft args expected a b done-t done-e)
      (let* ((bo (k-binders-of ft)) (kinds (extract bo 1)) (inner (extract bo 2)) (callee (k-as-subr inner)))
        (if (null? callee)
            (k-fail (string-append "not a subroutine, even once projected: " (k-show-ty ft)) a b)
            (let ((params (extract (car callee) 2)) (result (extract (car callee) 3)) (solved (the k-solved (new nil))))
              (if (not (= (k-length params) (k-length args)))
                  (k-fail (k-cat4 "expected " (int->string (k-length params)) " argument(s), got " (int->string (k-length args))) a b)
                  (begin
                    (if (>= expected 0) (k-unify result expected kinds solved (the k-trail (new nil))) #u)
                    (k-inst-asked args params 0 kinds solved done-t done-e)
                    (k-inst-told args params 0 kinds solved done-t done-e)
                    (k-inst-shapes args params 0 solved done-t)
                    (k-default-regions kinds solved)
                    (let ((m (k-finish kinds solved a b ft))) (begin (k-check-bounds kinds m a b) (k-check-finite-sizes kinds m inner a b) (k-subst inner m))))))))))
  ;; What the arguments are, except the ones that need to be told.
  (k-inst-asked (subr (maxeff checks spin) (kxs k-ids int k-binders k-solved (arrayof int @t) (arrayof k-eff @t)) unit)
    (lambda (args params i kinds solved done-t done-e)
      (if (null? args)
          #u
          (begin
            (if (k-needs-telling? (car args))
                #u
                (let ((p (k-subst (car params) (get solved))))
                  (if (not (k-mentions-any-unknown? p kinds solved))
                      (let ((e (k-check (car args) p))) (begin (array-set! done-t i p) (array-set! done-e i e)))
                      (let ((r (k-synth (car args))))
                        (tagcase (k-get (extract r 1))
                          (ty-poly (bs body) #u)
                          (else y
                            (begin (k-unify (car params) (extract r 1) kinds solved (the k-trail (new nil)))
                                   (array-set! done-t i (extract r 1))
                                   (array-set! done-e i (extract r 2)))))))))
            (k-inst-asked (cdr args) (cdr params) (+ i 1) kinds solved done-t done-e)))))
  ;; The arguments that needed telling: each is checked against its parameter
  ;; as solved so far, and what it turns out to be solves more.
  (k-inst-told (subr (maxeff checks spin) (kxs k-ids int k-binders k-solved (arrayof int @t) (arrayof k-eff @t)) unit)
    (lambda (args params i kinds solved done-t done-e)
      (if (null? args)
          #u
          (begin
            (if (>= (array-ref done-t i) 0)
                #u
                (let* ((arg (car args))
                       (defaulted (k-default-regions kinds solved))
                       (p (k-subst (car params) (get solved))))
                 (letrec ((not-known (subr (maxeff (read @globals) checks spin) (int) void)
                         (lambda (t)
                           (k-fail (k-cat5 "argument " (int->string (+ i 1)) " must be a " (k-show-ty t)
                                           ", which is not yet known here; give the other arguments first, or `proj` the operator")
                                   (k-start arg) (k-end arg)))))
                  (cond
                    ;; A thunk has no parameters to be told: told nothing, it
                    ;; says what it is, as any argument does.
                    ((and (k-needs-telling? arg) (null? (k-as-subr p)) (tagcase arg (x-lambda (ps body a b) (null? ps)) (else y #f)))
                     (let ((r (k-synth arg)))
                       (begin (k-unify (car params) (extract r 1) kinds solved (the k-trail (new nil)))
                              (array-set! done-t i (extract r 1))
                              (array-set! done-e i (extract r 2)))))
                    ((k-needs-telling? arg)
                     (let ((c (k-as-subr p)))
                       (if (or (null? c) (k-any-unknown-type? (extract (car c) 2) kinds solved))
                           (not-known p)
                           (let* ((res (extract (car c) 3))
                                  (r (k-synth-lambda-as arg (extract (car c) 2)
                                                        (if (k-mentions-unknown-type? res kinds solved) -1 res))))
                             (begin (k-unify (car params) (extract r 1) kinds solved (the k-trail (new nil)))
                                    (array-set! done-t i (extract r 1))
                                    (array-set! done-e i (extract r 2)))))))
                    ((k-mentions-unknown-type? p kinds solved) (not-known p))
                    (else (let ((e (k-check arg p))) (begin (array-set! done-t i p) (array-set! done-e i e))))))))
            (k-inst-told (cdr args) (cdr params) (+ i 1) kinds solved done-t done-e)))))
  ;;; ------------------------------------------------------------ check mode
  (k-check (subr (maxeff checks spin) (kx int) k-eff)
    (lambda (x expected)
      (let ((e (k-frozen x (k-check-mode x expected))))
        (begin (k-note-effect x e) e))))
  (k-check-mode (subr (maxeff checks spin) (kx int) k-eff)
    (lambda (x expected)
      (let* ((et (k-get expected))
             (poly? (tagcase et (ty-poly (bs body) #t) (else y #f)))
             (plambda? (tagcase x (x-plambda (bs body a b) #t) (else y #f))))
        (cond
          ((and poly? (not plambda?))
           (tagcase et
             (ty-poly (bs body)
               (let ((e (k-check x body)))
                 (if (k-generalizable? x e) e (k-fail (string-append "a polymorphic value must be pure, and this has " (k-show-effect e)) (k-start x) (k-end x)))))
             (else y nil)))
          ((and poly? plambda? (k-plambda-matches? x et))
           (tagcase x
             (x-plambda (binders body a b)
               (tagcase et
                 (ty-poly (bs want)
                   (let* ((want (k-subst want (k-rename bs binders))) (e (k-check body want)))
                     (if (k-generalizable? body e) e (k-fail (string-append "a `plambda` body must be pure, and this one has " (k-show-effect e)) a b))))
                 (else y nil)))
             (else y nil)))
          (else (k-check-node x expected et))))))
  (k-check-node (subr (maxeff checks spin) (kx int k-ty) k-eff)
    (lambda (x expected et)
      (letrec ((otherwise (subr (maxeff (read @globals) checks spin) () k-eff)
                           (lambda () (let ((r (k-synth x))) (begin (k-expect x (extract r 1) expected) (extract r 2))))))
       (the k-eff (let ((a (k-start x)) (b (k-end x)))
        (tagcase x
          (x-lambda (ps body xa xb)
            (let ((c (k-as-subr expected)))
              (cond
                ((not (null? c))
                 (let ((want (extract (car c) 2)))
                   (if (not (= (k-length want) (k-length ps)))
                       (k-fail (k-cat4 "a subroutine of " (int->string (k-length want)) " parameter(s) is expected, and this `lambda` has "
                                       (int->string (k-length ps)))
                               a b)
                       (let ((r (k-synth-lambda-as x want (extract (car c) 3))))
                         (begin (k-expect x (extract r 1) expected) (extract r 2))))))
                ((k-some-untyped? ps) (k-fail (string-append "a `lambda` cannot be a " (k-show-ty expected)) a b))
                (else (otherwise)))))
          (x-rlambda (r l xa xb)
            (if (null? (k-as-subr expected))
                (otherwise)
                (let ((rr (k-synth-rlambda x r l expected))) (begin (k-expect x (extract rr 1) expected) (extract rr 2)))))
          (x-app (f args xa xb)
            (let ((r (k-synth-app x f args expected))) (begin (k-expect x (extract r 1) expected) (extract r 2))))
          (x-bloblet (op i args xa xb)
            (let ((r (k-synth-bloblet x op i args expected))) (begin (k-expect x (extract r 1) expected) (extract r 2))))
          (x-tagcase (s arms els xa xb) (extract (k-synth-tagcase x s arms els expected) 2))
          (x-product (fs xa xb)
            (tagcase et
              (ty-product (want)
                (if (k-same-labels? fs want)
                    (k-mask x (k-check-fields fs want) expected)
                    (otherwise)))
              (else y (otherwise))))
          (x-sum (l e xa xb)
            (tagcase et
              (ty-sum (vs)
                (let ((t (k-part-find vs l)))
                  (if (>= t 0) (k-mask x (k-check e t) expected) (otherwise))))
              (else y (otherwise))))
          ;; A natural literal is a `nat`, and a `(nat k)`.
          (x-const (ty k xa xb)
            (if (and (= ty k-int) (>= k 0) (tagcase et (ty-nat (z) (k-size-le? (k-size-lit k) z)) (else w #f)))
                nil
                (otherwise)))
          (x-var (s xa xb)
            (let ((t (k-lookup s)))
              (cond
               ;; `nil` is a `nlist` of no elements, or of some.
               ((and (string=? (symbol->string s) "nil") (>= t 0) (k-named-has? (get k-std) s t)
                     (tagcase et (ty-nlist (e z r) (or (tagcase z (sz-finite () #t) (else w #f)) (k-size-eq? z (k-size-lit 0)))) (else w #f)))
                nil)
               ((and (>= t 0) (tagcase (k-get t) (ty-poly (bs body) #t) (else y #f)))
                (let ((inst (k-instantiate-against t expected a b)))
                  (begin (k-expect x inst expected) (k-naming-effect s t))))
               (else (otherwise)))))
          (x-if (p c d xa xb)
            (let* ((pe (k-check p k-bool))
                   (cert (k-acyclic-test p))
                   (saved (get k-certified))
                   (pushed (set k-certified (if (null? cert) saved (the (listof (pairof symbol int @t) acyclic) (cons (car cert) saved)))))
                   (lens (k-length-test p))
                   (lsaved (get k-certified-lengths))
                   (lpushed (set k-certified-lengths (if (null? lens) lsaved (the (listof k-cert-len acyclic) (cons (car lens) lsaved)))))
                   (nats (k-nat-test p))
                   (nsaved (get k-certified-nats))
                   (npushed (set k-certified-nats (if (null? nats) nsaved (the (listof (pairof symbol int @t) acyclic) (cons (car nats) nsaved)))))
                   (facts (k-test-facts p))
                   (fsaved (get k-size-facts))
                   (fyes (set k-size-facts (k-with-fact (car facts) fsaved)))
                   (ce (k-check c expected))
                   (fpopped (set k-size-facts fsaved))
                   (popped (set k-certified saved))
                   (lpopped (set k-certified-lengths lsaved)) (npopped (set k-certified-nats nsaved))
                   (fno (set k-size-facts (k-with-fact (cdr facts) fsaved)))
                   (de (k-check d expected))
                   (fdone (set k-size-facts fsaved)))
              (k-mask x (k-union pe (k-union ce de)) expected)))
          (x-begin (xs xa xb)
            (let ((e (k-check-seq xs expected nil)))
              (k-mask x e expected)))
          (x-let (bs body xa xb)
            (let* ((inits (k-synth-lets bs)) (saved (k-mark)) (named (get k-skolems)))
              (begin
                (k-bind-named (extract inits 1))
                (k-note-let-lambdas bs)
                (let ((e (k-check body expected)))
                  (begin (k-unbind-to saved) (set k-skolems named) (k-mask x (k-union (extract inits 2) e) expected))))))
          (else y (otherwise))))))))
  (k-check-seq (subr (maxeff checks spin) (kxs int k-eff) k-eff)
    (lambda (xs expected e)
      (if (null? (cdr xs))
          (k-union e (k-check (car xs) expected))
          (let ((r (k-synth (car xs)))) (k-check-seq (cdr xs) expected (k-union e (extract r 2)))))))
  (k-check-fields (subr (maxeff checks spin) ((listof (productof (1 symbol) (2 kx)) acyclic) k-parts) k-eff)
    (lambda (fs ps)
      (if (null? fs)
          nil
          (let* ((e (k-check (extract (car fs) 2) (extract (car ps) 2))) (rest (k-check-fields (cdr fs) (cdr ps))))
            (k-union e rest)))))
  (k-synth-tagcase (subr (maxeff checks spin) (kx kx k-arms (listof (productof (1 symbol) (2 kx)) acyclic) int) k-te)
    (lambda (x s arms els expected)
      (let* ((rs (k-synth s)) (st (extract rs 1)))
        (tagcase (k-get st)
          (ty-sum (variants)
            (let* ((arm-results (k-tagcase-arms arms variants st expected))
                   (rest (k-variants-not-named variants arms))
                   (e (k-union (extract rs 2) (extract arm-results 2)))
                   (both
                    (if (null? els)
                        (if (null? rest)
                            (product (1 (extract arm-results 1)) (2 e))
                            (k-fail (string-append "this `tagcase` has no arm for " (k-join (k-part-names rest) ", ")) (k-start x) (k-end x)))
                        (let* ((y (extract (car els) 1)) (body (extract (car els) 2))
                               (rest-ty (k-ty-new (ty-sum rest)))
                               (r (k-in-scope-check y rest-ty body expected)))
                          (product (1 (k-push-ids (extract arm-results 1) (cons (extract r 1) nil))) (2 (k-union e (extract r 2)))))))
                   (types (extract both 1))
                   (t (if (>= expected 0)
                          expected
                          (let ((found (k-upper-bound types types)))
                            (if (< found 0)
                                (k-fail (string-append "the arms are " (k-join (k-show-list types nil) ", ")) (k-start x) (k-end x))
                                found)))))
              (k-te t (k-mask x (extract both 2) t))))
          (else y (k-fail (string-append "a sum is expected here, and this is a " (k-show-ty st)) (k-start s) (k-end s)))))))
  ;; Each arm: its type and the effects of all.
  (k-tagcase-arms (subr (maxeff checks spin) (k-arms k-parts int int) (productof (1 k-ids) (2 k-eff)))
    (lambda (arms variants st expected)
      (if (null? arms)
          (product (1 nil) (2 nil))
          (let* ((arm (car arms)) (tag (extract arm 1)) (body (extract arm 4)) (t (k-part-find variants tag)))
            (if (< t 0)
                (k-fail (k-cat4 "a " (k-show-ty st) " has no tag " (k-quote (symbol->string tag))) (k-start body) (k-end body))
                (let* ((bound (if (extract arm 2)
                                  (tagcase (k-get t)
                                    (ty-product (fs)
                                      (if (= (k-length fs) (k-length (extract arm 3)))
                                          (k-zip-fields (extract arm 3) fs)
                                          (k-cannot-take-apart tag t (extract arm 3) body)))
                                    (else y (k-cannot-take-apart tag t (extract arm 3) body)))
                                  (the k-bindings (cons (cons (car (extract arm 3)) t) nil))))
                       (saved (k-mark))
                       (r (begin
                            (k-bind-all bound)
                            (if (>= expected 0) (k-te expected (k-check body expected)) (k-synth body))))
                       (restored (k-unbind-to saved))
                       (rest (k-tagcase-arms (cdr arms) variants st expected)))
                  (product (1 (cons (extract r 1) (extract rest 1))) (2 (k-union (extract r 2) (extract rest 2))))))))))
  (k-in-scope-check (subr (maxeff checks spin) (symbol int kx int) k-te)
    (lambda (y t body expected)
      (let ((saved (k-mark)))
        (begin
          (k-bind y t)
          (let ((r (if (>= expected 0) (k-te expected (k-check body expected)) (k-synth body))))
            (begin (k-unbind-to saved) r))))))
  ;;; ------------------------------------------------------------ bloblets
  (k-synth-bloblet (subr (maxeff checks spin) (kx symbol int kxs int) k-te)
    (lambda (x op i args expected)
      (let ((name (symbol->string op)) (a (k-start x)) (b (k-end x)))
        (if (or (string=? name "make-bloblet") (string=? name "rmake-bloblet"))
            ;; `rmake-bloblet`'s region is its first operand's; `make-bloblet`'s
            ;; the type it is checked against, or a fresh one.
            (let* ((rm (string=? name "rmake-bloblet"))
                   (gr (if rm (k-synth (car args)) (k-te k-unit (the k-eff nil))))
                   (given (the (listof k-region acyclic)
                            (if rm
                                (tagcase (k-get (extract gr 1))
                                  (ty-place (r) (cons r nil))
                                  (else y (k-fail (k-cat3 "a region is expected here, and this is a " (k-show-ty (extract gr 1)) "") a b)))
                                nil)))
                   (args (if rm (cdr args) args))
                   (e (k-union (extract gr 2) (k-check (car args) k-int)))
                   (fields (cdr args))
                   (want (the (listof k-ty acyclic)
                           (if (< expected 0)
                               nil
                               (tagcase (k-get expected)
                                 (ty-bloblet (fs z r)
                                   (if (and (not z) (= (k-length fs) (k-length fields)) (or (null? given) (k-region=? r (car given))))
                                       (cons (k-get expected) nil)
                                       nil))
                                 (else y nil)))))
                   (made (if (null? want)
                             (let ((r (k-synth-each fields)))
                               (product (1 (extract r 1)) (2 (extract r 2))
                                        (3 (if (null? given) (k-fresh-region "bloblet") (car given)))))
                             (tagcase (car want)
                               (ty-bloblet (fs z r) (product (1 fs) (2 (k-check-each fields fs)) (3 r)))
                               (else y (k-fail "a bloblet" a b)))))
                   (region (extract made 3))
                   (e (k-insert (a-alloc region) (k-union e (extract made 2))))
                   (t (k-ty-new (ty-bloblet (extract made 1) #f region)))
                   (unknotted (k-no-knot t a b)))
              (k-te t (k-mask x e t)))
            (let* ((bx (car args)) (rest (cdr args)) (rb (k-synth bx)) (bt (extract rb 1)))
              (tagcase (k-get bt)
                (ty-bloblet (fields frozen region)
                  (letrec ((field (subr (maxeff (read @globals) checks spin) () int)
                                  (lambda ()
                                    (if (< i (k-length fields))
                                        (k-nth fields i)
                                        (k-fail (k-cat5 "a " (k-show-ty bt) " has no field " (int->string i)
                                                        (string-append ": its fields are 0 to " (int->string (- (k-length fields) 1))))
                                                a b)))))
                  (let* ((e (extract rb 2))
                         (te
                          (cond
                            ((string=? name "bloblet-ref")
                             (let ((t (field))) (k-te t (if frozen e (k-insert (a-read region) e)))))
                            ((string=? name "bloblet-set!")
                             (let ((t (field)))
                               (if frozen
                                   (k-fail (k-cat3 "a " (k-show-ty bt) " cannot be changed: its fields are frozen") a b)
                                   (k-te k-unit (k-insert (a-write region) (k-union e (k-check (car rest) t)))))))
                            ((string=? name "bloblet-freeze")
                             (k-te (k-ty-new (ty-bloblet fields #t region)) (k-insert (a-write region) e)))
                            ((string=? name "bloblet-byte")
                             (k-te k-int (k-insert (a-read region) (k-union e (k-check (car rest) k-int)))))
                            ((string=? name "bloblet-set-byte!")
                             (let* ((e1 (k-check (car rest) k-int)) (e2 (k-check (car (cdr rest)) k-int)))
                               (k-te k-unit (k-insert (a-write region) (k-union e (k-union e1 e2))))))
                            (else (k-te k-int e)))))
                    (k-te (extract te 1) (k-mask x (extract te 2) (extract te 1))))))
                (else y (k-fail (string-append "a bloblet is expected here, and this is a " (k-show-ty bt)) (k-start bx) (k-end bx)))))))))
  (k-synth-each (subr (maxeff checks spin) (kxs) (productof (1 k-ids) (2 k-eff)))
    (lambda (xs)
      (if (null? xs)
          (product (1 nil) (2 nil))
          (let* ((r (k-synth (car xs))) (rest (k-synth-each (cdr xs))))
            (product (1 (cons (extract r 1) (extract rest 1))) (2 (k-union (extract r 2) (extract rest 2))))))))
  (k-check-each (subr (maxeff checks spin) (kxs k-ids) k-eff)
    (lambda (xs ts)
      (if (null? xs) nil (let* ((e (k-check (car xs) (car ts))) (rest (k-check-each (cdr xs) (cdr ts)))) (k-union e rest)))))
  ;;; ------------------------------------------------------------ prompts
  ;;; The tag's type fixes what crosses the prompt, and the body's effect must
  ;;; be within the tag's bound apart from control on its region. Then the
  ;;; prompt delimits: that control is removed, if the body can reach no other
  ;;; tag in the region.
  (k-synth-prompt (subr (maxeff checks spin) (kx kx kx kx) k-te)
    (lambda (x tag body handler)
      (let* ((rt (k-synth tag)) (tt (extract rt 1)))
        (tagcase (k-get tt)
          (ty-tag (answer payload bound region)
            (let* ((be (extract (k-rewriting (lambda () (k-te answer (k-check body answer))) (k-start body) (k-end body)
                                             (lambda (m want got) (k-cat4 "the tag's prompts deliver a " want ", and this body is a " got)))
                                2))
                   (own (k-insert (a-goto region) (k-one (a-comefrom region))))
                   (beyond (k-beyond be bound own)))
              (if (not (null? beyond))
                  (k-fail (k-cat4 "the tag allows its delimited computations " (k-show-effect bound) ", and this body also has " (k-show-effect beyond))
                          (k-start body) (k-end body))
                  (let* ((rh (k-synth-handler handler payload answer))
                         (ht (extract rh 1))
                         (c (k-as-subr ht)))
                    (if (null? c)
                        (k-fail (string-append "a handler is a subroutine, not a " (k-show-ty ht)) (k-start handler) (k-end handler))
                        (let ((ps (extract (car c) 2)))
                          (if (or (not (= (k-length ps) 1)) (not (k-subtype payload (car ps))) (not (k-subtype (extract (car c) 3) answer)))
                              (k-fail (k-cat5 (k-cat3 "the handler must take a " (k-show-ty payload) " to a ") (k-show-ty answer) "; it is a " (k-show-ty ht) "")
                                      (k-start handler) (k-end handler))
                              (let* ((delimited (if (k-reaches-only? body tag region) (k-beyond be nil own) be))
                                     (e (k-union (extract rt 2) (k-union (extract rh 2) (k-union (extract (car c) 1) delimited)))))
                                (k-te answer (k-mask x e answer))))))))))
          (else y (k-fail (string-append "a prompt needs a prompt tag, not a " (k-show-ty tt)) (k-start tag) (k-end tag)))))))
  ;; A handler written as a `lambda` of one parameter is told what it takes
  ;; and gives.
  (k-synth-handler (subr (maxeff checks spin) (kx int int) k-te)
    (lambda (h payload answer)
      (tagcase h
        (x-lambda (ps hbody a b)
          (if (= (k-length ps) 1)
              (k-rewriting (lambda () (k-synth-lambda-as h (cons payload nil) answer)) (k-start hbody) (k-end hbody)
                           (lambda (m want got)
                             (k-cat5 (k-cat3 "the handler must take a " (k-show-ty payload) " to a ") (k-show-ty answer) ", and this gives a " got "")))
              (k-synth h)))
        (else y (k-synth h))))))

;;; ------------------------------------------------------------ programs

;; The initial environment: `(name type)` for each binding.
(define k-standard (subr (maxeff checks spin) ((listof syn acyclic)) unit)
  (lambda (entries)
    (if (null? entries)
        #u
        (let* ((pair (k-items (car entries) "a standard binding"))
               (t (k-parse-type (k-nth pair 1))))
          (let ((n (k-name-of (car pair) "a name")))
            (begin (k-bind n t) (set k-std (cons (cons n t) (get k-std))) (k-standard (cdr entries))))))))

(define-type k-out (listof string acyclic))
(define k-push-binders (subr kstate (k-binders) unit)
  (lambda (bs)
    (if (null? bs)
        #u
        (let ((v (extract (car bs) 1)))
          (begin (k-push-desc (k-dvar-name v) (ds-var v (extract (car bs) 2))) (k-push-binders (cdr bs)))))))

;; Put the binders of every `poly` at the top of `t` in scope for reading.
(define k-bind-signature (subr (maxeff kstate spin) (int) unit)
  (lambda (t)
    (tagcase (k-get t)
      (ty-poly (bs body) (begin (k-push-binders bs) (k-bind-signature body)))
      (else y #u))))

(define k-private (subr checks (syns-a) unit)
  (lambda (rs)
    (if (null? rs)
        #u
        (let ((name (k-name-of (car rs) "expected a name")))
          (if (not (k-at-name? (symbol->string name)))
              (k-sfail "a region constant is written `@name`" (car rs))
              (begin (k-push-desc name (ds-private (k-fresh-region (symbol->string name)))) (k-private (cdr rs))))))))

;; `define-type`, `define-effect` and `private-regions`.
;;; ------------------------------------------------------------ proofs
;;; A definition whose declared type is `(proves …)` is a lemma once its
;;; body is a guarded structural identity (`src/lemma.rs`): it takes apart
;;; only what it was given, rebuilds the same tags and labels, applies
;;; hypotheses and proofs only to what was given at the same place, and uses
;;; itself only under a constructor.

;; A place in what a proof was given: a variable and the labels extracted.
(define-type k-pos (pairof symbol (listof symbol acyclic) @t))
(define k-syms=? (subr (read @globals) ((listof symbol acyclic) (listof symbol acyclic)) bool)
  (lambda (xs ys) (if (null? xs) (null? ys) (and (not (null? ys)) (symbol=? (car xs) (car ys)) (k-syms=? (cdr xs) (cdr ys))))))
(define k-append-sym (subr (maxeff (read @globals) (alloc @t)) ((listof symbol acyclic) symbol) (listof symbol acyclic))
  (lambda (xs l) (if (null? xs) (the (listof symbol acyclic) (cons l nil)) (the (listof symbol acyclic) (cons (car xs) (k-append-sym (cdr xs) l))))))
;; Whether `f` names a generative type's conversion.
(define k-names-conversion? (subr (maxeff (read @globals) (read @t) (alloc @t) spin) (kx) bool)
  (lambda (f)
    (tagcase (k-under f)
      (x-var (s a b) (let ((t (k-lookup s))) (and (>= t 0) (k-named-has? (get k-conversions) s t))))
      (else y #f))))
;; `e` under ascriptions and conversions, which are the identity.
(define k-strip-conv (subr (maxeff (read @globals) (read @t) (alloc @t) spin) (kx) kx)
  (lambda (e)
    (tagcase e
      (x-the (t x a b) (k-strip-conv x))
      (x-app (f args a b) (if (and (k-sc-one? args) (k-names-conversion? f)) (k-strip-conv (car args)) e))
      (else y e))))
;; The place `e` names, if it names one (none or one).
(define k-place-of (subr (maxeff (read @globals) (read @t) (alloc @t) spin) (kx) (listof k-pos acyclic))
  (lambda (e)
    (tagcase (k-strip-conv e)
      (x-var (s a b) (the (listof k-pos acyclic) (cons (cons s nil) nil)))
      (x-extract (x l a b)
        (let ((p (k-place-of x))) (if (null? p) nil (the (listof k-pos acyclic) (cons (cons (car (car p)) (k-append-sym (cdr (car p)) l)) nil)))))
      (else y nil))))
(define k-at? (subr (maxeff (read @globals) (read @t) (alloc @t) spin) (kx k-pos) bool)
  (lambda (e at)
    (let ((p (k-place-of e))) (and (not (null? p)) (symbol=? (car (car p)) (car at)) (k-syms=? (cdr (car p)) (cdr at))))))
;; `t` with generative types unfolded, as far as they go.
(define k-unfold-all (subr (maxeff kstate spin) (int int) int)
  (lambda (t n)
    (if (= n 0)
        t
        (let ((t (k-resolve t))) (tagcase (k-get t) (ty-named (g ds) (k-unfold-all (k-unfold g ds) (- n 1))) (else y t))))))
(define k-proof-fail (subr checks (kx string string) void)
  (lambda (e want why) (k-fail (k-cat4 "this does not prove " want ": " why) (k-start e) (k-end e))))
(define k-lemma-name? (subr (maxeff (read @globals) (read @t) spin) ((listof k-lemma acyclic) symbol int) bool)
  (lambda (ls s t) (and (not (null? ls)) (or (k-named-has? (extract (car ls) 5) s t) (k-lemma-name? (cdr ls) s t)))))
(define k-names-meet? (subr (maxeff (read @globals) (read @t)) (k-names k-names) bool)
  (lambda (xs ys) (and (not (null? xs)) (or (k-has-name? ys (car xs)) (k-names-meet? (cdr xs) ys)))))
(define k-last (subr (maxeff (read @globals) (read @t)) (kxs) kx) (lambda (xs) (if (null? (cdr xs)) (car xs) (k-last (cdr xs)))))
(define k-but-last (subr (maxeff (read @globals) (read @t) (alloc @t)) (kxs) kxs)
  (lambda (xs) (if (null? (cdr xs)) nil (the kxs (cons (car xs) (k-but-last (cdr xs)))))))
(define-rec
  ;; Whether `e0` rebuilds, as the identity, what was given at `at`, of type
  ;; `ty`; `guarded` once something has been rebuilt above it.
  (k-rebuild (subr (maxeff checks spin) (kx k-pos int bool symbol k-names string) unit)
    (lambda (e0 at ty guarded me hyps want)
      (let ((e (k-strip-conv e0)))
        (if (k-at? e at)
            #u
            (tagcase e
              (x-app (f args a b)
                (let ((op (tagcase (k-under f) (x-var (s fa fb) (the k-names (cons s nil))) (else y (the k-names nil)))))
                  (if (null? op)
                      (k-proof-fail e want "a proof may call only its hypotheses, itself, or another proof")
                      (let ((f (car op)))
                        (if (k-has-name? hyps f)
                            (if (and (k-sc-one? args) (k-at? (car args) at))
                                #u
                                (k-proof-fail e want "a hypothesis applies only to what was given here"))
                            (let* ((me? (symbol=? f me))
                                   (t (k-lookup f))
                                   (lemma? (and (>= t 0) (k-lemma-name? (get k-lemmas) f t))))
                              (cond ((and (not me?) (not lemma?))
                                     (k-proof-fail e want "a proof may call only its hypotheses, itself, or another proof"))
                                    ((and me? (not guarded))
                                     (k-proof-fail e want "it uses itself before rebuilding anything, which proves nothing"))
                                    ((null? args) (k-proof-fail e want "a proof applies to something"))
                                    (else
                                     (let ((last (k-last args)))
                                       (if (k-at? last at)
                                           (k-proof-coercions (k-but-last args) guarded me hyps want)
                                           (k-proof-fail last want "a proof applies only to what was given here")))))))))))
              (x-tagcase (sc arms els a b)
                (if (not (k-at? sc at))
                    (k-proof-fail sc want "a proof takes apart only what was given here")
                    (tagcase (k-get (k-unfold-all ty 64))
                      (ty-sum (vs)
                        (begin
                          (k-rebuild-arms arms vs at me hyps want)
                          (if (null? els)
                              #u
                              (let ((y (extract (car els) 1)) (body (extract (car els) 2)))
                                (if (or (symbol=? y me) (k-has-name? hyps y))
                                    (k-proof-fail body want "a proof may not rebind the names it relies on")
                                    (k-rebuild body (cons y nil) ty guarded me hyps want))))))
                      (else z (k-proof-fail sc want "what is given here is not a sum")))))
              (x-product (gs a b)
                (tagcase (k-get (k-unfold-all ty 64))
                  (ty-product (fs)
                    (if (k-same-labels? gs fs)
                        (k-rebuild-paths gs fs at me hyps want)
                        (k-proof-fail e want "a product is rebuilt with its fields, in order")))
                  (else z (k-proof-fail e want "what is given here is not a product"))))
              (else y (k-proof-fail e want "a proof may only take apart and rebuild what it was given")))))))
  (k-rebuild-arms (subr (maxeff checks spin) (k-arms k-parts k-pos symbol k-names string) unit)
    (lambda (arms vs at me hyps want)
      (if (null? arms)
          #u
          (let* ((arm (car arms)) (tag (extract arm 1)) (fields? (extract arm 2)) (names (extract arm 3)) (body0 (extract arm 4)))
            (begin
              (if (or (k-has-name? names (car at)) (k-has-name? names me) (k-names-meet? names hyps))
                  (k-proof-fail body0 want "a proof may not rebind the names it relies on")
                  #u)
              (let ((vt (k-part-find vs tag)))
                (if (< vt 0)
                    (k-proof-fail body0 want "an arm for a tag that is not there")
                    (let ((body (k-strip-conv body0)))
                      (tagcase body
                        (x-sum (t2 inner sa sb)
                          (if (not (symbol=? t2 tag))
                              (k-proof-fail body0 want "each arm rebuilds its own tag")
                              (if fields?
                                  (tagcase (k-get (k-unfold-all vt 64))
                                    (ty-product (fs)
                                      (let ((inner (k-strip-conv inner)))
                                        (tagcase inner
                                          (x-product (gs pa pb)
                                            (if (and (= (k-length gs) (k-length fs)) (= (k-length names) (k-length fs)) (k-same-labels? gs fs))
                                                (k-rebuild-fields gs fs names me hyps want)
                                                (k-proof-fail inner want "each arm rebuilds its fields, in order")))
                                          (else z (k-proof-fail inner want "each arm rebuilds its fields")))))
                                    (else z (k-proof-fail body0 want "fields of something that is not a product")))
                                  (k-rebuild inner (cons (car names) nil) vt #t me hyps want))))
                        (else z (k-proof-fail body0 want "each arm rebuilds its own tag"))))))
              (k-rebuild-arms (cdr arms) vs at me hyps want))))))
  (k-rebuild-fields (subr (maxeff checks spin) ((listof (productof (1 symbol) (2 kx)) acyclic) k-parts k-names symbol k-names string) unit)
    (lambda (gs fs xs me hyps want)
      (if (null? gs)
          #u
          (begin (k-rebuild (extract (car gs) 2) (cons (car xs) nil) (extract (car fs) 2) #t me hyps want)
                 (k-rebuild-fields (cdr gs) (cdr fs) (cdr xs) me hyps want)))))
  (k-rebuild-paths (subr (maxeff checks spin) ((listof (productof (1 symbol) (2 kx)) acyclic) k-parts k-pos symbol k-names string) unit)
    (lambda (gs fs at me hyps want)
      (if (null? gs)
          #u
          (begin (k-rebuild (extract (car gs) 2) (cons (car at) (k-append-sym (cdr at) (extract (car gs) 1))) (extract (car fs) 2) #t me hyps want)
                 (k-rebuild-paths (cdr gs) (cdr fs) at me hyps want)))))
  ;; A coercion a proof passes to a proof: a hypothesis, a proof, itself
  ;; (under a constructor), or a lambda whose parameter is annotated and
  ;; whose body rebuilds it.
  (k-proof-coercion (subr (maxeff checks spin) (kx bool symbol k-names string) unit)
    (lambda (c0 guarded me hyps want)
      (let ((c (k-strip-conv c0)))
        (tagcase c
          (x-var (s a b)
            (cond ((k-has-name? hyps s) #u)
                  ((symbol=? s me) (if guarded #u (k-proof-fail c want "it passes itself on before rebuilding anything")))
                  ((let ((t (k-lookup s))) (and (>= t 0) (k-lemma-name? (get k-lemmas) s t))) #u)
                  (else (k-proof-fail c want "a proof is given only hypotheses, proofs, or coercions that rebuild"))))
          (x-lambda (ps body a b)
            (if (and (not (null? ps)) (null? (cdr ps)) (not (null? (extract (car ps) 2))))
                (let ((x (extract (car ps) 1)))
                  (if (or (symbol=? x me) (k-has-name? hyps x))
                      (k-proof-fail c want "a proof may not rebind the names it relies on")
                      (k-rebuild body (cons x nil) (car (extract (car ps) 2)) guarded me hyps want)))
                (k-proof-fail c want "a coercion given to a proof takes one parameter, with its type written")))
          (else y (k-proof-fail c want "a proof is given only hypotheses, proofs, or coercions that rebuild"))))))
  (k-proof-coercions (subr (maxeff checks spin) (kxs bool symbol k-names string) unit)
    (lambda (cs guarded me hyps want)
      (if (null? cs) #u (begin (k-proof-coercion (car cs) guarded me hyps want) (k-proof-coercions (cdr cs) guarded me hyps want))))))
(define k-under-abstractions (subr (maxeff (read @globals) spin) (kx) kx)
  (lambda (x) (tagcase x (x-plambda (bs body a b) (k-under-abstractions body)) (x-the (t body a b) (k-under-abstractions body)) (else y x))))
(define k-param-names-first (subr (maxeff (read @globals) (read @t) (alloc @t)) ((listof (productof (1 symbol) (2 k-ids)) acyclic) int) k-names)
  (lambda (ps n) (if (= n 0) nil (the k-names (cons (extract (car ps) 1) (k-param-names-first (cdr ps) (- n 1)))))))

;; Whether `e`, the body of `name`, proves lemma `l`; an error where not.
(define k-check-proof (subr (maxeff checks spin) (k-lemma symbol kx) unit)
  (lambda (l name e)
    (let* ((want (k-cat5 "`" (k-show-ty (extract l 2)) " ≤ " (k-show-ty (extract l 3)) "`"))
           (x (k-under-abstractions e)))
      (tagcase x
        (x-lambda (ps body a b)
          (let ((n (k-length (extract l 4))))
            (if (not (= (k-length ps) (+ n 1)))
                (k-fail (k-cat3 "a proof of " want " takes a coercion for each hypothesis, then what it proves of") a b)
                (k-rebuild body (cons (extract (k-nth ps n) 1) nil) (extract l 2) #f name (k-param-names-first ps n) want))))
        (else y (k-fail (k-cat3 "a proof of " want " is a lambda") (k-start e) (k-end e)))))))
;; The generative type `name` may see inside, as one of its conversions, or
;; -1; no longer, once asked.
(define k-take-inside (subr kstate (symbol) int)
  (lambda (name)
    (letrec ((find (subr (maxeff (read @globals) (read @t)) ((listof (pairof symbol int @t) acyclic)) int)
                   (lambda (xs) (cond ((null? xs) -1) ((symbol=? (car (car xs)) name) (cdr (car xs))) (else (find (cdr xs))))))
             (drop (subr (maxeff (read @globals) (read @t) (alloc @t)) ((listof (pairof symbol int @t) acyclic)) (listof (pairof symbol int @t) acyclic))
                   (lambda (xs)
                     (cond ((null? xs) xs)
                           ((symbol=? (car (car xs)) name) (cdr xs))
                           (else (the (listof (pairof symbol int @t) acyclic) (cons (car xs) (drop (cdr xs)))))))))
      (let ((g (find (get k-inside))))
        (begin (if (>= g 0) (set k-inside (drop (get k-inside))) #u) g)))))
(define k-declare (subr (maxeff checks spin) (top) unit)
  (lambda (form)
    (tagcase form
      (t-define-type (name def a b)
        (if (syn-symbol? name)
            (begin (k-define-type (k-name-of name "expected a name") def a b) #u)
            (let ((items (k-items name "a type definition")))
              (if (null? items)
                  (k-sfail "expected a name" name)
                  (k-define-family (k-name-of (car items) "expected a name") (cdr items) def)))))
      (t-define-effect (name def a b)
        (let* ((n (k-name-of name "expected a name")) (e (k-parse-effect def))) (k-push-desc n (ds-eff e))))
      (t-private-regions (rs a b) (k-private rs))
      (t-define-generative (head rep a b)
        (let* ((name (k-define-generative head rep)) (g (- (get k-ngens) 1)) (n (symbol->string name)))
          ;; Only its own conversions, which follow, see inside it.
          (set k-inside (cons (cons (string->symbol (string-append "down-" n)) g)
                              (cons (cons (string->symbol (string-append "up-" n)) g) (get k-inside))))))
      (else y #u))))

;; The first pass: abbreviations, so that types can refer to each other in
;; any order. Values cannot: a definition sees only those before it.
(define k-ahead (subr (maxeff checks spin) ((listof top acyclic)) unit)
  (lambda (forms)
    (if (null? forms)
        #u
        (begin (k-declare (car forms)) (k-ahead (cdr forms))))))

(define k-line (subr (maxeff (read @globals) (read @t) (alloc @t) spin) (int k-eff) string)
  (lambda (t e) (k-cat3 (k-show-ty t) " ! " (k-show-effect e))))
(define k-push-lines (subr (maxeff (read @globals) (read @t) (alloc @t)) ((listof string acyclic) k-out) k-out)
  (lambda (lines out) (if (null? lines) out (k-push-lines (cdr lines) (cons (car lines) out)))))
(define k-rec-types (subr (maxeff checks spin) ((listof (productof (1 symbol) (2 syn) (3 exp)) acyclic)) k-ids)
  (lambda (bs)
    (if (null? bs)
        nil
        (let* ((t (k-parse-type (extract (car bs) 2))) (bound (k-bind-global (extract (car bs) 1) t))
               (noted (k-note-known (extract (car bs) 1) 0)))
          (cons t (k-rec-types (cdr bs)))))))
;; Each lambda, read under its signature: a lambda, or an error.
(define k-rec-lambdas (subr (maxeff checks spin) ((listof (productof (1 symbol) (2 syn) (3 exp)) acyclic) k-ids) k-group)
  (lambda (bs ts)
    (if (null? bs)
        nil
        (let* ((name (extract (car bs) 1))
               (t (car ts))
               (saved (get k-dscope))
               (signed (k-bind-signature t))
               (x (k-resolve-exp (extract (car bs) 3)))
               (restored (set k-dscope saved))
               (checked (if (k-lambda? x) #u (k-fail (k-letrec-not-lambda name) (k-start x) (k-end x)))))
          (cons (product (1 name) (2 t) (3 x)) (k-rec-lambdas (cdr bs) (cdr ts)))))))
(define k-rec-check (subr (maxeff checks spin) (k-group) (listof string acyclic))
  (lambda (g)
    (if (null? g)
        nil
        (let* ((name (extract (car g) 1))
               (t (extract (car g) 2))
               (e (k-check-declared name t (extract (car g) 3)))
               (line (k-cat4 "define " (symbol->string name) " : " (k-line t e)))
               (rest (k-rec-check (cdr g))))
          (cons line rest)))))

;; A `define-rec` group's free variables.
(define k-group-free (subr (maxeff (read @globals) (read @t) (alloc @t)) (k-group k-names) k-names)
  (lambda (g out) (if (null? g) out (k-group-free (cdr g) (k-free-into (extract (car g) 3) nil out)))))
;; `(define-rec (name type lambda) …)`: every name in scope first, then each
;; lambda checked against its type. A line for each.
(define k-define-rec (subr (maxeff checks spin) ((listof (productof (1 symbol) (2 syn) (3 exp)) acyclic)) (listof string acyclic))
  (lambda (bs)
    (let* ((rsaved (get k-recursive))
           (g (k-rec-lambdas bs (k-rec-types bs)))
           (u (set k-last-uses (k-group-free g nil)))
           ;; A group whose every run ends needs no `spin`.
           (why (k-termination g))
           (noted (if (string=? why "") #u (begin (k-note-recursive g) (k-note-why g why))))
           (lines (k-rec-check g)))
      (begin (set k-recursive rsaved) lines))))

;;; Redefinition (`top.rs`, `Checker::top_defining`), for files and the REPL
;;; alike: a global's uses always refer to what it is now. A definition of a
;;; name already a global, at a type every use can take (each a subtype of
;;; the old), assigns the global. At any other type it makes a new global,
;;; and every earlier definition that uses the name (and every one that uses
;;; those) is checked again, in order: each that checks is defined again,
;;; by the same rule; each that does not is broken. To keep a value as it
;;; was, a program binds it: `(define d (let ((g g)) …))`.

(define k-rev-runs (subr (read @globals) ((listof k-run acyclic) (listof k-run acyclic)) (listof k-run acyclic))
  (lambda (xs acc) (if (null? xs) acc (k-rev-runs (cdr xs) (the (listof k-run acyclic) (cons (car xs) acc))))))
;; For a driver: what the program checked runs, in order (`compile-checked`,
;; `run-checked`).
(define checked-tops (subr (maxeff (read @globals) (read @t)) () (listof k-run acyclic))
  (lambda () (k-rev-runs (get k-runs) nil)))
(define k-rev-defs (subr (read @globals) ((listof k-def acyclic) (listof k-def acyclic)) (listof k-def acyclic))
  (lambda (xs acc) (if (null? xs) acc (k-rev-defs (cdr xs) (the (listof k-def acyclic) (cons (car xs) acc))))))
(define k-rec-names (subr (read @globals) ((listof (productof (1 symbol) (2 syn) (3 exp)) acyclic)) k-names)
  (lambda (bs) (if (null? bs) nil (the k-names (cons (extract (car bs) 1) (k-rec-names (cdr bs)))))))
;; The names a form defines.
(define k-top-names (subr (read @globals) (top) k-names)
  (lambda (form)
    (tagcase form
      (t-define (name ty init a b) (the k-names (cons name nil)))
      (t-define-rec (bs a b) (k-rec-names bs))
      (else y (the k-names nil)))))
;; Whether `n` is a global a definition made.
(define k-defined? (subr (maxeff (read @globals) (read @t)) (symbol) bool)
  (lambda (n)
    (letrec ((go (subr (maxeff (read @globals) (read @t)) ((listof k-def acyclic)) bool)
               (lambda (ds) (and (not (null? ds)) (or (k-has-name? (extract (car ds) 1) n) (go (cdr ds)))))))
      (go (get k-defs)))))
;; The names of `ns` that are globals already, with their types.
(define-type k-olds (listof (pairof symbol int acyclic) acyclic))
(define k-old-types (subr (maxeff (read @globals) (read @t) spin) (k-names) k-olds)
  (lambda (ns)
    (cond ((null? ns) nil)
          ((k-defined? (car ns)) (the k-olds (cons (cons (car ns) (k-lookup-raw (car ns))) (k-old-types (cdr ns)))))
          (else (k-old-types (cdr ns))))))
;; Whether each of them now has a type its old one's uses can take.
(define k-fits-old? (subr (maxeff kstate spin) (k-olds) bool)
  (lambda (os) (or (null? os) (and (k-subtype (k-lookup-raw (car (car os))) (cdr (car os))) (k-fits-old? (cdr os))))))
(define k-names-without (subr (maxeff (read @globals) (read @t)) (k-names k-names) k-names)
  (lambda (xs ns)
    (cond ((null? xs) xs)
          ((k-has-name? ns (car xs)) (k-names-without (cdr xs) ns))
          (else (the k-names (cons (car xs) (k-names-without (cdr xs) ns)))))))
(define k-defs-without (subr (maxeff (read @globals) (read @t)) ((listof k-def acyclic) k-names) (listof k-def acyclic))
  (lambda (ds ns)
    (cond ((null? ds) ds)
          ((k-names-meet? (extract (car ds) 1) ns) (k-defs-without (cdr ds) ns))
          (else (the (listof k-def acyclic) (cons (car ds) (k-defs-without (cdr ds) ns)))))))
;; `form`, which defines `ns`, recorded as their definition now.
(define k-record (subr kstate (top k-names) unit)
  (lambda (form ns)
    (if (null? ns)
        #u
        (set k-defs (the (listof k-def acyclic)
                      (cons (product (1 ns) (2 form) (3 (k-names-without (get k-last-uses) ns))) (k-defs-without (get k-defs) ns)))))))
;; The definitions that use `ns`, and those that use them, and so on,
;; oldest first.
(define k-users-of (subr (maxeff (read @globals) (read @t) (alloc @t)) (k-names) (listof k-def acyclic))
  (lambda (ns)
    (letrec ((go (subr (maxeff (read @globals) (read @t) (alloc @t)) ((listof k-def acyclic) k-names) (listof k-def acyclic))
               (lambda (ds used)
                 (cond ((null? ds) nil)
                       ((k-names-meet? (extract (car ds) 1) ns) (go (cdr ds) used))
                       ((k-names-meet? (extract (car ds) 3) used)
                        (the (listof k-def acyclic) (cons (car ds) (go (cdr ds) (k-names-onto (extract (car ds) 1) used)))))
                       (else (go (cdr ds) used))))))
      (go (k-rev-defs (get k-defs) nil) ns))))
;; Names as a message shows them: `a`, `b`.
(define k-shown (subr (maxeff (read @globals) (read @t) (alloc @t)) (k-names) string)
  (lambda (ns)
    (letrec ((go (subr (maxeff (read @globals) (alloc @t)) (k-names) (listof string acyclic))
               (lambda (xs) (if (null? xs) nil (the (listof string acyclic) (cons (k-cat3 "`" (symbol->string (car xs)) "`") (go (cdr xs))))))))
      (k-join (go ns) ", "))))
(define k-break-all (subr (maxeff kstate spin) (k-names string) unit)
  (lambda (ns why)
    (if (null? ns)
        #u
        (begin (set k-broken (the (listof k-break acyclic) (cons (product (1 (car ns)) (2 (k-name-depth (car ns))) (3 why)) (get k-broken))))
               (k-break-all (cdr ns) why)))))
(define k-lines-append (subr (read @globals) ((listof string acyclic) (listof string acyclic)) (listof string acyclic))
  (lambda (xs ys) (if (null? xs) ys (the (listof string acyclic) (cons (car xs) (k-lines-append (cdr xs) ys))))))
;; `t`, a `subr` under any `poly`s, with `extra` in its latent effect; -1 if
;; `t` is not one.
(define k-with-latent (subr (maxeff kstate spin) (int k-eff) int)
  (lambda (t extra)
    (tagcase (k-get (k-resolve t))
      (ty-poly (bs body) (let ((b (k-with-latent body extra))) (if (< b 0) -1 (k-ty-new (ty-poly bs b)))))
      (ty-subr (e ps r cv) (k-ty-new (ty-subr (k-union e extra) ps r cv)))
      (else y -1))))
;; The atoms of `e` on globals.
(define k-globals-of (subr (maxeff (read @globals) (read @t) (alloc @t)) (k-eff) k-eff)
  (lambda (e) (cond ((null? e) nil) ((k-globals-atom? (car e)) (the k-eff (cons (car e) (k-globals-of (cdr e))))) (else (k-globals-of (cdr e))))))
;; `n`'s innermost binding, now of type `t`.
(define k-rebind-top (subr (maxeff kstate spin) (symbol int) unit)
  (lambda (n t) (table-set! (get k-env) n (cons t (cdr (table-ref (get k-env) n nil))))))
;; `f`'s value, or, if it fails, the error `say` makes of its message.
(define k-saying (subr (maxeff (read @globals) checks spin) ((subr (maxeff checks spin) () k-te) (subr (maxeff checks spin) (string) string)) k-te)
  (lambda (f say)
    (let ((r (prompt k-tag (k-done (f)) (lambda (r) r))))
      (tagcase r
        (k-done (te) te)
        (k-err (m ea eb) (k-fail (say m) ea eb))
        (k-ok (xs) (k-fail "k-ok inside" 0 0))))))
;; `(define name type init)`, or, if `star` is not empty,
;; `(define* name type init)`: its line.
(define k-define-typed (subr (maxeff checks spin) (symbol syn (listof syn acyclic) exp) (listof string acyclic))
  (lambda (name written star-syns init)
    ;; A lambda is in scope in itself, as a `letrec`
    ;; binding is; anything else is not.
    (let* ((reset (set k-pending-lemma nil))
           (t (k-parse-type written))
           ;; `define*`: checked as though its type read
           ;; `@globals`, which finds what it reads.
           (star (not (null? star-syns)))
           (tw (if star (k-with-latent t (k-one (a-read (r-globals)))) t))
           (subr-ok (if (< tw 0) (k-sfail "`define*` finds what a procedure reads: its type is a `subr`" written) #u))
           ;; A `proves` type: a lemma, once the body proves it.
           (lemma (get k-pending-lemma))
           (taken (set k-pending-lemma nil))
           (saved (get k-dscope))
           (signed (k-bind-signature t))
           (x (k-resolve-exp init))
           (lambda-ok (if (and star (not (k-lambda? x))) (k-fail "`define*` defines a procedure: a `lambda`" (k-start x) (k-end x)) #u))
           (u (set k-last-uses (k-free-into x nil nil)))
           (restored (set k-dscope saved))
           (bound (if (k-lambda? x) (k-bind-global name t) #u))
           (rsaved (get k-recursive))
           ;; A lambda whose every run ends needs no `spin`.
           (noted (if (k-lambda? x)
                      (begin (k-note-known name 0)
                             (let* ((g (the k-group (cons (product (1 name) (2 tw) (3 x)) nil)))
                                    (why (k-termination g)))
                               (if (string=? why "")
                                   #u
                                   (begin (set k-recursive (cons (cons name tw) rsaved)) (k-note-why g why)))))
                      #u))
           ;; A generative type's own `up-` and `down-` see
           ;; inside it.
           (inside (k-take-inside name))
           (opened (if (>= inside 0) (set k-transparent (cons inside (get k-transparent))) #u))
           (e0 (k-check-declared name tw x))
           ;; With `define*`, the globals the lambda read,
           ;; found, are its type's; and it is checked again
           ;; at that type, bound to it: one that fails is
           ;; the checker's mistake, not the program's.
           (tf (if star (k-with-latent t (k-globals-of (get k-last-latent))) tw))
           (refound (if star
                        (begin
                          (k-rebind-top name tf)
                          (set k-recursive rsaved)
                          (let* ((g (the k-group (cons (product (1 name) (2 tf) (3 x)) nil)))
                                 (why (k-termination g)))
                            (if (string=? why "")
                                #u
                                (begin (set k-recursive (cons (cons name tf) rsaved)) (k-note-why g why)))))
                        #u))
           (e (if star
                  (extract (k-saying (lambda () (k-te tf (k-check-declared name tf x)))
                                     (lambda (m) (k-cat5 (k-cat3 "`define*` found `" (symbol->string name) "` to be a ")
                                                         (k-show-ty tf) ", and checked at it, it does not check (a mistake of the checker's): " m "")))
                           2)
                  e0))
           (closed (if (>= inside 0)
                       (begin (set k-transparent (cdr (get k-transparent)))
                              (set k-conversions (cons (cons name t) (get k-conversions))))
                       #u))
           (popped (set k-recursive rsaved))
           (proved (if (null? lemma)
                       #u
                       (let ((l (car lemma)))
                         (begin (k-check-proof l name x)
                                (set k-lemmas (cons (product (1 (extract l 1)) (2 (extract l 2)) (3 (extract l 3)) (4 (extract l 4))
                                                             (5 (the k-named (cons (cons name t) nil))))
                                                    (get k-lemmas)))))))
           (after (if (k-lambda? x) #u (k-bind-global name tf))))
      (cons (k-cat4 "define " (symbol->string name) " : " (k-line tf e)) nil))))
;; One top-level form's lines: what each definition and expression is.
(define k-top-lines (subr (maxeff checks spin) (top) (listof string acyclic))
  (lambda (form)
    (the (listof string acyclic) (tagcase form
                 (t-define (name ty init a b)
                   (if (null? ty)
                       (let* ((x (k-resolve-exp init)) (u (set k-last-uses (k-free-into x nil nil))) (r (k-synth x)))
                         (begin (k-bind-global name (extract r 1))
                                (if (k-lambda? x) (k-note-known name 0) #u)
                                (cons (k-cat4 "define " (symbol->string name) " : " (k-line (extract r 1) (extract r 2))) nil)))
                       (k-define-typed name (car ty) (cdr ty) init)))
                 (t-define-rec (bs a b) (k-define-rec bs))
                 (t-exp (e)
                   (let* ((x (k-resolve-exp e)) (r (k-synth x)))
                     (cons (k-line (extract r 1) (extract r 2)) nil)))
                 (else y nil)))))
(define k-lines-append-names (subr (read @globals) (k-names k-names) k-names)
  (lambda (xs ys) (if (null? xs) ys (the k-names (cons (car xs) (k-lines-append-names (cdr xs) ys))))))
;; The names `defs` define, in order.
(define k-defs-names (subr (maxeff (read @globals) (read @t) (alloc @t)) ((listof k-def acyclic)) k-names)
  (lambda (ds) (if (null? ds) nil (k-lines-append-names (extract (car ds) 1) (k-defs-names (cdr ds))))))
;; Those of `xs` that are in `ys`, in `xs`'s order.
(define k-names-within (subr (maxeff (read @globals) (read @t)) (k-names k-names) k-names)
  (lambda (xs ys)
    (cond ((null? xs) xs)
          ((k-has-name? ys (car xs)) (the k-names (cons (car xs) (k-names-within (cdr xs) ys))))
          (else (k-names-within (cdr xs) ys)))))
;; Whether `t` is a procedure whose calls may not end: `spin` in its latent
;; effect, under any `poly`.
(define k-type-spins? (subr (maxeff (read @globals) (read @t) spin) (int) bool)
  (lambda (t)
    (tagcase (k-get (k-resolve t))
      (ty-poly (bs body) (k-type-spins? body))
      (ty-subr (e ps r cv)
        (letrec ((go (subr (read @globals) (k-eff) bool) (lambda (e) (and (not (null? e)) (or (tagcase (car e) (a-spin () #t) (else y #f)) (go (cdr e)))))))
          (go e)))
      (else y #f))))
(define k-names-spin? (subr (maxeff (read @globals) (read @t) spin) (k-names) bool)
  (lambda (ns) (and (not (null? ns)) (or (k-type-spins? (k-lookup-raw (car ns))) (k-names-spin? (cdr ns))))))
(define k-top-start (subr pure (top) int)
  (lambda (form) (tagcase form (t-define (name ty init a b) a) (t-define-rec (bs a b) a) (else y 0))))
(define k-top-end (subr pure (top) int)
  (lambda (form) (tagcase form (t-define (name ty init a b) b) (t-define-rec (bs a b) b) (else y 0))))
(define k-atoms-globals (subr (maxeff (read @globals) (alloc @t)) (k-eff) k-regions)
  (lambda (e)
    (cond ((null? e) nil)
          ((k-globals-atom? (car e)) (the k-regions (cons (k-atom-region (car e)) (k-atoms-globals (cdr e)))))
          (else (k-atoms-globals (cdr e))))))
;; The globals calling a value of type `t` reads: its latent effect's, under
;; any `poly`; none, if it is not a procedure.
(define k-latent-globals (subr (maxeff (read @globals) (read @t) (alloc @t) spin) (int) k-regions)
  (lambda (t)
    (tagcase (k-get (k-resolve t))
      (ty-poly (bs body) (k-latent-globals body))
      (ty-subr (e ps r cv) (k-atoms-globals e))
      (else y nil))))
;; The first of `ns` whose global `rs` has, if any.
(define k-first-read (subr (maxeff (read @globals) (read @t) (alloc @t) spin) (k-regions k-names) k-names)
  (lambda (rs ns)
    (cond ((null? ns) nil)
          ((k-has-region-in? rs (r-global (car ns))) (the k-names (cons (car ns) nil)))
          (else (k-first-read rs (cdr ns))))))
;; Defining a global writes it: a procedure stored in global `f` whose calls
;; read `f` may reach itself through the global, which termination checking,
;; trusting every procedure of a type without `spin` to end, has not seen.
;; So it must say `spin`, as a procedure kept in a ref must, however it
;; reads `f`; one that stays `pure` binds itself with a local `letrec`. A
;; group's members read each other so. Reading `@globals` may read `f` only
;; once `f` is a global (`top.rs`, `no_reaching_itself`).
(define k-no-reaching-itself (subr (maxeff checks spin) (top k-names bool) unit)
  (lambda (form ns redefining)
    (letrec ((each (subr (maxeff checks spin) (k-names) unit)
               (lambda (ms)
                 (if (null? ms)
                     #u
                     (let* ((n (car ms)) (t (k-lookup-raw n)))
                       (if (k-type-spins? t)
                           (each (cdr ms))
                           (let* ((reads (k-latent-globals t))
                                  (m (k-first-read reads ns))
                                  (name (symbol->string n)))
                             (cond ((not (null? m))
                                    (k-fail (k-cat5 (k-cat5 "calling `" name "` reads `" (symbol->string (car m)) "`, so `")
                                                    name "` may reach itself through a global: its type must say `spin` (or, to call itself directly, it binds itself with a local `letrec`)" "" "")
                                            (k-top-start form) (k-top-end form)))
                                   ((and redefining (k-has-region-in? reads (r-globals)))
                                    (k-fail (k-cat5 (k-cat5 "calling `" name "` may read any global, `" name "` too, so `")
                                                    name "` may reach itself through a global: its type must say `spin`" "" "")
                                            (k-top-start form) (k-top-end form)))
                                   (else (each (cdr ms)))))))))))
      (each ns))))
;; Each of `users` checked again after the redefinition of `ns`: defined
;; again if it checks, broken if not.
(define k-rerun (subr (maxeff (read @globals) checks spin) ((listof k-def acyclic) k-names (listof string acyclic)) (listof string acyclic))
  (lambda (users ns lines)
    (if (null? users)
        lines
        (let* ((u (car users))
               (olds (k-old-types (extract u 1)))
               (m (k-mark))
               (reset (set k-last-uses nil))
               (r (prompt k-tag
                    (let ((ls (k-top-lines (extract u 2))))
                      (begin (k-no-reaching-itself (extract u 2) (extract u 1) #t) (k-ok ls)))
                    (lambda (r) r))))
          (tagcase r
            (k-ok (ls)
              (let* ((assigns (k-fits-old? olds))
                     (recorded (k-record (extract u 2) (extract u 1)))
                     (ran (set k-runs (the (listof k-run acyclic) (cons (product (1 (extract u 2)) (2 assigns)) (get k-runs))))))
                (k-rerun (cdr users) ns (k-lines-append lines ls))))
            (k-err (msg a b)
              (begin (k-unbind-to m)
                     (k-break-all (extract u 1) (k-cat5 "since " (k-shown ns) " was redefined (" msg ")"))
                     (k-rerun (cdr users) ns lines)))
            (else y (k-rerun (cdr users) ns lines)))))))
;; A top-level form, checked under redefinition: its lines, and those of
;; the definitions it has run again.
(define k-defining (subr (maxeff checks spin) (top) (listof string acyclic))
  (lambda (form)
    (let* ((ns (k-top-names form))
           (olds (k-old-types ns))
           (users (if (null? olds) (the (listof k-def acyclic) nil) (k-users-of ns)))
           (reset (set k-last-uses nil))
           (lines (k-top-lines form))
           (knot (k-no-reaching-itself form ns (not (null? olds))))
           (assigns (and (not (null? olds)) (k-fits-old? olds)))
           (recorded (k-record form ns))
           (ran (set k-runs (the (listof k-run acyclic) (cons (product (1 form) (2 assigns)) (get k-runs))))))
      (if (or (null? olds) assigns) lines (k-rerun users ns lines)))))


;; The second pass: definitions and expressions, in order, each under
;; redefinition (`k-defining`).
(define k-forms (subr (maxeff checks spin) ((listof top acyclic) k-out) k-out)
  (lambda (forms out)
    (if (null? forms)
        (reverse out)
        (k-forms (cdr forms) (k-push-lines (k-defining (car forms)) out)))))

;; The entry point: check a program's trees, in the initial environment
;; written `standard`. What each definition and expression is, in order,
;; or the first error.
(define check-program (subr (maxeff (read @globals) checks spin) ((listof syn acyclic) (listof top acyclic)) k-result)
  (lambda (standard forms)
    (prompt k-tag
      (begin (k-reset) (k-standard standard) (k-ahead forms) (k-ok (k-forms forms nil)))
      (lambda (r) r))))

;; The entry point for more of a program, form by form, as the REPL gives
;; them: checked in the environment the forms before left, which
;; `check-program` began. The facts for the compiler are only the new
;; forms', whose positions are in their own text.
(define check-more (subr (maxeff (read @globals) checks spin) ((listof top acyclic)) k-result)
  (lambda (forms)
    (prompt k-tag
      (begin (set k-extracts nil) (set k-effect-notes nil) (set k-runs nil) (k-ahead forms) (k-ok (k-forms forms nil)))
      (lambda (r) r))))
