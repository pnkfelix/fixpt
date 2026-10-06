;;; The checker, in FX-26: programs, form by form, and proofs.
;;; Part of the checker, `check-types.fx` first (PLAN.md §11, step 10).

;;; ------------------------------------------------------------ programs

;; Its types, at top level: declared ahead, named anywhere.
(define-type k-out (listof string acyclic))

;; A place in what a proof was given: a variable and the labels extracted.
(define-type k-pos (pairof symbol (listof symbol acyclic) @t))
;; What checking a proof relies on: its own name, the names of its
;; hypotheses, and what it proves, in words.
(define-type k-proving (productof (1 symbol) (2 k-names) (3 string)))
;; An arm of a `tagcase`: its tag, whether it takes the fields apart, the
;; names it binds, and its body.
(define-type k-case-arm (productof (1 symbol) (2 bool) (3 k-names) (4 kx)))
;; The top-level forms of a program.
(define-type k-tops (listof top acyclic))
;; A `define-rec`'s bindings: names, written types, and lambdas.
(define-type k-rec-forms (listof (productof (1 symbol) (2 syn) (3 exp)) acyclic))
(define-type k-run-list (listof k-run acyclic))
(define-type k-def-list (listof k-def acyclic))
;; The names of `ns` that are globals already, with their types.
(define-type k-olds (listof (pairof symbol int acyclic) acyclic))

;; A module (`TODO.md` §34: the front end into modules, a file at a time);
;; what other files use re-exported after it.
(define check-program-module (module
;; `n`, of type `t`, bound as a standard binding.
(define k-bind-std (subr (maxeff kstate spin) (symbol int) unit)
  (lambda (n t) (begin (k-bind n t) (set k-std (cons (cons n t) (get k-std))))))
;; The initial environment: `(name type)` for each binding.
(define k-standard (subr (maxeff checks spin) (syns-a) unit)
  (lambda (entries)
    (if (null? entries)
        #u
        (let ((pair (k-items (car entries) "a standard binding")))
          ;; `vsubr`'s declaration first: generative type 0, as in the Rust
          ;; checker (`check::VSUBR`), with no `up-` or `down-`.
          (if (and (syn-symbol? (car pair)) (string=? (syn-name (car pair)) "define-generative"))
              (begin (k-define-generative (k-nth pair 1) (k-nth pair 2)) (k-standard (cdr entries)))
              (let ((t (k-parse-type (k-nth pair 1))) (n (k-name-of (car pair) "a name")))
                (begin (k-bind-std n t) (k-standard (cdr entries)))))))))

;; Put the binders of every `poly` at the top of `t` in scope for reading.
(define k-bind-signature (subr (maxeff kstate spin) (int) unit)
  (lambda (t)
    (tagcase (k-get t)
      (ty-poly (bs body) (begin (k-push-binders bs) (k-bind-signature body)))
      (else y #u))))

;; The region `private-regions` makes `name` stand for: the one it stands
;; for already, if an earlier `private-regions` made it the program's own
;; (a file loaded again is the same program, over the same regions);
;; otherwise a fresh one.
(define k-private-region (subr kstate (symbol) k-region)
  (lambda (name)
    (let ((d (k-lookup-desc name)))
      (if (null? d)
          (k-fresh-region (symbol->string name))
          (tagcase (car d)
            (ds-private (r) r)
            (else x (k-fresh-region (symbol->string name))))))))
(define k-private (subr checks (syns-a) unit)
  (lambda (rs)
    (if (null? rs)
        #u
        (let ((name (k-name-of (car rs) "expected a name")))
          (if (not (k-at-name? (symbol->string name)))
              (k-sfail "a region constant is written `@name`" (car rs))
              (begin (k-push-desc name (ds-private (k-private-region name)))
                     (k-private (cdr rs))))))))

;; `define-type`, `define-effect` and `private-regions`.
;;; ------------------------------------------------------------ proofs
;;; A definition whose declared type is `(proves …)` is a lemma once its
;;; body is a guarded structural identity (`src/lemma.rs`): it takes apart
;;; only what it was given, rebuilds the same tags and labels, applies
;;; hypotheses and proofs only to what was given at the same place, and uses
;;; itself only under a constructor.

(define k-syms=? (subr (read @globals) ((listof symbol acyclic) (listof symbol acyclic)) bool)
  (lambda (xs ys)
    (if (null? xs)
        (null? ys)
        (and (not (null? ys)) (symbol=? (car xs) (car ys)) (k-syms=? (cdr xs) (cdr ys))))))
(define k-append-sym (subr (maxeff (read @globals) (alloc @t)) (k-names symbol) k-names)
  (lambda (xs l)
    (if (null? xs)
        (the k-names (cons l nil))
        (the k-names (cons (car xs) (k-append-sym (cdr xs) l))))))
;; The place of field `l` of what is at `p`.
(define k-pos-field (subr (maxeff kreads (alloc @t)) (k-pos symbol) k-pos)
  (lambda (p l) (cons (car p) (k-append-sym (cdr p) l))))
;; Whether `p` and `q` are the same place.
(define k-pos=? (subr kreads (k-pos k-pos) bool)
  (lambda (p q) (and (symbol=? (car p) (car q)) (k-syms=? (cdr p) (cdr q)))))
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
      (x-app (f args a b)
        (if (and (k-sc-one? args) (k-names-conversion? f)) (k-strip-conv (car args)) e))
      (else y e))))
;; The place `e` names, if it names one (none or one).
(define k-place-of (subr (maxeff kreads (alloc @t) spin) (kx) (listof k-pos acyclic))
  (lambda (e)
    (tagcase (k-strip-conv e)
      (x-var (s a b) (the (listof k-pos acyclic) (cons (cons s nil) nil)))
      (x-extract (x l a b)
        (let ((p (k-place-of x)))
          (if (null? p) nil (the (listof k-pos acyclic) (cons (k-pos-field (car p) l) nil)))))
      (else y nil))))
(define k-at? (subr (maxeff (read @globals) (read @t) (alloc @t) spin) (kx k-pos) bool)
  (lambda (e at)
    (let ((p (k-place-of e))) (and (not (null? p)) (k-pos=? (car p) at)))))
;; `t` with generative types unfolded, as far as they go.
(define k-unfold-all (subr (maxeff kstate spin) (int int) int)
  (lambda (t n)
    (if (= n 0)
        t
        (let ((t (k-resolve t)))
          (tagcase (k-get t)
            (ty-named (g ds) (k-unfold-all (k-unfold g ds) (- n 1)))
            (else y t))))))
;; The error that `e` does not prove what `pv` is to, and why.
(define k-proof-fail (subr checks (kx k-proving string) void)
  (lambda (e pv why) (k-fail-at (k-cat4 "this does not prove " (extract pv 3) ": " why) e)))
;; Why a proof may not call, or be given, what it is.
(define k-proof-calls string "a proof may call only its hypotheses, itself, or another proof")
(define k-proof-given string "a proof is given only hypotheses, proofs, or coercions that rebuild")
(define k-lemma-name? (subr (maxeff kreads spin) ((listof k-lemma acyclic) symbol int) bool)
  (lambda (ls s t)
    (and (not (null? ls))
         (or (k-named-has? (extract (car ls) 5) s t) (k-lemma-name? (cdr ls) s t)))))
;; Whether `s` names a proof.
(define k-lemma-named? (subr (maxeff kreads spin) (symbol) bool)
  (lambda (s) (let ((t (k-lookup s))) (and (>= t 0) (k-lemma-name? (get k-lemmas) s t)))))
(define k-names-meet? (subr (maxeff (read @globals) (read @t)) (k-names k-names) bool)
  (lambda (xs ys)
    (and (not (null? xs)) (or (k-has-name? ys (car xs)) (k-names-meet? (cdr xs) ys)))))
;; Whether `y` is a name the proof relies on: its own, or a hypothesis's.
(define k-relied-on? (subr kreads (k-proving symbol) bool)
  (lambda (pv y) (or (symbol=? y (extract pv 1)) (k-has-name? (extract pv 2) y))))
;; Whether `names`, bound by an arm, rebind what the proof relies on: what
;; was given at `at`, its own name, or a hypothesis's.
(define k-rebinds? (subr kreads (k-names k-pos k-proving) bool)
  (lambda (names at pv)
    (or (k-has-name? names (car at))
        (k-has-name? names (extract pv 1))
        (k-names-meet? names (extract pv 2)))))
;; Whether fields `gs` rebuild `fs`, which `names` name: as many, with the
;; same labels, in order.
(define k-fields-fit? (subr kreads (k-let-bs k-parts k-names) bool)
  (lambda (gs fs names)
    (and (= (k-length gs) (k-length fs))
         (= (k-length names) (k-length fs))
         (k-same-labels? gs fs))))
(define k-last (subr kreads (kxs) kx)
  (lambda (xs) (if (null? (cdr xs)) (car xs) (k-last (cdr xs)))))
(define k-but-last (subr (maxeff (read @globals) (read @t) (alloc @t)) (kxs) kxs)
  (lambda (xs) (if (null? (cdr xs)) nil (the kxs (cons (car xs) (k-but-last (cdr xs)))))))
(define-rec
  ;; Whether `e0` rebuilds, as the identity, what was given at `at`, of type
  ;; `ty`; `guarded` once something has been rebuilt above it.
  (k-rebuild (subr (maxeff checks spin) (kx k-pos int bool k-proving) unit)
    (lambda (e0 at ty guarded pv)
      (let ((e (k-strip-conv e0)))
        (if (k-at? e at) #u (k-rebuild-node e at ty guarded pv)))))
  ;; `e`, not what was given at `at` itself: a call, or what takes that
  ;; apart or rebuilds it.
  (k-rebuild-node (subr (maxeff checks spin) (kx k-pos int bool k-proving) unit)
    (lambda (e at ty guarded pv)
      (tagcase e
        (x-app (f args a b) (k-rebuild-call e f args at guarded pv))
        (x-tagcase (sc arms els a b)
          (if (not (k-at? sc at))
              (k-proof-fail sc pv "a proof takes apart only what was given here")
              (tagcase (k-get (k-unfold-all ty 64))
                (ty-sum (vs)
                  (begin (k-rebuild-arms arms vs at pv) (k-rebuild-else els ty guarded pv)))
                (else z (k-proof-fail sc pv "what is given here is not a sum")))))
        (x-product (gs a b) (k-rebuild-product e gs at ty pv))
        (else y
          (k-proof-fail e pv "a proof may only take apart and rebuild what it was given")))))
  ;; A call `e`, of `f` on `args`: a hypothesis applied to what was given at
  ;; `at`, or a proof.
  (k-rebuild-call (subr (maxeff checks spin) (kx kx kxs k-pos bool k-proving) unit)
    (lambda (e f args at guarded pv)
      (let ((op (k-callee-name f)))
        (cond ((null? op) (k-proof-fail e pv k-proof-calls))
              ((k-has-name? (extract pv 2) (car op))
               (if (and (k-sc-one? args) (k-at? (car args) at))
                   #u
                   (k-proof-fail e pv "a hypothesis applies only to what was given here")))
              (else (k-rebuild-proof-call e (car op) args at guarded pv))))))
  ;; A call `e` of `f`, itself (once guarded) or another proof, on `args`:
  ;; applied to what was given at `at`, last, with coercions before it.
  (k-rebuild-proof-call (subr (maxeff checks spin) (kx symbol kxs k-pos bool k-proving) unit)
    (lambda (e f args at guarded pv)
      (let ((me? (symbol=? f (extract pv 1))) (lemma? (k-lemma-named? f)))
        (cond ((and (not me?) (not lemma?)) (k-proof-fail e pv k-proof-calls))
              ((and me? (not guarded))
               (k-proof-fail e pv (string-append "it uses itself before rebuilding anything, "
                                                 "which proves nothing")))
              ((null? args) (k-proof-fail e pv "a proof applies to something"))
              (else
               (let ((last (k-last args)))
                 (if (k-at? last at)
                     (k-proof-coercions (k-but-last args) guarded pv)
                     (k-proof-fail last pv "a proof applies only to what was given here"))))))))
  ;; A product `e` of fields `gs`, rebuilding what was given at `at`, of
  ;; type `ty`.
  (k-rebuild-product (subr (maxeff checks spin) (kx k-let-bs k-pos int k-proving) unit)
    (lambda (e gs at ty pv)
      (tagcase (k-get (k-unfold-all ty 64))
        (ty-product (fs)
          (if (k-same-labels? gs fs)
              (k-rebuild-paths gs fs at pv)
              (k-proof-fail e pv "a product is rebuilt with its fields, in order")))
        (else z (k-proof-fail e pv "what is given here is not a product")))))
  ;; A `tagcase`'s `else`, if it has one, rebuilding what it is given, of
  ;; type `ty`, under its own name.
  (k-rebuild-else (subr (maxeff checks spin) (k-let-bs int bool k-proving) unit)
    (lambda (els ty guarded pv)
      (if (null? els)
          #u
          (let ((y (extract (car els) 1)) (body (extract (car els) 2)))
            (if (k-relied-on? pv y)
                (k-proof-fail body pv "a proof may not rebind the names it relies on")
                (k-rebuild body (cons y nil) ty guarded pv))))))
  (k-rebuild-arms (subr (maxeff checks spin) (k-arms k-parts k-pos k-proving) unit)
    (lambda (arms vs at pv)
      (if (null? arms)
          #u
          (let ((arm (car arms)))
            (begin
              (if (k-rebinds? (extract arm 3) at pv)
                  (k-proof-fail (extract arm 4) pv "a proof may not rebind the names it relies on")
                  #u)
              (k-rebuild-arm arm vs pv)
              (k-rebuild-arms (cdr arms) vs at pv))))))
  ;; An arm, of a variant among `vs`, rebuilding its own tag: its fields, or
  ;; what it binds.
  (k-rebuild-arm (subr (maxeff checks spin) (k-case-arm k-parts k-proving) unit)
    (lambda (arm vs pv)
      (let* ((tag (extract arm 1)) (names (extract arm 3)) (body0 (extract arm 4))
             (vt (k-part-find vs tag)))
        (if (< vt 0)
            (k-proof-fail body0 pv "an arm for a tag that is not there")
            (let ((body (k-strip-conv body0)))
              (tagcase body
                (x-sum (t2 inner sa sb)
                  (cond ((not (symbol=? t2 tag))
                         (k-proof-fail body0 pv "each arm rebuilds its own tag"))
                        ((extract arm 2) (k-rebuild-arm-fields inner vt names body0 pv))
                        (else (k-rebuild inner (cons (car names) nil) vt #t pv))))
                (else z (k-proof-fail body0 pv "each arm rebuilds its own tag"))))))))
  ;; An arm's body, `body0`, a variant of type `vt` made of `inner0`,
  ;; rebuilding the fields `names` name.
  (k-rebuild-arm-fields (subr (maxeff checks spin) (kx int k-names kx k-proving) unit)
    (lambda (inner0 vt names body0 pv)
      (tagcase (k-get (k-unfold-all vt 64))
        (ty-product (fs)
          (let ((inner (k-strip-conv inner0)))
            (tagcase inner
              (x-product (gs pa pb)
                (if (k-fields-fit? gs fs names)
                    (k-rebuild-fields gs fs names pv)
                    (k-proof-fail inner pv "each arm rebuilds its fields, in order")))
              (else z (k-proof-fail inner pv "each arm rebuilds its fields")))))
        (else z (k-proof-fail body0 pv "fields of something that is not a product")))))
  (k-rebuild-fields (subr (maxeff checks spin) (k-let-bs k-parts k-names k-proving) unit)
    (lambda (gs fs xs pv)
      (if (null? gs)
          #u
          (begin (k-rebuild (extract (car gs) 2) (cons (car xs) nil) (extract (car fs) 2) #t pv)
                 (k-rebuild-fields (cdr gs) (cdr fs) (cdr xs) pv)))))
  (k-rebuild-paths (subr (maxeff checks spin) (k-let-bs k-parts k-pos k-proving) unit)
    (lambda (gs fs at pv)
      (if (null? gs)
          #u
          (let ((field-at (k-pos-field at (extract (car gs) 1))))
            (begin (k-rebuild (extract (car gs) 2) field-at (extract (car fs) 2) #t pv)
                   (k-rebuild-paths (cdr gs) (cdr fs) at pv))))))
  ;; A coercion a proof passes to a proof: a hypothesis, a proof, itself
  ;; (under a constructor), or a lambda whose parameter is annotated and
  ;; whose body rebuilds it.
  (k-proof-coercion (subr (maxeff checks spin) (kx bool k-proving) unit)
    (lambda (c0 guarded pv)
      (let ((c (k-strip-conv c0)))
        (tagcase c
          (x-var (s a b)
            (cond ((k-has-name? (extract pv 2) s) #u)
                  ((symbol=? s (extract pv 1))
                   (if guarded
                       #u
                       (k-proof-fail c pv "it passes itself on before rebuilding anything")))
                  ((k-lemma-named? s) #u)
                  (else (k-proof-fail c pv k-proof-given))))
          (x-lambda (ps body a b) (k-rebuild-coercion c ps body guarded pv))
          (else y (k-proof-fail c pv k-proof-given))))))
  ;; A coercion `c` that is a lambda of parameters `ps`: of one, its type
  ;; written, which its body rebuilds.
  (k-rebuild-coercion (subr (maxeff checks spin) (kx k-typed-params kx bool k-proving) unit)
    (lambda (c ps body guarded pv)
      (if (and (not (null? ps)) (null? (cdr ps)) (not (null? (extract (car ps) 2))))
          (let ((x (extract (car ps) 1)))
            (if (k-relied-on? pv x)
                (k-proof-fail c pv "a proof may not rebind the names it relies on")
                (k-rebuild body (cons x nil) (car (extract (car ps) 2)) guarded pv)))
          (k-proof-fail c pv (string-append "a coercion given to a proof takes one parameter, "
                                            "with its type written")))))
  (k-proof-coercions (subr (maxeff checks spin) (kxs bool k-proving) unit)
    (lambda (cs guarded pv)
      (if (null? cs)
          #u
          (begin (k-proof-coercion (car cs) guarded pv) (k-proof-coercions (cdr cs) guarded pv))))))
(define k-under-abstractions (subr (maxeff (read @globals) spin) (kx) kx)
  (lambda (x)
    (tagcase x
      (x-plambda (bs body a b) (k-under-abstractions body))
      (x-the (t body a b) (k-under-abstractions body))
      (else y x))))
(define k-param-names-first (subr (maxeff kreads (alloc @t)) (k-typed-params int) k-names)
  (lambda (ps n)
    (if (= n 0)
        nil
        (the k-names (cons (extract (car ps) 1) (k-param-names-first (cdr ps) (- n 1)))))))

;; Whether `e`, the body of `name`, proves lemma `l`; an error where not.
(define k-check-proof (subr (maxeff checks spin) (k-lemma symbol kx) unit)
  (lambda (l name e)
    (let* ((want (k-cat5 "`" (k-show-ty (extract l 2)) " ≤ " (k-show-ty (extract l 3)) "`"))
           (x (k-under-abstractions e)))
      (tagcase x
        (x-lambda (ps body a b)
          (let ((n (k-length (extract l 4))))
            (if (not (= (k-length ps) (+ n 1)))
                (k-fail (k-cat3 "a proof of " want
                                (string-append " takes a coercion for each hypothesis, "
                                               "then what it proves of"))
                        a b)
                (let ((given (the k-pos (cons (extract (k-nth ps n) 1) nil)))
                      (pv (product (1 name) (2 (k-param-names-first ps n)) (3 want))))
                  (k-rebuild body given (extract l 2) #f pv)))))
        (else y (k-fail-at (k-cat3 "a proof of " want " is a lambda") e))))))
;; The generative type `name` may see inside, as one of its conversions, or
;; -1; no longer, once asked.
(define k-take-inside (subr kstate (symbol) int)
  (lambda (name)
    (letrec ((find (subr kreads (k-named) int)
                   (lambda (xs)
                     (cond ((null? xs) -1)
                           ((symbol=? (car (car xs)) name) (cdr (car xs)))
                           (else (find (cdr xs))))))
             (drop (subr (maxeff kreads (alloc @t)) (k-named) k-named)
                   (lambda (xs)
                     (cond ((null? xs) xs)
                           ((symbol=? (car (car xs)) name) (cdr xs))
                           (else (the k-named (cons (car xs) (drop (cdr xs)))))))))
      (let ((g (find (get k-inside))))
        (begin (if (>= g 0) (set k-inside (drop (get k-inside))) #u) g)))))
;; The symbol `prefix` then `n` spells.
(define k-prefixed (subr (read @globals) (string string) symbol)
  (lambda (prefix n) (string->symbol (string-append prefix n))))
(define k-declare (subr (maxeff checks spin) (top) unit)
  (lambda (form)
    (tagcase form
      (t-define-type (name def a b)
        (cond
          ;; `(define-type f (dlambda …))`: a name for a description function.
          ((and (syn-symbol? name) (string=? (k-list-head def) "dlambda"))
           (k-push-desc (k-name-of name "expected a name") (ds-fun (k-parse-fun def -1))))
          ((syn-symbol? name)
            (begin (k-define-type (k-name-of name "expected a name") def a b) #u))
          (else
            (let ((items (k-items name "a type definition")))
              (if (null? items)
                  (k-sfail "expected a name" name)
                  (k-define-family (k-name-of (car items) "expected a name") (cdr items) def))))))
      (t-define-effect (name def a b)
        (let* ((n (k-name-of name "expected a name"))
               (e (k-parse-effect def)))
          (k-push-desc n (ds-eff e))))
      (t-private-regions (rs a b) (k-private rs))
      (t-define-generative (head rep a b)
        (let* ((name (k-define-generative head rep))
               (g (- (get k-ngens) 1))
               (n (symbol->string name)))
          ;; Only its own conversions, which follow, see inside it.
          (set k-inside (cons (cons (k-prefixed "down-" n) g)
                              (cons (cons (k-prefixed "up-" n) g) (get k-inside))))))
      (else y #u))))

(define k-declare-each (subr (maxeff checks spin) (k-tops) unit)
  (lambda (forms)
    (if (null? forms)
        #u
        (begin (k-declare (car forms)) (k-declare-each (cdr forms))))))
(define k-names-reversed (subr (read @globals) (k-names k-names) k-names)
  (lambda (xs acc) (if (null? xs) acc (k-names-reversed (cdr xs) (cons (car xs) acc)))))
;; The names simple `define-type`s give, in order, each as often as given.
(define k-ahead-names-of (subr (maxeff (read @globals) (read @s) spin) (k-tops k-names) k-names)
  (lambda (forms acc)
    (if (null? forms)
        (k-names-reversed acc nil)
        (k-ahead-names-of
         (cdr forms)
         (tagcase (car forms)
           (t-define-type (name def a b)
             (if (and (syn-symbol? name) (not (string=? (k-list-head def) "dlambda")))
                 (cons (string->symbol (syn-name name)) acc)
                 acc))
           (else y acc))))))
;; The first pass: abbreviations, so that types can refer to each other in
;; any order. Values cannot: a definition sees only those before it. Each
;; abbreviation defined once, by name, is in scope before any is read, and
;; checked grounded once all are.
(define* k-ahead (subr (maxeff checks spin) (k-tops) unit)
  (lambda (forms)
    (let ((names (k-ahead-names-of forms nil)))
      (begin
        (set k-ahead-names nil)
        (set k-ahead-filled nil)
        (k-ahead-declare names names)
        (k-declare-each forms)
        (set k-ahead-names nil)
        (let ((filled (get k-ahead-filled)))
          (begin (set k-ahead-filled nil) (k-ground-filled (k-filled-reversed filled nil))))))))
(define k-line (subr (maxeff (read @globals) (read @t) (alloc @t) spin) (int k-eff) string)
  (lambda (t e) (k-cat3 (k-show-ty t) " ! " (k-show-effect e))))
;; The line for a definition of `name`, of type `t` and effect `e`.
(define k-define-line (subr (maxeff kreads (alloc @t) spin) (symbol int k-eff) string)
  (lambda (name t e) (k-cat4 "define " (symbol->string name) " : " (k-line t e))))
(define k-push-lines (subr (maxeff kreads (alloc @t)) (k-out k-out) k-out)
  (lambda (lines out) (if (null? lines) out (k-push-lines (cdr lines) (cons (car lines) out)))))
;; Bind `n`, at top level, to a value of type `t`: a global, a module's
;; abstract types named for it.
(define k-bind-named-global (subr (maxeff kstate spin) (symbol int) unit)
  (lambda (n t) (k-bind-global n (k-name-module n t))))
(define k-rec-types (subr (maxeff checks spin) (k-rec-forms) k-ids)
  (lambda (bs)
    (if (null? bs)
        nil
        (let* ((t (k-select-syn (k-parse-type (extract (car bs) 2)) (extract (car bs) 2)))
               (bound (k-bind-named-global (extract (car bs) 1) t))
               (noted (k-note-known (extract (car bs) 1) 0)))
          (cons t (k-rec-types (cdr bs)))))))
;; Each lambda, read under its signature: a lambda, or an error.
(define k-rec-lambdas (subr (maxeff checks spin) (k-rec-forms k-ids) k-letrec-bs)
  (lambda (bs ts)
    (if (null? bs)
        nil
        (let* ((name (extract (car bs) 1))
               (t (car ts))
               (saved (get k-dscope))
               (signed (k-bind-signature t))
               (x (k-resolve-exp (extract (car bs) 3)))
               (restored (set k-dscope saved))
               (checked (if (k-lambda? x) #u (k-fail-not-lambda name x))))
          (cons (product (1 name) (2 t) (3 x)) (k-rec-lambdas (cdr bs) (cdr ts)))))))
(define k-rec-check (subr (maxeff checks spin) (k-letrec-bs) k-out)
  (lambda (g)
    (if (null? g)
        nil
        (let* ((name (extract (car g) 1))
               (t (extract (car g) 2))
               (e (k-check-declared name t (extract (car g) 3)))
               (line (k-define-line name t e))
               (rest (k-rec-check (cdr g))))
          (cons line rest)))))

;; Each of `g`, by name and type, noted as recursive.
(define k-note-recursive (subr kstate (k-letrec-bs) unit)
  (lambda (g)
    (if (null? g)
        #u
        (let ((m (car g)))
          (begin (set k-recursive (cons (cons (extract m 1) (extract m 2)) (get k-recursive)))
                 (k-note-recursive (cdr g)))))))
;; A `define-rec` group's free variables.
(define k-group-free (subr kmakes (k-letrec-bs k-names) k-names)
  (lambda (g out)
    (if (null? g) out (k-group-free (cdr g) (k-free-into (extract (car g) 3) nil out)))))
;; `(define-rec (name type lambda) …)`: every name in scope first, then each
;; lambda checked against its type. A line for each.
(define k-define-rec (subr (maxeff checks spin) (k-rec-forms) k-out)
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

(define k-rev-runs (subr (read @globals) (k-run-list k-run-list) k-run-list)
  (lambda (xs acc) (if (null? xs) acc (k-rev-runs (cdr xs) (the k-run-list (cons (car xs) acc))))))
;; For a driver: what the program checked runs, in order (`compile-checked`,
;; `run-checked`).
(define checked-tops (subr (maxeff (read @globals) (read @t)) () (listof k-run acyclic))
  (lambda () (k-rev-runs (get k-runs) nil)))
(define k-rev-defs (subr (read @globals) (k-def-list k-def-list) k-def-list)
  (lambda (xs acc) (if (null? xs) acc (k-rev-defs (cdr xs) (the k-def-list (cons (car xs) acc))))))
(define k-rec-names (subr (read @globals) (k-rec-forms) k-names)
  (lambda (bs)
    (if (null? bs) nil (the k-names (cons (extract (car bs) 1) (k-rec-names (cdr bs)))))))
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
    (letrec ((go (subr (maxeff (read @globals) (read @t)) (k-def-list) bool)
               (lambda (ds)
                 (and (not (null? ds)) (or (k-has-name? (extract (car ds) 1) n) (go (cdr ds)))))))
      (go (get k-defs)))))
(define k-old-types (subr (maxeff (read @globals) (read @t) spin) (k-names) k-olds)
  (lambda (ns)
    (cond ((null? ns) nil)
          ((k-defined? (car ns))
           (the k-olds (cons (cons (car ns) (k-lookup-raw (car ns))) (k-old-types (cdr ns)))))
          (else (k-old-types (cdr ns))))))
;; Whether `o`'s global now has a type its old one's uses can take.
(define k-fits-its-old? (subr (maxeff kstate spin) ((pairof symbol int acyclic)) bool)
  (lambda (o) (k-subtype (k-lookup-raw (car o)) (cdr o))))
;; Whether each of them now has a type its old one's uses can take.
(define k-fits-old? (subr (maxeff kstate spin) (k-olds) bool)
  (lambda (os) (or (null? os) (and (k-fits-its-old? (car os)) (k-fits-old? (cdr os))))))
(define k-names-without (subr (maxeff (read @globals) (read @t)) (k-names k-names) k-names)
  (lambda (xs ns)
    (cond ((null? xs) xs)
          ((k-has-name? ns (car xs)) (k-names-without (cdr xs) ns))
          (else (the k-names (cons (car xs) (k-names-without (cdr xs) ns)))))))
(define k-defs-without (subr kreads (k-def-list k-names) k-def-list)
  (lambda (ds ns)
    (cond ((null? ds) ds)
          ((k-names-meet? (extract (car ds) 1) ns) (k-defs-without (cdr ds) ns))
          (else (the k-def-list (cons (car ds) (k-defs-without (cdr ds) ns)))))))
;; `form`, which defines `ns`, recorded as their definition now.
(define k-record (subr kstate (top k-names) unit)
  (lambda (form ns)
    (if (null? ns)
        #u
        (let ((def (product (1 ns) (2 form) (3 (k-names-without (get k-last-uses) ns)))))
          (set k-defs (the k-def-list (cons def (k-defs-without (get k-defs) ns))))))))
;; The definitions that use `ns`, and those that use them, and so on,
;; oldest first.
(define k-users-of (subr (maxeff kreads (alloc @t)) (k-names) k-def-list)
  (lambda (ns)
    (letrec ((go (subr (maxeff kreads (alloc @t)) (k-def-list k-names) k-def-list)
               (lambda (ds used)
                 (cond ((null? ds) nil)
                       ((k-names-meet? (extract (car ds) 1) ns) (go (cdr ds) used))
                       ((k-names-meet? (extract (car ds) 3) used)
                        (let ((more (k-names-onto (extract (car ds) 1) used)))
                          (the k-def-list (cons (car ds) (go (cdr ds) more)))))
                       (else (go (cdr ds) used))))))
      (go (k-rev-defs (get k-defs) nil) ns))))
;; Names as a message shows them: `a`, `b`.
(define k-shown (subr (maxeff (read @globals) (read @t) (alloc @t)) (k-names) string)
  (lambda (ns)
    (letrec ((go (subr (maxeff (read @globals) (alloc @t)) (k-names) k-texts)
               (lambda (xs)
                 (if (null? xs)
                     nil
                     (the k-texts (cons (k-quote (symbol->string (car xs))) (go (cdr xs))))))))
      (k-join (go ns) ", "))))
(define k-break-all (subr (maxeff kstate spin) (k-names string) unit)
  (lambda (ns why)
    (if (null? ns)
        #u
        (let ((b (product (1 (car ns)) (2 (k-name-depth (car ns))) (3 why))))
          (begin (set k-broken (the (listof k-break acyclic) (cons b (get k-broken))))
                 (k-break-all (cdr ns) why))))))
(define k-lines-append (subr (read @globals) (k-out k-out) k-out)
  (lambda (xs ys) (if (null? xs) ys (the k-out (cons (car xs) (k-lines-append (cdr xs) ys))))))
;; An error at `written` unless `tw`, the type `define*` checks at, is a
;; `subr` (≥ 0).
(define k-star-subr (subr checks (int syn) unit)
  (lambda (tw written)
    (if (< tw 0)
        (k-sfail "`define*` finds what a procedure reads: its type is a `subr`" written)
        #u)))
;; An error at `x` if `define*` (`star`) defines it, and it is not a
;; `lambda`.
(define k-star-lambda (subr checks (bool kx) unit)
  (lambda (star x)
    (if (and star (not (k-lambda? x)))
        (k-fail-at "`define*` defines a procedure: a `lambda`" x)
        #u)))
;; Note of `name`, the lambda `x` of type `t`, whether its runs may not
;; end, and if so why: then it is recursive, as a group of one, beside
;; those of `rsaved`.
(define k-note-alone (subr (maxeff kstate spin) (symbol int kx k-named) unit)
  (lambda (name t x rsaved)
    (let* ((g (the k-letrec-bs (cons (product (1 name) (2 t) (3 x)) nil)))
           (why (k-termination g)))
      (if (string=? why "")
          #u
          (begin (set k-recursive (cons (cons name t) rsaved)) (k-note-why g why))))))
;; Lemma `l`, now of the names `named`.
(define k-lemma-as (subr pure (k-lemma k-named) k-lemma)
  (lambda (l named)
    (product (1 (extract l 1)) (2 (extract l 2)) (3 (extract l 3)) (4 (extract l 4)) (5 named))))
;; `name`, of type `t`, defined as `x`, noted as a proof of `l`, once `x`
;; proves it.
(define k-note-lemma (subr (maxeff checks spin) (k-lemma symbol int kx) unit)
  (lambda (l name t x)
    (let ((named (the k-named (cons (cons name t) nil))))
      (begin (k-check-proof l name x)
             (set k-lemmas (cons (k-lemma-as l named) (get k-lemmas)))))))
;; `(define name type init)`, or, if `star` is not empty,
;; `(define* name type init)`: its line.
(define k-define-typed (subr (maxeff checks spin) (symbol syn syns-a exp) k-out)
  (lambda (name written star-syns init)
    ;; A lambda is in scope in itself, as a `letrec`
    ;; binding is; anything else is not.
    (let* ((reset (set k-pending-lemma nil))
           (t (k-select-syn (k-parse-type written) written))
           ;; `define*`: checked as though its type read
           ;; `@globals`, which finds what it reads.
           (star (not (null? star-syns)))
           (tw (if star (k-with-latent t (k-one (a-read (r-globals)))) t))
           (subr-ok (k-star-subr tw written))
           ;; A `proves` type: a lemma, once the body proves it.
           (lemma (get k-pending-lemma))
           (taken (set k-pending-lemma nil))
           (saved (get k-dscope))
           (signed (k-bind-signature t))
           (x (k-resolve-exp init))
           (lambda-ok (k-star-lambda star x))
           (u (set k-last-uses (k-free-into x nil nil)))
           (restored (set k-dscope saved))
           (bound (if (k-lambda? x) (k-bind-named-global name t) #u))
           (rsaved (get k-recursive))
           ;; A lambda whose every run ends needs no `spin`.
           (noted (if (k-lambda? x)
                      (begin (k-note-known name 0) (k-note-alone name tw x rsaved))
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
                        (begin (k-rebind-top name tf)
                               (set k-recursive rsaved)
                               (k-note-alone name tf x rsaved))
                        #u))
           (e (if star (k-star-checked name tf x) e0))
           (closed (if (>= inside 0)
                       (begin (set k-transparent (cdr (get k-transparent)))
                              (set k-conversions (cons (cons name t) (get k-conversions))))
                       #u))
           (popped (set k-recursive rsaved))
           (proved (if (null? lemma) #u (k-note-lemma (car lemma) name t x)))
           (after (if (k-lambda? x) #u (k-bind-named-global name tf))))
      (cons (k-define-line name tf e) nil))))
;; `(define name init)`, of no type written: its line.
(define k-define-untyped (subr (maxeff checks spin) (symbol exp) k-out)
  (lambda (name init)
    (let* ((x (k-resolve-exp init))
           (u (set k-last-uses (k-free-into x nil nil)))
           (r (k-synth x)))
      (begin (k-bind-named-global name (extract r 1))
             (if (k-lambda? x) (k-note-known name 0) #u)
             (cons (k-define-line name (extract r 1) (extract r 2)) nil)))))
;; One top-level form's lines: what each definition and expression is.
(define k-top-lines (subr (maxeff checks spin) (top) k-out)
  (lambda (form)
    (the k-out (tagcase form
                 (t-define (name ty init a b)
                   (if (null? ty)
                       (k-define-untyped name init)
                       (k-define-typed name (car ty) (cdr ty) init)))
                 (t-define-rec (bs a b) (k-define-rec bs))
                 (t-exp (e)
                   (let* ((x (k-resolve-exp e)) (r (k-synth x)))
                     (cons (k-line (extract r 1) (extract r 2)) nil)))
                 (else y nil)))))
(define k-lines-append-names (subr (read @globals) (k-names k-names) k-names)
  (lambda (xs ys)
    (if (null? xs) ys (the k-names (cons (car xs) (k-lines-append-names (cdr xs) ys))))))
;; The names `defs` define, in order.
(define k-defs-names (subr (maxeff kreads (alloc @t)) (k-def-list) k-names)
  (lambda (ds)
    (if (null? ds) nil (k-lines-append-names (extract (car ds) 1) (k-defs-names (cdr ds))))))
;; Those of `xs` that are in `ys`, in `xs`'s order.
(define k-names-within (subr (maxeff (read @globals) (read @t)) (k-names k-names) k-names)
  (lambda (xs ys)
    (cond ((null? xs) xs)
          ((k-has-name? ys (car xs)) (the k-names (cons (car xs) (k-names-within (cdr xs) ys))))
          (else (k-names-within (cdr xs) ys)))))
;; Whether effect `e` has `spin`.
(define k-has-spin? (subr (read @globals) (k-eff) bool)
  (lambda (e)
    (and (not (null? e)) (or (tagcase (car e) (a-spin () #t) (else y #f)) (k-has-spin? (cdr e))))))
;; Whether `t` is a procedure whose calls may not end: `spin` in its latent
;; effect, under any `poly`.
(define k-type-spins? (subr (maxeff (read @globals) (read @t) spin) (int) bool)
  (lambda (t)
    (tagcase (k-get (k-resolve t))
      (ty-poly (bs body) (k-type-spins? body))
      (ty-subr (e ps r cv) (k-has-spin? e))
      (else y #f))))
(define k-names-spin? (subr (maxeff (read @globals) (read @t) spin) (k-names) bool)
  (lambda (ns)
    (and (not (null? ns)) (or (k-type-spins? (k-lookup-raw (car ns))) (k-names-spin? (cdr ns))))))
(define k-top-start (subr pure (top) int)
  (lambda (form)
    (tagcase form (t-define (name ty init a b) a) (t-define-rec (bs a b) a) (else y 0))))
(define k-top-end (subr pure (top) int)
  (lambda (form)
    (tagcase form (t-define (name ty init a b) b) (t-define-rec (bs a b) b) (else y 0))))
(define k-atoms-globals (subr (maxeff (read @globals) (alloc @t)) (k-eff) k-regions)
  (lambda (e)
    (cond ((null? e) nil)
          ((k-globals-atom? (car e))
           (the k-regions (cons (k-atom-region (car e)) (k-atoms-globals (cdr e)))))
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
(define k-first-read (subr (maxeff kreads (alloc @t) spin) (k-regions k-names) k-names)
  (lambda (rs ns)
    (cond ((null? ns) nil)
          ((k-has-region-in? rs (r-global (car ns))) (the k-names (cons (car ns) nil)))
          (else (k-first-read rs (cdr ns))))))
;; What a procedure that may reach itself through a global must do.
(define k-must-spin string "` may reach itself through a global: its type must say `spin`")
;; Why calling `name`, which reads the global `m`, may reach itself.
(define k-reads-itself (subr (read @globals) (string string) string)
  (lambda (name m)
    (k-cat4 (k-cat5 "calling `" name "` reads `" m "`, so `") name k-must-spin
            " (or, to call itself directly, it binds itself with a local `letrec`)")))
;; Why calling `name`, which may read any global, may reach itself.
(define k-reads-any (subr (read @globals) (string) string)
  (lambda (name)
    (let ((so (k-cat5 "calling `" name "` may read any global, `" name "` too, so `")))
      (k-cat3 so name k-must-spin))))
;; An error at `form` if calling the procedure `name`, of type `t`, may
;; reach itself through a global: if it reads one of `ns`, or, if
;; `redefining`, any global.
(define k-not-reaching (subr (maxeff checks spin) (top string int k-names bool) unit)
  (lambda (form name t ns redefining)
    (let* ((reads (k-latent-globals t))
           (m (k-first-read reads ns))
           (a (k-top-start form))
           (b (k-top-end form)))
      (cond ((not (null? m)) (k-fail (k-reads-itself name (symbol->string (car m))) a b))
            ((and redefining (k-has-region-in? reads (r-globals))) (k-fail (k-reads-any name) a b))
            (else #u)))))
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
                           (begin (k-not-reaching form (symbol->string n) t ns redefining)
                                  (each (cdr ms)))))))))
      (each ns))))
;; Note that `form` runs, assigning the globals it defines (`assigns`) or
;; making them new.
(define k-note-run (subr kstate (top bool) unit)
  (lambda (form assigns)
    (set k-runs (the k-run-list (cons (product (1 form) (2 assigns)) (get k-runs))))))
;; Each of `users` checked again after the redefinition of `ns`: defined
;; again if it checks, broken if not.
(define k-rerun (subr (maxeff (read @globals) checks spin) (k-def-list k-names k-out) k-out)
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
                     (ran (k-note-run (extract u 2) assigns)))
                (k-rerun (cdr users) ns (k-lines-append lines ls))))
            (k-err (msg a b)
              (begin (k-unbind-to m)
                     (let ((why (k-cat5 "since " (k-shown ns) " was redefined (" msg ")")))
                       (k-break-all (extract u 1) why))
                     (k-rerun (cdr users) ns lines)))
            (else y (k-rerun (cdr users) ns lines)))))))
;; Whether a redefinition that makes a new global leaves the definitions
;; that use the name as they are, out of date, rather than checking them
;; again (`k-rerun`): what the REPL asks for, re-running them when told
;; (`,rerun-outdated`), as the Rust checker's `defer_reruns`.
(define k-defer-reruns (ref bool @t) (new #f))
;; For a driver: whether re-runs wait.
(define check-defer-reruns! (subr (maxeff (read @globals) (write @t)) (bool) unit)
  (lambda (on) (set k-defer-reruns on)))
;; A top-level form, checked under redefinition: its lines, and those of
;; the definitions it has run again.
(define k-defining (subr (maxeff checks spin) (top) k-out)
  (lambda (form)
    (let* ((ns (k-top-names form))
           (olds (k-old-types ns))
           (defer (get k-defer-reruns))
           (users (if (or (null? olds) defer) (the k-def-list nil) (k-users-of ns)))
           (reset (set k-last-uses nil))
           (lines (k-top-lines form))
           (knot (k-no-reaching-itself form ns (not (null? olds))))
           (assigns (and (not (null? olds)) (k-fits-old? olds)))
           (recorded (k-record form ns))
           (ran (k-note-run form assigns)))
      (if (or (null? olds) assigns defer) lines (k-rerun users ns lines)))))


;; The second pass: definitions and expressions, in order, each under
;; redefinition (`k-defining`).
(define k-forms (subr (maxeff checks spin) (k-tops k-out) k-out)
  (lambda (forms out)
    (if (null? forms)
        (reverse out)
        (k-forms (cdr forms) (k-push-lines (k-defining (car forms)) out)))))

;; The entry point: check a program's trees, in the initial environment
;; written `standard`. What each definition and expression is, in order,
;; or the first error.
(define check-program (subr (maxeff (read @globals) checks spin) (syns-a k-tops) k-result)
  (lambda (standard forms)
    (prompt k-tag
      (begin (k-reset) (k-standard standard) (set k-std-dscope (get k-dscope))
             (k-ahead forms) (k-ok (k-forms forms nil)))
      (lambda (r) r))))

;; The entry point for more of a program, form by form, as the REPL gives
;; them: checked in the environment the forms before left, which
;; `check-program` began. The facts for the compiler are only the new
;; forms', whose positions are in their own text.
(define check-more (subr (maxeff (read @globals) checks spin) (k-tops) k-result)
  (lambda (forms)
    (prompt k-tag
      (begin (set k-extracts nil)
             (set k-effect-notes nil)
             (set k-with-vals nil)
             (set k-reshapes nil)
             (set k-runs nil)
             (k-ahead forms)
             (k-ok (k-forms forms nil)))
      (lambda (r) r))))))

(define k-syms=? (with check-program-module k-syms=?))
(define k-place-of (with check-program-module k-place-of))
(define k-ahead (with check-program-module k-ahead))
(define checked-tops (with check-program-module checked-tops))
(define k-record (with check-program-module k-record))
(define check-defer-reruns! (with check-program-module check-defer-reruns!))
(define k-defining (with check-program-module k-defining))
(define check-program (with check-program-module check-program))
(define check-more (with check-program-module check-more))
