;;; The checker, in FX-26: proofs. A lemma's proof, checked: it calls only
;;; its hypotheses, itself or other proofs, and what it proves is what the
;;; lemma says. After `check-close.fx`; `check-program.fx` uses it (split
;;; from that file, `TODO.md` §68).

;; Its types, those it uses of the files before it, and the signatures of
;; what it is given.
;; Its types (`check-program-types.fx`, its file's after it), loaded before the
;; module so that they are not among its values; the module names what it
;; uses of them.
(let* ((check-program-types (load-module "fx26:check-program-types.fx"))
       (check-types-types (load-module "fx26:check-types-types.fx"))
       (check-resolve-types (load-module "fx26:check-resolve-types.fx"))
       (parser-types ((proj (load-module "fx26:parser-types.fx") @s @e @m @c @p)))
       (check-env-types (load-module "fx26:check-env-types.fx"))
       (check-calls-types (load-module "fx26:check-calls-types.fx"))
       (check-generative-types (load-module "fx26:check-generative-types.fx"))
       (check-read-descs-types (load-module "fx26:check-read-descs-types.fx"))
       (check-errors-types (load-module "fx26:check-errors-types.fx"))
       (check-read-types (load-module "fx26:check-read-types.fx"))
       (check-subtype-types (load-module "fx26:check-subtype-types.fx"))
       (check-sub-env-types (load-module "fx26:check-sub-env-types.fx"))
       (check-modules-types (load-module "fx26:check-modules-types.fx"))
       (check-modules-read-types (load-module "fx26:check-modules-read-types.fx"))
       (check-infer-types (load-module "fx26:check-infer-types.fx"))
       (check-terminate-types (load-module "fx26:check-terminate-types.fx"))
       (check-sc-graphs-types (load-module "fx26:check-sc-graphs-types.fx"))
       (check-print-types (load-module "fx26:check-print-types.fx"))
       (table-types (load-module "fx26:table-types.fx"))
       (reader-types (load-module "fx26:reader-types.fx")))
  ;; What it is given: the modules of the files before it that it uses.
  (lambda ((check-types (select check-types-types check-types-sig))
           (check-resolve (select check-resolve-types check-resolve-sig))
           (check-env (select check-env-types check-env-sig))
           (check-calls (select check-calls-types check-calls-sig))
           (check-generative (select check-generative-types check-generative-sig))
           (check-read-descs (select check-read-descs-types check-read-descs-sig))
           (check-errors (select check-errors-types check-errors-sig))
           (check-read (select check-read-types check-read-sig))
           (check-subtype (select check-subtype-types check-subtype-sig))
           (check-modules (select check-modules-types check-modules-sig))
           (check-infer (select check-infer-types check-infer-sig))
           (check-terminate (select check-terminate-types check-terminate-sig))
           (check-print (select check-print-types check-print-sig))
           (tables (select table-types tables-sig))
           (parser (select reader-types parser-sig))
           (check-sc-graphs (select check-sc-graphs-types check-sc-graphs-sig))
           (check-sub-env (select check-sub-env-types check-sub-env-sig))
           (check-modules-read (select check-modules-read-types check-modules-read-sig)))
    (module
(hide (include check-program-types) (include check-types-types) (include check-resolve-types)
      (include parser-types))
;; The types it uses of the files before it.
;; What it uses of the modules it is given: all of each, hidden.
(hide (include check-types) (include check-resolve) (include check-env) (include check-calls)
      (include check-generative) (include check-read-descs) (include check-errors)
      (include check-read) (include check-sub-env) (include check-modules-read)
      (include check-infer) (include check-sc-graphs) (include check-print) (include tables)
      (include parser))

;; `n`, of type `t`, bound as a standard binding: at a node of its own,
;; since a binding is the standard one by its type's id (`k-std-binding?`),
;; which interning would give a local of the same type.
(define k-bind-std (->* (symbol int) unit)
  (lambda (n t0)
    (let ((t (k-ty-fresh t0)))
      (begin (k-bind n t) (set k-std (cons (cons n t) (get k-std)))
             (table-set! (get k-std-table) n t)))))
;; A standard binding, `(name type)`, or `datum`'s `(define-type name type)`
;; (`check::DATUM`).
(define k-standard-binding (->* (syns-a) unit)
  (lambda (pair)
    (if (and (syn-symbol? (car pair)) (string=? (syn-name (car pair)) "define-type"))
        (begin (k-define-type (k-name-of (k-nth pair 1) "a name") (k-nth pair 2) 0 0) #u)
        (k-bind-std (k-name-of (car pair) "a name") (k-parse-type (k-nth pair 1))))))
;; The initial environment: `(name type)` for each binding.
(define k-standard (->* (syns-a) unit)
  (lambda (entries)
    (if (null? entries)
        #u
        (let ((pair (k-items (car entries) "a standard binding")))
          ;; `vsubr`'s declaration first: generative type 0, as in the Rust
          ;; checker (`check::VSUBR`), with no `up-` or `down-`.
          (if (and (syn-symbol? (car pair)) (string=? (syn-name (car pair)) "define-generative"))
              (begin (k-define-generative (k-nth pair 1) (k-nth pair 2)) (k-standard (cdr entries)))
              (begin (k-standard-binding pair) (k-standard (cdr entries))))))))

;; Put the binders of every `poly` at the top of `t` in scope for reading.
(define k-bind-signature (->* (int) unit)
  (lambda (t)
    (tagcase (k-get t)
      (ty-poly (bs body) (begin (k-push-binders bs) (k-bind-signature body)))
      (else y #u))))

;; `define-type` and `define-effect`.
;;; ------------------------------------------------------------ proofs
;;; A definition whose declared type is `(proves …)` is a lemma once its
;;; body is a guarded structural identity (`src/lemma.rs`): it takes apart
;;; only what it was given, rebuilds the same tags and labels, applies
;;; hypotheses and proofs only to what was given at the same place, and uses
;;; itself only under a constructor.

(define k-syms=? (->* ((listof symbol acyclic) (listof symbol acyclic)) bool)
  (lambda (xs ys)
    (if (null? xs)
        (null? ys)
        (and (not (null? ys)) (symbol=? (car xs) (car ys)) (k-syms=? (cdr xs) (cdr ys))))))
(define k-append-sym (->* (k-names symbol) k-names)
  (lambda (xs l)
    (if (null? xs)
        (the k-names (cons l nil))
        (the k-names (cons (car xs) (k-append-sym (cdr xs) l))))))
;; The place of field `l` of what is at `p`.
(define k-pos-field (->* (k-pos symbol) k-pos)
  (lambda (p l) (cons (car p) (k-append-sym (cdr p) l))))
;; Whether `p` and `q` are the same place.
(define k-pos=? (->* (k-pos k-pos) bool)
  (lambda (p q) (and (symbol=? (car p) (car q)) (k-syms=? (cdr p) (cdr q)))))
;; Whether `f` names a generative type's conversion.
(define k-names-conversion? (->* (kx) bool)
  (lambda (f)
    (tagcase (k-under f)
      (x-var (s a b abk)
        (let ((t (k-lookup s))) (and (>= t 0) (k-named-has? (get k-conversions) s t))))
      (else y #f))))
;; `e` under ascriptions and conversions, which are the identity.
(define k-strip-conv (->* (kx) kx)
  (lambda (e)
    (tagcase e
      (x-the (t x a b abk) (k-strip-conv x))
      (x-app (f args a b abk)
        (if (and (k-sc-one? args) (k-names-conversion? f)) (k-strip-conv (car args)) e))
      (else y e))))
;; The place `e` names, if it names one (none or one).
(define k-place-of (->* (kx) (listof k-pos acyclic))
  (lambda (e)
    (tagcase (k-strip-conv e)
      (x-var (s a b abk) (the (listof k-pos acyclic) (cons (cons s nil) nil)))
      (x-extract (x l a b abk)
        (let ((p (k-place-of x)))
          (if (null? p) nil (the (listof k-pos acyclic) (cons (k-pos-field (car p) l) nil)))))
      (else y nil))))
(define k-at? (->* (kx k-pos) bool)
  (lambda (e at)
    (let ((p (k-place-of e))) (and (not (null? p)) (k-pos=? (car p) at)))))
;; `t` with generative types unfolded, as far as they go.
(define k-unfold-all (->* (int int) int)
  (lambda (t n)
    (if (= n 0)
        t
        (let ((t (k-resolve t)))
          (tagcase (k-get t)
            (ty-named (g ds) (k-unfold-all (k-unfold g ds) (- n 1)))
            (else y t))))))
;; The error that `e` does not prove what `pv` is to, and why.
(define k-proof-fail (->* (kx k-proving string) void)
  (lambda (e pv why) (k-fail-at (k-cat4 "this does not prove " (extract pv 3) ": " why) e)))
;; Why a proof may not call, or be given, what it is.
(define k-proof-calls string "a proof may call only its hypotheses, itself, or another proof")
(define k-proof-given string "a proof is given only hypotheses, proofs, or coercions that rebuild")
(define k-lemma-name? (->* ((listof k-lemma acyclic) symbol int) bool)
  (lambda (ls s t)
    (and (not (null? ls))
         (or (k-named-has? (extract (car ls) 5) s t) (k-lemma-name? (cdr ls) s t)))))
;; Whether `s` names a proof.
(define k-lemma-named? (->* (symbol) bool)
  (lambda (s) (let ((t (k-lookup s))) (and (>= t 0) (k-lemma-name? (get k-lemmas) s t)))))
(define k-names-meet? (->* (k-names k-names) bool)
  (lambda (xs ys)
    (and (not (null? xs)) (or (k-has-name? ys (car xs)) (k-names-meet? (cdr xs) ys)))))
;; Whether `y` is a name the proof relies on: its own, or a hypothesis's.
(define k-relied-on? (->* (k-proving symbol) bool)
  (lambda (pv y) (or (symbol=? y (extract pv 1)) (k-has-name? (extract pv 2) y))))
;; Whether `names`, bound by an arm, rebind what the proof relies on: what
;; was given at `at`, its own name, or a hypothesis's.
(define k-rebinds? (->* (k-names k-pos k-proving) bool)
  (lambda (names at pv)
    (or (k-has-name? names (car at))
        (k-has-name? names (extract pv 1))
        (k-names-meet? names (extract pv 2)))))
;; Whether fields `gs` rebuild `fs`, which `names` name: as many, with the
;; same labels, in order.
(define k-fields-fit? (->* (k-let-bs k-parts k-names) bool)
  (lambda (gs fs names)
    (and (= (k-length gs) (k-length fs))
         (= (k-length names) (k-length fs))
         (k-same-labels? gs fs))))
(define k-last (->* (kxs) kx)
  (lambda (xs) (if (null? (cdr xs)) (car xs) (k-last (cdr xs)))))
(define k-but-last (->* (kxs) kxs)
  (lambda (xs) (if (null? (cdr xs)) nil (the kxs (cons (car xs) (k-but-last (cdr xs)))))))
(define-rec
  ;; Whether `e0` rebuilds, as the identity, what was given at `at`, of type
  ;; `ty`; `guarded` once something has been rebuilt above it.
  (k-rebuild (->* (kx k-pos int bool k-proving) unit)
    (lambda (e0 at ty guarded pv)
      (let ((e (k-strip-conv e0)))
        (if (k-at? e at) #u (k-rebuild-node e at ty guarded pv)))))
  ;; `e`, not what was given at `at` itself: a call, or what takes that
  ;; apart or rebuilds it.
  (k-rebuild-node (->* (kx k-pos int bool k-proving) unit)
    (lambda (e at ty guarded pv)
      (tagcase e
        (x-app (f args a b abk) (k-rebuild-call e f args at guarded pv))
        (x-tagcase (sc arms els a b abk)
          (if (not (k-at? sc at))
              (k-proof-fail sc pv "a proof takes apart only what was given here")
              (tagcase (k-get (k-unfold-all ty 64))
                (ty-sum (vs)
                  (begin (k-rebuild-arms arms vs at pv) (k-rebuild-else els ty guarded pv)))
                (else z (k-proof-fail sc pv "what is given here is not a sum")))))
        (x-product (gs a b abk) (k-rebuild-product e gs at ty pv))
        (else y
          (k-proof-fail e pv "a proof may only take apart and rebuild what it was given")))))
  ;; A call `e`, of `f` on `args`: a hypothesis applied to what was given at
  ;; `at`, or a proof.
  (k-rebuild-call (->* (kx kx kxs k-pos bool k-proving) unit)
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
  (k-rebuild-proof-call (->* (kx symbol kxs k-pos bool k-proving) unit)
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
  (k-rebuild-product (->* (kx k-let-bs k-pos int k-proving) unit)
    (lambda (e gs at ty pv)
      (tagcase (k-get (k-unfold-all ty 64))
        (ty-product (fs)
          (if (k-same-labels? gs fs)
              (k-rebuild-paths gs fs at pv)
              (k-proof-fail e pv "a product is rebuilt with its fields, in order")))
        (else z (k-proof-fail e pv "what is given here is not a product")))))
  ;; A `tagcase`'s `else`, if it has one, rebuilding what it is given, of
  ;; type `ty`, under its own name.
  (k-rebuild-else (->* (k-let-bs int bool k-proving) unit)
    (lambda (els ty guarded pv)
      (if (null? els)
          #u
          (let ((y (extract (car els) 1)) (body (extract (car els) 2)))
            (if (k-relied-on? pv y)
                (k-proof-fail body pv "a proof may not rebind the names it relies on")
                (k-rebuild body (cons y nil) ty guarded pv))))))
  (k-rebuild-arms (->* (k-arms k-parts k-pos k-proving) unit)
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
  (k-rebuild-arm (->* (k-case-arm k-parts k-proving) unit)
    (lambda (arm vs pv)
      (let* ((tag (extract arm 1)) (names (extract arm 3)) (body0 (extract arm 4))
             (vt (k-part-find vs tag)))
        (if (< vt 0)
            (k-proof-fail body0 pv "an arm for a tag that is not there")
            (let ((body (k-strip-conv body0)))
              (tagcase body
                (x-sum (t2 inner sa sb sasbk)
                  (cond ((not (symbol=? t2 tag))
                         (k-proof-fail body0 pv "each arm rebuilds its own tag"))
                        ((extract arm 2) (k-rebuild-arm-fields inner vt names body0 pv))
                        (else (k-rebuild inner (cons (car names) nil) vt #t pv))))
                (else z (k-proof-fail body0 pv "each arm rebuilds its own tag"))))))))
  ;; An arm's body, `body0`, a variant of type `vt` made of `inner0`,
  ;; rebuilding the fields `names` name.
  (k-rebuild-arm-fields (->* (kx int k-names kx k-proving) unit)
    (lambda (inner0 vt names body0 pv)
      (tagcase (k-get (k-unfold-all vt 64))
        (ty-product (fs)
          (let ((inner (k-strip-conv inner0)))
            (tagcase inner
              (x-product (gs pa pb papbk)
                (if (k-fields-fit? gs fs names)
                    (k-rebuild-fields gs fs names pv)
                    (k-proof-fail inner pv "each arm rebuilds its fields, in order")))
              (else z (k-proof-fail inner pv "each arm rebuilds its fields")))))
        (else z (k-proof-fail body0 pv "fields of something that is not a product")))))
  (k-rebuild-fields (->* (k-let-bs k-parts k-names k-proving) unit)
    (lambda (gs fs xs pv)
      (if (null? gs)
          #u
          (begin (k-rebuild (extract (car gs) 2) (cons (car xs) nil) (extract (car fs) 2) #t pv)
                 (k-rebuild-fields (cdr gs) (cdr fs) (cdr xs) pv)))))
  (k-rebuild-paths (->* (k-let-bs k-parts k-pos k-proving) unit)
    (lambda (gs fs at pv)
      (if (null? gs)
          #u
          (let ((field-at (k-pos-field at (extract (car gs) 1))))
            (begin (k-rebuild (extract (car gs) 2) field-at (extract (car fs) 2) #t pv)
                   (k-rebuild-paths (cdr gs) (cdr fs) at pv))))))
  ;; A coercion a proof passes to a proof: a hypothesis, a proof, itself
  ;; (under a constructor), or a lambda whose parameter is annotated and
  ;; whose body rebuilds it.
  (k-proof-coercion (->* (kx bool k-proving) unit)
    (lambda (c0 guarded pv)
      (let ((c (k-strip-conv c0)))
        (tagcase c
          (x-var (s a b abk)
            (cond ((k-has-name? (extract pv 2) s) #u)
                  ((symbol=? s (extract pv 1))
                   (if guarded
                       #u
                       (k-proof-fail c pv "it passes itself on before rebuilding anything")))
                  ((k-lemma-named? s) #u)
                  (else (k-proof-fail c pv k-proof-given))))
          (x-lambda (ps body a b abk) (k-rebuild-coercion c ps body guarded pv))
          (else y (k-proof-fail c pv k-proof-given))))))
  ;; A coercion `c` that is a lambda of parameters `ps`: of one, its type
  ;; written, which its body rebuilds.
  (k-rebuild-coercion (->* (kx k-typed-params kx bool k-proving) unit)
    (lambda (c ps body guarded pv)
      (if (and (not (null? ps)) (null? (cdr ps)) (not (null? (extract (car ps) 2))))
          (let ((x (extract (car ps) 1)))
            (if (k-relied-on? pv x)
                (k-proof-fail c pv "a proof may not rebind the names it relies on")
                (k-rebuild body (cons x nil) (car (extract (car ps) 2)) guarded pv)))
          (k-proof-fail c pv (string-append "a coercion given to a proof takes one parameter, "
                                            "with its type written")))))
  (k-proof-coercions (->* (kxs bool k-proving) unit)
    (lambda (cs guarded pv)
      (if (null? cs)
          #u
          (begin (k-proof-coercion (car cs) guarded pv) (k-proof-coercions (cdr cs) guarded pv))))))
(define k-under-abstractions (->* (kx) kx)
  (lambda (x)
    (tagcase x
      (x-plambda (bs body a b abk) (k-under-abstractions body))
      (x-the (t body a b abk) (k-under-abstractions body))
      (else y x))))
(define k-param-names-first (->* (k-typed-params int) k-names)
  (lambda (ps n)
    (if (= n 0)
        nil
        (the k-names (cons (extract (car ps) 1) (k-param-names-first (cdr ps) (- n 1)))))))

;; Whether `e`, the body of `name`, proves lemma `l`; an error where not.
(define k-check-proof (->* (k-lemma symbol kx) unit)
  (lambda (l name e)
    (let* ((want (k-cat5 "`" (k-show-ty (extract l 2)) " ≤ " (k-show-ty (extract l 3)) "`"))
           (x (k-under-abstractions e)))
      (tagcase x
        (x-lambda (ps body a b abk)
          (let ((n (k-length (extract l 4))))
            (if (not (= (k-length ps) (+ n 1)))
                (k-fail (k-cat3 "a proof of " want
                                (string-append " takes a coercion for each hypothesis, "
                                               "then what it proves of"))
                        a b)
                (let ((given (the k-pos (cons (extract (k-nth ps n) 1) nil)))
                      (pv (product (1 name) (2 (k-param-names-first ps n)) (3 want))))
                  (k-rebuild body given (extract l 2) #f pv)))))
        (else y (k-fail-at (k-cat3 "a proof of " want " is a lambda") e)))))))))
