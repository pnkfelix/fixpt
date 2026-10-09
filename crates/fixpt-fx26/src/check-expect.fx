;;; The checker, in FX-26: what was expected and what was found, said;
;;; conversions between conventions; and the binding helpers the rules use.
;;; After `check-subtype.fx`.
;;; Part of the checker, `check-types.fx` first (PLAN.md §11, step 10).

;;; ------------------------------------------------------------ errors

;; Its types, those it uses of the files before it, and the signatures of
;; what it is given.
(let* ((check-types-types (load-module "fx26:check-types-types.fx"))
       (check-synth-types (load-module "fx26:check-synth-types.fx"))
       (check-env-types (load-module "fx26:check-env-types.fx"))
       (check-subtype-types (load-module "fx26:check-subtype-types.fx"))
       (check-resolve-types (load-module "fx26:check-resolve-types.fx"))
       (check-subst-types (load-module "fx26:check-subst-types.fx"))
       (check-print-types (load-module "fx26:check-print-types.fx"))
       (check-kinds-types (load-module "fx26:check-kinds-types.fx"))
       (check-effects-types (load-module "fx26:check-effects-types.fx"))
       (check-modules-types (load-module "fx26:check-modules-types.fx")))
  ;; What it is given: the modules of the files before it that it uses.
  (lambda ((check-types (select check-types-types check-types-sig))
           (check-env (select check-env-types check-env-sig))
           (check-subtype (select check-subtype-types check-subtype-sig))
           (check-print (select check-print-types check-print-sig))
           (check-kinds (select check-kinds-types check-kinds-sig))
           (check-resolve (select check-resolve-types check-resolve-sig))
           (check-effects (select check-effects-types check-effects-sig))
           (check-modules (select check-modules-types check-modules-sig)))
    (module

;; The types it uses of the files before it.
(define a-alloc (with check-types-types a-alloc))
(define a-read (with check-types-types a-read))
(define a-spin (with check-types-types a-spin))
(define-effect checks (select check-types-types checks))
(define cv-cellular (with check-types-types cv-cellular))
(define cv-native (with check-types-types cv-native))
(define de (with check-types-types de))
(define df (with check-types-types df))
(define dt (with check-types-types dt))
(define-type k-binders (select check-types-types k-binders))
(define-type k-conv (select check-types-types k-conv))
(define-type k-desc (select check-types-types k-desc))
(define-type k-descs (select check-types-types k-descs))
(define k-done (with check-types-types k-done))
(define-type k-eff (select check-types-types k-eff))
(define k-err (with check-types-types k-err))
(define-type k-ids (select check-types-types k-ids))
(define-type k-map (select check-types-types k-map))
(define-type k-names (select check-types-types k-names))
(define k-ok (with check-types-types k-ok))
(define-type k-te (select check-types-types k-te))
(define-effect kreads (select check-types-types kreads))
(define-effect kstate (select check-types-types kstate))
(define-type kx (select check-types-types kx))
(define r-global (with check-types-types r-global))
(define sz-finite (with check-types-types sz-finite))
(define ty-module (with check-types-types ty-module))
(define ty-nat (with check-types-types ty-nat))
(define ty-poly (with check-types-types ty-poly))
(define ty-select (with check-types-types ty-select))
(define ty-subr (with check-types-types ty-subr))
(define x-lambda (with check-types-types x-lambda))
(define x-plambda (with check-types-types x-plambda))
(define x-rlambda (with check-types-types x-rlambda))
(define x-the (with check-types-types x-the))
(define-type k-done (select check-synth-types k-done))
(define-type k-bindings (select check-env-types k-bindings))
(define-type k-checking (select check-subtype-types k-checking))
(define-type k-effs (select check-subtype-types k-effs))
(define-type k-saying (select check-subtype-types k-saying))
(define-type k-let-bs (select check-resolve-types k-let-bs))
(define-type k-letrec-bs (select check-resolve-types k-letrec-bs))
(define-type k-typed-params (select check-resolve-types k-typed-params))
(define-effect kmakes (select check-subst-types kmakes))
;; What it uses of the modules it is given.
(define k-arrow-kind? (with check-types k-arrow-kind?))
(define k-cat3 (with check-types k-cat3))
(define k-cat4 (with check-types k-cat4))
(define k-cat5 (with check-types k-cat5))
(define k-dvar-name (with check-types k-dvar-name))
(define k-fail (with check-types k-fail))
(define k-find-sub (with check-types k-find-sub))
(define k-get (with check-types k-get))
(define k-length (with check-types k-length))
(define k-named-has? (with check-types k-named-has?))
(define k-new-dvar-of (with check-types k-new-dvar-of))
(define k-quote (with check-types k-quote))
(define k-recursive (with check-types k-recursive))
(define k-resolve (with check-types k-resolve))
(define k-skolems (with check-types k-skolems))
(define k-tag (with check-types k-tag))
(define k-te (with check-types k-te))
(define k-ty-new (with check-types k-ty-new))
(define k-bind (with check-env k-bind))
(define k-extracts (with check-env k-extracts))
(define k-global? (with check-env k-global?))
(define k-globals-effects (with check-env k-globals-effects))
(define k-note-known (with check-env k-note-known))
(define k-unit (with check-env k-unit))
(define k-reshape-at (with check-subtype k-reshape-at))
(define k-subtype (with check-subtype k-subtype))
(define k-conv-default (with check-print k-conv-default))
(define k-conv=? (with check-print k-conv=?))
(define k-kind-word (with check-print k-kind-word))
(define k-show-effect (with check-print k-show-effect))
(define k-show-ty (with check-print k-show-ty))
(define k-size-var (with check-print k-size-var))
(define k-desc-of-kind? (with check-kinds k-desc-of-kind?))
(define k-end (with check-resolve k-end))
(define k-start (with check-resolve k-start))
(define k-insert (with check-effects k-insert))
(define k-one (with check-effects k-one))
(define k-within? (with check-effects k-within?))
(define k-name-module (with check-modules k-name-module))
(define k-resolve-selects (with check-modules k-resolve-selects))

(define k-newline string (char->string (integer->char 10)))
;; Run `f`, and if it fails at `a`..`b` with "a W is expected here, and
;; this is a G", fail instead with what `say` makes of W and G.
(define k-expected-split (subr (maxeff (read @globals) spin) (string) string)
  (lambda (m) (if (= (string-search m "a " 0) 0) (substring m 2 (string-length m)) "")))
(define k-sep string " is expected here, and this is a ")
;; "a W is expected here, and this is a G", of `w` and `g`.
(define k-expected-here (subr (read @globals) (string string) string)
  (lambda (w g) (k-cat4 "a " w k-sep g)))
(define k-rewriting (subr (maxeff checks spin) (k-checking int int k-saying) k-te)
  (lambda (f a b say)
    (let ((r (prompt k-tag (k-done (f)) (lambda (r) r))))
      (tagcase r
        (k-done (te) te)
        (k-err (m ea eb)
          ;; Its second line, an effect's delta, apart, and put back last.
          (let* ((nl (string-search m k-newline 0))
                 (first (if (< nl 0) m (substring m 0 nl)))
                 (delta (if (< nl 0) "" (substring m nl (string-length m))))
                 (rest (k-expected-split first)) (at (k-find-sub rest k-sep 0)))
            (if (and (= ea a) (= eb b) (not (string=? rest "")) (>= at 0))
                (let ((w (substring rest 0 at))
                      (g (substring rest (+ at (string-length k-sep)) (string-length rest))))
                  (k-fail (string-append (say m w g) delta) ea eb))
                (k-fail m ea eb))))
        (k-ok (xs) (k-fail "k-ok inside" a b))))))
;; The same, for any error at `a`..`b`.
(define k-prefixing (subr checks ((subr checks () k-te) int int (subr checks () string)) k-te)
  (lambda (f a b prefix)
    (let ((r (prompt k-tag (k-done (f)) (lambda (r) r))))
      (tagcase r
        (k-done (te) te)
        (k-err (m ea eb)
          (if (and (= ea a) (= eb b)) (k-fail (string-append (prefix) m) ea eb) (k-fail m ea eb)))
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
            (if (and (not (k-conv=? from to)) (k-subtype (k-ty-new (ty-subr e ps r to)) want))
                (cons to nil)
                nil))
          (else y nil)))
      (else y nil))))
;; Conversion `code` at `x`'s span, among the facts `checked-extracts` gives.
(define k-note-conversion (subr (maxeff checks spin) (kx int) unit)
  (lambda (x code)
    (let ((fact (product (1 (k-start x)) (2 (k-end x)) (3 (- -1000 code)))))
      (set k-extracts (cons fact (get k-extracts))))))
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
(define k-latent-of (subr (maxeff kstate spin) (int) k-effs)
  (lambda (t)
    (tagcase (k-get (k-resolve t))
      (ty-poly (bs body) (k-latent-of body))
      (ty-subr (e ps r cv) (the k-effs (cons e nil)))
      (else y nil))))
;; The atoms of `g` that `w` does not cover.
(define k-uncovered (subr (maxeff kstate spin) (k-eff k-eff) k-eff)
  (lambda (g w)
    (cond ((null? g) nil)
          ((k-within? (k-one (car g)) w) (k-uncovered (cdr g) w))
          (else (the k-eff (cons (car g) (k-uncovered (cdr g) w)))))))
;; The second line of an "is expected here" message, where `got` and `want`
;; are procedures: the atoms of `got`'s latent effect that `want`'s does not
;; cover (`Checker::effect_delta`).
(define* k-effect-delta (subr (maxeff kstate spin) (int int) string)
  (lambda (got want)
    (let ((g (k-latent-of got)) (w (k-latent-of want)))
      (if (or (null? g) (null? w))
          ""
          (let ((beyond (k-uncovered (car g) (car w))))
            (if (null? beyond)
                ""
                (k-cat3 k-newline "  beyond what is expected, it has " (k-show-effect beyond))))))))
;; `got ≤ want`, or an error at `x` saying so.
(define k-expect (subr (maxeff checks spin) (kx int int) unit)
  (lambda (x got want)
    (if (k-subtype got want)
        #u
        (let ((c (k-conversion got want)))
          (cond ((not (null? c)) (k-convert-at x got (car c)))
                ((k-reshape-at x got want) #u)
                (else
                 (k-fail (string-append (k-expected-here (k-show-ty want) (k-show-ty got))
                                        (k-effect-delta got want))
                         (k-start x) (k-end x))))))))
;; Bind each, the first first.
(define k-bind-all (subr (maxeff kstate spin) (k-bindings) unit)
  (lambda (bs)
    (if (null? bs) #u (begin (k-bind (car (car bs)) (cdr (car bs))) (k-bind-all (cdr bs))))))
;; `t` for a variable being bound to it: a `nat` of no known size is given
;; one, a variable of its own named after the variable, so that tests of it
;; can teach facts; and a module's abstract types are named too.
(define k-name-nat (subr (maxeff kstate spin) (symbol int) int)
  (lambda (name t)
    (tagcase (k-get (k-resolve t))
      (ty-module (abs ds vs) (k-name-module name t))
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
        (let ((n (car (car bs))) (t (cdr (car bs))))
          (begin (k-bind n (k-name-nat n t)) (k-bind-named (cdr bs)))))))
(define k-note-letrec (subr (maxeff kstate spin) (k-letrec-bs bool) unit)
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
(define k-naming-effect (subr (maxeff kmakes spin) (symbol int) k-eff)
  (lambda (s t)
    (let ((spins (if (k-named-has? (get k-recursive) s t) (k-one (a-spin)) (the k-eff nil))))
      (if (and (get k-globals-effects) (k-global? s))
          (k-insert (a-read (r-global s)) spins)
          spins))))
(define k-bind-letrec (subr (maxeff kstate spin) (k-letrec-bs) unit)
  (lambda (bs)
    (if (null? bs)
        #u
        (begin (k-bind (extract (car bs) 1) (extract (car bs) 2)) (k-bind-letrec (cdr bs))))))
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
  (lambda (ns n)
    (cond ((null? ns) 0)
          ((symbol=? (car ns) n) (+ 1 (k-count-name (cdr ns) n)))
          (else (k-count-name (cdr ns) n)))))
;; Note each `let` binding of a lambda as known, once bound: of several of
;; one name, each is as many from the innermost as come after it. The
;; names, in order.
(define k-note-let-lambdas (subr (maxeff kstate spin) (k-let-bs) k-names)
  (lambda (bs)
    (if (null? bs)
        nil
        (let* ((later (k-note-let-lambdas (cdr bs)))
               (n (extract (car bs) 1))
               (x (extract (car bs) 2))
               (noted (if (k-lambda? x) (k-note-known n (k-count-name later n)) #u)))
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
(define k-only-alloc? (subr kreads (k-eff) bool)
  (lambda (e)
    (or (null? e) (and (tagcase (car e) (a-alloc (r) #t) (else y #f)) (k-only-alloc? (cdr e))))))
(define k-generalizable? (subr kreads (kx k-eff) bool)
  (lambda (x e) (or (null? e) (and (k-rlambda-under? x) (k-only-alloc? e)))))
(define k-letrec-not-lambda (subr (read @globals) (symbol) string)
  (lambda (n)
    (k-cat3 (k-quote (symbol->string n))
            " is bound recursively, so it must be a lambda: "
            "nothing may run before every binding exists")))

;; Binder `v`'s name, quoted.
(define k-quote-dvar (subr kreads (int) string)
  (lambda (v) (k-quote (symbol->string (k-dvar-name v)))))
;; Effect `e`, its `select`s resolved: as a subroutine's latent effect.
(define k-effect-resolved (subr (maxeff checks spin) (k-eff int int) k-eff)
  (lambda (e a b)
    (let ((t (k-resolve-selects (k-ty-new (ty-subr e nil k-unit (get k-conv-default))) a b)))
      (tagcase (k-get t) (ty-subr (r ps res cv) r) (else y e)))))
;; Description `d`, given where one of kind `k` is wanted: a `select` given
;; for a description function, resolved, and taken as one; a type given,
;; its `select`s resolved, as an annotation's are (a type a module
;; re-exports may be inside it); an effect, likewise (`(select m e)`).
(define k-select-fun (subr (maxeff checks spin) (k-desc int int int) k-desc)
  (lambda (d k a b)
    (let ((t (tagcase d (dt (x) x) (df (x) x) (else y -1))))
      (cond ((and (k-arrow-kind? k) (>= t 0) (tagcase (k-get t) (ty-select (m n) #t) (else y #f)))
             (df (k-resolve-selects t a b)))
            ((tagcase d (dt (x) #t) (else y #f)) (dt (k-resolve-selects t a b)))
            (else (tagcase d (de (e) (de (k-effect-resolved e a b))) (else y d)))))))
(define k-proj-map (subr (maxeff checks spin) (k-binders k-descs int int) k-map)
  (lambda (bs ds a b)
    (if (null? bs)
        nil
        (let* ((v (extract (car bs) 1)) (k (extract (car bs) 2))
               ;; A function given as a `select`: resolved first.
               (d (k-select-fun (car ds) k a b))
               (ok (k-desc-of-kind? d k)))
          (if ok
              (cons (cons v d) (k-proj-map (cdr bs) (cdr ds) a b))
              (k-fail (k-cat4 (k-quote-dvar v) " is bound as a " (k-kind-word k)
                              ", and the description given is not one")
                      a b))))))
(define k-param-types (subr checks (k-typed-params k-ids int int) k-bindings)
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
(define k-binding-types (subr kmakes (k-bindings) k-ids)
  (lambda (bs) (if (null? bs) nil (cons (cdr (car bs)) (k-binding-types (cdr bs))))))
(define k-some-untyped? (subr kreads (k-typed-params) bool)
  (lambda (ps)
    (cond ((null? ps) #f)
          ((null? (extract (car ps) 2)) #t)
          (else (k-some-untyped? (cdr ps))))))

(define k-unannotated? (subr kreads (kx) bool)
  (lambda (x) (tagcase x (x-lambda (ps body a b) (k-some-untyped? ps)) (else y #f))))
;; A `lambda` missing parameter types, or a thunk: better told than asked.
(define k-needs-telling? (subr kreads (kx) bool)
  (lambda (x)
    (tagcase x (x-lambda (ps body a b) (or (null? ps) (k-some-untyped? ps))) (else y #f)))))))
