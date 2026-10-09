;;; The checker, in FX-26: dependent procedures (`docs/research/
;;; first-class-modules.md`, stage M5), as the Rust checker's `modules.rs`
;;; and `synth_lambda_as` make them. After `check-subtype.fx`, whose
;;; `k-name-nat` names a parameter's module. Part of the checker,
;;; `check-types.fx` first.

;;; ------------------------------------------------------------ dependent procedures
;;; A procedure's parameter may be named, `(name type)`, for the types after
;;; it to select from (`first-class-modules.md`, M5): in its type, `(select
;;; $k t)`, the `k`th parameter's type `t`.

;; Its types, those it uses of the files before it, and the signatures of
;; what it is given.
(let* ((check-dependent-types (load-module "fx26:check-dependent-types.fx"))
       (check-types-types (load-module "fx26:check-types-types.fx"))
       (check-env-types (load-module "fx26:check-env-types.fx"))
       (check-holds-types (load-module "fx26:check-holds-types.fx"))
       (parser-types ((proj (load-module "fx26:parser-types.fx") @s @e @m @c @p)))
       (check-modules-types (load-module "fx26:check-modules-types.fx"))
       (check-read-descs-types (load-module "fx26:check-read-descs-types.fx"))
       (check-expect-types (load-module "fx26:check-expect-types.fx"))
       (check-subst-types (load-module "fx26:check-subst-types.fx")))
  ;; What it is given: the modules of the files before it that it uses.
  (lambda ((check-types (select check-types-types check-types-sig))
           (check-env (select check-env-types check-env-sig))
           (check-modules (select check-modules-types check-modules-sig))
           (check-read-descs (select check-read-descs-types check-read-descs-sig))
           (check-expect (select check-expect-types check-expect-sig))
           (check-holds (select check-holds-types check-holds-sig))
           (check-subst (select check-subst-types check-subst-sig)))
    (module
(define-type k-given-back (select check-dependent-types k-given-back))
(define-type k-dependent (select check-dependent-types k-dependent))
(define-type k-callables (select check-dependent-types k-callables))
;; The types it uses of the files before it.
(define-effect checks (select check-types-types checks))
(define dt (with check-types-types dt))
(define-type k-desc (select check-types-types k-desc))
(define-type k-ids (select check-types-types k-ids))
(define-type k-map (select check-types-types k-map))
(define-type k-names (select check-types-types k-names))
(define-type k-parts (select check-types-types k-parts))
(define-effect kreads (select check-types-types kreads))
(define-effect kstate (select check-types-types kstate))
(define-type kxs (select check-types-types kxs))
(define ty-module (with check-types-types ty-module))
(define ty-param (with check-types-types ty-param))
(define ty-var (with check-types-types ty-var))
(define x-var (with check-types-types x-var))
(define-type k-bindings (select check-env-types k-bindings))
(define-type k-params-given (select check-env-types k-params-given))
(define-type k-seen (select check-holds-types k-seen))
(define-type names (select parser-types names))
;; What it uses of the modules it is given.
(define k-cat3 (with check-types k-cat3))
(define k-cat5 (with check-types k-cat5))
(define k-fail (with check-types k-fail))
(define k-get (with check-types k-get))
(define k-length (with check-types k-length))
(define k-nth (with check-types k-nth))
(define k-resolve (with check-types k-resolve))
(define k-ty-new (with check-types k-ty-new))
(define k-bind (with check-env k-bind))
(define k-lookup (with check-env k-lookup))
(define k-param-in (with check-env k-param-in))
(define k-param-map (with check-env k-param-map))
(define k-binding-names (with check-modules k-binding-names))
(define k-check-apps-each (with check-modules k-check-apps-each))
(define k-resolve-outside (with check-modules k-resolve-outside))
(define k-ids-then (with check-read-descs k-ids-then))
(define k-ty-kids (with check-read-descs k-ty-kids))
(define k-name-nat (with check-expect k-name-nat))
(define k-new-seen (with check-holds k-new-seen))
(define k-seen? (with check-holds k-seen?))
(define k-subst (with check-subst k-subst))

;; `t` with each `(select $k n)` what `given` says it is.
(define k-instantiate-params (subr (maxeff kstate spin) (int k-params-given) int)
  (lambda (t given)
    (if (null? given)
        t
        (let ((outer (get k-param-map)))
          (begin (set k-param-map given)
                 (let ((r (k-subst t nil))) (begin (set k-param-map outer) r)))))))
(define k-abs-given (subr (maxeff kstate spin) (int k-parts k-params-given k-map) k-given-back)
  (lambda (j abs given back)
    (if (null? abs)
        (product (1 given) (2 back))
        (let* ((a (extract (car abs) 1)) (w (extract (car abs) 2))
               (g (product (1 j) (2 a) (3 (k-ty-new (ty-var w)))))
               (bk (the (pairof int k-desc @t) (cons w (dt (k-ty-new (ty-param j a)))))))
          (k-abs-given j (cdr abs) (the k-params-given (cons g given))
                       (the k-map (cons bk back)))))))
;; Parameters `typed`, from the `j`th, bound in order, at `a`..`b`: a
;; parameter's type may name a module in scope, or an earlier parameter.
;; What it names of an earlier one is, in the procedure's type, `(select $k
;; t)`; a type told it says it so, and is given the earlier parameter's.
(define k-bind-dependent
  (subr (maxeff checks spin) (k-bindings k-names int k-params-given k-map int int) k-dependent)
  (lambda (typed names j given back a b)
    (if (null? typed)
        (product (1 (the k-bindings nil)) (2 given) (3 back))
        (let* ((n (car (car typed)))
               (outside (k-resolve-outside (cdr (car typed)) names a b))
               (resolved (k-instantiate-params outside given))
               (bound (k-name-nat n resolved))
               (pushed (k-bind n bound))
               (t (if (null? back) resolved (k-subst resolved back)))
               (gb (tagcase (k-get bound)
                     (ty-module (abs ds vs) (k-abs-given j abs given back))
                     (else y (product (1 given) (2 back)))))
               (rest (k-bind-dependent (cdr typed) (cdr names) (+ j 1)
                                       (extract gb 1) (extract gb 2) a b)))
          (product (1 (the k-bindings (cons (cons n t) (extract rest 1))))
                   (2 (extract rest 2)) (3 (extract rest 3)))))))
;; A `lambda`'s parameters `typed`, at `a`..`b`, bound so.
(define k-bind-params (subr (maxeff checks spin) (k-bindings int int) k-dependent)
  (lambda (typed a b) (k-bind-dependent typed (k-binding-names typed) 0 nil nil a b)))
;; A lambda's result type `t`, as the procedure's type says it.
(define k-result-back (subr (maxeff kstate spin) (int k-map) int)
  (lambda (t back) (if (null? back) t (k-subst t back))))

(define k-abs-types (subr (maxeff kstate spin) (k-parts k-parts) k-parts)
  (lambda (abs ds)
    (if (null? abs)
        ds
        (cons (product (1 (extract (car abs) 1)) (2 (k-ty-new (ty-var (extract (car abs) 2)))))
              (k-abs-types (cdr abs) ds)))))
;; A module-typed binding's types, by component name: each abstract type as
;; named for the binding, then each transparent one.
(define k-module-types (subr (maxeff kstate spin) (int) k-parts)
  (lambda (mt)
    (tagcase (k-get mt)
      (ty-module (abs ds vs) (k-abs-types abs ds))
      (else y nil))))
;; Each `(select $k x)` in `t`, as first met, onto `out`.
(define-rec
  (k-param-sels-from (subr (maxeff kstate spin) (int k-seen (ref k-params-given @t)) unit)
    (lambda (t seen out)
      (let ((t (k-resolve t)))
        (if (k-seen? seen t)
            #u
            (begin
              (tagcase (k-get t)
                (ty-param (k x)
                  (if (>= (k-param-in (get out) k x -1) 0)
                      #u
                      (set out (cons (product (1 k) (2 x) (3 t)) (get out)))))
                (else y (k-param-sels-each (k-ty-kids t) seen out))))))))
  (k-param-sels-each (subr (maxeff kstate spin) (k-ids k-seen (ref k-params-given @t)) unit)
    (lambda (ts seen out)
      (if (null? ts)
          #u
          (begin (k-param-sels-from (car ts) seen out) (k-param-sels-each (cdr ts) seen out))))))
;; `ps` reversed, onto `acc`.
(define k-given-reversed
  (subr (maxeff (read @globals) (alloc @t) spin) (k-params-given k-params-given) k-params-given)
  (lambda (ps acc) (if (null? ps) acc (k-given-reversed (cdr ps) (cons (car ps) acc)))))
;; What an argument a procedure's types depend on, not a name, says.
(define k-by-name string
  (string-append " is a module the procedure's types depend on: "
                 "give it by name (bind it with `let` first)"))
(define k-part-of-types (subr (maxeff kreads spin) (k-parts symbol) int)
  (lambda (ps n)
    (cond ((null? ps) -1)
          ((symbol=? (extract (car ps) 1) n) (extract (car ps) 2))
          (else (k-part-of-types (cdr ps) n)))))
;; What each `(select $k x)` of `found` is for a call with `args`, at
;; `a`..`b`: the type `x` of the module the `k`th argument names, by name.
(define k-args-given (subr (maxeff checks spin) (k-params-given kxs int int) k-params-given)
  (lambda (found args a b)
    (if (null? found)
        nil
        (let* ((k (extract (car found) 1)) (x (extract (car found) 2))
               (arg (if (< k (k-length args)) (the kxs (cons (k-nth args k) nil)) (the kxs nil)))
               (v (if (null? arg) '|| (tagcase (car arg) (x-var (v va vb) v) (else z '||))))
               (mt (if (symbol=? v '||) -1 (k-lookup v)))
               (to (if (< mt 0)
                       (k-fail (k-cat3 "argument " (int->string (+ k 1)) k-by-name) a b)
                       (let ((t (k-part-of-types (k-module-types mt) x)))
                         (if (< t 0)
                             (k-fail (k-cat5 "`" (symbol->string v) "` has no type `"
                                             (symbol->string x) "`")
                                     a b)
                             t))))
               (rest (k-args-given (cdr found) args a b)))
          (cons (product (1 k) (2 x) (3 to)) rest)))))
(define k-instantiate-all (subr (maxeff kstate spin) (k-ids k-params-given) k-ids)
  (lambda (ts given)
    (if (null? ts)
        nil
        (let ((t (k-instantiate-params (car ts) given)))
          (cons t (k-instantiate-all (cdr ts) given))))))
(define k-dependent-callee (subr (maxeff checks spin) (k-callables kxs int int) k-callables)
  (lambda (c args a b)
    (if (null? c)
        c
        (let* ((ps (extract (car c) 2)) (r (extract (car c) 3))
               (out (the (ref k-params-given @t) (new nil)))
               (seen (k-new-seen))
               (walked (begin (k-param-sels-each ps seen out) (k-param-sels-from r seen out))))
          (if (null? (get out))
              c
              (let* ((given (k-args-given (k-given-reversed (get out) nil) args a b))
                     (ps2 (k-instantiate-all ps given))
                     (r2 (k-instantiate-params r given)))
                (begin (k-check-apps-each (k-ids-then ps2 r2) (k-new-seen) a b)
                       (cons (product (1 (extract (car c) 1)) (2 ps2) (3 r2)) nil)))))))))))
