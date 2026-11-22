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
       (check-read-helpers-types (load-module "fx26:check-read-helpers-types.fx"))
       (check-expect-types (load-module "fx26:check-expect-types.fx"))
       (check-subst-types (load-module "fx26:check-subst-types.fx")))
  ;; What it is given: the modules of the files before it that it uses.
  (lambda ((check-types (select check-types-types check-types-sig))
           (check-env (select check-env-types check-env-sig))
           (check-modules (select check-modules-types check-modules-sig))
           (check-read-descs (select check-read-descs-types check-read-descs-sig))
           (check-expect (select check-expect-types check-expect-sig))
           (check-holds (select check-holds-types check-holds-sig))
           (check-subst (select check-subst-types check-subst-sig))
           (check-read-helpers (select check-read-helpers-types check-read-helpers-sig)))
    (module
(hide (include check-dependent-types) (include check-types-types) (include check-env-types)
      (include check-holds-types) (include parser-types))
;; The types it uses of the files before it.
;; What it uses of the modules it is given: all of each, hidden.
(hide (include check-types) (include check-env) (include check-modules)
      (include check-read-helpers) (include check-expect) (include check-holds)
      (include check-subst))

;; `t` with each `(select $k n)` what `given` says it is.
(define k-instantiate-params (->* (int k-paths-given) int)
  (lambda (t given)
    (if (null? given)
        t
        (let ((outer (get k-param-map)))
          (begin (set k-param-map given)
                 (let ((r (k-subst t nil))) (begin (set k-param-map outer) r)))))))
(define k-abs-given (->* (int k-parts k-paths-given k-map) k-given-back)
  (lambda (j abs given back)
    (if (null? abs)
        (product (1 given) (2 back))
        (let* ((a (extract (car abs) 1)) (w (extract (car abs) 2))
               (g (product (1 j) (2 a) (3 (the k-names nil)) (4 (k-ty-new (ty-var w)))))
               (bk (the (pairof int k-desc @t) (cons w (dt (k-ty-new (ty-param j a nil)))))))
          (k-abs-given j (cdr abs) (the k-paths-given (cons g given))
                       (the k-map (cons bk back)))))))
;; Of a dependent procedure's module parameters, each `k`th's binding's anchor
;; (`anchors`), the abstract types of each path from it read so far,
;; `env.m-base..t`, onto `gb`: as the procedure's type says them, `(select
;; (with $k m-base) t)`, onto its map back; as the body has them, onto what is
;; given. So a parameter of a dependent module type, whose abstract types are
;; its members', gives them as one whose own they are does. As the Rust
;; checker's `params_paths_back`.
(define k-paths-back (->* (k-param-anchors k-given-back) k-given-back)
  (lambda (anchors gb)
    (if (null? anchors) gb (k-paths-back-in (get k-module-paths) anchors gb))))
(define k-paths-back-in (->* (k-anchor-paths k-param-anchors k-given-back) k-given-back)
  (lambda (ps anchors gb)
    (if (null? ps)
        gb
        (let ((j (k-anchor-param anchors (extract (car ps) 1))) (e (car ps)))
          (k-paths-back-in (cdr ps) anchors
                           (if (< j 0) gb (k-path-parts-back j (extract e 4) (extract e 3) gb)))))))
(define k-anchor-param (->* (k-param-anchors int) int)
  (lambda (as v)
    (cond ((null? as) -1)
          ((= (extract (car as) 2) v) (extract (car as) 1))
          (else (k-anchor-param (cdr as) v)))))
(define k-path-parts-back (->* (int k-names k-parts k-given-back) k-given-back)
  (lambda (j path made gb)
    (if (null? made)
        gb
        (let ((a (extract (car made) 1)) (w (extract (car made) 2)))
          (k-path-parts-back
            j path (cdr made)
            (if (k-map-has? (extract gb 2) w)
                gb
                (let* ((g (product (1 j) (2 a) (3 path) (4 (k-ty-new (ty-var w)))))
                       (sel (k-ty-new (ty-param j a path)))
                       (bk (the (pairof int k-desc @t)
                                (cons w (if (= (k-dvar-kind w) 2) (dt sel) (df sel))))))
                  (product (1 (the k-paths-given (cons g (extract gb 1))))
                           (2 (the k-map (cons bk (extract gb 2))))))))))))
(define k-map-has? (->* (k-map int) bool)
  (lambda (m v) (and (not (null? m)) (or (= (car (car m)) v) (k-map-has? (cdr m) v)))))
;; Parameters `typed`, from the `j`th, bound in order, at `a`..`b`: a
;; parameter's type may name a module in scope, or an earlier parameter.
;; What it names of an earlier one is, in the procedure's type, `(select $k
;; t)`, or of a path from it, `(select (with $k m) t)` (`k-paths-back`); a
;; type told it says it so, and is given the earlier parameter's.
(define k-bind-dependent
  (->* (k-bindings k-names int k-given-back k-param-anchors int int) k-dependent)
  (lambda (typed names j gb0 anchors a b)
    (if (null? typed)
        (let ((gb (k-paths-back anchors gb0)))
          (product (1 (the k-bindings nil)) (2 (extract gb 1))
                   (3 (product (1 (extract gb 2)) (2 anchors)))))
        (let* ((n (car (car typed)))
               (outside (k-resolve-outside (cdr (car typed)) names a b))
               (resolved (k-instantiate-params outside (extract gb0 1)))
               (bound (k-name-nat n resolved))
               (pushed (k-bind n bound))
               (gb1 (k-paths-back anchors gb0))
               (given (extract gb1 1)) (back (extract gb1 2))
               (t (if (null? back) resolved (k-subst resolved back)))
               (gb (tagcase (k-get bound)
                     (ty-module (abs ds vs) (k-abs-given j abs given back))
                     (else y gb1)))
               (an (k-anchor-of bound))
               (anchors2 (if (null? an)
                             anchors
                             (append anchors (list (product (1 j) (2 (extract (car an) 2)))))))
               (rest (k-bind-dependent (cdr typed) (cdr names) (+ j 1) gb anchors2 a b)))
          (product (1 (the k-bindings (cons (cons n t) (extract rest 1))))
                   (2 (extract rest 2)) (3 (extract rest 3)))))))
;; A `lambda`'s parameters `typed`, at `a`..`b`, bound so.
(define k-bind-params (->* (k-bindings int int) k-dependent)
  (lambda (typed a b)
    (k-bind-dependent typed (k-binding-names typed) 0
                      (product (1 (the k-paths-given nil)) (2 (the k-map nil))) nil a b)))
;; A lambda's result type `t`, as the procedure's type says it: a path's from
;; a parameter too, read in the body.
(define k-result-back (->* (int k-backs) int)
  (lambda (t bs)
    (let ((back (extract (k-paths-back (extract bs 2)
                                       (product (1 (the k-paths-given nil)) (2 (extract bs 1))))
                         2)))
      (if (null? back) t (k-subst t back)))))

(define k-abs-types (->* (k-parts k-parts) k-parts)
  (lambda (abs ds)
    (if (null? abs)
        ds
        (cons (product (1 (extract (car abs) 1)) (2 (k-ty-new (ty-var (extract (car abs) 2)))))
              (k-abs-types (cdr abs) ds)))))
;; A module-typed binding's types, by component name: each abstract type as
;; named for the binding, then each transparent one.
(define k-module-types (->* (int) k-parts)
  (lambda (mt)
    (tagcase (k-get mt)
      (ty-module (abs ds vs) (k-abs-types abs ds))
      (else y nil))))
;; Each `(select $k x)` in `t`, as first met, onto `out`.
(define-rec
  (k-param-sels-from (->* (int k-seen (ref k-paths-given @t)) unit)
    (lambda (t seen out)
      (let ((t (k-resolve t)))
        (if (k-seen? seen t)
            #u
            (begin
              (tagcase (k-get t)
                (ty-param (k x p)
                  (if (>= (k-path-in (get out) k x p -1) 0)
                      #u
                      (set out (cons (product (1 k) (2 x) (3 p) (4 t)) (get out)))))
                (else y (k-param-sels-each (k-ty-kids t) seen out))))))))
  (k-param-sels-each (->* (k-ids k-seen (ref k-paths-given @t)) unit)
    (lambda (ts seen out)
      (if (null? ts)
          #u
          (begin (k-param-sels-from (car ts) seen out) (k-param-sels-each (cdr ts) seen out))))))
;; `ps` reversed, onto `acc`.
(define k-given-reversed
  (->* (k-paths-given k-paths-given) k-paths-given)
  (lambda (ps acc) (if (null? ps) acc (k-given-reversed (cdr ps) (cons (car ps) acc)))))
;; What an argument a procedure's types depend on, not a name, says.
(define k-by-name string
  (string-append " is a module the procedure's types depend on: "
                 "give it by name (bind it with `let` first)"))
;; What each `(select $k x)` of `found` is for a call with `args`, at
;; `a`..`b`: the type `x` of the module the `k`th argument names, by name; of
;; `(select (with $k m …) x)`, of the module the path from it reaches, as
;; `(with v m)` reads it, its abstract types the path's from `v`'s binding.
(define k-args-given (->* (k-paths-given kxs int int) k-paths-given)
  (lambda (found args a b)
    (if (null? found)
        nil
        (let* ((k (extract (car found) 1)) (x (extract (car found) 2)) (p (extract (car found) 3))
               (arg (if (< k (k-length args)) (the kxs (cons (k-nth args k) nil)) (the kxs nil)))
               (v
                (if (null? arg) '||
                    (tagcase (car arg) (x-var (v va vb vavbk vavbkr) v) (else z '||))))
               (mt (if (symbol=? v '||) -1 (k-lookup v)))
               (to (if (< mt 0)
                       (k-fail (k-cat3 "argument " (int->string (+ k 1)) k-by-name) a b)
                       (let* ((m (if (null? p) mt (k-member-path-type v p)))
                              (t (if (< m 0) -1 (k-part-find (k-module-types m) x))))
                         (if (< t 0)
                             (k-fail (k-cat5 "`" (k-with-path (symbol->string v) p)
                                             "` has no type `" (symbol->string x) "`")
                                     a b)
                             t))))
               (rest (k-args-given (cdr found) args a b)))
          (cons (product (1 k) (2 x) (3 p) (4 to)) rest)))))
;; The module type the path `p` of members from module variable `v` reaches,
;; as `(with (with v a) b)` reads it (`k-component`); -1 if none. As the Rust
;; checker's `member_path_type`.
(define k-member-path-type (->* (symbol k-names) int)
  (lambda (v p) (k-member-path-from (k-module-path-base v) p)))
(define k-member-path-from (->* (k-path-at k-names) int)
  (lambda (q p)
    (cond ((< (extract q 1) 0) -1)
          ((null? p) (extract q 1))
          (else (k-member-path-from (k-component q (car p)) (cdr p))))))
(define k-instantiate-all (->* (k-ids k-paths-given) k-ids)
  (lambda (ts given)
    (if (null? ts)
        nil
        (let ((t (k-instantiate-params (car ts) given)))
          (cons t (k-instantiate-all (cdr ts) given))))))
(define k-dependent-callee (->* (k-callables kxs int int) k-callables)
  (lambda (c args a b)
    (if (null? c)
        c
        (let* ((ps (extract (car c) 2)) (r (extract (car c) 3))
               (out (the (ref k-paths-given @t) (new nil)))
               (seen (k-new-seen))
               (walked (begin (k-param-sels-each ps seen out) (k-param-sels-from r seen out)
                              (k-seen-done! seen))))
          (if (null? (get out))
              c
              (let* ((given (k-args-given (k-given-reversed (get out) nil) args a b))
                     (ps2 (k-instantiate-all ps given))
                     (r2 (k-instantiate-params r given)))
                (begin (let ((seen2 (k-new-seen)))
                         (begin (k-check-apps-each (k-ids-then ps2 r2) seen2 a b)
                                (k-seen-done! seen2)))
                       (cons (product (1 (extract (car c) 1)) (2 ps2) (3 r2)) nil)))))))))))
