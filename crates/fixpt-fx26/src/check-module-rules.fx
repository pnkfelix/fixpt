;;; The checker, in FX-26: first-class modules' rules
;;; (`docs/research/first-class-modules.md`, stage M2): `module` and `with`,
;;; module types compared, and what the termination check sees in them. The
;;; Rust checker's `modules.rs`, rule for rule; `check-modules.fx` reads and
;;; names. Part of the checker, `check-types.fx` first.

;;; ------------------------------------------------------------ module

;; What a module's items make, its abstract types, descriptions and values
;; (each newest first), and the effect of making them.
(define-type k-made (productof (1 k-parts) (2 k-parts) (3 k-parts) (4 k-eff)))
(define k-made-of (subr (alloc @t) (k-parts k-parts k-parts k-eff) k-made)
  (lambda (abs ds vs e) (product (1 abs) (2 ds) (3 vs) (4 e))))
;; An abstract type `t`, its representation seen only through its own
;; conversions, which stay inside the module: each the identity, made as a
;; closure is, checked on its representation and bound at `t`. A type
;; constructor's representation is a `dlambda` of its parameters: its
;; conversions are polymorphic in them, as FX-91's at a higher kind.
(define k-module-abs (subr (maxeff checks spin) (k-item int int k-made) k-made)
  (lambda (it a b made)
    (let* ((n (car (extract it 2)))
           (v (extract it 3))
           (whole (car (extract it 4)))
           (bs (tagcase (k-get whole) (ty-lam (bs body) bs) (else x (the k-binders nil))))
           (inner (tagcase (k-get whole)
                    (ty-lam (bs body) (tagcase body (dt (t) t) (else x whole)))
                    (else x whole)))
           (rep (k-resolve-selects inner a b))
           (var (k-ty-new (ty-var v)))
           (t (if (null? bs) var (k-ty-new (ty-app var (k-binders-as-descs bs)))))
           (identity (k-new-subr nil (the k-ids (cons rep nil)) rep))
           (fns (extract it 5))
           (up (k-check (car fns) identity))
           (down (k-check (car (cdr fns)) identity))
           (up-t (k-new-subr nil (the k-ids (cons rep nil)) t))
           (down-t (k-new-subr nil (the k-ids (cons t nil)) rep)))
      (begin
        (k-bind (k-conversion-name "up-" n) (if (null? bs) up-t (k-ty-new (ty-poly bs up-t))))
        (k-bind (k-conversion-name "down-" n)
                (if (null? bs) down-t (k-ty-new (ty-poly bs down-t))))
        (k-made-of (k-part-onto n v (extract made 1)) (extract made 2) (extract made 3)
                   (extract made 4))))))
;; A value: checked against its type, if it has one, or found; bound, its
;; sizes and abstract types named for it, for the items after it.
(define k-module-val (subr (maxeff checks spin) (k-item int int k-made) k-made)
  (lambda (it a b made)
    (let* ((n (car (extract it 2)))
           (ts (extract it 4))
           (init (car (extract it 5)))
           (r (if (null? ts)
                  (k-synth init)
                  (let ((t (k-resolve-selects (car ts) a b))) (k-te t (k-check init t)))))
           (bound (k-bind n (k-name-nat n (extract r 1)))))
      (k-made-of (extract made 1) (extract made 2) (k-part-onto n (extract r 1) (extract made 3))
                 (k-union (extract made 4) (extract r 2))))))
;; A group's bindings, each type resolved at `a`..`b` in turn.
(define k-group-bindings (subr (maxeff checks spin) (k-names k-ids kxs int int) k-letrec-bs)
  (lambda (ns ts xs a b)
    (if (null? ns)
        nil
        (let* ((t (k-resolve-selects (car ts) a b))
               (rest (k-group-bindings (cdr ns) (cdr ts) (cdr xs) a b)))
          (cons (product (1 (car ns)) (2 t) (3 (car xs))) rest)))))
;; Every one of `bs` a `lambda`, or an error at the first that is not.
(define k-group-lambdas (subr checks (k-letrec-bs) unit)
  (lambda (bs)
    (cond ((null? bs) #u)
          ((k-lambda? (extract (car bs) 3)) (k-group-lambdas (cdr bs)))
          (else (k-fail-at (k-cat3 "`" (symbol->string (extract (car bs) 1))
                                   "`, in a `define-rec`, is a `lambda`")
                           (extract (car bs) 3))))))
(define k-parts-of-group (subr (maxeff (read @globals) (alloc @t)) (k-letrec-bs k-parts) k-parts)
  (lambda (bs ps)
    (if (null? bs)
        ps
        (k-parts-of-group (cdr bs) (k-part-onto (extract (car bs) 1) (extract (car bs) 2) ps)))))
;; `(define-rec (f T e) …)`: every name in scope first, known; then each
;; `lambda` checked against its type, a group whose every run ends needing
;; no `spin`.
(define k-module-group (subr (maxeff checks spin) (k-item int int k-made) k-made)
  (lambda (it a b made)
    (let* ((bs (k-group-bindings (extract it 2) (extract it 4) (extract it 5) a b))
           (rsaved (get k-recursive))
           (bound (k-bind-letrec bs))
           (lambdas (k-group-lambdas bs))
           (noted (k-note-ending bs (k-termination bs)))
           (e (k-check-letrec bs))
           (restored (set k-recursive rsaved)))
      (k-made-of (extract made 1) (extract made 2) (k-parts-of-group bs (extract made 3))
                 (k-union (extract made 4) e)))))
;; Items `items`, each in the scope of those before it.
(define k-module-items (subr (maxeff checks spin) (k-items int int k-made) k-made)
  (lambda (items a b made)
    (if (null? items)
        made
        (let* ((it (car items))
               (k (extract it 1))
               (next (cond
                       ((= k 0) (k-module-abs it a b made))
                       ((or (< k 0) (> k 3)) made)
                       ((= k 1)
                        (let ((t (k-resolve-selects (car (extract it 4)) a b)))
                          (k-made-of (extract made 1)
                                     (k-part-onto (car (extract it 2)) t (extract made 2))
                                     (extract made 3) (extract made 4))))
                       ((= k 2) (k-module-val it a b made))
                       (else (k-module-group it a b made)))))
          (k-module-items (cdr items) a b next)))))
;; Each value's type, `vs`, mentions none of `inner`, the sizes and abstract
;; types named inside the module; or an error at `a`..`b`.
(define k-vals-known (subr (maxeff checks spin) (k-parts k-ids int int) unit)
  (lambda (vs inner a b)
    (if (null? vs)
        #u
        (let ((v (k-first-mentioned (extract (car vs) 2) inner)))
          (if (< v 0)
              (k-vals-known (cdr vs) inner a b)
              (k-fail (k-cat5 "`" (symbol->string (extract (car vs) 1)) "`'s type mentions `"
                              (k-dvar-string v) "`, which is not known outside the module")
                      a b))))))
;; `(module item …)`: each item checked in the scope of those before it;
;; the module's type, its abstract types bound in it.
(define k-synth-module-here (subr (maxeff checks spin) (kx k-items int int) k-te)
  (lambda (x items a b)
    (let* ((saved (k-mark))
           (named (get k-skolems))
           (made (k-module-items items a b (k-made-of nil nil nil nil)))
           (unbound (k-unbind-to saved))
           (vs (k-parts-reversed (extract made 3) nil))
           ;; A component's module, bound inside, has abstract types no one
           ;; outside can name.
           (known (k-vals-known vs (k-named-since named (get k-skolems) nil) a b))
           (popped (set k-skolems named))
           (abs (k-parts-reversed (extract made 1) nil))
           (t (k-ty-new (ty-module abs (k-parts-reversed (extract made 2) nil) vs))))
      (k-te-masked x t (extract made 4)))))
;; The same; a module read from a file (`load-module`, M7) seeing only the
;; standard environment, what is wrong in it said where it is read.
(define k-synth-module (subr (maxeff checks spin) (kx k-items int int) k-te)
  (lambda (x items a b)
    (let ((k (if (null? items) 0 (extract (car items) 1))))
      (if (< k 4)
          (k-synth-module-here x items a b)
          (let ((got (the (ref k-te @t) (new (k-te 0 nil)))) (hid (get k-hide-mark)))
            (begin (set k-hide-mark (k-mark))
                   (k-in-loaded (lambda () (set got (k-synth-module-here x items a b))) k a b)
                   (set k-hide-mark hid)
                   (get got)))))))

;;; ------------------------------------------------------------ with

;; The names of parts `ps`.
(define k-comp-names (subr (maxeff (read @globals) (alloc @t)) (k-parts) k-names)
  (lambda (ps) (if (null? ps) nil (cons (extract (car ps) 1) (k-comp-names (cdr ps))))))
;; Each of `ps` bound, the first first.
(define k-bind-parts (subr (maxeff kstate spin) (k-parts) unit)
  (lambda (ps)
    (if (null? ps)
        #u
        (begin (k-bind (extract (car ps) 1) (extract (car ps) 2)) (k-bind-parts (cdr ps))))))
;; `(with m body)`: the body with `m`'s values in scope, by name, at their
;; types for `m`.
(define k-synth-with (subr (maxeff checks spin) (kx symbol kx int int) k-te)
  (lambda (x m body a b)
    (let ((mt (k-lookup m)) (shown (symbol->string m)))
      (if (< mt 0)
          (k-fail (k-cat3 "`" shown "` is not bound") a b)
          (tagcase (k-get mt)
            (ty-module (abs ds vs)
              (let* ((noted (set k-with-vals (cons (product (1 a) (2 b) (3 (k-comp-names vs)))
                                                   (get k-with-vals))))
                     (naming (k-naming-effect m mt))
                     (saved (k-mark))
                     (bound (k-bind-parts vs))
                     (r (k-synth body))
                     (unbound (k-unbind-to saved)))
                (k-te-masked x (extract r 1) (k-union naming (extract r 2)))))
            (else y
              (let ((what (k-show-ty mt)))
                (k-fail (k-cat4 "`with` opens a module, and `" shown "` is a " what) a b))))))))

(define k-module-rule (subr (maxeff checks spin) (kx) k-te)
  (lambda (x)
    (tagcase x
      (x-module (items a b) (k-synth-module x items a b))
      (x-with (m body a b) (k-synth-with x m body a b))
      (else y (k-fail-at "a module" x)))))
(set k-module-rules k-module-rule)

;;; ------------------------------------------------------------ subtyping

;; The type part `n` of `ps` is, or -1.
(define k-part-of (subr (maxeff kreads spin) (k-parts symbol) int)
  (lambda (ps n)
    (cond ((null? ps) -1)
          ((symbol=? (extract (car ps) 1) n) (extract (car ps) 2))
          (else (k-part-of (cdr ps) n)))))
;; Whether a name of `xs` is one of `ys`'s.
(define k-comps-meet? (subr (maxeff kreads spin) (k-parts k-parts) bool)
  (lambda (xs ys)
    (and (not (null? xs))
         (or (>= (k-part-of ys (extract (car xs) 1)) 0) (k-comps-meet? (cdr xs) ys)))))
;; Whether `xs` and `ys` are values of the same names, in order.
(define k-same-names? (subr (maxeff kreads spin) (k-parts k-parts) bool)
  (lambda (xs ys)
    (if (null? xs)
        (null? ys)
        (and (not (null? ys))
             (symbol=? (extract (car xs) 1) (extract (car ys) 1))
             (k-same-names? (cdr xs) (cdr ys))))))
;; Each abstract type of `ab` (from position `i`) paired with `aa`'s of its
;; name, as a `poly`'s binders are, in the environments `es`; or met by a
;; description of `da`'s. None, if one is neither.
(define k-pair-abs
  (subr (maxeff kstate spin) (k-parts k-parts k-parts int int int k-benvs k-labels)
        (listof k-benvs acyclic))
  (lambda (ab aa da a b i es labels)
    (if (null? ab)
        (the (listof k-benvs acyclic) (cons es nil))
        (let* ((n (extract (car ab) 1)) (x (k-part-of aa n)))
          (cond
            ((and (>= x 0) (not (= (k-dvar-kind x) (k-dvar-kind (extract (car ab) 2))))) nil)
            ((>= x 0)
             (let* ((l (k-label labels a b i))
                    (ea (k-benv-set (car es) x l))
                    (eb (k-benv-set (cdr es) (extract (car ab) 2) l)))
               (k-pair-abs (cdr ab) aa da a b (+ i 1) (the k-benvs (cons ea eb)) labels)))
            ((>= (k-part-of da n) 0) (k-pair-abs (cdr ab) aa da a b (+ i 1) es labels))
            (else nil))))))
;; Type `t` as the description that stands for variable `v`: a function, if
;; `v` is of an arrow kind.
(define k-as-kind (subr kreads (int int) k-desc)
  (lambda (v t) (if (k-arrow-kind? (k-dvar-kind v)) (df t) (dt t))))
;; Each binder named in `ea`, as the type of the name its pair was given.
(define k-labels-map (subr (maxeff kstate spin) (k-benv) k-map)
  (lambda (ea)
    (if (null? ea)
        nil
        (let ((t (k-ty-new (ty-var (cdr (car ea))))))
          (the k-map (cons (cons (car (car ea)) (k-as-kind (car (car ea)) t))
                           (k-labels-map (cdr ea))))))))
;; `b`'s abstract types (`ab`) that `a` defines (`da`, not abstract in `aa`):
;; each as that definition, `m` naming `a`'s own abstract types in it.
(define k-defined-map (subr (maxeff kstate spin) (k-parts k-parts k-parts k-map) k-map)
  (lambda (ab aa da m)
    (if (null? ab)
        nil
        (let* ((n (extract (car ab) 1))
               (d (if (>= (k-part-of aa n) 0) -1 (k-part-of da n)))
               (rest (k-defined-map (cdr ab) aa da m)))
          (if (< d 0)
              rest
              (let ((y (extract (car ab) 2)))
                (the k-map (cons (cons y (k-as-kind y (k-subst d m))) rest))))))))
;; For the pair of module types `a` and `b`, met before in this question, the
;; wanted one's descriptions and values with its abstract types the given
;; one's transparent ones: made once, so that a recursive type meets the same
;; pair again, which the trail catches. Kept with the question's labels, at
;; position -1, as a module type of no abstract types.
(define k-module-memo (subr (maxeff kreads spin) (k-label-list int int) int)
  (lambda (ls a b)
    (cond ((null? ls) -1)
          ((k-label-of? (car ls) a b -1) (extract (car ls) 4))
          (else (k-module-memo (cdr ls) a b)))))
(define k-module-parts
  (subr (maxeff kstate spin) (int int k-parts k-parts k-parts k-parts k-parts k-benv k-labels) int)
  (lambda (a b aa da ab db vb ea labels)
    (let ((known (k-module-memo (get labels) a b)))
      (if (>= known 0)
          known
          (let* ((by (k-defined-map ab aa da (k-labels-map ea)))
                 (bd (k-subst-each db by))
                 (bv (k-subst-each vb by))
                 (t (k-ty-new (ty-module nil bd bv))))
            (begin (set labels (cons (product (1 a) (2 b) (3 -1) (4 t)) (get labels))) t))))))
;; Each description of `bd` one of `da`'s, the same.
(define k-descs-same?
  (subr (maxeff kstate spin) (k-parts k-parts k-benv k-benv k-strail k-labels) bool)
  (lambda (bd da ea eb trail labels)
    (or (null? bd)
        (let ((x (k-part-of da (extract (car bd) 1))))
          (and (>= x 0) (k-inv x (extract (car bd) 2) ea eb trail labels)
               (k-descs-same? (cdr bd) da ea eb trail labels))))))
;; Each value of `va` a subtype of `bv`'s, pairwise.
(define k-vals-sub?
  (subr (maxeff kstate spin) (k-parts k-parts k-benv k-benv k-strail k-labels) bool)
  (lambda (va bv ea eb trail labels)
    (or (null? va)
        (and (k-sub (extract (car va) 2) (extract (car bv) 2) ea eb trail labels)
             (k-vals-sub? (cdr va) (cdr bv) ea eb trail labels)))))
;; Module type `a` ≤ `b` (`first-class-modules.md`, M4): each abstract type
;; of `b`'s an abstract type of `a`'s (paired as a `poly`'s binders are) or
;; a transparent one (`b`'s abstract type is then what `a` says it is); each
;; description of `b`'s one of `a`'s, the same; and their values the same
;; names, in order, each `a`'s a subtype of `b`'s, since a module is a
;; product of its values. Fewer values, or another order, `k-expect` makes by
;; reshaping (`k-reshape`).
(define k-sub-modules k-sub-rule
  (lambda (a b ta tb ea eb trail labels)
    (tagcase ta
      ;; `(select $k x)`: only itself.
      (ty-param (k x) (tagcase tb (ty-param (j y) (and (= k j) (symbol=? x y))) (else z #f)))
      (ty-module (aa da va)
        (tagcase tb
          (ty-module (ab db vb)
            (and (not (k-comps-meet? aa db))
                 (k-same-names? va vb)
                 (let ((paired (k-pair-abs ab aa da a b 0 (the k-benvs (cons ea eb)) labels)))
                   (and (not (null? paired))
                        (let* ((ia (car (car paired))) (ib (cdr (car paired)))
                               (parts (k-module-parts a b aa da ab db vb ia labels)))
                          (tagcase (k-get parts)
                            (ty-module (none bd bv)
                              (and (k-descs-same? bd da ia ib trail labels)
                                   (k-vals-sub? va bv ia ib trail labels)))
                            (else z #f)))))))
          (else z #f)))
      (else z #f))))
(set k-sub-module k-sub-modules)

;; Where in `vs` the value named `n` first is, from `i`; or -1.
(define k-val-position (subr (maxeff kreads spin) (k-parts symbol int) int)
  (lambda (vs n i)
    (cond ((null? vs) -1)
          ((symbol=? (extract (car vs) 1) n) i)
          (else (k-val-position (cdr vs) n (+ i 1))))))
;; Each of `wanted`'s values' position in `vs`; none if one is not there.
(define k-positions (subr (maxeff kreads (alloc @t) spin) (k-parts k-parts) (listof k-ids acyclic))
  (lambda (wanted vs)
    (if (null? wanted)
        (the (listof k-ids acyclic) (cons (the k-ids nil) nil))
        (let ((k (k-val-position vs (extract (car wanted) 1) 0))
              (rest (k-positions (cdr wanted) vs)))
          (if (or (< k 0) (null? rest))
              nil
              (the (listof k-ids acyclic) (cons (the k-ids (cons k (car rest))) nil)))))))
;; Whether `at` is each position of `n`, in order, from `i`.
(define k-in-order? (subr (maxeff (read @globals) spin) (k-ids int int) bool)
  (lambda (at n i) (if (null? at) (= i n) (and (= (car at) i) (k-in-order? (cdr at) n (+ i 1))))))
;; The values of `vs` at positions `at`.
(define k-vals-at (subr (maxeff kreads (alloc @t) spin) (k-parts k-ids) k-parts)
  (lambda (vs at) (if (null? at) nil (cons (k-nth vs (car at)) (k-vals-at vs (cdr at))))))
;; A module of type `got` made one of type `want`, which has fewer of its
;; values or the same in another order: each of `want`'s values' position in
;; `got`, if `got`'s values so chosen fit `want`; none otherwise.
(define k-reshape (subr (maxeff kstate spin) (int int) (listof k-ids acyclic))
  (lambda (got want)
    (tagcase (k-get got)
      (ty-module (abs ds vs)
        (tagcase (k-get want)
          (ty-module (wa wd wanted)
            (let ((at (k-positions wanted vs)))
              (if (or (null? at) (k-in-order? (car at) (k-length vs) 0))
                  nil
                  (let ((t (k-ty-new (ty-module abs ds (k-vals-at vs (car at))))))
                    (if (k-subtype t want) at nil)))))
          (else z nil)))
      (else z nil))))
;; Where `x`, of type `got`, is wanted as a `want`: reshaped, if it may be,
;; and noted so (`k-reshapes`).
(define k-reshape-at (subr (maxeff checks spin) (kx int int) bool)
  (lambda (x got want)
    (let ((at (k-reshape got want)))
      (if (null? at)
          #f
          (begin (set k-reshapes (cons (product (1 (k-start x)) (2 (k-end x)) (3 (car at)))
                                       (get k-reshapes)))
                 #t)))))
(set k-reshape-hook k-reshape-at)

;;; ------------------------------------------------------------ termination

;; `sc` with `ns` hidden: bound, and none of the group's.
(define k-sc-hide-names (subr kstate (k-names k-tscope) k-tscope)
  (lambda (ns sc) (if (null? ns) sc (k-sc-hide-names (cdr ns) (k-sc-bind (car ns) nil sc)))))
;; A module's values made, each as any expression is.
(define k-sc-walk-items (subr (maxeff kstate spin) (k-items k-tscope k-guards) unit)
  (lambda (items sc gs)
    (if (null? items)
        #u
        (let* ((it (car items)) (k (extract it 1)) (ns (extract it 2)))
          (cond ((= k 0)
                 (let ((inner (k-sc-hide-names (k-conversions-onto (car ns) nil) sc)))
                   (k-sc-walk-items (cdr items) inner gs)))
                ((or (= k 1) (< k 0) (> k 3)) (k-sc-walk-items (cdr items) sc gs))
                ((= k 2)
                 (begin (k-sc-walk-list (extract it 5) sc gs)
                        (k-sc-walk-items (cdr items) (k-sc-hide-names ns sc) gs)))
                (else
                 (let ((inner (k-sc-hide-names ns sc)))
                   (begin (k-sc-walk-list (extract it 5) inner gs)
                          (k-sc-walk-items (cdr items) inner gs)))))))))
;; A module's values made, and a `with`'s module named, each as any
;; expression or variable is.
(define k-sc-walk-modular (subr (maxeff kstate spin) (kx k-tscope k-guards) unit)
  (lambda (x sc gs)
    (tagcase x
      (x-module (items a b) (k-sc-walk-items items sc gs))
      (x-with (m body a b)
        (let ((member (k-sc-member sc m)))
          (begin (if (>= member 0) (k-sc-escape member) #u)
                 (k-sc-walk body (k-sc-hide-names (k-with-names a b) sc) gs))))
      (else y #u))))
(set k-sc-walk-module k-sc-walk-modular)
