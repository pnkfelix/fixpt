;;; The FX-26 evaluator proper: the parser's trees, run. After
;;; `eval-values.fx` and `eval-prims.fx`.
;;;
;;; An environment is a list of each name and the cell that holds its value,
;;; newest first; a closure is a procedure of the host's, closing over the
;;; environment it was made in, globals included: a top-level form runs in
;;; the global environment as it stands then, so a second `define` of a name
;;; shadows the first, and code before it keeps the first, as the lowering
;;; to Scheme does (`lower::Globals`). Descriptions are not needed to run a
;;; program, so they are passed over.
;;; Made by the conductor (`conductor.fx`), of the evaluator's values and
;;; primitives, and the checker's environment and resolution.

;; Its types, and the signatures of what it is given (`eval-types.fx`).
(define eval-types (load-module "fx26:eval-types.fx"))
(define-effect stores (select eval-types stores))
(define-effect runs (select eval-types runs))
(define-effect evals (select eval-types evals))
(define-type val (select eval-types val))
(define-type vals (select eval-types vals))
(define-type vfields (select eval-types vfields))
(define-type vcell (select eval-types vcell))
(define-type env (select eval-types env))
(define-type eresult (select eval-types eresult))
(define-type ev-at (select eval-types ev-at))
(define-type ev-with-at (select eval-types ev-with-at))
(define-type vcells (select eval-types vcells))
(define o-product (with eval-types o-product))
(define o-sum (with eval-types o-sum))
(define ev-ok (with eval-types ev-ok))
(define ev-err (with eval-types ev-err))
;; What it is given: the evaluator's values and primitives, and the
;; checker's environment (`check-env.fx`) and resolution (`check-resolve.fx`).
(define-type eval-values-sig (select eval-types eval-values-sig))
(define-type eval-prims-sig (select eval-types eval-prims-sig))
;; The types of the trees it runs, and of what the checker says of them.
(define parser-types ((proj (load-module "fx26:parser-types.fx") @s @e @m @c @p)))
(define-type exp (select parser-types exp))
(define-type exp-list (select parser-types exp-list))
(define-type mod-items (select parser-types mod-items))
(define-type names (select parser-types names))
(define-type top (select parser-types top))
(define check-env-types (load-module "fx26:check-env-types.fx"))
(define-type k-reshape-list (select check-env-types k-reshape-list))
(define-type k-with-list (select check-env-types k-with-list))
(define-type check-env-sig (select check-env-types check-env-sig))
(define check-resolve-types (load-module "fx26:check-resolve-types.fx"))
(define-type exp-arms (select check-resolve-types exp-arms))
(define-type exp-let-bs (select check-resolve-types exp-let-bs))
(define-type exp-letrec-bs (select check-resolve-types exp-letrec-bs))
(define-type k-run (select check-resolve-types k-run))
(define-type check-resolve-sig (select check-resolve-types check-resolve-sig))
(define check-types-types (load-module "fx26:check-types-types.fx"))
(define-type k-ids (select check-types-types k-ids))
(define-type k-names (select check-types-types k-names))
(define check-subst-types (load-module "fx26:check-subst-types.fx"))
(define-type exp-params (select check-subst-types exp-params))

(define make
  (lambda ((values eval-values-sig) (prims eval-prims-sig)
           (env check-env-sig) (resolve check-resolve-sig))
    (module
;; What it uses of the modules it is given.
(define apply-val (with values apply-val))
(define apply1 (with values apply1))
(define as-bool (with values as-bool))
(define as-fields (with values as-fields))
(define as-other (with values as-other))
(define as-tag (with values as-tag))
(define efail (with values efail))
(define efail-expected (with values efail-expected))
(define eval-tag (with values eval-tag))
(define show-val (with values show-val))
(define the-unit (with values the-unit))
(define ev-bloblet (with prims ev-bloblet))
(define standard (with prims standard))
(define k-fx-module? (with env k-fx-module?))
(define k-reshapes (with env k-reshapes))
(define k-with-vals (with env k-with-vals))
(define exp-start (with resolve exp-start))
(define exp-end (with resolve exp-end))

;; The global environment, newest first.
(define genv (ref env @v) (new nil))

(define* cell (subr (alloc @v) (val) vcell) (lambda (v) (new v)))

;; `e` with `n` bound to a new cell holding `v`.
(define* extend (subr (alloc @v) (symbol val env) env)
  (lambda (n v e) (cons (cons n (cell v)) e)))

(define* lookup (subr (maxeff evals spin) (env symbol) val)
  (lambda (e name)
    (cond ((null? e) (standard name))
          ((symbol=? (car (car e)) name) (get (cdr (car e))))
          (else (lookup (cdr e) name)))))

(define* find-cell (subr (maxeff evals spin) (env symbol) vcell)
  (lambda (e n)
    (cond ((null? e) (efail "no such local"))
          ((symbol=? (car (car e)) n) (cdr (car e)))
          (else (find-cell (cdr e) n)))))

;; A closure's parameters, bound to its arguments.
(define* bind (subr (maxeff evals spin) (exp-params vals env) env)
  (lambda (ps xs e)
    (cond ((and (null? ps) (null? xs)) e)
          ((or (null? ps) (null? xs)) (efail "the wrong number of arguments"))
          (else (cons (cons (extract (car ps) 1) (cell (car xs))) (bind (cdr ps) (cdr xs) e))))))

(define* field-of (subr (maxeff evals spin) (val symbol) val)
  (lambda (p l)
    (letrec ((find (subr (maxeff evals spin) (vfields) val)
               (lambda (fs)
                 (cond ((null? fs) (efail "no such label"))
                       ((symbol=? (car (car fs)) l) (cdr (car fs)))
                       (else (find (cdr fs)))))))
      (find (as-fields p "a product")))))

;; An arm's names, bound to a product's fields in order.
(define* bind-fields (subr (maxeff evals spin) (names val env) env)
  (lambda (ns p e)
    (letrec ((go (subr evals (names vfields env) env)
               (lambda (ns fs e)
                 (cond ((and (null? ns) (null? fs)) e)
                       ((or (null? ns) (null? fs)) (efail "the wrong number of fields"))
                       (else (go (cdr ns) (cdr fs) (extend (car ns) (cdr (car fs)) e)))))))
      (go ns (as-fields p "a product") e))))

(define* nth-field (subr (maxeff evals spin) (vfields int) (pairof symbol val @v))
  (lambda (fs i)
    (cond ((null? fs) (efail "no such field"))
          ((= i 0) (car fs))
          (else (nth-field (cdr fs) (- i 1))))))

;; `fs` reversed, onto `acc`.
(define* reverse-fields (subr (maxeff (read @v) (alloc @v) spin) (vfields vfields) vfields)
  (lambda (fs acc) (if (null? fs) acc (reverse-fields (cdr fs) (cons (car fs) acc)))))

;; The modules to reshape (`k-reshapes`), as `run-checked` was given them.
(define ev-reshapes (ref k-reshape-list @v) (new nil))

(define* ev-reshape-in (subr (maxeff (alloc @v) spin) (k-reshape-list int int) ev-at)
  (lambda (rs a b)
    (cond ((null? rs) nil)
          ((and (= (extract (car rs) 1) a) (= (extract (car rs) 2) b))
           (the ev-at (cons (extract (car rs) 3) nil)))
          (else (ev-reshape-in (cdr rs) a b)))))

;; Each `with` the checker saw (`k-with-vals`), as `run-checked` was given
;; them: where it is, and the module's values its body names, with their
;; positions.
(define ev-withs (ref k-with-list @v) (new nil))

(define* ev-with-in (subr (maxeff (alloc @v) spin) (k-with-list int int) ev-with-at)
  (lambda (ws a b)
    (cond ((null? ws) nil)
          ((and (= (extract (car ws) 1) a) (= (extract (car ws) 2) b))
           (the ev-with-at (cons (product (1 (extract (car ws) 3)) (2 (extract (car ws) 4))) nil)))
          (else (ev-with-in (cdr ws) a b)))))

;; The fields of `fs` at positions `ks`, in order.
(define* pick-fields (subr (maxeff evals spin) (vfields k-ids) vfields)
  (lambda (fs ks) (if (null? ks) nil (cons (nth-field fs (car ks)) (pick-fields fs (cdr ks))))))

;; Module `v` as `at` (in a list of one) reshapes it: its values at those
;; positions; as it is, if none.
(define* reshape-val (subr (maxeff evals spin) (val ev-at) val)
  (lambda (v at)
    (if (null? at)
        v
        (let ((fs (as-fields v "a module")))
          (o-product (pick-fields fs (car at)))))))

;; `e` with each of module `m`'s values bound to its name, in order.
(define* bind-module (subr (maxeff evals spin) (val env) env)
  (lambda (m e)
    (letrec ((go (subr (maxeff (read @v) (alloc @v) spin) (vfields env) env)
               (lambda (fs e)
                 (if (null? fs) e (go (cdr fs) (extend (car (car fs)) (cdr (car fs)) e))))))
      (go (as-fields m "a module") e))))

;; Module `m`'s values at positions `ps`, bound in `e` by names `ns`.
(define* bind-module-at (subr (maxeff evals spin) (val k-names k-ids env) env)
  (lambda (m ns ps e)
    (let ((fs (as-fields m "a module")))
      (letrec ((go (subr (maxeff evals spin) (k-names k-ids env) env)
                 (lambda (ns ps e)
                   (if (or (null? ns) (null? ps))
                       e
                       (let ((v (cdr (nth-field fs (car ps)))))
                         (go (cdr ns) (cdr ps) (extend (car ns) v e)))))))
        (go ns ps e)))))

;; An abstract type `n`'s conversions' names.
(define* conversion-names (subr (read @globals) (string) names)
  (lambda (n)
    (the names (list (string->symbol (string-append "up-" n))
                     (string->symbol (string-append "down-" n))))))

;; The names a module's items define, in order.
(define* module-names (subr (maxeff (alloc @v) spin) (mod-items) names)
  (lambda (items)
    (if (null? items)
        nil
        (let* ((it (car items)) (k (extract it 1)) (ns (extract it 2))
               (rest (module-names (cdr items))))
          (case k ((0) (append (conversion-names (symbol->string (car ns))) rest))
                  ((2 3) (append ns rest))
                  (else rest))))))

;; Each of `ns` bound in `e`, holding #u.
(define* open-names (subr (maxeff (alloc @v) spin) (names env) env)
  (lambda (ns e) (if (null? ns) e (open-names (cdr ns) (extend (car ns) the-unit e)))))

;; The values of `ns`, in `e`, onto `vs`, newest first.
(define* rec-values (subr (maxeff evals spin) (names env vfields) vfields)
  (lambda (ns e vs)
    (if (null? ns)
        vs
        (rec-values (cdr ns) e (cons (cons (car ns) (get (find-cell e (car ns)))) vs)))))

;; A module's values, from `e`, onto `vs`, newest first: its definitions'.
(define* module-values (subr (maxeff evals spin) (mod-items env vfields) vfields)
  (lambda (items e vs)
    (if (null? items)
        vs
        (let ((k (extract (car items) 1)))
          (module-values (cdr items) e
                         (if (or (= k 2) (= k 3)) (rec-values (extract (car items) 2) e vs) vs))))))

(define* open-letrec (subr (maxeff (alloc @v) spin) (exp-letrec-bs env) env)
  (lambda (bs e) (if (null? bs) e (open-letrec (cdr bs) (extend (extract (car bs) 1) the-unit e)))))

(define-rec
  (eval-all (subr (maxeff evals spin) ((listof exp acyclic) env) vals)
    (lambda (es e)
      (if (null? es)
          nil
          (let ((v (eval (car es) e)))
            (cons v (eval-all (cdr es) e))))))
  (eval-begin (subr (maxeff evals spin) ((listof exp acyclic) env) val)
    (lambda (es e)
      (cond ((null? es) the-unit)
            ((null? (cdr es)) (eval (car es) e))
            (else (begin (eval (car es) e) (eval-begin (cdr es) e))))))
  ;; `x`'s value; a module reshaped where the checker said so
  ;; (`k-reshape-at`), a product of the values its type wanted, by position.
  ;; With none to reshape, `eval-node` is called last, so that the
  ;; program's tail calls are the evaluator's, and a loop runs in constant
  ;; space.
  (eval (subr (maxeff evals spin) (exp env) val)
    (lambda (x e)
      (let ((rs (get ev-reshapes)))
        (if (null? rs)
            (eval-node x e)
            (reshape-val (eval-node x e) (ev-reshape-in rs (exp-start x) (exp-end x)))))))
  (eval-node (subr (maxeff evals spin) (exp env) val)
    (lambda (x e)
      (tagcase x
        (e-var (n a b) (lookup e n))
        (e-int (n a b) n)
        (e-bool (v a b) v)
        (e-str (s a b) s)
        (e-char (c a b) c)
        (e-float (x a b) x)
        (e-sym (s a b) s)
        (e-unit (a b) the-unit)
        ;; A closure: the host's procedure of its arguments.
        (e-lambda (ps body a b) (lambda ((xs vals)) (eval body (bind ps xs e))))
        (e-app (f args a b) (let* ((fv (eval f e)) (xs (eval-all args e))) (apply-val fv xs)))
        (e-plambda (d body a b) (eval body e))
        ;; Regions and places are erased: a `letrena`'s or `letreap`'s
        ;; allocation is the heap's, and its name, the place as a value, is
        ;; unit.
        (e-letregion (k r i body a b) (eval body (extend r the-unit e)))
        (e-rlambda (r l a b) (eval l e))
        (e-proj (body ds a b) (eval body e))
        (e-the (d body a b) (eval body e))
        (e-convention (cnv body a b) (eval body e))
        (e-if (t th el a b) (if (as-bool (eval t e)) (eval th e) (eval el e)))
        (e-letrec (bs body a b) (eval-letrec bs body e))
        (e-let (bs body a b) (eval body (eval-let bs e e)))
        (e-begin (es a b) (eval-begin es e))
        (e-prompt (t body h a b)
          (let* ((tag (as-tag (eval t e))) (hv (eval h e)))
            (prompt tag (eval body e) (lambda (v) (apply1 hv v)))))
        (e-bloblet (op i args a b) (ev-bloblet op i (eval-all args e)))
        (e-product (fs a b) (o-product (eval-fields fs e)))
        (e-extract (p l a b) (field-of (eval p e) l))
        (e-sum (t v a b) (o-sum t (eval v e)))
        (e-tagcase (s arms els a b) (eval-tagcase (eval s e) arms els e))
        ;; A module: a product of its values, in order, each labelled by its
        ;; name; its abstract types' conversions the identity.
        (e-module (items a b) (eval-module items e))
        ;; `with`: the module's values its body names, by position, bound by
        ;; their names (all of them, if the checker did not say which).
        ;; `(with #%fx n)`: the standard `n`, whatever binds `n` here.
        (e-with (m body a b)
          (if (k-fx-module? m)
              (tagcase body (e-var (n c d) (standard n)) (else y (efail "`(with #%fx name)`")))
              (let ((used (ev-with-in (get ev-withs) a b)))
                (eval body
                      (if (null? used)
                          (bind-module (lookup e m) e)
                          (bind-module-at (lookup e m) (extract (car used) 1) (extract (car used) 2)
                                          e)))))))))
  ;; A module's items, as a `letrec*`'s (`DONE.md` §37): every name first,
  ;; holding #u; then each item's values, in order, in the scope of all.
  (eval-module (subr (maxeff evals spin) (mod-items env) val)
    (lambda (items e)
      (let ((inner (open-names (module-names items) e)))
        (begin (fill-module items inner)
               (o-product (reverse-fields (module-values items inner nil) nil))))))
  (fill-module (subr (maxeff evals spin) (mod-items env) unit)
    (lambda (items e)
      (if (null? items)
          #u
          (let* ((it (car items)) (k (extract it 1)) (ns (extract it 2)) (xs (extract it 4)))
            (begin
              (case k ((0) (fill-cells (conversion-names (symbol->string (car ns))) xs e))
                      ((2 3) (fill-cells ns xs e))
                      (else #u))
              (fill-module (cdr items) e))))))
  ;; Each value of `xs`, into its name's cell in `e`.
  (fill-cells (subr (maxeff evals spin) (names exp-list env) unit)
    (lambda (ns xs e)
      (if (null? ns)
          #u
          (begin (set (find-cell e (car ns)) (eval (car xs) e))
                 (fill-cells (cdr ns) (cdr xs) e)))))
  (eval-let (subr (maxeff evals spin) (exp-let-bs env env) env)
    (lambda (bs outer e)
      (if (null? bs)
          e
          (let ((v (eval (extract (car bs) 2) outer)))
            (eval-let (cdr bs) outer (extend (extract (car bs) 1) v e))))))
  ;; Every name first, holding #u; then each value, in the scope of all.
  (eval-letrec (subr (maxeff evals spin) (exp-letrec-bs exp env) val)
    (lambda (bs body e)
      (let ((inner (open-letrec bs e)))
        (begin (fill-letrec bs inner) (eval body inner)))))
  ;; Each binding's value, into its name's cell in `inner`.
  (fill-letrec (subr (maxeff evals spin) (exp-letrec-bs env) unit)
    (lambda (bs inner)
      (if (null? bs)
          #u
          (let ((c (find-cell inner (extract (car bs) 1))))
            (begin (set c (eval (extract (car bs) 3) inner))
                   (fill-letrec (cdr bs) inner))))))
  (eval-fields (subr (maxeff evals spin) (exp-let-bs env) vfields)
    (lambda (fs e)
      (if (null? fs)
          nil
          (let ((v (eval (extract (car fs) 2) e)))
            (cons (cons (extract (car fs) 1) v) (eval-fields (cdr fs) e))))))
  ;; The arm for sum `s`'s tag, its fields bound; else the `else`.
  (eval-tagcase (subr (maxeff evals spin) (val exp-arms exp-let-bs env) val)
    (lambda (s arms els e)
      (tagcase (as-other s "a sum")
        (o-sum (tag v)
          (letrec ((try (subr (maxeff evals spin) (exp-arms) val)
                     (lambda (as)
                       (cond ((null? as)
                              (if (null? els)
                                  (efail "no arm for this value")
                                  (eval (extract (car els) 2) (extend (extract (car els) 1) s e))))
                             ((symbol=? (extract (car as) 1) tag)
                              (eval (extract (car as) 4)
                                    (if (extract (car as) 2)
                                        (bind-fields (extract (car as) 3) v e)
                                        (extend (car (extract (car as) 3)) v e))))
                             (else (try (cdr as)))))))
            (try arms)))
        (else y (efail-expected "a sum"))))))

;; Names whose next definition keeps the cell they have: definitions that
;; assign their globals (`checked-tops`, under redefinition).
(define ev-keep (ref (listof symbol acyclic) @v) (new nil))

(define* ev-kept? (subr spin ((listof symbol acyclic) symbol) bool)
  (lambda (ks n) (and (not (null? ks)) (or (symbol=? (car ks) n) (ev-kept? (cdr ks) n)))))

(define* ev-unkeep (subr spin ((listof symbol acyclic) symbol) (listof symbol acyclic))
  (lambda (ks n)
    (cond ((null? ks) ks)
          ((symbol=? (car ks) n) (ev-unkeep (cdr ks) n))
          (else (the (listof symbol acyclic) (cons (car ks) (ev-unkeep (cdr ks) n)))))))

(define* ev-new-global (subr stores (symbol) vcell)
  (lambda (n) (let ((c (cell the-unit))) (begin (set genv (cons (cons n c) (get genv))) c))))

;; The cell global `n` has; a new one, if it has none.
(define* ev-cell-of (subr (maxeff stores spin) (env symbol) vcell)
  (lambda (e n)
    (cond ((null? e) (ev-new-global n))
          ((symbol=? (car (car e)) n) (cdr (car e)))
          (else (ev-cell-of (cdr e) n)))))

;; The cell a definition of `n` sets: the one it has, if kept; else new.
(define* push-global (subr (maxeff stores spin) (symbol) vcell)
  (lambda (n)
    (if (ev-kept? (get ev-keep) n)
        (begin (set ev-keep (ev-unkeep (get ev-keep) n)) (ev-cell-of (get genv) n))
        (ev-new-global n))))

(define* rec-cells (subr (maxeff stores spin) (exp-letrec-bs) vcells)
  (lambda (bs)
    (if (null? bs)
        nil
        (let ((c (push-global (extract (car bs) 1)))) (cons c (rec-cells (cdr bs)))))))

(define* rec-fill (subr (maxeff evals spin) (exp-letrec-bs vcells) unit)
  (lambda (bs cells)
    (if (null? bs)
        #u
        (begin (set (car cells) (eval (extract (car bs) 3) (get genv)))
               (rec-fill (cdr bs) (cdr cells))))))

;; Whether `x` is a lambda, under any type abstractions and ascriptions.
(define* lambda-exp? (subr spin (exp) bool)
  (lambda (x)
    (tagcase x
      (e-lambda (ps body a b) #t)
      (e-plambda (d body a b) (lambda-exp? body))
      (e-the (d body a b) (lambda-exp? body))
      (e-convention (cnv body a b) (lambda-exp? body))
      (else y #f))))

;; Defines `n` as `x`'s value, run in the scope before it.
(define* ev-define (subr (maxeff evals spin) (symbol exp) val)
  (lambda (n x) (let ((v (eval x (get genv)))) (begin (set (push-global n) v) the-unit))))

(define* eval-top (subr (maxeff evals spin) (top) val)
  (lambda (t)
    (tagcase t
      (t-define (n ty x a b)
        (if (and (not (null? ty)) (lambda-exp? x))
            ;; A lambda: the cell first, so that it can call itself.
            (let ((c (push-global n))) (begin (set c (eval x (get genv))) the-unit))
            ;; Not recursive: the value first, in the scope before it.
            (ev-define n x)))
      ;; Every name's cell first; then each lambda, which runs nothing.
      (t-define-rec (bs a b) (begin (rec-fill bs (rec-cells bs)) the-unit))
      (t-exp (x) (eval x (get genv)))
      (else x the-unit))))

;; The value so far, after top-level form `t` gave `v`: `v` if `t` is an
;; expression, else `last`, as before.
(define* ev-last (subr pure (top val val) val)
  (lambda (t v last) (tagcase t (t-exp (x) v) (else y last))))

;; The value of the last form, or the first error.
(define* eval-program (subr (maxeff evals spin) ((listof top acyclic)) eresult)
  (lambda (tops)
    (prompt eval-tag
      (letrec ((go (subr (maxeff evals spin) ((listof top acyclic) val) val)
                 (lambda (ts last)
                   (if (null? ts)
                       last
                       (let ((v (eval-top (car ts)))) (go (cdr ts) (ev-last (car ts) v last)))))))
        (ev-ok (go tops the-unit)))
      (lambda (r) r))))

;; Name `n`, and a `define-rec`'s names, to keep their cells.
(define* ev-keep! (subr (maxeff (read @v) (write @v) (alloc @v)) (symbol) unit)
  (lambda (n) (set ev-keep (the (listof symbol acyclic) (cons n (get ev-keep))))))

(define* ev-keep-all (subr (maxeff (read @v) (write @v) (alloc @v) spin) (exp-letrec-bs) unit)
  (lambda (bs) (if (null? bs) #u (begin (ev-keep! (extract (car bs) 1)) (ev-keep-all (cdr bs))))))

;; Before a run that assigns its names' globals: each keeps its cell.
(define* ev-keep-names (subr (maxeff (read @v) (write @v) (alloc @v) spin) (top) unit)
  (lambda (t)
    (tagcase t
      (t-define (n ty x a b) (ev-keep! n))
      (t-define-rec (bs a b) (ev-keep-all bs))
      (else y #u))))

;; What a checked program runs (`checked-tops`), each in turn: the value of
;; the last expression, or the first error.
(define* eval-runs (subr (maxeff evals spin) ((listof k-run acyclic)) eresult)
  (lambda (runs)
    (prompt eval-tag
      (letrec ((go (subr (maxeff evals spin) ((listof k-run acyclic) val) val)
                 (lambda (rs last)
                   (if (null? rs)
                       last
                       (let* ((r (car rs))
                              (kept (if (extract r 2) (ev-keep-names (extract r 1)) #u))
                              (v (eval-top (extract r 1))))
                         (go (cdr rs) (ev-last (extract r 1) v last)))))))
        (ev-ok (go runs the-unit)))
      (lambda (r) r))))

;; A whole program begins with no globals, and no names kept.
(define* ev-begin! (subr stores (k-reshape-list k-with-list) unit)
  (lambda (rs ws) (begin (set genv nil) (set ev-keep nil) (set ev-reshapes rs) (set ev-withs ws))))

;; The entry point for a program the checker written in FX-26 checked: what
;; it runs (`checked-tops`, under redefinition), run; its value shown, or
;; its error. A whole program, as each is.
(define run-checked (subr (maxeff evals (read @t) spin) ((listof k-run acyclic)) string)
  (lambda (runs)
    (tagcase (begin (ev-begin! (get k-reshapes) (get k-with-vals)) (eval-runs runs))
      (ev-ok (v) (show-val v))
      (ev-err (m) (string-append "!! " m)))))

;; The entry point: a program's trees, run; its value shown, or its error.
(define run-program (subr (maxeff evals spin) ((listof top acyclic)) string)
  (lambda (tops)
    (tagcase (begin (ev-begin! nil nil) (eval-program tops))
      (ev-ok (v) (show-val v))
      (ev-err (m) (string-append "!! " m))))))))
