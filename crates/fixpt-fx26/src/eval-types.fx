;;; The evaluator's types (`eval-values.fx`, `eval-prims.fx`, `eval-core.fx`):
;;; a module file of no state, which each of them loads (`TODO.md` §68). Its
;;; values and their effects, and the signatures of the evaluator's own
;;; modules as the others use them.

;; The checker's types it uses.
(define check-types-types (load-module "fx26:check-types-types.fx"))
(define-type k-ids (select check-types-types k-ids))
(define-type k-names (select check-types-types k-names))

;; What changing the program's store on @v may do; what a delimited part
;; of the program may do, besides control on @x; and what evaluating may,
;; perhaps without end: what it is given is a module of procedures over
;; `val`, which a procedure may be given itself in, so a call of one is
;; not known to end (`TODO.md` §68).
(define-effect stores (maxeff (read @globals) (read @v) (write @v) (alloc @v)))

(define-effect runs (maxeff stores (read @x) (write @x) (alloc @x)))

(define-effect evals (maxeff runs (goto @x) (comefrom @x) spin))

;; A value: as itself, or an `other`, the one sum among them.
(define-type val
  (union int f64 f32 char bool string symbol nil
         (pairof val val @v) (arrayof val @v)
         (subr (maxeff evals spin) ((listof val @v)) val)
         (ref val @v)
         other))

;; A value of no shape of its own: unit (a symbol's shape at run time, so
;; told apart here), a product with its labels (as `extract` names one) or a
;; sum with its tag, an i-cell (whether full, and its value), a bloblet (its
;; fields, and its suffix's bytes), and the evaluator's own control.
(define-datatype other
  (o-unit)
  (o-product (listof (pairof symbol val @v) @v))
  (o-sum symbol val)
  (o-icell (ref bool @v) (ref val @v))
  (o-blob (arrayof val @v) (arrayof int @v))
  (o-tag (prompt-tag val val (maxeff runs spin) @x))
  (o-cont (composable val val (maxeff runs spin) @x))
  ;; A `cwcc` escape.
  (o-esc (subr (goto @x) (val) void))
  (o-key (mark-key val @x)))

(define-type vals (listof val @v))

(define-type vproc (subr (maxeff evals spin) (vals) val))

;; A product's fields, by label.
(define-type vfields (listof (pairof symbol val @v) @v))

;; Variables: each name and the cell that holds its value.
(define-type vcell (ref val @v))

(define-type env (listof (pairof symbol vcell @v) @v))

(define-type vtag (prompt-tag val val (maxeff runs spin) @x))

(define-type vcont (composable val val (maxeff runs spin) @x))

(define-datatype eresult (ev-ok val) (ev-err string))

;; The positions a module reshaped from `a` to `b` keeps, in a list of one;
;; none if it is not reshaped.
(define-type ev-at (listof k-ids @v))

;; Those of the `with` from `a` to `b`, in a list of one; none if the checker
;; did not see it (a program run unchecked, `run-program`).
(define-type ev-with-at (listof (productof (1 k-names) (2 k-ids)) @v))

;; The cells of a `define-rec`'s names, and its values put in them.
(define-type vcells (listof vcell @v))

;;; ------------------------------------------------------------ signatures

;; The values module as `eval-prims.fx` and `eval-core.fx` use it.
(define-type eval-values-sig
  (moduleof
   (val apply-val (subr (maxeff evals spin) (val vals) val))
   (val apply1 (subr (maxeff evals spin) (val val) val))
   (val as-array (subr evals (val) (arrayof val @v)))
   (val as-bool (subr evals (val) bool))
   (val as-char (subr evals (val) char))
   (val as-cont (subr (maxeff evals spin) (val) vcont))
   (val as-f32 (subr evals (val) f32))
   (val as-f64 (subr evals (val) f64))
   (val as-fields (subr (maxeff evals spin) (val string) vfields))
   (val as-int (subr evals (val) int))
   (val as-key (subr (maxeff evals spin) (val) (mark-key val @x)))
   (val as-other (subr evals (val string) other))
   (val as-pair (subr evals (val) (pairof val val @v)))
   (val as-ref (subr evals (val) vcell))
   (val as-str (subr evals (val) string))
   (val as-sym (subr evals (val) symbol))
   (val as-tag (subr (maxeff evals spin) (val) vtag))
   (val efail (subr evals (string) void))
   (val efail-expected (subr evals (string) void))
   (val ev-arg (subr (maxeff evals spin) (vals int) val))
   (val ev-eq? (subr pure (val val) bool))
   (val ev-intern (subr (maxeff stores spin) (val) val))
   (val eval-tag (prompt-tag eresult eresult (maxeff runs spin) @x))
   (val list->val (subr (maxeff (read @globals) (read @x) (alloc @v) spin) ((listof val @x)) val))
   (val show-val (subr (maxeff (read @globals) (read @v) (alloc @v) spin) (val) string))
   (val the-unit val)
   (val val->vals (subr (maxeff (read @globals) (read @v) (alloc @v) spin) (val) vals))
   (val vals->val (subr (maxeff (read @globals) (read @v) (alloc @v) spin) (vals) val))))
;; The primitives' module as `eval-core.fx` uses it.
(define-type eval-prims-sig
  (moduleof
   (val ev-bloblet (subr (maxeff evals spin) (symbol int vals) val))
   (val standard (subr (maxeff evals spin) (symbol) val))))
