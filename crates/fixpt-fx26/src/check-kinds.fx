;;; The checker, in FX-26: higher kinds (`docs/research/higher-kinds.md`),
;;; the Rust checker's `kinds.rs`. Description functions, of arrow kinds
;;; `(=> (k1 … kn) k)`, made by `dlambda` and applied to descriptions: a
;;; `dlambda` applied is reduced (beta), one that only applies a function to
;;; its parameters is that function (eta), and a variable applied is an
;;; application, `ty-app`, equal only to one of the same function to equal
;;; descriptions. To an effect, an application is an atom, `a-app`.
;;; Reading them is `check-read-descs.fx`'s, with the rest of reading
;;; types. Part of the checker, `check-types.fx` first.

;;; ------------------------------------------------------------ description functions

;; Its types, those it uses of the files before it, and the signatures of
;; what it is given.
(let* ((check-types-types (load-module "fx26:check-types-types.fx"))
       (check-read-descs-types (load-module "fx26:check-read-descs-types.fx"))
       (check-holds-types (load-module "fx26:check-holds-types.fx"))
       (check-print-types (load-module "fx26:check-print-types.fx")))
  ;; What it is given: the modules of the files before it that it uses.
  (lambda ((check-types (select check-types-types check-types-sig))
           (check-read-descs (select check-read-descs-types check-read-descs-sig))
           (check-holds (select check-holds-types check-holds-sig))
           (check-print (select check-print-types check-print-sig)))
    (module

;; The types it uses of the files before it.
(define dc (with check-types-types dc))
(define de (with check-types-types de))
(define df (with check-types-types df))
(define dr (with check-types-types dr))
(define dt (with check-types-types dt))
(define dz (with check-types-types dz))
(define-type k-binders (select check-types-types k-binders))
(define-type k-desc (select check-types-types k-desc))
(define-effect kstate (select check-types-types kstate))
(define ty-named (with check-types-types ty-named))
;; What it uses of the modules it is given.
(define k-arrow (with check-types k-arrow))
(define k-arrow-kind? (with check-types k-arrow-kind?))
(define k-binder-kinds (with check-types k-binder-kinds))
(define k-dvar-name (with check-types k-dvar-name))
(define k-gen-of (with check-types k-gen-of))
(define k-new-dvar-of (with check-types k-new-dvar-of))
(define k-ty-new (with check-types k-ty-new))
(define k-binders-as-descs (with check-read-descs k-binders-as-descs))
(define k-lam (with check-read-descs k-lam))
(define k-fun-kind (with check-holds k-fun-kind))
(define k-place? (with check-print k-place?))

;; Whether description `d` is of kind `k`, as a binder of that kind takes; a
;; function whose kind is not known yet, a `select`, is let through.
(define k-desc-of-kind? (subr (maxeff kstate spin) (k-desc int) bool)
  (lambda (d k)
    (tagcase d
      (dr (r) (or (= k 0) (and (= k 3) (k-place? r))))
      (de (e) (= k 1))
      (dt (t) (or (= k 2) (= k 4)))
      (dz (z) (= k 5))
      (dc (c) (= k 6))
      (df (f) (and (k-arrow-kind? k) (let ((g (k-fun-kind f))) (or (< g 0) (= g k))))))))

;; Binders `ps` made again: fresh variables of the same names and kinds.
(define k-fresh-binders (subr (maxeff kstate spin) (k-binders) k-binders)
  (lambda (ps)
    (if (null? ps)
        nil
        (let* ((v (extract (car ps) 1)) (k (extract (car ps) 2))
               (w (k-new-dvar-of (k-dvar-name v) k))
               (rest (k-fresh-binders (cdr ps))))
          (the k-binders (cons (product (1 w) (2 k)) rest))))))
;; The `g`th generative type as a description function of kind `want`,
;; `(dlambda ((p k) …) (name p …))`; -1 if it is not of that kind.
(define k-generative-fun (subr (maxeff kstate spin) (int int) int)
  (lambda (g want)
    (let ((ps (extract (k-gen-of g) 2)))
      (if (not (= (k-arrow (k-binder-kinds ps) 2) want))
          -1
          (let* ((fresh (k-fresh-binders ps))
                 (body (k-ty-new (ty-named g (k-binders-as-descs fresh)))))
            (k-lam fresh (dt body))))))))))
