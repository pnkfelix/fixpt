;;; The checker, in FX-26: higher kinds (`docs/research/higher-kinds.md`),
;;; the Rust checker's `kinds.rs`. Description functions, of arrow kinds
;;; `(=> (k1 … kn) k)`, made by `dlambda` and applied to descriptions: a
;;; `dlambda` applied is reduced (beta), one that only applies a function to
;;; its parameters is that function (eta), and a variable applied is an
;;; application, `ty-app`, equal only to one of the same function to equal
;;; descriptions. To an effect, an application is an atom, `a-app`.
;;; Reading them is `check-read-types.fx`'s, with the rest of reading
;;; types. Part of the checker, `check-types.fx` first.

;;; ------------------------------------------------------------ description functions

;; A module (`TODO.md` §34: the front end into modules, a file at a time);
;; what other files use re-exported after it.
(define check-kinds-module (module
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
            (k-lam fresh (dt body)))))))))

(define k-desc-of-kind? (with check-kinds-module k-desc-of-kind?))
(define k-generative-fun (with check-kinds-module k-generative-fun))
