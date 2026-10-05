;;; The checker, in FX-26: descriptions given as `proj` arguments, each
;;; read as the kind its shape, or its name's binding, says. Part of the
;;; checker, `check-types.fx` first (moved out of `check-syntax.fx`,
;;; 2026-10-04).

;; A module (`TODO.md` §34: the front end into modules, a file at a time);
;; what other files use re-exported after it.
(define check-args-module (module
;; Name or `dlambda` `s`, a description function.
(define k-fun-d (subr (maxeff checks spin) (syn) k-desc)
  (lambda (s) (df ((get k-fun-reader) s -1))))
;; A `proj` argument: which kind it is shows in its shape, or, for a bare
;; name, in how the name is bound.
;; A convention, if name `s` is one of FX-26's own; else a type.
(define k-parse-conv-or-type (subr (maxeff checks spin) (syn) k-desc)
  (lambda (s)
    (let ((n (syn-name s)))
      (if (or (string=? n "cellular") (string=? n "native") (string=? n "fx"))
          (dc (k-parse-conv s))
          (dt (k-parse-type s))))))
;; What name `s`, meaning `d` (none or one), is as a `proj` argument: by how
;; it is bound; if it is not bound as a description, a convention or a type.
(define k-parse-d-bound (subr (maxeff checks spin) (syn (listof k-ds acyclic)) k-desc)
  (lambda (s d)
    (if (null? d)
        (if (null? (k-ctor-params (syn-name s))) (k-parse-conv-or-type s) (k-fun-d s))
        (tagcase (car d)
          (ds-fun (f) (k-fun-d s))
          (ds-abbrev (ps body) (if (null? ps) (k-parse-conv-or-type s) (k-fun-d s)))
          (ds-gen (g)
            (if (null? (extract (k-gen-of g) 2)) (k-parse-conv-or-type s) (k-fun-d s)))
          (ds-var (v k)
            (cond ((>= k 100) (k-fun-d s))
                  ((or (= k 0) (= k 3)) (dr (r-var v)))
                  ((= k 1) (de (k-one (a-var v))))
                  ((= k 5) (dz (k-size-var v)))
                  ((= k 6) (dc (cv-var v)))
                  (else (k-parse-conv-or-type s))))
          (ds-region (r) (dr r))
          (ds-eff (e) (de e))
          (ds-size (z) (dz z))
          (ds-conv (c) (dc c))
          (else x (k-parse-conv-or-type s))))))
;; A `proj` argument that is a name.
(define k-parse-d-name (subr (maxeff checks spin) (syn) k-desc)
  (lambda (s)
    (let* ((n (syn-name s)) (sym (string->symbol n)))
      (cond ((k-at-name? n) (dr (k-region-constant sym)))
            ((string=? n "pure") (de nil))
            ((string=? n "spin") (de (k-one (a-spin))))
            ((string=? n "const") (dr (r-frozen -1 #f)))
            ((string=? n "acyclic") (dr (r-frozen -1 #t)))
            ((string=? n "finite") (dz (sz-finite)))
            ((string=? n "heap") (dr (r-heap)))
            (else (k-parse-d-bound s (k-lookup-desc sym)))))))
(define k-parse-d (subr (maxeff checks spin) (syn) k-desc)
  (lambda (s)
    (cond ((tagcase s (atom (d a b) (datum-int? d)) (else x #f))
           ;; A natural number can only be a size.
           (dz (k-parse-size s)))
          ((syn-symbol? s) (k-parse-d-name s))
          (else
           (let ((hd (k-head (k-items s "a description"))))
             (cond ((string=? hd "dlambda") (k-fun-d s))
                   ((or (k-atom-head? hd) (string=? hd "maxeff")) (de (k-parse-effect s)))
                   ((or (string=? hd "+") (string=? hd "-")) (dz (k-parse-size s)))
                   (else (dt (k-parse-type s)))))))))))

(define k-parse-d (with check-args-module k-parse-d))
