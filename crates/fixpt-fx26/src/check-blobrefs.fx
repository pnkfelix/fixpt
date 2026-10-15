;;; The checker, in FX-26: the `blobref` forms' types and what they tell
;;; the compilers (`TODO.md` §77): a new blobref's flat, the bytes it takes,
;;; and an array's element and length. Out of `check-read-helpers.fx`.

;; Its types, those it uses of the files before it, and the signatures of
;; what it is given.
(let* ((check-types-types (load-module "fx26:check-types-types.fx"))
       (check-env-types (load-module "fx26:check-env-types.fx"))
       (check-print-types (load-module "fx26:check-print-types.fx"))
       (check-read-helpers-types (load-module "fx26:check-read-helpers-types.fx")))
  ;; What it is given: the modules of the files before it that it uses.
  (lambda ((check-types (select check-types-types check-types-sig))
           (check-env (select check-env-types check-env-sig))
           (check-print (select check-print-types check-print-sig))
           (check-read-helpers (select check-read-helpers-types check-read-helpers-sig)))
    (module

;; The types it uses of the files before it.
(hide (include check-types-types) (include check-env-types))
;; What it uses of the modules it is given: all of each, hidden.
(hide (include check-types) (include check-env) (include check-print)
      (include check-read-helpers))

;; The bytes flat `f` takes at the least (`Checker::flat_least_size`): its
;; size, or, one that is or ends in an array that runs to the end of the
;; suffix, its size with none of that array's elements; -1 if not known.
(define k-flat-least-size (subr (maxeff kstate spin) (int) int)
  (lambda (f)
    (car (k-flat-layout
          (if (null? (k-unsized-length f)) f (k-with-unsized-length f (sz-lin 0 nil)))))))
;; A new blobref at `a`..`z`, the `k`th there, to flat `f`: the bytes it
;; takes, noted for the compilers to check in the suffix
;; (`Checker::note_fits`); `f`.
(define k-note-fits (subr (maxeff checks spin) (int int int int) int)
  (lambda (a z k f)
    (let ((s (k-flat-least-size f)))
      (if (< s 0)
          (k-fail (k-cat3 "the layout of a " (k-show-ty f) " is not known") a z)
          (let ((fact (product (1 (product (1 a) (2 z) (3 k))) (2 s))))
            (begin (set k-extracts (cons fact (get k-extracts))) f))))))
;; The flat the type checked against says, for a new blobref at `a`..`z`,
;; the `k`th there.
(define k-blobref-wanted (subr (maxeff checks spin) (int int int int) int)
  (lambda (a z k expected)
    (let ((p (if (< expected 0) nil (k-blobref-parts expected))))
      (if (null? p)
          (k-fail (string-append "which flat a new `blobref` points to is said by the type it is "
                                 "checked against: `(the (blobref B F) …)`")
                  a z)
          (let* ((f (cdr (car p))) (n (k-unsized-length f)))
            (if (or (null? n) (tagcase (car n) (sz-finite () #t) (else y #f)))
                (k-note-fits a z k f)
                (k-fail (k-cat3 "a new blobref's array of a length not literal is of length "
                                "`finite`, not a "
                                (string-append (k-show-ty f)
                                               ": the length is named where the blobref is bound"))
                        a z)))))))
;; Of a blobref at `a`..`z`, the `k`th there, of type `xt`, owner `b`, flat
;; `f`, read or written: the owner's region, `f` a scalar; noting the
;; scalar's layout for the compilers if `note`.
(define k-blobref-region
  (subr (maxeff checks spin) (int int int int int int bool) k-region)
  (lambda (a z k xt b f note)
    (let ((code (tagcase (k-get (k-resolve f)) (ty-base (s) (k-flat-code s)) (else y -1))))
      (if (< code 0)
          (k-fail (k-cat3 "only a scalar's bytes are read or written, and this points to a "
                          (k-show-ty f) "")
                  a z)
          (tagcase (k-get (k-resolve b))
            (ty-bloblet (fs fz r)
              (let ((fact (product (1 (product (1 a) (2 z) (3 k))) (2 code))))
                (begin (if note (set k-extracts (cons fact (get k-extracts))) #u) r)))
            (else y (k-fail (k-cat3 "the region of a " (k-show-ty xt) "'s owner is not known")
                            a z)))))))
;; A `blobref-length` at `a`..`z`, the `k`th there, of flat array `f`: a
;; `(nat n)` of its length `n`, told the compilers as `blobref-index`'s is
;; (`TODO.md` §77).
(define k-blobref-length (subr (maxeff checks spin) (int int int int) int)
  (lambda (a z k f)
    (let* ((p (k-flat-array-parts f)) (e (k-flat-layout (car p))))
      (if (< (car e) 0)
          (k-fail (k-cat3 "the layout of a " (k-show-ty (car p)) " is not known") a z)
          (let ((fact (product (1 (product (1 a) (2 z) (3 k)))
                                (2 (+ (* (cdr p) 4294967296) (car e))))))
            (begin
              (set k-extracts (cons fact (get k-extracts)))
              (k-ty-new (ty-nat (k-flat-array-length f)))))))))
;; Flat array `t`'s length, a size (`Checker::flat_array_parts`).
(define k-flat-array-length (subr (maxeff kreads (alloc @t) spin) (int) k-size)
  (lambda (t)
    (tagcase (k-get (k-resolve t))
      (ty-named (g ds)
        (tagcase (car (cdr ds)) (dz (z) z) (else y (sz-finite))))
      (else y (sz-finite)))))
;; A `blobref-index` at `a`..`z`, the `k`th there, into flat array `f`: its
;; element, its length and the element's size noted for the compilers, `n
;; << 32 | size`.
(define k-blobref-element (subr (maxeff checks spin) (int int int int) int)
  (lambda (a z k f)
    (let* ((p (k-flat-array-parts f)) (e (k-flat-layout (car p))))
      (if (< (car e) 0)
          (k-fail (k-cat3 "the layout of a " (k-show-ty (car p)) " is not known") a z)
          (let ((fact (product (1 (product (1 a) (2 z) (3 k)))
                                (2 (+ (* (cdr p) 4294967296) (car e))))))
            (begin (set k-extracts (cons fact (get k-extracts))) (car p)))))))
)))
