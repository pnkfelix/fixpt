;;; The checker, in FX-26: an `allof` type made of its members, `subr`s of
;;; one convention, or products of them distributed field by field
;;; (`logical-types.md` §8.5). Apart from `check-read-descs.fx` since
;;; 2026-11-05 (`TODO.md` §188), which reads the members and makes it of the
;;; modules it is given.
;;; A file of one expression (`load-input`, `TODO.md` §68).


;; Its types, those it uses of the files before it, and the signatures of
;; what it is given.
(let* ((check-types-types (load-module "fx26:check-types-types.fx"))
       (eager-reader-types ((proj (load-module "fx26:eager-reader-types.fx") @s @e @m @c)))
       (parser-types ((proj (load-module "fx26:parser-types.fx") @s @e @m @c @p)))
       (check-syntax-types (load-module "fx26:check-syntax-types.fx"))
       (check-read-types (load-module "fx26:check-read-types.fx"))
       (check-env-types (load-module "fx26:check-env-types.fx"))
       (check-holds-types (load-module "fx26:check-holds-types.fx"))
       (check-read-helpers-types (load-module "fx26:check-read-helpers-types.fx"))
       (check-subst-types (load-module "fx26:check-subst-types.fx"))
       (check-print-types (load-module "fx26:check-print-types.fx"))
       (check-print-parts-types (load-module "fx26:check-print-parts-types.fx"))
       (check-proving-types (load-module "fx26:check-proving-types.fx"))
       (check-effects-types (load-module "fx26:check-effects-types.fx"))
       (check-unions-types (load-module "fx26:check-unions-types.fx"))
       (reader-types (load-module "fx26:reader-types.fx"))
       (check-specs-types (load-module "fx26:check-specs-types.fx"))
       (check-read-made-types (load-module "fx26:check-read-made-types.fx")))
  ;; What it is given: the modules of the files before it that it uses.
  (lambda ((check-types (select check-types-types check-types-sig))
           (check-read-helpers (select check-read-helpers-types check-read-helpers-sig))
           (check-syntax (select check-syntax-types check-syntax-sig))
           (check-read (select check-read-types check-read-sig))
           (check-subst (select check-subst-types check-subst-sig))
           (check-env (select check-env-types check-env-sig))
           (check-print (select check-print-types check-print-sig))
           (check-holds (select check-holds-types check-holds-sig))
           (check-proving (select check-proving-types check-proving-sig))
           (check-effects (select check-effects-types check-effects-sig))
           (check-unions (select check-unions-types check-unions-sig))
           (parser (select reader-types parser-sig))
           (check-print-parts (select check-print-parts-types check-print-parts-sig))
           (check-specs (select check-specs-types check-specs-sig))
           (check-read-made (select check-read-made-types check-read-made-sig)))
    (module

;; The types it uses of the files before it.
(hide (include check-types-types) (include eager-reader-types) (include parser-types)
      (include check-syntax-types) (include check-read-types) (include check-env-types)
      (include check-holds-types))
;; What it uses of the modules it is given: all of each, hidden.
(hide (include check-types) (include check-read-helpers) (include check-syntax)
      (include check-subst) (include check-env) (include check-print-parts) (include check-print)
      (include check-holds) (include check-proving) (include check-unions) (include parser))
(import check-read k-sfail)

(define k-subr-conv (->* (int) k-conv)
  (lambda (t) (tagcase (k-get t) (ty-subr (e ps r cv spc) cv) (else y (get k-conv-default)))))
(define k-allof-one-conv (->* (k-ids int syn) unit)
  (lambda (ms m0 s)
    (cond ((null? ms) #u)
          ((k-conv=? (k-subr-conv (car ms)) (k-subr-conv m0)) (k-allof-one-conv (cdr ms) m0 s))
          (else (k-sfail (k-cat5 "an `allof`'s members have one convention: a " (k-show-ty m0)
                                 " and a " (k-show-ty (car ms)) " do not")
                         s)))))
(define k-product-parts (->* (int) k-parts)
  (lambda (t) (tagcase (k-get (k-resolve t)) (ty-product (fs) fs) (else y nil))))
(define k-product? (->* (int) bool)
  (lambda (t) (tagcase (k-get (k-resolve t)) (ty-product (fs) #t) (else y #f))))
(define k-same-labels? (->* (k-parts k-parts) bool)
  (lambda (fs gs)
    (cond ((null? fs) (null? gs))
          ((null? gs) #f)
          (else (and (symbol=? (extract (car fs) 1) (extract (car gs) 1))
                     (k-same-labels? (cdr fs) (cdr gs)))))))
;; Of `ms`, the first that is a product, and the first that is not a
;; product of `first`'s labels; -1 for none.
(define k-first-product (->* (k-ids) int)
  (lambda (ms)
    (cond ((null? ms) -1) ((k-product? (car ms)) (car ms)) (else (k-first-product (cdr ms))))))
(define k-first-unlike (->* (k-ids k-parts) int)
  (lambda (ms first)
    (cond ((null? ms) -1)
          ((and (k-product? (car ms)) (k-same-labels? (k-product-parts (car ms)) first))
           (k-first-unlike (cdr ms) first))
          (else (car ms)))))
;; The `allof` of `ms`, each a `subr` or a product (`allof`s among them
;; flattened): of `subr`s of one convention, the `allof`; of products of the
;; same labels in order, the product whose field is what every member's is,
;; where they are the same, and their `allof` where not, so that only
;; procedures differ (`logical-types.md` §8.5: the intersection distributes
;; over products). As Rust's `Checker::allof_of`.
(define k-allof-of (->* (k-ids syn) int)
  (lambda (ms s)
    (let ((p0 (k-first-product ms)))
      (if (< p0 0)
          (begin (k-allof-one-conv ms (car ms) s) (k-ty-new (ty-allof ms)))
          (let ((other (k-first-unlike ms (k-product-parts p0))))
            (if (>= other 0)
                (k-sfail (k-cat5 "an `allof` of products: its members are products of the same "
                                 "labels, in order, and a " (k-show-ty p0) " and a "
                                 (string-append (k-show-ty other) " are not"))
                         s)
                (k-ty-new (ty-product (k-allof-fields ms (k-product-parts p0) 1 s)))))))))
;; From the field `i`th (from 1) of `fs`, the first product's, each field of
;; the products `ms`.
(define k-allof-fields (->* (k-ids k-parts int syn) k-parts)
  (lambda (ms fs i s)
    (if (null? fs)
        nil
        (let* ((l (extract (car fs) 1)) (t0 (extract (car fs) 2)) (at (k-fields-at ms i))
               (t (if (k-all-same-type? t0 at) t0 (k-allof-of (k-allof-flat at t0 at l s) s))))
          (cons (product (1 l) (2 t)) (k-allof-fields ms (cdr fs) (+ i 1) s))))))
(define k-fields-at (->* (k-ids int) k-ids)
  (lambda (ms i)
    (if (null? ms)
        nil
        (the k-ids (cons (extract (k-nth (k-product-parts (car ms)) (- i 1)) 2)
                         (k-fields-at (cdr ms) i))))))
(define k-all-same-type? (->* (int k-ids) bool)
  (lambda (t0 ts) (or (null? ts) (and (k-same-type? t0 (car ts)) (k-all-same-type? t0 (cdr ts))))))
(define k-first-not-same (->* (int k-ids int) int)
  (lambda (t0 ts dflt)
    (cond ((null? ts) dflt)
          ((k-same-type? t0 (car ts)) (k-first-not-same t0 (cdr ts) dflt))
          (else (car ts)))))
;; The members of field `l`'s types `ts`, `allof`s flattened; each a `subr`
;; or a product, else refused.
(define k-allof-flat (->* (k-ids int k-ids symbol syn) k-ids)
  (lambda (ts t0 at l s)
    (if (null? ts)
        nil
        (let ((t (k-resolve (car ts))))
          (tagcase (k-get t)
            (ty-allof (ms) (append ms (k-allof-flat (cdr ts) t0 at l s)))
            (ty-subr (e ps r cv spc) (the k-ids (cons t (k-allof-flat (cdr ts) t0 at l s))))
            (ty-product (fs) (the k-ids (cons t (k-allof-flat (cdr ts) t0 at l s))))
            (else y (k-sfail (k-cat5 "an `allof`'s members differ at `" (symbol->string l) "`, a "
                                     (k-show-ty t0)
                                     (string-append " and a " (k-show-ty (k-first-not-same t0 at t))
                                                    ": only procedures, and products of them, may"))
                             s))))))))))
