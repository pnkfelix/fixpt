;;; The FX-26 evaluator's bloblets and blobrefs (`docs/object-model.md`,
;;; `TODO.md` §77): a bloblet's fields and bytes, made and read and
;;; written; a blobref's owner and offset, and the flat data it points to,
;;; read as the checker found its layout. Apart from `eval-prims.fx` since
;;; 2026-10-31 (`TODO.md` §188); `eval-core.fx` uses it.
;;; A file of one expression (`load-input`, `TODO.md` §68): what makes the
;;; module, which the conductor (`conductor.fx`) applies to the evaluator's
;;; values.

;; Its types, and the signature of what it is given (`eval-types.fx`).
(let* ((eval-types (load-module "fx26:eval-types.fx"))
       (parser-types ((proj (load-module "fx26:parser-types.fx") @s @e @m @c @p))))
  ;; What it is given: the evaluator's values.
  (lambda ((values (select eval-types eval-values-sig)))
    (module
(hide (include eval-types))
;; A flat array's operand taken apart (`k-array-operand`).
(import parser-types k-array-length k-array-size)
;; What it uses of the module it is given.
(import values as-f32 as-f64 as-int as-other efail efail-expected ev-arg ev-eq? the-unit)

;; How many `xs` there are.
(define ev-vals-count (->* (vals) int)
  (lambda (xs) (if (null? xs) 0 (+ 1 (ev-vals-count (cdr xs))))))

;; Elements `i` on of `a`, from `xs`.
(define ev-fill-array (->* ((arrayof val @v) vals int) unit)
  (lambda (a xs i)
    (if (null? xs) #u (begin (array-set! a i (car xs)) (ev-fill-array a (cdr xs) (+ i 1))))))

;; A bloblet of `n` bytes, its fields `xs`.
(define ev-make-bloblet (->* (vals) val)
  (lambda (xs)
    (let* ((n (as-int (ev-arg xs 0))) (fields (cdr xs))
           (fs (the (arrayof val @v) (make-array (ev-vals-count fields) the-unit))))
      (begin (ev-fill-array fs fields 0)
             (o-blob fs (the (arrayof int @v) (make-array n 0)))))))

;;; ------------------------------------------------------------ blobrefs
;; A blobref to byte `at` of `owner`'s suffix, checked to be one of it.
(define ev-bref (->* (val int) val)
  (lambda (owner at)
    (tagcase (as-other owner "a bloblet")
      (o-blob (fs bs)
        (if (and (>= at 0) (< at (array-length bs)))
            (o-bref owner at)
            (efail "suffix ref: the bloblet's suffix has no such byte")))
      (else y (efail-expected "a bloblet")))))
;; New blobref `r`, back where its flat's `size` bytes lie in the suffix
;; (`Checker::note_fits`).
(define ev-fits (->* (val int) val)
  (lambda (r size)
    (let ((p (ev-bref-bytes r)))
      (if (<= (+ (cdr p) size) (array-length (car p)))
          r
          (efail "suffix ref: a flat runs past the end of the suffix")))))
;; Blobref `v`'s owner's suffix's bytes, and its offset.
(define ev-bref-bytes (->* (val) (pairof (arrayof int @v) int @v))
  (lambda (v)
    (tagcase (as-other v "a blobref")
      (o-bref (o at)
        (tagcase (as-other o "a bloblet")
          (o-blob (fs bs) (cons bs at))
          (else y (efail "a bloblet"))))
      (else y (efail-expected "a blobref")))))
;; 256 to the `w`, times `acc`.
(define ev-pow256 (->* (int int) int)
  (lambda (w acc) (if (= w 0) acc (ev-pow256 (- w 1) (* 256 acc)))))
;; Bytes `at` to `at` + `k`, little-endian, after `acc`: the highest first.
(define ev-bytes-int (->* ((arrayof int @v) int int int) int)
  (lambda (bs at k acc)
    (if (< k 0) acc (ev-bytes-int bs at (- k 1) (+ (* acc 256) (array-ref bs (+ at k)))))))
;; `w` bytes from `at` := `n`, not negative, little-endian.
(define ev-int-bytes! (->* ((arrayof int @v) int int int) unit)
  (lambda (bs at w n)
    (if (= w 0)
        #u
        (begin (array-set! bs at (modulo n 256))
               (ev-int-bytes! bs (+ at 1) (- w 1) (quotient n 256))))))
;; A scalar's width, by its layout (`fixpt_heap::layout::FLAT_*`).
(define ev-flat-width (->* (int) int)
  (lambda (code) (if (or (= code 2) (= code 3) (= code 5)) 8 4)))
;; The scalar of layout `code` at byte `at` of `bs`, as a value.
(define ev-scalar-get (->* ((arrayof int @v) int int) val)
  (lambda (bs at code)
    (let ((w (ev-flat-width code)))
      (if (> (+ at w) (array-length bs))
          (efail "suffix ref: the bloblet's suffix has no such byte")
          (let ((u (ev-bytes-int bs at (- w 1) 0)))
            (case code
              ((0) (if (>= u 2147483648) (- u 4294967296) u))
              ((2) (if (>= u 9223372036854775808) (- u 18446744073709551616) u))
              ((4) (bits->f32 (int->u32 u)))
              ((5) (bits->f64 (int->u64 u)))
              (else u)))))))
;; The scalar of layout `code` at byte `at` of `bs` := `v`.
(define ev-scalar-set! (->* ((arrayof int @v) int int val) unit)
  (lambda (bs at code v)
    (let ((w (ev-flat-width code)))
      (if (> (+ at w) (array-length bs))
          (efail "suffix ref: the bloblet's suffix has no such byte")
          (let ((n (case code
                     ((4) (u32->int (f32->bits (as-f32 v))))
                     ((5) (u64->int (f64->bits (as-f64 v))))
                     (else (as-int v)))))
            (ev-int-bytes! bs at w (if (< n 0) (+ n (ev-pow256 w 1)) n)))))))
;; Blobref operation `op` on `xs`; `i` the layout the checker found: a
;; scalar's (`blobref-get`, `-set!`), or an array's `n << 32 | size`.
(define ev-blobref (->* (symbol int vals) val)
  (lambda (op i xs)
    (if (symbol=? op 'blobref-at)
        (ev-fits (ev-bref (ev-arg xs 0) (as-int (ev-arg xs 1))) i)
        (let ((r (ev-arg xs 0)))
          (tagcase (as-other r "a blobref")
            (o-bref (o at)
              (case op
                ((blobref+) (ev-fits (ev-bref o (+ at (as-int (ev-arg xs 1)))) i))
                ((blobref-owner) o)
                ((blobref-offset) at)
                ((blobref-length) (ev-flat-length r (k-array-length i) (k-array-size i)))
                ((blobref-index)
                 (let* ((k (as-int (ev-arg xs 1))) (size (k-array-size i))
                        (n (ev-flat-length r (k-array-length i) size)))
                   (if (and (>= k 0) (< k n))
                       (ev-bref o (+ at (* k size)))
                       (efail "blobref-index: out of range"))))
                ((blobref-get) (let ((p (ev-bref-bytes r))) (ev-scalar-get (car p) at i)))
                ((blobref-variant!) (ev-flat-variant r i (ev-arg xs 1)))
                (else (let ((p (ev-bref-bytes r)))
                        (begin (ev-scalar-set! (car p) at i (ev-arg xs 1)) the-unit)))))
            (else y (efail-expected "a blobref")))))))

;; A flat array's length, `n` as the checker knew it, or, for one that runs
;; to the end of the suffix (`n` 268435455, `FLAT_TO_THE_END`), the whole
;; elements of `size` bytes left of the suffix after blobref `r` (`TODO.md`
;; §77).
(define ev-flat-length (->* (val int int) int)
  (lambda (r n size)
    (if (and (= n 268435455) (> size 0))
        (let ((p (ev-bref-bytes r))) (quotient (- (array-length (car p)) (cdr p)) size))
        n)))

;; A flat sum's tag, of layout `k` (`TODO.md` §77): `w` bytes, a number as
;; it is if the key is numeric; else the owner's field it indexes, which
;; holds the label (`%fx26-flat-tag`).
(define ev-flat-tag (->* (val int) val)
  (lambda (r k)
    (let* ((p (ev-bref-bytes r)) (bs (car p)) (at (cdr p)) (w (modulo k 8)))
      (if (> (+ at w) (array-length bs))
          (efail "suffix ref: the bloblet's suffix has no such byte")
          (let ((n (ev-bytes-int bs at (- w 1) 0)))
            (if (= (modulo (quotient k 8) 2) 1)
                n
                (tagcase (as-other (ev-bref-owner r) "a bloblet")
                  (o-blob (fs gs)
                    (if (< n (array-length fs))
                        (array-ref fs n)
                        (efail "flat sum: its tag names no field of its owner")))
                  (else y (efail-expected "a bloblet")))))))))
;; Whether tag `t` is label `l` of a flat sum of layout `k`: its number, or
;; the symbol.
(define ev-label-is? (->* (val symbol int) bool)
  (lambda (t l k)
    (typecase t
      (int n (and (= (modulo (quotient k 8) 2) 1) (string=? (int->string n) (symbol->string l))))
      (symbol s (and (= (modulo (quotient k 8) 2) 0) (symbol=? s l)))
      (else #f))))
;; `blobref-variant!` (`%fx26-flat-variant!`): the tag made `label`'s, a
;; number as it is, or else the first of the owner's fields holding it; a
;; blobref to the variant.
(define ev-flat-variant (->* (val int val) val)
  (lambda (r k label)
    (let* ((p (ev-bref-bytes r)) (bs (car p)) (at (cdr p)) (w (modulo k 8))
           (n (if (= (modulo (quotient k 8) 2) 1)
                  (as-int label)
                  (tagcase (as-other (ev-bref-owner r) "a bloblet")
                    (o-blob (fs gs) (ev-field-holding fs label 0))
                    (else y (efail-expected "a bloblet"))))))
      (cond ((>= n (ev-pow256 w 1)) (efail "blobref-variant!: the tag does not fit its key"))
            ((> (+ at w) (array-length bs))
             (efail "suffix ref: the bloblet's suffix has no such byte"))
            (else (begin (ev-int-bytes! bs at w n)
                         (ev-bref (ev-bref-owner r) (+ at (quotient k 256)))))))))
(define ev-field-holding (->* ((arrayof val @v) val int) int)
  (lambda (fs label i)
    (cond ((= i (array-length fs))
           (efail "blobref-variant!: no field of the owner holds the label"))
          ((ev-eq? (array-ref fs i) label) i)
          (else (ev-field-holding fs label (+ i 1))))))
(define ev-bref-owner (->* (val) val)
  (lambda (r)
    (tagcase (as-other r "a blobref") (o-bref (o at) o) (else y (efail-expected "a blobref")))))

;; Bloblet operation `op`, at field `i`, of `xs`.
(define ev-bloblet (->* (symbol int vals) val)
  (lambda (op i xs)
    (case op
      ((rmake-bloblet) (ev-make-bloblet (cdr xs)))
      ((make-bloblet) (ev-make-bloblet xs))
      ((blobref-at blobref+ blobref-owner blobref-offset blobref-get blobref-set! blobref-index
        blobref-length blobref-variant!)
       (ev-blobref op i xs))
      (else
       (tagcase (as-other (ev-arg xs 0) "a bloblet")
         (o-blob (fs bs)
           (case op
             ((bloblet-ref) (array-ref fs i))
             ((bloblet-set!) (begin (array-set! fs i (ev-arg xs 1)) the-unit))
             ((bloblet-freeze) (ev-arg xs 0))
             ((bloblet-byte) (array-ref bs (as-int (ev-arg xs 1))))
             ((bloblet-set-byte!)
              (begin (array-set! bs (as-int (ev-arg xs 1)) (as-int (ev-arg xs 2))) the-unit))
             (else (array-length bs))))
         (else y (efail-expected "a bloblet"))))))))))
