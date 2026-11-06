;;; The checker, in FX-26: flat data (`TODO.md` §77): which types are flat,
;;; their layouts and sizes, the views and blobrefs of them. Apart from
;;; `check-read-helpers.fx` since 2026-10-31 (`TODO.md` §188), which is given
;;; it and gives on what its clients use.
;;; A file of one expression (`load-input`, `TODO.md` §68), which the
;;; conductor applies to the modules it is given, as `check-read-helpers.fx`.


;; Its types, those it uses of the files before it, and the signatures of
;; what it is given.
(let* ((check-types-types (load-module "fx26:check-types-types.fx"))
       (check-read-types (load-module "fx26:check-read-types.fx"))
       (check-env-types (load-module "fx26:check-env-types.fx"))
       (check-subst-types (load-module "fx26:check-subst-types.fx"))
       (eager-reader-types ((proj (load-module "fx26:eager-reader-types.fx") @s @e @m @c)))
       (parser-types ((proj (load-module "fx26:parser-types.fx") @s @e @m @c @p)))
       (check-print-types (load-module "fx26:check-print-types.fx"))
       (check-print-parts-types (load-module "fx26:check-print-parts-types.fx"))
       (check-syntax-types (load-module "fx26:check-syntax-types.fx"))
       (check-effects-types (load-module "fx26:check-effects-types.fx"))
       (reader-types (load-module "fx26:reader-types.fx")))
  ;; What it is given: the modules of the files before it that it uses.
  (lambda ((check-types (select check-types-types check-types-sig))
           (check-read (select check-read-types check-read-sig))
           (check-env (select check-env-types check-env-sig))
           (check-subst (select check-subst-types check-subst-sig))
           (check-print (select check-print-types check-print-sig))
           (check-syntax (select check-syntax-types check-syntax-sig))
           (check-effects (select check-effects-types check-effects-sig))
           (parser (select reader-types parser-sig))
           (check-print-parts (select check-print-parts-types check-print-parts-sig)))
    (module

;; The types it uses of the files before it.
(hide (include check-types-types) (include check-read-types) (include check-env-types)
      (include check-subst-types) (include eager-reader-types) (include parser-types))
;; What it uses of the modules it is given: all of each, hidden.
(hide (include check-types) (include check-syntax) (include check-print-parts) (include check-env)
      (include check-subst) (include check-print) (include parser))
(import check-read k-atom-head? k-sfail k-items k-any-typed-kind? k-arrow-syntax)
(import check-effects k-one k-insert)

;; A flat (`TODO.md` §77): the scalars' names, whose bytes a `blobref`
;; reads as a value of the type of the same name.
(define k-flat-scalar? (->* (symbol) bool)
  (lambda (s)
    (or (symbol=? s 'f64) (symbol=? s 'f32) (symbol=? s 'i32) (symbol=? s 'u32)
        (symbol=? s 'i64) (symbol=? s 'u64))))
(define k-flat-usage string
  (string-append "a flat is `f64`, `f32`, `i32`, `u32`, `i64`, `u64`, "
                 (k-cat3 "`(productof (label flat) …)`, `(sumof [key] (label flat) …)`, "
                         "`(arrayof flat n)`, " "or a variable of kind `flat`")))
;; What a flat named `n` where a type is wanted is told.
(define k-flat-not-type (->* (string) string)
  (lambda (n) (string-append "`" n "` is a flat, not a type")))
;; Whether `t` is a variable of kind `flat`.
(define k-flat-var-type? (->* (int) bool)
  (lambda (t) (tagcase (k-get (k-resolve t)) (ty-var (v) (k-flat-var? v)) (else y #f))))
;; Whether `t` is a flat: a scalar, or a variable of kind `flat`.
(define k-is-flat? (->* (int) bool)
  (lambda (t)
    (tagcase (k-get (k-resolve t))
      (ty-base (s) (k-flat-scalar? s))
      (ty-var (v) (k-flat-var? v))
      (ty-product (ps) (k-flat-parts? ps))
      (ty-sum (ps) (k-flat-parts? ps))
      (ty-named (g ds) (or (= g k-flat-arrayof-gen) (= g k-flat-keyed-gen)))
      (else y #f))))
(define k-flat-parts? (->* (k-parts) bool)
  (lambda (ps) (or (null? ps) (and (k-is-flat? (extract (car ps) 2)) (k-flat-parts? (cdr ps))))))
;; A flat, as written (`Checker::parse_flat`): a scalar's name, as the type
;; its bytes are read as; or a variable of kind `flat`, or a family's flat
;; parameter.
(define k-parse-flat (->* (syn) int)
  (lambda (s)
    (if (not (null? (k-list-items s)))
        (k-parse-flat-list s (k-list-items s))
    (if (syn-symbol? s)
        (let* ((sym (syn-head s)) (d (k-lookup-desc sym)))
          (if (null? d)
              (if (k-flat-scalar? sym) (k-ty-new (ty-base sym)) (k-sfail k-flat-usage s))
              (tagcase (car d)
                (ds-var (v k) (if (= k 7) (k-ty-new (ty-var v)) (k-sfail k-flat-usage s)))
                ;; A type named, read as a flat: its parts as `productof` and
                ;; `sumof` would have them (`TODO.md` §77).
                (ds-rec (t)
                  (if (k-is-flat? t)
                      (let ((why (k-flat-parts-wrong t))) (if (string=? why "") t (k-sfail why s)))
                      (k-sfail k-flat-usage s)))
                (else x (k-sfail k-flat-usage s)))))
        (k-sfail k-flat-usage s)))))
;; A list's items, or none for what is no list (or an empty one).
(define k-list-items (->* (syn) k-syns)
  (lambda (s) (tagcase s (lst (items d a b) items) (else x nil))))
;; `(productof (label flat) …)`, its fields laid out in the order written;
;; or `(arrayof flat n)`, `n` a literal length (`Checker::parse_flat_list`).
(define k-parse-flat-list (->* (syn k-syns) int)
  (lambda (s items)
    (let ((hd (if (syn-symbol? (car items)) (syn-name (car items)) "")))
      (cond ((string=? hd "productof")
             (let* ((parts (k-parse-flat-parts (cdr items) nil 0))
                    (bad (k-unsized-before-last parts (cdr items) nil)))
               (if (null? bad)
                   (k-ty-new (ty-product parts))
                   (k-sfail (string-append "only a flat product's last part may be of a length not "
                                           "known: it runs to the end of the suffix")
                            (car bad)))))
            ((string=? hd "sumof") (k-parse-flat-sum (cdr items)))
            ;; A length a literal; or a size, which runs to the end of the
            ;; suffix (`TODO.md` §77).
            ((and (string=? hd "arrayof") (= (k-length items) 3))
             (let ((f (k-parse-flat (k-nth items 1))) (n (k-nth items 2)))
               (if (not (k-flat-sized? f))
                   (k-sfail "a flat array's element has a length of its own" (k-nth items 1))
                   (let ((z (k-parse-size n)))
                     (if (tagcase z
                           (sz-lin (k ts) (and (null? ts) (or (< k 0) (>= k 268435455))))
                           (else y #f))
                         (k-sfail "a flat array's literal length is 0 to 268435454" n)
                         (k-ty-new (ty-named k-flat-arrayof-gen (list (dt f) (dz z)))))))))
            (else (k-sfail k-flat-usage s))))))
(define k-parse-flat-parts (->* (k-syns k-parts int) k-parts)
  (lambda (ps done w)
    (if (null? ps)
        (reverse done)
        (let ((pair (k-items (car ps) "`(label flat)`")))
          (if (= (k-length pair) 2)
              (let ((l (k-syn-label (car pair))))
                (cond ((k-has-label? done l) (k-sfail (k-twice (symbol->string l)) (car ps)))
                      ((and (> w 0) (not (k-digits-below? (symbol->string l) 0 0 (k-key-limit w))))
                       (k-sfail (k-cat5 "a label of a sum keyed by `u" (int->string (* 8 w))
                                        "` is a number below 2^" (int->string (* 8 w)) "")
                                (car pair)))
                      (else
                       (let ((f (k-parse-flat (k-nth pair 1))))
                         (k-parse-flat-parts (cdr ps) (cons (product (1 l) (2 f)) done) w)))))
              (k-sfail "`(label flat)`" (car ps)))))))
;; `(sumof [key] (label flat) …)`: a key first, a width, if the labels are numbers stored as they
;; are; else the tag indexes the owner's fields, which hold the labels (`TODO.md` §77).
(define k-parse-flat-sum (->* (k-syns) int)
  (lambda (ps)
    (let* ((w (if (and (not (null? ps)) (syn-symbol? (car ps))) (k-key-width (car ps)) 0))
           (written (if (= w 0) ps (cdr ps)))
           (parts (k-parse-flat-parts written nil w))
           (bad (k-unsized-first parts written)))
      (cond ((not (null? bad)) (k-sfail "a flat sum's variant has a length of its own" (car bad)))
            ((= w 0) (k-ty-new (ty-sum parts)))
            (else
             (k-ty-new (ty-named k-flat-keyed-gen
                                 (list (dz (k-size-lit w)) (dt (k-ty-new (ty-sum parts)))))))))))
;; What is wrong with flat `t`'s parts, "" if nothing (`Checker::flat_parts_wrong`).
(define k-flat-parts-wrong (->* (int) string)
  (lambda (t)
    (tagcase (k-get (k-resolve t))
      (ty-product (ps)
        (if (k-unsized-before-last? ps)
            (string-append "only a flat product's last part may be of a length not known: it runs "
                           "to the end of the suffix")
            ""))
      (ty-sum (ps) (if (k-any-unsized? ps) "a flat sum's variant has a length of its own" ""))
      (else y ""))))
(define k-unsized-before-last? (->* (k-parts) bool)
  (lambda (ps)
    (and (not (null? ps)) (not (null? (cdr ps)))
         (or (not (k-flat-sized? (extract (car ps) 2))) (k-unsized-before-last? (cdr ps))))))
(define k-any-unsized? (->* (k-parts) bool)
  (lambda (ps)
    (and (not (null? ps))
         (or (not (k-flat-sized? (extract (car ps) 2))) (k-any-unsized? (cdr ps))))))
;; The first of `parts`, written `ps`, of a length not known: its syntax.
(define k-unsized-first (->* (k-parts k-syns) k-syns)
  (lambda (parts ps)
    (cond ((null? parts) nil)
          ((not (k-flat-sized? (extract (car parts) 2))) (the k-syns (cons (car ps) nil)))
          (else (k-unsized-first (cdr parts) (cdr ps))))))
;; The last of `parts` before the last, written `ps`, of a length not known,
;; `found` so far: its syntax.
(define k-unsized-before-last
  (->* (k-parts k-syns k-syns) k-syns)
  (lambda (parts ps found)
    (cond ((or (null? parts) (null? (cdr parts))) found)
          ((not (k-flat-sized? (extract (car parts) 2)))
           (k-unsized-before-last (cdr parts) (cdr ps) (the k-syns (cons (car ps) nil))))
          (else (k-unsized-before-last (cdr parts) (cdr ps) found)))))
(define k-key-width (->* (syn) int)
  (lambda (k)
    (case (syn-name k)
      (("u8") 1) (("u16") 2) (("u32") 4)
      (else (k-sfail "a flat sum's key is `u8`, `u16` or `u32`" k)))))
(define k-key-limit (->* (int) int)
  (lambda (w) (case w ((1) 256) ((2) 65536) (else 4294967296))))
;; Whether `s` from `i` is a number's digits, `n` so far, below `limit`.
(define k-digits-below? (->* (string int int int) bool)
  (lambda (s i n limit)
    (cond ((>= n limit) #f)
          ((= i (string-length s)) (> i 0))
          ((and (char>=? (string-ref s i) #\0) (char<=? (string-ref s i) #\9))
           (k-digits-below? s (+ i 1) (+ (* n 10) (- (char->integer (string-ref s i)) 48)) limit))
          (else #f))))

;; `blobref`, standard generative type 5 (`check::BLOBREF_INDEX`); a flat
;; array, 6 (`check::FLAT_ARRAYOF_INDEX`); a flat sum with a key, 7.
(define k-blobref-gen int 5)
(define k-flat-arrayof-gen int 6)
(define k-flat-keyed-gen int 7)
;; A scalar flat's layout (`fixpt_heap::layout::FLAT_*`), or -1.
(define k-flat-code (->* (symbol) int)
  (lambda (s)
    (case (symbol->string s)
      (("i32") 0) (("u32") 1) (("i64") 2) (("u64") 3) (("f32") 4) (("f64") 5) (else -1))))
(define-type k-int-pair (pairof int int @t))
;; `n` rounded up to a multiple of `a`.
(define k-round-up (->* (int int) int)
  (lambda (n a) (* (quotient (+ n (- a 1)) a) a)))
;; A flat's size and alignment in bytes (`Checker::flat_layout`); -1s for
;; one whose layout is not known.
(define k-flat-layout (->* (int) k-int-pair)
  (lambda (t)
    (tagcase (k-get (k-resolve t))
      (ty-base (s)
        (case (symbol->string s)
          (("i32" "u32" "f32") (cons 4 4)) (("i64" "u64" "f64") (cons 8 8)) (else (cons -1 -1))))
      (ty-product (ps) (k-flat-parts-layout ps 0 1))
      (ty-sum (ps) (k-flat-sum-size t))
      (ty-named (g ds)
        (let ((p (k-flat-array-parts t)))
          (if (= g k-flat-keyed-gen)
              (k-flat-sum-size t)
          (if (or (< (car p) 0) (not (k-flat-sized? t)))
              (cons -1 -1)
              (let ((e (k-flat-layout (car p))))
                (if (< (car e) 0) e (cons (* (car e) (cdr p)) (cdr e))))))))
      (else y (cons -1 -1)))))
(define k-flat-parts-layout (->* (k-parts int int) k-int-pair)
  (lambda (ps at align)
    (if (null? ps)
        (cons (k-round-up at align) align)
        (let ((l (k-flat-layout (extract (car ps) 2))))
          (if (< (car l) 0)
              l
              (k-flat-parts-layout (cdr ps) (+ (k-round-up at (cdr l)) (car l))
                                   (if (> (cdr l) align) (cdr l) align)))))))
;; Flat product `t`'s field `l`: its offset in bytes, and its flat; -1s if
;; none (`Checker::flat_field`).
(define k-flat-field (->* (int symbol) k-int-pair)
  (lambda (t l)
    (tagcase (k-get (k-resolve t))
      (ty-product (ps) (k-flat-field-from ps l 0))
      (else y (cons -1 -1)))))
(define k-flat-field-from (->* (k-parts symbol int) k-int-pair)
  (lambda (ps l at)
    (if (null? ps)
        (cons -1 -1)
        (let ((a (k-flat-align (extract (car ps) 2))))
          (cond ((< a 0) (cons -1 -1))
                ;; The last may be of a length not known: its offset is not.
                ((symbol=? (extract (car ps) 1) l) (cons (k-round-up at a) (extract (car ps) 2)))
                (else
                 (let ((e (k-flat-layout (extract (car ps) 2))))
                   (if (< (car e) 0)
                       (cons -1 -1)
                       (k-flat-field-from (cdr ps) l (+ (k-round-up at a) (car e)))))))))))
;; A flat's alignment in bytes, known whether or not its size is; -1 if not
;; known (`Checker::flat_align`).
(define k-flat-align (->* (int) int)
  (lambda (t)
    (tagcase (k-get (k-resolve t))
      (ty-product (ps) (k-parts-align ps 1))
      (ty-named (g ds)
        (if (= g k-flat-arrayof-gen)
            (let ((p (k-flat-array-parts t))) (if (< (car p) 0) -1 (k-flat-align (car p))))
            (cdr (k-flat-layout t))))
      (else y (cdr (k-flat-layout t))))))
(define k-parts-align (->* (k-parts int) int)
  (lambda (ps a)
    (if (null? ps)
        a
        (let ((b (k-flat-align (extract (car ps) 2))))
          (if (< b 0) -1 (k-parts-align (cdr ps) (if (> b a) b a)))))))
;; The length of the array of a length not known that flat `t` is, or ends
;; in: none if `t` has a size of its own (`TODO.md` §77).
(define k-unsized-length (->* (int) (listof k-size acyclic))
  (lambda (t)
    (tagcase (k-get (k-resolve t))
      (ty-named (g ds)
        (if (and (= g k-flat-arrayof-gen) (= (k-length ds) 2))
            (tagcase (car (cdr ds))
              (dz (z) (tagcase z
                        (sz-lin (k ts) (if (null? ts) nil (the (listof k-size acyclic) (list z))))
                        (else y (the (listof k-size acyclic) (list z)))))
              (else y nil))
            nil))
      (ty-product (ps) (if (null? ps) nil (k-unsized-length (extract (k-last-part ps) 2))))
      (else y nil))))
(define k-last-part (->* (k-parts) (productof (1 symbol) (2 int)))
  (lambda (ps) (if (null? (cdr ps)) (car ps) (k-last-part (cdr ps)))))
(define k-flat-sized? (->* (int) bool)
  (lambda (t) (null? (k-unsized-length t))))
;; Flat `t` with the length of the array of a length not known that it is,
;; or ends in, `z`.
(define k-with-unsized-length (->* (int k-size) int)
  (lambda (t z)
    (tagcase (k-get (k-resolve t))
      (ty-named (g ds)
        (tagcase (car ds)
          (dt (f) (k-ty-new (ty-named k-flat-arrayof-gen (list (dt f) (dz z)))))
          (else y t)))
      (ty-product (ps) (k-ty-new (ty-product (k-with-last-part ps z))))
      (else y t))))
(define k-with-last-part (->* (k-parts k-size) k-parts)
  (lambda (ps z)
    (if (null? (cdr ps))
        (the k-parts
             (list (product (1 (extract (car ps) 1))
                            (2 (k-with-unsized-length (extract (car ps) 2) z)))))
        (cons (car ps) (k-with-last-part (cdr ps) z)))))
;; Flat array `t`'s element and length, 268435455 (`FLAT_TO_THE_END`) for
;; one that runs to the end of the suffix; -1s if it is none.
(define k-flat-array-parts (->* (int) k-int-pair)
  (lambda (t)
    (tagcase (k-get (k-resolve t))
      (ty-named (g ds)
        (if (and (= g k-flat-arrayof-gen) (= (k-length ds) 2))
            (tagcase (car ds)
              (dt (f)
                (tagcase (car (cdr ds))
                  (dz (z) (tagcase z (sz-lin (k ts) (if (null? ts) (cons f k) (cons f 268435455)))
                            (else y (cons f 268435455))))
                  (else y (cons -1 -1))))
              (else y (cons -1 -1)))
            (cons -1 -1)))
      (else y (cons -1 -1)))))
;; A flat sum's variants, its key's width in bytes (-1 if `t` is no flat
;; sum), and whether its labels are numbers (`Checker::flat_sum_parts`).
(define-type k-sum-parts (productof (1 k-parts) (2 int) (3 bool)))
(define k-no-sum k-sum-parts (product (1 (the k-parts nil)) (2 -1) (3 #f)))
(define k-flat-sum-parts (->* (int) k-sum-parts)
  (lambda (t)
    (tagcase (k-get (k-resolve t))
      (ty-sum (ps) (if (k-flat-parts? ps) (product (1 ps) (2 1) (3 #f)) k-no-sum))
      (ty-named (g ds)
        (if (and (= g k-flat-keyed-gen) (= (k-length ds) 2))
            (tagcase (car ds)
              (dz (z)
                (tagcase z
                  (sz-lin (k ts)
                    (tagcase (car (cdr ds))
                      (dt (s) (tagcase (k-get (k-resolve s))
                                (ty-sum (ps) (product (1 ps) (2 k) (3 #t)))
                                (else y k-no-sum)))
                      (else y k-no-sum)))
                  (else y k-no-sum)))
              (else y k-no-sum))
            k-no-sum))
      (else y k-no-sum))))
;; A flat sum's code for the compilers, size, alignment and variants
;; (`Checker::flat_sum_layout`): the tag, `w` bytes, then the variant at the
;; widest one's alignment, at `p`; the code `w + 8 * numeric + 256 * p`, or
;; -1 if `t` is no flat sum or its layout is not known.
(define-type k-sum-layout (productof (1 int) (2 int) (3 int) (4 k-parts)))
(define k-no-layout k-sum-layout (product (1 -1) (2 -1) (3 -1) (4 (the k-parts nil))))
(define k-flat-sum-layout (->* (int) k-sum-layout)
  (lambda (t)
    (let ((p (k-flat-sum-parts t)))
      (if (< (extract p 2) 0)
          k-no-layout
          (k-sum-layout-of (extract p 1) (extract p 2) (extract p 3) (extract p 1) 0 1)))))
(define k-sum-layout-of
  (->* (k-parts int bool k-parts int int) k-sum-layout)
  (lambda (ps w numeric all size align)
    (if (null? ps)
        (let ((p (k-round-up w align)) (al (if (> w align) w align)))
          (product (1 (+ (+ w (if numeric 8 0)) (* 256 p))) (2 (k-round-up (+ p size) al)) (3 al)
                   (4 all)))
        (let ((l (k-flat-layout (extract (car ps) 2))))
          (if (< (car l) 0)
              k-no-layout
              (k-sum-layout-of (cdr ps) w numeric all (if (> (car l) size) (car l) size)
                               (if (> (cdr l) align) (cdr l) align)))))))
(define k-flat-sum-size (->* (int) k-int-pair)
  (lambda (t)
    (let ((l (k-flat-sum-layout t)))
      (if (< (extract l 1) 0) (cons -1 -1) (cons (extract l 2) (extract l 3))))))
;; A `tagcase`, `at`, whose scrutinee is of type and effect `rs`: if a
;; blobref to a flat sum (`TODO.md` §77), seen as a sum of blobrefs to its
;; variants, its tag read from the owner's region, and its layout's code
;; noted for the compilers; else `rs`.
(define k-flat-view (->* (k-at k-te) k-te)
  (lambda (at rs)
    (let* ((st (extract rs 1)) (p (k-blobref-parts st))
           (l (if (null? p) k-no-layout (k-flat-sum-layout (cdr (car p))))))
      (if (< (extract l 1) 0)
          rs
          (let* ((b (car (car p))) (r (k-owner-region (extract at 1) (extract at 2) st b)))
            (begin
              (set k-extracts
                   (cons (product (1 at) (2 (n-datum (datum-layout (extract l 1)))))
                         (get k-extracts)))
              (k-te (k-ty-new (ty-sum (k-blobref-variants b (extract l 4))))
                    (k-insert (a-read r) (extract rs 2)))))))))
(define k-blobref-variants (->* (int k-parts) k-parts)
  (lambda (b ps)
    (if (null? ps)
        nil
        (let* ((v (product (1 (extract (car ps) 1)) (2 (k-blobref-of b (extract (car ps) 2)))))
               (rest (k-blobref-variants b (cdr ps))))
          (the k-parts (cons v rest))))))
;; What a `tagcase`'s `else` binds, its scrutinee of type `st`, the variants
;; `rest` not named: the blobref as it is, to a flat sum; else their sum.
(define k-else-type (->* (int k-parts) int)
  (lambda (st rest)
    (let ((p (k-blobref-parts st)))
      (if (and (not (null? p)) (>= (extract (k-flat-sum-layout (cdr (car p))) 1) 0))
          st
          (k-ty-new (ty-sum rest))))))
;; The region of blobref type `xt`'s owner, `b`, at `a`..`z`.
(define k-owner-region (->* (int int int int) k-region)
  (lambda (a z xt b)
    (tagcase (k-get (k-resolve b))
      (ty-bloblet (fs fz r) r)
      (else y (k-fail (k-cat3 "the region of a " (k-show-ty xt) "'s owner is not known") a z)))))
;; `body`'s type and effect with `y` bound to `t`, by `synth-as` (the
;; checker's knot), against `expected` if given (≥ 0).
(define-type k-synth-as-knot (subr (maxeff checks spin) (kx int) k-te))
(define k-in-scope-check (->* (symbol int kx int k-synth-as-knot) k-te)
  (lambda (y t body expected synth-as)
    (let ((saved (k-mark)))
      (begin
        (k-bind y t)
        (let ((r (synth-as body expected)))
          (begin (k-unbind-to saved) r))))))
;; `body`, at `ba`..`bb`, its type and effect with `ps` bound, the first
;; first, by `synth-as` (the checker's knot), against `expected` if given
;; (≥ 0): a `with`'s body, at `a`..`b`, of which an error at the body is
;; said, so that a call's argument's is the argument's (`Checker::with_as`).
(define k-in-scope-parts
  (->* (k-parts kx int k-synth-as-knot int int int int) k-te)
  (lambda (ps body expected synth-as a b ba bb)
    (let ((saved (k-mark)))
      (begin
        (k-bind-each ps)
        (let ((r (if (< expected 0)
                     (synth-as body expected)
                     (k-respanning (lambda () (synth-as body expected)) ba bb a b))))
          (begin (k-unbind-to saved) r))))))
;; `f`, an error at `a`..`b` said at `ta`..`tb` instead, any other as it is.
(define k-respanning
  (->* ((subr (maxeff checks spin) () k-te) int int int int) k-te)
  (lambda (f a b ta tb)
    (let ((r (prompt k-tag (k-done (f)) (lambda (r) r))))
      (tagcase r
        (k-done (te) te)
        (k-err (m ea eb) (if (and (= ea a) (= eb b)) (k-fail m ta tb) (k-fail m ea eb)))
        (k-ok (xs) (k-fail "k-ok inside" a b))))))
(define k-bind-each (->* (k-parts) unit)
  (lambda (ps)
    (if (null? ps)
        #u
        (begin (k-bind (extract (car ps) 1) (extract (car ps) 2)) (k-bind-each (cdr ps))))))
;; `blobref-variant!` at `a`..`z` of the flat sum `f` a blobref of type `xt`
;; and owner `b` points to, its label `lx` at `la`..`lz`: a blobref to the
;; variant, of effect `e` and the owner's region read and written; the
;; layout's code noted for the compilers (`Checker::synth_blobref`).
(define k-blobref-variant
  (->* (int int int int int int int kx int int k-eff) k-te)
  (lambda (a z k kr xt b f lx la lz e)
    (let* ((l (k-flat-sum-layout f)) (code (extract l 1)) (label (k-variant-label lx code)))
      (if (null? label)
          (k-fail (string-append "a variant is named by a literal: `'label`, or a number where "
                                 "the sum has a key")
                  la lz)
          (let ((g (k-part-find (extract l 4) (car label))))
            (if (< g 0)
                (k-fail (k-cat5 "a " (k-show-ty f) " has no variant `" (symbol->string (car label))
                                "`")
                        la lz)
                (let ((r (k-owner-region a z xt b)))
                  (begin
                    (set k-extracts
                         (cons (product (1 (product (1 a) (2 z) (3 k) (4 kr)))
                                        (2 (n-datum (datum-layout code))))
                               (get k-extracts)))
                    (k-te (k-blobref-of b g) (k-insert (a-write r) (k-insert (a-read r) e)))))))))))
;; A `blobref-variant!`'s label, `lx`, for a sum of layout `code`: a number
;; where the sum has a key, else a name, as `check-modules-read.fx`'s
;; `k-label-const` resolves it (its value -1, its name the type's); none if
;; it is neither.
(define k-variant-label (->* (kx int) (listof symbol acyclic))
  (lambda (lx code)
    (tagcase lx
      (x-const (t n c d cdk cdkr)
        (cond ((= (modulo (quotient code 8) 2) 1)
               (if (= t k-int) (list (string->symbol (int->string n))) nil))
              ((or (= t k-int) (not (= n -1))) nil)
              (else (tagcase (k-get t) (ty-base (s) (list s)) (else y nil)))))
      (else y nil))))
;; `(blobref b f)`'s owner and flat, if `t` is one.
(define-type k-owner-flat (listof (pairof int int @t) acyclic))
(define k-blobref-parts (->* (int) k-owner-flat)
  (lambda (t)
    (tagcase (k-get (k-resolve t))
      (ty-named (g ds)
        (if (and (= g k-blobref-gen) (= (k-length ds) 2))
            (tagcase (car ds)
              (dt (b) (tagcase (car (cdr ds)) (dt (f) (list (cons b f))) (else y nil)))
              (else y nil))
            nil))
      (else y nil))))
(define k-blobref-of (->* (int int) int)
  (lambda (b f) (k-ty-new (ty-named k-blobref-gen (list (dt b) (dt f)))))))))
