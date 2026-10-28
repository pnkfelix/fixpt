;;; The checker, in FX-26: the memory of the subtype test, before
;;; `check-subtype.fx`. Base types compared; the environments of binders
;;; on each side, and conventions, regions and effects by them; the trail of
;;; questions open, counted by pair; and the labels of pairs of binders.

;; Its types, those it uses of the files before it, and the signatures of
;; what it is given.
;; Its types (`check-subtype-types.fx`, its file's after it), loaded before the
;; module so that they are not among its values; the module names what it
;; uses of them.
(let* ((check-subtype-types (load-module "fx26:check-subtype-types.fx"))
       (check-types-types (load-module "fx26:check-types-types.fx"))
       (check-subst-types (load-module "fx26:check-subst-types.fx"))
       (table-types (load-module "fx26:table-types.fx"))
       (check-print-types (load-module "fx26:check-print-types.fx"))
       (check-print-parts-types (load-module "fx26:check-print-parts-types.fx"))
       (check-effects-types (load-module "fx26:check-effects-types.fx"))
       (reader-types (load-module "fx26:reader-types.fx")))
  ;; What it is given: the modules of the files before it that it uses.
  (lambda ((check-types (select check-types-types check-types-sig))
           (check-print (select check-print-types check-print-sig))
           (check-effects (select check-effects-types check-effects-sig))
           (tables (select table-types tables-sig))
           (parser (select reader-types parser-sig))
           (check-print-parts (select check-print-parts-types check-print-parts-sig)))
    (module
(hide (include check-subtype-types) (include check-types-types) (include check-subst-types))
;; The types it uses of the files before it.
(define-type table (select table-types table))
;; What it uses of the modules it is given: all of each, hidden.
(hide (include check-types) (include check-print-parts) (include check-effects) (include tables)
      (include parser))

;; Base `x` below base `y`: the same, or an `i8`, `u8`, `i32` or `u32`, the
;; fixnum it stands for, or an `i64` or `u64`, the exact integer, below
;; `int`. As the Rust checker's rule.
(define k-base-below? (->* (symbol symbol) bool)
  (lambda (x y)
    (or (symbol=? x y)
        (and (string=? (symbol->string y) "int")
             (case (symbol->string x)
               (("i8" "u8" "i32" "u32" "i64" "u64") #t)
               (else #f))))))

(define k-bool=? (->* (bool bool) bool) (lambda (x y) (if x y (not y))))
(define k-part-find (->* (k-parts symbol) int)
  (lambda (ps l)
    (cond ((null? ps) -1)
          ((symbol=? (extract (car ps) 1) l) (extract (car ps) 2))
          (else (k-part-find (cdr ps) l)))))

(define k-benv-var (->* (k-benv int) int)
  (lambda (env v)
    (cond ((null? env) v)
          ((= (car (car env)) v) (cdr (car env)))
          (else (k-benv-var (cdr env) v)))))
;; Whether binders `x` and `y` stand for the same, each by its side's
;; environment.
(define k-benv-var=? (->* (int int k-benv k-benv) bool)
  (lambda (x y ea eb) (= (k-benv-var ea x) (k-benv-var eb y))))
;; Whether a procedure called in convention `a` may be used as one called
;; in `b`: the same, or any of FX-26's own as `fx`; binders by the binders
;; they stand for.
(define k-conv-sub? (->* (k-conv k-conv k-benv k-benv) bool)
  (lambda (a b ea eb)
    (tagcase a
      (cv-var (x) (tagcase b (cv-var (y) (k-benv-var=? x y ea eb)) (else z #f)))
      (else y (or (k-conv=? a b) (tagcase b (cv-fx () #t) (else z #f)))))))
;; Whether two conventions are the same, binders by what they stand for.
(define k-conv-same? (->* (k-conv k-conv k-benv k-benv) bool)
  (lambda (a b ea eb)
    (tagcase a
      (cv-var (x) (tagcase b (cv-var (y) (k-benv-var=? x y ea eb)) (else z #f)))
      (else y (k-conv=? a b)))))
;; `env` with `v` named `l`, in place of any name it had: re-entering a scope
;; shadows it, so the environments stay finitely many.
(define k-benv-set (->* (k-benv int int) k-benv)
  (lambda (env v l)
    (letrec ((drop (subr kmakes (k-benv) k-benv)
               (lambda (e)
                 (cond ((null? e) nil)
                       ((= (car (car e)) v) (cdr e))
                       (else (cons (car e) (drop (cdr e))))))))
      (the k-benv (cons (the (pairof int int @t) (cons v l)) (drop env))))))
(define k-benv-within? (->* (k-benv k-benv) bool)
  (lambda (x y)
    (or (null? x)
        (and (= (k-benv-var y (car (car x))) (cdr (car x))) (k-benv-within? (cdr x) y)))))
(define k-benv=? (->* (k-benv k-benv) bool)
  (lambda (x y) (and (= (k-length x) (k-length y)) (k-benv-within? x y))))
;; `a ≤ b` for frozen data: the same, or finite data seen as possibly
;; cyclic; and covariant in the order of lifetimes (Kayak's, 2026-10-28),
;; at a place that outlives the one expected, the heap every place, as
;; nothing writes frozen data (`Checker::frozen_le`).
(define k-frozen-le? (->* (k-region k-region) bool)
  (lambda (a b)
    (or (k-region=? a b)
        (tagcase a
          (r-frozen (p f)
            (tagcase b (r-frozen (q g) (and (or f (not g)) (k-place-outlives? p q))) (else y #f)))
          (else y #f)))))
;; Whether place `p` outlives place `q` (-1 the heap): the same, the heap,
;; or one bound around `q`'s binder, which `q` won't outlive.
(define k-place-outlives? (->* (int int) bool)
  (lambda (p q) (or (= p -1) (= p q) (and (>= q 0) (k-has-id? (k-outer-of q) p)))))
(define k-benv-region (->* (k-benv k-region) k-region)
  (lambda (env r)
    (if (null? env)
        r
        (tagcase r
          (r-var (v) (r-var (k-benv-var env v)))
          (r-frozen (p f) (if (< p 0) r (r-frozen (k-benv-var env p) f)))
          (else y r)))))
;; Whether regions `r` and `s` are the same, each by its side's environment.
(define k-benv-region=? (->* (k-region k-region k-benv k-benv) bool)
  (lambda (r s ea eb) (k-region=? (k-benv-region ea r) (k-benv-region eb s))))
;; `r ≤ s` for frozen data, each by its side's environment.
(define k-benv-frozen-le? (->* (k-region k-region k-benv k-benv) bool)
  (lambda (r s ea eb) (k-frozen-le? (k-benv-region ea r) (k-benv-region eb s))))
;; Whether `g` is the `x` of a dependent procedure's `k`th parameter.
(define k-param-is? (->* (int int symbol) bool)
  (lambda (g k x) (tagcase (k-get g) (ty-param (j y) (and (= k j) (symbol=? x y))) (else z #f))))
;; Whether `g` is `(select m x)` as written.
(define k-select-is? (->* (int symbol symbol) bool)
  (lambda (g m x)
    (tagcase (k-get g) (ty-select (n y) (and (symbol=? m n) (symbol=? x y))) (else z #f))))
;; Convention `c` by an environment.
(define k-benv-conv (->* (k-benv k-conv) k-conv)
  (lambda (env c) (tagcase c (cv-var (v) (cv-var (k-benv-var env v))) (else y c))))
(define-rec
  (k-benv-effect (->* (k-benv k-eff) k-eff)
    (lambda (env e)
      (if (or (null? env) (null? e))
          e
          (let ((x (car e)) (rest (k-benv-effect env (cdr e))))
            (cons (tagcase x
                    (a-read (r) (a-read (k-benv-region env r)))
                    (a-write (r) (a-write (k-benv-region env r)))
                    (a-alloc (r) (a-alloc (k-benv-region env r)))
                    (a-goto (r) (a-goto (k-benv-region env r)))
                    (a-comefrom (r) (a-comefrom (k-benv-region env r)))
                    (a-await (r) (a-await (k-benv-region env r)))
                    (a-init (r) (a-init (k-benv-region env r)))
                    (a-send (r) (a-send (k-benv-region env r)))
                    (a-receive (r) (a-receive (k-benv-region env r)))
                    (a-spin () x)
                    (a-nondet () x)
                    (a-io (k) x)
                    (a-var (v) (a-var (k-benv-var env v)))
                    ;; Its variable, and what it was given, as named here.
                    (a-app (v ds) (a-app (k-benv-var env v) (k-benv-eargs env ds))))
                  rest)))))
  (k-benv-eargs (->* (k-benv k-descs) k-descs)
    (lambda (env ds)
      (if (null? ds)
          nil
          (let* ((d (tagcase (car ds)
                      (dr (r) (dr (k-benv-region env r)))
                      (de (e) (de (k-benv-effect env e)))
                      (dc (c) (dc (k-benv-conv env c)))
                      (else y (car ds))))
                 (rest (k-benv-eargs env (cdr ds))))
            (the k-descs (cons d rest)))))))
;; The entries of the trails of the questions open, by the pair of nodes each
;; names (`k-strail-key`, which two pairs may share), newest first: each
;; with the depth of its question (`k-question`), its pair and its
;; environments. Questions nest, and each drops what it pushed, newest
;; first, before the one around it goes on, so the newest entry of a key is
;; the next one dropped; and whether a pair is assumed in the question
;; asking is a look at its key's own entries, those of its depth, not along
;; its trail, which grew with every pair the question compared (a module
;; against its signature).
(define-type k-strail-entry (productof (1 int) (2 int) (3 int) (4 k-benv) (5 k-benv)))
(define k-strail-index (ref (table int (listof k-strail-entry @t) @t) @t)
  (new (make-table (lambda ((n int)) n) (lambda ((m int) (n int)) (= m n)))))
(define k-strail-key (->* (int int) int) (lambda (a b) (+ (* a 65599) b)))
;; How deep the questions open are: the one asking is the deepest.
(define k-question (ref int @t) (new 0))
(define k-question-begin! (->* () unit) (lambda () (set k-question (+ (get k-question) 1))))
(define k-question-end! (->* () unit) (lambda () (set k-question (- (get k-question) 1))))
;; `a ≤ b` assumed, in `ea` and `eb`.
(define k-strail-push (->* (k-strail int int k-benv k-benv) unit)
  (lambda (trail a b ea eb)
    (let ((k (k-strail-key a b)))
      (begin
        (table-set! (get k-strail-index) k
                    (cons (product (1 (get k-question)) (2 a) (3 b) (4 ea) (5 eb))
                          (table-ref (get k-strail-index) k nil)))
        (set trail (cons (product (1 a) (2 b) (3 ea) (4 eb)) (get trail)))))))
;; The entries of `ps` newer than `st` dropped from the index: each the
;; newest of its key's.
(define k-strail-drop (->* (k-assumed k-assumed) unit)
  (lambda (ps st)
    (if (or (null? ps) (eq? ps st))
        #u
        (let ((k (k-strail-key (extract (car ps) 1) (extract (car ps) 2))))
          (begin (table-set! (get k-strail-index) k (cdr (table-ref (get k-strail-index) k nil)))
                 (k-strail-drop (cdr ps) st))))))
;; Whether `a ≤ b` is assumed in `ea` and `eb` by the question asking, whose
;; trail is `ps`: among its key's entries, those of its depth, the first.
(define k-strail-has? (->* (k-assumed int int k-benv k-benv) bool)
  (lambda (ps a b ea eb)
    (letrec ((in? (->* ((listof k-strail-entry @t)) bool)
                   (lambda (es)
                     (and (pair? es)
                          (= (extract (car es) 1) (get k-question))
                          (or (let ((e (car es)))
                                (and (= (extract e 2) a) (= (extract e 3) b)
                                     (k-benv=? (extract e 4) ea) (k-benv=? (extract e 5) eb)))
                              (in? (cdr es)))))))
      (in? (table-ref (get k-strail-index) (k-strail-key a b) nil)))))
;; Put a subtype question's memory back as it was: trail `st`, labels `sl`.
(define k-restore (->* (k-strail k-labels k-assumed k-label-list) unit)
  (lambda (trail labels st sl)
    (begin (k-strail-drop (get trail) st) (set trail st) (set labels sl))))
;; Whether label entry `x` is for the binders at position `i` of nodes `a`
;; and `b`.
(define k-label-of? (->* (k-label-entry int int int) bool)
  (lambda (x a b i) (and (= (extract x 1) a) (= (extract x 2) b) (= (extract x 3) i))))
(define k-label (->* (k-labels int int int) int)
  (lambda (labels a b i)
    (letrec ((find (subr kreads (k-label-list) int)
               (lambda (ls)
                 (cond ((null? ls) 0)
                       ((k-label-of? (car ls) a b i) (extract (car ls) 4))
                       (else (find (cdr ls)))))))
      (let ((found (find (get labels))))
        (if (< found 0)
            found
            (let ((l (- -1000 (k-length (get labels)))))
              (begin (set labels (cons (product (1 a) (2 b) (3 i) (4 l)) (get labels))) l)))))))

;; Whether `r` is frozen data's region.
(define k-frozen-region? (->* (k-region) bool)
  (lambda (r) (tagcase r (r-frozen (p f) #t) (else y #f))))
;; Where data at region `r` is: the place it is frozen into, or the place or
;; region it was made at, or else the heap.
(define k-data-place (->* (k-region) k-region)
  (lambda (r)
    (tagcase r
      (r-frozen (p f) (if (< p 0) (r-heap) (r-var p)))
      (r-var (v) (r-var v))
      (else y (r-heap)))))
;; Where the data a `data` variable stands for is: its bound, or the heap.
(define k-data-var-place (->* (int) k-region)
  (lambda (v) (let ((b (k-bound-of v))) (if (null? b) (r-heap) (car b)))))
;; Whether data at `q` may be taken where data at `place` is wanted: `place`
;; empty for anywhere, or else the heap or the one place it holds.
(define k-data-here? (->* (k-regions k-region) bool)
  (lambda (place q) (or (null? place) (k-region=? q (r-heap)) (k-region=? q (car place)))))

;; Whether `t` is data: built only from base types, `datum`, products and
;; sums, and pairs and bloblets that are frozen, of data; and type variables
;; of kind `data`. With `place` naming one, each frozen part is also in the
;; heap or in that place.
(define-rec
  (k-data-walk (->* (int int k-regions) bool)
    (lambda (t seen place)
      (let ((t (k-resolve t)))
        (if (k-visit? t seen)
            #t
            (tagcase (k-get t)
              (ty-base (s) #t)
              (ty-void () #t)
              (ty-var (v) (and (k-data-var? v) (k-data-here? place (k-data-var-place v))))
              (ty-product (ps) (k-data-parts ps seen place))
              (ty-sum (ps) (k-data-parts ps seen place))
              (ty-nil () #t)
              (ty-union (ms) (k-data-list ms seen place))
              (ty-pair (a b r nl)
                (and (k-frozen-region? r) (k-data-here? place (k-data-place r))
                     (k-data-walk a seen place) (k-data-walk b seen place)))
              (ty-bloblet (fs z r)
                (and z (k-data-here? place (k-data-place r)) (k-data-list fs seen place)))
              (ty-nlist (e z r)
                (and (k-data-here? place (k-data-place r)) (k-data-walk e seen place)))
              (ty-nat (z) #t)
              (else y #f))))))
  (k-data-parts (->* (k-parts int k-regions) bool)
    (lambda (ps seen place)
      (or (null? ps)
          (and (k-data-walk (extract (car ps) 2) seen place) (k-data-parts (cdr ps) seen place)))))
  (k-data-list (->* (k-ids int k-regions) bool)
    (lambda (ts seen place)
      (or (null? ts) (and (k-data-walk (car ts) seen place) (k-data-list (cdr ts) seen place))))))
(define k-is-data? (->* (int) bool)
  (lambda (t) (k-data-walk t (k-new-epoch) nil)))
;; Whether `t` is data at `place`, a place variable or the heap.
(define k-is-data-at? (->* (int k-region) bool)
  (lambda (t place) (k-data-walk t (k-new-epoch) (the k-regions (cons place nil)))))
;; Whether a field of type `t` may be forgotten from a bloblet at region
;; `r`, frozen if `frozen`, as a bloblet type of fewer fields does
;; (`Checker::forgettable`): of a frozen bloblet, data at its place; of one
;; not frozen, what mentions no region but `r` and the heap, stores only in
;; `r`, and holds no procedure, nor a variable that could be one.
(define k-forgettable? (->* (int k-region bool) bool)
  (lambda (t r frozen)
    (if frozen (k-is-data-at? t (k-data-place r)) (k-forget-walk t r (k-new-epoch)))))
;; Frozen data's region `q`, as near as `r`: the heap's, or `r`'s place.
(define k-near? (->* (k-region k-region) bool)
  (lambda (q r)
    (tagcase q
      (r-heap () #t)
      (r-frozen (p f) (or (< p 0) (k-region=? (r-var p) r)))
      (else y (k-region=? q r)))))
;; A region `q` of storage, or of frozen data if `frozen`, as `r` allows.
(define k-forget-region? (->* (k-region k-region bool) bool)
  (lambda (q r frozen) (if frozen (k-near? q r) (k-region=? q r))))
(define-rec
  (k-forget-walk (->* (int k-region int) bool)
    (lambda (t r seen)
      (let ((t (k-resolve t)))
        (if (k-visit? t seen)
            #t
            (tagcase (k-get t)
              (ty-base (s) #t)
              (ty-nat (z) #t)
              (ty-void () #t)
              (ty-nil () #t)
              (ty-var (v) (and (k-data-var? v) (k-near? (k-data-var-place v) r)))
              (ty-ref (a q) (and (k-region=? q r) (k-forget-walk a r seen)))
              (ty-array (a nz q) (and (k-region=? q r) (k-forget-walk a r seen)))
              (ty-icell (a q) (and (k-region=? q r) (k-forget-walk a r seen)))
              (ty-pair (a b q nl)
                (and (k-forget-region? q r (k-frozen-region? q))
                     (k-forget-walk a r seen) (k-forget-walk b r seen)))
              (ty-bloblet (fs z q) (and (k-forget-region? q r z) (k-forget-list fs r seen)))
              (ty-product (ps) (k-forget-parts ps r seen))
              (ty-sum (ps) (k-forget-parts ps r seen))
              (ty-union (ms) (k-forget-list ms r seen))
              (ty-nlist (e z q) (and (k-near? q r) (k-forget-walk e r seen)))
              (else y #f))))))
  (k-forget-parts (->* (k-parts k-region int) bool)
    (lambda (ps r seen)
      (or (null? ps)
          (and (k-forget-walk (extract (car ps) 2) r seen) (k-forget-parts (cdr ps) r seen)))))
  (k-forget-list (->* (k-ids k-region int) bool)
    (lambda (ts r seen)
      (or (null? ts) (and (k-forget-walk (car ts) r seen) (k-forget-list (cdr ts) r seen))))))
)))
