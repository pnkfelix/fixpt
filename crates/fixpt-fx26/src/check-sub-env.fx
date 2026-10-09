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
(define-type k-benv (select check-subtype-types k-benv))
(define-type k-assumed (select check-subtype-types k-assumed))
(define-type k-strail (select check-subtype-types k-strail))
(define-type k-label-entry (select check-subtype-types k-label-entry))
(define-type k-label-list (select check-subtype-types k-label-list))
(define-type k-labels (select check-subtype-types k-labels))
;; The types it uses of the files before it.
(define a-alloc (with check-types-types a-alloc))
(define a-app (with check-types-types a-app))
(define a-await (with check-types-types a-await))
(define a-comefrom (with check-types-types a-comefrom))
(define a-goto (with check-types-types a-goto))
(define a-read (with check-types-types a-read))
(define a-spin (with check-types-types a-spin))
(define a-var (with check-types-types a-var))
(define a-write (with check-types-types a-write))
(define cv-fx (with check-types-types cv-fx))
(define cv-var (with check-types-types cv-var))
(define dc (with check-types-types dc))
(define de (with check-types-types de))
(define dr (with check-types-types dr))
(define-type k-conv (select check-types-types k-conv))
(define-type k-descs (select check-types-types k-descs))
(define-type k-eff (select check-types-types k-eff))
(define-type k-parts (select check-types-types k-parts))
(define-type k-region (select check-types-types k-region))
(define-effect kreads (select check-types-types kreads))
(define-effect kstate (select check-types-types kstate))
(define r-frozen (with check-types-types r-frozen))
(define r-var (with check-types-types r-var))
(define ty-param (with check-types-types ty-param))
(define ty-select (with check-types-types ty-select))
(define-effect kmakes (select check-subst-types kmakes))
(define-type table (select table-types table))
;; What it uses of the modules it is given.
(define k-get (with check-types k-get))
(define k-length (with check-types k-length))
(define k-conv=? (with check-print-parts k-conv=?))
(define k-region=? (with check-effects k-region=?))
(define make-table (with tables make-table))
(define table-ref (with tables table-ref))
(define table-set! (with tables table-set!))
(define drop (with parser drop))

;; Base `x` below base `y`: the same, or an `i32` or `u32`, the fixnum it
;; stands for, below `int`. As the Rust checker's rule.
(define k-base-below? (subr (read @globals) (symbol symbol) bool)
  (lambda (x y)
    (or (symbol=? x y)
        (and (string=? (symbol->string y) "int")
             (or (string=? (symbol->string x) "i32") (string=? (symbol->string x) "u32"))))))

(define k-bool=? (subr pure (bool bool) bool) (lambda (x y) (if x y (not y))))
(define k-part-find (subr kreads (k-parts symbol) int)
  (lambda (ps l)
    (cond ((null? ps) -1)
          ((symbol=? (extract (car ps) 1) l) (extract (car ps) 2))
          (else (k-part-find (cdr ps) l)))))

(define k-benv-var (subr kreads (k-benv int) int)
  (lambda (env v)
    (cond ((null? env) v)
          ((= (car (car env)) v) (cdr (car env)))
          (else (k-benv-var (cdr env) v)))))
;; Whether binders `x` and `y` stand for the same, each by its side's
;; environment.
(define k-benv-var=? (subr kreads (int int k-benv k-benv) bool)
  (lambda (x y ea eb) (= (k-benv-var ea x) (k-benv-var eb y))))
;; Whether a procedure called in convention `a` may be used as one called
;; in `b`: the same, or any of FX-26's own as `fx`; binders by the binders
;; they stand for.
(define k-conv-sub? (subr kreads (k-conv k-conv k-benv k-benv) bool)
  (lambda (a b ea eb)
    (tagcase a
      (cv-var (x) (tagcase b (cv-var (y) (k-benv-var=? x y ea eb)) (else z #f)))
      (else y (or (k-conv=? a b) (tagcase b (cv-fx () #t) (else z #f)))))))
;; Whether two conventions are the same, binders by what they stand for.
(define k-conv-same? (subr kreads (k-conv k-conv k-benv k-benv) bool)
  (lambda (a b ea eb)
    (tagcase a
      (cv-var (x) (tagcase b (cv-var (y) (k-benv-var=? x y ea eb)) (else z #f)))
      (else y (k-conv=? a b)))))
;; `env` with `v` named `l`, in place of any name it had: re-entering a scope
;; shadows it, so the environments stay finitely many.
(define k-benv-set (subr kmakes (k-benv int int) k-benv)
  (lambda (env v l)
    (letrec ((drop (subr kmakes (k-benv) k-benv)
               (lambda (e)
                 (cond ((null? e) nil)
                       ((= (car (car e)) v) (cdr e))
                       (else (cons (car e) (drop (cdr e))))))))
      (the k-benv (cons (the (pairof int int @t) (cons v l)) (drop env))))))
(define k-benv-within? (subr kreads (k-benv k-benv) bool)
  (lambda (x y)
    (or (null? x)
        (and (= (k-benv-var y (car (car x))) (cdr (car x))) (k-benv-within? (cdr x) y)))))
(define k-benv=? (subr kreads (k-benv k-benv) bool)
  (lambda (x y) (and (= (k-length x) (k-length y)) (k-benv-within? x y))))
;; `a ≤ b` for frozen data: the same, or finite data seen as possibly
;; cyclic, in one place.
(define k-frozen-le? (subr (maxeff (read @globals) spin) (k-region k-region) bool)
  (lambda (a b)
    (or (k-region=? a b)
        (tagcase a
          (r-frozen (p f) (and f (tagcase b (r-frozen (q g) (and (= p q) (not g))) (else y #f))))
          (else y #f)))))
(define k-benv-region (subr kreads (k-benv k-region) k-region)
  (lambda (env r)
    (if (null? env)
        r
        (tagcase r
          (r-var (v) (r-var (k-benv-var env v)))
          (r-frozen (p f) (if (< p 0) r (r-frozen (k-benv-var env p) f)))
          (else y r)))))
;; Whether regions `r` and `s` are the same, each by its side's environment.
(define k-benv-region=? (subr (maxeff kreads spin) (k-region k-region k-benv k-benv) bool)
  (lambda (r s ea eb) (k-region=? (k-benv-region ea r) (k-benv-region eb s))))
;; `r ≤ s` for frozen data, each by its side's environment.
(define k-benv-frozen-le? (subr (maxeff kreads spin) (k-region k-region k-benv k-benv) bool)
  (lambda (r s ea eb) (k-frozen-le? (k-benv-region ea r) (k-benv-region eb s))))
;; Whether `g` is the `x` of a dependent procedure's `k`th parameter.
(define k-param-is? (subr (maxeff kreads spin) (int int symbol) bool)
  (lambda (g k x) (tagcase (k-get g) (ty-param (j y) (and (= k j) (symbol=? x y))) (else z #f))))
;; Whether `g` is `(select m x)` as written.
(define k-select-is? (subr (maxeff kreads spin) (int symbol symbol) bool)
  (lambda (g m x)
    (tagcase (k-get g) (ty-select (n y) (and (symbol=? m n) (symbol=? x y))) (else z #f))))
;; Convention `c` by an environment.
(define k-benv-conv (subr kreads (k-benv k-conv) k-conv)
  (lambda (env c) (tagcase c (cv-var (v) (cv-var (k-benv-var env v))) (else y c))))
(define-rec
  (k-benv-effect (subr (maxeff kmakes spin) (k-benv k-eff) k-eff)
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
                    (a-spin () x)
                    (a-var (v) (a-var (k-benv-var env v)))
                    ;; Its variable, and what it was given, as named here.
                    (a-app (v ds) (a-app (k-benv-var env v) (k-benv-eargs env ds))))
                  rest)))))
  (k-benv-eargs (subr (maxeff kmakes spin) (k-benv k-descs) k-descs)
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
;; How many entries of the trails of the questions open name each pair of
;; nodes (by `k-strail-key`, which two pairs may share): a pair named by
;; none is not assumed, known at once, where looking along the trail grew
;; with every pair a question compared (a module against its signature).
(define k-strail-count (ref (table int int @t) @t)
  (new (make-table (lambda ((n int)) n) (lambda ((m int) (n int)) (= m n)))))
(define k-strail-key (subr pure (int int) int) (lambda (a b) (+ (* a 65599) b)))
(define k-strail-bump (subr kstate (int int int) unit)
  (lambda (a b d)
    (let ((k (k-strail-key a b)))
      (table-set! (get k-strail-count) k (+ d (table-ref (get k-strail-count) k 0))))))
;; `a ≤ b` assumed, in `ea` and `eb`.
(define k-strail-push (subr kstate (k-strail int int k-benv k-benv) unit)
  (lambda (trail a b ea eb)
    (begin (k-strail-bump a b 1)
           (set trail (cons (product (1 a) (2 b) (3 ea) (4 eb)) (get trail))))))
;; The entries of `ps` newer than `st` no longer counted.
(define k-strail-drop (subr (maxeff kstate spin) (k-assumed k-assumed) unit)
  (lambda (ps st)
    (if (or (null? ps) (eq? ps st))
        #u
        (begin (k-strail-bump (extract (car ps) 1) (extract (car ps) 2) -1)
               (k-strail-drop (cdr ps) st)))))
(define k-strail-in? (subr kreads (k-assumed int int k-benv k-benv) bool)
  (lambda (ps a b ea eb)
    (and (not (null? ps))
         (or (let ((p (car ps)))
               (and (= (extract p 1) a) (= (extract p 2) b)
                    (k-benv=? (extract p 3) ea) (k-benv=? (extract p 4) eb)))
             (k-strail-in? (cdr ps) a b ea eb)))))
(define k-strail-has? (subr kreads (k-assumed int int k-benv k-benv) bool)
  (lambda (ps a b ea eb)
    (and (> (table-ref (get k-strail-count) (k-strail-key a b) 0) 0)
         (k-strail-in? ps a b ea eb))))
;; Put a subtype question's memory back as it was: trail `st`, labels `sl`.
(define k-restore (subr (maxeff kstate spin) (k-strail k-labels k-assumed k-label-list) unit)
  (lambda (trail labels st sl)
    (begin (k-strail-drop (get trail) st) (set trail st) (set labels sl))))
;; Whether label entry `x` is for the binders at position `i` of nodes `a`
;; and `b`.
(define k-label-of? (subr pure (k-label-entry int int int) bool)
  (lambda (x a b i) (and (= (extract x 1) a) (= (extract x 2) b) (= (extract x 3) i))))
(define k-label (subr kstate (k-labels int int int) int)
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
              (begin (set labels (cons (product (1 a) (2 b) (3 i) (4 l)) (get labels))) l))))))))))
