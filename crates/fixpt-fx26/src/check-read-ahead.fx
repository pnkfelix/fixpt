;;; The checker, in FX-26: what a program declares ahead, its simple
;;; `define-type`s read before the rest: which forms are read in order (a
;;; type that names a file), the names given, those given more than once
;;; (a warning), and where a top-level `include` ends what is declared
;;; ahead. Apart from `check-read-descs.fx` since 2026-10-31 (`TODO.md`
;;; §188), which makes it of the modules it is given and gives on all it
;;; defines.
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
(import check-read-made k-type-made-by k-restrict-by k-param-selects-given)
(import check-read k-at-name? k-atom-head? k-ctor-params k-effect-desc k-effect-named
        k-effect-selected k-frozen-into k-head k-items k-items-or-nil k-name-of k-not-applied
        k-parse-binders k-parse-place k-parse-region k-region-constant k-sfail k-symbol-head)
(import check-effects k-one k-union)
(import check-specs k-spec-clause? k-specified k-spec-pnames)

;; Whether top-level `form` is a `define-type` that names a file, its type
;; `(%type-made …)` or `(%input-made …)` (`load-moduleof`): read in order,
;; not ahead, as its file's hidden global is defined before it
;; (`declare_each`).
(define k-read-in-order? (->* (top) bool)
  (lambda (form)
    (tagcase form (t-define-type (name def a b) (k-names-a-file? def)) (else y #f))))
(define k-names-a-file? (->* (syn) bool)
  (lambda (s)
    (tagcase s
      (lst (items d a b)
        (let ((h (if (and (not (null? items)) (syn-symbol? (car items)))
                     (syn-name (car items))
                     "")))
          (or (string=? h "%type-made") (string=? h "%input-made") (string=? h "restrict")
              (k-any-names-a-file? items))))
      (else y #f))))
(define k-any-names-a-file? (->* (k-syns) bool)
  (lambda (xs)
    (and (not (null? xs)) (or (k-names-a-file? (car xs)) (k-any-names-a-file? (cdr xs))))))
;; A program's forms, and lines said of them (`check-program-types.fx`'s).
(define-type k-tops (listof top acyclic))
(define-type k-out (listof string acyclic))
;; The names simple `define-type`s give, in order, each as often as given;
;; if `stop?`, those before a top-level `include` (`k-included?`).
(define k-ahead-names-of (->* (k-tops k-names bool) k-names)
  (lambda (forms acc stop?)
    (if (or (null? forms) (and stop? (k-included? (car forms))))
        (the k-names (reverse acc))
        (k-ahead-names-of
         (cdr forms)
         (tagcase (car forms)
           (t-define-type (name def a b)
             (if (and (syn-symbol? name) (not (string=? (k-list-head def) "dlambda"))
                      (not (k-names-a-file? def)))
                 (cons (string->symbol (syn-name name)) acc)
                 acc))
           (else y acc))
         stop?))))
;; The names `ns` gives more than once, each once, in the order each is
;; given a second time.
(define k-given-again (->* (k-names k-names k-names) k-names)
  (lambda (ns seen again)
    (cond ((null? ns) (the k-names (reverse again)))
          ((not (k-has-name? seen (car ns))) (k-given-again (cdr ns) (cons (car ns) seen) again))
          ((k-has-name? again (car ns)) (k-given-again (cdr ns) seen again))
          (else (k-given-again (cdr ns) seen (cons (car ns) again))))))
;; A warning for each type a whole program defines more than once
;; (`TODO.md` §34): not an error, but its values see only the last.
(define k-again-lines (->* (k-names) k-out)
  (lambda (ns)
    (if (null? ns)
        nil
        (cons (k-cat3 "warning: `" (symbol->string (car ns))
                      "` is defined as a type more than once; every value sees the last")
              (k-again-lines (cdr ns))))))
;; Where a top-level `include` ended what is declared ahead (`k-included?`),
;; or -1: a type or effect defined after it is read in order.
(define k-ahead-stop (ref int @t) (new -1))
;; Whether `form` is where a top-level `include` was (`included-mark`).
(define k-included? (->* (top) bool)
  (lambda (form)
    (tagcase form
      (t-define-effect (name def a b)
        (and (syn-symbol? name) (string=? (syn-name name) "%included")))
      (else y #f))))
;; Where a type's or an effect's definition starts; -1 for any other form.
(define k-type-top-start (->* (top) int)
  (lambda (form)
    (tagcase form
      (t-define-type (n d a b) a) (t-define-effect (n d a b) a) (t-define-generative (h r a b) a)
      (t-define-convention (n f a b) a) (else y -1))))
;; Whether `form`, a type's or an effect's definition, is declared where it
;; is, not ahead: it names a file (`k-read-in-order?`), or is after a
;; top-level `include` (`declare_each`).
(define k-declared-later? (->* (top) bool)
  (lambda (form)
    (or (k-read-in-order? form)
        (let ((a (k-type-top-start form)))
          (and (>= a 0) (>= (get k-ahead-stop) 0) (>= a (get k-ahead-stop))))))))))
