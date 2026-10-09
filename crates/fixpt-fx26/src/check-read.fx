;;; The checker, in FX-26: syntax read, and the pieces descriptions are read
;;; from it with (names, kinds, regions, atoms); and what `(select m e)`, read
;;; as an effect, stands for. `check-syntax.fx` reads descriptions with them,
;;; after it (split from it, 2026-10-05). Part of the checker,
;;; `check-types.fx` first (PLAN.md §11, step 10).

;;; ------------------------------------------------------------ reading syntax

;; Its types, those it uses of the files before it, and the signatures of
;; what it is given.
;; Its types (`check-read-types.fx`), loaded before the module so that they are not
;; among its values; the module names what it uses of them.
(let* ((check-read-types (load-module "fx26:check-read-types.fx"))
       (check-types-types (load-module "fx26:check-types-types.fx"))
       (eager-reader-types ((proj (load-module "fx26:eager-reader-types.fx") @s @e @m @c)))
       (parser-types ((proj (load-module "fx26:parser-types.fx") @s @e @m @c @p)))
       (check-effects-types (load-module "fx26:check-effects-types.fx"))
       (check-print-types (load-module "fx26:check-print-types.fx"))
       (check-print-parts-types (load-module "fx26:check-print-parts-types.fx"))
       (check-env-types (load-module "fx26:check-env-types.fx"))
       (reader-types (load-module "fx26:reader-types.fx")))
  ;; What it is given: the modules of the files before it that it uses.
  (lambda ((check-types (select check-types-types check-types-sig))
           (check-effects (select check-effects-types check-effects-sig))
           (check-print (select check-print-types check-print-sig))
           (check-env (select check-env-types check-env-sig))
           (parser (select reader-types parser-sig))
           (check-print-parts (select check-print-parts-types check-print-parts-sig)))
    (module
(define-type k-syns (select check-read-types k-syns))
(define-type k-arrow-syns (select check-read-types k-arrow-syns))
(define-type k-params (select check-read-types k-params))
(define-type k-effect-sels (select check-read-types k-effect-sels))
;; The types it uses of the files before it.
(define a-alloc (with check-types-types a-alloc))
(define a-await (with check-types-types a-await))
(define a-comefrom (with check-types-types a-comefrom))
(define a-goto (with check-types-types a-goto))
(define a-read (with check-types-types a-read))
(define a-spin (with check-types-types a-spin))
(define a-var (with check-types-types a-var))
(define a-write (with check-types-types a-write))
(define-effect checks (select check-types-types checks))
(define de (with check-types-types de))
(define ds-eff (with check-types-types ds-eff))
(define ds-region (with check-types-types ds-region))
(define ds-var (with check-types-types ds-var))
(define-type k-atom (select check-types-types k-atom))
(define-type k-binders (select check-types-types k-binders))
(define-type k-eff (select check-types-types k-eff))
(define-type k-ids (select check-types-types k-ids))
(define-type k-region (select check-types-types k-region))
(define-type k-regions (select check-types-types k-regions))
(define-effect kbuilds (select check-types-types kbuilds))
(define-effect kreads (select check-types-types kreads))
(define-effect kstate (select check-types-types kstate))
(define r-const (with check-types-types r-const))
(define r-frozen (with check-types-types r-frozen))
(define r-global (with check-types-types r-global))
(define r-globals (with check-types-types r-globals))
(define r-heap (with check-types-types r-heap))
(define r-var (with check-types-types r-var))
(define ty-lam (with check-types-types ty-lam))
(define-type k-items (select check-types-types k-items))
(define lst (with eager-reader-types lst))
(define-type result (select eager-reader-types result))
(define-type syn (select parser-types syn))
;; What it uses of the modules it is given.
(define k-arrow (with check-types k-arrow))
(define k-bounds (with check-types k-bounds))
(define k-cat3 (with check-types k-cat3))
(define k-cat5 (with check-types k-cat5))
(define k-copy-array (with check-types k-copy-array))
(define k-fail (with check-types k-fail))
(define k-length (with check-types k-length))
(define k-new-dvar-of (with check-types k-new-dvar-of))
(define k-nth (with check-types k-nth))
(define k-quote (with check-types k-quote))
(define k-ty-new (with check-types k-ty-new))
(define k-tys (with check-types k-tys))
(define k-insert (with check-effects k-insert))
(define k-one (with check-effects k-one))
(define k-kind-text (with check-print-parts k-kind-text))
(define k-place? (with check-print-parts k-place?))
(define k-region-show (with check-print-parts k-region-show))
(define k-lookup-desc (with check-env k-lookup-desc))
(define k-push-desc (with check-env k-push-desc))
(define syn-end (with parser syn-end))
(define syn-head (with parser syn-head))
(define syn-name (with parser syn-name))
(define syn-start (with parser syn-start))
(define syn-symbol? (with parser syn-symbol?))

(define k-sfail (subr checks (string syn) void)
  (lambda (m s) (k-fail m (syn-start s) (syn-end s))))
(define k-items (subr checks (syn string) k-syns)
  (lambda (s what)
    (tagcase s
      (lst (items d a b) items)
      (else x (k-sfail (string-append what ": expected a list") s)))))
(define k-head (subr (maxeff (read @globals) (read @s)) (k-syns) string)
  (lambda (items) (if (null? items) "" (syn-name (car items)))))
;; The name at the head of `items`, or "" if they do not start with one.
(define k-symbol-head (subr (maxeff (read @globals) (read @s)) (k-syns) string)
  (lambda (items)
    (if (and (not (null? items)) (syn-symbol? (car items))) (syn-name (car items)) "")))
(define k-name-of (subr checks (syn string) symbol)
  (lambda (s what) (if (syn-symbol? s) (syn-head s) (k-sfail what s))))
(define k-at-name? (subr pure (string) bool)
  (lambda (n) (and (> (string-length n) 0) (string=? (substring n 0 1) "@"))))
(define k-nil-syn? (subr (read @s) (syn) bool)
  (lambda (s) (tagcase s (lst (items d a b) (null? items)) (else x #f))))
;; The items of a list that may be written `()`.
(define k-items-or-nil (subr checks (syn string) k-syns)
  (lambda (s what) (if (k-nil-syn? s) nil (k-items s what))))

;; Whether kind `k` describes values, or makes what does: a type, data, or
;; a description function (which may give one).
(define k-typed-kind? (subr pure (int) bool)
  (lambda (k) (or (= k 2) (= k 4) (>= k 100))))
(define k-any-typed-kind? (subr (read @globals) (k-ids) bool)
  (lambda (ks) (and (not (null? ks)) (or (k-typed-kind? (car ks)) (k-any-typed-kind? (cdr ks))))))

;; What a kind is, what a description function gives, and what one to an
;; effect takes, as errors say.
(define k-kind-usage string
  "a kind is `region`, `place`, `effect`, `type`, `data`, `size`, `conv` or `(=> (kind …) kind)`")
(define k-fun-result-usage string
  "a description function gives a type, an effect, or another description function")
(define k-effect-fun-usage string
  "a description function to an effect takes regions, places, effects, sizes and conventions")
(define k-arrow-syntax (subr (maxeff kreads (read @s) (alloc @t) spin) (syn) k-arrow-syns)
  (lambda (s)
    (let ((items (tagcase s (lst (items d a b) items) (else x (the k-syns nil)))))
      (if (and (= (k-length items) 3) (string=? (k-symbol-head items) "=>"))
          (tagcase (k-nth items 1)
            (lst (ps d a b)
              (if (null? ps) nil (the k-arrow-syns (list (cons ps (k-nth items 2))))))
            (else x nil))
          nil))))
(define-rec
  (k-parse-kind (subr (maxeff checks spin) (syn) int)
    (lambda (s)
      (let ((n (if (syn-symbol? s) (syn-name s) ""))
            (usage k-kind-usage))
        (case n (("region") 0)
                (("place") 3)
                (("effect") 1)
                (("type") 2)
                (("data") 4)
                (("size") 5)
                (("conv") 6)
                (else
                 (cond ((syn-symbol? s) (k-sfail usage s))
                       (else (k-parse-arrow-kind s usage))))))))
  ;; `(=> (k1 … kn) k)`: a description function's kind (`check-kinds.fx`).
  (k-parse-arrow-kind (subr (maxeff checks spin) (syn string) int)
    (lambda (s usage)
      (let ((parts (k-arrow-syntax s)))
        (if (null? parts)
            (k-sfail usage s)
            (let* ((last (cdr (car parts)))
                   (params (k-parse-kinds (car (car parts))))
                   (result (k-parse-kind last)))
              (cond ((or (= result 0) (= result 3) (= result 5) (= result 6))
                     (k-sfail k-fun-result-usage last))
                    ((and (= result 1) (k-any-typed-kind? params))
                     (k-sfail k-effect-fun-usage s))
                    (else (k-arrow params result))))))))
  (k-parse-kinds (subr (maxeff checks spin) (k-syns) k-ids)
    (lambda (xs)
      (if (null? xs)
          nil
          (let* ((k (k-parse-kind (car xs))) (rest (k-parse-kinds (cdr xs))))
            (the k-ids (cons k rest)))))))

;; What `name`, a description function, says written where a type is.
(define k-not-applied (subr (maxeff kreads (alloc @t) spin) (string int) string)
  (lambda (n k)
    (k-cat5 (k-quote n) " is a description function, of kind " (k-kind-text k)
            ": it is applied, " (k-quote (k-cat3 "(" n " …)")))))
(define k-ctor-params (subr (read @globals) (string) (listof k-params acyclic))
  (lambda (n)
    (letrec ((one (subr (read @globals) (symbol int) k-params)
                  (lambda (x k) (the k-params (cons (product (1 x) (2 k)) nil)))))
      ;; Type `x` and region `r`.
      (let ((typed (lambda ((x symbol)) (the k-params (cons (product (1 x) (2 2)) (one 'r 0))))))
        (case n (("ref" "icell" "listof" "arrayof" "mark-key")
                 (the (listof k-params acyclic) (cons (typed 't) nil)))
                (("pairof")
                 (the (listof k-params acyclic)
                      (cons (the k-params (cons (product (1 'a) (2 2)) (typed 'b))) nil)))
                (else nil))))))
;; `@globals`, or `(globals g …)` as the regions of each `g`, in a list of
;; one; none if `s` is neither.
(define k-global-names (subr (maxeff checks spin) (k-syns) k-regions)
  (lambda (ns)
    (if (null? ns)
        nil
        (let ((g (k-name-of (car ns) "a global's name")))
          (the k-regions (cons (r-global g) (k-global-names (cdr ns))))))))
;; `rs`, alone in a list.
(define k-regions-alone (subr pure (k-regions) (listof k-regions acyclic))
  (lambda (rs) (the (listof k-regions acyclic) (cons rs nil))))
(define k-globals-region (subr (maxeff checks spin) (syn) (listof k-regions acyclic))
  (lambda (s)
    (if (syn-symbol? s)
        (if (string=? (syn-name s) "@globals")
            (k-regions-alone (the k-regions (cons (r-globals) nil)))
            nil)
        (let ((items (k-items-or-nil s "a region")))
          (if (string=? (k-symbol-head items) "globals")
              (if (null? (cdr items))
                  (k-sfail "`(globals name …)`: at least one global" s)
                  (k-regions-alone (k-global-names (cdr items))))
              nil)))))
;; Each of `rs`, read (or written).
(define k-atoms-on (subr kbuilds (bool k-regions) k-eff)
  (lambda (read rs)
    (if (null? rs)
        nil
        (k-insert (if read (a-read (car rs)) (a-write (car rs))) (k-atoms-on read (cdr rs))))))
;; The region `@name` stands for: the constant of that name.
(define k-region-constant (subr (maxeff kreads (alloc @t)) (symbol) k-region)
  (lambda (sym) (r-const sym)))
;; The region a name stands for.
(define k-region-named (subr (maxeff checks spin) (syn) k-region)
  (lambda (s)
    (let* ((n (syn-name s)) (sym (string->symbol n)))
      (cond ((k-at-name? n) (k-region-constant sym))
            ((string=? n "const") (r-frozen -1 #f))
            ((string=? n "acyclic") (r-frozen -1 #t))
            ((string=? n "finite")
             (k-sfail "`finite` is a size; data with no cycle through it is at `acyclic`" s))
            ((string=? n "heap") (r-heap))
            (else
             (let ((d (k-lookup-desc sym))
                   (no (lambda () (string-append (k-quote n) " is not a region"))))
               (if (null? d)
                   (k-sfail (no) s)
                   (tagcase (car d)
                     (ds-var (v k) (if (or (= k 0) (= k 3)) (r-var v) (k-sfail (no) s)))
                     (ds-region (r) r)
                     (else x (k-sfail (no) s))))))))))
;; The region of data frozen into place `p`: `(acyclic p)` if `f`, else
;; `(const p)`.
(define k-frozen-into (subr (read @globals) (k-region bool) k-region)
  (lambda (p f) (tagcase p (r-var (v) (r-frozen v f)) (else y (r-frozen -1 f)))))
;; What a region that is not a place says.
(define k-not-place (subr kreads (k-region) string)
  (lambda (r) (string-append (k-quote (k-region-show r)) " is not a place")))

(define-rec
  (k-parse-region (subr (maxeff checks spin) (syn) k-region)
    (lambda (s)
      (cond ((not (null? (k-globals-region s)))
             (k-sfail (string-append "globals are a region only in effects: "
                                     "`(read @globals)`, `(write (globals g))`")
                      s))
            ((syn-symbol? s) (k-region-named s))
            (else (k-parse-frozen s)))))
  ;; `(const p)`: data frozen into place `p`; `(acyclic p)`, and never
  ;; written, so with no cycle through it.
  (k-parse-frozen (subr (maxeff checks spin) (syn) k-region)
    (lambda (s)
      (let* ((items (k-items-or-nil s "a region")) (head (k-symbol-head items)))
        (if (and (= (k-length items) 2) (or (string=? head "const") (string=? head "acyclic")))
            (let ((p (k-parse-place (k-nth items 1))) (f (string=? head "acyclic")))
              (k-frozen-into p f))
            (k-sfail "expected a region" s)))))
  ;; A place: a region that is one.
  (k-parse-place (subr (maxeff checks spin) (syn) k-region)
    (lambda (s)
      (let ((r (k-parse-region s)))
        (if (k-place? r) r (k-sfail (k-not-place r) s))))))

;; What a binder may be.
(define k-binder-shapes string
  (string-append "a binder is `(name kind)`, `(name region place)` "
                 "or `(name data place)`"))
;; A binder's bound, none or one, from what follows its kind: `(r region
;; p)` is a region that won't outlive `p`, a place bound before it.
(define k-parse-bound (subr (maxeff checks spin) (k-syns int) k-regions)
  (lambda (rest kind)
    (cond ((null? rest) (the k-regions nil))
          ((or (= kind 0) (= kind 4)) (the k-regions (cons (k-parse-place (car rest)) nil)))
          (else (k-sfail (string-append "only a region or data binder has a bound: "
                                        "`(name region place)` or `(name data place)`")
                         (car rest))))))
;; Note region variable `v`'s bound, if it has one.
(define k-note-bound (subr kstate (int k-regions) unit)
  (lambda (v bound)
    (if (null? bound) #u (set k-bounds (cons (cons v (car bound)) (get k-bounds))))))
(define k-binders-each (subr (maxeff checks spin) (k-syns) k-binders)
  (lambda (bs)
    (if (null? bs)
        nil
        (let ((pair (k-items (car bs) "a binder")))
          (if (or (= (k-length pair) 2) (= (k-length pair) 3))
              (let* ((name (k-name-of (car pair) "a binder's name"))
                     (kind (k-parse-kind (k-nth pair 1)))
                     (bound (k-parse-bound (cdr (cdr pair)) kind))
                     (v (k-new-dvar-of name kind))
                     (bounded (k-note-bound v bound))
                     (pushed (k-push-desc name (ds-var v kind)))
                     (rest (k-binders-each (cdr bs))))
                (cons (product (1 v) (2 kind)) rest))
              (k-sfail k-binder-shapes (car bs)))))))

;; `((name kind) …)`, binding each name for the rest of the reading.
(define k-parse-binders (subr (maxeff checks spin) (syn) k-binders)
  (lambda (s) (k-binders-each (k-items s "binders"))))

;; The effect a name stands for.
(define k-effect-named (subr (maxeff checks spin) (syn) k-eff)
  (lambda (s)
    (let ((n (syn-name s)))
      (case n (("pure") nil)
              (("spin") (k-one (a-spin)))
              (else
               (let ((d (k-lookup-desc (string->symbol n)))
                     (no (lambda () (string-append (k-quote n) " is not an effect"))))
                 (if (null? d)
                     (k-sfail (no) s)
                     (tagcase (car d)
                       (ds-var (v k) (if (= k 1) (k-one (a-var v)) (k-sfail (no) s)))
                       (ds-eff (e) e)
                       (else x (k-sfail (no) s))))))))))
;; Whether `h` heads an atom of effect on a region: `(read r)` and so on.
(define k-atom-head? (subr pure (string) bool)
  (lambda (h)
    (or (string=? h "read") (string=? h "write") (string=? h "alloc")
        (string=? h "goto") (string=? h "comefrom") (string=? h "await"))))
;; The atom `(head r)`, `head` one `k-atom-head?` accepts.
(define k-atom-of (subr (read @globals) (string k-region) k-atom)
  (lambda (head r)
    (case head (("read") (a-read r))
               (("write") (a-write r))
               (("alloc") (a-alloc r))
               (("goto") (a-goto r))
               (("await") (a-await r))
               (else (a-comefrom r)))))

(define k-effect-selects (ref k-effect-sels @t) (new nil))
;; The entry for `(select m e)` in `ss`, or none.
(define k-effect-sel-find (subr (maxeff (read @globals) (read @t)) (k-effect-sels symbol symbol)
                                k-effect-sels)
  (lambda (ss m e)
    (cond ((null? ss) nil)
          ((and (symbol=? (extract (car ss) 1) m) (symbol=? (extract (car ss) 2) e)) ss)
          (else (k-effect-sel-find (cdr ss) m e)))))
;; The variable `(select m e)` read as an effect stands for, named as written.
(define k-effect-select (subr (maxeff kstate spin) (symbol symbol) int)
  (lambda (m e)
    (let ((found (k-effect-sel-find (get k-effect-selects) m e)))
      (if (null? found)
          (let* ((shown (k-cat5 "(select " (symbol->string m) " " (symbol->string e) ")"))
                 (v (k-new-dvar-of (string->symbol shown) 1)))
            (begin (set k-effect-selects (cons (product (1 m) (2 e) (3 v)) (get k-effect-selects)))
                   v))
          (extract (car found) 3)))))
;; A module's description of an effect, `(define-effect e E)`'s: a
;; description function of no parameters giving it.
(define k-effect-desc (subr (maxeff kstate spin) (k-eff) int)
  (lambda (e) (k-ty-new (ty-lam nil (de e)))))
;; `(select m e)` as an effect, in a list: the variable for it.
(define k-effect-selected (subr (maxeff checks spin) (syn k-syns) (listof k-eff acyclic))
  (lambda (s items)
    (if (and (= (k-length items) 3) (syn-symbol? (k-nth items 1)) (syn-symbol? (k-nth items 2)))
        (let ((m (syn-head (k-nth items 1))) (e (syn-head (k-nth items 2))))
          (the (listof k-eff acyclic) (list (k-one (a-var (k-effect-select m e))))))
        (begin (k-sfail "`(select module name)`: a module's name, and a component's" s) nil))))

;;; ------------------------------------------------------------ types kept as themselves

;; While a type's `select`s are resolved (`k-resolve-selects`): its nodes
;; that lead to none, each kept as itself rather than rebuilt by the
;; substitution, so that what the type shares with others, a named type,
;; it still shares. Marked in an array of their own, a walk's epoch each
;; (`k-new-epoch`), as `k-visit?` marks: `k-subst-keep` the epoch of those
;; kept, or -1. As the Rust checker's `subst_keep`.
(define k-keep-marks (ref (arrayof int @t) @t) (new (make-array 512 0)))
(define k-subst-keep (ref int @t) (new -1))
;; Type `t`'s mark, the marks grown to hold it.
(define k-keep-at (subr (maxeff kstate spin) (int) int)
  (lambda (t)
    (begin
      (if (>= t (array-length (get k-keep-marks)))
          (let ((bigger (the (arrayof int @t) (make-array (* 2 (array-length (get k-tys))) 0))))
            (begin (k-copy-array (get k-keep-marks) bigger 0) (set k-keep-marks bigger)))
          #u)
      (array-ref (get k-keep-marks) t))))
(define k-keep-set! (subr (maxeff kstate spin) (int int) unit)
  (lambda (t e) (begin (k-keep-at t) (array-set! (get k-keep-marks) t e)))))))
