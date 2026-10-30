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
(hide (include check-read-types) (include eager-reader-types) (include parser-types))
;; The types it uses of the files before it.
(import check-types-types a-alloc a-await a-comefrom a-goto a-read a-spin a-io a-init a-send
        a-receive a-nondet a-stage a-var a-write de ds-eff ds-region ds-var r-const r-frozen
        r-global r-globals r-heap r-var ty-lam
        (type k-atom k-binders k-eff k-names k-ids k-region k-regions k-items)
        (effect checks kbuilds kreads kstate))
;; What it uses of the modules it is given: all of each, hidden.
(hide (include check-types) (include check-env) (include check-print-parts) (include parser))
(import check-effects k-insert k-one k-union)

(define k-sfail (->* (string syn) void)
  (lambda (m s) (k-fail m (syn-start s) (syn-end s))))
(define k-items (->* (syn string) k-syns)
  (lambda (s what)
    (tagcase s
      (lst (items d a b) items)
      (else x (k-sfail (string-append what ": expected a list") s)))))
(define k-head (->* (k-syns) string)
  (lambda (items) (if (null? items) "" (syn-name (car items)))))
;; The name at the head of `items`, or "" if they do not start with one.
(define k-symbol-head (->* (k-syns) string)
  (lambda (items)
    (if (and (not (null? items)) (syn-symbol? (car items))) (syn-name (car items)) "")))
(define k-name-of (->* (syn string) symbol)
  (lambda (s what) (if (syn-symbol? s) (syn-head s) (k-sfail what s))))
(define k-at-name? (->* (string) bool)
  (lambda (n) (and (> (string-length n) 0) (string=? (substring n 0 1) "@"))))
(define k-nil-syn? (->* (syn) bool)
  (lambda (s) (tagcase s (lst (items d a b) (null? items)) (else x #f))))
;; The items of a list that may be written `()`.
(define k-items-or-nil (->* (syn string) k-syns)
  (lambda (s what) (if (k-nil-syn? s) nil (k-items s what))))

;; Whether kind `k` describes values, or makes what does: a type, data, or
;; a description function (which may give one).
(define k-typed-kind? (->* (int) bool)
  (lambda (k) (or (= k 2) (= k 4) (= k 8) (= k 7) (>= k 100))))
(define k-any-typed-kind? (->* (k-ids) bool)
  (lambda (ks) (and (not (null? ks)) (or (k-typed-kind? (car ks)) (k-any-typed-kind? (cdr ks))))))

;; What a kind is, what a description function gives, and what one to an
;; effect takes, as errors say.
(define k-kind-usage string
  (string-append "a kind is `region`, `place`, `effect`, `type`, `data`, `sendable`, `flat`, "
                 "`size`, `conv` or `(=> (kind …) kind)`"))
(define k-fun-result-usage string
  "a description function gives a type, an effect, or another description function")
(define k-effect-fun-usage string
  "a description function to an effect takes regions, places, effects, sizes and conventions")
(define k-arrow-syntax (->* (syn) k-arrow-syns)
  (lambda (s)
    (let ((items (tagcase s (lst (items d a b) items) (else x (the k-syns nil)))))
      (if (and (= (k-length items) 3) (string=? (k-symbol-head items) "=>"))
          (tagcase (k-nth items 1)
            (lst (ps d a b)
              (if (null? ps) nil (the k-arrow-syns (list (cons ps (k-nth items 2))))))
            (else x nil))
          nil))))
(define-rec
  (k-parse-kind (->* (syn) int)
    (lambda (s)
      (let ((n (if (syn-symbol? s) (syn-name s) ""))
            (usage k-kind-usage))
        (case n (("region") 0)
                (("place") 3)
                (("effect") 1)
                (("type") 2)
                (("data") 4)
                (("sendable") 8)
                (("flat") 7)
                (("size") 5)
                (("conv") 6)
                (else
                 (cond ((syn-symbol? s) (k-sfail usage s))
                       (else (k-parse-arrow-kind s usage))))))))
  ;; `(=> (k1 … kn) k)`: a description function's kind (`check-kinds.fx`).
  (k-parse-arrow-kind (->* (syn string) int)
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
  (k-parse-kinds (->* (k-syns) k-ids)
    (lambda (xs)
      (if (null? xs)
          nil
          (let* ((k (k-parse-kind (car xs))) (rest (k-parse-kinds (cdr xs))))
            (the k-ids (cons k rest)))))))

;; What `name`, a description function, says written where a type is.
(define k-not-applied (->* (string int) string)
  (lambda (n k)
    (k-cat5 (k-quote n) " is a description function, of kind " (k-kind-text k)
            ": it is applied, " (k-quote (k-cat3 "(" n " …)")))))
(define k-ctor-params (->* (string) (listof k-params acyclic))
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
(define k-global-names (->* (k-syns) k-regions)
  (lambda (ns)
    (if (null? ns)
        nil
        (let ((g (k-name-of (car ns) "a global's name")))
          (the k-regions (cons (r-global g) (k-global-names (cdr ns))))))))
;; `rs`, alone in a list.
(define k-regions-alone (->* (k-regions) (listof k-regions acyclic))
  (lambda (rs) (the (listof k-regions acyclic) (cons rs nil))))
(define k-globals-region (->* (syn) (listof k-regions acyclic))
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
(define k-atoms-on (->* (bool k-regions) k-eff)
  (lambda (read rs)
    (if (null? rs)
        nil
        (k-insert (if read (a-read (car rs)) (a-write (car rs))) (k-atoms-on read (cdr rs))))))
;; The region `@name` stands for: the constant of that name.
(define k-region-constant (->* (symbol) k-region)
  (lambda (sym) (r-const sym)))
;; The region a name stands for.
(define k-region-named (->* (syn) k-region)
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
(define k-frozen-into (->* (k-region bool) k-region)
  (lambda (p f) (tagcase p (r-var (v) (r-frozen v f)) (else y (r-frozen -1 f)))))
;; What a region that is not a place says.
(define k-not-place (->* (k-region) string)
  (lambda (r) (string-append (k-quote (k-region-show r)) " is not a place")))

(define-rec
  (k-parse-region (->* (syn) k-region)
    (lambda (s)
      (cond ((not (null? (k-globals-region s)))
             (k-sfail (string-append "globals are a region only in effects: "
                                     "`(read @globals)`, `(write (globals g))`")
                      s))
            ((syn-symbol? s) (k-region-named s))
            (else (k-parse-frozen s)))))
  ;; `(const p)`: data frozen into place `p`; `(acyclic p)`, and never
  ;; written, so with no cycle through it.
  (k-parse-frozen (->* (syn) k-region)
    (lambda (s)
      (let* ((items (k-items-or-nil s "a region")) (head (k-symbol-head items)))
        (if (and (= (k-length items) 2) (or (string=? head "const") (string=? head "acyclic")))
            (let ((p (k-parse-place (k-nth items 1))) (f (string=? head "acyclic")))
              (k-frozen-into p f))
            (k-sfail "expected a region" s)))))
  ;; A place: a region that is one.
  (k-parse-place (->* (syn) k-region)
    (lambda (s)
      (let ((r (k-parse-region s)))
        (if (k-place? r) r (k-sfail (k-not-place r) s))))))

;; What a binder may be.
(define k-binder-shapes string
  (string-append "a binder is `(name kind)`, `(name region place)` "
                 "or `(name data place)`, a region's perhaps `distinct` last"))
;; A binder's bound, none or one, from what follows its kind: `(r region
;; p)` is a region that won't outlive `p`, a place bound before it.
(define k-parse-bound (->* (k-syns int) k-regions)
  (lambda (rest kind)
    (cond ((null? rest) (the k-regions nil))
          ((or (= kind 0) (= kind 4)) (the k-regions (cons (k-parse-place (car rest)) nil)))
          (else (k-sfail (string-append "only a region or data binder has a bound: "
                                        "`(name region place)` or `(name data place)`")
                         (car rest))))))
;; Note region variable `v`'s bound, if it has one.
(define k-note-bound (->* (int k-regions) unit)
  (lambda (v bound)
    (if (null? bound) #u (set k-bounds (cons (cons v (car bound)) (get k-bounds))))))
(define k-binders-each (->* (k-syns) k-binders)
  (lambda (bs)
    (if (null? bs)
        nil
        (let* ((whole (k-items (car bs) "a binder"))
               ;; A region binder marked `distinct`, last (`Checker::
               ;; parse_binders`).
               (distinct (k-distinct-marked? whole))
               (pair (if distinct (k-drop-last whole) whole)))
          (if (or (= (k-length pair) 2) (= (k-length pair) 3))
              (let* ((name (k-name-of (car pair) "a binder's name"))
                     (kind (k-parse-kind (k-nth pair 1)))
                     (bound (k-parse-bound (cdr (cdr pair)) kind))
                     (v (if (and distinct (not (= kind 0)))
                            (k-sfail "only a region binder is `distinct`" (car bs))
                            (k-new-dvar-of name kind)))
                     (bounded (begin (k-note-bound v bound) (if distinct (k-set-distinct v) #u)))
                     (pushed (k-push-desc name (ds-var v kind)))
                     (rest (k-binders-each (cdr bs))))
                (cons (product (1 v) (2 kind)) rest))
              (k-sfail k-binder-shapes (car bs)))))))

;; Whether binder `items`, of three or more, ends with `distinct`.
(define k-distinct-marked? (->* (k-syns) bool)
  (lambda (items)
    (and (>= (k-length items) 3)
         (let ((last (k-nth items (- (k-length items) 1))))
           (and (syn-symbol? last) (string=? (syn-name last) "distinct"))))))
(define k-drop-last (->* (k-syns) k-syns)
  (lambda (xs) (if (null? (cdr xs)) nil (the k-syns (cons (car xs) (k-drop-last (cdr xs)))))))

;; `((name kind) …)`, binding each name for the rest of the reading.
(define k-parse-binders (->* (syn) k-binders)
  (lambda (s) (k-binders-each (k-items s "binders"))))

;; An effect name nothing defines: in a module with `include`s, the modules
;; included's, as `k-type-unknown` for types; else what `no` says.
(define k-effect-unknown
  (->* (symbol syn (subr (maxeff checks spin) () string)) k-eff)
  (lambda (sym s no)
    (if (not (null? (k-lookup-desc '%include-scope)))
        (k-one (a-var (k-effect-select '%include sym)))
        (k-sfail (no) s))))
;; The effect a name stands for: in `with` bodies, the modules' first
;; (`k-with-effect-selected`).
(define k-effect-named (->* (syn) k-eff)
  (lambda (s)
    (let* ((n (syn-name s)) (sym (string->symbol n)))
      (case n (("pure") nil)
              (("spin") (k-one (a-spin)))
              (("nondet") (k-one (a-nondet)))
              (("stage") (k-one (a-stage)))
              (else
               (let ((withs (k-withs-over sym)))
                 (if (null? withs)
                     (k-effect-name-read s n)
                     (let ((has (or (not (null? (k-lookup-desc sym)))
                                    (not (null? (k-lookup-desc '%include-scope))))))
                       (k-with-effect-selected
                         withs sym has (if has (k-effect-name-read s n) nil))))))))))
;; Effect name `n`, written `s`, as the description scope and `include`s say.
(define k-effect-name-read (->* (syn string) k-eff)
  (lambda (s n)
    (let ((d (k-lookup-desc (string->symbol n)))
          (no (lambda () (string-append (k-quote n) " is not an effect"))))
      (if (null? d)
          (k-effect-unknown (string->symbol n) s no)
          (tagcase (car d)
            (ds-var (v k) (if (= k 1) (k-one (a-var v)) (k-sfail (no) s)))
            (ds-eff (e) e)
            (else x (k-sfail (no) s)))))))
;; Each effect variable an effect name in a `with` body was read as, not
;; shared as `k-effect-selects`' others are; whether the name meant
;; anything outside, and what, should the module not give it.
(define k-with-effect-falls (ref k-effect-falls @t) (new nil))
;; The entry for `v` in `k-with-effect-falls`, or none.
(define k-with-effect-fall (->* (int) k-effect-falls)
  (lambda (v)
    (letrec ((find (subr kreads (k-effect-falls) k-effect-falls)
                (lambda (fs)
                  (cond ((null? fs) nil)
                        ((= (extract (car fs) 1) v) fs)
                        (else (find (cdr fs)))))))
      (find (get k-with-effect-falls)))))
;; Effect name `sym`, read in the bodies of `with`s of modules `withs`
;; (innermost first): a variable for `(select m sym)` of each, each falling
;; back to the next, out to `outer` if `has`. As `parse.rs`'s
;; `with_effect_selected`.
(define k-with-effect-selected (->* (k-names symbol bool k-eff) k-eff)
  (lambda (withs sym has outer)
    (if (null? withs)
        outer
        (let* ((inner (k-with-effect-selected (cdr withs) sym has outer))
               (falls (or has (not (null? (cdr withs)))))
               (m (car withs))
               (v (k-new-dvar-of (string->symbol (k-cat5 "(select " (symbol->string m) " "
                                                         (symbol->string sym) ")"))
                                 1)))
          (begin
            (set k-effect-selects (cons (product (1 m) (2 sym) (3 v)) (get k-effect-selects)))
            (set k-with-effect-falls
                 (cons (product (1 v) (2 falls) (3 inner)) (get k-with-effect-falls)))
            (k-one (a-var v)))))))
;; Whether `h` heads an atom of effect on a region: `(read r)` and so on.
(define k-atom-head? (->* (string) bool)
  (lambda (h)
    (or (string=? h "read") (string=? h "write") (string=? h "alloc")
        (string=? h "goto") (string=? h "comefrom") (string=? h "await") (string=? h "io")
        (string=? h "init") (string=? h "send") (string=? h "receive"))))
;; The atom `(head r)`, `head` one `k-atom-head?` accepts.
(define k-atom-of (->* (string k-region) k-atom)
  (lambda (head r)
    (case head (("read") (a-read r))
               (("write") (a-write r))
               (("alloc") (a-alloc r))
               (("goto") (a-goto r))
               (("await") (a-await r))
               (("init") (a-init r))
               (("send") (a-send r))
               (("receive") (a-receive r))
               (else (a-comefrom r)))))

(define k-effect-selects (ref k-effect-sels @t) (new nil))
;; The entry for `(select m e)` in `ss`, or none; not a `with`'s
;; (`k-with-effect-selected`), which is not shared.
(define k-effect-sel-find (->* (k-effect-sels symbol symbol) k-effect-sels)
  (lambda (ss m e)
    (cond ((null? ss) nil)
          ((and (symbol=? (extract (car ss) 1) m) (symbol=? (extract (car ss) 2) e)
                (null? (k-with-effect-fall (extract (car ss) 3))))
           ss)
          (else (k-effect-sel-find (cdr ss) m e)))))
;; The variable `(select m e)` read as an effect stands for, named as written.
(define k-effect-select (->* (symbol symbol) int)
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
(define k-effect-desc (->* (k-eff) int)
  (lambda (e) (k-ty-new (ty-lam nil (de e)))))
;; `(select m e)` as an effect, in a list: the variable for it.
(define k-effect-selected (->* (syn k-syns) (listof k-eff acyclic))
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
(define k-keep-at (->* (int) int)
  (lambda (t)
    (begin
      (if (>= t (array-length (get k-keep-marks)))
          (let ((bigger (the (arrayof int @t) (make-array (* 2 (array-length (get k-tys))) 0))))
            (begin (k-copy-array (get k-keep-marks) bigger 0) (set k-keep-marks bigger)))
          #u)
      (array-ref (get k-keep-marks) t))))
(define k-keep-set! (->* (int int) unit)
  (lambda (t e) (begin (k-keep-at t) (array-set! (get k-keep-marks) t e)))))))
