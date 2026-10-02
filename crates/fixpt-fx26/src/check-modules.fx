;;; The checker, in FX-26: first-class modules' descriptions
;;; (`docs/research/first-class-modules.md`, stage M2): reading `moduleof`
;;; and `select`, and a `module`'s items; a module's type bound to a name,
;;; its abstract types named for that binding; `select`s resolved; what
;;; may not leave a binding's scope. The Rust checker's `modules.rs`, as it
;;; reads and resolves. Part of the checker, `check-types.fx` first.
;;;
;;; A module's type is an existential package: its abstract types are
;;; binders of its `moduleof`. A variable of that type has them renamed for
;;; itself as it is bound (`k-name-module`), each a type equal only to
;;; itself, named `m..t`; `(select m t)` is that type. Its rules, `module`
;;; and `with`, are `check-module-rules.fx`'s.

;;; ------------------------------------------------------------ reading

;; `ps` reversed, onto `acc`.
(define k-parts-reversed (subr (maxeff (read @globals) (alloc @t)) (k-parts k-parts) k-parts)
  (lambda (ps acc) (if (null? ps) acc (k-parts-reversed (cdr ps) (cons (car ps) acc)))))

(define k-moduleof-usage string "`(moduleof (abs t type) … (desc d type) … (val x type) …)`")
;; The names among `xs`; what is not one is passed over.
(define k-syn-symbols (subr (maxeff (read @globals) (read @s) (alloc @t)) (k-syns) k-names)
  (lambda (xs)
    (cond ((null? xs) nil)
          ((syn-symbol? (car xs)) (cons (syn-head (car xs)) (k-syn-symbols (cdr xs))))
          (else (k-syn-symbols (cdr xs))))))
;; A component's names: its name; or, an `abs`'s, the names in a list.
(define k-component-names (subr (maxeff checks spin) (syn string) k-names)
  (lambda (name head)
    (if (syn-symbol? name)
        (the k-names (cons (syn-head name) nil))
        (tagcase name
          (lst (items d a b)
            (if (string=? head "abs") (k-syn-symbols items) (k-sfail "a component's name" name)))
          (else x (k-sfail "a component's name" name))))))
;; `seen` and `names`, each named once in component `c`.
(define k-names-once (subr (maxeff checks spin) (k-names k-names syn) k-names)
  (lambda (names seen c)
    (cond ((null? names) seen)
          ((k-has-name? seen (car names)) (k-sfail (k-twice (symbol->string (car names))) c))
          (else (k-names-once (cdr names) (cons (car names) seen) c)))))
;; Abstract types `names`, each a type variable in scope from here, onto `abs`.
(define k-abs-bound (subr (maxeff kstate spin) (k-names k-parts) k-parts)
  (lambda (names abs)
    (if (null? names)
        abs
        (let* ((n (car names)) (v (k-new-dvar-of n 2)))
          (begin (k-push-desc n (ds-var v 2))
                 (k-abs-bound (cdr names) (cons (product (1 n) (2 v)) abs)))))))
;; `(name type)` onto `ps`.
(define k-part-onto (subr (alloc @t) (symbol int k-parts) k-parts)
  (lambda (n t ps) (cons (product (1 n) (2 t)) ps)))
;; A `moduleof`'s components `cs`, those before them read into `abs`, `ds`
;; and `vs` (newest first), their names `seen`.
(define k-moduleof-comps (subr (maxeff checks spin) (k-syns k-parts k-parts k-parts k-names) int)
  (lambda (cs abs ds vs seen)
    (if (null? cs)
        (let ((ds (k-parts-reversed ds nil)) (vs (k-parts-reversed vs nil)))
          (k-ty-new (ty-module (k-parts-reversed abs nil) ds vs)))
        (let* ((c (car cs))
               (parts (k-items c "a module component"))
               (shaped (k-shape (= (k-length parts) 3) k-moduleof-usage c))
               (head (k-symbol-head parts))
               (names (k-component-names (k-nth parts 1) head))
               (seen (k-names-once names seen c))
               (what (k-nth parts 2)))
          (cond ((string=? head "abs")
                 (if (and (syn-symbol? what) (string=? (syn-name what) "type"))
                     (k-moduleof-comps (cdr cs) (k-abs-bound names abs) ds vs seen)
                     (k-sfail "an abstract component is a `type`, for now" what)))
                ((string=? head "desc")
                 (let ((t (k-parse-type what)))
                   (begin (k-push-desc (car names) (ds-rec t))
                          (k-moduleof-comps (cdr cs) abs (k-part-onto (car names) t ds) vs seen))))
                ((string=? head "val")
                 (let ((t (k-parse-type what)))
                   (k-moduleof-comps (cdr cs) abs ds (k-part-onto (car names) t vs) seen)))
                (else (k-sfail k-moduleof-usage (car parts))))))))
;; `(select m t)`: as written, for checking to resolve where `m` is bound.
(define k-parse-select (subr (maxeff checks spin) (syn k-syns) int)
  (lambda (s items)
    (cond ((not (= (k-length items) 3)) (k-sfail "`(select module name)`" s))
          ((and (syn-symbol? (k-nth items 1)) (syn-symbol? (k-nth items 2)))
           (k-ty-new (ty-select (syn-head (k-nth items 1)) (syn-head (k-nth items 2)))))
          (else (k-sfail "`(select module name)`: a module's name, and a component's" s)))))
;; `(moduleof …)`, each abstract type a binder in scope in what follows it;
;; or `(select m t)`.
(define k-read-module-type (subr (maxeff checks spin) (syn k-syns symbol) int)
  (lambda (s items hd)
    (if (symbol=? hd 'select)
        (k-parse-select s items)
        (let* ((saved (get k-dscope)) (t (k-moduleof-comps (cdr items) nil nil nil nil)))
          (begin (set k-dscope saved) t)))))
(set k-parse-module-type k-read-module-type)

;; A `define-rec`'s types and expressions, each type read before its
;; expression, as the Rust parser reads them.
(define-type k-rec-read (productof (1 k-ids) (2 kxs)))
(define k-resolve-rec-items (subr (maxeff checks spin) (syns-a exp-list) k-rec-read)
  (lambda (ts xs)
    (if (null? ts)
        (product (1 (the k-ids nil)) (2 (the kxs nil)))
        (let* ((t (k-parse-type (car ts)))
               (x (k-resolve-exp (car xs)))
               (rest (k-resolve-rec-items (cdr ts) (cdr xs))))
          (product (1 (the k-ids (cons t (extract rest 1))))
                   (2 (the kxs (cons x (extract rest 2)))))))))
;; A module item as `x-module` has it.
(define k-item-of (subr (maxeff (read @globals) (alloc @t)) (int names int k-ids kxs) k-item)
  (lambda (k ns v ts xs) (product (1 k) (2 (k-copy-names ns)) (3 v) (4 ts) (5 xs))))
;; One item: an abstract type a type variable in scope from here (with
;; its representation read in that scope), and a transparent one an alias.
(define k-resolve-item (subr (maxeff checks spin) (mod-item) k-item)
  (lambda (it)
    (let ((k (extract it 1)) (ns (extract it 2)) (ts (extract it 3)) (xs (extract it 4)))
      (cond ((= k 0)
             (let* ((v (k-new-dvar-of (car ns) 2))
                    (pushed (k-push-desc (car ns) (ds-var v 2)))
                    (rep (k-parse-type (car ts))))
               (k-item-of k ns v (the k-ids (cons rep nil)) (k-resolve-all xs))))
            ((= k 1)
             (let ((t (k-parse-type (car ts))))
               (begin (k-push-desc (car ns) (ds-rec t))
                      (k-item-of k ns -1 (the k-ids (cons t nil)) nil))))
            ((= k 2)
             (let* ((t (if (null? ts) (the k-ids nil) (k-parse-types ts))) (x (k-resolve-all xs)))
               (k-item-of k ns -1 t x)))
            (else
             (let ((r (k-resolve-rec-items ts xs)))
               (k-item-of k ns -1 (extract r 1) (extract r 2))))))))
(define k-resolve-items (subr (maxeff checks spin) (mod-items) k-items)
  (lambda (items)
    (if (null? items)
        nil
        (let* ((x (k-resolve-item (car items))) (rest (k-resolve-items (cdr items))))
          (cons x rest)))))
;; `(module item …)`: each item read in the scope of the descriptions
;; before it.
(define k-resolve-module-items (subr (maxeff checks spin) (mod-items int int) kx)
  (lambda (items a b)
    (let* ((saved (get k-dscope)) (xs (k-resolve-items items)))
      (begin (set k-dscope saved) (x-module xs a b)))))
(set k-resolve-module k-resolve-module-items)

;;; ------------------------------------------------------------ walking types

;; The types of parts `ps`, onto `tail`.
(define k-parts-onto (subr (maxeff (read @globals) (alloc @t)) (k-parts k-ids) k-ids)
  (lambda (ps tail)
    (if (null? ps) tail (cons (extract (car ps) 2) (k-parts-onto (cdr ps) tail)))))
;; `ts`, and `t` after them.
(define k-ids-then (subr (maxeff (read @globals) (alloc @t)) (k-ids int) k-ids)
  (lambda (ts t) (if (null? ts) (cons t nil) (cons (car ts) (k-ids-then (cdr ts) t)))))
;; The types `t` is made of, one level down.
(define k-ty-kids (subr (maxeff kmakes spin) (int) k-ids)
  (lambda (t)
    (tagcase (k-get t)
      (ty-subr (e ps r cv) (k-ids-then ps r))
      (ty-poly (bs x) (the k-ids (cons x nil)))
      (ty-ref (a r) (the k-ids (cons a nil)))
      (ty-array (a r) (the k-ids (cons a nil)))
      (ty-icell (a r) (the k-ids (cons a nil)))
      (ty-markkey (a r) (the k-ids (cons a nil)))
      (ty-pair (a d r) (k-ids-then (the k-ids (cons a nil)) d))
      (ty-tag (a h e r) (k-ids-then (the k-ids (cons a nil)) h))
      (ty-comp (x a e r) (k-ids-then (the k-ids (cons x nil)) a))
      (ty-product (ps) (k-parts-onto ps nil))
      (ty-sum (ps) (k-parts-onto ps nil))
      (ty-bloblet (fs z r) fs)
      (ty-named (g ds) (k-desc-types ds))
      (ty-nlist (e z r) (the k-ids (cons e nil)))
      (ty-module (abs ds vs) (k-parts-onto ds (k-parts-onto vs nil)))
      (else y nil))))
;; Whether type variable `v` is somewhere in `t`, or in `ts`; `seen`, the
;; nodes walked.
(define-rec
  (k-mentions-from? (subr (maxeff kstate spin) (int int (ref k-ids @t)) bool)
    (lambda (t v seen)
      (let ((t (k-resolve t)))
        (if (k-has-id? (get seen) t)
            #f
            (begin
              (set seen (cons t (get seen)))
              (or (tagcase (k-get t) (ty-var (w) (= w v)) (else y #f))
                  (k-any-mentions? (k-ty-kids t) v seen)))))))
  (k-any-mentions? (subr (maxeff kstate spin) (k-ids int (ref k-ids @t)) bool)
    (lambda (ts v seen)
      (and (not (null? ts))
           (or (k-mentions-from? (car ts) v seen) (k-any-mentions? (cdr ts) v seen))))))
(define k-mentions-var? (subr (maxeff kstate spin) (int int) bool)
  (lambda (t v) (k-mentions-from? t v (the (ref k-ids @t) (new nil)))))
;; The first of `vs` that `t` mentions, or -1.
(define k-first-mentioned (subr (maxeff kstate spin) (int k-ids) int)
  (lambda (t vs)
    (cond ((null? vs) -1)
          ((k-mentions-var? t (car vs)) (car vs))
          (else (k-first-mentioned t (cdr vs))))))

;;; ------------------------------------------------------------ naming

;; Whether `v` was made for a module's abstract type as it was bound.
(define k-module-var? (subr kreads (int) bool)
  (lambda (v) (k-has-id? (get k-module-vars) v)))
;; Abstract types `abs` renamed for a binding, each `prefix` and its name:
;; the new ones, and what each old one becomes.
(define-type k-renamed (productof (1 k-parts) (2 k-map)))
(define k-rename-abs (subr (maxeff kstate spin) (string k-parts) k-renamed)
  (lambda (prefix abs)
    (if (null? abs)
        (product (1 (the k-parts nil)) (2 (the k-map nil)))
        (let* ((a (extract (car abs) 1))
               (w (k-new-dvar-of (string->symbol (string-append prefix (symbol->string a))) 2))
               (noted (begin (set k-skolems (cons w (get k-skolems)))
                             (set k-module-vars (cons w (get k-module-vars)))))
               (to (dt (k-ty-new (ty-var w))))
               (rest (k-rename-abs prefix (cdr abs))))
          (product (1 (the k-parts (cons (product (1 a) (2 w)) (extract rest 1))))
                   (2 (the k-map (cons (cons (extract (car abs) 2) to) (extract rest 2)))))))))
;; Parts `ps`, each type with `m` for its binders.
(define k-subst-each (subr (maxeff kstate spin) (k-parts k-map) k-parts)
  (lambda (ps m)
    (if (null? ps)
        nil
        (let* ((t (k-subst (extract (car ps) 2) m)) (rest (k-subst-each (cdr ps) m)))
          (cons (product (1 (extract (car ps) 1)) (2 t)) rest)))))
;; A module's type, bound to `name`: its abstract types renamed for this
;; binding, each `name..t`, kept until the binding's scope ends. Any other
;; type as it is.
(define k-name-module (subr (maxeff kstate spin) (symbol int) int)
  (lambda (name t)
    (tagcase (k-get (k-resolve t))
      (ty-module (abs ds vs)
        (if (null? abs)
            t
            (let* ((r (k-rename-abs (string-append (symbol->string name) "..") abs))
                   (ds2 (k-subst-each ds (extract r 2)))
                   (vs2 (k-subst-each vs (extract r 2))))
              (k-ty-new (ty-module (extract r 1) ds2 vs2)))))
      (else y t))))
;; Of the sizes and abstract types `vs`, named in a scope that `t` leaves:
;; the sizes, to be forgotten. A module's abstract type cannot be: nothing
;; may leave its binding's scope still mentioning it.
(define k-sizes-of (subr (maxeff kreads (alloc @t)) (k-ids) k-ids)
  (lambda (vs)
    (cond ((null? vs) nil)
          ((k-module-var? (car vs)) (k-sizes-of (cdr vs)))
          (else (cons (car vs) (k-sizes-of (cdr vs)))))))
(define k-escaping (subr (maxeff kstate spin) (int k-ids) int)
  (lambda (t vs)
    (cond ((null? vs) -1)
          ((and (k-module-var? (car vs)) (k-mentions-var? t (car vs))) (car vs))
          (else (k-escaping t (cdr vs))))))
(define k-unescaped (subr (maxeff checks spin) (int k-ids int int) k-ids)
  (lambda (t vs a b)
    (let ((v (k-escaping t vs)))
      (if (< v 0)
          (k-sizes-of vs)
          (k-fail (k-cat5 "this is a " (k-show-ty t) ", and `" (k-dvar-string v)
                          (string-append "` is a module's abstract type, not known outside "
                                         "the scope where the module is named"))
                  a b)))))

;;; ------------------------------------------------------------ select

;; Each `(select m n)` in `t`, as first met, onto `out` (newest first); the
;; nodes walked, `seen`.
(define-rec
  (k-selects-from (subr (maxeff kstate spin) (int (ref k-ids @t) (ref k-selects @t)) unit)
    (lambda (t seen out)
      (let ((t (k-resolve t)))
        (if (k-has-id? (get seen) t)
            #u
            (begin
              (set seen (cons t (get seen)))
              (tagcase (k-get t)
                (ty-select (m n)
                  (if (>= (k-select-in (get out) m n -1) 0)
                      #u
                      (set out (cons (product (1 m) (2 n) (3 t)) (get out)))))
                (else y (k-selects-each (k-ty-kids t) seen out))))))))
  (k-selects-each (subr (maxeff kstate spin) (k-ids (ref k-ids @t) (ref k-selects @t)) unit)
    (lambda (ts seen out)
      (if (null? ts)
          #u
          (begin (k-selects-from (car ts) seen out) (k-selects-each (cdr ts) seen out))))))
;; `ss` reversed, onto `acc`.
(define k-selects-reversed
  (subr (maxeff (read @globals) (alloc @t)) (k-selects k-selects) k-selects)
  (lambda (ss acc) (if (null? ss) acc (k-selects-reversed (cdr ss) (cons (car ss) acc)))))
;; The `select`s in `t`, in the order first met.
(define k-selects-in (subr (maxeff kstate spin) (int) k-selects)
  (lambda (t)
    (let ((out (the (ref k-selects @t) (new nil))))
      (begin (k-selects-from t (the (ref k-ids @t) (new nil)) out)
             (k-selects-reversed (get out) nil)))))
;; `(select m n)`, as an error shows it.
(define k-select-shown (subr (read @globals) (symbol symbol) string)
  (lambda (m n) (k-cat5 "`(select " (symbol->string m) " " (symbol->string n) ")`")))
;; The type component `n` of parts `ps`, or -1.
(define k-comp-find (subr kreads (k-parts symbol) int)
  (lambda (ps n)
    (cond ((null? ps) -1)
          ((symbol=? (extract (car ps) 1) n) (extract (car ps) 2))
          (else (k-comp-find (cdr ps) n)))))
;; What `(select m n)` is, `m` a module bound to a type of abstract types
;; `abs` and descriptions `ds`: its abstract type `n`, or its description;
;; an error at `a`..`b` if it has neither.
(define k-select-component (subr (maxeff checks spin) (symbol symbol k-parts k-parts int int) int)
  (lambda (m n abs ds a b)
    (let ((v (k-comp-find abs n)) (d (k-comp-find ds n)))
      (cond ((>= v 0) (k-ty-new (ty-var v)))
            ((>= d 0) d)
            (else (k-fail (k-cat5 (k-select-shown m n) ": `" (symbol->string m) "` has no type `"
                                  (string-append (symbol->string n) "`"))
                          a b))))))
;; What each of `found` is where it is checked, at `a`..`b`.
(define k-selection (subr (maxeff checks spin) (k-selects int int) k-selects)
  (lambda (found a b)
    (if (null? found)
        nil
        (let* ((m (extract (car found) 1)) (n (extract (car found) 2))
               (mt (k-lookup m))
               (shown (k-cat3 (k-select-shown m n) ": `" (symbol->string m)))
               (to (if (< mt 0)
                       (k-fail (string-append shown "` is not bound here") a b)
                       (tagcase (k-get mt)
                         (ty-module (abs ds vs) (k-select-component m n abs ds a b))
                         (else y (k-fail (k-cat4 shown "` is a " (k-show-ty mt) ", not a module")
                                         a b)))))
               (rest (k-selection (cdr found) a b)))
          (cons (product (1 m) (2 n) (3 to)) rest)))))
;; `t` with each `(select m n)` in it replaced by what it is: `m`'s
;; abstract type `n`, as `m` was bound, or its description `n`. An error
;; at `a`..`b` if one is not.
(define k-resolve-selects (subr (maxeff checks spin) (int int int) int)
  (lambda (t a b)
    (let ((found (k-selects-in t)))
      (if (null? found)
          t
          (let ((outer (get k-select-map)))
            (begin
              (set k-select-map (k-selection found a b))
              (let ((r (k-subst t nil)))
                (begin (set k-select-map outer) r))))))))
;; The same for a type written as `s`, at `s`.
(define k-select-syn (subr (maxeff checks spin) (int syn) int)
  (lambda (t s) (k-resolve-selects t (syn-start s) (syn-end s))))
;; The same for the types a `letrec`'s bindings `bs` are declared, at the
;; `letrec`, `a`..`b`.
(define k-letrec-selected (subr (maxeff checks spin) (k-letrec-bs int int) k-letrec-bs)
  (lambda (bs a b)
    (if (null? bs)
        nil
        (let* ((x (car bs))
               (t (k-resolve-selects (extract x 2) a b))
               (rest (k-letrec-selected (cdr bs) a b)))
          (cons (product (1 (extract x 1)) (2 t) (3 (extract x 3))) rest)))))
;; The first `select` of `found` from one of `params`, or none.
(define k-select-from (subr kreads (k-selects k-names) k-selects)
  (lambda (found params)
    (cond ((null? found) nil)
          ((k-has-name? params (extract (car found) 1)) (cons (car found) nil))
          (else (k-select-from (cdr found) params)))))
;; `t` resolved, at `a`..`b`, where `params` are not yet bound, and so may
;; not be selected from: one that names the parameter it is the type of, or
;; a later one.
(define k-resolve-outside (subr (maxeff checks spin) (int k-names int int) int)
  (lambda (t params a b)
    (let ((dependent (k-select-from (k-selects-in t) params)))
      (if (null? dependent)
          (k-resolve-selects t a b)
          (let ((s (car dependent)))
            (k-fail (string-append
                     (k-select-shown (extract s 1) (extract s 2))
                     (string-append " names a parameter of the same `lambda`: "
                                    "a dependent type, not supported yet"))
                    a b))))))
(define k-binding-names (subr kmakes (k-bindings) k-names)
  (lambda (bs) (if (null? bs) nil (cons (car (car bs)) (k-binding-names (cdr bs))))))
