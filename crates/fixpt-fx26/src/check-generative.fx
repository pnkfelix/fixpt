;;; The checker, in FX-26: `define-generative`, read, its parameters' variance
;;; checked. Part of the checker, `check-types.fx` first (moved out of
;;; `check-syntax.fx`, 2026-10-04).

;;; ------------------------------------------------------------ polarity

;; A module (`TODO.md` §34: the front end into modules, a file at a time);
;; what other files use re-exported after it.
;; Its types (`check-generative-types.fx`), loaded before the module so that they are not
;; among its values; the module names what it uses of them.
(define check-generative-types (load-module "fx26:check-generative-types.fx"))
(define check-generative-module (module
(define-type k-seen-pol (select check-generative-types k-seen-pol))
(define-type k-pols-found (select check-generative-types k-pols-found))

;; Where, in a generative type's representation, each of its parameters
;; appears: covariantly, contravariantly, or both (moved out of
;; `check-print.fx`, 2026-10-04).
(define k-pol-seen? (subr kreads ((listof (pairof int int @t) acyclic) int int) bool)
  (lambda (xs t at)
    (and (not (null? xs))
         (or (and (= (car (car xs)) t) (= (cdr (car xs)) at)) (k-pol-seen? (cdr xs) t at)))))
(define-rec
  (k-polarity (subr (maxeff kstate spin) (int int int k-seen-pol k-pols-found) unit)
    (lambda (t v at seen found)
      (let ((t (k-resolve t)))
        (if (k-pol-seen? (get seen) t at)
            #u
            (letrec ((push (subr kstate (int) unit) (lambda (p) (set found (cons p (get found)))))
                     (reg (subr kstate (k-region) unit)
                          (lambda (r) (if (k-reg-is? r v) (push 2) #u)))
                     (eff (subr (maxeff kstate spin) (k-eff int) unit)
                          (lambda (e p)
                            (begin (if (k-eff-var? e v) (push p) #u)
                                   (if (k-eff-region-var? e v) (push 2) #u)
                                   ;; In an effect function applied: either way.
                                   (if (k-eff-app-var? e v) (push 2) #u))))
                     (go (subr (maxeff kstate spin) (int int) unit)
                         (lambda (x p) (k-polarity x v p seen found)))
                     (gos (subr (maxeff kstate spin) (k-ids int) unit)
                          (lambda (xs p) (k-polarities xs v p seen found))))
              (begin
                (set seen (cons (cons t at) (get seen)))
                (tagcase (k-get t)
                  (ty-var (x) (if (= x v) (push at) #u))
                  (ty-subr (e ps r cv) (begin (eff e at) (gos ps (k-flip at)) (go r at)))
                  (ty-poly (bs body) (go body at))
                  (ty-ref (a r) (begin (reg r) (go a 2)))
                  (ty-array (a r) (begin (reg r) (go a 2)))
                  (ty-icell (a r) (begin (reg r) (go a 2)))
                  (ty-markkey (a r) (begin (reg r) (go a 2)))
                  (ty-pair (a b r nl)
                    (let ((p (if (k-frozen? r) at 2))) (begin (reg r) (go a p) (go b p))))
                  (ty-bloblet (fs z r) (begin (reg r) (gos fs (if z at 2))))
                  (ty-product (ps) (k-polarity-parts ps v at seen found))
                  (ty-sum (ps) (k-polarity-parts ps v at seen found))
                  ;; Immutable, as a sum: covariant in its members.
                  (ty-union (ms) (gos ms at))
                  (ty-tag (a h e r) (begin (reg r) (eff e 2) (go a 2) (go h 2)))
                  (ty-comp (a h e r) (begin (reg r) (eff e 2) (go a 2) (go h 2)))
                  (ty-place (r) (reg r))
                  (ty-named (g ds) (k-polarity-descs ds (extract (k-gen-of g) 3) v at seen found))
                  (ty-nlist (e z r) (begin (reg r) (go e at)))
                  ;; What a description function is given, it may use either way.
                  (ty-app (g ds)
                    (begin (tagcase (k-get g) (ty-var (x) (if (= x v) (push 2) #u)) (else z #u))
                           (k-polarity-funs ds v seen found)))
                  (else y #u))))))))
  (k-polarities (subr (maxeff kstate spin) (k-ids int int k-seen-pol k-pols-found) unit)
    (lambda (ts v at seen found)
      (if (null? ts)
          #u
          (begin (k-polarity (car ts) v at seen found) (k-polarities (cdr ts) v at seen found)))))
  (k-polarity-parts (subr (maxeff kstate spin) (k-parts int int k-seen-pol k-pols-found) unit)
    (lambda (ps v at seen found)
      (if (null? ps)
          #u
          (begin (k-polarity (extract (car ps) 2) v at seen found)
                 (k-polarity-parts (cdr ps) v at seen found)))))
  (k-polarity-descs (subr (maxeff kstate spin) (k-descs k-ids int int k-seen-pol k-pols-found) unit)
    (lambda (ds ws v at seen found)
      (if (null? ds)
          #u
          (let* ((w (car ws))
                 (p (cond ((or (= w 2) (= at 2)) 2) ((= w 0) at) (else (k-flip at)))))
            (begin
              (tagcase (car ds)
                (dt (x) (k-polarity x v p seen found))
                (dr (r) (if (k-reg-is? r v) (set found (cons 2 (get found))) #u))
                (de (e) (begin (if (k-eff-var? e v) (set found (cons p (get found))) #u)
                               (if (k-eff-region-var? e v) (set found (cons 2 (get found))) #u)))
                (dz (z) #u)
                (dc (c) #u)
                (df (f) (k-polarity-fun (car ds) v seen found)))
              (k-polarity-descs (cdr ds) (cdr ws) v at seen found))))))
    ;; `v` anywhere in description `d`, given to a description function,
    ;; which may use what it is given either way: invariantly.
    (k-polarity-fun (subr (maxeff kstate spin) (k-desc int k-seen-pol k-pols-found) unit)
      (lambda (d v seen found)
        (begin
          (k-polarities (k-d-types d) v 2 seen found)
          (if (or (k-regions-name? (k-d-regions d) v)
                  (k-effs-name? (k-d-effects d) v)
                  (tagcase d (df (f) (k-type-is-var? f v)) (else z #f)))
              (set found (cons 2 (get found)))
              #u))))
    (k-polarity-funs (subr (maxeff kstate spin) (k-descs int k-seen-pol k-pols-found) unit)
      (lambda (ds v seen found)
        (if (null? ds)
            #u
            (begin (k-polarity-fun (car ds) v seen found)
                   (k-polarity-funs (cdr ds) v seen found))))))

;;; ------------------------------------------------------------ define-generative

(define k-all-ints? (subr (read @globals) (k-ids int) bool)
  (lambda (xs n) (or (null? xs) (and (= (car xs) n) (k-all-ints? (cdr xs) n)))))
;; What parameter `v`, declared of variance `want`, says when it occurs
;; where it may not in generative type `name`.
(define k-variance-message (subr kreads (int int symbol) string)
  (lambda (v want name)
    (k-cat4 (k-quote (k-dvar-string v)) " is declared "
            (if (= want 0) "covariant (+)" "contravariant (-)")
            (k-cat3 " in " (k-quote (symbol->string name)) ", but occurs where it may not"))))
;; Whether parameter `v` of `gen`, declared of variance `want` (0 or 1),
;; occurs in its representation only so.
(define k-check-param-variance (subr (maxeff checks spin) (k-gen int int syn) unit)
  (lambda (gen v want s)
    (let ((found (the k-pols-found (new nil))))
      (begin
        (k-polarity (extract gen 4) v 0 (the k-seen-pol (new nil)) found)
        (if (k-all-ints? (get found) want)
            #u
            (k-sfail (k-variance-message v want (extract gen 1)) s))))))
;; Whether the `g`th generative type's representation bears out the variance
;; declared for its parameters.
(define k-check-variance (subr (maxeff checks spin) (int syn) unit)
  (lambda (g s)
    (let ((gen (k-gen-of g)))
      (letrec ((each (subr (maxeff checks spin) (k-binders k-ids) unit)
                     (lambda (bs vs)
                       (if (null? bs)
                           #u
                           (let ((v (extract (car bs) 1)) (want (car vs)))
                             (begin
                               (if (= want 2) #u (k-check-param-variance gen v want s))
                               (each (cdr bs) (cdr vs))))))))
        (each (extract gen 2) (extract gen 3))))))
;; `(define-generative (name (param kind [+|-]) …) rep)`, or with no
;; parameters `(define-generative name rep)`: a new type, equal only to
;; itself, converted by `up-name` and `down-name`.
;; A parameter's variance, from its items `(name kind [+|-])`: 0
;; covariant, 1 contravariant, 2 invariant (none given).
(define k-parse-variance (subr (maxeff checks spin) (k-syns syn) int)
  (lambda (items p)
    (let ((n (k-length items)))
      (case n ((2) 2)
              ((3)
               (let ((x (k-nth items 2)))
                 (cond ((and (syn-symbol? x) (string=? (syn-name x) "+")) 0)
                       ((and (syn-symbol? x) (string=? (syn-name x) "-")) 1)
                       (else (k-sfail "a parameter's variance is `+` or `-`" x)))))
              (else
               (k-sfail "a parameter is `(name kind)`, `(name kind +)` or `(name kind -)`" p))))))
;; A region or place parameter `p` of kind `kind` must be invariant
;; (`v` 2): it names where data is.
(define k-check-invariant (subr checks (int int syn) unit)
  (lambda (v kind p)
    (cond ((and (not (= v 2)) (or (= kind 0) (= kind 3)))
           (k-sfail "a region or place parameter is invariant: it names where data is" p))
          ((and (not (= v 2)) (k-arrow-kind? kind))
           (k-sfail "a description function parameter is invariant" p))
          (else #u))))
(define k-gen-params (subr (maxeff checks spin) (k-syns int) (productof (1 k-binders) (2 k-ids)))
  (lambda (ps depth)
    (if (null? ps)
        (product (1 (the k-binders nil)) (2 (the k-ids nil)))
        (let* ((p (car ps))
               (items (k-items p "a parameter"))
               (v (k-parse-variance items p))
               (name (k-name-of (car items) "a parameter's name"))
               (kind (k-parse-kind (k-nth items 1)))
               (checked (k-check-invariant v kind p))
               (dv (k-new-dvar-of name kind))
               (pushed (k-push-desc name (ds-var dv kind)))
               (rest (k-gen-params (cdr ps) depth)))
          (product (1 (the k-binders (cons (product (1 dv) (2 kind)) (extract rest 1))))
                   (2 (the k-ids (cons v (extract rest 2)))))))))
(define k-define-generative (subr (maxeff checks spin) (syn syn) symbol)
  (lambda (head rep)
    (let* ((hs (tagcase head (lst (items d a b) items) (else x (the k-syns nil))))
           (name-syn (if (null? hs) head (car hs)))
           (ps (if (null? hs) (the k-syns nil) (cdr hs)))
           (name (k-name-of name-syn "a generative type's name"))
           (saved (get k-dscope))
           (params (k-gen-params ps 0))
           (g (get k-ngens))
           (slot (k-slot))
           (gen (product (1 name) (2 (extract params 1)) (3 (extract params 2)) (4 slot))))
      (begin
        (set k-gens (cons gen (get k-gens)))
        (set k-ngens (+ g 1))
        ;; In scope in its own representation: recursion through the name.
        (k-push-desc name (ds-gen g))
        (let ((r (k-parse-type rep)))
          (begin
            (set k-dscope saved)
            (k-set-link slot r)
            (k-check-variance g rep)
            (k-push-desc name (ds-gen g))
            name))))))))

(define k-define-generative (with check-generative-module k-define-generative))
(define-type k-seen-pol (select check-generative-module k-seen-pol))
