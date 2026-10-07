;;; The checker, in FX-26: reading types, one knot (a module's `letrec*`):
;;; type forms and effects (`check-syntax.fx`'s), descriptions and their
;;; functions and kinds (`check-kinds.fx`'s and `check-args.fx`'s), module
;;; types (`check-modules.fx`'s) and dependent parameters
;;; (`check-dependent.fx`'s), each reading the others. After
;;; `check-subst.fx`; part of the checker, `check-types.fx` first.

;; A module (`TODO.md` §34: the front end into modules, a file at a time);
;; what other files use re-exported after it.
(define check-read-types-module (module
;; A `dlambda` of no parameters, as an error says.
(define k-dlambda-empty string "a `dlambda` takes at least one description")
(define k-moduleof-usage string "`(moduleof (abs t type) … (desc d type) … (val x type) …)`")
(define k-abs-usage string
  "an abstract component is a `type`, or a type constructor `(=> (kind …) type)`, for now")
;; The heads of the type forms a type is read from, and every keyword: no
;; parameter's name.
(define k-type-forms k-names
  (list 'arrayof 'bloblet 'composable 'dletrec 'icell 'listof 'mark-key 'moduleof 'mu 'nat 'nlist
        'pairof 'place 'poly 'productof 'prompt-tag 'proves 'ref 'select 'subr 'sumof 'union))
(define k-keywords k-names
  (list 'lambda 'plambda 'proj 'if 'letrec 'let 'begin 'define 'define* 'define-type
        'define-generative 'subr 'poly 'ref 'pairof 'dletrec 'void 'pure 'maxeff 'read 'write
        'alloc 'goto 'comefrom 'region 'effect 'type 'prompt 'prompt-tag 'composable 'mark-key
        'listof 'cond 'else 'and 'or 'let* 'define-effect 'private-regions 'the 'bloblet 'fields
        'frozen 'arrayof 'icell 'await 'define-rec 'letrena 'letreap 'rlambda 'quote 'productof
        'sumof 'product 'extract 'sum 'tagcase 'module 'moduleof 'with 'select 'load-module
        'define-datatype 'make-bloblet 'bloblet-ref 'bloblet-set! 'bloblet-freeze 'bloblet-byte
        'bloblet-set-byte! 'bloblet-bytes 'rmake-bloblet 'dlambda '=> 'case))
(define k-no-name symbol '||)
(define k-effects (subr (maxeff checks spin) (k-syns) k-eff)
  (lambda (xs)
    (if (null? xs)
        nil
        (let* ((e (k-parse-effect (car xs))) (rest (k-effects (cdr xs)))) (k-union e rest)))))
(define k-parse-effect (subr (maxeff checks spin) (syn) k-eff)
  (lambda (s)
    (if (syn-symbol? s)
        (k-effect-named s)
        (let* ((items (k-items s "an effect"))
               (head (k-head items))
               ;; `(select m e)`: module `m`'s effect `e`, found where the
               ;; type it is in is checked, as a type's `select` is.
               (selected (if (string=? head "select")
                             (k-effect-selected s items)
                             (the (listof k-eff acyclic) nil)))
               ;; `(e d …)`: a description function to an effect, applied.
               (applied (if (null? selected) (k-parse-effect-app s items) selected)))
          (cond ((not (null? selected)) (car selected))
                ((not (null? applied)) (car applied))
                ((string=? head "maxeff") (k-effects (cdr items)))
                ((k-atom-head? head)
                 (if (= (k-length items) 2)
                     (k-effect-atom head (k-nth items 1))
                     (k-sfail (k-cat3 "`(" head " region)`") s)))
                (else (k-sfail "expected an effect" s)))))))
(define k-parse-types (subr (maxeff checks spin) (k-syns) k-ids)
  (lambda (xs)
    (if (null? xs)
        nil
        (let* ((t (k-parse-type (car xs))) (rest (k-parse-types (cdr xs)))) (cons t rest)))))
(define k-parse-parts (subr (maxeff checks spin) (k-syns k-parts) k-parts)
  (lambda (ps done)
    (if (null? ps)
        (reverse done)
        (let ((pair (k-items (car ps) "`(label type)`")))
          (if (= (k-length pair) 2)
              (let ((l (k-syn-label (car pair))))
                (if (k-has-label? done l)
                    (k-sfail (k-twice (symbol->string l)) (car ps))
                    (let ((t (k-parse-type (k-nth pair 1))))
                      (k-parse-parts (cdr ps) (cons (product (1 l) (2 t)) done)))))
              (k-sfail "`(label type)`" (car ps)))))))
;; Storage written: a procedure kept there may not reach itself unsaid
;; (`spin`).
(define k-parse-type (subr (maxeff checks spin) (syn) int)
  (lambda (s)
    (let ((t (k-parse-type-node s)))
      (begin
        (if (and (not (syn-symbol? s)) (k-storage-head? (k-head (k-items s "a type"))))
            (k-no-knot t (syn-start s) (syn-end s))
            #u)
        t))))
;; What `(proves prop)` states: the type of its proof, with the lemma kept
;; pending for the definition it declares.
(define k-parse-proves (subr (maxeff checks spin) (syn string) int)
  (lambda (prop usage)
    (let* ((items (k-items prop "a proposition"))
           (head (k-symbol-head items))
           (poly? (string=? head "poly"))
           (shape (cond (poly? (if (>= (k-length items) 3) #u (k-sfail usage prop)))
                        ((string=? head "<=") #u)
                        (else (k-sfail usage prop))))
           (bs (if poly? (k-parse-binders (k-nth items 1)) (the k-binders nil)))
           (conc (k-le (if poly? (k-nth items 2) prop)))
           (hyps (if poly? (k-les (cdr (cdr (cdr items)))) (the k-hyps nil)))
           (spin (k-one (a-spin)))
           (params (k-hyp-coercions hyps spin (the k-ids (cons (car conc) nil))))
           (body (k-ty-new (ty-subr spin params (cdr conc) (get k-conv-default))))
           (t (if (null? bs) body (k-ty-new (ty-poly bs body)))))
      (begin
        (set k-pending-lemma (cons (k-stated-lemma bs conc hyps) nil))
        t))))
(define k-le (subr (maxeff checks spin) (syn) (pairof int int @t))
  (lambda (s)
    (let ((items (k-items s "a proposition")))
      (if (and (= (k-length items) 3) (string=? (k-symbol-head items) "<="))
          (let* ((a (k-parse-type (k-nth items 1))) (b (k-parse-type (k-nth items 2))))
            (cons a b))
          (k-sfail "a proposition is `(<= type type)`" s)))))
(define k-les (subr (maxeff checks spin) (k-syns) k-hyps)
  (lambda (xs)
    (if (null? xs) nil (let* ((h (k-le (car xs))) (rest (k-les (cdr xs)))) (cons h rest)))))
;; `(name d …)` for the `g`th generative type: a node, never expanded.
(define k-apply-gen (subr (maxeff checks spin) (syn int k-syns) int)
  (lambda (s g args)
    (let* ((gen (k-gen-of g)) (ps (extract gen 2)))
      (if (not (= (k-length args) (k-length ps)))
          (k-sfail (k-arity-message (extract gen 1) (k-length ps) (k-length args)) s)
          (let ((t (k-ty-new (ty-named g (k-gen-args ps args)))))
            ;; What it holds may keep a procedure that reaches itself.
            (begin (k-no-knot t (syn-start s) (syn-end s)) t))))))
(define k-gen-args (subr (maxeff checks spin) (k-binders k-syns) k-descs)
  (lambda (ps args)
    (if (null? ps)
        nil
        (let* ((k (extract (car ps) 2))
               (d (cond ((k-type-kind? k) (dt (k-parse-type (car args))))
                        ((= k 0) (dr (k-parse-region (car args))))
                        ((= k 3) (dr (k-parse-place (car args))))
                        ((= k 5) (dz (k-parse-size (car args))))
                        ((= k 6) (dc (k-parse-conv (car args))))
                        ((>= k 100) (df (k-parse-fun (car args) k)))
                        (else (de (k-parse-effect (car args))))))
               (rest (k-gen-args (cdr ps) (cdr args))))
          (cons d rest)))))
;; The type a name stands for.
(define k-type-named (subr (maxeff checks spin) (syn) int)
  (lambda (s)
    (let* ((n (syn-name s)) (sym (string->symbol n)) (base (k-find (get k-base) sym)))
      (cond ((string=? n "void") k-void)
            ((and (string=? n "nat") (null? (k-lookup-desc sym)))
             (k-ty-new (ty-nat (sz-finite))))
            ((>= base 0) base)
            (else
             (let ((d (k-lookup-desc sym))
                   (no (lambda () (string-append (k-quote n) " is not a type"))))
               (if (null? d)
                   (k-sfail (no) s)
                   (tagcase (car d)
                     (ds-var (v k)
                       (cond ((k-type-kind? k) (k-ty-new (ty-var v)))
                             ((k-arrow-kind? k) (k-sfail (k-not-applied n k) s))
                             (else (k-sfail (no) s))))
                     (ds-fun (f)
                       (let ((k (k-fun-kind f))) (k-sfail (k-not-applied n (if (< k 0) 2 k)) s)))
                     (ds-rec (t) t)
                     (ds-gen (g) (k-apply-gen s g nil))
                     (else x (k-sfail (no) s))))))))))
(define k-parse-type-node (subr (maxeff checks spin) (syn) int)
  (lambda (s)
    (if (syn-symbol? s)
        (k-type-named s)
        (let* ((items (k-items s "a type"))
               (hd (if (null? items) '|()| (syn-head (car items))))
               (abbrev (if (symbol=? hd '|()|)
                           (the (listof k-ds acyclic) nil)
                           (k-lookup-desc hd)))
               (alias (k-select-alias abbrev)))
          (cond ((and (not (null? abbrev)) (k-ds-applied? (car abbrev)))
                 (tagcase (car abbrev)
                   (ds-abbrev (ps body) (k-expand-abbrev s hd ps body (cdr items)))
                   (ds-gen (g) (k-apply-gen s g (cdr items)))
                   ;; A description function applied (`check-kinds.fx`).
                   (ds-var (v k) (k-parse-app s (k-ty-new (ty-var v)) (cdr items)))
                   (ds-fun (f) (k-parse-app s f (cdr items)))
                   (else x (k-sfail "an abbreviation" s))))
                ((>= alias 0) (k-parse-app s alias (cdr items)))
                ;; `((dlambda …) d …)` and `((select m f) d …)`.
                ((and (not (null? items)) (tagcase (car items) (lst (xs d a b) #t) (else x #f)))
                 (k-parse-app s (k-parse-fun (car items) -1) (cdr items)))
                (else (k-parse-type-form s items hd)))))))
;; `(subr effect (param …) result)`, or with a convention first, `(subr
;; (conv C) effect (param …) result)`; left out, it is the program's.
(define k-parse-subr (subr (maxeff checks spin) (syn k-syns) int)
  (lambda (s items)
    (let* ((conv? (and (= (k-length items) 5) (string=? (k-list-head (k-nth items 1)) "conv")))
           (cv (if conv? (k-parse-conv-form (k-nth items 1)) (get k-conv-default)))
           (items (if conv? (the k-syns (cons (car items) (cdr (cdr items)))) items)))
      (begin
        (k-shape (= (k-length items) 4) "`(subr effect (param …) result)`" s)
        (let* ((e (k-parse-effect (k-nth items 1)))
               (ts (k-read-params (k-items-or-nil (k-nth items 2) "parameter types")
                                         (k-nth items 3))))
          (k-ty-new (ty-subr e (k-ids-but-last ts) (k-ids-last ts) cv)))))))
;; `(proves prop)`.
(define k-parse-proves-type (subr (maxeff checks spin) (syn k-syns) int)
  (lambda (s items)
    (let ((usage (string-append "`(proves (<= type type))` or `(proves (poly ((name kind) …) "
                                "(<= type type) (<= type type) …))`")))
      (begin
        (k-shape (= (k-length items) 2) usage s)
        (let* ((saved (get k-dscope)) (t (k-parse-proves (k-nth items 1) usage)))
          (begin (set k-dscope saved) t))))))
;; A type written as a form, `(hd …)`, `hd` no family's name.
(define k-parse-type-form (subr (maxeff checks spin) (syn k-syns symbol) int)
  (lambda (s items hd)
    (let ((n (k-length items)))
      (case hd
        ((subr) (k-parse-subr s items))
        ((proves) (k-parse-proves-type s items))
        ((poly)
         (begin
           (k-shape (= n 3) "`(poly ((name kind) …) type)`" s)
           (let* ((saved (get k-dscope))
                  (bs (k-parse-binders (k-nth items 1)))
                  (body (k-parse-type (k-nth items 2))))
             (begin (set k-dscope saved) (k-ty-new (ty-poly bs body))))))
        ((nlist)
         (begin
           (k-shape (or (= n 3) (= n 4)) "`(nlist type size)` or `(nlist type size place)`" s)
           (let* ((e (k-parse-type (k-nth items 1)))
                  (z (k-parse-size (k-nth items 2)))
                  (r (if (= n 4)
                         (k-frozen-into (k-parse-place (k-nth items 3)) #t)
                         (r-frozen -1 #t))))
             (k-ty-new (ty-nlist e z r)))))
        ((nat)
         (begin
           (k-shape (= n 2) "`(nat size)`" s)
           (k-ty-new (ty-nat (k-parse-size (k-nth items 1))))))
        ((ref)
         (begin
           (k-shape (= n 3) "`(ref type region)`" s)
           (let* ((t (k-parse-type (k-nth items 1))) (r (k-parse-region (k-nth items 2))))
             (k-ty-new (ty-ref t r)))))
        ((pairof)
         (begin
           (k-shape (= n 4) "`(pairof type type region)`" s)
           (let* ((a (k-parse-type (k-nth items 1))) (b (k-parse-type (k-nth items 2)))
                  (r (k-parse-region (k-nth items 3))))
             (k-ty-new (ty-pair a b r #f)))))
        ((union) (k-parse-union s items))
        ((dletrec) (k-parse-dletrec s items))
        ((mu) (k-parse-mu s items))
        ((listof)
         (begin
           (k-shape (= n 3) "`(listof type region)`" s)
           (let* ((t (k-parse-type (k-nth items 1))) (r (k-parse-region (k-nth items 2)))
                  (slot (k-slot)) (pair (k-ty-new (ty-pair t slot r #t))))
             (begin (k-set-link slot pair) slot))))
        ((prompt-tag)
         (begin
           (k-shape (= n 5) "`(prompt-tag answer payload effect region)`" s)
           (let* ((a (k-parse-type (k-nth items 1))) (h (k-parse-type (k-nth items 2)))
                  (e (k-parse-effect (k-nth items 3))) (r (k-parse-region (k-nth items 4))))
             (k-ty-new (ty-tag a h e r)))))
        ((composable)
         (begin
           (k-shape (= n 5) "`(composable argument answer effect region)`" s)
           (let* ((t (k-parse-type (k-nth items 1))) (a (k-parse-type (k-nth items 2)))
                  (e (k-parse-effect (k-nth items 3))) (r (k-parse-region (k-nth items 4))))
             (k-ty-new (ty-comp t a e r)))))
        ((bloblet)
         (begin
           (k-shape (= n 3) "`(bloblet (fields type …) region)`, or `(frozen type …)`" s)
           (let* ((fields (k-nth items 1))
                  (parts (k-items fields "`(fields type …)`"))
                  (which (k-head parts)))
             (if (or (string=? which "fields") (string=? which "frozen"))
                 (let* ((fs (k-parse-types (cdr parts))) (r (k-parse-region (k-nth items 2))))
                   (k-ty-new (ty-bloblet fs (string=? which "frozen") r)))
                 (k-sfail "`(fields type …)` or `(frozen type …)`" fields)))))
        ((productof) (k-ty-new (ty-product (k-parse-parts (cdr items) nil))))
        ((sumof) (k-ty-new (ty-sum (k-parse-parts (cdr items) nil))))
        ((arrayof)
         (begin
           (k-shape (= n 3) "`(arrayof type region)`" s)
           (let* ((t (k-parse-type (k-nth items 1))) (r (k-parse-region (k-nth items 2))))
             (k-ty-new (ty-array t r)))))
        ((icell)
         (begin
           (k-shape (= n 3) "`(icell type region)`" s)
           (let* ((t (k-parse-type (k-nth items 1))) (r (k-parse-region (k-nth items 2))))
             (k-ty-new (ty-icell t r)))))
        ((place)
         (begin
           (k-shape (= n 2) "`(place region)`" s)
           (k-ty-new (ty-place (k-parse-place (k-nth items 1))))))
        ((mark-key)
         (begin
           (k-shape (= n 3) "`(mark-key type region)`" s)
           (let* ((t (k-parse-type (k-nth items 1))) (r (k-parse-region (k-nth items 2))))
             (k-ty-new (ty-markkey t r)))))
        (else
         (cond ((k-module-type-head? hd) (k-read-module-type s items hd))
               (else (k-sfail "expected a type" s))))))))
;; `(dletrec ((name type) …) type)`: each name gets a forwarding slot
;; before any body is read, so the bodies can refer to it and each other.
(define k-parse-dletrec (subr (maxeff checks spin) (syn k-syns) int)
  (lambda (s items)
    (begin
      (k-shape (= (k-length items) 3) "`(dletrec ((name type) …) type)`" s)
      (let* ((saved (get k-dscope))
             (slots (k-dletrec-slots (k-items (k-nth items 1) "dletrec bindings")))
             (filled (k-dletrec-fill slots))
             (grounded (k-dletrec-grounded slots s))
             (unknotted (k-dletrec-no-knot slots s))
             (body (k-parse-type (k-nth items 2))))
        (begin (set k-dscope saved) body)))))
;; `(mu name type)`: a recursive type, anonymous; the same as `(dletrec
;; ((name type)) name)`.
;; A union (`docs/research/logical-types.md`): so far only of `nil` and a
;; pair, a pair that may be `nil`.
(define k-union-shape string "a union is, so far, `(union nil (pairof type type region))`")
(define k-parse-union (subr (maxeff checks spin) (syn k-syns) int)
  (lambda (s items)
    (begin
      (k-shape (and (= (k-length items) 3) (syn-symbol? (k-nth items 1))
                    (string=? (syn-name (k-nth items 1)) "nil"))
               k-union-shape s)
      (let* ((pair (k-nth items 2)) (p (k-resolve (k-parse-type pair))))
        (tagcase (k-get p)
          (ty-pair (a b r nl) (k-ty-new (ty-pair a b r #t)))
          (else y (k-fail k-union-shape (syn-start pair) (syn-end pair))))))))
(define k-parse-mu (subr (maxeff checks spin) (syn k-syns) int)
  (lambda (s items)
    (begin
      (k-shape (= (k-length items) 3) "`(mu name type)`" s)
      (let* ((name (k-name-of (k-nth items 1) "a name"))
             (saved (get k-dscope))
             (slot (k-slot))
             (pushed (k-push-desc name (ds-rec slot)))
             (t (k-parse-type (k-nth items 2)))
             (restored (set k-dscope saved))
             (filled (k-set-link slot t))
             (grounded (k-grounded slot (syn-start s) (syn-end s))))
        slot))))
(define k-dletrec-fill (subr (maxeff checks spin) (k-slots) unit)
  (lambda (ss)
    (if (null? ss)
        #u
        (let ((t (k-parse-type (cdr (car ss)))))
          (begin (k-set-link (car (car ss)) t) (k-dletrec-fill (cdr ss)))))))
;; A use of a parametric abbreviation: its body, read with each parameter
;; bound to the description given for it.
(define k-expand-abbrev (subr (maxeff checks spin) (syn symbol k-params syn k-syns) int)
  (lambda (s name ps body args)
    (cond
      ((not (= (k-length args) (k-length ps)))
       (k-sfail (k-arity-message name (k-length ps) (k-length args)) s))
      ((> (get k-expanding) 64) (k-endless s name))
      (else (k-expand-bound s name body (k-abbrev-args ps args))))))
;; The family `name`'s body, read with its parameters bound as `bound`
;; says: a use inside with the same descriptions is the slot its type
;; will fill, a knot.
(define k-expand-bound (subr (maxeff checks spin) (syn symbol syn k-scope) int)
  (lambda (s name body bound)
    (let ((knot (k-knot-of (get k-knots) name bound)))
      (if (>= knot 0)
          knot
          (let* ((saved (get k-dscope)) (slot (k-slot)) (kept (get k-knots)))
            (begin
              (set k-knots (cons (product (1 name) (2 bound) (3 slot)) kept))
              (k-push-all bound)
              (set k-expanding (+ (get k-expanding) 1))
              (let ((t (k-parse-type body)))
                (begin (set k-expanding (- (get k-expanding) 1))
                       (set k-dscope saved)
                       (set k-knots kept)
                       (k-set-link slot t)
                       (k-grounded slot (syn-start s) (syn-end s))
                       slot))))))))
(define k-abbrev-args (subr (maxeff checks spin) (k-params k-syns) k-scope)
  (lambda (ps args)
    (if (null? ps)
        nil
        (let* ((k (extract (car ps) 2))
               (d (cond ((k-type-kind? k) (ds-rec (k-parse-type (car args))))
                        ((= k 0) (ds-region (k-parse-region (car args))))
                        ((= k 3) (ds-region (k-parse-place (car args))))
                        ((= k 5) (ds-size (k-parse-size (car args))))
                        ((= k 6) (ds-conv (k-parse-conv (car args))))
                        ((>= k 100) (ds-fun (k-parse-fun (car args) k)))
                        (else (ds-eff (k-parse-effect (car args))))))
               (rest (k-abbrev-args (cdr ps) (cdr args))))
          (cons (cons (extract (car ps) 1) d) rest)))))
(define* k-define-type (subr (maxeff checks spin) (symbol syn int int) int)
  (lambda (name def a b)
    (let ((ahead (k-ahead-take name)))
      (if (>= ahead 0)
          ;; Declared ahead: its slot is in scope already; fill it, and check
          ;; it grounded once every slot is filled.
          (let ((t (k-parse-type def)))
            (begin (k-set-link ahead t)
                   (set k-ahead-filled (cons (product (1 ahead) (2 a) (3 b)) (get k-ahead-filled)))
                   ahead))
          (let ((slot (k-slot)))
            (begin
              (k-push-desc name (ds-rec slot))
              (let ((t (k-parse-type def)))
                (begin (k-set-link slot t) (k-grounded slot a b) slot))))))))
;; Name or `dlambda` `s`, a description function.
(define k-fun-d (subr (maxeff checks spin) (syn) k-desc)
  (lambda (s) (df (k-parse-fun s -1))))
;; A `proj` argument: which kind it is shows in its shape, or, for a bare
;; name, in how the name is bound.
;; A convention, if name `s` is one of FX-26's own; else a type.
(define k-parse-conv-or-type (subr (maxeff checks spin) (syn) k-desc)
  (lambda (s)
    (let ((n (syn-name s)))
      (if (or (string=? n "cellular") (string=? n "native") (string=? n "fx"))
          (dc (k-parse-conv s))
          (dt (k-parse-type s))))))
;; What name `s`, meaning `d` (none or one), is as a `proj` argument: by how
;; it is bound; if it is not bound as a description, a convention or a type.
(define k-parse-d-bound (subr (maxeff checks spin) (syn (listof k-ds acyclic)) k-desc)
  (lambda (s d)
    (if (null? d)
        (if (null? (k-ctor-params (syn-name s))) (k-parse-conv-or-type s) (k-fun-d s))
        (tagcase (car d)
          (ds-fun (f) (k-fun-d s))
          (ds-abbrev (ps body) (if (null? ps) (k-parse-conv-or-type s) (k-fun-d s)))
          (ds-gen (g)
            (if (null? (extract (k-gen-of g) 2)) (k-parse-conv-or-type s) (k-fun-d s)))
          (ds-var (v k)
            (cond ((>= k 100) (k-fun-d s))
                  ((or (= k 0) (= k 3)) (dr (r-var v)))
                  ((= k 1) (de (k-one (a-var v))))
                  ((= k 5) (dz (k-size-var v)))
                  ((= k 6) (dc (cv-var v)))
                  (else (k-parse-conv-or-type s))))
          (ds-region (r) (dr r))
          (ds-eff (e) (de e))
          (ds-size (z) (dz z))
          (ds-conv (c) (dc c))
          (else x (k-parse-conv-or-type s))))))
;; A `proj` argument that is a name.
(define k-parse-d-name (subr (maxeff checks spin) (syn) k-desc)
  (lambda (s)
    (let* ((n (syn-name s)) (sym (string->symbol n)))
      (cond ((k-at-name? n) (dr (k-region-constant sym)))
            ((string=? n "pure") (de nil))
            ((string=? n "spin") (de (k-one (a-spin))))
            ((string=? n "const") (dr (r-frozen -1 #f)))
            ((string=? n "acyclic") (dr (r-frozen -1 #t)))
            ((string=? n "finite") (dz (sz-finite)))
            ((string=? n "heap") (dr (r-heap)))
            (else (k-parse-d-bound s (k-lookup-desc sym)))))))
(define k-parse-d (subr (maxeff checks spin) (syn) k-desc)
  (lambda (s)
    (cond ((tagcase s (atom (d a b) (datum-int? d)) (else x #f))
           ;; A natural number can only be a size.
           (dz (k-parse-size s)))
          ((syn-symbol? s) (k-parse-d-name s))
          (else
           (let ((hd (k-head (k-items s "a description"))))
             (cond ((string=? hd "dlambda") (k-fun-d s))
                   ((or (k-atom-head? hd) (string=? hd "maxeff")) (de (k-parse-effect s)))
                   ((or (string=? hd "+") (string=? hd "-")) (dz (k-parse-size s)))
                   (else (dt (k-parse-type s)))))))))
;; Whether effect `e` is variable `v` alone.
(define k-eff-is-var? (subr (read @globals) (k-eff int) bool)
  (lambda (e v)
    (and (not (null? e)) (null? (cdr e)) (tagcase (car e) (a-var (w) (= w v)) (else y #f)))))
;; Whether `d` is variable `v` and nothing more.
(define k-is-the-var? (subr (maxeff kreads spin) (k-desc int) bool)
  (lambda (d v)
    (tagcase d
      (dr (r) (tagcase r (r-var (w) (= w v)) (else y #f)))
      (de (e) (k-eff-is-var? e v))
      (dz (z)
        (tagcase z
          (sz-lin (k ts)
            (and (= k 0) (not (null? ts)) (null? (cdr ts))
                 (= (car (car ts)) v) (= (cdr (car ts)) 1)))
          (else y #f)))
      (dc (c) (tagcase c (cv-var (w) (= w v)) (else y #f)))
      (dt (t) (k-type-is-var? t v))
      (df (t) (k-type-is-var? t v)))))
;; Whether `ds` are `bs`'s variables, in order.
(define k-the-vars? (subr (maxeff kreads spin) (k-descs k-binders) bool)
  (lambda (ds bs)
    (cond ((null? ds) (null? bs))
          ((null? bs) #f)
          ((k-is-the-var? (car ds) (extract (car bs) 1)) (k-the-vars? (cdr ds) (cdr bs)))
          (else #f))))
;; Whether `f` is one of `bs`'s variables.
(define k-param-head? (subr (maxeff kreads spin) (int k-binders) bool)
  (lambda (f bs) (tagcase (k-get f) (ty-var (v) (k-binder-has? bs v)) (else y #f))))
;; `(dlambda bs body)`, or, where `body` only applies a function to the
;; parameters in order, that function (eta).
(define k-lam (subr (maxeff kstate spin) (k-binders k-desc) int)
  (lambda (bs body)
    (let ((eta (tagcase body
                 (dt (t)
                   (tagcase (k-get t)
                     (ty-app (f ds)
                       (if (and (k-the-vars? ds bs) (not (k-param-head? f bs))) f -1))
                     (else y -1)))
                 (else y -1))))
      (if (>= eta 0) eta (k-ty-new (ty-lam bs body))))))
;; Each of binders `bs`, as a description.
(define k-binders-as-descs (subr (maxeff kstate spin) (k-binders) k-descs)
  (lambda (bs)
    (if (null? bs)
        nil
        (let* ((d (k-binder-desc (extract (car bs) 2) (extract (car bs) 1)))
               (rest (k-binders-as-descs (cdr bs))))
          (the k-descs (cons d rest))))))
;; "`f` takes n description(s), and has m", `f` shown.
(define k-fun-arity-message (subr kbuilds (int int int) string)
  (lambda (f want have)
    (k-cat5 (k-quote (k-show-ty f)) " takes " (int->string want)
            " description(s), and has " (int->string have))))
;; Binders of `kinds`, each a fresh variable named as `names`.
(define k-fresh-named (subr (maxeff kstate spin) (k-names k-ids) k-binders)
  (lambda (ns ks)
    (if (null? ns)
        nil
        (let* ((v (k-new-dvar-of (car ns) (car ks))) (rest (k-fresh-named (cdr ns) (cdr ks))))
          (the k-binders (cons (product (1 v) (2 (car ks))) rest))))))
;; Each binder, as a type family's parameter is bound to what it is given.
(define k-binders-as-scope (subr (maxeff kstate spin) (k-binders) k-scope)
  (lambda (bs)
    (if (null? bs)
        nil
        (let* ((v (extract (car bs) 1)) (k (extract (car bs) 2))
               (d (cond ((k-type-kind? k) (ds-rec (k-ty-new (ty-var v))))
                        ((or (= k 0) (= k 3)) (ds-region (r-var v)))
                        ((= k 1) (ds-eff (k-one (a-var v))))
                        ((= k 5) (ds-size (k-size-var v)))
                        ((= k 6) (ds-conv (cv-var v)))
                        (else (ds-fun (k-ty-new (ty-var v))))))
               (rest (k-binders-as-scope (cdr bs))))
          (the k-scope (cons (cons (k-dvar-name v) d) rest))))))
;; Type form `n`, `listof` and kin, of `ts`, given `t` and `r`.
(define k-ctor-type (subr (maxeff kstate spin) (string k-binders) int)
  (lambda (n bs)
    (let* ((t (k-ty-new (ty-var (extract (car bs) 1))))
           (second (extract (car (cdr bs)) 1))
           (r (r-var (if (null? (cdr (cdr bs))) second (extract (car (cdr (cdr bs))) 1)))))
      (case n (("ref") (k-ty-new (ty-ref t r)))
              (("icell") (k-ty-new (ty-icell t r)))
              (("arrayof") (k-ty-new (ty-array t r)))
              (("mark-key") (k-ty-new (ty-markkey t r)))
              (("pairof") (k-ty-new (ty-pair t (k-ty-new (ty-var second)) r #f)))
              (else (let* ((slot (k-slot)) (pair (k-ty-new (ty-pair t slot r #t))))
                      (begin (k-set-link slot pair) slot)))))))
(define k-params-names (subr (read @globals) (k-params) k-names)
  (lambda (ps) (if (null? ps) nil (cons (extract (car ps) 1) (k-params-names (cdr ps))))))
(define k-params-kinds (subr (read @globals) (k-params) k-ids)
  (lambda (ps) (if (null? ps) nil (cons (extract (car ps) 2) (k-params-kinds (cdr ps))))))
;; Whether `n` is bound to a description function.
(define k-fun-bound? (subr (maxeff kreads (alloc @t)) (string) bool)
  (lambda (n)
    (let ((d (k-lookup-desc (string->symbol n))))
      (and (not (null? d))
           (tagcase (car d) (ds-var (v k) (k-arrow-kind? k)) (ds-fun (f) #t) (else y #f))))))
;; Binder `b`'s name.
(define k-binder-name (subr kreads ((productof (1 int) (2 int))) symbol)
  (lambda (b) (k-dvar-name (extract b 1))))
(define k-binder-names (subr (maxeff kreads spin) (k-binders) k-names)
  (lambda (bs) (if (null? bs) nil (cons (k-binder-name (car bs)) (k-binder-names (cdr bs))))))
;; `(select m t)`: as written, for checking to resolve where `m` is bound.
(define k-parse-select (subr (maxeff checks spin) (syn k-syns) int)
  (lambda (s items)
    (cond ((not (= (k-length items) 3)) (k-sfail "`(select module name)`" s))
          ((and (syn-symbol? (k-nth items 1)) (syn-symbol? (k-nth items 2)))
           (k-ty-new (ty-select (syn-head (k-nth items 1)) (syn-head (k-nth items 2)))))
          (else (k-sfail "`(select module name)`: a module's name, and a component's" s)))))
;; Function `f`, given `have` descriptions at `s`, where it takes `want`.
(define k-arity-fail (subr (maxeff checks spin) (int int int syn) void)
  (lambda (f want have s) (k-sfail (k-fun-arity-message f want have) s)))
;; Function `f`, at `s`, giving a `result` where a `wanted` is.
(define k-gives-fail (subr (maxeff checks spin) (int int string syn) void)
  (lambda (f result wanted s)
    (k-sfail (k-cat5 (k-quote (k-show-ty f)) " gives a description of kind " (k-kind-text result)
                     ", not " wanted)
             s)))
;; Function `f`, at `s`, not giving a `wanted`.
(define k-not-giving (subr (maxeff checks spin) (int string syn) void)
  (lambda (f wanted s) (k-sfail (k-cat3 (k-quote (k-show-ty f)) " does not give " wanted) s)))
;; A description of kind `k`, as written.
(define k-parse-desc-at (subr (maxeff checks spin) (syn int) k-desc)
  (lambda (s k)
    (cond ((k-type-kind? k) (dt (k-parse-type s)))
          ((= k 0) (dr (k-parse-region s)))
          ((= k 3) (dr (k-parse-place s)))
          ((= k 1) (de (k-parse-effect s)))
          ((= k 5) (dz (k-parse-size s)))
          ((= k 6) (dc (k-parse-conv s)))
          (else (df (k-parse-fun s k))))))
;; Descriptions `xs`, each of its kind in `ks`.
(define k-parse-descs-at (subr (maxeff checks spin) (k-syns k-ids) k-descs)
  (lambda (xs ks)
    (if (null? xs)
        nil
        (let ((d (k-parse-desc-at (car xs) (car ks))))
          (cons d (k-parse-descs-at (cdr xs) (cdr ks)))))))
;; Description `s`, of kind `k` if that is known (not -1).
(define k-parse-desc-of (subr (maxeff checks spin) (syn int) k-desc)
  (lambda (s k) (if (>= k 0) (k-parse-desc-at s k) (k-parse-d s))))
;; A description function, as written where one of kind `want` (-1 if not
;; known) is wanted.
(define k-parse-fun (subr (maxeff checks spin) (syn int) int)
  (lambda (s want)
    (let* ((f (k-parse-fun-node s want)) (got (k-fun-kind f)))
      (if (and (>= want 0) (>= got 0) (not (= got want)))
          (k-sfail (k-cat4 "a description function of kind " (k-kind-text want)
                           " is wanted, and this is of kind " (k-kind-text got))
                   s)
          f))))
(define k-parse-fun-node (subr (maxeff checks spin) (syn int) int)
  (lambda (s want)
    (if (syn-symbol? s)
        (k-fun-named s)
        (let ((usage (string-append "a description function: a name, `(dlambda ((name kind) …) "
                                    "description)` or `(select module name)`")))
          (tagcase s
            (lst (items d a b)
              (let ((hd (k-symbol-head items)))
                (case hd (("dlambda") (k-parse-dlambda s items want))
                         (("select") (k-parse-select s items))
                         (else
                          (cond ((k-fun-bound? hd) (k-parse-fun-app s items))
                                (else (k-sfail usage s)))))))
            (else x (k-sfail usage s)))))))
;; `(dlambda ((x k) …) d)`.
(define k-parse-dlambda (subr (maxeff checks spin) (syn k-syns int) int)
  (lambda (s items want)
    (if (not (= (k-length items) 3))
        (k-sfail "`(dlambda ((name kind) …) description)`" s)
        (let* ((result (if (>= want 0) (k-arrow-result want) -1))
               (saved (get k-dscope))
               (bs (k-parse-binders (k-nth items 1)))
               (none (if (null? bs) (k-sfail k-dlambda-empty (k-nth items 1)) #u))
               (body (k-parse-desc-of (k-nth items 2) result)))
          (begin (set k-dscope saved) (k-lam bs body))))))
;; `(g d …)`, where `g` gives a description function.
(define k-parse-fun-app (subr (maxeff checks spin) (syn k-syns) int)
  (lambda (s items)
    (let* ((g (k-parse-fun (car items) -1))
           (shown (k-quote (k-show-ty g)))
           (parts (k-arrow-parts (k-fun-kind g)))
           (no (k-cat3 shown " does not give a description function" "")))
      (cond ((or (null? parts) (not (k-arrow-kind? (cdr (car parts))))) (k-sfail no s))
            ((not (= (k-length (cdr items)) (k-length (car (car parts)))))
             (k-arity-fail g (k-length (car (car parts))) (k-length (cdr items)) s))
            (else
             (let ((d (k-apply-fun g (k-parse-descs-at (cdr items) (car (car parts))))))
               (tagcase d (df (f) f) (else y (k-sfail no s)))))))))
;; A description function named.
(define k-fun-named (subr (maxeff checks spin) (syn) int)
  (lambda (s)
    (let* ((n (syn-name s)) (sym (string->symbol n)) (d (k-lookup-desc sym))
           (no (k-cat3 (k-quote n) " is not a description function" "")))
      (if (null? d)
          (let ((ctor (k-ctor-params n)))
            (if (null? ctor) (k-sfail no s) (k-ctor-eta n (car ctor))))
          (tagcase (car d)
            (ds-var (v k) (if (k-arrow-kind? k) (k-ty-new (ty-var v)) (k-sfail no s)))
            (ds-fun (f) f)
            (ds-abbrev (ps body) (if (null? ps) (k-sfail no s) (k-abbrev-eta s sym ps body)))
            (ds-gen (g)
              (let ((ps (extract (k-gen-of g) 2)))
                (if (null? ps) (k-sfail no s) (k-gen-eta g ps))))
            (else x (k-sfail no s)))))))
;; A type family as a description function: `(dlambda ((p k) …) (name p …))`.
(define k-abbrev-eta (subr (maxeff checks spin) (syn symbol k-params syn) int)
  (lambda (s name ps body)
    (let* ((bs (k-fresh-named (k-params-names ps) (k-params-kinds ps)))
           (t (if (> (get k-expanding) 64)
                  (k-endless s name)
                  (k-expand-bound s name body (k-binders-as-scope bs)))))
      (k-lam bs (dt t)))))
;; A generative type as one.
(define k-gen-eta (subr (maxeff checks spin) (int k-binders) int)
  (lambda (g ps)
    (let* ((bs (k-fresh-named (k-binder-names ps) (k-binder-kinds ps)))
           (t (k-ty-new (ty-named g (k-binders-as-descs bs)))))
      (k-lam bs (dt t)))))
;; A type form, `listof` and kin, as one.
(define k-ctor-eta (subr (maxeff checks spin) (string k-params) int)
  (lambda (n ps)
    (let ((bs (k-fresh-named (k-params-names ps) (k-params-kinds ps))))
      (k-lam bs (dt (k-ctor-type n bs))))))
;; `(f d …)` as a type: `f` given the descriptions `args` are, of the
;; kinds it takes; reduced, if it is a `dlambda`. Where `f`'s kind is not
;; known yet (a `select`), what it is given is read by its shape, and
;; checked once it is resolved.
(define k-parse-app (subr (maxeff checks spin) (syn int k-syns) int)
  (lambda (s f args)
    (let ((parts (k-arrow-parts (k-fun-kind f))))
      (if (null? parts)
          (k-ty-new (ty-app f (k-parse-ds args)))
          (let ((ps (car (car parts))) (result (cdr (car parts))))
            (cond ((not (= (k-length args) (k-length ps)))
                   (k-arity-fail f (k-length ps) (k-length args) s))
                  ((not (k-type-kind? result)) (k-gives-fail f result "a type" s))
                  (else
                   (tagcase (k-apply-fun f (k-parse-descs-at args ps))
                     (dt (t) t)
                     (else y (k-not-giving f "a type" s))))))))))
(define k-parse-ds (subr (maxeff checks spin) (k-syns) k-descs)
  (lambda (xs)
    (if (null? xs) nil (let ((d (k-parse-d (car xs)))) (cons d (k-parse-ds (cdr xs)))))))
;; `(e d …)` in an effect, where `e` is a description function to an
;; effect: its effect, reduced if it is a `dlambda`; none if `items` are
;; no such application.
(define k-parse-effect-app (subr (maxeff checks spin) (syn k-syns) (listof k-eff acyclic))
  (lambda (s items)
    (let ((f (if (null? items)
                 -1
                 (let ((head (car items)))
                   (if (syn-symbol? head)
                       (if (k-fun-bound? (syn-name head)) (k-fun-named head) -1)
                       (if (string=? (k-list-head head) "dlambda") (k-parse-fun head -1) -1))))))
      (if (< f 0)
          nil
          (let ((parts (k-arrow-parts (k-fun-kind f))))
            (if (null? parts)
                nil
                (let ((ps (car (car parts))) (result (cdr (car parts))))
                  (cond ((not (= result 1)) (k-gives-fail f result "an effect" s))
                        ((not (= (k-length (cdr items)) (k-length ps)))
                         (k-arity-fail f (k-length ps) (k-length (cdr items)) s))
                        (else
                         (tagcase (k-apply-fun f (k-parse-descs-at (cdr items) ps))
                           (de (e) (the (listof k-eff acyclic) (cons e nil)))
                           (else y (k-not-giving f "an effect" s))))))))))))
;; `ps` reversed, onto `acc`.
(define k-parts-reversed (subr (maxeff (read @globals) (alloc @t)) (k-parts k-parts) k-parts)
  (lambda (ps acc) (if (null? ps) acc (k-parts-reversed (cdr ps) (cons (car ps) acc)))))
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
(define k-try-kind (subr (maxeff kstate (read @s) spin) (syn) int)
  (lambda (s)
    (let ((n (if (syn-symbol? s) (syn-name s) "")))
      (case n (("region") 0)
              (("place") 3)
              (("effect") 1)
              (("type") 2)
              (("data") 4)
              (("size") 5)
              (("conv") 6)
              (else
               (cond ((syn-symbol? s) -1)
                     (else (k-try-arrow-kind s))))))))
(define k-try-arrow-kind (subr (maxeff kstate (read @s) spin) (syn) int)
  (lambda (s)
    (let ((parts (k-arrow-syntax s)))
      (if (null? parts)
          -1
          (let* ((params (k-try-kinds (car (car parts))))
                 (result (k-try-kind (cdr (car parts)))))
            (cond ((or (k-has-id? params -1) (< result 0)) -1)
                  ((or (= result 0) (= result 3) (= result 5) (= result 6)) -1)
                  ((and (= result 1) (k-any-typed-kind? params)) -1)
                  (else (k-arrow params result))))))))
(define k-try-kinds (subr (maxeff kstate (read @s) spin) (k-syns) k-ids)
  (lambda (xs)
    (if (null? xs)
        nil
        (let* ((k (k-try-kind (car xs))) (rest (k-try-kinds (cdr xs))))
          (the k-ids (cons k rest))))))
;; Abstract types `names`, each a variable of kind `k`, in scope from here,
;; onto `abs`; a type constructor among `k-abstract-funs`.
(define k-abs-bound (subr (maxeff kstate spin) (k-names int k-parts) k-parts)
  (lambda (names k abs)
    (if (null? names)
        abs
        (let* ((n (car names)) (v (k-new-dvar-of n k)))
          (begin (if (= k 2) #u (set k-abstract-funs (cons v (get k-abstract-funs))))
                 (k-push-desc n (ds-var v k))
                 (k-abs-bound (cdr names) k (cons (product (1 n) (2 v)) abs)))))))
;; `(name type)` onto `ps`.
(define k-part-onto (subr (alloc @t) (symbol int k-parts) k-parts)
  (lambda (n t ps) (cons (product (1 n) (2 t)) ps)))
;; Whether `s` is written as an effect: `pure`, `spin`, a name bound to one,
;; or one of `k-parse-effect`'s atoms or `maxeff`.
(define k-effect-shaped? (subr (maxeff kreads (read @s) (alloc @t) spin) (syn) bool)
  (lambda (s)
    (if (syn-symbol? s)
        (let ((n (syn-name s)))
          (or (string=? n "pure") (string=? n "spin")
              (let ((d (k-lookup-desc (string->symbol n))))
                (and (not (null? d))
                     (tagcase (car d) (ds-eff (e) #t) (ds-var (v k) (= k 1)) (else x #f))))))
        (let ((h (k-list-head s))) (or (k-atom-head? h) (string=? h "maxeff"))))))
;; A `moduleof`'s description `what` of `name`, in scope in what follows it:
;; `(desc e E)`, an effect, as a module's `define-effect` gives; a description
;; function; or a type.
(define k-moduleof-desc (subr (maxeff checks spin) (symbol syn) int)
  (lambda (name what)
    (cond ((k-effect-shaped? what)
           (let* ((e (k-parse-effect what)) (d (k-effect-desc e)))
             (begin (k-push-desc name (ds-eff e)) d)))
          ((string=? (k-list-head what) "dlambda")
           (let ((f (k-parse-fun what -1))) (begin (k-push-desc name (ds-fun f)) f)))
          (else (let ((t (k-parse-type what))) (begin (k-push-desc name (ds-rec t)) t))))))
;; A `moduleof`'s components `cs`, those before them read into `abs`, `ds`
;; and `vs` (newest first), their names `seen` (types and effects) and `vseen`
;; (values): a value may have a type's name.
(define k-moduleof-comps
  (subr (maxeff checks spin) (k-syns k-parts k-parts k-parts k-names k-names) int)
  (lambda (cs abs ds vs seen vseen)
    (if (null? cs)
        (let ((ds (k-parts-reversed ds nil)) (vs (k-parts-reversed vs nil)))
          (k-ty-new (ty-module (k-parts-reversed abs nil) ds vs)))
        (let* ((c (car cs))
               (parts (k-items c "a module component"))
               (shaped (k-shape (= (k-length parts) 3) k-moduleof-usage c))
               (head (k-symbol-head parts))
               (names (k-component-names (k-nth parts 1) head))
               (val? (string=? head "val"))
               (seen (if val? seen (k-names-once names seen c)))
               (vseen (if val? (k-names-once names vseen c) vseen))
               (what (k-nth parts 2)))
          (case head
            (("abs")
             (let ((k (k-try-kind what)))
               (if (or (= k 2) (and (k-arrow-kind? k) (= (k-arrow-result k) 2)))
                   (k-moduleof-comps (cdr cs) (k-abs-bound names k abs) ds vs seen vseen)
                   (k-sfail k-abs-usage what))))
            (("desc")
             (let ((d (k-moduleof-desc (car names) what)))
               (k-moduleof-comps (cdr cs) abs (k-part-onto (car names) d ds) vs seen vseen)))
            (("val")
             (let ((t (k-parse-type what)))
               (k-moduleof-comps (cdr cs) abs ds (k-part-onto (car names) t vs) seen vseen)))
            (else (k-sfail k-moduleof-usage (car parts))))))))
;; `(moduleof …)`, each abstract type a binder in scope in what follows it;
;; or `(select m t)`.
(define k-read-module-type (subr (maxeff checks spin) (syn k-syns symbol) int)
  (lambda (s items hd)
    (if (symbol=? hd 'select)
        (k-parse-select s items)
        (let* ((saved (get k-dscope)) (t (k-moduleof-comps (cdr items) nil nil nil nil nil)))
          (begin (set k-dscope saved) t)))))
;; The types of parts `ps`, onto `tail`.
(define k-parts-onto (subr (maxeff (read @globals) (alloc @t)) (k-parts k-ids) k-ids)
  (lambda (ps tail)
    (if (null? ps) tail (cons (extract (car ps) 2) (k-parts-onto (cdr ps) tail)))))
;; `ts`, and `t` after them.
(define k-ids-then (subr (maxeff (read @globals) (alloc @t)) (k-ids int) k-ids)
  (lambda (ts t) (if (null? ts) (cons t nil) (cons (car ts) (k-ids-then (cdr ts) t)))))
;; The types and functions among descriptions `ds`.
(define k-desc-kids (subr (maxeff (read @globals) (alloc @t)) (k-descs) k-ids)
  (lambda (ds)
    (if (null? ds)
        nil
        (let ((rest (k-desc-kids (cdr ds))))
          (tagcase (car ds) (dt (x) (cons x rest)) (df (x) (cons x rest)) (else y rest))))))
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
      (ty-pair (a d r nl) (k-ids-then (the k-ids (cons a nil)) d))
      (ty-tag (a h e r) (k-ids-then (the k-ids (cons a nil)) h))
      (ty-comp (x a e r) (k-ids-then (the k-ids (cons x nil)) a))
      (ty-product (ps) (k-parts-onto ps nil))
      (ty-sum (ps) (k-parts-onto ps nil))
      (ty-bloblet (fs z r) fs)
      (ty-named (g ds) (k-desc-kids ds))
      (ty-app (f ds) (the k-ids (cons f (k-desc-kids ds))))
      (ty-lam (bs x) (k-desc-kids (the k-descs (cons x nil))))
      (ty-nlist (e z r) (the k-ids (cons e nil)))
      (ty-module (abs ds vs) (k-parts-onto ds (k-parts-onto vs nil)))
      (else y nil))))
(define k-selects-from (subr (maxeff kstate spin) (int k-seen (ref k-selects @t)) unit)
  (lambda (t seen out)
    (let ((t (k-resolve t)))
      (if (k-seen? seen t)
          #u
          (begin
            (tagcase (k-get t)
              (ty-select (m n) (set out (cons (product (1 m) (2 n) (3 t)) (get out))))
              (else y (k-selects-each (k-ty-kids t) seen out))))))))
(define k-selects-each (subr (maxeff kstate spin) (k-ids k-seen (ref k-selects @t)) unit)
  (lambda (ts seen out)
    (if (null? ts)
        #u
        (begin (k-selects-from (car ts) seen out) (k-selects-each (cdr ts) seen out)))))
;; `ss` reversed, onto `acc`.
(define k-selects-reversed
  (subr (maxeff (read @globals) (alloc @t)) (k-selects k-selects) k-selects)
  (lambda (ss acc) (if (null? ss) acc (k-selects-reversed (cdr ss) (cons (car ss) acc)))))
;; The `select`s in `t`, in the order first met.
(define k-selects-in (subr (maxeff kstate spin) (int) k-selects)
  (lambda (t)
    (let ((out (the (ref k-selects @t) (new nil))))
      (begin (k-selects-from t (k-new-seen) out)
             (k-selects-reversed (get out) nil)))))
;; A procedure type's parameter written `(name type)`, where `name` names no
;; type or type form: its name, in a list of one; none if it is not one.
(define k-param-name (subr (maxeff kreads (alloc @t) (read @s) spin) (syn) k-names)
  (lambda (p)
    (tagcase p
      (lst (items d a b)
        (if (and (= (k-length items) 2) (syn-symbol? (car items)))
            (let ((n (syn-head (car items))))
              (if (or (k-has-name? k-type-forms n) (k-has-name? k-keywords n)
                      (not (null? (k-lookup-desc n))) (>= (k-find (get k-base) n) 0))
                  nil
                  (the k-names (cons n nil))))
            nil))
      (else x nil))))
;; Where `m` last is among `names` (each a name, or `||` for none), from
;; `i`; or -1.
(define k-name-last (subr (maxeff kreads spin) (k-names symbol int) int)
  (lambda (names m i)
    (if (null? names)
        -1
        (let ((later (k-name-last (cdr names) m (+ i 1))))
          (if (and (< later 0) (symbol=? (car names) m)) i later)))))
;; Of `found`, those that select from a parameter of `names`: each as
;; `(select $k x)`.
(define k-param-selects (subr (maxeff kstate spin) (k-selects k-names) k-selects)
  (lambda (found names)
    (if (null? found)
        nil
        (let* ((m (extract (car found) 1)) (x (extract (car found) 2))
               (k (k-name-last names m 0))
               (rest (k-param-selects (cdr found) names)))
          (if (< k 0)
              rest
              (the k-selects (cons (product (1 m) (2 x) (3 (k-ty-new (ty-param k x)))) rest)))))))
(define k-all-unnamed? (subr (maxeff (read @globals) spin) (k-names) bool)
  (lambda (ns) (or (null? ns) (and (symbol=? (car ns) k-no-name) (k-all-unnamed? (cdr ns))))))
;; `t` with each `(select m x)` of a parameter named before it, the `k`th,
;; made `(select $k x)`.
(define k-select-params (subr (maxeff kstate spin) (int k-names) int)
  (lambda (t names)
    (let ((sel (if (k-all-unnamed? names)
                   (the k-selects nil)
                   (k-param-selects (k-selects-in t) names))))
      (if (null? sel)
          t
          (let ((outer (get k-select-map)))
            (begin (set k-select-map sel)
                   (let ((r (k-subst t nil))) (begin (set k-select-map outer) r))))))))
;; `names` with `n` last.
(define k-names-snoc (subr (maxeff (read @globals) (alloc @t) spin) (k-names symbol) k-names)
  (lambda (ns n) (if (null? ns) (cons n nil) (cons (car ns) (k-names-snoc (cdr ns) n)))))
;; A `subr` type's parameters `ps` (from those named `names`) and its
;; result `r`, read: their types, the result last.
(define k-read-params-from (subr (maxeff checks spin) (k-syns syn k-names) k-ids)
  (lambda (ps r names)
    (if (null? ps)
        (cons (k-select-params (k-parse-type r) names) nil)
        (let* ((named (k-param-name (car ps)))
               (written (if (null? named) (car ps) (k-nth (k-items (car ps) "a parameter") 1)))
               (t (k-select-params (k-parse-type written) names))
               (name (if (null? named) k-no-name (car named)))
               (rest (k-read-params-from (cdr ps) r (k-names-snoc names name))))
          (cons t rest)))))
(define k-read-params (subr (maxeff checks spin) (k-syns syn) k-ids)
  (lambda (ps r) (k-read-params-from ps r nil)))))

(define k-parse-effect (with check-read-types-module k-parse-effect))
(define k-parse-types (with check-read-types-module k-parse-types))
(define k-parse-type (with check-read-types-module k-parse-type))
(define k-define-type (with check-read-types-module k-define-type))
(define k-parse-d (with check-read-types-module k-parse-d))
(define k-lam (with check-read-types-module k-lam))
(define k-binders-as-descs (with check-read-types-module k-binders-as-descs))
(define k-parse-fun (with check-read-types-module k-parse-fun))
(define k-parts-reversed (with check-read-types-module k-parts-reversed))
(define k-part-onto (with check-read-types-module k-part-onto))
(define k-ids-then (with check-read-types-module k-ids-then))
(define k-desc-kids (with check-read-types-module k-desc-kids))
(define k-ty-kids (with check-read-types-module k-ty-kids))
(define k-selects-in (with check-read-types-module k-selects-in))
