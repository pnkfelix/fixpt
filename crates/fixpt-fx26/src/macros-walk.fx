;;; A program's walk, in FX-26 (`docs/research/binding-shapes.md`;
;;; `macros/shapes.rs`): a program's form after expansion aligned with the
;;; binding structure of the kernel's forms and `scope-forms`, and walked
;;; (`macros-align.fx`'s program mode, `macros-scopes.fx`'s `walk`), as the
;;; checkers will read it. Part of the expander: loaded by
;;; `macros-shaper.fx`, and loading an instance of `macros-scopes.fx` of its
;;; own, since a program's walk reads no macro's signature.

(module-parameters ((rs region) (re region) (rm region) (rc region) (rp region)))
(define scopes-module ((proj (load-module "fx26:macros-scopes.fx") rs re rm rc rp)))
(define align-module (with scopes-module align-module))
(define types-module (with align-module types-module))
(define parser-module (with types-module parser-module))
(define reader-types (with parser-module reader-types))
(import reader-types atom lst dotted vec (type syn))
(import parser-module parse-tag p-ok p-err syn-symbol? syn-symbol syn-name mk-symbol mk-list len
        nth syn-string? syn-datums (type syns-a names presult loaded-file loaded-files)
        (effect parses tree-builds))
(import types-module kind-of proper-items s-item s-expr syn-keyword? split
        (type fails addr atm atms))
(import align-module align node-export node-imports node-syn node-core node-kids node-path nnodes
        nodes-reset!
        program-walk unplaced lv-rib lv-earlier lv-shape lv-cage k-binder k-ref k-form k-pair
        k-desc k-seq atm-lit
        env-empty env-lookup binder-name
        (type level levels found rooted env))
(import scopes-module walk evaluate)

;;; ------------------------------------------------------------ a program's walk

;; Program `form`, after expansion, aligned and walked: its root node, and
;; what the walk found, each binder and name referred to with its
;; environment.
(define walked (->* (fails syn bool) (tupleof int found))
  (lambda (fail form top)
    (begin
      (set program-walk #t)
      (nodes-reset!)
      (set unplaced nil)
      (let* ((root (align fail 3 nil (if top (s-item) (s-expr)) form -1 nil))
             (found (walk fail root env-empty #f 0)))
        (begin (set program-walk #f) (tuple root found))))))

;; Each of `forms`, a program's after expansion, its local value binders
;; renamed as the walk finds their scopes, written (`macros.rs`'s
;; `Macros::alpha_renamed`, for `tests/scopes.rs`, which holds the two walks
;; to one another): `walk: ` and why, where one does not walk.
(define walked-forms (->* (syns-a) (listof string acyclic))
  (lambda (forms)
    (if (null? forms)
        nil
        (cons (walked-one (car forms)) (walked-forms (cdr forms))))))
(define walked-out (ref string rs) (new ""))
(define walked-one (->* (syn) string)
  (lambda (form)
    (let ((r (prompt parse-tag
                     (begin (set walked-out (show-renamed (alpha-renamed pfail-walk form)))
                            (p-ok nil))
                     (lambda ((r presult)) r))))
      (begin
        (set program-walk #f)
        (tagcase r
          (p-err (why a b) (string-append "walk: " why))
          (else y (get walked-out)))))))
(define pfail-walk (->* (string int int) void)
  (lambda (message a b) (abort-current-continuation parse-tag (p-err message a b))))

;; Program `form` with each local value binder renamed, `name%k`, `k` its
;; place among them in the order they are written, and each reference to
;; it: but a definition's name, and every binder of a name some reference
;; reaches only past what a `with` or `include` gives, or that the walk
;; cannot place.
(define alpha-renamed (->* (fails syn) syn)
  (lambda (fail form)
    (let* ((w (walked fail form #t)) (root (extract w 1)) (found (extract w 2))
           (defined (defined-binders fail 0 (get nnodes) nil))
           (t (targets found nil nil))
           (kept (append (extract t 1) (get unplaced)))
           (binders (sorted-binders (renamable 0 (get nnodes) defined kept nil) nil))
           (names (numbered binders 1 nil))
           (refs (referred (extract t 2) names nil)))
      (renamed-syn form nil (append names refs)))))
;; The nodes a module's items or a program's definitions bind by: what a
;; definition's form exports.
(define defined-binders (->* (fails int int (listof int acyclic)) (listof int acyclic))
  (lambda (fail i n out)
    (if (= i n)
        out
        (defined-binders fail (+ i 1) n
          (let ((k (kind-of (node-core i))))
            (if (or (= k 14) (= k 11))
                (tagcase (node-kids i)
                  (k-form (x)
                    (let ((ex (node-export x)))
                      (if (null? ex)
                          out
                          (lits-onto (evaluate fail (extract (car ex) 1) (extract (car ex) 2)
                                       (node-syn i))
                                     out))))
                  (else y out))
                out))))))
(define lits-onto (->* (levels (listof int acyclic)) (listof int acyclic))
  (lambda (ls out)
    (if (null? ls)
        out
        (lits-onto (cdr ls)
                   (tagcase (car ls) (lv-rib (as) (atm-lits as out)) (else y out))))))
(define atm-lits (->* (atms (listof int acyclic)) (listof int acyclic))
  (lambda (as out)
    (if (null? as)
        out
        (atm-lits (cdr as) (tagcase (car as) (atm-lit (b d) (cons b out)) (else y out))))))
;; Of `found`, each value reference's binder, innermost first: the names
;; reached only past a module's names, kept (not renamed); and each
;; reference with its binder's node.
(define-type pairs (listof (tupleof int int) acyclic))
(define targets (->* (found names pairs) (tupleof names pairs))
  (lambda (found kept out)
    (if (null? found)
        (tuple kept out)
        (let ((at (extract (car found) 1)) (env (extract (car found) 2)))
          (tagcase (node-kids at)
            (k-ref (n d free)
              (if d
                  (targets (cdr found) kept out)
                  (let ((b (binder-in n env)))
                    (cond ((= b -1) (targets (cdr found) kept out))
                          ((= b -2) (targets (cdr found) (cons n kept) out))
                          (else (targets (cdr found) kept (cons (tuple at b) out)))))))
            (else y (targets (cdr found) kept out)))))))
;; Value binder `n`'s node in `env`, innermost first: -1 if none binds it,
;; -2 if a module's names are looked past first.
(define binder-in (->* (symbol env) int)
  (lambda (n env)
    (let ((l (env-lookup env n #f 0 binder-name)))
      (case (extract l 1) ((0) (extract l 2)) ((1) -2) (else -1)))))
(define value-binder-in (->* (symbol atms) int)
  (lambda (n as)
    (if (null? as)
        -1
        (tagcase (car as)
          (atm-lit (b d)
            (if (and (not d) (tagcase (node-kids b) (k-binder (m e) (symbol=? m n)) (else y #f)))
                b
                (value-binder-in n (cdr as))))
          (else y (value-binder-in n (cdr as)))))))
;; Each value binder's node from `i` to `n`, but those of `defined` and of
;; a name of `kept`.
(define renamable
  (->* (int int (listof int acyclic) names (listof int acyclic)) (listof int acyclic))
  (lambda (i n defined kept out)
    (if (= i n)
        out
        (renamable (+ i 1) n defined kept
                   (tagcase (node-kids i)
                     (k-binder (m d)
                       (if (or d (int-in? i defined) (sym-in? m kept)) out (cons i out)))
                     (else y out))))))
(define int-in? (->* (int (listof int acyclic)) bool)
  (lambda (i is) (and (not (null? is)) (or (= i (car is)) (int-in? i (cdr is))))))
(define sym-in? (->* (symbol names) bool)
  (lambda (n ns) (and (not (null? ns)) (or (symbol=? n (car ns)) (sym-in? n (cdr ns))))))
;; Nodes `xs` in the order their parts are written, a list's first part
;; before its rest, one of each path. (A program walk's paths are kept
;; innermost step first, `path+`: each in order, once.)
(define sorted-binders
  (->* ((listof int acyclic) (listof (tupleof int addr) acyclic)) (listof int acyclic))
  (lambda (xs out)
    (if (null? xs)
        (the (listof int acyclic) (map-firsts out))
        (sorted-binders (cdr xs) (inserted (tuple (car xs) (reverse (node-path (car xs)))) out)))))
(define map-firsts (->* ((listof (tupleof int addr) acyclic)) (listof int acyclic))
  (lambda (xs) (if (null? xs) nil (cons (extract (car xs) 1) (map-firsts (cdr xs))))))
(define inserted (->* ((tupleof int addr) (listof (tupleof int addr) acyclic))
                      (listof (tupleof int addr) acyclic))
  (lambda (x out)
    (cond ((null? out) (list x))
          ((addr=? (extract x 2) (extract (car out) 2)) out)
          ((addr<? (extract x 2) (extract (car out) 2)) (cons x out))
          (else (cons (car out) (inserted x (cdr out)))))))
(define addr<? (->* (addr addr) bool)
  (lambda (a b)
    (cond ((null? b) #f)
          ((null? a) #t)
          ((eq? (car a) (car b)) (addr<? (cdr a) (cdr b)))
          (else (car a)))))
(define addr=? (->* (addr addr) bool)
  (lambda (a b)
    (cond ((null? a) (null? b))
          ((null? b) #f)
          (else (and (eq? (car a) (car b)) (addr=? (cdr a) (cdr b)))))))
;; Each of binders `bs` with its new name, `name%k` from `k`, by its path.
(define-type renames (listof (tupleof addr string) acyclic))
(define numbered (->* ((listof int acyclic) int renames) renames)
  (lambda (bs k out)
    (if (null? bs)
        out
        (numbered (cdr bs) (+ k 1)
                  (cons (tuple (node-path (car bs))
                               (string-append (syn-name (node-syn (car bs))) "%" (int->string k)))
                        out)))))
;; Each reference of `pairs` whose binder is renamed, with that name.
(define referred (->* (pairs renames renames) renames)
  (lambda (ps names out)
    (if (null? ps)
        out
        (let ((nm (name-at (node-path (extract (car ps) 2)) names)))
          (referred (cdr ps) names
                    (if (null? nm) out (cons (tuple (node-path (extract (car ps) 1)) (car nm))
                                         out)))))))
(define name-at (->* (addr renames) (listof string acyclic))
  (lambda (p rs)
    (cond ((null? rs) nil)
          ((addr=? p (extract (car rs) 1)) (list (extract (car rs) 2)))
          (else (name-at p (cdr rs))))))
;; `s`, at `path` (innermost step first, as a walk's), each name at a path
;; of `rs` renamed so.
(define renamed-syn (->* (syn addr renames) syn)
  (lambda (s path rs)
    (tagcase s
      (lst (items d a b x) (lst (renamed-items items path rs) d a b x))
      (dotted (items tail d a b x)
        (dotted (renamed-items items path rs) (renamed-syn tail (falses path (len items)) rs) d a
          b x))
      ;; A string written empty: what it holds binds nothing, and is not
      ;; escaped as written (`show-syn`).
      (atom (dt a b x)
        (cond ((string? dt) (atom "" a b x))
              ((syn-symbol? s)
               (let ((nm (name-at path rs)))
                 (if (null? nm) s (atom (string->symbol (car nm)) a b x))))
              (else s)))
      (else y s))))
(define renamed-items (->* (syns-a addr renames) syns-a)
  (lambda (items path rs)
    (if (null? items)
        nil
        (cons (renamed-syn (car items) (cons #t path) rs)
              (renamed-items (cdr items) (cons #f path) rs)))))
;; Path `p`, innermost step first, `k` cdrs further.
(define falses (->* (addr int) addr)
  (lambda (p k) (if (= k 0) p (falses (cons #f p) (- k 1)))))
;; `s` written.
(define show-renamed (->* (syn) string)
  (lambda (s) ((with types-module show-syn) s)))
