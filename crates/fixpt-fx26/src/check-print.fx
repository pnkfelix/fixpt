;;; The checker, in FX-26: types and effects shown as the Rust checker shows
;;; them; and what a type holds: where a procedure kept in it could reach
;;; itself, and at which polarities a variable occurs in it.
;;; Part of the checker, `check-types.fx` first (PLAN.md §11, step 10).

;;; ------------------------------------------------------------ printing

;; Its types, those it uses of the files before it, and the signatures of
;; what it is given.
;; Its types (`check-print-types.fx`), loaded before the module so that they are not
;; among its values; the module names what it uses of them.
(let* ((check-print-types (load-module "fx26:check-print-types.fx"))
       (eager-reader-types ((proj (load-module "fx26:eager-reader-types.fx") @s @e @m @c)))
       (check-types-types (load-module "fx26:check-types-types.fx"))
       (check-print-parts-types (load-module "fx26:check-print-parts-types.fx"))
       (check-env-types (load-module "fx26:check-env-types.fx"))
       (check-logic-types (load-module "fx26:check-logic-types.fx")))
  ;; What it is given: the modules of the files before it that it uses.
  (lambda ((check-types (select check-types-types check-types-sig))
           (check-print-parts (select check-print-parts-types check-print-parts-sig))
           (check-env (select check-env-types check-env-sig))
           (check-logic (select check-logic-types check-logic-sig)))
    (module
(hide (include check-print-types) (include eager-reader-types) (include check-types-types))
;; The types it uses of the files before it.
;; What it uses of the modules it is given: all of each, hidden.
(hide (include check-types) (include check-print-parts) (include check-env))
(import check-logic k-show-spec k-latent-split)

;; What a type is shown as so far (`check-print-types.fx`).
(define k-shown-none k-shown (product (1 (the k-strings nil)) (2 (the k-ids nil)) (3 0)))
;; `st`, then `s`.
(define k-put (->* (string k-shown) k-shown)
  (lambda (s st)
    (product (1 (the k-strings (cons s (extract st 1)))) (2 (extract st 2))
             (3 (+ (extract st 3) 1)))))
;; `st`, its depths `ds`.
(define k-shown-depths (->* (k-shown k-ids) k-shown)
  (lambda (st ds) (product (1 (extract st 1)) (2 ds) (3 (extract st 3)))))
;; `ds` without `d`.
(define k-ids-without (->* (k-ids int) k-ids)
  (lambda (ds d)
    (cond ((null? ds) ds)
          ((= (car ds) d) (k-ids-without (cdr ds) d))
          (else (the k-ids (cons (car ds) (k-ids-without (cdr ds) d)))))))
;; The first `k` pieces of `xs`, then `mid`, then the rest: `(mu %d ` put
;; before a node's pieces once it is known to be met again below.
(define k-pieces-before (->* (k-strings int string) k-strings)
  (lambda (xs k mid)
    (if (or (<= k 0) (null? xs))
        (the k-strings (cons mid xs))
        (the k-strings (cons (car xs) (k-pieces-before (cdr xs) (- k 1) mid))))))
;; The pieces, the last first, joined: their characters gathered, last to
;; first, into one list in an arena of its own, made a string once.
(define k-pieces-string (->* (k-strings) string)
  (lambda (xs)
    (letrena r
      (letrec ((chars (subr (alloc r) (string int (listof char r)) (listof char r))
                 (lambda (s i acc)
                   (if (< i 0) acc (chars s (- i 1) (rcons r (string-ref s i) acc)))))
               (all (subr (maxeff (alloc r) (read @t)) (k-strings (listof char r)) (listof char r))
                 (lambda (xs acc)
                   (if (null? xs)
                       acc
                       (all (cdr xs) (chars (car xs) (- (string-length (car xs)) 1) acc))))))
        (list->string (all xs nil))))))
(define-rec
  (k-show-on (->* (int k-printing k-shown) k-shown)
    (lambda (t path st)
      (let* ((t (k-resolve t))
             (named (k-part-named (extract path 2) t))
             (name (if (null? named) (k-abbrev-by (extract path 3) t) named)))
        (if (null? name) (k-show-body t path st) (k-put (car name) st)))))
  ;; Each of `ts`, `sep` between each two.
  (k-show-seq (->* (k-ids k-printing string k-shown) k-shown)
    (lambda (ts path sep st)
      (cond ((null? ts) st)
            ((null? (cdr ts)) (k-show-on (car ts) path st))
            (else (k-show-seq (cdr ts) path sep (k-put sep (k-show-on (car ts) path st)))))))
  ;; Each part's ` (label type)`.
  (k-show-parts (->* (k-parts k-printing k-shown) k-shown)
    (lambda (ps path st)
      (if (null? ps)
          st
          (let* ((st (k-put (k-cat3 " (" (symbol->string (extract (car ps) 1)) " ") st))
                 (st (k-put ")" (k-show-on (extract (car ps) 2) path st))))
            (k-show-parts (cdr ps) path st)))))
  (k-show-desc (->* (k-desc k-printing k-shown) k-shown)
    (lambda (d p st)
      (tagcase d
        (dt (t) (k-show-on t p st))
        (dr (r) (k-put (k-region-show r) st))
        (de (e) (k-put (k-show-effect e) st))
        (dz (z) (k-put (k-show-size z) st))
        (dc (c) (k-put (k-conv-show c) st))
        (df (f) (k-show-on f p st)))))
  ;; Each of `ds`, a space between each two.
  (k-show-descs (->* (k-descs k-printing k-shown) k-shown)
    (lambda (ds p st)
      (cond ((null? ds) st)
            ((null? (cdr ds)) (k-show-desc (car ds) p st))
            (else (k-show-descs (cdr ds) p (k-put " " (k-show-desc (car ds) p st)))))))
  ;; A `subr` type; with a specification, its parameters by their names,
  ;; and its clauses after the result.
  ;; What a `bool` result proves, `(bool (then …) (else …))`, as written;
  ;; a specification's parameters by their names, where it has clauses, and
  ;; its clauses after the result.
  (k-show-subr (->* (k-eff k-ids int k-conv k-specs k-printing k-shown) k-shown)
    (lambda (e ps r cv sp p st)
      (let* ((split (if (null? sp) nil (k-latent-split (extract (car sp) 4))))
             (clauses
              (cond ((null? sp) "")
                    ((null? split) (k-show-spec (car sp)))
                    (else (let ((s (car sp)))
                            (k-show-spec (product (1 (extract s 1)) (2 (extract s 2))
                                                  (3 (extract s 3))
                                                  (4 (extract (car split) 3))))))))
             (st (k-put (k-cat5 "(subr " (k-conv-prefix cv) (k-show-effect e) " (" "") st))
             (st (k-put ") " (if (string=? clauses "")
                                 (k-show-seq ps p " " st)
                                 (k-show-named ps (extract (car sp) 1) p st))))
             (st (if (null? split)
                     (k-show-on r p st)
                     (let ((l (car split)))
                       (k-put (k-cat5 "(bool " (k-show-props "then" (extract l 1)) " "
                                      (k-show-props "else" (extract l 2)) ")")
                              st)))))
        (k-put (string-append clauses ")") st))))
  ;; Parameters `ps`, each `(name : T)` where `names` names it, a space between
  ;; each two.
  (k-show-named (->* (k-ids k-names k-printing k-shown) k-shown)
    (lambda (ps names p st)
      (if (null? ps)
          st
          (let* ((n (if (null? names) '|| (car names)))
                 (st (if (symbol=? n '||) st (k-put (k-cat3 "(" (symbol->string n) " : ") st)))
                 (st (k-show-on (car ps) p st))
                 (st (if (symbol=? n '||) st (k-put ")" st)))
                 (st (if (null? (cdr ps)) st (k-put " " st))))
            (k-show-named (cdr ps) (if (null? names) names (cdr names)) p st)))))
  ;; `(head a h e r)`: a prompt tag's type, or a composable continuation's.
  (k-show-control (->* (string int int k-eff k-region k-printing k-shown) k-shown)
    (lambda (head a h e r p st)
      (let* ((st (k-put " " (k-show-on a p (k-put head st))))
             (st (k-show-on h p st)))
        (k-put (k-cat5 " " (k-show-effect e) " " (k-region-show r) ")") st))))
  ;; `(head a r)`.
  (k-show-in-region (->* (string int k-region k-printing k-shown) k-shown)
    (lambda (head a r p st)
      (k-put (k-cat3 " " (k-region-show r) ")") (k-show-on a p (k-put head st)))))
  ;; A node met again on the way down is a cycle: named by its depth, and
  ;; written `(mu %d …)` where the cycle starts, once its pieces are known
  ;; to name it.
  (k-show-body (->* (int k-printing k-shown) k-shown)
    (lambda (t path st)
      (let ((ids (extract path 1)))
        (if (k-has-id? ids t)
            (let ((d (k-depth-of ids t)))
              (k-put (string-append "%" (int->string d))
                     (if (k-has-id? (extract st 2) d)
                         st
                         (k-shown-depths st (the k-ids (cons d (extract st 2)))))))
            (let* ((p (product (1 (the k-ids (cons t ids))) (2 (extract path 2))
                               (3 (extract path 3))))
                   (d (k-length (extract p 1)))
                   (out (k-show-node t p st)))
              (if (k-has-id? (extract out 2) d)
                  (let ((mu (k-cat3 "(mu %" (int->string d) " "))
                        (n (- (extract out 3) (extract st 3))))
                    (product (1 (the k-strings
                                  (cons ")" (k-pieces-before (extract out 1) n mu))))
                             (2 (k-ids-without (extract out 2) d))
                             (3 (+ (extract out 3) 2))))
                  out))))))
  ;; What node `t` shows as, `p` the path to it from the root, newest
  ;; first.
  (k-show-node (->* (int k-printing k-shown) k-shown)
    (lambda (t p st)
      (tagcase (k-get t)
        (ty-base (s) (k-put (symbol->string s) st))
        (ty-void () (k-put "void" st))
        (ty-nil () (k-put "nil" st))
        (ty-false () (k-put "false" st))
        (ty-union (ms) (k-put ")" (k-show-seq ms p " " (k-put "(union " st))))
        (ty-var (v) (k-put (k-dvar-string v) st))
        (ty-link (x) (k-put "?" st))
        (ty-subr (e ps r cv spc) (k-show-subr e ps r cv spc p st))
        (ty-poly (bs body)
          (let ((binders (k-join (k-show-binders bs) " ")))
            (k-put ")" (k-show-on body p (k-put (k-cat3 "(poly (" binders ") ") st)))))
        (ty-ref (a r) (k-show-in-region "(ref " a r p st))
        (ty-product (ps) (k-put ")" (k-show-parts ps p (k-put "(productof" st))))
        (ty-sum (ps) (k-put ")" (k-show-parts ps p (k-put "(sumof" st))))
        (ty-array (a nz r)
          (tagcase nz
            (sz-finite () (k-show-in-region "(arrayof " a r p st))
            (else y (k-put (k-cat5 " " (k-show-size nz) " " (k-region-show r) ")")
                           (k-show-on a p (k-put "(narrayof " st))))))
        (ty-icell (a r) (k-show-in-region "(icell " a r p st))
        (ty-place (r) (k-put (k-cat3 "(place " (k-region-show r) ")") st))
        (ty-pair (a b r nl)
          (if (and nl (= (k-resolve b) t))
              (k-show-in-region "(listof " a r p st)
              (let* ((st (k-put (if nl "(union nil (pairof " "(pairof ") st))
                     (st (k-show-on b p (k-put " " (k-show-on a p st))))
                     (st (k-put (k-cat3 " " (k-region-show r) ")") st)))
                (if nl (k-put ")" st) st))))
        (ty-tag (a h e r) (k-show-control "(prompt-tag " a h e r p st))
        (ty-comp (a h e r once)
          (k-show-control (if once "(oneshot " "(composable ") a h e r p st))
        (ty-markkey (a r) (k-show-in-region "(mark-key " a r p st))
        (ty-bloblet (fs z r)
          (let* ((head (if z "(bloblet (frozen" "(bloblet (fields"))
                 (st (k-put (if (null? fs) head (string-append head " ")) st))
                 (st (k-show-seq fs p " " st)))
            (k-put (k-cat3 ") " (k-region-show r) ")") st)))
        (ty-nlist (e z r)
          (let ((st (k-show-on e p (k-put "(nlist " st))))
            (k-put (k-cat3 " " (k-show-size z) (k-nlist-end r)) st)))
        (ty-nat (z)
          (k-put (tagcase z (sz-finite () "nat") (else y (k-cat3 "(nat " (k-show-size z) ")"))) st))
        (ty-named (g ds)
          (let ((name (symbol->string (extract (k-gen-of g) 1))))
            (if (null? ds)
                (k-put name st)
                (k-put ")" (k-show-descs ds p (k-put (k-cat3 "(" name " ") st))))))
        ;; Each description's name, after it, names what it is.
        (ty-module (abs ds vs)
          (let* ((st (k-put (string-append "(moduleof" (k-show-abs abs)) st))
                 (st (k-show-comps "desc" ds p st)))
            (k-put ")" (k-show-comps "val" vs (k-printing-named p ds) st))))
        (ty-select (m n)
          (k-put (k-cat5 "(select " (symbol->string m) " " (symbol->string n) ")") st))
        (ty-param (k n)
          (k-put (k-cat5 "(select $" (int->string (+ k 1)) " " (symbol->string n) ")") st))
        (ty-app (g ds)
          (let ((st (k-put " " (k-show-on g p (k-put "(" st)))))
            (k-put ")" (k-show-descs ds p st))))
        (ty-lam (bs body)
          (let ((head (k-cat3 "(dlambda (" (k-join (k-show-binders bs) " ") ") ")))
            (k-put ")" (k-show-desc body p (k-put head st))))))))
  ;; A module type's components of kind `what`: ` (what name type)` each.
  ;; A description's name naming it in the components after it.
  (k-show-comps (->* (string k-parts k-printing k-shown) k-shown)
    (lambda (what ps p st)
      (if (null? ps)
          st
          (let* ((one (k-cat5 " (" what " " (symbol->string (extract (car ps) 1)) " "))
                 (after (if (string=? what "desc") (k-printing-named p (list (car ps))) p))
                 (own (if (string=? what "desc") (extract (car ps) 1) '||))
                 (st (k-put ")" (k-show-comp (extract (car ps) 2) p own (k-put one st)))))
            (k-show-comps what (cdr ps) after st)))))
  ;; A component's type; an effect, a description function of no parameters,
  ;; as the effect. A description shows what it is, not its own name `n` (a
  ;; value's, `||`, no name): a `define-type` alias of it, `(select m n)`, is
  ;; named `n` too.
  ;; A family too (`(dlambda …)`), as the Rust checker shows one.
  (k-show-comp (->* (int k-printing symbol k-shown) k-shown)
    (lambda (t p n st)
      (tagcase (k-get t)
        (ty-lam (bs body)
          (if (null? bs) (k-show-desc body p st) (k-show-comp-named t p n st)))
        (else y (k-show-comp-named t p n st)))))
  (k-show-comp-named (->* (int k-printing symbol k-shown) k-shown)
    (lambda (t p n st)
      (let* ((r (k-resolve t))
             (named (k-part-named (extract p 2) r))
             (name (if (null? named) (k-abbrev-by (extract p 3) r) named)))
        (if (or (null? name) (string=? (car name) (symbol->string n)))
            (k-show-body r p st)
            (k-put (car name) st))))))

;; Each of `ts` shown, as printing `path` shows it.
(define k-show-list (->* (k-ids k-printing) k-strings)
  (lambda (ts path)
    (if (null? ts)
        nil
        (cons (k-pieces-string (extract (k-show-on (car ts) path k-shown-none) 1))
              (k-show-list (cdr ts) path)))))
;; Whether type `t` is variable `v`.
(define k-type-is-var? (->* (int int) bool)
  (lambda (t v) (tagcase (k-get t) (ty-var (w) (= w v)) (else y #f))))
;; The tree of a scope's `define-type`s (`k-atree-of`), kept with the scope
;; it was made of and how many links had been made (`k-links`): made once
;; for the top level, whose types are declared ahead, while what they
;; resolve to stays, not again for each line shown (`k-keep-atree!`).
(define k-atree-kept (ref (listof k-atree-of-scope acyclic) @t) (new nil))
;; Whether `kept` is the tree of the scope now.
(define k-atree-current? (->* ((listof k-atree-of-scope acyclic)) bool)
  (lambda (kept)
    (and (not (null? kept))
         (eq? (extract (car kept) 1) (get k-dscope))
         (= (extract (car kept) 2) (get k-links)))))
;; For the driver of the top level, which may write: the tree of the scope
;; now, if the one kept is not of it.
(define k-keep-atree! (->* () unit)
  (lambda ()
    (if (k-atree-current? (get k-atree-kept))
        #u
        (let ((ds (get k-dscope)))
          (begin (set k-links-below (get k-ntys))
                 (set k-atree-kept
                      (list (product (1 ds) (2 (get k-links))
                                     (3 (k-atree-of ds 0 (a-leaf)))))))))))
;; The tree of the scope now: the one kept, if it is of it.
(define k-atree-now (->* () k-atree)
  (lambda ()
    (let ((kept (get k-atree-kept)))
      (if (k-atree-current? kept)
          (extract (car kept) 3)
          (k-atree-of (get k-dscope) 0 (a-leaf))))))
;;; ------------------------------------------------------------ syscalls

;; A syscall's type in canonical form (`docs/research/syscalls.md`), as
;; `syscall.rs`'s `canonical`, check for check: every name expanded,
;; effects deduplicated and sorted by their text, region binders `r1`, `r2`,
;; … in order; a tree of names, at `a`..`b`, which `k-syn-text` prints.
;; Refused at `ta`..`tb` where it is no syscall's type.
(define k-sys-shape string "a syscall's type is a `subr`, or a `poly` over regions only of one")
(define k-sys-crossing string
  (string-append "a syscall takes and gives only `int`, `i64`, `u64`, `bool`, `char`, `unit`, "
                 "`string`, `(flatarrayof i64 r)` and `(bytevectorof r)`"))
(define k-sys-effects string
  (string-append "a syscall's effect holds only reads, writes and allocations "
                 "of its regions, I/O, `spin` and `nondet`"))
(define k-sys-regions string "a syscall's regions are its `poly`'s")
(define k-sys-sym (->* (string int int) syn) (lambda (n a b) (atom (string->symbol n) a b)))
;; A list of `xs`; its datum, which nothing reads of a type, empty.
(define k-sys-list (->* ((listof syn acyclic) int int) syn) (lambda (xs a b) (lst xs nil a b)))
(define k-sys-2 (->* (syn syn int int) syn)
  (lambda (x y a b) (k-sys-list (list x y) a b)))
;; Printed: names apart by one space, no other whitespace.
(define k-syn-text (->* (syn) string)
  (lambda (s)
    (tagcase s
      (atom (d a b) (typecase d (symbol n (symbol->string n)) (else x "")))
      (lst (items d a b) (string-append "(" (k-syn-texts items) ")"))
      (else x ""))))
(define k-syn-texts (->* ((listof syn acyclic)) string)
  (lambda (xs)
    (cond ((null? xs) "")
          ((null? (cdr xs)) (k-syn-text (car xs)))
          (else (string-append (k-syn-text (car xs)) " " (k-syn-texts (cdr xs)))))))
;; Region variable `v`'s name, the `i`th of `bs` from `i`, or "" if none.
(define k-sys-region-name (->* (k-binders int int) string)
  (lambda (bs v i)
    (cond ((null? bs) "")
          ((= (extract (car bs) 1) v) (string-append "r" (int->string i)))
          (else (k-sys-region-name (cdr bs) v (+ i 1))))))
;; Region `r`, a binder of `bs`, or a failure with `m`.
(define k-sys-region (->* (k-binders k-region string int int int int) syn)
  (lambda (bs r m a b ta tb)
    (let ((n (tagcase r (r-var (v) (k-sys-region-name bs v 1)) (else x ""))))
      (if (string=? n "") (k-fail m ta tb) (k-sys-sym n a b)))))
(define k-sys-base? (->* (symbol) bool)
  (lambda (n)
    (let ((s (symbol->string n)))
      (or (string=? s "int") (string=? s "i64") (string=? s "u64") (string=? s "bool")
          (string=? s "char") (string=? s "unit") (string=? s "string")))))
(define k-sys-i64? (->* (int) bool)
  (lambda (t) (tagcase (k-get (k-resolve t)) (ty-base (n) (symbol=? n 'i64)) (else x #f))))
;; A type that crosses, canonical.
(define k-sys-crossing-of (->* (k-binders int int int int int) syn)
  (lambda (bs t a b ta tb)
    (let ((fail (lambda () (k-fail k-sys-crossing ta tb))))
      (tagcase (k-get (k-resolve t))
        (ty-base (n) (if (k-sys-base? n) (atom n a b) (fail)))
        (ty-named (g ds)
          (cond ((and (= g 2) (= (length ds) 2))
                 (tagcase (car ds)
                   (dt (e)
                     (tagcase (car (cdr ds))
                       (dr (r)
                         (if (k-sys-i64? e)
                             (k-sys-list (list (k-sys-sym "flatarrayof" a b) (k-sys-sym "i64" a b)
                                               (k-sys-region bs r k-sys-regions a b ta tb))
                                         a b)
                             (fail)))
                       (else x (fail))))
                   (else x (fail))))
                ((and (= g 8) (= (length ds) 1))
                 (tagcase (car ds)
                   (dr (r) (k-sys-2 (k-sys-sym "bytevectorof" a b)
                                    (k-sys-region bs r k-sys-regions a b ta tb) a b))
                   (else x (fail))))
                (else (fail))))
        (else x (fail))))))
(define k-sys-crossings (->* (k-binders k-ids int int int int) (listof syn acyclic))
  (lambda (bs ts a b ta tb)
    (if (null? ts)
        nil
        (let ((t (k-sys-crossing-of bs (car ts) a b ta tb)))
          (cons t (k-sys-crossings bs (cdr ts) a b ta tb))))))
;; An effect's atom, canonical.
(define k-sys-atom (->* (k-binders k-atom int int int int) syn)
  (lambda (bs x a b ta tb)
    (let ((on (lambda ((n string) (r k-region))
                (k-sys-2 (k-sys-sym n a b) (k-sys-region bs r k-sys-effects a b ta tb) a b))))
      (tagcase x
        (a-read (r) (on "read" r))
        (a-write (r) (on "write" r))
        (a-alloc (r) (on "alloc" r))
        (a-io (k) (k-sys-2 (k-sys-sym "io" a b) (k-sys-sym (k-io-kind-name k) a b) a b))
        (a-spin () (k-sys-sym "spin" a b))
        (a-nondet () (k-sys-sym "nondet" a b))
        (else y (k-fail k-sys-effects ta tb))))))
(define-type k-sys-texts (listof (productof (1 string) (2 syn)) acyclic))
;; `x` among `xs`, sorted by text, each text once.
(define k-sys-insert (->* ((productof (1 string) (2 syn)) k-sys-texts) k-sys-texts)
  (lambda (x xs)
    (cond ((null? xs) (the k-sys-texts (list x)))
          ((string=? (extract x 1) (extract (car xs) 1)) xs)
          ((string<? (extract x 1) (extract (car xs) 1)) (the k-sys-texts (cons x xs)))
          (else (the k-sys-texts (cons (car xs) (k-sys-insert x (cdr xs))))))))
(define k-sys-sorted (->* (k-binders k-eff int int int int k-sys-texts) k-sys-texts)
  (lambda (bs e a b ta tb acc)
    (if (null? e)
        acc
        (let ((x (k-sys-atom bs (car e) a b ta tb)))
          (k-sys-sorted bs (cdr e) a b ta tb
                        (k-sys-insert (product (1 (k-syn-text x)) (2 x)) acc))))))
(define k-sys-syns (->* (k-sys-texts) (listof syn acyclic))
  (lambda (xs) (if (null? xs) nil (cons (extract (car xs) 2) (k-sys-syns (cdr xs))))))
;; None `pure`, one alone, else in a `maxeff`.
(define k-sys-effect (->* (k-binders k-eff int int int int) syn)
  (lambda (bs e a b ta tb)
    (let ((xs (k-sys-syns (k-sys-sorted bs e a b ta tb nil))))
      (cond ((null? xs) (k-sys-sym "pure" a b))
            ((null? (cdr xs)) (car xs))
            (else (k-sys-list (cons (k-sys-sym "maxeff" a b) xs) a b))))))
;; Its `subr`, its binders `bs`.
(define k-sys-subr (->* (k-binders int int int int int) syn)
  (lambda (bs t a b ta tb)
    (tagcase (k-get (k-resolve t))
      (ty-subr (e ps r cv spc)
        (begin
          ;; Called as the program calls any procedure: no `conv` but its own.
          (if (k-conv=? cv (get k-conv-default)) #u (k-fail k-sys-shape ta tb))
          (if (null? spc) #u (k-fail k-sys-shape ta tb))
          (if (> (length ps) 6) (k-fail "a syscall takes at most 6 arguments" ta tb) #u)
          (let* ((ef (k-sys-effect bs e a b ta tb))
                 (params (k-sys-crossings bs ps a b ta tb))
                 (result (k-sys-crossing-of bs r a b ta tb)))
            (k-sys-list (list (k-sys-sym "subr" a b) ef (k-sys-list params a b) result) a b))))
      (else x (k-fail k-sys-shape ta tb)))))
;; The `poly`'s binders, each `(ri region)`; a binder not a region refused.
(define k-sys-binders (->* (k-binders int int int int int) (listof syn acyclic))
  (lambda (bs i a b ta tb)
    (cond ((null? bs) nil)
          ((= (extract (car bs) 2) 0)
           (cons (k-sys-2 (k-sys-sym (string-append "r" (int->string i)) a b)
                          (k-sys-sym "region" a b) a b)
                 (k-sys-binders (cdr bs) (+ i 1) a b ta tb)))
          (else (k-fail k-sys-shape ta tb)))))
(define k-syscall-canonical (->* (int int int int int) syn)
  (lambda (t a b ta tb)
    (tagcase (k-get (k-resolve t))
      (ty-poly (bs body)
        (let ((written (k-sys-binders bs 1 a b ta tb)))
          (k-sys-list (list (k-sys-sym "poly" a b) (k-sys-list written a b)
                            (k-sys-subr bs body a b ta tb))
                      a b)))
      (else x (k-sys-subr nil t a b ta tb)))))
;; A type. One `define-type` named prints as its name; any other recursive
;; type as `(mu %d …)`, `%d` naming the cycle.
(define k-show-ty (->* (int) string)
  (lambda (t)
    (let* ((trs (the k-atrees (list (k-atree-now))))
           (p (product (1 (the k-ids nil)) (2 (the k-parts nil)) (3 trs))))
      (k-pieces-string (extract (k-show-on t p k-shown-none) 1))))))))
