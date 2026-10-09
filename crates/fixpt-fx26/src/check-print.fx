;;; The checker, in FX-26: types and effects shown as the Rust checker shows
;;; them; and what a type holds: where a procedure kept in it could reach
;;; itself, and at which polarities a variable occurs in it.
;;; Part of the checker, `check-types.fx` first (PLAN.md §11, step 10).

;;; ------------------------------------------------------------ printing

;; A module (`TODO.md` §34: the front end into modules, a file at a time);
;; what other files use re-exported after it.
;; Its types (`check-print-types.fx`), loaded before the module so that they are not
;; among its values; the module names what it uses of them.
(define check-print-types (load-module "fx26:check-print-types.fx"))
(define check-print-module (module
(define-type k-atree (select check-print-types k-atree))
(define a-leaf (with check-print-types a-leaf))
(define a-node (with check-print-types a-node))
(define-type k-atrees (select check-print-types k-atrees))
(define-type k-named-at (select check-print-types k-named-at))
(define-type k-size-fact (select check-print-types k-size-fact))
(define-type k-lins (select check-print-types k-lins))
(define-type k-printing (select check-print-types k-printing))
(define-effect kshows (select check-print-types kshows))


;; What a type is shown as so far (`check-print-types.fx`).
(define-type k-shown (select check-print-types k-shown))
(define k-shown-none k-shown (product (1 (the k-strings nil)) (2 (the k-ids nil)) (3 0)))
;; `st`, then `s`.
(define k-put (subr (read @globals) (string k-shown) k-shown)
  (lambda (s st)
    (product (1 (the k-strings (cons s (extract st 1)))) (2 (extract st 2))
             (3 (+ (extract st 3) 1)))))
;; `st`, its depths `ds`.
(define k-shown-depths (subr pure (k-shown k-ids) k-shown)
  (lambda (st ds) (product (1 (extract st 1)) (2 ds) (3 (extract st 3)))))
;; `ds` without `d`.
(define k-ids-without (subr (read @globals) (k-ids int) k-ids)
  (lambda (ds d)
    (cond ((null? ds) ds)
          ((= (car ds) d) (k-ids-without (cdr ds) d))
          (else (the k-ids (cons (car ds) (k-ids-without (cdr ds) d)))))))
;; The first `k` pieces of `xs`, then `mid`, then the rest: `(mu %d ` put
;; before a node's pieces once it is known to be met again below.
(define k-pieces-before (subr (maxeff (read @globals) spin) (k-strings int string) k-strings)
  (lambda (xs k mid)
    (if (or (<= k 0) (null? xs))
        (the k-strings (cons mid xs))
        (the k-strings (cons (car xs) (k-pieces-before (cdr xs) (- k 1) mid))))))
;; The pieces, the last first, joined: their characters gathered, last to
;; first, into one list in an arena of its own, made a string once.
(define k-pieces-string (subr (maxeff (read @globals) (read @t)) (k-strings) string)
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
  (k-show-on (subr kbuilds (int k-printing k-shown) k-shown)
    (lambda (t path st)
      (let* ((t (k-resolve t))
             (named (k-part-named (extract path 2) t))
             (name (if (null? named) (k-abbrev-by (extract path 3) t) named)))
        (if (null? name) (k-show-body t path st) (k-put (car name) st)))))
  ;; Each of `ts`, `sep` between each two.
  (k-show-seq (subr kbuilds (k-ids k-printing string k-shown) k-shown)
    (lambda (ts path sep st)
      (cond ((null? ts) st)
            ((null? (cdr ts)) (k-show-on (car ts) path st))
            (else (k-show-seq (cdr ts) path sep (k-put sep (k-show-on (car ts) path st)))))))
  ;; Each part's ` (label type)`.
  (k-show-parts (subr kbuilds (k-parts k-printing k-shown) k-shown)
    (lambda (ps path st)
      (if (null? ps)
          st
          (let* ((st (k-put (k-cat3 " (" (symbol->string (extract (car ps) 1)) " ") st))
                 (st (k-put ")" (k-show-on (extract (car ps) 2) path st))))
            (k-show-parts (cdr ps) path st)))))
  (k-show-desc (subr kbuilds (k-desc k-printing k-shown) k-shown)
    (lambda (d p st)
      (tagcase d
        (dt (t) (k-show-on t p st))
        (dr (r) (k-put (k-region-show r) st))
        (de (e) (k-put (k-show-effect e) st))
        (dz (z) (k-put (k-show-size z) st))
        (dc (c) (k-put (k-conv-show c) st))
        (df (f) (k-show-on f p st)))))
  ;; Each of `ds`, a space between each two.
  (k-show-descs (subr kbuilds (k-descs k-printing k-shown) k-shown)
    (lambda (ds p st)
      (cond ((null? ds) st)
            ((null? (cdr ds)) (k-show-desc (car ds) p st))
            (else (k-show-descs (cdr ds) p (k-put " " (k-show-desc (car ds) p st)))))))
  ;; A `subr` type.
  (k-show-subr (subr kbuilds (k-eff k-ids int k-conv k-printing k-shown) k-shown)
    (lambda (e ps r cv p st)
      (let* ((st (k-put (k-cat5 "(subr " (k-conv-prefix cv) (k-show-effect e) " (" "") st))
             (st (k-put ") " (k-show-seq ps p " " st))))
        (k-put ")" (k-show-on r p st)))))
  ;; `(head a h e r)`: a prompt tag's type, or a composable continuation's.
  (k-show-control (subr kbuilds (string int int k-eff k-region k-printing k-shown) k-shown)
    (lambda (head a h e r p st)
      (let* ((st (k-put " " (k-show-on a p (k-put head st))))
             (st (k-show-on h p st)))
        (k-put (k-cat5 " " (k-show-effect e) " " (k-region-show r) ")") st))))
  ;; `(head a r)`.
  (k-show-in-region (subr kbuilds (string int k-region k-printing k-shown) k-shown)
    (lambda (head a r p st)
      (k-put (k-cat3 " " (k-region-show r) ")") (k-show-on a p (k-put head st)))))
  ;; A node met again on the way down is a cycle: named by its depth, and
  ;; written `(mu %d …)` where the cycle starts, once its pieces are known
  ;; to name it.
  (k-show-body (subr kbuilds (int k-printing k-shown) k-shown)
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
  (k-show-node (subr kbuilds (int k-printing k-shown) k-shown)
    (lambda (t p st)
      (tagcase (k-get t)
        (ty-base (s) (k-put (symbol->string s) st))
        (ty-void () (k-put "void" st))
        (ty-nil () (k-put "nil" st))
        (ty-false () (k-put "false" st))
        (ty-union (ms) (k-put ")" (k-show-seq ms p " " (k-put "(union " st))))
        (ty-proving (t e)
          (k-put (k-cat5 "(bool " (k-show-props "then" t) " " (k-show-props "else" e) ")") st))
        (ty-var (v) (k-put (k-dvar-string v) st))
        (ty-link (x) (k-put "?" st))
        (ty-subr (e ps r cv) (k-show-subr e ps r cv p st))
        (ty-poly (bs body)
          (let ((binders (k-join (k-show-binders bs) " ")))
            (k-put ")" (k-show-on body p (k-put (k-cat3 "(poly (" binders ") ") st)))))
        (ty-ref (a r) (k-show-in-region "(ref " a r p st))
        (ty-product (ps) (k-put ")" (k-show-parts ps p (k-put "(productof" st))))
        (ty-sum (ps) (k-put ")" (k-show-parts ps p (k-put "(sumof" st))))
        (ty-array (a r) (k-show-in-region "(arrayof " a r p st))
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
        (ty-comp (a h e r) (k-show-control "(composable " a h e r p st))
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
  (k-show-comps (subr kbuilds (string k-parts k-printing k-shown) k-shown)
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
  (k-show-comp (subr kbuilds (int k-printing symbol k-shown) k-shown)
    (lambda (t p n st)
      (tagcase (k-get t)
        (ty-lam (bs body)
          (if (null? bs) (k-show-desc body p st) (k-show-comp-named t p n st)))
        (else y (k-show-comp-named t p n st)))))
  (k-show-comp-named (subr kbuilds (int k-printing symbol k-shown) k-shown)
    (lambda (t p n st)
      (let* ((r (k-resolve t))
             (named (k-part-named (extract p 2) r))
             (name (if (null? named) (k-abbrev-by (extract p 3) r) named)))
        (if (or (null? name) (string=? (car name) (symbol->string n)))
            (k-show-body r p st)
            (k-put (car name) st))))))

;; Each of `ts` shown, as printing `path` shows it.
(define k-show-list (subr kbuilds (k-ids k-printing) k-strings)
  (lambda (ts path)
    (if (null? ts)
        nil
        (cons (k-pieces-string (extract (k-show-on (car ts) path k-shown-none) 1))
              (k-show-list (cdr ts) path)))))
;; Whether type `t` is variable `v`.
(define k-type-is-var? (subr (maxeff kreads spin) (int int) bool)
  (lambda (t v) (tagcase (k-get t) (ty-var (w) (= w v)) (else y #f))))
;; The tree of a scope's `define-type`s (`k-atree-of`), kept with the scope
;; it was made of and how many links had been made (`k-links`): made once
;; for the top level, whose types are declared ahead, while what they
;; resolve to stays, not again for each line shown (`k-keep-atree!`).
(define-type k-atree-of-scope (select check-print-types k-atree-of-scope))
(define k-atree-kept (ref (listof k-atree-of-scope acyclic) @t) (new nil))
;; Whether `kept` is the tree of the scope now.
(define k-atree-current? (subr kreads ((listof k-atree-of-scope acyclic)) bool)
  (lambda (kept)
    (and (not (null? kept))
         (eq? (extract (car kept) 1) (get k-dscope))
         (= (extract (car kept) 2) (get k-links)))))
;; For the driver of the top level, which may write: the tree of the scope
;; now, if the one kept is not of it.
(define k-keep-atree! (subr (maxeff kreads (write @t) (alloc @t) spin) () unit)
  (lambda ()
    (if (k-atree-current? (get k-atree-kept))
        #u
        (let ((ds (get k-dscope)))
          (begin (set k-links-below (get k-ntys))
                 (set k-atree-kept
                      (list (product (1 ds) (2 (get k-links))
                                     (3 (k-atree-of ds 0 (a-leaf)))))))))))
;; The tree of the scope now: the one kept, if it is of it.
(define k-atree-now (subr kbuilds () k-atree)
  (lambda ()
    (let ((kept (get k-atree-kept)))
      (if (k-atree-current? kept)
          (extract (car kept) 3)
          (k-atree-of (get k-dscope) 0 (a-leaf))))))
;; A type. One `define-type` named prints as its name; any other recursive
;; type as `(mu %d …)`, `%d` naming the cycle.
(define k-show-ty (subr kbuilds (int) string)
  (lambda (t)
    (let* ((trs (the k-atrees (list (k-atree-now))))
           (p (product (1 (the k-ids nil)) (2 (the k-parts nil)) (3 trs))))
      (k-pieces-string (extract (k-show-on t p k-shown-none) 1)))))))

(define-type k-size-fact (select check-print-module k-size-fact))
(define k-show-list (with check-print-module k-show-list))
(define k-type-is-var? (with check-print-module k-type-is-var?))
(define k-show-ty (with check-print-module k-show-ty))
(define k-keep-atree! (with check-print-module k-keep-atree!))
