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
;; While a type with a cycle is shown: each node it reaches shown as its
;; class's first, the classes those of the type's minimal graph (Moore's
;; refinement), so that a type shows as itself however it was written or
;; made (the user's: a type is a semantic object), as the Rust checker's
;; `minimal_classes` has it. And while those are found, each node's own
;; part shown alone, its types `·`. Each node's place in the walk of the
;; type shown (`k-cpos`), valid where `k-cwalk` is this walk's number.
(define k-canon-on (ref bool @t) (new #f))
(define k-shallow (ref bool @t) (new #f))
(define k-cpos (ref (arrayof int @t) @t) (new (make-array 512 0)))
(define k-cwalk (ref (arrayof int @t) @t) (new (make-array 512 0)))
(define k-cepoch (ref int @t) (new 0))
;; Each place's class's first node.
(define k-cfirst (ref (arrayof int @t) @t) (new (make-array 1 0)))
;; Node `t`'s place in this walk, or -1.
(define k-cpos-of (->* (int) int)
  (lambda (t)
    (if (and (< t (array-length (get k-cwalk))) (= (array-ref (get k-cwalk) t) (get k-cepoch)))
        (array-ref (get k-cpos) t)
        -1)))
;; Node `t` as its class's first, while a type is shown so.
(define k-canon-of (->* (int) int)
  (lambda (t)
    (if (get k-canon-on)
        (let ((i (k-cpos-of t))) (if (< i 0) t (array-ref (get k-cfirst) i)))
        t)))
;; While a type is printed: the descriptions of the modules bound in scope,
;; each by its `select`, by shape (`k-shape-hash`), for a type of their
;; structure to be named so, not written out wherever each later module
;; has it (`TODO.md` §138), as the Rust checker's `module_selects`: the
;; modules in the order they were bound, each's descriptions in order; the
;; innermost binding of each name, not a standard one nor a hidden one
;; (`%…`), nor the global whose line is printed (`k-print-self`); a
;; description function, applied where it is used, not.
(define-type k-sel-list (listof (pairof string int @t) @t))
(define k-selects-on (ref bool @t) (new #f))
(define k-sel-buckets int 1021)
(define k-selects-table (ref (arrayof k-sel-list @t) @t) (new (make-array 1 (the k-sel-list nil))))
(define k-print-self (ref symbol @t) (new '||))
(define k-print-self! (->* (symbol) unit) (lambda (n) (set k-print-self n)))
(define k-selects-gather! (->* () unit)
  (lambda ()
    (let ((tbl (the (arrayof k-sel-list @t) (make-array k-sel-buckets (the k-sel-list nil)))))
      (begin (k-selects-of (k-innermost (get k-trail) (- (get k-depth) 1) nil) tbl)
             (set k-selects-table tbl)
             (set k-selects-on #t)))))
;; Of the trail's names `ns`, newest first, the first at depth `d`: those
;; that are their names' innermost bindings (`k-bound-since?`), oldest first.
(define k-innermost (->* (k-names int k-names) k-names)
  (lambda (ns d acc)
    (cond ((null? ns) acc)
          ((k-bound-since? (car ns) (+ d 1)) (k-innermost (cdr ns) (- d 1) acc))
          (else (k-innermost (cdr ns) (- d 1) (cons (car ns) acc))))))
;; The descriptions of the modules `ns` (oldest first) name, into `tbl`: the
;; newest first, so that in each list the oldest's are first.
(define k-selects-of (->* (k-names (arrayof k-sel-list @t)) unit)
  (lambda (ns tbl)
    (if (null? ns)
        #u
        (let* ((n (car ns)) (t (k-lookup-raw n)) (shown (symbol->string n)))
          (begin
            (k-selects-of (cdr ns) tbl)
            (if (or (< t 0) (symbol=? n (get k-print-self)) (k-std-binding? n t)
                    (and (> (string-length shown) 0) (string=? (substring shown 0 1) "%")))
                #u
                (tagcase (k-get (k-resolve t))
                  (ty-module (abs ds vs) (k-selects-descs shown ds tbl))
                  (else y #u))))))))
;; Module `g`'s descriptions `ds`, each by its `select`, the first in front.
(define k-selects-descs (->* (string k-parts (arrayof k-sel-list @t)) unit)
  (lambda (g ds tbl)
    (if (null? ds)
        #u
        (let ((x (k-resolve (extract (car ds) 2))))
          (begin
            (k-selects-descs g (cdr ds) tbl)
            (if (and (k-abbreviates? x) (tagcase (k-get x) (ty-lam (bs b) #f) (else y #t)))
                (let ((h (modulo (k-shape-hash x 2) k-sel-buckets))
                      (s (k-cat5 "(select " g " " (symbol->string (extract (car ds) 1)) ")")))
                  (array-set! tbl h (cons (cons s x) (array-ref tbl h))))
                #u))))))
(define k-selects-clear! (->* () unit) (lambda () (set k-selects-on #f)))
;; The `select` that names `t`, of the modules gathered (`k-selects-gather!`).
(define k-select-by (->* (int) k-strings)
  (lambda (t)
    (if (not (get k-selects-on))
        nil
        (letrec ((find (->* (k-sel-list) k-strings)
                   (lambda (cs)
                     (cond ((null? cs) nil)
                           ((k-fits? (cdr (car cs)) t) (the k-strings (list (car (car cs)))))
                           (else (find (cdr cs)))))))
          (if (k-abbreviates? t)
              (find (array-ref (get k-selects-table) (modulo (k-shape-hash t 2) k-sel-buckets)))
              nil)))))
;; Whether name `s` is a module's `select` (`k-select-by`).
(define k-select-name? (->* (string) bool)
  (lambda (s) (and (> (string-length s) 8) (string=? (substring s 0 8) "(select "))))
;; The name `define-type` gave `t`; else a module's description's `select`.
(define k-abbrev-or-select (->* (k-atrees int) k-strings)
  (lambda (trs t) (let ((a (k-abbrev-by trs t))) (if (null? a) (k-select-by t) a))))
;; A product's or sum's label as a type shows it: a keyword, `#:name`
;; (`docs/fx26.md`, "Keywords"); a number, which no keyword is, bare (as
;; `unparse.rs`'s `show_label`).
(define k-digits-only? (->* (string int) bool)
  (lambda (s i)
    (or (= i (string-length s))
        (and (char-numeric? (string-ref s i)) (k-digits-only? s (+ i 1))))))
(define k-label-shown (->* (symbol) string)
  (lambda (l)
    (let ((n (symbol->string l)))
      (if (and (> (string-length n) 0) (k-digits-only? n 0)) n (string-append "#:" n)))))
(define-rec
  (k-show-on (->* (int k-printing k-shown) k-shown)
    (lambda (t path st)
      (if (get k-shallow)
          (k-put "·" st)
          (let* ((t (k-canon-of (k-resolve t)))
                 (named (k-part-named (extract path 2) t))
                 (name (if (null? named) (k-abbrev-or-select (extract path 3) t) named)))
            (if (null? name) (k-show-body t path st) (k-put (car name) st))))))
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
          (let* ((st (k-put (k-cat3 " (" (k-label-shown (extract (car ps) 1)) " ") st))
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
        ;; A list when its tail is itself; not in a label (`k-shallow`),
        ;; which is the node's own part, not where its tail goes, so that a
        ;; list and a pair whose tail is that list (`nil` beside a pair, in
        ;; a join) are one class, and show alike.
        (ty-pair (a b r nl)
          (if (and nl (not (get k-shallow)) (= (k-canon-of (k-resolve b)) t))
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
  ;; A description function as its `(dlambda …)`, as the Rust checker
  ;; shows one: a name of one does not stand bare.
  (k-show-comp (->* (int k-printing symbol k-shown) k-shown)
    (lambda (t p n st)
      (tagcase (k-get t)
        (ty-lam (bs body)
          (if (null? bs) (k-show-desc body p st) (k-show-body (k-canon-of (k-resolve t)) p st)))
        (else y (k-show-comp-named t p n st)))))
  ;; Its class's first node (`k-canon-of`), as `k-show-on` shows: a list's
  ;; is the one whose tail is itself.
  (k-show-comp-named (->* (int k-printing symbol k-shown) k-shown)
    (lambda (t p n st)
      (let* ((r (k-canon-of (k-resolve t)))
             (named (k-part-named (extract p 2) r))
             (name (if (null? named) (k-abbrev-or-select (extract p 3) r) named)))
        ;; Nor a description by a module's `select` (`k-select-by`), which,
        ;; of the module printed, would name it by itself.
        (if (or (null? name) (string=? (car name) (symbol->string n))
                (and (not (symbol=? n '||)) (k-select-name? (car name))))
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
;;; ------------------------------------------------------------ canonical cycles
(define k-canon-onto (->* (k-ids k-ids) k-ids)
  (lambda (xs ys) (if (null? xs) ys (cons (car xs) (k-canon-onto (cdr xs) ys)))))
(define k-canon-resolved (->* (k-ids) k-ids)
  (lambda (xs) (if (null? xs) nil (cons (k-resolve (car xs)) (k-canon-resolved (cdr xs))))))

;; The types `t` is made of, one level down, each followed through its
;; links: as `k-ty-kids` has them (`check-read-helpers.fx`).
(define k-canon-kids (->* (int) k-ids)
  (lambda (t)
    (letrec ((ds (->* (k-descs) k-ids)
                (lambda (xs)
                  (if (null? xs)
                      nil
                      (tagcase (car xs)
                        (dt (x) (cons x (ds (cdr xs)))) (df (x) (cons x (ds (cdr xs))))
                        (else y (ds (cdr xs)))))))
             (parts (->* (k-parts) k-ids)
               (lambda (ps) (if (null? ps) nil (cons (extract (car ps) 2) (parts (cdr ps)))))))
      (k-canon-resolved
       (tagcase (k-get t)
         (ty-subr (e ps r cv spc) (k-canon-onto ps (list r)))
         (ty-poly (bs x) (list x)) (ty-ref (a r) (list a)) (ty-array (a nz r) (list a))
         (ty-icell (a r) (list a)) (ty-markkey (a r) (list a)) (ty-pair (a d r nl) (list a d))
         (ty-tag (a h e r) (list a h)) (ty-comp (x a e r once) (list x a))
         (ty-product (ps) (parts ps)) (ty-sum (ps) (parts ps)) (ty-bloblet (fs z r) fs)
         (ty-union (ms) ms) (ty-named (g xs) (ds xs)) (ty-app (f xs) (cons f (ds xs)))
         (ty-lam (bs x) (ds (list x))) (ty-nlist (e z r) (list e))
         (ty-module (abs xs vs) (k-canon-onto (parts xs) (parts vs)))
         (else y nil))))))
;; A new array of `n` from `xs`, the rest `fill`.
(define k-cgrown (->* ((arrayof int @t) int int) (arrayof int @t))
  (lambda (xs n fill)
    (let ((ys (the (arrayof int @t) (make-array n fill))))
      (letrec ((copy (->* (int) (arrayof int @t))
                 (lambda (i)
                   (if (>= i (array-length xs))
                       ys
                       (begin (array-set! ys i (array-ref xs i)) (copy (+ i 1)))))))
        (copy 0)))))
;; Node `t` put at place `i` of this walk.
(define k-cpos-set! (->* (int int) unit)
  (lambda (t i)
    (begin
      (if (< t (array-length (get k-cwalk)))
          #u
          (let ((n (+ t (array-length (get k-cwalk)))))
            (begin (set k-cwalk (k-cgrown (get k-cwalk) n -1))
                   (set k-cpos (k-cgrown (get k-cpos) n 0)))))
      (array-set! (get k-cwalk) t (get k-cepoch))
      (array-set! (get k-cpos) t i))))
;; The nodes `todo` and what they reach, each once, the last met first, onto
;; `acc`, each put at its place in this walk from `n` (`k-cpos-set!`).
(define k-canon-walk (->* (k-ids k-ids int) k-ids)
  (lambda (todo acc n)
    (cond ((null? todo) acc)
          ((>= (k-cpos-of (car todo)) 0) (k-canon-walk (cdr todo) acc n))
          (else
           (begin (k-cpos-set! (car todo) n)
                  (k-canon-walk (k-canon-onto (k-canon-kids (car todo)) (cdr todo))
                                (cons (car todo) acc) (+ n 1)))))))
;; Whether a walk down from place `i` comes back to a place on its way
;; (`color`: 1 on the way, 2 done).
(define-rec
  (k-canon-cyclic? (->* (int (arrayof int @t) (arrayof k-ids @t)) bool)
    (lambda (i color kids)
      (let ((c (array-ref color i)))
        (cond ((= c 1) #t)
              ((= c 2) #f)
              (else (begin (array-set! color i 1)
                           (let ((r (k-canon-any? (array-ref kids i) color kids)))
                             (begin (array-set! color i 2) r))))))))
  (k-canon-any? (->* (k-ids (arrayof int @t) (arrayof k-ids @t)) bool)
    (lambda (ts color kids)
      (and (not (null? ts))
           (or (k-canon-cyclic? (k-cpos-of (car ts)) color kids)
               (k-canon-any? (cdr ts) color kids))))))
(define-type k-cbucket (listof (pairof string int @t) @t))
;; Class `k`'s number for key `s` in `buckets`, if it is there; -1.
(define k-cbucket-find (->* (k-cbucket string) int)
  (lambda (b s)
    (cond ((null? b) -1)
          ((string=? (car (car b)) s) (cdr (car b)))
          (else (k-cbucket-find (cdr b) s)))))
;; Each of the `n` places numbered by the first whose key, `keys[i]`, is
;; its own: each's class in `cls`, and how many.
(define k-canon-number (->* ((arrayof string @t) (arrayof int @t)) int)
  (lambda (keys cls)
    (let* ((n (array-length keys)) (m (+ (* 2 n) 1))
           (buckets (the (arrayof k-cbucket @t) (make-array m nil))))
      (letrec ((each (->* (int int) int)
                 (lambda (i k)
                   (if (>= i n)
                       k
                       (let* ((s (array-ref keys i)) (h (modulo (string-hash s) m))
                              (c (k-cbucket-find (array-ref buckets h) s)))
                         (if (>= c 0)
                             (begin (array-set! cls i c) (each (+ i 1) k))
                             (begin (array-set! buckets h
                                                (cons (cons s k) (array-ref buckets h)))
                                    (array-set! cls i k)
                                    (each (+ i 1) (+ k 1)))))))))
        (each 0 0)))))
;; Classes `xs` of places, in order, as a key: their numbers, `,` between.
(define k-canon-key (->* ((arrayof int @t) k-ids) string)
  (lambda (cls xs)
    (if (null? xs)
        ""
        (string-append (int->string (array-ref cls (k-cpos-of (car xs)))) ","
                       (k-canon-key cls (cdr xs))))))
;; Classes `cls` (`k` of them) refined until their count is the same twice.
(define k-canon-refine
  (->* ((arrayof int @t) (arrayof k-ids @t) (arrayof int @t) int) (arrayof int @t))
  (lambda (nodes kids cls k)
    (let* ((n (array-length nodes))
           (keys (the (arrayof string @t) (make-array n "")))
           (next (the (arrayof int @t) (make-array n 0))))
      (letrec ((fill (->* (int) unit)
                 (lambda (i)
                   (if (>= i n)
                       #u
                       (let ((own (int->string (array-ref cls i))))
                         (begin (array-set! keys i
                                            (string-append own ":"
                                                           (k-canon-key cls (array-ref kids i))))
                                (fill (+ i 1))))))))
        (begin (fill 0)
               (let ((k2 (k-canon-number keys next)))
                 (if (= k2 k) next (k-canon-refine nodes kids next k2))))))))
;; Whether `t` reaches a cycle: if so, each place's class's first in
;; `k-cfirst`, and `k-canon-on` set. `p` the path a type is shown from.
(define k-canon-set! (->* (int k-printing) bool)
  (lambda (t p)
    (let* ((t (k-resolve t))
           (epoch (set k-cepoch (+ (get k-cepoch) 1)))
           (order (k-ids-reversed (k-canon-walk (list t) nil 0) nil))
           (n (k-length order))
           (nodes (the (arrayof int @t) (make-array n 0)))
           (kids (the (arrayof k-ids @t) (make-array n nil)))
           (placed (k-canon-place order 0 nodes kids))
           (color (the (arrayof int @t) (make-array n 0))))
      (and (k-canon-cyclic? 0 color kids)
           (let* ((labels (the (arrayof string @t) (make-array n "")))
                  (shallow (set k-shallow #t))
                  (labeled (k-canon-label nodes labels p 0))
                  (unshallow (set k-shallow #f))
                  (cls (the (arrayof int @t) (make-array n 0)))
                  (k (k-canon-number labels cls))
                  (cls (k-canon-refine nodes kids cls k))
                  (first (the (arrayof int @t) (make-array n -1)))
                  (canon (the (arrayof int @t) (make-array n 0))))
             (begin (k-canon-firsts nodes cls first 0)
                    (k-canon-fill nodes cls first canon 0)
                    (set k-cfirst canon)
                    (set k-canon-on #t)
                    #t))))))
;; Places `i`… of `order`: each's node, and its kids.
(define k-canon-place (->* (k-ids int (arrayof int @t) (arrayof k-ids @t)) unit)
  (lambda (order i nodes kids)
    (if (null? order)
        #u
        (begin (array-set! nodes i (car order))
               (array-set! kids i (k-canon-kids (car order)))
               (k-canon-place (cdr order) (+ i 1) nodes kids)))))
;; Each place's node's own part, shown alone (`k-shallow`).
(define k-canon-label (->* ((arrayof int @t) (arrayof string @t) k-printing int) unit)
  (lambda (nodes labels p i)
    (if (>= i (array-length nodes))
        #u
        (let ((shown (k-show-body (array-ref nodes i) p k-shown-none)))
          (begin (array-set! labels i (k-pieces-string (extract shown 1)))
                 (k-canon-label nodes labels p (+ i 1)))))))
;; Each class's first place, by the class, in `first`.
(define k-canon-firsts (->* ((arrayof int @t) (arrayof int @t) (arrayof int @t) int) unit)
  (lambda (nodes cls first i)
    (if (>= i (array-length nodes))
        #u
        (let ((c (array-ref cls i)))
          (begin (if (< (array-ref first c) 0) (array-set! first c i) #u)
                 (k-canon-firsts nodes cls first (+ i 1)))))))
;; Each place's class's first node, by the place, in `canon`.
(define k-canon-fill
  (->* ((arrayof int @t) (arrayof int @t) (arrayof int @t) (arrayof int @t) int) unit)
  (lambda (nodes cls first canon i)
    (if (>= i (array-length nodes))
        #u
        (begin (array-set! canon i (array-ref nodes (array-ref first (array-ref cls i))))
               (k-canon-fill nodes cls first canon (+ i 1))))))
(define k-ids-reversed (->* (k-ids k-ids) k-ids)
  (lambda (xs acc) (if (null? xs) acc (k-ids-reversed (cdr xs) (cons (car xs) acc)))))
;; A type. One `define-type` named prints as its name; any other recursive
;; type as `(mu %d …)`, `%d` naming the cycle: its minimal one
;; (`k-canon-set!`).
(define k-show-ty (->* (int) string)
  (lambda (t) (k-show-ty-named t #t)))
;; The same with no `define-type` named, for a checker of another program:
;; what `stage` gives the one that runs with its text.
(define k-show-ty-whole (->* (int) string)
  (lambda (t) (k-show-ty-named t #f)))
(define k-show-ty-named (->* (int bool) string)
  (lambda (t named)
    (let* ((trs (if named (the k-atrees (list (k-atree-now))) (the k-atrees nil)))
           (p (product (1 (the k-ids nil)) (2 (the k-parts nil)) (3 trs)))
           (sel (and (not (get k-selects-on)) (begin (k-selects-gather!) #t)))
           (on (and (not (get k-canon-on)) (not (get k-shallow)) (k-canon-set! t p)))
           (shown (k-pieces-string (extract (k-show-on t p k-shown-none) 1))))
      (begin (if on (set k-canon-on #f) #u) (if sel (k-selects-clear!) #u) shown)))))))
