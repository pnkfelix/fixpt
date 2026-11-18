;;; A procedural macro's contract checked at a use (`typed-macros.md`,
;;; "Decided: procedural macros checked by their contracts";
;;; `Macros::contract_renames`, `contract_expanded`): the use's binders and
;;; the parts in their scopes, found as a pattern's are; the use renamed;
;;; and its two expansions held to each other, placement and commutation.
;;; `macros-procedural.fx`, above it, runs the transformer. On top of
;;; `macros-solve.fx`, which it loads and gives on (`solve-module`).

(module-parameters ((rs region) (re region) (rm region) (rc region) (rp region)))
(define solve-module ((proj (load-module "fx26:macros-solve.fx") rs re rm rc rp)))
(define infer-module (with solve-module infer-module))
(define files-module (with infer-module files-module))
(define align-module (with files-module align-module))
(define exports-module (with files-module exports-module))
(define match-module (with exports-module match-module))
(define scopes-module (with exports-module scopes-module))
(define types-module (with align-module types-module))
(define parser-module (with types-module parser-module))
(define reader-types (with parser-module reader-types))
;; The names the expander makes fresh, and its expansions' tags: the one
;; instance, which `macros-procedural.fx` and `macros.fx` take from here.
(define fresh-module ((proj (load-module "fx26:macros-fresh.fx") rs re rm rc rp)))
(import fresh-module tag-of)
(import reader-types atom lst dotted vec (type syn))
(import parser-module syn-start syn-end syn-symbol? syn-name syn-symbol syn-datums syn->datum
        syn-expansion len nth (type syns-a names))
(import types-module fail-at s-expr s-defn split kind-of atm-var atm-lit atm-rib-of show-syn sub?
        syntax-sig-of bind-rib s-export (type fails sty atms entries addr))
(import files-module signature-of)
(import align-module align node-syn node-kids node-core node-hole node-export nnodes nodes-reset!
        env-empty env-levels lv-rib lv-earlier k-pvar k-binder k-ref k-form program-walk defined
        macro-of (type pvars levels found env))
(import scopes-module walk evaluate program-scoped)
(import exports-module exports-of)
(import match-module same-atom?)

(define-type renames (listof (tupleof symbol symbol) acyclic))
;; Parts' places; binders' names by part; what is renamed in each part.
(define-type places (listof (tupleof int int) acyclic))
(define-type numbered (listof (tupleof int symbol) acyclic))
(define-type renamings (listof (tupleof int int renames sty) acyclic))
;; The parts of use operands `operands`, aligned with contract `sig` (just
;; now: the nodes are the use's), that a binder's scope reaches: each by its
;; place, with what is renamed in it, its binders' names each to a fresh
;; one, the innermost first; and each fresh name with the name it stands
;; for (`Macros::contract_renames`). Found as a pattern's are: each of the
;; use's parts at a leaf of the signature made a pattern variable, the
;; pattern aligned and walked.
(define contract-renames
  (->* (fails sty syn) (tupleof renamings renames))
  (lambda (fail sig operands)
    (let* ((leaves (leaves-of fail 0 (get nnodes) nil))
           (made (begin (set pseudo-parts nil) (pseudo-pattern operands leaves)))
           (parts (the syns-a (reverse (get pseudo-parts))))
           (root (begin (nodes-reset!) (align fail 0 (the pvars nil) sig made -1 nil)))
           (found (walk fail root env-empty #f 0))
           (vars (part-vars fail found parts nil))
           (binders (binder-parts vars parts nil))
           (fresh (fresh-names binders)))
      (tuple (part-renames vars parts binders fresh nil)
             (the renames (fresh-originals binders fresh))))))
;; The places of the nodes from `i` to `n` at a leaf of the signature.
(define leaves-of (->* (fails int int places) places)
  (lambda (fail i n out)
    (if (= i n)
        out
        (begin
          (if (null? (node-hole i))
              #u
              (fail-at fail "a procedural macro's contract of typed parts: not yet" (node-syn i)))
          (leaves-of fail (+ i 1) n
                     (if (leaf-sty? (node-core i))
                         (cons (tuple (syn-start (node-syn i)) (syn-end (node-syn i))) out)
                         out))))))
(define leaf-sty? (->* (sty) bool)
  (lambda (t)
    (tagcase t
      (s-expr () #t) (s-lambda () #t) (s-bvar () #t) (s-dvar () #t) (s-id () #t) (s-data () #t)
      (s-type () #t) (s-label () #t) (s-kind () #t) (s-defn () #t) (s-item () #t)
      (else y #f))))
(define pseudo-parts (ref syns-a rs) (new nil))
;; `s`, each part at a place in `leaves` the pattern variable `%part:k`,
;; that part `pseudo-parts`' `k`th.
(define pseudo-pattern (->* (syn places) syn)
  (lambda (s leaves)
    (if (place-in? (syn-start s) (syn-end s) leaves)
        (let ((k (len (get pseudo-parts))))
          (begin (set pseudo-parts (cons s (get pseudo-parts)))
                 (atom (string->symbol (string-append "%part:" (int->string k)))
                       (syn-start s) (syn-end s) (syn-expansion s))))
        (tagcase s
          (lst (items d a b x)
            (let ((xs (pseudo-each items leaves))) (lst xs (syn-datums xs) a b x)))
          (dotted (items tail d a b x)
            (let ((xs (pseudo-each items leaves)) (tl (pseudo-pattern tail leaves)))
              (dotted xs tl (datum-dotted (syn-datums xs) (syn->datum tl)) a b x)))
          (else y s)))))
(define pseudo-each (->* (syns-a places) syns-a)
  (lambda (xs leaves)
    (if (null? xs)
        nil
        (let ((x (pseudo-pattern (car xs) leaves))) (cons x (pseudo-each (cdr xs) leaves))))))
(define place-in? (->* (int int places) bool)
  (lambda (a b ps)
    (and (not (null? ps))
         (or (and (= a (extract (car ps) 1)) (= b (extract (car ps) 2)))
             (place-in? a b (cdr ps))))))
;; Part `k` of a pattern variable `%part:k`; -1 for another name.
(define part-number (->* (symbol) int)
  (lambda (n)
    (let ((s (symbol->string n)))
      (if (and (> (string-length s) 6) (string=? (substring s 0 6) "%part:"))
          (parse-nat (substring s 6 (string-length s)) 10)
          -1))))
;; Each pattern variable the walk found: its part, whether a binder, and the
;; binders (as pattern variables) in its scope, innermost first.
(define-type part-var (tupleof int bool (listof symbol acyclic) sty))
(define part-vars (->* (fails found syns-a (listof part-var acyclic)) (listof part-var acyclic))
  (lambda (fail fs parts out)
    (if (null? fs)
        out
        (let* ((at (extract (car fs) 1))
               (v (tagcase (node-kids at)
                    (k-pvar (n)
                      (let ((k (part-number n)))
                        (if (< k 0)
                            nil
                            (list (tuple k (tagcase (node-core at) (s-bvar () #t) (s-dvar () #t)
                                             (else y #f))
                                         (scope-binders fail (env-levels (extract (car fs) 2))
                                                        (nth parts k) nil)
                                         (node-core at))))))
                    (else y nil))))
          (part-vars fail (cdr fs) parts (if (null? v) out (cons (car v) out)))))))
(define scope-binders (->* (fails levels syn (listof symbol acyclic)) (listof symbol acyclic))
  (lambda (fail ls part out)
    (if (null? ls)
        (the (listof symbol acyclic) (reverse out))
        (tagcase (car ls)
          (lv-rib (as) (scope-binders fail (cdr ls) part (atoms-binders fail as part out)))
          (lv-earlier (as) (scope-binders fail (cdr ls) part (atoms-binders fail as part out)))
          (else y (begin (fail-at fail (string-append "a part in the scope of a ribcage or a "
                                                      "module: not yet in a procedural macro's "
                                                      "contract")
                                  part)
                         out))))))
(define atoms-binders (->* (fails atms syn (listof symbol acyclic)) (listof symbol acyclic))
  (lambda (fail as part out)
    (if (null? as)
        out
        (tagcase (car as)
          (atm-var (b d g) (atoms-binders fail (cdr as) part (cons b out)))
          (else y (begin (fail-at fail (string-append "a part in the scope of the binders another "
                                                      "part exports: not yet in a procedural "
                                                      "macro's contract")
                                  part)
                         out))))))
;; Each binder: its part's number, and its name.
(define binder-parts
  (->* ((listof part-var acyclic) syns-a numbered)
       numbered)
  (lambda (vs parts out)
    (cond ((null? vs) out)
          ((and (extract (car vs) 2) (syn-symbol? (nth parts (extract (car vs) 1))))
           (binder-parts (cdr vs) parts
                         (cons (tuple (extract (car vs) 1)
                                      (syn-symbol (nth parts (extract (car vs) 1))))
                               out)))
          (else (binder-parts (cdr vs) parts out)))))
;; Each binder's fresh name, by its part, as `Macros::contract_renames` makes it.
(define fresh-names (->* (numbered) numbered)
  (lambda (bs)
    (if (null? bs)
        nil
        (cons (tuple (extract (car bs) 1)
                     (string->symbol (string-append "%contract:" (int->string (extract (car bs) 1))
                                                    ":" (symbol->string (extract (car bs) 2)))))
              (fresh-names (cdr bs))))))
(define fresh-originals (->* (numbered numbered) renames)
  (lambda (bs fs)
    (if (null? bs)
        nil
        (cons (tuple (extract (car fs) 2) (extract (car bs) 2))
              (fresh-originals (cdr bs) (cdr fs))))))
(define part-name (->* (int numbered) (listof symbol acyclic))
  (lambda (k bs)
    (cond ((null? bs) nil) ((= k (extract (car bs) 1)) (list (extract (car bs) 2)))
          (else (part-name k (cdr bs))))))
(define var-part (->* (symbol) int) (lambda (b) (part-number b)))
;; Each part a binder's scope reaches, by its place, and what is renamed in it.
(define part-renames
  (->* ((listof part-var acyclic) syns-a numbered
        numbered renamings)
       renamings)
  (lambda (vs parts bs fs out)
    (if (null? vs)
        out
        (let* ((k (extract (car vs) 1))
               (own (if (extract (car vs) 2)
                        (the renames (list (tuple (car (part-name k bs)) (car (part-name k fs)))))
                        nil))
               (rs (scope-renames (extract (car vs) 3) bs fs own))
               (p (nth parts k)))
          (part-renames (cdr vs) parts bs fs
                        (if (null? rs)
                            out
                            (cons (tuple (syn-start p) (syn-end p) rs (extract (car vs) 4))
                                  out)))))))
(define scope-renames
  (->* ((listof symbol acyclic) numbered
        numbered renames)
       renames)
  (lambda (in-scope bs fs out)
    (if (null? in-scope)
        out
        (let* ((k (var-part (car in-scope))) (x (part-name k bs)) (to (part-name k fs)))
          (scope-renames (cdr in-scope) bs fs
                         (if (or (null? x) (not (null? (renamed-to (car x) out))))
                             out
                             (cons (tuple (car x) (car to)) out)))))))
(define renamed-to (->* (symbol renames) (listof symbol acyclic))
  (lambda (n rs)
    (cond ((null? rs) nil) ((symbol=? n (extract (car rs) 1)) (list (extract (car rs) 2)))
          (else (renamed-to n (cdr rs))))))
(define syn-renamed (->* (syn renames) syn)
  (lambda (s rs)
    (tagcase s
      (atom (d a b x)
        (if (syn-symbol? s)
            (let ((to (renamed-to (syn-symbol s) rs))) (if (null? to) s (atom (car to) a b x)))
            s))
      (lst (items d a b x) (let ((xs (renamed-each items rs))) (lst xs (syn-datums xs) a b x)))
      (dotted (items tail d a b x)
        (let ((xs (renamed-each items rs)) (tl (syn-renamed tail rs)))
          (dotted xs tl (datum-dotted (syn-datums xs) (syn->datum tl)) a b x)))
      (vec (items d a b x)
        (let ((xs (renamed-each items rs))) (vec xs (datum-list->vector (syn-datums xs)) a b x))))))
(define renamed-each (->* (syns-a renames) syns-a)
  (lambda (xs rs) (if (null? xs) nil (cons (syn-renamed (car xs) rs) (renamed-each (cdr xs) rs)))))
;; Use `s`, each part `ps` has by its place renamed as it says.
;; Use `s` α-renamed: each part `ps` has, by its place, a binder's its fresh
;; name, any other's references to the binders in whose scope it is, as
;; the part's own binding structure finds them (`references-renamed`).
(define renamed-use (->* (fails syn renamings) syn)
  (lambda (fail s ps)
    (let ((r (part-renames-at (syn-start s) (syn-end s) ps)))
      (if (not (null? r))
          (tagcase (extract (car r) 2)
            (s-bvar () (syn-renamed s (extract (car r) 1)))
            (s-dvar () (syn-renamed s (extract (car r) 1)))
            (else y (references-renamed fail s (extract (car r) 2) (extract (car r) 1))))
          (tagcase s
            (lst (items d a b x)
              (let ((xs (renamed-use-each fail items ps))) (lst xs (syn-datums xs) a b x)))
            (dotted (items tail d a b x)
              (let ((xs (renamed-use-each fail items ps)) (tl (renamed-use fail tail ps)))
                (dotted xs tl (datum-dotted (syn-datums xs) (syn->datum tl)) a b x)))
            (else y s))))))
(define renamed-use-each (->* (fails syns-a renamings) syns-a)
  (lambda (fail xs ps)
    (if (null? xs) nil (cons (renamed-use fail (car xs) ps) (renamed-use-each fail (cdr xs) ps)))))
(define part-renames-at (->* (int int renamings) (listof (tupleof renames sty) acyclic))
  (lambda (a b ps)
    (cond ((null? ps) nil)
          ((and (= a (extract (car ps) 1)) (= b (extract (car ps) 2)))
           (list (tuple (extract (car ps) 3) (extract (car ps) 4))))
          (else (part-renames-at a b (cdr ps))))))
;; Part `part`, of syntax type `core`, each free reference in it to a name
;; `rs` names renamed, as its own binding structure finds them (aligned as
;; a program's form is, its macros' uses by their signatures); its binders,
;; and what it quotes, as they are (`Macros::references_renamed`). By
;; place: two references at one place are one template's part, alike.
(define references-renamed (->* (fails syn sty renames) syn)
  (lambda (fail part core rs)
    (let* ((found (extract (program-scoped fail core part #f nil) 2))
           (at (free-refs found rs nil)))
      (syn-renamed-at part at))))
(define-type placed-renames (listof (tupleof int int symbol) acyclic))
(define free-refs (->* (found renames placed-renames) placed-renames)
  (lambda (fs rs out)
    (if (null? fs)
        out
        (free-refs (cdr fs) rs
                   (tagcase (node-kids (extract (car fs) 1))
                     (k-ref (n d f)
                       (let ((to (renamed-to n rs)) (s (node-syn (extract (car fs) 1))))
                         (if (or (null? to)
                                 (not (= (bound-by (env-levels (extract (car fs) 2)) n d) -1)))
                             out
                             (cons (tuple (syn-start s) (syn-end s) (car to)) out))))
                     (else y out))))))
;; `s`, each symbol at a place `at` has made the name it says.
(define syn-renamed-at (->* (syn placed-renames) syn)
  (lambda (s at)
    (tagcase s
      (atom (d a b x)
        (let ((to (placed-at a b at)))
          (if (and (syn-symbol? s) (not (null? to))) (atom (car to) a b x) s)))
      (lst (items d a b x) (let ((xs (renamed-at-each items at))) (lst xs (syn-datums xs) a b x)))
      (dotted (items tail d a b x)
        (let ((xs (renamed-at-each items at)) (tl (syn-renamed-at tail at)))
          (dotted xs tl (datum-dotted (syn-datums xs) (syn->datum tl)) a b x)))
      (vec (items d a b x)
        (let ((xs (renamed-at-each items at)))
          (vec xs (datum-list->vector (syn-datums xs)) a b x))))))
(define renamed-at-each (->* (syns-a placed-renames) syns-a)
  (lambda (xs at)
    (if (null? xs) nil (cons (syn-renamed-at (car xs) at) (renamed-at-each (cdr xs) at)))))
(define placed-at (->* (int int placed-renames) (listof symbol acyclic))
  (lambda (a b at)
    (cond ((null? at) nil)
          ((and (= a (extract (car at) 1)) (= b (extract (car at) 2))) (list (extract (car at) 3)))
          (else (placed-at a b (cdr at))))))
;; The binder node a reference to `n` (of a description's if `d`) is bound
;; by in `ls`, the innermost; -2 for a pattern's binder, -1 for none.
(define bound-by (->* (levels symbol bool) int)
  (lambda (ls n d)
    (if (null? ls)
        -1
        (let ((b (tagcase (car ls)
                   (lv-rib (as) (bound-in as n d))
                   (lv-earlier (as) (bound-in as n d))
                   (else y -1))))
          (if (= b -1) (bound-by (cdr ls) n d) b)))))
(define bound-in (->* (atms symbol bool) int)
  (lambda (as n d)
    (if (null? as)
        -1
        (let ((b (tagcase (car as)
                   (atm-lit (i e)
                     (tagcase (node-kids i)
                       (k-binder (m e2) (if (and (symbol=? m n) (eq? e2 d)) i -1))
                       (else y -1)))
                   (atm-var (m e g) (if (and (symbol=? m n) (eq? e d)) -2 -1))
                   (else y -1))))
          (if (= b -1) (bound-in (cdr as) n d) b)))))
;; Output `s`'s nodes, aligned as a program's form is (nothing expanded) and
;; walked, each as α-equivalence takes it: its kind, the nodes under it by
;; number, a binder whatever its name, a reference by its binder or, free,
;; by its name, any other part as it is (`Macros::alpha_nodes`).
(define-type anode (tupleof int (listof int acyclic) (listof symbol acyclic) (listof syn acyclic)))
(define-type anodes (listof anode acyclic))
(define alpha-nodes (->* (fails syn sty) anodes)
  (lambda (fail s made)
    (let ((found (extract (program-scoped fail made s #f nil) 2)))
      (anodes-from 0 (get nnodes) found nil))))
(define anodes-from (->* (int int found anodes) anodes)
  (lambda (i n fs out)
    (if (= i n)
        (the anodes (reverse out))
        (anodes-from (+ i 1) n fs (cons (anode-of i fs) out)))))
(define anode-of (->* (int found) anode)
  (lambda (i fs)
    (let ((none (the (listof symbol acyclic) nil)) (no (the (listof syn acyclic) nil))
          (bit (lambda ((d bool)) (if d 1 0))))
      (tagcase (node-kids i)
        (k-pair (x y) (tuple 0 (list x y) none no))
        (k-nil () (tuple 1 nil none no))
        (k-binder (m d) (tuple 2 (list (bit d)) none no))
        (k-ref (m d f)
          (let ((b (bound-by (env-levels (env-at i fs)) m d)))
            (if (= b -1) (tuple 4 (list (bit d)) (list m) no) (tuple 3 (list b) none no))))
        (k-desc (xs) (tuple 5 xs none no))
        (k-seq (x) (tuple 6 (list x) none no))
        (k-form (x) (tuple 7 (list x) none no))
        (else y (tuple 8 nil none (list (node-syn i))))))))
(define env-at (->* (int found) env)
  (lambda (i fs)
    (cond ((null? fs) env-empty)
          ((= i (extract (car fs) 1)) (extract (car fs) 2))
          (else (env-at i (cdr fs))))))
(define alpha-same? (->* (anodes anodes) bool)
  (lambda (as bs)
    (cond ((null? as) (null? bs))
          ((null? bs) #f)
          (else (and (anode-same? (car as) (car bs)) (alpha-same? (cdr as) (cdr bs)))))))
(define anode-same? (->* (anode anode) bool)
  (lambda (a b)
    (and (= (extract a 1) (extract b 1)) (ints-same? (extract a 2) (extract b 2))
         (names-same? (extract a 3) (extract b 3))
         (or (null? (extract a 4))
             (and (not (null? (extract b 4)))
                  (syn-same? (car (extract a 4)) (car (extract b 4))))))))
(define ints-same? (->* ((listof int acyclic) (listof int acyclic)) bool)
  (lambda (xs ys)
    (cond ((null? xs) (null? ys)) ((null? ys) #f)
          (else (and (= (car xs) (car ys)) (ints-same? (cdr xs) (cdr ys)))))))
(define names-same? (->* ((listof symbol acyclic) (listof symbol acyclic)) bool)
  (lambda (xs ys)
    (cond ((null? xs) (null? ys)) ((null? ys) #f)
          (else (and (symbol=? (car xs) (car ys)) (names-same? (cdr xs) (cdr ys)))))))
;; Output `out2`, the transformer's of the α-renamed use, held to output
;; `out`, its of the use: the same up to their binders' names; else refused
;; at use `s`, by `in-use`: a fresh name of `fresh`, or its alias of
;; expansion `made` (`%~K.N:x′`), free in `out2`, placed outside its binder's
;; scope; else a name read (`Macros::contract_expanded`).
(define contract-held (->* (fails syn syn syn renames int sty) unit)
  (lambda (in-use s out out2 fresh made ty)
    (let* ((ours (lambda ((m string) (a int) (b int))
                   (in-use (string-append "its expansion: " m) (syn-start s) (syn-end s))))
           (a (alpha-nodes ours out ty)) (b (alpha-nodes ours out2 ty)))
      (if (alpha-same? a b)
          #u
          (let ((x (escaped b fresh made)))
            (in-use (if (null? x)
                        "its expansion depends on how its use's bound names are spelled"
                        (string-append "its expansion places `" (symbol->string (car x))
                                       "` where its contract does not put it in `"
                                       (symbol->string (car x)) "`'s scope"))
                    (syn-start s) (syn-end s)))))))
(define escaped (->* (anodes renames int) (listof symbol acyclic))
  (lambda (ns fresh made)
    (if (null? ns)
        nil
        (let ((x (if (and (= (extract (car ns) 1) 4) (not (null? (extract (car ns) 3))))
                     (fresh-of (car (extract (car ns) 3)) fresh made)
                     nil)))
          (if (null? x) (escaped (cdr ns) fresh made) x)))))
(define fresh-of (->* (symbol renames int) (listof symbol acyclic))
  (lambda (n fresh made)
    (cond ((null? fresh) nil)
          ((or (symbol=? n (extract (car fresh) 1))
               (string=? (symbol->string n)
                         (string-append "%~" (tag-of made) ":"
                                        (symbol->string (extract (car fresh) 1)))))
           (list (extract (car fresh) 2)))
          (else (fresh-of n (cdr fresh) made)))))
;; Whether syntax `a` and `b` are the same, part by part, wherever each is.
(define syn-same? (->* (syn syn) bool)
  (lambda (a b)
    (tagcase a
      (lst (xs d c e x) (tagcase b (lst (ys d2 c2 e2 x2) (all-same? xs ys)) (else y #f)))
      (dotted (xs t d c e x)
        (tagcase b
          (dotted (ys u d2 c2 e2 x2) (and (all-same? xs ys) (syn-same? t u)))
          (else y #f)))
      (atom (d c e x)
        (if (syn-symbol? a)
            (and (syn-symbol? b) (symbol=? (syn-symbol a) (syn-symbol b)))
            (same-atom? a b)))
      (else y #f))))
(define all-same? (->* (syns-a syns-a) bool)
  (lambda (xs ys)
    (if (null? xs)
        (null? ys)
        (and (not (null? ys)) (syn-same? (car xs) (car ys)) (all-same? (cdr xs) (cdr ys))))))

;;; ------------------------------------------------------------ definitions

;; Names, each with whether a description's.
(define-type named-ns (listof (tupleof symbol bool) acyclic))
;; Definitions `out`, what a transformer made of use operands `operands` in
;; expansion `made`, held to contract `sig` (`Macros::defined_held`):
;; definitions, aligned as a program's are, that define of the use's names
;; exactly those the contract says its uses define; any other name they
;; define their own, an alias of the expansion (`%~K.N:x`). Refused at `out`.
(define defined-held (->* (fails sty syn syn int) unit)
  (lambda (fail sig operands out made)
    (let* ((said (contract-said fail sig operands))
           (ours (lambda ((m string) (a int) (b int))
                   (fail (string-append "its expansion: " m) a b)))
           (defines (expansion-defines ours out))
           (own (string-append "%~" (tag-of made) ":"))
           (extra (named-not-in defines said own))
           (missing (named-not-in said defines "")))
      (cond ((not (null? extra))
             (fail-at fail (string-append "its expansion defines `" (symbol->string (car extra))
                                          "`, which its contract does not say a use defines, "
                                          "nor is it its own (an alias, as `rename` makes one)")
                      out))
            ((not (null? missing))
             (fail-at fail (string-append "its contract says a use defines `"
                                          (symbol->string (car missing))
                                          "`, and its expansion does not")
                      out))
            (else #u)))))
;; The first of `xs` that `ys` has not, nor, if `own` is not empty, is
;; spelled from it; in a list of one.
(define named-not-in (->* (named-ns named-ns string) (listof symbol acyclic))
  (lambda (xs ys own)
    (cond ((null? xs) nil)
          ((or (named-in? (car xs) ys) (own-name? (extract (car xs) 1) own))
           (named-not-in (cdr xs) ys own))
          (else (list (extract (car xs) 1))))))
(define named-in? (->* ((tupleof symbol bool) named-ns) bool)
  (lambda (x ys)
    (and (not (null? ys))
         (or (and (symbol=? (extract x 1) (extract (car ys) 1))
                  (eq? (extract x 2) (extract (car ys) 2)))
             (named-in? x (cdr ys))))))
(define own-name? (->* (symbol string) bool)
  (lambda (n own)
    (let ((s (symbol->string n)) (k (string-length own)))
      (and (> k 0) (>= (string-length s) k) (string=? (substring s 0 k) own)))))
;; What contract `sig` says a use of operands `operands` defines, of the
;; use's names: the use aligned, then made a pattern, each leaf a part, whose
;; export is evaluated.
(define contract-said (->* (fails sty syn) named-ns)
  (lambda (fail sig operands)
    (let* ((use (begin (nodes-reset!) (align fail 2 (the pvars nil) sig operands -1 nil)))
           (leaves (leaves-of fail 0 (get nnodes) nil))
           (made (begin (set pseudo-parts nil) (pseudo-pattern operands leaves)))
           (parts (the syns-a (reverse (get pseudo-parts))))
           (root (begin (nodes-reset!) (align fail 0 (the pvars nil) sig made -1 nil)))
           (found (walk fail root env-empty #f 0))
           (e (node-export root)))
      (if (null? e)
          nil
          (let ((x (exports-of (evaluate fail (extract (car e) 1) (extract (car e) 2) made))))
            (if (null? (extract x 2))
                (said-names fail (extract x 1) parts operands)
                (begin (said-not-yet fail operands) nil)))))))
(define said-not-yet (->* (fails syn) unit)
  (lambda (fail at)
    (fail-at fail "a contract whose uses define what a part of theirs defines: not yet" at)))
(define said-names (->* (fails atms syns-a syn) named-ns)
  (lambda (fail as parts at)
    (if (null? as)
        nil
        (tagcase (car as)
          (atm-var (b d g)
            (let ((p (nth parts (part-number b))))
              (if (syn-symbol? p)
                  (cons (tuple (syn-symbol p) d) (said-names fail (cdr as) parts at))
                  (begin (fail-at fail "a binder that is not a name" p) nil))))
          (atm-rib-of (n) (begin (said-not-yet fail at) nil))
          (atm-lit (i d) (said-names fail (cdr as) parts at))))))
;; What definitions `out` define, aligned as a program's are: each binder a
;; definition's form exports, by its name.
(define expansion-defines (->* (fails syn) named-ns)
  (lambda (fail out)
    (let* ((scoped (program-scoped fail (s-defn) out #f nil))
           (ds (begin (set program-walk #t) (defines-from fail 0 (get nnodes) nil))))
      (begin (set program-walk #f) ds))))
(define defines-from (->* (fails int int named-ns) named-ns)
  (lambda (fail i n out)
    (if (= i n)
        out
        (defines-from fail (+ i 1) n
          (let ((k (kind-of (node-core i))))
            (if (or (= k 14) (= k 11))
                (tagcase (node-kids i)
                  (k-form (x)
                    (let ((ex (node-export x)))
                      (if (null? ex)
                          out
                          (level-defines (evaluate fail (extract (car ex) 1) (extract (car ex) 2)
                                                   (node-syn i))
                                         out))))
                  (else y out))
                out))))))
(define level-defines (->* (levels named-ns) named-ns)
  (lambda (ls out)
    (if (null? ls)
        out
        (level-defines (cdr ls)
                       (tagcase (car ls) (lv-rib (as) (atm-defines as out)) (else y out))))))
(define atm-defines (->* (atms named-ns) named-ns)
  (lambda (as out)
    (if (null? as)
        out
        (atm-defines (cdr as)
                     (tagcase (car as)
                       (atm-lit (b d)
                         (tagcase (node-kids b)
                           (k-binder (m e)
                             (if (named-in? (tuple m d) out) out (cons (tuple m d) out)))
                           (else y out)))
                       (else y out))))))

;;; ------------------------------------------------------------ macros an expansion defines

;; The macros the last top-level form's expansion defined, in order
;; (`Withs::made_syntax`): for the parser, which holds each to the globals
;; and checks its templates (`made-syntax-taken!`).
(define made-syntax (ref names rs) (new nil))
(define made-syntax-reset! (->* () unit) (lambda () (set made-syntax nil)))
(define made-syntax-add! (->* (names) unit)
  (lambda (ns) (set made-syntax (append (get made-syntax) ns))))
(define made-syntax-count (->* () int) (lambda () (length (get made-syntax))))
(define made-syntax-taken! (->* () names)
  (lambda () (let ((ns (get made-syntax))) (begin (set made-syntax nil) ns))))
;; Use `s` of macro `name`, its expansion done: each macro its signature
;; says a use defines, `(ℓ (macro σ made))` in what it makes, defined by the
;; expansion (`made-syntax` from `from` on), and of signature `σ`
;; (`Macros::syntax_held`).
(define syntax-held (->* (fails symbol syn int) unit)
  (lambda (fail name s from)
    (let ((m (macro-of name (get defined))))
      (if (null? m)
          #u
          (tagcase (extract (car m) 1)
            (s-export (body b)
              (tagcase b (bind-rib (es) (syntax-held-each fail name s from es)) (else y #u)))
            (else y #u))))))
(define syntax-held-each (->* (fails symbol syn int entries) unit)
  (lambda (fail name s from es)
    (if (null? es)
        #u
        (let ((d (extract (car es) 2)))
          (if (< d 100)
              (syntax-held-each fail name s from (cdr es))
              (let* ((said (syntax-sig-of d)) (shown (show-syn said))
                     (part (syn-at-addr (nth (split s) 1) (extract (car es) 1)))
                     (x (if (and (not (null? part)) (syn-symbol? (car part)))
                            (syn-name (car part))
                            ""))
                     (refused (lambda ((m string))
                                (fail (string-append "a use of `" (symbol->string name) "`: " m)
                                      (syn-start s) (syn-end s)))))
                (cond ((string=? x "")
                       (refused (string-append "its signature says a macro of `" shown "` is "
                                               "defined at a part that is not a name")))
                      ((not (name-in-from? (string->symbol x) (get made-syntax) from))
                       (refused (string-append "its signature says it defines `" x "`, a macro "
                                               "of `" shown "`, and its expansion does not")))
                      ((not (same-signature? fail (string->symbol x) said))
                       (refused (string-append "its signature says `" x "` is a macro of `"
                                               shown "`, and its expansion defines one of "
                                               "another signature")))
                      (else (syntax-held-each fail name s from (cdr es))))))))))
;; The part of `s` at address `a`, in a list of one; none if there is none.
(define syn-at-addr (->* (syn addr) syns-a)
  (lambda (s a)
    (cond ((null? a) (list s))
          ((null? (split s)) nil)
          (else (syn-at-addr (if (car a) (car (split s)) (nth (split s) 1)) (cdr a))))))
;; Whether `n` is among `ns` from the `k`th on.
(define name-in-from? (->* (symbol names int) bool)
  (lambda (n ns k)
    (cond ((null? ns) #f)
          ((> k 0) (name-in-from? n (cdr ns) (- k 1)))
          (else (or (symbol=? n (car ns)) (name-in-from? n (cdr ns) 0))))))
;; Whether macro `n`'s signature is the one `said` writes: the same syntax
;; type, each a subtype of the other, of the same made, none `poly`, and no
;; procedural macro's of no contract.
(define same-signature? (->* (fails symbol syn) bool)
  (lambda (fail n said)
    (let ((have (car (macro-of n (get defined)))) (want (signature-of fail said)))
      (and (null? (extract want 1)) (null? (extract have 3))
           (= (extract have 4) (extract want 3))
           (sub? (extract have 1) (extract want 2) nil)
           (sub? (extract want 2) (extract have 1) nil)))))

;; Each of `internal`'s macros, a file's by its name there, that `s`, what
;; a transformer gave in expansion `tag` (its number), names as renamed: by
;; the name the importer has it by (`macros-procedural.fx`'s
;; `expand-procedural`, `Macros::procedural_opened`; Heist's report,
;; 2026-11-18).
(define file-macros (->* (syn (listof (tupleof symbol symbol) acyclic) int) syn)
  (lambda (s internal tag)
    (if (null? internal)
        s
        (tagcase s
          (atom (d a b x)
            (if (symbol? d)
                (let ((i (renamed-macro (symbol->string d) internal tag)))
                  (if (null? i) s (atom (car i) a b x)))
                s))
          (lst (items d a b x)
            (let ((xs (file-macros-each items internal tag))) (lst xs (syn-datums xs) a b x)))
          (dotted (items t d a b x)
            (let ((xs (file-macros-each items internal tag)) (u (file-macros t internal tag)))
              (dotted xs u (datum-dotted (syn-datums xs) (syn->datum u)) a b x)))
          (vec (items d a b x) s)))))
(define file-macros-each (->* (syns-a (listof (tupleof symbol symbol) acyclic) int) syns-a)
  (lambda (xs internal tag)
    (if (null? xs)
        nil
        (cons (file-macros (car xs) internal tag) (file-macros-each (cdr xs) internal tag)))))
(define renamed-macro
  (->* (string (listof (tupleof symbol symbol) acyclic) int) (listof symbol acyclic))
  (lambda (n internal tag)
    (cond ((null? internal) nil)
          ((string=? n (string-append "%~" (tag-of tag) ":"
                                      (symbol->string (extract (car internal) 1))))
           (list (extract (car internal) 2)))
          (else (renamed-macro n (cdr internal) tag)))))
