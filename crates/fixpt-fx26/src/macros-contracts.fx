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
(import reader-types atom lst dotted vec (type syn))
(import parser-module syn-start syn-end syn-symbol? syn-name syn-symbol syn-datums syn->datum
        syn-expansion len nth (type syns-a))
(import types-module fail-at s-expr split (type fails sty atms))
(import align-module align node-syn node-kids node-core node-hole nnodes nodes-reset! env-empty
        env-levels lv-rib lv-earlier k-pvar k-binder k-ref program-walk
        (type pvars levels found))
(import scopes-module walk)
(import match-module same-atom?)

(define-type renames (listof (tupleof symbol symbol) acyclic))
;; Parts' places; binders' names by part; what is renamed in each part.
(define-type places (listof (tupleof int int) acyclic))
(define-type numbered (listof (tupleof int symbol) acyclic))
(define-type renamings (listof (tupleof int int renames) acyclic))
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
(define-type part-var (tupleof int bool (listof symbol acyclic)))
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
                                                        (nth parts k) nil))))))
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
                        (if (null? rs) out (cons (tuple (syn-start p) (syn-end p) rs) out)))))))
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
(define renamed-use (->* (syn renamings) syn)
  (lambda (s ps)
    (let ((r (part-renames-at (syn-start s) (syn-end s) ps)))
      (if (not (null? r))
          (syn-renamed s (car r))
          (tagcase s
            (lst (items d a b x)
              (let ((xs (renamed-use-each items ps))) (lst xs (syn-datums xs) a b x)))
            (dotted (items tail d a b x)
              (let ((xs (renamed-use-each items ps)) (tl (renamed-use tail ps)))
                (dotted xs tl (datum-dotted (syn-datums xs) (syn->datum tl)) a b x)))
            (else y s))))))
(define renamed-use-each (->* (syns-a renamings) syns-a)
  (lambda (xs ps)
    (if (null? xs) nil (cons (renamed-use (car xs) ps) (renamed-use-each (cdr xs) ps)))))
(define part-renames-at (->* (int int renamings) (listof renames acyclic))
  (lambda (a b ps)
    (cond ((null? ps) nil)
          ((and (= a (extract (car ps) 1)) (= b (extract (car ps) 2))) (list (extract (car ps) 3)))
          (else (part-renames-at a b (cdr ps))))))
;; Output `out2`'s fresh names each a binder, or a reference in the scope of
;; one, as its program's walk finds them; else refused at use `s`.
(define placed-in-scopes (->* (fails syn syn renames) unit)
  (lambda (in-use s out2 fresh)
    (let* ((fail (lambda ((m string) (a int) (b int))
                   (in-use (string-append "its expansion: " m) (syn-start s) (syn-end s))))
           (root (begin (nodes-reset!) (set program-walk #t)
                        (align fail 3 (the pvars nil) (s-expr) out2 -1 nil)))
           (found (walk fail root env-empty #f 0)))
      (begin (set program-walk #f) (refs-bound in-use s found fresh)))))
(define refs-bound (->* (fails syn found renames) unit)
  (lambda (in-use s fs fresh)
    (if (null? fs)
        #u
        (begin
          (tagcase (node-kids (extract (car fs) 1))
            (k-ref (n d f)
              (let ((original (renamed-to n fresh)))
                (if (or (null? original) (levels-bind? (env-levels (extract (car fs) 2)) n))
                    #u
                    (in-use (string-append "its expansion places `" (symbol->string (car original))
                                           "` where its contract does not put it in `"
                                           (symbol->string (car original)) "`'s scope")
                            (syn-start s) (syn-end s)))))
            (else y #u))
          (refs-bound in-use s (cdr fs) fresh)))))
(define levels-bind? (->* (levels symbol) bool)
  (lambda (ls n)
    (and (not (null? ls))
         (or (tagcase (car ls)
               (lv-rib (as) (atoms-bind? as n))
               (lv-earlier (as) (atoms-bind? as n))
               (else y #f))
             (levels-bind? (cdr ls) n)))))
(define atoms-bind? (->* (atms symbol) bool)
  (lambda (as n)
    (and (not (null? as))
         (or (tagcase (car as)
               (atm-var (b d g) (symbol=? b n))
               (atm-lit (i d) (tagcase (node-kids i) (k-binder (m e) (symbol=? m n)) (else y #f)))
               (else y #f))
             (atoms-bind? (cdr as) n)))))

;; Output `out2`, the transformer's of the renamed use, held to output
;; `out`, its of the use: its fresh names where their binders' scopes are
;; (`placed-in-scopes`), and, each named back, `out` itself; else refused
;; at use `s`, by `in-use`.
(define contract-held (->* (fails syn syn syn renames int) unit)
  (lambda (in-use s out out2 fresh0 made)
    (let ((fresh (append fresh0 (aliased fresh0 made #f)))
          (back (append fresh0 (aliased fresh0 made #t))))
     (begin
      (placed-in-scopes in-use s out2 fresh)
      (if (syn-same? (syn-renamed out2 back) out)
          #u
          (in-use "its expansion depends on how its use's bound names are spelled"
                  (syn-start s) (syn-end s)))))))
;; Of each fresh name of `fs`, its alias of expansion `made`, `%~N:x′` (a
;; name the transformer wrote where its macro is defined, closed so), fresh
;; too: with the original's alias if `back`, else the original
;; (`Macros::contract_expanded`).
(define aliased (->* (renames int bool) renames)
  (lambda (fs made back)
    (if (null? fs)
        nil
        (let ((at (lambda ((n symbol))
                    (string->symbol (string-append "%~" (int->string made) ":"
                                                   (symbol->string n))))))
          (cons (tuple (at (extract (car fs) 1))
                       (if back (at (extract (car fs) 2)) (extract (car fs) 2)))
                (aliased (cdr fs) made back))))))
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
