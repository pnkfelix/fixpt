;;; Typed hygienic macros, in FX-26: signatures inferred, a `syntax-rules`
;;; macro's where its `define-syntax` writes none, as the Rust expander
;;; infers them (`macros/infer.rs`, whose comment says how). Its shape is
;;; its patterns' merged; each pattern variable's syntax type what its
;;; template places it as, `(many …)` if placed more than once; the bindings
;;; it is in the scope of, those its template places it in, said where an
;;; address can say them; a template's use of the macro itself, or of
;;; another of its `define-syntax-rec`, aligned with the signature so far,
;;; until it says the same twice. What is inferred is then checked as a
;;; written signature is (`macros.fx`, which loads this file and takes
;;; `files-module` from it, so that the expander's parts are one).

(module-parameters ((rs region) (re region) (rm region) (rc region) (rp region)))
(define files-module ((proj (load-module "fx26:macros-files.fx") rs re rm rc rp)))
(define exports-module (with files-module exports-module))
(define match-module (with exports-module match-module))
(define scopes-module (with exports-module scopes-module))
(define align-module (with files-module align-module))
(define types-module (with align-module types-module))
(define parser-module (with types-module parser-module))
(define reader-types (with parser-module reader-types))
(import reader-types atom lst dotted vec (type syn))
(import parser-module syn-start syn-end syn-symbol? syn-name syn-symbol len nth mk-list
        mk-symbol syn-datums syn->datum parse-tag p-ok p-err pfail-at
        (type syns-a names presult) (effect parses))
(import types-module fail-at split syn-nil? syn-keyword? reserved? ellipsis-of proper-items
        name-in? show-syn kind-of sty=? mu-new mu-set! mu-body type-form? kernel-sigs
        s-expr s-bvar s-id s-data s-type s-label s-nil s-literal s-pair s-import s-export s-mu
        s-many s-union s-typed s-lambda s-defn s-dvar s-kind bind-rib bind-cage ring-rib ring-at
        bind-direct bind-earlier atm-var atm-rib-of atm-lit
        (type fails addr entries ring rings bind sty stys atm atms))
(import align-module defined macro-of nodes-reset! align node-core node-kids k-pvar lv-rib
        lv-cage lv-earlier
        (type macro macro-env pinfo pvars levels found))
(import scopes-module walk levels-of normal)
(import exports-module exports-of (type exported))

;;; ------------------------------------------------------------ the shape

;; A part of the shape of a macro's operands (`infer.rs`'s `Shape`): a
;; list by ellipsis, its element; a pattern variable's, of more than one,
;; the clauses'.
(define-datatype shape (sh-nil) (sh-pair int int) (sh-seq int) (sh-lit symbol) (sh-leaf)
  (sh-union (listof int acyclic)))
(define-type ints (listof int acyclic))
;; A part: its shape, its address from its region's root, and that root.
(define-type part (tupleof shape addr int))
;; A pattern's part, of a clause, under so many ellipses in its pattern.
(define-type item (tupleof int syn int))
(define-type items (listof item acyclic))
(define-datatype class (cl-seq syn) (cl-wild) (cl-lit symbol) (cl-var symbol) (cl-nil)
  (cl-pair syn syn))
(define-type classes (listof class acyclic))
;; Each pattern variable's part, by its clause, and how many ellipses its
;; pattern has it under, in the order found.
(define-type vars (listof (tupleof int symbol int int) acyclic))

(define parts (ref (arrayof part rs) rs) (new (make-array 64 (tuple (sh-leaf) (the addr nil) 0))))
(define nparts (ref int rs) (new 0))
(define found-vars (ref vars rs) (new nil))
;; Each region's root (a list's element, a `union`'s member), and the part
;; whose region it is; the clauses each member is of; each list by
;; ellipsis that took in patterns written one by one, and the place of the
;; first.
(define boundaries (ref (listof (tupleof int int) acyclic) rs) (new nil))
(define members (ref (listof (tupleof int ints) acyclic) rs) (new nil))
(define absorbed (ref (listof (tupleof int int int) acyclic) rs) (new nil))
(define roots (ref ints rs) (new nil))
(define parts-reset! (->* () unit)
  (lambda ()
    (begin (set nparts 0) (set found-vars nil) (set boundaries nil) (set members nil)
           (set absorbed nil) (set roots nil))))
(define part-at (->* (int) part) (lambda (i) (array-ref (get parts) i)))
(define shape-of (->* (int) shape) (lambda (i) (extract (part-at i) 1)))
(define path-of (->* (int) addr) (lambda (i) (extract (part-at i) 2)))
(define region (->* (int) int) (lambda (i) (extract (part-at i) 3)))
(define shape-set! (->* (int shape) unit)
  (lambda (i sh)
    (array-set! (get parts) i (tuple sh (path-of i) (region i)))))
;; A new part at `path` from `root` (-1: a region of its own): its number.
(define part-new (->* (addr int) int)
  (lambda (path root)
    (let ((i (get nparts)))
      (begin
        (if (= i (array-length (get parts)))
            (let ((bigger (the (arrayof part rs) (make-array (* 2 i) (part-at 0)))))
              (begin (copy-parts (get parts) bigger 0) (set parts bigger)))
            #u)
        (set nparts (+ i 1))
        (array-set! (get parts) i (tuple (sh-leaf) (if (< root 0) (the addr nil) path)
                                         (if (< root 0) i root)))
        i))))
(define copy-parts (->* ((arrayof part rs) (arrayof part rs) int) unit)
  (lambda (from to i)
    (if (= i (array-length from))
        #u
        (begin (array-set! to i (array-ref from i)) (copy-parts from to (+ i 1))))))
(define leaf? (->* (int) bool) (lambda (p) (tagcase (shape-of p) (sh-leaf () #t) (else y #f))))
(define union? (->* (int) bool)
  (lambda (p) (tagcase (shape-of p) (sh-union (ms) #t) (else y #f))))
(define int-assoc (->* (int (listof (tupleof int int) acyclic)) ints)
  (lambda (k xs)
    (cond ((null? xs) nil)
          ((= k (extract (car xs) 1)) (list (extract (car xs) 2)))
          (else (int-assoc k (cdr xs))))))
(define int-in? (->* (int ints) bool)
  (lambda (i is) (and (not (null? is)) (or (= i (car is)) (int-in? i (cdr is))))))
;; The part whose region `r` is, if any.
(define boundary-of (->* (int) ints) (lambda (r) (int-assoc r (get boundaries))))
;; Pattern variable `n` of clause `cid`'s part, and its depth, in a list of
;; one.
(define var-of (->* (int symbol) (listof (tupleof int int) acyclic))
  (lambda (cid n) (var-in cid n (get found-vars))))
(define var-in (->* (int symbol vars) (listof (tupleof int int) acyclic))
  (lambda (cid n vs)
    (cond ((null? vs) nil)
          ((and (= cid (extract (car vs) 1)) (symbol=? n (extract (car vs) 2)))
           (list (tuple (extract (car vs) 3) (extract (car vs) 4))))
          (else (var-in cid n (cdr vs))))))
(define var-part (->* (int symbol) ints)
  (lambda (cid n) (let ((v (var-of cid n))) (if (null? v) nil (list (extract (car v) 1))))))
(define var! (->* (int symbol int int) unit)
  (lambda (cid n p depth)
    (set found-vars (if (null? (var-of cid n))
                        (append (get found-vars) (the vars (list (tuple cid n p depth))))
                        (var-replaced cid n p depth (get found-vars))))))
(define var-replaced (->* (int symbol int int vars) vars)
  (lambda (cid n p depth vs)
    (cond ((null? vs) nil)
          ((and (= cid (extract (car vs) 1)) (symbol=? n (extract (car vs) 2)))
           (cons (tuple cid n p depth) (cdr vs)))
          (else (cons (car vs) (var-replaced cid n p depth (cdr vs)))))))

;; The regions part `p` is in, innermost first.
(define regions (->* (int) ints)
  (lambda (p) (regions-from (region p))))
(define regions-from (->* (int) ints)
  (lambda (r)
    (let ((b (boundary-of r))) (if (null? b) (list r) (cons r (regions-from (region (car b))))))))
;; How part `x` is reached from region `r`: directly (-1), or through the
;; part in `r` whose region it is in; in a list of one, none if `r` is not
;; around it.
(define via (->* (int int) ints)
  (lambda (x r) (if (= (region x) r) (list -1) (via-from (region x) r))))
(define via-from (->* (int int) ints)
  (lambda (q r)
    (let ((b (boundary-of q)))
      (cond ((null? b) nil)
            ((= (region (car b)) r) (list (car b)))
            (else (via-from (region (car b)) r))))))
;; The region inside part `b` clause `cid` is in, in a list of one.
(define inner (->* (int int) ints)
  (lambda (b cid)
    (tagcase (shape-of b)
      (sh-seq (e) (list e))
      (sh-union (ms) (member-of ms cid))
      (else y nil))))
(define member-of (->* (ints int) ints)
  (lambda (ms cid)
    (cond ((null? ms) nil)
          ((let ((cs (members-of (car ms) (get members)))) (int-in? cid cs)) (list (car ms)))
          (else (member-of (cdr ms) cid)))))
(define members-of (->* (int (listof (tupleof int ints) acyclic)) ints)
  (lambda (m xs)
    (cond ((null? xs) nil)
          ((= m (extract (car xs) 1)) (extract (car xs) 2))
          (else (members-of m (cdr xs))))))

;; What each clause's macro's literals are.
(define-type lits-of (listof names acyclic))
(define class-of (->* (fails item lits-of) class)
  (lambda (fail it lits)
    (let* ((s (extract it 2)) (x (ellipsis-of s)))
      (cond
        ((not (null? x)) (cl-seq (car x)))
        ((syn-symbol? s)
         (let ((name (syn-name s)))
           (cond ((string=? name "_") (cl-wild))
                 ((string=? name "...")
                  (begin (fail-at fail "`...` follows the part it repeats, last in a list" s)
                         (cl-wild)))
                 ((or (name-in? (syn-symbol s) (nth-names lits (extract it 1))) (reserved? name))
                  (cl-lit (syn-symbol s)))
                 (else (cl-var (syn-symbol s))))))
        ((syn-nil? s) (cl-nil))
        ((null? (split s)) (cl-wild))
        ;; A datum matches itself: its part takes anything.
        (else (tagcase s
                (vec (i d a b y) (cl-wild))
                (else z (cl-pair (car (split s)) (nth (split s) 1)))))))))
(define nth-names (->* (lits-of int) names)
  (lambda (xs i) (if (= i 0) (car xs) (nth-names (cdr xs) (- i 1)))))
(define classes-of (->* (fails items lits-of) classes)
  (lambda (fail its lits)
    (if (null? its) nil (cons (class-of fail (car its) lits) (classes-of fail (cdr its) lits)))))
(define leafy? (->* (class) bool)
  (lambda (c) (tagcase c (cl-var (n) #t) (cl-wild () #t) (else y #f))))
(define all-leafy? (->* (classes) bool)
  (lambda (cs) (or (null? cs) (and (leafy? (car cs)) (all-leafy? (cdr cs))))))

;; What the shape is built from: each clause's macro's literals, the
;; pattern variables' syntax types last found, and the lists by ellipsis
;; that are not to take in patterns written one by one.
(define-type cx (tupleof lits-of pkinds spans))
(define-type spans (listof (tupleof int int) acyclic))

;; The part for `its`, at `path` from region `root` (-1: its own).
(define merge (->* (fails items addr int cx) int)
  (lambda (fail its path root c)
    (let* ((id (part-new path root)) (cs (classes-of fail its (extract c 1))))
      (if (all-leafy? cs)
          (begin (vars-here! its cs id) id)
          (let ((ab (absorbable fail its cs c)))
            (if (not (null? ab))
                (let ((a (car ab)))
                  (begin
                    (seq-vars! (extract a 2) id)
                    (let ((e (merge fail (extract a 1) nil -1 c)))
                      (begin
                        (set boundaries (cons (tuple e id) (get boundaries)))
                        (shape-set! id (sh-seq e))
                        (if (extract a 3)
                            (let ((s (extract (car its) 2)))
                              (set absorbed (cons (tuple id (syn-start s) (syn-end s))
                                                  (get absorbed))))
                            #u)
                        id))))
                (let ((groups (grouped cs 0 nil)))
                  (begin
                    (if (null? (cdr groups))
                        (one! fail id its cs c)
                        (shape-set! id (sh-union (members! fail its groups id c))))
                    id))))))))
(define vars-here! (->* (items classes int) unit)
  (lambda (its cs id)
    (if (null? its)
        #u
        (begin (tagcase (car cs)
                 (cl-var (n) (var! (extract (car its) 1) n id (extract (car its) 3)))
                 (else y #u))
               (vars-here! (cdr its) (cdr cs) id)))))
(define seq-vars! (->* (vars int) unit)
  (lambda (vs id)
    (if (null? vs)
        #u
        (begin (var! (extract (car vs) 1) (extract (car vs) 2) id (extract (car vs) 4))
               (seq-vars! (cdr vs) id)))))
;; Each shape the patterns have here, by the indices of `cs` of it, in the
;; order first written.
(define-type groups (listof (tupleof class ints) acyclic))
(define same-group? (->* (class class) bool)
  (lambda (a b)
    (tagcase a
      (cl-nil () (tagcase b (cl-nil () #t) (else y #f)))
      (cl-pair (x y) (tagcase b (cl-pair (u v) #t) (else z #f)))
      (cl-seq (x) (tagcase b (cl-seq (u) #t) (else z #f)))
      (cl-lit (n) (tagcase b (cl-lit (m) (symbol=? n m)) (else z #f)))
      (else y (leafy? b)))))
(define grouped (->* (classes int groups) groups)
  (lambda (cs k out)
    (if (null? cs)
        out
        (grouped (cdr cs) (+ k 1) (into-group (car cs) k out)))))
(define into-group (->* (class int groups) groups)
  (lambda (c k gs)
    (cond ((null? gs) (list (tuple c (the ints (list k)))))
          ((same-group? (extract (car gs) 1) c)
           (cons (tuple (extract (car gs) 1) (append (extract (car gs) 2) (the ints (list k))))
                 (cdr gs)))
          (else (cons (car gs) (into-group c k (cdr gs)))))))
(define nth-item (->* (items int) item)
  (lambda (xs i) (if (= i 0) (car xs) (nth-item (cdr xs) (- i 1)))))
(define items-at (->* (items ints) items)
  (lambda (its ks) (if (null? ks) nil (cons (nth-item its (car ks)) (items-at its (cdr ks))))))
(define members! (->* (fails items groups int cx) ints)
  (lambda (fail its gs id c)
    (if (null? gs)
        nil
        (let* ((sub (items-at its (extract (car gs) 2)))
               (m (merge fail sub nil -1 c)))
          (begin
            (set boundaries (cons (tuple m id) (get boundaries)))
            (set members (cons (tuple m (dedup-cids sub)) (get members)))
            (cons m (members! fail its (cdr gs) id c)))))))
(define dedup-cids (->* (items) ints)
  (lambda (its)
    (cond ((null? its) nil)
          ((and (not (null? (cdr its))) (= (extract (car its) 1) (extract (car (cdr its)) 1)))
           (dedup-cids (cdr its)))
          (else (cons (extract (car its) 1) (dedup-cids (cdr its)))))))
;; Part `id`, of `its` all of one shape.
(define one! (->* (fails int items classes cx) unit)
  (lambda (fail id its cs c)
    (tagcase (car cs)
      (cl-nil () (shape-set! id (sh-nil)))
      (cl-lit (n) (shape-set! id (sh-lit n)))
      (cl-pair (x y)
        (let* ((root (region id)) (base (path-of id))
               (a (merge fail (halves its cs #t) (append base (the addr (list #t))) root c))
               (d (merge fail (halves its cs #f) (append base (the addr (list #f))) root c)))
          (shape-set! id (sh-pair a d))))
      (else y #u))))
(define halves (->* (items classes bool) items)
  (lambda (its cs car?)
    (if (null? its)
        nil
        (tagcase (car cs)
          (cl-pair (a d)
            (cons (tuple (extract (car its) 1) (if car? a d) (extract (car its) 3))
                  (halves (cdr its) (cdr cs) car?)))
          (else y (halves (cdr its) (cdr cs) car?))))))
;; If `its` may be one list by ellipsis, in a list of one: its elements'
;; patterns, the pattern variables of the whole list, and whether it took
;; in patterns written one by one (`infer.rs`'s `absorbable`).
(define-type took (tupleof items vars bool bool))
(define absorbable (->* (fails items classes cx) (listof took acyclic))
  (lambda (fail its cs c)
    (if (or (not (any-list-end? cs)) (all-nil? cs))
        nil
        (let ((t (take-each fail its c (tuple (the items nil) (the vars nil) #f #f))))
          (cond
            ((null? t) nil)
            ((not (extract (car t) 4)) nil)
            ((and (extract (car t) 3)
                  (or (span-in? (extract (car its) 2) (extract c 3))
                      (unknit? (extract (car t) 1) (extract c 2))))
             nil)
            (else t))))))
(define any-list-end? (->* (classes) bool)
  (lambda (cs)
    (and (not (null? cs))
         (or (tagcase (car cs) (cl-nil () #t) (cl-seq (x) #t) (else y #f))
             (any-list-end? (cdr cs))))))
(define all-nil? (->* (classes) bool)
  (lambda (cs)
    (or (null? cs) (and (tagcase (car cs) (cl-nil () #t) (else y #f)) (all-nil? (cdr cs))))))
(define span-in? (->* (syn spans) bool)
  (lambda (s xs)
    (and (not (null? xs))
         (or (and (= (syn-start s) (extract (car xs) 1)) (= (syn-end s) (extract (car xs) 2)))
             (span-in? s (cdr xs))))))
(define take-each (->* (fails items cx took) (listof took acyclic))
  (lambda (fail its c acc)
    (if (null? its)
        (list acc)
        (let ((t (take fail (car its) c acc)))
          (if (null? t) nil (take-each fail (cdr its) c (car t)))))))
(define take (->* (fails item cx took) (listof took acyclic))
  (lambda (fail it c acc)
    (let ((cid (extract it 1)) (depth (extract it 3))
          (es (extract acc 1)) (vs (extract acc 2)) (tk (extract acc 3)) (sq (extract acc 4)))
      (tagcase (class-of fail it (extract c 1))
        (cl-nil () (list acc))
        (cl-wild () (list acc))
        (cl-seq (x)
         (list (tuple (append es (the items (list (tuple cid x (+ depth 1))))) vs tk #t)))
        (cl-var (n) (list (tuple es (append vs (the vars (list (tuple cid n 0 depth)))) tk sq)))
        (cl-pair (a d)
          (take fail (tuple cid d depth) c
                (tuple (append es (the items (list (tuple cid a depth)))) vs #t sq)))
        (cl-lit (n) nil)))))
;; Whether elements `es`' pattern variables are of syntax types known
;; that do not agree.
(define unknit? (->* (items pkinds) bool)
  (lambda (es pk)
    (let ((known (known-kinds es pk)))
      (any-disagree? known known))))
(define known-kinds (->* (items pkinds) kds)
  (lambda (es pk)
    (if (null? es)
        nil
        (let* ((s (extract (car es) 2))
               (k (if (syn-symbol? s) (pkind-of (extract (car es) 1) (syn-symbol s) pk) nil))
               (rest (known-kinds (cdr es) pk)))
          (if (and (not (null? k)) (tagcase (car k) (kd-ty (t) #t) (else y #f)))
              (cons (car k) rest)
              rest)))))
(define any-disagree? (->* (kds kds) bool)
  (lambda (as all)
    (and (not (null? as))
         (or (disagrees-any? (car as) all) (any-disagree? (cdr as) all)))))
(define disagrees-any? (->* (kd kds) bool)
  (lambda (a bs)
    (and (not (null? bs))
         (or (and (not (reconcile? a (car bs))) (not (reconcile? (car bs) a)))
             (disagrees-any? a (cdr bs))))))

;; The shape, as compared from one iteration to the next.
(define fingerprint (->* () string)
  (lambda () (string-append (ints-text (get roots)) (parts-text (- (get nparts) 1) ""))))
;; Parts `i` and those before it, onto `out`.
(define parts-text (->* (int string) string)
  (lambda (i out)
    (if (< i 0)
        out
        (parts-text (- i 1)
                    (string-append (shape-text (shape-of i)) (addr-text (path-of i))
                                   (int->string (region i)) ";" out)))))
(define shape-text (->* (shape) string)
  (lambda (sh)
    (tagcase sh
      (sh-nil () "n") (sh-pair (a d) (string-append "p" (int->string a) "," (int->string d)))
      (sh-seq (e) (string-append "s" (int->string e))) (sh-lit (n) (symbol->string n))
      (sh-leaf () "l") (sh-union (ms) (string-append "u" (ints-text ms))))))
(define ints-text (->* (ints) string)
  (lambda (is) (if (null? is) "." (string-append (int->string (car is)) " " (ints-text (cdr is))))))
(define addr-text (->* (addr) string)
  (lambda (a) (if (null? a) "/" (string-append (if (car a) "A" "D") (addr-text (cdr a))))))

;;; ------------------------------------------------------------ kinds

;; What a pattern variable's part is of: a syntax type, or a part of the
;; signature being inferred (a list by ellipsis, a `union`).
(define-datatype kd (kd-ty sty) (kd-ref int))
(define-type kds (listof kd acyclic))
(define-type pkinds (listof (tupleof int symbol kd) acyclic))
(define-type kinds (listof (tupleof int kd) acyclic))
(define kd=? (->* (kd kd) bool)
  (lambda (a b)
    (tagcase a
      (kd-ref (p) (tagcase b (kd-ref (q) (= p q)) (else y #f)))
      (kd-ty (t) (tagcase b (kd-ty (u) (sty=? t u)) (else y #f))))))
(define pkind-of (->* (int symbol pkinds) kds)
  (lambda (cid n pk)
    (cond ((null? pk) nil)
          ((and (= cid (extract (car pk) 1)) (symbol=? n (extract (car pk) 2)))
           (list (extract (car pk) 3)))
          (else (pkind-of cid n (cdr pk))))))
(define kind-at (->* (int kinds) kds)
  (lambda (p ks)
    (cond ((null? ks) nil)
          ((= p (extract (car ks) 1)) (list (extract (car ks) 2)))
          (else (kind-at p (cdr ks))))))
;; How specific a syntax type is, where a part is placed as more than one
;; (`infer.rs`'s `rank`).
(define rank (->* (kd) int)
  (lambda (k)
    (tagcase k
      (kd-ref (p) 4)
      (kd-ty (t)
        (let ((n (kind-of t)))
          (cond ((= n 1) 0) ((= n 12) 1) ((= n 5) 2) ((= n 2) 3) ((= n 0) 6) ((= n 10) 7)
                ((= n 3) 8) (else 4)))))))
;; Whether a part of syntax type `a` may be placed where `b` is too.
(define reconcile? (->* (kd kd) bool)
  (lambda (a b)
    (or (kd=? a b)
        (tagcase a
          (kd-ty (t)
            (tagcase b
              (kd-ty (u)
                (let ((x (kind-of t)) (y (kind-of u)))
                  (or (and (= x 1) (or (= y 0) (= y 2) (= y 10)))
                      (and (= x 12) (or (= y 4) (= y 0) (= y 2)))
                      (and (= x 5) (= y 0)) (and (= x 2) (= y 0)) (and (= x 0) (= y 10)))))
              (else z #f)))
          (else y #f)))))
;; One syntax type for a part placed as each of `ks` (none if none), and
;; whether some of them do not agree with it.
(define combine (->* (kds) (tupleof kds bool))
  (lambda (ks)
    (if (null? ks)
        (tuple (the kds nil) #f)
        (let ((chosen (least-ranked (cdr ks) (car ks))))
          (tuple (the kds (list chosen)) (not (all-reconciled? chosen ks)))))))
(define least-ranked (->* (kds kd) kd)
  (lambda (ks best)
    (cond ((null? ks) best)
          ((< (rank (car ks)) (rank best)) (least-ranked (cdr ks) (car ks)))
          (else (least-ranked (cdr ks) best)))))
(define all-reconciled? (->* (kd kds) bool)
  (lambda (c ks) (or (null? ks) (and (reconcile? c (car ks)) (all-reconciled? c (cdr ks))))))
;; Whether a part of syntax type `k` is placed in a scope its signature
;; says; whether one with an expression in it runs each time it is placed.
(define scoped? (->* (kd) bool)
  (lambda (k)
    (tagcase k
      (kd-ref (p) #t)
      (kd-ty (t)
        (let ((n (kind-of t)))
          (not (or (= n 1) (= n 12) (= n 3) (= n 4) (= n 5) (= n 13) (= n 11))))))))
(define affine? (->* (kd) bool)
  (lambda (k)
    (tagcase k
      (kd-ref (p) #t)
      (kd-ty (t)
        (let ((n (kind-of t)))
          (not (or (= n 1) (= n 12) (= n 2) (= n 5) (= n 3) (= n 4) (= n 13))))))))
;; Whether `t` has an annotation whose addresses are from outside it.
(define open? (->* (sty) bool)
  (lambda (t)
    (tagcase t
      (s-import (b x) #t) (s-export (b x) #t)
      (s-pair (a d) (or (open? a) (open? d)))
      (s-many (b) (open? b)) (s-typed (b h) (open? b))
      (else y #f))))
(define compound? (->* (sty) bool)
  (lambda (t)
    (tagcase t
      (s-pair (a d) #t) (s-mu (i) #t) (s-union (ms) #t) (s-import (b x) #t) (s-export (b x) #t)
      (s-many (b) #t) (s-typed (b h) #t) (else y #f))))

;;; ------------------------------------------------------------ what it makes

;; What each macro makes (0 an expression, 1 definitions, 2 a description),
;; by its templates (`infer.rs`'s `makes_all`): its name, its literals, its
;; clauses; each clause's macro, pattern and template.
(define-type unsigned (tupleof symbol names syns-a syn))
(define-type unsigneds (listof unsigned acyclic))
(define-type rule (tupleof int syn syn))
(define-type rules (listof rule acyclic))
(define-type makes-known (listof ints acyclic))
(define makes-all (->* (fails unsigneds rules) ints)
  (lambda (fail us rs)
    (let ((known (makes-rounds fail us rs (nones (len-us us)) (len-us us))))
      (made-or-expr known))))
(define len-us (->* (unsigneds) int)
  (lambda (us) (if (null? us) 0 (+ 1 (len-us (cdr us))))))
(define nones (->* (int) makes-known) (lambda (n) (nones-onto n nil)))
(define nones-onto (->* (int makes-known) makes-known)
  (lambda (n out) (if (= n 0) out (nones-onto (- n 1) (cons (the ints nil) out)))))
(define made-or-expr (->* (makes-known) ints)
  (lambda (ks)
   (if (null? ks) nil (cons (if (null? (car ks)) 0 (car (car ks))) (made-or-expr (cdr ks))))))
(define makes-rounds (->* (fails unsigneds rules makes-known int) makes-known)
  (lambda (fail us rs known n)
    (if (< n 0)
        known
        (let ((next (makes-round fail us rs known (nones (len-us us)))))
          (if (known=? next known) known (makes-rounds fail us rs next (- n 1)))))))
(define known=? (->* (makes-known makes-known) bool)
  (lambda (a b)
    (or (and (null? a) (null? b))
        (and (not (null? a)) (not (null? b))
             (if (null? (car a))
                 (null? (car b))
                 (and (not (null? (car b))) (= (car (car a)) (car (car b)))))
             (known=? (cdr a) (cdr b))))))
(define makes-round (->* (fails unsigneds rules makes-known makes-known) makes-known)
  (lambda (fail us rs known next)
    (if (null? rs)
        next
        (let* ((mi (extract (car rs) 1)) (t (extract (car rs) 3))
               (u (nth-unsigned us mi))
               (pv (pattern-vars-of (extract (car rs) 2) (extract u 2)))
               (k (makes-of t pv us known)))
          (if (null? k)
              (makes-round fail us (cdr rs) known next)
              (let ((j (nth-known next mi)))
                (if (and (not (null? j)) (not (= (car j) (car k))))
                    (begin
                      (fail-at fail (string-append "this template makes " (made-said (car k))
                                                   ", and another of `"
                                                   (symbol->string (extract u 1)) "`'s "
                                                   (made-said (car j)))
                               t)
                      next)
                    (makes-round fail us (cdr rs) known (set-known next mi k)))))))))
(define made-said (->* (int) string)
  (lambda (k) (cond ((= k 1) "definitions") ((= k 2) "a description") (else "an expression"))))
(define nth-unsigned (->* (unsigneds int) unsigned)
  (lambda (us i) (if (= i 0) (car us) (nth-unsigned (cdr us) (- i 1)))))
(define nth-known (->* (makes-known int) ints)
  (lambda (ks i) (if (= i 0) (car ks) (nth-known (cdr ks) (- i 1)))))
(define set-known (->* (makes-known int ints) makes-known)
  (lambda (ks i k) (if (= i 0) (cons k (cdr ks)) (cons (car ks) (set-known (cdr ks) (- i 1) k)))))
;; A pattern's names but `_`, `...`, the forms' and the literals.
(define pattern-vars-of (->* (syn names) names)
  (lambda (p lits)
    (cond ((syn-symbol? p)
           (let ((n (syn-name p)))
             (if (or (string=? n "_") (string=? n "...") (reserved? n)
                     (name-in? (syn-symbol p) lits))
                 nil
                 (list (syn-symbol p)))))
          ((null? (split p)) nil)
          (else (append (pattern-vars-of (car (split p)) lits)
                        (pattern-vars-of (nth (split p) 1) lits))))))
(define makes-of (->* (syn names unsigneds makes-known) ints)
  (lambda (t pv us known)
    (cond
      ((syn-symbol? t)
       (if (or (string=? (syn-name t) "#t") (string=? (syn-name t) "#f")) (list 0) nil))
      ((syn-nil? t) nil)
      ((null? (split t)) (list 0))
      (else
       (let ((h (car (split t))))
         (cond
           ((syn-keyword? h) (list 0))
           ((not (syn-symbol? h)) nil)
           ((name-in? (syn-symbol h) pv) nil)
           (else
            (let ((i (unsigned-index (syn-symbol h) us 0)))
              (if (>= i 0)
                  (nth-known known i)
                  (let ((m (macro-of (syn-symbol h) (get defined))))
                    (if (not (null? m))
                        (list (extract (car m) 4))
                        (head-makes (syn-name h) (proper-or-dotted t) pv us known))))))))))))
(define unsigned-index (->* (symbol unsigneds int) int)
  (lambda (n us i)
    (cond ((null? us) -1)
          ((symbol=? n (extract (car us) 1)) i)
          (else (unsigned-index n (cdr us) (+ i 1))))))
(define proper-or-dotted (->* (syn) syns-a)
  (lambda (s)
   (tagcase s (lst (items d a b x) items) (dotted (items t d a b x) items) (else y nil))))
(define head-makes (->* (string syns-a names unsigneds makes-known) ints)
  (lambda (n items pv us known)
    (cond
      ((or (string=? n "define") (string=? n "define*") (string=? n "define-rec")
           (string=? n "define-type") (string=? n "define-effect"))
       (list 1))
      ((string=? n "begin")
       (let ((each (each-makes (cdr items) pv us known)))
         (cond ((int-in? 1 each) (list 1)) ((null? each) nil) (else (list (car each))))))
      ((kernel-form? n) (list 0))
      ((type-form? n) (list 2))
      (else nil))))
(define each-makes (->* (syns-a names unsigneds makes-known) ints)
  (lambda (xs pv us known)
    (if (null? xs)
        nil
        (append (makes-of (car xs) pv us known) (each-makes (cdr xs) pv us known)))))
(define kernel-form? (->* (string) bool)
  (lambda (n) (named-in? (string->symbol n) (kernel-sigs pfail-at))))
(define named-in? (->* (symbol (listof (tupleof symbol sty) acyclic)) bool)
  (lambda (n xs)
   (and (not (null? xs)) (or (symbol=? n (extract (car xs) 1)) (named-in? n (cdr xs))))))

;;; ------------------------------------------------------------ the signature so far

;; What an iteration infers, by part (`infer.rs`'s `Sol`): each leaf's
;; syntax type, each pattern variable's, the parts `many`, the imports and
;; exports, each macro's export, and the lists by ellipsis not to take in
;; patterns written one by one.
(define-type binds-at (listof (tupleof int bind) acyclic))
(define-type sol (tupleof kinds pkinds ints binds-at binds-at binds-at spans))
(define sol-empty (->* () sol)
  (lambda () (tuple (the kinds nil) (the pkinds nil) (the ints nil) (the binds-at nil)
                    (the binds-at nil) (the binds-at nil) (the spans nil))))
(define bind-at (->* (int binds-at) (listof bind acyclic))
  (lambda (p bs)
    (cond ((null? bs) nil)
          ((= p (extract (car bs) 1)) (list (extract (car bs) 2)))
          (else (bind-at p (cdr bs))))))

;; Each macro's signature so far, from `s`: its syntax types, and each `mu`
;; made for a list by ellipsis, a `union`, or a part not known yet, by its
;; part (`infer.rs`'s `build`).
(define-type mu-parts (listof (tupleof int int) acyclic))
(define built-mus (ref mu-parts rs) (new nil))
(define build (->* (sol) stys)
  (lambda (s)
    (begin
      (set built-mus nil)
      (alloc-mus! 0 s)
      (build-roots (get roots) 0 s))))
(define alloc-mus! (->* (int sol) unit)
  (lambda (p s)
    (if (= p (get nparts))
        #u
        (begin
          (if (or (tagcase (shape-of p) (sh-seq (e) #t) (sh-union (ms) #t) (else y #f))
                  (and (leaf? p) (null? (kind-at p (extract s 1)))))
              (set built-mus (cons (tuple p (mu-new)) (get built-mus)))
              #u)
          (alloc-mus! (+ p 1) s)))))
(define mu-of (->* (int) int) (lambda (p) (car (int-assoc p (get built-mus)))))
(define build-roots (->* (ints int sol) stys)
  (lambda (rs mi s)
    (if (null? rs)
        nil
        (let* ((t (part-ty (car rs) s)) (e (bind-at mi (extract s 6))))
          (cons (if (null? e) t (s-export t (car e))) (build-roots (cdr rs) (+ mi 1) s))))))
(define part-ty (->* (int sol) sty)
  (lambda (p s)
    (let* ((base
            (tagcase (shape-of p)
              (sh-nil () (s-nil))
              (sh-lit (n) (s-literal n))
              (sh-pair (a d) (s-pair (part-ty a s) (part-ty d s)))
              (sh-leaf ()
                (let ((k (kind-at p (extract s 1))))
                  (if (null? k)
                      ;; Not known: anything, by a `mu` of its own.
                      (let ((id (mu-of p))) (begin (mu-set! id (s-data)) (s-mu id)))
                      (tagcase (car k)
                        (kd-ref (q) (s-mu (mu-of q)))
                        (kd-ty (t)
                          (if (and (compound? t) (open? t))
                              (let ((id (mu-new))) (begin (mu-set! id t) (s-mu id)))
                              t))))))
              (sh-seq (e) (seq-ty p e s))
              (sh-union (ms)
                (let ((id (mu-of p)))
                  (begin (mu-set! id (s-union (members-ty ms s))) (s-mu id))))))
           (t (if (int-in? p (extract s 3)) (s-many base) base))
           (i (bind-at p (extract s 4))))
      (if (null? i) t (s-import t (car i))))))
(define members-ty (->* (ints sol) stys)
  (lambda (ms s)
    (if (null? ms)
        nil
        (let* ((t (part-ty (car ms) s)) (e (bind-at (car ms) (extract s 5))))
          (cons (if (null? e) t (s-export t (car e))) (members-ty (cdr ms) s))))))
;; As `seq-type` makes `(elem ...)`.
(define seq-ty (->* (int int sol) sty)
  (lambda (p e s)
    (let* ((id (mu-of p)) (t (part-ty e s)) (x (bind-at e (extract s 5)))
           (elem (cond ((not (null? x)) (s-export t (car x)))
                       ((= (kind-of t) 1) (s-export t (bind-rib (list (tuple (the addr nil) 1)))))
                       ((= (kind-of t) 12) (s-export t (bind-rib (list (tuple (the addr nil) 4)))))
                       (else t)))
           (pair (s-pair elem (s-mu id))))
      (begin
        (mu-set! id (s-union (tagcase elem
                               (s-export (b y)
                                 (list (s-export (s-nil) (bind-rib nil))
                                       (s-export pair (bind-rib (list (tuple (the addr (list #t)) 2)
                                                                      (tuple (the addr (list #f))
                                                                             2))))))
                               (else z (list (s-nil) pair)))))
        (s-mu id)))))

;;; ------------------------------------------------------------ placements

;; A pattern variable placed by a template: which, as what, in what scope,
;; whether in a `many` part, under how many ellipses.
(define-type placement (tupleof symbol sty levels bool int))
(define-type placements (listof placement acyclic))
;; Clause `cid`'s template's placements, and, if it makes definitions,
;; what of what a use gives it defines (in a list of one); none if its
;; template is refused with the signature so far.
(define-type placed (tupleof placements (listof exported acyclic)))
(define got (ref (listof placed acyclic) rs) (new nil))
(define placements-of (->* (int syn int sol) (listof placed acyclic))
  (lambda (cid template made s)
    (let ((as-names (try-placing cid template made s #t)))
      (if (null? as-names) (try-placing cid template made s #f) as-names))))
(define try-placing (->* (int syn int sol bool) (listof placed acyclic))
  (lambda (cid template made s names)
    (begin
      (set got nil)
      (let ((r (prompt parse-tag
                       (begin (set got (list (placed-as pfail-at cid template made s names)))
                              (p-ok nil))
                       (lambda (r) r))))
        (tagcase r (p-err (m x y) (the (listof placed acyclic) nil)) (p-ok (ts) (get got)))))))
;; With each pattern variable whose syntax type is not known yet taken for
;; a name (`names`), where a form takes a name or a list; else anything.
(define placed-as (->* (fails int syn int sol bool) placed)
  (lambda (fail cid template made s names)
    (begin
      (nodes-reset!)
      (let* ((ps (pvars-for cid (get found-vars) s names))
             (ty (cond ((= made 1) (s-defn)) ((= made 2) (s-type)) (else (s-expr))))
             (root (align fail 1 ps ty template -1 nil))
             (fs (walk fail root nil #f 0)))
        (tuple (placements-in fs)
               (if (= made 1)
                   (the (listof exported acyclic)
                        (list (exports-of (levels-of fail root template))))
                   nil))))))
(define pvars-for (->* (int vars sol bool) pvars)
  (lambda (cid vs s names)
    (cond
      ((null? vs) nil)
      ((= cid (extract (car vs) 1))
       (let* ((p (extract (car vs) 3)) (k (kind-at p (extract s 1)))
              (core (cond ((not (leaf? p)) (s-data))
                          ((and (not (null? k)) (tagcase (car k) (kd-ty (t) #t) (else y #f)))
                           (tagcase (car k) (kd-ty (t) t) (else y (s-data))))
                          ((and (null? k) names) (s-id))
                          (else (s-data)))))
         (cons (tuple (extract (car vs) 2)
                      (tuple core (the levels nil) #f nil (extract (car vs) 4)))
               (pvars-for cid (cdr vs) s names))))
      (else (pvars-for cid (cdr vs) s names)))))
(define placements-in (->* (found) placements)
  (lambda (fs)
    (if (null? fs)
        nil
        (let ((at (extract (car fs) 1)))
          (tagcase (node-kids at)
            (k-pvar (n)
              (cons (tuple n (node-core at) (normal (extract (car fs) 2)) (extract (car fs) 3)
                           (extract (car fs) 4))
                    (placements-in (cdr fs))))
            (else y (placements-in (cdr fs))))))))
