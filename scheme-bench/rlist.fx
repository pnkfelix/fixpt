;;; RLIST -- Random-access list benchmark for (scheme rlist).
;;;
;;; From Larceny's R7RS benchmarks (test/Benchmarking/R7RS/src/rlist.scm),
;;; ported to FX-26. Larceny's input: 5 iterations of (go 7).
;;; Answer: ((x0 x1 x2 x3 x4 x5 x6)).
;;;
;;; FX-26 has no (scheme rlist), so SRFI 101's random-access lists are
;;; written here, after Larceny's (David Van Horn's reference
;;; implementation, lib/SRFI/srfi/%3a101.sls): a list of complete binary
;;; trees of skew-binary sizes, each tree kept with its size. Polymorphic
;;; in the element type, as there; `rmap` and `rfor-each` in the effect of
;;; the procedure they are given too. What differs, and why:
;;; - Representation. Larceny's `kons` is a record (size, tree, rest) and
;;;   its `node` a record (val, left, right), with a leaf the element
;;;   itself, told from a node by `node?`. FX-26 has no untagged union:
;;;   here a random-access list is a frozen list (`acyclic`) of frozen
;;;   pairs (size . tree), and a tree a sum, `(leaf x)` or `(node (val
;;;   left right))`. So a leaf costs an object where Larceny's costs none,
;;;   a node two where Larceny's costs one, and a `kons` two, where
;;;   Larceny's costs one. (Pairs, not products: a procedure that uses
;;;   `extract` has no native code yet, and runs as cellular code.)
;;; - `ra:car+cdr` returns its two values as a pair (one more object);
;;;   `ra:car` and `ra:cdr` each call it and take one, as Larceny's do.
;;; - `ra:foldl/1` and `ra:foldr/1`, made by `make-foldl` and
;;;   `make-foldr`, are written out for the one `cons` each is given
;;;   (`ra:cons` for `append` and `reverse`, `cons` for `rlist->list`).
;;; - `half`, an arithmetic shift right, is `quotient` by 2, the same for
;;;   the sizes it is given (positive).
;;; - `rlist?` (`ra:list?`) walks the spine, as there. `requal?` asks it of
;;;   both arguments at every step, as there; on the symbols in the lists
;;;   it is #f at once, and `requal?` is `equal?`, `symbol=?`: that case is
;;;   `requal-symbol?`.
;;; - `rmember`'s `same?` is `requal?`, the one the benchmark passes.
;;; - `(map rlist->list (rlist->list …))`: the two fused, one pass.

(define-type (tree (t type))
  (sumof (leaf t) (node (productof (val t) (left (tree t)) (right (tree t))))))
(define-type (kons (t type)) (pairof int (tree t) acyclic))
(define-type (rl (t type)) (listof (kons t) acyclic))
(define-type (car+cdr (t type)) (pairof t (rl t) acyclic))

(define* half (subr pure (int) int) (lambda (n) (quotient n 2)))

(define* tree-val
  (poly ((t type)) (subr pure ((tree t)) t))
  (plambda ((t type))
    (lambda (t) (tagcase t (node (v l r) v) (leaf x x)))))

(define* tree-map
  (poly ((a type) (b type) (e effect)) (subr (maxeff e spin) ((subr e (a) b) (tree a)) (tree b)))
  (plambda ((a type) (b type) (e effect))
    (lambda (f t)
      (tagcase t
        (node (v l r)
          (let* ((v2 (f v)) (l2 (tree-map f l)) (r2 (tree-map f r)))
            (sum node (product (val v2) (left l2) (right r2)))))
        (leaf x (sum leaf (f x)))))))

(define* tree-for-each
  (poly ((a type) (e effect)) (subr (maxeff e spin) ((subr e (a) unit) (tree a)) unit))
  (plambda ((a type) (e effect))
    (lambda (f t)
      (tagcase t
        (node (v l r) (begin (f v) (tree-for-each f l) (tree-for-each f r)))
        (leaf x (f x))))))

(define* tree-ref/a
  (poly ((t type)) (subr spin ((tree t) int int) t))
  (plambda ((t type))
    (lambda (t i mid)
      (cond ((= i 0) (tree-val t))
            ((<= i mid)
             (tagcase t
               (node (v l r) (tree-ref/a l (- i 1) (half (- mid 1))))
               (leaf x x)))           ; never: a leaf's index is 0
            (else
             (tagcase t
               (node (v l r) (tree-ref/a r (- (- i mid) 1) (half (- mid 1))))
               (leaf x x)))))))

(define* tree-ref
  (poly ((t type)) (subr spin (int (tree t) int) t))
  (plambda ((t type))
    (lambda (size t i)
      (if (= i 0)
          (tree-val t)
          (tree-ref/a t i (half (- size 1)))))))

(define* ra:cons
  (poly ((t type)) (subr pure (t (rl t)) (rl t)))
  (plambda ((t type))
    (lambda (x ls)
      (if (not (null? ls))
          (let ((s (car (car ls))))
            (if (and (not (null? (cdr ls)))
                     (= (car (car (cdr ls))) s))
                (cons (cons (+ 1 (+ s s))
                               (sum node (product (val x)
                                                        (left (cdr (car ls)))
                                                        (right (cdr (car (cdr ls)))))))
                      (cdr (cdr ls)))
                (cons (cons 1 (sum leaf x)) ls)))
          (cons (cons 1 (sum leaf x)) ls)))))

(define* ra:car+cdr
  (poly ((t type)) (subr pure ((rl t)) (car+cdr t)))
  (plambda ((t type))
    (lambda (p)
      (let ((k (car p)))
        (tagcase (cdr k)
          (node (v l r)
            (let ((s* (half (car k))))
              (cons v
                    (cons (cons s* l)
                          (cons (cons s* r)
                                (cdr p))))))
          (leaf x (cons x (cdr p))))))))

(define* ra:car
  (poly ((t type)) (subr pure ((rl t)) t))
  (plambda ((t type)) (lambda (p) (car (ra:car+cdr p)))))

(define* ra:cdr
  (poly ((t type)) (subr pure ((rl t)) (rl t)))
  (plambda ((t type)) (lambda (p) (cdr (ra:car+cdr p)))))

(define* ra:list?
  (poly ((t type)) (subr spin ((rl t)) bool))
  (plambda ((t type))
    (lambda (x) (or (null? x) (ra:list? (cdr x))))))

(define* ra:length
  (poly ((t type)) (subr spin ((rl t)) int))
  (plambda ((t type))
    (lambda (ls)
      (letrec ((recr (subr spin ((rl t)) int)
                 (lambda (ls) (if (null? ls) 0 (+ (car (car ls)) (recr (cdr ls)))))))
        (if (ra:list? ls) (recr ls) 0)))))  ; (assert (ra:list? ls))

;; (ra:foldr/1 ra:cons l2 l1)
(define* ra:append
  (poly ((t type)) (subr spin ((rl t) (rl t)) (rl t)))
  (plambda ((t type))
    (lambda (l1 l2)
      (if (null? l1) l2 (ra:cons (ra:car l1) (ra:append (ra:cdr l1) l2))))))

;; (ra:foldl/1 ra:cons ra:null ls)
(define* ra:reverse
  (poly ((t type)) (subr spin ((rl t)) (rl t)))
  (plambda ((t type))
    (lambda (ls)
      (letrec ((f (subr (maxeff spin (read (globals ra:cons ra:car ra:cdr ra:car+cdr half))) ((rl t) (rl t)) (rl t))
                 (lambda (empty ls) (if (null? ls) empty (f (ra:cons (ra:car ls) empty) (ra:cdr ls))))))
        (f nil ls)))))

(define* ra:list-tail
  (poly ((t type)) (subr spin ((rl t) int) (rl t)))
  (plambda ((t type))
    (lambda (xs j) (if (= j 0) xs (ra:list-tail (ra:cdr xs) (- j 1))))))

(define* ra:list-ref
  (poly ((t type)) (subr spin ((rl t) int) t))
  (plambda ((t type))
    (lambda (xs j)
      (let ((s (car (car xs))))
        (if (< j s)
            (tree-ref s (cdr (car xs)) j)
            (ra:list-ref (cdr xs) (- j s)))))))

(define* ra:map
  (poly ((a type) (b type) (e effect)) (subr (maxeff e spin) ((subr e (a) b) (rl a)) (rl b)))
  (plambda ((a type) (b type) (e effect))
    (lambda (f ls)
      (if (null? ls)
          nil
          (let* ((t2 (tree-map f (cdr (car ls))))
                 (r2 (ra:map f (cdr ls))))
            (cons (cons (car (car ls)) t2) r2))))))

(define* ra:for-each
  (poly ((a type) (e effect)) (subr (maxeff e spin) ((subr e (a) unit) (rl a)) unit))
  (plambda ((a type) (e effect))
    (lambda (f ls)
      (if (null? ls)
          #u
          (begin (tree-for-each f (cdr (car ls)))
                 (ra:for-each f (cdr ls)))))))

;; (ra:foldr/1 cons '() x)
(define* rlist->list
  (poly ((t type)) (subr (maxeff (alloc @heap) spin) ((rl t)) (listof t @heap)))
  (plambda ((t type))
    (lambda (x) (if (null? x) nil (cons (ra:car x) (rlist->list (ra:cdr x)))))))

;;; The benchmark.

(define-type syms (rl symbol))
(define-type sets (rl syms))

(define* riota (subr spin (int) (rl int))
  (lambda (n)
    (letrec ((loop (subr (maxeff spin (read (globals ra:cons))) (int (rl int)) (rl int))
               (lambda (n r)
                 (if (= n 0)
                     r
                     (let ((n-1 (- n 1)))
                       (loop n-1 (ra:cons n-1 r)))))))
      (loop n nil))))

(define* rconcatenate (subr spin ((rl sets)) sets)
  (lambda (rs)
    (if (null? rs)
        nil
        (ra:append (ra:car rs) (rconcatenate (ra:cdr rs))))))

(define* rtake (subr spin (syms int) syms)
  (lambda (r i)
    (letrec ((loop (subr (maxeff spin (read (globals ra:cons ra:list-ref tree-ref tree-ref/a tree-val half))) (int syms) syms)
               (lambda (i r2)
                 (if (= i 0)
                     r2
                     (let ((i-1 (- i 1)))
                       (loop i-1 (ra:cons (ra:list-ref r i-1) r2)))))))
      (loop i nil))))

(define* rdrop (subr spin (syms int) syms)
  (lambda (r i) (ra:list-tail r i)))

(define* rfilter
  (poly ((e effect)) (subr (maxeff e (read @heap) (write @heap) (alloc @heap) spin) ((subr e (syms) bool) sets) sets))
  (plambda ((e effect))
    (lambda (pred r)
      (let ((r2 (the (ref sets @heap) (new nil))))
        (begin
          (ra:for-each (lambda ((x syms))
                         (if (pred x)
                             (set r2 (ra:cons x (get r2)))
                             #u))
                       (ra:reverse r))
          (get r2))))))

;; requal? on two symbols: neither is an rlist, so equal?.
(define* requal-symbol? (subr pure (symbol symbol) bool)
  (lambda (x y) (symbol=? x y)))

(define* requal? (subr spin (syms syms) bool)
  (lambda (x y)
    (cond ((or (not (ra:list? x))
               (not (ra:list? y)))
           #f)                          ; (equal? x y): never, here
          ((null? x)
           (null? y))
          ((null? y)
           (null? x))
          ((requal-symbol? (ra:car x) (ra:car y))
           (requal? (ra:cdr x) (ra:cdr y)))
          (else
           #f))))

(define* rmember (subr spin (syms sets) bool)
  (lambda (x r)
    (cond ((null? r) #f)
          ((requal? x (ra:car r)) #t)
          (else (rmember x (ra:cdr r))))))

(define* symbols (subr spin (int) syms)
  (lambda (n)
    (ra:map (lambda ((s string)) (string->symbol s))
            (ra:map (lambda ((s string)) (string-append "x" s))
                    (ra:map (lambda ((i int)) (int->string i))
                            (riota n))))))

(define* powerset (subr spin (syms) sets)
  (lambda (universe)
    (if (null? universe)
        (ra:cons (the syms nil) nil)
        (let* ((x (ra:car universe))
               (u2 (ra:cdr universe))
               (pu2 (powerset u2)))
          (ra:append pu2
                     (ra:map (lambda ((y syms)) (ra:cons x y))
                             pu2))))))

(define* permutations (subr spin (syms) sets)
  (lambda (universe)
    (if (null? universe)
        (ra:cons (the syms nil) nil)
        (let* ((x (ra:car universe))
               (u2 (ra:cdr universe))
               (perms2 (permutations u2)))
          (rconcatenate
           (ra:map (lambda ((perm syms))
                     (ra:map (lambda ((i int))
                               (ra:append (rtake perm i)
                                          (ra:cons x (rdrop perm i))))
                             (riota (+ 1 (ra:length perm)))))
                   perms2))))))

(define* go (subr (maxeff (read @heap) (write @heap) (alloc @heap) spin) (int) (listof (listof symbol @heap) @heap))
  (lambda (n)
    (let* ((universe (symbols n))
           (subsets (powerset universe))
           (perms (permutations universe)))
      (letrec ((map-rlist->list (subr (maxeff (alloc @heap) spin (read (globals rlist->list ra:car ra:cdr ra:car+cdr half)))
                                      (sets) (listof (listof symbol @heap) @heap))
                 (lambda (x)
                   (if (null? x)
                       nil
                       (cons (rlist->list (ra:car x)) (map-rlist->list (ra:cdr x)))))))
        (map-rlist->list
         (rfilter (lambda ((perm syms))
                    (rmember perm subsets))
                  perms))))))

;; The inputs, where no compiler can fold them (Larceny's `hide`): globals,
;; which a later definition may replace.
(define input1 int 7)
(define iterations int 5)

(define* run (subr (maxeff (read @heap) (write @heap) (alloc @heap) spin)
                   (int (listof (listof symbol @heap) @heap)) (listof (listof symbol @heap) @heap))
  (lambda (i result) (if (= i 0) result (run (- i 1) (go input1)))))
(run iterations nil)
