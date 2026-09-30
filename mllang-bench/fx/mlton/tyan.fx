;;; TYAN -- A Grobner Basis calculation for polynomials over F17, with
;;; "geobuckets" for the intermediate results.
;;;
;;; Original code from Thomas Yan, who has given his permission for this
;;; code be used as a benchmarking code for SML compilers; adapted from the
;;; TIL benchmark suite by Allyn Dimock (SML '97, Standard Basis Library,
;;; unreachable code commented out); modified by sweeks@sweeks.com
;;; 2001-10-03 to go in the MLton benchmark suite (the u6 list of
;;; polynomials hardwired, and a loop). The data structure for the
;;; intermediate results is described in Thomas Yan, "The Geobucket Data
;;; Structure For Polynomials", Journal Of Symbolic Computation 23(3),
;;; 285-293, 1998.
;;;
;;; From MLton's benchmark suite (benchmark/tests/tyan.sml, commit
;;; aa2fd1ad9b91), ported to FX-26. MLton's driver was not fetched; the
;;; iteration count, 3 runs of `gb u6` (`doit 3`), is this port's.
;;; Answer: the 92 lines `gb` prints for the basis, as a list of strings,
;;; from "a8b4c3 + 22 terms\n" to "g6 + 44 terms\n" (2740 terms in all
;;; beyond the leading ones).
;;;
;;; What changed:
;;; - `Word.andb`, `Word.<<` and `Word.>>`, used only on non-negative
;;;   integers, with masks and shifts of powers of two, are the same
;;;   operations in integer arithmetic: `v << 16` is `v * 65536`, `v >> k` is
;;;   `quotient v 2^k`, `v andb 65535` is `modulo v 65536`, `v andb ~65536`
;;;   is `v - modulo v 65536`, and `n && 15` is `modulo n 16`.
;;; - One-constructor datatypes (`F.field`, `M.mono`, `P.poly`,
;;;   `HP.hpoly`, `MI.mono_ideal`) are what they box: an int, an int list, a
;;;   list of terms, an array of polys, a ref (MLton represents them so).
;;;   Tuples are products, but for a term (`F.field * M.mono`), which is a
;;;   two-field bloblet read by `term-a` and `term-m`: a procedure that
;;;   inlines one that `extract`s from a product is declined by the
;;;   register compiler (the field's position is looked up in the facts of
;;;   the form being compiled, and the inlined `extract` is not among
;;;   them), and runs as cellular code; `P.leadMono` and the like made most
;;;   of the benchmark so (reported, with a reproduction).
;;; - The structures are flattened into top-level definitions, prefixed
;;;   (`m-`, `mi-`, `p-`, `hp-`, `g-`) where names would clash. `MI`'s
;;;   operations, `Util.insert`, `Util.stripSort`, `tabulate` and
;;;   `arrayoflist` are polymorphic (`poly`), used at several types as in
;;;   SML; the Basis's `map`, `app`, `foldl`, `foldr` and `length` are
;;;   written out at each type used.
;;; - `MI.search`'s exception Found aborts to a prompt; its value is then
;;;   `!result`, as in SML (NONE if the search returns normally, which is
;;;   the only value it returns). The exceptions that mean an error
;;;   (Illegal, Impossible, DoesntDivide, Div, Tabulate, ArrayofList) abort
;;;   to a tag no prompt is for, and none is raised.
;;; - FX-26 has no output: `print` does nothing, but every string the
;;;   original prints is still made (`Int.toString`, `String.concat`,
;;;   `M.display`). `gb` returns the lines it prints for the basis, which is
;;;   the answer.

;;; ---------------------------------------------------------------- basics

(define-type ints (listof int @heap))
(define-type mono ints)
(define-type strings (listof string @heap))
(define-datatype relation (less) (equal) (greater))
(define-datatype (option (t type)) (none) (some t))

;; An uncaught exception: an abort to a tag no prompt is for.
(define fail-tag (prompt-tag unit string pure @f) (make-continuation-prompt-tag))
(define* fail (subr (goto @f) (string) void)
  (lambda (s) (abort-current-continuation fail-tag s)))

;; Everything the benchmark does, and MI.search's Found, which aborts to @x.
(define-effect base (maxeff (read @heap) (write @heap) (alloc @heap) spin (read @globals) (goto @f)))
(define-effect teff (maxeff base (goto @x)))
(define found-tag (prompt-tag unit unit base @x) (make-continuation-prompt-tag))

(define print (subr pure (string) unit) (lambda (s) #u))

(define* imax (subr pure (int int) int) (lambda (a b) (if (> a b) a b)))

;; The Word operations, on non-negative integers.
(define* lshift16 (subr pure (int) int) (lambda (v) (* v 65536)))
(define* rshift16 (subr pure (int) int) (lambda (v) (quotient v 65536)))
(define* andb-65535 (subr pure (int) int) (lambda (v) (modulo v 65536)))
(define* andb-not-65535 (subr pure (int) int) (lambda (v) (- v (modulo v 65536))))

(define len
  (poly ((t type)) (subr teff ((listof t @heap)) int))
  (plambda ((t type))
    (lambda (l)
      (letrec ((loop (subr teff ((listof t @heap) int) int)
                 (lambda (l n) (if (null? l) n (loop (cdr l) (+ n 1))))))
        (loop l 0)))))

(define tabulate
  (poly ((t type)) (subr teff (int (subr teff (int) t)) (arrayof t @heap)))
  (plambda ((t type))
    (lambda (i f)
      (if (<= i 0)
          (fail "Tabulate")
          (let ((a (the (arrayof t @heap) (make-array i (f 0)))))
            (letrec ((tabify (subr teff (int) (arrayof t @heap))
                       (lambda (j) (if (< j i) (begin (array-set! a j (f j)) (tabify (+ j 1))) a))))
              (tabify 1)))))))

(define arrayoflist
  (poly ((t type)) (subr teff ((listof t @heap)) (arrayof t @heap)))
  (plambda ((t type))
    (lambda (l)
      (if (null? l)
          (fail "ArrayofList")
          (let ((a (the (arrayof t @heap) (make-array (+ (len (cdr l)) 1) (car l)))))
            (letrec ((al (subr teff ((listof t @heap) int) (arrayof t @heap))
                       (lambda (l i) (if (null? l) a (begin (array-set! a i (car l)) (al (cdr l) (+ i 1)))))))
              (al (cdr l) 1)))))))

;;; ---------------------------------------------------------------- Util

;; arr[i] := obj :: arr[i]; extend non-empty arr if necessary
(define util-insert
  (poly ((t type)) (subr teff (t int (arrayof (listof t @heap) @heap)) (arrayof (listof t @heap) @heap)))
  (plambda ((t type))
    (lambda (obj i arr)
      (let ((len (array-length arr)))
        (if (< i len)
            (begin (array-set! arr i (the (listof t @heap) (cons obj (array-ref arr i)))) arr)
            (let ((arr2 (the (arrayof (listof t @heap) @heap) (make-array (imax (+ i 1) (+ len len)) nil))))
              (letrec ((copy (subr teff (int) (arrayof (listof t @heap) @heap))
                         (lambda (j)
                           (if (= j -1)
                               (begin (array-set! arr2 i (the (listof t @heap) (cons obj nil))) arr2)
                               (begin (array-set! arr2 j (array-ref arr j)) (copy (- j 1)))))))
                (copy (- len 1)))))))))

;; given compare and array a, return list of contents of a sorted in
;; ascending order, with duplicates stripped out; which copy of a duplicate
;; remains is random.  NOTE that a is modified.
(define strip-sort
  (poly ((t type)) (subr teff ((subr teff (t t) relation) (arrayof t @heap)) (listof t @heap)))
  (plambda ((t type))
    (lambda (compare a)
      (letrec ((swap (subr teff (int int) unit)
                 (lambda (i j)
                   (let ((ai (array-ref a i)))
                     (begin (array-set! a i (array-ref a j)) (array-set! a j ai)))))
               ;; sort all a[k], 0<=i<=k<j<=length a
               (s (subr teff (int int (listof t @heap)) (listof t @heap))
                 (lambda (i j acc)
                   (if (= i j)
                       acc
                       (let ((pivot (array-ref a (quotient (+ i j) 2))))
                         (letrec ((partition (subr teff (int int int) (productof (lo int) (hi int)))
                                    (lambda (lo k hi)
                                      (if (= k hi)
                                          (product (lo lo) (hi hi))
                                          (tagcase (compare pivot (array-ref a k))
                                            (less () (begin (swap lo k) (partition (+ lo 1) (+ k 1) hi)))
                                            (equal () (partition lo (+ k 1) hi))
                                            (greater () (begin (swap k (- hi 1)) (partition lo k (- hi 1)))))))))
                           (let ((lh (partition i i j)))
                             (s i (extract lh lo) (the (listof t @heap) (cons pivot (s (extract lh hi) j acc)))))))))))
        (s 0 (array-length a) nil)))))

;;; ---------------------------------------------------------------- F

(define p int 17)
;; (F n), always 0<=n<p: the int itself.
(define f-one int 1)
(define* f-coerce-int (subr pure (int) int) (lambda (n) (modulo n p)))
(define* f-add (subr pure (int int) int) (lambda (n m) (let ((k (+ n m))) (if (>= k p) (- k p) k))))
(define* f-subtract (subr pure (int int) int) (lambda (n m) (if (>= n m) (- n m) (+ (- n m) p))))
(define* f-negate (subr pure (int) int) (lambda (n) (if (= n 0) 0 (- p n))))
(define* f-multiply (subr pure (int int) int) (lambda (n m) (modulo (* n m) p)))
(define* f-reciprocal (subr teff (int) int)
  (lambda (n)
    (if (= n 0)
        (fail "Div")
        ;; consider euclid gcd alg on (a,b) starting with a=p, b=n.
        ;; if maintain a = a1 n + a2 p, b = b1 n + b2 p, a>b,
        ;; then when 1 = a = a1 n + a2 p, have a1 = inverse of n mod p
        ;; note that it is not necessary to keep a2, b2 around.
        (letrec ((gcd (subr teff (int int int int) int)
                   (lambda (a a1 b b1)
                     (if (= b 1)
                         ;; by continued fraction expansion, 0<|b1|<p
                         (if (< b1 0) (+ p b1) b1)
                         (let ((q (quotient a b)))
                           (gcd b b1 (- a (* q b)) (- a1 (* q b1))))))))
          (gcd p 0 n 1)))))
(define* f-is-zero (subr pure (int) bool) (lambda (n) (= n 0)))

;;; ---------------------------------------------------------------- M (MONO)

;; encode (var,pwr) as a long word: hi word is var, lo word is pwr
;; masks 0xffff for pwr, mask ~0x10000 for var, rshift 16 for var
;; note that encoded pairs u, v have same var if u>=v, u andb ~0x10000<v

(define-type var-pwr (productof (v int) (p int)))
(define-type var-pwrs (listof var-pwr @heap))

(define m-one mono nil)
(define* m-x-i (subr (alloc @heap) (int) mono) (lambda (v) (the mono (cons (+ (lshift16 v) 1) nil))))
(define* m-explode (subr teff (mono) var-pwrs)
  (lambda (l)
    (if (null? l)
        nil
        (the var-pwrs (cons (product (v (rshift16 (car l))) (p (andb-65535 (car l)))) (m-explode (cdr l)))))))
(define* m-implode (subr teff (var-pwrs) mono)
  (lambda (l)
    (if (null? l)
        nil
        (the mono (cons (+ (lshift16 (extract (car l) v)) (extract (car l) p)) (m-implode (cdr l)))))))

(define* m-deg (subr teff (mono) int)
  (lambda (l)
    (letrec ((d (subr teff (ints int) int)
               (lambda (l n) (if (null? l) n (d (cdr l) (+ (andb-65535 (car l)) n))))))
      (d l 0))))

;; x^k > y^l if x>k or x=y and k>l
(define* m-compare (subr teff (mono mono) relation)
  (lambda (m m2)
    (cond ((null? m) (if (null? m2) (equal) (less)))
          ((null? m2) (greater))
          ((= (car m) (car m2)) (m-compare (cdr m) (cdr m2)))
          ((< (car m) (car m2)) (less))
          (else (greater)))))

(define* char-list-append (subr teff ((listof char @heap) (listof char @heap)) (listof char @heap))
  (lambda (xs ys) (if (null? xs) ys (the (listof char @heap) (cons (car xs) (char-list-append (cdr xs) ys))))))

(define* m-display (subr teff (mono) string)
  (lambda (l)
    (letrec ((dv (subr pure (int) char)
               (lambda (v) (if (< v 26)
                               (integer->char (+ v (char->integer #\a)))
                               (integer->char (+ (- v 26) (char->integer #\A))))))
             (d (subr teff (int (listof char @heap)) (listof char @heap))
               (lambda (vv acc)
                 (let ((v (rshift16 vv)) (p (andb-65535 vv)))
                   (if (= p 1)
                       (the (listof char @heap) (cons (dv v) acc))
                       (the (listof char @heap)
                         (cons (dv v) (char-list-append (the (listof char @heap) (string->list (int->string p))) acc)))))))
             ;; fold d l [] (List.foldl)
             (fold (subr teff (ints (listof char @heap)) (listof char @heap))
               (lambda (l acc) (if (null? l) acc (fold (cdr l) (d (car l) acc))))))
      (list->string (fold l nil)))))

(define* m-multiply (subr teff (mono mono) mono)
  (lambda (m m2)
    (letrec ((mul (subr teff (ints ints) ints)
               (lambda (m m2)
                 (cond ((null? m) m2)
                       ((null? m2) m)
                       (else
                        (let* ((u (car m)) (us (cdr m)) (v (car m2)) (vs (cdr m2))
                               (uu (andb-not-65535 u)))
                          (if (= uu (andb-not-65535 v))
                              (let ((w (+ u (andb-65535 v))))
                                (if (= uu (andb-not-65535 w))
                                    (the ints (cons w (mul us vs)))
                                    (fail (string-append "Mono.multiply overflow: "
                                            (string-append (m-display m)
                                              (string-append ", " (m-display m2)))))))
                              (if (> u v)
                                  (the ints (cons u (mul us m2)))
                                  ;; u<v
                                  (the ints (cons v (mul m vs)))))))))))
      (mul m m2))))

(define* m-lcm (subr teff (mono mono) mono)
  (lambda (m m2)
    (cond ((null? m) m2)
          ((null? m2) m)
          (else
           (let ((u (car m)) (us (cdr m)) (v (car m2)) (vs (cdr m2)))
             (if (>= u v)
                 (if (< (andb-not-65535 u) v)
                     (the mono (cons u (m-lcm us vs)))
                     (the mono (cons u (m-lcm us m2))))
                 (if (< (andb-not-65535 v) u)
                     (the mono (cons v (m-lcm us vs)))
                     (the mono (cons v (m-lcm m vs))))))))))

(define* m-try-divide (subr teff (mono mono) (option mono))
  (lambda (m m2)
    (letrec ((rev (subr teff (ints ints) ints)
               (lambda (l acc) (if (null? l) acc (rev (cdr l) (the ints (cons (car l) acc))))))
             (d (subr teff (ints ints ints) (option mono))
               (lambda (m m2 q)
                 (cond ((null? m2) (some (rev q m)))
                       ((null? m) (none))
                       (else
                        (let ((u (car m)) (us (cdr m)) (v (car m2)) (vs (cdr m2)))
                          (cond ((< u v) (none))
                                ((= (andb-not-65535 u) (andb-not-65535 v))
                                 (if (= u v)
                                     (d us vs q)
                                     (d us vs (the ints (cons (- u (andb-65535 v)) q)))))
                                (else (d us m2 (the ints (cons u q)))))))))))
      (d m m2 nil))))

(define* m-divide (subr teff (mono mono) mono)
  (lambda (m m2)
    (tagcase (m-try-divide m m2)
      (some (q) q)
      (none () (fail "DoesntDivide")))))

;;; ---------------------------------------------------------------- MI (MONO_IDEAL)

;; trie:
;; index first by increasing order of vars
;; children listed in increasing degree order
;; tag, encoded (var,pwr) and children
(define-datatype (mono-trie (t type))
  (mt (option t) (listof (productof (vp int) (child (mono-trie t))) @heap)))
(define-type (children (t type)) (listof (productof (vp int) (child (mono-trie t))) @heap))
;; int maxDegree = least degree > all elements
(define-type (mono-ideal (t type)) (ref (productof (d int) (trie (mono-trie t))) @heap))
(define-type (tagged (t type)) (productof (m mono) (a t)))

(define* rev-ints (subr teff (ints ints) ints)
  (lambda (l acc) (if (null? l) acc (rev-ints (cdr l) (the ints (cons (car l) acc))))))

(define mi-empty-trie
  (poly ((t type)) (subr (read @globals) () (mono-trie t)))
  (plambda ((t type)) (lambda () (mt (none) (the (children t) nil)))))
(define mi-make-empty
  (poly ((t type)) (subr teff () (mono-ideal t)))
  (plambda ((t type)) (lambda () (the (mono-ideal t) (new (product (d 0) (trie (mi-empty-trie))))))))

(define* mi-encode (subr pure (int int) int) (lambda (var pwr) (+ (lshift16 var) pwr)))
(define* grab-var (subr pure (int) int) (lambda (vp) (andb-not-65535 vp)))
(define* grab-pwr (subr pure (int) int) (lambda (vp) (andb-65535 vp)))
(define* smaller-var (subr pure (int int) bool) (lambda (vp vp2) (< vp (andb-not-65535 vp2))))

(define mi-search
  (poly ((t type)) (subr teff ((mono-ideal t) mono) (option (tagged t))))
  (plambda ((t type))
    (lambda (mi m0)
      (let* ((mt (extract (get mi) trie))
             (result (the (ref (option (tagged t)) @heap) (new (none)))))
        ;; s works on remaining input mono, current output mono, tag, trie
        (letrec ((s (subr teff (ints ints (mono-trie t)) (option (tagged t)))
                   (lambda (m1 m trie)
                     (tagcase trie
                       (mt (tag kids)
                         (tagcase tag
                           (some (a)
                             (begin (set result (some (product (m m) (a a))))
                                    (abort-current-continuation found-tag #u)))
                           (none () (s2 m1 m kids)))))))
                 (s2 (subr teff (ints ints (children t)) (option (tagged t)))
                   (lambda (m1 m trie)
                     (if (or (null? m1) (null? trie))
                         (none)
                         (let ((vp1 (car m1)) (rest1 (cdr m1))
                               (vp (extract (car trie) vp)) (child (extract (car trie) child))
                               (children (cdr trie)))
                           (cond ((smaller-var vp1 vp) (s2 rest1 m trie))
                                 ((= (grab-pwr vp) 0) (begin (s m1 m child) (s2 m1 m children)))
                                 ((smaller-var vp vp1) (none))
                                 ((<= vp vp1) (begin (s rest1 (the ints (cons vp m)) child) (s2 m1 m children)))
                                 (else (none))))))))
          (begin
            (prompt found-tag (begin (s (rev-ints m0 nil) nil mt) #u) (lambda (u) #u))
            (get result)))))))

(define* map-encode (subr teff (var-pwrs) ints)
  (lambda (l)
    (if (null? l)
        nil
        (the ints (cons (mi-encode (extract (car l) v) (extract (car l) p)) (map-encode (cdr l)))))))

;; assume m is a new generator, i.e. not a multiple of an existing one
(define mi-insert
  (poly ((t type)) (subr teff ((mono-ideal t) mono t) unit))
  (plambda ((t type))
    (lambda (mi m a)
      (let* ((dmt (get mi)) (d (extract dmt d)) (mt0 (extract dmt trie)))
        (letrec ((i (subr teff (ints (mono-trie t)) (mono-trie t))
                   (lambda (vps mt0)
                     (tagcase mt0
                       (mt (a2 trie)
                         (if (null? vps)
                             (tagcase a2
                               (some (x) (fail "MONO_IDEAL.insert duplicate"))
                               (none () (mt (some a) trie)))
                             (let ((vp (car vps)) (m (cdr vps)))
                               (if (null? trie)
                                   (mt a2 (the (children t) (cons (product (vp vp) (child (i m (mi-empty-trie)))) nil)))
                                   (let ((vp2 (extract (car trie) vp)))
                                     (letrec ((j (subr teff ((children t)) (children t))
                                                (lambda (kids)
                                                  (if (null? kids)
                                                      (the (children t) (cons (product (vp vp) (child (i m (mi-empty-trie)))) nil))
                                                      (let ((vp2 (extract (car kids) vp)) (child (extract (car kids) child)))
                                                        (cond ((< vp vp2)
                                                               (the (children t) (cons (product (vp vp) (child (i m (mi-empty-trie)))) kids)))
                                                              ((= vp vp2)
                                                               (the (children t) (cons (product (vp vp2) (child (i m child))) (cdr kids))))
                                                              (else
                                                               (the (children t) (cons (car kids) (j (cdr kids)))))))))))
                                       (cond ((smaller-var vp vp2)
                                              (mt a2 (list (product (vp (grab-var vp)) (child (mt (none) trie)))
                                                           (product (vp vp) (child (i m (mi-empty-trie)))))))
                                             ((smaller-var vp2 vp)
                                              (i (the ints (cons (grab-var vp2) (cons vp m))) mt0))
                                             (else (mt a2 (j trie))))))))))))))
          (set mi (product (d (imax d (m-deg m)))
                           (trie (i (rev-ints (map-encode (m-explode m)) nil) mt0)))))))))

(define mi-make-ideal
  (poly ((t type)) (subr teff ((listof (tagged t) @heap)) (mono-ideal t)))
  (plambda ((t type))
    (lambda (orig-ms)
      (if (null? orig-ms)
          (mi-make-empty)
          (letrec ((ins (subr teff ((tagged t) (arrayof (listof (tagged t) @heap) @heap)) (arrayof (listof (tagged t) @heap) @heap))
                     (lambda (ma arr) (util-insert ma (m-deg (extract ma m)) arr)))
                   ;; revfold ins ms (List.foldr)
                   (revfold (subr teff ((listof (tagged t) @heap) (arrayof (listof (tagged t) @heap) @heap)) (arrayof (listof (tagged t) @heap) @heap))
                     (lambda (l b) (if (null? l) b (ins (car l) (revfold (cdr l) b))))))
            (let* ((msa (arrayoflist orig-ms))
                   (ms (strip-sort (lambda ((x (tagged t)) (y (tagged t))) (m-compare (extract x m) (extract y m))) msa))
                   (buckets (revfold ms (the (arrayof (listof (tagged t) @heap) @heap) (make-array 0 nil))))
                   (n (array-length buckets))
                   (mi (the (mono-ideal t) (mi-make-empty))))
              (letrec ((redundant (subr teff ((tagged t)) bool)
                         (lambda (x) (tagcase (mi-search mi (extract x m)) (none () #f) (some (y) #t))))
                       (filter (subr teff ((listof (tagged t) @heap) (listof (tagged t) @heap)) unit)
                         (lambda (xx l)
                           (if (null? xx)
                               (letrec ((app (subr teff ((listof (tagged t) @heap)) unit)
                                          (lambda (l) (if (null? l) #u (begin (mi-insert mi (extract (car l) m) (extract (car l) a)) (app (cdr l)))))))
                                 (app l))
                               (if (redundant (car xx))
                                   (filter (cdr xx) l)
                                   (filter (cdr xx) (the (listof (tagged t) @heap) (cons (car xx) l)))))))
                       (sort (subr teff (int) (mono-ideal t))
                         (lambda (i)
                           (if (>= i n)
                               mi
                               (begin
                                 (filter (array-ref buckets i) nil)
                                 (array-set! buckets i nil)
                                 (sort (+ i 1)))))))
                (sort 0))))))))

(define mi-fold
  (poly ((t type) (b type)) (subr teff ((subr teff ((tagged t) b) b) (mono-ideal t) b) b))
  (plambda ((t type) (b type))
    (lambda (g mi init)
      (letrec ((f (subr teff (b ints (mono-trie t)) b)
                 (lambda (acc m trie)
                   (tagcase trie
                     (mt (tag children)
                       (tagcase tag
                         (none () (f2 acc m children))
                         (some (a) (f2 (g (product (m m) (a a)) acc) m children)))))))
               (f2 (subr teff (b ints (children t)) b)
                 (lambda (acc m children)
                   (if (null? children)
                       acc
                       (let ((vp (extract (car children) vp)) (child (extract (car children) child)))
                         (if (= (grab-pwr vp) 0)
                             (f2 (f acc m child) m (cdr children))
                             (f2 (f acc (the ints (cons vp m)) child) m (cdr children))))))))
        (f init nil (extract (get mi) trie))))))

;;; ---------------------------------------------------------------- counts

(define* log2 (subr spin (int) int)
  (lambda (n)
    (letrec ((log (subr spin (int int) int) (lambda (n l) (if (<= n 1) l (log (quotient n 2) (+ 1 l))))))
      (log n 0))))
(define max-left (ref int @heap) (new 0))
(define max-right (ref int @heap) (new 0))
(define counts (arrayof (arrayof int @heap) @heap) (tabulate 20 (lambda ((i int)) (the (arrayof int @heap) (make-array 20 0)))))

(define* pair (subr teff (int int) unit)
  (lambda (l r)
    (let ((l (log2 l)) (r (log2 r)))
      (begin
        (set max-left (imax (get max-left) l))
        (set max-right (imax (get max-right) r))
        (let ((a (array-ref counts l)))
          (array-set! a r (+ (array-ref a r) 1)))))))

;;; ---------------------------------------------------------------- P (POLY)

;; (F.field * M.mono) list, in descending mono order
;; A term, F.field * M.mono: a bloblet, not a product (see the header).
(define-type term (bloblet (fields int mono) @heap))
(define mk-term (subr (alloc @heap) (int mono) term) (lambda (a m) (the term (make-bloblet 0 a m))))
(define term-a (subr (read @heap) (term) int) (lambda (t) (bloblet-ref t 0)))
(define term-m (subr (read @heap) (term) mono) (lambda (t) (bloblet-ref t 1)))
(define-type poly (listof term @heap))
(define-type polys (listof poly @heap))

(define p-zero poly nil)
(define* p-coerce (subr (alloc @heap) (int mono) poly) (lambda (a m) (the poly (cons (mk-term a m) nil))))
(define* p-cons (subr (alloc @heap) (term poly) poly) (lambda (am p) (the poly (cons am p))))
(define* p-length (subr teff (poly) int) (lambda (p) (len p)))

(define* p-neg (subr teff (poly) poly)
  (lambda (p)
    (if (null? p)
        nil
        (the poly (cons (mk-term (f-negate (term-a (car p))) (term-m (car p))) (p-neg (cdr p)))))))
(define* p-plus (subr teff (poly poly) poly)
  (lambda (p1 p2)
    (cond ((null? p1) p2)
          ((null? p2) p1)
          (else
           (let ((a (term-a (car p1))) (m (term-m (car p1))) (ms (cdr p1))
                 (b (term-a (car p2))) (n (term-m (car p2))) (ns (cdr p2)))
             (tagcase (m-compare m n)
               (less () (the poly (cons (car p2) (p-plus p1 ns))))
               (greater () (the poly (cons (car p1) (p-plus ms p2))))
               (equal ()
                 (let ((c (f-add a b)))
                   (if (f-is-zero c)
                       (p-plus ms ns)
                       (the poly (cons (mk-term c m) (p-plus ms ns))))))))))))
(define* p-minus (subr teff (poly poly) poly)
  (lambda (p1 p2)
    (cond ((null? p1) (p-neg p2))
          ((null? p2) p1)
          (else
           (let ((a (term-a (car p1))) (m (term-m (car p1))) (ms (cdr p1))
                 (b (term-a (car p2))) (n (term-m (car p2))) (ns (cdr p2)))
             (tagcase (m-compare m n)
               (less () (the poly (cons (mk-term (f-negate b) n) (p-minus p1 ns))))
               (greater () (the poly (cons (car p1) (p-minus ms p2))))
               (equal ()
                 (let ((c (f-subtract a b)))
                   (if (f-is-zero c)
                       (p-minus ms ns)
                       (the poly (cons (mk-term c m) (p-minus ms ns))))))))))))
(define* p-term-mult (subr teff (int mono poly) poly)
  (lambda (a m p)
    (if (null? p)
        nil
        (the poly (cons (mk-term (f-multiply a (term-a (car p))) (m-multiply m (term-m (car p))))
                        (p-term-mult a m (cdr p)))))))

(define* p-add (subr teff (poly poly) poly)
  (lambda (p1 p2) (begin (pair (p-length p1) (p-length p2)) (p-plus p1 p2))))
(define* p-subtract (subr teff (poly poly) poly)
  (lambda (p1 p2) (begin (pair (p-length p1) (p-length p2)) (p-minus p1 p2))))
(define* p-spair (subr teff (int mono poly int mono poly) poly)
  (lambda (a m f b n g)
    (begin (pair (p-length f) (p-length g))
           (p-minus (p-term-mult a m f) (p-term-mult b n g)))))
(define* p-scalar-mult (subr teff (int poly) poly)
  (lambda (a p)
    (if (null? p)
        nil
        (the poly (cons (mk-term (f-multiply a (term-a (car p))) (term-m (car p)))
                        (p-scalar-mult a (cdr p)))))))
(define* p-is-zero (subr pure (poly) bool) (lambda (p) (null? p)))

;; these should only be called if there is a leading term, i.e. poly<>0
(define* p-lead-mono (subr teff (poly) mono)
  (lambda (p) (if (null? p) (fail "POLY.leadMono") (term-m (car p)))))
(define* p-lead-coeff (subr teff (poly) int)
  (lambda (p) (if (null? p) (fail "POLY.leadCoeff") (term-a (car p)))))
(define* p-rest (subr teff (poly) poly)
  (lambda (p) (if (null? p) (fail "POLY.rest") (cdr p))))
(define-type lead-rest (productof (lead term) (rest poly)))
(define* p-lead-and-rest (subr teff (poly) lead-rest)
  (lambda (p) (if (null? p) (fail "POLY.leadAndRest") (product (lead (car p)) (rest (cdr p))))))
(define* p-deg (subr teff (poly) int)
  (lambda (p) (if (null? p) (fail "POLY.deg on zero poly") (m-deg (term-m (car p))))))   ; homogeneous poly
(define* p-num-terms (subr teff (poly) int) (lambda (p) (len p)))

;;; ---------------------------------------------------------------- HP

(define-type hpoly (arrayof poly @heap))

(define* hp-log (subr spin (int) int)
  (lambda (n)
    (letrec ((log (subr spin (int int) int) (lambda (n l) (if (< n 8) l (log (quotient n 4) (+ 1 l))))))
      (log n 0))))
(define* hp-make (subr teff (poly) hpoly)
  (lambda (p)
    (let ((l (hp-log (p-num-terms p))))
      (tabulate (+ l 1) (lambda ((i int)) (if (= i l) p p-zero))))))
(define* hp-add (subr teff (poly hpoly) hpoly)
  (lambda (p ps)
    (let ((l (hp-log (p-num-terms p))))
      (if (>= l (array-length ps))
          (let ((n (array-length ps)))
            (tabulate (+ n n) (lambda ((i int)) (if (< i n) (array-ref ps i) (if (= i l) p p-zero)))))
          (let ((p (p-add p (array-ref ps l))))
            (if (= l (hp-log (p-num-terms p)))
                (begin (array-set! ps l p) ps)
                (begin (array-set! ps l p-zero) (hp-add p ps))))))))

(define-type amh (productof (a int) (m mono) (hp hpoly)))
(define* hp-lead-and-rest (subr teff (hpoly) (option amh))
  (lambda (ps)
    (let ((n (array-length ps)))
      (letrec ((lar (subr teff (mono ints int) (option amh))
                 (lambda (m indices i)
                   (if (>= i n)
                       (lar2 m indices)
                       (let ((p (array-ref ps i)))
                         (cond ((p-is-zero p) (lar m indices (+ i 1)))
                               ((null? indices) (lar (p-lead-mono p) (the ints (cons i nil)) (+ i 1)))
                               (else
                                (tagcase (m-compare m (p-lead-mono p))
                                  (less () (lar (p-lead-mono p) (the ints (cons i nil)) (+ i 1)))
                                  (equal () (lar m (the ints (cons i indices)) (+ i 1)))
                                  (greater () (lar m indices (+ i 1))))))))))
               (lar2 (subr teff (mono ints) (option amh))
                 (lambda (m indices)
                   (if (null? indices)
                       (none)
                       (letrec ((extract-lead (subr teff (int) int)
                                  (lambda (i)
                                    (let ((lr (p-lead-and-rest (array-ref ps i))))
                                      (begin (array-set! ps i (extract lr rest))
                                             (term-a (extract lr lead))))))
                                ;; revfold (fn (j,b) => F.add(extract j,b)) is (extract i)
                                (revfold (subr teff (ints int) int)
                                  (lambda (l b) (if (null? l) b (f-add (extract-lead (car l)) (revfold (cdr l) b))))))
                         (let ((a (let ((first (extract-lead (car indices)))) (revfold (cdr indices) first))))
                           (if (f-is-zero a)
                               (lar m-one nil 0)
                               (some (product (a a) (m m) (hp ps))))))))))
        (lar m-one nil 0)))))

;;; ---------------------------------------------------------------- G

(define auto-reduce (ref bool @heap) (new #t))
(define max-deg (ref int @heap) (new 10000))
(define maybe-pairs (ref int @heap) (new 0))
(define prime-pairs (ref int @heap) (new 0))
(define used-pairs (ref int @heap) (new 0))
(define new-gens (ref int @heap) (new 0))

(define* reset (subr teff () unit)
  (lambda () (begin (set maybe-pairs 0) (set prime-pairs 0) (set used-pairs 0) (set new-gens 0))))
(define* inc (subr teff ((ref int @heap)) unit) (lambda (r) (set r (+ (get r) 1))))

(define-type gen-ideal (mono-ideal (ref poly @heap)))

(define* g-reduce (subr teff (poly gen-ideal) poly)
  (lambda (f mi)
    (if (p-is-zero f)
        f
        ;; use accumulator and reverse at end?
        (letrec ((r (subr teff (hpoly) poly)
                   (lambda (hp)
                     (tagcase (hp-lead-and-rest hp)
                       (none () nil)
                       (some (amh)
                         (let ((a (extract amh a)) (m (extract amh m)) (hp (extract amh hp)))
                           (tagcase (mi-search mi m)
                             (none () (the poly (cons (mk-term a m) (r hp))))
                             (some (mp)
                               (r (hp-add (p-term-mult (f-negate a) (m-divide m (extract mp m)) (get (extract mp a))) hp))))))))))
          (r (hp-make f))))))

;; assume f<>0
(define* mk-monic (subr teff (poly) poly)
  (lambda (f) (p-scalar-mult (f-reciprocal (p-lead-coeff f)) f)))

(define-type pair-ideal (mono-ideal (productof (m mono) (g poly))))
(define-type (buckets (t type)) (arrayof (listof t @heap) @heap))
(define-type fgs (arrayof poly @heap))

;; given monic h, a monomial ideal mi of m's tagged with g's representing
;; an ideal (g1,...,gn): a poly g is represented as (lead mono m,rest of g).
;; update pairs to include new s-pairs induced by h on g's:
;; 1) compute minimal gi1...gik so that <gij:h's> generate <gi:h's>, i.e.
;;    compute monomial ideal for gi:h's tagged with gi
;; 2) toss out gij's whose lead mono is rel. prime to h's lead mono (why?)
;; 3) put (h,gij) pairs into degree buckets: for h,gij with lead mono's m,m'
;;    deg(h,gij) = deg lcm(m,m') = deg (lcm/m) + deg m = deg (m':m) + deg m
;; 4) store list of pairs (h,g1),...,(h,gn) as vector (h,g1,...,gn)
(define* add-pairs (subr teff (poly gen-ideal (buckets fgs)) (buckets fgs))
  (lambda (h mi pairs)
    (let* ((m (p-lead-mono h))
           (d (m-deg m))
           (tag (lambda ((mg (tagged (ref poly @heap))) (quots (listof (tagged (productof (m mono) (g poly))) @heap)))
                  (begin
                    (inc maybe-pairs)
                    (the (listof (tagged (productof (m mono) (g poly))) @heap)
                      (cons (product (m (m-divide (m-lcm m (extract mg m)) m))
                                     (a (product (m (extract mg m)) (g (get (extract mg a))))))
                            quots)))))
           ;; recall mm = m':m
           (insert (lambda ((x (tagged (productof (m mono) (g poly)))) (arr (buckets poly)))
                     (let ((mm (extract x m)) (m2 (extract (extract x a) m)) (g2 (extract (extract x a) g)))
                       (tagcase (m-compare m2 mm)
                         (equal () (begin (inc prime-pairs) arr))   ; rel. prime
                         (else r
                           (begin (inc used-pairs)
                                  (util-insert (p-cons (mk-term f-one m2) g2) (+ (m-deg mm) d) arr)))))))
           (buckets (mi-fold insert
                             (mi-make-ideal (mi-fold tag mi (the (listof (tagged (productof (m mono) (g poly))) @heap) nil)))
                             (the (buckets poly) (make-array 0 nil)))))
      (letrec ((ins (subr teff (int (buckets fgs)) (buckets fgs))
                 (lambda (i pairs)
                   (if (= i -1)
                       pairs
                       (let ((gs (array-ref buckets i)))
                         (if (null? gs)
                             (ins (- i 1) pairs)
                             (ins (- i 1) (util-insert (arrayoflist (the polys (cons h gs))) i pairs))))))))
        (ins (- (array-length buckets) 1) pairs)))))

(define* string-concat (subr teff (strings) string)
  (lambda (l) (if (null? l) "" (string-append (car l) (string-concat (cdr l))))))
(define* strings-append (subr teff (strings strings) strings)
  (lambda (xs ys) (if (null? xs) ys (the strings (cons (car xs) (strings-append (cdr xs) ys))))))
(define* pr (subr teff (strings) unit)
  (lambda (l) (print (string-concat (strings-append l (the strings (cons "\n" nil)))))))

(define* num-pairs (subr teff ((listof fgs @heap) int) int)
  (lambda (ps n) (if (null? ps) n (num-pairs (cdr ps) (+ (- n 1) (array-length (car ps)))))))

(define* grobner (subr teff (polys) gen-ideal)
  (lambda (fs0)
    (letrec ((revfold (subr teff (polys (buckets poly)) (buckets poly))
               (lambda (l b) (if (null? l) b (util-insert (car l) (p-deg (car l)) (revfold (cdr l) b))))))
      (let* ((fs (revfold fs0 (the (buckets poly) (make-array 0 nil))))
             ;; pairs at least as long as fs, so done when done w/ all pairs
             (pairs (the (ref (buckets fgs) @heap) (new (make-array (array-length fs) nil))))
             (mi (the gen-ideal (mi-make-empty)))
             (new-deg-gens (the (ref (listof (ref poly @heap) @heap) @heap) (new nil)))
             ;; add and maybe auto-reduce new monic generator h
             (add-gen
              (if (not (get auto-reduce))
                  (lambda ((h poly)) (mi-insert mi (p-lead-mono h) (the (ref poly @heap) (new (p-rest h)))))
                  (lambda ((h poly))
                    (let* ((lr (p-lead-and-rest h))
                           (m (term-m (extract lr lead)))
                           (rh (extract lr rest)))
                      (letrec ((auto-reduce (subr teff (poly) poly)
                                 (lambda (f)
                                   (if (p-is-zero f)
                                       f
                                       (let* ((lr (p-lead-and-rest f))
                                              (a (term-a (extract lr lead)))
                                              (m2 (term-m (extract lr lead)))
                                              (rf (extract lr rest)))
                                         (tagcase (m-compare m m2)
                                           (less () (p-cons (mk-term a m2) (auto-reduce rf)))
                                           (equal () (p-subtract rf (p-scalar-mult a rh)))
                                           (greater () f))))))
                               (app (subr teff ((listof (ref poly @heap) @heap)) unit)
                                 (lambda (l) (if (null? l) #u (begin (set (car l) (auto-reduce (get (car l)))) (app (cdr l)))))))
                        (let ((rrh (the (ref poly @heap) (new rh))))
                          (begin
                            (mi-insert mi (p-lead-mono h) rrh)
                            (app (get new-deg-gens))
                            (set new-deg-gens (the (listof (ref poly @heap) @heap) (cons rrh (get new-deg-gens)))))))))))
             (tasksleft (the (ref int @heap) (new 0))))
        (letrec ((feedback (subr teff () unit)
                   (lambda ()
                     (let ((n (get tasksleft)))
                       (begin
                         (if (= (modulo n 16) 0) (print (int->string n)) #u)
                         (print ".")
                         (set tasksleft (- n 1))))))
                 (try (subr teff (poly) unit)
                   (lambda (h)
                     (begin
                       (feedback)
                       (let ((h (g-reduce h mi)))
                         (if (p-is-zero h)
                             #u
                             (let ((h (mk-monic h)))
                               (begin
                                 (print "#")
                                 (set pairs (add-pairs h mi (get pairs)))
                                 (add-gen h)
                                 (inc new-gens))))))))
                 (try-pairs (subr teff (fgs) unit)
                   (lambda (fgs)
                     (let* ((lr (p-lead-and-rest (array-ref fgs 0)))
                            (a (term-a (extract lr lead)))
                            (m (term-m (extract lr lead)))
                            (f (extract lr rest)))
                       (letrec ((try-pair (subr teff (int) unit)
                                  (lambda (i)
                                    (if (= i 0)
                                        #u
                                        (let* ((lr (p-lead-and-rest (array-ref fgs i)))
                                               (b (term-a (extract lr lead)))
                                               (n (term-m (extract lr lead)))
                                               (g (extract lr rest))
                                               (k (m-lcm m n)))
                                          (begin
                                            (try (p-spair b (m-divide k m) f a (m-divide k n) g))
                                            (try-pair (- i 1))))))))
                         (try-pair (- (array-length fgs) 1))))))
                 (app-try-pairs (subr teff ((listof fgs @heap)) unit)
                   (lambda (l) (if (null? l) #u (begin (try-pairs (car l)) (app-try-pairs (cdr l))))))
                 (app-try (subr teff (polys) unit)
                   (lambda (l) (if (null? l) #u (begin (try (car l)) (app-try (cdr l))))))
                 (gb (subr teff (int) gen-ideal)
                   (lambda (d)
                     (if (>= d (array-length (get pairs)))
                         mi
                         ;; note: i nullify entries to reclaim space
                         (begin
                           (pr (list "DEGREE " (int->string d) " with "
                                     (int->string (num-pairs (array-ref (get pairs) d) 0)) " pairs "
                                     (if (>= d (array-length fs)) "0" (int->string (len (array-ref fs d))))
                                     " generators to do"))
                           (set tasksleft (num-pairs (array-ref (get pairs) d) 0))
                           (if (>= d (array-length fs))
                               #u
                               (set tasksleft (+ (get tasksleft) (len (array-ref fs d)))))
                           (if (> d (get max-deg))
                               #u
                               (begin
                                 (reset)
                                 (set new-deg-gens nil)
                                 (app-try-pairs (array-ref (get pairs) d))
                                 (array-set! (get pairs) d nil)
                                 (if (>= d (array-length fs))
                                     #u
                                     (begin (app-try (array-ref fs d)) (array-set! fs d nil)))
                                 (pr (list "maybe " (int->string (get maybe-pairs)) " prime "
                                           (int->string (get prime-pairs))
                                           " using " (int->string (get used-pairs))
                                           "; found " (int->string (get new-gens))))))
                           (gb (+ d 1)))))))
          (gb 0))))))

;;; ---------------------------------------------------------------- parsing

;; grammar:
;;  dig  ::= 0 | ... | 9
;;  var  ::= a | ... | z | A | ... | Z
;;  sign ::= + | -
;;  nat  ::= dig | nat dig
;;  mono ::=  | var mono | var num mono
;;  term ::= nat mono | mono
;;  poly ::= term | sign term | poly sign term
(define-datatype pchar (dig int) (var int) (sign int))
(define-type pchars (listof pchar @heap))

(define* char->pchar (subr teff (char) pchar)
  (lambda (ch)
    (let ((och (char->integer ch)))
      (cond ((and (<= (char->integer #\0) och) (<= och (char->integer #\9))) (dig (- och (char->integer #\0))))
            ((and (<= (char->integer #\a) och) (<= och (char->integer #\z))) (var (- och (char->integer #\a))))
            ((and (<= (char->integer #\A) och) (<= och (char->integer #\Z))) (var (+ (- och (char->integer #\A)) 26)))
            ((= och (char->integer #\+)) (sign 1))
            ((= och (char->integer #\-)) (sign -1))
            (else (fail (string-append "bad ch in poly: " (char->string ch))))))))

(define-type n-rest (productof (n int) (l pchars)))
(define* nat (subr teff (int pchars) n-rest)
  (lambda (n l)
    (if (null? l)
        (product (n n) (l l))
        (tagcase (car l)
          (dig (d) (nat (+ (* n 10) d) (cdr l)))
          (else c (product (n n) (l l)))))))
(define-type m-rest (productof (m mono) (l pchars)))
(define* parse-mono (subr teff (mono pchars) m-rest)
  (lambda (m l)
    (if (null? l)
        (product (m m) (l l))
        (tagcase (car l)
          (var (v)
            (let ((l2 (cdr l)))
              (if (null? l2)
                  (parse-mono (m-multiply (m-x-i v) m) l2)
                  (tagcase (car l2)
                    (dig (d)
                      (let ((nl (nat d (cdr l2))))
                        (parse-mono (m-multiply (m-implode (the var-pwrs (cons (product (v v) (p (extract nl n))) nil))) m)
                                    (extract nl l))))
                    (else c (parse-mono (m-multiply (m-x-i v) m) l2))))))
          (else c (product (m m) (l l)))))))
(define-type t-rest (productof (t term) (l pchars)))
(define* parse-term (subr teff (pchars) t-rest)
  (lambda (l)
    (let* ((nl (if (null? l)
                   (product (n 1) (l l))
                   (tagcase (car l) (dig (d) (nat d (cdr l))) (else c (product (n 1) (l l))))))
           (ml (parse-mono m-one (extract nl l))))
      (product (t (mk-term (f-coerce-int (extract nl n)) (extract ml m))) (l (extract ml l))))))
(define* parse-poly-chars (subr teff (poly pchars) poly)
  (lambda (p l)
    (if (null? l)
        p
        (let* ((sl (tagcase (car l)
                     (sign (s) (product (s (f-coerce-int s)) (l (cdr l))))
                     (else c (product (s f-one) (l l)))))
               (tl (parse-term (extract sl l)))
               (a (term-a (extract tl t)))
               (m (term-m (extract tl t))))
          (parse-poly-chars (p-add (p-coerce (f-multiply (extract sl s) a) m) p) (extract tl l))))))
(define* map-char (subr teff ((listof char @heap)) pchars)
  (lambda (l) (if (null? l) nil (the pchars (cons (char->pchar (car l)) (map-char (cdr l)))))))
(define* parse-poly (subr teff (string) poly)
  (lambda (s) (parse-poly-chars p-zero (map-char (the (listof char @heap) (string->list s))))))

;;; ---------------------------------------------------------------- main

(define* grab (subr teff (gen-ideal) polys)
  (lambda (mi)
    (mi-fold (lambda ((mg (tagged (ref poly @heap))) (l polys))
               (the polys (cons (p-cons (mk-term f-one (extract mg m)) (get (extract mg a))) l)))
             mi
             (the polys nil))))

;; The lines `gb` prints, one per polynomial of the basis.
(define* gb (subr teff (polys) strings)
  (lambda (fs)
    (let* ((g (grobner fs))
           (fs (grab g)))
      (letrec ((info (subr teff (poly) string)
                 (lambda (f)
                   (let ((s (string-concat (list (m-display (p-lead-mono f))
                                                 " + " (int->string (- (p-num-terms f) 1))
                                                 " terms\n"))))
                     (begin (print s) s))))
               (app (subr teff (polys) strings)
                 (lambda (l) (if (null? l) nil (let ((s (info (car l)))) (the strings (cons s (app (cdr l)))))))))
        (app fs)))))

(set max-deg 1000000)

(define* map-parse-poly (subr teff (strings) polys)
  (lambda (l) (if (null? l) nil (the polys (cons (parse-poly (car l)) (map-parse-poly (cdr l)))))))

(define* doit (subr teff (int) strings)
  (lambda (n)
    (let ((u6 (map-parse-poly
                (list "abcdef-g6" "a+b+c+d+e+f" "ab+bc+cd+de+ef+fa"
                      "abc+bcd+cde+def+efa+fab"
                      "abcd+bcde+cdef+defa+efab+fabc"
                      "abcde+bcdef+cdefa+defab+efabc+fabcd")))
          (result (the (ref strings @heap) (new nil))))
      (letrec ((loop (subr teff (int) strings)
                 (lambda (n) (if (= n 0) (get result) (begin (set result (gb u6)) (loop (- n 1)))))))
        (loop n)))))

;; The input, where no compiler can fold it: a global, which a later
;; definition may replace.
(define iterations int 3)
(doit iterations)
