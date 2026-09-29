;;; SORTS -- "Test bench for sorting algorithms": in its default mode
;;; (-teststd), the standard library's List.sort, List.stable_sort,
;;; Array.sort and Array.stable_sort, on ints and records of 25 lengths up
;;; to 2323, each result checked to be sorted and a permutation of its
;;; input.
;;;
;;; From OCaml's classic test programs (testsuite/tests/misc/sorts.ml, ocaml
;;; commit 7da997d28b1a), ported to FX-26. The original, run with no
;;; arguments, prints what it tests (the 198 lines of sorts.reference). The
;;; port does those tests `iterations` = 1 time, as the original does, and
;;; where the original prints, it hashes: each character printed updates
;;; h := (h * 131 + code) mod 1000000007, from h = 0 each time. Answer:
;;; 810716784, which is that hash of the reference output's 10054
;;; characters (which it matches only if no test failed).
;;;
;;; What the port changes, and why:
;;; - Only the default mode is ported: the other modes' 70-odd sorting
;;;   procedures (the bulk of the file) and timers are not run by it, and
;;;   are left out.
;;; - The sorts tested are OCaml's standard library's, not in the file:
;;;   they are written here as the library has them (List.stable_sort, a
;;;   merge sort that List.sort also is; Array.sort, a heap sort with
;;;   ternary sift-down; Array.stable_sort, a merge sort with insertion
;;;   sort below 6 elements).
;;; - Random: the data comes from OCaml's `Random` (LXM, seeded through
;;;   MD5 by `full_init`), whose 64-bit wrapping arithmetic FX-26's 61-bit
;;;   checked integers do not have. The port's `Random` is a Park-Miller
;;;   generator (x := x * 48271 mod (2^31 - 1)) with the same interface:
;;;   `init`, `full_init` of an array (folded into the state), `bits` (30
;;;   bits) and `int` (OCaml's rejection of the top, kept). So the numbers
;;;   differ from OCaml's; the output does not depend on them.
;;; - `bytes` fields are strings (the records are never changed), and
;;;   `compare` on them is `string-compare`, OCaml's order (bytes, then
;;;   length). OCaml builds a record's fields right to left; so does
;;;   `mkrec1` here, so the numbers drawn go to the same fields.
;;; - The polymorphic `=` of `chkgen` (an element found) is an `eq`
;;;   argument, and `a = mkconst n` is `int-array=?`. `raise Exit` is an
;;;   abort to a prompt tag. `chkgen` also catches Invalid_argument (an
;;;   index out of bounds), which FX-26 cannot catch; it happens only for
;;;   a result that is not sorted, and would stop the port with an error.
;;; - The `aux` records are products; `lc` and `ac`, polymorphic in OCaml,
;;;   are made for ints and for records (`lc-int`, `lc-rec`, ...). `test`
;;;   already takes its sort twice, once for ints and once for records;
;;;   so does `test1` here. The `try ... with e -> Exception e` around a
;;;   sort is left out: FX-26 cannot catch a sort's errors, and these
;;;   raise none.
;;; - `for` and `while` loops are local recursive procedures.

(define-effect so (maxeff (read @heap) (write @heap) (alloc @heap) spin (goto @e) (read @globals)))
(define-effect so-body (maxeff (read @heap) (write @heap) (alloc @heap) spin (read @globals)))

(define-type ints (arrayof int @heap))

;;;; Printing, hashed.

(define out-hash (ref int @heap) (new 0))

(define* print-string (subr so (string) unit)
  (lambda (s)
    (letrec ((loop (subr so (int) unit)
               (lambda (i)
                 (if (< i (string-length s))
                     (begin
                       (set out-hash (modulo (+ (* (get out-hash) 131) (char->integer (string-ref s i)))
                                             1000000007))
                       (loop (+ i 1)))
                     #u))))
      (loop 0))))

;; printf "%5d"
(define* print-int5 (subr so (int) unit)
  (lambda (n)
    (letrec ((pad (subr so (string) string)
               (lambda (s) (if (< (string-length s) 5) (pad (string-append " " s)) s))))
      (print-string (pad (int->string n))))))

;;;; Random, as OCaml's interface has it (see above).

(define random-state (ref int @heap) (new 1))

(define* random-full-init (subr so (ints) unit)
  (lambda (seed)
    (letrec ((fold (subr so (int int) int)
               (lambda (i s)
                 (if (< i (array-length seed))
                     (fold (+ i 1) (modulo (+ (* s 31) (modulo (array-ref seed i) 1000000007)) 2147483647))
                     s))))
      (let ((s (fold 0 (+ 12345 (array-length seed)))))
        (set random-state (if (= s 0) 1 s))))))

(define* random-init (subr so (int) unit)
  (lambda (seed) (random-full-init (make-array 1 seed))))

(define* random-bits (subr so () int)
  (lambda ()
    (begin
      (set random-state (modulo (* (get random-state) 48271) 2147483647))
      (modulo (get random-state) 1073741824))))

(define* random-int (subr so (int) int)
  (lambda (bound)
    (let* ((r (random-bits))
           (v (modulo r bound)))
      (if (> (- r v) (+ (- 1073741823 bound) 1))
          (random-int bound)
          v))))

;;;; The standard library's sorts.

(define* list-length (poly ((a type)) (subr so ((listof a @heap)) int))
  (lambda (l) (if (null? l) 0 (+ 1 (list-length (cdr l))))))

(define* list-rev-append (poly ((a type)) (subr so ((listof a @heap) (listof a @heap)) (listof a @heap)))
  (lambda (l1 l2) (if (null? l1) l2 (list-rev-append (cdr l1) (cons (car l1) l2)))))

;; List.stable_sort (and List.sort)
(define* list-stable-sort (poly ((a type)) (subr so ((subr so (a a) int) (listof a @heap)) (listof a @heap)))
  (lambda (cmp l)
    (letrec ((rev-merge (subr so ((listof a @heap) (listof a @heap) (listof a @heap)) (listof a @heap))
               (lambda (l1 l2 accu)
                 (cond ((null? l1) (list-rev-append l2 accu))
                       ((null? l2) (list-rev-append l1 accu))
                       (else
                        (let ((h1 (car l1)) (t1 (cdr l1)) (h2 (car l2)) (t2 (cdr l2)))
                          (if (<= (cmp h1 h2) 0)
                              (rev-merge t1 l2 (cons h1 accu))
                              (rev-merge l1 t2 (cons h2 accu))))))))
             (rev-merge-rev (subr so ((listof a @heap) (listof a @heap) (listof a @heap)) (listof a @heap))
               (lambda (l1 l2 accu)
                 (cond ((null? l1) (list-rev-append l2 accu))
                       ((null? l2) (list-rev-append l1 accu))
                       (else
                        (let ((h1 (car l1)) (t1 (cdr l1)) (h2 (car l2)) (t2 (cdr l2)))
                          (if (> (cmp h1 h2) 0)
                              (rev-merge-rev t1 l2 (cons h1 accu))
                              (rev-merge-rev l1 t2 (cons h2 accu))))))))
             (sort (subr so (int (listof a @heap)) (productof (s (listof a @heap)) (tl (listof a @heap))))
               (lambda (n l)
                 (cond
                   ((and (= n 2) (not (null? l)) (not (null? (cdr l))))
                    (let ((x1 (car l)) (x2 (car (cdr l))) (tl (cdr (cdr l))))
                      (product (s (if (<= (cmp x1 x2) 0)
                                      (cons x1 (cons x2 nil))
                                      (cons x2 (cons x1 nil))))
                               (tl tl))))
                   ((and (= n 3) (not (null? l)) (not (null? (cdr l))) (not (null? (cdr (cdr l)))))
                    (let ((x1 (car l)) (x2 (car (cdr l))) (x3 (car (cdr (cdr l)))) (tl (cdr (cdr (cdr l)))))
                      (product (s (if (<= (cmp x1 x2) 0)
                                      (cond ((<= (cmp x2 x3) 0) (cons x1 (cons x2 (cons x3 nil))))
                                            ((<= (cmp x1 x3) 0) (cons x1 (cons x3 (cons x2 nil))))
                                            (else (cons x3 (cons x1 (cons x2 nil)))))
                                      (cond ((<= (cmp x1 x3) 0) (cons x2 (cons x1 (cons x3 nil))))
                                            ((<= (cmp x2 x3) 0) (cons x2 (cons x3 (cons x1 nil))))
                                            (else (cons x3 (cons x2 (cons x1 nil)))))))
                               (tl tl))))
                   (else
                    (let* ((n1 (quotient n 2))
                           (n2 (- n n1))
                           (r1 (rev-sort n1 l))
                           (r2 (rev-sort n2 (extract r1 tl))))
                      (product (s (rev-merge-rev (extract r1 s) (extract r2 s) nil))
                               (tl (extract r2 tl))))))))
             (rev-sort (subr so (int (listof a @heap)) (productof (s (listof a @heap)) (tl (listof a @heap))))
               (lambda (n l)
                 (cond
                   ((and (= n 2) (not (null? l)) (not (null? (cdr l))))
                    (let ((x1 (car l)) (x2 (car (cdr l))) (tl (cdr (cdr l))))
                      (product (s (if (> (cmp x1 x2) 0)
                                      (cons x1 (cons x2 nil))
                                      (cons x2 (cons x1 nil))))
                               (tl tl))))
                   ((and (= n 3) (not (null? l)) (not (null? (cdr l))) (not (null? (cdr (cdr l)))))
                    (let ((x1 (car l)) (x2 (car (cdr l))) (x3 (car (cdr (cdr l)))) (tl (cdr (cdr (cdr l)))))
                      (product (s (if (> (cmp x1 x2) 0)
                                      (cond ((> (cmp x2 x3) 0) (cons x1 (cons x2 (cons x3 nil))))
                                            ((> (cmp x1 x3) 0) (cons x1 (cons x3 (cons x2 nil))))
                                            (else (cons x3 (cons x1 (cons x2 nil)))))
                                      (cond ((> (cmp x1 x3) 0) (cons x2 (cons x1 (cons x3 nil))))
                                            ((> (cmp x2 x3) 0) (cons x2 (cons x3 (cons x1 nil))))
                                            (else (cons x3 (cons x2 (cons x1 nil)))))))
                               (tl tl))))
                   (else
                    (let* ((n1 (quotient n 2))
                           (n2 (- n n1))
                           (r1 (sort n1 l))
                           (r2 (sort n2 (extract r1 tl))))
                      (product (s (rev-merge (extract r1 s) (extract r2 s) nil))
                               (tl (extract r2 tl)))))))))
      (let ((len (list-length l)))
        (if (< len 2) l (extract (sort len l) s))))))

;; exception Bottom of int
(define-datatype bottom-outcome (b-ok int) (b-bottom int))
(define bottom (prompt-tag bottom-outcome int so-body @e) (make-continuation-prompt-tag))

;; Array.sort
(define* array-sort (poly ((a type)) (subr so ((subr so (a a) int) (arrayof a @heap)) unit))
  (lambda (cmp a)
    (letrec ((maxson (subr so (int int) int)
               (lambda (l i)
                 (let* ((i31 (+ (+ (+ i i) i) 1))
                        (x (the (ref int @heap) (new i31))))
                   (if (< (+ i31 2) l)
                       (begin
                         (if (< (cmp (array-ref a i31) (array-ref a (+ i31 1))) 0) (set x (+ i31 1)) #u)
                         (if (< (cmp (array-ref a (get x)) (array-ref a (+ i31 2))) 0) (set x (+ i31 2)) #u)
                         (get x))
                       (if (and (< (+ i31 1) l) (< (cmp (array-ref a i31) (array-ref a (+ i31 1))) 0))
                           (+ i31 1)
                           (if (< i31 l) i31 (abort-current-continuation bottom i)))))))
             (trickledown (subr so (int int a) unit)
               (lambda (l i e)
                 (let ((j (maxson l i)))
                   (if (> (cmp (array-ref a j) e) 0)
                       (begin (array-set! a i (array-ref a j)) (trickledown l j e))
                       (array-set! a i e)))))
             (trickle (subr so (int int a) unit)
               (lambda (l i e)
                 (tagcase (prompt bottom (begin (trickledown l i e) (b-ok 0)) (lambda (i) (b-bottom i)))
                   (b-ok (z) #u)
                   (b-bottom (i) (array-set! a i e)))))
             (bubbledown (subr so (int int) int)
               (lambda (l i)
                 (let ((j (maxson l i)))
                   (begin (array-set! a i (array-ref a j)) (bubbledown l j)))))
             (bubble (subr so (int int) int)
               (lambda (l i)
                 (tagcase (prompt bottom (b-ok (bubbledown l i)) (lambda (i) (b-bottom i)))
                   (b-ok (z) z)
                   (b-bottom (i) i))))
             (trickleup (subr so (int a) unit)
               (lambda (i e)
                 (let ((father (quotient (- i 1) 3)))
                   (if (< (cmp (array-ref a father) e) 0)
                       (begin
                         (array-set! a i (array-ref a father))
                         (if (> father 0) (trickleup father e) (array-set! a 0 e)))
                       (array-set! a i e)))))
             (loop1 (subr so (int int) unit)
               (lambda (l i)
                 (if (>= i 0) (begin (trickle l i (array-ref a i)) (loop1 l (- i 1))) #u)))
             (loop2 (subr so (int) unit)
               (lambda (i)
                 (if (>= i 2)
                     (let ((e (array-ref a i)))
                       (begin
                         (array-set! a i (array-ref a 0))
                         (trickleup (bubble i 0) e)
                         (loop2 (- i 1))))
                     #u))))
      (let ((l (array-length a)))
        (begin
          (loop1 l (- (quotient (+ l 1) 3) 1))
          (loop2 (- l 1))
          (if (> l 1)
              (let ((e (array-ref a 1)))
                (begin (array-set! a 1 (array-ref a 0)) (array-set! a 0 e)))
              #u))))))

(define* array-blit (poly ((a type)) (subr so ((arrayof a @heap) int (arrayof a @heap) int int) unit))
  (lambda (src sp dst dp len)
    ;; (never overlapping here)
    (if (> len 0)
        (begin (array-set! dst dp (array-ref src sp)) (array-blit src (+ sp 1) dst (+ dp 1) (- len 1)))
        #u)))

(define cutoff int 5)

;; Array.stable_sort
(define* array-stable-sort (poly ((a type)) (subr so ((subr so (a a) int) (arrayof a @heap)) unit))
  (lambda (cmp a)
    (letrec ((merge (subr so (int int (arrayof a @heap) int int (arrayof a @heap) int) unit)
               (lambda (src1ofs src1len src2 src2ofs src2len dst dstofs)
                 (let ((src1r (+ src1ofs src1len)) (src2r (+ src2ofs src2len)))
                   (letrec ((loop (subr so (int a int a int) unit)
                              (lambda (i1 s1 i2 s2 d)
                                (if (<= (cmp s1 s2) 0)
                                    (begin
                                      (array-set! dst d s1)
                                      (let ((i1 (+ i1 1)))
                                        (if (< i1 src1r)
                                            (loop i1 (array-ref a i1) i2 s2 (+ d 1))
                                            (array-blit src2 i2 dst (+ d 1) (- src2r i2)))))
                                    (begin
                                      (array-set! dst d s2)
                                      (let ((i2 (+ i2 1)))
                                        (if (< i2 src2r)
                                            (loop i1 s1 i2 (array-ref src2 i2) (+ d 1))
                                            (array-blit a i1 dst (+ d 1) (- src1r i1)))))))))
                     (loop src1ofs (array-ref a src1ofs) src2ofs (array-ref src2 src2ofs) dstofs)))))
             (isortto (subr so (int (arrayof a @heap) int int) unit)
               (lambda (srcofs dst dstofs len)
                 (letrec ((for (subr so (int) unit)
                            (lambda (i)
                              (if (<= i (- len 1))
                                  (let ((e (array-ref a (+ srcofs i)))
                                        (j (the (ref int @heap) (new (- (+ dstofs i) 1)))))
                                    (letrec ((while (subr so () unit)
                                               (lambda ()
                                                 (if (and (>= (get j) dstofs) (> (cmp (array-ref dst (get j)) e) 0))
                                                     (begin
                                                       (array-set! dst (+ (get j) 1) (array-ref dst (get j)))
                                                       (set j (- (get j) 1))
                                                       (while))
                                                     #u))))
                                      (begin
                                        (while)
                                        (array-set! dst (+ (get j) 1) e)
                                        (for (+ i 1)))))
                                  #u))))
                   (for 0))))
             (sortto (subr so (int (arrayof a @heap) int int) unit)
               (lambda (srcofs dst dstofs len)
                 (if (<= len cutoff)
                     (isortto srcofs dst dstofs len)
                     (let* ((l1 (quotient len 2))
                            (l2 (- len l1)))
                       (begin
                         (sortto (+ srcofs l1) dst (+ dstofs l1) l2)
                         (sortto srcofs a (+ srcofs l2) l1)
                         (merge (+ srcofs l2) l1 dst (+ dstofs l1) l2 dst dstofs)))))))
      (let ((l (array-length a)))
        (if (<= l cutoff)
            (isortto 0 a 0 l)
            (let* ((l1 (quotient l 2))
                   (l2 (- l l1))
                   (t (the (arrayof a @heap) (make-array l2 (array-ref a 0)))))
              (begin
                (sortto l1 t 0 l2)
                (sortto 0 a l2 l1)
                (merge l2 l1 t 0 l2 a 0))))))))

(define* array-to-list (poly ((a type)) (subr so ((arrayof a @heap)) (listof a @heap)))
  (lambda (a)
    (letrec ((loop (subr so (int (listof a @heap)) (listof a @heap))
               (lambda (i res) (if (< i 0) res (loop (- i 1) (cons (array-ref a i) res))))))
      (loop (- (array-length a) 1) nil))))

;; Array.of_list, given the array the list was made from, which has an
;; element to fill a new array with if it is not empty.
(define* array-of-list (poly ((a type)) (subr so ((listof a @heap) (arrayof a @heap)) (arrayof a @heap)))
  (lambda (l from)
    (if (null? l)
        (if (= (array-length from) 0) from (make-array 0 (array-ref from 0)))
        (let ((a (the (arrayof a @heap) (make-array (list-length l) (car l)))))
          (letrec ((fill (subr so (int (listof a @heap)) (arrayof a @heap))
                     (lambda (i l) (if (null? l) a (begin (array-set! a i (car l)) (fill (+ i 1) (cdr l)))))))
            (fill 0 l))))))

;;;; auxiliary functions

(define* compare-int (subr pure (int int) int)
  (lambda (x y) (cond ((< x y) -1) ((> x y) 1) (else 0))))

(define* int-array=? (subr so (ints ints) bool)
  (lambda (a b)
    (and (= (array-length a) (array-length b))
         (letrec ((loop (subr so (int) bool)
                    (lambda (i)
                      (or (>= i (array-length a))
                          (and (= (array-ref a i) (array-ref b i)) (loop (+ i 1)))))))
           (loop 0)))))

(define* mkconst (subr so (int) ints) (lambda (n) (make-array n 0)))
(define* chkconst (subr so (ints int ints) bool) (lambda (rstate n a) (int-array=? a (mkconst n))))

(define* mksorted (subr so (int) ints)
  (lambda (n)
    (let ((a (the ints (make-array n 0))))
      (letrec ((for (subr so (int) ints)
                 (lambda (i) (if (<= i (- n 1)) (begin (array-set! a i i) (for (+ i 1))) a))))
        (for 0)))))
(define* chksorted (subr so (ints int ints) bool) (lambda (rstate n a) (int-array=? a (mksorted n))))

(define* mkrev (subr so (int) ints)
  (lambda (n)
    (let ((a (the ints (make-array n 0))))
      (letrec ((for (subr so (int) ints)
                 (lambda (i) (if (<= i (- n 1)) (begin (array-set! a i (- (- n 1) i)) (for (+ i 1))) a))))
        (for 0)))))
(define* chkrev (subr so (ints int ints) bool) (lambda (rstate n a) (int-array=? a (mksorted n))))

(define seed (ref int @heap) (new 0))
(define* random-reinit (subr so () unit) (lambda () (random-init (get seed))))

(define* random-get-state (subr so () ints)
  (lambda ()
    (let ((a (the ints (make-array 55 0))))
      (letrec ((for (subr so (int) unit)
                 (lambda (i) (if (<= i 54) (begin (array-set! a i (random-bits)) (for (+ i 1))) #u))))
        (begin
          (for 0)
          (random-full-init a)
          a)))))

(define* random-set-state (subr so (ints) unit) (lambda (a) (random-full-init a)))

;; exception Exit
(define exit-tag (prompt-tag bool unit so-body @e) (make-continuation-prompt-tag))

(define* chkgen (poly ((a type))
                  (subr so ((subr so (int) a) (subr so (a a) int) (subr so (a a) bool) ints int (arrayof a @heap)) bool))
  (lambda (mke cmp eq rstate n a)
    (let ((marks (the ints (make-array n -1))))
      (prompt exit-tag
        (letrec ((skipmarks (subr so (int) int)
                   (lambda (l)
                     (if (= (array-ref marks l) -1)
                         l
                         (let ((m (the (ref int @heap) (new (array-ref marks l)))))
                           (letrec ((while (subr so () unit)
                                      (lambda ()
                                        (if (not (= (array-ref marks (get m)) -1))
                                            (begin (set m (+ (get m) 1)) (while))
                                            #u))))
                             (begin
                               (while)
                               (array-set! marks l (get m))
                               (get m)))))))
                 (linear (subr so (a int) unit)
                   (lambda (e l)
                     (letrec ((loop (subr so (int) unit)
                                (lambda (l)
                                  (cond ((> (cmp (array-ref a l) e) 0) (abort-current-continuation exit-tag #u))
                                        ((eq e (array-ref a l)) (array-set! marks l (+ l 1)))
                                        (else (loop (+ l 1)))))))
                       (loop (skipmarks l)))))
                 (dicho (subr so (a int int) unit)
                   (lambda (e l r)
                     (if (= l r)
                         (linear e l)
                         (let ((m (quotient (+ l r) 2)))
                           (if (>= (cmp (array-ref a m) e) 0) (dicho e l m) (dicho e (+ m 1) r))))))
                 (for1 (subr so (int) unit)
                   (lambda (i)
                     (if (<= i (- n 2))
                         (begin
                           (if (> (cmp (array-ref a i) (array-ref a (+ i 1))) 0)
                               (abort-current-continuation exit-tag #u)
                               #u)
                           (for1 (+ i 1)))
                         #u)))
                 (for2 (subr so (int) unit)
                   (lambda (i)
                     (if (<= i (- n 1))
                         (begin (dicho (mke i) 0 (- (array-length a) 1)) (for2 (+ i 1)))
                         #u))))
          (begin
            (for1 0)
            (random-set-state rstate)
            (for2 0)
            #t))
        (lambda (u) #f)))))

(define* mkrand-dup (subr so (int) ints)
  (lambda (n)
    (let ((a (the ints (make-array n 0))))
      (letrec ((for (subr so (int) ints)
                 (lambda (i) (if (<= i (- n 1)) (begin (array-set! a i (random-int n)) (for (+ i 1))) a))))
        (for 0)))))

(define* chkrand-dup (subr so (ints int ints) bool)
  (lambda (rstate n a)
    (chkgen (lambda ((i int)) (random-int n)) compare-int (lambda ((x int) (y int)) (= x y)) rstate n a)))

(define* mkrand-nodup (subr so (int) ints)
  (lambda (n)
    (let ((a (the ints (make-array n 0))))
      (letrec ((for (subr so (int) ints)
                 (lambda (i) (if (<= i (- n 1)) (begin (array-set! a i (random-bits)) (for (+ i 1))) a))))
        (for 0)))))

(define* chkrand-nodup (subr so (ints int ints) bool)
  (lambda (rstate n a)
    (chkgen (lambda ((i int)) (random-bits)) compare-int (lambda ((x int) (y int)) (= x y)) rstate n a)))

(define-type record (productof (s1 string) (s2 string) (i1 int) (i2 int)))
(define-type recs (arrayof record @heap))

(define* rand-string (subr so () string)
  (lambda ()
    (let ((len (random-int 10)))
      (letrec ((for (subr so (int (listof char @heap)) (listof char @heap))
                 (lambda (i acc)
                   (if (<= i (- len 1))
                       (let ((c (integer->char (random-int 256))))
                         (for (+ i 1) (cons c acc)))
                       acc))))
        (list->string (reverse (for 0 nil)))))))

;; OCaml builds a record's fields from the last to the first.
(define* mkrec1 (subr so (int int) record)
  (lambda (b i)
    (let* ((i1 (random-int b))
           (s2 (rand-string))
           (s1 (rand-string)))
      (product (s1 s1) (s2 s2) (i1 i1) (i2 i)))))

(define* mkrecs (subr so (int int) recs)
  (lambda (b n)
    (if (= n 0)
        (make-array 0 (product (s1 "") (s2 "") (i1 0) (i2 0)))
        (let ((a (the recs (make-array n (mkrec1 b 0)))))
          (letrec ((for (subr so (int) recs)
                     (lambda (i) (if (< i n) (begin (array-set! a i (mkrec1 b i)) (for (+ i 1))) a))))
            (for 1))))))

;; compare on strings: byte by byte, then the shorter first.
(define* string-compare (subr so (string string) int)
  (lambda (s t)
    (letrec ((loop (subr so (int) int)
               (lambda (i)
                 (cond ((and (= i (string-length s)) (= i (string-length t))) 0)
                       ((= i (string-length s)) -1)
                       ((= i (string-length t)) 1)
                       (else
                        (let ((c (char->integer (string-ref s i))) (d (char->integer (string-ref t i))))
                          (cond ((< c d) -1) ((> c d) 1) (else (loop (+ i 1))))))))))
      (loop 0))))

(define* record=? (subr so (record record) bool)
  (lambda (r1 r2)
    (and (string=? (extract r1 s1) (extract r2 s1))
         (string=? (extract r1 s2) (extract r2 s2))
         (= (extract r1 i1) (extract r2 i1))
         (= (extract r1 i2) (extract r2 i2)))))

(define* cmpstr (subr so (record record) int)
  (lambda (r1 r2)
    (let ((c1 (string-compare (extract r1 s1) (extract r2 s1))))
      (if (= c1 0) (string-compare (extract r1 s2) (extract r2 s2)) c1))))
(define* lestr (subr so (record record) bool)
  (lambda (r1 r2)
    (let ((c1 (string-compare (extract r1 s1) (extract r2 s1))))
      (if (= c1 0) (<= (string-compare (extract r1 s2) (extract r2 s2)) 0) (< c1 0)))))
(define* chkstr (subr so (int ints int recs) bool)
  (lambda (b rstate n a) (chkgen (lambda ((i int)) (mkrec1 b i)) cmpstr record=? rstate n a)))

(define* cmpint (subr so (record record) int)
  (lambda (r1 r2) (compare-int (extract r1 i1) (extract r2 i1))))
(define* leint (subr so (record record) bool)
  (lambda (r1 r2) (<= (extract r1 i1) (extract r2 i1))))
(define* chkint (subr so (int ints int recs) bool)
  (lambda (b rstate n a) (chkgen (lambda ((i int)) (mkrec1 b i)) cmpint record=? rstate n a)))

(define* cmplex (subr so (record record) int)
  (lambda (r1 r2)
    (let ((c1 (compare-int (extract r1 i1) (extract r2 i1))))
      (if (= c1 0) (compare-int (extract r1 i2) (extract r2 i2)) c1))))
(define* lelex (subr so (record record) bool)
  (lambda (r1 r2)
    (let ((c1 (compare-int (extract r1 i1) (extract r2 i1))))
      (if (= c1 0) (<= (extract r1 i2) (extract r2 i2)) (< c1 0)))))
(define* chklex (subr so (int ints int recs) bool)
  (lambda (b rstate n a) (chkgen (lambda ((i int)) (mkrec1 b i)) cmplex record=? rstate n a)))

;;;; The tests

(define lens (listof int @heap)
  (cons 0 (cons 1 (cons 2 (cons 3 (cons 4 (cons 5 (cons 6 (cons 7 (cons 8 (cons 9 (cons 10 (cons 11 (cons 12 (cons 13 (cons 28
  (cons 100 (cons 127 (cons 128 (cons 129 (cons 193 (cons 506
  (cons 1000 (cons 1025 (cons 1535 (cons 2323 nil))))))))))))))))))))))))))

;; type ('a, 'b, 'c, 'd) aux
(define-type (aux (a type) (b type) (c type) (d type))
  (productof (prepf (subr so ((subr so (a a) int) (subr so (a a) bool)) b))
             (prepd (subr so ((arrayof a @heap)) c))
             (postd (subr so ((arrayof a @heap) d) (arrayof a @heap)))))

(define-type (cmpf (a type)) (subr so (a a) int))
(define-type (list-aux (a type)) (aux a (cmpf a) (listof a @heap) (listof a @heap)))
(define-type (array-aux (a type)) (aux a (cmpf a) (arrayof a @heap) unit))

;; let lc = { prepf = (fun x y -> x); prepd = Array.to_list; postd = postl }
(define lc-int (list-aux int)
  (product (prepf (lambda ((x (cmpf int)) (y (subr so (int int) bool))) x))
           (prepd (lambda ((a ints)) (array-to-list a)))
           (postd (lambda ((x ints) (y (listof int @heap))) (array-of-list y x)))))
(define lc-rec (list-aux record)
  (product (prepf (lambda ((x (cmpf record)) (y (subr so (record record) bool))) x))
           (prepd (lambda ((a recs)) (array-to-list a)))
           (postd (lambda ((x recs) (y (listof record @heap))) (array-of-list y x)))))
;; let ac = { prepf = (fun x y -> x); prepd = id; postd = posta }
(define ac-int (array-aux int)
  (product (prepf (lambda ((x (cmpf int)) (y (subr so (int int) bool))) x))
           (prepd (lambda ((a ints)) a))
           (postd (lambda ((x ints) (y unit)) x))))
(define ac-rec (array-aux record)
  (product (prepf (lambda ((x (cmpf record)) (y (subr so (record record) bool))) x))
           (prepd (lambda ((a recs)) a))
           (postd (lambda ((x recs) (y unit)) x))))

(define numfailed (ref int @heap) (new 0))

(define* test1 (poly ((a type) (c type) (d type))
                 (subr so (string (subr so ((cmpf a) c) d) (subr so ((arrayof a @heap)) c)
                           (subr so ((arrayof a @heap) d) (arrayof a @heap)) (cmpf a) string
                           (subr so (int) (arrayof a @heap)) (subr so (ints int (arrayof a @heap)) bool))
                       unit))
  (lambda (name f prepdata postdata cmp desc mk chk)
    (begin
      (random-reinit)
      (print-string "  ") (print-string name) (print-string " with ") (print-string desc)
      (let ((i (the (ref int @heap) (new 0))))
        (letrec ((each (subr so ((listof int @heap)) unit)
                   (lambda (l)
                     (if (null? l)
                         #u
                         (let ((n (car l)))
                           (begin
                             (if (= (get i) 0) (print-string "\n    ") #u)
                             (set i (+ (get i) 1))
                             (if (> (get i) 11) (set i 0) #u)
                             (print-int5 n)
                             (let* ((rstate (random-get-state))
                                    (a (mk n))
                                    (input (prepdata a))
                                    (output (f cmp input)))
                               (begin
                                 (print-string ".")
                                 (if (not (chk rstate n (postdata a output)))
                                     (begin (set numfailed (+ (get numfailed) 1)) (print-string "\n*** FAIL\n"))
                                     #u)))
                             (each (cdr l))))))))
          (each lens)))
      (print-string "\n"))))

(define* test (poly ((c1 type) (d1 type) (c2 type) (d2 type))
                (subr so (string bool (subr so ((cmpf int) c1) d1) (subr so ((cmpf record) c2) d2)
                          (aux int (cmpf int) c1 d1) (aux record (cmpf record) c2 d2))
                      unit))
  (lambda (name stable f1 f2 aux1 aux2)
    (begin
      (print-string "Testing ") (print-string name) (print-string "...\n")
      (let ((t (lambda ((cmp (cmpf int)) (desc string) (mk (subr so (int) ints)) (chk (subr so (ints int ints) bool)))
                 (test1 name f1 (extract aux1 prepd) (extract aux1 postd) cmp desc mk chk)))
            (cmp ((extract aux1 prepf) compare-int (lambda ((x int) (y int)) (<= x y)))))
        (begin
          (t cmp "constant ints" mkconst chkconst)
          (t cmp "sorted ints" mksorted chksorted)
          (t cmp "reverse-sorted ints" mkrev chkrev)
          (t cmp "random ints (many dups)" mkrand-dup chkrand-dup)
          (t cmp "random ints (few dups)" mkrand-nodup chkrand-nodup)))
      (let ((t (lambda ((cmp (cmpf record)) (desc string) (mk (subr so (int) recs)) (chk (subr so (ints int recs) bool)))
                 (test1 name f2 (extract aux2 prepd) (extract aux2 postd) cmp desc mk chk))))
        (begin
          (let ((cmp ((extract aux2 prepf) cmpstr lestr)))
            (t cmp "records (str)" (lambda ((n int)) (mkrecs 1 n))
               (lambda ((r ints) (n int) (a recs)) (chkstr 1 r n a))))
          (let ((cmp ((extract aux2 prepf) cmpint leint))
                (ms (the (listof int @heap) (cons 1 (cons 10 (cons 100 (cons 1000 nil)))))))
            (letrec ((each (subr so ((listof int @heap) string) unit)
                       (lambda (l suffix)
                         (if (null? l)
                             #u
                             (let ((m (car l)))
                               (begin
                                 (t cmp (string-append (string-append (string-append "records (int[" (int->string m)) "])") suffix)
                                    (lambda ((n int)) (mkrecs m n))
                                    (if (string=? suffix "")
                                        (lambda ((r ints) (n int) (a recs)) (chkint m r n a))
                                        (lambda ((r ints) (n int) (a recs)) (chklex m r n a))))
                                 (each (cdr l) suffix)))))))
              (begin
                (each ms "")
                (if stable (each ms " [stable]") #u)))))))))

;; The input, where no compiler can fold it: a global.
(define iterations int 1)

(define* main (subr so () int)
  (lambda ()
    (begin
      (set out-hash 0)
      (set numfailed 0)
      (print-string "Command line arguments are:")
      (print-string "\n")
      (test "List.sort" #f list-stable-sort list-stable-sort lc-int lc-rec)
      (test "List.stable_sort" #t list-stable-sort list-stable-sort lc-int lc-rec)
      (test "Array.sort" #f array-sort array-sort ac-int ac-rec)
      (test "Array.stable_sort" #t array-stable-sort array-stable-sort ac-int ac-rec)
      (print-string "Number of tests failed: ") (print-string (int->string (get numfailed))) (print-string "\n")
      (get out-hash))))

(define* run (subr so (int int) int)
  (lambda (i result) (if (= i 0) result (run (- i 1) (main)))))
(run iterations 0)
