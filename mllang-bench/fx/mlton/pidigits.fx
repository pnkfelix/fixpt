;;; PIDIGITS -- the digits of pi, from a lazy stream of linear fractional
;;; transformations (Gibbons's unbounded spigot), in exact integers.
;;;
;;; From MLton's benchmark suite (benchmark/tests/pidigits.sml, commit
;;; aa2fd1ad9b91), ported to FX-26. Iteration count (ours; MLton's driver
;;; was not fetched): 1 call of `MainBenchmark.doit`, (doit 250), which
;;; reads digits until the 251st zero and prints the index of that digit.
;;; Answer: 2881, that index, counting the leading 3 as digit 0 (a Python
;;; transcription of the same streams gives 2881 too; for (doit 0) both
;;; give 32, where pi's first zero is: 3.1415926535897932384626433832795028).
;;;
;;; What changed:
;;; - IntInf.int is `int`, which is exact at any size. `IntInf.div` floors,
;;;   where `quotient` truncates: `floor-div` is written here.
;;; - The stream type `'a Stream.t = unit -> 'a u` is a parametric datatype
;;;   `(u a)` of a thunk; `Stream.unfold`, `Stream.map` and
;;;   `PiDigits.stream` are `poly`s. Curried functions take their arguments
;;;   together, and `Stream.unfold`'s option is a sum.
;;; - `display` returns the index where the original prints it; its `raise
;;;   Empty`, for a stream that ends (the digits never do), is an abort.
;;;   Only MainBenchmark is ported; MainShootout, which prints the digits
;;;   themselves, is the Benchmarks Game's, ported as
;;;   `benchmarksgame/pidigits5.fx`.

;; What the streams' thunks do: the globals are those `pi`'s procedures read.
(define-effect st-body
  (maxeff spin (read (globals Cons Nil NONE SOME comp floor-extr floor-div))))
(define-effect st (maxeff st-body (goto @z)))

(define-datatype (u (a type))
  (Nil)
  (Cons a (subr st () (u a))))

(define-type lft (productof (q int) (r int) (s int) (t int)))

(define-datatype (option (a type))
  (NONE)
  (SOME a))

;; What a stream that ends aborts with: the digits never do.
(define empty-tag (prompt-tag int unit st-body @z) (make-continuation-prompt-tag))

;; IntInf.div: floor division.
(define* floor-div (subr pure (int int) int)
  (lambda (a b)
    (let ((q (quotient a b)))
      (if (or (= (* q b) a) (if (< a 0) (< b 0) (>= b 0))) q (- q 1)))))

;; ---- structure Stream

(define unfold
  (poly ((a type) (b type))
    (subr pure ((subr st (b) (option (productof (1 a) (2 b)))))
          (subr pure (b) (subr st () (u a)))))
  (plambda ((a type) (b type))
    (lambda (f)
      (letrec ((loop (subr pure (b) (subr st () (u a)))
                 (lambda (b)
                   (lambda ()
                     (tagcase (f b)
                       (NONE () (Nil))
                       (SOME (p) (Cons (extract p 1) (loop (extract p 2)))))))))
        loop))))

(define smap
  (poly ((a type) (b type))
    (subr (read (globals unfold)) ((subr st (a) b))
          (subr pure ((subr st () (u a))) (subr st () (u b)))))
  (plambda ((a type) (b type))
    (lambda (f)
      ((proj unfold b (subr st () (u a)))
       (lambda ((s (subr st () (u a))))
         (tagcase (s)
           (Nil () (NONE))
           (Cons (x xs) (SOME (product (1 (f x)) (2 xs))))))))))

;; ---- structure PiDigits

(define stream
  (poly ((a type) (b type) (c type))
    (subr pure ((subr st (b) c) (subr st (b c) bool) (subr st (b c) b) (subr st (b a) b))
          (subr pure (b (subr st () (u a))) (subr st () (u c)))))
  (plambda ((a type) (b type) (c type))
    (lambda (next safe prod cons)
      (letrec ((loop (subr pure (b (subr st () (u a))) (subr st () (u c)))
                 (lambda (z s)
                   (lambda ()
                     (let ((y (next z)))
                       (if (safe z y)
                           (Cons y (loop (prod z y) s))
                           (tagcase (s)
                             (Nil () (Nil))
                             (Cons (x xs) ((loop (cons z x) xs))))))))))
        loop))))

(define unit lft (product (q 1) (r 0) (s 0) (t 1)))

(define* comp (subr pure (lft lft) lft)
  (lambda (a b)
    (let ((q (extract a q)) (r (extract a r)) (s (extract a s)) (t (extract a t))
          (u (extract b q)) (v (extract b r)) (w (extract b s)) (x (extract b t)))
      (product (q (+ (* q u) (* r w))) (r (+ (* q v) (* r x)))
               (s (+ (* s u) (* t w))) (t (+ (* s v) (* t x)))))))

(define* floor-extr (subr pure (lft int) int)
  (lambda (z x)
    (floor-div (+ (* (extract z q) x) (extract z r)) (+ (* (extract z s) x) (extract z t)))))

;; The lfts (k, 4k+2, 0, 2k+1) for k = 1, 2, ...
(define* lfts (subr (read (globals smap unfold)) () (subr st () (u lft)))
  (lambda ()
    (((proj smap int lft)
      (lambda (k) (product (q k) (r (+ (* 4 k) 2)) (s 0) (t (+ (* 2 k) 1)))))
     (((proj unfold int int) (lambda (i) (SOME (product (1 i) (2 (+ i 1)))))) 1))))

(define* pi (subr pure () (subr st () (u int)))
  (lambda ()
    (((proj stream lft lft int)
      (lambda (z) (floor-extr z 3))
      (lambda (z n) (= n (floor-extr z 4)))
      (lambda (z n) (comp (product (q 10) (r (* -10 n)) (s 0) (t 1)) z))
      (lambda (z z2) (comp z z2)))
     unit (lfts))))

;; ---- structure MainBenchmark

(define* display (subr st (int) int)
  (lambda (n)
    (let ((tag empty-tag) (ds (pi)))
      (letrec ((loop (subr st ((subr st () (u int)) int int) int)
                 (lambda (ds k n)
                   (tagcase (ds)
                     (Nil () (abort-current-continuation tag #u))
                     (Cons (d ds)
                       (if (= d 0)
                           (if (= n 0) k (loop ds (+ k 1) (- n 1)))
                           (loop ds (+ k 1) n)))))))
        (prompt tag (loop ds 0 n) (lambda (x) -1))))))

;; The input, where no compiler can fold it: a global, which a later
;; definition may replace.
(define input int 250)

(display input)
