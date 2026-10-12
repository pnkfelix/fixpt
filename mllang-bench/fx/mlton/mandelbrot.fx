;;; MANDELBROT -- the iterations of z := z^2 + c over a grid, summed.
;;;
;;; From MLton's benchmark suite (benchmark/tests/mandelbrot.sml, from the
;;; SML/NJ suite), ported to FX-26. Sizes (ours): a grid of 1024 by 1024,
;;; not 32768, and 20 runs, (doit 20); `maxCount` 2048 as the original.
;;; Answer: the iterations summed, as the original's `testit` prints them.
;;;
;;; The original's `c_re` is `x_base * (delta + real j)`, kept as written.
;;; Its `sum_iterations` reference is an accumulator here. `loop3` carries
;;; `z_re` and `z_im`, two `f64`s, round its loop.

(define x-base f64 -2.)
(define y-base f64 1.25)
(define side f64 2.5)
(define sz int 1024)
(define max-count int 2048)

(define* loop3
  (subr (maxeff spin (read (globals max-count))) (int f64 f64 f64 f64) int)
  (lambda (count z-re z-im c-re c-im)
    (if (< count max-count)
        (let* ((z-re-sq (f64* z-re z-re)) (z-im-sq (f64* z-im z-im)))
          (if (f64> (f64+ z-re-sq z-im-sq) 4.)
              count
              (let ((z-re-im (f64* z-re z-im)))
                (loop3 (+ count 1) (f64+ (f64- z-re-sq z-im-sq) c-re)
                       (f64+ (f64+ z-re-im z-re-im) c-im) c-re c-im))))
        count)))

(define* loop2
  (subr (maxeff spin (read (globals x-base side sz loop3 max-count))) (int f64 int) int)
  (lambda (j c-im sum)
    (if (>= j sz)
        sum
        (let ((c-re (f64* x-base (f64+ (f64/ side (int->f64 sz)) (int->f64 j)))))
          (loop2 (+ j 1) c-im (+ sum (loop3 0 c-re c-im c-re c-im)))))))

(define* loop1
  (subr (maxeff spin (read (globals y-base side sz loop2 x-base loop3 max-count))) (int int) int)
  (lambda (i sum)
    (if (>= i sz)
        sum
        (let ((c-im (f64- y-base (f64* (f64/ side (int->f64 sz)) (int->f64 i)))))
          (loop1 (+ i 1) (loop2 0 c-im sum))))))

(define* doit (subr (maxeff spin (read (globals loop1 y-base side sz loop2 x-base loop3 max-count))) (int) int)
  (lambda (n)
    (letrec ((loop (subr (maxeff spin (read (globals loop1 y-base side sz loop2 x-base loop3 max-count)))
                         (int int) int)
               (lambda (n last) (if (= n 0) last (loop (- n 1) (loop1 0 0))))))
      (loop n 0))))

(doit 20)
