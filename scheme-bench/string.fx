;;; STRING -- One of the Kernighan and Van Wyk benchmarks.
;;;
;;; From Larceny's R7RS benchmarks (test/Benchmarking/R7RS/src/string.scm),
;;; ported to FX-26. Larceny's input: 25 iterations of (my-try 500000).
;;; Answer: 524278.
;;;
;;; The global string `s`, which the benchmark assigns, is a reference. The
;;; `do` loops are local `letrec` loops (their unused counters kept).
;;; `string-append` takes two strings, so appending five is four calls.

(define s (ref string @heap) (new "abcdef"))

(define* grow (subr (maxeff (read @heap) (write @heap)) () string)
  (lambda ()
    (begin
      (set s (string-append "123" (string-append (get s) (string-append "456" (string-append (get s) "789")))))
      (set s (string-append
              (substring (get s) (quotient (string-length (get s)) 2) (string-length (get s)))
              (substring (get s) 0 (+ 1 (quotient (string-length (get s)) 2)))))
      (get s))))

(define* trial (subr (maxeff (read @heap) (write @heap) spin) (int) int)
  (lambda (n)
    (letrec ((loop (subr (maxeff (read @heap) (write @heap) spin (read (globals grow s))) (int) int)
               (lambda (i)
                 (if (> (string-length (get s)) n)
                     (string-length (get s))
                     (begin (grow)
                            (loop (+ i 1)))))))
      (loop 0))))

(define* my-try (subr (maxeff (read @heap) (write @heap) spin) (int) int)
  (lambda (n)
    (letrec ((loop (subr (maxeff (read @heap) (write @heap) spin (read (globals grow s trial))) (int) int)
               (lambda (i)
                 (if (>= i 10)
                     (string-length (get s))
                     (begin (set s "abcdef")
                            (trial n)
                            (loop (+ i 1)))))))
      (loop 0))))

;; The inputs, where no compiler can fold them (Larceny's `hide`): globals,
;; which a later definition may replace.
(define input1 int 500000)
(define iterations int 25)

(define* run (subr (maxeff (read @heap) (write @heap) spin) (int int) int)
  (lambda (i result) (if (= i 0) result (run (- i 1) (my-try input1)))))
(run iterations 0)
