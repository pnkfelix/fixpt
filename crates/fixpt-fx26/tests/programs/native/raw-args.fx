;;; `f64`s passed raw (TODO.md §91), each way a call may meet them: `orbit`
;;; takes its `f64`s raw and calls itself so, in tail position through its
;;; global (as `mandelbrot`'s `loop3`); `scale` takes one raw, from a caller
;;; that has it raw (`orbit`) and from one that has a value (`kept`, from a
;;; list); `keep` takes one as a value (into a list), given it raw; `deepr`
;;; takes one raw and recurses on it, past the stack cache's limit, so that
;;; the overflow at its entry finds it raw; a continuation is given one;
;;; and, where no inlining hides the call, `keepn` takes a value given raw
;;; (`mixed`'s), `sqsum` one raw given a value and given raw, `dot2` two
;;; raw given one of each.
(define* scale (subr pure (f64 int) f64)
  (lambda (x k) (f64* x (int->f64 k))))
(define* keep (subr (alloc @heap) (f64) (listof f64 @heap))
  (lambda (x) (cons x nil)))
(define* orbit (subr (maxeff spin (read (globals scale))) (int f64 f64) f64)
  (lambda (n x c)
    (if (= n 0) x (orbit (- n 1) (f64+ (f64* x .5) (scale c 2)) c))))
(define* deepr (subr (maxeff (alloc @heap) (read @heap) spin) (int f64) f64)
  (lambda (n x)
    (if (= n 0)
        x
        (let ((junk (the (listof int @heap) (cons 1 nil))))
          (f64+ (f64* x 1e-3) (deepr (- n (car junk)) (f64+ x 1.1)))))))
(define* kept (subr (maxeff (alloc @heap) (read @heap) (read (globals keep scale))) (f64) f64)
  (lambda (x) (scale (car (keep (f64* x 3.))) 2)))
(define* keepn (subr (maxeff (alloc @heap) spin) (int f64) (listof f64 @heap))
  (lambda (n x) (if (= n 0) nil (cons x (keepn (- n 1) x)))))
(define* sqsum (subr spin (int f64) f64)
  (lambda (n x) (if (= n 0) 0. (f64+ (f64* x x) (sqsum (- n 1) x)))))
(define* dot2 (subr spin (int f64 f64) f64)
  (lambda (n a b) (if (= n 0) 0. (f64+ (f64* a b) (dot2 (- n 1) a b)))))
(define* shown (subr (alloc @heap) (f64) int)
  (lambda (x) (string-length (f64->string x))))
(define* mixed
  (subr (maxeff (alloc @heap) (read @heap) spin (read (globals keepn sqsum dot2 shown))) (f64) f64)
  (lambda (x)
    (let ((xs (keepn 3 (f64* x 2.))))
      (f64+ (f64+ (sqsum 2 (car xs)) (sqsum 2 (f64+ x 1.)))
            (f64+ (dot2 2 (car xs) (f64+ x 1.)) (int->f64 (shown (f64* x .5))))))))
(define-effect grabbing (maxeff (goto @p) (comefrom @p) (read (globals u))))
(define u (prompt-tag f64 f64 grabbing @p) (make-continuation-prompt-tag))
(define* given (subr (maxeff grabbing (read (globals u))) (f64) f64)
  (lambda (x)
    (prompt u
            (f64+ 1. (call-with-composable-continuation (lambda (k) (k (f64* x 2.))) u))
            (lambda (v) v))))
(define* raw-args
  (subr (maxeff (alloc @heap) (read @heap) grabbing spin
                (read (globals orbit deepr kept given mixed keepn sqsum dot2 shown keep scale u)))
        (int) int)
  (lambda (n)
    (+ (f64->int (f64-truncate (orbit n 1. .25)))
       (+ (f64->int (f64-truncate (deepr n 0.)))
          (+ (f64->int (f64-truncate (kept 1.5)))
             (+ (f64->int (f64-truncate (given 3.)))
                (f64->int (f64-truncate (mixed 1.5)))))))))
(raw-args 3000)
