#lang racket/base
(require racket/control '#%paramz)

;; 1. A mark in tail position replaces rather than accumulates (Clements & Felleisen).
(define (loop n)
  (with-continuation-mark 'depth n
    (if (= n 0)
        (continuation-mark-set->list (current-continuation-marks) 'depth)
        (loop (- n 1)))))
(printf "1. tail loop marks: ~a\n" (loop 5))

(define (nontail n)
  (with-continuation-mark 'depth n
    (if (= n 0)
        (continuation-mark-set->list (current-continuation-marks) 'depth)
        (car (list (nontail (- n 1)))))))
(printf "   non-tail marks:  ~a\n" (nontail 3))

;; 2. Marks are delimited by prompts: introspection stops at the prompt tag.
(define tag (make-continuation-prompt-tag 'hole))
(printf "2. seen through prompt: ~a\n"
  (with-continuation-mark 'k 'outside
    (car (list
      (call-with-continuation-prompt
        (lambda ()
          (with-continuation-mark 'k 'inside
            (car (list (continuation-mark-set->list (current-continuation-marks tag) 'k)))))
        tag)))))

;; 3. Exception handlers and parameterizations live in marks, not globals.
(printf "3. handler key is a mark key: ~a\n"
  (with-handlers ([void void])
    (and (continuation-mark-set-first #f exception-handler-key) #t)))
(printf "   parameterization-key present: ~a\n"
  (and (continuation-mark-set-first #f parameterization-key) #t))

;; 4. Aborting to a prompt discards the marks with the frames: no leak.
(define p (make-parameter 'global))
(call-with-continuation-prompt
  (lambda () (parameterize ([p 'inside]) (abort-current-continuation tag void)))
  tag (lambda (k) (void)))
(printf "4. parameter after abort: ~a\n" (p))

;; 5. A captured composable continuation carries its marks; you can inspect it
;;    without running it.
(define held #f)
(call-with-continuation-prompt
  (lambda ()
    (with-continuation-mark 'ctx '(argument 2 of 2 to vector-ref)
      (+ 0 ((call-with-composable-continuation (lambda (k) (set! held k) (abort-current-continuation tag void)) tag)))))
  tag (lambda (v) (void)))
(printf "5. marks of held k: ~a\n"
  (continuation-mark-set->list (continuation-marks held tag) 'ctx))
(printf "   resume twice: ~a ~a\n" (held (lambda () 1)) (held (lambda () 2)))
