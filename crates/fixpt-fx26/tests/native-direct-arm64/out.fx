;;; The wrappers' ends (`harness.rs`), `{EFF}` their effect: the labels
;;; `ls` bound, a `brk #0`, the stubs placed, each call-out's load given
;;; field `n + 3`; the call-outs' count, the call-outs, `pre`, and the bytes
;;; (or 0xee, `ada-err` saying why).
(define t-bind (subr {EFF} ((listof int @k)) unit)
  (lambda (ls) (if (null? ls) #u (begin (ada-bind (car ls)) (t-bind (cdr ls))))))
(define t-fields (subr {EFF} ((listof (productof (1 int) (2 int)) @k)) unit)
  (lambda (ls)
    (if (null? ls)
        #u
        (begin (ada-callout-field (extract (car ls) 1) (+ 3 (extract (car ls) 2)))
               (t-fields (cdr ls))))))
(define t-out (subr {EFF} ((listof int @k) (listof int @k)) (listof int @k))
  (lambda (pre ls)
    (begin (t-bind ls) (ada-e 3558866944) (ada-place-stubs) (t-fields (ada-callout-loads-made))
      (let* ((cs (ada-callouts)) (code (ada-finish)))
        (cons (list-length cs) (append cs (append pre (if (ada-ok?) code (cons 238 nil)))))))))
(define t-bit (subr pure (bool) int) (lambda (b) (if b 1 0)))
;; `n` `nop`s.
(define t-nops (subr {EFF} (int) unit)
  (lambda (n) (if (<= n 0) #u (begin (ada-e 3573751839) (t-nops (- n 1))))))
