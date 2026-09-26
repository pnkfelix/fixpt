;;; An abort out of a `letrena`'s body, to a prompt around it: the region
;;; is ended with what the abort cuts, as a return would end it. Many times
;;; over, and nested, so that regions left live would pile up.
(define t (prompt-tag int int pure @p) (make-continuation-prompt-tag))

(define escape (subr (goto @p) (int) int)
  (lambda (n)
    (letrena r
      (letrena s
        (let ((xs (the (listof int r) (rcons r n nil)))
              (ys (the (listof int s) (rcons s 1 nil))))
          (+ (car ys) (abort-current-continuation t (car xs))))))))

(define rounds (subr (goto @p) (int int) int)
  (lambda (i acc)
    (if (= i 0)
        acc
        (rounds (- i 1) (+ acc (prompt t (escape i) (lambda (v) v)))))))

(prompt t (rounds 1000 0) (lambda (v) v))
