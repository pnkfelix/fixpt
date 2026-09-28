;;; A throw to a whole continuation out of a `letrena`'s body, the
;;; continuation taken outside it: the region is ended with what the throw
;;; leaves, as an abort would end it. Many times over, and nested, so that
;;; regions left live would pile up (docs/research/soundness-findings.md, F7).
(define escape (subr (goto @k) (int (subr (goto @k) (int) void)) int)
  (lambda (n k)
    (letrena r
      (letrena s
        (let ((xs (the (listof int r) (rcons r n nil)))
              (ys (the (listof int s) (rcons s 1 nil))))
          (+ (car ys) (k (car xs))))))))

(define* rounds (subr (maxeff (goto @k) (comefrom @k) spin) (int int) int)
  (lambda (i acc)
    (if (= i 0)
        acc
        (rounds (- i 1)
                (+ acc ((proj (proj (proj cwcc @k) int) (maxeff (goto @k) (read (globals escape))))
                        (lambda ((k (subr (goto @k) (int) void))) (escape i k))))))))

(rounds 1000 0)
