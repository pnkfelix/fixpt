;;; Sums and products made in line natively (`%make-frozen`): many, kept in
;;; a list and taken apart again, with collections moving them; products
;;; of one to seven fields, a sum around each.
(define-datatype shape (dot int) (box int int) (wide int int int int int int int))
(define-type shapes (listof shape @heap))
(define* make (subr (maxeff (alloc @heap) spin) (int shapes) shapes)
  (lambda (i acc)
    (if (= i 0)
        acc
        (make (- i 1)
              (cons (if (= (modulo i 3) 0) (dot i)
                        (if (= (modulo i 3) 1) (box i (+ i 1)) (wide i 1 2 3 4 5 6)))
                    acc)))))
(define* case-shape (subr pure (shape) int)
  (lambda (s)
    (tagcase s
      (dot (x) x)
      (box (x y) (* x y))
      (wide (a b c d e f g) (+ a (+ b (+ c (+ d (+ e (+ f g))))))))))
(define* weigh (subr (maxeff (read @heap) spin) (shapes int) int)
  (lambda (xs acc)
    (if (null? xs)
        acc
        (weigh (cdr xs)
               (+ acc (case-shape (car xs)))))))
(define* frozen-made (subr (maxeff (alloc @heap) (read @heap) spin) (int) int)
  (lambda (n) (weigh (make n nil) 0)))
(frozen-made 300)
