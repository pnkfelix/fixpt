(define-syntax unroll
  (er-macro-transformer
   (lambda (form rename compare)
     (let loop ((i (cadr form)) (acc '()))
       (if (= i 0) (cons (rename 'begin) acc) (loop (- i 1) (cons (caddr form) acc)))))))
(define n 0)
(unroll 4 (set! n (+ n 1)))
n
