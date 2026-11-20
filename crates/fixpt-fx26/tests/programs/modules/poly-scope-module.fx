;; => 9
;; A definition's `poly` binders are in scope in what it is defined as, in a
;; module as at a program's top level: `define`, `define*` and `define-rec`,
;; no `plambda` (Heist's should-work note, entry 16).
(define m
  (module
    (define count-of
      (poly ((p place) (a type)) (subr (read (acyclic p)) ((listof a (acyclic p))) int))
      (lambda (l)
        (letrec ((go (subr (read (acyclic p)) ((listof a (acyclic p)) int) int)
                   (lambda (l n) (if (null? l) n (go (cdr l) (+ n 1))))))
          (go l 0))))
    (define* first-or
      (poly ((a type)) (subr pure ((listof a acyclic) a) a))
      (lambda (l d) (let ((x (the a d))) (if (null? l) x (car l)))))
    (define-rec
      (len (poly ((a type)) (subr spin ((listof a acyclic)) int))
        (lambda (l)
          (let ((n (the int 0))) (if (null? l) n (+ 1 (len (the (listof a acyclic) (cdr l)))))))))))
(+ ((with m count-of) (list 1 2 3)) (+ ((with m first-or) (list 4) 0) ((with m len) (list 1 2))))
