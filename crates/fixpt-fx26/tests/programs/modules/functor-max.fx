;; => 5
;; A dependent procedure (`first-class-modules.md`, M5): the types of the
;; later parameters and the result are the first one's type `t`.
(define-type ordered (moduleof (abs t type) (val less (subr pure (t t) bool))))
(define int-order
  (module (define-type t int)
          (define less (subr pure (t t) bool) (lambda (a b) (< a b)))))
(define max-of (subr pure ((o ordered) (select o t) (select o t)) (select o t))
  (lambda ((o ordered) (a (select o t)) (b (select o t))) (with o (if (less a b) b a))))
(max-of int-order 3 5)
