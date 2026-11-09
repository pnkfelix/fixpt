;; => 3
;; A template's procedure type with a parameter named: the name a value's
;; binder, made fresh, in scope in the types after it and the result, as
;; `(select o t)`.
(define-type ordered (moduleof (abs t type) (val less (subr pure (t t) bool))))
(define int-order
  (module (define-type t int)
          (define less (subr pure (t t) bool) (lambda (a b) (< a b)))))
(define-syntax define-first
  (-> (bvar) defn)
  (syntax-rules ()
    ((_ name)
     (define name (subr pure ((o : ordered) (select o t) (select o t)) (select o t))
       (lambda (o a b) a)))))
(define-first first-of)
(first-of int-order 3 5)
