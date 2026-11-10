;; ! the names `m` gives are not known before it is checked: give it a type where it is bound, `(the (moduleof …) e)` or a parameter's
;; An `include` of a module whose names the program does not say before it
;; is checked, an item naming one of them.
(define-type sig (moduleof (val x int)))
(define k (lambda ((ms (listof sig))) (let ((m (car ms))) (module (include m) (define y int x)))))
