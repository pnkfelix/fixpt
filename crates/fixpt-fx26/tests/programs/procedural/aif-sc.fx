;; => (6 0)
;; The same by syntactic closures: the branches closed in the use's
;; environment but for `it`, a free name, which is the macro's binding.
(define-syntax aif
  (sc-macro-transformer
    (lambda (form env)
      (let ((test (make-syntactic-closure env '() (car (cdr form))))
            (then (make-syntactic-closure env '(it) (car (cdr (cdr form)))))
            (else (make-syntactic-closure env '(it) (car (cdr (cdr (cdr form)))))))
        `(let ((it ,test)) (if (= it 0) ,else ,then))))))
(list (aif (+ 2 4) it -1) (aif 0 it 0))
