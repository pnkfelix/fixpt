;; => (1 2)
;; A keyword compared as a name, as `cond`'s `else` is: `(pick a then b)`
;; gives `a`, any other word `b`. `compare` takes a renamed name for its name.
(define-syntax pick
  (er-macro-transformer
    (lambda (form rename compare)
      (let ((k (car (cdr (cdr form)))))
        (if (and (symbol? k) (compare k (rename 'then)))
            (car (cdr form))
            (car (cdr (cdr (cdr form)))))))))
(list (pick 1 then 2) (pick 1 else 2))
