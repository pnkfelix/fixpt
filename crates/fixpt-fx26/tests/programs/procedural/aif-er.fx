;; => (6 0)
;; Capture on purpose: an anaphoric `if`, whose branches see `it`, the test's
;; value. By explicit renaming, `it` is the one name not renamed. No
;; `syntax-rules` can say this but by the use writing the name.
(define-syntax aif
  (er-macro-transformer
    (lambda (form rename compare)
      (let ((test (car (cdr form))) (then (car (cdr (cdr form))))
            (else (car (cdr (cdr (cdr form))))))
        `(,(rename 'let) ((it ,test))
           (,(rename 'if) (,(rename '=) it 0) ,else ,then))))))
(list (aif (+ 2 4) it -1) (aif 0 it 0))
