;; A procedural macro of a file: what its transformer renames means what it
;; means in the file, where it is used and where the file is imported.
(define helper (subr pure (int) int) (lambda (x) (+ x 1)))
(define-syntax inc
  (er-macro-transformer
    (lambda (form rename compare) `(,(rename 'helper) ,(car (cdr form))))))
(define six int (let ((helper 0)) (inc 5)))
