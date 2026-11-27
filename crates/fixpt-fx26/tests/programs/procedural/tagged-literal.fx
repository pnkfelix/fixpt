;; => (5 0)
;; A tag bound to a procedural macro, run at expansion: its text a `utf8`,
;; looked at once, and what it makes, here a count, in the literal's place.
(define-syntax literal:len
  (er-macro-transformer
    (lambda (form rename compare)
      (let ((t (car (cdr form)))) (if (utf8? t) (utf8-length t) 0)))))
(list #Llen"héllo" #Llen"")
