; Design A, escape only, the raiser polymorphic in the tag's region: each
; handler makes a region of its own (`letregion`) and a tag in it, so the
; prompt delimits (nothing else free in its body names that region) and
; `safe-digit` is pure but for reading `digit`. The tag's `D`, what its
; prompts' bodies may do, still has to be written: `(read @globals)`.
;; What a prompt's body may do, which every tag must say (its `D`).
(define-effect bodies (read @globals))
(define digit
  (poly ((r region)) (subr (goto r) ((prompt-tag int string bodies r) char) int))
  (plambda ((r region))
    (lambda (t c)
      (if (and (char>=? c #\0) (char<=? c #\9))
          (- (char->integer c) 48)
          ((proj (proj abort-current-continuation r) int string bodies) t "not a digit")))))
(define safe-digit (subr (read (globals digit)) (char) int)
  (lambda (c)
    (letregion r
      (let ((t ((proj (proj make-continuation-prompt-tag r) int string bodies))))
        (prompt t ((proj digit r) t c) (lambda ((why string)) -1))))))
(define main (subr (read (globals digit safe-digit)) () (listof int acyclic))
  (lambda () (list (safe-digit #\7) (safe-digit #\x))))
(main)
