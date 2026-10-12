; Design A, escape only, with a raiser fixed to one region: `digit` aborts
; to a tag at @fail, which its type names. A prompt around a call of it
; cannot remove `(goto @fail)`: `digit`, free in the body, has @fail in its
; type, so another tag in @fail could be reached past the prompt.
;; What a prompt's body may do, which every tag must say (its `D`).
(define-effect bodies (read @globals))
(define-type fail-tag (prompt-tag int string bodies @fail))
(define digit (subr (goto @fail) (fail-tag char) int)
  (lambda (t c)
    (if (and (char>=? c #\0) (char<=? c #\9))
        (- (char->integer c) 48)
        ((proj (proj abort-current-continuation @fail) int string bodies) t "not a digit"))))
(define safe-digit (subr (read (globals digit)) (char) int)
  (lambda (c)
    (let ((t (the fail-tag ((proj (proj make-continuation-prompt-tag @fail) int string bodies)))))
      (prompt t (digit t c) (lambda ((why string)) -1)))))
