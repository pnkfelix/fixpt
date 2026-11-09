;; ! is expected
;; A template's arithmetic of literals is no literal, though the checkers
;; take arithmetic whose nodes are all at one place for one (a literal past
;; a fixnum, as the parsers write it): its `+` is the standard's, through
;; `#%fx`, which that never is. Both refuse it where a `u8` is wanted.
(define-syntax three
  ()
  (syntax-rules ()
    ((_) (+ 1 2))))
(the u8 (three))
