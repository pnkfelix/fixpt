;; => (#t #f #f #t #t #t)
;; `gensym` makes a symbol equal to itself alone (`TODO.md` §292): not to
;; the interned symbol of its name, nor to another of the same prefix and
;; seed; its name is its prefix, then its seed's, a gensym's too. Making
;; one is an effect of its own, `gensym`, which `f` says.
(define f (subr gensym (symbol) symbol) (lambda (x) (gensym "%:1:" x)))
(let* ((g (f 'x)) (h (f 'x)) (gg (gensym "%~" g)))
  (list (symbol=? g g) (symbol=? g h) (symbol=? g (string->symbol "%:1:x"))
        (string=? (symbol->string g) "%:1:x") (string=? (symbol->string gg) "%~%:1:x")
        (symbol=? (car (list g h)) g)))
