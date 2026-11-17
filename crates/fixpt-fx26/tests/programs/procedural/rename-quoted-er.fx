;; => (#t #t #t)
;; `rename` gives one name for one name in a call, made an alias of the
;; expansion after the call (`procedural::tagged`), a quoted one too: the same
;; name twice, and, quoted, the name itself (`renamed-type-label-quote.fx`);
;; and an alias of an alias, `(rename (rename 'x))`, `compare`d to `x`, as
;; both are `x` where the macro was defined.
(define-syntax names
  (er-macro-transformer
    (lambda (form rename compare)
      (list 'list
            (list 'eq? (list 'quote (rename 'x)) (list 'quote (rename 'x)))
            (list 'eq? (list 'quote (rename 'x)) (list 'quote 'x))
            (compare (rename (rename 'x)) 'x)))))
(names)
