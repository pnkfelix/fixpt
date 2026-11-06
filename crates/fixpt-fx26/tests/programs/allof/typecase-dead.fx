;; => (y b y x)
;; The same by `typecase`, whose arms are those tests in turn: an arm a
;; member's type rules out is skipped under it, the last member too (the list
;; member first here).
(define-type syms (listof symbol acyclic))
(define swap (allof (subr pure (symbol symbol syms) syms)
                    (subr pure (symbol symbol symbol) symbol))
  (letrec ((swap (allof (subr pure (symbol symbol syms) syms)
                        (subr pure (symbol symbol symbol) symbol))
             (lambda (a b t)
               (typecase t
                 (symbol s (cond ((eq? s a) b) ((eq? s b) a) (else s)))
                 (nil n (the syms nil))
                 (pair p (cons (swap a b (car p)) (swap a b (cdr p))))
                 (else u u)))))
    swap))
(cons (swap 'x 'y 'x)
      (cons (swap 'x 'y 'b) (swap 'x 'y (list 'x 'y))))
