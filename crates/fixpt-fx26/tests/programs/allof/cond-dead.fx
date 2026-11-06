;; => (y b y x)
;; A `cond` branch a member's type rules out is skipped under that member,
;; as a `tagcase` arm is (`docs/research/logical-types.md` §8.5, rule 2):
;; under `(symbol) symbol` neither `null?`'s branch nor `pair?`'s can run,
;; and what they give is no `symbol`; under the list member, `symbol?`'s.
;; Each member checks `pure`: under each, what its types rule out is passed
;; over in finding whether the recursion ends, as in checking it.
(define-type syms (listof symbol acyclic))
(define swap (allof (subr pure (symbol symbol symbol) symbol)
                    (subr pure (symbol symbol syms) syms))
  (letrec ((swap (allof (subr pure (symbol symbol symbol) symbol)
                        (subr pure (symbol symbol syms) syms))
             (lambda (a b t)
               (cond ((symbol? t) (cond ((eq? t a) b) ((eq? t b) a) (else t)))
                     ((null? t) (the syms nil))
                     ((pair? t) (cons (swap a b (car t)) (swap a b (cdr t))))
                     (else t)))))
    swap))
(cons (swap 'x 'y 'x)
      (cons (swap 'x 'y 'b) (swap 'x 'y (list 'x 'y))))
