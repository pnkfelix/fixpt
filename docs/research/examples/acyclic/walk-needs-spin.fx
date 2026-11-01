;;; Refused: a walk that follows the cycle of cycle-through-ref.fx, from a
;;; cell through its frozen list and back through `get`, declared without
;;; `spin`. The `car` of a pair at `acyclic` is smaller, but what `get`
;;; gives is not, so size-change finds no decrease
;;; (`acyclic-shallow-and-deep.md` §2.1).
(define-type cell (ref (listof cell acyclic) @r))
(define c cell (new (the (listof cell acyclic) (list))))
(define l (listof cell acyclic) (list c))
(set c l)
(define walk (subr (read @r) (cell) int)
  (lambda (c)
    (letrec ((cells (subr (read @r) ((listof cell acyclic)) int)
               (lambda (xs) (if (null? xs) 0 (+ (cell (car xs)) (cells (cdr xs))))))
             (cell (subr (read @r) (cell) int)
               (lambda (c) (+ 1 (cells (get c))))))
      (cell c))))
(walk c)
