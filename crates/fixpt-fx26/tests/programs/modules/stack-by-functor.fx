;; => (3 2 1)
;; Okasaki's `'a Stack` (Purely Functional Data Structures, §2.1), encoded
;; as an ML functor would be: a dependent procedure from a module giving
;; the element type, `elt`, to a stack module over `(select elt t)`.
;;
;; Drawbacks, against Okasaki's signature:
;; - The element type must come wrapped in a module, `(module (define-type
;;   t int))`, where a type argument would do.
;; - Each application makes a new abstract type, as each call does in
;;   `stack-by-poly.fx`: two applications to the same element module give
;;   stacks that do not mix.
;; - No one module exports a polymorphic `push`: each instance's operations
;;   are at one element type.
;; - `top` and `pop` of the empty stack trap (`car` of `nil`), where
;;   Okasaki raises `Empty`.
(define-type elt-sig (moduleof (abs t type)))
(define-type (stack-of (e type))
  (moduleof (abs stack type)
            (val empty stack)
            (val is-empty (subr (read @heap) (stack) bool))
            (val push (subr (alloc @heap) (e stack) stack))
            (val top (subr (read @heap) (stack) e))
            (val pop (subr (read @heap) (stack) stack))))
(define make-stack (subr pure ((elt elt-sig)) (stack-of (select elt t)))
  (lambda ((elt elt-sig))
    (module
      (define-generative stack (listof (select elt t) @heap))
      (define empty stack (up-stack nil))
      (define is-empty (subr (read @heap) (stack) bool)
        (lambda (s) (null? (down-stack s))))
      (define push (subr (alloc @heap) ((select elt t) stack) stack)
        (lambda (x s) (up-stack (cons x (down-stack s)))))
      (define top (subr (read @heap) (stack) (select elt t))
        (lambda (s) (car (down-stack s))))
      (define pop (subr (read @heap) (stack) stack)
        (lambda (s) (up-stack (cdr (down-stack s))))))))
(define int-elt (module (define-type t int)))
(define bool-elt (module (define-type t bool)))
(let ((ints (make-stack int-elt))
      (bools (make-stack bool-elt)))
  (let ((s (with ints (push 3 (push 2 (push 1 empty))))))
    (list (with ints (top s))
          (with ints (top (pop s)))
          (if (with bools (is-empty empty)) 1 0))))
