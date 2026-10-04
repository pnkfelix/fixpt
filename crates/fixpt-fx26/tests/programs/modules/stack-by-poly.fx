;; => (3 2 1)
;; Okasaki's `'a Stack` (Purely Functional Data Structures, §2.1), encoded
;; without a type constructor of kind type -> type: one polymorphic
;; procedure that makes a stack module for whichever element type it is
;; projected at. Its type stands for the signature STACK.
;;
;; Drawbacks, against Okasaki's signature:
;; - Each call makes a new abstract type. Two stacks of ints from two calls
;;   of `(proj stacks int)` do not mix; in ML, `int Stack` is one type
;;   wherever it is used. Sharing takes binding the module once and passing
;;   that module around.
;; - No one module exports a polymorphic `push`: each instance's operations
;;   are at one element type, so a procedure over "stacks of anything" takes
;;   the maker, `stacks`, not a stack module.
;; - `top` and `pop` of the empty stack trap (`car` of `nil`), where
;;   Okasaki raises `Empty`.
(define-type stack-sig
  (poly ((a type))
    (subr pure ()
      (moduleof (abs stack type)
                (val empty stack)
                (val is-empty (subr (read @heap) (stack) bool))
                (val push (subr (alloc @heap) (a stack) stack))
                (val top (subr (read @heap) (stack) a))
                (val pop (subr (read @heap) (stack) stack))))))
(define stacks stack-sig
  (plambda ((a type))
    (lambda ()
      (module
        (define-generative stack (listof a @heap))
        (define empty stack (up-stack nil))
        (define is-empty (subr (read @heap) (stack) bool)
          (lambda (s) (null? (down-stack s))))
        (define push (subr (alloc @heap) (a stack) stack)
          (lambda (x s) (up-stack (cons x (down-stack s)))))
        (define top (subr (read @heap) (stack) a)
          (lambda (s) (car (down-stack s))))
        (define pop (subr (read @heap) (stack) stack)
          (lambda (s) (up-stack (cdr (down-stack s)))))))))
(let ((ints ((proj stacks int)))
      (bools ((proj stacks bool))))
  (let ((s (with ints (push 3 (push 2 (push 1 empty))))))
    (list (with ints (top s))
          (with ints (top (pop s)))
          (if (with bools (is-empty empty)) 1 0))))
