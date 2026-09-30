;;; A write in one form, seen by the next: the evaluator, which runs each form
;;; after the text of those before, keeps an expression that writes in that
;;; text (TODO §18).
(define xs (listof int @heap) (cons 1 (cons 2 nil)))
(set-car! (cdr xs) 20)
(+ (car xs) (car (cdr xs)))
