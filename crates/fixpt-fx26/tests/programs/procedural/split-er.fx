;; => (13 7)
;; A call split by a union argument's members, made by a procedural macro,
;; every part of whose answer is at the use's place: an error found at `y`,
;; a variable, is not inside the other argument, `(+ 1 2)`, though its
;; place is. Inside is by structure (the error's origin), not by place.
(define f (allof (subr pure (int int) int) (subr pure (string int) int))
  (lambda (a n) (typecase a (int i (+ i n)) (string s (+ (string-length s) n)) (else e 0))))
(define-syntax call3
  (er-macro-transformer
    (lambda (form rename compare)
      `(,(rename 'f) ,(car (cdr form)) (,(rename '+) 1 2)))))
(define g (subr (read (globals f)) ((oneof int string)) int)
  (lambda (y) (call3 y)))
(list (g 10) (g "abcd"))
