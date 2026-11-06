;; A stage against a module whose type names the program's own generative
;; types (`TODO.md` §206): the stage's checker makes each from the
;; definition its rep carries, a recursive one with a parameter too. Code
;; staged passes a value of one between the module's procedures; it cannot
;; take one apart, nor pass its representation for it.
(define-generative id int)
(define-generative (tree (a type)) (sumof (leaf a) (node (tupleof (tree a) (tree a)))))
(define rt
  (module (define make (subr (read (globals up-id)) (int) id) (lambda (n) (up-id n)))
          (define get (subr (read (globals down-id)) (id) int) (lambda (i) (down-id i)))
          (define leaf (subr (read (globals up-tree)) (int) (tree int))
            (lambda (n) (up-tree (sum leaf n))))
          (define join (subr (read (globals up-tree)) ((tree int) (tree int)) (tree int))
            (lambda (l r) (up-tree (sum node (tuple l r)))))
          (define total (subr (read (globals down-tree)) ((tree int)) int)
            (letrec ((total (subr (read (globals down-tree)) ((tree int)) int)
                       (lambda (t)
                         (tagcase (down-tree t) (leaf n n) (node (l r) (+ (total l) (total r)))))))
              total))))
(define number
  (subr (maxeff stage spin (read (globals rt up-id down-id up-tree down-tree))) (datum) string)
  (lambda (code)
    (stage rt (read (globals up-id down-id up-tree down-tree)) int code
      (p (int->string (p)))
      (why (string-append "refused: " (extract why message))))))
(define line (subr (io stdout) (string) unit)
  (lambda (s) (begin (write-out (string-append s "\n")) #u)))
(define main
  (subr (maxeff stage spin (io stdout)
                (read (globals rt number line up-id down-id up-tree down-tree)))
        () int)
  (lambda ()
    (begin
      (line (number '(get (make 41))))
      (line (number '(total (join (leaf 1) (join (leaf 2) (leaf 3))))))
      ;; The representation is not the type.
      (line (number '(get 41)))
      ;; Twice, the one type: a stage's value of it given back to the module.
      (line (number '(let ((i (make 5))) (+ (get i) (get i)))))
      0)))
