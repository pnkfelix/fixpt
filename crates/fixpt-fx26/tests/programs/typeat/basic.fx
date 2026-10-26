;; => "45 52 int; 58 60 int; error 14 18; 123 124 f"
;; `type-at` (Heist's, FIXPT-CHANGES.md F3): the checker's type of the
;; innermost expression of a program text at a character, its span in
;; characters; a refusal as `error START END …`; and a type a `define-type`
;; names, by its name, though the checker keeps it only for data.
(define prog string
  (string-append "(define* f (subr pure (int) int) (lambda (x) (+ x 1)))\n"
                 "(f 41)\n(define s string \"hi\")"))
(define* first-three (subr spin (string) string)
  ;; "error START END" of a refusal, the message left off.
  (lambda (s)
    (let* ((a (string-search s " " 0)) (b (string-search s " " (+ a 1)))
           (c (string-search s " " (+ b 1))))
      (substring s 0 c))))
(define named string
  (string-append "(define-type pt (productof (x int) (y int)))\n"
                 "(define-type f (subr pure (pt) int))\n"
                 "(define* g f (lambda (p) (extract p x)))\ng"))
(string-append (type-at prog 47) "; " (type-at prog 58) "; "
               (first-three (type-at "(define x int \"no\")" 3))
               "; " (type-at named 123))
