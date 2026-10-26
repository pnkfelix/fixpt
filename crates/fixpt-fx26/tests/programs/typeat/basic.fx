;; => "45 52 int; 58 60 int; error 14 18"
;; `type-at` (Heist's, FIXPT-CHANGES.md F3): the checker's type of the
;; innermost expression of a program text at a character, its span in
;; characters; a refusal as `error START END …`.
(define prog string "(define* f (subr pure (int) int) (lambda (x) (+ x 1)))\n(f 41)\n(define s string \"hi\")")
(define* first-three (subr spin (string) string)
  ;; "error START END" of a refusal, the message left off.
  (lambda (s)
    (let* ((a (string-search s " " 0)) (b (string-search s " " (+ a 1))) (c (string-search s " " (+ b 1))))
      (substring s 0 c))))
(string-append (type-at prog 47) "; " (type-at prog 58) "; " (first-three (type-at "(define x int \"no\")" 3)))
