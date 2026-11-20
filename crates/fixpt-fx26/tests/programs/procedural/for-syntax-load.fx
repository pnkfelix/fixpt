;; => 13
;; A phase-1 form loads a file from the directory of the file it is written
;; in, and that file one from its own (Heist's should-work note, entry 14).
(begin-for-syntax
  (define helpers (load-module "../module-files/phase1-plus.fx"))
  (import helpers plus-base))
(define-syntax plus-ten
  (er-macro-transformer
    (lambda (form rename compare) (let ((d (car (cdr form)))) (if (int? d) (plus-base d) d)))))
(plus-ten 3)
