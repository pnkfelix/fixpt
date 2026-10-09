;; A file of one expression, for `load-input`: a module, of no state and
;; given nothing, its types loaded around it (`TODO.md` §68).
(let ((types (load-module "answer-types.fx")))
  (module
(define-effect doubles (select types doubles))
(define twice (subr doubles (int) int) (lambda (n) (* 2 n)))
(define half int 21)))
