;;; The syscalls Fixpt's runtime has (`docs/research/syscalls.md`), declared
;;; as a runtime's own code does (`--syscalls`): asked whether each is there,
;;; and called. Its flat arrays move, so it makes no view of one: -1.
(define-optional-syscall page-words "code:page-words/1" (subr (io sys) () int))
(define-optional-syscall exec-view "code:exec-view/1"
  (poly ((r region)) (subr (maxeff (io sys) (write r)) ((flatarrayof i64 r) int int) int)))
(define-syscall flush-code "code:flush/1"
  (poly ((r region)) (subr (maxeff (io sys) (read r)) ((flatarrayof i64 r) int int) unit)))
(define code (flatarrayof i64 @c) (make-flatarray (i64-flat) 1024 0))
(and (syscall-available? page-words) (syscall-available? exec-view)
     (syscall-available? flush-code))
(> (page-words) 0)
(exec-view code 0 (page-words))
(flush-code code 0 (page-words))
