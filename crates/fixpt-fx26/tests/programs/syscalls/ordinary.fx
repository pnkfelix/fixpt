;;; An ordinary program may not declare a syscall: only a runtime's own code
;;; may, a module file built in or a program its driver was told is one.
(define-optional-syscall page-words "code:page-words/1" (subr (io sys) () int))
