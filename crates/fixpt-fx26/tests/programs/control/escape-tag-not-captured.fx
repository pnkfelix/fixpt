; Rejected: an escape-only tag is never captured with (TODO.md §89), so
; its prompts need bound nothing; `call-with-composable-continuation`
; takes a `prompt-tag`.
(define grab (subr (maxeff (alloc @r) (comefrom @r)) () int)
  (lambda ()
    (let ((t ((proj (proj make-escape-tag @r) int int))))
      (call-with-composable-continuation (lambda (k) 0) t))))
