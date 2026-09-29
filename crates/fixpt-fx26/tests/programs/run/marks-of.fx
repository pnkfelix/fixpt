; A continuation captured under a mark, and the mark read back out of it.
(define-effect marking (maxeff (write @m) (read @m) (alloc @l) (read (globals key t))))
(define t (prompt-tag (listof int @l) int marking @p)
  (make-continuation-prompt-tag))
(define key (mark-key int @m) (make-continuation-mark-key))

(prompt t
  (with-mark key 7
    (lambda () (call-with-composable-continuation (lambda (k) (marks-of k key)) t)))
  (lambda (v) nil))
