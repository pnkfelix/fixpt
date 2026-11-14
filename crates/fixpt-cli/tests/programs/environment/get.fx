;; A variable of the environment, read (`get-environment-variable`):
;; set, set empty, unset, and a name that cannot be one.
(define said (subr (io env-read) (string) string)
  (lambda (name)
    (tagcase (get-environment-variable name)
      (value v (string-append "=" v))
      (unset u "unset")
      (not-text u "not-text"))))
(list (said "FIXPT_TEST_SET") (said "FIXPT_TEST_EMPTY") (said "FIXPT_TEST_UNSET") (said "A=B")
      (said ""))
