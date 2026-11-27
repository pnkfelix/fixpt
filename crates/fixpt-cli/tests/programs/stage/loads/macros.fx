;;; Macros a module file gives, which a session's step imports
;;; (`session-macros.fx`).
(define-syntax thrice (syntax-rules ((_ e) (+ e (+ e e)))))
(define-syntax unless-zero (syntax-rules ((_ n e) (if (= n 0) 0 e))))
