;;; The types of `regcode-entry.fx`, its `regcode-entry-module`: a module file of no
;;; state, which it loads, and so may its clients (`TODO.md` §68); its
;;; items in the order they were there.

;; The types these use, from the files that define them.
(define regcode-types (load-module "fx26:regcode-types.fx"))
(define-type rgen (select regcode-types rgen))
;; A top-level definition's name and word, in a list (`c-own-now`).
(define-type rowner (listof (productof (1 symbol) (2 tword)) @k))
;; What was made, in a list; none if declined.
(define-type rgens (listof rgen @k))
