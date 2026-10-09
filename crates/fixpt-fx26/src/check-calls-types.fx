;;; The types of `check-calls.fx`, its `check-calls-module`: a module file of no
;;; state, which it loads, and so may its clients (`TODO.md` §68); its
;;; items in the order they were there.
;; Whether a procedure of type `t` could be given itself: a cycle in `t`
;; runs through a parameter of a procedure (or the argument of a
;; continuation). A type that is merely recursive, as a list is, does not let
;; anything loop. `path`: the nodes on the way down, newest first, each with
;; whether it was reached through a parameter.
(define-type k-cpath (listof (pairof int bool @t) acyclic))
