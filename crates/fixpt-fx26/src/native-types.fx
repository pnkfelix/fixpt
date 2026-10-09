;;; The types of `native.fx`, and its signature as its clients use it: a
;;; module file of no state, which it loads, and so may its clients
;;; (`TODO.md` §68).

(define-effect assembles (maxeff (read @globals) (read @k) (write @k) (alloc @k)))
;; Writing the assembler's arrays, and looping; reading them to make lists.
(define-effect n-writes (maxeff (read @globals) (read @k) (write @k) spin))
(define-effect n-lists (maxeff (read @globals) (read @k) (alloc @k) spin))
;; The assembler's arrays; the code it gives; and that with where each
;; cell's code starts.
(define-type n-ints (arrayof int @k))
(define-type n-bools (arrayof bool @k))
(define-type n-instrs (listof int @k))
(define-type n-assembled (productof (1 n-instrs) (2 n-instrs)))
;; A branch to patch: where it is, its label, and for a conditional one
;; its condition or register.
(define-datatype n-fix
  (fix-b int int)
  (fix-bcond int int int)
  (fix-cbz int int int)
  (fix-cbnz int int int))
;; Traps raised in the code being emitted, placed after it: label, code,
;; detail; newest first.
(define-type n-stub-list (listof (productof (1 int) (2 int) (3 int)) @k))

;;; ------------------------------------------------------------ signatures

;; What the conductor names of the assembler, for `bootstrap.fx` and Rust.
(define-type native-sig
  (moduleof (val native-assemble (subr (maxeff assembles spin) (tword int int) n-assembled))))
