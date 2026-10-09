;;; The signature of `compile-twins.fx`, its `compile-twins-module`,
;;; as its clients use it (`TODO.md` §68): a module file of no state.

;;; ------------------------------------------------------------ signatures

;; What its clients use of it (`compile-programs.fx`).
(define-type compile-twins-sig
  (moduleof (val c-form-twins
                 (subr (maxeff (alloc @k)
                               (goto @y)
                               (read @globals)
                               (read @k)
                               (read @t)
                               (write @k)
                               spin)
                       ()
                       unit))))
