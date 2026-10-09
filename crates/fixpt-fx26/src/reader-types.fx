;;; The signature of `reader.fx`, its `parser-module`,
;;; as its clients use it (`TODO.md` §68): a module file of no state.

;;; ------------------------------------------------------------ signatures

;; What its clients use of it (`check-program.fx`).
;; The types it names, from the files that define them.
(define parser-types ((proj (load-module "fx26:parser-types.fx") @s @e @m @c @p)))
(define-type syn (select parser-types syn))
(define-type syns-a (select parser-types syns-a))
(define-type parser-sig
  (moduleof (val syn-symbol? (subr pure (syn) bool))
            (val syn-name (subr pure (syn) string))
            (val drop (subr (maxeff (read @globals) (read @s)) (syns-a int) syns-a))))
