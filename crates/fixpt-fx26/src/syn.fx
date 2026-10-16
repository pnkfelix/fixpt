;;; What the reader reads, `syn`, as the plain datum it reads as. A module
;;; file of the reader's regions, apart from the reader, so that the parser
;;; and any other client of `syn` load no reader: the eager reader, which
;;; holds continuations (`eager-reader-states.fx`), is the reader's own
;;; business (kayak's request, 2026-10-15).

(module-parameters ((rs region) (re region) (rm region) (rc region)))
(hide (define reader-types ((proj (load-module "fx26:eager-reader-types.fx") rs re rm rc))))
(import reader-types (type syn))

(define syn->datum (subr pure (syn) datum)
  (lambda (s)
    (tagcase s
      (atom (d a b) d)
      (lst (items d a b) d)
      (dotted (items tail d a b) d)
      (vec (items d a b) d))))
