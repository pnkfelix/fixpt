;;; The types of `check-modules.fx`, its `check-modules-module`: a module file of no
;;; state, which it loads, and so may its clients (`TODO.md` §68); its
;;; items in the order they were there.

;; The types these use, from the files that define them.
(define check-types-types (load-module "fx26:check-types-types.fx"))
(define-effect checks (select check-types-types checks))
(define-type k-ids (select check-types-types k-ids))
(define-type k-map (select check-types-types k-map))
(define-type k-parts (select check-types-types k-parts))
(define-type kxs (select check-types-types kxs))
;; A `define-rec`'s types and expressions, each type read before its
;; expression, as the Rust parser reads them.
(define-type k-rec-read (productof (1 k-ids) (2 kxs)))
;; Run `f`; an error it makes in the file read at `base` (`load-module`)
;; said at `a`..`b`, with where in the file, as the Rust checker says it.
(define-type k-thunk-unit (subr (maxeff checks spin) () unit))
;; Abstract types `abs` renamed for a binding, each `prefix` and its name:
;; the new ones, and what each old one becomes.
(define-type k-renamed (productof (1 k-parts) (2 k-map)))
