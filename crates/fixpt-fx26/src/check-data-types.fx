;;; The signature of `check-data.fx`, its `check-data-module`,
;;; as its clients use it (`TODO.md` §68): a module file of no state.

;;; ------------------------------------------------------------ signatures

;; What its clients use of it (`check-rules.fx`).
;; The types it names, from the files that define them.
(define check-types-types (load-module "fx26:check-types-types.fx"))
(define-type k-binders (select check-types-types k-binders))
(define-type k-map (select check-types-types k-map))
;; The types it names, from the files that define them.
(define-type k-regions (select check-types-types k-regions))
(define-type check-data-sig
  (moduleof (val k-is-data?
                 (subr (maxeff (alloc @t) (read @globals) (read @t) (write @t) spin)
                       (int)
                       bool))
            (val k-data-places-solved
                 (subr (maxeff (alloc @t)
                               (goto @z)
                               (read (globals dr k-bound-of k-map-find k-new-epoch r-heap))
                               (read @globals)
                               (read @s)
                               (read @t)
                               (write @t)
                               spin)
                       (k-binders k-binders k-map)
                       k-map))
            (val k-check-data
                 (subr (maxeff (alloc @t)
                               (goto @z)
                               (read
                                (globals k-cat3
                                         k-cat4
                                         k-cat5
                                         k-fail
                                         k-map-find
                                         k-quote-dvar
                                         k-region-show
                                         k-show-ty
                                         k-subst-region
                                         r-heap))
                               (read @globals)
                               (read @s)
                               (read @t)
                               (write @t)
                               spin)
                       (int k-regions k-map int int)
                       unit))))
