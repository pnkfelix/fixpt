;;; The signature of `check-data.fx`, its `check-data-module`,
;;; as its clients use it (`TODO.md` §68): a module file of no state.

;;; ------------------------------------------------------------ signatures

;; What its clients use of it (`check-rules.fx`).
;; The types it names, from the files that define them.
(hide (define check-types-types (load-module "fx26:check-types-types.fx")))
(import check-types-types (type k-binders k-map))
;; The types it names, from the files that define them.
(import check-types-types (type k-regions k-ids k-atom) (effect kstate checks))
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
                       unit))
            (val k-addr-index int)
            (val k-inbox-index int)
            (val k-process-index int)
            (val k-untransmissible (subr (maxeff kstate spin) (int k-ids k-ids) string))
            (val k-crossing-atom? (subr (read @globals) (k-atom) bool))
            (val k-check-sendable (subr (maxeff checks spin) (int k-map int int) unit))))
