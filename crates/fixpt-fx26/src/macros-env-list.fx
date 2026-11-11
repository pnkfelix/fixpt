;;; The expander's environments as a list of levels, innermost first
;;; (`macros-env-types.fx`'s `env-ops`): the plain one, which
;;; `macros-env-indexed.fx` is held to. A name is looked for through every
;;; level, so a module of `n` items, a rib each, costs `n` for each name
;;; looked for in it. A module file of no state.

(module-parameters ((rs region) (re region) (rm region) (rc region) (rp region)))
(define env-types ((proj (load-module "fx26:macros-env-types.fx") rs re rm rc rp)))
(import env-types lv-rib lv-cage lv-earlier lv-shape (type level levels namer looked))
(define types-module (with env-types types-module))
(import types-module atm-lit (type atm atms))

;; Abstract outside this file by what is imported of it: `macros-nodes.fx`
;; takes the type and the operations, never `env-of` (a datatype, since a
;; type `define-generative` makes, of a module a file makes, cannot be named
;; in that file's own type: `TODO.md` §235).
(define-datatype env (env-of levels))
(define down-env (->* (env) levels) (lambda (e) (tagcase e (env-of (x) x))))
(define env-empty env (env-of nil))
(define env-within (->* (env levels namer) env)
  (lambda (e ls name) (env-of (append ls (down-env e)))))
(define env-levels (->* (env) levels) (lambda (e) (down-env e)))
(define env-any-shape? (->* (env) bool) (lambda (e) (any-shape-level? (down-env e))))
(define any-shape-level? (->* (levels) bool)
  (lambda (ls)
    (and (not (null? ls))
         (or (tagcase (car ls) (lv-shape (m) #t) (else y #f)) (any-shape-level? (cdr ls))))))
(define env-lookup (->* (env symbol bool int namer) looked)
  (lambda (e n d from name) (looked-in (dropped (down-env e) from) n d from name)))
(define dropped (->* (levels int) levels)
  (lambda (ls k) (if (or (= k 0) (null? ls)) ls (dropped (cdr ls) (- k 1)))))
(define looked-in (->* (levels symbol bool int namer) looked)
  (lambda (ls n d k name)
    (if (null? ls)
        (tuple -1 -1 k)
        (let ((next (+ k 1)))
          (tagcase (car ls)
            (lv-rib (as)
              (let ((b (named n d as name)))
                (if (>= b 0) (tuple 0 b next) (looked-in (cdr ls) n d next name))))
            (lv-earlier (as)
              (let ((b (named n d as name)))
                (if (>= b 0) (tuple 0 b next) (looked-in (cdr ls) n d next name))))
            (lv-cage (c) (looked-in (cdr ls) n d next name))
            (lv-shape (m) (tuple 1 m next)))))))
;; The first binder of `as` named `n`, a description's if `d`; -1 if none.
(define named (->* (symbol bool atms namer) int)
  (lambda (n d as name)
    (if (null? as)
        -1
        (tagcase (car as)
          (atm-lit (b e)
            (if (and (eq? d e) (let ((m (name b))) (and (not (null? m)) (symbol=? (car m) n))))
                b
                (named n d (cdr as) name)))
          (else y (named n d (cdr as) name))))))
