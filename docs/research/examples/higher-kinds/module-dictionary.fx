;; => 2
;; The lighter interim that works TODAY: "dictionary passing over
;; modules" (no arrow kinds, no defunctionalised brands). Two modules
;; with genuinely different representations both match `counter-like`,
;; and one dependent procedure (functor) is generic over which module it
;; gets, exactly as `tests/programs/modules/functor-abstract.fx` is
;; generic over one module. This is Path 2 with today's restriction
;; still in force: the abstract component `t` is kind `type`, standing
;; for "this container of `int`" as a whole, not for a reusable
;; constructor `t` could be applied at other element types within the
;; same functor call (see the note's "what this does not give you").
(define-type counter-like
  (moduleof (abs t type)
            (val empty t)
            (val insert (subr (maxeff (alloc @heap) (read @heap)) (int t) t))
            (val size (subr (read @heap) (t) int))))

;; Representation: a running count paired with the elements seen.
(define list-backed
  (module
    (define-generative t (pairof int (listof int @heap) @heap))
    (define empty t (up-t (cons 0 nil)))
    (define insert (subr (maxeff (alloc @heap) (read @heap)) (int t) t)
      (lambda (x s) (up-t (cons (+ 1 (car (down-t s))) (cons x (cdr (down-t s)))))))
    (define size (subr (read @heap) (t) int)
      (lambda (s) (car (down-t s))))))

;; Representation: the count alone, discarding the elements. A module
;; whose `insert` and `size` need no allocation still fits
;; `counter-like`'s `(alloc @heap)`/anything signature: sub-effecting.
(define count-only
  (module
    (define-generative t int)
    (define empty t (up-t 0))
    (define insert (subr pure (int t) t)
      (lambda (x s) (up-t (+ 1 (down-t s)))))
    (define size (subr pure (t) int)
      (lambda (s) (down-t s)))))

(define use-three
  (subr (maxeff (alloc @heap) (read @heap)) ((c counter-like) (select c t) int) int)
  (lambda (c s x) (with c (size (insert x s)))))

(+ (use-three list-backed (with list-backed empty) 7)
   (use-three count-only (with count-only empty) 9))
