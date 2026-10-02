;; PROPOSED — Path 2 extended (an arrow-kinded module component). None
;; of this parses today: `(abs t type)` is the only shape the checker
;; accepts (`crates/fixpt-fx26/src/parse.rs:1515-1524`,
;; `crates/fixpt-fx26/src/check-modules.fx:67-70`, both hard-coding the
;; literal symbol `"type"`), confirmed by the existing negative test
;; `crates/fixpt-fx26/tests/programs/modules/abs-kind.fx`: "an abstract
;; component is a `type`, for now". Confirmed by running
;; `target/release/fixpt check` on this file (2026-10-02): both
;; checkers reject it at line 22 col 20 (the `(abs f (=> type type))`),
;; with exactly that message.
;;
;; Contrast this with `docs/research/examples/higher-kinds/
;; module-dictionary.fx`, which checks TODAY but is stuck at kind
;; `type`: each module there is a dictionary for containers-of-`int`
;; specifically. Here `f` is kind `(=> type type)`, so ONE module value
;; packages a container SHAPE, reusable at any element type within a
;; single functor call — the thing today's modules cannot express
;; (FX-91 report §2.2.6 already allowed "any kind" for `abs`, including
;; `(->> k …)`; FX-26 has not yet revisited that for modules —
;; `docs/research/first-class-modules.md:39-42,171`).
(define-type container-sig
  (moduleof (abs f (=> type type))
            (val empty (poly ((a type)) (f a)))
            (val insert (poly ((a type)) (subr (alloc @heap) (a (f a)) (f a))))
            (val fmap (poly ((a type) (b type))
                        (subr pure ((subr pure (a) b) (f a)) (f b))))))

(define list-container
  (module
    (define-generative f (=> type type))        ; PROPOSED: a generative
                                                  ; type CONSTRUCTOR, not
                                                  ; a generative type.
    (define empty (poly ((a type)) (f a)) (plambda ((a type)) (up-f nil)))
    (define insert
      (poly ((a type)) (subr (alloc @heap) (a (f a)) (f a)))
      (plambda ((a type)) (lambda (x xs) (up-f (cons x (down-f xs))))))
    (define fmap
      (poly ((a type) (b type)) (subr pure ((subr pure (a) b) (f a)) (f b)))
      (plambda ((a type) (b type)) (lambda (g xs) (up-f (map-list g (down-f xs))))))))

;; A functor generic over ANY container shape, at ANY element type
;; within the one call — the capability Path 2 extended (or Path 1) adds
;; over `module-dictionary.fx`'s functor, which is fixed at `int`. The
;; element type `a` is a second binder on `double-all` itself, and
;; `(select c f)` is then applied to it, `((select c f) a)`: type
;; application in a procedure's type, needing a kind-arrow `select`.
(define double-all
  (poly ((a type))
    (subr pure ((c container-sig) (subr pure (a) a) ((select c f) a)) ((select c f) a)))
  (plambda ((a type))
    (lambda (c double xs) (with c (fmap double xs)))))
