;; A diamond 40 deep, a procedure that reads no global at its bottom: walked
;; into, and nothing found.
;; `(chain m0 (m1 m2 …))`: m1 is `double` applied to m0, m2 to m1, and on:
;; a type made of the one below, twice, at each level.
(define-syntax chain
  (syntax-rules ()
    ((_ a (b)) (define b ((with #%toplevel double) a)))
    ((_ a (b c . rest))
     (begin (define b ((with #%toplevel double) a)) (chain b (c . rest))))))
(define-type elt-sig (moduleof (abs t type) (val v t)))
(define double
  (subr (alloc @heap) ((e : elt-sig))
        (moduleof (desc t (productof (1 (select e t)) (2 (select e t)))) (val v t)))
  (lambda ((e elt-sig))
    (module
      (define-type t (productof (1 (select e t)) (2 (select e t))))
      (define v t (product (1 (with e v)) (2 (with e v)))))))
(define m0 (module (define-type t (subr pure () int)) (define v t (lambda () 1))))
(chain m0
  (m1 m2 m3 m4 m5 m6 m7 m8 m9 m10 m11 m12 m13 m14 m15 m16 m17 m18 m19 m20 m21 m22 m23 m24 m25
   m26 m27 m28 m29 m30 m31 m32 m33 m34 m35 m36 m37 m38 m39 m40))
