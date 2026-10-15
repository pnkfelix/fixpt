;; ! `(import module name … (type name …) (effect name …))`: a name
;; An `import` defines names.
(define m (module (define x 1)))
(import m (type 3))
