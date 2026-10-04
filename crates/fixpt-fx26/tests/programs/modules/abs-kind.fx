;; ! an abstract component is a `type`, or a type constructor `(=> kind … type)`, for now
;; An abstract component of a module type is a type, or a type constructor (a
;; description function to a type), for now: not a region.
(define-type bad (moduleof (abs t region) (val zero t)))
