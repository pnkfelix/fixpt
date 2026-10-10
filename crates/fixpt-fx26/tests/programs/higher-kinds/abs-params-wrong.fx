;; ! an abstract type constructor is `(abs (f (name kind) …) type)`
;; A list after `abs` is names, or one constructor and its parameters; not
;; both. (It once read as `(abs f type)`, the parameter passed over.)
(define-type bad (moduleof (abs (f g (a type)) type)))
