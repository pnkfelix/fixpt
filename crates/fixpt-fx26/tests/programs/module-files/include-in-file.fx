;; A module file including a module it makes, using its type by name.
(include ((proj (load-module "include-cell.fx") @heap)))
(define z (listof cell @heap) nil)
