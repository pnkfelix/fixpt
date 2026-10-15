;; ! `(import module name … (type name …) (effect name …))`: the module, named by a variable
;; An `import` names its module by a variable.
(import (module (define x 1)) x)
