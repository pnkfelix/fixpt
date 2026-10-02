;; ! `(select nowhere t)`: `nowhere` is not bound here
;; `select` names a module bound where the type is checked.
(the (select nowhere t) 1)
