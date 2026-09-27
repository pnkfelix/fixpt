; Rejected: a frozen list given straight to `set-car!` cannot be written
; either. (What is done to `const` is never masked away.)
(set-car! (letfreeze r (the (listof int r) (cons 1 nil))) 3)
