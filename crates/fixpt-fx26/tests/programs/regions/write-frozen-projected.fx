; Rejected: nor with `set-car!` projected at `const` by hand.
((proj (proj set-car! const) int (listof int const)) (letfreeze r (the (listof int r) (cons 1 nil))) 3)
