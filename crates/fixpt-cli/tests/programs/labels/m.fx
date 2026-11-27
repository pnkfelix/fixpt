;; A module file a program loads, whose sum labels are bare (`bare_labels.rs`).
(define-type r (sumof (yes int) (#:no unit)))
(define one r (sum yes 1))
