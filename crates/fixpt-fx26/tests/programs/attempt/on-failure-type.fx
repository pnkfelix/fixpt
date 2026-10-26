;; ! `attempt`'s on-failure takes the failure's message
;; Refused: on-failure takes an int, not the failure's message.
(attempt 1 (lambda ((m int)) m))
