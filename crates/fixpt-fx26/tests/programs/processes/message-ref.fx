;; ! a process's messages are copied to it, so they must be transmissible
;; A message is copied into its process: a reference cannot be.
(define w (addr (ref int @c) @w) (spawn (box (ref int @c) p) (set (receive box) 1)))
