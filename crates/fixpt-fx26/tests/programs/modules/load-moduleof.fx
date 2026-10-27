;; => 15
;; Files that are functions of the modules they use, each parameter typed by
;; what a file makes (`docs/research/derived-signatures.md`), made once each
;; and given along: 7 twice, and the first ticket.
(define main
  (lambda ()
    (let* ((core ((proj (load-module "../module-files/made-core.fx") @heap pure)))
           (buffer ((proj (load-input "../module-files/made-buffer.fx") @heap pure) core))
           (client ((proj (load-input "../module-files/made-client.fx") @heap pure) core buffer))
           (b ((with buffer make) 7)))
      (+ ((with client twice) b) ((with client ticket-of) b)))))
(main)
