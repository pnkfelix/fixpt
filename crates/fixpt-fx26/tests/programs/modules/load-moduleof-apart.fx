;; ! argument 2 is a (moduleof (desc buffer (productof (owner (select c1 counter)) (t c1..ticket)))
;; Two schedulers' types are apart: buffers made over one are not what the
;; client given the other takes.
(let* ((c1 ((proj (load-module "../module-files/made-core.fx") @heap pure)))
       (c2 ((proj (load-module "../module-files/made-core.fx") @heap pure)))
       (buffer ((proj (load-input "../module-files/made-buffer.fx") @heap pure) c1))
       (client ((proj (load-input "../module-files/made-client.fx") @heap pure) c2 buffer)))
  0)
