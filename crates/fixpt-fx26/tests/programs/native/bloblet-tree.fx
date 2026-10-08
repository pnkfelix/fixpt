;;; Mutable bloblets made and written in line natively (`TODO.md` §57): a
;;; tree of nodes, each `(bloblet (fields child child int) @heap)`, a child
;;; `(union int node)`; built, then every leaf replaced by a new node, an
;;; older bloblet given a younger one (the card it is in marked), then
;;; summed. Collecting often, the fields must live through each.
(define-type node (bloblet (fields (union int node) (union int node) int) @heap))
(define* build (subr (maxeff (alloc @heap) spin) (int) node)
  (lambda (d)
    (if (= d 0) (make-bloblet 0 0 0 1) (make-bloblet 0 (build (- d 1)) (build (- d 1)) d))))
(define* grow (subr (maxeff (read @heap) (write @heap) (alloc @heap) spin) (node int) unit)
  (lambda (n k)
    (let ((l (bloblet-ref n 0)) (r (bloblet-ref n 1)))
      (begin
        (if (int? l) (bloblet-set! n 0 (the node (make-bloblet 0 k 0 k))) (grow l (+ k 1)))
        (if (int? r) (bloblet-set! n 1 (the node (make-bloblet 0 0 k k))) (grow r (+ k 2)))))))
(define* total (subr (maxeff (read @heap) spin) ((union int node)) int)
  (lambda (x)
    (typecase x
      (int n n)
      (else b (+ (bloblet-ref b 2) (+ (total (bloblet-ref b 0)) (total (bloblet-ref b 1))))))))
(define* tree (subr (maxeff (read @heap) (write @heap) (alloc @heap) spin) (int) int)
  (lambda (d) (let ((t (build d))) (begin (grow t 1) (total t)))))
(tree 10)
