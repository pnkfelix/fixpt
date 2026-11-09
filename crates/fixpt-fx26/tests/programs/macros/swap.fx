;; => (2 1)
;; Herman's hygiene example, over cells: the template's `tmp` against the
;; use's own `tmp`.
(define-syntax swap!
  ;; As named: ((a id) (b id))
  (id id)
  (syntax-rules ()
    ((_ a b) (let ((tmp (get a))) (begin (set a (get b)) (set b tmp))))))
(let ((tmp (new 1)) (other (new 2)))
  (begin (swap! tmp other) (list (get tmp) (get other))))
