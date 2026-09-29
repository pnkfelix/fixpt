;;; Standard operations as values, whatever the runtime primitive they run
;;; as (`char-downcase`), and `parse-nat`, which fails on a radix past 36.
(define* map-chars (subr (maxeff (alloc @heap) (read @heap) spin) ((subr pure (char) char) (listof char @heap)) (listof char @heap))
  (lambda (f cs) (if (null? cs) cs (cons (f (car cs)) (map-chars f (cdr cs))))))
(list->string (map-chars char-downcase (string->list "HeLLo")))
(+ (parse-nat "ff" 16) (parse-nat "-1" 10))
(parse-nat "12" 99)
