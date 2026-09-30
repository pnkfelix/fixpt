;;; STRING-CONCAT -- concatenating three copies of a 2017-character string,
;;; and summing the characters' codes.
;;;
;;; From MLton's benchmark suite (benchmark/tests/string-concat.sml, commit
;;; aa2fd1ad9b91), ported to FX-26. Iteration count (ours; MLton's driver
;;; was not fetched): a loop from 4000 down to -1, 4001 concatenations.
;;; (The original's doit n counts down from n * 10000.)
;;; Answer: 468705, the sum (the original checks for it).
;;; CharVector.tabulate (through a list of characters, `list->string`),
;;; String.concat (of a list of strings, by `string-append` two at a time,
;;; FX-26 having no n-ary one) and CharVector.foldl are written here.

(define-type chars (listof char @l))

(define* tabulate (subr (maxeff (alloc @l) (read @l) spin) (int (subr pure (int) char)) string)
  (lambda (n f)
    (letrec ((build (subr (maxeff (alloc @l) spin) (int chars) chars)
               (lambda (i acc) (if (< i 0) acc (build (- i 1) (cons (f i) acc))))))
      (list->string (build (- n 1) nil)))))

(define* concat (subr (maxeff (read @l) spin) ((listof string @l)) string)
  (lambda (ss) (if (null? ss) "" (string-append (car ss) (concat (cdr ss))))))

(define* foldl (subr spin ((subr pure (char int) int) int string) int)
  (lambda (f b s)
    (letrec ((loop (subr spin (int int) int)
               (lambda (i acc) (if (< i (string-length s)) (loop (+ i 1) (f (string-ref s i) acc)) acc))))
      (loop 0 b))))

(define alpha string (tabulate 26 (lambda (i) (integer->char (+ (char->integer #\A) i)))))

;; The inputs, where no compiler can fold them: globals, which a later
;; definition may replace.
(define len int 2017)
(define iterations int 4000)

(define* doit (subr (maxeff (alloc @l) (read @l) spin) (int) int)
  (lambda (n)
    (let* ((alpha alpha)
           (s (tabulate len (lambda (i) (string-ref alpha (modulo i 26))))))
      (letrec ((loop (subr (maxeff (alloc @l) (read @l) spin (read (globals concat foldl))) (int int) int)
                 (lambda (n result)
                   (if (< n 0)
                       result
                       (loop (- n 1)
                             (foldl (lambda (c s) (+ s (char->integer c))) 0
                                    (concat (list s s s))))))))
        (loop n -1)))))
(doit iterations)
