;;; Characters, symbols and strings read in line natively (TODO.md §126):
;;; `char-whitespace?` of every code point below 0x100 and of some above
;;; (Unicode's, the primitive's), `char->integer`, `char-in?` in an empty
;;; string, a short one and a long, `string<?` of every two of some strings
;;; (empty; a prefix; equal; differing early, late, past 16 bits), and
;;; `symbol-name-hash` as `string->symbol` gives it.
(define-type strs (listof string @heap))
(define* spaces (subr spin (int int int) int)
  (lambda (i n acc)
    (if (>= i n)
        acc
        (spaces (+ i 1) n
                (if (char-whitespace? (integer->char i))
                    (+ (* acc 3) i)
                    (remainder acc 1000003))))))
(define* far-spaces (subr spin () int)
  (lambda ()
    (+ (+ (spaces 133 134 0) (spaces 160 161 0)) (+ (+ (spaces 5760 5761 0) (spaces 8192 8203 0))
       (+ (+ (spaces 8232 8234 0) (spaces 12288 12289 0)) (spaces 1000 1001 0))))))
(define* points (subr spin (string int int) int)
  (lambda (s i acc)
    (if (>= i (string-length s))
        acc
        (points s (+ i 1) (+ (* acc 31) (char->integer (string-ref s i)))))))
(define* ins (subr spin (string int int) int)
  (lambda (s i acc)
    (if (>= i 130)
        acc
        (ins s (+ i 1)
             (if (char-in? (integer->char i) s) (+ (* acc 2) i) (remainder acc 999983))))))
(define* below (subr (maxeff (read @heap) spin) (string strs int) int)
  (lambda (s ss acc)
    (if (null? ss) acc (below s (cdr ss) (if (string<? s (car ss)) (+ (* acc 2) 1) (* acc 2))))))
(define* pairs (subr (maxeff (read @heap) spin) (strs strs int) int)
  (lambda (ss all acc)
    (if (null? ss)
        acc
        (pairs (cdr ss) all (remainder (+ (* acc 7) (below (car ss) all 0)) 1000003)))))
(define* hashes (subr (maxeff (read @heap) spin) (strs int) int)
  (lambda (ss acc)
    (if (null? ss)
        acc
        (hashes (cdr ss) (remainder (+ (* acc 5) (symbol-name-hash (string->symbol (car ss))))
                                    1000003)))))
(define* char-reads (subr (maxeff (alloc @heap) (read @heap) spin) (int) int)
  (lambda (n)
    (let* ((far (list->string (list #\a (integer->char 128512))))
           (ws (the strs (list "" "a" "ab" "abc" "abd" "b" "ab" far (string-append far "a")
                               (int->string n) " \t\n" "zzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzz~"))))
      (+ (+ (+ (spaces 0 256 0) (far-spaces)) (+ (points far 0 0) (points (int->string n) 0 0)))
         (+ (+ (ins "" 0 0) (+ (ins " \t\n" 0 0) (ins "zzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzz~" 0 0)))
            (+ (pairs ws ws 0) (hashes ws 0)))))))
(char-reads 1000)
