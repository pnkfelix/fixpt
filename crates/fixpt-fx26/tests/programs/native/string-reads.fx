;;; Strings read in line natively: `string=?` of every two of some strings
;;; (empty; odd and even lengths; the same but for the last character, in
;;; a word's low half or its high half; a prefix; a character past 16 bits;
;;; made at run time, and literal), `string-ref` summed, `string-length`.
(define-type strs (listof string @heap))
(define* char-sum (subr (maxeff spin) (string int int) int)
  (lambda (s i acc)
    (if (>= i (string-length s))
        acc
        (char-sum s (+ i 1) (+ acc (char->integer (string-ref s i)))))))
(define* equals (subr (maxeff (read @heap) spin) (string strs int) int)
  (lambda (s ss acc)
    (if (null? ss) acc (equals s (cdr ss) (if (string=? s (car ss)) (+ acc 1) acc)))))
(define* pairs (subr (maxeff (read @heap) spin) (strs strs int) int)
  (lambda (ss all acc)
    (if (null? ss)
        acc
        (pairs (cdr ss) all
               (+ (* acc 7) (+ (equals (car ss) all 0)
                               (+ (char-sum (car ss) 0 0) (string-length (car ss)))))))))
(define* words (subr (maxeff (alloc @heap)) (int) strs)
  (lambda (n)
    (let ((far (list->string (list #\a (integer->char 128512)))))
      (list "" "a" (string-append "a" "b") "abc" "abd" "abcd" "abce" (string-append "ab" "c")
            "ab" far (list->string (list #\a (integer->char 128513))) (string-append far "")
            (int->string n)))))
(define* string-reads (subr (maxeff (alloc @heap) (read @heap) spin) (int) int)
  (lambda (n) (let ((ws (words n))) (pairs ws ws 0))))
(string-reads 1000)
