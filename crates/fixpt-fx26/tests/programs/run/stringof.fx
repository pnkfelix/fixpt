; Strings at a region, `(stringof r)` (the user's, 2026-10-28): made,
; written, filled and copied there; frozen by `letfreeze`, a `string`,
; nothing copied; made in a place; read by the operations a `string` has,
; at any region.
(define* joined (subr pure (string string) string)
  (lambda (a b)
    (letfreeze r
      (let ((out (the (stringof r) (make-string (+ (string-length a) (string-length b)) #\space))))
        (begin (string-copy! out 0 a 0 (string-length a))
               (string-copy! out (string-length a) b 0 (string-length b))
               out)))))
(define* upcased! (subr (maxeff (read @s) (write @s) spin) ((stringof @s) int) unit)
  (lambda (s i)
    (if (>= i (string-length s))
        #u
        (let ((c (string-ref s i)))
          (begin (if (and (char>=? c #\a) (char<=? c #\z))
                     (string-set! s i (integer->char (- (char->integer c) 32)))
                     #u)
                 (upcased! s (+ i 1)))))))
(joined "abc" "défg")
(string=? (joined "x" "y") "xy")
(let ((s (the (stringof @s) (string-copy "hello, world" 0 12))))
  (begin (upcased! s 0) (substring s 0 (string-length s))))
(let ((s (the (stringof @s) (make-string 3 #\a))))
  (begin (string-fill! s #\b) (string-set! s 1 #\c) (string->list s)))
(letrena p
  (let ((t (rmake-string p 4 #\z)))
    (begin (string-set! t 0 #\y) (string=? t "yzzz"))))
(string->utf8 (joined "é" "!"))
