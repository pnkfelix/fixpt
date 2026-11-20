;;; Text the expander written in FX-26 writes and reads of its own, which
;;; no syntax type is of, for `macros-procedural.fx`: a datum written as the
;;; reader reads it back (`syn-text`'s atoms); a phase-1 form as it is held,
;;; its text with the directory of its file (`phase1.rs`'s `Form`); and the
;;; place a refusal of one is at, as the runtime answers it, and the part
;;; of the form there. Of no state.

(module-parameters ((rs region) (re region) (rm region) (rc region) (rp region)))
(hide (define parser-types ((proj (load-module "fx26:parser-types.fx") rs re rm rc rp))))
(import parser-types (type syn syns-a))

;;; ------------------------------------------------------------ data

;; `s` as text the reader reads back.
(define syn-text (->* (syn) string)
  (lambda (s)
    (tagcase s
      (atom (d a b x) (datum-text d))
      (lst (items d a b x) (string-append "(" (syns-text items) ")"))
      (dotted (items tail d a b x)
        (string-append "(" (syns-text items) " . " (syn-text tail) ")"))
      (vec (items d a b x) (string-append "#(" (syns-text items) ")")))))
(define syns-text (->* (syns-a) string)
  (lambda (xs)
    (cond ((null? xs) "")
          ((null? (cdr xs)) (syn-text (car xs)))
          (else (string-append (syn-text (car xs)) " " (syns-text (cdr xs)))))))

;; `d`, an atom, as text the reader reads back.
(define datum-text (->* (datum) string)
  (lambda (d)
    (cond ((null? d) "()")
          ((symbol? d) (symbol->string d))
          ((keyword? d) (string-append "#:" (symbol->string (keyword->symbol d))))
          ((string? d) (string-append "\"" (escaped d 0 "") "\""))
          ((char? d) (char-text d))
          ((int? d) (int->string d))
          ((f64? d) (f64->string d))
          ((bool? d) (if d "#t" "#f"))
          (else "#u"))))
(define escaped (->* (string int string) string)
  (lambda (s i out)
    (if (>= i (string-length s))
        out
        (let ((c (string-ref s i)))
          (escaped s (+ i 1)
                   (string-append out (cond ((char=? c #\") "\\\"")
                                            ((char=? c #\\) "\\\\")
                                            ((char=? c (integer->char 10)) "\\n")
                                            (else (char->string c)))))))))
(define char-text (->* (char) string)
  (lambda (c)
    (cond ((char=? c #\space) "#\\space")
          ((char=? c (integer->char 10)) "#\\newline")
          ((char=? c (integer->char 9)) "#\\tab")
          (else (string-append "#\\" (char->string c))))))

;;; ------------------------------------------------------------ phase 1

;; The directory of the file of key `key` (`TODO.md` §68's, `input:` or not)
;; as a phase-1 form names it: up to its last `/`, kept; `""` if it has none
;; (`phase1.rs`'s `dir_of_key`).
(define key-dir (->* (string) string)
  (lambda (key)
    (let* ((w (string-length "input:"))
           (path (if (and (>= (string-length key) w) (string=? (substring key 0 w) "input:"))
                     (substring key w (string-length key))
                     key)))
      (substring path 0 (+ 1 (last-slash path (- (string-length path) 1)))))))
;; The place of the last `/` in `s` at or before `i`; -1 if none.
(define last-slash (->* (string int) int)
  (lambda (s i)
    (cond ((< i 0) -1) ((char=? (string-ref s i) #\/) i) (else (last-slash s (- i 1))))))
;; Phase-1 form `text`, written in a file of directory `dir`, as it is held:
;; the directory's length, `:`, the directory, then the text (`Form::decoded`).
(define phase1-form (->* (string string) string)
  (lambda (dir text) (string-append (int->string (string-length dir)) ":" dir text)))

;; A refusal of phase-1 forms, as the runtime says it (`Refused::answer`):
;; `@I S E` and a newline first where it is at a place, character `S` to `E`
;; of form `I`'s text. Its place, in a list of one, or none.
(define refusal-place
  (->* (string) (listof (productof (1 int) (2 int) (3 int)) acyclic))
  (lambda (why)
    (if (and (> (string-length why) 0) (char=? (string-ref why 0) #\@))
        (let* ((i (digits-end why 1)) (s (digits-end why (+ i 1))) (e (digits-end why (+ s 1))))
          (list (product (1 (digits-of why 1 i 0)) (2 (digits-of why (+ i 1) s 0))
                         (3 (digits-of why (+ s 1) e 0)))))
        nil)))
;; What it says, its place left out.
(define refusal-message (->* (string) string)
  (lambda (why)
    (if (null? (refusal-place why))
        why
        (let ((n (line-end why 0)))
          (if (< n (string-length why)) (substring why (+ n 1) (string-length why)) "")))))
(define line-end (->* (string int) int)
  (lambda (s i)
    (cond ((>= i (string-length s)) i) ((char=? (string-ref s i) (integer->char 10)) i)
          (else (line-end s (+ i 1))))))
;; Where the digits from `i` of `s` end.
(define digits-end (->* (string int) int)
  (lambda (s i)
    (if (and (< i (string-length s)) (char-numeric? (string-ref s i))) (digits-end s (+ i 1)) i)))
;; The number digits `i` to `j` of `s` write, after `n`.
(define digits-of (->* (string int int int) int)
  (lambda (s i j n)
    (if (>= i j)
        n
        (digits-of s (+ i 1) j
                   (+ (* 10 n) (- (char->integer (string-ref s i)) (char->integer #\0)))))))
(define phase1-forms-of (->* (string syns-a) (listof string acyclic))
  (lambda (dir xs)
    (if (null? xs)
        nil
        (cons (phase1-form dir (syn-text (car xs))) (phase1-forms-of dir (cdr xs))))))
;; Where a refusal of phase-1 forms at `place` is said: in a form of `new`
;; (after `old` of them in force), the part whose text holds it; else at
;; `s`, the `begin-for-syntax` (`Macros::for_syntax`).
(define refused-part
  (->* (syn syns-a int (listof (productof (1 int) (2 int) (3 int)) acyclic)) syn)
  (lambda (s new old place)
    (if (null? place)
        s
        (let ((i (- (extract (car place) 1) old)))
          (if (and (>= i 0) (< i (length new)))
              (syn-at (nth-syn new i) (extract (car place) 2))
              s)))))
;; The deepest part of `s` whose text, as `s` is written (`syn-text`), holds
;; its character `at`; `s` if none does (`macros.rs`'s `written_part`).
(define syn-at (->* (syn int) syn)
  (lambda (s at)
    (tagcase s
      (lst (items d a b x) (syn-at-in s items at 1 nil))
      (dotted (items tail d a b x) (syn-at-in s items at 1 (list tail)))
      (vec (items d a b x) (syn-at-in s items at 2 nil))
      (else y s))))
(define syn-at-in (->* (syn syns-a int int syns-a) syn)
  (lambda (s xs at o tail)
    (if (null? xs)
        ;; ` . ` after the last item's space.
        (if (null? tail)
            s
            (let ((n (string-length (syn-text (car tail)))) (t-at (+ o 2)))
              (if (and (>= at t-at) (< at (+ t-at n))) (syn-at (car tail) (- at t-at)) s)))
        (let ((n (string-length (syn-text (car xs)))))
          (if (and (>= at o) (< at (+ o n)))
              (syn-at (car xs) (- at o))
              (syn-at-in s (cdr xs) at (+ (+ o n) 1) tail))))))
(define nth-syn (->* (syns-a int) syn)
  (lambda (xs i) (if (= i 0) (car xs) (nth-syn (cdr xs) (- i 1)))))
