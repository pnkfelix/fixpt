;;; A reading's identity (`parser-ids.fx`): what every expression read
;;; from one text in one state of a session is of, beside its number.
;;; A module file of the reader's regions and no state, which the parser,
;;; the conductor and the checker load (a syscall's definitions, which it
;;; makes, are a reading).

(module-parameters ((rs region) (re region) (rm region) (rc region)))
(hide (define reader-types ((proj (load-module "fx26:eager-reader-types.fx") rs re rm rc))))
(import reader-types (type syn))

;; A reading: a digest of the session's state before it, `s`, and the
;; trees read, never 0 (the Rust checker's facts are of reading 0 until the
;; compiler gives them the trees'). Not a count: what the trees and the
;; state are decides it, so whoever reads the same in the same state makes
;; the same, and needs to ask no one (`ids.rs`'s `reading_of` is the same
;; function). Of the trees, not the text: what the text says and not how,
;; no space, comment or spelling the reader makes the same tree of, and no
;; position, which is provenance (`docs/research/loads-and-places.md`, "A
;; reading is a digest, not a count"). Each piece folded into 40 bits, by a
;; multiplier that keeps every step in a fixnum: a character as its code, a
;; mark as a code past every character's, each tree its kind's mark first,
;; a name, a string or a number's digits ended by one, so that no two
;; trees fold alike as a sequence.
(define reading-of (->* (int (listof syn acyclic)) int)
  (lambda (s forms)
    (let ((h (fold-trees (bitwise-and s 1099511627775) forms))) (if (= h 0) 1 h))))

;; A form's reading (`docs/research/loads-and-places.md`, "Decided: three
;; keys"): the session's state before it, `s`, folded with the switches the
;; checker is set to (`checked-settings`), the form's trees, and each file
;; the form loads first, by its key and its trees, in the order of the
;; keys; never 0. The state after the form, which the next is read in: so a
;; session's state is the same however its forms were split into texts.
;; `ids.rs`'s `form_reading` is the same function.
(define-type loads (listof (productof (1 string) (2 (listof syn acyclic))) acyclic))
(define form-reading (->* (int string syn loads) int)
  (lambda (s settings form ls)
    (let ((h (fold-loads (fold-tree (fold-text (bitwise-and s 1099511627775) settings) form)
                         (sort-loads ls nil))))
      (if (= h 0) 1 h))))
;; Each file: its key after mark 17, its trees, an end.
(define fold-loads (->* (int loads) int)
  (lambda (h ls)
    (if (null? ls)
        h
        (fold-loads (fold1 (fold-trees (fold-run h 17 (extract (car ls) 1)) (extract (car ls) 2))
                           (mark 0))
                    (cdr ls)))))
;; `ls` in the order of their keys, onto `out`, sorted.
(define sort-loads (->* (loads loads) loads)
  (lambda (ls out) (if (null? ls) out (sort-loads (cdr ls) (insert-load (car ls) out)))))
(define insert-load (->* ((productof (1 string) (2 (listof syn acyclic))) loads) loads)
  (lambda (l out)
    (cond ((null? out) (the loads (cons l nil)))
          ((string<? (extract l 1) (extract (car out) 1)) (the loads (cons l out)))
          (else (the loads (cons (car out) (insert-load l (cdr out))))))))

;; A session's state where its checker begins in the standard environment
;; `standard` (as read): its trees' reading, in no state before
;; (`ids.rs`'s `standard_state`).
(define standard-state (->* ((listof syn acyclic)) int) (lambda (standard) (reading-of 0 standard)))
;; The state `s`, as a staged step's text is read in it: with the type it is
;; checked against, `rep`, and the types its names are given, `named`, each
;; a rep's bytes, folded in (`ids.rs`'s `with_reps`): what checking it reads
;; beside the session's state and its trees. None, `s` as it is.
(define with-reps
  (->* (int (bytevectorof @t) (listof (productof (1 symbol) (2 (bytevectorof @t))) acyclic)) int)
  (lambda (s rep named)
    (letrec ((go (subr (maxeff (read @globals) (read @t) spin)
                       (int (listof (productof (1 symbol) (2 (bytevectorof @t))) acyclic)) int)
               (lambda (h ns)
                 (if (null? ns)
                     h
                     (go (fold-rep (fold-run h 19 (symbol->string (extract (car ns) 1)))
                                   (extract (car ns) 2))
                         (cdr ns))))))
      (if (and (= (bytevector-length rep) 0) (null? named))
          s
          (let ((h (go (fold-rep (fold1 (bitwise-and s 1099511627775) (mark 18)) rep) named)))
            (if (= h 0) 1 h))))))
;; A rep's bytes, then an end.
(define fold-rep (->* (int (bytevectorof @t)) int)
  (lambda (h b)
    (letrec ((go (subr (maxeff (read @globals) (read @t) spin) (int int) int)
               (lambda (i h)
                 (if (>= i (bytevector-length b))
                     (fold1 h (mark 0))
                     (go (+ i 1) (fold1 h (u8->int (bytevector-u8-ref b i))))))))
      (go 0 h))))

;; The reading of a form read before, `r`, read again in the state `s` (a
;; definition checked again after a name it uses was redefined: `k-rerun`),
;; never 0 (`ids.rs`'s `read_again`): of the form, which `r` decides, and
;; of the state it is checked in now.
(define read-again-reading (->* (int int) int)
  (lambda (s r)
    (let ((h (fold1 (fold1 (bitwise-and s 1099511627775) (mark 20)) (bitwise-and r 1099511627775))))
      (if (= h 0) 1 h))))

;; The reading of a text that is no trees (a syscall's definitions, which
;; the checker makes): its characters, in `s`, `reading-of`'s fold.
(define text-reading-of (->* (int string) int)
  (lambda (s text)
    (let ((h (fold-text (bitwise-and s 1099511627775) text))) (if (= h 0) 1 h))))

;; One piece `x`, a character's code or a mark, folded into `h`.
(define fold1 (->* (int int) int)
  (lambda (h x) (bitwise-and (+ (* h 1000003) (+ x 1)) 1099511627775)))
;; Mark `m`: past every character's code.
(define mark (->* (int) int) (lambda (m) (+ 1114112 m)))

(define fold-text (->* (int string) int)
  (lambda (h text)
    (letrec ((go (subr (maxeff (read @globals) spin) (int int) int)
               (lambda (i h)
                 (if (>= i (string-length text))
                     h
                     (go (+ i 1) (fold1 h (char->integer (string-ref text i))))))))
      (go 0 h))))
;; `text`'s characters after mark `m`, then the end's mark, 0.
(define fold-run (->* (int int string) int)
  (lambda (h m text) (fold1 (fold-text (fold1 h (mark m)) text) (mark 0))))

(define fold-trees (->* (int (listof syn acyclic)) int)
  (lambda (h xs) (if (null? xs) h (fold-trees (fold-tree h (car xs)) (cdr xs)))))
;; The marks: 0 an end, 1 a list, 2 a list's end, 3 a dotted list, 4 its
;; dot, 5 a vector, 6 a name, 7 a keyword, 8 a string, 9 a character, 10 an
;; integer, 11 a float (its bits), 12 true, 13 false, 14 a bytevector, its
;; bytes, 15 a ratio's numerator and then its denominator, in lowest terms,
;; 16 any other atom, of which the reader makes none; 17 a file loaded
;; (`form-reading`), 18 a staged step's rep, 19 a name it gives a type
;; (`with-reps`), 20 a form read again (`read-again-reading`).
(define fold-tree (->* (int syn) int)
  (lambda (h x)
    (tagcase x
      (lst (items d a b) (fold1 (fold-trees (fold1 h (mark 1)) items) (mark 2)))
      (dotted (items tail d a b)
        (fold1 (fold-tree (fold1 (fold-trees (fold1 h (mark 3)) items) (mark 4)) tail) (mark 2)))
      (vec (items d a b) (fold1 (fold-trees (fold1 h (mark 5)) items) (mark 2)))
      (atom (d a b)
        (cond ((null? d) (fold1 (fold1 h (mark 1)) (mark 2)))
              ((symbol? d) (fold-run h 6 (symbol->string d)))
              ((keyword? d) (fold-run h 7 (symbol->string (keyword->symbol d))))
              ((string? d) (fold-run h 8 d))
              ((char? d) (fold1 (fold1 h (mark 9)) (char->integer d)))
              ((int? d) (fold-run h 10 (int->string d)))
              ((f64? d) (fold-run h 11 (int->string (u64->int (f64->bits d)))))
              ((datum-rational? d)
               (fold-run (fold-run h 15 (int->string (datum-numerator d)))
                         15 (int->string (datum-denominator d))))
              ((bool? d) (fold1 h (mark (if d 12 13))))
              ((bytevector? d) (fold-bytes (fold1 h (mark 14)) d))
              (else (fold1 h (mark 16))))))))
(define fold-bytes (->* (int datum) int)
  (lambda (h v)
    (letrec ((go (subr (maxeff (read @globals) spin) (int int) int)
               (lambda (i h)
                 (if (>= i (datum-bytevector-length v))
                     (fold1 h (mark 0))
                     (go (+ i 1) (fold1 h (datum-bytevector-ref v i)))))))
      (go 0 h))))
