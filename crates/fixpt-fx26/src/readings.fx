;;; A reading's identity (`parser-ids.fx`): what every expression read
;;; from one text in one state of a session is of, beside its number.
;;; A module file of no state, which the parser, the conductor and the
;;; checker load (a syscall's definitions, which it makes, are a reading).

;; A reading: a digest of the session's state before it, `s`, and the text
;; read, never 0 (the Rust checker's facts are of reading 0 until the
;; compiler gives them the trees'). Not a count: what the text and the
;; state are decides it, so whoever reads the same text in the same state
;; makes the same, and needs to ask no one (`ids.rs`'s `reading_of` is the
;; same function). A fold of each character into 40 bits, by a multiplier
;; that keeps every step in a fixnum.
(define reading-of (->* (int string) int)
  (lambda (s text)
    (let* ((mask 1099511627775)
           (h (letrec ((go (subr (maxeff (read @globals) spin) (int int) int)
                         (lambda (i h)
                           (if (>= i (string-length text))
                               h
                               (go (+ i 1)
                                   (bitwise-and
                                    (+ (* h 1000003) (+ (char->integer (string-ref text i)) 1))
                                    mask))))))
                (go 0 (bitwise-and s mask)))))
      (if (= h 0) 1 h))))
