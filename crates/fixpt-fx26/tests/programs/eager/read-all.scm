;;; Feeding a whole string to each eager reader, from Scheme. `fx:` names are
;;; the FX-26 reader's, lowered; the unprefixed ones are the Scheme reader's.
(define (fx-read-all text)
  (let loop ((st (fx:eager-start)) (i 0))
    (cond ((not (eq? (fx:eager-state-kind st) 'need)) st)
          ((= i (string-length text)) (fx:eager-feed st #\newline))
          (else (loop (fx:eager-feed st (string-ref text i)) (+ i 1))))))
(define (fx-data text) (fx:eager-state-data (fx-read-all text)))

(define (feed-all start feed text)
  (let loop ((st (start)) (cs (string->list text)))
    (if (null? cs) st (loop (feed st (car cs)) (cdr cs)))))
(define (fx-context text) (fx:eager-context (feed-all fx:eager-start fx:eager-feed text)))
(define (scheme-context text) (eager-context (feed-all eager-start eager-feed text)))
