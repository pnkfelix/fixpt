;;; The names the expander makes fresh, numbered within each top-level form
;;; (`macros.rs`'s `Macros::form_begin`, alike): `%x:K.N`, `K` the form's
;;; key, `N` the count of names it made so far. A form's key is a hash of
;;; what was written (`syn-hash`), and, past the first form of that hash,
;;; how many came before it, `H-1`, `H-2`: two forms' keys are never one, so
;;; neither are their names, and a form's names are of it and the macros it
;;; uses alone, not of how many names the forms before it made. A module
;;; file's own forms count apart, their keys `mH`, the program's state put
;;; back after (`fresh-scope-begin!`).

(module-parameters ((rs region) (re region) (rm region) (rc region) (rp region)))
(define parser-module ((proj (load-module "fx26:parser.fx") rs re rm rc rp)))
(define reader-types (with parser-module reader-types))
(import reader-types atom lst dotted vec (type syn))
(import parser-module (type syns-a))

;; The form's key, the names it made, the binders the resolution renamed
;; (`%x~K.N`, `macros-shapes.fx`), and each key's hash with how many forms
;; had it; whether the forms are a module file's.
(define form-key (ref string rs) (new ""))
(define fresh-count (ref int rs) (new 0))
(define captors-made (ref int rs) (new 0))
(define-type seen-keys (listof (tupleof int int) acyclic))
(define keys-seen (ref seen-keys rs) (new nil))
(define in-module (ref bool rs) (new #f))

;; A hash of `s`'s symbols, strings and shape, as the Rust one's
;; (`macros.rs`'s `syn_hash`): any other atom is its kind alone.
(define hash-p int 2147483647)
(define mix (->* (int int) int) (lambda (h x) (remainder (+ (* h 65599) x) hash-p)))
(define syn-hash (->* (syn) int)
  (lambda (s)
    (tagcase s
      (atom (d a b x)
        (cond ((symbol? d) (mix 1 (remainder (string-hash (symbol->string d)) hash-p)))
              ((string? d) (mix 2 (remainder (string-hash d) hash-p)))
              (else 3)))
      (lst (xs d a b x) (syns-hash 4 xs))
      (dotted (xs t d a b x) (mix (syns-hash 5 xs) (syn-hash t)))
      (vec (xs d a b x) (syns-hash 6 xs)))))
(define syns-hash (->* (int syns-a) int)
  (lambda (h xs) (if (null? xs) h (syns-hash (mix h (syn-hash (car xs))) (cdr xs)))))

;; Form `s` begun: its key, and its names counted from none.
(define form-begin! (->* (syn) unit)
  (lambda (s)
    (let* ((h (syn-hash s)) (n (seen-count h (get keys-seen))))
      (begin (set keys-seen (cons (tuple h (+ n 1)) (get keys-seen)))
             (set form-key (string-append (if (get in-module) "m" "") (int->string h)
                                          (if (= n 0) "" (string-append "-" (int->string n)))))
             (set fresh-count 0)
             (set captors-made 0)))))
(define seen-count (->* (int seen-keys) int)
  (lambda (h ks)
    (cond ((null? ks) 0)
          ((= h (extract (car ks) 1)) (extract (car ks) 2))
          (else (seen-count h (cdr ks))))))
;; The next name's tag, `K.N`.
(define fresh-tag (->* () string)
  (lambda ()
    (begin (set fresh-count (+ (get fresh-count) 1))
           (string-append (get form-key) "." (int->string (get fresh-count))))))
;; The next renamed binder's tag, counted apart.
(define captor-tag (->* () string)
  (lambda ()
    (begin (set captors-made (+ (get captors-made) 1))
           (string-append (get form-key) "." (int->string (get captors-made))))))

;; A module file's forms begun: their keys their own; what is given back
;; puts the program's back (`fresh-scope-end!`).
(define-type fresh-saved (tupleof string int int seen-keys bool))
(define fresh-scope-begin! (->* () fresh-saved)
  (lambda ()
    (let ((s (tuple (get form-key) (get fresh-count) (get captors-made) (get keys-seen)
                    (get in-module))))
      (begin (set keys-seen nil) (set in-module #t) s))))
(define fresh-scope-end! (->* (fresh-saved) unit)
  (lambda (s)
    (begin (set form-key (extract s 1)) (set fresh-count (extract s 2))
           (set captors-made (extract s 3)) (set keys-seen (extract s 4))
           (set in-module (extract s 5)))))
;; The state a session keeps after a form, and puts back before the next.
(define seen-now (->* () seen-keys) (lambda () (get keys-seen)))
(define seen! (->* (seen-keys) unit) (lambda (ks) (set keys-seen ks)))
