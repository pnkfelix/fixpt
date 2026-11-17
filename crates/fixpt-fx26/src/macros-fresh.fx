;;; The names the expander makes fresh, numbered within each top-level form
;;; (`macros.rs`'s `Macros::form_begin`, alike): `%x:K.N`, `K` the form's
;;; key, `N` the count of names it made so far. A form's key is a hash of
;;; what was written (`syn-hash`), and, past the first form of that hash,
;;; how many came before it, `H-1`, `H-2`: two forms' keys are never one, so
;;; neither are their names, and a form's names are of it and the macros it
;;; uses alone, not of how many names the forms before it made. A module
;;; file's own forms count apart, their keys `m{F}mH`, `F` a hash of the
;;; file's key, the program's state put back after (`fresh-scope-begin!`);
;;; an importer's expansions of the file's uses, `m{F}mmH` (`file-prefix`).

(module-parameters ((rs region) (re region) (rm region) (rc region) (rp region)))
(define parser-module ((proj (load-module "fx26:parser.fx") rs re rm rc rp)))
(define reader-types (with parser-module reader-types))
(import reader-types atom lst dotted vec (type syn))
(import parser-module (type syns-a))

;; The form's key, the names it made, the binders the resolution renamed
;; (`%x~K.N`, `macros-shapes.fx`), its expansions, each by its number with
;; its tag (`expansion-begun!`), and each key's hash with how many forms had
;; it; the prefix of a module file's forms' keys, "" for a program's.
(define form-key (ref string rs) (new ""))
(define fresh-count (ref int rs) (new 0))
(define captors-made (ref int rs) (new 0))
(define expanded (ref int rs) (new 0))
(define-type tags (listof (tupleof int string) acyclic))
(define form-tags (ref tags rs) (new nil))
(define-type seen-keys (listof (tupleof int int) acyclic))
(define keys-seen (ref seen-keys rs) (new nil))
(define module-prefix (ref string rs) (new ""))

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
             (set form-key (string-append (get module-prefix) (int->string h)
                                          (if (= n 0) "" (string-append "-" (int->string n)))))
             (set fresh-count 0)
             (set captors-made 0)
             (set expanded 0)
             (set form-tags nil)))))
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

;; Expansion `made` begun: its tag, `K.N`, counted apart from the names'
;; (`macros.rs`'s `expansion_begun`), so that its aliases, `%~K.N:x`, are of
;; the form and the macros it uses alone.
(define expansion-begun! (->* (int) string)
  (lambda (made)
    (begin (set expanded (+ (get expanded) 1))
           (let ((t (string-append (get form-key) "." (int->string (get expanded)))))
             (begin (set form-tags (cons (tuple made t) (get form-tags))) t)))))
;; Expansion `made`'s tag, one of this form's; a template's check's (`made`
;; 0), `0`.
(define tag-of (->* (int) string) (lambda (made) (tag-in made (get form-tags))))
(define tag-in (->* (int tags) string)
  (lambda (made ts)
    (cond ((null? ts) "0")
          ((= made (extract (car ts) 1)) (extract (car ts) 2))
          (else (tag-in made (cdr ts))))))
;; Whether `c` may be in an expansion's tag: a form's key, `H`, `H-1`,
;; `m{F}mH` or `m{F}mmH`, and a count.
(define tag-char? (->* (char) bool)
  (lambda (c) (or (char-numeric? c) (char=? c #\.) (char=? c #\-) (char=? c #\m))))

;; The prefix of the keys of the forms of the module file of key `key`
;; (`input:` or not): `m{F}m` for its own expansion, `m{F}mm` for the uses
;; an importer expands (`imported`), `F` a hash of the key as a string's
;; (`macros.rs`'s `file_prefix`): no two files' forms, nor a file's and an
;; importer's, have one key, nor so their expansions' tags, which their
;; definition environments are kept by.
(define file-prefix (->* (string bool) string)
  (lambda (key imported)
    (let* ((path (if (and (> (string-length key) 6) (string=? (substring key 0 6) "input:"))
                     (substring key 6 (string-length key))
                     key))
           (f (mix 2 (remainder (string-hash path) hash-p))))
      (string-append "m" (int->string f) (if imported "mm" "m")))))
;; A module file's forms begun, their keys of `prefix`: their own; what is
;; given back puts the program's back (`fresh-scope-end!`).
(define-type fresh-saved (tupleof string int int seen-keys string int tags))
(define fresh-scope-begin! (->* (string) fresh-saved)
  (lambda (prefix)
    (let ((s (tuple (get form-key) (get fresh-count) (get captors-made) (get keys-seen)
                    (get module-prefix) (get expanded) (get form-tags))))
      (begin (set keys-seen nil) (set module-prefix prefix) s))))
(define fresh-scope-end! (->* (fresh-saved) unit)
  (lambda (s)
    (begin (set form-key (extract s 1)) (set fresh-count (extract s 2))
           (set captors-made (extract s 3)) (set keys-seen (extract s 4))
           (set module-prefix (extract s 5)) (set expanded (extract s 6))
           (set form-tags (extract s 7)))))
;; An importer's expansions of a file's uses begun (`macros-imports.fx`'s
;; `define-file`): their keys of `prefix`, counted apart; the importer's
;; count and prefix given back, for `file-keys-end!`.
(define file-keys-begin! (->* (string) (tupleof seen-keys string))
  (lambda (prefix)
    (let ((s (tuple (get keys-seen) (get module-prefix))))
      (begin (set keys-seen nil) (set module-prefix prefix) s))))
(define file-keys-end! (->* ((tupleof seen-keys string)) unit)
  (lambda (s) (begin (set keys-seen (extract s 1)) (set module-prefix (extract s 2)))))
;; One use of the file's expanded as a form of its own: the form's state
;; before, for `use-end!`, which puts it back but for the keys counted.
(define use-begin! (->* () fresh-saved)
  (lambda ()
    (tuple (get form-key) (get fresh-count) (get captors-made) (get keys-seen)
           (get module-prefix) (get expanded) (get form-tags))))
(define use-end! (->* (fresh-saved) unit)
  (lambda (s)
    (begin (set form-key (extract s 1)) (set fresh-count (extract s 2))
           (set captors-made (extract s 3)) (set expanded (extract s 6))
           (set form-tags (extract s 7)))))
;; The state a session keeps after a form, and puts back before the next.
(define seen-now (->* () seen-keys) (lambda () (get keys-seen)))
(define seen! (->* (seen-keys) unit) (lambda (ks) (set keys-seen ks)))
