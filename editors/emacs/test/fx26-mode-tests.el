;;; fx26-mode-tests.el --- Tests for fx26-mode  -*- lexical-binding: t; -*-

;; Run with editors/emacs/run-tests.sh.  The tests that run fixpt are
;; skipped unless it is built (target/release/fixpt).

;;; Code:

(require 'ert)
(require 'fx26-mode)

(defun fx26-test--indented (text)
  "TEXT, every line's indentation removed, then indented by `fx26-mode'."
  (with-temp-buffer
    (insert (replace-regexp-in-string "^[ \t]+" "" text))
    (delay-mode-hooks (fx26-mode))
    (flymake-mode -1)
    (let ((inhibit-message t))
      (indent-region (point-min) (point-max)))
    (buffer-string)))

(defun fx26-test--same-indentation (text)
  "Whether `fx26-mode' indents TEXT as it is written."
  (should (equal (fx26-test--indented text) text)))

(ert-deftest fx26-indents-definitions-and-bodies ()
  (fx26-test--same-indentation "\
(define k-syn-symbols (subr checks (k-syns) k-names)
  (lambda (xs)
    (cond ((null? xs) nil)
          ((syn-symbol? (car xs)) (cons (syn-head (car xs)) (k-syn-symbols (cdr xs))))
          (else (k-syn-symbols (cdr xs))))))
"))

(ert-deftest fx26-indents-define-rec-members-as-definitions ()
  (fx26-test--same-indentation "\
(define-rec
  (even? (subr spin (int) bool)
    (lambda (n) (if (= n 0) #t (odd? (- n 1)))))
  (odd? (subr spin (int) bool)
    (lambda (n) (if (= n 0) #f (even? (- n 1))))))
"))

(ert-deftest fx26-indents-tagcase-arms-and-let ()
  (fx26-test--same-indentation "\
(define size (subr pure (k-desc) int)
  (lambda (d)
    (tagcase d
      (dz (z)
        (let* ((a 1)
               (b 2))
          (+ a b)))
      (else y 0))))
"))

(ert-deftest fx26-indents-modules-and-cond-alone ()
  (fx26-test--same-indentation "\
(define m sig
  (module
    (define-type t int)
    (define x t
      (cond
        ((= 1 2) 3)
        (else 4)))))
"))

(ert-deftest fx26-indents-whole-line-comments-as-code ()
  (fx26-test--same-indentation "\
; a comment at the top
(define f (subr pure () int)
  ; a comment in a body
  (lambda () 1))
"))

(ert-deftest fx26-indents-with-spaces ()
  (should-not (string-match-p "\t" (fx26-test--indented "\
(define f (subr pure () int)
(lambda ()
(cond ((= 1 2) 3)
(else 4))))
"))))

(defun fx26-test--face-at (text needle)
  "The face `fx26-mode' gives NEEDLE's first character in TEXT."
  (with-temp-buffer
    (insert text)
    (delay-mode-hooks (fx26-mode))
    (flymake-mode -1)
    (font-lock-ensure)
    (goto-char (point-min))
    (search-forward needle)
    (get-text-property (match-beginning 0) 'face)))

(ert-deftest fx26-highlights-forms-kinds-effects-and-regions ()
  (let ((text "(define-rec (go (subr (maxeff (read @heap) spin) ((x region)) int) (lambda (x) 1)))"))
    (should (eq (fx26-test--face-at text "define-rec") 'font-lock-keyword-face))
    (should (eq (fx26-test--face-at text "subr") 'font-lock-type-face))
    (should (eq (fx26-test--face-at text "maxeff") 'font-lock-builtin-face))
    (should (eq (fx26-test--face-at text "@heap") 'font-lock-constant-face))
    (should (eq (fx26-test--face-at text "region") 'font-lock-builtin-face))
    (should (eq (fx26-test--face-at text "lambda") 'font-lock-keyword-face))
    (should (eq (fx26-test--face-at "(define-type sig int)" "sig") 'font-lock-type-face))
    (should (eq (fx26-test--face-at "(define f 1)" "f 1") 'font-lock-function-name-face))))

(ert-deftest fx26-reads-what-fixpt-check-says ()
  (with-temp-buffer
    (insert "(define x 1)\n(define y\n  (car 5))\n")
    (delay-mode-hooks (fx26-mode))
    (flymake-mode -1)
    (let* ((out (concat "define x : int ! pure\n"
                        "! <stdin>:3:8: argument 1 is a int, where a (pairof ? ? r) is expected\n"
                        "  and a second line\n"
                        "; both checkers agree\n"))
           (diags (fx26--parse-check out (current-buffer)))
           (d (car diags)))
      (should (= (length diags) 1))
      (should (eq (flymake-diagnostic-type d) :error))
      (should (equal (buffer-substring (flymake-diagnostic-beg d) (flymake-diagnostic-end d)) "5"))
      (should (string-match-p "and a second line" (flymake-diagnostic-text d)))
      (should (equal (gethash "x" fx26--globals) "int ! pure")))))

(ert-deftest fx26-says-when-the-checkers-disagree ()
  (with-temp-buffer
    (insert "(define x 1)\n")
    (delay-mode-hooks (fx26-mode))
    (flymake-mode -1)
    (let ((diags (fx26--parse-check "; the checkers disagree\n" (current-buffer))))
      (should (eq (flymake-diagnostic-type (car diags)) :warning)))))

;;;; With fixpt itself

(defun fx26-test--built ()
  "Whether fixpt is built, for the tests that run it."
  (ignore-errors (fx26--program)))

(defun fx26-test--check (text)
  "The diagnostics `fx26-flymake' reports for TEXT, in the current buffer."
  (erase-buffer)
  (insert text)
  (let ((got 'none))
    (fx26-flymake (lambda (diags &rest _) (setq got diags)))
    (with-timeout (60 (error "fixpt check did not answer"))
      (while (eq got 'none) (accept-process-output nil 0.1)))
    got))

(ert-deftest fx26-flymake-runs-both-checkers ()
  (skip-unless (fx26-test--built))
  (with-temp-buffer
    (delay-mode-hooks (fx26-mode))
    (flymake-mode -1)
    ;; A program that checks: no diagnostics, and each global's type.
    (should (null (fx26-test--check "(define x 1)\n(define y (+ x 1))\n")))
    (should (equal (gethash "x" fx26--globals) "int ! pure"))
    ;; One that does not: the error, at the subform; the types kept.
    (let ((got (fx26-test--check "(define x 1)\n(define y\n  (car 5))\n")))
      (should (= (length got) 1))
      (should (equal (buffer-substring (flymake-diagnostic-beg (car got))
                                       (flymake-diagnostic-end (car got)))
                     "5"))
      (should (equal (gethash "x" fx26--globals) "int ! pure")))))

(defun fx26-test--repl-output-until (regexp)
  "Wait for REGEXP in the REPL's buffer; its text."
  (with-current-buffer fx26-repl-buffer-name
    (with-timeout (120 (error "The REPL did not say %s: %s" regexp (buffer-string)))
      (while (not (save-excursion (goto-char (point-min)) (re-search-forward regexp nil t)))
        (accept-process-output (get-buffer-process (current-buffer)) 0.1)))
    (buffer-string)))

(ert-deftest fx26-repl-runs-what-is-sent-and-places-its-errors ()
  (skip-unless (fx26-test--built))
  (let ((file (make-temp-file "fx26-test" nil ".fx" "(define x 41)\n\n(define y\n  (car x))\n")))
    (unwind-protect
        (progn
          (save-window-excursion (run-fx26))
          (fx26-test--repl-output-until "^fx26> ")
          (with-current-buffer (find-file-noselect file)
            (goto-char (point-min))
            (fx26-send-definition)
            (fx26-test--repl-output-until "x : int ! pure")
            (goto-char (point-min))
            (forward-line 2)
            (fx26-send-definition)
            ;; The error, said where `x' is in the file: line 4, column 8.
            (fx26-test--repl-output-until
             (concat (regexp-quote (file-name-nondirectory file)) ":4:8: "))))
      (let ((proc (get-buffer-process fx26-repl-buffer-name)))
        (when proc (delete-process proc)))
      (kill-buffer fx26-repl-buffer-name)
      (when-let ((b (get-file-buffer file))) (kill-buffer b))
      (delete-file file))))

(provide 'fx26-mode-tests)
;;; fx26-mode-tests.el ends here
