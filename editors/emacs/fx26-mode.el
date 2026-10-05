;;; fx26-mode.el --- Editing FX-26, and a REPL for it  -*- lexical-binding: t; -*-

;; Part of fixpt (https://github.com/pnkfelix/fixpt).

;;; Commentary:

;; A major mode for FX-26 source (`.fx' files): font-lock for its forms,
;; kinds, effects and regions; indentation as the repository writes it;
;; a REPL (`run-fx26'), into which a definition, a region or the file can
;; be sent; `flymake' running both of fixpt's checkers as you type; and
;; `eldoc' showing the type and effect the last check found for the
;; global at point.
;;
;; The REPL runs `fixpt --dialect fx26 --emacs repl'.  `--emacs' turns off
;; the continuation prompt and accepts `,at FILE LINE COL' before a form,
;; so that its errors name where it was sent from; in the REPL buffer,
;; `compilation-shell-minor-mode' makes them links.
;;
;; To use it:
;;
;;   (add-to-list 'load-path "~/Dev/Rust/fixpt/editors/emacs")
;;   (require 'fx26-mode)

;;; Code:

(require 'comint)
(require 'compile)
(require 'flymake)
(require 'lisp-mode)
(require 'subr-x)

(defgroup fx26 nil
  "Editing FX-26, and running it."
  :group 'languages
  :prefix "fx26-")

(defconst fx26--this-directory
  (file-name-directory (or load-file-name buffer-file-name default-directory))
  "Where this file is: `editors/emacs/' in the fixpt repository.")

(defcustom fx26-program nil
  "The `fixpt' executable.
When nil, the one in `exec-path', or else the repository's release build
next to this file."
  :type '(choice (const :tag "Find it" nil) file))

(defcustom fx26-repl-arguments '("--dialect" "fx26" "--emacs" "repl")
  "Arguments for the REPL.
Add flags such as \"--fx26-run\" \"cellular\" before \"repl\"; keep
\"--emacs\"."
  :type '(repeat string))

(defcustom fx26-check-arguments '("check" "-")
  "Arguments for checking a buffer: its text is the standard input."
  :type '(repeat string))

(defun fx26--program ()
  "The `fixpt' executable to run."
  (or fx26-program
      (executable-find "fixpt")
      (let ((built (expand-file-name "../../target/release/fixpt" fx26--this-directory)))
        (and (file-executable-p built) built))
      (user-error "No `fixpt' found: set `fx26-program', or build it (cargo build --release)")))

;;;; Syntax

(defvar fx26-mode-syntax-table
  (let ((table (make-syntax-table lisp-data-mode-syntax-table)))
    ;; `#' begins `#t', `#u', `#\c' and `#|' comments, as in Scheme.
    (modify-syntax-entry ?# "' 14" table)
    (modify-syntax-entry ?| "\" 23bn" table)
    ;; `@' is part of a region's name, `@heap'.
    (modify-syntax-entry ?@ "_" table)
    (modify-syntax-entry ?\[ "(]" table)
    (modify-syntax-entry ?\] ")[" table)
    table)
  "Syntax table for `fx26-mode'.")

;;;; Font-lock

(defconst fx26--definers
  '("define" "define*" "define-rec" "define-type" "define-generative"
    "define-datatype" "define-effect")
  "Forms that define a name.")

(defconst fx26--special-forms
  '("lambda" "plambda" "vlambda" "rlambda" "dlambda" "proj" "if" "cond" "else"
    "and" "or" "let" "let*" "letrec" "begin" "the" "quote" "tagcase" "product"
    "extract" "sum" "prompt" "module" "with" "load-module" "private-regions"
    "letregion" "letfreeze" "letrena" "letreap" "convention")
  "Syntax that is not a definition.")

(defconst fx26--type-forms
  '("subr" "vsubr" "poly" "ref" "icell" "pairof" "listof" "arrayof" "mark-key"
    "prompt-tag" "composable" "bloblet" "fields" "frozen" "productof" "sumof"
    "dletrec" "mu" "nat" "nlist" "place" "moduleof" "abs" "desc" "val" "select"
    "proves" "conv" "flatarrayof" "eqtable" "=>")
  "Heads of types, and their parts.")

(defconst fx26--base-types
  '("int" "bool" "char" "string" "unit" "symbol" "datum" "void" "i32" "u32"
    "i64" "u64" "f64" "f32")
  "Types written by name.")

(defconst fx26--kinds
  '("region" "effect" "type" "data" "size" "conv")
  "Kinds, as binders say them.")

(defconst fx26--effects
  '("pure" "spin" "maxeff" "read" "write" "alloc" "goto" "comefrom" "await"
    "globals" "const" "acyclic" "finite" "heap")
  "Effects, their atoms, and the regions and sizes written by name.")

(defun fx26--words (words)
  "A regexp matching WORDS as whole symbols."
  (concat "\\_<" (regexp-opt words t) "\\_>"))

(defvar fx26-font-lock-keywords
  `((,(concat "(" (regexp-opt fx26--definers t) "\\_>[ \t]*(?\\(\\(?:\\sw\\|\\s_\\)+\\)")
     (1 font-lock-keyword-face)
     (2 (if (member (match-string 1) '("define-type" "define-generative" "define-datatype" "define-effect"))
            font-lock-type-face
          font-lock-function-name-face)))
    (,(concat "(" (fx26--words fx26--special-forms)) 1 font-lock-keyword-face)
    (,(concat "(" (fx26--words fx26--type-forms)) 1 font-lock-type-face)
    (,(fx26--words fx26--base-types) 1 font-lock-type-face)
    (,(fx26--words fx26--kinds) 1 font-lock-builtin-face)
    (,(fx26--words fx26--effects) 1 font-lock-builtin-face)
    ("\\_<@\\(?:\\sw\\|\\s_\\)+" 0 font-lock-constant-face)
    ("\\_<#[tfu]\\_>" 0 font-lock-constant-face)
    ("\\_<#\\\\\\(?:\\sw\\|\\s_\\|.\\)" 0 font-lock-string-face)
    ("^\\s-*\\(,[a-z-]+\\)" 1 font-lock-preprocessor-face))
  "Highlighting for `fx26-mode'.")

;;;; Indentation

(defvar fx26-indent-specs
  (let ((table (make-hash-table :test #'equal)))
    (dolist (spec '(;; Forms that bind or open something, then a body.
                    ("lambda" . 1) ("plambda" . 1) ("vlambda" . 1) ("rlambda" . 1)
                    ("dlambda" . 1) ("let" . 1) ("let*" . 1) ("letrec" . 1)
                    ("letregion" . 1) ("letfreeze" . 1) ("letrena" . 1) ("letreap" . 1)
                    ("tagcase" . 1) ("with" . 1) ("the" . 1) ("poly" . 1) ("prompt" . 1)
                    ("with-mark" . 2) ("convention" . 1)
                    ;; Bodies of items alone.
                    ("begin" . 0) ("cond" . 0) ("module" . 0) ("define-rec" . 0) ("private-regions" . 0)
                    ;; A name (and type), then a body.
                    ("define" . defun) ("define*" . defun) ("define-type" . 1)
                    ("define-generative" . 1) ("define-datatype" . 1) ("define-effect" . 1)))
      (puthash (car spec) (cdr spec) table))
    table)
  "How each form's arguments indent, as `lisp-indent-function' takes it:
a number of distinguished arguments before a body, or `defun'.")

(defun fx26--head-at (pos)
  "The name at the head of the list that opens at POS, or nil."
  (save-excursion
    (goto-char (1+ pos))
    (when (looking-at "\\(?:\\sw\\|\\s_\\)+")
      (match-string-no-properties 0))))

(defun fx26-indent-function (indent-point state)
  "Indent as the fixpt repository does: `lisp-indent-function', with
FX-26's forms from `fx26-indent-specs', and each member of a
`define-rec' group indented as a definition.
INDENT-POINT and STATE are as `lisp-indent-function' has them."
  (let* ((normal-indent (current-column))
         (open (elt state 1))
         (head (fx26--head-at open))
         (spec (and head (gethash head fx26-indent-specs)))
         (opens (elt state 9))
         (outer (car (last (butlast opens))))
         (as-definition
          (or
           ;; `(define-rec (name type lambda) …)': each member.
           (and outer (equal (fx26--head-at outer) "define-rec"))
           ;; `(tagcase e (tag (x …) body) …)': each arm, past the subject.
           (and outer (equal (fx26--head-at outer) "tagcase")
                (save-excursion
                  (goto-char (1+ outer)) (forward-sexp 2) (skip-chars-forward " \t\n")
                  (<= (point) open))))))
    (cond
     ((and as-definition (null spec))
      (lisp-indent-defform state indent-point))
     ((eq spec 'defun) (lisp-indent-defform state indent-point))
     ((integerp spec) (lisp-indent-specform spec state indent-point normal-indent))
     ;; No rule: `calculate-lisp-indent' lines the arguments up, as in
     ;; Scheme (not Emacs Lisp's rules for `if', `let' and the rest).
     (t nil))))

;;;; Comments

(defun fx26-comment-indent ()
  "Where a comment goes: alone on its line, as code there would be;
after code, at `comment-column'."
  (if (save-excursion (skip-chars-backward " \t") (bolp))
      (save-excursion
        (beginning-of-line)
        (let ((indent (calculate-lisp-indent)))
          (or (if (consp indent) (car indent) indent) 0)))
    comment-column))

;;;; The REPL

(defvar fx26-repl-buffer-name "*fx26*"
  "The REPL's buffer.")

(defconst fx26-prompt-regexp "^\\(?:fx26> \\)+"
  "The REPL's prompt; with `--emacs' there is no continuation prompt.")

(defvar fx26-repl-mode-map
  (let ((map (make-sparse-keymap)))
    (set-keymap-parent map comint-mode-map)
    map)
  "Keys in the REPL.")

(define-derived-mode fx26-repl-mode comint-mode "FX-26 REPL"
  "The FX-26 REPL, `fixpt --emacs repl'."
  :syntax-table fx26-mode-syntax-table
  (setq-local comint-prompt-regexp fx26-prompt-regexp)
  (setq-local comint-prompt-read-only t)
  (setq-local font-lock-defaults '(fx26-font-lock-keywords))
  ;; `file:line:col: message' becomes a link.
  (compilation-shell-minor-mode 1))

;;;###autoload
(defun run-fx26 ()
  "Start the FX-26 REPL, or switch to it."
  (interactive)
  (let ((buffer (get-buffer-create fx26-repl-buffer-name)))
    (unless (comint-check-proc buffer)
      (let ((default-directory (or (fx26--project-root) default-directory))
            ;; A pipe, not a terminal: at a terminal fixpt edits lines itself.
            (process-connection-type nil))
        (apply #'make-comint-in-buffer "fx26" buffer (fx26--program) nil fx26-repl-arguments))
      (with-current-buffer buffer (fx26-repl-mode)))
    (pop-to-buffer buffer)))

(defun fx26--project-root ()
  "The current project's root, if there is a project."
  (when-let ((p (project-current))) (project-root p)))

(defun fx26--process ()
  "The REPL's process, started if need be."
  (or (get-buffer-process fx26-repl-buffer-name)
      (save-window-excursion (run-fx26) (get-buffer-process fx26-repl-buffer-name))))

(defun fx26-send-region (start end)
  "Send the text from START to END to the REPL, said to be from this file."
  (interactive "r")
  (let* ((proc (fx26--process))
         (text (buffer-substring-no-properties start end))
         (file (or buffer-file-name (buffer-name))))
    (save-excursion
      (goto-char start)
      (skip-chars-forward " \t\n" end)
      (comint-send-string
       proc (format ",at %s %d %d\n" file (line-number-at-pos) (1+ (current-column)))))
    (comint-send-string proc (concat (string-trim-left text) "\n"))))

(defun fx26-send-definition ()
  "Send the top-level form at point to the REPL."
  (interactive)
  (save-excursion
    (end-of-defun)
    (let ((end (point)))
      (beginning-of-defun)
      (fx26-send-region (point) end))))

(defun fx26-load-file (file)
  "Load FILE into the REPL, as `,load' does; save it first."
  (interactive (list (or buffer-file-name (read-file-name "Load FX-26 file: "))))
  (when (and buffer-file-name (buffer-modified-p)) (save-buffer))
  (comint-send-string (fx26--process) (format ",load %s\n" (expand-file-name file))))

(defun fx26-switch-to-repl ()
  "Switch to the REPL, starting it if need be."
  (interactive)
  (run-fx26))

;;;; Checking as you type

(defvar-local fx26--flymake-process nil
  "The check running for this buffer, if any.")

(defvar-local fx26--globals nil
  "What the last check that passed said of each global: its name to its
type and effect.")

(defun fx26--parse-check (output buffer)
  "The diagnostics in OUTPUT, from `fixpt check -' run on BUFFER.
Also notes, in BUFFER, each definition's type and effect for `eldoc'."
  (let ((diags nil) (globals (make-hash-table :test #'equal)))
    (with-temp-buffer
      (insert output)
      (goto-char (point-min))
      (while (not (eobp))
        (cond
         ;; `! <stdin>:LINE:COL: message', the rest indented under it.
         ((looking-at "^! [^:\n]*:\\([0-9]+\\):\\([0-9]+\\): \\(.*\\)$")
          (let ((line (string-to-number (match-string 1)))
                (col (string-to-number (match-string 2)))
                (message (match-string 3)))
            (forward-line 1)
            (while (looking-at "^  \\(.*\\)$")
              (setq message (concat message "\n" (match-string 1)))
              (forward-line 1))
            (push (list line col message :error) diags)))
         ((looking-at "^; the checkers disagree")
          (push (list 1 1 "the checkers disagree: fixpt check shows how" :warning) diags)
          (forward-line 1))
         ;; `define NAME : TYPE ! EFFECT'.
         ((looking-at "^define \\([^ \n]+\\) : \\(.*\\)$")
          (puthash (match-string 1) (match-string 2) globals)
          (forward-line 1))
         (t (forward-line 1)))))
    ;; A program with an error says no definition's type: keep the last
    ;; check's, for `eldoc'.
    (when (or (null diags) (> (hash-table-count globals) 0))
      (with-current-buffer buffer (setq fx26--globals globals)))
    (mapcar (lambda (d)
              (pcase-let ((`(,line ,col ,message ,kind) d))
                (with-current-buffer buffer
                  (save-excursion
                    (goto-char (point-min))
                    (forward-line (1- line))
                    (move-to-column (1- col))
                    (let ((beg (point))
                          (end (condition-case nil
                                   (progn (forward-sexp 1) (point))
                                 (error (line-end-position)))))
                      (flymake-make-diagnostic buffer beg (max end (1+ beg)) kind message))))))
            (nreverse diags))))

(defun fx26-flymake (report-fn &rest _args)
  "A `flymake' backend: both of fixpt's checkers, on the buffer's text.
REPORT-FN is `flymake''s."
  (when (process-live-p fx26--flymake-process)
    (kill-process fx26--flymake-process))
  (let* ((source (current-buffer))
         (default-directory (if buffer-file-name (file-name-directory buffer-file-name) default-directory))
         (out (generate-new-buffer " *fx26-check*")))
    (setq fx26--flymake-process
          (make-process
           :name "fx26-check" :noquery t :connection-type 'pipe
           :buffer out
           :command (cons (fx26--program) fx26-check-arguments)
           :sentinel
           (lambda (proc _event)
             (when (memq (process-status proc) '(exit signal))
               (unwind-protect
                   (when (and (buffer-live-p source)
                              (eq proc (buffer-local-value 'fx26--flymake-process source)))
                     (funcall report-fn
                              (fx26--parse-check (with-current-buffer (process-buffer proc) (buffer-string))
                                                 source)))
                 (kill-buffer (process-buffer proc)))))))
    (process-send-region fx26--flymake-process (point-min) (point-max))
    (process-send-eof fx26--flymake-process)))

(defun fx26-eldoc (callback &rest _)
  "An `eldoc' function: the type and effect of the global at point, as
the last check found it.  CALLBACK is `eldoc''s."
  (when-let* ((name (thing-at-point 'symbol t))
              (globals fx26--globals)
              (type (gethash name globals)))
    (funcall callback (concat name " : " type) :thing name :face 'font-lock-function-name-face)))

;;;; The mode

(defvar fx26-mode-map
  (let ((map (make-sparse-keymap)))
    (define-key map (kbd "C-M-x") #'fx26-send-definition)
    (define-key map (kbd "C-c C-e") #'fx26-send-definition)
    (define-key map (kbd "C-c C-r") #'fx26-send-region)
    (define-key map (kbd "C-c C-l") #'fx26-load-file)
    (define-key map (kbd "C-c C-z") #'fx26-switch-to-repl)
    map)
  "Keys in `fx26-mode'.")

;;;###autoload
(define-derived-mode fx26-mode lisp-data-mode "FX-26"
  "Major mode for FX-26 source.

\\{fx26-mode-map}"
  :syntax-table fx26-mode-syntax-table
  (setq-local font-lock-defaults '(fx26-font-lock-keywords nil nil))
  (setq-local lisp-indent-function #'fx26-indent-function)
  (setq-local indent-tabs-mode nil)
  (setq-local comment-start ";; ")
  (setq-local comment-add 1)
  (setq-local comment-indent-function #'fx26-comment-indent)
  (add-hook 'flymake-diagnostic-functions #'fx26-flymake nil t)
  (add-hook 'eldoc-documentation-functions #'fx26-eldoc nil t)
  (flymake-mode 1))

;;;###autoload
(add-to-list 'auto-mode-alist '("\\.fx\\'" . fx26-mode))

(provide 'fx26-mode)
;;; fx26-mode.el ends here
