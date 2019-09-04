;;; ergo-mode.el --- Major mode for the Ergo legal contracts language

;;; Commentary:

;; Author: Jerome Simeon <jerome@clause.io>
;; Version: 0.0.40
;; Keywords: languages ergo
;; URL: https://ergo.accordproject.org
;;
;; This file is not part of GNU Emacs.

;;; Code:

(require 'cl-lib)
(require 'compile)
(require 'etags)
(require 'ffap)
(require 'find-file)
(require 'ring)
(require 'url)
(require 'xref nil :noerror)  ; xref is new in Emacs 25.1


(eval-when-compile
  (defmacro ergo--forward-word (&optional arg)
   (if (fboundp 'forward-word-strictly)
       `(forward-word-strictly ,arg)
     `(forward-word ,arg))))

(defun ergo--delete-whole-line (&optional arg)
  "Delete the current line without putting it in the `kill-ring'.
Derived from function `kill-whole-line'.  ARG is defined as for that
function."
  (setq arg (or arg 1))
  (if (and (> arg 0)
           (eobp)
           (save-excursion (forward-visible-line 0) (eobp)))
      (signal 'end-of-buffer nil))
  (if (and (< arg 0)
           (bobp)
           (save-excursion (end-of-visible-line) (bobp)))
      (signal 'beginning-of-buffer nil))
  (cond ((zerop arg)
         (delete-region (progn (forward-visible-line 0) (point))
                        (progn (end-of-visible-line) (point))))
        ((< arg 0)
         (delete-region (progn (end-of-visible-line) (point))
                        (progn (forward-visible-line (1+ arg))
                               (unless (bobp)
                                 (backward-char))
                               (point))))
        (t
         (delete-region (progn (forward-visible-line 0) (point))
                        (progn (forward-visible-line arg) (point))))))

(defun ergo-goto-opening-parenthesis (&optional _legacy-unused)
  "Move up one level of parentheses."
  ;; The old implementation of ergo-goto-opening-parenthesis had an
  ;; optional argument to speed up the function.  It didn't change the
  ;; function's outcome.

  ;; Silently fail if there's no matching opening parenthesis.
  (condition-case nil
      (backward-up-list)
    (scan-error nil)))


(defconst ergo-dangling-operators-regexp "[^-]-\\|[^+]\\+\\|[/*&><.=|^]")
(defconst ergo--max-dangling-operator-length 2
  "The maximum length of dangling operators.
This must be at least the length of the longest string matched by
‘ergo-dangling-operators-regexp.’, and must be updated whenever
that constant is changed.")

(defconst ergo-identifier-regexp "[[:word:][:multibyte:]]+")
(defconst ergo-type-name-no-prefix-regexp "\\(?:[[:word:][:multibyte:]]+\\.\\)?[[:word:][:multibyte:]]+")
(defconst ergo-qualified-identifier-regexp (concat ergo-identifier-regexp "\\." ergo-identifier-regexp))
(defconst ergo-label-regexp ergo-identifier-regexp)
(defconst ergo-type-regexp "[[:word:][:multibyte:]*]+")
(defconst ergo-func-regexp (concat "\\_<\\(function\\|clause\\)\\_>\\s *\\(" ergo-identifier-regexp "\\)"))
(defconst ergo-func-meth-regexp (concat
                               "\\_<\\(function\\|clause\\)\\_>\\s *\\(?:(\\s *"
                               "\\(" ergo-identifier-regexp "\\s +\\)?" ergo-type-regexp
                               "\\s *)\\s *\\)?\\("
                               ergo-identifier-regexp
                               "\\)("))

(defconst ergo-builtins
  '("now" "min"   "max"   "some")
  "All built-in functions in the Ergo language.  Used for font locking.")

(defconst ergo-mode-keywords
  '("function"    "with"        "match"     "none"
    "namespace"   "enforce"     "if"        "then"      "else"      "let"
    "foreach"     "import"      "where"     "return"    "constant"
    "upon"        "request"     "contract"  "clause"    "over"      "define"
    "set"         "state"       "emit"      "emits"     "throw"
    "extends"     "event"       "asset"     "enum"      "concept"
    "participant" "transaction" "abstract")
  "All keywords in the Ergo language.  Used for font locking.")

(defconst ergo-constants '("nil" "true" "false"))
(defconst ergo-type-name-regexp (concat "\\(?:[*(]\\)*\\(\\(?:" ergo-identifier-regexp "\\.\\)?" ergo-identifier-regexp "\\)"))

;; Maximum number of identifiers that can be highlighted as type names
;; in one function type/declaration.
(defconst ergo--font-lock-func-param-num-groups 16)

(defvar ergo-dangling-cache)

(defgroup ergo nil
  "Major mode for editing Ergo code."
  :link '(url-link "https://github.com/accordproject/ergo-mode")
  :group 'languages)

(defgroup ergo-cover nil
  "Options specific to `cover`."
  :group 'ergo)

(defcustom ergo-fontify-function-calls t
  "Fontify function and method calls if this is non-nil."
  :type 'boolean
  :group 'ergo)

(defcustom ergo-mode-hook nil
  "Hook called by `ergo-mode'."
  :type 'hook
  :group 'ergo)

(defcustom ergo-command "ergo"
  "The 'ergo' command.
Some users have multiple Ergo development trees and invoke the 'ergo'
tool via a wrapper that sets ERGOROOT and ERGOPATH based on the
current directory.  Such users should customize this variable to
point to the wrapper script."
  :type 'string
  :group 'ergo)

(defcustom ergo-other-file-alist
  '(("_test\\.ergo\\'" (".ergo"))
    ("\\.ergo\\'" ("_test.ergo")))
  "See the documentation of `ff-other-file-alist' for details."
  :type '(repeat (list regexp (choice (repeat string) function)))
  :group 'ergo)

(defcustom ergo-packages-function 'ergo-packages-native
  "Function called by `ergo-packages' to determine the list of available packages.
This is used in e.g. tab completion in `ergo-import-add'.

This package provides two functions: `ergo-packages-native' uses
elisp to find all .a files in all /pkg/ directories.
`ergo-packages-ergo-list' uses 'ergo list all' to determine all Ergo
packages.  `ergo-packages-ergo-list' generally produces more accurate
results, but can be slower than `ergo-packages-native'."
  :type 'function
  :package-version '(ergo-mode . 1.4.0)
  :group 'ergo)

(defcustom ergo-guess-ergopath-functions (list #'ergo-ergodep-ergopath
                                           #'ergo-wergo-ergopath
                                           #'ergo-gb-ergopath
                                           #'ergo-plain-ergopath)
  "Functions to call in sequence to detect a project's ERGOPATH.

The functions in this list will be called one after another,
until a function returns non-nil.  The order of the functions in
this list is important, as some project layouts may superficially
look like others.  For example, a subset of wergo projects look like
gb projects.  That's why we need to detect wergo first, to avoid
mis-identifying them as gb projects."
  :type '(repeat function)
  :group 'ergo)

(defun ergo--kill-new-message (url)
  "Make URL the latest kill and print a message."
  (kill-new url)
  (message "%s" url))

(defvar ergo-mode-syntax-table
  (let ((st (make-syntax-table)))
    (modify-syntax-entry ?+  "." st)
    (modify-syntax-entry ?-  "." st)
    (modify-syntax-entry ?%  "." st)
    (modify-syntax-entry ?&  "." st)
    (modify-syntax-entry ?|  "." st)
    (modify-syntax-entry ?^  "." st)
    (modify-syntax-entry ?!  "." st)
    (modify-syntax-entry ?=  "." st)
    (modify-syntax-entry ?<  "." st)
    (modify-syntax-entry ?>  "." st)
    (modify-syntax-entry ?/  ". 124b" st)
    (modify-syntax-entry ?*  ". 23" st)
    (modify-syntax-entry ?\n "> b" st)
    (modify-syntax-entry ?\" "\"" st)
    (modify-syntax-entry ?\' "\"" st)
    (modify-syntax-entry ?`  "\"" st)
    (modify-syntax-entry ?\\ "\\" st)
    ;; TODO make _ a symbol constituent now that xemacs is gone
    (modify-syntax-entry ?_  "w" st)

    st)
  "Syntax table for Ergo mode.")

(defun ergo--build-font-lock-keywords ()
  ;; we cannot use 'symbols in regexp-opt because GNU Emacs <24
  ;; doesn't understand that
  (append
   `((ergo--match-func
      ,@(mapcar (lambda (x) `(,x font-lock-type-face))
                (number-sequence 1 ergo--font-lock-func-param-num-groups)))
     (,(concat "\\_<" (regexp-opt ergo-mode-keywords t) "\\_>") . font-lock-keyword-face)
     (,(concat "\\(\\_<" (regexp-opt ergo-builtins t) "\\_>\\)[[:space:]]*(") 1 font-lock-builtin-face)
     (,(concat "\\_<" (regexp-opt ergo-constants t) "\\_>") . font-lock-constant-face)
     (,ergo-func-regexp 1 font-lock-function-name-face)) ;; function (not method) name

   (if ergo-fontify-function-calls
       `((,(concat "\\(" ergo-identifier-regexp "\\)[[:space:]]*(") 1 font-lock-function-name-face) ;; function call/method name
         (,(concat "[^[:word:][:multibyte:]](\\(" ergo-identifier-regexp "\\))[[:space:]]*(") 1 font-lock-function-name-face)) ;; bracketed function call
     `((,ergo-func-meth-regexp 2 font-lock-function-name-face))) ;; method name

   `(
     ("\\(`[^`]*`\\)" 1 font-lock-multiline) ;; raw string literal, needed for font-lock-syntactic-keywords
     (,(concat "\\_<type\\_>[[:space:]]+\\([^[:space:](]+\\)") 1 font-lock-type-face) ;; types
     (,(concat "\\_<type\\_>[[:space:]]+" ergo-identifier-regexp "[[:space:]]*" ergo-type-name-regexp) 1 font-lock-type-face) ;; types
     (,(concat "[^[:word:][:multibyte:]]\\[\\([[:digit:]]+\\|\\.\\.\\.\\)?\\]" ergo-type-name-regexp) 2 font-lock-type-face) ;; Arrays/slices
     (,(concat "\\(" ergo-identifier-regexp "\\)" "{") 1 font-lock-type-face)
     (,(concat "\\_<map\\_>\\[[^]]+\\]" ergo-type-name-regexp) 1 font-lock-type-face) ;; map value type
     (,(concat "\\_<map\\_>\\[" ergo-type-name-regexp) 1 font-lock-type-face) ;; map key type
     (,(concat "\\_<chan\\_>[[:space:]]*\\(?:<-[[:space:]]*\\)?" ergo-type-name-regexp) 1 font-lock-type-face) ;; channel type
     (,(concat "\\_<\\(?:new\\|make\\)\\_>\\(?:[[:space:]]\\|)\\)*(" ergo-type-name-regexp) 1 font-lock-type-face) ;; new/make type
     ;; TODO do we actually need this one or isn't it just a function call?
     (,(concat "\\.\\s *(" ergo-type-name-regexp) 1 font-lock-type-face) ;; Type conversion
     ;; Like the original ergo-mode this also marks compound literal
     ;; fields. There, it was marked as to fix, but I grew quite
     ;; accustomed to it, so it'll stay for now.
     (,(concat "^[[:space:]]*\\(" ergo-label-regexp "\\)[[:space:]]*:\\(\\S.\\|$\\)") 1 font-lock-constant-face) ;; Labels and compound literal fields
     (,(concat "\\_<\\(goto\\|break\\|continue\\)\\_>[[:space:]]*\\(" ergo-label-regexp "\\)") 2 font-lock-constant-face)))) ;; labels in goto/break/continue

(let ((m (define-prefix-command 'ergo-goto-map)))
  (define-key m "a" #'ergo-goto-arguments)
  (define-key m "f" #'ergo-goto-function)
  (define-key m "i" #'ergo-goto-imports)
  (define-key m "m" #'ergo-goto-method-receiver)
  (define-key m "n" #'ergo-goto-function-name)
  (define-key m "r" #'ergo-goto-return-values))

(defvar ergo-mode-map
  (let ((m (make-sparse-keymap)))
    (unless (boundp 'electric-indent-chars)
        (define-key m "}" #'ergo-mode-insert-and-indent)
        (define-key m ")" #'ergo-mode-insert-and-indent))
    (define-key m (kbd "C-c C-a") #'ergo-import-add)
    (define-key m (kbd "C-c C-f") 'ergo-goto-map)
    m)
  "Keymap used by ‘ergo-mode’.")

(easy-menu-define ergo-mode-menu ergo-mode-map
  "Menu for Ergo mode."
  '("Ergo"
    ["Add Import"            ergo-import-add t]
    ["Remove Unused Imports" ergo-remove-unused-imports t]
    ["Go to Imports"         ergo-goto-imports t]
    "---"
    ["Customize Mode"        (customize-group 'ergo) t]))

(defun ergo-mode-insert-and-indent (key)
  "Invoke the global binding of KEY, then reindent the line."

  (interactive (list (this-command-keys)))
  (call-interactively (lookup-key (current-global-map) key))
  (indent-according-to-mode))

(defmacro ergo-paren-level ()
  `(car (syntax-ppss)))

(defmacro ergo-in-string-or-comment-p ()
  `(nth 8 (syntax-ppss)))

(defmacro ergo-in-string-p ()
  `(nth 3 (syntax-ppss)))

(defmacro ergo-in-comment-p ()
  `(nth 4 (syntax-ppss)))

(defmacro ergo-goto-beginning-of-string-or-comment ()
  `(goto-char (nth 8 (syntax-ppss))))

(defun ergo--backward-irrelevant (&optional stop-at-string)
  "Skip backwards over any characters that are irrelevant for
indentation and related tasks.

It skips over whitespace, comments, cases and labels and, if
STOP-AT-STRING is not true, over strings."

  (let (pos (start-pos (point)))
    (skip-chars-backward "\n\s\t")
    (if (and (save-excursion (beginning-of-line) (ergo-in-string-p))
             (= (char-before) ?`)
             (not stop-at-string))
        (backward-char))
    (if (and (ergo-in-string-p)
             (not stop-at-string))
        (ergo-goto-beginning-of-string-or-comment))
    (if (looking-back "\\*/" (line-beginning-position))
        (backward-char))
    (if (ergo-in-comment-p)
        (ergo-goto-beginning-of-string-or-comment))
    (setq pos (point))
    (beginning-of-line)
    (if (or (looking-at (concat "^" ergo-label-regexp ":"))
            (looking-at "^[[:space:]]*\\(case .+\\|default\\):"))
        (end-of-line 0)
      (goto-char pos))
    (if (/= start-pos (point))
        (ergo--backward-irrelevant stop-at-string))
    (/= start-pos (point))))

(defun ergo--buffer-narrowed-p ()
  "Return non-nil if the current buffer is narrowed."
  (/= (buffer-size)
      (- (point-max)
         (point-min))))

(defun ergo-previous-line-has-dangling-op-p ()
  "Return non-nil if the current line is a continuation line."
  (let* ((cur-line (line-number-at-pos))
         (val (gethash cur-line ergo-dangling-cache 'nope)))
    (if (or (ergo--buffer-narrowed-p) (equal val 'nope))
        (save-excursion
          (beginning-of-line)
          (ergo--backward-irrelevant t)
          (setq val (looking-back ergo-dangling-operators-regexp
                                  (- (point) ergo--max-dangling-operator-length)))
          (if (not (ergo--buffer-narrowed-p))
              (puthash cur-line val ergo-dangling-cache))))
    val))

(defun ergo--at-function-definition ()
  "Return non-nil if point is on the opening curly brace of a
function definition.

We do this by first calling (beginning-of-defun), which will take
us to the start of *some* function.  We then look for the opening
curly brace of that function and compare its position against the
curly brace we are checking.  If they match, we return non-nil."
  (if (= (char-after) ?\{)
      (save-excursion
        (let ((old-point (point))
              start-nesting)
          (beginning-of-defun)
          (when (looking-at "func ")
            (setq start-nesting (ergo-paren-level))
            (skip-chars-forward "^{")
            (while (> (ergo-paren-level) start-nesting)
              (forward-char)
              (skip-chars-forward "^{") 0)
            (if (and (= (ergo-paren-level) start-nesting) (= old-point (point)))
                t))))))

(defun ergo--indentation-for-opening-parenthesis ()
  "Return the semantic indentation for the current opening parenthesis.

If point is on an opening curly brace and said curly brace
belongs to a function declaration, the indentation of the func
keyword will be returned.  Otherwise the indentation of the
current line will be returned."
  (save-excursion
    (if (ergo--at-function-definition)
        (progn
          (beginning-of-defun)
          (current-indentation))
      (current-indentation))))

(defun ergo-indentation-at-point ()
  (save-excursion
    (let (start-nesting)
      (back-to-indentation)
      (setq start-nesting (ergo-paren-level))

      (cond
       ((ergo-in-string-p)
        (current-indentation))
       ((looking-at "[])}]")
        (ergo-goto-opening-parenthesis)
        (if (ergo-previous-line-has-dangling-op-p)
            (- (current-indentation) tab-width)
          (ergo--indentation-for-opening-parenthesis)))
       ((progn (ergo--backward-irrelevant t)
               (looking-back ergo-dangling-operators-regexp
                             (- (point) ergo--max-dangling-operator-length)))
        ;; only one nesting for all dangling operators in one operation
        (if (ergo-previous-line-has-dangling-op-p)
            (current-indentation)
          (+ (current-indentation) tab-width)))
       ((zerop (ergo-paren-level))
        0)
       ((progn (ergo-goto-opening-parenthesis) (< (ergo-paren-level) start-nesting))
        (if (ergo-previous-line-has-dangling-op-p)
            (current-indentation)
          (+ (ergo--indentation-for-opening-parenthesis) tab-width)))
       (t
        (current-indentation))))))

(defun ergo-mode-indent-line ()
  (interactive)
  (let (indent
        shift-amt
        (pos (- (point-max) (point)))
        (point (point))
        (beg (line-beginning-position)))
    (back-to-indentation)
    (if (ergo-in-string-or-comment-p)
        (goto-char point)
      (setq indent (ergo-indentation-at-point))
      (if (looking-at (concat ergo-label-regexp ":\\([[:space:]]*/.+\\)?$\\|case .+:\\|default:"))
          (cl-decf indent tab-width))
      (setq shift-amt (- indent (current-column)))
      (if (zerop shift-amt)
          nil
        (delete-region beg (point))
        (indent-to indent))
      ;; If initial point was within line's indentation,
      ;; position after the indentation.  Else stay at same point in text.
      (if (> (- (point-max) pos) (point))
          (goto-char (- (point-max) pos))))))

(defun ergo-beginning-of-defun (&optional count)
  (unless (bolp)
    (end-of-line))
  (setq count (or count 1))
  (let (first failure)
    (dotimes (i (abs count))
      (setq first t)
      (while (and (not failure)
                  (or first (ergo-in-string-or-comment-p)))
        (if (>= count 0)
            (progn
              (ergo--backward-irrelevant)
              (if (not (re-search-backward ergo-func-meth-regexp nil t))
                  (setq failure t)))
          (if (looking-at ergo-func-meth-regexp)
              (forward-char))
          (if (not (re-search-forward ergo-func-meth-regexp nil t))
              (setq failure t)))
        (setq first nil)))
    (if (< count 0)
        (beginning-of-line))
    (not failure)))

(defun ergo-end-of-defun ()
  (let (orig-level)
    ;; It can happen that we're not placed before a function by emacs
    (if (not (looking-at "function"))
        (ergo-beginning-of-defun -1))
    ;; Find the { that starts the function, i.e., the next { that isn't
    ;; preceded by struct or interface, or a comment or struct tag.  BUG:
    ;; breaks if there's a comment between the struct/interface keyword and
    ;; bracket, like this:
    ;;
    ;;     struct /* why? */ {
    (while (progn
      (skip-chars-forward "^{")
      (forward-char)
      (or (ergo-in-string-or-comment-p)
          (looking-back "\\(struct\\|interface\\)\\s-*{"
                        (line-beginning-position)))))
    (setq orig-level (ergo-paren-level))
    (while (>= (ergo-paren-level) orig-level)
      (skip-chars-forward "^}")
      (forward-char))))

(defun ergo--find-enclosing-parentheses (position)
  "Return points of outermost '(' and ')' surrounding POSITION if
such parentheses exist.

If outermost '(' exists but ')' does not, it returns the next blank
line or end-of-buffer position instead of the position of the closing
parenthesis.

If the starting parenthesis is not found, it returns (POSITION
POSITION)."
  (save-excursion
    (let (beg end)
      (goto-char position)
      (while (> (ergo-paren-level) 0)
        (re-search-backward "[(\\[{]" nil t)
        (when (looking-at "(")
          (setq beg (point))))
      (if (null beg)
          (list position position)
        (goto-char position)
        (while (and (> (ergo-paren-level) 0)
                    (search-forward ")" nil t)))
        (when (> (ergo-paren-level) 0)
          (unless (re-search-forward "^[[:space:]]*$" nil t)
            (goto-char (point-max))))
        (list beg (point))))))

(defun ergo--search-next-comma (end)
  "Search forward from point for a comma whose nesting level is
the same as point.  If it reaches the end of line or a closing
parenthesis before a comma, it stops at it."
  (let ((orig-level (ergo-paren-level)))
    (while (and (< (point) end)
                (or (looking-at "[^,)\n]")
                    (> (ergo-paren-level) orig-level)))
      (forward-char))
    (when (and (looking-at ",")
               (< (point) (1- end)))
      (forward-char))))

(defun ergo--looking-at-keyword ()
  (and (looking-at (concat "\\(" ergo-identifier-regexp "\\)"))
       (member (match-string 1) ergo-mode-keywords)))

(defun ergo--match-func (end)
  "Search for identifiers used as type names from a function
parameter list, and set the identifier positions as the results
of last search.  Return t if search succeeded."
  (when (re-search-forward "\\_<\\(function\\|clause\\)\\_>" end t)
    (let ((regions (ergo--match-func-type-names end)))
      (if (null regions)
          ;; Nothing to highlight. This can happen if the current func
          ;; is "func()". Try next one.
          (ergo--match-func end)
        ;; There are something to highlight. Set those positions as
        ;; last search results.
        (setq regions (ergo--filter-match-data regions end))
        (when regions
          (set-match-data (ergo--make-match-data regions))
          t)))))

(defun ergo--match-func-type-names (end)
  (cond
   ;; Function declaration (e.g. "func foo(")
   ((looking-at (concat "[[:space:]\n]*" ergo-identifier-regexp "[[:space:]\n]*("))
    (goto-char (match-end 0))
    (nconc (ergo--match-parameter-list end)
           (ergo--match-function-result end)))
   ;; Method declaration, function literal, or function type
   ((looking-at "[[:space:]]*(")
    (goto-char (match-end 0))
    (let ((regions (ergo--match-parameter-list end)))
      ;; Method declaration (e.g. "func (x y) foo(")
      (when (looking-at (concat "[[:space:]]*" ergo-identifier-regexp "[[:space:]\n]*("))
        (goto-char (match-end 0))
        (setq regions (nconc regions (ergo--match-parameter-list end))))
      (nconc regions (ergo--match-function-result end))))))

(defun ergo--parameter-list-type (end)
  "Return `present' if the parameter list has names, or `absent' if not.
Assumes point is at the beginning of a parameter list, just
after '('."
  (save-excursion
    (skip-chars-forward "[:space:]\n" end)
    (cond ((> (point) end)
           nil)
          ((looking-at (concat ergo-identifier-regexp "[[:space:]\n]*,"))
           (goto-char (match-end 0))
           (ergo--parameter-list-type end))
          ((or (looking-at ergo-qualified-identifier-regexp)
               (looking-at (concat ergo-type-name-no-prefix-regexp "[[:space:]\n]*\\(?:)\\|\\'\\)"))
               (ergo--looking-at-keyword)
               (looking-at "[*\\[]\\|\\.\\.\\.\\|\\'"))
           'absent)
          (t 'present))))

(defconst ergo--opt-dotdotdot-regexp "\\(?:\\.\\.\\.\\)?")
(defconst ergo--parameter-type-regexp
  (concat ergo--opt-dotdotdot-regexp "[[:space:]*\n]*\\(" ergo-type-name-no-prefix-regexp "\\)[[:space:]\n]*\\([,)]\\|\\'\\)"))
(defconst ergo--func-type-in-parameter-list-regexp
  (concat ergo--opt-dotdotdot-regexp "[[:space:]*\n]*\\(\\_<\\(function\\|clause\\)\\_>" "\\)"))

(defun ergo--match-parameters-common (identifier-regexp end)
  (let ((acc ())
        (start -1))
    (while (progn (skip-chars-forward "[:space:]\n" end)
                  (and (not (looking-at "\\(?:)\\|\\'\\)"))
                       (< start (point))
                       (<= (point) end)))
      (setq start (point))
      (cond
       ((looking-at (concat identifier-regexp ergo--parameter-type-regexp))
        (setq acc (nconc acc (list (match-beginning 1) (match-end 1))))
        (goto-char (match-beginning 2)))
       ((looking-at (concat identifier-regexp ergo--func-type-in-parameter-list-regexp))
        (goto-char (match-beginning 1))
        (setq acc (nconc acc (ergo--match-func-type-names end)))
        (ergo--search-next-comma end))
       (t
        (ergo--search-next-comma end))))
    (when (and (looking-at ")")
               (< (point) end))
      (forward-char))
    acc))

(defun ergo--match-parameters-with-identifier-list (end)
  (ergo--match-parameters-common
   (concat ergo-identifier-regexp "[[:space:]\n]+")
   end))

(defun ergo--match-parameters-without-identifier-list (end)
  (ergo--match-parameters-common "" end))

(defun ergo--filter-match-data (regions end)
  "Remove points from REGIONS if they are beyond END.
REGIONS are a list whose size is multiple of 2.  Element 2n is beginning of a
region and 2n+1 is end of it.

This function is used to make sure we don't override end point
that `font-lock-mode' gave to us."
  (when regions
    (let* ((vec (vconcat regions))
           (i 0)
           (len (length vec)))
      (while (and (< i len)
                  (<= (nth i regions) end)
                  (<= (nth (1+ i) regions) end))
        (setq i (+ i 2)))
      (cond ((= i len)
             regions)
            ((zerop i)
             nil)
            (t
             (butlast regions (- (length regions) i)))))))

(defun ergo--make-match-data (regions)
  (let ((deficit (- (* 2 ergo--font-lock-func-param-num-groups)
                    (length regions))))
    (when (> deficit 0)
      (let ((last (car (last regions))))
        (setq regions (nconc regions (make-list deficit last))))))
  `(,(car regions) ,@(last regions) ,@regions))

(defun ergo--match-parameter-list (end)
  "Return a list of identifier positions that are used as type
names in a function parameter list, assuming point is at the
beginning of a parameter list.  Return nil if the text after
point does not look like a parameter list.

Set point to end of closing parenthesis on success.

In Ergo, the names must either all be present or all be absent
within a list of parameters.

Parsing a parameter list is a little bit complicated because we
have to scan through the parameter list to determine whether or
not the list has names. Until a type name is found or reaching
end of a parameter list, we are not sure which form the parameter
list is.

For example, X and Y are type names in a parameter list \"(X,
Y)\" but are parameter names in \"(X, Y int)\". We cannot say if
X is a type name until we see int after Y.

Note that even \"(int, float T)\" is a valid parameter
list. Builtin type names are not reserved words. In this example,
int and float are parameter names and only T is a type name.

In this function, we first scan the parameter list to see if the
list has names, and then handle it accordingly."
  (let ((name (ergo--parameter-list-type end)))
    (cond ((eq name 'present)
           (ergo--match-parameters-with-identifier-list end))
          ((eq name 'absent)
           (ergo--match-parameters-without-identifier-list end))
          (t nil))))

(defun ergo--match-function-result (end)
  "Return a list of identifier positions that are used as type
names in a function result, assuming point is at the beginning of
a result.

Function result is a unparenthesized type or a parameter list."
  (cond ((and (looking-at (concat "[[:space:]*]*:[[:space:]*]*\\(" ergo-type-name-no-prefix-regexp "\\)"))
              (not (member (match-string 1) ergo-mode-keywords)))
         (list (match-beginning 1) (match-end 1)))
        ((looking-at "[[:space:]]*(")
         (goto-char (match-end 0))
         (ergo--match-parameter-list end))
        (t nil)))

(defun ergo--reset-dangling-cache-before-change (&optional _beg _end)
  "Reset `ergo-dangling-cache'.

This is intended to be called from `before-change-functions'."
  (setq ergo-dangling-cache (make-hash-table :test 'eql)))

;;;###autoload
(define-derived-mode ergo-mode prog-mode "Ergo"
  "Major mode for editing Ergo source text.

This mode provides (not just) basic editing capabilities for
working with Ergo code. It offers almost complete syntax
highlighting, proper parsing of the buffer content to allow
features such as navigation by function, manipulation of comments
or detection of strings.

The following extra functions are defined:

- `ergo-import-add'
- `ergo-remove-unused-imports'
- `ergo-goto-arguments'
- `ergo-goto-function'
- `ergo-goto-function-name'
- `ergo-goto-imports'
- `ergo-goto-return-values'
- `ergo-goto-method-receiver'
- `ergo-set-project'
- `ergo-reset-ergopath'

"

  ;; Font lock
  (set (make-local-variable 'font-lock-defaults)
       '(ergo--build-font-lock-keywords))

  ;; Indentation
  (set (make-local-variable 'indent-line-function) #'ergo-mode-indent-line)

  ;; Comments
  (set (make-local-variable 'comment-start) "// ")
  (set (make-local-variable 'comment-end)   "")
  (set (make-local-variable 'comment-use-syntax) t)
  (set (make-local-variable 'comment-start-skip) "\\(//+\\|/\\*+\\)\\s *")

  (set (make-local-variable 'beginning-of-defun-function) #'ergo-beginning-of-defun)
  (set (make-local-variable 'end-of-defun-function) #'ergo-end-of-defun)

  (set (make-local-variable 'parse-sexp-lookup-properties) t)
  (set (make-local-variable 'syntax-propertize-function) #'ergo-propertize-syntax)

  (if (boundp 'electric-indent-chars)
      (set (make-local-variable 'electric-indent-chars) '(?\n ?} ?\))))

  (set (make-local-variable 'compilation-error-screen-columns) nil)

  (set (make-local-variable 'ergo-dangling-cache) (make-hash-table :test 'eql))
  (add-hook 'before-change-functions #'ergo--reset-dangling-cache-before-change t t)

  ;; ff-find-other-file
  (setq ff-other-file-alist 'ergo-other-file-alist)

  (setq imenu-generic-expression
        '(("type" "^type *\\([^ \t\n\r\f]*\\)" 1)
          ("function" "^\\(function\\|clause\\) *\\(.*\\) {" 1)))
  (imenu-add-to-menubar "Index")

  ;; Ergo style
  (setq indent-tabs-mode t)

  ;; Handle unit test failure output in compilation-mode
  ;;
  ;; Note that we add our entry to the beginning of
  ;; compilation-error-regexp-alist. In older versions of Emacs, the
  ;; list was processed from the end, and we would've wanted to add
  ;; ours last. But at some point this changed, and now the list is
  ;; processed from the beginning. It's important that our entry comes
  ;; before gnu, because gnu matches ergo test output, but includes the
  ;; leading whitespace in the file name.
  ;;
  ;; http://lists.gnu.org/archive/html/bug-gnu-emacs/2001-12/msg00674.html
  ;; documents the old, reverseed order.
  (when (and (boundp 'compilation-error-regexp-alist)
             (boundp 'compilation-error-regexp-alist-alist))
    (add-to-list 'compilation-error-regexp-alist 'ergo-test)
    (add-to-list 'compilation-error-regexp-alist-alist
                 '(ergo-test . ("^\t+\\([^()\t\n]+\\):\\([0-9]+\\):? .*$" 1 2)) t)))

;;;###autoload
(add-to-list 'auto-mode-alist (cons "\\.ergo\\'" 'ergo-mode))
(add-to-list 'auto-mode-alist (cons "\\.cto\\'" 'ergo-mode))

(defun ergo--apply-rcs-patch (patch-buffer)
  "Apply an RCS-formatted diff from PATCH-BUFFER to the current buffer."
  (let ((target-buffer (current-buffer))
        ;; Relative offset between buffer line numbers and line numbers
        ;; in patch.
        ;;
        ;; Line numbers in the patch are based on the source file, so
        ;; we have to keep an offset when making changes to the
        ;; buffer.
        ;;
        ;; Appending lines decrements the offset (possibly making it
        ;; negative), deleting lines increments it. This order
        ;; simplifies the forward-line invocations.
        (line-offset 0)
        (column (current-column)))
    (save-excursion
      (with-current-buffer patch-buffer
        (goto-char (point-min))
        (while (not (eobp))
          (unless (looking-at "^\\([ad]\\)\\([0-9]+\\) \\([0-9]+\\)")
            (error "Invalid rcs patch or internal error in ergo--apply-rcs-patch"))
          (forward-line)
          (let ((action (match-string 1))
                (from (string-to-number (match-string 2)))
                (len  (string-to-number (match-string 3))))
            (cond
             ((equal action "a")
              (let ((start (point)))
                (forward-line len)
                (let ((text (buffer-substring start (point))))
                  (with-current-buffer target-buffer
                    (cl-decf line-offset len)
                    (goto-char (point-min))
                    (forward-line (- from len line-offset))
                    (insert text)))))
             ((equal action "d")
              (with-current-buffer target-buffer
                (ergo--goto-line (- from line-offset))
                (cl-incf line-offset len)
                (ergo--delete-whole-line len)))
             (t
              (error "Invalid rcs patch or internal error in ergo--apply-rcs-patch")))))))
    (move-to-column column)))

;;;###autoload
(defun ergo-goto-imports ()
  "Move point to the block of imports.

If using

  import (
    \"foo\"
    \"bar\"
  )

it will move point directly behind the last import.

If using

  import \"foo\"
  import \"bar\"

it will move point to the next line after the last import.

If no imports can be found, point will be moved after the package
declaration."
  (interactive)
  ;; FIXME if there's a block-commented import before the real
  ;; imports, we'll jump to that one.

  ;; Generally, this function isn't very forgiving. it'll bark on
  ;; extra whitespace. It works well for clean code.
  (let ((old-point (point)))
    (goto-char (point-min))
    (cond
     ((re-search-forward "^import ([^)]+)" nil t)
      (backward-char 2)
      'block)
     ((re-search-forward "\\(^import \\([^\"]+ \\)?\"[^\"]+\"\n?\\)+" nil t)
      'single)
     ((re-search-forward "^[[:spaoce:]\n]*namespace .+?\n" nil t)
      (message "No imports found, moving point after namespace declaration")
      'none)
     (t
      (goto-char old-point)
      (message "No imports or package declaration found. Is this really a Ergo file?")
      'fail))))

(defun ergo-propertize-syntax (start end)
  (save-excursion
    (goto-char start)
    (while (search-forward "\\" end t)
      (put-text-property (1- (point)) (point) 'syntax-table (if (= (char-after) ?`) '(1) '(9))))))

(defun ergo-import-add (arg import)
  "Add a new IMPORT to the list of imports.

When called with a prefix ARG asks for an alternative name to
import the package as.

If no list exists yet, one will be created if possible.

If an identical import has been commented, it will be
uncommented, otherwise a new import will be added."

  ;; - If there's a matching `// import "foo"`, uncomment it
  ;; - If we're in an import() block and there's a matching `"foo"`, uncomment it
  ;; - Otherwise add a new import, with the appropriate syntax
  (interactive
   (list
    current-prefix-arg
    (replace-regexp-in-string "^[\"']\\|[\"']$" "" (completing-read "Package: " (ergo-packages)))))
  (save-excursion
    (let (as line import-start)
      (if arg
          (setq as (read-from-minibuffer "Import as: ")))
      (if as
          (setq line (format "%s \"%s\"" as import))
        (setq line (format "\"%s\"" import)))

      (goto-char (point-min))
      (if (re-search-forward (concat "^[[:space:]]*//[[:space:]]*import " line "$") nil t)
          (uncomment-region (line-beginning-position) (line-end-position))
        (cl-case (ergo-goto-imports)
          ('fail (message "Could not find a place to add import."))
          ('block-empty
           (insert "\n\t" line "\n"))
          ('block
              (save-excursion
                (re-search-backward "^import (")
                (setq import-start (point)))
            (if (re-search-backward (concat "^[[:space:]]*//[[:space:]]*" line "$")  import-start t)
                (uncomment-region (line-beginning-position) (line-end-position))
              (insert "\n\t" line)))
          ('single (insert "import " line "\n"))
          ('none (insert "\nimport (\n\t" line "\n)\n")))))))

(defun ergo-root-and-paths ()
  (let* ((output (process-lines ergo-command "env" "ERGOROOT" "ERGOPATH"))
         (root (car output))
         (paths (split-string (cadr output) path-separator)))
    (cons root paths)))

(defun ergo--string-prefix-p (s1 s2 &optional ignore-case)
  "Return non-nil if S1 is a prefix of S2.
If IGNORE-CASE is non-nil, the comparison is case-insensitive."
  (eq t (compare-strings s1 nil nil
                         s2 0 (length s1) ignore-case)))

(defun ergo--directory-dirs (dir)
  "Recursively return all subdirectories in DIR."
  (if (file-directory-p dir)
      (let ((dir (directory-file-name dir))
            (dirs '())
            (files (directory-files dir nil nil t)))
        (dolist (file files)
          (unless (member file '("." ".."))
            (let ((file (concat dir "/" file)))
              (if (file-directory-p file)
                  (setq dirs (append (cons file
                                           (ergo--directory-dirs file))
                                     dirs))))))
        dirs)
    '()))


(defun ergo-packages ()
  (funcall ergo-packages-function))

(defun ergo-packages-native ()
  "Return a list of all installed Ergo packages.
It looks for archive files in /pkg/."
  (sort
   (delete-dups
    (cl-mapcan
     (lambda (topdir)
       (let ((pkgdir (concat topdir "/pkg/")))
         (cl-mapcan (lambda (dir)
                   (mapcar (lambda (file)
                             (let ((sub (substring file (length pkgdir) -2)))
                               (unless (or (ergo--string-prefix-p "obj/" sub) (ergo--string-prefix-p "tool/" sub))
                                 (mapconcat #'identity (cdr (split-string sub "/")) "/"))))
                           (if (file-directory-p dir)
                               (directory-files dir t "\\.a$"))))
                 (if (file-directory-p pkgdir)
                     (ergo--directory-dirs pkgdir)))))
     (ergo-root-and-paths)))
   #'string<))

(defun ergo-packages-ergo-list ()
  "Return a list of all Ergo packages, using `ergo list'."
  (process-lines ergo-command "list" "-e" "all"))

(defun ergo-unused-imports-lines ()
  (reverse (remove nil
                   (mapcar
                    (lambda (line)
                      (when (string-match "^\\(.+\\):\\([[:digit:]]+\\): imported and not used: \".+\".*$" line)
                        (let ((error-file-name (match-string 1 line))
                              (error-line-num (match-string 2 line)))
                          (if (string= (file-truename error-file-name) (file-truename buffer-file-name))
                              (string-to-number error-line-num)))))
                    (split-string (shell-command-to-string
                                   (concat ergo-command
                                           (if (string-match "_test\\.ergo$" buffer-file-truename)
                                               " test -c"
                                             (concat " build -o " null-device))
                                           " -gcflags=-e"
                                           " "
                                           (shell-quote-argument (file-truename buffer-file-name)))) "\n")))))

(defun ergo-remove-unused-imports (arg)
  "Remove all unused imports.
If ARG is non-nil, unused imports will be commented, otherwise
they will be removed completely."
  (interactive "P")
  (save-excursion
    (let ((cur-buffer (current-buffer)) flymake-state lines)
      (when (boundp 'flymake-mode)
        (setq flymake-state flymake-mode)
        (flymake-mode-off))
      (save-some-buffers nil (lambda () (equal cur-buffer (current-buffer))))
      (if (buffer-modified-p)
          (message "Cannot operate on unsaved buffer")
        (setq lines (ergo-unused-imports-lines))
        (dolist (import lines)
          (ergo--goto-line import)
          (beginning-of-line)
          (if arg
              (comment-region (line-beginning-position) (line-end-position))
            (ergo--delete-whole-line)))
        (message "Removed %d imports" (length lines)))
      (if flymake-state (flymake-mode-on)))))

(defun ergo--goto-line (line)
  (goto-char (point-min))
  (forward-line (1- line)))

(defun ergo--line-column-to-point (line column)
  (save-excursion
    (ergo--goto-line line)
    (forward-char (1- column))
    (point)))

(cl-defstruct ergo--covered
  start-line start-column end-line end-column covered count)

(defun ergo-goto-function (&optional arg)
  "Go to the function defintion (named or anonymous) surrounding point.

If we are on a docstring, follow the docstring down.
If no function is found, assume that we are at the top of a file
and search forward instead.

If point is looking at the func keyword of an anonymous function,
go to the surrounding function.

If ARG is non-nil, anonymous functions are ignored."
  (interactive "P")
  (let ((p (point)))
    (cond
     ((save-excursion
        (beginning-of-line)
        (looking-at "^//"))
      ;; In case we are looking at the docstring, move on forward until we are
      ;; not anymore
      (beginning-of-line)
      (while (looking-at "^//")
        (forward-line 1))
      ;; If we are still not looking at a function, retry by calling self again.
      (when (not (looking-at "\\<\\(function\\|clause\\)\\>"))
        (ergo-goto-function arg)))

     ;; If we're already looking at an anonymous func, look for the
     ;; surrounding function.
     ((and (looking-at "\\<\\(function\\|clause\\)\\>")
           (not (looking-at "^\\(function\\|clause\\)\\>")))
      (re-search-backward "\\<\\(function\\|clause\\)\\>" nil t))

     ((not (looking-at "\\<\\(function\\|clause\\)\\>"))
      ;; If point is on the "function" keyword, step back a word and retry
      (if (string= (symbol-name (symbol-at-point)) "function")
          (backward-word)
        ;; If we are not looking at the beginning of a function line, do a regexp
        ;; search backwards
        (re-search-backward "\\<\\(function\\|clause\\)\\>" nil t))

      ;; If nothing is found, assume that we are at the top of the file and
      ;; should search forward instead.
      (when (not (looking-at "\\<\\(function\\|clause\\)\\>"))
        (re-search-forward "\\<\\(function\\|clause\\)\\>" nil t)
        (ergo--forward-word -1))

      ;; If we have landed at an anonymous function, it is possible that we
      ;; were not inside it but below it. If we were not inside it, we should
      ;; go to the containing function.
      (while (and (not (ergo--in-function-p p))
                  (not (looking-at "^func\\>")))
        (ergo-goto-function arg)))))

  (cond
   ((ergo-in-comment-p)
    ;; If we are still in a comment, redo the call so that we get out of it.
    (ergo-goto-function arg))

   ((and (looking-at "\\<\\(function\\|clause\\)(") arg)
    ;; If we are looking at an anonymous function and a prefix argument has
    ;; been supplied, redo the call so that we skip the anonymous function.
    (ergo-goto-function arg))))

(defun ergo--goto-opening-curly-brace ()
  ;; Find the { that starts the function, i.e., the next { that isn't
  ;; preceded by struct or interface, or a comment or struct tag.  BUG:
  ;; breaks if there's a comment between the struct/interface keyword and
  ;; bracket, like this:
  ;;
  ;;     struct /* why? */ {
  (ergo--goto-return-values)
  (while (progn
           (skip-chars-forward "^{")
           (forward-char)
           (or (ergo-in-string-or-comment-p)
               (looking-back "\\(struct\\|interface\\)\\s-*{"
                             (line-beginning-position)))))
  (backward-char))

(defun ergo--in-function-p (compare-point)
  "Return t if COMPARE-POINT lies inside the function immediately surrounding point."
  (save-excursion
    (when (not (looking-at "\\<\\(function\\|clause\\)\\>"))
      (ergo-goto-function))
    (let ((start (point)))
      (ergo--goto-opening-curly-brace)

      (unless (looking-at "{")
        (error "Expected to be looking at opening curly brace"))
      (forward-list 1)
      (and (>= compare-point start)
           (<= compare-point (point))))))

(defun ergo-goto-function-name (&optional arg)
  "Go to the name of the current function.

If the function is a test, place point after 'Test'.
If the function is anonymous, place point on the 'func' keyword.

If ARG is non-nil, anonymous functions are skipped."
  (interactive "P")
  (when (not (looking-at "\\<\\(function\\|clause\\)\\>"))
    (ergo-goto-function arg))
  ;; If we are looking at func( we are on an anonymous function and
  ;; nothing else should be done.
  (when (not (looking-at "\\<\\(function\\|clause\\)("))
    (let ((words 1)
          (chars 1))
      (when (looking-at "\\<\\(function\\|clause\\) (")
        (setq words 3
              chars 2))
      (ergo--forward-word words)
      (forward-char chars)
      (when (looking-at "Test")
        (forward-char 4)))))

(defun ergo-goto-arguments (&optional arg)
  "Go to the arguments of the current function.

If ARG is non-nil, anonymous functions are skipped."
  (interactive "P")
  (ergo-goto-function-name arg)
  (ergo--forward-word 1)
  (forward-char 1))

(defun ergo--goto-return-values (&optional arg)
  "Go to the declaration of return values for the current function."
  (ergo-goto-arguments arg)
  (backward-char)
  (forward-list)
  (forward-char))

(defun ergo-goto-return-values (&optional arg)
  "Go to the return value declaration of the current function.

If there are multiple ones contained in a parenthesis, enter the parenthesis.
If there is none, make space for one to be added.

If ARG is non-nil, anonymous functions are skipped."
  (interactive "P")
  (ergo--goto-return-values arg)

  ;; Opening parenthesis, enter it
  (when (looking-at "(")
    (forward-char 1))

  ;; No return arguments, add space for adding
  (when (looking-at "{")
    (insert " ")
    (backward-char 1)))

(defun ergo-goto-method-receiver (&optional arg)
  "Go to the receiver of the current method.

If there is none, add parenthesis to add one.

Anonymous functions cannot have method receivers, so when this is called
interactively anonymous functions will be skipped.  If called programmatically,
an error is raised unless ARG is non-nil."
  (interactive "P")

  (when (and (not (called-interactively-p 'interactive))
             (not arg)
             (ergo--in-anonymous-funcion-p))
    (error "Anonymous functions cannot have method receivers"))

  (ergo-goto-function t)  ; Always skip anonymous functions
  (forward-char 5)
  (when (not (looking-at "("))
    (save-excursion
      (insert "() ")))
  (forward-char 1))

(defun ergo--function-name (&optional arg)
  "Return the name of the surrounding function.

If ARG is non-nil, anonymous functions will be ignored and the
name returned will be that of the top-level function.  If ARG is
nil and the surrounding function is anonymous, nil will be
returned."
  (when (or (not (ergo--in-anonymous-funcion-p))
            arg)
    (save-excursion
      (ergo-goto-function-name t)
      (symbol-name (symbol-at-point)))))

(defun ergo--in-anonymous-funcion-p ()
  "Return t if point is inside an anonymous function, nil otherwise."
  (save-excursion
    (ergo-goto-function)
    (looking-at "\\<\\(function\\|clause\\)(")))

(defun ergo-guess-ergopath (&optional buffer)
  "Determine a suitable ERGOPATH for BUFFER, or the current buffer if BUFFER is nil.

This function supports gb-based projects as well as Ergodep, in
addition to ordinary uses of ERGOPATH."
  (with-current-buffer (or buffer (current-buffer))
    (let ((ergopath (cl-some (lambda (el) (funcall el))
                           ergo-guess-ergopath-functions)))
      (if ergopath
          (mapconcat
           (lambda (el) (file-truename el))
           ergopath
           path-separator)))))

(defun ergo-plain-ergopath ()
  "Detect a normal ERGOPATH, by looking for the first `src'
directory up the directory tree."
  (let ((d (locate-dominating-file buffer-file-name "src")))
    (if d
        (list d))))

(defun ergo-ergodep-ergopath ()
  "Detect a Ergodeps workspace by looking for Ergodeps/_workspace up
the directory tree. The result is combined with that of
`ergo-plain-ergopath'."
  (let* ((d (locate-dominating-file buffer-file-name "Ergodeps"))
         (workspace (concat d
                            (file-name-as-directory "Ergodeps")
                            (file-name-as-directory "_workspace"))))
    (if (and d
             (file-exists-p workspace))
        (list workspace
              (locate-dominating-file buffer-file-name "src")))))

(defun ergo-gb-ergopath ()
  "Detect a gb project."
  (or (ergo--gb-vendor-ergopath)
      (ergo--gb-vendor-ergopath-reverse)))

(defun ergo--gb-vendor-ergopath ()
  (let* ((d (locate-dominating-file buffer-file-name "src"))
         (vendor (concat d (file-name-as-directory "vendor"))))
    (if (and d
             (file-exists-p vendor))
        (list d vendor))))

(defun ergo--gb-vendor-ergopath-reverse ()
  (let* ((d (locate-dominating-file buffer-file-name "vendor"))
         (src (concat d (file-name-as-directory "src"))))
    (if (and d
             (file-exists-p src))
        (list d (concat d
                        (file-name-as-directory "vendor"))))))

(defun ergo-wergo-ergopath ()
  "Detect a wergo project."
  (or (ergo--wergo-ergocfg "src")
      (ergo--wergo-ergocfg "vendor")))

(defun ergo--wergo-ergocfg (needle)
  (let* ((d (locate-dominating-file buffer-file-name needle))
         (ergocfg (concat d (file-name-as-directory ".ergocfg"))))
    (if (and d
             (file-exists-p ergocfg))
        (with-temp-buffer
          (insert-file-contents (concat ergocfg "ergopaths"))
          (append
           (mapcar (lambda (el) (concat d (file-name-as-directory el))) (split-string (buffer-string) "\n" t))
           (list (ergo-original-ergopath)))))))

(defun ergo-set-project (&optional buffer)
  "Set ERGOPATH based on `ergo-guess-ergopath' for BUFFER, or the current buffer if BUFFER is nil.

If ergo-guess-ergopath returns nil, that is if it couldn't determine
a valid value for ERGOPATH, ERGOPATH will be set to the initial value
of when Emacs was started.

This function can for example be used as a
projectile-switch-project-hook, or simply be called manually when
switching projects."
  (interactive)
  (let ((ergopath (or (ergo-guess-ergopath buffer)
                    (ergo-original-ergopath))))
    (setenv "ERGOPATH" ergopath)
    (message "Set ERGOPATH to %s" ergopath)))

(defun ergo-reset-ergopath ()
  "Reset ERGOPATH to the value it had when Emacs started."
  (interactive)
  (let ((ergopath (ergo-original-ergopath)))
    (setenv "ERGOPATH" ergopath)
    (message "Set ERGOPATH to %s" ergopath)))

(defun ergo-original-ergopath ()
  "Return the original value of ERGOPATH from when Emacs was started."
  (let ((process-environment initial-environment)) (getenv "ERGOPATH")))

(defun ergo--insert-modified-files ()
  "Insert the contents of each modified Ergo buffer into the
current buffer in the format specified by guru's -modified flag."
  (mapc #'(lambda (b)
            (and (buffer-modified-p b)
                 (buffer-file-name b)
                 (string= (file-name-extension (buffer-file-name b)) "ergo")
                 (ergo--insert-modified-file (buffer-file-name b) b)))
        (buffer-list)))

(defun ergo--insert-modified-file (name buffer)
  (insert (format "%s\n%d\n" name (ergo--buffer-size-bytes buffer)))
  (insert-buffer-substring buffer))

(defun ergo--buffer-size-bytes (&optional buffer)
  (message "buffer; %s" buffer)
  "Return the number of bytes in the current buffer.
If BUFFER, return the number of characters in that buffer instead."
  (with-current-buffer (or buffer (current-buffer))
    (1- (position-bytes (point-max)))))


(provide 'ergo-mode)

;;; ergo-mode.el ends here
