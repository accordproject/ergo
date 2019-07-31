;;; cicero-mode.el --- A major mode for editing Accord Project Cicero templates.

;; Author: Jerome Simeon
;;       Tony Gentilcore
;;       Chris Wanstrath
;;       Daniel Hackney
;;       Daniel Evans
;;
;; Version: 1.4

;; This file is not part of Emacs

;; This file is free software; you can redistribute it and/or modify
;; it under the terms of the GNU General Public License as published by
;; the Free Software Foundation; either version 2, or (at your option)
;; any later version.

;; This file is distributed in the hope that it will be useful,
;; but WITHOUT ANY WARRANTY; without even the implied warranty of
;; MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
;; GNU General Public License for more details.

;; You should have received a copy of the GNU General Public License
;; along with GNU Emacs; see the file COPYING.  If not, write to
;; the Free Software Foundation, Inc., 59 Temple Place - Suite 330,
;; Boston, MA 02111-1307, USA.

;;; Commentary:

;; 1) Copy this file somewhere in your Emacs `load-path'.  To see what
;;    your `load-path' is, run inside emacs: C-h v load-path<RET>
;;
;; 2) Add the following to your .emacs file:
;;
;;    (require 'template-mode)

;; The indentation still has minor bugs due to the fact that
;; templates do not require valid HTML.

;; It would be nice to be able to highlight attributes of HTML tags,
;; however this is difficult due to the presence of CTemplate symbols
;; embedded within attributes.

(eval-when-compile
  (require 'font-lock))


(defgroup cicero nil
  ""
  :group 'languages)

(defface cicero-mode-section-face
  '((t (:inherit font-lock-keyword-face)))
  ""
  :group 'cicero)

(defface cicero-mode-comment-face
  '((t (:inherit font-lock-comment-face)))
  ""
  :group 'cicero)

(defface cicero-mode-include-face
  '((t (:inherit font-lock-function-name-face)))
  ""
  :group 'cicero)

(defface cicero-mode-builtins-face
  '((t (:inherit font-lock-variable-name-face)))
  ""
  :group 'cicero)

(defface cicero-mode-variable-face
  '((t (:inherit font-lock-constant-face)))
  ""
  :group 'cicero)



(defvar cicero-mode-version "1.3"
  "Version of `cicero-mode.el'.")

;; TODO: this keystrokes should be altered to avoid conflict with mustache-mode
(defvar cicero-mode-map
  (let ((map (make-sparse-keymap)))
    (define-key map "\C-m" 'reindent-then-newline-and-indent)
    (define-key map "\C-ct" 'cicero-insert-tag)
    (define-key map "\C-cv" 'cicero-insert-variable)
    (define-key map "\C-cs" 'cicero-insert-section)
    map)
  "Keymap for cicero-mode major mode")

(defvar cicero-mode-syntax-table
  (let ((st (make-syntax-table)))
    (modify-syntax-entry ?<  "(>  " st)
    (modify-syntax-entry ?>  ")<  " st)
    (modify-syntax-entry ?\" ".   " st)
    (modify-syntax-entry ?\\ ".   " st)
    (modify-syntax-entry ?'  "w   " st)
    st)
  "Syntax table in use in cicero-mode buffers.")

(defcustom cicero-basic-offset 2
  "The basic indentation offset for cicero."
  :group 'cicero
  :type 'integer)

;; Constant regular expressions to identify template elements.
(defconst cicero-mode-cicero-token "\\([a-zA-Z_.][a-zA-Z0-9_:=\?!.-]*\s+\\)*[a-zA-Z_.][a-zA-Z0-9_:=\?!.-]*")
(defconst cicero-mode-section (concat "\\({{[#^/]\s*"
                                   cicero-mode-cicero-token
                                   "\s*}}\\)"))
(defconst cicero-mode-open-section (concat "\\({{#\s*"
                                        cicero-mode-cicero-token
                                        "\s*}}\\)"))
(defconst cicero-mode-close-section (concat "{{/\\(\s*"
                                         cicero-mode-cicero-token
                                         "\s*\\)}}"))
;; TODO(tonyg) Figure out a way to support multiline comments.
(defconst cicero-mode-comment "\\({{!.*?}}\\)")
(defconst cicero-mode-include (concat "\\({{[><]\s*"
                                   cicero-mode-cicero-token
                                   "\s*}}\\)"))
(defconst cicero-mode-variable (concat "\\({{\s*"
                                    cicero-mode-cicero-token
                                    "\s*}}\\)"))
(defconst cicero-mode-variable (concat "\\({{{?\s*"
                                    cicero-mode-cicero-token
                                    "\s*}}}?\\)"))
(defconst cicero-mode-else (concat "\\({{\s*else\s*}}\\)"))
(defconst cicero-mode-variable-path (concat "\\({{\s*./\s*"
                                    cicero-mode-cicero-token
                                    "\s*}}\\)"))
(defconst cicero-mode-variable-path-parent (concat "\\({{\s*../\s*"
                                    cicero-mode-cicero-token
                                    "\s*}}\\)"))
(defconst cicero-mode-builtins
  (concat
   "\\({{\\<\s*"
   (regexp-opt
    '("BI_NEWLINE" "BI_SPACE")
    t)
   "\s*\\>}}\\)"))
(defconst cicero-mode-close-section-at-start (concat "^[ \t]*?"
                                                  cicero-mode-close-section))

;; Constant regular expressions to identify html tags.
;; Taken from HTML 4.01 / XHTML 1.0 Reference found at:
;; http://www.w3schools.com/tags/default.asp.
(defconst cicero-mode-html-constant "\\(&#?[a-z0-9]\\{2,5\\};\\)")
(defconst cicero-mode-pair-tag
  (concat
   "\\<"
   (regexp-opt
    '("a" "abbr" "acronym" "address" "applet" "area" "b" "bdo"
      "big" "blockquote" "body" "button" "caption" "center" "cite"
      "code" "col" "colgroup" "dd" "del" "dfn" "dif" "div" "dl"
      "dt" "em" "fieldset" "font" "form" "frame" "frameset" "h1"
      "header" "nav" "footer" "section"
      "h2" "h3" "h4" "h5" "h6" "head" "html" "i" "iframe" "ins"
      "kbd" "label" "legend" "li" "link" "map" "menu" "noframes"
      "noscript" "object" "ol" "optgroup" "option" "p" "pre" "q"
      "s" "samp" "script" "select" "small" "span" "strike"
      "strong" "style" "sub" "sup" "table" "tbody" "td" "textarea"
      "tfoot" "th" "thead" "title" "tr" "tt" "u" "ul" "var" "aside")
    t)
   "\\>"))
(defconst cicero-mode-standalone-tag
  (concat
   "\\<"
   (regexp-opt
    '("base" "br" "hr" "img" "input" "meta" "param")
    t)
   "\\>"))
(defconst cicero-mode-open-tag (concat "<\\("
                                    cicero-mode-pair-tag
                                    "\\)"))
(defconst cicero-mode-close-tag (concat "</\\("
                                     cicero-mode-pair-tag
                                     "\\)>"))
(defconst cicero-mode-close-tag-at-start (concat "^[ \t]*?"
                                              cicero-mode-close-tag))

(defconst cicero-mode-blank-line "^[ \t]*?$")
(defconst cicero-mode-else-line "^[ \t]*?{{[ \t]*?else[ \t]*?}}")
(defconst cicero-mode-dangling-open (concat "\\("
                                         cicero-mode-open-section
                                         "\\)\\|\\("
                                         cicero-mode-open-tag
                                         "\\)[^/]*$"))

(defun cicero-insert-tag (tag)
  "Inserts an HTML tag."
  (interactive "sTag: ")
  (cicero-indent)
  (insert (concat "<" tag ">"))
  (insert "\n\n")
  (insert (concat "</" tag ">"))
  (cicero-indent)
  (forward-line -1)
  (cicero-indent))

(defun cicero-insert-variable (variable)
  "Inserts a tpl variable."
  (interactive "sVariable: ")
  (insert (concat "{{" variable "}}")))

(defun cicero-insert-section (section)
  "Inserts a tpl section."
  (interactive "sSection: ")
  (cicero-indent)
  (insert (concat "{{#" section "}}\n"))
  (insert "\n")
  (insert (concat "{{/" section "}}"))
  (cicero-indent)
  (forward-line -1)
  (cicero-indent))

(defun cicero-indent ()
  "Indent current line"
  ;; Set the point to beginning of line.
  (beginning-of-line)
  ;; If we are at the beginning of the file, indent to 0.
  (if (bobp)
      (indent-line-to 0)
    (let ((tag-stack 1) (close-tag "") (cur-indent 0) (old-pnt (point-marker))
          (close-at-start) (open-token) (dangling-open))
      (progn
        ;; Determine if this is a template line or an html line.
        (if (looking-at "^[ \t]*?{{")
            (setq close-at-start cicero-mode-close-section-at-start
                  open-token "{{#")
          (setq close-at-start cicero-mode-close-tag-at-start
                open-token "<"))

        ;; If there is a closing tag at the start of the line, search back
        ;; for its opener and indent to that level.
        (if (looking-at close-at-start)
            (progn
              (save-excursion
                (setq close-tag (match-string 1))
                ;; Keep searching for a match for the close tag until
                ;; the tag-stack is 0.
                (while (and (not (bobp))
                            (> tag-stack 0)
                            (re-search-backward (concat (replace-regexp-in-string "{{#" "{{#?" open-token)
                                                        "\\(/?\\)"
                                                        close-tag) nil t))
                  (if (string-equal (match-string 1) "/")
                      ;; We found another close tag, so increment tag-stack.
                      (setq tag-stack (+ tag-stack 1))
                    ;; We found an open tag, so decrement tag-stack.
                    (setq tag-stack (- tag-stack 1)))
                  (setq cur-indent (current-indentation))))
              (if (> tag-stack 0)
                  (save-excursion
                    (forward-line -1)
                    (setq cur-indent (current-indentation)))))
          ;; This was not a closing tag, so we check if the previous line
          ;; was an opening tag.
          (save-excursion
            ;; Keep moving back until we find a line that is not blank
            (while (progn
                     (forward-line -1)
                     (and (not (bobp)) (looking-at cicero-mode-blank-line))))
            (setq cur-indent (current-indentation))
            (if (or (re-search-forward cicero-mode-dangling-open old-pnt t) (looking-at cicero-mode-else-line))
                (setq cur-indent (+ cur-indent cicero-basic-offset)))))

        ;; Reduce the indentation by one level if it is an else tag.
        (if (looking-at cicero-mode-else-line)
            (setq cur-indent (- cur-indent cicero-basic-offset)))

        ;; Finally, we execute the actual indentation.
        (if (> cur-indent 0)
            (indent-line-to cur-indent)
          (indent-line-to 0))))))

(defconst cicero-mode-font-lock-keywords
  `((,cicero-mode-section (1 'cicero-mode-section-face))
    (,cicero-mode-else (1 'cicero-mode-section-face))
    (,cicero-mode-comment (1 'cicero-mode-comment-face))
    (,cicero-mode-include (1 'cicero-mode-include-face))
    (,cicero-mode-builtins (1 'cicero-mode-builtins-face))
    (,cicero-mode-variable (1 font-lock-constant-face))
    (,cicero-mode-variable-path (1 font-lock-constant-face))
    (,cicero-mode-variable-path-parent (1 font-lock-constant-face))
    (,(concat "</?\\(" cicero-mode-pair-tag "\\)") (1 font-lock-function-name-face))
    (,(concat "<\\(" cicero-mode-standalone-tag "\\)") (1 font-lock-function-name-face))
    (,cicero-mode-html-constant (1 font-lock-variable-name-face))))

;;;###autoload
(define-derived-mode cicero-mode fundamental-mode "Cicero"
  (set (make-local-variable 'indent-line-function) 'cicero-indent)
  (set (make-local-variable 'indent-tabs-mode) nil)
  (set (make-local-variable 'comment-start) "{{!")
  (set (make-local-variable 'comment-end) "}}")
  (set (make-local-variable 'font-lock-defaults) '(cicero-mode-font-lock-keywords)))

;;;###autoload
(add-to-list 'auto-mode-alist '("\\.tem$" . cicero-mode))

(provide 'cicero-mode)

;;; cicero-mode.el ends here
