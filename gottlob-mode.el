(require 'comint)
(require 'compile)

(defvar gottlob-mode-map
   (let ((map (make-sparse-keymap)))
     ;; (define-key map [foo] 'gottlob-do-foo)
     map)
   "Keymap for `gottlob-mode'.")

(defvar gottlob-mode-syntax-table
  (let ((st (make-syntax-table)))
    (modify-syntax-entry ?- ". 12b" st)
    (modify-syntax-entry ?\n "> b" st)
    ;; (modify-syntax-entry ?{- "({-" st)
    ;; (modify-syntax-entry ?-} ")-}" st)
    st)
  "Syntax table for `gottlob-mode'.")


(defvar gottlob-keywords
  '("data" "where"
    "forall" "iota"
    "case" "of"
    "theorem" "proof" "qed" 
    "module"
    "infix" "infixl" "infixr" "pre" "post"
    "formula" "prog" "set" "special" "tactic"
    "cmp" "invcmp" "inst" "mp" "discharge"
    "ug" "beta" "invbeta" "by" "from"
    ))


(defvar gottlob-builtins
  '(
                ;; Ordering
                ;; 'Derived' operators
                "show" )
        )

(defvar gottlob-types
        '("Type" "Nat" "Formula" "LogicalKind" "Bool")
                )

;; (defvar gottlob-operators
;;         '("fuc" "\\:\\:" )
;;         )
(defvar gottlob-keywords-regexp (regexp-opt gottlob-keywords 'words))
(defvar gottlob-types-regexp (regexp-opt gottlob-types 'words))
;;(defvar gottlob-operators-regexp ":[:]? \\|->\\| = \\| \\. \\| \\\\ | \\] \\| \\[ ")
(defvar gottlob-builtins-regexp (regexp-opt gottlob-builtins 'words))
;;(defvar gottlob-prog-regexp "\\b[[:lower:]_][[:alnum:]'_]*\\b")
(defvar gottlob-set-regexp "\\b[[:upper:]][[:alnum:]'_]*\\b")


;; font-lock-builtin-face
;; font-lock-comment-delimiter-face
;; font-lock-comment-face
;; font-lock-constant-face
;; font-lock-doc-face
;; font-lock-function-name-face
;; font-lock-keyword-face
;; font-lock-negation-char-face
;; font-lock-preprocessor-face
;; font-lock-reference-face
;; font-lock-string-face
;; font-lock-type-face
;; font-lock-variable-name-face
;; font-lock-warning-face
(defvar gottlob-font-lock-keywords
   `(
                 (,gottlob-keywords-regexp . font-lock-keyword-face)
                 (,gottlob-types-regexp . font-lock-type-face)
;;                 (,gottlob-operators-regexp . font-lock-variable-name-face)
;;                 (,gottlob-prog-regexp . font-lock-function-name-face)
                 (,gottlob-builtins-regexp . font-lock-variable-name-face)
                 (,gottlob-set-regexp . font-lock-type-face)
                 )
   "Keyword highlighting specification for `gottlob-mode'.")

 ;; (defvar gottlob-imenu-generic-expression
 ;;   ...)

 ;; (defvar gottlob-outline-regexp
 ;;   ...)

 ;;;###autoload

 ;;; Indentation

 (defun gottlob-indent-line ()
   "Indent current line of Gottlob code."
   (interactive)
   (let ((savep (> (current-column) (current-indentation)))
         (indent (condition-case nil (max (gottlob-calculate-indentation) 0)
                   (error 0))))
     (if savep
         (save-excursion (indent-line-to indent))
       (indent-line-to indent))))

 (defun gottlob-calculate-indentation ()
   "Return the column to which the current line should be indented."
   0)

(defun gottlob-comment-dwim (arg)
        "Comment or uncomment current line or region in a smart way.
For details, see `comment-dwim'."
   (interactive "*P")
   (require 'newcomment)
   (let ((deactivate-mark nil) (comment-start "--") (comment-end ""))
     (comment-dwim arg)))


;; Run the typechecker
(defun gottlob-typecheck-buffer ()
        (interactive)
        (let ((fname (buffer-file-name))
                                ;; Should pull this from a customizable variable.
              (cmdstr (concat "gottlob " buffer-file-name)))
          (set (make-local-variable 'compile-command) cmdstr)
          (call-interactively 'compile)))


(define-derived-mode gottlob-mode fundamental-mode "Gottlob"
   "A major mode for editing Gottlob files."
   :syntax-table gottlob-mode-syntax-table
   (set (make-local-variable 'comment-start) "-- ")
   ;; (set (make-local-variable 'comment-start-skip) "#+\\s-*")
   (set (make-local-variable 'font-lock-defaults)
                                '(gottlob-font-lock-keywords))
   ;; (set (make-local-variable 'indent-line-function) 'gottlob-indent-line)
   ;; (set (make-local-variable 'imenu-generic-expression)
         ;;                     gottlob-imenu-generic-expression)
   ;; (set (make-local-variable 'outline-regexp) gottlob-outline-regexp)

         ; Add the 'typecheck' command
   (define-key gottlob-mode-map (kbd "C-c C-t") 'gottlob-typecheck-buffer)
   (define-key gottlob-mode-map (kbd "C-c C-l") 'gottlob-repl-load)
   (define-key gottlob-mode-map (kbd "C-c C-r") 'gottlob-repl-reload)

         ; set up the comments
   (define-key gottlob-mode-map [remap comment-dwim] 'gottlob-comment-dwim)
   )


;; Interactive mode

(defvar inferior-gottlob-buffer nil)
(defcustom gottlob-repl-command "gottlob-repl" "ha")
(defun gottlob-run-repl (&optional dont-switch-p)
  (if (not (comint-check-proc "*gottlob*"))
      (save-excursion (let ((cmdlist nil))
                        (set-buffer (apply 'make-comint "gottlob"
                                           gottlob-repl-command
                                           nil nil))
                        (gottlob-repl-mode))))
  (setq inferior-gottlob-buffer "*gottlob*")
  (if (not dont-switch-p)
      (pop-to-buffer "*gottlob*")))

(defun gottlob-repl-send-cmd (cmd &optional args)
        (interactive)
        (gottlob-run-repl)
        (comint-send-string inferior-gottlob-buffer cmd)
        (comint-send-string inferior-gottlob-buffer " ")
        (if args
            (comint-send-string inferior-gottlob-buffer args))
        (comint-send-string inferior-gottlob-buffer "\n"))


(defun gottlob-repl-load ()
        "Load the file in the current buffer."
        (interactive)
        (let ((filename (buffer-file-name)))
          (gottlob-repl-send-cmd ":load" filename)))


(defun gottlob-repl-reload ()
        "Reload the current module."
        (interactive)
        (gottlob-repl-send-cmd ":reload" ""))

;; Cribbed from haskell-inf mode
(define-derived-mode gottlob-repl-mode comint-mode "Gottlob-Repl"
        "Mode for interacting with gottlob interactive process"
        (set (make-local-variable 'comint-prompt-regexp)
                         "^gottlob> ")

        ;(add-hook 'comint-output-filter-functions      'gottlob-repl-spot-prompt nil t)
  (set (make-local-variable 'compilation-error-regexp-alist)
       gottlob-repl-error-regexp-alist)
  (set (make-local-variable 'compilation-first-column) 0) ;GHCI counts from 0.
        (compilation-shell-minor-mode 1))

(defconst gottlob-repl-error-regexp-alist
    `(("^\\(.+?\\):\\([0-9]+\\):\\(\\([0-9]+\\):\\)?\\( \\|\n *\\)\\(Warning\\)?"
     1 2 4 ,@(if (fboundp 'compilation-fake-loc)
                 '((6) nil (5 '(face nil font-lock-multiline t)))))))


(provide 'gottlob-mode)
