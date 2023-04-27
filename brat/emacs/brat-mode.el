(defconst brat-prim-types
  "[^[:alnum:]]\\(Vec\\|Nat\\|Int\\|List\\|Bool\\|Bit\\|Qubit\\|Pair\\|\\Type\\|String\\|Float\\|Option\\|<<<\\)")
(defconst brat-prim-kinds
  "\\*\\|#")
(defconst brat-import "\\(open\\)?[[:space:]]*import[[:space:]]*[[:alnum:]\\.]*[[:space:]]*\\(as\\)")
(defconst brat-punctuation "?\\|;\\|->\\|\\|,\\|=")
(defconst brat-tricky-punctuation "\\(-o\\)\\|\\(=>\\)\\|:\\|,")
(defconst brat-port-pull "\\([[:alnum:]'_-]*:\\)+[^:]")
(defconst brat-comments "\\(--\\)\\(.*\\)$")
(defconst brat-holes "?[[:alnum:]'_-]*")
(defconst brat-keywords "\\b\\(type\\|open\\|import\\|ext\\|let\\|in\\)\\([[:space:]]\\|[^[:alnum:]'_-]\\|$\\)\\b")
(defconst brat-decl
  "^[[:space:]]*\\(ext[[:space:]]*\".*\"\\)?[[:space:]]*\\([[:alnum:]'_-]*\\)\\((.*)[[:space:]]*-\\|[[:space:]]*::\\)")
(defconst brat-decl2 "^[[:space:]]*\\([[:alnum:]'_-]*\\)[[:print:]]*=")
(defconst brat-literal "\\(^\\|[[:space:]]\\|[^[:alpha:]]\\)\\(true\\|false\\|[-]?[[:digit:]]+\\)")
(defconst brat-con "\\(1\\+\\|2\\*\\|nil\\|cons\\|some\\|none\\)[^[:alnum:]'_-]")

(defvar brat-font-lock-keywords
  (list
   (cons brat-keywords    '(0 font-lock-keyword-face))
   (cons brat-import      '(2 font-lock-keyword-face))
   (cons brat-decl        '(2 font-lock-function-name-face))
   (cons brat-decl2       '(1 font-lock-function-name-face))
   ;(cons brat-port-pull   '(1 font-lock-type-face))
   (cons brat-prim-types  '(1 font-lock-type-face))
   (cons brat-prim-kinds  '(0 font-lock-type-face))
   (cons brat-punctuation 'font-lock-builtin-face)
   (cons brat-tricky-punctuation '((0 font-lock-builtin-face nil)))
   (cons brat-holes       '(0 font-lock-preprocessor-face t))
   (cons brat-literal     '(2 font-lock-constant-face))
   (cons brat-con         '(1 font-lock-builtin-face t))
   (cons brat-comments    '((1 font-lock-comment-delimiter-face t)
                            (2 font-lock-comment-face t)))
   ))

(add-to-list 'auto-mode-alist '("\\.brat\\'" . brat-mode))

(defun brat-compile-buffer()
  (interactive)
  (compile (format "brat %s" buffer-file-name)))

(defvar brat-mode-map
  (let ((map (make-sparse-keymap)))
    (define-key map "\C-c\C-c" 'brat-compile-buffer)
    map))

(define-derived-mode brat-mode
  prog-mode "BRAT"
  "Major mode for brat programming
  \\{brat-mode-map}"
  (setq font-lock-defaults '(brat-font-lock-keywords)))
