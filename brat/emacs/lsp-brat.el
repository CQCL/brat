(require 'lsp-mode)

(defvar lsp-brat-server-path "~/.local/bin/lsp-brat")

;; Associate brat-mode with this lsp mode
;; (not sure if this is different to the :major-modes line below?)
(add-to-list 'lsp-language-id-configuration '(brat-mode . "brat"))

;; Register the client itself
(lsp-register-client
  (make-lsp--client
    :new-connection (lsp-stdio-connection lsp-brat-server-path)
    :major-modes '(brat-mode)
    :server-id 'lsp-brat
    :initialized-fn 'ignore
    :language-id "brat"
    :completion-in-comments? nil
    :ignore-messages nil
    ))

(provide 'lsp-brat)
