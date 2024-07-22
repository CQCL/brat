(load-file "~/.local/share/brat/brat-mode.el")
(load-file "~/.local/share/brat/lsp-brat.el")
(add-hook 'brat-mode-hook #'lsp)

(add-to-list 'exec-path "~/.local/bin")
