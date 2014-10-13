;; 
;; ProofGneral に適したウィンドウを開く。
;;
(global-set-key [f4] 'coq-windows)
(defun coq-windows ()
  "Setup Windows for Proof General"
  (interactive)
  (delete-other-windows)
  (new-frame)
  (other-frame 1)
  (split-window-vertically)
  (switch-to-buffer "*goals*")
  (other-window 1)
  (switch-to-buffer "*response*"))
;; end
