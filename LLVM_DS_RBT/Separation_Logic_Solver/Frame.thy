theory Frame
  imports "Isabelle_LLVM.Frame_Infer"
begin


section "Frame"


definition frame ("_/ -- _/ \<tturnstile> _/ -- _" [0,0,0,10] 10 ) where "frame p pr q qr \<equiv> p ** pr \<turnstile> q ** qr"


abbreviation post_frame ("_/ \<tturnstile> _/ -- _" [0,0,10] 10)
  where "post_frame p q qr \<equiv> frame p \<box> q qr"


abbreviation pre_frame ("_/ -- _/ \<tturnstile> _" [0,0,10] 10)
  where "pre_frame p pr q \<equiv> frame p pr q \<box>"


lemma frameD: "p -- pr  \<tturnstile> q -- qr \<Longrightarrow> p ** pr \<turnstile> q ** qr"
  unfolding frame_def by simp


lemma frameI: "p ** pr \<turnstile> q ** qr \<Longrightarrow> p ** pr \<tturnstile> q -- qr"
  unfolding frame_def by simp


end