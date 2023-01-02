theory Shifts
  imports Frame Append
begin


lemma shift_entails_prem: "(As ** A) ** Bs \<turnstile> Q \<Longrightarrow> As ** A ** Bs \<turnstile> Q"
  by simp 


lemma shift_frame_prem: "((As ** A) ** Bs) -- PR \<tturnstile> Q -- QR \<Longrightarrow> (As ** A ** Bs) -- PR \<tturnstile> Q -- QR"
  by simp


lemma shift_frame_conc: "P -- PR \<tturnstile> ((As ** A) ** Bs) -- QR \<Longrightarrow> P -- PR \<tturnstile> (As ** A ** Bs) -- QR"
  by simp


method all_entails_prem_shifts methods M = append \<open>M\<close> \<open>rule shift_entails_prem, all_entails_prem_shifts M\<close>
method all_frame_prem_shifts methods M = append \<open>M\<close> \<open>rule shift_frame_prem, all_frame_prem_shifts M\<close>
method all_frame_conc_shifts methods M = append \<open>M\<close> \<open>rule shift_frame_conc, all_frame_conc_shifts M\<close>


end