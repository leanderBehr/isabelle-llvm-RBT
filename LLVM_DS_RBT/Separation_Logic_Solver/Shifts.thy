theory Shifts
  imports Frame Append
begin


lemma shift_entails_prem: "(As ** A) ** Bs \<turnstile> Q \<Longrightarrow> As ** A ** Bs \<turnstile> Q"
  by simp


lemma shift_entails_conc: "P \<turnstile> (As ** A) ** Bs \<Longrightarrow> P  \<turnstile> As ** A ** Bs"
  by simp


lemma shift_frame_prem: "((As ** A) ** Bs) -- PR \<tturnstile> Q -- QR \<Longrightarrow> (As ** A ** Bs) -- PR \<tturnstile> Q -- QR"
  by simp


lemma shift_frame_conc: "P -- PR \<tturnstile> ((As ** A) ** Bs) -- QR \<Longrightarrow> P -- PR \<tturnstile> (As ** A ** Bs) -- QR"
  by simp

method_setup no_inst_rule = 
  \<open>Attrib.thms >> (fn thms => fn ctxt => SIMPLE_METHOD' (match_tac ctxt thms THEN_ALL_NEW Goal.norm_hhf_tac ctxt))\<close>

method all_entails_prem_shifts methods M = append \<open>M\<close> \<open>no_inst_rule shift_entails_prem, all_entails_prem_shifts M\<close>
method all_entails_conc_shifts methods M = append \<open>M\<close> \<open>no_inst_rule shift_entails_conc, all_entails_conc_shifts M\<close>
method all_frame_prem_shifts methods M = append \<open>M\<close> \<open>no_inst_rule shift_frame_prem, all_frame_prem_shifts M\<close>
method all_frame_conc_shifts methods M = append \<open>M\<close> \<open>no_inst_rule shift_frame_conc, all_frame_conc_shifts M\<close>


end