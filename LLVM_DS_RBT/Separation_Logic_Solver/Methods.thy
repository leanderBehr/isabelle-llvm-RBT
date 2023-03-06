theory Methods
  imports
    Shifts
    Append
    "HOL-Eisbach.Eisbach_Tools"
begin


section "Tools"


method is_sep_goal = 
  succeeds 
  \<open>(match conclusion in "?X \<turnstile> ?Y" \<Rightarrow> succeed \<bar> "?P -- ?PR \<tturnstile> ?Q -- ?QR" \<Rightarrow> succeed \<bar> _ \<Rightarrow> fail)\<close>

method is_non_sep_goal = fails \<open>is_sep_goal\<close>

method any_succeed methods m = fails \<open>all \<open>fails m\<close>\<close>


method has_any_sep_goal = any_succeed \<open>is_sep_goal\<close>


method defer_non_sep_goal = then_else \<open>is_sep_goal\<close> \<open>fail\<close> \<open>defer_tac\<close>


method solves_sep_goals methods m = m;fails \<open>is_sep_goal\<close> 


section "Normalization"


lemma frame_cong: "\<lbrakk>p\<equiv>p'; q\<equiv>q'\<rbrakk> \<Longrightarrow> frame p pr q qr \<equiv> frame p' pr q' qr" by simp
lemma sep_conj_cong: "\<lbrakk>x\<equiv>x'; y\<equiv>y'\<rbrakk> \<Longrightarrow> x ** y \<equiv> x' ** y'" by simp


(*simp without any rules other than those given*)
method_setup normalize_with_impl = 
  \<open>Attrib.thms >>
  (fn thms => fn ctxt => 
    SIMPLE_METHOD'
      (simp_tac (
        ((empty_simpset ctxt) addsimps thms)
      )
  ))\<close>


lemma n1: "\<box> ** X \<equiv> X" by simp
lemma n2: "X ** \<box> \<equiv> X" by simp
lemma n3: "((P ** Q) ** R) \<equiv> (P ** Q ** R)" by simp


method normalize_with uses thms = normalize_with_impl thms


method isep_normalize = is_sep_goal, changed \<open>normalize_with_impl n1 n2 n3\<close>


section "Methods"


method has_rule uses rule = (match rule in _ \<Rightarrow> succeed) | (print_term "NO_RULE_GIVEN", fail)


method star methods m = (m+)?





method_setup no_inst_drule = 
  \<open>Attrib.thms >> (fn thms => fn ctxt => SIMPLE_METHOD' (dmatch_tac ctxt thms THEN_ALL_NEW Goal.norm_hhf_tac ctxt))\<close>


method_setup no_inst_erule = 
  \<open>Attrib.thms >> (fn thms => fn ctxt => SIMPLE_METHOD' (ematch_tac ctxt thms THEN_ALL_NEW Goal.norm_hhf_tac ctxt))\<close>


subsection "Assumption"


subsubsection "Frame"


(*matches second conjunct of premise against first conjunct of conclusion*)
(*order matters for prioritization*)
lemma frame_assumption_rule:
  "As ** Bs -- PR \<tturnstile> Ds ** Cs -- QR \<Longrightarrow> As ** A ** Bs -- PR \<tturnstile> Ds ** A ** Cs -- QR" (*multi elem conj both sides*)
  "As -- PR \<tturnstile> Ds ** Cs -- QR \<Longrightarrow> As ** A -- PR \<tturnstile> Ds ** A ** Cs -- QR"             (*single elem left, multi elem right, mut. ex. with next*)
  "As ** Bs -- PR \<tturnstile> Ds ** \<box> -- QR \<Longrightarrow> As ** A ** Bs -- PR \<tturnstile> Ds ** A -- QR"        (*multi elem left, single elem right, mut. ex. with prev.*)
  "As -- PR \<tturnstile> Ds ** \<box> -- QR \<Longrightarrow> As ** A -- PR \<tturnstile> Ds ** A -- QR"                    (*single elem conj both sides*)
  unfolding frame_def 
  apply (simp add: conj_entails_mono sep_conj_left_commute)+
  done

lemma frame_prem_boxD: "\<box> ** A -- PR \<tturnstile> B -- QR \<Longrightarrow>  A -- PR \<tturnstile> B -- QR" by simp
lemma frame_prem_boxI: "A -- PR \<tturnstile> B -- QR \<Longrightarrow> \<box> ** A -- PR \<tturnstile> B -- QR" by simp

lemma frame_conc_boxD: "A -- PR \<tturnstile> \<box> ** B -- QR \<Longrightarrow>  A -- PR \<tturnstile> B -- QR" by simp
lemma frame_conc_boxI: "A -- PR \<tturnstile> B -- QR \<Longrightarrow> A -- PR \<tturnstile> \<box> ** B -- QR" by simp

method frame_assumption' =
  rule frame_prem_boxD,
  rule frame_conc_boxD,
  all_frame_conc_shifts \<open>all_frame_prem_shifts \<open>determ \<open>rule frame_assumption_rule\<close>\<close>\<close>,
  isep_normalize?,
  (rule frame_prem_boxI)?, (*does not apply if only the box is left*)
  (rule frame_conc_boxI)? (*does not apply if only the box is left*)


lemma frame_boxI: 
  "\<box> -- \<box> \<tturnstile> \<box> -- \<box>" (*perfectly balanced as all things should be*)
  "\<box> -- Q \<tturnstile> Q -- \<box>" (*premise exhausted*)
  "P -- \<box> \<tturnstile> \<box> -- P" (*conclusion exhausted*)
  unfolding frame_def
  by simp+


method end_frame = determ \<open>rule frame_boxI\<close>


method frame_assumption = end_frame | frame_assumption', end_frame?


(*matches second conjunct of premise against first conjunct of conclusion*)
(*order matters for prioritization*)
lemma frame_rev_assumption_rule:
  "Cs -- PR \<tturnstile> As ** Bs -- QR \<Longrightarrow> A ** Cs -- PR \<tturnstile> As ** A ** Bs -- QR" (*multi elem conj both sides*)
  "Cs -- PR \<tturnstile> As -- QR \<Longrightarrow> A ** Cs -- PR \<tturnstile> As ** A -- QR"             (*single elem left, multi elem right, mut. ex. with next*)
  "\<box> -- PR \<tturnstile> As ** Bs -- QR \<Longrightarrow> A -- PR \<tturnstile> As ** A ** Bs -- QR"        (*multi elem left, single elem right, mut. ex. with prev.*)
  "\<box> -- PR \<tturnstile> As -- QR \<Longrightarrow> A -- PR \<tturnstile> As ** A -- QR"                    (*single elem conj both sides*)
  unfolding frame_def 
  apply (simp add: conj_entails_mono sep_conj_left_commute)+
  done


method frame_rev_assumption' =
  rule frame_conc_boxD,
  all_frame_conc_shifts \<open>determ \<open>rule frame_rev_assumption_rule\<close>\<close>,
  isep_normalize?,
  (rule frame_conc_boxI)? (*does not apply if only the box is left*)
    

method frame_rev_assumption = end_frame | frame_rev_assumption', end_frame?


subsubsection "Entails"


lemma degenerate_frameD: "P -- \<box> \<tturnstile> Q -- \<box> \<Longrightarrow> P \<turnstile> Q" unfolding frame_def by simp
lemma degenerate_frameI: "P \<turnstile> Q \<Longrightarrow> P -- \<box> \<tturnstile> Q -- \<box>" unfolding frame_def by simp


method entails_assumption' = rule degenerate_frameD, frame_assumption', rule degenerate_frameI 
method entails_assumption = rule degenerate_frameD, frame_assumption, (rule degenerate_frameI)?


method entails_rev_assumption' = rule degenerate_frameD, frame_rev_assumption', rule degenerate_frameI
method entails_rev_assumption = rule degenerate_frameD, frame_rev_assumption, (rule degenerate_frameI)?


subsubsection "Combined"
  

method is_entails = match conclusion in "?P \<turnstile> ?Q" (cut) \<Rightarrow> succeed \<bar> _ (cut) \<Rightarrow> fail
method is_frame = match conclusion in "?P -- ?PR \<tturnstile> ?Q -- ?QR" (cut) \<Rightarrow> succeed \<bar> _ (cut) \<Rightarrow> fail

method is_pre_frame = match conclusion in "?P -- ?PR \<tturnstile> ?Q" (cut) \<Rightarrow> succeed \<bar> _ (cut) \<Rightarrow> fail
method is_post_frame = match conclusion in "?P \<tturnstile> ?Q -- ?QR" (cut) \<Rightarrow> succeed \<bar> _ (cut) \<Rightarrow> fail


method isep_assumption = 
  entails_assumption |
  is_post_frame, frame_assumption |
  is_pre_frame, frame_rev_assumption

schematic_goal "A ** B ** C ** X \<tturnstile> B ** C ** A -- ?QR"
  apply isep_assumption
  apply isep_assumption
  apply isep_assumption
  done


schematic_goal "A ** B ** C -- ?PR \<tturnstile> B ** C ** X ** A"
  apply isep_assumption
  apply isep_assumption
  apply isep_assumption
  done


subsection "Rule Application"


lemma frame_reduction_rule:
  assumes
    weaken_pre: "P_o \<tturnstile> P -- PR_o" and
    strengthen_post: "Q -- QR_o \<tturnstile> Q_o" and
    reduction: "is_sep_red P' Q' P Q" and
    reduced: "P' ** PR_o -- PR \<tturnstile> Q' ** QR_o -- QR"
  shows "P_o -- PR \<tturnstile> Q_o -- QR"
  using assms unfolding frame_def is_sep_red_def
  by (simp add: sep_drule(2) sep_rule(2))


method isep_red_rule_raw uses red_rule =
  (
    has_rule rule: red_rule,
    (rule degenerate_frameD)?,
    rule frame_reduction_rule[OF _ _ red_rule],
    (isep_normalize?)[2],
    prefer_last,
    (no_inst_rule degenerate_frameI)?,
    isep_normalize?,
    defer_tac
  )[1]


method isep_red_rule uses red_rule =
  isep_red_rule_raw red_rule: red_rule,
  (star isep_assumption)[2]


lemma intro_red_rule:
  assumes intro: "Q' \<turnstile> Q"
  shows "is_sep_red \<box> Q' \<box> Q"
  apply (rule is_sep_redI)
  subgoal premises prems
    apply (rule sep_drule[OF prems])
    apply (rule conj_entails_mono)
    using intro by simp+
  done


method isep_rule uses rule = has_rule rule: rule, isep_red_rule red_rule: intro_red_rule[OF rule]
                                                                                  

lemma dest_red_rule:
  assumes drule: "P \<turnstile> P'"
  shows "is_sep_red P' \<box> P \<box>"
  apply (rule is_sep_redI)
  subgoal premises prems
    apply (rule sep_rule[OF prems])
    apply (rule conj_entails_mono)
    using drule by simp+
  done


method isep_drule uses drule = has_rule rule: drule, isep_red_rule red_rule: dest_red_rule[OF drule]


lemma
  assumes 
    d1: "A \<turnstile> B" and d2: "B \<turnstile> C" and d3: "C \<turnstile> D"
  shows "A \<turnstile> D"
  apply (isep_drule drule: d1)
  apply (isep_drule drule: d2)
  apply (isep_drule drule: d3)
  apply isep_assumption
  done              


lemma
  assumes 
    d1: "A \<turnstile> B" and d2: "B \<turnstile> C" and d3: "C \<turnstile> D"
  shows "A \<turnstile> D"
  apply (isep_rule rule: d3)
  apply (isep_rule rule: d2)
  apply (isep_rule rule: d1)
  apply isep_assumption
  done


method sep_red_rule_must_succeed uses red_rule =
  isep_red_rule_raw red_rule: red_rule,
  (all \<open>solves \<open>isep_assumption+\<close>\<close>)[2];
  isep_normalize?


method isep_backtracking_red_rule uses red_rule = match red_rule in r: _ \<Rightarrow> \<open>sep_red_rule_must_succeed red_rule: r\<close>
method isep_backtracking_rule uses rule = match rule in r: _ \<Rightarrow> \<open>sep_red_rule_must_succeed red_rule: intro_red_rule[OF r]\<close>
method isep_backtracking_drule uses drule = match drule in r: _ \<Rightarrow> \<open>sep_red_rule_must_succeed red_rule: dest_red_rule[OF r]\<close>


lemma
  assumes 
    d1: "A \<turnstile> B" and d2: "B \<turnstile> C" and d3: "C \<turnstile> D" and trap1: "T \<turnstile> D" and trap2: "T \<turnstile> C" and trap3: "T \<turnstile> B"
  shows "A \<turnstile> D"
  apply ((isep_backtracking_rule rule: trap1 trap2 trap3 d1 d2 d3)+, isep_assumption)
  done


subsection "Existential Quantifier Handling"


lemma sep_exI: "P x \<turnstile> (EXS x. P x)"
  apply (rule entails_exI)
  by auto


lemma entails_exE: "(\<And>x. P x \<turnstile> C) \<Longrightarrow> (EXS x. P x) \<turnstile> C"
  unfolding entails_def
  by blast


lemma frame_exE: "(\<And>x. P x -- Pr \<tturnstile> Q -- Qr) \<Longrightarrow> (EXS x. P x) -- Pr \<tturnstile> Q -- Qr"
  unfolding frame_def entails_def sep_conj_def
  by blast


method isep_elim_ex = 
  (simp (no_asm) only: sep_conj_exists cong: entails_pre_cong)?,
  ((rule entails_exE)+ | (rule frame_exE)+),
  isep_normalize?


method isep_intro_ex =
  (simp (no_asm) only: sep_conj_exists cong: entails_post_cong)?,
  (isep_backtracking_rule rule: sep_exI)+,
  isep_normalize?


method isep_intro_ex_with for x =
  (simp (no_asm) only: sep_conj_exists cong: entails_post_cong)?,
  isep_backtracking_rule rule: sep_exI[where x=x],
  isep_normalize?


subsection "Pure Assertion Handling"

lemma pure_entails_boxI:
  "sep_is_pure_assn X \<Longrightarrow> X \<turnstile> \<box>"
  unfolding entails_def sep_is_pure_assn_def by auto


method entails_box_solver = rule pure_entails_boxI, (auto intro!: sep_is_pure_assn_conjI)[1]


lemma frame_pureI: "\<lbrakk>pure_part P \<Longrightarrow> P -- Pr \<tturnstile> Q -- Qr\<rbrakk> \<Longrightarrow> P -- Pr \<tturnstile> Q -- Qr"
  unfolding frame_def
  using entails_pureI pure_part_split_conj by auto


lemma dupl_D:  "P \<Longrightarrow> P \<Longrightarrow> True" ..


method thin_duplicate = (determ \<open>drule(1) dupl_D, thin_tac True\<close>)
method thin_duplicates = thin_duplicate+ 

method isep_extract_pure =
  changed \<open>
    (rule entails_pureI | rule frame_pureI),
    star \<open>erule conjE | determ \<open>drule pure_part_split_conj\<close>\<close>,
    thin_duplicates?
  \<close>
  
subsection "Solver"

named_theorems isep_intro
named_theorems isep_dest
named_theorems isep_red

locale separation_logic_solver
begin
definition "TAG x = x"

lemma entails_TAGG: 
"A \<turnstile> B ** TAG C \<Longrightarrow> A \<turnstile> B ** C" unfolding TAG_def by simp

lemma frame_TAGG: 
"A -- Pr \<tturnstile> B ** TAG C -- Qr \<Longrightarrow> A -- Pr \<tturnstile> B ** C -- Qr" unfolding TAG_def by simp

lemma TAG_def_norm: "TAG x \<equiv> x" unfolding TAG_def by simp

method first_partition_entails methods m =
  all_entails_conc_shifts \<open>rule entails_TAGG, isep_normalize?, m; (normalize_with thms: TAG_def_norm)?\<close> | m

method first_partition_frame methods m =
  all_frame_conc_shifts \<open>rule frame_TAGG, isep_normalize?, m; (normalize_with thms: TAG_def_norm)?\<close> | m


method first_partition methods m = 
  is_entails, first_partition_entails m |
  is_frame, first_partition_frame m


lemma "P -- Pr \<tturnstile> A ** B ** C ** D -- Qr"
  apply (first_partition \<open>print_headgoal, fail\<close>)? oops

method sep_step =
  is_sep_goal,
  (
    isep_normalize |
    isep_extract_pure |
    entails_box_solver |
    isep_elim_ex |
    (
      first_partition
      \<open>
        append
          isep_assumption
          \<open>isep_backtracking_red_rule red_rule: fri_red_rules isep_red\<close>
          \<open>isep_backtracking_rule rule: isep_intro\<close>
          \<open>isep_backtracking_drule drule: isep_dest\<close>
      \<close>      
    )
  )

method sepE_step declares isep_red isep_intro isep_dest = append sep_step \<open>(is_sep_goal, isep_intro_ex)\<close> 


method sep_step_filter methods filter declares isep_red isep_intro isep_dest =
  sep_step;(is_sep_goal | filter)[1]

method sepE_step_filter methods filter declares isep_red isep_intro isep_dest = 
  sepE_step;(is_sep_goal | filter)[1]


method sep declares isep_red isep_intro isep_dest = (sep_step+)[1]
method sepE declares isep_red isep_intro isep_dest = (sepE_step+)[1]

method sepwith methods filter declares isep_red isep_intro isep_dest =
  ((sep_step_filter filter)+)[1]

method sepEwith methods filter declares isep_red isep_intro isep_dest =
  ((sepE_step_filter filter)+)[1]

method find_sep = (has_any_sep_goal, is_non_sep_goal, defer_tac)+

method sep_solves = is_non_sep_goal

end 

interpretation separation_logic_solver .

lemma
  assumes 
    d1: "A \<turnstile> B" and d2: "B \<turnstile> C" and d3: "C \<turnstile> D" and trap1: "T \<turnstile> D" and trap2: "T \<turnstile> C" and trap3: "T \<turnstile> B"
  shows "A \<turnstile> D"
  apply (sep isep_intro: trap1 trap2 trap3 d1 d2 d3; fail) done


lemma 
  assumes 
    r1: "K ** L \<turnstile> X ** Z" and r2: "M ** N \<turnstile> Y ** W" and
    dr1:"A ** B \<turnstile> K ** N" and dr2:"C ** D \<turnstile> L ** M" 
  shows "A ** B ** C ** D \<turnstile> X ** Y ** Z ** W"
  apply (sep isep_intro: r1 r2 isep_dest: dr1 dr2)
  done


lemma 
  assumes
    trap: "False \<Longrightarrow> A \<turnstile> B" and rule: "True \<Longrightarrow> A \<turnstile> B"
  shows "A \<turnstile> B"
  apply (sep isep_intro: trap rule | find_sep)+ back ..

lemma sep_pureI [isep_intro]: "B \<Longrightarrow> \<box> \<turnstile> \<up>B"
  by (simp add: pure_true_conv)


lemma frame_FRAMEI: "P \<tturnstile> Q -- R \<Longrightarrow> FRAME P Q R"
  unfolding frame_def FRAME_def by simp


lemma entails_FRAME_INFERI: "P \<turnstile> Q \<Longrightarrow> FRAME_INFER P Q \<box>"
  unfolding FRAME_INFER_def by simp


lemma frame_FRAME_INFERI: "P \<tturnstile> Q -- R \<Longrightarrow> FRAME_INFER P Q R"
  unfolding frame_def FRAME_INFER_def by simp


method vcg_compat = ((simp only: PRECOND_def ENTAILS_def FRI_END_def) | (no_inst_rule entails_FRAME_INFERI frame_FRAMEI frame_FRAME_INFERI))+


schematic_goal "ff A ** ff B \<tturnstile> ff ?X -- ?R"
  apply isep_assumption back
  done

lemma prune_pureE: "\<lbrakk>pure_part X; T\<rbrakk> \<Longrightarrow> T" by simp

method prune_pure = elim prune_pureE

end