theory Methods
  imports 
    Shifts
    "HOL-Eisbach.Eisbach_Tools"
begin


section "Normalization"


text "We match premises so that simp only acts on conclusion"


method is_sep_goal = (match conclusion in "?X \<turnstile> ?Y" \<Rightarrow> succeed \<bar> "?P -- ?PR \<tturnstile> ?Q -- ?QR" \<Rightarrow> succeed \<bar> _ \<Rightarrow> fail)


method any_succeed methods m = fails \<open>all \<open>fails m\<close>\<close>


lemma sep_conj_noop_cong: "(x ** y) = (x ** y)" by simp
lemma frame_cong: "\<lbrakk>p=p'; q=q'\<rbrakk> \<Longrightarrow> frame p pr q qr = frame p' pr q' qr" by simp

method has_prems = match premises in _ (cut) \<Rightarrow> succeed
method match_prems methods M = 
  then_else \<open>has_prems\<close> \<open>match premises in _ (cut) \<Rightarrow> M\<close> \<open>M\<close>

method normalize_with uses thms congs = 
  is_sep_goal, match_prems \<open>simp only: thms cong: congs frame_cong\<close>


(*removed \<box> from conjunctions*)
method isep_normalize_box_conj = normalize_with thms: sep_conj_empty sep_conj_empty' congs: sep_conj_noop_cong


(*applies associativity*)
method isep_normalize_conj_braces = normalize_with thms: sep_conj_assoc


section "Methods"


method has_rule uses rule = (match rule in _ \<Rightarrow> succeed) | (print_term "NO_RULE_GIVEN", fail)


method star methods m = (m+)?


subsection "Assumption"


subsubsection "Frame"


(*matches second conjunct of premise against first conjunct of conclusion*)
(*order matters for prioritization*)
lemma frame_assumption_rule:
  "As ** Bs -- PR \<tturnstile> Cs -- QR \<Longrightarrow> As ** A ** Bs -- PR \<tturnstile> A ** Cs -- QR" (*multi elem conj both sides*)
  "As -- PR \<tturnstile> Cs -- QR \<Longrightarrow> As ** A -- PR \<tturnstile> A ** Cs -- QR"             (*single elem left, multi elem right, mut. ex. with next*)
  "As ** Bs -- PR \<tturnstile> \<box> -- QR \<Longrightarrow> As ** A ** Bs -- PR \<tturnstile> A -- QR"        (*multi elem left, single elem right, mut. ex. with prev.*)
  "As -- PR \<tturnstile> \<box> -- QR \<Longrightarrow> As ** A -- PR \<tturnstile> A -- QR"                    (*single elem conj both sides*)
  unfolding frame_def 
  apply (simp add: conj_entails_mono sep_conj_left_commute)+
  done


lemma frame_prem_boxD: "\<box> ** A -- PR \<tturnstile> B -- QR \<Longrightarrow>  A -- PR \<tturnstile> B -- QR" by simp
lemma frame_prem_boxI: "A -- PR \<tturnstile> B -- QR \<Longrightarrow> \<box> ** A -- PR \<tturnstile> B -- QR" by simp


method frame_assumption' =
  rule frame_prem_boxD,
  all_frame_prem_shifts \<open>determ \<open>rule frame_assumption_rule\<close>\<close>,
  isep_normalize_conj_braces?,
  (rule frame_prem_boxI)? (*does not apply if only the box is left*)


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


lemma frame_conc_boxD: "A -- PR \<tturnstile> \<box> ** B -- QR \<Longrightarrow>  A -- PR \<tturnstile> B -- QR" by simp
lemma frame_conc_boxI: "A -- PR \<tturnstile> B -- QR \<Longrightarrow> A -- PR \<tturnstile> \<box> ** B -- QR" by simp


method frame_rev_assumption' =
  rule frame_conc_boxD,
  all_frame_conc_shifts \<open>determ \<open>rule frame_rev_assumption_rule\<close>\<close>,
  isep_normalize_conj_braces?,
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


lemma entails_reduction_rule:
  assumes
    weaken_pre: "P_o \<tturnstile> P -- R_o" and
    (*not quite symmetric to weaken_pre because we don't have reverse frame inference*)
    (*i.e. Q ** ?R \<turnstile> Q_o*)
    strengthen_post: "Q \<turnstile> Q_o" and
    reduction: "is_sep_red P' Q' P Q" and
    reduced: "P' ** R_o \<turnstile> Q'"
  shows "P_o \<turnstile> Q_o"
proof -
  from reduction have
    "P' ** Ps \<turnstile> Q' ** Qs \<Longrightarrow> P ** Ps \<turnstile> Q ** Qs"
    for Ps Qs unfolding is_sep_red_def by blast

  then have red_rule: "P' \<and>* R_o \<turnstile> Q' \<Longrightarrow> P \<and>* R_o \<turnstile> Q"
    using sep_conj_empty by metis

  from weaken_pre have drule: "P_o \<turnstile> P ** R_o" unfolding frame_def by simp

  show "P_o \<turnstile> Q_o"
    apply (rule sep_drule[OF drule])
    apply (rule sep_rule[OF strengthen_post])
    apply (rule red_rule)
    using reduced .
qed


lemma frame_reduction_rule:
  assumes
    weaken_pre: "P_o \<tturnstile> P -- PR_o" and
    (*not quite symmetric to weaken_pre because we don't have reverse frame inference*)
    (*i.e. Q ** ?R \<turnstile> Q_o*)
    strengthen_post: "Q -- QR_o \<tturnstile> Q_o" and
    reduction: "is_sep_red P' Q' P Q" and
    reduced: "P' ** PR_o -- PR \<tturnstile> Q' ** QR_o -- QR"
  shows "P_o -- PR \<tturnstile> Q_o -- QR"
  using assms unfolding frame_def is_sep_red_def
  by (simp add: sep_drule(2) sep_rule(2))


method isep_red_rule_raw uses red_rule =
  has_rule rule: red_rule,
  (rule degenerate_frameD)?,
  rule frame_reduction_rule[OF _ _ red_rule],
  prefer_last,  
  (rule degenerate_frameI)?,
  defer_tac


method isep_red_rule uses red_rule =
  isep_red_rule_raw red_rule: red_rule,
  (star isep_assumption)[2];
  isep_normalize_box_conj?; 
  isep_normalize_conj_braces?


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
  isep_normalize_box_conj?; 
  isep_normalize_conj_braces?


method isep_backtracking_red_rule uses red_rule = match red_rule in r: _ \<Rightarrow> \<open>sep_red_rule_must_succeed red_rule: r\<close>
method isep_backtracking_rule uses rule = match rule in r: _ \<Rightarrow> \<open>sep_red_rule_must_succeed red_rule: intro_red_rule[OF r]\<close>
method isep_backtracking_drule uses drule = match drule in r: _ \<Rightarrow> \<open>sep_red_rule_must_succeed red_rule: dest_red_rule[OF r]\<close>


lemma
  assumes 
    d1: "A \<turnstile> B" and d2: "B \<turnstile> C" and d3: "C \<turnstile> D" and trap1: "T \<turnstile> D" and trap2: "T \<turnstile> C" and trap3: "T \<turnstile> B"
  shows "A \<turnstile> D"
  apply ((isep_backtracking_rule rule: trap1 trap2 trap3 d1 d2 d3)+, isep_assumption)
  done


named_theorems isep_intro
named_theorems isep_dest
named_theorems isep_reduction


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
  (normalize_with thms: sep_conj_exists congs: entails_pre_cong)?,
  (rule entails_exE)+ | (rule frame_exE)+,
  isep_normalize_conj_braces?


method isep_intro_ex =
  (normalize_with thms: sep_conj_exists congs: entails_post_cong)?,
  (isep_backtracking_rule rule: sep_exI)+,
  isep_normalize_conj_braces?


method isep_intro_ex_with for x =
  (normalize_with thms: sep_conj_exists congs: entails_post_cong)?,
  isep_backtracking_rule rule: sep_exI[where x=x],
  isep_normalize_conj_braces?


lemma pure_entails_boxI:
  "sep_is_pure_assn X \<Longrightarrow> X \<turnstile> \<box>"
  unfolding entails_def sep_is_pure_assn_def by auto


method entails_box_solver = rule pure_entails_boxI, (auto intro: sep_is_pure_assn_conjI)[1]


method has_any_sep_goal = any_succeed \<open>is_sep_goal\<close>


method defer_non_sep_goal = then_else \<open>is_sep_goal\<close> \<open>fail\<close> \<open>defer_tac\<close>


method solves_non_sep_goals methods m = m;fails \<open>is_sep_goal\<close> 


lemma dupl: "X \<Longrightarrow> (X \<Longrightarrow> Y) \<Longrightarrow> Y" by simp


method thin_duplicate = 
  match premises in P[thin]: Q for Q \<Rightarrow> 
  \<open>match premises in Q \<Rightarrow> \<open>thin_tac P\<close>\<close>


method thin_all_duplicates = thin_duplicate+


method isep_extract_pure =
 changed \<open>
   rule entails_pureI,
   star \<open>erule conjE | drule pure_part_split_conj\<close>,
   thin_all_duplicates?
  \<close>


method isep_solver_keep declares isep_reduction isep_intro isep_dest =
  ((
      has_any_sep_goal,
      (
        defer_non_sep_goal+ |
        isep_normalize_conj_braces |
        entails_box_solver |
        isep_elim_ex, isep_extract_pure |  
        isep_assumption |
        changed \<open>isep_backtracking_red_rule red_rule: fri_red_rules isep_reduction\<close> |
        isep_backtracking_rule rule: isep_intro |
        isep_backtracking_drule drule: isep_dest |
        solves_non_sep_goals \<open>isep_intro_ex, isep_solver_keep\<close>
        )
      )+)[1]


method isep_solver 
  declares isep_reduction isep_intro isep_dest = 
  solves_non_sep_goals \<open>isep_solver_keep\<close>


lemma
  assumes 
    d1: "A \<turnstile> B" and d2: "B \<turnstile> C" and d3: "C \<turnstile> D" and trap1: "T \<turnstile> D" and trap2: "T \<turnstile> C" and trap3: "T \<turnstile> B"
  shows "A \<turnstile> D"
  by (isep_solver isep_intro: trap1 trap2 trap3 d1 d2 d3)


lemma 
  assumes 
    r1: "K ** L \<turnstile> X ** Z" and r2: "M ** N \<turnstile> Y ** W" and
    dr1:"A ** B \<turnstile> K ** N" and dr2:"C ** D \<turnstile> L ** M" 
  shows "A ** B ** C ** D \<turnstile> X ** Y ** Z ** W"
  apply (isep_solver_keep isep_intro: r1 r2 isep_dest: dr1 dr2)
  done 


lemma 
  assumes
    trap: "False \<Longrightarrow> A \<turnstile> B" and rule: "True \<Longrightarrow> A \<turnstile> B"
  shows "A \<turnstile> B"
  apply (isep_solver isep_intro: trap rule)
  back ..


lemma sep_pureI [isep_intro]: "B \<Longrightarrow> \<box> \<turnstile> \<up>B"
  by (simp add: pure_true_conv)


end