theory LLVM_DS_RBT
  imports
  "LLVM_DS_RBT/Free"
  "LLVM_DS_RBT/Insert/Insert"
  "LLVM_DS_RBT/Insert/Naive_Insert"
  "LLVM_DS_RBT/Lookup/Lookup"
 
  "LLVM_DS_RBT/Example/Export"
  "LLVM_DS_RBT/Bench_Export"
begin

abbreviation htripleN ("\<Turnstile> {_}/ _/ {_}") where
  "htripleN P c Q \<equiv> htriple P c Q" 

lemma
  wpa_mono:
  "(\<And>r s. P r s \<Longrightarrow> Q r s) \<Longrightarrow> wpa asf c P s \<Longrightarrow> wpa asf c Q s"
  by (simp add: wp_monoI wpa_def)


context rbt_impl
begin
interpretation rbt_impl_deps .

lemma compose_htriple1:
  assumes
    "\<Turnstile> {P1} c1 {\<lambda>r. P2 r}" and
    "\<And>r. \<Turnstile> {P2 r} (c2 r) {\<lambda>r. P3 r}"
  shows
    "\<Turnstile> {P1} (do {x \<leftarrow>c1;c2 x}) {\<lambda>r. P3 r}"
  using assms unfolding htriple_def Mbind_def
  by (smt (verit, best) Mbind_def wpa_bindI wpa_mono)

find_theorems name: wpa_mono

lemma compose_htriple2:
  assumes
    "\<Turnstile> {P1'} c1 {\<lambda>r. P2 r}" and
    "P1 \<tturnstile> P1' -- F" and
    "\<And>r. \<Turnstile> {P2 r ** F} (c2 r) {P3}"
  shows
    "\<Turnstile> {P1} (do{x\<leftarrow>c1;c2 x}) {\<lambda>r. P3 r}"
proof -
  from assms(1-2) have "\<Turnstile> {P1} c1 {\<lambda>r. P2 r ** F}"
    unfolding frame_def apply simp
    using frame_rule htriple_ent_pre by blast

  
  thus "\<Turnstile> {P1} (do{x\<leftarrow>c1;c2 x}) {\<lambda>r. P3 r}"
    using assms(3) compose_htriple1 by blast
qed

lemma compose_htriple3:
  assumes
    "\<Turnstile> {P'} c {Q'} " and
    "P \<tturnstile> P' -- F" and
    "\<And>r. (Q' r) ** F \<turnstile> Q r"
  shows "\<Turnstile> {P} c {Q}"
  using assms unfolding frame_def apply simp
  by (metis (mono_tags) frame_rule htriple_ent_post htriple_ent_pre)

interpretation v_option: option_impl value_assn .


lemma return_rule:
  "\<Turnstile> {P} return x {\<lambda>r. P ** \<up>(r = x)}"
  by (simp add: htripleI pure_true_conv wpa_return)


lemma if_rule:
  assumes 
    "b \<Longrightarrow> \<Turnstile> {P} c1 {Q}" and
    "\<not>b \<Longrightarrow> \<Turnstile> {P} c2 {Q}"
  shows
    "\<Turnstile> {P} (if b then c1 else c2) {Q}"
  using assms by simp

lemma
  htriple_exE:
  "(\<And>x. \<Turnstile> {P x} c {Q}) \<Longrightarrow>  \<Turnstile> {EXS x. P x} c {Q}"
  unfolding htriple_def STATE_def
  by blast

lemma "\<Turnstile> {EXS x. P x} c {Q} \<Longrightarrow> \<Turnstile> {\<lambda>s. \<exists>x. P x s} c {Q}"
  
  unfolding htriple_def STATE_def
  by blast

find_theorems pred_ex sep_conj



method isep_extract_pure_ht =
  changed \<open>
    (rule htriple_pure_preI),
    star \<open>erule conjE | drule pure_part_split_conj\<close>,
    thin_duplicates?
  \<close>


lemma lookup_correct [vcg_rules]:
  assumes
    copy_rule [vcg_rules]:
    "\<And>v vi.
      llvm_htriple
      (\<upharpoonleft>value_assn v vi)
      (value_copy vi)
      (\<lambda>r. \<upharpoonleft>value_assn v vi ** \<upharpoonleft>value_assn v r)
    "   
  shows
    "
      llvm_htriple
      (rbt_assn t ti ** \<upharpoonleft>key_assn kn ki)
      (lookup value_copy ti ki)
      (\<lambda>opt.
        \<upharpoonleft>value_option_assn (rbt_lookup t kn) opt **
        rbt_assn t ti **
        \<upharpoonleft>key_assn kn ki)
    " oops
(*
proof(induction t arbitrary: ti)
  case Empty
  then show ?case
    unfolding value_option_assn_def
    apply (subst lookup.simps)
    apply (rule if_rule)
    subgoal
      using return_rule apply (rule compose_htriple3)
       apply simp
       apply isep_assumption+
      apply (isep_solver_keep, simp)
      done
    subgoal by simp
    done
next
  case (Branch c l k v r)

  note [vcg_rules] = Branch.IH

  show ?case
    apply (subst lookup.simps)
    apply (rule if_rule)
    subgoal 
      using return_rule apply (rule compose_htriple3)
       apply isep_assumption+
      by auto
    subgoal
      using load_rbt apply (rule compose_htriple2)
       apply isep_solver
      apply (simp (no_asm) only: sep_conj_exists)
      apply (rule htriple_exE)+
      apply isep_extract_pure_ht
      using return_rule apply (rule compose_htriple2)
       apply isep_solver_keep
      using lt_impl_rule apply (rule compose_htriple2)
      apply ((isep_solver_keep | simp)+)[1]

      apply (rule if_rule)
      subgoal
        using Branch(1) apply (rule compose_htriple3)
         apply ((isep_solver_keep | simp)+)[1]
        apply isep_solver_keep
        sorry
      subgoal sorry
      done
    done
qed
*)
end


end