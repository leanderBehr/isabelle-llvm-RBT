theory List_Copy
  imports
    Arl_Ext
    "../Separation_Logic_Solver/Methods"
begin


locale arl_copy =
  fixes
    ai_type :: "'ai :: llvm_rep itself" and
    el_assn :: "('a, 'ai) dr_assn" and
    el_copy :: "'ai \<Rightarrow> 'ai llM"
  assumes
    el_copy_rule [vcg_rules]:
    "llvm_htriple (\<upharpoonleft>el_assn a ai) (el_copy ai) (\<lambda>copied. \<upharpoonleft>el_assn a ai ** \<upharpoonleft>el_assn a copied)"
begin


unbundle monad_syntax_M


partial_function (M) arl_copy' ::
  "('ai, 'l::len2) array_list \<Rightarrow> ('ai, 'l) array_list \<Rightarrow> 'l word \<Rightarrow> unit llM" where
  "arl_copy' xs ys i =
  do {
    len \<leftarrow> arl_len xs;
    le \<leftarrow> ll_icmp_ult i len;
    if le = 1
    then do {
      el \<leftarrow> arl_nth xs i;
      copied \<leftarrow> el_copy el;
      arl_upd ys i copied;
      ip1 \<leftarrow> ll_add i 1;
      arl_copy' xs ys ip1
    }
    else return ()
  }"



lemma STATE_pure_partI:
  "STATE asf P s \<Longrightarrow> pure_part P"
  unfolding STATE_def pure_part_def by blast


lemma STATE_pure_partE:
  "\<lbrakk>STATE asf P s; pure_part P \<Longrightarrow> T\<rbrakk> \<Longrightarrow> T"
  using STATE_pure_partI by blast


lemma arl_copy'_rule:
  "
  llvm_htriple
  (
    \<upharpoonleft>snat.assn i ii **
    arl_elem_assn el_assn xs xsi **
    \<upharpoonleft>(list_assn el_assn Map.empty) (take i xs) (take i ys') **
    \<upharpoonleft>arl_assn ys' ysi **
    \<up>(length ys' = length xs)
  )
  (arl_copy' xsi ysi ii)
  (\<lambda>_.
    arl_elem_assn el_assn xs xsi ** arl_elem_assn el_assn xs ysi)
"
  unfolding arl_elem_assn_def'
proof(induction "length xs - i" arbitrary: i ii ys')
  case 0
  hence "i \<ge> length xs" by simp
  then show ?case
    apply (subst arl_copy'.simps)
    unfolding arl_elem_assn_def'
    apply vcg
    subgoal (*contradiction*)
      apply (erule STATE_pure_partE)
      apply (star \<open>erule conjE | drule pure_part_split_conj\<close>)
      using list_assn_pure_partD by fastforce

    subgoal by vcg
    done
next
  case (Suc x)
  note Suc(1)[vcg_rules]
  show ?case
    apply (subst arl_copy'.simps)
    unfolding arl_elem_assn_def'
    apply vcg
    subgoal for asf r sa
      apply vcg_rl
       apply vcg_compat
      using Suc(2) apply - apply (sepwith simp)
      apply vcg_solve
      apply vcg
      apply vcg_rl
        apply vcg_compat
        apply (isep_rule rule: pure_pure_asm_prefixI, simp)
        apply sep 
         apply (simp add: list_update_append take_update_last take_Suc_conv_app_nth)
        apply sepE
         apply simp

        apply (isep_drule drule: list_assn_push_back)
        apply (drule list_assn_pure_partD)+
        apply (simp add: list_update_append take_update_last take_Suc_conv_app_nth)
        apply sep
       apply auto
      apply vcg_solve+
 done
    subgoal
      apply vcg
      apply vcg_compat
      apply sepE
      apply (auto dest!: list_assn_pure_partD)
      done
    done
qed


definition arl_copy ::
  "('ai, 'l::len2) array_list \<Rightarrow> ('ai, 'l) array_list llM" where
  "arl_copy xs =
  do {
    len \<leftarrow> arl_len xs;
    ys \<leftarrow> arl_new_sz TYPE('ai) len;
    arl_copy' xs ys 0;
    return ys
  }"


lemmas arl_copy'.simps[llvm_code]
lemmas arl_copy_def[llvm_code]


lemma snat_assn_z_z:  
  "\<box> \<turnstile>\<upharpoonleft>snat.assn 0 0"
  by (simp add: prepare_pure_assn snat.assn_pure snat_z_z_init)


lemma arl_copy_rule [vcg_rules]:
  "
  llvm_htriple
  (arl_elem_assn el_assn xs (xsi::('ai, 'l::len2) array_list) ** \<up>(LENGTH('l) > 4))
  (arl_copy xsi)
  (\<lambda>arl_copy. arl_elem_assn el_assn xs xsi ** arl_elem_assn el_assn xs arl_copy)
"
  supply arl_copy'_rule[vcg_rules]
  apply (subst arl_copy_def)
  apply vcg
  apply vcg_rl
   apply vcg_compat
   apply isep_extract_pure
   apply (sepE isep_intro: snat_assn_z_z)
    apply (auto dest: list_assn_pure_partD)[]
   apply simp
   apply (sepE isep_intro: list_assn_empty)
  apply vcg_solve
  apply vcg
  done


end


end