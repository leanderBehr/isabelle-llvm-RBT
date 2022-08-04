theory Balance
  imports 
    "../Utilities"
    Balance_Adapted
begin


context rbt_impl
begin
interpretation rbt_impl_deps .


subsection \<open>Checks\<close>


definition "check_1 lhs_p rhs_p \<equiv> is_red lhs_p &&! is_red rhs_p"
definition "check_2 lhs_p rhs_p \<equiv> is_red lhs_p &&! (do {l \<leftarrow> left lhs_p; is_red l})"
definition "check_3 lhs_p rhs_p \<equiv> is_red lhs_p &&! (do {r \<leftarrow> right lhs_p; is_red r})"
definition "check_4 lhs_p rhs_p \<equiv> is_red rhs_p &&! (do {r \<leftarrow> right rhs_p; is_red r})"
definition "check_5 lhs_p rhs_p \<equiv> is_red rhs_p &&! (do {l \<leftarrow> left rhs_p; is_red l})"


lemma check_1_correct [vcg_rules]:
  "
    llvm_htriple
    (\<upharpoonleft>rbt_assn lhs lhsi ** \<upharpoonleft>rbt_assn rhs rhsi)
    (check_1 lhsi rhsi)
    (\<lambda>r. \<upharpoonleft>rbt_assn lhs lhsi ** \<upharpoonleft>rbt_assn rhs rhsi ** \<upharpoonleft>bool.assn(rbt_check_1 lhs rhs) r)
  "
  unfolding rbt_check_1_def check_1_def sc_and_def
  apply vcg
  subgoal unfolding rbt_is_red_def by vcg
  subgoal by vcg
  done


lemma check_2_correct [vcg_rules]:
  "
    llvm_htriple
    (\<upharpoonleft>rbt_assn lhs lhsi ** \<upharpoonleft>rbt_assn rhs rhsi)
    (check_2 lhsi rhsi)
    (\<lambda>r. \<upharpoonleft>rbt_assn lhs lhsi ** \<upharpoonleft>rbt_assn rhs rhsi ** \<upharpoonleft>bool.assn (rbt_check_2 lhs rhs) r)
  "
  unfolding rbt_check_2_def check_2_def sc_and_def
  apply vcg
  subgoal
    unfolding rbt_assn_branch_def rbt_is_red_def rbt_left_def
    apply vcg_try_solve
    done 
  subgoal by vcg
  done


lemma check_3_correct [vcg_rules]:
  "
    llvm_htriple
    (\<upharpoonleft>rbt_assn lhs lhsi ** \<upharpoonleft>rbt_assn rhs rhsi)
    (check_3 lhsi rhsi)
    (\<lambda>r. \<upharpoonleft>rbt_assn lhs lhsi ** \<upharpoonleft>rbt_assn rhs rhsi ** \<upharpoonleft>bool.assn(rbt_check_3 lhs rhs) r)
  "
  unfolding rbt_check_3_def check_3_def sc_and_def
  apply vcg
  subgoal
    unfolding rbt_assn_branch_def rbt_is_red_def rbt_right_def
    apply vcg_try_solve
    done 
  subgoal by vcg
  done


lemma check_4_correct [vcg_rules]:
  "
    llvm_htriple
    (\<upharpoonleft>rbt_assn lhs lhsi ** \<upharpoonleft>rbt_assn rhs rhsi)
    (check_4 lhsi rhsi)
    (\<lambda>r. \<upharpoonleft>rbt_assn lhs lhsi ** \<upharpoonleft>rbt_assn rhs rhsi ** \<upharpoonleft>bool.assn(rbt_check_4 lhs rhs) r)
  "
  unfolding rbt_check_4_def check_4_def sc_and_def
  apply vcg
  subgoal
    unfolding rbt_assn_branch_def rbt_is_red_def rbt_right_def
    apply vcg_try_solve
    done 
  subgoal by vcg
  done


lemma check_5_correct [vcg_rules]:
  "
    llvm_htriple
    (\<upharpoonleft>rbt_assn lhs lhsi ** \<upharpoonleft>rbt_assn rhs rhsi)
    (check_5 lhsi rhsi)
    (\<lambda>r. \<upharpoonleft>rbt_assn lhs lhsi ** \<upharpoonleft>rbt_assn rhs rhsi ** \<upharpoonleft>bool.assn(rbt_check_5 lhs rhs) r)
  "
  unfolding rbt_check_5_def check_5_def sc_and_def
  apply vcg
  subgoal
    unfolding rbt_assn_branch_def rbt_is_red_def rbt_left_def
    apply vcg_try_solve
    done 
  subgoal by vcg
  done


lemmas [llvm_inline] = 
  check_1_def            
  check_2_def
  check_3_def
  check_4_def
  check_5_def


subsection \<open>Balance Cases\<close>


definition "balance_ad_case_1 lhs_p k v rhs_p \<equiv> do {
  lhs \<leftarrow> ll_load lhs_p;
  rhs \<leftarrow> ll_load rhs_p;
  case lhs of (RBT_NODE _ a w x b) \<Rightarrow>
  case rhs of (RBT_NODE _ c y z d) \<Rightarrow>
    do {
      ll_store (RBT_NODE 1 a w x b) lhs_p;
      ll_store (RBT_NODE 1 c y z d) rhs_p;
      new (RBT_NODE 0 lhs_p k v rhs_p)
    }
  }"


lemma balance_ad_case_1_correct [vcg_rules]:
  "
    llvm_htriple
    (\<upharpoonleft>rbt_assn lhs lhsi ** \<upharpoonleft>rbt_assn rhs rhsi ** \<upharpoonleft>key_assn k ki ** \<upharpoonleft>value_assn v vi ** \<up>(rbt_check_1 lhs rhs))
    (balance_ad_case_1 lhsi ki vi rhsi)
    (\<lambda>r. \<upharpoonleft>rbt_assn (rbt_balance_ad_case_1 lhs k v rhs) r)
  "
  unfolding balance_ad_case_1_def rbt_balance_ad_case_1_def new_def
  apply vcg
  apply (erule rbt_check_1_unfold)
  apply vcg
  done


definition "balance_ad_case_2 lhs_p k v rhs_p \<equiv> do {
  lhs \<leftarrow> ll_load lhs_p;
  case lhs of (RBT_NODE _ llhs_p s t c) \<Rightarrow>
  do {
    llhs \<leftarrow> ll_load llhs_p;
    case llhs of (RBT_NODE _ a w x b) \<Rightarrow>
    let y = k; z = v; d = rhs_p in
    do {
      ll_free lhs_p;
      ll_free llhs_p;
      lhs_n \<leftarrow> new (RBT_NODE 1 a w x b);
      rhs_n \<leftarrow> new (RBT_NODE 1 c y z d);
      new (RBT_NODE 0 lhs_n s t rhs_n)
    }
  }
}"


lemma balance_ad_case_2_correct [vcg_rules]: 
  "
    llvm_htriple
    (\<upharpoonleft>rbt_assn lhs lhsi ** \<upharpoonleft>rbt_assn rhs rhsi ** \<upharpoonleft>key_assn k ki ** \<upharpoonleft>value_assn v vi ** \<up>(rbt_check_2 lhs rhs))
    (balance_ad_case_2 lhsi ki vi rhsi)
    (\<lambda>r. \<upharpoonleft>rbt_assn (rbt_balance_ad_case_2 lhs k v rhs) r)
  "
  unfolding balance_ad_case_2_def rbt_balance_ad_case_2_def new_def
  apply vcg
  apply (erule rbt_check_2_unfold)
  apply vcg
  done


definition "balance_ad_case_3 lhs_p k v rhs_p \<equiv> do {
  lhs \<leftarrow> ll_load lhs_p;
  case lhs of (RBT_NODE _ a w x rlhs_p) \<Rightarrow>
  do {
    rlhs \<leftarrow> ll_load rlhs_p;
    case rlhs of (RBT_NODE _ b s t c) \<Rightarrow>
    let y = k; z = v; d = rhs_p in
    do {
      ll_free lhs_p;
      ll_free rlhs_p;
      lhs_n \<leftarrow> new (RBT_NODE 1 a w x b);
      rhs_n \<leftarrow> new (RBT_NODE 1 c y z d);
      new (RBT_NODE 0 lhs_n s t rhs_n)
    }
  }
}"


lemma balance_ad_case_3_correct [vcg_rules]: 
  "
    llvm_htriple
    (\<upharpoonleft>rbt_assn lhs lhsi ** \<upharpoonleft>rbt_assn rhs rhsi ** \<upharpoonleft>key_assn k ki ** \<upharpoonleft>value_assn v vi ** \<up>(rbt_check_3 lhs rhs))
    (balance_ad_case_3 lhsi ki vi rhsi)
    (\<lambda>r. \<upharpoonleft>rbt_assn (rbt_balance_ad_case_3 lhs k v rhs) r)
  "
  unfolding balance_ad_case_3_def rbt_balance_ad_case_3_def new_def
  apply vcg
  apply (erule rbt_check_3_unfold)
  apply vcg
  done


definition "balance_ad_case_4 l_p k v r_p \<equiv> do {
  let a=l_p; w=k; x=v in
  do {    
    r \<leftarrow> ll_load r_p;
    case r of (RBT_NODE _ b s t rr_p) \<Rightarrow> 
    do {
      rr \<leftarrow> ll_load rr_p;
      case rr of (RBT_NODE _ c y z d) \<Rightarrow> 
      do {
        ll_free r_p;
        ll_free rr_p;
        lhs_n \<leftarrow> new (RBT_NODE 1 a w x b);
        rhs_n \<leftarrow> new (RBT_NODE 1 c y z d);
        new (RBT_NODE 0 lhs_n s t rhs_n)
      }
    }
  }
}"


lemma balance_ad_case_4_correct [vcg_rules]: 
  "
    llvm_htriple
    (\<upharpoonleft>rbt_assn lhs lhsi ** \<upharpoonleft>rbt_assn rhs rhsi ** \<upharpoonleft>key_assn k ki ** \<upharpoonleft>value_assn v vi ** \<up>(rbt_check_4 lhs rhs))
    (balance_ad_case_4 lhsi ki vi rhsi)
    (\<lambda>r. \<upharpoonleft>rbt_assn (rbt_balance_ad_case_4 lhs k v rhs) r)
  "
  unfolding balance_ad_case_4_def rbt_balance_ad_case_4_def new_def
  apply vcg
  apply (erule rbt_check_4_unfold)
  apply vcg
  done


definition "balance_ad_case_5 l_p k v r_p \<equiv> do {
  let a=l_p; w=k; x=v in
  do {    
    r \<leftarrow> ll_load r_p;
    case r of (RBT_NODE _ rl_p y z d) \<Rightarrow> 
    do {
      rl \<leftarrow> ll_load rl_p;
      case rl of (RBT_NODE _ b s t c) \<Rightarrow> 
      do {
        ll_free r_p;
        ll_free rl_p;
        lhs_n \<leftarrow> new (RBT_NODE 1 a w x b);
        rhs_n \<leftarrow> new (RBT_NODE 1 c y z d);
        new (RBT_NODE 0 lhs_n s t rhs_n)
      }
    }
  }
}"


lemma balance_ad_case_5_correct [vcg_rules]: 
  "
    llvm_htriple
    (\<upharpoonleft>rbt_assn lhs lhsi ** \<upharpoonleft>rbt_assn rhs rhsi ** \<upharpoonleft>key_assn k ki ** \<upharpoonleft>value_assn v vi ** \<up>(rbt_check_5 lhs rhs))
    (balance_ad_case_5 lhsi ki vi rhsi)
    (\<lambda>r. \<upharpoonleft>rbt_assn (rbt_balance_ad_case_5 lhs k v rhs) r)
  "
  unfolding balance_ad_case_5_def rbt_balance_ad_case_5_def new_def
  apply vcg
  apply (erule rbt_check_5_unfold)
  apply vcg
  done

                                             
definition "balance_ad_case_6 l_p k v r_p \<equiv> new (RBT_NODE 1 l_p k v r_p)"


lemma balance_ad_case_6_correct [vcg_rules]: 
  "
    llvm_htriple
    (\<upharpoonleft>rbt_assn lhs lhsi ** \<upharpoonleft>rbt_assn rhs rhsi ** \<upharpoonleft>key_assn k ki ** \<upharpoonleft>value_assn v vi)
    (balance_ad_case_6 lhsi ki vi rhsi)
    (\<lambda>r. \<upharpoonleft>rbt_assn (rbt_balance_ad_case_6 lhs k v rhs) r)
  "
  unfolding balance_ad_case_6_def rbt_balance_ad_case_6_def
  by vcg


lemmas [llvm_code] = 
  balance_ad_case_1_def
  balance_ad_case_2_def
  balance_ad_case_3_def
  balance_ad_case_4_def
  balance_ad_case_5_def
  balance_ad_case_6_def


subsection \<open>Balance Function\<close>


definition balance ::
  "('ki, 'vi) rbti \<Rightarrow> 'ki \<Rightarrow> 'vi \<Rightarrow> ('ki, 'vi) rbti \<Rightarrow> ('ki, 'vi) rbti llM" where
  "balance lhs_p k v rhs_p = do {
      if! check_1 lhs_p rhs_p
      then! balance_ad_case_1 lhs_p k v rhs_p
      else! if! check_2 lhs_p rhs_p
      then! balance_ad_case_2 lhs_p k v rhs_p
      else! if! check_3 lhs_p rhs_p
      then! balance_ad_case_3 lhs_p k v rhs_p
      else! if! check_4 lhs_p rhs_p
      then! balance_ad_case_4 lhs_p k v rhs_p
      else! if! check_5 lhs_p rhs_p
      then! balance_ad_case_5 lhs_p k v rhs_p
      else! balance_ad_case_6 lhs_p k v rhs_p
  }"


lemmas [llvm_code] = balance_def


lemma balance_correct':
  "llvm_htriple
  (
    \<upharpoonleft>rbt_assn tree_l tree_li **
    \<upharpoonleft>rbt_assn tree_r tree_ri **   
    \<upharpoonleft>key_assn k ki **
    \<upharpoonleft>value_assn v vi
  )
  (balance tree_li ki vi tree_ri)
  (\<lambda>ri. \<upharpoonleft>rbt_assn (rbt_balance_ad tree_l k v tree_r) ri) 
  "
proof -
  show ?thesis
    unfolding balance_def
    by vcg
qed


lemma balance_correct [vcg_rules]:
  "llvm_htriple
  (
    \<upharpoonleft>rbt_assn tree_l tree_li **
    \<upharpoonleft>rbt_assn tree_r tree_ri **   
    \<upharpoonleft>key_assn k ki **
    \<upharpoonleft>value_assn v vi
  )
  (balance tree_li ki vi tree_ri)
  (\<lambda>ri. \<upharpoonleft>rbt_assn (rbt_balance tree_l k v tree_r) ri) 
  "
  by (metis balance_correct' rbt_balance_ad_correct)


end


end