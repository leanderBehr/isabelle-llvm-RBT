theory Balance
  imports 
    "../Delete"
    Balance_Adapted
begin


context rbt_impl
begin
interpretation llvm_prim_ctrl_setup .
interpretation llvm_prim_arith_setup .
interpretation llvm_prim_setup .


subsection \<open>Utilities\<close>


subsubsection \<open>Functions\<close>


definition "is_red node_p \<equiv> do {
    if node_p = null
    then return 0
    else do {
      node \<leftarrow> ll_load node_p;
      return from_bool (rbt_node.color node = 0)
    }
  }"


lemma is_red_correct [vcg_rules]:
  "
    llvm_htriple
    (\<upharpoonleft>rbt_assn t ti)
    (is_red ti)
    (\<lambda>r. \<up>(r = fb (rbt_is_red t)) ** \<upharpoonleft>rbt_assn t ti) 
  "
proof(cases t)
  case Empty
  then show ?thesis 
    unfolding is_red_def rbt_is_red_def
    by vcg
next
  case (Branch col lhs k v rhs)
  then show ?thesis
    apply (simp add: rbt_assn_branch_def rbt_is_red_def is_red_def)
    apply (cases col)
    apply vcg
    done
qed


definition "left node_p \<equiv> do {
    node \<leftarrow> ll_load node_p;
    return rbt_node.left node
}"


lemma left_correct [vcg_rules]:
  "
    llvm_htriple
    (\<upharpoonleft>rbt_assn (Branch col lhs k v rhs) ni)
    (left ni)
    (\<lambda>lhsi.
      EXS coli ki vi rhsi. 
        \<upharpoonleft>ll_bpto (RBT_NODE coli lhsi ki vi rhsi) ni **
        \<upharpoonleft>color_assn col coli **
        \<upharpoonleft>rbt_assn lhs lhsi **
        \<upharpoonleft>key_assn k ki **
        \<up>(vi=v) **  
        \<upharpoonleft>rbt_assn rhs rhsi
    )
  "
  unfolding left_def
  by vcg


definition "right node_p \<equiv> do {
    node \<leftarrow> ll_load node_p;
    return rbt_node.right node
}"


lemma right_correct [vcg_rules]:
  "
    llvm_htriple
    (\<upharpoonleft>rbt_assn (Branch col lhs k v rhs) ni)
    (right ni)
    (\<lambda>rhsi.
      EXS coli lhsi ki vi. 
        \<upharpoonleft>ll_bpto (RBT_NODE coli lhsi ki vi rhsi) ni **
        \<upharpoonleft>color_assn col coli **
        \<upharpoonleft>rbt_assn lhs lhsi **
        \<upharpoonleft>key_assn k ki **
        \<up>(vi=v) **  
        \<upharpoonleft>rbt_assn rhs rhsi
    )
  "
  unfolding right_def
  by vcg


definition "new x \<equiv> do {
    ptr \<leftarrow> ll_balloc;
    ll_store x ptr;
    return ptr
  }"


lemma new_correct [vcg_rules]:
  "
    llvm_htriple
    \<box>
    (new x)
    (\<lambda>r. \<upharpoonleft>ll_bpto x r)
  "
  unfolding new_def
  by vcg


lemmas [llvm_inline] = 
  is_red_def
  left_def
  right_def
  new_def


subsubsection \<open>Macros\<close>


definition If_ll :: 
  "1 word llM \<Rightarrow> 'a llM \<Rightarrow> 'a llM \<Rightarrow> 'a llM" 
  ("(if! (_)/ then! (_)/ else! (_))" [0, 0, 10] 10) where
  "If_ll condf truef elsef = do {
    cond \<leftarrow> condf;
    if cond = 1
    then truef
    else elsef
  }"


definition sc_and (infixl "&&!" 64) where
  "sc_and a b \<equiv> do {
    if! a
    then! b
    else! return 0
  }"


lemmas [simp, llvm_pre_simp] = If_ll_def sc_and_def


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
    (\<lambda>r. \<upharpoonleft>rbt_assn lhs lhsi ** \<upharpoonleft>rbt_assn rhs rhsi ** \<up>(r = fb (rbt_check_1 lhs rhs)))
  "
  unfolding rbt_check_1_def check_1_def sc_and_def
  by vcg


lemma check_2_correct [vcg_rules]:
  "
    llvm_htriple
    (\<upharpoonleft>rbt_assn lhs lhsi ** \<upharpoonleft>rbt_assn rhs rhsi)
    (check_2 lhsi rhsi)
    (\<lambda>r. \<upharpoonleft>rbt_assn lhs lhsi ** \<upharpoonleft>rbt_assn rhs rhsi ** \<up>(r = fb (rbt_check_2 lhs rhs)))
  "
  unfolding rbt_check_2_def check_2_def sc_and_def
  apply vcg
  apply (erule rbt_is_red_unfold_branch)
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
    (\<lambda>r. \<upharpoonleft>rbt_assn lhs lhsi ** \<upharpoonleft>rbt_assn rhs rhsi ** \<up>(r = fb (rbt_check_3 lhs rhs)))
  "
  unfolding rbt_check_3_def check_3_def sc_and_def
  apply vcg
  apply (erule rbt_is_red_unfold_branch)
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
    (\<lambda>r. \<upharpoonleft>rbt_assn lhs lhsi ** \<upharpoonleft>rbt_assn rhs rhsi ** \<up>(r = fb (rbt_check_4 lhs rhs)))
  "
  unfolding rbt_check_4_def check_4_def sc_and_def
  apply vcg
  apply (erule rbt_is_red_unfold_branch)
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
    (\<lambda>r. \<upharpoonleft>rbt_assn lhs lhsi ** \<upharpoonleft>rbt_assn rhs rhsi ** \<up>(r = fb (rbt_check_5 lhs rhs)))
  "
  unfolding rbt_check_5_def check_5_def sc_and_def
  apply vcg
  apply (erule rbt_is_red_unfold_branch)
  apply vcg
  subgoal
    unfolding rbt_assn_branch_def rbt_is_red_def rbt_left_def
    apply vcg_try_solve
    done 
  subgoal by vcg
  done


lemmas [llvm_code] = 
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
    (\<upharpoonleft>rbt_assn lhs lhsi ** \<upharpoonleft>rbt_assn rhs rhsi ** \<upharpoonleft>key_assn k ki ** \<up>(rbt_check_1 lhs rhs))
    (balance_ad_case_1 lhsi ki v rhsi)
    (\<lambda>r. \<upharpoonleft>rbt_assn (rbt_balance_ad_case_1 lhs k v rhs) r)
  "
  unfolding balance_ad_case_1_def rbt_balance_ad_case_1_def new_def
  apply vcg
  apply (erule rbt_check_1_unfold)
  apply vcg
  apply auto
  unfolding rbt_assn_branch_def
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
    (\<upharpoonleft>rbt_assn lhs lhsi ** \<upharpoonleft>rbt_assn rhs rhsi ** \<upharpoonleft>key_assn k ki ** \<up>(rbt_check_2 lhs rhs))
    (balance_ad_case_2 lhsi ki v rhsi)
    (\<lambda>r. \<upharpoonleft>rbt_assn (rbt_balance_ad_case_2 lhs k v rhs) r)
  "
  unfolding balance_ad_case_2_def rbt_balance_ad_case_2_def new_def
  apply vcg
  apply (erule rbt_check_2_unfold)
  apply vcg
  apply auto
  unfolding rbt_assn_branch_def
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
    (\<upharpoonleft>rbt_assn lhs lhsi ** \<upharpoonleft>rbt_assn rhs rhsi ** \<upharpoonleft>key_assn k ki ** \<up>(rbt_check_3 lhs rhs))
    (balance_ad_case_3 lhsi ki v rhsi)
    (\<lambda>r. \<upharpoonleft>rbt_assn (rbt_balance_ad_case_3 lhs k v rhs) r)
  "
  unfolding balance_ad_case_3_def rbt_balance_ad_case_3_def new_def
  apply vcg
  apply (erule rbt_check_3_unfold)
  apply vcg
  apply auto
  unfolding rbt_assn_branch_def
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
    (\<upharpoonleft>rbt_assn lhs lhsi ** \<upharpoonleft>rbt_assn rhs rhsi ** \<upharpoonleft>key_assn k ki ** \<up>(rbt_check_4 lhs rhs))
    (balance_ad_case_4 lhsi ki v rhsi)
    (\<lambda>r. \<upharpoonleft>rbt_assn (rbt_balance_ad_case_4 lhs k v rhs) r)
  "
  unfolding balance_ad_case_4_def rbt_balance_ad_case_4_def new_def
  apply vcg
  apply (erule rbt_check_4_unfold)
  apply vcg
  apply auto
  unfolding rbt_assn_branch_def
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
    (\<upharpoonleft>rbt_assn lhs lhsi ** \<upharpoonleft>rbt_assn rhs rhsi ** \<upharpoonleft>key_assn k ki ** \<up>(rbt_check_5 lhs rhs))
    (balance_ad_case_5 lhsi ki v rhsi)
    (\<lambda>r. \<upharpoonleft>rbt_assn (rbt_balance_ad_case_5 lhs k v rhs) r)
  "
  unfolding balance_ad_case_5_def rbt_balance_ad_case_5_def new_def
  apply vcg
  apply (erule rbt_check_5_unfold)
  apply vcg
  apply auto
  unfolding rbt_assn_branch_def
  apply vcg
  done

                                             
definition "balance_ad_case_6 l_p k v r_p \<equiv> new (RBT_NODE 1 l_p k v r_p)"


lemma balance_ad_case_6_correct [vcg_rules]: 
  "
    llvm_htriple
    (\<upharpoonleft>rbt_assn lhs lhsi ** \<upharpoonleft>rbt_assn rhs rhsi ** \<upharpoonleft>key_assn k ki)
    (balance_ad_case_6 lhsi ki v rhsi)
    (\<lambda>r. \<upharpoonleft>rbt_assn (rbt_balance_ad_case_6 lhs k v rhs) r)
  "
  unfolding balance_ad_case_6_def rbt_balance_ad_case_6_def
  apply vcg
  unfolding rbt_assn_branch_def
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
  "('ki, 'v::llvm_rep) rbti \<Rightarrow> 'ki \<Rightarrow> 'v \<Rightarrow> ('ki, 'v) rbti \<Rightarrow> ('ki, 'v) rbti llM" where
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
    \<upharpoonleft>key_assn k ki
  )
  (balance tree_li ki v tree_ri)
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
    \<upharpoonleft>key_assn k ki
  )
  (balance tree_li ki v tree_ri)
  (\<lambda>ri. \<upharpoonleft>rbt_assn (rbt_balance tree_l k v tree_r) ri) 
  "
  by (metis balance_correct' rbt_balance_ad_correct)



subsection \<open>WIP GARBAGE\<close>


lemma pure_part_split_conjE:
  fixes A B
  assumes "pure_part (A ** B)"
  obtains
    "pure_part A"
    "pure_part B"
  using assms
  by (blast dest: pure_part_split_conj)

lemma rbt_assn_non_null_def:
  assumes 
    "pure_part (\<upharpoonleft>rbt_assn tree_l tree_li)"
  shows
    "tree_li = null \<longleftrightarrow> (tree_l = rbt.Empty)"
  using assms
  apply (cases tree_l)
  subgoal by simp
  subgoal
    unfolding rbt_assn_branch_def
    by fastforce
  done

lemma fri_exE: "(\<And>x. FRAME_INFER (P x) Qs F) \<Longrightarrow> FRAME_INFER (EXS x. P x) Qs F"
  by (auto simp: FRAME_INFER_def entails_def)


end


end