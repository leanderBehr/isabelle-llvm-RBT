theory Balance_Opt
  imports "../Balance"
begin

context rbt_impl
begin
interpretation rbt_impl_deps .

definition "rotate_left n_p \<equiv>
  do {
    r_p \<leftarrow> right n_p;
    rl_p \<leftarrow> left r_p;
    set_left_p n_p r_p;
    set_right_p rl_p n_p;
    return r_p
  }
"

definition "rotate_right n_p \<equiv>
  do {
    l_p \<leftarrow> left n_p;
    lr_p \<leftarrow> right l_p;
    set_right_p n_p l_p;
    set_left_p lr_p n_p;
    return l_p
  }
"

definition "balance_opt_case_1 n_p \<equiv> 
  do {
    n \<leftarrow> ll_load n_p;
    set_color_p 0 n_p;
    set_color_p 1 (rbt_node.left n);
    set_color_p 1 (rbt_node.right n);
    return n_p
  }"
                            
definition "balance_opt_case_2 n_p \<equiv> 
  do {
    n2_p \<leftarrow> rotate_right n_p;
    l_p \<leftarrow> left n2_p;
    set_color_p 1 l_p;
    return n2_p
  }"

definition "balance_opt_case_3 n_p \<equiv> 
  do {
    l_p \<leftarrow> left n_p;
    l2_p \<leftarrow> rotate_left l_p;
    set_left_p l2_p n_p;
    n2_p \<leftarrow> rotate_right n_p;
    set_color_p 1 l_p;
    return n2_p
  }"

definition "balance_opt_case_4 n_p \<equiv> 
  do {
    n2_p \<leftarrow> rotate_left n_p;
    r_p \<leftarrow> right n2_p;
    set_color_p 1 r_p;
    return n2_p
  }"

definition "balance_opt_case_5 n_p \<equiv> 
  do {
    r_p \<leftarrow> right n_p;
    r2_p \<leftarrow> rotate_right r_p;
    set_right_p r2_p n_p;
    n2_p \<leftarrow> rotate_left n_p;
    set_color_p 1 r_p;
    return n2_p
  }"

definition "balance_opt n_p \<equiv>
  do {
    if! ll_matches_rbt
        (RP_Branch CP_Var 
          (RP_Branch CP_R RP_Var RP_Var)
          (RP_Branch CP_R RP_Var RP_Var)
        ) n_p
    then! balance_opt_case_1 n_p
    else!
    do {
      n \<leftarrow> ll_load n_p;
      l_p \<leftarrow> return rbt_node.left n;
      r_p \<leftarrow> return rbt_node.right n;
      if! ll_matches_rbt
        (RP_Branch CP_R (RP_Branch CP_R RP_Var RP_Var) RP_Var) l_p
      then! balance_opt_case_2 n_p
      else! if! ll_matches_rbt 
        (RP_Branch CP_R RP_Var (RP_Branch CP_R RP_Var RP_Var)) l_p
      then! balance_opt_case_3 n_p
      else! if! ll_matches_rbt 
        (RP_Branch CP_R RP_Var (RP_Branch CP_R RP_Var RP_Var)) r_p
      then! balance_opt_case_4 n_p
      else! if! ll_matches_rbt 
        (RP_Branch CP_R (RP_Branch CP_R RP_Var RP_Var) RP_Var) r_p
      then! balance_opt_case_5 n_p
      else! return n_p
    }
  }
"

lemmas [llvm_inline] =
    balance_opt_case_1_def
    balance_opt_case_2_def
    balance_opt_case_3_def
    balance_opt_case_4_def
    balance_opt_case_5_def
    rotate_left_def    
    rotate_right_def

lemmas [llvm_code] = balance_opt_def


lemma balance_opt_correct [vcg_rules]:
  "llvm_htriple
  (
    \<upharpoonleft>ll_bpto (RBT_NODE ci li ki vi ri) n_p **
    rbt_assn l li **
    rbt_assn r ri **   
    \<upharpoonleft>key_assn k ki **
    \<upharpoonleft>value_assn v vi **
    color_assn color.B ci
  )
  (balance_opt n_p)
  (\<lambda>res. rbt_assn (rbt_balance l k v r) res) 
  "
  unfolding 
    balance_opt_def
    balance_opt_case_1_def
    balance_opt_case_2_def
    balance_opt_case_3_def
    balance_opt_case_4_def
    balance_opt_case_5_def
    rotate_left_def    
    rotate_right_def

  apply vcg
  subgoal (*Case 1*)
    apply (cases "(l, k, v, r)" rule: RBT_Impl.balance.cases)
                        apply auto
    apply vcg
    done
  subgoal (*Case 2+*)
    apply vcg
    subgoal (*Case 3*)
      apply (cases "(l, k, v, r)" rule: RBT_Impl.balance.cases)
                          apply auto
       apply vcg
      done
    subgoal (*Case 4+*)
      apply vcg
      subgoal (*Case 4*)
        apply (cases "(l, k, v, r)" rule: RBT_Impl.balance.cases)
                            apply auto
           apply vcg
        done
      subgoal (*Case 5+*)
        apply vcg
        subgoal (*Case 5*)
          apply (cases "(l, k, v, r)" rule: RBT_Impl.balance.cases)
                              apply auto
           apply vcg
          done
        subgoal (*Case 6*)
          apply (cases "(l, k, v, r)" rule: RBT_Impl.balance.cases)
                              apply auto
                              apply vcg
          done
        done
      done
    done
  done

end


end