theory Balance_Opt_LR
  imports
    "../Balance_LR"
    "../../Insert/Alloc_Optimized/Insert_Opt"
begin


context rbt_impl
begin
interpretation rbt_impl_deps .


definition "bl_opt_case_1 n_p \<equiv>
  do {
    l_p \<leftarrow> left n_p;
    set_color_p 0 n_p;
    set_color_p 1 l_p;
    return n_p
  }
"


definition "bl_opt_case_2 n_p \<equiv>
  do {
    r_p \<leftarrow> right n_p;
    set_color_p 0 r_p;
    set_color_p 1 n_p;
    balance_opt n_p
  }
"


definition "bl_opt_case_3 n_p \<equiv>
  do {
    r_p \<leftarrow> right n_p;

    r_p \<leftarrow> rotate_right r_p;
    set_right_p r_p n_p;

    n2_p \<leftarrow> rotate_left n_p;
    
    r_p \<leftarrow> right n2_p;
    rr_p \<leftarrow> right r_p;
    (if rr_p = null then return () else set_color_p 0 rr_p);

    set_color_p 1 r_p;
    r_p \<leftarrow> balance_opt r_p;
    set_right_p r_p n2_p;

    set_color_p 1 n_p;
    set_color_p 0 n2_p;
    return n2_p
  }
"

definition [llvm_inline]: "TFail \<equiv> fail" (*avoids VCG assuming fail can't be reached*)



definition "balance_left_opt n_p \<equiv> 
  do {
    n \<leftarrow> ll_load n_p;
    case n of (RBT_NODE _ l_p k v r_p) \<Rightarrow>
    if! ll_matches_rbt bl_pat_1 l_p
    then! bl_opt_case_1 n_p
    else! if! ll_matches_rbt bl_pat_2 r_p
    then! bl_opt_case_2 n_p
    else! if! ll_matches_rbt bl_pat_3 r_p
    then! bl_opt_case_3 n_p
    else! do { 
      free n_p;
      empty
    }
  }"


lemma balance_left_opt_correct [vcg_rules]:
  "
    llvm_htriple
    (
      rbt_assn l li **
      \<upharpoonleft>key_assn k ki **
      \<upharpoonleft>value_assn v vi **
      rbt_assn r ri **
      color_assn c ci **
      \<upharpoonleft>ll_bpto (RBT_NODE ci li ki vi ri) n_p **

      \<up>(matches_rbt (RP_Branch CP_B RP_Var RP_Var) l_pre) **
      \<up>(inv1 (Branch c l_pre k v r)) **
      \<up>(inv2 (Branch c l_pre k v r))
    )
    (balance_left_opt n_p)
    (\<lambda>res. rbt_assn (rbt_balance_left l k v r) res)
  "
  unfolding 
    balance_left_opt_def
    bl_opt_case_1_def
    bl_opt_case_2_def
    bl_opt_case_3_def
    rotate_left_def
    rotate_right_def
    left_def
    right_def
  apply vcg
  subgoal (*case 1*)
    apply (cases "(l, k, v, r)" rule: RBT_Impl.balance_left.cases)
              apply auto
       apply vcg
    done
  subgoal (*case 2+*)
    apply vcg

    subgoal (*case 2*)
      apply (cases "(l, k, v, r)" rule: RBT_Impl.balance_left.cases)
                apply auto
       apply vcg
      done
    subgoal (*case 3+*)
      apply vcg
      subgoal (*case 4*)
        apply (cases "(l, k, v, r)" rule: RBT_Impl.balance_left.cases)
                  apply (auto elim!: matches_rbt.elims)
        done
      done
    done
  done

definition "br_opt_case_1 n_p \<equiv>
  do {
    l_p \<leftarrow> right n_p;
    set_color_p 0 n_p;
    set_color_p 1 l_p;
    return n_p
  }
"


definition "br_opt_case_2 n_p \<equiv>
  do {
    r_p \<leftarrow> left n_p;
    set_color_p 0 r_p;
    set_color_p 1 n_p;
    balance_opt n_p
  }
"


definition "br_opt_case_3 n_p \<equiv>
  do {
    r_p \<leftarrow> left n_p;

    r_p \<leftarrow> rotate_left r_p;
    set_left_p r_p n_p;

    n2_p \<leftarrow> rotate_right n_p;
    
    r_p \<leftarrow> left n2_p;
    rr_p \<leftarrow> left r_p;
    (if rr_p = null then return () else set_color_p 0 rr_p);

    set_color_p 1 r_p;
    r_p \<leftarrow> balance_opt r_p;
    set_left_p r_p n2_p;

    set_color_p 1 n_p;
    set_color_p 0 n2_p;
    return n2_p
  }
"


definition "balance_right_opt n_p \<equiv> 
  do {
    n \<leftarrow> ll_load n_p;
    case n of (RBT_NODE _ l_p k v r_p) \<Rightarrow>
    if! ll_matches_rbt br_pat_1 r_p
    then! br_opt_case_1 n_p
    else! if! ll_matches_rbt br_pat_2 l_p
    then! br_opt_case_2 n_p
    else! if! ll_matches_rbt br_pat_3 l_p
    then! br_opt_case_3 n_p
    else! do { 
      free n_p;
      empty
    }
  }"


lemma balance_right_opt_correct [vcg_rules]:
  "
    llvm_htriple
    (
      rbt_assn l li **
      \<upharpoonleft>key_assn k ki **
      \<upharpoonleft>value_assn v vi **
      rbt_assn r ri **
      color_assn c ci **
      \<upharpoonleft>ll_bpto (RBT_NODE ci li ki vi ri) n_p **

      \<up>(matches_rbt (RP_Branch CP_B RP_Var RP_Var) r_pre) **
      \<up>(inv1 (Branch c l k v r_pre)) **
      \<up>(inv2 (Branch c l k v r_pre))
    )
    (balance_right_opt n_p)
    (\<lambda>res. rbt_assn (rbt_balance_right l k v r) res)
  "
  unfolding 
    balance_right_opt_def
    br_opt_case_1_def
    br_opt_case_2_def
    br_opt_case_3_def
    rotate_right_def
    rotate_left_def
    right_def
    left_def

  apply vcg
  subgoal (*case 1*)
    apply (cases "(l, k, v, r)" rule: RBT_Impl.balance_right.cases)
              apply auto
       apply vcg
    done
  subgoal (*case 2+*)
    apply vcg

    subgoal (*case 2*)
      apply (cases "(l, k, v, r)" rule: RBT_Impl.balance_right.cases)
                apply auto
       apply vcg
      done
    subgoal (*case 3+*)
      apply vcg
      subgoal (*case 4*)
        apply (cases "(l, k, v, r)" rule: RBT_Impl.balance_right.cases)
                  apply (auto elim: matches_rbt.elims)
        done
      done
    done
  done

lemmas [llvm_inline] = 
  br_opt_case_1_def
  br_opt_case_2_def
  br_opt_case_3_def
  bl_opt_case_1_def
  bl_opt_case_2_def
  bl_opt_case_3_def


lemmas [llvm_code] =
  balance_right_opt_def
  balance_left_opt_def


lemma balance_left_opt_correct_combine [vcg_rules]:
  "
    llvm_htriple
    (
      rbt_assn l li **
      \<upharpoonleft>key_assn k ki **
      \<upharpoonleft>value_assn v vi **
      rbt_assn r ri **
      color_assn c ci **
      \<upharpoonleft>ll_bpto (RBT_NODE ci li ki vi ri) n_p **

      \<up>(matches_rbt (RP_Branch CP_B RP_Var RP_Var) r)
    )
    (balance_left_opt n_p)
    (\<lambda>res. rbt_assn (rbt_balance_left l k v r) res)
  "
  unfolding 
    balance_left_opt_def
    bl_opt_case_1_def
    bl_opt_case_2_def
    bl_opt_case_3_def
    rotate_left_def
    rotate_right_def
    left_def
    right_def
  apply vcg
  subgoal (*case 1*)
    apply (cases "(l, k, v, r)" rule: RBT_Impl.balance_left.cases)
              apply auto
    apply vcg
    done
  subgoal (*case 2+*)
    apply vcg
    done
  done

end


end