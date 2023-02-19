theory Balance_LR
  imports
    "../Setup"
    "../Utilities"
    "../Insert/Balance"
    "../Free"
begin


context rbt_impl
begin
interpretation rbt_impl_deps .

subsection \<open>Balance Left\<close>


subsubsection \<open>Patterns\<close>


abbreviation "bl_pat_1 \<equiv> RP_Branch CP_R RP_Var RP_Var"
abbreviation "bl_pat_2 \<equiv> RP_Branch CP_B RP_Var RP_Var"
abbreviation "bl_pat_3 \<equiv> RP_Branch CP_R (RP_Branch CP_B RP_Var RP_Var) RP_Var"


subsubsection \<open>Adjusted Function\<close>


fun rbt_balance_left_ad where
  "rbt_balance_left_ad l key val r =
    (
      if matches_rbt bl_pat_1 l
      then case l of (rbt.Branch color.R a k x b) \<Rightarrow>
        rbt.Branch color.R (rbt.Branch color.B a k x b) key val r
      else if matches_rbt bl_pat_2 r
      then case r of (rbt.Branch color.B a s y b) \<Rightarrow> 
        rbt_balance l key val (rbt.Branch color.R a s y b)
      else if matches_rbt bl_pat_3 r
      then case r of (rbt.Branch color.R (rbt.Branch color.B a s y b) t z c) \<Rightarrow>
        rbt.Branch color.R (rbt.Branch color.B l key val a) s y (rbt_balance b t z (paint color.R c))
      else rbt.Empty
    )"

lemma rbt_balance_left_ad_correct:
  "rbt_balance_left_ad l k v r = rbt_balance_left l k v r"
  apply(induction l k v r rule: RBT_Impl.balance_left.induct)
  by auto


subsubsection \<open>Concrete Implementation\<close>


definition "bl_case_1 l_p k v r_p \<equiv>
  do {
    set_color_p 1 l_p;
    new (RBT_NODE 0 l_p k v r_p)
  }"


definition "bl_case_2 l_p k v r_p \<equiv> 
  do {
    set_color_p 0 r_p;
    balance l_p k v r_p
  }"


definition "bl_case_3 l_p k v r_p \<equiv> 
  do {
    let bl=l_p; k=k; x=v in
    do {
      r \<leftarrow> ll_load r_p;
      case r of (RBT_NODE r_col rl_p t z c) \<Rightarrow> 
      do {
        rl \<leftarrow> ll_load rl_p;
        case rl of (RBT_NODE rl_col a s y b) \<Rightarrow>
        do {
          (if c \<noteq> null then set_color_p 0 c else return ());
          balanced \<leftarrow> balance b t z c;
          ll_store (RBT_NODE 1 bl k x a) rl_p;
          ll_store (RBT_NODE 0 rl_p s y balanced) r_p;
          return r_p
        }
      }
    }
  }"


definition "balance_left l_p k v r_p \<equiv> 
  do {
    if! ll_matches_rbt bl_pat_1 l_p
    then! bl_case_1 l_p k v r_p
    else! if! ll_matches_rbt bl_pat_2 r_p
    then! bl_case_2 l_p k v r_p
    else! if! ll_matches_rbt bl_pat_3 r_p
    then! bl_case_3 l_p k v r_p
    else! do { 
      key_free k;
      value_free v;
      free l_p; free r_p;
      empty
    }
  }"


lemmas [llvm_inline] = 
  bl_case_1_def
  bl_case_2_def
  bl_case_3_def


lemmas [llvm_code] = balance_left_def


lemma balance_left_correct':
  "
    llvm_htriple
    (rbt_assn l li ** \<upharpoonleft>key_assn k ki ** \<upharpoonleft>value_assn v vi ** rbt_assn r ri)
    (balance_left li ki vi ri)
    (\<lambda>x. rbt_assn (rbt_balance_left_ad l k v r) x)
  "
  unfolding 
    balance_left_def
    bl_case_1_def
    bl_case_2_def
    bl_case_3_def
  apply vcg
  subgoal (*case 1*)
    apply resolve_rbt_pat_mat
    apply vcg
    done
  subgoal (*case 2+*)

    apply vcg
  
    subgoal (*case 2*)
      apply resolve_rbt_pat_mat
      apply vcg
      done
    subgoal (*case 3+*)
      apply vcg
      subgoal (*case 3*)
        apply resolve_rbt_pat_mat
        apply vcg
        supply load_rbt_non_null[vcg_rules]
        apply vcg
        done
      subgoal (*case 4*) by vcg
      done
    done
  done

lemma balance_left_correct [vcg_rules]:
  "
    llvm_htriple
    (rbt_assn l li ** \<upharpoonleft>key_assn k ki ** \<upharpoonleft>value_assn v vi ** rbt_assn r ri)
    (balance_left li ki vi ri)
    (\<lambda>x. rbt_assn (rbt_balance_left l k v r) x)
  "
  using balance_left_correct' rbt_balance_left_ad_correct by metis


subsection \<open>Balance Right\<close>


subsubsection \<open>Patterns\<close>


abbreviation "br_pat_1 \<equiv> RP_Branch CP_R RP_Var RP_Var"
abbreviation "br_pat_2 \<equiv> RP_Branch CP_B RP_Var RP_Var"
abbreviation "br_pat_3 \<equiv> RP_Branch CP_R RP_Var (RP_Branch CP_B RP_Var RP_Var)"


subsubsection \<open>Concrete Implementation\<close>


definition "br_case_1 l_p k v r_p \<equiv>
  do {
    set_color_p 1 r_p;
    new (RBT_NODE 0 l_p k v r_p)
  }"


definition "br_case_2 l_p k v r_p \<equiv> 
  do {
    set_color_p 0 l_p;
    balance l_p k v r_p
  }"


definition "br_case_3 l_p k v r_p \<equiv> 
  do {
    let bl=r_p; t=k; z=v in
    do {
      l \<leftarrow> ll_load l_p;
      case l of (RBT_NODE l_col a k x lr_p) \<Rightarrow> 
      do {
        lr \<leftarrow> ll_load lr_p;
        case lr of (RBT_NODE lr_col b s y c) \<Rightarrow>
        do {
          (if a \<noteq> null then set_color_p 0 a else return ());
          balanced \<leftarrow> balance a k x b;
          ll_store (RBT_NODE 1 c t z bl) lr_p;
          ll_store (RBT_NODE 0 balanced s y lr_p) l_p;
          return l_p
        }
      }
    }
  }"


definition "balance_right l_p k v r_p \<equiv>
  do {
    if! ll_matches_rbt br_pat_1 r_p
    then! br_case_1 l_p k v r_p
    else! if! ll_matches_rbt br_pat_2 l_p
    then! br_case_2 l_p k v r_p
    else! if! ll_matches_rbt br_pat_3 l_p
    then! br_case_3 l_p k v r_p
    else! do { 
      key_free k;
      value_free v;
      free l_p; free r_p;
      empty
    }
  }
"

lemma neq_Red: "(c \<noteq> color.R) = (c = color.B)"
  using color.exhaust by blast

method resolve_rbt_pat_mat' =
  ((erule matches_rbt.elims(2-3) | simp add: neq_Red)+)[1]

lemma balance_right_correct [vcg_rules]: 
  "
    llvm_htriple
    (rbt_assn l li ** \<upharpoonleft>key_assn k ki ** \<upharpoonleft>value_assn v vi ** rbt_assn r ri)
    (balance_right li ki vi ri)
    (\<lambda>x. rbt_assn (rbt_balance_right l k v r) x)
  "
  unfolding
    balance_right_def
    br_case_1_def
    br_case_2_def
    br_case_3_def
  apply vcg
  subgoal (*case 1*)
    apply resolve_rbt_pat_mat
    apply vcg
    done
  subgoal (*case 2+*)
    apply vcg
    subgoal (*case 2*)
      apply (cases "(l, k, v, r)" rule: RBT_Impl.balance_right.cases, auto)
       apply vcg
      done
    subgoal (*case 3+*)
      apply vcg
      subgoal (*case 3*)
        apply (cases "(l, k, v, r)" rule: RBT_Impl.balance_right.cases, auto)
         supply load_rbt_non_null[vcg_rules]
         apply vcg
        done
      subgoal (*case 4*) 
        apply (cases "(l, k, v, r)" rule: RBT_Impl.balance_right.cases, auto)
             apply vcg
        done
      done
    done
  done


lemmas [llvm_inline] = 
  br_case_1_def
  br_case_2_def
  br_case_3_def


lemmas [llvm_code] = balance_right_def


end

end