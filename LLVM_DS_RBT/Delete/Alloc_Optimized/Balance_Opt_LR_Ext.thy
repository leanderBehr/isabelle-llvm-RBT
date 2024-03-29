theory Balance_Opt_LR_Ext
  imports 
    "../../Free_Ext"
    "../../Insert/Alloc_Optimized/Balance_Opt_Ext"
    Balance_Opt_LR
    
begin


context rbt_impl
begin

lemma balance_left_opt_ext_correct':
  "
  llvm_htriple
  ( 
    \<upharpoonleft>ll_bpto (RBT_NODE ci li ki vi ri) n_p **
    rbt_assn_ext l {} li **
    \<upharpoonleft>key_assn k ki **
    \<upharpoonleft>value_assn v vi **
    rbt_assn_ext r {} ri **
    color_assn c ci **
    \<up>(rbt_sorted (Branch c (rbt_of l) k v (rbt_of r))) **
    
    
    \<up>(matches_rbt (RP_Branch CP_B RP_Var RP_Var) l_pre) ** 
    \<up>(inv1 (Branch c l_pre k v (rbt_of r))) **
    \<up>(inv2 (Branch c l_pre k v (rbt_of r)))
  )
  (balance_left_opt n_p)
  (\<lambda>ti_res. EXS t_res.
    rbt_assn_ext t_res {} ti_res **
    \<up>(rbt_of t_res = rbt_balance_left (rbt_of l) k v (rbt_of r)) **
    ctx(rbt_sorted (rbt_of t_res)) **
    \<up>(ptr_of_key t_res ti_res = ptr_of_key (ATBranch c k v ci li ki vi ri l r) n_p) **
    \<up>(value_of_key t_res = value_of_key (ATBranch c k v ci li ki vi ri l r))
  )
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
  supply sep_context_pureI[fri_red_rules]
  apply vcg
  subgoal (*case 1*)
    apply (cases "(rbt_of l, k, v, rbt_of r)" rule: RBT_Impl.balance_left.cases, auto)
     apply vcg_vok
    done
  subgoal (*case 2+*)
    apply vcg

    subgoal (*case 2*)
      apply (cases "(rbt_of l, k, v, rbt_of r)" rule: RBT_Impl.balance_left.cases, auto)
      subgoal by vcg_vok
      subgoal by vcg_vok
      subgoal by vcg_vok
      subgoal by vcg_vok

      done
    subgoal (*case 3+*)
      apply vcg
      subgoal (*case 3*)
        apply (cases "(rbt_of l, k, v, rbt_of r)" rule: RBT_Impl.balance_left.cases, auto)
         supply rbt_greater_trans[intro]
         supply rbt_less_trans[intro]

        subgoal 
          apply vcg
          apply vcg_compat
          subgoal
            apply (sepEwith \<open>solves auto | solves pok_solver | solves vok_solver\<close>)
            apply simp
            apply sep
            done
          done

        subgoal
          apply vcg
          apply vcg_compat
          subgoal
            apply (sepEwith \<open>solves auto | solves pok_solver | solves vok_solver\<close>)
            apply simp
            apply sep
            done
          done
        done
      subgoal (*case 4*)
        apply (cases "(rbt_of l, k, v, rbt_of r)" rule: RBT_Impl.balance_left.cases)
                  apply (auto elim: matches_rbt.elims)
        done
      done
    done
  done


lemmas balance_left_opt_ext_correct[vcg_rules] = balance_left_opt_ext_correct'[simplified ctx_def]

lemma balance_right_opt_ext_correct':
  "
  llvm_htriple
  ( 
    \<upharpoonleft>ll_bpto (RBT_NODE ci li ki vi ri) n_p **
    rbt_assn_ext l {} li **
    \<upharpoonleft>key_assn k ki **
    \<upharpoonleft>value_assn v vi **
    rbt_assn_ext r {} ri **
    color_assn c ci **
    \<up>(rbt_sorted (Branch c (rbt_of l) k v (rbt_of r))) **

    \<up>(matches_rbt (RP_Branch CP_B RP_Var RP_Var) r_pre) **
    \<up>(inv1 (Branch c (rbt_of l) k v r_pre)) **
    \<up>(inv2 (Branch c (rbt_of l) k v r_pre))
  )
  (balance_right_opt n_p)
  (\<lambda>ti_res. EXS t_res.
    rbt_assn_ext t_res {} ti_res **
    \<up>(rbt_of t_res = rbt_balance_right (rbt_of l) k v (rbt_of r)) **
    ctx(rbt_sorted (rbt_of t_res)) **
    \<up>(ptr_of_key t_res ti_res = ptr_of_key (ATBranch c k v ci li ki vi ri l r) n_p) **
    \<up>(value_of_key t_res = value_of_key (ATBranch c k v ci li ki vi ri l r))
  )
  "
  unfolding 
    balance_right_opt_def
    br_opt_case_1_def
    br_opt_case_2_def
    br_opt_case_3_def
    rotate_left_def
    rotate_right_def
    left_def
    right_def
  apply vcg
  subgoal (*case 1*)
    apply (cases "(rbt_of l, k, v, rbt_of r)" rule: RBT_Impl.balance_right.cases, auto)
     apply vcg_vok
    done
  subgoal (*case 2+*)
    apply vcg

    subgoal (*case 2*)
      apply (cases "(rbt_of l, k, v, rbt_of r)" rule: RBT_Impl.balance_right.cases, auto)
      subgoal by vcg_vok
      subgoal by vcg_vok
      subgoal by vcg_vok
      subgoal by vcg_vok
      done
    subgoal (*case 3+*)
      apply vcg
      subgoal (*case 3*)
        apply (cases "(rbt_of l, k, v, rbt_of r)" rule: RBT_Impl.balance_right.cases, auto)
         supply rbt_greater_trans[intro]
         supply rbt_less_trans[intro]

        subgoal
          apply vcg
          apply vcg_compat
          subgoal
            apply (sepEwith \<open>solves auto | solves pok_solver | solves vok_solver\<close>)
            apply simp
            apply sep
            done
          done

        subgoal 
          apply vcg
          apply vcg_compat
          subgoal
            apply (sepEwith \<open>solves auto | solves pok_solver | solves vok_solver\<close>)
            apply simp
            apply sep
            done
          done
        done
      subgoal (*case 4*)
        apply (cases "(rbt_of l, k, v, rbt_of r)" rule: RBT_Impl.balance_right.cases)
        by (auto elim: matches_rbt.elims)
      done
    done
  done

lemmas balance_right_opt_ext_correct[vcg_rules] = balance_right_opt_ext_correct'[simplified ctx_def]



lemma balance_left_opt_ext_combine_correct':
  "
  llvm_htriple
  ( 
    \<upharpoonleft>ll_bpto (RBT_NODE ci li ki vi ri) n_p **
    rbt_assn_ext l {} li **
    \<upharpoonleft>key_assn k ki **
    \<upharpoonleft>value_assn v vi **
    rbt_assn_ext r {} ri **
    color_assn c ci **
    \<up>(rbt_sorted (Branch c (rbt_of l) k v (rbt_of r))) **
    \<up>(matches_rbt (RP_Branch CP_B RP_Var RP_Var) (rbt_of r))
  )
  (balance_left_opt n_p)
  (\<lambda>ti_res. EXS t_res.
    rbt_assn_ext t_res {} ti_res **
    \<up>(rbt_of t_res = rbt_balance_left (rbt_of l) k v (rbt_of r)) **
    ctx(rbt_sorted (rbt_of t_res)) **
    \<up>(ptr_of_key t_res ti_res = ptr_of_key (ATBranch c k v ci li ki vi ri l r) n_p) **
    \<up>(value_of_key t_res = value_of_key (ATBranch c k v ci li ki vi ri l r))
  )
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
    apply (cases "(rbt_of l, k, v, rbt_of r)" rule: RBT_Impl.balance_left.cases, auto)
    apply vcg_vok
    done
  subgoal (*case 2+*)
    apply vcg

    subgoal (*case 2*)
      apply (cases "(rbt_of l, k, v, rbt_of r)" rule: RBT_Impl.balance_left.cases, auto)
       apply vcg_vok
      done
    apply vcg (*all other cases unreachable*)
    done
  done

lemmas balance_left_opt_ext_combine_correct[vcg_rules] =
  balance_left_opt_ext_combine_correct'[simplified ctx_def]

end

end