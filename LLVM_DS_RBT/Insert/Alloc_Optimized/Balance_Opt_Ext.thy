theory Balance_Opt_Ext
  imports 
    Balance_Opt
    "../../Assertion_Tree_Lookup"
    "../../Utilities_Ext"
begin

context rbt_impl
begin

lemma balance_opt_correct_ext [vcg_rules]:
  "llvm_htriple
  (
    rbt_assn_ext (ATBranch color.B k v ci li ki vi ri l r) {} ti ** \<up>(rbt_sorted (rbt_of (ATBranch color.B k v ci li ki vi ri l r)))
  )
  (balance_opt ti)
  (\<lambda>res. EXS res_t. rbt_assn_ext res_t {} res **
    \<up>(rbt_of res_t = rbt_balance (rbt_of l) k v (rbt_of r)) **
    \<up>(rbt_sorted (rbt_of res_t)) **
    \<up>(ptr_of_key res_t res = ptr_of_key (ATBranch color.B k v ci li ki vi ri l r) ti)  
  )
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
    right_def
    left_def
  supply rbt_greater_trans[intro] rbt_less_trans[intro]
  apply vcg
  subgoal (*Case 1*)
    apply (cases "(rbt_of l, k, v, rbt_of r)" rule: RBT_Impl.balance.cases)
    apply auto
    apply vcg
    done
  subgoal (*Case 2+*)
    apply vcg
    subgoal (*Case 2*)
      apply (cases "(rbt_of l, k, v, rbt_of r)" rule: RBT_Impl.balance.cases)
      apply auto
      apply vcg
      done
    subgoal (*Case 3+*)
      apply vcg
      subgoal (*Case 3*)
        apply (cases "(rbt_of l, k, v, rbt_of r)" rule: RBT_Impl.balance.cases)
        apply auto 
        apply vcg
        done
      subgoal (*Case 4+*)
        apply vcg
        subgoal (*Case 4*)
          apply (cases "(rbt_of l, k, v, rbt_of r)" rule: RBT_Impl.balance.cases)
          apply auto
          apply vcg
          done
        subgoal (*Case 5*)
          apply (cases "(rbt_of l, k, v, rbt_of r)" rule: RBT_Impl.balance.cases)
          apply auto
          apply vcg
          done
        done
      done
    done
  done

end

end