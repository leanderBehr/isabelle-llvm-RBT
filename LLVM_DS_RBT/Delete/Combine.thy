theory Combine
  imports Balance_LR
begin


context rbt_impl
begin
interpretation llvm_prim_ctrl_setup .
interpretation llvm_prim_arith_setup .
interpretation llvm_prim_setup .


abbreviation "is_black_b x \<equiv> matches_rbt_pattern (Branch CP_B RVar RVar) x"
abbreviation "is_red_b x \<equiv> matches_rbt_pattern (Branch CP_R RVar RVar) x"

abbreviation "is_black_b_i x \<equiv> matches_rbt_pattern_i (Branch CP_B RVar RVar) x"
abbreviation "is_red_b_i x \<equiv> matches_rbt_pattern_i (Branch CP_R RVar RVar) x"


partial_function (M) combine ::
  "('ki, 'v::llvm_rep) rbti \<Rightarrow> ('ki, 'v) rbti \<Rightarrow> ('ki, 'v) rbti llM" where
  "combine l_p r_p = do {
    if l_p = null then return r_p
    else if r_p = null then return l_p
    else do {
      l \<leftarrow> ll_load l_p;
      r \<leftarrow> ll_load r_p;
      if rbt_node.color l = rbt_node.color r
      then do {
        combined_p \<leftarrow> combine (rbt_node.right l) (rbt_node.left r);
        is_red_b \<leftarrow> is_red_b_i combined_p;
        if is_red_b = ll_True then
        do {
            combined \<leftarrow> ll_load combined_p;
            case combined of (RBT_NODE cc cl ck cv cr) \<Rightarrow>
            do {
              set_right_p cl l_p;
              set_left_p cr r_p;
              ll_store (RBT_NODE cc l_p ck cv r_p) combined_p;
              return combined_p
            }
        }
        else do {
          set_left_p combined_p r_p;
          if rbt_node.color l = 0
          then do {
            set_right_p r_p l_p;
            return l_p
          }
          else do {
            case l of (RBT_NODE _ ll lk lv _) \<Rightarrow>
            do {
              ll_free l_p;
              balance_left ll lk lv r_p
            }
          }
        }
      }
      else if (rbt_node.color r = 0)
      then do {
        combined_p \<leftarrow> combine l_p (rbt_node.left r);
        set_left_p combined_p r_p;
        return r_p
      }
      else do { 
        combined_p \<leftarrow> combine (rbt_node.right l) r_p;
        set_right_p combined_p l_p;
        return l_p
      }
    }
  }"


lemma combine_correct:
"
  llvm_htriple
  (\<upharpoonleft>rbt_assn l li ** \<upharpoonleft>rbt_assn r ri)
  (combine li ri)
  (\<lambda>x. \<upharpoonleft>rbt_assn (rbt_combine l r) x)
"
proof(induction l r arbitrary: li ri rule: combine.induct)
  case (1 x)
  then show ?case 
    apply (subst combine.simps)
    apply vcg
    done
next
  case (2 v va vb vc vd)
  then show ?case 
    apply (subst combine.simps)
    apply vcg
    done
next
  case (3 a k x b c s y d)
  note [vcg_rules] = 3
  show ?case
    apply (subst combine.simps)
    apply vcg
    subgoal
      apply resolve_rbt_pat_mat
      apply vcg
      unfolding rbt_assn_branch_def
      apply vcg_try_solve
      done
    subgoal
      apply vcg
      apply simp
      apply (cases "rbt_combine b c")
       apply auto
      subgoal
        unfolding rbt_assn_branch_def
        apply vcg
        done
      subgoal for col
        apply (auto split: color.splits)
        apply (rule close_rbt_assn[where ti=ri], vcg_solve)
        apply (rule close_rbt_assn[where ti=li], vcg_solve)
        apply vcg
        done
        (*broken*)
        (*
        apply (cases col, auto)
        unfolding rbt_assn_branch_def
        apply vcg_solve
        apply fri_dbg_start
        apply (rule fri_exE)+
        apply fri_dbg_step

        apply fri_dbg_step
         apply fri_dbg_step
         apply vcg_try_solve
        apply fri_dbg_step
        apply fri_dbg_step
        apply fri_dbg_step
        apply fri_dbg_step
        apply fri_dbg_step
         apply fri_dbg_step
         apply vcg_try_solve
        apply fri_dbg_step
        apply fri_dbg_step
        sorry
      *)
      done
    done
next
  case (4 a k x b c s y d)
  note [vcg_rules] = 4
  show ?case
    apply (subst combine.simps)
    apply vcg
    subgoal
      apply resolve_rbt_pat_mat
      apply vcg
      apply (simp add: rbt_assn_branch_def)
      apply vcg
      done
    subgoal
      apply vcg
      apply (erule close_rbt_assn, vcg_solve)
      apply vcg
      apply (cases "rbt_combine b c")
      subgoal 
        apply auto
        apply vcg
        done
      subgoal
        apply (auto split: color.splits)
        apply vcg
        done
      done
    done
next
  case (5 va vb vc vd b k x c)

  note [vcg_rules] = 5

  show ?case
    apply (subst combine.simps)
    apply vcg
    apply (erule close_rbt_assn[where ti=li], vcg_solve)
    apply vcg
    apply (rule close_rbt_assn[where ti=ri], vcg_solve)
    apply vcg
    done
next
  case (6 a k x b va vb vc vd)
  note [vcg_rules] = 6
  show ?case
    apply (subst combine.simps)
    apply vcg
    apply (erule close_rbt_assn[where ti=ri], vcg_solve)
    apply vcg
    apply (rule close_rbt_assn[where ti=li], vcg_solve)
    apply vcg    
    done
qed


end


end