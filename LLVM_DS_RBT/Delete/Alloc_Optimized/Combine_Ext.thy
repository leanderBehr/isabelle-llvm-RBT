theory Combine_Ext
  imports
    Combine_Opt
    Balance_Opt_LR_Ext
    "../../Assertion_Tree_Lookup"
    "../../Utilities_Ext"
begin

context rbt_impl
begin


lemma disjoint_trees_map_add_graph [simp]:
  assumes "rbt_of l |\<guillemotleft> k" and "k \<guillemotleft>| rbt_of r"
  shows
    "Map.graph (ptr_of_key l li ++ ptr_of_key r ri) =
         Map.graph (ptr_of_key l li) \<union> Map.graph (ptr_of_key r ri)" 
  unfolding map_add_def Map.graph_def
  apply (rule equalityI)
  subgoal by (auto split: option.splits)
  subgoal apply (auto split: option.splits)
    subgoal for a b x2
    proof (cases k a rule: linorder_cases)
      case less
      with assms have "ptr_of_key l li a = None"  
        using ptr_of_key_less_none rbt_less_trans by blast
      moreover assume "ptr_of_key l li a = Some b"
      ultimately show ?thesis by simp
    next
      case equal
      with assms have "ptr_of_key l li a = None"  
        using ptr_of_key_less_none rbt_less_trans by blast
      moreover assume "ptr_of_key l li a = Some b"
      ultimately show ?thesis by simp

    next
      case greater
      with assms have "ptr_of_key r ri a = None"  
        using ptr_of_key_greater_none rbt_greater_trans by blast
      moreover assume "ptr_of_key r ri a = Some x2"
      ultimately show ?thesis by simp
    qed
    done
  done

lemma combine_correct_ext':
  "
  llvm_htriple
  (rbt_assn_ext l {} li ** rbt_assn_ext r {} ri **
   \<up>(rbt_sorted (rbt_of l)) ** \<up>(rbt_sorted (rbt_of r)) ** \<up>(rbt_of l |\<guillemotleft> k \<and> k \<guillemotleft>| rbt_of r))
  (combine_opt li ri)
  (\<lambda>res_ti. EXS res_t.
    rbt_assn_ext res_t {} res_ti **
    ctx(rbt_of res_t = rbt_combine (rbt_of l) (rbt_of r)) **
    ctx(rbt_sorted (rbt_of res_t)) **
    \<up>(ptr_of_key res_t res_ti = ptr_of_key l li ++ ptr_of_key r ri)
  )
  "
  supply ptr_of_key_simps[simp]
  supply sep_context_pureI[fri_red_rules]
proof(induction "rbt_of l" "rbt_of r" arbitrary: l r li ri rule: RBT_Impl.combine.induct)
  case 1
  then show ?case
    apply (subst combine_opt.simps)
    apply vcg
    done
next
  case (2 v va vb vc vd)
  then show ?case
    apply (subst combine_opt.simps)
    apply vcg
    done
next
  case (3 a k x b c s y d)
  note 3(1)[simplified ctx_def, vcg_rules]

  from 3(2-3) show ?case
    supply RBT_Impl.combine.simps[simp del]

    apply (subst combine_opt.simps)
    apply vcg
    subgoal
      apply resolve_rbt_pat_mat
      subgoal
        supply rbt_sorted.simps[simp del]
        apply vcg
        apply vcg_compat
        subgoal
          apply sepE
           apply (auto simp add: RBT_Impl.combine.simps)[] 

          apply sep
           apply simp
           apply (rule combine_rbt_sorted)
          using rbt_sorted.simps apply fast+
            apply auto[2]

          apply (sepwith auto)
          apply simp
          apply (sepwith simp)

          done
        done
      done
    subgoal
      supply rbt_sorted.simps[simp del]
      apply vcg
      apply vcg_try_solve
       apply (cases "rbt_combine b c")
        apply (auto simp add: RBT_Impl.combine.simps split: color.splits)[2]
      apply vcg_compat
      apply sep

       apply simp
       apply (rule combine_rbt_sorted)
      using rbt_sorted.simps apply fast+
        apply auto[2]

      apply sep  
       apply simp
       apply (auto simp: rbt_sorted.simps)[1]

      apply sep
      done
    done
next
  case (4 a k x b c s y d)
  note 4(1)[simplified ctx_def, vcg_rules]

  from 4(2-3) show ?case
    supply RBT_Impl.combine.simps[simp del]

    apply (subst combine_opt.simps)
    apply vcg
    subgoal
      apply resolve_rbt_pat_mat
      supply rbt_sorted.simps[simp del]
      apply vcg
      apply vcg_compat
      subgoal
        apply sepE
         apply (auto simp add: RBT_Impl.combine.simps)[] 

        apply sep
         apply simp
         apply (rule combine_rbt_sorted)
        using rbt_sorted.simps apply fast+
          apply auto[2]

        apply (sepwith auto)
        apply simp
        apply (sepwith simp)

        done
      done

    subgoal
      supply  
        rbt_less_trans[intro]
        rbt_greater_trans[intro]
        combine_rbt_greater[intro]
        combine_rbt_less[intro]
      apply vcg
      apply vcg_compat
      apply sepE
       apply (cases "rbt_combine b c")
        apply (auto simp add: RBT_Impl.combine.simps split: color.splits)[2]
      apply sep

       apply simp
      apply sep

       apply simp 
       apply (subst ptr_of_key_simps(4), (auto)[])+
       apply auto[1]

      apply sep
      done
    done
  next
    case (5 va vb vc vd b k x c)
    note 5(1)[simplified ctx_def, vcg_rules]
    note load_rbt_non_null[vcg_rules]
    from 5(2-3) show ?case
      apply (subst combine_opt.simps)
      apply vcg
      apply vcg_compat
      subgoal
        supply  
          rbt_less_trans[intro]
          rbt_greater_trans[intro]
          combine_rbt_greater[intro]
          combine_rbt_less[intro]

        apply (sepEwith force)
        apply simp 
        apply (sepwith simp)
        done 
      done
  next
    case (6 a k x b va vb vc vd)
    note 6(1)[simplified ctx_def, vcg_rules]
    note load_rbt_non_null[vcg_rules]
    from 6(2-3) show ?case
      apply (subst combine_opt.simps)
      apply vcg
      apply vcg_compat
      subgoal
        supply  
          rbt_less_trans[intro]
          rbt_greater_trans[intro]
          combine_rbt_greater[intro]
          combine_rbt_less[intro]

        apply (sepEwith force)
        apply simp 
        apply (sepwith simp)
        done 
      done
  qed

lemmas combine_correct_ext[vcg_rules] = combine_correct_ext'[simplified ctx_def]

end

end