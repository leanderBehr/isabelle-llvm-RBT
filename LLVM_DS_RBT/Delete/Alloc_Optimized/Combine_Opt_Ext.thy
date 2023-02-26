theory Combine_Opt_Ext
  imports
    Combine_Opt
    Balance_Opt_LR_Ext
    "../../Assertion_Tree_Lookup"
    "../../Utilities_Ext"
begin

context rbt_impl
begin


lemma disjoint_trees_ptr_map_add_graph [simp]:
  assumes "rbt_of l |\<guillemotleft> k" and "k \<guillemotleft>| rbt_of r"
  shows
    "Map.graph (ptr_of_key l li ++ ptr_of_key r ri) =
         Map.graph (ptr_of_key l li) \<union> Map.graph (ptr_of_key r ri)" 
  unfolding map_add_def Map.graph_def
  apply (rule equalityI)
  subgoal by (auto split: option.splits)
  subgoal  
    apply (auto split: option.splits)
    by (metis assms linorder_not_less option.distinct(1) 
        ptr_of_key_greater_none ptr_of_key_less_none
        rbt_greater_trans rbt_less_eq_trans)
  done

lemma disjoint_trees_value_map_add_graph [simp]:
  assumes "rbt_of l |\<guillemotleft> k" and "k \<guillemotleft>| rbt_of r"
  shows
    "Map.graph (value_of_key l ++ value_of_key r) =
         Map.graph (value_of_key l) \<union> Map.graph (value_of_key r)" 
  unfolding map_add_def Map.graph_def
  apply (rule equalityI)
  subgoal by (auto split: option.splits)
  subgoal  
    apply (auto split: option.splits)
    by (metis assms linorder_not_less option.distinct(1)
        value_of_key_greater_none value_of_key_less_none
        rbt_greater_trans rbt_less_eq_trans)
  done

lemma combine_correct_ext':
  "
  llvm_htriple
  (rbt_assn_ext l {} li ** rbt_assn_ext r {} ri **
   \<up>(rbt_sorted (rbt_of l)) ** \<up>(rbt_sorted (rbt_of r)) ** \<up>(rbt_of l |\<guillemotleft> k \<and> k \<guillemotleft>| rbt_of r))
  (combine_opt li ri)
  (\<lambda>ti_res. EXS t_res.
    rbt_assn_ext t_res {} ti_res **
    ctx(rbt_of t_res = rbt_combine (rbt_of l) (rbt_of r)) **
    ctx(rbt_sorted (rbt_of t_res)) **
    \<up>(ptr_of_key t_res ti_res = ptr_of_key l li ++ ptr_of_key r ri) **
    \<up>(value_of_key t_res = value_of_key l ++ value_of_key r)
  )
  "
proof(induction "rbt_of l" "rbt_of r" arbitrary: l r li ri rule: RBT_Impl.combine.induct)
  case 1
  then show ?case
    apply (subst combine_opt.simps)
    apply vcg_vok
    done
next
  case (2 v va vb vc vd)
  then show ?case
    apply (subst combine_opt.simps)
    apply vcg_vok
    done
next
  case (3 a k x b c s y d)
  note 3(1)[simplified ctx_def, vcg_rules]

  from 3(2-3) show ?case
    supply
      RBT_Impl.combine.simps[simp del]
      combine_rbt_sorted[simp]

    apply (subst combine_opt.simps)
    apply vcg
    subgoal
      apply resolve_rbt_pat_mat
      subgoal
        apply vcg_compat
        apply sepE
         apply (auto simp add: RBT_Impl.combine.simps)[] 

        apply sep
         apply (simp add: combine_rbt_sorted)

        apply sep
        subgoal
          apply (simp add: ptr_of_key_simps)
          apply pok_solver
          done
        apply sep
        subgoal
          apply (simp add: value_of_key_simps)
          apply vok_solver
          done
        apply simp
        apply sep
        done
      done
    subgoal
      apply vcg
      apply vcg_compat

      apply sepE (*rbt_of*)

       apply (cases "rbt_combine b c")
        apply (auto simp add: RBT_Impl.combine.simps split: color.splits)[2]

      apply sep (*sorted*)
       apply simp

      apply sep
      subgoal
        apply (simp add: ptr_of_key_simps)
        apply pok_solver 
        done

      apply sep
      subgoal
        apply (simp add: value_of_key_simps)
        apply vok_solver
        done

      apply simp
      apply sep
      done
    done
next
  case (4 a k x b c s y d)
  note 4(1)[simplified ctx_def, vcg_rules]

  from 4(2-3) show ?case
    supply
      RBT_Impl.combine.simps[simp del]
      combine_rbt_sorted[simp]

    apply (subst combine_opt.simps)
    apply vcg
    subgoal
      apply resolve_rbt_pat_mat
      apply vcg_compat

      apply sepE
       apply (auto simp add: RBT_Impl.combine.simps)[] (*rbt_of*)

      apply sep (*sorted*)
       apply simp 

      apply sep (*pok*)
      subgoal
        apply (simp add: ptr_of_key_simps)
        apply pok_solver
        done

      apply sep (*vok*)
      subgoal
        apply (simp add: value_of_key_simps)
        apply vok_solver
        done

      apply simp
      apply sep
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
      apply (simp add: ptr_of_key_simps)
      apply pok_solver

      apply sep
      apply (simp add: value_of_key_simps)
      apply vok_solver
      
      apply sep
      done
    done
next
  case (5 va vb vc vd b k x c)
  note 5(1)[simplified ctx_def, vcg_rules]
  from 5(2-3) show ?case
    supply
      RBT_Impl.combine.simps[simp del]
      combine_rbt_sorted[simp]

    apply (subst combine_opt.simps)
    apply vcg
    apply vcg_compat
    subgoal
      supply  
        rbt_less_trans[intro]
        rbt_greater_trans[intro]

      apply sepE
       apply (simp add: RBT_Impl.combine.simps)

      apply sep
       apply simp

      apply sep
       apply (simp add: ptr_of_key_simps)
       apply pok_solver

      apply sep
       apply (simp add: value_of_key_simps)
       apply vok_solver

      apply simp 
      apply sep
      done 
    done
next
  case (6 a k x b va vb vc vd)
  note 6(1)[simplified ctx_def, vcg_rules]
  from 6(2-3) show ?case
    supply
      RBT_Impl.combine.simps[simp del]
      combine_rbt_sorted[simp]

    apply (subst combine_opt.simps)
    apply vcg
    apply vcg_compat
    subgoal
      supply  
        rbt_less_trans[intro]
        rbt_greater_trans[intro]

      apply sepE
       apply (simp add: RBT_Impl.combine.simps)

      apply sep
       apply simp

      apply sep
       apply (simp add: ptr_of_key_simps)
       apply pok_solver

      apply sep
       apply (simp add: value_of_key_simps)
       apply vok_solver

      apply simp 
      apply sep
      done 
    done
qed

lemmas combine_correct_ext[vcg_rules] = combine_correct_ext'[simplified ctx_def]

end

end