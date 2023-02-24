theory Delete_Opt_Ext
  imports 
    Delete_Opt
    Balance_Opt_LR_Ext
    Combine_Opt_Ext
    "../../Assertion_Tree_Lookup"
    "../../Utilities_Ext"
begin

context rbt_impl
begin

lemma del_opt_correct_ext':
  "
  llvm_htriple
  (rbt_assn_ext t {} ti ** \<upharpoonleft>key_assn k ki ** \<up>(is_rbt_node (rbt_of t)))
  (del_opt ki ti)
  (\<lambda>ti_res. EXS t_res.
    rbt_assn_ext t_res {} ti_res **
    \<upharpoonleft>key_assn k ki **
    \<up>(rbt_of t_res = rbt_del_ad k (rbt_of t)) **
    ctx(rbt_sorted (rbt_of t_res)) **
    \<up>((ptr_of_key t ti)(k := None) \<subseteq>\<^sub>m ptr_of_key t_res ti_res) **
    \<up>((value_of_key t)(k := None) \<subseteq>\<^sub>m value_of_key t_res)
  )
  "
  supply sep_context_pureI[fri_red_rules]
proof(induct k "rbt_of t" arbitrary: t ki ti rule: rbt_del_ad.induct)
  case (1 k)
  then show ?case
    apply (subst del_opt.simps)
    apply vcg
    done
next
  case (2 k c l kc vc r)

  from 2(5) show ?case
    apply (subst del_opt.simps)
    supply load_rbt_non_null[vcg_rules]
    apply vcg

    subgoal for al ar ci li ki vi ri asf ra sa (*k < kc*)
      apply (cases ra)
      subgoal (*ra = 0*)
        supply 2(2)[simplified ctx_def, vcg_rules]

        supply rbt_del_ad_correct[simp]
        supply rbt_del_rbt_less[intro]
        supply rbt_del_rbt_sorted[intro]

        supply ptr_of_key_simps[simp]
        supply value_of_key'_simps[simp]

        apply vcg 
        apply vcg_compat
        apply (sepEwith auto)
        apply simp
        apply sep
        done

      subgoal (*ra = 1*)
        supply 2(1)[simplified ctx_def, vcg_rules]
        supply rbt_del_rbt_less[simp]
        supply rbt_del_ad_correct[simp]


        apply vcg
        apply vcg_compat

        supply value_of_key'_simps[simp]
        supply ptr_of_key_simps[simp]

        apply (sepEwith \<open>solves auto\<close>)
        done
      done

    subgoal for al ar ci li ki vi ri asf ra s (*kc \<le> k*)
      apply vcg
      subgoal for rb sa (*kc < k*)
              apply (cases rb)
      subgoal (*rb = 0*)
        supply 2(4)[simplified ctx_def, vcg_rules]

        supply rbt_del_ad_correct[simp]
        supply rbt_del_rbt_greater[intro]
        supply rbt_del_rbt_sorted[intro]

        supply ptr_of_key_simps[simp]
        supply value_of_key'_simps[simp]

        apply vcg 
        apply vcg_compat
        apply (sepEwith auto)

        apply simp
        apply sep
        done

      subgoal (*rb = 1*)
        supply 2(3)[simplified ctx_def, vcg_rules]
        supply rbt_del_rbt_greater[simp]
        supply rbt_del_ad_correct[simp]
        supply ptr_of_key_simps[simp]

        apply vcg 
        supply value_of_key'_simps[simp]
        apply vcg_vok

        done
      done
      subgoal (*kc = k*)
        supply ptr_of_key_simps[simp]
        supply value_of_key'_simps[simp]
        apply vcg_vok
      done
    done
  done
qed

lemmas del_opt_ext_correct = del_opt_correct_ext'[simplified ctx_def rbt_del_ad_correct]

method pok_solver = (simp?, (subst ptr_of_key_simps | (auto simp: ptr_of_key_simps)[])+)[]

lemma delete_opt_ext_correct:
  "
  llvm_htriple
  (\<upharpoonleft>key_assn k ki ** rbt_assn_ext t {} ti ** \<up>(is_rbt_node (rbt_of t)))
  (delete_opt ki ti)
  (\<lambda>res_ti. EXS res_t.
    rbt_assn_ext res_t {} res_ti **
    \<upharpoonleft>key_assn k ki **
    \<up>(rbt_of res_t = (rbt_delete k (rbt_of t))) **
    ctx(rbt_sorted (rbt_of res_t)) **
    \<up>((ptr_of_key t ti)(k := None) \<subseteq>\<^sub>m ptr_of_key res_t res_ti) **
    \<up>((value_of_key t)(k := None) \<subseteq>\<^sub>m value_of_key res_t)
  )
"
  unfolding delete_opt_def rbt_delete_def paint_def
  supply 
    del_opt_ext_correct[vcg_rules] 
    load_rbt_non_null[vcg_rules] 
    sep_context_pureI[isep_red]

  apply vcg
  subgoal
    apply vcg_compat
    apply (sepEwith auto) 

(*rbt_of =*)
     apply (cases "rbt_del k (rbt_of t)") 
      apply simp_all

    apply sep
     apply (metis rbt_sorted.simps(2)) 

    apply (sepwith \<open>solves pok_solver | solves vok_solver\<close>) 
    done
  done

lemmas [vcg_rules] = delete_opt_ext_correct[simplified ctx_def] 

end

end