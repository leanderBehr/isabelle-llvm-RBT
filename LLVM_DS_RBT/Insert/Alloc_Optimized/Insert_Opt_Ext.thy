theory Insert_Opt_Ext
  imports
    Insert_Opt  
    Balance_Opt_Ext
    "../../Utilities_Ext"
    "../../Assertion_Tree_Lookup"
begin

context rbt_impl
begin

lemma insert'_opt_correct_ext:
  "
    llvm_htriple
    (rbt_assn_ext t {} ti ** \<upharpoonleft>key_assn k ki ** \<upharpoonleft>value_assn v vi ** \<up>(rbt_sorted (rbt_of t)))
    (insert'_opt ki vi ti)
    (\<lambda>res. EXS res_t. rbt_assn_ext res_t {} res **
      \<up>(rbt_of res_t = (rbt_ins (\<lambda>_ _ v. v)) k v (rbt_of t)) **
      \<up>(rbt_sorted (rbt_of res_t)) **
      \<up>(ptr_of_key t ti \<subseteq>\<^sub>m ptr_of_key res_t res)
    )
  "
  supply ptr_of_key_subsetD[dest!]
proof (induction k v "rbt_of t" arbitrary: ti t rule: rbt_insert_ad'.induct )
  case (1 k\<^sub>n v\<^sub>n)
  then show ?case
    apply (subst insert'_opt.simps)
    supply load_rbt_non_null[vcg_rules]
    apply vcg
    done
next
  case (2 k\<^sub>n v\<^sub>n l k v r)

  note [vcg_rules] = 2(1-2)

  from 2(3) show ?case
    apply (subst insert'_opt.simps)
    unfolding balance_black_def
    supply load_rbt_non_null[vcg_rules]
    apply (vcg;fail)
    done
next
  case (3 k\<^sub>n v\<^sub>n l k v r)

  note [vcg_rules] = 3(1-2)

  from 3(3) show ?case
    apply (subst insert'_opt.simps)
    unfolding balance_black_def
    supply load_rbt_non_null[vcg_rules] 
    apply (vcg;fail)
    done
qed

lemma insert_opt_correct_ext' [vcg_rules]:
  "
    llvm_htriple
    (rbt_assn_ext t {} ti ** \<upharpoonleft>key_assn k ki ** \<upharpoonleft>value_assn v vi ** \<up>(rbt_sorted (rbt_of t)))
    (insert_opt ki vi ti)
    (\<lambda>res_ti. EXS res_t.
      rbt_assn_ext res_t {} res_ti **
      \<up>(rbt_of res_t = rbt_insert k v (rbt_of t)) **
      \<up>(rbt_sorted (rbt_of res_t)) **
      \<up>(ptr_of_key t ti \<subseteq>\<^sub>m ptr_of_key res_t res_ti)
    )
  "
  unfolding insert_opt_def rbt_insert_def rbt_insert_with_key_def paint_def
  supply insert'_opt_correct_ext[vcg_rules]
  apply vcg_step
  apply vcg_step
  apply vcg_step
  apply vcg_step
  apply vcg_rl
   apply vcg_solve
  apply vcg_solve (*where did \<up>rbt_sorted (rbt_of x) go?*)
  apply vcg
  apply (cases "rbt_ins (\<lambda>_ _ v. v) k v (rbt_of t)")
  subgoal using rbt_ins_non_empty by fast
  apply vcg
  apply (subgoal_tac "rbt_sorted (rbt_of (ATBranch color.B x23 x24 1 li ki vi ri al ar))")
   apply vcg_compat 
   apply (sepE | find_sep)+
      apply simp
      apply sep
  subgoal using ins_rbt_sorted rbt_of.simps(2) rbt_sorted.simps(2) by metis
  subgoal by simp
  subgoal by blast
  subgoal by (auto dest!: ptr_of_key_subsetD)
  done


lemma insert_opt_correct_ext [vcg_rules]:
  "
    llvm_htriple
    (rbt_assn_ext t {} ti ** \<upharpoonleft>key_assn k ki ** \<upharpoonleft>value_assn v vi ** \<up>(is_rbt (rbt_of t)))
    (insert_opt ki vi ti)
    (\<lambda>res_ti. EXS res_t.
      rbt_assn_ext res_t {} res_ti **
      \<up>(rbt_of res_t = rbt_insert k v (rbt_of t)) **
      \<up>(is_rbt (rbt_of res_t)) **
      \<up>(ptr_of_key t ti \<subseteq>\<^sub>m ptr_of_key res_t res_ti)
    )
  "
  apply vcg
  done

end

end