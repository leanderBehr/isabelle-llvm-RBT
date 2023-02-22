theory Insert_Opt_Ext
  imports
    Insert_Opt  
    Balance_Opt_Ext
    "../../Utilities_Ext"
    "../../Assertion_Tree_Lookup"
begin

context rbt_impl
begin

lemma pure_assn_prem_from_prem: "(P1 \<Longrightarrow> P2 \<Longrightarrow> htriple P3 c Q) \<Longrightarrow> htriple (\<up>P1 ** \<up>P2 ** P3) c Q"
  by (metis (mono_tags) htriple_realizable_preI n1 pure_true_conv realizable_extract_pure)

lemma less_key_not_in_value_graph [dest]: "(k, vi) \<in> at_value_graph t ti \<Longrightarrow> (rbt_of t) |\<guillemotleft> k \<Longrightarrow> False"
  apply (induction t arbitrary: ti) by auto

lemma greater_key_not_in_value_graph [dest]: "(k, vi) \<in> at_value_graph t ti \<Longrightarrow> k \<guillemotleft>| (rbt_of t) \<Longrightarrow> False"
  apply (induction t arbitrary: ti) by auto

lemma insert'_opt_correct_ext:
  "
    llvm_htriple
    (rbt_assn_ext t {} ti ** \<upharpoonleft>key_assn k ki ** \<upharpoonleft>value_assn v vi ** \<up>(rbt_sorted (rbt_of t)))
    (insert'_opt ki vi ti)
    (\<lambda>res. EXS res_t. rbt_assn_ext res_t {} res **
      \<up>(rbt_of res_t = (rbt_ins (\<lambda>_ _ v. v)) k v (rbt_of t)) **
      \<up>(rbt_sorted (rbt_of res_t)) **
      \<up>(ptr_of_key t ti \<subseteq>\<^sub>m ptr_of_key res_t res) **
      \<up>(value_of_key res_t res = (value_of_key t ti)(k \<mapsto> vi))
    )
  "
  supply ptr_of_key_subsetD[dest!]
proof (induction k v "rbt_of t" arbitrary: t ti rule: rbt_insert_ad'.induct )
  case (1 k\<^sub>n v\<^sub>n)
  then show ?case
    apply (subst insert'_opt.simps)
    supply load_rbt_non_null[vcg_rules]
    apply vcg
    apply vcg_compat
    apply (sepEwith \<open>vok_filter,auto?\<close>)
    apply simp
    apply (sepwith simp)
    done
next
  case (2 k\<^sub>n v\<^sub>n l k v r)

  have []: 
    "llvm_htriple (\<up>(k\<^sub>n < k \<and> l = rbt_of t) ** rbt_assn_ext t {} ti \<and>* \<upharpoonleft>key_assn k\<^sub>n ki \<and>* \<upharpoonleft>value_assn v\<^sub>n vi \<and>* \<up>rbt_sorted (rbt_of t))
          (insert'_opt ki vi ti)
          (\<lambda>res s.
              \<exists>x. (rbt_assn_ext x {} res \<and>*
                   \<up>(rbt_of x = rbt_ins (\<lambda>_ _ v. v) k\<^sub>n v\<^sub>n (rbt_of t)) \<and>*
                   \<up>rbt_sorted (rbt_of x) \<and>*
                   \<up>(ptr_of_key t ti \<subseteq>\<^sub>m ptr_of_key x res) \<and>*
                   \<up>(value_of_key x res = value_of_key t ti(k\<^sub>n \<mapsto> vi)))
                   s)" for t ti supply 2(1)[vcg_rules] by vcg

  have []:
      "llvm_htriple (\<up>(\<not> k\<^sub>n < k \<and> k < k\<^sub>n \<and> r = rbt_of t) ** rbt_assn_ext t {} ti \<and>* \<upharpoonleft>key_assn k\<^sub>n ki \<and>* \<upharpoonleft>value_assn v\<^sub>n vi \<and>* \<up>rbt_sorted (rbt_of t))
          (insert'_opt ki vi ti)
          (\<lambda>res s.
              \<exists>x. (rbt_assn_ext x {} res \<and>*
                   \<up>(rbt_of x = rbt_ins (\<lambda>_ _ v. v) k\<^sub>n v\<^sub>n (rbt_of t)) \<and>*
                   \<up>rbt_sorted (rbt_of x) \<and>*
                   \<up>(ptr_of_key t ti \<subseteq>\<^sub>m ptr_of_key x res) \<and>*
                   \<up>(value_of_key x res = value_of_key t ti(k\<^sub>n \<mapsto> vi)))
                   s)" for t ti supply 2(2)[vcg_rules] by vcg

  from 2(3) show ?case
    apply (subst insert'_opt.simps)
    unfolding balance_black_def
    supply load_rbt_non_null[vcg_rules]

    supply 
      rbt_greater_trans[intro]
      rbt_less_trans[intro]      
      value_of_key_simps[simp]

    supply 2(1-2)[vcg_rules] 
    apply (vcg;fail) 
    done
next
  case (3 k\<^sub>n v\<^sub>n l k v r)

  note [vcg_rules] = 3(1-2)

  from 3(3) show ?case
    apply (subst insert'_opt.simps)
    unfolding balance_black_def
    supply load_rbt_non_null[vcg_rules] 
    supply 
      rbt_greater_trans[intro]
      rbt_less_trans[intro]      
      value_of_key_simps[simp]
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
      \<up>(ptr_of_key t ti \<subseteq>\<^sub>m ptr_of_key res_t res_ti) **
      \<up>(value_of_key res_t res_ti = (value_of_key t ti)(k \<mapsto> vi))
    )
  "
  unfolding insert_opt_def rbt_insert_def rbt_insert_with_key_def paint_def
  supply insert'_opt_correct_ext[vcg_rules]
  apply vcg
  apply (cases "rbt_ins (\<lambda>_ _ v. v) k v (rbt_of t)")
  subgoal using rbt_ins_non_empty by fast
  apply vcg
  apply (subgoal_tac "rbt_sorted (rbt_of (ATBranch color.B x23 x24 1 li ki vi ri al ar))")
   apply vcg_compat 
   apply (sepEwith \<open>auto dest!: ptr_of_key_subsetD\<close>)
    apply (auto simp add: value_of_key_simps intro: rbt_less_trans rbt_greater_trans)[]  
  apply simp
  using ins_rbt_sorted rbt_of.simps(2) rbt_sorted.simps(2) 
  by metis 
 
  


lemma insert_opt_correct_ext [vcg_rules]:
  "
    llvm_htriple
    (rbt_assn_ext t {} ti ** \<upharpoonleft>key_assn k ki ** \<upharpoonleft>value_assn v vi ** \<up>(is_rbt (rbt_of t)))
    (insert_opt ki vi ti)
    (\<lambda>res_ti. EXS res_t.
      rbt_assn_ext res_t {} res_ti **
      \<up>(rbt_of res_t = rbt_insert k v (rbt_of t)) **
      \<up>(is_rbt (rbt_of res_t)) **
      \<up>(ptr_of_key t ti \<subseteq>\<^sub>m ptr_of_key res_t res_ti) **
      \<up>(value_of_key res_t res_ti = (value_of_key t ti)(k \<mapsto> vi))
    )
  "
  apply vcg
  done

end

end