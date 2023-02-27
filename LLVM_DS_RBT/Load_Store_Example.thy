theory Load_Store_Example
  imports 
    Extended_Assertion
    Utilities_Ext
    Assertion_Tree_Lookup
    Lookup_Ext
    "Insert/Alloc_Optimized/Insert_Opt_Ext"
    "Delete/Alloc_Optimized/Delete_Opt_Ext"
    Extended_Assertion_Exceptions
    Load_Store
begin

context rbt_impl
begin
interpretation rbt_impl_deps .

definition "example t k1 v1 k2 v2 \<equiv>
  do {
    p \<leftarrow> lookup_ptr k1 t;
    t' \<leftarrow> insert_opt k2 v2 t;
    vp \<leftarrow> load p;
    store p v1;
    return (t', vp)
  }
"

method is_contains = match conclusion in "value_of_key _ _  = _" \<Rightarrow> succeed
method join_filter = then_else is_contains \<open>solves auto\<close> succeed

lemma example_correct:
  "is_rbt (rbt_of t) \<Longrightarrow> rbt_lookup (rbt_of t) k1 \<noteq> None \<Longrightarrow>
  llvm_htriple
  (
    rbt_assn_ext t {} ti **
    \<upharpoonleft>key_assn k1 k1i **
    \<upharpoonleft>key_assn k2 k2i **
    \<upharpoonleft>value_assn v1 v1i **
    \<upharpoonleft>value_assn v2 v2i
  )
  (example ti k1i v1i k2i v2i)
  (\<lambda>(ti_res, vi_res). EXS t_res v_res.
    rbt_assn_ext t_res {} ti_res **
    \<upharpoonleft>value_assn v_res vi_res ** \<upharpoonleft>key_assn k1 k1i **
    \<up>(rbt_of t_res = (rbt_update k1 v1 (rbt_insert k2 v2 (rbt_of t))))
  )
  "
  unfolding example_def
  supply map_leD[elim]
  apply vcg
  apply vcg_compat
  apply (isep_drule drule: value_ex_join_ent; join_filter) 
    apply simp_all
  apply sepE
  done

lemma example_correct_2:
  " is_rbt (rbt_of t) \<Longrightarrow> rbt_lookup (rbt_of t) k1 \<noteq> None \<Longrightarrow>
  llvm_htriple
  (
    rbt_assn_ext t {} ti **
    \<upharpoonleft>key_assn k1 k1i **
    \<upharpoonleft>key_assn k2 k2i **
    \<upharpoonleft>value_assn v1 v1i **
    \<upharpoonleft>value_assn v2 v2i
  )
  (example ti k1i v1i k2i v2i)
  (\<lambda>(ti_res, vi_res). EXS t_res v_res.
    rbt_assn_ext t_res {} ti_res **
    \<upharpoonleft>value_assn (the (rbt_lookup (rbt_insert k2 v2 (rbt_of t)) k1)) vi_res ** \<upharpoonleft>key_assn k1 k1i **
    \<up>(rbt_of t_res = (rbt_update k1 v1 (rbt_insert k2 v2 (rbt_of t))))
  )
  "
  unfolding example_def
  supply map_leD[elim]
  apply vcg
  apply vcg_compat
  apply (sepEwith \<open>join_filter, auto?\<close> isep_dest: value_ex_join_ent)
  apply simp
  apply sep
  done 



definition "example2 t k1 k2 k3 v1 v2 f1 f2 \<equiv>
  do {
    pk1 \<leftarrow> lookup_ptr k1 t;
    t' \<leftarrow> insert_opt k2 v2 t;
    vk1 \<leftarrow> load pk1;
    t'' \<leftarrow> delete_opt k3 t';
    vk1' \<leftarrow> f1 vk1;
    f2 v2;
    store pk1 v1;
    return (t'', vk1')
  }
"

lemma rbt_assn_ext_diff_ex_sets [fri_red_rules]:
  "ex1 = ex2 \<Longrightarrow> is_sep_red \<box> \<box> (rbt_assn_ext t ex1 ti) (rbt_assn_ext t ex2 ti)"
  apply (rule is_sep_redI)
  apply simp
  subgoal premises prems
    apply (sep isep_dest: prems(2))
    done
  done


lemma rbt_update_comp_comm: 
  "k1 \<noteq> k2 \<Longrightarrow> rbt_update k2 v2 (rbt_update k1 v1 t) = rbt_update k1 v1 (rbt_update k2 v2 t)" 
  apply (induction t) by auto


lemma example2_correct:
  assumes
    [vcg_rules]: "\<And>v vi. llvm_htriple (\<upharpoonleft>value_assn v vi) (f1i vi) (\<lambda>v_res. \<upharpoonleft>value_assn (f1 v) v_res)" and
    [vcg_rules]: "\<And>v vi. llvm_htriple (\<upharpoonleft>value_assn v vi) (f2i vi) (\<lambda>_. \<upharpoonleft>value_assn (f2 v) vi)"
  shows
    "\<lbrakk>is_rbt (rbt_of t); rbt_lookup (rbt_of t) k1 \<noteq> None; k1 \<noteq> k2; k1 \<noteq> k3; k2 \<noteq> k3\<rbrakk> \<Longrightarrow>
  llvm_htriple
  (
    rbt_assn_ext t {} ti **
    \<upharpoonleft>key_assn k1 k1i **
    \<upharpoonleft>key_assn k2 k2i **
    \<upharpoonleft>key_assn k3 k3i **
    \<upharpoonleft>value_assn v1 v1i **
    \<upharpoonleft>value_assn v2 v2i
  )
  (example2 ti k1i k2i k3i v1i v2i f1i f2i)
  (\<lambda>(ti_res, vi_res). EXS t_res v_res.
    rbt_assn_ext t_res {} ti_res **
    \<upharpoonleft>key_assn k1 k1i ** \<upharpoonleft>key_assn k3 k3i **
    \<upharpoonleft>value_assn (f1 (the (rbt_lookup (rbt_of t) k1))) vi_res **
    \<up>(rbt_of t_res = (rbt_update k2 (f2 v2) (rbt_update  k1 v1 (rbt_delete k3 (rbt_insert k2 v2 (rbt_of t))))))
  )
  "
  unfolding example2_def
  supply
    map_leD[elim!]
    is_rbt_def[simp]
  supply value_ex_split_red[fri_red_rules]
  apply vcg
  apply vcg_rl

   apply vcg_compat
   apply (sepwith auto) 

  apply vcg_solve
  apply vcg
  apply vcg_rl

   apply vcg_compat
   apply (sepwith \<open>solves auto\<close>)

  term "inv1"
  apply vcg_solve
  apply vcg


  apply vcg_compat
  subgoal 
    apply (sepEwith \<open>solves auto\<close> isep_dest: value_ex_join_ent) 

    apply sep 

    apply (simp_all add: rbt_update_comp_comm rbt_lookup_delete inv_12_def rbt_lookup_rbt_insert)

    subgoal premises
      apply sep
      done
    done
  done

end

end