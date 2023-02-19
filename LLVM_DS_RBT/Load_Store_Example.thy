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
    p \<leftarrow> lookup_ptr t k1;
    t' \<leftarrow> insert_opt k2 v2 t;
    vp \<leftarrow> load p;
    store p v1;
    return (t', vp)
  }
"

method is_contains = match conclusion in "value_of_key _ _ _ = _" \<Rightarrow> succeed
method join_filter = then_else is_contains \<open>solves auto\<close> succeed

lemma example_correct:
  " rbt_sorted (rbt_of t) \<Longrightarrow> rbt_lookup (rbt_of t) k1 \<noteq> None \<Longrightarrow>
  llvm_htriple
  (
    rbt_assn_ext t {} ti **
    \<upharpoonleft>key_assn k1 k1i **
    \<upharpoonleft>key_assn k2 k2i **
    \<upharpoonleft>value_assn v1 v1i **
    \<upharpoonleft>value_assn v2 v2i
  )
  (example ti k1i v1i k2i v2i)
  (\<lambda>(res_ti, res_vi). EXS res_t res_v.
    rbt_assn_ext res_t {} res_ti **
    \<upharpoonleft>value_assn res_v res_vi ** \<upharpoonleft>key_assn k1 k1i **
    \<up>(rbt_of res_t = (rbt_update (rbt_insert k2 v2 (rbt_of t)) k1 v1))
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
  " rbt_sorted (rbt_of t) \<Longrightarrow> rbt_lookup (rbt_of t) k1 \<noteq> None \<Longrightarrow>
  llvm_htriple
  (
    rbt_assn_ext t {} ti **
    \<upharpoonleft>key_assn k1 k1i **
    \<upharpoonleft>key_assn k2 k2i **
    \<upharpoonleft>value_assn v1 v1i **
    \<upharpoonleft>value_assn v2 v2i
  )
  (example ti k1i v1i k2i v2i)
  (\<lambda>(res_ti, res_vi). EXS res_t res_v.
    rbt_assn_ext res_t {} res_ti **
    \<upharpoonleft>value_assn (the (rbt_lookup (rbt_insert k2 v2 (rbt_of t)) k1)) res_vi ** \<upharpoonleft>key_assn k1 k1i **
    \<up>(rbt_of res_t = (rbt_update (rbt_insert k2 v2 (rbt_of t)) k1 v1))
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

declare insert_opt_correct_ext'[vcg_rules del]

definition "example2 t k1 v1 k2 v2 k3 f \<equiv>
  do {
    p \<leftarrow> lookup_ptr t k1;
    t' \<leftarrow> insert_opt k2 v2 t;
    vp \<leftarrow> load p;
    t'' \<leftarrow> delete_opt k3 t';
    vp' \<leftarrow> f vp;
    store p v1;
    return (t'', vp')
  }
"

lemma example2_correct:
  assumes
    [vcg_rules]: "\<And>v vi. llvm_htriple (\<upharpoonleft>value_assn v vi) (fi vi) (\<lambda>res_v. \<upharpoonleft>value_assn (f v) res_v)"
  shows
  "is_rbt (rbt_of t) \<Longrightarrow> rbt_lookup (rbt_of t) k1 \<noteq> None \<Longrightarrow> k1 \<noteq> k3 \<Longrightarrow>
  llvm_htriple
  (
    rbt_assn_ext t {} ti **
    \<upharpoonleft>key_assn k1 k1i **
    \<upharpoonleft>key_assn k2 k2i **
    \<upharpoonleft>key_assn k3 k3i **
    \<upharpoonleft>value_assn v1 v1i **
    \<upharpoonleft>value_assn v2 v2i
  )
  (example2 ti k1i v1i k2i v2i k3i fi)
  (\<lambda>(res_ti, res_vi). EXS res_t res_v.
    rbt_assn_ext res_t {} res_ti **
    \<upharpoonleft>key_assn k1 k1i ** \<upharpoonleft>key_assn k3 k3i **
    \<upharpoonleft>value_assn (f (the (rbt_lookup (rbt_delete k3 (rbt_insert k2 v2 (rbt_of t))) k1))) res_vi **
    \<up>(rbt_of res_t = (rbt_update (rbt_delete k3 (rbt_insert k2 v2 (rbt_of t))) k1 v1))
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

  apply vcg_compat
  apply (sepEwith \<open>join_filter, auto?\<close> isep_dest: value_ex_join_ent)
  apply simp 
  apply sep
  done

end

end