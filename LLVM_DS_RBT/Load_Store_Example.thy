theory Load_Store_Example
  imports 
    Extended_Assertion
    Utilities_Extended_Assertion
    Assertion_Tree_Lookup
    Lookup_Extended_Assertion
    "Insert/Alloc_Optimized/Insert_Opt_Ext"
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
    return t'
  }
"

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
  (\<lambda>res_ti. EXS res_t res_vi res_v.
    rbt_assn_ext res_t {} res_ti **
    \<upharpoonleft>value_assn res_v res_vi ** \<upharpoonleft>key_assn k1 k1i **
    \<up>(rbt_of res_t = (rbt_update (rbt_insert k2 v2 (rbt_of t)) k1 v1))
  )
  "
  unfolding example_def
  supply map_leD[elim]
  apply vcg
     apply auto[3]
  apply vcg
  apply vcg_compat
  apply (isep_drule drule: value_ex_join_ent, (auto)[3])
  apply simp
  apply sepE
  done

method is_contains = match conclusion in "_ \<in> _" \<Rightarrow> succeed

method test_filter = then_else is_contains \<open>solves auto\<close> succeed


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
  (\<lambda>res_ti. EXS res_t res_vi res_v.
    rbt_assn_ext res_t {} res_ti **
    \<upharpoonleft>value_assn res_v res_vi ** \<upharpoonleft>key_assn k1 k1i **
    \<up>(rbt_of res_t = (rbt_update (rbt_insert k2 v2 (rbt_of t)) k1 v1))
  )
  "
  unfolding example_def
  supply map_leD[elim]
  apply vcg
     apply auto[3]
  apply vcg
  apply vcg_compat
  apply (sepEwith \<open>test_filter, auto?\<close> isep_dest: value_ex_join_ent)
  apply simp
  apply (sepEwith \<open>test_filter, auto?\<close> isep_dest: value_ex_join_ent)
  done

end

end