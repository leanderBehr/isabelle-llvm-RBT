theory Map_Interface
  imports 
    "Lookup/Lookup"
    "Insert/Alloc_Optimized/Insert_Opt"
    "Delete/Alloc_Optimized/Delete_Opt"
    "Separation_Logic_Solver/Methods"
begin


locale rbt_map = rbt_impl keyabs_t key_t valueabs_t value_t
  for
    keyabs_t :: "'k :: linorder itself" and
    key_t :: "'ki :: llvm_rep itself" and
    valueabs_t :: "'v itself" and
    value_t :: "'vi :: llvm_rep itself"
    +
  fixes value_copy :: "'vi \<Rightarrow> 'vi llM"
  assumes
    value_copy_rule [vcg_rules]:  
    "
      llvm_htriple
      (\<upharpoonleft>value_assn v vi)
      (value_copy vi)
      (\<lambda>r. \<upharpoonleft>value_assn v vi ** \<upharpoonleft>value_assn v r)
    "
begin


fun rbt_map_assn :: "('k \<rightharpoonup> 'v) \<Rightarrow> ('ki, 'vi) rbti \<Rightarrow> ll_assn" where
  "rbt_map_assn m ti = (EXS t. rbt_assn_full t ti ** \<up>(rbt_lookup t = m))"


lemma empty_map_rule:
"
  llvm_htriple
  \<box>
  empty
  (\<lambda>r. rbt_map_assn Map.empty r)
" by vcg


lemma free_map_rule:
  "
    llvm_htriple
    (rbt_map_assn m ti)
    (free ti)
    (\<lambda>_. \<box>)
  " by vcg 


lemma lookup_map_rule:
  "
    llvm_htriple
    (rbt_map_assn m ti ** \<upharpoonleft>key_assn k ki)
    (lookup value_copy ki ti)
    (\<lambda>opt. \<upharpoonleft>value_option_assn (m k) opt ** rbt_map_assn m ti ** \<upharpoonleft>key_assn k ki)
  " by vcg


lemma insert_map_rule:
  "
    llvm_htriple
    (rbt_map_assn m ti ** \<upharpoonleft>key_assn k ki ** \<upharpoonleft>value_assn v vi)
    (insert ki vi ti)
    (\<lambda>r. rbt_map_assn (m(k \<mapsto> v)) r)
  "
    apply vcg
    apply vcg_compat
    apply (sepEwith simp)
    apply (simp_all add: rbt_lookup_rbt_insert)
    done

lemma insert_opt_map_rule:
  "
    llvm_htriple
    (rbt_map_assn m ti ** \<upharpoonleft>key_assn k ki ** \<upharpoonleft>value_assn v vi)
    (insert_opt ki vi ti)
    (\<lambda>r. rbt_map_assn (m(k \<mapsto> v)) r)
  "
    apply vcg
    apply vcg_compat
    apply (sepEwith simp)
    apply (simp_all add: rbt_lookup_rbt_insert)
    done


lemma delete_map_rule:
  "
    llvm_htriple
    (rbt_map_assn m ti ** \<upharpoonleft>key_assn k ki)
    (delete ki ti)
    (\<lambda>r. rbt_map_assn (m |` (-{k})) r ** \<upharpoonleft>key_assn k ki)
  "
    apply vcg
    apply vcg_compat
    apply (sepEwith simp)
    apply (simp_all add: rbt_lookup_rbt_delete)
  done


lemma delete_opt_map_rule:
  "
    llvm_htriple
    (rbt_map_assn m ti ** \<upharpoonleft>key_assn k ki)
    (delete_opt ki ti)
    (\<lambda>r. rbt_map_assn (m |` (-{k})) r ** \<upharpoonleft>key_assn k ki)
  "
  supply is_rbt_def[simp]
  apply vcg
  apply vcg_compat
  apply (sepE | find_sep)+   
  using is_rbt_def rbt_delete_is_rbt apply blast
  apply (simp add: rbt_lookup_rbt_delete)
  done


lemmas rbt_map_rules[vcg_rules] = 
  empty_map_rule
  free_map_rule
  lookup_map_rule
  insert_map_rule
  delete_map_rule
  insert_opt_map_rule
  delete_opt_map_rule

lemmas rbt_tree_rules[vcg_rules del] =
  empty_correct
  free_correct
  lookup_correct
  insert_correct
  delete_correct
  insert_opt_correct
  delete_opt_correct

lemma pure_part_exE:
    assumes "pure_part (\<lambda>s. \<exists>x. P x s)"
    obtains x where "pure_part (P x)"
  using assms unfolding pure_part_def by blast

lemma rbt_map_finite: 
  "pure_part(rbt_map_assn m ti) \<Longrightarrow> finite (dom m)"
  by (auto elim!: pure_part_exE pure_part_split_conjE)
  

declare rbt_map_assn.simps[simp del]


end


end