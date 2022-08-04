theory Map_Interface
  imports 
    "Lookup/Lookup"
    "Insert/Insert"
    "Delete/Delete"
    "Separation_Logic_Solver/Methods"
    "HOL-Library.RBT_Mapping"
begin


locale rbt_map = rbt_impl keyabs_t key_t valueabs_t value_t
  for
    keyabs_t :: "'k :: linorder itself" and
    key_t :: "'ki :: llvm_rep itself" and
    valueabs_t :: "'v itself" and
    value_t :: "'vi :: llvm_rep itself"
begin


fun rbt_map_assn :: "('k \<rightharpoonup> 'v) \<Rightarrow> ('ki, 'vi) rbti \<Rightarrow> ll_assn" where
  "rbt_map_assn m ti = (EXS t. \<upharpoonleft>rbt_assn t ti ** \<up>(rbt_lookup t = m) ** \<up>(is_rbt t))"


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
  (\<lambda>r. \<box>)
" by vcg 
             
               
lemma lookup_map_rule:
"
  llvm_htriple
  (rbt_map_assn m ti ** \<upharpoonleft>key_assn k ki)
  (lookup ti ki)
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
  apply isep_solver
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
  apply isep_solver
  apply (simp_all add: rbt_lookup_rbt_delete)
  done


lemmas rbt_map_rules[vcg_rules] = 
  empty_map_rule
  free_map_rule
  lookup_map_rule
  insert_map_rule
  delete_map_rule


lemmas rbt_tree_rules[vcg_rules del] =
  empty_correct
  free_correct
  lookup_correct
  insert_correct
  delete_correct


lemma rbt_map_finite: 
  "pure_part(rbt_map_assn m ti) \<Longrightarrow> finite (dom m)"
  apply auto
  unfolding pure_part_def
  by (metis (full_types) finite_dom_rbt_lookup pure_partI pure_part_pure_conj_eq pure_part_split_conjE)


declare rbt_map_assn.simps[simp del]


end


end