theory Update
  imports Lookup
begin

context rbt_impl
begin
interpretation rbt_impl_deps .


definition update :: "('ki, 'vi) rbti \<Rightarrow> 'ki \<Rightarrow> 'vi \<Rightarrow> unit llM" where
  "update t k v = do { p \<leftarrow> lookup_ptr t k; rbt_ptr_store p v }"


lemma update_correct:
  assumes 
    "k \<in> rbt_key_set t" and 
    "is_rbt t" and
    "k \<notin> ex"
  shows
"
  llvm_htriple
  (rbt_assn_cplx t ptrs ex ti ** \<upharpoonleft>key_assn k ki ** \<upharpoonleft>value_assn v vi)
  (update ti ki vi)
  (\<lambda>_. EXS ptrs'. rbt_assn_cplx (rbt_map_entry k (\<lambda>_. v) t) ptrs' ex ti ** \<upharpoonleft>key_assn k ki)
"
  unfolding update_def
  using assms apply vcg
  apply (simp split: if_splits)
  apply vcg
  done

end


end

