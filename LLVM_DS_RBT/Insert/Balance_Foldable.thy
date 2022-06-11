theory Balance_Foldable
  imports 
    Balance
    "../Setup_Foldable"
begin


context rbt_impl
begin
interpretation llvm_prim_ctrl_setup .
interpretation llvm_prim_arith_setup .
interpretation llvm_prim_setup .


lemma assn_ent_assnm: "\<upharpoonleft>rbt_assn t ti = \<upharpoonleft>rbt_assn_m t (RBTA ti U)"
unfolding rbt_assn_m_tag_def rbt_assn_tag_def
  apply (induction t)
  apply auto
  unfolding rbt_assn_tag_def
  by auto


lemma balance_correct_ :
  "llvm_htriple
  (
    \<upharpoonleft>rbt_assn_m tree_l (RBTA tree_li X) **
    \<upharpoonleft>rbt_assn_m tree_r (RBTA tree_ri Y) **   
    \<upharpoonleft>key_assn k ki
  )
  (balance tree_li ki v tree_ri)
  (\<lambda>ri. \<upharpoonleft>rbt_assn (rbt_balance tree_l k v tree_r) ri) 
  "
  apply (rule htriple_ent_pre)
  sorry


end


end