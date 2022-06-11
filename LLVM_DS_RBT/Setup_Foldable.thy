theory Setup_Foldable
  imports Setup
begin


datatype ('kk, 'vv) Conc = U | B "('kk, 'vv) rbt_node"


datatype ('kk, 'vv) RbtA = RBTA "('kk, 'vv) rbti" "('kk, 'vv) Conc"


context rbt_impl
begin
interpretation llvm_prim_ctrl_setup .
interpretation llvm_prim_arith_setup .
interpretation llvm_prim_setup .


fun rbt_assn_m' ::
  "('k, 'v) rbt \<Rightarrow>
  ('ki::llvm_rep, 'v::llvm_rep) RbtA \<Rightarrow>
  ll_assn" where
  "rbt_assn_m' rbt.Empty (RBTA p X) = \<up>(p = null)"
| "rbt_assn_m' (rbt.Branch col lhs k v rhs) (RBTA p U) = 
  (  
    EXS coli lhsi ki vi rhsi. 
          \<upharpoonleft>ll_bpto (RBT_NODE coli lhsi ki vi rhsi) p **
          \<upharpoonleft>color_assn col coli **
          \<upharpoonleft>rbt_assn lhs lhsi **
          \<upharpoonleft>key_assn k ki **
          \<up>(vi=v) **
          \<upharpoonleft>rbt_assn rhs rhsi
  )"
| "rbt_assn_m' (rbt.Branch col lhs k v rhs) (RBTA p (B (RBT_NODE coli lhsi ki vi rhsi))) =
  (    
    \<upharpoonleft>ll_bpto (RBT_NODE coli lhsi ki vi rhsi) p **
    \<upharpoonleft>color_assn col coli **
    \<upharpoonleft>rbt_assn lhs lhsi **
    \<upharpoonleft>key_assn k ki **
    \<up>(vi=v) **
    \<upharpoonleft>rbt_assn rhs rhsi
  )  
"


definition "rbt_assn_m = mk_assn rbt_assn_m'"


lemma rbt_assn_m_tag_def: "\<upharpoonleft>rbt_assn_m = rbt_assn_m'"
  unfolding rbt_assn_m_def dr_assn_prefix_def mk_assn_def
  by simp


lemma close_rbt_assn_m_entails:
  "
  (
    \<upharpoonleft>ll_bpto (RBT_NODE 0 lhsi ki vi rhsi) ti **
    \<upharpoonleft>rbt_assn lhs lhsi **
    \<upharpoonleft>key_assn k ki **
    \<upharpoonleft>rbt_assn rhs rhsi
  ) \<turnstile>
  (\<upharpoonleft>rbt_assn_m (rbt.Branch color.R lhs k vi rhs) (RBTA ti (B (RBT_NODE 0 lhsi ki vi rhsi))))
  "
  unfolding rbt_assn_m_tag_def
  by (simp add: sep_algebra_simps)


end


end