theory LLVM_DS_RBT
  imports
  "LLVM_DS_RBT/Delete"
  "LLVM_DS_RBT/Balance"
  "LLVM_DS_RBT/Export"
  "LLVM_DS_RBT/Lookup"
begin                                     


context rbt_impl
begin
interpretation llvm_prim_ctrl_setup .
interpretation llvm_prim_arith_setup .
interpretation llvm_prim_setup .


partial_function (M) dummy_insert1 :: "
('ki, 'val::llvm_rep) rbti \<Rightarrow> 'ki \<Rightarrow> 'val \<Rightarrow> ('ki, 'val) rbti llM
" where " 
dummy_insert1 tree k v = do {
  new_node \<leftarrow> ll_balloc;
  ll_store (RBT_NODE 0 null k v null) new_node;
  delete tree;
  return new_node
}"


lemma dummy_insert1_correct:
  "llvm_htriple
  (\<upharpoonleft>rbt_assn tree treei ** \<upharpoonleft>key_assn k ki)
  (dummy_insert1 treei ki v)
  (\<lambda>ri. \<upharpoonleft>rbt_assn (rbt.Branch color.R rbt.Empty k v rbt.Empty) ri)"
proof(cases tree)
  case Empty

  note [simp] = rbt_assn_branch_def

  then show ?thesis
    apply (subst dummy_insert1.simps)
    apply vcg_monadify
    apply vcg
    done
next
  case (Branch col lhs k v rhs)

  note [vcg_rules] = delete_rule (*Why?*)
  note [simp] = rbt_assn_branch_def
 
  then show ?thesis
    apply (subst dummy_insert1.simps)
    apply vcg_monadify
    apply vcg
    done
qed


partial_function (M) dummy_insert2 :: "
('ki, 'val::llvm_rep) rbti \<Rightarrow> 'ki \<Rightarrow> 'val \<Rightarrow> ('ki, 'val) rbti llM
" where " 
dummy_insert2 tree k v = do {
  new_node \<leftarrow> ll_balloc;
  ll_store (RBT_NODE 0 null k v null) new_node;
  if tree = null
  then return new_node
  else do {
    delete tree;
    return new_node
  }
}"


ML_val \<open>Basic_VCG.print_solvers @{context}\<close>


lemma dummy_insert2_correct:
  "llvm_htriple
  (\<upharpoonleft>rbt_assn tree treei ** \<upharpoonleft>key_assn k ki)
  (dummy_insert2 treei ki v)
  (\<lambda>ri. \<upharpoonleft>rbt_assn (rbt.Branch color.R rbt.Empty k v rbt.Empty) ri)"
proof(cases tree)
  case Empty

  note [simp] = rbt_assn_branch_def

  then show ?thesis
    apply (subst dummy_insert2.simps)
    apply vcg_monadify
    apply vcg
    done
next
  case (Branch col lhs k v rhs)

  note [simp] = rbt_assn_branch_def[abs_def]

  then show ?thesis
    apply (subst dummy_insert2.simps)
    apply vcg_monadify
    apply vcg
    done
qed


end


end