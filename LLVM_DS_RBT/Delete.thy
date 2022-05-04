theory Delete
  imports Setup
begin

context rbt_impl
begin
interpretation llvm_prim_ctrl_setup .
interpretation llvm_prim_arith_setup .
interpretation llvm_prim_setup .


partial_function (M) delete :: "
  ('ki, 'val::llvm_rep) rbti \<Rightarrow> unit llM 
" where "
  delete tree_p = do {
    if tree_p = null
    then return ()
    else do {
      tree \<leftarrow> ll_load tree_p;
      key_delete (rbt_node.key tree);
      ll_free tree_p;
      delete (rbt_node.left tree);
      delete (rbt_node.right tree)
    }
  }
"


lemma delete_rule [vcg_rules]: "
  llvm_htriple
  (\<upharpoonleft>rbt_assn tree treei)
  (delete treei)
  (\<lambda>_. \<box>)
"
proof(induction tree arbitrary: treei)
  case Empty
  then show ?case
    apply (subst delete.simps)
    apply vcg_monadify
    apply vcg
    done
next
  case (Branch col lhs k v rhs)

  note [vcg_rules] = Branch.IH 
  note [simp] = rbt_assn_branch_def
  
  then show ?case
    apply (subst delete.simps)
    apply vcg_monadify
    apply vcg
    done
qed


end


end