theory Free
  imports Setup
begin

context rbt_impl
begin
interpretation rbt_impl_deps .


partial_function (M) free :: "
  ('ki, 'vi::llvm_rep) rbti \<Rightarrow> unit llM 
" where "
  free tree_p = do {
    if tree_p = null
    then return ()
    else do {
      tree \<leftarrow> ll_load tree_p;
      key_delete (rbt_node.key tree);
      value_delete (rbt_node.val tree);
      ll_free tree_p;
      free (rbt_node.left tree);
      free (rbt_node.right tree)
    }
  }
"


lemma free_correct [vcg_rules]: "
  llvm_htriple
  (rbt_assn tree treei)
  (free treei)
  (\<lambda>_. \<box>)
"
proof(induction tree arbitrary: treei)
  case Empty
  then show ?case
    apply (subst free.simps)
    apply vcg
    done
next
  case (Branch col lhs k v rhs)

  note [vcg_rules] = Branch.IH
  
  then show ?case
    apply (subst free.simps)
    apply vcg
    done
qed


lemmas [llvm_code] = free.simps


end


end