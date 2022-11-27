theory Free
  imports Setup
begin

context rbt_impl
begin
interpretation rbt_impl_deps .


text_raw \<open>\snip{freedef}{1}{2}{%\<close>
partial_function (M) free :: "
  ('ki, 'vi) rbti \<Rightarrow> unit llM 
" where "
  free n_p = do {
    if n_p = null
    then return ()
    else do {
      n \<leftarrow> ll_load n_p;
      key_delete (rbt_node.key n);
      value_delete (rbt_node.val n);
      ll_free n_p;
      free (rbt_node.left n);
      free (rbt_node.right n)
    }
  }
"
text_raw \<open>}%endsnip\<close>


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