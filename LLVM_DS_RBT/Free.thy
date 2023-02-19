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
      case n of (RBT_NODE _ l k v r) \<Rightarrow> do {
        key_free k;
        value_free v;
        ll_free n_p;
        free l;
        free (rbt_node.right n)
      }
    }
  }
"
text_raw \<open>}%endsnip\<close>

lemmas [llvm_code] = free.simps

lemma free_correct [vcg_rules]:
  "
    llvm_htriple
    (rbt_assn t ti)
    (free ti)
    (\<lambda>_. \<box>)
  "
proof(induction t arbitrary: ti)
  case Empty
  then show ?case
    apply (subst free.simps)
    apply vcg
    done
next
  case (Branch c l k v r)

  note [vcg_rules] = Branch.IH
  
  then show ?case
    apply (subst free.simps)
    apply vcg
    done
qed

end

end