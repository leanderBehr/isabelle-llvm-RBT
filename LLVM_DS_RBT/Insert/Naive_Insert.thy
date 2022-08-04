theory Naive_Insert
  imports 
    "../Setup"
    "../Separation_Logic_Solver/Methods"
    "../Bool_Assn_Setup"
begin


fun rbt_naive_insert ::
  "('k::linorder, 'v) rbt \<Rightarrow> 'k \<Rightarrow> 'v \<Rightarrow> ('k, 'v) rbt"
  where
    "rbt_naive_insert rbt.Empty k v = Branch color.R rbt.Empty k v rbt.Empty"
  | "rbt_naive_insert (rbt.Branch col lhs k' v' rhs) k v = (
    if k < k'
    then rbt.Branch col (rbt_naive_insert lhs k v) k' v' rhs
    else (
      if k > k'
      then rbt.Branch col lhs k' v' (rbt_naive_insert rhs k v)
      else rbt.Branch col lhs k' v' rhs
    )
)"


context rbt_impl
begin
interpretation rbt_impl_deps .


partial_function (M) naive_insert :: "
('ki, 'vi) rbti \<Rightarrow> 'ki \<Rightarrow> 'vi \<Rightarrow> ('ki, 'vi) rbti llM
" where " 
naive_insert tree_p k v = do {
  if tree_p = null
  then do {
    new_node \<leftarrow> ll_balloc;
    ll_store (RBT_NODE 0 null k v null) new_node;
    return new_node
  }
  else do {
    tree \<leftarrow> ll_load tree_p;
    k_old \<leftarrow> return rbt_node.key tree;

    k_lt \<leftarrow> lt_impl k k_old;
    if k_lt = 1
    then do {
      new_lhs \<leftarrow> naive_insert (rbt_node.left tree) k v;
      new_tree \<leftarrow> ll_insert_value tree new_lhs 1;
      ll_store new_tree tree_p;
      return tree_p
    }
    else do {
      k_gt \<leftarrow> lt_impl k_old k;
      if k_gt = 1
      then do {
        new_rhs \<leftarrow> naive_insert (rbt_node.right tree) k v;       
        new_tree \<leftarrow> ll_insert_value tree new_rhs 4;
        ll_store new_tree tree_p;
        return tree_p
      }
      else do {
         key_delete k;
         value_delete v;
         return tree_p
      }
    }
  }
}"


lemma naive_insert_correct [vcg_rules]:
  "llvm_htriple
  (\<upharpoonleft>rbt_assn tree treei ** \<upharpoonleft>key_assn k\<^sub>n ki ** \<upharpoonleft>value_assn v vi)
  (naive_insert treei ki vi)
  (\<lambda>r. \<upharpoonleft>rbt_assn (rbt_naive_insert tree k\<^sub>n v) r)"
proof(induction tree arbitrary: treei)
  case Empty

  note [simp] = rbt_assn_branch_def

  from Empty show ?case
    apply (subst naive_insert.simps)
    apply vcg
    done
next
  case (Branch col lhs k\<^sub>t v rhs)

  note [vcg_rules] = Branch.IH
  note [simp] = rbt_assn_branch_def

  show ?case
    apply (subst naive_insert.simps)
    apply vcg
    done
qed


lemmas [llvm_code] = naive_insert.simps


lemma naive_insert_correct_mem [vcg_rules]:
  "k\<^sub>n \<notin> set (RBT_Impl.keys tree) \<Longrightarrow>
  llvm_htriple
  (rbt_assn_mem tree ptrs treei ** \<upharpoonleft>key_assn k\<^sub>n ki ** \<upharpoonleft>value_assn v vi)
  (naive_insert treei ki vi)
  (\<lambda>r. EXS n. rbt_assn_mem (rbt_naive_insert tree k\<^sub>n v) (ptrs(k\<^sub>n := Some n)) r)"
proof(induction tree arbitrary: treei)
  case Empty
  note naive_insert_correct[vcg_rules del]
  then show ?case 
    apply (subst naive_insert.simps)
    apply vcg
    done
next
  case (Branch c lhs k v rhs)

  note naive_insert_correct[vcg_rules del]
  note Branch(1-2)[vcg_rules]

  from Branch(3) show ?case
    apply (subst naive_insert.simps)
    apply vcg
    subgoal (*k\<^sub>n < k*)
      apply (simp add: fun_upd_def)
      apply vcg_compat
      apply (isep_solver_keep isep_intro: ptrs_upd_rbt_assn_mem_sepI)
        apply simp_all
      done
    subgoal (*k\<^sub>n \<ge> k*)
      apply vcg
      subgoal (*k\<^sub>n > k*)
        apply (simp add: fun_upd_def)
        apply vcg_compat
        apply (isep_solver_keep isep_intro: ptrs_upd_rbt_assn_mem_sepI)
          apply simp_all
        done
      subgoal (*k\<^sub>n = k -- contradiction*) by vcg
      done
    done
qed


end


end