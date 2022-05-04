theory Insert
  imports Delete
begin


context rbt_impl
begin
interpretation llvm_prim_ctrl_setup .
interpretation llvm_prim_arith_setup .
interpretation llvm_prim_setup .


fun rbt_insert ::
  "('key::linorder, 'val) rbt \<Rightarrow> 'key \<Rightarrow> 'val \<Rightarrow> ('key, 'val) rbt"
  where
  "rbt_insert rbt.Empty k v = Branch color.R rbt.Empty k v rbt.Empty"
| "rbt_insert (rbt.Branch col lhs k' v' rhs) k v = (
    if k < k'
    then rbt.Branch col (rbt_insert lhs k v) k' v' rhs
    else (
      if k > k'
      then rbt.Branch col lhs k' v' (rbt_insert rhs k v)
      else rbt.Branch col lhs k' v' rhs
    )
)"

lemma "rbt_insert rbt.Empty (1::nat) 1 = 
    Branch color.R rbt.Empty 1 1 rbt.Empty" by auto


partial_function (M) insert :: "
('ki, 'val::llvm_rep) rbti \<Rightarrow> 'ki \<Rightarrow> 'val \<Rightarrow> ('ki, 'val) rbti llM
" where " 
insert tree_p k v = do {
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
      new_lhs \<leftarrow> insert (rbt_node.left tree) k v;
      new_tree \<leftarrow> ll_insert_value tree new_lhs 1;
      ll_store new_tree tree_p;
      return tree_p
    }
    else do {
      k_gt \<leftarrow> lt_impl k_old k;
      if k_gt = 1
      then do {
        new_rhs \<leftarrow> insert (rbt_node.right tree) k v;       
        new_tree \<leftarrow> ll_insert_value tree new_rhs 4;
        ll_store new_tree tree_p;
        return tree_p
      }
      else do {
         key_delete k;
         return tree_p
      }
    }
  }
}"


lemma insert_correct:
  "llvm_htriple
  (\<upharpoonleft>rbt_assn tree treei ** \<upharpoonleft>key_assn k\<^sub>n ki)
  (insert treei ki v)
  (\<lambda>r. \<upharpoonleft>rbt_assn (rbt_insert tree k\<^sub>n v) r)"
proof(induction tree arbitrary: treei)
  case Empty

  note [simp] = rbt_assn_branch_def

  from Empty show ?case
    apply (subst insert.simps)
    apply vcg
    done
next
  case (Branch col lhs k\<^sub>t v rhs)

  note [vcg_rules] = Branch.IH
  note [simp] = rbt_assn_branch_def
  note [vcg_normalize_simps] = rbt_node_insert_value

  show ?case
    apply (subst insert.simps)
    apply vcg_monadify
    apply vcg
    subgoal 
      apply simp
      apply vcg
      done
    subgoal
      apply vcg
      done
    done
qed


end


end