theory Lookup
  imports Setup OptionI
begin


context rbt_impl
begin
interpretation llvm_prim_ctrl_setup .
interpretation llvm_prim_arith_setup .
interpretation llvm_prim_setup .

partial_function (M) contains :: "
  ('ki, 'v::llvm_rep) rbti \<Rightarrow> 'ki \<Rightarrow> 1 word llM
" where "
  contains rbtp k = do {
    if rbtp = null
    then return 0
    else do {
      node \<leftarrow> ll_load rbtp;
      go_left \<leftarrow> lt_impl k (rbt_node.key node);
      if go_left = 1
      then contains (rbt_node.left node) k
      else do {
        go_right \<leftarrow> lt_impl (rbt_node.key node) k;
        if go_right = 1
        then contains (rbt_node.right node) k
        else return 1
      }
    }
  }"


definition "rbt_contains t k \<equiv> rbt_lookup t k \<noteq> None" 


lemma contains_correct:
  "llvm_htriple
  (\<upharpoonleft>rbt_assn t ti ** \<upharpoonleft>key_assn k ki)
  (contains ti ki)
  (\<lambda>ri. \<up>(ri = fb (rbt_contains t k)) ** \<upharpoonleft>rbt_assn t ti ** \<upharpoonleft>key_assn k ki)"
proof(induction t arbitrary: ti)
  case Empty
  then show ?case
    unfolding rbt_contains_def
    apply (subst contains.simps)
    apply vcg_monadify
    apply vcg
    done
next
  case (Branch c lhs key val rhs)
  note [vcg_rules] = Branch.IH
  note [simp] = rbt_contains_def rbt_assn_branch_def

  show ?case
    apply (subst contains.simps)
    apply vcg_monadify
    apply vcg
    done
qed


abbreviation "alloc_opt_of v \<equiv> do {
    opt \<leftarrow> ll_balloc;
    ll_store (OPTION_I v 1) opt;
    return opt
}"


abbreviation "alloc_opt_none \<equiv> do {
    opt \<leftarrow> ll_balloc;
    ll_store (OPTION_I init 0) opt;
    return opt
}"




partial_function (M) lookup :: 
  "('ki, 'v::llvm_rep) rbti \<Rightarrow> 'ki \<Rightarrow> (('v option_i) ptr) llM" where
  "lookup node_p k = do {
    if node_p = null
    then alloc_opt_none
    else do {
      node \<leftarrow> ll_load node_p;
      k_old \<leftarrow> return rbt_node.key node;
      k_lt \<leftarrow> lt_impl k k_old;
      if k_lt = 1
      then lookup (rbt_node.left node) k
      else do {
        k_gt \<leftarrow> lt_impl k_old k;
        if k_gt = 1
        then lookup (rbt_node.right node) k
        else alloc_opt_of (rbt_node.val node)
      }
    }
  }"


lemmas [llvm_code] = lookup.simps


interpretation v_option: option_impl 
  "mk_assn (\<lambda> v vi. \<up>(v = vi))"
  .


abbreviation "option_assn \<equiv> v_option.option_assn"


lemma lookup_correct:
  "llvm_htriple
  (\<upharpoonleft>rbt_assn t ti ** \<upharpoonleft>key_assn k ki)
  (lookup ti ki)
  (\<lambda>ri. (EXS opt.
            \<upharpoonleft>ll_bpto opt ri **
            \<upharpoonleft>option_assn (rbt_lookup t k) opt **
            \<upharpoonleft>rbt_assn t ti **
            \<upharpoonleft>key_assn k ki))"
proof(induction t arbitrary: ti)
  case Empty
  then show ?case
    apply (subst lookup.simps)
    apply vcg
    done
next
  case (Branch x1 t1 x3 x4 t2)

  note [vcg_rules] = Branch.IH
  note [simp] = rbt_assn_branch_def

  show ?case
    apply (subst lookup.simps)
    apply vcg_monadify
    apply vcg
    apply (auto split: if_split)
    apply vcg
    done
qed


end


end