theory Lookup
  imports 
    "../Setup"
    "../Bool_Assn_Setup"
    "../Utilities"
    OptionI
begin


context rbt_impl
begin
interpretation rbt_impl_deps .


partial_function (M) contains :: "
  ('ki, 'vi) rbti \<Rightarrow> 'ki \<Rightarrow> 1 word llM
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
  (rbt_assn t ti ** \<upharpoonleft>key_assn k ki)
  (contains ti ki)
  (\<lambda>ri. \<upharpoonleft>bool.assn (rbt_contains t k) ri ** rbt_assn t ti ** \<upharpoonleft>key_assn k ki)"
proof(induction t arbitrary: ti)
  case Empty
  then show ?case
    unfolding rbt_contains_def
    apply (subst contains.simps)
    apply vcg
    done
next
  case (Branch c lhs key val rhs)
  note [vcg_rules] = Branch.IH
  note [simp] = rbt_contains_def

  show ?case
    apply (subst contains.simps)
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
  "('vi \<Rightarrow> 'vi llM) \<Rightarrow> ('ki, 'vi) rbti \<Rightarrow> 'ki \<Rightarrow> 'vi option_i llM" where
  "lookup value_copy node_p k = do {
    if node_p = null
    then return (OPTION_I init 0)
    else do {
      node \<leftarrow> ll_load node_p;
      k_old \<leftarrow> return rbt_node.key node;
      if!  lt_impl k k_old
      then! lookup value_copy (rbt_node.left node) k
      else! if! lt_impl k_old k
      then! lookup value_copy (rbt_node.right node) k
      else! do {
        val_copy \<leftarrow> value_copy (rbt_node.val node);
        return (OPTION_I val_copy 1)
      }
    }
  }"


lemmas [llvm_code] = lookup.simps


interpretation v_option: option_impl value_assn .


definition "value_option_assn \<equiv> v_option.option_assn"


lemma lookup_correct [vcg_rules]:
  assumes
    copy_rule [vcg_rules]:
    "\<And>v vi.
      llvm_htriple
      (\<upharpoonleft>value_assn v vi)
      (value_copy vi)
      (\<lambda>r. \<upharpoonleft>value_assn v vi ** \<upharpoonleft>value_assn v r)
    "   
  shows
    "
      llvm_htriple
      (rbt_assn t ti ** \<upharpoonleft>key_assn kn ki)
      (lookup value_copy ti ki)
      (\<lambda>opt.
        \<upharpoonleft>value_option_assn (rbt_lookup t kn) opt **
        rbt_assn t ti **
        \<upharpoonleft>key_assn kn ki)
    "
proof(induction t arbitrary: ti)
  case Empty
  then show ?case
    unfolding value_option_assn_def
    apply (subst lookup.simps)
    apply vcg
    done
next
  case (Branch c l k v r)

  note [vcg_rules] = Branch.IH

  from Branch show ?case
    apply (subst lookup.simps)
    apply vcg
    unfolding value_option_assn_def
    apply vcg
    done
qed


lemma lookup_correct_mem [vcg_rules]:
  assumes
    copy_rule [vcg_rules]:
    "\<And>v vi.
      llvm_htriple
      (\<upharpoonleft>value_assn v vi)
      (value_copy vi)
      (\<lambda>r. \<upharpoonleft>value_assn v vi ** \<upharpoonleft>value_assn v r)
    " and
    "k \<notin> ex"
  shows
    "
      llvm_htriple
      (rbt_assn_cplx t ptrs ex ti ** \<upharpoonleft>key_assn k ki)
      (lookup value_copy ti ki)
      (\<lambda>opt.
        \<upharpoonleft>value_option_assn (rbt_lookup t k) opt **
        rbt_assn_cplx t ptrs ex ti **
        \<upharpoonleft>key_assn k ki)
    "
proof(induction t arbitrary: ti)
  case Empty
  then show ?case
    unfolding value_option_assn_def
    apply (subst lookup.simps)
    apply vcg
    done
next
  case Branch

  note [vcg_rules] = Branch.IH

  from `k\<notin>ex` show ?case
    apply (subst lookup.simps)
    apply vcg
    unfolding value_option_assn_def
    apply vcg_compat
    apply (sep | simp)+
    done
qed


partial_function (M) lookup_ptr ::
  "('ki, 'vi) rbti \<Rightarrow> 'ki \<Rightarrow> ('ki, 'vi) rbti llM" where
  "lookup_ptr node_p k = do {
    if node_p = null
    then return null
    else do {
      node \<leftarrow> ll_load node_p;
      k_old \<leftarrow> return rbt_node.key node;
      if! lt_impl k k_old
      then! lookup_ptr (rbt_node.left node) k
      else! if! lt_impl k_old k
      then! lookup_ptr (rbt_node.right node) k
      else! return node_p
    }
  }"


lemma lookup_ptr_rule [vcg_rules]:
  "
    rbt_sorted t \<Longrightarrow>
    llvm_htriple
    (rbt_assn_cplx t ptrs ex ti ** \<upharpoonleft>key_assn kn ki)
    (lookup_ptr ti ki)
    (\<lambda>ptr. rbt_assn_cplx t ptrs ex ti ** \<upharpoonleft>key_assn kn ki **
      \<up>(if ptr = null then kn \<notin> rbt_key_set t else ptr = fst (the (ptrs kn)) \<and> kn \<in> rbt_key_set t ))
  "
proof(induction t arbitrary: ti)
  case Empty
  then show ?case 
    apply(subst lookup_ptr.simps)
    apply vcg
    done
next
  case (Branch c l k v r)
  
  note Branch[vcg_rules]

  from Branch(3) show ?case
    apply(subst lookup_ptr.simps)
    apply vcg
    subgoal
      apply vcg_compat
      apply (sep | find_sep)+
      unfolding rbt_greater_prop apply auto
      done

    apply vcg
    subgoal
      apply vcg_compat
      apply (sep | find_sep)+
      unfolding rbt_less_prop apply auto
      done

    apply vcg
    done
qed


lemma H: 
  "(\<And>x. llvm_htriple (P x) C (\<lambda>r. Q x r)) \<Longrightarrow>
  llvm_htriple (EXS x. P x) C (\<lambda>r. EXS x. Q x r) "
  unfolding htriple_def wpa_def STATE_def NEMonad.wp_def Sep_Generic_Wp.wp_def
  by blast


(*
lemma lookup_ptr_rule':
"
    rbt_sorted t \<Longrightarrow>
    llvm_htriple
    (EXS ptrs ex. rbt_assn_cplx t ptrs ex ti ** \<upharpoonleft>key_assn kn ki)
    (lookup_ptr ti ki)
    (\<lambda>ptr. EXS ptrs ex. rbt_assn_cplx t ptrs ex ti ** \<upharpoonleft>key_assn kn ki ** \<up>(if ptr = null then kn \<notin> rbt_key_set t else ptr = the (ptrs kn)))
"
  apply (rule H)+
  apply (rule lookup_ptr_rule)
  apply assumption
  done
*)


lemma rbt_lookup_none_keys:
 "rbt_sorted t \<Longrightarrow> k \<notin> rbt_key_set t \<Longrightarrow> rbt_lookup t k = None"
  using rbt_lookup_iff_keys
  by blast


lemma rbt_lookup_some_keys:
  assumes "rbt_sorted t" and "k \<in> rbt_key_set t" obtains v where "rbt_lookup t k = Some v"
  using rbt_lookup_iff_keys assms
  by blast

end


end