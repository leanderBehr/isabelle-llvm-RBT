theory Lookup
  imports 
    "../Setup"
    "../Bool_Assn_Setup"
    "../Utilities"
    Rbt_Pointer
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
      k_lt \<leftarrow> lt_impl k k_old;
      if k_lt = 1
      then lookup value_copy (rbt_node.left node) k
      else do {
        k_gt \<leftarrow> lt_impl k_old k;
        if k_gt = 1
        then lookup value_copy (rbt_node.right node) k
        else do {
          val_copy \<leftarrow> value_copy (rbt_node.val node);
          return (OPTION_I val_copy 1)
        }
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

  show ?case
    apply (subst lookup.simps)
    apply vcg
    apply (simp add: `k\<notin>ex`)
    unfolding value_option_assn_def
    apply vcg
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
      apply isep_solver
      unfolding rbt_greater_prop apply auto
      done

    apply vcg
    subgoal
      apply vcg_compat
      apply isep_solver
      unfolding rbt_less_prop apply auto
      done

    apply vcg
    done
qed


definition lookup_ptr_to_option where
  "lookup_ptr_to_option value_copy t k \<equiv>
    do {
      res_p \<leftarrow> lookup_ptr t k;
      if res_p = null
      then return (OPTION_I init 0)
      else do {
        v \<leftarrow> rbt_ptr_load res_p;
        v_copy \<leftarrow> value_copy v;
        return (OPTION_I v_copy 1)
      }
    }
  "


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

find_theorems rbt_assn_cplx RBT_Impl.keys

lemma rbt_assn_cplx_join:
      "kn \<in> rbt_key_set t \<Longrightarrow> rbt_sorted t \<Longrightarrow>
      rbt_assn_cplx t ptrs {kn} ti ** \<upharpoonleft>value_assn (the (rbt_lookup t kn)) (snd (the (ptrs kn)))
      \<turnstile> rbt_assn_cplx t ptrs {} ti"
proof(induction t arbitrary: ti)
  case Empty
  then show ?case by simp
next
  case (Branch c l k v r)

  have H1: "(x::'a::linorder) < y \<Longrightarrow> \<not>(y < x)" for x y by simp

  from Branch(3-4) show ?case
    
    apply (rule rbt_key_set_cases)

    subgoal
      apply simp
      apply isep_elim_ex
      apply isep_intro_ex
      apply isep_solver_keep
      apply simp
      apply isep_solver_keep
      done

    subgoal
      apply simp
      apply isep_elim_ex
      apply isep_intro_ex
      apply (isep_drule drule: Branch(1))
      using Branch(4) apply auto
      apply isep_solver_keep
      done

    subgoal
      apply (simp split del: if_split)
      apply isep_elim_ex
      apply isep_intro_ex
      apply (isep_drule drule: Branch(2))
      using Branch(4) apply (simp_all add: H1)
      apply isep_assumption+
      done

    done
qed
  

lemma lookup_ptr_to_option_correct_cplx [vcg_rules]:
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
      rbt_sorted t \<Longrightarrow>
      llvm_htriple
      (rbt_assn_cplx t ptrs {} ti ** \<upharpoonleft>key_assn kn ki)
      (lookup_ptr_to_option value_copy ti ki)
      (\<lambda>opt.
        \<upharpoonleft>value_option_assn (rbt_lookup t kn) opt **
        rbt_assn_cplx t ptrs {} ti **
        \<upharpoonleft>key_assn kn ki)
    "
  unfolding lookup_ptr_to_option_def
  apply vcg
  subgoal
    unfolding value_option_assn_def
    apply (simp add: rbt_lookup_none_keys)
    apply vcg
    done
  apply vcg
  subgoal
    unfolding value_option_assn_def
    apply vcg_compat
    apply (rule rbt_lookup_some_keys, simp, simp)
    apply (isep_solver_keep isep_dest: rbt_assn_cplx_join | simp)+
    done
  done


lemma htriple_ent_pre_post:
  "\<lbrakk>htriple P' c Q'; P \<turnstile> P'; \<And>r. Q' r \<turnstile> Q r\<rbrakk> \<Longrightarrow> htriple P c Q"
  using htriple_ent_pre htriple_ent_post by blast


lemma lookup_ptr_to_option_correct_cplx' [vcg_rules]:
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
      rbt_sorted t \<Longrightarrow>
      llvm_htriple
      (EXS ptrs. rbt_assn_cplx t ptrs {} ti ** \<upharpoonleft>key_assn kn ki)
      (lookup_ptr_to_option value_copy ti ki)
      (\<lambda>opt. EXS ptrs.
        \<upharpoonleft>value_option_assn (rbt_lookup t kn) opt **
        rbt_assn_cplx t ptrs {} ti **
        \<upharpoonleft>key_assn kn ki)
    "
  apply (rule H)
  using copy_rule lookup_ptr_to_option_correct_cplx by simp


lemma lookup_ptr_to_option_correct [vcg_rules]:
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
      rbt_sorted t \<Longrightarrow>
      llvm_htriple
      (rbt_assn t ti ** \<upharpoonleft>key_assn kn ki)
      (lookup_ptr_to_option value_copy ti ki)
      (\<lambda>opt.
        \<upharpoonleft>value_option_assn (rbt_lookup t kn) opt **
        rbt_assn t ti **
        \<upharpoonleft>key_assn kn ki)
    "
  using lookup_ptr_to_option_correct_cplx
  apply - 
  apply (rule htriple_ent_pre_post[OF lookup_ptr_to_option_correct_cplx'])
  using copy_rule apply simp
    apply simp
   apply (isep_solver_keep isep_dest: rbt_assn_entails_rbt_assn_cplx)
   apply simp
  apply (isep_solver_keep isep_dest: rbt_assn_cplx_entails_rbt_assn)
  done


end


end