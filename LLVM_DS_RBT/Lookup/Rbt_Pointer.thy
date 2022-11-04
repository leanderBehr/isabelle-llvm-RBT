theory Rbt_Pointer
  imports Setup
begin


context rbt_impl
begin


interpretation monad_syntax_M_loc .


definition rbt_ptr_load :: "('ki, 'vi) rbti \<Rightarrow> 'vi llM" where
  "rbt_ptr_load p \<equiv> do { n \<leftarrow> ll_load p; return rbt_node.val n }"


lemma pure_part_exE:
    assumes "pure_part (\<lambda>s. \<exists>x. P x s)"
    obtains x where "pure_part (P x)"
  using assms unfolding pure_part_def by blast
  

lemma rbt_assn_cplx_ptrs_someI:
  "\<lbrakk>k \<in> set (RBT_Impl.keys t); pure_part (rbt_assn_cplx t ptrs ex ti)\<rbrakk> \<Longrightarrow> 
  \<exists>p. ptrs k = Some p"
proof(induction t arbitrary: ti)
  case Empty
  then show ?case by simp
next
  case (Branch c k l v r)
  then show ?case
    apply auto
    subgoal by (auto dest!: pure_part_split_conj elim!: pure_part_exE)
    subgoal by (auto dest!: pure_part_split_conj elim!: pure_part_exE)
    subgoal by (auto dest!: pure_part_split_conj elim!: pure_part_exE)
    done
qed


lemma rbt_assn_cplx_ptrs_domI:
  "\<lbrakk>pure_part (rbt_assn_cplx t ptrs ex ti)\<rbrakk> \<Longrightarrow> set (RBT_Impl.keys t) \<subseteq> dom ptrs"
  using rbt_assn_cplx_ptrs_someI by blast  


lemma rbt_assn_cplx_extra_ex [simp]:
  "k \<notin> set (RBT_Impl.keys t) \<Longrightarrow> rbt_assn_cplx t ptrs (insert k ex) ti = rbt_assn_cplx t ptrs ex ti"
  by (induction t arbitrary: ti, auto)


lemma rbt_key_set_cases:
  assumes
    "kn \<in> rbt_key_set (rbt.Branch c l k v r)" and
    "rbt_sorted (rbt.Branch c l k v r)" and
    "\<lbrakk>kn = k; kn \<notin> rbt_key_set l; kn \<notin> rbt_key_set r\<rbrakk> \<Longrightarrow> thesis" and
    "\<lbrakk>kn \<noteq> k; kn \<in> rbt_key_set l; kn < k; kn \<notin> rbt_key_set r\<rbrakk> \<Longrightarrow> thesis" and
    "\<lbrakk>kn \<noteq> k; kn \<notin> rbt_key_set l; kn > k; kn \<in> rbt_key_set r\<rbrakk> \<Longrightarrow> thesis"
  shows
    thesis
  using assms
  apply (fastforce simp add: rbt_greater_prop rbt_less_prop)
  done


lemma rbt_ptr_load_correct' [vcg_rules]:
  assumes
    "rbt_sorted t" and
    "kn \<in> rbt_key_set t" and
    "kn \<notin> ex"
  shows
    "
    llvm_htriple
    (rbt_assn_cplx t ptrs ex ti)
    (rbt_ptr_load (fst (the (ptrs kn))) )
    (\<lambda>vi. \<upharpoonleft>value_assn (the (rbt_lookup t kn)) vi ** rbt_assn_cplx t ptrs (ex \<union> {kn}) ti **
      \<up>(vi = snd (the (ptrs kn))))
    "
  using assms
proof(induction t arbitrary: ti)
  case Empty 
  then show ?case by simp
next
  case (Branch c l k v r)
  from Branch(3-5) show ?case
    apply -

    apply (rule rbt_key_set_cases, assumption, assumption)

    subgoal unfolding rbt_ptr_load_def by vcg
    subgoal
      supply Branch(1)[vcg_rules]
      apply vcg
      done
    subgoal
      supply Branch(2)[vcg_rules]
      apply vcg
      apply auto (*unnecessarily splits the k \<in> ex if*)
       apply vcg
      done
    done
qed


lemma rbt_ptr_load_correct :
  assumes
    "rbt_sorted t" and
    "rbt_lookup t kn = Some v" and
    "kn \<notin> ex"
  shows
    "
    llvm_htriple
    (rbt_assn_cplx t ptrs ex ti)
    (rbt_ptr_load (fst (the (ptrs kn))) )
    (\<lambda>vi. \<upharpoonleft>value_assn v vi ** rbt_assn_cplx t ptrs (ex \<union> {kn}) ti **
      \<up>(vi = snd (the (ptrs kn))))
    "
  using assms rbt_ptr_load_correct' rbt_lookup_iff_keys(3)
  by (smt (verit, del_insts) entails_eq_iff htriple_ent_post option.sel)


end


end