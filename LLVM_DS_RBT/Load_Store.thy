theory Load_Store
  imports 
    Assertion_Tree_Lookup
    Extended_Assertion_Exceptions
begin

context rbt_impl
begin
interpretation rbt_impl_deps .

subsection \<open>Load\<close>

definition "load p \<equiv> do { n \<leftarrow> ll_load p; return rbt_node.val n }"

lemma rbt_ptr_load_correct [vcg_rules]:
  assumes
    "rbt_sorted (rbt_of t)" and
    "(kn, VALUE_EX) \<notin> ex" and
    "(kn, PTO_EX) \<notin> ex"
  shows
    "
    llvm_htriple
    (rbt_assn_ext t ex ti ** \<up>(ptr_of_key t ti kn = Some p))
    (load p)
    (\<lambda>res_v.
        \<upharpoonleft>value_assn (the (rbt_lookup (rbt_of t) kn)) res_v **
        rbt_assn_ext t ({(kn, VALUE_EX)} \<union> ex) ti **
        \<up>(Some res_v = value_of_key t ti kn)
    )
    "
  using assms
proof(induction t arbitrary: ti)
  case ATEmpty 
  show ?case by (simp add: ptr_of_key.simps)
next
  case (ATBranch c k v ci li ki vi ri al ar)
  note ATBranch(1-2)[vcg_rules]

  note value_of_key.simps[simp]

  show ?case
  proof(cases kn k rule: linorder_cases)
    case less
    moreover from less ATBranch have "kn \<guillemotleft>| rbt_of ar" by (auto intro: rbt_greater_trans)
    moreover from less have "k \<noteq> kn" by blast

    ultimately show ?thesis using ATBranch(3-5)
      supply ptr_of_key.simps[simp]      
      apply vcg
      done
  next
    case equal
    with ATBranch(3-5) show ?thesis
      unfolding load_def
      supply ptr_of_key.simps[simp]
      apply vcg
      unfolding rbt_assn_ext_unfold
      apply vcg
      done
  next
    case greater
    moreover from greater ATBranch have "rbt_of al |\<guillemotleft> kn" by (auto intro: rbt_less_trans)
    moreover from greater have "k \<noteq> kn" by blast

    ultimately show ?thesis using ATBranch(3-5)
      supply ptr_of_key.simps[simp]
      apply vcg
      apply simp
      apply vcg
      done
  qed
qed

subsection \<open>Store\<close>

definition store :: "('ki, 'vi) rbti \<Rightarrow> 'vi \<Rightarrow> unit llM" where
  "store p v = set_value_p v p"

lemma store_correct [vcg_rules]:
  assumes
    "rbt_sorted (rbt_of t)" and
    "(kn, VALUE_EX) \<in> ex" and
    "(kn, PTO_EX) \<notin> ex" and
    "ptr_of_key t ti kn = Some p"
  shows
    "
    llvm_htriple
    (rbt_assn_ext t ex ti)
    (store p vni)
    (\<lambda>_. EXS res_t.
      rbt_assn_ext res_t ex ti **
      \<up>(rbt_of res_t = rbt_of t) **
      \<up>(ptr_of_key res_t ti = ptr_of_key t ti) **
      \<up>(value_of_key res_t ti = (value_of_key t ti)(kn \<mapsto> vni))
    )
    "
  using assms
proof(induction t arbitrary: ti)
  case ATEmpty thus ?case by (simp add: ptr_of_key.simps)
next
  case (ATBranch c k v ci li ki vi ri l r)
  show ?case
  proof(cases k kn rule: linorder_cases)
    case less
    note ATBranch(2)[vcg_rules]
    from less ATBranch(6) have "ptr_of_key r ri kn = Some p"
      by (simp add: order_less_not_sym ptr_of_key.simps)
    with less ATBranch(3-5) show ?thesis
      apply vcg
      apply vcg_compat
      apply (sepE | find_sep)+

      subgoal by blast

      subgoal for x
        apply (rule ext)
        unfolding ptr_of_key.simps
        by (auto, metis)

      apply (rule ext)
      subgoal for asf sa x xa
        apply (drule fun_cong[where x = xa])+
        apply (auto simp add: value_of_key.simps)
        done
      done
  next
    case equal
    with ATBranch(6) have "p = ti" by (simp add: ptr_of_key.simps) 
    with ATBranch(3-5) equal show ?thesis
      unfolding store_def
      unfolding rbt_assn_ext_unfold
      apply vcg
      apply vcg_compat
      apply (sepEwith \<open>auto simp add: value_of_key.simps\<close>)
      apply simp
      done
  next
    case greater
    note ATBranch(1)[vcg_rules]
    from greater ATBranch(6) have "Some p = ptr_of_key l li kn"
      by (auto simp add: ptr_of_key.simps)
    with greater ATBranch(3-5) show ?thesis
      apply vcg
      apply vcg_compat
      apply (sepE | find_sep)+

      subgoal by blast

      subgoal for x
        apply (rule ext)
        unfolding ptr_of_key.simps
        by (auto, metis)

      apply (rule ext)
      subgoal for asf sa x xa
        apply (drule fun_cong[where x = xa])+
        apply (auto simp add: value_of_key.simps)
        done
      done
  qed
qed

end

end