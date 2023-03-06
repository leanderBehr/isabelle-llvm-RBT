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
    "rbt_sorted (rbt_of t)"
  shows
    "
    llvm_htriple
    (rbt_assn_ext t ex ti ** \<up>(ptr_of_key t ti kn = Some p))
    (load p)
    (\<lambda>vi_res.
        rbt_assn_ext t ex ti **
        \<up>(value_of_key t kn = Some vi_res)
    )
    "
  using assms
proof(induction t arbitrary: ti)
  case ATEmpty 
  show ?case by (simp add: ptr_of_key.simps)
next
  case (ATBranch c k v ci li ki vi ri al ar)
  note ATBranch(1-2)[vcg_rules]

  show ?case
  proof(cases kn k rule: linorder_cases)
    case less
    moreover from less ATBranch have "kn \<guillemotleft>| rbt_of ar" by (auto intro: rbt_greater_trans)
    moreover from less have "k \<noteq> kn" by blast

    ultimately show ?thesis using ATBranch(3)
      supply ptr_of_key.simps[simp]
      apply vcg
      done
  next
    case equal
    with ATBranch(3) show ?thesis
      unfolding load_def
      supply ptr_of_key.simps[simp]
      unfolding rbt_assn_ext_unfold
      apply vcg
      done
  next
    case greater
    moreover from greater ATBranch have "rbt_of al |\<guillemotleft> kn" by (auto intro: rbt_less_trans)
    moreover from greater have "k \<noteq> kn" by blast
    ultimately show ?thesis using ATBranch(3)
      supply ptr_of_key.simps[simp] order_less_not_sym[simp] 
      apply vcg
      done
  qed
qed

subsection \<open>Store\<close>


definition store :: "('ki, 'vi) rbti \<Rightarrow> 'vi \<Rightarrow> unit llM" where
  "store p v = set_value_p v p"

lemma Hx: "(k, v) \<in> graph (value_of_key t) \<Longrightarrow> rbt_of t |\<guillemotleft> k \<Longrightarrow> T"
  apply (induction t)
  unfolding graph_def
  apply auto
  done

lemma Hy: "(k, v) \<in> graph (value_of_key t) \<Longrightarrow> k \<guillemotleft>| rbt_of t \<Longrightarrow> T"
  apply (induction t)
  unfolding graph_def
   apply auto
  done

lemma store_correct:
  assumes
    "ptr_of_key t ti kn = Some p" and
    "kn \<in> ex" and
    "rbt_sorted (rbt_of t)"
  shows
    "
    llvm_htriple
    (rbt_assn_ext t ex ti)
    (store p vni)
    (\<lambda>_. EXS t_res.
      rbt_assn_ext t_res ex ti **
      \<up>(rbt_of t_res = rbt_of t) **
      \<up>(ptr_of_key t_res ti = ptr_of_key t ti) **
      \<up>(value_of_key t_res = (value_of_key t)(kn \<mapsto> vni))
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
    from less ATBranch(3) have "ptr_of_key r ri kn = Some p"
      by (simp add: order_less_not_sym ptr_of_key.simps)
    with less ATBranch(3-5) show ?thesis
      apply vcg
      apply vcg_compat
      apply (sepEwith \<open>simp\<close> | find_sep)+
       apply pok_solver

      unfolding fun_upd_apply[symmetric]
      apply vok_solver
      by (fast intro: rbt_less_trans elim: Hx)
  next
    case equal
    with ATBranch(3) have "p = ti" by (simp add: ptr_of_key.simps) 
    with ATBranch(3-5) equal show ?thesis
      unfolding store_def
      unfolding rbt_assn_ext_unfold
      apply vcg
      apply vcg_compat
      apply (sepEwith \<open>(solves auto) | solves pok_solver | succeed\<close>)
      unfolding fun_upd_apply[symmetric]
      apply vok_solver
        apply (auto elim: Hx Hy)
      done
  next
    case greater
    note ATBranch(1)[vcg_rules]
    from greater ATBranch(3) have "ptr_of_key l li kn = Some p"
      by (auto simp add: ptr_of_key.simps)
    with greater ATBranch(3-5) show ?thesis
      apply vcg
      apply vcg_compat
      apply (sepEwith simp | find_sep)+
      unfolding fun_upd_apply[symmetric]
       apply pok_solver
      apply vok_solver
      by (fast intro: rbt_greater_trans elim: Hy)
  qed
qed


lemma store_correct_no_ex:
  assumes
    "ptr_of_key t ti kn = Some p" and
    "kn \<notin> ex" and
    "rbt_sorted (rbt_of t)"
  shows
    "
    llvm_htriple
    (rbt_assn_ext t ex ti)
    (store p vni)
    (\<lambda>_. EXS t_res.
      rbt_assn_ext t_res ({kn} \<union> ex) ti ** \<upharpoonleft>value_assn (the (rbt_lookup (rbt_of t) kn)) (the (value_of_key t kn)) **
      \<up>(rbt_of t_res = rbt_of t) **
      \<up>(ptr_of_key t_res ti = ptr_of_key t ti) **
      \<up>(value_of_key t_res = (value_of_key t)(kn \<mapsto> vni))
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
    from less ATBranch(3) have "ptr_of_key r ri kn = Some p"
      by (simp add: order_less_not_sym ptr_of_key.simps)



    then show ?thesis using less ATBranch(3-5)
      apply vcg
      apply vcg_compat
      apply (sepEwith simp)
       apply pok_solver
      apply sep
       apply (simp_all only: fun_upd_apply[symmetric])
       apply vok_solver
       apply (fast intro: rbt_less_trans elim: Hx)

      apply (auto simp: less_imp_neq rbt_less_trans ) 
      apply sep
      done
  next
    case equal
    with ATBranch(3) have "p = ti" by (simp add: ptr_of_key.simps) 
    with ATBranch(3-5) equal show ?thesis
      unfolding store_def
      unfolding rbt_assn_ext_unfold
      apply vcg
      apply vcg_compat
      apply (sepEwith simp)
       apply pok_solver
      apply sep
      unfolding fun_upd_apply[symmetric]
       apply vok_solver
      apply (auto elim: Hx Hy)
      done
  next
    case greater
    note ATBranch(1)[vcg_rules]
    from greater ATBranch(3) have "Some p = ptr_of_key l li kn"
      by (auto simp add: ptr_of_key.simps)

    moreover from greater have "k \<noteq> kn" by simp 

    ultimately show ?thesis using greater ATBranch(3-5)
      apply vcg
      apply vcg_compat
      apply (sepEwith simp)
       apply pok_solver

      apply sep
      unfolding fun_upd_apply[symmetric]
       apply vok_solver
       apply (fast intro: rbt_greater_trans elim: Hy)
      apply (auto simp: rbt_greater_trans order_less_not_sym)
      done
  qed
qed



lemma store_correct' [vcg_rules]:
    "
    llvm_htriple
    (rbt_assn_ext t ex ti ** \<up>(ptr_of_key t ti kn = Some p) ** \<up>(kn \<in> ex) ** \<up>(rbt_sorted (rbt_of t)))
    (store p vni)
    (\<lambda>_. EXS t_res.
      rbt_assn_ext t_res ex ti **
      \<up>(rbt_of t_res = rbt_of t) **
      \<up>(ptr_of_key t_res ti = ptr_of_key t ti) **
      \<up>(value_of_key t_res = (value_of_key t)(kn \<mapsto> vni))
    )
    "
  supply store_correct[vcg_rules]
  apply vcg 
    apply auto
  apply vcg
  done

lemma store_correct_no_ex' [vcg_rules]:
    "
    llvm_htriple
    (rbt_assn_ext t ex ti ** \<up>(ptr_of_key t ti kn = Some p) ** \<up>(kn \<notin> ex) ** \<up>(rbt_sorted (rbt_of t)))
    (store p vni)
    (\<lambda>_. EXS t_res.
      rbt_assn_ext t_res ({kn} \<union> ex) ti ** \<upharpoonleft>value_assn (the (rbt_lookup (rbt_of t) kn)) (the (value_of_key t kn)) **
      \<up>(rbt_of t_res = rbt_of t) **
      \<up>(ptr_of_key t_res ti = ptr_of_key t ti) **
      \<up>(value_of_key t_res = (value_of_key t)(kn \<mapsto> vni))
    )
    "
  supply store_correct_no_ex[vcg_rules]
  apply vcg
    apply auto
  apply vcg
  done


end

end