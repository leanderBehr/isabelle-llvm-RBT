theory Extended_Assertion_Exceptions
  imports 
    Abstract_Rbt
    Assertion_Tree_Lookup
begin

context rbt_impl
begin

lemma rbt_less_value_ex_eq_2 [simp]:
  "rbt_of t |\<guillemotleft> kn \<Longrightarrow> rbt_assn_ext t (ex - {(kn, VALUE_EX)}) ti = rbt_assn_ext t ex ti"
proof (induction t arbitrary: ti)
  case ATEmpty
  show ?case by simp
next
  case (ATBranch c k v ci li ki vi ri l r)

  hence "kn \<noteq> k" by auto  
  
  with ATBranch show ?case
    unfolding rbt_assn_ext_unfold
    apply simp
    done
qed

lemma rbt_less_value_ex_eq_1 [simp]:
  "rbt_of t |\<guillemotleft> kn \<Longrightarrow> rbt_assn_ext t (Set.insert (kn, VALUE_EX) ex) ti = rbt_assn_ext t ex ti"
  apply (subst rbt_less_value_ex_eq_2[symmetric]) by simp+

lemma rbt_greater_value_ex_eq_2 [simp]:
  "kn \<guillemotleft>| rbt_of t \<Longrightarrow> rbt_assn_ext t (ex - {(kn, VALUE_EX)}) ti = rbt_assn_ext t ex ti"
proof (induction t arbitrary: ti)
  case ATEmpty
  show ?case by simp
next
  case (ATBranch c k v ci li ki vi ri l r)

  hence "kn \<noteq> k" by auto  
  
  with ATBranch show ?case
    unfolding rbt_assn_ext_unfold
    apply simp
    done
qed

lemma rbt_greater_value_ex_eq_1 [simp]:
  "kn \<guillemotleft>| rbt_of t \<Longrightarrow> rbt_assn_ext t (Set.insert (kn, VALUE_EX) ex) ti = rbt_assn_ext t ex ti"
  apply (subst rbt_greater_value_ex_eq_2[symmetric]) by simp+

lemma value_ex_join_ent:
  assumes
    "(kn, VALUE_EX) \<in> ex" and
    "value_of_key t1 ti kn = Some vi" and
    "rbt_sorted (rbt_of t1)"
  shows
    "
    rbt_assn_ext t1 ex ti ** \<upharpoonleft>value_assn v vi \<turnstile> 
    (EXS t2. rbt_assn_ext t2 (ex - {(kn, VALUE_EX)}) ti ** \<up>(rbt_of t2 = rbt_update (rbt_of t1) kn v))
    "
  using assms
proof (induction t1 arbitrary: ti)
  case ATEmpty
  then show ?case unfolding value_of_key.simps by simp
next
  case (ATBranch c k v ci li ki vi ri l r)
  show ?case
  proof(cases kn k rule: linorder_cases)
    case less
    note ATBranch(2)[isep_dest]

    from less have "kn \<noteq> k" by simp
    moreover from ATBranch(5) rbt_greater_trans less have "kn \<guillemotleft>| rbt_of r" by auto

    ultimately show ?thesis using ATBranch(3-4) less
      apply - 
      unfolding rbt_assn_ext_unfold
      apply (isep_drule drule: ATBranch(1))
      using ATBranch(5) apply (auto simp add: value_of_key.simps)[3]
      apply sepE
       apply auto[]
      apply auto[]
      apply sep
      done
  next
    case equal
    with ATBranch(4) show ?thesis
      apply -
      apply sepE
       apply auto[]
      unfolding rbt_assn_ext_unfold
      apply sep
      using ATBranch(5) rbt_less_trans rbt_greater_trans apply auto[]
      using ATBranch(3) apply (simp add: value_of_key.simps) 
      apply sep
      done
  next
    case greater
    note ATBranch(2)[isep_dest]

    from greater have "\<not>kn < k" by simp
    moreover from greater have "kn \<noteq> k" by simp
    moreover from ATBranch(5) rbt_less_trans greater have "rbt_of l |\<guillemotleft> kn" by auto

    ultimately show ?thesis using ATBranch(3-4) greater
      apply - 
      unfolding rbt_assn_ext_unfold
      apply (isep_drule drule: ATBranch(2)) 
      using ATBranch(5) apply (auto simp add: order_less_not_sym value_of_key.simps)[3]
      apply sepE
       apply auto[]
      apply auto[]
      apply sep
      done
  qed
qed

lemma value_ex_join_red:
  "rbt_sorted (rbt_of t1) \<Longrightarrow> (k, VALUE_EX) \<in> ex \<Longrightarrow> (k, VALUE_EX) \<notin> ex' \<Longrightarrow> value_of_key t1 ti k = Some vi \<Longrightarrow>
  is_sep_red
  (EXS t2. rbt_assn_ext t2 (ex - {(k, VALUE_EX)}) ti ** \<up>(rbt_of t2 = rbt_update (rbt_of t1) k v))
  (EXS t3. rbt_assn_ext t3 ex' ti)
  (rbt_assn_ext t1 ex ti ** \<upharpoonleft>value_assn v vi)
  (EXS t3. rbt_assn_ext t3 ex' ti)
  "
  apply (rule is_sep_redI)
  subgoal premises prems for Ps Qs
  apply (rule entails_trans[OF _ prems(5)])
    apply (isep_drule drule: value_ex_join_ent)
    using prems(1-4) apply auto[3]
    apply sepE
    done
  done

end

end