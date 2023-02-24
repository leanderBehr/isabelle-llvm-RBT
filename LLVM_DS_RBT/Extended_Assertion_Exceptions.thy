theory Extended_Assertion_Exceptions
  imports 
    Abstract_Rbt
    Assertion_Tree_Lookup
    Utilities_Ext
begin

context rbt_impl
begin

lemma rbt_less_value_ex_eq_2 [simp]:
  "rbt_of t |\<guillemotleft> kn \<Longrightarrow> rbt_assn_ext t (ex - {kn}) ti = rbt_assn_ext t ex ti"
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
  "rbt_of t |\<guillemotleft> kn \<Longrightarrow> rbt_assn_ext t (Set.insert kn ex) ti = rbt_assn_ext t ex ti"
  apply (subst rbt_less_value_ex_eq_2[symmetric]) by simp+

lemma rbt_greater_value_ex_eq_2 [simp]:
  "kn \<guillemotleft>| rbt_of t \<Longrightarrow> rbt_assn_ext t (ex - {kn}) ti = rbt_assn_ext t ex ti"
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
  "kn \<guillemotleft>| rbt_of t \<Longrightarrow> rbt_assn_ext t (Set.insert kn ex) ti = rbt_assn_ext t ex ti"
  apply (subst rbt_greater_value_ex_eq_2[symmetric]) by simp+

lemma [simp]:
  "value_of_key ATEmpty k = None"
  unfolding value_of_key_def value_of_key'.simps by simp

lemma [simp]:
  "kn < k \<Longrightarrow> value_of_key (ATBranch c k v ci li ki vi ri l r) kn = value_of_key l kn"
  unfolding value_of_key_def apply (simp add: value_of_key'.simps)
  unfolding value_of_key'.simps[symmetric]
  using value_of_key'_value_of_key_eq by metis

lemma [simp]:
  "k < kn \<Longrightarrow> value_of_key (ATBranch c k v ci li ki vi ri l r) kn = value_of_key r kn"
  unfolding value_of_key_def apply (auto simp add: value_of_key'.simps)
  unfolding value_of_key'.simps[symmetric]
  using value_of_key'_value_of_key_eq by metis

lemma [simp]:
  "value_of_key (ATBranch c k v ci li ki vi ri l r) k = Some vi"
  unfolding value_of_key_def apply (auto simp add: value_of_key'.simps)
  done

lemma value_ex_split_ent:
  assumes
    "kn \<notin> ex" and
    "value_of_key t kn = Some vi" and
    "rbt_sorted (rbt_of t)"
  shows
    "
      rbt_assn_ext t ex ti \<turnstile> rbt_assn_ext t (ex \<union> {kn}) ti ** \<upharpoonleft>value_assn (the (rbt_lookup (rbt_of t) kn)) vi
    "
  using assms
proof(induction t arbitrary: ti)
  case ATEmpty
  then show ?case by simp
next
  case (ATBranch c k v ci li ki vi ri l r)
  then show ?case
      proof(cases kn k rule: linorder_cases)
        case less

        note ATBranch(1)[isep_dest]

        from less have "k \<noteq> kn" by simp
        moreover from less ATBranch(5) have "kn \<guillemotleft>| rbt_of r"
          using rbt_greater_trans by auto

        ultimately show ?thesis using less ATBranch(3-5)
          unfolding rbt_assn_ext_unfold
          apply simp
          apply (sepwith simp) 
          apply simp
          done
      next
        case equal
        with ATBranch show ?thesis
          unfolding rbt_assn_ext_unfold
          apply -
          apply (sepEwith \<open>auto intro: rbt_less_trans rbt_greater_trans\<close>) 
          apply simp
          apply sep
          done
      next
        case greater
        
        note ATBranch(2)[isep_dest]

        from greater have "k \<noteq> kn" by simp
        moreover from greater ATBranch(5) have "rbt_of l |\<guillemotleft> kn"
          using rbt_less_trans by auto

        ultimately show ?thesis using greater ATBranch(3-5)
          unfolding rbt_assn_ext_unfold
          apply auto[]
          apply (sepwith \<open>simp add: order_less_not_sym\<close>)
          apply simp
          done
      qed
qed


lemma value_ex_split_red:
  assumes
    "kn \<notin> ex" and
    "value_of_key t kn = Some vi" and
    "rbt_sorted (rbt_of t)"
  shows
    "
      is_sep_red (rbt_assn_ext t (ex \<union> {kn}) ti) \<box> (rbt_assn_ext t ex ti) (\<upharpoonleft>value_assn (the (rbt_lookup (rbt_of t) kn)) vi)
    "
  apply (rule is_sep_redI)
  subgoal premises prems
    apply (sep isep_dest: value_ex_split_ent)
    using assms apply auto
    apply (sep isep_dest: prems[simplified])
    done
  done

lemma value_ex_join_ent':
  assumes
    "value_of_key t kn = Some vi" and
    "kn \<in> ex" and
    "rbt_sorted (rbt_of t)"
  shows
    "
    rbt_assn_ext t ex ti ** \<upharpoonleft>value_assn v vi \<turnstile> 
    (EXS t_res.
      rbt_assn_ext t_res (ex - {kn}) ti **
      \<up>(rbt_of t_res = rbt_update (rbt_of t) kn v) **
      ctx(rbt_sorted (rbt_of t_res)) **
      \<up>(ptr_of_key t_res ti = ptr_of_key t ti) **
      \<up>(value_of_key t_res = value_of_key t)
    )
    "
  using assms
proof (induction t arbitrary: ti)
  case ATEmpty
  then show ?case by simp
next
  case (ATBranch c k v ci li ki vi ri l r)
  show ?case
  proof(cases kn k rule: linorder_cases)
    case less
    note ATBranch(2)[isep_dest]

    from less have "kn \<noteq> k" by simp
    moreover from ATBranch(5) rbt_greater_trans less have "kn \<guillemotleft>| rbt_of r" by auto

    ultimately show ?thesis using ATBranch(3-5) less
      apply - 
      unfolding rbt_assn_ext_unfold
      apply (isep_drule drule: ATBranch(1))
      apply (auto)[3]
 
      apply (sepEwith \<open>(solves auto)?\<close>)
       apply (simp add: rbt_map_entry_rbt_less rbt_map_entry_rbt_sorted)  

      apply (sepEwith \<open>(solves auto)?\<close>)
      subgoal by (simp add: ptr_of_key_simps)

      apply (sepEwith \<open>(solves auto)?\<close>)
      subgoal 
        apply simp
        apply prune_pure
        thm value_of_key_simps
        apply vok_solver 
        done

      apply simp
      apply (sepEwith \<open>(solves auto)?\<close>)
      done
  next
    case equal
    with ATBranch(3-5) show ?thesis
      unfolding rbt_assn_ext_unfold
      apply -
      apply (sepEwith \<open>auto intro: rbt_less_trans rbt_greater_trans\<close>)
       apply vok_solver
      apply simp
      apply sep
      done
  next
    case greater
    note ATBranch(2)[isep_dest]

    from greater have "\<not>kn < k" by simp
    moreover from greater have "kn \<noteq> k" by simp
    moreover from ATBranch(5) rbt_less_trans greater have "rbt_of l |\<guillemotleft> kn" by auto

    ultimately show ?thesis using ATBranch(3-5) greater
      apply - 
      unfolding rbt_assn_ext_unfold
      apply (isep_drule drule: ATBranch(2))
      apply (auto)[3]
 
      apply (sepEwith \<open>(solves auto)?\<close>)
       apply (simp add: rbt_map_entry_rbt_greater rbt_map_entry_rbt_sorted)  

      apply (sepEwith \<open>(solves auto)?\<close>)
      subgoal by (simp add: ptr_of_key_simps)

      apply (sepEwith \<open>(solves auto)?\<close>)
      subgoal 
        apply simp
        apply prune_pure
        apply vok_solver 
        done

      apply simp
      apply (sepEwith \<open>(solves auto)?\<close>)
      done
  qed
qed

lemmas value_ex_join_ent = value_ex_join_ent'[simplified ctx_def]

lemma value_ex_join_red:
  "rbt_sorted (rbt_of t1) \<Longrightarrow> k \<in> ex \<Longrightarrow> k \<notin> ex' \<Longrightarrow> value_of_key t1 k = Some vi \<Longrightarrow>
  is_sep_red
  (EXS t2. rbt_assn_ext t2 (ex - {k}) ti ** \<up>(rbt_of t2 = rbt_update (rbt_of t1) k v))
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