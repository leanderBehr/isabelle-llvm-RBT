theory Lookup_Ext
  imports 
    Lookup
    "../Extended_Assertion"
    "../Assertion_Tree_Lookup"
begin

context rbt_impl
begin

interpretation v_option: option_impl value_assn .

lemma lookup_correct_ext [vcg_rules]:
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
      (rbt_assn_ext t {} ti ** \<upharpoonleft>key_assn kn ki)
      (lookup value_copy ki ti)
      (\<lambda>opt.
        \<upharpoonleft>value_option_assn (rbt_lookup (rbt_of t) kn) opt **
        rbt_assn_ext t {} ti **
        \<upharpoonleft>key_assn kn ki)
    "
proof(induction t arbitrary: ti)
  case ATEmpty
  then show ?case
    unfolding value_option_assn_def
    apply (subst lookup.simps)
    apply vcg
    done
next
  case (ATBranch c l k v r)

  note [vcg_rules] = ATBranch.IH

  from ATBranch show ?case
    apply (subst lookup.simps)
    apply vcg
    unfolding value_option_assn_def
    apply vcg
    done
qed

lemma lookup_ptr_corrext_ext [vcg_rules]:
  "
    llvm_htriple
    (rbt_assn_ext t {} ti ** \<upharpoonleft>key_assn kn ki ** \<up>(rbt_sorted (rbt_of t)))
    (lookup_ptr ki ti)
    (\<lambda>ptr. rbt_assn_ext t {} ti ** \<upharpoonleft>key_assn kn ki **
      \<up>(if rbt_lookup (rbt_of t) kn = None then ptr = null else ptr_of_key t ti kn = Some ptr))
  "
proof(induction t arbitrary: ti)
  case ATEmpty
  then show ?case 
    apply(subst lookup_ptr.simps)
    apply vcg
    done
next
  case (ATBranch c k v ci li ki vi ri al ar)
  
  note ATBranch[vcg_rules]

  show ?case
    apply(subst lookup_ptr.simps)
    apply vcg
    subgoal
      apply vcg_compat
      apply (sepwith simp) 
       apply (cases "rbt_lookup (rbt_of al) kn")
        apply (auto simp add: ptr_of_key.simps)
      done

    apply vcg
    subgoal
      apply vcg_compat
      apply (sepwith simp)
      apply (cases "rbt_lookup (rbt_of ar) kn")
      apply (auto simp add: ptr_of_key.simps)
      done

    apply vcg
    subgoal
      apply vcg_compat
      apply (sep | simp add: ptr_of_key.simps)+
      done
    done
qed

end

end