theory Utilities_Ext
  imports 
    Utilities
    Extended_Assertion
begin 

context rbt_impl
begin

declare ll_matches_rbt.simps[simp]

lemma matches_rbt_correct [vcg_rules]:
  "
  llvm_htriple
  (rbt_assn_ext t {} ti)
  (ll_matches_rbt pat ti)
  (\<lambda>r. rbt_assn_ext t {} ti ** \<upharpoonleft>bool.assn (matches_rbt pat (rbt_of t)) r)
"
proof(induction pat arbitrary: t ti)
  case RP_Var
  then show ?case
    apply vcg
    apply (subst Hack_1) (*!FIX!*)
    apply vcg
    done
next
  case RP_Empty
  then show ?case
    apply vcg
    apply (subst Hack_1) (*!FIX!*)
    apply vcg_compat
    apply isep_extract_pure
    apply (simp add: bool_assn_pure_eq)
    apply auto[]
    apply (sepwith \<open>auto elim: rbt_of.elims\<close>)+
    done
next
  case (RP_Branch x1 pat1 pat2)
  note [vcg_rules] = RP_Branch

  show "?case"
    apply vcg
    subgoal
      apply (subst Hack_1) (*!FIX!*)
      apply (simp add: bool_assn_pure_eq)
      apply vcg
      done
    subgoal
      supply load_rbt_non_null[vcg_rules]
      apply vcg
        apply (all \<open>subst Hack_1\<close>)
        apply vcg
      done
    done
qed

declare ll_matches_rbt.simps[simp del]

definition "ctx (P::bool) \<equiv> \<up>P"

lemma sep_context_pureI: "B \<Longrightarrow> is_sep_red (\<up>B) \<box> \<box> (ctx B)"
  unfolding ctx_def
  apply (rule is_sep_redI)
  by (simp add: pure_true_conv)


end

end