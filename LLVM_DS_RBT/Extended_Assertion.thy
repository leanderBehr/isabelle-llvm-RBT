theory Extended_Assertion
  imports Setup
begin

subsection \<open>Assertion Tree\<close>

datatype ('k, 'v, 'ki, 'vi) assn_tree =
  ATEmpty |
  ATBranch
  (color: color)
  (key: 'k)
  (val: 'v) 
  "8 word"
  (ll_left: "('ki, 'vi) rbti")
  (ll_key: 'ki) 
  (ll_val: 'vi) 
  (ll_right: "('ki, 'vi) rbti")
  (left: "('k, 'v, 'ki, 'vi) assn_tree")
  (right: "('k, 'v, 'ki, 'vi) assn_tree")


subsubsection \<open>rbt of\<close>

fun rbt_of :: "('k, 'v, 'ki, 'vi) assn_tree \<Rightarrow> ('k, 'v) rbt"  where
  "rbt_of ATEmpty = rbt.Empty" |
  "rbt_of (ATBranch c k v _ _ _ _ _ l r) =
    (rbt.Branch c (rbt_of l) k v (rbt_of r))"

declare rbt_of.elims[where y=rbt.Empty, simplified, elim!]
lemma rbt_of_branchE [elim!]:
  assumes
    "rbt_of t = rbt.Branch c l k v r"
  shows
    "\<lbrakk>\<And>al ar. rbt_of al = l \<Longrightarrow> rbt_of ar = r  \<Longrightarrow> (\<And>ci li ki vi ri. t = ATBranch c k v ci li ki vi ri al ar \<Longrightarrow> P)\<rbrakk> \<Longrightarrow> P"
  using assms
  by (blast elim: rbt_of.elims)


lemma rbt_of_branchI [intro!]:
  assumes 
    "rbt_of l = l'"
    "rbt_of r = r'"
  shows
    "rbt_of (ATBranch c k v ci li ki vi ri l r) = (rbt.Branch c l' k v r')"
  using assms by simp


lemma rbt_of_emptyI [intro!]:
  "rbt_of ATEmpty = rbt.Empty"
  by simp

lemma rbt_of_reorient_branch [simp]: 
  "(Branch c l k v r = rbt_of x) = (rbt_of x = Branch c l k v r)" by auto

lemma rbt_of_reorient_empty [simp]:
  "(rbt.Empty = rbt_of t) = (rbt_of t = rbt.Empty)" by auto

subsection \<open>Assertion\<close>

datatype except = VALUE_EX

fun assn_unless (infixl "unless" 40) where 
  "assn_unless assn b = (if b then \<box> else assn)"
declare assn_unless.simps[simp del]


lemma assn_unless_True [simp]:
  "(assn unless False) = assn"
  by (simp add: assn_unless.simps)


lemma assn_unless_False [simp]:
  "(assn unless True) = \<box>"
  by (simp add: assn_unless.simps)


context rbt_impl
begin
interpretation rbt_impl_deps .

fun rbt_assn_ext :: "('k, 'v, 'ki, 'vi) assn_tree \<Rightarrow> ('k \<times> except) set \<Rightarrow> ('ki, 'vi) rbti \<Rightarrow> ll_assn" where
  "rbt_assn_ext ATEmpty ex p = \<up>(p = null)"
| "rbt_assn_ext (ATBranch c k v ci li ki vi ri l r) ex p =
    (
      \<upharpoonleft>ll_bpto (RBT_NODE ci li ki vi ri) p **
      color_assn c ci **
      rbt_assn_ext l ex li **
      \<upharpoonleft>key_assn k ki **
      \<upharpoonleft>value_assn v vi unless (k, VALUE_EX) \<in> ex **
      rbt_assn_ext r ex ri
    )"
declare rbt_assn_ext.simps(2)[simp del]
lemmas rbt_assn_ext_unfold = rbt_assn_ext.simps(2)


lemma rbt_assn_ext_null [simp]: 
  "rbt_assn_ext t ex null = \<up>(t =  ATEmpty)"
  apply (cases t)
  using rbt_assn_ext_unfold apply auto
  done

lemma rbt_assn_ext_empty_set_null [simp]:
  "rbt_assn_ext t {} null = \<up>(t  = ATEmpty)" by simp


subsection \<open>Load Rules\<close>


lemma load_rbt [vcg_rules]:
  "
    llvm_htriple
    (rbt_assn_ext (ATBranch c k v ci li ki vi ri l r) ex ti)
    (ll_load ti)
    (\<lambda>res.
      rbt_assn_ext (ATBranch c k v ci li ki vi ri l r) ex ti **
      \<up>(res = RBT_NODE ci li ki vi ri)
    )
  "
  unfolding rbt_assn_ext_unfold
  apply vcg
  done


lemma load_rbt_non_null:
  "
    ti \<noteq> null \<Longrightarrow>
    llvm_htriple
    (rbt_assn_ext t {} ti)
    (ll_load ti)
    (\<lambda>res.
      EXS ci li ki vi ri c l k v r.
      rbt_assn_ext t {} ti **
      \<up>(t = (ATBranch c k v ci li ki vi ri l r)) **
      \<up>(res = RBT_NODE ci li ki vi ri)
    )
  "
  apply vcg
  apply (cases t)
  subgoal by simp (*contradiction*)
  subgoal by vcg
  done

subsection \<open>Reduction Rules\<close>

lemma unfold_rbt_assn_ext_red_rule_1 [fri_red_rules]:
  "
    is_sep_red
    (\<upharpoonleft>ll_bpto (RBT_NODE ci li ki vi ri) ti)
    (
        \<upharpoonleft>ll_bpto (RBT_NODE ci li ki vi ri) ti **
        color_assn c ci **
        rbt_assn_ext l ex li **
        \<upharpoonleft>key_assn k ki **
        \<upharpoonleft>value_assn v vi unless (k, VALUE_EX) \<in> ex **
        rbt_assn_ext r ex ri
    )
    (\<upharpoonleft>ll_bpto (RBT_NODE ci li ki vi ri) ti)
    (rbt_assn_ext (ATBranch c k v ci li ki vi ri l r) ex ti)
  "
  apply (rule is_sep_redI)
  unfolding rbt_assn_ext_unfold
  apply simp
  done

lemma unfold_rbt_assn_ext_red_rule_2 [fri_red_rules]:
  "
    is_sep_red
    (\<upharpoonleft>ll_bpto (RBT_NODE ci li ki vi ri) ti unless cond)
    (
        \<upharpoonleft>ll_bpto (RBT_NODE ci li ki vi ri) ti **
        color_assn c ci **
        rbt_assn_ext l ex li **
        \<upharpoonleft>key_assn k ki **
        \<upharpoonleft>value_assn v vi unless (k, VALUE_EX) \<in> ex **
        rbt_assn_ext r ex ri
    )
    (\<upharpoonleft>ll_bpto (RBT_NODE ci li ki vi ri) ti unless cond)
    (rbt_assn_ext (ATBranch c k v ci li ki vi ri l r) ex ti)
  "
  apply (rule is_sep_redI)
  unfolding rbt_assn_ext_unfold
  apply simp
  done


lemma rbt_assn_ext_key_assn_unfold [fri_red_rules]: 
  "
    is_sep_red
    (
      \<upharpoonleft>ll_bpto (RBT_NODE ci li ki vi ri) ti \<and>*
      color_assn c ci \<and>* rbt_assn_ext l {} li \<and>*
      \<upharpoonleft>value_assn v vi \<and>*
      rbt_assn_ext r {} ri)
    \<box>
    (rbt_assn_ext (ATBranch c k v ci li ki vi ri l r) {} ti)
    (\<upharpoonleft>key_assn k ki)
  "
  apply (rule is_sep_redI)
  unfolding rbt_assn_ext_unfold
  apply simp
  subgoal premises prems
    apply (sep isep_dest: prems)
    done
  done


lemma rbt_assn_ext_color_assn_unfold [fri_red_rules]: 
  "
    is_sep_red
    (
      \<upharpoonleft>ll_bpto (RBT_NODE ci li ki vi ri) ti \<and>*
      rbt_assn_ext l {} li \<and>*
      \<upharpoonleft>key_assn k ki **
      \<upharpoonleft>value_assn v vi \<and>*
      rbt_assn_ext r {} ri)
    \<box>
    (rbt_assn_ext (ATBranch c k v ci li ki vi ri l r) {} ti)
    (color_assn c ci)
  "
  apply (rule is_sep_redI)
  unfolding rbt_assn_ext_unfold
  apply simp
  subgoal premises prems
    apply (sep isep_dest: prems)
    done
  done


lemma rbt_assn_ext_pto_assn_unfold [fri_red_rules]:
  "
    is_sep_red
    (
      color_assn c ci **
      rbt_assn_ext l {} li \<and>*
      \<upharpoonleft>key_assn k ki **
      \<upharpoonleft>value_assn v vi \<and>*
      rbt_assn_ext r {} ri)
    \<box>
    (rbt_assn_ext (ATBranch c k v ci li ki vi ri l r) {} ti)
    (\<upharpoonleft>ll_bpto (RBT_NODE ci li ki vi ri) ti)
  "
  apply (rule is_sep_redI)
  unfolding rbt_assn_ext_unfold
  apply simp
  subgoal premises prems
    apply (sep isep_dest: prems)
    done
  done


lemma rbt_assn_ext_left_assn_unfold [fri_red_rules]:
  "
    is_sep_red
    (
      \<upharpoonleft>ll_bpto (RBT_NODE ci li ki vi ri) ti **
      color_assn c ci **
      \<upharpoonleft>key_assn k ki **
      \<upharpoonleft>value_assn v vi unless (k, VALUE_EX) \<in> ex \<and>*
      rbt_assn_ext r ex ri)
    \<box>
    (rbt_assn_ext (ATBranch c k v ci li ki vi ri l r) ex ti)
    (rbt_assn_ext l ex li)
  "
  apply (rule is_sep_redI)
  unfolding rbt_assn_ext_unfold
  apply simp
  subgoal premises prems
    apply (sep isep_dest: prems)
    done
  done

lemma rbt_assn_ext_right_assn_unfold [fri_red_rules]:
  "
    is_sep_red
    (
      \<upharpoonleft>ll_bpto (RBT_NODE ci li ki vi ri) ti **
      color_assn c ci **
      rbt_assn_ext l ex li **
      \<upharpoonleft>key_assn k ki **
      \<upharpoonleft>value_assn v vi unless (k, VALUE_EX) \<in> ex
    )
    \<box>
    (rbt_assn_ext (ATBranch c k v ci li ki vi ri l r) ex ti)
    (rbt_assn_ext r ex ri)
  "
  apply (rule is_sep_redI)
  unfolding rbt_assn_ext_unfold
  apply simp
  subgoal premises prems
    apply (sep isep_dest: prems)
    done
  done

subsection \<open>Empty Constructor\<close>

lemma empty_correct_ext [vcg_rules]: 
  "llvm_htriple
   \<box>
   empty
   (\<lambda>res_ti. rbt_assn_ext ATEmpty {} res_ti)"
  unfolding empty_def
  by vcg

end

end