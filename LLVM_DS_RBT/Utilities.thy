theory Utilities
  imports 
    Setup
    Bool_Assn_Setup
begin


context rbt_impl
begin
interpretation rbt_impl_deps .


lemma pure_part_split_conjE:
  fixes A B
  assumes "pure_part (A ** B)"
  obtains
    "pure_part A"
    "pure_part B"
  using assms
  by (blast dest: pure_part_split_conj)

lemma rbt_assn_non_null_def:
  assumes 
    "pure_part (\<upharpoonleft>rbt_assn t ti)"
  shows
    "ti = null \<longleftrightarrow> (t = rbt.Empty)"
  using assms
  apply (cases t)
  subgoal by simp
  subgoal unfolding rbt_assn_branch_def by fastforce
  done

lemma rbt_assn_non_null_unfold:
  assumes 
    "ti \<noteq> null"
    "pure_part (\<upharpoonleft>rbt_assn t ti)"
  obtains c l k v r where
  "t = (rbt.Branch c l k v r)"
  using assms rbt_assn_non_null_def
  by (cases t; auto)


lemma non_null_rbt_assn_sepD:
  "ti \<noteq> null \<Longrightarrow> \<upharpoonleft>rbt_assn t ti \<turnstile> (EXS c l k v r. \<upharpoonleft>rbt_assn (rbt.Branch c l k v r) ti)"
  apply (cases t)
  subgoal by simp
  subgoal by isep_solver
  done                  


lemma extract_pure: "STATE asf X s \<Longrightarrow> (pure_part X \<Longrightarrow> thesis) \<Longrightarrow> thesis"
  by (meson STATE_def pure_partI)


subsubsection \<open>Macros\<close>


definition If_ll :: 
  "1 word llM \<Rightarrow> 'a llM \<Rightarrow> 'a llM \<Rightarrow> 'a llM" 
  ("(if! (_)/ then! (_)/ else! (_))" [0, 0, 10] 10) where
  "If_ll condf truef elsef = do {
    cond \<leftarrow> condf;
    if cond = 1
    then truef
    else elsef
  }"


lemma If_ll_mono[partial_function_mono]:
  assumes
    "monotone (fun_ord Mle) Mle C" and
    "monotone (fun_ord Mle) Mle F" and
    "monotone (fun_ord Mle) Mle G"
  shows
    "monotone (fun_ord Mle) Mle (\<lambda>f. if! C f then! F f else! G f)"
  unfolding If_ll_def
  apply (tactic \<open>Partial_Function.mono_tac @{context} 1\<close>)
  using assms apply simp_all
  done


definition sc_and (infixl "&&!" 35) where
  "sc_and a b \<equiv> do {
    if! a
    then! b
    else! return 0
  }"


definition sc_or (infixl "||!" 30) where
  "sc_or a b \<equiv> do {
    if! a
    then! return 1
    else! b
  }"


lemmas [simp, llvm_pre_simp] = If_ll_def sc_and_def sc_or_def


subsection \<open>Functions\<close>


definition "is_red node_p \<equiv> do {
    if node_p = null
    then return 0
    else do {
      node \<leftarrow> ll_load node_p;
      return from_bool (rbt_node.color node = 0)
    }
  }"


lemma is_red_correct [vcg_rules]:
  "
    llvm_htriple
    (\<upharpoonleft>rbt_assn t ti)
    (is_red ti)
    (\<lambda>r. \<upharpoonleft>bool.assn (rbt_is_red t) r ** \<upharpoonleft>rbt_assn t ti) 
  "
proof(cases t)
  case Empty
  then show ?thesis 
    unfolding is_red_def rbt_is_red_def
    by vcg
next
  case (Branch col lhs k v rhs)
  then show ?thesis
    apply (simp add: rbt_assn_branch_def rbt_is_red_def is_red_def)
    apply (cases col)
    apply vcg
    done
qed


definition "left node_p \<equiv> do {
    node \<leftarrow> ll_load node_p;
    return rbt_node.left node
}"


lemma left_correct [vcg_rules]:
  "
    llvm_htriple
    (\<upharpoonleft>rbt_assn (Branch col lhs k v rhs) ni)
    (left ni)
    (\<lambda>lhsi.
      EXS coli ki vi rhsi. 
        \<upharpoonleft>ll_bpto (RBT_NODE coli lhsi ki vi rhsi) ni **
        color_assn col coli **
        \<upharpoonleft>rbt_assn lhs lhsi **
        \<upharpoonleft>key_assn k ki **
        \<upharpoonleft>value_assn v vi **  
        \<upharpoonleft>rbt_assn rhs rhsi
    )
  "
  unfolding left_def
  by vcg


definition "right node_p \<equiv> do {
    node \<leftarrow> ll_load node_p;
    return rbt_node.right node
}"


lemma right_correct [vcg_rules]:
  "
    llvm_htriple
    (\<upharpoonleft>rbt_assn (Branch col lhs k v rhs) ni)
    (right ni)
    (\<lambda>rhsi.
      EXS coli lhsi ki vi. 
        \<upharpoonleft>ll_bpto (RBT_NODE coli lhsi ki vi rhsi) ni **
        color_assn col coli **
        \<upharpoonleft>rbt_assn lhs lhsi **
        \<upharpoonleft>key_assn k ki **
        \<upharpoonleft>value_assn v vi **  
        \<upharpoonleft>rbt_assn rhs rhsi
    )
  "
  unfolding right_def
  by vcg


definition "is_branch node_p \<equiv> Mreturn (from_bool (node_p \<noteq> null))"


lemma is_branch_correct [vcg_rules]:
  "
    llvm_htriple
    (\<upharpoonleft>rbt_assn t ti)
    (is_branch ti)
    (\<lambda>r. \<upharpoonleft>bool.assn(rbt_is_branch t) r ** \<upharpoonleft>rbt_assn t ti) 
  "
  unfolding is_branch_def rbt_is_branch_def
  apply (cases t; vcg)
  apply (simp add: bool_assn_pure_eq)
  apply vcg
  done
  
  


definition "is_black node_p \<equiv>
  Mreturn (from_bool (node_p = null)) ||!
  do {
    node \<leftarrow> ll_load node_p;
    return from_bool (rbt_node.color node = 1)
  }"


lemma is_black_correct [vcg_rules]:
  "
    llvm_htriple
    (\<upharpoonleft>rbt_assn t ti)
    (is_black ti)
    (\<lambda>r. \<upharpoonleft>bool.assn (rbt_is_black t) r ** \<upharpoonleft>rbt_assn t ti) 
  "
  unfolding is_black_def rbt_is_black_def
  apply (cases t; (auto split: color.splits))
  by vcg


definition "is_black_branch node_p \<equiv> 
  Mreturn (from_bool (node_p \<noteq> null)) &&! 
  do {
    node \<leftarrow> ll_load node_p;
    return from_bool (rbt_node.color node = 1)
  }"


lemma is_black_branch_correct [vcg_rules]:
  "
    llvm_htriple
    (\<upharpoonleft>rbt_assn t ti)
    (is_black_branch ti)
    (\<lambda>r. \<upharpoonleft>bool.assn(rbt_is_black t \<and> rbt_is_branch t) r ** \<upharpoonleft>rbt_assn t ti) 
  "
  unfolding is_black_branch_def rbt_is_black_def rbt_is_branch_def
  apply (cases t; (auto split: color.splits))
  by vcg


definition "new x \<equiv> do {
    ptr \<leftarrow> ll_balloc;
    ll_store x ptr;
    return ptr
  }"


lemma new_correct [vcg_rules]:
  "
    llvm_htriple
    \<box>
    (new x)
    (\<lambda>r. \<upharpoonleft>ll_bpto x r)
  "
  unfolding new_def
  by vcg


lemmas [llvm_inline] = 
  is_red_def
  left_def
  right_def
  new_def


datatype ColorPattern = CP_Var | CP_R | CP_B
datatype RbtPattern = RVar | Empty | Branch ColorPattern RbtPattern RbtPattern


fun matches_color_pattern_i ::
  "ColorPattern \<Rightarrow> 8 word \<Rightarrow> 1 word llM" where
  "matches_color_pattern_i CP_Var c = Mreturn ll_True"
| "matches_color_pattern_i CP_R c = Mreturn (from_bool (c = 0))"
| "matches_color_pattern_i CP_B c = Mreturn (from_bool (c = 1))"


fun matches_color_pattern ::
  "ColorPattern \<Rightarrow> color \<Rightarrow> bool" where
  "matches_color_pattern CP_Var c = True"
| "matches_color_pattern CP_R c = (c = color.R)"
| "matches_color_pattern CP_B c = (c = color.B)"
  

fun matches_rbt_pattern ::
  "RbtPattern \<Rightarrow> ('k, 'v) rbt \<Rightarrow> bool" where
  "matches_rbt_pattern RVar t = True"
| "matches_rbt_pattern Empty t = (t = rbt.Empty)"
| "matches_rbt_pattern (Branch c l r) rbt.Empty = False"
| "matches_rbt_pattern (Branch cp lp rp) (rbt.Branch c l _ _ r) = 
  (matches_color_pattern cp c \<and> matches_rbt_pattern lp l \<and> matches_rbt_pattern rp r)"


fun matches_rbt_pattern_i ::
  "RbtPattern \<Rightarrow> ('ki, 'vi) rbti \<Rightarrow> 1 word llM" where
  "matches_rbt_pattern_i RVar t = Mreturn ll_True"
| "matches_rbt_pattern_i Empty t = Mreturn (from_bool (t = null))"
| "matches_rbt_pattern_i (Branch c l r) t = do {
    if t = null then return ll_False
    else do {
      node \<leftarrow> ll_load t;
      case node of (RBT_NODE ci li ki v ri) \<Rightarrow> 
      do {
        c_check \<leftarrow> matches_color_pattern_i c ci;
        l_check \<leftarrow> matches_rbt_pattern_i l li;
        r_check \<leftarrow> matches_rbt_pattern_i r ri;
        return c_check && l_check && r_check
      }
    }
  }"


lemma matches_color_pattern_correct [vcg_rules]:
"
  llvm_htriple
  (color_assn c ci)
  (matches_color_pattern_i pat ci)
  (\<lambda>r. \<upharpoonleft>bool.assn (matches_color_pattern pat c) r)
"
  apply(cases pat; cases c)
  apply vcg
  done


lemma H3: "pure_part (\<upharpoonleft>rbt_assn t ti) \<Longrightarrow> (ti = null) = (t = rbt.Empty)"
  apply (cases ti)
  apply auto
  done


method STATE_extract_pure = 
  rule extract_pure,
  (auto)[1],
  ((erule pure_part_split_conjE)+)?
term bool.assn

lemma 
  Hack_1:
  "(standard_opr_abstraction.assn (\<lambda>a::1 word. a = 1) (\<lambda>_. True)) = bool.assn"
  by (metis from_bool_1 from_bool_to_bool1)


lemma 
  bool_assn_conj_cong_sepI:
  "\<upharpoonleft>bool.assn A X ** \<upharpoonleft>bool.assn B Y \<turnstile> \<upharpoonleft>bool.assn (A \<and> B) (X && Y)"
  apply (auto simp only: bool_assn_pure_eq)
  apply isep_solver
  apply auto
  done
  

lemma matches_rbt_pattern_correct [vcg_rules]:
"
  llvm_htriple
  (\<upharpoonleft>rbt_assn t ti)
  (matches_rbt_pattern_i pat ti)
  (\<lambda>r. \<upharpoonleft>bool.assn (matches_rbt_pattern pat t) r ** \<upharpoonleft>rbt_assn t ti)
"
proof(induction pat arbitrary: t ti)
  case RVar
  then show ?case 
    apply vcg
    apply (subst Hack_1) (*!FIX!*)
    apply vcg
    done
next
  case Empty
  then show ?case
    apply vcg
    apply (subst Hack_1) (*!FIX!*)
    apply vcg_compat
    apply isep_extract_pure
    apply (auto simp add: rbt_assn_non_null_def bool_assn_pure_eq)
     apply (isep_solver_keep | simp)+
    done
next
  case (Branch x1 pat1 pat2)

  note [vcg_rules] = Branch
  
  show "?case"
    apply vcg
    subgoal
      apply (subst Hack_1) (*!FIX!*)
      (* apply vcg_try_solve *) (*!FIX! annoying tags*)
      apply (simp add: bool_assn_pure_eq)
      apply vcg
      done
    subgoal
      apply vcg
      apply STATE_extract_pure
      apply (rule rbt_assn_non_null_unfold, auto)
      apply vcg
      apply (subst Hack_1)
      apply vcg_compat
      apply (isep_rule rule: bool_assn_conj_cong_sepI)
      apply (isep_rule rule: bool_assn_conj_cong_sepI)
      apply (rule ENTAILSD)
      apply vcg
      done
    done
qed


lemma matches_rbt_pattern_var_E:
  assumes 
    "matches_rbt_pattern RVar t" and 
    "thesis"
  shows "thesis"
  using assms by simp


lemma matches_rbt_pattern_empty_E:
  assumes 
    "matches_rbt_pattern Empty t" and 
    "t = rbt.Empty \<Longrightarrow> thesis"
  shows "thesis"
  using assms by simp


lemma matches_rbt_pattern_branch_E:
  assumes                  
    "matches_rbt_pattern (Branch cp lp rp) t" 
  obtains c l k v r
  where 
    "t = rbt.Branch c l k v r" and
    "matches_color_pattern cp c" and
    "matches_rbt_pattern lp l" and
    "matches_rbt_pattern rp r"
  using assms by (cases t, auto)


lemmas matches_rbt_pattern_unfold_elims = 
  matches_rbt_pattern_var_E
  matches_rbt_pattern_empty_E
  matches_rbt_pattern_branch_E


lemmas [simp del] = matches_rbt_pattern_i.simps


lemmas [llvm_pre_simp] =
  matches_rbt_pattern_i.simps
  matches_color_pattern_i.simps
  


method resolve_rbt_pat_mat =
  (auto elim!: matches_rbt_pattern.elims(1-2))[1]


end


end