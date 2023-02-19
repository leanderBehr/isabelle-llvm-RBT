theory Utilities
  imports 
    Setup
    Bool_Assn_Setup
begin


context rbt_impl
begin
interpretation rbt_impl_deps .

subsection \<open>STATE pure part extraction\<close>

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
    "pure_part (rbt_assn t ti)"
  shows
    "ti = null \<longleftrightarrow> (t = rbt.Empty)"
  using assms
  apply (cases t)
  subgoal by (auto elim: pure_part_split_conjE)
  subgoal by auto
  done

lemma extract_pure: "STATE asf X s \<Longrightarrow> (pure_part X \<Longrightarrow> thesis) \<Longrightarrow> thesis"
  by (meson STATE_def pure_partI)


subsection \<open>Macros\<close>


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


subsection \<open>Pattern Matching Emulation\<close>


definition is_red :: "_ \<Rightarrow> 1 word llM" where
  "is_red node_p \<equiv> do {
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
    (rbt_assn t ti)
    (is_red ti)
    (\<lambda>r. \<upharpoonleft>bool.assn (rbt_is_red t) r ** rbt_assn t ti) 
  "
proof(cases t)
  case Empty
  then show ?thesis 
    unfolding is_red_def rbt_is_red_def
    by vcg
next
  case (Branch col lhs k v rhs)
  then show ?thesis
    apply (simp add: rbt_is_red_def is_red_def)
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
  (\<upharpoonleft>ll_bpto (RBT_NODE ci li ki vi ri) n_p)
  (left n_p)
  (\<lambda>res. \<up>(res = li) ** \<upharpoonleft>ll_bpto (RBT_NODE ci li ki vi ri) n_p)
"
  unfolding left_def
  by vcg


lemma left_correct_unfolding [vcg_rules]:
  "
    llvm_htriple
    (rbt_assn (Branch col lhs k v rhs) ni)
    (left ni)
    (\<lambda>lhsi.
      (
      EXS coli ki vi rhsi. 
        \<upharpoonleft>ll_bpto (RBT_NODE coli lhsi ki vi rhsi) ni **
        color_assn col coli **
        rbt_assn lhs lhsi **
        \<upharpoonleft>key_assn k ki **
        \<upharpoonleft>value_assn v vi **  
        rbt_assn rhs rhsi
      )
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
  (\<upharpoonleft>ll_bpto (RBT_NODE ci li ki vi ri) n_p)
  (right n_p)
  (\<lambda>res. \<up>(res = ri) ** \<upharpoonleft>ll_bpto (RBT_NODE ci li ki vi ri) n_p)
"
  unfolding right_def
  by vcg


lemma right_correct_unfolding [vcg_rules]:
  "
    llvm_htriple
    (rbt_assn (Branch col lhs k v rhs) ni)
    (right ni)
    (\<lambda>rhsi.
      (
      EXS coli lhsi ki vi. 
        \<upharpoonleft>ll_bpto (RBT_NODE coli lhsi ki vi rhsi) ni **
        color_assn col coli **
        rbt_assn lhs lhsi **
        \<upharpoonleft>key_assn k ki **
        \<upharpoonleft>value_assn v vi **  
        rbt_assn rhs rhsi
      )
    )
  "
  unfolding right_def
  by vcg


definition "is_branch node_p \<equiv> Mreturn (from_bool (node_p \<noteq> null))"


lemma is_branch_correct [vcg_rules]:
  "
    llvm_htriple
    (rbt_assn t ti)
    (is_branch ti)
    (\<lambda>r. \<upharpoonleft>bool.assn(rbt_is_branch t) r ** rbt_assn t ti) 
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
    (rbt_assn t ti)
    (is_black ti)
    (\<lambda>r. \<upharpoonleft>bool.assn (rbt_is_black t) r ** rbt_assn t ti) 
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
    (rbt_assn t ti)
    (is_black_branch ti)
    (\<lambda>r. \<upharpoonleft>bool.assn(rbt_is_black t \<and> rbt_is_branch t) r ** rbt_assn t ti) 
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


end

text_raw \<open>\snip{patterndef}{1}{2}{%\<close>
datatype ColorPattern = CP_Var | CP_R | CP_B
datatype RbtPattern = RP_Var | RP_Empty | RP_Branch ColorPattern RbtPattern RbtPattern
text_raw \<open>}%endsnip\<close>

fun ll_matches_color ::
  "ColorPattern \<Rightarrow> 8 word \<Rightarrow> 1 word llM" where
  "ll_matches_color CP_Var c = Mreturn ll_True"
| "ll_matches_color CP_R c = Mreturn (from_bool (c = 0))"
| "ll_matches_color CP_B c = Mreturn (from_bool (c = 1))"


fun matches_color ::
  "ColorPattern \<Rightarrow> color \<Rightarrow> bool" where
  "matches_color CP_Var c = True"
| "matches_color CP_R c = (c = color.R)"
| "matches_color CP_B c = (c = color.B)"
  

fun matches_rbt ::
  "RbtPattern \<Rightarrow> ('k, 'v) rbt \<Rightarrow> bool" where
  "matches_rbt RP_Var t = True"
| "matches_rbt RP_Empty t = (t = rbt.Empty)"
| "matches_rbt (RP_Branch c l r) rbt.Empty = False"
| "matches_rbt (RP_Branch cp lp rp) (rbt.Branch c l _ _ r) = 
  (matches_color cp c \<and> matches_rbt lp l \<and> matches_rbt rp r)"


context rbt_impl
begin
interpretation rbt_impl_deps .


text_raw \<open>\snip{llmatchesrbtdef}{1}{2}{%\<close>
fun ll_matches_rbt ::
  "RbtPattern \<Rightarrow> ('ki, 'vi) rbti \<Rightarrow> 1 word llM" where
  "ll_matches_rbt RP_Var _ = (return ll_True)"
| "ll_matches_rbt RP_Empty n_p = (return from_bool (n_p = null))"
| "ll_matches_rbt (RP_Branch c l r) n_p = do {
    if n_p = null then return ll_False
    else do {
      n \<leftarrow> ll_load n_p;
      case n of (RBT_NODE ci li _ _ ri) \<Rightarrow>
        ll_matches_color c ci &&!
        ll_matches_rbt l li &&!  
        ll_matches_rbt r ri
    }
  }"
text_raw \<open>}%endsnip\<close>


lemma matches_color_correct [vcg_rules]:
"
  llvm_htriple
  (color_assn c ci)
  (ll_matches_color pat ci)
  (\<lambda>r. \<upharpoonleft>bool.assn (matches_color pat c) r ** color_assn c ci)
"
  apply(cases pat; cases c)
  apply vcg
  done


method STATE_extract_pure = 
  rule extract_pure,
  (auto)[1],
  ((erule pure_part_split_conjE)+)?


lemma 
  Hack_1:
  "(standard_opr_abstraction.assn (\<lambda>a::1 word. a = 1) (\<lambda>_. True)) = bool.assn"
  by (metis from_bool_1 from_bool_to_bool1)


lemma 
  bool_assn_conj_cong_sepI:
  "\<upharpoonleft>bool.assn A X ** \<upharpoonleft>bool.assn B Y \<turnstile> \<upharpoonleft>bool.assn (A \<and> B) (X && Y)"
  apply (auto simp only: bool_assn_pure_eq)
  apply (sepwith auto)
  done
  

lemma matches_rbt_correct [vcg_rules]:
"
  llvm_htriple
  (rbt_assn t ti)
  (ll_matches_rbt pat ti)
  (\<lambda>r. \<upharpoonleft>bool.assn (matches_rbt pat t) r ** rbt_assn t ti)
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
    apply (auto simp add: rbt_assn_non_null_def bool_assn_pure_eq)
     apply (sepwith simp)+
    done
next
  case (RP_Branch x1 pat1 pat2)

  note [vcg_rules] = RP_Branch
  
  show "?case"
    apply vcg
    subgoal
      apply (subst Hack_1) (*!FIX!*)
      (* apply vcg_try_solve *) (*!FIX! annoying tags*)
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


lemmas [simp del] = ll_matches_rbt.simps


lemmas [llvm_pre_simp] =
  ll_matches_rbt.simps
  ll_matches_color.simps
 

method resolve_rbt_pat_mat =
  (auto elim!: matches_rbt.elims(1-2))[1]


end


end