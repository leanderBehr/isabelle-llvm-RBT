theory Abstract_Rbt
  imports "HOL-Library.RBT_Impl"
begin

abbreviation "rbt_balance \<equiv> RBT_Impl.balance"
abbreviation "rbt_balance_left \<equiv> RBT_Impl.balance_left"
abbreviation "rbt_balance_right \<equiv> RBT_Impl.balance_right"
abbreviation "rbt_combine \<equiv> RBT_Impl.combine"

hide_const balance
hide_const balance_left
hide_const balance_right
hide_const combine


subsection \<open>Rbt Utilities\<close>


definition "rbt_is_red tree \<equiv> 
  case tree of
    (Branch color.R _ _ _ _ ) \<Rightarrow> True |
    _ \<Rightarrow> False
"


lemma rbt_is_red_unfold_branch [elim!]:
  assumes "rbt_is_red tree"
  obtains lhs k v rhs where "tree = Branch color.R lhs k v rhs"
  using assms
  unfolding rbt_is_red_def
  apply (cases tree)
  subgoal by auto
  subgoal for c  by (cases c; auto)
  done


definition "rbt_is_black tree \<equiv> 
  case tree of
    (rbt.Branch color.B _ _ _ _ ) \<Rightarrow> True |
    rbt.Empty \<Rightarrow> True |
    _ \<Rightarrow> False
"


lemma rbt_is_black_cases [elim!]:
  assumes
    "rbt_is_black tree"
    "tree = rbt.Empty \<Longrightarrow> thesis"
    "EX l k v r. tree = (rbt.Branch color.B l k v r) \<Longrightarrow> thesis"
  shows "thesis"
  using assms
  unfolding rbt_is_black_def
  by (auto split: color.splits rbt.splits)
  

lemma rbt_is_black_branchE [elim!]:
  assumes 
    "rbt_is_black (rbt.Branch c l k v r)"
    "c = color.B \<Longrightarrow> thesis"
  shows "thesis"
  using assms by auto


definition "rbt_is_branch tree \<equiv> 
  (case tree of rbt.Empty \<Rightarrow> False | _ \<Rightarrow> True)"


lemma rbt_is_branch_unfold [elim!]:
  assumes "rbt_is_branch tree"
  obtains c lhs k v rhs where "tree = Branch c lhs k v rhs"
  using assms
  unfolding rbt_is_branch_def
  by (cases tree; auto)


definition "rbt_left node \<equiv> case node of (Branch _ lhs _ _ _) \<Rightarrow> lhs" 
definition "rbt_right node \<equiv> case node of (Branch _ _ _ _ rhs) \<Rightarrow> rhs"


end