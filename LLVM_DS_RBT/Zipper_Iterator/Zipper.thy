theory Zipper
  imports
    "../Setup"
    "../Insert/Naive_Insert"
begin


datatype ('k, 'v) Parent = LParent color 'k 'v "('k, 'v) rbt" | RParent color "('k, 'v) rbt" 'k 'v


datatype ('k, 'v) td_zip = TDZ "('k, 'v) Parent list" "('k, 'v) rbt"
datatype ('k, 'v) bu_zip = BUZ "('k, 'v) Parent list" "('k, 'v) rbt"


definition "to_bu buz \<equiv> case buz of TDZ ps t \<Rightarrow> BUZ (rev ps) t"
definition "to_td tdz \<equiv> case tdz of BUZ ps t \<Rightarrow> TDZ (rev ps) t"


fun go_up :: "('k, 'v) bu_zip \<Rightarrow> ('k, 'v) bu_zip" where
  "go_up (BUZ (LParent c k v r # ps) t) = BUZ ps (rbt.Branch c t k v r)"
| "go_up (BUZ (RParent c l k v # ps) t) = BUZ ps (rbt.Branch c l k v t)"
| "go_up (BUZ [] _) = undefined"


fun go_left :: "('k, 'v) bu_zip \<Rightarrow> ('k, 'v) bu_zip" where
  "go_left (BUZ ps rbt.Empty) = undefined"
| "go_left (BUZ ps (rbt.Branch c l k v r)) = BUZ (LParent c k v r # ps) l"


fun go_right :: "('k, 'v) bu_zip \<Rightarrow> ('k, 'v) bu_zip" where
  "go_right (BUZ ps rbt.Empty) = undefined"
| "go_right (BUZ ps (rbt.Branch c l k v r)) = BUZ (RParent c l k v # ps) r"


(*required for termination proof of to_tree*)
lemma go_up_parents_length_dec [simp]:
  "size (go_up (BUZ (p # ps) t)) <
  Suc (Suc (size p + size_list size ps + size t))"
  by (cases p; simp)
  

fun to_tree :: "('k, 'v) bu_zip \<Rightarrow> ('k, 'v) rbt" where
  "to_tree (BUZ [] t) = t"
| "to_tree tdz = to_tree (go_up tdz)"


definition to_tree_td where "to_tree_td tdz = to_tree (to_bu tdz)"


lemmas [simp del] = go_up_parents_length_dec


fun zip_naive_insert' :: "('k::linorder, 'v) td_zip \<Rightarrow> 'k \<Rightarrow> 'v \<Rightarrow> ('k, 'v) td_zip" where
  "zip_naive_insert' (TDZ [] t) k v = TDZ [] (rbt_naive_insert t k v)"
| "zip_naive_insert' (TDZ (LParent c pk pv r # ps) t) k v = 
  (
    if k < pk
    then case zip_naive_insert' (TDZ ps t) k v of TDZ ps' t' \<Rightarrow> 
      TDZ (LParent c pk pv r # ps') t'
    else if pk < k
    then let r'=rbt_naive_insert r k v in TDZ (LParent c pk pv r' # ps) t
    else TDZ (LParent c pk pv r # ps) t
  )"
| "zip_naive_insert' (TDZ (RParent c l pk pv # ps) t) k v = 
  (
    if k < pk
    then let l'= rbt_naive_insert l k v in TDZ (RParent c l' pk pv # ps) t
    else if pk < k
    then case zip_naive_insert' (TDZ ps t) k v of TDZ ps' t' \<Rightarrow> 
      TDZ (RParent c l pk pv # ps') t'
    else TDZ (RParent c l pk pv # ps) t
  )"


fun zip_naive_insert where
  "zip_naive_insert tdz k v = to_bu (zip_naive_insert' (to_td tdz) k v)"


lemma to_tree_snoc_lparent [simp]:
  "to_tree (BUZ (ps @ [LParent c k v r]) t) = rbt.Branch c (to_tree (BUZ ps t)) k v r"
proof (induction ps arbitrary: t)
  case Nil
  then show ?case by simp
next
  case (Cons p ps)
  then show ?case by (cases p) auto
qed


lemma to_tree_snoc_rparent [simp]:
  "to_tree (BUZ (ps @ [RParent c l k v]) t) = rbt.Branch c l k v (to_tree (BUZ ps t))"
proof (induction ps arbitrary: t)
  case Nil
  then show ?case by simp
next
  case (Cons p ps)
  then show ?case by (cases p) auto
qed


lemma zip_naive_insert_correct:
  "to_tree (zip_naive_insert (BUZ ps t) k v) = rbt_naive_insert (to_tree (BUZ ps t)) k v"
proof(induction ps rule: rev_induct)
  case Nil
  then show ?case by (simp add: to_bu_def to_td_def)
next
  case (snoc p ps)
  then show ?case
  proof(cases p)
    case (LParent c pk pv r)
    show ?thesis
    proof(rule linorder_cases[of k pk], goal_cases)
      case 1
      with snoc LParent show ?case
        apply (simp add: to_bu_def to_td_def)
        apply (cases "zip_naive_insert' (TDZ (rev ps) t) k v")
        apply auto
        done
    qed (auto simp add: to_bu_def to_td_def snoc LParent)
  next
    case (RParent c l pk pv)
    show ?thesis
    proof(rule linorder_cases[of k pk], goal_cases)
      case 1
      with snoc RParent show ?case
        by (simp add: to_tree_snoc_rparent to_bu_def to_td_def)
    next
      case 2
      with snoc RParent show ?case
        by (simp add: to_tree_snoc_rparent to_bu_def to_td_def)
    next
      case 3
      with snoc RParent show ?case
        apply (cases "zip_naive_insert' (TDZ (rev ps) t) k v")
        by (simp add: to_tree_snoc_rparent to_bu_def to_td_def)
    qed
  qed
qed

end