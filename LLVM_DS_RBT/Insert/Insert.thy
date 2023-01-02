theory Insert
  imports Balance
begin


fun rbt_insert_ad' where
  "rbt_insert_ad' k\<^sub>n v\<^sub>n rbt.Empty = rbt.Branch color.R rbt.Empty k\<^sub>n v\<^sub>n rbt.Empty"
| "rbt_insert_ad' k\<^sub>n v\<^sub>n (rbt.Branch color.B l k v r) = (
    if k\<^sub>n < k then rbt_balance (rbt_insert_ad' k\<^sub>n v\<^sub>n l) k v r
    else if k\<^sub>n > k then rbt_balance l k v (rbt_insert_ad' k\<^sub>n v\<^sub>n r)
    else rbt.Branch color.B l k\<^sub>n v\<^sub>n r
  )"
| "rbt_insert_ad' k\<^sub>n v\<^sub>n (rbt.Branch color.R l k v r) = (
    if k\<^sub>n < k then rbt.Branch color.R (rbt_insert_ad' k\<^sub>n v\<^sub>n l) k v r
    else if k\<^sub>n > k then rbt.Branch color.R l k v (rbt_insert_ad' k\<^sub>n v\<^sub>n r)
    else rbt.Branch color.R l k\<^sub>n v\<^sub>n r
  )"


definition rbt_insert_ad where
  "rbt_insert_ad k v t = paint color.B (rbt_insert_ad' k v t)"


lemma rbt_insert_ad'_correct: 
  "rbt_insert_ad' k v t = rbt_ins (\<lambda>_ _ nv. nv) k v t"
  by (induction k v t rule: rbt_insert_ad'.induct; auto)
  
  
lemma rbt_insert_ad_correct:
  "rbt_insert_ad k v t = rbt_insert k v t"
  unfolding rbt_insert_def rbt_insert_ad_def rbt_insert_with_key_def
  using rbt_insert_ad'_correct 
  by (rule arg_cong)


context rbt_impl
begin 
interpretation rbt_impl_deps .

partial_function (M) insert' ::
  "'ki \<Rightarrow> 'vi \<Rightarrow> ('ki, 'vi) rbti \<Rightarrow> ('ki, 'vi) rbti llM" where
  "insert' k\<^sub>n v\<^sub>n n_p = do {
    if n_p = null
    then new (RBT_NODE 0 null k\<^sub>n v\<^sub>n null)
    else do {
      n \<leftarrow> ll_load n_p;
      ll_free n_p;
      case n of (RBT_NODE col l k v r) \<Rightarrow>      
      do {
        if col = 0
        then do {
          if! lt_impl k\<^sub>n k
          then! do { l\<^sub>n \<leftarrow> insert' k\<^sub>n v\<^sub>n l; new (RBT_NODE 0 l\<^sub>n k v r) }
          else! do {
            if! lt_impl k k\<^sub>n
            then! do { r\<^sub>n \<leftarrow> insert' k\<^sub>n v\<^sub>n r; new (RBT_NODE 0 l k v r\<^sub>n) }
            else! do {
              key_delete k;
              value_delete v;
              new (RBT_NODE 0 l k\<^sub>n v\<^sub>n r)
            }
          }
        }
        else do {
          if! lt_impl k\<^sub>n k                         
          then! do { l\<^sub>n \<leftarrow> insert' k\<^sub>n v\<^sub>n l; balance l\<^sub>n k v r }
          else! do {
            if! lt_impl k k\<^sub>n
            then! do { r\<^sub>n \<leftarrow> insert' k\<^sub>n v\<^sub>n r; balance l k v r\<^sub>n }
            else! do {
              key_delete k;
              value_delete v;
              new (RBT_NODE 1 l k\<^sub>n v\<^sub>n r)
            }
          }
        }
      }
    }
  }"


lemma insert'_correct:
  "
    llvm_htriple
    (rbt_assn tree treei ** \<upharpoonleft>key_assn k ki ** \<upharpoonleft>value_assn v vi)
    (insert' ki vi treei)
    (\<lambda>r. rbt_assn (rbt_insert_ad' k v tree) r)
  "
proof (induction k v tree arbitrary: treei ki v rule: rbt_insert_ad'.induct)
  case (1 k\<^sub>n v\<^sub>n)
  then show ?case
    apply (subst insert'.simps)
    apply vcg
    done
next
  case (2 k\<^sub>n v\<^sub>n l k v r)
  
  note [vcg_rules] = 2

  show ?case
    apply (subst insert'.simps)
    apply vcg
    done
next
  case (3 k\<^sub>n v\<^sub>n l k v r)

  note [vcg_rules] = 3

  show ?case
    apply (subst insert'.simps)
    apply vcg
    done
qed


lemmas [llvm_code] = insert'.simps


definition insert where 
  "insert k v tree \<equiv>
  do {
    r_p \<leftarrow> insert' k v tree;
    set_color_p 1 r_p;
    return r_p
  }"


lemma rbt_balance_non_empty:
  "rbt_balance l k v r \<noteq> rbt.Empty"
  by (induction l k v r rule: RBT_Impl.balance.induct, auto)


lemma rbt_insert_ad'_non_empty:
  "rbt_insert_ad' k v tree \<noteq> rbt.Empty"
  by(induction k v tree rule: rbt_insert_ad'.induct,
      simp_all add: rbt_balance_non_empty)

lemma insert_correct':
  "
    llvm_htriple
    (rbt_assn tree treei ** \<upharpoonleft>key_assn k ki ** \<upharpoonleft>value_assn v vi)
    (insert ki vi treei)
    (\<lambda>r. rbt_assn (rbt_insert_ad k v tree) r)
  "
  unfolding insert_def rbt_insert_ad_def
  supply insert'_correct[vcg_rules]
  apply vcg
  apply (cases "rbt_insert_ad' k v tree")
  subgoal using rbt_insert_ad'_non_empty by fast
  subgoal
    apply simp
    apply vcg
    done
  done


lemma insert_correct [vcg_rules]:
  "
    llvm_htriple
    (rbt_assn tree treei ** \<upharpoonleft>key_assn k ki ** \<upharpoonleft>value_assn v vi)
    (insert ki vi treei)
    (\<lambda>r. rbt_assn (rbt_insert k v tree) r)
  " 
  using insert_correct' rbt_insert_ad_correct by metis


lemmas [llvm_code] = insert_def


end


end