theory Insert_Opt
  imports 
    "../Insert"
    Balance_Opt
begin

context rbt_impl
begin
interpretation rbt_impl_deps .

definition "balance_black n_p c \<equiv> do { if c = 1 then balance_opt n_p else return n_p }"

lemmas [llvm_inline] = balance_black_def

partial_function (M) insert'_opt ::
  "'ki \<Rightarrow> 'vi \<Rightarrow> ('ki, 'vi) rbti \<Rightarrow> ('ki, 'vi) rbti llM" where
  "insert'_opt k\<^sub>n v\<^sub>n n_p =
  do {
    if n_p = null
    then new (RBT_NODE 0 null k\<^sub>n v\<^sub>n null)
    else
    do {
      n \<leftarrow> ll_load n_p;
      case n of (RBT_NODE c l_p k v r_p) \<Rightarrow>      
      do {
          if! lt_impl k\<^sub>n k
          then! do {l_p\<^sub>n \<leftarrow> insert'_opt k\<^sub>n v\<^sub>n l_p; set_left_p l_p\<^sub>n n_p; balance_black n_p c}
          else! if! lt_impl k k\<^sub>n
          then! do {r_p\<^sub>n \<leftarrow> insert'_opt k\<^sub>n v\<^sub>n r_p; set_right_p r_p\<^sub>n n_p; balance_black n_p c}
          else! do {key_free k; value_free v;
                    set_key_p k\<^sub>n n_p; set_value_p v\<^sub>n n_p;
                    return n_p}
      }     
    }
  }"

lemmas [llvm_code] = insert'_opt.simps

lemma insert'_opt_correct:
  "
    llvm_htriple
    (rbt_assn tree treei ** \<upharpoonleft>key_assn k ki ** \<upharpoonleft>value_assn v vi)
    (insert'_opt ki vi treei)
    (\<lambda>r. rbt_assn ((rbt_ins (\<lambda>_ _ v. v)) k v tree) r)
  "
proof (induction k v tree arbitrary: treei ki v rule: rbt_insert_ad'.induct)
  case (1 k\<^sub>n v\<^sub>n)
  then show ?case
    apply (subst insert'_opt.simps)
    apply vcg
    done
next
  case (2 k\<^sub>n v\<^sub>n l k v r)
  
  note [vcg_rules] = 2

  show ?case
    apply (subst insert'_opt.simps)
    unfolding balance_black_def
    apply vcg
    done
next
  case (3 k\<^sub>n v\<^sub>n l k v r)

  note [vcg_rules] = 3

  show ?case
    apply (subst insert'_opt.simps)
    unfolding balance_black_def
    apply vcg
    done
qed



lemma rbt_ins_non_empty:
  "rbt_ins f k v t \<noteq> rbt.Empty"
  apply (induction f k v t rule: rbt_ins.induct)
  subgoal by simp
  subgoal using rbt_balance_non_empty by (simp, fast)
  subgoal by simp
  done

definition insert_opt where
  "insert_opt k v n_p \<equiv>
  do {
    r_p \<leftarrow> insert'_opt k v n_p;
    set_color_p 1 r_p;
    return r_p
  }"

lemmas [llvm_code] = insert_opt_def

lemma insert_opt_correct [vcg_rules]:
  "
    llvm_htriple
    (rbt_assn tree treei ** \<upharpoonleft>key_assn k ki ** \<upharpoonleft>value_assn v vi)
    (insert_opt ki vi treei)
    (\<lambda>r. rbt_assn (rbt_insert k v tree) r)
  " 
  unfolding insert_opt_def rbt_insert_def rbt_insert_with_key_def paint_def
  supply insert'_opt_correct[vcg_rules]
  apply vcg
  apply (cases "rbt_ins (\<lambda>_ _ v. v) k v tree")
  using rbt_ins_non_empty apply fast
  apply vcg
  done

end

end