theory Zipper
  imports 
    Setup
    "Insert/Naive_Insert"
    "Zipper_Iterator/Zipper"
    "Separation_Logic_Solver/Methods"
begin


context rbt_impl
begin
interpretation llvm_prim_ctrl_setup .
interpretation llvm_prim_arith_setup .
interpretation llvm_prim_setup .




(*

fun td_zip_assn ::
  "('k, 'v) td_zip \<Rightarrow> ('ki, 'v::llvm_rep) rbti \<Rightarrow> ('ki, 'v) rbti \<Rightarrow> ll_assn" where
  "td_zip_assn (TDZ [] t) ti iti = \<up>(iti = ti)"
| "td_zip_assn (TDZ (LParent c k v r # ps) t) ti iti = 
  (
    EXS ci li ki vi ri.
      \<upharpoonleft>ll_bpto (RBT_NODE ci li ki vi ri) ti **
      \<upharpoonleft>color_assn c ci **
      td_zip_assn (TDZ ps t) li iti **
      \<upharpoonleft>key_assn k ki **
      \<up>(v = vi) **
      rbt_assn r ri
  )
"
| "td_zip_assn (TDZ (RParent c l k v # ps) t) ti iti =
  (
    EXS ci li ki vi ri.
      \<upharpoonleft>ll_bpto (RBT_NODE ci li ki vi ri) ti **
      \<upharpoonleft>color_assn c ci **
      rbt_assn l li **
      \<upharpoonleft>key_assn k ki **
      \<up>(v = vi) **
      td_zip_assn (TDZ ps t) ri iti
  )"


fun zip_assn where 
  "zip_assn (BUZ ps t) ti iti = (td_zip_assn (to_td (BUZ ps t)) ti iti ** rbt_assn t iti)"


lemmas [simp del] = zip_assn.simps


definition "go_left_i n_p = 
  do {
    n \<leftarrow> ll_load n_p;
    return rbt_node.left n
  }
"



lemma td_zip_assn_go_leftI:
"
  td_zip_assn (TDZ ps (rbt.Branch c l k v r)) ti iti **

  \<upharpoonleft>ll_bpto (RBT_NODE ci li ki vi ri) iti **
  \<upharpoonleft>color_assn c ci **

  \<upharpoonleft>key_assn k ki **
  \<up>(vi = v) **
  rbt_assn r ri

  \<turnstile>

  td_zip_assn (TDZ (ps @ [LParent c k v r]) l) ti li
"
proof(induction ps arbitrary: ti)
  case Nil
  then show ?case
    apply simp
    apply isep_extract_pure
    apply simp
    apply isep_solver_keep
    apply simp_all
    done
next
  case (Cons p ps)
  then show ?case
    apply (cases p)
    subgoal premises prems for c k v r
      apply (simp add: prems(2))
      apply (isep_solver isep_dest: prems(1))
      done

    subgoal premises prems for c l k v
      apply (simp add: prems(2))
      apply (isep_solver isep_dest: prems(1))
      done
    done
qed


lemma "zip_assn (BUZ ps (rbt.Branch c l k v r)) ti iti \<turnstile> (EXS itli. zip_assn (BUZ (LParent c k v r # ps) l) ti itli)"
proof(induction ps arbitrary: ti rule: rev_induct)
  case Nil
  then show ?case
    apply (auto simp add: zip_assn.simps to_td_def)
    unfolding rbt_assn_branch_def    
    apply isep_solver_keep
    apply isep_extract_pure
    apply (isep_solver_keep | simp)+
    done
next
  case (snoc p ps)

  show ?case
    unfolding zip_assn.simps to_td_def
    apply auto
    apply(cases p)
    subgoal for c' k' v' r'
      apply (simp add: zip_assn.simps)
      apply isep_elim_ex
      
      apply (isep_drule drule: snoc)
        apply (simp add: zip_assn.simps to_td_def)
        apply isep_solver
       apply isep_solver


      apply isep_solver_keep
      apply (simp add: zip_assn.simps to_td_def)      
      apply isep_solver_keep
      
      apply simp
      done
    subgoal
      unfolding zip_assn.simps
      apply (simp add: zip_assn.simps)
      apply isep_elim_ex
      
      apply (isep_drule drule: snoc)
        apply (simp add: zip_assn.simps to_td_def)
        apply isep_solver
       apply isep_solver


      apply isep_solver_keep
      apply (simp add: zip_assn.simps to_td_def)      
      apply isep_solver_keep
      
      apply simp
      done
    done
qed


lemma color_assn_from_pure [fri_red_rules]: "\<flat>\<^sub>pcolor_assn c ci \<Longrightarrow> is_sep_red \<box> \<box> \<box> (\<upharpoonleft>color_assn c ci)"
  apply (rule is_sep_redI)
  by (simp add: color_assn_pure extract_pure_assn pure_true_conv)


lemma go_left_i_correct:
"
  llvm_htriple
  (zip_assn (BUZ ps (rbt.Branch c l k v r)) ti iti)
  (go_left_i iti)
  (\<lambda>x. zip_assn (go_left (BUZ ps (rbt.Branch c l k v r))) ti x)
"
  unfolding go_left_i_def
  apply vcg
  unfolding zip_assn.simps
  apply vcg_rl back
   apply vcg_compat
   apply isep_solver_keep
  apply vcg_solve+
  apply vcg_compat
  apply (isep_solver_keep isep_intro: td_zip_assn_go_leftI | simp add: to_td_def)+
  done


definition "rbt_update k v = rbt_map_entry k (\<lambda>_. v)"


fun rbt_update_ad where
  "rbt_update_ad k v rbt.Empty = rbt.Empty"
| "rbt_update_ad k v (rbt.Branch c l bk bv r) =
  (
    if k < bk
    then rbt.Branch c (rbt_update_ad k v l) bk bv r
    else if k > bk 
    then rbt.Branch c l bk bv (rbt_update_ad k v r)
    else Branch c l k v r
  )
"


lemma rbt_update_ad_correct:
  "rbt_update_ad k v t = rbt_update k v t"
  unfolding rbt_update_def
  by (induction t, auto)


fun zip_update :: "'v \<Rightarrow> ('k, 'v) Zipper \<Rightarrow> ('k, 'v) Zipper" where
  "zip_update v (ps, rbt.Branch c l bk bv r) = (ps, rbt.Branch c l bk v r)"
| "zip_update v (ps, rbt.Empty) = undefined"


lemma
  to_tree_greaterE: "\<lbrakk>k \<guillemotleft>| to_tree (ps, t); (k \<guillemotleft>| t \<Longrightarrow> thesis)\<rbrakk> \<Longrightarrow> thesis" and
  to_tree_lessE: "\<lbrakk>to_tree (ps, t) |\<guillemotleft> k; t |\<guillemotleft> k \<Longrightarrow> thesis\<rbrakk> \<Longrightarrow> thesis"
   apply (induction ps rule: rev_induct)
     apply simp_all
  subgoal for p by (cases p, auto)
  subgoal for p by (cases p, auto)
  done


lemma zip_update_correct:
  assumes "rbt_sorted (to_tree (ps, rbt.Branch c l bk bv r))"
  shows "to_tree (zip_update v (ps, rbt.Branch c l bk bv r)) = rbt_update bk v (to_tree (ps, rbt.Branch c l bk bv r))"
using assms proof (induction ps rule: rev_induct)
  case Nil thus ?case unfolding rbt_update_def by simp
next
  case (snoc p' ps')
  show ?case 
  proof (cases p')
    case (LParent pc pk pv pr)

    from LParent snoc(2) have "pk > bk"
      apply simp
      by (metis to_tree_lessE rbt_less_simps(2)) (*erule is weak*)

    then show ?thesis
      using LParent snoc by (auto simp: rbt_update_def)
  next
    case (RParent pc pl pk pv)

    from RParent snoc(2) have "pk < bk"
      apply simp
      by (metis rbt_greater_simps(2) to_tree_greaterE)

    then show ?thesis
      using RParent snoc by (auto simp: rbt_update_def)
  qed
qed


definition "it_update it v \<equiv> set_value_p v it"


lemma it_update_correct:
"
  llvm_htriple
  (zip_assn (ps, Branch c l k v r) ti iti)
  (it_update iti v)
  (\<lambda>_. zip_assn (zip_update v (ps, Branch c l k v r)) ti iti)
"
  unfolding it_update_def
  apply vcg
  apply (simp only: zip_assn.simps)
  apply vcg
  done


lemma rbt_assn_entails_root_zip_assn:
  "rbt_assn t ti \<turnstile> zip_assn ([], t) ti ti"
  apply (simp add: zip_assn.simps)
  apply isep_extract_pure
  apply isep_solver_keep
  ..


lemma zip_assn_to_tree_rbt_assn:
  "zip_assn (ps, t) ti iti \<turnstile> rbt_assn (to_tree (ps, t)) ti"
proof(induction ps arbitrary: ti rule: rev_induct)
  case Nil
  then show ?case
    apply (simp add: zip_assn.simps)
    apply isep_extract_pure
    apply (isep_solver_keep | simp)+
    done
next
  case (snoc p ps)

  note IH = snoc[simplified zip_assn.simps]
  thm IH
  show ?case
  proof(cases p)
    case (LParent c k v r)
    then show ?thesis
      apply (simp add: zip_assn.simps LParent)
      apply isep_elim_ex
      apply isep_extract_pure
      apply (isep_solver_keep isep_dest: IH)
      apply simp
      done
  next
    case (RParent c l k v)
    then show ?thesis
      apply (simp add: zip_assn.simps RParent)
      apply isep_elim_ex
      apply isep_extract_pure
      apply (isep_solver_keep isep_dest: IH)
      apply simp
      done
  qed
qed


partial_function (M) lookup_it :: 
  "('ki, 'v::llvm_rep) rbti \<Rightarrow> 'ki \<Rightarrow> ('ki, 'v) rbti llM" where
  "lookup_it node_p k = do {
    if node_p = null
    then return null
    else do {
      node \<leftarrow> ll_load node_p;
      k_old \<leftarrow> return rbt_node.key node;
      k_lt \<leftarrow> lt_impl k k_old;
      if k_lt = 1
      then lookup_it (rbt_node.left node) k
      else do {
        k_gt \<leftarrow> lt_impl k_old k;
        if k_gt = 1
        then lookup_it (rbt_node.right node) k
        else return node_p
      }
    }
  }"


lemma lookup_it_correct:
"
  llvm_htriple
  (rbt_assn t ti ** \<upharpoonleft>key_assn k ki)
  (lookup_it ti ki)
  (\<lambda>iti. (case rbt_lookup t k of
     None \<Rightarrow> \<up>(iti = null) ** rbt_assn t ti |
    (Some v) \<Rightarrow> (EXS ps c l r. zip_assn (ps, rbt.Branch c l k v r) ti iti)) ** \<upharpoonleft>key_assn k ki)
"
proof(cases "rbt_lookup t k" )
  case None
  then show ?thesis
  proof(induction t arbitrary: ti ki)
    case Empty
    then show ?case
      apply (subst lookup_it.simps)
      apply vcg
      done
  next
    case (Branch bc bl bk bv br)

    note [vcg_rules] = Branch(1-2)

    from Branch(3) have left_none: "k < bk \<Longrightarrow> rbt_lookup bl k = None" by simp
    moreover from Branch(3) have right_none: "k > bk \<Longrightarrow> rbt_lookup br k = None" 
      by (auto split: if_splits)
    moreover from Branch(3) have neq: "k \<noteq> bk" by auto

    ultimately show ?case
      apply (subst lookup_it.simps)
      apply vcg
      done
  qed
next
  case (Some v)
  then show ?thesis
    apply simp
  proof(induction t arbitrary: ti ki)
    case Empty
    then show ?case
      apply (subst lookup_it.simps)
      apply vcg
      done
  next
    case (Branch bc bl bk bv br)

    note [vcg_rules] = Branch(1-2)

    from Branch(3) have left_some: "k < bk \<Longrightarrow> rbt_lookup bl k = Some v" by simp
    moreover from Branch(3) have right_some: "k > bk \<Longrightarrow> rbt_lookup br k = Some v" 
      by (auto split: if_splits)
    moreover from Branch(3) have eq: "k = bk \<Longrightarrow> v = bv" by auto

    ultimately show ?case
      apply (subst lookup_it.simps)
      apply vcg
      subgoal for asf bci bli bki bri iti _ ps b\<^sub>tc b\<^sub>tl b\<^sub>tr (*k < bk*)
        apply vcg_compat
        (*need to manually define how the extra level in the tree translates into the parent list of the zipper *)
        apply (isep_intro_ex_with "ps @ [LParent bc bk bv br]")
        apply (simp only: zip_assn.simps)
        apply (isep_solver_keep | simp)+
        done

      subgoal for asf bci bli bki bri s (*k \<ge> bk*)
        apply vcg
        subgoal for iti sa ps b\<^sub>tc b\<^sub>tl b\<^sub>tr (*k > bk*)
          apply vcg_compat
          (*need to manually define how the extra level in the tree translates into the parent list of the zipper *)
          apply (isep_intro_ex_with "ps @ [RParent bc bl bk bv]")
          apply (simp only: zip_assn.simps)
          apply (isep_solver_keep | simp)+
          done
        subgoal (*k = bk*)
          apply vcg
          apply vcg_compat
          apply (isep_intro_ex_with "[]")
          apply (simp only: zip_assn.simps)
          apply (isep_solver_keep | simp)+
          done
        done
      done
  qed
qed
*)

end


end