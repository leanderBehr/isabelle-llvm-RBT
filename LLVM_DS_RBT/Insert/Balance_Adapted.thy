theory Balance_Adapted
  imports "../Abstract_Rbt"
begin                                     


subsection \<open>Balance Cases\<close>


definition "rbt_balance_ad_case_1 lhs k v rhs \<equiv>
  case (lhs, k, v, rhs) of 
  ((Branch color.R a w x b), s, t, (Branch color.R c y z d)) \<Rightarrow>
   Branch color.R (Branch color.B a w x b) s t (Branch color.B c y z d)"

definition "rbt_balance_ad_case_2 lhs k v rhs \<equiv>
  case (lhs, k, v, rhs) of 
  ((Branch color.R (Branch color.R a w x b) s t c), y, z, d) \<Rightarrow>
   Branch color.R (Branch color.B a w x b) s t (Branch color.B c y z d)"

definition "rbt_balance_ad_case_3 lhs k v rhs \<equiv>
  case (lhs, k, v, rhs) of 
  ((Branch color.R a w x (Branch color.R b s t c)), y, z, d) \<Rightarrow>
   Branch color.R (Branch color.B a w x b) s t (Branch color.B c y z d)"

definition "rbt_balance_ad_case_4 lhs k v rhs \<equiv>
  case (lhs, k, v, rhs) of 
  (a, w, x, (Branch color.R b s t (Branch color.R c y z d))) \<Rightarrow>
   Branch color.R (Branch color.B a w x b) s t (Branch color.B c y z d)"

definition "rbt_balance_ad_case_5 lhs k v rhs \<equiv>
  case (lhs, k, v, rhs) of 
  (a, w, x, (Branch color.R (Branch color.R b s t c) y z d)) \<Rightarrow>
   Branch color.R (Branch color.B a w x b) s t (Branch color.B c y z d)"

definition "rbt_balance_ad_case_6 lhs k v rhs \<equiv>
  case (lhs, k, v, rhs) of 
  (a, s, t, b) \<Rightarrow> Branch color.B a s t b"


subsection \<open>Case Checks\<close>


definition "rbt_check_1 lhs rhs \<equiv> rbt_is_red lhs \<and> rbt_is_red rhs"
definition "rbt_check_2 lhs rhs \<equiv> rbt_is_red lhs \<and> rbt_is_red (rbt_left lhs)"
definition "rbt_check_3 lhs rhs \<equiv> rbt_is_red lhs \<and> rbt_is_red (rbt_right lhs)"
definition "rbt_check_4 lhs rhs \<equiv> rbt_is_red rhs \<and> rbt_is_red (rbt_right rhs)"
definition "rbt_check_5 lhs rhs \<equiv> rbt_is_red rhs \<and> rbt_is_red (rbt_left rhs)"


subsubsection \<open>unfold lemmas for checks\<close>


lemma rbt_check_1_unfold:
  assumes "rbt_check_1 lhs rhs"
  obtains ll k_l v_l lr
    rl k_r v_r rr where
    "lhs = (Branch color.R ll k_l v_l lr)"
    "rhs = (Branch color.R rl k_r v_r rr)"
  using assms by (meson rbt_is_red_unfold_branch rbt_check_1_def)


lemma rbt_check_2_unfold:
  assumes "rbt_check_2 lhs rhs"
  obtains k_l v_l lr
    lll k_ll v_ll llr where
    "lhs = (Branch color.R (Branch color.R lll k_ll v_ll llr) k_l v_l lr)"
  using assms
  unfolding rbt_check_2_def rbt_left_def
  by fastforce


lemma rbt_check_3_unfold:
  assumes "rbt_check_3 lhs rhs"
  obtains ll k_l v_l
    lrl k_lr v_lr lrr where
    "lhs = (Branch color.R ll k_l v_l (Branch color.R lrl k_lr v_lr lrr))"
  using assms
  unfolding rbt_check_3_def rbt_right_def
  by fastforce


lemma rbt_check_4_unfold:
  assumes "rbt_check_4 lhs rhs"
  obtains rl k_r v_r
    rrl k_rr v_rr rrr where
    "rhs = (Branch color.R rl k_r v_r (Branch color.R rrl k_rr v_rr rrr))"
  using assms
  unfolding rbt_check_4_def rbt_right_def
  by fastforce


lemma rbt_check_5_unfold:
  assumes "rbt_check_5 lhs rhs"
  obtains k_r v_r rr
    rll k_rl v_rl rlr where
    "rhs = (Branch color.R (Branch color.R rll k_rl v_rl rlr) k_r v_r rr)"
  using assms
  unfolding rbt_check_5_def rbt_left_def
  by fastforce


subsubsection \<open>Adapted Balance Function\<close>


fun rbt_balance_ad where 
  "rbt_balance_ad lhs k v rhs = 
  (
    if rbt_check_1 lhs rhs
      then rbt_balance_ad_case_1 lhs k v rhs
    else if rbt_check_2 lhs rhs
      then rbt_balance_ad_case_2 lhs k v rhs
    else if rbt_check_3 lhs rhs
      then rbt_balance_ad_case_3 lhs k v rhs
    else if rbt_check_4 lhs rhs
      then rbt_balance_ad_case_4 lhs k v rhs
    else if rbt_check_5 lhs rhs
      then rbt_balance_ad_case_5 lhs k v rhs
    else rbt_balance_ad_case_6 lhs k v rhs
  )
  "


lemma rbt_balance_ad_correct: 
  "rbt_balance_ad lhs k v rhs = rbt_balance lhs k v rhs"
  apply (induction lhs k v rhs rule: balance.induct)
  by(auto simp add: 
      rbt_is_red_def
      rbt_left_def
      rbt_right_def
      rbt_balance_ad_case_1_def
      rbt_balance_ad_case_2_def
      rbt_balance_ad_case_3_def
      rbt_balance_ad_case_4_def
      rbt_balance_ad_case_5_def
      rbt_balance_ad_case_6_def
      rbt_check_1_def
      rbt_check_2_def
      rbt_check_3_def
      rbt_check_4_def
      rbt_check_5_def
      )


end