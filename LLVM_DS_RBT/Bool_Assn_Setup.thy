theory Bool_Assn_Setup
  imports
    Isabelle_LLVM.LLVM_Shallow_RS
    "Separation_Logic_Solver/Methods"
begin

abbreviation (input) ll_True :: "1 word" where "ll_True \<equiv> 1"
abbreviation (input) ll_False :: "1 word" where "ll_False \<equiv> 0"


lemma [simp]: "\<flat>\<^sub>pbool.assn B ll_True = B"
  by (simp add: bool.assn_def)


lemma [simp]: "\<flat>\<^sub>pbool.assn B ll_False = (\<not>B)"
  by (simp add: bool.assn_def)


lemma
  bool_assn_pure_eq:
  "\<upharpoonleft>bool.assn b bi = \<up>(if b then bi = 1 else bi = 0)"
  unfolding bool.assn_def 
  apply (cases b; cases bi)
  apply auto
  done


lemma 
  bool_assn_True_TrueI:
  "\<box> \<turnstile> \<upharpoonleft>bool.assn True ll_True"
  by (auto simp add: pure_true_conv bool_assn_pure_eq)


lemma 
  bool_assn_True_True_eq [simp]:
  "\<upharpoonleft>bool.assn True ll_True = \<box>"
  by (auto simp add: pure_true_conv bool_assn_pure_eq)


lemma
  bool_assn_False_FalseI:
  "\<box> \<turnstile> \<upharpoonleft>bool.assn False ll_False"
  by (auto simp add: pure_true_conv bool_assn_pure_eq)


lemma
  bool_assn_False_False_eq [simp]:
  "\<upharpoonleft>bool.assn False ll_False = \<box>"
  by (auto simp add: pure_true_conv bool_assn_pure_eq)



declare intro_red_rule[OF bool_assn_True_TrueI, fri_red_rules]
declare intro_red_rule[OF bool_assn_False_FalseI, fri_red_rules]


lemma [simp]: "x \<noteq> ll_True \<longleftrightarrow> x = ll_False"
  using word1_neqZ_is_one by blast

lemma [simp]: "x \<noteq> ll_False \<longleftrightarrow> x = ll_True" using word1_neqZ_is_one .


lemma from_bool_False [simp]: "from_bool False = 0" by simp
lemma from_bool_True [simp]: "from_bool True = 1" by simp


end
    