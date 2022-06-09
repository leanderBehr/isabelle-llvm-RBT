theory Delete
  imports 
    Balance_LR
begin


context rbt_impl
begin
interpretation llvm_prim_ctrl_setup .
interpretation llvm_prim_arith_setup .
interpretation llvm_prim_setup .


subsection \<open>random crap\<close>


definition "Equiv (f:: real \<Rightarrow> real) g \<equiv> \<forall>x. f (g x) = x"


lemma 1 [intro]: "f = (\<lambda>x. f' (x - c)) \<Longrightarrow> Equiv f' g \<Longrightarrow> Equiv f (\<lambda>x. g x + c)"
  unfolding Equiv_def by simp

lemma 2 [intro]: "Equiv f (\<lambda>x. g x + (-c)) \<Longrightarrow> Equiv f (\<lambda>x. g x - c)"
  by simp

lemma 3 [intro]: "c \<noteq> 0 \<Longrightarrow> f = (\<lambda>x. f' ( x / c)) \<Longrightarrow> Equiv f' g \<Longrightarrow> Equiv f (\<lambda>x. c * g x)"
  unfolding Equiv_def
  by auto

lemma 4 [intro]: "f = (\<lambda>x. x) \<Longrightarrow> Equiv f (\<lambda>x. x)"
  unfolding Equiv_def by simp

lemma 5 [intro]: "Equiv f (\<lambda>x. (1/c) * g x ) \<Longrightarrow> Equiv f (\<lambda>x. g x / c)"
  by simp



definition "g \<equiv> (\<lambda>(x::real). 2 * (x + 5 - x) + x + 12 * x - 1 + (1.1 * x))"

schematic_goal "Equiv ?f g"
  unfolding g_def
  apply (rule | simp)+
  done


definition "Cond (ff::'a list \<Rightarrow> 'b) (gg:: 'a list \<Rightarrow> 'b) = (ff = gg)"


lemma R1: "f [] = undefined \<Longrightarrow> (\<And>l. f l = E (hd l) (tl l)) \<Longrightarrow> Cond f (\<lambda>l. case l of x # xs \<Rightarrow> E x xs)" 
  unfolding Cond_def
  apply standard
  by (simp add: list.case_eq_if)


schematic_goal "Cond ?f (\<lambda>l. case l of x # (y # xs) \<Rightarrow> x)"
  apply (rule R1)
  sorry


end 


end