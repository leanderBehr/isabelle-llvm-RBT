theory LLVM_DS_RBT
  imports
  "LLVM_DS_RBT/Free"
  "LLVM_DS_RBT/Insert/Insert"
  "LLVM_DS_RBT/Export"
  "LLVM_DS_RBT/Lookup"
begin                                     


lemma fri_exE: "(\<And>x. FRAME_INFER (P x) Qs F) \<Longrightarrow> FRAME_INFER (EXS x. P x) Qs F"
  by (auto simp: FRAME_INFER_def entails_def)


datatype ('k, 'v) Parent = LParent color 'k 'v "('k, 'v) rbt" | RParent color "('k, 'v) rbt" 'k 'v


type_synonym ('k, 'v) Zipper = "(('k, 'v) Parent) list \<times> ('k, 'v) rbt"


fun go_up :: "('k, 'v) Zipper \<Rightarrow> ('k, 'v) Zipper" where
  "go_up ((LParent c k v r) # ps, t) = (ps, rbt.Branch c t k v r)"
| "go_up ((RParent c l k v) # ps, t) = (ps, rbt.Branch c l k v t)"
| "go_up ([], _) = undefined"


lemma [simp]: "length (fst (go_up (v # va, t))) < Suc (length va)"
 by (cases v; simp)


fun go_left :: "('k, 'v) Zipper \<Rightarrow> ('k, 'v) Zipper" where
  "go_left (ps, rbt.Empty) = undefined"
| "go_left (ps, rbt.Branch c l k v r) = ((LParent c k v r) # ps, l)"


fun go_right :: "('k, 'v) Zipper \<Rightarrow> ('k, 'v) Zipper" where
  "go_right (ps, rbt.Empty) = undefined"
| "go_right (ps, rbt.Branch c l k v r) = ((RParent c l k v) # ps, r)"


fun to_tree :: "('k, 'v) Zipper \<Rightarrow> ('k, 'v) rbt" where
  "to_tree ([], t) = t"
| "to_tree (ps, t) = to_tree (go_up (ps, t))"
  

lemma
  "to_tree (ps, Branch c l k v r) = to_tree (go_left ((ps, Branch c l k v r)))"
  by simp

lemma
  "to_tree (ps, Branch c l k v r) = to_tree (go_right ((ps, Branch c l k v r)))"
  by simp

lemma
  "to_tree (p#ps, t) = to_tree (go_up ((p#ps, t)))"
  by simp

lemma "to_tree ([], t) = t" by simp


definition "pplus x y \<equiv> x + y"


datatype 'a Op = Plus "'a Op" "'a Op" | Mult "'a Op" "'a Op" | C 'a


fun eval where
  "eval (C x) = x"
| "eval (Plus x y) = eval x + eval y"
| "eval (Mult x y) = eval x * eval y"


lemma PlusI:
"A = Plus b' c' \<Longrightarrow> eval b' = b \<Longrightarrow> eval c' = c \<Longrightarrow> eval A = b + c" by simp


lemma MultI:
"A = Mult b' c' \<Longrightarrow> eval b' = b \<Longrightarrow> eval c' = c \<Longrightarrow> eval A = b * c" by simp


lemma CI: "A = C b \<Longrightarrow> eval A = b" by simp


definition "Y a b c d e \<equiv> a + b * e + c * d"

schematic_goal GG: "eval ?X = Y a b c d e"
  unfolding Y_def
  apply (rule PlusI | rule MultI | rule CI | simp)+
  done


datatype A = B A | C 


definition "M f x \<equiv> undefined"


lemma LLL: "case x of B x \<Rightarrow> f x = M f x" sorry


term "case_abs (\<lambda>x. B x) "


fun find :: "('k::linorder, 'v) Zipper \<Rightarrow> 'k \<Rightarrow> ('k, 'v) Zipper" where
  "find (ps, rbt.Empty) targ = (ps, rbt.Empty)"
| "find (ps, (rbt.Branch c l k v r)) targ = 
  (
    if targ < k
    then find ((LParent c k v r) # ps, l) targ
    else if targ > k
    then find ((RParent c l k v) # ps, r) targ
    else (ps, (rbt.Branch c l k v r))
  )"


definition lookup :: "('k::linorder, 'v) Zipper \<Rightarrow> 'k  \<Rightarrow> 'v option" where
  "lookup z k = (case find z k of (_, rbt.Empty) \<Rightarrow> None | (_, rbt.Branch _ _ _ v _) \<Rightarrow> Some v)"


lemma 1: "rbt_lookup t k = None \<Longrightarrow> \<exists>ps'. find (ps, t) k = (ps', rbt.Empty)"
  by (induction t arbitrary: ps; auto)


lemma 11:
  assumes "rbt_lookup t k = None" 
  obtains ps' where  "find (ps, t) k = (ps', rbt.Empty)"
  using 1 assms by blast


lemma 2: "rbt_lookup t k = Some v \<Longrightarrow> \<exists>ps' c l r. find (ps, t) k = (ps', rbt.Branch c l k v r)"
  by (induction t arbitrary: ps; auto)


lemma 22:
  assumes "rbt_lookup t k = Some v" 
  obtains ps' c l r where  "find (ps, t) k = (ps', rbt.Branch c l k v r)"
  using 2 assms by fast


lemma "rbt_lookup t k = lookup (ps, t) k"
  unfolding lookup_def
  apply (cases "rbt_lookup t k")
  subgoal 
    apply simp
    apply (erule 11[where ps=ps])
    by simp
  subgoal
    apply simp
    apply (erule 22[where ps=ps])
    by simp
  done


definition "Equiv (f:: real \<Rightarrow> real) g \<equiv> \<forall>x. f (g x) = x"


lemma A [intro]: "f = (\<lambda>x. f' (x - c)) \<Longrightarrow> Equiv f' g \<Longrightarrow> Equiv f (\<lambda>x. g x + c)"
  unfolding Equiv_def by simp

lemma B [intro]: "Equiv f (\<lambda>x. g x + (-c)) \<Longrightarrow> Equiv f (\<lambda>x. g x - c)"
  by simp

lemma C [intro]: "c \<noteq> 0 \<Longrightarrow> f = (\<lambda>x. f' ( x / c)) \<Longrightarrow> Equiv f' g \<Longrightarrow> Equiv f (\<lambda>x. c * g x)"
  unfolding Equiv_def
  by auto

lemma D [intro]: "f = (\<lambda>x. x) \<Longrightarrow> Equiv f (\<lambda>x. x)"
  unfolding Equiv_def by simp

lemma E [intro]: "Equiv f (\<lambda>x. (1/c) * g x ) \<Longrightarrow> Equiv f (\<lambda>x. g x / c)"
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


context rbt_impl
begin
interpretation llvm_prim_ctrl_setup .
interpretation llvm_prim_arith_setup .
interpretation llvm_prim_setup .

ML_val \<open>Basic_VCG.print_solvers @{context}\<close>

end


end