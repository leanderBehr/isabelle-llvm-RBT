theory LLVM_DS_RBT
  imports
  "LLVM_DS_RBT/Load_Store_Example"
  "LLVM_DS_RBT/Example/Export"
  "LLVM_DS_RBT/Bench_Export"
  "LLVM_DS_RBT/Balanced_Properties"
begin
context rbt_impl
begin
interpretation rbt_impl_deps . 

find_theorems rbt_assn_ext lookup_ptr htriple
find_theorems rbt_assn_ext insert_opt htriple
find_theorems rbt_assn_ext load htriple
find_theorems rbt_assn_ext delete_opt htriple
find_theorems rbt_assn_ext store htriple

partial_function (M) nonterm :: "nat \<Rightarrow> unit llM" where
  "nonterm x = nonterm (x+1)"

find_theorems htriple wpa STATE
term rbt_assn_ext
thm htriple_vcg_frame_erule[simplified PRECOND_def FRAME_def EXTRACT_def]
find_theorems STATE entails

lemma "\<exists>F. P \<turnstile> Q ** F \<Longrightarrow> P \<turnstile> Q ** sep_true"
  by (metis entails_mp entails_true sep_conj_commute)

definition "wb A \<equiv> (\<forall>s s'. A s \<and> A s' \<longrightarrow> s = s')"

lemma "P s \<Longrightarrow> \<exists>s'. (s :: llvm_amemory) ## s' \<and> P s'"
  oops

lemma "wb X \<Longrightarrow> \<exists>s. X s"
  unfolding wb_def
  oops

lemma "is_sep_red \<box> \<box> A A"
  apply (rule is_sep_redI)
  apply simp
  apply sep
  apply simp
  done

term sep_is_pure_assn

lemma 
  assumes [fri_red_rules]:
    "is_sep_red R \<box> (T(P ** Q)) (T(P' ** Q'))"
  shows "ENTAILS (T(P ** Q)) (T(P' ** Q') ** R)"
  apply vcg_try_solve
  apply vcg_compat?
  apply sep?
  done

lemma "wb X \<Longrightarrow> (\<exists>s. X s) \<Longrightarrow> (P \<turnstile> Q) = (P ** X \<turnstile> Q ** X)"
  apply rule
   apply (simp add: conj_entails_mono)
  unfolding wb_def entails_def
  subgoal premises prems
    apply standard+
  proof -
    thm prems
    fix s
    assume asm: "P s"
    with prems(2) obtain sx where "X sx" by blast

    with asm have "(P \<and>* X) (s + sx)"
      unfolding sep_conj_def 
      oops

  
  

lemma H1:
  "llvm_pto v p s \<Longrightarrow> llvm_pto v p s' \<Longrightarrow> s = s'"
  by (metis EXACT_def llvm_pto_is_ato pure_partI pure_part_llvm_pto)

lemma "\<upharpoonleft>ll_bpto v p s \<Longrightarrow> \<upharpoonleft>ll_bpto v p s' \<Longrightarrow> s = s'"
  unfolding dr_assn_prefix_def ll_bpto_def ll_pto_def mk_assn_def
  apply simp
  unfolding ll_malloc_tag_def llvm_blockp_def
  apply (simp add: pure_true_conv)
  by (smt (z3) EXACT_def H1 pure_partI pure_part_pureD pure_true_conv sep_conj_def sep_conj_empty')

thm rbt_assn_ext.simps

lemma 
  "P ** X \<turnstile> Q ** X ** F \<Longrightarrow> F \<turnstile> F' \<Longrightarrow>
    (\<exists>F. (P \<turnstile> Q ** F) \<and> (F \<turnstile> F'))" 
  unfolding entails_def sep_conj_def  
  oops

lemma balance_correct_test [vcg_rules]:
  "llvm_htriple
  (
    rbt_assn l li **
    rbt_assn r ri **   
    \<upharpoonleft>key_assn k ki **
    \<upharpoonleft>value_assn v vi
  )
  (balance_left li ki vi ri)
  (\<lambda>res. rbt_assn (rbt_balance_left l k v r) res) 
  "
  unfolding balance_left_def bl_case_1_def
  apply vcg
  apply (auto elim!: matches_rbt.elims) []
  oops
              
lemma "sep_is_pure_assn = (\<lambda>A. A \<turnstile> \<box>)"
  unfolding sep_is_pure_assn_def entails_def sep_empty_def by simp



lemma "x + y = (0 :: 'a :: stronger_sep_algebra) \<Longrightarrow> x = 0" 
  oops

lemma "P \<turnstile> \<box> \<Longrightarrow> Q \<turnstile> \<box> \<Longrightarrow> P ** Q \<turnstile> \<box>"
  using conj_entails_mono by fastforce

lemma "(A ** B) s \<Longrightarrow> sep_is_pure_assn (A ** B) \<Longrightarrow> sep_is_pure_assn A" 
  unfolding sep_is_pure_assn_def
  apply standard+
  subgoal for s'
  proof(rule ccontr)
    assume 
      asm1: "A s'" and
      asm2: "\<forall>s. (A \<and>* B) s \<longrightarrow> s = 0" and
      asm3: "s' \<noteq> 0" and
      asm4: "(A \<and>* B) s"

    from asm2 asm4 have "s = 0" by simp
    with asm4 have "B 0" unfolding sep_conj_def 
      oops


lemma "card {P = \<up>pure_part P, sep_is_pure_assn P, P \<turnstile> \<box>} = 1"
  by (smt (verit, best) One_nat_def card_1_singleton_iff entails_def entails_pure_box(2) insert_absorb2 pure_part_pure_eq sep_is_pure_assn_def sep_is_pure_assn_empty)

schematic_goal "Set.insert x (Set.remove x ?X) = ?X"
  by auto
end
end