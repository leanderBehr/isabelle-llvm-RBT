theory List_Less
  imports
    "HOL-Library.List_Lexorder"
    "Isabelle_LLVM.LLVM_DS_Array_List"
    "../Setup"
    "../Separation_Logic_Solver/Methods"
    Arl_Ext
    "../Bool_Assn_Setup"
begin


partial_function (M) list_le'
  :: "(8 word, 'l::len2) array_list \<Rightarrow> (8 word, 'l) array_list \<Rightarrow> 'l word \<Rightarrow> 1 word llM"  where
  "list_le' xs ys i =
  doM {
    len_left \<leftarrow> arl_len xs;
    len_right \<leftarrow> arl_len ys;

    if i < len_right
    then if i < len_left
      then doM {
        x \<leftarrow> arl_nth xs i;
        y \<leftarrow> arl_nth ys i;
        le \<leftarrow> ll_icmp_ult x y;
        if le = 1
        then Mreturn ll_True
        else doM {
          ge \<leftarrow> ll_icmp_ult y x;
          if ge = 1 
          then Mreturn ll_False
          else list_le' xs ys (i+1)
        }
      }
      else Mreturn ll_True
    else Mreturn ll_False
  }
"


abbreviation "string_assn str (stri:: (8 word, 'l::len2) array_list) \<equiv>
   \<up>(LENGTH('l) > 4) ** (EXS ws. \<upharpoonleft>arl_assn ws stri ** \<up>(length ws = length str) **
   \<up>(\<forall>i < length str. \<flat>\<^sub>punat.assn (str ! i) (ws ! i)))"

(*
abbreviation "string_assn str (stri:: (8 word, 'l::len2) array_list) \<equiv> arl_elem_assn snat.assn str stri"
*)

lemma postfix_le: 
  "\<lbrakk>i < length xs; i < length ys\<rbrakk> \<Longrightarrow> drop i xs < drop i ys = (xs ! i < ys ! i \<or> xs ! i = ys ! i \<and> drop (i+1) xs < drop (i+1) ys)"  
  by (auto simp add: drop_Suc_nth)


lemma arl_length_snat_bound:  
  "pure_part (\<upharpoonleft>arl_assn xs (xsi :: ('a::llvm_rep, 'l::len2) array_list))
   \<Longrightarrow> length xs < 2 ^ (LENGTH('l)-1)"
  unfolding arl_assn_def dr_assn_prefix_def mk_assn_def
  unfolding arl_assn'_def mk_assn_def
  apply (cases xsi)
  apply simp
proof -
  fix li ci ai
  assume "pure_part (\<lambda>s. \<exists>c l a. (\<upharpoonleft>snat.assn l (li::'l word) \<and>*
                                    \<upharpoonleft>snat.assn c (ci::'l word) \<and>*
                                    \<upharpoonleft>narray_assn a ai \<and>*
                                    \<up>(4 < LENGTH('l) \<and> l \<le> c \<and> c = length a \<and> xs = take l a)) s)"

  then obtain c l a  where pp: "pure_part (\<upharpoonleft>snat.assn l li \<and>*
                                    \<upharpoonleft>snat.assn c ci \<and>*
                                    \<upharpoonleft>narray_assn a ai \<and>*
                                    \<up>(4 < LENGTH('l) \<and> l \<le> c \<and> c = length a \<and> xs = take l a))"
    unfolding pure_part_def
    by auto

  from pp have "xs = take l a"
    by (auto dest!: pure_part_split_conj)

  hence length_le: "length xs \<le> l" by simp

  from pp have "\<flat>\<^sub>psnat.assn l li"
    apply (auto dest!: pure_part_split_conj)
    by (simp add: snat.assn_def)
  hence "l \<in> snats LENGTH('l)"
    by (simp add: snat.assn_def)
  hence "l < 2 ^ (LENGTH('l)-1)"
    unfolding snats_def by blast

  with length_le show "length xs < 2 ^ (LENGTH('l) - Suc 0)" 
    by simp
qed


lemma [simp]: "length xs > 0 \<Longrightarrow> [] < xs"
  by (cases xs, auto)


lemma [simp]: "i < length xs \<Longrightarrow> [] < drop i xs" by simp


lemma list_le'_rule:
  "
  llvm_htriple
  (string_assn xs xsi ** string_assn ys ysi ** \<upharpoonleft>snat.assn i ii)
  (list_le' xsi ysi ii)
  (\<lambda>r. \<upharpoonleft>bool.assn (drop i xs < drop i ys) r ** string_assn xs xsi ** string_assn ys ysi )
"
proof(induction "min (length xs) (length ys) - i" arbitrary: i ii)
  case 0
  then show ?case
    apply (subst list_le'.simps)
    apply vcg
    subgoal by simp (*unreachable recursive path*)
     apply vcg
    done

next
  case (Suc x)
  from Suc(2) have precond: "x = min (length xs) (length ys) - (i+1)" by simp

  note Suc(1)[OF precond, vcg_rules]

  show ?case
    apply (subst list_le'.simps)
    apply vcg
    subgoal for asf x xa r ra s
      apply vcg_rl back
       apply vcg_compat
       apply (sep isep_intro: pure_pure_asm_prefixI | find_sep)+
        apply (auto simp add: SOLVE_AUTO_DEFER_def)
       apply vcg_solve
       apply vcg 
       apply vcg_compat

       apply (sepE isep_intro: pure_pure_asm_prefixI | find_sep)+
             apply (auto simp add: postfix_le)
      apply vcg_solve
      apply vcg
      apply vcg_rl back 
       apply vcg_compat
       apply (sepwith \<open>auto\<close> isep_intro: pure_pure_asm_prefixI) 
      apply vcg_solve
      apply vcg
      apply vcg_rl
       apply vcg_compat
       apply (sepEwith simp isep_intro: pure_pure_asm_prefixI)
        apply simp_all
      subgoal 
        unfolding dr_assn_pure_asm_prefix_def snat.assn_def snat_invar_def
        apply (rule conjI)
         apply simp_all
        by (smt (verit) Suc_eq_plus1 less_trans_Suc linorder_not_less msb_unat_big snat_eq_unat(1) unat_1 unat_plus_if' unsigned_less)
      apply isep_intro_ex
      apply (sepwith simp)
      apply vcg_solve+
      done
    subgoal by vcg
    subgoal by vcg
    done
qed


unbundle monad_syntax_M


partial_function (M) list_le''
  :: "(8 word, 'l::len2) array_list \<Rightarrow> (8 word, 'l) array_list \<Rightarrow> 'l word \<Rightarrow> 1 word llM"  where
  "list_le'' xs ys i =
  do {
    len_left \<leftarrow> arl_len xs;
    len_right \<leftarrow> arl_len ys;

    if i < len_right
    then if i < len_left
      then do {
        x \<leftarrow> arl_nth xs i;
        y \<leftarrow> arl_nth ys i;
        le \<leftarrow> ll_icmp_ult x y;
        if le = 1
        then return ll_True
        else do {
          ge \<leftarrow> ll_icmp_ult y x;
          if ge = 1 
          then return ll_False
          else do {ip1 \<leftarrow> ll_add i 1; list_le'' xs ys ip1}
        }
      }
      else return ll_True
    else return ll_False
  }
"


lemmas list_le''.simps[llvm_code]


lemma list_le''_rule:
  "
  llvm_htriple
  (string_assn xs xsi ** string_assn ys ysi ** \<upharpoonleft>snat.assn i ii)
  (list_le'' xsi ysi ii)
  (\<lambda>r. \<upharpoonleft>bool.assn (drop i xs < drop i ys) r ** string_assn xs xsi ** string_assn ys ysi )
"
proof(induction "min (length xs) (length ys) - i" arbitrary: i ii)
  case 0
  then show ?case 
    apply (subst list_le''.simps)
    apply vcg
    subgoal by simp (*unreachable recursive path*)
     apply vcg
    done
next
  case (Suc x)
  show ?case
    apply (subst list_le''.simps)
    apply vcg
    subgoal for asf x xa r ra s
      apply vcg_rl back
       apply vcg_compat
       apply (sep isep_intro: pure_pure_asm_prefixI | find_sep)+
        apply (auto simp add: SOLVE_AUTO_DEFER_def)
       apply vcg_solve
       apply vcg
       apply vcg_compat
       apply (sepE isep_intro: pure_pure_asm_prefixI | find_sep)+
             apply (auto simp add: postfix_le)
      apply vcg_solve
      apply vcg
      apply vcg_rl back
       apply vcg_compat
       apply (sepwith auto isep_intro: pure_pure_asm_prefixI)
      apply vcg_solve
      apply vcg
      supply Suc(1)[vcg_rules]
      apply vcg
      subgoal using Suc(2) by simp
      apply vcg
      done
    subgoal by vcg
    subgoal by vcg
    done
qed


definition "list_le xsi ysi \<equiv> list_le'' xsi ysi 0"


lemmas list_le_def[llvm_code, llvm_inline]


lemma list_le_rule:
  "
  llvm_htriple
  (string_assn xs xsi ** string_assn ys ysi)
  (list_le xsi ysi)
  (\<lambda>r. \<upharpoonleft>bool.assn (xs < ys) r ** string_assn xs xsi ** string_assn ys ysi )
"
  unfolding list_le_def
  supply list_le''_rule[vcg_rules]
  by vcg


end