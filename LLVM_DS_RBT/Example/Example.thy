theory Example
  imports 
    "../Map_Interface"
    List_Less
    List_Copy
    Arl_Ext
    "../Export_Wrappers"
begin


definition "string_dr_assn \<equiv> mk_assn string_assn" 


abbreviation "string_list_assn strs strsi \<equiv> arl_elem_assn string_dr_assn strs strsi"


lemma string_dr_assn_eq [simp]: "\<upharpoonleft>string_dr_assn = string_assn"
  unfolding string_dr_assn_def 
  by fastforce


interpretation map: rbt_map
  list_le
  string_dr_assn
  arl_free
  snat.assn
  "\<lambda>x. Mreturn ()"
  "TYPE(nat list)"
  "TYPE((8 word, 'l::len2) array_list)"
  _
  _
  "\<lambda>x. Mreturn x"
proof(standard, goal_cases)
  case (1 lhs lhsi rhs rhsi)
  then show ?case
    using list_le_rule by fastforce
next
  case (2 k ki)
  then show ?case by vcg
next
  case (3 v vi)
  then show ?case by vcg
next
  case (4 v vi)
  then show ?case by vcg
qed


definition list_id_map :: "'a list \<Rightarrow> (nat \<rightharpoonup> 'a)" where
  "list_id_map xs = (\<lambda>i. if i < length xs then Some (xs ! i) else None)"


definition is_id_bijection :: "'a list \<Rightarrow> ('a \<rightharpoonup> 'b) \<Rightarrow> ('b \<rightharpoonup> 'a) \<Rightarrow> bool" where
  "is_id_bijection xs m1 m2 \<equiv> (\<forall> x \<in> set xs. (m2 \<circ>\<^sub>m m1) x = Some x)"


type_synonym stringi = "(8 word, 64) array_list"


type_synonym 'a array_list_64 = "('a, 64) array_list" 


interpretation copy: arl_copy "TYPE(8 word)" unat.assn "\<lambda>x. Mreturn x"
  by (standard, vcg)


interpretation monad_syntax_M_loc .


lemma arl_mems_nth_rule [vcg_rules]:
"
  llvm_htriple
  (arl_elem_assn_ex A xs xsi arl {} ** \<upharpoonleft>snat.assn i ii ** \<up>(i < length xs))
  (arl_nth arl ii)
  (\<lambda>elem. arl_elem_assn_ex A xs xsi arl {i} ** \<upharpoonleft>A (xs ! i) elem ** \<up>(elem = xsi ! i))
"
  unfolding arl_elem_assn_ex_def
  apply vcg
  apply vcg_compat
  apply (sep | find_sep)+
    apply ((auto dest!: list_assn_pure_partD))
  unfolding idxe_map_def
  by (simp add: restrict_map_insert)


partial_function (M) make_id_map_rec' where [llvm_code]:
  "make_id_map_rec' strs i = 
  do {
    len \<leftarrow> arl_len strs;
    if i < len
    then do {
      ip1 \<leftarrow> ll_add i 1;
      m \<leftarrow> make_id_map_rec' strs ip1;
      str \<leftarrow> arl_nth strs i;
      str_copy \<leftarrow> copy.arl_copy str;
      map.insert_opt str_copy i m
    }
    else map.empty
  }"


definition make_id_map_loop' where [llvm_code]:
  "make_id_map_loop' strs = 
  do {
    len \<leftarrow> arl_len strs;
    empty_map \<leftarrow> map.empty;
    llc_for_range 0 len
    (\<lambda>i m. do {
        str \<leftarrow> arl_nth strs i;
        str_copy \<leftarrow> copy.arl_copy str;
        map.insert_opt str_copy i m
    })
    empty_map
  }"


definition "make_id_map_loop'_inv strs strsi i mi \<equiv> 
  (
    EXS m. map.rbt_map_assn m mi **
    string_list_assn strs strsi **
    \<up>(is_id_bijection (take i strs) m (list_id_map strs))
  )" 
  
declare string_dr_assn_eq[simp del]


lemma pure_part_pure_conjI:
  "\<lbrakk>sep_is_pure_assn X; sep_is_pure_assn Y; pure_part X; pure_part Y\<rbrakk> \<Longrightarrow> pure_part (X ** Y)"
  by (metis pure_part_pure_conj_eq pure_part_pure_eq)


lemma pure_sep_set_img_pure_partI:
  assumes
    fin: "finite X" and
    pps: "\<And>x. x\<in>X \<longrightarrow> sep_is_pure_assn (P x) \<and> pure_part (P x)"
  shows 
    "pure_part (\<Union>*x\<in>X. P x)" and "sep_is_pure_assn (\<Union>*x\<in>X. P x)"
  using fin pps
proof(induction X arbitrary: )
  case empty
  {
    case 1 thus ?case by auto
  next
    case 2 thus ?case by simp
  }
next
  case (insert x F)
  {
    case 1 with insert show ?case
      apply auto
      apply (rule pure_part_pure_conjI)
      apply auto
      done
  next
    case 2 thus ?case
      by (blast intro: sep_is_pure_assn_imgI)
  }
qed 
    

lemma string_assn_arl_elem_assnI:
"\<upharpoonleft>string_dr_assn str (stri::(8 word, 'l::len2) array_list)
   \<turnstile> arl_elem_assn unat.assn str stri ** \<up>(4 < LENGTH('l))"
  unfolding string_dr_assn_eq arl_elem_assn_def'
  apply (sep | find_sep)+
  apply isep_intro_ex
  apply (sep | find_sep)+
  unfolding LLVM_DS_List_Assn.list_assn_def
  apply (simp_all add: pure_true_conv)
proof -
  fix x::"8 word list"
  assume assm: "\<forall>i<length str. \<flat>\<^sub>punat.assn (str ! i) (x ! i)"
  have 1: "sep_is_pure_assn (\<Union>*xa\<in>{0..<length str}. \<upharpoonleft>unat.assn (str ! xa) (x ! xa))" 
    apply (rule sep_is_pure_assn_imgI)
    by (simp add: unat.assn_def)

  have 2: "pure_part (\<Union>*xa\<in>{0..<length str}. \<upharpoonleft>unat.assn (str ! xa) (x ! xa))"
    apply (rule pure_sep_set_img_pure_partI)
     apply auto
    apply (simp add: unat.assn_def)
    using assm by (simp add: thin_dr_pure_asm)

  from 1 2 show "\<box> \<turnstile> (\<Union>*xa\<in>{0..<length str}. \<upharpoonleft>unat.assn (str ! xa) (x ! xa))"
    by (metis (mono_tags, lifting) pure_part_pure_eq sep_pureI)
qed


lemma arl_elem_assn_string_assnI:
  "arl_elem_assn unat.assn str (stri::(8 word, 'l::len2) array_list) **
   \<up>(4 < LENGTH('l)) \<turnstile> \<upharpoonleft>string_dr_assn str stri"
    unfolding string_dr_assn_eq arl_elem_assn_def'
    apply (sepE | find_sep)+
    subgoal unfolding LLVM_DS_List_Assn.list_assn_def
      apply simp
      apply (rule pure_entails_boxI sep_is_pure_assn_conjI | simp)+
      apply (rule sep_is_pure_assn_imgI)
      by (simp add: unat.assn_def)    
   
    apply (auto dest: list_assn_pure_partD)[1]
    apply (simp add: dr_assn_pure_asm_prefix_def list_assn_pure_partD unat.assn_pure) 
    done


lemma arl_elem_assn_update:
  assumes "i < length xs" and "i\<in>ex"
  shows
  "arl_elem_assn_ex A xs xsi arl ex ** \<upharpoonleft>A (xs ! i) (xsi ! i) \<turnstile>
   arl_elem_assn_ex A xs xsi arl (ex - {i})"
  unfolding arl_elem_assn_ex_def
  apply isep_extract_pure
  apply (isep_drule drule: LLVM_DS_List_Assn.list_assn_update[where i=i]) 
  using assms apply (auto simp: idxe_map_def dest: list_assn_pure_partD)
  apply sep
  done


lemma make_id_map_rec'_rule:
  "
  llvm_htriple
  (string_list_assn strs strsi ** \<upharpoonleft>snat.assn i ii)
  (make_id_map_rec' strsi ii)
  (\<lambda>mi. (EXS m. map.rbt_map_assn m mi **
                  string_list_assn strs strsi **
                  \<up>(is_id_bijection (drop i strs) m (list_id_map strs))))
"
proof(induction "length strs - i" arbitrary: i ii)
  case 0
  from 0 show ?case 
    apply (subst make_id_map_rec'.simps)
    apply vcg
    apply vcg_compat
    apply (sepE | find_sep)+
    unfolding is_id_bijection_def
    by simp
next
  case (Suc x)
  note Suc(1)[vcg_rules]
  show ?case
    apply (subst make_id_map_rec'.simps)
    apply vcg
    subgoal using Suc(2) by simp
    subgoal
      apply vcg
      apply vcg_rl
       apply vcg_compat
       apply (isep_drule drule: string_assn_arl_elem_assnI)
       apply isep_extract_pure
       apply (isep_rule rule: sep_pureI, simp)
       apply (sepE | find_sep)+
      apply vcg_solve
      apply vcg_rl
       apply vcg_compat

       apply (isep_rule rule: arl_elem_assn_string_assnI)
       apply (isep_rule rule: pure_pure_asm_prefixI, simp)        
       apply (sepEwith simp)
       apply simp

      apply vcg_solve
      apply vcg

      apply vcg_compat
      apply isep_intro_ex
      apply isep_assumption


      apply (isep_drule drule: arl_elem_assn_string_assnI)
        apply (sepEwith simp)
       apply isep_assumption

      apply (isep_drule drule: arl_elem_assn_update)
        apply simp_all
      apply (sepEwith simp)
      unfolding is_id_bijection_def list_id_map_def map_comp_def
      apply auto
      by (simp add: drop_Suc_nth)
    subgoal using Suc by simp (*unreachable*)
    done
qed


lemma make_id_map_loop'_rule:
  "
  llvm_htriple
  (string_list_assn strs strsi)
  (make_id_map_loop' strsi)
  (\<lambda>mi. (EXS m. map.rbt_map_assn m mi **
                  string_list_assn strs strsi **
                  \<up>(is_id_bijection strs m (list_id_map strs))))
  "
  unfolding make_id_map_loop'_def
  supply llc_for_range_rule[where I="make_id_map_loop'_inv strs strsi", vcg_rules]
  apply vcg
  apply vcg_rl
  (*precond*)
  unfolding make_id_map_loop'_inv_def
  apply vcg_try_solve
  apply vcg_compat
  unfolding is_id_bijection_def apply simp
    apply (sepEwith simp)
  subgoal for asf x r ra s ia iia si (*step*)
    apply vcg
      (*arl copy*)
    apply vcg_rl 
     apply vcg_compat
     apply (isep_drule drule: string_assn_arl_elem_assnI)
     apply isep_extract_pure
     apply (isep_rule rule: sep_pureI, simp)
     apply (sepE | find_sep)+
    (*done*)
    apply vcg_solve
    (*insert*)
    apply vcg_rl
     apply vcg_compat
     apply (isep_rule rule: arl_elem_assn_string_assnI)
     apply (isep_rule rule: pure_pure_asm_prefixI, simp)        
     apply (sepEwith simp)
    (*done*)
    apply vcg_solve
    apply vcg
        apply vcg_compat
      apply isep_intro_ex
      apply isep_assumption


      apply (isep_drule drule: arl_elem_assn_string_assnI)
        apply (sepEwith simp)
       apply isep_assumption

      apply (isep_drule drule: arl_elem_assn_update)
        apply simp_all
    apply (sep | find_sep)+
      unfolding is_id_bijection_def list_id_map_def map_comp_def
      apply (simp add: take_Suc_conv_app_nth)
      done
    subgoal (*post loop*) by vcg_solve+
    done




definition make_id_map_rec
  :: "stringi array_list_64 \<Rightarrow> ((stringi, 64 word) rbti \<times> stringi array_list_64) llM" where
  "make_id_map_rec strs =
  do {
    m \<leftarrow> make_id_map_rec' strs 0;
    return (m, strs)
  }"


definition make_id_map_loop
  :: "stringi array_list_64 \<Rightarrow> ((stringi, 64 word) rbti \<times> stringi array_list_64) llM" where
  "make_id_map_loop strs =
  do {
    m \<leftarrow> make_id_map_loop' strs;
    return (m, strs)
  }"


lemmas [llvm_code] = make_id_map_rec_def make_id_map_loop_def


lemma make_id_map_rec_rule:
  "
  llvm_htriple
  (string_list_assn strs strsi)
  (make_id_map_rec strsi)
  (\<lambda>(mi, li). EXS m l. map.rbt_map_assn m mi ** string_list_assn l li ** \<up>(is_id_bijection strs m (list_id_map l)))
"
  supply make_id_map_rec'_rule[vcg_rules]
  unfolding make_id_map_rec_def
  apply vcg
  done

lemma make_id_map_loop_rule:
  "
  llvm_htriple
  (string_list_assn strs strsi)
  (make_id_map_loop strsi)
  (\<lambda>(mi, li). (EXS m l. map.rbt_map_assn m mi ** string_list_assn l li ** \<up>(is_id_bijection strs m (list_id_map l))))
"
  supply make_id_map_loop'_rule[vcg_rules]
  unfolding make_id_map_loop_def
  apply vcg
  done


end