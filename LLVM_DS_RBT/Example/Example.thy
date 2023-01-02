theory Example
  imports 
    "../Map_Interface"
    List_Less
    List_Copy
    Arl_Ext
    "../Export_Wrappers"
begin


definition "string_dr_assn \<equiv> mk_assn string_assn" 


abbreviation "string_arl_assn strs strsi \<equiv> arl_mems_assn' string_dr_assn strs strsi"


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


definition list_index_mapping :: "'a list \<Rightarrow> (nat \<rightharpoonup> 'a)" where
  "list_index_mapping xs = (\<lambda>i. if i < length xs then Some (xs ! i) else None)"


definition is_index_mapping :: "'a list \<Rightarrow> ('a \<rightharpoonup> 'b) \<Rightarrow> ('b \<rightharpoonup> 'a) \<Rightarrow> bool" where
  "is_index_mapping xs m1 m2 \<equiv> (\<forall> x \<in> set xs. (m2 \<circ>\<^sub>m m1) x = Some x)"


type_synonym stringi = "(8 word, 64) array_list"


type_synonym 'a array_list_64 = "('a, 64) array_list" 


interpretation copy: arl_copy "TYPE(8 word)" snat.assn "\<lambda>x. Mreturn x"
  by (standard, vcg)


interpretation monad_syntax_M_loc .


lemma arl_mems_nth_rule [vcg_rules]:
"
  llvm_htriple
  (arl_mems_assn_ex A xs xsi arl {} ** \<upharpoonleft>snat.assn i ii ** \<up>(i < length xs))
  (arl_nth arl ii)
  (\<lambda>elem. arl_mems_assn_ex A xs xsi arl {i} ** \<upharpoonleft>A (xs ! i) elem ** \<up>(elem = xsi ! i))
"
  unfolding arl_mems_assn_ex_def
  apply vcg
  apply vcg_compat
  apply (sepwith ignore)
    apply ((auto dest!: list_assn_pure_partD))
  unfolding idxe_map_def
  by (simp add: restrict_map_insert)


partial_function (M) make_index_mapping' where [llvm_code]:
  "make_index_mapping' strs i = 
  do {
    len \<leftarrow> arl_len strs;
    if i < len
    then do {
      ip1 \<leftarrow> ll_add i 1;
      m \<leftarrow> make_index_mapping' strs ip1;
      str \<leftarrow> arl_nth strs i;
      str_copy \<leftarrow> copy.arl_copy str;
      map.insert str_copy i m
    }
    else map.empty
  }"


definition make_index_mapping'' where [llvm_code]:
  "make_index_mapping'' strs = 
  do {
    len \<leftarrow> arl_len strs;
    empty_map \<leftarrow> map.empty;
    llc_for_range 0 len
    (\<lambda>i m.
      do
      {
        str \<leftarrow> arl_nth strs i;
        str_copy \<leftarrow> copy.arl_copy str;
        map.insert str_copy i m
      }
    )
    empty_map
  }"


definition "make_index_mapping''_loop_inv
  strs strsi i mi \<equiv> 
  (
    EXS m. map.rbt_map_assn m mi **
    string_arl_assn strs strsi **
    \<up>(is_index_mapping (take i strs) m (list_index_mapping strs))
  )" 
  
declare string_dr_assn_eq[simp del]


lemma 
  pure_part_pure_conjI:
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
    

lemma string_assn_arl_mems_assnI:
"\<upharpoonleft>string_dr_assn str (stri::(8 word, 'l::len2) array_list)
   \<turnstile> arl_mems_assn' snat.assn str stri ** \<up>(4 < LENGTH('l))"
  unfolding string_dr_assn_eq arl_mems_assn_def'
  apply (sepwith ignore)
  apply isep_intro_ex
  apply (sepwith ignore)
  unfolding LLVM_DS_List_Assn.list_assn_def
  apply (simp_all add: pure_true_conv)
proof -
  fix x::"8 word list"
  assume assm: "\<forall>i<length str. \<flat>\<^sub>psnat.assn (str ! i) (x ! i)"
  have 1: "sep_is_pure_assn (\<Union>*xa\<in>{0..<length str}. \<upharpoonleft>snat.assn (str ! xa) (x ! xa))" 
    apply (rule sep_is_pure_assn_imgI)
    by (meson is_pure_def snat.assn_pure)

  have 2: "pure_part (\<Union>*xa\<in>{0..<length str}. \<upharpoonleft>snat.assn (str ! xa) (x ! xa))"
    apply (rule pure_sep_set_img_pure_partI)
     apply auto
     apply (meson is_pure_def snat.assn_pure)
    using assm by (simp add: thin_dr_pure_asm)

  from 1 2 show "\<box> \<turnstile> (\<Union>*xa\<in>{0..<length str}. \<upharpoonleft>snat.assn (str ! xa) (x ! xa))"
    by (metis (mono_tags, lifting) pure_part_pure_eq sep_pureI)
qed


lemma 
  arl_mems_assn_string_assnI:
  "arl_mems_assn' snat.assn str (stri::(8 word, 'l::len2) array_list) **
   \<up>(4 < LENGTH('l)) \<turnstile> \<upharpoonleft>string_dr_assn str stri"
    unfolding string_dr_assn_eq arl_mems_assn_def'
    apply (sepEwith ignore)
    subgoal unfolding LLVM_DS_List_Assn.list_assn_def
      apply simp
      apply (rule pure_entails_boxI sep_is_pure_assn_conjI | simp)+
      apply (rule sep_is_pure_assn_imgI)
      by (simp add: snat.assn_def)    
   
    apply (auto dest: list_assn_pure_partD)[1]
    apply (simp add: dr_assn_pure_asm_prefix_def list_assn_pure_partD snat.assn_pure) 
    done


lemma arl_mems_assn_update:
  assumes "i < length xs" and "i\<in>ex"
  shows
  "arl_mems_assn_ex A xs xsi arl ex ** \<upharpoonleft>A (xs ! i) (xsi ! i) \<turnstile>
   arl_mems_assn_ex A xs xsi arl (ex - {i})"
  unfolding arl_mems_assn_ex_def
  apply isep_extract_pure
  apply (isep_drule drule: LLVM_DS_List_Assn.list_assn_update[where i=i]) 
  using assms apply (auto simp: idxe_map_def dest: list_assn_pure_partD)
  apply sep
  done


lemma make_index_mapping'_rule:
  "
  llvm_htriple
  (string_arl_assn strs strsi ** \<upharpoonleft>snat.assn i ii)
  (make_index_mapping' strsi ii)
  (\<lambda>mi. (EXS m. map.rbt_map_assn m mi **
                  string_arl_assn strs strsi **
                  \<up>(is_index_mapping (drop i strs) m (list_index_mapping strs))))
"
proof(induction "length strs - i" arbitrary: i ii)
  case 0
  from 0 show ?case 
    apply (subst make_index_mapping'.simps)
    apply vcg
    apply vcg_compat
    apply (sepEwith ignore)
    unfolding is_index_mapping_def
    by simp
next
  case (Suc x)
  note Suc(1)[vcg_rules]
  show ?case
    apply (subst make_index_mapping'.simps)
    apply vcg
    subgoal using Suc(2) by simp
    subgoal
      apply vcg
      apply vcg_rl
       apply vcg_compat
       apply (isep_drule drule: string_assn_arl_mems_assnI)
       apply isep_extract_pure
       apply (isep_rule rule: sep_pureI, simp)
       apply (sepEwith ignore)
      apply vcg_solve
      apply vcg_rl
       apply vcg_compat

       apply (isep_rule rule: arl_mems_assn_string_assnI)
       apply (isep_rule rule: pure_pure_asm_prefixI, simp)        
       apply (sepEwith simp)
       apply simp

      apply vcg_solve
      apply vcg

      apply vcg_compat
      apply isep_intro_ex
      apply isep_assumption


      apply (isep_drule drule: arl_mems_assn_string_assnI)
        apply (sepEwith simp)
       apply isep_assumption

      apply (isep_drule drule: arl_mems_assn_update)
        apply simp_all
      apply (sepEwith simp)
      unfolding is_index_mapping_def list_index_mapping_def map_comp_def
      apply auto
      by (simp add: drop_Suc_nth)
    subgoal using Suc by simp (*unreachable*)
    done
qed


lemma make_index_mapping''_rule:
  "
  llvm_htriple
  (string_arl_assn strs strsi)
  (make_index_mapping'' strsi)
  (\<lambda>mi. (EXS m. map.rbt_map_assn m mi **
                  string_arl_assn strs strsi **
                  \<up>(is_index_mapping strs m (list_index_mapping strs))))
  "
  unfolding make_index_mapping''_def
  supply llc_for_range_rule[where I="make_index_mapping''_loop_inv strs strsi", vcg_rules]
  apply vcg
  apply vcg_rl
  (*precond*)
  unfolding make_index_mapping''_loop_inv_def
  apply vcg_try_solve
  apply vcg_compat
  unfolding is_index_mapping_def apply simp
    apply (sepEwith simp)
  subgoal for asf x r ra s ia iia si (*step*)
    apply vcg
      (*arl copy*)
    apply vcg_rl 
     apply vcg_compat
     apply (isep_drule drule: string_assn_arl_mems_assnI)
     apply isep_extract_pure
     apply (isep_rule rule: sep_pureI, simp)
     apply (sepEwith ignore)
    (*done*)
    apply vcg_solve
    (*insert*)
    apply vcg_rl
     apply vcg_compat
     apply (isep_rule rule: arl_mems_assn_string_assnI)
     apply (isep_rule rule: pure_pure_asm_prefixI, simp)        
     apply (sepEwith simp)
    (*done*)
    apply vcg_solve
    apply vcg
        apply vcg_compat
      apply isep_intro_ex
      apply isep_assumption


      apply (isep_drule drule: arl_mems_assn_string_assnI)
        apply (sepEwith simp)
       apply isep_assumption

      apply (isep_drule drule: arl_mems_assn_update)
        apply simp_all
      apply (sepwith ignore)
      unfolding is_index_mapping_def list_index_mapping_def map_comp_def
      apply (simp add: take_Suc_conv_app_nth)
      done
    subgoal (*post loop*) by vcg_solve+
    done


definition make_index_mapping
  :: "stringi array_list_64 \<Rightarrow> ((stringi, 64 word) rbti \<times> stringi array_list_64) llM" where
  "make_index_mapping strs =
  do {
    m \<leftarrow> make_index_mapping' strs 0;
    return (m, strs)
  }"


definition make_index_mapping_alt
  :: "stringi array_list_64 \<Rightarrow> ((stringi, 64 word) rbti \<times> stringi array_list_64) llM" where
  "make_index_mapping_alt strs =
  do {
    m \<leftarrow> make_index_mapping'' strs;
    return (m, strs)
  }"


lemmas [llvm_code] = make_index_mapping_def make_index_mapping_alt_def


lemma make_index_mapping_rule:
  "
  llvm_htriple
  (string_arl_assn strs strsi)
  (make_index_mapping strsi)
  (\<lambda>(mi, li). (EXS m l. map.rbt_map_assn m mi ** string_arl_assn l li ** \<up>(is_index_mapping strs m (list_index_mapping l))))
"
  supply make_index_mapping'_rule[vcg_rules]
  unfolding make_index_mapping_def
  apply vcg
  done

lemma make_index_mapping_alt_rule:
  "
  llvm_htriple
  (string_arl_assn strs strsi)
  (make_index_mapping_alt strsi)
  (\<lambda>(mi, li). (EXS m l. map.rbt_map_assn m mi ** string_arl_assn l li ** \<up>(is_index_mapping strs m (list_index_mapping l))))
"
  supply make_index_mapping''_rule[vcg_rules]
  unfolding make_index_mapping_alt_def
  apply vcg
  done


end