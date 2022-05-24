theory OptionI
  imports Isabelle_LLVM.LLVM_DS_Dflt
  Main
begin


datatype 'a option_i =
  OPTION_I (val: 'a) (flag: "8 word")
hide_const (open) val flag

instantiation option_i :: (llvm_rep) llvm_rep
begin


definition to_val_option_i :: "'a option_i \<Rightarrow> llvm_val" where
  "to_val_option_i opti \<equiv> (
    case opti of (OPTION_I x flag)  \<Rightarrow> LL_STRUCT [to_val x, to_val flag]
  )"


definition from_val_option_i :: "llvm_val \<Rightarrow> 'a option_i" where
  "from_val_option_i val \<equiv> (
    case val of
     LL_STRUCT [x_val, flag_val] \<Rightarrow> OPTION_I (from_val x_val) (from_val flag_val)|
      _ \<Rightarrow> undefined
  )"


definition "struct_of_option_i (_ :: 'a option_i itself) \<equiv> 
  VS_STRUCT [struct_of TYPE('a), struct_of TYPE(8 word)]"


definition "init_option_i \<equiv> OPTION_I init init" 

instance
proof(standard, goal_cases)
  case 1
  then show ?case
    unfolding from_val_option_i_def to_val_option_i_def id_def
    apply standard
    by (auto split:  option_i.split)
next
  case (2 v)
  then show ?case
    unfolding from_val_option_i_def to_val_option_i_def struct_of_option_i_def
    by (auto split: llvm_val.split)
next
  case (3 x)
  then show ?case
    unfolding to_val_option_i_def struct_of_option_i_def
    by (auto split: option_i.split)
next
  case 4
  then show ?case
    unfolding to_val_option_i_def init_option_i_def struct_of_option_i_def
    by (auto simp add: init_zero to_val_word_def)
qed
end


subsubsection \<open>Setup for LLVM code export\<close>
text \<open>Declare structure to code generator.\<close>
lemma to_val_option_i[ll_to_val]:
  "to_val opti = LL_STRUCT [to_val (option_i.val opti),
                            to_val (option_i.flag opti)]"
  by (cases opti; (simp add: to_val_option_i_def))
  

subsubsection \<open>Code Generator Preprocessor Setup\<close>  
text \<open>The next two are auxiliary lemmas\<close>
lemma option_i_insert_value:
  "ll_insert_value (OPTION_I x flag) xn 0 = Mreturn (OPTION_I xn flag)"
  "ll_insert_value (OPTION_I x flag) flagn (Suc 0) = Mreturn (OPTION_I x flagn)"
  by (simp add:
      ll_insert_value_def
      llvm_insert_value_def
      to_val_option_i_def
      checked_from_val_def
      struct_of_option_i_def
      from_val_option_i_def)+


lemma option_i_extract_value:
  "ll_extract_value (OPTION_I x flag) 0 = Mreturn x"
  "ll_extract_value (OPTION_I x flag) (Suc 0) = Mreturn flag"
  by (simp add:
      ll_extract_value_def
      llvm_extract_value_def 
      checked_from_val_def
      to_val_option_i_def)+


text \<open>Lemmas to translate node construction and destruction\<close>
lemma inline_return_option_i[llvm_pre_simp]: "Mreturn (OPTION_I x flag) =
   doM {
    res \<leftarrow> ll_insert_value init x 0;
    res \<leftarrow> ll_insert_value res flag 1;
    Mreturn res
  }"
  by (auto simp: init_option_i_def option_i_insert_value)


lemma inline_option_i_case[llvm_pre_simp]: "
  (case opti of (OPTION_I x flag) \<Rightarrow> f x flag) =
   doM {
    x \<leftarrow> ll_extract_value opti 0;
    flag \<leftarrow> ll_extract_value opti 1;
    f x flag
  }"  
  apply (cases opti)
  by (auto simp: option_i_extract_value)


lemma inline_return_option_i_case[llvm_pre_simp]:
 "Mreturn (case opti of (OPTION_I x flag) \<Rightarrow> f x flag) = 
  doM {
    x \<leftarrow> ll_extract_value opti 0;
    flag \<leftarrow> ll_extract_value opti 1;
    Mreturn (f x flag)   
  }"  
  apply (cases opti)
  by (auto simp: option_i_extract_value)


lemmas [llvm_inline] = option_i.val_def option_i.flag_def


locale option_impl =
  fixes elem_assn :: "('a, 'ai) dr_assn"
begin


fun option_assn' :: "'a option \<Rightarrow> 'ai option_i \<Rightarrow> ll_assn" where
  "option_assn' None (OPTION_I xi flag) = \<up>(flag = 0)"
| "option_assn' (Some x) (OPTION_I xi flag) = (\<up>(flag = 1) ** \<upharpoonleft>elem_assn x xi)"


definition "option_assn \<equiv> mk_assn option_assn'"


lemma option_assn_None [simp]: "\<upharpoonleft>option_assn None (OPTION_I xi flag) = \<up>(flag = 0)"
  unfolding option_assn_def by auto


lemma option_assn_Some [simp]: 
  "\<upharpoonleft>option_assn (Some x) (OPTION_I xi flag) =(\<up>(flag = 1) ** \<upharpoonleft>elem_assn x xi)"
  unfolding option_assn_def by auto


lemma option_assn_0 [simp]: "\<upharpoonleft>option_assn opt (OPTION_I xi 0) = \<up>(opt = None)"
  unfolding option_assn_def
  by (cases opt; simp)


end


end