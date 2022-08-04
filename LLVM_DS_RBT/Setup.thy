theory Setup
  imports
    Isabelle_LLVM.LLVM_DS_All
    Abstract_Rbt
begin


subsection \<open>RBT_NODE Datatype\<close>


datatype ('key :: llvm_rep, 'value :: llvm_rep) rbt_node =
  RBT_NODE
  (color: "8 word")
  (left: "('key,'value) rbt_node ptr")
  (key: 'key) 
  (val: 'value)
  (right: "('key,'value) rbt_node ptr")

hide_const (open) color left key val right

type_synonym ('k, 'v) rbti = "('k, 'v) rbt_node ptr"  


text \<open>Abstract type rbt represented by rbti where null represents rbt.Empty\<close>


subsubsection \<open>Encoding to heap-representable\<close>


instantiation rbt_node :: (llvm_rep, llvm_rep) llvm_rep
begin

fun to_val_rbt_node where
  "to_val_rbt_node (RBT_NODE col l_child k v r_child) = 
    LL_STRUCT [to_val col, to_val l_child, to_val k, to_val v, to_val r_child]"

fun from_val_rbt_node where
  "from_val_rbt_node (LL_STRUCT [col, l_child_rep, k_rep, v_rep, r_child_rep]) = 
    RBT_NODE (from_val col)
             (from_val l_child_rep)
             (from_val k_rep)
             (from_val v_rep)
             (from_val r_child_rep)"
| "from_val_rbt_node _ = undefined"

definition "struct_of_rbt_node (_::('a, 'b) rbt_node itself) = 
    VS_STRUCT [VS_INT 8, VS_PTR, struct_of TYPE('a), struct_of TYPE('b), VS_PTR]"

definition "init_rbt_node \<equiv> RBT_NODE init init init init init"

instance 
proof(standard, goal_cases)
  case 1
  then show ?case unfolding comp_def id_def
  proof
    fix x:: "('a,'b) rbt_node"
    show "from_val (to_val x) = x"
      by (cases x; simp)
  qed
next
  case (2 v)
  then show ?case
    unfolding struct_of_rbt_node_def
    by (cases v rule: from_val_rbt_node.cases; simp)
next
  case (3 x)
  then show ?case
    unfolding struct_of_rbt_node_def
    by (cases x; simp)
next
  case 4
  then show ?case
    unfolding init_rbt_node_def
      struct_of_rbt_node_def
    by (auto simp: init_zero to_val_word_def to_val_ptr_def null_def)
qed
end


subsubsection \<open>Setup for LLVM code export\<close>
text \<open>Declare structure to code generator.\<close>
lemma to_val_rbt_node [ll_struct_of]:
  "struct_of TYPE(('k::llvm_rep, 'v::llvm_rep) rbt_node) =
      VS_STRUCT 
      [
        struct_of TYPE(8 word),
        struct_of TYPE(('k, 'v) rbt_node ptr),
        struct_of TYPE('k),
        struct_of TYPE('v),
        struct_of TYPE(('k, 'v) rbt_node ptr)
      ]"
  unfolding struct_of_rbt_node_def
  by auto


text \<open>Declare as named structure. Required b/c of circular reference.\<close>
lemma [ll_identified_structures]:
  "ll_is_identified_structure ''rbt_node'' TYPE((_, _) rbt_node)"  
  unfolding ll_is_identified_structure_def
    struct_of_rbt_node_def
  by simp


subsubsection \<open>Code Generator Preprocessor Setup\<close>  
text \<open>The next two are auxiliary lemmas\<close>
lemma rbt_node_insert_value [simp]:
  "ll_insert_value (RBT_NODE c l k v r) ci 0 = Mreturn (RBT_NODE ci l k v r)"
  "ll_insert_value (RBT_NODE c l k v r) li (Suc 0) = Mreturn (RBT_NODE c li k v r)"
  "ll_insert_value (RBT_NODE c l k v r) ki 2 = Mreturn (RBT_NODE c l ki v r)"
  "ll_insert_value (RBT_NODE c l k v r) vi 3 = Mreturn (RBT_NODE c l k vi r)"
  "ll_insert_value (RBT_NODE c l k v r) ri 4 = Mreturn (RBT_NODE c l k v ri)"
  by (simp_all add:
      ll_insert_value_def llvm_insert_value_def
      Let_def checked_from_val_def struct_of_rbt_node_def)


lemma rbt_node_extract_value [simp]:
  "ll_extract_value (RBT_NODE c l k v r) 0 = Mreturn c"
  "ll_extract_value (RBT_NODE c l k v r) (Suc 0) = Mreturn l"
  "ll_extract_value (RBT_NODE c l k v r) 2 = Mreturn k"
  "ll_extract_value (RBT_NODE c l k v r) 3 = Mreturn v"
  "ll_extract_value (RBT_NODE c l k v r) 4 = Mreturn r"
  by (simp_all add:
      ll_extract_value_def llvm_extract_value_def Let_def checked_from_val_def)


text \<open>Lemmas to translate node construction and destruction\<close>
lemma inline_return_node [llvm_pre_simp]: "Mreturn (RBT_NODE c l k v r) =
   doM {
    res \<leftarrow> ll_insert_value init c 0;
    res \<leftarrow> ll_insert_value res l 1;
    res \<leftarrow> ll_insert_value res k 2;
    res \<leftarrow> ll_insert_value res v 3;
    res \<leftarrow> ll_insert_value res r 4;
    Mreturn res
  }"
  by (auto simp: init_rbt_node_def)


lemma inline_node_case[llvm_pre_simp]: "
  (case x of (RBT_NODE c l k v r) \<Rightarrow> f c l k v r) =
   doM {
    c \<leftarrow> ll_extract_value x 0;
    l \<leftarrow> ll_extract_value x 1;
    k \<leftarrow> ll_extract_value x 2;
    v \<leftarrow> ll_extract_value x 3;
    r \<leftarrow> ll_extract_value x 4;
    f c l k v r
  }"
  apply (cases x)
  by auto


lemma inline_return_node_case[llvm_pre_simp]: "Mreturn (case x of (RBT_NODE c l k v r) \<Rightarrow> f c l k v r) = 
  doM {
    c \<leftarrow> ll_extract_value x 0;
    l \<leftarrow> ll_extract_value x 1;
    k \<leftarrow> ll_extract_value x 2;
    v \<leftarrow> ll_extract_value x 3;
    r \<leftarrow> ll_extract_value x 4;
    Mreturn (f c l k v r)   
  }"
  apply (cases x)
  by auto


lemmas [llvm_inline] = 
  rbt_node.color_def
  rbt_node.left_def
  rbt_node.key_def
  rbt_node.val_def
  rbt_node.right_def


subsubsection \<open>Setters\<close>


definition set_color :: 
  "('k::llvm_rep, 'v::llvm_rep) rbt_node \<Rightarrow> 8 word \<Rightarrow> _"
  where "set_color node col \<equiv> ll_insert_value node col 0"
definition set_left :: 
  "('k::llvm_rep, 'v::llvm_rep) rbt_node \<Rightarrow> ('k, 'v) rbti \<Rightarrow> _"
  where "set_left node lhs \<equiv> ll_insert_value node lhs 1"
definition set_key :: 
  "('k::llvm_rep, 'v::llvm_rep) rbt_node \<Rightarrow> 'k \<Rightarrow> _"
  where "set_key node k \<equiv> ll_insert_value node k 2"
definition set_value :: 
  "('k::llvm_rep, 'v::llvm_rep) rbt_node \<Rightarrow> 'v \<Rightarrow> _"
  where "set_value node v \<equiv> ll_insert_value node v 3"
definition set_right :: 
  "('k::llvm_rep, 'v::llvm_rep) rbt_node \<Rightarrow> ('k, 'v) rbti \<Rightarrow> _"
  where "set_right node rhs \<equiv> ll_insert_value node rhs 4"


definition [llvm_pre_simp, simp]: "mod_ptr f n_p \<equiv>
  doM {
    n_pre \<leftarrow> ll_load n_p;
    n_post \<leftarrow> f n_pre;
    ll_store n_post n_p 
  }"


definition "set_color_p x \<equiv> mod_ptr (\<lambda>n. set_color n x)"
definition "set_left_p x \<equiv> mod_ptr (\<lambda>n. set_left n x)"
definition "set_key_p x \<equiv> mod_ptr (\<lambda>n. set_key n x)"
definition "set_value_p x \<equiv> mod_ptr (\<lambda>n. set_value n x)"
definition "set_right_p x \<equiv> mod_ptr (\<lambda>n. set_right n x)"


lemmas [llvm_inline, simp] =
  set_color_def
  set_left_def
  set_key_def
  set_value_def
  set_right_def

  set_color_p_def
  set_left_p_def
  set_key_p_def
  set_value_p_def
  set_right_p_def


subsection \<open>Color Assertion\<close>


fun color_assn' :: "color \<Rightarrow> 8 word \<Rightarrow> ll_assn" where
  "color_assn' color.R rep = \<up>(rep=0)"
| "color_assn' color.B rep = \<up>(rep=1)"


definition "color_assn \<equiv> mk_assn color_assn'"


lemma color_assn_eq: "\<upharpoonleft>color_assn c rep = 
  \<up>(case c of color.R \<Rightarrow> rep = 0 | color.B \<Rightarrow> rep = 1)"
  unfolding color_assn_def 
  by (cases c; simp)


lemma color_assn_pure [is_pure_rule]: "is_pure color_assn" 
  unfolding is_pure_def color_assn_eq by simp


lemma [simp]: "\<upharpoonleft>color_assn color.R rep = \<up>(rep=0)"
  unfolding color_assn_def by simp

lemma [simp]: "\<upharpoonleft>color_assn color.B rep = \<up>(rep=1)"
  unfolding color_assn_def by simp

lemma [simp]: "\<upharpoonleft>color_assn c 0 = \<up>(c = color.R)"
  unfolding color_assn_eq
  by (cases c; auto)

lemma [simp]: "\<upharpoonleft>color_assn c 1 = \<up>(c = color.B)"
  unfolding color_assn_eq
  by (cases c; auto)


lemma [simp]: "\<upharpoonleft>\<^sub>pcolor_assn color.R rep = \<up>(rep=0)"
  by (simp add: dr_assn_pure_prefix_def)

lemma [simp]: "\<upharpoonleft>\<^sub>pcolor_assn color.B rep = \<up>(rep=1)"
  by (simp add: dr_assn_pure_prefix_def)

lemma [simp]: "\<upharpoonleft>\<^sub>pcolor_assn c 0 = \<up>(c = color.R)"
  by (cases c; auto)

lemma [simp]: "\<upharpoonleft>\<^sub>pcolor_assn c 1 = \<up>(c = color.B)"
  by (cases c; auto)


lemma [simp]: "\<flat>\<^sub>pcolor_assn color.R rep = (rep=0)"
  unfolding dr_assn_pure_asm_prefix_def
  using color_assn_pure by auto
  
lemma [simp]: "\<flat>\<^sub>p color_assn color.B rep = (rep=1)"
  unfolding dr_assn_pure_asm_prefix_def
  using color_assn_pure by auto

lemma [simp]: "\<flat>\<^sub>pcolor_assn c 0 = (c = color.R)"
  by (cases c; auto)

lemma [simp]: "\<flat>\<^sub>pcolor_assn c 1 = (c = color.B)"
  by (cases c; auto)


subsection \<open>fb Setup\<close>


definition fb :: "bool \<Rightarrow> 1 word" where "fb = from_bool"


lemma fb_true [simp]: "fb True = 1" 
  unfolding fb_def
  by simp


lemma fb_false [simp]: "fb False = 0" 
  unfolding fb_def
  by simp


lemma fb_num [simp]: 
  "fb x = 0 \<longleftrightarrow> \<not>x"
  "fb x = 1 \<longleftrightarrow> x"
  unfolding fb_def
  by simp+


abbreviation ll_True :: "1 word" where "ll_True \<equiv> 1"
abbreviation ll_False :: "1 word" where "ll_False \<equiv> 0"


subsection \<open>Linorder Locale\<close>


locale linorder_impl =
  fixes lt_impl :: "('ai::llvm_rep) \<Rightarrow> 'ai \<Rightarrow> 1 word llM"
    and elem_assn :: "('a::linorder, 'ai) dr_assn"
  assumes lt_impl_rule [vcg_rules]: 
    "llvm_htriple
            (\<upharpoonleft>elem_assn lhs lhsi ** \<upharpoonleft>elem_assn rhs rhsi)
            (lt_impl lhsi rhsi)
            (\<lambda>r. 
              \<up>(r = fb (lhs < rhs)) **
              \<upharpoonleft>elem_assn lhs lhsi **
              \<upharpoonleft>elem_assn rhs rhsi)"


subsection \<open>RBT Locale\<close>


locale rbt_impl = linorder_impl lt_impl key_assn
  for lt_impl :: "('ki::llvm_rep) \<Rightarrow> 'ki \<Rightarrow> 1 word llM"
    and key_assn :: "('k::linorder, 'ki) dr_assn" +
  fixes key_delete :: "'ki \<Rightarrow> unit llM"
  assumes key_delete_rule [vcg_rules]: "
    llvm_htriple
    (\<upharpoonleft>key_assn k ki)
    (key_delete ki)
    (\<lambda>_.\<box>)
  "
begin
unbundle monad_syntax_M  
interpretation llvm_prim_ctrl_setup .
interpretation llvm_prim_arith_setup .
interpretation llvm_prim_setup .


subsection \<open>RBT Assertion\<close>


fun rbt_assn' :: "
  ('k, 'v) rbt \<Rightarrow>
  ('ki::llvm_rep, 'v::llvm_rep) rbti \<Rightarrow>
  ll_assn
" where
  "rbt_assn' rbt.Empty p = \<up>(p=null)"
| "rbt_assn' (rbt.Branch col lhs k v rhs) p = (
    EXS coli lhsi ki vi rhsi. 
      \<upharpoonleft>ll_bpto (RBT_NODE coli lhsi ki vi rhsi) p **
      \<upharpoonleft>color_assn col coli **
      rbt_assn' lhs lhsi **
      \<upharpoonleft>key_assn k ki **
      \<up>(vi=v) **
      rbt_assn' rhs rhsi
  )"


fun rbt_val_assn where
  "rbt_val_assn (Branch col lhs k v rhs) (RBT_NODE coli lhsi ki vi rhsi) = 
    (
     \<upharpoonleft>color_assn col coli **
      rbt_assn' lhs lhsi **
        \<upharpoonleft>key_assn k ki **
        \<up>(vi=v) **  
      rbt_assn' rhs rhsi
    )" |
  "rbt_val_assn _ _ = sep_false"


lemma entails_exE:
  assumes "\<And>x. P x \<turnstile> Q"
  shows "(EXS x. P x) \<turnstile> Q"
  using assms unfolding entails_def
  by auto


lemma entails_pre_pure_iff:
  fixes P Q R
  shows
  "((\<lambda>s. P \<and> (Q s)) \<turnstile> R) \<longleftrightarrow> (P \<longrightarrow> Q \<turnstile> R)"
  unfolding entails_def
  by blast


lemma "rbt_assn' (Branch col lhs k v rhs) p =
    (EXS n. \<upharpoonleft>ll_bpto n p ** rbt_val_assn (Branch col lhs k v rhs) n)"
  apply (auto simp add: entails_eq_iff)
  subgoal
    apply isep_elim_ex
    apply isep_intro_ex
    apply isep_solver_keep
    apply simp
    done
  subgoal
    apply isep_elim_ex
    subgoal for x
      apply (cases x, simp)
      apply isep_solver
      done
    done
  done


definition "rbt_assn \<equiv> mk_assn rbt_assn'"


lemma rbt_assn_tag_def: "\<upharpoonleft>rbt_assn = rbt_assn'"
  unfolding rbt_assn_def mk_assn_def dr_assn_prefix_def 
  by simp 


lemma[simp]: "\<upharpoonleft>rbt_assn t null = \<up>(t=rbt.Empty)"
  unfolding rbt_assn_def
  by (cases t; auto)


lemma[simp]: "\<upharpoonleft>rbt_assn rbt.Empty p = \<up>(p=null)"
  unfolding rbt_assn_def by simp


lemma rbt_assn_branch_def: "\<upharpoonleft>rbt_assn (Branch col lhs k v rhs) p = (
  EXS coli lhsi ki vi rhsi. 
    \<upharpoonleft>ll_bpto (RBT_NODE coli lhsi ki vi rhsi) p **
    \<upharpoonleft>color_assn col coli **
    \<upharpoonleft>rbt_assn lhs lhsi **
    \<upharpoonleft>key_assn k ki **
    \<up>(vi=v) **  
    \<upharpoonleft>rbt_assn rhs rhsi
  )"
  unfolding rbt_assn_def
  by simp


lemma close_rbt_assn_entails:
  "
  (
    \<upharpoonleft>ll_bpto (RBT_NODE coli lhsi ki vi rhsi) ti **
    \<upharpoonleft>color_assn col coli **  
    \<upharpoonleft>rbt_assn lhs lhsi **
    \<upharpoonleft>key_assn k ki **
    \<upharpoonleft>rbt_assn rhs rhsi
  ) \<turnstile> 
  \<upharpoonleft>rbt_assn (rbt.Branch col lhs k vi rhs) ti
  "
  unfolding rbt_assn_branch_def
  apply (rule ENTAILSD)
  apply vcg_solve
  done


lemma entails_to_state_elim:
  assumes
    "PRE \<turnstile> POST"
    "STATE asf X s"
    "FRAME X PRE Y"
    "STATE asf (POST ** Y) s \<Longrightarrow> thesis"
  shows thesis
  using assms
  using FRAME_def STATE_monoI entails_mp by blast


lemma entails_to_ENTAILS_elim:
  assumes
    "PRE \<turnstile> POST"
    "FRAME P PRE Y"
    "ENTAILS (POST**Y) Q"
  shows "ENTAILS P Q"
  using assms                    
  using ENTAILS_def gen_drule by blast


lemmas close_rbt_assn = entails_to_state_elim[OF close_rbt_assn_entails]
                        entails_to_ENTAILS_elim[OF close_rbt_assn_entails]


subsection \<open>RBT Load Rule\<close>


lemma load_rbt [vcg_rules]:
  "
    llvm_htriple
    (\<upharpoonleft>rbt_assn (Branch col lhs k v rhs) ti)
    (ll_load ti)
    (\<lambda>r. 
      EXS coli lhsi ki vi rhsi.
        \<upharpoonleft>ll_bpto (RBT_NODE coli lhsi ki vi rhsi) ti **
        \<upharpoonleft>color_assn col coli **
        \<upharpoonleft>rbt_assn lhs lhsi **
        \<upharpoonleft>key_assn k ki **
        \<up>(vi=v) **  
        \<upharpoonleft>rbt_assn rhs rhsi **
        \<up>(r = RBT_NODE coli lhsi ki vi rhsi)
    )
  "
  unfolding rbt_assn_branch_def
  by vcg


subsection "Empty Function"


definition empty :: "('ki, 'v) rbti llM"
  where "empty \<equiv> Mreturn null"


lemma empty_correct [vcg_rules]: 
  "llvm_htriple
   \<box>
   empty
   (\<lambda> r. \<upharpoonleft>rbt_assn rbt.Empty r)"
  unfolding empty_def
  by vcg


lemmas [llvm_code] = empty_def


subsection "Reduction Rules"


lemma unfold_rbt_assn_red_rule [fri_red_rules]: "is_sep_red
    \<box>
    (\<upharpoonleft>color_assn c ci ** \<upharpoonleft>rbt_assn l li \<and>* \<upharpoonleft>key_assn k ki \<and>* \<up>(vi = v) \<and>* \<upharpoonleft>rbt_assn r ri)
    (\<upharpoonleft>ll_bpto (RBT_NODE ci li ki vi ri) ti)
    (\<upharpoonleft>rbt_assn (rbt.Branch c l k v r) ti)"
  apply (rule is_sep_redI)
  unfolding rbt_assn_branch_def
  subgoal premises prems for Ps Qs
    apply (sep_drule prems)
    apply (simp only: fri_extract_simps entails_lift_extract_simps cong: entails_pre_cong)
    apply clarify
    apply fri
    done
  done


end


end