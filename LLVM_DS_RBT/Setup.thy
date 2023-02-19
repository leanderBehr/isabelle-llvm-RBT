theory Setup
  imports   
    Isabelle_LLVM.LLVM_DS_All
    Abstract_Rbt
    "Separation_Logic_Solver/Methods"
begin


subsection \<open>RBT NODE Datatype\<close>

text_raw \<open>\snip{rbtnodedef}{1}{2}{%\<close>
datatype ('key :: llvm_rep, 'value :: llvm_rep) rbt_node =
  RBT_NODE
  (color: "8 word")
  (left: "('key,'value) rbt_node ptr")
  (key: 'key) 
  (val: 'value)
  (right: "('key,'value) rbt_node ptr")
text_raw \<open>}%endsnip\<close>

hide_const (open) color left key val right


type_synonym ('k, 'v) rbti = "('k, 'v) rbt_node ptr"  


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
    show "from_val (to_val x) = x" by (cases x; simp)
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
    by (simp add: init_zero init_rbt_node_def struct_of_rbt_node_def to_val_word_def to_val_ptr_def null_def)
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


lemma inline_node_case [llvm_pre_simp]: "
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


lemma inline_return_node_case [llvm_pre_simp]: 
  "Mreturn (case x of (RBT_NODE c l k v r) \<Rightarrow> f c l k v r) = 
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


definition [llvm_pre_simp, simp]: 
  "mod_ptr f n_p \<equiv>
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


fun color_pred where 
  "color_pred color.R ci = (ci = 0)"
| "color_pred color.B ci = (ci = 1)"


abbreviation "color_assn c ci \<equiv> \<up>(color_pred c ci)" 


lemma color_assn_R_0 [fri_red_rules]:
  "is_sep_red \<box> \<box> \<box> (color_assn color.R 0)"
  apply (rule is_sep_redI)
  apply sep
  by simp_all


lemma color_assn_B_1 [fri_red_rules]:
  "is_sep_red \<box> \<box> \<box> (color_assn color.B 1)"
  apply (rule is_sep_redI)
  apply sep
  by simp_all


subsection \<open>Linorder Locale\<close>


locale linorder_impl =
  fixes 
    abs_type :: "'a :: linorder itself" and
    conc_type :: "'ai :: llvm_rep itself" and
    lt_impl :: "'ai \<Rightarrow> 'ai \<Rightarrow> 1 word llM" and
    elem_assn :: "('a, 'ai) dr_assn"
  assumes lt_impl_rule [vcg_rules]: 
    "llvm_htriple
            (\<upharpoonleft>elem_assn l li ** \<upharpoonleft>elem_assn r ri)
            (lt_impl li ri)
            (\<lambda>res. 
              \<upharpoonleft>bool.assn (l < r) res **
              \<upharpoonleft>elem_assn l li **
              \<upharpoonleft>elem_assn r ri)"


subsection \<open>RBT Locale\<close>


locale monad_syntax_M_loc
begin

unbundle monad_syntax_M

end


locale rbt_impl_deps = 
  monad_syntax_M_loc +
  llvm_prim_ctrl_setup +
  llvm_prim_arith_setup +
  llvm_prim_setup


locale rbt_impl =
  linorder_impl key_type key_type_i lt_impl key_assn
  for
    key_type :: "'k :: linorder itself" and
    key_type_i :: "'ki :: llvm_rep itself" and
    value_type :: "'v itself" and
    value_type_i :: "'vi :: llvm_rep itself" and    

lt_impl and
key_assn and
key_free :: "'ki \<Rightarrow> unit llM" and
value_assn :: "('v, 'vi) dr_assn" and
value_free :: "'vi \<Rightarrow> unit llM" +
assumes
  key_free_rule [vcg_rules]: 
  "
      llvm_htriple
      (\<upharpoonleft>key_assn k ki)
      (key_free ki)
      (\<lambda>_. \<box>)
    " and
  value_free_rule [vcg_rules]:
  "
      llvm_htriple
      (\<upharpoonleft>value_assn v vi)
      (value_free vi)
      (\<lambda>_. \<box>)
    "
begin
interpretation rbt_impl_deps .


subsection \<open>RBT Assertion\<close>

fun rbt_assn :: "
  ('k, 'v) rbt \<Rightarrow>
  ('ki, 'vi) rbti \<Rightarrow>
  ll_assn
" where
  "rbt_assn rbt.Empty p = \<up>(p=null)"
| "rbt_assn (rbt.Branch c l k v r) p = (
    EXS ci li ki vi ri. 
      \<upharpoonleft>ll_bpto (RBT_NODE ci li ki vi ri) p **
      color_assn c ci **
      rbt_assn l li **
      \<upharpoonleft>key_assn k ki **
      \<upharpoonleft>value_assn v vi **
      rbt_assn r ri
  )"
declare rbt_assn.simps(2)[simp del]
lemmas rbt_assn_unfold = rbt_assn.simps(2)

fun rbt_assn_full where "rbt_assn_full t ti = (rbt_assn t ti ** \<up>(is_rbt t))"

lemma rbt_sorted_key_uniqI:
  "rbt_sorted (Branch c l k v r) \<Longrightarrow> k \<notin> set (RBT_Impl.keys l)"
  "rbt_sorted (Branch c l k v r) \<Longrightarrow> k \<notin> set (RBT_Impl.keys r)"
   apply simp_all
  unfolding rbt_less_prop rbt_greater_prop
  by blast+


lemma rbt_sorted_subtrees_disjoint:
  "rbt_sorted (Branch c l k v r) \<Longrightarrow> set (RBT_Impl.keys l) \<inter> set (RBT_Impl.keys r) = {}"
  apply simp
  unfolding rbt_less_prop rbt_greater_prop
  by fastforce


lemma [simp]: "rbt_assn t null = \<up>(t=rbt.Empty)"
  by (cases t; simp add: rbt_assn_unfold pure_true_conv)


lemma [simp]: "rbt_assn_full t null = \<up>(t=rbt.Empty)"
  by (cases t; simp add: pure_true_conv)


subsection \<open>Load Rule\<close>


lemma load_rbt [vcg_rules]:
  "
    llvm_htriple
    (rbt_assn (Branch c l k v r) ti)
    (ll_load ti)
    (\<lambda>res.
      EXS ci li ki vi ri.
        \<upharpoonleft>ll_bpto res ti **
        color_assn c ci **
        rbt_assn l li **
        \<upharpoonleft>key_assn k ki **
        \<upharpoonleft>value_assn v vi **  
        rbt_assn r ri **
        \<up>(res = RBT_NODE ci li ki vi ri)
    )
  "
  unfolding rbt_assn_unfold
  apply vcg
  done


lemma load_rbt_non_null:
  "
    ti \<noteq> null \<Longrightarrow>
    llvm_htriple
    (rbt_assn t ti)
    (ll_load ti)
    (\<lambda>res.
      EXS ci li ki vi ri c l k v r.
        \<upharpoonleft>ll_bpto res ti **
        color_assn c ci **
        rbt_assn l li **
        \<upharpoonleft>key_assn k ki **
        \<upharpoonleft>value_assn v vi **  
        rbt_assn r ri **
        \<up>(res = RBT_NODE ci li ki vi ri) **
        \<up>(t = rbt.Branch c l k v r))
  "
  apply vcg
  apply (cases t)
  subgoal by (simp add: rbt_assn_unfold) (*contradiction*)
  subgoal by vcg
  done


subsection \<open>Reduction Rules\<close>


lemma unfold_rbt_assn_red_rule [fri_red_rules]: 
  "
    is_sep_red
    \<box>
    (color_assn c ci \<and>* rbt_assn l li \<and>* \<upharpoonleft>key_assn k ki \<and>* \<upharpoonleft>value_assn v vi \<and>* rbt_assn r ri)
    (\<upharpoonleft>ll_bpto (RBT_NODE ci li ki vi ri) ti)
    (rbt_assn (rbt.Branch c l k v r) ti)
  "
  apply (rule is_sep_redI)
  apply (simp add: rbt_assn_unfold)
  subgoal premises prems for Ps Qs
    apply (sepE isep_dest: prems)
      (*
    apply (sep_drule prems)
    apply (simp only: fri_extract_simps entails_lift_extract_simps cong: entails_pre_cong)
    apply clarify
    apply fri
    *)
    done
  done

subsection \<open>Empty Constructor\<close>


definition empty :: "('ki, 'vi) rbti llM"
  where [llvm_code]: "empty \<equiv> Mreturn null"


lemma empty_correct [vcg_rules]: 
  "llvm_htriple
   \<box>
   empty
   (\<lambda> r. rbt_assn rbt.Empty r)"
  unfolding empty_def
  by vcg

end


end