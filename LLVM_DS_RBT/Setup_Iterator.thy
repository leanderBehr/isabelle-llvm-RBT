theory Setup_Iterator
  imports
    "../../isabelle_llvm/thys/ds/LLVM_DS_All"
    "HOL-Library.RBT_Impl"
begin
                         
datatype ('key :: llvm_rep, 'value :: llvm_rep) rbt_node =
  RBT_NODE
  (color: "8 word")
  (left: "('key,'value) rbt_node ptr")
  (key: 'key) (val: 'value)
  (right: "('key,'value) rbt_node ptr")


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
lemma to_val_rbt_node[ll_to_val]:
  "to_val x = LL_STRUCT [to_val (rbt_node.color x),
                         to_val (rbt_node.left x),
                         to_val (rbt_node.key x),
                         to_val (rbt_node.val x),
                         to_val (rbt_node.right x)]"
  apply (cases x)
  apply (auto simp: to_val_node_def)
  done


text \<open>Declare as named structure. Required b/c of circular reference.\<close>
lemma [ll_identified_structures]:
  "ll_is_identified_structure ''rbt_node'' TYPE((_, _) rbt_node)"  
  unfolding ll_is_identified_structure_def
    struct_of_rbt_node_def
  by simp


subsubsection \<open>Code Generator Preprocessor Setup\<close>  
text \<open>The next two are auxiliary lemmas\<close>
lemma rbt_node_insert_value:
  "ll_insert_value (RBT_NODE c l k v r) ci 0 = Mreturn (RBT_NODE ci l k v r)"
  "ll_insert_value (RBT_NODE c l k v r) li (Suc 0) = Mreturn (RBT_NODE c li k v r)"
  "ll_insert_value (RBT_NODE c l k v r) ki 2 = Mreturn (RBT_NODE c l ki v r)"
  "ll_insert_value (RBT_NODE c l k v r) vi 3 = Mreturn (RBT_NODE c l k vi r)"
  "ll_insert_value (RBT_NODE c l k v r) ri 4 = Mreturn (RBT_NODE c l k v ri)"
  by (simp_all add:
      ll_insert_value_def llvm_insert_value_def
      Let_def checked_from_val_def struct_of_rbt_node_def)


lemma rbt_node_extract_value:
  "ll_extract_value (RBT_NODE c l k v r) 0 = Mreturn c"
  "ll_extract_value (RBT_NODE c l k v r) (Suc 0) = Mreturn l"
  "ll_extract_value (RBT_NODE c l k v r) 2 = Mreturn k"
  "ll_extract_value (RBT_NODE c l k v r) 3 = Mreturn v"
  "ll_extract_value (RBT_NODE c l k v r) 4 = Mreturn r"
  by (simp_all add:
      ll_extract_value_def llvm_extract_value_def Let_def checked_from_val_def)


text \<open>Lemmas to translate node construction and destruction\<close>
lemma inline_return_node[llvm_pre_simp]: "Mreturn (RBT_NODE c l k v r) =
   doM {
    res \<leftarrow> ll_insert_value init c 0;
    res \<leftarrow> ll_insert_value res l 1;
    res \<leftarrow> ll_insert_value res k 2;
    res \<leftarrow> ll_insert_value res v 3;
    res \<leftarrow> ll_insert_value res r 4;
    Mreturn res
  }"
  by (auto simp: init_rbt_node_def rbt_node_insert_value)


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
  by (auto simp: rbt_node_extract_value)


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
  by (auto simp: rbt_node_extract_value)


lemmas [llvm_inline] = rbt_node.color_def rbt_node.left_def rbt_node.key_def 
  rbt_node.val_def rbt_node.right_def


fun color_assn' :: "color \<Rightarrow> 8 word \<Rightarrow> ll_assn" where
  "color_assn' color.R rep = \<up>(rep=0)"
| "color_assn' color.B rep = \<up>(rep=1)"


definition "color_assn \<equiv> mk_assn color_assn'"


lemma [simp]: "\<upharpoonleft>color_assn color.R rep = \<up>(rep=0)"
  unfolding color_assn_def by simp


lemma [simp]: "\<upharpoonleft>color_assn color.B rep = \<up>(rep=1)"
  unfolding color_assn_def by simp


lemma color_assn_pure [is_pure_rule]: "is_pure color_assn"
  unfolding is_pure_def
proof(standard+)
  fix col coli
  show "sep_is_pure_assn (\<upharpoonleft>color_assn col coli)"
    by (cases col; auto)
qed

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


datatype ('key, 'key_impl, 'value) iterator_decl = 
  ITERATOR_DECL 
  (ptr: "('key_impl, 'value) rbt_node ptr")
  (key: 'key)


fun rbt_assn'' :: "
  ('k, 'v) rbt \<times>
  ('k, 'ki, 'v) iterator_decl set \<Rightarrow>
  ('ki::llvm_rep, 'v::llvm_rep) rbti \<Rightarrow>
  ll_assn
" where
  "rbt_assn'' (rbt.Empty, its) p = \<up>(p=null \<and> its = {})"
| "rbt_assn'' ((rbt.Branch col lhs k v rhs), its) p = (
    EXS coli lhsi ki vi rhsi. 
      \<upharpoonleft>ll_bpto (RBT_NODE coli lhsi ki vi rhsi) p **
      \<upharpoonleft>color_assn col coli **
      rbt_assn'' (lhs, its) lhsi **
      \<upharpoonleft>key_assn k ki **
      \<up>(vi=v) **  
      rbt_assn'' (rhs, its) rhsi **
      \<up>(\<forall> itdecl\<in> its. iterator_decl.key itdecl = k \<longrightarrow> iterator_decl.ptr itdecl = p)
  )"

definition rbt_assn' where "rbt_assn' tree its treei \<equiv> rbt_assn'' (tree, its) treei" 

definition "rbt_assn''' \<equiv> mk_assn rbt_assn''"

abbreviation "rbt_assn tree its treei \<equiv> \<upharpoonleft>rbt_assn''' (tree, its) treei"

lemmas rbt_assn_def = rbt_assn'''_def


lemma[simp]: "rbt_assn t its null = \<up>(t=rbt.Empty \<and> its = {})"
  unfolding rbt_assn_def
  by (cases t; auto)


lemma[simp]: "rbt_assn rbt.Empty its p = \<up>(p=null \<and> its = {})"
  unfolding rbt_assn_def by simp


lemma rbt_assn_branch_def: "rbt_assn (Branch col lhs k v rhs) its p = (
  EXS coli lhsi ki vi rhsi. 
    \<upharpoonleft>ll_bpto (RBT_NODE coli lhsi ki vi rhsi) p **
    \<upharpoonleft>color_assn col coli **
    rbt_assn lhs its lhsi **
    \<upharpoonleft>key_assn k ki **
    \<up>(vi=v) **  
    rbt_assn rhs its rhsi **
    \<up>(\<forall> itdecl\<in> its. iterator_decl.key itdecl = k \<longrightarrow> iterator_decl.ptr itdecl = p)
  )"
  unfolding rbt_assn_def
  by simp

lemma impl_pure: "(X ** \<up>Y) s \<Longrightarrow> Y"
  by (metis pred_lift_extract_simps(2) sep_conj_commuteI)

lemma "(P x ** \<up>(x = y)) s \<Longrightarrow> P y s"
proof -
  assume assm: "(P x ** \<up>(x = y)) s"

  hence "pure_part (\<up>(x = y))"
    by (simp add: pred_lift_extract_simps(1) sep_conj_def)

  hence "x = y" by auto

  with assm have "(P y ** \<up>(x = y)) s"
    by blast

  thus "P y s"
    by (simp add: \<open>x = y\<close> pure_true_conv)
qed

term RBT_Impl.keys

lemma "((X ** Y) ** Z) = (X ** (Y ** Z))"
  by simp

lemma X: "\<lbrakk>i \<in> its; key i \<in> set (RBT_Impl.keys tree)\<rbrakk> \<Longrightarrow>
  rbt_assn tree its treei s \<Longrightarrow>
  \<exists>X. (EXS coli lhsi ki vi rhsi.
    \<upharpoonleft>ll_bpto (RBT_NODE coli lhsi ki vi rhsi) (ptr i) ** X) s"
proof(induction tree arbitrary: treei s)
  case Empty
  then show ?case by simp
next
  case (Branch col lhs k v rhs)

  from Branch(4) have "key i = k \<or>
        key i \<in> set (RBT_Impl.keys lhs) \<or>
        key i \<in> set (RBT_Impl.keys rhs)"
    unfolding keys_def by auto

  from Branch(5) have *:
      "\<forall>itdecl\<in>its. iterator_decl.key itdecl = k \<longrightarrow> ptr itdecl = treei"
      unfolding rbt_assn_branch_def
    proof -
      assume "\<exists>x xa xb xc xd.
     (\<upharpoonleft>ll_bpto (RBT_NODE x xa xb xc xd) treei \<and>*
      \<upharpoonleft>color_assn col x \<and>*
      rbt_assn lhs its xa \<and>*
      \<upharpoonleft>key_assn k xb \<and>*
      \<up>(xc = v) \<and>*
      rbt_assn rhs its xd \<and>*
      \<up>(\<forall>itdecl\<in>its. iterator_decl.key itdecl = k \<longrightarrow> ptr itdecl = treei))
      s"


      then obtain x xa xb xc xd
      where "
       (\<upharpoonleft>ll_bpto (RBT_NODE x xa xb xc xd) treei \<and>*
        \<upharpoonleft>color_assn col x \<and>*
        rbt_assn lhs its xa \<and>*
        \<upharpoonleft>key_assn k xb \<and>*
        \<up>(xc = v) \<and>*
        rbt_assn rhs its xd \<and>*
        \<up>(\<forall>itdecl\<in>its. iterator_decl.key itdecl = k \<longrightarrow> ptr itdecl = treei))
        s" by blast
        
      with impl_pure[of "\<upharpoonleft>ll_bpto (RBT_NODE x xa xb xc xd) treei \<and>*
        \<upharpoonleft>color_assn col x \<and>*
        rbt_assn lhs its xa \<and>*
        \<upharpoonleft>key_assn k xb \<and>*
        \<up>(xc = v) \<and>*
        rbt_assn rhs its xd"]
      show "
        \<forall>itdecl\<in>its. iterator_decl.key itdecl = k \<longrightarrow> ptr itdecl = treei"
        by auto
    qed

  moreover from Branch(3,5) * have "key i = k \<Longrightarrow> ?case"
    unfolding rbt_assn_branch_def
    by blast

  moreover have "key i \<in> set (RBT_Impl.keys lhs) \<Longrightarrow> ?case"
  proof -

    assume assm: "key i \<in> set (RBT_Impl.keys lhs)"

    from Branch(5) obtain 
      treei' s' s'' where "s = s' + s'' \<and> rbt_assn lhs its treei' s'"
      unfolding rbt_assn_branch_def
      by (smt (z3) sep.mult.left_commute sep_conjD)

    moreover obtain X where "X s''" by simp

    with Branch(3) Branch(1)[of treei' s'] assm show ?case
      try0      

      sorry
      
      
    

  qed


 moreover from Branch have "key i \<in> set (RBT_Impl.keys rhs) \<Longrightarrow> ?case"
    unfolding rbt_assn_branch_def
    sorry


  ultimately show ?case
    by blast
qed



definition empty :: "('ki, 'v) rbti llM"
  where "empty \<equiv> Mreturn null"


lemma empty_correct:  
  "llvm_htriple
   \<box>
   empty
   (\<lambda> r. rbt_assn rbt.Empty {} r)"
  unfolding empty_def
  by vcg
end



end