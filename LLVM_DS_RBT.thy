theory LLVM_DS_RBT
  imports "../isabelle_llvm/thys/ds/LLVM_DS_All"
    "HOL-Library.RBT_Impl"
begin                                     


datatype ('key :: llvm_rep, 'value :: llvm_rep) rbt_node =
  RBT_NODE
  (color: "1 word")
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
    VS_STRUCT [VS_INT 1, VS_PTR, struct_of TYPE('a), struct_of TYPE('b), VS_PTR]"

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


fun color_assn' :: "color \<Rightarrow> 1 word \<Rightarrow> ll_assn" where
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


locale linorder_impl =
  fixes lt_impl :: "('ai::llvm_rep) \<Rightarrow> 'ai \<Rightarrow> 1 word llM"
    and elem_assn :: "('a::linorder, 'ai) dr_assn"
  assumes lt_impl_rule [vcg_rules]: 
    "llvm_htriple
            (\<upharpoonleft>elem_assn lhs lhsi ** \<upharpoonleft>elem_assn rhs rhsi)
            (lt_impl lhsi rhsi)
            (\<lambda>r. \<up>(r = from_bool (lhs < rhs)) **
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


definition "rbt_assn \<equiv> mk_assn rbt_assn'"


lemma[simp]: "\<upharpoonleft>rbt_assn t null = \<up>(t=rbt.Empty)"
  unfolding rbt_assn_def
  by (cases t; auto)


lemma[simp]: "\<upharpoonleft>rbt_assn (rbt.Empty) p = \<up>(p=null)"
  unfolding rbt_assn_def by simp


lemma rbt_assn_branch_def [simp]: "\<upharpoonleft>rbt_assn (Branch col lhs k v rhs) p = (
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


definition rbt_empty :: "('ki, 'v) rbti llM"
  where "rbt_empty \<equiv> Mreturn null"


lemma rbt_empty_correct: 
  "llvm_htriple
   \<box>
   rbt_empty
   (\<lambda> r. \<upharpoonleft>rbt_assn rbt.Empty r)"
  unfolding rbt_empty_def
  by vcg


partial_function (M) contains :: "
  ('ki, 'v::llvm_rep) rbti \<Rightarrow> 'ki \<Rightarrow> 1 word llM
" where "
  contains rbtp k = do {
    if rbtp = null
    then return 0
    else do {
      node \<leftarrow> ll_load rbtp;
      go_left \<leftarrow> lt_impl k (rbt_node.key node);
      if go_left = 1
      then contains (rbt_node.left node) k
      else do {
        go_right \<leftarrow> lt_impl (rbt_node.key node) k;
        if go_right = 1
        then contains (rbt_node.right node) k
        else return 1
      }
    }
  }"


definition "rbt_contains t k \<equiv> rbt_lookup t k \<noteq> None" 


lemma [simp]: "\<upharpoonleft>bool.assn False 0 = \<box>" 
  unfolding bool.assn_def
  by (simp add: sep_algebra_simps)


lemma [simp]: "\<upharpoonleft>bool.assn True 1 = \<box>" 
  unfolding bool.assn_def
  by (simp add: sep_algebra_simps)


lemma helper: "\<not>a < b \<Longrightarrow> a \<noteq> b \<Longrightarrow> a > b" for a b :: "'a :: linorder"
  by auto


lemma contains_correct:
  "llvm_htriple
  (\<upharpoonleft>rbt_assn t ti ** \<upharpoonleft>key_assn k ki)
  (contains ti ki)
  (\<lambda>ri. \<upharpoonleft>bool.assn (rbt_contains t k) ri ** \<upharpoonleft>rbt_assn t ti ** \<upharpoonleft>key_assn k ki)"
proof(induction t arbitrary: ti)
  case Empty
  then show ?case
    unfolding rbt_contains_def
    apply (subst contains.simps)
    apply vcg_monadify
    apply vcg
    done
next
  case (Branch c lhs key val rhs)
  note [vcg_rules] = Branch.IH
  note [simp] = rbt_contains_def helper

  show ?case
    apply (subst contains.simps)
    apply vcg_monadify
    apply vcg
    done
qed


partial_function (M) delete :: "
  ('ki, 'val::llvm_rep) rbti \<Rightarrow> unit llM 
" where "
  delete tree_p = do {
    if tree_p = null
    then return ()
    else do {
      tree \<leftarrow> ll_load tree_p;
      key_delete (rbt_node.key tree);
      ll_free tree_p;
      delete (rbt_node.left tree);
      delete (rbt_node.right tree)
    }
  }
"


lemma delete_rule [vcg_rules]: "
  llvm_htriple
  (\<upharpoonleft>rbt_assn tree treei)
  (delete treei)
  (\<lambda>_. \<box>)
"
proof(induction tree arbitrary: treei)
  case Empty
  then show ?case
    apply (subst delete.simps)
    apply vcg_monadify
    apply vcg
    done
next
  case (Branch col lhs k v rhs)

  note [vcg_rules] = Branch.IH
  
  then show ?case
    apply (subst delete.simps)
    apply vcg_monadify
    apply vcg
    done
qed


partial_function (M) dummy_insert1 :: "
('ki, 'val::llvm_rep) rbti \<Rightarrow> 'ki \<Rightarrow> 'val \<Rightarrow> ('ki, 'val) rbti llM
" where " 
dummy_insert1 tree k v = do {
  new_node \<leftarrow> ll_balloc;
  ll_store (RBT_NODE (0::1 word) null k v null) new_node;
  delete tree;
  return new_node
}"


lemma dummy_insert1_correct:
  "llvm_htriple
  (\<upharpoonleft>rbt_assn tree treei ** \<upharpoonleft>key_assn k ki)
  (dummy_insert1 treei ki v)
  (\<lambda>ri. \<upharpoonleft>rbt_assn (rbt.Branch color.R rbt.Empty k v rbt.Empty) ri)"
proof(cases tree)
  case Empty

  then show ?thesis
    apply (subst dummy_insert1.simps)
    apply vcg_monadify
    apply vcg
    done
next
  case (Branch col lhs k v rhs)

  note [vcg_rules] = delete_rule (*Why?*)

  then show ?thesis
    apply (subst dummy_insert1.simps)
    apply vcg_monadify
    apply vcg
    done
qed


partial_function (M) dummy_insert2 :: "
('ki, 'val::llvm_rep) rbti \<Rightarrow> 'ki \<Rightarrow> 'val \<Rightarrow> ('ki, 'val) rbti llM
" where " 
dummy_insert2 tree k v = do {
  new_node \<leftarrow> ll_balloc;
  ll_store (RBT_NODE (0::1 word) null k v null) new_node;
  if tree = null
  then return new_node
  else do {
    delete tree;
    return new_node
  }
}"

(* how to do this proof? *)
lemma dummy_insert2_correct:
  "llvm_htriple
  (\<upharpoonleft>rbt_assn tree treei ** \<upharpoonleft>key_assn k ki)
  (dummy_insert2 treei ki v)
  (\<lambda>ri. \<upharpoonleft>rbt_assn (rbt.Branch color.R rbt.Empty k v rbt.Empty) ri)"
proof(cases tree)
  case Empty

  then show ?thesis
    apply (subst dummy_insert2.simps)
    apply vcg_monadify
    apply vcg
    done
next
  case (Branch col lhs k v rhs)

  then show ?thesis
    apply (subst dummy_insert2.simps)
    apply vcg_monadify
    apply vcg
    sorry
qed


fun rbt_insert ::
  "('key::linorder, 'val) rbt \<Rightarrow> 'key \<Rightarrow> 'val \<Rightarrow> ('key, 'val) rbt"
  where
  "rbt_insert rbt.Empty k v = Branch color.R rbt.Empty k v rbt.Empty"
| "rbt_insert (rbt.Branch col lhs k' v' rhs) k v = (
    if k < k'
    then rbt.Branch col (rbt_insert lhs k v) k' v' rhs
    else (
      if k > k'
      then rbt.Branch col lhs k' v' (rbt_insert rhs k v)
      else rbt.Branch col lhs k' v' rhs
    )
)"

lemma "rbt_insert rbt.Empty (1::nat) 1 = 
    Branch color.R rbt.Empty 1 1 rbt.Empty" by auto


partial_function (M) insert :: "
('ki, 'val::llvm_rep) rbti \<Rightarrow> 'ki \<Rightarrow> 'val \<Rightarrow> ('ki, 'val) rbti llM
" where " 
insert tree_p k v = do {
  if tree_p = null
  then do {
    new_node \<leftarrow> ll_balloc;
    ll_store (RBT_NODE 0 null k v null) new_node;
    return new_node
  }
  else do {
    tree \<leftarrow> ll_load tree_p;
    k_old \<leftarrow> return rbt_node.key tree;  

    k_lt \<leftarrow> lt_impl k k_old;
    if k_lt = 1 
    then do {
      new_lhs \<leftarrow> insert (rbt_node.left tree) k v;
       new_tree \<leftarrow> ll_insert_value tree new_lhs 1;
      ll_store new_tree tree_p;
      return tree_p
    }
    else do {
      k_gt \<leftarrow> lt_impl k_old k;
      if k_gt = 1
      then do {
        new_rhs \<leftarrow> insert (rbt_node.right tree) k v;
        new_tree \<leftarrow> ll_insert_value tree new_rhs 3;
        ll_store new_tree tree_p;
        return tree_p
      }
      else do {
         return tree_p 
      }    
    }
  }
}"

lemma left_insert:
  "llvm_htriple
  (\<upharpoonleft>rbt_assn (rbt.Branch col lhs k\<^sub>o v\<^sub>o rhs) treei **
  \<upharpoonleft>rbt_assn (local.rbt_insert lhs k\<^sub>n v\<^sub>n) lhs_ins_i)
  (ll_insert_value treei )

  "


lemma insert_correct:
  "llvm_htriple
  (\<upharpoonleft>rbt_assn tree treei ** \<upharpoonleft>key_assn k\<^sub>n ki)
  (insert treei ki v)
  (\<lambda>r. \<upharpoonleft>rbt_assn (rbt_insert tree k\<^sub>n v) r)"
proof(induction tree arbitrary: treei)
  case Empty
  then show ?case
    apply (subst insert.simps)
    by vcg
next
  case (Branch col lhs k\<^sub>t v rhs)

  note [vcg_rules] = Branch.IH

  show ?case
    apply (subst insert.simps)
    apply vcg_monadify
    apply vcg
    apply (auto simp del: rbt_assn_branch_def)



qed





end

definition "key_assn \<equiv> bool.assn"

definition lt_impl:: "1 word \<Rightarrow> 1 word \<Rightarrow> 1 word llM" where
  "lt_impl x y \<equiv> ll_icmp_ult x y"


lemma H1 [simp]: "
  llvm_htriple
  (\<upharpoonleft>bool.assn lhs lhsi ** \<upharpoonleft>bool.assn rhs rhsi)
  (lt_impl lhsi rhsi)
  (\<lambda>r. \<upharpoonleft>bool.assn (lhs < rhs) r)" 
  unfolding lt_impl_def
  apply vcg_monadify
  apply vcg
  sorry


interpretation rbt_impl
  lt_impl
  key_assn
proof(standard, goal_cases)
  case (1 lhs lhsi rhs rhsi)
  note [vcg_rules] = H1

  thus ?case 
    unfolding lt_impl_def
    unfolding key_assn_def
    apply vcg
    sorry

qed

lemma H: "\<upharpoonleft>(Abs_dr_assn x) = x" 
  unfolding dr_assn_prefix_def
  by simp


end

