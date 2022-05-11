theory Export
  imports
    Delete
    Insert
    Lookup
begin


definition key_delete :: "'a :: len word \<Rightarrow> unit llM" where [llvm_inline]:
"key_delete _ = Mreturn ()"


lemma word1_neq1_is_zero: "(x::1 word) \<noteq> 1 \<longleftrightarrow> x = 0"
  using word1_neqZ_is_one by blast


global_interpretation unat_rbt: rbt_impl
  ll_icmp_ult
  "unat.assn::(nat, 'a :: len word) dr_assn"
  key_delete 
  defines 
    unat_rbt_insert = unat_rbt.insert and
    unat_rbt_empty = unat_rbt.empty and
    unat_rbt_lookup = unat_rbt.lookup
proof(standard, goal_cases)
  case (1 lhs lhsi rhs rhsi)

  thus ?case
    apply vcg
    unfolding bool.assn_def 
    apply (auto simp add: word1_neqZ_is_one word1_neq1_is_zero)
     apply vcg+
    done
next
  case (2 k ki)

  show ?case
    unfolding key_delete_def
    by vcg
qed


lemmas [llvm_code] = unat_rbt.insert.simps unat_rbt.empty_def unat_rbt.lookup.simps


abbreviation unat_rbt_insert_64 :: 
  "(64 word, 8 word) rbt_node ptr \<Rightarrow> _"        
  where "unat_rbt_insert_64 \<equiv> unat_rbt_insert"


abbreviation unat_rbt_empty_64 :: "(64 word, 8 word) rbti llM"
  where "unat_rbt_empty_64 \<equiv> unat_rbt_empty"


abbreviation unat_rbt_lookup_64 :: "(64 word, 8 word) rbti \<Rightarrow> _"
  where "unat_rbt_lookup_64 \<equiv> unat_rbt_lookup"


export_llvm
  unat_rbt_empty_64 is "rbt_node* empty()"  
  unat_rbt_insert_64 is "rbt_node* insert(rbt_node*, uint64_t, uint8_t)"
  unat_rbt_lookup_64 is "option_i* lookup(rbt_node*, uint64_t)"
  defines \<open>
    typedef struct {
       uint8_t color;
       rbt_node* lhs;
       uint64_t key;
       uint8_t value;
       rbt_node* rhs;        
    } rbt_node;
    
    typedef struct {
      uint8_t value;
      uint8_t flag;
    } option_i;
  \<close>
  rewrites 
    \<open>(64 word, 8 word) rbt_node\<close> = rbt_node
    \<open>(8 word) option_i\<close> = option_i
  file "../exports/rbt.ll"


end