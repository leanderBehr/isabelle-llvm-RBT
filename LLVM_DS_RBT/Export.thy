theory Export
  imports
    Free
    "Insert/Insert"
    Lookup
    "Insert/Naive_Insert"
    Delete
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
    unat_rbt_naive_insert = unat_rbt.naive_insert and
    unat_rbt_balance = unat_rbt.balance and
    unat_rbt_insert = unat_rbt.insert and
    unat_rbt_empty = unat_rbt.empty and
    unat_rbt_lookup = unat_rbt.lookup and
    unat_rbt_free = unat_rbt.free and
    unat_rbt_balance_left = unat_rbt.balance_left and
    unat_rbt_balance_right = unat_rbt.balance_right
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


abbreviation unat_rbt_naive_insert_64 :: 
  "(64 word, 8 word) rbt_node ptr \<Rightarrow> _"        
  where "unat_rbt_naive_insert_64 \<equiv> unat_rbt_naive_insert"

abbreviation unat_rbt_insert_64 :: 
  "_ \<Rightarrow> _ \<Rightarrow> (64 word, 8 word) rbt_node ptr \<Rightarrow> _"        
  where "unat_rbt_insert_64 \<equiv> unat_rbt_insert"

abbreviation unat_rbt_balance_64 :: 
  "(64 word, 8 word) rbt_node ptr \<Rightarrow> _"        
  where "unat_rbt_balance_64 \<equiv> unat_rbt_balance"

abbreviation unat_rbt_empty_64 :: "(64 word, 8 word) rbti llM"
  where "unat_rbt_empty_64 \<equiv> unat_rbt_empty"

abbreviation unat_rbt_lookup_64 :: "(64 word, 8 word) rbti \<Rightarrow> _"
  where "unat_rbt_lookup_64 \<equiv> unat_rbt_lookup"

abbreviation unat_rbt_free_64 :: "(64 word, 8 word) rbti \<Rightarrow> _"
  where "unat_rbt_free_64 \<equiv> unat_rbt_free"

abbreviation unat_rbt_balance_left_64 :: "(64 word, 8 word) rbti \<Rightarrow> _"
  where "unat_rbt_balance_left_64 \<equiv> unat_rbt_balance_left"

abbreviation unat_rbt_balance_right_64 :: "(64 word, 8 word) rbti \<Rightarrow> _"
  where "unat_rbt_balance_right_64 \<equiv> unat_rbt_balance_right"

export_llvm
  unat_rbt_empty_64 is "rbt_node* rbt_empty()"  
  unat_rbt_naive_insert_64 is "rbt_node* rbt_naive_insert(rbt_node*, uint64_t, uint8_t)"
  unat_rbt_insert_64 is "rbt_node* rbt_insert(uint64_t, uint8_t, rbt_node*)"
  unat_rbt_balance_64 is "rbt_node* rbt_balance(rbt_node*, uint64_t, uint8_t, rbt_node*)"
  unat_rbt_lookup_64 is "option_i* rbt_lookup(rbt_node*, uint64_t)"
  unat_rbt_free_64 is "void rbt_free(rbt_node*)"
  unat_rbt_balance_left_64 is "rbt_node* rbt_balance_left(rbt_node*, uint64_t, uint8_t, rbt_node*)"
  unat_rbt_balance_right_64 is "rbt_node* rbt_balance_right(rbt_node*, uint64_t, uint8_t, rbt_node*)"
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