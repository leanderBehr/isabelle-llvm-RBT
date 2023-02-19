theory Bench_Export
  imports
    Free
    Map_Interface
    Export_Wrappers
    Fail_Setup
begin      


interpretation bench_rbt: rbt_map
  ll_icmp_ult       (*less impl*)
  unat.assn         (*key assn*)
  "\<lambda>x. Mreturn ()"  (*key delete*)
  sint.assn         (*value assn*)
  "\<lambda>x. Mreturn ()"  (*value delete*)
  "TYPE(nat)"       (*abs key type*)
  "TYPE(64 word)"   (*key type*)
  "TYPE(int)"       (*abs value type*)
  "TYPE(64 word)"   (*value type*)
  "\<lambda>x. Mreturn x"   (*value copy*)
  by (standard, vcg)


export_llvm
  bench_rbt.empty_wrap is rbt_empty
  "M_CONST bench_rbt.free_wrap" is rbt_free
  "M_CONST bench_rbt.lookup_wrap" is rbt_lookup
  "M_CONST bench_rbt.insert_wrap" is rbt_insert
  "M_CONST bench_rbt.insert_opt_wrap" is rbt_insert_opt
  "M_CONST bench_rbt.delete_wrap" is rbt_delete
  "M_CONST bench_rbt.delete_opt_wrap" is rbt_delete_opt
  defines \<open>
    typedef struct {
       uint8_t color;
       rbt_node* lhs;
       uint64_t key;
       int64_t value;
       rbt_node* rhs;
    } rbt_node;
    
    typedef struct {
      int64_t value;
      uint8_t flag;
    } option_i;
  \<close>
  rewrites 
    \<open>(64 word, 64 word) rbt_node\<close> = rbt_node
    \<open>(64 word) option_i\<close> = option_i
  file "../exports/rbt.ll"


end