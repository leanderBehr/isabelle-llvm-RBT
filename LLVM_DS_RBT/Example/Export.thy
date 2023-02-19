theory Export
  imports 
    Example
    Arl_Export_Wrappers
    "../Export_Wrappers"
begin


type_synonym string = "(8 word, 64) array_list"


definition [llvm_code]: "make_id_map_rec_wrap strs_p res_out_p \<equiv> 
  do {
    strs \<leftarrow> ll_load strs_p;
    res \<leftarrow> make_id_map_rec strs;
    ll_store res res_out_p
  }
"


definition [llvm_code]: "make_id_map_loop_wrap strs_p res_out_p \<equiv> 
  do {
    strs \<leftarrow> ll_load strs_p;
    res \<leftarrow> make_id_map_loop strs;
    ll_store res res_out_p
  }
"


abbreviation "string_push_back \<equiv> arl_push_back_wrap :: string ptr \<Rightarrow> 8 word ptr \<Rightarrow> _"
abbreviation "string_list_push_back \<equiv> arl_push_back_wrap :: (string, 64) array_list ptr \<Rightarrow> string ptr \<Rightarrow> _"

abbreviation "string_new \<equiv> arl_new_wrap :: string ptr \<Rightarrow> unit llM"
abbreviation "string_list_new \<equiv> arl_new_wrap :: (string, 64) array_list ptr \<Rightarrow> unit llM"

definition [llvm_code]: "string_free \<equiv> arl_free_wrap (\<lambda>x. Mreturn ()) :: string ptr \<Rightarrow> _"
definition [llvm_code]: "string_list_free \<equiv> arl_free_wrap (arl_mems_free (\<lambda>x. Mreturn ())) :: (string, 64) array_list ptr \<Rightarrow> _"

abbreviation "string_nth \<equiv> arl_nth_wrap :: string ptr \<Rightarrow> _"
abbreviation "string_list_nth \<equiv> arl_nth_wrap :: (string, 64) array_list ptr \<Rightarrow> _"


abbreviation "map_new \<equiv> map.empty_wrap :: (string, 64 word) rbti ptr \<Rightarrow> unit llM"
abbreviation "map_free \<equiv> map.free_wrap :: (string, 64 word) rbti ptr \<Rightarrow> unit llM"
abbreviation "map_lookup \<equiv> map.lookup_wrap :: (string, 64 word) rbti ptr \<Rightarrow> _ \<Rightarrow> _\<Rightarrow> unit llM"
abbreviation "map_insert \<equiv> map.insert_wrap :: (string, 64 word) rbti ptr \<Rightarrow> _ \<Rightarrow> _\<Rightarrow> unit llM"
abbreviation "map_delete \<equiv> map.delete_wrap :: (string, 64 word) rbti ptr  \<Rightarrow> _\<Rightarrow> unit llM"

abbreviation "map_insert_opt \<equiv> map.insert_opt_wrap :: (string, 64 word) rbti ptr \<Rightarrow> _ \<Rightarrow> _\<Rightarrow> unit llM"
abbreviation "map_delete_opt \<equiv> map.delete_opt_wrap :: (string, 64 word) rbti ptr  \<Rightarrow> _\<Rightarrow> unit llM"

export_llvm
  make_id_map_rec_wrap is "void impl_make_id_map_rec(string_list*, result*)"
  make_id_map_loop_wrap is "void impl_make_id_map_loop(string_list*, result*)"

  string_new is impl_string_new
  string_list_new is impl_string_list_new
  
  string_free is impl_string_free
  string_list_free is impl_string_list_free
  
  string_push_back is "void impl_string_push_back(string*, char*)"
  string_list_push_back is impl_string_list_push_back
  
  string_nth is "void impl_string_nth(string*, int64_t, char*)"
  string_list_nth is "void impl_string_list_nth(string_list*, int64_t, string*)"
  
  map_new is impl_map_new
  "M_CONST map_free" is impl_map_free
  "M_CONST map_lookup" is impl_map_lookup
  "M_CONST map_insert" is impl_map_insert
  "M_CONST map_delete" is impl_map_delete

  "M_CONST map_insert_opt" is impl_map_insert_opt
  "M_CONST map_delete_opt" is impl_map_delete_opt

  defines 
    \<open>
      typedef struct {
        int64_t len;
        struct {
          int64_t cap;
          char* chars;
        };
      } string;

      typedef struct {
         uint8_t color;
         rbt* lhs;
         string key;
         int64_t value;
         rbt* rhs;        
      } rbt;

      typedef struct {
        int64_t len;
        struct {
          int64_t cap;
          string* strings;
        };
      } string_list;

      typedef struct {
        rbt* m1;
        string_list m2;
      } result;

      typedef struct {
        int64_t value;
        uint8_t flag;
      } uint64_option;
    \<close>
  rewrites
    \<open>64 word option_i\<close> = uint64_option
    \<open>string\<close> = string
    \<open>(string, 64 word) rbt_node\<close> = rbt
    \<open>(string, 64) array_list\<close> = string_list
    \<open>(string, 64 word) rbti \<times> (string, 64) array_list\<close> = result
  file "../../exports/example.ll"






end