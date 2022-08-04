theory Arl_Export_Wrappers
  imports Arl_Ext
begin


unbundle monad_syntax_M


definition arl_new_wrap  :: "_ ptr \<Rightarrow> unit llM" where [llvm_code]: 
  "arl_new_wrap res_p = 
  do {
    arl \<leftarrow> arl_new_raw;
    ll_store arl res_p
  }"


definition arl_free_wrap :: "_ \<Rightarrow> _ ptr \<Rightarrow> unit llM" where [llvm_code]: 
  "arl_free_wrap el_free arl_p = 
  do {
    arl \<leftarrow> ll_load arl_p;
    arl_mems_free el_free arl
  }"


definition arl_nth_wrap ::
  "('a::llvm_rep, 'l::len2) array_list ptr \<Rightarrow> 'l word \<Rightarrow> _ ptr \<Rightarrow> unit llM" where [llvm_code]: 
  "arl_nth_wrap arl_p i res_p = 
  do {
    arl \<leftarrow> ll_load arl_p;
    el \<leftarrow> arl_nth arl i;
    ll_store el res_p
  }"


definition arl_push_back_wrap :: "_ ptr \<Rightarrow> _ ptr  \<Rightarrow> unit llM" where [llvm_code]: 
  "arl_push_back_wrap arl_p el_p = 
  do {
    arl \<leftarrow> ll_load arl_p;
    el \<leftarrow> ll_load el_p;
    arl_n \<leftarrow> arl_push_back arl el;
    ll_store arl_n arl_p
  }"


end