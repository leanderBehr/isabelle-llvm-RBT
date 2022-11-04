theory Export_Wrappers
  imports Map_Interface
begin


context rbt_map
begin


interpretation monad_syntax_M_loc .


definition empty_wrap :: "_ ptr \<Rightarrow> unit llM" where [llvm_code]:
  "empty_wrap res_p =
    do {
      res \<leftarrow> empty;
      ll_store res res_p
    }
  "


definition free_wrap :: "_ ptr \<Rightarrow> unit llM" where [llvm_code]:
  "free_wrap rbt_p =
    do {
      rbt \<leftarrow> ll_load rbt_p;
      free rbt
    }
  "


definition lookup_wrap :: "_ ptr \<Rightarrow> _ ptr \<Rightarrow> _ ptr \<Rightarrow> unit llM" where [llvm_code]:
  "lookup_wrap rbt_p key_p res_p =
    do {
      rbt \<leftarrow> ll_load rbt_p;
      key \<leftarrow> ll_load key_p;
      res \<leftarrow> lookup value_copy rbt key;
      ll_store res res_p
    }
  "


definition insert_wrap :: "_ ptr \<Rightarrow> _ ptr \<Rightarrow> _ ptr \<Rightarrow> unit llM" where [llvm_code]:
  "insert_wrap rbt_p key_p value_p =
    do {
      rbt \<leftarrow> ll_load rbt_p;
      key \<leftarrow> ll_load key_p;
      value \<leftarrow> ll_load value_p;
      res \<leftarrow> insert key value rbt;
      ll_store res rbt_p
    }
  "


definition delete_wrap :: "_ ptr \<Rightarrow> _ ptr \<Rightarrow> unit llM" where [llvm_code]:
  "delete_wrap rbt_p key_p  =
    do {
      rbt \<leftarrow> ll_load rbt_p;
      key \<leftarrow> ll_load key_p;
      res \<leftarrow> delete key rbt;
      ll_store res rbt_p
    }
  "


end


end