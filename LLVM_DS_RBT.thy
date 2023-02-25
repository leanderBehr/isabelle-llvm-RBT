theory LLVM_DS_RBT
  imports
  "LLVM_DS_RBT/Load_Store_Example"
  "LLVM_DS_RBT/Example/Export"
  "LLVM_DS_RBT/Bench_Export"
begin
context rbt_impl
begin
interpretation rbt_impl_deps . 

thm insert_opt_correct_ext

lemma balance_correct_test [vcg_rules]:
  "llvm_htriple
  (
    rbt_assn l li **
    rbt_assn r ri **   
    \<upharpoonleft>key_assn k ki **
    \<upharpoonleft>value_assn v vi
  )
  (balance_left li ki vi ri)
  (\<lambda>res. rbt_assn (rbt_balance_left l k v r) res) 
  "
  unfolding balance_left_def bl_case_1_def
  apply vcg
  apply (auto elim!: matches_rbt.elims) []
  oops

end
end