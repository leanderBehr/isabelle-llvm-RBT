theory LLVM_DS_RBT
  imports
  "LLVM_DS_RBT/Free"
  "LLVM_DS_RBT/Insert/Insert"
  "LLVM_DS_RBT/Insert/Naive_Insert"
  "LLVM_DS_RBT/Lookup/Lookup"
  "LLVM_DS_RBT/Export"
begin                                     


context rbt_impl
begin
interpretation llvm_prim_ctrl_setup .
interpretation llvm_prim_arith_setup .
interpretation llvm_prim_setup .


ML_val \<open>Basic_VCG.print_solvers @{context}\<close>


end