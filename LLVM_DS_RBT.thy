theory LLVM_DS_RBT
  imports
  "LLVM_DS_RBT/Delete"
  "LLVM_DS_RBT/Balance"
  "LLVM_DS_RBT/Export"
  "LLVM_DS_RBT/Lookup"
begin                                     


context rbt_impl
begin
interpretation llvm_prim_ctrl_setup .
interpretation llvm_prim_arith_setup .
interpretation llvm_prim_setup .

ML_val \<open>Basic_VCG.print_solvers @{context}\<close>

end


end