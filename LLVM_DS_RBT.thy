theory LLVM_DS_RBT
  imports
  "LLVM_DS_RBT/Load_Store_Example"
  "LLVM_DS_RBT/Example/Export"
  "LLVM_DS_RBT/Bench_Export"
begin
context rbt_impl
begin
find_theorems rbt_of HOL.eq name: reorient
end
end