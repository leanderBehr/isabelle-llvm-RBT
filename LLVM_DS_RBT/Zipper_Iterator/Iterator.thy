theory Iterator
  imports 
    Zipper
    "../Separation_Logic_Solver/Methods"
begin


context rbt_impl
begin
interpretation llvm_prim_ctrl_setup .
interpretation llvm_prim_arith_setup .
interpretation llvm_prim_setup .


end


end