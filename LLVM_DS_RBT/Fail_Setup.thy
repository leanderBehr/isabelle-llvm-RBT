theory Fail_Setup
  imports Isabelle_LLVM.LLVM_VCG_Main
begin

context
begin
unbundle monad_syntax_M

lemma T: 
  "do {x \<leftarrow> fail; m x} = fail"
  by (simp add: M_eq_iff pw_Mbind1 pw_basic(3) run_Mfail)

lemma [llvm_inline]: "fail = do {ll_store (null:: 8 word ptr) null; return init}" 
  unfolding ll_store_def llvm_store_def llvm_extract_addr_def ll_load_def llvm_load_def
  apply (simp add: T LLVM_Shallow.null_def to_val_ptr_def)
  done

end


end