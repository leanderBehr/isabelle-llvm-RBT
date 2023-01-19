theory Free_Ext
  imports 
    Extended_Assertion
    Free
begin

context rbt_impl
begin

lemma free_correct_ext [vcg_rules]:
  "
    llvm_htriple
    (rbt_assn_ext t {} ti)
    (free ti)
    (\<lambda>_. \<box>)
  "
proof(induction t arbitrary: ti)
  case ATEmpty
  then show ?case
    apply (subst free.simps)
    apply vcg
    done
next
  case (ATBranch c k v ci li ki vi ri al ar)

  note [vcg_rules] = ATBranch.IH
  
  then show ?case
    apply (subst free.simps)
    apply vcg
    done
qed

end

end