theory Arl_Ext
  imports
    "../Setup"
    "../Separation_Logic_Solver/Methods"
    "../Bool_Assn_Setup"

    "Isabelle_LLVM.LLVM_DS_All"
begin


hide_const Proto_EOArray.list_assn


definition elem_wise_assn_ex ::
  "('a \<Rightarrow> 'b \<Rightarrow> ll_assn) \<Rightarrow> 'a list \<Rightarrow> 'b list \<Rightarrow> nat set \<Rightarrow> ll_assn" where
  "elem_wise_assn_ex a xs ys ex = (\<Union>* i\<in>{0..<length xs} - ex. a (xs ! i) (ys ! i))"


abbreviation "elem_wise_assn a xs ys \<equiv> elem_wise_assn_ex a xs ys {}"


definition arl_mems_assn_ex ::
  "('a, 'b) dr_assn \<Rightarrow> 'a list \<Rightarrow> 'b list \<Rightarrow> ('b::llvm_rep, 'l::len2) array_list \<Rightarrow> nat set \<Rightarrow> ll_assn" where 
  "arl_mems_assn_ex A xs xsi arl ex \<equiv> \<upharpoonleft>arl_assn xsi arl ** \<upharpoonleft>(list_assn A (idxe_map xsi |` ex)) xs xsi"


abbreviation "arl_mems_assn' A xs arl \<equiv> (EXS xsi. arl_mems_assn_ex A xs xsi arl {})"


lemma 
  frame_assumption_rule_dyn :
  "\<lbrakk>P = Q; PS -- Pr \<tturnstile> QS -- Qr\<rbrakk> \<Longrightarrow> P ** PS -- Pr \<tturnstile> Q ** QS -- Qr"
  "\<lbrakk>P = Q; \<box> -- Pr \<tturnstile> QS -- Qr\<rbrakk> \<Longrightarrow> P -- Pr \<tturnstile> Q ** QS -- Qr"
  "\<lbrakk>P = Q; \<box> -- Pr \<tturnstile> \<box> -- Qr\<rbrakk> \<Longrightarrow> P -- Pr \<tturnstile> Q -- Qr"
  apply (simp_all add: frame_assumption_rule(2) sep_conj_commute)
  using frame_assumption_rule(2) apply fastforce+
  done


lemma entails_refl_dyn:
  "\<lbrakk>P = Q; PS \<turnstile> QS \<rbrakk> \<Longrightarrow> P ** PS \<turnstile> Q ** QS"
  "\<lbrakk>P = Q; \<box> \<turnstile> QS\<rbrakk> \<Longrightarrow> P \<turnstile> Q ** QS"
  "\<lbrakk>P = Q; \<box> \<turnstile> \<box>\<rbrakk> \<Longrightarrow> P \<turnstile> Q"
    apply (auto intro: conj_entails_mono)[1]
   apply (simp, isep_assumption, simp)
  apply simp
  done


lemma arl_mems_assn_def':
  "arl_mems_assn' A xs xsi = (EXS l. \<upharpoonleft>arl_assn l xsi ** \<upharpoonleft>(list_assn A (Map.empty)) xs l)"
  unfolding arl_mems_assn_ex_def
  by simp


lemma is_pure_pureI:
  "is_pure A \<Longrightarrow> pure_part (\<upharpoonleft>A x y) \<Longrightarrow> \<box> \<turnstile> \<upharpoonleft>A x y"
  by (simp add: extract_pure_assn pure_true_conv)


lemma pure_pure_asm_prefixI:
  "\<flat>\<^sub>passn x y \<Longrightarrow> \<box> \<turnstile> \<upharpoonleft>assn x y"
  by (metis (full_types) dr_assn_pure_asm_prefix_def entails_refl extract_pure_assn pure_true_conv)


lemma snat_assn_le_iso [simp]:
  "\<lbrakk>\<flat>\<^sub>psnat.assn x xi; \<flat>\<^sub>psnat.assn y yi\<rbrakk> \<Longrightarrow> xi < yi \<longleftrightarrow> x < y"
  unfolding snat.assn_def  
  by (auto simp add: snat_eq_unat_aux2 unat_mono word_less_nat_alt)


lemma 
  assumes "i \<notin> ex" and "i < length xs"
  shows
    "elem_wise_assn_ex a xs ys ex \<turnstile> elem_wise_assn_ex a xs ys (ex \<union> {i}) ** a (xs ! i) (ys ! i)"
  unfolding elem_wise_assn_ex_def
  using assms
  by (simp add: list_assn_extract_aux sep.mult_commute)



lemmas la_ired_extract[isep_red] = la_red_extract[simplified PRECOND_def SOLVE_AUTO_def]

lemma la_ired_join[isep_red]:
  "R i = None \<and> i<length xs \<and> x=xs!i \<and> y=ys!i 
      \<Longrightarrow> is_sep_red \<box> \<box> (\<upharpoonleft>A x y ** \<upharpoonleft>(list_assn A (R(i\<mapsto>ys!i))) xs ys) (\<upharpoonleft>(list_assn A R) xs ys)"
  apply (rule is_sep_redI)
  subgoal premises prems
    apply (isep_drule drule: prems(2))
    apply (isep_drule drule: list_assn_join)
    using prems apply auto
    apply (simp add: fun_upd_idem)
    done
  done



lemma arl_mems_len_rule [vcg_rules]:
  "
  llvm_htriple
  (arl_mems_assn_ex A xs xsi arl ex)
  (arl_len arl)
  (\<lambda>len. \<upharpoonleft>snat.assn (length xs) len ** arl_mems_assn_ex A xs xsi arl ex)
"
  unfolding arl_mems_assn_ex_def
  apply vcg
  apply vcg_compat
  apply isep_extract_pure
  apply (isep_rule rule: pure_pure_asm_prefixI, (auto dest: list_assn_pure_partD)[1])
  apply sep
  done



lemma arl_mems_nth_rule [vcg_rules]:
"
  llvm_htriple
  (arl_mems_assn_ex A xs xsi arl ex ** \<upharpoonleft>snat.assn i ii ** \<up>(i < length xs) ** \<up>(i \<notin> ex))
  (arl_nth arl ii)
  (\<lambda>elem. arl_mems_assn_ex A xs xsi arl (ex \<union> {i}) ** \<upharpoonleft>A (xs ! i) elem ** \<up>(elem = xsi ! i))
"
  unfolding arl_mems_assn_ex_def
  apply vcg
  apply vcg_compat
  apply (sep | find_sep)+
    apply ((auto dest!: list_assn_pure_partD))
  unfolding idxe_map_def
  by (simp add: restrict_map_insert)


lemma no_ex_arl_mems_nth_rule [vcg_rules]:
"
  llvm_htriple
  (arl_mems_assn_ex A xs xsi arl {} ** \<upharpoonleft>snat.assn i ii ** \<up>(i < length xs))
  (arl_nth arl ii)
  (\<lambda>elem. arl_mems_assn_ex A xs xsi arl {i} ** \<upharpoonleft>A (xs ! i) elem ** \<up>(elem = xsi ! i))
"
  by vcg

unbundle monad_syntax_M 


definition [llvm_inline]: "llc_for_range l h c s \<equiv> doM {
  (_,s) \<leftarrow> llc_while (\<lambda>(i,s). ll_cmp (i<h)) (\<lambda>(i,s). doM { 
    s\<leftarrow>c i s; 
    i \<leftarrow> ll_add i 1; 
    Mreturn (i,s)}
  ) (l,s);
  Mreturn s
}"


lemma llc_for_range_rule:
  assumes [vcg_rules]:
    "\<And>i ii si.
     llvm_htriple 
      (\<upharpoonleft>snat.assn i ii ** \<up>\<^sub>d(lo\<le>i \<and> i<hi) ** I i si) 
      (c ii si) 
      (\<lambda>si. I (i+1) si)"
  shows 
    "llvm_htriple
      (\<upharpoonleft>snat.assn lo loi ** \<upharpoonleft>snat.assn hi hii ** \<up>(lo\<le>hi) ** I lo si)
      (llc_for_range loi hii c si)
      (\<lambda>si. I hi si)"
  unfolding llc_for_range_def
  apply (rewrite at 1 to "signed_nat 1" signed_nat_def[symmetric])
  apply (rewrite annotate_llc_while[where 
    I="\<lambda>(ii,si) t. EXS i. \<upharpoonleft>snat.assn i ii ** \<up>(lo\<le>i \<and> i\<le>hi) ** \<up>\<^sub>!(t=hi-i) ** I i si" 
    and R="measure id"])
  apply vcg_monadify
  apply vcg'
  done


definition [llvm_code]:
  "arl_mems_free mem_free arl =
  do {
    len \<leftarrow> arl_len arl;
    llc_for_range 0 len 
    (\<lambda>i x.
      do {
        mem \<leftarrow> arl_nth arl i;
        mem_free mem;
        return 0
      }
    )
    (0::1 word);
    arl_free arl
  }"


definition "loop_inv A xs xsi arl i si \<equiv> arl_mems_assn_ex A xs xsi arl {0..<i}"


lemma empty_arl_mems_assn_ex_sepD:
  "arl_mems_assn_ex A xs xsi arl {0..<length xs} \<turnstile> \<upharpoonleft>arl_assn xsi arl"
  unfolding arl_mems_assn_ex_def
  apply isep_assumption
  apply isep_extract_pure
  apply (isep_drule drule: list_assn_free_none)
  apply (auto dest: list_assn_pure_partD)
  done


(*
  uint
  unat
  sint
  snat
*)


(*uint \<longrightarrow> unat*)
lemma "uint c1 = a1 \<Longrightarrow> unat c1 = nat a1" by auto

(*uint \<longrightarrow> sint*)
lemma uint_sint_pos: 
  "\<lbrakk>uint c1 = a1; a1 < 2^(word_len c1 - 1)\<rbrakk> \<Longrightarrow> sint c1 = a1"
  by (simp add: sint_eq_uint_2pl uint_power_lower word_less_def)

lemma uint_sint_neg:
  "\<lbrakk>uint c1 = a1; a1 \<ge> 2^(word_len c1 - 1)\<rbrakk> \<Longrightarrow> sint c1 = a1 - 2^(word_len c1)"
  using word_sint_msb_eq word_size msb_uint_big by (metis (full_types))

(*uint \<rightarrow> snat*)
lemma uint_snat_pos:
  "\<lbrakk>uint c1 = a1; a1 < 2^(word_len c1 - 1)\<rbrakk> \<Longrightarrow> snat c1 = nat a1"
  by (simp add: snat_eq_unat_aux1 unat_def)

lemma uint_snat_neg:
  "\<lbrakk>uint c1 = a1; a1 \<ge> 2^(word_len c1 - 1)\<rbrakk> \<Longrightarrow> snat c1 = 0"
  unfolding snat_def
  apply (auto simp add: uint_sint_neg)
  using less_le_not_le by blast




(*unat \<longrightarrow> uint*)
lemma "unat c1 = a1 \<Longrightarrow> uint c1 = int a1" by auto

(*unat \<longrightarrow> snat*)
lemma "\<lbrakk>unat c1 = a1; a1 < 2^(word_len c1 - 1)\<rbrakk> \<Longrightarrow> snat c1 = a1" using snat_eq_unat by blast 
lemma "\<lbrakk>unat c1 = a1; a1 \<ge> 2^(word_len c1 - 1)\<rbrakk> \<Longrightarrow> snat c1 = 0"
proof -
  assume "unat c1 = a1" "a1 \<ge> 2^(word_len c1 - 1)"  

  hence "msb c1" using msb_unat_big by blast
  hence "sint c1 < 0" using word_msb_sint by blast

  thus "snat c1 = 0" by (simp add: snat_def)
qed


(*unat \<longrightarrow> sint*)


lemma "uint c1 = a1 \<Longrightarrow> unat c1 = nat a1" by auto (*uint \<longrightarrow> unat*)



lemma "snat c1 = a1 \<Longrightarrow> \<not>msb c1 \<Longrightarrow> sint c1 = int a1"
  by (simp add: sint_eq_uint snat_eq_unat(2) snat_invar_def uint_nat)
lemma "\<lbrakk>snat c1 = a1; msb c1\<rbrakk> \<Longrightarrow> a1 = 0"
  unfolding snat_def using word_msb_sint by force



lemma arl_mems_free_rule:
  assumes
    mem_free_rule:
    "\<And>el eli.
      llvm_htriple
      (\<upharpoonleft>A el eli)
      (mem_free eli)
      (\<lambda>_. \<box>)
    "
  shows
    "
      llvm_htriple
      (arl_mems_assn_ex A xs xsi arl {})
      (arl_mems_free mem_free arl)
      (\<lambda>_. \<box>)
    "
  unfolding arl_mems_free_def
  supply llc_for_range_rule[where I="loop_inv A xs xsi arl", vcg_rules]
  apply vcg
  apply vcg_rl
  unfolding loop_inv_def apply vcg_solve (*pre cond*)
  subgoal for asf r sa i ii si (*step*)
    supply mem_free_rule[vcg_rules]
    apply vcg
    apply (simp only: atLeast0_lessThan_Suc)
    apply vcg_solve
    done
  subgoal (*after loop*)
    apply vcg_solve
    unfolding arl_mems_assn_ex_def
    apply vcg
    apply vcg_compat
    apply isep_extract_pure
    apply (isep_drule drule: list_assn_free_none)
     apply (auto dest: list_assn_pure_partD)
    done
  done

  
end