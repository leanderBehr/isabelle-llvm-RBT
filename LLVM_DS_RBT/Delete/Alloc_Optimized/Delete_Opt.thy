theory Delete_Opt
  imports 
    "Combine_Opt"
    "../Delete"
begin


context rbt_impl
begin
interpretation rbt_impl_deps .


partial_function (M) del_opt ::
  "'ki \<Rightarrow> ('ki, 'vi) rbti \<Rightarrow> (('ki, 'vi) rbti) llM" where
  "del_opt x t_p =
  do {
    if t_p = null then return null
    else do {
      t \<leftarrow> ll_load t_p;
      case t of (RBT_NODE c a y s b) \<Rightarrow>
      do {
        if! lt_impl x y
        then! do {
          cond \<leftarrow> ll_is_black_br a;
          l_del \<leftarrow> del_opt x a;
          set_left_p l_del t_p;
          if cond = 1
          then do {balance_left_opt t_p}
          else do {set_color_p 0 t_p; return t_p}
        }
        else! if! lt_impl y x
        then! do {
          cond \<leftarrow> ll_is_black_br b;
          r_del \<leftarrow> del_opt x b;
          set_right_p r_del t_p;
          if cond = 1
          then do {balance_right_opt t_p }
          else do {set_color_p 0 t_p; return t_p}
        }
        else! do {
            key_delete y;
            value_delete s;
            ll_free t_p;
            combine a b
        }
      }
    }
  }"


lemmas [llvm_code] = del_opt.simps


lemma del_opt_correct':
"
  llvm_htriple
  (\<upharpoonleft>key_assn k ki ** rbt_assn t ti)
  (del_opt ki ti)
  (\<lambda>r. rbt_assn (rbt_del_ad k t) r ** \<upharpoonleft>key_assn k ki)
"
proof(induct k t arbitrary: ki ti rule: rbt_del_ad.induct)
  case (1 x)
  then show ?case
    apply (subst del_opt.simps)
    apply vcg
    done
next
  case (2 x c a y s b)

  have IH1: 
    "x < y \<Longrightarrow> llvm_htriple
      (\<upharpoonleft>key_assn x ki \<and>* rbt_assn a ti)
      (del_opt ki ti)
      (\<lambda>r. rbt_assn (rbt_del_ad x a) r \<and>* \<upharpoonleft>key_assn x ki)"
    for ki ti
    using 2(1-2) by fast

  have IH2:
    "y < x \<Longrightarrow> llvm_htriple
      (\<upharpoonleft>key_assn x ki \<and>* rbt_assn b ti)
      (del_opt ki ti)
      (\<lambda>r. rbt_assn (rbt_del_ad x b) r \<and>* \<upharpoonleft>key_assn x ki)"
    for ki ti using 2(3-4) by fastforce

  note [vcg_rules] = IH1 IH2

  show ?case
    apply (subst del_opt.simps)
    apply vcg
    done
qed


lemma del_opt_correct:
"
  llvm_htriple
  (\<upharpoonleft>key_assn k ki ** rbt_assn t ti)
  (del_opt ki ti)
  (\<lambda>r. rbt_assn (rbt_del k t) r ** \<upharpoonleft>key_assn k ki)
"
  using del_opt_correct' rbt_del_ad_correct by metis


definition "delete_opt x t \<equiv> do { 
  del_res \<leftarrow> del_opt x t;
  (if del_res = null then return () else set_color_p 1 del_res);
  return del_res 
  }"


lemmas [llvm_code] = delete_opt_def


lemma delete_opt_correct [vcg_rules]:
"
  llvm_htriple
  (\<upharpoonleft>key_assn k ki ** rbt_assn t ti)
  (delete_opt ki ti)
  (\<lambda>r. rbt_assn (rbt_delete k t) r ** \<upharpoonleft>key_assn k ki)
"
  unfolding delete_opt_def rbt_delete_def paint_def
  supply del_opt_correct[vcg_rules] load_rbt_non_null[vcg_rules]
  apply vcg
  done


end


end