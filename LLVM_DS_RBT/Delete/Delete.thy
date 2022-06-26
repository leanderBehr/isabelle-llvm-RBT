theory Delete
  imports 
    Balance_LR
    Combine
begin


context rbt_impl
begin
interpretation llvm_prim_ctrl_setup .
interpretation llvm_prim_arith_setup .
interpretation llvm_prim_setup .


fun rbt_del_ad where
  "rbt_del_ad x rbt.Empty = rbt.Empty"
| "rbt_del_ad x (rbt.Branch c a y s b) = 
(
  if x < y then
    if is_black_b a
    then rbt_balance_left (rbt_del_ad x a) y s b
    else rbt.Branch color.R (rbt_del_ad x a) y s b
  else if x > y then
    if is_black_b b
    then rbt_balance_right a y s (rbt_del_ad x b)
    else rbt.Branch color.R a y s (rbt_del_ad x b)
  else
    rbt_combine a b
)
"


(*looks easy now but really wasn't*)
lemma 
  rbt_del_ad_correct_left:
  "\<lbrakk>x < y\<rbrakk> \<Longrightarrow>
  rbt_del_ad x (rbt.Branch c a (y::'k) (s::'a) b) = rbt_del_from_left x a y s b" and

  rbt_del_ad_correct_right:
  "\<lbrakk>x > y\<rbrakk> \<Longrightarrow>
  rbt_del_ad x (rbt.Branch c a y s b) = rbt_del_from_right x a y s b" and

  rbt_del_ad_correct:
  "rbt_del_ad x (t:: ('k, 'a) rbt) = rbt_del x t"

proof (induct x a y s b and x a y s b and x t
    rule: rbt_del_from_left_rbt_del_from_right_rbt_del.induct)
  case (2 x c a y s b)
  then show ?case by (cases "x<y", auto)
qed auto


partial_function (M) del ::
  "'ki \<Rightarrow> ('ki, 'v::llvm_rep) rbti \<Rightarrow> (('ki, 'v::llvm_rep) rbti) llM" where
 "del x t_p = do {
  if t_p = null then return null
  else do {
    t \<leftarrow> ll_load t_p;
    case t of (RBT_NODE c a y s b) \<Rightarrow>
    do {
      le \<leftarrow> lt_impl x y;
      if le = 1 then
      do {
        cond \<leftarrow> is_black_b_i a;
        l_del \<leftarrow> del x a;
        if cond = 1
        then do { ll_free t_p; balance_left l_del y s b }
        else do { set_left_p l_del t_p; set_color_p 0 t_p; return t_p }
      }
      else
      do {
        ge \<leftarrow> lt_impl y x;
        if ge = 1
        then do {
          cond \<leftarrow> is_black_b_i b;
          r_del \<leftarrow> del x b;
          if cond = 1
          then do { ll_free t_p; balance_right a y s (r_del) }
          else do { set_right_p r_del t_p; set_color_p 0 t_p; return t_p }
        }
        else do {
          key_delete y;          
          ll_free t_p;
          combine a b
        }
      }
    }
  }
}"


lemma del_correct':
"
  llvm_htriple
  (\<upharpoonleft>key_assn k ki ** \<upharpoonleft>rbt_assn t ti)
  (del ki ti)
  (\<lambda>r. \<upharpoonleft>rbt_assn (rbt_del_ad k t) r ** \<upharpoonleft>key_assn k ki)
"
proof(induct k t arbitrary: ki ti rule: rbt_del_ad.induct)
  case (1 x)
  then show ?case
    apply (subst del.simps)
    apply vcg
    done
next
  case (2 x c a y s b)

  have IH1: 
    "x < y \<Longrightarrow> llvm_htriple
      (\<upharpoonleft>key_assn x ki \<and>* \<upharpoonleft>rbt_assn a ti)
      (del ki ti)
      (\<lambda>r. \<upharpoonleft>rbt_assn (rbt_del_ad x a) r \<and>* \<upharpoonleft>key_assn x ki)"
    for ki ti
    using 2(1-2) by fast

  have IH2:
    "y < x \<Longrightarrow> llvm_htriple
      (\<upharpoonleft>key_assn x ki \<and>* \<upharpoonleft>rbt_assn b ti)
      (del ki ti)
      (\<lambda>r. \<upharpoonleft>rbt_assn (rbt_del_ad x b) r \<and>* \<upharpoonleft>key_assn x ki)"
    for ki ti using 2(3-4) by fastforce

  note [vcg_rules] = IH1 IH2

  show ?case
    apply (subst del.simps)
    apply vcg
    done
qed


lemma del_correct:
"
  llvm_htriple
  (\<upharpoonleft>key_assn k ki ** \<upharpoonleft>rbt_assn t ti)
  (del ki ti)
  (\<lambda>r. \<upharpoonleft>rbt_assn (rbt_del k t) r ** \<upharpoonleft>key_assn k ki)
"
  using del_correct' rbt_del_ad_correct by metis


lemmas [llvm_code] = del.simps


definition "delete x t \<equiv> do { 
  del_res \<leftarrow> del x t;
  (if del_res = null then return () else set_color_p 1 del_res);
  return del_res 
  }"


lemma delete_correct [vcg_rules]:
"
  llvm_htriple
  (\<upharpoonleft>key_assn k ki ** \<upharpoonleft>rbt_assn t ti)
  (delete ki ti)
  (\<lambda>r. \<upharpoonleft>rbt_assn (rbt_delete k t) r ** \<upharpoonleft>key_assn k ki)
"
  unfolding delete_def rbt_delete_def paint_def
  supply del_correct[vcg_rules]
  apply vcg
  apply STATE_extract_pure
  apply (erule rbt_assn_non_null_unfold, simp)
  apply vcg
  done

lemmas [llvm_code] = delete_def


end 


end