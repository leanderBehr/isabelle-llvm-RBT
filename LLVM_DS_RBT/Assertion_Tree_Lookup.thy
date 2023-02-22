theory Assertion_Tree_Lookup
  imports Extended_Assertion
begin

context rbt_impl
begin

fun p_node_of_key :: "_ \<Rightarrow> ('ki, 'vi) rbti \<Rightarrow> 'k  \<Rightarrow> _ option" where
  "p_node_of_key ATEmpty _  _ = None"
| "p_node_of_key br p kn =
  (
    if kn < (assn_tree.key br) then p_node_of_key (assn_tree.left br) (assn_tree.ll_left br) kn
    else if kn > (assn_tree.key br) then p_node_of_key (assn_tree.right br) (assn_tree.ll_right br) kn
    else Some (p, br)
  )
"

fun ptr_of_key :: "_ \<Rightarrow> ('ki, 'vi) rbti \<Rightarrow> 'k  \<Rightarrow> ('ki, 'vi) rbti option" where
  "ptr_of_key t ti k = map_option fst (p_node_of_key t ti k)"


fun at_ptr_graph where
  "at_ptr_graph ATEmpty _ = {}"
| "at_ptr_graph (ATBranch c k v ci li ki vi ri al ar) p = 
    {(k, p)} \<union> (at_ptr_graph al li) \<union> (at_ptr_graph ar ri)
  "

fun value_of_key where
  "value_of_key t ti k = map_option (assn_tree.ll_val \<circ> snd) (p_node_of_key t ti k)"


fun at_value_graph where
  "at_value_graph ATEmpty _ = {}"
| "at_value_graph (ATBranch c k v ci li ki vi ri al ar) p = 
    {(k, vi)} \<union> (at_value_graph al li) \<union> (at_value_graph ar ri)
  "

lemma ptr_of_key_less_none:
  "rbt_of t |\<guillemotleft> k \<Longrightarrow> ptr_of_key t p k = None"
  apply (induction t arbitrary: p)
  by auto

lemma value_of_key_less_none:
  "rbt_of t |\<guillemotleft> k \<Longrightarrow> value_of_key t p k = None"
  apply (induction t arbitrary: p)
  by auto

lemma p_node_of_key_less_none:
  "rbt_of t |\<guillemotleft> k \<Longrightarrow> p_node_of_key t p k = None"
  apply (induction t arbitrary: p)
  by auto


lemma ptr_of_key_greater_none:
  "k \<guillemotleft>| rbt_of t \<Longrightarrow> ptr_of_key t p k = None"
  apply (induction t arbitrary: p)
  by auto


lemma value_of_key_greater_none:
  "k \<guillemotleft>| rbt_of t \<Longrightarrow> value_of_key t p k = None"
  apply (induction t arbitrary: p)
  by auto


lemma p_node_of_key_greater_none:
  "k \<guillemotleft>| rbt_of t \<Longrightarrow> p_node_of_key t p k = None"
  apply (induction t arbitrary: p)
  by auto


declare value_of_key.simps[simp del]


lemma graph_p_node_of_key_eq:
  "rbt_sorted (rbt_of (ATBranch c k v ci li ki vi ri al ar)) \<Longrightarrow>
  Map.graph (p_node_of_key (ATBranch c k v ci li ki vi ri al ar) p) =
  {(k, (p, ATBranch c k v ci li ki vi ri al ar))} \<union> (Map.graph (p_node_of_key al li)) \<union> (Map.graph (p_node_of_key ar ri))"
  apply standard
  subgoal 
    unfolding Map.graph_def
    apply standard
    apply simp
    by (metis assn_tree.sel(2,5,8,9,10) linorder_neq_iff option.inject)
  subgoal premises prems
  proof
    fix x
    let ?br = "ATBranch c k v ci li ki vi ri al ar"
    assume asm: "x \<in> {(k, p, ?br)} \<union> Map.graph (p_node_of_key al li) \<union> Map.graph (p_node_of_key ar ri)"
    obtain xk xp xbr where ab: "x = (xk, xp, xbr)" using prod_cases3 .

    have "xk \<guillemotleft>| rbt_of ar" and "rbt_of al |\<guillemotleft> xk" if "xk = k" using prems that by simp+
    hence "x \<in> {(k, p, ?br)}" if "xk = k"
      using that p_node_of_key_greater_none p_node_of_key_less_none asm in_graphD ab
      by (metis Un_iff option.distinct(1))

    hence center: "p_node_of_key ?br p k = Some (xp, xbr)" if "xk = k" using that ab by simp


    from ab have lnot1: "x \<notin> {(k, p, ?br)}" if "xk < k" using that by blast

    have "xk \<guillemotleft>| rbt_of ar" if "xk < k" using that prems rbt_greater_trans by auto
    hence "p_node_of_key ar ri xk = None" if "xk < k" using that ptr_of_key_greater_none by auto
    with ab have lnot3: "x \<notin> Map.graph (p_node_of_key ar ri)" if "xk < k" using that in_graphD by fastforce

    from lnot1 lnot3 asm ab have left: "p_node_of_key al li xk = Some (xp, xbr)" if "xk < k" using that in_graphD by fast


    have right: "p_node_of_key ar ri xk = Some (xp, xbr)" if "xk > k" 
      using that in_graphD p_node_of_key_less_none prems rbt_less_trans asm ab
      by (metis (no_types, opaque_lifting) Un_iff dual_order.irrefl empty_iff insert_iff option.distinct(1) prod.sel(1) rbt_of.simps(2) rbt_sorted.simps(2))


    from center left right show "x \<in> Map.graph (p_node_of_key ?br p)"
      apply (cases xk k rule: linorder_cases)
      using ab apply (auto intro!: in_graphI)
      done
  qed
  done

lemma ptr_of_key_node_p_of_key_eq:
  "Map.graph (ptr_of_key t ti) = { (a, fst b) | a b. (a, b) \<in> Map.graph (p_node_of_key t ti) } "
  unfolding Map.graph_def
  by simp

lemma graph_ptr_of_key_eq:
  "rbt_sorted (rbt_of (ATBranch c k v ci li ki vi ri al ar)) \<Longrightarrow>
  Map.graph (ptr_of_key (ATBranch c k v ci li ki vi ri al ar) p) =
  {(k,p)} \<union> (Map.graph (ptr_of_key al li)) \<union> (Map.graph (ptr_of_key ar ri))"
  apply (simp add: ptr_of_key_node_p_of_key_eq)
  using graph_p_node_of_key_eq by fastforce


lemma fun_eq_graphI:
  "Map.graph f = Map.graph g \<Longrightarrow> f = g"
  unfolding Map.graph_def
  apply standard
  subgoal for x 
    apply (cases "f x"; cases "g x")
       apply force+
    done
  done



lemma at_ptr_graph_graph_eq:
  "rbt_sorted (rbt_of t) \<Longrightarrow> at_ptr_graph t p = Map.graph (ptr_of_key t p)"
  apply (induction t arbitrary: p)
  subgoal
    unfolding Map.graph_def
    apply simp
    done
  subgoal premises prems for x1 x2 x3 x4 x5 x6 x7 x8 t1 t2 p
  proof -
    from prems have "at_ptr_graph t1 p = Map.graph (ptr_of_key t1 p)" by auto
    moreover from prems have "at_ptr_graph t2 p = Map.graph (ptr_of_key t2 p)" by auto

    ultimately show ?thesis
      using prems graph_ptr_of_key_eq
      by fastforce
  qed
  done

subsection \<open>value of key\<close>

lemma value_of_key_node_p_of_key_eq:
  "Map.graph (value_of_key t ti) = { (a, ll_val (snd b)) | a b. (a, b) \<in> Map.graph (p_node_of_key t ti) } "
  unfolding Map.graph_def
  by (auto simp: value_of_key.simps)

lemma graph_value_of_key_eq:
  "rbt_sorted (rbt_of (ATBranch c k v ci li ki vi ri al ar)) \<Longrightarrow>
  Map.graph (value_of_key (ATBranch c k v ci li ki vi ri al ar) p) =
  {(k,vi)} \<union> (Map.graph (value_of_key al li)) \<union> (Map.graph (value_of_key ar ri))"
  supply value_of_key.simps[simp]
  apply (auto simp add: value_of_key_node_p_of_key_eq graph_p_node_of_key_eq) 
  by force


lemma at_value_graph_eq:
  "rbt_sorted (rbt_of t) \<Longrightarrow> at_value_graph t p = Map.graph (value_of_key t p)"
  supply value_of_key.simps[simp]
proof (induction t arbitrary: p)
  case ATEmpty
  then show ?case
    unfolding Map.graph_def
    by simp
next
  case (ATBranch x1 x2 x3 x4 x5 x6 x7 x8 t1 t2)
  from ATBranch have "at_value_graph t1 p = Map.graph (value_of_key t1 p)" by fastforce
  moreover from ATBranch have "at_value_graph t2 p = Map.graph (value_of_key t2 p)" by fastforce

  ultimately show ?case
    using ATBranch graph_value_of_key_eq
    by fastforce
qed

subsection \<open>ptr of key handling\<close>

subsubsection \<open>special case rules without handling updates\<close>

lemma ptr_of_key_eqI [intro!]:
  "\<lbrakk>rbt_sorted (rbt_of t); rbt_sorted (rbt_of t'); at_ptr_graph t p = at_ptr_graph t' p'\<rbrakk>
   \<Longrightarrow> ptr_of_key t p = ptr_of_key t' p'"
  using at_ptr_graph_graph_eq fun_eq_graphI by metis

lemma ptr_of_key_subsetI [intro!]:
  "\<lbrakk>rbt_sorted (rbt_of t); rbt_sorted (rbt_of t'); at_ptr_graph t p \<subseteq> at_ptr_graph t' p'\<rbrakk>
   \<Longrightarrow> ptr_of_key t p \<subseteq>\<^sub>m ptr_of_key t' p'"
  apply (simp add: at_ptr_graph_graph_eq) 
  unfolding map_le_def Map.graph_def
  by fastforce

declare ptr_of_key.simps[simp del]

lemma ptr_of_key_subsetD:
  "\<lbrakk>ptr_of_key t ti \<subseteq>\<^sub>m ptr_of_key t' ti'; rbt_sorted (rbt_of t); rbt_sorted (rbt_of t')\<rbrakk> 
    \<Longrightarrow> at_ptr_graph t ti \<subseteq> at_ptr_graph t' ti'"
  apply (simp add: at_ptr_graph_graph_eq)
  unfolding map_le_def Map.graph_def by force


subsubsection \<open>general rules\<close>

text \<open>
  1: @{term "m1 \<subseteq>\<^sub>m m2"} or m1 = m2 to Map.graph m1 ? Map.graph m2
  2: translate map updates to set operations
  3: @{term "Map.graph (ptr_of_key t k) = at_ptr_graph t k"}
\<close>

(*step 1*)
lemma key_to_ptr_map_subset_eq:
  "(m1:: 'k \<rightharpoonup> ('ki, 'vi) rbti) \<subseteq>\<^sub>m m2 \<longleftrightarrow> Map.graph m1 \<subseteq> Map.graph m2"
  unfolding Map.graph_def map_le_def by force

lemma key_to_ptr_map_eq_eq:
  "(m1:: 'k \<rightharpoonup> ('ki, 'vi) rbti) = m2 \<longleftrightarrow> Map.graph m1 = Map.graph m2"
  unfolding  map_le_def
  apply (rule iffI)
  subgoal by simp
  subgoal using fun_eq_graphI .
  done

(*step2, simp for update to Some missing*)
lemma graph_upd_none_eq:
  "Map.graph (m1(x:=None)) = Map.graph m1 - {(x, y) |y. True}"
  unfolding Map.graph_def 
  by (auto split!: if_splits)


lemma graph_upd_some_eq:
  "Map.graph (m1(x \<mapsto> y)) = Map.graph m1 - {(x, the (m1 x))} \<union> {(x, y)}"
  unfolding Map.graph_def
  by (auto split!: if_splits)


(*step3*)
lemmas map_grap_at_ptr_grap_eq = at_ptr_graph_graph_eq[symmetric]

lemmas ptr_of_key_simps = 
  (*step1*)
  key_to_ptr_map_subset_eq
  key_to_ptr_map_eq_eq
  (*step2*)
  graph_upd_none_eq
  (*step3*)
  map_grap_at_ptr_grap_eq

(*step 1*)
lemma value_to_ptr_map_subset_eq:
  "(m1:: 'k \<rightharpoonup> 'vi) \<subseteq>\<^sub>m m2 \<longleftrightarrow> Map.graph m1 \<subseteq> Map.graph m2"
  unfolding Map.graph_def map_le_def by force

lemma value_to_ptr_map_eq_eq:
  "(m1:: 'k \<rightharpoonup> 'vi) = m2 \<longleftrightarrow> Map.graph m1 = Map.graph m2"
  unfolding  map_le_def
  apply (rule iffI)
  subgoal by simp
  subgoal using fun_eq_graphI .
  done

lemmas value_of_key_simps = 
  (*step1*)
  value_to_ptr_map_subset_eq
  value_to_ptr_map_eq_eq
  (*step2*)
  graph_upd_none_eq
  (*step3*)
  at_value_graph_eq[symmetric]

subsection \<open>methods\<close>

method vok_solver = ((subst value_of_key_simps | subst (asm) value_of_key_simps | (auto)[])+)[]
method pok_solver = ((subst ptr_of_key_simps | subst (asm) ptr_of_key_simps | (auto)[])+)[]

method vok_filter = match conclusion in "value_of_key _ _ = _" \<Rightarrow> vok_solver 
                                      \<bar> _ \<Rightarrow> succeed

method catch_entails = match conclusion in "ENTAILS _ _" \<Rightarrow> vcg_compat

method vcg_vok = ((catch_entails | vcg_step)+, (sepEwith \<open>vok_filter,auto?\<close> | simp)+)+


end

end