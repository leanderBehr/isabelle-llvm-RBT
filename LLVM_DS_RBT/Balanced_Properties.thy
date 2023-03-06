theory Balanced_Properties
  imports Utilities
begin
 
(*number of nodes on the longest path, not quite the usual definition of height*)
fun rbt_node_height :: "_ \<Rightarrow> nat" where
  "rbt_node_height rbt.Empty = 0"
| "rbt_node_height (Branch _ l _ _ r) = 1 + max (rbt_node_height l) (rbt_node_height r)"


lemma
  A1: "\<lbrakk>is_rbt_node t; color_of t = color.R\<rbrakk> \<Longrightarrow> rbt_node_height t \<le> 2 * bheight t + 1" and
  A2: "\<lbrakk>is_rbt_node t; color_of t = color.B\<rbrakk> \<Longrightarrow> rbt_node_height t \<le> 2 * bheight t"
proof(induction t)
  case Empty
  {
    case 1
    then show ?case by simp
  next
    case 2
    then show ?case by simp
  }
next
  case (Branch x1 t1 x3 x4 t2)
  {
    case 1
    then show ?case using Branch by simp
  next
    case 2
    then show ?case using Branch by force
  }
qed

lemma B: "is_rbt_node (Branch c l k v r) \<Longrightarrow> bheight l = bheight r" by simp

abbreviation "rbt_size t \<equiv> length (RBT_Impl.entries t) "

lemma C: "is_rbt_node t \<Longrightarrow> 2 ^ bheight t \<le> rbt_size t + 1"
  by (induction t; auto)

lemma H1: "n \<ge> 2 \<Longrightarrow> ((2::nat) ^ n + 1) ^ 2 \<le> 2 ^ (2 * n + 1)"
proof - 
  assume n1: "n \<ge> 2"

  have n4: "(2::nat) ^ n \<ge> 4" using n1 
  proof (induction "n - 2" arbitrary: n)
    case 0
    then show ?case by simp
  next
    case (Suc x)
    from Suc(2-3) have nx: "n - 3 = x" by simp
    from Suc(2-3) have n3: "n \<ge> 3" by simp
    have "Suc(Suc(Suc 0)) = 3" by simp
    with nx n3 Suc(1)[of "n - 1"] have "(4::nat) \<le> 2 ^ (n - 1)" by auto
    then show ?case
      using order_trans by fastforce
  qed 
    
      
  have "(2::nat) ^ (n + 1) + 1 \<le> 4 * 2 ^ n" by simp
  with n4 have H: "(2::nat) ^ (n + 1) + 1 \<le> 2 ^ n * 2 ^ n"
    by (meson le_trans mult_le_mono1)


  have "((2::nat) ^ n + 1) ^ 2 = 2 ^ (2 * n) + 2 ^ (n + 1) + 1"
    by (simp add: power2_eq_square power_even_eq)

  from n1 H have "... \<le> 2 * 2 ^ n * 2 ^ n"
    by (simp add: power2_eq_square power_even_eq)

  
  thus "((2::nat) ^ n + 1) ^ 2 \<le> 2 ^ (2 * n + 1)" 
    by (simp add: power2_eq_square power_even_eq)
qed

lemma D:
  "is_rbt t \<Longrightarrow> 2 ^ rbt_node_height t \<le> (rbt_size t + 1) ^ 2" 
  using A2 C
proof -
  assume "is_rbt t"
  hence "color_of t = color.B" and rn: "is_rbt_node t" unfolding is_rbt_def by auto

  with A2 have "rbt_node_height t \<le> 2 * bheight t" by blast
  hence "(2::nat) ^ rbt_node_height t \<le> 2 ^ (2 * bheight t)" by simp
  hence X: "(2::nat) ^ rbt_node_height t \<le> (2 ^ bheight t) ^ 2" using power_even_eq by metis


  from C rn have Y: "2 ^ bheight t \<le> rbt_size t + 1" by blast
  hence Y: "(2 ^ bheight t) ^ 2 \<le> (rbt_size t + 1) ^ 2" by auto

  from X Y show ?thesis using order_trans by blast
qed

lemma rbt_node_height_cap_size:
  assumes
    "is_rbt t" and
    "rbt_size t \<le> 2^n" and
    "n \<ge> 2"
  shows 
    "rbt_node_height t \<le> 2*n+1"
proof - 
  have 1: "2 ^ rbt_node_height t \<le> (rbt_size t + 1) ^ 2" 
    using D assms
    by blast

  from assms have "rbt_size t + 1 \<le> 2 ^ n + 1" by simp
  with assms have "(rbt_size t + 1) ^ 2 \<le> (2 ^ n + 1) ^ 2"
    using power2_nat_le_eq_le by blast

  with 1 have "2 ^ rbt_node_height t \<le> ((2::nat) ^ n + 1) ^ 2" by linarith
  moreover from `n \<ge> 2` H1 have "((2::nat) ^ n + 1) ^ 2 \<le> 2 ^ (2 * n + 1)" by simp
  ultimately have "2 ^ rbt_node_height t \<le> (2::nat) ^ (2 * n + 1)" by simp

  thus "rbt_node_height t \<le> 2 * n + 1"
    by (metis One_nat_def lessI numerals(2) power_increasing_iff)
qed

lemma "is_rbt t \<Longrightarrow> rbt_size t \<le> 2^64 \<Longrightarrow> rbt_node_height t \<le> 129"
  using rbt_node_height_cap_size by fastforce

end