(*  Title:       
    Author:      
    Maintainer:  
https://behemoth.cl.cam.ac.uk/search/
https://arxiv.org/pdf/2102.03003.pdf
https://math.stackexchange.com/
https://mathoverflow.net/
https://stackoverflow.com/
*)

section \<open> Examples \<close>

text \<open> We prove partial correctness specifications of some hybrid systems with our 
verification components.\<close>

theory Real_Arith_Problems
  imports "HOL-Analysis.Analysis"
  "HOL-Eisbach.Eisbach"

begin

method bin_unfold = (simp add: power2_diff power2_sum power_mult_distrib)

named_theorems monomial_rules "lista de propiedes para simplificar monomios"

declare  semiring_normalization_rules(29) [monomial_rules]
    and semiring_normalization_rules(28) [monomial_rules]
    and semiring_normalization_rules(27) [monomial_rules]
    and semiring_normalization_rules(18) [monomial_rules]
 
thm semiring_normalization_rules(27)

thm cross3_simps(11) semiring_normalization_rules(27,28,29)

named_theorems mono_rules "otra lista para simplificar monomios"

declare semiring_normalization_rules(29) [mono_rules]
    and semiring_normalization_rules(28) [mono_rules]

method mon_simp = (simp add: monomial_rules)+


subsection \<open> Basic \<close>

lemma abs_le_eq:
  shows "(r::real) > 0 \<Longrightarrow> (\<bar>x\<bar> < r) = (-r < x \<and> x < r)"
    and "(r::real) > 0 \<Longrightarrow> (\<bar>x\<bar> \<le> r) = (-r \<le> x \<and> x \<le> r)"
   apply linarith
  apply linarith
  done

lemma "(Collect ((\<le>) (0::real))) = {x:: real. x\<ge>0}"
  by simp

lemma is_interval_real_nonneg[simp]: "is_interval {x:: real. x\<ge>0}"
  using is_interval_1 by force 

lemma "((a::real)-b)^2 = a^2 - 2 * a * b + b^2"
  apply (subst power2_diff[of a b])
by bin_unfold

lemma norm_rotate_eq:
  fixes x :: "'a:: {banach,real_normed_field}"
  shows "(x * cos t - y * sin t)\<^sup>2 + (x * sin t + y * cos t)\<^sup>2 = x\<^sup>2 + y\<^sup>2" (is "?a^2+?b^2 =_")
    and "(x * cos t + y * sin t)\<^sup>2 + (y * cos t - x * sin t)\<^sup>2 = x\<^sup>2 + y\<^sup>2" (is "?e^2+?f^2 =_")
proof-
  have exp1: "?a^2 = x^2 * (cos t)^2 -2 * x * y * cos t * sin t + y^2 * (sin t)^2 " (is "_ = ?c")
    by bin_unfold
  have exp2: "?b^2 = x^2 * (sin t)^2 +2 * x * y * sin t * cos t + y^2 * (cos t)^2" (is "_=?d")
    by (simp add: power2_sum power_mult_distrib)
  have id1:  "(cos t)^2 + (sin t)^2 = 1"
    by simp
  have "?a\<^sup>2 + ?b\<^sup>2 = ?c+?d "
    using exp1 exp2
    by fastforce
  also have "... = x^2 * (cos t)^2 + y^2 * (sin t)^2 +x^2 * (sin t)^2  + y^2 * (cos t)^2"
    by auto
  also have "... = x^2 + y^2"
    by (smt (z3) \<open>(cos t)\<^sup>2 + (sin t)\<^sup>2 = 1\<close> add_diff_cancel_left'
        cancel_ab_semigroup_add_class.diff_right_commute diff_add_cancel
        mult.commute mult_numeral_1 numeral_One vector_space_over_itself.scale_left_diff_distrib)
  finally show  "?a\<^sup>2+?b\<^sup>2 = x\<^sup>2 + y\<^sup>2" 
    by simp
next
  have exp3: "?e^2 = x^2 * (cos t)^2 +2 * x * y * cos t * sin t + y^2 * (sin t)^2 " (is "_ = ?g")
    by (simp add: power2_sum power_mult_distrib)
  have exp4: "?f^2 =  y^2 * (cos t)^2 -2 * x * y * sin t * cos t + x^2 * (sin t)^2  "(is "_= ?h")
     by bin_unfold
have id1:  "(cos t)^2 + (sin t)^2 = 1"
    by simp
  have "?e\<^sup>2 + ?f\<^sup>2 = ?g+?h "
    using exp3 exp4
    by presburger
  also have "... = x^2 * (cos t)^2 + x^2 * (sin t)^2  + y^2 * (sin t)^2 + y^2 * (cos t)^2  "
    by fastforce
  also have "... = x^2 + y^2 "
    by (smt (z3) add_diff_cancel_left' diff_add_cancel id1 is_num_normalize(1)
 mult.commute mult_numeral_1 numeral_One vector_space_over_itself.scale_left_diff_distrib)
  finally show  "?e\<^sup>2 + ?f\<^sup>2 = x\<^sup>2 + y\<^sup>2"
    by (simp add: \<open>x\<^sup>2 * (cos t)\<^sup>2 + 2 * x * y * cos t * sin t + y\<^sup>2 * (sin t)\<^sup>2 
+ (y\<^sup>2 * (cos t)\<^sup>2 - 2 * x * y * sin t * cos t + x\<^sup>2 * (sin t)\<^sup>2) = x\<^sup>2 * (cos t)\<^sup>2
 + x\<^sup>2 * (sin t)\<^sup>2 + y\<^sup>2 * (sin t)\<^sup>2 + y\<^sup>2 * (cos t)\<^sup>2\<close> \<open>x\<^sup>2 * (cos t)\<^sup>2 + x\<^sup>2 * (sin t)\<^sup>2
 + y\<^sup>2 * (sin t)\<^sup>2 + y\<^sup>2 * (cos t)\<^sup>2 = x\<^sup>2 + y\<^sup>2\<close>) 
qed

lemma mult_abs_right_mono: "a < b \<Longrightarrow> a * \<bar>c\<bar> \<le> b * \<bar>c\<bar>" for c::real
  by (simp add: mult_right_mono)

lemma dyn_cons_qty_arith: "(36::real) * (x1\<^sup>2 * (x1 * x2 ^ 3)) - 
  (- (24 * (x1\<^sup>2 * x2) * x1 ^ 3 * (x2)\<^sup>2) - 12 * (x1\<^sup>2 * x2) * x1 * x2 ^ 4) - 
  36 * (x1\<^sup>2 * (x2 * x1)) * (x2)\<^sup>2 - 12 * (x1\<^sup>2 * (x1 * x2 ^ 5)) = 24 * (x1 ^ 5 * x2 ^ 3)" 
  (is "?t1 - (- ?t2 - ?t3) - ?t4 - ?t5 = ?t6")
proof- 
  have "?t1= ?t4"
    by (simp add: power2_eq_square power3_eq_cube)
  have "?t2 = ?t6"
    by (metis (no_types, hide_lams)
 mult.assoc mult.left_commute power2_eq_square power3_eq_cube power_add_numeral2
 semiring_norm(2) semiring_norm(7))
  have h1: "?t3 = ?t5"
    by (simp add: semiring_normalization_rules(27))
  have "?t1 - (- ?t2 - ?t3) - ?t4 - ?t5 = ?t2 + ?t3 - ?t5"
    by (simp add: \<open>36 * (x1\<^sup>2 * (x1 * x2 ^ 3)) = 36 * (x1\<^sup>2 * (x2 * x1)) * x2\<^sup>2\<close>)
  also have "... = ?t2 "
    using h1 by simp
  also have "... = ?t6 "
    by (simp add: \<open>24 * (x1\<^sup>2 * x2) * x1 ^ 3 * x2\<^sup>2 = 24 * (x1 ^ 5 * x2 ^ 3)\<close>)
  finally show "?t1 - (- ?t2 - ?t3) - ?t4 - ?t5 = ?t6" 
    by simp
qed

lemma local_lipschitz_first_order_linear:
  fixes c::"real \<Rightarrow> real"
  assumes "continuous_on T c"
  shows "local_lipschitz T UNIV (\<lambda>t x.  (c t) * x)"
proof(unfold local_lipschitz_def lipschitz_on_def, clarsimp simp: dist_norm)
  fix x t::real assume "t \<in> T"
  thus "\<exists>u>0. \<exists>L. \<forall>t\<in>cball t u \<inter> T. 0 \<le> L \<and> 
    (\<forall>xa\<in>cball x u. \<forall>y\<in>cball x u. \<bar>c t * xa - c t * y\<bar> \<le> L * \<bar>xa - y\<bar>)"
    sorry
qed


lemma darboux_ineq_arith:
  assumes "0 \<le> s\<^sub>1 + s\<^sub>2" and "0 \<le> (t::real)" and "t * s\<^sub>1 < 1"
  shows "0 \<le> s\<^sub>1 / (1 - t * s\<^sub>1) + (s\<^sub>2 - s\<^sub>1 * ln (1 - t * s\<^sub>1)) / (1 - t * s\<^sub>1)"

  oops

lemma picard_lindeloef_dyn_bif: "continuous_on T g \<Longrightarrow> t\<^sub>0 \<in> T \<Longrightarrow> is_interval T \<Longrightarrow>
  open T \<Longrightarrow> (t::real) \<in> T \<Longrightarrow> \<exists>u>0. (\<exists>ta. \<bar>t - ta\<bar> \<le> u \<and> ta \<in> T) \<longrightarrow> 
  (\<exists>L\<ge>0. \<forall>xa\<in>cball (x::real) u. \<forall>y\<in>cball x u. \<bar>xa\<^sup>2 - y\<^sup>2\<bar> \<le> L * \<bar>xa - y\<bar>)"
proof-
  fix x t::real
  show "\<exists>u>0. (\<exists>\<tau>. \<bar>t - \<tau>\<bar> \<le> u \<and> \<tau> \<in> T) \<longrightarrow> 
  (\<exists>L\<ge>0. \<forall>xa\<in>cball x u. \<forall>y\<in>cball x u. \<bar>xa\<^sup>2 - y\<^sup>2\<bar> \<le> L * \<bar>xa - y\<bar>)"
  proof (rule_tac x = 1 in  exI, clarsimp)
    fix w 
    assume "\<bar>t - w\<bar> \<le> 1" and "w \<in> T"
    show " \<exists>L\<ge>0. \<forall>z\<in>cball x 1. \<forall>y\<in>cball x 1. \<bar>z\<^sup>2 - y\<^sup>2\<bar> \<le> L * \<bar>z - y\<bar>"
      apply (rule_tac x = 22 in exI)
      thm allE ballE  allI ballI
      thm exE exI bexE bexI
      thm conjI conjE
      thm disjI1 disjI2 disjE
      thm iffI iffE
     (* apply (rule allE)*)
      sorry
    oops

lemma sumfrac: "((a:: real) + b) / c = a / c + b / c" "(a-b)/c= a/c - b/c"
   apply (clarsimp simp: add_divide_distrib)
  apply (clarsimp simp:  diff_divide_distrib)
  done

lemma frac: "(1:: real)/ a * 1 / b = 1 / (a * b) "
  by simp

lemma "((x::real)-y)^2  / (2 * B)   = x^2 / (2 * B)  -2 * x * y /(2 * B)  + y^2  / (2 * B)"
  by (simp add: power2_diff diff_divide_distrib add_divide_distrib)

lemma STTexample3a_arith:
  assumes "0 < (B::real)" "0 \<le> t" "0 \<le> x2" and key: "x1 + x2\<^sup>2 / (2 * B) \<le> S"
  shows "x2 * t - B * t\<^sup>2 / 2 + x1 + (x2 - B * t)\<^sup>2 / (2 * B) \<le> S" (is "?lhs \<le> S")
proof-
  have "(x2 - B * t)\<^sup>2 =  x2\<^sup>2 -2 * B * x2 * t + B^2 * t\<^sup>2 "
     by bin_unfold
  hence "(x2 - B * t)\<^sup>2 / (2 * B) =(x2\<^sup>2 -2 * B * x2 * t + B^2 * t\<^sup>2) / (2 * B) " (is "_ = ?f")
    by simp
   also have "... = x2^2 /(2 * B)- 2 * B * x2* t/(2 * B) + B^2* t^2 /(2 * B) "
    by (simp add: add_divide_distrib  diff_divide_distrib)
  also have "... =x2^2 /(2 * B) - x2 * t + B* t^2/ 2 " using assms
    by (simp add: power2_eq_square)
  finally have "(x2 - B * t)\<^sup>2 / (2 * B) = x2^2 /(2 * B) - x2 * t + B* t^2/ 2 ".
  hence "?lhs = x1 + x2\<^sup>2 / (2 * B) "
    by simp
  thus  "?lhs \<le> S"
    using assms(4) by simp
qed

lemma "(a:: real)*(b+c) = a* b + a* c"
  by (simp add: Groups.algebra_simps(18))

lemma STTexample5_arith:
  assumes "0 < A" "0 < B" "0 < \<epsilon>" "0 \<le> x2" "0 \<le> (t::real)" 
    and key: "x1 + x2\<^sup>2 / (2 * B) + (A * (A * \<epsilon>\<^sup>2 / 2 + \<epsilon> * x2) / B + (A * \<epsilon>\<^sup>2 / 2 + \<epsilon> * x2)) \<le> S" (is "?k3 \<le> S")
    and ghyp: "\<forall>\<tau>. 0 \<le> \<tau> \<and> \<tau> \<le> t \<longrightarrow> \<tau> \<le> \<epsilon>"
  shows "A * t\<^sup>2 / 2 + x2 * t + x1 + (A * t + x2)\<^sup>2 / (2 * B) \<le> S" (is "?k0 \<le> S")
proof-
  have "(A * t + x2)\<^sup>2 = A^2 * t^2 +2* A * t * x2  + x2^2 "
 by (simp add: power2_sum power_mult_distrib)
  hence "(A * t + x2)\<^sup>2 / (2 * B) = (A^2 * t^2 +2* A * t * x2  + x2^2) / (2 * B)"
    by simp
  also have "... = A^2 * t^2 /(2 * B) + 2 * A * t * x2 /(2 * B) + x2^2 /(2 * B) "
    by (simp add: add_divide_distrib)
  also have "... = A^2 * t^2 /(2 * B) + A * t * x2 / B + x2^2 /(2 * B) "
    by  clarsimp
  finally have coso1: "(A * t + x2)\<^sup>2 / (2 * B) = A^2 * t^2 /(2 * B) + A * t * x2 / B + x2^2 /(2 * B) ".
  have r1: "t \<le>  \<epsilon> "
    using ghyp assms(5) by force 
  have des1: "x2 * t \<le>  \<epsilon> * x2"
    by (simp add: \<open>t \<le> \<epsilon>\<close> assms(4) mult.commute mult_right_mono)
  have des2: "A * t\<^sup>2 / 2 \<le> A * \<epsilon>\<^sup>2 / 2 "
    by (simp add: \<open>t \<le> \<epsilon>\<close> assms(1) assms(5) power_mono)
  hence des3: "A^2 * t^2 /(2 * B) \<le> A^2 * \<epsilon>\<^sup>2 /(2 * B)  " using assms(2)
    apply clarsimp
    by (simp add: assms(1) frac_le mult_left_mono) 
  have des4: "A* t* x2 / B \<le> A * \<epsilon> * x2 / B " using r1 assms
    by (metis div_0 divide_right_mono le_divide_eq_1_neg less_eq_real_def 
mult_le_cancel_left_pos mult_le_cancel_right not_one_le_zero)
  have "?k0 = A * t\<^sup>2 / 2 + x2 * t + x1 + A^2 * t^2 /(2 * B) + A * t * x2 / B + x2^2 /(2 * B)" (is "_=?k1")
    by (simp add: coso1)
  have "?k3 = x1 + x2\<^sup>2 / (2 * B) + (A^2 * \<epsilon>\<^sup>2 / 2 +A *  \<epsilon> * x2) / B + (A * \<epsilon>\<^sup>2 / 2 + \<epsilon> * x2)" 
    using assms(2)
    by (clarsimp simp: Groups.algebra_simps(18) power2_eq_square)
  also have "... = x1 + x2\<^sup>2 / (2 * B) + A^2 * \<epsilon>\<^sup>2 / (2 * B) +A *  \<epsilon> * x2 / B + (A * \<epsilon>\<^sup>2 / 2 + \<epsilon> * x2)" (is "_=?k2")
    by (clarsimp simp: frac add_divide_distrib)
  oops
 

lemma STTexample6_arith:
  assumes "0 < A" "0 < B" "0 < \<epsilon>" "0 \<le> x2" "0 \<le> (t::real)" "- B \<le> k" "k \<le> A"
    and key: "x1 + x2\<^sup>2 / (2 * B) + (A * (A * \<epsilon>\<^sup>2 / 2 + \<epsilon> * x2) / B + (A * \<epsilon>\<^sup>2 / 2 + \<epsilon> * x2)) \<le> S" (is "?k3 \<le> S")
    and ghyp: "\<forall>\<tau>. 0 \<le> \<tau> \<and> \<tau> \<le> t \<longrightarrow> 0 \<le> k * \<tau> + x2 \<and> \<tau> \<le> \<epsilon>"
  shows "k * t\<^sup>2 / 2 + x2 * t + x1 + (k * t + x2)\<^sup>2 / (2 * B) \<le> S" (is "?k0 \<le> S")
  oops


  subsubsection \<open> STTT Tutorial: Example 7 \<close>

lemma consprod: assumes  "(0::real) < b" "s \<le> t" 
  shows " s / b \<le>  t / b"
  using assms(1) assms(2) divide_right_mono by fastforce

lemma consprod2: assumes  "(0::real) < b" "s \<le> t" 
  shows " b* s \<le> b * t"
  by (simp add: assms(1) assms(2))

lemma STTexample7_arith1:
  assumes "(0::real) < A" "0 < b" "0 < \<epsilon>" "0 \<le> v" "0 \<le> t" "k \<le> A"
    and "x + v\<^sup>2 / (2 * b) + (A * (A * \<epsilon>\<^sup>2 / 2 + \<epsilon> * v) / b + (A * \<epsilon>\<^sup>2 / 2 + \<epsilon> * v)) \<le> S" (is "?expr1 \<le> S")
    and guard: "\<forall>\<tau>. 0 \<le> \<tau> \<and> \<tau> \<le> t \<longrightarrow> 0 \<le> k * \<tau> + v \<and> \<tau> \<le> \<epsilon>"
  shows "k * t\<^sup>2 / 2 + v * t + x + (k * t + v)\<^sup>2 / (2 * b) \<le> S" (is "?lhs \<le> S")
proof-
  have "k * t\<^sup>2 / 2 + v * t + x + (k * t + v)\<^sup>2 / (2 * b) \<le> S"
  oops

lemma "(a:: real)*c+ a * b = a * (c + b)"
  by (simp add: ring_class.ring_distribs(1))

lemma "(v:: real) * t + k * t\<^sup>2 / 2 = (v + k * t / 2) * t"
  by (simp add: power2_eq_square ring_class.ring_distribs(2))

method divide_simplify = (clarsimp simp: add_divide_distrib)

lemma STTexample7_arith2:
  assumes "(0::real) < b" "0 \<le> v" "0 \<le> t" "k \<le> - b"
    and key: "x + v\<^sup>2 / (2 * b) \<le> S" 
    and guard: "\<forall>\<tau>. 0 \<le> \<tau> \<and> \<tau> \<le> t \<longrightarrow> 0 \<le> k * \<tau> + v \<and> \<tau> \<le> \<epsilon>"
  shows "k * t\<^sup>2 / 2 + v * t + x + (k * t + v)\<^sup>2 / (2 * b) \<le> S" (is "?lhs \<le> S")
proof-
  have des1: " 0 \<le> k * t / 2 + v" 
    using assms(6) assms(2) assms(3) by force
  have " k / b \<le> -1" using assms(1) assms(4) consprod
    by fastforce
  hence des2: "1 + k / b \<le> 0"
    by simp
  have "(k * t + v)\<^sup>2  = (k^2 * t^2 + 2 * k * t * v + v^2)"
    by bin_unfold
  have "(k * t + v)\<^sup>2/ (2 * b) = (k^2 * t^2 + 2 * k * t * v + v^2) / (2 * b)"
    by (simp add: \<open>(k * t + v)\<^sup>2 = k\<^sup>2 * t\<^sup>2 + 2 * k * t * v + v\<^sup>2\<close>)
  also have "... = k^2 * t^2 / (2 * b)+ k * t * v/ b + v^2/ (2 * b)"
    by divide_simplify
  finally have "?lhs = k * t\<^sup>2 / 2 + v * t + x + k^2 * t^2 / (2 * b)+ k * t * v/ b + v^2/ (2 * b) "
    by simp
  also have "... = (v * t + k * t * v/ b) + (k * t\<^sup>2 / 2 + k^2 * t^2 / (2 * b)) + x + v^2/ (2 * b)"
    by auto
  also have "... = v * t * (1 + k / b) + k * t^2 / 2 * (1 + k / b) + x + v^2 / (2 * b)"
    apply (clarsimp simp: ring_distribs(1))
    by (metis (no_types, hide_lams) divide_divide_eq_right mult_numeral_1 
power2_eq_square times_divide_eq_left)
  also have "... = (v * t + k * t^2 /2) * (1 + k / b) + x + v^2 / (2 * b) "
    apply clarsimp
    by (simp add: ring_class.ring_distribs(2))
  also have "... =  (v + k * t / 2) * t  * (1 + k / b) + x + v^2 / (2 * b) "
    apply clarsimp
    by (simp add: power2_eq_square ring_class.ring_distribs(2))
  finally have "?lhs = (v + k * t / 2) * t  * (1 + k / b) + x + v^2 / (2 * b)" (is "_ = ?d")
    by simp
  have "(v + k * t / 2) * t \<ge> 0" using assms(3) des1
    by fastforce
  hence "(v + k * t / 2) * t  * (1 + k / b) \<le> 0 " 
    using des2 divide_self_if neg_divide_le_eq by force 
  hence "?d \<le>  x + v^2 / (2 * b)"
    by simp
  hence "?lhs \<le> x + v^2 / (2 * b)"
    by (simp add: \<open>?d \<le> x + v\<^sup>2 / (2 * b)\<close> \<open>k * t\<^sup>2 / 2 + v * t + x + (k * t + v)\<^sup>2 / (2 * b) = ?d\<close>) 
  thus "?lhs \<le> S" 
    using assms(5)
    by auto
qed

lemma STTexample9a_arith:
  "(10*x-10*r) * v/4 + v\<^sup>2/2 + (x-r)*(2*r-2*x-3 * v)/2 + v * (2*r-2*x-3 * v)/2 \<le> (0::real)" 
  (is "?t1 + ?t2 + ?t3 + ?t4 \<le> 0")
  oops

lemma LICSexample4a_arith:
  assumes "(0::real) \<le> A" "0 < b" "v\<^sup>2 \<le> 2 * b * (m - x)" "0 \<le> t"
      and guard: "\<forall>\<tau>. 0 \<le> \<tau> \<and> \<tau> \<le> t \<longrightarrow> 0 \<le> A * \<tau> + v \<and> \<tau> \<le> \<epsilon>"
      and key: "v\<^sup>2 + (A * (A * \<epsilon>\<^sup>2 + 2 * \<epsilon> * v) + b * (A * \<epsilon>\<^sup>2 + 2 * \<epsilon> * v)) \<le> 2 * b * (m - x)" (is "?expr1 \<le> _")
    shows "(A * t + v)\<^sup>2 \<le> 2 * b * (m - (A * t\<^sup>2 / 2 + v * t + x))"
  oops

lemma "(a:: real) * a = a^2"
  oops

lemma LICSexample4c_arith1:
  assumes "v\<^sup>2 \<le> 2 * b * (m - x)" "0 \<le> t" "A \<ge> 0" "b > 0"
    and key: "v\<^sup>2 + (A * (A * \<epsilon>\<^sup>2 + 2 * \<epsilon> * v) + b * (A * \<epsilon>\<^sup>2 + 2 * \<epsilon> * v)) \<le> 2 * b * (m - x)"
    and guard: "\<forall>\<tau>. 0 \<le> \<tau> \<and> \<tau> \<le> t \<longrightarrow> (0::real) \<le> A * \<tau> + v \<and> \<tau> \<le> \<epsilon>"
  shows "(A * t + v)\<^sup>2 \<le> 2 * b * (m - (A * t\<^sup>2 / 2 + v * t + x))" (is "_ \<le> ?rhs")
proof-
  have " ?rhs = 2 * b *(m - A * t\<^sup>2 / 2 - v * t - x)"
    by simp
  also have "... = 2 * b * m - 2 * b * (A * t^2 / 2) - 2 * b * v * t - 2 * b * x"
    by (simp add: cross3_simps(25))
  also have "... = 2 * b * (m- x) - 2 * b * (A * t^2 / 2) - 2 * b * v * t"
    by (simp add: cross3_simps(25))
  also have "... =  2 * b * (m- x) - b * A * t^2  - 2 * b * v * t "
    by simp
  also have "... = 2 * b * (m- x) - b * (A * t^2  + 2 * v * t)"
    by (simp add: vector_space_over_itself.scale_right_distrib)
  finally have exp1: "?rhs =  2 * b * (m- x) - b * (A * t^2  + 2 * v * t)"
    by simp
  have exp2: "t \<le> \<epsilon>"
    using guard by (simp add: assms(2))
  have "v \<ge> 0" 
    using assms(6) assms(2) mult_not_zero by auto
  hence " 2 * t * v \<le> 2 * \<epsilon> * v" and "A * t^2 \<le> A * \<epsilon>^2"
    using assms(3) exp2 assms(2) mult_right_mono apply auto[1]
    by (simp add: assms(2) assms(3) guard mult_mono)
  hence exp3: "A * t^2 + 2 * t * v \<le> A * \<epsilon>^2 + 2 * \<epsilon> * v"
    by simp
  hence exp4: "A *(A * t^2 + 2 * t * v) \<le> A* (A * \<epsilon>^2 + 2 * \<epsilon> * v)"
    by (simp add: assms(3) ordered_comm_semiring_class.comm_mult_left_mono)
  have "b *(A * t^2 + 2 * t * v) \<le> b* (A * \<epsilon>^2 + 2 * \<epsilon> * v)"
    using exp3 assms(4) by auto 
  hence "v\<^sup>2 + (A * (A * t\<^sup>2 + 2 * t * v) + b * (A * t\<^sup>2 + 2 * t * v)) \<le> v\<^sup>2 + (A * (A * \<epsilon>\<^sup>2 + 2 * \<epsilon> * v) + b * (A * \<epsilon>\<^sup>2 + 2 * \<epsilon> * v))"
    using exp4 by auto
  hence exp5: "v\<^sup>2 + (A * (A * t\<^sup>2 + 2 * t * v) + b * (A * t\<^sup>2 + 2 * t * v)) \<le> 2 * b * (m - x)" (is "?f \<le> _")
    using assms(5) by simp
  have "?f = v^2 + A * A * t\<^sup>2 + 2 * A * t * v + b * A * t\<^sup>2 + 2 * b * t * v" (is "_ = ?g")
    by (clarsimp simp: algebra_simps(18))
  hence "?g \<le> 2 * b * (m - x) " 
    using exp5 by simp
  hence "v^2 + A * A * t\<^sup>2 + 2 * A * t * v \<le> 2 * b * (m - x) - b * A * t\<^sup>2 - 2 * b * t * v"
    by simp
  hence exp6: "A * A * t\<^sup>2 + 2 * A * t * v + v^2 \<le> 2 * b * (m - x) -2* b * A * t\<^sup>2 / 2- 2 * b * t * v"
    by simp
  have "(A * t + v)^2  = A * A * t\<^sup>2 + 2 * A * t * v + v^2"
    by (simp add: power2_diff power2_sum power_mult_distrib semiring_normalization_rules(29))
  have "2 * b * (m - x) -2* b * A * t\<^sup>2 / 2- 2 * b * t * v = 2 * b * (m- x) - b * A * t^2 -b* 2 * v * t"
    by simp
  also have "... = 2 * b * (m- x) - b * (A * t^2  + 2 * v * t)"
    using \<open>2 * b * (m - x) - b * A * t\<^sup>2 - 2 * b * v * t = 2 * b * (m - x) - b * (A * t\<^sup>2 + 2 * v * t)\<close>
    by auto 
  also have "... = ?rhs"
    using exp1 by simp
  finally have "2 * b * (m - x) -2* b * A * t\<^sup>2 / 2- 2 * b * t * v = ?rhs".
  thus "(A * t + v)^2 \<le> ?rhs"
    using exp6 \<open>(A * t + v)\<^sup>2 = A * A * t\<^sup>2 + 2 * A * t * v + v\<^sup>2\<close> by presburger 
qed


lemma LICSexample5_arith1:
  assumes "(0::real) < b" "0 \<le> t"
    and key: "v\<^sup>2 \<le> 2 * b * (m - x)"
  shows "v * t - b * t\<^sup>2 / 2 + x \<le> m"
proof-
  have "(v - b* t)^2 \<ge>0 "
    by simp
  have "v^2 - 2*b*(m-x)\<le>0 " using assms(3)
    by simp
  hence "(v - b* t)^2 \<ge> v^2 - 2*b*(m-x) "
    using \<open>0 \<le> (v - b * t)\<^sup>2\<close> by linarith
  have cuad: "(v - b* t)^2 = v^2 -2 * v * b* t + b^2 * t^2 "
     by bin_unfold
  have "v^2 -2 * v * b* t + b^2 * t^2 \<ge>  v^2 - 2*b*(m-x)"
    using cuad \<open>v\<^sup>2 - 2 * b * (m - x) \<le> (v - b * t)\<^sup>2\<close> by auto
  hence " 2 * b * (m-x) - v^2 \<ge> - v\<^sup>2 + 2 * v * b* t - b^2 * t^2 "
    by auto
  hence " 2 * b * (m-x) \<ge>  2 * v * b* t - b^2 * t^2 "
    by simp
  hence "2 * b * (m-x) / (2 * b) \<ge> (2 * v * b* t - b^2 * t^2) / (2 * b) " using assms(1) consprod
    by (metis eq_divide_eq_numeral1(1) half_gt_zero_iff mult_2 mult_2_right)
  hence "m - x \<ge> (2 * v * b* t - b^2 * t^2) / (2 * b) "
    using assms(1) by auto 
  have " (2 * v * b* t - b^2 * t^2) / (2 * b) = 2 * v * b * t / (2 * b) - b^2 * t^2 / (2 * b)  "
    by (simp add: diff_divide_distrib)
  also have "... = v * t - b^2 * t^2 / (2 * b)"
    using assms(1) by auto
  also have "... = v * t - b * t^2 / 2  "
    apply clarsimp
    by (simp add: power2_eq_square)
  finally have r1: "(2 * v * b* t - b^2 * t^2) / (2 * b) =   v * t - b * t^2 / 2"
    by simp
  have "m - x \<ge>  v * t - b * t^2 / 2 "
    using r1 \<open>(2 * v * b * t - b\<^sup>2 * t\<^sup>2) / (2 * b) \<le> m - x\<close> by auto
  thus  "v * t - b * t\<^sup>2 / 2 + x \<le> m"
    using \<open>v * t - b * t\<^sup>2 / 2 \<le> m - x\<close> by fastforce 
qed

lemma LICSexample5_arith2:
  assumes "(0::real) < b" "0 \<le> v" "\<forall>t\<in>{0..}. v * t - b * t\<^sup>2 / 2 + x \<le> m"
  shows "v\<^sup>2 \<le> 2 * b * (m - x)"
proof-
  have h1: "v / b \<ge> 0 "
    using assms(1) assms(2) by auto
have h2: "2 *b > 0 "
    using assms(1) by simp
  have "v * (v/b) - b * (v/b)\<^sup>2 / 2 + x \<le> m "
    using assms(3) apply (erule_tac x = "v/b" in ballE) 
     apply simp
    using h1 by simp
  have "v * (v/b) - b * (v/b)\<^sup>2 / 2 + x = v^2 / b - 1/2 * v^2 / b + x"
    by (clarsimp simp: power2_eq_square)
  also have "... = 1/2 * v^2 /b + x "
    by simp
  also have "... = v^2 / (2*b)+x"
    by simp
  finally have "v * (v/b) - b * (v/b)\<^sup>2 / 2 + x = v^2 / (2*b)+x ".
  hence "v^2 / (2*b)+x \<le> m"
    using \<open>v * (v / b) - b * (v / b)\<^sup>2 / 2 + x \<le> m\<close> by auto
  hence "v^2 / (2*b) \<le> m - x" 
    by auto
  hence "(2*b) * v^2 / (2*b) \<le> (2 * b)* (m - x) " using h2 consprod2
    by (metis times_divide_eq_right)
  thus "v^2 \<le> 2 * b* (m - x) "
    using h2 by auto
qed

(*lemma "(p  \<Longrightarrow> False) \<Longrightarrow> \<not> p  "
  by (rule notI)*)

lemma LICSexample6_arith1:
  assumes "0 \<le> v" "0 < b" "0 \<le> A" "0 \<le> \<epsilon>" 
    and guard: "\<forall>t\<in>{0..}. (\<forall>\<tau>. 0 \<le> \<tau> \<and> \<tau> \<le> t \<longrightarrow> \<tau> \<le> \<epsilon>) \<longrightarrow> (\<forall>\<tau>\<in>{0..}. 
  A * t * \<tau> + v * \<tau> - b * \<tau>\<^sup>2 / 2 + (A * t\<^sup>2 / 2 + v * t + x) \<le> (m::real))"
  shows "v\<^sup>2 + (A * (A * \<epsilon>\<^sup>2 + 2 * \<epsilon> * v) + b * (A * \<epsilon>\<^sup>2 + 2 * \<epsilon> * v)) \<le> 2 * b * (m - x)"
  oops

lemma ETCS_arith1: 
  assumes "0 < b" "0 \<le> A" "0 \<le> v" "0 \<le> t"
    and "v\<^sup>2 / (2 * b) + (A * (A * \<epsilon>\<^sup>2 / 2 + \<epsilon> * v)/ b + (A * \<epsilon>\<^sup>2 / 2 + \<epsilon> * v)) \<le> m - x" (is "?expr1 \<le> m - x")
    and guard: "\<forall>\<tau>. 0 \<le> \<tau> \<and> \<tau> \<le> t \<longrightarrow> \<tau> \<le> \<epsilon>"
  shows "(A * t + v)\<^sup>2/(2 * b) \<le> (m::real) - (A * t\<^sup>2/2 + v * t + x)" (is "?lhs \<le> ?rhs")
proof-
 have "(A * t + v)\<^sup>2  = (A^2 * t^2 + 2 * A * t * v + v^2)"
    by bin_unfold
  hence "(A * t + v)\<^sup>2/ (2 * b) = (A^2 * t^2 + 2 * A * t * v + v^2) / (2 * b)"
    by (simp add: \<open>(A * t + v)\<^sup>2 = A^2 * t\<^sup>2 + 2 * A * t * v + v\<^sup>2\<close>)
  also have "... = A^2 * t^2 / (2 * b)+ A * t * v/ b + v^2/ (2 * b)"
    by divide_simplify
  also have "... = (A^2 * t\<^sup>2 / 2)/ b + (A * t * v) / b + v^2/ (2 * b)"
    by simp
  also have "... = (A^2 * t\<^sup>2 / 2 + A * t * v)/ b + v^2/ (2 * b)"
    apply clarsimp
    by (simp add: sumfrac(1))
  also have "... = A * (A * t^2 / 2 + t * v) / b + v^2 /(2 * b)"
    apply clarsimp using assms(1) assms(4) 
    by (simp add: Groups.algebra_simps(18) power2_eq_square)
  have "t \<le> \<epsilon>"
    using assms(6) assms(4) by simp
  hence "v *t \<le> v * \<epsilon>"  
    using assms(3) by (simp add: mult_left_mono)
  have "A * t^2 / 2 \<le> A * \<epsilon>^2 / 2"
    by (simp add: \<open>t \<le> \<epsilon>\<close> assms(2) assms(4) mult_mono power_mono)
  have "?expr1 = v\<^sup>2 / (2 * b) + (A^2 * \<epsilon>\<^sup>2 / 2 + A * \<epsilon> * v)/ b + A * \<epsilon>\<^sup>2 / 2 + \<epsilon> * v"
    apply clarsimp
    sorry 
  oops

lemma ETCS_Prop1_arith2:
  assumes "0 \<le> v" "0 \<le> \<delta>" "0 < b" "x \<le> m" "0 \<le> (t::real)"
      and key: "v\<^sup>2 - \<delta>\<^sup>2 \<le> 2 * b * (m - x)" "m \<le> v * t - b * t\<^sup>2 / 2 + x"
      and guard: "\<forall>\<tau>\<in> closed_segment 0 t. b * \<tau> \<le> v"
    shows "v - b * t \<le> \<delta>"
proof-
  have d0: "2 * b > 0"
    using assms(3) by simp
  have "m - x \<le> v * t - b * t\<^sup>2 / 2"
    using assms(7) by simp
  hence d1: "m - x - v^2 /(2* b) \<le> v * t - b * t\<^sup>2 / 2 - v^2 /(2* b)"
    by simp
  have " - (v - b * t)\<^sup>2 = - (v^2 - 2 * v * b * t + b^2 * t^2)"
    by bin_unfold
  hence "- (v - b * t)\<^sup>2/(2* b) = - (v^2 - 2 * v * b * t + b^2 * t^2) /(2* b)"
    by simp
  also have "... = - (v^2 /(2* b) - 2 * v * b * t /(2* b) + b^2 * t^2 /(2* b))"
    by (metis (no_types, hide_lams) add_diff_cancel_right' sumfrac(1) uminus_add_conv_diff)
  also have "... = - (v^2 /(2* b) - v * t + b * t^2 / 2) "
    using assms(3) apply clarsimp 
    by (simp add: power2_eq_square)
  also have "... = - v\<^sup>2 /(2* b) + v * t - b * t^2 / 2"
    by auto
  finally have "- (v - b * t)\<^sup>2/(2* b) =  - v\<^sup>2 /(2* b) + v * t - b * t^2 / 2 "
    by simp
  hence "m - x - v^2 /(2* b) \<le> - (v - b * t)\<^sup>2/(2* b)"
    using d1 by simp
  hence d2: "(2* b) *(m - x - v^2 /(2* b)) \<le> (2 * b) * (-(v - b * t)\<^sup>2 / (2* b))"
    using d0 consprod2
    by blast
  have eq1: "(2* b) *(m - x - v^2 /(2* b)) = (2* b) *(m - x) - v^2"
    using assms(3) by (simp add: Groups.algebra_simps(19))
  have eq2: "(2 * b) * (-(v - b * t)\<^sup>2 / (2* b)) = -(v - b * t)\<^sup>2"
    using d0 by auto
  have d3: " (2* b) *(m - x) - v^2 \<le> -(v - b * t)\<^sup>2 " 
    using eq1 eq2 d2 by simp
  have "- \<delta>\<^sup>2 \<le> (2* b) *(m - x) - v^2 "
    using assms(6) by simp
  hence "- \<delta>\<^sup>2 \<le> -(v - b * t)\<^sup>2"
    using d3 by auto
  hence d4: "(v - b * t)\<^sup>2 \<le> \<delta>\<^sup>2"
    by simp
  have " b * t \<le> v" using assms(8)
    by simp
  hence "v - b * t \<ge> 0" 
    by simp
  thus "v - b * t \<le> \<delta>"
    using d4 assms(2) pos2 power_mono_iff by blast
qed

(*
Aquí iré haciendo pruebas de algunas herramientas de Eisbach
*)
method elimconj = (rule impI, erule conjE)

lemma "P \<and> Q \<longrightarrow> P"
  by elimconj

named_theorems eliminacion

declare conjE[eliminacion]

method elimconj2 = ((rule impI, (erule eliminacion)?) | assumption)+

lemma "P \<and> Q \<longrightarrow> P"
  by elimconj2

named_theorems introduccion

declare conjI [introduccion] and impI [introduccion]

method elimconj3 = ((rule introduccion, (erule eliminacion)?) | assumption)+

lemma "P \<and> Q \<longrightarrow> P"
  by elimconj3

method rule_twice uses my_rule =
(rule my_rule, rule my_rule)

lemma "P \<and> P \<and> P \<Longrightarrow> P"
  by (rule_twice my_rule: conjE)

lemma "P \<Longrightarrow> P \<Longrightarrow> P \<Longrightarrow> P"
  by blast

method conjuncion uses rule =
(intro conjI ; intro rule)

lemma
assumes hip: "P"
shows "P \<and> P \<and> P"
  by (conjuncion rule: hip)

method divide_distrib uses rule =
(simp add: add_divide_distrib  diff_divide_distrib; simp add: power2_eq_square)

lemma STTejemplo3a_arith:
  assumes "0 < (B::real)" "0 \<le> t" "0 \<le> x2" and key: "x1 + x2\<^sup>2 / (2 * B) \<le> S"
  shows "x2 * t - B * t\<^sup>2 / 2 + x1 + (x2 - B * t)\<^sup>2 / (2 * B) \<le> S" (is "?lhs \<le> S")
  apply (bin_unfold, divide_distrib) using assms by (auto simp: power2_eq_square)
(* esta sería la prueba formal del lema:
  have "(x2 - B * t)\<^sup>2 =  x2\<^sup>2 -2 * B * x2 * t + B^2 * t\<^sup>2 "
     by bin_unfold
  hence "(x2 - B * t)\<^sup>2 / (2 * B) =(x2\<^sup>2 -2 * B * x2 * t + B^2 * t\<^sup>2) / (2 * B) " (is "_ = ?f")
    by simp
   also have "... = x2^2 /(2 * B)- 2 * B * x2* t/(2 * B) + B^2* t^2 /(2 * B) "
    by (simp add: add_divide_distrib  diff_divide_distrib)
  also have "... =x2^2 /(2 * B) - x2 * t + B* t^2/ 2 " using assms
    by (simp add: power2_eq_square)
  finally have "(x2 - B * t)\<^sup>2 / (2 * B) = x2^2 /(2 * B) - x2 * t + B* t^2/ 2 ".
  hence "?lhs = x1 + x2\<^sup>2 / (2 * B) "
    by simp
  thus  "?lhs \<le> S"
    using assms(4) by simp
qed

pero intentaré aplicar concatenación para escribir la prueba en menos líneas

proof-
have "(x2 - B * t)\<^sup>2 =  x2\<^sup>2 -2 * B * x2 * t + B^2 * t\<^sup>2 "
     by bin_unfold
  hence "(x2 - B * t)\<^sup>2 / (2 * B) = x2^2 /(2 * B) - x2 * t + B* t^2/ 2 " using assms
    by divide_distrib
  hence "?lhs = x1 + x2\<^sup>2 / (2 * B) "
    by simp
  thus  "?lhs \<le> S"
    using assms(4) by simp
qed
*)

(* (auto 0 3 intro!: teorema1 simp: teorema2 elim: teorema 3 dest: teorema 4) *)


lemma assumes "(x:: real) \<noteq>  y"
  shows "(x^2 - y^2)/ (x - y) = x + y" (is "?l =_")
proof-
  have "x^2 - y^2 = (x + y)*(x - y)"
    by (simp add: power2_eq_square square_diff_square_factored)
  hence "?l = (x + y)*(x - y)/(x-y)"
    by simp
  also have "... = x+y"
    by (simp add: assms)
  thus "?l= x+ y"
    by (simp add: calculation)
qed

lemma "(x :: real) * y = ((x + y)^2 - (x - y)^2) / 4"
  by bin_unfold

lemma assumes "(x:: real)^2 - 10 * x + 25 = 0"
  shows "x = 5"
proof-
  have "(x:: real)^2 - 10 * x + 25 = (x - 5)^2"
    by bin_unfold
 thus "x = 5" using assms by simp
qed

lemma domain: assumes "(x:: real) * y = 0"
  shows "x = 0 | y = 0"
  apply (rule divisors_zero) using assms.

(*lemma domain1: assumes "(x::real) * (x - 2) = 0"
  shows "x = 0 | x = 2"
proof-
  show "x = 0 | x = 2" using assms domain by simp
qed
*)

lemma assumes "(x:: real)^2 - 2 * x = 0"
  shows "x = 0 | x = 2"
proof-
  have "x^2 - 2 * x = x * (x - 2)"
    by (simp add: Groups.algebra_simps(19) power2_eq_square)
  thus  "x = 0 | x = 2" 
    using assms domain by simp
qed

(*
Intentare encontrar una tactica para simplificar cualquier monomio
*)
lemma "(a:: real) * (b* c) = (a * b) *c"
  apply (rule semiring_normalization_rules(18)).

lemma "(a:: real)* a^n = a^(Suc n)"
  by (rule semiring_normalization_rules(27))

lemma "(a:: real) * b = b * a"
  apply (rule cross3_simps(11))
  done

lemma "(x:: real) * y * z = x * z * y"
  by mon_simp

lemma "(a:: real) * a * b = a^2 * b"
  by mon_simp

lemma "(x:: real)^3 * y * x^2 * x = y * x^6"
  by mon_simp

lemma "(a:: real) * a^5 = a^6"
  by mon_simp

lemma "(x:: real)^2 * z^2 * y * z * x = x^3 * y * z^3"
  apply mon_simp
  done

thm monomial_rules

(*
  apply (simp add: mult.assoc[symmetric])
  apply mon_simp
  apply (simp add: cross3_simps(11) [of  "x^2" "z^2"])
  apply mon_simp
  oops
  apply mon_simp
  apply (simp add: mult.assoc[symmetric])
  apply mon_simp
*)

(*
Aqui desarrollare una tactica para encontrar el comun denominador entre dos fracciones
*)
lemma  assumes "b \<noteq> 0" and "d \<noteq> 0"
  shows "(a:: real) / b + c / d = (a * d + b * c) / (b * d)"
  by (simp add: add_frac_eq assms(1) assms(2))

lemma  assumes "b \<noteq> 0" and "d \<noteq> 0"
  shows "(a:: real) / b - c / d = (a * d - b * c) / (b * d)"
 by (simp add: diff_frac_eq assms(1) assms(2))

method frac_ad = (simp add: add_frac_eq  diff_frac_eq)

lemma "(1:: real) / 2 + 1 / 3 = 5 / 6"
  by frac_ad

lemma "(x:: real) / 2 + y / 6 = (3 * x + y) / 6"
  by frac_ad

lemma assumes "(k:: real) > 1"
  shows "1 / k + 1 / (1 - k) = 1 / (k * (1 - k))"
  using assms by frac_ad

lemma assumes "(k:: real) > 0" and "1 / (k * (k + 1)) \<le> S"
  shows "1 / k - 1 / (k+1) \<le> S"
 using assms by frac_ad


thm algebra_simps(5)
            
lemma "a * b = b * a" for a :: real
  apply (subst cross3_simps(11)[where b=b])
  apply (rule refl)
  done

lemma "a * b * c = c * a * b" for a::real
  apply (subst cross3_simps(11)[where b=c])+
  apply (subst mult.assoc)+
  apply (rule refl)
  done

(* Buscare una tactica para reagrupar variables  *)
lemma "(x:: real) * y * x * y * x = x^3 * y^2"
  apply (subst cross3_simps(11)[where b=x])+
  apply (subst mult.assoc)+
  apply mon_simp
  done


subsection \<open> Advanced \<close>

thm has_derivative_def
thm tendsto_def

lemma has_vderiv_mono_test:
  assumes T_hyp: "is_interval T" 
    and d_hyp: "(f has_vderiv_on f') T"
    and xy_hyp: "x\<in>T" "y\<in>T" "x \<le> y" 
  shows "\<forall>x\<in>T. (0::real) \<le> f' x \<Longrightarrow> f x \<le> f y"
    and "\<forall>x\<in>T. f' x \<le> 0 \<Longrightarrow> f x \<ge> f y"
  oops

lemma continuous_on_ge_ball_ge: 
  "continuous_on T f \<Longrightarrow> x \<in> T \<Longrightarrow> f x > (k::real) \<Longrightarrow> \<exists>\<epsilon>>0. \<forall>y\<in>ball x \<epsilon> \<inter> T. f y > k"
  oops

lemma current_vderiv_ge_always_ge:
  fixes c::real
  assumes init: "c < x t\<^sub>0" and ode: "D x = x' on {t\<^sub>0..}" 
    and dhyp: "x' = (\<lambda>t. g (x t))" "\<forall>x\<ge>c. g x \<ge> 0"
  shows "\<forall>t\<ge>t\<^sub>0. x t > c"
  oops

lemma LICSexample6_arith2:
  assumes "0 \<le> v" "0 < b" "0 \<le> A" "0 \<le> t" "0 \<le> \<tau>" "t \<le> \<epsilon>"
    and "v\<^sup>2 + (A * (A * \<epsilon>\<^sup>2 + 2 * \<epsilon> * v) + b * (A * \<epsilon>\<^sup>2 + 2 * \<epsilon> * v)) \<le> 2 * b * (m - x)"
  shows "A * \<epsilon> * \<tau> + s $ 2 * \<tau> - b * \<tau>\<^sup>2 / 2 + (A * \<epsilon>\<^sup>2 / 2 + s $ 2 * \<epsilon> + s $ 1) \<le> m"
  (* Need to show that function (\<lambda>\<tau>. A * \<epsilon> * \<tau> + s $ 2 * \<tau> - b * \<tau>\<^sup>2 / 2) attains maximum at \<tau> = (A*\<epsilon> + v)/b *)
  oops

lemma ETCS_Prop1_arith1:
  assumes "0 \<le> v" "0 \<le> \<delta>" "0 < b" "x \<le> m"
    and "\<forall>t\<in>{0..}. (\<forall>\<tau>\<in>{0--t}. b * \<tau> \<le> v) \<longrightarrow>
       m \<le> v * t - b * t\<^sup>2 / 2 + x \<longrightarrow> v - b * t \<le> \<delta>"
  shows "v\<^sup>2 - \<delta>\<^sup>2 \<le> 2 * b * (m - x)"
    (* solve arithmetic *)
  sorry

end