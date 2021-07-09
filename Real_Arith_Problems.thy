(*  Title:       
    Author:      
    Maintainer:  
*)

section \<open> Examples \<close>

text \<open> We prove partial correctness specifications of some hybrid systems with our 
verification components.\<close>

theory Real_Arith_Problems
  imports "HOL-Analysis.Analysis"

begin


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
  by (simp add: is_interval_1)

lemma "((a::real)-b)^2 = a^2 - 2 * a * b + b^2"
by (simp add: power2_diff power_mult_distrib)

lemma norm_rotate_eq:
  fixes x :: "'a:: {banach,real_normed_field}"
  shows "(x * cos t - y * sin t)\<^sup>2 + (x * sin t + y * cos t)\<^sup>2 = x\<^sup>2 + y\<^sup>2" (is "?a^2+?b^2 =_")
    and "(x * cos t + y * sin t)\<^sup>2 + (y * cos t - x * sin t)\<^sup>2 = x\<^sup>2 + y\<^sup>2" (is "?e^2+?f^2 =_")
proof-
  have exp1: "?a^2 = x^2 * (cos t)^2 -2 * x * y * cos t * sin t + y^2 * (sin t)^2 " (is "_ = ?c")
    by (simp add: power2_diff power_mult_distrib)
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
    by (simp add: power2_diff power_mult_distrib)
have id1:  "(cos t)^2 + (sin t)^2 = 1"
    by simp
  have "?e\<^sup>2 + ?f\<^sup>2 = ?g+?h "
    using exp3 exp4
    by presburger
  also have "... = x^2 * (cos t)^2 + x^2 * (sin t)^2  + y^2 * (sin t)^2 + y^2 * (cos t)^2  "
    by fastforce
  have "... = x^2 + y^2 "
    by (smt (z3) add_diff_cancel_left' diff_add_cancel id1 is_num_normalize(1)
 mult.commute mult_numeral_1 numeral_One vector_space_over_itself.scale_left_diff_distrib)
  finally show  "?e\<^sup>2 + ?f\<^sup>2 = x\<^sup>2 + y\<^sup>2"
    by (simp add: \<open>x\<^sup>2 * (cos t)\<^sup>2 + 2 * x * y * cos t * sin t + y\<^sup>2 * (sin t)\<^sup>2 
+ (y\<^sup>2 * (cos t)\<^sup>2 - 2 * x * y * sin t * cos t + x\<^sup>2 * (sin t)\<^sup>2) = x\<^sup>2 * (cos t)\<^sup>2
 + x\<^sup>2 * (sin t)\<^sup>2 + y\<^sup>2 * (sin t)\<^sup>2 + y\<^sup>2 * (cos t)\<^sup>2\<close> \<open>x\<^sup>2 * (cos t)\<^sup>2 + x\<^sup>2 * (sin t)\<^sup>2
 + y\<^sup>2 * (sin t)\<^sup>2 + y\<^sup>2 * (cos t)\<^sup>2 = x\<^sup>2 + y\<^sup>2\<close> calculation) 
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
 power_commutes semiring_norm(2) semiring_norm(7))
  have "?t1 - (- ?t2 - ?t3) - ?t4 - ?t5 = ?t2 + ?t3 - ?t5"
    by (simp add: \<open>36 * (x1\<^sup>2 * (x1 * x2 ^ 3)) = 36 * (x1\<^sup>2 * (x2 * x1)) * x2\<^sup>2\<close>)
  also have "... = ?t2 "
    by (metis diff_add_cancel mult.commute
 numeral_plus_numeral one_eq_numeral_iff power_add power_one_right pth_2 semiring_norm(3)
vector_space_over_itself.scale_scale)
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
    sorry
qed

lemma STTexample3a_arith:
  assumes "0 < (B::real)" "0 \<le> t" "0 \<le> x2" and key: "x1 + x2\<^sup>2 / (2 * B) \<le> S"
  shows "x2 * t - B * t\<^sup>2 / 2 + x1 + (x2 - B * t)\<^sup>2 / (2 * B) \<le> S" (is "?lhs \<le> S")
  oops

lemma STTexample5_arith:
  assumes "0 < A" "0 < B" "0 < \<epsilon>" "0 \<le> x2" "0 \<le> (t::real)" 
    and key: "x1 + x2\<^sup>2 / (2 * B) + (A * (A * \<epsilon>\<^sup>2 / 2 + \<epsilon> * x2) / B + (A * \<epsilon>\<^sup>2 / 2 + \<epsilon> * x2)) \<le> S" (is "?k3 \<le> S")
    and ghyp: "\<forall>\<tau>. 0 \<le> \<tau> \<and> \<tau> \<le> t \<longrightarrow> \<tau> \<le> \<epsilon>"
  shows "A * t\<^sup>2 / 2 + x2 * t + x1 + (A * t + x2)\<^sup>2 / (2 * B) \<le> S" (is "?k0 \<le> S")
  oops

lemma STTexample6_arith:
  assumes "0 < A" "0 < B" "0 < \<epsilon>" "0 \<le> x2" "0 \<le> (t::real)" "- B \<le> k" "k \<le> A"
    and key: "x1 + x2\<^sup>2 / (2 * B) + (A * (A * \<epsilon>\<^sup>2 / 2 + \<epsilon> * x2) / B + (A * \<epsilon>\<^sup>2 / 2 + \<epsilon> * x2)) \<le> S" (is "?k3 \<le> S")
    and ghyp: "\<forall>\<tau>. 0 \<le> \<tau> \<and> \<tau> \<le> t \<longrightarrow> 0 \<le> k * \<tau> + x2 \<and> \<tau> \<le> \<epsilon>"
  shows "k * t\<^sup>2 / 2 + x2 * t + x1 + (k * t + x2)\<^sup>2 / (2 * B) \<le> S" (is "?k0 \<le> S")
  oops


subsubsection \<open> STTT Tutorial: Example 7 \<close>

lemma STTexample7_arith1:
  assumes "(0::real) < A" "0 < b" "0 < \<epsilon>" "0 \<le> v" "0 \<le> t" "k \<le> A"
    and "x + v\<^sup>2 / (2 * b) + (A * (A * \<epsilon>\<^sup>2 / 2 + \<epsilon> * v) / b + (A * \<epsilon>\<^sup>2 / 2 + \<epsilon> * v)) \<le> S" (is "?expr1 \<le> S")
    and guard: "\<forall>\<tau>. 0 \<le> \<tau> \<and> \<tau> \<le> t \<longrightarrow> 0 \<le> k * \<tau> + v \<and> \<tau> \<le> \<epsilon>"
  shows "k * t\<^sup>2 / 2 + v * t + x + (k * t + v)\<^sup>2 / (2 * b) \<le> S" (is "?lhs \<le> S")
  oops

lemma STTexample7_arith2:
  assumes "(0::real) < b" "0 \<le> v" "0 \<le> t" "k \<le> - b"
    and key: "x + v\<^sup>2 / (2 * b) \<le> S" 
    and guard: "\<forall>\<tau>. 0 \<le> \<tau> \<and> \<tau> \<le> t \<longrightarrow> 0 \<le> k * \<tau> + v \<and> \<tau> \<le> \<epsilon>"
  shows "k * t\<^sup>2 / 2 + v * t + x + (k * t + v)\<^sup>2 / (2 * b) \<le> S" (is "?lhs \<le> S")
  oops

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

lemma LICSexample4c_arith1:
  assumes "v\<^sup>2 \<le> 2 * b * (m - x)" "0 \<le> t" "A \<ge> 0" "b > 0"
    and key: "v\<^sup>2 + (A * (A * \<epsilon>\<^sup>2 + 2 * \<epsilon> * v) + b * (A * \<epsilon>\<^sup>2 + 2 * \<epsilon> * v)) \<le> 2 * b * (m - x)"
    and guard: "\<forall>\<tau>. 0 \<le> \<tau> \<and> \<tau> \<le> t \<longrightarrow> (0::real) \<le> A * \<tau> + v \<and> \<tau> \<le> \<epsilon>"
  shows "(A * t + v)\<^sup>2 \<le> 2 * b * (m - (A * t\<^sup>2 / 2 + v * t + x))" (is "_ \<le> ?rhs")
  oops


lemma LICSexample5_arith1:
  assumes "(0::real) < b" "0 \<le> t"
    and key: "v\<^sup>2 \<le> 2 * b * (m - x)"
  shows "v * t - b * t\<^sup>2 / 2 + x \<le> m"
  oops

lemma LICSexample5_arith2:
  assumes "(0::real) < b" "0 \<le> v" "\<forall>t\<in>{0..}. v * t - b * t\<^sup>2 / 2 + x \<le> m"
  shows "v\<^sup>2 \<le> 2 * b * (m - x)"
  oops

lemma LICSexample6_arith1:
  assumes "0 \<le> v" "0 < b" "0 \<le> A" "0 \<le> \<epsilon>" and guard: "\<forall>t\<in>{0..}. (\<forall>\<tau>. 0 \<le> \<tau> \<and> \<tau> \<le> t \<longrightarrow> \<tau> \<le> \<epsilon>) \<longrightarrow> (\<forall>\<tau>\<in>{0..}. 
  A * t * \<tau> + v * \<tau> - b * \<tau>\<^sup>2 / 2 + (A * t\<^sup>2 / 2 + v * t + x) \<le> (m::real))"
  shows "v\<^sup>2 + (A * (A * \<epsilon>\<^sup>2 + 2 * \<epsilon> * v) + b * (A * \<epsilon>\<^sup>2 + 2 * \<epsilon> * v)) \<le> 2 * b * (m - x)"
  oops

lemma ETCS_arith1: 
  assumes "0 < b" "0 \<le> A" "0 \<le> v" "0 \<le> t"
    and "v\<^sup>2 / (2 * b) + (A * (A * \<epsilon>\<^sup>2 / 2 + \<epsilon> * v)/ b + (A * \<epsilon>\<^sup>2 / 2 + \<epsilon> * v)) \<le> m - x" (is "?expr1 \<le> m - x")
    and guard: "\<forall>\<tau>. 0 \<le> \<tau> \<and> \<tau> \<le> t \<longrightarrow> \<tau> \<le> \<epsilon>"
  shows "(A * t + v)\<^sup>2/(2 * b) \<le> (m::real) - (A * t\<^sup>2/2 + v * t + x)" (is "?lhs \<le> ?rhs")
  oops

lemma ETCS_Prop1_arith2:
  assumes "0 \<le> v" "0 \<le> \<delta>" "0 < b" "x \<le> m" "0 \<le> (t::real)"
      and key: "v\<^sup>2 - \<delta>\<^sup>2 \<le> 2 * b * (m - x)" "m \<le> v * t - b * t\<^sup>2 / 2 + x"
      and guard: "\<forall>\<tau>\<in>{0--t}. b * \<tau> \<le> v"
    shows "v - b * t \<le> \<delta>"
  oops

subsection \<open> Advanced \<close>

lemma has_vderiv_mono_test:
  assumes T_hyp: "is_interval T" 
    and d_hyp: "D f = f' on T"
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