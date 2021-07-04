(*  Title:       
    Author:      
    Maintainer:  
*)

section \<open> Examples \<close>

text \<open> We prove partial correctness specifications of some hybrid systems with our 
verification components.\<close>

theory Real_Arith_Solutions
  imports "HOL-Analysis.Analysis"

begin


subsection \<open> Basic \<close>

lemma abs_le_eq:
  shows "(r::real) > 0 \<Longrightarrow> (\<bar>x\<bar> < r) = (-r < x \<and> x < r)"
    and "(r::real) > 0 \<Longrightarrow> (\<bar>x\<bar> \<le> r) = (-r \<le> x \<and> x \<le> r)"
  by linarith+

lemma is_interval_real_nonneg[simp]: "is_interval (Collect ((\<le>) (0::real)))"
  by (auto simp: is_interval_def)

lemma norm_rotate_eq[simp]:
  fixes x :: "'a:: {banach,real_normed_field}"
  shows "(x * cos t - y * sin t)\<^sup>2 + (x * sin t + y * cos t)\<^sup>2 = x\<^sup>2 + y\<^sup>2"
    and "(x * cos t + y * sin t)\<^sup>2 + (y * cos t - x * sin t)\<^sup>2 = x\<^sup>2 + y\<^sup>2"
proof-
  have "(x * cos t - y * sin t)\<^sup>2 = x\<^sup>2 * (cos t)\<^sup>2 + y\<^sup>2 * (sin t)\<^sup>2 - 2 * (x * cos t) * (y * sin t)"
    by(simp add: power2_diff power_mult_distrib)
  also have "(x * sin t + y * cos t)\<^sup>2 = y\<^sup>2 * (cos t)\<^sup>2 + x\<^sup>2 * (sin t)\<^sup>2 + 2 * (x * cos t) * (y * sin t)"
    by(simp add: power2_sum power_mult_distrib)
  ultimately show "(x * cos t - y * sin t)\<^sup>2 + (x * sin t + y * cos t)\<^sup>2 = x\<^sup>2 + y\<^sup>2"
    by (simp add: Groups.mult_ac(2) Groups.mult_ac(3) right_diff_distrib sin_squared_eq)
  thus "(x * cos t + y * sin t)\<^sup>2 + (y * cos t - x * sin t)\<^sup>2 = x\<^sup>2 + y\<^sup>2"
    by (simp add: add.commute add.left_commute power2_diff power2_sum)
qed


lemma mult_abs_right_mono: "a < b \<Longrightarrow> a * \<bar>c\<bar> \<le> b * \<bar>c\<bar>" for c::real
  by (simp add: mult_right_mono)

lemma dyn_cons_qty_arith: "(36::real) * (x1\<^sup>2 * (x1 * x2 ^ 3)) - 
  (- (24 * (x1\<^sup>2 * x2) * x1 ^ 3 * (x2)\<^sup>2) - 12 * (x1\<^sup>2 * x2) * x1 * x2 ^ 4) - 
  36 * (x1\<^sup>2 * (x2 * x1)) * (x2)\<^sup>2 - 12 * (x1\<^sup>2 * (x1 * x2 ^ 5)) = 24 * (x1 ^ 5 * x2 ^ 3)" 
  (is "?t1 - (- ?t2 - ?t3) - ?t4 - ?t5 = ?t6")
proof-
  have eq1: "?t1 = ?t4"
    by (simp add: power2_eq_square power3_eq_cube)
  have eq2: "- (- ?t2 - ?t3) = (?t6 + ?t3)"
    by (auto simp: field_simps semiring_normalization_rules(27))
  have eq3: "?t3 = ?t5"
    by (auto simp: field_simps semiring_normalization_rules(27))
  show "?t1 - (- ?t2 - ?t3) - ?t4 - ?t5 = ?t6"
    unfolding eq1 eq2 eq3 by (simp add: field_simps semiring_normalization_rules(27))
qed

lemma local_lipschitz_first_order_linear:
  fixes c::"real \<Rightarrow> real"
  assumes "continuous_on T c"
  shows "local_lipschitz T UNIV (\<lambda>t. (*) (c t))"
proof(unfold local_lipschitz_def lipschitz_on_def, clarsimp simp: dist_norm)
  fix x t::real assume "t \<in> T"
  then obtain \<delta> where d_hyp: "\<delta> > 0 \<and> (\<forall>\<tau>\<in>T. \<bar>\<tau> - t\<bar> < \<delta> \<longrightarrow> \<bar>c \<tau> - c t\<bar> < max 1 \<bar>c t\<bar>)"
    using assms unfolding continuous_on_iff 
    apply(erule_tac x=t in ballE, erule_tac x="max 1 (\<bar>c t\<bar>)" in allE; clarsimp)
    by (metis dist_norm less_max_iff_disj real_norm_def zero_less_one)
  {fix \<tau> x\<^sub>1 x\<^sub>2 
    assume "\<tau> \<in> cball t (\<delta>/2) \<inter> T" "x\<^sub>1 \<in> cball x (\<delta>/2)" "x\<^sub>2 \<in> cball x (\<delta>/2)" 
    hence "\<bar>\<tau> - t\<bar> < \<delta>" "\<tau> \<in> T"
      by (auto simp: dist_norm, smt d_hyp)
    hence "\<bar>c \<tau> - c t\<bar> < max 1 \<bar>c t\<bar>"
      using d_hyp by auto
    hence "- (max 1 \<bar>c t\<bar> + \<bar>c t\<bar>) < c \<tau> \<and> c \<tau> < max 1 \<bar>c t\<bar> + \<bar>c t\<bar>"
      by (auto simp: abs_le_eq)
    hence obs: "\<bar>c \<tau>\<bar> < max 1 \<bar>c t\<bar> + \<bar>c t\<bar>"
      by (simp add: abs_le_eq)
    have "\<bar>c \<tau> * x\<^sub>1 - c \<tau> * x\<^sub>2\<bar> = \<bar>c \<tau>\<bar> * \<bar>x\<^sub>1 - x\<^sub>2\<bar>"
      by (metis abs_mult left_diff_distrib mult.commute)
    also have "... \<le> (max 1 \<bar>c t\<bar> + \<bar>c t\<bar>) * \<bar>x\<^sub>1 - x\<^sub>2\<bar>"
      using mult_abs_right_mono[OF obs] by blast
    finally have "\<bar>c \<tau> * x\<^sub>1 - c \<tau> * x\<^sub>2\<bar> \<le> (max 1 \<bar>c t\<bar> + \<bar>c t\<bar>) * \<bar>x\<^sub>1 - x\<^sub>2\<bar>" .}
  hence "\<exists>L. \<forall>t\<in>cball t (\<delta>/2) \<inter> T. 0 \<le> L \<and>
    (\<forall>x\<^sub>1\<in>cball x (\<delta>/2). \<forall>x\<^sub>2\<in>cball x (\<delta>/2). \<bar>c t * x\<^sub>1 - c t * x\<^sub>2\<bar> \<le> L * \<bar>x\<^sub>1 - x\<^sub>2\<bar>)"
    by (rule_tac x="max 1 \<bar>c t\<bar> + \<bar>c t\<bar>" in exI, clarsimp simp: dist_norm)
  thus "\<exists>u>0. \<exists>L. \<forall>t\<in>cball t u \<inter> T. 0 \<le> L \<and> 
    (\<forall>xa\<in>cball x u. \<forall>y\<in>cball x u. \<bar>c t * xa - c t * y\<bar> \<le> L * \<bar>xa - y\<bar>)"
    apply(rule_tac x="\<delta>/2" in exI) 
    using d_hyp by auto
qed

lemma darboux_ineq_arith:
  assumes "0 \<le> s\<^sub>1 + s\<^sub>2" and "0 \<le> (t::real)" and "t * s\<^sub>1 < 1"
  shows "0 \<le> s\<^sub>1 / (1 - t * s\<^sub>1) + (s\<^sub>2 - s\<^sub>1 * ln (1 - t * s\<^sub>1)) / (1 - t * s\<^sub>1)"
proof-
  have "s\<^sub>1 * ln (1 - t * s\<^sub>1) \<le> 0"
  proof(cases "s\<^sub>1 \<le> 0")
    case True
    hence "1 - t * s\<^sub>1 \<ge> 1"
      using \<open>0 \<le> t\<close> by (simp add: mult_le_0_iff)
    thus ?thesis
      using True ln_ge_zero mult_nonneg_nonpos2 by blast
  next
    case False
    hence "1 - t * s\<^sub>1 \<le> 1"
      using \<open>0 \<le> t\<close> by auto
    thus ?thesis
      by (metis (mono_tags, hide_lams) False add.left_neutral antisym_conv assms(3) 
          diff_le_eq ln_ge_zero_iff ln_one mult_zero_right not_le order_refl zero_le_mult_iff)
  qed
  hence "s\<^sub>1 + s\<^sub>2 - s\<^sub>1 * ln (1 - t * s\<^sub>1) \<ge> s\<^sub>1 + s\<^sub>2"
    by linarith
  hence "(s\<^sub>1 + s\<^sub>2 - s\<^sub>1 * ln (1 - t * s\<^sub>1))/(1 - t * s\<^sub>1) \<ge> (s\<^sub>1 + s\<^sub>2)/(1 - t * s\<^sub>1)"
    using \<open>t * s\<^sub>1 < 1\<close> by (simp add: \<open>0 \<le> s\<^sub>1 + s\<^sub>2\<close> divide_right_mono)
  also have "(s\<^sub>1 + s\<^sub>2)/(1 - t * s\<^sub>1) \<ge> 0"
    using \<open>t * s\<^sub>1 < 1\<close> by (simp add: \<open>0 \<le> s\<^sub>1 + s\<^sub>2\<close>)
  ultimately show ?thesis
    by (metis (full_types) add_diff_eq add_divide_distrib order_trans)
qed

lemma picard_lindeloef_dyn_bif: "continuous_on T g \<Longrightarrow> t\<^sub>0 \<in> T \<Longrightarrow> is_interval T \<Longrightarrow>
  open T \<Longrightarrow> (t::real) \<in> T \<Longrightarrow> \<exists>u>0. (\<exists>ta. \<bar>t - ta\<bar> \<le> u \<and> ta \<in> T) \<longrightarrow> 
  (\<exists>L\<ge>0. \<forall>xa\<in>cball (x::real) u. \<forall>y\<in>cball x u. \<bar>xa\<^sup>2 - y\<^sup>2\<bar> \<le> L * \<bar>xa - y\<bar>)"
proof-
  {fix x1 and x2
    assume "x1 \<in>cball x 1" and "x2 \<in>cball x 1"
    hence leq: "\<bar>x - x1\<bar> \<le> 1" "\<bar>x - x2\<bar> \<le> 1"
      by (auto simp: dist_norm)
    have "\<bar>x1 + x2\<bar> = \<bar>x1 - x + x2 - x + 2 * x\<bar>"
      by simp
    also have "... \<le> \<bar>x1 - x\<bar> + \<bar>x2 - x\<bar> + 2 * \<bar>x\<bar>"
      using abs_triangle_ineq by auto
    also have "... \<le> 2 * (1 + \<bar>x\<bar>)"
      using leq by auto
    finally have obs: "\<bar>x1 + x2\<bar> \<le> 2 * (1 + \<bar>x\<bar>)" .
    also have "\<bar>x1\<^sup>2 - x2\<^sup>2\<bar> = \<bar>x1 + x2\<bar>*\<bar>x1 - x2\<bar>"
      by (metis abs_mult power2_eq_square square_diff_square_factored)
    ultimately have "\<bar>x1\<^sup>2 - x2\<^sup>2\<bar> \<le> (2 * (1 + \<bar>x\<bar>)) * \<bar>x1 - x2\<bar>"
      by (metis abs_ge_zero mult_right_mono)}
  thus "\<exists>u>0. (\<exists>\<tau>. \<bar>t - \<tau>\<bar> \<le> u \<and> \<tau> \<in> T) \<longrightarrow> 
  (\<exists>L\<ge>0. \<forall>xa\<in>cball x u. \<forall>y\<in>cball x u. \<bar>xa\<^sup>2 - y\<^sup>2\<bar> \<le> L * \<bar>xa - y\<bar>)"
    by (rule_tac x=1 in exI, clarsimp, rule_tac x="2 * (1 + \<bar>x\<bar>)" in exI, auto)
qed

lemma STTexample3a_arith:
  assumes "0 < (B::real)" "0 \<le> t" "0 \<le> x2" and key: "x1 + x2\<^sup>2 / (2 * B) \<le> S"
  shows "x2 * t - B * t\<^sup>2 / 2 + x1 + (x2 - B * t)\<^sup>2 / (2 * B) \<le> S" (is "?lhs \<le> S")
proof-
  have "?lhs = 2 * B * x2 * t/(2*B) - B^2 * t\<^sup>2 / (2*B) + (2 * B * x1)/(2*B) + (x2 - B * t)\<^sup>2 / (2 * B)"
    using \<open>0 < B\<close> by (auto simp: power2_eq_square)
  also have "(x2 - B * t)\<^sup>2 / (2 * B) = x2^2/(2*B) + B^2 * t^2/(2*B) - 2*x2*B*t/(2*B)"
    using \<open>0 < B\<close> by (auto simp: power2_diff field_simps)
  ultimately have "?lhs = x1 + x2\<^sup>2 / (2 * B)"
    using \<open>0 < B\<close> by auto
  thus "?lhs \<le> S"
    using key by simp
qed

lemma STTexample5_arith:
  assumes "0 < A" "0 < B" "0 < \<epsilon>" "0 \<le> x2" "0 \<le> (t::real)" 
    and key: "x1 + x2\<^sup>2 / (2 * B) + (A * (A * \<epsilon>\<^sup>2 / 2 + \<epsilon> * x2) / B + (A * \<epsilon>\<^sup>2 / 2 + \<epsilon> * x2)) \<le> S" (is "?k3 \<le> S")
    and ghyp: "\<forall>\<tau>. 0 \<le> \<tau> \<and> \<tau> \<le> t \<longrightarrow> \<tau> \<le> \<epsilon>"
  shows "A * t\<^sup>2 / 2 + x2 * t + x1 + (A * t + x2)\<^sup>2 / (2 * B) \<le> S" (is "?k0 \<le> S")
proof-
  have "t \<le> \<epsilon>"
    using ghyp \<open>0 \<le> t\<close> by auto
  hence "A*t^2/2 + t*x2 \<le> A*\<epsilon>^2/2 + \<epsilon>*x2"
    using \<open>0 \<le> t\<close> \<open>0 < A\<close> \<open>0 \<le> x2\<close>
    by (smt (verit, ccfv_SIG) divide_right_mono mult_less_cancel_left mult_right_mono power_less_imp_less_base)
  hence "((A + B)/B) * (A*t^2/2 + t*x2) + x1 + x2\<^sup>2 / (2 * B) \<le>
    x1 + x2\<^sup>2 / (2 * B) + ((A + B)/B) * (A*\<epsilon>^2/2 + \<epsilon>*x2)" (is "?k1 \<le> ?k2")
    using \<open>0 < B\<close> \<open>0 < A\<close> by (smt (verit, ccfv_SIG) divide_pos_pos mult_less_cancel_left) 
  moreover have "?k0 = ?k1"
    using \<open>0 < B\<close> \<open>0 < A\<close> by (auto simp: field_simps power2_sum power2_eq_square)
  moreover have "?k2 = ?k3"
    using \<open>0 < B\<close> \<open>0 < A\<close> by (auto simp: field_simps power2_sum power2_eq_square)
  ultimately show "?k0 \<le> S"
    using key by linarith
qed

lemma STTexample6_arith:
  assumes "0 < A" "0 < B" "0 < \<epsilon>" "0 \<le> x2" "0 \<le> (t::real)" "- B \<le> k" "k \<le> A"
    and key: "x1 + x2\<^sup>2 / (2 * B) + (A * (A * \<epsilon>\<^sup>2 / 2 + \<epsilon> * x2) / B + (A * \<epsilon>\<^sup>2 / 2 + \<epsilon> * x2)) \<le> S" (is "?k3 \<le> S")
    and ghyp: "\<forall>\<tau>. 0 \<le> \<tau> \<and> \<tau> \<le> t \<longrightarrow> 0 \<le> k * \<tau> + x2 \<and> \<tau> \<le> \<epsilon>"
  shows "k * t\<^sup>2 / 2 + x2 * t + x1 + (k * t + x2)\<^sup>2 / (2 * B) \<le> S" (is "?k0 \<le> S")
proof-
  have "0 \<le> k * t + x2 + x2"
    using ghyp \<open>0 \<le> x2\<close> \<open>0 \<le> t\<close> by force
  hence "0 \<le> (k * t + 2 * x2) * t/2"
    by (metis assms(5) divide_nonneg_pos is_num_normalize(1) mult_2 mult_sign_intros(1) rel_simps(51))
  hence f1: "0 \<le> k*t^2/2 + t*x2"
    by (auto simp: field_simps power2_eq_square)
  have f2: "0 \<le> (k + B) / B" "(k + B) / B \<le> (A + B) / B"
    using \<open>0 < A\<close> \<open>0 < B\<close> \<open>- B \<le> k\<close> \<open>k \<le> A\<close> divide_le_cancel by (auto, fastforce)
  have "t \<le> \<epsilon>"
    using ghyp \<open>0 \<le> t\<close> by auto
  hence "k*t^2/2 + t*x2 \<le> A*t^2/2 + t*x2"
    using \<open>k \<le> A\<close> by (auto simp: mult_right_mono)
  also have f3: "... \<le> A*\<epsilon>^2/2 + \<epsilon>*x2"
    using \<open>0 \<le> t\<close> \<open>0 < A\<close> \<open>0 \<le> x2\<close> \<open>t \<le> \<epsilon>\<close>
    by (smt field_sum_of_halves mult_right_mono power_less_imp_less_base mult_less_cancel_left)
  finally have "k*t^2/2 + t*x2 \<le> A*\<epsilon>^2/2 + \<epsilon>*x2" .
  hence "((k + B)/B) * (k*t^2/2 + t*x2) \<le> ((A + B)/B) * (A*\<epsilon>^2/2 + \<epsilon>*x2)"
    using f1 f2 \<open>k \<le> A\<close> apply(rule_tac b="((A + B)/B) * (A*t^2/2 + t*x2)" in order.trans)
     apply (rule mult_mono', simp, simp, simp add: mult_right_mono, simp, simp)
    by (metis f3 add_sign_intros(4) assms(1,2) less_eq_real_def mult_zero_left 
        mult_less_cancel_left zero_compare_simps(5))
  hence "((k + B)/B) * (k*t^2/2 + t*x2) + x1 + x2\<^sup>2 / (2 * B) \<le>
    x1 + x2\<^sup>2 / (2 * B) + ((A + B)/B) * (A*\<epsilon>^2/2 + \<epsilon>*x2)" (is "?k1 \<le> ?k2")
    using \<open>0 < B\<close> \<open>0 < A\<close> by (smt mult_less_cancel_left zero_compare_simps(9))
  moreover have "?k0 = ?k1"
    using \<open>0 < B\<close> \<open>0 < A\<close> by (auto simp: field_simps power2_sum power2_eq_square)
  moreover have "?k2 = ?k3"
    using \<open>0 < B\<close> \<open>0 < A\<close> by (auto simp: field_simps power2_sum power2_eq_square)
  ultimately show "?k0 \<le> S"
    using key by linarith
qed

lemma STTexample7_arith1:
  assumes "(0::real) < A" "0 < b" "0 < \<epsilon>" "0 \<le> v" "0 \<le> t" "k \<le> A"
    and "x + v\<^sup>2 / (2 * b) + (A * (A * \<epsilon>\<^sup>2 / 2 + \<epsilon> * v) / b + (A * \<epsilon>\<^sup>2 / 2 + \<epsilon> * v)) \<le> S" (is "?expr1 \<le> S")
    and guard: "\<forall>\<tau>. 0 \<le> \<tau> \<and> \<tau> \<le> t \<longrightarrow> 0 \<le> k * \<tau> + v \<and> \<tau> \<le> \<epsilon>"
  shows "k * t\<^sup>2 / 2 + v * t + x + (k * t + v)\<^sup>2 / (2 * b) \<le> S" (is "?lhs \<le> S")
proof-
  have obs1: "?lhs*(2*b) = k*t\<^sup>2*b + 2 * v * t*b + 2*x*b + (k*t+v)\<^sup>2" (is "_ = ?expr2 k t")
    using \<open>0 < b\<close> by (simp add: field_simps)
  have "?expr2 A \<epsilon> = ?expr1*(2*b)"
    using \<open>0 < b\<close> by (simp add: field_simps power2_eq_square)
  also have "... \<le> S*(2*b)"
    using \<open>?expr1 \<le> S\<close> \<open>0 < b\<close> by force 
  finally have obs2: "?expr2 A \<epsilon> \<le> S*(2*b)" .
  have "t \<le> \<epsilon>"
    using guard \<open>0 \<le> t\<close> by auto
  hence "t\<^sup>2 \<le> \<epsilon>\<^sup>2" "k * t + v \<le> A * \<epsilon> + v"
    using \<open>k \<le> A\<close> \<open>0 < A\<close> power_mono[OF \<open>t \<le> \<epsilon>\<close> \<open>0 \<le> t\<close>, of 2] 
    by auto (meson \<open>0 \<le> t\<close> less_eq_real_def mult_mono)
  hence "k * t\<^sup>2 * b \<le> A * \<epsilon>\<^sup>2 * b" "2 * v * t * b \<le> 2 * v * \<epsilon> * b"
    using \<open>t \<le> \<epsilon>\<close> \<open>0 < b\<close> \<open>k \<le> A\<close> \<open>0 \<le> v\<close> 
    by (auto simp: mult_left_mono) (meson \<open>0 < A\<close> less_eq_real_def mult_mono zero_compare_simps(12))
  hence "?expr2 k t \<le> ?expr2 A \<epsilon>"
    by (smt \<open>k * t + v \<le> A * \<epsilon> + v\<close> ends_in_segment(2) \<open>0 \<le> t\<close> guard power_mono)
  hence "?lhs*(2*b) \<le> S*(2*b)" 
    using obs1 obs2 by simp
  thus "?lhs \<le> S"
    using \<open>0 < b\<close> by force
qed

lemma STTexample7_arith2:
  assumes "(0::real) < b" "0 \<le> v" "0 \<le> t" "k \<le> - b"
    and key: "x + v\<^sup>2 / (2 * b) \<le> S" 
    and guard: "\<forall>\<tau>. 0 \<le> \<tau> \<and> \<tau> \<le> t \<longrightarrow> 0 \<le> k * \<tau> + v \<and> \<tau> \<le> \<epsilon>"
  shows "k * t\<^sup>2 / 2 + v * t + x + (k * t + v)\<^sup>2 / (2 * b) \<le> S" (is "?lhs \<le> S")
proof-
  have obs: "1 + k/b \<le> 0" "k * t + v \<ge> 0"
    using \<open>k \<le> - b\<close> \<open>0 < b\<close> guard \<open>0 \<le> t\<close> by (auto simp: mult_imp_div_pos_le real_add_le_0_iff)
  have "?lhs = (k * t + v + v)*t/2 * (1 + k/b) + x + v\<^sup>2 / (2 * b)"
    using \<open>0 < b\<close> by (auto simp: field_simps power2_eq_square)
  also have "... \<le> x + v\<^sup>2 / (2 * b)"
    using obs \<open>0 \<le> t\<close> \<open>0 \<le> v\<close>
    by (smt mult_nonneg_nonneg zero_compare_simps(11) zero_compare_simps(6))
  also have "... \<le> S"
    using key .
  finally show ?thesis .
qed

lemma STTexample9a_arith:
  "(10*x-10*r) * v/4 + v\<^sup>2/2 + (x-r)*(2*r-2*x-3 * v)/2 + v * (2*r-2*x-3 * v)/2 \<le> (0::real)" 
  (is "?t1 + ?t2 + ?t3 + ?t4 \<le> 0")
proof-
  have "?t1 = 5 * (x-r) * v/2"
    by auto
  moreover have "?t3 = -((x - r)^2) - 3 * v * (x-r)/2"
    by (auto simp: field_simps power2_diff power2_eq_square)
  moreover have "?t4 = - 2 * (x - r) * v/2 - 3 * v^2/2"
    by (auto simp: field_simps power2_diff power2_eq_square)
  ultimately have "?t1 + ?t3 + ?t4 = -((x - r)^2) - 3 * v^2/2"
    by (auto simp: field_simps)
  hence "?t1 + ?t2 + ?t3 + ?t4 = -((x - r)^2) - v^2"
    by auto
  also have "... \<le> 0"
    by auto
  finally show ?thesis .
qed

lemma LICSexample4a_arith:
  assumes "(0::real) \<le> A" "0 < b" "v\<^sup>2 \<le> 2 * b * (m - x)" "0 \<le> t"
      and guard: "\<forall>\<tau>. 0 \<le> \<tau> \<and> \<tau> \<le> t \<longrightarrow> 0 \<le> A * \<tau> + v \<and> \<tau> \<le> \<epsilon>"
      and key: "v\<^sup>2 + (A * (A * \<epsilon>\<^sup>2 + 2 * \<epsilon> * v) + b * (A * \<epsilon>\<^sup>2 + 2 * \<epsilon> * v)) \<le> 2 * b * (m - x)" (is "?expr1 \<le> _")
    shows "(A * t + v)\<^sup>2 \<le> 2 * b * (m - (A * t\<^sup>2 / 2 + v * t + x))"
proof-
  have "t \<le> \<epsilon>" "0 \<le> v"
    using guard \<open>0 \<le> t\<close> by (force, erule_tac x=0 in allE, auto)
  hence "A * t\<^sup>2 + 2 * t * v \<le> A * \<epsilon>\<^sup>2 + 2 * \<epsilon> * v"
    using \<open>0 \<le> A\<close> \<open>0 \<le> t\<close>
    by (smt mult_less_cancel_left_disj mult_right_mono power_less_imp_less_base) 
  hence "v\<^sup>2 + (A + b) * (A * t\<^sup>2 + 2 * t * v) \<le> v\<^sup>2 + (A + b) * (A * \<epsilon>\<^sup>2 + 2 * \<epsilon> * v)"
    using \<open>0 \<le> A\<close> \<open>0 < b\<close> by (smt mult_left_mono) 
  also have "... = ?expr1"
    by (auto simp: field_simps)
  finally have "v\<^sup>2 + (A + b) * (A * t\<^sup>2 + 2 * t * v) \<le> 2 * b * (m - x)"
    using key by auto
  thus ?thesis
    by (auto simp: field_simps power2_eq_square)
qed

lemma LICSexample4c_arith1:
  assumes "v\<^sup>2 \<le> 2 * b * (m - x)" "0 \<le> t" "A \<ge> 0" "b > 0"
    and key: "v\<^sup>2 + (A * (A * \<epsilon>\<^sup>2 + 2 * \<epsilon> * v) + b * (A * \<epsilon>\<^sup>2 + 2 * \<epsilon> * v)) \<le> 2 * b * (m - x)"
    and guard: "\<forall>\<tau>. 0 \<le> \<tau> \<and> \<tau> \<le> t \<longrightarrow> (0::real) \<le> A * \<tau> + v \<and> \<tau> \<le> \<epsilon>"
  shows "(A * t + v)\<^sup>2 \<le> 2 * b * (m - (A * t\<^sup>2 / 2 + v * t + x))" (is "_ \<le> ?rhs")
proof-
  have "t \<le> \<epsilon>" "0 \<le> \<epsilon>" "0 \<le> v"
    using guard \<open>0 \<le> t\<close> by (force, erule_tac x=0 in allE, simp, erule_tac x=0 in allE, simp)
  hence obs1: "A * t\<^sup>2 + 2 * t * v \<le> A * \<epsilon>\<^sup>2 + 2 * \<epsilon> * v"
    using \<open>A \<ge> 0\<close> \<open>0 \<le> t\<close> \<open>t \<le> \<epsilon>\<close> by (smt mult_mono power_mono zero_compare_simps(12)) 
  have obs2:"?rhs + A * b * t^2 + 2 * b * v * t = 2 * b * (m - x)"
    by (simp add: field_simps)
  have "(A * t + v)\<^sup>2 + A * b * t^2 + 2 * b * v * t = v\<^sup>2 + (A * (A * t\<^sup>2 + 2 * t * v) + b * (A * t\<^sup>2 + 2 * t * v))"
    by (simp add: field_simps power2_eq_square)
  also have "... \<le> v\<^sup>2 + (A * (A * \<epsilon>\<^sup>2 + 2 * \<epsilon> * v) + b * (A * \<epsilon>\<^sup>2 + 2 * \<epsilon> * v))"
    using obs1 \<open>A \<ge> 0\<close> \<open>b > 0\<close> by (smt mult_less_cancel_left) 
  also have "... \<le> 2 * b * (m - x)"
    using key .
  finally show ?thesis
    using obs2 by auto
qed


lemma LICSexample5_arith1:
  assumes "(0::real) < b" "0 \<le> t"
    and key: "v\<^sup>2 \<le> 2 * b * (m - x)"
  shows "v * t - b * t\<^sup>2 / 2 + x \<le> m"
proof-
  have "v\<^sup>2 \<le> 2 * b * (m - x) + (b * t - v)^2"
    using key by (simp add: add_increasing2) 
  hence "b^2 * t^2 - 2 * b * v * t \<ge> 2 * b * x - 2 * b * m"
    by (auto simp: field_simps power2_diff)
  hence "(b^2/b) * t^2 - 2 * (b/b) * v * t \<ge> 2 * (b/b) * x - 2 * (b/b) * m"
    using \<open>b > 0\<close> by (auto simp: field_simps)
  thus ?thesis
    using \<open>b > 0\<close> by (simp add: power2_eq_square)
qed

lemma LICSexample5_arith2:
  assumes "(0::real) < b" "0 \<le> v" "\<forall>t\<in>{0..}. v * t - b * t\<^sup>2 / 2 + x \<le> m"
  shows "v\<^sup>2 \<le> 2 * b * (m - x)"
proof(cases "v = 0")
  case True
  have "m - x \<ge> 0"
    using assms by (erule_tac x=0 in ballE, auto)
  thus ?thesis 
    using assms True by auto
next
  case False
  hence obs: "v > 0 \<and> (\<exists>k. k > 0 \<and> v = b * k)"
    using assms(1,2) by (metis (no_types, hide_lams) divide_pos_pos divide_self_if 
        less_eq_real_def linorder_not_le mult_1_right mult_1s(1) times_divide_eq_left) 
  {fix t::real assume "t \<ge> 0"
    hence "v * t - b * t\<^sup>2 / 2 + x \<le> m"
      using assms by auto
    hence "2 * b * v * t - b * b * t\<^sup>2 + 2 * b * x \<le> 2 * b * m"
      using \<open>b > 0\<close> by (simp add: field_simps) (metis distrib_left mult_le_cancel_left_pos) 
    hence "- b\<^sup>2 * t\<^sup>2 + 2 * b * v * t \<le> 2 * b * m - 2 * b * x"
      using \<open>b > 0\<close> by (simp add: power2_eq_square) 
    hence "v^2 \<le> 2 * b * (m - x) + (b^2 * t^2 + v^2 - 2 * b * v * t)"
      by (simp add: field_simps)
    also have "... = 2 * b * (m - x) + (b * t - v)^2"
      by (simp add: power2_diff power_mult_distrib)
    finally have "v^2 \<le> 2 * b * (m - x) + (b * t - v)^2" .}
  hence "\<forall>t\<ge>0. v\<^sup>2 \<le> 2 * b * (m - x) + (b * t - v)\<^sup>2"
    by blast
  then obtain k where "v\<^sup>2 \<le> 2 * b * (m - x) + (b * k - v)\<^sup>2 \<and> k > 0 \<and> v = b * k"
    using obs by fastforce
  then show ?thesis 
    by auto
qed

lemma LICSexample6_arith1:
  assumes "0 \<le> v" "0 < b" "0 \<le> A" "0 \<le> \<epsilon>" and guard: "\<forall>t\<in>{0..}. (\<forall>\<tau>. 0 \<le> \<tau> \<and> \<tau> \<le> t \<longrightarrow> \<tau> \<le> \<epsilon>) \<longrightarrow> (\<forall>\<tau>\<in>{0..}. 
  A * t * \<tau> + v * \<tau> - b * \<tau>\<^sup>2 / 2 + (A * t\<^sup>2 / 2 + v * t + x) \<le> (m::real))"
  shows "v\<^sup>2 + (A * (A * \<epsilon>\<^sup>2 + 2 * \<epsilon> * v) + b * (A * \<epsilon>\<^sup>2 + 2 * \<epsilon> * v)) \<le> 2 * b * (m - x)"
proof-
  {fix \<tau>::real
    assume "\<tau> \<ge> 0"
    hence "A * \<epsilon> * \<tau> + v * \<tau> - b * \<tau>\<^sup>2 / 2 + (A * \<epsilon>\<^sup>2 / 2 + v * \<epsilon> + x) \<le> m"
      using guard \<open>0 \<le> \<epsilon>\<close> apply(erule_tac x=\<epsilon> in ballE)
      by (erule impE, auto simp: closed_segment_eq_real_ivl)
    hence "2 * (A * \<epsilon> * \<tau> + v * \<tau> - b * \<tau>\<^sup>2 / 2 + (A * \<epsilon>\<^sup>2 / 2 + v * \<epsilon> + x)) * b \<le> 2 * m * b"
      using \<open>0 < b\<close> by (meson less_eq_real_def mult_left_mono mult_right_mono rel_simps(51)) 
    hence "2 * A * \<epsilon> * \<tau> * b + 2 * v * \<tau> * b - b^2 * \<tau>\<^sup>2 + b * (A * \<epsilon>\<^sup>2 + 2 * v * \<epsilon>) \<le> 2 * b * (m - x)"
      using \<open>0 < b\<close> apply(simp add: algebra_simps(17,18,19,20) add.assoc[symmetric] 
          power2_eq_square[symmetric] mult.assoc[symmetric])
      by (simp add: mult.commute mult.left_commute power2_eq_square)}
  hence "\<forall>\<tau>\<ge>0. 2 * A * \<epsilon> * \<tau> * b + 2 * v * \<tau> * b - b^2 * \<tau>\<^sup>2 + b * (A * \<epsilon>\<^sup>2 + 2 * v * \<epsilon>) \<le> 2 * b * (m - x)"
    by blast
  moreover have "2 * A * \<epsilon> * ((A*\<epsilon> + v)/b) * b + 2 * v * ((A*\<epsilon> + v)/b) * b - b^2 * ((A*\<epsilon> + v)/b)\<^sup>2 =
    2 * A * \<epsilon> * (A*\<epsilon> + v) + 2 * v * (A*\<epsilon> + v) - (A*\<epsilon> + v)\<^sup>2"
    using \<open>0 < b\<close> by (simp add: field_simps)
  moreover have "... = v\<^sup>2 + A * (A * \<epsilon>\<^sup>2 + 2 * \<epsilon> * v)"
    using \<open>0 < b\<close> by (simp add: field_simps power2_eq_square)
  moreover have "(A*\<epsilon> + v)/b \<ge> 0"
    using assms by auto
  ultimately have "v\<^sup>2 + A * (A * \<epsilon>\<^sup>2 + 2 * \<epsilon> * v) + b * (A * \<epsilon>\<^sup>2 + 2 * v * \<epsilon>) \<le> 2 * b * (m - x)"
    using assms by (erule_tac x="(A*\<epsilon> + v)/b" in allE, auto)
  thus ?thesis
    by argo
qed

lemma ETCS_arith1: 
  assumes "0 < b" "0 \<le> A" "0 \<le> v" "0 \<le> t"
    and "v\<^sup>2 / (2 * b) + (A * (A * \<epsilon>\<^sup>2 / 2 + \<epsilon> * v)/ b + (A * \<epsilon>\<^sup>2 / 2 + \<epsilon> * v)) \<le> m - x" (is "?expr1 \<le> m - x")
    and guard: "\<forall>\<tau>. 0 \<le> \<tau> \<and> \<tau> \<le> t \<longrightarrow> \<tau> \<le> \<epsilon>"
  shows "(A * t + v)\<^sup>2/(2 * b) \<le> (m::real) - (A * t\<^sup>2/2 + v * t + x)" (is "?lhs \<le> ?rhs")
proof-
  have "2*b*(v\<^sup>2/(2*b) + (A*(A*\<epsilon>\<^sup>2/2+\<epsilon>* v)/b + (A*\<epsilon>\<^sup>2/2+\<epsilon>* v))) \<le> 2*b*(m-x)" (is "?expr2 \<le> 2*b*(m-x)")
    using \<open>0 < b\<close> mult_left_mono[OF \<open>?expr1 \<le> m - x\<close>, of "2 * b"] by auto
  also have "?expr2 = v\<^sup>2 +  2 * A * (A * \<epsilon>\<^sup>2 / 2 + \<epsilon> * v) + b * A * \<epsilon>\<^sup>2 + 2 * b * \<epsilon> * v"
    using \<open>0 < b\<close> by (auto simp: field_simps)
  also have "... = v\<^sup>2 +  A^2 * \<epsilon>\<^sup>2 + 2 * A * \<epsilon> * v + b * A * \<epsilon>\<^sup>2 + 2 * b * \<epsilon> * v"
    by (auto simp: field_simps power2_eq_square)
  finally have obs: "v\<^sup>2 +  A\<^sup>2*\<epsilon>\<^sup>2 + 2*A*\<epsilon>* v + b*A*\<epsilon>\<^sup>2 + 2*b*\<epsilon>* v \<le> 2*b*(m-x)" (is "?expr3 \<epsilon> \<le> 2*b*(m-x)") .
  have "t \<le> \<epsilon>"
    using guard \<open>0 \<le> t\<close> by auto
  hence "v\<^sup>2 + A\<^sup>2 * t\<^sup>2 + b * A * t\<^sup>2 \<le> v\<^sup>2 + A\<^sup>2 * \<epsilon>\<^sup>2 + b * A * \<epsilon>\<^sup>2"
    using power_mono[OF \<open>t \<le> \<epsilon>\<close> \<open>0 \<le> t\<close>, of 2]
    by (smt assms(1,2) mult_less_cancel_left zero_compare_simps(4) zero_le_power) 
  hence "v\<^sup>2 + A\<^sup>2 * t\<^sup>2 + 2 * A * t * v + b * A * t\<^sup>2 \<le> v\<^sup>2 + A\<^sup>2 * \<epsilon>\<^sup>2 + 2 * A * \<epsilon> * v + b * A * \<epsilon>\<^sup>2"
    using assms(1,2,3,4) \<open>t \<le> \<epsilon>\<close> by (smt mult_left_mono mult_right_mono) 
  hence "?expr3 t \<le> 2 * b * (m - x)"
    using assms(1,2,3,4) \<open>t \<le> \<epsilon>\<close> obs
    by (smt (z3) mult_less_cancel_left mult_minus_right mult_right_mono_neg) 
  hence "A\<^sup>2 * t\<^sup>2 + v\<^sup>2 + 2 * A * t * v \<le> 2 * b * m - b * A * t\<^sup>2 - 2 * b * t * v - 2 * b * x"
    by (simp add: right_diff_distrib)
  hence "(A * t + v)\<^sup>2 \<le> 2 * b * m - b * A * t\<^sup>2 - 2 * b * t * v - 2 * b * x"
    unfolding cross3_simps(29)[of A t 2] power2_sum[of "A*t" v] by (simp add: mult.assoc)
  hence "?lhs \<le> (2 * b * m - b * A * t\<^sup>2 - 2 * b * t * v - 2 * b * x)/(2 * b)" (is "_ \<le> ?expr4")
    using \<open>0 < b\<close> divide_right_mono by fastforce
  also have "?expr4 = ?rhs"
    using \<open>0 < b\<close> by (auto simp: field_simps)
  finally show "?lhs \<le> ?rhs" .
qed

lemma ETCS_Prop1_arith2:
  assumes "0 \<le> v" "0 \<le> \<delta>" "0 < b" "x \<le> m" "0 \<le> (t::real)"
      and key: "v\<^sup>2 - \<delta>\<^sup>2 \<le> 2 * b * (m - x)" "m \<le> v * t - b * t\<^sup>2 / 2 + x"
      and guard: "\<forall>\<tau>\<in>{0--t}. b * \<tau> \<le> v"
    shows "v - b * t \<le> \<delta>"
proof-
  have "2 * b * (m - x) \<le> 2 * b * (v * t - b * t\<^sup>2 / 2) - v\<^sup>2 + v\<^sup>2"
    using key(2) \<open>0 < b\<close> by simp
  also have "... = v\<^sup>2 - (v - b * t)\<^sup>2"
    using \<open>0 < b\<close> by (simp add: power2_diff field_simps power2_eq_square)
  finally have "(v - b * t)\<^sup>2 \<le> \<delta>\<^sup>2"
    using key(1) by simp
  thus "v - b * t \<le> \<delta>"
    using guard \<open>0 \<le> t\<close> \<open>0 \<le> \<delta>\<close> by auto
qed

subsection \<open> Advanced \<close>

lemma has_vderiv_mono_test:
  assumes T_hyp: "is_interval T" 
    and d_hyp: "D f = f' on T"
    and xy_hyp: "x\<in>T" "y\<in>T" "x \<le> y" 
  shows "\<forall>x\<in>T. (0::real) \<le> f' x \<Longrightarrow> f x \<le> f y"
    and "\<forall>x\<in>T. f' x \<le> 0 \<Longrightarrow> f x \<ge> f y"
proof-
  have "{x..y} \<subseteq> T"
    using T_hyp xy_hyp by (meson atLeastAtMost_iff mem_is_interval_1_I subsetI) 
  hence "D f = f' on {x..y}"
    using has_vderiv_on_subset[OF d_hyp(1)] by blast
  hence "(\<And>t. x \<le> t \<Longrightarrow> t \<le> y \<Longrightarrow> D f \<mapsto> (\<lambda>\<tau>. \<tau> *\<^sub>R f' t) at t within {x..y})"
    unfolding has_vderiv_on_def has_vector_derivative_def by auto
  then obtain c where c_hyp: "c \<in> {x..y} \<and> f y - f x = (y - x) *\<^sub>R f' c"
    using mvt_very_simple[OF xy_hyp(3), of f "(\<lambda>t \<tau>. \<tau> *\<^sub>R f' t)"] by blast
  hence mvt_hyp: "f x = f y - f' c * (y - x)"
    by (simp add: mult.commute)
  also have "\<forall>x\<in>T. 0 \<le> f' x \<Longrightarrow> ... \<le> f y"
    using xy_hyp d_hyp c_hyp \<open>{x..y} \<subseteq> T\<close> by auto
  finally show "\<forall>x\<in>T. 0 \<le> f' x \<Longrightarrow> f x \<le> f y" .
  have "\<forall>x\<in>T. f' x \<le> 0 \<Longrightarrow> f y - f' c * (y - x) \<ge> f y"
    using xy_hyp d_hyp c_hyp \<open>{x..y} \<subseteq> T\<close> by (auto simp: mult_le_0_iff)
  thus "\<forall>x\<in>T. f' x \<le> 0 \<Longrightarrow> f x \<ge> f y"
    using mvt_hyp by auto
qed

lemma continuous_on_ge_ball_ge: 
  "continuous_on T f \<Longrightarrow> x \<in> T \<Longrightarrow> f x > (k::real) \<Longrightarrow> \<exists>\<epsilon>>0. \<forall>y\<in>ball x \<epsilon> \<inter> T. f y > k"
  unfolding continuous_on_iff apply(erule_tac x=x in ballE; clarsimp?)
  apply(erule_tac x="f x - k" in allE, clarsimp simp: dist_norm)
  apply(rename_tac \<delta>, rule_tac x=\<delta> in exI, clarsimp)
  apply(erule_tac x=y in ballE; clarsimp?)
  by (subst (asm) abs_le_eq, simp_all add: dist_commute)

lemma current_vderiv_ge_always_ge:
  fixes c::real
  assumes init: "c < x t\<^sub>0" and ode: "D x = x' on {t\<^sub>0..}" 
    and dhyp: "x' = (\<lambda>t. g (x t))" "\<forall>x\<ge>c. g x \<ge> 0"
  shows "\<forall>t\<ge>t\<^sub>0. x t > c"
proof-
  have cont: "continuous_on {t\<^sub>0..} x"
    using vderiv_on_continuous_on[OF ode] .
  {assume "\<exists>t\<ge>t\<^sub>0. x t \<le> c"
    hence inf: "{t. t > t\<^sub>0 \<and> x t \<le> c} \<noteq> {}" "bdd_below {t. t > t\<^sub>0 \<and> x t \<le> c}"
      using init less_eq_real_def unfolding bdd_below_def by force (rule_tac x=t\<^sub>0 in exI, simp)
    define t\<^sub>1 where t1_hyp: "t\<^sub>1 = Inf {t. t > t\<^sub>0 \<and> x t \<le> c}"
    hence "t\<^sub>0 \<le> t\<^sub>1"  
      using le_cInf_iff[OF inf, of t\<^sub>0] by auto
    have "x t\<^sub>1 \<ge> c"
    proof-
      {assume "x t\<^sub>1 < c"
        hence obs: "x t\<^sub>1 \<le> c" "x t\<^sub>0 \<ge> c" "t\<^sub>1 \<noteq> t\<^sub>0"
          using init by auto
        hence "t\<^sub>1 > t\<^sub>0"
          using \<open>t\<^sub>0 \<le> t\<^sub>1\<close> by auto
        then obtain k where k2_hyp: "k \<ge> t\<^sub>0 \<and> k \<le> t\<^sub>1 \<and> x k = c"
          using IVT2'[of "\<lambda>t. x t", OF obs(1,2) _ continuous_on_subset[OF cont]] by auto
        hence "t\<^sub>0 < k" "k < t\<^sub>1"
          using \<open>x t\<^sub>1 < c\<close> less_eq_real_def init by auto
        also have "t\<^sub>1 \<le> k"
          using cInf_lower[OF _ inf(2)] k2_hyp calculation unfolding t1_hyp by auto
        ultimately have False
          by simp}
      thus "x t\<^sub>1 \<ge> c"
        by fastforce
    qed
    hence obs: "\<forall>t\<in>{t\<^sub>0..<t\<^sub>1}. x t > c"
    proof-
      {assume "\<exists>t\<in>{t\<^sub>0..<t\<^sub>1}. x t \<le> c"
        then obtain k where k2_hyp: "k \<ge> t\<^sub>0 \<and> k < t\<^sub>1 \<and> x k \<le> c"
          by auto
        hence "k > t\<^sub>0"
          using \<open>x t\<^sub>0 > c\<close> less_eq_real_def by auto
        hence "t\<^sub>1 \<le> k"
          using cInf_lower[OF _ inf(2)] k2_hyp unfolding t1_hyp by auto
        hence "False"
          using k2_hyp by auto}
      thus "\<forall>t\<in>{t\<^sub>0..<t\<^sub>1}. x t > c"
        by force
    qed
    hence "\<forall>t\<in>{t\<^sub>0..t\<^sub>1}. x' t \<ge> 0"
      using \<open>x t\<^sub>1 \<ge> c\<close> dhyp(2) less_eq_real_def 
      unfolding dhyp by (metis atLeastAtMost_iff atLeastLessThan_iff) 
    hence "x t\<^sub>0 \<le> x t\<^sub>1"
      apply(rule_tac f="\<lambda>t. x t" and T="{t\<^sub>0..t\<^sub>1}" in has_vderiv_mono_test(1); clarsimp)
      using has_vderiv_on_subset[OF ode] apply force
      using \<open>t\<^sub>0  \<le> t\<^sub>1\<close>  by (auto simp: less_eq_real_def)
    hence "c < x t\<^sub>1"
      using \<open>x t\<^sub>1 \<ge> c\<close> init by auto
    then obtain \<epsilon> where eps_hyp: "\<epsilon> > 0 \<and> (\<forall>t\<in>ball t\<^sub>1 \<epsilon> \<inter> {t\<^sub>0..}. c < x t)"
      using continuous_on_ge_ball_ge[of _ "\<lambda>t. x t", OF cont _ \<open>c < x t\<^sub>1\<close>] \<open>t\<^sub>0  \<le> t\<^sub>1\<close> by auto
    hence "\<forall>t\<in>{t\<^sub>0..<t\<^sub>1+\<epsilon>}. c < x t"
      using obs \<open>t\<^sub>0 \<le> t\<^sub>1\<close> ball_eq_greaterThanLessThan by auto
    hence "\<forall>t\<in>{t. t > t\<^sub>0 \<and> x t \<le> c}. t\<^sub>1+\<epsilon> \<le> t"
      by (metis (mono_tags, lifting) atLeastLessThan_iff less_eq_real_def mem_Collect_eq not_le)
    hence "t\<^sub>1+\<epsilon> \<le> t\<^sub>1"
      using le_cInf_iff[OF inf] unfolding t1_hyp by simp
    hence False
      using eps_hyp by auto}
  thus "\<forall>t\<ge>t\<^sub>0. c < x t"
    by fastforce
qed

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