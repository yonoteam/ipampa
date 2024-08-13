(*<*)
theory CNF
  imports Main
begin
(*>*)


datatype 'a formula = 
  is_Atom: Atom "'a"
  | is_Neg: Neg "'a formula" 
  | is_Disj: Or "'a formula" "'a formula" 
  | is_Conj: And "'a formula" "'a formula"

primrec sat :: "('a \<Rightarrow> bool) \<Rightarrow> 'a formula \<Rightarrow> bool"
  where "sat v (Atom p) = v p"
  | "sat v (Neg \<phi>) = (\<not> sat v \<phi>)"
  | "sat v (Or \<phi> \<psi>) = (sat v \<phi> \<or> sat v \<psi>)"
  | "sat v (And \<phi> \<psi>) = (sat v \<phi> \<and> sat v \<psi>)"

primrec subformula :: "'a formula \<Rightarrow> 'a formula \<Rightarrow> bool"
  where "subformula \<phi> (Atom p) = (\<phi> = Atom p)"
  | "subformula \<phi> (Neg \<psi>) = (\<phi> = Neg \<psi> \<or> subformula \<phi> \<psi>)"
  | "subformula \<phi> (Or \<psi> \<gamma>) = (\<phi> = Or \<psi> \<gamma> \<or> subformula \<phi> \<psi> \<or> subformula \<phi> \<gamma>)"
  | "subformula \<phi> (And \<psi> \<gamma>) = (\<phi> = And \<psi> \<gamma> \<or> subformula \<phi> \<psi> \<or> subformula \<phi> \<gamma>)"

bundle syntax_no_notation
begin

no_notation Atom ("@\<^sub>F_" [85] 85)
     and formula.Neg ("\<not>\<^sub>F _" [82] 82)
     and formula.And (infixr "\<and>\<^sub>F" 80)
     and formula.Or (infixr "\<or>\<^sub>F" 80)
     and sat ("_ \<Turnstile> _" [55, 55] 55)

end


bundle syntax_notation
begin

notation Atom ("@\<^sub>F_" [85] 85)
     and formula.Neg ("\<not>\<^sub>F _" [82] 82)
     and formula.And (infixr "\<and>\<^sub>F" 80)
     and formula.Or (infixr "\<or>\<^sub>F" 80)
     and sat ("_ \<Turnstile> _" [55, 55] 55)

end

unbundle syntax_notation

fun is_literal :: "'a formula \<Rightarrow> bool"
  where "is_literal (@\<^sub>F p) = True"
  | "is_literal (\<not>\<^sub>F (@\<^sub>F p)) = True"
  | "is_literal _ = False"

lemma is_literal_iff: "is_literal \<phi> \<longleftrightarrow> (\<exists>p. \<phi> = @\<^sub>F p \<or> \<phi> = \<not>\<^sub>F @\<^sub>F p)"
  by (cases \<phi> rule: is_literal.cases, simp_all)

lemma is_literal_NegD: "is_literal (\<not>\<^sub>F \<phi>) \<Longrightarrow> \<exists>p. \<phi> = @\<^sub>F p"
  by (clarsimp simp: is_literal_iff)

primrec is_clause :: "'a formula \<Rightarrow> bool"
  where "is_clause (@\<^sub>F p) = True"
  | "is_clause (\<not>\<^sub>F \<phi>) = is_literal (\<not>\<^sub>F \<phi>)"
  | "is_clause (\<phi> \<or>\<^sub>F \<psi>) = (is_clause \<phi> \<and> is_clause \<psi>)"
  | "is_clause (\<phi> \<and>\<^sub>F \<psi>) = False"

lemma is_clause_iff_rec: 
  "is_clause \<phi> \<longleftrightarrow> (is_literal \<phi> \<or> (\<exists>\<psi> \<gamma>. is_clause \<psi> \<and> is_clause \<gamma> \<and> \<phi> = \<psi> \<or>\<^sub>F \<gamma>))"
  by (induct \<phi>, simp_all)

fun is_CNF :: "'a formula \<Rightarrow> bool"
  where "is_CNF (@\<^sub>F p) = True"
  | "is_CNF (\<not>\<^sub>F (@\<^sub>F p)) = True"
  | "is_CNF (\<not>\<^sub>F \<phi>) = False"
  | "is_CNF (\<phi> \<or>\<^sub>F \<psi>) = (is_clause \<phi> \<and> is_clause \<psi>)"
  | "is_CNF (\<phi> \<and>\<^sub>F \<psi>) = (is_CNF \<phi> \<and> is_CNF \<psi>)"

lemma is_CNF_iff_rec: 
  "is_CNF \<phi> \<longleftrightarrow> (is_clause \<phi> \<or> (\<exists>\<psi> \<gamma>. is_CNF \<psi> \<and> is_CNF \<gamma> \<and> \<phi> = \<psi> \<and>\<^sub>F \<gamma>))"
  by (induct \<phi> rule: is_CNF.induct, simp_all)

lemmas is_CNFD = iffD1[OF is_CNF_iff_rec] 
  and is_CNFI = iffD2[OF is_CNF_iff_rec]

lemma clause_is_CNF: "is_clause \<phi> \<Longrightarrow> is_CNF \<phi>"
  by (induct \<phi> rule: is_CNF.induct, auto)

lemma is_CNF_NegD: "is_CNF (\<not>\<^sub>F \<phi>) \<Longrightarrow> \<exists>p. \<phi> = @\<^sub>F p"
  by (cases \<phi> rule: is_CNF.cases, simp_all)

fun push_neg :: "'a formula \<Rightarrow> 'a formula"
  where "push_neg (@\<^sub>F p) = @\<^sub>F p"
  | "push_neg (\<not>\<^sub>F (@\<^sub>F p)) = \<not>\<^sub>F (@\<^sub>F p)"
  | "push_neg (\<not>\<^sub>F (\<not>\<^sub>F \<phi>)) = push_neg \<phi>"
  | "push_neg (\<not>\<^sub>F (\<phi> \<or>\<^sub>F \<psi>)) = (push_neg (\<not>\<^sub>F \<phi>)) \<and>\<^sub>F (push_neg (\<not>\<^sub>F \<psi>))"
  | "push_neg (\<not>\<^sub>F (\<phi> \<and>\<^sub>F \<psi>)) = (push_neg (\<not>\<^sub>F \<phi>)) \<or>\<^sub>F (push_neg (\<not>\<^sub>F \<psi>))"
  | "push_neg (\<phi> \<or>\<^sub>F \<psi>) = (push_neg \<phi>) \<or>\<^sub>F (push_neg \<psi>)"
  | "push_neg (\<phi> \<and>\<^sub>F \<psi>) = (push_neg \<phi>) \<and>\<^sub>F (push_neg \<psi>)"

lemma sat_push_neg_iff: "v \<Turnstile> push_neg \<phi> \<longleftrightarrow> v \<Turnstile> \<phi>"
  by (induct \<phi> rule: push_neg.induct, simp_all)

lemma NNF_push_neg: 
  "subformula \<psi> (push_neg \<phi>) \<Longrightarrow> is_Neg \<psi> \<Longrightarrow> is_literal \<psi>"
  by (induct \<phi> rule: push_neg.induct)
    (auto simp add: is_literal_iff)

fun distrib_law :: "'a formula \<Rightarrow> 'a formula \<Rightarrow> 'a formula"
  where "distrib_law \<phi> \<psi> = 
    (case \<phi> of 
      \<phi>\<^sub>1 \<and>\<^sub>F \<phi>\<^sub>2 \<Rightarrow> (distrib_law \<phi>\<^sub>1 \<psi>) \<and>\<^sub>F (distrib_law \<phi>\<^sub>2 \<psi>)
      | _ \<Rightarrow> (case \<psi> of 
          \<psi>\<^sub>1 \<and>\<^sub>F \<psi>\<^sub>2 \<Rightarrow> (distrib_law \<phi> \<psi>\<^sub>1) \<and>\<^sub>F (distrib_law \<phi> \<psi>\<^sub>2)
          | _ \<Rightarrow> \<phi> \<or>\<^sub>F \<psi>))"

lemma distrib_law__clauses:
  assumes "is_clause \<phi>"
    and "is_clause \<psi>"
  shows "is_clause (distrib_law \<phi> \<psi>)"
  using assms 
  by - (induct \<phi>; induct \<psi>; force simp add: is_literal_iff)

lemma distrib_law_CNF_clause:
  assumes "is_CNF \<phi>"
    and "is_clause \<psi>"
  shows "is_CNF (distrib_law \<phi> \<psi>)"
    and "is_CNF (distrib_law \<psi> \<phi>)"
  using assms 
  by - (induct \<phi>; induct \<psi>; force simp add: is_literal_iff dest: is_CNF_NegD)+

lemma is_CNF_distrib_law:
  assumes "is_CNF \<phi>"
    and "is_CNF \<psi>"
  shows "is_CNF (distrib_law \<phi> \<psi>)"
  using assms
  by (induct \<phi>; induct \<psi>; clarsimp simp add: is_literal_iff dest!: is_CNF_NegD)
    (metis distrib_law.simps distrib_law_CNF_clause(2))

lemma sat_distrib_law1: 
  "is_clause \<phi> \<Longrightarrow> is_clause \<psi> \<Longrightarrow> v \<Turnstile> distrib_law \<phi> \<psi> \<longleftrightarrow> v \<Turnstile> \<phi> \<or>\<^sub>F \<psi>"
  by (induct \<phi>; induct \<psi>; clarsimp)

lemma sat_distrib_law2: 
  "is_clause \<phi> \<Longrightarrow> is_CNF \<psi> \<Longrightarrow> \<psi> = \<psi>\<^sub>1 \<and>\<^sub>F \<psi>\<^sub>2 \<Longrightarrow> v \<Turnstile> distrib_law \<phi> \<psi> \<longleftrightarrow> v \<Turnstile> (\<phi> \<or>\<^sub>F \<psi>\<^sub>1) \<and>\<^sub>F (\<phi> \<or>\<^sub>F \<psi>\<^sub>2)"
  apply (induct \<phi>; induct \<psi> arbitrary: \<psi>\<^sub>1 \<psi>\<^sub>2; clarsimp simp: is_literal_iff)
  oops

fun to_CNF :: "'a formula \<Rightarrow> 'a formula"
  where "to_CNF (\<phi> \<and>\<^sub>F \<psi>) = to_CNF \<phi> \<and>\<^sub>F to_CNF \<psi>"
  | "to_CNF (\<phi> \<or>\<^sub>F \<psi>) = distrib_law (to_CNF \<phi>) (to_CNF \<psi>)"
  | "to_CNF \<phi> = \<phi>"

lemma "is_CNF (to_CNF (push_neg \<phi>))"
  by (induct \<phi> rule: push_neg.induct)
    (simp_all add: is_CNF_distrib_law 
      del: distrib_law.simps)

value "is_CNF (\<not>\<^sub>F ((@\<^sub>Fp \<and>\<^sub>F @\<^sub>Fq) \<and>\<^sub>F \<not>\<^sub>F @\<^sub>Fr))"

value "to_CNF (push_neg (\<not>\<^sub>F ((@\<^sub>Fp \<and>\<^sub>F @\<^sub>Fq) \<and>\<^sub>F \<not>\<^sub>F @\<^sub>Fr)))"



(*>*)
end
(*<*)
