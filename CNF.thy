(*<*)
theory Syntax
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

lemma sat_push_neg_iff: "sat v (push_neg \<phi>) \<longleftrightarrow> sat v \<phi>"
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

fun to_CNF :: "'a formula \<Rightarrow> 'a formula"
  where "to_CNF (\<phi> \<and>\<^sub>F \<psi>) = to_CNF \<phi> \<and>\<^sub>F to_CNF \<psi>"
  | "to_CNF (\<phi> \<or>\<^sub>F \<psi>) = distrib_law (to_CNF \<phi>) (to_CNF \<psi>)"
  | "to_CNF \<phi> = \<phi>"

lemma "is_CNF (to_CNF (push_neg \<phi>))"
  by (induct \<phi> rule: push_neg.induct)
    (simp_all add: is_CNF_distrib_law 
      del: distrib_law.simps)

(******************************************************)

fun distrib_conj :: "'a formula \<Rightarrow> 'a formula"
  where "distrib_conj (@\<^sub>F p) = @\<^sub>F p"
  | "distrib_conj (\<not>\<^sub>F \<phi>) = \<not>\<^sub>F (distrib_conj \<phi>)"
  | "distrib_conj (\<phi> \<or>\<^sub>F \<psi>) = Or (distrib_conj \<phi>) (distrib_conj \<psi>)"
  | "distrib_conj (And (\<phi> \<or>\<^sub>F \<psi>) \<gamma>) = (let \<gamma>' = distrib_conj \<gamma> in 
      Or (And (distrib_conj \<phi>) \<gamma>') (And (distrib_conj \<psi>) \<gamma>'))"
  | "distrib_conj (And \<phi> (Or \<psi> \<gamma>)) = (let \<phi>' = distrib_conj \<phi> in 
      Or (And \<phi>' (distrib_conj \<psi>)) (And \<phi>' (distrib_conj \<gamma>)))"
  | "distrib_conj (\<phi> \<and>\<^sub>F \<psi>) = And (distrib_conj \<phi>) (distrib_conj \<psi>)"

lemma correct_distrib_conj: "sat v (distrib_conj \<phi>) \<longleftrightarrow> sat v \<phi>"
  by (induct \<phi> rule: distrib_conj.induct, auto simp: Let_def)

fun distrib_disj :: "'a formula \<Rightarrow> 'a formula"
  where "distrib_disj (@\<^sub>F p) = @\<^sub>F p"
  |"distrib_disj (\<not>\<^sub>F \<phi>) = \<not>\<^sub>F (distrib_disj \<phi>)"
  |"distrib_disj (And \<phi> \<psi>) = And (distrib_disj \<phi>) (distrib_disj \<psi>)"
  |"distrib_disj (Or (And \<phi> \<psi>) \<gamma>) = (let \<gamma>' = distrib_disj \<gamma> in 
      And (Or (distrib_disj \<phi>) \<gamma>') (Or (distrib_disj \<psi>) \<gamma>'))"
  |"distrib_disj (Or \<phi> (And \<psi> \<gamma>)) = (let \<phi>' = distrib_disj \<phi> in 
      And (Or \<phi>' (distrib_disj \<psi>)) (Or \<phi>' (distrib_disj \<gamma>)))"
  |"distrib_disj (Or \<phi> \<psi>) = Or (distrib_disj \<phi>) (distrib_disj \<psi>)"

lemma correct_distrib_disj: "sat v (distrib_disj \<phi>) \<longleftrightarrow> sat v \<phi>"
  by (induct \<phi> rule: distrib_disj.induct, auto simp: Let_def)

lemma is_clause_distrib_disjI: "is_clause \<phi> \<Longrightarrow> is_clause (distrib_disj \<phi>)"
  by (induct \<phi> rule: distrib_disj.induct, auto simp: is_literal_iff)

lemma is_CNF_distrib_disjI: "is_CNF \<phi> \<Longrightarrow> is_CNF (distrib_disj \<phi>)"
  by (induct \<phi> rule: distrib_disj.induct)
    (auto simp: is_literal_iff intro!: is_clause_distrib_disjI 
      dest: is_CNF_NegD)

lemma is_CNF_compow_distrib_disjI: 
  "m \<le> n \<Longrightarrow> is_CNF ((distrib_disj^^m) \<phi>) \<Longrightarrow> is_CNF ((distrib_disj^^n) \<phi>)"
  using is_CNF_distrib_disjI le_Suc_eq
  by (induct n, auto)

lemma compow_distrib_disj_And[simp]:
  "(distrib_disj^^n) (\<phi> \<and>\<^sub>F \<psi>) = (distrib_disj^^n) \<phi> \<and>\<^sub>F (distrib_disj^^n) \<psi>"
  by (induct n, simp_all)

lemma "\<exists>n. is_CNF ((distrib_disj ^^ n) (push_neg \<phi>))"
proof (induct \<phi> rule: push_neg.induct)
  case (1 p)
  then show ?case 
    by (rule_tac x=1 in exI, simp)
next
  case (2 p)
  then show ?case 
    by (rule_tac x=1 in exI, simp)
next
  case (3 \<phi>)
  then show ?case 
    by clarsimp
next
  case (4 \<phi> \<psi>)
  then obtain m and n 
    where "is_CNF ((distrib_disj ^^ m) (push_neg (\<not>\<^sub>F \<phi>)))"
      and "is_CNF ((distrib_disj ^^ n) (push_neg (\<not>\<^sub>F \<psi>)))"
    by blast
  hence "is_CNF ((distrib_disj ^^ (max m n)) (push_neg (\<not>\<^sub>F \<phi>)))"
      and "is_CNF ((distrib_disj ^^ (max m n)) (push_neg (\<not>\<^sub>F \<psi>)))"
    using is_CNF_compow_distrib_disjI[of _ "max m n"] 
      max.cobounded1 max.cobounded2 by blast+
  then show ?case
    by auto
next
  case (5 \<phi> \<psi>)
  then show ?case 
    apply clarsimp
    apply (subst (asm) is_CNF_iff_rec)
    apply (subst (asm) is_clause_iff_rec; clarsimp)

    sorry
next
  case (6 \<phi> \<psi>)
  then show ?case 
    apply clarsimp
    sorry
next
  case (7 \<phi> \<psi>)
  then obtain m and n 
    where "is_CNF ((distrib_disj ^^ m) (push_neg \<phi>))"
      and "is_CNF ((distrib_disj ^^ n) (push_neg \<psi>))"
    by blast
  hence "is_CNF ((distrib_disj ^^ (max m n)) (push_neg \<phi>))"
      and "is_CNF ((distrib_disj ^^ (max m n)) (push_neg \<psi>))"
    using is_CNF_compow_distrib_disjI[of _ "max m n"] 
      max.cobounded1 max.cobounded2 by blast+
  then show ?case
    by auto
qed

primrec elim_doubles :: "'a formula \<Rightarrow> 'a formula" 
  where "elim_doubles (@\<^sub>F p) = @\<^sub>F p"
  | "elim_doubles (\<not>\<^sub>F \<phi>) = (\<not>\<^sub>F (elim_doubles \<phi>))"
  | "elim_doubles (\<phi> \<and>\<^sub>F \<psi>) = (if \<phi> = \<psi> then elim_doubles \<phi> else (elim_doubles \<phi>) \<and>\<^sub>F (elim_doubles \<psi>))"
  | "elim_doubles (\<phi> \<or>\<^sub>F \<psi>) = (if \<phi> = \<psi> then elim_doubles \<phi> else (elim_doubles \<phi>) \<or>\<^sub>F (elim_doubles \<psi>))"

lemma correct_elim_doubles: "sat v (elim_doubles \<phi>) \<longleftrightarrow> sat v \<phi>"
  by (induct \<phi>, simp_all)

primrec is_dlause :: "'a formula \<Rightarrow> bool"
  where "is_dlause (@\<^sub>F p) = True"
  | "is_dlause (\<not>\<^sub>F \<phi>) = is_literal (\<not>\<^sub>F \<phi>)"
  | "is_dlause (Or \<phi> \<psi>) = False"
  | "is_dlause (And \<phi> \<psi>) = (is_dlause \<phi> \<and> is_dlause \<psi>)"

lemma is_dlause_iff_rec: 
  "is_dlause \<phi> \<longleftrightarrow> (is_literal \<phi> \<or> (\<exists>\<psi> \<gamma>. is_dlause \<psi> \<and> is_dlause \<gamma> \<and> \<phi> = \<psi> \<and>\<^sub>F \<gamma>))"
  by (induct \<phi>, simp_all)

fun is_DNF :: "'a formula \<Rightarrow> bool"
  where "is_DNF (@\<^sub>F p) = True"
  | "is_DNF (\<not>\<^sub>F (@\<^sub>F p)) = True"
  | "is_DNF (\<not>\<^sub>F \<phi>) = False"
  | "is_DNF (Or \<phi> \<psi>) = (is_DNF \<phi> \<and> is_DNF \<psi>)"
  | "is_DNF (And \<phi> \<psi>) = (is_dlause \<phi> \<and> is_dlause \<psi>)"

(******************************************************)

term "((@\<^sub>Fa\<^sub>1 \<or>\<^sub>F @\<^sub>Fa\<^sub>1) \<and>\<^sub>F @\<^sub>Fa\<^sub>1) \<or>\<^sub>F @\<^sub>Fa\<^sub>1"
term "@\<^sub>Fa\<^sub>1 \<or>\<^sub>F (@\<^sub>Fa\<^sub>1 \<and>\<^sub>F @\<^sub>Fa\<^sub>1) \<or>\<^sub>F @\<^sub>Fa\<^sub>1"
term "@\<^sub>Fa\<^sub>1 \<or>\<^sub>F (@\<^sub>Fa\<^sub>1 \<and>\<^sub>F (@\<^sub>Fa\<^sub>1 \<or>\<^sub>F @\<^sub>Fa\<^sub>1))"
term "(@\<^sub>Fa\<^sub>1 \<and>\<^sub>F @\<^sub>Fa\<^sub>1) \<or>\<^sub>F (@\<^sub>Fa\<^sub>1 \<and>\<^sub>F @\<^sub>Fa\<^sub>1)"

value "is_CNF (to_CNF (((@\<^sub>Fa\<^sub>1 \<and>\<^sub>F @\<^sub>Fa\<^sub>1) \<or>\<^sub>F @\<^sub>Fa\<^sub>1 \<and>\<^sub>F @\<^sub>Fa\<^sub>1)))"
value "is_CNF (to_CNF (@\<^sub>Fa\<^sub>1 \<or>\<^sub>F (@\<^sub>Fa\<^sub>1 \<and>\<^sub>F @\<^sub>Fa\<^sub>1) \<or>\<^sub>F @\<^sub>Fa\<^sub>1))"
value "is_CNF (to_CNF (@\<^sub>Fa\<^sub>1 \<or>\<^sub>F (@\<^sub>Fa\<^sub>1 \<and>\<^sub>F (@\<^sub>Fa\<^sub>1 \<or>\<^sub>F @\<^sub>Fa\<^sub>1))))"
value "is_CNF (to_CNF ((@\<^sub>Fa\<^sub>1 \<and>\<^sub>F @\<^sub>Fa\<^sub>1) \<or>\<^sub>F (@\<^sub>Fa\<^sub>1 \<and>\<^sub>F @\<^sub>Fa\<^sub>1)))"

lemma "is_CNF ((push_neg \<phi>)) \<or> is_DNF ((push_neg \<phi>))"
  oops

(*>*)
end
(*<*)
