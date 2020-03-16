theory MagicMethods imports 
  Main 
begin

(* MM1 *)

fun sq :: "nat \<Rightarrow> nat" where
"sq 0 = 0" |
"sq (Suc 0) = 1" |
"sq n = sq (n - 1) + n - 1 + n"

(* Readable but redundant and long proof *)

lemma 
  shows "sq n = n * n"
proof (induction n rule: sq.induct)
  case 1
  then show ?case by simp
next
  case 2
  then show ?case by simp
next
  case (3 v)
  then show ?case (is "sq ?v = ?v * ?v")
  proof -
    have unfolded_rhs: "?v * ?v = ?v + (?v - 1) + (?v - 1) * (?v - 1)" by simp
    have unfolded_sq: "sq ?v = sq (?v - 1) + (?v - 1) + ?v" by simp
    from "3.IH" have from_induction_hypothesis: "sq (?v - 1) = (?v - 1) * (?v - 1)" by auto
    from unfolded_rhs unfolded_sq from_induction_hypothesis show ?case by simp
  qed
qed

(* Proof by applying simp 3 times *)

lemma [simp]: 
  shows "sq n = n * n"
proof (induction n rule: sq.induct)
  case 1
  then show ?case by simp
next
  case 2
  then show ?case by simp
next
  case (3 v)
  from this show ?case by simp
qed

(* MM2 *)      

lemma
  fixes n :: nat
  fixes m :: nat
  assumes pre: "m \<le> n"
  shows aux_manual: "(n + (n - m)) * m + sq (n - m) = sq n"
proof -
  have "sq (n - m) = (n - m) * (n - m)" by simp
  moreover have "(n + (n - m)) * m = n * m + (n - m) * m" by algebra
  moreover have "(n - m) * m + (n - m) * (n - m) = (n - m) * (n - m + m)" by algebra
  moreover have "(n - m)  * (n - m + m) = (n - m) * n" by auto
  moreover have "n * m + (n - m) * n = n * (m + (n - m))" by algebra
  moreover have "m \<le> n \<Longrightarrow> n * (m + (n - m)) = n * n" by simp
  ultimately show ?thesis using pre
    by simp
qed

lemma "100 < n \<Longrightarrow> (n + (n - 100)) * 100 + sq (n - 100) = sq n"
  using aux_manual less_imp_le_nat by blast

(* MM3 *)

lemma
  fixes n :: nat
  assumes "n mod 10 = 5"
  shows "((n - 5) div 10) * ((n + 5) div 10) * 100 + 25 = sq n"
proof -
  have div_10_mul_10: "(x div 10) * (y div 10) * 100 = (x * y)"
    if a: "x mod 10 = 0" "y mod 10 = 0"
    for x y :: nat
    using a by auto
  have "(n - 5) mod 10 = 0" using assms by presburger
  moreover have "(n + 5) mod 10 = 0" using assms by presburger
  ultimately have s1: "((n - 5) div 10) * ((n + 5) div 10) * 100 + 25 = (n - 5) * (n + 5) + 25" 
    using div_10_mul_10 assms
    by auto
  moreover have "(n - 5) * (n + 5) + 25 = (n - 5) * n + (n - 5) * 5 + 5 * 5"
    by algebra
  moreover have "(n - 5) * n + (n - 5) * 5 + 5 * 5 = (n - 5) * n + 5 * ((n - 5) + 5)" 
    by algebra
  moreover have "(n - 5) * n + 5 * ((n - 5) + 5) = (n - 5) * n + 5 * n"
    using assms by auto
  moreover have "(n - 5) * n + 5 * n = ((n - 5) + 5) * n" by algebra
  moreover have "((n - 5) + 5) * n = n * n" using assms by auto
  ultimately show ?thesis by simp
qed
  
end 