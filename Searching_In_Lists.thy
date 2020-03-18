theory Searching_In_Lists
imports
  Main
begin

fun first_pos :: "('a \<Rightarrow> bool) \<Rightarrow> 'a list \<Rightarrow> nat" where
"first_pos _ Nil = 0" |
\<open>first_pos f (Cons x xs) = (if f x then 0 else 1 + first_pos f xs)\<close>

value "first_pos (\<lambda>x. x = (3 :: nat)) [1::nat, 3, 5, 3, 1]"
value "first_pos (\<lambda>x. x \<ge> 4) [1::nat, 3, 5, 7]"
value "first_pos (\<lambda>x. size x > 1) [[], [1::nat, 2], [3]]"

lemma "(first_pos P xs = size xs) = (\<forall> x \<in> set xs. \<not>(P x))"
  by(induct xs, auto)

lemma "list_all (\<lambda>x. \<not>P x) (take (first_pos P xs) xs)"
  by(induct xs, auto)

lemma "first_pos (\<lambda>x. P x \<or> Q x) xs = min (first_pos P xs) (first_pos Q xs)"
  by(induction xs, auto)

lemma "first_pos (\<lambda>x. P x \<and> Q x) xs \<ge> max (first_pos P xs) (first_pos Q xs)"
  by(induction xs, auto)

lemma
  assumes "\<forall>x. (P x \<longrightarrow> Q x)" 
  shows "first_pos P xs < length xs \<longrightarrow> first_pos Q xs < length xs"
  using assms by (induction xs, auto)

fun count :: "('a \<Rightarrow> bool) \<Rightarrow> 'a list \<Rightarrow> nat" where
"count _ Nil = 0" |
"count f (Cons x xs) = (if f x then 1 else 0) + count f xs"

print_theorems  

lemma count_concat_split: "count f (xs @ ys) = count f xs + count f ys"
  by(induct xs, auto)

lemma "count f xs = count f (rev xs)"
  by(induct xs, auto simp add: count_concat_split)

lemma "length (filter f xs) = count f xs"
  by(induct xs, auto)

end