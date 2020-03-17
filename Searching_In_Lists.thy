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

end