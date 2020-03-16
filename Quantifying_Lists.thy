theory Quantifying_Lists
imports
  Main
begin

fun alls :: "('a \<Rightarrow> bool) \<Rightarrow> 'a list \<Rightarrow> bool" where
"alls _ Nil = True" |
"alls f (x # xs) = (f x \<and> alls f xs)"

fun exs :: "('a \<Rightarrow> bool) \<Rightarrow> 'a list \<Rightarrow> bool" where
"exs _ Nil = False" |
"exs f (x # xs) = (f x \<or> exs f xs)"

lemma [simp]: "alls (\<lambda>x. P x \<and> Q x) xs = (alls P xs \<and> alls Q xs)"
proof(induct xs)
case Nil
  then show ?case by simp
next
  case (Cons a xs)
  then show ?case by auto
qed

lemma [simp]: "alls P (xs @ ys) = (alls P xs \<and> alls P ys)"
proof(induct xs)
  case Nil
  then show ?case 
    by simp
next
case (Cons a xs)
  then show ?case by simp
qed

lemma "alls P (rev xs) = alls P xs"
proof(induct xs)
case Nil
then show ?case by simp
next
  case (Cons a xs)
  then show ?case by auto
qed

lemma nex_all: "\<not>(\<exists>x. P x) \<equiv> \<forall> x. \<not>P x"
  by simp

lemma "\<exists>P Q xs. exs (\<lambda>x. P x \<and> Q x) xs \<noteq> (exs P xs \<and> exs Q xs)"
proof(rule ccontr)
  assume "\<not>?thesis"
  then have "\<forall>P Q xs. \<not>(exs (\<lambda>x. P x \<and> Q x) xs \<noteq> (exs P xs \<and> exs Q xs))"
    apply(simp only: nex_all)
    



end