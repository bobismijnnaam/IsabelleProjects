theory SNOC
imports
    Main
begin

fun snoc :: "'a list \<Rightarrow> 'a \<Rightarrow> 'a list" where
"snoc Nil e = (Cons e Nil)" |
"snoc (Cons x xs) e = (Cons x (snoc xs e))"

lemma rev_app_back:
  shows "xs @ [x] = snoc xs x"
proof(induct xs arbitrary: x)
  case Nil
  then show ?case by simp
next
  case (Cons a xs)
  then show ?case by simp
qed

theorem rev_cons:
  shows "rev (x # xs) = snoc (rev xs) x"
proof(induct xs arbitrary: x)
  case Nil
  then show ?case by simp
next
  case (Cons a xs)
  then show ?case using rev_app_back by auto
qed

end