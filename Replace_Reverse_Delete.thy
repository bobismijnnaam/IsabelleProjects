theory Replace_Reverse_Delete
  imports
  Main
begin

fun replace :: "'a \<Rightarrow> 'a \<Rightarrow> 'a list \<Rightarrow> 'a list" where
"replace needle new_needle (Cons hay rest) = (Cons
  (if hay = needle 
    then new_needle else hay)
  (replace needle new_needle rest))" |
"replace _ _ Nil = Nil"

lemma
  shows replace_append_eq: "replace x y zs @ [y] = replace x y (zs @ [x])"
  by (induct zs arbitrary: x y, simp+)
qed

lemma
  assumes "a \<noteq> x"
  shows replace_append_neq:
    "replace x y zs @ [a] = replace x y (zs @ [a])"
  by(induct zs, auto simp add: assms)

theorem
  shows "rev (replace x y zs) = replace x y (rev zs)"
proof(induct zs)
case Nil
then show ?case by simp
next
  case (Cons a zs)
  then show ?case 
    using replace_append_eq replace_append_neq
    by auto
qed

(* Not true by counterexample: 
theorem
  shows "replace x y (replace u v zs) = replace u v (replace x y zs)" *)

(* Not true by counterexample: 
theorem
  shows "replace y z (replace x y zs) = replace x z zs" *)

fun del1 :: "'a \<Rightarrow> 'a list \<Rightarrow> 'a list" where
"del1 x (Cons y xs) = (if x = y then xs else (Cons y (del1 x xs)))" |
"del1 x Nil = Nil"

fun delall :: "'a \<Rightarrow> 'a list \<Rightarrow> 'a list" where
"delall x (Cons y xs) = (let tail = delall x xs in
  (if x = y then tail else (Cons y tail)))" |
"delall x Nil = Nil"

lemma [simp]:
  assumes "a \<noteq> x"
  shows delall_assoc_cons_neq: "delall x (a # xs) = a # delall x xs"
  using assms by auto

lemma [simp]:
  shows delall_assoc_cons_eq: "delall x (x # xs) = delall x xs"
  by simp

lemma [simp]:
  assumes "a \<noteq> x"
  shows del1_assoc_cons_neq: "del1 x (a # xs) = a # del1 x xs"
  using assms by auto

lemma [simp]:
  shows del1_assoc_cons_eq: "del1 x (x # xs) = xs"
  by simp

theorem
  shows del1_after_delall: "del1 x (delall x xs) = delall x xs"
proof(induct xs)
  case Nil
  then show ?case by simp
next
  case (Cons a xs)
  then show ?case
    by(auto simp add: Let_def)
qed

theorem
  shows "delall x (delall x xs) = delall x xs"
proof(induct xs)
case Nil
then show ?case by simp
next
  case (Cons a xs)
  then show ?case by(auto simp add: Let_def)
qed

theorem
  shows "delall x (del1 x xs) = delall x xs"
proof(induct xs)
case Nil
then show ?case by simp
next
  case (Cons a xs)
  then show ?case by(auto simp add: Let_def)
qed

theorem
  shows "del1 x (del1 y zs) = del1 y (del1 x zs)"
proof(induct zs)
case Nil
then show ?case by simp
next
  case (Cons a zs)
  then show ?case by(auto simp add: Let_def)
qed

theorem
  shows "delall x (del1 y zs) = del1 y (delall x zs)"
proof(induct zs arbitrary: x y)
case Nil
  then show ?case by simp
next
  case (Cons a zs)
  then show ?case 
    by (simp add: Let_def del1_after_delall)
qed

theorem
  shows "delall x (delall y zs) = delall y (delall x zs)"
proof(induct zs)
case Nil
  then show ?case by simp
next
  case (Cons a zs)
  then show ?case by(auto simp add: Let_def)
qed

(* Disproven by counterexample
theorem
  shows "del1 y (replace x y xs) = del1 x xs" *)

(* Disproven by counterexample
theorem
  shows "delall y (replace x y xs) = delall x xs" *)

theorem "replace x y (delall x zs) = delall x zs"
proof(induction zs)
case Nil
  then show ?case by simp
next
  case (Cons a zs)
  then show ?case by (auto simp add: Let_def)
qed

(* Disproven by counterexample
theorem "replace x y (delall z zs) = delall z (replace x y zs)" *)

(* Disproven by counterexample 
theorem "rev(del1 x xs) = del1 x (rev xs)" *)

lemma delall_append_eq:
"delall x (xs @ [x]) = delall x xs "
  by(induct xs, simp+)

lemma delall_append_neq:
"x \<noteq> a \<Longrightarrow> delall x xs @ [a] = delall x (xs @ [a])"
  by(induct xs, auto simp add: Let_def)

lemmas delall_append = delall_append_eq delall_append_neq

theorem "rev(delall x xs) = delall x (rev xs)"
proof(induction xs)
case Nil
then show ?case by simp
next
case (Cons a xs)
  then show ?case
    by(auto simp add: Let_def delall_append)
qed

end