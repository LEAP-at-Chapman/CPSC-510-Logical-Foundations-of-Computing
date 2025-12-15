*Download the Isabelle .thy file for this exercise [here](./exercise_2_2.thy)*


```isabelle
theory exercise_2_2
  imports Main

begin

fun add :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
  "add 0 n = n" |
  "add (Suc m) n = Suc (add m n)" 

value "add 0 5"
value "add 3 4"
value "add (Suc 2) 4"

lemma add_assoc: "add (add m n) p = add m (add n p)"
proof (induction m) 
  case 0 (* this sets m = 0 as the base case *)
  (* sets goal to "add (add 0 n) p = add 0 (add n p)" *)
  show ?case by simp (* simplify the goal to "add n p = add n p" *)
next
  case (Suc m) (* fixes m, goal specialized to Suc m; provides Suc.IH *)
  (* goal: add (add (Suc m) n) p = add (Suc m) (add n p) *)
  (* IH: add (add m n) p = add m (add n p) which we assume to be true *)
  show ?case by (simp add: Suc.IH) (*Suc.IH is the Induction Hypothesis *)
  (* Use the recursive definition of add to expand both sides, 
   then apply the induction hypothesis (Suc.IH) to rewrite the inner equality, 
   letting simp close the goal. *)
  (* 	
  •	simp unfolds add (Suc m) n = Suc (add m n)
	•	add: Suc.IH uses the hypothesis add (add m n) p = add m (add n p)
	•	Both sides then simplify to Suc (...) = Suc (...), which is trivially true
  *)
qed

(* use 2 helper lemmas - add_0_right and add_Suc_right - for communative property *)
lemma add_0_right: "add m 0 = m"
proof(induction m)
  case 0
  (* Goal: add 0 0 = 0. By the base equation add 0 n = n. *)
  show ?case by simp
  (* Base: add 0 0 = 0 by add.simps(1) *)
next
  case (Suc m)
  (* 
  IH: add m 0 = m
  Goal: add (Suc m) 0 = Suc m.
  Expand the LHS with the recursive clause, then use the IH. 
  *)
  show ?case by (simp add: Suc.IH)
  (* Step: add (Suc m) 0 = Suc (add m 0) by add.simps(2), then = Suc m by IH *)
qed

lemma add_Suc_right: "add m (Suc n) = Suc (add m n)"
proof(induction m)
  case 0
  (* 
  Goal: add 0 (Suc n) = Suc (add 0 n).
  By add 0 x = x, both sides become Suc n.
  *)
  show ?case by simp
  (* Base: add 0 (Suc n) = Suc n and Suc (add 0 n) = Suc n *)
next
  case (Suc m)
  (*
  IH: add m (Suc n) = Suc (add m n)
  Goal: add (Suc m) (Suc n) = Suc (add (Suc m) n).
  Expand LHS with add.simps, then use IH, then fold once.
  *)
  show ?case by (simp add: Suc.IH)
  (* Step: add (Suc m) (Suc n) = Suc (add m (Suc n)) (def), then by IH = Suc (Suc (add m n)), 
  and simp recognizes that equals Suc (add (Suc m) n) via the def again *)
qed

lemma add_comm: "add m n = add n m"
proof (induction m)
  case 0
  show ?case
    by (simp add: add_0_right)
next
  case (Suc m)
  show ?case
    by (simp add: Suc.IH add_Suc_right)
qed

end
```