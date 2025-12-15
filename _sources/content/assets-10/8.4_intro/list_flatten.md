*Download the Isabelle .thy file for this exercise [here](./list_flatten.thy)*



```isabelle
theory list_flatten 
    imports Main
begin

fun flatten :: "'a list list => 'a list" where
  "flatten [] = []"
|"flatten (xs # xss) = xs @ flatten xss"

lemma "flatten [[1::nat, 2], [3,4], [5,6], [7]] = [1,2,3,4,5,6,7]"
  apply simp
  done

lemma length_flatten:
  "length (flatten xss) = sum_list (map length xss)"
  apply (induct xss)
   apply simp
  by simp
  
end
```