theory AllPAreQ_noProofs

imports Main

begin

typedecl atProp

datatype formula = All atProp atProp ("All _ are _ ")

type_synonym 'a model = "(atProp \<Rightarrow>'a set)" 

fun satisfies :: "'a model \<Rightarrow> formula \<Rightarrow> bool" ("_ \<Turnstile> _" )
where
  "satisfies M (All x are y) = (M x \<subseteq> M y)"

datatype example_2_1 = e1 | e2 | e3 | e4 | e5

lemma example_2_1:
assumes "(UNIV :: atProp set) = {n,p,q} \<and> n\<noteq>p \<and> n\<noteq>q \<and> p\<noteq>q"
assumes "M n = {}  \<and>  M p = {e1,e3,e4}  \<and>  M q = {e1,e3}"
shows "M \<Turnstile> All n are n" 
   and "M \<Turnstile>All n are p" 
   and "M \<Turnstile>All n are q" 
   and "M \<Turnstile> All p are p" 
   and "M \<Turnstile> All q are p" 
   and "M \<Turnstile> All q are q"
   and "\<not> (M \<Turnstile> All p are n)"
   and "\<not> (M \<Turnstile> All p are q)"
   and "\<not> (M \<Turnstile> All q are n)"
  sorry

definition M_satisfies_G :: "'a model \<Rightarrow> formula set \<Rightarrow> bool" ("_ \<Turnstile>M _")
where
  "M_satisfies_G M G  \<equiv> \<forall>f. f \<in> G \<longrightarrow> (M \<Turnstile> f)"

definition entails_b :: "formula set \<Rightarrow> formula \<Rightarrow> 'a \<Rightarrow> bool" 
where
  "entails_b G f (ty::'a) \<equiv> \<forall> (M::'a model). (M \<Turnstile>M G) \<longrightarrow> (M \<Turnstile> f)"

definition entails :: "formula set \<Rightarrow> formula \<Rightarrow> 'a itself \<Rightarrow> bool" ("_ \<Turnstile>G _ _")
where
  "entails G f (ty::'a itself) \<equiv> \<forall> (M::'a model). (M \<Turnstile>M G) \<longrightarrow> (M \<Turnstile> f)"

inductive derivable :: "formula \<Rightarrow> bool" ("0\<turnstile> _")
where
  A_axiom: "0\<turnstile> (All X are X)"
| A_barbara: "\<lbrakk>0\<turnstile>(All X are Y); 0\<turnstile>(All Y are Z)\<rbrakk> \<Longrightarrow> 0\<turnstile>(All X are Z)"

lemma example_2_5:
assumes "0\<turnstile>All l are m" 
and "0\<turnstile>All q are l" 
and "0\<turnstile>All m are p" 
and "0\<turnstile>All n are p" 
and "0\<turnstile>All l are q"
shows "0\<turnstile> All q are p"
  sorry

inductive derives :: "formula set \<Rightarrow> formula \<Rightarrow> bool" ("_ \<turnstile> _")
where
  A_assumption: "f \<in> hs \<Longrightarrow>  hs \<turnstile> f"
| A_axiom: "hs \<turnstile> (All X are X)"
| A_barbara: "\<lbrakk>hs \<turnstile>(All X are Y); hs \<turnstile>(All Y are Z)\<rbrakk> \<Longrightarrow> hs \<turnstile>(All X are Z)"

lemma example_2_5_b:
fixes l m n p q
defines "G_2_5  \<equiv> {All l are m,All q are l,All m are p,All n are p,All l are q}"
shows "G_2_5 \<turnstile> All q are p"
  sorry

lemma prop_2_2_1:
  fixes G g
  assumes "G \<turnstile> g"
  shows  "G \<Turnstile>G g (TYPE(atProp))"
  sorry

definition less_equal_atprop :: "atProp \<Rightarrow> formula set \<Rightarrow> atProp \<Rightarrow> bool" ("_ \<lesssim>_ _")
where
  "less_equal_atprop u G v \<equiv> G \<turnstile> All u are v"

find_theorems name:preorder

lemma prop_2_4_1:
  fixes G 
  shows "preorder_on UNIV { (x,y). x \<lesssim>G y }"
  sorry

definition "canonical_model G u \<equiv> { v. v \<lesssim>G u }"

lemma lemma_2_4_2:
  fixes G assumes "M = canonical_model G"
  shows "M \<Turnstile>M G"
  sorry

lemma thm_2_4_3: 
  assumes "G \<Turnstile>G (All p are q) (TYPE(atProp))"
  shows "G \<turnstile> All p are q"
  sorry

end

