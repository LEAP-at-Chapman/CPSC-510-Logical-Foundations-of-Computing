theory AllPAreQ

imports Main

begin

typedecl atProp

datatype formula = All atProp atProp ("All _ are _ ")

type_synonym 'a model = "(atProp \<Rightarrow>'a set)" 

type_synonym 'a pre_model = "'a set \<times> (atProp \<Rightarrow> 'a set)"
definition wf_model :: "'a pre_model \<Rightarrow> bool" 
  where "wf_model M \<equiv> let (M,f) = M in (! p. f p \<subseteq> M)" 

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
proof %invisible -
  show "M \<Turnstile> All n are n" by simp
  show "M \<Turnstile> All n are p" by (metis assms(2) empty_subsetI satisfies.simps)
  show "M \<Turnstile> All n are q" by (metis assms(2) bot.extremum satisfies.simps)
  show "M \<Turnstile> All p are p" by simp
  show "M \<Turnstile> All q are p" by (metis assms(2) insert_mono satisfies.simps subset_insertI)
  show "M \<Turnstile> All q are q" by simp
  show "\<not> (M \<Turnstile> All p are n)" by (metis assms(2) bot.extremum_unique insert_not_empty satisfies.simps)
  show "\<not> (M \<Turnstile> All p are q)" by (metis assms(2) empty_iff example_2_1.distinct(15) example_2_1.distinct(5) insert_iff insert_subset satisfies.simps)
  show "\<not> (M \<Turnstile> All q are n)" by (metis assms(2) insert_not_empty satisfies.simps subset_empty)
qed    

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

apply (rule_tac Y=l in A_barbara)
 apply (rule assms(2))
  
 apply (rule_tac Y=m in A_barbara)
  apply (rule_tac Y=m in A_barbara)
   apply (rule assms(1))

   apply (rule A_axiom)
  apply (rule assms(3))
done 

inductive derives :: "formula set \<Rightarrow> formula \<Rightarrow> bool" ("_ \<turnstile> _")
where
  A_assumption: "f \<in> hs \<Longrightarrow>  hs \<turnstile> f"
| A_axiom: "hs \<turnstile> (All X are X)"
| A_barbara: "\<lbrakk>hs \<turnstile>(All X are Y); hs \<turnstile>(All Y are Z)\<rbrakk> \<Longrightarrow> hs \<turnstile>(All X are Z)"

lemma example_2_5_b:
fixes l m n p q
defines "G_2_5  \<equiv> {All l are m,All q are l,All m are p,All n are p,All l are q}"
shows "G_2_5 \<turnstile> All q are p"
apply (rule_tac Y=l in A_barbara)
 apply (rule A_assumption) apply (simp add: G_2_5_def)
  apply (rule_tac Y=m in A_barbara)
    apply (rule_tac Y=m in A_barbara)
     apply (rule A_assumption) apply (simp add: G_2_5_def)

     apply (rule A_axiom)
    apply (rule A_assumption) apply (simp add: G_2_5_def)
done 

lemma prop_2_2_1:
  fixes G g
  assumes "G \<turnstile> g"
  shows  "G \<Turnstile>G g (TYPE(atProp))"
using assms
proof (induct rule: derives.induct)
  case (A_assumption) 
  show ?case 
by (metis A_assumption.hyps M_satisfies_G_def entails_def)
next 
  case (A_axiom)
  show ?case by (metis entails_def order_refl satisfies.simps)
next
  case (A_barbara)
  show ?case by (metis A_barbara.hyps(2) A_barbara.hyps(4) entails_def satisfies.simps subset_trans)
qed

definition less_equal_atprop :: "atProp \<Rightarrow> formula set \<Rightarrow> atProp \<Rightarrow> bool" ("_ \<lesssim>_ _")
where
  "less_equal_atprop u G v \<equiv> G \<turnstile> All u are v"

find_theorems name:preorder

lemma prop_2_4_1:
  fixes G 
  shows "preorder_on UNIV { (x,y). x \<lesssim>G y }"
proof (auto simp add: preorder_on_def)
   show "refl { (x,y). x \<lesssim>G y }" 
    unfolding refl_on_def
    using A_axiom by (metis UNIV_Times_UNIV case_prodI iso_tuple_UNIV_I less_equal_atprop_def mem_Collect_eq subset_iff)
  show "trans { (x,y). x \<lesssim>G y }" 
    unfolding trans_def
    using A_barbara by %invisible (metis (full_types) less_equal_atprop_def mem_Collect_eq split_conv)
qed

definition "canonical_model G u \<equiv> { v. v \<lesssim>G u }"

lemma lemma_2_4_2:
  fixes G assumes "M = canonical_model G"
  shows "M \<Turnstile>M G"
proof (auto simp add: M_satisfies_G_def)
  fix g  assume "g \<in> G"
  then obtain p q where "(All p are q) = g" by %invisible (metis formula.exhaust)

  then have "p \<lesssim>G q" using A_assumption by %invisible (metis (full_types) `g \<in> G` less_equal_atprop_def)

  then have "M p \<subseteq> M q" using A_barbara by %invisible (metis assms canonical_model_def less_equal_atprop_def mem_Collect_eq subsetI)

  thus "M \<Turnstile> g" by %invisible (metis `(All p are q) = g` satisfies.simps)

qed

lemma thm_2_4_3: 
  assumes "G \<Turnstile>G (All p are q) (TYPE(atProp))"
  shows "G \<turnstile> All p are q"
proof -
  define M where "M =  canonical_model G"
  have "M \<Turnstile> All p are q" using lemma_2_4_2 by %invisible (metis (full_types) M_def assms entails_def)
  
  then have "M p \<subseteq> M q" by %invisible auto


  have "p \<lesssim>G p" using A_axiom by %invisible (metis less_equal_atprop_def)

  then have "p \<in> M p" using canonical_model_def by %invisible (metis M_def mem_Collect_eq)


  have "p \<in> M q" using `M p \<subseteq> M q` by %invisible (metis `p \<in> M p`  set_rev_mp)

  then have "p \<lesssim>G q" using canonical_model_def by %invisible (metis M_def  mem_Collect_eq)

  thus ?thesis by %invisible (metis less_equal_atprop_def)

qed

end

