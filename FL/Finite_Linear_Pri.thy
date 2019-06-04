theory Finite_Linear_Pri

imports
  "FL-Core.Finite_Linear"
begin

fun priacc :: "'a partialorder \<Rightarrow> 'a acceptance \<Rightarrow> 'a acceptance" ("priacc\<^sub>[\<^sub>_\<^sub>] '(_')" 65) where
"priacc\<^sub>[\<^sub>p\<^sub>](\<bullet>) = \<bullet>" |
\<comment> \<open>Any acceptance Z, that is not \<bullet>, is related to A, where A is a set that 
    contains events in Z, such that no event b in Z is of higher priority as
    given by the partial order p.\<close>
"priacc\<^sub>[\<^sub>p\<^sub>]([Z]\<^sub>\<F>\<^sub>\<L>) = [{a. a \<in> Z \<and> \<not>(\<exists>b. b\<in>Z \<and> a <\<^sup>*p b)}]\<^sub>\<F>\<^sub>\<L>"

lemma prirelS_induct_case:
  assumes "((prirelacc p (acceptance A) (acceptance Z)) \<and> event(A) = event(Z) 
     \<and>
      (maximal(p,event(A)) 
       \<or> 
      (acceptance(Z) \<noteq> \<bullet> \<and> \<not>(\<exists>b. b \<in>\<^sub>\<F>\<^sub>\<L> acceptance(Z) \<and> event(A) <\<^sup>*p b))
       \<or>
      acceptance(A) \<noteq> \<bullet>))"
  shows "acceptance A \<le> acceptance Z \<inter>\<^sub>\<F>\<^sub>\<L> (higherPri p (acceptance Z)) \<and> event(A) = event(Z)  \<and>
         (maximal(p,event(A)) 
          \<or> 
          ( event(Z) \<in>\<^sub>\<F>\<^sub>\<L> acceptance Z \<inter>\<^sub>\<F>\<^sub>\<L> (higherPri p (acceptance Z)))
          )"
  using assms unfolding higherPri_def apply auto
    apply (cases A, auto, cases Z, auto, case_tac a, auto, case_tac aa, auto)
    apply (case_tac a, auto)
    apply (cases A, auto, cases Z, auto, case_tac a, auto, case_tac aa, auto)
   apply (cases A, auto, cases Z, auto)
     apply (case_tac a, auto, case_tac aa, auto)
    apply (cases Z, auto, case_tac a, auto)
   apply (cases A, auto, cases Z, auto, case_tac a, auto, case_tac aa, auto)
  apply (case_tac a, auto)
   apply (cases A, auto, case_tac a, auto)
  apply (cases A, auto, case_tac a, auto, cases Z, auto, case_tac a, auto)
  by (cases Z, auto, case_tac a, auto)

definition Pri :: "'a partialorder \<Rightarrow> 'a fltraces \<Rightarrow> 'a fltraces" where
"Pri p F = {A|A Z. prirel p A Z \<and> Z \<in> F}"

end