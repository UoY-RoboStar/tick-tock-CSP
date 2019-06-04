theory Finite_Linear_Priority_Simplify

imports
  Finite_Linear_Priority
begin

fun ainter :: "'a acceptance \<Rightarrow> 'a acceptance \<Rightarrow> 'a acceptance" (infixl "\<inter>\<^sub>\<F>\<^sub>\<L>" 65) where
"ainter \<bullet> X = \<bullet>" |
"ainter X \<bullet> = \<bullet>" |
"ainter [S]\<^sub>\<F>\<^sub>\<L> [R]\<^sub>\<F>\<^sub>\<L> = [S \<inter> R]\<^sub>\<F>\<^sub>\<L>"

lemma ainter_idem: "a \<inter>\<^sub>\<F>\<^sub>\<L> a = a"
  by (cases a, auto)

lemma ainter_assoc: "(a \<inter>\<^sub>\<F>\<^sub>\<L> b) \<inter>\<^sub>\<F>\<^sub>\<L> c = a \<inter>\<^sub>\<F>\<^sub>\<L> (b \<inter>\<^sub>\<F>\<^sub>\<L> c)"
  by (cases a, auto, cases b, auto, cases c, auto)

lemma ainter_comm: "a \<inter>\<^sub>\<F>\<^sub>\<L> b = b \<inter>\<^sub>\<F>\<^sub>\<L> a"
  by (cases a, auto, cases b, auto, cases b, auto)

interpretation ainter_comm_monoid: comm_monoid "ainter" "[UNIV]\<^sub>\<F>\<^sub>\<L>"
  apply (unfold_locales)
  using ainter_assoc apply blast
  using ainter_comm apply blast
  by (case_tac a, auto)+

definition higherPri :: "'a partialorder \<Rightarrow> 'a acceptance \<Rightarrow> 'a acceptance" where
"higherPri p Z = [{a. \<not>(\<exists>b. b\<in>\<^sub>\<F>\<^sub>\<L> Z \<and> a <\<^sup>*p b)}]\<^sub>\<F>\<^sub>\<L>" (* \<forall>b. a <\<^sup>*p b \<longrightarrow> b\<notin>\<^sub>\<F>\<^sub>\<L> Z *)

lemma higherPri_inter_bullet_iff:
  "\<bullet> = Z \<inter>\<^sub>\<F>\<^sub>\<L> (higherPri p Z) \<longleftrightarrow> Z = \<bullet>"
  unfolding higherPri_def by (cases Z, auto)

lemma prirelS_base_case:
  assumes "(A = Z \<inter>\<^sub>\<F>\<^sub>\<L> (higherPri p Z))"
  shows "prirelacc p A Z \<and> (A = \<bullet> \<longrightarrow> Z = \<bullet>)"
  using assms unfolding higherPri_def apply (induct p A Z rule:prirelacc.induct, auto)
  by (case_tac Za, auto)

lemma prirelS_base_case':
  assumes "prirelacc p A Z \<and> (A = \<bullet> \<longrightarrow> Z = \<bullet>)" 
  shows "(A = Z \<inter>\<^sub>\<F>\<^sub>\<L> (higherPri p Z))"
  using assms unfolding higherPri_def by (induct p A Z rule:prirelacc.induct, auto)

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

lemma prirelS_induct_case':
  assumes "acceptance A \<le> acceptance Z \<inter>\<^sub>\<F>\<^sub>\<L> (higherPri p (acceptance Z)) \<and> event(A) = event(Z)  \<and>
         (maximal(p,event(A)) 
          \<or> 
          (event(Z) \<in>\<^sub>\<F>\<^sub>\<L> acceptance Z \<inter>\<^sub>\<F>\<^sub>\<L> (higherPri p (acceptance Z))) 
          )"
  shows "((prirelacc p (acceptance A) (acceptance Z)) \<and> event(A) = event(Z) 
     \<and>
      (maximal(p,event(A)) 
       \<or> 
      (acceptance(Z) \<noteq> \<bullet> \<and> \<not>(\<exists>b. b \<in>\<^sub>\<F>\<^sub>\<L> acceptance(Z) \<and> event(A) <\<^sup>*p b))
       \<or>
      acceptance(A) \<noteq> \<bullet>))"
  using assms unfolding higherPri_def apply auto
  
     apply (cases A, auto, cases Z, auto)
  apply (case_tac aa, auto, case_tac a, auto)
  
  apply (metis (lifting) Int_iff)
      apply (metis (mono_tags, lifting) Int_Collect)

  apply (smt Int_Collect)
    apply (cases A, auto, cases Z, auto)
      apply (case_tac aa, auto, case_tac a, auto, case_tac a, auto, case_tac a, auto)
  apply (cases A, auto, cases Z, auto)
      apply (case_tac aa, auto, case_tac a, auto)

  apply (metis (mono_tags, lifting) Int_Collect, smt Int_Collect, smt Int_Collect)
  by (cases A, auto, cases Z, auto, case_tac a, auto)

fun prirelS :: "'a partialorder \<Rightarrow> 'a fltrace \<Rightarrow> 'a fltrace \<Rightarrow> bool" where
\<comment> \<open>The base case of this relation is given by prirelacc. \<close>
"prirelS p \<langle>A\<rangle>\<^sub>\<F>\<^sub>\<L> \<langle>Z\<rangle>\<^sub>\<F>\<^sub>\<L> = (A = Z \<inter>\<^sub>\<F>\<^sub>\<L> (higherPri p Z))" (*prirelacc p A Z \<and> (A = \<bullet> \<longrightarrow> Z = \<bullet>))"*) |
\<comment> \<open>The relation is defined for sequences of the same length. Observe, however,
    that this would not preclude the definition of a weaker relation whereby a
    longer sequence is related to a shorter sequence (see definition commented out). \<close>
"prirelS p \<langle>A\<rangle>\<^sub>\<F>\<^sub>\<L> (Z #\<^sub>\<F>\<^sub>\<L> zz) = False" | (* (prirelacc p A (acceptance Z)) *)
"prirelS p (A #\<^sub>\<F>\<^sub>\<L> aa) \<langle>Z\<rangle>\<^sub>\<F>\<^sub>\<L> = False" |
\<comment> \<open>The acceptance(A) and acceptance(Z) satisfy prirelacc, the events are the same, 
    and it is not the case that there is an event b in Z that has higher priority
    than event(A).\<close>
"prirelS p (A #\<^sub>\<F>\<^sub>\<L> aa) (Z #\<^sub>\<F>\<^sub>\<L> zz) 
  = 
  (acceptance A \<le> acceptance Z \<inter>\<^sub>\<F>\<^sub>\<L> (higherPri p (acceptance Z)) \<and> (prirelS p aa zz) \<and> event(A) = event(Z)  \<and>
         (maximal(p,event(A)) 
          \<or> 
          (event(Z) \<in>\<^sub>\<F>\<^sub>\<L> acceptance Z \<inter>\<^sub>\<F>\<^sub>\<L> (higherPri p (acceptance Z))) 
          ))"

lemma prirelS_imp_prirel:
  assumes "prirelS p s t"
  shows "prirel p s t"
  using assms apply (induct p s t rule:prirelS.induct, simp_all)
  using prirelS_base_case apply auto[1]
  by (metis event_in_acceptance prirelS_induct_case')

lemma prirel_imp_prirelS:
  assumes "prirel p s t"
  shows "prirelS p s t"
  using assms apply (induct p s t rule:prirel.induct, simp_all)
  using prirelS_base_case' apply auto[1]
  by (metis event_in_acceptance prirelS_induct_case)

lemma prirel_eq_prirelS:
  "prirel p s t \<longleftrightarrow> prirelS p s t"
  using prirelS_imp_prirel prirel_imp_prirelS by blast

end