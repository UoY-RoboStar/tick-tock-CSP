theory Finite_Linear_Priority

imports
  Finite_Linear_Pri
begin

section \<open> Original definition \<close>

text \<open> In what follows we formalise the definition of Pri as found in 
       "Expressiveness of CSP with Priority". \<close>

fun prirelacc :: "'a partialorder \<Rightarrow> 'a acceptance \<Rightarrow> 'a acceptance \<Rightarrow> bool" where
\<comment> \<open>Any acceptance Z is related to \<bullet>.\<close>
"prirelacc p \<bullet> Z = True" |
\<comment> \<open>Any acceptance Z, that is not \<bullet>, is related to A, where A is a set that 
    contains events in Z, such that no event b in Z is of higher priority as
    given by the partial order p.\<close>
"prirelacc p [A]\<^sub>\<F>\<^sub>\<L> [Z]\<^sub>\<F>\<^sub>\<L> = (A = {a. a \<in> Z \<and> \<not>(\<exists>b. b\<in>Z \<and> a <\<^sup>*p b)})" |
"prirelacc p X Y = False"

text \<open> Pri is defined by the relation prirel below. The recursive case has been
       simplified in comparison to that in the paper, while the base case has
       been made clear. \<close>

fun prirel :: "'a partialorder \<Rightarrow> 'a fltrace \<Rightarrow> 'a fltrace \<Rightarrow> bool" where
\<comment> \<open>The base case of this relation is given by prirelacc. \<close>
"prirel p \<langle>A\<rangle>\<^sub>\<F>\<^sub>\<L> \<langle>Z\<rangle>\<^sub>\<F>\<^sub>\<L> = (prirelacc p A Z \<and> (A = \<bullet> \<longrightarrow> Z = \<bullet>))" |
\<comment> \<open>The relation is defined for sequences of the same length. Observe, however,
    that this would not preclude the definition of a weaker relation whereby a
    longer sequence is related to a shorter sequence (see definition commented out). \<close>
"prirel p \<langle>A\<rangle>\<^sub>\<F>\<^sub>\<L> (Z #\<^sub>\<F>\<^sub>\<L> zz) = False" | (* (prirelacc p A (acceptance Z)) *)
"prirel p (A #\<^sub>\<F>\<^sub>\<L> aa) \<langle>Z\<rangle>\<^sub>\<F>\<^sub>\<L> = False" |
\<comment> \<open>The acceptance(A) and acceptance(Z) satisfy prirelacc, the events are the same, 
    and it is not the case that there is an event b in Z that has higher priority
    than event(A).\<close>
"prirel p (A #\<^sub>\<F>\<^sub>\<L> aa) (Z #\<^sub>\<F>\<^sub>\<L> zz) 
  = 
  ((prirelacc p (acceptance A) (acceptance Z)) \<and> (prirel p aa zz) \<and> event(A) = event(Z) 
    \<and> (event(A) \<in>\<^sub>\<F>\<^sub>\<L> acceptance A \<or> acceptance A = \<bullet>) \<and>
      (maximal(p,event(A)) 
       \<or> 
      (acceptance(Z) \<noteq> \<bullet> \<and> \<not>(\<exists>b. b \<in>\<^sub>\<F>\<^sub>\<L> acceptance(Z) \<and> event(A) <\<^sup>*p b))
       \<or>
      acceptance(A) \<noteq> \<bullet>))"

lemma pri_induct_case:
  assumes "((prirelacc p (acceptance A) (acceptance Z)) \<and> event(A) = event(Z) 
     \<and>
      (maximal(p,event(A)) 
       \<or> 
      (acceptance(Z) \<noteq> \<bullet> \<and> \<not>(\<exists>b. b \<in>\<^sub>\<F>\<^sub>\<L> acceptance(Z) \<and> event(A) <\<^sup>*p b))
       \<or>
      acceptance(A) \<noteq> \<bullet>))"
  shows "(acceptance A \<le> priacc\<^sub>[\<^sub>p\<^sub>](acceptance Z) \<and> event(A) = event(Z)  \<and>
         (\<not> maximal(p,event(A)) \<longrightarrow> event(Z) \<in>\<^sub>\<F>\<^sub>\<L> priacc\<^sub>[\<^sub>p\<^sub>](acceptance Z)))"
  using assms apply auto
         apply (cases A, auto, cases Z, auto, case_tac a, auto, case_tac aa, auto, case_tac a, auto)
     apply (cases A, auto, cases Z, auto, case_tac a, auto, case_tac aa, auto)
    apply (cases A, auto, cases Z, auto, case_tac a, auto, case_tac aa, auto)
    apply (cases Z, auto, case_tac a, auto)
  by (cases A, auto, cases Z, auto, case_tac a, auto, case_tac aa, auto, case_tac a, auto)+

lemma priacc_imp_prirelacc:
  assumes "a \<le> priacc\<^sub>[\<^sub>p\<^sub>] aa" 
  shows "prirelacc p a aa"
  using assms apply(induct aa rule:priacc.induct, auto)
   apply (cases a, auto)
  apply (cases a, auto)
    apply (metis (mono_tags, lifting) Int_iff)
   apply (metis (mono_tags, lifting) Int_Collect)
  by (smt Int_Collect)

lemma prirelacc_imp_priacc:
  assumes "prirelacc p a aa" 
  shows "a \<le> priacc\<^sub>[\<^sub>p\<^sub>] aa" 
  using assms apply(induct aa rule:priacc.induct, auto)
   apply (cases a, auto)
  by (cases a, auto)

lemma prirelacc_eq_priacc [simp]:
  "prirelacc p a aa \<longleftrightarrow> a \<le> priacc\<^sub>[\<^sub>p\<^sub>] aa" 
  using priacc_imp_prirelacc prirelacc_imp_priacc by blast

lemma maximal_event_in_priacc [intro]:
  assumes "event Z \<in>\<^sub>\<F>\<^sub>\<L> priacc\<^sub>[\<^sub>p\<^sub>] acceptance Z" "b \<in>\<^sub>\<F>\<^sub>\<L> acceptance Z" "event Z <\<^sup>*p b"
  shows "maximal(p,event Z)"
  using assms by (cases Z, auto, case_tac a, auto)

lemma pri_induct_case':
  assumes "acceptance A \<le> priacc\<^sub>[\<^sub>p\<^sub>](acceptance Z)" "event(A) = event(Z)"
          "(\<not> maximal(p,event(A)) \<longrightarrow> event(Z) \<in>\<^sub>\<F>\<^sub>\<L> priacc\<^sub>[\<^sub>p\<^sub>](acceptance Z))"
    shows "((prirelacc p (acceptance A) (acceptance Z)) \<and> event(A) = event(Z) 
     \<and>
      (maximal(p,event(A)) 
       \<or> 
      (acceptance(Z) \<noteq> \<bullet> \<and> \<not>(\<exists>b. b \<in>\<^sub>\<F>\<^sub>\<L> acceptance(Z) \<and> event(A) <\<^sup>*p b))
       \<or>
      acceptance(A) \<noteq> \<bullet>))"
  using assms by auto

lemma prirel_alt_induct_case:
  "prirel p (A #\<^sub>\<F>\<^sub>\<L> aa) (Z #\<^sub>\<F>\<^sub>\<L> zz) 
  = 
  (acceptance A \<le> priacc\<^sub>[\<^sub>p\<^sub>](acceptance Z) \<and> (prirel p aa zz) \<and> event(A) = event(Z) \<and>
   (\<not> maximal(p,event(A)) \<longrightarrow> event(Z) \<in>\<^sub>\<F>\<^sub>\<L> priacc\<^sub>[\<^sub>p\<^sub>](acceptance Z)))"
proof -
  have "prirel p (A #\<^sub>\<F>\<^sub>\<L> aa) (Z #\<^sub>\<F>\<^sub>\<L> zz) 
  = 
  ((prirelacc p (acceptance A) (acceptance Z)) \<and> (prirel p aa zz) \<and> event(A) = event(Z) 
    \<and> (event(A) \<in>\<^sub>\<F>\<^sub>\<L> acceptance A \<or> acceptance A = \<bullet>) \<and>
      (maximal(p,event(A)) 
       \<or> 
      (acceptance(Z) \<noteq> \<bullet> \<and> \<not>(\<exists>b. b \<in>\<^sub>\<F>\<^sub>\<L> acceptance(Z) \<and> event(A) <\<^sup>*p b))
       \<or>
      acceptance(A) \<noteq> \<bullet>))"
    by auto
  also have "... =
    ((prirelacc p (acceptance A) (acceptance Z)) \<and> (prirel p aa zz) \<and> event(A) = event(Z) 
     \<and>
      (maximal(p,event(A)) 
       \<or> 
      (acceptance(Z) \<noteq> \<bullet> \<and> \<not>(\<exists>b. b \<in>\<^sub>\<F>\<^sub>\<L> acceptance(Z) \<and> event(A) <\<^sup>*p b))
       \<or>
      acceptance(A) \<noteq> \<bullet>))"
    using event_in_acceptance by blast
  also have "... =
      (acceptance A \<le> priacc\<^sub>[\<^sub>p\<^sub>](acceptance Z) \<and> (prirel p aa zz) \<and> event(A) = event(Z)  \<and>
         (\<not> maximal(p,event(A)) \<longrightarrow> event(Z) \<in>\<^sub>\<F>\<^sub>\<L> priacc\<^sub>[\<^sub>p\<^sub>](acceptance Z)))"
    using pri_induct_case pri_induct_case' by blast
  finally show ?thesis .
qed

subsection \<open>Auxiliary results\<close>

lemma prirelacc_acceptances_eq:
  assumes "acceptance(A) \<noteq> \<bullet>"
          "acceptance(Z) \<noteq> \<bullet>"
    shows "(prirelacc p (acceptance A) (acceptance Z)) \<longleftrightarrow> acceptance(A) = [{a. a \<in>\<^sub>\<F>\<^sub>\<L> acceptance(Z) \<and> \<not>(\<exists>b. b\<in>\<^sub>\<F>\<^sub>\<L> acceptance(Z) \<and> a <\<^sup>*p b)}]\<^sub>\<F>\<^sub>\<L>"
  using assms apply auto
   apply (cases A, auto, cases Z, auto)
  by (case_tac a, auto)

lemma acceptance_not_bullet_imp_prirelacc:
  assumes "acceptance(A) \<noteq> \<bullet>"
          "prirelacc p (acceptance A) (acceptance Z)"
    shows "acceptance(Z) \<noteq> \<bullet>"
  using assms by auto
  
lemma prirelacc_acceptance_not_bullet_imp:
  assumes "prirelacc p (acceptance A) (acceptance Z)" "acceptance(A) \<noteq> \<bullet>"
  shows "\<not>(\<exists>b. b \<in>\<^sub>\<F>\<^sub>\<L> acceptance(Z) \<and> event(A) <\<^sup>*p b)"
  using assms apply auto
  apply (cases Z, auto, cases A, auto)
  apply (case_tac aa, auto, case_tac a, auto)
  by (metis (mono_tags, lifting) Int_Collect)

lemma maximal_not_exists_higher:
  assumes "maximal(p,event(A))"
    shows "\<not>(\<exists>b. b \<in>\<^sub>\<F>\<^sub>\<L> acceptance(Z) \<and> event(A) <\<^sup>*p b)"
  using assms apply auto
  unfolding maximal_def apply (cases Z, auto)
  by (meson assms some_higher_not_maximal)

text \<open> We now show that the definition of prirel for the recursive case is just like
       that of Roscoe. \<close>

lemma prirel_original_induct_case:
  "prirel p (A #\<^sub>\<F>\<^sub>\<L> aa) (Z #\<^sub>\<F>\<^sub>\<L> zz) 
  = 
  ((prirel p aa zz) \<and> event(A) = event(Z) \<and> (event(A) \<in>\<^sub>\<F>\<^sub>\<L> acceptance A \<or> acceptance A = \<bullet>) \<and>
    ((maximal(p,event(A)) \<and> acceptance(A) = \<bullet>)
    \<or>
    (\<not>maximal(p,event(A)) \<and> acceptance(A) = \<bullet> \<and> acceptance(Z) \<noteq> \<bullet> \<and> \<not>(\<exists>b. b \<in>\<^sub>\<F>\<^sub>\<L> acceptance(Z) \<and> event(A) <\<^sup>*p b))
    \<or>
    (acceptance(A) \<noteq> \<bullet> \<and> acceptance(Z) \<noteq> \<bullet> \<and> acceptance(A) = [{a. a \<in>\<^sub>\<F>\<^sub>\<L> acceptance(Z) \<and> \<not>(\<exists>b. b\<in>\<^sub>\<F>\<^sub>\<L> acceptance(Z) \<and> a <\<^sup>*p b)}]\<^sub>\<F>\<^sub>\<L>)
    ))
  "
proof -
  have "
    ((prirel p aa zz) \<and> event(A) = event(Z) \<and> (event(A) \<in>\<^sub>\<F>\<^sub>\<L> acceptance A \<or> acceptance A = \<bullet>) \<and>
    ((maximal(p,event(A)) \<and> acceptance(A) = \<bullet>)
    \<or>
    (\<not>maximal(p,event(A)) \<and> acceptance(A) = \<bullet> \<and> acceptance(Z) \<noteq> \<bullet> \<and> \<not>(\<exists>b. b \<in>\<^sub>\<F>\<^sub>\<L> acceptance(Z) \<and> event(A) <\<^sup>*p b))
    \<or>
    (acceptance(A) \<noteq> \<bullet> \<and> acceptance(Z) \<noteq> \<bullet> \<and> acceptance(A) = [{a. a \<in>\<^sub>\<F>\<^sub>\<L> acceptance(Z) \<and> \<not>(\<exists>b. b\<in>\<^sub>\<F>\<^sub>\<L> acceptance(Z) \<and> a <\<^sup>*p b)}]\<^sub>\<F>\<^sub>\<L>)
    ))
  =
    ((prirelacc p (acceptance A) (acceptance Z)) \<and> (prirel p aa zz) \<and> event(A) = event(Z) \<and> (event(A) \<in>\<^sub>\<F>\<^sub>\<L> acceptance A \<or> acceptance A = \<bullet>) \<and>
    (acceptance(A) = \<bullet> \<and>
       (maximal(p,event(A))
        \<or>
       (\<not>maximal(p,event(A)) \<and> acceptance(Z) \<noteq> \<bullet> \<and> \<not>(\<exists>b. b \<in>\<^sub>\<F>\<^sub>\<L> acceptance(Z) \<and> event(A) <\<^sup>*p b)))
     \<or>
     (acceptance(A) \<noteq> \<bullet> \<and> acceptance(Z) \<noteq> \<bullet>)))"
    using prirelacc_acceptances_eq by auto
  also have "... =
    ((prirelacc p (acceptance A) (acceptance Z)) \<and> (prirel p aa zz) \<and> event(A) = event(Z) \<and> (event(A) \<in>\<^sub>\<F>\<^sub>\<L> acceptance A \<or> acceptance A = \<bullet>) \<and>
      (acceptance(A) = \<bullet> \<and> (maximal(p,event(A)) \<or> acceptance(Z) \<noteq> \<bullet> \<and> \<not>(\<exists>b. b \<in>\<^sub>\<F>\<^sub>\<L> acceptance(Z) \<and> event(A) <\<^sup>*p b))
     \<or>
     (acceptance(A) \<noteq> \<bullet>)))"
    using acceptance_not_bullet_imp_prirelacc by auto
  also have "... =
    ((prirelacc p (acceptance A) (acceptance Z)) \<and> (prirel p aa zz) \<and> event(A) = event(Z) \<and> (event(A) \<in>\<^sub>\<F>\<^sub>\<L> acceptance A \<or> acceptance A = \<bullet>) \<and>
      ((maximal(p,event(A)) \<or> acceptance(Z) \<noteq> \<bullet> \<and> \<not>(\<exists>b. b \<in>\<^sub>\<F>\<^sub>\<L> acceptance(Z) \<and> event(A) <\<^sup>*p b))
     \<or>
     (acceptance(A) \<noteq> \<bullet>)))"
    by auto
  also have "... =
    ((prirelacc p (acceptance A) (acceptance Z)) \<and> (prirel p aa zz) \<and> event(A) = event(Z) \<and> (event(A) \<in>\<^sub>\<F>\<^sub>\<L> acceptance A \<or> acceptance A = \<bullet>) \<and>
      (maximal(p,event(A)) 
       \<or> 
      (acceptance(Z) \<noteq> \<bullet> \<and> \<not>(\<exists>b. b \<in>\<^sub>\<F>\<^sub>\<L> acceptance(Z) \<and> event(A) <\<^sup>*p b))
       \<or>
      acceptance(A) \<noteq> \<bullet>))"
    using maximal_not_exists_higher by auto
  also have "... =
    ((prirelacc p (acceptance A) (acceptance Z)) \<and> (prirel p aa zz) \<and> event(A) = event(Z) \<and> (event(A) \<in>\<^sub>\<F>\<^sub>\<L> acceptance A \<or> acceptance A = \<bullet>)
       \<and> \<not>(\<exists>b. b \<in>\<^sub>\<F>\<^sub>\<L> acceptance(Z) \<and> event(A) <\<^sup>*p b) \<and>
      (maximal(p,event(A)) 
       \<or> 
      (acceptance(Z) \<noteq> \<bullet>)
       \<or>
      acceptance(A) \<noteq> \<bullet>))"
    apply auto
    using maximal_not_exists_higher apply blast
     apply (metis maximal_event_in_priacc not_bullet_less_eq_imp some_higher_not_maximal)
    using maximal_not_exists_higher by blast
  then show ?thesis
    using calculation by auto
qed

lemma prirel_imp_pri:
  assumes "prirel p A Z" 
  shows "pri p A Z"
  using assms apply (induct p A Z rule:pri.induct, auto)
   apply (case_tac Aa, auto)
  by (metis pri_induct_case prirelacc.simps(1))

lemma pri_imp_prirel:
  assumes "pri p A Z"
  shows "prirel p A Z" 
  using assms apply (induct p A Z rule:pri.induct, auto)
    apply (case_tac Za, auto)
  using event_in_acceptance by force+

definition PriOriginal :: "'a partialorder \<Rightarrow> 'a fltraces \<Rightarrow> 'a fltraces" where
"PriOriginal p F = {A|A Z. prirel p A Z \<and> Z \<in> F}"

lemma PriOriginal_eq_Pri:
  "PriOriginal p P = Pri p P"
  unfolding PriOriginal_def Pri_def apply auto
  using prirel_imp_pri apply blast
  using pri_imp_prirel by blast

lemma prirel_prirel_for_FL1:
  assumes "s \<le> t"
          "prirel p t Z"
    shows "\<exists>Y. prirel p s Y \<and> Y \<le> Z"
  using assms
proof (induct p t Z arbitrary:s rule:prirel.induct)
  case (1 p A Z)
  then show ?case 
    apply (cases s, auto)
    apply (cases A, auto, cases Z, auto)
    using "1.prems"(2) less_eq_acceptance.elims(2) 
    apply (metis bullet_left_zero2 order_refl prirel.simps(1) prirelacc.simps(1) x_le_x_concat2)
    using "1.prems"(2) dual_order.antisym less_eq_acceptance.simps(1) 
    by (metis "1.prems"(1) prirelacc.elims(2) prirelacc.simps(3))
next
  case (2 p A Z zz)
  then show ?case by auto
next
  case (3 p A aa Z)
  then show ?case by auto
next
  case (4 p A aa Z zz)
  then show ?case
  proof (induct s)
    case (Acceptance x)
    then show ?case using 4 apply simp
      apply (cases x, simp)      
      apply (metis fltrace_concat2.simps(3) prirel.simps(1) prirelacc.simps(1) x_le_x_concat2)
      apply (cases x, simp)
      by (metis acceptance.distinct(1) less_eq_fltrace.simps(2) not_bullet_less_eq_imp order_refl pri.simps(1) pri_imp_prirel)
  next
    case (AEvent x z)
    then obtain C where C:"prirel p z C \<and> C \<le> zz"
      by (meson less_eq_fltrace.simps(3) prirel_alt_induct_case)
    then have x_less_eq_A:"x \<le> A"
      using AEvent by auto
    then have event_x_z:"event(x) = event(Z)"
      by (metis AEvent.prems(3) less_eq_aevent_def prirel.simps(4))
    then show ?case using 4 AEvent
       proof (cases "acceptance(A) = \<bullet>")
         case A_bullet:True
         then show ?thesis 
           using A_bullet 4 x_less_eq_A event_x_z
           apply (intro exI[where x="Z #\<^sub>\<F>\<^sub>\<L> C"], simp)
           apply (simp add: less_eq_aevent_def C)+
           apply (cases x, auto)
           by (case_tac a, auto)+
       next
         case A_not_bullet:False
         then show ?thesis using 4 AEvent
          proof (cases "acceptance(Z) = \<bullet>")
            case True
            then show ?thesis using 4 A_not_bullet
              apply (intro exI[where x="Z #\<^sub>\<F>\<^sub>\<L> C"], simp)
              apply (simp add: less_eq_aevent_def C)
              using prirelacc.elims(2) by blast
          next
            case False
            then show ?thesis using 4 A_not_bullet event_x_z
              apply (intro exI[where x="Z #\<^sub>\<F>\<^sub>\<L> C"], simp)
              apply (simp add: less_eq_aevent_def C)
              apply (cases x, auto, cases Z, auto)
              by (metis acceptance_set less_eq_aevent_def not_bullet_less_eq_imp x_less_eq_A)
          qed
       qed
  qed
qed

lemma FL1_prirel_prirel:
  assumes "prirel p x Z"
    shows "\<exists>Y. prirel p x Y \<and> Y \<le> Z"
  using assms
proof (induct p x Z rule:prirel.induct)
  case (1 p A Z)
  then show ?case
    apply auto
     apply (case_tac A, auto, case_tac Z, auto)
  using "1.prems" by blast+
next
  case (2 p A Z zz)
  then show ?case 
    by auto
next
  case (3 p A aa Z)
  then show ?case 
    by auto
next
  case (4 p A aa Z zz)
  then obtain C where C:"prirel p aa C \<and> C \<le> zz"
    using prirel.simps(4) by blast
  then have "(prirelacc p (acceptance A) (acceptance Z)) \<and> event(A) = event(Z)"
    using "4.prems"(1) prirel.simps(4) by blast
  then show ?case using 4 C
  proof (cases "acceptance(A) = \<bullet>")
    case A_is_bullet:True
    then show ?thesis 
    proof (cases "acceptance(Z) = \<bullet>")
      case True
      then show ?thesis using 4 A_is_bullet apply auto
        apply (intro exI[where x="(\<bullet>,event(Z))\<^sub>\<F>\<^sub>\<L> #\<^sub>\<F>\<^sub>\<L> C"], auto)
        by (simp_all add:C)
    next
      case False
      then show ?thesis using 4 A_is_bullet apply auto
         apply (intro exI[where x="(\<bullet>,event(Z))\<^sub>\<F>\<^sub>\<L> #\<^sub>\<F>\<^sub>\<L> C"], auto)
          apply (simp_all add:C)
        apply (intro exI[where x="(acceptance(Z),event(Z))\<^sub>\<F>\<^sub>\<L> #\<^sub>\<F>\<^sub>\<L> C"], auto)
          apply (simp_all add:C)
        by (simp add: less_eq_aevent_def)
    qed
  next
    case A_not_bullet:False
    then show ?thesis using 4
      apply auto
          apply (intro exI[where x="(acceptance(Z),event(Z))\<^sub>\<F>\<^sub>\<L> #\<^sub>\<F>\<^sub>\<L> C"], auto)
      using C apply blast
      apply (cases A, auto)
       apply (simp add: less_eq_aevent_def)
    using C by blast
  qed
qed

lemma FL1_prirel:
  assumes "s \<le> t" "prirel p t Z" "Z \<in> P" "FL1 P"
  shows "\<exists>Z. prirel p s Z \<and> Z \<in> P"
  using assms 
  by (meson FL1_def prirel_prirel_for_FL1)

end