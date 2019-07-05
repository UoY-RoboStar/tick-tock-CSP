theory Finite_Linear_Pri

imports
  "Finite_Linear_Priority"
begin

fun priacc :: "'a partialorder \<Rightarrow> 'a acceptance \<Rightarrow> 'a acceptance" ("priacc\<^sub>[\<^sub>_\<^sub>] _" [65,65]) where
"priacc\<^sub>[\<^sub>p\<^sub>](\<bullet>) = \<bullet>" |
\<comment> \<open>Any acceptance Z, that is not \<bullet>, is related to A, where A is a set that 
    contains events in Z, such that no event b in Z is of higher priority as
    given by the partial order p.\<close>
"priacc\<^sub>[\<^sub>p\<^sub>]([Z]\<^sub>\<F>\<^sub>\<L>) = [Z \<inter> {e. \<not>(\<exists>b. b\<in>Z \<and> e <\<^sup>*p b)}]\<^sub>\<F>\<^sub>\<L>"

fun pri :: "'a partialorder \<Rightarrow> 'a fltrace \<Rightarrow> 'a fltrace \<Rightarrow> bool" where
"pri p \<langle>A\<rangle>\<^sub>\<F>\<^sub>\<L> \<langle>Z\<rangle>\<^sub>\<F>\<^sub>\<L> = (A = priacc\<^sub>[\<^sub>p\<^sub>](Z))" |
"pri p \<langle>A\<rangle>\<^sub>\<F>\<^sub>\<L> (Z #\<^sub>\<F>\<^sub>\<L> \<sigma>) = False" |
"pri p (A #\<^sub>\<F>\<^sub>\<L> \<rho>) \<langle>Z\<rangle>\<^sub>\<F>\<^sub>\<L> = False" |
"pri p (A #\<^sub>\<F>\<^sub>\<L> \<rho>) (Z #\<^sub>\<F>\<^sub>\<L> \<sigma>) = 
  (acceptance A \<le> priacc\<^sub>[\<^sub>p\<^sub>](acceptance Z) \<and> (pri p \<rho> \<sigma>) \<and> event(A) = event(Z) \<and>
    (\<not> maximal(p,event(A)) \<longrightarrow> event(Z) \<in>\<^sub>\<F>\<^sub>\<L> priacc\<^sub>[\<^sub>p\<^sub>](acceptance Z)))"

syntax 
  "_pri" :: "'a fltrace \<Rightarrow> 'a partialorder \<Rightarrow> 'a fltrace \<Rightarrow> bool" ("_ pri\<^sub>[\<^sub>_\<^sub>] _" [51,51,51])

translations
  "x pri\<^sub>[\<^sub>p\<^sub>] y" == "CONST pri p x y"

definition Pri :: "'a partialorder \<Rightarrow> 'a fltraces \<Rightarrow> 'a fltraces" ("Pri\<^sub>[\<^sub>_\<^sub>] _" [51,51]) where 
"Pri\<^sub>[\<^sub>p\<^sub>] P = {\<rho>|\<sigma> \<rho>. \<rho> pri\<^sub>[\<^sub>p\<^sub>] \<sigma> \<and> \<sigma> \<in> P}"

lemma pri_mono:
  assumes "P \<subseteq> Q"
  shows "Pri p P \<subseteq> Pri p Q"
  using assms unfolding Pri_def by auto

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

lemma bullet_in_pri:
  assumes "FL0 P" "FL1 P"
  shows "\<langle>\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L> \<in> Pri p P"
  using assms unfolding FL0_def Pri_def apply auto
  using FL0_FL1_bullet_in assms(1) pri.simps(1) priacc.simps(1)
  by metis

lemma pri_FL0:
  assumes "FL0 P" "FL1 P"
  shows "FL0 (Pri p P)"
  using assms FL0_def
  using bullet_in_pri by fastforce

lemma prirel_prirel_for_FL1:
  assumes "s \<le> t"
          "pri p t Z"
    shows "\<exists>Y. pri p s Y \<and> Y \<le> Z"
  using assms
proof (induct p t Z arbitrary:s rule:pri.induct)
  case (1 p A Z)
  then show ?case 
    apply (cases s, auto)
    apply (cases A, auto, cases Z, auto)
    using "1.prems"(2) less_eq_acceptance.elims(2) 
    apply (metis bullet_left_zero2 x_le_x_concat2)
    using "1.prems"(2) less_eq_acceptance.simps(1) 
    by (metis acceptance.distinct(1) eq_iff less_eq_acceptance.elims(2) less_eq_fltrace.simps(1) pri.simps(1) priacc.simps(1))
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
    then show ?case using 4 apply auto
      apply (cases x, auto)
      apply (metis fltrace_concat2.simps(3) pri.simps(1) priacc.simps(1) x_le_x_concat2)
      apply (cases x, auto)
      apply (metis acceptance.distinct(1) eq_iff less_eq_acceptance.elims(2) less_eq_fltrace.simps(2) pri.simps(1))
      apply (cases x, auto)
      apply (metis less_eq_acceptance.simps(1) less_eq_fltrace.simps(2) pri.simps(1) priacc.simps(1))
      by (metis acceptance.distinct(1) less_eq_acceptance.elims(2) less_eq_fltrace.simps(2) order_refl pri.simps(1))
 next
    case (AEvent x z)
    then obtain C where C:"pri p z C \<and> C \<le> zz"
      by auto
    then have x_less_eq_A:"x \<le> A"
      using AEvent by auto
    then have event_x_z:"event(x) = event(Z)"
      by (metis AEvent.prems(3) less_eq_aevent_def pri.simps(4))
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
              by (simp add: eq_iff)
          next
            case False
            then show ?thesis using 4 A_not_bullet event_x_z
              apply (intro exI[where x="Z #\<^sub>\<F>\<^sub>\<L> C"], simp)
              apply (simp add: less_eq_aevent_def C)
              apply (cases x, auto, cases Z, auto)
              by (metis acceptance_set less_eq_aevent_def order.trans x_less_eq_A)+
          qed
       qed
  qed
qed

lemma FL1_prirel:
  assumes "s \<le> t" "pri p t Z" "Z \<in> P" "FL1 P"
  shows "\<exists>Z. pri p s Z \<and> Z \<in> P"
  using assms 
  by (meson FL1_def prirel_prirel_for_FL1)

lemma pri_FL1:
  assumes "FL1 P"
  shows "FL1 (Pri p P)"
  using assms unfolding FL1_def Pri_def apply safe
  using FL1_prirel assms by blast

lemma FL1_prirel_prirel:
  assumes "pri p x Z"
    shows "\<exists>Y. pri p x Y \<and> Y \<le> Z"
  using assms
proof (induct p x Z rule:pri.induct)
  case (1 p A Z)
  then show ?case by blast
next
  case (2 p A Z zz)
  then show ?case by auto
next
  case (3 p A aa Z)
  then show ?case by auto
next
  case (4 p A aa Z zz)
  then show ?case by blast
qed

lemma prirel_cons_imp1:
  assumes "pri p (x #\<^sub>\<F>\<^sub>\<L> y) (a #\<^sub>\<F>\<^sub>\<L> b)"
  shows "pri p \<langle>x,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L> \<langle>a,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>"
  using assms by auto

lemma prirel_cons_imp2:
  assumes "pri p (x #\<^sub>\<F>\<^sub>\<L> y) (a #\<^sub>\<F>\<^sub>\<L> b)"
  shows "pri p y b"
  using assms by auto

lemma acceptance_null [intro]:
  assumes "acceptance A \<le> \<bullet>"
  shows "acceptance A = \<bullet>"
  using assms by (cases A, auto, case_tac a, auto)

lemma not_bullet_less_eq_imp [simp]:
  assumes "a \<noteq> \<bullet>"
          "a \<le> x"
    shows "a = x"
  using assms 
  apply (cases a, auto)
  apply (cases x, auto)
  by presburger+
  
lemma prirel_two_acceptances_bullet_not_bullet:
  assumes "acceptance(A) \<noteq> \<bullet>"
  shows "pri p \<langle>A,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L> \<langle>Z,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L> = (acceptance(Z) \<noteq> \<bullet> \<and> event A = event Z \<and> acceptance(A) =  [{a. a \<in>\<^sub>\<F>\<^sub>\<L> acceptance(Z) \<and> \<not>(\<exists>b. b\<in>\<^sub>\<F>\<^sub>\<L> acceptance(Z) \<and> a <\<^sup>*p b)}]\<^sub>\<F>\<^sub>\<L>)"
  using assms apply auto
     apply (cases Z, auto, case_tac a, auto, cases A, auto)
     apply (simp add:Int_def)
  apply (cases A, auto, cases Z, auto, case_tac a, auto)
      apply (case_tac aa, auto, metis (mono_tags, lifting) Int_Collect)
     apply (case_tac aa, auto, metis (mono_tags, lifting) Int_Collect)
    apply (case_tac aa, auto, smt Int_Collect)
  by (cases A, auto, cases Z, auto, case_tac a, auto)+
  
lemma prirel_rhs_singleton_iff:
  "pri p x \<langle>[{a}]\<^sub>\<F>\<^sub>\<L>\<rangle>\<^sub>\<F>\<^sub>\<L> = (x = \<langle>[{a}]\<^sub>\<F>\<^sub>\<L>\<rangle>\<^sub>\<F>\<^sub>\<L>)"
  by (cases x, auto)

lemma prirel_cons_imp_exists:
  assumes "pri p x (([{a}]\<^sub>\<F>\<^sub>\<L>,a)\<^sub>\<F>\<^sub>\<L> #\<^sub>\<F>\<^sub>\<L> s)"
  shows "(\<exists>z. (x = ([{a}]\<^sub>\<F>\<^sub>\<L>,a)\<^sub>\<F>\<^sub>\<L> #\<^sub>\<F>\<^sub>\<L> z \<or> x = (\<bullet>,a)\<^sub>\<F>\<^sub>\<L> #\<^sub>\<F>\<^sub>\<L> z) \<and> pri p z s)"
  using assms
proof (induct p x s rule:pri.induct)
  case (1 p A Z)
  then show ?case by auto
next
  case (2 p A Z zz)
  then show ?case by auto
next
  case (3 p A aa Z)
  then show ?case
    apply (cases A, cases Z, cases aa, auto)
     apply (rule exI[where x="\<langle>\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>"], auto, case_tac ab, auto, metis)
    by (rule exI[where x="aa"], auto, case_tac ab, auto, metis)
next
  case (4 p A aa Z zz)
  then show ?case
    apply (cases A, cases Z, auto)
    by (metis less_eq_acceptance.elims(2))+
qed

lemma prirel_cons_iff_exists:
  "pri p x (([{a}]\<^sub>\<F>\<^sub>\<L>,a)\<^sub>\<F>\<^sub>\<L> #\<^sub>\<F>\<^sub>\<L> s) 
   = 
   (\<exists>z. (x = ([{a}]\<^sub>\<F>\<^sub>\<L>,a)\<^sub>\<F>\<^sub>\<L> #\<^sub>\<F>\<^sub>\<L> z \<or> x = (\<bullet>,a)\<^sub>\<F>\<^sub>\<L> #\<^sub>\<F>\<^sub>\<L> z) \<and> pri p z s)"
  apply auto
  using prirel_cons_imp_exists
  by (simp add: prirel_cons_imp_exists)

lemma prirel_cons_bullet_iff_exists:
  "pri p x ((\<bullet>,a)\<^sub>\<F>\<^sub>\<L> #\<^sub>\<F>\<^sub>\<L> s) 
   = 
   (\<exists>z. x = (\<bullet>,a)\<^sub>\<F>\<^sub>\<L> #\<^sub>\<F>\<^sub>\<L> z \<and> maximal(p,a) \<and> pri p z s)"
  apply auto
   apply (cases x, auto)
  by (case_tac x21, auto, case_tac aa, auto)

lemma pri_Prefix_eq_Prefix_pri:
  shows "Pri p (a \<rightarrow>\<^sub>\<F>\<^sub>\<L> P) = (a \<rightarrow>\<^sub>\<F>\<^sub>\<L> (Pri p P))"
  unfolding Prefix_def Pri_def prefixH_def apply auto
         apply (simp add: prirel_rhs_singleton_iff)
        apply (metis fltrace.exhaust pri.simps(1) pri.simps(3) priacc.simps(1))
       apply (meson prirel_cons_imp_exists)
      apply (meson prirel_cons_bullet_iff_exists)
     apply force
    apply force
   apply (metis prirel_cons_iff_exists)
  by (metis prirel_cons_iff_exists)

lemma prirel_less_eq_imp:
  assumes "pri p \<langle>B,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L> \<langle>Z,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>" "A \<le> B"
  shows "pri p \<langle>A,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L> \<langle>Z,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>"
  using assms apply auto
  apply (simp_all add:less_eq_aevent_def)
  by (metis less_eq_acceptance.elims(2))+

lemma prirel_singleton_set_iff:
  "pri p A \<langle>[X]\<^sub>\<F>\<^sub>\<L>\<rangle>\<^sub>\<F>\<^sub>\<L> = (A = \<langle>[{a. a \<in> X \<and> \<not>(\<exists>b. b \<in> X \<and> a <\<^sup>*p b)}]\<^sub>\<F>\<^sub>\<L>\<rangle>\<^sub>\<F>\<^sub>\<L>)"
  apply auto
  by (cases A, auto)

lemma prirel_singleton_set_iff_diff:
  "pri p \<langle>[A]\<^sub>\<F>\<^sub>\<L>\<rangle>\<^sub>\<F>\<^sub>\<L> \<langle>[X]\<^sub>\<F>\<^sub>\<L>\<rangle>\<^sub>\<F>\<^sub>\<L> = (A = X - {a. a \<in> X \<and> (\<exists>b. b \<in> X \<and> a <\<^sup>*p b)})"
  by auto

lemma prirel_singleton_set_iff_diff2:
  "pri p A \<langle>[X]\<^sub>\<F>\<^sub>\<L>\<rangle>\<^sub>\<F>\<^sub>\<L> = (A = \<langle>[X - {a. a \<in> X \<and> (\<exists>b. b \<in> X \<and> a <\<^sup>*p b)}]\<^sub>\<F>\<^sub>\<L>\<rangle>\<^sub>\<F>\<^sub>\<L>)"
  by (cases A, auto)

lemma not_prirelAlt_less_eq_both_events [simp]:
  assumes "b <\<^sup>*p a" "a \<in> X" "b \<in> X"
  shows "\<not> pri p x (([X]\<^sub>\<F>\<^sub>\<L>,b)\<^sub>\<F>\<^sub>\<L> #\<^sub>\<F>\<^sub>\<L> \<rho>)"
  using assms apply (cases x, auto)
   apply (case_tac x21, auto, case_tac aa, auto)
  by (meson some_higher_not_maximal)+

lemma prirel_cons:
  assumes "b <\<^sup>*p a" "pri p z \<rho>"
  shows "pri p (([{a}]\<^sub>\<F>\<^sub>\<L>,a)\<^sub>\<F>\<^sub>\<L> #\<^sub>\<F>\<^sub>\<L> z) (([{b, a}]\<^sub>\<F>\<^sub>\<L>,a)\<^sub>\<F>\<^sub>\<L> #\<^sub>\<F>\<^sub>\<L> \<rho>) \<or> pri p ((\<bullet>,a)\<^sub>\<F>\<^sub>\<L> #\<^sub>\<F>\<^sub>\<L> z) (([{b, a}]\<^sub>\<F>\<^sub>\<L>,a)\<^sub>\<F>\<^sub>\<L> #\<^sub>\<F>\<^sub>\<L> \<rho>)"
  using assms by auto

lemma prirel_cons_also_prirel:
  assumes "pri p s z"
  shows "pri p ((\<bullet>,a)\<^sub>\<F>\<^sub>\<L> #\<^sub>\<F>\<^sub>\<L> s) (([{a}]\<^sub>\<F>\<^sub>\<L>,a)\<^sub>\<F>\<^sub>\<L> #\<^sub>\<F>\<^sub>\<L> z)"
  using assms by auto

lemma prirel_rel_less_eq_twoset:
  assumes "b <\<^sup>*p a" "pri p x (([{b,a}]\<^sub>\<F>\<^sub>\<L>,a)\<^sub>\<F>\<^sub>\<L> #\<^sub>\<F>\<^sub>\<L> s)"
  shows "pri p x (([{a}]\<^sub>\<F>\<^sub>\<L>,a)\<^sub>\<F>\<^sub>\<L> #\<^sub>\<F>\<^sub>\<L> s)"
  using assms
  apply (cases x, simp) 
  apply (case_tac x21, simp, case_tac y, simp, case_tac aa, simp)
  apply safe
   apply simp_all
  by (smt IntD2 Int_insert_left insert_absorb2 insert_is_Un mem_Collect_eq sup_inf_absorb)+

lemma prirel_cons_iff_exists_less_eq_twoset:
  assumes "b <\<^sup>*p a"
  shows "pri p x (([{b,a}]\<^sub>\<F>\<^sub>\<L>,a)\<^sub>\<F>\<^sub>\<L> #\<^sub>\<F>\<^sub>\<L> s) 
   = 
   (\<exists>z. (x = ([{a}]\<^sub>\<F>\<^sub>\<L>,a)\<^sub>\<F>\<^sub>\<L> #\<^sub>\<F>\<^sub>\<L> z \<or> x = (\<bullet>,a)\<^sub>\<F>\<^sub>\<L> #\<^sub>\<F>\<^sub>\<L> z) \<and> pri p z s)"
  using assms apply auto
  by (simp add: prirel_cons_imp_exists prirel_rel_less_eq_twoset)

lemma
  assumes "R pri\<^sub>[\<^sub>p\<^sub>] \<langle>[{a}]\<^sub>\<F>\<^sub>\<L>\<rangle>\<^sub>\<F>\<^sub>\<L>" "b <\<^sup>*p a"
  shows "R pri\<^sub>[\<^sub>p\<^sub>] \<langle>[{b, a}]\<^sub>\<F>\<^sub>\<L>\<rangle>\<^sub>\<F>\<^sub>\<L>"
  using assms by (cases R, auto)

lemma prirel_ExtChoice_extends:
  assumes "b <\<^sup>*p a"
  shows "(\<exists>A B X. pri p R X \<and> ExtChoiceH A B X \<and> A \<in> (a \<rightarrow>\<^sub>\<F>\<^sub>\<L> P) \<and> B \<in> (b \<rightarrow>\<^sub>\<F>\<^sub>\<L> Q)) = (\<exists>A. pri p R A \<and> A \<in> (a \<rightarrow>\<^sub>\<F>\<^sub>\<L> P))"
  using assms unfolding Prefix_def apply (safe, simp_all)
                     apply auto[4]
                  apply (rule_tac x="\<langle>[{a}]\<^sub>\<F>\<^sub>\<L>\<rangle>\<^sub>\<F>\<^sub>\<L>" in exI) apply auto[1]
  apply (metis (no_types, lifting) partialorder.dual_order.strict_implies_order preirelacc_a_removed prirel_rhs_singleton_iff prirel_singleton_set_iff prirelacc.simps(2))
                 apply (metis prirel_cons_bullet_iff_exists some_higher_not_maximal)   
                apply (rule_tac x="\<langle>[{a}]\<^sub>\<F>\<^sub>\<L>\<rangle>\<^sub>\<F>\<^sub>\<L>" in exI) apply auto[1]
                 apply (metis (no_types, lifting) partialorder.dual_order.strict_implies_order preirelacc_a_removed prirel_rhs_singleton_iff prirel_singleton_set_iff prirelacc.simps(2))
               apply (simp_all add: prirel_cons_bullet_iff_exists some_higher_not_maximal)
 apply blast apply safe
                 apply (rule_tac x="\<langle>[{a}]\<^sub>\<F>\<^sub>\<L>\<rangle>\<^sub>\<F>\<^sub>\<L>" in exI) apply auto[1]
             apply (metis (no_types, lifting) partialorder.dual_order.strict_implies_order preirelacc_a_removed prirel_rhs_singleton_iff prirel_singleton_set_iff prirelacc.simps(2))
            apply (metis prirel_rel_less_eq_twoset)
   apply (rule_tac x="([{a}]\<^sub>\<F>\<^sub>\<L>,a)\<^sub>\<F>\<^sub>\<L> #\<^sub>\<F>\<^sub>\<L> \<rho>" in exI) apply auto[1]
            apply (simp add: prirel_rel_less_eq_twoset)
  using prirel_rel_less_eq_twoset apply fastforce
                   apply (rule_tac x="\<langle>\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>" in exI) apply auto[1]
                  apply (rule_tac x="\<langle>[{a}]\<^sub>\<F>\<^sub>\<L>\<rangle>\<^sub>\<F>\<^sub>\<L>" in exI) apply auto[1]
  apply (simp_all add: prirel_cons_bullet_iff_exists some_higher_not_maximal)
             apply (rule_tac x="\<langle>\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>" in exI) apply auto[1]
            apply (metis prirel_cons_also_prirel)
  apply (rule_tac x="\<langle>\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>" in exI) apply auto[1]
  
          apply (metis prirel_cons_also_prirel)+
     apply (rule_tac x="\<langle>\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>" in exI) apply auto[1]
     apply (rule_tac x="\<langle>\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>" in exI) apply auto[1]
    apply (rule_tac x="\<langle>[{a}]\<^sub>\<F>\<^sub>\<L>\<rangle>\<^sub>\<F>\<^sub>\<L>" in exI) apply auto[1]
  apply (rule_tac x="\<langle>[{b}]\<^sub>\<F>\<^sub>\<L>\<rangle>\<^sub>\<F>\<^sub>\<L>" in exI) apply auto[1]
  apply (cases R, auto)
   apply (rule_tac x="([{a}]\<^sub>\<F>\<^sub>\<L>,a)\<^sub>\<F>\<^sub>\<L> #\<^sub>\<F>\<^sub>\<L> \<rho>" in exI) apply auto[1]
    apply (rule_tac x="\<langle>[{b}]\<^sub>\<F>\<^sub>\<L>\<rangle>\<^sub>\<F>\<^sub>\<L>" in exI) apply auto[1]
    apply (rule_tac x="([{b,a}]\<^sub>\<F>\<^sub>\<L>,a)\<^sub>\<F>\<^sub>\<L> #\<^sub>\<F>\<^sub>\<L> \<rho>" in exI) apply auto[1]
   apply (simp_all add: prirel_cons_iff_exists_less_eq_twoset prirel_cons_imp_exists)
  by (metis ExtChoiceH.simps(3) ExtChoiceH_sym acceptance_event acceptance_set aunion.simps(2) prirel_cons_bullet_iff_exists)

lemma pri_ExtChoice_two_prefixes:
  assumes "b <\<^sup>*p a" "FL1 P"
  shows "Pri p ((a \<rightarrow>\<^sub>\<F>\<^sub>\<L> P) \<box>\<^sub>\<F>\<^sub>\<L> (b \<rightarrow>\<^sub>\<F>\<^sub>\<L> Q))
        =
        Pri p (a \<rightarrow>\<^sub>\<F>\<^sub>\<L> P)"
proof -
  have "((a \<rightarrow>\<^sub>\<F>\<^sub>\<L> P) \<box>\<^sub>\<F>\<^sub>\<L> (b \<rightarrow>\<^sub>\<F>\<^sub>\<L> Q))
      =
      {X| X A B. ExtChoiceH A B X \<and> A \<in> (a \<rightarrow>\<^sub>\<F>\<^sub>\<L> P) \<and> B \<in> (b \<rightarrow>\<^sub>\<F>\<^sub>\<L> Q)}"
    unfolding ExtChoice_def by auto
  then have "Pri p ((a \<rightarrow>\<^sub>\<F>\<^sub>\<L> P) \<box>\<^sub>\<F>\<^sub>\<L> (b \<rightarrow>\<^sub>\<F>\<^sub>\<L> Q))
      =
      {R|R A B X. pri p R X \<and> ExtChoiceH A B X \<and> A \<in> (a \<rightarrow>\<^sub>\<F>\<^sub>\<L> P) \<and> B \<in> (b \<rightarrow>\<^sub>\<F>\<^sub>\<L> Q)}"
    unfolding Pri_def by auto
  also have "... = {R|R A. pri p R A \<and> A \<in> (a \<rightarrow>\<^sub>\<F>\<^sub>\<L> P)}"
    using assms(1)
    by (simp add: prirel_ExtChoice_extends)
  also have "... = Pri p (a \<rightarrow>\<^sub>\<F>\<^sub>\<L> P)"
    unfolding Pri_def by auto 
  then show ?thesis using calculation 
    by auto
qed

lemma pri_IntChoice_dist:
  "Pri p (P \<sqinter>\<^sub>\<F>\<^sub>\<L> Q) = (Pri p P) \<sqinter>\<^sub>\<F>\<^sub>\<L> (Pri p Q)"
  unfolding Pri_def IntChoice_def by auto


lemma
  assumes "\<not>a <\<^sup>*p b" "\<not>b <\<^sup>*p a"
  shows "Pri p ((a \<rightarrow>\<^sub>\<F>\<^sub>\<L> P) \<box>\<^sub>\<F>\<^sub>\<L> (b \<rightarrow>\<^sub>\<F>\<^sub>\<L> P))
        =
        Pri p (a \<rightarrow>\<^sub>\<F>\<^sub>\<L> P) \<box>\<^sub>\<F>\<^sub>\<L> Pri p (b \<rightarrow>\<^sub>\<F>\<^sub>\<L> P)"
  using assms unfolding ExtChoice_def Pri_def apply auto
  oops

lemma prirel_cons_eq_length_imp:
  assumes "pri p (xs &\<^sub>\<F>\<^sub>\<L> \<langle>x,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>) (ys &\<^sub>\<F>\<^sub>\<L> \<langle>y,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>)" "length xs = length ys"
  shows "pri p xs ys"
  using assms apply(induct xs ys rule:pri.induct, auto)
  apply (case_tac A, auto)
  by (case_tac Z, auto)+

lemma prirel_cons_eq_length_imp_prirel_acceptances:
  assumes "pri p (xs &\<^sub>\<F>\<^sub>\<L> \<langle>x,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>) (ys &\<^sub>\<F>\<^sub>\<L> \<langle>y,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>)" "length xs = length ys" "last xs = \<bullet>"
  shows "pri p \<langle>x,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L> \<langle>y,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>"
  using assms apply(induct xs ys rule:pri.induct, auto)
  by (case_tac Z, auto)+

lemma prirel_cons_eq_length_imp_prirel_acceptances_last_bullet:
  assumes "pri p (xs &\<^sub>\<F>\<^sub>\<L> \<langle>x,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>) (ys &\<^sub>\<F>\<^sub>\<L> \<langle>y,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>)" "length xs = length ys" "last xs = \<bullet>"
  shows "last ys = \<bullet>"
  using assms apply(induct xs ys rule:pri.induct, auto)
  by (case_tac Z, auto)

lemma prirel_cons_eq_length_imp_prirel_acceptances_last_bullet_eq:
  assumes "pri p (xs &\<^sub>\<F>\<^sub>\<L> \<langle>x,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>) (ys &\<^sub>\<F>\<^sub>\<L> \<langle>y,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>)" "length xs = length ys" 
  shows "last xs = \<bullet> \<longleftrightarrow> last ys = \<bullet>"
  using assms apply(induct xs ys rule:pri.induct, auto)
   apply (case_tac Z, auto)
  by (case_tac A, auto)

lemma prirel_cons_eq_length_imp_prirel_acceptances_last_not_bullet:
  assumes "length xs = length ys" "last xs \<noteq> \<bullet>"
  shows "pri p (xs &\<^sub>\<F>\<^sub>\<L> \<langle>x,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>) (ys &\<^sub>\<F>\<^sub>\<L> \<langle>y,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>) = pri p (xs) (ys)"
  using assms apply(induct xs ys rule:pri.induct, auto)
   apply (case_tac A, auto)
  by (case_tac Z, auto)+
  
lemma prirel_cons_eq_length_imp_prirel_acceptances_eq:
  assumes "length xs = length ys" "last xs = \<bullet>" "last ys = \<bullet>" "pri p (xs &\<^sub>\<F>\<^sub>\<L> \<langle>x\<rangle>\<^sub>\<F>\<^sub>\<L>) (ys &\<^sub>\<F>\<^sub>\<L> \<langle>y\<rangle>\<^sub>\<F>\<^sub>\<L>)"
  shows  "pri p (\<langle>x\<rangle>\<^sub>\<F>\<^sub>\<L>) (\<langle>y\<rangle>\<^sub>\<F>\<^sub>\<L>)"
  using assms by(induct xs ys rule:pri.induct, auto)

lemma prirel_cons_eq_length_imp_prirel_eq_prefix:
  assumes "length xs = length ys" "last xs = \<bullet>" "last ys = \<bullet>" "pri p (xs &\<^sub>\<F>\<^sub>\<L> \<langle>x\<rangle>\<^sub>\<F>\<^sub>\<L>) (ys &\<^sub>\<F>\<^sub>\<L> \<langle>y\<rangle>\<^sub>\<F>\<^sub>\<L>)"
  shows  "pri p xs ys"
  using assms by(induct xs ys rule:pri.induct, auto)

lemma prirel_last_bullets_cons_imp:
  assumes "pri p (xs &\<^sub>\<F>\<^sub>\<L> \<langle>x\<rangle>\<^sub>\<F>\<^sub>\<L>) (ys &\<^sub>\<F>\<^sub>\<L> \<langle>y\<rangle>\<^sub>\<F>\<^sub>\<L>)" "last xs = \<bullet>" "last ys = \<bullet>"
  shows "(x = \<bullet>) \<or> (\<exists>xA yA. x = [xA]\<^sub>\<F>\<^sub>\<L> \<and> y = [yA]\<^sub>\<F>\<^sub>\<L>)"
  using assms apply (induct p xs ys rule:pri.induct, auto)
  by (cases x, auto, cases y, auto)+

lemma prirelacc_trans:
  assumes "priacc p A = Z" "priacc p Z = Y"
  shows "priacc p A = Y"
  using assms 
  by (cases A, auto)
  
lemma prirel_trans:
  assumes "pri p xs ys" "pri p ys zs"
  shows "pri p xs zs"
  using assms apply (induct p xs zs arbitrary:ys rule:pri.induct, auto)
        apply (metis fltrace.exhaust pri.simps(1) pri.simps(3) prirelacc_trans)
       apply (metis fltrace.exhaust pri.simps(2))
      apply (metis fltrace.exhaust pri.simps(3))
     apply (case_tac ysa, auto)
        apply (metis prirelacc_trans less_eq_acceptance.elims(2) priacc.simps(1))
       apply (metis prirelacc_trans less_eq_acceptance.elims(2) priacc.simps(1))
      apply (metis prirelacc_trans less_eq_acceptance.elims(2) priacc.simps(1))
     apply (metis prirelacc_trans less_eq_acceptance.elims(2) priacc.simps(1))
    apply (metis (mono_tags, hide_lams) fltrace.exhaust pri.simps(3) pri.simps(4))
   apply (case_tac ysa, auto)
  by (metis fltrace.exhaust pri.simps(2) pri.simps(4))

lemma
  assumes "pri p x Z" "pri p Z Za" "Za \<in> P" 
  shows "\<exists>Z. pri p x Z \<and> Z \<in> P"
  using assms(1) assms(2) assms(3) prirel_trans by blast

(*
lemma
  assumes "prirel p xs ys" "ys \<in> P" "FL1 P"
  shows "prirel p xs ys \<and> (\<exists>Za. prirel p ys Za \<and> Za \<in> P)"
  using assms 
  apply (induct xs ys rule:ftrace_cons_induct_both_eq_length)
  
  using assms(1) prirel_same_length apply blast
  apply (case_tac x, auto)

  using prirelAlt_bullet_refl_iff prirelAlt_imp_prirel apply blast
    apply (case_tac y, auto)
  apply (rule_tac x="\<langle>[x2a]\<^sub>\<F>\<^sub>\<L>\<rangle>\<^sub>\<F>\<^sub>\<L>" in exI, auto)
  sledgehammer*)

lemma prirel_extend_both_acceptance:
  assumes "pri p xs zs" "pri p \<langle>x\<rangle>\<^sub>\<F>\<^sub>\<L> \<langle>y\<rangle>\<^sub>\<F>\<^sub>\<L>"
  shows "pri p (xs &\<^sub>\<F>\<^sub>\<L> \<langle>x\<rangle>\<^sub>\<F>\<^sub>\<L>) (zs &\<^sub>\<F>\<^sub>\<L> \<langle>y\<rangle>\<^sub>\<F>\<^sub>\<L>)"
  using assms
  apply (induct p xs zs rule:pri.induct, auto)
  by (cases y, auto, case_tac Z, auto)

lemma prirelacc_decompose:
  assumes "priacc p xs = ys" 
  shows "\<exists>Z. priacc p xs = Z \<and> priacc p Z = ys"
  using assms by(induct p xs rule:priacc.induct, auto)

lemma priacc_less_eq_some_pri:
  assumes "(A #\<^sub>\<F>\<^sub>\<L> \<rho>) pri\<^sub>[\<^sub>p\<^sub>] Z"
  shows "acceptance A \<le> priacc\<^sub>[\<^sub>p\<^sub>] (acceptance A)"
  using assms 
  apply (cases A, auto, cases Z, auto)
  by (metis Finite_Linear_Pri.prirelacc_trans amember.simps(1) not_bullet_less_eq_imp)+

lemma
  assumes "\<rho> pri\<^sub>[\<^sub>p\<^sub>] Za" "(A #\<^sub>\<F>\<^sub>\<L> Za) pri\<^sub>[\<^sub>p\<^sub>] (Z #\<^sub>\<F>\<^sub>\<L> \<sigma>)" "acceptance A \<noteq> \<bullet>"
  shows "(A #\<^sub>\<F>\<^sub>\<L> \<rho>) pri\<^sub>[\<^sub>p\<^sub>] (A #\<^sub>\<F>\<^sub>\<L> Za)"
  using assms nitpick
  oops

lemma prirel_decompose:
  assumes "pri p xs ys" 
  shows "\<exists>Z. pri p xs Z \<and> pri p Z ys"
  using assms 
proof(induct p xs ys rule:pri.induct)
  case (1 p A Z)
  then show ?case 
    by (metis pri.simps(1) prirelacc_trans)
next
  case (2 p A Z \<sigma>)
  then show ?case
    by (cases A, auto)
next
  case (3 p A \<rho> Z)
  then show ?case 
    by (cases A, auto)
next
  case (4 p A \<rho> Z \<sigma>) (* Split proof on acceptance(A) cases *)
  then have "\<rho> pri\<^sub>[\<^sub>p\<^sub>] \<sigma>"
            "\<exists>Z. \<rho> pri\<^sub>[\<^sub>p\<^sub>] Z \<and> Z pri\<^sub>[\<^sub>p\<^sub>] \<sigma>"
    by auto
  then have "\<exists>Za. \<rho> pri\<^sub>[\<^sub>p\<^sub>] Za \<and> (A #\<^sub>\<F>\<^sub>\<L> Za) pri\<^sub>[\<^sub>p\<^sub>] (Z #\<^sub>\<F>\<^sub>\<L> \<sigma>)"
    using 4 by auto

  obtain Y where Y:"Y = ([{a. a \<in>\<^sub>\<F>\<^sub>\<L> acceptance Z \<and> (\<forall>b. b \<in>\<^sub>\<F>\<^sub>\<L> acceptance Z \<longrightarrow> \<not> a <\<^sup>*p b)}]\<^sub>\<F>\<^sub>\<L>,event Z)\<^sub>\<F>\<^sub>\<L>"
    by auto
  then have "\<exists>Za. \<rho> pri\<^sub>[\<^sub>p\<^sub>] Za \<and> (Y #\<^sub>\<F>\<^sub>\<L> Za) pri\<^sub>[\<^sub>p\<^sub>] (Z #\<^sub>\<F>\<^sub>\<L> \<sigma>)"
    using 4 apply auto

  then have "\<exists>Za. (A #\<^sub>\<F>\<^sub>\<L> \<rho>) pri\<^sub>[\<^sub>p\<^sub>] (A #\<^sub>\<F>\<^sub>\<L> Za) \<and> (A #\<^sub>\<F>\<^sub>\<L> Za) pri\<^sub>[\<^sub>p\<^sub>] (Z #\<^sub>\<F>\<^sub>\<L> \<sigma>)"
  proof -
    have "\<forall>Za. \<rho> pri\<^sub>[\<^sub>p\<^sub>] Za \<longrightarrow> (A #\<^sub>\<F>\<^sub>\<L> \<rho>) pri\<^sub>[\<^sub>p\<^sub>] (A #\<^sub>\<F>\<^sub>\<L> Za)"
      apply auto
      using 4 priacc_less_eq_some_pri apply blast
      sledgehammer
      apply (cases A, auto, cases Z, auto, case_tac a, auto, case_tac aa, auto)
    apply auto
    using 4 priacc_less_eq_some_pri apply blast
    apply (cases A, auto, cases Z, auto)
    
    apply (metis "4.prems" acceptance.distinct(1) acceptance.exhaust acceptance.inject acceptance.simps(3) acceptance_event acceptance_null acceptance_set amember.elims(1) amember.elims(2) amember.simps(2) aunion.elims not_bullet_less_eq_imp pri.simps(4) priacc_less_eq_some_pri)
    
    apply (metis "4.prems" acceptance_set amember.simps(1) not_bullet_less_eq_imp pri.simps(4) priacc.simps(1))
    apply (cases Z, auto)
    apply (rule_tac x="\<sigma>" in exI, auto, case_tac a, auto)
  sledgehammer
    apply (cases A, auto, case_tac a, auto)
    
  then show ?case using 4
    
qed
    apply (metis pri.simps(1) prirelacc_trans)
  apply (case_tac \<rho>, auto, case_tac x1, auto)
     apply (metis Finite_Linear_Pri.prirelacc_trans less_eq_acceptance.elims(2) order_refl pri.simps(4) priacc.simps(1))
    apply (metis Finite_Linear_Pri.prirelacc_trans less_eq_acceptance.elims(2) order_refl pri.simps(4) priacc.simps(1))
  apply (metis Finite_Linear_Pri.prirelacc_trans less_eq_acceptance.elims(2) less_eq_acceptance.simps(1) pri.simps(4))
  apply (rule_tac x="(([{a. a \<in>\<^sub>\<F>\<^sub>\<L> acceptance Z \<and> (\<forall>b. b \<in>\<^sub>\<F>\<^sub>\<L> acceptance Z \<longrightarrow> \<not> a <\<^sup>*pa b)}]\<^sub>\<F>\<^sub>\<L>,event Z)\<^sub>\<F>\<^sub>\<L> #\<^sub>\<F>\<^sub>\<L> Za)" in exI, auto)
      apply (case_tac A, auto, case_tac Z, auto, case_tac a, auto)
  oops (* TODO: to be continued.. *)

lemma
  assumes "pri p xs ys" "ys \<in> P" "FL1 P"
  shows "\<exists>Z. pri p xs Z \<and> (\<exists>Za. pri p Z Za \<and> Za \<in> P)"
  using assms prirel_decompose by blast

lemma pri_idem:
  "Pri p (Pri p P) = Pri p P"
  unfolding Pri_def apply auto
  using prirel_trans apply blast
  using prirel_decompose by blast


end