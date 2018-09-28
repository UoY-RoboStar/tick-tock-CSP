theory Finite_Linear_Priority

imports
  Event_Priority
  Finite_Linear_Model
begin

text \<open> The following function was part of an attempt at characterising Pri within a
       FL-model that can distinguish events that definitely happen from stable states
       from those that happen from unstable states. That is, a model that does not
       necessarily observe prefix closure. \<close>

fun priamember :: "'a prievent \<Rightarrow> 'a acceptance \<Rightarrow> bool" ("(_/ \<in>\<^sub>p _)" [51, 51] 50) where
"\<tau> \<in>\<^sub>p \<bullet> = True" |
"\<tau> \<in>\<^sub>p [X]\<^sub>\<F>\<^sub>\<L> = False" |
"\<ee>(p) \<in>\<^sub>p X = (p \<in>\<^sub>\<F>\<^sub>\<L> X)"

section \<open> Original definition \<close>

text \<open> In what follows we formalise the definition of Pri as found in 
       "Expressiveness of CSP with Priority". \<close>

fun prirelacc :: "'a partialorder \<Rightarrow> 'a acceptance \<Rightarrow> 'a acceptance \<Rightarrow> bool" where
\<comment> \<open>Any acceptance Z is related to \<bullet>.\<close>
"prirelacc p \<bullet> Z = True" |
\<comment> \<open>Any acceptance Z, that is not \<bullet>, is related to A, where A is a set that 
    contains events in Z, such that no event b in Z is of higher priority as
    given by the partial order p.\<close>
"prirelacc p A Z = (Z \<noteq> \<bullet> \<and> A = [{a. a \<in>\<^sub>\<F>\<^sub>\<L> Z \<and> \<not>(\<exists>b. b\<in>\<^sub>\<F>\<^sub>\<L>Z \<and> a <\<^sup>*p b)}]\<^sub>\<F>\<^sub>\<L>)"

text \<open> Pri is defined by the relation prirel below. The recursive case has been
       simplified in comparison to that in the paper, while the base case has
       been made clear. \<close>

fun prirel :: "'a partialorder \<Rightarrow> 'a fltrace \<Rightarrow> 'a fltrace \<Rightarrow> bool" where
\<comment> \<open>The base case of this relation is given by prirelacc. \<close>
"prirel p \<langle>A\<rangle>\<^sub>\<F>\<^sub>\<L> \<langle>Z\<rangle>\<^sub>\<F>\<^sub>\<L> = (prirelacc p A Z)" |
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
  ((prirelacc p (acceptance A) (acceptance Z)) \<and> (prirel p aa zz) \<and> event(A) = event(Z) \<and>
   \<not>(\<exists>b. b \<in>\<^sub>\<F>\<^sub>\<L> acceptance(Z) \<and> event(A) <\<^sup>*p b))"

(* I think we will be able to show that we can simplify prirel (by defining
   prirelacc as follows), so that pri(P) is equivalent for P that is healthy.

   The definition Roscoe gives is, much in the spirit of prirelacc, healthy
   by definition as it relates any Z on the RHS to bullet on the LHS when
   the event on the LHS is either maximal or, if not maximal, then .

"prirelacc p \<bullet> \<bullet> = True" |
"prirelacc p [A]\<^sub>\<F>\<^sub>\<L> [Z]\<^sub>\<F>\<^sub>\<L> = (A = {a. a \<in> Z \<and> \<not>(\<exists>b. b\<in> Z \<and> a <\<^sup>*p b)})" |
"prirelacc p X Y = False" *)

subsection \<open>Auxiliary results\<close>

lemma prirelacc_acceptances_eq:
  assumes "acceptance(A) \<noteq> \<bullet>"
          "acceptance(Z) \<noteq> \<bullet>"
    shows "(prirelacc p (acceptance A) (acceptance Z)) \<longleftrightarrow> acceptance(A) = [{a. a \<in>\<^sub>\<F>\<^sub>\<L> acceptance(Z) \<and> \<not>(\<exists>b. b\<in>\<^sub>\<F>\<^sub>\<L> acceptance(Z) \<and> a <\<^sup>*p b)}]\<^sub>\<F>\<^sub>\<L>"
  using assms apply auto
  apply (cases A, auto, cases Z, auto)
  using amember.elims(2) by fastforce

lemma acceptance_not_bullet_imp_prirelacc:
  assumes "acceptance(A) \<noteq> \<bullet>"
          "prirelacc p (acceptance A) (acceptance Z)"
    shows "acceptance(Z) \<noteq> \<bullet>"
  using assms apply auto
  apply (cases Z, auto, cases A, auto)
  by (case_tac a, auto)

lemma prirelacc_acceptance_not_bullet_imp:
  assumes "prirelacc p (acceptance A) (acceptance Z)" "acceptance(A) \<noteq> \<bullet>"
  shows "\<not>(\<exists>b. b \<in>\<^sub>\<F>\<^sub>\<L> acceptance(Z) \<and> event(A) <\<^sup>*p b)"
  using assms apply auto
  apply (cases Z, auto, cases A, auto)
  by (metis (mono_tags, lifting) acceptance.inject acceptance_not_bullet_imp_prirelacc acceptance_set amember.elims(2) mem_Collect_eq prirelacc_acceptances_eq)

lemma maximal_not_exists_higher:
  assumes "maximal(p,event(A))"
    shows "\<not>(\<exists>b. b \<in>\<^sub>\<F>\<^sub>\<L> acceptance(Z) \<and> event(A) <\<^sup>*p b)"
  using assms apply auto
  unfolding maximal_def apply (cases Z, auto)
  by (simp add: partialorder.less_le_not_le)

(*
lemma
  assumes "prirelacc p (acceptance A) (acceptance Z)" "event(A) = event(Z)"
  shows "\<not>(\<exists>b. b \<in>\<^sub>\<F>\<^sub>\<L> acceptance(Z) \<and> event(A) <\<^sup>*p b)"
  nitpick
*)

text \<open> We now show that the definition of prirel for the recursive case is just like
       that of Roscoe.

       This is a very pleasing result, in that we do not need to worry about whether an
       event has maximal priority or not. \<close>

lemma
  "prirel p (A #\<^sub>\<F>\<^sub>\<L> aa) (Z #\<^sub>\<F>\<^sub>\<L> zz) 
  = 
  ((prirel p aa zz) \<and> event(A) = event(Z) \<and>
    ((maximal(p,event(A)) \<and> acceptance(A) = \<bullet>)
    \<or>
    (\<not>maximal(p,event(A)) \<and> acceptance(A) = \<bullet> \<and> acceptance(Z) \<noteq> \<bullet> \<and> \<not>(\<exists>b. b \<in>\<^sub>\<F>\<^sub>\<L> acceptance(Z) \<and> event(A) <\<^sup>*p b))
    \<or>
    (acceptance(A) \<noteq> \<bullet> \<and> acceptance(Z) \<noteq> \<bullet> \<and> acceptance(A) = [{a. a \<in>\<^sub>\<F>\<^sub>\<L> acceptance(Z) \<and> \<not>(\<exists>b. b\<in>\<^sub>\<F>\<^sub>\<L> acceptance(Z) \<and> a <\<^sup>*p b)}]\<^sub>\<F>\<^sub>\<L>)
    \<or>
    (acceptance(A) = \<bullet> \<and> acceptance(Z) = \<bullet>)))
  "
proof -
  have "
    ((prirel p aa zz) \<and> event(A) = event(Z) \<and>
    ((maximal(p,event(A)) \<and> acceptance(A) = \<bullet>)
    \<or>
    (\<not>maximal(p,event(A)) \<and> acceptance(A) = \<bullet> \<and> acceptance(Z) \<noteq> \<bullet> \<and> \<not>(\<exists>b. b \<in>\<^sub>\<F>\<^sub>\<L> acceptance(Z) \<and> event(A) <\<^sup>*p b))
    \<or>
    (acceptance(A) \<noteq> \<bullet> \<and> acceptance(Z) \<noteq> \<bullet> \<and> acceptance(A) = [{a. a \<in>\<^sub>\<F>\<^sub>\<L> acceptance(Z) \<and> \<not>(\<exists>b. b\<in>\<^sub>\<F>\<^sub>\<L> acceptance(Z) \<and> a <\<^sup>*p b)}]\<^sub>\<F>\<^sub>\<L>)
    \<or>
    (acceptance(A) = \<bullet> \<and> acceptance(Z) = \<bullet>)))
  =
    ((prirelacc p (acceptance A) (acceptance Z)) \<and> (prirel p aa zz) \<and> event(A) = event(Z) \<and>
    (acceptance(A) = \<bullet> \<and>
       (maximal(p,event(A))
        \<or>
       (\<not>maximal(p,event(A)) \<and> acceptance(Z) \<noteq> \<bullet> \<and> \<not>(\<exists>b. b \<in>\<^sub>\<F>\<^sub>\<L> acceptance(Z) \<and> event(A) <\<^sup>*p b))
        \<or>
       (acceptance(Z) = \<bullet>))
     \<or>
     (acceptance(A) \<noteq> \<bullet> \<and> acceptance(Z) \<noteq> \<bullet>)))"
    using prirelacc_acceptances_eq by auto
  also have "... =
    ((prirelacc p (acceptance A) (acceptance Z)) \<and> (prirel p aa zz) \<and> event(A) = event(Z) \<and>
      (acceptance(A) = \<bullet> \<and> (maximal(p,event(A)) \<or> \<not>(\<exists>b. b \<in>\<^sub>\<F>\<^sub>\<L> acceptance(Z) \<and> event(A) <\<^sup>*p b))
     \<or>
     (acceptance(A) \<noteq> \<bullet>)))"
    using acceptance_not_bullet_imp_prirelacc by auto
  also have "... =
    ((prirelacc p (acceptance A) (acceptance Z)) \<and> (prirel p aa zz) \<and> event(A) = event(Z) \<and>
      ((maximal(p,event(A)) \<or> \<not>(\<exists>b. b \<in>\<^sub>\<F>\<^sub>\<L> acceptance(Z) \<and> event(A) <\<^sup>*p b))
     \<or>
     (acceptance(A) \<noteq> \<bullet>)))"
    by auto
  also have "... =
    ((prirelacc p (acceptance A) (acceptance Z)) \<and> (prirel p aa zz) \<and> event(A) = event(Z) \<and>
      (\<not>(\<exists>b. b \<in>\<^sub>\<F>\<^sub>\<L> acceptance(Z) \<and> event(A) <\<^sup>*p b)
     \<or>
     (acceptance(A) \<noteq> \<bullet>)))"
    using maximal_not_exists_higher by blast
  also have "... =
    ((prirelacc p (acceptance A) (acceptance Z)) \<and> (prirel p aa zz) \<and> event(A) = event(Z) \<and>
      \<not>(\<exists>b. b \<in>\<^sub>\<F>\<^sub>\<L> acceptance(Z) \<and> event(A) <\<^sup>*p b))"
    using prirelacc_acceptance_not_bullet_imp by blast
  then show ?thesis
    using calculation by auto
qed

definition pri :: "'a partialorder \<Rightarrow> 'a fltraces \<Rightarrow> 'a fltraces" where
"pri p F = {A|A Z. prirel p A Z \<and> Z \<in> F}"

section \<open> Revised definition \<close>

text \<open> It turns out that for healthy processes (FL1) the definition of prirel and prirelacc
       can be simplified further. \<close>

text \<open> Because processes are FL1, there is no implicit need to relate every acceptance to \<bullet>,
       rather we can consider just two cases, where both acceptances are \<bullet>, or where they are
       both sets. \<close>

fun prirelaccAlt :: "'a partialorder \<Rightarrow> 'a acceptance \<Rightarrow> 'a acceptance \<Rightarrow> bool" where
"prirelaccAlt p \<bullet> \<bullet> = True" |
"prirelaccAlt p [A]\<^sub>\<F>\<^sub>\<L> [Z]\<^sub>\<F>\<^sub>\<L> = (A = {a. a \<in> Z \<and> \<not>(\<exists>b. b\<in> Z \<and> a <\<^sup>*p b)})" |
"prirelaccAlt p X Y = False"

fun prirelAlt :: "'a partialorder \<Rightarrow> 'a fltrace \<Rightarrow> 'a fltrace \<Rightarrow> bool" where
"prirelAlt p \<langle>A\<rangle>\<^sub>\<F>\<^sub>\<L> \<langle>Z\<rangle>\<^sub>\<F>\<^sub>\<L> = (prirelaccAlt p A Z)" |
"prirelAlt p \<langle>A\<rangle>\<^sub>\<F>\<^sub>\<L> (Z #\<^sub>\<F>\<^sub>\<L> zz) = False" |
"prirelAlt p (A #\<^sub>\<F>\<^sub>\<L> aa) \<langle>Z\<rangle>\<^sub>\<F>\<^sub>\<L> = False" |
"prirelAlt p (A #\<^sub>\<F>\<^sub>\<L> aa) (Z #\<^sub>\<F>\<^sub>\<L> zz) 
  = ((prirelaccAlt p (acceptance A) (acceptance Z)) \<and> (prirelAlt p aa zz) \<and> event(A) = event(Z))"

text \<open>Observe, that, in general, the recursive case for the relation is not equivalent. \<close>

lemma
  "prirel p (A #\<^sub>\<F>\<^sub>\<L> aa) (Z #\<^sub>\<F>\<^sub>\<L> zz) 
  = 
  ((prirelAlt p aa zz) \<and> event(A) = event(Z) \<and> prirelaccAlt p (acceptance A) (acceptance Z))"
  nitpick[expect=genuine]
  oops

definition priAlt :: "'a partialorder \<Rightarrow> 'a fltraces \<Rightarrow> 'a fltraces" where
"priAlt p F = {A|A Z. prirelAlt p A Z \<and> Z \<in> F}"

lemma prirel_concatFL_acceptance1:
  assumes "prirel p x xs"
  shows "prirel p x (xs &\<^sub>\<F>\<^sub>\<L> \<langle>xa\<rangle>\<^sub>\<F>\<^sub>\<L>)"
  using assms apply (induct p x xs rule:prirel.induct, auto)
  apply (case_tac xa, auto)
  by (metis plus_acceptance.elims prirelacc.simps(1) prirelacc.simps(2))

(*
lemma prirel_concatFL_acceptance2:
  assumes "prirel p x xs"
  shows "prirel p x (xs &\<^sub>\<F>\<^sub>\<L> \<langle>xa,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>)"
  using assms apply (induct p x xs rule:prirel.induct, auto)
  apply (case_tac Z, auto)
  by (case_tac A, auto)
*)

lemma prirelaccAlt_imp_prirelacc:
  assumes "prirelaccAlt p x y"
  shows "prirelacc p x y"
  using assms by (induct p x y rule:prirelaccAlt.induct, auto)

lemma prirelAlt_imp_prirel:
  assumes "prirelAlt p x Z"
  shows "prirel p x Z"
  using assms apply (induct p x Z rule:prirel.induct, auto)
  using prirelaccAlt_imp_prirelacc apply auto
  by (smt amember.elims(2) prirelaccAlt.simps(4) prirelaccAlt_imp_prirelacc prirelacc_acceptance_not_bullet_imp)

lemma prirelaccAlt_eq_event_imp_priority_choice:
  assumes "(prirelaccAlt p (acceptance A) (acceptance Z))" "event(A) = event(Z)"
  shows "\<not>(\<exists>b. b \<in>\<^sub>\<F>\<^sub>\<L> acceptance(Z) \<and> event(A) <\<^sup>*p b)"
  using assms apply auto
  apply (cases A, auto, cases Z, auto)
   apply (metis acceptance_event acceptance_set amember.simps(1) prirelaccAlt_imp_prirelacc prirelacc_acceptance_not_bullet_imp)
  by (cases Z, auto, case_tac a, auto)

lemma prirelacc_to_prirelaccAlt_refl:
  assumes "prirelacc p A Z"
  shows "prirelaccAlt p A A"
  using assms by (induct p A A rule:prirelaccAlt.induct, auto)

lemma prirel_to_prirelAlt_refl:
  assumes "prirel p A Z"
  shows "prirelAlt p A A"
  using assms apply (induct p A Z rule:prirelAlt.induct, auto)
  by (simp add: prirelacc_to_prirelaccAlt_refl)+

lemma acceptance_prirelacc_prirelaccAlt_case0:
  assumes "acceptance A \<noteq> \<bullet>"
          "prirelacc p (acceptance A) (acceptance Z)"
    shows "prirelaccAlt p (acceptance A) [{a. a \<in>\<^sub>\<F>\<^sub>\<L> acceptance Z}]\<^sub>\<F>\<^sub>\<L>"
  using assms by (cases A, auto, case_tac a, auto)

(* TODO: Generalise these results, this is cheeky. *)

lemma acceptance_prirelaccAlt_prirelaccAlt_case0:
  assumes "acceptance A \<noteq> \<bullet>"
          "prirelaccAlt p (acceptance A) (acceptance Z)"
    shows "prirelaccAlt p (acceptance A) [{a. a \<in>\<^sub>\<F>\<^sub>\<L> acceptance Z}]\<^sub>\<F>\<^sub>\<L>"
  using assms
  using acceptance_prirelacc_prirelaccAlt_case0 prirelaccAlt_imp_prirelacc by fastforce

lemma FL1_prirel_prirelAlt:
  assumes "prirel p x Z"
    shows "\<exists>Y. prirelAlt p x Y \<and> Y \<le> Z"
  using assms
proof (induct p x Z rule:prirel.induct)
  case (1 p A Z)
  then show ?case
    apply auto
    apply (case_tac A, safe, case_tac Z, safe)
      apply (meson order_refl prirelAlt.simps(1) prirelaccAlt.simps(1))
    using less_eq_acceptance.simps(1) less_eq_fltrace.simps(1) prirelAlt.simps(1) prirelaccAlt.simps(1) apply blast
    apply (case_tac Z, safe, simp)
    by (rule exI[where x="\<langle>Z\<rangle>\<^sub>\<F>\<^sub>\<L>"], simp)
next
  case (2 p A Z zz)
  then show ?case 
    by auto
   (* apply (case_tac A, safe, case_tac Z, safe)
    using prirelAlt.simps(1) prirelaccAlt.simps(1) apply fastforce
    using prirelAlt.simps(1) apply fastforce
    apply (rule exI[where x="\<langle>acceptance Z\<rangle>\<^sub>\<F>\<^sub>\<L>"], safe)
    using prirelaccAlt.elims(3) apply fastforce
    using less_eq_fltrace.simps(2) by blast *)
next
  case (3 p A aa Z)
  then show ?case 
    by auto
next
  case (4 p A aa Z zz)
  then obtain C where C:"prirelAlt p aa C \<and> C \<le> zz"
    using prirel.simps(4) by blast
  then have "(prirelacc p (acceptance A) (acceptance Z)) \<and> event(A) = event(Z) 
              \<and> \<not>(\<exists>b. b \<in>\<^sub>\<F>\<^sub>\<L> acceptance(Z) \<and> event(A) <\<^sup>*p b)"
    using "4.prems"(1) prirel.simps(4) by blast
  then show ?case using 4 C
  proof (cases "acceptance(A) = \<bullet>")
    case True
    then show ?thesis using 4
      apply (intro exI[where x="(\<bullet>,event(Z))\<^sub>\<F>\<^sub>\<L> #\<^sub>\<F>\<^sub>\<L> C"], auto)
      using C apply blast
      using C by blast
  next
    case A_not_bullet:False
    then show ?thesis using 4
      proof (cases "acceptance(Z) = \<bullet>")
        case True
        then show ?thesis using 4 A_not_bullet
          apply (intro exI[where x="([{a. a \<in>\<^sub>\<F>\<^sub>\<L> acceptance(Z) \<and> \<not>(\<exists>b. b\<in>\<^sub>\<F>\<^sub>\<L> acceptance(Z) \<and> a <\<^sup>*p b)}]\<^sub>\<F>\<^sub>\<L>,event(Z))\<^sub>\<F>\<^sub>\<L> #\<^sub>\<F>\<^sub>\<L> C"], auto)
          apply (smt Collect_cong Rep_aevent_inverse acceptance.rep_eq acceptance_not_bullet_imp_prirelacc event.rep_eq prirelacc_acceptances_eq prirelacc_to_prirelaccAlt_refl prod.collapse)
          using C apply blast
          apply (smt acceptance_event acceptance_not_bullet_imp_prirelacc amember.simps(2) event_in_acceptance mem_Collect_eq)
          using acceptance_not_bullet_imp_prirelacc apply force
          using C by blast
      next
        case False
        then show ?thesis using 4 A_not_bullet
          apply (intro exI[where x="([{a. a \<in>\<^sub>\<F>\<^sub>\<L> acceptance(Z)}]\<^sub>\<F>\<^sub>\<L>,event(Z))\<^sub>\<F>\<^sub>\<L> #\<^sub>\<F>\<^sub>\<L> C"], auto)
          using acceptance_prirelacc_prirelaccAlt_case0 apply force
          using C apply blast
          apply (cases Z, auto, case_tac a, auto)
          using C by blast
      qed
  qed
qed

lemma FL1_prirel_prirelAlt_prefix:
  assumes "FL1 P"
          "prirel p x Z" "Z \<in> P"
    shows "\<exists>Y. prirelAlt p x Y \<and> Y \<in> P"
  by (meson FL1_def FL1_prirel_prirelAlt assms(1) assms(2) assms(3))

lemma
  assumes "prirel p x (xs &\<^sub>\<F>\<^sub>\<L> \<langle>xa,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>)" "last xs \<noteq> \<bullet>"
  shows "prirel p x xs"
  by (metis assms(1) assms(2) fltrace_concat2.simps(4) fltrace_concat2_assoc plus_acceptance.elims rev3_rev3_const2_last)

lemma prirelAlt_in_P_imp_prirel:
  assumes "prirelAlt p x Z" "Z \<in> P"
    shows "\<exists>Z. prirel p x Z \<and> Z \<in> P"
  using assms 
  using prirelAlt_imp_prirel by blast+

text \<open>For prefix-closed processes then the definition pri is equivalent to priAlt\<close>

lemma FL1_pri_eq_priAlt:
  assumes "FL1 P"
  shows "pri p P = priAlt p P"
  using assms unfolding pri_def priAlt_def apply auto
   apply (simp add: FL1_prirel_prirelAlt_prefix)
  using prirelAlt_imp_prirel by blast

(* Likely similar to the earlier proof *)

lemma prirelAlt_prefix_exists:
  assumes "s \<le> t"
          "prirelAlt p t Z"
    shows "\<exists>Y. prirelAlt p s Y \<and> Y \<le> Z"
  using assms
proof (induct p t Z arbitrary:s rule:prirelAlt.induct)
  case (1 p A Z)
  then show ?case 
    apply (cases s, auto)
    apply (cases A, auto, cases Z, auto)
    using "1.prems"(2) less_eq_acceptance.elims(2) apply blast
    by (metis fltrace_trans less_eq_acceptance.elims(2) order_refl prefixFL_induct2 prirelAlt.simps(1) prirelaccAlt.simps(1))
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
    then show ?case using 4
      apply (cases x, auto)
      using prirelAlt.simps(1) prirelaccAlt.simps(1) apply fastforce
      by (metis acceptance.distinct(1) acceptance.simps(3) eq_iff less_eq_acceptance.elims(2) less_eq_fltrace.simps(2) prirelAlt.simps(1))
  next
    case (AEvent x z)
    then obtain C where C:"prirelAlt p z C \<and> C \<le> zz"
      by auto
    then have x_less_eq_A:"x \<le> A"
      using AEvent by auto
    then show ?case using 4 AEvent
       proof (cases "acceptance(x) = \<bullet>")
         case True
         then show ?thesis using 4 x_less_eq_A
            apply (intro exI[where x="(\<bullet>,event(Z))\<^sub>\<F>\<^sub>\<L> #\<^sub>\<F>\<^sub>\<L> C"], auto)
           using C apply blast
             apply (simp add: less_eq_aevent_def)+
           using C by blast
       next
         case x_not_bullet:False
         then show ?thesis using 4
           proof (cases "acceptance(Z) = \<bullet>")
             case True
             then show ?thesis using 4 x_not_bullet
              apply (intro exI[where x="([{a. a \<in>\<^sub>\<F>\<^sub>\<L> acceptance(Z) \<and> \<not>(\<exists>b. b\<in>\<^sub>\<F>\<^sub>\<L> acceptance(Z) \<and> a <\<^sup>*p b)}]\<^sub>\<F>\<^sub>\<L>,event(Z))\<^sub>\<F>\<^sub>\<L> #\<^sub>\<F>\<^sub>\<L> C"], auto)
                   apply (metis less_eq_acceptance.simps(2) less_eq_aevent_def prirelaccAlt.elims(2) prirelaccAlt.elims(3) prirelaccAlt.simps(1) prirelaccAlt.simps(4) x_less_eq_A)
               using C apply blast
               apply (metis less_eq_acceptance.elims(2) less_eq_aevent_def prirelaccAlt.elims(2) prirelaccAlt.simps(1) prirelaccAlt.simps(4) x_less_eq_A)
               apply (metis less_eq_acceptance.elims(2) less_eq_aevent_def prirelaccAlt.elims(2) prirelaccAlt.simps(1) prirelaccAlt.simps(4) x_less_eq_A)
               using C by blast
           next
             case False
             then have x_eq_A:"x = A"
               by (metis dual_order.antisym less_eq_acceptance.elims(2) less_eq_aevent_def x_less_eq_A x_not_bullet)
             then show ?thesis using False 4 x_not_bullet
              apply (intro exI[where x="([{a. a \<in>\<^sub>\<F>\<^sub>\<L> acceptance(Z)}]\<^sub>\<F>\<^sub>\<L>,event(Z))\<^sub>\<F>\<^sub>\<L> #\<^sub>\<F>\<^sub>\<L> C"], auto)
               using acceptance_prirelaccAlt_prirelaccAlt_case0 x_eq_A apply force
               using C apply blast
                apply (cases Z, auto, case_tac a, auto)
               using C by blast
           qed
       qed
  qed
qed


lemma FL1_priAlt:
  assumes "FL1 P"
          "t \<in> priAlt p P" "s \<le> t"
    shows "s \<in> priAlt p P"
  using assms 
  unfolding priAlt_def apply auto
  by (meson FL1_def prirelAlt_prefix_exists)

lemma priAlt_FL1_closed:
  assumes "FL1 P"
  shows "FL1 (priAlt p P)"
  using assms
  using FL1_def FL1_priAlt by blast

lemma priAlt_mono:
  assumes "P \<subseteq> Q"
  shows "priAlt p P \<subseteq> priAlt p Q"
  using assms unfolding priAlt_def by auto

lemma pri_mono:
  assumes "P \<subseteq> Q"
  shows "pri p P \<subseteq> pri p Q"
  using assms unfolding pri_def by auto

lemma bullet_in_pri:
  assumes "FL0 P" "FL1 P"
  shows "\<langle>\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L> \<in> pri p P"
  using assms unfolding FL0_def pri_def apply auto
  using FL0_FL1_bullet_in assms(1) prirel.simps(1) prirelacc.simps(1) by blast

lemma pri_FL0:
  assumes "FL0 P" "FL1 P"
  shows "FL0 (pri p P)"
  using assms FL0_def
  using bullet_in_pri by fastforce

lemma pri_FL1:
  assumes "FL1 P"
  shows "FL1 (pri p P)"
  using assms unfolding FL1_def pri_def apply auto
  oops

lemma prirel_cons_le_add:
  assumes "prirel p A Z" "prirel p B A"
          "prirel p (X #\<^sub>\<F>\<^sub>\<L> A) (Y #\<^sub>\<F>\<^sub>\<L> Z)"
    shows "prirel p (X #\<^sub>\<F>\<^sub>\<L> B) (Y #\<^sub>\<F>\<^sub>\<L> Z)"
  oops

lemma prirel_cons_le_add:
  assumes "prirel p A Z"
          "prirel p (X #\<^sub>\<F>\<^sub>\<L> A) (Y #\<^sub>\<F>\<^sub>\<L> Z)" "x \<le> X"
    shows "prirel p (x #\<^sub>\<F>\<^sub>\<L> A) (Y #\<^sub>\<F>\<^sub>\<L> Z)"
  using assms apply auto
  apply (metis less_eq_acceptance.elims(2) less_eq_aevent_def prirelacc.simps(1))
  by (simp_all add: less_eq_aevent_def)

lemma prirel_cons_imp1:
  assumes "prirel p (x #\<^sub>\<F>\<^sub>\<L> y) (a #\<^sub>\<F>\<^sub>\<L> b)"
  shows "prirel p \<langle>x,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L> \<langle>a,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>"
  using assms by auto

lemma prirel_cons_imp2:
  assumes "prirel p (x #\<^sub>\<F>\<^sub>\<L> y) (a #\<^sub>\<F>\<^sub>\<L> b)"
  shows "prirel p y b"
  using assms by auto

lemma
  assumes "prirel p y b"
  shows "\<exists>a. prirel p (x #\<^sub>\<F>\<^sub>\<L> y) (a #\<^sub>\<F>\<^sub>\<L> b)"
  using assms 
  oops

lemma prirel_two_acceptances_bullet:
  "prirelAlt p \<langle>A,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L> \<langle>Z,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L> \<longleftrightarrow> (event(A) = event(Z) \<and> prirelaccAlt p (acceptance A) (acceptance Z))"
  by auto

lemma prirel_two_acceptances_bullet_eq_event:
  assumes "acceptance(A) = \<bullet>"
  shows "prirel p \<langle>A,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L> \<langle>Z,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L> \<longleftrightarrow> event A = event Z"
  using assms apply auto
  nitpick
  oops

lemma prirel_two_acceptances_bullet_not_bullet:
  assumes "acceptance(A) \<noteq> \<bullet>"
  shows "prirel p \<langle>A,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L> \<langle>Z,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L> \<longleftrightarrow> acceptance(Z) \<noteq> \<bullet> \<and> event A = event Z \<and> acceptance(A) = [{a. a \<in>\<^sub>\<F>\<^sub>\<L> acceptance(Z) \<and> \<not>(\<exists>b. b\<in>\<^sub>\<F>\<^sub>\<L> acceptance(Z) \<and> a <\<^sup>*p b)}]\<^sub>\<F>\<^sub>\<L>"
  using assms apply auto
   apply (metis amember.elims(2) event_in_acceptance prirelacc.simps(2))
   apply (cases A, auto)
   apply (smt Collect_cong acceptance_not_bullet_imp_prirelacc acceptance_set prirelacc_acceptances_eq)
  by (metis (mono_tags, lifting) amember.simps(2) assms event_in_acceptance mem_Collect_eq)

lemma prirel_less_eq_imp:
  assumes "prirel p \<langle>B,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L> \<langle>Z,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>" "A \<le> B"
  shows "prirel p \<langle>A,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L> \<langle>Z,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>"
  using assms apply auto
  by (metis less_eq_acceptance.elims(2) less_eq_aevent_def prirelacc.simps(1))+

lemma prirel_refl_if_any_acceptance:
  assumes "prirel p \<langle>A,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L> \<langle>Z,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>"
  shows "prirel p \<langle>A,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L> \<langle>A,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>"
  using assms apply auto
  using prirelaccAlt_imp_prirelacc prirelacc_to_prirelaccAlt_refl apply blast
  using prirelaccAlt_eq_event_imp_priority_choice prirelacc_to_prirelaccAlt_refl by fastforce

lemma prirel_refl_if_any:
  assumes "prirel p a z"
  shows "prirel p a a"
  using assms apply (induct p a z rule:prirel.induct)
  apply (case_tac Z, simp)
  apply (metis (full_types) acceptance.exhaust prirelacc.simps(2))
     apply (case_tac A, simp)
  apply auto
    apply (case_tac A, simp)
    apply auto
  using prirelaccAlt_imp_prirelacc prirelacc_to_prirelaccAlt_refl apply blast
  using prirelaccAlt_eq_event_imp_priority_choice prirelacc_to_prirelaccAlt_refl by fastforce

lemma
  assumes "prirel p s a" "prirel p \<langle>A,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L> \<langle>Z,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>"
  shows "prirel p (A #\<^sub>\<F>\<^sub>\<L> s) (A #\<^sub>\<F>\<^sub>\<L> a)"
  using assms 
  oops

lemma
  assumes "prirel p s a" "prirel p \<langle>B,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L> \<langle>Z,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>" "A \<le> B"
  shows "\<exists>a. prirel p (A #\<^sub>\<F>\<^sub>\<L> s) a"
  using assms 
  oops

lemma prirelacc_singleton:
  "prirelacc p [{b}]\<^sub>\<F>\<^sub>\<L> [{b}]\<^sub>\<F>\<^sub>\<L>"
  by auto

lemma preirelacc_a_removed:
  assumes "a \<le>\<^sup>*p b"
  shows "prirelacc p [{b}]\<^sub>\<F>\<^sub>\<L> [{a,b}]\<^sub>\<F>\<^sub>\<L>"
  using assms apply (simp add:my_lt_def)
  using partialorder.dual_order.antisym by auto

lemma preirelacc_pair_removed:
  assumes "a <\<^sup>*p b" "prirelacc p [X]\<^sub>\<F>\<^sub>\<L> [Y]\<^sub>\<F>\<^sub>\<L>" "a \<in> Y" "b \<in> Y"
  shows "a \<notin> X"
  using assms by (auto simp add:my_lt_def)

lemma prirel_same_from_singleton:
  shows "prirel p \<langle>([{b}]\<^sub>\<F>\<^sub>\<L>,b)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L> \<langle>([{b}]\<^sub>\<F>\<^sub>\<L>,b)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>" 
  by auto

lemma prirel_same:
  assumes "a <\<^sup>*p b" "prirel p \<langle>([X]\<^sub>\<F>\<^sub>\<L>,b)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L> \<langle>([Y]\<^sub>\<F>\<^sub>\<L>,b)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>" "b \<in> Y" "b \<in> X"
  shows "a \<notin> X" 
  using assms by auto

end