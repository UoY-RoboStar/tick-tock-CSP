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
  ((prirelacc p (acceptance A) (acceptance Z)) \<and> (prirel p aa zz) \<and> event(A) = event(Z) \<and>
      (maximal(p,event(A)) 
       \<or> 
      (acceptance(Z) \<noteq> \<bullet> \<and> \<not>(\<exists>b. b \<in>\<^sub>\<F>\<^sub>\<L> acceptance(Z) \<and> event(A) <\<^sup>*p b))
       \<or>
      acceptance(A) \<noteq> \<bullet>))"

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
  using Collect_cong amember.simps(2) prirelacc.elims(2) apply fastforce
  using prirelacc.elims(3) by fastforce

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
       that of Roscoe. \<close>

lemma
  "prirel p (A #\<^sub>\<F>\<^sub>\<L> aa) (Z #\<^sub>\<F>\<^sub>\<L> zz) 
  = 
  ((prirel p aa zz) \<and> event(A) = event(Z) \<and>
    ((maximal(p,event(A)) \<and> acceptance(A) = \<bullet>)
    \<or>
    (\<not>maximal(p,event(A)) \<and> acceptance(A) = \<bullet> \<and> acceptance(Z) \<noteq> \<bullet> \<and> \<not>(\<exists>b. b \<in>\<^sub>\<F>\<^sub>\<L> acceptance(Z) \<and> event(A) <\<^sup>*p b))
    \<or>
    (acceptance(A) \<noteq> \<bullet> \<and> acceptance(Z) \<noteq> \<bullet> \<and> acceptance(A) = [{a. a \<in>\<^sub>\<F>\<^sub>\<L> acceptance(Z) \<and> \<not>(\<exists>b. b\<in>\<^sub>\<F>\<^sub>\<L> acceptance(Z) \<and> a <\<^sup>*p b)}]\<^sub>\<F>\<^sub>\<L>)
    ))
  "
proof -
  have "
    ((prirel p aa zz) \<and> event(A) = event(Z) \<and>
    ((maximal(p,event(A)) \<and> acceptance(A) = \<bullet>)
    \<or>
    (\<not>maximal(p,event(A)) \<and> acceptance(A) = \<bullet> \<and> acceptance(Z) \<noteq> \<bullet> \<and> \<not>(\<exists>b. b \<in>\<^sub>\<F>\<^sub>\<L> acceptance(Z) \<and> event(A) <\<^sup>*p b))
    \<or>
    (acceptance(A) \<noteq> \<bullet> \<and> acceptance(Z) \<noteq> \<bullet> \<and> acceptance(A) = [{a. a \<in>\<^sub>\<F>\<^sub>\<L> acceptance(Z) \<and> \<not>(\<exists>b. b\<in>\<^sub>\<F>\<^sub>\<L> acceptance(Z) \<and> a <\<^sup>*p b)}]\<^sub>\<F>\<^sub>\<L>)
    ))
  =
    ((prirelacc p (acceptance A) (acceptance Z)) \<and> (prirel p aa zz) \<and> event(A) = event(Z) \<and>
    (acceptance(A) = \<bullet> \<and>
       (maximal(p,event(A))
        \<or>
       (\<not>maximal(p,event(A)) \<and> acceptance(Z) \<noteq> \<bullet> \<and> \<not>(\<exists>b. b \<in>\<^sub>\<F>\<^sub>\<L> acceptance(Z) \<and> event(A) <\<^sup>*p b)))
     \<or>
     (acceptance(A) \<noteq> \<bullet> \<and> acceptance(Z) \<noteq> \<bullet>)))"
    using prirelacc_acceptances_eq by auto
  also have "... =
    ((prirelacc p (acceptance A) (acceptance Z)) \<and> (prirel p aa zz) \<and> event(A) = event(Z) \<and>
      (acceptance(A) = \<bullet> \<and> (maximal(p,event(A)) \<or> acceptance(Z) \<noteq> \<bullet> \<and> \<not>(\<exists>b. b \<in>\<^sub>\<F>\<^sub>\<L> acceptance(Z) \<and> event(A) <\<^sup>*p b))
     \<or>
     (acceptance(A) \<noteq> \<bullet>)))"
    using acceptance_not_bullet_imp_prirelacc by auto
  also have "... =
    ((prirelacc p (acceptance A) (acceptance Z)) \<and> (prirel p aa zz) \<and> event(A) = event(Z) \<and>
      ((maximal(p,event(A)) \<or> acceptance(Z) \<noteq> \<bullet> \<and> \<not>(\<exists>b. b \<in>\<^sub>\<F>\<^sub>\<L> acceptance(Z) \<and> event(A) <\<^sup>*p b))
     \<or>
     (acceptance(A) \<noteq> \<bullet>)))"
    by auto
  also have "... =
    ((prirelacc p (acceptance A) (acceptance Z)) \<and> (prirel p aa zz) \<and> event(A) = event(Z) \<and>
      (maximal(p,event(A)) 
       \<or> 
      (acceptance(Z) \<noteq> \<bullet> \<and> \<not>(\<exists>b. b \<in>\<^sub>\<F>\<^sub>\<L> acceptance(Z) \<and> event(A) <\<^sup>*p b))
       \<or>
      acceptance(A) \<noteq> \<bullet>))"
    using maximal_not_exists_higher by auto
  also have "... =
    ((prirelacc p (acceptance A) (acceptance Z)) \<and> (prirel p aa zz) \<and> event(A) = event(Z)
       \<and> \<not>(\<exists>b. b \<in>\<^sub>\<F>\<^sub>\<L> acceptance(Z) \<and> event(A) <\<^sup>*p b) \<and>
      (maximal(p,event(A)) 
       \<or> 
      (acceptance(Z) \<noteq> \<bullet>)
       \<or>
      acceptance(A) \<noteq> \<bullet>))"
    apply auto
    using maximal_not_exists_higher apply blast
    using prirelacc_acceptance_not_bullet_imp by fastforce
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
  = ((prirelaccAlt p (acceptance A) (acceptance Z)) \<and> (prirelAlt p aa zz) \<and> event(A) = event(Z)
      \<and> (acceptance(Z) = \<bullet> \<longrightarrow> maximal(p,event(A))))"

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
    apply (case_tac Z, auto, case_tac A, auto)
   apply (case_tac A, auto)
  oops

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
  apply (case_tac Za, auto)
  by (smt amember.elims(2) prirelaccAlt.simps(4) prirelaccAlt_imp_prirelacc prirelacc_acceptance_not_bullet_imp)

lemma prirelaccAlt_eq_event_imp_priority_choice:
  assumes "(prirelaccAlt p (acceptance A) (acceptance Z))" "event(A) = event(Z)"
  shows "\<not>(\<exists>b. b \<in>\<^sub>\<F>\<^sub>\<L> acceptance(Z) \<and> event(A) <\<^sup>*p b)"
  using assms apply auto
  apply (cases A, auto, cases Z, auto)
   apply (metis acceptance_event acceptance_set amember.simps(1) prirelaccAlt_imp_prirelacc prirelacc_acceptance_not_bullet_imp)
  by (cases Z, auto, case_tac a, auto)

(*
lemma prirelacc_to_prirelaccAlt_refl:
  assumes "prirelacc p A Z"
  shows "prirelaccAlt p A A"
  using assms by (induct p A A rule:prirelaccAlt.induct, auto)
*)

(*
lemma prirel_to_prirelAlt_refl:
  assumes "prirel p A Z"
  shows "prirelAlt p A A"
  nitpick
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
*)

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
      by (metis acceptance.simps(3) eq_iff less_eq_acceptance.elims(2) less_eq_fltrace.simps(2) prirel.simps(1))
  next
    case (AEvent x z)
    then obtain C where C:"prirel p z C \<and> C \<le> zz"
      by auto
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
              apply (metis (no_types, lifting) acceptance_set less_eq_acceptance.simps(3) less_eq_aevent_def prirelacc.elims(3) prirelacc_acceptances_eq x_less_eq_A)
              using prirelacc_acceptance_not_bullet_imp by fastforce
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
       apply (simp add: less_eq_aevent_def)
    using C by blast
  qed
qed

(*
lemma FL1_prirel_prirelAlt_prefix:
  assumes "FL1 P"
          "prirel p x Z" "Z \<in> P"
    shows "\<exists>Y. prirelAlt p x Y \<and> Y \<in> P"
  by (meson FL1_def FL1_prirel_prirelAlt assms(1) assms(2) assms(3))
*)

lemma
  assumes "prirel p x (xs &\<^sub>\<F>\<^sub>\<L> \<langle>xa,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>)" "last xs \<noteq> \<bullet>"
  shows "prirel p x xs"
  by (metis assms(1) assms(2) fltrace_concat2.simps(4) fltrace_concat2_assoc plus_acceptance.elims rev3_rev3_const2_last)

lemma prirelAlt_in_P_imp_prirel:
  assumes "prirelAlt p x Z" "Z \<in> P"
    shows "\<exists>Z. prirel p x Z \<and> Z \<in> P"
  using assms 
  using prirelAlt_imp_prirel by blast+

(*
text \<open>For prefix-closed processes then the definition pri is equivalent to priAlt\<close>

lemma FL1_pri_eq_priAlt:
  assumes "FL1 P"
  shows "pri p P = priAlt p P"
  using assms unfolding pri_def priAlt_def apply auto
   apply (simp add: FL1_prirel_prirelAlt_prefix)
  using prirelAlt_imp_prirel by blast *)

(* Likely similar to the earlier proof *)

(*
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
*)

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

lemma FL1_prirel:
  assumes "s \<le> t" "prirel p t Z" "Z \<in> P" "FL1 P"
  shows "\<exists>Z. prirel p s Z \<and> Z \<in> P"
  using assms 
  by (meson FL1_def prirel_prirel_for_FL1)

lemma pri_FL1:
  assumes "FL1 P"
  shows "FL1 (pri p P)"
  using assms unfolding FL1_def pri_def apply safe
  using FL1_prirel assms by blast

(*
lemma prirel_cons_le_add:
  assumes "prirel p A Z" "prirel p B A"
          "prirel p (X #\<^sub>\<F>\<^sub>\<L> A) (Y #\<^sub>\<F>\<^sub>\<L> Z)"
    shows "prirel p (X #\<^sub>\<F>\<^sub>\<L> B) (Y #\<^sub>\<F>\<^sub>\<L> Z)"
  oops

lemma prirel_cons_le_add:
  assumes "prirel p A Z"
          "prirel p (X #\<^sub>\<F>\<^sub>\<L> A) (Y #\<^sub>\<F>\<^sub>\<L> Z)" "x \<le> X"
    shows "prirel p (x #\<^sub>\<F>\<^sub>\<L> A) (Y #\<^sub>\<F>\<^sub>\<L> Z)"
  using assms nitpick apply auto
  apply (metis less_eq_acceptance.elims(2) less_eq_aevent_def prirelacc.simps(1))
  by (simp_all add: less_eq_aevent_def)
*)

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

(*
lemma prirel_two_acceptances_bullet:
  "prirelAlt p \<langle>A,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L> \<langle>Z,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L> \<longleftrightarrow> (event(A) = event(Z) \<and> prirelaccAlt p (acceptance A) (acceptance Z))"
  nitpick
*)
lemma prirel_two_acceptances_bullet_eq_event:
  assumes "acceptance(A) = \<bullet>"
  shows "prirel p \<langle>A,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L> \<langle>Z,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L> \<longleftrightarrow> event A = event Z"
  using assms apply auto
  nitpick
  oops

lemma prirel_two_acceptances_bullet_not_bullet:
  assumes "acceptance(A) \<noteq> \<bullet>"
  shows "prirel p \<langle>A,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L> \<langle>Z,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L> = (acceptance(Z) \<noteq> \<bullet> \<and> event A = event Z \<and> acceptance(A) = [{a. a \<in>\<^sub>\<F>\<^sub>\<L> acceptance(Z) \<and> \<not>(\<exists>b. b\<in>\<^sub>\<F>\<^sub>\<L> acceptance(Z) \<and> a <\<^sup>*p b)}]\<^sub>\<F>\<^sub>\<L>)"
  using assms apply auto
  using acceptance_not_bullet_imp_prirelacc apply force
   apply (cases A, auto, case_tac a, auto)
  using amember.elims(3) apply force
    apply (metis acceptance.distinct(1) acceptance_event acceptance_set amember.simps(2) prirelacc_acceptance_not_bullet_imp)
   by (cases Z, auto, case_tac a, auto)+

lemma prirel_less_eq_imp:
  assumes "prirel p \<langle>B,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L> \<langle>Z,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>" "A \<le> B"
  shows "prirel p \<langle>A,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L> \<langle>Z,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>"
  using assms apply auto
  apply (simp_all add:less_eq_aevent_def)
      apply (metis less_eq_acceptance.elims(2) prirelacc.simps(1))
     apply (metis less_eq_acceptance.elims(2) prirelacc.simps(1))
    apply (metis less_eq_acceptance.elims(2) prirelacc.simps(1))
   apply (cases Z, auto, cases A, auto, cases B, auto, case_tac a, auto)
  by (cases Z, auto, cases A, auto, cases B, auto, case_tac a, auto, case_tac aa, auto)

(*
lemma prirel_refl_if_any_acceptance:
  assumes "prirel p \<langle>A,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L> \<langle>Z,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>"
  shows "prirel p \<langle>A,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L> \<langle>A,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>"
  using assms nitpick apply auto
     apply (cases A, auto, case_tac a, auto)
     apply (cases Z, auto, case_tac a, auto)
    apply (cases A, cases Z, auto, case_tac a, auto, case_tac aa, auto)
   apply (cases A, cases Z, auto, case_tac aa, auto)
  oops

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
*)

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

lemma prirelAlt_acceptance_refl:
  "prirelAlt p \<langle>[{a}]\<^sub>\<F>\<^sub>\<L>\<rangle>\<^sub>\<F>\<^sub>\<L> \<langle>[{a}]\<^sub>\<F>\<^sub>\<L>\<rangle>\<^sub>\<F>\<^sub>\<L>"
  by auto

lemma prirelAlt_acceptance_refl_iff:
  "prirelAlt p x \<langle>[{a}]\<^sub>\<F>\<^sub>\<L>\<rangle>\<^sub>\<F>\<^sub>\<L> \<longleftrightarrow> x = \<langle>[{a}]\<^sub>\<F>\<^sub>\<L>\<rangle>\<^sub>\<F>\<^sub>\<L>"
  apply auto
  by (cases x, auto, case_tac x1, auto)

lemma prirelAlt_bullet_refl:
  "prirelAlt p \<langle>\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L> \<langle>\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>"
  by auto

lemma prirelAlt_bullet_refl_iff:
  "prirelAlt p x \<langle>\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L> \<longleftrightarrow> x = \<langle>\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>"
  apply auto
  by (cases x, auto, case_tac x1, auto)

lemma prirelAlt_cons_acceptance_iff:
  "prirelAlt p x (([{a}]\<^sub>\<F>\<^sub>\<L>,a)\<^sub>\<F>\<^sub>\<L> #\<^sub>\<F>\<^sub>\<L> s) \<longleftrightarrow> (\<exists>z. x = (([{a}]\<^sub>\<F>\<^sub>\<L>,a)\<^sub>\<F>\<^sub>\<L> #\<^sub>\<F>\<^sub>\<L> z) \<and> prirelAlt p z s)"
  apply auto
  apply (cases x, auto)
  by (metis Rep_aevent_inverse acceptance.rep_eq event.rep_eq first.simps(1) prirelAlt.simps(1) prirelAlt_acceptance_refl_iff prod.collapse)

(*
lemma prirelAlt_cons_bullet_iff:
  "prirelAlt p x ((\<bullet>,a)\<^sub>\<F>\<^sub>\<L> #\<^sub>\<F>\<^sub>\<L> s) \<longleftrightarrow> (\<exists>z. x = ((\<bullet>,a)\<^sub>\<F>\<^sub>\<L> #\<^sub>\<F>\<^sub>\<L> z) \<and> prirelAlt p z s)"
  apply auto
  apply (cases x, auto)
  by (metis Rep_aevent_inverse acceptance.rep_eq acceptance_not_bullet_imp_prirelacc acceptance_set event.rep_eq prirelaccAlt_imp_prirelacc prod.collapse)
*)

lemma FL1_some_prirelAlt:
  assumes "s \<in> P" "FL1 P"
  shows "\<exists>Z s. prirelAlt p s Z \<and> Z \<in> P"
  using assms apply (rule_tac x="\<langle>\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>" in exI)
  by (simp add: prirelAlt_bullet_refl_iff)

lemma prirel_rhs_singleton_iff:
  "prirel p x \<langle>[{a}]\<^sub>\<F>\<^sub>\<L>\<rangle>\<^sub>\<F>\<^sub>\<L> = (x = \<langle>[{a}]\<^sub>\<F>\<^sub>\<L>\<rangle>\<^sub>\<F>\<^sub>\<L>)"
  by (cases x, auto, case_tac x1, auto)

lemma prirel_cons_imp_exists:
  assumes "prirel p x (([{a}]\<^sub>\<F>\<^sub>\<L>,a)\<^sub>\<F>\<^sub>\<L> #\<^sub>\<F>\<^sub>\<L> s)"
  shows "(\<exists>z. (x = ([{a}]\<^sub>\<F>\<^sub>\<L>,a)\<^sub>\<F>\<^sub>\<L> #\<^sub>\<F>\<^sub>\<L> z \<or> x = (\<bullet>,a)\<^sub>\<F>\<^sub>\<L> #\<^sub>\<F>\<^sub>\<L> z) \<and> prirel p z s)"
  using assms
proof (induct p x s rule:prirel.induct)
  case (1 p A Z)
  then show ?case by auto
next
  case (2 p A Z zz)
  then show ?case by auto
next
  case (3 p A aa Z)
  then show ?case
    apply (cases A, cases Z, cases aa, auto)
         apply (rule exI[where x="\<langle>\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>"], case_tac x1, auto)
         apply (metis acceptance.distinct(1) amember.elims(2) fltrace.exhaust fltrace.inject(1) prirel.simps(1) prirel.simps(2) prirel_rhs_singleton_iff prirelacc.simps(1))
         apply (rule exI[where x="\<langle>\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>"], case_tac x1, auto)
         apply (metis acceptance.distinct(1) amember.elims(2) fltrace.exhaust fltrace.inject(1) prirel.simps(1) prirel.simps(2) prirel_rhs_singleton_iff prirelacc.simps(1))
         apply (rule exI[where x="\<langle>\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>"], case_tac x1, auto)
         apply (metis acceptance.distinct(1) amember.elims(2) fltrace.exhaust fltrace.inject(1) prirel.simps(1) prirel.simps(2) prirel_rhs_singleton_iff prirelacc.simps(1))
      apply (cases aa, auto, case_tac x1, auto)
    
    apply (metis "3.prems" acceptance.simps(3) amember.elims(2) fltrace.inject(1) prirel.simps(1) prirel_cons_imp2 prirel_rhs_singleton_iff)
   
     apply (metis Finite_Linear_Model.last.simps(1) prirel.simps(1) prirel_rhs_singleton_iff)
   
   by (metis Finite_Linear_Model.last.simps(1) prirel.simps(1) prirel_rhs_singleton_iff)
(*     apply (rule exI[where x="\<langle>\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>"], auto)
         apply (metis acceptance.distinct(1) amember.elims(2) fltrace.exhaust fltrace.inject(1) prirel.simps(1) prirel.simps(2) prirel_rhs_singleton_iff prirelacc.simps(1))
      apply (rule_tac x="\<langle>[{a \<in> x2. \<forall>b. b \<in> x2 \<longrightarrow> \<not> a <\<^sup>*p b}]\<^sub>\<F>\<^sub>\<L>\<rangle>\<^sub>\<F>\<^sub>\<L>" in exI, auto)
         apply (metis acceptance.distinct(1) amember.elims(2) fltrace.exhaust fltrace.inject(1) prirel.simps(1) prirel.simps(2) prirel_rhs_singleton_iff prirelacc.simps(1))
    apply (metis acceptance.distinct(1) amember.elims(2) fltrace.inject(1) prirel.simps(1) prirel_rhs_singleton_iff)
    by (metis fltrace.inject(1) prirel.simps(1) prirel_rhs_singleton_iff)*)
next
  case (4 p A aa Z zz)
  then show ?case
    apply (cases A, cases Z, auto)
    by (metis Finite_Linear_Model.last.simps(1) prirel.simps(1) prirel_rhs_singleton_iff)+
qed

lemma prirel_cons_iff_exists:
  "prirel p x (([{a}]\<^sub>\<F>\<^sub>\<L>,a)\<^sub>\<F>\<^sub>\<L> #\<^sub>\<F>\<^sub>\<L> s) 
   = 
   (\<exists>z. (x = ([{a}]\<^sub>\<F>\<^sub>\<L>,a)\<^sub>\<F>\<^sub>\<L> #\<^sub>\<F>\<^sub>\<L> z \<or> x = (\<bullet>,a)\<^sub>\<F>\<^sub>\<L> #\<^sub>\<F>\<^sub>\<L> z) \<and> prirel p z s)"
  apply auto
  using prirel_cons_imp_exists
  by (simp add: prirel_cons_imp_exists)

lemma prirel_cons_bullet_iff_exists:
  "prirel p x ((\<bullet>,a)\<^sub>\<F>\<^sub>\<L> #\<^sub>\<F>\<^sub>\<L> s) 
   = 
   (\<exists>z. x = (\<bullet>,a)\<^sub>\<F>\<^sub>\<L> #\<^sub>\<F>\<^sub>\<L> z \<and> maximal(p,a) \<and> prirel p z s)"
  apply auto
   apply (cases x, auto)
  apply (case_tac x21, auto, case_tac aa, auto)
   apply (case_tac x21, auto, case_tac aa, auto)
  by (case_tac x21, auto, case_tac aa, auto)

lemma priAlt_PrefixAlt_eq_PrefixAlt_priAlt:
  assumes "FL1 P"
  shows "pri p (PrefixAlt a P) = (PrefixAlt a (pri p P))"
  unfolding PrefixAlt_def pri_def prefixH_def apply auto
  apply (auto simp add:prirel_rhs_singleton_iff)
         apply (metis FL0_FL1_bullet_in FL0_def assms empty_iff prirel.simps(1) prirelacc.simps(1)) 
  apply (metis FL0_FL1_bullet_in_so acceptance.exhaust assms fltrace.exhaust prirel.simps(1) prirel.simps(3) prirelacc.simps(3))
   apply (meson prirel_cons_imp_exists)
      apply (meson prirel_cons_bullet_iff_exists)
  apply (meson prirel_rhs_singleton_iff)
  using prirel.simps(1) prirelacc.simps(1) apply blast
     apply (metis prirel_cons_iff_exists)
  by force+

lemma pri_Prefix_eq_Prefix_pri:
  shows "pri p (a \<rightarrow>\<^sub>\<F>\<^sub>\<L> P) = (a \<rightarrow>\<^sub>\<F>\<^sub>\<L> (pri p P))"
  unfolding Prefix_def pri_def prefixH_def apply auto
         apply (simp add: prirel_rhs_singleton_iff)
  apply (metis acceptance.exhaust fltrace.exhaust prirel.simps(1) prirel.simps(3) prirelacc.simps(3))
  apply (meson prirel_cons_imp_exists)
  apply (meson prirel_cons_bullet_iff_exists)
  apply force
  apply force
   apply (metis prirel_cons_iff_exists)
  by (metis prirel_cons_iff_exists)

lemma prirel_singleton_set_iff:
  "prirel p A \<langle>[X]\<^sub>\<F>\<^sub>\<L>\<rangle>\<^sub>\<F>\<^sub>\<L> = (A = \<langle>[{a. a \<in> X \<and> \<not>(\<exists>b. b \<in> X \<and> a <\<^sup>*p b)}]\<^sub>\<F>\<^sub>\<L>\<rangle>\<^sub>\<F>\<^sub>\<L>)"
  apply auto
  by (cases A, auto, case_tac x1, auto)

lemma prirel_singleton_set_iff_diff:
  "prirel p \<langle>[A]\<^sub>\<F>\<^sub>\<L>\<rangle>\<^sub>\<F>\<^sub>\<L> \<langle>[X]\<^sub>\<F>\<^sub>\<L>\<rangle>\<^sub>\<F>\<^sub>\<L> = (A = X - {a. a \<in> X \<and> (\<exists>b. b \<in> X \<and> a <\<^sup>*p b)})"
  apply safe
  apply simp_all
  by blast

lemma prirel_singleton_set_iff_diff2:
  "prirel p A \<langle>[X]\<^sub>\<F>\<^sub>\<L>\<rangle>\<^sub>\<F>\<^sub>\<L> = (A = \<langle>[X - {a. a \<in> X \<and> (\<exists>b. b \<in> X \<and> a <\<^sup>*p b)}]\<^sub>\<F>\<^sub>\<L>\<rangle>\<^sub>\<F>\<^sub>\<L>)"
  apply (cases A, auto)
  by (case_tac x1, auto)

lemma not_prirelAlt_less_eq_both_events [simp]:
  assumes "b <\<^sup>*p a" "a \<in> X" "b \<in> X"
  shows "\<not> prirel p x (([X]\<^sub>\<F>\<^sub>\<L>,b)\<^sub>\<F>\<^sub>\<L> #\<^sub>\<F>\<^sub>\<L> \<rho>)"
  using assms apply (cases x, auto)
   apply (case_tac x21, auto, case_tac aa, auto)
  apply (meson some_higher_not_maximal)
  by (case_tac x21, auto, case_tac aa, auto)

lemma prirel_cons:
  assumes "b <\<^sup>*p a" "prirel p z \<rho>"
  shows "prirel p (([{a}]\<^sub>\<F>\<^sub>\<L>,a)\<^sub>\<F>\<^sub>\<L> #\<^sub>\<F>\<^sub>\<L> z) (([{b, a}]\<^sub>\<F>\<^sub>\<L>,a)\<^sub>\<F>\<^sub>\<L> #\<^sub>\<F>\<^sub>\<L> \<rho>) \<or> prirel p ((\<bullet>,a)\<^sub>\<F>\<^sub>\<L> #\<^sub>\<F>\<^sub>\<L> z) (([{b, a}]\<^sub>\<F>\<^sub>\<L>,a)\<^sub>\<F>\<^sub>\<L> #\<^sub>\<F>\<^sub>\<L> \<rho>)"
  using assms by auto

lemma prirel_cons_also_prirel:
  assumes "prirel p s z"
  shows "prirel p ((\<bullet>,a)\<^sub>\<F>\<^sub>\<L> #\<^sub>\<F>\<^sub>\<L> s) (([{a}]\<^sub>\<F>\<^sub>\<L>,a)\<^sub>\<F>\<^sub>\<L> #\<^sub>\<F>\<^sub>\<L> z)"
  using assms by auto

lemma prirel_rel_less_eq_twoset:
  assumes "b <\<^sup>*p a" "prirel p x (([{b,a}]\<^sub>\<F>\<^sub>\<L>,a)\<^sub>\<F>\<^sub>\<L> #\<^sub>\<F>\<^sub>\<L> s)"
  shows "prirel p x (([{a}]\<^sub>\<F>\<^sub>\<L>,a)\<^sub>\<F>\<^sub>\<L> #\<^sub>\<F>\<^sub>\<L> s)"
  using assms by (cases x, simp, case_tac x21, simp, case_tac y, simp, case_tac aa, simp, force)

lemma prirel_cons_iff_exists_less_eq_twoset:
  assumes "b <\<^sup>*p a"
  shows "prirel p x (([{b,a}]\<^sub>\<F>\<^sub>\<L>,a)\<^sub>\<F>\<^sub>\<L> #\<^sub>\<F>\<^sub>\<L> s) 
   = 
   (\<exists>z. (x = ([{a}]\<^sub>\<F>\<^sub>\<L>,a)\<^sub>\<F>\<^sub>\<L> #\<^sub>\<F>\<^sub>\<L> z \<or> x = (\<bullet>,a)\<^sub>\<F>\<^sub>\<L> #\<^sub>\<F>\<^sub>\<L> z) \<and> prirel p z s)"
  using assms apply auto
  by (simp add: prirel_cons_imp_exists prirel_rel_less_eq_twoset)

lemma prirel_ExtChoice_extends:
  assumes "b <\<^sup>*p a"
  shows "(\<exists>A B X. prirel p R X \<and> ExtChoiceH A B X \<and> A \<in> (a \<rightarrow>\<^sub>\<F>\<^sub>\<L> P) \<and> B \<in> (b \<rightarrow>\<^sub>\<F>\<^sub>\<L> Q)) = (\<exists>A. prirel p R A \<and> A \<in> (a \<rightarrow>\<^sub>\<F>\<^sub>\<L> P))"
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
  apply (metis acceptance.simps(3) partialorder.less_imp_le preirelacc_a_removed prirel.simps(1) prirel_rhs_singleton_iff)
    apply (rule_tac x="([{a}]\<^sub>\<F>\<^sub>\<L>,a)\<^sub>\<F>\<^sub>\<L> #\<^sub>\<F>\<^sub>\<L> \<rho>" in exI) apply auto[1]
    apply (rule_tac x="\<langle>[{b}]\<^sub>\<F>\<^sub>\<L>\<rangle>\<^sub>\<F>\<^sub>\<L>" in exI) apply auto[1]
    apply (rule_tac x="([{b,a}]\<^sub>\<F>\<^sub>\<L>,a)\<^sub>\<F>\<^sub>\<L> #\<^sub>\<F>\<^sub>\<L> \<rho>" in exI) apply auto[1]
   apply (simp_all add: prirel_cons_iff_exists_less_eq_twoset prirel_cons_imp_exists)
  by (metis ExtChoiceH.simps(3) ExtChoiceH_sym acceptance_event acceptance_set aunion.simps(2) prirel_cons_bullet_iff_exists)
(*apply (rule_tac x="\<langle>\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>" in exI, auto, rule_tac x="\<langle>\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>" in exI, auto)
  apply (rule_tac x="(\<bullet>,a)\<^sub>\<F>\<^sub>\<L> #\<^sub>\<F>\<^sub>\<L> \<rho>" in exI, auto)
apply (rule_tac x="(\<bullet>,a)\<^sub>\<F>\<^sub>\<L> #\<^sub>\<F>\<^sub>\<L> \<rho>" in exI, auto)
  apply (rule_tac x="([{b,a}]\<^sub>\<F>\<^sub>\<L>,a)\<^sub>\<F>\<^sub>\<L> #\<^sub>\<F>\<^sub>\<L> \<rho>" in exI, auto)
  apply (simp add: prirel_cons_iff_exists_less_eq_twoset prirel_cons_imp_exists)
   apply (rule_tac x="([{a}]\<^sub>\<F>\<^sub>\<L>,a)\<^sub>\<F>\<^sub>\<L> #\<^sub>\<F>\<^sub>\<L> \<rho>" in exI, auto)
   apply (rule_tac x="\<langle>[{b}]\<^sub>\<F>\<^sub>\<L>\<rangle>\<^sub>\<F>\<^sub>\<L>" in exI, auto)
by (rule_tac x="([{b,a}]\<^sub>\<F>\<^sub>\<L>,a)\<^sub>\<F>\<^sub>\<L> #\<^sub>\<F>\<^sub>\<L> \<rho>" in exI, auto)   apply (metis (full_types) insert_commute partialorder.dual_order.strict_implies_order preirelacc_a_removed prirel.simps(1) prirel_rhs_singleton_iff prirel_singleton_set_iff)
   
apply (simp add: prirel_cons_iff_exists_less_eq_twoset prirel_cons_imp_exists)
      apply (rule_tac x="\<langle>[{a}]\<^sub>\<F>\<^sub>\<L>\<rangle>\<^sub>\<F>\<^sub>\<L>" in exI, auto, rule_tac x="\<langle>[{b}]\<^sub>\<F>\<^sub>\<L>\<rangle>\<^sub>\<F>\<^sub>\<L>" in exI, rule_tac x="\<langle>[{a,b}]\<^sub>\<F>\<^sub>\<L>\<rangle>\<^sub>\<F>\<^sub>\<L>" in exI, auto)
  apply (metis (full_types) insert_commute partialorder.dual_order.strict_implies_order preirelacc_a_removed prirel.simps(1) prirel_rhs_singleton_iff prirel_singleton_set_iff)
    apply (rule_tac x="\<langle>\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>" in exI, auto, rule_tac x="\<langle>\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>" in exI, auto)
   apply (rule_tac x="([{a}]\<^sub>\<F>\<^sub>\<L>,a)\<^sub>\<F>\<^sub>\<L> #\<^sub>\<F>\<^sub>\<L> \<rho>" in exI, auto)
   apply (rule_tac x="\<langle>[{b}]\<^sub>\<F>\<^sub>\<L>\<rangle>\<^sub>\<F>\<^sub>\<L>" in exI, auto)
apply (rule_tac x="([{b,a}]\<^sub>\<F>\<^sub>\<L>,a)\<^sub>\<F>\<^sub>\<L> #\<^sub>\<F>\<^sub>\<L> \<rho>" in exI, auto)
  apply (simp add: prirel_cons_iff_exists_less_eq_twoset prirel_cons_imp_exists)
   apply (rule_tac x="([{a}]\<^sub>\<F>\<^sub>\<L>,a)\<^sub>\<F>\<^sub>\<L> #\<^sub>\<F>\<^sub>\<L> \<rho>" in exI, auto)
   apply (rule_tac x="\<langle>[{b}]\<^sub>\<F>\<^sub>\<L>\<rangle>\<^sub>\<F>\<^sub>\<L>" in exI, auto)
by (rule_tac x="([{b,a}]\<^sub>\<F>\<^sub>\<L>,a)\<^sub>\<F>\<^sub>\<L> #\<^sub>\<F>\<^sub>\<L> \<rho>" in exI, auto)
*)
lemma pri_ExtChoice_two_prefixes:
  assumes "b <\<^sup>*p a" "FL1 P"
  shows "pri p ((a \<rightarrow>\<^sub>\<F>\<^sub>\<L> P) \<box>\<^sub>\<F>\<^sub>\<L> (b \<rightarrow>\<^sub>\<F>\<^sub>\<L> Q))
        =
        pri p (a \<rightarrow>\<^sub>\<F>\<^sub>\<L> P)"
proof -
  have "((a \<rightarrow>\<^sub>\<F>\<^sub>\<L> P) \<box>\<^sub>\<F>\<^sub>\<L> (b \<rightarrow>\<^sub>\<F>\<^sub>\<L> Q))
      =
      {X| X A B. ExtChoiceH A B X \<and> A \<in> (a \<rightarrow>\<^sub>\<F>\<^sub>\<L> P) \<and> B \<in> (b \<rightarrow>\<^sub>\<F>\<^sub>\<L> Q)}"
    unfolding ExtChoice_def by auto
  then have "pri p ((a \<rightarrow>\<^sub>\<F>\<^sub>\<L> P) \<box>\<^sub>\<F>\<^sub>\<L> (b \<rightarrow>\<^sub>\<F>\<^sub>\<L> Q))
      =
      {R|R A B X. prirel p R X \<and> ExtChoiceH A B X \<and> A \<in> (a \<rightarrow>\<^sub>\<F>\<^sub>\<L> P) \<and> B \<in> (b \<rightarrow>\<^sub>\<F>\<^sub>\<L> Q)}"
    unfolding pri_def by auto
  also have "... = {R|R A. prirel p R A \<and> A \<in> (a \<rightarrow>\<^sub>\<F>\<^sub>\<L> P)}"
    using assms(1)
    by (simp add: prirel_ExtChoice_extends)
  also have "... = pri p (a \<rightarrow>\<^sub>\<F>\<^sub>\<L> P)"
    unfolding pri_def by auto 
  then show ?thesis using calculation 
    by auto
qed

lemma pri_IntChoice_dist:
  "pri p (P \<sqinter>\<^sub>\<F>\<^sub>\<L> Q) = (pri p P) \<sqinter>\<^sub>\<F>\<^sub>\<L> (pri p Q)"
  unfolding pri_def IntChoice_def by auto

lemma
  "pri p (pri p P) = pri p P"
  unfolding pri_def apply auto
  oops

lemma
  assumes "prirel p x Z" "prirel p Z Za" "Za \<in> P" 
  shows "\<exists>Z. prirel p x Z \<and> Z \<in> P"
  oops

lemma
  assumes "\<not>a <\<^sup>*p b" "\<not>b <\<^sup>*p a"
  shows "pri p ((a \<rightarrow>\<^sub>\<F>\<^sub>\<L> P) \<box>\<^sub>\<F>\<^sub>\<L> (b \<rightarrow>\<^sub>\<F>\<^sub>\<L> P))
        =
        pri p (a \<rightarrow>\<^sub>\<F>\<^sub>\<L> P) \<box>\<^sub>\<F>\<^sub>\<L> pri p (b \<rightarrow>\<^sub>\<F>\<^sub>\<L> P)"
  using assms unfolding ExtChoice_def pri_def apply auto
  oops

lemma prirel_cons_eq_length_imp:
  assumes "prirel p (xs &\<^sub>\<F>\<^sub>\<L> \<langle>x,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>) (ys &\<^sub>\<F>\<^sub>\<L> \<langle>y,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>)" "length xs = length ys"
  shows "prirel p xs ys"
  using assms apply(induct xs ys rule:prirel.induct, auto)
  apply (case_tac A, auto)
  by (case_tac Z, auto)+

lemma prirel_cons_eq_length_imp_prirel_acceptances:
  assumes "prirel p (xs &\<^sub>\<F>\<^sub>\<L> \<langle>x,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>) (ys &\<^sub>\<F>\<^sub>\<L> \<langle>y,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>)" "length xs = length ys" "last xs = \<bullet>"
  shows "prirel p \<langle>x,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L> \<langle>y,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>"
  using assms apply(induct xs ys rule:prirel.induct, auto)
     apply (case_tac Z, auto)
    apply (case_tac Z, auto)
     apply (case_tac Z, auto)
  by (case_tac Z, auto)

lemma prirel_cons_eq_length_imp_prirel_acceptances_last_bullet:
  assumes "prirel p (xs &\<^sub>\<F>\<^sub>\<L> \<langle>x,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>) (ys &\<^sub>\<F>\<^sub>\<L> \<langle>y,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>)" "length xs = length ys" "last xs = \<bullet>"
  shows "last ys = \<bullet>"
  using assms apply(induct xs ys rule:prirel.induct, auto)
  by (case_tac Z, auto)

lemma prirel_cons_eq_length_imp_prirel_acceptances_last_bullet_eq:
  assumes "prirel p (xs &\<^sub>\<F>\<^sub>\<L> \<langle>x,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>) (ys &\<^sub>\<F>\<^sub>\<L> \<langle>y,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>)" "length xs = length ys" 
  shows "last xs = \<bullet> \<longleftrightarrow> last ys = \<bullet>"
  using assms apply(induct xs ys rule:prirel.induct, auto)
   apply (case_tac Z, auto)
  by (case_tac A, auto)

lemma prirel_cons_eq_length_imp_prirel_acceptances_last_not_bullet:
  assumes "length xs = length ys" "last xs \<noteq> \<bullet>"
  shows "prirel p (xs &\<^sub>\<F>\<^sub>\<L> \<langle>x,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>) (ys &\<^sub>\<F>\<^sub>\<L> \<langle>y,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>) = prirel p (xs) (ys)"
  using assms apply(induct xs ys rule:prirel.induct, auto)
  apply (case_tac A, auto, case_tac Z, auto)
  by (case_tac A, auto, case_tac Z, auto)

lemma prirel_cons_eq_length_imp_prirel_acceptances_eq:
  assumes "length xs = length ys" "last xs = \<bullet>" "last ys = \<bullet>" "prirel p (xs &\<^sub>\<F>\<^sub>\<L> \<langle>x\<rangle>\<^sub>\<F>\<^sub>\<L>) (ys &\<^sub>\<F>\<^sub>\<L> \<langle>y\<rangle>\<^sub>\<F>\<^sub>\<L>)"
  shows  "prirel p (\<langle>x\<rangle>\<^sub>\<F>\<^sub>\<L>) (\<langle>y\<rangle>\<^sub>\<F>\<^sub>\<L>)"
  using assms by(induct xs ys rule:prirel.induct, auto)

lemma prirel_cons_eq_length_imp_prirel_eq_prefix:
  assumes "length xs = length ys" "last xs = \<bullet>" "last ys = \<bullet>" "prirel p (xs &\<^sub>\<F>\<^sub>\<L> \<langle>x\<rangle>\<^sub>\<F>\<^sub>\<L>) (ys &\<^sub>\<F>\<^sub>\<L> \<langle>y\<rangle>\<^sub>\<F>\<^sub>\<L>)"
  shows  "prirel p xs ys"
  using assms by(induct xs ys rule:prirel.induct, auto)

lemma prirel_last_bullets_cons_imp:
  assumes "prirel p (xs &\<^sub>\<F>\<^sub>\<L> \<langle>x\<rangle>\<^sub>\<F>\<^sub>\<L>) (ys &\<^sub>\<F>\<^sub>\<L> \<langle>y\<rangle>\<^sub>\<F>\<^sub>\<L>)" "last xs = \<bullet>" "last ys = \<bullet>"
  shows "(x = \<bullet>) \<or> (\<exists>xA yA. x = [xA]\<^sub>\<F>\<^sub>\<L> \<and> y = [yA]\<^sub>\<F>\<^sub>\<L>)"
  using assms apply (induct p xs ys rule:prirel.induct, auto)
   apply (induct x y rule:prirelacc.induct, auto)
  apply (induct x y rule:prirelacc.induct, auto)
  by (cases x, auto)+

end