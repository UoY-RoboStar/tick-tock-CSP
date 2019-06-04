theory Finite_Linear_Ops

imports
  Finite_Linear_Model
begin

subsection \<open> Operators \<close>

definition Div :: "'e fltraces" where
"Div = {\<langle>\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>}"

lemma FL2_Div [simp]:
  "FL2 Div"
  unfolding FL2_def Div_def apply auto
  by (metis Finite_Linear_Model.last.simps(1) amember.simps(1) concat_FL_last_not_bullet_absorb last_bullet_then_last_cons)

definition Stop :: "'e fltraces" where
"Stop = {\<langle>\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>} \<union> {\<langle>[{}]\<^sub>\<F>\<^sub>\<L>\<rangle>\<^sub>\<F>\<^sub>\<L>}"

lemma Stop_is_FL2 [simp]: "FL2 Stop"
  unfolding FL2_def Stop_def apply auto
  apply (metis Finite_Linear_Model.last.simps(1) acceptance.inject amember.elims(2) concat_FL_last_not_bullet_absorb empty_iff last_bullet_then_last_cons)
  by (metis Finite_Linear_Model.last.simps(1) amember.simps(1) concat_FL_last_not_bullet_absorb last_bullet_then_last_cons)

definition prefixH :: "'e \<Rightarrow> 'e fltrace \<Rightarrow> 'e fltrace \<Rightarrow> bool" where
"prefixH a aa X = (X = \<langle>[{a}]\<^sub>\<F>\<^sub>\<L>\<rangle>\<^sub>\<F>\<^sub>\<L> \<or> X = \<langle>\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L> \<or> X = ([{a}]\<^sub>\<F>\<^sub>\<L>,a)\<^sub>\<F>\<^sub>\<L> #\<^sub>\<F>\<^sub>\<L> aa \<or> X = (\<bullet>,a)\<^sub>\<F>\<^sub>\<L> #\<^sub>\<F>\<^sub>\<L> aa)"

definition Prefix :: "'e \<Rightarrow> 'e fltraces \<Rightarrow> 'e fltraces" (infixl "\<rightarrow>\<^sub>\<F>\<^sub>\<L>" 65) where
"a \<rightarrow>\<^sub>\<F>\<^sub>\<L> P = {\<langle>\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>} \<union> {\<langle>[{a}]\<^sub>\<F>\<^sub>\<L>\<rangle>\<^sub>\<F>\<^sub>\<L>} \<union> {([{a}]\<^sub>\<F>\<^sub>\<L>,a)\<^sub>\<F>\<^sub>\<L>#\<^sub>\<F>\<^sub>\<L>\<rho>| \<rho>. \<rho> \<in> P} \<union> {(\<bullet>,a)\<^sub>\<F>\<^sub>\<L>#\<^sub>\<F>\<^sub>\<L>\<rho>| \<rho>. \<rho> \<in> P}"

definition PrefixAlt :: "'e \<Rightarrow> 'e fltraces \<Rightarrow> 'e fltraces" where
"PrefixAlt a P = {x|s x. prefixH a s x \<and> s\<in>P}"

(*
lemma eq_acceptances [simp]:
  "([{aa}]\<^sub>\<F>\<^sub>\<L>,aa)\<^sub>\<F>\<^sub>\<L> = ([{a}]\<^sub>\<F>\<^sub>\<L>,a)\<^sub>\<F>\<^sub>\<L> \<longleftrightarrow> a = aa"
  apply auto
  by (simp add: acceptance_pair_eq)

lemma unequal_acceptances [simp]:
  "([{aa}]\<^sub>\<F>\<^sub>\<L>,aa)\<^sub>\<F>\<^sub>\<L> \<noteq> (\<bullet>,a)\<^sub>\<F>\<^sub>\<L>"
  apply auto
  by (metis acceptance.distinct(1) acceptance_set amember.simps(2) singletonI)

lemma unequal_acceptances_2 [simp]:
  "(\<bullet>,a)\<^sub>\<F>\<^sub>\<L> \<noteq> ([{aa}]\<^sub>\<F>\<^sub>\<L>,aa)\<^sub>\<F>\<^sub>\<L>"
  apply auto
  by (metis acceptance.distinct(1) acceptance_set amember.simps(2) singletonI)

lemma eq_acceptances_bullet [simp]:
  "(\<bullet>,aa)\<^sub>\<F>\<^sub>\<L> = (\<bullet>,a)\<^sub>\<F>\<^sub>\<L> \<longleftrightarrow> aa = a"
  apply auto
  by (metis acceptance_event)*)

lemma Prefix_PrefixAlt_eq:
  assumes "FL0 P" "FL1 P"
  shows "Prefix a P = PrefixAlt a P"
  using assms unfolding Prefix_def PrefixAlt_def prefixH_def apply auto
  using FL0_def apply fastforce
  using FL0_def by fastforce

definition IntChoice :: "'e fltraces \<Rightarrow> 'e fltraces \<Rightarrow> 'e fltraces" (infixl "\<sqinter>\<^sub>\<F>\<^sub>\<L>" 65) where
"P \<sqinter>\<^sub>\<F>\<^sub>\<L> Q \<equiv> P \<union> Q"

fun ExtChoiceH :: "'e fltrace \<Rightarrow> 'e fltrace \<Rightarrow> 'e fltrace \<Rightarrow> bool" where
"ExtChoiceH \<langle>A\<rangle>\<^sub>\<F>\<^sub>\<L> \<langle>B\<rangle>\<^sub>\<F>\<^sub>\<L> X = (X = \<langle>A \<union>\<^sub>\<F>\<^sub>\<L> B\<rangle>\<^sub>\<F>\<^sub>\<L>)" |
"ExtChoiceH (A #\<^sub>\<F>\<^sub>\<L> aa) (B #\<^sub>\<F>\<^sub>\<L> bb) X = 
  (X = ((acceptance(A) \<union>\<^sub>\<F>\<^sub>\<L> acceptance(B),event(A))\<^sub>\<F>\<^sub>\<L> #\<^sub>\<F>\<^sub>\<L> aa)
   \<or> 
   X = ((acceptance(A) \<union>\<^sub>\<F>\<^sub>\<L> acceptance(B),event(B))\<^sub>\<F>\<^sub>\<L> #\<^sub>\<F>\<^sub>\<L> bb))" |
"ExtChoiceH \<langle>A\<rangle>\<^sub>\<F>\<^sub>\<L> (B #\<^sub>\<F>\<^sub>\<L> bb) X = 
  (X = \<langle>A \<union>\<^sub>\<F>\<^sub>\<L> acceptance(B)\<rangle>\<^sub>\<F>\<^sub>\<L> \<or> X = ((A \<union>\<^sub>\<F>\<^sub>\<L> acceptance(B),event(B))\<^sub>\<F>\<^sub>\<L> #\<^sub>\<F>\<^sub>\<L> bb))" |
"ExtChoiceH (A #\<^sub>\<F>\<^sub>\<L> aa) \<langle>B\<rangle>\<^sub>\<F>\<^sub>\<L> X = 
  (X = \<langle>acceptance(A) \<union>\<^sub>\<F>\<^sub>\<L> B\<rangle>\<^sub>\<F>\<^sub>\<L> \<or> X = ((acceptance(A) \<union>\<^sub>\<F>\<^sub>\<L> B,event(A))\<^sub>\<F>\<^sub>\<L> #\<^sub>\<F>\<^sub>\<L> aa))"

definition ExtChoice :: "'e fltraces \<Rightarrow> 'e fltraces \<Rightarrow> 'e fltraces" (infixl "\<box>\<^sub>\<F>\<^sub>\<L>" 65) where
"P \<box>\<^sub>\<F>\<^sub>\<L> Q = {X| X A B. ExtChoiceH A B X \<and> A \<in> P \<and> B \<in> Q}"

fun HideAcceptance :: "'e acceptance \<Rightarrow> 'e set \<Rightarrow> 'e acceptance" where
"HideAcceptance \<bullet> X = \<bullet>" |
"HideAcceptance [A]\<^sub>\<F>\<^sub>\<L> X = (if A \<inter> X = {} then [A]\<^sub>\<F>\<^sub>\<L> else \<bullet>)"

fun HideFL :: "'e fltrace \<Rightarrow> 'e set \<Rightarrow> 'e fltrace" where
"HideFL \<langle>A\<rangle>\<^sub>\<F>\<^sub>\<L> X = \<langle>HideAcceptance A X\<rangle>\<^sub>\<F>\<^sub>\<L>" |
"HideFL (A #\<^sub>\<F>\<^sub>\<L> aa) X = (if event(A) \<in> X then (HideFL aa X) 
                          else (HideAcceptance (acceptance(A)) X,event(A))\<^sub>\<F>\<^sub>\<L> #\<^sub>\<F>\<^sub>\<L> (HideFL aa X))"

definition Hiding :: "'e fltraces \<Rightarrow> 'e set \<Rightarrow> 'e fltraces" (infixl "\\\<^sub>\<F>\<^sub>\<L>" 65) where
"P \\\<^sub>\<F>\<^sub>\<L> X = {HideFL s X|s. s \<in> P}"

lemma ExtChoiceH_bullet:
  assumes "ExtChoiceH \<langle>\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L> B x" "B \<in> P" "FL1 P"
  shows "x \<in> P"
  using assms apply (cases B, auto) 
  apply (metis FL0_FL1_bullet_in_so aunion.simps(1) unionA_sym)
  using acceptance_bullet_event_FL1 by blast

lemma ExtChoiceH_emptyset:
  assumes "ExtChoiceH \<langle>[{}]\<^sub>\<F>\<^sub>\<L>\<rangle>\<^sub>\<F>\<^sub>\<L> B x" "B \<in> P" "FL1 P"
  shows "x \<in> P"
  using assms apply (cases B, auto, case_tac x21, auto)
    apply (case_tac a, auto)
    apply (simp add: aevent_less_eq_FL1)
  by (case_tac x21, auto)

(*
lemma ExtChoice_Div_zero:
  assumes "FL0 P" "FL1 P"
  shows "Div \<box>\<^sub>\<F>\<^sub>\<L> P = Div"
  using assms unfolding Div_def ExtChoice_def apply auto
   apply (simp add: ExtChoiceH_bullet_then)
  using FL0_FL1_bullet_in by force
*)

lemma ExtChoiceH_exists:
  assumes "x \<in> P"
  shows "\<exists>B. (ExtChoiceH \<langle>\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L> B x \<or> ExtChoiceH \<langle>[{}]\<^sub>\<F>\<^sub>\<L>\<rangle>\<^sub>\<F>\<^sub>\<L> B x) \<and> B \<in> P"
  using assms
proof (cases x)
  case (Acceptance x1)
  then show ?thesis
  proof (cases x1)
    case acnil
    then show ?thesis using Acceptance assms apply auto
      by (rule exI[where x="\<langle>\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>"], auto)
  next
    case (acset x2)
    then show ?thesis using Acceptance assms apply auto
      by (rule exI[where x="\<langle>[x2]\<^sub>\<F>\<^sub>\<L>\<rangle>\<^sub>\<F>\<^sub>\<L>"], auto)
  qed
next
  case (AEvent x21 x22)
  then show ?thesis 
  proof (cases "acceptance(x21) = \<bullet>")
    case True
    then show ?thesis using AEvent assms apply auto
      apply (case_tac x21, auto)
      by (rule exI[where x="((\<bullet>,event(x21))\<^sub>\<F>\<^sub>\<L> #\<^sub>\<F>\<^sub>\<L> x22)"], auto)
  next
    case acceptance_not_bullet:False
    then obtain A b where Ab:"x21 = ([A]\<^sub>\<F>\<^sub>\<L>,b)\<^sub>\<F>\<^sub>\<L> \<and> b \<in>\<^sub>\<F>\<^sub>\<L> [A]\<^sub>\<F>\<^sub>\<L>"
      by (metis Rep_aevent_inverse acceptance.rep_eq amember.elims(2) event.rep_eq event_in_acceptance prod.collapse)
    then show ?thesis 
    proof (cases "A = {}")
      case True
      then show ?thesis using acceptance_not_bullet AEvent Ab by auto
    next
      case False
      then show ?thesis using acceptance_not_bullet AEvent Ab assms
        by (intro exI[where x="(([A]\<^sub>\<F>\<^sub>\<L>,b)\<^sub>\<F>\<^sub>\<L> #\<^sub>\<F>\<^sub>\<L> x22)"], auto)
    qed
  qed
qed


lemma
  assumes "FL1 P" "x \<in> P" 
  shows "(\<exists>B. ExtChoiceH \<langle>[{}]\<^sub>\<F>\<^sub>\<L>\<rangle>\<^sub>\<F>\<^sub>\<L> B x \<and> B \<in> P) \<or> (\<exists>B. ExtChoiceH \<langle>\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L> B x \<and> B \<in> P)"
  using assms apply auto
  apply (intro exI[where x="\<langle>\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>"], auto)
  oops

lemma ExtChoiceH_triple_refl: "ExtChoiceH x x x"
  apply (induct x rule:fltrace.induct, auto)
  by (case_tac x, auto, case_tac x1a, auto, case_tac a, auto)

lemma ExtChoiceH_sym: "ExtChoiceH A B x = ExtChoiceH B A x"
  by (induct A B x rule:ExtChoiceH.induct, auto)

lemma ExtChoice_refines_double:
  "P \<box>\<^sub>\<F>\<^sub>\<L> P \<sqsubseteq>\<^sub>\<F>\<^sub>\<L> P"
  unfolding ExtChoice_def apply auto
  using ExtChoiceH_triple_refl by blast

(*
lemma
  assumes "s \<le> t" "FL1 P" "FL1 Q"
          "ExtChoiceH A B t" "A \<in> P" "B \<in> Q"
    shows "\<exists>A B. ExtChoiceH A B s \<and> A \<in> P \<and> B \<in> Q"
  using assms 
proof (induct A B t arbitrary:s rule:ExtChoiceH.induct)
  case (1 A B X)
  then show ?case 
    apply auto
    apply (cases s, auto, case_tac x1, auto)
     apply (rule exI[where x="\<langle>\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>"])
     apply (rule exI[where x="\<langle>\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>"], auto)
    apply (cases A, auto, cases B, auto, cases B, auto)
    by (metis "1.prems"(4))
next
  case ExtChoiceH2:(2 A aa B bb X)
  then show ?case
  proof (induct s X rule:less_eq_fltrace.induct)
    case (1 x y)
    then show ?case using ExtChoiceH2 by auto
  next
    case (2 x y ys)
    then have "x \<le> acceptance(y)"
      using less_eq_fltrace.simps(2) by blast
    then show ?case using 2
       apply (cases x, auto)
        apply (rule exI[where x="\<langle>\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>"],rule exI[where x="\<langle>\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>"], auto)
        apply (rule exI[where x="\<langle>\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>"],rule exI[where x="\<langle>\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>"], auto)
       apply (rule exI[where x="\<langle>acceptance(A)\<rangle>\<^sub>\<F>\<^sub>\<L>"])
       apply (rule exI[where x="\<langle>acceptance(B)\<rangle>\<^sub>\<F>\<^sub>\<L>"])
       apply auto
      using less_eq_acceptance.elims(2) apply force
      using FL_cons_acceptance apply blast
      using FL_cons_acceptance apply blast
       apply (rule exI[where x="\<langle>acceptance(A)\<rangle>\<^sub>\<F>\<^sub>\<L>"])
       apply (rule exI[where x="\<langle>acceptance(B)\<rangle>\<^sub>\<F>\<^sub>\<L>"])
       apply auto
      using less_eq_acceptance.elims(2) apply force
      using FL_cons_acceptance apply blast
      using FL_cons_acceptance by blast
  next
    case (3 x xs y ys)
    have "event A \<in>\<^sub>\<F>\<^sub>\<L> (acceptance A \<union>\<^sub>\<F>\<^sub>\<L> acceptance B) \<or> acceptance A \<union>\<^sub>\<F>\<^sub>\<L> acceptance B = \<bullet>"
      by (cases A, auto, cases B, auto, case_tac a, auto, case_tac aa, auto, case_tac a, auto)
    then have "x = (acceptance A \<union>\<^sub>\<F>\<^sub>\<L> acceptance B,event A)\<^sub>\<F>\<^sub>\<L> \<or> x = (\<bullet>,event A)\<^sub>\<F>\<^sub>\<L>"
      using 3 apply auto
       apply (cases x, auto)      
      apply (metis acceptance_set amember.simps(1) dual_order.antisym less_eq_acceptance.elims(2) less_eq_aevent_def)
      apply (metis Un_iff acceptance.distinct(1) acceptance_event amember.simps(2) aunion.elims event_in_acceptance less_eq_aevent_def)
       apply (cases x, auto)      
      sledgehammer[debug=true]

      then obtain pA pB xA where pAB:
            "xA \<le> xs \<and> pA \<le> (acceptance A,event A)\<^sub>\<F>\<^sub>\<L> \<and> pB \<le> (acceptance B,event A)\<^sub>\<F>\<^sub>\<L>"
      by auto
(*    then have "x = (acceptance pA \<union>\<^sub>\<F>\<^sub>\<L> acceptance pB,event pA)\<^sub>\<F>\<^sub>\<L>"
      using 3 
      apply auto
      apply (cases x, auto, case_tac a, auto, cases A, cases B, auto) *)
    then show ?case using 3
      apply auto
       apply (rule exI[where x="pA #\<^sub>\<F>\<^sub>\<L> xA"])
       apply (rule exI[where x="pB #\<^sub>\<F>\<^sub>\<L> xA"], auto)
      next
    case (4 x xs y)
    then show ?case sorry
  qed
next
  case (3 A B bb X)
  then obtain sA where sA: "sA \<le> A" by auto
  then show ?case using 3
    apply (cases X, auto)
     apply (rule exI[where x="\<langle>sA\<rangle>\<^sub>\<F>\<^sub>\<L>"], cases A, auto, cases sA, auto)
      apply (rule exI[where x="\<langle>\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>"], cases s, auto, case_tac x1, auto)
    apply (cases B, auto)
    apply (cases sA, auto, cases s, auto)

  proof (induct s X rule:less_eq_fltrace.induct)
    case (1 x y)
    then show ?case
      apply auto
      apply (cases x, auto)
       apply (rule exI[where x="\<langle>\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>"])
       apply (rule exI[where x="\<langle>\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>"], auto)
      apply (cases A, auto, cases B, auto, case_tac a, auto)
      by (metis "1.prems"(4))
  next
    case (2 x y ys)
    then show ?case 
      apply auto
      apply (cases x, auto)
      apply (rule exI[where x="\<langle>\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>"])
       apply (rule exI[where x="\<langle>\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>"], auto)
      apply (cases A, auto, cases B, auto, case_tac a, auto)
      by (metis ExtChoiceH.simps(3) acceptance_set amember.simps(2) aunion.simps(3))
  next
    case (3 x xs y ys)
    then show ?case
      apply auto
      apply (cases "bb = \<langle>A \<union>\<^sub>\<F>\<^sub>\<L> acceptance B\<rangle>\<^sub>\<F>\<^sub>\<L>", auto)
       apply (rule exI[where x="\<langle>A\<rangle>\<^sub>\<F>\<^sub>\<L>"], auto)
       apply (rule exI[where x="\<langle>B,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>"], auto)
      apply (cases xs, auto, case_tac x1, auto)
      apply (cases x, auto)
       apply (cases A, auto, case_tac a, auto)
        apply (simp add: less_eq_aevent_def)+
      apply (cases B, auto)
  next
    case (4 x xs y)
    then show ?case sorry
  qed
    case (Acceptance x)
    then show ?case
      apply auto
      apply (cases x, auto)
      apply (rule exI[where x="\<langle>\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>"], rule exI[where x="\<langle>\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>"], auto)
     apply (cases A, cases B, auto, cases B, auto, case_tac a, auto)
     apply (metis "3.prems"(4))
    apply (cases x, auto)
      apply (rule exI[where x="\<langle>\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>"], rule exI[where x="\<langle>\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>"], auto)
    apply (cases A, cases B, auto, cases B, auto, case_tac a, auto)
    by (metis ExtChoiceH.simps(3) acceptance_set amember.simps(2) aunion.simps(3))
  next
    case (AEvent x1a s)
    then show ?case 
    proof (cases s)
      case (Acceptance x1)
      then show ?thesis using AEvent
        apply auto
        apply (cases x1a, auto)
        apply (rule exI[where x="\<langle>A \<union>\<^sub>\<F>\<^sub>\<L> acceptance B\<rangle>\<^sub>\<F>\<^sub>\<L>"])
        apply (rule exI[where x="\<langle>B,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>"], auto)
            apply (cases B, auto, cases A, auto, case_tac a, auto)
        apply (case_tac aa, auto)
        apply (simp add: less_eq_aevent_def)
             apply (case_tac aa, auto, case_tac a, auto)
        sledgehammer[debug=true]
             apply (metis Un_iff acceptance_event acceptance_set amember.elims(2) amember.simps(2) less_eq_acceptance.simps(3) less_eq_aevent_def less_eq_fltrace.simps(1) sup.idem sup_left_commute)
        apply (cases A, auto, case_tac a, auto)
             apply (metis Un_commute Un_left_absorb acceptance.distinct(1) acceptance_event acceptance_set amember.elims(2) aunion.simps(3) eq_iff first.simps(2) less_eq_acceptance.elims(2) less_eq_acceptance.simps(2) less_eq_aevent_def unionA_sym)
        apply (case_tac a, auto)
            apply (metis Un_commute Un_left_absorb acceptance.distinct(1) acceptance_event acceptance_set amember.elims(2) aunion.simps(3) eq_iff first.simps(2) less_eq_acceptance.elims(2) less_eq_acceptance.simps(2) less_eq_aevent_def unionA_sym)

    next
      case (AEvent x21 x22)
      then show ?thesis sorry
    qed
      apply auto
      apply (cases x1a, auto, case_tac a, auto, cases A, auto)
        apply (simp_all add: less_eq_aevent_def)
       apply (cases B, auto, case_tac a, auto)
       apply (cases s, auto)
      apply (case_tac x1, auto)
    qed
next
case (4 A aa B X)
  then show ?case sorry
qed
        apply (cases s, auto)

lemma 
  assumes "FL1 P" "FL1 Q"
  shows "FL1 (P \<box>\<^sub>\<F>\<^sub>\<L> Q)"
  using assms unfolding FL1_def ExtChoice_def apply auto
*)

text \<open>Idempotency does not hold for external choice in FL.\<close>

lemma
  "P \<sqsubseteq>\<^sub>\<F>\<^sub>\<L> (P \<box>\<^sub>\<F>\<^sub>\<L> P)"
  unfolding ExtChoice_def apply auto
  nitpick[expect=genuine]
  oops

lemma ExtChoice_sym:
  "P \<box>\<^sub>\<F>\<^sub>\<L> Q = Q \<box>\<^sub>\<F>\<^sub>\<L> P"
  unfolding ExtChoice_def apply auto
  using ExtChoiceH_sym by blast+

lemma ExtChoice_unit:
  assumes "FL1 P"
  shows "Stop \<box>\<^sub>\<F>\<^sub>\<L> P = P"
  using assms unfolding ExtChoice_def Stop_def apply auto
    apply (simp add: ExtChoiceH_emptyset)
   apply (simp add: ExtChoiceH_bullet)
  using ExtChoiceH_exists
  by blast

lemma ExtChoice_dist:
  shows "P \<box>\<^sub>\<F>\<^sub>\<L> (Q \<sqinter>\<^sub>\<F>\<^sub>\<L> R) = (P \<box>\<^sub>\<F>\<^sub>\<L> Q) \<sqinter>\<^sub>\<F>\<^sub>\<L> (P \<box>\<^sub>\<F>\<^sub>\<L> R)"
  unfolding ExtChoice_def IntChoice_def by auto

text \<open>Following laws do not hold in FL.\<close>

lemma
  assumes "FL0 P" "FL0 Q" "FL0 R"
  shows "((P \<sqinter>\<^sub>\<F>\<^sub>\<L> R) \<box>\<^sub>\<F>\<^sub>\<L> (Q \<sqinter>\<^sub>\<F>\<^sub>\<L> R)) = ((P \<box>\<^sub>\<F>\<^sub>\<L> Q) \<sqinter>\<^sub>\<F>\<^sub>\<L> R)"
  nitpick[expect=genuine]
  oops

lemma
  assumes "FL0 P" "FL0 Q" "FL0 R"
  shows "P \<sqinter>\<^sub>\<F>\<^sub>\<L> (Q \<box>\<^sub>\<F>\<^sub>\<L> R) = (P \<sqinter>\<^sub>\<F>\<^sub>\<L> Q) \<box>\<^sub>\<F>\<^sub>\<L> (P \<sqinter>\<^sub>\<F>\<^sub>\<L> R)"
  nitpick[expect=genuine]
  oops

lemma a_then_Stop:
  "a \<rightarrow>\<^sub>\<F>\<^sub>\<L> Stop = {\<langle>\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>,
                  \<langle>[{a}]\<^sub>\<F>\<^sub>\<L>\<rangle>\<^sub>\<F>\<^sub>\<L>,
                  \<langle>(\<bullet>,a)\<^sub>\<F>\<^sub>\<L>,[{}]\<^sub>\<F>\<^sub>\<L>\<rangle>\<^sub>\<F>\<^sub>\<L>,
                  \<langle>(\<bullet>,a)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>,
                  \<langle>([{a}]\<^sub>\<F>\<^sub>\<L>,a)\<^sub>\<F>\<^sub>\<L>,[{}]\<^sub>\<F>\<^sub>\<L>\<rangle>\<^sub>\<F>\<^sub>\<L>,
                  \<langle>([{a}]\<^sub>\<F>\<^sub>\<L>,a)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>
                  }"
  unfolding Prefix_def Stop_def by auto

lemma Hiding_Stop:
  "Stop \\\<^sub>\<F>\<^sub>\<L> X = Stop"
  unfolding Stop_def Hiding_def apply auto
   apply (rule exI[where x="\<langle>[{}]\<^sub>\<F>\<^sub>\<L>\<rangle>\<^sub>\<F>\<^sub>\<L>"], auto)
  by (rule exI[where x="\<langle>\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>"], auto)

lemma Hiding_a_then_Stop:
  assumes "a \<notin> X"
  shows "(PrefixAlt a Stop) \\\<^sub>\<F>\<^sub>\<L> X = (PrefixAlt a Stop)"
  using assms 
  unfolding PrefixAlt_def Stop_def Hiding_def prefixH_def apply auto
         apply (rule exI[where x="\<langle>[{a}]\<^sub>\<F>\<^sub>\<L>\<rangle>\<^sub>\<F>\<^sub>\<L>"], auto)
        apply (rule exI[where x="\<langle>[{a}]\<^sub>\<F>\<^sub>\<L>\<rangle>\<^sub>\<F>\<^sub>\<L>"], auto)
       apply (rule exI[where x="\<langle>\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>"], auto)
      apply (rule exI[where x="\<langle>([{a}]\<^sub>\<F>\<^sub>\<L>,a)\<^sub>\<F>\<^sub>\<L>,[{}]\<^sub>\<F>\<^sub>\<L>\<rangle>\<^sub>\<F>\<^sub>\<L>"], auto)
     apply (rule exI[where x="\<langle>(\<bullet>,a)\<^sub>\<F>\<^sub>\<L>,[{}]\<^sub>\<F>\<^sub>\<L>\<rangle>\<^sub>\<F>\<^sub>\<L>"], auto)
    apply (rule exI[where x="\<langle>\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>"], auto)
   apply (rule exI[where x="\<langle>([{a}]\<^sub>\<F>\<^sub>\<L>,a)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>"], auto)
  by (rule exI[where x="\<langle>(\<bullet>,a)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>"], auto)

lemma Hiding_a_then_Stop2:
  "(PrefixAlt a Stop) \\\<^sub>\<F>\<^sub>\<L> {a} = Stop"
  unfolding PrefixAlt_def Hiding_def Stop_def prefixH_def apply auto
   apply (rule exI[where x="([{a}]\<^sub>\<F>\<^sub>\<L>,a)\<^sub>\<F>\<^sub>\<L> #\<^sub>\<F>\<^sub>\<L>\<langle>[{}]\<^sub>\<F>\<^sub>\<L>\<rangle>\<^sub>\<F>\<^sub>\<L>"], auto)
  by (rule exI[where x="\<langle>\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>"], auto)

lemma Hiding_a_then_P:
  assumes "FL1 P"
  shows "(PrefixAlt a P) \\\<^sub>\<F>\<^sub>\<L> {a} = P \\\<^sub>\<F>\<^sub>\<L> {a}"
  using assms unfolding PrefixAlt_def Hiding_def Stop_def prefixH_def apply auto
   apply (rule exI[where x="\<langle>\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>"], auto)
  by (rule_tac x="([{a}]\<^sub>\<F>\<^sub>\<L>,a)\<^sub>\<F>\<^sub>\<L> #\<^sub>\<F>\<^sub>\<L> s" in exI, auto)

lemma Hiding_a_then_P_event_in_set:
  assumes "FL1 P" "a \<in> X"
  shows "(PrefixAlt a P) \\\<^sub>\<F>\<^sub>\<L> X = P \\\<^sub>\<F>\<^sub>\<L> X"
  using assms unfolding PrefixAlt_def Hiding_def Stop_def prefixH_def apply auto
   apply (rule exI[where x="\<langle>\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>"], auto)
  by (rule_tac x="([{a}]\<^sub>\<F>\<^sub>\<L>,a)\<^sub>\<F>\<^sub>\<L> #\<^sub>\<F>\<^sub>\<L> s" in exI, auto)

lemma Hiding_a_then_P_event_not_in_set:
  assumes "FL1 P" "a \<notin> X"
  shows "(PrefixAlt a P) \\\<^sub>\<F>\<^sub>\<L> X = (PrefixAlt a (P \\\<^sub>\<F>\<^sub>\<L> X))"
  using assms unfolding PrefixAlt_def Hiding_def Stop_def prefixH_def apply auto
  apply (rule exI[where x="\<langle>[{a}]\<^sub>\<F>\<^sub>\<L>\<rangle>\<^sub>\<F>\<^sub>\<L>"], auto)
    apply (rule exI[where x="\<langle>\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>"], auto)
   apply (rule_tac x="([{a}]\<^sub>\<F>\<^sub>\<L>,a)\<^sub>\<F>\<^sub>\<L> #\<^sub>\<F>\<^sub>\<L> sa" in exI, auto)
  by (rule_tac x="(\<bullet>,a)\<^sub>\<F>\<^sub>\<L> #\<^sub>\<F>\<^sub>\<L> sa" in exI, auto)

lemma
  assumes "\<forall> P Q. f (P \<union> Q) = f P \<union> f Q"
  shows "\<forall> P Q. Q \<subseteq> P \<longrightarrow> f Q \<subseteq> f P"
  using assms apply auto
  by (metis UnCI Un_absorb2)

lemma
  assumes "\<forall> P Q. Q \<subseteq> P \<longrightarrow> f Q \<subseteq> f P"
  shows "\<forall> P Q. f (P \<union> Q) = f P \<union> f Q"
  using assms nitpick[expect=genuine]
  oops

end