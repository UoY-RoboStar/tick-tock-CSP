theory CTockTick_FL
  
imports
  CTockTick
  Finite_Linear_Tick_Param
begin
  
fun flt2cttobs :: "('e cttevent) fltrace \<Rightarrow> ('e cttobs) list" where
"flt2cttobs \<langle>A\<rangle>\<^sub>\<F>\<^sub>\<L> = (if A = \<bullet> then [] else [[{z. z \<notin>\<^sub>\<F>\<^sub>\<L> A}]\<^sub>R])" |
"flt2cttobs (A #\<^sub>\<F>\<^sub>\<L> fl) = (if event(A) = Tock then
                             (if acceptance(A) \<noteq> \<bullet> then
                              ([{z. z \<notin>\<^sub>\<F>\<^sub>\<L> acceptance(A)}]\<^sub>R # [Tock]\<^sub>E # (flt2cttobs fl))
                              else []) 
                          else ([event A]\<^sub>E # flt2cttobs fl))" 

fun flt2goodTock :: "('e cttevent) fltrace \<Rightarrow> bool" where
"flt2goodTock \<langle>A\<rangle>\<^sub>\<F>\<^sub>\<L> = True" |
"flt2goodTock (A #\<^sub>\<F>\<^sub>\<L> fl) = (if acceptance(A) \<noteq> \<bullet> then (flt2goodTock fl) else
                            (if event(A) = Tock then False else (flt2goodTock fl)))" 

lemma flt2cttobs_is_cttWF:
  assumes "tickWF Tick fltrace"
  shows "cttWF (flt2cttobs fltrace)"
  using assms
  apply (induct fltrace rule:flt2cttobs.induct, auto)
  apply (case_tac A, auto, case_tac a, auto, case_tac b, auto)
  by (metis cttWF.simps(4) cttWF2.simps(1) cttWF2.simps(23) cttWF2_cttWF cttevent.exhaust flt2cttobs.simps(1))

definition fl2ctt :: "('e cttevent) fltrace set \<Rightarrow> ('e cttobs) list set" where
"fl2ctt P = {flt2cttobs fl|fl. fl \<in> P}"

lemma fl2ctt_univ_disj:
  "fl2ctt (\<Union> P) = \<Union>{fl2ctt fl| fl. fl \<in> P}"
  unfolding fl2ctt_def by auto

definition ctt2fl :: "('e cttobs) list set \<Rightarrow> ('e cttevent) fltrace set" where
"ctt2fl P = \<Union>{fl. FL1 fl \<and> (fl2ctt fl) \<subseteq> P}"

lemma ctt2fl_mono:
  assumes "P \<subseteq> Q"
  shows "ctt2fl(P) \<subseteq> ctt2fl(Q)"
  using assms unfolding ctt2fl_def by auto

lemma fl2ctt_ctt2fl_refines: "fl2ctt(ctt2fl(P)) \<subseteq> P"
  unfolding ctt2fl_def fl2ctt_def by auto

definition CTwf :: "'e cttobs list set \<Rightarrow> bool" where
  "CTwf P = (\<forall>x\<in>P. cttWF x)"

definition CT1c :: "'e cttobs list set \<Rightarrow> bool" where
  "CT1c P = (\<forall> \<rho> \<sigma>. (\<rho> \<le>\<^sub>C \<sigma> \<and> \<sigma> \<in> P) \<longrightarrow> \<rho> \<in> P)"

lemma some_x_then_nil_CT1c [simp]:
  assumes "x \<in> P" "CT1c P"
  shows "[] \<in> P"
  using assms 
  unfolding CT1c_def by force

lemma fl_le_CT1c:
  assumes "fl \<le> \<langle>[{z. z \<notin> x1}]\<^sub>\<F>\<^sub>\<L>\<rangle>\<^sub>\<F>\<^sub>\<L>" "[Ref x1] \<in> P" "CT1c P"
  shows "flt2cttobs fl \<in> P"
  using assms apply (cases fl, auto)
  apply (case_tac x1a, auto)
  by (case_tac "x2 = {z. z \<notin> x1}", auto)

lemma fl_le_CT1c_Event:
  assumes "fl \<le> \<langle>(\<bullet>,(Event ev))\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>" "[[Event ev]\<^sub>E] \<in> P" "CT1c P"
  shows "flt2cttobs fl \<in> P"
  using assms apply (cases fl, auto)
  apply (simp_all add: less_eq_aevent_def)
  apply (case_tac x1, auto)
    apply (case_tac x21, auto)
  by (case_tac x22, auto, case_tac x1, auto)+

lemma fl_le_CT1c_Tick:
  assumes "fl \<le> \<langle>(\<bullet>,Tick)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>" "[[Tick]\<^sub>E] \<in> P" "CT1c P"
  shows "flt2cttobs fl \<in> P"
  using assms apply (cases fl, auto)
     apply (simp_all add: less_eq_aevent_def)
  apply (case_tac x1, auto)
    apply (case_tac x21, auto)
   apply (case_tac a, auto)
  by (case_tac x22, auto, case_tac x1, auto)

declare cttWF_prefix_is_cttWF [simp]

lemma last_flt2cttobs_eq_ref_imp_last:
  assumes "flt2cttobs (xs) \<noteq> []" "List.last(flt2cttobs (xs)) = Ref r" 
  shows "last xs = [{x. x \<notin> r}]\<^sub>\<F>\<^sub>\<L>"
(* 
proof -
  have "xs = butlast xs &\<^sub>\<F>\<^sub>\<L> \<langle>last xs\<rangle>\<^sub>\<F>\<^sub>\<L>"
    using butlast_last_cons2_FL[symmetric] by auto
  *)
  using assms apply (induct xs rule:flt2cttobs.induct, auto)
   apply (case_tac A, auto)
  apply (case_tac A, auto)
   apply (case_tac b, auto)
     apply (metis cttobs.distinct(1) flt2cttobs.simps(1))
    apply (smt List.last.simps acceptance.distinct(1) amember.elims(2) cttobs.distinct(1) flt2cttobs.simps(1) list.discI)
   apply (metis cttobs.distinct(1) flt2cttobs.simps(1))
   apply (case_tac b, auto)
    apply (metis cttobs.distinct(1) flt2cttobs.simps(1))
  apply (case_tac fl, auto)
  apply (metis (mono_tags, lifting) Collect_cong cttobs.distinct(1) flt2cttobs.simps(1))
  by (smt cttobs.distinct(1) flt2cttobs.simps(2) last_ConsR list.discI)
  

lemma concat_ref_tock_imp_tock_in_last_of_flt2cttobs:
  assumes "ys @ [[x1]\<^sub>R] @ [[Tock]\<^sub>E] \<in> P" "CTwf P" "CT3 P"
          "ys @ [[x1]\<^sub>R] @ [[Tock]\<^sub>E] = flt2cttobs fl @ [[Tock]\<^sub>E]"
    shows "Tock \<in>\<^sub>\<F>\<^sub>\<L> last fl"
proof -
  have a:"ys @ [[x1]\<^sub>R] = flt2cttobs fl" "fl \<noteq> \<langle>\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>"
    using assms 
    by (induct fl, auto)
  then have b:"flt2cttobs fl @ [[Tock]\<^sub>E] \<in> P"
    using assms apply auto
    by (metis assms(1) assms(4))
  then have "flt2cttobs fl \<noteq> []"
    using a(1) by auto
  then show ?thesis 
    using a assms 
    proof (induct fl rule:fltrace_induct0)
      case 1
      then show ?case by auto
    next
      case (2 x xs)
      then have tock_not_in_x1:"Tock \<notin> x1"
        using assms
        by (metis CT3_def CT3_trace.simps(3) CT3_trace_cons_right append_Cons append_Nil)
      then obtain r where r:"List.last(flt2cttobs (xs &\<^sub>\<F>\<^sub>\<L> x)) = [r]\<^sub>R"
        using 2
        by (metis last_snoc)
      then have tock_not_in_r:"Tock \<notin> r"
        using 2
        by (metis cttobs.inject(2) last_snoc tock_not_in_x1)
      then have last_eq: "last (xs &\<^sub>\<F>\<^sub>\<L> x) = [{x. x \<notin> r}]\<^sub>\<F>\<^sub>\<L>"
        using r
        using "2.prems"(3)
        using "2.prems"(1) last_flt2cttobs_eq_ref_imp_last by fastforce
      then have "Tock \<in>\<^sub>\<F>\<^sub>\<L> [{x. x \<notin> r}]\<^sub>\<F>\<^sub>\<L>"
        by (simp add: tock_not_in_r)
      then show ?case using 2 last_eq by auto
    qed
  qed

(*
lemma
  assumes "e \<in>\<^sub>\<F>\<^sub>\<L> last fl"
  shows "flt2cttobs fl \<noteq> []"
  nitpick

lemma
  assumes "last xs = \<bullet>" "flt2cttobs(xs) \<noteq> []" "flt2cttobs(ys) \<noteq> []"
  shows "flt2cttobs (xs @\<^sub>\<F>\<^sub>\<L> ys) = flt2cttobs(xs) @ flt2cttobs(ys)"
  nitpick

lemma
  assumes "flt2cttobs (butlast fl) \<noteq> []" "Tock \<in>\<^sub>\<F>\<^sub>\<L> last fl"
  shows "flt2cttobs (fl @\<^sub>\<F>\<^sub>\<L> \<langle>(last fl,Tock)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>) = flt2cttobs(butlast fl) @ flt2cttobs(\<langle>(last fl,Tock)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>)"
  using assms apply (induct fl, auto)
  apply (case_tac x1a, auto, case_tac b, auto, case_tac a, auto)
*)

lemma flt2cttobs_last_tock:
  assumes "Tock \<in>\<^sub>\<F>\<^sub>\<L> last fl" "flt2goodTock fl"
  shows "flt2cttobs (fl @\<^sub>\<F>\<^sub>\<L> \<langle>(last fl,Tock)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>) = flt2cttobs fl @ [[Tock]\<^sub>E]"
  using assms
  by (induct fl rule:flt2cttobs.induct, auto)

lemma flt2cttobs_butlast_cons_eq_list_cons:
  assumes "flt2goodTock fl"
  shows "flt2cttobs (butlast fl &\<^sub>\<F>\<^sub>\<L> \<langle>y,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>) = flt2cttobs(butlast fl) @ flt2cttobs(\<langle>y,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>)"
  using assms by (induct fl, auto)

lemma flt2cttobs_acceptance_cons_eq_list_cons:
  assumes "last fl = \<bullet>" "flt2goodTock fl"
  shows "flt2cttobs (fl &\<^sub>\<F>\<^sub>\<L> \<langle>y,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>) = flt2cttobs(fl) @ flt2cttobs(\<langle>y,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>)"
  using assms
  by (metis bullet_right_zero2 butlast_last_cons2_FL flt2cttobs_butlast_cons_eq_list_cons)

(* FIXME: Horrendous proof below *)
lemma flt2cttobs_last_non_tock:
  assumes "e \<noteq> Tock" "e \<in>\<^sub>\<F>\<^sub>\<L> last fl \<or> last fl = \<bullet>" "flt2goodTock fl" 
          "List.last(flt2cttobs fl) = [f]\<^sub>E"
  shows "flt2cttobs (fl @\<^sub>\<F>\<^sub>\<L> \<langle>(last fl,e)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>) = flt2cttobs fl @ [[e]\<^sub>E]"
  using assms
  apply (induct fl rule:flt2cttobs.induct, auto)
  apply (case_tac A, auto)
          apply (case_tac A, auto)
         apply (case_tac A, auto, case_tac b, auto)
  apply (case_tac a, auto)
           apply (case_tac "flt2cttobs fla = []", auto)
  apply (metis (no_types, lifting) acceptance_event flt2cttobs.simps(1) flt2cttobs.simps(2) flt2goodTock.elims(2) fltrace_concat.simps(3) list.discI)
  apply (metis (no_types, lifting) List.butlast.simps(2) acceptance_event append_eq_append_conv2 butlast_snoc flt2cttobs.simps(1) flt2cttobs.simps(2) flt2goodTock.elims(2) fltrace_concat.simps(3) list.discI)
  apply (metis (no_types, lifting) List.butlast.simps(2) acceptance_event append_eq_append_conv2 butlast_snoc flt2cttobs.simps(1) flt2cttobs.simps(2) flt2goodTock.elims(2) fltrace_concat.simps(3) list.discI)
  apply (metis (no_types, lifting) List.butlast.simps(2) acceptance_event append_eq_append_conv2 butlast_snoc flt2cttobs.simps(1) flt2cttobs.simps(2) flt2goodTock.elims(2) fltrace_concat.simps(3) list.discI)
         apply (case_tac A, auto, case_tac b, auto)
  apply (metis (no_types, lifting) List.butlast.simps(2) acceptance_event append_eq_append_conv2 butlast_snoc flt2cttobs.simps(1) flt2cttobs.simps(2) flt2goodTock.elims(2) fltrace_concat.simps(3) list.discI)
  apply (metis (no_types, lifting) List.butlast.simps(2) acceptance_event append_eq_append_conv2 butlast_snoc flt2cttobs.simps(1) flt2cttobs.simps(2) flt2goodTock.elims(2) fltrace_concat.simps(3) list.discI)
  apply (metis (no_types, lifting) List.butlast.simps(2) acceptance_event append_eq_append_conv2 butlast_snoc flt2cttobs.simps(1) flt2cttobs.simps(2) flt2goodTock.elims(2) fltrace_concat.simps(3) list.discI)
  apply (metis (no_types, lifting) List.butlast.simps(2) acceptance_event append_eq_append_conv2 butlast_snoc flt2cttobs.simps(1) flt2cttobs.simps(2) flt2goodTock.elims(2) fltrace_concat.simps(3) list.discI)
         apply (case_tac A, auto, case_tac b, auto)
  apply (metis (no_types, lifting) List.butlast.simps(2) acceptance_event append_eq_append_conv2 butlast_snoc flt2cttobs.simps(1) flt2cttobs.simps(2) flt2goodTock.elims(2) fltrace_concat.simps(3) list.discI)
   apply (metis (no_types, lifting) List.butlast.simps(2) acceptance_event append_eq_append_conv2 butlast_snoc flt2cttobs.simps(1) flt2cttobs.simps(2) flt2goodTock.elims(2) fltrace_concat.simps(3) list.discI)
  apply (metis (no_types, lifting) List.butlast.simps(2) acceptance_event append_eq_append_conv2 butlast_snoc flt2cttobs.simps(1) flt2cttobs.simps(2) flt2goodTock.elims(2) fltrace_concat.simps(3) list.discI)
  apply (metis (no_types, lifting) List.butlast.simps(2) acceptance_event append_eq_append_conv2 butlast_snoc flt2cttobs.simps(1) flt2cttobs.simps(2) flt2goodTock.elims(2) fltrace_concat.simps(3) list.discI)
         apply (case_tac A, auto, case_tac b, auto)
  apply (metis (no_types, lifting) List.butlast.simps(2) acceptance_event append_eq_append_conv2 butlast_snoc flt2cttobs.simps(1) flt2cttobs.simps(2) flt2goodTock.elims(2) fltrace_concat.simps(3) list.discI)
  apply (metis (no_types, lifting) List.butlast.simps(2) acceptance_event append_eq_append_conv2 butlast_snoc flt2cttobs.simps(1) flt2cttobs.simps(2) flt2goodTock.elims(2) fltrace_concat.simps(3) list.discI)
  apply (metis (no_types, lifting) List.butlast.simps(2) acceptance_event append_eq_append_conv2 butlast_snoc flt2cttobs.simps(1) flt2cttobs.simps(2) flt2goodTock.elims(2) fltrace_concat.simps(3) list.discI)
  by (metis (no_types, lifting) List.butlast.simps(2) acceptance_event append_eq_append_conv2 butlast_snoc flt2cttobs.simps(1) flt2cttobs.simps(2) flt2goodTock.elims(2) fltrace_concat.simps(3) list.discI)

lemma flt2cttobs_fl_acceptance:
  assumes "flt2goodTock fl" 
          "List.last(flt2cttobs fl) = [f]\<^sub>E" "flt2cttobs fl \<noteq> []"
  shows "flt2cttobs (fl @\<^sub>\<F>\<^sub>\<L> \<langle>[{x. x \<notin> r}]\<^sub>\<F>\<^sub>\<L>\<rangle>\<^sub>\<F>\<^sub>\<L>) = flt2cttobs fl @ [[r]\<^sub>R]"
  using assms
  apply (induct fl rule:flt2cttobs.induct, auto)
    apply (case_tac A, auto)
   apply (case_tac A, auto, case_tac b, auto)
     by (case_tac "flt2cttobs fla = []", auto, case_tac fla, auto, meson list.discI)+

lemma funFLCTockl_last_fl_not_bullet_dist_list_cons:
  assumes "last fl \<noteq> \<bullet>"
  shows "flt2cttobs(fl) = flt2cttobs(butlast fl) @ flt2cttobs(\<langle>last fl\<rangle>\<^sub>\<F>\<^sub>\<L>)"
  nitpick
  using assms apply (induct fl, auto)
  oops

(* BEGIN: weak_less_eq_fltrace lemmas. 
   TODO: Move into Finite_Linear_Model.thy and give it a nice symbol for this prefix relation. *)

lemma strong_less_eq_fltrace_cons_imp_lhs:
  assumes "(xs &\<^sub>\<F>\<^sub>\<L> \<langle>x\<rangle>\<^sub>\<F>\<^sub>\<L>) \<le>\<^sub>\<F>\<^sub>\<L> t"
  shows "xs \<le>\<^sub>\<F>\<^sub>\<L> t"
  using assms apply (induct xs t rule:strong_less_eq_fltrace.induct, auto)
  apply (cases x, auto)
  by (case_tac xa, auto)

lemma strong_less_eq_fltrace_imp_flt2cttobs_ctt:
  assumes "s \<le>\<^sub>\<F>\<^sub>\<L> t"
  shows "flt2cttobs s \<le>\<^sub>C flt2cttobs t"
  using assms apply(induct s t rule:strong_less_eq_fltrace.induct, auto)
  apply (case_tac x, auto)
  apply (metis less_eq_acceptance.elims(2))
              apply (metis less_eq_acceptance.elims(2))
  by (metis (full_types) less_eq_acceptance.elims(2) less_eq_aevent_def)+

lemma strong_less_eq_fltrace_acceptance_aevent_imp:
  assumes "(xs &\<^sub>\<F>\<^sub>\<L> \<langle>[x2]\<^sub>\<F>\<^sub>\<L>\<rangle>\<^sub>\<F>\<^sub>\<L>) \<le>\<^sub>\<F>\<^sub>\<L> (xsa &\<^sub>\<F>\<^sub>\<L> \<langle>x,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>)"
  shows "(xs &\<^sub>\<F>\<^sub>\<L> \<langle>[x2]\<^sub>\<F>\<^sub>\<L>\<rangle>\<^sub>\<F>\<^sub>\<L>) \<le>\<^sub>\<F>\<^sub>\<L> xsa"
  using assms 
  apply(induct xs xsa rule:strong_less_eq_fltrace.induct, auto)
   apply(metis (no_types, hide_lams) fltrace_concat2.simps(3) fltrace_concat2.simps(4) less_eq_acceptance.elims(3) strong_less_eq_fltrace.simps(1) strong_less_eq_fltrace.simps(2))
  apply(case_tac y, auto)
  by (metis Finite_Linear_Model.last.simps(1) fltrace.distinct(1) last_cons_acceptance_not_bullet less_eq_acceptance.elims(2) strong_less_eq_fltrace.elims(2))

lemma strong_less_eq_fltrace_less_eq_common:
  assumes "s \<le> t" "e \<in>\<^sub>\<F>\<^sub>\<L> last fl \<or> last fl = \<bullet>"
          "\<not> s \<le>\<^sub>\<F>\<^sub>\<L> (butlast fl &\<^sub>\<F>\<^sub>\<L> \<langle>(last fl,e)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>)"
          "t \<le>\<^sub>\<F>\<^sub>\<L> (butlast fl &\<^sub>\<F>\<^sub>\<L> \<langle>(last fl,e)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>)"
        shows "s \<le> fl"
using assms 
proof (induct s fl arbitrary:t rule:less_eq_fltrace.induct)
  case (1 x y)
  then show ?case
  proof (induct t rule:fltrace_induct)
    case 1
    then show ?case by auto
  next
    case (2 z zs)
    then show ?case 
      apply (case_tac z, auto)
      apply (case_tac x, auto)
      apply (metis fltrace.distinct(1) fltrace_concat2.simps(3) strong_less_eq_fltrace.elims(2) strong_less_eq_fltrace_acceptance_aevent_imp)
      by (metis fltrace.distinct(1) fltrace_concat2.simps(3) strong_less_eq_fltrace.elims(2) strong_less_eq_fltrace_acceptance_aevent_imp)
  next
    case (3 z zs)
    then show ?case
      apply (case_tac z, auto)
      apply (metis "3.prems"(1) acceptance_set amember.elims(2) bullet_left_zero2 last_fltrace_acceptance less_eq_acceptance.simps(3) less_eq_aevent_def less_eq_fltrace.simps(2) strong_less_eq_fltrace_cons_iff_lhs_bullet strong_less_eq_fltrace_last_cons_bullet_imp_le)
      using fltrace_trans strongFL_imp_less_eq by fastforce+
  qed
next
  case (2 x y ys)
  then show ?case 
    proof (induct t rule:fltrace_induct)
      case 1
      then show ?case by auto
    next
      case (2 z zs)
      then show ?case
        apply (case_tac z, auto)
        apply (case_tac x, auto)
        using fltrace_trans less_eq_fltrace.simps(2) strongFL_imp_less_eq by blast+
    next
      case (3 z zs)
      then show ?case 
        apply (case_tac z, auto)
        by (meson dual_order.trans less_eq_fltrace.simps(2) strongFL_imp_less_eq)+
    qed
next
case (3 x xs y ys)
  then show ?case 
  proof (induct t)
    case (Acceptance z)
    then show ?case by auto
  next
    case (AEvent x1a t)
    then show ?case
      using dual_order.trans by auto
  qed
next
  case (4 x xs y)
  then show ?case 
    by (metis Finite_Linear_Model.butlast.simps(1) bullet_left_zero2 dual_order.antisym fltrace_trans less_eq_acceptance.simps(1) less_eq_fltrace.simps(3) strong_less_eq_fltrace.simps(1) strong_less_eq_fltrace.simps(3) strongFL_imp_less_eq x_le_x_concat2)
qed

lemma strong_less_eq_fltrace_less_eq_common_singleton:
  assumes "s \<le> t"
          "\<not> s \<le>\<^sub>\<F>\<^sub>\<L> (fl @\<^sub>\<F>\<^sub>\<L> \<langle>z\<rangle>\<^sub>\<F>\<^sub>\<L>)"
          "t \<le>\<^sub>\<F>\<^sub>\<L> (fl @\<^sub>\<F>\<^sub>\<L> \<langle>z\<rangle>\<^sub>\<F>\<^sub>\<L>)"
        shows "s \<le> fl"
  using assms
  proof (induct s fl arbitrary:t rule:less_eq_fltrace.induct)
case (1 x y)
  then show ?case 
    apply auto
      by (meson less_eq_fltrace.simps(1) order_trans strongFL_imp_less_eq)
next
  case (2 x y ys)
  then show ?case 
    apply auto
    by (meson less_eq_fltrace.simps(2) order.trans strongFL_imp_less_eq)
next
case (3 x xs y ys)
  then show ?case
    apply auto
       apply (meson fltrace_trans less_eq_fltrace.simps(3) strongFL_imp_less_eq)
      apply (meson less_eq_fltrace.simps(3) order.trans strongFL_imp_less_eq)
     apply (meson less_eq_fltrace.simps(3) order.trans strongFL_imp_less_eq)
    by (smt fltrace.distinct(1) fltrace.inject(2) fltrace_concat.simps(2) less_eq_fltrace.simps(3) order_trans strong_less_eq_fltrace.elims(2) strong_less_eq_fltrace.elims(3))
next
  case (4 x xs y)
  then show ?case 
    apply auto
    by (meson dual_order.trans less_eq_fltrace.simps(4) strongFL_imp_less_eq)
qed

lemma flt2cttobs_last_fl_not_bullet_dist_list_cons:
  assumes "last fl \<noteq> \<bullet>" "flt2goodTock fl"
  shows "flt2cttobs(fl) = flt2cttobs(butlast fl) @ flt2cttobs(\<langle>last fl\<rangle>\<^sub>\<F>\<^sub>\<L>)"
  using assms by (induct fl, auto)

lemma FL1_extends_strong_less_eq_fltrace_last:
  assumes "FL1 x" "fl \<in> x" "e \<in>\<^sub>\<F>\<^sub>\<L> last fl"
  shows "FL1 (x \<union> {fl\<^sub>0. fl\<^sub>0 \<le>\<^sub>\<F>\<^sub>\<L> (fl @\<^sub>\<F>\<^sub>\<L> \<langle>(last fl,e)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>)})"
  using assms
  unfolding FL1_def 
  by (metis Un_iff fl_cons_acceptance_consFL mem_Collect_eq strong_less_eq_fltrace_less_eq_common)

lemma FL1_extends_strong_less_eq_fltrace_last_bullet:
  assumes "FL1 x" "fl \<in> x" "last fl = \<bullet>"
  shows "FL1 (x \<union> {fl\<^sub>0. fl\<^sub>0 \<le>\<^sub>\<F>\<^sub>\<L> (fl @\<^sub>\<F>\<^sub>\<L> \<langle>(last fl,e)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>)})"
  using assms apply (auto)
  unfolding FL1_def
  by (metis Un_iff fl_cons_acceptance_consFL mem_Collect_eq strong_less_eq_fltrace_less_eq_common)

lemma FL1_extends_strong_less_eq_fltrace_acceptance:
  assumes "FL1 x" "fl \<in> x" 
  shows "FL1 (x \<union> {fl\<^sub>0. fl\<^sub>0 \<le>\<^sub>\<F>\<^sub>\<L> (fl @\<^sub>\<F>\<^sub>\<L> \<langle>X\<rangle>\<^sub>\<F>\<^sub>\<L>)})"
  using assms unfolding FL1_def 
  using strong_less_eq_fltrace_less_eq_common_singleton by blast

lemma flt2goodTock_extend_consFL_last_fl_e:
  assumes "flt2goodTock fl" "e \<in>\<^sub>\<F>\<^sub>\<L> last fl"
  shows "flt2goodTock (fl @\<^sub>\<F>\<^sub>\<L> \<langle>(last fl,e)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>)"
  using assms by(induct fl rule:flt2goodTock.induct, auto)

lemma flt2goodTock_extend_consFL_last_fl_bullet:
  assumes "flt2goodTock fl" "last fl = \<bullet>" "e \<noteq> Tock"
  shows "flt2goodTock (fl @\<^sub>\<F>\<^sub>\<L> \<langle>(last fl,e)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>)"
  using assms by(induct fl rule:flt2goodTock.induct, auto)

lemma flt2goodTock_extend_consFL_acceptance:
  assumes "flt2goodTock fl"
  shows "flt2goodTock (fl @\<^sub>\<F>\<^sub>\<L> \<langle>X\<rangle>\<^sub>\<F>\<^sub>\<L>)"
  using assms by(induct fl rule:flt2goodTock.induct, auto)


(*
abbreviation StrongFL :: "'a fltrace \<Rightarrow> 'a \<Rightarrow> 'a fltrace set" where
"StrongFL fl e \<equiv> {fl\<^sub>0. fl\<^sub>0 \<le>\<^sub>\<F>\<^sub>\<L> fl @\<^sub>\<F>\<^sub>\<L> \<langle>(last fl,e)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>}"

lemma
  assumes "FL1 x"
          "fl \<in> x" "last fl = \<bullet>"
        shows "FL1 (x \<union> {fl\<^sub>0. fl\<^sub>0 \<le>\<^sub>\<F>\<^sub>\<L> fl @\<^sub>\<F>\<^sub>\<L> \<langle>(Finite_Linear_Model.last fl,Event e3)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>})"
  using assms FL1_extends_strong_less_eq_fltrace_last_bullet apply force  sledgehammer[debug=true]
*)
lemma CTwf_1c_3_imp_flt2cttobs_FL1:
  assumes "x \<in> P" 
      and CTwf_healthy: "CTwf P" 
      and CT1c_healthy: "CT1c P"
      and CT3_healthy:  "CT3 P"
  shows "\<exists>fl. x = flt2cttobs fl \<and> flt2goodTock fl \<and> (\<exists>x. FL1 x \<and> {flt2cttobs fl |fl. fl \<in> x} \<subseteq> P \<and> fl \<in> x)"
  using assms 
proof(induct x rule:rev_induct)
  case Nil
  then show ?case 
    apply (intro exI[where x="\<langle>\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>"], auto)
    apply (rule exI[where x="{\<langle>\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>}"], auto)
    unfolding FL1_def apply auto
    by (case_tac s, auto, case_tac x1, auto)
next
  case (snoc x xs)
  then have xs_in_P:"xs \<in> P" "cttWF (xs @ [x])"
     apply auto
    using CT1c_def ctt_prefix_concat apply blast
    using CTwf_def by blast

  from snoc show ?case
  proof (induct xs rule:rev_induct)
    case Nil
    then show ?case
    proof (cases x)
      case (Ref x1)
      then show ?thesis
        apply (intro exI[where x="\<langle>[{x. x \<notin> x1}]\<^sub>\<F>\<^sub>\<L>\<rangle>\<^sub>\<F>\<^sub>\<L>"], auto)
        apply (rule exI[where x="{z. z \<le> \<langle>[{z. z \<notin> x1}]\<^sub>\<F>\<^sub>\<L>\<rangle>\<^sub>\<F>\<^sub>\<L>}"], auto)
        using FL1_def dual_order.trans apply blast
        using fl_le_CT1c using Nil by auto
    next
      case (ObsEvent x2)
      then show ?thesis
      proof (cases x2)
        case (Event ev)
        then show ?thesis
          apply (intro exI[where x="\<langle>(\<bullet>,Event ev)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>"])
          apply (simp add:ObsEvent)
          apply (intro exI[where x="{z. z \<le> \<langle>(\<bullet>,Event ev)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>}"], auto)
          using FL1_def dual_order.trans apply blast
          using ObsEvent Nil by (simp add: fl_le_CT1c_Event)
      next
        case Tock
        text \<open> There cannot be a Tock without a refusal before it following cttWF,
               so this case is automatically solved. \<close>
        then show ?thesis
          using Nil.prems(3) ObsEvent
          by (metis CTwf_def Nil.prems(2) append_Nil cttWF.simps(6))
      next
        case Tick
        then show ?thesis
          apply (intro exI[where x="\<langle>(\<bullet>,Tick)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>"])
          apply (auto simp add: ObsEvent)
          apply (intro exI[where x="{z. z \<le> \<langle>(\<bullet>,Tick)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>}"])
          apply auto
          using FL1_def dual_order.trans apply blast
          using ObsEvent Nil by (simp add:fl_le_CT1c_Tick)
      qed
    qed
  next
    case yys:(snoc y ys)
    then have ys_y_inP:"ys @ [y] \<in> P" using CT1c_def
      by (metis ctt_prefix_concat)
    then have ys_y_fl:"\<exists>fl. ys @ [y] = flt2cttobs fl \<and> flt2goodTock fl \<and> (\<exists>x. FL1 x \<and> {flt2cttobs fl |fl. fl \<in> x} \<subseteq> P \<and> fl \<in> x)"
      using yys by auto
    then have ys_y_x: "\<exists>fl. ys @ [y] @ [x] = flt2cttobs fl @ [x] \<and> flt2goodTock fl \<and> (\<exists>x. FL1 x \<and> {flt2cttobs fl |fl. fl \<in> x} \<subseteq> P \<and> fl \<in> x)"
      by auto

    then show ?case
    proof (cases y)
      case r1:(Ref r1)
      then have exp:"\<exists>fl. ys @ [[r1]\<^sub>R] @ [x] = flt2cttobs fl @ [x] \<and> (\<exists>x. FL1 x \<and> {flt2cttobs fl |fl. fl \<in> x} \<subseteq> P \<and> fl \<in> x)"
        using ys_y_fl by auto

      then show ?thesis
      proof (cases x)
        case (Ref r2) text \<open>Not allowed\<close>
        then have "\<not>cttWF (ys @ [Ref r1, Ref r2])"
          by (induct ys rule:cttWF.induct, auto)
        then have "ys @ [Ref r1, Ref r2] \<notin> P"
          using assms unfolding CTwf_def by auto
        then show ?thesis using Ref r1 yys by auto
      next
        case (ObsEvent e1)
        then show ?thesis
        proof (cases e1)
          case (Event e2)
          then have "\<not>cttWF (ys @ [Ref r1, [Event e2]\<^sub>E])"
            by (induct ys rule:cttWF.induct, auto)
          then show ?thesis
            using assms unfolding CTwf_def
            by (metis Cons_eq_append_conv Event ObsEvent append_eq_appendI r1 ys_y_x yys.prems(2))
        next
          case Tock
          then have tock_not_in_r1: "Tock \<notin> r1"
            using CT3_any_cons_end_tock CT3_healthy ObsEvent r1 yys.prems(2) by auto

          text \<open>Then from the hypothesis we have the case:\<close>

          then obtain fl where fl:"ys @ [Ref r1] = flt2cttobs fl \<and> flt2goodTock fl \<and> (\<exists>x. FL1 x \<and> {flt2cttobs fl |fl. fl \<in> x} \<subseteq> P \<and> fl \<in> x)"
            using r1 ys_y_fl by blast
          then have last_fl_acceptance:"last fl = [{x. x \<notin> r1}]\<^sub>\<F>\<^sub>\<L>"
            by (metis (mono_tags, lifting) last_flt2cttobs_eq_ref_imp_last snoc_eq_iff_butlast)
          then have tock_in_last_fl: "Tock \<in>\<^sub>\<F>\<^sub>\<L> last fl"
            using tock_not_in_r1 by simp
          then have "ys @ [[r1]\<^sub>R] @ [[Tock]\<^sub>E] = flt2cttobs fl @ [[Tock]\<^sub>E] \<and> flt2goodTock fl \<and> (\<exists>x. FL1 x \<and> {flt2cttobs fl |fl. fl \<in> x} \<subseteq> P \<and> fl \<in> x)"
            by (simp add: fl)
          then have "ys @ [[r1]\<^sub>R] @ [[Tock]\<^sub>E] = flt2cttobs (fl @\<^sub>\<F>\<^sub>\<L> \<langle>(last fl,Tock)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>) \<and> flt2goodTock fl \<and> (\<exists>x. FL1 x \<and> {flt2cttobs fl |fl. fl \<in> x} \<subseteq> P \<and> fl \<in> x)"
            using tock_in_last_fl by (simp add: flt2cttobs_last_tock fl)

          have "{flt2cttobs fl\<^sub>0|fl\<^sub>0. fl\<^sub>0 \<le> fl} \<subseteq> P"
            using CT1c_healthy 
            using FL1_def fl subset_eq by blast

          have flt2cttobs_strongFL_subset:"{flt2cttobs fl\<^sub>0|fl\<^sub>0. fl\<^sub>0 \<le>\<^sub>\<F>\<^sub>\<L> (fl @\<^sub>\<F>\<^sub>\<L> \<langle>(last fl,Tock)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>)} \<subseteq> P"
            apply auto
            using strong_less_eq_fltrace_imp_flt2cttobs_ctt
            by (metis (no_types, lifting) CT1c_def CT1c_healthy ObsEvent Tock \<open>ys @ [[r1]\<^sub>R] @ [[Tock]\<^sub>E] = flt2cttobs (fl @\<^sub>\<F>\<^sub>\<L> \<langle>(Finite_Linear_Model.last fl,Tock)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>) \<and> flt2goodTock fl \<and> (\<exists>x. FL1 x \<and> {flt2cttobs fl |fl. fl \<in> x} \<subseteq> P \<and> fl \<in> x)\<close> \<open>ys @ [[r1]\<^sub>R] @ [[Tock]\<^sub>E] = flt2cttobs fl @ [[Tock]\<^sub>E] \<and> flt2goodTock fl \<and> (\<exists>x. FL1 x \<and> {flt2cttobs fl |fl. fl \<in> x} \<subseteq> P \<and> fl \<in> x)\<close> fl r1 yys.prems(2))

          have "(ys @ [[r1]\<^sub>R] @ [[Tock]\<^sub>E] = flt2cttobs(fl @\<^sub>\<F>\<^sub>\<L> \<langle>(last fl,Tock)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>) \<and> flt2goodTock fl
                \<and> (\<exists>x. FL1 x \<and> {flt2cttobs fl |fl. fl \<in> x} \<subseteq> P \<and> fl \<in> x))"
            using \<open>ys @ [[r1]\<^sub>R] @ [[Tock]\<^sub>E] = flt2cttobs (fl @\<^sub>\<F>\<^sub>\<L> \<langle>(Finite_Linear_Model.last fl,Tock)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>) \<and> flt2goodTock fl \<and> (\<exists>x. FL1 x \<and> {flt2cttobs fl |fl. fl \<in> x} \<subseteq> P \<and> fl \<in> x)\<close> tock_in_last_fl by blast
          then have 
               "ys @ [[r1]\<^sub>R] @ [[Tock]\<^sub>E] = flt2cttobs (fl @\<^sub>\<F>\<^sub>\<L> \<langle>(last fl,Tock)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>) \<and> flt2goodTock fl  
                \<and> (\<exists>x. FL1 (x \<union> {fl\<^sub>0. fl\<^sub>0 \<le>\<^sub>\<F>\<^sub>\<L> (fl @\<^sub>\<F>\<^sub>\<L> \<langle>(last fl,Tock)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>)}) \<and> {flt2cttobs fl |fl. fl \<in> x} \<subseteq> P \<and> fl \<in> x)"
            using FL1_extends_strong_less_eq_fltrace_last tock_in_last_fl
            by (metis (mono_tags, lifting) Collect_cong \<open>ys @ [[r1]\<^sub>R] @ [[Tock]\<^sub>E] = flt2cttobs (fl @\<^sub>\<F>\<^sub>\<L> \<langle>(Finite_Linear_Model.last fl,Tock)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>) \<and> flt2goodTock fl \<and> (\<exists>x. FL1 x \<and> {flt2cttobs fl |fl. fl \<in> x} \<subseteq> P \<and> fl \<in> x)\<close> fl)
          then have 
               "ys @ [[r1]\<^sub>R] @ [[Tock]\<^sub>E] = flt2cttobs (fl @\<^sub>\<F>\<^sub>\<L> \<langle>(last fl,Tock)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>) \<and> flt2goodTock fl 
                \<and> (\<exists>x. FL1 (x \<union> {fl\<^sub>0. fl\<^sub>0 \<le>\<^sub>\<F>\<^sub>\<L> (fl @\<^sub>\<F>\<^sub>\<L> \<langle>(last fl,Tock)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>)})
                \<and> {flt2cttobs fl\<^sub>0 |fl\<^sub>0. fl\<^sub>0 \<in> (x \<union> {fl\<^sub>0. fl\<^sub>0 \<le>\<^sub>\<F>\<^sub>\<L> (fl @\<^sub>\<F>\<^sub>\<L> \<langle>(last fl,Tock)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>)})} \<subseteq> P \<and> fl \<in> x)"
            using flt2cttobs_strongFL_subset
            by (smt Un_iff mem_Collect_eq subset_iff)
          then have 
               "ys @ [[r1]\<^sub>R] @ [[Tock]\<^sub>E] = flt2cttobs (fl @\<^sub>\<F>\<^sub>\<L> \<langle>(last fl,Tock)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>) \<and> flt2goodTock fl 
                \<and> (\<exists>x. FL1 (x \<union> {fl\<^sub>0. fl\<^sub>0 \<le>\<^sub>\<F>\<^sub>\<L> (fl @\<^sub>\<F>\<^sub>\<L> \<langle>(last fl,Tock)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>)})
                \<and> {flt2cttobs fl\<^sub>0 |fl\<^sub>0. fl\<^sub>0 \<in> (x \<union> {fl\<^sub>0. fl\<^sub>0 \<le>\<^sub>\<F>\<^sub>\<L> (fl @\<^sub>\<F>\<^sub>\<L> \<langle>(last fl,Tock)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>)})} \<subseteq> P 
                \<and> fl \<in> x
                \<and> fl @\<^sub>\<F>\<^sub>\<L> \<langle>(last fl,Tock)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L> \<in> (x \<union> {fl\<^sub>0. fl\<^sub>0 \<le>\<^sub>\<F>\<^sub>\<L> (fl @\<^sub>\<F>\<^sub>\<L> \<langle>(last fl,Tock)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>)}))"
            by (simp add: strong_less_eq_fltrace_refl)
          then have 
               "ys @ [[r1]\<^sub>R] @ [[Tock]\<^sub>E] = flt2cttobs (fl @\<^sub>\<F>\<^sub>\<L> \<langle>(last fl,Tock)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>) \<and> flt2goodTock fl 
                \<and> (\<exists>z. FL1 z
                \<and> {flt2cttobs fl\<^sub>0 |fl\<^sub>0. fl\<^sub>0 \<in> z} \<subseteq> P 
                \<and> fl @\<^sub>\<F>\<^sub>\<L> \<langle>(last fl,Tock)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L> \<in> z)"
            by blast
          then have 
               "ys @ [[r1]\<^sub>R] @ [[Tock]\<^sub>E] = flt2cttobs (fl @\<^sub>\<F>\<^sub>\<L> \<langle>(last fl,Tock)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>) \<and> flt2goodTock fl 
                \<and> flt2goodTock (fl @\<^sub>\<F>\<^sub>\<L> \<langle>(last fl,Tock)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>)
                \<and> (\<exists>z. FL1 z
                \<and> {flt2cttobs fl\<^sub>0 |fl\<^sub>0. fl\<^sub>0 \<in> z} \<subseteq> P 
                \<and> fl @\<^sub>\<F>\<^sub>\<L> \<langle>(last fl,Tock)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L> \<in> z)"
            using tock_in_last_fl by (simp add:flt2goodTock_extend_consFL_last_fl_e)
          then have 
               "\<exists>fl. ys @ [[r1]\<^sub>R] @ [[Tock]\<^sub>E] = flt2cttobs fl \<and> flt2goodTock fl 
                \<and> (\<exists>z. FL1 z \<and> {flt2cttobs fl\<^sub>0 |fl\<^sub>0. fl\<^sub>0 \<in> z} \<subseteq> P \<and> fl \<in> z)"
            by blast
          then show ?thesis using Tock ObsEvent r1 by auto
        next
          case Tick
          then have "\<not>cttWF (ys @ [Ref r1, [Tick]\<^sub>E])"
            by (induct ys rule:cttWF.induct, auto)
          then show ?thesis
            using CTwf_healthy unfolding CTwf_def
            by (metis ObsEvent Tick append.assoc append_Cons append_Nil r1 ys_y_x yys.prems(2))
        qed
      qed
    next
      case e1:(ObsEvent e1)
      text \<open>Then from the hypothesis we have the case:\<close>
      then obtain fl where fl:"ys @ [[e1]\<^sub>E] = flt2cttobs fl \<and> flt2goodTock fl \<and> (\<exists>x. FL1 x \<and> {flt2cttobs fl |fl. fl \<in> x} \<subseteq> P \<and> fl \<in> x)"
        using ys_y_fl by blast
      then have ys_e1_x:"ys @ [[e1]\<^sub>E] @ [x] = flt2cttobs fl @ [x] \<and> flt2goodTock fl \<and> (\<exists>x. FL1 x \<and> {flt2cttobs fl |fl. fl \<in> x} \<subseteq> P \<and> fl \<in> x)"
        by auto
      then have last_fl:"last fl = \<bullet>"
        by (metis cttobs.distinct(1) fl flt2cttobs.simps(1) flt2cttobs_last_fl_not_bullet_dist_list_cons last_snoc)

      then show ?thesis
      proof (cases x)
        case e2:(ObsEvent e2)
        then show ?thesis
        proof (cases e2)
          case (Event e3)
          have flt2cttobs_strongFL_subset:"{flt2cttobs fl\<^sub>0|fl\<^sub>0. fl\<^sub>0 \<le>\<^sub>\<F>\<^sub>\<L> (fl @\<^sub>\<F>\<^sub>\<L> \<langle>(last fl,Event e3)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>)} \<subseteq> P"
            apply auto
            using strong_less_eq_fltrace_imp_flt2cttobs_ctt
            by (metis (no_types, lifting) CT1c_def CT1c_healthy Event cttevent.simps(3) e1 e2 fl flt2cttobs_last_non_tock last_fl last_snoc yys.prems(2))
          
          from fl have fl_e3: "ys @ [[e1]\<^sub>E] @ [[Event e3]\<^sub>E] = flt2cttobs fl @ [[Event e3]\<^sub>E]
                  \<and> flt2goodTock fl \<and> (\<exists>x. FL1 x \<and> {flt2cttobs fl\<^sub>0 |fl\<^sub>0. fl\<^sub>0 \<in> x} \<subseteq> P \<and> fl \<in> x)"
            using ys_e1_x by auto
          also have "... =
                  (ys @ [[e1]\<^sub>E] @ [[Event e3]\<^sub>E] = flt2cttobs(fl @\<^sub>\<F>\<^sub>\<L> \<langle>(last fl,Event e3)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>)
                  \<and> flt2goodTock fl \<and> (\<exists>x. FL1 x \<and> {flt2cttobs fl\<^sub>0 |fl\<^sub>0. fl\<^sub>0 \<in> x} \<subseteq> P \<and> fl \<in> x))"
            proof -
              from fl have "ys @ [[e1]\<^sub>E] = flt2cttobs fl"
                by auto
              then have "List.last(flt2cttobs fl) = [e1]\<^sub>E"
                by (metis last_snoc)
              then have "flt2cttobs fl @ [[Event e3]\<^sub>E] = flt2cttobs(fl @\<^sub>\<F>\<^sub>\<L> \<langle>(last fl,Event e3)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>)"
                using fl last_fl flt2cttobs_last_non_tock
                by (metis (no_types, lifting) cttevent.distinct(1))
              then show ?thesis using calculation  by auto
            qed
          finally have "
                  ys @ [[e1]\<^sub>E] @ [[Event e3]\<^sub>E] = flt2cttobs(fl @\<^sub>\<F>\<^sub>\<L> \<langle>(last fl,Event e3)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>)
                  \<and> flt2goodTock fl 
                  \<and> (\<exists>x. FL1 (x \<union> {fl\<^sub>0. fl\<^sub>0 \<le>\<^sub>\<F>\<^sub>\<L> (fl @\<^sub>\<F>\<^sub>\<L> \<langle>(last fl,Event e3)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>)}) 
                      \<and> {flt2cttobs fl\<^sub>0 |fl\<^sub>0. fl\<^sub>0 \<in> x} \<subseteq> P \<and> fl \<in> x)"
              apply auto using FL1_extends_strong_less_eq_fltrace_last_bullet last_fl 
              by fastforce
         then have "
                  ys @ [[e1]\<^sub>E] @ [[Event e3]\<^sub>E] = flt2cttobs(fl @\<^sub>\<F>\<^sub>\<L> \<langle>(last fl,Event e3)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>)
                  \<and> flt2goodTock fl 
                  \<and> (\<exists>x. FL1 (x \<union> {fl\<^sub>0. fl\<^sub>0 \<le>\<^sub>\<F>\<^sub>\<L> (fl @\<^sub>\<F>\<^sub>\<L> \<langle>(last fl,Event e3)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>)}) 
                      \<and> {flt2cttobs fl\<^sub>0 |fl\<^sub>0. fl\<^sub>0 \<in> (x \<union> {fl\<^sub>0. fl\<^sub>0 \<le>\<^sub>\<F>\<^sub>\<L> (fl @\<^sub>\<F>\<^sub>\<L> \<langle>(last fl,Event e3)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>)})} \<subseteq> P \<and> fl \<in> x)"  
           using flt2cttobs_strongFL_subset 
           by (smt Un_iff mem_Collect_eq subset_iff)
         then have "
                  ys @ [[e1]\<^sub>E] @ [[Event e3]\<^sub>E] = flt2cttobs(fl @\<^sub>\<F>\<^sub>\<L> \<langle>(last fl,Event e3)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>)
                  \<and> flt2goodTock fl 
                  \<and> (\<exists>x. FL1 (x \<union> {fl\<^sub>0. fl\<^sub>0 \<le>\<^sub>\<F>\<^sub>\<L> (fl @\<^sub>\<F>\<^sub>\<L> \<langle>(last fl,Event e3)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>)}) 
                      \<and> {flt2cttobs fl\<^sub>0 |fl\<^sub>0. fl\<^sub>0 \<in> (x \<union> {fl\<^sub>0. fl\<^sub>0 \<le>\<^sub>\<F>\<^sub>\<L> (fl @\<^sub>\<F>\<^sub>\<L> \<langle>(last fl,Event e3)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>)})} \<subseteq> P 
                      \<and> fl \<in> x
                      \<and> fl @\<^sub>\<F>\<^sub>\<L> \<langle>(last fl,Event e3)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L> \<in> (x \<union> {fl\<^sub>0. fl\<^sub>0 \<le>\<^sub>\<F>\<^sub>\<L> (fl @\<^sub>\<F>\<^sub>\<L> \<langle>(last fl,Event e3)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>)}))"
            by (simp add: strong_less_eq_fltrace_refl)  
         then have "
                  ys @ [[e1]\<^sub>E] @ [[Event e3]\<^sub>E] = flt2cttobs(fl @\<^sub>\<F>\<^sub>\<L> \<langle>(last fl,Event e3)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>)
                  \<and> flt2goodTock fl 
                  \<and> (\<exists>z. FL1 z 
                      \<and> {flt2cttobs fl\<^sub>0 |fl\<^sub>0. fl\<^sub>0 \<in> z} \<subseteq> P 
                      \<and> fl @\<^sub>\<F>\<^sub>\<L> \<langle>(last fl,Event e3)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L> \<in> z)"
           by blast
         then have "
                  ys @ [[e1]\<^sub>E] @ [[Event e3]\<^sub>E] = flt2cttobs(fl @\<^sub>\<F>\<^sub>\<L> \<langle>(last fl,Event e3)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>)
                  \<and> flt2goodTock fl 
                  \<and> flt2goodTock (fl @\<^sub>\<F>\<^sub>\<L> \<langle>(last fl,Event e3)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>)
                  \<and> (\<exists>z. FL1 z 
                      \<and> {flt2cttobs fl\<^sub>0 |fl\<^sub>0. fl\<^sub>0 \<in> z} \<subseteq> P 
                      \<and> fl @\<^sub>\<F>\<^sub>\<L> \<langle>(last fl,Event e3)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L> \<in> z)"
           using last_fl flt2goodTock_extend_consFL_last_fl_bullet
           by blast
         then have "
                  \<exists>fl. ys @ [[e1]\<^sub>E] @ [[Event e3]\<^sub>E] = flt2cttobs(fl)
                  \<and> flt2goodTock fl 
                  \<and> (\<exists>z. FL1 z \<and> {flt2cttobs fl\<^sub>0 |fl\<^sub>0. fl\<^sub>0 \<in> z} \<subseteq> P \<and> fl \<in> z)"
           by blast
         then show ?thesis using Event e1 e2 by auto
        next
          case Tock
          then have "\<not>cttWF (ys @ [[e1]\<^sub>E, [Tock]\<^sub>E])"
            apply (induct ys rule:cttWF.induct, auto)
            using cttWF.elims(2) cttWF.simps(6) by blast+
          then show ?thesis
            using e1 e2 CTwf_healthy unfolding CTwf_def
            by (metis Tock append_eq_Cons_conv fl ys_e1_x yys.prems(2))
        next
          case Tick
          have flt2cttobs_strongFL_subset:"{flt2cttobs fl\<^sub>0|fl\<^sub>0. fl\<^sub>0 \<le>\<^sub>\<F>\<^sub>\<L> (fl @\<^sub>\<F>\<^sub>\<L> \<langle>(last fl,Tick)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>)} \<subseteq> P"
            apply auto
            using strong_less_eq_fltrace_imp_flt2cttobs_ctt
            by (metis (no_types, lifting) CT1c_def CT1c_healthy Tick cttevent.distinct(5) e1 e2 fl flt2cttobs_last_non_tock last_fl last_snoc yys.prems(2))
            
          from fl have fl_e3: "ys @ [[e1]\<^sub>E] @ [[Tick]\<^sub>E] = flt2cttobs fl @ [[Tick]\<^sub>E]
                  \<and> flt2goodTock fl \<and> (\<exists>x. FL1 x \<and> {flt2cttobs fl\<^sub>0 |fl\<^sub>0. fl\<^sub>0 \<in> x} \<subseteq> P \<and> fl \<in> x)"
            using ys_e1_x by auto
          also have "... =
                  (ys @ [[e1]\<^sub>E] @ [[Tick]\<^sub>E] = flt2cttobs(fl @\<^sub>\<F>\<^sub>\<L> \<langle>(last fl,Tick)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>)
                  \<and> flt2goodTock fl \<and> (\<exists>x. FL1 x \<and> {flt2cttobs fl\<^sub>0 |fl\<^sub>0. fl\<^sub>0 \<in> x} \<subseteq> P \<and> fl \<in> x))"
            proof -
              from fl have "ys @ [[e1]\<^sub>E] = flt2cttobs fl"
                by auto
              then have "List.last(flt2cttobs fl) = [e1]\<^sub>E"
                by (metis last_snoc)
              then have "flt2cttobs fl @ [[Tick]\<^sub>E] = flt2cttobs(fl @\<^sub>\<F>\<^sub>\<L> \<langle>(last fl,Tick)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>)"
                using fl last_fl flt2cttobs_last_non_tock
                by (metis (no_types, lifting) cttevent.simps(7))
              then show ?thesis using calculation  by auto
            qed
          finally have "
                  ys @ [[e1]\<^sub>E] @ [[Tick]\<^sub>E] = flt2cttobs(fl @\<^sub>\<F>\<^sub>\<L> \<langle>(last fl,Tick)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>)
                  \<and> flt2goodTock fl 
                  \<and> (\<exists>x. FL1 (x \<union> {fl\<^sub>0. fl\<^sub>0 \<le>\<^sub>\<F>\<^sub>\<L> (fl @\<^sub>\<F>\<^sub>\<L> \<langle>(last fl,Tick)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>)}) 
                      \<and> {flt2cttobs fl\<^sub>0 |fl\<^sub>0. fl\<^sub>0 \<in> x} \<subseteq> P \<and> fl \<in> x)"
              apply auto using FL1_extends_strong_less_eq_fltrace_last_bullet last_fl 
              by fastforce
         then have "
                  ys @ [[e1]\<^sub>E] @ [[Tick]\<^sub>E] = flt2cttobs(fl @\<^sub>\<F>\<^sub>\<L> \<langle>(last fl,Tick)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>)
                  \<and> flt2goodTock fl 
                  \<and> (\<exists>x. FL1 (x \<union> {fl\<^sub>0. fl\<^sub>0 \<le>\<^sub>\<F>\<^sub>\<L> (fl @\<^sub>\<F>\<^sub>\<L> \<langle>(last fl,Tick)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>)}) 
                      \<and> {flt2cttobs fl\<^sub>0 |fl\<^sub>0. fl\<^sub>0 \<in> (x \<union> {fl\<^sub>0. fl\<^sub>0 \<le>\<^sub>\<F>\<^sub>\<L> (fl @\<^sub>\<F>\<^sub>\<L> \<langle>(last fl,Tick)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>)})} \<subseteq> P \<and> fl \<in> x)"  
           using flt2cttobs_strongFL_subset 
           by (smt Un_iff mem_Collect_eq subset_iff)
         then have "
                  ys @ [[e1]\<^sub>E] @ [[Tick]\<^sub>E] = flt2cttobs(fl @\<^sub>\<F>\<^sub>\<L> \<langle>(last fl,Tick)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>)
                  \<and> flt2goodTock fl 
                  \<and> (\<exists>x. FL1 (x \<union> {fl\<^sub>0. fl\<^sub>0 \<le>\<^sub>\<F>\<^sub>\<L> (fl @\<^sub>\<F>\<^sub>\<L> \<langle>(last fl,Tick)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>)}) 
                      \<and> {flt2cttobs fl\<^sub>0 |fl\<^sub>0. fl\<^sub>0 \<in> (x \<union> {fl\<^sub>0. fl\<^sub>0 \<le>\<^sub>\<F>\<^sub>\<L> (fl @\<^sub>\<F>\<^sub>\<L> \<langle>(last fl,Tick)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>)})} \<subseteq> P 
                      \<and> fl \<in> x
                      \<and> fl @\<^sub>\<F>\<^sub>\<L> \<langle>(last fl,Tick)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L> \<in> (x \<union> {fl\<^sub>0. fl\<^sub>0 \<le>\<^sub>\<F>\<^sub>\<L> (fl @\<^sub>\<F>\<^sub>\<L> \<langle>(last fl,Tick)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>)}))"
            by (simp add: strong_less_eq_fltrace_refl)  
         then have "
                  ys @ [[e1]\<^sub>E] @ [[Tick]\<^sub>E] = flt2cttobs(fl @\<^sub>\<F>\<^sub>\<L> \<langle>(last fl,Tick)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>)
                  \<and> flt2goodTock fl 
                  \<and> (\<exists>z. FL1 z 
                      \<and> {flt2cttobs fl\<^sub>0 |fl\<^sub>0. fl\<^sub>0 \<in> z} \<subseteq> P 
                      \<and> fl @\<^sub>\<F>\<^sub>\<L> \<langle>(last fl,Tick)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L> \<in> z)"
           by blast
         then have "
                  ys @ [[e1]\<^sub>E] @ [[Tick]\<^sub>E] = flt2cttobs(fl @\<^sub>\<F>\<^sub>\<L> \<langle>(last fl,Tick)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>)
                  \<and> flt2goodTock fl 
                  \<and> flt2goodTock (fl @\<^sub>\<F>\<^sub>\<L> \<langle>(last fl,Tick)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>)
                  \<and> (\<exists>z. FL1 z 
                      \<and> {flt2cttobs fl\<^sub>0 |fl\<^sub>0. fl\<^sub>0 \<in> z} \<subseteq> P 
                      \<and> fl @\<^sub>\<F>\<^sub>\<L> \<langle>(last fl,Tick)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L> \<in> z)"
           using last_fl flt2goodTock_extend_consFL_last_fl_bullet
           by blast
         then have "
                  \<exists>fl. ys @ [[e1]\<^sub>E] @ [[Tick]\<^sub>E] = flt2cttobs(fl)
                  \<and> flt2goodTock fl 
                  \<and> (\<exists>z. FL1 z \<and> {flt2cttobs fl\<^sub>0 |fl\<^sub>0. fl\<^sub>0 \<in> z} \<subseteq> P \<and> fl \<in> z)"
           by blast
         then show ?thesis using Tick e1 e2 by auto
        qed
      next
        case (Ref r2)
       (* have flt2cttobs_strongFL_subset:"{flt2cttobs fl\<^sub>0|fl\<^sub>0. fl\<^sub>0 \<le>\<^sub>\<F>\<^sub>\<L> (fl @\<^sub>\<F>\<^sub>\<L> \<langle>[{x. x \<notin> r2}]\<^sub>\<F>\<^sub>\<L>\<rangle>\<^sub>\<F>\<^sub>\<L>)} \<subseteq> P"
            apply auto
          using strong_less_eq_fltrace_imp_flt2cttobs_ctt
          sledgehammer[debug=true]
          by (metis CT1c_def CT1c_healthy Collect_cong Ref e1 fl flt2cttobs_fl_acceptance last_snoc mem_Collect_eq snoc_eq_iff_butlast subsetI subset_iff yys.prems(2))
        *)
        from fl have fl_e3: "ys @ [[e1]\<^sub>E] @ [[r2]\<^sub>R] = flt2cttobs fl @ [[r2]\<^sub>R]
                  \<and> flt2goodTock fl \<and> (\<exists>x. FL1 x \<and> {flt2cttobs fl\<^sub>0 |fl\<^sub>0. fl\<^sub>0 \<in> x} \<subseteq> P \<and> fl \<in> x)"
          using ys_e1_x by auto
        also have "... =
                  (ys @ [[e1]\<^sub>E] @ [[r2]\<^sub>R] = flt2cttobs(fl @\<^sub>\<F>\<^sub>\<L> \<langle>[{x. x \<notin> r2}]\<^sub>\<F>\<^sub>\<L>\<rangle>\<^sub>\<F>\<^sub>\<L>)
                  \<and> flt2goodTock fl \<and> (\<exists>x. FL1 x \<and> {flt2cttobs fl\<^sub>0 |fl\<^sub>0. fl\<^sub>0 \<in> x} \<subseteq> P \<and> fl \<in> x))"
          proof -
              from fl have "ys @ [[e1]\<^sub>E] = flt2cttobs fl"
                by auto
              then have "List.last(flt2cttobs fl) = [e1]\<^sub>E"
                by (metis last_snoc)
              then have "flt2cttobs fl @ [[r2]\<^sub>R] = flt2cttobs(fl @\<^sub>\<F>\<^sub>\<L> \<langle>[{x. x \<notin> r2}]\<^sub>\<F>\<^sub>\<L>\<rangle>\<^sub>\<F>\<^sub>\<L>)"
                using fl last_fl flt2cttobs_fl_acceptance
                by (metis (no_types, lifting) Collect_cong snoc_eq_iff_butlast)
              then show ?thesis using calculation  by auto
            qed
         finally have "
                  ys @ [[e1]\<^sub>E] @ [[r2]\<^sub>R] = flt2cttobs(fl @\<^sub>\<F>\<^sub>\<L> \<langle>[{x. x \<notin> r2}]\<^sub>\<F>\<^sub>\<L>\<rangle>\<^sub>\<F>\<^sub>\<L>)
                  \<and> flt2goodTock fl 
                  \<and> (\<exists>x. FL1 (x \<union> {fl\<^sub>0. fl\<^sub>0 \<le>\<^sub>\<F>\<^sub>\<L> (fl @\<^sub>\<F>\<^sub>\<L> \<langle>[{x. x \<notin> r2}]\<^sub>\<F>\<^sub>\<L>\<rangle>\<^sub>\<F>\<^sub>\<L>)}) 
                      \<and> {flt2cttobs fl\<^sub>0 |fl\<^sub>0. fl\<^sub>0 \<in> x} \<subseteq> P \<and> fl \<in> x)"
              apply auto using FL1_extends_strong_less_eq_fltrace_acceptance last_fl 
              by fastforce 
         then have "
                  ys @ [[e1]\<^sub>E] @ [[r2]\<^sub>R] = flt2cttobs(fl @\<^sub>\<F>\<^sub>\<L> \<langle>[{x. x \<notin> r2}]\<^sub>\<F>\<^sub>\<L>\<rangle>\<^sub>\<F>\<^sub>\<L>)
                  \<and> flt2goodTock fl 
                  \<and> (\<exists>x. FL1 (x \<union> {fl\<^sub>0. fl\<^sub>0 \<le>\<^sub>\<F>\<^sub>\<L> (fl @\<^sub>\<F>\<^sub>\<L> \<langle>[{x. x \<notin> r2}]\<^sub>\<F>\<^sub>\<L>\<rangle>\<^sub>\<F>\<^sub>\<L>)}) 
                      \<and> {flt2cttobs fl\<^sub>0 |fl\<^sub>0. fl\<^sub>0 \<in> (x \<union> {fl\<^sub>0. fl\<^sub>0 \<le>\<^sub>\<F>\<^sub>\<L> (fl @\<^sub>\<F>\<^sub>\<L> \<langle>[{x. x \<notin> r2}]\<^sub>\<F>\<^sub>\<L>\<rangle>\<^sub>\<F>\<^sub>\<L>)})} \<subseteq> P \<and> fl \<in> x)"  
         proof -
           have
            "{flt2cttobs fl\<^sub>0|fl\<^sub>0. fl\<^sub>0 \<le>\<^sub>\<F>\<^sub>\<L> (fl @\<^sub>\<F>\<^sub>\<L> \<langle>[{x. x \<notin> r2}]\<^sub>\<F>\<^sub>\<L>\<rangle>\<^sub>\<F>\<^sub>\<L>)} \<subseteq> P"
            apply auto
            using strong_less_eq_fltrace_imp_flt2cttobs_ctt
            by (metis (no_types, lifting) CT1c_def CT1c_healthy Ref \<open>ys @ [[e1]\<^sub>E] @ [[r2]\<^sub>R] = flt2cttobs (fl @\<^sub>\<F>\<^sub>\<L> \<langle>[{x. x \<notin> r2}]\<^sub>\<F>\<^sub>\<L>\<rangle>\<^sub>\<F>\<^sub>\<L>) \<and> flt2goodTock fl \<and> (\<exists>x. FL1 (x \<union> {fl\<^sub>0. fl\<^sub>0 \<le>\<^sub>\<F>\<^sub>\<L> fl @\<^sub>\<F>\<^sub>\<L> \<langle>[{x. x \<notin> r2}]\<^sub>\<F>\<^sub>\<L>\<rangle>\<^sub>\<F>\<^sub>\<L>}) \<and> {flt2cttobs fl\<^sub>0 |fl\<^sub>0. fl\<^sub>0 \<in> x} \<subseteq> P \<and> fl \<in> x)\<close> e1 fl fl_e3 yys.prems(2))
          then show ?thesis 
            by (smt Un_iff \<open>ys @ [[e1]\<^sub>E] @ [[r2]\<^sub>R] = flt2cttobs (fl @\<^sub>\<F>\<^sub>\<L> \<langle>[{x. x \<notin> r2}]\<^sub>\<F>\<^sub>\<L>\<rangle>\<^sub>\<F>\<^sub>\<L>) \<and> flt2goodTock fl \<and> (\<exists>x. FL1 (x \<union> {fl\<^sub>0. fl\<^sub>0 \<le>\<^sub>\<F>\<^sub>\<L> fl @\<^sub>\<F>\<^sub>\<L> \<langle>[{x. x \<notin> r2}]\<^sub>\<F>\<^sub>\<L>\<rangle>\<^sub>\<F>\<^sub>\<L>}) \<and> {flt2cttobs fl\<^sub>0 |fl\<^sub>0. fl\<^sub>0 \<in> x} \<subseteq> P \<and> fl \<in> x)\<close> mem_Collect_eq subset_iff)
        qed
        then have "
                  ys @ [[e1]\<^sub>E] @ [[r2]\<^sub>R] = flt2cttobs(fl @\<^sub>\<F>\<^sub>\<L> \<langle>[{x. x \<notin> r2}]\<^sub>\<F>\<^sub>\<L>\<rangle>\<^sub>\<F>\<^sub>\<L>)
                  \<and> flt2goodTock fl 
                  \<and> (\<exists>x. FL1 (x \<union> {fl\<^sub>0. fl\<^sub>0 \<le>\<^sub>\<F>\<^sub>\<L> (fl @\<^sub>\<F>\<^sub>\<L> \<langle>[{x. x \<notin> r2}]\<^sub>\<F>\<^sub>\<L>\<rangle>\<^sub>\<F>\<^sub>\<L>)}) 
                      \<and> {flt2cttobs fl\<^sub>0 |fl\<^sub>0. fl\<^sub>0 \<in> (x \<union> {fl\<^sub>0. fl\<^sub>0 \<le>\<^sub>\<F>\<^sub>\<L> (fl @\<^sub>\<F>\<^sub>\<L> \<langle>[{x. x \<notin> r2}]\<^sub>\<F>\<^sub>\<L>\<rangle>\<^sub>\<F>\<^sub>\<L>)})} \<subseteq> P 
                      \<and> fl \<in> x
                      \<and> (fl @\<^sub>\<F>\<^sub>\<L> \<langle>[{x. x \<notin> r2}]\<^sub>\<F>\<^sub>\<L>\<rangle>\<^sub>\<F>\<^sub>\<L>) \<in> (x \<union> {fl\<^sub>0. fl\<^sub>0 \<le>\<^sub>\<F>\<^sub>\<L> (fl @\<^sub>\<F>\<^sub>\<L> \<langle>[{x. x \<notin> r2}]\<^sub>\<F>\<^sub>\<L>\<rangle>\<^sub>\<F>\<^sub>\<L>)}))"  
         by (simp add: strong_less_eq_fltrace_refl)  
        then have "
                  ys @ [[e1]\<^sub>E] @ [[r2]\<^sub>R] = flt2cttobs(fl @\<^sub>\<F>\<^sub>\<L> \<langle>[{x. x \<notin> r2}]\<^sub>\<F>\<^sub>\<L>\<rangle>\<^sub>\<F>\<^sub>\<L>)
                  \<and> flt2goodTock fl 
                  \<and> (\<exists>z. FL1 z 
                      \<and> {flt2cttobs fl\<^sub>0 |fl\<^sub>0. fl\<^sub>0 \<in> z} \<subseteq> P 
                      \<and> fl @\<^sub>\<F>\<^sub>\<L> \<langle>[{x. x \<notin> r2}]\<^sub>\<F>\<^sub>\<L>\<rangle>\<^sub>\<F>\<^sub>\<L> \<in> z)"
          by blast
        then have "
                  ys @ [[e1]\<^sub>E] @ [[r2]\<^sub>R] = flt2cttobs(fl @\<^sub>\<F>\<^sub>\<L> \<langle>[{x. x \<notin> r2}]\<^sub>\<F>\<^sub>\<L>\<rangle>\<^sub>\<F>\<^sub>\<L>)
                  \<and> flt2goodTock fl
                  \<and> flt2goodTock (fl @\<^sub>\<F>\<^sub>\<L> \<langle>[{x. x \<notin> r2}]\<^sub>\<F>\<^sub>\<L>\<rangle>\<^sub>\<F>\<^sub>\<L>) 
                  \<and> (\<exists>z. FL1 z 
                      \<and> {flt2cttobs fl\<^sub>0 |fl\<^sub>0. fl\<^sub>0 \<in> z} \<subseteq> P 
                      \<and> fl @\<^sub>\<F>\<^sub>\<L> \<langle>[{x. x \<notin> r2}]\<^sub>\<F>\<^sub>\<L>\<rangle>\<^sub>\<F>\<^sub>\<L> \<in> z)"
          using flt2goodTock_extend_consFL_acceptance by blast
        then have "
                  \<exists>fl. ys @ [[e1]\<^sub>E] @ [[r2]\<^sub>R] = flt2cttobs(fl)
                  \<and> flt2goodTock fl
                  \<and> (\<exists>z. FL1 z 
                      \<and> {flt2cttobs fl\<^sub>0 |fl\<^sub>0. fl\<^sub>0 \<in> z} \<subseteq> P 
                      \<and> fl \<in> z)"
          by blast
        then show ?thesis using Ref e1 by auto
        qed
    qed
  qed
qed

lemma subset_fl2ctt_ctt2fl:
  assumes 
          CTwf_healthy: "CTwf P" 
      and CT1c_healthy: "CT1c P"
      and CT3_healthy:  "CT3 P"
  shows "P \<subseteq> fl2ctt(ctt2fl(P))"
  unfolding ctt2fl_def fl2ctt_def apply auto
  using assms CTwf_1c_3_imp_flt2cttobs_FL1 by blast

lemma fl2ctt_ctt2fl_bij:
  assumes 
          CTwf_healthy: "CTwf P" 
      and CT1c_healthy: "CT1c P"
      and CT3_healthy:  "CT3 P"
    shows "P = fl2ctt(ctt2fl(P))"
  using assms
  by (simp add: fl2ctt_ctt2fl_refines subset_antisym subset_fl2ctt_ctt2fl)

lemma fl2ctt_mono:
  assumes "P \<subseteq> Q"
  shows "fl2ctt(P) \<subseteq> fl2ctt(Q)"
  using assms unfolding fl2ctt_def by auto

lemma
  assumes CTwf_healthy: "CTwf P" 
  shows "\<forall>x. x \<in> ctt2fl(P) \<longrightarrow> tickWF Tick x"
  using assms unfolding ctt2fl_def apply auto
  oops

(* Not true, of course..
lemma
  assumes "tickWF tick xs"
  shows "tickWF tick (xs &\<^sub>\<F>\<^sub>\<L> \<langle>x\<rangle>\<^sub>\<F>\<^sub>\<L>)"
  using assms apply (induct xs, auto)
  apply (cases x, auto, case_tac xa, auto)
*)
(*
lemma
  assumes "CTwf P" 
          "FL1 xa" 
          "fl2ctt xa \<subseteq> P" "fl \<in> xa"
    shows "tickWF Tick fl"
  using assms apply (induct fl rule:fltrace_induct, auto)
  apply (case_tac x, auto)*)

end
  