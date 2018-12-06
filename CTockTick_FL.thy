theory CTockTick_FL
  
imports
  CTockTick_Core
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

definition CTRMax :: "('a cttobs) list set \<Rightarrow> bool" where
"CTRMax P = (\<forall>t X. t @ [[X]\<^sub>R] \<in> P \<longrightarrow> \<not>(\<exists>Y. X \<subset> Y \<and> (t @ [[Y]\<^sub>R]) \<in> P))" 

definition CTTick :: "('a cttobs) list set \<Rightarrow> bool" where
"CTTick P = (\<forall>t X. t @ [[X]\<^sub>R] \<in> P \<longrightarrow> Tick \<in> X)"

(* FIXME: CTRMax is way too strong. Instead we need to require that
          every refusal set has Tick. Sufficient? *)

fun CTTickTrace :: "('a cttobs) list \<Rightarrow> bool" where
"CTTickTrace [] = True" |
"CTTickTrace ([e]\<^sub>E # xs) = CTTickTrace xs" |
"CTTickTrace ([r]\<^sub>R # xs) = (Tick \<in> r \<and> CTTickTrace xs)"

definition CTTickAll :: "('a cttobs) list set \<Rightarrow> bool" where
"CTTickAll P = (\<forall>t. t \<in> P \<longrightarrow> CTTickTrace t)"

lemma CTRMax_top_refusal:
  assumes "CTRMax P" "t @ [[X]\<^sub>R] \<in> P" "X \<subset> Y"
  shows "\<not> t @ [[Y]\<^sub>R] \<in> P"
  using assms unfolding CTRMax_def by auto

lemma CTRMax_CT4_Tick:
  assumes "CTRMax P" "CT4 P" "t @ [[X]\<^sub>R] \<in> P"
  shows "Tick \<in> X"
proof (cases "Tick \<in> X")
  case True
  then show ?thesis by auto
next
  case False
  then have "t @ [[X \<union> {Tick}]\<^sub>R] \<in> P"
    using assms(2,3) unfolding CT4_def by auto
  then have "t @ [[X \<union> {Tick}]\<^sub>R] \<notin> P"
    using CTRMax_top_refusal False assms(1) assms(3) insertI1 by blast
  then show ?thesis
    using \<open>t @ [[X \<union> {Tick}]\<^sub>R] \<in> P\<close> by blast
qed

lemma CTTickTrace_dist_concat:
  "CTTickTrace (xs @ ys) = (CTTickTrace xs \<and> CTTickTrace ys)"
  by (induct xs rule:CTTickTrace.induct, auto)

lemma CTRMax_CT4_CT1c_CTTickTrace:
  assumes "CTRMax P" "CT4 P" "CT1c P" "x \<in> P"
  shows "CTTickTrace x"
  using assms apply(induct x rule:rev_induct, auto)
  apply (simp add:CTTickTrace_dist_concat)
  apply (case_tac xa, auto)
  unfolding CT1c_def apply auto
  using ctt_prefix_concat apply blast
  using ctt_prefix_concat apply blast
  using CTRMax_CT4_Tick by blast

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
"ctt2fl P = \<Union>{fl. FLTick0 Tick fl \<and> FL1 fl \<and> (fl2ctt fl) \<subseteq> P}"

lemma ctt2fl_mono:
  assumes "P \<subseteq> Q"
  shows "ctt2fl(P) \<subseteq> ctt2fl(Q)"
  using assms unfolding ctt2fl_def by auto

lemma fl2ctt_ctt2fl_refines: "fl2ctt(ctt2fl(P)) \<subseteq> P"
  unfolding ctt2fl_def fl2ctt_def by auto

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

lemma tickWF_cons_prefix:
  assumes "tickWF Tick fl" "xa \<le>\<^sub>\<F>\<^sub>\<L> fl @\<^sub>\<F>\<^sub>\<L> \<langle>(Finite_Linear_Model.last fl,e)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>" "e \<noteq> Tick" "e \<in>\<^sub>\<F>\<^sub>\<L> last fl"
  shows "tickWF Tick xa"
  using assms apply (induct xa fl arbitrary:e rule:less_eq_fltrace.induct, auto)
         apply (simp_all add: less_eq_aevent_def)
    apply (metis acceptance.distinct(1) amember.elims(2) less_eq_acceptance.elims(2))
   apply (metis amember.elims(2) less_eq_acceptance.simps(3))
  by (metis amember.simps(1) bullet_left_zero2 dual_order.antisym strongFL_imp_less_eq tickWF.simps(1) x_le_x_concat2)

lemma tickWF_prefix_imp:
  assumes "tickWF Tick fl" "xa \<le>\<^sub>\<F>\<^sub>\<L> fl"
  shows "tickWF Tick xa"
  using assms apply (induct xa fl rule:less_eq_fltrace.induct, auto)
      apply (metis amember.simps(1) less_eq_acceptance.elims(2))
     apply (metis dual_order.antisym event_in_acceptance less_eq_acceptance.simps(1) less_eq_aevent_def)
    apply (metis bullet_left_zero2 dual_order.antisym less_eq_aevent_def strongFL_imp_less_eq x_le_x_concat2)
   apply (metis acceptance.distinct(1) amember.elims(2) less_eq_acceptance.elims(2) less_eq_aevent_def)
  by (simp add: less_eq_aevent_def)

lemma tickWF_concatFL_imp:
  assumes "tickWF Tick fl" "Tick \<notin> events fl" "e \<in>\<^sub>\<F>\<^sub>\<L> last fl \<or> last fl = \<bullet>"
  shows "tickWF Tick (fl @\<^sub>\<F>\<^sub>\<L> \<langle>(Finite_Linear_Model.last fl,e)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>)"
  using assms by (induct fl, auto)

lemma tickWF_concatFL_acceptance_imp:
  assumes "tickWF Tick fl" "Tick \<notin> events fl" "Tick \<notin>\<^sub>\<F>\<^sub>\<L> X"
  shows "tickWF Tick (fl @\<^sub>\<F>\<^sub>\<L> \<langle>X\<rangle>\<^sub>\<F>\<^sub>\<L>)"
  using assms by (induct fl, auto)

lemma tickWF_concatFL_prefix_last:
  assumes "tickWF Tick fl" "Tick \<notin> events fl" "e \<in>\<^sub>\<F>\<^sub>\<L> last fl \<or> last fl = \<bullet>" "xa \<le>\<^sub>\<F>\<^sub>\<L> fl @\<^sub>\<F>\<^sub>\<L> \<langle>(Finite_Linear_Model.last fl,e)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>"
  shows "tickWF Tick xa"
  using assms
  using tickWF_concatFL_imp tickWF_prefix_imp by blast

lemma FLTick0_extends_strong_less_eq_fltrace_last:
  assumes "FLTick0 Tick x" "fl \<in> x" "e \<in>\<^sub>\<F>\<^sub>\<L> last fl" "e \<noteq> Tick"
  shows "FLTick0 Tick (x \<union> {fl\<^sub>0. fl\<^sub>0 \<le>\<^sub>\<F>\<^sub>\<L> (fl @\<^sub>\<F>\<^sub>\<L> \<langle>(last fl,e)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>)})"
  using assms
  unfolding FLTick0_def apply auto
  using tickWF_cons_prefix by blast

lemma FL1_extends_strong_less_eq_fltrace_last_bullet:
  assumes "FL1 x" "fl \<in> x" "last fl = \<bullet>"
  shows "FL1 (x \<union> {fl\<^sub>0. fl\<^sub>0 \<le>\<^sub>\<F>\<^sub>\<L> (fl @\<^sub>\<F>\<^sub>\<L> \<langle>(last fl,e)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>)})"
  using assms apply (auto)
  unfolding FL1_def
  by (metis Un_iff fl_cons_acceptance_consFL mem_Collect_eq strong_less_eq_fltrace_less_eq_common)

lemma FL0_Tick_extends_strong_less_eq_fltrace_last_bullet:
  assumes "FLTick0 Tick x" "fl \<in> x" "last fl = \<bullet>" "Tick \<notin> events fl"
  shows "FLTick0 Tick (x \<union> {fl\<^sub>0. fl\<^sub>0 \<le>\<^sub>\<F>\<^sub>\<L> (fl @\<^sub>\<F>\<^sub>\<L> \<langle>(last fl,e)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>)})"
  using assms apply (auto)
  unfolding FLTick0_def apply auto
  by (metis tickWF_concatFL_prefix_last)

lemma FL1_extends_strong_less_eq_fltrace_acceptance:
  assumes "FL1 x" "fl \<in> x" 
  shows "FL1 (x \<union> {fl\<^sub>0. fl\<^sub>0 \<le>\<^sub>\<F>\<^sub>\<L> (fl @\<^sub>\<F>\<^sub>\<L> \<langle>X\<rangle>\<^sub>\<F>\<^sub>\<L>)})"
  using assms unfolding FL1_def 
  using strong_less_eq_fltrace_less_eq_common_singleton by blast

lemma FL0Tick_extends_strong_less_eq_fltrace_acceptance:
  assumes "FLTick0 Tick x" "fl \<in> x" "Tick \<notin>\<^sub>\<F>\<^sub>\<L> X" "Tick \<notin> events fl"
  shows "FLTick0 Tick (x \<union> {fl\<^sub>0. fl\<^sub>0 \<le>\<^sub>\<F>\<^sub>\<L> (fl @\<^sub>\<F>\<^sub>\<L> \<langle>X\<rangle>\<^sub>\<F>\<^sub>\<L>)})"
  using assms
  by (metis (no_types, lifting) FLTick0_def UnE mem_Collect_eq tickWF_concatFL_acceptance_imp tickWF_prefix_imp)

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

lemma CTwf_concat_two_events_not_Tick_butlast:
  assumes "ys @ [[e1]\<^sub>E] @ [[e2]\<^sub>E] \<in> P" "CTwf P" 
  shows "e1 \<noteq> Tick"
proof -
  have "cttWF (ys @ [[e1]\<^sub>E] @ [[e2]\<^sub>E])"
    using assms unfolding CTwf_def by auto
  then show ?thesis
    by (induct ys rule:cttWF.induct, auto)
qed

lemma CTwf_concat_prefix_set_no_Tick:
  assumes "ys @ [[e1]\<^sub>E] \<in> P" "CTwf P" 
  shows "[Tick]\<^sub>E \<notin> set ys"
proof -
  have "cttWF (ys @ [[e1]\<^sub>E])"
    using assms unfolding CTwf_def by auto
  then show ?thesis
    by (induct ys rule:cttWF.induct, auto)
qed

lemma CTwf_concat_prefix_of_ref_set_no_Tick:
  assumes "ys @ [[e1]\<^sub>R] \<in> P" "CTwf P" 
  shows "[Tick]\<^sub>E \<notin> set ys"
proof -
  have "cttWF (ys @ [[e1]\<^sub>R])"
    using assms unfolding CTwf_def by auto
  then show ?thesis
    by (induct ys rule:cttWF.induct, auto)
qed

lemma event_not_in_set_of_flt2cttobs_imp_not_in_events:
  assumes "[e]\<^sub>E \<notin> set ys" "flt2cttobs zs = ys" "flt2goodTock zs"
  shows "e \<notin> events zs"
  using assms apply (induct zs arbitrary: ys e rule:flt2cttobs.induct, auto) 
   apply (case_tac A, auto, cases e, auto)
    apply (cases e, auto)
    apply (case_tac b, auto, case_tac a, auto)
   apply (case_tac b, auto, case_tac a, auto)
    apply (case_tac b, auto, case_tac b, auto)
  apply (case_tac A, auto)
   apply (case_tac b, auto, case_tac a, auto, case_tac a, auto, case_tac a, auto)
  by (case_tac b, auto)

(* TODO: Specialize the following for (\<exists>ar. prirelRef p ar x [] P \<and> x \<in> P),
         then can strengthen this to consider fl that is flt2goodAcceptance.

         So effectively, we want to ascertain, even for x \<in> P that we if
         there is an effective prioritisation, then we can find, for a
         stable refusal in P related to the event in x. 

         But this cannot be done directly, so flt2goodAcceptance must only
         require the existence of 'refusals'/'acceptances' for events that
         are non-maximal in the trace. *)

lemma CTwf_1c_3_imp_flt2cttobs_FL1:
  assumes "x \<in> P" 
      and CTwf_healthy: "CTwf P" 
      and CT1c_healthy: "CT1c P"
      and CT3_healthy:  "CT3 P"
      and CTTick_healthy: "CTTick P"
      and CT4_healthy: "CT4 P"
  shows "\<exists>fl. x = flt2cttobs fl \<and> flt2goodTock fl \<and> (\<exists>x. FLTick0 Tick x \<and> FL1 x \<and> {flt2cttobs fl |fl. fl \<in> x} \<subseteq> P \<and> fl \<in> x)"
  using assms
proof(induct x rule:rev_induct)
  case Nil
  then show ?case 
    apply (intro exI[where x="\<langle>\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>"], auto)
    apply (rule exI[where x="{\<langle>\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>}"], auto)
    unfolding FL1_def apply auto
    unfolding FLTick0_def apply auto
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
      then have "Tick \<in> x1"
        using CTRMax_CT4_Tick CT4_healthy CTTick_healthy
        using CTTick_def snoc.prems(1) by blast
      then show ?thesis
          apply (intro exI[where x="\<langle>[{x. x \<notin> x1} - {Tick}]\<^sub>\<F>\<^sub>\<L>\<rangle>\<^sub>\<F>\<^sub>\<L>"], auto)
          using Ref apply auto
           apply (rule exI[where x="{z. z \<le> \<langle>[{z. z \<notin> x1} - {Tick}]\<^sub>\<F>\<^sub>\<L>\<rangle>\<^sub>\<F>\<^sub>\<L>}"], auto)
        unfolding FLTick0_def apply auto
          apply (case_tac x, auto)
        apply (metis (full_types) amember.elims(2) less_eq_acceptance.simps(3) mem_Collect_eq)
        using FL1_def dual_order.trans apply blast
        using fl_le_CT1c using Nil by auto
      (*next
        case False
        then show ?thesis
          using Ref apply (intro exI[where x="\<langle>[{x. x \<notin> x1} - {Tick}]\<^sub>\<F>\<^sub>\<L>\<rangle>\<^sub>\<F>\<^sub>\<L>"], auto)
          apply (rule exI[where x="{z. z \<le> \<langle>[{z. z \<notin> x1} - {Tick}]\<^sub>\<F>\<^sub>\<L>\<rangle>\<^sub>\<F>\<^sub>\<L>}"], auto)
        unfolding FLTick0_def apply auto
          apply (case_tac x, auto)
        apply (case_tac x1a, auto)
        sledgehammer
        using FL1_def dual_order.trans apply blast
        using fl_le_CT1c using Nil by auto
      qed*)
        
    next
      case (ObsEvent x2)
      then show ?thesis
      proof (cases x2)
        case (Event ev)
        then show ?thesis
          apply (intro exI[where x="\<langle>(\<bullet>,Event ev)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>"])
          apply (simp add:ObsEvent)
          apply (intro exI[where x="{z. z \<le> \<langle>(\<bullet>,Event ev)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>}"], auto)
          unfolding FLTick0_def apply auto
          apply (metis acceptance_set amember.simps(1) bullet_left_zero2 tickWF.simps(1) tickWF.simps(2) x_le_x_concat2 xs_less_eq_z_two_only)
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
          unfolding FLTick0_def apply auto
          apply (metis acceptance_set amember.simps(1) bullet_left_zero2 tickWF.simps(1) tickWF.simps(2) x_le_x_concat2 xs_less_eq_z_two_only)
          using FL1_def dual_order.trans apply blast
          using ObsEvent Nil by (simp add:fl_le_CT1c_Tick)
      qed
    qed
  next
    case yys:(snoc y ys)
    then have ys_y_inP:"ys @ [y] \<in> P" using CT1c_def
      by (metis ctt_prefix_concat)
    then have ys_y_fl:"\<exists>fl. ys @ [y] = flt2cttobs fl \<and> flt2goodTock fl \<and> (\<exists>x. FLTick0 Tick x \<and> FL1 x \<and> {flt2cttobs fl |fl. fl \<in> x} \<subseteq> P \<and> fl \<in> x)"
      using yys by auto
    then have ys_y_x: "\<exists>fl. ys @ [y] @ [x] = flt2cttobs fl @ [x] \<and> flt2goodTock fl \<and> (\<exists>x. FLTick0 Tick x \<and> FL1 x \<and> {flt2cttobs fl |fl. fl \<in> x} \<subseteq> P \<and> fl \<in> x)"
      by auto

    then show ?case
    proof (cases y)
      case r1:(Ref r1)
      then have exp:"\<exists>fl. ys @ [[r1]\<^sub>R] @ [x] = flt2cttobs fl @ [x] \<and> (\<exists>x. FLTick0 Tick x \<and> FL1 x \<and> {flt2cttobs fl |fl. fl \<in> x} \<subseteq> P \<and> fl \<in> x)"
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

          then obtain fl where fl:"ys @ [Ref r1] = flt2cttobs fl \<and> flt2goodTock fl \<and> (\<exists>x. FLTick0 Tick x \<and> FL1 x \<and>  {flt2cttobs fl |fl. fl \<in> x} \<subseteq> P \<and> fl \<in> x)"
            using r1 ys_y_fl by blast
          then have last_fl_acceptance:"last fl = [{x. x \<notin> r1}]\<^sub>\<F>\<^sub>\<L>"
            by (metis (mono_tags, lifting) last_flt2cttobs_eq_ref_imp_last snoc_eq_iff_butlast)
          then have tock_in_last_fl: "Tock \<in>\<^sub>\<F>\<^sub>\<L> last fl"
            using tock_not_in_r1 by simp
          then have "ys @ [[r1]\<^sub>R] @ [[Tock]\<^sub>E] = flt2cttobs fl @ [[Tock]\<^sub>E] \<and> flt2goodTock fl \<and> (\<exists>x. FLTick0 Tick x \<and> FL1 x \<and> {flt2cttobs fl |fl. fl \<in> x} \<subseteq> P \<and> fl \<in> x)"
            by (simp add: fl)
          then have "ys @ [[r1]\<^sub>R] @ [[Tock]\<^sub>E] = flt2cttobs (fl @\<^sub>\<F>\<^sub>\<L> \<langle>(last fl,Tock)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>) \<and> flt2goodTock fl \<and> (\<exists>x. FLTick0 Tick x \<and> FL1 x \<and> {flt2cttobs fl |fl. fl \<in> x} \<subseteq> P \<and> fl \<in> x)"
            using tock_in_last_fl by (simp add: flt2cttobs_last_tock fl)

          have "{flt2cttobs fl\<^sub>0|fl\<^sub>0. fl\<^sub>0 \<le> fl} \<subseteq> P"
            using CT1c_healthy 
            using FL1_def fl subset_eq by blast

          have flt2cttobs_strongFL_subset:"{flt2cttobs fl\<^sub>0|fl\<^sub>0. fl\<^sub>0 \<le>\<^sub>\<F>\<^sub>\<L> (fl @\<^sub>\<F>\<^sub>\<L> \<langle>(last fl,Tock)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>)} \<subseteq> P"
            apply auto
            using strong_less_eq_fltrace_imp_flt2cttobs_ctt
            by (metis (no_types, lifting) CT1c_def CT1c_healthy ObsEvent Tock \<open>ys @ [[r1]\<^sub>R] @ [[Tock]\<^sub>E] = flt2cttobs (fl @\<^sub>\<F>\<^sub>\<L> \<langle>(Finite_Linear_Model.last fl,Tock)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>) \<and> flt2goodTock fl \<and> (\<exists>x. FLTick0 Tick x \<and> FL1 x \<and> {flt2cttobs fl |fl. fl \<in> x} \<subseteq> P \<and> fl \<in> x)\<close> \<open>ys @ [[r1]\<^sub>R] @ [[Tock]\<^sub>E] = flt2cttobs fl @ [[Tock]\<^sub>E] \<and> flt2goodTock fl \<and> (\<exists>x. FLTick0 Tick x \<and> FL1 x \<and> {flt2cttobs fl |fl. fl \<in> x} \<subseteq> P \<and> fl \<in> x)\<close> fl r1 yys.prems(2))

          have "(ys @ [[r1]\<^sub>R] @ [[Tock]\<^sub>E] = flt2cttobs(fl @\<^sub>\<F>\<^sub>\<L> \<langle>(last fl,Tock)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>) \<and> flt2goodTock fl
                \<and> (\<exists>x. FLTick0 Tick x \<and> FL1 x \<and> {flt2cttobs fl |fl. fl \<in> x} \<subseteq> P \<and> fl \<in> x))"
            using \<open>ys @ [[r1]\<^sub>R] @ [[Tock]\<^sub>E] = flt2cttobs (fl @\<^sub>\<F>\<^sub>\<L> \<langle>(Finite_Linear_Model.last fl,Tock)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>) \<and> flt2goodTock fl \<and> (\<exists>x. FLTick0 Tick x \<and> FL1 x \<and> {flt2cttobs fl |fl. fl \<in> x} \<subseteq> P \<and> fl \<in> x)\<close> tock_in_last_fl by blast
          then have 
               "ys @ [[r1]\<^sub>R] @ [[Tock]\<^sub>E] = flt2cttobs (fl @\<^sub>\<F>\<^sub>\<L> \<langle>(last fl,Tock)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>) \<and> flt2goodTock fl  
                \<and> (\<exists>x. FLTick0 Tick x \<and> FL1 (x \<union> {fl\<^sub>0. fl\<^sub>0 \<le>\<^sub>\<F>\<^sub>\<L> (fl @\<^sub>\<F>\<^sub>\<L> \<langle>(last fl,Tock)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>)}) \<and> {flt2cttobs fl |fl. fl \<in> x} \<subseteq> P \<and> fl \<in> x)"
            using FL1_extends_strong_less_eq_fltrace_last tock_in_last_fl
            by (metis (mono_tags, lifting) Collect_cong \<open>ys @ [[r1]\<^sub>R] @ [[Tock]\<^sub>E] = flt2cttobs (fl @\<^sub>\<F>\<^sub>\<L> \<langle>(Finite_Linear_Model.last fl,Tock)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>) \<and> flt2goodTock fl \<and> (\<exists>x. FLTick0 Tick x \<and> FL1 x \<and> {flt2cttobs fl |fl. fl \<in> x} \<subseteq> P \<and> fl \<in> x)\<close> fl)
          then have 
               "ys @ [[r1]\<^sub>R] @ [[Tock]\<^sub>E] = flt2cttobs (fl @\<^sub>\<F>\<^sub>\<L> \<langle>(last fl,Tock)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>) \<and> flt2goodTock fl  
                \<and> (\<exists>x. FLTick0 Tick (x \<union> {fl\<^sub>0. fl\<^sub>0 \<le>\<^sub>\<F>\<^sub>\<L> (fl @\<^sub>\<F>\<^sub>\<L> \<langle>(last fl,Tock)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>)}) 
                        \<and> FL1 (x \<union> {fl\<^sub>0. fl\<^sub>0 \<le>\<^sub>\<F>\<^sub>\<L> (fl @\<^sub>\<F>\<^sub>\<L> \<langle>(last fl,Tock)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>)}) \<and> {flt2cttobs fl |fl. fl \<in> x} \<subseteq> P \<and> fl \<in> x)"
            using FLTick0_extends_strong_less_eq_fltrace_last tock_in_last_fl
            by auto
          then have 
               "ys @ [[r1]\<^sub>R] @ [[Tock]\<^sub>E] = flt2cttobs (fl @\<^sub>\<F>\<^sub>\<L> \<langle>(last fl,Tock)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>) \<and> flt2goodTock fl 
                \<and> (\<exists>x. FLTick0 Tick (x \<union> {fl\<^sub>0. fl\<^sub>0 \<le>\<^sub>\<F>\<^sub>\<L> (fl @\<^sub>\<F>\<^sub>\<L> \<langle>(last fl,Tock)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>)}) 
                    \<and> FL1 (x \<union> {fl\<^sub>0. fl\<^sub>0 \<le>\<^sub>\<F>\<^sub>\<L> (fl @\<^sub>\<F>\<^sub>\<L> \<langle>(last fl,Tock)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>)})
                    \<and> {flt2cttobs fl\<^sub>0 |fl\<^sub>0. fl\<^sub>0 \<in> (x \<union> {fl\<^sub>0. fl\<^sub>0 \<le>\<^sub>\<F>\<^sub>\<L> (fl @\<^sub>\<F>\<^sub>\<L> \<langle>(last fl,Tock)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>)})} \<subseteq> P \<and> fl \<in> x)"
            using flt2cttobs_strongFL_subset
            by (smt Un_iff mem_Collect_eq subset_iff)
          then have 
               "ys @ [[r1]\<^sub>R] @ [[Tock]\<^sub>E] = flt2cttobs (fl @\<^sub>\<F>\<^sub>\<L> \<langle>(last fl,Tock)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>) \<and> flt2goodTock fl 
                \<and> (\<exists>x. FLTick0 Tick (x \<union> {fl\<^sub>0. fl\<^sub>0 \<le>\<^sub>\<F>\<^sub>\<L> (fl @\<^sub>\<F>\<^sub>\<L> \<langle>(last fl,Tock)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>)}) 
                \<and> FL1 (x \<union> {fl\<^sub>0. fl\<^sub>0 \<le>\<^sub>\<F>\<^sub>\<L> (fl @\<^sub>\<F>\<^sub>\<L> \<langle>(last fl,Tock)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>)})
                \<and> {flt2cttobs fl\<^sub>0 |fl\<^sub>0. fl\<^sub>0 \<in> (x \<union> {fl\<^sub>0. fl\<^sub>0 \<le>\<^sub>\<F>\<^sub>\<L> (fl @\<^sub>\<F>\<^sub>\<L> \<langle>(last fl,Tock)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>)})} \<subseteq> P 
                \<and> fl \<in> x
                \<and> fl @\<^sub>\<F>\<^sub>\<L> \<langle>(last fl,Tock)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L> \<in> (x \<union> {fl\<^sub>0. fl\<^sub>0 \<le>\<^sub>\<F>\<^sub>\<L> (fl @\<^sub>\<F>\<^sub>\<L> \<langle>(last fl,Tock)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>)}))"
            by (simp add: strong_less_eq_fltrace_refl)
          then have 
               "ys @ [[r1]\<^sub>R] @ [[Tock]\<^sub>E] = flt2cttobs (fl @\<^sub>\<F>\<^sub>\<L> \<langle>(last fl,Tock)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>) \<and> flt2goodTock fl 
                \<and> (\<exists>z. FLTick0 Tick z \<and> FL1 z
                \<and> {flt2cttobs fl\<^sub>0 |fl\<^sub>0. fl\<^sub>0 \<in> z} \<subseteq> P 
                \<and> fl @\<^sub>\<F>\<^sub>\<L> \<langle>(last fl,Tock)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L> \<in> z)"
            by blast
          then have 
               "ys @ [[r1]\<^sub>R] @ [[Tock]\<^sub>E] = flt2cttobs (fl @\<^sub>\<F>\<^sub>\<L> \<langle>(last fl,Tock)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>) \<and> flt2goodTock fl 
                \<and> flt2goodTock (fl @\<^sub>\<F>\<^sub>\<L> \<langle>(last fl,Tock)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>)
                \<and> (\<exists>z. FLTick0 Tick z \<and> FL1 z
                \<and> {flt2cttobs fl\<^sub>0 |fl\<^sub>0. fl\<^sub>0 \<in> z} \<subseteq> P 
                \<and> fl @\<^sub>\<F>\<^sub>\<L> \<langle>(last fl,Tock)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L> \<in> z)"
            using tock_in_last_fl by (simp add:flt2goodTock_extend_consFL_last_fl_e)
          then have 
               "\<exists>fl. ys @ [[r1]\<^sub>R] @ [[Tock]\<^sub>E] = flt2cttobs fl \<and> flt2goodTock fl 
                \<and> (\<exists>z. FLTick0 Tick z \<and> FL1 z \<and> {flt2cttobs fl\<^sub>0 |fl\<^sub>0. fl\<^sub>0 \<in> z} \<subseteq> P \<and> fl \<in> z)"
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
      then obtain fl where fl:"ys @ [[e1]\<^sub>E] = flt2cttobs fl \<and> flt2goodTock fl \<and> (\<exists>x. FLTick0 Tick x \<and> FL1 x \<and> {flt2cttobs fl |fl. fl \<in> x} \<subseteq> P \<and> fl \<in> x)"
        using ys_y_fl by blast
      then have ys_e1_x:"ys @ [[e1]\<^sub>E] @ [x] = flt2cttobs fl @ [x] \<and> flt2goodTock fl \<and> (\<exists>x. FLTick0 Tick x \<and> FL1 x \<and> {flt2cttobs fl |fl. fl \<in> x} \<subseteq> P \<and> fl \<in> x)"
        by auto
      then have last_fl:"last fl = \<bullet>"
        by (metis cttobs.distinct(1) fl flt2cttobs.simps(1) flt2cttobs_last_fl_not_bullet_dist_list_cons last_snoc)

      then show ?thesis
      proof (cases x)
        case e2:(ObsEvent e2)
        then have "ys @ [[e1]\<^sub>E] @ [[e2]\<^sub>E] \<in> P"
          using e1 fl ys_e1_x yys.prems(2) by presburger
        then have "[Tick]\<^sub>E \<notin> set (ys @ [[e1]\<^sub>E])" 
          using CTwf_healthy CTwf_concat_prefix_set_no_Tick
          using e1 e2 yys.prems(2) by blast
        then have Tick_not_in_events_fl: "Tick \<notin> events fl"
          by (simp add: event_not_in_set_of_flt2cttobs_imp_not_in_events fl)
          
        then show ?thesis
        proof (cases e2)
          case (Event e3)
          have flt2cttobs_strongFL_subset:"{flt2cttobs fl\<^sub>0|fl\<^sub>0. fl\<^sub>0 \<le>\<^sub>\<F>\<^sub>\<L> (fl @\<^sub>\<F>\<^sub>\<L> \<langle>(last fl,Event e3)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>)} \<subseteq> P"
            apply auto
            using strong_less_eq_fltrace_imp_flt2cttobs_ctt
            by (metis (no_types, lifting) CT1c_def CT1c_healthy Event cttevent.simps(3) e1 e2 fl flt2cttobs_last_non_tock last_fl last_snoc yys.prems(2))
          
          from fl have fl_e3: "ys @ [[e1]\<^sub>E] @ [[Event e3]\<^sub>E] = flt2cttobs fl @ [[Event e3]\<^sub>E]
                  \<and> flt2goodTock fl \<and> (\<exists>x. FLTick0 Tick x \<and> FL1 x \<and> {flt2cttobs fl\<^sub>0 |fl\<^sub>0. fl\<^sub>0 \<in> x} \<subseteq> P \<and> fl \<in> x)"
            using ys_e1_x by auto
          also have "... =
                  (ys @ [[e1]\<^sub>E] @ [[Event e3]\<^sub>E] = flt2cttobs(fl @\<^sub>\<F>\<^sub>\<L> \<langle>(last fl,Event e3)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>)
                  \<and> flt2goodTock fl \<and> (\<exists>x. FLTick0 Tick x \<and> FL1 x \<and> {flt2cttobs fl\<^sub>0 |fl\<^sub>0. fl\<^sub>0 \<in> x} \<subseteq> P \<and> fl \<in> x))"
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
                  \<and> (\<exists>x. FLTick0 Tick x \<and> FL1 (x \<union> {fl\<^sub>0. fl\<^sub>0 \<le>\<^sub>\<F>\<^sub>\<L> (fl @\<^sub>\<F>\<^sub>\<L> \<langle>(last fl,Event e3)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>)}) 
                      \<and> {flt2cttobs fl\<^sub>0 |fl\<^sub>0. fl\<^sub>0 \<in> x} \<subseteq> P \<and> fl \<in> x)"
              apply auto using FL1_extends_strong_less_eq_fltrace_last_bullet last_fl 
            by fastforce
          then have "
                  ys @ [[e1]\<^sub>E] @ [[Event e3]\<^sub>E] = flt2cttobs(fl @\<^sub>\<F>\<^sub>\<L> \<langle>(last fl,Event e3)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>)
                  \<and> flt2goodTock fl 
                  \<and> (\<exists>x. FLTick0 Tick (x \<union> {fl\<^sub>0. fl\<^sub>0 \<le>\<^sub>\<F>\<^sub>\<L> (fl @\<^sub>\<F>\<^sub>\<L> \<langle>(last fl,Event e3)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>)}) 
                      \<and> FL1 (x \<union> {fl\<^sub>0. fl\<^sub>0 \<le>\<^sub>\<F>\<^sub>\<L> (fl @\<^sub>\<F>\<^sub>\<L> \<langle>(last fl,Event e3)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>)}) 
                      \<and> {flt2cttobs fl\<^sub>0 |fl\<^sub>0. fl\<^sub>0 \<in> x} \<subseteq> P \<and> fl \<in> x)"
            apply auto using FL0_Tick_extends_strong_less_eq_fltrace_last_bullet last_fl Tick_not_in_events_fl
            by blast
         then have "
                  ys @ [[e1]\<^sub>E] @ [[Event e3]\<^sub>E] = flt2cttobs(fl @\<^sub>\<F>\<^sub>\<L> \<langle>(last fl,Event e3)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>)
                  \<and> flt2goodTock fl 
                  \<and> (\<exists>x. FLTick0 Tick (x \<union> {fl\<^sub>0. fl\<^sub>0 \<le>\<^sub>\<F>\<^sub>\<L> (fl @\<^sub>\<F>\<^sub>\<L> \<langle>(last fl,Event e3)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>)}) 
                      \<and> FL1 (x \<union> {fl\<^sub>0. fl\<^sub>0 \<le>\<^sub>\<F>\<^sub>\<L> (fl @\<^sub>\<F>\<^sub>\<L> \<langle>(last fl,Event e3)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>)}) 
                      \<and> {flt2cttobs fl\<^sub>0 |fl\<^sub>0. fl\<^sub>0 \<in> (x \<union> {fl\<^sub>0. fl\<^sub>0 \<le>\<^sub>\<F>\<^sub>\<L> (fl @\<^sub>\<F>\<^sub>\<L> \<langle>(last fl,Event e3)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>)})} \<subseteq> P \<and> fl \<in> x)"  
           using flt2cttobs_strongFL_subset 
           by (smt Un_iff mem_Collect_eq subset_iff)
         then have "
                  ys @ [[e1]\<^sub>E] @ [[Event e3]\<^sub>E] = flt2cttobs(fl @\<^sub>\<F>\<^sub>\<L> \<langle>(last fl,Event e3)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>)
                  \<and> flt2goodTock fl 
                  \<and> (\<exists>x. FLTick0 Tick (x \<union> {fl\<^sub>0. fl\<^sub>0 \<le>\<^sub>\<F>\<^sub>\<L> (fl @\<^sub>\<F>\<^sub>\<L> \<langle>(last fl,Event e3)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>)}) 
                      \<and> FL1 (x \<union> {fl\<^sub>0. fl\<^sub>0 \<le>\<^sub>\<F>\<^sub>\<L> (fl @\<^sub>\<F>\<^sub>\<L> \<langle>(last fl,Event e3)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>)}) 
                      \<and> {flt2cttobs fl\<^sub>0 |fl\<^sub>0. fl\<^sub>0 \<in> (x \<union> {fl\<^sub>0. fl\<^sub>0 \<le>\<^sub>\<F>\<^sub>\<L> (fl @\<^sub>\<F>\<^sub>\<L> \<langle>(last fl,Event e3)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>)})} \<subseteq> P 
                      \<and> fl \<in> x
                      \<and> fl @\<^sub>\<F>\<^sub>\<L> \<langle>(last fl,Event e3)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L> \<in> (x \<union> {fl\<^sub>0. fl\<^sub>0 \<le>\<^sub>\<F>\<^sub>\<L> (fl @\<^sub>\<F>\<^sub>\<L> \<langle>(last fl,Event e3)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>)}))"
            by (simp add: strong_less_eq_fltrace_refl)  
         then have "
                  ys @ [[e1]\<^sub>E] @ [[Event e3]\<^sub>E] = flt2cttobs(fl @\<^sub>\<F>\<^sub>\<L> \<langle>(last fl,Event e3)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>)
                  \<and> flt2goodTock fl 
                  \<and> (\<exists>z. FLTick0 Tick z \<and> FL1 z 
                      \<and> {flt2cttobs fl\<^sub>0 |fl\<^sub>0. fl\<^sub>0 \<in> z} \<subseteq> P 
                      \<and> fl @\<^sub>\<F>\<^sub>\<L> \<langle>(last fl,Event e3)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L> \<in> z)"
           by blast
         then have "
                  ys @ [[e1]\<^sub>E] @ [[Event e3]\<^sub>E] = flt2cttobs(fl @\<^sub>\<F>\<^sub>\<L> \<langle>(last fl,Event e3)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>)
                  \<and> flt2goodTock fl 
                  \<and> flt2goodTock (fl @\<^sub>\<F>\<^sub>\<L> \<langle>(last fl,Event e3)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>)
                  \<and> (\<exists>z. FLTick0 Tick z \<and> FL1 z 
                      \<and> {flt2cttobs fl\<^sub>0 |fl\<^sub>0. fl\<^sub>0 \<in> z} \<subseteq> P 
                      \<and> fl @\<^sub>\<F>\<^sub>\<L> \<langle>(last fl,Event e3)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L> \<in> z)"
           using last_fl flt2goodTock_extend_consFL_last_fl_bullet
           by blast
         then have "
                  \<exists>fl. ys @ [[e1]\<^sub>E] @ [[Event e3]\<^sub>E] = flt2cttobs(fl)
                  \<and> flt2goodTock fl 
                  \<and> (\<exists>z. FLTick0 Tick z \<and> FL1 z \<and> {flt2cttobs fl\<^sub>0 |fl\<^sub>0. fl\<^sub>0 \<in> z} \<subseteq> P \<and> fl \<in> z)"
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
                  \<and> flt2goodTock fl \<and> (\<exists>x. FLTick0 Tick x \<and> FL1 x \<and> {flt2cttobs fl\<^sub>0 |fl\<^sub>0. fl\<^sub>0 \<in> x} \<subseteq> P \<and> fl \<in> x)"
            using ys_e1_x by auto
          also have "... =
                  (ys @ [[e1]\<^sub>E] @ [[Tick]\<^sub>E] = flt2cttobs(fl @\<^sub>\<F>\<^sub>\<L> \<langle>(last fl,Tick)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>)
                  \<and> flt2goodTock fl \<and> (\<exists>x. FLTick0 Tick x \<and> FL1 x \<and> {flt2cttobs fl\<^sub>0 |fl\<^sub>0. fl\<^sub>0 \<in> x} \<subseteq> P \<and> fl \<in> x))"
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
                  \<and> (\<exists>x. FLTick0 Tick x \<and> FL1 (x \<union> {fl\<^sub>0. fl\<^sub>0 \<le>\<^sub>\<F>\<^sub>\<L> (fl @\<^sub>\<F>\<^sub>\<L> \<langle>(last fl,Tick)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>)}) 
                      \<and> {flt2cttobs fl\<^sub>0 |fl\<^sub>0. fl\<^sub>0 \<in> x} \<subseteq> P \<and> fl \<in> x)"
              apply auto using FL1_extends_strong_less_eq_fltrace_last_bullet last_fl 
            by fastforce
         then have "
                  ys @ [[e1]\<^sub>E] @ [[Tick]\<^sub>E] = flt2cttobs(fl @\<^sub>\<F>\<^sub>\<L> \<langle>(last fl,Tick)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>)
                  \<and> flt2goodTock fl 
                  \<and> (\<exists>x. FLTick0 Tick (x \<union> {fl\<^sub>0. fl\<^sub>0 \<le>\<^sub>\<F>\<^sub>\<L> (fl @\<^sub>\<F>\<^sub>\<L> \<langle>(last fl,Tick)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>)}) 
                      \<and> FL1 (x \<union> {fl\<^sub>0. fl\<^sub>0 \<le>\<^sub>\<F>\<^sub>\<L> (fl @\<^sub>\<F>\<^sub>\<L> \<langle>(last fl,Tick)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>)}) 
                      \<and> {flt2cttobs fl\<^sub>0 |fl\<^sub>0. fl\<^sub>0 \<in> x} \<subseteq> P \<and> fl \<in> x)"
          apply auto using FL0_Tick_extends_strong_less_eq_fltrace_last_bullet last_fl Tick_not_in_events_fl
            by blast
         then have "
                  ys @ [[e1]\<^sub>E] @ [[Tick]\<^sub>E] = flt2cttobs(fl @\<^sub>\<F>\<^sub>\<L> \<langle>(last fl,Tick)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>)
                  \<and> flt2goodTock fl 
                  \<and> (\<exists>x. FLTick0 Tick (x \<union> {fl\<^sub>0. fl\<^sub>0 \<le>\<^sub>\<F>\<^sub>\<L> (fl @\<^sub>\<F>\<^sub>\<L> \<langle>(last fl,Tick)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>)}) 
                      \<and> FL1 (x \<union> {fl\<^sub>0. fl\<^sub>0 \<le>\<^sub>\<F>\<^sub>\<L> (fl @\<^sub>\<F>\<^sub>\<L> \<langle>(last fl,Tick)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>)}) 
                      \<and> {flt2cttobs fl\<^sub>0 |fl\<^sub>0. fl\<^sub>0 \<in> (x \<union> {fl\<^sub>0. fl\<^sub>0 \<le>\<^sub>\<F>\<^sub>\<L> (fl @\<^sub>\<F>\<^sub>\<L> \<langle>(last fl,Tick)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>)})} \<subseteq> P \<and> fl \<in> x)"  
           using flt2cttobs_strongFL_subset 
           by (smt Un_iff mem_Collect_eq subset_iff)
         then have "
                  ys @ [[e1]\<^sub>E] @ [[Tick]\<^sub>E] = flt2cttobs(fl @\<^sub>\<F>\<^sub>\<L> \<langle>(last fl,Tick)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>)
                  \<and> flt2goodTock fl 
                  \<and> (\<exists>x. FLTick0 Tick (x \<union> {fl\<^sub>0. fl\<^sub>0 \<le>\<^sub>\<F>\<^sub>\<L> (fl @\<^sub>\<F>\<^sub>\<L> \<langle>(last fl,Tick)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>)}) 
                      \<and> FL1 (x \<union> {fl\<^sub>0. fl\<^sub>0 \<le>\<^sub>\<F>\<^sub>\<L> (fl @\<^sub>\<F>\<^sub>\<L> \<langle>(last fl,Tick)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>)}) 
                      \<and> {flt2cttobs fl\<^sub>0 |fl\<^sub>0. fl\<^sub>0 \<in> (x \<union> {fl\<^sub>0. fl\<^sub>0 \<le>\<^sub>\<F>\<^sub>\<L> (fl @\<^sub>\<F>\<^sub>\<L> \<langle>(last fl,Tick)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>)})} \<subseteq> P 
                      \<and> fl \<in> x
                      \<and> fl @\<^sub>\<F>\<^sub>\<L> \<langle>(last fl,Tick)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L> \<in> (x \<union> {fl\<^sub>0. fl\<^sub>0 \<le>\<^sub>\<F>\<^sub>\<L> (fl @\<^sub>\<F>\<^sub>\<L> \<langle>(last fl,Tick)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>)}))"
            by (simp add: strong_less_eq_fltrace_refl)  
         then have "
                  ys @ [[e1]\<^sub>E] @ [[Tick]\<^sub>E] = flt2cttobs(fl @\<^sub>\<F>\<^sub>\<L> \<langle>(last fl,Tick)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>)
                  \<and> flt2goodTock fl 
                  \<and> (\<exists>z. FLTick0 Tick z \<and> FL1 z 
                      \<and> {flt2cttobs fl\<^sub>0 |fl\<^sub>0. fl\<^sub>0 \<in> z} \<subseteq> P 
                      \<and> fl @\<^sub>\<F>\<^sub>\<L> \<langle>(last fl,Tick)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L> \<in> z)"
           by blast
         then have "
                  ys @ [[e1]\<^sub>E] @ [[Tick]\<^sub>E] = flt2cttobs(fl @\<^sub>\<F>\<^sub>\<L> \<langle>(last fl,Tick)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>)
                  \<and> flt2goodTock fl 
                  \<and> flt2goodTock (fl @\<^sub>\<F>\<^sub>\<L> \<langle>(last fl,Tick)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>)
                  \<and> (\<exists>z. FLTick0 Tick z \<and> FL1 z 
                      \<and> {flt2cttobs fl\<^sub>0 |fl\<^sub>0. fl\<^sub>0 \<in> z} \<subseteq> P 
                      \<and> fl @\<^sub>\<F>\<^sub>\<L> \<langle>(last fl,Tick)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L> \<in> z)"
           using last_fl flt2goodTock_extend_consFL_last_fl_bullet
           by blast
         then have "
                  \<exists>fl. ys @ [[e1]\<^sub>E] @ [[Tick]\<^sub>E] = flt2cttobs(fl)
                  \<and> flt2goodTock fl 
                  \<and> (\<exists>z. FLTick0 Tick z \<and> FL1 z \<and> {flt2cttobs fl\<^sub>0 |fl\<^sub>0. fl\<^sub>0 \<in> z} \<subseteq> P \<and> fl \<in> z)"
           by blast
         then show ?thesis using Tick e1 e2 by auto
        qed
      next
        case (Ref r2)
        have Tick_in_r2:"Tick \<in> r2"
          using CT4_healthy CTRMax_CT4_Tick CTTick_healthy Ref
          using CTTick_def snoc.prems(1) by blast
        then have "ys @ [[e1]\<^sub>E] @ [[r2]\<^sub>R] \<in> P"
          using e1 Ref yys.prems(2) by auto
        then have "[Tick]\<^sub>E \<notin> set (ys @ [[e1]\<^sub>E])" 
          using CTwf_healthy CTwf_concat_prefix_of_ref_set_no_Tick
          using e1 Ref
          by (metis fl ys_e1_x)
        then have Tick_not_in_events_fl: "Tick \<notin> events fl"
          by (simp add: event_not_in_set_of_flt2cttobs_imp_not_in_events fl)
       (* have flt2cttobs_strongFL_subset:"{flt2cttobs fl\<^sub>0|fl\<^sub>0. fl\<^sub>0 \<le>\<^sub>\<F>\<^sub>\<L> (fl @\<^sub>\<F>\<^sub>\<L> \<langle>[{x. x \<notin> r2}]\<^sub>\<F>\<^sub>\<L>\<rangle>\<^sub>\<F>\<^sub>\<L>)} \<subseteq> P"
            apply auto
          using strong_less_eq_fltrace_imp_flt2cttobs_ctt
          sledgehammer[debug=true]
          by (metis CT1c_def CT1c_healthy Collect_cong Ref e1 fl flt2cttobs_fl_acceptance last_snoc mem_Collect_eq snoc_eq_iff_butlast subsetI subset_iff yys.prems(2))
        *)
        from fl have fl_e3: "ys @ [[e1]\<^sub>E] @ [[r2]\<^sub>R] = flt2cttobs fl @ [[r2]\<^sub>R]
                  \<and> flt2goodTock fl \<and> (\<exists>x. FLTick0 Tick x \<and> FL1 x \<and> {flt2cttobs fl\<^sub>0 |fl\<^sub>0. fl\<^sub>0 \<in> x} \<subseteq> P \<and> fl \<in> x)"
          using ys_e1_x by auto
        also have "... =
                  (ys @ [[e1]\<^sub>E] @ [[r2]\<^sub>R] = flt2cttobs(fl @\<^sub>\<F>\<^sub>\<L> \<langle>[{x. x \<notin> r2} - {Tick}]\<^sub>\<F>\<^sub>\<L>\<rangle>\<^sub>\<F>\<^sub>\<L>)
                  \<and> flt2goodTock fl \<and> (\<exists>x. FLTick0 Tick x \<and> FL1 x \<and> {flt2cttobs fl\<^sub>0 |fl\<^sub>0. fl\<^sub>0 \<in> x} \<subseteq> P \<and> fl \<in> x))"
          proof -
              from fl have "ys @ [[e1]\<^sub>E] = flt2cttobs fl"
                by auto
              then have "List.last(flt2cttobs fl) = [e1]\<^sub>E"
                by (metis last_snoc)
              then have "flt2cttobs fl @ [[r2]\<^sub>R] = flt2cttobs(fl @\<^sub>\<F>\<^sub>\<L> \<langle>[{x. x \<notin> r2} - {Tick}]\<^sub>\<F>\<^sub>\<L>\<rangle>\<^sub>\<F>\<^sub>\<L>)"
                using fl last_fl flt2cttobs_fl_acceptance Tick_in_r2
              proof -
                have "flt2cttobs fl \<noteq> []"
                  by (metis (no_types) append_is_Nil_conv fl not_Cons_self2)
                then show ?thesis
                  by (simp add: Tick_in_r2 \<open>List.last (flt2cttobs fl) = [e1]\<^sub>E\<close> fl flt2cttobs_fl_acceptance)
                qed
              then show ?thesis using calculation by auto
            qed
         finally have "
                  ys @ [[e1]\<^sub>E] @ [[r2]\<^sub>R] = flt2cttobs(fl @\<^sub>\<F>\<^sub>\<L> \<langle>[{x. x \<notin> r2} - {Tick}]\<^sub>\<F>\<^sub>\<L>\<rangle>\<^sub>\<F>\<^sub>\<L>)
                  \<and> flt2goodTock fl 
                  \<and> (\<exists>x. FLTick0 Tick x \<and> FL1 (x \<union> {fl\<^sub>0. fl\<^sub>0 \<le>\<^sub>\<F>\<^sub>\<L> (fl @\<^sub>\<F>\<^sub>\<L> \<langle>[{x. x \<notin> r2} - {Tick}]\<^sub>\<F>\<^sub>\<L>\<rangle>\<^sub>\<F>\<^sub>\<L>)}) 
                      \<and> {flt2cttobs fl\<^sub>0 |fl\<^sub>0. fl\<^sub>0 \<in> x} \<subseteq> P \<and> fl \<in> x)"
              apply auto using FL1_extends_strong_less_eq_fltrace_acceptance last_fl 
           by fastforce 
         then have "
                  ys @ [[e1]\<^sub>E] @ [[r2]\<^sub>R] = flt2cttobs(fl @\<^sub>\<F>\<^sub>\<L> \<langle>[{x. x \<notin> r2} - {Tick}]\<^sub>\<F>\<^sub>\<L>\<rangle>\<^sub>\<F>\<^sub>\<L>)
                  \<and> flt2goodTock fl 
                  \<and> (\<exists>x. FLTick0 Tick (x \<union> {fl\<^sub>0. fl\<^sub>0 \<le>\<^sub>\<F>\<^sub>\<L> (fl @\<^sub>\<F>\<^sub>\<L> \<langle>[{x. x \<notin> r2} - {Tick}]\<^sub>\<F>\<^sub>\<L>\<rangle>\<^sub>\<F>\<^sub>\<L>)})
                      \<and> FL1 (x \<union> {fl\<^sub>0. fl\<^sub>0 \<le>\<^sub>\<F>\<^sub>\<L> (fl @\<^sub>\<F>\<^sub>\<L> \<langle>[{x. x \<notin> r2}- {Tick}]\<^sub>\<F>\<^sub>\<L>\<rangle>\<^sub>\<F>\<^sub>\<L>)}) 
                      \<and> {flt2cttobs fl\<^sub>0 |fl\<^sub>0. fl\<^sub>0 \<in> x} \<subseteq> P \<and> fl \<in> x)"
            apply auto using FL0Tick_extends_strong_less_eq_fltrace_acceptance last_fl Tick_in_r2 Tick_not_in_events_fl
           by (smt Collect_cong Diff_empty Diff_insert0 FLTick0_def Un_iff amember.simps(2) mem_Collect_eq tickWF_concatFL_acceptance_imp tickWF_prefix_imp)
         then have "
                  ys @ [[e1]\<^sub>E] @ [[r2]\<^sub>R] = flt2cttobs(fl @\<^sub>\<F>\<^sub>\<L> \<langle>[{x. x \<notin> r2} - {Tick}]\<^sub>\<F>\<^sub>\<L>\<rangle>\<^sub>\<F>\<^sub>\<L>)
                  \<and> flt2goodTock fl 
                  \<and> (\<exists>x. FLTick0 Tick (x \<union> {fl\<^sub>0. fl\<^sub>0 \<le>\<^sub>\<F>\<^sub>\<L> (fl @\<^sub>\<F>\<^sub>\<L> \<langle>[{x. x \<notin> r2} - {Tick}]\<^sub>\<F>\<^sub>\<L>\<rangle>\<^sub>\<F>\<^sub>\<L>)})
                      \<and> FL1 (x \<union> {fl\<^sub>0. fl\<^sub>0 \<le>\<^sub>\<F>\<^sub>\<L> (fl @\<^sub>\<F>\<^sub>\<L> \<langle>[{x. x \<notin> r2} - {Tick}]\<^sub>\<F>\<^sub>\<L>\<rangle>\<^sub>\<F>\<^sub>\<L>)}) 
                      \<and> {flt2cttobs fl\<^sub>0 |fl\<^sub>0. fl\<^sub>0 \<in> (x \<union> {fl\<^sub>0. fl\<^sub>0 \<le>\<^sub>\<F>\<^sub>\<L> (fl @\<^sub>\<F>\<^sub>\<L> \<langle>[{x. x \<notin> r2} - {Tick}]\<^sub>\<F>\<^sub>\<L>\<rangle>\<^sub>\<F>\<^sub>\<L>)})} \<subseteq> P \<and> fl \<in> x)"  
         proof -
           have
            "{flt2cttobs fl\<^sub>0|fl\<^sub>0. fl\<^sub>0 \<le>\<^sub>\<F>\<^sub>\<L> (fl @\<^sub>\<F>\<^sub>\<L> \<langle>[{x. x \<notin> r2} - {Tick}]\<^sub>\<F>\<^sub>\<L>\<rangle>\<^sub>\<F>\<^sub>\<L>)} \<subseteq> P"
            apply auto
            using strong_less_eq_fltrace_imp_flt2cttobs_ctt
            by (metis (no_types, lifting) CT1c_def CT1c_healthy Ref \<open>ys @ [[e1]\<^sub>E] @ [[r2]\<^sub>R] = flt2cttobs (fl @\<^sub>\<F>\<^sub>\<L> \<langle>[{x. x \<notin> r2} - {Tick}]\<^sub>\<F>\<^sub>\<L>\<rangle>\<^sub>\<F>\<^sub>\<L>) \<and> flt2goodTock fl \<and> (\<exists>x. FLTick0 Tick x \<and> FL1 (x \<union> {fl\<^sub>0. fl\<^sub>0 \<le>\<^sub>\<F>\<^sub>\<L> fl @\<^sub>\<F>\<^sub>\<L> \<langle>[{x. x \<notin> r2} - {Tick}]\<^sub>\<F>\<^sub>\<L>\<rangle>\<^sub>\<F>\<^sub>\<L>}) \<and> {flt2cttobs fl\<^sub>0 |fl\<^sub>0. fl\<^sub>0 \<in> x} \<subseteq> P \<and> fl \<in> x)\<close> e1 fl fl_e3 yys.prems(2))
          then show ?thesis 
            by (smt Un_iff \<open>ys @ [[e1]\<^sub>E] @ [[r2]\<^sub>R] = flt2cttobs (fl @\<^sub>\<F>\<^sub>\<L> \<langle>[{x. x \<notin> r2} - {Tick}]\<^sub>\<F>\<^sub>\<L>\<rangle>\<^sub>\<F>\<^sub>\<L>) \<and> flt2goodTock fl \<and> (\<exists>x. FLTick0 Tick (x \<union> {fl\<^sub>0. fl\<^sub>0 \<le>\<^sub>\<F>\<^sub>\<L> fl @\<^sub>\<F>\<^sub>\<L> \<langle>[{x. x \<notin> r2} - {Tick}]\<^sub>\<F>\<^sub>\<L>\<rangle>\<^sub>\<F>\<^sub>\<L>}) \<and> FL1 (x \<union> {fl\<^sub>0. fl\<^sub>0 \<le>\<^sub>\<F>\<^sub>\<L> fl @\<^sub>\<F>\<^sub>\<L> \<langle>[{x. x \<notin> r2} - {Tick}]\<^sub>\<F>\<^sub>\<L>\<rangle>\<^sub>\<F>\<^sub>\<L>}) \<and> {flt2cttobs fl\<^sub>0 |fl\<^sub>0. fl\<^sub>0 \<in> x} \<subseteq> P \<and> fl \<in> x)\<close> mem_Collect_eq subset_eq)
        qed
        then have "
                  ys @ [[e1]\<^sub>E] @ [[r2]\<^sub>R] = flt2cttobs(fl @\<^sub>\<F>\<^sub>\<L> \<langle>[{x. x \<notin> r2} - {Tick}]\<^sub>\<F>\<^sub>\<L>\<rangle>\<^sub>\<F>\<^sub>\<L>)
                  \<and> flt2goodTock fl 
                  \<and> (\<exists>x. FLTick0 Tick (x \<union> {fl\<^sub>0. fl\<^sub>0 \<le>\<^sub>\<F>\<^sub>\<L> (fl @\<^sub>\<F>\<^sub>\<L> \<langle>[{x. x \<notin> r2} - {Tick}]\<^sub>\<F>\<^sub>\<L>\<rangle>\<^sub>\<F>\<^sub>\<L>)})
                      \<and> FL1 (x \<union> {fl\<^sub>0. fl\<^sub>0 \<le>\<^sub>\<F>\<^sub>\<L> (fl @\<^sub>\<F>\<^sub>\<L> \<langle>[{x. x \<notin> r2} - {Tick}]\<^sub>\<F>\<^sub>\<L>\<rangle>\<^sub>\<F>\<^sub>\<L>)}) 
                      \<and> {flt2cttobs fl\<^sub>0 |fl\<^sub>0. fl\<^sub>0 \<in> (x \<union> {fl\<^sub>0. fl\<^sub>0 \<le>\<^sub>\<F>\<^sub>\<L> (fl @\<^sub>\<F>\<^sub>\<L> \<langle>[{x. x \<notin> r2} - {Tick}]\<^sub>\<F>\<^sub>\<L>\<rangle>\<^sub>\<F>\<^sub>\<L>)})} \<subseteq> P 
                      \<and> fl \<in> x
                      \<and> (fl @\<^sub>\<F>\<^sub>\<L> \<langle>[{x. x \<notin> r2} - {Tick}]\<^sub>\<F>\<^sub>\<L>\<rangle>\<^sub>\<F>\<^sub>\<L>) \<in> (x \<union> {fl\<^sub>0. fl\<^sub>0 \<le>\<^sub>\<F>\<^sub>\<L> (fl @\<^sub>\<F>\<^sub>\<L> \<langle>[{x. x \<notin> r2} - {Tick}]\<^sub>\<F>\<^sub>\<L>\<rangle>\<^sub>\<F>\<^sub>\<L>)}))"  
         by (simp add: strong_less_eq_fltrace_refl)  
        then have "
                  ys @ [[e1]\<^sub>E] @ [[r2]\<^sub>R] = flt2cttobs(fl @\<^sub>\<F>\<^sub>\<L> \<langle>[{x. x \<notin> r2} - {Tick}]\<^sub>\<F>\<^sub>\<L>\<rangle>\<^sub>\<F>\<^sub>\<L>)
                  \<and> flt2goodTock fl 
                  \<and> (\<exists>z. FLTick0 Tick z \<and> FL1 z 
                      \<and> {flt2cttobs fl\<^sub>0 |fl\<^sub>0. fl\<^sub>0 \<in> z} \<subseteq> P 
                      \<and> fl @\<^sub>\<F>\<^sub>\<L> \<langle>[{x. x \<notin> r2} - {Tick}]\<^sub>\<F>\<^sub>\<L>\<rangle>\<^sub>\<F>\<^sub>\<L> \<in> z)"
          by blast
        then have "
                  ys @ [[e1]\<^sub>E] @ [[r2]\<^sub>R] = flt2cttobs(fl @\<^sub>\<F>\<^sub>\<L> \<langle>[{x. x \<notin> r2} - {Tick}]\<^sub>\<F>\<^sub>\<L>\<rangle>\<^sub>\<F>\<^sub>\<L>)
                  \<and> flt2goodTock fl
                  \<and> flt2goodTock (fl @\<^sub>\<F>\<^sub>\<L> \<langle>[{x. x \<notin> r2} - {Tick}]\<^sub>\<F>\<^sub>\<L>\<rangle>\<^sub>\<F>\<^sub>\<L>) 
                  \<and> (\<exists>z. FLTick0 Tick z \<and> FL1 z 
                      \<and> {flt2cttobs fl\<^sub>0 |fl\<^sub>0. fl\<^sub>0 \<in> z} \<subseteq> P 
                      \<and> fl @\<^sub>\<F>\<^sub>\<L> \<langle>[{x. x \<notin> r2} - {Tick}]\<^sub>\<F>\<^sub>\<L>\<rangle>\<^sub>\<F>\<^sub>\<L> \<in> z)"
          using flt2goodTock_extend_consFL_acceptance by blast
        then have "
                  \<exists>fl. ys @ [[e1]\<^sub>E] @ [[r2]\<^sub>R] = flt2cttobs(fl)
                  \<and> flt2goodTock fl
                  \<and> (\<exists>z. FLTick0 Tick z \<and> FL1 z 
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
      and CTTick_healthy: "CTTick P"
      and CT4_healthy: "CT4 P"
  shows "P \<subseteq> fl2ctt(ctt2fl(P))"
  unfolding ctt2fl_def fl2ctt_def apply auto
  using assms CTwf_1c_3_imp_flt2cttobs_FL1 by blast

lemma fl2ctt_ctt2fl_bij:
  assumes 
          CTwf_healthy: "CTwf P" 
      and CT1c_healthy: "CT1c P"
      and CT3_healthy:  "CT3 P"
      and CTTick_healthy: "CTTick P"
      and CT4_healthy: "CT4 P"
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

lemma flt2cttobs_flt2goodTock_less_eq_exists:
  assumes "flt2cttobs fl \<noteq> []"
  shows "\<exists>fla. flt2cttobs fl = flt2cttobs fla \<and> fla \<le> fl \<and> flt2goodTock fla"
  using assms
proof (induct fl rule:flt2goodTock.induct)
  case (1 A)
  then show ?case 
    apply auto
    by (rule exI[where x="\<langle>A\<rangle>\<^sub>\<F>\<^sub>\<L>"], auto)
next
  case (2 A fl)
  then show ?case
  proof (cases "flt2cttobs fl \<noteq> []")
    case flt2cttobs_not_Nil:True
    then show ?thesis
      proof (cases "acceptance(A) \<noteq> \<bullet>")
      case True
        then have "\<exists>flaa. flt2cttobs fl = flt2cttobs flaa \<and> flaa \<le> fl \<and> flt2goodTock flaa"
          using flt2cttobs_not_Nil 2 by auto
        then show ?thesis using 2 True
          by (metis flt2cttobs.simps(2) flt2goodTock.simps(2) less_eq_fltrace.simps(3) order_refl)
      next
        case False
        then show ?thesis 
          using flt2cttobs_not_Nil 2 apply auto
          by (metis flt2cttobs.simps(2) flt2goodTock.simps(2) less_eq_fltrace.simps(3) order_refl)
      qed
  next
    case fl2cttobs_is_Nil:False
    then show ?thesis
      proof (cases "acceptance(A) \<noteq> \<bullet>")
        case True
        then show ?thesis using fl2cttobs_is_Nil 2 apply auto
          apply (rule exI[where x="\<langle>A,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>"], auto)
           apply (metis dual_order.refl dual_order.trans prefixFL_induct2)
          apply (rule exI[where x="\<langle>A,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>"], auto)
          by (metis dual_order.refl dual_order.trans prefixFL_induct2)
      next
      case False
      then show ?thesis using fl2cttobs_is_Nil 2 apply auto
        apply (rule exI[where x="\<langle>A,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>"], auto)
        by (metis dual_order.refl dual_order.trans prefixFL_induct2)
      qed
    qed
  qed

lemma flt2cttobs_FL1_exists_flt2goodTock:
  assumes "flt2cttobs fl \<noteq> []" "fl \<in> P" "FL1 P"
  shows "\<exists>fla. flt2cttobs fl = flt2cttobs fla \<and> fla \<in> P \<and> flt2goodTock fla"
  using assms
  by (meson FL1_def flt2cttobs_flt2goodTock_less_eq_exists)

lemma fl2ctt_FL0_FL1_flt2goodTock_non_bullet:
  assumes "FL0 P" "FL1 P"
  shows "fl2ctt P = {flt2cttobs fl|fl. fl \<in> P \<and> flt2goodTock fl \<and> fl \<noteq> \<langle>\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>} \<union> {[]}"
  using assms unfolding fl2ctt_def apply auto
  using flt2cttobs_FL1_exists_flt2goodTock
  apply (metis Finite_Linear_Model.butlast.simps(1) Finite_Linear_Model.last.simps(1) acceptance.distinct(1) append_self_conv2 flt2cttobs_last_fl_not_bullet_dist_list_cons flt2goodTock.simps(1))
  by (rule exI[where x="\<langle>\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>"], auto)

lemma fl2ctt_FL0_FL1_flt2goodTock:
  assumes "FL0 P" "FL1 P"
  shows "fl2ctt P = {flt2cttobs fl|fl. fl \<in> P \<and> flt2goodTock fl} \<union> {[]}"
  using assms unfolding fl2ctt_def apply auto
  using flt2cttobs_FL1_exists_flt2goodTock
  apply (metis)
  by (rule exI[where x="\<langle>\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>"], auto)

(* flt2goodAcceptance sufficient? *)

lemma tickWF_last_bullet_imp_Tick_notin:
  assumes "tickWF Tick (xs &\<^sub>\<F>\<^sub>\<L> \<langle>x\<rangle>\<^sub>\<F>\<^sub>\<L>)"
          "Finite_Linear_Model.last xs = \<bullet>"
  shows   "Tick \<notin>\<^sub>\<F>\<^sub>\<L> x"
  using assms apply(induct xs, auto)
  apply (case_tac x1a, auto, case_tac b, auto)
  by (case_tac b, auto)

lemma FLTick0_Tick_FL1_concat_ref_Tick_in:
  assumes "FLTick0 Tick P" "t @ [[X]\<^sub>R] = flt2cttobs fl" "fl \<in> P" "flt2goodTock fl"
  shows "Tick \<in> X"
  using assms proof (induct fl arbitrary:t X rule:fltrace_induct)
  case 1
  then show ?case by auto
next
  case (2 x xs)
  then show ?case
  proof (cases "last xs = \<bullet>")
    case True
    then have "t @ [[X]\<^sub>R] = flt2cttobs (xs) @ flt2cttobs(\<langle>x\<rangle>\<^sub>\<F>\<^sub>\<L>)"
      using 2
      by (metis Finite_Linear_Model.last.simps(1) acceptance.distinct(1) flt2cttobs_last_fl_not_bullet_dist_list_cons last_bullet_butlast_last last_bullet_then_last_cons last_flt2cttobs_eq_ref_imp_last snoc_eq_iff_butlast)
    then have X_x:"[[X]\<^sub>R] = flt2cttobs(\<langle>x\<rangle>\<^sub>\<F>\<^sub>\<L>)"
      by (metis "2.prems"(2) Nil_is_append_conv True acceptance.distinct(1) bullet_right_zero2 flt2cttobs.simps(1) last_flt2cttobs_eq_ref_imp_last last_snoc)
    then show ?thesis
    proof (cases x)
      case acnil
      then show ?thesis using 2 by auto
    next
      case (acset x2)
      have "tickWF Tick (xs &\<^sub>\<F>\<^sub>\<L> \<langle>x\<rangle>\<^sub>\<F>\<^sub>\<L>)"
        using 2
        by (meson FLTick0_def)
      then have "Tick \<notin> x2"
        using True tickWF_last_bullet_imp_Tick_notin
        using acset by fastforce
      then show ?thesis using X_x acset by auto
    qed
  next
    case False
    then have "t @ [[X]\<^sub>R] = flt2cttobs (xs)"
      using 2
      by (simp add: concat_FL_last_not_bullet_absorb)
    then have X_x:"[[X]\<^sub>R] = flt2cttobs(\<langle>last xs\<rangle>\<^sub>\<F>\<^sub>\<L>)"
      using "2.prems"(4) False concat_FL_last_not_bullet_absorb flt2cttobs_last_fl_not_bullet_dist_list_cons by fastforce
    then show ?thesis
      by (metis "2.hyps" "2.prems"(3) "2.prems"(4) False \<open>t @ [[X]\<^sub>R] = flt2cttobs xs\<close> assms(1) concat_FL_last_not_bullet_absorb)
  qed
next
  case (3 x xs)
  then show ?case
    proof (cases "last xs = \<bullet>")
      case True
      then show ?thesis
        by (metis "3.prems"(2) List.last.simps acceptance.distinct(1) append_is_Nil_conv last_appendR last_cons_bullet_iff last_flt2cttobs_eq_ref_imp_last list.simps(3))
    next
      case False
      then have "t @ [[X]\<^sub>R] = flt2cttobs (xs)"
      using 3
      by (simp add: concat_FL_last_not_bullet_absorb)
    then have X_x:"[[X]\<^sub>R] = flt2cttobs(\<langle>last xs\<rangle>\<^sub>\<F>\<^sub>\<L>)"
      using "3.prems"(4) False concat_FL_last_not_bullet_absorb flt2cttobs_last_fl_not_bullet_dist_list_cons by fastforce
    then show ?thesis
      by (metis "3.hyps" "3.prems"(4) "3.prems"(3) \<open>t @ [[X]\<^sub>R] = flt2cttobs xs\<close> assms(1) concat_FL_last_not_bullet_absorb flt2cttobs.simps(1) list.distinct(1))
    qed
  qed

lemma CTTick_dist_empty_trace: "CTTick(P \<union> {[]}) = CTTick(P)"
  unfolding CTTick_def by auto

lemma CTTickAll_dist_empty_trace: "CTTickAll(P \<union> {[]}) = CTTickAll(P)"
  unfolding CTTickAll_def by auto

lemma CTTick_fl2ctt:
  assumes "FL0 P" "FL1 P" "FLTick0 Tick P"
  shows "CTTick (fl2ctt P)"
proof -
  have "CTTick (fl2ctt P) = CTTick({flt2cttobs fl|fl. fl \<in> P \<and> flt2goodTock fl} \<union> {[]})"
    using assms
    by (simp add: fl2ctt_FL0_FL1_flt2goodTock)
  also have "... = CTTick({flt2cttobs fl|fl. fl \<in> P \<and> flt2goodTock fl})"
    using CTTick_dist_empty_trace by auto
  also have "... = True"
    unfolding CTTick_def fl2ctt_def apply auto
    using assms FLTick0_Tick_FL1_concat_ref_Tick_in by metis
  finally show ?thesis by auto
qed

lemma tickWF_imp_CTTickTrace_flt2cttobs:
  assumes "tickWF Tick fl"
  shows "CTTickTrace (flt2cttobs fl)"
  using assms apply (induct fl rule:flt2cttobs.induct, auto)
   apply (case_tac A, auto, case_tac a, auto, case_tac b, auto)
  by (case_tac A, auto, case_tac b, auto)

lemma CTTickAll_fl2ctt:
  assumes "FL0 P" "FL1 P" "FLTick0 Tick P"
  shows "CTTickAll (fl2ctt P)"
proof -
  have "CTTickAll (fl2ctt P) = CTTickAll({flt2cttobs fl|fl. fl \<in> P \<and> flt2goodTock fl} \<union> {[]})"
    using assms
    by (simp add: fl2ctt_FL0_FL1_flt2goodTock)
  also have "... = CTTickAll({flt2cttobs fl|fl. fl \<in> P \<and> flt2goodTock fl})"
    using CTTickAll_dist_empty_trace by auto
  also have "... = True"
    unfolding CTTickAll_def fl2ctt_def apply auto
    using assms tickWF_imp_CTTickTrace_flt2cttobs
    by (metis FLTick0_def)
  finally show ?thesis by auto
qed

lemma FL0_ctt2fl:
  assumes "CT0 P" "CT1c P"
  shows "FL0 (ctt2fl P)"
  using assms unfolding ctt2fl_def FL0_def apply auto
  apply (rule exI[where x="{\<langle>\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>}"], auto)
  unfolding FL1_def apply auto
  unfolding FLTick0_def apply auto
   apply (metis bullet_left_zero2 dual_order.antisym x_le_x_concat2)
  unfolding fl2ctt_def apply auto
  using CT0_CT1c_empty by blast

lemma FL1_imp_disj:
  assumes "FL1(P)" "FL1(Q)"
  shows "FL1(P \<union> Q)"
  unfolding FL1_def apply auto
  using FL1_def assms by blast+

lemma prefix_ctt2fl_FL1:
  assumes "t \<in> ctt2fl P"
          "s \<le> t"
    shows "s \<in> ctt2fl P"
  using assms unfolding ctt2fl_def apply auto
  using FL1_def by blast

lemma FL1_ctt2fl:
  "FL1 (ctt2fl P)"
  unfolding FL1_def apply safe
  using prefix_ctt2fl_FL1 by blast

(*
lemma
  assumes "tickWF Tick fltrace"
  shows "CTwf (fl2ctt xa)"
  using assms unfolding fl2ctt_def CTwf_def apply auto
  sledgehammer
*)

lemma FLTick0_Tick_ctt2fl:
  assumes "CTwf P"
  shows "FLTick0 Tick (ctt2fl P)"
  using assms unfolding ctt2fl_def FLTick0_def CTwf_def by auto

lemma tickWF_consFL_notin_prefix:
  assumes "tickWF Tick (\<beta> &\<^sub>\<F>\<^sub>\<L> \<langle>A\<rangle>\<^sub>\<F>\<^sub>\<L>)" "a \<in>\<^sub>\<F>\<^sub>\<L> A"
  shows "Tick \<notin> events(\<beta>)"
  using assms apply auto
  apply (cases A, auto)
  by (metis Finite_Linear_Model.last.simps(1) bullet_right_zero2 concat_FL_last_not_bullet_absorb last_bullet_butlast_last last_cons_acceptance_not_bullet not_in_events_not_in_butlast_twice tickWF_last_x_is_emptyset)

lemma FLTick0_Tick_consFL_acceptance_imp_consFL:
  assumes "FLTick0 Tick x" "\<beta> &\<^sub>\<F>\<^sub>\<L> \<langle>A\<rangle>\<^sub>\<F>\<^sub>\<L> \<in> x" "a \<in>\<^sub>\<F>\<^sub>\<L> A"
  shows "FLTick0 Tick (x \<union> {\<beta> &\<^sub>\<F>\<^sub>\<L> \<langle>(A,a)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>})"
  using assms unfolding FLTick0_def apply auto
  using tickWF_consFL_notin_prefix
  by (metis (no_types, lifting) Finite_Linear_Model.last.simps(1) amember.simps(1) concat_FL_last_not_bullet_absorb fl_cons_acceptance_consFL last_bullet_butlast_last last_bullet_then_last_cons tickWF_concatFL_imp)

lemma FLTick0_dist_union:
  "FLTick0 Tick (x \<union> y) = (FLTick0 Tick x \<and> FLTick0 Tick y)"
  unfolding FLTick0_def by auto

lemma FL_prefix_not_in_events:
  assumes "s \<le> t" "e \<notin> events t"
  shows "e \<notin> events s"
  using assms apply (induct s t rule:less_eq_fltrace.induct, auto)
  using less_eq_aevent_def by blast

lemma tickWF_acceptance_imp_tickWF_consFL:
  assumes "tickWF tick (\<beta> &\<^sub>\<F>\<^sub>\<L> \<langle>A\<rangle>\<^sub>\<F>\<^sub>\<L>)" "a \<in>\<^sub>\<F>\<^sub>\<L> A"
  shows "tickWF tick (\<beta> &\<^sub>\<F>\<^sub>\<L> \<langle>(A,a)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>)"
  using assms apply (induct tick \<beta> rule:tickWF.induct, auto)
   apply (case_tac A, auto)
   apply (case_tac Aa, auto)
  apply (case_tac A, auto)
  by (metis Finite_Linear_Model.last.simps(1) last_cons_acceptance_not_bullet)

lemma tickWF_imp_prefix:
  assumes "tickWF tick t" "s \<le> t"
  shows "tickWF tick s"
  using assms apply (induct s t rule:less_eq_fltrace.induct, auto)
  apply (metis amember.simps(1) less_eq_acceptance.elims(2))
      apply (metis amember.simps(1) less_eq_acceptance.elims(2))
  apply (metis amember.elims(2) event_in_acceptance less_eq_acceptance.simps(2) less_eq_aevent_def)
  apply (metis bullet_left_zero2 dual_order.antisym less_eq_aevent_def x_le_x_concat2)
    apply (metis amember.simps(1) less_eq_acceptance.elims(2) less_eq_aevent_def)
    by (simp add: less_eq_aevent_def)
  
lemma FLTick0_Tick_consFL_acceptance_imp_consFL':
  assumes "FLTick0 Tick x" "\<beta> &\<^sub>\<F>\<^sub>\<L> \<langle>A\<rangle>\<^sub>\<F>\<^sub>\<L> \<in> x" "a \<in>\<^sub>\<F>\<^sub>\<L> A"
  shows "FLTick0 Tick (x \<union> {s. s \<le> \<beta> &\<^sub>\<F>\<^sub>\<L> \<langle>(A,a)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>})"
proof -
  have a:"FLTick0 Tick (x \<union> {s. s \<le> \<beta> &\<^sub>\<F>\<^sub>\<L> \<langle>(A,a)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>})
        =
        FLTick0 Tick ({s. s \<le> \<beta> &\<^sub>\<F>\<^sub>\<L> \<langle>(A,a)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>})"
    using assms using FLTick0_dist_union by auto
  have "tickWF Tick (\<beta> &\<^sub>\<F>\<^sub>\<L> \<langle>A\<rangle>\<^sub>\<F>\<^sub>\<L>)"
    using assms(1,2)
    by (simp add: FLTick0_def)
  then have "tickWF Tick (\<beta> &\<^sub>\<F>\<^sub>\<L> \<langle>(A,a)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>)"
    by (simp add: assms(3) tickWF_acceptance_imp_tickWF_consFL)
  then have "\<forall>s. s \<le> \<beta> &\<^sub>\<F>\<^sub>\<L> \<langle>(A,a)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L> \<longrightarrow> tickWF Tick s"
    by (meson tickWF_imp_prefix)
  then have "FLTick0 Tick ({s. s \<le> \<beta> &\<^sub>\<F>\<^sub>\<L> \<langle>(A,a)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>})"
    by (simp add: FLTick0_def)
  then show ?thesis using a by auto
qed

definition CTM2a :: "'e cttobs list set \<Rightarrow> bool" where
  "CTM2a P = (\<forall> \<rho> X e. (\<rho> @ [[X]\<^sub>R] \<in> P \<and> e \<notin> X \<and> e \<noteq> Tock) \<longrightarrow> \<rho> @ [[e]\<^sub>E] \<in> P)"

definition CTM2b :: "'e cttobs list set \<Rightarrow> bool" where
  "CTM2b P = (\<forall> \<rho> X e. (\<rho> @ [[X]\<^sub>R] \<in> P \<and> e \<notin> X \<and> e = Tock) \<longrightarrow> \<rho> @ [[X]\<^sub>R,[e]\<^sub>E] \<in> P)"

lemma flt2cttobs_not_flt2goodTock_imp_flt2cttobs_eq_consFL_any:
  assumes "\<not> flt2goodTock xs"
  shows "flt2cttobs (xs &\<^sub>\<F>\<^sub>\<L> ys) = flt2cttobs (xs)"
  using assms by(induct xs, auto)

lemma prefixFL_same_length_imp:
  assumes "length xs = length ys" "last ys = \<bullet>" "last xs = \<bullet>" 
          "xs &\<^sub>\<F>\<^sub>\<L> x \<le> ys &\<^sub>\<F>\<^sub>\<L> y"
  shows "x \<le> y"
  using assms by (induct xs ys arbitrary:a b rule:less_eq_fltrace.induct, auto)

lemma prefixFL_same_length_imp_1:
  assumes "xs \<le> ys" "a \<le> b" "last ys = \<bullet>" "last xs = \<bullet>" "length xs = length ys"
  shows "xs &\<^sub>\<F>\<^sub>\<L> a \<le> ys &\<^sub>\<F>\<^sub>\<L> b"
  using assms by (induct xs ys arbitrary:a b rule:less_eq_fltrace.induct, auto)

lemma prefixFL_same_length_imp_2:
  assumes "length xs = length ys" "last ys = \<bullet>" "last xs = \<bullet>" 
          "xs &\<^sub>\<F>\<^sub>\<L> a \<le> ys &\<^sub>\<F>\<^sub>\<L> b"
        shows "xs \<le> ys"
  using assms by (induct xs ys arbitrary:a b rule:less_eq_fltrace.induct, auto)

lemma CT1c_prefix_concat_in:
  assumes "xs @ ys \<in> P" "CT1c P"
  shows "xs \<in> P"
proof -
  have "xs \<le>\<^sub>C xs @ ys"
    using ctt_prefix_concat by blast
  then have "xs \<in> P"
    using assms CT1c_def by blast
  then show ?thesis .
qed

lemma flt2cttobs_for_FL2_imp:
  assumes "flt2cttobs (\<beta> &\<^sub>\<F>\<^sub>\<L> \<langle>A\<rangle>\<^sub>\<F>\<^sub>\<L>) \<in> P" "a \<in>\<^sub>\<F>\<^sub>\<L> A" "CTM2a P" "CTM2b P" "CT1c P"
  shows "flt2cttobs (\<beta> &\<^sub>\<F>\<^sub>\<L> \<langle>(A,a)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>) \<in> P \<and> flt2cttobs (\<beta> &\<^sub>\<F>\<^sub>\<L> \<langle>(\<bullet>,a)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>) \<in> P"
  using assms (* NOTE: lhs conjunct does not require CT1c *)
proof (cases "last \<beta> = \<bullet>")
  case last_B_bullet:True
  then show ?thesis
  proof (cases "flt2goodTock \<beta>")
    case True
    then have "flt2cttobs (\<beta>) @ flt2cttobs (\<langle>A\<rangle>\<^sub>\<F>\<^sub>\<L>) \<in> P"
      by (metis (no_types, lifting) Finite_Linear_Model.last.simps(1) acceptance.simps(3) amember.elims(2) assms(1) assms(2) butlast_last_FL flt2cttobs_last_fl_not_bullet_dist_list_cons flt2goodTock_extend_consFL_acceptance last_B_bullet last_bullet_butlast_last last_bullet_then_last_cons)
    then obtain R where R:"R = {x. x \<notin>\<^sub>\<F>\<^sub>\<L> A}"
      using assms(2) by force
    then have "a \<notin> R"
      using assms(2) by blast
    then have "flt2cttobs (\<beta>) @ [[R]\<^sub>R] \<in> P"
      using R by (metis \<open>flt2cttobs \<beta> @ flt2cttobs \<langle>A\<rangle>\<^sub>\<F>\<^sub>\<L> \<in> P\<close> amember.simps(1) assms(2) flt2cttobs.simps(1))
    then show ?thesis
    proof (cases a)
      case (Event x1)
      then have "flt2cttobs (\<beta>) @ [[a]\<^sub>E] \<in> P"
        using assms
        using CTM2a_def \<open>a \<notin> R\<close> \<open>flt2cttobs \<beta> @ [[R]\<^sub>R] \<in> P\<close> by blast
      then show ?thesis
        using Event True assms(2) flt2cttobs_acceptance_cons_eq_list_cons last_B_bullet by fastforce
    next
      case Tock
      then have flt2cttobs_bullet:"flt2cttobs (\<beta> &\<^sub>\<F>\<^sub>\<L> \<langle>(\<bullet>,a)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>) = flt2cttobs (\<beta>)"
        by (simp add: True flt2cttobs_acceptance_cons_eq_list_cons last_B_bullet)
      then have flt2cttobs_R_tock:"flt2cttobs (\<beta>) @ [[R]\<^sub>R,[a]\<^sub>E] \<in> P"
        using Tock CTM2b_def \<open>a \<notin> R\<close> \<open>flt2cttobs \<beta> @ [[R]\<^sub>R] \<in> P\<close> assms(4) by blast
      then have c1:"flt2cttobs (\<beta> &\<^sub>\<F>\<^sub>\<L> \<langle>(A,a)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>) \<in> P"
        using R Tock True amember.simps(1) assms(2) flt2cttobs_acceptance_cons_eq_list_cons last_B_bullet by fastforce
      
      have c2:"flt2cttobs (\<beta> &\<^sub>\<F>\<^sub>\<L> \<langle>(\<bullet>,a)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>) \<in> P"
        using CT1c_prefix_concat_in assms flt2cttobs_bullet flt2cttobs_R_tock by auto
      then show ?thesis using c1 by auto
    next
      case Tick
      then have "flt2cttobs (\<beta>) @ [[a]\<^sub>E] \<in> P"
        using CTM2a_def \<open>a \<notin> R\<close> \<open>flt2cttobs \<beta> @ [[R]\<^sub>R] \<in> P\<close> assms(3) by blast
      then show ?thesis
        using Tick True assms(2) flt2cttobs_acceptance_cons_eq_list_cons last_B_bullet by fastforce
    qed  
  next
    case False
    then show ?thesis
      using assms(1) flt2cttobs_not_flt2goodTock_imp_flt2cttobs_eq_consFL_any by fastforce
  qed
next
  case False
  then show ?thesis
    using assms(1) concat_FL_last_not_bullet_absorb by fastforce
qed

lemma FL1_extends_strong_less_eq_fltrace_last_extended:
  assumes "FL1 x" "fl \<in> x" "e \<in>\<^sub>\<F>\<^sub>\<L> X" "last fl = X"
  shows "FL1 (x \<union> {fl\<^sub>0. fl\<^sub>0 \<le>\<^sub>\<F>\<^sub>\<L> (fl @\<^sub>\<F>\<^sub>\<L> \<langle>(X,e)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>)})"
  using assms unfolding FL1_def
  by (metis (no_types, lifting) Un_iff fl_cons_acceptance_consFL mem_Collect_eq strong_less_eq_fltrace_less_eq_common)

lemma FL1_extends_strong_less_eq_fltrace_last_bullet':
  assumes "FL1 x" "fl \<in> x" "e \<in>\<^sub>\<F>\<^sub>\<L> X" "last fl = \<bullet>"
  shows "FL1(x \<union> {fl\<^sub>0. fl\<^sub>0 \<le>\<^sub>\<F>\<^sub>\<L> (fl @\<^sub>\<F>\<^sub>\<L> \<langle>X\<rangle>\<^sub>\<F>\<^sub>\<L>) \<or> fl\<^sub>0 \<le>\<^sub>\<F>\<^sub>\<L> (fl @\<^sub>\<F>\<^sub>\<L> \<langle>(X,e)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>)})"
proof -
  have fl:"FL1(x \<union> {fl\<^sub>0. fl\<^sub>0 \<le>\<^sub>\<F>\<^sub>\<L> (fl @\<^sub>\<F>\<^sub>\<L> \<langle>X\<rangle>\<^sub>\<F>\<^sub>\<L>)})"
    by (simp add: FL1_extends_strong_less_eq_fltrace_acceptance assms(1) assms(2))
  then obtain z newfl where z:"z = (x \<union> {fl\<^sub>0. fl\<^sub>0 \<le>\<^sub>\<F>\<^sub>\<L> (fl @\<^sub>\<F>\<^sub>\<L> \<langle>X\<rangle>\<^sub>\<F>\<^sub>\<L>)}) \<and> newfl = (fl @\<^sub>\<F>\<^sub>\<L> \<langle>X\<rangle>\<^sub>\<F>\<^sub>\<L>) \<and> newfl \<in> z" 
    using strong_less_eq_fltrace_refl by auto
  then have "e \<in>\<^sub>\<F>\<^sub>\<L> last newfl"
    by (metis assms(3) assms(4) butlast_last_FL last_bullet_butlast_last last_rev3_acceptance last_rev3_is_bullet rev3_rev3_const2_last)
  then have "FL1(z \<union> {fl\<^sub>0. fl\<^sub>0 \<le>\<^sub>\<F>\<^sub>\<L> (newfl @\<^sub>\<F>\<^sub>\<L> \<langle>(X,e)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>)})"
    using z FL1_extends_strong_less_eq_fltrace_last_extended
    proof -
      have "Finite_Linear_Model.last newfl = X"
        by (metis assms(4) butlast_last_FL last_bullet_butlast_last last_dist_plus last_rev3_acceptance last_rev3_is_bullet z)
      then show ?thesis
        by (metis (full_types) \<open>\<And>x fl e X. \<lbrakk>FL1 x; fl \<in> x; e \<in>\<^sub>\<F>\<^sub>\<L> X; Finite_Linear_Model.last fl = X\<rbrakk> \<Longrightarrow> FL1 (x \<union> {fl\<^sub>0. fl\<^sub>0 \<le>\<^sub>\<F>\<^sub>\<L> fl @\<^sub>\<F>\<^sub>\<L> \<langle>(X,e)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>})\<close> \<open>e \<in>\<^sub>\<F>\<^sub>\<L> Finite_Linear_Model.last newfl\<close> fl z)
    qed
  then have "FL1((x \<union> {fl\<^sub>0. fl\<^sub>0 \<le>\<^sub>\<F>\<^sub>\<L> (fl @\<^sub>\<F>\<^sub>\<L> \<langle>X\<rangle>\<^sub>\<F>\<^sub>\<L>)}) \<union> {fl\<^sub>0. fl\<^sub>0 \<le>\<^sub>\<F>\<^sub>\<L> (newfl @\<^sub>\<F>\<^sub>\<L> \<langle>(X,e)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>)})"
    using z by auto
  then have "FL1(x \<union> ({fl\<^sub>0. fl\<^sub>0 \<le>\<^sub>\<F>\<^sub>\<L> (fl @\<^sub>\<F>\<^sub>\<L> \<langle>X\<rangle>\<^sub>\<F>\<^sub>\<L>)} \<union> {fl\<^sub>0. fl\<^sub>0 \<le>\<^sub>\<F>\<^sub>\<L> (newfl @\<^sub>\<F>\<^sub>\<L> \<langle>(X,e)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>)}))"
    by (simp add: Un_assoc)
  then have "FL1(x \<union> {fl\<^sub>0. fl\<^sub>0 \<le>\<^sub>\<F>\<^sub>\<L> (fl @\<^sub>\<F>\<^sub>\<L> \<langle>X\<rangle>\<^sub>\<F>\<^sub>\<L>) \<or> fl\<^sub>0 \<le>\<^sub>\<F>\<^sub>\<L> (newfl @\<^sub>\<F>\<^sub>\<L> \<langle>(X,e)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>)})"
    by (simp add: Collect_disj_eq)
  then have "FL1(x \<union> {fl\<^sub>0. fl\<^sub>0 \<le>\<^sub>\<F>\<^sub>\<L> (fl @\<^sub>\<F>\<^sub>\<L> \<langle>X\<rangle>\<^sub>\<F>\<^sub>\<L>) \<or> fl\<^sub>0 \<le>\<^sub>\<F>\<^sub>\<L> ((fl @\<^sub>\<F>\<^sub>\<L> \<langle>X\<rangle>\<^sub>\<F>\<^sub>\<L>) @\<^sub>\<F>\<^sub>\<L> \<langle>(X,e)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>)})"
    using z by auto
  then have "FL1(x \<union> {fl\<^sub>0. fl\<^sub>0 \<le>\<^sub>\<F>\<^sub>\<L> (fl @\<^sub>\<F>\<^sub>\<L> \<langle>X\<rangle>\<^sub>\<F>\<^sub>\<L>) \<or> fl\<^sub>0 \<le>\<^sub>\<F>\<^sub>\<L> (fl @\<^sub>\<F>\<^sub>\<L> \<langle>(X,e)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>)})"
    by (simp add: fltrace_concat_assoc)
  then show ?thesis by auto
qed

lemma FL0_Tick_extends_strong_less_eq_fltrace_last_bullet':
  assumes "FLTick0 Tick x" "fl \<in> x" "last fl = \<bullet>" "Tick \<notin> events fl" "Tick \<notin>\<^sub>\<F>\<^sub>\<L> X" "e \<in>\<^sub>\<F>\<^sub>\<L> X"
  shows "FLTick0 Tick (x \<union> {fl\<^sub>0. fl\<^sub>0 \<le>\<^sub>\<F>\<^sub>\<L> (fl @\<^sub>\<F>\<^sub>\<L> \<langle>X\<rangle>\<^sub>\<F>\<^sub>\<L>) \<or> fl\<^sub>0 \<le>\<^sub>\<F>\<^sub>\<L> (fl @\<^sub>\<F>\<^sub>\<L> \<langle>(X,e)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>)})"
  using assms
  unfolding FLTick0_def apply auto
  using tickWF_concatFL_acceptance_imp tickWF_prefix_imp apply blast
  by (metis (mono_tags, lifting) assms(2) assms(3) assms(4) assms(5) assms(6) bullet_right_zero2 butlast_last_FL butlast_last_cons2_FL fl_cons_acceptance_consFL last_bullet_butlast_last last_bullet_then_last_cons last_rev3_acceptance last_rev3_cons2_is_last_cons tickWF_acceptance_imp_tickWF_consFL tickWF_concatFL_acceptance_imp tickWF_prefix_imp)

lemma flt2goodTock_extend_consFL_last_e':
  assumes "flt2goodTock fl" "e \<in>\<^sub>\<F>\<^sub>\<L> X"
  shows "flt2goodTock (fl @\<^sub>\<F>\<^sub>\<L> \<langle>(X,e)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>)"
  using assms by (induct fl rule:flt2goodTock.induct, auto)

lemma FL1_extends_strong_less_eq_consFL:
  assumes "FL1 x" "\<beta> &\<^sub>\<F>\<^sub>\<L> \<langle>A\<rangle>\<^sub>\<F>\<^sub>\<L> \<in> x" "a \<in>\<^sub>\<F>\<^sub>\<L> A"
  shows "FL1 (x \<union> {s. s \<le>\<^sub>\<F>\<^sub>\<L> \<beta> &\<^sub>\<F>\<^sub>\<L> \<langle>(A,a)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>})"
  using assms
proof(cases "last \<beta> = \<bullet>")
  case True
  then have "last (\<beta> &\<^sub>\<F>\<^sub>\<L> \<langle>A\<rangle>\<^sub>\<F>\<^sub>\<L>) = A"
    by simp
  then have "FL1 (x \<union> {fl\<^sub>0. fl\<^sub>0 \<le>\<^sub>\<F>\<^sub>\<L> ((\<beta> &\<^sub>\<F>\<^sub>\<L> \<langle>A\<rangle>\<^sub>\<F>\<^sub>\<L>) @\<^sub>\<F>\<^sub>\<L> \<langle>(A,a)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>)})"
    using assms 
    by (simp add: FL1_extends_strong_less_eq_fltrace_last_extended)
  then have "FL1 (x \<union> {fl\<^sub>0. fl\<^sub>0 \<le>\<^sub>\<F>\<^sub>\<L> (\<beta> &\<^sub>\<F>\<^sub>\<L> \<langle>(A,a)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>)})"
  proof -
    have "(\<beta> &\<^sub>\<F>\<^sub>\<L> \<langle>A\<rangle>\<^sub>\<F>\<^sub>\<L>) @\<^sub>\<F>\<^sub>\<L> \<langle>(A,a)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L> = \<beta> &\<^sub>\<F>\<^sub>\<L> \<langle>(A,a)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>"
      by (simp add: True last_bullet_concatmix)
    then show ?thesis
      using \<open>FL1 (x \<union> {fl\<^sub>0. fl\<^sub>0 \<le>\<^sub>\<F>\<^sub>\<L> (\<beta> &\<^sub>\<F>\<^sub>\<L> \<langle>A\<rangle>\<^sub>\<F>\<^sub>\<L>) @\<^sub>\<F>\<^sub>\<L> \<langle>(A,a)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>})\<close> by auto
  qed
  then show ?thesis
    by blast
next
  case False
  then show ?thesis
    by (metis FL1_extends_strong_less_eq_fltrace_acceptance assms(1) assms(2) butlast_last_FL concat_FL_last_not_bullet_absorb fltrace_concat.simps(1) fltrace_concat_assoc)
qed

lemma CT1c_CTM2a_CTM2b_strong_less_eq_fltrace:
  assumes "a \<in>\<^sub>\<F>\<^sub>\<L> A" "CT1c P" "CTM2a P" "CTM2b P"
          "FLTick0 Tick x"
          "FL1 x" "{flt2cttobs fl |fl. fl \<in> x} \<subseteq> P" "\<beta> &\<^sub>\<F>\<^sub>\<L> \<langle>A\<rangle>\<^sub>\<F>\<^sub>\<L> \<in> x" 
          "fl \<le>\<^sub>\<F>\<^sub>\<L> \<beta> &\<^sub>\<F>\<^sub>\<L> \<langle>(A,a)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>" 
        shows "flt2cttobs fl \<in> P"
  using assms proof(induct fl arbitrary:\<beta> A a x rule:fltrace_induct)
case 1
  then show ?case by (metis (mono_tags, lifting) CollectI FL0_FL1_bullet_in_so flt2cttobs.simps(1) in_mono)
next
  case (2 z zs)
  then have "flt2cttobs (\<beta> &\<^sub>\<F>\<^sub>\<L> \<langle>A\<rangle>\<^sub>\<F>\<^sub>\<L>) \<in> P"
    by blast
  then have flt2cttobs_B_Aa:
        "flt2cttobs (\<beta> &\<^sub>\<F>\<^sub>\<L> \<langle>(A,a)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>) \<in> P"
        "flt2cttobs (\<beta> &\<^sub>\<F>\<^sub>\<L> \<langle>(\<bullet>,a)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>) \<in> P"
    using flt2cttobs_for_FL2_imp "2.prems"(1) assms(2) assms(3) assms(4) by blast+
  then have "flt2cttobs (zs &\<^sub>\<F>\<^sub>\<L> \<langle>z\<rangle>\<^sub>\<F>\<^sub>\<L>) \<le>\<^sub>C flt2cttobs (\<beta> &\<^sub>\<F>\<^sub>\<L> \<langle>(A,a)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>)"
    using "2.prems"(9) strong_less_eq_fltrace_imp_flt2cttobs_ctt by blast
  then have "flt2cttobs (zs &\<^sub>\<F>\<^sub>\<L> \<langle>z\<rangle>\<^sub>\<F>\<^sub>\<L>) \<in> P"
    using assms flt2cttobs_B_Aa CT1c_def by blast
  then show ?case by auto
next
  case (3 z zs)
  then have "flt2cttobs (\<beta> &\<^sub>\<F>\<^sub>\<L> \<langle>A\<rangle>\<^sub>\<F>\<^sub>\<L>) \<in> P"
    by blast
  then have flt2cttobs_B_Aa:
        "flt2cttobs (\<beta> &\<^sub>\<F>\<^sub>\<L> \<langle>(A,a)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>) \<in> P"
        "flt2cttobs (\<beta> &\<^sub>\<F>\<^sub>\<L> \<langle>(\<bullet>,a)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>) \<in> P"
    using flt2cttobs_for_FL2_imp "3.prems"(1) assms(2) assms(3) assms(4) by blast+
  then have "flt2cttobs (zs &\<^sub>\<F>\<^sub>\<L> \<langle>z,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>) \<le>\<^sub>C flt2cttobs (\<beta> &\<^sub>\<F>\<^sub>\<L> \<langle>(A,a)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>)"
    using "3.prems"(9) strong_less_eq_fltrace_imp_flt2cttobs_ctt by blast
  then have "flt2cttobs (zs &\<^sub>\<F>\<^sub>\<L> \<langle>z,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>) \<in> P"
    using assms flt2cttobs_B_Aa CT1c_def by blast
  then show ?case .
qed
  
lemma FL2_ctt2fl:
  assumes "CTM2a P" "CTM2b P" "CT1c P"
  shows "FL2 (ctt2fl P)"
  using assms unfolding ctt2fl_def FL2_def fl2ctt_def apply auto
  apply (rule_tac x="x \<union> {s. s \<le>\<^sub>\<F>\<^sub>\<L> \<beta> &\<^sub>\<F>\<^sub>\<L> \<langle>(A,a)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>}" in exI, auto)
  apply (metis (mono_tags, lifting) FLTick0_def FLTick0_dist_union mem_Collect_eq tickWF_acceptance_imp_tickWF_consFL tickWF_prefix_imp)
  apply (simp add: FL1_extends_strong_less_eq_consFL)
  using CT1c_CTM2a_CTM2b_strong_less_eq_fltrace
   apply blast
  using strong_less_eq_fltrace_refl by blast

lemma flt2goodTock_consFL_imp:
  assumes "flt2goodTock xs" "e \<noteq> Tock" "e \<in>\<^sub>\<F>\<^sub>\<L> [x2]\<^sub>\<F>\<^sub>\<L>"
  shows "flt2goodTock (xs &\<^sub>\<F>\<^sub>\<L> \<langle>([x2]\<^sub>\<F>\<^sub>\<L>,e)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>)"
  using assms apply (induct xs, auto)
  by (case_tac x, auto)

lemma FL2_imp_CTM2a_part:
  assumes "FL2 P" "e \<notin> X" "e \<noteq> Tock" "\<rho> @ [[X]\<^sub>R] = flt2cttobs fl" "fl \<in> P" "flt2goodTock fl"
  shows "\<exists>fl. \<rho> @ [[e]\<^sub>E] = flt2cttobs fl \<and> fl \<in> P \<and> flt2goodTock fl"
  using assms 
proof (induct fl arbitrary:\<rho> e X rule:fltrace_induct)
  case 1
  then show ?case by auto
next
  case (2 x xs)
  then show ?case 
  proof (cases "last xs = \<bullet>")
    case True
    then show ?thesis
    proof (cases x)
      case acnil
      then show ?thesis
        by (metis "2.prems"(4) Nil_is_append_conv True acceptance.distinct(1) bullet_right_zero2 last_flt2cttobs_eq_ref_imp_last last_snoc not_Cons_self2)
    next
      case (acset x2)
      then have flt2goodTock_xs: "flt2goodTock (xs)"
        using 2
        by (metis True flt2cttobs_not_flt2goodTock_imp_flt2cttobs_eq_consFL_any last_cons_acceptance_not_bullet last_flt2cttobs_eq_ref_imp_last snoc_eq_iff_butlast)
      then have "flt2cttobs (xs &\<^sub>\<F>\<^sub>\<L> \<langle>x\<rangle>\<^sub>\<F>\<^sub>\<L>) = flt2cttobs(xs) @ flt2cttobs(\<langle>x\<rangle>\<^sub>\<F>\<^sub>\<L>)"
        using 2 True
        by (metis Finite_Linear_Model.last.simps(1) append_Nil2 bullet_right_zero2 flt2cttobs.simps(1) flt2cttobs_last_fl_not_bullet_dist_list_cons last_bullet_butlast_last last_bullet_then_last_cons)
      then have "\<rho> @ [[X]\<^sub>R] = flt2cttobs(xs) @ flt2cttobs(\<langle>x\<rangle>\<^sub>\<F>\<^sub>\<L>)"
        using 2 by auto
      then have "\<rho> = flt2cttobs(xs)" "[[X]\<^sub>R] = flt2cttobs(\<langle>x\<rangle>\<^sub>\<F>\<^sub>\<L>)"
         apply (metis List.last.simps Nil_is_append_conv True acceptance.distinct(1) append_Nil2 butlast_snoc flt2cttobs.simps(1) last_appendR last_flt2cttobs_eq_ref_imp_last)
        by (metis "2.prems"(4) Nil_is_append_conv True \<open>\<rho> @ [[X]\<^sub>R] = flt2cttobs xs @ flt2cttobs \<langle>x\<rangle>\<^sub>\<F>\<^sub>\<L>\<close> acceptance.distinct(1) bullet_right_zero2 flt2cttobs.simps(1) last_flt2cttobs_eq_ref_imp_last last_snoc)

      have \<rho>_e:"\<rho> @ [[e]\<^sub>E] = flt2cttobs (xs &\<^sub>\<F>\<^sub>\<L> \<langle>([x2]\<^sub>\<F>\<^sub>\<L>,e)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>)"
      proof -
        have "flt2cttobs (xs &\<^sub>\<F>\<^sub>\<L> \<langle>([x2]\<^sub>\<F>\<^sub>\<L>,e)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>) = flt2cttobs(xs) @ flt2cttobs(\<langle>([x2]\<^sub>\<F>\<^sub>\<L>,e)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>)"
          using assms
          by (metis "2.prems"(4) True \<open>\<rho> = flt2cttobs xs\<close> \<open>flt2cttobs (xs &\<^sub>\<F>\<^sub>\<L> \<langle>x\<rangle>\<^sub>\<F>\<^sub>\<L>) = flt2cttobs xs @ flt2cttobs \<langle>x\<rangle>\<^sub>\<F>\<^sub>\<L>\<close> acset append_self_conv flt2cttobs_acceptance_cons_eq_list_cons flt2cttobs_not_flt2goodTock_imp_flt2cttobs_eq_consFL_any list.simps(3))
        also have "... = flt2cttobs(xs) @ [[e]\<^sub>E]"
          using "2.prems"(2) "2.prems"(3) \<open>[[X]\<^sub>R] = flt2cttobs \<langle>x\<rangle>\<^sub>\<F>\<^sub>\<L>\<close> acset by auto
        then show ?thesis
          by (simp add: \<open>\<rho> = flt2cttobs xs\<close> calculation)
      qed

      have "xs &\<^sub>\<F>\<^sub>\<L> \<langle>([x2]\<^sub>\<F>\<^sub>\<L>,e)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L> \<in> P"
        by (metis "2.prems"(2) "2.prems"(5) CollectI FL2_def List.last.simps \<open>[[X]\<^sub>R] = flt2cttobs \<langle>x\<rangle>\<^sub>\<F>\<^sub>\<L>\<close> acset assms(1) cttobs.inject(2) flt2cttobs.simps(1) list.simps(3))
      then have "\<rho> @ [[e]\<^sub>E] = flt2cttobs (xs &\<^sub>\<F>\<^sub>\<L> \<langle>([x2]\<^sub>\<F>\<^sub>\<L>,e)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>) \<and> xs &\<^sub>\<F>\<^sub>\<L> \<langle>([x2]\<^sub>\<F>\<^sub>\<L>,e)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L> \<in> P"
        using \<rho>_e
        by blast
      then have "\<rho> @ [[e]\<^sub>E] = flt2cttobs (xs &\<^sub>\<F>\<^sub>\<L> \<langle>([x2]\<^sub>\<F>\<^sub>\<L>,e)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>) \<and> xs &\<^sub>\<F>\<^sub>\<L> \<langle>([x2]\<^sub>\<F>\<^sub>\<L>,e)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L> \<in> P 
                              \<and> flt2goodTock (xs &\<^sub>\<F>\<^sub>\<L> \<langle>([x2]\<^sub>\<F>\<^sub>\<L>,e)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>)"
        using flt2goodTock_xs 2 flt2goodTock_consFL_imp
        by (metis CollectI \<open>[[X]\<^sub>R] = flt2cttobs \<langle>x\<rangle>\<^sub>\<F>\<^sub>\<L>\<close> acset cttobs.inject(2) flt2cttobs.simps(1) last_snoc not_Cons_self2)
      then show ?thesis by blast
    qed
  next
    case False
    then show ?thesis
      by (metis "2.hyps" "2.prems"(2) "2.prems"(3) "2.prems"(4) "2.prems"(5) "2.prems"(6) assms(1) concat_FL_last_not_bullet_absorb)
  qed
next
  case (3 x xs)
  then show ?case
    proof (cases "last xs = \<bullet>")
      case True
      then show ?thesis
        by (metis "3.prems"(4) acceptance.distinct(1) last_cons_bullet_iff last_flt2cttobs_eq_ref_imp_last snoc_eq_iff_butlast)
    next
      case False
      then have flt2goodTock_xs:"flt2goodTock (xs)"
        using "3.prems"(6) concat_FL_last_not_bullet_absorb by fastforce
      have "[[X]\<^sub>R] = flt2cttobs(\<langle>last xs\<rangle>\<^sub>\<F>\<^sub>\<L>)"
        using False "3.prems"(4) "3.prems"(6) concat_FL_last_not_bullet_absorb flt2cttobs_last_fl_not_bullet_dist_list_cons by fastforce
      have "xs \<in> P"
        using 3 False
        by (metis concat_FL_last_not_bullet_absorb)
      then have "butlast xs &\<^sub>\<F>\<^sub>\<L> \<langle>last xs\<rangle>\<^sub>\<F>\<^sub>\<L> \<in> P"
        by (simp add: butlast_last_cons2_FL)
      then have xs_e:"butlast xs &\<^sub>\<F>\<^sub>\<L> \<langle>(last xs,e)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L> \<in> P"
        by (metis "3.prems"(2) CollectI FL2_def False List.last.simps \<open>[[X]\<^sub>R] = flt2cttobs \<langle>Finite_Linear_Model.last xs\<rangle>\<^sub>\<F>\<^sub>\<L>\<close> assms(1) cttobs.inject(2) flt2cttobs.simps(1))
      then have "\<rho> @ [[e]\<^sub>E] = flt2cttobs(butlast xs &\<^sub>\<F>\<^sub>\<L> \<langle>(last xs,e)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>)"
        by (metis (no_types, lifting) "3.prems"(2) "3.prems"(3) "3.prems"(4) "3.prems"(6) CollectI False acceptance_event butlast_snoc concat_FL_last_not_bullet_absorb cttobs.inject(2) flt2cttobs.simps(1) flt2cttobs.simps(2) flt2cttobs_butlast_cons_eq_list_cons flt2cttobs_last_fl_not_bullet_dist_list_cons last_snoc)
      then have "\<rho> @ [[e]\<^sub>E] = flt2cttobs(butlast xs &\<^sub>\<F>\<^sub>\<L> \<langle>(last xs,e)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>) \<and> butlast xs &\<^sub>\<F>\<^sub>\<L> \<langle>(last xs,e)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L> \<in> P"
        using xs_e by auto
      then have "\<rho> @ [[e]\<^sub>E] = flt2cttobs(butlast xs &\<^sub>\<F>\<^sub>\<L> \<langle>(last xs,e)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>) 
                              \<and> butlast xs &\<^sub>\<F>\<^sub>\<L> \<langle>(last xs,e)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L> \<in> P
                              \<and> flt2goodTock (butlast xs &\<^sub>\<F>\<^sub>\<L> \<langle>(last xs,e)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>)"
        using flt2goodTock_xs
        by (metis (no_types, lifting) "3.prems"(2) "3.prems"(3) "3.prems"(4) CollectI False Finite_Linear_Model.last.simps(1) List.last.simps Nil_is_append_conv \<open>[[X]\<^sub>R] = flt2cttobs \<langle>Finite_Linear_Model.last xs\<rangle>\<^sub>\<F>\<^sub>\<L>\<close> \<open>\<rho> @ [[e]\<^sub>E] = flt2cttobs (Finite_Linear_Model.butlast xs &\<^sub>\<F>\<^sub>\<L> \<langle>(Finite_Linear_Model.last xs,e)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>)\<close> append_self_conv butlast_last_cons2_FL concat_FL_last_not_bullet_absorb cttobs.inject(2) flt2cttobs.simps(1) flt2cttobs_last_fl_not_bullet_dist_list_cons flt2cttobs_not_flt2goodTock_imp_flt2cttobs_eq_consFL_any flt2goodTock_consFL_imp last_flt2cttobs_eq_ref_imp_last last_snoc list.inject mem_Collect_eq not_Cons_self2 xs_e)
      then show ?thesis by blast
    qed
qed

lemma FL2_imp_CTM2b_part:
  assumes "FL2 P" "Tock \<notin> X" "\<rho> @ [[X]\<^sub>R] = flt2cttobs fl" "fl \<in> P" "flt2goodTock fl"
  shows "\<exists>fl. \<rho> @ [[X]\<^sub>R, [Tock]\<^sub>E] = flt2cttobs fl \<and> fl \<in> P \<and> flt2goodTock fl"
  using assms 
proof (induct fl arbitrary:\<rho> X rule:fltrace_induct)
  case 1
  then show ?case by auto
next
  case (2 x xs)
  then show ?case 
  proof (cases "last xs = \<bullet>")
    case True
    then show ?thesis
    proof (cases x)
      case acnil
      then show ?thesis
        by (metis "2.prems"(3) True acceptance.distinct(1) bullet_right_zero2 last_flt2cttobs_eq_ref_imp_last snoc_eq_iff_butlast)
    next
      case (acset x2)
      then have flt2goodTock_xs: "flt2goodTock (xs)"
        using 2
        by (metis True flt2cttobs_not_flt2goodTock_imp_flt2cttobs_eq_consFL_any last_cons_acceptance_not_bullet last_flt2cttobs_eq_ref_imp_last snoc_eq_iff_butlast)
      then have "flt2cttobs (xs &\<^sub>\<F>\<^sub>\<L> \<langle>x\<rangle>\<^sub>\<F>\<^sub>\<L>) = flt2cttobs(xs) @ flt2cttobs(\<langle>x\<rangle>\<^sub>\<F>\<^sub>\<L>)"
        using 2 True
        by (metis Finite_Linear_Model.last.simps(1) append_Nil2 bullet_right_zero2 flt2cttobs.simps(1) flt2cttobs_last_fl_not_bullet_dist_list_cons last_bullet_butlast_last last_bullet_then_last_cons)
      then have "\<rho> @ [[X]\<^sub>R] = flt2cttobs(xs) @ flt2cttobs(\<langle>x\<rangle>\<^sub>\<F>\<^sub>\<L>)"
        using 2 by auto
      then have "\<rho> = flt2cttobs(xs)" "[[X]\<^sub>R] = flt2cttobs(\<langle>x\<rangle>\<^sub>\<F>\<^sub>\<L>)"
         apply (metis List.last.simps Nil_is_append_conv True acceptance.distinct(1) append_Nil2 butlast_snoc flt2cttobs.simps(1) last_appendR last_flt2cttobs_eq_ref_imp_last)
        using \<open>\<rho> @ [[X]\<^sub>R] = flt2cttobs xs @ flt2cttobs \<langle>x\<rangle>\<^sub>\<F>\<^sub>\<L>\<close> acset by auto
 
      have \<rho>_e:"\<rho> @ [[{x. x \<notin> x2}]\<^sub>R,[Tock]\<^sub>E] = flt2cttobs (xs &\<^sub>\<F>\<^sub>\<L> \<langle>([x2]\<^sub>\<F>\<^sub>\<L>,Tock)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>)"
      proof -
        have "flt2cttobs (xs &\<^sub>\<F>\<^sub>\<L> \<langle>([x2]\<^sub>\<F>\<^sub>\<L>,Tock)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>) = flt2cttobs(xs) @ flt2cttobs(\<langle>([x2]\<^sub>\<F>\<^sub>\<L>,Tock)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>)"
          using assms True flt2cttobs_acceptance_cons_eq_list_cons flt2goodTock_xs by blast
        also have "... = flt2cttobs(xs) @ [[{x. x \<notin> x2}]\<^sub>R,[Tock]\<^sub>E]"
          using "2.prems"(2) "2.prems"(3) \<open>[[X]\<^sub>R] = flt2cttobs \<langle>x\<rangle>\<^sub>\<F>\<^sub>\<L>\<close> acset by auto
        then show ?thesis
          by (simp add: \<open>\<rho> = flt2cttobs xs\<close> calculation)
      qed

      have "xs &\<^sub>\<F>\<^sub>\<L> \<langle>([x2]\<^sub>\<F>\<^sub>\<L>,Tock)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L> \<in> P"
        by (metis "2.prems"(2) "2.prems"(4) CollectI FL2_def \<open>[[X]\<^sub>R] = flt2cttobs \<langle>x\<rangle>\<^sub>\<F>\<^sub>\<L>\<close> acceptance.simps(3) acset assms(1) cttobs.inject(2) flt2cttobs.simps(1) list.inject)
      then have "\<rho> @ [[{x. x \<notin> x2}]\<^sub>R,[Tock]\<^sub>E] = flt2cttobs (xs &\<^sub>\<F>\<^sub>\<L> \<langle>([x2]\<^sub>\<F>\<^sub>\<L>,Tock)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>) \<and> xs &\<^sub>\<F>\<^sub>\<L> \<langle>([x2]\<^sub>\<F>\<^sub>\<L>,Tock)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L> \<in> P"
        using \<rho>_e
        by blast
      then have "\<rho> @ [[{x. x \<notin> x2}]\<^sub>R,[Tock]\<^sub>E] = flt2cttobs (xs &\<^sub>\<F>\<^sub>\<L> \<langle>([x2]\<^sub>\<F>\<^sub>\<L>,Tock)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>) \<and> xs &\<^sub>\<F>\<^sub>\<L> \<langle>([x2]\<^sub>\<F>\<^sub>\<L>,Tock)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L> \<in> P 
                              \<and> flt2goodTock (xs &\<^sub>\<F>\<^sub>\<L> \<langle>([x2]\<^sub>\<F>\<^sub>\<L>,Tock)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>)"
        using flt2goodTock_xs 2 flt2goodTock_consFL_imp
        by (metis True \<open>[[X]\<^sub>R] = flt2cttobs \<langle>x\<rangle>\<^sub>\<F>\<^sub>\<L>\<close> acceptance.distinct(1) acset cttobs.inject(2) flt2cttobs.simps(1) flt2goodTock_extend_consFL_last_e' fltrace_concat.simps(3) last_bullet_concatmix list.inject mem_Collect_eq)
      then show ?thesis
        by (metis (no_types, lifting) "2.prems"(2) Cons_eq_append_conv Finite_Linear_Model.butlast.simps(1) Finite_Linear_Model.last.simps(1) True \<open>[[X]\<^sub>R] = flt2cttobs \<langle>x\<rangle>\<^sub>\<F>\<^sub>\<L>\<close> \<open>\<rho> = flt2cttobs xs\<close> acceptance.distinct(1) acset cttobs.inject(2) fl_cons_acceptance_consFL flt2cttobs.simps(1) flt2cttobs_acceptance_cons_eq_list_cons flt2cttobs_last_tock flt2goodTock.simps(1) flt2goodTock_xs fltrace_concat2.simps(3) list.inject mem_Collect_eq)
    qed
  next
    case False
    then show ?thesis
      by (metis "2.hyps" "2.prems"(2) "2.prems"(3) "2.prems"(4) "2.prems"(5) assms(1) concat_FL_last_not_bullet_absorb)
  qed
next
  case (3 x xs)
  then show ?case
    proof (cases "last xs = \<bullet>")
      case True
      then show ?thesis
        by (metis "3.prems"(3) acceptance.distinct(1) last_cons_bullet_iff last_flt2cttobs_eq_ref_imp_last snoc_eq_iff_butlast)
   next
      case False
      then have flt2goodTock_xs:"flt2goodTock (xs)"
        using "3.prems"(5) concat_FL_last_not_bullet_absorb by force
      have "[[X]\<^sub>R] = flt2cttobs(\<langle>last xs\<rangle>\<^sub>\<F>\<^sub>\<L>)"
        using "3.prems"(3) False concat_FL_last_not_bullet_absorb flt2cttobs_last_fl_not_bullet_dist_list_cons flt2goodTock_xs by fastforce
      have "xs \<in> P"
        using 3 False
        by (metis concat_FL_last_not_bullet_absorb)
      then have "butlast xs &\<^sub>\<F>\<^sub>\<L> \<langle>last xs\<rangle>\<^sub>\<F>\<^sub>\<L> \<in> P"
        by (simp add: butlast_last_cons2_FL)
      then have xs_e:"butlast xs &\<^sub>\<F>\<^sub>\<L> \<langle>(last xs,Tock)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L> \<in> P"
        by (metis "3.prems"(2) CollectI FL2_def False List.last.simps \<open>[[X]\<^sub>R] = flt2cttobs \<langle>Finite_Linear_Model.last xs\<rangle>\<^sub>\<F>\<^sub>\<L>\<close> assms(1) cttobs.inject(2) flt2cttobs.simps(1))
      then have "\<rho> @ [[X]\<^sub>R,[Tock]\<^sub>E] = flt2cttobs(butlast xs &\<^sub>\<F>\<^sub>\<L> \<langle>(last xs,Tock)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>)"
      proof -
        have f1: "flt2cttobs xs = \<rho> @ [[X]\<^sub>R]"
          by (simp add: "3.prems"(3) False concat_FL_last_not_bullet_absorb)
        have f2: "List.butlast [[X]\<^sub>R, [Tock]\<^sub>E] = [[X]\<^sub>R]"
          by simp
        have "Tock \<in>\<^sub>\<F>\<^sub>\<L> Finite_Linear_Model.last xs"
          using "3.prems"(2) False \<open>[[X]\<^sub>R] = flt2cttobs \<langle>Finite_Linear_Model.last xs\<rangle>\<^sub>\<F>\<^sub>\<L>\<close> by force
        then show ?thesis
          using f2 f1 by (metis (no_types) List.last.simps append_butlast_last_id append_is_Nil_conv butlast_append fl_cons_acceptance_consFL flt2cttobs_last_tock flt2goodTock_xs last_appendR list.simps(3))
      qed
      then have "\<rho> @ [[X]\<^sub>R,[Tock]\<^sub>E] = flt2cttobs(butlast xs &\<^sub>\<F>\<^sub>\<L> \<langle>(last xs,Tock)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>) \<and> butlast xs &\<^sub>\<F>\<^sub>\<L> \<langle>(last xs,Tock)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L> \<in> P"
        using xs_e by auto
      then have "\<rho> @ [[X]\<^sub>R,[Tock]\<^sub>E] = flt2cttobs(butlast xs &\<^sub>\<F>\<^sub>\<L> \<langle>(last xs,Tock)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>) 
                              \<and> butlast xs &\<^sub>\<F>\<^sub>\<L> \<langle>(last xs,Tock)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L> \<in> P
                              \<and> flt2goodTock (butlast xs &\<^sub>\<F>\<^sub>\<L> \<langle>(last xs,Tock)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>)"
        using flt2goodTock_xs
        by (metis "3.prems"(2) CollectI False \<open>[[X]\<^sub>R] = flt2cttobs \<langle>Finite_Linear_Model.last xs\<rangle>\<^sub>\<F>\<^sub>\<L>\<close> cttobs.inject(2) fl_cons_acceptance_consFL flt2cttobs.simps(1) flt2goodTock_extend_consFL_last_fl_e list.inject)
      then show ?thesis by blast
    qed
qed

lemma CTM2a_union_empty_trace:
  "CTM2a(P \<union> {[]}) = CTM2a(P)"
  unfolding CTM2a_def by auto

lemma CTM2b_union_empty_trace:
  "CTM2b(P \<union> {[]}) = CTM2b(P)"
  unfolding CTM2b_def by auto

lemma CTM2a_fl2ctt_for_FL2_FL1_FL0:
  assumes "FL2 P" "FL1 P" "FL0 P"
  shows "CTM2a(fl2ctt P)"
proof -
  have "CTM2a(fl2ctt P) = CTM2a({flt2cttobs fl|fl. fl \<in> P \<and> flt2goodTock fl} \<union> {[]})"
    using assms
    by (simp add: fl2ctt_FL0_FL1_flt2goodTock)
  also have "... = CTM2a({flt2cttobs fl|fl. fl \<in> P \<and> flt2goodTock fl})"
    using CTM2a_union_empty_trace by auto
  also have "... = True"
    using assms unfolding fl2ctt_def CTM2a_def apply auto
    using FL2_imp_CTM2a_part by blast
  finally show ?thesis by auto
qed

lemma CTM2b_fl2ctt_for_FL2_FL1_FL0:
  assumes "FL2 P" "FL1 P" "FL0 P"
  shows "CTM2b(fl2ctt P)"
proof -
  have "CTM2b(fl2ctt P) = CTM2b({flt2cttobs fl|fl. fl \<in> P \<and> flt2goodTock fl} \<union> {[]})"
    using assms
    by (simp add: fl2ctt_FL0_FL1_flt2goodTock)
  also have "... = CTM2b({flt2cttobs fl|fl. fl \<in> P \<and> flt2goodTock fl})"
    using CTM2b_union_empty_trace by auto
  also have "... = True"
    using assms unfolding fl2ctt_def CTM2b_def apply auto
    using FL2_imp_CTM2b_part by blast
  finally show ?thesis by auto
qed

lemma Tick_of_Refuals_in_flt2cttobs:
  assumes "tickWF Tick fl" "\<rho> @ [[X]\<^sub>R] = flt2cttobs fl"
  shows "Tick \<in> X"
  using assms apply (induct fl arbitrary:X \<rho> rule:flt2cttobs.induct, auto)
   apply (case_tac A, auto)
  apply (case_tac A, auto, case_tac b, auto, case_tac a, auto)
    apply (meson append_eq_Cons_conv cttobs.simps(4) list.inject)
  apply (case_tac a, auto)
  apply (metis List.last.simps cttobs.simps(4) list.simps(3) not_Cons_self snoc_eq_iff_butlast)
  apply (case_tac b, auto)
  by (meson append_eq_Cons_conv cttobs.simps(4) list.inject)

lemma CT4_fl2ctt_part:
  assumes "\<rho> @ [[X]\<^sub>R] = flt2cttobs fl" "FLTick0 Tick P"
          "fl \<in> P" 
    shows "\<exists>fl. \<rho> @ [[insert Tick X]\<^sub>R] = flt2cttobs fl \<and> fl \<in> P"
  using assms Tick_of_Refuals_in_flt2cttobs
  by (metis FLTick0_def insert_absorb)

lemma CT4_fl2ctt:
  assumes "FLTick0 Tick P"
  shows "CT4 (fl2ctt P)" 
  using assms unfolding CT4_def fl2ctt_def apply auto
  using CT4_fl2ctt_part by blast

lemma tickWF_add_Tick_refusal_trace_flt2cttobs_idem:
  assumes "tickWF Tick xs"
  shows "add_Tick_refusal_trace (flt2cttobs xs) = (flt2cttobs xs)"
  using assms apply(induct xs rule:flt2cttobs.induct, auto)
   apply (case_tac A, auto, case_tac a, auto, case_tac b, auto)
  by (case_tac A, auto, case_tac b, auto)

lemma CT4s_fl2ctt_part:
  assumes "FLTick0 Tick P" "fl \<in> P"
  shows "\<exists>fla. add_Tick_refusal_trace (flt2cttobs fl) = flt2cttobs fla \<and> fla \<in> P"
  using tickWF_add_Tick_refusal_trace_flt2cttobs_idem
  by (metis FLTick0_def assms(1) assms(2))

lemma CT4s_union_empty_trace:
  assumes "CT0 P" "CT1c P"
  shows "CT4s(P \<union> {[]}) = CT4s(P)"
  using assms unfolding CT4s_def by auto

lemma CT0_union_empty:
  "CT0(P \<union> {[]})"
  unfolding CT0_def by auto

lemma CT4s_fl2ctt:
  assumes "FLTick0 Tick P"
  shows "CT4s (fl2ctt P)" 
  using assms unfolding CT4s_def fl2ctt_def apply auto
  using CT4s_fl2ctt_part by blast

lemma CT3_trace_fl2cttobs:
  "CT3_trace (flt2cttobs fl)"
  apply (induct fl rule:flt2cttobs.induct) apply auto[1]
  apply (case_tac A, safe) 
   apply (case_tac a, safe) apply auto[1]
  apply (case_tac b, safe) apply auto[4]
  by (metis CT3_trace.simps(2) CT3_trace.simps(4) neq_Nil_conv)+

lemma CT3_fl2ctt:
  shows "CT3 (fl2ctt P)"
  unfolding CT3_def fl2ctt_def using CT3_trace_fl2cttobs by auto

abbreviation "CT2p \<rho> X P \<equiv> 
    {e. e \<noteq> Tock \<and> (\<exists>fl. \<rho> @ [[e]\<^sub>E] = flt2cttobs fl \<and> fl \<in> P \<and> flt2goodTock fl) \<or>
                e = Tock \<and> (\<exists>fl. \<rho> @ [[X]\<^sub>R, [e]\<^sub>E] = flt2cttobs fl \<and> fl \<in> P \<and> flt2goodTock fl)}"

lemma CT2_fl2ctt_part:
  assumes "FL2 P" "FL1 P" "FL0 P"
          "Y \<inter> CT2p \<rho> X P = {}"
          "\<rho> @ [[X]\<^sub>R] = flt2cttobs fl" "fl \<in> P" "flt2goodTock fl"
    shows "\<exists>fl. \<rho> @ [[X \<union> Y]\<^sub>R] = flt2cttobs fl \<and> fl \<in> P \<and> flt2goodTock fl \<and> X \<union> Y = X"
  using assms proof (induct fl arbitrary:\<rho> X Y rule:fltrace_induct)
case 1
  then show ?case by auto
next
  case (2 x xs)
  then show ?case
  proof (cases "last xs = \<bullet>")
    case True
    then have \<rho>_X:"\<rho> @ [[X]\<^sub>R] = flt2cttobs (xs) @ flt2cttobs(\<langle>x\<rangle>\<^sub>\<F>\<^sub>\<L>)"
      using 2
      by (metis (no_types, lifting) Finite_Linear_Model.last.simps(1) append.right_neutral bullet_right_zero2 flt2cttobs.simps(1) flt2cttobs_last_fl_not_bullet_dist_list_cons last_bullet_butlast_last last_bullet_then_last_cons)
    then show ?thesis
      proof (cases x)
        case acnil
        then show ?thesis using 2 True by auto
      next
        case (acset x2)
        then have "[[X]\<^sub>R] = flt2cttobs(\<langle>x\<rangle>\<^sub>\<F>\<^sub>\<L>)"
          using \<rho>_X by auto
        then have X_x2:"X = {x. x \<notin> x2}"
          using acset by auto
        
        have a:"\<forall>e. (e \<notin> X \<and> e \<noteq> Tock) \<longrightarrow> (\<exists>fl. \<rho> @ [[e]\<^sub>E] = flt2cttobs fl \<and> fl \<in> P \<and> flt2goodTock fl)"
          using "2.prems"(5) "2.prems"(6) "2.prems"(7) FL2_imp_CTM2a_part assms(1) by blast
        then have a2:"\<forall>e. (e \<in> x2 \<and> e \<noteq> Tock) \<longrightarrow> (\<exists>fl. \<rho> @ [[e]\<^sub>E] = flt2cttobs fl \<and> fl \<in> P \<and> flt2goodTock fl)"
          using X_x2 by blast
        
        have b:"\<forall>e. (e \<notin> X \<and> e = Tock) \<longrightarrow> (\<exists>fl. \<rho> @ [[X]\<^sub>R, [Tock]\<^sub>E] = flt2cttobs fl \<and> fl \<in> P \<and> flt2goodTock fl)"
          using "2.prems"(5) "2.prems"(6) "2.prems"(7) FL2_imp_CTM2b_part assms(1) by blast
        then have b2:"\<forall>e. (e \<in> x2 \<and> e = Tock) \<longrightarrow> (\<exists>fl. \<rho> @ [[X]\<^sub>R, [Tock]\<^sub>E] = flt2cttobs fl \<and> fl \<in> P \<and> flt2goodTock fl)"
          using X_x2 by blast

        have "x2 \<subseteq> {e. e \<noteq> Tock \<and> (\<exists>fl. \<rho> @ [[e]\<^sub>E] = flt2cttobs fl \<and> fl \<in> P \<and> flt2goodTock fl) \<or> e = Tock \<and> (\<exists>fl. \<rho> @ [[X]\<^sub>R, [e]\<^sub>E] = flt2cttobs fl \<and> fl \<in> P \<and> flt2goodTock fl)}"
          using a2 b2 by auto
        then have "Y \<subseteq> X"
          using 2 X_x2 by blast
        then have "X \<union> Y = X"
          by auto
       then show ?thesis using 2
         by metis
      qed
  next
    case False
    then have "\<rho> @ [[X]\<^sub>R] = flt2cttobs (xs)"
              "xs \<in> P"
              "flt2goodTock xs"
      using 2 by (metis concat_FL_last_not_bullet_absorb)+
    then show ?thesis using 2
      by blast
  qed
next
  case (3 x xs)
  then show ?case
  proof (cases "last xs = \<bullet>")
    case True
    then show ?thesis using 3
      by (metis (mono_tags, lifting) Nil_is_append_conv acceptance.distinct(1) last_cons_bullet_iff last_flt2cttobs_eq_ref_imp_last last_snoc not_Cons_self2)
  next
    case False
    then have "\<rho> @ [[X]\<^sub>R] = flt2cttobs (xs)"
      using 3 by (metis concat_FL_last_not_bullet_absorb)
    then show ?thesis 
      using 3 by (metis (no_types, lifting) False concat_FL_last_not_bullet_absorb)
  qed
qed

lemma CT2_fl2ctt_part':
  assumes "FL2 P" "FL1 P" "FL0 P"
          "Y \<inter> CT2p \<rho> X P = {}"
          "\<rho> @ [[X]\<^sub>R] = flt2cttobs fl" "fl \<in> P" "flt2goodTock fl"
        shows "\<exists>fl. \<rho> @ [[X \<union> Y]\<^sub>R] = flt2cttobs fl \<and> fl \<in> P \<and> flt2goodTock fl"
proof -
  have "\<exists>fl. \<rho> @ [[X \<union> Y]\<^sub>R] = flt2cttobs fl \<and> fl \<in> P \<and> flt2goodTock fl \<and> X \<union> Y = X"
    using assms by (auto simp add:CT2_fl2ctt_part)
  then have "\<exists>fl. \<rho> @ [[X \<union> Y]\<^sub>R] = flt2cttobs fl \<and> fl \<in> P \<and> flt2goodTock fl"
    by blast
  then show ?thesis by auto
qed

lemma CT2_union_empty_trace:
  "CT2(P \<union> {[]}) = CT2(P)"
  unfolding CT2_def by auto

lemma CT2_fl2ctt:
  assumes "FL2 P" "FL1 P" "FL0 P"
  shows "CT2 (fl2ctt P)"
proof -
  have "CT2 (fl2ctt P) = CT2 ({flt2cttobs fl|fl. fl \<in> P \<and> flt2goodTock fl} \<union> {[]})"
    using assms by (simp add: fl2ctt_FL0_FL1_flt2goodTock)
  also have "... = CT2 ({flt2cttobs fl|fl. fl \<in> P \<and> flt2goodTock fl})"
    using CT2_union_empty_trace by auto
  also have "... = (\<forall>\<rho> X Y.
        \<rho> @ [[X]\<^sub>R] \<in> {flt2cttobs fl |fl. fl \<in> P \<and> flt2goodTock fl} \<and>
        Y \<inter> CT2p \<rho> X P = {} \<longrightarrow>
        \<rho> @ [[X \<union> Y]\<^sub>R] \<in> {flt2cttobs fl |fl. fl \<in> P \<and> flt2goodTock fl})"
    using assms unfolding CT2_def fl2ctt_def by auto
  also have "... = True"
    using assms by (auto simp add: CT2_fl2ctt_part')
  finally show ?thesis by auto
qed

lemma cttWF_dist_cons_refusal': 
  assumes "cttWF (s @ [[S]\<^sub>R] @ t)"
  shows "cttWF ([[S]\<^sub>R] @ t)"
  using assms by(induct s rule:cttWF.induct, auto)

lemma flt2cttobs_split_cons:
  assumes "ys @ xs = flt2cttobs fl" "flt2goodTock fl" "cttWF ys"
  shows "\<exists>fl\<^sub>1 fl\<^sub>0. ys = flt2cttobs fl\<^sub>0 \<and> xs = flt2cttobs fl\<^sub>1 \<and> fl\<^sub>0 &\<^sub>\<F>\<^sub>\<L> fl\<^sub>1 = fl \<and> flt2goodTock fl\<^sub>0 \<and> flt2goodTock fl\<^sub>1"
  using assms
proof (induct fl arbitrary:xs ys rule:flt2cttobs.induct)
  case (1 A)
  then show ?case 
    apply (cases A, auto)
     apply (rule_tac x="\<langle>\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>" in exI, auto)
    apply (induct ys, auto)
     apply (rule_tac x="\<langle>[x2]\<^sub>\<F>\<^sub>\<L>\<rangle>\<^sub>\<F>\<^sub>\<L>" in exI, rule_tac x="\<langle>\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>" in exI, auto)
    by (rule_tac x="\<langle>\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>" in exI, rule_tac x="\<langle>[x2]\<^sub>\<F>\<^sub>\<L>\<rangle>\<^sub>\<F>\<^sub>\<L>" in exI, auto)
next
  case (2 A fl)
  then show ?case
  proof (cases "event A = Tock \<and> acceptance A \<noteq> \<bullet>")
    case True
    then show ?thesis sorry
  next
    case False
    then show ?thesis sorry
  qed
qed

lemma CT2s_fl2ctt_part:
  assumes "FL2 P" "FL1 P" "FL0 P" "FLTick0 Tick P"
          "Y \<inter> CT2p \<rho> X P = {}"
          "\<rho> @ [[X]\<^sub>R] @ \<sigma> = flt2cttobs fl" "fl \<in> P" "flt2goodTock fl"
        shows "\<exists>fl. \<rho> @ [[X \<union> Y]\<^sub>R] @ \<sigma> = flt2cttobs fl \<and> fl \<in> P \<and> flt2goodTock fl"
  using assms
proof (cases \<sigma>)
  case Nil
  then show ?thesis using assms by (auto simp add: CT2_fl2ctt_part')
next
  case (Cons a list)
  then have "a = [Tock]\<^sub>E"
  proof -
    have "cttWF(\<rho> @ [[X]\<^sub>R] @ \<sigma>)"
      using flt2cttobs_is_cttWF assms
      by (metis FLTick0_def)
    then have "cttWF([[X]\<^sub>R] @ \<sigma>)"
      using cttWF_dist_cons_refusal' by blast
    then have "cttWF([[X]\<^sub>R] @ (a # list))"
      using Cons by auto
    then have "cttWF([X]\<^sub>R # a # list)"
      by auto
    then show ?thesis
      using cttWF.elims(2) by blast
  qed

  have cttWF_cons:"cttWF(\<rho> @ [[X]\<^sub>R])"
    by (metis FLTick0_def append_assoc assms(4) assms(6) assms(7) cttWF_prefix_is_cttWF flt2cttobs_is_cttWF)
  then obtain fl\<^sub>0 fl\<^sub>1 where fls:"\<rho> @ [[X]\<^sub>R] = flt2cttobs fl\<^sub>0 \<and> flt2goodTock fl\<^sub>0 \<and> flt2goodTock fl\<^sub>1 \<and> \<sigma> = flt2cttobs fl\<^sub>1 \<and> fl\<^sub>0 &\<^sub>\<F>\<^sub>\<L> fl\<^sub>1 = fl"
    using assms flt2cttobs_split_cons
    by (metis (no_types, lifting) append_assoc)
  then have "fl\<^sub>0 \<in> P"
    using assms x_le_concat2_FL1 by blast
  then have "\<exists>fl. \<rho> @ [[X \<union> Y]\<^sub>R] = flt2cttobs fl \<and> fl \<in> P \<and> flt2goodTock fl \<and> X \<union> Y = X"
    using assms CT2_fl2ctt_part
    by (metis (no_types, lifting) acceptance.distinct(1) append_assoc append_is_Nil_conv append_self_conv concat_FL_last_not_bullet_absorb fls last_flt2cttobs_eq_ref_imp_last last_snoc list.simps(3) local.Cons)
  then show ?thesis
    by (metis assms(6) assms(7) assms(8))
qed
(*
  
  have "hd \<sigma> = [Tock]\<^sub>E"

  obtain fl\<^sub>0 fl\<^sub>1 where fls:"\<rho> @ [[X]\<^sub>R] = flt2cttobs fl\<^sub>0 \<and> \<sigma> = flt2cttobs fl\<^sub>1 \<and> flt2cttobs (fl\<^sub>0
  using assms proof (induct fl arbitrary:\<rho> X Y \<sigma> rule:fltrace_induct)
case 1
  then show ?case by auto
next
  case (2 x xs)
  then show ?case
  proof (cases "last xs = \<bullet>")
    case True
    then have \<rho>_X:"\<rho> @ [[X]\<^sub>R] @ \<sigma> = flt2cttobs (xs) @ flt2cttobs(\<langle>x\<rangle>\<^sub>\<F>\<^sub>\<L>)"
      using 2
      by (metis (no_types, lifting) Finite_Linear_Model.last.simps(1) append.right_neutral bullet_right_zero2 flt2cttobs.simps(1) flt2cttobs_last_fl_not_bullet_dist_list_cons last_bullet_butlast_last last_bullet_then_last_cons)
    then show ?thesis
      proof (cases x)
        case acnil
        then show ?thesis using 2 True by auto
      next
        case (acset x2)
        then show ?thesis using 2
        (*then have "[[X]\<^sub>R] @ \<sigma> = flt2cttobs(\<langle>x\<rangle>\<^sub>\<F>\<^sub>\<L>)"
          using \<rho>_X by auto*)
        then have X_x2:"X = {x. x \<notin> x2}"
          using acset by auto
        
        have a:"\<forall>e. (e \<notin> X \<and> e \<noteq> Tock) \<longrightarrow> (\<exists>fl. \<rho> @ [[e]\<^sub>E] = flt2cttobs fl \<and> fl \<in> P \<and> flt2goodTock fl)"
          using "2.prems"(5) "2.prems"(6) "2.prems"(7) FL2_imp_CTM2a_part assms(1) sledgehammer
        then have a2:"\<forall>e. (e \<in> x2 \<and> e \<noteq> Tock) \<longrightarrow> (\<exists>fl. \<rho> @ [[e]\<^sub>E] = flt2cttobs fl \<and> fl \<in> P \<and> flt2goodTock fl)"
          using X_x2 by blast
        
        have b:"\<forall>e. (e \<notin> X \<and> e = Tock) \<longrightarrow> (\<exists>fl. \<rho> @ [[X]\<^sub>R, [Tock]\<^sub>E] = flt2cttobs fl \<and> fl \<in> P \<and> flt2goodTock fl)"
          using "2.prems"(5) "2.prems"(6) "2.prems"(7) FL2_imp_CTM2b_part assms(1) by blast
        then have b2:"\<forall>e. (e \<in> x2 \<and> e = Tock) \<longrightarrow> (\<exists>fl. \<rho> @ [[X]\<^sub>R, [Tock]\<^sub>E] = flt2cttobs fl \<and> fl \<in> P \<and> flt2goodTock fl)"
          using X_x2 by blast

        have "x2 \<subseteq> {e. e \<noteq> Tock \<and> (\<exists>fl. \<rho> @ [[e]\<^sub>E] = flt2cttobs fl \<and> fl \<in> P \<and> flt2goodTock fl) \<or> e = Tock \<and> (\<exists>fl. \<rho> @ [[X]\<^sub>R, [e]\<^sub>E] = flt2cttobs fl \<and> fl \<in> P \<and> flt2goodTock fl)}"
          using a2 b2 by auto
        then have "Y \<subseteq> X"
          using 2 X_x2 by blast
        then have "X \<union> Y = X"
          by auto
       then show ?thesis using 2
         by metis
      qed
  next
    case False
    then have "\<rho> @ [[X]\<^sub>R] = flt2cttobs (xs)"
              "xs \<in> P"
              "flt2goodTock xs"
      using 2 by (metis concat_FL_last_not_bullet_absorb)+
    then show ?thesis using 2
      by blast
  qed
next
  case (3 x xs)
  then show ?case
  proof (cases "last xs = \<bullet>")
    case True
    then show ?thesis using 3
      by (metis (mono_tags, lifting) Nil_is_append_conv acceptance.distinct(1) last_cons_bullet_iff last_flt2cttobs_eq_ref_imp_last last_snoc not_Cons_self2)
  next
    case False
    then have "\<rho> @ [[X]\<^sub>R] = flt2cttobs (xs)"
      using 3 by (metis concat_FL_last_not_bullet_absorb)
    then show ?thesis 
      using 3 by (metis (no_types, lifting) False concat_FL_last_not_bullet_absorb)
  qed
qed*)

lemma CT2s_union_empty_trace:
  "CT2s(P \<union> {[]}) = CT2s(P)"
  unfolding CT2s_def by auto

lemma CT2s_fl2ctt:
  assumes "FL2 P" "FL1 P" "FL0 P" "FLTick0 Tick P"
  shows "CT2s (fl2ctt P)"
proof -
  have "CT2s (fl2ctt P) = CT2s ({flt2cttobs fl|fl. fl \<in> P \<and> flt2goodTock fl} \<union> {[]})"
    using assms by (simp add: fl2ctt_FL0_FL1_flt2goodTock)
  also have "... = CT2s ({flt2cttobs fl|fl. fl \<in> P \<and> flt2goodTock fl})"
    using CT2s_union_empty_trace by auto
 (* also have "... = (\<forall>\<rho> X Y \<sigma>.
        \<rho> @ [[X]\<^sub>R] @ \<sigma> \<in> {flt2cttobs fl |fl. fl \<in> P \<and> flt2goodTock fl} \<and>
        Y \<inter> CT2p \<rho> X P = {} \<longrightarrow>
        \<rho> @ [[X \<union> Y]\<^sub>R] @ \<sigma> \<in> {flt2cttobs fl |fl. fl \<in> P \<and> flt2goodTock fl})"
    using assms unfolding CT2s_def fl2ctt_def apply auto*)
  also have "... = True"
    using assms unfolding CT2s_def 
    apply auto using CT2s_fl2ctt_part
    by (auto)
  finally show ?thesis by auto
qed

lemma CTwf_fl2ctt:
  assumes "FLTick0 Tick P" 
  shows "CTwf(fl2ctt(P))"
  using assms unfolding fl2ctt_def CTwf_def
  by (auto simp add: FLTick0_def flt2cttobs_is_cttWF)

lemma CT1c_fl2ctt_part:
  assumes "\<rho> \<le>\<^sub>C flt2cttobs fl"
  shows "\<exists>fl\<^sub>2. \<rho> = flt2cttobs fl\<^sub>2 \<and> fl\<^sub>2 \<le> fl"
  using assms  
proof (induct fl arbitrary:\<rho> rule:flt2cttobs.induct)
case (1 A)
  then show ?case 
    apply (cases A, auto)
     apply (cases \<rho>, auto)
     apply (rule_tac x="\<langle>\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>" in exI, auto)
    apply (cases \<rho>, auto)
     apply (rule_tac x="\<langle>\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>" in exI, auto)
    apply (rule_tac x="\<langle>[x2]\<^sub>\<F>\<^sub>\<L>\<rangle>\<^sub>\<F>\<^sub>\<L>" in exI, auto)
    by (case_tac list, auto)
next
  case (2 A fl)
  then show ?case 
  proof (cases "event A = Tock \<and> acceptance A \<noteq> \<bullet>")
    case True
    then have "A = (acceptance(A),Tock)\<^sub>\<F>\<^sub>\<L> \<and> Tock \<in>\<^sub>\<F>\<^sub>\<L> acceptance(A)"
      by (metis Rep_aevent_inverse acceptance.rep_eq event.rep_eq event_in_acceptance prod.collapse)
    then have flt2cttobs_A_fl:"flt2cttobs (A #\<^sub>\<F>\<^sub>\<L> fl) = [{x. x \<notin>\<^sub>\<F>\<^sub>\<L> acceptance(A)}]\<^sub>R # [Tock]\<^sub>E # flt2cttobs fl"
      using True by auto
    then have "\<rho> \<le>\<^sub>C flt2cttobs (A #\<^sub>\<F>\<^sub>\<L> fl) = (\<rho> \<le>\<^sub>C ([{x. x \<notin>\<^sub>\<F>\<^sub>\<L> acceptance(A)}]\<^sub>R # [Tock]\<^sub>E # flt2cttobs fl))"
      using True by auto
    show ?thesis using True 2
    proof (induct \<rho>)
      case Nil
      then show ?case 
        apply auto
        by (rule_tac x="\<langle>\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>" in exI, auto)
    next
      case (Cons a as)
      then have "a = [{x. x \<notin>\<^sub>\<F>\<^sub>\<L> acceptance(A)}]\<^sub>R"
        by auto
      then show ?case using True 2 Cons
      proof (induct as)
        case Nil
        then show ?case using True
          apply auto
          by (rule_tac x="\<langle>acceptance(A)\<rangle>\<^sub>\<F>\<^sub>\<L>" in exI, auto)
      next
        case (Cons z zs)
        then have "z = [Tock]\<^sub>E"
          by auto
        then have "a # z # zs \<le>\<^sub>C flt2cttobs (A #\<^sub>\<F>\<^sub>\<L> fl)"
          using Cons by blast
        then have "[{x. x \<notin>\<^sub>\<F>\<^sub>\<L> acceptance(A)}]\<^sub>R # [Tock]\<^sub>E # zs \<le>\<^sub>C flt2cttobs (A #\<^sub>\<F>\<^sub>\<L> fl)"
          using Cons.prems(1) \<open>z = [Tock]\<^sub>E\<close> by blast
        then have "[{x. x \<notin>\<^sub>\<F>\<^sub>\<L> acceptance(A)}]\<^sub>R # [Tock]\<^sub>E # zs \<le>\<^sub>C [{x. x \<notin>\<^sub>\<F>\<^sub>\<L> acceptance(A)}]\<^sub>R # [Tock]\<^sub>E # flt2cttobs fl"
          using flt2cttobs_A_fl by auto
        then have "zs \<le>\<^sub>C flt2cttobs fl"
          by auto
        then have "\<exists>fl\<^sub>2. zs = flt2cttobs fl\<^sub>2 \<and> fl\<^sub>2 \<le> fl"
          using Cons True by blast
        then have "\<exists>fl\<^sub>2. [{x. x \<notin>\<^sub>\<F>\<^sub>\<L> acceptance(A)}]\<^sub>R # [Tock]\<^sub>E # zs = [{x. x \<notin>\<^sub>\<F>\<^sub>\<L> acceptance(A)}]\<^sub>R # [Tock]\<^sub>E # flt2cttobs fl\<^sub>2 \<and> A #\<^sub>\<F>\<^sub>\<L> fl\<^sub>2 \<le> A #\<^sub>\<F>\<^sub>\<L> fl"
          by auto
        then have "\<exists>fl\<^sub>2. [{x. x \<notin>\<^sub>\<F>\<^sub>\<L> acceptance(A)}]\<^sub>R # [Tock]\<^sub>E # zs = flt2cttobs (A #\<^sub>\<F>\<^sub>\<L> fl\<^sub>2) \<and> A #\<^sub>\<F>\<^sub>\<L> fl\<^sub>2 \<le> A #\<^sub>\<F>\<^sub>\<L> fl"
          using True by auto
        then have "\<exists>fl\<^sub>2. a # z # zs = flt2cttobs (A #\<^sub>\<F>\<^sub>\<L> fl\<^sub>2) \<and> A #\<^sub>\<F>\<^sub>\<L> fl\<^sub>2 \<le> A #\<^sub>\<F>\<^sub>\<L> fl"
          using Cons by auto
        then have "\<exists>fl\<^sub>2. a # z # zs = flt2cttobs fl\<^sub>2 \<and> fl\<^sub>2 \<le> A #\<^sub>\<F>\<^sub>\<L> fl"
          by blast
        then show ?case by blast
      qed
    qed
  next
    case False
    then show ?thesis using 2 apply auto
      apply (metis (no_types, hide_lams) bullet_left_zero2 ctt_prefix.simps(2) flt2cttobs.simps(1) flt2cttobs.simps(2) less_eq_fltrace.simps(3) neq_Nil_conv order_refl x_le_x_concat2)  
      apply (cases A, auto)
      apply (case_tac b, auto)
      apply (metis (no_types, hide_lams) acceptance_event bullet_left_zero2 ctt_prefix.simps(2) cttevent.distinct(1) flt2cttobs.simps(1) flt2cttobs.simps(2) less_eq_fltrace.simps(3) neq_Nil_conv order_refl x_le_x_concat2)
      using ctt_prefix_split apply force
      by (metis (no_types, hide_lams) acceptance_event bullet_left_zero2 ctt_prefix.simps(2) cttevent.distinct(5) flt2cttobs.simps(1) flt2cttobs.simps(2) less_eq_fltrace.simps(3) neq_Nil_conv order_refl x_le_x_concat2)
  qed
qed

(*
lemma
  assumes "\<rho> \<le>\<^sub>C x" "x = flt2cttobs fl" "tickWF Tick fl"
  shows "\<exists>fl\<^sub>2. \<rho> = flt2cttobs fl\<^sub>2 \<and> fl\<^sub>2 \<le> fl"
  using assms
proof (induct \<rho> x arbitrary:fl rule:ctt_prefix.induct)
  case (1 x)
  then show ?case
    apply auto
    apply (rule_tac x="\<langle>\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>" in exI, auto)
    by (simp add: prefixFL_induct21)
next
  case (2 x xa y ya)
  then have "xa \<le>\<^sub>C ya"
    using ctt_prefix.simps(2) by blast
  have "cttWF (y # ya)"
    by (simp add: "2.prems"(2) "2.prems"(3) flt2cttobs_is_cttWF)
  then have y_not_Tock:"y \<noteq> [Tock]\<^sub>E"
    using cttWF.simps(6) by blast
  then show ?case using 2
  proof (cases y)
    case (ObsEvent x1)
    then have "x1 \<noteq> Tock"
      using y_not_Tock by auto
    then show ?thesis using 2
      apply (induct fl, auto)
      using ObsEvent apply force
      apply (case_tac x1a, auto)
      apply (case_tac a, auto, case_tac b, auto)
      apply (metis ObsEvent acceptance_event amember.simps(2) cttobs.inject(1) flt2cttobs.simps(2) less_eq_fltrace.simps(3) order_refl)
      using ObsEvent apply blast
      apply (case_tac b, auto)
      apply (metis acceptance_event aevent_less_eq_iff_components cttevent.distinct(1) flt2cttobs.simps(2) less_eq_fltrace.simps(3))
      by (metis acceptance_event ctt_prefix.simps(1) ctt_prefix_antisym cttevent.distinct(5) flt2cttobs.simps(1) flt2cttobs.simps(2) order_refl)
(* then obtain yA where yA:"(flt2cttobs \<langle>(yA,x1)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L> = [[x1]\<^sub>E]) \<and> (x1 \<in>\<^sub>\<F>\<^sub>\<L> yA \<or> yA = \<bullet>)"
      using 2 y_not_Tock apply auto
      apply (case_tac x1, auto)
       apply (metis ObsEvent acceptance_event flt2cttobs.simps(1))
      by (metis acceptance_event cttevent.distinct(5) flt2cttobs.simps(1))
    then show ?thesis using 2*)
  next
    case (Ref x2)
    then have "x = [x2]\<^sub>R"
      using "2.prems"(1) by auto
    then show ?thesis using 2
    proof (induct ya)
      case Nil
      then show ?case using Ref 2 
        apply (induct fl, auto)
         apply (case_tac x, auto)
        apply (metis (no_types, lifting) Collect_cong acceptance.distinct(1) amember.simps(2) ctt_prefix.elims(2) flt2cttobs.simps(1) list.distinct(1) list.inject order_refl)
        apply (case_tac x1a, auto, case_tac b, auto, case_tac a, auto)
          apply (metis cttobs.simps(4) list.inject)
         apply (case_tac a, auto)
         apply (metis list.distinct(1) list.inject)
        apply (case_tac b, auto)
         apply (metis "2.prems"(2) Ref cttobs.simps(4) list.inject)
        by (metis cttobs.simps(4) last_snoc)
    next
      case (Cons z za)
      then have "cttWF (y # z # za)"
        by (simp add: flt2cttobs_is_cttWF)
      then have "z = [Tock]\<^sub>E"
        using Ref cttWF.elims(2) by blast
      then show ?case using Ref 2 Cons 
        proof (induct fl)
          case (Acceptance A)
          then show ?case using Ref 2 Cons apply auto
            apply (cases A, auto)
            by (metis Cons.prems(4) list.inject neq_Nil_conv)
        next
          case (AEvent x1a fla)
          then have "[x2]\<^sub>R # [Tock]\<^sub>E # za = flt2cttobs (x1a #\<^sub>\<F>\<^sub>\<L> fla)"
            by auto
          then have "x # [Tock]\<^sub>E # za = flt2cttobs (x1a #\<^sub>\<F>\<^sub>\<L> fla)"
            using 2 Cons by auto
          then have "[[x2]\<^sub>R,[Tock]\<^sub>E] @ za = flt2cttobs (x1a #\<^sub>\<F>\<^sub>\<L> fla)"
            by auto
          then have "[[x2]\<^sub>R,[Tock]\<^sub>E] @ za = flt2cttobs (\<langle>x1a,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>) @ flt2cttobs(fla)"
            by auto
          then have "za = flt2cttobs(fla)"
            by (metis (no_types, lifting) AEvent.prems(6) \<open>[x2]\<^sub>R # [Tock]\<^sub>E # za = flt2cttobs (x1a #\<^sub>\<F>\<^sub>\<L> fla)\<close> cttWF.simps(6) flt2cttobs.simps(1) flt2cttobs.simps(2) flt2cttobs_is_cttWF list.distinct(1) list.inject tickWF.simps(2))
          
          then show ?case sledgehammer sorry
        qed
        apply (induct fl, auto)
         apply (case_tac x, auto)
         apply (metis Cons.prems(4) list.inject neq_Nil_conv)
        apply (case_tac x1a, auto, case_tac b, auto)
          apply (metis cttobs.simps(4) list.sel(1))
         apply (case_tac a, auto)
        sledgehammer
         apply (metis list.distinct(1) list.inject)
        apply (case_tac x1a, auto, case_tac b, auto)
        apply (metis cttobs.simps(4) list.inject)
         apply (case_tac a, auto)
        apply (cases z, auto)
        sledgehammer
        apply (metis cttobs.inject(1) list.inject)
    qed
      using 2
      apply (induct fl, auto)
       apply (case_tac x, auto)
      apply (metis (no_types, lifting) Collect_cong acceptance.distinct(1) amember.simps(2) ctt_prefix.elims(2) flt2cttobs.simps(1) list.distinct(1) list.inject order_refl)
      apply (case_tac x1a, auto, case_tac b, auto)
        apply (metis cttobs.simps(4) list.inject)
       apply (case_tac a, auto)
      sorry
  qed
next
  case (3 x xa)
  then show ?case by auto
qed
*)
  
lemma CT1c_fl2ctt:
  assumes "FL1 P"
  shows "CT1c(fl2ctt(P))"
  using assms unfolding fl2ctt_def CT1c_def apply auto
  using CT1c_fl2ctt_part FL1_def by blast

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
  