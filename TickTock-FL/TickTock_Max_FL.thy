theory TickTock_Max_FL
  
imports
  "TickTock.TickTock_Core"
  "TickTock_Max"
  "FL.Finite_Linear_Tick_Param"
  "FL.Finite_Linear"
begin

text \<open> This theory establishes results about the Galois connection between the Finite-Linear
       model and tick-tock.\<close>

section \<open> Introduction \<close>

text \<open> Because the treatment of termination in FL.Finite_Linear_Tick_Param is parametric, the
       healthiness condition FL3, is in fact, an application of FLTick0 with the event Tick. \<close>

abbreviation "FL3 P == FLTick0 Tick P"

section \<open> Adjoints \<close>

subsection \<open> From FL to Tick-Tock \<close>

text \<open> The function fl2ttobs maps from FL traces to Tick-Tock traces. \<close>

fun fl2ttobs :: "('e ttevent) fltrace \<Rightarrow> ('e ttobs) list" where
"fl2ttobs \<langle>A\<rangle>\<^sub>\<F>\<^sub>\<L> = (if A = \<bullet> then [] else [[{z. z \<notin>\<^sub>\<F>\<^sub>\<L> A}]\<^sub>R])" |
"fl2ttobs (A #\<^sub>\<F>\<^sub>\<L> fl) = (if event(A) = Tock then
                             (if acceptance(A) \<noteq> \<bullet> then
                              ([{z. z \<notin>\<^sub>\<F>\<^sub>\<L> acceptance(A)}]\<^sub>R # [Tock]\<^sub>E # (fl2ttobs fl))
                              else []) 
                          else ([event A]\<^sub>E # fl2ttobs fl))"

lemma fl_le_TT1w:
  assumes "fl \<le> \<langle>[{z. z \<notin> x1}]\<^sub>\<F>\<^sub>\<L>\<rangle>\<^sub>\<F>\<^sub>\<L>" "[Ref x1] \<in> P" "TT1w P"
  shows "fl2ttobs fl \<in> P"
  using assms apply (cases fl, auto)
  apply (case_tac x1a, auto)
  by (case_tac "x2 = {z. z \<notin> x1}", auto)

lemma fl_le_TT1w_Event:
  assumes "fl \<le> \<langle>(\<bullet>,(Event ev))\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>" "[[Event ev]\<^sub>E] \<in> P" "TT1w P"
  shows "fl2ttobs fl \<in> P"
  using assms apply (cases fl, auto)
  apply (simp_all add: less_eq_aevent_def)
  apply (case_tac x1, auto)
    apply (case_tac x21, auto)
  by (case_tac x22, auto, case_tac x1, auto)+

lemma fl_le_TT1w_Tick:
  assumes "fl \<le> \<langle>(\<bullet>,Tick)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>" "[[Tick]\<^sub>E] \<in> P" "TT1w P"
  shows "fl2ttobs fl \<in> P"
  using assms apply (cases fl, auto)
     apply (simp_all add: less_eq_aevent_def)
  apply (case_tac x1, auto)
    apply (case_tac x21, auto)
   apply (case_tac a, auto)
  by (case_tac x22, auto, case_tac x1, auto)

(*declare ttWF_prefix_is_ttWF [simp]*)

lemma last_fl2ttobs_eq_ref_imp_last:
  assumes "fl2ttobs (xs) \<noteq> []" "List.last(fl2ttobs (xs)) = Ref r" 
  shows "last xs = [{x. x \<notin> r}]\<^sub>\<F>\<^sub>\<L>"
(* 
proof -
  have "xs = butlast xs &\<^sub>\<F>\<^sub>\<L> \<langle>last xs\<rangle>\<^sub>\<F>\<^sub>\<L>"
    using butlast_last_cons2_FL[symmetric] by auto
  *)
  using assms apply (induct xs rule:fl2ttobs.induct, auto)
   apply (case_tac A, auto)
  apply (case_tac A, auto)
   apply (case_tac b, auto)
     apply (metis ttobs.distinct(1) fl2ttobs.simps(1))
  apply (case_tac a, auto)
  apply (meson ttobs.distinct(1))
   apply (metis ttobs.distinct(1) fl2ttobs.simps(1))
   apply (case_tac b, auto)
    apply (metis ttobs.distinct(1) fl2ttobs.simps(1))
  apply (case_tac fl, auto)
   apply (metis (mono_tags) fl2ttobs.simps(1) ttobs.distinct(1))
  apply (case_tac x21, auto, case_tac b, auto)
   apply (meson ttobs.distinct(1))
    apply (case_tac a, auto)
   apply (meson ttobs.distinct(1))
  by (case_tac b, auto)

text \<open> The following function characterises the fltraces containing Tock
       events that do not follow from a \<bullet> acceptance. This helps in proving
       properties about fl2ttobs that require such a proviso. \<close>

fun flt2goodTock :: "('e ttevent) fltrace \<Rightarrow> bool" where
"flt2goodTock \<langle>A\<rangle>\<^sub>\<F>\<^sub>\<L> = True" |
"flt2goodTock (A #\<^sub>\<F>\<^sub>\<L> fl) = (if acceptance(A) \<noteq> \<bullet> then (flt2goodTock fl) else
                            (if event(A) = Tock then False else (flt2goodTock fl)))" 

lemma fl2ttobs_not_flt2goodTock_imp_fl2ttobs_eq_consFL_any:
  assumes "\<not> flt2goodTock xs"
  shows "fl2ttobs (xs &\<^sub>\<F>\<^sub>\<L> ys) = fl2ttobs (xs)"
  using assms by(induct xs, auto)

lemma fl2ttobs_is_ttWF:
  assumes "tickWF Tick fltrace"
  shows "ttWF (fl2ttobs fltrace)"
  using assms
  apply (induct fltrace rule:fl2ttobs.induct, auto)
  apply (case_tac A, auto, case_tac a, auto, case_tac b, auto)
  by (metis ttWF.simps(4) ttWF2.simps(1) ttWF2.simps(23) ttWF2_ttWF ttevent.exhaust fl2ttobs.simps(1))

lemma fl2ttobs_flt2goodTock_less_eq_exists:
  assumes "fl2ttobs fl \<noteq> []"
  shows "\<exists>fla. fl2ttobs fl = fl2ttobs fla \<and> fla \<le> fl \<and> flt2goodTock fla"
  using assms
proof (induct fl rule:flt2goodTock.induct)
  case (1 A)
  then show ?case 
    apply auto
    by (rule exI[where x="\<langle>A\<rangle>\<^sub>\<F>\<^sub>\<L>"], auto)
next
  case (2 A fl)
  then show ?case
  proof (cases "fl2ttobs fl \<noteq> []")
    case fl2ttobs_not_Nil:True
    then show ?thesis
      proof (cases "acceptance(A) \<noteq> \<bullet>")
      case True
        then have "\<exists>flaa. fl2ttobs fl = fl2ttobs flaa \<and> flaa \<le> fl \<and> flt2goodTock flaa"
          using fl2ttobs_not_Nil 2 by auto
        then show ?thesis using 2 True
          by (metis fl2ttobs.simps(2) flt2goodTock.simps(2) less_eq_fltrace.simps(3) order_refl)
      next
        case False
        then show ?thesis 
          using fl2ttobs_not_Nil 2 apply auto
          by (metis fl2ttobs.simps(2) flt2goodTock.simps(2) less_eq_fltrace.simps(3) order_refl)
      qed
  next
    case fl2ttobs_is_Nil:False
    then show ?thesis
      proof (cases "acceptance(A) \<noteq> \<bullet>")
        case True
        then show ?thesis using fl2ttobs_is_Nil 2 apply auto
          apply (rule exI[where x="\<langle>A,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>"], auto)
           apply (metis dual_order.refl dual_order.trans prefixFL_induct2)
          apply (rule exI[where x="\<langle>A,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>"], auto)
          by (metis dual_order.refl dual_order.trans prefixFL_induct2)
      next
      case False
      then show ?thesis using fl2ttobs_is_Nil 2 apply auto
        apply (rule exI[where x="\<langle>A,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>"], auto)
        by (metis dual_order.refl dual_order.trans prefixFL_induct2)
      qed
  qed
qed

lemma fl2ttobs_FL1_exists_flt2goodTock:
  assumes "fl2ttobs fl \<noteq> []" "fl \<in> P" "FL1 P"
  shows "\<exists>fla. fl2ttobs fl = fl2ttobs fla \<and> fla \<in> P \<and> flt2goodTock fla"
  using assms
  by (meson FL1_def fl2ttobs_flt2goodTock_less_eq_exists)

lemma flt2goodTock_consFL_imp:
  assumes "flt2goodTock xs" "e \<noteq> Tock" "e \<in>\<^sub>\<F>\<^sub>\<L> [x2]\<^sub>\<F>\<^sub>\<L>"
  shows "flt2goodTock (xs &\<^sub>\<F>\<^sub>\<L> \<langle>([x2]\<^sub>\<F>\<^sub>\<L>,e)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>)"
  using assms apply (induct xs, auto)
  by (case_tac x, auto)

text \<open> So FL processes are mapped to Tick-Tock processes by fl2ttm. \<close>

definition fl2ttm :: "('e ttevent) fltrace set \<Rightarrow> ('e ttobs) list set" where
"fl2ttm P = {fl2ttobs fl|fl. fl \<in> P}"

lemma fl2ttm_univ_disj:
  "fl2ttm (\<Union> P) = \<Union>{fl2ttm fl| fl. fl \<in> P}"
  unfolding fl2ttm_def by auto

lemma concat_ref_tock_imp_tock_in_last_of_fl2ttobs:
  assumes "ys @ [[x1]\<^sub>R] @ [[Tock]\<^sub>E] \<in> P" "TTwf P" "ttWFx P"
          "ys @ [[x1]\<^sub>R] @ [[Tock]\<^sub>E] = fl2ttobs fl @ [[Tock]\<^sub>E]"
    shows "Tock \<in>\<^sub>\<F>\<^sub>\<L> last fl"
proof -
  have a:"ys @ [[x1]\<^sub>R] = fl2ttobs fl" "fl \<noteq> \<langle>\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>"
    using assms 
    by (induct fl, auto)
  then have b:"fl2ttobs fl @ [[Tock]\<^sub>E] \<in> P"
    using assms apply auto
    by (metis assms(1) assms(4))
  then have "fl2ttobs fl \<noteq> []"
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
        by (metis ttWFx_def ttWFx_trace.simps(3) ttWFx_trace_cons_right append_Cons append_Nil)
      then obtain r where r:"List.last(fl2ttobs (xs &\<^sub>\<F>\<^sub>\<L> x)) = [r]\<^sub>R"
        using 2
        by (metis last_snoc)
      then have tock_not_in_r:"Tock \<notin> r"
        using 2
        by (metis ttobs.inject(2) last_snoc tock_not_in_x1)
      then have last_eq: "last (xs &\<^sub>\<F>\<^sub>\<L> x) = [{x. x \<notin> r}]\<^sub>\<F>\<^sub>\<L>"
        using r
        using "2.prems"(3)
        using "2.prems"(1) last_fl2ttobs_eq_ref_imp_last by fastforce
      then have "Tock \<in>\<^sub>\<F>\<^sub>\<L> [{x. x \<notin> r}]\<^sub>\<F>\<^sub>\<L>"
        by (simp add: tock_not_in_r)
      then show ?case using 2 last_eq by auto
    qed
  qed

lemma fl2ttobs_last_tock:
  assumes "Tock \<in>\<^sub>\<F>\<^sub>\<L> last fl" "flt2goodTock fl"
  shows "fl2ttobs (fl @\<^sub>\<F>\<^sub>\<L> \<langle>(last fl,Tock)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>) = fl2ttobs fl @ [[Tock]\<^sub>E]"
  using assms
  by (induct fl rule:fl2ttobs.induct, auto)

lemma fl2ttobs_butlast_cons_eq_list_cons:
  assumes "flt2goodTock fl"
  shows "fl2ttobs (butlast fl &\<^sub>\<F>\<^sub>\<L> \<langle>y,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>) = fl2ttobs(butlast fl) @ fl2ttobs(\<langle>y,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>)"
  using assms by (induct fl, auto)

lemma fl2ttobs_acceptance_cons_eq_list_cons:
  assumes "last fl = \<bullet>" "flt2goodTock fl"
  shows "fl2ttobs (fl &\<^sub>\<F>\<^sub>\<L> \<langle>y,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>) = fl2ttobs(fl) @ fl2ttobs(\<langle>y,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>)"
  using assms
  by (metis bullet_right_zero2 butlast_last_cons2_FL fl2ttobs_butlast_cons_eq_list_cons)

(* FIXME: Horrendous proof below *)
lemma fl2ttobs_last_non_tock:
  assumes "e \<noteq> Tock" "e \<in>\<^sub>\<F>\<^sub>\<L> last fl \<or> last fl = \<bullet>" "flt2goodTock fl" 
          "List.last(fl2ttobs fl) = [f]\<^sub>E"
  shows "fl2ttobs (fl @\<^sub>\<F>\<^sub>\<L> \<langle>(last fl,e)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>) = fl2ttobs fl @ [[e]\<^sub>E]"
  using assms
  apply (induct fl rule:fl2ttobs.induct, auto)
  apply (case_tac A, auto)
          apply (case_tac A, auto)
         apply (case_tac A, auto, case_tac b, auto)
  apply (case_tac a, auto)
           apply (case_tac "fl2ttobs fla = []", auto)
  apply (metis (no_types, lifting) acceptance_event fl2ttobs.simps(1) fl2ttobs.simps(2) flt2goodTock.elims(2) fltrace_concat.simps(3) list.discI)
  apply (metis (no_types, lifting) List.butlast.simps(2) acceptance_event append_eq_append_conv2 butlast_snoc fl2ttobs.simps(1) fl2ttobs.simps(2) flt2goodTock.elims(2) fltrace_concat.simps(3) list.discI)
  apply (metis (no_types, lifting) List.butlast.simps(2) acceptance_event append_eq_append_conv2 butlast_snoc fl2ttobs.simps(1) fl2ttobs.simps(2) flt2goodTock.elims(2) fltrace_concat.simps(3) list.discI)
  apply (metis (no_types, lifting) List.butlast.simps(2) acceptance_event append_eq_append_conv2 butlast_snoc fl2ttobs.simps(1) fl2ttobs.simps(2) flt2goodTock.elims(2) fltrace_concat.simps(3) list.discI)
         apply (case_tac A, auto, case_tac b, auto)
  apply (metis (no_types, lifting) List.butlast.simps(2) acceptance_event append_eq_append_conv2 butlast_snoc fl2ttobs.simps(1) fl2ttobs.simps(2) flt2goodTock.elims(2) fltrace_concat.simps(3) list.discI)
  apply (metis (no_types, lifting) List.butlast.simps(2) acceptance_event append_eq_append_conv2 butlast_snoc fl2ttobs.simps(1) fl2ttobs.simps(2) flt2goodTock.elims(2) fltrace_concat.simps(3) list.discI)
  apply (metis (no_types, lifting) List.butlast.simps(2) acceptance_event append_eq_append_conv2 butlast_snoc fl2ttobs.simps(1) fl2ttobs.simps(2) flt2goodTock.elims(2) fltrace_concat.simps(3) list.discI)
  apply (metis (no_types, lifting) List.butlast.simps(2) acceptance_event append_eq_append_conv2 butlast_snoc fl2ttobs.simps(1) fl2ttobs.simps(2) flt2goodTock.elims(2) fltrace_concat.simps(3) list.discI)
         apply (case_tac A, auto, case_tac b, auto)
  apply (metis (no_types, lifting) List.butlast.simps(2) acceptance_event append_eq_append_conv2 butlast_snoc fl2ttobs.simps(1) fl2ttobs.simps(2) flt2goodTock.elims(2) fltrace_concat.simps(3) list.discI)
   apply (metis (no_types, lifting) List.butlast.simps(2) acceptance_event append_eq_append_conv2 butlast_snoc fl2ttobs.simps(1) fl2ttobs.simps(2) flt2goodTock.elims(2) fltrace_concat.simps(3) list.discI)
  apply (metis (no_types, lifting) List.butlast.simps(2) acceptance_event append_eq_append_conv2 butlast_snoc fl2ttobs.simps(1) fl2ttobs.simps(2) flt2goodTock.elims(2) fltrace_concat.simps(3) list.discI)
  apply (metis (no_types, lifting) List.butlast.simps(2) acceptance_event append_eq_append_conv2 butlast_snoc fl2ttobs.simps(1) fl2ttobs.simps(2) flt2goodTock.elims(2) fltrace_concat.simps(3) list.discI)
         apply (case_tac A, auto, case_tac b, auto)
  apply (metis (no_types, lifting) List.butlast.simps(2) acceptance_event append_eq_append_conv2 butlast_snoc fl2ttobs.simps(1) fl2ttobs.simps(2) flt2goodTock.elims(2) fltrace_concat.simps(3) list.discI)
  apply (metis (no_types, lifting) List.butlast.simps(2) acceptance_event append_eq_append_conv2 butlast_snoc fl2ttobs.simps(1) fl2ttobs.simps(2) flt2goodTock.elims(2) fltrace_concat.simps(3) list.discI)
  apply (metis (no_types, lifting) List.butlast.simps(2) acceptance_event append_eq_append_conv2 butlast_snoc fl2ttobs.simps(1) fl2ttobs.simps(2) flt2goodTock.elims(2) fltrace_concat.simps(3) list.discI)
  by (metis (no_types, lifting) List.butlast.simps(2) acceptance_event append_eq_append_conv2 butlast_snoc fl2ttobs.simps(1) fl2ttobs.simps(2) flt2goodTock.elims(2) fltrace_concat.simps(3) list.discI)

lemma fl2ttobs_fl_acceptance:
  assumes "flt2goodTock fl" 
          "List.last(fl2ttobs fl) = [f]\<^sub>E" "fl2ttobs fl \<noteq> []"
  shows "fl2ttobs (fl @\<^sub>\<F>\<^sub>\<L> \<langle>[{x. x \<notin> r}]\<^sub>\<F>\<^sub>\<L>\<rangle>\<^sub>\<F>\<^sub>\<L>) = fl2ttobs fl @ [[r]\<^sub>R]"
  using assms
  apply (induct fl rule:fl2ttobs.induct, auto)
    apply (case_tac A, auto)
   apply (case_tac A, auto, case_tac b, auto)
  by (case_tac "fl2ttobs fla = []", auto, case_tac fla, auto, meson list.discI)+

lemma fl2ttobs_last_fl_not_bullet_dist_list_cons:
  assumes "last fl \<noteq> \<bullet>" "flt2goodTock fl"
  shows "fl2ttobs(fl) = fl2ttobs(butlast fl) @ fl2ttobs(\<langle>last fl\<rangle>\<^sub>\<F>\<^sub>\<L>)"
  using assms by (induct fl, auto)

lemma fl2ttm_FL0_FL1_flt2goodTock_non_bullet:
  assumes "FL0 P" "FL1 P"
  shows "fl2ttm P = {fl2ttobs fl|fl. fl \<in> P \<and> flt2goodTock fl \<and> fl \<noteq> \<langle>\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>} \<union> {[]}"
  using assms unfolding fl2ttm_def apply auto
  using fl2ttobs_FL1_exists_flt2goodTock
  apply (metis Finite_Linear_Model.butlast.simps(1) Finite_Linear_Model.last.simps(1) acceptance.distinct(1) append_self_conv2 fl2ttobs_last_fl_not_bullet_dist_list_cons flt2goodTock.simps(1))
  by (rule exI[where x="\<langle>\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>"], auto)

lemma fl2ttm_FL0_FL1_flt2goodTock:
  assumes "FL0 P" "FL1 P"
  shows "fl2ttm P = {fl2ttobs fl|fl. fl \<in> P \<and> flt2goodTock fl} \<union> {[]}"
  using assms unfolding fl2ttm_def apply auto
  using fl2ttobs_FL1_exists_flt2goodTock
  apply (metis)
  by (rule exI[where x="\<langle>\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>"], auto)

subsection \<open> From Tick-Tock to FL \<close>

definition ttm2fl :: "('e ttobs) list set \<Rightarrow> ('e ttevent) fltrace set" where
"ttm2fl P = \<Union>{fl. FLTick0 Tick fl \<and> FL1 fl \<and> (fl2ttm fl) \<subseteq> P}"

text \<open> Although in this definition we do not use all the healthiness conditions
       of FL, namely FL0, (as standard for an adjoint of a Galois connection), note 
       that an equivalent definition can be obtained for healthy P, that is, when
       applied to FL processes as proved in {@lemma ttm2fl_alt} in TickTock_FL.thy. 

       The fact we do not use the conjunction of all healthiness conditions in {@term ttm2fl}
       made it simpler to construct some of the proofs regarding the Galois connection. \<close>

lemma ttm2fl_mono:
  assumes "P \<subseteq> Q"
  shows "ttm2fl(P) \<subseteq> ttm2fl(Q)"
  using assms unfolding ttm2fl_def by auto

lemma fl2ttm_ttm2fl_refines: "fl2ttm(ttm2fl(P)) \<subseteq> P"
  unfolding ttm2fl_def fl2ttm_def by auto

(* BEGIN: weak_less_eq_fltrace lemmas. 
   TODO: Move into Finite_Linear_Model.thy and give it a nice symbol for this prefix relation. *)

lemma strong_less_eq_fltrace_cons_imp_lhs:
  assumes "(xs &\<^sub>\<F>\<^sub>\<L> \<langle>x\<rangle>\<^sub>\<F>\<^sub>\<L>) \<le>\<^sub>\<F>\<^sub>\<L> t"
  shows "xs \<le>\<^sub>\<F>\<^sub>\<L> t"
  using assms apply (induct xs t rule:strong_less_eq_fltrace.induct, auto)
  apply (cases x, auto)
  by (case_tac xa, auto)

lemma strong_less_eq_fltrace_imp_fl2ttobs_tt:
  assumes "s \<le>\<^sub>\<F>\<^sub>\<L> t"
  shows "fl2ttobs s \<le>\<^sub>C fl2ttobs t"
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

lemma event_not_in_set_of_fl2ttobs_imp_not_in_events:
  assumes "[e]\<^sub>E \<notin> set ys" "fl2ttobs zs = ys" "flt2goodTock zs"
  shows "e \<notin> events zs"
  using assms apply (induct zs arbitrary: ys e rule:fl2ttobs.induct, auto) 
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

subsection \<open> Bijection between maximal Tick-Tock and subset of FL. \<close>

lemma TTwf_1c_3_imp_fl2ttobs_FL1:
  assumes "x \<in> P" 
      and TTwf_healthy: "TTwf P" 
      and TT1w_healthy: "TT1w P"
      and ttWFx_healthy:  "ttWFx P"
      and TTick_healthy: "TTick P"
      and TT4w_healthy: "TT4w P"
  shows "\<exists>fl. x = fl2ttobs fl \<and> flt2goodTock fl \<and> (\<exists>x. FLTick0 Tick x \<and> FL1 x \<and> {fl2ttobs fl |fl. fl \<in> x} \<subseteq> P \<and> fl \<in> x)"
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
  then have xs_in_P:"xs \<in> P" "ttWF (xs @ [x])"
     apply auto
    using TT1w_def tt_prefix_concat apply blast
    using TTwf_def by blast

  from snoc show ?case
  proof (induct xs rule:rev_induct)
    case Nil
    then show ?case
    proof (cases x)
      case (Ref x1)
      then have "Tick \<in> x1"
        using TT4w_healthy TTick_healthy
        using TTick_def snoc.prems(1) by blast
      then show ?thesis
          apply (intro exI[where x="\<langle>[{x. x \<notin> x1} - {Tick}]\<^sub>\<F>\<^sub>\<L>\<rangle>\<^sub>\<F>\<^sub>\<L>"], auto)
          using Ref apply auto
           apply (rule exI[where x="{z. z \<le> \<langle>[{z. z \<notin> x1} - {Tick}]\<^sub>\<F>\<^sub>\<L>\<rangle>\<^sub>\<F>\<^sub>\<L>}"], auto)
        unfolding FLTick0_def apply auto
          apply (case_tac x, auto)
        apply (metis (full_types) amember.elims(2) less_eq_acceptance.simps(3) mem_Collect_eq)
        using FL1_def dual_order.trans apply blast
        using fl_le_TT1w using Nil by auto
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
        using fl_le_TT1w using Nil by auto
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
          using ObsEvent Nil by (simp add: fl_le_TT1w_Event)
      next
        case Tock
        text \<open> There cannot be a Tock without a refusal before it following ttWF,
               so this case is automatically solved. \<close>
        then show ?thesis
          using Nil.prems(3) ObsEvent
          by (metis TTwf_def Nil.prems(2) append_Nil ttWF.simps(6))
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
          using ObsEvent Nil by (simp add:fl_le_TT1w_Tick)
      qed
    qed
  next
    case yys:(snoc y ys)
    then have ys_y_inP:"ys @ [y] \<in> P" using TT1w_def
      by (metis tt_prefix_concat)
    then have ys_y_fl:"\<exists>fl. ys @ [y] = fl2ttobs fl \<and> flt2goodTock fl \<and> (\<exists>x. FLTick0 Tick x \<and> FL1 x \<and> {fl2ttobs fl |fl. fl \<in> x} \<subseteq> P \<and> fl \<in> x)"
      using yys by auto
    then have ys_y_x: "\<exists>fl. ys @ [y] @ [x] = fl2ttobs fl @ [x] \<and> flt2goodTock fl \<and> (\<exists>x. FLTick0 Tick x \<and> FL1 x \<and> {fl2ttobs fl |fl. fl \<in> x} \<subseteq> P \<and> fl \<in> x)"
      by auto

    then show ?case
    proof (cases y)
      case r1:(Ref r1)
      then have exp:"\<exists>fl. ys @ [[r1]\<^sub>R] @ [x] = fl2ttobs fl @ [x] \<and> (\<exists>x. FLTick0 Tick x \<and> FL1 x \<and> {fl2ttobs fl |fl. fl \<in> x} \<subseteq> P \<and> fl \<in> x)"
        using ys_y_fl by auto

      then show ?thesis
      proof (cases x)
        case (Ref r2) text \<open>Not allowed\<close>
        then have "\<not>ttWF (ys @ [Ref r1, Ref r2])"
          by (induct ys rule:ttWF.induct, auto)
        then have "ys @ [Ref r1, Ref r2] \<notin> P"
          using assms unfolding TTwf_def by auto
        then show ?thesis using Ref r1 yys by auto
      next
        case (ObsEvent e1)
        then show ?thesis
        proof (cases e1)
          case (Event e2)
          then have "\<not>ttWF (ys @ [Ref r1, [Event e2]\<^sub>E])"
            by (induct ys rule:ttWF.induct, auto)
          then show ?thesis
            using assms unfolding TTwf_def
            by (metis Cons_eq_append_conv Event ObsEvent append_eq_appendI r1 ys_y_x yys.prems(2))
        next
          case Tock
          then have tock_not_in_r1: "Tock \<notin> r1"
            using ttWFx_any_cons_end_tock ttWFx_healthy ObsEvent r1 yys.prems(2) by auto

          text \<open>Then from the hypothesis we have the case:\<close>

          then obtain fl where fl:"ys @ [Ref r1] = fl2ttobs fl \<and> flt2goodTock fl \<and> (\<exists>x. FLTick0 Tick x \<and> FL1 x \<and>  {fl2ttobs fl |fl. fl \<in> x} \<subseteq> P \<and> fl \<in> x)"
            using r1 ys_y_fl by blast
          then have last_fl_acceptance:"last fl = [{x. x \<notin> r1}]\<^sub>\<F>\<^sub>\<L>"
            by (metis (mono_tags, lifting) last_fl2ttobs_eq_ref_imp_last snoc_eq_iff_butlast)
          then have tock_in_last_fl: "Tock \<in>\<^sub>\<F>\<^sub>\<L> last fl"
            using tock_not_in_r1 by simp
          then have "ys @ [[r1]\<^sub>R] @ [[Tock]\<^sub>E] = fl2ttobs fl @ [[Tock]\<^sub>E] \<and> flt2goodTock fl \<and> (\<exists>x. FLTick0 Tick x \<and> FL1 x \<and> {fl2ttobs fl |fl. fl \<in> x} \<subseteq> P \<and> fl \<in> x)"
            by (simp add: fl)
          then have "ys @ [[r1]\<^sub>R] @ [[Tock]\<^sub>E] = fl2ttobs (fl @\<^sub>\<F>\<^sub>\<L> \<langle>(last fl,Tock)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>) \<and> flt2goodTock fl \<and> (\<exists>x. FLTick0 Tick x \<and> FL1 x \<and> {fl2ttobs fl |fl. fl \<in> x} \<subseteq> P \<and> fl \<in> x)"
            using tock_in_last_fl by (simp add: fl2ttobs_last_tock fl)

          have "{fl2ttobs fl\<^sub>0|fl\<^sub>0. fl\<^sub>0 \<le> fl} \<subseteq> P"
            using TT1w_healthy 
            using FL1_def fl subset_eq by blast

          have fl2ttobs_strongFL_subset:"{fl2ttobs fl\<^sub>0|fl\<^sub>0. fl\<^sub>0 \<le>\<^sub>\<F>\<^sub>\<L> (fl @\<^sub>\<F>\<^sub>\<L> \<langle>(last fl,Tock)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>)} \<subseteq> P"
            apply auto
            using strong_less_eq_fltrace_imp_fl2ttobs_tt
            by (metis (no_types, lifting) TT1w_def TT1w_healthy ObsEvent Tock \<open>ys @ [[r1]\<^sub>R] @ [[Tock]\<^sub>E] = fl2ttobs (fl @\<^sub>\<F>\<^sub>\<L> \<langle>(Finite_Linear_Model.last fl,Tock)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>) \<and> flt2goodTock fl \<and> (\<exists>x. FLTick0 Tick x \<and> FL1 x \<and> {fl2ttobs fl |fl. fl \<in> x} \<subseteq> P \<and> fl \<in> x)\<close> \<open>ys @ [[r1]\<^sub>R] @ [[Tock]\<^sub>E] = fl2ttobs fl @ [[Tock]\<^sub>E] \<and> flt2goodTock fl \<and> (\<exists>x. FLTick0 Tick x \<and> FL1 x \<and> {fl2ttobs fl |fl. fl \<in> x} \<subseteq> P \<and> fl \<in> x)\<close> fl r1 yys.prems(2))

          have "(ys @ [[r1]\<^sub>R] @ [[Tock]\<^sub>E] = fl2ttobs(fl @\<^sub>\<F>\<^sub>\<L> \<langle>(last fl,Tock)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>) \<and> flt2goodTock fl
                \<and> (\<exists>x. FLTick0 Tick x \<and> FL1 x \<and> {fl2ttobs fl |fl. fl \<in> x} \<subseteq> P \<and> fl \<in> x))"
            using \<open>ys @ [[r1]\<^sub>R] @ [[Tock]\<^sub>E] = fl2ttobs (fl @\<^sub>\<F>\<^sub>\<L> \<langle>(Finite_Linear_Model.last fl,Tock)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>) \<and> flt2goodTock fl \<and> (\<exists>x. FLTick0 Tick x \<and> FL1 x \<and> {fl2ttobs fl |fl. fl \<in> x} \<subseteq> P \<and> fl \<in> x)\<close> tock_in_last_fl by blast
          then have 
               "ys @ [[r1]\<^sub>R] @ [[Tock]\<^sub>E] = fl2ttobs (fl @\<^sub>\<F>\<^sub>\<L> \<langle>(last fl,Tock)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>) \<and> flt2goodTock fl  
                \<and> (\<exists>x. FLTick0 Tick x \<and> FL1 (x \<union> {fl\<^sub>0. fl\<^sub>0 \<le>\<^sub>\<F>\<^sub>\<L> (fl @\<^sub>\<F>\<^sub>\<L> \<langle>(last fl,Tock)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>)}) \<and> {fl2ttobs fl |fl. fl \<in> x} \<subseteq> P \<and> fl \<in> x)"
            using FL1_extends_strong_less_eq_fltrace_last tock_in_last_fl
            by (metis (mono_tags, lifting) Collect_cong \<open>ys @ [[r1]\<^sub>R] @ [[Tock]\<^sub>E] = fl2ttobs (fl @\<^sub>\<F>\<^sub>\<L> \<langle>(Finite_Linear_Model.last fl,Tock)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>) \<and> flt2goodTock fl \<and> (\<exists>x. FLTick0 Tick x \<and> FL1 x \<and> {fl2ttobs fl |fl. fl \<in> x} \<subseteq> P \<and> fl \<in> x)\<close> fl)
          then have 
               "ys @ [[r1]\<^sub>R] @ [[Tock]\<^sub>E] = fl2ttobs (fl @\<^sub>\<F>\<^sub>\<L> \<langle>(last fl,Tock)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>) \<and> flt2goodTock fl  
                \<and> (\<exists>x. FLTick0 Tick (x \<union> {fl\<^sub>0. fl\<^sub>0 \<le>\<^sub>\<F>\<^sub>\<L> (fl @\<^sub>\<F>\<^sub>\<L> \<langle>(last fl,Tock)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>)}) 
                        \<and> FL1 (x \<union> {fl\<^sub>0. fl\<^sub>0 \<le>\<^sub>\<F>\<^sub>\<L> (fl @\<^sub>\<F>\<^sub>\<L> \<langle>(last fl,Tock)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>)}) \<and> {fl2ttobs fl |fl. fl \<in> x} \<subseteq> P \<and> fl \<in> x)"
            using FLTick0_extends_strong_less_eq_fltrace_last tock_in_last_fl
            by auto
          then have 
               "ys @ [[r1]\<^sub>R] @ [[Tock]\<^sub>E] = fl2ttobs (fl @\<^sub>\<F>\<^sub>\<L> \<langle>(last fl,Tock)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>) \<and> flt2goodTock fl 
                \<and> (\<exists>x. FLTick0 Tick (x \<union> {fl\<^sub>0. fl\<^sub>0 \<le>\<^sub>\<F>\<^sub>\<L> (fl @\<^sub>\<F>\<^sub>\<L> \<langle>(last fl,Tock)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>)}) 
                    \<and> FL1 (x \<union> {fl\<^sub>0. fl\<^sub>0 \<le>\<^sub>\<F>\<^sub>\<L> (fl @\<^sub>\<F>\<^sub>\<L> \<langle>(last fl,Tock)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>)})
                    \<and> {fl2ttobs fl\<^sub>0 |fl\<^sub>0. fl\<^sub>0 \<in> (x \<union> {fl\<^sub>0. fl\<^sub>0 \<le>\<^sub>\<F>\<^sub>\<L> (fl @\<^sub>\<F>\<^sub>\<L> \<langle>(last fl,Tock)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>)})} \<subseteq> P \<and> fl \<in> x)"
            using fl2ttobs_strongFL_subset
            by (smt Un_iff mem_Collect_eq subset_iff)
          then have 
               "ys @ [[r1]\<^sub>R] @ [[Tock]\<^sub>E] = fl2ttobs (fl @\<^sub>\<F>\<^sub>\<L> \<langle>(last fl,Tock)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>) \<and> flt2goodTock fl 
                \<and> (\<exists>x. FLTick0 Tick (x \<union> {fl\<^sub>0. fl\<^sub>0 \<le>\<^sub>\<F>\<^sub>\<L> (fl @\<^sub>\<F>\<^sub>\<L> \<langle>(last fl,Tock)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>)}) 
                \<and> FL1 (x \<union> {fl\<^sub>0. fl\<^sub>0 \<le>\<^sub>\<F>\<^sub>\<L> (fl @\<^sub>\<F>\<^sub>\<L> \<langle>(last fl,Tock)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>)})
                \<and> {fl2ttobs fl\<^sub>0 |fl\<^sub>0. fl\<^sub>0 \<in> (x \<union> {fl\<^sub>0. fl\<^sub>0 \<le>\<^sub>\<F>\<^sub>\<L> (fl @\<^sub>\<F>\<^sub>\<L> \<langle>(last fl,Tock)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>)})} \<subseteq> P 
                \<and> fl \<in> x
                \<and> fl @\<^sub>\<F>\<^sub>\<L> \<langle>(last fl,Tock)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L> \<in> (x \<union> {fl\<^sub>0. fl\<^sub>0 \<le>\<^sub>\<F>\<^sub>\<L> (fl @\<^sub>\<F>\<^sub>\<L> \<langle>(last fl,Tock)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>)}))"
            by (simp add: strong_less_eq_fltrace_refl)
          then have 
               "ys @ [[r1]\<^sub>R] @ [[Tock]\<^sub>E] = fl2ttobs (fl @\<^sub>\<F>\<^sub>\<L> \<langle>(last fl,Tock)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>) \<and> flt2goodTock fl 
                \<and> (\<exists>z. FLTick0 Tick z \<and> FL1 z
                \<and> {fl2ttobs fl\<^sub>0 |fl\<^sub>0. fl\<^sub>0 \<in> z} \<subseteq> P 
                \<and> fl @\<^sub>\<F>\<^sub>\<L> \<langle>(last fl,Tock)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L> \<in> z)"
            by blast
          then have 
               "ys @ [[r1]\<^sub>R] @ [[Tock]\<^sub>E] = fl2ttobs (fl @\<^sub>\<F>\<^sub>\<L> \<langle>(last fl,Tock)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>) \<and> flt2goodTock fl 
                \<and> flt2goodTock (fl @\<^sub>\<F>\<^sub>\<L> \<langle>(last fl,Tock)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>)
                \<and> (\<exists>z. FLTick0 Tick z \<and> FL1 z
                \<and> {fl2ttobs fl\<^sub>0 |fl\<^sub>0. fl\<^sub>0 \<in> z} \<subseteq> P 
                \<and> fl @\<^sub>\<F>\<^sub>\<L> \<langle>(last fl,Tock)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L> \<in> z)"
            using tock_in_last_fl by (simp add:flt2goodTock_extend_consFL_last_fl_e)
          then have 
               "\<exists>fl. ys @ [[r1]\<^sub>R] @ [[Tock]\<^sub>E] = fl2ttobs fl \<and> flt2goodTock fl 
                \<and> (\<exists>z. FLTick0 Tick z \<and> FL1 z \<and> {fl2ttobs fl\<^sub>0 |fl\<^sub>0. fl\<^sub>0 \<in> z} \<subseteq> P \<and> fl \<in> z)"
            by blast
          then show ?thesis using Tock ObsEvent r1 by auto
        next
          case Tick
          then have "\<not>ttWF (ys @ [Ref r1, [Tick]\<^sub>E])"
            by (induct ys rule:ttWF.induct, auto)
          then show ?thesis
            using TTwf_healthy unfolding TTwf_def
            by (metis ObsEvent Tick append.assoc append_Cons append_Nil r1 ys_y_x yys.prems(2))
        qed
      qed
    next
      case e1:(ObsEvent e1)
      text \<open>Then from the hypothesis we have the case:\<close>
      then obtain fl where fl:"ys @ [[e1]\<^sub>E] = fl2ttobs fl \<and> flt2goodTock fl \<and> (\<exists>x. FLTick0 Tick x \<and> FL1 x \<and> {fl2ttobs fl |fl. fl \<in> x} \<subseteq> P \<and> fl \<in> x)"
        using ys_y_fl by blast
      then have ys_e1_x:"ys @ [[e1]\<^sub>E] @ [x] = fl2ttobs fl @ [x] \<and> flt2goodTock fl \<and> (\<exists>x. FLTick0 Tick x \<and> FL1 x \<and> {fl2ttobs fl |fl. fl \<in> x} \<subseteq> P \<and> fl \<in> x)"
        by auto
      then have last_fl:"last fl = \<bullet>"
        by (metis ttobs.distinct(1) fl fl2ttobs.simps(1) fl2ttobs_last_fl_not_bullet_dist_list_cons last_snoc)

      then show ?thesis
      proof (cases x)
        case e2:(ObsEvent e2)
        then have "ys @ [[e1]\<^sub>E] @ [[e2]\<^sub>E] \<in> P"
          using e1 fl ys_e1_x yys.prems(2) by presburger
        then have "[Tick]\<^sub>E \<notin> set (ys @ [[e1]\<^sub>E])" 
          using TTwf_healthy TTwf_concat_prefix_set_no_Tick
          using e1 e2 yys.prems(2) by blast
        then have Tick_not_in_events_fl: "Tick \<notin> events fl"
          by (simp add: event_not_in_set_of_fl2ttobs_imp_not_in_events fl)
          
        then show ?thesis
        proof (cases e2)
          case (Event e3)
          have fl2ttobs_strongFL_subset:"{fl2ttobs fl\<^sub>0|fl\<^sub>0. fl\<^sub>0 \<le>\<^sub>\<F>\<^sub>\<L> (fl @\<^sub>\<F>\<^sub>\<L> \<langle>(last fl,Event e3)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>)} \<subseteq> P"
            apply auto
            using strong_less_eq_fltrace_imp_fl2ttobs_tt
            by (metis (no_types, lifting) TT1w_def TT1w_healthy Event ttevent.simps(3) e1 e2 fl fl2ttobs_last_non_tock last_fl last_snoc yys.prems(2))
          
          from fl have fl_e3: "ys @ [[e1]\<^sub>E] @ [[Event e3]\<^sub>E] = fl2ttobs fl @ [[Event e3]\<^sub>E]
                  \<and> flt2goodTock fl \<and> (\<exists>x. FLTick0 Tick x \<and> FL1 x \<and> {fl2ttobs fl\<^sub>0 |fl\<^sub>0. fl\<^sub>0 \<in> x} \<subseteq> P \<and> fl \<in> x)"
            using ys_e1_x by auto
          also have "... =
                  (ys @ [[e1]\<^sub>E] @ [[Event e3]\<^sub>E] = fl2ttobs(fl @\<^sub>\<F>\<^sub>\<L> \<langle>(last fl,Event e3)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>)
                  \<and> flt2goodTock fl \<and> (\<exists>x. FLTick0 Tick x \<and> FL1 x \<and> {fl2ttobs fl\<^sub>0 |fl\<^sub>0. fl\<^sub>0 \<in> x} \<subseteq> P \<and> fl \<in> x))"
            proof -
              from fl have "ys @ [[e1]\<^sub>E] = fl2ttobs fl"
                by auto
              then have "List.last(fl2ttobs fl) = [e1]\<^sub>E"
                by (metis last_snoc)
              then have "fl2ttobs fl @ [[Event e3]\<^sub>E] = fl2ttobs(fl @\<^sub>\<F>\<^sub>\<L> \<langle>(last fl,Event e3)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>)"
                using fl last_fl fl2ttobs_last_non_tock
                by (metis (no_types, lifting) ttevent.distinct(1))
              then show ?thesis using calculation  by auto
            qed
          finally have "
                  ys @ [[e1]\<^sub>E] @ [[Event e3]\<^sub>E] = fl2ttobs(fl @\<^sub>\<F>\<^sub>\<L> \<langle>(last fl,Event e3)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>)
                  \<and> flt2goodTock fl 
                  \<and> (\<exists>x. FLTick0 Tick x \<and> FL1 (x \<union> {fl\<^sub>0. fl\<^sub>0 \<le>\<^sub>\<F>\<^sub>\<L> (fl @\<^sub>\<F>\<^sub>\<L> \<langle>(last fl,Event e3)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>)}) 
                      \<and> {fl2ttobs fl\<^sub>0 |fl\<^sub>0. fl\<^sub>0 \<in> x} \<subseteq> P \<and> fl \<in> x)"
              apply auto using FL1_extends_strong_less_eq_fltrace_last_bullet last_fl 
            by fastforce
          then have "
                  ys @ [[e1]\<^sub>E] @ [[Event e3]\<^sub>E] = fl2ttobs(fl @\<^sub>\<F>\<^sub>\<L> \<langle>(last fl,Event e3)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>)
                  \<and> flt2goodTock fl 
                  \<and> (\<exists>x. FLTick0 Tick (x \<union> {fl\<^sub>0. fl\<^sub>0 \<le>\<^sub>\<F>\<^sub>\<L> (fl @\<^sub>\<F>\<^sub>\<L> \<langle>(last fl,Event e3)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>)}) 
                      \<and> FL1 (x \<union> {fl\<^sub>0. fl\<^sub>0 \<le>\<^sub>\<F>\<^sub>\<L> (fl @\<^sub>\<F>\<^sub>\<L> \<langle>(last fl,Event e3)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>)}) 
                      \<and> {fl2ttobs fl\<^sub>0 |fl\<^sub>0. fl\<^sub>0 \<in> x} \<subseteq> P \<and> fl \<in> x)"
            apply auto using FL0_Tick_extends_strong_less_eq_fltrace_last_bullet last_fl Tick_not_in_events_fl
            by blast
         then have "
                  ys @ [[e1]\<^sub>E] @ [[Event e3]\<^sub>E] = fl2ttobs(fl @\<^sub>\<F>\<^sub>\<L> \<langle>(last fl,Event e3)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>)
                  \<and> flt2goodTock fl 
                  \<and> (\<exists>x. FLTick0 Tick (x \<union> {fl\<^sub>0. fl\<^sub>0 \<le>\<^sub>\<F>\<^sub>\<L> (fl @\<^sub>\<F>\<^sub>\<L> \<langle>(last fl,Event e3)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>)}) 
                      \<and> FL1 (x \<union> {fl\<^sub>0. fl\<^sub>0 \<le>\<^sub>\<F>\<^sub>\<L> (fl @\<^sub>\<F>\<^sub>\<L> \<langle>(last fl,Event e3)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>)}) 
                      \<and> {fl2ttobs fl\<^sub>0 |fl\<^sub>0. fl\<^sub>0 \<in> (x \<union> {fl\<^sub>0. fl\<^sub>0 \<le>\<^sub>\<F>\<^sub>\<L> (fl @\<^sub>\<F>\<^sub>\<L> \<langle>(last fl,Event e3)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>)})} \<subseteq> P \<and> fl \<in> x)"  
           using fl2ttobs_strongFL_subset 
           by (smt Un_iff mem_Collect_eq subset_iff)
         then have "
                  ys @ [[e1]\<^sub>E] @ [[Event e3]\<^sub>E] = fl2ttobs(fl @\<^sub>\<F>\<^sub>\<L> \<langle>(last fl,Event e3)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>)
                  \<and> flt2goodTock fl 
                  \<and> (\<exists>x. FLTick0 Tick (x \<union> {fl\<^sub>0. fl\<^sub>0 \<le>\<^sub>\<F>\<^sub>\<L> (fl @\<^sub>\<F>\<^sub>\<L> \<langle>(last fl,Event e3)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>)}) 
                      \<and> FL1 (x \<union> {fl\<^sub>0. fl\<^sub>0 \<le>\<^sub>\<F>\<^sub>\<L> (fl @\<^sub>\<F>\<^sub>\<L> \<langle>(last fl,Event e3)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>)}) 
                      \<and> {fl2ttobs fl\<^sub>0 |fl\<^sub>0. fl\<^sub>0 \<in> (x \<union> {fl\<^sub>0. fl\<^sub>0 \<le>\<^sub>\<F>\<^sub>\<L> (fl @\<^sub>\<F>\<^sub>\<L> \<langle>(last fl,Event e3)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>)})} \<subseteq> P 
                      \<and> fl \<in> x
                      \<and> fl @\<^sub>\<F>\<^sub>\<L> \<langle>(last fl,Event e3)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L> \<in> (x \<union> {fl\<^sub>0. fl\<^sub>0 \<le>\<^sub>\<F>\<^sub>\<L> (fl @\<^sub>\<F>\<^sub>\<L> \<langle>(last fl,Event e3)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>)}))"
            by (simp add: strong_less_eq_fltrace_refl)  
         then have "
                  ys @ [[e1]\<^sub>E] @ [[Event e3]\<^sub>E] = fl2ttobs(fl @\<^sub>\<F>\<^sub>\<L> \<langle>(last fl,Event e3)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>)
                  \<and> flt2goodTock fl 
                  \<and> (\<exists>z. FLTick0 Tick z \<and> FL1 z 
                      \<and> {fl2ttobs fl\<^sub>0 |fl\<^sub>0. fl\<^sub>0 \<in> z} \<subseteq> P 
                      \<and> fl @\<^sub>\<F>\<^sub>\<L> \<langle>(last fl,Event e3)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L> \<in> z)"
           by blast
         then have "
                  ys @ [[e1]\<^sub>E] @ [[Event e3]\<^sub>E] = fl2ttobs(fl @\<^sub>\<F>\<^sub>\<L> \<langle>(last fl,Event e3)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>)
                  \<and> flt2goodTock fl 
                  \<and> flt2goodTock (fl @\<^sub>\<F>\<^sub>\<L> \<langle>(last fl,Event e3)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>)
                  \<and> (\<exists>z. FLTick0 Tick z \<and> FL1 z 
                      \<and> {fl2ttobs fl\<^sub>0 |fl\<^sub>0. fl\<^sub>0 \<in> z} \<subseteq> P 
                      \<and> fl @\<^sub>\<F>\<^sub>\<L> \<langle>(last fl,Event e3)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L> \<in> z)"
           using last_fl flt2goodTock_extend_consFL_last_fl_bullet
           by blast
         then have "
                  \<exists>fl. ys @ [[e1]\<^sub>E] @ [[Event e3]\<^sub>E] = fl2ttobs(fl)
                  \<and> flt2goodTock fl 
                  \<and> (\<exists>z. FLTick0 Tick z \<and> FL1 z \<and> {fl2ttobs fl\<^sub>0 |fl\<^sub>0. fl\<^sub>0 \<in> z} \<subseteq> P \<and> fl \<in> z)"
           by blast
         then show ?thesis using Event e1 e2 by auto
        next
          case Tock
          then have "\<not>ttWF (ys @ [[e1]\<^sub>E, [Tock]\<^sub>E])"
            apply (induct ys rule:ttWF.induct, auto)
            using ttWF.elims(2) ttWF.simps(6) by blast+
          then show ?thesis
            using e1 e2 TTwf_healthy unfolding TTwf_def
            by (metis Tock append_eq_Cons_conv fl ys_e1_x yys.prems(2))
        next
          case Tick
          have fl2ttobs_strongFL_subset:"{fl2ttobs fl\<^sub>0|fl\<^sub>0. fl\<^sub>0 \<le>\<^sub>\<F>\<^sub>\<L> (fl @\<^sub>\<F>\<^sub>\<L> \<langle>(last fl,Tick)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>)} \<subseteq> P"
            apply auto
            using strong_less_eq_fltrace_imp_fl2ttobs_tt
            by (metis (no_types, lifting) TT1w_def TT1w_healthy Tick ttevent.distinct(5) e1 e2 fl fl2ttobs_last_non_tock last_fl last_snoc yys.prems(2))
            
          from fl have fl_e3: "ys @ [[e1]\<^sub>E] @ [[Tick]\<^sub>E] = fl2ttobs fl @ [[Tick]\<^sub>E]
                  \<and> flt2goodTock fl \<and> (\<exists>x. FLTick0 Tick x \<and> FL1 x \<and> {fl2ttobs fl\<^sub>0 |fl\<^sub>0. fl\<^sub>0 \<in> x} \<subseteq> P \<and> fl \<in> x)"
            using ys_e1_x by auto
          also have "... =
                  (ys @ [[e1]\<^sub>E] @ [[Tick]\<^sub>E] = fl2ttobs(fl @\<^sub>\<F>\<^sub>\<L> \<langle>(last fl,Tick)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>)
                  \<and> flt2goodTock fl \<and> (\<exists>x. FLTick0 Tick x \<and> FL1 x \<and> {fl2ttobs fl\<^sub>0 |fl\<^sub>0. fl\<^sub>0 \<in> x} \<subseteq> P \<and> fl \<in> x))"
            proof -
              from fl have "ys @ [[e1]\<^sub>E] = fl2ttobs fl"
                by auto
              then have "List.last(fl2ttobs fl) = [e1]\<^sub>E"
                by (metis last_snoc)
              then have "fl2ttobs fl @ [[Tick]\<^sub>E] = fl2ttobs(fl @\<^sub>\<F>\<^sub>\<L> \<langle>(last fl,Tick)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>)"
                using fl last_fl fl2ttobs_last_non_tock
                by (metis (no_types, lifting) ttevent.simps(7))
              then show ?thesis using calculation  by auto
            qed
          finally have "
                  ys @ [[e1]\<^sub>E] @ [[Tick]\<^sub>E] = fl2ttobs(fl @\<^sub>\<F>\<^sub>\<L> \<langle>(last fl,Tick)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>)
                  \<and> flt2goodTock fl 
                  \<and> (\<exists>x. FLTick0 Tick x \<and> FL1 (x \<union> {fl\<^sub>0. fl\<^sub>0 \<le>\<^sub>\<F>\<^sub>\<L> (fl @\<^sub>\<F>\<^sub>\<L> \<langle>(last fl,Tick)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>)}) 
                      \<and> {fl2ttobs fl\<^sub>0 |fl\<^sub>0. fl\<^sub>0 \<in> x} \<subseteq> P \<and> fl \<in> x)"
              apply auto using FL1_extends_strong_less_eq_fltrace_last_bullet last_fl 
            by fastforce
         then have "
                  ys @ [[e1]\<^sub>E] @ [[Tick]\<^sub>E] = fl2ttobs(fl @\<^sub>\<F>\<^sub>\<L> \<langle>(last fl,Tick)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>)
                  \<and> flt2goodTock fl 
                  \<and> (\<exists>x. FLTick0 Tick (x \<union> {fl\<^sub>0. fl\<^sub>0 \<le>\<^sub>\<F>\<^sub>\<L> (fl @\<^sub>\<F>\<^sub>\<L> \<langle>(last fl,Tick)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>)}) 
                      \<and> FL1 (x \<union> {fl\<^sub>0. fl\<^sub>0 \<le>\<^sub>\<F>\<^sub>\<L> (fl @\<^sub>\<F>\<^sub>\<L> \<langle>(last fl,Tick)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>)}) 
                      \<and> {fl2ttobs fl\<^sub>0 |fl\<^sub>0. fl\<^sub>0 \<in> x} \<subseteq> P \<and> fl \<in> x)"
          apply auto using FL0_Tick_extends_strong_less_eq_fltrace_last_bullet last_fl Tick_not_in_events_fl
            by blast
         then have "
                  ys @ [[e1]\<^sub>E] @ [[Tick]\<^sub>E] = fl2ttobs(fl @\<^sub>\<F>\<^sub>\<L> \<langle>(last fl,Tick)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>)
                  \<and> flt2goodTock fl 
                  \<and> (\<exists>x. FLTick0 Tick (x \<union> {fl\<^sub>0. fl\<^sub>0 \<le>\<^sub>\<F>\<^sub>\<L> (fl @\<^sub>\<F>\<^sub>\<L> \<langle>(last fl,Tick)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>)}) 
                      \<and> FL1 (x \<union> {fl\<^sub>0. fl\<^sub>0 \<le>\<^sub>\<F>\<^sub>\<L> (fl @\<^sub>\<F>\<^sub>\<L> \<langle>(last fl,Tick)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>)}) 
                      \<and> {fl2ttobs fl\<^sub>0 |fl\<^sub>0. fl\<^sub>0 \<in> (x \<union> {fl\<^sub>0. fl\<^sub>0 \<le>\<^sub>\<F>\<^sub>\<L> (fl @\<^sub>\<F>\<^sub>\<L> \<langle>(last fl,Tick)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>)})} \<subseteq> P \<and> fl \<in> x)"  
           using fl2ttobs_strongFL_subset 
           by (smt Un_iff mem_Collect_eq subset_iff)
         then have "
                  ys @ [[e1]\<^sub>E] @ [[Tick]\<^sub>E] = fl2ttobs(fl @\<^sub>\<F>\<^sub>\<L> \<langle>(last fl,Tick)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>)
                  \<and> flt2goodTock fl 
                  \<and> (\<exists>x. FLTick0 Tick (x \<union> {fl\<^sub>0. fl\<^sub>0 \<le>\<^sub>\<F>\<^sub>\<L> (fl @\<^sub>\<F>\<^sub>\<L> \<langle>(last fl,Tick)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>)}) 
                      \<and> FL1 (x \<union> {fl\<^sub>0. fl\<^sub>0 \<le>\<^sub>\<F>\<^sub>\<L> (fl @\<^sub>\<F>\<^sub>\<L> \<langle>(last fl,Tick)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>)}) 
                      \<and> {fl2ttobs fl\<^sub>0 |fl\<^sub>0. fl\<^sub>0 \<in> (x \<union> {fl\<^sub>0. fl\<^sub>0 \<le>\<^sub>\<F>\<^sub>\<L> (fl @\<^sub>\<F>\<^sub>\<L> \<langle>(last fl,Tick)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>)})} \<subseteq> P 
                      \<and> fl \<in> x
                      \<and> fl @\<^sub>\<F>\<^sub>\<L> \<langle>(last fl,Tick)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L> \<in> (x \<union> {fl\<^sub>0. fl\<^sub>0 \<le>\<^sub>\<F>\<^sub>\<L> (fl @\<^sub>\<F>\<^sub>\<L> \<langle>(last fl,Tick)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>)}))"
            by (simp add: strong_less_eq_fltrace_refl)  
         then have "
                  ys @ [[e1]\<^sub>E] @ [[Tick]\<^sub>E] = fl2ttobs(fl @\<^sub>\<F>\<^sub>\<L> \<langle>(last fl,Tick)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>)
                  \<and> flt2goodTock fl 
                  \<and> (\<exists>z. FLTick0 Tick z \<and> FL1 z 
                      \<and> {fl2ttobs fl\<^sub>0 |fl\<^sub>0. fl\<^sub>0 \<in> z} \<subseteq> P 
                      \<and> fl @\<^sub>\<F>\<^sub>\<L> \<langle>(last fl,Tick)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L> \<in> z)"
           by blast
         then have "
                  ys @ [[e1]\<^sub>E] @ [[Tick]\<^sub>E] = fl2ttobs(fl @\<^sub>\<F>\<^sub>\<L> \<langle>(last fl,Tick)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>)
                  \<and> flt2goodTock fl 
                  \<and> flt2goodTock (fl @\<^sub>\<F>\<^sub>\<L> \<langle>(last fl,Tick)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>)
                  \<and> (\<exists>z. FLTick0 Tick z \<and> FL1 z 
                      \<and> {fl2ttobs fl\<^sub>0 |fl\<^sub>0. fl\<^sub>0 \<in> z} \<subseteq> P 
                      \<and> fl @\<^sub>\<F>\<^sub>\<L> \<langle>(last fl,Tick)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L> \<in> z)"
           using last_fl flt2goodTock_extend_consFL_last_fl_bullet
           by blast
         then have "
                  \<exists>fl. ys @ [[e1]\<^sub>E] @ [[Tick]\<^sub>E] = fl2ttobs(fl)
                  \<and> flt2goodTock fl 
                  \<and> (\<exists>z. FLTick0 Tick z \<and> FL1 z \<and> {fl2ttobs fl\<^sub>0 |fl\<^sub>0. fl\<^sub>0 \<in> z} \<subseteq> P \<and> fl \<in> z)"
           by blast
         then show ?thesis using Tick e1 e2 by auto
        qed
      next
        case (Ref r2)
        have Tick_in_r2:"Tick \<in> r2"
          using TT4w_healthy  TTick_healthy Ref
          using TTick_def snoc.prems(1) by blast
        then have "ys @ [[e1]\<^sub>E] @ [[r2]\<^sub>R] \<in> P"
          using e1 Ref yys.prems(2) by auto
        then have "[Tick]\<^sub>E \<notin> set (ys @ [[e1]\<^sub>E])" 
          using TTwf_healthy TTwf_concat_prefix_of_ref_set_no_Tick
          using e1 Ref
          by (metis fl ys_e1_x)
        then have Tick_not_in_events_fl: "Tick \<notin> events fl"
          by (simp add: event_not_in_set_of_fl2ttobs_imp_not_in_events fl)
       (* have fl2ttobs_strongFL_subset:"{fl2ttobs fl\<^sub>0|fl\<^sub>0. fl\<^sub>0 \<le>\<^sub>\<F>\<^sub>\<L> (fl @\<^sub>\<F>\<^sub>\<L> \<langle>[{x. x \<notin> r2}]\<^sub>\<F>\<^sub>\<L>\<rangle>\<^sub>\<F>\<^sub>\<L>)} \<subseteq> P"
            apply auto
          using strong_less_eq_fltrace_imp_fl2ttobs_tt
          sledgehammer[debug=true]
          by (metis TT1w_def TT1w_healthy Collect_cong Ref e1 fl fl2ttobs_fl_acceptance last_snoc mem_Collect_eq snoc_eq_iff_butlast subsetI subset_iff yys.prems(2))
        *)
        from fl have fl_e3: "ys @ [[e1]\<^sub>E] @ [[r2]\<^sub>R] = fl2ttobs fl @ [[r2]\<^sub>R]
                  \<and> flt2goodTock fl \<and> (\<exists>x. FLTick0 Tick x \<and> FL1 x \<and> {fl2ttobs fl\<^sub>0 |fl\<^sub>0. fl\<^sub>0 \<in> x} \<subseteq> P \<and> fl \<in> x)"
          using ys_e1_x by auto
        also have "... =
                  (ys @ [[e1]\<^sub>E] @ [[r2]\<^sub>R] = fl2ttobs(fl @\<^sub>\<F>\<^sub>\<L> \<langle>[{x. x \<notin> r2} - {Tick}]\<^sub>\<F>\<^sub>\<L>\<rangle>\<^sub>\<F>\<^sub>\<L>)
                  \<and> flt2goodTock fl \<and> (\<exists>x. FLTick0 Tick x \<and> FL1 x \<and> {fl2ttobs fl\<^sub>0 |fl\<^sub>0. fl\<^sub>0 \<in> x} \<subseteq> P \<and> fl \<in> x))"
          proof -
              from fl have "ys @ [[e1]\<^sub>E] = fl2ttobs fl"
                by auto
              then have "List.last(fl2ttobs fl) = [e1]\<^sub>E"
                by (metis last_snoc)
              then have "fl2ttobs fl @ [[r2]\<^sub>R] = fl2ttobs(fl @\<^sub>\<F>\<^sub>\<L> \<langle>[{x. x \<notin> r2} - {Tick}]\<^sub>\<F>\<^sub>\<L>\<rangle>\<^sub>\<F>\<^sub>\<L>)"
                using fl last_fl fl2ttobs_fl_acceptance Tick_in_r2
              proof -
                have "fl2ttobs fl \<noteq> []"
                  by (metis (no_types) append_is_Nil_conv fl not_Cons_self2)
                then show ?thesis
                  by (simp add: Tick_in_r2 \<open>List.last (fl2ttobs fl) = [e1]\<^sub>E\<close> fl fl2ttobs_fl_acceptance)
                qed
              then show ?thesis using calculation by auto
            qed
         finally have "
                  ys @ [[e1]\<^sub>E] @ [[r2]\<^sub>R] = fl2ttobs(fl @\<^sub>\<F>\<^sub>\<L> \<langle>[{x. x \<notin> r2} - {Tick}]\<^sub>\<F>\<^sub>\<L>\<rangle>\<^sub>\<F>\<^sub>\<L>)
                  \<and> flt2goodTock fl 
                  \<and> (\<exists>x. FLTick0 Tick x \<and> FL1 (x \<union> {fl\<^sub>0. fl\<^sub>0 \<le>\<^sub>\<F>\<^sub>\<L> (fl @\<^sub>\<F>\<^sub>\<L> \<langle>[{x. x \<notin> r2} - {Tick}]\<^sub>\<F>\<^sub>\<L>\<rangle>\<^sub>\<F>\<^sub>\<L>)}) 
                      \<and> {fl2ttobs fl\<^sub>0 |fl\<^sub>0. fl\<^sub>0 \<in> x} \<subseteq> P \<and> fl \<in> x)"
              apply auto using FL1_extends_strong_less_eq_fltrace_acceptance last_fl 
           by fastforce 
         then have "
                  ys @ [[e1]\<^sub>E] @ [[r2]\<^sub>R] = fl2ttobs(fl @\<^sub>\<F>\<^sub>\<L> \<langle>[{x. x \<notin> r2} - {Tick}]\<^sub>\<F>\<^sub>\<L>\<rangle>\<^sub>\<F>\<^sub>\<L>)
                  \<and> flt2goodTock fl 
                  \<and> (\<exists>x. FLTick0 Tick (x \<union> {fl\<^sub>0. fl\<^sub>0 \<le>\<^sub>\<F>\<^sub>\<L> (fl @\<^sub>\<F>\<^sub>\<L> \<langle>[{x. x \<notin> r2} - {Tick}]\<^sub>\<F>\<^sub>\<L>\<rangle>\<^sub>\<F>\<^sub>\<L>)})
                      \<and> FL1 (x \<union> {fl\<^sub>0. fl\<^sub>0 \<le>\<^sub>\<F>\<^sub>\<L> (fl @\<^sub>\<F>\<^sub>\<L> \<langle>[{x. x \<notin> r2}- {Tick}]\<^sub>\<F>\<^sub>\<L>\<rangle>\<^sub>\<F>\<^sub>\<L>)}) 
                      \<and> {fl2ttobs fl\<^sub>0 |fl\<^sub>0. fl\<^sub>0 \<in> x} \<subseteq> P \<and> fl \<in> x)"
            apply auto using FL0Tick_extends_strong_less_eq_fltrace_acceptance last_fl Tick_in_r2 Tick_not_in_events_fl
           by (smt Collect_cong Diff_empty Diff_insert0 FLTick0_def Un_iff amember.simps(2) mem_Collect_eq tickWF_concatFL_acceptance_imp tickWF_prefix_imp)
         then have "
                  ys @ [[e1]\<^sub>E] @ [[r2]\<^sub>R] = fl2ttobs(fl @\<^sub>\<F>\<^sub>\<L> \<langle>[{x. x \<notin> r2} - {Tick}]\<^sub>\<F>\<^sub>\<L>\<rangle>\<^sub>\<F>\<^sub>\<L>)
                  \<and> flt2goodTock fl 
                  \<and> (\<exists>x. FLTick0 Tick (x \<union> {fl\<^sub>0. fl\<^sub>0 \<le>\<^sub>\<F>\<^sub>\<L> (fl @\<^sub>\<F>\<^sub>\<L> \<langle>[{x. x \<notin> r2} - {Tick}]\<^sub>\<F>\<^sub>\<L>\<rangle>\<^sub>\<F>\<^sub>\<L>)})
                      \<and> FL1 (x \<union> {fl\<^sub>0. fl\<^sub>0 \<le>\<^sub>\<F>\<^sub>\<L> (fl @\<^sub>\<F>\<^sub>\<L> \<langle>[{x. x \<notin> r2} - {Tick}]\<^sub>\<F>\<^sub>\<L>\<rangle>\<^sub>\<F>\<^sub>\<L>)}) 
                      \<and> {fl2ttobs fl\<^sub>0 |fl\<^sub>0. fl\<^sub>0 \<in> (x \<union> {fl\<^sub>0. fl\<^sub>0 \<le>\<^sub>\<F>\<^sub>\<L> (fl @\<^sub>\<F>\<^sub>\<L> \<langle>[{x. x \<notin> r2} - {Tick}]\<^sub>\<F>\<^sub>\<L>\<rangle>\<^sub>\<F>\<^sub>\<L>)})} \<subseteq> P \<and> fl \<in> x)"  
         proof -
           have
            "{fl2ttobs fl\<^sub>0|fl\<^sub>0. fl\<^sub>0 \<le>\<^sub>\<F>\<^sub>\<L> (fl @\<^sub>\<F>\<^sub>\<L> \<langle>[{x. x \<notin> r2} - {Tick}]\<^sub>\<F>\<^sub>\<L>\<rangle>\<^sub>\<F>\<^sub>\<L>)} \<subseteq> P"
            apply auto
            using strong_less_eq_fltrace_imp_fl2ttobs_tt
            by (metis (no_types, lifting) TT1w_def TT1w_healthy Ref \<open>ys @ [[e1]\<^sub>E] @ [[r2]\<^sub>R] = fl2ttobs (fl @\<^sub>\<F>\<^sub>\<L> \<langle>[{x. x \<notin> r2} - {Tick}]\<^sub>\<F>\<^sub>\<L>\<rangle>\<^sub>\<F>\<^sub>\<L>) \<and> flt2goodTock fl \<and> (\<exists>x. FLTick0 Tick x \<and> FL1 (x \<union> {fl\<^sub>0. fl\<^sub>0 \<le>\<^sub>\<F>\<^sub>\<L> fl @\<^sub>\<F>\<^sub>\<L> \<langle>[{x. x \<notin> r2} - {Tick}]\<^sub>\<F>\<^sub>\<L>\<rangle>\<^sub>\<F>\<^sub>\<L>}) \<and> {fl2ttobs fl\<^sub>0 |fl\<^sub>0. fl\<^sub>0 \<in> x} \<subseteq> P \<and> fl \<in> x)\<close> e1 fl fl_e3 yys.prems(2))
          then show ?thesis 
            by (smt Un_iff \<open>ys @ [[e1]\<^sub>E] @ [[r2]\<^sub>R] = fl2ttobs (fl @\<^sub>\<F>\<^sub>\<L> \<langle>[{x. x \<notin> r2} - {Tick}]\<^sub>\<F>\<^sub>\<L>\<rangle>\<^sub>\<F>\<^sub>\<L>) \<and> flt2goodTock fl \<and> (\<exists>x. FLTick0 Tick (x \<union> {fl\<^sub>0. fl\<^sub>0 \<le>\<^sub>\<F>\<^sub>\<L> fl @\<^sub>\<F>\<^sub>\<L> \<langle>[{x. x \<notin> r2} - {Tick}]\<^sub>\<F>\<^sub>\<L>\<rangle>\<^sub>\<F>\<^sub>\<L>}) \<and> FL1 (x \<union> {fl\<^sub>0. fl\<^sub>0 \<le>\<^sub>\<F>\<^sub>\<L> fl @\<^sub>\<F>\<^sub>\<L> \<langle>[{x. x \<notin> r2} - {Tick}]\<^sub>\<F>\<^sub>\<L>\<rangle>\<^sub>\<F>\<^sub>\<L>}) \<and> {fl2ttobs fl\<^sub>0 |fl\<^sub>0. fl\<^sub>0 \<in> x} \<subseteq> P \<and> fl \<in> x)\<close> mem_Collect_eq subset_eq)
        qed
        then have "
                  ys @ [[e1]\<^sub>E] @ [[r2]\<^sub>R] = fl2ttobs(fl @\<^sub>\<F>\<^sub>\<L> \<langle>[{x. x \<notin> r2} - {Tick}]\<^sub>\<F>\<^sub>\<L>\<rangle>\<^sub>\<F>\<^sub>\<L>)
                  \<and> flt2goodTock fl 
                  \<and> (\<exists>x. FLTick0 Tick (x \<union> {fl\<^sub>0. fl\<^sub>0 \<le>\<^sub>\<F>\<^sub>\<L> (fl @\<^sub>\<F>\<^sub>\<L> \<langle>[{x. x \<notin> r2} - {Tick}]\<^sub>\<F>\<^sub>\<L>\<rangle>\<^sub>\<F>\<^sub>\<L>)})
                      \<and> FL1 (x \<union> {fl\<^sub>0. fl\<^sub>0 \<le>\<^sub>\<F>\<^sub>\<L> (fl @\<^sub>\<F>\<^sub>\<L> \<langle>[{x. x \<notin> r2} - {Tick}]\<^sub>\<F>\<^sub>\<L>\<rangle>\<^sub>\<F>\<^sub>\<L>)}) 
                      \<and> {fl2ttobs fl\<^sub>0 |fl\<^sub>0. fl\<^sub>0 \<in> (x \<union> {fl\<^sub>0. fl\<^sub>0 \<le>\<^sub>\<F>\<^sub>\<L> (fl @\<^sub>\<F>\<^sub>\<L> \<langle>[{x. x \<notin> r2} - {Tick}]\<^sub>\<F>\<^sub>\<L>\<rangle>\<^sub>\<F>\<^sub>\<L>)})} \<subseteq> P 
                      \<and> fl \<in> x
                      \<and> (fl @\<^sub>\<F>\<^sub>\<L> \<langle>[{x. x \<notin> r2} - {Tick}]\<^sub>\<F>\<^sub>\<L>\<rangle>\<^sub>\<F>\<^sub>\<L>) \<in> (x \<union> {fl\<^sub>0. fl\<^sub>0 \<le>\<^sub>\<F>\<^sub>\<L> (fl @\<^sub>\<F>\<^sub>\<L> \<langle>[{x. x \<notin> r2} - {Tick}]\<^sub>\<F>\<^sub>\<L>\<rangle>\<^sub>\<F>\<^sub>\<L>)}))"  
         by (simp add: strong_less_eq_fltrace_refl)  
        then have "
                  ys @ [[e1]\<^sub>E] @ [[r2]\<^sub>R] = fl2ttobs(fl @\<^sub>\<F>\<^sub>\<L> \<langle>[{x. x \<notin> r2} - {Tick}]\<^sub>\<F>\<^sub>\<L>\<rangle>\<^sub>\<F>\<^sub>\<L>)
                  \<and> flt2goodTock fl 
                  \<and> (\<exists>z. FLTick0 Tick z \<and> FL1 z 
                      \<and> {fl2ttobs fl\<^sub>0 |fl\<^sub>0. fl\<^sub>0 \<in> z} \<subseteq> P 
                      \<and> fl @\<^sub>\<F>\<^sub>\<L> \<langle>[{x. x \<notin> r2} - {Tick}]\<^sub>\<F>\<^sub>\<L>\<rangle>\<^sub>\<F>\<^sub>\<L> \<in> z)"
          by blast
        then have "
                  ys @ [[e1]\<^sub>E] @ [[r2]\<^sub>R] = fl2ttobs(fl @\<^sub>\<F>\<^sub>\<L> \<langle>[{x. x \<notin> r2} - {Tick}]\<^sub>\<F>\<^sub>\<L>\<rangle>\<^sub>\<F>\<^sub>\<L>)
                  \<and> flt2goodTock fl
                  \<and> flt2goodTock (fl @\<^sub>\<F>\<^sub>\<L> \<langle>[{x. x \<notin> r2} - {Tick}]\<^sub>\<F>\<^sub>\<L>\<rangle>\<^sub>\<F>\<^sub>\<L>) 
                  \<and> (\<exists>z. FLTick0 Tick z \<and> FL1 z 
                      \<and> {fl2ttobs fl\<^sub>0 |fl\<^sub>0. fl\<^sub>0 \<in> z} \<subseteq> P 
                      \<and> fl @\<^sub>\<F>\<^sub>\<L> \<langle>[{x. x \<notin> r2} - {Tick}]\<^sub>\<F>\<^sub>\<L>\<rangle>\<^sub>\<F>\<^sub>\<L> \<in> z)"
          using flt2goodTock_extend_consFL_acceptance by blast
        then have "
                  \<exists>fl. ys @ [[e1]\<^sub>E] @ [[r2]\<^sub>R] = fl2ttobs(fl)
                  \<and> flt2goodTock fl
                  \<and> (\<exists>z. FLTick0 Tick z \<and> FL1 z 
                      \<and> {fl2ttobs fl\<^sub>0 |fl\<^sub>0. fl\<^sub>0 \<in> z} \<subseteq> P 
                      \<and> fl \<in> z)"
          by blast
        then show ?thesis using Ref e1 by auto
        qed
    qed
  qed
qed

lemma subset_fl2ttm_ttm2fl:
  assumes 
          TTwf_healthy: "TTwf P" 
      and TT1w_healthy: "TT1w P"
      and ttWFx_healthy:  "ttWFx P"
      and TTick_healthy: "TTick P"
      and TT4w_healthy: "TT4w P"
  shows "P \<subseteq> fl2ttm(ttm2fl(P))"
  unfolding ttm2fl_def fl2ttm_def apply auto
  using assms TTwf_1c_3_imp_fl2ttobs_FL1 by blast

lemma fl2ttm_ttm2fl_bij:
  assumes 
          TTwf_healthy: "TTwf P" 
      and TT1w_healthy: "TT1w P"
      and ttWFx_healthy:  "ttWFx P"
      and TTick_healthy: "TTick P"
      and TT4w_healthy: "TT4w P"
    shows "P = fl2ttm(ttm2fl(P))"
  using assms
  by (simp add: fl2ttm_ttm2fl_refines subset_antisym subset_fl2ttm_ttm2fl)

lemma fl2ttm_mono:
  assumes "P \<subseteq> Q"
  shows "fl2ttm(P) \<subseteq> fl2ttm(Q)"
  using assms unfolding fl2ttm_def by auto

lemma
  assumes TTwf_healthy: "TTwf P" 
  shows "\<forall>x. x \<in> ttm2fl(P) \<longrightarrow> tickWF Tick x"
  using assms unfolding ttm2fl_def apply auto
  oops

(* flt2goodAcceptance sufficient? *)

lemma tickWF_last_bullet_imp_Tick_notin:
  assumes "tickWF Tick (xs &\<^sub>\<F>\<^sub>\<L> \<langle>x\<rangle>\<^sub>\<F>\<^sub>\<L>)"
          "Finite_Linear_Model.last xs = \<bullet>"
  shows   "Tick \<notin>\<^sub>\<F>\<^sub>\<L> x"
  using assms apply(induct xs, auto)
  apply (case_tac x1a, auto, case_tac b, auto)
  by (case_tac b, auto)

lemma FLTick0_Tick_FL1_concat_ref_Tick_in:
  assumes "FLTick0 Tick P" "t @ [[X]\<^sub>R] = fl2ttobs fl" "fl \<in> P" "flt2goodTock fl"
  shows "Tick \<in> X"
  using assms proof (induct fl arbitrary:t X rule:fltrace_induct)
  case 1
  then show ?case by auto
next
  case (2 x xs)
  then show ?case
  proof (cases "last xs = \<bullet>")
    case True
    then have "t @ [[X]\<^sub>R] = fl2ttobs (xs) @ fl2ttobs(\<langle>x\<rangle>\<^sub>\<F>\<^sub>\<L>)"
      using 2
      by (metis Finite_Linear_Model.last.simps(1) acceptance.distinct(1) fl2ttobs_last_fl_not_bullet_dist_list_cons last_bullet_butlast_last last_bullet_then_last_cons last_fl2ttobs_eq_ref_imp_last snoc_eq_iff_butlast)
    then have X_x:"[[X]\<^sub>R] = fl2ttobs(\<langle>x\<rangle>\<^sub>\<F>\<^sub>\<L>)"
      by (metis "2.prems"(2) Nil_is_append_conv True acceptance.distinct(1) bullet_right_zero2 fl2ttobs.simps(1) last_fl2ttobs_eq_ref_imp_last last_snoc)
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
    then have "t @ [[X]\<^sub>R] = fl2ttobs (xs)"
      using 2
      by (simp add: concat_FL_last_not_bullet_absorb)
    then have X_x:"[[X]\<^sub>R] = fl2ttobs(\<langle>last xs\<rangle>\<^sub>\<F>\<^sub>\<L>)"
      using "2.prems"(4) False concat_FL_last_not_bullet_absorb fl2ttobs_last_fl_not_bullet_dist_list_cons by fastforce
    then show ?thesis
      by (metis "2.hyps" "2.prems"(3) "2.prems"(4) False \<open>t @ [[X]\<^sub>R] = fl2ttobs xs\<close> assms(1) concat_FL_last_not_bullet_absorb)
  qed
next
  case (3 x xs)
  then show ?case
    proof (cases "last xs = \<bullet>")
      case True
      then show ?thesis
        by (metis "3.prems"(2) List.last.simps acceptance.distinct(1) append_is_Nil_conv last_appendR last_cons_bullet_iff last_fl2ttobs_eq_ref_imp_last list.simps(3))
    next
      case False
      then have "t @ [[X]\<^sub>R] = fl2ttobs (xs)"
      using 3
      by (simp add: concat_FL_last_not_bullet_absorb)
    then have X_x:"[[X]\<^sub>R] = fl2ttobs(\<langle>last xs\<rangle>\<^sub>\<F>\<^sub>\<L>)"
      using "3.prems"(4) False concat_FL_last_not_bullet_absorb fl2ttobs_last_fl_not_bullet_dist_list_cons by fastforce
    then show ?thesis
      by (metis "3.hyps" "3.prems"(4) "3.prems"(3) \<open>t @ [[X]\<^sub>R] = fl2ttobs xs\<close> assms(1) concat_FL_last_not_bullet_absorb fl2ttobs.simps(1) list.distinct(1))
    qed
  qed

lemma FL1_imp_disj:
  assumes "FL1(P)" "FL1(Q)"
  shows "FL1(P \<union> Q)"
  unfolding FL1_def apply auto
  using FL1_def assms by blast+

subsection \<open> Closure of ttm2fl under healthiness conditions of FL. \<close>

lemma FL0_ttm2fl:
  assumes "TT0 P" "TT1w P"
  shows "FL0 (ttm2fl P)"
  using assms unfolding ttm2fl_def FL0_def apply auto
  apply (rule exI[where x="{\<langle>\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>}"], auto)
  unfolding FL1_def apply auto
  unfolding FLTick0_def apply auto
   apply (metis bullet_left_zero2 dual_order.antisym x_le_x_concat2)
  unfolding fl2ttm_def apply auto
  using TT0_TT1w_empty by blast

lemma prefix_ttm2fl_FL1:
  assumes "t \<in> ttm2fl P"
          "s \<le> t"
    shows "s \<in> ttm2fl P"
  using assms unfolding ttm2fl_def apply auto
  using FL1_def by blast

lemma FL1_ttm2fl:
  "FL1 (ttm2fl P)"
  unfolding FL1_def apply safe
  using prefix_ttm2fl_FL1 by blast

lemma FLTick0_Tick_ttm2fl:
  assumes "TTwf P"
  shows "FLTick0 Tick (ttm2fl P)"
  using assms unfolding ttm2fl_def FLTick0_def TTwf_def by auto

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

(* TODO: Move the following *)
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

lemma prefixFL_same_length_imp:
  assumes "length xs = length ys" "last ys = \<bullet>" "last xs = \<bullet>" 
          "xs &\<^sub>\<F>\<^sub>\<L> x \<le> ys &\<^sub>\<F>\<^sub>\<L> y"
  shows "x \<le> y"
  using assms by (induct xs ys rule:less_eq_fltrace.induct, auto)

lemma prefixFL_same_length_imp_1:
  assumes "xs \<le> ys" "a \<le> b" "last ys = \<bullet>" "last xs = \<bullet>" "length xs = length ys"
  shows "xs &\<^sub>\<F>\<^sub>\<L> a \<le> ys &\<^sub>\<F>\<^sub>\<L> b"
  using assms by (induct xs ys arbitrary:a b rule:less_eq_fltrace.induct, auto)

lemma prefixFL_same_length_imp_2:
  assumes "length xs = length ys" "last ys = \<bullet>" "last xs = \<bullet>" 
          "xs &\<^sub>\<F>\<^sub>\<L> a \<le> ys &\<^sub>\<F>\<^sub>\<L> b"
        shows "xs \<le> ys"
  using assms by (induct xs ys arbitrary:a b rule:less_eq_fltrace.induct, auto)

lemma fl2ttobs_for_FL2_imp:
  assumes "fl2ttobs (\<beta> &\<^sub>\<F>\<^sub>\<L> \<langle>A\<rangle>\<^sub>\<F>\<^sub>\<L>) \<in> P" "a \<in>\<^sub>\<F>\<^sub>\<L> A" "TTM1 P" "TTM2 P" "TT1w P"
  shows "fl2ttobs (\<beta> &\<^sub>\<F>\<^sub>\<L> \<langle>(A,a)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>) \<in> P \<and> fl2ttobs (\<beta> &\<^sub>\<F>\<^sub>\<L> \<langle>(\<bullet>,a)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>) \<in> P"
  using assms (* NOTE: lhs conjunct does not require TT1w *)
proof (cases "last \<beta> = \<bullet>")
  case last_B_bullet:True
  then show ?thesis
  proof (cases "flt2goodTock \<beta>")
    case True
    then have "fl2ttobs (\<beta>) @ fl2ttobs (\<langle>A\<rangle>\<^sub>\<F>\<^sub>\<L>) \<in> P"
      by (metis (no_types, lifting) Finite_Linear_Model.last.simps(1) acceptance.simps(3) amember.elims(2) assms(1) assms(2) butlast_last_FL fl2ttobs_last_fl_not_bullet_dist_list_cons flt2goodTock_extend_consFL_acceptance last_B_bullet last_bullet_butlast_last last_bullet_then_last_cons)
    then obtain R where R:"R = {x. x \<notin>\<^sub>\<F>\<^sub>\<L> A}"
      using assms(2) by force
    then have "a \<notin> R"
      using assms(2) by blast
    then have "fl2ttobs (\<beta>) @ [[R]\<^sub>R] \<in> P"
      using R by (metis \<open>fl2ttobs \<beta> @ fl2ttobs \<langle>A\<rangle>\<^sub>\<F>\<^sub>\<L> \<in> P\<close> amember.simps(1) assms(2) fl2ttobs.simps(1))
    then show ?thesis
    proof (cases a)
      case (Event x1)
      then have "fl2ttobs (\<beta>) @ [[a]\<^sub>E] \<in> P"
        using assms
        using TTM1_def \<open>a \<notin> R\<close> \<open>fl2ttobs \<beta> @ [[R]\<^sub>R] \<in> P\<close> by blast
      then show ?thesis
        using Event True assms(2) fl2ttobs_acceptance_cons_eq_list_cons last_B_bullet by fastforce
    next
      case Tock
      then have fl2ttobs_bullet:"fl2ttobs (\<beta> &\<^sub>\<F>\<^sub>\<L> \<langle>(\<bullet>,a)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>) = fl2ttobs (\<beta>)"
        by (simp add: True fl2ttobs_acceptance_cons_eq_list_cons last_B_bullet)
      then have fl2ttobs_R_tock:"fl2ttobs (\<beta>) @ [[R]\<^sub>R,[a]\<^sub>E] \<in> P"
        using Tock TTM2_def \<open>a \<notin> R\<close> \<open>fl2ttobs \<beta> @ [[R]\<^sub>R] \<in> P\<close> assms(4) by blast
      then have c1:"fl2ttobs (\<beta> &\<^sub>\<F>\<^sub>\<L> \<langle>(A,a)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>) \<in> P"
        using R Tock True amember.simps(1) assms(2) fl2ttobs_acceptance_cons_eq_list_cons last_B_bullet by fastforce
      
      have c2:"fl2ttobs (\<beta> &\<^sub>\<F>\<^sub>\<L> \<langle>(\<bullet>,a)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>) \<in> P"
        using TT1w_prefix_concat_in assms fl2ttobs_bullet fl2ttobs_R_tock by auto
      then show ?thesis using c1 by auto
    next
      case Tick
      then have "fl2ttobs (\<beta>) @ [[a]\<^sub>E] \<in> P"
        using TTM1_def \<open>a \<notin> R\<close> \<open>fl2ttobs \<beta> @ [[R]\<^sub>R] \<in> P\<close> assms(3) by blast
      then show ?thesis
        using Tick True assms(2) fl2ttobs_acceptance_cons_eq_list_cons last_B_bullet by fastforce
    qed  
  next
    case False
    then show ?thesis
      using assms(1) fl2ttobs_not_flt2goodTock_imp_fl2ttobs_eq_consFL_any by fastforce
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

lemma TT1w_TTM1_TTM2_strong_less_eq_fltrace:
  assumes "a \<in>\<^sub>\<F>\<^sub>\<L> A" "TT1w P" "TTM1 P" "TTM2 P"
          "FLTick0 Tick x"
          "FL1 x" "{fl2ttobs fl |fl. fl \<in> x} \<subseteq> P" "\<beta> &\<^sub>\<F>\<^sub>\<L> \<langle>A\<rangle>\<^sub>\<F>\<^sub>\<L> \<in> x" 
          "fl \<le>\<^sub>\<F>\<^sub>\<L> \<beta> &\<^sub>\<F>\<^sub>\<L> \<langle>(A,a)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>" 
        shows "fl2ttobs fl \<in> P"
  using assms proof(induct fl arbitrary:\<beta> A a x rule:fltrace_induct)
case 1
  then show ?case by (metis (mono_tags, lifting) CollectI FL0_FL1_bullet_in_so fl2ttobs.simps(1) in_mono)
next
  case (2 z zs)
  then have "fl2ttobs (\<beta> &\<^sub>\<F>\<^sub>\<L> \<langle>A\<rangle>\<^sub>\<F>\<^sub>\<L>) \<in> P"
    by blast
  then have fl2ttobs_B_Aa:
        "fl2ttobs (\<beta> &\<^sub>\<F>\<^sub>\<L> \<langle>(A,a)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>) \<in> P"
        "fl2ttobs (\<beta> &\<^sub>\<F>\<^sub>\<L> \<langle>(\<bullet>,a)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>) \<in> P"
    using fl2ttobs_for_FL2_imp "2.prems"(1) assms(2) assms(3) assms(4) by blast+
  then have "fl2ttobs (zs &\<^sub>\<F>\<^sub>\<L> \<langle>z\<rangle>\<^sub>\<F>\<^sub>\<L>) \<le>\<^sub>C fl2ttobs (\<beta> &\<^sub>\<F>\<^sub>\<L> \<langle>(A,a)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>)"
    using "2.prems"(9) strong_less_eq_fltrace_imp_fl2ttobs_tt by blast
  then have "fl2ttobs (zs &\<^sub>\<F>\<^sub>\<L> \<langle>z\<rangle>\<^sub>\<F>\<^sub>\<L>) \<in> P"
    using assms fl2ttobs_B_Aa TT1w_def by blast
  then show ?case by auto
next
  case (3 z zs)
  then have "fl2ttobs (\<beta> &\<^sub>\<F>\<^sub>\<L> \<langle>A\<rangle>\<^sub>\<F>\<^sub>\<L>) \<in> P"
    by blast
  then have fl2ttobs_B_Aa:
        "fl2ttobs (\<beta> &\<^sub>\<F>\<^sub>\<L> \<langle>(A,a)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>) \<in> P"
        "fl2ttobs (\<beta> &\<^sub>\<F>\<^sub>\<L> \<langle>(\<bullet>,a)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>) \<in> P"
    using fl2ttobs_for_FL2_imp "3.prems"(1) assms(2) assms(3) assms(4) by blast+
  then have "fl2ttobs (zs &\<^sub>\<F>\<^sub>\<L> \<langle>z,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>) \<le>\<^sub>C fl2ttobs (\<beta> &\<^sub>\<F>\<^sub>\<L> \<langle>(A,a)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>)"
    using "3.prems"(9) strong_less_eq_fltrace_imp_fl2ttobs_tt by blast
  then have "fl2ttobs (zs &\<^sub>\<F>\<^sub>\<L> \<langle>z,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>) \<in> P"
    using assms fl2ttobs_B_Aa TT1w_def by blast
  then show ?case .
qed
  
lemma FL2_ttm2fl:
  assumes "TTM1 P" "TTM2 P" "TT1w P"
  shows "FL2 (ttm2fl P)"
  using assms unfolding ttm2fl_def FL2_def fl2ttm_def apply auto
  apply (rule_tac x="x \<union> {s. s \<le>\<^sub>\<F>\<^sub>\<L> \<beta> &\<^sub>\<F>\<^sub>\<L> \<langle>(A,a)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>}" in exI, auto)
  apply (metis (mono_tags, lifting) FLTick0_def FLTick0_dist_union mem_Collect_eq tickWF_acceptance_imp_tickWF_consFL tickWF_prefix_imp)
  apply (simp add: FL1_extends_strong_less_eq_consFL)
  using TT1w_TTM1_TTM2_strong_less_eq_fltrace
   apply blast
  using strong_less_eq_fltrace_refl by blast

lemma FL_ttm2fl_closed:
  assumes "TT0 P" "TT1w P" "TTM1 P" "TTM2 P" "TTM3 P"
  shows "FL0(ttm2fl(P))" "FL1(ttm2fl(P))" "FL2(ttm2fl(P))" "FL3(ttm2fl(P))"
     apply (simp add: FL0_ttm2fl assms(1) assms(2))
    apply (simp add:FL1_ttm2fl)
   apply (simp add: FL2_ttm2fl assms(2) assms(3) assms(4))
  by (metis (no_types, lifting) FLTick0_def mem_Collect_eq mem_simps(9) ttm2fl_def)

subsection \<open> Closure of fl2ttm under healthiness conditions of maximal Tick-Tock. \<close>

lemma TTick_fl2ttm:
  assumes "FL0 P" "FL1 P" "FLTick0 Tick P"
  shows "TTick (fl2ttm P)"
proof -
  have "TTick (fl2ttm P) = TTick({fl2ttobs fl|fl. fl \<in> P \<and> flt2goodTock fl} \<union> {[]})"
    using assms
    by (simp add: fl2ttm_FL0_FL1_flt2goodTock)
  also have "... = TTick({fl2ttobs fl|fl. fl \<in> P \<and> flt2goodTock fl})"
    using TTick_dist_empty_trace by auto
  also have "... = True"
    unfolding TTick_def fl2ttm_def apply auto
    using assms FLTick0_Tick_FL1_concat_ref_Tick_in by metis
  finally show ?thesis by auto
qed

lemma tickWF_imp_TTickTrace_fl2ttobs:
  assumes "tickWF Tick fl"
  shows "TTickTrace (fl2ttobs fl)"
  using assms apply (induct fl rule:fl2ttobs.induct, auto)
   apply (case_tac A, auto, case_tac a, auto, case_tac b, auto)
  by (case_tac A, auto, case_tac b, auto)

lemma TTM3_fl2ttm:
  assumes "FL0 P" "FL1 P" "FLTick0 Tick P"
  shows "TTM3 (fl2ttm P)"
proof -
  have "TTM3 (fl2ttm P) = TTM3({fl2ttobs fl|fl. fl \<in> P \<and> flt2goodTock fl} \<union> {[]})"
    using assms
    by (simp add: fl2ttm_FL0_FL1_flt2goodTock)
  also have "... = TTM3({fl2ttobs fl|fl. fl \<in> P \<and> flt2goodTock fl})"
    using TTM3_dist_empty_trace by auto
  also have "... = True"
    unfolding TTM3_def fl2ttm_def apply auto
    using assms tickWF_imp_TTickTrace_fl2ttobs
    by (metis FLTick0_def)
  finally show ?thesis by auto
qed

lemma FL2_imp_TTM1_part:
  assumes "FL2 P" "e \<notin> X" "e \<noteq> Tock" "\<rho> @ [[X]\<^sub>R] = fl2ttobs fl" "fl \<in> P" "flt2goodTock fl"
  shows "\<exists>fl. \<rho> @ [[e]\<^sub>E] = fl2ttobs fl \<and> fl \<in> P \<and> flt2goodTock fl"
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
        by (metis "2.prems"(4) Nil_is_append_conv True acceptance.distinct(1) bullet_right_zero2 last_fl2ttobs_eq_ref_imp_last last_snoc not_Cons_self2)
    next
      case (acset x2)
      then have flt2goodTock_xs: "flt2goodTock (xs)"
        using 2
        by (metis True fl2ttobs_not_flt2goodTock_imp_fl2ttobs_eq_consFL_any last_cons_acceptance_not_bullet last_fl2ttobs_eq_ref_imp_last snoc_eq_iff_butlast)
      then have "fl2ttobs (xs &\<^sub>\<F>\<^sub>\<L> \<langle>x\<rangle>\<^sub>\<F>\<^sub>\<L>) = fl2ttobs(xs) @ fl2ttobs(\<langle>x\<rangle>\<^sub>\<F>\<^sub>\<L>)"
        using 2 True
        by (metis Finite_Linear_Model.last.simps(1) append_Nil2 bullet_right_zero2 fl2ttobs.simps(1) fl2ttobs_last_fl_not_bullet_dist_list_cons last_bullet_butlast_last last_bullet_then_last_cons)
      then have "\<rho> @ [[X]\<^sub>R] = fl2ttobs(xs) @ fl2ttobs(\<langle>x\<rangle>\<^sub>\<F>\<^sub>\<L>)"
        using 2 by auto
      then have "\<rho> = fl2ttobs(xs)" "[[X]\<^sub>R] = fl2ttobs(\<langle>x\<rangle>\<^sub>\<F>\<^sub>\<L>)"
         apply (metis List.last.simps Nil_is_append_conv True acceptance.distinct(1) append_Nil2 butlast_snoc fl2ttobs.simps(1) last_appendR last_fl2ttobs_eq_ref_imp_last)
        by (metis "2.prems"(4) Nil_is_append_conv True \<open>\<rho> @ [[X]\<^sub>R] = fl2ttobs xs @ fl2ttobs \<langle>x\<rangle>\<^sub>\<F>\<^sub>\<L>\<close> acceptance.distinct(1) bullet_right_zero2 fl2ttobs.simps(1) last_fl2ttobs_eq_ref_imp_last last_snoc)

      have \<rho>_e:"\<rho> @ [[e]\<^sub>E] = fl2ttobs (xs &\<^sub>\<F>\<^sub>\<L> \<langle>([x2]\<^sub>\<F>\<^sub>\<L>,e)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>)"
      proof -
        have "fl2ttobs (xs &\<^sub>\<F>\<^sub>\<L> \<langle>([x2]\<^sub>\<F>\<^sub>\<L>,e)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>) = fl2ttobs(xs) @ fl2ttobs(\<langle>([x2]\<^sub>\<F>\<^sub>\<L>,e)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>)"
          using assms
          by (metis "2.prems"(4) True \<open>\<rho> = fl2ttobs xs\<close> \<open>fl2ttobs (xs &\<^sub>\<F>\<^sub>\<L> \<langle>x\<rangle>\<^sub>\<F>\<^sub>\<L>) = fl2ttobs xs @ fl2ttobs \<langle>x\<rangle>\<^sub>\<F>\<^sub>\<L>\<close> acset append_self_conv fl2ttobs_acceptance_cons_eq_list_cons fl2ttobs_not_flt2goodTock_imp_fl2ttobs_eq_consFL_any list.simps(3))
        also have "... = fl2ttobs(xs) @ [[e]\<^sub>E]"
          using "2.prems"(2) "2.prems"(3) \<open>[[X]\<^sub>R] = fl2ttobs \<langle>x\<rangle>\<^sub>\<F>\<^sub>\<L>\<close> acset by auto
        then show ?thesis
          by (simp add: \<open>\<rho> = fl2ttobs xs\<close> calculation)
      qed

      have "xs &\<^sub>\<F>\<^sub>\<L> \<langle>([x2]\<^sub>\<F>\<^sub>\<L>,e)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L> \<in> P"
        by (metis "2.prems"(2) "2.prems"(5) CollectI FL2_def List.last.simps \<open>[[X]\<^sub>R] = fl2ttobs \<langle>x\<rangle>\<^sub>\<F>\<^sub>\<L>\<close> acset assms(1) ttobs.inject(2) fl2ttobs.simps(1) list.simps(3))
      then have "\<rho> @ [[e]\<^sub>E] = fl2ttobs (xs &\<^sub>\<F>\<^sub>\<L> \<langle>([x2]\<^sub>\<F>\<^sub>\<L>,e)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>) \<and> xs &\<^sub>\<F>\<^sub>\<L> \<langle>([x2]\<^sub>\<F>\<^sub>\<L>,e)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L> \<in> P"
        using \<rho>_e
        by blast
      then have "\<rho> @ [[e]\<^sub>E] = fl2ttobs (xs &\<^sub>\<F>\<^sub>\<L> \<langle>([x2]\<^sub>\<F>\<^sub>\<L>,e)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>) \<and> xs &\<^sub>\<F>\<^sub>\<L> \<langle>([x2]\<^sub>\<F>\<^sub>\<L>,e)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L> \<in> P 
                              \<and> flt2goodTock (xs &\<^sub>\<F>\<^sub>\<L> \<langle>([x2]\<^sub>\<F>\<^sub>\<L>,e)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>)"
        using flt2goodTock_xs 2 flt2goodTock_consFL_imp
        by (metis CollectI \<open>[[X]\<^sub>R] = fl2ttobs \<langle>x\<rangle>\<^sub>\<F>\<^sub>\<L>\<close> acset ttobs.inject(2) fl2ttobs.simps(1) last_snoc not_Cons_self2)
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
        by (metis "3.prems"(4) acceptance.distinct(1) last_cons_bullet_iff last_fl2ttobs_eq_ref_imp_last snoc_eq_iff_butlast)
    next
      case False
      then have flt2goodTock_xs:"flt2goodTock (xs)"
        using "3.prems"(6) concat_FL_last_not_bullet_absorb by fastforce
      have "[[X]\<^sub>R] = fl2ttobs(\<langle>last xs\<rangle>\<^sub>\<F>\<^sub>\<L>)"
        using False "3.prems"(4) "3.prems"(6) concat_FL_last_not_bullet_absorb fl2ttobs_last_fl_not_bullet_dist_list_cons by fastforce
      have "xs \<in> P"
        using 3 False
        by (metis concat_FL_last_not_bullet_absorb)
      then have "butlast xs &\<^sub>\<F>\<^sub>\<L> \<langle>last xs\<rangle>\<^sub>\<F>\<^sub>\<L> \<in> P"
        by (simp add: butlast_last_cons2_FL)
      then have xs_e:"butlast xs &\<^sub>\<F>\<^sub>\<L> \<langle>(last xs,e)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L> \<in> P"
        by (metis "3.prems"(2) CollectI FL2_def False List.last.simps \<open>[[X]\<^sub>R] = fl2ttobs \<langle>Finite_Linear_Model.last xs\<rangle>\<^sub>\<F>\<^sub>\<L>\<close> assms(1) ttobs.inject(2) fl2ttobs.simps(1))
      then have "\<rho> @ [[e]\<^sub>E] = fl2ttobs(butlast xs &\<^sub>\<F>\<^sub>\<L> \<langle>(last xs,e)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>)"
        by (metis (no_types, lifting) "3.prems"(2) "3.prems"(3) "3.prems"(4) "3.prems"(6) CollectI False acceptance_event butlast_snoc concat_FL_last_not_bullet_absorb ttobs.inject(2) fl2ttobs.simps(1) fl2ttobs.simps(2) fl2ttobs_butlast_cons_eq_list_cons fl2ttobs_last_fl_not_bullet_dist_list_cons last_snoc)
      then have "\<rho> @ [[e]\<^sub>E] = fl2ttobs(butlast xs &\<^sub>\<F>\<^sub>\<L> \<langle>(last xs,e)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>) \<and> butlast xs &\<^sub>\<F>\<^sub>\<L> \<langle>(last xs,e)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L> \<in> P"
        using xs_e by auto
      then have "\<rho> @ [[e]\<^sub>E] = fl2ttobs(butlast xs &\<^sub>\<F>\<^sub>\<L> \<langle>(last xs,e)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>) 
                              \<and> butlast xs &\<^sub>\<F>\<^sub>\<L> \<langle>(last xs,e)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L> \<in> P
                              \<and> flt2goodTock (butlast xs &\<^sub>\<F>\<^sub>\<L> \<langle>(last xs,e)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>)"
        using flt2goodTock_xs
        by (metis (no_types, lifting) "3.prems"(2) "3.prems"(3) "3.prems"(4) CollectI False Finite_Linear_Model.last.simps(1) List.last.simps Nil_is_append_conv \<open>[[X]\<^sub>R] = fl2ttobs \<langle>Finite_Linear_Model.last xs\<rangle>\<^sub>\<F>\<^sub>\<L>\<close> \<open>\<rho> @ [[e]\<^sub>E] = fl2ttobs (Finite_Linear_Model.butlast xs &\<^sub>\<F>\<^sub>\<L> \<langle>(Finite_Linear_Model.last xs,e)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>)\<close> append_self_conv butlast_last_cons2_FL concat_FL_last_not_bullet_absorb ttobs.inject(2) fl2ttobs.simps(1) fl2ttobs_last_fl_not_bullet_dist_list_cons fl2ttobs_not_flt2goodTock_imp_fl2ttobs_eq_consFL_any flt2goodTock_consFL_imp last_fl2ttobs_eq_ref_imp_last last_snoc list.inject mem_Collect_eq not_Cons_self2 xs_e)
      then show ?thesis by blast
    qed
qed

lemma FL2_imp_TTM2_part:
  assumes "FL2 P" "Tock \<notin> X" "\<rho> @ [[X]\<^sub>R] = fl2ttobs fl" "fl \<in> P" "flt2goodTock fl"
  shows "\<exists>fl. \<rho> @ [[X]\<^sub>R, [Tock]\<^sub>E] = fl2ttobs fl \<and> fl \<in> P \<and> flt2goodTock fl"
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
        by (metis "2.prems"(3) True acceptance.distinct(1) bullet_right_zero2 last_fl2ttobs_eq_ref_imp_last snoc_eq_iff_butlast)
    next
      case (acset x2)
      then have flt2goodTock_xs: "flt2goodTock (xs)"
        using 2
        by (metis True fl2ttobs_not_flt2goodTock_imp_fl2ttobs_eq_consFL_any last_cons_acceptance_not_bullet last_fl2ttobs_eq_ref_imp_last snoc_eq_iff_butlast)
      then have "fl2ttobs (xs &\<^sub>\<F>\<^sub>\<L> \<langle>x\<rangle>\<^sub>\<F>\<^sub>\<L>) = fl2ttobs(xs) @ fl2ttobs(\<langle>x\<rangle>\<^sub>\<F>\<^sub>\<L>)"
        using 2 True
        by (metis Finite_Linear_Model.last.simps(1) append_Nil2 bullet_right_zero2 fl2ttobs.simps(1) fl2ttobs_last_fl_not_bullet_dist_list_cons last_bullet_butlast_last last_bullet_then_last_cons)
      then have "\<rho> @ [[X]\<^sub>R] = fl2ttobs(xs) @ fl2ttobs(\<langle>x\<rangle>\<^sub>\<F>\<^sub>\<L>)"
        using 2 by auto
      then have "\<rho> = fl2ttobs(xs)" "[[X]\<^sub>R] = fl2ttobs(\<langle>x\<rangle>\<^sub>\<F>\<^sub>\<L>)"
         apply (metis List.last.simps Nil_is_append_conv True acceptance.distinct(1) append_Nil2 butlast_snoc fl2ttobs.simps(1) last_appendR last_fl2ttobs_eq_ref_imp_last)
        using \<open>\<rho> @ [[X]\<^sub>R] = fl2ttobs xs @ fl2ttobs \<langle>x\<rangle>\<^sub>\<F>\<^sub>\<L>\<close> acset by auto
 
      have \<rho>_e:"\<rho> @ [[{x. x \<notin> x2}]\<^sub>R,[Tock]\<^sub>E] = fl2ttobs (xs &\<^sub>\<F>\<^sub>\<L> \<langle>([x2]\<^sub>\<F>\<^sub>\<L>,Tock)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>)"
      proof -
        have "fl2ttobs (xs &\<^sub>\<F>\<^sub>\<L> \<langle>([x2]\<^sub>\<F>\<^sub>\<L>,Tock)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>) = fl2ttobs(xs) @ fl2ttobs(\<langle>([x2]\<^sub>\<F>\<^sub>\<L>,Tock)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>)"
          using assms True fl2ttobs_acceptance_cons_eq_list_cons flt2goodTock_xs by blast
        also have "... = fl2ttobs(xs) @ [[{x. x \<notin> x2}]\<^sub>R,[Tock]\<^sub>E]"
          using "2.prems"(2) "2.prems"(3) \<open>[[X]\<^sub>R] = fl2ttobs \<langle>x\<rangle>\<^sub>\<F>\<^sub>\<L>\<close> acset by auto
        then show ?thesis
          by (simp add: \<open>\<rho> = fl2ttobs xs\<close> calculation)
      qed

      have "xs &\<^sub>\<F>\<^sub>\<L> \<langle>([x2]\<^sub>\<F>\<^sub>\<L>,Tock)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L> \<in> P"
        by (metis "2.prems"(2) "2.prems"(4) CollectI FL2_def \<open>[[X]\<^sub>R] = fl2ttobs \<langle>x\<rangle>\<^sub>\<F>\<^sub>\<L>\<close> acceptance.simps(3) acset assms(1) ttobs.inject(2) fl2ttobs.simps(1) list.inject)
      then have "\<rho> @ [[{x. x \<notin> x2}]\<^sub>R,[Tock]\<^sub>E] = fl2ttobs (xs &\<^sub>\<F>\<^sub>\<L> \<langle>([x2]\<^sub>\<F>\<^sub>\<L>,Tock)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>) \<and> xs &\<^sub>\<F>\<^sub>\<L> \<langle>([x2]\<^sub>\<F>\<^sub>\<L>,Tock)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L> \<in> P"
        using \<rho>_e
        by blast
      then have "\<rho> @ [[{x. x \<notin> x2}]\<^sub>R,[Tock]\<^sub>E] = fl2ttobs (xs &\<^sub>\<F>\<^sub>\<L> \<langle>([x2]\<^sub>\<F>\<^sub>\<L>,Tock)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>) \<and> xs &\<^sub>\<F>\<^sub>\<L> \<langle>([x2]\<^sub>\<F>\<^sub>\<L>,Tock)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L> \<in> P 
                              \<and> flt2goodTock (xs &\<^sub>\<F>\<^sub>\<L> \<langle>([x2]\<^sub>\<F>\<^sub>\<L>,Tock)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>)"
        using flt2goodTock_xs 2 flt2goodTock_consFL_imp
        by (metis True \<open>[[X]\<^sub>R] = fl2ttobs \<langle>x\<rangle>\<^sub>\<F>\<^sub>\<L>\<close> acceptance.distinct(1) acset ttobs.inject(2) fl2ttobs.simps(1) flt2goodTock_extend_consFL_last_e' fltrace_concat.simps(3) last_bullet_concatmix list.inject mem_Collect_eq)
      then show ?thesis
        by (metis (no_types, lifting) "2.prems"(2) Cons_eq_append_conv Finite_Linear_Model.butlast.simps(1) Finite_Linear_Model.last.simps(1) True \<open>[[X]\<^sub>R] = fl2ttobs \<langle>x\<rangle>\<^sub>\<F>\<^sub>\<L>\<close> \<open>\<rho> = fl2ttobs xs\<close> acceptance.distinct(1) acset ttobs.inject(2) fl_cons_acceptance_consFL fl2ttobs.simps(1) fl2ttobs_acceptance_cons_eq_list_cons fl2ttobs_last_tock flt2goodTock.simps(1) flt2goodTock_xs fltrace_concat2.simps(3) list.inject mem_Collect_eq)
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
        by (metis "3.prems"(3) acceptance.distinct(1) last_cons_bullet_iff last_fl2ttobs_eq_ref_imp_last snoc_eq_iff_butlast)
   next
      case False
      then have flt2goodTock_xs:"flt2goodTock (xs)"
        using "3.prems"(5) concat_FL_last_not_bullet_absorb by force
      have "[[X]\<^sub>R] = fl2ttobs(\<langle>last xs\<rangle>\<^sub>\<F>\<^sub>\<L>)"
        using "3.prems"(3) False concat_FL_last_not_bullet_absorb fl2ttobs_last_fl_not_bullet_dist_list_cons flt2goodTock_xs by fastforce
      have "xs \<in> P"
        using 3 False
        by (metis concat_FL_last_not_bullet_absorb)
      then have "butlast xs &\<^sub>\<F>\<^sub>\<L> \<langle>last xs\<rangle>\<^sub>\<F>\<^sub>\<L> \<in> P"
        by (simp add: butlast_last_cons2_FL)
      then have xs_e:"butlast xs &\<^sub>\<F>\<^sub>\<L> \<langle>(last xs,Tock)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L> \<in> P"
        by (metis "3.prems"(2) CollectI FL2_def False List.last.simps \<open>[[X]\<^sub>R] = fl2ttobs \<langle>Finite_Linear_Model.last xs\<rangle>\<^sub>\<F>\<^sub>\<L>\<close> assms(1) ttobs.inject(2) fl2ttobs.simps(1))
      then have "\<rho> @ [[X]\<^sub>R,[Tock]\<^sub>E] = fl2ttobs(butlast xs &\<^sub>\<F>\<^sub>\<L> \<langle>(last xs,Tock)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>)"
      proof -
        have f1: "fl2ttobs xs = \<rho> @ [[X]\<^sub>R]"
          by (simp add: "3.prems"(3) False concat_FL_last_not_bullet_absorb)
        have f2: "List.butlast [[X]\<^sub>R, [Tock]\<^sub>E] = [[X]\<^sub>R]"
          by simp
        have "Tock \<in>\<^sub>\<F>\<^sub>\<L> Finite_Linear_Model.last xs"
          using "3.prems"(2) False \<open>[[X]\<^sub>R] = fl2ttobs \<langle>Finite_Linear_Model.last xs\<rangle>\<^sub>\<F>\<^sub>\<L>\<close> by force
        then show ?thesis
          using f2 f1 by (metis (no_types) List.last.simps append_butlast_last_id append_is_Nil_conv butlast_append fl_cons_acceptance_consFL fl2ttobs_last_tock flt2goodTock_xs last_appendR list.simps(3))
      qed
      then have "\<rho> @ [[X]\<^sub>R,[Tock]\<^sub>E] = fl2ttobs(butlast xs &\<^sub>\<F>\<^sub>\<L> \<langle>(last xs,Tock)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>) \<and> butlast xs &\<^sub>\<F>\<^sub>\<L> \<langle>(last xs,Tock)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L> \<in> P"
        using xs_e by auto
      then have "\<rho> @ [[X]\<^sub>R,[Tock]\<^sub>E] = fl2ttobs(butlast xs &\<^sub>\<F>\<^sub>\<L> \<langle>(last xs,Tock)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>) 
                              \<and> butlast xs &\<^sub>\<F>\<^sub>\<L> \<langle>(last xs,Tock)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L> \<in> P
                              \<and> flt2goodTock (butlast xs &\<^sub>\<F>\<^sub>\<L> \<langle>(last xs,Tock)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>)"
        using flt2goodTock_xs
        by (metis "3.prems"(2) CollectI False \<open>[[X]\<^sub>R] = fl2ttobs \<langle>Finite_Linear_Model.last xs\<rangle>\<^sub>\<F>\<^sub>\<L>\<close> ttobs.inject(2) fl_cons_acceptance_consFL fl2ttobs.simps(1) flt2goodTock_extend_consFL_last_fl_e list.inject)
      then show ?thesis by blast
    qed
qed

lemma TTM1_fl2ttm_for_FL2_FL1_FL0:
  assumes "FL2 P" "FL1 P" "FL0 P"
  shows "TTM1(fl2ttm P)"
proof -
  have "TTM1(fl2ttm P) = TTM1({fl2ttobs fl|fl. fl \<in> P \<and> flt2goodTock fl} \<union> {[]})"
    using assms
    by (simp add: fl2ttm_FL0_FL1_flt2goodTock)
  also have "... = TTM1({fl2ttobs fl|fl. fl \<in> P \<and> flt2goodTock fl})"
    using TTM1_union_empty_trace by auto
  also have "... = True"
    using assms unfolding fl2ttm_def TTM1_def apply auto
    using FL2_imp_TTM1_part by blast
  finally show ?thesis by auto
qed

lemma TTM2_fl2ttm_for_FL2_FL1_FL0:
  assumes "FL2 P" "FL1 P" "FL0 P"
  shows "TTM2(fl2ttm P)"
proof -
  have "TTM2(fl2ttm P) = TTM2({fl2ttobs fl|fl. fl \<in> P \<and> flt2goodTock fl} \<union> {[]})"
    using assms
    by (simp add: fl2ttm_FL0_FL1_flt2goodTock)
  also have "... = TTM2({fl2ttobs fl|fl. fl \<in> P \<and> flt2goodTock fl})"
    using TTM2_union_empty_trace by auto
  also have "... = True"
    using assms unfolding fl2ttm_def TTM2_def apply auto
    using FL2_imp_TTM2_part by blast
  finally show ?thesis by auto
qed

lemma Tick_of_Refuals_in_fl2ttobs:
  assumes "tickWF Tick fl" "\<rho> @ [[X]\<^sub>R] = fl2ttobs fl"
  shows "Tick \<in> X"
  using assms apply (induct fl arbitrary:X \<rho> rule:fl2ttobs.induct, auto)
   apply (case_tac A, auto)
  apply (case_tac A, auto, case_tac b, auto, case_tac a, auto)
    apply (meson append_eq_Cons_conv ttobs.simps(4) list.inject)
  apply (case_tac a, auto)
  apply (metis List.last.simps ttobs.simps(4) list.simps(3) not_Cons_self snoc_eq_iff_butlast)
  apply (case_tac b, auto)
  by (meson append_eq_Cons_conv ttobs.simps(4) list.inject)

lemma TT4w_fl2ttm_part:
  assumes "\<rho> @ [[X]\<^sub>R] = fl2ttobs fl" "FLTick0 Tick P"
          "fl \<in> P" 
    shows "\<exists>fl. \<rho> @ [[insert Tick X]\<^sub>R] = fl2ttobs fl \<and> fl \<in> P"
  using assms Tick_of_Refuals_in_fl2ttobs
  by (metis FLTick0_def insert_absorb)

lemma TT4w_fl2ttm:
  assumes "FLTick0 Tick P"
  shows "TT4w (fl2ttm P)" 
  using assms unfolding TT4w_def fl2ttm_def apply auto
  using TT4w_fl2ttm_part by blast

lemma tickWF_add_Tick_refusal_trace_fl2ttobs_idem:
  assumes "tickWF Tick xs"
  shows "add_Tick_refusal_trace (fl2ttobs xs) = (fl2ttobs xs)"
  using assms apply(induct xs rule:fl2ttobs.induct, auto)
   apply (case_tac A, auto, case_tac a, auto, case_tac b, auto)
  by (case_tac A, auto, case_tac b, auto)

lemma TT4_fl2ttm_part:
  assumes "FLTick0 Tick P" "fl \<in> P"
  shows "\<exists>fla. add_Tick_refusal_trace (fl2ttobs fl) = fl2ttobs fla \<and> fla \<in> P"
  using tickWF_add_Tick_refusal_trace_fl2ttobs_idem
  by (metis FLTick0_def assms(1) assms(2))



lemma TT0_union_empty:
  "TT0(P \<union> {[]})"
  unfolding TT0_def by auto

lemma TT4_fl2ttm:
  assumes "FLTick0 Tick P"
  shows "TT4 (fl2ttm P)" 
  using assms unfolding TT4_def fl2ttm_def apply auto
  using TT4_fl2ttm_part by blast

lemma ttWFx_trace_fl2ttobs:
  "ttWFx_trace (fl2ttobs fl)"
  apply (induct fl rule:fl2ttobs.induct) apply auto[1]
  apply (case_tac A, safe) 
   apply (case_tac a, safe) apply auto[1]
  apply (case_tac b, safe) apply auto[4]
  by (metis ttWFx_trace.simps(2) ttWFx_trace.simps(4) neq_Nil_conv)+

lemma ttWFx_fl2ttm:
  shows "ttWFx (fl2ttm P)"
  unfolding ttWFx_def fl2ttm_def using ttWFx_trace_fl2ttobs by auto

abbreviation "TT2wp \<rho> X P \<equiv> 
    {e. e \<noteq> Tock \<and> (\<exists>fl. \<rho> @ [[e]\<^sub>E] = fl2ttobs fl \<and> fl \<in> P \<and> flt2goodTock fl) \<or>
                e = Tock \<and> (\<exists>fl. \<rho> @ [[X]\<^sub>R, [e]\<^sub>E] = fl2ttobs fl \<and> fl \<in> P \<and> flt2goodTock fl)}"

lemma TT2w_fl2ttm_part:
  assumes "FL2 P" "FL1 P" "FL0 P"
          "Y \<inter> TT2wp \<rho> X P = {}"
          "\<rho> @ [[X]\<^sub>R] = fl2ttobs fl" "fl \<in> P" "flt2goodTock fl"
    shows "\<exists>fl. \<rho> @ [[X \<union> Y]\<^sub>R] = fl2ttobs fl \<and> fl \<in> P \<and> flt2goodTock fl \<and> X \<union> Y = X"
  using assms proof (induct fl arbitrary:\<rho> X Y rule:fltrace_induct)
case 1
  then show ?case by auto
next
  case (2 x xs)
  then show ?case
  proof (cases "last xs = \<bullet>")
    case True
    then have \<rho>_X:"\<rho> @ [[X]\<^sub>R] = fl2ttobs (xs) @ fl2ttobs(\<langle>x\<rangle>\<^sub>\<F>\<^sub>\<L>)"
      using 2
      by (metis (no_types, lifting) Finite_Linear_Model.last.simps(1) append.right_neutral bullet_right_zero2 fl2ttobs.simps(1) fl2ttobs_last_fl_not_bullet_dist_list_cons last_bullet_butlast_last last_bullet_then_last_cons)
    then show ?thesis
      proof (cases x)
        case acnil
        then show ?thesis using 2 True by auto
      next
        case (acset x2)
        then have "[[X]\<^sub>R] = fl2ttobs(\<langle>x\<rangle>\<^sub>\<F>\<^sub>\<L>)"
          using \<rho>_X by auto
        then have X_x2:"X = {x. x \<notin> x2}"
          using acset by auto
        
        have a:"\<forall>e. (e \<notin> X \<and> e \<noteq> Tock) \<longrightarrow> (\<exists>fl. \<rho> @ [[e]\<^sub>E] = fl2ttobs fl \<and> fl \<in> P \<and> flt2goodTock fl)"
          using "2.prems"(5) "2.prems"(6) "2.prems"(7) FL2_imp_TTM1_part assms(1) by blast
        then have a2:"\<forall>e. (e \<in> x2 \<and> e \<noteq> Tock) \<longrightarrow> (\<exists>fl. \<rho> @ [[e]\<^sub>E] = fl2ttobs fl \<and> fl \<in> P \<and> flt2goodTock fl)"
          using X_x2 by blast
        
        have b:"\<forall>e. (e \<notin> X \<and> e = Tock) \<longrightarrow> (\<exists>fl. \<rho> @ [[X]\<^sub>R, [Tock]\<^sub>E] = fl2ttobs fl \<and> fl \<in> P \<and> flt2goodTock fl)"
          using "2.prems"(5) "2.prems"(6) "2.prems"(7) FL2_imp_TTM2_part assms(1) by blast
        then have b2:"\<forall>e. (e \<in> x2 \<and> e = Tock) \<longrightarrow> (\<exists>fl. \<rho> @ [[X]\<^sub>R, [Tock]\<^sub>E] = fl2ttobs fl \<and> fl \<in> P \<and> flt2goodTock fl)"
          using X_x2 by blast

        have "x2 \<subseteq> {e. e \<noteq> Tock \<and> (\<exists>fl. \<rho> @ [[e]\<^sub>E] = fl2ttobs fl \<and> fl \<in> P \<and> flt2goodTock fl) \<or> e = Tock \<and> (\<exists>fl. \<rho> @ [[X]\<^sub>R, [e]\<^sub>E] = fl2ttobs fl \<and> fl \<in> P \<and> flt2goodTock fl)}"
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
    then have "\<rho> @ [[X]\<^sub>R] = fl2ttobs (xs)"
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
      by (metis (mono_tags, lifting) Nil_is_append_conv acceptance.distinct(1) last_cons_bullet_iff last_fl2ttobs_eq_ref_imp_last last_snoc not_Cons_self2)
  next
    case False
    then have "\<rho> @ [[X]\<^sub>R] = fl2ttobs (xs)"
      using 3 by (metis concat_FL_last_not_bullet_absorb)
    then show ?thesis 
      using 3 by (metis (no_types, lifting) False concat_FL_last_not_bullet_absorb)
  qed
qed

lemma flt2goodTock_consFL_imp_rhs:
  assumes "flt2goodTock (xs &\<^sub>\<F>\<^sub>\<L> ys)" "last xs = \<bullet>"
  shows "flt2goodTock (ys)"
  using assms apply (induct xs arbitrary:ys, auto)
  by (case_tac x1a, auto, case_tac a, auto, case_tac b, auto)

lemma flt2goodTock_consFL_imp_lhs:
  assumes "flt2goodTock (xs &\<^sub>\<F>\<^sub>\<L> ys)"
  shows "flt2goodTock (xs)"
  using assms by (induct xs arbitrary:ys, auto)

lemma TT2w_fl2ttm_part_Tock:
  assumes "FL2 P" "FL1 P" "FL0 P"
          "Y \<inter> TT2wp \<rho> X P = {}"
          "\<rho> @ [[X]\<^sub>R,[Tock]\<^sub>E] = fl2ttobs fl" "fl \<in> P" "flt2goodTock fl"
    shows "\<exists>fl. \<rho> @ [[X \<union> Y]\<^sub>R,[Tock]\<^sub>E] = fl2ttobs fl \<and> fl \<in> P \<and> flt2goodTock fl \<and> X \<union> Y = X"
  using assms proof (induct fl arbitrary:\<rho> X Y rule:fltrace_induct)
case 1
  then show ?case by auto
next
  case (2 x xs)
  then show ?case
  proof (cases "last xs = \<bullet>")
    case True
    then have \<rho>_X:"\<rho> @ [[X]\<^sub>R,[Tock]\<^sub>E] = fl2ttobs (xs) @ fl2ttobs(\<langle>x\<rangle>\<^sub>\<F>\<^sub>\<L>)"
      using 2
      by (metis (no_types, lifting) Finite_Linear_Model.last.simps(1) append.right_neutral bullet_right_zero2 fl2ttobs.simps(1) fl2ttobs_last_fl_not_bullet_dist_list_cons last_bullet_butlast_last last_bullet_then_last_cons)
    then show ?thesis
      proof (cases x)
        case acnil
        then show ?thesis using 2 True by auto
      next
        case (acset x2)
        then have "[[X]\<^sub>R] = fl2ttobs(\<langle>x\<rangle>\<^sub>\<F>\<^sub>\<L>)"
          using \<rho>_X by auto
        then show ?thesis
          by (metis \<rho>_X ttobs.distinct(1) last_ConsL last_ConsR last_append list.distinct(1))
      qed
    next
    case False
    then have "\<rho> @ [[X]\<^sub>R,[Tock]\<^sub>E] = fl2ttobs (xs)"
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
    then have \<rho>_X:"\<rho> @ [[X]\<^sub>R,[Tock]\<^sub>E] = fl2ttobs (xs) @ fl2ttobs(\<langle>x,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>)"
      using 3 
      by (metis (no_types, lifting) fl2ttobs_acceptance_cons_eq_list_cons fl2ttobs_not_flt2goodTock_imp_fl2ttobs_eq_consFL_any fltrace_concat2_assoc last_cons_bullet_iff)
    then have "flt2goodTock \<langle>x,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>"
      using "3.prems"(7) flt2goodTock_consFL_imp_rhs True by blast
    then have X_Tock:"[[X]\<^sub>R,[Tock]\<^sub>E] = fl2ttobs(\<langle>x,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>)"
      using \<rho>_X by (cases x, auto, case_tac b, auto, case_tac b, auto) 
    then obtain xA where xA:"x = ([xA]\<^sub>\<F>\<^sub>\<L>,Tock)\<^sub>\<F>\<^sub>\<L> \<and> Tock \<in> xA \<and> X = {x. x \<notin> xA}"
      using \<rho>_X by (auto, cases x, auto, case_tac a, auto, case_tac b, auto, case_tac b, auto)
    then have "[[X]\<^sub>R] = fl2ttobs(\<langle>[xA]\<^sub>\<F>\<^sub>\<L>\<rangle>\<^sub>\<F>\<^sub>\<L>)"
      using X_Tock by auto
    then have "\<rho> @ [[X]\<^sub>R] = fl2ttobs (xs &\<^sub>\<F>\<^sub>\<L> \<langle>[xA]\<^sub>\<F>\<^sub>\<L>\<rangle>\<^sub>\<F>\<^sub>\<L>)"
      by (metis (mono_tags, lifting) "3.prems"(7) Finite_Linear_Model.last.simps(1) True X_Tock \<rho>_X append_same_eq butlast_last_FL fl2ttobs_last_fl_not_bullet_dist_list_cons flt2goodTock_consFL_imp_lhs flt2goodTock_extend_consFL_acceptance last_bullet_butlast_last last_bullet_then_last_cons last_cons_acceptance_not_bullet)
    
    have "xs &\<^sub>\<F>\<^sub>\<L> \<langle>acceptance(x)\<rangle>\<^sub>\<F>\<^sub>\<L> \<in> P"
      by (metis (mono_tags, hide_lams) "3.prems"(6) FL1_def True assms(2) less_eq_fltrace.simps(2) prefixFL_same_length_imp_1 strongFL_imp_less_eq strong_less_eq_fltrace.simps(1) strong_less_eq_fltrace_refl)
    then have "xs &\<^sub>\<F>\<^sub>\<L> \<langle>[xA]\<^sub>\<F>\<^sub>\<L>\<rangle>\<^sub>\<F>\<^sub>\<L> \<in> P"
      using xA by auto

    have a:"\<forall>e. (e \<notin> X \<and> e \<noteq> Tock) \<longrightarrow> (\<exists>fl. \<rho> @ [[e]\<^sub>E] = fl2ttobs fl \<and> fl \<in> P \<and> flt2goodTock fl)"
      using xA FL2_imp_TTM1_part
      by (metis "3.prems"(7) Finite_Linear_Model.last.simps(1) True \<open>\<rho> @ [[X]\<^sub>R] = fl2ttobs (xs &\<^sub>\<F>\<^sub>\<L> \<langle>[xA]\<^sub>\<F>\<^sub>\<L>\<rangle>\<^sub>\<F>\<^sub>\<L>)\<close> \<open>xs &\<^sub>\<F>\<^sub>\<L> \<langle>[xA]\<^sub>\<F>\<^sub>\<L>\<rangle>\<^sub>\<F>\<^sub>\<L> \<in> P\<close> assms(1) butlast_last_FL flt2goodTock_consFL_imp_lhs flt2goodTock_extend_consFL_acceptance last_bullet_butlast_last)
    then have a2:"\<forall>e. (e \<in> xA \<and> e \<noteq> Tock) \<longrightarrow> (\<exists>fl. \<rho> @ [[e]\<^sub>E] = fl2ttobs fl \<and> fl \<in> P \<and> flt2goodTock fl)"
      using xA by blast

    have b:"\<forall>e. (e \<notin> X \<and> e = Tock) \<longrightarrow> (\<exists>fl. \<rho> @ [[X]\<^sub>R, [Tock]\<^sub>E] = fl2ttobs fl \<and> fl \<in> P \<and> flt2goodTock fl)"
      using xA FL2_imp_TTM2_part
      using "3.prems"(5) "3.prems"(6) "3.prems"(7) by blast
    then have b2:"\<forall>e. (e \<in> xA \<and> e = Tock) \<longrightarrow> (\<exists>fl. \<rho> @ [[X]\<^sub>R, [Tock]\<^sub>E] = fl2ttobs fl \<and> fl \<in> P \<and> flt2goodTock fl)"
      using xA by blast

    have "xA \<subseteq> {e. e \<noteq> Tock \<and> (\<exists>fl. \<rho> @ [[e]\<^sub>E] = fl2ttobs fl \<and> fl \<in> P \<and> flt2goodTock fl) \<or> e = Tock \<and> (\<exists>fl. \<rho> @ [[X]\<^sub>R, [e]\<^sub>E] = fl2ttobs fl \<and> fl \<in> P \<and> flt2goodTock fl)}"
      using a2 b2 by auto
    then have "Y \<subseteq> X"
      using 3 xA by blast
    then have "X \<union> Y = X"
      by auto
   then show ?thesis using 3
      by metis
  next
    case False
    then have "\<rho> @ [[X]\<^sub>R,[Tock]\<^sub>E] = fl2ttobs (xs)"
      using 3 by (metis concat_FL_last_not_bullet_absorb)
    then show ?thesis 
      using 3 by (metis (no_types, lifting) False concat_FL_last_not_bullet_absorb)
  qed
qed

lemma TT2w_fl2ttm_part':
  assumes "FL2 P" "FL1 P" "FL0 P"
          "Y \<inter> TT2wp \<rho> X P = {}"
          "\<rho> @ [[X]\<^sub>R] = fl2ttobs fl" "fl \<in> P" "flt2goodTock fl"
        shows "\<exists>fl. \<rho> @ [[X \<union> Y]\<^sub>R] = fl2ttobs fl \<and> fl \<in> P \<and> flt2goodTock fl"
proof -
  have "\<exists>fl. \<rho> @ [[X \<union> Y]\<^sub>R] = fl2ttobs fl \<and> fl \<in> P \<and> flt2goodTock fl \<and> X \<union> Y = X"
    using assms by (auto simp add:TT2w_fl2ttm_part)
  then have "\<exists>fl. \<rho> @ [[X \<union> Y]\<^sub>R] = fl2ttobs fl \<and> fl \<in> P \<and> flt2goodTock fl"
    by blast
  then show ?thesis by auto
qed

lemma TT2w_union_empty_trace:
  "TT2w(P \<union> {[]}) = TT2w(P)"
  unfolding TT2w_def by auto

lemma TT2w_fl2ttm:
  assumes "FL2 P" "FL1 P" "FL0 P"
  shows "TT2w (fl2ttm P)"
proof -
  have "TT2w (fl2ttm P) = TT2w ({fl2ttobs fl|fl. fl \<in> P \<and> flt2goodTock fl} \<union> {[]})"
    using assms by (simp add: fl2ttm_FL0_FL1_flt2goodTock)
  also have "... = TT2w ({fl2ttobs fl|fl. fl \<in> P \<and> flt2goodTock fl})"
    using TT2w_union_empty_trace by auto
  also have "... = (\<forall>\<rho> X Y.
        \<rho> @ [[X]\<^sub>R] \<in> {fl2ttobs fl |fl. fl \<in> P \<and> flt2goodTock fl} \<and>
        Y \<inter> TT2wp \<rho> X P = {} \<longrightarrow>
        \<rho> @ [[X \<union> Y]\<^sub>R] \<in> {fl2ttobs fl |fl. fl \<in> P \<and> flt2goodTock fl})"
    using assms unfolding TT2w_def fl2ttm_def by auto
  also have "... = True"
    using assms by (auto simp add: TT2w_fl2ttm_part')
  finally show ?thesis by auto
qed

lemma ttWF_dist_cons_refusal': 
  assumes "ttWF (s @ [[S]\<^sub>R] @ t)"
  shows "ttWF ([[S]\<^sub>R] @ t)"
  using assms by(induct s rule:ttWF.induct, auto)

lemma fl2ttobs_split_cons:
  assumes "ys @ xs = fl2ttobs fl" "flt2goodTock fl" "ttWF ys" "ttWF xs"
  shows "\<exists>fl\<^sub>1 fl\<^sub>0. ys = fl2ttobs fl\<^sub>0 \<and> xs = fl2ttobs fl\<^sub>1 \<and> fl\<^sub>0 &\<^sub>\<F>\<^sub>\<L> fl\<^sub>1 = fl \<and> flt2goodTock fl\<^sub>0 \<and> flt2goodTock fl\<^sub>1"
  using assms
proof (induct fl arbitrary:xs ys rule:fl2ttobs.induct)
  case (1 A)
  then show ?case 
    apply (cases A, auto)
     apply (rule_tac x="\<langle>\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>" in exI, auto)
    apply (induct ys, auto)
     apply (rule_tac x="\<langle>[x2]\<^sub>\<F>\<^sub>\<L>\<rangle>\<^sub>\<F>\<^sub>\<L>" in exI, rule_tac x="\<langle>\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>" in exI, auto)
    by (rule_tac x="\<langle>\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>" in exI, rule_tac x="\<langle>[x2]\<^sub>\<F>\<^sub>\<L>\<rangle>\<^sub>\<F>\<^sub>\<L>" in exI, auto)
next
  case (2 A fl)
  then obtain eA e where eA:"A = (eA, e)\<^sub>\<F>\<^sub>\<L> \<and> (e \<in>\<^sub>\<F>\<^sub>\<L> eA \<or> eA = \<bullet>)"
      by (metis Rep_aevent_inverse acceptance.rep_eq event.rep_eq event_in_acceptance prod.collapse)
  then have fl2ttobs_A_fl:"fl2ttobs (A #\<^sub>\<F>\<^sub>\<L> fl) = fl2ttobs ((eA, e)\<^sub>\<F>\<^sub>\<L> #\<^sub>\<F>\<^sub>\<L> fl)"
      using 2 by auto
  
  show ?case using 2
  proof (induct ys)
    case Nil
    then show ?case
      by (metis append_Nil bullet_left_zero2 fl2ttobs.simps(1) flt2goodTock.simps(1))
  next
    case (Cons a ys)
    then show ?case
    proof (cases a)
      case (ObsEvent x1)
      then show ?thesis
      proof (cases x1)
        case (Event e1)
        then have ys_xs:"([Event e1]\<^sub>E # ys) @ xs = fl2ttobs ((eA, e)\<^sub>\<F>\<^sub>\<L> #\<^sub>\<F>\<^sub>\<L> fl)"
          using ObsEvent Cons fl2ttobs_A_fl by auto
        then have "e = Event e1"
          using eA by (cases e, auto, cases eA, auto)
        then have e1_fl2ttobs:"[[Event e1]\<^sub>E] = fl2ttobs (\<langle>(eA, e)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>)"
                  "ys @ xs = fl2ttobs fl"
          using eA ys_xs by auto
        then have "\<exists>fl\<^sub>1 fl\<^sub>0. ys = fl2ttobs fl\<^sub>0 \<and> xs = fl2ttobs fl\<^sub>1 \<and> fl\<^sub>0 &\<^sub>\<F>\<^sub>\<L> fl\<^sub>1 = fl \<and> flt2goodTock fl\<^sub>0 \<and> flt2goodTock fl\<^sub>1"
          using ObsEvent Cons
          by (metis Event ttWF.simps(4) flt2goodTock.simps(2))
        then have "\<exists>fl\<^sub>1 fl\<^sub>0. [Event e1]\<^sub>E # ys = fl2ttobs (\<langle>(eA, e)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>) @ fl2ttobs fl\<^sub>0 \<and> xs = fl2ttobs fl\<^sub>1 
                                \<and> fl\<^sub>0 &\<^sub>\<F>\<^sub>\<L> fl\<^sub>1 = fl \<and> flt2goodTock fl\<^sub>0 \<and> flt2goodTock fl\<^sub>1" 
          using e1_fl2ttobs by auto
        then have "\<exists>fl\<^sub>1 fl\<^sub>0. [Event e1]\<^sub>E # ys = fl2ttobs (\<langle>(eA, e)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>) @ fl2ttobs fl\<^sub>0 \<and> xs = fl2ttobs fl\<^sub>1 
                                \<and> (\<langle>(eA, e)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L> &\<^sub>\<F>\<^sub>\<L> fl\<^sub>0) &\<^sub>\<F>\<^sub>\<L> fl\<^sub>1 = (eA, e)\<^sub>\<F>\<^sub>\<L> #\<^sub>\<F>\<^sub>\<L> fl \<and> flt2goodTock fl\<^sub>0 \<and> flt2goodTock fl\<^sub>1" 
          by auto
        then have "\<exists>fl\<^sub>1 fl\<^sub>0. [Event e1]\<^sub>E # ys = fl2ttobs (\<langle>(eA, e)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L> &\<^sub>\<F>\<^sub>\<L> fl\<^sub>0) \<and> xs = fl2ttobs fl\<^sub>1 
                                \<and> (\<langle>(eA, e)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L> &\<^sub>\<F>\<^sub>\<L> fl\<^sub>0) &\<^sub>\<F>\<^sub>\<L> fl\<^sub>1 = (eA, e)\<^sub>\<F>\<^sub>\<L> #\<^sub>\<F>\<^sub>\<L> fl \<and> flt2goodTock (\<langle>(eA, e)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L> &\<^sub>\<F>\<^sub>\<L> fl\<^sub>0) \<and> flt2goodTock fl\<^sub>1" 
          using \<open>e = Event e1\<close> eA by auto
        then have "\<exists>fl\<^sub>1 fl\<^sub>0. a # ys = fl2ttobs (\<langle>(eA, e)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L> &\<^sub>\<F>\<^sub>\<L> fl\<^sub>0) \<and> xs = fl2ttobs fl\<^sub>1 
                                \<and> (\<langle>(eA, e)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L> &\<^sub>\<F>\<^sub>\<L> fl\<^sub>0) &\<^sub>\<F>\<^sub>\<L> fl\<^sub>1 = A #\<^sub>\<F>\<^sub>\<L> fl \<and> flt2goodTock (\<langle>(eA, e)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L> &\<^sub>\<F>\<^sub>\<L> fl\<^sub>0) \<and> flt2goodTock fl\<^sub>1" 
          using ObsEvent Event eA by auto
        then show ?thesis by blast
      next
        case Tock
        then show ?thesis using Cons
          by (metis ObsEvent ttWF.simps(6))
      next
        case Tick
        then have ys_xs:"([Tick]\<^sub>E # ys) @ xs = fl2ttobs ((eA, e)\<^sub>\<F>\<^sub>\<L> #\<^sub>\<F>\<^sub>\<L> fl)"
          using ObsEvent Cons fl2ttobs_A_fl by auto
        then have "e = Tick"
          using eA by (cases e, auto, cases eA, auto)
        then have e1_fl2ttobs:"[[Tick]\<^sub>E] = fl2ttobs (\<langle>(eA, e)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>)"
                  "ys @ xs = fl2ttobs fl"
          using eA ys_xs by auto
        then have "\<exists>fl\<^sub>1 fl\<^sub>0. ys = fl2ttobs fl\<^sub>0 \<and> xs = fl2ttobs fl\<^sub>1 \<and> fl\<^sub>0 &\<^sub>\<F>\<^sub>\<L> fl\<^sub>1 = fl \<and> flt2goodTock fl\<^sub>0 \<and> flt2goodTock fl\<^sub>1"
          using ObsEvent Cons
          by (metis Tick append_Nil bullet_left_zero2 ttWF.simps(8) fl2ttobs.simps(1) flt2goodTock.simps(1) flt2goodTock.simps(2) neq_Nil_conv)
        then have "\<exists>fl\<^sub>1 fl\<^sub>0. [Tick]\<^sub>E # ys = fl2ttobs (\<langle>(eA, e)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>) @ fl2ttobs fl\<^sub>0 \<and> xs = fl2ttobs fl\<^sub>1 
                                \<and> fl\<^sub>0 &\<^sub>\<F>\<^sub>\<L> fl\<^sub>1 = fl \<and> flt2goodTock fl\<^sub>0 \<and> flt2goodTock fl\<^sub>1" 
          using e1_fl2ttobs by auto
        then have "\<exists>fl\<^sub>1 fl\<^sub>0. [Tick]\<^sub>E # ys = fl2ttobs (\<langle>(eA, e)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>) @ fl2ttobs fl\<^sub>0 \<and> xs = fl2ttobs fl\<^sub>1 
                                \<and> (\<langle>(eA, e)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L> &\<^sub>\<F>\<^sub>\<L> fl\<^sub>0) &\<^sub>\<F>\<^sub>\<L> fl\<^sub>1 = (eA, e)\<^sub>\<F>\<^sub>\<L> #\<^sub>\<F>\<^sub>\<L> fl \<and> flt2goodTock fl\<^sub>0 \<and> flt2goodTock fl\<^sub>1" 
          by auto
        then have "\<exists>fl\<^sub>1 fl\<^sub>0. [Tick]\<^sub>E # ys = fl2ttobs (\<langle>(eA, e)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L> &\<^sub>\<F>\<^sub>\<L> fl\<^sub>0) \<and> xs = fl2ttobs fl\<^sub>1 
                                \<and> (\<langle>(eA, e)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L> &\<^sub>\<F>\<^sub>\<L> fl\<^sub>0) &\<^sub>\<F>\<^sub>\<L> fl\<^sub>1 = (eA, e)\<^sub>\<F>\<^sub>\<L> #\<^sub>\<F>\<^sub>\<L> fl \<and> flt2goodTock (\<langle>(eA, e)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L> &\<^sub>\<F>\<^sub>\<L> fl\<^sub>0) \<and> flt2goodTock fl\<^sub>1" 
          using \<open>e = Tick\<close> eA by auto
        then have "\<exists>fl\<^sub>1 fl\<^sub>0. a # ys = fl2ttobs (\<langle>(eA, e)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L> &\<^sub>\<F>\<^sub>\<L> fl\<^sub>0) \<and> xs = fl2ttobs fl\<^sub>1 
                                \<and> (\<langle>(eA, e)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L> &\<^sub>\<F>\<^sub>\<L> fl\<^sub>0) &\<^sub>\<F>\<^sub>\<L> fl\<^sub>1 = A #\<^sub>\<F>\<^sub>\<L> fl \<and> flt2goodTock (\<langle>(eA, e)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L> &\<^sub>\<F>\<^sub>\<L> fl\<^sub>0) \<and> flt2goodTock fl\<^sub>1" 
          using ObsEvent Tick eA by auto
        then show ?thesis by blast
      qed
    next
      case (Ref x2)
      then show ?thesis using Cons
        proof (induct ys)
          case Nil_ys:Nil
          then show ?case using Cons
          proof (induct xs)
            case Nil
            then show ?case
              by (metis append.right_neutral bullet_right_zero2 fl2ttobs.simps(1) flt2goodTock.simps(1))
          next
            case Cons_xs:(Cons b zs)
            then have "[a] @ b # zs = fl2ttobs (A #\<^sub>\<F>\<^sub>\<L> fl)"
              using Cons_xs Cons
              by blast
            then have b_Tock:"b = [Tock]\<^sub>E"
              using Ref apply (auto, cases A, auto, case_tac aa, auto, case_tac ba, auto)
              by (case_tac ba, auto)
            then have "\<not> ttWF (b # zs)"
              by auto
            then show ?case using Cons_xs by blast
          qed
        next
          case Cons_ys:(Cons b zs)
          then have "ttWF (a # b # zs)"
            using Cons_ys.prems(7) by blast
          then have b_Tock:"b = [Tock]\<^sub>E"
            using Cons Ref
            by (metis ttWF.simps(11) ttWF.simps(12) ttWF.simps(13) ttevent.exhaust ttobs.distinct(1) ttobs.exhaust ttobs.inject(1) last_snoc)
          then have "([x2]\<^sub>R # [Tock]\<^sub>E # zs) @ xs = fl2ttobs (A #\<^sub>\<F>\<^sub>\<L> fl)"
            using Cons_ys.prems(5) Ref by blast 
          then have ys_xs:"([x2]\<^sub>R # [Tock]\<^sub>E # zs) @ xs = fl2ttobs ((eA, e)\<^sub>\<F>\<^sub>\<L> #\<^sub>\<F>\<^sub>\<L> fl)"
            using Cons fl2ttobs_A_fl b_Tock
            by presburger
          then have "[[x2]\<^sub>R,[Tock]\<^sub>E] @ (zs @ xs) = fl2ttobs ((eA, e)\<^sub>\<F>\<^sub>\<L> #\<^sub>\<F>\<^sub>\<L> fl)"
            by auto
          then have "[[x2]\<^sub>R,[Tock]\<^sub>E] @ (zs @ xs) = fl2ttobs (\<langle>(eA, e)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L> &\<^sub>\<F>\<^sub>\<L> fl)"
            by auto
          then have e1_fl2ttobs:"[[x2]\<^sub>R,[Tock]\<^sub>E] = fl2ttobs (\<langle>(eA, e)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>)"
                  "zs @ xs = fl2ttobs fl"
            using eA ys_xs apply (auto, cases eA, auto, cases e, auto, cases eA, auto, cases e, auto, cases e, auto, cases eA, auto, cases e, auto)
            by (cases e, auto)
          then have flt2goodTock_eA: "flt2goodTock (\<langle>(eA, e)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>)"
            by auto
          then have "\<exists>fl\<^sub>1 fl\<^sub>0. zs = fl2ttobs fl\<^sub>0 \<and> xs = fl2ttobs fl\<^sub>1 \<and> fl\<^sub>0 &\<^sub>\<F>\<^sub>\<L> fl\<^sub>1 = fl \<and> flt2goodTock fl\<^sub>0 \<and> flt2goodTock fl\<^sub>1"
            using Cons e1_fl2ttobs
            by (metis Cons_ys.prems(7) Ref b_Tock ttWF.simps(5) flt2goodTock.simps(2))
          then have "\<exists>fl\<^sub>1 fl\<^sub>0. [x2]\<^sub>R # [Tock]\<^sub>E # zs = fl2ttobs (\<langle>(eA, e)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>) @ fl2ttobs fl\<^sub>0 \<and> xs = fl2ttobs fl\<^sub>1 
                                \<and> fl\<^sub>0 &\<^sub>\<F>\<^sub>\<L> fl\<^sub>1 = fl \<and> flt2goodTock fl\<^sub>0 \<and> flt2goodTock fl\<^sub>1" 
          using e1_fl2ttobs
          by (metis Cons_eq_appendI eq_Nil_appendI)
        then have "\<exists>fl\<^sub>1 fl\<^sub>0. [x2]\<^sub>R # [Tock]\<^sub>E # zs = fl2ttobs (\<langle>(eA, e)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>) @ fl2ttobs fl\<^sub>0 \<and> xs = fl2ttobs fl\<^sub>1 
                                \<and> (\<langle>(eA, e)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L> &\<^sub>\<F>\<^sub>\<L> fl\<^sub>0) &\<^sub>\<F>\<^sub>\<L> fl\<^sub>1 = (eA, e)\<^sub>\<F>\<^sub>\<L> #\<^sub>\<F>\<^sub>\<L> fl \<and> flt2goodTock fl\<^sub>0 \<and> flt2goodTock fl\<^sub>1" 
          by auto
        then have "\<exists>fl\<^sub>1 fl\<^sub>0. [x2]\<^sub>R # [Tock]\<^sub>E # zs = fl2ttobs (\<langle>(eA, e)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L> &\<^sub>\<F>\<^sub>\<L> fl\<^sub>0) \<and> xs = fl2ttobs fl\<^sub>1 
                                \<and> (\<langle>(eA, e)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L> &\<^sub>\<F>\<^sub>\<L> fl\<^sub>0) &\<^sub>\<F>\<^sub>\<L> fl\<^sub>1 = (eA, e)\<^sub>\<F>\<^sub>\<L> #\<^sub>\<F>\<^sub>\<L> fl \<and> flt2goodTock (\<langle>(eA, e)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L> &\<^sub>\<F>\<^sub>\<L> fl\<^sub>0) \<and> flt2goodTock fl\<^sub>1" 
          using eA flt2goodTock_eA 
          apply auto
            apply blast
          by (cases e, auto)+
        then have "\<exists>fl\<^sub>1 fl\<^sub>0. a # b # zs = fl2ttobs (\<langle>(eA, e)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L> &\<^sub>\<F>\<^sub>\<L> fl\<^sub>0) \<and> xs = fl2ttobs fl\<^sub>1 
                                \<and> (\<langle>(eA, e)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L> &\<^sub>\<F>\<^sub>\<L> fl\<^sub>0) &\<^sub>\<F>\<^sub>\<L> fl\<^sub>1 = A #\<^sub>\<F>\<^sub>\<L> fl \<and> flt2goodTock (\<langle>(eA, e)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L> &\<^sub>\<F>\<^sub>\<L> fl\<^sub>0) \<and> flt2goodTock fl\<^sub>1" 
          using Ref eA b_Tock by auto
        then show ?case by blast
        qed
      qed
  qed
qed

lemma TT2_fl2ttm_part:
  assumes "FL2 P" "FL1 P" "FL0 P" "FLTick0 Tick P"
          "Y \<inter> TT2wp \<rho> X P = {}"
          "\<rho> @ [[X]\<^sub>R] @ \<sigma> = fl2ttobs fl" "fl \<in> P" "flt2goodTock fl"
        shows "\<exists>fl. \<rho> @ [[X \<union> Y]\<^sub>R] @ \<sigma> = fl2ttobs fl \<and> fl \<in> P \<and> flt2goodTock fl"
  using assms
proof (cases \<sigma>)
  case Nil
  then show ?thesis using assms by (auto simp add: TT2w_fl2ttm_part')
next
  case (Cons a list)
  then have "a = [Tock]\<^sub>E"
  proof -
    have "ttWF(\<rho> @ [[X]\<^sub>R] @ \<sigma>)"
      using fl2ttobs_is_ttWF assms
      by (metis FLTick0_def)
    then have "ttWF([[X]\<^sub>R] @ \<sigma>)"
      using ttWF_dist_cons_refusal' by blast
    then have "ttWF([[X]\<^sub>R] @ (a # list))"
      using Cons by auto
    then have "ttWF([X]\<^sub>R # a # list)"
      by auto
    then show ?thesis
      using ttWF.elims(2) by blast
  qed

  then have ttWF_cons:"ttWF(\<rho> @ [[X]\<^sub>R,a])"
  proof -
    have "ttWF(\<rho> @ [X]\<^sub>R # a # list)"
      by (metis Cons_eq_append_conv FLTick0_def assms(4) assms(6) assms(7) ttWF_dist_cons_refusal' fl2ttobs_is_ttWF local.Cons)
    then have "ttWF(\<rho> @ [[X]\<^sub>R,a])"
      by (metis (no_types, hide_lams) Cons_eq_append_conv append_eq_appendI ttWF_prefix_is_ttWF self_append_conv2)
    then show ?thesis .
  qed

  then have ttWF_list:"ttWF(list)"
  proof -
    have "ttWF(\<rho> @ [X]\<^sub>R # a # list)"
      by (metis Cons_eq_append_conv FLTick0_def assms(4) assms(6) assms(7) ttWF_dist_cons_refusal' fl2ttobs_is_ttWF local.Cons)
    then have "ttWF(list)"
      by (metis \<open>a = [Tock]\<^sub>E\<close> append_eq_Cons_conv ttWF.simps(5) ttWF_dist_cons_refusal' local.Cons)
    then show ?thesis .
  qed

  have "\<rho> @ [[X]\<^sub>R,a] @ list = \<rho> @ [[X]\<^sub>R] @ \<sigma>"
    by (simp add: local.Cons)
  then obtain fl\<^sub>0 fl\<^sub>1 where fls:"\<rho> @ [[X]\<^sub>R,a] = fl2ttobs fl\<^sub>0 \<and> flt2goodTock fl\<^sub>0 \<and> flt2goodTock fl\<^sub>1 \<and> list = fl2ttobs fl\<^sub>1 \<and> fl\<^sub>0 &\<^sub>\<F>\<^sub>\<L> fl\<^sub>1 = fl"
    using assms fl2ttobs_split_cons ttWF_cons ttWF_list 
    by (metis (no_types, lifting) append_assoc)
  then have "fl\<^sub>0 \<in> P"
    using assms x_le_concat2_FL1 by blast
  then have "\<exists>fl. \<rho> @ [[X \<union> Y]\<^sub>R,a] = fl2ttobs fl \<and> fl \<in> P \<and> flt2goodTock fl \<and> X \<union> Y = X"
    using assms TT2w_fl2ttm_part TT2w_fl2ttm_part_Tock 
  proof -
    have "\<forall>C cs f Ca F. ((((((Ca \<union> C = Ca \<or> C \<inter> TT2wp cs Ca F \<noteq> {}) \<or> cs @ [[Ca]\<^sub>R, a] \<noteq> fl2ttobs f) \<or> f \<notin> F) \<or> \<not> flt2goodTock f) \<or> \<not> FL2 F) \<or> \<not> FL1 F) \<or> \<not> FL0 F"
      using TT2w_fl2ttm_part_Tock \<open>a = [Tock]\<^sub>E\<close> by blast
    then have "X \<union> Y = X"
      using \<open>FL0 P\<close> \<open>FL1 P\<close> \<open>FL2 P\<close> \<open>Y \<inter> TT2wp \<rho> X P = {}\<close> \<open>fl\<^sub>0 \<in> P\<close> fls by blast
    then show ?thesis
    by (metis (no_types) \<open>fl\<^sub>0 \<in> P\<close> fls)
  qed
  then show ?thesis
    by (metis assms(6) assms(7) assms(8))
qed

lemma TT2_union_empty_trace:
  "TT2(P \<union> {[]}) = TT2(P)"
  unfolding TT2_def by auto

lemma TT2_fl2ttm:
  assumes "FL2 P" "FL1 P" "FL0 P" "FLTick0 Tick P"
  shows "TT2 (fl2ttm P)"
proof -
  have "TT2 (fl2ttm P) = TT2 ({fl2ttobs fl|fl. fl \<in> P \<and> flt2goodTock fl} \<union> {[]})"
    using assms by (simp add: fl2ttm_FL0_FL1_flt2goodTock)
  also have "... = TT2 ({fl2ttobs fl|fl. fl \<in> P \<and> flt2goodTock fl})"
    using TT2_union_empty_trace by auto
  also have "... = True"
    using assms unfolding TT2_def 
    apply auto using TT2_fl2ttm_part
    by (auto)
  finally show ?thesis by auto
qed

lemma TTwf_fl2ttm:
  assumes "FLTick0 Tick P" 
  shows "TTwf(fl2ttm(P))"
  using assms unfolding fl2ttm_def TTwf_def
  by (auto simp add: FLTick0_def fl2ttobs_is_ttWF)

lemma TT1w_fl2ttm_part:
  assumes "\<rho> \<le>\<^sub>C fl2ttobs fl"
  shows "\<exists>fl\<^sub>2. \<rho> = fl2ttobs fl\<^sub>2 \<and> fl\<^sub>2 \<le> fl"
  using assms  
proof (induct fl arbitrary:\<rho> rule:fl2ttobs.induct)
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
    then have fl2ttobs_A_fl:"fl2ttobs (A #\<^sub>\<F>\<^sub>\<L> fl) = [{x. x \<notin>\<^sub>\<F>\<^sub>\<L> acceptance(A)}]\<^sub>R # [Tock]\<^sub>E # fl2ttobs fl"
      using True by auto
    then have "\<rho> \<le>\<^sub>C fl2ttobs (A #\<^sub>\<F>\<^sub>\<L> fl) = (\<rho> \<le>\<^sub>C ([{x. x \<notin>\<^sub>\<F>\<^sub>\<L> acceptance(A)}]\<^sub>R # [Tock]\<^sub>E # fl2ttobs fl))"
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
        then have "a # z # zs \<le>\<^sub>C fl2ttobs (A #\<^sub>\<F>\<^sub>\<L> fl)"
          using Cons by blast
        then have "[{x. x \<notin>\<^sub>\<F>\<^sub>\<L> acceptance(A)}]\<^sub>R # [Tock]\<^sub>E # zs \<le>\<^sub>C fl2ttobs (A #\<^sub>\<F>\<^sub>\<L> fl)"
          using Cons.prems(1) \<open>z = [Tock]\<^sub>E\<close> by blast
        then have "[{x. x \<notin>\<^sub>\<F>\<^sub>\<L> acceptance(A)}]\<^sub>R # [Tock]\<^sub>E # zs \<le>\<^sub>C [{x. x \<notin>\<^sub>\<F>\<^sub>\<L> acceptance(A)}]\<^sub>R # [Tock]\<^sub>E # fl2ttobs fl"
          using fl2ttobs_A_fl by auto
        then have "zs \<le>\<^sub>C fl2ttobs fl"
          by auto
        then have "\<exists>fl\<^sub>2. zs = fl2ttobs fl\<^sub>2 \<and> fl\<^sub>2 \<le> fl"
          using Cons True by blast
        then have "\<exists>fl\<^sub>2. [{x. x \<notin>\<^sub>\<F>\<^sub>\<L> acceptance(A)}]\<^sub>R # [Tock]\<^sub>E # zs = [{x. x \<notin>\<^sub>\<F>\<^sub>\<L> acceptance(A)}]\<^sub>R # [Tock]\<^sub>E # fl2ttobs fl\<^sub>2 \<and> A #\<^sub>\<F>\<^sub>\<L> fl\<^sub>2 \<le> A #\<^sub>\<F>\<^sub>\<L> fl"
          by auto
        then have "\<exists>fl\<^sub>2. [{x. x \<notin>\<^sub>\<F>\<^sub>\<L> acceptance(A)}]\<^sub>R # [Tock]\<^sub>E # zs = fl2ttobs (A #\<^sub>\<F>\<^sub>\<L> fl\<^sub>2) \<and> A #\<^sub>\<F>\<^sub>\<L> fl\<^sub>2 \<le> A #\<^sub>\<F>\<^sub>\<L> fl"
          using True by auto
        then have "\<exists>fl\<^sub>2. a # z # zs = fl2ttobs (A #\<^sub>\<F>\<^sub>\<L> fl\<^sub>2) \<and> A #\<^sub>\<F>\<^sub>\<L> fl\<^sub>2 \<le> A #\<^sub>\<F>\<^sub>\<L> fl"
          using Cons by auto
        then have "\<exists>fl\<^sub>2. a # z # zs = fl2ttobs fl\<^sub>2 \<and> fl\<^sub>2 \<le> A #\<^sub>\<F>\<^sub>\<L> fl"
          by blast
        then show ?case by blast
      qed
    qed
  next
    case False
    then show ?thesis using 2 apply auto
      apply (metis (no_types, hide_lams) bullet_left_zero2 tt_prefix.simps(2) fl2ttobs.simps(1) fl2ttobs.simps(2) less_eq_fltrace.simps(3) neq_Nil_conv order_refl x_le_x_concat2)  
      apply (cases A, auto)
      apply (case_tac b, auto)
      apply (metis (no_types, hide_lams) acceptance_event bullet_left_zero2 tt_prefix.simps(2) ttevent.distinct(1) fl2ttobs.simps(1) fl2ttobs.simps(2) less_eq_fltrace.simps(3) neq_Nil_conv order_refl x_le_x_concat2)
      using tt_prefix_split apply force
      by (metis (no_types, hide_lams) acceptance_event bullet_left_zero2 tt_prefix.simps(2) ttevent.distinct(5) fl2ttobs.simps(1) fl2ttobs.simps(2) less_eq_fltrace.simps(3) neq_Nil_conv order_refl x_le_x_concat2)
  qed
qed

lemma TT0_fl2ttm:
  assumes "FL0 P" "FL1 P" "FL2 P" "FL3 P"
  shows "TT0(fl2ttm(P))"
  using assms using TT0_union_empty assms(1) assms(2) fl2ttm_FL0_FL1_flt2goodTock by fastforce

lemma TT1w_fl2ttm:
  assumes "FL1 P"
  shows "TT1w(fl2ttm(P))"
  using assms unfolding fl2ttm_def TT1w_def apply auto
  using TT1w_fl2ttm_part FL1_def by blast

lemma maximal_TT_fl2ttm_closed:
  assumes "FL0 P" "FL1 P" "FL2 P" "FL3 P"
  shows "TTwf(fl2ttm(P))"
        "TT0(fl2ttm(P))"
        "TT1w(fl2ttm(P))"
        "TT2(fl2ttm(P))"
        "ttWFx(fl2ttm(P))"
        "TT4(fl2ttm(P))"
        "TTM1(fl2ttm(P))"
        "TTM2(fl2ttm(P))"
        "TTM3(fl2ttm(P))"
  using assms TTwf_fl2ttm apply auto
  using assms TT0_fl2ttm apply auto
        apply (simp add: TT1w_fl2ttm assms(2))
       apply (simp add: TT2_fl2ttm assms(1) assms(2) assms(3) assms(4))
      apply (simp add: ttWFx_fl2ttm)
     apply (simp add: TT4_fl2ttm assms(4))
    apply (simp add: TTM1_fl2ttm_for_FL2_FL1_FL0 assms(1) assms(2) assms(3))
   apply (simp add: TTM2_fl2ttm_for_FL2_FL1_FL0 assms(1) assms(2) assms(3))
  by (simp add: TTM3_fl2ttm assms(1) assms(2) assms(4))

end
