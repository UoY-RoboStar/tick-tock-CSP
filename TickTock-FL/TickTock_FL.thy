theory TickTock_FL

imports
  TickTock_Max_FL
  TickTock_Max_TT1
  TickTock_FL_Pri
begin

text \<open> This theory defines the overall Galois connection between FL and Tick-Tock, using the
       two Galois connections, defined in TickTock_Max_FL and TickTock_Max_TT1. \<close>

section \<open> Adjoints \<close>

definition "fl2tt(P) = mkTT1(fl2ttm(P))"

definition "tt2fl(P) = ttm2fl(unTT1(P))"

section \<open> Properties \<close>

lemma fl2tt_mono:
  assumes "P \<subseteq> Q"
  shows "fl2tt(P) \<subseteq> fl2tt(Q)"
  using assms 
  by (simp add: fl2tt_def fl2ttm_mono mkTT1_mono)

lemma tt2fl_mono:
  assumes "P \<subseteq> Q"
  shows "tt2fl(P) \<subseteq> tt2fl(Q)"
  using assms
  by (simp add: tt2fl_def ttm2fl_mono unTT1_mono)

lemma TT_fl2tt_closed:
  assumes "FL0 P" "FL1 P" "FL2 P" "FL3 P"
  shows "TTwf(fl2tt(P))"
        "TT0(fl2tt(P))"
        "TT1(fl2tt(P))"
        "TT2(fl2tt(P))"
        "ttWFx(fl2tt(P))"
        "TT3(fl2tt(P))"
  using assms unfolding fl2tt_def 
  using TTwf_fl2ttm TTwf_mkTT1 apply blast
      apply (simp add: TT0_fl2ttm TT0_mkTT1 assms(1) assms(2) assms(3) assms(4))
     apply (simp add: TT1_mkTT1)
    apply (simp add: TT1w_fl2ttm TT2_fl2ttm TT2_mkTT1 TTM1_fl2ttm_for_FL2_FL1_FL0 TTM2_fl2ttm_for_FL2_FL1_FL0 assms(1) assms(2) assms(3) assms(4))
   apply (simp add: ttWFx_fl2ttm ttWFx_mkTT1)
  by (simp add: TT3_fl2ttm TT3_mkTT1 assms(4))

lemma FL_tt2fl_closed:
  assumes "TT(P)"
  shows "FL0(tt2fl(P))" "FL1(tt2fl(P))" "FL2(tt2fl(P))" "FL3(tt2fl(P))"
  using assms unfolding tt2fl_def
     apply (simp add: FL0_ttm2fl TT0_unTT1 TT1w_unTT1 TT_TT0 TT_TT1)
    apply (simp add: FL1_ttm2fl)
   apply (simp add: FL2_ttm2fl TT1w_unTT1 TTM1_unTT1 TTM2_unTT1)
  by (simp add: FL_ttm2fl_closed(4) TT0_unTT1 TT1w_unTT1 TTM1_unTT1 TTM2_unTT1 TTM3_unTT1 TT_TT0 TT_TT1 assms)

lemma
  shows "ttm2fl P = \<Union>{fl. FL3 fl \<and> FL0 fl \<and> FL1 fl \<and> (fl2ttm fl) \<subseteq> P}"
  unfolding ttm2fl_def apply auto
  using FL0_def by blast

lemma ttm2fl_alt:
  assumes "TTM1 P" "TTM2 P" "TT1w P" 
  shows "ttm2fl P = \<Union>{fl. FL3 fl \<and> FL2 fl \<and> FL1 fl \<and> FL0 fl \<and> (fl2ttm fl) \<subseteq> P}"
  using assms unfolding ttm2fl_def fl2ttm_def apply auto
  (*The following seems to give me an easy way to generalise this kind of proof. *)
  apply (rule_tac x="\<Union>{fl. FL3 fl \<and> FL1 fl \<and> {fl2ttobs fla |fla. fla \<in> fl} \<subseteq> P}" in exI, auto)
    apply (smt FLTick0_def mem_Collect_eq mem_simps(9)) 
  using  FL2_ttm2fl 
   apply (simp add: fl2ttm_def ttm2fl_def) 
  using FL2_ttm2fl assms(1) assms(2) assms(3) apply blast
   apply (smt FL1_def Union_iff mem_Collect_eq)
  using FL0_def by blast

(* Move the following into FL theories. *)
definition mkFL2 :: "'a fltraces \<Rightarrow> 'a fltraces" where
"mkFL2 P \<equiv> P \<union> {s. \<exists>\<beta> A a. \<beta> &\<^sub>\<F>\<^sub>\<L> \<langle>A\<rangle>\<^sub>\<F>\<^sub>\<L> \<in> P \<and> a \<in>\<^sub>\<F>\<^sub>\<L> A \<and> s = \<beta> &\<^sub>\<F>\<^sub>\<L> \<langle>(A,a)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>}"

lemma mkFL2_disj_univ: "mkFL2 (\<Union> P) = \<Union> ({mkFL2(x)|x. x \<in> P})"
  unfolding mkFL2_def by auto

lemma FL2_fixpoint: "FL2 P \<longleftrightarrow> mkFL2 P = P"
  unfolding FL2_def mkFL2_def by auto

lemma mkFL2_is_FL2: "FL2(mkFL2(P))"
  unfolding mkFL2_def FL2_def apply auto
  by (metis Finite_Linear_Model.last.simps(1) amember.simps(1) concat_FL_last_not_bullet_absorb last_bullet_then_last_cons last_cons_bullet_iff)

definition mkFL12 :: "'a fltraces \<Rightarrow> 'a fltraces" where
"mkFL12 P \<equiv> P \<union> {s. \<exists>\<beta> A a. \<beta> &\<^sub>\<F>\<^sub>\<L> \<langle>A\<rangle>\<^sub>\<F>\<^sub>\<L> \<in> P \<and> a \<in>\<^sub>\<F>\<^sub>\<L> A \<and> s \<le> \<beta> &\<^sub>\<F>\<^sub>\<L> \<langle>(A,a)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>}"

lemma mkFL12_eq_mkFL1_mkFL2:
  assumes "FL1 P"
  shows "mkFL12(P) = mkFL1(mkFL2(P))"
  using assms unfolding mkFL1_def mkFL2_def mkFL12_def apply safe
  apply blast+
  using FL1_def by blast+

lemma mkFL12_disj_univ: "mkFL12 (\<Union> P) = \<Union> ({mkFL12(x)|x. x \<in> P})"
  unfolding mkFL12_def by auto

lemma mkFL12_is_FL2: 
  assumes "FL1 P"
  shows "FL1(mkFL12(P))"
  using assms unfolding mkFL12_def FL1_def apply safe
  apply blast
  using order_trans by blast

lemma FL2_disj_imp:
  assumes "FL2 P" "FL2 Q" 
  shows "FL2(P \<union> Q)"
  using assms unfolding FL2_def by auto

lemma
  "\<rho> \<in> x \<Longrightarrow> add_Tick_refusal_trace \<rho> \<in> mkTT3 x"
  unfolding mkTT3_def by auto

lemma unTT1_alt:
  assumes "TT P" "TT3 P"
  shows "unTT1 P = \<Union>{x. TT0 x \<and> TT2 x \<and> ttWFx x \<and> TT3 x \<and> TTM1 x \<and> TTM2 x \<and> TTM3 x \<and> TT1w x \<and> TTwf x \<and> (mkTT1 x) \<subseteq> P}"
  unfolding unTT1_def mkTT1_def apply auto
  using assms apply (rule_tac x="unTT1 P" in exI, auto)
  using TT0_unTT1 TT_TT0 TT_TT1 apply blast
  using TT3_TT1_imp_TT3w assms using TT2_unTT1 TT_TT1 apply blast
  using ttWFx_unTT1 TT_TT1 TT_ttWFx apply blast
  using TT3_unTT1 TT_TT1 apply blast
  using TTM1_unTT1 apply blast
  using TTM2_unTT1 apply blast
  using TTM3_unTT1 apply blast
  using TT1w_unTT1 apply blast
  unfolding unTT1_def apply auto
  apply (metis TT_TTwf TTwf_unTT1 unTT1_def)
  apply (metis (mono_tags, lifting) UnI1 contra_subsetD mkTT1_def) 
   apply (metis (mono_tags, lifting) contra_subsetD mem_Collect_eq mkTT1_simp)
  apply (rule_tac x="X" in exI, auto)
  by (metis contra_subsetD mkTT1_simp)

(* TODO: Below move into other theories. *)

lemma
  assumes "last \<beta> \<noteq> \<bullet>"
  shows "\<not>(\<exists>z. z \<le> \<beta> &\<^sub>\<F>\<^sub>\<L> \<langle>(A,a)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L> \<and> \<beta> &\<^sub>\<F>\<^sub>\<L> \<langle>A\<rangle>\<^sub>\<F>\<^sub>\<L> \<le> z \<and> z \<noteq> \<beta> &\<^sub>\<F>\<^sub>\<L> \<langle>A\<rangle>\<^sub>\<F>\<^sub>\<L>)"
  using assms apply auto
  by (simp add: concat_FL_last_not_bullet_absorb)

lemma fltrace_less_imp_not_less:
  assumes "\<beta> &\<^sub>\<F>\<^sub>\<L> \<langle>A\<rangle>\<^sub>\<F>\<^sub>\<L> < z"
  shows "\<not> z < \<beta> &\<^sub>\<F>\<^sub>\<L> \<langle>(A,a)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>"
  using assms  apply (induct z \<beta> rule:less_eq_fltrace.induct, auto)
  apply (metis acceptance.distinct(1) acceptance_set dual_order.strict_iff_order fltrace_concat2.simps(3) less_eq_acceptance.elims(2) less_eq_fltrace.simps(1) less_eq_fltrace.simps(2) plus_acceptance.elims)
  using less_eq_fltrace.simps(4) less_fltrace_def apply blast
   apply (simp add: less_le_not_le)
  by (metis Finite_Linear_Model.last.simps(1) aevent_less_eq_iff_components bullet_left_zero2 concat_FL_last_not_bullet_absorb fltrace_concat2.simps(1) less_eq_acceptance.elims(2) less_eq_aevent_def less_eq_fltrace.simps(2) less_eq_fltrace.simps(3) less_fltrace_def x_le_x_concat2)

lemma fltrace_less_imp_not_less':
  assumes "\<beta> &\<^sub>\<F>\<^sub>\<L> \<langle>A\<rangle>\<^sub>\<F>\<^sub>\<L> < z"
  shows "\<not> z < \<beta> &\<^sub>\<F>\<^sub>\<L> \<langle>(\<bullet>,a)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>"
  using assms  apply (induct z \<beta> rule:less_eq_fltrace.induct, auto)
apply (metis acceptance.distinct(1) acceptance_set dual_order.strict_iff_order fltrace_concat2.simps(3) less_eq_acceptance.elims(2) less_eq_fltrace.simps(1) less_eq_fltrace.simps(2) plus_acceptance.elims)
  using less_eq_fltrace.simps(4) less_fltrace_def apply blast
   apply (simp add: less_le_not_le)
  by (metis Finite_Linear_Model.last.simps(1) aevent_less_eq_iff_components bullet_left_zero2 concat_FL_last_not_bullet_absorb fltrace_concat2.simps(1) less_eq_acceptance.elims(2) less_eq_aevent_def less_eq_fltrace.simps(2) less_eq_fltrace.simps(3) less_fltrace_def x_le_x_concat2)

lemma order_no_intermediate_imp_eq:
  fixes x ::"'a::order"
  assumes "\<forall>y. y \<le> c \<longrightarrow> x \<noteq> y" "c \<le> x" "x \<le> b" "\<not>(\<exists>z. c < z \<and> z < b)" 
  shows "b \<le> x"
  using assms apply auto 
  using dual_order.order_iff_strict by blast

lemma fltrace_consFL_less_eq_case:
  assumes "a \<in>\<^sub>\<F>\<^sub>\<L> A \<or> A = \<bullet>"
  shows "x &\<^sub>\<F>\<^sub>\<L> \<langle>A\<rangle>\<^sub>\<F>\<^sub>\<L> \<le> x &\<^sub>\<F>\<^sub>\<L> \<langle>(A,a)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>"
  using assms
  apply (induct x, auto)
   apply (case_tac x, auto)
   apply (cases A, auto)
  by (case_tac x, auto)

lemma FL3_union_imp_dist:
  assumes "FL3 (P \<union> Q)"
  shows "FL3 P"
  using assms unfolding FLTick0_def by auto

lemma FL3_mkFL2:
  assumes "FL3 X"
  shows "FL3 (mkFL2 X)"
  using assms unfolding mkFL2_def  apply auto
  by (smt FLTick0_def Un_iff mem_Collect_eq tickWF_acceptance_imp_tickWF_consFL)

lemma TTM3_TT3w:
  assumes "TTM3 P"
  shows "TT3w P"
  using assms unfolding TTM3_def TT3w_def apply auto
  using TTM3_TTick_part assms insert_absorb by force

lemma PriTT_eq_fl2tt_Pri_tt2fl:
  assumes "TT P" "TT2 P" "TT3 P"
  shows "PriTT p P = fl2tt(Pri p (tt2fl P))"
proof-
  have "PriTT p P = PriTT1 p P"
    by (simp add: PriTT_eq_priTT assms(1) assms(2) assms(3))
  also have "... = mkTT1(PriMax p (unTT1 P))"
    by (simp add: TT3_TT1_imp_TT3w TT_TT1 TT_ttWFx assms(1) assms(2) assms(3) mkTT1_PriMax_unTT1_priTT)
  also have "... = mkTT1(fl2ttm(Pri p (ttm2fl (unTT1 P))))"
  proof -
    have TTs:
         "TT0 (unTT1 P)"
         "TTwf (unTT1 P)"
         "TT1w (unTT1 P)" 
         "ttWFx (unTT1 P)" 
         "TT3 (unTT1 P)" 
         "TTM3 (unTT1 P)"
      by (simp_all add: assms unTT1_TT_closure)
    then have TT3w:"TT3w (unTT1 P)"
      using TTM3_TT3w by auto

    have TTick:"TTick (unTT1 P)"
      using assms TTM3_TTick TTM3_unTT1 by blast

    have "PriMax p (unTT1 P) = fl2ttm(Pri p (ttm2fl (unTT1 P)))"
      using TTs TTick TT3w fl2ttm_pri_ttm2fl_PriMax by auto
    then show ?thesis by auto
  qed
  also have "... = fl2tt(Pri p (ttm2fl (unTT1 P)))"
    unfolding fl2tt_def by auto
  also have "... = fl2tt(Pri p (tt2fl P))"
    unfolding tt2fl_def by auto
  finally show ?thesis .
qed

end