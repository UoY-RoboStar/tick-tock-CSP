theory TickTock_FL

imports
  TickTock_Max_FL
  TickTock_Max_TT1
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
        "TT3(fl2tt(P))"
        "TT4(fl2tt(P))"
  using assms unfolding fl2tt_def 
  using TTwf_fl2ttm TTwf_mkTT1 apply blast
      apply (simp add: TT0_mkTT1 assms(1) assms(2) assms(3) assms(4) maximal_TT_fl2ttm_closed(1))
     apply (simp add:TT1_mkTT1)
    apply (simp add: TT1w_fl2ttm TT2_mkTT1 assms(1) assms(2) assms(3) assms(4) maximal_TT_fl2ttm_closed(3) maximal_TT_fl2ttm_closed(6) maximal_TT_fl2ttm_closed(7))
   apply (simp add: TT3_fl2ttm TT3_mkTT1)
  by (simp add: TT4_fl2ttm TT4_mkTT1 assms(4))

lemma FL_tt2fl_closed:
  assumes "TT(P)"
  shows "FL0(tt2fl(P))" "FL1(tt2fl(P))" "FL2(tt2fl(P))" "FL3(tt2fl(P))"
  using assms unfolding tt2fl_def
     apply (simp add: FL0_ttm2fl TT0_unTT1 TT1w_unTT1 TT_TT0 TT_TT1)
    apply (simp add: FL1_ttm2fl)
   apply (simp add: FL2_ttm2fl TT1w_unTT1 TTM1_unTT1 TTM2_unTT1)
  by (simp add: FL_ttm2fl_closed(4) TT0_unTT1 TT1w_unTT1 TTM1_unTT1 TTM2_unTT1 TTM3_unTT1 TT_TT0 TT_TT1 assms)

lemma

  shows "ttm2fl P = \<Union>{fl. FLTick0 Tick fl \<and> FL0 fl \<and> FL1 fl \<and> (fl2ttm fl) \<subseteq> P}"
  unfolding ttm2fl_def apply auto
  using FL0_def by blast

(* \<forall>\<beta> A a. \<beta> &\<^sub>\<F>\<^sub>\<L> \<langle>A\<rangle>\<^sub>\<F>\<^sub>\<L> \<in> P \<and> a \<in>\<^sub>\<F>\<^sub>\<L> A \<longrightarrow> \<beta> &\<^sub>\<F>\<^sub>\<L> \<langle>(A,a)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L> \<in> P" *)
definition mkFL2 :: "'a fltraces \<Rightarrow> 'a fltraces" where
"mkFL2 P \<equiv> P \<union> {s. \<exists>\<beta> A a. \<beta> &\<^sub>\<F>\<^sub>\<L> \<langle>A\<rangle>\<^sub>\<F>\<^sub>\<L> \<in> P \<and> a \<in>\<^sub>\<F>\<^sub>\<L> A \<and> s = \<beta> &\<^sub>\<F>\<^sub>\<L> \<langle>(A,a)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>}"

lemma mkFL2_disj_univ: "mkFL2 (\<Union> P) = \<Union> ({mkFL2(x)|x. x \<in> P})"
  unfolding mkFL2_def by auto

lemma FL2_fixpoint: "FL2 P \<longleftrightarrow> mkFL2 P = P"
  unfolding FL2_def mkFL2_def by auto

lemma mkFL2_is_FL2: "FL2(mkFL2(P))"
  unfolding mkFL2_def FL2_def apply auto
  by (metis Finite_Linear_Model.last.simps(1) amember.simps(1) concat_FL_last_not_bullet_absorb last_bullet_then_last_cons last_cons_bullet_iff)

definition mkFL120 :: "'a fltraces \<Rightarrow> 'a fltraces" where
"mkFL120 P \<equiv> P \<union> {s. \<exists>\<beta> A a t. \<beta> &\<^sub>\<F>\<^sub>\<L> \<langle>A\<rangle>\<^sub>\<F>\<^sub>\<L> \<in> P \<and> a \<in>\<^sub>\<F>\<^sub>\<L> A \<and> t \<le> \<langle>(A,a)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L> \<and> s = \<beta> &\<^sub>\<F>\<^sub>\<L> t}"


lemma
  shows "FL2({s. \<exists>\<beta> A a. \<beta> &\<^sub>\<F>\<^sub>\<L> \<langle>A\<rangle>\<^sub>\<F>\<^sub>\<L> \<in> P \<and> a \<in>\<^sub>\<F>\<^sub>\<L> A \<and> s = \<beta> &\<^sub>\<F>\<^sub>\<L> \<langle>(\<bullet>,a)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>})"

lemma mkFL12_is_FL2: 
  assumes "FL1 P"
  shows "FL1(mkFL120(P))"
  using assms unfolding mkFL120_def FL1_def apply safe
   apply blast
  apply (case_tac A, safe)
    apply (metis amember.simps(1))
  apply (rule_tac x="\<beta>" in exI, rule_tac x="[x2]\<^sub>\<F>\<^sub>\<L>" in exI, rule_tac x="a" in exI)
  apply (case_tac ta, safe)
  
  apply (metis acceptance.exhaust acceptance_set assms bullet_right_zero2 less_eq_acceptance.simps(3) less_eq_fltrace.simps(2) x_le_concat2_FL1)
  apply (case_tac x21, safe, case_tac aa, safe)
    apply (meson amember.simps(1))
   apply (case_tac x22, safe, case_tac x1, safe)
  apply (rule_tac x="\<langle>([x2a]\<^sub>\<F>\<^sub>\<L>,b)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>" in exI, safe)
  sledgehammer
  apply safe
   apply (case_tac "\<beta> &\<^sub>\<F>\<^sub>\<L> \<langle>([x2]\<^sub>\<F>\<^sub>\<L>,a)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L> \<in> P")

  apply (case_tac "\<beta> &\<^sub>\<F>\<^sub>\<L> \<langle>(\<bullet>,a)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L> \<in> P")


lemma
  assumes "s \<notin> P" "FL1 P"
       "s \<le> \<beta> &\<^sub>\<F>\<^sub>\<L> \<langle>([x2]\<^sub>\<F>\<^sub>\<L>,a)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>"
       "\<beta> &\<^sub>\<F>\<^sub>\<L> \<langle>[x2]\<^sub>\<F>\<^sub>\<L>\<rangle>\<^sub>\<F>\<^sub>\<L> \<in> P"
       "a \<in>\<^sub>\<F>\<^sub>\<L> [x2]\<^sub>\<F>\<^sub>\<L>"
     shows "(s = \<beta> &\<^sub>\<F>\<^sub>\<L> \<langle>([x2]\<^sub>\<F>\<^sub>\<L>,a)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L> \<or> s = \<beta> &\<^sub>\<F>\<^sub>\<L> \<langle>(\<bullet>,a)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>)"
  nitpick


lemma
  assumes "s \<le> \<beta> &\<^sub>\<F>\<^sub>\<L> \<langle>([x2]\<^sub>\<F>\<^sub>\<L>,a)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>" "s \<noteq> \<beta> &\<^sub>\<F>\<^sub>\<L> \<langle>(\<bullet>,a)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>" "\<not> s \<le> \<beta> &\<^sub>\<F>\<^sub>\<L> \<langle>[x2]\<^sub>\<F>\<^sub>\<L>\<rangle>\<^sub>\<F>\<^sub>\<L>"
  shows "s = \<beta> &\<^sub>\<F>\<^sub>\<L> \<langle>([x2]\<^sub>\<F>\<^sub>\<L>,a)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>" nitpick

definition mkFL12 :: "'a fltraces \<Rightarrow> 'a fltraces" where
"mkFL12 P \<equiv> P \<union> {s. \<exists>\<beta> A a. \<beta> &\<^sub>\<F>\<^sub>\<L> \<langle>A\<rangle>\<^sub>\<F>\<^sub>\<L> \<in> P \<and> a \<in>\<^sub>\<F>\<^sub>\<L> A \<and> s \<le> \<beta> &\<^sub>\<F>\<^sub>\<L> \<langle>(A,a)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>}"

lemma mkFL12_disj_univ: "mkFL12 (\<Union> P) = \<Union> ({mkFL12(x)|x. x \<in> P})"
  unfolding mkFL12_def by auto

lemma mkFL12_is_FL2: 
  assumes "FL1 P"
  shows "FL1(mkFL12(P))"
  using assms unfolding mkFL12_def FL1_def apply safe
  apply blast
  using order_trans by blast

lemma mkFL12_is_FL2: "FL2(mkFL12(P))"
  unfolding mkFL12_def FL2_def apply auto
  apply (case_tac A, auto, case_tac Aa, auto)
  
  apply (metis Finite_Linear_Model.last.simps(1) amember.simps(1) concat_FL_last_not_bullet_absorb last_bullet_then_last_cons last_cons_bullet_iff)
  by (metis acceptance.exhaust amember.simps(1) concat_FL_last_not_bullet_absorb last_cons_acceptance_not_bullet last_cons_bullet_iff)

lemma
  fixes x ::"'a::order"
  assumes "x \<le> b" "c < b" "\<not>x \<le> c" "x \<noteq> c" "\<not>(\<exists>z. c < z \<and> z < b)"
  shows "b \<le> x"
  using assms nitpick
  
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

lemma
  shows "\<not>(\<exists>z. \<beta> &\<^sub>\<F>\<^sub>\<L> \<langle>A\<rangle>\<^sub>\<F>\<^sub>\<L> < z \<and> z < \<beta> &\<^sub>\<F>\<^sub>\<L> \<langle>(A,a)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>)"
  using fltrace_less_imp_not_less
  by (simp add: fltrace_less_imp_not_less)

lemma
  

lemma
  assumes "FL1 P" "x \<notin> P" "x \<le> b" "c \<in> P" "c \<le> b" "\<not>(\<exists>z. c < z \<and> z < b)"
  shows "x = b"
proof -
  have "\<forall>y. y \<le> c \<longrightarrow> y \<in> P"
    using FL1_def assms(1) assms(4) by blast
  then have "\<forall>y. y \<le> c \<longrightarrow> x \<noteq> y"
    using assms(2) by blast
  then have "\<not> x \<le> c" "x \<noteq> c"
    apply blast
    using assms(2) assms(4) by blast
  then have "b \<le> x"
    nitpick
    by (metis assms(3) assms(5) assms(6) eq_iff order.not_eq_order_implies_strict)
    using assms(3) by blast
    using assms(3) by blast

lemma order_no_intermediate_imp_eq:
  fixes x ::"'a::order"
  assumes "\<forall>y. y \<le> c \<longrightarrow> x \<noteq> y" "c \<le> x" "x \<le> b" "\<not>(\<exists>z. c < z \<and> z < b)" 
  shows "b \<le> x"
  using assms apply auto 
  using dual_order.order_iff_strict by blast

lemma
  fixes a :: "'a::{order,plus}"
  assumes "\<forall>a b c. (a \<le> c \<and> b \<le> c) \<longrightarrow> (a \<le> b \<or> b \<le> a)" "\<forall>a c. (\<exists>b. a + b = c) \<longleftrightarrow> a \<le> c"
  shows "a \<le> b + c \<longrightarrow> a \<le> b \<or> b \<le> a"
  using assms oops

lemma
  fixes x :: "'a fltrace"
  assumes "\<beta> &\<^sub>\<F>\<^sub>\<L> \<langle>A\<rangle>\<^sub>\<F>\<^sub>\<L> \<le> \<beta> &\<^sub>\<F>\<^sub>\<L> \<langle>(A,a)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>" "x \<le> \<beta> &\<^sub>\<F>\<^sub>\<L> \<langle>(A,a)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>" "\<not> x \<le> \<beta> &\<^sub>\<F>\<^sub>\<L> \<langle>A\<rangle>\<^sub>\<F>\<^sub>\<L>"
  shows "\<beta> &\<^sub>\<F>\<^sub>\<L> \<langle>A\<rangle>\<^sub>\<F>\<^sub>\<L> \<le> x"
  nitpick

lemma
  fixes x :: "'a fltrace"
  assumes "x \<le> \<beta> &\<^sub>\<F>\<^sub>\<L> \<langle>(\<bullet>,a)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>" "\<not> x \<le> \<beta> &\<^sub>\<F>\<^sub>\<L> \<langle>A\<rangle>\<^sub>\<F>\<^sub>\<L>" "A \<noteq> \<bullet>" "\<not>(\<exists>z. \<beta> &\<^sub>\<F>\<^sub>\<L> \<langle>A\<rangle>\<^sub>\<F>\<^sub>\<L> < z \<and> z < \<beta> &\<^sub>\<F>\<^sub>\<L> \<langle>(\<bullet>,a)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>)"
  shows "\<beta> &\<^sub>\<F>\<^sub>\<L> \<langle>A\<rangle>\<^sub>\<F>\<^sub>\<L> \<le> x"
  using assms 

lemma fltrace_consFL_less_eq_case:
  assumes "a \<in>\<^sub>\<F>\<^sub>\<L> A \<or> A = \<bullet>"
  shows "x &\<^sub>\<F>\<^sub>\<L> \<langle>A\<rangle>\<^sub>\<F>\<^sub>\<L> \<le> x &\<^sub>\<F>\<^sub>\<L> \<langle>(A,a)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>"
  using assms
  apply (induct x, auto)
   apply (case_tac x, auto)
   apply (cases A, auto)
  by (case_tac x, auto)

lemma
  assumes "FL1 P"
  shows "FL1({s. \<exists>\<beta> A a. \<beta> &\<^sub>\<F>\<^sub>\<L> \<langle>A\<rangle>\<^sub>\<F>\<^sub>\<L> \<in> P \<and> a \<in>\<^sub>\<F>\<^sub>\<L> A \<and> s \<le> \<beta> &\<^sub>\<F>\<^sub>\<L> \<langle>(A,a)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>})"
  using assms unfolding FL1_def apply safe
   apply (rule_tac x="\<beta>" in exI, rule_tac x="A" in exI, rule_tac x="a" in exI)
   apply safe
  sledgehammer
  using fltrace_trans by blast

lemma FL1_mkFL12:
  assumes "FL1 P"
  shows "FL1(mkFL12(P))"
proof -
  have "FL1({s. \<exists>\<beta> A a. \<beta> &\<^sub>\<F>\<^sub>\<L> \<langle>A\<rangle>\<^sub>\<F>\<^sub>\<L> \<in> P \<and> a \<in>\<^sub>\<F>\<^sub>\<L> A \<and> (s = \<beta> &\<^sub>\<F>\<^sub>\<L> \<langle>(A,a)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L> \<or> s = \<beta> &\<^sub>\<F>\<^sub>\<L> \<langle>(\<bullet>,a)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>)})"
    unfolding mkFL12_def by auto
  also have "... = FL1({s. \<exists>\<beta> A a. \<beta> &\<^sub>\<F>\<^sub>\<L> \<langle>A\<rangle>\<^sub>\<F>\<^sub>\<L> \<in> P \<and> a \<in>\<^sub>\<F>\<^sub>\<L> A \<and> (s = \<beta> &\<^sub>\<F>\<^sub>\<L> \<langle>(A,a)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L> \<or> s = \<beta> &\<^sub>\<F>\<^sub>\<L> \<langle>(\<bullet>,a)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>)})"
    using assms sledgehammer
  using assms unfolding mkFL12_def FL1_def 
 
  
  apply safe
  
  using FL1_def apply blast
   apply (rule_tac x="\<beta>" in exI, rule_tac x="A" in exI, rule_tac x="a" in exI)
  sledgehammer
  apply (rule_tac x="a" in exI, auto)

lemma
  assumes "\<forall>y. y \<le> \<beta> &\<^sub>\<F>\<^sub>\<L> \<langle>A\<rangle>\<^sub>\<F>\<^sub>\<L> \<longrightarrow> x \<noteq> y" "x \<le> \<beta> &\<^sub>\<F>\<^sub>\<L> \<langle>(\<bullet>,a)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>" "\<beta> &\<^sub>\<F>\<^sub>\<L> \<langle>A\<rangle>\<^sub>\<F>\<^sub>\<L> \<in> P" "a \<in>\<^sub>\<F>\<^sub>\<L> A"
  shows "\<beta> &\<^sub>\<F>\<^sub>\<L> \<langle>(\<bullet>,a)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L> \<le> x" nitpick
  using assms apply (induct x , auto)
  apply (induct \<beta>, auto)
   apply (case_tac xa, auto)
  apply (cases \<beta>, auto)
   apply (cases \<beta>, auto)
   apply (cases A, auto, case_tac x1, auto)
  apply (induct \<beta>, auto)
  
  apply (metis Finite_Linear_Model.last.simps(1) bullet_right_zero2 concat_FL_last_not_bullet_absorb fltrace.distinct(1) fltrace_concat2.simps(3) plus_acceptance.elims x_le_x_concat2 xs_less_eq_z_two_only)
  sledgehammer apply (case_tac x1a, auto)
  apply (metis FL1_def Finite_Linear_Model.last.simps(1) assms(4) bullet_left_zero2 concat_FL_last_not_bullet_absorb x_le_x_concat2 xs_less_eq_z_two_only)
    
   apply (metis FL_cons_acceptance acceptance.distinct(1) less_eq_acceptance.elims(2))
sledgehammer
     apply (smt FL_cons_acceptance acceptance.distinct(1) bullet_right_zero2 first.simps(1) fltrace.distinct(1) fltrace.inject(2) fltrace_concat2.simps(2) fltrace_induct fltrace_trans less_eq_acceptance.elims(2) less_eq_fltrace.elims(2) x_le_x_concat2 xs_less_eq_z_two_only)
  apply (smt FL_cons_acceptance acceptance.distinct(1) acceptance_set bullet_right_zero2 first.simps(1) first.simps(2) fltrace.distinct(1) fltrace_concat2.simps(2) fltrace_concat2.simps(3) fltrace_consFL_less_eq_case less_eq_acceptance.elims(2) less_eq_fltrace.elims(2) x_le_concat2_FL1)
proof -
  have "\<forall>y. y \<le> \<beta> &\<^sub>\<F>\<^sub>\<L> \<langle>A\<rangle>\<^sub>\<F>\<^sub>\<L> \<longrightarrow> y \<in> P"
    using FL1_def assms(1) assms(4) by blast
  then have a:"\<forall>y. y \<le> \<beta> &\<^sub>\<F>\<^sub>\<L> \<langle>A\<rangle>\<^sub>\<F>\<^sub>\<L> \<longrightarrow> x \<noteq> y"
    using assms(2) by blast
  then have b:"\<not> x \<le> \<beta> &\<^sub>\<F>\<^sub>\<L> \<langle>A\<rangle>\<^sub>\<F>\<^sub>\<L>" "x \<noteq> \<beta> &\<^sub>\<F>\<^sub>\<L> \<langle>A\<rangle>\<^sub>\<F>\<^sub>\<L>"
    apply blast
    using assms(2) assms(4) by blast
  then have c:"\<not>(\<exists>z. \<beta> &\<^sub>\<F>\<^sub>\<L> \<langle>A\<rangle>\<^sub>\<F>\<^sub>\<L> < z \<and> z < \<beta> &\<^sub>\<F>\<^sub>\<L> \<langle>(\<bullet>,a)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>)"
    apply auto
    by (simp add: fltrace_less_imp_not_less')
  then show ?thesis sledgehammer

  {assume "\<beta> &\<^sub>\<F>\<^sub>\<L> \<langle>A\<rangle>\<^sub>\<F>\<^sub>\<L> \<le> x"
  then have "\<beta> &\<^sub>\<F>\<^sub>\<L> \<langle>(\<bullet>,a)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L> \<le> x"
    using order_no_intermediate_imp_eq a c assms(3) by }

  assume "\<not> \<beta> &\<^sub>\<F>\<^sub>\<L> \<langle>A\<rangle>\<^sub>\<F>\<^sub>\<L> \<le> x"
  then have "\<not> \<beta> &\<^sub>\<F>\<^sub>\<L> \<langle>A\<rangle>\<^sub>\<F>\<^sub>\<L> < x"
    by (simp add: less_le)
  then have "\<not> x \<le> \<beta> &\<^sub>\<F>\<^sub>\<L> \<langle>(A,a)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>"
    
    using a b c 

lemma
  assumes "FL1 P" "\<not> x \<le> \<beta> &\<^sub>\<F>\<^sub>\<L> \<langle>A\<rangle>\<^sub>\<F>\<^sub>\<L>" "x \<le> \<beta> &\<^sub>\<F>\<^sub>\<L> \<langle>(\<bullet>,a)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>"  "a \<in>\<^sub>\<F>\<^sub>\<L> A"
  shows "x = \<beta> &\<^sub>\<F>\<^sub>\<L> \<langle>(\<bullet>,a)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>"
  using assms apply (case_tac "last \<beta> \<noteq> \<bullet>", auto)
  
   apply (simp add: concat_FL_last_not_bullet_absorb)
  sledgehammer
  using assms apply (induct x arbitrary:\<beta>, auto)
   apply (case_tac xa, auto)
  
    apply (metis bullet_left_zero2 x_le_x_concat2)
   apply (cases A, auto)
   apply (case_tac \<beta>, auto, case_tac x1, auto)
  apply (case_tac x1a, auto, case_tac aa, auto)
apply (case_tac \<beta>, auto, case_tac x1, auto)
   apply (case_tac xa, auto)

  apply (metis Finite_Linear_Model.last.simps(1) acceptance.distinct(1) acceptance.exhaust acceptance_set bullet_left_zero2 concat_FL_last_not_bullet_absorb less_eq_acceptance.simps(2) less_eq_acceptance.simps(3) less_eq_fltrace.simps(1) less_eq_fltrace.simps(2))
   apply (cases A, auto)
  apply (case_tac xa, auto, case_tac y, auto)
  
     apply (metis acceptance_set aevent_less_eq_iff_components amember.simps(1))
    apply (case_tac aa,auto)
  
    apply (simp add: aevent_less_eq_iff_components)
   apply (case_tac y, auto, case_tac aa, auto)
  


lemma
  assumes "FL1 P" "x \<notin> P" "x \<le> \<beta> &\<^sub>\<F>\<^sub>\<L> \<langle>(A,a)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>" "\<beta> &\<^sub>\<F>\<^sub>\<L> \<langle>A\<rangle>\<^sub>\<F>\<^sub>\<L> \<in> P" "a \<in>\<^sub>\<F>\<^sub>\<L> A"
  shows "x = \<beta> &\<^sub>\<F>\<^sub>\<L> \<langle>(A,a)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L> \<or> x = \<beta> &\<^sub>\<F>\<^sub>\<L> \<langle>(\<bullet>,a)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>"
proof -
  have "\<forall>y. y \<le> \<beta> &\<^sub>\<F>\<^sub>\<L> \<langle>A\<rangle>\<^sub>\<F>\<^sub>\<L> \<longrightarrow> y \<in> P"
    using FL1_def assms(1) assms(4) by blast
  then have a:"\<forall>y. y \<le> \<beta> &\<^sub>\<F>\<^sub>\<L> \<langle>A\<rangle>\<^sub>\<F>\<^sub>\<L> \<longrightarrow> x \<noteq> y"
    using assms(2) by blast
  then have b:"\<not> x \<le> \<beta> &\<^sub>\<F>\<^sub>\<L> \<langle>A\<rangle>\<^sub>\<F>\<^sub>\<L>" "x \<noteq> \<beta> &\<^sub>\<F>\<^sub>\<L> \<langle>A\<rangle>\<^sub>\<F>\<^sub>\<L>"
    apply blast
    using assms(2) assms(4) by blast
  then have c:"\<not>(\<exists>z. \<beta> &\<^sub>\<F>\<^sub>\<L> \<langle>A\<rangle>\<^sub>\<F>\<^sub>\<L> < z \<and> z < \<beta> &\<^sub>\<F>\<^sub>\<L> \<langle>(A,a)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>)"
    apply auto
    by (simp add: fltrace_less_imp_not_less)
  have "\<beta> &\<^sub>\<F>\<^sub>\<L> \<langle>A\<rangle>\<^sub>\<F>\<^sub>\<L> \<le> \<beta> &\<^sub>\<F>\<^sub>\<L> \<langle>(A,a)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>"
    by (simp add: fltrace_consFL_less_eq_case assms(5))
  have "\<beta> &\<^sub>\<F>\<^sub>\<L> \<langle>(\<bullet>,a)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L> \<le> x"
    sledgehammer
  {assume "\<beta> &\<^sub>\<F>\<^sub>\<L> \<langle>A\<rangle>\<^sub>\<F>\<^sub>\<L> \<le> x"
  then have "\<beta> &\<^sub>\<F>\<^sub>\<L> \<langle>(A,a)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L> \<le> x"
    using order_no_intermediate_imp_eq a c assms(3) }

  assume "\<not> \<beta> &\<^sub>\<F>\<^sub>\<L> \<langle>A\<rangle>\<^sub>\<F>\<^sub>\<L> \<le> x"
  then have "\<not> \<beta> &\<^sub>\<F>\<^sub>\<L> \<langle>A\<rangle>\<^sub>\<F>\<^sub>\<L> < x"
    by (simp add: less_le)
  then have "\<not> x \<le> \<beta> &\<^sub>\<F>\<^sub>\<L> \<langle>(A,a)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>"
    
    using a b c 
    using \<open>\<beta> &\<^sub>\<F>\<^sub>\<L> \<langle>A\<rangle>\<^sub>\<F>\<^sub>\<L> \<le> x\<close> by blast
  (* x \<le> b \<and> \<not> x \<le> c \<and> c \<le> b \<longrightarrow> x = b*)

(*
lemma FL1_mkFL2:
  assumes "FL1 P"
  shows "FL1(mkFL2(P))"
  using assms unfolding mkFL2_def FL1_def 
 
  
  apply safe
  
  using FL1_def apply blast
  apply (rule_tac x="\<beta>" in exI, rule_tac x="A" in exI, auto)
  apply (rule_tac x="a" in exI, auto)
  *)
lemma FL3_union_imp_dist:
  assumes "FL3 (P \<union> Q)"
  shows "FL3 P"
  using assms unfolding FLTick0_def by auto

lemma FL3_mkFL2:
  assumes "FL3 X"
  shows "FL3 (mkFL2 X)"
  using assms unfolding mkFL2_def  apply auto
  by (smt FLTick0_def Un_iff mem_Collect_eq tickWF_acceptance_imp_tickWF_consFL)

lemma FL3_mkFL12:
  assumes "FL3 X"
  shows "FL3 (mkFL12 X)"
  using assms unfolding mkFL12_def FLTick0_def apply auto
   apply (simp add: tickWF_acceptance_imp_tickWF_consFL)
  by (metis (no_types, lifting) bullet_right_zero2 concat_FL_last_not_bullet_absorb fltrace_concat.simps(3) last_bullet_concatmix tickWF_concatFL_imp tickWF_consFL_notin_prefix tickWF_imp_prefix x_le_x_concat2)


lemma FL1_mkFL2:
  "FL1(mkFL2 X)"
  unfolding mkFL2_def FL1_def apply auto
  sorry

lemma FL1_mkFL12:
  "FL1(mkFL12 X)"
  unfolding mkFL12_def FL1_def apply auto
  sledgehammer
  sorry

lemma ttm2fl_alt:
  assumes "TTM1 P" "TTM2 P" "TT1w P" "FL2 (ttm2fl P)"
  shows "ttm2fl P = \<Union>{fl. FLTick0 Tick fl \<and> FL2 fl \<and> FL1 fl \<and> (fl2ttm fl) \<subseteq> P}"
  using assms unfolding ttm2fl_def fl2ttm_def apply auto
  apply (rule_tac x="mkFL12 X" in exI, auto)
  using FL3_mkFL12 apply blast
  using mkFL12_is_FL2 apply blast
  using FL1_mkFL12 apply blast
  unfolding mkFL12_def apply auto
  using FL2_def Un_iff mem_Collect_eq mem_simps(9) mkFL2_def subset_eq
   apply (smt fl2ttobs_for_FL2_imp)
  using fl2ttobs_for_FL2_imp by blast
 (* by (smt FL2_def Un_iff mem_Collect_eq mem_simps(9) mkFL2_def subset_eq)+*)

lemma ttm2fl_alt':
  assumes "TTM1 P" "TTM2 P" "TT1w P"
  shows "ttm2fl P = \<Union>{fl. FLTick0 Tick fl \<and> FL2 fl \<and> FL1 fl \<and> (fl2ttm fl) \<subseteq> P}"
proof -
  have "FL2 (ttm2fl P)"
    using assms by (simp add:FL2_ttm2fl)
  then show ?thesis
    using assms ttm2fl_alt by blast
qed

end