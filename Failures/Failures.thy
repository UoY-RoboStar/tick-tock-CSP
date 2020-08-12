theory Failures

imports
 Main
 Failures_Core
 Failures_BasicOps
begin

text \<open> The conjecture here is that there is a Galois connection between the F4 superset, and 
       a subset that doesn't observe it necessarily. \<close>

definition sf2f :: "'a process \<Rightarrow> 'a process"
  where "sf2f P = \<Sqinter>{Q. T0 Q \<and> T1 Q \<and> T2 Q \<and> F2 Q \<and> F3 Q \<and> P \<sqsubseteq> (mkF24 Q)}"

text \<open> The following function is the actual one that matters. \<close>

definition sf25f :: "'a process \<Rightarrow> 'a process"
  where "sf25f P = \<Sqinter>{Q. T0 Q \<and> T1 Q \<and> T2 Q \<and> F2 Q \<and> F3 Q \<and> F5 Q \<and> F6 Q \<and> P \<sqsubseteq> (mkF24 Q)}"

definition unmkF25 :: "'a process \<Rightarrow> 'a process"
  where "unmkF25 P = \<Sqinter>{Q. T0 Q \<and> T1 Q \<and> T2 Q \<and> F2 Q \<and> F3 Q \<and> P \<sqsubseteq> (mkF25 Q)}"

lemma sf2f_mono:
  assumes "P \<sqsubseteq> Q"
  shows "sf2f P \<sqsubseteq> sf2f Q"
  using assms unfolding sf2f_def IntChoice_def apply auto
  by (smt SUP_least UN_I mem_Collect_eq prod.sel(1) prod.sel(2) refines_def refines_tran subsetI)

lemma mkF24_mono:
  assumes "P \<sqsubseteq> Q"
  shows "mkF24 P \<sqsubseteq> mkF24 Q"
  using assms unfolding mkF24_def traces_def refines_def by auto

text \<open> Key theorem would be to show that applying mkF24 and sf2f yields the same? \<close>

lemma T1_dist_IntChoice_two_imp:
  assumes "T1 P" "T1 Q"
  shows "T1 (\<Sqinter>{P,Q})"
  using assms unfolding IntChoice_def apply auto
  unfolding T1_def traces_def by auto

lemma T0_closed_intChoice:
  assumes "T0 P" "T0 Q"
  shows "T0 (P \<sqinter> Q)"
  using assms unfolding intChoice_def T0_def traces_def by auto

lemma T1_closed_intChoice:
  assumes "T1 P" "T1 Q"
  shows "T1 (P \<sqinter> Q)"
  using assms unfolding intChoice_def T1_def traces_def by auto

lemma T2_closed_intChoice:
  assumes "T2 P" "T2 Q"
  shows "T2 (P \<sqinter> Q)"
  using assms unfolding intChoice_def T2_def traces_def by auto

lemma F2_closed_intChoice:
  assumes "F2 P" "F2 Q"
  shows "F2 (P \<sqinter> Q)"
  using assms unfolding intChoice_def F2_def traces_def by auto

lemma F3_closed_intChoice:
  assumes "F3 P" "F3 Q"
  shows "F3 (P \<sqinter> Q)"
  using assms unfolding intChoice_def F3_def traces_def apply auto
  by (metis (mono_tags, lifting) Int_Collect Int_emptyI emptyE mem_Collect_eq)+

lemma T1_IntChoice_dist_two_imp:
  assumes "T1 (\<Sqinter>{P,Q})"
  shows "T1 P \<or> T1 Q" 
  using assms unfolding IntChoice_def apply auto
  unfolding T1_def traces_def 
  oops

lemma T0_dist_IntChoice:
  assumes "T0`S = {True}"
  shows "T0 (\<Sqinter>S)"
  using assms unfolding IntChoice_def T0_def traces_def by auto

lemma T1_dist_IntChoice:
  assumes "T1`S = {True}"
  shows "T1 (\<Sqinter>S)"
  using assms unfolding IntChoice_def T1_def traces_def apply safe
   apply auto[1]
  by (smt UN_iff imageI mem_Collect_eq singleton_conv2 snd_conv)

lemma T2_closed_IntChoice:
  assumes "T2`S = {True}"
  shows "T2 (\<Sqinter>S)"
  using assms unfolding IntChoice_def 
  by (smt T2_def UN_iff fst_conv image_iff singleton_iff snd_conv traces_def)

lemma F2_closed_IntChoice:
  assumes "F2`S = {True}"
  shows "F2 (\<Sqinter>S)"
  using assms unfolding IntChoice_def 
  by (smt F2_def UN_iff fst_conv image_iff singleton_iff snd_conv traces_def)

lemma F3_closed_IntChoice:
  assumes "F3`S = {True}"
  shows "F3 (\<Sqinter>S)"
  using assms unfolding IntChoice_def F3_def apply safe
  unfolding traces_def apply simp
  by blast

lemma F5_closed_IntChoice:
  assumes "F5`S = {True}"
  shows "F5 (\<Sqinter>S)"
  using assms unfolding IntChoice_def F5_def apply safe
  unfolding traces_def apply simp
  by blast

lemma F6_closed_IntChoice:
  assumes "F6`S = {True}"
  shows "F6 (\<Sqinter>S)"
  using assms unfolding IntChoice_def F6_def apply safe
  unfolding traces_def apply simp
  by blast

lemma 
  assumes "traces(P) \<noteq> {}"
  shows "traces(sf2f P) \<noteq> {}"
  using assms unfolding sf2f_def traces_def apply auto
  oops

abbreviation remTraceTick :: "'a trace \<Rightarrow> 'a trace" where
"remTraceTick s == filter (\<lambda>x. x\<noteq>tick) s"

definition remTick :: "'a process \<Rightarrow> 'a process" where
"remTick P = (fst P,remTraceTick`snd P)"

lemma Tick_last_prefix_remTraceTick:
  assumes "Tick_last t"
  shows "prefix (remTraceTick t) t"
  using assms by(induct rule:Tick_last.induct, auto)

lemma remTraceTick_no_last_tick:
  "s @ [tick] \<noteq> remTraceTick x"
  apply (induct s, auto)
  apply (induct x, auto)
   apply (metis (mono_tags, lifting) filter_eq_ConsD list.inject)
  apply (induct x, auto)
  by (smt append.simps(1) append.simps(2) filter_eq_ConsD hd_Cons_tl list.inject not_Cons_self2)

lemma mkF24_remTick_refines:
  assumes "T0 P" "T1 P" "T2 P" "F2 P" "F3 P"
  shows "P \<sqsubseteq> mkF24(remTick(P))"
  apply (rule refines_rule)
  using assms unfolding remTick_def mkF24_def traces_def apply auto
  using remTraceTick_no_last_tick apply blast
  using remTraceTick_no_last_tick apply blast
  using T0_def T1_def Tick_last_prefix_remTraceTick traces_def by blast

lemma Tick_last_remTraceTick:
  "Tick_last (remTraceTick x)"
  apply (induct x, auto)
  by (case_tac a, auto)
  
lemma T0_remTick:
  assumes "T0 P"
  shows "T0 (remTick(P))"
  using assms unfolding T0_def traces_def remTick_def using Tick_last_remTraceTick by auto

lemma T0_remTick:
  assumes "T1 P" "T0 P"
  shows "T1 (remTick(P))"
  using assms unfolding T0_def T1_def traces_def remTick_def oops

lemma always_refines_Div:
  assumes "T1 P" 
  shows "\<exists>Q. T0 Q \<and> T1 Q \<and> T2 Q \<and> F2 Q \<and> F3 Q \<and> F5 Q \<and> F6 Q \<and> P \<sqsubseteq> mkF24 Q"
  using assms Div_top 
  by (metis F2_Div F3_Div F4_Div F5_Div F6_Div T0_Div T1_Div T2_Div mkF24_fixpoint_imp)

lemma always_refines_F5_Div:
  assumes "T1 P" 
  shows "\<exists>Q. T0 Q \<and> T1 Q \<and> T2 Q \<and> F2 Q \<and> F3 Q \<and> F5 Q \<and> F6 Q \<and> P \<sqsubseteq> mkF24 Q"
  using assms Div_top
  by (metis F2_Div F3_Div F4_Div F5_Div F6_Div T0_Div T1_Div T2_Div mkF24_fixpoint_imp)

lemma T1_sf2f_ran:
  assumes "T0 P" "T1 P" "T2 P" "F2 P" "F3 P" "F4 P"
  shows "T1`{Q. T0 Q \<and> T1 Q \<and> T2 Q \<and> F2 Q \<and> F3 Q \<and> P \<sqsubseteq> mkF24 Q} = {True}"
  using assms apply auto
  using always_refines_Div by fastforce

lemma T0_sf2f_ran:
  assumes "T0 P" "T1 P" "T2 P" "F2 P" "F3 P" "F4 P"
  shows "T0`{Q. T0 Q \<and> T1 Q \<and> T2 Q \<and> F2 Q \<and> F3 Q \<and> P \<sqsubseteq> mkF24 Q} = {True}"
  using assms apply auto
  using always_refines_Div by fastforce

lemma T2_sf2f_ran:
  assumes "T0 P" "T1 P" "T2 P" "F2 P" "F3 P" "F4 P"
  shows "T2`{Q. T0 Q \<and> T1 Q \<and> T2 Q \<and> F2 Q \<and> F3 Q \<and> P \<sqsubseteq> mkF24 Q} = {True}"
  using assms apply auto
  using always_refines_Div by fastforce

lemma F2_sf2f_ran:
  assumes "T0 P" "T1 P" "T2 P" "F2 P" "F3 P" "F4 P"
  shows "F2`{Q. T0 Q \<and> T1 Q \<and> T2 Q \<and> F2 Q \<and> F3 Q \<and> P \<sqsubseteq> mkF24 Q} = {True}"
  using assms apply auto
  using always_refines_Div by fastforce

lemma F3_sf2f_ran:
  assumes "T0 P" "T1 P" "T2 P" "F2 P" "F3 P" "F4 P"
  shows "F3`{Q. T0 Q \<and> T1 Q \<and> T2 Q \<and> F2 Q \<and> F3 Q \<and> P \<sqsubseteq> mkF24 Q} = {True}"
  using assms apply auto
  using always_refines_Div by fastforce

(* sf25 below *)

lemma T1_sf25f_ran:
  assumes "T1 P" 
  shows "T1`{Q. T0 Q \<and> T1 Q \<and> T2 Q \<and> F2 Q \<and> F3 Q \<and> F5 Q \<and> F6 Q \<and> P \<sqsubseteq> mkF24 Q} = {True}"
  using assms apply auto
  using always_refines_F5_Div by fastforce

lemma T0_sf25f_ran:
  assumes "T1 P"
  shows "T0`{Q. T0 Q \<and> T1 Q \<and> T2 Q \<and> F2 Q \<and> F3 Q \<and> F5 Q \<and> F6 Q \<and> P \<sqsubseteq> mkF24 Q} = {True}"
  using assms apply auto
  using always_refines_F5_Div by fastforce

lemma T2_sf25f_ran:
  assumes "T1 P"
  shows "T2`{Q. T0 Q \<and> T1 Q \<and> T2 Q \<and> F2 Q \<and> F3 Q \<and> F5 Q \<and> F6 Q \<and> P \<sqsubseteq> mkF24 Q} = {True}"
  using assms apply auto
  using always_refines_F5_Div by fastforce

lemma F2_sf25f_ran:
  assumes "T1 P"
  shows "F2`{Q. T0 Q \<and> T1 Q \<and> T2 Q \<and> F2 Q \<and> F3 Q \<and> F5 Q \<and> F6 Q \<and> P \<sqsubseteq> mkF24 Q} = {True}"
  using assms apply auto
  using always_refines_F5_Div by fastforce

lemma F3_sf25f_ran:
  assumes "T1 P"
  shows "F3`{Q. T0 Q \<and> T1 Q \<and> T2 Q \<and> F2 Q \<and> F3 Q \<and> F5 Q \<and> F6 Q \<and> P \<sqsubseteq> mkF24 Q} = {True}"
  using assms apply auto
  using always_refines_F5_Div by fastforce

lemma F5_sf25f_ran:
  assumes "T1 P"
  shows "F5`{Q. T0 Q \<and> T1 Q \<and> T2 Q \<and> F2 Q \<and> F3 Q \<and> F5 Q \<and> F6 Q \<and> P \<sqsubseteq> mkF24 Q} = {True}"
  using assms apply auto
  using always_refines_F5_Div by fastforce

lemma F6_sf25f_ran:
  assumes "T1 P"
  shows "F6`{Q. T0 Q \<and> T1 Q \<and> T2 Q \<and> F2 Q \<and> F3 Q \<and> F5 Q \<and> F6 Q \<and> P \<sqsubseteq> mkF24 Q} = {True}"
  using assms apply auto
  using always_refines_F5_Div by fastforce

lemma T1_sf2f:
  assumes "T0 P" "T1 P" "T2 P" "F2 P" "F3 P" "F4 P"
  shows "T1 (sf2f P)"
  using assms unfolding sf2f_def using T1_sf2f_ran
  by (metis (no_types, lifting) Collect_cong T1_dist_IntChoice)

lemma T0_sf2f:
  assumes "T0 P" "T1 P" "T2 P" "F2 P" "F3 P" "F4 P"
  shows "T0 (sf2f P)"
  using assms unfolding sf2f_def using T0_sf2f_ran
  by (metis (no_types, lifting) Collect_cong T0_dist_IntChoice)

lemma T2_sf2f:
  assumes "T0 P" "T1 P" "T2 P" "F2 P" "F3 P" "F4 P"
  shows "T2 (sf2f P)"
  using assms unfolding sf2f_def using T2_sf2f_ran
  by (metis (no_types, lifting) Collect_cong T2_closed_IntChoice)

lemma F3_sf2f:
  assumes "T0 P" "T1 P" "T2 P" "F2 P" "F3 P" "F4 P"
  shows "F3 (sf2f P)"
  using assms unfolding sf2f_def using F3_sf2f_ran
  by (metis (no_types, lifting) Collect_cong F3_closed_IntChoice)

(* sf25 below *)

lemma T1_sf25f:
  assumes "T1 P"
  shows "T1 (sf25f P)"
  using assms unfolding sf25f_def using T1_sf25f_ran
  by (metis (no_types, lifting) Collect_cong T1_dist_IntChoice)

lemma T0_sf25f:
  assumes "T1 P"
  shows "T0 (sf25f P)"
  using assms unfolding sf25f_def using T0_sf25f_ran
  by (metis (no_types, lifting) Collect_cong T0_dist_IntChoice)

lemma T2_sf25f:
  assumes "T1 P"
  shows "T2 (sf25f P)"
  using assms unfolding sf25f_def using T2_sf25f_ran
  by (metis (no_types, lifting) Collect_cong T2_closed_IntChoice)

lemma F3_sf25f:
  assumes "T1 P"
  shows "F3 (sf25f P)"
  using assms unfolding sf25f_def using F3_sf25f_ran
  by (metis (no_types, lifting) Collect_cong F3_closed_IntChoice)

lemma F5_sf25f:
  assumes "T1 P"
  shows "F5 (sf25f P)"
  using assms unfolding sf25f_def using F5_sf25f_ran
  by (metis (no_types, lifting) Collect_cong F5_closed_IntChoice)

lemma F6_sf25f:
  assumes "T1 P"
  shows "F6 (sf25f P)"
  using assms unfolding sf25f_def using F6_sf25f_ran
  by (metis (no_types, lifting) Collect_cong F6_closed_IntChoice)

lemma traces_eq_traces_mkF24:
  shows "traces P = traces (mkF24 P)"
  unfolding traces_def mkF24_def by auto

lemma traces_eq_traces_mkF25:
  shows "traces P = traces (mkF25 P)"
  unfolding traces_def mkF25_def by auto

(*
lemma traces_eq_traces_unmkF25:
  assumes "T0 P" "T1 P" "T2 P" "F2 P" "F3 P" "F4 P"
  shows "traces P \<subseteq> traces (unmkF25 P)"
  using assms
  unfolding unmkF25_def mkF25_def refines_def IntChoice_def traces_def apply auto
  by (smt Collect_cong F4_F2_imp_tick_failures UNIV_I case_prod_conv prod.collapse subsetI)*)

lemma traces_eq_traces_sf2f:
  assumes "T0 P" "T1 P" "T2 P" "F2 P" "F3 P" "F4 P"
  shows "traces P \<subseteq> traces (sf2f P)"
  using assms
  unfolding sf2f_def mkF24_def refines_def IntChoice_def traces_def apply auto
  by (smt Collect_cong F4_F2_imp_tick_failures UNIV_I case_prod_conv prod.collapse subsetI)

lemma T0_empty_failures[simp]:
  assumes "T0 P"
  shows "T0 ({}, snd P)"
  using assms unfolding T0_def traces_def by auto

lemma T1_empty_failures[simp]:
  assumes "T1 P"
  shows "T1({}, snd P)"
  using assms unfolding T1_def traces_def by auto

lemma T2_empty_failures[simp]:
  "T2({}, snd P)"
  unfolding T2_def traces_def by auto

lemma F2_empty_failures[simp]:
  "F2({}, snd P)"
  unfolding F2_def by auto

lemma F3_empty_failures[simp]:
  "F3({}, snd P)"
  unfolding F3_def by auto

lemma F5_empty_failures[simp]:
  "F5({}, snd P)"
  unfolding F5_def by auto

lemma F6_empty_failures[simp]:
  "F6({}, snd P)"
  unfolding F6_def by auto

lemma traces_imp_traces_sf25f:
  assumes "T0 P" "T1 P" "T2 P" "F2 P" "F3 P" "F4 P"
  shows "traces P \<subseteq> traces (sf25f P)"
  using assms
  unfolding sf25f_def IntChoice_def traces_def apply auto
  apply (rule exI[where x="{}"])
  apply (rule exI[where x="snd P"], auto)
  unfolding mkFailuresF5_def mkF24_def traces_def refines_def traces_def apply auto
  apply (metis F2_def F4_def insert_subset traces_def)
  by (metis F2_def F4_def insert_subset subset_UNIV traces_def)

lemma traces_sf25f_imp_traces:
  assumes "T0 P" "T1 P" "T2 P" "F2 P" "F3 P" 
  shows "traces (sf25f P) \<subseteq> traces P"
  using assms
  unfolding sf25f_def mkF24_def refines_def IntChoice_def traces_def by auto

lemma traces_sf2f_eq_traces:
  assumes "T0 P" "T1 P" "T2 P" "F2 P" "F3 P" "F4 P"
  shows "traces (sf2f P) \<subseteq> traces P"
  using assms
  unfolding sf2f_def mkF24_def refines_def IntChoice_def traces_def by auto

lemma traces_sf2f_eq:
  assumes "T0 P" "T1 P" "T2 P" "F2 P" "F3 P" "F4 P"
  shows "traces (sf2f P) = traces P"
  by (simp add: assms(1) assms(2) assms(3) assms(4) assms(5) assms(6) subset_antisym traces_eq_traces_sf2f traces_sf2f_eq_traces)

lemma traces_sf25f_eq:
  assumes "T0 P" "T1 P" "T2 P" "F2 P" "F3 P" "F4 P"
  shows "traces (sf25f P) = traces P"
  by (simp add: antisym assms(1) assms(2) assms(3) assms(4) assms(5) assms(6) traces_imp_traces_sf25f traces_sf25f_imp_traces)

lemma mkF24_sf2f_refined:
  assumes "T0 P" "T1 P" "T2 P" "F2 P" "F3 P" "F4 P" 
  shows "mkF24 (sf2f P) \<sqsubseteq> P"
proof (rule refines_rule)
  show "fst P \<subseteq> fst (mkF24 (sf2f P))"
    using assms unfolding mkF24_def apply auto
    by (smt IntChoice_def UN_I assms(1) assms(2) assms(3) assms(4) assms(5) assms(6) fst_conv le_sup_iff mem_Collect_eq mkF24_def mkF24_fixpoint_imp refines_refl sf2f_def subsetI subset_eq subset_iff traces_eq_traces_mkF24)

  show "snd P \<subseteq> snd (mkF24 (sf2f P))"
    using assms(1) assms(2) assms(3) assms(4) assms(5) assms(6) traces_def traces_eq_traces_mkF24 traces_eq_traces_sf2f by blast
qed

lemma mkF24_sf25f_refines:
  assumes "T0 P" "T1 P" "T2 P" "F2 P" "F3 P" "F4 P" 
  shows "P \<sqsubseteq> mkF24 (sf25f P)"
proof (rule refines_rule)
  show "snd (mkF24 (sf25f P)) \<subseteq> snd P"
   using assms(1) assms(2) assms(3) assms(4) assms(5) traces_def traces_eq_traces_mkF24 traces_sf25f_imp_traces by blast
    
  show "fst (mkF24 (sf25f P)) \<subseteq> fst P"
    unfolding sf25f_def mkF24_def traces_def IntChoice_def apply auto
      apply (simp add: refines_def subset_eq)
        apply (metis (no_types, lifting) F2_def F4_def assms(4) assms(6) insert_Diff insert_subset refines_def snd_conv traces_def)
        by (smt Un_subset_iff case_prodI2 fst_conv mem_Collect_eq refines_def subset_eq)
qed

lemma sf25f_mkF24_refined:
  assumes "T0 P" "T1 P" "T2 P" "F2 P" "F3 P" "F5 P" "F6 P" 
  shows "sf25f (mkF24 P) \<sqsubseteq> P"
proof (rule refines_rule)
  show "snd P \<subseteq> snd (sf25f (mkF24 P))"
    by (metis F2_mkF24 F3_mkF24 F4_mkF24 T0_def T1_mkF24 T2_mkF24 assms(1) assms(2) assms(3) assms(4) assms(5) eq_iff traces_def traces_eq_traces_mkF24 traces_sf25f_eq)

  show "fst P \<subseteq> fst (sf25f (mkF24 P))"
    unfolding sf25f_def mkF24_def traces_def IntChoice_def apply auto
    using assms(1) assms(2) assms(3) assms(4) assms(5) assms(6) assms(7) refines_refl by force
qed

text \<open> The following only holds because cardinality of 'a evt, when not tick is
       non-zero? Otherwise they would map to the same. \<close>

lemma Stop_not_Skip_mkF24: 
  shows "\<not> mkF24 (StopF) \<sqsubseteq> mkF24(SkipUF)"
  unfolding SkipUF_def StopF_def intChoice_def
  unfolding refines_def mkF24_def traces_def by auto

lemma F6_termination_not_F4:
  assumes "F6 P" "\<exists>s. s@[tick] \<in> snd P"
  shows "\<not> F4 P"
  using assms unfolding F6_def F4_def traces_def by auto

lemma F4_termination_not_F6:
  assumes "F4 P" "\<exists>s. s@[tick] \<in> snd P"
  shows "\<not> F6 P"
  using assms unfolding F6_def F4_def traces_def by auto

lemma mkF24_eq_1:
  assumes "(a, b) \<in> fst Q" "(a, b) \<notin> fst P" "(mkF24 P) \<sqsubseteq> (mkF24 Q)" 
  shows "\<exists>s. s @ [tick] \<in> snd P \<and> (a = s \<and> b \<subseteq> UNIV - {tick} \<or> a = s @ [tick])"
  using assms unfolding mkF24_def refines_def traces_def by auto

lemma mkF24_eq_2:
  assumes "(s, b) \<notin> fst P" "s @ [tick] \<in> snd Q" "b \<subseteq> UNIV - {tick}" "(mkF24 P) \<sqsubseteq> (mkF24 Q)"
  shows "\<exists>sa. sa @ [tick] \<in> snd P \<and> (s = sa \<or> s = sa @ [tick])"
  using assms unfolding mkF24_def refines_def traces_def by auto

lemma mkF24_eq_3:
  assumes "(s @ [tick], b) \<notin> fst P" "s @ [tick] \<in> snd Q" "(mkF24 P) \<sqsubseteq> (mkF24 Q)"
  shows "\<exists>sa. sa @ [tick] \<in> snd P \<and> (s @ [tick] = sa \<and> b \<subseteq> UNIV - {tick} \<or> s = sa)"
  using assms unfolding mkF24_def refines_def traces_def by auto

lemma F235_mkF24_rev_mono:
  assumes "(mkF24 P) \<sqsubseteq> (mkF24 Q)" "F2 Q" "F5 Q" "F6 Q" "F2 P" "F5 P" "F6 P"
  shows "fst Q \<subseteq> fst P"
proof -

  have Q_mkF25: "Q = mkF25 Q"
    by (simp add: F5_F2_imp_mkF25_fixpoint assms)

  have P_mkF25: "P = mkF25 P"
    by (simp add: F5_F2_imp_mkF25_fixpoint assms)

   have "fst (mkF25 Q) \<subseteq> fst (mkF25 P)"
      unfolding mkF25_def traces_def apply auto
      using assms mkF24_eq_1 
      using F5_def F6_def by blast+

   then have "fst Q \<subseteq> fst P"
     using Q_mkF25 P_mkF25 by auto

   then show ?thesis .
 qed

lemma sf25f_mkF24_refines:
  assumes "T0 P" "T1 P" "T2 P" "F2 P" "F3 P" "F5 P" "F6 P" 
  shows "P \<sqsubseteq> sf25f (mkF24 P)"
proof (rule refines_rule)
  show "snd (sf25f (mkF24 P)) \<subseteq> snd P"
    by (metis F2_mkF24 F3_mkF24 F4_mkF24 T0_def T1_mkF24 T2_mkF24 assms(1) assms(2) assms(3) assms(4) assms(5) eq_iff traces_def traces_eq_traces_mkF24 traces_sf25f_eq)
   
  show "fst (sf25f (mkF24 P)) \<subseteq> fst P"
  proof -
    have fst_sf25f:"fst (sf25f (mkF24 P)) = {x. \<exists>Q. T0 Q \<and> T1 Q \<and> T2 Q \<and> F2 Q \<and> F3 Q \<and> F5 Q \<and> F6 Q \<and> (mkF24 P) \<sqsubseteq> (mkF24 Q) \<and> x \<in> (fst Q)}"
    proof -
      have "fst (sf25f (mkF24 P)) = fst (\<Sqinter>{Q. T0 Q \<and> T1 Q \<and> T2 Q \<and> F2 Q \<and> F3 Q \<and> F5 Q \<and> F6 Q \<and> (mkF24 P) \<sqsubseteq> (mkF24 Q)})"
        unfolding sf25f_def by auto
      also have "... = \<Union>(fst`{Q. T0 Q \<and> T1 Q \<and> T2 Q \<and> F2 Q \<and> F3 Q \<and> F5 Q \<and> F6 Q \<and> (mkF24 P) \<sqsubseteq> (mkF24 Q)})"
        unfolding IntChoice_def by auto
      also have "... = \<Union>({y. \<exists>x. x \<in> {Q. T0 Q \<and> T1 Q \<and> T2 Q \<and> F2 Q \<and> F3 Q \<and> F5 Q \<and> F6 Q \<and> (mkF24 P) \<sqsubseteq> (mkF24 Q)} \<and> y = (fst x)})"
        by auto
      also have "... = \<Union>({y. \<exists>Q. T0 Q \<and> T1 Q \<and> T2 Q \<and> F2 Q \<and> F3 Q \<and> F5 Q \<and> F6 Q \<and> (mkF24 P) \<sqsubseteq> (mkF24 Q) \<and> y = (fst Q)})"
        by auto (* \<Union>A = {x. \<exists>B \<in> A. x \<in> B} *)
      also have "... = {x. \<exists>B \<in> {y. \<exists>Q. T0 Q \<and> T1 Q \<and> T2 Q \<and> F2 Q \<and> F3 Q \<and> F5 Q \<and> F6 Q \<and> (mkF24 P) \<sqsubseteq> (mkF24 Q) \<and> y = (fst Q)}. x \<in> B}"
        by auto
      also have "... = {x. \<exists>Q. T0 Q \<and> T1 Q \<and> T2 Q \<and> F2 Q \<and> F3 Q \<and> F5 Q \<and> F6 Q \<and> (mkF24 P) \<sqsubseteq> (mkF24 Q) \<and> x \<in> (fst Q)}"
        by auto
      finally show ?thesis .
    qed

    
    have "{x. \<exists>Q. T0 Q \<and> T1 Q \<and> T2 Q \<and> F2 Q \<and> F3 Q \<and> F5 Q \<and> F6 Q \<and> (mkF24 P) \<sqsubseteq> (mkF24 Q) \<and> x \<in> (fst Q)} \<subseteq> fst P"
      using assms F235_mkF24_rev_mono apply auto
      by (smt fst_conv subset_eq F235_mkF24_rev_mono)

    then have "fst (sf25f (mkF24 P)) \<subseteq> fst P"
      using fst_sf25f by auto

    then show ?thesis .
  qed
qed

lemma sf25f_mkF24_eq:
  assumes "T0 P" "T1 P" "T2 P" "F2 P" "F3 P" "F5 P" "F6 P" 
  shows "sf25f (mkF24 P) = P"
  apply (rule refines_asym)
   apply (simp add: assms(1) assms(2) assms(3) assms(4) assms(5) assms(6) assms(7) sf25f_mkF24_refined)
  using assms(1) assms(2) assms(3) assms(4) assms(5) assms(6) assms(7) sf25f_mkF24_refines by blast

lemma T0_mkFailuresF5_remTraceTick [simp]:
  assumes "T0 P"
  shows "T0(mkFailuresF5 (fst P),remTraceTick`snd P)"
  using assms unfolding T0_def traces_def mkFailuresF5_def apply auto
  using Tick_last_remTraceTick by blast
                   
definition mkF5_weak_failure where "mkF5_weak_failure P == {(t,X). (t = [] \<or> last t \<noteq> tick) \<and> (t,X) \<in> P \<and> (t,X\<union>{tick}) \<in> P}"

definition mkF5_weak :: "'a process \<Rightarrow> 'a process"
  where "mkF5_weak P = (mkF5_weak_failure (fst P), snd P)"

lemma F5_mkF5_weak[simp]:
  shows "F5 (mkF5_weak P)"
  unfolding mkF5_weak_def F5_def mkF5_weak_failure_def by auto

lemma T0_mkF5_weak_failure [simp]:
  assumes "T0 P"
  shows "T0 (mkF5_weak_failure (fst P), snd P)"
  using assms unfolding T0_def traces_def by auto

lemma T1_mkF5_weak_failure [simp]:
  assumes "T1 P"
  shows "T1 (mkF5_weak_failure (fst P), snd P)"
  using assms unfolding T1_def traces_def by auto

lemma T2_mkF5_weak_failure [simp]:
  assumes "T2 P"
  shows "T2 (mkF5_weak_failure (fst P), snd P)"
  using assms unfolding T2_def traces_def mkF5_weak_failure_def by auto

lemma F2_mkF5_weak_failure [simp]:
  assumes "F2 P" 
  shows "F2 (mkF5_weak_failure (fst P), snd P)"
  using assms unfolding F2_def traces_def mkF5_weak_failure_def apply auto
  by blast+

lemma F3_mkF5_weak_failure [simp]:
  assumes "F3 P" 
  shows "F3 (mkF5_weak_failure (fst P), snd P)"
  using assms unfolding F3_def traces_def mkF5_weak_failure_def apply auto
  proof -
    fix X :: "'a evt set" and Y :: "'a evt set"
  assume a1: "\<forall>s X Y. (s, X) \<in> fst P \<and> Y \<inter> {x. s @ [x] \<in> snd P} = {} \<longrightarrow> (s, X \<union> Y) \<in> fst P"
    assume a2: "([], insert tick X) \<in> fst P"
    assume "Y \<inter> {x. [x] \<in> snd P} = {}"
    then have "Y \<inter> {e. [] @ [e] \<in> snd P} \<subseteq> {}"
  by simp
    then have "([], insert tick X \<union> Y) \<in> fst P"
      using a2 a1 by blast
    then show "([], insert tick (X \<union> Y)) \<in> fst P"
  by force
next
  fix X Y :: "'a evt set" and s :: "'a trace"
  assume as:"\<forall>s X Y. (s, X) \<in> fst P \<and> Y \<inter> {x. s @ [x] \<in> snd P} = {} \<longrightarrow> (s, X \<union> Y) \<in> fst P"
  and as1:"(s, X) \<in> fst P"
  and as2:"(s, insert tick X) \<in> fst P"
  and as3:"Y \<inter> {x. s @ [x] \<in> snd P} = {}"
  and as4:"last s \<noteq> tick"
  show "(s, insert tick (X \<union> Y)) \<in> fst P"
    using as as1 as2 as3 as4 by (metis Un_insert_left)
qed

lemma F5_mkF5_weak_failure [simp]:
  shows "F5 (mkF5_weak_failure (fst P), snd P)"
  unfolding F5_def traces_def mkF5_weak_failure_def by auto

lemma F6_mkF5_weak_failure [simp]:
  shows "F6 (mkF5_weak_failure (fst P), snd P)"
  unfolding F6_def traces_def mkF5_weak_failure_def by auto

lemma mkF24_mkF5_weak_failure:
  assumes "T0 P" "T1 P" "T2 P" "F2 P" "F3 P" "F4 P"
  shows "P \<sqsubseteq> mkF24 (mkF5_weak_failure (fst P), snd P)"
  using assms unfolding refines_def mkF24_def mkF5_weak_failure_def traces_def apply auto
   apply (metis F2_def F4_def insert_subset traces_def)
  by (metis F2_def F4_def insert_subset subset_UNIV traces_def)

lemma UNIV_tick:
  assumes "(a,b) \<in> fst P" "\<not> b \<subseteq> UNIV-{tick}"
  shows "(a,b\<union>{tick}) \<in> fst P"
  using assms insert_absorb by fastforce

lemma no_tick_then_refuse:
  assumes "F3 P" "(s,b) \<in> fst P" "s @ [tick] \<notin> snd P"
  shows "(s,b\<union>{tick}) \<in> fst P"
  by (metis (no_types, lifting) F3_def Int_emptyI assms mem_Collect_eq singletonD traces_def)

lemma mkF24_sf25f_refined:
  assumes "T0 P" "T1 P" "T2 P" "F2 P" "F3 P" "F4 P" 
  shows "mkF24 (sf25f P) \<sqsubseteq> P"
proof (rule refines_rule)
  show "snd P \<subseteq> snd (mkF24 (sf25f P))"
    by (metis assms(1) assms(2) assms(3) assms(4) assms(5) assms(6) order_refl traces_def traces_eq_traces_mkF24 traces_sf25f_eq)

  show "fst P \<subseteq> fst (mkF24 (sf25f P))"
  proof -
    have A:"fst (mkF24 (sf25f P)) = {y. \<exists>Q. T0 Q \<and> T1 Q \<and> T2 Q \<and> F2 Q \<and> F3 Q \<and> F5 Q \<and> F6 Q \<and> P \<sqsubseteq> (mkF24 Q) \<and> y \<in> fst (mkF24 Q)}"
    proof -
      have "fst (mkF24 (sf25f P)) = fst (mkF24 (\<Sqinter>{Q. T0 Q \<and> T1 Q \<and> T2 Q \<and> F2 Q \<and> F3 Q \<and> F5 Q \<and> F6 Q \<and> P \<sqsubseteq> (mkF24 Q)}))"
        unfolding sf25f_def by auto
      also have "... = fst (\<Sqinter>(mkF24`{Q. T0 Q \<and> T1 Q \<and> T2 Q \<and> F2 Q \<and> F3 Q \<and> F5 Q \<and> F6 Q \<and> P \<sqsubseteq> (mkF24 Q)}))"
        unfolding IntChoice_def mkF24_def traces_def refines_def apply auto
        by blast+
      also have "... = fst (\<Sqinter>({y. \<exists>x. x \<in> {Q. T0 Q \<and> T1 Q \<and> T2 Q \<and> F2 Q \<and> F3 Q \<and> F5 Q \<and> F6 Q \<and> P \<sqsubseteq> (mkF24 Q)} \<and> y = mkF24 x}))"
        unfolding IntChoice_def traces_def refines_def by auto
      also have "... = \<Union>({y. \<exists>x. x \<in> {Q. T0 Q \<and> T1 Q \<and> T2 Q \<and> F2 Q \<and> F3 Q \<and> F5 Q \<and> F6 Q \<and> P \<sqsubseteq> (mkF24 Q)} \<and> y = fst (mkF24 x)})"
        unfolding IntChoice_def traces_def refines_def 
        apply auto 
        by blast
      also have "... = \<Union>({y. \<exists>Q. T0 Q \<and> T1 Q \<and> T2 Q \<and> F2 Q \<and> F3 Q \<and> F5 Q \<and> F6 Q \<and> P \<sqsubseteq> (mkF24 Q) \<and> y = fst (mkF24 Q)})"
        by auto
      also have "... = {y. \<exists>Q. T0 Q \<and> T1 Q \<and> T2 Q \<and> F2 Q \<and> F3 Q \<and> F5 Q \<and> F6 Q \<and> P \<sqsubseteq> (mkF24 Q) \<and> y \<in> fst (mkF24 Q)}"
        by auto
      finally show ?thesis .
    qed

    have B:"fst P \<subseteq> {y. \<exists>Q. T0 Q \<and> T1 Q \<and> T2 Q \<and> F2 Q \<and> F3 Q \<and> F5 Q \<and> F6 Q \<and> P \<sqsubseteq> (mkF24 Q) \<and> y \<in> fst (mkF24 Q)}"
      apply auto
      using assms
      apply (rule_tac x="mkF5_weak_failure (fst P)" in exI)
      apply (rule exI[where x="snd P"])
      apply auto
      apply (simp add:mkF24_mkF5_weak_failure)
      unfolding mkF24_def mkF5_weak_failure_def traces_def apply auto
      apply (metis (full_types) T2_def append_butlast_last_id traces_def)
      using UNIV_tick no_tick_then_refuse
      by (metis Un_empty_right Un_insert_right) 

    have "fst P \<subseteq> fst (mkF24 (sf25f P))"
      using A B by auto
    then show ?thesis .
  qed
qed

lemma mkF24_sf25f_eq:
  assumes "T0 P" "T1 P" "T2 P" "F2 P" "F3 P" "F4 P" 
  shows "mkF24 (sf25f P) = P"
  by (simp add: assms(1) assms(2) assms(3) assms(4) assms(5) assms(6) mkF24_sf25f_refined mkF24_sf25f_refines refines_asym)

lemma mkF24_sf2f_refines:
  assumes "T0 P" "T1 P" "T2 P" "F2 P" "F3 P" "F4 P" 
  shows "P \<sqsubseteq> mkF24 (sf2f P)"
proof (rule refines_rule)
  show "snd (mkF24 (sf2f P)) \<subseteq> snd P"
    by (metis assms(1) assms(2) assms(3) assms(4) assms(5) assms(6) order_refl traces_def traces_eq_traces_mkF24 traces_sf2f_eq)

 show "fst (mkF24 (sf2f P)) \<subseteq> fst P"
   by (smt IntChoice_def SUP_least UN_I UnCI Un_absorb2 assms(1) assms(2) assms(3) assms(4) assms(5) assms(6) case_prodI2 case_prod_conv fst_conv mem_Collect_eq mkF24_def mkF24_fixpoint_imp refines_def refines_refl sf2f_def subset_iff surjective_pairing traces_def traces_eq_traces_mkF24 traces_sf2f_eq)
qed

text \<open> Therefore, our model of failures is just as expressive as stable failures. \<close>

lemma mkF24_sf2f_eq:
  assumes "T0 P" "T1 P" "T2 P" "F2 P" "F3 P" "F4 P" 
  shows "mkF24 (sf2f P) = P"
  by (simp add: assms(1) assms(2) assms(3) assms(4) assms(5) assms(6) mkF24_sf2f_refined mkF24_sf2f_refines refines_asym)

lemma mkF25_unmkF25_refined:
  assumes "T0 P" "T1 P" "T2 P" "F2 P" "F3 P" "F5 P"
  shows "mkF25 (unmkF25 P) \<sqsubseteq> P"
proof (rule refines_rule)
  show "fst P \<subseteq> fst (mkF25 (unmkF25 P))"
    unfolding mkF25_def unmkF25_def IntChoice_def refines_def apply auto
    proof -
      fix a :: "'a evt list" and b :: "'a evt set"
      assume a1: "(a, b) \<in> fst P"
      assume a2: "\<forall>aa ba. ba \<subseteq> snd P \<longrightarrow> {(t, X). \<exists>Y. (t, Y) \<in> aa \<and> X \<subseteq> insert tick Y} \<subseteq> fst P \<longrightarrow> aa \<subseteq> fst P \<longrightarrow> F3 (aa, ba) \<longrightarrow> F2 (aa, ba) \<longrightarrow> T2 (aa, ba) \<longrightarrow> T1 (aa, ba) \<longrightarrow> T0 (aa, ba) \<longrightarrow> (a, b) \<notin> aa"
      have f3: "F3 (fst P, snd P)"
        by (metis assms(5) prod.collapse)
      have f4: "F2 (fst P, snd P)"
        by (metis assms(4) prod.collapse)
      have f5: "T2 (fst P, snd P)"
        by (simp add: assms(3))
      have f6: "T1 (fst P, snd P)"
        using assms(2) by fastforce
      have f7: "T0 (fst P, snd P)"
        by (simp add: assms(1))
      have "{(es, E). \<exists>Ea. (es, Ea) \<in> fst P \<and> E \<subseteq> insert tick Ea} \<subseteq> fst P"
        using F5_F2_imp_tick_failures assms(4) assms(6) by blast
      then show "\<exists>Y. (\<exists>aa b. T0 (aa, b) \<and> T1 (aa, b) \<and> T2 (aa, b) \<and> F2 (aa, b) \<and> F3 (aa, b) \<and> aa \<subseteq> fst P \<and> {(t, X). \<exists>Y. (t, Y) \<in> aa \<and> X \<subseteq> insert tick Y} \<subseteq> fst P \<and> b \<subseteq> snd P \<and> (a, Y) \<in> aa) \<and> b \<subseteq> insert tick Y"
        using f7 f6 f5 f4 f3 a2 a1 by (meson subsetI)
    qed
    
  show "snd P \<subseteq> snd (mkF25 (unmkF25 P))"
      unfolding mkF25_def unmkF25_def IntChoice_def refines_def apply auto
      by (metis (mono_tags) F5_F2_imp_tick_failures assms(1) assms(2) assms(3) assms(4) assms(5) assms(6) subset_refl surjective_pairing)
  qed

lemma mkF25_unmkF25_refines:
  shows "P \<sqsubseteq> mkF25 (unmkF25 P)"
proof (rule refines_rule)
  show "fst (mkF25 (unmkF25 P)) \<subseteq> fst P"
    unfolding mkF25_def unmkF25_def IntChoice_def refines_def by auto
  show "snd (mkF25 (unmkF25 P)) \<subseteq> snd P"
    unfolding mkF25_def unmkF25_def IntChoice_def refines_def by auto
qed

lemma mkF25_unmkF25_eq:
  assumes "T0 P" "T1 P" "T2 P" "F2 P" "F3 P" "F5 P"
  shows "mkF25 (unmkF25 P) = P"
  by (simp add: assms(1) assms(2) assms(3) assms(4) assms(5) assms(6) mkF25_unmkF25_refined mkF25_unmkF25_refines refines_asym)

lemma unmkF25_mkF25_refined:
  assumes "T0 P" "T1 P" "T2 P" "F2 P" "F3 P"
  shows "unmkF25 (mkF25 P) \<sqsubseteq> P"
proof (rule refines_rule)
  show "fst P \<subseteq> fst (unmkF25 (mkF25 P))"
    unfolding mkF25_def unmkF25_def IntChoice_def refines_def apply auto
    proof -
      fix a :: "'a evt list" and b :: "'a evt set"
      assume "(a, b) \<in> fst P"
      then have "\<exists>Pa. F3 (Pa, snd P) \<and> F2 (Pa, snd P) \<and> T2 (Pa, snd P) \<and> T1 (Pa, snd P) \<and> T0 (Pa, snd P) \<and> (a, b) \<in> Pa \<and> Pa \<subseteq> fst P \<union> {(es, E). \<exists>Ea. (es, Ea) \<in> fst P \<and> E \<subseteq> insert tick Ea} \<and> {(es, E). \<exists>Ea. (es, Ea) \<in> Pa \<and> E \<subseteq> insert tick Ea} \<subseteq> fst P \<union> {(es, E). \<exists>Ea. (es, Ea) \<in> fst P \<and> E \<subseteq> insert tick Ea}"
        using assms(1) assms(2) assms(3) assms(4) assms(5) by force
      then show "\<exists>Pa E. T0 (Pa, E) \<and> T1 (Pa, E) \<and> T2 (Pa, E) \<and> F2 (Pa, E) \<and> F3 (Pa, E) \<and> Pa \<subseteq> fst P \<union> {(es, E). \<exists>Ea. (es, Ea) \<in> fst P \<and> E \<subseteq> insert tick Ea} \<and> {(es, E). \<exists>Ea. (es, Ea) \<in> Pa \<and> E \<subseteq> insert tick Ea} \<subseteq> fst P \<union> {(es, E). \<exists>Ea. (es, Ea) \<in> fst P \<and> E \<subseteq> insert tick Ea} \<and> E \<subseteq> snd P \<and> (a, b) \<in> Pa"
        by auto
    qed

  show "snd P \<subseteq> snd (unmkF25 (mkF25 P))"
    unfolding mkF25_def unmkF25_def IntChoice_def refines_def apply auto
    proof -
      fix x :: "'a evt list"
      assume "x \<in> snd P"
      then have "\<exists>E. (((((x \<in> E \<and> E \<subseteq> snd P) \<and> T2 (fst P, E)) \<and> T1 (fst P, E)) \<and> T0 (fst P, E)) \<and> F3 (fst P, E)) \<and> F2 (fst P, E)"
        by (metis (full_types) assms(1) assms(2) assms(3) assms(4) assms(5) prod.collapse subset_refl)
      then show "\<exists>Pa E. T0 (Pa, E) \<and> T1 (Pa, E) \<and> T2 (Pa, E) \<and> F2 (Pa, E) \<and> F3 (Pa, E) \<and> Pa \<subseteq> fst P \<union> {(es, E). \<exists>Ea. (es, Ea) \<in> fst P \<and> E \<subseteq> insert tick Ea} \<and> {(es, E). \<exists>Ea. (es, Ea) \<in> Pa \<and> E \<subseteq> insert tick Ea} \<subseteq> fst P \<union> {(es, E). \<exists>Ea. (es, Ea) \<in> fst P \<and> E \<subseteq> insert tick Ea} \<and> E \<subseteq> snd P \<and> x \<in> E"
        by blast
    qed
  qed

text \<open> How about the other way around? \<close>

lemma "fst (sf2f (mkF24 (({},{[],[tick]})))) = {}"
  unfolding sf2f_def mkF24_def traces_def IntChoice_def refines_def apply auto 
  apply (case_tac aa, auto)
  oops

lemma traces_sf2f_mkF24_eq:
  assumes "T0 P" "T1 P" "T2 P" "F2 P" "F3 P"
  shows "traces (sf2f (mkF24 P)) = traces P"
  using assms 
  by (metis F2_mkF24 F3_mkF24 F4_mkF24 T0_def T1_mkF24 T2_mkF24 traces_eq_traces_mkF24 traces_sf2f_eq)

lemma mkF24_traces_refines:
  assumes "(mkF24 P) \<sqsubseteq> (mkF24 Q)"
  shows "snd Q \<subseteq> snd P"
  using assms unfolding mkF24_def traces_def apply auto
  by (metis (no_types, lifting) in_mono refines_def snd_conv)

lemma mkF24_dist_intChoice:
  "mkF24(P \<sqinter> Q) = mkF24(P) \<sqinter> mkF24(Q)"
  apply (rule refines_asym)
  unfolding mkF24_def intChoice_def traces_def refines_def by auto

lemma
  assumes "T0 P" "T1 P" "T2 P" "F2 P" "F3 P"
  shows "sf2f(mkF24(P)) \<sqsubseteq> P"
proof (rule refines_rule)
  show "snd P \<subseteq> snd (sf2f (mkF24 P))"
    by (metis F2_mkF24 F3_mkF24 F4_mkF24 T0_def T1_mkF24 T2_mkF24 assms(1) assms(2) assms(3) assms(4) assms(5) eq_iff traces_def traces_eq_traces_mkF24 traces_sf2f_eq)

  show "fst P \<subseteq> fst (sf2f (mkF24 P))"
    unfolding sf2f_def mkF24_def traces_def IntChoice_def apply auto
    using assms(1) assms(2) assms(3) assms(4) assms(5) refines_refl by force
qed

(* Old below *)

definition D1 :: "'a process \<Rightarrow> bool"
 where "D1 P \<equiv> \<forall>s t. s \<in> (snd P) \<longrightarrow> (s@t) \<in> (snd P)"
 
definition D2 :: "'a process \<Rightarrow> bool"
 where "D2 P \<equiv> \<forall>s X. s \<in> (snd P) \<longrightarrow> (s, X) \<in> (fst P)"

definition trace :: "'a failure \<Rightarrow> 'a trace"
 where "trace f = fst f"

definition fd2r :: "('a failure) set \<Rightarrow> ('a trace) set \<Rightarrow> 'a prel"
 where "fd2r F D = { (s,s'). {the s,the s'} \<subseteq> F \<and> s \<noteq> None \<and> s' \<noteq> None
                             \<and> (\<exists>a. trace (the s') = (trace (the s) @ a))
                             }
                   \<union> { (s,s'). trace (the s) \<in> D \<and> 
                               (s'=None \<or> (\<exists>a. trace (the s') = trace (the s) @ a)) } \<union> { (None,None) }"                               

definition fdP2r :: "'a process \<Rightarrow> 'a prel"
 where "fdP2r P = fd2r (fst P) (snd P)"
                               
definition divFailureStrict :: "('a failure) set \<Rightarrow> ('a trace) set \<Rightarrow> ('a failure) set"
 where "divFailureStrict F D = F \<union> {(s,X). s \<in> D}"
 
definition divStrict :: "('a trace) set \<Rightarrow> ('a trace) set"
 where "divStrict D = D \<union> {s'. \<exists>s a. s' = s @ a \<and> s \<in> D}"
 
definition F2f :: "('a failure) set \<Rightarrow> bool"
 where "F2f F \<equiv> \<forall>s X Y. (s, X) \<in> F \<and> Y \<subseteq> X \<longrightarrow> (s, Y) \<in> F" 
 
section {* Relational model*}

subsection {* Healthiness Conditions*}

text {* In a predicative style *}

text {* Prefix closure *} 
 
definition CR1H :: "'a prel \<Rightarrow> bool"
 where "CR1H R = (\<forall>s s'. ((s,s') \<in> R \<and> s\<noteq>None \<and> s'\<noteq>None) \<longrightarrow> (\<exists>t. trace (the s') = trace (the s) @ t))"
 
text {* Divergence strictness*}

definition CR2H :: "'a prel \<Rightarrow> bool"
 where "CR2H R = (\<forall>s s'. ((s,None) \<in> R \<and> s \<noteq> None \<and> s' \<noteq> None 
                  \<and> trace (the s) = trace (the s')) \<longrightarrow> (s',None) \<in> R)"
                  
text {* None to None *}

definition CR3H :: "'a prel \<Rightarrow> bool"
 where "CR3H R = (\<forall>s. s \<noteq> None \<and> (None,s) \<notin> R \<and> (None,None) \<in> R)"
 
text {* Or in a fixed-point style *}

definition R1H :: "'a prel \<Rightarrow> 'a prel"
 where "R1H R = { (s,s'). \<exists>t.(s,s') \<in> R \<and> s \<noteq> None \<and> trace (the s') = trace (the s) @ t }"

definition R2H :: "'a prel \<Rightarrow> 'a prel"
 where "R2H R = { (s,s'). \<exists>t. (s,None) \<in> R \<and> s \<noteq> None \<and> trace(the s') = trace (the s) @ t \<or> (s,s') \<in> R }"
 
definition R3H :: "'a prel \<Rightarrow> 'a prel"
 where "R3H R = R \<union> {(None,None)}"

subsection {* Linking from the relational model *}
 
text {* From a relation to a set of failures. *}

definition r2f :: "'a prel \<Rightarrow> ('a failure) set"
 where "r2f R = { f. \<exists>s s'. (s,s') \<in> R \<and> f = the s' \<and> s \<noteq> None \<and> s' \<noteq> None}"
 
text {* From a relation to a set of divergences. *} 
 
definition r2d :: "'a prel \<Rightarrow> ('a trace) set"
 where "r2d R = { t. \<exists>s. (s,None) \<in> R \<and> t = trace (the s) \<and> s \<noteq> None}"
 
text {* From a relation to a CSP process. *} 
 
definition r2P :: "'a prel \<Rightarrow> 'a process"
 where "r2P R = (r2f R, r2d R)"
 
lemma "CR1H(fd2r F D)"
 apply (simp add:CR1H_def fd2r_def trace_def)
 by auto
 
lemma "CR2H(fd2r F D)"
 apply (simp add:fd2r_def CR2H_def trace_def)
 by auto
 
lemma
 assumes "CR3H R" "CR2H R" "CR1H R"
 shows "fd2r (r2f R) (r2d R) = R"
 using assms
 apply (simp add:CR3H_def CR2H_def CR1H_def r2f_def r2d_def fd2r_def trace_def)
 by blast
 
lemma r2fd_is_F1:
 assumes "CR3H R" "CR2H R" "CR1H R"
 shows "F1((r2f R),(r2d R))"
 using assms unfolding CR1H_def CR2H_def CR3H_def
 by blast

lemma r2fd_is_F2:
 assumes "CR3H R" "CR2H R" "CR1H R"
 shows "F2((r2f R),(r2d R))"
 using assms unfolding CR1H_def CR2H_def CR3H_def
 by blast

lemma r2fd_is_F3:
 assumes "CR3H R" "CR2H R" "CR1H R"
 shows "F3((r2f R),(r2d R))"
 using assms unfolding CR1H_def CR2H_def CR3H_def
 by blast
 
lemma r2fd_is_D1:
 assumes "CR3H R" "CR2H R" "CR1H R"
 shows "D1((r2f R),(r2d R))"
 using assms unfolding CR1H_def CR2H_def CR3H_def
 by blast
 
lemma r2fd_is_D2:
 assumes "CR3H R" "CR2H R" "CR1H R"
 shows "D2((r2f R),(r2d R))"
 using assms unfolding CR1H_def CR2H_def CR3H_def
 by blast

lemma r2f_fd2r:
assumes "divStrict D = D" and "divFailureStrict F D = F"
shows "r2f (fd2r F D) = F"
apply auto
apply (simp add:fd2r_def r2f_def trace_def)
apply auto
using assms unfolding divStrict_def divFailureStrict_def
apply (simp add:fd2r_def r2f_def)
apply blast
using assms unfolding divStrict_def divFailureStrict_def
apply (simp add:fd2r_def r2f_def)
by (metis (no_types, lifting) append_Nil2 option.sel)

lemma r2d_fd2r: "r2d (fd2r F D) = D"
apply auto 
apply (simp add:fd2r_def r2d_def)
apply blast
apply (simp add:fd2r_def r2d_def)
by (metis option.sel prod.sel(1) trace_def)

lemma D1_is_divStrict:
 shows "D1(P) = (divStrict (snd P) = (snd P))"
 apply (simp add:divStrict_def D1_def)
 by blast
 
lemma D2_is_divFailureStrict:
 shows "D2(P) = (divFailureStrict (fst P) (snd P) = (fst P))"
 apply (simp add:divFailureStrict_def D2_def)
 by blast

lemma r2P_fdP2r:
 assumes "D1(P)" "D2(P)"
 shows "r2P (fdP2r P) = P"
 apply (simp add:r2P_def fdP2r_def)
 using assms
 by (simp add: D1_is_divStrict D2_is_divFailureStrict r2d_fd2r r2f_fd2r)

lemma fdP2r_r2P:
 assumes "CR3H R"
 shows "fdP2r (r2P R) = R"
 using CR3H_def and assms by blast

end