theory TickTock_Recursion
  imports TickTock_Core TickTock_IntChoice
begin

fun iterateTT :: "('a ttobs list set \<Rightarrow> 'a ttobs list set) \<Rightarrow> nat \<Rightarrow> 'a ttobs list set" where
  "iterateTT F 0       = {[]}" |
  "iterateTT F (Suc n) = F (iterateTT F n)"

lemma iterateTT_wf:
  assumes "\<And> X. \<forall>t\<in>X. ttWF t \<Longrightarrow> \<forall>t\<in>F X. ttWF t"
  shows "\<forall>t\<in>(iterateTT F n). ttWF t"
  by (induct n, simp_all add: assms)

lemma iterateTT_TT0:
  assumes "\<And> X. TT0 X \<Longrightarrow>TT0 (F X)"
  shows "TT0 (iterateTT F n)"
  by (induct n, simp_all add: assms, unfold TT0_def, simp)

lemma iterateTT_TT1:
  assumes "\<And> X. TT1 X \<Longrightarrow>TT1 (F X)"
  shows "TT1 (iterateTT F n)"
  by (induct n, simp_all add: assms, unfold TT1_def, auto, case_tac \<rho>, auto)

lemma iterateTT_TT2:
  assumes "\<And> X. TT2 X \<Longrightarrow>TT2 (F X)"
  shows "TT2 (iterateTT F n)"
  by (induct n, simp_all add: assms, unfold TT2_def, auto)

lemma iterateTT_TT2w:
  assumes "\<And> X. TT2w X \<Longrightarrow>TT2w (F X)"
  shows "TT2w (iterateTT F n)"
  by (induct n, simp_all add: assms, unfold TT2w_def, auto)

lemma iterateTT_TT3:
  assumes "\<And> X. TT3 X \<Longrightarrow>TT3 (F X)"
  shows "TT3 (iterateTT F n)"
  by (induct n, simp_all add: assms, unfold TT3_def, auto)

lemma iterateTT_TT4:
  assumes "\<And> X. TT4 X \<Longrightarrow>TT4 (F X)"
  shows "TT4 (iterateTT F n)"
  by (induct n, simp_all add: assms, unfold TT4_def, auto)

lemma iterateTT_TT4w:
  assumes "\<And> X. TT4w X \<Longrightarrow>TT4w (F X)"
  shows "TT4w (iterateTT F n)"
  by (induct n, simp_all add: assms, unfold TT4w_def, auto)

lemma iterateTT_TT:
  assumes "\<And> X. TT X \<Longrightarrow>TT (F X)"
  shows "TT (iterateTT F n)"
  apply (induct n, simp_all add: assms, unfold TT_def, auto simp add: TT_defs)
  using TT1_def tt_prefix_subset.elims(2) by auto

lemma TT0_Union: "X \<noteq> {} \<Longrightarrow> \<forall> x\<in>X. TT0 x \<Longrightarrow> TT0 (\<Union>X)"
  by (simp add: TT0_def)

lemma TT1_Union: "\<forall> x\<in>X. TT1 x \<Longrightarrow> TT1 (\<Union>X)"
  by (meson TT1_def Union_iff)

lemma TT2_Union: "X \<noteq> {} \<Longrightarrow> \<forall> x\<in>X. TT2 x \<Longrightarrow> TT2 (\<Union>X)"
  unfolding TT2_def apply (simp, safe, simp, erule_tac x=Xaa in ballE, erule_tac x=Xaa in ballE, auto)
  by (erule_tac x=\<rho> in allE, erule_tac x=\<sigma> in allE, erule_tac x=Xa in allE, erule_tac x=Y in allE, auto)

lemma TT2w_Union: "X \<noteq> {} \<Longrightarrow> \<forall> x\<in>X. TT2w x \<Longrightarrow> TT2w (\<Union>X)"
  unfolding TT2w_def apply (simp, safe, simp, erule_tac x=Xaa in ballE, erule_tac x=Xaa in ballE, auto)
  by (erule_tac x=\<rho> in allE, erule_tac x=Xa in allE, erule_tac x=Y in allE, auto)

lemma TT3_Union: "\<forall> x\<in>X. TT3 x \<Longrightarrow> TT3 (\<Union>X)"
  unfolding TT3_def by auto

lemma TT4_Union: "\<forall> x\<in>X. TT4 x \<Longrightarrow> TT4 (\<Union>X)"
  unfolding TT4_def by auto

lemma TT4w_Union: "\<forall> x\<in>X. TT4w x \<Longrightarrow> TT4w (\<Union>X)"
  unfolding TT4w_def by auto

definition RecursionTT :: "('a ttobs list set \<Rightarrow> 'a ttobs list set) \<Rightarrow> 'a ttobs list set" where
  "RecursionTT F = \<Union> {P. \<exists> n. P = iterateTT F n}"

lemma RecursionTT_wf:
  assumes "\<And> X. \<forall>t\<in>X. ttWF t \<Longrightarrow> \<forall>t\<in>F X. ttWF t"
  shows "\<forall>t\<in>(RecursionTT F). ttWF t"
  unfolding RecursionTT_def
  by (smt Union_iff assms iterateTT_wf mem_Collect_eq)

lemma RecursionTT_TT0:
  assumes "\<And> X. TT0 X \<Longrightarrow> TT0 (F X)"
  shows "TT0 (RecursionTT F)"
  unfolding RecursionTT_def by (smt Collect_empty_eq TT0_Union assms iterateTT_TT0 mem_Collect_eq) 

lemma RecursionTT_TT1:
  assumes "\<And> X. TT1 X \<Longrightarrow>TT1 (F X)"
  shows "TT1 (RecursionTT F)"
  unfolding RecursionTT_def by (smt TT1_Union assms iterateTT_TT1 mem_Collect_eq) 

lemma RecursionTT_TT2:
  assumes "\<And> X. TT2 X \<Longrightarrow>TT2 (F X)"
  shows "TT2 (RecursionTT F)"
  unfolding RecursionTT_def by (smt Collect_empty_eq TT2_Union assms iterateTT_TT2 mem_Collect_eq)

lemma RecursionTT_TT2w:
  assumes "\<And> X. TT2w X \<Longrightarrow>TT2w (F X)"
  shows "TT2w (RecursionTT F)"
  unfolding RecursionTT_def by (smt TT2w_Union assms empty_iff iterateTT_TT2w mem_Collect_eq) 

lemma RecursionTT_TT3:
  assumes "\<And> X. TT3 X \<Longrightarrow>TT3 (F X)"
  shows "TT3 (RecursionTT F)"
  unfolding RecursionTT_def by (smt TT3_Union assms iterateTT_TT3 mem_Collect_eq)

lemma RecursionTT_TT4:
  assumes "\<And> X. TT4 X \<Longrightarrow>TT4 (F X)"
  shows "TT4 (RecursionTT F)"
  unfolding RecursionTT_def by (smt TT4_Union assms iterateTT_TT4 mem_Collect_eq) 

lemma RecursionTT_TT4w:
  assumes "\<And> X. TT4w X \<Longrightarrow>TT4w (F X)"
  shows "TT4w (RecursionTT F)"
  unfolding RecursionTT_def by (smt TT4w_Union assms iterateTT_TT4w mem_Collect_eq)

lemma RecursionTT_TT:
  assumes "\<And> X. TT X \<Longrightarrow>TT (F X)"
  shows "TT (RecursionTT F)"
  unfolding RecursionTT_def TT_def apply auto
  using TT_def assms iterateTT_TT apply auto
  apply (metis (mono_tags, lifting) CollectI Sup_bot_conv(1) TT0_def empty_not_insert iterateTT.simps(1))
  apply (smt TT1_Union TT_TT1 assms iterateTT_TT mem_Collect_eq)
  apply (smt TT2w_Union TT_TT2w assms empty_iff iterateTT_TT mem_Collect_eq)
  apply (smt TT3_Union TT_TT3 assms iterateTT_TT mem_Collect_eq)
  done

end