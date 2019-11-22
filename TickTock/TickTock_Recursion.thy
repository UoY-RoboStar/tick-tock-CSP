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

lemma iterateTT_ttWFx:
  assumes "\<And> X. ttWFx X \<Longrightarrow>ttWFx (F X)"
  shows "ttWFx (iterateTT F n)"
  by (induct n, simp_all add: assms, unfold ttWFx_def, auto)

lemma iterateTT_TT3w:
  assumes "\<And> X. TT3w X \<Longrightarrow>TT3w (F X)"
  shows "TT3w (iterateTT F n)"
  by (induct n, simp_all add: assms, unfold TT3w_def, auto)

lemma iterateTT_TT3ww:
  assumes "\<And> X. TT3ww X \<Longrightarrow>TT3ww (F X)"
  shows "TT3ww (iterateTT F n)"
  by (induct n, simp_all add: assms, unfold TT3ww_def, auto)

lemma iterateTT_TT3:
  assumes "\<And> X. TT3 X \<Longrightarrow>TT3 (F X)"
  shows "TT3 (iterateTT F n)"
  by (induct n, simp_all add: assms, unfold TT3_def, auto)

lemma iterateTT_TT:
  assumes "\<And> X. TT X \<Longrightarrow>TT (F X)"
  shows "TT (iterateTT F n)"
  apply (induct n, simp_all add: assms, unfold TT_def, auto simp add: TT_defs)
  using TT1_def tt_prefix_subset.elims(2) by auto

lemma iterateTT_subset:
  assumes TT0_F: "\<And> X. TT0 X \<Longrightarrow> TT0 (F X)" 
  assumes TT1_F: "\<And> X. TT1 X \<Longrightarrow> TT1 (F X)"
  assumes monotonic_F: "\<And> X Y. X \<sqsubseteq>\<^sub>C Y \<Longrightarrow> F X \<sqsubseteq>\<^sub>C F Y"
  shows "iterateTT F n \<subseteq> iterateTT F (n+1)"
proof (induct n, auto)
  show "[] \<in> F {[]}"
    by (metis TT0_F TT0_TT1_empty TT0_def TT1_F empty_subsetI insert_subset iterateTT.simps(1) iterateTT_TT1)
next
  fix n x
  assume "iterateTT F n \<subseteq> F (iterateTT F n)"
  then have "F (iterateTT F n) \<subseteq> F (F (iterateTT F n))"
    by (meson RefinesTT_def monotonic_F)
  then show "x \<in> F (iterateTT F n) \<Longrightarrow> x \<in> F (F (iterateTT F n))"
    by blast
qed

lemma iterateTT_subset2:
  assumes TT0_F: "\<And> X. TT0 X \<Longrightarrow> TT0 (F X)" 
  assumes TT1_F: "\<And> X. TT1 X \<Longrightarrow> TT1 (F X)"
  assumes monotonic_F: "\<And> X Y. X \<sqsubseteq>\<^sub>C Y \<Longrightarrow> F X \<sqsubseteq>\<^sub>C F Y"
  shows "n > m \<Longrightarrow> iterateTT F m \<subseteq> iterateTT F n"
  by (induct n, auto, smt TT0_F TT1_F add.commute iterateTT.simps(2) iterateTT_subset less_Suc_eq monotonic_F plus_1_eq_Suc set_mp)

lemma iterateTT_subset3:
  assumes TT0_F: "\<And> X. TT0 X \<Longrightarrow> TT0 (F X)" 
  assumes TT1_F: "\<And> X. TT1 X \<Longrightarrow> TT1 (F X)"
  assumes monotonic_F: "\<And> X Y. X \<sqsubseteq>\<^sub>C Y \<Longrightarrow> F X \<sqsubseteq>\<^sub>C F Y"
  shows "iterateTT F m \<subseteq> iterateTT F n \<or> iterateTT F n \<subseteq> iterateTT F m"
  by (metis TT0_F TT1_F eq_iff iterateTT_subset2 monotonic_F not_less)

lemma iterateTT_mono:
  assumes mono_F: "\<And>X Y. X \<sqsubseteq>\<^sub>C Y \<Longrightarrow> F X \<sqsubseteq>\<^sub>C F Y"
  shows "(\<And>P. F P \<sqsubseteq>\<^sub>C G P) \<Longrightarrow> iterateTT F n \<sqsubseteq>\<^sub>C iterateTT G n"
  using mono_F unfolding RefinesTT_def by (induct n, auto, blast)

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

lemma ttWFx_Union: "\<forall> x\<in>X. ttWFx x \<Longrightarrow> ttWFx (\<Union>X)"
  unfolding ttWFx_def by auto

lemma TT3w_Union: "\<forall> x\<in>X. TT3w x \<Longrightarrow> TT3w (\<Union>X)"
  unfolding TT3w_def by auto

lemma TT3ww_Union: "\<forall> x\<in>X. TT3ww x \<Longrightarrow> TT3ww (\<Union>X)"
  unfolding TT3ww_def by auto

definition RecursionTT :: "('a ttobs list set \<Rightarrow> 'a ttobs list set) \<Rightarrow> 'a ttobs list set" ("\<mu>\<^sub>C(_)") where
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
  assumes "\<And> X. TT1 X \<Longrightarrow> TT1 (F X)"
  shows "TT1 (RecursionTT F)"
  unfolding RecursionTT_def by (smt TT1_Union assms iterateTT_TT1 mem_Collect_eq) 

lemma RecursionTT_TT2:
  assumes "\<And> X. TT2 X \<Longrightarrow> TT2 (F X)"
  shows "TT2 (RecursionTT F)"
  unfolding RecursionTT_def by (smt Collect_empty_eq TT2_Union assms iterateTT_TT2 mem_Collect_eq)

lemma RecursionTT_TT2w:
  assumes "\<And> X. TT2w X \<Longrightarrow> TT2w (F X)"
  shows "TT2w (RecursionTT F)"
  unfolding RecursionTT_def by (smt TT2w_Union assms empty_iff iterateTT_TT2w mem_Collect_eq) 

lemma RecursionTT_ttWFx:
  assumes "\<And> X. ttWFx X \<Longrightarrow> ttWFx (F X)"
  shows "ttWFx (RecursionTT F)"
  unfolding RecursionTT_def by (smt ttWFx_Union assms iterateTT_ttWFx mem_Collect_eq)

lemma RecursionTT_TT3w:
  assumes "\<And> X. TT3w X \<Longrightarrow> TT3w (F X)"
  shows "TT3w (RecursionTT F)"
  unfolding RecursionTT_def by (smt TT3w_Union assms iterateTT_TT3w mem_Collect_eq) 

lemma RecursionTT_TT3ww:
  assumes "\<And> X. TT3ww X \<Longrightarrow> TT3ww (F X)"
  shows "TT3ww (RecursionTT F)"
  unfolding RecursionTT_def by (smt TT3ww_Union assms iterateTT_TT3ww mem_Collect_eq)

lemma RecursionTT_TT:
  assumes "\<And> X. TT X \<Longrightarrow> TT (F X)"
  shows "TT (RecursionTT F)"
  unfolding RecursionTT_def TT_def apply auto
  using TT_def assms iterateTT_TT apply auto
  apply (metis (mono_tags, lifting) CollectI Sup_bot_conv(1) TT0_def empty_not_insert iterateTT.simps(1))
  apply (smt TT1_Union TT_TT1 assms iterateTT_TT mem_Collect_eq)
  apply (smt TT2w_Union TT_TT2w assms empty_iff iterateTT_TT mem_Collect_eq)
  apply (smt ttWFx_Union TT_ttWFx assms iterateTT_TT mem_Collect_eq)
  done

lemma RecursionTT_strengthen:
  assumes monotonic_F: "\<And> X Y. X \<sqsubseteq>\<^sub>C Y \<Longrightarrow> F X \<sqsubseteq>\<^sub>C F Y"
  assumes TT0_F: "\<And> X. TT0 X \<Longrightarrow> TT0 (F X)" 
  assumes TT1_F: "\<And> X. TT1 X \<Longrightarrow> TT1 (F X)" 
  shows "F (\<mu>\<^sub>C F) \<sqsubseteq>\<^sub>C \<mu>\<^sub>C F"
  unfolding RefinesTT_def RecursionTT_def
proof auto
  fix x n
  show "x \<in> iterateTT F n \<Longrightarrow> x \<in> F (\<Union>{P. \<exists>n. P = iterateTT F n})"
  proof (induct n, auto)
    show "[] \<in> F (\<Union>{P. \<exists>n. P = iterateTT F n})"
      by (metis (full_types) RecursionTT_TT0 RecursionTT_TT1 RecursionTT_def TT0_F TT0_TT1_empty TT1_F)
  next
    fix n
    have "iterateTT F n \<subseteq> \<Union>{P. \<exists>n. P = iterateTT F n}"
      by auto
    then have "F (iterateTT F n) \<subseteq> F (\<Union>{P. \<exists>n. P = iterateTT F n})"
      by (meson RefinesTT_def monotonic_F)
    then show "x \<in> F (iterateTT F n) \<Longrightarrow> x \<in> F (\<Union>{P. \<exists>n. P = iterateTT F n})"
      by auto
  qed
qed

lemma RecursionTT_sfp:
  assumes monotonic_F: "\<And> X Y. X \<sqsubseteq>\<^sub>C Y \<Longrightarrow> F X \<sqsubseteq>\<^sub>C F Y"
  assumes Y_TT0: "TT0 Y" and Y_TT1: "TT1 Y"
  shows "Y \<sqsubseteq>\<^sub>C F(Y) \<Longrightarrow> Y \<sqsubseteq>\<^sub>C (\<mu>\<^sub>C F)"
  unfolding RefinesTT_def RecursionTT_def
proof (auto)
  fix x n
  assume assm: "F Y \<subseteq> Y"
  have "iterateTT F n \<subseteq> Y"
  proof (induct n, auto)
    show "[] \<in> Y"
      by (simp add: TT0_TT1_empty Y_TT0 Y_TT1)
  next
    fix x n
    assume "iterateTT F n \<subseteq> Y"
    then have "F (iterateTT F n) \<subseteq> F Y"
      by (meson RefinesTT_def monotonic_F)
    then have "F (iterateTT F n) \<subseteq> Y"
      using assm by blast
    then show "x \<in> F (iterateTT F n) \<Longrightarrow> x \<in> Y"
      by auto
  qed
  then show "F Y \<subseteq> Y \<Longrightarrow> x \<in> iterateTT F n \<Longrightarrow> x \<in> Y"
    by auto
qed

lemma RecursionTT_unfold:
  assumes TT0_F: "\<And> X. TT0 X \<Longrightarrow> TT0 (F X)" 
  assumes TT1_F: "\<And> X. TT1 X \<Longrightarrow> TT1 (F X)"
  assumes dist_F: "\<And>S. S \<noteq> {} \<Longrightarrow> F (\<Union>S) = \<Union>{R. \<exists>Q. Q \<in> S \<and> R = F Q}"
  shows "(\<mu>\<^sub>C F) = F (\<mu>\<^sub>C F)"
proof -
  have "{P. \<exists>n. P = iterateTT F n} \<noteq> {}"
    by blast
  then have "\<Union>{P. \<exists>n. P = F (iterateTT F n)} = F (\<Union>{P. \<exists>n. P = iterateTT F n})"
    using dist_F[where S="{P. \<exists>n. P = iterateTT F n}"] by auto
  also have "\<Union>{P. \<exists>n. P = F (iterateTT F n)} = \<Union>{P. \<exists>n. P = (iterateTT F n)}"
  proof auto
    fix x n
    show "x \<in> F (iterateTT F n) \<Longrightarrow> \<exists>xa. (\<exists>n. xa = iterateTT F n) \<and> x \<in> xa"
      by (rule_tac x="iterateTT F (n+1)" in exI, auto, rule_tac x="n+1" in exI, auto)
  next
    fix x n
    show "x \<in> iterateTT F n \<Longrightarrow> \<exists>xa. (\<exists>n. xa = F (iterateTT F n)) \<and> x \<in> xa"
      apply (induct n, auto, rule_tac x="iterateTT F 1" in exI, auto, rule_tac x="0" in exI, auto)
      by (metis TT0_F TT0_TT1_empty TT0_def TT1_F insert_not_empty iterateTT.simps(1) iterateTT_TT1)
  qed
  then show ?thesis
    unfolding RefinesTT_def RecursionTT_def using calculation by auto
qed

lemma RecursionTT_mono:
  assumes mono_F: "\<And>X Y. X \<sqsubseteq>\<^sub>C Y \<Longrightarrow> F X \<sqsubseteq>\<^sub>C F Y"
  shows "(\<And> P. F P \<sqsubseteq>\<^sub>C G P) \<Longrightarrow> (\<mu>\<^sub>C F) \<sqsubseteq>\<^sub>C (\<mu>\<^sub>C G)"
  using iterateTT_mono unfolding RecursionTT_def RefinesTT_def apply auto
  by (rule_tac x="iterateTT F n" in exI, auto, metis RefinesTT_def iterateTT_mono mono_F subsetCE)

end