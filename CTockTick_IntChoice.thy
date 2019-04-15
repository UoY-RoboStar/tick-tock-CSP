theory CTockTick_IntChoice
  imports CTockTick_Core
begin
  
subsection {* Internal Choice *}

definition IntChoiceCTT :: "'e cttobs list set \<Rightarrow> 'e cttobs list set \<Rightarrow> 'e cttobs list set" (infixl "\<sqinter>\<^sub>C" 56) where
  "P \<sqinter>\<^sub>C Q = P \<union> Q"

lemma IntChoiceCTT_wf: "\<forall> t\<in>P. ttWF t \<Longrightarrow> \<forall> t\<in>Q. ttWF t \<Longrightarrow> \<forall> t\<in>P \<sqinter>\<^sub>C Q. ttWF t"
  unfolding IntChoiceCTT_def by auto

lemma CT2s_IntChoice:
  assumes "CT2s P" "CT2s Q"
  shows "CT2s (P \<sqinter>\<^sub>C Q)"
    using assms unfolding IntChoiceCTT_def CT2s_def by (auto, (smt disjoint_iff_not_equal mem_Collect_eq)+)

lemma CT4s_IntChoice:
  assumes "CT4s P" "CT4s Q"
  shows "CT4s (P \<sqinter>\<^sub>C Q)"
  using assms unfolding IntChoiceCTT_def CT4s_def by auto

lemma CT_IntChoice:
  assumes "CT P" "CT Q"
  shows "CT (P \<sqinter>\<^sub>C Q)"
  unfolding CT_defs
proof auto
  fix x
  show "x \<in> P \<sqinter>\<^sub>C Q \<Longrightarrow> ttWF x"
    by (metis CT_wf IntChoiceCTT_def Un_iff assms(1) assms(2))
next
  show "P \<sqinter>\<^sub>C Q = {} \<Longrightarrow> False"
    using CT_empty IntChoiceCTT_def assms(1) by blast
next
  fix \<rho> \<sigma>
  show "\<rho> \<lesssim>\<^sub>C \<sigma> \<Longrightarrow> \<sigma> \<in> P \<sqinter>\<^sub>C Q \<Longrightarrow> \<rho> \<in> P \<sqinter>\<^sub>C Q"
    by (metis CT1_def CT_CT1 IntChoiceCTT_def Un_iff assms(1) assms(2))
next
  fix \<rho> X Y
  assume assm1: "\<rho> @ [[X]\<^sub>R] \<in> P \<sqinter>\<^sub>C Q"
  assume assm2: "Y \<inter> {e. e \<noteq> Tock \<and> \<rho> @ [[e]\<^sub>E] \<in> P \<sqinter>\<^sub>C Q \<or> e = Tock \<and> \<rho> @ [[X]\<^sub>R, [e]\<^sub>E] \<in> P \<sqinter>\<^sub>C Q} = {}"
  have 1: "\<rho> @ [[X]\<^sub>R] \<in> P \<or> \<rho> @ [[X]\<^sub>R] \<in> Q"
    using assm1 unfolding IntChoiceCTT_def by auto
  have 2: "{e. e \<noteq> Tock \<and> \<rho> @ [[e]\<^sub>E] \<in> P \<sqinter>\<^sub>C Q \<or> e = Tock \<and> \<rho> @ [[X]\<^sub>R, [e]\<^sub>E] \<in> P \<sqinter>\<^sub>C Q} = 
    {e. e \<noteq> Tock \<and> \<rho> @ [[e]\<^sub>E] \<in> P \<or> e = Tock \<and> \<rho> @ [[X]\<^sub>R, [e]\<^sub>E] \<in> P} \<union> {e. e \<noteq> Tock \<and> \<rho> @ [[e]\<^sub>E] \<in> Q \<or> e = Tock \<and> \<rho> @ [[X]\<^sub>R, [e]\<^sub>E] \<in> Q}"
    unfolding IntChoiceCTT_def by auto
  have 3: "Y \<inter> {e. e \<noteq> Tock \<and> \<rho> @ [[e]\<^sub>E] \<in> P \<or> e = Tock \<and> \<rho> @ [[X]\<^sub>R, [e]\<^sub>E] \<in> P} = {}"
    using 2 assm2 inf_sup_distrib1 by auto
  have 4: "Y \<inter> {e. e \<noteq> Tock \<and> \<rho> @ [[e]\<^sub>E] \<in> Q \<or> e = Tock \<and> \<rho> @ [[X]\<^sub>R, [e]\<^sub>E] \<in> Q} = {}"
    using 2 assm2 inf_sup_distrib1 by auto
  have 5: "\<rho> @ [[X]\<^sub>R] \<in> P \<Longrightarrow> \<rho> @ [[X \<union> Y]\<^sub>R] \<in> P"
    using "3" CT2_def CT_def assms(1) by blast
  have 6: "\<rho> @ [[X]\<^sub>R] \<in> Q \<Longrightarrow> \<rho> @ [[X \<union> Y]\<^sub>R] \<in> Q"
    using "4" CT2_def CT_def assms(2) by blast
  show "\<rho> @ [[X \<union> Y]\<^sub>R] \<in> P \<sqinter>\<^sub>C Q"
    using "1" "5" "6" IntChoiceCTT_def by blast
next
  fix x
  show "x \<in> P \<sqinter>\<^sub>C Q \<Longrightarrow> CT3_trace x"
    by (metis CT3_def CT_CT3 IntChoiceCTT_def UnE assms(1) assms(2))
qed 

end