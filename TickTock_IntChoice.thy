theory TickTock_IntChoice
  imports TickTock_Core
begin
  
subsection {* Internal Choice *}

definition IntChoiceTT :: "'e cttobs list set \<Rightarrow> 'e cttobs list set \<Rightarrow> 'e cttobs list set" (infixl "\<sqinter>\<^sub>C" 56) where
  "P \<sqinter>\<^sub>C Q = P \<union> Q"

lemma IntChoiceTT_wf: "\<forall> t\<in>P. ttWF t \<Longrightarrow> \<forall> t\<in>Q. ttWF t \<Longrightarrow> \<forall> t\<in>P \<sqinter>\<^sub>C Q. ttWF t"
  unfolding IntChoiceTT_def by auto

lemma TT2s_IntChoice:
  assumes "TT2s P" "TT2s Q"
  shows "TT2s (P \<sqinter>\<^sub>C Q)"
    using assms unfolding IntChoiceTT_def TT2s_def by (auto, (smt disjoint_iff_not_equal mem_Collect_eq)+)

lemma TT4s_IntChoice:
  assumes "TT4s P" "TT4s Q"
  shows "TT4s (P \<sqinter>\<^sub>C Q)"
  using assms unfolding IntChoiceTT_def TT4s_def by auto

lemma TT_IntChoice:
  assumes "TT P" "TT Q"
  shows "TT (P \<sqinter>\<^sub>C Q)"
  unfolding TT_defs
proof auto
  fix x
  show "x \<in> P \<sqinter>\<^sub>C Q \<Longrightarrow> ttWF x"
    by (metis TT_wf IntChoiceTT_def Un_iff assms(1) assms(2))
next
  show "P \<sqinter>\<^sub>C Q = {} \<Longrightarrow> False"
    using TT_empty IntChoiceTT_def assms(1) by blast
next
  fix \<rho> \<sigma>
  show "\<rho> \<lesssim>\<^sub>C \<sigma> \<Longrightarrow> \<sigma> \<in> P \<sqinter>\<^sub>C Q \<Longrightarrow> \<rho> \<in> P \<sqinter>\<^sub>C Q"
    by (metis TT1_def TT_TT1 IntChoiceTT_def Un_iff assms(1) assms(2))
next
  fix \<rho> X Y
  assume assm1: "\<rho> @ [[X]\<^sub>R] \<in> P \<sqinter>\<^sub>C Q"
  assume assm2: "Y \<inter> {e. e \<noteq> Tock \<and> \<rho> @ [[e]\<^sub>E] \<in> P \<sqinter>\<^sub>C Q \<or> e = Tock \<and> \<rho> @ [[X]\<^sub>R, [e]\<^sub>E] \<in> P \<sqinter>\<^sub>C Q} = {}"
  have 1: "\<rho> @ [[X]\<^sub>R] \<in> P \<or> \<rho> @ [[X]\<^sub>R] \<in> Q"
    using assm1 unfolding IntChoiceTT_def by auto
  have 2: "{e. e \<noteq> Tock \<and> \<rho> @ [[e]\<^sub>E] \<in> P \<sqinter>\<^sub>C Q \<or> e = Tock \<and> \<rho> @ [[X]\<^sub>R, [e]\<^sub>E] \<in> P \<sqinter>\<^sub>C Q} = 
    {e. e \<noteq> Tock \<and> \<rho> @ [[e]\<^sub>E] \<in> P \<or> e = Tock \<and> \<rho> @ [[X]\<^sub>R, [e]\<^sub>E] \<in> P} \<union> {e. e \<noteq> Tock \<and> \<rho> @ [[e]\<^sub>E] \<in> Q \<or> e = Tock \<and> \<rho> @ [[X]\<^sub>R, [e]\<^sub>E] \<in> Q}"
    unfolding IntChoiceTT_def by auto
  have 3: "Y \<inter> {e. e \<noteq> Tock \<and> \<rho> @ [[e]\<^sub>E] \<in> P \<or> e = Tock \<and> \<rho> @ [[X]\<^sub>R, [e]\<^sub>E] \<in> P} = {}"
    using 2 assm2 inf_sup_distrib1 by auto
  have 4: "Y \<inter> {e. e \<noteq> Tock \<and> \<rho> @ [[e]\<^sub>E] \<in> Q \<or> e = Tock \<and> \<rho> @ [[X]\<^sub>R, [e]\<^sub>E] \<in> Q} = {}"
    using 2 assm2 inf_sup_distrib1 by auto
  have 5: "\<rho> @ [[X]\<^sub>R] \<in> P \<Longrightarrow> \<rho> @ [[X \<union> Y]\<^sub>R] \<in> P"
    using "3" TT2_def TT_def assms(1) by blast
  have 6: "\<rho> @ [[X]\<^sub>R] \<in> Q \<Longrightarrow> \<rho> @ [[X \<union> Y]\<^sub>R] \<in> Q"
    using "4" TT2_def TT_def assms(2) by blast
  show "\<rho> @ [[X \<union> Y]\<^sub>R] \<in> P \<sqinter>\<^sub>C Q"
    using "1" "5" "6" IntChoiceTT_def by blast
next
  fix x
  show "x \<in> P \<sqinter>\<^sub>C Q \<Longrightarrow> TT3_trace x"
    by (metis TT3_def TT_TT3 IntChoiceTT_def UnE assms(1) assms(2))
qed 

end