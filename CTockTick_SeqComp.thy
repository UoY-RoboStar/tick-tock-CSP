theory CTockTick_SeqComp
  imports CTockTick_Core
begin

subsection {* Sequential Composition *}

definition SeqCompCTT :: "'e cttobs list set \<Rightarrow> 'e cttobs list set \<Rightarrow> 'e cttobs list set" (infixl ";\<^sub>C" 60) where
  "P ;\<^sub>C Q = P \<union> {\<rho>. \<exists> s t. s @ [[Tick]\<^sub>E] \<in> P \<and> t \<in> Q \<and> \<rho> = s @ t}"

lemma SeqComp_wf: "\<forall> t\<in>P. cttWF t \<Longrightarrow> \<forall> t\<in>Q. cttWF t \<Longrightarrow> \<forall> t \<in> P ;\<^sub>C Q. cttWF t"
  unfolding SeqCompCTT_def
proof auto
  fix s ta
  assume "\<forall>x\<in>P. cttWF x" "s @ [[Tick]\<^sub>E] \<in> P"
  then have 1: "cttWF (s @ [[Tick]\<^sub>E])"
    by auto
  assume "\<forall>x\<in>Q. cttWF x" "ta \<in> Q"
  then have 2: "cttWF ta"
    by auto
  from 1 2 show "cttWF (s @ ta)"
    by (induct s rule:cttWF.induct, auto)
qed

lemma CT0_SeqComp: "CT0 P \<Longrightarrow> CT0 Q \<Longrightarrow> CT0 (P ;\<^sub>C Q)"
  unfolding SeqCompCTT_def CT0_def by auto

lemma CT1_SeqComp: "CT1 P \<Longrightarrow> CT1 Q \<Longrightarrow> CT1 (P ;\<^sub>C Q)"
  unfolding SeqCompCTT_def CT1_def
proof (safe, blast)
  fix \<rho> \<sigma> s t :: "'a cttobs list"
  assume assm1: "\<forall>\<rho> \<sigma>. \<rho> \<lesssim>\<^sub>C \<sigma> \<and> \<sigma> \<in> P \<longrightarrow> \<rho> \<in> P"
  assume assm2: "\<forall>\<rho> \<sigma>. \<rho> \<lesssim>\<^sub>C \<sigma> \<and> \<sigma> \<in> Q \<longrightarrow> \<rho> \<in> Q"
  assume assm3: "\<rho> \<notin> P"
  assume assm4: "\<rho> \<lesssim>\<^sub>C s @ t"
  assume assm5: "s @ [[Tick]\<^sub>E] \<in> P"
  assume assm6: "t \<in> Q"
  obtain r where 1: "\<rho> \<subseteq>\<^sub>C r \<and> r \<le>\<^sub>C s @ t"
    using assm4 ctt_prefix_subset_imp_ctt_subset_ctt_prefix by blast
  then obtain t' where 2: "r = s @ t' \<and> t' \<lesssim>\<^sub>C t"
    by (meson assm1 assm3 assm5 ctt_prefix_append_split ctt_prefix_concat ctt_prefix_imp_prefix_subset ctt_subset_imp_prefix_subset)
  then obtain s' t'' where 3: "s' \<subseteq>\<^sub>C s \<and> \<rho> = s' @ t''"
    using "1" ctt_prefix_concat ctt_prefix_ctt_subset ctt_prefix_split by blast
  then have 4: "t'' \<subseteq>\<^sub>C t'"
    using "1" "2" ctt_subset_remove_start by blast
  have "s' @ [[Tick]\<^sub>E] \<lesssim>\<^sub>C s @ [[Tick]\<^sub>E]"
    using 3 by (simp add: ctt_subset_end_event ctt_subset_imp_prefix_subset)
  then have 5: "s' @ [[Tick]\<^sub>E] \<in> P"
    using assm1 assm5 by blast
  have 6: "t'' \<in> Q"
    using "2" "4" assm2 assm6 ctt_subset_imp_prefix_subset by blast
  show "\<exists>s t. s @ [[Tick]\<^sub>E] \<in> P \<and> t \<in> Q \<and> \<rho> = s @ t"
    by (rule_tac x="s'" in exI, rule_tac x="t''" in exI, simp add: 3 5 6)
qed

lemma CT2_SeqComp: "CT P \<Longrightarrow> CT Q \<Longrightarrow> CT2 (P ;\<^sub>C Q)"
  unfolding SeqCompCTT_def CT2_def
proof auto
  fix \<rho> X Y
  assume assm1: "Y \<inter> {e. e \<noteq> Tock \<and> (\<rho> @ [[e]\<^sub>E] \<in> P \<or> (\<exists>s. s @ [[Tick]\<^sub>E] \<in> P \<and> (\<exists>t. t \<in> Q \<and> \<rho> @ [[e]\<^sub>E] = s @ t))) \<or>
                      e = Tock \<and>
                      (\<rho> @ [[X]\<^sub>R, [e]\<^sub>E] \<in> P \<or> (\<exists>s. s @ [[Tick]\<^sub>E] \<in> P \<and> (\<exists>t. t \<in> Q \<and> \<rho> @ [[X]\<^sub>R, [e]\<^sub>E] = s @ t)))} =
             {}"
  assume assm2: "CT P"
  assume assm3: "\<rho> @ [[X]\<^sub>R] \<in> P"
  have "Y \<inter> {e. e \<noteq> Tock \<and> (\<rho> @ [[e]\<^sub>E] \<in> P \<or> (\<exists>s. s @ [[Tick]\<^sub>E] \<in> P \<and> (\<exists>t. t \<in> Q \<and> \<rho> @ [[e]\<^sub>E] = s @ t))) \<or>
      e = Tock \<and> (\<rho> @ [[X]\<^sub>R, [e]\<^sub>E] \<in> P \<or> (\<exists>s. s @ [[Tick]\<^sub>E] \<in> P \<and> (\<exists>t. t \<in> Q \<and> \<rho> @ [[X]\<^sub>R, [e]\<^sub>E] = s @ t)))}
    = Y \<inter> ({e. e \<noteq> Tock \<and> \<rho> @ [[e]\<^sub>E] \<in> P \<or> e = Tock \<and> \<rho> @ [[X]\<^sub>R, [e]\<^sub>E] \<in> P}
      \<union> {e. e \<noteq> Tock \<and> (\<exists>s. s @ [[Tick]\<^sub>E] \<in> P \<and> (\<exists>t. t \<in> Q \<and> \<rho> @ [[e]\<^sub>E] = s @ t)) \<or>
        e = Tock \<and> (\<exists>s. s @ [[Tick]\<^sub>E] \<in> P \<and> (\<exists>t. t \<in> Q \<and> \<rho> @ [[X]\<^sub>R, [e]\<^sub>E] = s @ t))})"
    by auto
  then have "Y \<inter> ({e. e \<noteq> Tock \<and> \<rho> @ [[e]\<^sub>E] \<in> P \<or> e = Tock \<and> \<rho> @ [[X]\<^sub>R, [e]\<^sub>E] \<in> P}
      \<union> {e. e \<noteq> Tock \<and> (\<exists>s. s @ [[Tick]\<^sub>E] \<in> P \<and> (\<exists>t. t \<in> Q \<and> \<rho> @ [[e]\<^sub>E] = s @ t)) \<or>
        e = Tock \<and> (\<exists>s. s @ [[Tick]\<^sub>E] \<in> P \<and> (\<exists>t. t \<in> Q \<and> \<rho> @ [[X]\<^sub>R, [e]\<^sub>E] = s @ t))}) = {}"
    using assm1 by auto
  then have "(Y \<inter> {e. e \<noteq> Tock \<and> \<rho> @ [[e]\<^sub>E] \<in> P \<or> e = Tock \<and> \<rho> @ [[X]\<^sub>R, [e]\<^sub>E] \<in> P})
      \<union> (Y \<inter> {e. e \<noteq> Tock \<and> (\<exists>s. s @ [[Tick]\<^sub>E] \<in> P \<and> (\<exists>t. t \<in> Q \<and> \<rho> @ [[e]\<^sub>E] = s @ t)) \<or>
        e = Tock \<and> (\<exists>s. s @ [[Tick]\<^sub>E] \<in> P \<and> (\<exists>t. t \<in> Q \<and> \<rho> @ [[X]\<^sub>R, [e]\<^sub>E] = s @ t))}) = {}"
    by (simp add: Int_Un_distrib)  
  then have "Y \<inter> {e. e \<noteq> Tock \<and> \<rho> @ [[e]\<^sub>E] \<in> P \<or> e = Tock \<and> \<rho> @ [[X]\<^sub>R, [e]\<^sub>E] \<in> P} = {}
    \<and> Y \<inter> {e. e \<noteq> Tock \<and> (\<exists>s. s @ [[Tick]\<^sub>E] \<in> P \<and> (\<exists>t. t \<in> Q \<and> \<rho> @ [[e]\<^sub>E] = s @ t)) \<or>
        e = Tock \<and> (\<exists>s. s @ [[Tick]\<^sub>E] \<in> P \<and> (\<exists>t. t \<in> Q \<and> \<rho> @ [[X]\<^sub>R, [e]\<^sub>E] = s @ t))} = {}"
    by auto
  then show "\<rho> @ [[X \<union> Y]\<^sub>R] \<in> P"
    using CT2_def CT_CT2 assm2 assm3 by auto
next
  fix \<rho> X Y s t
  assume assm1: "Y \<inter> {e. e \<noteq> Tock \<and> (\<rho> @ [[e]\<^sub>E] \<in> P \<or> (\<exists>s. s @ [[Tick]\<^sub>E] \<in> P \<and> (\<exists>t. t \<in> Q \<and> \<rho> @ [[e]\<^sub>E] = s @ t))) \<or>
    e = Tock \<and> (\<rho> @ [[X]\<^sub>R, [e]\<^sub>E] \<in> P \<or> (\<exists>s. s @ [[Tick]\<^sub>E] \<in> P \<and> (\<exists>t. t \<in> Q \<and> \<rho> @ [[X]\<^sub>R, [e]\<^sub>E] = s @ t)))} = {}"
  assume assm2: "CT P"
  assume assm3: "CT Q"
  assume assm4: "\<forall>s. s @ [[Tick]\<^sub>E] \<in> P \<longrightarrow> (\<forall>t. t \<in> Q \<longrightarrow> \<rho> @ [[X \<union> Y]\<^sub>R] \<noteq> s @ t)"
  assume assm5: "s @ [[Tick]\<^sub>E] \<in> P"
  assume assm6: "t \<in> Q"
  assume assm7: "\<rho> @ [[X]\<^sub>R] = s @ t"
  have "t = [] \<or> (\<exists> t'. t = t' @ [[X]\<^sub>R])"
    by (metis append_butlast_last_id assm7 last_appendR last_snoc) 
  then show "\<rho> @ [[X \<union> Y]\<^sub>R] \<in> P"
  proof auto
    assume case_assm: "t = []"
    then have "s = \<rho> @ [[X]\<^sub>R]"
      by (simp add: assm7)
    then have "\<rho> @ [[X]\<^sub>R, [Tick]\<^sub>E] \<in> P"
      using assm5 by auto
    then have "cttWF (\<rho> @ [[X]\<^sub>R, [Tick]\<^sub>E])"
      using CT_wf assm2 by blast
    then have "False"
      by (induct \<rho> rule:cttWF.induct, auto)
    then show "\<rho> @ [[X \<union> Y]\<^sub>R] \<in> P"
      by auto
  next
    fix t'
    assume case_assm: "t = t' @ [[X]\<^sub>R]"
    then have 1: "{e. e \<noteq> Tock \<and> t' @ [[e]\<^sub>E] \<in> Q \<or> e = Tock \<and> t' @ [[X]\<^sub>R, [e]\<^sub>E] \<in> Q}
      \<subseteq> {e. e \<noteq> Tock \<and> (\<exists>s. s @ [[Tick]\<^sub>E] \<in> P \<and> (\<exists>t. t \<in> Q \<and> \<rho> @ [[e]\<^sub>E] = s @ t)) \<or>
          e = Tock \<and> (\<exists>s. s @ [[Tick]\<^sub>E] \<in> P \<and> (\<exists>t. t \<in> Q \<and> \<rho> @ [[X]\<^sub>R, [e]\<^sub>E] = s @ t))}"
      using assm5 assm7 by auto
    have "Y \<inter> {e. e \<noteq> Tock \<and> (\<rho> @ [[e]\<^sub>E] \<in> P \<or> (\<exists>s. s @ [[Tick]\<^sub>E] \<in> P \<and> (\<exists>t. t \<in> Q \<and> \<rho> @ [[e]\<^sub>E] = s @ t))) \<or>
        e = Tock \<and> (\<rho> @ [[X]\<^sub>R, [e]\<^sub>E] \<in> P \<or> (\<exists>s. s @ [[Tick]\<^sub>E] \<in> P \<and> (\<exists>t. t \<in> Q \<and> \<rho> @ [[X]\<^sub>R, [e]\<^sub>E] = s @ t)))}
      = Y \<inter> ({e. e \<noteq> Tock \<and> \<rho> @ [[e]\<^sub>E] \<in> P \<or> e = Tock \<and> \<rho> @ [[X]\<^sub>R, [e]\<^sub>E] \<in> P}
        \<union> {e. e \<noteq> Tock \<and> (\<exists>s. s @ [[Tick]\<^sub>E] \<in> P \<and> (\<exists>t. t \<in> Q \<and> \<rho> @ [[e]\<^sub>E] = s @ t)) \<or>
          e = Tock \<and> (\<exists>s. s @ [[Tick]\<^sub>E] \<in> P \<and> (\<exists>t. t \<in> Q \<and> \<rho> @ [[X]\<^sub>R, [e]\<^sub>E] = s @ t))})"
      by auto
    then have "Y \<inter> ({e. e \<noteq> Tock \<and> \<rho> @ [[e]\<^sub>E] \<in> P \<or> e = Tock \<and> \<rho> @ [[X]\<^sub>R, [e]\<^sub>E] \<in> P}
        \<union> {e. e \<noteq> Tock \<and> (\<exists>s. s @ [[Tick]\<^sub>E] \<in> P \<and> (\<exists>t. t \<in> Q \<and> \<rho> @ [[e]\<^sub>E] = s @ t)) \<or>
          e = Tock \<and> (\<exists>s. s @ [[Tick]\<^sub>E] \<in> P \<and> (\<exists>t. t \<in> Q \<and> \<rho> @ [[X]\<^sub>R, [e]\<^sub>E] = s @ t))}) = {}"
      using assm1 by auto
    then have "(Y \<inter> {e. e \<noteq> Tock \<and> \<rho> @ [[e]\<^sub>E] \<in> P \<or> e = Tock \<and> \<rho> @ [[X]\<^sub>R, [e]\<^sub>E] \<in> P})
        \<union> (Y \<inter> {e. e \<noteq> Tock \<and> (\<exists>s. s @ [[Tick]\<^sub>E] \<in> P \<and> (\<exists>t. t \<in> Q \<and> \<rho> @ [[e]\<^sub>E] = s @ t)) \<or>
          e = Tock \<and> (\<exists>s. s @ [[Tick]\<^sub>E] \<in> P \<and> (\<exists>t. t \<in> Q \<and> \<rho> @ [[X]\<^sub>R, [e]\<^sub>E] = s @ t))}) = {}"
      by (simp add: Int_Un_distrib)  
    then have "Y \<inter> {e. e \<noteq> Tock \<and> \<rho> @ [[e]\<^sub>E] \<in> P \<or> e = Tock \<and> \<rho> @ [[X]\<^sub>R, [e]\<^sub>E] \<in> P} = {}
      \<and> Y \<inter> {e. e \<noteq> Tock \<and> (\<exists>s. s @ [[Tick]\<^sub>E] \<in> P \<and> (\<exists>t. t \<in> Q \<and> \<rho> @ [[e]\<^sub>E] = s @ t)) \<or>
          e = Tock \<and> (\<exists>s. s @ [[Tick]\<^sub>E] \<in> P \<and> (\<exists>t. t \<in> Q \<and> \<rho> @ [[X]\<^sub>R, [e]\<^sub>E] = s @ t))} = {}"
      by auto    
    then have "Y \<inter> {e. e \<noteq> Tock \<and> \<rho> @ [[e]\<^sub>E] \<in> P \<or> e = Tock \<and> \<rho> @ [[X]\<^sub>R, [e]\<^sub>E] \<in> P} = {}
        \<and> Y \<inter> {e. e \<noteq> Tock \<and> t' @ [[e]\<^sub>E] \<in> Q \<or> e = Tock \<and> t' @ [[X]\<^sub>R, [e]\<^sub>E] \<in> Q} = {}"
      by (metis (no_types, lifting) 1 Int_left_commute inf.orderE inf_bot_right)
    then have "t' @ [[X \<union> Y]\<^sub>R] \<in> Q"
      using CT2_def CT_def assm3 assm6 case_assm by auto
    then have "\<rho> @ [[X \<union> Y]\<^sub>R] \<noteq> s @ t' @ [[X \<union> Y]\<^sub>R]"
      using assm4 assm5 by auto
    then have "False"
      using case_assm assm7 by auto
    then show "\<rho> @ [[X \<union> Y]\<^sub>R] \<in> P"
      by auto
  qed
qed

lemma CT3_SeqComp: 
  assumes "CT P" "CT Q"
  shows "CT3 (P ;\<^sub>C Q)"
  unfolding CT3_def SeqCompCTT_def
proof auto
  fix x
  show "x \<in> P \<Longrightarrow> CT3_trace x"
    using CT3_def CT_CT3 assms(1) by blast
next
  fix s t
  assume "s @ [[Tick]\<^sub>E] \<in> P"
  then have 1: "CT3_trace s"
    by (meson CT1_def CT3_def CT_CT1 CT_CT3 assms(1) ctt_prefix_concat ctt_prefix_imp_prefix_subset)
  assume "t \<in> Q"
  then have 2: "CT3_trace t \<and> cttWF t"
    using CT3_def CT_CT3 CT_wf assms(2) by blast
  show "CT3_trace (s @ t)"
    using 1 2 CT3_append by auto
qed     

lemma CT4s_SeqComp:
  assumes "CT4s P" "CT4s Q"
  shows "CT4s (P ;\<^sub>C Q)"
  unfolding SeqCompCTT_def CT4s_def
proof auto
  fix \<rho>
  show "\<rho> \<in> P \<Longrightarrow> add_Tick_refusal_trace \<rho> \<in> P"
    using CT4s_def assms(1) by blast
next
  fix s t
  assume "s @ [[Tick]\<^sub>E] \<in> P" "t \<in> Q"
  then have "add_Tick_refusal_trace s @ [[Tick]\<^sub>E] \<in> P \<and> add_Tick_refusal_trace t \<in> Q"
    by (metis CT4s_def add_Tick_refusal_trace_end_event assms(1) assms(2))
  then show "\<forall>sa. sa @ [[Tick]\<^sub>E] \<in> P \<longrightarrow> (\<forall>ta. ta \<in> Q \<longrightarrow> add_Tick_refusal_trace (s @ t) \<noteq> sa @ ta) \<Longrightarrow>
    add_Tick_refusal_trace (s @ t) \<in> P"
    using add_Tick_refusal_trace_concat by blast
qed

lemma CT_SeqComp: 
  assumes "CT P" "CT Q"
  shows "CT (P ;\<^sub>C Q)"
  unfolding CT_def apply auto
  apply (metis CT_def SeqComp_wf assms(1) assms(2))
  apply (simp add: CT0_SeqComp CT_CT0 assms(1) assms(2))
  apply (simp add: CT1_SeqComp CT_CT1 assms(1) assms(2))
  apply (simp add: CT2_SeqComp assms(1) assms(2))
  apply (simp add: CT3_SeqComp assms(1) assms(2))
  done

end