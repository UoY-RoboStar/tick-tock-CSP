theory CTockTick
  imports CTockTick_Basic_Ops CTockTick_Prefix CTockTick_IntChoice CTockTick_ExtChoice CTockTick_SeqComp CTockTick_ParComp
begin


subsection {* Compositionality *}

lemma Prefix_compositional: 
  "P \<sqsubseteq>\<^sub>C Q \<Longrightarrow> e \<rightarrow>\<^sub>C P \<sqsubseteq>\<^sub>C e \<rightarrow>\<^sub>C Q"
  unfolding RefinesCTT_def PrefixCTT_def by auto

lemma IntChoice_compositional1: 
  "P \<sqsubseteq>\<^sub>C Q \<Longrightarrow> P \<sqinter>\<^sub>C R \<sqsubseteq>\<^sub>C Q \<sqinter>\<^sub>C R"
  unfolding RefinesCTT_def IntChoiceCTT_def by auto

lemma IntChoice_compositional2: 
  "P \<sqsubseteq>\<^sub>C Q \<Longrightarrow> R \<sqinter>\<^sub>C P \<sqsubseteq>\<^sub>C R \<sqinter>\<^sub>C Q"
  unfolding RefinesCTT_def IntChoiceCTT_def by auto

lemma ExtChoice_compositional1: 
  "P \<sqsubseteq>\<^sub>C Q \<Longrightarrow> P \<box>\<^sub>C R \<sqsubseteq>\<^sub>C Q \<box>\<^sub>C R"
  unfolding RefinesCTT_def ExtChoiceCTT_def by auto

lemma ExtChoice_compositional2: 
  "P \<sqsubseteq>\<^sub>C Q \<Longrightarrow> R \<box>\<^sub>C P \<sqsubseteq>\<^sub>C R \<box>\<^sub>C Q"
  unfolding RefinesCTT_def ExtChoiceCTT_def by auto

lemma SeqComp_compositional1: 
  "P \<sqsubseteq>\<^sub>C Q \<Longrightarrow> P ;\<^sub>C R \<sqsubseteq>\<^sub>C Q ;\<^sub>C R"
  unfolding RefinesCTT_def SeqCompCTT_def by auto

lemma SeqComp_compositional2: 
  "P \<sqsubseteq>\<^sub>C Q \<Longrightarrow> R ;\<^sub>C P \<sqsubseteq>\<^sub>C R ;\<^sub>C Q"
  unfolding RefinesCTT_def SeqCompCTT_def by auto

end