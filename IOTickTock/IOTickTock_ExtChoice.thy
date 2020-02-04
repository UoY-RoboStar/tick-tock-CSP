theory IOTickTock_ExtChoice
  imports IOTickTock_Core
begin

lemma IOTT0_ExtChoiceTT:
  assumes IOTT0_P: "IOTT0 Outs P"
  assumes IOTT0_Q: "IOTT0 Outs Q"
  shows "IOTT0 Outs (P \<box>\<^sub>C Q)"
  unfolding IOTT0_def ExtChoiceTT_def
proof auto
  fix \<rho> \<sigma> \<tau> :: "'a tttrace"
  assume assm1: "\<rho> \<in> tocks UNIV"
  assume assm2: "\<rho> @ \<sigma> \<in> P"
  assume assm3: "\<rho> @ \<tau> \<in> Q"
  assume assm4: "\<forall>\<rho>'\<in>tocks UNIV. \<rho>' \<le>\<^sub>C \<rho> @ \<sigma> \<longrightarrow> \<rho>' \<le>\<^sub>C \<rho>"
  assume assm5: "\<forall>\<rho>'\<in>tocks UNIV. \<rho>' \<le>\<^sub>C \<rho> @ \<tau> \<longrightarrow> \<rho>' \<le>\<^sub>C \<rho>"
  assume assm6: "\<forall>X. \<sigma> = [[X]\<^sub>R] \<longrightarrow> (\<exists>Y. \<tau> = [[Y]\<^sub>R] \<and> (\<forall>e. (e \<in> X) = (e \<in> Y) \<or> e = Tock))"
  assume assm7: "\<forall>X. \<tau> = [[X]\<^sub>R] \<longrightarrow> (\<exists>Y. \<sigma> = [[Y]\<^sub>R] \<and> (\<forall>e. (e \<in> X) = (e \<in> Y) \<or> e = Tock))"

  have 1: "IOTT0_trace Outs \<rho> \<in> tocks UNIV"
    by (meson IOTT0_def IOTT0_tocks assm1 subset_UNIV)
  have 2: "IOTT0_trace Outs \<rho> @ IOTT0_trace Outs \<sigma> \<in> P"
    using IOTT0_P assm2 unfolding IOTT0_def by (metis IOTT0_trace_append) 
  have 3: "IOTT0_trace Outs \<rho> @ IOTT0_trace Outs \<tau> \<in> Q"
    using IOTT0_Q assm3 unfolding IOTT0_def by (metis IOTT0_trace_append)
  have 4: "\<forall>\<rho>'\<in>tocks UNIV. \<rho>' \<le>\<^sub>C IOTT0_trace Outs \<rho> @ IOTT0_trace Outs \<sigma> \<longrightarrow> \<rho>' \<le>\<^sub>C IOTT0_trace Outs \<rho>"
  proof (auto)
    fix \<rho>'
    assume case_assms2: "\<rho>' \<in> tocks UNIV" "\<rho>' \<le>\<^sub>C IOTT0_trace Outs \<rho> @ IOTT0_trace Outs \<sigma>" 
    have "\<rho>' \<le>\<^sub>C IOTT0_trace Outs (\<rho> @ \<sigma>)"
      by (simp add: IOTT0_trace_append case_assms2(2))
    then obtain \<rho>'' where \<rho>''_assms: "\<rho>'' \<le>\<^sub>C \<rho> @ \<sigma> \<and> \<rho>' = IOTT0_trace Outs \<rho>'' \<and> \<rho>'' \<in> tocks UNIV"
      using IOTT0_trace_prefix_monotonic_inv IOTT0_trace_tocks_imp2 case_assms2(1) by blast
    then have "\<rho>'' \<le>\<^sub>C \<rho>"
      using assm4 case_assms2 by (erule_tac x=\<rho>'' in ballE, auto)
    then show "\<rho>' \<le>\<^sub>C IOTT0_trace Outs \<rho>"
      using IOTT0_trace_prefix_monotonic \<rho>''_assms by blast
  qed
  have 5: "\<forall>\<rho>'\<in>tocks UNIV. \<rho>' \<le>\<^sub>C IOTT0_trace Outs \<rho> @ IOTT0_trace Outs \<tau> \<longrightarrow> \<rho>' \<le>\<^sub>C IOTT0_trace Outs \<rho>"
  proof (auto)
    fix \<rho>'
    assume case_assms2: "\<rho>' \<in> tocks UNIV" "\<rho>' \<le>\<^sub>C IOTT0_trace Outs \<rho> @ IOTT0_trace Outs \<tau>" 
    have "\<rho>' \<le>\<^sub>C IOTT0_trace Outs (\<rho> @ \<tau>)"
      by (simp add: IOTT0_trace_append case_assms2(2))
    then obtain \<rho>'' where \<rho>''_assms: "\<rho>'' \<le>\<^sub>C \<rho> @ \<tau> \<and> \<rho>' = IOTT0_trace Outs \<rho>'' \<and> \<rho>'' \<in> tocks UNIV"
      using IOTT0_trace_prefix_monotonic_inv IOTT0_trace_tocks_imp2 case_assms2(1) by blast
    then have "\<rho>'' \<le>\<^sub>C \<rho>"
      using assm5 case_assms2 by (erule_tac x=\<rho>'' in ballE, auto)
    then show "\<rho>' \<le>\<^sub>C IOTT0_trace Outs \<rho>"
      using IOTT0_trace_prefix_monotonic \<rho>''_assms by blast
  qed
  have 6: "\<forall>X. IOTT0_trace Outs \<sigma> = [[X]\<^sub>R] \<longrightarrow> (\<exists>Y. IOTT0_trace Outs \<tau> = [[Y]\<^sub>R] \<and> (\<forall>e. (e \<in> X) = (e \<in> Y) \<or> e = Tock))"
  proof auto
    fix X
    assume case_assm2: "IOTT0_trace Outs \<sigma> = [[X]\<^sub>R]"
    then obtain X' where X'_assm: "\<sigma> = [[X']\<^sub>R]"
      by (cases \<sigma> rule:ttWF.cases, auto)
    then have X_def: "X = X' \<union> Event ` Outs"
      using case_assm2 by auto
    then obtain Y' where "\<tau> = [[Y']\<^sub>R] \<and> (\<forall>e. (e \<in> X') = (e \<in> Y') \<or> e = Tock)"
      using X'_assm assm6 by blast
    from this and X_def show "\<exists>Y. IOTT0_trace Outs \<tau> = [[Y]\<^sub>R] \<and> (\<forall>e. (e \<in> X) = (e \<in> Y) \<or> e = Tock)"
      by (rule_tac x="Y' \<union> Event ` Outs" in exI, auto)
  qed
  have 7: "\<forall>X. IOTT0_trace Outs \<tau> = [[X]\<^sub>R] \<longrightarrow> (\<exists>Y. IOTT0_trace Outs \<sigma> = [[Y]\<^sub>R] \<and> (\<forall>e. (e \<in> X) = (e \<in> Y) \<or> e = Tock))"
  proof auto
    fix X
    assume case_assm2: "IOTT0_trace Outs \<tau> = [[X]\<^sub>R]"
    then obtain X' where X'_assm: "\<tau> = [[X']\<^sub>R]"
      by (cases \<tau> rule:ttWF.cases, auto)
    then have X_def: "X = X' \<union> Event ` Outs"
      using case_assm2 by auto
    then obtain Y' where "\<sigma> = [[Y']\<^sub>R] \<and> (\<forall>e. (e \<in> X') = (e \<in> Y') \<or> e = Tock)"
      using X'_assm assm7 by blast
    from this and X_def show "\<exists>Y. IOTT0_trace Outs \<sigma> = [[Y]\<^sub>R] \<and> (\<forall>e. (e \<in> X) = (e \<in> Y) \<or> e = Tock)"
      by (rule_tac x="Y' \<union> Event ` Outs" in exI, auto)
  qed
  show "\<exists>\<rho>'\<in>tocks UNIV. \<exists>\<sigma>'. \<rho>' @ \<sigma>' \<in> P \<and> (\<exists>\<tau>. \<rho>' @ \<tau> \<in> Q \<and>
    (\<forall>\<rho>''\<in>tocks UNIV. \<rho>'' \<le>\<^sub>C \<rho>' @ \<sigma>' \<longrightarrow> \<rho>'' \<le>\<^sub>C \<rho>') \<and>
    (\<forall>\<rho>''\<in>tocks UNIV. \<rho>'' \<le>\<^sub>C \<rho>' @ \<tau> \<longrightarrow> \<rho>'' \<le>\<^sub>C \<rho>') \<and>
    (\<forall>X. \<sigma>' = [[X]\<^sub>R] \<longrightarrow> (\<exists>Y. \<tau> = [[Y]\<^sub>R] \<and> (\<forall>e. (e \<in> X) = (e \<in> Y) \<or> e = Tock))) \<and>
    (\<forall>X. \<tau> = [[X]\<^sub>R] \<longrightarrow> (\<exists>Y. \<sigma>' = [[Y]\<^sub>R] \<and> (\<forall>e. (e \<in> X) = (e \<in> Y) \<or> e = Tock))) \<and>
      (IOTT0_trace Outs (\<rho> @ \<sigma>) = \<rho>' @ \<sigma>' \<or> IOTT0_trace Outs (\<rho> @ \<sigma>) = \<rho>' @ \<tau>))"
    using 1 2 3 4 5 6 7 IOTT0_trace_append
    by (rule_tac x="IOTT0_trace Outs \<rho>" in bexI, auto, rule_tac x="IOTT0_trace Outs \<sigma>" in exI, auto)
next
  fix \<rho> \<sigma> \<tau> :: "'a tttrace"
  assume assm1: "\<rho> \<in> tocks UNIV"
  assume assm2: "\<rho> @ \<sigma> \<in> P"
  assume assm3: "\<rho> @ \<tau> \<in> Q"
  assume assm4: "\<forall>\<rho>'\<in>tocks UNIV. \<rho>' \<le>\<^sub>C \<rho> @ \<sigma> \<longrightarrow> \<rho>' \<le>\<^sub>C \<rho>"
  assume assm5: "\<forall>\<rho>'\<in>tocks UNIV. \<rho>' \<le>\<^sub>C \<rho> @ \<tau> \<longrightarrow> \<rho>' \<le>\<^sub>C \<rho>"
  assume assm6: "\<forall>X. \<sigma> = [[X]\<^sub>R] \<longrightarrow> (\<exists>Y. \<tau> = [[Y]\<^sub>R] \<and> (\<forall>e. (e \<in> X) = (e \<in> Y) \<or> e = Tock))"
  assume assm7: "\<forall>X. \<tau> = [[X]\<^sub>R] \<longrightarrow> (\<exists>Y. \<sigma> = [[Y]\<^sub>R] \<and> (\<forall>e. (e \<in> X) = (e \<in> Y) \<or> e = Tock))"

  have 1: "IOTT0_trace Outs \<rho> \<in> tocks UNIV"
    by (meson IOTT0_def IOTT0_tocks assm1 subset_UNIV)
  have 2: "IOTT0_trace Outs \<rho> @ IOTT0_trace Outs \<sigma> \<in> P"
    using IOTT0_P assm2 unfolding IOTT0_def by (metis IOTT0_trace_append) 
  have 3: "IOTT0_trace Outs \<rho> @ IOTT0_trace Outs \<tau> \<in> Q"
    using IOTT0_Q assm3 unfolding IOTT0_def by (metis IOTT0_trace_append)
  have 4: "\<forall>\<rho>'\<in>tocks UNIV. \<rho>' \<le>\<^sub>C IOTT0_trace Outs \<rho> @ IOTT0_trace Outs \<sigma> \<longrightarrow> \<rho>' \<le>\<^sub>C IOTT0_trace Outs \<rho>"
  proof (auto)
    fix \<rho>'
    assume case_assms2: "\<rho>' \<in> tocks UNIV" "\<rho>' \<le>\<^sub>C IOTT0_trace Outs \<rho> @ IOTT0_trace Outs \<sigma>" 
    have "\<rho>' \<le>\<^sub>C IOTT0_trace Outs (\<rho> @ \<sigma>)"
      by (simp add: IOTT0_trace_append case_assms2(2))
    then obtain \<rho>'' where \<rho>''_assms: "\<rho>'' \<le>\<^sub>C \<rho> @ \<sigma> \<and> \<rho>' = IOTT0_trace Outs \<rho>'' \<and> \<rho>'' \<in> tocks UNIV"
      using IOTT0_trace_prefix_monotonic_inv IOTT0_trace_tocks_imp2 case_assms2(1) by blast
    then have "\<rho>'' \<le>\<^sub>C \<rho>"
      using assm4 case_assms2 by (erule_tac x=\<rho>'' in ballE, auto)
    then show "\<rho>' \<le>\<^sub>C IOTT0_trace Outs \<rho>"
      using IOTT0_trace_prefix_monotonic \<rho>''_assms by blast
  qed
  have 5: "\<forall>\<rho>'\<in>tocks UNIV. \<rho>' \<le>\<^sub>C IOTT0_trace Outs \<rho> @ IOTT0_trace Outs \<tau> \<longrightarrow> \<rho>' \<le>\<^sub>C IOTT0_trace Outs \<rho>"
  proof (auto)
    fix \<rho>'
    assume case_assms2: "\<rho>' \<in> tocks UNIV" "\<rho>' \<le>\<^sub>C IOTT0_trace Outs \<rho> @ IOTT0_trace Outs \<tau>" 
    have "\<rho>' \<le>\<^sub>C IOTT0_trace Outs (\<rho> @ \<tau>)"
      by (simp add: IOTT0_trace_append case_assms2(2))
    then obtain \<rho>'' where \<rho>''_assms: "\<rho>'' \<le>\<^sub>C \<rho> @ \<tau> \<and> \<rho>' = IOTT0_trace Outs \<rho>'' \<and> \<rho>'' \<in> tocks UNIV"
      using IOTT0_trace_prefix_monotonic_inv IOTT0_trace_tocks_imp2 case_assms2(1) by blast
    then have "\<rho>'' \<le>\<^sub>C \<rho>"
      using assm5 case_assms2 by (erule_tac x=\<rho>'' in ballE, auto)
    then show "\<rho>' \<le>\<^sub>C IOTT0_trace Outs \<rho>"
      using IOTT0_trace_prefix_monotonic \<rho>''_assms by blast
  qed
  have 6: "\<forall>X. IOTT0_trace Outs \<sigma> = [[X]\<^sub>R] \<longrightarrow> (\<exists>Y. IOTT0_trace Outs \<tau> = [[Y]\<^sub>R] \<and> (\<forall>e. (e \<in> X) = (e \<in> Y) \<or> e = Tock))"
  proof auto
    fix X
    assume case_assm2: "IOTT0_trace Outs \<sigma> = [[X]\<^sub>R]"
    then obtain X' where X'_assm: "\<sigma> = [[X']\<^sub>R]"
      by (cases \<sigma> rule:ttWF.cases, auto)
    then have X_def: "X = X' \<union> Event ` Outs"
      using case_assm2 by auto
    then obtain Y' where "\<tau> = [[Y']\<^sub>R] \<and> (\<forall>e. (e \<in> X') = (e \<in> Y') \<or> e = Tock)"
      using X'_assm assm6 by blast
    from this and X_def show "\<exists>Y. IOTT0_trace Outs \<tau> = [[Y]\<^sub>R] \<and> (\<forall>e. (e \<in> X) = (e \<in> Y) \<or> e = Tock)"
      by (rule_tac x="Y' \<union> Event ` Outs" in exI, auto)
  qed
  have 7: "\<forall>X. IOTT0_trace Outs \<tau> = [[X]\<^sub>R] \<longrightarrow> (\<exists>Y. IOTT0_trace Outs \<sigma> = [[Y]\<^sub>R] \<and> (\<forall>e. (e \<in> X) = (e \<in> Y) \<or> e = Tock))"
  proof auto
    fix X
    assume case_assm2: "IOTT0_trace Outs \<tau> = [[X]\<^sub>R]"
    then obtain X' where X'_assm: "\<tau> = [[X']\<^sub>R]"
      by (cases \<tau> rule:ttWF.cases, auto)
    then have X_def: "X = X' \<union> Event ` Outs"
      using case_assm2 by auto
    then obtain Y' where "\<sigma> = [[Y']\<^sub>R] \<and> (\<forall>e. (e \<in> X') = (e \<in> Y') \<or> e = Tock)"
      using X'_assm assm7 by blast
    from this and X_def show "\<exists>Y. IOTT0_trace Outs \<sigma> = [[Y]\<^sub>R] \<and> (\<forall>e. (e \<in> X) = (e \<in> Y) \<or> e = Tock)"
      by (rule_tac x="Y' \<union> Event ` Outs" in exI, auto)
  qed
  show "\<exists>\<rho>'\<in>tocks UNIV. \<exists>\<sigma>. \<rho>' @ \<sigma> \<in> P \<and> (\<exists>\<tau>'. \<rho>' @ \<tau>' \<in> Q \<and>
    (\<forall>\<rho>''\<in>tocks UNIV. \<rho>'' \<le>\<^sub>C \<rho>' @ \<sigma> \<longrightarrow> \<rho>'' \<le>\<^sub>C \<rho>') \<and>
    (\<forall>\<rho>''\<in>tocks UNIV. \<rho>'' \<le>\<^sub>C \<rho>' @ \<tau>' \<longrightarrow> \<rho>'' \<le>\<^sub>C \<rho>') \<and>
    (\<forall>X. \<sigma> = [[X]\<^sub>R] \<longrightarrow> (\<exists>Y. \<tau>' = [[Y]\<^sub>R] \<and> (\<forall>e. (e \<in> X) = (e \<in> Y) \<or> e = Tock))) \<and>
    (\<forall>X. \<tau>' = [[X]\<^sub>R] \<longrightarrow> (\<exists>Y. \<sigma> = [[Y]\<^sub>R] \<and> (\<forall>e. (e \<in> X) = (e \<in> Y) \<or> e = Tock))) \<and>
      (IOTT0_trace Outs (\<rho> @ \<tau>) = \<rho>' @ \<sigma> \<or> IOTT0_trace Outs (\<rho> @ \<tau>) = \<rho>' @ \<tau>'))"
    using 1 2 3 4 5 6 7 IOTT0_trace_append
    by (rule_tac x="IOTT0_trace Outs \<rho>" in bexI, auto, rule_tac x="IOTT0_trace Outs \<sigma>" in exI, auto)
qed