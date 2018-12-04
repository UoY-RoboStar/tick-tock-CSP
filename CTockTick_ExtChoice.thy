theory CTockTick_ExtChoice
  imports CTockTick_Core
begin

subsection {* External Choice *}

definition ExtChoiceCTT :: "'e cttobs list set \<Rightarrow> 'e cttobs list set \<Rightarrow> 'e cttobs list set" (infixl "\<box>\<^sub>C" 57) where
  "P \<box>\<^sub>C Q = {t. \<exists> \<rho>\<in>tocks(UNIV). \<exists> \<sigma> \<tau>. 
    \<rho> @ \<sigma> \<in> P \<and> \<rho> @ \<tau> \<in> Q \<and>
    (\<forall>\<rho>'\<in>tocks(UNIV). \<rho>' \<le>\<^sub>C \<rho> @ \<sigma> \<longrightarrow> \<rho>' \<le>\<^sub>C \<rho>) \<and>
    (\<forall>\<rho>'\<in>tocks(UNIV). \<rho>' \<le>\<^sub>C \<rho> @ \<tau> \<longrightarrow> \<rho>' \<le>\<^sub>C \<rho>) \<and>
    (\<forall> X. \<sigma> = [[X]\<^sub>R] \<longrightarrow> (\<exists> Y. \<tau> = [[Y]\<^sub>R] \<and> (\<forall> e. (e \<in> X = (e \<in> Y)) \<or> (e = Tock)))) \<and>
    (\<forall> X. \<tau> = [[X]\<^sub>R] \<longrightarrow> (\<exists> Y. \<sigma> = [[Y]\<^sub>R] \<and> (\<forall> e. (e \<in> X = (e \<in> Y)) \<or> (e = Tock)))) \<and>
    (t = \<rho> @ \<sigma> \<or> t = \<rho> @ \<tau>)}"

lemma ExtChoiceCTT_wf: "\<forall> t\<in>P. cttWF t \<Longrightarrow> \<forall> t\<in>Q. cttWF t \<Longrightarrow> \<forall> t\<in>P \<box>\<^sub>C Q. cttWF t"
  unfolding ExtChoiceCTT_def by auto

lemma CT0_ExtChoice:
  assumes "CT P" "CT Q"
  shows "CT0 (P \<box>\<^sub>C Q)"
  unfolding CT0_def apply auto
  unfolding ExtChoiceCTT_def apply auto
  using CT_empty assms(1) assms(2) tocks.empty_in_tocks by fastforce

lemma CT1_ExtChoice:
  assumes "CT P" "CT Q"
  shows "CT1 (P \<box>\<^sub>C Q)"
  unfolding CT1_def
proof auto
  fix \<rho> \<sigma> :: "'a cttobs list"
  assume assm1: "\<rho> \<lesssim>\<^sub>C \<sigma>"
  assume assm2: "\<sigma> \<in> P \<box>\<^sub>C Q"
  obtain \<rho>2 where \<rho>2_assms: "\<rho>2 \<le>\<^sub>C \<sigma>" "\<rho> \<subseteq>\<^sub>C \<rho>2"
    using assm1 ctt_prefix_subset_imp_ctt_subset_ctt_prefix by auto
  from assm2 obtain \<sigma>' s t where assm2_assms:
    "\<sigma>'\<in>tocks UNIV"
    "\<sigma>' @ s \<in> P"
    "\<sigma>' @ t \<in> Q"
    "(\<forall>\<rho>'\<in>tocks UNIV. \<rho>' \<le>\<^sub>C \<sigma>' @ s \<longrightarrow> \<rho>' \<le>\<^sub>C \<sigma>')"
    "(\<forall>\<rho>'\<in>tocks UNIV. \<rho>' \<le>\<^sub>C \<sigma>' @ t \<longrightarrow> \<rho>' \<le>\<^sub>C \<sigma>')"
    "\<forall>X. s = [[X]\<^sub>R] \<longrightarrow> (\<exists>Y. t = [[Y]\<^sub>R] \<and> (\<forall>e. (e \<in> X) = (e \<in> Y) \<or> e = Tock))"
    "\<forall>X. t = [[X]\<^sub>R] \<longrightarrow> (\<exists>Y. s = [[Y]\<^sub>R] \<and> (\<forall>e. (e \<in> X) = (e \<in> Y) \<or> e = Tock))"
    "\<sigma> = \<sigma>' @ t \<or> \<sigma> = \<sigma>' @ s"
    unfolding ExtChoiceCTT_def by blast
  from assm2_assms(8) have "\<rho>2 \<in> P \<box>\<^sub>C Q"
  proof (auto)
    assume case_assm: "\<sigma> = \<sigma>' @ s"
    then have \<sigma>_in_P: "\<sigma> \<in> P"
      using assm2_assms(2) by blast
    have \<rho>2_in_P: "\<rho>2 \<in> P"
      using CT1_def CT_CT1 \<rho>2_assms(1) \<sigma>_in_P assms(1) ctt_prefix_imp_prefix_subset by blast
    have "\<rho>2 \<le>\<^sub>C \<sigma>' \<or> (\<exists> \<rho>2'. \<rho>2 = \<sigma>' @ \<rho>2' \<and> \<rho>2' \<le>\<^sub>C s)"
      using \<rho>2_assms(1) case_assm ctt_prefix_append_split by blast
    then show "\<rho>2 \<in> P \<box>\<^sub>C Q"
    proof auto
      assume case_assm2: "\<rho>2 \<le>\<^sub>C \<sigma>'"
      have \<rho>2_in_Q: "\<rho>2 \<in> Q"
        by (meson CT1_def CT_CT1 assm2_assms(3) assms(2) case_assm2 ctt_prefix_concat ctt_prefix_imp_prefix_subset)
      obtain \<rho>' where \<rho>'_assms: "\<rho>' \<in> tocks UNIV" "\<rho>2 = \<rho>' \<or> (\<exists>Y. \<rho>2 = \<rho>' @ [[Y]\<^sub>R])"
        using case_assm2 assm2_assms(1) ctt_prefix_tocks by blast
      then show "\<rho>2 \<in> P \<box>\<^sub>C Q"
      proof auto
        assume case_assm3: "\<rho>2 = \<rho>'"
        then show "\<rho>' \<in> P \<box>\<^sub>C Q"
          using \<rho>2_in_P \<rho>2_in_Q case_assm3 \<rho>'_assms(1) unfolding ExtChoiceCTT_def apply auto
          apply (rule_tac x="\<rho>'" in bexI, auto)
          apply (rule_tac x="[]" in exI, auto)
          apply (rule_tac x="[]" in exI, auto)
          done
      next
        fix Y
        assume case_assm3: "\<rho>2 = \<rho>' @ [[Y]\<^sub>R]"
        then show "\<rho>' @ [[Y]\<^sub>R] \<in> P \<box>\<^sub>C Q"
          using \<rho>2_in_P \<rho>2_in_Q \<rho>'_assms(1) unfolding ExtChoiceCTT_def apply auto
          apply (rule_tac x="\<rho>'" in bexI, auto)
          apply (rule_tac x="[[Y]\<^sub>R]" in exI, auto)
          apply (rule_tac x="[[Y]\<^sub>R]" in exI, auto)
          by (metis butlast_append butlast_snoc ctt_prefix_concat ctt_prefix_decompose end_refusal_notin_tocks)
      qed
    next
      fix \<rho>2'
      assume case_assm2: "\<rho>2' \<le>\<^sub>C s"
      assume case_assm3: "\<rho>2 = \<sigma>' @ \<rho>2'"
      have in_P: "\<sigma>' @ \<rho>2' \<in> P"
        using CT1_def CT_CT1 \<rho>2_assms(1) assm2_assms(2) assms(1) case_assm case_assm3 ctt_prefix_imp_prefix_subset by blast
      show "\<sigma>' @ \<rho>2' \<in> P \<box>\<^sub>C Q"
      proof (cases "\<exists>X. \<rho>2' = [[X]\<^sub>R]", auto)
        fix X
        assume case_assm4: "\<rho>2' = [[X]\<^sub>R]"
        then have case_assm5: "s = [[X]\<^sub>R]"
          using case_assm2
        proof -
          have "cttWF s"
            using CT_wf assm2_assms(1) assm2_assms(2) assms(1) tocks_append_wf2 by fastforce
          then show "\<rho>2' = [[X]\<^sub>R] \<Longrightarrow> \<rho>2' \<le>\<^sub>C s \<Longrightarrow> s = [[X]\<^sub>R]"
            apply (cases s rule:cttWF.cases, auto, insert assm2_assms(1) assm2_assms(4))
            apply (erule_tac x="\<sigma>' @ [[X]\<^sub>R, [Tock]\<^sub>E]" in ballE, auto simp add: ctt_prefix_same_front)
            using ctt_prefix_antisym ctt_prefix_concat apply blast
            apply (induct \<sigma>', auto simp add: tocks.tock_insert_in_tocks)
            by (metis append_Cons subset_UNIV tocks.empty_in_tocks tocks.tock_insert_in_tocks tocks_append_tocks)
        qed
        thm assm2_assms
        then obtain Y where "t = [[Y]\<^sub>R]" "\<forall>e. (e \<in> X) = (e \<in> Y) \<or> e = Tock"
          using assm2_assms(6) by auto
        then have "\<sigma>' @ [[{e\<in>X. e \<noteq> Tock}]\<^sub>R] \<in> Q"
        proof -
          assume "t = [[Y]\<^sub>R]"
          then have "\<sigma>' @ [[Y]\<^sub>R] \<in> Q"
            using assm2_assms(3) by auto
          also assume "\<forall>e. (e \<in> X) = (e \<in> Y) \<or> e = Tock"
          then have "\<sigma>' @ [[{e\<in>X. e \<noteq> Tock}]\<^sub>R] \<lesssim>\<^sub>C \<sigma>' @ [[Y]\<^sub>R]"
            using ctt_prefix_subset_same_front[where r=\<sigma>'] by auto
          then show "\<sigma>' @ [[{e\<in>X. e \<noteq> Tock}]\<^sub>R] \<in> Q"
            using calculation CT1_def CT_CT1 assms(2) by blast
        qed
        then show "\<sigma>' @ [[X]\<^sub>R] \<in> P \<box>\<^sub>C Q"
          unfolding ExtChoiceCTT_def apply auto
          apply (rule_tac x="\<sigma>'" in bexI, simp_all add: assm2_assms(1))
          apply (rule_tac x="[[X]\<^sub>R]" in exI, insert in_P case_assm4, simp)
          apply (rule_tac x="[[{e\<in>X. e \<noteq> Tock}]\<^sub>R]" in exI, insert assm2_assms(4) case_assm5, auto)
          by (metis (no_types, lifting) butlast_append butlast_snoc ctt_prefix_concat ctt_prefix_decompose end_refusal_notin_tocks)
      next
        have \<sigma>'_in_Q: "\<sigma>' \<in> Q"
          using CT1_def CT_CT1 assm2_assms(3) assms(2) ctt_prefix_concat ctt_prefix_imp_prefix_subset by blast
        then show "\<forall>X. \<rho>2' \<noteq> [[X]\<^sub>R] \<Longrightarrow> \<sigma>' @ \<rho>2' \<in> P \<box>\<^sub>C Q"
           unfolding ExtChoiceCTT_def apply auto
           apply (rule_tac x="\<sigma>'" in bexI, simp_all add: assm2_assms(1))
           apply (rule_tac x="\<rho>2'" in exI, simp add: in_P)
           apply (rule_tac x="[]" in exI, auto)
           using \<rho>2_assms(1) assm2_assms(4) case_assm case_assm3 ctt_prefix_trans by blast
       qed
     qed
   next
    assume case_assm: "\<sigma> = \<sigma>' @ t"
    then have \<sigma>_in_Q: "\<sigma> \<in> Q"
      using assm2_assms(3) by blast
    have \<rho>2_in_Q: "\<rho>2 \<in> Q"
      using CT1_def CT_CT1 \<rho>2_assms(1) \<sigma>_in_Q assms(2) ctt_prefix_imp_prefix_subset by blast
    have "\<rho>2 \<le>\<^sub>C \<sigma>' \<or> (\<exists> \<rho>2'. \<rho>2 = \<sigma>' @ \<rho>2' \<and> \<rho>2' \<le>\<^sub>C t)"
      using \<rho>2_assms(1) case_assm ctt_prefix_append_split by blast
    then show "\<rho>2 \<in> P \<box>\<^sub>C Q"
    proof auto
      assume case_assm2: "\<rho>2 \<le>\<^sub>C \<sigma>'"
      have \<rho>2_in_P: "\<rho>2 \<in> P"
        by (meson CT1_def CT_CT1 assm2_assms(2) assms(1) case_assm2 ctt_prefix_concat ctt_prefix_imp_prefix_subset)
      obtain \<rho>' where \<rho>'_assms: "\<rho>' \<in> tocks UNIV" "\<rho>2 = \<rho>' \<or> (\<exists>Y. \<rho>2 = \<rho>' @ [[Y]\<^sub>R])"
        using case_assm2 assm2_assms(1) ctt_prefix_tocks by blast
      then show "\<rho>2 \<in> P \<box>\<^sub>C Q"
      proof auto
        assume case_assm3: "\<rho>2 = \<rho>'"
        then show "\<rho>' \<in> P \<box>\<^sub>C Q"
          using \<rho>2_in_P \<rho>2_in_Q case_assm3 \<rho>'_assms(1) unfolding ExtChoiceCTT_def apply auto
          apply (rule_tac x="\<rho>'" in bexI, auto)
          apply (rule_tac x="[]" in exI, auto)
          apply (rule_tac x="[]" in exI, auto)
          done
      next
        fix Y
        assume case_assm3: "\<rho>2 = \<rho>' @ [[Y]\<^sub>R]"
        then show "\<rho>' @ [[Y]\<^sub>R] \<in> P \<box>\<^sub>C Q"
          using \<rho>2_in_P \<rho>2_in_Q \<rho>'_assms(1) unfolding ExtChoiceCTT_def apply auto
          apply (rule_tac x="\<rho>'" in bexI, auto)
          apply (rule_tac x="[[Y]\<^sub>R]" in exI, auto)
          apply (rule_tac x="[[Y]\<^sub>R]" in exI, auto)
          by (metis butlast_append butlast_snoc ctt_prefix_concat ctt_prefix_decompose end_refusal_notin_tocks)
      qed
    next
      fix \<rho>2'
      assume case_assm2: "\<rho>2' \<le>\<^sub>C t"
      assume case_assm3: "\<rho>2 = \<sigma>' @ \<rho>2'"
      have in_Q: "\<sigma>' @ \<rho>2' \<in> Q"
        using \<rho>2_in_Q case_assm3 by blast
      show "\<sigma>' @ \<rho>2' \<in> P \<box>\<^sub>C Q"
      proof (cases "\<exists>X. \<rho>2' = [[X]\<^sub>R]", auto)
        fix X
        assume case_assm4: "\<rho>2' = [[X]\<^sub>R]"
        then have case_assm5: "t = [[X]\<^sub>R]"
          using case_assm2
        proof -
          have "cttWF t"
            using CT_wf assm2_assms(1) assm2_assms(3) assms(2) tocks_append_wf2 by fastforce
          then show "\<rho>2' = [[X]\<^sub>R] \<Longrightarrow> \<rho>2' \<le>\<^sub>C t \<Longrightarrow> t = [[X]\<^sub>R]"
            apply (cases t rule:cttWF.cases, auto, insert assm2_assms(1) assm2_assms(5))
            apply (erule_tac x="\<sigma>' @ [[X]\<^sub>R, [Tock]\<^sub>E]" in ballE, auto simp add: ctt_prefix_same_front)
            using ctt_prefix_antisym ctt_prefix_concat apply blast
            apply (induct \<sigma>', auto simp add: tocks.tock_insert_in_tocks)
            by (metis append_Cons subset_UNIV tocks.empty_in_tocks tocks.tock_insert_in_tocks tocks_append_tocks)
        qed
        then obtain Y where "s = [[Y]\<^sub>R]" "\<forall>e. (e \<in> X) = (e \<in> Y) \<or> e = Tock"
          using assm2_assms(7) by auto
        then have "\<sigma>' @ [[{e\<in>X. e \<noteq> Tock}]\<^sub>R] \<in> P"
        proof -
          assume "s = [[Y]\<^sub>R]"
          then have "\<sigma>' @ [[Y]\<^sub>R] \<in> P"
            using assm2_assms(2) by auto
          also assume "\<forall>e. (e \<in> X) = (e \<in> Y) \<or> e = Tock"
          then have "\<sigma>' @ [[{e\<in>X. e \<noteq> Tock}]\<^sub>R] \<lesssim>\<^sub>C \<sigma>' @ [[Y]\<^sub>R]"
            using ctt_prefix_subset_same_front[where r=\<sigma>'] by auto
          then show "\<sigma>' @ [[{e\<in>X. e \<noteq> Tock}]\<^sub>R] \<in> P"
            using calculation CT1_def CT_CT1 assms(1) by blast
        qed
        then show "\<sigma>' @ [[X]\<^sub>R] \<in> P \<box>\<^sub>C Q"
          unfolding ExtChoiceCTT_def apply auto
          apply (rule_tac x="\<sigma>'" in bexI, simp_all add: assm2_assms(1))
          apply (rule_tac x="[[{e\<in>X. e \<noteq> Tock}]\<^sub>R]" in exI, insert assm2_assms(4) case_assm5, auto)
          apply (rule_tac x="[[X]\<^sub>R]" in exI, insert in_Q case_assm4 assm2_assms(5), auto)
          by (metis (no_types, lifting) butlast_append butlast_snoc ctt_prefix_concat ctt_prefix_decompose end_refusal_notin_tocks)
      next
        have \<sigma>'_in_P: "\<sigma>' \<in> P"
          using CT1_def CT_CT1 assm2_assms(2) assms(1) ctt_prefix_concat ctt_prefix_imp_prefix_subset by blast
        then show "\<forall>X. \<rho>2' \<noteq> [[X]\<^sub>R] \<Longrightarrow> \<sigma>' @ \<rho>2' \<in> P \<box>\<^sub>C Q"
           unfolding ExtChoiceCTT_def apply auto
           apply (rule_tac x="\<sigma>'" in bexI, simp_all add: assm2_assms(1))
           apply (rule_tac x="[]" in exI, auto)
           apply (rule_tac x="\<rho>2'" in exI, simp add: in_Q)
           using \<rho>2_assms(1) assm2_assms(5) case_assm case_assm3 ctt_prefix_trans by blast
       qed
     qed
   qed
   then obtain \<rho>2' s2 t2 where \<rho>2_split:
     "\<rho>2'\<in>tocks UNIV"
     "\<rho>2' @ s2 \<in> P"
     "\<rho>2' @ t2 \<in> Q"
     "(\<forall>\<rho>'\<in>tocks UNIV. \<rho>' \<le>\<^sub>C \<rho>2' @ s2 \<longrightarrow> \<rho>' \<le>\<^sub>C \<rho>2')"
     "(\<forall>\<rho>'\<in>tocks UNIV. \<rho>' \<le>\<^sub>C \<rho>2' @ t2 \<longrightarrow> \<rho>' \<le>\<^sub>C \<rho>2')"
     "\<forall>X. s2 = [[X]\<^sub>R] \<longrightarrow> (\<exists>Y. t2 = [[Y]\<^sub>R] \<and> (\<forall>e. (e \<in> X) = (e \<in> Y) \<or> e = Tock))"
     "\<forall>X. t2 = [[X]\<^sub>R] \<longrightarrow> (\<exists>Y. s2 = [[Y]\<^sub>R] \<and> (\<forall>e. (e \<in> X) = (e \<in> Y) \<or> e = Tock))"
     "\<rho>2 = \<rho>2' @ t2 \<or> \<rho>2 = \<rho>2' @ s2"
    unfolding ExtChoiceCTT_def by blast
  then show "\<rho> \<in>  P \<box>\<^sub>C Q"
  proof auto
    assume case_assm: "\<rho>2 = \<rho>2' @ t2"
    have \<rho>_wf: "cttWF \<rho>"
      using CT1_def CT_CT1 CT_wf \<rho>2_assms(2) \<rho>2_split(3) assms(2) case_assm ctt_subset_imp_prefix_subset by blast
    then obtain \<rho>' \<rho>'' where \<rho>'_\<rho>''_assms:
      "\<rho> = \<rho>' @ \<rho>''"
      "\<rho>' \<in> tocks UNIV"
      "\<forall>t\<in>tocks UNIV. t \<le>\<^sub>C \<rho>' @ \<rho>'' \<longrightarrow> t \<le>\<^sub>C \<rho>'"
      using split_tocks_longest by blast
    then have \<rho>'_\<rho>''_ctt_subset: "\<rho>' \<subseteq>\<^sub>C \<rho>2' \<and> \<rho>'' \<subseteq>\<^sub>C t2"
      using CT_wf \<rho>_wf \<rho>2_assms(2) \<rho>2_split(1) \<rho>2_split(3) \<rho>2_split(5) assms(2) case_assm ctt_subset_longest_tocks by blast
    then have \<rho>'_in_P_Q: "\<rho>' \<in> P \<and> \<rho>' \<in> Q"
      by (meson CT_CT1 CT_defs(3) \<rho>2_split(2) \<rho>2_split(3) assms(1) assms(2) ctt_prefix_concat ctt_prefix_subset_ctt_prefix_trans ctt_subset_imp_prefix_subset)
    show "\<rho> \<in> P \<box>\<^sub>C Q"
    proof (cases "\<exists> X. t2 = [[X]\<^sub>R]")
      assume case_assm2: "\<exists> X. t2 = [[X]\<^sub>R]"
      then obtain X where t2_def: "t2 = [[X]\<^sub>R]"
        by auto
      then have "\<exists> Y. Y \<subseteq> X \<and> \<rho>'' = [[Y]\<^sub>R]"
        using \<rho>'_\<rho>''_ctt_subset apply (simp, induct \<rho>'' t2 rule:ctt_subset.induct, simp_all)
        using ctt_subset_same_length by force
      then obtain Y where Y_assms: "Y \<subseteq> X \<and> \<rho>'' = [[Y]\<^sub>R]"
        by auto
      then obtain Z where Z_assms: "s2 = [[Z]\<^sub>R] \<and> (\<forall>e. (e \<in> X) = (e \<in> Z) \<or> e = Tock)"
        using t2_def \<rho>2_split(7) by blast
      then have "{e. e \<in> Y \<and> e \<noteq> Tock} \<subseteq> Z"
        using Y_assms by blast
      then have 1: "\<rho>' @ [[{e. e \<in> Y \<and> e \<noteq> Tock}]\<^sub>R] \<subseteq>\<^sub>C \<rho>2' @ [[Z]\<^sub>R]"
        by (simp add: \<rho>'_\<rho>''_ctt_subset ctt_subset_combine)
      have 2: "\<rho>' @ [[Y]\<^sub>R] \<subseteq>\<^sub>C \<rho>2' @ [[X]\<^sub>R]"
        using Y_assms \<rho>'_\<rho>''_assms(1) \<rho>2_assms(2) case_assm t2_def by blast
      have 3: "\<rho>' @ [[{e. e \<in> Y \<and> e \<noteq> Tock}]\<^sub>R] \<in> P"
        using "1" CT1_def CT_CT1 Z_assms \<rho>2_split(2) assms(1) ctt_subset_imp_prefix_subset by blast
      have 4: "\<rho>' @ [[Y]\<^sub>R] \<in> Q"
        using "2" CT1_def CT_CT1 \<rho>2_split(3) assms(2) ctt_subset_imp_prefix_subset t2_def by blast
      then show "\<rho> \<in> P \<box>\<^sub>C Q"
        unfolding ExtChoiceCTT_def apply auto
        apply (rule_tac x="\<rho>'" in bexI, auto simp add: \<rho>'_\<rho>''_assms)
        apply (rule_tac x="[[{e. e \<in> Y \<and> e \<noteq> Tock}]\<^sub>R]" in exI, auto simp add: 3)
        apply (rule_tac x="[[Y]\<^sub>R]" in exI, auto simp add: 4 Y_assms)
        apply (metis (no_types, lifting) butlast_append butlast_snoc ctt_prefix_concat ctt_prefix_decompose end_refusal_notin_tocks)
        by (simp add: Y_assms \<rho>'_\<rho>''_assms(3))
    next
      assume "\<nexists>X. t2 = [[X]\<^sub>R]"
      then have "\<nexists>X. \<rho>'' = [[X]\<^sub>R]"
        using \<rho>'_\<rho>''_ctt_subset by (auto, cases t2 rule:cttWF.cases, auto)
      then show "\<rho> \<in> P \<box>\<^sub>C Q"
        unfolding ExtChoiceCTT_def apply auto
        apply (rule_tac x="\<rho>'" in bexI, auto simp add: \<rho>'_\<rho>''_assms)
        apply (rule_tac x="[]" in exI, auto simp add: \<rho>'_in_P_Q)
        apply (rule_tac x="\<rho>''" in exI, auto)
        using CT1_def CT_CT1 \<rho>'_\<rho>''_assms(1) \<rho>2_assms(2) \<rho>2_split(3) assms(2) case_assm ctt_subset_imp_prefix_subset apply blast
        using \<rho>'_\<rho>''_assms(3) by blast
    qed
  next
    assume case_assm: "\<rho>2 = \<rho>2' @ s2"
    have \<rho>_wf: "cttWF \<rho>"
      by (metis CT_def ExtChoiceCTT_wf assm1 assm2 assms(1) assms(2) ctt_prefix_subset_cttWF)
    then obtain \<rho>' \<rho>'' where \<rho>'_\<rho>''_assms:
      "\<rho> = \<rho>' @ \<rho>''"
      "\<rho>' \<in> tocks UNIV"
      "\<forall>t\<in>tocks UNIV. t \<le>\<^sub>C \<rho>' @ \<rho>'' \<longrightarrow> t \<le>\<^sub>C \<rho>'"
      using split_tocks_longest by blast
    then have \<rho>'_\<rho>''_ctt_subset: "\<rho>' \<subseteq>\<^sub>C \<rho>2' \<and> \<rho>'' \<subseteq>\<^sub>C s2"
      using CT_wf \<rho>2_assms(2) \<rho>2_split(1) \<rho>2_split(2) \<rho>2_split(4) \<rho>_wf assms(1) case_assm ctt_subset_longest_tocks by blast
    then have \<rho>'_in_P_Q: "\<rho>' \<in> P \<and> \<rho>' \<in> Q"
      by (meson CT_CT1 CT_defs(3) \<rho>2_split(2) \<rho>2_split(3) assms(1) assms(2) ctt_prefix_concat ctt_prefix_subset_ctt_prefix_trans ctt_subset_imp_prefix_subset)
    show "\<rho> \<in> P \<box>\<^sub>C Q"
    proof (cases "\<exists> X. s2 = [[X]\<^sub>R]")
      assume case_assm2: "\<exists> X. s2 = [[X]\<^sub>R]"
      then obtain X where s2_def: "s2 = [[X]\<^sub>R]"
        by auto
      then have "\<exists> Y. Y \<subseteq> X \<and> \<rho>'' = [[Y]\<^sub>R]"
        using \<rho>'_\<rho>''_ctt_subset apply (simp, induct \<rho>'' s2 rule:ctt_subset.induct, simp_all)
        using ctt_subset_same_length by force
      then obtain Y where Y_assms: "Y \<subseteq> X \<and> \<rho>'' = [[Y]\<^sub>R]"
        by auto
      then obtain Z where Z_assms: "t2 = [[Z]\<^sub>R] \<and> (\<forall>e. (e \<in> X) = (e \<in> Z) \<or> e = Tock)"
        using s2_def \<rho>2_split(6) by blast
      then have "{e. e \<in> Y \<and> e \<noteq> Tock} \<subseteq> Z"
        using Y_assms by blast
      then have 1: "\<rho>' @ [[{e. e \<in> Y \<and> e \<noteq> Tock}]\<^sub>R] \<subseteq>\<^sub>C \<rho>2' @ [[Z]\<^sub>R]"
        by (simp add: \<rho>'_\<rho>''_ctt_subset ctt_subset_combine)
      have 2: "\<rho>' @ [[Y]\<^sub>R] \<subseteq>\<^sub>C \<rho>2' @ [[X]\<^sub>R]"
        using Y_assms \<rho>'_\<rho>''_assms(1) \<rho>2_assms(2) case_assm s2_def by blast
      have 3: "\<rho>' @ [[{e. e \<in> Y \<and> e \<noteq> Tock}]\<^sub>R] \<in> Q"
        using "1" CT1_def CT_CT1 Z_assms \<rho>2_split(3) assms(2) ctt_subset_imp_prefix_subset by blast
      have 4: "\<rho>' @ [[Y]\<^sub>R] \<in> P"
        using "2" CT1_def CT_CT1 \<rho>2_split(2) assms(1) ctt_subset_imp_prefix_subset s2_def by blast
      then show "\<rho> \<in> P \<box>\<^sub>C Q"
        unfolding ExtChoiceCTT_def apply auto
        apply (rule_tac x="\<rho>'" in bexI, auto simp add: \<rho>'_\<rho>''_assms)
        apply (rule_tac x="[[Y]\<^sub>R]" in exI, auto simp add: 4 Y_assms)
        apply (rule_tac x="[[{e. e \<in> Y \<and> e \<noteq> Tock}]\<^sub>R]" in exI, auto simp add: 3)
        using Y_assms \<rho>'_\<rho>''_assms(3) apply blast
        by (metis (no_types, lifting) butlast_append butlast_snoc ctt_prefix_concat ctt_prefix_decompose end_refusal_notin_tocks)
    next
      assume "\<nexists>X. s2 = [[X]\<^sub>R]"
      then have "\<nexists>X. \<rho>'' = [[X]\<^sub>R]"
        using \<rho>'_\<rho>''_ctt_subset by (auto, cases s2 rule:cttWF.cases, auto)
      then show "\<rho> \<in> P \<box>\<^sub>C Q"
        unfolding ExtChoiceCTT_def apply auto
        apply (rule_tac x="\<rho>'" in bexI, auto simp add: \<rho>'_\<rho>''_assms)
        apply (rule_tac x="\<rho>''" in exI, auto)
        using CT1_def CT_CT1 \<rho>'_\<rho>''_assms(1) \<rho>2_assms(2) \<rho>2_split(2) assms(1) case_assm ctt_subset_imp_prefix_subset apply blast
        apply (rule_tac x="[]" in exI, auto simp add: \<rho>'_in_P_Q)
        using \<rho>'_\<rho>''_assms(3) by blast
    qed
  qed
qed

lemma CT2_ExtChoice:
  assumes "CT P" "CT Q"
  shows "CT2 (P \<box>\<^sub>C Q)"
  unfolding CT2_def
proof auto
  fix \<rho> :: "'a cttobs list"
  fix X Y :: "'a cttevent set"
  assume assm1: "\<rho> @ [[X]\<^sub>R] \<in> P \<box>\<^sub>C Q"
  assume assm2: "Y \<inter> {e. e \<noteq> Tock \<and> \<rho> @ [[e]\<^sub>E] \<in> P \<box>\<^sub>C Q \<or> e = Tock \<and> \<rho> @ [[X]\<^sub>R, [e]\<^sub>E] \<in> P \<box>\<^sub>C Q} = {}"
  from assm1 have "cttWF \<rho>"
    by (metis CT_def ExtChoiceCTT_wf assms(1) assms(2) ctt_prefix_concat ctt_prefix_imp_prefix_subset ctt_prefix_subset_cttWF)
  then obtain \<rho>' \<rho>'' where \<rho>_split: "\<rho>'\<in>tocks UNIV \<and> \<rho> = \<rho>' @ \<rho>'' \<and> (\<forall>t'\<in>tocks UNIV. t' \<le>\<^sub>C \<rho> \<longrightarrow> t' \<le>\<^sub>C \<rho>')"
    using split_tocks_longest by blast
  have \<rho>'_in_P_Q: "\<rho>' \<in> P \<and> \<rho>' \<in> Q"
    using assm1 unfolding ExtChoiceCTT_def apply auto
    apply (metis CT1_def CT_CT1 \<rho>_split assms(1) ctt_prefix_concat ctt_prefix_imp_prefix_subset)
    apply (metis CT1_def CT_CT1 \<rho>_split append.assoc assms(2) ctt_prefix_concat ctt_prefix_imp_prefix_subset)
    apply (metis CT1_def CT_CT1 \<rho>_split append.assoc assms(1) ctt_prefix_concat ctt_prefix_imp_prefix_subset)
    by (metis CT1_def CT_CT1 \<rho>_split assms(2) ctt_prefix_concat ctt_prefix_imp_prefix_subset)
  have set1: "{e. e \<noteq> Tock \<and> \<rho> @ [[e]\<^sub>E] \<in> P \<box>\<^sub>C Q} = {e. e \<noteq> Tock \<and> \<rho> @ [[e]\<^sub>E] \<in> P} \<union> {e. e \<noteq> Tock \<and> \<rho> @ [[e]\<^sub>E] \<in> Q}"
  proof auto
    fix x :: "'a cttevent"
    assume "\<rho> @ [[x]\<^sub>E] \<in> P \<box>\<^sub>C Q"
    then have "\<rho> @ [[x]\<^sub>E] \<in> P \<or> \<rho> @ [[x]\<^sub>E] \<in> Q"
      unfolding ExtChoiceCTT_def by auto
    then show "\<rho> @ [[x]\<^sub>E] \<notin> Q \<Longrightarrow> \<rho> @ [[x]\<^sub>E] \<in> P"
      by auto
  next
    fix x :: "'a cttevent"
    assume "x \<noteq> Tock" "\<rho> @ [[x]\<^sub>E] \<in> P"
    then show "\<rho> @ [[x]\<^sub>E] \<in> P \<box>\<^sub>C Q"
      unfolding ExtChoiceCTT_def apply auto
      apply (rule_tac x="\<rho>'" in bexI, simp_all add: \<rho>_split)
      apply (rule_tac x="\<rho>'' @ [[x]\<^sub>E]" in exI, simp_all)
      apply (rule_tac x="[]" in exI, simp add: \<rho>'_in_P_Q)
      apply (auto, case_tac "\<rho>''' \<le>\<^sub>C \<rho>' @ \<rho>''")
      using \<rho>_split apply blast
      by (metis append.assoc append_Cons append_Nil ctt_prefix_notfront_is_whole cttevent.exhaust end_event_notin_tocks mid_tick_notin_tocks)
  next
    fix x :: "'a cttevent"
    assume "x \<noteq> Tock" "\<rho> @ [[x]\<^sub>E] \<in> Q"
    then show "\<rho> @ [[x]\<^sub>E] \<in> P \<box>\<^sub>C Q"
      unfolding ExtChoiceCTT_def apply auto
      apply (rule_tac x="\<rho>'" in bexI, simp_all add: \<rho>_split)
      apply (rule_tac x="[]" in exI, simp add: \<rho>'_in_P_Q)
      apply (auto, case_tac "\<rho>''' \<le>\<^sub>C \<rho>' @ \<rho>''")
      using \<rho>_split apply blast
      by (metis append.assoc append_Cons append_Nil ctt_prefix_notfront_is_whole cttevent.exhaust end_event_notin_tocks mid_tick_notin_tocks)
  qed
  have set2: "{e. e = Tock \<and> \<rho>'' = [] \<and> \<rho> @ [[X]\<^sub>R, [e]\<^sub>E] \<in> P \<box>\<^sub>C Q} = 
    {e. e = Tock \<and> \<rho>'' = [] \<and> \<rho> @ [[X]\<^sub>R, [e]\<^sub>E] \<in> P} \<inter> {e. e = Tock \<and> \<rho>'' = [] \<and> \<rho> @ [[X]\<^sub>R, [e]\<^sub>E] \<in> Q}"
  proof auto
    assume case_assms: "\<rho> @ [[X]\<^sub>R, [Tock]\<^sub>E] \<in> P \<box>\<^sub>C Q" "\<rho>'' = []"
    then have "\<rho>' @ [[X]\<^sub>R, [Tock]\<^sub>E] \<in> P \<box>\<^sub>C Q"
      by (simp add: \<rho>_split)
    then obtain r s t where rst_assms: 
      "r \<in> tocks UNIV"
      "r @ s \<in> P"
      "r @ t \<in> Q"
      "\<forall>x\<in>tocks UNIV. x \<le>\<^sub>C r @ s \<longrightarrow> x \<le>\<^sub>C r"
      "\<forall>x\<in>tocks UNIV. x \<le>\<^sub>C r @ t \<longrightarrow> x \<le>\<^sub>C r"
      "(\<rho>' @ [[X]\<^sub>R, [Tock]\<^sub>E] = r @ s \<or> \<rho>' @ [[X]\<^sub>R, [Tock]\<^sub>E] = r @ t)"
      unfolding ExtChoiceCTT_def by auto
    have in_tocks: "\<rho>' @ [[X]\<^sub>R, [Tock]\<^sub>E] \<in> tocks UNIV"
      by (simp add: \<rho>_split tocks.empty_in_tocks tocks.tock_insert_in_tocks tocks_append_tocks)
    then have r_def: "r = \<rho>' @ [[X]\<^sub>R, [Tock]\<^sub>E]"
      using ctt_prefix_refl rst_assms(4) rst_assms(5) rst_assms(6) self_extension_ctt_prefix by fastforce
    then have "r \<in> P \<and> r \<in> Q"
      by (smt CT1_def CT_CT1 rst_assms assms(1) assms(2) ctt_prefix_concat ctt_prefix_imp_prefix_subset in_tocks rst_assms(4))
    then show "\<rho> @ [[X]\<^sub>R, [Tock]\<^sub>E] \<in> P"
      by (simp add: r_def \<rho>_split case_assms(2))
  next
    assume case_assms: "\<rho> @ [[X]\<^sub>R, [Tock]\<^sub>E] \<in> P \<box>\<^sub>C Q" "\<rho>'' = []"
    then have "\<rho>' @ [[X]\<^sub>R, [Tock]\<^sub>E] \<in> P \<box>\<^sub>C Q"
      by (simp add: \<rho>_split)
    then obtain r s t where rst_assms: 
      "r \<in> tocks UNIV"
      "r @ s \<in> P"
      "r @ t \<in> Q"
      "\<forall>x\<in>tocks UNIV. x \<le>\<^sub>C r @ s \<longrightarrow> x \<le>\<^sub>C r"
      "\<forall>x\<in>tocks UNIV. x \<le>\<^sub>C r @ t \<longrightarrow> x \<le>\<^sub>C r"
      "(\<rho>' @ [[X]\<^sub>R, [Tock]\<^sub>E] = r @ s \<or> \<rho>' @ [[X]\<^sub>R, [Tock]\<^sub>E] = r @ t)"
      unfolding ExtChoiceCTT_def by auto
    have in_tocks: "\<rho>' @ [[X]\<^sub>R, [Tock]\<^sub>E] \<in> tocks UNIV"
      by (simp add: \<rho>_split tocks.empty_in_tocks tocks.tock_insert_in_tocks tocks_append_tocks)
    then have r_def: "r = \<rho>' @ [[X]\<^sub>R, [Tock]\<^sub>E]"
      using ctt_prefix_refl rst_assms(4) rst_assms(5) rst_assms(6) self_extension_ctt_prefix by fastforce
    then have "r \<in> P \<and> r \<in> Q"
      by (smt CT1_def CT_CT1 rst_assms assms(1) assms(2) ctt_prefix_concat ctt_prefix_imp_prefix_subset in_tocks rst_assms(4))
    then show "\<rho> @ [[X]\<^sub>R, [Tock]\<^sub>E] \<in> Q"
      by (simp add: r_def \<rho>_split case_assms(2))
  next
    assume case_assms: "\<rho> @ [[X]\<^sub>R, [Tock]\<^sub>E] \<in> P" "\<rho>'' = []" "\<rho> @ [[X]\<^sub>R, [Tock]\<^sub>E] \<in> Q"
    then have "\<rho>' @ [[X]\<^sub>R, [Tock]\<^sub>E] \<in> P \<and> \<rho>' @ [[X]\<^sub>R, [Tock]\<^sub>E] \<in> Q"
      by (simp add: \<rho>_split)
    also have "\<rho>' @ [[X]\<^sub>R, [Tock]\<^sub>E] \<in> tocks UNIV"
      by (simp add: \<rho>_split tocks.empty_in_tocks tocks.tock_insert_in_tocks tocks_append_tocks)
    then show "\<rho> @ [[X]\<^sub>R, [Tock]\<^sub>E] \<in> P \<box>\<^sub>C Q"
      unfolding ExtChoiceCTT_def apply auto
      apply (rule_tac x="\<rho>' @ [[X]\<^sub>R, [Tock]\<^sub>E]" in bexI, simp_all)
      apply (rule_tac x="[]" in exI, simp_all add: calculation)
      apply (rule_tac x="[]" in exI, simp_all add: calculation)
      by (simp add: \<rho>_split case_assms(2))
  qed
  have set3: "{e. e = Tock \<and> \<rho>'' \<noteq> [] \<and> \<rho> @ [[X]\<^sub>R, [e]\<^sub>E] \<in> P \<box>\<^sub>C Q} = 
    {e. e = Tock \<and> \<rho>'' \<noteq> [] \<and> \<rho> @ [[X]\<^sub>R, [e]\<^sub>E] \<in> P} \<union> {e. e = Tock \<and> \<rho>'' \<noteq> [] \<and> \<rho> @ [[X]\<^sub>R, [e]\<^sub>E] \<in> Q}"
  proof auto
    assume "\<rho>'' \<noteq> []" "\<rho> @ [[X]\<^sub>R, [Tock]\<^sub>E] \<in> P \<box>\<^sub>C Q"
    then show "\<rho> @ [[X]\<^sub>R, [Tock]\<^sub>E] \<notin> Q \<Longrightarrow> \<rho> @ [[X]\<^sub>R, [Tock]\<^sub>E] \<in> P"
      unfolding ExtChoiceCTT_def by auto
  next
    assume \<rho>''_nonempty: "\<rho>'' \<noteq> []"
    assume in_P: "\<rho> @ [[X]\<^sub>R, [Tock]\<^sub>E] \<in> P"
    have full_notin_tocks: "\<rho>' @ \<rho>'' @ [[X]\<^sub>R, [Tock]\<^sub>E] \<notin> tocks UNIV"
        by (metis \<rho>''_nonempty \<rho>_split append.assoc ctt_prefix_refl nontocks_append_tocks self_extension_ctt_prefix tocks.empty_in_tocks tocks.tock_insert_in_tocks top_greatest)
    have "\<forall>x\<in>tocks UNIV. x \<le>\<^sub>C \<rho> @ [[X]\<^sub>R, [Tock]\<^sub>E] \<longrightarrow> x \<le>\<^sub>C \<rho>'"
    proof (auto simp add: \<rho>_split)
      fix x :: "'a cttobs list"
      assume x_in_tocks: "x \<in> tocks UNIV"
      assume "x \<le>\<^sub>C \<rho>' @ \<rho>'' @ [[X]\<^sub>R, [Tock]\<^sub>E]"
      also have "\<And> y. x \<le>\<^sub>C y @ [[X]\<^sub>R, [Tock]\<^sub>E] \<Longrightarrow> x \<le>\<^sub>C y \<or> x = y @ [[X]\<^sub>R] \<or> x = y @ [[X]\<^sub>R, [Tock]\<^sub>E]"
      proof -
        fix y
        show "x \<le>\<^sub>C y @ [[X]\<^sub>R, [Tock]\<^sub>E] \<Longrightarrow> x \<le>\<^sub>C y \<or> x = y @ [[X]\<^sub>R] \<or> x = y @ [[X]\<^sub>R, [Tock]\<^sub>E]"
          using ctt_prefix.elims(2) ctt_prefix_antisym by (induct x y rule:ctt_prefix.induct, auto, fastforce)
      qed
      then have "x \<le>\<^sub>C \<rho>' @ \<rho>'' \<or> x = \<rho>' @ \<rho>'' @ [[X]\<^sub>R] \<or> x = \<rho>' @ \<rho>'' @ [[X]\<^sub>R, [Tock]\<^sub>E]"
        using calculation by force
      then show "x \<le>\<^sub>C \<rho>'"
        apply auto
        apply (simp add: \<rho>_split x_in_tocks)
        apply (metis append_assoc end_refusal_notin_tocks x_in_tocks)
        using full_notin_tocks x_in_tocks by blast
    qed
    then show "\<rho> @ [[X]\<^sub>R, [Tock]\<^sub>E] \<in> P \<box>\<^sub>C Q"
      unfolding ExtChoiceCTT_def apply auto
      apply (rule_tac x="\<rho>'" in bexI, auto simp add: \<rho>_split)
      apply (rule_tac x="\<rho>'' @ [[X]\<^sub>R, [Tock]\<^sub>E]" in exI, insert \<rho>_split in_P, auto)
      apply (rule_tac x="[]" in exI, auto simp add: \<rho>'_in_P_Q)
      done
  next
    assume \<rho>''_nonempty: "\<rho>'' \<noteq> []"
    assume in_Q: "\<rho> @ [[X]\<^sub>R, [Tock]\<^sub>E] \<in> Q"
    have full_notin_tocks: "\<rho>' @ \<rho>'' @ [[X]\<^sub>R, [Tock]\<^sub>E] \<notin> tocks UNIV"
        by (metis \<rho>''_nonempty \<rho>_split append.assoc ctt_prefix_refl nontocks_append_tocks self_extension_ctt_prefix tocks.empty_in_tocks tocks.tock_insert_in_tocks top_greatest)
    have "\<forall>x\<in>tocks UNIV. x \<le>\<^sub>C \<rho> @ [[X]\<^sub>R, [Tock]\<^sub>E] \<longrightarrow> x \<le>\<^sub>C \<rho>'"
    proof (auto simp add: \<rho>_split)
      fix x :: "'a cttobs list"
      assume x_in_tocks: "x \<in> tocks UNIV"
      assume "x \<le>\<^sub>C \<rho>' @ \<rho>'' @ [[X]\<^sub>R, [Tock]\<^sub>E]"
      also have "\<And> y. x \<le>\<^sub>C y @ [[X]\<^sub>R, [Tock]\<^sub>E] \<Longrightarrow> x \<le>\<^sub>C y \<or> x = y @ [[X]\<^sub>R] \<or> x = y @ [[X]\<^sub>R, [Tock]\<^sub>E]"
      proof -
        fix y
        show "x \<le>\<^sub>C y @ [[X]\<^sub>R, [Tock]\<^sub>E] \<Longrightarrow> x \<le>\<^sub>C y \<or> x = y @ [[X]\<^sub>R] \<or> x = y @ [[X]\<^sub>R, [Tock]\<^sub>E]"
          using ctt_prefix.elims(2) ctt_prefix_antisym by (induct x y rule:ctt_prefix.induct, auto, fastforce)
      qed
      then have "x \<le>\<^sub>C \<rho>' @ \<rho>'' \<or> x = \<rho>' @ \<rho>'' @ [[X]\<^sub>R] \<or> x = \<rho>' @ \<rho>'' @ [[X]\<^sub>R, [Tock]\<^sub>E]"
        using calculation by force
      then show "x \<le>\<^sub>C \<rho>'"
        apply auto
        apply (simp add: \<rho>_split x_in_tocks)
        apply (metis append_assoc end_refusal_notin_tocks x_in_tocks)
        using full_notin_tocks x_in_tocks by blast
    qed
    then show "\<rho> @ [[X]\<^sub>R, [Tock]\<^sub>E] \<in> P \<box>\<^sub>C Q"
      unfolding ExtChoiceCTT_def apply auto
      apply (rule_tac x="\<rho>'" in bexI, auto simp add: \<rho>_split)
      apply (rule_tac x="[]" in exI, auto simp add: \<rho>'_in_P_Q)
      apply (insert \<rho>_split in_Q, auto)
      done
  qed
  thm set1 set2 set3
  have in_P_or_Q: "\<rho> @ [[X]\<^sub>R] \<in> P \<or> \<rho> @ [[X]\<^sub>R] \<in> Q"
    using assm1 unfolding ExtChoiceCTT_def by auto
  show "\<rho> @ [[X \<union> Y]\<^sub>R] \<in> P \<box>\<^sub>C Q"
  proof (cases "\<rho>'' \<noteq> []", auto)
    assume case_assm: "\<rho>'' \<noteq> []"
    have "{e. e \<noteq> Tock \<and> \<rho> @ [[e]\<^sub>E] \<in> P \<box>\<^sub>C Q \<or> e = Tock \<and> \<rho> @ [[X]\<^sub>R, [e]\<^sub>E] \<in> P \<box>\<^sub>C Q}
      = {e. e \<noteq> Tock \<and> \<rho> @ [[e]\<^sub>E] \<in> P \<or> e = Tock \<and> \<rho> @ [[X]\<^sub>R, [e]\<^sub>E] \<in> P} \<union> {e. e \<noteq> Tock \<and> \<rho> @ [[e]\<^sub>E] \<in> Q \<or> e = Tock \<and> \<rho> @ [[X]\<^sub>R, [e]\<^sub>E] \<in> Q}"
      (is "?lhs = ?rhs")
    proof -
      have "?lhs = {e. e \<noteq> Tock \<and> \<rho> @ [[e]\<^sub>E] \<in> P \<box>\<^sub>C Q} \<union> {e. e = Tock \<and> \<rho> @ [[X]\<^sub>R, [e]\<^sub>E] \<in> P \<box>\<^sub>C Q}"
        by auto
      also have "... = {e. e \<noteq> Tock \<and> \<rho> @ [[e]\<^sub>E] \<in> P} \<union> {e. e \<noteq> Tock \<and> \<rho> @ [[e]\<^sub>E] \<in> Q} \<union> {e. e = Tock \<and> \<rho> @ [[X]\<^sub>R, [e]\<^sub>E] \<in> P \<box>\<^sub>C Q}"
        using set1 by auto
      also have "... = {e. e \<noteq> Tock \<and> \<rho> @ [[e]\<^sub>E] \<in> P} \<union> {e. e \<noteq> Tock \<and> \<rho> @ [[e]\<^sub>E] \<in> Q} \<union> {e. e = Tock \<and> \<rho> @ [[X]\<^sub>R, [e]\<^sub>E] \<in> P} \<union> {e. e = Tock \<and> \<rho> @ [[X]\<^sub>R, [e]\<^sub>E] \<in> Q}"
        using set3 case_assm by auto
      also have "... = ?rhs"
        by auto
      then show "?lhs = ?rhs"
        using calculation by auto
    qed
    then have 
      "(Y \<inter> {e. e \<noteq> Tock \<and> \<rho> @ [[e]\<^sub>E] \<in> P \<or> e = Tock \<and> \<rho> @ [[X]\<^sub>R, [e]\<^sub>E] \<in> P})
        \<union> (Y \<inter> {e. e \<noteq> Tock \<and> \<rho> @ [[e]\<^sub>E] \<in> Q \<or> e = Tock \<and> \<rho> @ [[X]\<^sub>R, [e]\<^sub>E] \<in> Q}) = {}"
      using assm2 inf_sup_distrib1 by auto
    then have "Y \<inter> {e. e \<noteq> Tock \<and> \<rho> @ [[e]\<^sub>E] \<in> P \<or> e = Tock \<and> \<rho> @ [[X]\<^sub>R, [e]\<^sub>E] \<in> P} = {}
      \<and> Y \<inter> {e. e \<noteq> Tock \<and> \<rho> @ [[e]\<^sub>E] \<in> Q \<or> e = Tock \<and> \<rho> @ [[X]\<^sub>R, [e]\<^sub>E] \<in> Q} = {}"
      by auto
    then have "\<rho> @ [[X \<union> Y]\<^sub>R] \<in> P \<or> \<rho> @ [[X \<union> Y]\<^sub>R] \<in> Q"
      using CT2_def CT_def assms(1) assms(2) in_P_or_Q by auto
    then show "\<rho> @ [[X \<union> Y]\<^sub>R] \<in> P \<box>\<^sub>C Q"
      unfolding ExtChoiceCTT_def apply auto
      apply (rule_tac x="\<rho>'" in bexI, auto simp add: \<rho>_split)
      apply (rule_tac x="\<rho>'' @ [[X \<union> Y]\<^sub>R]" in exI, auto)
      apply (rule_tac x="[]" in exI, auto simp add: \<rho>_split \<rho>'_in_P_Q case_assm)
      apply (metis \<rho>_split append.assoc ctt_prefix_notfront_is_whole end_refusal_notin_tocks)
      apply (rule_tac x="\<rho>'" in bexI, auto simp add: \<rho>_split)
      apply (rule_tac x="[]" in exI, auto simp add: \<rho>_split \<rho>'_in_P_Q case_assm)
      apply (metis \<rho>_split append.assoc ctt_prefix_notfront_is_whole end_refusal_notin_tocks)
      done
  next
    assume case_assm: "\<rho>'' = []"
    have "\<rho> @ [[{e. e \<in> X \<and> e \<noteq> Tock}]\<^sub>R] \<lesssim>\<^sub>C \<rho> @ [[X]\<^sub>R]"
      by (induct \<rho>, auto, case_tac a, auto)
    then have "\<rho> @ [[{e. e \<in> X \<and> e \<noteq> Tock}]\<^sub>R] \<in> P \<box>\<^sub>C Q"
      using CT1_ExtChoice CT1_def assm1 assms(1) assms(2) by blast
    then have "\<rho>' @ [[{e. e \<in> X \<and> e \<noteq> Tock}]\<^sub>R] \<in> P \<box>\<^sub>C Q"
      by (simp add: \<rho>_split case_assm)
    then have in_P_and_Q: "\<rho>' @ [[{e. e \<in> X \<and> e \<noteq> Tock}]\<^sub>R] \<in> P \<and> \<rho>' @ [[{e. e \<in> X \<and> e \<noteq> Tock}]\<^sub>R] \<in> Q"
      unfolding ExtChoiceCTT_def
    proof auto
      fix \<rho> \<sigma> \<tau> :: "'a cttobs list"
      assume case_assm1: "\<rho> \<in> tocks UNIV"
      assume case_assm2: "\<forall>\<rho>'\<in>tocks UNIV. \<rho>' \<le>\<^sub>C \<rho> @ \<sigma> \<longrightarrow> \<rho>' \<le>\<^sub>C \<rho>"
      assume case_assm3: "\<rho>' @ [[{e \<in> X. e \<noteq> Tock}]\<^sub>R] = \<rho> @ \<sigma>"
      assume case_assm4: "\<forall>X. \<sigma> = [[X]\<^sub>R] \<longrightarrow> (\<exists>Y. \<tau> = [[Y]\<^sub>R] \<and> (\<forall>e. (e \<in> X) = (e \<in> Y) \<or> e = Tock))"
      assume case_assm5: "\<rho> @ \<tau> \<in> Q"
      have \<rho>_def: "\<rho> = \<rho>'"
        by (metis (no_types, lifting) \<rho>_split butlast_append butlast_snoc case_assm1 case_assm2 case_assm3 ctt_prefix_antisym ctt_prefix_concat end_refusal_notin_tocks)
      then have \<sigma>_def: "\<sigma> = [[{e \<in> X. e \<noteq> Tock}]\<^sub>R]"
        using case_assm3 by blast
      obtain Y where Y_assms: "\<tau> = [[Y]\<^sub>R]" "\<forall>e. (e \<in> X) = (e \<in> Y) \<or> e = Tock"
        using case_assm4 by (erule_tac x="{e. e \<in> X \<and> e \<noteq> Tock}" in allE, simp add: \<sigma>_def, auto)
      then have "\<rho>' @ [[{e \<in> X. e \<noteq> Tock}]\<^sub>R] \<lesssim>\<^sub>C \<rho>' @ [[Y]\<^sub>R]"
        by (induct \<rho>', auto, case_tac a, auto)
      then have "\<rho>' @ [[{e \<in> X. e \<noteq> Tock}]\<^sub>R] \<in> Q"
        using CT1_def CT_CT1 Y_assms(1) \<rho>_def assms(2) case_assm5 by blast
      then show "\<rho> @ \<sigma> \<in> Q"
        by (simp add: case_assm3)
    next
      fix \<rho> \<sigma> \<tau> :: "'a cttobs list"
      assume case_assm1: "\<rho> \<in> tocks UNIV"
      assume case_assm2: "\<forall>\<rho>'\<in>tocks UNIV. \<rho>' \<le>\<^sub>C \<rho> @ \<tau> \<longrightarrow> \<rho>' \<le>\<^sub>C \<rho>"
      assume case_assm3: "\<rho>' @ [[{e \<in> X. e \<noteq> Tock}]\<^sub>R] = \<rho> @ \<tau>"
      assume case_assm4: "\<forall>X. \<tau> = [[X]\<^sub>R] \<longrightarrow> (\<exists>Y. \<sigma> = [[Y]\<^sub>R] \<and> (\<forall>e. (e \<in> X) = (e \<in> Y) \<or> e = Tock))"
      assume case_assm5: "\<rho> @ \<sigma> \<in> P"
      have \<rho>_def: "\<rho> = \<rho>'"
        by (metis (no_types, lifting) \<rho>_split butlast_append butlast_snoc case_assm1 case_assm2 case_assm3 ctt_prefix_antisym ctt_prefix_concat end_refusal_notin_tocks)
      then have \<sigma>_def: "\<tau> = [[{e \<in> X. e \<noteq> Tock}]\<^sub>R]"
        using case_assm3 by blast
      obtain Y where Y_assms: "\<sigma> = [[Y]\<^sub>R]" "\<forall>e. (e \<in> X) = (e \<in> Y) \<or> e = Tock"
        using case_assm4 by (erule_tac x="{e. e \<in> X \<and> e \<noteq> Tock}" in allE, simp add: \<sigma>_def, auto)
      then have "\<rho>' @ [[{e \<in> X. e \<noteq> Tock}]\<^sub>R] \<lesssim>\<^sub>C \<rho>' @ [[Y]\<^sub>R]"
        by (induct \<rho>', auto, case_tac a, auto)
      then have "\<rho>' @ [[{e \<in> X. e \<noteq> Tock}]\<^sub>R] \<in> P"
        using CT1_def CT_CT1 Y_assms(1) \<rho>_def assms(1) case_assm5 by blast
      then show "\<rho> @ \<tau> \<in> P"
        by (simp add: case_assm3)
    qed
    have notocks_assm2: "{e. e \<in> Y \<and> e \<noteq> Tock} \<inter> {e. e \<noteq> Tock \<and> \<rho> @ [[e]\<^sub>E] \<in> P \<or> e = Tock \<and> \<rho> @ [[{e. e \<in> X \<and> e \<noteq> Tock}]\<^sub>R, [e]\<^sub>E] \<in> P} = {} 
        \<and> {e. e \<in> Y \<and> e \<noteq> Tock} \<inter> {e. e \<noteq> Tock \<and> \<rho> @ [[e]\<^sub>E] \<in> Q \<or> e = Tock \<and> \<rho> @ [[{e. e \<in> X \<and> e \<noteq> Tock}]\<^sub>R, [e]\<^sub>E] \<in> Q} = {}"
      using set1 assm2 by blast
    have CT2_P_Q: "CT2 P \<and> CT2 Q"
      by (simp add: CT_CT2 assms(1) assms(2))
    then have notock_X_Y_in_P_Q: "\<rho> @ [[{e. e \<in> X \<union> Y \<and> e \<noteq> Tock}]\<^sub>R] \<in> P \<and> \<rho> @ [[{e. e \<in> X \<union> Y \<and> e \<noteq> Tock}]\<^sub>R] \<in> Q"
      unfolding CT2_def
    proof auto
      assume "\<forall>\<rho> X Y. \<rho> @ [[X]\<^sub>R] \<in> P \<and> 
          Y \<inter> {e. e \<noteq> Tock \<and> \<rho> @ [[e]\<^sub>E] \<in> P \<or> e = Tock \<and> \<rho> @ [[X]\<^sub>R, [e]\<^sub>E] \<in> P} = {} \<longrightarrow>
            \<rho> @ [[X \<union> Y]\<^sub>R] \<in> P"
      then have "\<rho> @ [[{e. e \<in> X \<and> e \<noteq> Tock} \<union> {e. e \<in> Y \<and> e \<noteq> Tock}]\<^sub>R] \<in> P"
        using in_P_and_Q notocks_assm2 case_assm \<rho>_split by auto
      also have "\<rho> @ [[{e. e \<in> X \<and> e \<noteq> Tock} \<union> {e. e \<in> Y \<and> e \<noteq> Tock}]\<^sub>R] = \<rho> @ [[{e. (e \<in> X \<or> e \<in> Y) \<and> e \<noteq> Tock}]\<^sub>R]"
        by auto
      then show "\<rho> @ [[{e. (e \<in> X \<or> e \<in> Y) \<and> e \<noteq> Tock}]\<^sub>R] \<in> P"
        using calculation by auto
    next
      assume "\<forall>\<rho> X Y. \<rho> @ [[X]\<^sub>R] \<in> Q \<and> 
          Y \<inter> {e. e \<noteq> Tock \<and> \<rho> @ [[e]\<^sub>E] \<in> Q \<or> e = Tock \<and> \<rho> @ [[X]\<^sub>R, [e]\<^sub>E] \<in> Q} = {} \<longrightarrow>
            \<rho> @ [[X \<union> Y]\<^sub>R] \<in> Q"
      then have "\<rho> @ [[{e. e \<in> X \<and> e \<noteq> Tock} \<union> {e. e \<in> Y \<and> e \<noteq> Tock}]\<^sub>R] \<in> Q"
        using in_P_and_Q notocks_assm2 case_assm \<rho>_split by auto
      also have "\<rho> @ [[{e. e \<in> X \<and> e \<noteq> Tock} \<union> {e. e \<in> Y \<and> e \<noteq> Tock}]\<^sub>R] = \<rho> @ [[{e. (e \<in> X \<or> e \<in> Y) \<and> e \<noteq> Tock}]\<^sub>R]"
        by auto
      then show "\<rho> @ [[{e. (e \<in> X \<or> e \<in> Y) \<and> e \<noteq> Tock}]\<^sub>R] \<in> Q"
        using calculation by auto
    qed
    have in_P_or_Q: "\<rho> @ [[X]\<^sub>R] \<in> P \<or> \<rho> @ [[X]\<^sub>R] \<in> Q"
      using assm1 unfolding ExtChoiceCTT_def by auto
    show "\<rho> @ [[X \<union> Y]\<^sub>R] \<in> P \<box>\<^sub>C Q"
    proof (cases "Tock \<in> Y")
      assume case_assm2: "Tock \<in> Y"
      have assm2_nontock_P: "{e. e \<in> Y \<and> e \<noteq> Tock} \<inter> {e. e \<noteq> Tock \<and> \<rho> @ [[e]\<^sub>E] \<in> P} = {}"
        using assm2 set1 by auto
      have assm2_nontock_Q: "{e. e \<in> Y \<and> e \<noteq> Tock} \<inter> {e. e \<noteq> Tock \<and> \<rho> @ [[e]\<^sub>E] \<in> Q} = {}"
        using assm2 set1 by auto
      have "{e. e \<in> Y \<and> e = Tock} \<inter> {e. e = Tock \<and> \<rho> @ [[X]\<^sub>R, [e]\<^sub>E] \<in> P \<box>\<^sub>C Q} = {}"
        using assm2 by auto
      then have "Tock \<notin> {e. e = Tock \<and> \<rho> @ [[X]\<^sub>R, [e]\<^sub>E] \<in> P \<box>\<^sub>C Q}"
        using case_assm2 by auto
      then have "Tock \<notin> {e. e = Tock \<and> \<rho> @ [[X]\<^sub>R, [e]\<^sub>E] \<in> P} \<inter> {e. e = Tock \<and> \<rho> @ [[X]\<^sub>R, [e]\<^sub>E] \<in> Q}"
        using set2 case_assm by auto
      then have "({e. e \<in> Y \<and> e = Tock} \<inter> {e. e = Tock \<and> \<rho> @ [[X]\<^sub>R, [e]\<^sub>E] \<in> P} = {} \<and> {e. e \<in> Y \<and> e = Tock} \<inter> {e. e = Tock \<and> \<rho> @ [[X]\<^sub>R, [e]\<^sub>E] \<in> Q} = {})
        \<or> (\<rho> @ [[X]\<^sub>R, [Tock]\<^sub>E] \<in> P \<and> {e. e \<in> Y \<and> e = Tock} \<inter> {e. e = Tock \<and> \<rho> @ [[X]\<^sub>R, [e]\<^sub>E] \<in> Q} = {})
        \<or> ({e. e \<in> Y \<and> e = Tock} \<inter> {e. e = Tock \<and> \<rho> @ [[X]\<^sub>R, [e]\<^sub>E] \<in> P} = {} \<and> \<rho> @ [[X]\<^sub>R, [Tock]\<^sub>E] \<in> Q)"
        by auto
      then have "(Y \<inter> {e. e \<noteq> Tock \<and> \<rho> @ [[e]\<^sub>E] \<in> P \<or> e = Tock \<and> \<rho> @ [[X]\<^sub>R, [e]\<^sub>E] \<in> P} = {} \<and> Y \<inter> {e. e \<noteq> Tock \<and> \<rho> @ [[e]\<^sub>E] \<in> Q \<or> e = Tock \<and> \<rho> @ [[X]\<^sub>R, [e]\<^sub>E] \<in> Q} = {})
        \<or> (\<rho> @ [[X]\<^sub>R, [Tock]\<^sub>E] \<in> P \<and> Y \<inter> {e. e \<noteq> Tock \<and> \<rho> @ [[e]\<^sub>E] \<in> Q \<or> e = Tock \<and> \<rho> @ [[X]\<^sub>R, [e]\<^sub>E] \<in> Q} = {})
        \<or> (Y \<inter> {e. e \<noteq> Tock \<and> \<rho> @ [[e]\<^sub>E] \<in> P \<or> e = Tock \<and> \<rho> @ [[X]\<^sub>R, [e]\<^sub>E] \<in> P} = {} \<and> \<rho> @ [[X]\<^sub>R, [Tock]\<^sub>E] \<in> Q)"
        using assm2_nontock_P assm2_nontock_Q by (safe, blast+)
      then show "\<rho> @ [[X \<union> Y]\<^sub>R] \<in> P \<box>\<^sub>C Q"
      proof safe
        assume case_assm3: "Y \<inter> {e. e \<noteq> Tock \<and> \<rho> @ [[e]\<^sub>E] \<in> P \<or> e = Tock \<and> \<rho> @ [[X]\<^sub>R, [e]\<^sub>E] \<in> P} = {}"
        assume case_assm4: "Y \<inter> {e. e \<noteq> Tock \<and> \<rho> @ [[e]\<^sub>E] \<in> Q \<or> e = Tock \<and> \<rho> @ [[X]\<^sub>R, [e]\<^sub>E] \<in> Q} = {}"
        show "\<rho> @ [[X \<union> Y]\<^sub>R] \<in> P \<box>\<^sub>C Q"
          using in_P_or_Q
        proof auto
          assume case_assm5: "\<rho> @ [[X]\<^sub>R] \<in> P"
          then have "\<rho> @ [[X \<union> Y]\<^sub>R] \<in> P"
            using CT2_P_Q case_assm3 unfolding CT2_def by auto
          also have "\<rho> @ [[{e \<in> X \<union> Y. e \<noteq> Tock}]\<^sub>R] \<in> Q"
            using notock_X_Y_in_P_Q by auto
          then show "\<rho> @ [[X \<union> Y]\<^sub>R] \<in> P \<box>\<^sub>C Q"
            unfolding ExtChoiceCTT_def using calculation apply auto
            apply (rule_tac x="\<rho>'" in bexI, simp_all add: \<rho>_split case_assm)
            apply (rule_tac x="[[X \<union> Y]\<^sub>R]" in exI, simp_all)
            apply (rule_tac x="[[{e \<in> X \<union> Y. e \<noteq> Tock}]\<^sub>R]" in exI, auto)
            using ctt_prefix_notfront_is_whole end_refusal_notin_tocks by blast+
        next
          assume case_assm5: "\<rho> @ [[X]\<^sub>R] \<in> Q"
          then have "\<rho> @ [[X \<union> Y]\<^sub>R] \<in> Q"
            using CT2_P_Q case_assm4 unfolding CT2_def by auto
          also have "\<rho> @ [[{e \<in> X \<union> Y. e \<noteq> Tock}]\<^sub>R] \<in> P"
            using notock_X_Y_in_P_Q by auto
          then show "\<rho> @ [[X \<union> Y]\<^sub>R] \<in> P \<box>\<^sub>C Q"
            unfolding ExtChoiceCTT_def using calculation apply auto
            apply (rule_tac x="\<rho>'" in bexI, simp_all add: \<rho>_split case_assm)
            apply (rule_tac x="[[{e \<in> X \<union> Y. e \<noteq> Tock}]\<^sub>R]" in exI, auto)
            apply (rule_tac x="[[X \<union> Y]\<^sub>R]" in exI, simp_all)
            using ctt_prefix_notfront_is_whole end_refusal_notin_tocks by blast+
        qed
      next
        assume case_assm3: "\<rho> @ [[X]\<^sub>R, [Tock]\<^sub>E] \<in> P"
        assume case_assm4: "Y \<inter> {e. e \<noteq> Tock \<and> \<rho> @ [[e]\<^sub>E] \<in> Q \<or> e = Tock \<and> \<rho> @ [[X]\<^sub>R, [e]\<^sub>E] \<in> Q} = {}"
        have CT1_P: "CT1 P"
          by (simp add: CT_CT1 assms(1))
        have "\<rho> @ [[X]\<^sub>R] \<lesssim>\<^sub>C \<rho> @ [[X]\<^sub>R, [Tock]\<^sub>E]"
          using ctt_prefix_subset_same_front by fastforce
        then have in_P: "\<rho> @ [[X]\<^sub>R] \<in> P"
          using CT1_P case_assm3 unfolding CT1_def by auto 
        have CT3_P: "CT3 P"
          by (simp add: CT_CT3 assms(1))
        then have "Tock \<notin> X"
          using CT3_def CT3_end_tock \<rho>'_in_P_Q \<rho>_split case_assm case_assm3 by force
        then have in_Q: "\<rho> @ [[X]\<^sub>R] \<in> Q"
          using assm1 unfolding ExtChoiceCTT_def
        proof auto
          fix r s t :: "'a cttobs list"
          assume 1: "r \<in> tocks UNIV"
          assume 2: "r @ s \<in> P"
          assume 3: "r @ t \<in> Q"
          assume 4: "\<forall>\<rho>''\<in>tocks UNIV. \<rho>'' \<le>\<^sub>C r @ s \<longrightarrow> \<rho>'' \<le>\<^sub>C r"
          assume 5: "\<forall>\<rho>''\<in>tocks UNIV. \<rho>'' \<le>\<^sub>C r @ t \<longrightarrow> \<rho>'' \<le>\<^sub>C r"
          assume 6: "\<forall>X. s = [[X]\<^sub>R] \<longrightarrow> (\<exists>Y. t = [[Y]\<^sub>R] \<and> (\<forall>e. (e \<in> X) = (e \<in> Y) \<or> e = Tock))"
          assume 7: "\<forall>X. t = [[X]\<^sub>R] \<longrightarrow> (\<exists>Y. s = [[Y]\<^sub>R] \<and> (\<forall>e. (e \<in> X) = (e \<in> Y) \<or> e = Tock))"
          assume 8: "\<rho> @ [[X]\<^sub>R] = r @ s"
          assume 9: "Tock \<notin> X"
          have r_is_\<rho>: "r = \<rho>"
            by (metis "1" "4" "8" \<rho>_split append.right_neutral butlast_append butlast_snoc case_assm ctt_prefix_antisym ctt_prefix_concat end_refusal_notin_tocks)
          then have "s = [[X]\<^sub>R]"
            using "8" by blast
          then obtain Y where Y_assms: "t = [[Y]\<^sub>R]" "\<forall>e. (e \<in> X) = (e \<in> Y) \<or> e = Tock"
            using "6" by auto
          then have "\<rho> @ [[Y]\<^sub>R] \<in> Q"
            using "3" r_is_\<rho> by blast
          also have "\<rho> @ [[X]\<^sub>R] \<lesssim>\<^sub>C \<rho> @ [[Y]\<^sub>R]"
            by (metis "9" Y_assms(2) ctt_prefix_subset.simps(2) ctt_prefix_subset_refl ctt_prefix_subset_same_front subsetI)
          then have "\<rho> @ [[X]\<^sub>R] \<in> Q"
            using CT1_def CT_CT1 assms(2) calculation by blast
          then show "r @ s \<in> Q"
            using "8" by auto
        qed
        then have "\<rho> @ [[X \<union> Y]\<^sub>R] \<in> Q"
          using CT2_P_Q CT2_def case_assm4 by blast
        then show "\<rho> @ [[X \<union> Y]\<^sub>R] \<in> P \<box>\<^sub>C Q"
          unfolding ExtChoiceCTT_def using notock_X_Y_in_P_Q apply auto
          apply (rule_tac x="\<rho>'" in bexI, simp_all add: \<rho>_split case_assm)
          apply (rule_tac x="[[{e \<in> X \<union> Y. e \<noteq> Tock}]\<^sub>R]" in exI, auto)
          apply (rule_tac x="[[X \<union> Y]\<^sub>R]" in exI, simp_all)
          using ctt_prefix_notfront_is_whole end_refusal_notin_tocks by blast+
      next
        assume case_assm3: "\<rho> @ [[X]\<^sub>R, [Tock]\<^sub>E] \<in> Q"
        assume case_assm4: "Y \<inter> {e. e \<noteq> Tock \<and> \<rho> @ [[e]\<^sub>E] \<in> P \<or> e = Tock \<and> \<rho> @ [[X]\<^sub>R, [e]\<^sub>E] \<in> P} = {}"
        have CT1_P: "CT1 Q"
          by (simp add: CT_CT1 assms(2))
        have "\<rho> @ [[X]\<^sub>R] \<lesssim>\<^sub>C \<rho> @ [[X]\<^sub>R, [Tock]\<^sub>E]"
          using ctt_prefix_subset_same_front by fastforce
        then have in_P: "\<rho> @ [[X]\<^sub>R] \<in> Q"
          using CT1_P case_assm3 unfolding CT1_def by auto 
        have CT3_P: "CT3 Q"
          by (simp add: CT_CT3 assms(2))
        then have "Tock \<notin> X"
          using CT3_def CT3_end_tock \<rho>'_in_P_Q \<rho>_split case_assm case_assm3 by force
        then have in_P: "\<rho> @ [[X]\<^sub>R] \<in> P"
          using assm1 unfolding ExtChoiceCTT_def
        proof auto
          fix r s t :: "'a cttobs list"
          assume 1: "r \<in> tocks UNIV"
          assume 2: "r @ s \<in> P"
          assume 3: "r @ t \<in> Q"
          assume 4: "\<forall>\<rho>''\<in>tocks UNIV. \<rho>'' \<le>\<^sub>C r @ s \<longrightarrow> \<rho>'' \<le>\<^sub>C r"
          assume 5: "\<forall>\<rho>''\<in>tocks UNIV. \<rho>'' \<le>\<^sub>C r @ t \<longrightarrow> \<rho>'' \<le>\<^sub>C r"
          assume 6: "\<forall>X. s = [[X]\<^sub>R] \<longrightarrow> (\<exists>Y. t = [[Y]\<^sub>R] \<and> (\<forall>e. (e \<in> X) = (e \<in> Y) \<or> e = Tock))"
          assume 7: "\<forall>X. t = [[X]\<^sub>R] \<longrightarrow> (\<exists>Y. s = [[Y]\<^sub>R] \<and> (\<forall>e. (e \<in> X) = (e \<in> Y) \<or> e = Tock))"
          assume 8: "\<rho> @ [[X]\<^sub>R] = r @ t"
          assume 9: "Tock \<notin> X"
          have r_is_\<rho>: "r = \<rho>"
            by (metis "1" "5" "8" \<rho>_split append.right_neutral butlast_append butlast_snoc case_assm ctt_prefix_antisym ctt_prefix_concat end_refusal_notin_tocks)
          then have "t = [[X]\<^sub>R]"
            using "8" by blast
          then obtain Y where Y_assms: "s = [[Y]\<^sub>R]" "\<forall>e. (e \<in> X) = (e \<in> Y) \<or> e = Tock"
            using "7" by auto
          then have "\<rho> @ [[Y]\<^sub>R] \<in> P"
            using "2" r_is_\<rho> by blast
          also have "\<rho> @ [[X]\<^sub>R] \<lesssim>\<^sub>C \<rho> @ [[Y]\<^sub>R]"
            by (metis "9" Y_assms(2) ctt_prefix_subset.simps(2) ctt_prefix_subset_refl ctt_prefix_subset_same_front subsetI)
          then have "\<rho> @ [[X]\<^sub>R] \<in> P"
            using CT1_def CT_CT1 assms(1) calculation by blast
          then show "r @ t \<in> P"
            using "8" by auto
        qed
        then have "\<rho> @ [[X \<union> Y]\<^sub>R] \<in> P"
          using CT2_P_Q CT2_def case_assm4 by blast
        then show "\<rho> @ [[X \<union> Y]\<^sub>R] \<in> P \<box>\<^sub>C Q"
          unfolding ExtChoiceCTT_def using notock_X_Y_in_P_Q apply auto
          apply (rule_tac x="\<rho>'" in bexI, simp_all add: \<rho>_split case_assm)
          apply (rule_tac x="[[X \<union> Y]\<^sub>R]" in exI, simp_all)
          apply (rule_tac x="[[{e \<in> X \<union> Y. e \<noteq> Tock}]\<^sub>R]" in exI, auto)
          using ctt_prefix_notfront_is_whole end_refusal_notin_tocks by blast+
      qed
    next
      assume case_assm2: "Tock \<notin> Y"
      then have "Y \<inter> {e. e \<noteq> Tock \<and> \<rho> @ [[e]\<^sub>E] \<in> P \<box>\<^sub>C Q \<or> e = Tock \<and> \<rho> @ [[X]\<^sub>R, [e]\<^sub>E] \<in> P \<box>\<^sub>C Q}
        = {e. e \<in> Y \<and> e \<noteq> Tock} \<inter> {e. e \<noteq> Tock \<and> \<rho> @ [[e]\<^sub>E] \<in> P \<box>\<^sub>C Q \<or> e = Tock \<and> \<rho> @ [[X]\<^sub>R, [e]\<^sub>E] \<in> P \<box>\<^sub>C Q}"
        by auto
      also have "... = {e. e \<in> Y \<and> e \<noteq> Tock} \<inter> {e. e \<noteq> Tock \<and> \<rho> @ [[e]\<^sub>E] \<in> P \<box>\<^sub>C Q}"
        by auto
      also have "... = {e. e \<in> Y \<and> e \<noteq> Tock} \<inter> ({e. e \<noteq> Tock \<and> \<rho> @ [[e]\<^sub>E] \<in> P} \<union> {e. e \<noteq> Tock \<and> \<rho> @ [[e]\<^sub>E] \<in> Q})"
        using set1 by auto
      also have "... = ({e. e \<in> Y \<and> e \<noteq> Tock} \<inter> {e. e \<noteq> Tock \<and> \<rho> @ [[e]\<^sub>E] \<in> P}) \<union> ({e. e \<in> Y \<and> e \<noteq> Tock} \<inter> {e. e \<noteq> Tock \<and> \<rho> @ [[e]\<^sub>E] \<in> Q})"
        by auto
      also have "... = ({e. e \<in> Y \<and> e \<noteq> Tock} \<inter> {e. e \<noteq> Tock \<and> \<rho> @ [[e]\<^sub>E] \<in> P \<or> e = Tock \<and> \<rho> @ [[X]\<^sub>R, [e]\<^sub>E] \<in> P}) 
        \<union> ({e. e \<in> Y \<and> e \<noteq> Tock} \<inter> {e. e \<noteq> Tock \<and> \<rho> @ [[e]\<^sub>E] \<in> Q \<or> e = Tock \<and> \<rho> @ [[X]\<^sub>R, [e]\<^sub>E] \<in> Q})"
        by auto
      also have "... = (Y \<inter> {e. e \<noteq> Tock \<and> \<rho> @ [[e]\<^sub>E] \<in> P \<or> e = Tock \<and> \<rho> @ [[X]\<^sub>R, [e]\<^sub>E] \<in> P}) 
        \<union> (Y \<inter> {e. e \<noteq> Tock \<and> \<rho> @ [[e]\<^sub>E] \<in> Q \<or> e = Tock \<and> \<rho> @ [[X]\<^sub>R, [e]\<^sub>E] \<in> Q})"
        using case_assm2 by auto
      then have assm2_expand: "Y \<inter> {e. e \<noteq> Tock \<and> \<rho> @ [[e]\<^sub>E] \<in> P \<or> e = Tock \<and> \<rho> @ [[X]\<^sub>R, [e]\<^sub>E] \<in> P} = {}
          \<and> Y \<inter> {e. e \<noteq> Tock \<and> \<rho> @ [[e]\<^sub>E] \<in> Q \<or> e = Tock \<and> \<rho> @ [[X]\<^sub>R, [e]\<^sub>E] \<in> Q} = {}"
        using calculation assm2 by auto
      show "\<rho> @ [[X \<union> Y]\<^sub>R] \<in> P \<box>\<^sub>C Q"
        using in_P_or_Q
      proof auto
        assume  case_assm3: "\<rho> @ [[X]\<^sub>R] \<in> P"
        have "CT2 P"
          by (simp add: CT2_P_Q)
        then have "\<rho> @ [[X \<union> Y]\<^sub>R] \<in> P"
          unfolding CT2_def using case_assm3 assm2_expand by auto
        then show  "\<rho> @ [[X \<union> Y]\<^sub>R] \<in> P \<box>\<^sub>C Q"
          unfolding ExtChoiceCTT_def using notock_X_Y_in_P_Q apply auto
          apply (rule_tac x="\<rho>'" in bexI, simp_all add: \<rho>_split case_assm)
          apply (rule_tac x="[[X \<union> Y]\<^sub>R]" in exI, simp_all)
          apply (rule_tac x="[[{e \<in> X \<union> Y. e \<noteq> Tock}]\<^sub>R]" in exI, auto)
          using ctt_prefix_notfront_is_whole end_refusal_notin_tocks by blast+
      next
        assume  case_assm3: "\<rho> @ [[X]\<^sub>R] \<in> Q"
        have "CT2 Q"
          by (simp add: CT2_P_Q)
        then have "\<rho> @ [[X \<union> Y]\<^sub>R] \<in> Q"
          unfolding CT2_def using case_assm3 assm2_expand by auto
        then show  "\<rho> @ [[X \<union> Y]\<^sub>R] \<in> P \<box>\<^sub>C Q"
          unfolding ExtChoiceCTT_def using notock_X_Y_in_P_Q apply auto
          apply (rule_tac x="\<rho>'" in bexI, simp_all add: \<rho>_split case_assm)
          apply (rule_tac x="[[{e \<in> X \<union> Y. e \<noteq> Tock}]\<^sub>R]" in exI, auto)
          apply (rule_tac x="[[X \<union> Y]\<^sub>R]" in exI, simp_all)
          using ctt_prefix_notfront_is_whole end_refusal_notin_tocks by blast+
      qed
    qed
  qed
qed

lemma CT3_ExtChoice: 
  assumes "CT3 P" "CT3 Q"
  shows "CT3 (P \<box>\<^sub>C Q)"
  using assms unfolding CT3_def ExtChoiceCTT_def by auto

lemma CT4s_ExtChoice:
  assumes "CT4s P" "CT4s Q"
  shows "CT4s (P \<box>\<^sub>C Q)"
  unfolding CT4s_def ExtChoiceCTT_def
proof auto
  fix \<rho>' \<sigma> \<tau> :: "'a cttobs list"
  assume assm1: "\<rho>' \<in> tocks UNIV"
  assume assm2: "\<rho>' @ \<sigma> \<in> P"
  assume assm3: "\<rho>' @ \<tau> \<in> Q"
  assume assm4: "\<forall>\<rho>''\<in>tocks UNIV. \<rho>'' \<le>\<^sub>C \<rho>' @ \<sigma> \<longrightarrow> \<rho>'' \<le>\<^sub>C \<rho>'"
  assume assm5: "\<forall>\<rho>''\<in>tocks UNIV. \<rho>'' \<le>\<^sub>C \<rho>' @ \<tau> \<longrightarrow> \<rho>'' \<le>\<^sub>C \<rho>'"
  assume assm6: "\<forall>X. \<sigma> = [[X]\<^sub>R] \<longrightarrow> (\<exists>Y. \<tau> = [[Y]\<^sub>R] \<and> (\<forall>e. (e \<in> X) = (e \<in> Y) \<or> e = Tock))"
  assume assm7: "\<forall>X. \<tau> = [[X]\<^sub>R] \<longrightarrow> (\<exists>Y. \<sigma> = [[Y]\<^sub>R] \<and> (\<forall>e. (e \<in> X) = (e \<in> Y) \<or> e = Tock))"
  have 1: "add_Tick_refusal_trace \<rho>' \<in> tocks UNIV"
    using CT4s_def CT4s_tocks assm1 by blast
  have 2: "add_Tick_refusal_trace \<rho>' @ add_Tick_refusal_trace \<sigma> \<in> P"
    using assms(1) assm2 unfolding CT4s_def by (erule_tac x="\<rho>' @ \<sigma>" in allE, auto simp add: add_Tick_refusal_trace_concat)
  have 3: "add_Tick_refusal_trace \<rho>' @ add_Tick_refusal_trace \<tau> \<in> Q"
    using assms(2) assm3 unfolding CT4s_def by (erule_tac x="\<rho>' @ \<tau>" in allE, auto simp add: add_Tick_refusal_trace_concat)
  have 4: "\<forall>\<rho>''\<in>tocks UNIV. \<rho>'' \<le>\<^sub>C add_Tick_refusal_trace \<rho>' @ add_Tick_refusal_trace \<sigma> \<longrightarrow> \<rho>'' \<le>\<^sub>C add_Tick_refusal_trace \<rho>'"
  proof auto
    fix \<rho>''
    assume assms2: "\<rho>'' \<in> tocks UNIV" "\<rho>'' \<le>\<^sub>C add_Tick_refusal_trace \<rho>' @ add_Tick_refusal_trace \<sigma>"
    then obtain \<rho>''' where \<rho>'''_assms: "\<rho>''' \<subseteq>\<^sub>C \<rho>'' \<and> \<rho>''' \<le>\<^sub>C \<rho>' @ \<sigma>"
      by (metis add_Tick_refusal_trace_concat add_Tick_refusal_trace_ctt_subset ctt_prefix_ctt_subset)
    then have "\<rho>''' \<in> tocks UNIV"
      using assms2(1) tocks_ctt_subset1 by blast
    then have "\<rho>''' \<le>\<^sub>C \<rho>'"
      using \<rho>'''_assms assm4 by blast
    then show "\<rho>'' \<le>\<^sub>C add_Tick_refusal_trace \<rho>'"
      by (smt \<rho>'''_assms add_Tick_refusal_trace_concat add_Tick_refusal_trace_ctt_subset append_eq_append_conv assms2(2) ctt_prefix_concat ctt_prefix_split ctt_subset_same_length)
  qed
  have 5: "\<forall>\<rho>''\<in>tocks UNIV. \<rho>'' \<le>\<^sub>C add_Tick_refusal_trace \<rho>' @ add_Tick_refusal_trace \<tau> \<longrightarrow> \<rho>'' \<le>\<^sub>C add_Tick_refusal_trace \<rho>'"
  proof auto
    fix \<rho>''
    assume assms2: "\<rho>'' \<in> tocks UNIV" "\<rho>'' \<le>\<^sub>C add_Tick_refusal_trace \<rho>' @ add_Tick_refusal_trace \<tau>"
    then obtain \<rho>''' where \<rho>'''_assms: "\<rho>''' \<subseteq>\<^sub>C \<rho>'' \<and> \<rho>''' \<le>\<^sub>C \<rho>' @ \<tau>"
      by (metis add_Tick_refusal_trace_concat add_Tick_refusal_trace_ctt_subset ctt_prefix_ctt_subset)
    then have "\<rho>''' \<in> tocks UNIV"
      using assms2(1) tocks_ctt_subset1 by blast
    then have "\<rho>''' \<le>\<^sub>C \<rho>'"
      using \<rho>'''_assms assm5 by blast
    then show "\<rho>'' \<le>\<^sub>C add_Tick_refusal_trace \<rho>'"
      by (smt \<rho>'''_assms add_Tick_refusal_trace_concat add_Tick_refusal_trace_ctt_subset append_eq_append_conv assms2(2) ctt_prefix_concat ctt_prefix_split ctt_subset_same_length)
  qed
  have 6: "\<forall>X. add_Tick_refusal_trace \<sigma> = [[X]\<^sub>R] \<longrightarrow> (\<exists>Y. add_Tick_refusal_trace \<tau> = [[Y]\<^sub>R] \<and> (\<forall>e. (e \<in> X) = (e \<in> Y) \<or> e = Tock))"
  proof auto
    fix X
    assume "add_Tick_refusal_trace \<sigma> = [[X]\<^sub>R]"
    then obtain X' where X'_assms: "\<sigma> = [[X']\<^sub>R] \<and> X = X' \<union> {Tick}"
      apply (cases \<sigma> rule:add_Tick_refusal_trace.cases, simp_all)
      using add_Tick_refusal_trace.elims by blast
    then obtain Y' where Y'_assms: "\<tau> = [[Y']\<^sub>R] \<and> (\<forall>e. (e \<in> X') = (e \<in> Y') \<or> e = Tock)"
      using assm6 by blast
    then show "\<exists>Y. add_Tick_refusal_trace \<tau> = [[Y]\<^sub>R] \<and> (\<forall>e. (e \<in> X) = (e \<in> Y) \<or> e = Tock)"
      using X'_assms by (rule_tac x="Y' \<union> {Tick}" in exI, auto)
  qed
  have 7: "\<forall>X. add_Tick_refusal_trace \<tau> = [[X]\<^sub>R] \<longrightarrow> (\<exists>Y. add_Tick_refusal_trace \<sigma> = [[Y]\<^sub>R] \<and> (\<forall>e. (e \<in> X) = (e \<in> Y) \<or> e = Tock))"
  proof auto
    fix X
    assume "add_Tick_refusal_trace \<tau> = [[X]\<^sub>R]"
    then obtain X' where X'_assms: "\<tau> = [[X']\<^sub>R] \<and> X = X' \<union> {Tick}"
      apply (cases \<tau> rule:add_Tick_refusal_trace.cases, simp_all)
      using add_Tick_refusal_trace.elims by blast
    then obtain Y' where Y'_assms: "\<sigma> = [[Y']\<^sub>R] \<and> (\<forall>e. (e \<in> X') = (e \<in> Y') \<or> e = Tock)"
      using assm7 by blast
    then show "\<exists>Y. add_Tick_refusal_trace \<sigma> = [[Y]\<^sub>R] \<and> (\<forall>e. (e \<in> X) = (e \<in> Y) \<or> e = Tock)"
      using X'_assms by (rule_tac x="Y' \<union> {Tick}" in exI, auto)
  qed
  show "\<exists>\<rho>\<in>tocks UNIV.
    \<exists>\<sigma>'. \<rho> @ \<sigma>' \<in> P \<and>
      (\<exists>\<tau>. \<rho> @ \<tau> \<in> Q \<and>
        (\<forall>\<rho>'\<in>tocks UNIV. \<rho>' \<le>\<^sub>C \<rho> @ \<sigma>' \<longrightarrow> \<rho>' \<le>\<^sub>C \<rho>) \<and>
        (\<forall>\<rho>'\<in>tocks UNIV. \<rho>' \<le>\<^sub>C \<rho> @ \<tau> \<longrightarrow> \<rho>' \<le>\<^sub>C \<rho>) \<and>
        (\<forall>X. \<sigma>' = [[X]\<^sub>R] \<longrightarrow> (\<exists>Y. \<tau> = [[Y]\<^sub>R] \<and> (\<forall>e. (e \<in> X) = (e \<in> Y) \<or> e = Tock))) \<and>
        (\<forall>X. \<tau> = [[X]\<^sub>R] \<longrightarrow> (\<exists>Y. \<sigma>' = [[Y]\<^sub>R] \<and> (\<forall>e. (e \<in> X) = (e \<in> Y) \<or> e = Tock))) \<and>
        (add_Tick_refusal_trace (\<rho>' @ \<sigma>) = \<rho> @ \<sigma>' \<or> add_Tick_refusal_trace (\<rho>' @ \<sigma>) = \<rho> @ \<tau>))"
    using 1 2 3 4 5 6 7 apply (rule_tac x="add_Tick_refusal_trace \<rho>'" in bexI, auto)
    apply (rule_tac x="add_Tick_refusal_trace \<sigma>" in exI, auto)
    apply (rule_tac x="add_Tick_refusal_trace \<tau>" in exI, auto)
    by (simp add: add_Tick_refusal_trace_concat)
next
  fix \<rho>' \<sigma> \<tau> :: "'a cttobs list"
  assume assm1: "\<rho>' \<in> tocks UNIV"
  assume assm2: "\<rho>' @ \<sigma> \<in> P"
  assume assm3: "\<rho>' @ \<tau> \<in> Q"
  assume assm4: "\<forall>\<rho>''\<in>tocks UNIV. \<rho>'' \<le>\<^sub>C \<rho>' @ \<sigma> \<longrightarrow> \<rho>'' \<le>\<^sub>C \<rho>'"
  assume assm5: "\<forall>\<rho>''\<in>tocks UNIV. \<rho>'' \<le>\<^sub>C \<rho>' @ \<tau> \<longrightarrow> \<rho>'' \<le>\<^sub>C \<rho>'"
  assume assm6: "\<forall>X. \<sigma> = [[X]\<^sub>R] \<longrightarrow> (\<exists>Y. \<tau> = [[Y]\<^sub>R] \<and> (\<forall>e. (e \<in> X) = (e \<in> Y) \<or> e = Tock))"
  assume assm7: "\<forall>X. \<tau> = [[X]\<^sub>R] \<longrightarrow> (\<exists>Y. \<sigma> = [[Y]\<^sub>R] \<and> (\<forall>e. (e \<in> X) = (e \<in> Y) \<or> e = Tock))"
  have 1: "add_Tick_refusal_trace \<rho>' \<in> tocks UNIV"
    using CT4s_def CT4s_tocks assm1 by blast
  have 2: "add_Tick_refusal_trace \<rho>' @ add_Tick_refusal_trace \<sigma> \<in> P"
    using assms(1) assm2 unfolding CT4s_def by (erule_tac x="\<rho>' @ \<sigma>" in allE, auto simp add: add_Tick_refusal_trace_concat)
  have 3: "add_Tick_refusal_trace \<rho>' @ add_Tick_refusal_trace \<tau> \<in> Q"
    using assms(2) assm3 unfolding CT4s_def by (erule_tac x="\<rho>' @ \<tau>" in allE, auto simp add: add_Tick_refusal_trace_concat)
  have 4: "\<forall>\<rho>''\<in>tocks UNIV. \<rho>'' \<le>\<^sub>C add_Tick_refusal_trace \<rho>' @ add_Tick_refusal_trace \<sigma> \<longrightarrow> \<rho>'' \<le>\<^sub>C add_Tick_refusal_trace \<rho>'"
  proof auto
    fix \<rho>''
    assume assms2: "\<rho>'' \<in> tocks UNIV" "\<rho>'' \<le>\<^sub>C add_Tick_refusal_trace \<rho>' @ add_Tick_refusal_trace \<sigma>"
    then obtain \<rho>''' where \<rho>'''_assms: "\<rho>''' \<subseteq>\<^sub>C \<rho>'' \<and> \<rho>''' \<le>\<^sub>C \<rho>' @ \<sigma>"
      by (metis add_Tick_refusal_trace_concat add_Tick_refusal_trace_ctt_subset ctt_prefix_ctt_subset)
    then have "\<rho>''' \<in> tocks UNIV"
      using assms2(1) tocks_ctt_subset1 by blast
    then have "\<rho>''' \<le>\<^sub>C \<rho>'"
      using \<rho>'''_assms assm4 by blast
    then show "\<rho>'' \<le>\<^sub>C add_Tick_refusal_trace \<rho>'"
      by (smt \<rho>'''_assms add_Tick_refusal_trace_concat add_Tick_refusal_trace_ctt_subset append_eq_append_conv assms2(2) ctt_prefix_concat ctt_prefix_split ctt_subset_same_length)
  qed
  have 5: "\<forall>\<rho>''\<in>tocks UNIV. \<rho>'' \<le>\<^sub>C add_Tick_refusal_trace \<rho>' @ add_Tick_refusal_trace \<tau> \<longrightarrow> \<rho>'' \<le>\<^sub>C add_Tick_refusal_trace \<rho>'"
  proof auto
    fix \<rho>''
    assume assms2: "\<rho>'' \<in> tocks UNIV" "\<rho>'' \<le>\<^sub>C add_Tick_refusal_trace \<rho>' @ add_Tick_refusal_trace \<tau>"
    then obtain \<rho>''' where \<rho>'''_assms: "\<rho>''' \<subseteq>\<^sub>C \<rho>'' \<and> \<rho>''' \<le>\<^sub>C \<rho>' @ \<tau>"
      by (metis add_Tick_refusal_trace_concat add_Tick_refusal_trace_ctt_subset ctt_prefix_ctt_subset)
    then have "\<rho>''' \<in> tocks UNIV"
      using assms2(1) tocks_ctt_subset1 by blast
    then have "\<rho>''' \<le>\<^sub>C \<rho>'"
      using \<rho>'''_assms assm5 by blast
    then show "\<rho>'' \<le>\<^sub>C add_Tick_refusal_trace \<rho>'"
      by (smt \<rho>'''_assms add_Tick_refusal_trace_concat add_Tick_refusal_trace_ctt_subset append_eq_append_conv assms2(2) ctt_prefix_concat ctt_prefix_split ctt_subset_same_length)
  qed
  have 6: "\<forall>X. add_Tick_refusal_trace \<sigma> = [[X]\<^sub>R] \<longrightarrow> (\<exists>Y. add_Tick_refusal_trace \<tau> = [[Y]\<^sub>R] \<and> (\<forall>e. (e \<in> X) = (e \<in> Y) \<or> e = Tock))"
  proof auto
    fix X
    assume "add_Tick_refusal_trace \<sigma> = [[X]\<^sub>R]"
    then obtain X' where X'_assms: "\<sigma> = [[X']\<^sub>R] \<and> X = X' \<union> {Tick}"
      apply (cases \<sigma> rule:add_Tick_refusal_trace.cases, simp_all)
      using add_Tick_refusal_trace.elims by blast
    then obtain Y' where Y'_assms: "\<tau> = [[Y']\<^sub>R] \<and> (\<forall>e. (e \<in> X') = (e \<in> Y') \<or> e = Tock)"
      using assm6 by blast
    then show "\<exists>Y. add_Tick_refusal_trace \<tau> = [[Y]\<^sub>R] \<and> (\<forall>e. (e \<in> X) = (e \<in> Y) \<or> e = Tock)"
      using X'_assms by (rule_tac x="Y' \<union> {Tick}" in exI, auto)
  qed
  have 7: "\<forall>X. add_Tick_refusal_trace \<tau> = [[X]\<^sub>R] \<longrightarrow> (\<exists>Y. add_Tick_refusal_trace \<sigma> = [[Y]\<^sub>R] \<and> (\<forall>e. (e \<in> X) = (e \<in> Y) \<or> e = Tock))"
  proof auto
    fix X
    assume "add_Tick_refusal_trace \<tau> = [[X]\<^sub>R]"
    then obtain X' where X'_assms: "\<tau> = [[X']\<^sub>R] \<and> X = X' \<union> {Tick}"
      apply (cases \<tau> rule:add_Tick_refusal_trace.cases, simp_all)
      using add_Tick_refusal_trace.elims by blast
    then obtain Y' where Y'_assms: "\<sigma> = [[Y']\<^sub>R] \<and> (\<forall>e. (e \<in> X') = (e \<in> Y') \<or> e = Tock)"
      using assm7 by blast
    then show "\<exists>Y. add_Tick_refusal_trace \<sigma> = [[Y]\<^sub>R] \<and> (\<forall>e. (e \<in> X) = (e \<in> Y) \<or> e = Tock)"
      using X'_assms by (rule_tac x="Y' \<union> {Tick}" in exI, auto)
  qed
  show "\<exists>\<rho>\<in>tocks UNIV.
    \<exists>\<sigma>. \<rho> @ \<sigma> \<in> P \<and>
      (\<exists>\<tau>'. \<rho> @ \<tau>' \<in> Q \<and>
        (\<forall>\<rho>'\<in>tocks UNIV. \<rho>' \<le>\<^sub>C \<rho> @ \<sigma> \<longrightarrow> \<rho>' \<le>\<^sub>C \<rho>) \<and>
        (\<forall>\<rho>'\<in>tocks UNIV. \<rho>' \<le>\<^sub>C \<rho> @ \<tau>' \<longrightarrow> \<rho>' \<le>\<^sub>C \<rho>) \<and>
        (\<forall>X. \<sigma> = [[X]\<^sub>R] \<longrightarrow> (\<exists>Y. \<tau>' = [[Y]\<^sub>R] \<and> (\<forall>e. (e \<in> X) = (e \<in> Y) \<or> e = Tock))) \<and>
        (\<forall>X. \<tau>' = [[X]\<^sub>R] \<longrightarrow> (\<exists>Y. \<sigma> = [[Y]\<^sub>R] \<and> (\<forall>e. (e \<in> X) = (e \<in> Y) \<or> e = Tock))) \<and>
        (add_Tick_refusal_trace (\<rho>' @ \<tau>) = \<rho> @ \<sigma> \<or> add_Tick_refusal_trace (\<rho>' @ \<tau>) = \<rho> @ \<tau>'))"
    using 1 2 3 4 5 6 7 apply (rule_tac x="add_Tick_refusal_trace \<rho>'" in bexI, auto)
    apply (rule_tac x="add_Tick_refusal_trace \<sigma>" in exI, auto)
    apply (rule_tac x="add_Tick_refusal_trace \<tau>" in exI, auto)
    by (simp add: add_Tick_refusal_trace_concat)
qed

lemma CT_ExtChoice:
  assumes "CT P" "CT Q"
  shows "CT (P \<box>\<^sub>C Q)"
  unfolding CT_def apply auto
  apply (metis CT_def ExtChoiceCTT_wf assms(1) assms(2))
  apply (simp add: CT0_ExtChoice assms(1) assms(2))
  apply (simp add: CT1_ExtChoice assms(1) assms(2))
  apply (simp add: CT2_ExtChoice assms(1) assms(2))
  apply  (simp add: CT3_ExtChoice CT_CT3 assms(1) assms(2))
  done

lemma ExtChoiceCTT_comm: "P \<box>\<^sub>C Q = Q \<box>\<^sub>C P"
  unfolding ExtChoiceCTT_def by auto

(*lemma ExtChoiceCTT_aux_assoc: 
  assumes "\<forall>t\<in>P. cttWF t" "\<forall>t\<in>Q. cttWF t" "\<forall>t\<in>R. cttWF t"
  shows "P \<box>\<^sup>C (Q \<box>\<^sup>C R) = (P \<box>\<^sup>C Q) \<box>\<^sup>C R"
  (is "?lhs = ?rhs")
proof -
  have "?lhs = {t. \<exists> \<rho>\<in>tocks(UNIV). \<exists> \<sigma> \<tau>. 
    \<rho> @ \<sigma> \<in> P \<and> \<rho> @ \<tau> \<in> (Q \<box>\<^sup>C R) \<and>
    (\<forall>\<rho>'\<in>tocks(UNIV). \<rho>' \<le>\<^sub>C \<rho> @ \<sigma> \<longrightarrow> \<rho>' \<le>\<^sub>C \<rho>) \<and>
    (\<forall>\<rho>'\<in>tocks(UNIV). \<rho>' \<le>\<^sub>C \<rho> @ \<tau> \<longrightarrow> \<rho>' \<le>\<^sub>C \<rho>) \<and>
    (((\<exists> X. \<sigma> = [[X]\<^sub>R]) \<or> (\<exists> X. \<tau> = [[X]\<^sub>R])) \<longrightarrow> \<rho> @ \<sigma> = \<rho> @ \<tau>) \<and>
    (t = \<rho> @ \<sigma> \<or> t = \<rho> @ \<tau>)}"
    unfolding ExtChoiceCTT_aux_def by simp
  also have "... =  {t. \<exists> \<rho>\<in>tocks(UNIV). \<exists> \<sigma> \<tau>. 
    \<rho> @ \<sigma> \<in> (P \<box>\<^sup>C Q) \<and> \<rho> @ \<tau> \<in> R \<and>
    (\<forall>\<rho>'\<in>tocks(UNIV). \<rho>' \<le>\<^sub>C \<rho> @ \<sigma> \<longrightarrow> \<rho>' \<le>\<^sub>C \<rho>) \<and>
    (\<forall>\<rho>'\<in>tocks(UNIV). \<rho>' \<le>\<^sub>C \<rho> @ \<tau> \<longrightarrow> \<rho>' \<le>\<^sub>C \<rho>) \<and>
    (((\<exists> X. \<sigma> = [[X]\<^sub>R]) \<or> (\<exists> X. \<tau> = [[X]\<^sub>R])) \<longrightarrow> \<rho> @ \<sigma> = \<rho> @ \<tau>) \<and>
    (t = \<rho> @ \<sigma> \<or> t = \<rho> @ \<tau>)}"
  proof (safe)
    fix \<rho> \<sigma> \<tau> :: "'a cttobs list"
    assume assm1: "\<rho> \<in> tocks UNIV"
    assume assm2: "\<rho> @ \<sigma> \<in> P"
    assume assm3: "\<rho> @ \<tau> \<in> Q \<box>\<^sup>C R"
    assume assm4: "\<forall>\<rho>'\<in>tocks UNIV. \<rho>' \<le>\<^sub>C \<rho> @ \<sigma> \<longrightarrow> \<rho>' \<le>\<^sub>C \<rho>"
    assume assm5: "\<forall>\<rho>'\<in>tocks UNIV. \<rho>' \<le>\<^sub>C \<rho> @ \<tau> \<longrightarrow> \<rho>' \<le>\<^sub>C \<rho>"
    assume assm6: "\<not> (\<exists>\<rho>'\<in>tocks UNIV.
              \<exists>\<sigma>' \<tau>. \<rho>' @ \<sigma>' \<in> P \<box>\<^sup>C Q \<and>
                     \<rho>' @ \<tau> \<in> R \<and>
                     (\<forall>\<rho>''\<in>tocks UNIV. \<rho>'' \<le>\<^sub>C \<rho>' @ \<sigma>' \<longrightarrow> \<rho>'' \<le>\<^sub>C \<rho>') \<and>
                     (\<forall>\<rho>''\<in>tocks UNIV. \<rho>'' \<le>\<^sub>C \<rho>' @ \<tau> \<longrightarrow> \<rho>'' \<le>\<^sub>C \<rho>') \<and>
                     ((\<exists>X. \<sigma>' = [[X]\<^sub>R]) \<or> (\<exists>X. \<tau> = [[X]\<^sub>R]) \<longrightarrow> \<rho>' @ \<sigma>' = \<rho>' @ \<tau>) \<and> (\<rho> @ \<sigma> = \<rho>' @ \<sigma>' \<or> \<rho> @ \<sigma> = \<rho>' @ \<tau>))"
    assume assm7: "\<nexists>X. \<tau> = [[X]\<^sub>R]"
    obtain \<rho>' \<sigma>' \<tau>' where additional_assms:
                    "\<rho>' \<in> tocks UNIV" "\<rho>' @ \<sigma>' \<in> Q" "\<rho>' @ \<tau>' \<in> R"
                    "\<forall>\<rho>''\<in>tocks UNIV. \<rho>'' \<le>\<^sub>C \<rho>' @ \<sigma>' \<longrightarrow> \<rho>'' \<le>\<^sub>C \<rho>'"
                    "\<forall>\<rho>''\<in>tocks UNIV. \<rho>'' \<le>\<^sub>C \<rho>' @ \<tau>' \<longrightarrow> \<rho>'' \<le>\<^sub>C \<rho>'"
                    "\<rho> @ \<tau> = \<rho>' @ \<sigma>' \<or> \<rho> @ \<tau> = \<rho>' @ \<tau>'"
                    "(\<exists>X. \<sigma>' = [[X]\<^sub>R]) \<or> (\<exists>X. \<tau>' = [[X]\<^sub>R]) \<longrightarrow> \<rho>' @ \<sigma>' = \<rho>' @ \<tau>'"
      using assm3 unfolding ExtChoiceCTT_aux_def by (clarify, blast)
    have "\<rho> = \<rho>'"
      using additional_assms(6)
    proof auto
      assume case1: "\<rho> @ \<tau> = \<rho>' @ \<sigma>'"
      have "\<rho> \<le>\<^sub>C \<rho>'" by (metis additional_assms(4) assm1 case1 ctt_prefix_concat)
      also have "\<rho>' \<le>\<^sub>C \<rho>" by (simp add: additional_assms(1) assm5 case1 ctt_prefix_concat)
      then show "\<rho> = \<rho>'" by (simp add: calculation ctt_prefix_antisym)
    next
      assume case1: "\<rho> @ \<tau> = \<rho>' @ \<tau>'"
      have "\<rho> \<le>\<^sub>C \<rho>'" by (metis additional_assms(5) assm1 case1 ctt_prefix_concat)
      also have "\<rho>' \<le>\<^sub>C \<rho>" by (simp add: additional_assms(1) assm5 case1 ctt_prefix_concat)
      then show "\<rho> = \<rho>'" by (simp add: calculation ctt_prefix_antisym)
    qed
    then have "\<nexists>X. \<sigma> = [[X]\<^sub>R] \<Longrightarrow> \<exists>\<rho>'\<in>tocks UNIV.
              \<exists>\<sigma>' \<tau>. \<rho>' @ \<sigma>' \<in> P \<box>\<^sup>C Q \<and>
                     \<rho>' @ \<tau> \<in> R \<and>
                     (\<forall>\<rho>''\<in>tocks UNIV. \<rho>'' \<le>\<^sub>C \<rho>' @ \<sigma>' \<longrightarrow> \<rho>'' \<le>\<^sub>C \<rho>') \<and>
                     (\<forall>\<rho>''\<in>tocks UNIV. \<rho>'' \<le>\<^sub>C \<rho>' @ \<tau> \<longrightarrow> \<rho>'' \<le>\<^sub>C \<rho>') \<and>
                     ((\<exists>X. \<sigma>' = [[X]\<^sub>R]) \<or> (\<exists>X. \<tau> = [[X]\<^sub>R]) \<longrightarrow> \<rho>' @ \<sigma>' = \<rho>' @ \<tau>) \<and> (\<rho> @ \<sigma> = \<rho>' @ \<sigma>' \<or> \<rho> @ \<sigma> = \<rho>' @ \<tau>)"
      apply (rule_tac x="\<rho>" in bexI, rule_tac x="\<sigma>" in exI, rule_tac x="\<tau>'" in exI, safe)
      using assm1 assm2 assm4 assm5 assm7 additional_assms apply (simp_all)
      unfolding ExtChoiceCTT_aux_def apply (safe)
      apply (rule_tac x="\<rho>" in bexI, rule_tac x="\<sigma>" in exI, rule_tac x="\<sigma>'" in exI, safe, blast, blast)+
      done
    then show "\<exists>X. \<sigma> = [[X]\<^sub>R]"
      using assm6 by blast
  next
    fix \<rho> \<sigma> \<tau> :: "'a cttobs list"
    assume assm1: "\<rho> \<in> tocks UNIV"
    assume assm2: "\<rho> @ \<tau> \<in> P"
    assume assm3: "\<rho> @ \<tau> \<in> Q \<box>\<^sup>C R"
    assume assm5: "\<forall>\<rho>'\<in>tocks UNIV. \<rho>' \<le>\<^sub>C \<rho> @ \<tau> \<longrightarrow> \<rho>' \<le>\<^sub>C \<rho>"
    obtain \<rho>' \<sigma>' \<tau>' where additional_assms:
                    "\<rho>' \<in> tocks UNIV" "\<rho>' @ \<sigma>' \<in> Q" "\<rho>' @ \<tau>' \<in> R"
                    "\<forall>\<rho>''\<in>tocks UNIV. \<rho>'' \<le>\<^sub>C \<rho>' @ \<sigma>' \<longrightarrow> \<rho>'' \<le>\<^sub>C \<rho>'"
                    "\<forall>\<rho>''\<in>tocks UNIV. \<rho>'' \<le>\<^sub>C \<rho>' @ \<tau>' \<longrightarrow> \<rho>'' \<le>\<^sub>C \<rho>'"
                    "\<rho> @ \<tau> = \<rho>' @ \<sigma>' \<or> \<rho> @ \<tau> = \<rho>' @ \<tau>'"
                    "(\<exists>X. \<sigma>' = [[X]\<^sub>R]) \<or> (\<exists>X. \<tau>' = [[X]\<^sub>R]) \<longrightarrow> \<rho>' @ \<sigma>' = \<rho>' @ \<tau>'"
      using assm3 unfolding ExtChoiceCTT_aux_def by (clarify, blast)
    have "\<rho> = \<rho>'"
      using additional_assms(6)
    proof auto
      assume case1: "\<rho> @ \<tau> = \<rho>' @ \<sigma>'"
      have "\<rho> \<le>\<^sub>C \<rho>'" by (metis additional_assms(4) assm1 case1 ctt_prefix_concat)
      also have "\<rho>' \<le>\<^sub>C \<rho>" by (simp add: additional_assms(1) assm5 case1 ctt_prefix_concat)
      then show "\<rho> = \<rho>'" by (simp add: calculation ctt_prefix_antisym)
    next
      assume case1: "\<rho> @ \<tau> = \<rho>' @ \<tau>'"
      have "\<rho> \<le>\<^sub>C \<rho>'" by (metis additional_assms(5) assm1 case1 ctt_prefix_concat)
      also have "\<rho>' \<le>\<^sub>C \<rho>" by (simp add: additional_assms(1) assm5 case1 ctt_prefix_concat)
      then show "\<rho> = \<rho>'" by (simp add: calculation ctt_prefix_antisym)
    qed
    then show "\<exists>\<rho>'\<in>tocks UNIV.
          \<exists>\<sigma> \<tau>'. \<rho>' @ \<sigma> \<in> P \<box>\<^sup>C Q \<and>
                 \<rho>' @ \<tau>' \<in> R \<and>
                 (\<forall>\<rho>''\<in>tocks UNIV. \<rho>'' \<le>\<^sub>C \<rho>' @ \<sigma> \<longrightarrow> \<rho>'' \<le>\<^sub>C \<rho>') \<and>
                 (\<forall>\<rho>''\<in>tocks UNIV. \<rho>'' \<le>\<^sub>C \<rho>' @ \<tau>' \<longrightarrow> \<rho>'' \<le>\<^sub>C \<rho>') \<and>
                 ((\<exists>X. \<sigma> = [[X]\<^sub>R]) \<or> (\<exists>X. \<tau>' = [[X]\<^sub>R]) \<longrightarrow> \<rho>' @ \<sigma> = \<rho>' @ \<tau>') \<and> (\<rho> @ \<tau> = \<rho>' @ \<sigma> \<or> \<rho> @ \<tau> = \<rho>' @ \<tau>')"
      apply (rule_tac x="\<rho>" in bexI, rule_tac x="\<tau>" in exI, rule_tac x="\<tau>'" in exI, safe)
      using assm1 assm2 assm5 additional_assms apply (simp_all)
      apply safe
      unfolding ExtChoiceCTT_aux_def apply (safe)
      apply (rule_tac x="\<rho>" in bexI, rule_tac x="\<sigma>'" in exI, rule_tac x="\<sigma>'" in exI, safe)
      apply (rule_tac x="\<rho>" in bexI, rule_tac x="\<sigma>'" in exI, rule_tac x="\<sigma>'" in exI, safe)
      apply (rule_tac x="\<rho>" in bexI, rule_tac x="\<sigma>'" in exI, rule_tac x="\<sigma>'" in exI, safe)
      apply (rule_tac x="\<rho>" in bexI, rule_tac x="\<tau>'" in exI, rule_tac x="\<sigma>'" in exI, safe)
      apply (rule_tac x="\<rho>" in bexI, rule_tac x="\<tau>'" in exI, rule_tac x="\<sigma>'" in exI, safe)
      apply (rule_tac x="\<rho>" in bexI, rule_tac x="\<tau>'" in exI, rule_tac x="\<sigma>'" in exI, safe)
      apply (rule_tac x="\<rho>" in bexI, rule_tac x="\<tau>'" in exI, rule_tac x="\<tau>'" in exI, safe)
      apply (rule_tac x="\<rho>" in bexI, rule_tac x="\<tau>'" in exI, rule_tac x="\<tau>'" in exI, safe)
      apply (blast)
      done
  next
    fix \<rho> \<sigma> \<tau> :: "'a cttobs list"
    assume assm1: "\<rho> \<in> tocks UNIV"
    assume assm2: "\<rho> @ \<sigma> \<in> P"
    assume assm3: "\<rho> @ \<tau> \<in> Q \<box>\<^sup>C R"
    assume assm4: "\<forall>\<rho>'\<in>tocks UNIV. \<rho>' \<le>\<^sub>C \<rho> @ \<sigma> \<longrightarrow> \<rho>' \<le>\<^sub>C \<rho>"
    assume assm5: "\<forall>\<rho>'\<in>tocks UNIV. \<rho>' \<le>\<^sub>C \<rho> @ \<tau> \<longrightarrow> \<rho>' \<le>\<^sub>C \<rho>"
    assume assm6: "\<not> (\<exists>\<rho>'\<in>tocks UNIV.
              \<exists>\<sigma> \<tau>'. \<rho>' @ \<sigma> \<in> P \<box>\<^sup>C Q \<and>
                     \<rho>' @ \<tau>' \<in> R \<and>
                     (\<forall>\<rho>''\<in>tocks UNIV. \<rho>'' \<le>\<^sub>C \<rho>' @ \<sigma> \<longrightarrow> \<rho>'' \<le>\<^sub>C \<rho>') \<and>
                     (\<forall>\<rho>''\<in>tocks UNIV. \<rho>'' \<le>\<^sub>C \<rho>' @ \<tau>' \<longrightarrow> \<rho>'' \<le>\<^sub>C \<rho>') \<and>
                     ((\<exists>X. \<sigma> = [[X]\<^sub>R]) \<or> (\<exists>X. \<tau>' = [[X]\<^sub>R]) \<longrightarrow> \<rho>' @ \<sigma> = \<rho>' @ \<tau>') \<and> (\<rho> @ \<tau> = \<rho>' @ \<sigma> \<or> \<rho> @ \<tau> = \<rho>' @ \<tau>'))"
    assume assm7: "\<nexists>X. \<tau> = [[X]\<^sub>R]"
    obtain \<rho>' \<sigma>' \<tau>' where additional_assms:
                    "\<rho>' \<in> tocks UNIV" "\<rho>' @ \<sigma>' \<in> Q" "\<rho>' @ \<tau>' \<in> R"
                    "\<forall>\<rho>''\<in>tocks UNIV. \<rho>'' \<le>\<^sub>C \<rho>' @ \<sigma>' \<longrightarrow> \<rho>'' \<le>\<^sub>C \<rho>'"
                    "\<forall>\<rho>''\<in>tocks UNIV. \<rho>'' \<le>\<^sub>C \<rho>' @ \<tau>' \<longrightarrow> \<rho>'' \<le>\<^sub>C \<rho>'"
                    "\<rho> @ \<tau> = \<rho>' @ \<sigma>' \<or> \<rho> @ \<tau> = \<rho>' @ \<tau>'"
                    "(\<exists>X. \<sigma>' = [[X]\<^sub>R]) \<or> (\<exists>X. \<tau>' = [[X]\<^sub>R]) \<longrightarrow> \<rho>' @ \<sigma>' = \<rho>' @ \<tau>'"
      using assm3 unfolding ExtChoiceCTT_aux_def by (clarify, blast)
    have "\<rho> = \<rho>'"
      using additional_assms(6)
    proof auto
      assume case1: "\<rho> @ \<tau> = \<rho>' @ \<sigma>'"
      have "\<rho> \<le>\<^sub>C \<rho>'" by (metis additional_assms(4) assm1 case1 ctt_prefix_concat)
      also have "\<rho>' \<le>\<^sub>C \<rho>" by (simp add: additional_assms(1) assm5 case1 ctt_prefix_concat)
      then show "\<rho> = \<rho>'" by (simp add: calculation ctt_prefix_antisym)
    next
      assume case1: "\<rho> @ \<tau> = \<rho>' @ \<tau>'"
      have "\<rho> \<le>\<^sub>C \<rho>'" by (metis additional_assms(5) assm1 case1 ctt_prefix_concat)
      also have "\<rho>' \<le>\<^sub>C \<rho>" by (simp add: additional_assms(1) assm5 case1 ctt_prefix_concat)
      then show "\<rho> = \<rho>'" by (simp add: calculation ctt_prefix_antisym)
    qed
    then have "\<nexists>X. \<sigma> = [[X]\<^sub>R] \<Longrightarrow> \<exists>\<rho>'\<in>tocks UNIV.
              \<exists>\<sigma> \<tau>'. \<rho>' @ \<sigma> \<in> P \<box>\<^sup>C Q \<and>
                     \<rho>' @ \<tau>' \<in> R \<and>
                     (\<forall>\<rho>''\<in>tocks UNIV. \<rho>'' \<le>\<^sub>C \<rho>' @ \<sigma> \<longrightarrow> \<rho>'' \<le>\<^sub>C \<rho>') \<and>
                     (\<forall>\<rho>''\<in>tocks UNIV. \<rho>'' \<le>\<^sub>C \<rho>' @ \<tau>' \<longrightarrow> \<rho>'' \<le>\<^sub>C \<rho>') \<and>
                     ((\<exists>X. \<sigma> = [[X]\<^sub>R]) \<or> (\<exists>X. \<tau>' = [[X]\<^sub>R]) \<longrightarrow> \<rho>' @ \<sigma> = \<rho>' @ \<tau>') \<and> (\<rho> @ \<tau> = \<rho>' @ \<sigma> \<or> \<rho> @ \<tau> = \<rho>' @ \<tau>')"
      apply (rule_tac x="\<rho>" in bexI, rule_tac x="\<sigma>'" in exI, rule_tac x="\<tau>'" in exI, safe)
      using assm1 assm2 assm4 assm5 assm7 additional_assms apply (simp_all)
      unfolding ExtChoiceCTT_aux_def apply (safe)
      apply (rule_tac x="\<rho>" in bexI, rule_tac x="\<sigma>" in exI, rule_tac x="\<sigma>'" in exI, safe, blast, blast)+
      done
    then show "\<exists>X. \<sigma> = [[X]\<^sub>R]"
      using assm6 by blast
  next
    fix \<rho> \<sigma> \<tau> :: "'a cttobs list"
    assume assm1: "\<rho> \<in> tocks UNIV"
    assume assm2: "\<rho> @ \<tau> \<in> P"
    assume assm3: "\<rho> @ \<tau> \<in> Q \<box>\<^sup>C R"
    assume assm5: "\<forall>\<rho>'\<in>tocks UNIV. \<rho>' \<le>\<^sub>C \<rho> @ \<tau> \<longrightarrow> \<rho>' \<le>\<^sub>C \<rho>"
    obtain \<rho>' \<sigma>' \<tau>' where additional_assms:
                    "\<rho>' \<in> tocks UNIV" "\<rho>' @ \<sigma>' \<in> Q" "\<rho>' @ \<tau>' \<in> R"
                    "\<forall>\<rho>''\<in>tocks UNIV. \<rho>'' \<le>\<^sub>C \<rho>' @ \<sigma>' \<longrightarrow> \<rho>'' \<le>\<^sub>C \<rho>'"
                    "\<forall>\<rho>''\<in>tocks UNIV. \<rho>'' \<le>\<^sub>C \<rho>' @ \<tau>' \<longrightarrow> \<rho>'' \<le>\<^sub>C \<rho>'"
                    "\<rho> @ \<tau> = \<rho>' @ \<sigma>' \<or> \<rho> @ \<tau> = \<rho>' @ \<tau>'"
                    "(\<exists>X. \<sigma>' = [[X]\<^sub>R]) \<or> (\<exists>X. \<tau>' = [[X]\<^sub>R]) \<longrightarrow> \<rho>' @ \<sigma>' = \<rho>' @ \<tau>'"
      using assm3 unfolding ExtChoiceCTT_aux_def by (clarify, blast)
    have "\<rho> = \<rho>'"
      using additional_assms(6)
    proof auto
      assume case1: "\<rho> @ \<tau> = \<rho>' @ \<sigma>'"
      have "\<rho> \<le>\<^sub>C \<rho>'" by (metis additional_assms(4) assm1 case1 ctt_prefix_concat)
      also have "\<rho>' \<le>\<^sub>C \<rho>" by (simp add: additional_assms(1) assm5 case1 ctt_prefix_concat)
      then show "\<rho> = \<rho>'" by (simp add: calculation ctt_prefix_antisym)
    next
      assume case1: "\<rho> @ \<tau> = \<rho>' @ \<tau>'"
      have "\<rho> \<le>\<^sub>C \<rho>'" by (metis additional_assms(5) assm1 case1 ctt_prefix_concat)
      also have "\<rho>' \<le>\<^sub>C \<rho>" by (simp add: additional_assms(1) assm5 case1 ctt_prefix_concat)
      then show "\<rho> = \<rho>'" by (simp add: calculation ctt_prefix_antisym)
    qed
    then show "\<exists>\<rho>'\<in>tocks UNIV.
          \<exists>\<sigma> \<tau>'. \<rho>' @ \<sigma> \<in> P \<box>\<^sup>C Q \<and>
                 \<rho>' @ \<tau>' \<in> R \<and>
                 (\<forall>\<rho>''\<in>tocks UNIV. \<rho>'' \<le>\<^sub>C \<rho>' @ \<sigma> \<longrightarrow> \<rho>'' \<le>\<^sub>C \<rho>') \<and>
                 (\<forall>\<rho>''\<in>tocks UNIV. \<rho>'' \<le>\<^sub>C \<rho>' @ \<tau>' \<longrightarrow> \<rho>'' \<le>\<^sub>C \<rho>') \<and>
                 ((\<exists>X. \<sigma> = [[X]\<^sub>R]) \<or> (\<exists>X. \<tau>' = [[X]\<^sub>R]) \<longrightarrow> \<rho>' @ \<sigma> = \<rho>' @ \<tau>') \<and> (\<rho> @ \<tau> = \<rho>' @ \<sigma> \<or> \<rho> @ \<tau> = \<rho>' @ \<tau>')"
      apply (rule_tac x="\<rho>" in bexI, rule_tac x="\<tau>" in exI, rule_tac x="\<tau>'" in exI, safe)
      using assm1 assm2 assm5 additional_assms apply (simp_all)
      apply safe
      unfolding ExtChoiceCTT_aux_def apply (safe)
      apply (rule_tac x="\<rho>" in bexI, rule_tac x="\<sigma>'" in exI, rule_tac x="\<sigma>'" in exI, safe)
      apply (rule_tac x="\<rho>" in bexI, rule_tac x="\<sigma>'" in exI, rule_tac x="\<sigma>'" in exI, safe)
      apply (rule_tac x="\<rho>" in bexI, rule_tac x="\<sigma>'" in exI, rule_tac x="\<sigma>'" in exI, safe)
      apply (rule_tac x="\<rho>" in bexI, rule_tac x="\<tau>'" in exI, rule_tac x="\<sigma>'" in exI, safe)
      apply (rule_tac x="\<rho>" in bexI, rule_tac x="\<tau>'" in exI, rule_tac x="\<sigma>'" in exI, safe)
      apply (rule_tac x="\<rho>" in bexI, rule_tac x="\<tau>'" in exI, rule_tac x="\<sigma>'" in exI, safe)
      apply (rule_tac x="\<rho>" in bexI, rule_tac x="\<tau>'" in exI, rule_tac x="\<tau>'" in exI, safe)
      apply (rule_tac x="\<rho>" in bexI, rule_tac x="\<tau>'" in exI, rule_tac x="\<tau>'" in exI, safe)
      apply (blast)
      done
  next
    fix \<rho> \<sigma> \<tau> :: "'a cttobs list"
    assume assm1: "\<rho> \<in> tocks UNIV"
    assume assm2: "\<rho> @ \<sigma> \<in> P \<box>\<^sup>C Q"
    assume assm3: "\<rho> @ \<tau> \<in> R"
    assume assm4: "\<forall>\<rho>'\<in>tocks UNIV. \<rho>' \<le>\<^sub>C \<rho> @ \<sigma> \<longrightarrow> \<rho>' \<le>\<^sub>C \<rho>"
    assume assm5: "\<forall>\<rho>'\<in>tocks UNIV. \<rho>' \<le>\<^sub>C \<rho> @ \<tau> \<longrightarrow> \<rho>' \<le>\<^sub>C \<rho>"
    assume assm6: "\<not> (\<exists>\<rho>'\<in>tocks UNIV.
              \<exists>\<sigma>' \<tau>. \<rho>' @ \<sigma>' \<in> P \<and>
                     \<rho>' @ \<tau> \<in> Q \<box>\<^sup>C R \<and>
                     (\<forall>\<rho>''\<in>tocks UNIV. \<rho>'' \<le>\<^sub>C \<rho>' @ \<sigma>' \<longrightarrow> \<rho>'' \<le>\<^sub>C \<rho>') \<and>
                     (\<forall>\<rho>''\<in>tocks UNIV. \<rho>'' \<le>\<^sub>C \<rho>' @ \<tau> \<longrightarrow> \<rho>'' \<le>\<^sub>C \<rho>') \<and>
                     ((\<exists>X. \<sigma>' = [[X]\<^sub>R]) \<or> (\<exists>X. \<tau> = [[X]\<^sub>R]) \<longrightarrow> \<rho>' @ \<sigma>' = \<rho>' @ \<tau>) \<and> (\<rho> @ \<sigma> = \<rho>' @ \<sigma>' \<or> \<rho> @ \<sigma> = \<rho>' @ \<tau>))"
    assume assm7: "\<nexists>X. \<tau> = [[X]\<^sub>R]"
    obtain \<rho>' \<sigma>' \<tau>' where additional_assms:
                    "\<rho>' \<in> tocks UNIV" "\<rho>' @ \<sigma>' \<in> P" "\<rho>' @ \<tau>' \<in> Q"
                    "\<forall>\<rho>''\<in>tocks UNIV. \<rho>'' \<le>\<^sub>C \<rho>' @ \<sigma>' \<longrightarrow> \<rho>'' \<le>\<^sub>C \<rho>'"
                    "\<forall>\<rho>''\<in>tocks UNIV. \<rho>'' \<le>\<^sub>C \<rho>' @ \<tau>' \<longrightarrow> \<rho>'' \<le>\<^sub>C \<rho>'"
                    "\<rho> @ \<sigma> = \<rho>' @ \<sigma>' \<or> \<rho> @ \<sigma> = \<rho>' @ \<tau>'"
                    "(\<exists>X. \<sigma>' = [[X]\<^sub>R]) \<or> (\<exists>X. \<tau>' = [[X]\<^sub>R]) \<longrightarrow> \<rho>' @ \<sigma>' = \<rho>' @ \<tau>'"
      using assm2 unfolding ExtChoiceCTT_aux_def by (clarify, blast)
    have "\<rho> = \<rho>'"
      using additional_assms(6)
    proof auto
      assume case1: "\<rho> @ \<sigma> = \<rho>' @ \<sigma>'"
      have "\<rho> \<le>\<^sub>C \<rho>'" by (metis additional_assms(4) assm1 case1 ctt_prefix_concat)
      also have "\<rho>' \<le>\<^sub>C \<rho>" by (simp add: additional_assms(1) assm4 case1 ctt_prefix_concat)
      then show "\<rho> = \<rho>'" by (simp add: calculation ctt_prefix_antisym)
    next
      assume case1: "\<rho> @ \<sigma> = \<rho>' @ \<tau>'"
      have "\<rho> \<le>\<^sub>C \<rho>'" by (metis additional_assms(5) assm1 case1 ctt_prefix_concat)
      also have "\<rho>' \<le>\<^sub>C \<rho>" by (simp add: additional_assms(1) assm4 case1 ctt_prefix_concat)
      then show "\<rho> = \<rho>'" by (simp add: calculation ctt_prefix_antisym)
    qed
    then have "\<nexists>X. \<sigma> = [[X]\<^sub>R] \<Longrightarrow> (\<exists>\<rho>'\<in>tocks UNIV.
              \<exists>\<sigma>' \<tau>. \<rho>' @ \<sigma>' \<in> P \<and>
                     \<rho>' @ \<tau> \<in> Q \<box>\<^sup>C R \<and>
                     (\<forall>\<rho>''\<in>tocks UNIV. \<rho>'' \<le>\<^sub>C \<rho>' @ \<sigma>' \<longrightarrow> \<rho>'' \<le>\<^sub>C \<rho>') \<and>
                     (\<forall>\<rho>''\<in>tocks UNIV. \<rho>'' \<le>\<^sub>C \<rho>' @ \<tau> \<longrightarrow> \<rho>'' \<le>\<^sub>C \<rho>') \<and>
                     ((\<exists>X. \<sigma>' = [[X]\<^sub>R]) \<or> (\<exists>X. \<tau> = [[X]\<^sub>R]) \<longrightarrow> \<rho>' @ \<sigma>' = \<rho>' @ \<tau>) \<and> (\<rho> @ \<sigma> = \<rho>' @ \<sigma>' \<or> \<rho> @ \<sigma> = \<rho>' @ \<tau>))"
      apply (rule_tac x="\<rho>" in bexI, rule_tac x="\<sigma>'" in exI, rule_tac x="\<tau>'" in exI, safe)
      using assm1 assm3 assm4 assm5 assm7 additional_assms apply (simp_all)
      unfolding ExtChoiceCTT_aux_def apply (safe)
      apply (rule_tac x="\<rho>" in bexI, rule_tac x="\<tau>'" in exI, rule_tac x="\<tau>" in exI, safe, blast, blast)+
      done
    then show "\<exists>X. \<sigma> = [[X]\<^sub>R]"
      using assm6 by blast
  next
    fix \<rho> \<sigma> \<tau> :: "'a cttobs list"
    assume assm1: "\<rho> \<in> tocks UNIV"
    assume assm2: "\<rho> @ \<tau> \<in> P \<box>\<^sup>C Q"
    assume assm3: "\<rho> @ \<tau> \<in> R"
    assume assm4: "\<forall>\<rho>'\<in>tocks UNIV. \<rho>' \<le>\<^sub>C \<rho> @ \<sigma> \<longrightarrow> \<rho>' \<le>\<^sub>C \<rho>"
    assume assm5: "\<forall>\<rho>'\<in>tocks UNIV. \<rho>' \<le>\<^sub>C \<rho> @ \<tau> \<longrightarrow> \<rho>' \<le>\<^sub>C \<rho>"
    obtain \<rho>' \<sigma>' \<tau>' where additional_assms:
                    "\<rho>' \<in> tocks UNIV" "\<rho>' @ \<sigma>' \<in> P" "\<rho>' @ \<tau>' \<in> Q"
                    "\<forall>\<rho>''\<in>tocks UNIV. \<rho>'' \<le>\<^sub>C \<rho>' @ \<sigma>' \<longrightarrow> \<rho>'' \<le>\<^sub>C \<rho>'"
                    "\<forall>\<rho>''\<in>tocks UNIV. \<rho>'' \<le>\<^sub>C \<rho>' @ \<tau>' \<longrightarrow> \<rho>'' \<le>\<^sub>C \<rho>'"
                    "\<rho> @ \<tau> = \<rho>' @ \<sigma>' \<or> \<rho> @ \<tau> = \<rho>' @ \<tau>'"
                    "(\<exists>X. \<sigma>' = [[X]\<^sub>R]) \<or> (\<exists>X. \<tau>' = [[X]\<^sub>R]) \<longrightarrow> \<rho>' @ \<sigma>' = \<rho>' @ \<tau>'"
      using assm2 unfolding ExtChoiceCTT_aux_def by (clarify, blast)
    have "\<rho> = \<rho>'"
      using additional_assms(6)
    proof auto
      assume case1: "\<rho> @ \<tau> = \<rho>' @ \<sigma>'"
      have "\<rho> \<le>\<^sub>C \<rho>'" by (metis additional_assms(4) assm1 case1 ctt_prefix_concat)
      also have "\<rho>' \<le>\<^sub>C \<rho>" by (simp add: additional_assms(1) assm5 case1 ctt_prefix_concat)
      then show "\<rho> = \<rho>'" by (simp add: calculation ctt_prefix_antisym)
    next
      assume case1: "\<rho> @ \<tau> = \<rho>' @ \<tau>'"
      have "\<rho> \<le>\<^sub>C \<rho>'" by (metis additional_assms(5) assm1 case1 ctt_prefix_concat)
      also have "\<rho>' \<le>\<^sub>C \<rho>" by (simp add: additional_assms(1) assm5 case1 ctt_prefix_concat)
      then show "\<rho> = \<rho>'" by (simp add: calculation ctt_prefix_antisym)
    qed
    then show "\<exists>\<rho>'\<in>tocks UNIV.
          \<exists>\<sigma> \<tau>'. \<rho>' @ \<sigma> \<in> P \<and>
                 \<rho>' @ \<tau>' \<in> Q \<box>\<^sup>C R \<and>
                 (\<forall>\<rho>''\<in>tocks UNIV. \<rho>'' \<le>\<^sub>C \<rho>' @ \<sigma> \<longrightarrow> \<rho>'' \<le>\<^sub>C \<rho>') \<and>
                 (\<forall>\<rho>''\<in>tocks UNIV. \<rho>'' \<le>\<^sub>C \<rho>' @ \<tau>' \<longrightarrow> \<rho>'' \<le>\<^sub>C \<rho>') \<and>
                 ((\<exists>X. \<sigma> = [[X]\<^sub>R]) \<or> (\<exists>X. \<tau>' = [[X]\<^sub>R]) \<longrightarrow> \<rho>' @ \<sigma> = \<rho>' @ \<tau>') \<and> (\<rho> @ \<tau> = \<rho>' @ \<sigma> \<or> \<rho> @ \<tau> = \<rho>' @ \<tau>')"
      apply (rule_tac x="\<rho>" in bexI, rule_tac x="\<sigma>'" in exI, rule_tac x="\<tau>" in exI, safe)
      using assm1 assm3 assm4 assm5 additional_assms apply (simp_all)
      unfolding ExtChoiceCTT_aux_def apply (safe)
      apply (rule_tac x="\<rho>" in bexI, rule_tac x="\<tau>'" in exI, rule_tac x="\<sigma>'" in exI, safe, blast, blast)+
      done
  next
    fix \<rho> \<sigma> \<tau> :: "'a cttobs list"
    assume assm1: "\<rho> \<in> tocks UNIV"
    assume assm2: "\<rho> @ \<sigma> \<in> P \<box>\<^sup>C Q"
    assume assm3: "\<rho> @ \<tau> \<in> R"
    assume assm4: "\<forall>\<rho>'\<in>tocks UNIV. \<rho>' \<le>\<^sub>C \<rho> @ \<sigma> \<longrightarrow> \<rho>' \<le>\<^sub>C \<rho>"
    assume assm5: "\<forall>\<rho>'\<in>tocks UNIV. \<rho>' \<le>\<^sub>C \<rho> @ \<tau> \<longrightarrow> \<rho>' \<le>\<^sub>C \<rho>"
    assume assm6: "\<not> (\<exists>\<rho>'\<in>tocks UNIV.
              \<exists>\<sigma> \<tau>'. \<rho>' @ \<sigma> \<in> P \<and>
                     \<rho>' @ \<tau>' \<in> Q \<box>\<^sup>C R \<and>
                     (\<forall>\<rho>''\<in>tocks UNIV. \<rho>'' \<le>\<^sub>C \<rho>' @ \<sigma> \<longrightarrow> \<rho>'' \<le>\<^sub>C \<rho>') \<and>
                     (\<forall>\<rho>''\<in>tocks UNIV. \<rho>'' \<le>\<^sub>C \<rho>' @ \<tau>' \<longrightarrow> \<rho>'' \<le>\<^sub>C \<rho>') \<and>
                     ((\<exists>X. \<sigma> = [[X]\<^sub>R]) \<or> (\<exists>X. \<tau>' = [[X]\<^sub>R]) \<longrightarrow> \<rho>' @ \<sigma> = \<rho>' @ \<tau>') \<and> (\<rho> @ \<tau> = \<rho>' @ \<sigma> \<or> \<rho> @ \<tau> = \<rho>' @ \<tau>'))"
    assume assm7: "\<nexists>X. \<tau> = [[X]\<^sub>R]"
    obtain \<rho>' \<sigma>' \<tau>' where additional_assms:
                    "\<rho>' \<in> tocks UNIV" "\<rho>' @ \<sigma>' \<in> P" "\<rho>' @ \<tau>' \<in> Q"
                    "\<forall>\<rho>''\<in>tocks UNIV. \<rho>'' \<le>\<^sub>C \<rho>' @ \<sigma>' \<longrightarrow> \<rho>'' \<le>\<^sub>C \<rho>'"
                    "\<forall>\<rho>''\<in>tocks UNIV. \<rho>'' \<le>\<^sub>C \<rho>' @ \<tau>' \<longrightarrow> \<rho>'' \<le>\<^sub>C \<rho>'"
                    "\<rho> @ \<sigma> = \<rho>' @ \<sigma>' \<or> \<rho> @ \<sigma> = \<rho>' @ \<tau>'"
                    "(\<exists>X. \<sigma>' = [[X]\<^sub>R]) \<or> (\<exists>X. \<tau>' = [[X]\<^sub>R]) \<longrightarrow> \<rho>' @ \<sigma>' = \<rho>' @ \<tau>'"
      using assm2 unfolding ExtChoiceCTT_aux_def by (clarify, blast)
    have "\<rho> = \<rho>'"
      using additional_assms(6)
    proof auto
      assume case1: "\<rho> @ \<sigma> = \<rho>' @ \<sigma>'"
      have "\<rho> \<le>\<^sub>C \<rho>'" by (metis additional_assms(4) assm1 case1 ctt_prefix_concat)
      also have "\<rho>' \<le>\<^sub>C \<rho>" by (simp add: additional_assms(1) assm4 case1 ctt_prefix_concat)
      then show "\<rho> = \<rho>'" by (simp add: calculation ctt_prefix_antisym)
    next
      assume case1: "\<rho> @ \<sigma> = \<rho>' @ \<tau>'"
      have "\<rho> \<le>\<^sub>C \<rho>'" by (metis additional_assms(5) assm1 case1 ctt_prefix_concat)
      also have "\<rho>' \<le>\<^sub>C \<rho>" by (simp add: additional_assms(1) assm4 case1 ctt_prefix_concat)
      then show "\<rho> = \<rho>'" by (simp add: calculation ctt_prefix_antisym)
    qed
    then have "\<nexists>X. \<sigma> = [[X]\<^sub>R] \<Longrightarrow> (\<exists>\<rho>'\<in>tocks UNIV.
              \<exists>\<sigma> \<tau>'. \<rho>' @ \<sigma> \<in> P \<and>
                     \<rho>' @ \<tau>' \<in> Q \<box>\<^sup>C R \<and>
                     (\<forall>\<rho>''\<in>tocks UNIV. \<rho>'' \<le>\<^sub>C \<rho>' @ \<sigma> \<longrightarrow> \<rho>'' \<le>\<^sub>C \<rho>') \<and>
                     (\<forall>\<rho>''\<in>tocks UNIV. \<rho>'' \<le>\<^sub>C \<rho>' @ \<tau>' \<longrightarrow> \<rho>'' \<le>\<^sub>C \<rho>') \<and>
                     ((\<exists>X. \<sigma> = [[X]\<^sub>R]) \<or> (\<exists>X. \<tau>' = [[X]\<^sub>R]) \<longrightarrow> \<rho>' @ \<sigma> = \<rho>' @ \<tau>') \<and> (\<rho> @ \<tau> = \<rho>' @ \<sigma> \<or> \<rho> @ \<tau> = \<rho>' @ \<tau>'))"
      apply (rule_tac x="\<rho>" in bexI, rule_tac x="\<sigma>'" in exI, rule_tac x="\<tau>" in exI, safe)
      using assm1 assm3 assm4 assm5 assm7 additional_assms apply (simp_all)
      unfolding ExtChoiceCTT_aux_def apply (safe)
      apply (rule_tac x="\<rho>" in bexI, rule_tac x="\<tau>'" in exI, rule_tac x="\<tau>" in exI, safe, blast+)
      done
    then show "\<exists>X. \<sigma> = [[X]\<^sub>R]"
      using assm6 by blast
  next
    fix \<rho> \<sigma> \<tau> :: "'a cttobs list"
    assume assm1: "\<rho> \<in> tocks UNIV"
    assume assm2: "\<rho> @ \<tau> \<in> P \<box>\<^sup>C Q"
    assume assm3: "\<rho> @ \<tau> \<in> R"
    assume assm4: "\<forall>\<rho>'\<in>tocks UNIV. \<rho>' \<le>\<^sub>C \<rho> @ \<sigma> \<longrightarrow> \<rho>' \<le>\<^sub>C \<rho>"
    assume assm5: "\<forall>\<rho>'\<in>tocks UNIV. \<rho>' \<le>\<^sub>C \<rho> @ \<tau> \<longrightarrow> \<rho>' \<le>\<^sub>C \<rho>"
    obtain \<rho>' \<sigma>' \<tau>' where additional_assms:
                    "\<rho>' \<in> tocks UNIV" "\<rho>' @ \<sigma>' \<in> P" "\<rho>' @ \<tau>' \<in> Q"
                    "\<forall>\<rho>''\<in>tocks UNIV. \<rho>'' \<le>\<^sub>C \<rho>' @ \<sigma>' \<longrightarrow> \<rho>'' \<le>\<^sub>C \<rho>'"
                    "\<forall>\<rho>''\<in>tocks UNIV. \<rho>'' \<le>\<^sub>C \<rho>' @ \<tau>' \<longrightarrow> \<rho>'' \<le>\<^sub>C \<rho>'"
                    "\<rho> @ \<tau> = \<rho>' @ \<sigma>' \<or> \<rho> @ \<tau> = \<rho>' @ \<tau>'"
                    "(\<exists>X. \<sigma>' = [[X]\<^sub>R]) \<or> (\<exists>X. \<tau>' = [[X]\<^sub>R]) \<longrightarrow> \<rho>' @ \<sigma>' = \<rho>' @ \<tau>'"
      using assm2 unfolding ExtChoiceCTT_aux_def by (clarify, blast)
    have "\<rho> = \<rho>'"
      using additional_assms(6)
    proof auto
      assume case1: "\<rho> @ \<tau> = \<rho>' @ \<sigma>'"
      have "\<rho> \<le>\<^sub>C \<rho>'" by (metis additional_assms(4) assm1 case1 ctt_prefix_concat)
      also have "\<rho>' \<le>\<^sub>C \<rho>" by (simp add: additional_assms(1) assm5 case1 ctt_prefix_concat)
      then show "\<rho> = \<rho>'" by (simp add: calculation ctt_prefix_antisym)
    next
      assume case1: "\<rho> @ \<tau> = \<rho>' @ \<tau>'"
      have "\<rho> \<le>\<^sub>C \<rho>'" by (metis additional_assms(5) assm1 case1 ctt_prefix_concat)
      also have "\<rho>' \<le>\<^sub>C \<rho>" by (simp add: additional_assms(1) assm5 case1 ctt_prefix_concat)
      then show "\<rho> = \<rho>'" by (simp add: calculation ctt_prefix_antisym)
    qed
    then show "\<exists>\<rho>'\<in>tocks UNIV.
          \<exists>\<sigma> \<tau>'. \<rho>' @ \<sigma> \<in> P \<and>
                 \<rho>' @ \<tau>' \<in> Q \<box>\<^sup>C R \<and>
                 (\<forall>\<rho>''\<in>tocks UNIV. \<rho>'' \<le>\<^sub>C \<rho>' @ \<sigma> \<longrightarrow> \<rho>'' \<le>\<^sub>C \<rho>') \<and>
                 (\<forall>\<rho>''\<in>tocks UNIV. \<rho>'' \<le>\<^sub>C \<rho>' @ \<tau>' \<longrightarrow> \<rho>'' \<le>\<^sub>C \<rho>') \<and>
                 ((\<exists>X. \<sigma> = [[X]\<^sub>R]) \<or> (\<exists>X. \<tau>' = [[X]\<^sub>R]) \<longrightarrow> \<rho>' @ \<sigma> = \<rho>' @ \<tau>') \<and> (\<rho> @ \<tau> = \<rho>' @ \<sigma> \<or> \<rho> @ \<tau> = \<rho>' @ \<tau>')"
      apply (rule_tac x="\<rho>" in bexI, rule_tac x="\<sigma>'" in exI, rule_tac x="\<tau>" in exI, safe)
      using assm1 assm3 assm4 assm5 additional_assms apply (simp_all)
      unfolding ExtChoiceCTT_aux_def apply (safe)
      apply (rule_tac x="\<rho>" in bexI, rule_tac x="\<tau>'" in exI, rule_tac x="\<sigma>'" in exI, safe, blast, blast)+
      done
  qed
  also have "... = ?rhs"
    unfolding ExtChoiceCTT_aux_def by simp
  then show ?thesis
    using calculation by auto
qed*)

lemma ExtChoiceCTT_union_dist: "P \<box>\<^sub>C (Q \<union> R) = (P \<box>\<^sub>C Q) \<union> (P \<box>\<^sub>C R)"
  unfolding ExtChoiceCTT_def by (safe, blast+)

lemma ExtChoice_subset_union: "P \<box>\<^sub>C Q \<subseteq> P \<union> Q"
  unfolding ExtChoiceCTT_def by auto

lemma ExtChoice_idempotent: "CT P \<Longrightarrow> P \<box>\<^sub>C P = P"
  unfolding ExtChoiceCTT_def apply auto
  using CT_wf split_tocks_longest by fastforce

end