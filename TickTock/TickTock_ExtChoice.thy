theory TickTock_ExtChoice
  imports TickTock_Core
begin

subsection {* External Choice *}

definition ExtChoiceTT :: "'e ttobs list set \<Rightarrow> 'e ttobs list set \<Rightarrow> 'e ttobs list set" (infixl "\<box>\<^sub>C" 57) where
  "P \<box>\<^sub>C Q = {t. \<exists> \<rho>\<in>tocks(UNIV). \<exists> \<sigma> \<tau>. 
    \<rho> @ \<sigma> \<in> P \<and> \<rho> @ \<tau> \<in> Q \<and>
    (\<forall>\<rho>'\<in>tocks(UNIV). \<rho>' \<le>\<^sub>C \<rho> @ \<sigma> \<longrightarrow> \<rho>' \<le>\<^sub>C \<rho>) \<and>
    (\<forall>\<rho>'\<in>tocks(UNIV). \<rho>' \<le>\<^sub>C \<rho> @ \<tau> \<longrightarrow> \<rho>' \<le>\<^sub>C \<rho>) \<and>
    (\<forall> X. \<sigma> = [[X]\<^sub>R] \<longrightarrow> (\<exists> Y. \<tau> = [[Y]\<^sub>R] \<and> (\<forall> e. (e \<in> X = (e \<in> Y)) \<or> (e = Tock)))) \<and>
    (\<forall> X. \<tau> = [[X]\<^sub>R] \<longrightarrow> (\<exists> Y. \<sigma> = [[Y]\<^sub>R] \<and> (\<forall> e. (e \<in> X = (e \<in> Y)) \<or> (e = Tock)))) \<and>
    (t = \<rho> @ \<sigma> \<or> t = \<rho> @ \<tau>)}"

lemma ExtChoiceTT_wf: "\<forall> t\<in>P. ttWF t \<Longrightarrow> \<forall> t\<in>Q. ttWF t \<Longrightarrow> \<forall> t\<in>P \<box>\<^sub>C Q. ttWF t"
  unfolding ExtChoiceTT_def by auto

lemma TT0_ExtChoice:
  assumes "TT P" "TT Q"
  shows "TT0 (P \<box>\<^sub>C Q)"
  unfolding TT0_def apply auto
  unfolding ExtChoiceTT_def apply auto
  using TT_empty assms(1) assms(2) tocks.empty_in_tocks by fastforce

lemma TT1_ExtChoice:
  assumes "TT P" "TT Q"
  shows "TT1 (P \<box>\<^sub>C Q)"
  unfolding TT1_def
proof auto
  fix \<rho> \<sigma> :: "'a ttobs list"
  assume assm1: "\<rho> \<lesssim>\<^sub>C \<sigma>"
  assume assm2: "\<sigma> \<in> P \<box>\<^sub>C Q"
  obtain \<rho>2 where \<rho>2_assms: "\<rho>2 \<le>\<^sub>C \<sigma>" "\<rho> \<subseteq>\<^sub>C \<rho>2"
    using assm1 tt_prefix_subset_imp_tt_subset_tt_prefix by auto
  from assm2 obtain \<sigma>' s t where assm2_assms:
    "\<sigma>'\<in>tocks UNIV"
    "\<sigma>' @ s \<in> P"
    "\<sigma>' @ t \<in> Q"
    "(\<forall>\<rho>'\<in>tocks UNIV. \<rho>' \<le>\<^sub>C \<sigma>' @ s \<longrightarrow> \<rho>' \<le>\<^sub>C \<sigma>')"
    "(\<forall>\<rho>'\<in>tocks UNIV. \<rho>' \<le>\<^sub>C \<sigma>' @ t \<longrightarrow> \<rho>' \<le>\<^sub>C \<sigma>')"
    "\<forall>X. s = [[X]\<^sub>R] \<longrightarrow> (\<exists>Y. t = [[Y]\<^sub>R] \<and> (\<forall>e. (e \<in> X) = (e \<in> Y) \<or> e = Tock))"
    "\<forall>X. t = [[X]\<^sub>R] \<longrightarrow> (\<exists>Y. s = [[Y]\<^sub>R] \<and> (\<forall>e. (e \<in> X) = (e \<in> Y) \<or> e = Tock))"
    "\<sigma> = \<sigma>' @ t \<or> \<sigma> = \<sigma>' @ s"
    unfolding ExtChoiceTT_def by blast
  from assm2_assms(8) have "\<rho>2 \<in> P \<box>\<^sub>C Q"
  proof (auto)
    assume case_assm: "\<sigma> = \<sigma>' @ s"
    then have \<sigma>_in_P: "\<sigma> \<in> P"
      using assm2_assms(2) by blast
    have \<rho>2_in_P: "\<rho>2 \<in> P"
      using TT1_def TT_TT1 \<rho>2_assms(1) \<sigma>_in_P assms(1) tt_prefix_imp_prefix_subset by blast
    have "\<rho>2 \<le>\<^sub>C \<sigma>' \<or> (\<exists> \<rho>2'. \<rho>2 = \<sigma>' @ \<rho>2' \<and> \<rho>2' \<le>\<^sub>C s)"
      using \<rho>2_assms(1) case_assm tt_prefix_append_split by blast
    then show "\<rho>2 \<in> P \<box>\<^sub>C Q"
    proof auto
      assume case_assm2: "\<rho>2 \<le>\<^sub>C \<sigma>'"
      have \<rho>2_in_Q: "\<rho>2 \<in> Q"
        by (meson TT1_def TT_TT1 assm2_assms(3) assms(2) case_assm2 tt_prefix_concat tt_prefix_imp_prefix_subset)
      obtain \<rho>' where \<rho>'_assms: "\<rho>' \<in> tocks UNIV" "\<rho>2 = \<rho>' \<or> (\<exists>Y. \<rho>2 = \<rho>' @ [[Y]\<^sub>R])"
        using case_assm2 assm2_assms(1) tt_prefix_tocks by blast
      then show "\<rho>2 \<in> P \<box>\<^sub>C Q"
      proof auto
        assume case_assm3: "\<rho>2 = \<rho>'"
        then show "\<rho>' \<in> P \<box>\<^sub>C Q"
          using \<rho>2_in_P \<rho>2_in_Q case_assm3 \<rho>'_assms(1) unfolding ExtChoiceTT_def apply auto
          apply (rule_tac x="\<rho>'" in bexI, auto)
          apply (rule_tac x="[]" in exI, auto)
          apply (rule_tac x="[]" in exI, auto)
          done
      next
        fix Y
        assume case_assm3: "\<rho>2 = \<rho>' @ [[Y]\<^sub>R]"
        then show "\<rho>' @ [[Y]\<^sub>R] \<in> P \<box>\<^sub>C Q"
          using \<rho>2_in_P \<rho>2_in_Q \<rho>'_assms(1) unfolding ExtChoiceTT_def apply auto
          apply (rule_tac x="\<rho>'" in bexI, auto)
          apply (rule_tac x="[[Y]\<^sub>R]" in exI, auto)
          apply (rule_tac x="[[Y]\<^sub>R]" in exI, auto)
          by (metis butlast_append butlast_snoc tt_prefix_concat tt_prefix_decompose end_refusal_notin_tocks)
      qed
    next
      fix \<rho>2'
      assume case_assm2: "\<rho>2' \<le>\<^sub>C s"
      assume case_assm3: "\<rho>2 = \<sigma>' @ \<rho>2'"
      have in_P: "\<sigma>' @ \<rho>2' \<in> P"
        using TT1_def TT_TT1 \<rho>2_assms(1) assm2_assms(2) assms(1) case_assm case_assm3 tt_prefix_imp_prefix_subset by blast
      show "\<sigma>' @ \<rho>2' \<in> P \<box>\<^sub>C Q"
      proof (cases "\<exists>X. \<rho>2' = [[X]\<^sub>R]", auto)
        fix X
        assume case_assm4: "\<rho>2' = [[X]\<^sub>R]"
        then have case_assm5: "s = [[X]\<^sub>R]"
          using case_assm2
        proof -
          have "ttWF s"
            using TT_wf assm2_assms(1) assm2_assms(2) assms(1) tocks_append_wf2 by fastforce
          then show "\<rho>2' = [[X]\<^sub>R] \<Longrightarrow> \<rho>2' \<le>\<^sub>C s \<Longrightarrow> s = [[X]\<^sub>R]"
            apply (cases s rule:ttWF.cases, auto, insert assm2_assms(1) assm2_assms(4))
            apply (erule_tac x="\<sigma>' @ [[X]\<^sub>R, [Tock]\<^sub>E]" in ballE, auto simp add: tt_prefix_same_front)
            using tt_prefix_antisym tt_prefix_concat apply blast
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
            using tt_prefix_subset_same_front[where r=\<sigma>'] by auto
          then show "\<sigma>' @ [[{e\<in>X. e \<noteq> Tock}]\<^sub>R] \<in> Q"
            using calculation TT1_def TT_TT1 assms(2) by blast
        qed
        then show "\<sigma>' @ [[X]\<^sub>R] \<in> P \<box>\<^sub>C Q"
          unfolding ExtChoiceTT_def apply auto
          apply (rule_tac x="\<sigma>'" in bexI, simp_all add: assm2_assms(1))
          apply (rule_tac x="[[X]\<^sub>R]" in exI, insert in_P case_assm4, simp)
          apply (rule_tac x="[[{e\<in>X. e \<noteq> Tock}]\<^sub>R]" in exI, insert assm2_assms(4) case_assm5, auto)
          by (metis (no_types, lifting) butlast_append butlast_snoc tt_prefix_concat tt_prefix_decompose end_refusal_notin_tocks)
      next
        have \<sigma>'_in_Q: "\<sigma>' \<in> Q"
          using TT1_def TT_TT1 assm2_assms(3) assms(2) tt_prefix_concat tt_prefix_imp_prefix_subset by blast
        then show "\<forall>X. \<rho>2' \<noteq> [[X]\<^sub>R] \<Longrightarrow> \<sigma>' @ \<rho>2' \<in> P \<box>\<^sub>C Q"
           unfolding ExtChoiceTT_def apply auto
           apply (rule_tac x="\<sigma>'" in bexI, simp_all add: assm2_assms(1))
           apply (rule_tac x="\<rho>2'" in exI, simp add: in_P)
           apply (rule_tac x="[]" in exI, auto)
           using \<rho>2_assms(1) assm2_assms(4) case_assm case_assm3 tt_prefix_trans by blast
       qed
     qed
   next
    assume case_assm: "\<sigma> = \<sigma>' @ t"
    then have \<sigma>_in_Q: "\<sigma> \<in> Q"
      using assm2_assms(3) by blast
    have \<rho>2_in_Q: "\<rho>2 \<in> Q"
      using TT1_def TT_TT1 \<rho>2_assms(1) \<sigma>_in_Q assms(2) tt_prefix_imp_prefix_subset by blast
    have "\<rho>2 \<le>\<^sub>C \<sigma>' \<or> (\<exists> \<rho>2'. \<rho>2 = \<sigma>' @ \<rho>2' \<and> \<rho>2' \<le>\<^sub>C t)"
      using \<rho>2_assms(1) case_assm tt_prefix_append_split by blast
    then show "\<rho>2 \<in> P \<box>\<^sub>C Q"
    proof auto
      assume case_assm2: "\<rho>2 \<le>\<^sub>C \<sigma>'"
      have \<rho>2_in_P: "\<rho>2 \<in> P"
        by (meson TT1_def TT_TT1 assm2_assms(2) assms(1) case_assm2 tt_prefix_concat tt_prefix_imp_prefix_subset)
      obtain \<rho>' where \<rho>'_assms: "\<rho>' \<in> tocks UNIV" "\<rho>2 = \<rho>' \<or> (\<exists>Y. \<rho>2 = \<rho>' @ [[Y]\<^sub>R])"
        using case_assm2 assm2_assms(1) tt_prefix_tocks by blast
      then show "\<rho>2 \<in> P \<box>\<^sub>C Q"
      proof auto
        assume case_assm3: "\<rho>2 = \<rho>'"
        then show "\<rho>' \<in> P \<box>\<^sub>C Q"
          using \<rho>2_in_P \<rho>2_in_Q case_assm3 \<rho>'_assms(1) unfolding ExtChoiceTT_def apply auto
          apply (rule_tac x="\<rho>'" in bexI, auto)
          apply (rule_tac x="[]" in exI, auto)
          apply (rule_tac x="[]" in exI, auto)
          done
      next
        fix Y
        assume case_assm3: "\<rho>2 = \<rho>' @ [[Y]\<^sub>R]"
        then show "\<rho>' @ [[Y]\<^sub>R] \<in> P \<box>\<^sub>C Q"
          using \<rho>2_in_P \<rho>2_in_Q \<rho>'_assms(1) unfolding ExtChoiceTT_def apply auto
          apply (rule_tac x="\<rho>'" in bexI, auto)
          apply (rule_tac x="[[Y]\<^sub>R]" in exI, auto)
          apply (rule_tac x="[[Y]\<^sub>R]" in exI, auto)
          by (metis butlast_append butlast_snoc tt_prefix_concat tt_prefix_decompose end_refusal_notin_tocks)
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
          have "ttWF t"
            using TT_wf assm2_assms(1) assm2_assms(3) assms(2) tocks_append_wf2 by fastforce
          then show "\<rho>2' = [[X]\<^sub>R] \<Longrightarrow> \<rho>2' \<le>\<^sub>C t \<Longrightarrow> t = [[X]\<^sub>R]"
            apply (cases t rule:ttWF.cases, auto, insert assm2_assms(1) assm2_assms(5))
            apply (erule_tac x="\<sigma>' @ [[X]\<^sub>R, [Tock]\<^sub>E]" in ballE, auto simp add: tt_prefix_same_front)
            using tt_prefix_antisym tt_prefix_concat apply blast
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
            using tt_prefix_subset_same_front[where r=\<sigma>'] by auto
          then show "\<sigma>' @ [[{e\<in>X. e \<noteq> Tock}]\<^sub>R] \<in> P"
            using calculation TT1_def TT_TT1 assms(1) by blast
        qed
        then show "\<sigma>' @ [[X]\<^sub>R] \<in> P \<box>\<^sub>C Q"
          unfolding ExtChoiceTT_def apply auto
          apply (rule_tac x="\<sigma>'" in bexI, simp_all add: assm2_assms(1))
          apply (rule_tac x="[[{e\<in>X. e \<noteq> Tock}]\<^sub>R]" in exI, insert assm2_assms(4) case_assm5, auto)
          apply (rule_tac x="[[X]\<^sub>R]" in exI, insert in_Q case_assm4 assm2_assms(5), auto)
          by (metis (no_types, lifting) butlast_append butlast_snoc tt_prefix_concat tt_prefix_decompose end_refusal_notin_tocks)
      next
        have \<sigma>'_in_P: "\<sigma>' \<in> P"
          using TT1_def TT_TT1 assm2_assms(2) assms(1) tt_prefix_concat tt_prefix_imp_prefix_subset by blast
        then show "\<forall>X. \<rho>2' \<noteq> [[X]\<^sub>R] \<Longrightarrow> \<sigma>' @ \<rho>2' \<in> P \<box>\<^sub>C Q"
           unfolding ExtChoiceTT_def apply auto
           apply (rule_tac x="\<sigma>'" in bexI, simp_all add: assm2_assms(1))
           apply (rule_tac x="[]" in exI, auto)
           apply (rule_tac x="\<rho>2'" in exI, simp add: in_Q)
           using \<rho>2_assms(1) assm2_assms(5) case_assm case_assm3 tt_prefix_trans by blast
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
    unfolding ExtChoiceTT_def by blast
  then show "\<rho> \<in>  P \<box>\<^sub>C Q"
  proof auto
    assume case_assm: "\<rho>2 = \<rho>2' @ t2"
    have \<rho>_wf: "ttWF \<rho>"
      using TT1_def TT_TT1 TT_wf \<rho>2_assms(2) \<rho>2_split(3) assms(2) case_assm tt_subset_imp_prefix_subset by blast
    then obtain \<rho>' \<rho>'' where \<rho>'_\<rho>''_assms:
      "\<rho> = \<rho>' @ \<rho>''"
      "\<rho>' \<in> tocks UNIV"
      "\<forall>t\<in>tocks UNIV. t \<le>\<^sub>C \<rho>' @ \<rho>'' \<longrightarrow> t \<le>\<^sub>C \<rho>'"
      using split_tocks_longest by blast
    then have \<rho>'_\<rho>''_tt_subset: "\<rho>' \<subseteq>\<^sub>C \<rho>2' \<and> \<rho>'' \<subseteq>\<^sub>C t2"
      using TT_wf \<rho>_wf \<rho>2_assms(2) \<rho>2_split(1) \<rho>2_split(3) \<rho>2_split(5) assms(2) case_assm tt_subset_longest_tocks by blast
    then have \<rho>'_in_P_Q: "\<rho>' \<in> P \<and> \<rho>' \<in> Q"
      by (meson TT_TT1 TT_defs(3) \<rho>2_split(2) \<rho>2_split(3) assms(1) assms(2) tt_prefix_concat tt_prefix_subset_tt_prefix_trans tt_subset_imp_prefix_subset)
    show "\<rho> \<in> P \<box>\<^sub>C Q"
    proof (cases "\<exists> X. t2 = [[X]\<^sub>R]")
      assume case_assm2: "\<exists> X. t2 = [[X]\<^sub>R]"
      then obtain X where t2_def: "t2 = [[X]\<^sub>R]"
        by auto
      then have "\<exists> Y. Y \<subseteq> X \<and> \<rho>'' = [[Y]\<^sub>R]"
        using \<rho>'_\<rho>''_tt_subset apply (simp, induct \<rho>'' t2 rule:tt_subset.induct, simp_all)
        using tt_subset_same_length by force
      then obtain Y where Y_assms: "Y \<subseteq> X \<and> \<rho>'' = [[Y]\<^sub>R]"
        by auto
      then obtain Z where Z_assms: "s2 = [[Z]\<^sub>R] \<and> (\<forall>e. (e \<in> X) = (e \<in> Z) \<or> e = Tock)"
        using t2_def \<rho>2_split(7) by blast
      then have "{e. e \<in> Y \<and> e \<noteq> Tock} \<subseteq> Z"
        using Y_assms by blast
      then have 1: "\<rho>' @ [[{e. e \<in> Y \<and> e \<noteq> Tock}]\<^sub>R] \<subseteq>\<^sub>C \<rho>2' @ [[Z]\<^sub>R]"
        by (simp add: \<rho>'_\<rho>''_tt_subset tt_subset_combine)
      have 2: "\<rho>' @ [[Y]\<^sub>R] \<subseteq>\<^sub>C \<rho>2' @ [[X]\<^sub>R]"
        using Y_assms \<rho>'_\<rho>''_assms(1) \<rho>2_assms(2) case_assm t2_def by blast
      have 3: "\<rho>' @ [[{e. e \<in> Y \<and> e \<noteq> Tock}]\<^sub>R] \<in> P"
        using "1" TT1_def TT_TT1 Z_assms \<rho>2_split(2) assms(1) tt_subset_imp_prefix_subset by blast
      have 4: "\<rho>' @ [[Y]\<^sub>R] \<in> Q"
        using "2" TT1_def TT_TT1 \<rho>2_split(3) assms(2) tt_subset_imp_prefix_subset t2_def by blast
      then show "\<rho> \<in> P \<box>\<^sub>C Q"
        unfolding ExtChoiceTT_def apply auto
        apply (rule_tac x="\<rho>'" in bexI, auto simp add: \<rho>'_\<rho>''_assms)
        apply (rule_tac x="[[{e. e \<in> Y \<and> e \<noteq> Tock}]\<^sub>R]" in exI, auto simp add: 3)
        apply (rule_tac x="[[Y]\<^sub>R]" in exI, auto simp add: 4 Y_assms)
        apply (metis (no_types, lifting) butlast_append butlast_snoc tt_prefix_concat tt_prefix_decompose end_refusal_notin_tocks)
        by (simp add: Y_assms \<rho>'_\<rho>''_assms(3))
    next
      assume "\<nexists>X. t2 = [[X]\<^sub>R]"
      then have "\<nexists>X. \<rho>'' = [[X]\<^sub>R]"
        using \<rho>'_\<rho>''_tt_subset by (auto, cases t2 rule:ttWF.cases, auto)
      then show "\<rho> \<in> P \<box>\<^sub>C Q"
        unfolding ExtChoiceTT_def apply auto
        apply (rule_tac x="\<rho>'" in bexI, auto simp add: \<rho>'_\<rho>''_assms)
        apply (rule_tac x="[]" in exI, auto simp add: \<rho>'_in_P_Q)
        apply (rule_tac x="\<rho>''" in exI, auto)
        using TT1_def TT_TT1 \<rho>'_\<rho>''_assms(1) \<rho>2_assms(2) \<rho>2_split(3) assms(2) case_assm tt_subset_imp_prefix_subset apply blast
        using \<rho>'_\<rho>''_assms(3) by blast
    qed
  next
    assume case_assm: "\<rho>2 = \<rho>2' @ s2"
    have \<rho>_wf: "ttWF \<rho>"
      by (metis TT_def ExtChoiceTT_wf assm1 assm2 assms(1) assms(2) tt_prefix_subset_ttWF)
    then obtain \<rho>' \<rho>'' where \<rho>'_\<rho>''_assms:
      "\<rho> = \<rho>' @ \<rho>''"
      "\<rho>' \<in> tocks UNIV"
      "\<forall>t\<in>tocks UNIV. t \<le>\<^sub>C \<rho>' @ \<rho>'' \<longrightarrow> t \<le>\<^sub>C \<rho>'"
      using split_tocks_longest by blast
    then have \<rho>'_\<rho>''_tt_subset: "\<rho>' \<subseteq>\<^sub>C \<rho>2' \<and> \<rho>'' \<subseteq>\<^sub>C s2"
      using TT_wf \<rho>2_assms(2) \<rho>2_split(1) \<rho>2_split(2) \<rho>2_split(4) \<rho>_wf assms(1) case_assm tt_subset_longest_tocks by blast
    then have \<rho>'_in_P_Q: "\<rho>' \<in> P \<and> \<rho>' \<in> Q"
      by (meson TT_TT1 TT_defs(3) \<rho>2_split(2) \<rho>2_split(3) assms(1) assms(2) tt_prefix_concat tt_prefix_subset_tt_prefix_trans tt_subset_imp_prefix_subset)
    show "\<rho> \<in> P \<box>\<^sub>C Q"
    proof (cases "\<exists> X. s2 = [[X]\<^sub>R]")
      assume case_assm2: "\<exists> X. s2 = [[X]\<^sub>R]"
      then obtain X where s2_def: "s2 = [[X]\<^sub>R]"
        by auto
      then have "\<exists> Y. Y \<subseteq> X \<and> \<rho>'' = [[Y]\<^sub>R]"
        using \<rho>'_\<rho>''_tt_subset apply (simp, induct \<rho>'' s2 rule:tt_subset.induct, simp_all)
        using tt_subset_same_length by force
      then obtain Y where Y_assms: "Y \<subseteq> X \<and> \<rho>'' = [[Y]\<^sub>R]"
        by auto
      then obtain Z where Z_assms: "t2 = [[Z]\<^sub>R] \<and> (\<forall>e. (e \<in> X) = (e \<in> Z) \<or> e = Tock)"
        using s2_def \<rho>2_split(6) by blast
      then have "{e. e \<in> Y \<and> e \<noteq> Tock} \<subseteq> Z"
        using Y_assms by blast
      then have 1: "\<rho>' @ [[{e. e \<in> Y \<and> e \<noteq> Tock}]\<^sub>R] \<subseteq>\<^sub>C \<rho>2' @ [[Z]\<^sub>R]"
        by (simp add: \<rho>'_\<rho>''_tt_subset tt_subset_combine)
      have 2: "\<rho>' @ [[Y]\<^sub>R] \<subseteq>\<^sub>C \<rho>2' @ [[X]\<^sub>R]"
        using Y_assms \<rho>'_\<rho>''_assms(1) \<rho>2_assms(2) case_assm s2_def by blast
      have 3: "\<rho>' @ [[{e. e \<in> Y \<and> e \<noteq> Tock}]\<^sub>R] \<in> Q"
        using "1" TT1_def TT_TT1 Z_assms \<rho>2_split(3) assms(2) tt_subset_imp_prefix_subset by blast
      have 4: "\<rho>' @ [[Y]\<^sub>R] \<in> P"
        using "2" TT1_def TT_TT1 \<rho>2_split(2) assms(1) tt_subset_imp_prefix_subset s2_def by blast
      then show "\<rho> \<in> P \<box>\<^sub>C Q"
        unfolding ExtChoiceTT_def apply auto
        apply (rule_tac x="\<rho>'" in bexI, auto simp add: \<rho>'_\<rho>''_assms)
        apply (rule_tac x="[[Y]\<^sub>R]" in exI, auto simp add: 4 Y_assms)
        apply (rule_tac x="[[{e. e \<in> Y \<and> e \<noteq> Tock}]\<^sub>R]" in exI, auto simp add: 3)
        using Y_assms \<rho>'_\<rho>''_assms(3) apply blast
        by (metis (no_types, lifting) butlast_append butlast_snoc tt_prefix_concat tt_prefix_decompose end_refusal_notin_tocks)
    next
      assume "\<nexists>X. s2 = [[X]\<^sub>R]"
      then have "\<nexists>X. \<rho>'' = [[X]\<^sub>R]"
        using \<rho>'_\<rho>''_tt_subset by (auto, cases s2 rule:ttWF.cases, auto)
      then show "\<rho> \<in> P \<box>\<^sub>C Q"
        unfolding ExtChoiceTT_def apply auto
        apply (rule_tac x="\<rho>'" in bexI, auto simp add: \<rho>'_\<rho>''_assms)
        apply (rule_tac x="\<rho>''" in exI, auto)
        using TT1_def TT_TT1 \<rho>'_\<rho>''_assms(1) \<rho>2_assms(2) \<rho>2_split(2) assms(1) case_assm tt_subset_imp_prefix_subset apply blast
        apply (rule_tac x="[]" in exI, auto simp add: \<rho>'_in_P_Q)
        using \<rho>'_\<rho>''_assms(3) by blast
    qed
  qed
qed

lemma TT2w_ExtChoice:
  assumes "TT P" "TT Q"
  shows "TT2w (P \<box>\<^sub>C Q)"
  unfolding TT2w_def
proof auto
  fix \<rho> :: "'a ttobs list"
  fix X Y :: "'a ttevent set"
  assume assm1: "\<rho> @ [[X]\<^sub>R] \<in> P \<box>\<^sub>C Q"
  assume assm2: "Y \<inter> {e. e \<noteq> Tock \<and> \<rho> @ [[e]\<^sub>E] \<in> P \<box>\<^sub>C Q \<or> e = Tock \<and> \<rho> @ [[X]\<^sub>R, [e]\<^sub>E] \<in> P \<box>\<^sub>C Q} = {}"
  from assm1 have "ttWF \<rho>"
    by (metis TT_def ExtChoiceTT_wf assms(1) assms(2) tt_prefix_concat tt_prefix_imp_prefix_subset tt_prefix_subset_ttWF)
  then obtain \<rho>' \<rho>'' where \<rho>_split: "\<rho>'\<in>tocks UNIV \<and> \<rho> = \<rho>' @ \<rho>'' \<and> (\<forall>t'\<in>tocks UNIV. t' \<le>\<^sub>C \<rho> \<longrightarrow> t' \<le>\<^sub>C \<rho>')"
    using split_tocks_longest by blast
  have \<rho>'_in_P_Q: "\<rho>' \<in> P \<and> \<rho>' \<in> Q"
    using assm1 unfolding ExtChoiceTT_def apply auto
    apply (metis TT1_def TT_TT1 \<rho>_split assms(1) tt_prefix_concat tt_prefix_imp_prefix_subset)
    apply (metis TT1_def TT_TT1 \<rho>_split append.assoc assms(2) tt_prefix_concat tt_prefix_imp_prefix_subset)
    apply (metis TT1_def TT_TT1 \<rho>_split append.assoc assms(1) tt_prefix_concat tt_prefix_imp_prefix_subset)
    by (metis TT1_def TT_TT1 \<rho>_split assms(2) tt_prefix_concat tt_prefix_imp_prefix_subset)
  have set1: "{e. e \<noteq> Tock \<and> \<rho> @ [[e]\<^sub>E] \<in> P \<box>\<^sub>C Q} = {e. e \<noteq> Tock \<and> \<rho> @ [[e]\<^sub>E] \<in> P} \<union> {e. e \<noteq> Tock \<and> \<rho> @ [[e]\<^sub>E] \<in> Q}"
  proof auto
    fix x :: "'a ttevent"
    assume "\<rho> @ [[x]\<^sub>E] \<in> P \<box>\<^sub>C Q"
    then have "\<rho> @ [[x]\<^sub>E] \<in> P \<or> \<rho> @ [[x]\<^sub>E] \<in> Q"
      unfolding ExtChoiceTT_def by auto
    then show "\<rho> @ [[x]\<^sub>E] \<notin> Q \<Longrightarrow> \<rho> @ [[x]\<^sub>E] \<in> P"
      by auto
  next
    fix x :: "'a ttevent"
    assume "x \<noteq> Tock" "\<rho> @ [[x]\<^sub>E] \<in> P"
    then show "\<rho> @ [[x]\<^sub>E] \<in> P \<box>\<^sub>C Q"
      unfolding ExtChoiceTT_def apply auto
      apply (rule_tac x="\<rho>'" in bexI, simp_all add: \<rho>_split)
      apply (rule_tac x="\<rho>'' @ [[x]\<^sub>E]" in exI, simp_all)
      apply (rule_tac x="[]" in exI, simp add: \<rho>'_in_P_Q)
      apply (auto, case_tac "\<rho>''' \<le>\<^sub>C \<rho>' @ \<rho>''")
      using \<rho>_split apply blast
      by (metis append.assoc append_Cons append_Nil tt_prefix_notfront_is_whole ttevent.exhaust end_event_notin_tocks mid_tick_notin_tocks)
  next
    fix x :: "'a ttevent"
    assume "x \<noteq> Tock" "\<rho> @ [[x]\<^sub>E] \<in> Q"
    then show "\<rho> @ [[x]\<^sub>E] \<in> P \<box>\<^sub>C Q"
      unfolding ExtChoiceTT_def apply auto
      apply (rule_tac x="\<rho>'" in bexI, simp_all add: \<rho>_split)
      apply (rule_tac x="[]" in exI, simp add: \<rho>'_in_P_Q)
      apply (auto, case_tac "\<rho>''' \<le>\<^sub>C \<rho>' @ \<rho>''")
      using \<rho>_split apply blast
      by (metis append.assoc append_Cons append_Nil tt_prefix_notfront_is_whole ttevent.exhaust end_event_notin_tocks mid_tick_notin_tocks)
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
      unfolding ExtChoiceTT_def by auto
    have in_tocks: "\<rho>' @ [[X]\<^sub>R, [Tock]\<^sub>E] \<in> tocks UNIV"
      by (simp add: \<rho>_split tocks.empty_in_tocks tocks.tock_insert_in_tocks tocks_append_tocks)
    then have r_def: "r = \<rho>' @ [[X]\<^sub>R, [Tock]\<^sub>E]"
      using tt_prefix_refl rst_assms(4) rst_assms(5) rst_assms(6) self_extension_tt_prefix by fastforce
    then have "r \<in> P \<and> r \<in> Q"
      by (smt TT1_def TT_TT1 rst_assms assms(1) assms(2) tt_prefix_concat tt_prefix_imp_prefix_subset in_tocks rst_assms(4))
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
      unfolding ExtChoiceTT_def by auto
    have in_tocks: "\<rho>' @ [[X]\<^sub>R, [Tock]\<^sub>E] \<in> tocks UNIV"
      by (simp add: \<rho>_split tocks.empty_in_tocks tocks.tock_insert_in_tocks tocks_append_tocks)
    then have r_def: "r = \<rho>' @ [[X]\<^sub>R, [Tock]\<^sub>E]"
      using tt_prefix_refl rst_assms(4) rst_assms(5) rst_assms(6) self_extension_tt_prefix by fastforce
    then have "r \<in> P \<and> r \<in> Q"
      by (smt TT1_def TT_TT1 rst_assms assms(1) assms(2) tt_prefix_concat tt_prefix_imp_prefix_subset in_tocks rst_assms(4))
    then show "\<rho> @ [[X]\<^sub>R, [Tock]\<^sub>E] \<in> Q"
      by (simp add: r_def \<rho>_split case_assms(2))
  next
    assume case_assms: "\<rho> @ [[X]\<^sub>R, [Tock]\<^sub>E] \<in> P" "\<rho>'' = []" "\<rho> @ [[X]\<^sub>R, [Tock]\<^sub>E] \<in> Q"
    then have "\<rho>' @ [[X]\<^sub>R, [Tock]\<^sub>E] \<in> P \<and> \<rho>' @ [[X]\<^sub>R, [Tock]\<^sub>E] \<in> Q"
      by (simp add: \<rho>_split)
    also have "\<rho>' @ [[X]\<^sub>R, [Tock]\<^sub>E] \<in> tocks UNIV"
      by (simp add: \<rho>_split tocks.empty_in_tocks tocks.tock_insert_in_tocks tocks_append_tocks)
    then show "\<rho> @ [[X]\<^sub>R, [Tock]\<^sub>E] \<in> P \<box>\<^sub>C Q"
      unfolding ExtChoiceTT_def apply auto
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
      unfolding ExtChoiceTT_def by auto
  next
    assume \<rho>''_nonempty: "\<rho>'' \<noteq> []"
    assume in_P: "\<rho> @ [[X]\<^sub>R, [Tock]\<^sub>E] \<in> P"
    have full_notin_tocks: "\<rho>' @ \<rho>'' @ [[X]\<^sub>R, [Tock]\<^sub>E] \<notin> tocks UNIV"
        by (metis \<rho>''_nonempty \<rho>_split append.assoc tt_prefix_refl nontocks_append_tocks self_extension_tt_prefix tocks.empty_in_tocks tocks.tock_insert_in_tocks top_greatest)
    have "\<forall>x\<in>tocks UNIV. x \<le>\<^sub>C \<rho> @ [[X]\<^sub>R, [Tock]\<^sub>E] \<longrightarrow> x \<le>\<^sub>C \<rho>'"
    proof (auto simp add: \<rho>_split)
      fix x :: "'a ttobs list"
      assume x_in_tocks: "x \<in> tocks UNIV"
      assume "x \<le>\<^sub>C \<rho>' @ \<rho>'' @ [[X]\<^sub>R, [Tock]\<^sub>E]"
      also have "\<And> y. x \<le>\<^sub>C y @ [[X]\<^sub>R, [Tock]\<^sub>E] \<Longrightarrow> x \<le>\<^sub>C y \<or> x = y @ [[X]\<^sub>R] \<or> x = y @ [[X]\<^sub>R, [Tock]\<^sub>E]"
      proof -
        fix y
        show "x \<le>\<^sub>C y @ [[X]\<^sub>R, [Tock]\<^sub>E] \<Longrightarrow> x \<le>\<^sub>C y \<or> x = y @ [[X]\<^sub>R] \<or> x = y @ [[X]\<^sub>R, [Tock]\<^sub>E]"
          using tt_prefix.elims(2) tt_prefix_antisym by (induct x y rule:tt_prefix.induct, auto, fastforce)
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
      unfolding ExtChoiceTT_def apply auto
      apply (rule_tac x="\<rho>'" in bexI, auto simp add: \<rho>_split)
      apply (rule_tac x="\<rho>'' @ [[X]\<^sub>R, [Tock]\<^sub>E]" in exI, insert \<rho>_split in_P, auto)
      apply (rule_tac x="[]" in exI, auto simp add: \<rho>'_in_P_Q)
      done
  next
    assume \<rho>''_nonempty: "\<rho>'' \<noteq> []"
    assume in_Q: "\<rho> @ [[X]\<^sub>R, [Tock]\<^sub>E] \<in> Q"
    have full_notin_tocks: "\<rho>' @ \<rho>'' @ [[X]\<^sub>R, [Tock]\<^sub>E] \<notin> tocks UNIV"
        by (metis \<rho>''_nonempty \<rho>_split append.assoc tt_prefix_refl nontocks_append_tocks self_extension_tt_prefix tocks.empty_in_tocks tocks.tock_insert_in_tocks top_greatest)
    have "\<forall>x\<in>tocks UNIV. x \<le>\<^sub>C \<rho> @ [[X]\<^sub>R, [Tock]\<^sub>E] \<longrightarrow> x \<le>\<^sub>C \<rho>'"
    proof (auto simp add: \<rho>_split)
      fix x :: "'a ttobs list"
      assume x_in_tocks: "x \<in> tocks UNIV"
      assume "x \<le>\<^sub>C \<rho>' @ \<rho>'' @ [[X]\<^sub>R, [Tock]\<^sub>E]"
      also have "\<And> y. x \<le>\<^sub>C y @ [[X]\<^sub>R, [Tock]\<^sub>E] \<Longrightarrow> x \<le>\<^sub>C y \<or> x = y @ [[X]\<^sub>R] \<or> x = y @ [[X]\<^sub>R, [Tock]\<^sub>E]"
      proof -
        fix y
        show "x \<le>\<^sub>C y @ [[X]\<^sub>R, [Tock]\<^sub>E] \<Longrightarrow> x \<le>\<^sub>C y \<or> x = y @ [[X]\<^sub>R] \<or> x = y @ [[X]\<^sub>R, [Tock]\<^sub>E]"
          using tt_prefix.elims(2) tt_prefix_antisym by (induct x y rule:tt_prefix.induct, auto, fastforce)
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
      unfolding ExtChoiceTT_def apply auto
      apply (rule_tac x="\<rho>'" in bexI, auto simp add: \<rho>_split)
      apply (rule_tac x="[]" in exI, auto simp add: \<rho>'_in_P_Q)
      apply (insert \<rho>_split in_Q, auto)
      done
  qed
  thm set1 set2 set3
  have in_P_or_Q: "\<rho> @ [[X]\<^sub>R] \<in> P \<or> \<rho> @ [[X]\<^sub>R] \<in> Q"
    using assm1 unfolding ExtChoiceTT_def by auto
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
      using TT2w_def TT_def assms(1) assms(2) in_P_or_Q by auto
    then show "\<rho> @ [[X \<union> Y]\<^sub>R] \<in> P \<box>\<^sub>C Q"
      unfolding ExtChoiceTT_def apply auto
      apply (rule_tac x="\<rho>'" in bexI, auto simp add: \<rho>_split)
      apply (rule_tac x="\<rho>'' @ [[X \<union> Y]\<^sub>R]" in exI, auto)
      apply (rule_tac x="[]" in exI, auto simp add: \<rho>_split \<rho>'_in_P_Q case_assm)
      apply (metis \<rho>_split append.assoc tt_prefix_notfront_is_whole end_refusal_notin_tocks)
      apply (rule_tac x="\<rho>'" in bexI, auto simp add: \<rho>_split)
      apply (rule_tac x="[]" in exI, auto simp add: \<rho>_split \<rho>'_in_P_Q case_assm)
      apply (metis \<rho>_split append.assoc tt_prefix_notfront_is_whole end_refusal_notin_tocks)
      done
  next
    assume case_assm: "\<rho>'' = []"
    have "\<rho> @ [[{e. e \<in> X \<and> e \<noteq> Tock}]\<^sub>R] \<lesssim>\<^sub>C \<rho> @ [[X]\<^sub>R]"
      by (induct \<rho>, auto, case_tac a, auto)
    then have "\<rho> @ [[{e. e \<in> X \<and> e \<noteq> Tock}]\<^sub>R] \<in> P \<box>\<^sub>C Q"
      using TT1_ExtChoice TT1_def assm1 assms(1) assms(2) by blast
    then have "\<rho>' @ [[{e. e \<in> X \<and> e \<noteq> Tock}]\<^sub>R] \<in> P \<box>\<^sub>C Q"
      by (simp add: \<rho>_split case_assm)
    then have in_P_and_Q: "\<rho>' @ [[{e. e \<in> X \<and> e \<noteq> Tock}]\<^sub>R] \<in> P \<and> \<rho>' @ [[{e. e \<in> X \<and> e \<noteq> Tock}]\<^sub>R] \<in> Q"
      unfolding ExtChoiceTT_def
    proof auto
      fix \<rho> \<sigma> \<tau> :: "'a ttobs list"
      assume case_assm1: "\<rho> \<in> tocks UNIV"
      assume case_assm2: "\<forall>\<rho>'\<in>tocks UNIV. \<rho>' \<le>\<^sub>C \<rho> @ \<sigma> \<longrightarrow> \<rho>' \<le>\<^sub>C \<rho>"
      assume case_assm3: "\<rho>' @ [[{e \<in> X. e \<noteq> Tock}]\<^sub>R] = \<rho> @ \<sigma>"
      assume case_assm4: "\<forall>X. \<sigma> = [[X]\<^sub>R] \<longrightarrow> (\<exists>Y. \<tau> = [[Y]\<^sub>R] \<and> (\<forall>e. (e \<in> X) = (e \<in> Y) \<or> e = Tock))"
      assume case_assm5: "\<rho> @ \<tau> \<in> Q"
      have \<rho>_def: "\<rho> = \<rho>'"
        by (metis (no_types, lifting) \<rho>_split butlast_append butlast_snoc case_assm1 case_assm2 case_assm3 tt_prefix_antisym tt_prefix_concat end_refusal_notin_tocks)
      then have \<sigma>_def: "\<sigma> = [[{e \<in> X. e \<noteq> Tock}]\<^sub>R]"
        using case_assm3 by blast
      obtain Y where Y_assms: "\<tau> = [[Y]\<^sub>R]" "\<forall>e. (e \<in> X) = (e \<in> Y) \<or> e = Tock"
        using case_assm4 by (erule_tac x="{e. e \<in> X \<and> e \<noteq> Tock}" in allE, simp add: \<sigma>_def, auto)
      then have "\<rho>' @ [[{e \<in> X. e \<noteq> Tock}]\<^sub>R] \<lesssim>\<^sub>C \<rho>' @ [[Y]\<^sub>R]"
        by (induct \<rho>', auto, case_tac a, auto)
      then have "\<rho>' @ [[{e \<in> X. e \<noteq> Tock}]\<^sub>R] \<in> Q"
        using TT1_def TT_TT1 Y_assms(1) \<rho>_def assms(2) case_assm5 by blast
      then show "\<rho> @ \<sigma> \<in> Q"
        by (simp add: case_assm3)
    next
      fix \<rho> \<sigma> \<tau> :: "'a ttobs list"
      assume case_assm1: "\<rho> \<in> tocks UNIV"
      assume case_assm2: "\<forall>\<rho>'\<in>tocks UNIV. \<rho>' \<le>\<^sub>C \<rho> @ \<tau> \<longrightarrow> \<rho>' \<le>\<^sub>C \<rho>"
      assume case_assm3: "\<rho>' @ [[{e \<in> X. e \<noteq> Tock}]\<^sub>R] = \<rho> @ \<tau>"
      assume case_assm4: "\<forall>X. \<tau> = [[X]\<^sub>R] \<longrightarrow> (\<exists>Y. \<sigma> = [[Y]\<^sub>R] \<and> (\<forall>e. (e \<in> X) = (e \<in> Y) \<or> e = Tock))"
      assume case_assm5: "\<rho> @ \<sigma> \<in> P"
      have \<rho>_def: "\<rho> = \<rho>'"
        by (metis (no_types, lifting) \<rho>_split butlast_append butlast_snoc case_assm1 case_assm2 case_assm3 tt_prefix_antisym tt_prefix_concat end_refusal_notin_tocks)
      then have \<sigma>_def: "\<tau> = [[{e \<in> X. e \<noteq> Tock}]\<^sub>R]"
        using case_assm3 by blast
      obtain Y where Y_assms: "\<sigma> = [[Y]\<^sub>R]" "\<forall>e. (e \<in> X) = (e \<in> Y) \<or> e = Tock"
        using case_assm4 by (erule_tac x="{e. e \<in> X \<and> e \<noteq> Tock}" in allE, simp add: \<sigma>_def, auto)
      then have "\<rho>' @ [[{e \<in> X. e \<noteq> Tock}]\<^sub>R] \<lesssim>\<^sub>C \<rho>' @ [[Y]\<^sub>R]"
        by (induct \<rho>', auto, case_tac a, auto)
      then have "\<rho>' @ [[{e \<in> X. e \<noteq> Tock}]\<^sub>R] \<in> P"
        using TT1_def TT_TT1 Y_assms(1) \<rho>_def assms(1) case_assm5 by blast
      then show "\<rho> @ \<tau> \<in> P"
        by (simp add: case_assm3)
    qed
    have notocks_assm2: "{e. e \<in> Y \<and> e \<noteq> Tock} \<inter> {e. e \<noteq> Tock \<and> \<rho> @ [[e]\<^sub>E] \<in> P \<or> e = Tock \<and> \<rho> @ [[{e. e \<in> X \<and> e \<noteq> Tock}]\<^sub>R, [e]\<^sub>E] \<in> P} = {} 
        \<and> {e. e \<in> Y \<and> e \<noteq> Tock} \<inter> {e. e \<noteq> Tock \<and> \<rho> @ [[e]\<^sub>E] \<in> Q \<or> e = Tock \<and> \<rho> @ [[{e. e \<in> X \<and> e \<noteq> Tock}]\<^sub>R, [e]\<^sub>E] \<in> Q} = {}"
      using set1 assm2 by blast
    have TT2w_P_Q: "TT2w P \<and> TT2w Q"
      by (simp add: TT_TT2w assms(1) assms(2))
    then have notock_X_Y_in_P_Q: "\<rho> @ [[{e. e \<in> X \<union> Y \<and> e \<noteq> Tock}]\<^sub>R] \<in> P \<and> \<rho> @ [[{e. e \<in> X \<union> Y \<and> e \<noteq> Tock}]\<^sub>R] \<in> Q"
      unfolding TT2w_def
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
      using assm1 unfolding ExtChoiceTT_def by auto
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
            using TT2w_P_Q case_assm3 unfolding TT2w_def by auto
          also have "\<rho> @ [[{e \<in> X \<union> Y. e \<noteq> Tock}]\<^sub>R] \<in> Q"
            using notock_X_Y_in_P_Q by auto
          then show "\<rho> @ [[X \<union> Y]\<^sub>R] \<in> P \<box>\<^sub>C Q"
            unfolding ExtChoiceTT_def using calculation apply auto
            apply (rule_tac x="\<rho>'" in bexI, simp_all add: \<rho>_split case_assm)
            apply (rule_tac x="[[X \<union> Y]\<^sub>R]" in exI, simp_all)
            apply (rule_tac x="[[{e \<in> X \<union> Y. e \<noteq> Tock}]\<^sub>R]" in exI, auto)
            using tt_prefix_notfront_is_whole end_refusal_notin_tocks by blast+
        next
          assume case_assm5: "\<rho> @ [[X]\<^sub>R] \<in> Q"
          then have "\<rho> @ [[X \<union> Y]\<^sub>R] \<in> Q"
            using TT2w_P_Q case_assm4 unfolding TT2w_def by auto
          also have "\<rho> @ [[{e \<in> X \<union> Y. e \<noteq> Tock}]\<^sub>R] \<in> P"
            using notock_X_Y_in_P_Q by auto
          then show "\<rho> @ [[X \<union> Y]\<^sub>R] \<in> P \<box>\<^sub>C Q"
            unfolding ExtChoiceTT_def using calculation apply auto
            apply (rule_tac x="\<rho>'" in bexI, simp_all add: \<rho>_split case_assm)
            apply (rule_tac x="[[{e \<in> X \<union> Y. e \<noteq> Tock}]\<^sub>R]" in exI, auto)
            apply (rule_tac x="[[X \<union> Y]\<^sub>R]" in exI, simp_all)
            using tt_prefix_notfront_is_whole end_refusal_notin_tocks by blast+
        qed
      next
        assume case_assm3: "\<rho> @ [[X]\<^sub>R, [Tock]\<^sub>E] \<in> P"
        assume case_assm4: "Y \<inter> {e. e \<noteq> Tock \<and> \<rho> @ [[e]\<^sub>E] \<in> Q \<or> e = Tock \<and> \<rho> @ [[X]\<^sub>R, [e]\<^sub>E] \<in> Q} = {}"
        have TT1_P: "TT1 P"
          by (simp add: TT_TT1 assms(1))
        have "\<rho> @ [[X]\<^sub>R] \<lesssim>\<^sub>C \<rho> @ [[X]\<^sub>R, [Tock]\<^sub>E]"
          using tt_prefix_subset_same_front by fastforce
        then have in_P: "\<rho> @ [[X]\<^sub>R] \<in> P"
          using TT1_P case_assm3 unfolding TT1_def by auto 
        have TT3_P: "TT3 P"
          by (simp add: TT_TT3 assms(1))
        then have "Tock \<notin> X"
          using TT3_def TT3_end_tock \<rho>'_in_P_Q \<rho>_split case_assm case_assm3 by force
        then have in_Q: "\<rho> @ [[X]\<^sub>R] \<in> Q"
          using assm1 unfolding ExtChoiceTT_def
        proof auto
          fix r s t :: "'a ttobs list"
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
            by (metis "1" "4" "8" \<rho>_split append.right_neutral butlast_append butlast_snoc case_assm tt_prefix_antisym tt_prefix_concat end_refusal_notin_tocks)
          then have "s = [[X]\<^sub>R]"
            using "8" by blast
          then obtain Y where Y_assms: "t = [[Y]\<^sub>R]" "\<forall>e. (e \<in> X) = (e \<in> Y) \<or> e = Tock"
            using "6" by auto
          then have "\<rho> @ [[Y]\<^sub>R] \<in> Q"
            using "3" r_is_\<rho> by blast
          also have "\<rho> @ [[X]\<^sub>R] \<lesssim>\<^sub>C \<rho> @ [[Y]\<^sub>R]"
            by (metis "9" Y_assms(2) tt_prefix_subset.simps(2) tt_prefix_subset_refl tt_prefix_subset_same_front subsetI)
          then have "\<rho> @ [[X]\<^sub>R] \<in> Q"
            using TT1_def TT_TT1 assms(2) calculation by blast
          then show "r @ s \<in> Q"
            using "8" by auto
        qed
        then have "\<rho> @ [[X \<union> Y]\<^sub>R] \<in> Q"
          using TT2w_P_Q TT2w_def case_assm4 by blast
        then show "\<rho> @ [[X \<union> Y]\<^sub>R] \<in> P \<box>\<^sub>C Q"
          unfolding ExtChoiceTT_def using notock_X_Y_in_P_Q apply auto
          apply (rule_tac x="\<rho>'" in bexI, simp_all add: \<rho>_split case_assm)
          apply (rule_tac x="[[{e \<in> X \<union> Y. e \<noteq> Tock}]\<^sub>R]" in exI, auto)
          apply (rule_tac x="[[X \<union> Y]\<^sub>R]" in exI, simp_all)
          using tt_prefix_notfront_is_whole end_refusal_notin_tocks by blast+
      next
        assume case_assm3: "\<rho> @ [[X]\<^sub>R, [Tock]\<^sub>E] \<in> Q"
        assume case_assm4: "Y \<inter> {e. e \<noteq> Tock \<and> \<rho> @ [[e]\<^sub>E] \<in> P \<or> e = Tock \<and> \<rho> @ [[X]\<^sub>R, [e]\<^sub>E] \<in> P} = {}"
        have TT1_P: "TT1 Q"
          by (simp add: TT_TT1 assms(2))
        have "\<rho> @ [[X]\<^sub>R] \<lesssim>\<^sub>C \<rho> @ [[X]\<^sub>R, [Tock]\<^sub>E]"
          using tt_prefix_subset_same_front by fastforce
        then have in_P: "\<rho> @ [[X]\<^sub>R] \<in> Q"
          using TT1_P case_assm3 unfolding TT1_def by auto 
        have TT3_P: "TT3 Q"
          by (simp add: TT_TT3 assms(2))
        then have "Tock \<notin> X"
          using TT3_def TT3_end_tock \<rho>'_in_P_Q \<rho>_split case_assm case_assm3 by force
        then have in_P: "\<rho> @ [[X]\<^sub>R] \<in> P"
          using assm1 unfolding ExtChoiceTT_def
        proof auto
          fix r s t :: "'a ttobs list"
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
            by (metis "1" "5" "8" \<rho>_split append.right_neutral butlast_append butlast_snoc case_assm tt_prefix_antisym tt_prefix_concat end_refusal_notin_tocks)
          then have "t = [[X]\<^sub>R]"
            using "8" by blast
          then obtain Y where Y_assms: "s = [[Y]\<^sub>R]" "\<forall>e. (e \<in> X) = (e \<in> Y) \<or> e = Tock"
            using "7" by auto
          then have "\<rho> @ [[Y]\<^sub>R] \<in> P"
            using "2" r_is_\<rho> by blast
          also have "\<rho> @ [[X]\<^sub>R] \<lesssim>\<^sub>C \<rho> @ [[Y]\<^sub>R]"
            by (metis "9" Y_assms(2) tt_prefix_subset.simps(2) tt_prefix_subset_refl tt_prefix_subset_same_front subsetI)
          then have "\<rho> @ [[X]\<^sub>R] \<in> P"
            using TT1_def TT_TT1 assms(1) calculation by blast
          then show "r @ t \<in> P"
            using "8" by auto
        qed
        then have "\<rho> @ [[X \<union> Y]\<^sub>R] \<in> P"
          using TT2w_P_Q TT2w_def case_assm4 by blast
        then show "\<rho> @ [[X \<union> Y]\<^sub>R] \<in> P \<box>\<^sub>C Q"
          unfolding ExtChoiceTT_def using notock_X_Y_in_P_Q apply auto
          apply (rule_tac x="\<rho>'" in bexI, simp_all add: \<rho>_split case_assm)
          apply (rule_tac x="[[X \<union> Y]\<^sub>R]" in exI, simp_all)
          apply (rule_tac x="[[{e \<in> X \<union> Y. e \<noteq> Tock}]\<^sub>R]" in exI, auto)
          using tt_prefix_notfront_is_whole end_refusal_notin_tocks by blast+
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
        have "TT2w P"
          by (simp add: TT2w_P_Q)
        then have "\<rho> @ [[X \<union> Y]\<^sub>R] \<in> P"
          unfolding TT2w_def using case_assm3 assm2_expand by auto
        then show  "\<rho> @ [[X \<union> Y]\<^sub>R] \<in> P \<box>\<^sub>C Q"
          unfolding ExtChoiceTT_def using notock_X_Y_in_P_Q apply auto
          apply (rule_tac x="\<rho>'" in bexI, simp_all add: \<rho>_split case_assm)
          apply (rule_tac x="[[X \<union> Y]\<^sub>R]" in exI, simp_all)
          apply (rule_tac x="[[{e \<in> X \<union> Y. e \<noteq> Tock}]\<^sub>R]" in exI, auto)
          using tt_prefix_notfront_is_whole end_refusal_notin_tocks by blast+
      next
        assume  case_assm3: "\<rho> @ [[X]\<^sub>R] \<in> Q"
        have "TT2w Q"
          by (simp add: TT2w_P_Q)
        then have "\<rho> @ [[X \<union> Y]\<^sub>R] \<in> Q"
          unfolding TT2w_def using case_assm3 assm2_expand by auto
        then show  "\<rho> @ [[X \<union> Y]\<^sub>R] \<in> P \<box>\<^sub>C Q"
          unfolding ExtChoiceTT_def using notock_X_Y_in_P_Q apply auto
          apply (rule_tac x="\<rho>'" in bexI, simp_all add: \<rho>_split case_assm)
          apply (rule_tac x="[[{e \<in> X \<union> Y. e \<noteq> Tock}]\<^sub>R]" in exI, auto)
          apply (rule_tac x="[[X \<union> Y]\<^sub>R]" in exI, simp_all)
          using tt_prefix_notfront_is_whole end_refusal_notin_tocks by blast+
      qed
    qed
  qed
qed

lemma TT2_ExtChoice:
  assumes "TT P" "TT Q" "TT2 P" "TT2 Q"
  shows "TT2 (P \<box>\<^sub>C Q)"
  unfolding TT2_def
proof auto
  fix \<rho> \<sigma> X Y
  assume assm1: "\<rho> @ [X]\<^sub>R # \<sigma> \<in> P \<box>\<^sub>C Q"
  assume assm2: "Y \<inter> {e. e \<noteq> Tock \<and> \<rho> @ [[e]\<^sub>E] \<in> P \<box>\<^sub>C Q \<or> e = Tock \<and> \<rho> @ [[X]\<^sub>R, [e]\<^sub>E] \<in> P \<box>\<^sub>C Q} = {}"
  from assm1 have \<rho>_\<sigma>_wf: "ttWF (\<rho> @ [X]\<^sub>R # \<sigma>)"
    by (metis TT_def ExtChoiceTT_wf assms(1) assms(2))
  then obtain \<rho>' \<rho>'' where \<rho>_\<sigma>_split: "\<rho>'\<in>tocks UNIV \<and> \<rho> @ [X]\<^sub>R # \<sigma> = \<rho>' @ \<rho>'' \<and> (\<forall>t'\<in>tocks UNIV. t' \<le>\<^sub>C \<rho> @ [X]\<^sub>R # \<sigma> \<longrightarrow> t' \<le>\<^sub>C \<rho>')"
    using split_tocks_longest by blast
  then have \<rho>'_\<rho>''_wf: "ttWF (\<rho>' @ \<rho>'')"
    using \<rho>_\<sigma>_wf by auto  
  have \<rho>'_in_P_Q: "\<rho>' \<in> P \<and> \<rho>' \<in> Q"
    using assm1 unfolding ExtChoiceTT_def apply auto
    apply (metis TT1_def TT_TT1 \<rho>_\<sigma>_split assms(1) tt_prefix_concat tt_prefix_imp_prefix_subset)
    apply (metis TT1_def TT_TT1 \<rho>_\<sigma>_split assms(2) tt_prefix_concat tt_prefix_imp_prefix_subset)
    apply (metis TT1_def TT_TT1 \<rho>_\<sigma>_split assms(1) tt_prefix_concat tt_prefix_imp_prefix_subset)
    by (metis TT1_def TT_TT1 \<rho>_\<sigma>_split assms(2) tt_prefix_concat tt_prefix_imp_prefix_subset)
  have \<rho>'_cases: "\<rho>' \<le>\<^sub>C \<rho> \<or> (\<exists> \<sigma>'. \<rho>' = \<rho> @ [X]\<^sub>R # \<sigma>' \<and> \<sigma>' \<le>\<^sub>C \<sigma> \<and> \<sigma>' \<noteq> [])"
    using \<rho>_\<sigma>_split \<rho>'_\<rho>''_wf \<rho>_\<sigma>_wf apply -
  proof (induct \<rho> \<rho>' rule:ttWF2.induct, auto simp add: notin_tocks tt_prefix_concat)
    fix \<rho> \<sigma>' :: "'a ttobs list"
    fix Y
    assume "[Y]\<^sub>R # [Tock]\<^sub>E # \<sigma>' \<in> tocks UNIV"
    then have 1: "\<sigma>' \<in> tocks UNIV"
      using tocks.cases by auto
    assume "\<forall>t'\<in>tocks UNIV. t' \<le>\<^sub>C [Y]\<^sub>R # [Tock]\<^sub>E # \<sigma>' @ \<rho>'' \<longrightarrow> t' \<le>\<^sub>C [Y]\<^sub>R # [Tock]\<^sub>E # \<sigma>'"
    then have 2: "\<forall>t'\<in>tocks UNIV. t' \<le>\<^sub>C \<sigma>' @ \<rho>'' \<longrightarrow> t' \<le>\<^sub>C \<sigma>'"
      using tocks.simps by (auto, erule_tac x="[Y]\<^sub>R # [Tock]\<^sub>E # t'" in ballE, auto, blast)
    assume "\<sigma>' \<in> tocks UNIV \<and> (\<forall>t'\<in>tocks UNIV. t' \<le>\<^sub>C \<sigma>' @ \<rho>'' \<longrightarrow> t' \<le>\<^sub>C \<sigma>') \<Longrightarrow> \<sigma>' \<le>\<^sub>C \<rho>"
    then show "\<sigma>' \<le>\<^sub>C \<rho>"
      using 1 2 by blast
  next
    fix Xa \<rho> \<sigma>'
    assume "[Xa]\<^sub>R # [Tick]\<^sub>E # \<rho> @ [X]\<^sub>R # \<sigma> = \<sigma>' @ \<rho>''" "ttWF (\<sigma>' @ \<rho>'')"
    then have "ttWF ([Xa]\<^sub>R # [Tick]\<^sub>E # \<rho> @ [X]\<^sub>R # \<sigma>)"
      by auto
    then show "\<sigma>' \<le>\<^sub>C [Xa]\<^sub>R # [Tick]\<^sub>E # \<rho>"
      by auto
  next
    fix Xa e \<rho> \<sigma>'
    assume "[Xa]\<^sub>R # [Event e]\<^sub>E # \<rho> @ [X]\<^sub>R # \<sigma> = \<sigma>' @ \<rho>''" "ttWF (\<sigma>' @ \<rho>'')"
    then have "ttWF ([Xa]\<^sub>R # [Event e]\<^sub>E # \<rho> @ [X]\<^sub>R # \<sigma>)"
      by auto
    then show "\<sigma>' \<le>\<^sub>C [Xa]\<^sub>R # [Event e]\<^sub>E # \<rho>"
      by auto
  next
    fix Xa Y \<rho> \<sigma>'
    assume "[Xa]\<^sub>R # [Y]\<^sub>R # \<rho> @ [X]\<^sub>R # \<sigma> = \<sigma>' @ \<rho>''" "ttWF (\<sigma>' @ \<rho>'')"
    then have "ttWF ([Xa]\<^sub>R # [Y]\<^sub>R # \<rho> @ [X]\<^sub>R # \<sigma>)"
      by auto
    then show "\<sigma>' \<le>\<^sub>C [Xa]\<^sub>R # [Y]\<^sub>R # \<rho>"
      by auto
  next
    fix x \<rho> \<sigma>'
    assume "[Tick]\<^sub>E # x # \<rho> @ [X]\<^sub>R # \<sigma> = \<sigma>' @ \<rho>''" "ttWF (\<sigma>' @ \<rho>'')"
    then have "ttWF ([Tick]\<^sub>E # x # \<rho> @ [X]\<^sub>R # \<sigma>)"
      by auto
    then show "\<sigma>' \<le>\<^sub>C [Tick]\<^sub>E # x # \<rho>"
      by auto
  next
    fix \<rho> \<sigma>'
    assume "[Tock]\<^sub>E # \<rho> @ [X]\<^sub>R # \<sigma> = \<sigma>' @ \<rho>''" "ttWF (\<sigma>' @ \<rho>'')"
    then have "ttWF ([Tock]\<^sub>E # \<rho> @ [X]\<^sub>R # \<sigma>)"
      by auto
    then show "\<sigma>' \<le>\<^sub>C [Tock]\<^sub>E # \<rho>"
      by auto
  qed
  then show "\<rho> @ [X \<union> Y]\<^sub>R # \<sigma> \<in> P \<box>\<^sub>C Q"
  proof auto
    assume case_assms: "\<rho>' \<le>\<^sub>C \<rho>"
    then obtain \<rho>2 where \<rho>2_def: "\<rho> = \<rho>' @ \<rho>2"
      using tt_prefix_decompose by blast
    have set1: "{e. e \<noteq> Tock \<and> \<rho> @ [[e]\<^sub>E] \<in> P \<box>\<^sub>C Q} = {e. e \<noteq> Tock \<and> \<rho> @ [[e]\<^sub>E] \<in> P} \<union> {e. e \<noteq> Tock \<and> \<rho> @ [[e]\<^sub>E] \<in> Q}"
    proof auto
      fix x :: "'a ttevent"
      assume "\<rho> @ [[x]\<^sub>E] \<in> P \<box>\<^sub>C Q"
      then have "\<rho> @ [[x]\<^sub>E] \<in> P \<or> \<rho> @ [[x]\<^sub>E] \<in> Q"
        unfolding ExtChoiceTT_def by auto
      then show "\<rho> @ [[x]\<^sub>E] \<notin> Q \<Longrightarrow> \<rho> @ [[x]\<^sub>E] \<in> P"
        by auto
    next
      fix x :: "'a ttevent"
      assume "x \<noteq> Tock" "\<rho> @ [[x]\<^sub>E] \<in> P"
      then show "\<rho> @ [[x]\<^sub>E] \<in> P \<box>\<^sub>C Q"
        unfolding ExtChoiceTT_def apply auto
        apply (rule_tac x="\<rho>'" in bexI, simp_all add: \<rho>_\<sigma>_split)
        apply (rule_tac x="\<rho>2 @ [[x]\<^sub>E]" in exI, simp_all add: \<rho>2_def)
        apply (rule_tac x="[]" in exI, simp add: \<rho>'_in_P_Q)
        by (metis \<rho>2_def \<rho>_\<sigma>_split append.assoc tt_prefix_concat tt_prefix_trans tocks_tt_prefix_end_event)
    next
      fix x :: "'a ttevent"
      assume "x \<noteq> Tock" "\<rho> @ [[x]\<^sub>E] \<in> Q"
      then show "\<rho> @ [[x]\<^sub>E] \<in> P \<box>\<^sub>C Q"
        unfolding ExtChoiceTT_def apply auto
        apply (rule_tac x="\<rho>'" in bexI, simp_all add: \<rho>_\<sigma>_split)
        apply (rule_tac x="[]" in exI, simp add: \<rho>'_in_P_Q)
        apply (rule_tac x="\<rho>2 @ [[x]\<^sub>E]" in exI, simp_all add: \<rho>2_def)
        by (metis \<rho>2_def \<rho>_\<sigma>_split append.assoc tt_prefix_concat tt_prefix_trans tocks_tt_prefix_end_event)
    qed
    have set2: "{e. e = Tock \<and> \<rho>2 = [] \<and> \<rho> @ [[X]\<^sub>R, [e]\<^sub>E] \<in> P \<box>\<^sub>C Q} = 
      {e. e = Tock \<and> \<rho>2 = [] \<and> \<rho> @ [[X]\<^sub>R, [e]\<^sub>E] \<in> P} \<inter> {e. e = Tock \<and> \<rho>2 = [] \<and> \<rho> @ [[X]\<^sub>R, [e]\<^sub>E] \<in> Q}"
    proof auto
      assume case_assms: "\<rho> @ [[X]\<^sub>R, [Tock]\<^sub>E] \<in> P \<box>\<^sub>C Q" "\<rho>2 = []"
      then have "\<rho>' @ [[X]\<^sub>R, [Tock]\<^sub>E] \<in> P \<box>\<^sub>C Q"
        using \<rho>2_def \<rho>_\<sigma>_split by auto
      then obtain r s t where rst_assms: 
        "r \<in> tocks UNIV"
        "r @ s \<in> P"
        "r @ t \<in> Q"
        "\<forall>x\<in>tocks UNIV. x \<le>\<^sub>C r @ s \<longrightarrow> x \<le>\<^sub>C r"
        "\<forall>x\<in>tocks UNIV. x \<le>\<^sub>C r @ t \<longrightarrow> x \<le>\<^sub>C r"
        "(\<rho>' @ [[X]\<^sub>R, [Tock]\<^sub>E] = r @ s \<or> \<rho>' @ [[X]\<^sub>R, [Tock]\<^sub>E] = r @ t)"
        unfolding ExtChoiceTT_def by auto
      have in_tocks: "\<rho>' @ [[X]\<^sub>R, [Tock]\<^sub>E] \<in> tocks UNIV"
        by (simp add: \<rho>_\<sigma>_split tocks.empty_in_tocks tocks.tock_insert_in_tocks tocks_append_tocks)
      then have r_def: "r = \<rho>' @ [[X]\<^sub>R, [Tock]\<^sub>E]"
        using tt_prefix_refl rst_assms(4) rst_assms(5) rst_assms(6) self_extension_tt_prefix by fastforce
      then have "r \<in> P \<and> r \<in> Q"
        by (smt TT1_def TT_TT1 rst_assms assms(1) assms(2) tt_prefix_concat tt_prefix_imp_prefix_subset in_tocks rst_assms(4))
      then show "\<rho> @ [[X]\<^sub>R, [Tock]\<^sub>E] \<in> P"
        by (simp add: \<rho>2_def case_assms(2) r_def)
    next
      assume case_assms: "\<rho> @ [[X]\<^sub>R, [Tock]\<^sub>E] \<in> P \<box>\<^sub>C Q" "\<rho>2 = []"
      then have "\<rho>' @ [[X]\<^sub>R, [Tock]\<^sub>E] \<in> P \<box>\<^sub>C Q"
        using \<rho>2_def \<rho>_\<sigma>_split by auto
      then obtain r s t where rst_assms: 
        "r \<in> tocks UNIV"
        "r @ s \<in> P"
        "r @ t \<in> Q"
        "\<forall>x\<in>tocks UNIV. x \<le>\<^sub>C r @ s \<longrightarrow> x \<le>\<^sub>C r"
        "\<forall>x\<in>tocks UNIV. x \<le>\<^sub>C r @ t \<longrightarrow> x \<le>\<^sub>C r"
        "(\<rho>' @ [[X]\<^sub>R, [Tock]\<^sub>E] = r @ s \<or> \<rho>' @ [[X]\<^sub>R, [Tock]\<^sub>E] = r @ t)"
        unfolding ExtChoiceTT_def by auto
      have in_tocks: "\<rho>' @ [[X]\<^sub>R, [Tock]\<^sub>E] \<in> tocks UNIV"
        by (simp add: \<rho>_\<sigma>_split tocks.empty_in_tocks tocks.tock_insert_in_tocks tocks_append_tocks)
      then have r_def: "r = \<rho>' @ [[X]\<^sub>R, [Tock]\<^sub>E]"
        using tt_prefix_refl rst_assms(4) rst_assms(5) rst_assms(6) self_extension_tt_prefix by fastforce
      then have "r \<in> P \<and> r \<in> Q"
        by (smt TT1_def TT_TT1 rst_assms assms(1) assms(2) tt_prefix_concat tt_prefix_imp_prefix_subset in_tocks rst_assms(4))
      then show "\<rho> @ [[X]\<^sub>R, [Tock]\<^sub>E] \<in> Q"
        by (simp add: \<rho>2_def case_assms(2) r_def)
    next
      assume case_assms: "\<rho> @ [[X]\<^sub>R, [Tock]\<^sub>E] \<in> P" "\<rho>2 = []" "\<rho> @ [[X]\<^sub>R, [Tock]\<^sub>E] \<in> Q"
      then have "\<rho>' @ [[X]\<^sub>R, [Tock]\<^sub>E] \<in> P \<and> \<rho>' @ [[X]\<^sub>R, [Tock]\<^sub>E] \<in> Q"
        using \<rho>2_def \<rho>_\<sigma>_split by auto
      also have "\<rho>' @ [[X]\<^sub>R, [Tock]\<^sub>E] \<in> tocks UNIV"
        by (simp add: \<rho>_\<sigma>_split tocks.empty_in_tocks tocks.tock_insert_in_tocks tocks_append_tocks)
      then show "\<rho> @ [[X]\<^sub>R, [Tock]\<^sub>E] \<in> P \<box>\<^sub>C Q"
        unfolding ExtChoiceTT_def apply auto
        apply (rule_tac x="\<rho>' @ [[X]\<^sub>R, [Tock]\<^sub>E]" in bexI, simp_all)
        apply (rule_tac x="[]" in exI, simp_all add: calculation)
        apply (rule_tac x="[]" in exI, simp_all add: calculation)
        using \<rho>2_def \<rho>_\<sigma>_split case_assms(2) by auto
    qed
    have set3: "{e. e = Tock \<and> \<rho>2 \<noteq> [] \<and> \<rho> @ [[X]\<^sub>R, [e]\<^sub>E] \<in> P \<box>\<^sub>C Q} =
      {e. e = Tock \<and> \<rho>2 \<noteq> [] \<and> \<rho> @ [[X]\<^sub>R, [e]\<^sub>E] \<in> P} \<union> {e. e = Tock \<and> \<rho>2 \<noteq> [] \<and> \<rho> @ [[X]\<^sub>R, [e]\<^sub>E] \<in> Q}"
    proof auto
      assume "\<rho>2 \<noteq> []" "\<rho> @ [[X]\<^sub>R, [Tock]\<^sub>E] \<in> P \<box>\<^sub>C Q"
      then show "\<rho> @ [[X]\<^sub>R, [Tock]\<^sub>E] \<notin> Q \<Longrightarrow> \<rho> @ [[X]\<^sub>R, [Tock]\<^sub>E] \<in> P"
        unfolding ExtChoiceTT_def by auto
    next
      assume \<rho>2_nonempty: "\<rho>2 \<noteq> []"
      assume in_P: "\<rho> @ [[X]\<^sub>R, [Tock]\<^sub>E] \<in> P"
      have \<rho>2_notin_tocks: "\<rho>2 \<notin> tocks UNIV"
      proof auto
        assume "\<rho>2 \<in> tocks UNIV"
        then have "\<rho>' @ \<rho>2 \<in> tocks UNIV"
          using \<rho>_\<sigma>_split tocks_append_tocks by blast
        then have "\<rho>' @ \<rho>2 \<le>\<^sub>C \<rho>'"
          using \<rho>2_def \<rho>_\<sigma>_split tt_prefix_concat by blast
        then have "\<rho>2 = []"
          using self_extension_tt_prefix by blast
        then show "False"
          using \<rho>2_nonempty by auto
      qed
      have full_notin_tocks: "\<rho>' @ \<rho>2 @ [[X]\<^sub>R, [Tock]\<^sub>E] \<notin> tocks UNIV"
        using \<rho>2_notin_tocks \<rho>_\<sigma>_split tocks_append_nontocks tocks_mid_refusal_front_in_tocks by blast
      have "\<forall>x\<in>tocks UNIV. x \<le>\<^sub>C \<rho> @ [[X]\<^sub>R, [Tock]\<^sub>E] \<longrightarrow> x \<le>\<^sub>C \<rho>'"
      proof (auto simp add: \<rho>2_def \<rho>_\<sigma>_split)
        fix x :: "'a ttobs list"
        assume x_in_tocks: "x \<in> tocks UNIV"
        assume "x \<le>\<^sub>C \<rho>' @ \<rho>2 @ [[X]\<^sub>R, [Tock]\<^sub>E]"
        also have "\<And> y. x \<le>\<^sub>C y @ [[X]\<^sub>R, [Tock]\<^sub>E] \<Longrightarrow> x \<le>\<^sub>C y \<or> x = y @ [[X]\<^sub>R] \<or> x = y @ [[X]\<^sub>R, [Tock]\<^sub>E]"
        proof -
          fix y
          show "x \<le>\<^sub>C y @ [[X]\<^sub>R, [Tock]\<^sub>E] \<Longrightarrow> x \<le>\<^sub>C y \<or> x = y @ [[X]\<^sub>R] \<or> x = y @ [[X]\<^sub>R, [Tock]\<^sub>E]"
            using tt_prefix.elims(2) tt_prefix_antisym by (induct x y rule:tt_prefix.induct, auto, fastforce)
        qed
        then have "x \<le>\<^sub>C \<rho>' @ \<rho>2 \<or> x = \<rho>' @ \<rho>2 @ [[X]\<^sub>R] \<or> x = \<rho>' @ \<rho>2 @ [[X]\<^sub>R, [Tock]\<^sub>E]"
          using calculation by force
        then show "x \<le>\<^sub>C \<rho>'"
          apply (auto simp add: \<rho>2_def \<rho>_\<sigma>_split x_in_tocks)
          using \<rho>2_def \<rho>_\<sigma>_split tt_prefix_concat tt_prefix_trans x_in_tocks apply blast
          apply (metis append_assoc end_refusal_notin_tocks x_in_tocks)
          using full_notin_tocks x_in_tocks by blast
      qed
      then show "\<rho> @ [[X]\<^sub>R, [Tock]\<^sub>E] \<in> P \<box>\<^sub>C Q"
        unfolding ExtChoiceTT_def apply auto
        apply (rule_tac x="\<rho>'" in bexI, auto simp add: \<rho>_\<sigma>_split)
        apply (rule_tac x="\<rho>2 @ [[X]\<^sub>R, [Tock]\<^sub>E]" in exI, insert \<rho>2_def \<rho>_\<sigma>_split in_P, auto)
        apply (rule_tac x="[]" in exI, auto simp add: \<rho>'_in_P_Q)
        done
    next
      assume \<rho>2_nonempty: "\<rho>2 \<noteq> []"
      assume in_Q: "\<rho> @ [[X]\<^sub>R, [Tock]\<^sub>E] \<in> Q"
      have \<rho>2_notin_tocks: "\<rho>2 \<notin> tocks UNIV"
      proof auto
        assume "\<rho>2 \<in> tocks UNIV"
        then have "\<rho>' @ \<rho>2 \<in> tocks UNIV"
          using \<rho>_\<sigma>_split tocks_append_tocks by blast
        then have "\<rho>' @ \<rho>2 \<le>\<^sub>C \<rho>'"
          using \<rho>2_def \<rho>_\<sigma>_split tt_prefix_concat by blast
        then have "\<rho>2 = []"
          using self_extension_tt_prefix by blast
        then show "False"
          using \<rho>2_nonempty by auto
      qed
      then have full_notin_tocks: "\<rho>' @ \<rho>'' @ [[X]\<^sub>R, [Tock]\<^sub>E] \<notin> tocks UNIV"
        by (metis \<rho>2_def \<rho>_\<sigma>_split append.assoc tocks_append_nontocks tocks_mid_refusal_front_in_tocks)
      have "\<forall>x\<in>tocks UNIV. x \<le>\<^sub>C \<rho> @ [[X]\<^sub>R, [Tock]\<^sub>E] \<longrightarrow> x \<le>\<^sub>C \<rho>'"
      proof (auto simp add: \<rho>_\<sigma>_split \<rho>2_def)
        fix x :: "'a ttobs list"
        assume x_in_tocks: "x \<in> tocks UNIV"
        assume "x \<le>\<^sub>C \<rho>' @ \<rho>2 @ [[X]\<^sub>R, [Tock]\<^sub>E]"
        also have "\<And> y. x \<le>\<^sub>C y @ [[X]\<^sub>R, [Tock]\<^sub>E] \<Longrightarrow> x \<le>\<^sub>C y \<or> x = y @ [[X]\<^sub>R] \<or> x = y @ [[X]\<^sub>R, [Tock]\<^sub>E]"
        proof -
          fix y
          show "x \<le>\<^sub>C y @ [[X]\<^sub>R, [Tock]\<^sub>E] \<Longrightarrow> x \<le>\<^sub>C y \<or> x = y @ [[X]\<^sub>R] \<or> x = y @ [[X]\<^sub>R, [Tock]\<^sub>E]"
            using tt_prefix.elims(2) tt_prefix_antisym by (induct x y rule:tt_prefix.induct, auto, fastforce)
        qed
        then have "x \<le>\<^sub>C \<rho>' @ \<rho>2 \<or> x = \<rho>' @ \<rho>2 @ [[X]\<^sub>R] \<or> x = \<rho>' @ \<rho>2 @ [[X]\<^sub>R, [Tock]\<^sub>E]"
          using calculation by force
        then show "x \<le>\<^sub>C \<rho>'"
          apply auto
          using \<rho>2_def \<rho>_\<sigma>_split tt_prefix_concat tt_prefix_trans x_in_tocks apply blast
          apply (metis append_assoc end_refusal_notin_tocks x_in_tocks)
          using \<rho>2_notin_tocks \<rho>_\<sigma>_split tocks_append_nontocks tocks_mid_refusal_front_in_tocks x_in_tocks by blast
      qed
      then show "\<rho> @ [[X]\<^sub>R, [Tock]\<^sub>E] \<in> P \<box>\<^sub>C Q"
        unfolding ExtChoiceTT_def apply auto
        apply (rule_tac x="\<rho>'" in bexI, auto simp add: \<rho>_\<sigma>_split)
        apply (rule_tac x="[]" in exI, auto simp add: \<rho>2_def \<rho>'_in_P_Q)
        apply (insert \<rho>2_def \<rho>_\<sigma>_split in_Q, auto)
        done
    qed
    thm set1 set2 set3
    have in_P_or_Q: "\<rho> @ [X]\<^sub>R # \<sigma> \<in> P \<or> \<rho> @ [X]\<^sub>R # \<sigma> \<in> Q"
      using assm1 unfolding ExtChoiceTT_def by auto
    show "\<rho> @ [X \<union> Y]\<^sub>R # \<sigma> \<in> P \<box>\<^sub>C Q"
    proof (cases "\<rho>2 \<noteq> []", auto)
      assume case_assm: "\<rho>2 \<noteq> []"
      have full_pretocks: "\<forall>\<rho>''\<in>tocks UNIV. \<rho>'' \<le>\<^sub>C \<rho>' @ \<rho>2 @ [X \<union> Y]\<^sub>R # \<sigma> \<longrightarrow> \<rho>'' \<le>\<^sub>C \<rho>'"
      proof -
        have "\<forall>\<rho>''\<in>tocks UNIV. \<rho>'' \<le>\<^sub>C \<rho>' @ \<rho>2 @ [X]\<^sub>R # \<sigma> \<longrightarrow> \<rho>'' \<le>\<^sub>C \<rho>'"
          by (simp add: \<rho>2_def \<rho>_\<sigma>_split)
        also have "\<rho>2 @ [X]\<^sub>R # \<sigma> \<subseteq>\<^sub>C \<rho>2 @ [X \<union> Y]\<^sub>R # \<sigma>"
          by (simp add: tt_subset_combine tt_subset_refl)
        then show ?thesis
          using calculation tt_subset_longest_tocks3 by blast
      qed
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
      then have "\<rho> @ [X \<union> Y]\<^sub>R # \<sigma> \<in> P \<or> \<rho> @ [X \<union> Y]\<^sub>R # \<sigma> \<in> Q"
        using assms(3) assms(4) in_P_or_Q unfolding TT2_def by auto
      then show "\<rho> @ [X \<union> Y]\<^sub>R # \<sigma> \<in> P \<box>\<^sub>C Q"
        unfolding ExtChoiceTT_def apply auto
        apply (rule_tac x="\<rho>'" in bexI, auto simp add: \<rho>2_def \<rho>_\<sigma>_split)
        apply (rule_tac x="\<rho>2 @ [[X \<union> Y]\<^sub>R] @ \<sigma>" in exI, auto)
        apply (rule_tac x="[]" in exI, auto simp add: \<rho>2_def \<rho>_\<sigma>_split \<rho>'_in_P_Q case_assm full_pretocks)
        apply (metis Cons_eq_append_conv Nil_is_append_conv case_assm list.simps(3))
        apply (rule_tac x="\<rho>'" in bexI, auto simp add: \<rho>2_def \<rho>_\<sigma>_split)
        apply (rule_tac x="[]" in exI, auto simp add: \<rho>2_def \<rho>_\<sigma>_split \<rho>'_in_P_Q case_assm full_pretocks)
        apply (metis Cons_eq_append_conv Nil_is_append_conv case_assm list.simps(3))
        done
    next
      assume case_assm: "\<rho>2 = []"
      show "\<rho> @ [X \<union> Y]\<^sub>R # \<sigma> \<in> P \<box>\<^sub>C Q"
      proof (cases "\<sigma> \<noteq> []", auto)
        assume case_assm2: "\<sigma> \<noteq> []"
        have \<sigma>_Tock_start: "\<exists> \<sigma>'. \<sigma> = [Tock]\<^sub>E # \<sigma>'"
          using assm1 case_assm2 apply (cases \<sigma> rule:ttWF.cases, auto)
          using \<rho>'_\<rho>''_wf \<rho>2_def \<rho>_\<sigma>_split case_assm tocks_append_wf2 by force+
        then have False
          using \<rho>_\<sigma>_split \<rho>2_def case_assm
        proof auto
          fix \<sigma>'
          assume "\<forall>t'\<in>tocks UNIV. t' \<le>\<^sub>C \<rho>' @ [X]\<^sub>R # [Tock]\<^sub>E # \<sigma>' \<longrightarrow> t' \<le>\<^sub>C \<rho>'" "\<rho>' \<in> tocks UNIV"
          then have "\<rho>' @ [[X]\<^sub>R, [Tock]\<^sub>E] \<le>\<^sub>C \<rho>'"
            by (erule_tac x="\<rho>' @ [[X]\<^sub>R, [Tock]\<^sub>E]" in ballE, auto simp add: tt_prefix_same_front tocks.intros tocks_append_tocks)
          then show False
            using self_extension_tt_prefix by blast
          qed
          then show "\<rho> @ [X \<union> Y]\<^sub>R # \<sigma> \<in> P \<box>\<^sub>C Q"
            by simp
        next
          assume case_assm2: "\<sigma> = []"  
          have "\<rho> @ [[{e. e \<in> X \<and> e \<noteq> Tock}]\<^sub>R] \<lesssim>\<^sub>C \<rho> @ [[X]\<^sub>R]"
            by (induct \<rho>, auto, case_tac a, auto)
          then have "\<rho> @ [[{e. e \<in> X \<and> e \<noteq> Tock}]\<^sub>R] \<in> P \<box>\<^sub>C Q"
            using TT1_ExtChoice TT1_def assm1 assms(1) assms(2) case_assm2 by blast
          then have "\<rho>' @ [[{e. e \<in> X \<and> e \<noteq> Tock}]\<^sub>R] \<in> P \<box>\<^sub>C Q"
            using \<rho>2_def \<rho>_\<sigma>_split case_assm by auto
          then have in_P_and_Q: "\<rho>' @ [[{e. e \<in> X \<and> e \<noteq> Tock}]\<^sub>R] \<in> P \<and> \<rho>' @ [[{e. e \<in> X \<and> e \<noteq> Tock}]\<^sub>R] \<in> Q"
            unfolding ExtChoiceTT_def
          proof auto
            fix \<rho> \<sigma> \<tau> :: "'a ttobs list"
            assume case_assm1: "\<rho> \<in> tocks UNIV"
            assume case_assm2: "\<forall>\<rho>'\<in>tocks UNIV. \<rho>' \<le>\<^sub>C \<rho> @ \<sigma> \<longrightarrow> \<rho>' \<le>\<^sub>C \<rho>"
            assume case_assm3: "\<rho>' @ [[{e \<in> X. e \<noteq> Tock}]\<^sub>R] = \<rho> @ \<sigma>"
            assume case_assm4: "\<forall>X. \<sigma> = [[X]\<^sub>R] \<longrightarrow> (\<exists>Y. \<tau> = [[Y]\<^sub>R] \<and> (\<forall>e. (e \<in> X) = (e \<in> Y) \<or> e = Tock))"
            assume case_assm5: "\<rho> @ \<tau> \<in> Q"
            have \<rho>_def: "\<rho> = \<rho>'"
              by (metis (no_types, lifting) \<rho>_\<sigma>_split butlast_append butlast_snoc case_assm1 case_assm2 case_assm3 tt_prefix_antisym tt_prefix_concat end_refusal_notin_tocks)
            then have \<sigma>_def: "\<sigma> = [[{e \<in> X. e \<noteq> Tock}]\<^sub>R]"
              using case_assm3 by blast
            obtain Y where Y_assms: "\<tau> = [[Y]\<^sub>R]" "\<forall>e. (e \<in> X) = (e \<in> Y) \<or> e = Tock"
              using case_assm4 by (erule_tac x="{e. e \<in> X \<and> e \<noteq> Tock}" in allE, simp add: \<sigma>_def, auto)
            then have "\<rho>' @ [[{e \<in> X. e \<noteq> Tock}]\<^sub>R] \<lesssim>\<^sub>C \<rho>' @ [[Y]\<^sub>R]"
              by (induct \<rho>', auto, case_tac a, auto)
            then have "\<rho>' @ [[{e \<in> X. e \<noteq> Tock}]\<^sub>R] \<in> Q"
              using TT1_def TT_TT1 Y_assms(1) \<rho>_def assms(2) case_assm5 by blast
            then show "\<rho> @ \<sigma> \<in> Q"
              by (simp add: case_assm3)
          next
            fix \<rho> \<sigma> \<tau> :: "'a ttobs list"
            assume case_assm1: "\<rho> \<in> tocks UNIV"
            assume case_assm2: "\<forall>\<rho>'\<in>tocks UNIV. \<rho>' \<le>\<^sub>C \<rho> @ \<tau> \<longrightarrow> \<rho>' \<le>\<^sub>C \<rho>"
            assume case_assm3: "\<rho>' @ [[{e \<in> X. e \<noteq> Tock}]\<^sub>R] = \<rho> @ \<tau>"
            assume case_assm4: "\<forall>X. \<tau> = [[X]\<^sub>R] \<longrightarrow> (\<exists>Y. \<sigma> = [[Y]\<^sub>R] \<and> (\<forall>e. (e \<in> X) = (e \<in> Y) \<or> e = Tock))"
            assume case_assm5: "\<rho> @ \<sigma> \<in> P"
            have \<rho>_def: "\<rho> = \<rho>'"
              by (metis (no_types, lifting) \<rho>_\<sigma>_split butlast_append butlast_snoc case_assm1 case_assm2 case_assm3 tt_prefix_antisym tt_prefix_concat end_refusal_notin_tocks)
            then have \<sigma>_def: "\<tau> = [[{e \<in> X. e \<noteq> Tock}]\<^sub>R]"
              using case_assm3 by blast
            obtain Y where Y_assms: "\<sigma> = [[Y]\<^sub>R]" "\<forall>e. (e \<in> X) = (e \<in> Y) \<or> e = Tock"
              using case_assm4 by (erule_tac x="{e. e \<in> X \<and> e \<noteq> Tock}" in allE, simp add: \<sigma>_def, auto)
            then have "\<rho>' @ [[{e \<in> X. e \<noteq> Tock}]\<^sub>R] \<lesssim>\<^sub>C \<rho>' @ [[Y]\<^sub>R]"
              by (induct \<rho>', auto, case_tac a, auto)
            then have "\<rho>' @ [[{e \<in> X. e \<noteq> Tock}]\<^sub>R] \<in> P"
              using TT1_def TT_TT1 Y_assms(1) \<rho>_def assms(1) case_assm5 by blast
            then show "\<rho> @ \<tau> \<in> P"
              by (simp add: case_assm3)
          qed
          have notocks_assm2: "{e. e \<in> Y \<and> e \<noteq> Tock} \<inter> {e. e \<noteq> Tock \<and> \<rho> @ [[e]\<^sub>E] \<in> P \<or> e = Tock \<and> \<rho> @ [[{e. e \<in> X \<and> e \<noteq> Tock}]\<^sub>R, [e]\<^sub>E] \<in> P} = {} 
              \<and> {e. e \<in> Y \<and> e \<noteq> Tock} \<inter> {e. e \<noteq> Tock \<and> \<rho> @ [[e]\<^sub>E] \<in> Q \<or> e = Tock \<and> \<rho> @ [[{e. e \<in> X \<and> e \<noteq> Tock}]\<^sub>R, [e]\<^sub>E] \<in> Q} = {}"
            using set1 assm2 by blast
          have TT2w_P_Q: "TT2w P \<and> TT2w Q"
            by (simp add: TT_TT2w assms(1) assms(2))
          then have notock_X_Y_in_P_Q: "\<rho> @ [[{e. e \<in> X \<union> Y \<and> e \<noteq> Tock}]\<^sub>R] \<in> P \<and> \<rho> @ [[{e. e \<in> X \<union> Y \<and> e \<noteq> Tock}]\<^sub>R] \<in> Q"
            unfolding TT2w_def
          proof auto
            assume "\<forall>\<rho> X Y. \<rho> @ [[X]\<^sub>R] \<in> P \<and> 
                Y \<inter> {e. e \<noteq> Tock \<and> \<rho> @ [[e]\<^sub>E] \<in> P \<or> e = Tock \<and> \<rho> @ [[X]\<^sub>R, [e]\<^sub>E] \<in> P} = {} \<longrightarrow>
                  \<rho> @ [[X \<union> Y]\<^sub>R] \<in> P"
            then have "\<rho> @ [[{e. e \<in> X \<and> e \<noteq> Tock} \<union> {e. e \<in> Y \<and> e \<noteq> Tock}]\<^sub>R] \<in> P"
              using \<rho>2_def case_assm in_P_and_Q notocks_assm2 by auto
            also have "\<rho> @ [[{e. e \<in> X \<and> e \<noteq> Tock} \<union> {e. e \<in> Y \<and> e \<noteq> Tock}]\<^sub>R] = \<rho> @ [[{e. (e \<in> X \<or> e \<in> Y) \<and> e \<noteq> Tock}]\<^sub>R]"
              by auto
            then show "\<rho> @ [[{e. (e \<in> X \<or> e \<in> Y) \<and> e \<noteq> Tock}]\<^sub>R] \<in> P"
              using calculation by auto
          next
            assume "\<forall>\<rho> X Y. \<rho> @ [[X]\<^sub>R] \<in> Q \<and> 
                Y \<inter> {e. e \<noteq> Tock \<and> \<rho> @ [[e]\<^sub>E] \<in> Q \<or> e = Tock \<and> \<rho> @ [[X]\<^sub>R, [e]\<^sub>E] \<in> Q} = {} \<longrightarrow>
                  \<rho> @ [[X \<union> Y]\<^sub>R] \<in> Q"
            then have "\<rho> @ [[{e. e \<in> X \<and> e \<noteq> Tock} \<union> {e. e \<in> Y \<and> e \<noteq> Tock}]\<^sub>R] \<in> Q"
              using \<rho>2_def case_assm in_P_and_Q notocks_assm2 by auto
            also have "\<rho> @ [[{e. e \<in> X \<and> e \<noteq> Tock} \<union> {e. e \<in> Y \<and> e \<noteq> Tock}]\<^sub>R] = \<rho> @ [[{e. (e \<in> X \<or> e \<in> Y) \<and> e \<noteq> Tock}]\<^sub>R]"
              by auto
            then show "\<rho> @ [[{e. (e \<in> X \<or> e \<in> Y) \<and> e \<noteq> Tock}]\<^sub>R] \<in> Q"
              using calculation by auto
          qed
          show "\<rho> @ [[X \<union> Y]\<^sub>R] \<in> P \<box>\<^sub>C Q"
          proof (cases "Tock \<in> Y")
            assume case_assm3: "Tock \<in> Y"
            have assm2_nontock_P: "{e. e \<in> Y \<and> e \<noteq> Tock} \<inter> {e. e \<noteq> Tock \<and> \<rho> @ [[e]\<^sub>E] \<in> P} = {}"
              using assm2 set1 by auto
            have assm2_nontock_Q: "{e. e \<in> Y \<and> e \<noteq> Tock} \<inter> {e. e \<noteq> Tock \<and> \<rho> @ [[e]\<^sub>E] \<in> Q} = {}"
              using assm2 set1 by auto
            have "{e. e \<in> Y \<and> e = Tock} \<inter> {e. e = Tock \<and> \<rho> @ [[X]\<^sub>R, [e]\<^sub>E] \<in> P \<box>\<^sub>C Q} = {}"
              using assm2 by auto
            then have "Tock \<notin> {e. e = Tock \<and> \<rho> @ [[X]\<^sub>R, [e]\<^sub>E] \<in> P \<box>\<^sub>C Q}"
              using case_assm3 by auto
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
              assume case_assm4: "Y \<inter> {e. e \<noteq> Tock \<and> \<rho> @ [[e]\<^sub>E] \<in> P \<or> e = Tock \<and> \<rho> @ [[X]\<^sub>R, [e]\<^sub>E] \<in> P} = {}"
              assume case_assm5: "Y \<inter> {e. e \<noteq> Tock \<and> \<rho> @ [[e]\<^sub>E] \<in> Q \<or> e = Tock \<and> \<rho> @ [[X]\<^sub>R, [e]\<^sub>E] \<in> Q} = {}"
              show "\<rho> @ [[X \<union> Y]\<^sub>R] \<in> P \<box>\<^sub>C Q"
                using in_P_or_Q case_assm case_assm2 \<rho>2_def
              proof auto
                assume case_assm6: "\<rho>' @ [[X]\<^sub>R] \<in> P"
                then have "\<rho>' @ [[X \<union> Y]\<^sub>R] \<in> P"
                  using TT2w_P_Q case_assm4 \<rho>2_def case_assm unfolding TT2w_def by auto
                also have "\<rho>' @ [[{e \<in> X \<union> Y. e \<noteq> Tock}]\<^sub>R] \<in> Q"
                  using notock_X_Y_in_P_Q \<rho>2_def case_assm by auto
                then show "\<rho>' @ [[X \<union> Y]\<^sub>R] \<in> P \<box>\<^sub>C Q"
                  unfolding ExtChoiceTT_def using calculation apply auto
                apply (rule_tac x="\<rho>'" in bexI, simp_all add: \<rho>_\<sigma>_split case_assm)
                apply (rule_tac x="[[X \<union> Y]\<^sub>R]" in exI, simp_all)
                apply (rule_tac x="[[{e \<in> X \<union> Y. e \<noteq> Tock}]\<^sub>R]" in exI, auto)
                using tt_prefix_notfront_is_whole end_refusal_notin_tocks by blast+
              next
                assume case_assm6: "\<rho>' @ [[X]\<^sub>R] \<in> Q"
                then have "\<rho>' @ [[X \<union> Y]\<^sub>R] \<in> Q"
                  using TT2w_P_Q case_assm5 \<rho>2_def case_assm unfolding TT2w_def by auto
                also have "\<rho>' @ [[{e \<in> X \<union> Y. e \<noteq> Tock}]\<^sub>R] \<in> P"
                  using notock_X_Y_in_P_Q \<rho>2_def case_assm by auto
                then show "\<rho>' @ [[X \<union> Y]\<^sub>R] \<in> P \<box>\<^sub>C Q"
                  unfolding ExtChoiceTT_def using calculation apply auto
                  apply (rule_tac x="\<rho>'" in bexI, simp_all add: \<rho>_\<sigma>_split case_assm)
                  apply (rule_tac x="[[{e \<in> X \<union> Y. e \<noteq> Tock}]\<^sub>R]" in exI, auto)
                  apply (rule_tac x="[[X \<union> Y]\<^sub>R]" in exI, simp_all)
                  using tt_prefix_notfront_is_whole end_refusal_notin_tocks by blast+
              qed
            next
              assume case_assm3: "\<rho> @ [[X]\<^sub>R, [Tock]\<^sub>E] \<in> P"
              assume case_assm4: "Y \<inter> {e. e \<noteq> Tock \<and> \<rho> @ [[e]\<^sub>E] \<in> Q \<or> e = Tock \<and> \<rho> @ [[X]\<^sub>R, [e]\<^sub>E] \<in> Q} = {}"
              have TT1_P: "TT1 P"
                by (simp add: TT_TT1 assms(1))
              have "\<rho> @ [[X]\<^sub>R] \<lesssim>\<^sub>C \<rho> @ [[X]\<^sub>R, [Tock]\<^sub>E]"
                using tt_prefix_subset_same_front by fastforce
              then have in_P: "\<rho> @ [[X]\<^sub>R] \<in> P"
                using TT1_P case_assm3 unfolding TT1_def by auto 
              have TT3_P: "TT3 P"
                by (simp add: TT_TT3 assms(1))
              then have "Tock \<notin> X"
                using TT3_any_cons_end_tock case_assm3 by blast
              then have in_Q: "\<rho> @ [[X]\<^sub>R] \<in> Q"
                using assm1 case_assm2 unfolding ExtChoiceTT_def
              proof auto
                fix r s t :: "'a ttobs list"
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
                  by (metis "1" "4" "8" \<rho>2_def \<rho>_\<sigma>_split append_Nil2 case_assm case_assm2 tt_prefix_antisym tt_prefix_concat)
                then have "s = [[X]\<^sub>R]"
                  using "8" by blast
                then obtain Y where Y_assms: "t = [[Y]\<^sub>R]" "\<forall>e. (e \<in> X) = (e \<in> Y) \<or> e = Tock"
                  using "6" by auto
                then have "\<rho> @ [[Y]\<^sub>R] \<in> Q"
                  using "3" r_is_\<rho> by blast
                also have "\<rho> @ [[X]\<^sub>R] \<lesssim>\<^sub>C \<rho> @ [[Y]\<^sub>R]"
                  by (metis "9" Y_assms(2) tt_prefix_subset.simps(2) tt_prefix_subset_refl tt_prefix_subset_same_front subsetI)
                then have "\<rho> @ [[X]\<^sub>R] \<in> Q"
                  using TT1_def TT_TT1 assms(2) calculation by blast
                then show "r @ s \<in> Q"
                  using "8" by auto
              qed
              then have "\<rho> @ [[X \<union> Y]\<^sub>R] \<in> Q"
                using TT2w_P_Q TT2w_def case_assm4 by blast
              then show "\<rho> @ [[X \<union> Y]\<^sub>R] \<in> P \<box>\<^sub>C Q"
                unfolding ExtChoiceTT_def using notock_X_Y_in_P_Q apply auto
                apply (rule_tac x="\<rho>'" in bexI, simp_all add: \<rho>_\<sigma>_split case_assm)
                apply (rule_tac x="[[{e \<in> X \<union> Y. e \<noteq> Tock}]\<^sub>R]" in exI, auto simp add: \<rho>2_def case_assm)
                apply (rule_tac x="[[X \<union> Y]\<^sub>R]" in exI, simp_all)
                using tt_prefix_notfront_is_whole end_refusal_notin_tocks by blast+
            next
              assume case_assm4: "\<rho> @ [[X]\<^sub>R, [Tock]\<^sub>E] \<in> Q"
              assume case_assm5: "Y \<inter> {e. e \<noteq> Tock \<and> \<rho> @ [[e]\<^sub>E] \<in> P \<or> e = Tock \<and> \<rho> @ [[X]\<^sub>R, [e]\<^sub>E] \<in> P} = {}"
              have TT1_Q: "TT1 Q"
                by (simp add: TT_TT1 assms(2))
              have "\<rho> @ [[X]\<^sub>R] \<lesssim>\<^sub>C \<rho> @ [[X]\<^sub>R, [Tock]\<^sub>E]"
                using tt_prefix_subset_same_front by fastforce
              then have in_Q: "\<rho> @ [[X]\<^sub>R] \<in> Q"
                using TT1_Q TT1_def case_assm4 by blast
              have TT3_Q: "TT3 Q"
                by (simp add: TT_TT3 assms(2))
              then have "Tock \<notin> X"
                using TT3_any_cons_end_tock case_assm4 by blast
              then have in_P: "\<rho> @ [[X]\<^sub>R] \<in> P"
                using assm1 case_assm2 unfolding ExtChoiceTT_def
              proof auto
                fix r s t :: "'a ttobs list"
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
                  by (metis "1" "5" "8" \<rho>2_def \<rho>_\<sigma>_split append_Nil2 case_assm case_assm2 tt_prefix_antisym tt_prefix_concat)
              then have "t = [[X]\<^sub>R]"
                using "8" by blast
              then obtain Y where Y_assms: "s = [[Y]\<^sub>R]" "\<forall>e. (e \<in> X) = (e \<in> Y) \<or> e = Tock"
                using "7" by auto
              then have "\<rho> @ [[Y]\<^sub>R] \<in> P"
                using "2" r_is_\<rho> by blast
              also have "\<rho> @ [[X]\<^sub>R] \<lesssim>\<^sub>C \<rho> @ [[Y]\<^sub>R]"
                by (metis "9" Y_assms(2) tt_prefix_subset.simps(2) tt_prefix_subset_refl tt_prefix_subset_same_front subsetI)
              then have "\<rho> @ [[X]\<^sub>R] \<in> P"
                using TT1_def TT_TT1 assms(1) calculation by blast
              then show "r @ t \<in> P"
                using "8" by auto
            qed
            then have "\<rho> @ [[X \<union> Y]\<^sub>R] \<in> P"
              using TT2w_P_Q TT2w_def case_assm5 by blast
            then show "\<rho> @ [[X \<union> Y]\<^sub>R] \<in> P \<box>\<^sub>C Q"
              unfolding ExtChoiceTT_def using notock_X_Y_in_P_Q apply auto
              apply (rule_tac x="\<rho>'" in bexI, simp_all add: \<rho>_\<sigma>_split case_assm)
              apply (rule_tac x="[[X \<union> Y]\<^sub>R]" in exI, simp_all add: \<rho>2_def case_assm)
              apply (rule_tac x="[[{e \<in> X \<union> Y. e \<noteq> Tock}]\<^sub>R]" in exI, auto)
              using tt_prefix_notfront_is_whole end_refusal_notin_tocks by blast+
          qed
        next
          assume case_assm3: "Tock \<notin> Y"
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
            using case_assm3 by auto
          then have assm2_expand: "Y \<inter> {e. e \<noteq> Tock \<and> \<rho> @ [[e]\<^sub>E] \<in> P \<or> e = Tock \<and> \<rho> @ [[X]\<^sub>R, [e]\<^sub>E] \<in> P} = {}
              \<and> Y \<inter> {e. e \<noteq> Tock \<and> \<rho> @ [[e]\<^sub>E] \<in> Q \<or> e = Tock \<and> \<rho> @ [[X]\<^sub>R, [e]\<^sub>E] \<in> Q} = {}"
            using calculation assm2 by auto
          show "\<rho> @ [[X \<union> Y]\<^sub>R] \<in> P \<box>\<^sub>C Q"
            using in_P_or_Q case_assm2
          proof auto
            assume  case_assm4: "\<rho> @ [[X]\<^sub>R] \<in> P"
            have "TT2w P"
              by (simp add: TT2w_P_Q)
            then have "\<rho> @ [[X \<union> Y]\<^sub>R] \<in> P"
              unfolding TT2w_def using case_assm4 assm2_expand by auto
            then show  "\<rho> @ [[X \<union> Y]\<^sub>R] \<in> P \<box>\<^sub>C Q"
              unfolding ExtChoiceTT_def using notock_X_Y_in_P_Q apply auto
              apply (rule_tac x="\<rho>'" in bexI, simp_all add: \<rho>_\<sigma>_split case_assm)
              apply (rule_tac x="[[X \<union> Y]\<^sub>R]" in exI, simp_all add: \<rho>2_def case_assm)
              apply (rule_tac x="[[{e \<in> X \<union> Y. e \<noteq> Tock}]\<^sub>R]" in exI, auto)
              using tt_prefix_notfront_is_whole end_refusal_notin_tocks by blast+
          next
            assume  case_assm4: "\<rho> @ [[X]\<^sub>R] \<in> Q"
            have "TT2w Q"
              by (simp add: TT2w_P_Q)
            then have "\<rho> @ [[X \<union> Y]\<^sub>R] \<in> Q"
              unfolding TT2w_def using case_assm4 assm2_expand by auto
            then show  "\<rho> @ [[X \<union> Y]\<^sub>R] \<in> P \<box>\<^sub>C Q"
              unfolding ExtChoiceTT_def using notock_X_Y_in_P_Q apply auto
              apply (rule_tac x="\<rho>'" in bexI, simp_all add: \<rho>_\<sigma>_split case_assm)
              apply (rule_tac x="[[{e \<in> X \<union> Y. e \<noteq> Tock}]\<^sub>R]" in exI, auto simp add: \<rho>2_def case_assm)
              apply (rule_tac x="[[X \<union> Y]\<^sub>R]" in exI, simp_all)
              using tt_prefix_notfront_is_whole end_refusal_notin_tocks by blast+
          qed
        qed
      qed
    qed
  next
    fix \<sigma>'
    assume case_assms: "\<rho>' = \<rho> @ [X]\<^sub>R # \<sigma>'" "\<sigma>' \<noteq> []" "\<sigma>' \<le>\<^sub>C \<sigma>"
    have \<rho>_Tock_in_tocks: "\<rho> @ [[X]\<^sub>R, [Tock]\<^sub>E] \<in> tocks UNIV"
      by (metis \<rho>_\<sigma>_split case_assms(1) tocks.empty_in_tocks tocks.tock_insert_in_tocks tocks_append_tocks tocks_mid_refusal tocks_mid_refusal_front_in_tocks)
    obtain \<sigma>'' where \<sigma>'_Tock_start: "\<sigma>' = [Tock]\<^sub>E # \<sigma>''"
      using case_assms apply (cases \<sigma>' rule:ttWF.cases, auto)
      using TT_TTwf TTwf_cons_end_not_refusal_refusal \<rho>'_in_P_Q assms(1) apply blast
      using \<rho>_\<sigma>_split ttWF.simps(12) ttWF_dist_cons_refusal tocks_wf apply blast
      apply (metis \<rho>_\<sigma>_split ttWF.simps(11) tocks_append_wf2 tocks_mid_refusal_front_in_tocks tocks_wf)
      using \<rho>'_\<rho>''_wf \<rho>_\<sigma>_split ttWF.simps(13) ttWF_prefix_is_ttWF tocks_append_wf2 tocks_mid_refusal_front_in_tocks apply blast
      using \<rho>'_\<rho>''_wf \<rho>_\<sigma>_split ttWF.simps(12) ttWF_prefix_is_ttWF tocks_append_wf2 tocks_mid_refusal_front_in_tocks apply (blast, blast)
      using \<rho>'_\<rho>''_wf \<rho>_\<sigma>_split ttWF.simps(13) ttWF_prefix_is_ttWF tocks_append_wf2 tocks_mid_refusal_front_in_tocks apply blast+
      done
    then obtain \<sigma>''' where \<sigma>'''_def: "\<sigma> = [Tock]\<^sub>E # \<sigma>'' @ \<sigma>'''"
      using case_assms(3) tt_prefix_decompose by fastforce
    then have "\<rho> @ [X]\<^sub>R # [Tock]\<^sub>E # \<sigma>'' @ \<sigma>''' \<in> P \<box>\<^sub>C Q"
      using assm1 by blast
    then have \<rho>_Tock_in_P_Q: "\<rho> @ [[X]\<^sub>R, [Tock]\<^sub>E] \<in> P \<and> \<rho> @ [[X]\<^sub>R, [Tock]\<^sub>E] \<in> Q"
      unfolding ExtChoiceTT_def
    proof auto
      fix \<rho>' \<sigma> \<tau>
      assume 1: "\<rho>' @ \<sigma> \<in> P"
      assume 2: "\<rho>' @ \<tau> \<in> Q"
      assume 3: "\<forall>\<rho>''\<in>tocks UNIV. \<rho>'' \<le>\<^sub>C \<rho>' @ \<sigma> \<longrightarrow> \<rho>'' \<le>\<^sub>C \<rho>'"
      assume 4: "\<rho> @ [X]\<^sub>R # [Tock]\<^sub>E # \<sigma>'' @ \<sigma>''' = \<rho>' @ \<sigma>"
      have "\<rho> @ [[X]\<^sub>R, [Tock]\<^sub>E] \<le>\<^sub>C \<rho>'"
        using 3 4 apply (erule_tac x="\<rho> @ [[X]\<^sub>R, [Tock]\<^sub>E]" in ballE, simp_all add: \<rho>_Tock_in_tocks)
        by (metis \<rho>_Tock_in_tocks tt_prefix.simps(1) tt_prefix.simps(2) tt_prefix_same_front)
      then show "\<rho> @ [[X]\<^sub>R, [Tock]\<^sub>E] \<in> P"
        by (meson "1" TT1_def TT_TT1 assms(1) tt_prefix_concat tt_prefix_imp_prefix_subset)
    next
      fix \<rho>' \<sigma> \<tau>
      assume 1: "\<rho>' @ \<sigma> \<in> P"
      assume 2: "\<rho>' @ \<tau> \<in> Q"
      assume 3: "\<forall>\<rho>''\<in>tocks UNIV. \<rho>'' \<le>\<^sub>C \<rho>' @ \<sigma> \<longrightarrow> \<rho>'' \<le>\<^sub>C \<rho>'"
      assume 4: "\<rho> @ [X]\<^sub>R # [Tock]\<^sub>E # \<sigma>'' @ \<sigma>''' = \<rho>' @ \<sigma>"
      have "\<rho> @ [[X]\<^sub>R, [Tock]\<^sub>E] \<le>\<^sub>C \<rho>'"
        using 3 4 apply (erule_tac x="\<rho> @ [[X]\<^sub>R, [Tock]\<^sub>E]" in ballE, simp_all add: \<rho>_Tock_in_tocks)
        by (metis \<rho>_Tock_in_tocks tt_prefix.simps(1) tt_prefix.simps(2) tt_prefix_same_front)
      then show "\<rho> @ [[X]\<^sub>R, [Tock]\<^sub>E] \<in> Q"
        by (meson "2" TT1_def TT_TT1 assms(2) tt_prefix_concat tt_prefix_imp_prefix_subset)
    next
      fix \<rho>' \<sigma> \<tau>
      assume 1: "\<rho>' @ \<sigma> \<in> P"
      assume 2: "\<rho>' @ \<tau> \<in> Q"
      assume 3: "\<forall>\<rho>''\<in>tocks UNIV. \<rho>'' \<le>\<^sub>C \<rho>' @ \<tau> \<longrightarrow> \<rho>'' \<le>\<^sub>C \<rho>'"
      assume 4: "\<rho> @ [X]\<^sub>R # [Tock]\<^sub>E # \<sigma>'' @ \<sigma>''' = \<rho>' @ \<tau>"
      have "\<rho> @ [[X]\<^sub>R, [Tock]\<^sub>E] \<le>\<^sub>C \<rho>'"
        using 3 4 apply (erule_tac x="\<rho> @ [[X]\<^sub>R, [Tock]\<^sub>E]" in ballE, simp_all add: \<rho>_Tock_in_tocks)
        by (metis \<rho>_Tock_in_tocks tt_prefix.simps(1) tt_prefix.simps(2) tt_prefix_same_front)
      then show "\<rho> @ [[X]\<^sub>R, [Tock]\<^sub>E] \<in> Q"
        by (meson "2" TT1_def TT_TT1 assms(2) tt_prefix_concat tt_prefix_imp_prefix_subset)
    next
      fix \<rho>' \<sigma> \<tau>
      assume 1: "\<rho>' @ \<sigma> \<in> P"
      assume 2: "\<rho>' @ \<tau> \<in> Q"
      assume 3: "\<forall>\<rho>''\<in>tocks UNIV. \<rho>'' \<le>\<^sub>C \<rho>' @ \<tau> \<longrightarrow> \<rho>'' \<le>\<^sub>C \<rho>'"
      assume 4: "\<rho> @ [X]\<^sub>R # [Tock]\<^sub>E # \<sigma>'' @ \<sigma>''' = \<rho>' @ \<tau>"
      have "\<rho> @ [[X]\<^sub>R, [Tock]\<^sub>E] \<le>\<^sub>C \<rho>'"
        using 3 4 apply (erule_tac x="\<rho> @ [[X]\<^sub>R, [Tock]\<^sub>E]" in ballE, simp_all add: \<rho>_Tock_in_tocks)
        by (metis \<rho>_Tock_in_tocks tt_prefix.simps(1) tt_prefix.simps(2) tt_prefix_same_front)
      then show "\<rho> @ [[X]\<^sub>R, [Tock]\<^sub>E] \<in> P"
        by (meson "1" TT1_def TT_TT1 assms(1) tt_prefix_concat tt_prefix_imp_prefix_subset)
    qed
    then have set1: "{e. e = Tock \<and> \<rho> @ [[X]\<^sub>R, [e]\<^sub>E] \<in> P \<box>\<^sub>C Q} =
        {e. e = Tock \<and> \<rho> @ [[X]\<^sub>R, [e]\<^sub>E] \<in> P} \<union> {e. e = Tock \<and> \<rho> @ [[X]\<^sub>R, [e]\<^sub>E] \<in> Q}"
      unfolding ExtChoiceTT_def apply auto
      apply (rule_tac x="\<rho> @ [[X]\<^sub>R, [Tock]\<^sub>E]" in bexI, simp_all add: \<rho>_Tock_in_tocks)
      apply (rule_tac x="[]" in exI, simp, rule_tac x="[]" in exI, simp)
      apply (rule_tac x="\<rho> @ [[X]\<^sub>R, [Tock]\<^sub>E]" in bexI, simp_all add: \<rho>_Tock_in_tocks)
      apply (rule_tac x="[]" in exI, simp, rule_tac x="[]" in exI, simp)
      done
    have set2: "{e. e \<noteq> Tock \<and> \<rho> @ [[e]\<^sub>E] \<in> P \<box>\<^sub>C Q} =
        {e. e \<noteq> Tock \<and> \<rho> @ [[e]\<^sub>E] \<in> P} \<union> {e. e \<noteq> Tock \<and> \<rho> @ [[e]\<^sub>E] \<in> Q}"
      unfolding ExtChoiceTT_def apply auto
      apply (rule_tac x="\<rho>" in bexI, rule_tac x="[[x]\<^sub>E]" in exI, simp, rule_tac x="[]" in exI, simp)
      apply (metis TT1_def TT_TT1 \<rho>'_in_P_Q assms(2) case_assms(1) tt_prefix_concat tt_prefix_imp_prefix_subset tocks_tt_prefix_end_event)
      using \<rho>_\<sigma>_split case_assms(1) tocks_mid_refusal_front_in_tocks apply blast
      apply (rule_tac x="\<rho>" in bexI, rule_tac x="[]" in exI, simp)
      apply (metis TT1_def TT_TT1 \<rho>'_in_P_Q assms(1) case_assms(1) tt_prefix_concat tt_prefix_imp_prefix_subset tocks_tt_prefix_end_event)
      by (metis \<rho>_\<sigma>_split case_assms(1) tocks_mid_refusal_front_in_tocks)
    have "{e. e \<noteq> Tock \<and> \<rho> @ [[e]\<^sub>E] \<in> P \<box>\<^sub>C Q \<or> e = Tock \<and> \<rho> @ [[X]\<^sub>R, [e]\<^sub>E] \<in> P \<box>\<^sub>C Q} =
        {e. e \<noteq> Tock \<and> \<rho> @ [[e]\<^sub>E] \<in> P \<or> e = Tock \<and> \<rho> @ [[X]\<^sub>R, [e]\<^sub>E] \<in> P} \<union> {e. e \<noteq> Tock \<and> \<rho> @ [[e]\<^sub>E] \<in> Q \<or> e = Tock \<and> \<rho> @ [[X]\<^sub>R, [e]\<^sub>E] \<in> Q}"
      using set1 set2 by blast
    then have set3: "Y \<inter> ({e. e \<noteq> Tock \<and> \<rho> @ [[e]\<^sub>E] \<in> P \<or> e = Tock \<and> \<rho> @ [[X]\<^sub>R, [e]\<^sub>E] \<in> P} \<union> {e. e \<noteq> Tock \<and> \<rho> @ [[e]\<^sub>E] \<in> Q \<or> e = Tock \<and> \<rho> @ [[X]\<^sub>R, [e]\<^sub>E] \<in> Q}) = {}"
      using assm2 by auto
    have P_assm2: "Y \<inter> {e. e \<noteq> Tock \<and> \<rho> @ [[e]\<^sub>E] \<in> P \<or> e = Tock \<and> \<rho> @ [[X]\<^sub>R, [e]\<^sub>E] \<in> P} = {}"
      using set3 by blast
    have Q_assm2: "Y \<inter> {e. e \<noteq> Tock \<and> \<rho> @ [[e]\<^sub>E] \<in> Q \<or> e = Tock \<and> \<rho> @ [[X]\<^sub>R, [e]\<^sub>E] \<in> Q} = {}"
      using set3 by blast
    have \<rho>'_subset: "\<rho> @ [X]\<^sub>R # \<sigma>' \<subseteq>\<^sub>C \<rho> @ [X \<union> Y]\<^sub>R # \<sigma>'"
      by (metis tt_subset.simps(2) tt_subset_combine tt_subset_refl inf_sup_absorb inf_sup_ord(2))
    have A: "\<rho> @ [X \<union> Y]\<^sub>R # \<sigma>' \<in> tocks UNIV"
      by (metis \<rho>'_subset \<rho>_\<sigma>_split case_assms(1) tocks_tt_subset2)
    have \<rho>_X_\<sigma>'_longest_pretocks: "\<forall>t'\<in>tocks UNIV. t' \<le>\<^sub>C \<rho> @ [X]\<^sub>R # \<sigma> \<longrightarrow> t' \<le>\<^sub>C \<rho> @ [X]\<^sub>R # \<sigma>'"
      by (metis \<rho>_\<sigma>_split case_assms(1))
    then have B: "\<forall>t'\<in>tocks UNIV. t' \<le>\<^sub>C \<rho> @ [X \<union> Y]\<^sub>R # \<sigma> \<longrightarrow> t' \<le>\<^sub>C \<rho> @ [X \<union> Y]\<^sub>R # \<sigma>'"
      using \<rho>'_subset \<sigma>'''_def \<sigma>'_Tock_start tt_subset_longest_tocks4[where ?s1.0="\<rho> @ [X]\<^sub>R # \<sigma>'", where s1'="\<rho> @ [X \<union> Y]\<^sub>R # \<sigma>'"] by auto
    have "\<rho> @ [X]\<^sub>R # \<sigma> \<in> P \<or> \<rho> @ [X]\<^sub>R # \<sigma> \<in> Q"
      using assm1 unfolding ExtChoiceTT_def by auto
    then show "\<rho> @ [X \<union> Y]\<^sub>R # \<sigma> \<in> P \<box>\<^sub>C Q"
    proof auto
      assume in_P: "\<rho> @ [X]\<^sub>R # \<sigma> \<in> P"
      have 1: "\<rho> @ [X \<union> Y]\<^sub>R # \<sigma> \<in> P"
        using assms(3) P_assm2 in_P unfolding TT2_def by force
      have 2: "\<rho> @ [X \<union> Y]\<^sub>R # \<sigma>' \<in> Q"
        using assms(4) Q_assm2 \<rho>'_in_P_Q case_assms unfolding TT2_def by force
      show "\<rho> @ [X \<union> Y]\<^sub>R # \<sigma> \<in> P \<box>\<^sub>C Q"
      proof (cases "\<exists> Z. \<sigma>''' = [[Z]\<^sub>R]", auto)
        fix Z
        assume \<sigma>'''_is_ref: "\<sigma>''' = [[Z]\<^sub>R]"
        then have "\<exists> W. \<rho> @ [X]\<^sub>R # \<sigma>' @ [[W]\<^sub>R] \<in> Q \<and> (\<forall>e. (e \<in> W) = (e \<in> Z) \<or> e = Tock)"
          using assm1 in_P \<sigma>'''_def \<sigma>'_Tock_start unfolding ExtChoiceTT_def
        proof auto
          fix \<rho>' \<sigma>'''' \<tau> :: "'a ttobs list"
          assume 1: "\<forall>\<rho>''\<in>tocks UNIV. \<rho>'' \<le>\<^sub>C \<rho>' @ \<sigma>'''' \<longrightarrow> \<rho>'' \<le>\<^sub>C \<rho>'"
          assume 2: "\<rho> @ [X]\<^sub>R # [Tock]\<^sub>E # \<sigma>'' @ [[Z]\<^sub>R] = \<rho>' @ \<sigma>''''"
          assume 3: "\<rho>' \<in> tocks UNIV"
          assume 4: "\<forall>X. \<sigma>'''' = [[X]\<^sub>R] \<longrightarrow> (\<exists>Y. \<tau> = [[Y]\<^sub>R] \<and> (\<forall>e. (e \<in> X) = (e \<in> Y) \<or> e = Tock))"
          assume 5: "\<rho>' @ \<tau> \<in> Q"
          have "\<rho> @ [X]\<^sub>R # [Tock]\<^sub>E # \<sigma>'' \<le>\<^sub>C \<rho>'"
            by (metis 1 2 \<rho>_\<sigma>_split \<sigma>'''_def \<sigma>'''_is_ref \<sigma>'_Tock_start case_assms(1) tt_prefix_concat)
          then have \<rho>'_def: "\<rho>' = \<rho> @ [X]\<^sub>R # [Tock]\<^sub>E # \<sigma>''"
            using "2" "3" \<rho>_X_\<sigma>'_longest_pretocks \<sigma>'''_def \<sigma>'''_is_ref \<sigma>'_Tock_start tt_prefix_antisym tt_prefix_concat by fastforce
          then have "\<sigma>'''' = [[Z]\<^sub>R]"
            using "2" by auto
          then show "\<exists>W. \<rho> @ [X]\<^sub>R # [Tock]\<^sub>E # \<sigma>'' @ [[W]\<^sub>R] \<in> Q \<and> (\<forall>e. (e \<in> W) = (e \<in> Z) \<or> e = Tock)"
            using 4 5 \<rho>'_def by auto
        next
          fix \<rho>' \<sigma>'''' \<tau> :: "'a ttobs list"
          assume 1: "\<rho>' @ \<tau> \<in> Q" "\<rho> @ [X]\<^sub>R # [Tock]\<^sub>E # \<sigma>'' @ [[Z]\<^sub>R] = \<rho>' @ \<tau>"
          then show "\<exists>W. \<rho> @ [X]\<^sub>R # [Tock]\<^sub>E # \<sigma>'' @ [[W]\<^sub>R] \<in> Q \<and> (\<forall>e. (e \<in> W) = (e \<in> Z) \<or> e = Tock)"
            by force
        qed
        then obtain W where "\<rho> @ [X]\<^sub>R # \<sigma>' @ [[W]\<^sub>R] \<in> Q \<and> (\<forall>e. (e \<in> W) = (e \<in> Z) \<or> e = Tock)"
          by blast
        then have C: "\<rho> @ [X \<union> Y]\<^sub>R # \<sigma>' @ [[W]\<^sub>R] \<in> Q \<and> (\<forall>e. (e \<in> W) = (e \<in> Z) \<or> e = Tock)"
          using assms(4) Q_assm2 unfolding TT2_def by auto
        have D: "\<forall> t\<in>tocks UNIV. t \<le>\<^sub>C \<rho> @ [X \<union> Y]\<^sub>R # \<sigma>' @ [[W]\<^sub>R] \<longrightarrow> t \<le>\<^sub>C \<rho> @ [X \<union> Y]\<^sub>R # \<sigma>'"
          using tt_prefix_notfront_is_whole end_refusal_notin_tocks by force
        show "\<rho> @ [X \<union> Y]\<^sub>R # \<sigma> \<in> P \<box>\<^sub>C Q"
          unfolding ExtChoiceTT_def using in_P \<sigma>'''_is_ref \<sigma>'''_def \<sigma>'_Tock_start \<rho>_\<sigma>_split case_assms 1 2 A B C D apply auto
          by (rule_tac x="\<rho> @ [X \<union> Y]\<^sub>R # \<sigma>'" in bexI, auto, rule_tac x="\<sigma>'''" in exI, auto, rule_tac x="[[W]\<^sub>R]" in exI, blast)
      next
        show "\<forall>Z. \<sigma>''' \<noteq> [[Z]\<^sub>R] \<Longrightarrow> \<rho> @ [X \<union> Y]\<^sub>R # \<sigma> \<in> P \<box>\<^sub>C Q"
          unfolding ExtChoiceTT_def using in_P \<sigma>'''_def \<sigma>'_Tock_start \<rho>_\<sigma>_split case_assms 1 2 A B apply auto
          by (rule_tac x="\<rho> @ [X \<union> Y]\<^sub>R # \<sigma>'" in bexI, auto, rule_tac x="\<sigma>'''" in exI, auto, rule_tac x="[]" in exI, auto)
      qed
    next
      assume in_Q: "\<rho> @ [X]\<^sub>R # \<sigma> \<in> Q"
      have 1: "\<rho> @ [X \<union> Y]\<^sub>R # \<sigma> \<in> Q"
        using assms(4) Q_assm2 in_Q unfolding TT2_def by force
      have 2: "\<rho> @ [X \<union> Y]\<^sub>R # \<sigma>' \<in> P"
        using assms(3) P_assm2 \<rho>'_in_P_Q case_assms unfolding TT2_def by force
      show "\<rho> @ [X \<union> Y]\<^sub>R # \<sigma> \<in> P \<box>\<^sub>C Q"
      proof (cases "\<exists> Z. \<sigma>''' = [[Z]\<^sub>R]", auto)
        fix Z
        assume \<sigma>'''_is_ref: "\<sigma>''' = [[Z]\<^sub>R]"
        then have "\<exists> W. \<rho> @ [X]\<^sub>R # \<sigma>' @ [[W]\<^sub>R] \<in> P \<and> (\<forall>e. (e \<in> W) = (e \<in> Z) \<or> e = Tock)"
          using assm1 in_Q \<sigma>'''_def \<sigma>'_Tock_start unfolding ExtChoiceTT_def
        proof auto
          fix \<rho>' \<sigma>'''' \<tau> :: "'a ttobs list"
          assume 1: "\<rho>' @ \<sigma>'''' \<in> P" "\<rho> @ [X]\<^sub>R # [Tock]\<^sub>E # \<sigma>'' @ [[Z]\<^sub>R] = \<rho>' @ \<sigma>''''"
          then show "\<exists>W. \<rho> @ [X]\<^sub>R # [Tock]\<^sub>E # \<sigma>'' @ [[W]\<^sub>R] \<in> P \<and> (\<forall>e. (e \<in> W) = (e \<in> Z) \<or> e = Tock)"
            by force
        next
          fix \<rho>' \<sigma>'''' \<tau> :: "'a ttobs list"
          assume 1: "\<forall>\<rho>''\<in>tocks UNIV. \<rho>'' \<le>\<^sub>C \<rho>' @ \<tau> \<longrightarrow> \<rho>'' \<le>\<^sub>C \<rho>'"
          assume 2: "\<rho> @ [X]\<^sub>R # [Tock]\<^sub>E # \<sigma>'' @ [[Z]\<^sub>R] = \<rho>' @ \<tau>"
          assume 3: "\<rho>' \<in> tocks UNIV"
          assume 4: "\<forall>X. \<tau> = [[X]\<^sub>R] \<longrightarrow> (\<exists>Y. \<sigma>'''' = [[Y]\<^sub>R] \<and> (\<forall>e. (e \<in> X) = (e \<in> Y) \<or> e = Tock))"
          assume 5: "\<rho>' @ \<sigma>'''' \<in> P"
          have "\<rho> @ [X]\<^sub>R # [Tock]\<^sub>E # \<sigma>'' \<le>\<^sub>C \<rho>'"
            by (metis 1 2 \<rho>_\<sigma>_split \<sigma>'''_def \<sigma>'''_is_ref \<sigma>'_Tock_start case_assms(1) tt_prefix_concat)
          then have \<rho>'_def: "\<rho>' = \<rho> @ [X]\<^sub>R # [Tock]\<^sub>E # \<sigma>''"
            using "2" "3" \<rho>_X_\<sigma>'_longest_pretocks \<sigma>'''_def \<sigma>'''_is_ref \<sigma>'_Tock_start tt_prefix_antisym tt_prefix_concat by fastforce
          then have "\<tau> = [[Z]\<^sub>R]"
            using "2" by auto
          then show "\<exists>W. \<rho> @ [X]\<^sub>R # [Tock]\<^sub>E # \<sigma>'' @ [[W]\<^sub>R] \<in> P \<and> (\<forall>e. (e \<in> W) = (e \<in> Z) \<or> e = Tock)"
            using 4 5 \<rho>'_def by auto
        qed
        then obtain W where "\<rho> @ [X]\<^sub>R # \<sigma>' @ [[W]\<^sub>R] \<in> P \<and> (\<forall>e. (e \<in> W) = (e \<in> Z) \<or> e = Tock)"
          by blast
        then have C: "\<rho> @ [X \<union> Y]\<^sub>R # \<sigma>' @ [[W]\<^sub>R] \<in> P \<and> (\<forall>e. (e \<in> W) = (e \<in> Z) \<or> e = Tock)"
          using assms(3) P_assm2 unfolding TT2_def by auto
        have D: "\<forall> t\<in>tocks UNIV. t \<le>\<^sub>C \<rho> @ [X \<union> Y]\<^sub>R # \<sigma>' @ [[W]\<^sub>R] \<longrightarrow> t \<le>\<^sub>C \<rho> @ [X \<union> Y]\<^sub>R # \<sigma>'"
          using tt_prefix_notfront_is_whole end_refusal_notin_tocks by force
        show "\<rho> @ [X \<union> Y]\<^sub>R # \<sigma> \<in> P \<box>\<^sub>C Q"
          unfolding ExtChoiceTT_def using in_Q \<sigma>'''_is_ref \<sigma>'''_def \<sigma>'_Tock_start \<rho>_\<sigma>_split case_assms 1 2 A B C D apply auto
          by (rule_tac x="\<rho> @ [X \<union> Y]\<^sub>R # \<sigma>'" in bexI, auto, rule_tac x="[[W]\<^sub>R]" in exI, auto)
      next
        show "\<forall>Z. \<sigma>''' \<noteq> [[Z]\<^sub>R] \<Longrightarrow> \<rho> @ [X \<union> Y]\<^sub>R # \<sigma> \<in> P \<box>\<^sub>C Q"
          unfolding ExtChoiceTT_def using in_Q \<sigma>'''_def \<sigma>'_Tock_start \<rho>_\<sigma>_split case_assms 1 2 A B apply auto
          by (rule_tac x="\<rho> @ [X \<union> Y]\<^sub>R # \<sigma>'" in bexI, auto, rule_tac x="[]" in exI, auto)
      qed
    qed
  qed
qed

lemma TT3_ExtChoice: 
  assumes "TT3 P" "TT3 Q"
  shows "TT3 (P \<box>\<^sub>C Q)"
  using assms unfolding TT3_def ExtChoiceTT_def by auto

lemma TT4_ExtChoice:
  assumes "TT4 P" "TT4 Q"
  shows "TT4 (P \<box>\<^sub>C Q)"
  unfolding TT4_def ExtChoiceTT_def
proof auto
  fix \<rho>' \<sigma> \<tau> :: "'a ttobs list"
  assume assm1: "\<rho>' \<in> tocks UNIV"
  assume assm2: "\<rho>' @ \<sigma> \<in> P"
  assume assm3: "\<rho>' @ \<tau> \<in> Q"
  assume assm4: "\<forall>\<rho>''\<in>tocks UNIV. \<rho>'' \<le>\<^sub>C \<rho>' @ \<sigma> \<longrightarrow> \<rho>'' \<le>\<^sub>C \<rho>'"
  assume assm5: "\<forall>\<rho>''\<in>tocks UNIV. \<rho>'' \<le>\<^sub>C \<rho>' @ \<tau> \<longrightarrow> \<rho>'' \<le>\<^sub>C \<rho>'"
  assume assm6: "\<forall>X. \<sigma> = [[X]\<^sub>R] \<longrightarrow> (\<exists>Y. \<tau> = [[Y]\<^sub>R] \<and> (\<forall>e. (e \<in> X) = (e \<in> Y) \<or> e = Tock))"
  assume assm7: "\<forall>X. \<tau> = [[X]\<^sub>R] \<longrightarrow> (\<exists>Y. \<sigma> = [[Y]\<^sub>R] \<and> (\<forall>e. (e \<in> X) = (e \<in> Y) \<or> e = Tock))"
  have 1: "add_Tick_refusal_trace \<rho>' \<in> tocks UNIV"
    using TT4_def TT4_tocks assm1 by blast
  have 2: "add_Tick_refusal_trace \<rho>' @ add_Tick_refusal_trace \<sigma> \<in> P"
    using assms(1) assm2 unfolding TT4_def by (erule_tac x="\<rho>' @ \<sigma>" in allE, auto simp add: add_Tick_refusal_trace_concat)
  have 3: "add_Tick_refusal_trace \<rho>' @ add_Tick_refusal_trace \<tau> \<in> Q"
    using assms(2) assm3 unfolding TT4_def by (erule_tac x="\<rho>' @ \<tau>" in allE, auto simp add: add_Tick_refusal_trace_concat)
  have 4: "\<forall>\<rho>''\<in>tocks UNIV. \<rho>'' \<le>\<^sub>C add_Tick_refusal_trace \<rho>' @ add_Tick_refusal_trace \<sigma> \<longrightarrow> \<rho>'' \<le>\<^sub>C add_Tick_refusal_trace \<rho>'"
  proof auto
    fix \<rho>''
    assume assms2: "\<rho>'' \<in> tocks UNIV" "\<rho>'' \<le>\<^sub>C add_Tick_refusal_trace \<rho>' @ add_Tick_refusal_trace \<sigma>"
    then obtain \<rho>''' where \<rho>'''_assms: "\<rho>''' \<subseteq>\<^sub>C \<rho>'' \<and> \<rho>''' \<le>\<^sub>C \<rho>' @ \<sigma>"
      by (metis add_Tick_refusal_trace_concat add_Tick_refusal_trace_tt_subset tt_prefix_tt_subset)
    then have "\<rho>''' \<in> tocks UNIV"
      using assms2(1) tocks_tt_subset1 by blast
    then have "\<rho>''' \<le>\<^sub>C \<rho>'"
      using \<rho>'''_assms assm4 by blast
    then show "\<rho>'' \<le>\<^sub>C add_Tick_refusal_trace \<rho>'"
      by (smt \<rho>'''_assms add_Tick_refusal_trace_concat add_Tick_refusal_trace_tt_subset append_eq_append_conv assms2(2) tt_prefix_concat tt_prefix_split tt_subset_same_length)
  qed
  have 5: "\<forall>\<rho>''\<in>tocks UNIV. \<rho>'' \<le>\<^sub>C add_Tick_refusal_trace \<rho>' @ add_Tick_refusal_trace \<tau> \<longrightarrow> \<rho>'' \<le>\<^sub>C add_Tick_refusal_trace \<rho>'"
  proof auto
    fix \<rho>''
    assume assms2: "\<rho>'' \<in> tocks UNIV" "\<rho>'' \<le>\<^sub>C add_Tick_refusal_trace \<rho>' @ add_Tick_refusal_trace \<tau>"
    then obtain \<rho>''' where \<rho>'''_assms: "\<rho>''' \<subseteq>\<^sub>C \<rho>'' \<and> \<rho>''' \<le>\<^sub>C \<rho>' @ \<tau>"
      by (metis add_Tick_refusal_trace_concat add_Tick_refusal_trace_tt_subset tt_prefix_tt_subset)
    then have "\<rho>''' \<in> tocks UNIV"
      using assms2(1) tocks_tt_subset1 by blast
    then have "\<rho>''' \<le>\<^sub>C \<rho>'"
      using \<rho>'''_assms assm5 by blast
    then show "\<rho>'' \<le>\<^sub>C add_Tick_refusal_trace \<rho>'"
      by (smt \<rho>'''_assms add_Tick_refusal_trace_concat add_Tick_refusal_trace_tt_subset append_eq_append_conv assms2(2) tt_prefix_concat tt_prefix_split tt_subset_same_length)
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
  fix \<rho>' \<sigma> \<tau> :: "'a ttobs list"
  assume assm1: "\<rho>' \<in> tocks UNIV"
  assume assm2: "\<rho>' @ \<sigma> \<in> P"
  assume assm3: "\<rho>' @ \<tau> \<in> Q"
  assume assm4: "\<forall>\<rho>''\<in>tocks UNIV. \<rho>'' \<le>\<^sub>C \<rho>' @ \<sigma> \<longrightarrow> \<rho>'' \<le>\<^sub>C \<rho>'"
  assume assm5: "\<forall>\<rho>''\<in>tocks UNIV. \<rho>'' \<le>\<^sub>C \<rho>' @ \<tau> \<longrightarrow> \<rho>'' \<le>\<^sub>C \<rho>'"
  assume assm6: "\<forall>X. \<sigma> = [[X]\<^sub>R] \<longrightarrow> (\<exists>Y. \<tau> = [[Y]\<^sub>R] \<and> (\<forall>e. (e \<in> X) = (e \<in> Y) \<or> e = Tock))"
  assume assm7: "\<forall>X. \<tau> = [[X]\<^sub>R] \<longrightarrow> (\<exists>Y. \<sigma> = [[Y]\<^sub>R] \<and> (\<forall>e. (e \<in> X) = (e \<in> Y) \<or> e = Tock))"
  have 1: "add_Tick_refusal_trace \<rho>' \<in> tocks UNIV"
    using TT4_def TT4_tocks assm1 by blast
  have 2: "add_Tick_refusal_trace \<rho>' @ add_Tick_refusal_trace \<sigma> \<in> P"
    using assms(1) assm2 unfolding TT4_def by (erule_tac x="\<rho>' @ \<sigma>" in allE, auto simp add: add_Tick_refusal_trace_concat)
  have 3: "add_Tick_refusal_trace \<rho>' @ add_Tick_refusal_trace \<tau> \<in> Q"
    using assms(2) assm3 unfolding TT4_def by (erule_tac x="\<rho>' @ \<tau>" in allE, auto simp add: add_Tick_refusal_trace_concat)
  have 4: "\<forall>\<rho>''\<in>tocks UNIV. \<rho>'' \<le>\<^sub>C add_Tick_refusal_trace \<rho>' @ add_Tick_refusal_trace \<sigma> \<longrightarrow> \<rho>'' \<le>\<^sub>C add_Tick_refusal_trace \<rho>'"
  proof auto
    fix \<rho>''
    assume assms2: "\<rho>'' \<in> tocks UNIV" "\<rho>'' \<le>\<^sub>C add_Tick_refusal_trace \<rho>' @ add_Tick_refusal_trace \<sigma>"
    then obtain \<rho>''' where \<rho>'''_assms: "\<rho>''' \<subseteq>\<^sub>C \<rho>'' \<and> \<rho>''' \<le>\<^sub>C \<rho>' @ \<sigma>"
      by (metis add_Tick_refusal_trace_concat add_Tick_refusal_trace_tt_subset tt_prefix_tt_subset)
    then have "\<rho>''' \<in> tocks UNIV"
      using assms2(1) tocks_tt_subset1 by blast
    then have "\<rho>''' \<le>\<^sub>C \<rho>'"
      using \<rho>'''_assms assm4 by blast
    then show "\<rho>'' \<le>\<^sub>C add_Tick_refusal_trace \<rho>'"
      by (smt \<rho>'''_assms add_Tick_refusal_trace_concat add_Tick_refusal_trace_tt_subset append_eq_append_conv assms2(2) tt_prefix_concat tt_prefix_split tt_subset_same_length)
  qed
  have 5: "\<forall>\<rho>''\<in>tocks UNIV. \<rho>'' \<le>\<^sub>C add_Tick_refusal_trace \<rho>' @ add_Tick_refusal_trace \<tau> \<longrightarrow> \<rho>'' \<le>\<^sub>C add_Tick_refusal_trace \<rho>'"
  proof auto
    fix \<rho>''
    assume assms2: "\<rho>'' \<in> tocks UNIV" "\<rho>'' \<le>\<^sub>C add_Tick_refusal_trace \<rho>' @ add_Tick_refusal_trace \<tau>"
    then obtain \<rho>''' where \<rho>'''_assms: "\<rho>''' \<subseteq>\<^sub>C \<rho>'' \<and> \<rho>''' \<le>\<^sub>C \<rho>' @ \<tau>"
      by (metis add_Tick_refusal_trace_concat add_Tick_refusal_trace_tt_subset tt_prefix_tt_subset)
    then have "\<rho>''' \<in> tocks UNIV"
      using assms2(1) tocks_tt_subset1 by blast
    then have "\<rho>''' \<le>\<^sub>C \<rho>'"
      using \<rho>'''_assms assm5 by blast
    then show "\<rho>'' \<le>\<^sub>C add_Tick_refusal_trace \<rho>'"
      by (smt \<rho>'''_assms add_Tick_refusal_trace_concat add_Tick_refusal_trace_tt_subset append_eq_append_conv assms2(2) tt_prefix_concat tt_prefix_split tt_subset_same_length)
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

lemma TT_ExtChoice:
  assumes "TT P" "TT Q"
  shows "TT (P \<box>\<^sub>C Q)"
  unfolding TT_def apply auto
  apply (metis TT_def ExtChoiceTT_wf assms(1) assms(2))
  apply (simp add: TT0_ExtChoice assms(1) assms(2))
  apply (simp add: TT1_ExtChoice assms(1) assms(2))
  apply (simp add: TT2w_ExtChoice assms(1) assms(2))
  apply  (simp add: TT3_ExtChoice TT_TT3 assms(1) assms(2))
  done

lemma ExtChoiceTT_comm: "P \<box>\<^sub>C Q = Q \<box>\<^sub>C P"
  unfolding ExtChoiceTT_def by auto

(*lemma ExtChoiceTT_aux_assoc: 
  assumes "\<forall>t\<in>P. ttWF t" "\<forall>t\<in>Q. ttWF t" "\<forall>t\<in>R. ttWF t"
  shows "P \<box>\<^sup>C (Q \<box>\<^sup>C R) = (P \<box>\<^sup>C Q) \<box>\<^sup>C R"
  (is "?lhs = ?rhs")
proof -
  have "?lhs = {t. \<exists> \<rho>\<in>tocks(UNIV). \<exists> \<sigma> \<tau>. 
    \<rho> @ \<sigma> \<in> P \<and> \<rho> @ \<tau> \<in> (Q \<box>\<^sup>C R) \<and>
    (\<forall>\<rho>'\<in>tocks(UNIV). \<rho>' \<le>\<^sub>C \<rho> @ \<sigma> \<longrightarrow> \<rho>' \<le>\<^sub>C \<rho>) \<and>
    (\<forall>\<rho>'\<in>tocks(UNIV). \<rho>' \<le>\<^sub>C \<rho> @ \<tau> \<longrightarrow> \<rho>' \<le>\<^sub>C \<rho>) \<and>
    (((\<exists> X. \<sigma> = [[X]\<^sub>R]) \<or> (\<exists> X. \<tau> = [[X]\<^sub>R])) \<longrightarrow> \<rho> @ \<sigma> = \<rho> @ \<tau>) \<and>
    (t = \<rho> @ \<sigma> \<or> t = \<rho> @ \<tau>)}"
    unfolding ExtChoiceTT_aux_def by simp
  also have "... =  {t. \<exists> \<rho>\<in>tocks(UNIV). \<exists> \<sigma> \<tau>. 
    \<rho> @ \<sigma> \<in> (P \<box>\<^sup>C Q) \<and> \<rho> @ \<tau> \<in> R \<and>
    (\<forall>\<rho>'\<in>tocks(UNIV). \<rho>' \<le>\<^sub>C \<rho> @ \<sigma> \<longrightarrow> \<rho>' \<le>\<^sub>C \<rho>) \<and>
    (\<forall>\<rho>'\<in>tocks(UNIV). \<rho>' \<le>\<^sub>C \<rho> @ \<tau> \<longrightarrow> \<rho>' \<le>\<^sub>C \<rho>) \<and>
    (((\<exists> X. \<sigma> = [[X]\<^sub>R]) \<or> (\<exists> X. \<tau> = [[X]\<^sub>R])) \<longrightarrow> \<rho> @ \<sigma> = \<rho> @ \<tau>) \<and>
    (t = \<rho> @ \<sigma> \<or> t = \<rho> @ \<tau>)}"
  proof (safe)
    fix \<rho> \<sigma> \<tau> :: "'a ttobs list"
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
      using assm3 unfolding ExtChoiceTT_aux_def by (clarify, blast)
    have "\<rho> = \<rho>'"
      using additional_assms(6)
    proof auto
      assume case1: "\<rho> @ \<tau> = \<rho>' @ \<sigma>'"
      have "\<rho> \<le>\<^sub>C \<rho>'" by (metis additional_assms(4) assm1 case1 tt_prefix_concat)
      also have "\<rho>' \<le>\<^sub>C \<rho>" by (simp add: additional_assms(1) assm5 case1 tt_prefix_concat)
      then show "\<rho> = \<rho>'" by (simp add: calculation tt_prefix_antisym)
    next
      assume case1: "\<rho> @ \<tau> = \<rho>' @ \<tau>'"
      have "\<rho> \<le>\<^sub>C \<rho>'" by (metis additional_assms(5) assm1 case1 tt_prefix_concat)
      also have "\<rho>' \<le>\<^sub>C \<rho>" by (simp add: additional_assms(1) assm5 case1 tt_prefix_concat)
      then show "\<rho> = \<rho>'" by (simp add: calculation tt_prefix_antisym)
    qed
    then have "\<nexists>X. \<sigma> = [[X]\<^sub>R] \<Longrightarrow> \<exists>\<rho>'\<in>tocks UNIV.
              \<exists>\<sigma>' \<tau>. \<rho>' @ \<sigma>' \<in> P \<box>\<^sup>C Q \<and>
                     \<rho>' @ \<tau> \<in> R \<and>
                     (\<forall>\<rho>''\<in>tocks UNIV. \<rho>'' \<le>\<^sub>C \<rho>' @ \<sigma>' \<longrightarrow> \<rho>'' \<le>\<^sub>C \<rho>') \<and>
                     (\<forall>\<rho>''\<in>tocks UNIV. \<rho>'' \<le>\<^sub>C \<rho>' @ \<tau> \<longrightarrow> \<rho>'' \<le>\<^sub>C \<rho>') \<and>
                     ((\<exists>X. \<sigma>' = [[X]\<^sub>R]) \<or> (\<exists>X. \<tau> = [[X]\<^sub>R]) \<longrightarrow> \<rho>' @ \<sigma>' = \<rho>' @ \<tau>) \<and> (\<rho> @ \<sigma> = \<rho>' @ \<sigma>' \<or> \<rho> @ \<sigma> = \<rho>' @ \<tau>)"
      apply (rule_tac x="\<rho>" in bexI, rule_tac x="\<sigma>" in exI, rule_tac x="\<tau>'" in exI, safe)
      using assm1 assm2 assm4 assm5 assm7 additional_assms apply (simp_all)
      unfolding ExtChoiceTT_aux_def apply (safe)
      apply (rule_tac x="\<rho>" in bexI, rule_tac x="\<sigma>" in exI, rule_tac x="\<sigma>'" in exI, safe, blast, blast)+
      done
    then show "\<exists>X. \<sigma> = [[X]\<^sub>R]"
      using assm6 by blast
  next
    fix \<rho> \<sigma> \<tau> :: "'a ttobs list"
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
      using assm3 unfolding ExtChoiceTT_aux_def by (clarify, blast)
    have "\<rho> = \<rho>'"
      using additional_assms(6)
    proof auto
      assume case1: "\<rho> @ \<tau> = \<rho>' @ \<sigma>'"
      have "\<rho> \<le>\<^sub>C \<rho>'" by (metis additional_assms(4) assm1 case1 tt_prefix_concat)
      also have "\<rho>' \<le>\<^sub>C \<rho>" by (simp add: additional_assms(1) assm5 case1 tt_prefix_concat)
      then show "\<rho> = \<rho>'" by (simp add: calculation tt_prefix_antisym)
    next
      assume case1: "\<rho> @ \<tau> = \<rho>' @ \<tau>'"
      have "\<rho> \<le>\<^sub>C \<rho>'" by (metis additional_assms(5) assm1 case1 tt_prefix_concat)
      also have "\<rho>' \<le>\<^sub>C \<rho>" by (simp add: additional_assms(1) assm5 case1 tt_prefix_concat)
      then show "\<rho> = \<rho>'" by (simp add: calculation tt_prefix_antisym)
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
      unfolding ExtChoiceTT_aux_def apply (safe)
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
    fix \<rho> \<sigma> \<tau> :: "'a ttobs list"
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
      using assm3 unfolding ExtChoiceTT_aux_def by (clarify, blast)
    have "\<rho> = \<rho>'"
      using additional_assms(6)
    proof auto
      assume case1: "\<rho> @ \<tau> = \<rho>' @ \<sigma>'"
      have "\<rho> \<le>\<^sub>C \<rho>'" by (metis additional_assms(4) assm1 case1 tt_prefix_concat)
      also have "\<rho>' \<le>\<^sub>C \<rho>" by (simp add: additional_assms(1) assm5 case1 tt_prefix_concat)
      then show "\<rho> = \<rho>'" by (simp add: calculation tt_prefix_antisym)
    next
      assume case1: "\<rho> @ \<tau> = \<rho>' @ \<tau>'"
      have "\<rho> \<le>\<^sub>C \<rho>'" by (metis additional_assms(5) assm1 case1 tt_prefix_concat)
      also have "\<rho>' \<le>\<^sub>C \<rho>" by (simp add: additional_assms(1) assm5 case1 tt_prefix_concat)
      then show "\<rho> = \<rho>'" by (simp add: calculation tt_prefix_antisym)
    qed
    then have "\<nexists>X. \<sigma> = [[X]\<^sub>R] \<Longrightarrow> \<exists>\<rho>'\<in>tocks UNIV.
              \<exists>\<sigma> \<tau>'. \<rho>' @ \<sigma> \<in> P \<box>\<^sup>C Q \<and>
                     \<rho>' @ \<tau>' \<in> R \<and>
                     (\<forall>\<rho>''\<in>tocks UNIV. \<rho>'' \<le>\<^sub>C \<rho>' @ \<sigma> \<longrightarrow> \<rho>'' \<le>\<^sub>C \<rho>') \<and>
                     (\<forall>\<rho>''\<in>tocks UNIV. \<rho>'' \<le>\<^sub>C \<rho>' @ \<tau>' \<longrightarrow> \<rho>'' \<le>\<^sub>C \<rho>') \<and>
                     ((\<exists>X. \<sigma> = [[X]\<^sub>R]) \<or> (\<exists>X. \<tau>' = [[X]\<^sub>R]) \<longrightarrow> \<rho>' @ \<sigma> = \<rho>' @ \<tau>') \<and> (\<rho> @ \<tau> = \<rho>' @ \<sigma> \<or> \<rho> @ \<tau> = \<rho>' @ \<tau>')"
      apply (rule_tac x="\<rho>" in bexI, rule_tac x="\<sigma>'" in exI, rule_tac x="\<tau>'" in exI, safe)
      using assm1 assm2 assm4 assm5 assm7 additional_assms apply (simp_all)
      unfolding ExtChoiceTT_aux_def apply (safe)
      apply (rule_tac x="\<rho>" in bexI, rule_tac x="\<sigma>" in exI, rule_tac x="\<sigma>'" in exI, safe, blast, blast)+
      done
    then show "\<exists>X. \<sigma> = [[X]\<^sub>R]"
      using assm6 by blast
  next
    fix \<rho> \<sigma> \<tau> :: "'a ttobs list"
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
      using assm3 unfolding ExtChoiceTT_aux_def by (clarify, blast)
    have "\<rho> = \<rho>'"
      using additional_assms(6)
    proof auto
      assume case1: "\<rho> @ \<tau> = \<rho>' @ \<sigma>'"
      have "\<rho> \<le>\<^sub>C \<rho>'" by (metis additional_assms(4) assm1 case1 tt_prefix_concat)
      also have "\<rho>' \<le>\<^sub>C \<rho>" by (simp add: additional_assms(1) assm5 case1 tt_prefix_concat)
      then show "\<rho> = \<rho>'" by (simp add: calculation tt_prefix_antisym)
    next
      assume case1: "\<rho> @ \<tau> = \<rho>' @ \<tau>'"
      have "\<rho> \<le>\<^sub>C \<rho>'" by (metis additional_assms(5) assm1 case1 tt_prefix_concat)
      also have "\<rho>' \<le>\<^sub>C \<rho>" by (simp add: additional_assms(1) assm5 case1 tt_prefix_concat)
      then show "\<rho> = \<rho>'" by (simp add: calculation tt_prefix_antisym)
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
      unfolding ExtChoiceTT_aux_def apply (safe)
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
    fix \<rho> \<sigma> \<tau> :: "'a ttobs list"
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
      using assm2 unfolding ExtChoiceTT_aux_def by (clarify, blast)
    have "\<rho> = \<rho>'"
      using additional_assms(6)
    proof auto
      assume case1: "\<rho> @ \<sigma> = \<rho>' @ \<sigma>'"
      have "\<rho> \<le>\<^sub>C \<rho>'" by (metis additional_assms(4) assm1 case1 tt_prefix_concat)
      also have "\<rho>' \<le>\<^sub>C \<rho>" by (simp add: additional_assms(1) assm4 case1 tt_prefix_concat)
      then show "\<rho> = \<rho>'" by (simp add: calculation tt_prefix_antisym)
    next
      assume case1: "\<rho> @ \<sigma> = \<rho>' @ \<tau>'"
      have "\<rho> \<le>\<^sub>C \<rho>'" by (metis additional_assms(5) assm1 case1 tt_prefix_concat)
      also have "\<rho>' \<le>\<^sub>C \<rho>" by (simp add: additional_assms(1) assm4 case1 tt_prefix_concat)
      then show "\<rho> = \<rho>'" by (simp add: calculation tt_prefix_antisym)
    qed
    then have "\<nexists>X. \<sigma> = [[X]\<^sub>R] \<Longrightarrow> (\<exists>\<rho>'\<in>tocks UNIV.
              \<exists>\<sigma>' \<tau>. \<rho>' @ \<sigma>' \<in> P \<and>
                     \<rho>' @ \<tau> \<in> Q \<box>\<^sup>C R \<and>
                     (\<forall>\<rho>''\<in>tocks UNIV. \<rho>'' \<le>\<^sub>C \<rho>' @ \<sigma>' \<longrightarrow> \<rho>'' \<le>\<^sub>C \<rho>') \<and>
                     (\<forall>\<rho>''\<in>tocks UNIV. \<rho>'' \<le>\<^sub>C \<rho>' @ \<tau> \<longrightarrow> \<rho>'' \<le>\<^sub>C \<rho>') \<and>
                     ((\<exists>X. \<sigma>' = [[X]\<^sub>R]) \<or> (\<exists>X. \<tau> = [[X]\<^sub>R]) \<longrightarrow> \<rho>' @ \<sigma>' = \<rho>' @ \<tau>) \<and> (\<rho> @ \<sigma> = \<rho>' @ \<sigma>' \<or> \<rho> @ \<sigma> = \<rho>' @ \<tau>))"
      apply (rule_tac x="\<rho>" in bexI, rule_tac x="\<sigma>'" in exI, rule_tac x="\<tau>'" in exI, safe)
      using assm1 assm3 assm4 assm5 assm7 additional_assms apply (simp_all)
      unfolding ExtChoiceTT_aux_def apply (safe)
      apply (rule_tac x="\<rho>" in bexI, rule_tac x="\<tau>'" in exI, rule_tac x="\<tau>" in exI, safe, blast, blast)+
      done
    then show "\<exists>X. \<sigma> = [[X]\<^sub>R]"
      using assm6 by blast
  next
    fix \<rho> \<sigma> \<tau> :: "'a ttobs list"
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
      using assm2 unfolding ExtChoiceTT_aux_def by (clarify, blast)
    have "\<rho> = \<rho>'"
      using additional_assms(6)
    proof auto
      assume case1: "\<rho> @ \<tau> = \<rho>' @ \<sigma>'"
      have "\<rho> \<le>\<^sub>C \<rho>'" by (metis additional_assms(4) assm1 case1 tt_prefix_concat)
      also have "\<rho>' \<le>\<^sub>C \<rho>" by (simp add: additional_assms(1) assm5 case1 tt_prefix_concat)
      then show "\<rho> = \<rho>'" by (simp add: calculation tt_prefix_antisym)
    next
      assume case1: "\<rho> @ \<tau> = \<rho>' @ \<tau>'"
      have "\<rho> \<le>\<^sub>C \<rho>'" by (metis additional_assms(5) assm1 case1 tt_prefix_concat)
      also have "\<rho>' \<le>\<^sub>C \<rho>" by (simp add: additional_assms(1) assm5 case1 tt_prefix_concat)
      then show "\<rho> = \<rho>'" by (simp add: calculation tt_prefix_antisym)
    qed
    then show "\<exists>\<rho>'\<in>tocks UNIV.
          \<exists>\<sigma> \<tau>'. \<rho>' @ \<sigma> \<in> P \<and>
                 \<rho>' @ \<tau>' \<in> Q \<box>\<^sup>C R \<and>
                 (\<forall>\<rho>''\<in>tocks UNIV. \<rho>'' \<le>\<^sub>C \<rho>' @ \<sigma> \<longrightarrow> \<rho>'' \<le>\<^sub>C \<rho>') \<and>
                 (\<forall>\<rho>''\<in>tocks UNIV. \<rho>'' \<le>\<^sub>C \<rho>' @ \<tau>' \<longrightarrow> \<rho>'' \<le>\<^sub>C \<rho>') \<and>
                 ((\<exists>X. \<sigma> = [[X]\<^sub>R]) \<or> (\<exists>X. \<tau>' = [[X]\<^sub>R]) \<longrightarrow> \<rho>' @ \<sigma> = \<rho>' @ \<tau>') \<and> (\<rho> @ \<tau> = \<rho>' @ \<sigma> \<or> \<rho> @ \<tau> = \<rho>' @ \<tau>')"
      apply (rule_tac x="\<rho>" in bexI, rule_tac x="\<sigma>'" in exI, rule_tac x="\<tau>" in exI, safe)
      using assm1 assm3 assm4 assm5 additional_assms apply (simp_all)
      unfolding ExtChoiceTT_aux_def apply (safe)
      apply (rule_tac x="\<rho>" in bexI, rule_tac x="\<tau>'" in exI, rule_tac x="\<sigma>'" in exI, safe, blast, blast)+
      done
  next
    fix \<rho> \<sigma> \<tau> :: "'a ttobs list"
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
      using assm2 unfolding ExtChoiceTT_aux_def by (clarify, blast)
    have "\<rho> = \<rho>'"
      using additional_assms(6)
    proof auto
      assume case1: "\<rho> @ \<sigma> = \<rho>' @ \<sigma>'"
      have "\<rho> \<le>\<^sub>C \<rho>'" by (metis additional_assms(4) assm1 case1 tt_prefix_concat)
      also have "\<rho>' \<le>\<^sub>C \<rho>" by (simp add: additional_assms(1) assm4 case1 tt_prefix_concat)
      then show "\<rho> = \<rho>'" by (simp add: calculation tt_prefix_antisym)
    next
      assume case1: "\<rho> @ \<sigma> = \<rho>' @ \<tau>'"
      have "\<rho> \<le>\<^sub>C \<rho>'" by (metis additional_assms(5) assm1 case1 tt_prefix_concat)
      also have "\<rho>' \<le>\<^sub>C \<rho>" by (simp add: additional_assms(1) assm4 case1 tt_prefix_concat)
      then show "\<rho> = \<rho>'" by (simp add: calculation tt_prefix_antisym)
    qed
    then have "\<nexists>X. \<sigma> = [[X]\<^sub>R] \<Longrightarrow> (\<exists>\<rho>'\<in>tocks UNIV.
              \<exists>\<sigma> \<tau>'. \<rho>' @ \<sigma> \<in> P \<and>
                     \<rho>' @ \<tau>' \<in> Q \<box>\<^sup>C R \<and>
                     (\<forall>\<rho>''\<in>tocks UNIV. \<rho>'' \<le>\<^sub>C \<rho>' @ \<sigma> \<longrightarrow> \<rho>'' \<le>\<^sub>C \<rho>') \<and>
                     (\<forall>\<rho>''\<in>tocks UNIV. \<rho>'' \<le>\<^sub>C \<rho>' @ \<tau>' \<longrightarrow> \<rho>'' \<le>\<^sub>C \<rho>') \<and>
                     ((\<exists>X. \<sigma> = [[X]\<^sub>R]) \<or> (\<exists>X. \<tau>' = [[X]\<^sub>R]) \<longrightarrow> \<rho>' @ \<sigma> = \<rho>' @ \<tau>') \<and> (\<rho> @ \<tau> = \<rho>' @ \<sigma> \<or> \<rho> @ \<tau> = \<rho>' @ \<tau>'))"
      apply (rule_tac x="\<rho>" in bexI, rule_tac x="\<sigma>'" in exI, rule_tac x="\<tau>" in exI, safe)
      using assm1 assm3 assm4 assm5 assm7 additional_assms apply (simp_all)
      unfolding ExtChoiceTT_aux_def apply (safe)
      apply (rule_tac x="\<rho>" in bexI, rule_tac x="\<tau>'" in exI, rule_tac x="\<tau>" in exI, safe, blast+)
      done
    then show "\<exists>X. \<sigma> = [[X]\<^sub>R]"
      using assm6 by blast
  next
    fix \<rho> \<sigma> \<tau> :: "'a ttobs list"
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
      using assm2 unfolding ExtChoiceTT_aux_def by (clarify, blast)
    have "\<rho> = \<rho>'"
      using additional_assms(6)
    proof auto
      assume case1: "\<rho> @ \<tau> = \<rho>' @ \<sigma>'"
      have "\<rho> \<le>\<^sub>C \<rho>'" by (metis additional_assms(4) assm1 case1 tt_prefix_concat)
      also have "\<rho>' \<le>\<^sub>C \<rho>" by (simp add: additional_assms(1) assm5 case1 tt_prefix_concat)
      then show "\<rho> = \<rho>'" by (simp add: calculation tt_prefix_antisym)
    next
      assume case1: "\<rho> @ \<tau> = \<rho>' @ \<tau>'"
      have "\<rho> \<le>\<^sub>C \<rho>'" by (metis additional_assms(5) assm1 case1 tt_prefix_concat)
      also have "\<rho>' \<le>\<^sub>C \<rho>" by (simp add: additional_assms(1) assm5 case1 tt_prefix_concat)
      then show "\<rho> = \<rho>'" by (simp add: calculation tt_prefix_antisym)
    qed
    then show "\<exists>\<rho>'\<in>tocks UNIV.
          \<exists>\<sigma> \<tau>'. \<rho>' @ \<sigma> \<in> P \<and>
                 \<rho>' @ \<tau>' \<in> Q \<box>\<^sup>C R \<and>
                 (\<forall>\<rho>''\<in>tocks UNIV. \<rho>'' \<le>\<^sub>C \<rho>' @ \<sigma> \<longrightarrow> \<rho>'' \<le>\<^sub>C \<rho>') \<and>
                 (\<forall>\<rho>''\<in>tocks UNIV. \<rho>'' \<le>\<^sub>C \<rho>' @ \<tau>' \<longrightarrow> \<rho>'' \<le>\<^sub>C \<rho>') \<and>
                 ((\<exists>X. \<sigma> = [[X]\<^sub>R]) \<or> (\<exists>X. \<tau>' = [[X]\<^sub>R]) \<longrightarrow> \<rho>' @ \<sigma> = \<rho>' @ \<tau>') \<and> (\<rho> @ \<tau> = \<rho>' @ \<sigma> \<or> \<rho> @ \<tau> = \<rho>' @ \<tau>')"
      apply (rule_tac x="\<rho>" in bexI, rule_tac x="\<sigma>'" in exI, rule_tac x="\<tau>" in exI, safe)
      using assm1 assm3 assm4 assm5 additional_assms apply (simp_all)
      unfolding ExtChoiceTT_aux_def apply (safe)
      apply (rule_tac x="\<rho>" in bexI, rule_tac x="\<tau>'" in exI, rule_tac x="\<sigma>'" in exI, safe, blast, blast)+
      done
  qed
  also have "... = ?rhs"
    unfolding ExtChoiceTT_aux_def by simp
  then show ?thesis
    using calculation by auto
qed*)

lemma ExtChoiceTT_union_dist: "P \<box>\<^sub>C (Q \<union> R) = (P \<box>\<^sub>C Q) \<union> (P \<box>\<^sub>C R)"
  unfolding ExtChoiceTT_def by (safe, blast+)

lemma ExtChoice_subset_union: "P \<box>\<^sub>C Q \<subseteq> P \<union> Q"
  unfolding ExtChoiceTT_def by auto

lemma ExtChoice_idempotent: "TT P \<Longrightarrow> P \<box>\<^sub>C P = P"
  unfolding ExtChoiceTT_def apply auto
  using TT_wf split_tocks_longest by fastforce

lemma ExtChoice_Union_dist1:
  "X \<noteq> {} \<Longrightarrow> P \<box>\<^sub>C \<Union>X = \<Union>{R. \<exists>Q. Q \<in> X \<and> R = P \<box>\<^sub>C Q}"
  unfolding ExtChoiceTT_def by auto

lemma ExtChoice_Union_dist2:
  "X \<noteq> {} \<Longrightarrow> \<Union>X \<box>\<^sub>C Q = \<Union>{R. \<exists>P. P \<in> X \<and> R = P \<box>\<^sub>C Q}"
  unfolding ExtChoiceTT_def by auto

lemma ExtChoice_mono1: 
  "P \<sqsubseteq>\<^sub>C Q \<Longrightarrow> P \<box>\<^sub>C R \<sqsubseteq>\<^sub>C Q \<box>\<^sub>C R"
  unfolding RefinesTT_def ExtChoiceTT_def by auto

lemma ExtChoice_mono2: 
  "P \<sqsubseteq>\<^sub>C Q \<Longrightarrow> R \<box>\<^sub>C P \<sqsubseteq>\<^sub>C R \<box>\<^sub>C Q"
  unfolding RefinesTT_def ExtChoiceTT_def by auto

end
