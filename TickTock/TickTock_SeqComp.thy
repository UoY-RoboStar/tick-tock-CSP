theory TickTock_SeqComp
  imports TickTock_Core
begin

subsection {* Sequential Composition *}

text_raw \<open>\DefineSnippet{SeqCompTT}{\<close>
definition SeqCompTT :: "'e ttprocess \<Rightarrow> 'e ttprocess \<Rightarrow> 'e ttprocess" (infixl ";\<^sub>C" 60) where
  "P ;\<^sub>C Q = {\<rho>\<in>P. \<nexists> s. \<rho> = s @ [[Tick]\<^sub>E]} 
            \<union> {\<rho>. \<exists> s t. s @ [[Tick]\<^sub>E] \<in> P \<and> t \<in> Q \<and> \<rho> = s @ t}"
text_raw \<open>}%EndSnippet\<close>

text_raw \<open>\DefineSnippet{SeqComp_wf}{\<close>
lemma SeqComp_wf: "\<forall> t\<in>P. ttWF t \<Longrightarrow> \<forall> t\<in>Q. ttWF t \<Longrightarrow> \<forall> t \<in> P ;\<^sub>C Q. ttWF t"
  unfolding SeqCompTT_def
proof auto
  fix s ta
  assume "\<forall>x\<in>P. ttWF x" "s @ [[Tick]\<^sub>E] \<in> P"
  then have 1: "ttWF (s @ [[Tick]\<^sub>E])"
    by auto
  assume "\<forall>x\<in>Q. ttWF x" "ta \<in> Q"
  then have 2: "ttWF ta"
    by auto
  from 1 2 show "ttWF (s @ ta)"
    by (induct s rule:ttWF.induct, auto)
qed
text_raw \<open>}%EndSnippet\<close>

lemma TT0_SeqComp: "TT0 P \<Longrightarrow> TT0 Q \<Longrightarrow> TT0 (P ;\<^sub>C Q)"
  unfolding SeqCompTT_def TT0_def by blast

lemma TT1_SeqComp: 
  assumes "\<forall>t\<in>P. ttWF t" "TT1 P" "TT1 Q"
  shows "TT1 (P ;\<^sub>C Q)"
  unfolding SeqCompTT_def TT1_def
proof (auto)
  fix \<rho> \<sigma> :: "'a ttobs list"
  show "\<rho> \<lesssim>\<^sub>C \<sigma> \<Longrightarrow> \<sigma> \<in> P \<Longrightarrow> \<rho> \<in> P"
    using TT1_def assms(2) by blast
next
  fix \<sigma> s :: "'a ttobs list"
  assume case_assms: "s @ [[Tick]\<^sub>E] \<lesssim>\<^sub>C \<sigma>" "\<sigma> \<in> P"
  then obtain s' t where \<sigma>_assms: "\<sigma> = s' @ t \<and> s @ [[Tick]\<^sub>E] \<subseteq>\<^sub>C s'"
    by (meson tt_prefix_split tt_prefix_subset_imp_tt_subset_tt_prefix)
  then have "\<exists> s'' x. s' = s'' @ x \<and> [[Tick]\<^sub>E] \<subseteq>\<^sub>C x"
    using tt_subset_split2 by blast
  then obtain s'' where "\<sigma> = s'' @ [[Tick]\<^sub>E] @ t"
    by (auto, case_tac x rule:ttWF.cases, auto simp add: \<sigma>_assms)
  then have "ttWF \<sigma> \<Longrightarrow> \<sigma> = s'' @ [[Tick]\<^sub>E]"
  proof auto
    show "ttWF (s'' @ [Tick]\<^sub>E # t) \<Longrightarrow> t = []"
      by (induct s'' rule:ttWF.induct, auto, cases t, auto)
  qed
  then have "\<sigma> = s'' @ [[Tick]\<^sub>E]"
    using assms(1) case_assms(2) by blast
  then show "\<forall>s. \<sigma> \<noteq> s @ [[Tick]\<^sub>E] \<Longrightarrow> False"
    by auto
next
  fix \<rho> \<sigma> s t :: "'a ttobs list"
  have assm1: "\<forall>\<rho> \<sigma>. \<rho> \<lesssim>\<^sub>C \<sigma> \<and> \<sigma> \<in> P \<longrightarrow> \<rho> \<in> P"
    using TT1_def assms(2) by blast
  have assm2: "\<forall>\<rho> \<sigma>. \<rho> \<lesssim>\<^sub>C \<sigma> \<and> \<sigma> \<in> Q \<longrightarrow> \<rho> \<in> Q"
    using TT1_def assms(3) by blast
  assume assm3: "\<forall>s. s @ [[Tick]\<^sub>E] \<in> P \<longrightarrow> (\<forall>t. t \<in> Q \<longrightarrow> \<rho> \<noteq> s @ t)"
  assume assm4: "\<rho> \<lesssim>\<^sub>C s @ t"
  assume assm5: "s @ [[Tick]\<^sub>E] \<in> P"
  assume assm6: "t \<in> Q"
  obtain r where 1: "\<rho> \<subseteq>\<^sub>C r \<and> r \<le>\<^sub>C s @ t"
    using assm4 tt_prefix_subset_imp_tt_subset_tt_prefix by blast
  then obtain t' where 2: "(r = s @ t' \<and> t' \<le>\<^sub>C t) \<or> r \<le>\<^sub>C s"
    using tt_prefix_append_split by blast
  then show "\<rho> \<in> P"
  proof auto
    assume case_assms: "r = s @ t'" "t' \<le>\<^sub>C t"
    obtain s' t'' where \<rho>_assms: "\<rho> = s' @ t'' \<and> s' \<subseteq>\<^sub>C s \<and> t'' \<subseteq>\<^sub>C t'"
      using "1" case_assms(1) tt_subset_split by blast
    have "s' @ [[Tick]\<^sub>E] \<in> P"
      using \<rho>_assms assm1 assm5 tt_subset_end_event tt_subset_imp_prefix_subset by blast
    also have "t'' \<in> Q"
      using \<rho>_assms assm2 assm6 case_assms(2) tt_prefix_imp_prefix_subset tt_subset_imp_prefix_subset by blast
    then show "\<rho> \<in> P"
      using \<rho>_assms assm3 calculation by blast
  next
    show "r \<le>\<^sub>C s \<Longrightarrow> \<rho> \<in> P"
      by (meson "1" assm1 assm5 tt_prefix_concat tt_prefix_imp_prefix_subset tt_subset_imp_prefix_subset)
  qed
next
  fix s t sa :: "'a ttobs list"
  have assm1: "\<forall>\<rho> \<sigma>. \<rho> \<lesssim>\<^sub>C \<sigma> \<and> \<sigma> \<in> P \<longrightarrow> \<rho> \<in> P"
    using TT1_def assms(2) by blast
  have assm2: "\<forall>\<rho> \<sigma>. \<rho> \<lesssim>\<^sub>C \<sigma> \<and> \<sigma> \<in> Q \<longrightarrow> \<rho> \<in> Q"
    using TT1_def assms(3) by blast
  assume case_assms: "sa @ [[Tick]\<^sub>E] \<lesssim>\<^sub>C s @ t" "s @ [[Tick]\<^sub>E] \<in> P" "t \<in> Q"
  obtain r where 1: "sa @ [[Tick]\<^sub>E] \<subseteq>\<^sub>C r \<and> r \<le>\<^sub>C s @ t"
    using case_assms(1) tt_prefix_subset_imp_tt_subset_tt_prefix by blast
  then obtain t' where 2: "(r = s @ t' \<and> t' \<le>\<^sub>C t) \<or> r \<le>\<^sub>C s"
    using tt_prefix_append_split by blast
  then show "\<forall>s. s @ [[Tick]\<^sub>E] \<in> P \<longrightarrow> (\<forall>t. t \<in> Q \<longrightarrow> sa @ [[Tick]\<^sub>E] \<noteq> s @ t) \<Longrightarrow> False"
  proof auto
    assume case_assms2: "r = s @ t'" "t' \<le>\<^sub>C t"
    obtain s' t'' where \<rho>_assms: "sa @ [[Tick]\<^sub>E] = s' @ t'' \<and> s' \<subseteq>\<^sub>C s \<and> t'' \<subseteq>\<^sub>C t'"
      using "1" case_assms2(1) tt_subset_split by blast
    have "s' @ [[Tick]\<^sub>E] \<in> P"
      using \<rho>_assms assm1 case_assms(2) tt_subset_end_event tt_subset_imp_prefix_subset by blast
    also have "t'' \<in> Q"
      using \<rho>_assms assm2 case_assms(3) case_assms2(2) tt_prefix_imp_prefix_subset tt_subset_imp_prefix_subset by blast
    then show "\<forall>s. s @ [[Tick]\<^sub>E] \<in> P \<longrightarrow> (\<forall>t. t \<in> Q \<longrightarrow> sa @ [[Tick]\<^sub>E] \<noteq> s @ t) \<Longrightarrow> False"
      using \<rho>_assms case_assms calculation by blast
  next
    have "\<exists> r1 r2. r = r1 @ r2 \<and> sa \<subseteq>\<^sub>C r1 \<and> [[Tick]\<^sub>E] \<subseteq>\<^sub>C r2"
      by (simp add: "1" tt_subset_split2)
    then obtain r' where "r = r' @ [[Tick]\<^sub>E]"
      by (auto, case_tac r2 rule:ttWF.cases, auto)
    also assume "r \<le>\<^sub>C s"
    then obtain s' where "r' @ [[Tick]\<^sub>E] @ s' @ [[Tick]\<^sub>E] \<in> P"
      using calculation case_assms(2) tt_prefix_split by fastforce
    then have "ttWF (r' @ [[Tick]\<^sub>E] @ s' @ [[Tick]\<^sub>E])"
      using assms(1) by blast
    then show "False"
      by (induct r' rule:ttWF.induct, auto, induct s' rule:ttWF.induct, auto)
  qed
qed


lemma TT2w_SeqComp: "TT4w P \<Longrightarrow> TT P \<Longrightarrow> TT Q \<Longrightarrow> TT2w (P ;\<^sub>C Q)"
  unfolding SeqCompTT_def TT2w_def
proof auto
  fix \<rho> X Y
  assume assm1: "Y \<inter> {e. e \<noteq> Tock \<and> (\<rho> @ [[e]\<^sub>E] \<in> P \<and> e \<noteq> Tick \<or> (\<exists>s. s @ [[Tick]\<^sub>E] \<in> P \<and> (\<exists>t. t \<in> Q \<and> \<rho> @ [[e]\<^sub>E] = s @ t))) \<or>
           e = Tock \<and> (\<rho> @ [[X]\<^sub>R, [e]\<^sub>E] \<in> P \<and> e \<noteq> Tick \<or> (\<exists>s. s @ [[Tick]\<^sub>E] \<in> P \<and> (\<exists>t. t \<in> Q \<and> \<rho> @ [[X]\<^sub>R, [e]\<^sub>E] = s @ t)))} = {}"
  assume assm2: "TT P"
  assume assm3: "\<rho> @ [[X]\<^sub>R] \<in> P"
  assume assm4: "TT4w P"
  have "Y \<inter> {e. e \<noteq> Tock \<and> (\<rho> @ [[e]\<^sub>E] \<in> P \<and> e \<noteq> Tick \<or> (\<exists>s. s @ [[Tick]\<^sub>E] \<in> P \<and> (\<exists>t. t \<in> Q \<and> \<rho> @ [[e]\<^sub>E] = s @ t))) \<or>
      e = Tock \<and> (\<rho> @ [[X]\<^sub>R, [e]\<^sub>E] \<in> P \<and> e \<noteq> Tick \<or> (\<exists>s. s @ [[Tick]\<^sub>E] \<in> P \<and> (\<exists>t. t \<in> Q \<and> \<rho> @ [[X]\<^sub>R, [e]\<^sub>E] = s @ t)))}
    = Y \<inter> ({e. e \<noteq> Tock \<and> \<rho> @ [[e]\<^sub>E] \<in> P \<and> e \<noteq> Tick \<or> e = Tock \<and> \<rho> @ [[X]\<^sub>R, [e]\<^sub>E] \<in> P \<and> e \<noteq> Tick}
      \<union> {e. e \<noteq> Tock \<and> (\<exists>s. s @ [[Tick]\<^sub>E] \<in> P \<and> (\<exists>t. t \<in> Q \<and> \<rho> @ [[e]\<^sub>E] = s @ t)) \<or>
        e = Tock \<and> (\<exists>s. s @ [[Tick]\<^sub>E] \<in> P \<and> (\<exists>t. t \<in> Q \<and> \<rho> @ [[X]\<^sub>R, [e]\<^sub>E] = s @ t))})"
    by auto
  then have "Y \<inter> ({e. e \<noteq> Tock \<and> \<rho> @ [[e]\<^sub>E] \<in> P \<and> e \<noteq> Tick \<or> e = Tock \<and> \<rho> @ [[X]\<^sub>R, [e]\<^sub>E] \<in> P \<and> e \<noteq> Tick}
      \<union> {e. e \<noteq> Tock \<and> (\<exists>s. s @ [[Tick]\<^sub>E] \<in> P \<and> (\<exists>t. t \<in> Q \<and> \<rho> @ [[e]\<^sub>E] = s @ t)) \<or>
        e = Tock \<and> (\<exists>s. s @ [[Tick]\<^sub>E] \<in> P \<and> (\<exists>t. t \<in> Q \<and> \<rho> @ [[X]\<^sub>R, [e]\<^sub>E] = s @ t))}) = {}"
    using assm1 by auto
  then have 1: "(Y \<inter> {e. e \<noteq> Tock \<and> \<rho> @ [[e]\<^sub>E] \<in> P \<and> e \<noteq> Tick \<or> e = Tock \<and> \<rho> @ [[X]\<^sub>R, [e]\<^sub>E] \<in> P \<and> e \<noteq> Tick})
      \<union> (Y \<inter> {e. e \<noteq> Tock \<and> (\<exists>s. s @ [[Tick]\<^sub>E] \<in> P \<and> (\<exists>t. t \<in> Q \<and> \<rho> @ [[e]\<^sub>E] = s @ t)) \<or>
        e = Tock \<and> (\<exists>s. s @ [[Tick]\<^sub>E] \<in> P \<and> (\<exists>t. t \<in> Q \<and> \<rho> @ [[X]\<^sub>R, [e]\<^sub>E] = s @ t))}) = {}"
    by (simp add: Int_Un_distrib)
  have TT2w_P: "TT2w P"
    using assm2 TT_TT2w by auto
  have "{e\<in>Y. e \<noteq> Tick} \<inter> {e. e \<noteq> Tock \<and> \<rho> @ [[e]\<^sub>E] \<in> P \<or> e = Tock \<and> \<rho> @ [[X]\<^sub>R, [e]\<^sub>E] \<in> P} = {}"
    using 1 by blast
  then have 2: "\<rho> @ [[X \<union> {e\<in>Y. e \<noteq> Tick}]\<^sub>R] \<in> P"
    using TT2w_P assm3 unfolding TT2w_def by auto
  show "\<rho> @ [[X \<union> Y]\<^sub>R] \<in> P"
  proof (cases "Tick \<in> Y")
    assume case_assm: "Tick \<in> Y"
    have "\<rho> @ [[X \<union> {e\<in>Y. e \<noteq> Tick} \<union> {Tick}]\<^sub>R] \<in> P"
      using 2 assm4 unfolding TT4w_def by auto
    also have "X \<union> {e\<in>Y. e \<noteq> Tick} \<union> {Tick} = X \<union> Y"
      using case_assm by blast
    then show "\<rho> @ [[X \<union> Y]\<^sub>R] \<in> P"
      using calculation by auto
  next
    assume "Tick \<notin> Y"
    then have "X \<union> {e\<in>Y. e \<noteq> Tick} = X \<union> Y"
      by blast
    then show "\<rho> @ [[X \<union> Y]\<^sub>R] \<in> P"
      using 2 by auto
  qed
next
  fix \<rho> X Y s t
  assume assm1: "Y \<inter> {e. e \<noteq> Tock \<and> (\<rho> @ [[e]\<^sub>E] \<in> P \<and> e \<noteq> Tick \<or> (\<exists>s. s @ [[Tick]\<^sub>E] \<in> P \<and> (\<exists>t. t \<in> Q \<and> \<rho> @ [[e]\<^sub>E] = s @ t))) \<or>
    e = Tock \<and> (\<rho> @ [[X]\<^sub>R, [e]\<^sub>E] \<in> P \<and> e \<noteq> Tick \<or> (\<exists>s. s @ [[Tick]\<^sub>E] \<in> P \<and> (\<exists>t. t \<in> Q \<and> \<rho> @ [[X]\<^sub>R, [e]\<^sub>E] = s @ t)))} = {}"
  assume assm2: "TT P"
  assume assm3: "TT Q"
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
    then have "ttWF (\<rho> @ [[X]\<^sub>R, [Tick]\<^sub>E])"
      using TT_wf assm2 by blast
    then have "False"
      by (induct \<rho> rule:ttWF.induct, auto)
    then show "\<rho> @ [[X \<union> Y]\<^sub>R] \<in> P"
      by auto
  next
    fix t'
    assume case_assm: "t = t' @ [[X]\<^sub>R]"
    then have 1: "{e. e \<noteq> Tock \<and> t' @ [[e]\<^sub>E] \<in> Q \<or> e = Tock \<and> t' @ [[X]\<^sub>R, [e]\<^sub>E] \<in> Q}
      \<subseteq> {e. e \<noteq> Tock \<and> (\<exists>s. s @ [[Tick]\<^sub>E] \<in> P \<and> (\<exists>t. t \<in> Q \<and> \<rho> @ [[e]\<^sub>E] = s @ t)) \<or>
          e = Tock \<and> (\<exists>s. s @ [[Tick]\<^sub>E] \<in> P \<and> (\<exists>t. t \<in> Q \<and> \<rho> @ [[X]\<^sub>R, [e]\<^sub>E] = s @ t))}"
      using assm5 assm7 by auto
    have "Y \<inter> {e. e \<noteq> Tock \<and> (\<rho> @ [[e]\<^sub>E] \<in> P \<and> e \<noteq> Tick \<or> (\<exists>s. s @ [[Tick]\<^sub>E] \<in> P \<and> (\<exists>t. t \<in> Q \<and> \<rho> @ [[e]\<^sub>E] = s @ t))) \<or>
        e = Tock \<and> (\<rho> @ [[X]\<^sub>R, [e]\<^sub>E] \<in> P \<and> e \<noteq> Tick \<or> (\<exists>s. s @ [[Tick]\<^sub>E] \<in> P \<and> (\<exists>t. t \<in> Q \<and> \<rho> @ [[X]\<^sub>R, [e]\<^sub>E] = s @ t)))}
      = Y \<inter> ({e. e \<noteq> Tock \<and> \<rho> @ [[e]\<^sub>E] \<in> P \<and> e \<noteq> Tick \<or> e = Tock \<and> \<rho> @ [[X]\<^sub>R, [e]\<^sub>E] \<in> P}
        \<union> {e. e \<noteq> Tock \<and> (\<exists>s. s @ [[Tick]\<^sub>E] \<in> P \<and> (\<exists>t. t \<in> Q \<and> \<rho> @ [[e]\<^sub>E] = s @ t)) \<or>
          e = Tock \<and> (\<exists>s. s @ [[Tick]\<^sub>E] \<in> P \<and> (\<exists>t. t \<in> Q \<and> \<rho> @ [[X]\<^sub>R, [e]\<^sub>E] = s @ t))})"
      by auto
    then have "Y \<inter> ({e. e \<noteq> Tock \<and> \<rho> @ [[e]\<^sub>E] \<in> P \<and> e \<noteq> Tick \<or> e = Tock \<and> \<rho> @ [[X]\<^sub>R, [e]\<^sub>E] \<in> P}
        \<union> {e. e \<noteq> Tock \<and> (\<exists>s. s @ [[Tick]\<^sub>E] \<in> P \<and> (\<exists>t. t \<in> Q \<and> \<rho> @ [[e]\<^sub>E] = s @ t)) \<or>
          e = Tock \<and> (\<exists>s. s @ [[Tick]\<^sub>E] \<in> P \<and> (\<exists>t. t \<in> Q \<and> \<rho> @ [[X]\<^sub>R, [e]\<^sub>E] = s @ t))}) = {}"
      using assm1 by auto
    then have "(Y \<inter> {e. e \<noteq> Tock \<and> \<rho> @ [[e]\<^sub>E] \<in> P \<and> e \<noteq> Tick \<or> e = Tock \<and> \<rho> @ [[X]\<^sub>R, [e]\<^sub>E] \<in> P})
        \<union> (Y \<inter> {e. e \<noteq> Tock \<and> (\<exists>s. s @ [[Tick]\<^sub>E] \<in> P \<and> (\<exists>t. t \<in> Q \<and> \<rho> @ [[e]\<^sub>E] = s @ t)) \<or>
          e = Tock \<and> (\<exists>s. s @ [[Tick]\<^sub>E] \<in> P \<and> (\<exists>t. t \<in> Q \<and> \<rho> @ [[X]\<^sub>R, [e]\<^sub>E] = s @ t))}) = {}"
      by (simp add: Int_Un_distrib)  
    then have "Y \<inter> {e. e \<noteq> Tock \<and> \<rho> @ [[e]\<^sub>E] \<in> P \<and> e \<noteq> Tick \<or> e = Tock \<and> \<rho> @ [[X]\<^sub>R, [e]\<^sub>E] \<in> P} = {}
      \<and> Y \<inter> {e. e \<noteq> Tock \<and> (\<exists>s. s @ [[Tick]\<^sub>E] \<in> P \<and> (\<exists>t. t \<in> Q \<and> \<rho> @ [[e]\<^sub>E] = s @ t)) \<or>
          e = Tock \<and> (\<exists>s. s @ [[Tick]\<^sub>E] \<in> P \<and> (\<exists>t. t \<in> Q \<and> \<rho> @ [[X]\<^sub>R, [e]\<^sub>E] = s @ t))} = {}"
      by auto    
    then have "Y \<inter> {e. e \<noteq> Tock \<and> \<rho> @ [[e]\<^sub>E] \<in> P \<and> e \<noteq> Tick \<or> e = Tock \<and> \<rho> @ [[X]\<^sub>R, [e]\<^sub>E] \<in> P} = {}
        \<and> Y \<inter> {e. e \<noteq> Tock \<and> t' @ [[e]\<^sub>E] \<in> Q \<or> e = Tock \<and> t' @ [[X]\<^sub>R, [e]\<^sub>E] \<in> Q} = {}"
      by (metis (no_types, lifting) 1 Int_left_commute inf.orderE inf_bot_right)
    then have "t' @ [[X \<union> Y]\<^sub>R] \<in> Q"
      using TT2w_def TT_def assm3 assm6 case_assm by auto
    then have "\<rho> @ [[X \<union> Y]\<^sub>R] \<noteq> s @ t' @ [[X \<union> Y]\<^sub>R]"
      using assm4 assm5 by auto
    then have "False"
      using case_assm assm7 by auto
    then show "\<rho> @ [[X \<union> Y]\<^sub>R] \<in> P"
      by auto
  qed
qed

lemma TT2_SeqComp:
  assumes TT1_P: "TT1 P" and TT4_P: "TT4 P"
  assumes TT2_P: "TT2 P" and TT2_Q: "TT2 Q"
  shows "TT2 (P ;\<^sub>C Q)"
  unfolding TT2_def
proof auto
  fix \<rho> \<sigma> X Y
  assume assm1: "\<rho> @ [X]\<^sub>R # \<sigma> \<in> P ;\<^sub>C Q"
  assume assm2: "Y \<inter> {e. e \<noteq> Tock \<and> \<rho> @ [[e]\<^sub>E] \<in> P ;\<^sub>C Q \<or> e = Tock \<and> \<rho> @ [[X]\<^sub>R, [e]\<^sub>E] \<in> P ;\<^sub>C Q} = {}"
  have "{e. e \<noteq> Tock \<and> \<rho> @ [[e]\<^sub>E] \<in> P \<and> e \<noteq> Tick \<or> e = Tock \<and> \<rho> @ [[X]\<^sub>R, [e]\<^sub>E] \<in> P} \<subseteq>
      {e. e \<noteq> Tock \<and> \<rho> @ [[e]\<^sub>E] \<in> P ;\<^sub>C Q \<or> e = Tock \<and> \<rho> @ [[X]\<^sub>R, [e]\<^sub>E] \<in> P ;\<^sub>C Q}"
    unfolding SeqCompTT_def by auto
  then have "Y \<inter> {e. e \<noteq> Tock \<and> \<rho> @ [[e]\<^sub>E] \<in> P \<and> e \<noteq> Tick \<or> e = Tock \<and> \<rho> @ [[X]\<^sub>R, [e]\<^sub>E] \<in> P} = {}"
    using assm2 subset_iff by auto
  then have P_assm2: "{e\<in>Y. e \<noteq> Tick} \<inter> {e. e \<noteq> Tock \<and> \<rho> @ [[e]\<^sub>E] \<in> P \<or> e = Tock \<and> \<rho> @ [[X]\<^sub>R, [e]\<^sub>E] \<in> P} = {}"
    using assm2 subset_iff by auto
  show "\<rho> @ [X \<union> Y]\<^sub>R # \<sigma> \<in> P ;\<^sub>C Q"
    using assm1 unfolding SeqCompTT_def
  proof auto
    assume case_assm: "\<rho> @ [X]\<^sub>R # \<sigma> \<in> P"
    then have "\<rho> @ [X \<union> {e\<in>Y. e \<noteq> Tick}]\<^sub>R # \<sigma> \<in> P"
      using TT2_P P_assm2 unfolding TT2_def by auto
    then show "\<rho> @ [X \<union> Y]\<^sub>R # \<sigma> \<in> P"
    proof (cases "Tick \<in> Y")
      have "\<rho> @ [X \<union> {e \<in> Y. e \<noteq> Tick}]\<^sub>R # \<sigma> \<in> P \<Longrightarrow> \<rho> @ [X \<union> {e \<in> Y. e \<noteq> Tick} \<union> {Tick}]\<^sub>R # \<sigma> \<in> P"
        using TT1_P TT4_TT1_add_Tick TT4_P by blast
      also have "Tick \<in> Y \<Longrightarrow> X \<union> {e \<in> Y. e \<noteq> Tick} \<union> {Tick} = X \<union> Y"
        by blast
      then show "\<rho> @ [X \<union> {e \<in> Y. e \<noteq> Tick}]\<^sub>R # \<sigma> \<in> P \<Longrightarrow> Tick \<in> Y \<Longrightarrow> \<rho> @ [X \<union> Y]\<^sub>R # \<sigma> \<in> P"
        using calculation by auto
    next
      assume "Tick \<notin> Y"
      then have "X \<union> {e \<in> Y. e \<noteq> Tick} = X \<union> Y"
        by auto
      then show "\<rho> @ [X \<union> {e \<in> Y. e \<noteq> Tick}]\<^sub>R # \<sigma> \<in> P \<Longrightarrow> \<rho> @ [X \<union> Y]\<^sub>R # \<sigma> \<in> P"
        by auto
    qed
  next
    fix s t
    assume case_assms: "s @ [[Tick]\<^sub>E] \<in> P" "t \<in> Q" "\<rho> @ [X]\<^sub>R # \<sigma> = s @ t"
    have "(\<exists> \<sigma>'. s = \<rho> @ [X]\<^sub>R # \<sigma>' \<and> \<sigma> = \<sigma>' @ t) \<or> (\<exists> \<rho>'. t = \<rho>' @ [X]\<^sub>R # \<sigma> \<and> \<rho> = s @ \<rho>')"
      using case_assms(3)
    proof auto
      have "\<And> s t. \<rho> @ [X]\<^sub>R # \<sigma> = s @ t \<Longrightarrow> \<forall>\<rho>'. t = \<rho>' @ [X]\<^sub>R # \<sigma> \<longrightarrow> \<rho> \<noteq> s @ \<rho>' \<Longrightarrow> \<exists>\<sigma>'. s = \<rho> @ [X]\<^sub>R # \<sigma>' \<and> \<sigma> = \<sigma>' @ t"
      proof (induct \<rho>, auto)
        fix s t
        show "[X]\<^sub>R # \<sigma> = s @ t \<Longrightarrow> s \<noteq> [] \<Longrightarrow> \<exists>\<sigma>'. s = [X]\<^sub>R # \<sigma>' \<and> \<sigma> = \<sigma>' @ t"
          by (metis Cons_eq_append_conv)
      next
        fix a \<rho> s t
        assume ind_hyp: "\<And>s t. \<rho> @ [X]\<^sub>R # \<sigma> = s @ t \<Longrightarrow> \<forall>\<rho>'. t = \<rho>' @ [X]\<^sub>R # \<sigma> \<longrightarrow> \<rho> \<noteq> s @ \<rho>' \<Longrightarrow> \<exists>\<sigma>'. s = \<rho> @ [X]\<^sub>R # \<sigma>' \<and> \<sigma> = \<sigma>' @ t"
        assume case_assms2: "a # \<rho> @ [X]\<^sub>R # \<sigma> = s @ t" "\<forall>\<rho>'. t = \<rho>' @ [X]\<^sub>R # \<sigma> \<longrightarrow> a # \<rho> \<noteq> s @ \<rho>'"
        have "s = [] \<or> (\<exists> s'. s = a # s')"
          by (metis Cons_eq_append_conv case_assms2(1))
        then show "\<exists>\<sigma>'. s = a # \<rho> @ [X]\<^sub>R # \<sigma>' \<and> \<sigma> = \<sigma>' @ t"
        proof auto
          fix t'
          assume case_assm3: "s = []"
          then have "t = a # \<rho> @ [X]\<^sub>R # \<sigma>"
            by (simp add: case_assms2(1))
          then obtain t' where "t = a # t' \<and> t' = \<rho> @ [X]\<^sub>R # \<sigma>"
            by blast
          then have "\<exists>\<sigma>'. [] = \<rho> @ [X]\<^sub>R # \<sigma>' \<and> \<sigma> = \<sigma>' @ \<rho> @ [X]\<^sub>R # \<sigma>"
            using case_assm3 case_assms2(2) by auto
          then show False
            by blast
        next
          fix s'
          assume case_assm3: "s = a # s'"
          then have "\<rho> @ [X]\<^sub>R # \<sigma> = s' @ t"
            using case_assms2(1) by auto
          then have "\<exists>\<sigma>'. s' = \<rho> @ [X]\<^sub>R # \<sigma>' \<and> \<sigma> = \<sigma>' @ t"
            using case_assm3 case_assms2(2) ind_hyp by auto
          then show "\<exists>\<sigma>'. s' = \<rho> @ [X]\<^sub>R # \<sigma>' \<and> \<sigma> = \<sigma>' @ t"
            by blast
        qed
      qed
      then show "\<rho> @ [X]\<^sub>R # \<sigma> = s @ t \<Longrightarrow> \<forall>\<rho>'. t = \<rho>' @ [X]\<^sub>R # \<sigma> \<longrightarrow> \<rho> \<noteq> s @ \<rho>' \<Longrightarrow> \<exists>\<sigma>'. s = \<rho> @ [X]\<^sub>R # \<sigma>' \<and> \<sigma> = \<sigma>' @ t"
        by auto
    qed
    then show "\<forall>s. s @ [[Tick]\<^sub>E] \<in> P \<longrightarrow> (\<forall>t. t \<in> Q \<longrightarrow> \<rho> @ [X \<union> Y]\<^sub>R # \<sigma> \<noteq> s @ t) \<Longrightarrow> 
      \<rho> @ [X \<union> Y]\<^sub>R # \<sigma> \<in> P"
    proof auto
      fix \<sigma>'
      assume case_assms2: "s = \<rho> @ [X]\<^sub>R # \<sigma>'" "\<sigma> = \<sigma>' @ t"
      then have "\<rho> @ [X \<union> {e\<in>Y. e \<noteq> Tick}]\<^sub>R # \<sigma>' @ [[Tick]\<^sub>E] \<in> P"
        using TT2_P P_assm2 case_assms case_assms2 unfolding TT2_def by auto
      then have "\<rho> @ [X \<union> Y]\<^sub>R # \<sigma>' @ [[Tick]\<^sub>E] \<in> P"
      proof (cases "Tick \<in> Y")
        assume case_assms3: "Tick \<in> Y" "\<rho> @ [X \<union> {e\<in>Y. e \<noteq> Tick}]\<^sub>R # \<sigma>' @ [[Tick]\<^sub>E] \<in> P"
        then have "\<rho> @ [X \<union> {e\<in>Y. e \<noteq> Tick} \<union> {Tick}]\<^sub>R # \<sigma>' @ [[Tick]\<^sub>E] \<in> P"
          using TT1_P TT4_TT1_add_Tick TT4_P by blast
        also have "X \<union> {e\<in>Y. e \<noteq> Tick} \<union> {Tick} = X \<union> Y"
          using case_assms3(1) by auto
        then show "\<rho> @ [X \<union> Y]\<^sub>R # \<sigma>' @ [[Tick]\<^sub>E] \<in> P"
          using calculation by auto
      next
        assume "Tick \<notin> Y"
        then have "X \<union> {e\<in>Y. e \<noteq> Tick} = X \<union> Y"
          by auto
        then show "\<rho> @ [X \<union> {e \<in> Y. e \<noteq> Tick}]\<^sub>R # \<sigma>' @ [[Tick]\<^sub>E] \<in> P \<Longrightarrow> \<rho> @ [X \<union> Y]\<^sub>R # \<sigma>' @ [[Tick]\<^sub>E] \<in> P"
          by auto
      qed
      then show "\<forall>s. s @ [[Tick]\<^sub>E] \<in> P \<longrightarrow> (\<forall>ta. ta \<in> Q \<longrightarrow> \<rho> @ [X \<union> Y]\<^sub>R # \<sigma>' @ t \<noteq> s @ ta) \<Longrightarrow>
          \<rho> @ [X \<union> Y]\<^sub>R # \<sigma>' @ t \<in> P"
        using case_assms by (erule_tac x="\<rho> @ [X \<union> Y]\<^sub>R # \<sigma>'" in allE, auto)
    next
      fix \<rho>'
      assume case_assms2: "t = \<rho>' @ [X]\<^sub>R # \<sigma>" "\<rho> = s @ \<rho>'"
      
      have "{e. e \<noteq> Tock \<and> \<rho>' @ [[e]\<^sub>E] \<in> Q \<or> e = Tock \<and> \<rho>' @ [[X]\<^sub>R, [e]\<^sub>E] \<in> Q} \<subseteq>
      {e. e \<noteq> Tock \<and> \<rho> @ [[e]\<^sub>E] \<in> P ;\<^sub>C Q \<or> e = Tock \<and> \<rho> @ [[X]\<^sub>R, [e]\<^sub>E] \<in> P ;\<^sub>C Q}"
        unfolding SeqCompTT_def using case_assms case_assms2 by auto
      then have "Y \<inter> {e. e \<noteq> Tock \<and> \<rho>' @ [[e]\<^sub>E] \<in> Q \<or> e = Tock \<and> \<rho>' @ [[X]\<^sub>R, [e]\<^sub>E] \<in> Q} = {}"
        using assm2 subsetCE by auto
      then have "\<rho>' @ [X \<union> Y]\<^sub>R # \<sigma> \<in> Q"
        using TT2_Q P_assm2 case_assms case_assms2 unfolding TT2_def by auto
      then show "\<forall>sa. sa @ [[Tick]\<^sub>E] \<in> P \<longrightarrow> (\<forall>t. t \<in> Q \<longrightarrow> s @ \<rho>' @ [X \<union> Y]\<^sub>R # \<sigma> \<noteq> sa @ t) \<Longrightarrow>
          s @ \<rho>' @ [X \<union> Y]\<^sub>R # \<sigma> \<in> P"
        using case_assms case_assms2 by auto
    qed
  next
    fix s :: "'a ttobs list"
    assume "\<rho> @ [X \<union> Y]\<^sub>R # \<sigma> = s @ [[Tick]\<^sub>E]"
    then obtain \<sigma>' where "\<sigma> = \<sigma>' @ [[Tick]\<^sub>E]"
      by (induct \<rho> s rule:tt_subset.induct, auto)
    then show "\<forall>s. \<rho> @ [X]\<^sub>R # \<sigma> \<noteq> s @ [[Tick]\<^sub>E] \<Longrightarrow> False"
      by simp
  next
    fix s t sa :: "'a ttobs list"
    assume case_assms: "\<rho> @ [X \<union> Y]\<^sub>R # \<sigma> = sa @ [[Tick]\<^sub>E]" "s @ [[Tick]\<^sub>E] \<in> P" "t \<in> Q" "\<rho> @ [X]\<^sub>R # \<sigma> = s @ t"
    obtain \<sigma>' where "\<sigma> = \<sigma>' @ [[Tick]\<^sub>E]"
      using case_assms(1) by (induct \<rho> sa rule:tt_subset.induct, auto)
    have "(\<exists> \<rho>2. \<rho> = s @ \<rho>2 \<and> t = \<rho>2 @ [X]\<^sub>R # \<sigma>) \<or> (\<exists> \<sigma>1. s = \<rho> @ [X]\<^sub>R # \<sigma>1 \<and> \<sigma> = \<sigma>1 @ t)"
      using case_assms(4) by (induct s \<rho> rule:tt_subset.induct, auto)
    then show "\<forall>s. s @ [[Tick]\<^sub>E] \<in> P \<longrightarrow> (\<forall>t. t \<in> Q \<longrightarrow> sa @ [[Tick]\<^sub>E] \<noteq> s @ t) \<Longrightarrow> False"
    proof auto
      fix \<rho>2 :: "'a ttobs list"
      assume case_assms2: "\<rho> = s @ \<rho>2" "t = \<rho>2 @ [X]\<^sub>R # \<sigma>"
      have "{e. e \<noteq> Tock \<and> \<rho>2 @ [[e]\<^sub>E] \<in> Q \<or> e = Tock \<and> \<rho>2 @ [[X]\<^sub>R, [e]\<^sub>E] \<in> Q} \<subseteq>
      {e. e \<noteq> Tock \<and> \<rho> @ [[e]\<^sub>E] \<in> P ;\<^sub>C Q \<or> e = Tock \<and> \<rho> @ [[X]\<^sub>R, [e]\<^sub>E] \<in> P ;\<^sub>C Q}"
        unfolding SeqCompTT_def using case_assms case_assms2 by auto
      then have "Y \<inter> {e. e \<noteq> Tock \<and> \<rho>2 @ [[e]\<^sub>E] \<in> Q \<or> e = Tock \<and> \<rho>2 @ [[X]\<^sub>R, [e]\<^sub>E] \<in> Q} = {}"
        using assm2 subsetCE by auto
      then have "\<rho>2 @ [X \<union> Y]\<^sub>R # \<sigma> \<in> Q"
        using TT2_Q case_assms(3) case_assms2(2) unfolding TT2_def by auto
      then show "\<forall>s. s @ [[Tick]\<^sub>E] \<in> P \<longrightarrow> (\<forall>t. t \<in> Q \<longrightarrow> sa @ [[Tick]\<^sub>E] \<noteq> s @ t) \<Longrightarrow> False"
        using case_assms by (erule_tac x="s" in allE, auto, erule_tac x="\<rho>2 @ [X \<union> Y]\<^sub>R # \<sigma>" in allE, auto simp add: case_assms2)
    next
      fix \<sigma>1 :: "'a ttobs list"
      assume case_assms2: "s = \<rho> @ [X]\<^sub>R # \<sigma>1" "\<sigma> = \<sigma>1 @ t"
      then have "\<rho> @ [X \<union> {e\<in>Y. e \<noteq> Tick}]\<^sub>R # \<sigma>1 @ [[Tick]\<^sub>E] \<in> P"
        using TT2_P P_assm2 case_assms case_assms2 unfolding TT2_def by auto
      then have "\<rho> @ [X \<union> Y]\<^sub>R # \<sigma>1 @ [[Tick]\<^sub>E] \<in> P"
      proof (cases "Tick \<in> Y")
        assume case_assms3: "Tick \<in> Y" "\<rho> @ [X \<union> {e\<in>Y. e \<noteq> Tick}]\<^sub>R # \<sigma>1 @ [[Tick]\<^sub>E] \<in> P"
        then have "\<rho> @ [X \<union> {e\<in>Y. e \<noteq> Tick} \<union> {Tick}]\<^sub>R # \<sigma>1 @ [[Tick]\<^sub>E] \<in> P"
          using TT1_P TT4_TT1_add_Tick TT4_P by blast
        also have "X \<union> {e\<in>Y. e \<noteq> Tick} \<union> {Tick} = X \<union> Y"
          using case_assms3(1) by auto
        then show "\<rho> @ [X \<union> Y]\<^sub>R # \<sigma>1 @ [[Tick]\<^sub>E] \<in> P"
          using calculation by auto
      next
        assume "Tick \<notin> Y"
        then have "X \<union> {e\<in>Y. e \<noteq> Tick} = X \<union> Y"
          by auto
        then show "\<rho> @ [X \<union> {e \<in> Y. e \<noteq> Tick}]\<^sub>R # \<sigma>1 @ [[Tick]\<^sub>E] \<in> P \<Longrightarrow> \<rho> @ [X \<union> Y]\<^sub>R # \<sigma>1 @ [[Tick]\<^sub>E] \<in> P"
          by auto
      qed
      then show "\<forall>s. s @ [[Tick]\<^sub>E] \<in> P \<longrightarrow> (\<forall>t. t \<in> Q \<longrightarrow> sa @ [[Tick]\<^sub>E] \<noteq> s @ t) \<Longrightarrow> False"
        using case_assms by (erule_tac x="\<rho> @ [X \<union> Y]\<^sub>R # \<sigma>1" in allE, auto, erule_tac x="t" in allE, auto simp add: case_assms2)
    qed
  qed
qed

text_raw \<open>\DefineSnippet{TT3_SeqComp}{\<close>
lemma TT3_SeqComp: 
  assumes "TT P" "TT Q"
  shows "TT3 (P ;\<^sub>C Q)"
  unfolding TT3_def SeqCompTT_def
proof auto
  fix x
  show "x \<in> P \<Longrightarrow> TT3_trace x"
    using TT3_def TT_TT3 assms(1) by blast
next
  fix s t
  assume "s @ [[Tick]\<^sub>E] \<in> P"
  then have 1: "TT3_trace s"
    by (meson TT1_def TT3_def TT_TT1 TT_TT3 assms(1) 
              tt_prefix_concat tt_prefix_imp_prefix_subset)
  assume "t \<in> Q"
  then have 2: "TT3_trace t \<and> ttWF t"
    using TT3_def TT_TT3 TT_wf assms(2) by blast
  show "TT3_trace (s @ t)"
    using 1 2 TT3_append by auto
qed
text_raw \<open>}%EndSnippet\<close>

text_raw \<open>\DefineSnippet{TT4_SeqComp}{\<close>
lemma TT4_SeqComp:
  assumes "TT4 P" "TT4 Q"
  shows "TT4 (P ;\<^sub>C Q)"
  unfolding SeqCompTT_def TT4_def
proof auto
  fix \<rho>
  show "\<rho> \<in> P \<Longrightarrow> add_Tick_refusal_trace \<rho> \<in> P"
    using TT4_def assms(1) by blast
next
  fix s t
  assume "s @ [[Tick]\<^sub>E] \<in> P" "t \<in> Q"
  then have "add_Tick_refusal_trace s @ [[Tick]\<^sub>E] \<in> P \<and> add_Tick_refusal_trace t \<in> Q"
    by (metis TT4_def add_Tick_refusal_trace_end_event assms(1) assms(2))
  then show "\<forall>sa. sa @ [[Tick]\<^sub>E] \<in> P \<longrightarrow> (\<forall>ta. ta \<in> Q \<longrightarrow> add_Tick_refusal_trace (s @ t) \<noteq> sa @ ta) \<Longrightarrow>
    add_Tick_refusal_trace (s @ t) \<in> P"
    using add_Tick_refusal_trace_concat by blast
next
  fix \<rho> s
  assume case_assms: "\<rho> \<in> P" "\<forall>s. \<rho> \<noteq> s @ [[Tick]\<^sub>E]" "add_Tick_refusal_trace \<rho> = s @ [[Tick]\<^sub>E]"
  have "\<exists> s'. s = add_Tick_refusal_trace s' \<and> \<rho> = s' @ [[Tick]\<^sub>E]"
    using case_assms(3) apply (induct \<rho> s rule:tt_subset.induct, auto)
    using add_Tick_refusal_trace.elims apply (rule_tac x="[]" in exI, auto)
    by (rule_tac x="[]" in exI, auto, metis list.discI list.sel(3))
  then show "\<forall>sa. sa @ [[Tick]\<^sub>E] \<in> P \<longrightarrow> (\<forall>t. t \<in> Q \<longrightarrow> s @ [[Tick]\<^sub>E] \<noteq> sa @ t) \<Longrightarrow> False"
    using case_assms(2) by blast
next
  fix s t sa
  assume case_assms: "s @ [[Tick]\<^sub>E] \<in> P" "t \<in> Q" "add_Tick_refusal_trace (s @ t) = sa @ [[Tick]\<^sub>E]"
  have 1: "add_Tick_refusal_trace s @ [[Tick]\<^sub>E] \<in> P"
    by (metis TT4_def add_Tick_refusal_trace_end_event assms(1) case_assms(1))
  have 2: "add_Tick_refusal_trace t \<in> Q"
    using TT4_def assms(2) case_assms(2) by blast
  show "\<forall>s. s @ [[Tick]\<^sub>E] \<in> P \<longrightarrow> (\<forall>t. t \<in> Q \<longrightarrow> sa @ [[Tick]\<^sub>E] \<noteq> s @ t) \<Longrightarrow> False"
    using 1 2 case_assms apply (erule_tac x="add_Tick_refusal_trace s" in allE, auto)
    by (erule_tac x="add_Tick_refusal_trace t" in allE, auto simp add: add_Tick_refusal_trace_concat)
qed
text_raw \<open>}%EndSnippet\<close>

lemma TT_SeqComp: 
  assumes "TT P" "TT Q" "TT4w P"
  shows "TT (P ;\<^sub>C Q)"
  unfolding TT_def apply auto
  apply (metis TT_def SeqComp_wf assms(1) assms(2))
  apply (simp add: TT0_SeqComp TT_TT0 assms(1) assms(2))
  using TT1_SeqComp TT_def assms(1) assms(2) apply blast
  apply (simp add: TT2w_SeqComp assms(1) assms(2) assms(3))
  apply (simp add: TT3_SeqComp assms(1) assms(2))
  done

end
