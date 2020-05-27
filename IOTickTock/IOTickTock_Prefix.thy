theory IOTickTock_Prefix
  imports IOTickTock_Core
begin

definition PrefixIOTT :: "'e \<Rightarrow> 'e set \<Rightarrow> 'e ttprocess \<Rightarrow> 'e ttprocess" (infixr "\<rightarrow>\<^sub>C\<^bsup>_\<^esup>" 61) where
  "PrefixIOTT e Outs P = 
    {t. \<exists> s\<in>tocks({x. x \<noteq> Tock \<and> x \<noteq> Event e}). e \<notin> Outs \<and> (t = s \<or> (\<exists> X. Tock \<notin> X \<and> Event e \<notin> X \<and> t = s @ [[X]\<^sub>R]))}
     \<union> {t. \<exists> s\<in>tocks({x. x \<noteq> Tock \<and> x \<noteq> Event e}). e \<notin> Outs \<and> (t = s \<or> (\<exists> \<sigma>\<in>P. t = s @ [[Event e]\<^sub>E] @ \<sigma>))}
     \<union> {t. ((\<exists> \<sigma>\<in>P. t = [[Event e]\<^sub>E] @ \<sigma>) \<or> t = []) \<and> e \<in> Outs}"

lemma PrefixIOTT_input_eq_PrefixTT:
  "e \<notin> Outs \<Longrightarrow> (e \<rightarrow>\<^sub>C\<^bsup>Outs\<^esup> P) = (e \<rightarrow>\<^sub>C P)"
  unfolding PrefixTT_def PrefixIOTT_def by auto

lemma "\<forall>x\<in>P. ttWF x \<Longrightarrow> \<forall> x \<in> e \<rightarrow>\<^sub>C\<^bsup>Outs\<^esup> P. ttWF x"
proof (cases "e \<in> Outs")
  assume "e \<in> Outs"
  then show "\<forall>x\<in>P. ttWF x \<Longrightarrow> \<forall>x\<in>e \<rightarrow>\<^sub>C\<^bsup>Outs\<^esup> P. ttWF x"
    unfolding PrefixIOTT_def by auto
next
  assume "e \<notin> Outs"
  then show "\<forall>x\<in>P. ttWF x \<Longrightarrow> \<forall>x\<in>e \<rightarrow>\<^sub>C\<^bsup>Outs\<^esup> P. ttWF x"
    by (simp add: PrefixIOTT_input_eq_PrefixTT PrefixTT_wf)
qed

lemma TT0_PrefixIOTT:
  "TT0 (e \<rightarrow>\<^sub>C\<^bsup>Outs\<^esup> P)"
proof (cases "e \<in> Outs")
  assume "e \<in> Outs"
  then show "TT0 (e \<rightarrow>\<^sub>C\<^bsup>Outs\<^esup> P)"
    unfolding PrefixIOTT_def TT0_def by auto
next
  assume "e \<notin> Outs"
  then show "TT0 (e \<rightarrow>\<^sub>C\<^bsup>Outs\<^esup> P)"
    using PrefixIOTT_input_eq_PrefixTT PrefixTT_def TT0_def tocks.empty_in_tocks by fastforce
qed

lemma TT1_PrefixIOTT:
  "TT1 P \<Longrightarrow> TT1 (e \<rightarrow>\<^sub>C\<^bsup>Outs\<^esup> P)"
proof (cases "e \<in> Outs")
  assume "e \<in> Outs"
  then show "TT1 P \<Longrightarrow> TT1 (e \<rightarrow>\<^sub>C\<^bsup>Outs\<^esup> P)"
    unfolding PrefixIOTT_def TT1_def apply auto
    apply (metis add_Tick_refusal_trace.cases tt_prefix_subset.simps(3) tt_prefix_subset.simps(5))
    using tt_prefix_subset.elims(2) by blast
next
  assume "e \<notin> Outs"
  then show "TT1 P \<Longrightarrow> TT1 (e \<rightarrow>\<^sub>C\<^bsup>Outs\<^esup> P)"
    by (simp add: PrefixIOTT_input_eq_PrefixTT TT1_Prefix)
qed

lemma TT2_PrefixIOTT:
  assumes "TT0 P" "TT1 P" "TT2 P"
  shows "TT2 (e \<rightarrow>\<^sub>C\<^bsup>Outs\<^esup> P)"
proof (cases "e \<in> Outs")
  assume "e \<in> Outs"
  then show "TT2 (e \<rightarrow>\<^sub>C\<^bsup>Outs\<^esup> P)"
    unfolding PrefixIOTT_def TT2_def
  proof auto
    fix \<rho> \<sigma> X Y \<sigma>'
    assume case_assms: "Y \<inter> {ea. ea \<noteq> Tock \<and> (\<exists>\<sigma>\<in>P. \<rho> @ [[ea]\<^sub>E] = [Event e]\<^sub>E # \<sigma>) 
        \<or> ea = Tock \<and> (\<exists>\<sigma>\<in>P. \<rho> @ [[X]\<^sub>R, [ea]\<^sub>E] = [Event e]\<^sub>E # \<sigma>)} = {}"
      "\<sigma>' \<in> P" "\<rho> @ [X]\<^sub>R # \<sigma> = [Event e]\<^sub>E # \<sigma>'"
    obtain \<rho>' where \<rho>'_def: "\<rho> = [Event e]\<^sub>E # \<rho>'"
      using case_assms(3) by (induct \<rho> rule:ttWF.induct, auto)
    have "\<rho>' @ [X \<union> Y]\<^sub>R # \<sigma> \<in> P"
      using  \<rho>'_def case_assms assms unfolding TT2_def by auto
    then show "\<exists>\<sigma>'\<in>P. \<rho> @ [X \<union> Y]\<^sub>R # \<sigma> = [Event e]\<^sub>E # \<sigma>'"
      by (simp add: \<rho>'_def)
  qed
next
  assume "e \<notin> Outs"
  then show "TT2 (e \<rightarrow>\<^sub>C\<^bsup>Outs\<^esup> P)"
    using assms by (simp add: PrefixIOTT_input_eq_PrefixTT TT2_Prefix)
qed

lemma TT3_PrefixIOTT:
  assumes "TT1 P" "TT3 P"
  shows "TT3 (e \<rightarrow>\<^sub>C\<^bsup>Outs\<^esup> P)"
proof (cases "e \<in> Outs")
  assume "e \<in> Outs"
  then show "TT3 (e \<rightarrow>\<^sub>C\<^bsup>Outs\<^esup> P)"
    unfolding PrefixIOTT_def TT3_def 
  proof auto
    fix \<rho> \<sigma> X \<sigma>'
    assume case_assms: "e \<in> Outs" "\<sigma>' \<in> P" "\<rho> @ [X]\<^sub>R # \<sigma> = [Event e]\<^sub>E # \<sigma>'"
    obtain \<rho>' where \<rho>'_def: "\<rho> = [Event e]\<^sub>E # \<rho>'"
      using case_assms(3) by (induct \<rho> rule:ttWF.induct, auto)
    have "\<rho>' @ [insert Tick X]\<^sub>R # \<sigma> \<in> P"
      using  \<rho>'_def case_assms assms unfolding TT3_def by auto
    then show "\<exists>\<sigma>'\<in>P. \<rho> @ [insert Tick X]\<^sub>R # \<sigma> = [Event e]\<^sub>E # \<sigma>'"
      by (simp add: \<rho>'_def)
  qed
next
  assume "e \<notin> Outs"
  then show "TT3 (e \<rightarrow>\<^sub>C\<^bsup>Outs\<^esup> P)"
    by (simp add: PrefixIOTT_input_eq_PrefixTT TT3_Prefix assms)
qed

lemma IOTT0_PrefixIOTT:
  "IOTT0 Outs P \<Longrightarrow> IOTT0 Outs (e \<rightarrow>\<^sub>C\<^bsup>Outs\<^esup> P)"
  unfolding IOTT0_def PrefixIOTT_def
proof auto
  fix s
  assume case_assms: "s \<in> tocks {x. x \<noteq> Tock \<and> x \<noteq> Event e}" "e \<notin> Outs"
  then have "IOTT0_trace Outs s \<in> tocks {x. x \<noteq> Tock \<and> x \<noteq> Event e}"
    apply - apply (induct s rule:tocks.induct, auto)
    using tocks.empty_in_tocks apply blast
    using tocks.simps by fastforce
  then show "\<forall>sa\<in>tocks {x. x \<noteq> Tock \<and> x \<noteq> Event e}.
            IOTT0_trace Outs s \<noteq> sa \<and> (\<forall>\<sigma>\<in>P. IOTT0_trace Outs s \<noteq> sa @ [Event e]\<^sub>E # \<sigma>) \<Longrightarrow>
         \<exists>sa\<in>tocks {x. x \<noteq> Tock \<and> x \<noteq> Event e}. \<exists>X. Tock \<notin> X \<and> Event e \<notin> X \<and> IOTT0_trace Outs s = sa @ [[X]\<^sub>R]"
    by auto
next
  fix s X
  assume case_assms: "s \<in> tocks {x. x \<noteq> Tock \<and> x \<noteq> Event e}" "e \<notin> Outs" "Tock \<notin> X" "Event e \<notin> X"
  then have "IOTT0_trace Outs s \<in> tocks {x. x \<noteq> Tock \<and> x \<noteq> Event e}"
    apply - apply (induct s rule:tocks.induct, auto)
    using tocks.empty_in_tocks apply blast
    using tocks.simps by fastforce
  then show "\<exists>sa\<in>tocks {x. x \<noteq> Tock \<and> x \<noteq> Event e}.
              \<exists>Xa. Tock \<notin> Xa \<and> Event e \<notin> Xa \<and> IOTT0_trace Outs (s @ [[X]\<^sub>R]) = sa @ [[Xa]\<^sub>R]"
    apply (rule_tac x="IOTT0_trace Outs s" in bexI, simp_all)
    by (rule_tac x="X \<union> Event ` Outs" in exI, auto simp add: case_assms IOTT0_trace_append_refusal)
next
  fix s
  assume case_assms: "s \<in> tocks {x. x \<noteq> Tock \<and> x \<noteq> Event e}" "e \<notin> Outs"
  then have "IOTT0_trace Outs s \<in> tocks {x. x \<noteq> Tock \<and> x \<noteq> Event e}"
    apply - apply (induct s rule:tocks.induct, auto)
    using tocks.empty_in_tocks apply blast
    using tocks.simps by fastforce
  then show "\<forall>sa\<in>tocks {x. x \<noteq> Tock \<and> x \<noteq> Event e}.
            IOTT0_trace Outs s \<noteq> sa \<and> (\<forall>\<sigma>\<in>P. IOTT0_trace Outs s \<noteq> sa @ [Event e]\<^sub>E # \<sigma>) \<Longrightarrow>
         \<exists>sa\<in>tocks {x. x \<noteq> Tock \<and> x \<noteq> Event e}. \<exists>X. Tock \<notin> X \<and> Event e \<notin> X \<and> IOTT0_trace Outs s = sa @ [[X]\<^sub>R]"
    by auto
next
  fix s \<sigma>
  assume case_assms: "s \<in> tocks {x. x \<noteq> Tock \<and> x \<noteq> Event e}" "e \<notin> Outs" "\<sigma> \<in> P" 
    "\<forall>x. x \<in> P \<longrightarrow> IOTT0_trace Outs x \<in> P" 
  then have "IOTT0_trace Outs s \<in> tocks {x. x \<noteq> Tock \<and> x \<noteq> Event e}"
    apply - apply (induct s rule:tocks.induct, auto)
    using tocks.empty_in_tocks apply blast
    using tocks.simps by fastforce
  also have "IOTT0_trace Outs \<sigma> \<in> P"
    using case_assms(3) case_assms(4) by blast
  then show "\<forall>sa\<in>tocks {x. x \<noteq> Tock \<and> x \<noteq> Event e}. IOTT0_trace Outs (s @ [Event e]\<^sub>E # \<sigma>) \<noteq> sa \<and>
              (\<forall>\<sigma>'\<in>P. IOTT0_trace Outs (s @ [Event e]\<^sub>E # \<sigma>) \<noteq> sa @ [Event e]\<^sub>E # \<sigma>') \<Longrightarrow>
           \<exists>sa\<in>tocks {x. x \<noteq> Tock \<and> x \<noteq> Event e}.
              \<exists>X. Tock \<notin> X \<and> Event e \<notin> X \<and> IOTT0_trace Outs (s @ [Event e]\<^sub>E # \<sigma>) = sa @ [[X]\<^sub>R]"
    using calculation apply (erule_tac x="IOTT0_trace Outs s" in ballE, auto)
    by (erule_tac x="IOTT0_trace Outs \<sigma>" in ballE, auto simp add: IOTT0_trace_append)
qed

end