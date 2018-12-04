theory CTockTick_Prefix
  imports CTockTick_Core
begin

subsection {* Prefix *}
  

definition PrefixCTT :: "'e \<Rightarrow> 'e cttobs list set \<Rightarrow> 'e cttobs list set" (infixr "\<rightarrow>\<^sub>C" 61) where
  "PrefixCTT e P = 
    {t. \<exists> s\<in>tocks({x. x \<noteq> Tock \<and> x \<noteq> Event e}). t = s \<or> (\<exists> X. Tock \<notin> X \<and> Event e \<notin> X \<and> t = s @ [[X]\<^sub>R])}
     \<union> {t. \<exists> s\<in>tocks({x. x \<noteq> Tock \<and> x \<noteq> Event e}). t = s \<or> (\<exists> \<sigma>\<in>P. t = s @ [[Event e]\<^sub>E] @ \<sigma>)}"
    (*add_pretocks {x. x \<noteq> Event e \<and> x \<noteq> Tock} ({[], [[Event e]\<^sub>E]} \<union> {t. \<exists> Y. Tock \<notin> Y \<and> Event e \<notin> Y \<and> t = [[Y]\<^sub>R]})*)

lemma PrefixCTT_wf: "\<forall> t\<in>P. cttWF t \<Longrightarrow> \<forall> t\<in>PrefixCTT e P. cttWF t"
  unfolding PrefixCTT_def by (auto simp add: tocks_wf tocks_append_wf)

lemma CT4s_Prefix:
  "CT4s P \<Longrightarrow> CT4s (e \<rightarrow>\<^sub>C P)"
  unfolding PrefixCTT_def CT4s_def
proof auto
  fix s
  assume "s \<in> tocks {x. x \<noteq> Tock \<and> x \<noteq> Event e}"
  then show "\<forall>sa\<in>tocks {x. x \<noteq> Tock \<and> x \<noteq> Event e}. add_Tick_refusal_trace s \<noteq> sa \<and>
      (\<forall>\<sigma>\<in>P. add_Tick_refusal_trace s \<noteq> sa @ [Event e]\<^sub>E # \<sigma>) \<Longrightarrow>
    \<exists>sa\<in>tocks {x. x \<noteq> Tock \<and> x \<noteq> Event e}. \<exists>X. Tock \<notin> X \<and> Event e \<notin> X \<and> add_Tick_refusal_trace s = sa @ [[X]\<^sub>R]"
    apply (erule_tac x="add_Tick_refusal_trace s" in ballE, auto)
    by (metis (mono_tags, lifting) CT4s_def CT4s_tocks cttevent.distinct(3) cttevent.simps(7) mem_Collect_eq)
next
  fix s X
  assume "s \<in> tocks {x. x \<noteq> Tock \<and> x \<noteq> Event e}" "Tock \<notin> X" "Event e \<notin> X"
  then show "\<exists>sa\<in>tocks {x. x \<noteq> Tock \<and> x \<noteq> Event e}.
    \<exists>Xa. Tock \<notin> Xa \<and> Event e \<notin> Xa \<and> add_Tick_refusal_trace (s @ [[X]\<^sub>R]) = sa @ [[Xa]\<^sub>R]"
    apply (rule_tac x="add_Tick_refusal_trace s" in bexI, rule_tac x="X \<union> {Tick}" in exI, auto simp add: add_Tick_refusal_trace_end_refusal)
    by (metis (mono_tags, lifting) CT4s_def CT4s_tocks cttevent.distinct(3) cttevent.simps(7) mem_Collect_eq)
next
  fix s
  assume "s \<in> tocks {x. x \<noteq> Tock \<and> x \<noteq> Event e}"
  then show "\<forall>sa\<in>tocks {x. x \<noteq> Tock \<and> x \<noteq> Event e}. add_Tick_refusal_trace s \<noteq> sa \<and>
      (\<forall>\<sigma>\<in>P. add_Tick_refusal_trace s \<noteq> sa @ [Event e]\<^sub>E # \<sigma>) \<Longrightarrow>
    \<exists>sa\<in>tocks {x. x \<noteq> Tock \<and> x \<noteq> Event e}. \<exists>X. Tock \<notin> X \<and> Event e \<notin> X \<and> add_Tick_refusal_trace s = sa @ [[X]\<^sub>R]"
    apply (erule_tac x="add_Tick_refusal_trace s" in ballE, auto)
    by (metis (mono_tags, lifting) CT4s_def CT4s_tocks cttevent.distinct(3) cttevent.simps(7) mem_Collect_eq)
next
  fix s \<sigma>
  assume "s \<in> tocks {x. x \<noteq> Tock \<and> x \<noteq> Event e}" "\<sigma> \<in> P"
  also assume "\<forall>\<rho>. \<rho> \<in> P \<longrightarrow> add_Tick_refusal_trace \<rho> \<in> P"
  then have "add_Tick_refusal_trace \<sigma> \<in> P"
    using calculation by auto
  then show "\<forall>sa\<in>tocks {x. x \<noteq> Tock \<and> x \<noteq> Event e}. add_Tick_refusal_trace (s @ [Event e]\<^sub>E # \<sigma>) \<noteq> sa \<and>
      (\<forall>\<sigma>'\<in>P. add_Tick_refusal_trace (s @ [Event e]\<^sub>E # \<sigma>) \<noteq> sa @ [Event e]\<^sub>E # \<sigma>') \<Longrightarrow>
    \<exists>sa\<in>tocks {x. x \<noteq> Tock \<and> x \<noteq> Event e}.
      \<exists>X. Tock \<notin> X \<and> Event e \<notin> X \<and> add_Tick_refusal_trace (s @ [Event e]\<^sub>E # \<sigma>) = sa @ [[X]\<^sub>R]"
    using calculation apply (erule_tac x="add_Tick_refusal_trace s" in ballE, auto)
    apply (erule_tac x="add_Tick_refusal_trace \<sigma>" in ballE, auto simp add: add_Tick_refusal_trace_end_event_trace)
    by (metis (mono_tags, lifting) CT4s_def CT4s_tocks cttevent.distinct(3) cttevent.simps(7) mem_Collect_eq)
qed

lemma CT_Prefix:
  assumes "CT P"
  shows "CT (e \<rightarrow>\<^sub>C P)"
  unfolding CT_defs
proof auto
  fix x
  show "x \<in> e \<rightarrow>\<^sub>C P \<Longrightarrow> cttWF x"
    by (meson CT_def PrefixCTT_wf assms)
next
  show "e \<rightarrow>\<^sub>C P = {} \<Longrightarrow> False"
    unfolding PrefixCTT_def using tocks.empty_in_tocks by (blast)
next
  fix \<rho> \<sigma> :: "'a cttobs list"
  show "\<rho> \<lesssim>\<^sub>C \<sigma> \<Longrightarrow> \<sigma> \<in> e \<rightarrow>\<^sub>C P \<Longrightarrow> \<rho> \<in> e \<rightarrow>\<^sub>C P"
    unfolding PrefixCTT_def
  proof auto
    assume assm1: "\<rho> \<lesssim>\<^sub>C \<sigma>"
    assume assm2: "\<forall>s\<in>tocks {x. x \<noteq> Tock \<and> x \<noteq> Event e}. \<rho> \<noteq> s \<and> (\<forall>\<sigma>\<in>P. \<rho> \<noteq> s @ [Event e]\<^sub>E # \<sigma>)"
    assume assm3: "\<sigma> \<in> tocks {x. x \<noteq> Tock \<and> x \<noteq> Event e}"
    obtain s where "s\<in>tocks {x. x \<noteq> Tock \<and> x \<noteq> Event e}" "\<rho> = s \<or> (\<exists>Y. \<rho> = s @ [[Y]\<^sub>R] \<and> Y \<subseteq> {x. x \<noteq> Tock \<and> x \<noteq> Event e})"
      using assm1 assm3 ctt_prefix_subset_tocks by blast
    then show "\<exists>s\<in>tocks {x. x \<noteq> Tock \<and> x \<noteq> Event e}. \<exists>X. Tock \<notin> X \<and> Event e \<notin> X \<and> \<rho> = s @ [[X]\<^sub>R]"
      using assm2 by auto
  next
    fix s X
    assume assm1: "\<rho> \<lesssim>\<^sub>C s @ [[X]\<^sub>R]"
    assume assm2: "\<forall>s\<in>tocks {x. x \<noteq> Tock \<and> x \<noteq> Event e}. \<rho> \<noteq> s \<and> (\<forall>\<sigma>\<in>P. \<rho> \<noteq> s @ [Event e]\<^sub>E # \<sigma>)"
    assume assm3: "s \<in> tocks {x. x \<noteq> Tock \<and> x \<noteq> Event e}"
    assume assm4: "Tock \<notin> X"
    assume assm5: "Event e \<notin> X"
    obtain t Z where "t\<in>tocks {x. x \<noteq> Tock \<and> x \<noteq> Event e}" "\<rho> = t \<or> \<rho> = t @ [[Z]\<^sub>R]" "Z \<subseteq> {x. x \<noteq> Tock \<and> x \<noteq> Event e} \<or> Z \<subseteq> X"
      using assm1 assm3 ctt_prefix_subset_tocks_refusal by blast
    then show "\<exists>s\<in>tocks {x. x \<noteq> Tock \<and> x \<noteq> Event e}. \<exists>X. Tock \<notin> X \<and> Event e \<notin> X \<and> \<rho> = s @ [[X]\<^sub>R]"
      using assm2 assm4 assm5 by auto
  next
    assume assm1: "\<rho> \<lesssim>\<^sub>C \<sigma>"
    assume assm2: "\<forall>s\<in>tocks {x. x \<noteq> Tock \<and> x \<noteq> Event e}. \<rho> \<noteq> s \<and> (\<forall>\<sigma>\<in>P. \<rho> \<noteq> s @ [Event e]\<^sub>E # \<sigma>)"
    assume assm3: "\<sigma> \<in> tocks {x. x \<noteq> Tock \<and> x \<noteq> Event e}"
    obtain s where "s\<in>tocks {x. x \<noteq> Tock \<and> x \<noteq> Event e}" "\<rho> = s \<or> (\<exists>Y. \<rho> = s @ [[Y]\<^sub>R] \<and> Y \<subseteq> {x. x \<noteq> Tock \<and> x \<noteq> Event e})"
      using assm1 assm3 ctt_prefix_subset_tocks by blast
    then show "\<exists>s\<in>tocks {x. x \<noteq> Tock \<and> x \<noteq> Event e}. \<exists>X. Tock \<notin> X \<and> Event e \<notin> X \<and> \<rho> = s @ [[X]\<^sub>R]"
      using assm2 by auto
  next
    fix s \<sigma>'
    assume assm1: "\<rho> \<lesssim>\<^sub>C s @ [Event e]\<^sub>E # \<sigma>'"
    assume assm2: "\<forall>s\<in>tocks {x. x \<noteq> Tock \<and> x \<noteq> Event e}. \<rho> \<noteq> s \<and> (\<forall>\<sigma>\<in>P. \<rho> \<noteq> s @ [Event e]\<^sub>E # \<sigma>)"
    assume assm3: "s \<in> tocks {x. x \<noteq> Tock \<and> x \<noteq> Event e}"
    assume assm4: "\<sigma>' \<in> P"
    thm ctt_prefix_subset_append_split
    from assm1 have "\<rho> \<lesssim>\<^sub>C (s @ [[Event e]\<^sub>E]) @ \<sigma>'"
      by simp
    then obtain a b where a_b_assms: "\<rho> = a @ b" "a \<lesssim>\<^sub>C s @ [[Event e]\<^sub>E]" "b \<lesssim>\<^sub>C \<sigma>'"
      "length a = length (s @ [[Event e]\<^sub>E]) \<and> length [x\<leftarrow>a . x = [Tock]\<^sub>E] = length [x\<leftarrow>(s @ [[Event e]\<^sub>E]) . x = [Tock]\<^sub>E] \<or> b = []"
      using ctt_prefix_subset_append_split by blast
    then obtain s' where s'_assms: "s'\<in>tocks {x. x \<noteq> Tock \<and> x \<noteq> Event e}"
            "s' \<lesssim>\<^sub>C s"
             "a = s' \<or>
              (\<exists>Y. a = s' @ [[Y]\<^sub>R] \<and> Y \<subseteq> {x. x \<noteq> Tock \<and> x \<noteq> Event e} \<and> length [x\<leftarrow>s' . x = [Tock]\<^sub>E] < length [x\<leftarrow>s . x = [Tock]\<^sub>E]) \<or>
              a = s' @ [[Event e]\<^sub>E] \<and> length [x\<leftarrow>s' . x = [Tock]\<^sub>E] = length [x\<leftarrow>s . x = [Tock]\<^sub>E]"
      using ctt_prefix_subset_tocks_event assm3 by blast
    have b_in_P: "b \<in> P"
      using CT1_def CT_CT1 a_b_assms(3) assm4 assms by blast
    from s'_assms have "b \<noteq> [] \<longrightarrow> a = s' @ [[Event e]\<^sub>E] \<and> length [x\<leftarrow>s' . x = [Tock]\<^sub>E] = length [x\<leftarrow>s . x = [Tock]\<^sub>E]"
      using a_b_assms(4) ctt_prefix_subset_length by (auto, fastforce+)
    then have b_empty: "b = []"
      using b_in_P a_b_assms(1) assm2 s'_assms(1) by fastforce
    then have "\<exists>Y. a = s' @ [[Y]\<^sub>R] \<and> Y \<subseteq> {x. x \<noteq> Tock \<and> x \<noteq> Event e} \<and> length [x\<leftarrow>s' . x = [Tock]\<^sub>E] < length [x\<leftarrow>s . x = [Tock]\<^sub>E]"
      using a_b_assms(1) assm2 b_in_P s'_assms(1) s'_assms(3) by blast
    then show "\<exists>s\<in>tocks {x. x \<noteq> Tock \<and> x \<noteq> Event e}. \<exists>X. Tock \<notin> X \<and> Event e \<notin> X \<and> \<rho> = s @ [[X]\<^sub>R]"
      apply (auto, rule_tac x="s'" in bexI, rule_tac x="Y" in exI)
      using b_empty a_b_assms(1) s'_assms(1) by blast+
  qed
next
  fix \<rho> X Y
  assume assm1: "Y \<inter> {ea. ea \<noteq> Tock \<and> \<rho> @ [[ea]\<^sub>E] \<in> e \<rightarrow>\<^sub>C P \<or> ea = Tock \<and> \<rho> @ [[X]\<^sub>R, [ea]\<^sub>E] \<in> e \<rightarrow>\<^sub>C P} = {}"
  assume "\<rho> @ [[X]\<^sub>R] \<in> e \<rightarrow>\<^sub>C P"
  then have "(\<rho> \<in> tocks {x. x \<noteq> Tock \<and> x \<noteq> Event e} \<and> Tock \<notin> X \<and> Event e \<notin> X) \<or>
    (\<exists> s \<sigma>. s \<in> tocks {x. x \<noteq> Tock \<and> x \<noteq> Event e} \<and> \<sigma> \<in> P \<and> \<rho> @ [[X]\<^sub>R] = s @ [Event e]\<^sub>E # \<sigma>)"
    unfolding PrefixCTT_def using end_refusal_notin_tocks by auto
  then show "\<rho> @ [[X \<union> Y]\<^sub>R] \<in> e \<rightarrow>\<^sub>C P"
  proof auto
    assume assm2: "\<rho> \<in> tocks {x. x \<noteq> Tock \<and> x \<noteq> Event e}"
    assume assm3: "Tock \<notin> X"
    assume assm4: "Event e \<notin> X"

    have "Tock \<in> {ea. ea \<noteq> Tock \<and> \<rho> @ [[ea]\<^sub>E] \<in> e \<rightarrow>\<^sub>C P \<or> ea = Tock \<and> \<rho> @ [[X]\<^sub>R, [ea]\<^sub>E] \<in> e \<rightarrow>\<^sub>C P}"
      unfolding PrefixCTT_def by (auto, smt assm2 assm3 assm4 mem_Collect_eq subset_iff tocks.simps tocks_append_tocks)
    then have 1: "Tock \<notin> Y"
      using assm1 by auto
    have "Event e \<in> {ea. ea \<noteq> Tock \<and> \<rho> @ [[ea]\<^sub>E] \<in> e \<rightarrow>\<^sub>C P \<or> ea = Tock \<and> \<rho> @ [[X]\<^sub>R, [ea]\<^sub>E] \<in> e \<rightarrow>\<^sub>C P}"
      unfolding PrefixCTT_def apply (auto)
      using CT_empty assm2 assms by blast
    then have 2: "Event e \<notin> Y"
      using assm1 by auto
    show "\<rho> @ [[X \<union> Y]\<^sub>R] \<in> e \<rightarrow>\<^sub>C P"
      unfolding PrefixCTT_def using 1 2 assm2 assm3 assm4 by (auto)
  next
    fix s \<sigma>
    assume assm2: "s \<in> tocks {x. x \<noteq> Tock \<and> x \<noteq> Event e}"
    assume assm3: "\<sigma> \<in> P"
    assume assm4: "\<rho> @ [[X]\<^sub>R] = s @ [Event e]\<^sub>E # \<sigma>"
    obtain \<sigma>' where \<sigma>'_assm: "\<sigma> = \<sigma>' @ [[X]\<^sub>R]"
      by (metis append_butlast_last_id assm4 cttobs.distinct(1) last.simps last_appendR list.distinct(1))
    have \<rho>_def: "\<rho> = s @ [Event e]\<^sub>E # \<sigma>'"
      using \<sigma>'_assm assm4 by auto
    have 1: "\<And>x. s @ [Event e]\<^sub>E # \<sigma>' @ [[x]\<^sub>E] \<notin> tocks {x. x \<noteq> Tock \<and> x \<noteq> Event e}"
      using mid_event_notin_tocks by force
    have 2: "s @ [Event e]\<^sub>E # \<sigma>' @ [[X]\<^sub>R, [Tock]\<^sub>E] \<notin> tocks {x. x \<noteq> Tock \<and> x \<noteq> Event e}"
      using mid_event_notin_tocks by force
    have "{ea. ea \<noteq> Tock \<and> \<sigma>' @ [[ea]\<^sub>E] \<in> P \<or> ea = Tock \<and> \<sigma>' @ [[X]\<^sub>R, [ea]\<^sub>E] \<in> P} = {ea. ea \<noteq> Tock \<and> \<rho> @ [[ea]\<^sub>E] \<in> e \<rightarrow>\<^sub>C P \<or> ea = Tock \<and> \<rho> @ [[X]\<^sub>R, [ea]\<^sub>E] \<in> e \<rightarrow>\<^sub>C P}"
      unfolding PrefixCTT_def apply auto
      using \<sigma>'_assm assm2 assm4  apply (auto simp add: 1 2)
      by (metis (lifting) append_Cons append_Nil equal_traces_imp_equal_tocks)+
    then have "Y \<inter> {ea. ea \<noteq> Tock \<and> \<sigma>' @ [[ea]\<^sub>E] \<in> P \<or> ea = Tock \<and> \<sigma>' @ [[X]\<^sub>R, [ea]\<^sub>E] \<in> P} = {}"
      using assm1 by auto
    then have "\<sigma>' @ [[X \<union> Y]\<^sub>R] \<in> P"
      using \<sigma>'_assm assm3 assms by (auto simp add: CT2_def CT_def)
    then show "\<rho> @ [[X \<union> Y]\<^sub>R] \<in> e \<rightarrow>\<^sub>C P"
      unfolding PrefixCTT_def using \<rho>_def assm2 by auto
  qed
next
  fix x
  have "\<forall>x\<in>P. CT3_trace x"
    using CT3_def CT_CT3 assms by blast
  also have "\<forall>x \<in> tocks {x. x \<noteq> Tock \<and> x \<noteq> Event e}. CT3_trace x"
    by (metis (mono_tags, lifting) CT3_def CT3_tocks mem_Collect_eq) 
  then show "x \<in> e \<rightarrow>\<^sub>C P \<Longrightarrow> CT3_trace x"
    unfolding PrefixCTT_def using calculation apply auto
    using CT3_append CT3_trace.simps(2) cttWF.simps(2) apply blast
    by (metis (no_types, lifting) CT3_append CT3_trace.simps(2) CT3_trace.simps(4) CT_wf assms cttWF.elims(2) cttWF.simps(4)) 
qed

end