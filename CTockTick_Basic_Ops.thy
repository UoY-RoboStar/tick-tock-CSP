theory CTockTick_Basic_Ops
  imports CTockTick_Core
begin

subsection {* Div *}

definition DivCTT :: "'e cttobs list set" ("div\<^sub>C") where
  "div\<^sub>C = {[]}"

lemma DivCTT_wf: "\<forall> t\<in>div\<^sub>C. cttWF t"
  unfolding DivCTT_def by auto

lemma CT4s_Div: "CT4s div\<^sub>C"
  unfolding DivCTT_def CT4s_def by auto

lemma CT_Div: "CT div\<^sub>C"
  unfolding CT_defs DivCTT_def by (auto simp add: ctt_prefix_subset_antisym)

subsection {* Stop *}

definition StopCTT :: "'e cttobs list set" ("STOP\<^sub>C") where
  "STOP\<^sub>C = {t. \<exists> s\<in>tocks({x. x \<noteq> Tock}). t = s \<or> (\<exists> X. t = s @ [[X]\<^sub>R] \<and> Tock \<notin> X)}
  (*add_pretocks {x. x \<noteq> Tock} ({t. \<exists> Y. Tock \<notin> Y \<and> t = [[Y]\<^sub>R]} \<union> {[]})*)"

lemma StopCTT_wf: "\<forall> t\<in>STOP\<^sub>C. cttWF t"
  unfolding StopCTT_def by (auto simp add: tocks_append_wf tocks_wf)

lemma CT4s_Stop: "CT4s STOP\<^sub>C"
  unfolding CT4s_def StopCTT_def apply auto
  apply (metis (mono_tags, lifting) CT4s_def CT4s_tocks cttevent.distinct(5) mem_Collect_eq)
  apply (rule_tac x="add_Tick_refusal_trace s" in bexI, auto)
  apply (erule_tac x="X \<union> {Tick}" in allE, auto simp add: add_Tick_refusal_trace_end_refusal)
  by (metis (mono_tags, lifting) CT4s_def CT4s_tocks cttevent.distinct(5) mem_Collect_eq)

lemma CT_Stop: "CT STOP\<^sub>C"
  unfolding CT_defs
proof (auto)
  fix x
  show "x \<in> STOP\<^sub>C \<Longrightarrow> cttWF x"
    using StopCTT_wf by auto
next
  show "STOP\<^sub>C = {} \<Longrightarrow> False"
    unfolding StopCTT_def by (auto, erule_tac x="[]" in allE, erule_tac x="[]" in ballE, auto simp add: empty_in_tocks)
next
  fix \<rho> \<sigma>
  show "\<rho> \<lesssim>\<^sub>C \<sigma> \<Longrightarrow> \<sigma> \<in> STOP\<^sub>C \<Longrightarrow> \<rho> \<in> STOP\<^sub>C"
    unfolding StopCTT_def using ctt_prefix_subset_tocks ctt_prefix_subset_tocks_refusal by (auto, fastforce+)
next
  fix \<rho> X Y
  show "\<rho> @ [[X]\<^sub>R] \<in> STOP\<^sub>C \<Longrightarrow>
             Y \<inter> {e. e \<noteq> Tock \<and> \<rho> @ [[e]\<^sub>E] \<in> STOP\<^sub>C \<or> e = Tock \<and> \<rho> @ [[X]\<^sub>R, [e]\<^sub>E] \<in> STOP\<^sub>C} = {} \<Longrightarrow> \<rho> @ [[X \<union> Y]\<^sub>R] \<in> STOP\<^sub>C"
    unfolding StopCTT_def
  proof auto
    assume "\<rho> @ [[X]\<^sub>R] \<in> tocks {x. x \<noteq> Tock}"
    then have "False"
      using tocks.cases by (induct \<rho> rule:cttWF.induct, auto)
    then show "\<exists>s\<in>tocks {x. x \<noteq> Tock}. \<rho> @ [[X \<union> Y]\<^sub>R] = s \<or> \<rho> = s \<and> Tock \<notin> X \<and> Tock \<notin> Y"
      by auto
  next
    assume Tock_notin_X: "Tock \<notin> X"
    assume rho_tocks: "\<rho> \<in> tocks {x. x \<noteq> Tock}"
    from rho_tocks have setA: "{e. e \<noteq> Tock \<and> \<rho> @ [[e]\<^sub>E] \<in> tocks {x. x \<noteq> Tock}} = {}"
      using tocks.cases by (auto, induct \<rho> rule:cttWF.induct, auto)
    from rho_tocks Tock_notin_X have setB: "{e. e = Tock \<and> \<rho> @ [[X]\<^sub>R, [e]\<^sub>E] \<in> tocks {x. x \<noteq> Tock}} = {Tock}"
      by (auto, intro tocks_append_tocks, auto, metis (mono_tags, lifting) mem_Collect_eq subsetI tocks.empty_in_tocks tocks.tock_insert_in_tocks)
    from setA setB have "{e. e \<noteq> Tock \<and> \<rho> @ [[e]\<^sub>E] \<in> tocks {x. x \<noteq> Tock} \<or> e = Tock \<and> \<rho> @ [[X]\<^sub>R, [e]\<^sub>E] \<in> tocks {x. x \<noteq> Tock}} = {Tock}"
      by (auto)
    also assume "Y \<inter> {e. e \<noteq> Tock \<and> \<rho> @ [[e]\<^sub>E] \<in> tocks {x. x \<noteq> Tock} \<or> e = Tock \<and> \<rho> @ [[X]\<^sub>R, [e]\<^sub>E] \<in> tocks {x. x \<noteq> Tock}} = {}"
    then have "Tock \<notin> Y"
      using calculation by (auto)
    from this and rho_tocks show "\<exists>s\<in>tocks {x. x \<noteq> Tock}. \<rho> @ [[X \<union> Y]\<^sub>R] = s \<or> \<rho> = s \<and> Tock \<notin> Y"
      by auto
  qed
next
  fix x
  have "\<forall>s \<in> tocks {x. x \<noteq> Tock}. CT3_trace s"
    by (metis (mono_tags, lifting) CT3_def CT3_tocks mem_Collect_eq)
  then show "x \<in> STOP\<^sub>C \<Longrightarrow> CT3_trace x"
    unfolding StopCTT_def using CT3_append CT3_trace.simps(2) cttWF.simps(2) by (auto, blast)
qed


subsection {* Skip *}

definition SkipCTT :: "'e cttobs list set" ("SKIP\<^sub>C") where
  "SKIP\<^sub>C = {[], [[Tick]\<^sub>E]}"
  (*{[], [[Tick]\<^sub>E]} \<union> {t. \<exists> Y. Tick \<notin> Y \<and> t = [[Y]\<^sub>R]} \<union> {t. \<exists> n s. (t = s \<or> t = s @ [[Tick]\<^sub>E]) \<and> s \<in> ntock {x. x \<noteq> Tick} n}*)

lemma SkipCTT_wf: "\<forall> t\<in>SKIP\<^sub>C. cttWF t"
  unfolding SkipCTT_def by auto

lemma CT4s_Skip: "CT4s SKIP\<^sub>C"
  unfolding SkipCTT_def CT4s_def by auto

lemma CT_Skip: "CT SKIP\<^sub>C"
  unfolding CT_defs SkipCTT_def 
  apply (auto simp add: ctt_prefix_subset_antisym)
  apply (case_tac \<rho> rule:cttWF.cases, auto)
  done

subsection {* Wait *}

definition WaitCTT :: "nat \<Rightarrow> 'e cttobs list set" ("wait\<^sub>C[_]") where
  "wait\<^sub>C[n] = 
    {t. \<exists> s\<in>tocks({x. x \<noteq> Tock}). length (filter (\<lambda> x. x = [Tock]\<^sub>E) s) < n \<and> (t = s \<or> (\<exists> X. Tock \<notin> X \<and> t = s @ [[X]\<^sub>R]))}
     \<union> {t. \<exists> s\<in>tocks({x. x \<noteq> Tock}). length (filter (\<lambda> x. x = [Tock]\<^sub>E) s) = n \<and> (t = s \<or> t = s @ [[Tick]\<^sub>E])}"
  (*{t. \<exists> s x. t = s @ x \<and> x \<in> {[], [[Tick]\<^sub>E]} \<and> s \<in> ntock {x. x \<noteq> Tock} n}*)

lemma WaitCTT_wf: "\<forall> t\<in>wait\<^sub>C[n]. cttWF t"
  unfolding WaitCTT_def by (auto simp add: tocks_wf tocks_append_wf)

lemma CT4s_Wait: "CT4s (wait\<^sub>C[n])"
  unfolding WaitCTT_def CT4s_def
proof auto
  fix s :: "'a cttobs list"
  assume "s \<in> tocks {x. x \<noteq> Tock}" "length [x\<leftarrow>s . x = [Tock]\<^sub>E] < n"
  then show "\<exists>sa\<in>tocks {x. x \<noteq> Tock}. length [x\<leftarrow>sa . x = [Tock]\<^sub>E] < n \<and>
    (add_Tick_refusal_trace s = sa \<or> (\<exists>X. Tock \<notin> X \<and> add_Tick_refusal_trace s = sa @ [[X]\<^sub>R]))"
  apply (rule_tac x="add_Tick_refusal_trace s" in bexI, auto)
  apply (metis add_Tick_refusal_trace_filter_Tock_same_length)
  by (meson CT4s_def CT4s_tocks cttevent.simps(7) mem_Collect_eq)
next
  fix s :: "'a cttobs list"
  fix X :: "'a cttevent set"
  assume "s \<in> tocks {x. x \<noteq> Tock}" "length [x\<leftarrow>s . x = [Tock]\<^sub>E] < n" "Tock \<notin> X"
  then show "\<exists>sa\<in>tocks {x. x \<noteq> Tock}. length [x\<leftarrow>sa . x = [Tock]\<^sub>E] < n \<and>
    (add_Tick_refusal_trace (s @ [[X]\<^sub>R]) = sa \<or> (\<exists>Xa. Tock \<notin> Xa \<and> add_Tick_refusal_trace (s @ [[X]\<^sub>R]) = sa @ [[Xa]\<^sub>R]))"
  apply (rule_tac x="add_Tick_refusal_trace s" in bexI, safe, simp_all)
  apply (metis add_Tick_refusal_trace_filter_Tock_same_length)
  apply (erule_tac x="X \<union> {Tick}" in allE, simp add: add_Tick_refusal_trace_end_refusal)
  by (metis (mono_tags, lifting) CT4s_def CT4s_tocks cttevent.simps(7) mem_Collect_eq)
next
  fix s :: "'a cttobs list"
  assume "s \<in> tocks {x. x \<noteq> Tock}" "n = length [x\<leftarrow>s . x = [Tock]\<^sub>E]"
  then show "\<forall>sa\<in>tocks {x. x \<noteq> Tock}. length [x\<leftarrow>sa . x = [Tock]\<^sub>E] = length [x\<leftarrow>s . x = [Tock]\<^sub>E] \<longrightarrow>
      add_Tick_refusal_trace s \<noteq> sa \<and> add_Tick_refusal_trace s \<noteq> sa @ [[Tick]\<^sub>E] \<Longrightarrow>
    \<exists>sa\<in>tocks {x. x \<noteq> Tock}. length [x\<leftarrow>sa . x = [Tock]\<^sub>E] < length [x\<leftarrow>s . x = [Tock]\<^sub>E] \<and>
      (add_Tick_refusal_trace s = sa \<or> (\<exists>X. Tock \<notin> X \<and> add_Tick_refusal_trace s = sa @ [[X]\<^sub>R]))"
    apply (erule_tac x="add_Tick_refusal_trace s" in ballE, safe, simp_all)
    apply (metis add_Tick_refusal_trace_filter_Tock_same_length)
    by (meson CT4s_def CT4s_tocks cttevent.simps(7) mem_Collect_eq)
next
  fix s :: "'a cttobs list"
  assume "s \<in> tocks {x. x \<noteq> Tock}" "n = length [x\<leftarrow>s . x = [Tock]\<^sub>E]"
  show "\<forall>sa\<in>tocks {x. x \<noteq> Tock}. length [x\<leftarrow>sa . x = [Tock]\<^sub>E] = length [x\<leftarrow>s . x = [Tock]\<^sub>E] \<longrightarrow>
      add_Tick_refusal_trace (s @ [[Tick]\<^sub>E]) \<noteq> sa \<and> add_Tick_refusal_trace (s @ [[Tick]\<^sub>E]) \<noteq> sa @ [[Tick]\<^sub>E] \<Longrightarrow>
    \<exists>sa\<in>tocks {x. x \<noteq> Tock}. length [x\<leftarrow>sa . x = [Tock]\<^sub>E] < length [x\<leftarrow>s . x = [Tock]\<^sub>E] \<and>
      (add_Tick_refusal_trace (s @ [[Tick]\<^sub>E]) = sa \<or> (\<exists>X. Tock \<notin> X \<and> add_Tick_refusal_trace (s @ [[Tick]\<^sub>E]) = sa @ [[X]\<^sub>R]))"
    apply (erule_tac x="add_Tick_refusal_trace s" in ballE, safe)
    apply (metis add_Tick_refusal_trace_filter_Tock_same_length)
    using add_Tick_refusal_trace_end_event apply blast
    by (metis (mono_tags, lifting) CT4s_def CT4s_tocks \<open>s \<in> tocks {x. x \<noteq> Tock}\<close> cttevent.simps(7) mem_Collect_eq)
qed

lemma CT_Wait: "CT wait\<^sub>C[n]"
  unfolding CT_defs
proof auto
  fix x
  show "x \<in> wait\<^sub>C[n] \<Longrightarrow> cttWF x"
    using WaitCTT_wf by auto
next
  show "wait\<^sub>C[n] = {} \<Longrightarrow> False"
    unfolding WaitCTT_def using tocks.empty_in_tocks by fastforce
next
  fix \<rho> \<sigma>
  show "\<rho> \<lesssim>\<^sub>C \<sigma> \<Longrightarrow> \<sigma> \<in> wait\<^sub>C[n] \<Longrightarrow> \<rho> \<in> wait\<^sub>C[n]"
    unfolding WaitCTT_def 
  proof auto
    assume assm1: "\<rho> \<lesssim>\<^sub>C \<sigma>"
    assume assm2: "\<sigma> \<in> tocks {x. x \<noteq> Tock}"
    assume assm3: "length [x\<leftarrow>\<sigma> . x = [Tock]\<^sub>E] < n"
    from assm1 assm2 have 1: "\<rho> \<in> {t. \<exists>s\<in>tocks {x. x \<noteq> Tock}. t = s \<or> (\<exists>Y. t = s @ [[Y]\<^sub>R] \<and> Y \<subseteq> {x. x \<noteq> Tock})}"
      using ctt_prefix_subset_tocks by blast
    from assm1 have "length [x\<leftarrow>\<rho> . x = [Tock]\<^sub>E] \<le> length [x\<leftarrow>\<sigma> . x = [Tock]\<^sub>E]"
      using ctt_prefix_subset_Tock_filter_length by auto
    from this assm3 have 2: "length [x\<leftarrow>\<rho> . x = [Tock]\<^sub>E] < n"
      by auto
    from 1 2 show "\<exists>s\<in>tocks {x. x \<noteq> Tock}. length [x\<leftarrow>s . x = [Tock]\<^sub>E] < n \<and> (\<rho> = s \<or> (\<exists>X. Tock \<notin> X \<and> \<rho> = s @ [[X]\<^sub>R]))"
      by (auto, rule_tac x="s" in bexI, auto)
  next
    fix s X
    assume assm1: "\<rho> \<lesssim>\<^sub>C s @ [[X]\<^sub>R]"
    assume assm2: "s \<in> tocks {x. x \<noteq> Tock}"
    assume assm3: "length [x\<leftarrow>s . x = [Tock]\<^sub>E] < n"
    assume assm4: "Tock \<notin> X"
    from assm1 assm2 have 1: "\<exists>t\<in>tocks {x. x \<noteq> Tock}. \<rho> = t \<or> (\<exists>Z. \<rho> = t @ [[Z]\<^sub>R] \<and> (Z \<subseteq> {x. x \<noteq> Tock} \<or> Z \<subseteq> X))"
      using ctt_prefix_subset_tocks_refusal by blast
    from assm1 have "length [x\<leftarrow>\<rho> . x = [Tock]\<^sub>E] \<le> length [x\<leftarrow>s @ [[X]\<^sub>R] . x = [Tock]\<^sub>E]"
      using ctt_prefix_subset_Tock_filter_length by blast
    from this assm3 have 2: "length [x\<leftarrow>\<rho> . x = [Tock]\<^sub>E] < n"
      by auto
    from 1 2 assm4 show "\<exists>s\<in>tocks {x. x \<noteq> Tock}. length [x\<leftarrow>s . x = [Tock]\<^sub>E] < n \<and> (\<rho> = s \<or> (\<exists>X. Tock \<notin> X \<and> \<rho> = s @ [[X]\<^sub>R]))"
      by (auto, rule_tac x="t" in bexI, auto)
  next
    assume assm1: "\<rho> \<lesssim>\<^sub>C \<sigma>"
    assume assm2: "\<sigma> \<in> tocks {x. x \<noteq> Tock}"
    assume assm3: "\<forall>s\<in>tocks {x. x \<noteq> Tock}. length [x\<leftarrow>s . x = [Tock]\<^sub>E] = length [x\<leftarrow>\<sigma> . x = [Tock]\<^sub>E] \<longrightarrow> \<rho> \<noteq> s \<and> \<rho> \<noteq> s @ [[Tick]\<^sub>E]"
    thm ctt_prefix_subset_tocks
    from assm1 assm2 have 1: "\<rho> \<in> {t. \<exists>s\<in>tocks {x. x \<noteq> Tock}. t = s \<or> (\<exists>Y. t = s @ [[Y]\<^sub>R] \<and> Y \<subseteq> {x. x \<noteq> Tock})}"
      using ctt_prefix_subset_tocks by auto
    from assm1 have 2: "length [x\<leftarrow>\<rho> . x = [Tock]\<^sub>E] \<le> length [x\<leftarrow>\<sigma> . x = [Tock]\<^sub>E]"
      using ctt_prefix_subset_Tock_filter_length by auto
    from equal_Tocks_tocks_imp assm1 assm2 have "length [x\<leftarrow>\<rho> . x = [Tock]\<^sub>E] = length [x\<leftarrow>\<sigma> . x = [Tock]\<^sub>E] \<Longrightarrow> \<rho> \<in> tocks {x. x \<noteq> Tock}"
      by auto
    from this assm3 have "length [x\<leftarrow>\<rho> . x = [Tock]\<^sub>E] = length [x\<leftarrow>\<sigma> . x = [Tock]\<^sub>E] \<Longrightarrow> False"
      by auto
    from this 2 have 3: "length [x\<leftarrow>\<rho> . x = [Tock]\<^sub>E] < length [x\<leftarrow>\<sigma> . x = [Tock]\<^sub>E]"
      by (cases "length [x\<leftarrow>\<rho> . x = [Tock]\<^sub>E] = length [x\<leftarrow>\<sigma> . x = [Tock]\<^sub>E]", auto)
    from 1 3 show "\<exists>s\<in>tocks {x. x \<noteq> Tock}.
       length [x\<leftarrow>s . x = [Tock]\<^sub>E] < length [x\<leftarrow>\<sigma> . x = [Tock]\<^sub>E] \<and> (\<rho> = s \<or> (\<exists>X. Tock \<notin> X \<and> \<rho> = s @ [[X]\<^sub>R]))"
      by (auto, rule_tac x="s" in bexI, auto)
  next
    fix s
    assume assm1: "\<rho> \<lesssim>\<^sub>C s @ [[Tick]\<^sub>E]"
    assume assm2: "s \<in> tocks {x. x \<noteq> Tock}"
    assume assm3: "\<forall>sa\<in>tocks {x. x \<noteq> Tock}.
            length [x\<leftarrow>sa . x = [Tock]\<^sub>E] = length [x\<leftarrow>s . x = [Tock]\<^sub>E] \<longrightarrow> \<rho> \<noteq> sa \<and> \<rho> \<noteq> sa @ [[Tick]\<^sub>E]"
    obtain s' where s'_assms: "s'\<in>tocks {x. x \<noteq> Tock}" "s' \<lesssim>\<^sub>C s" "\<rho> = s' \<or>
              (\<exists>Y. \<rho> = s' @ [[Y]\<^sub>R] \<and> Y \<subseteq> {x. x \<noteq> Tock} \<and> length [x\<leftarrow>s' . x = [Tock]\<^sub>E] < length [x\<leftarrow>s . x = [Tock]\<^sub>E]) \<or>
              \<rho> = s' @ [[Tick]\<^sub>E] \<and> length [x\<leftarrow>s' . x = [Tock]\<^sub>E] = length [x\<leftarrow>s . x = [Tock]\<^sub>E]"
      using assm1 assm2 ctt_prefix_subset_tocks_event by blast
    then have "length [x\<leftarrow>s' . x = [Tock]\<^sub>E] \<noteq> length [x\<leftarrow>s . x = [Tock]\<^sub>E]"
      using assm3 less_le by blast
    then show "\<exists>sa\<in>tocks {x. x \<noteq> Tock}.
            length [x\<leftarrow>sa . x = [Tock]\<^sub>E] < length [x\<leftarrow>s . x = [Tock]\<^sub>E] \<and> (\<rho> = sa \<or> (\<exists>X. Tock \<notin> X \<and> \<rho> = sa @ [[X]\<^sub>R]))"
      using ctt_prefix_subset_Tock_filter_length order.not_eq_order_implies_strict s'_assms s'_assms by (rule_tac x="s'" in bexI, auto)
  qed
next
  fix \<rho> :: "'e cttobs list" 
  fix X Y :: "'e cttevent set"
  assume assm1: "\<rho> @ [[X]\<^sub>R] \<in> wait\<^sub>C[n]"
  assume assm2: "Y \<inter> {e. e \<noteq> Tock \<and> \<rho> @ [[e]\<^sub>E] \<in> wait\<^sub>C[n] \<or> e = Tock \<and> \<rho> @ [[X]\<^sub>R, [e]\<^sub>E] \<in> wait\<^sub>C[n]} = {}"
  from assm1 have 1: "\<rho>\<in>tocks {x. x \<noteq> Tock}"
    unfolding WaitCTT_def using end_refusal_notin_tocks by blast
  from assm1 have 2: "length [x\<leftarrow>\<rho> . x = [Tock]\<^sub>E] < n \<and> Tock \<notin> X"
    unfolding WaitCTT_def using end_refusal_notin_tocks by blast
  have 3: "length [x\<leftarrow>\<rho> . x = [Tock]\<^sub>E] < n \<longrightarrow> Tock \<notin> Y"
  proof auto
    assume assm3: "length [x\<leftarrow>\<rho> . x = [Tock]\<^sub>E] < n"
    assume assm4: "Tock \<in> Y"
    have "Tock \<in> {e. e \<noteq> Tock \<and> \<rho> @ [[e]\<^sub>E] \<in> wait\<^sub>C[n] \<or> e = Tock \<and> \<rho> @ [[X]\<^sub>R, [e]\<^sub>E] \<in> wait\<^sub>C[n]}"
      unfolding WaitCTT_def apply auto
      apply (metis (mono_tags, lifting) "1" "2" assm3 less_not_refl mem_Collect_eq subset_iff tocks.simps tocks_append_tocks)
      apply (metis (mono_tags, lifting) "1" "2" assm3 less_not_refl mem_Collect_eq subset_iff tocks.simps tocks_append_tocks)
      apply (metis (mono_tags, lifting) "1" "2" assm3 less_not_refl mem_Collect_eq subset_iff tocks.simps tocks_append_tocks)
      using Suc_lessI assm3 by blast
    then have "Tock \<in> Y \<inter> {e. e \<noteq> Tock \<and> \<rho> @ [[e]\<^sub>E] \<in> wait\<^sub>C[n] \<or> e = Tock \<and> \<rho> @ [[X]\<^sub>R, [e]\<^sub>E] \<in> wait\<^sub>C[n]}"
      using assm4 by auto
    then show "False"
      using assm2 by auto
  qed
  show "\<rho> @ [[X \<union> Y]\<^sub>R] \<in> wait\<^sub>C[n]"
    using 1 2 3 unfolding WaitCTT_def by auto
next
  fix x
  have "\<forall>x \<in> tocks {x. x \<noteq> Tock}. CT3_trace x"
    by (metis (mono_tags, lifting) CT3_def CT3_tocks mem_Collect_eq)
  then show "x \<in> wait\<^sub>C[n] \<Longrightarrow> CT3_trace x"
    unfolding WaitCTT_def apply auto
    using CT3_append CT3_trace.simps(2) cttWF.simps(2) apply blast
    using CT3_append CT3_trace.simps(2) cttWF.simps(3) apply blast
    done
qed

end