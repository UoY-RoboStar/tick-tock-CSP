theory CTockTick_Basic_Ops
  imports CTockTick_Core
begin

subsection {* Div *}

definition DivCTT :: "'e cttobs list set" ("div\<^sub>C") where
  "div\<^sub>C = {[]}"

lemma DivCTT_wf: "\<forall> t\<in>div\<^sub>C. cttWF t"
  unfolding DivCTT_def by auto

lemma CT2s_Div: "CT2s div\<^sub>C"
  using DivCTT_wf unfolding DivCTT_def by (rule_tac wf_CT2s_induct, auto)

lemma CT4s_Div: "CT4s div\<^sub>C"
  unfolding DivCTT_def CT4s_def by auto

lemma CT_Div: "CT div\<^sub>C"
  unfolding CT_defs DivCTT_def by (auto simp add: ctt_prefix_subset_antisym)

subsection {* Timed Stop *}

definition StopCTT :: "'e cttobs list set" ("STOP\<^sub>C") where
  "STOP\<^sub>C = {t. \<exists> s\<in>tocks({x. x \<noteq> Tock}). t = s \<or> (\<exists> X. t = s @ [[X]\<^sub>R] \<and> Tock \<notin> X)}
  (*add_pretocks {x. x \<noteq> Tock} ({t. \<exists> Y. Tock \<notin> Y \<and> t = [[Y]\<^sub>R]} \<union> {[]})*)"

lemma StopCTT_wf: "\<forall> t\<in>STOP\<^sub>C. cttWF t"
  unfolding StopCTT_def by (auto simp add: tocks_append_wf tocks_wf)

lemma CT0_Stop: "CT0 STOP\<^sub>C"
  unfolding CT0_def StopCTT_def by (auto, rule_tac x="[]" in exI, auto simp add: empty_in_tocks)

lemma CT1_Stop: "CT1 STOP\<^sub>C"
  unfolding CT1_def StopCTT_def using ctt_prefix_subset_tocks ctt_prefix_subset_tocks_refusal by (auto, fastforce+)

lemma CT2_Stop: "CT2 STOP\<^sub>C"
  unfolding CT2_def StopCTT_def
proof auto
  fix \<rho> X Y
  assume "\<rho> @ [[X]\<^sub>R] \<in> tocks {x. x \<noteq> Tock}"
  then have "False"
    using tocks.cases by (induct \<rho> rule:cttWF.induct, auto)
  then show "\<exists>s\<in>tocks {x. x \<noteq> Tock}. \<rho> @ [[X \<union> Y]\<^sub>R] = s \<or> \<rho> = s \<and> Tock \<notin> X \<and> Tock \<notin> Y"
    by auto
next
  fix \<rho> :: "'a cttobs list"
  fix X Y :: "'a cttevent set"
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

lemma CT2s_Stop: "CT2s STOP\<^sub>C"
proof (rule_tac wf_CT2s_induct, safe, simp_all add: StopCTT_wf, unfold StopCTT_def, safe, simp_all)
  fix X Y :: "'a cttevent set"
  assume "[[X]\<^sub>R] \<in> tocks {x. x \<noteq> Tock}"
  then show "\<exists>s\<in>tocks {x. x \<noteq> Tock}. [[X \<union> Y]\<^sub>R] = s \<or> [] = s \<and> Tock \<notin> X \<and> Tock \<notin> Y"
    using refusal_notin_tocks by auto
next
  fix X Y Xa :: "'a cttevent set"
  fix s
  assume "Y \<inter> {e. e \<noteq> Tock \<and> [[e]\<^sub>E] \<in> tocks {x. x \<noteq> Tock} \<or> e = Tock \<and> [[Xa]\<^sub>R, [e]\<^sub>E] \<in> tocks {x. x \<noteq> Tock}} = {}" "Tock \<notin> Xa"
  then have "Tock \<notin> Y"
    by (auto, smt CollectI disjoint_iff_not_equal subsetI tocks.empty_in_tocks tocks.tock_insert_in_tocks)
  then show "Tock \<notin> Xa \<Longrightarrow> \<exists>s\<in>tocks {x. x \<noteq> Tock}. [[Xa \<union> Y]\<^sub>R] = s \<or> [] = s \<and> Tock \<notin> Y"
    using tocks.empty_in_tocks by blast
next
  fix X Y :: "'a cttevent set"
  fix \<sigma>
  assume assm1: "Y \<inter> {e. e \<noteq> Tock \<and> [[e]\<^sub>E] \<in> tocks {x. x \<noteq> Tock} \<or> e = Tock \<and> [[X]\<^sub>R, [e]\<^sub>E] \<in> tocks {x. x \<noteq> Tock}} = {}"
  assume assm2: "[X]\<^sub>R # [Tock]\<^sub>E # \<sigma> \<in> tocks {x. x \<noteq> Tock}"
  have Tock_notin_X: "Tock \<notin> X"
    by (metis (full_types) assm2 CT3_def CT3_tocks CT3_trace.simps(3) mem_Collect_eq)
  have Tock_notin_Y: "Tock \<notin> Y"
    by (smt Int_def Tock_notin_X assm1 emptyE mem_Collect_eq subset_eq tocks.empty_in_tocks tocks.tock_insert_in_tocks)
  have "\<sigma> \<in> tocks {x. x \<noteq> Tock}"
    using assm2 tocks.simps by auto
  then show "\<exists>s\<in>tocks {x. x \<noteq> Tock}. [X \<union> Y]\<^sub>R # [Tock]\<^sub>E # \<sigma> = s \<or> (\<exists>Xa. [X \<union> Y]\<^sub>R # [Tock]\<^sub>E # \<sigma> = s @ [[Xa]\<^sub>R] \<and> Tock \<notin> Xa)"
    by (metis (mono_tags, lifting) Tock_notin_X Tock_notin_Y mem_Collect_eq subsetI sup.bounded_iff tocks.tock_insert_in_tocks)
next
  fix X Y Xa :: "'a cttevent set"
  fix \<sigma> s
  assume assm1: "Y \<inter> {e. e \<noteq> Tock \<and> [[e]\<^sub>E] \<in> tocks {x. x \<noteq> Tock} \<or> e = Tock \<and> [[X]\<^sub>R, [e]\<^sub>E] \<in> tocks {x. x \<noteq> Tock}} = {}"
  assume assm2: "[X]\<^sub>R # [Tock]\<^sub>E # \<sigma> = s @ [[Xa]\<^sub>R]"
  assume assm3: "s \<in> tocks {x. x \<noteq> Tock}"
  assume assm4: "Tock \<notin> Xa"
  obtain s' where s'_assm: "s = [X]\<^sub>R # [Tock]\<^sub>E # s'"
    by (metis assm2 butlast.simps(2) butlast_snoc cttobs.distinct(1) last.simps last_snoc list.distinct(1))
  have Tock_notin_X: "Tock \<notin> X"
    using assm2 assm3 s'_assm by (auto, metis (full_types) CT3_def CT3_tocks CT3_trace.simps(3) mem_Collect_eq)
  have Tock_notin_Y: "Tock \<notin> Y"
    by (smt Int_def Tock_notin_X assm1 emptyE mem_Collect_eq subset_eq tocks.empty_in_tocks tocks.tock_insert_in_tocks)
  have "s' \<in> tocks {x. x \<noteq> Tock}"
    using s'_assm assm3 tocks.cases by auto
  then show "\<exists>s\<in>tocks {x. x \<noteq> Tock}. [X \<union> Y]\<^sub>R # [Tock]\<^sub>E # \<sigma> = s \<or> (\<exists>Xa. [X \<union> Y]\<^sub>R # [Tock]\<^sub>E # \<sigma> = s @ [[Xa]\<^sub>R] \<and> Tock \<notin> Xa)"
    using assm2 assm4 s'_assm apply (rule_tac x="[X \<union> Y]\<^sub>R # [Tock]\<^sub>E # s'" in bexI, auto)
    by (metis (mono_tags, lifting) Collect_mono Tock_notin_X Tock_notin_Y Un_def tocks.tock_insert_in_tocks)
next
  fix X Y :: "'a cttevent set"
  fix e \<rho> \<sigma>
  assume "[Event e]\<^sub>E # \<rho> @ [X]\<^sub>R # \<sigma> \<in> tocks {x. x \<noteq> Tock}"
  then show "\<exists>s\<in>tocks {x. x \<noteq> Tock}. [Event e]\<^sub>E # \<rho> @ [X \<union> Y]\<^sub>R # \<sigma> = s \<or> (\<exists>Xa. [Event e]\<^sub>E # \<rho> @ [X \<union> Y]\<^sub>R # \<sigma> = s @ [[Xa]\<^sub>R] \<and> Tock \<notin> Xa)"
    by (simp add: start_event_notin_tocks)
next
  fix X Y Xa :: "'a cttevent set"
  fix e \<rho> \<sigma> s
  assume "s \<in> tocks {x. x \<noteq> Tock}" "[Event e]\<^sub>E # \<rho> @ [X]\<^sub>R # \<sigma> = s @ [[Xa]\<^sub>R]"
  then have "\<exists> s'. [Event e]\<^sub>E # \<rho> @ [X]\<^sub>R # s' \<in> tocks {x. x \<noteq> Tock}"
    by (metis Nil_is_append_conv butlast.simps(2) butlast_snoc list.distinct(1) start_event_notin_tocks)
  then show "\<exists>s\<in>tocks {x. x \<noteq> Tock}. [Event e]\<^sub>E # \<rho> @ [X \<union> Y]\<^sub>R # \<sigma> = s \<or> (\<exists>Xa. [Event e]\<^sub>E # \<rho> @ [X \<union> Y]\<^sub>R # \<sigma> = s @ [[Xa]\<^sub>R] \<and> Tock \<notin> Xa)"
    by (simp add: start_event_notin_tocks)
next
  fix X Y Z :: "'a cttevent set"
  fix \<rho> \<sigma>
  assume ind_hyp: "(\<exists>s\<in>tocks {x. x \<noteq> Tock}. \<rho> @ [X]\<^sub>R # \<sigma> = s \<or> (\<exists>Xa. \<rho> @ [X]\<^sub>R # \<sigma> = s @ [[Xa]\<^sub>R] \<and> Tock \<notin> Xa)) \<and>
        Y \<inter> {e. e \<noteq> Tock \<and> \<rho> @ [[e]\<^sub>E] \<in> tocks {x. x \<noteq> Tock} \<or> e = Tock \<and> \<rho> @ [[X]\<^sub>R, [e]\<^sub>E] \<in> tocks {x. x \<noteq> Tock}} = {} \<Longrightarrow>
        \<exists>s\<in>tocks {x. x \<noteq> Tock}. \<rho> @ [X \<union> Y]\<^sub>R # \<sigma> = s \<or> (\<exists>Xa. \<rho> @ [X \<union> Y]\<^sub>R # \<sigma> = s @ [[Xa]\<^sub>R] \<and> Tock \<notin> Xa)" 
  assume assm1: "Y \<inter> {e. e \<noteq> Tock \<and> [Z]\<^sub>R # [Tock]\<^sub>E # \<rho> @ [[e]\<^sub>E] \<in> tocks {x. x \<noteq> Tock} \<or>
                e = Tock \<and> [Z]\<^sub>R # [Tock]\<^sub>E # \<rho> @ [[X]\<^sub>R, [e]\<^sub>E] \<in> tocks {x. x \<noteq> Tock}} = {}"
  assume assm2: "[Z]\<^sub>R # [Tock]\<^sub>E # \<rho> @ [X]\<^sub>R # \<sigma> \<in> tocks {x. x \<noteq> Tock}"
  have 1: "\<exists>s\<in>tocks {x. x \<noteq> Tock}. \<rho> @ [X]\<^sub>R # \<sigma> = s \<or> (\<exists>Xa. \<rho> @ [X]\<^sub>R # \<sigma> = s @ [[Xa]\<^sub>R] \<and> Tock \<notin> Xa)"
    using assm2 tocks.cases by auto
  have 2: "Y \<inter> {e. e \<noteq> Tock \<and> \<rho> @ [[e]\<^sub>E] \<in> tocks {x. x \<noteq> Tock} \<or> e = Tock \<and> \<rho> @ [[X]\<^sub>R, [e]\<^sub>E] \<in> tocks {x. x \<noteq> Tock}} = {}"
    by (smt assm1 assm2 disjoint_iff_not_equal list.distinct(1) list.inject mem_Collect_eq tocks.cases tocks.tock_insert_in_tocks)
  have "\<exists>s\<in>tocks {x. x \<noteq> Tock}. \<rho> @ [X \<union> Y]\<^sub>R # \<sigma> = s \<or> (\<exists>Xa. \<rho> @ [X \<union> Y]\<^sub>R # \<sigma> = s @ [[Xa]\<^sub>R] \<and> Tock \<notin> Xa)"
    using "1" "2" ind_hyp by linarith
  then show "\<exists>s\<in>tocks {x. x \<noteq> Tock}. [Z]\<^sub>R # [Tock]\<^sub>E # \<rho> @ [X \<union> Y]\<^sub>R # \<sigma> = s \<or> (\<exists>Xa. [Z]\<^sub>R # [Tock]\<^sub>E # \<rho> @ [X \<union> Y]\<^sub>R # \<sigma> = s @ [[Xa]\<^sub>R] \<and> Tock \<notin> Xa)"
    apply (auto, rule_tac x="[Z]\<^sub>R # [Tock]\<^sub>E # \<rho> @ [X \<union> Y]\<^sub>R # \<sigma>" in bexI, simp_all, metis assm2 list.inject list.simps(3) tocks.simps)
    by (smt Nil_is_append_conv append_butlast_last_id assm2 end_refusal_notin_tocks last.simps last_appendR list.distinct(1))
next
  fix X Y Z Xa :: "'a cttevent set"
  fix \<rho> \<sigma> s
  assume ind_hyp: "(\<exists>s\<in>tocks {x. x \<noteq> Tock}. \<rho> @ [X]\<^sub>R # \<sigma> = s \<or> (\<exists>Xa. \<rho> @ [X]\<^sub>R # \<sigma> = s @ [[Xa]\<^sub>R] \<and> Tock \<notin> Xa)) \<and>
        Y \<inter> {e. e \<noteq> Tock \<and> \<rho> @ [[e]\<^sub>E] \<in> tocks {x. x \<noteq> Tock} \<or> e = Tock \<and> \<rho> @ [[X]\<^sub>R, [e]\<^sub>E] \<in> tocks {x. x \<noteq> Tock}} = {} \<Longrightarrow>
        \<exists>s\<in>tocks {x. x \<noteq> Tock}. \<rho> @ [X \<union> Y]\<^sub>R # \<sigma> = s \<or> (\<exists>Xa. \<rho> @ [X \<union> Y]\<^sub>R # \<sigma> = s @ [[Xa]\<^sub>R] \<and> Tock \<notin> Xa)" 
  assume assm1: "Y \<inter> {e. e \<noteq> Tock \<and> [Z]\<^sub>R # [Tock]\<^sub>E # \<rho> @ [[e]\<^sub>E] \<in> tocks {x. x \<noteq> Tock} \<or>
                e = Tock \<and> [Z]\<^sub>R # [Tock]\<^sub>E # \<rho> @ [[X]\<^sub>R, [e]\<^sub>E] \<in> tocks {x. x \<noteq> Tock}} = {}"
  assume assm2: "[Z]\<^sub>R # [Tock]\<^sub>E # \<rho> @ [X]\<^sub>R # \<sigma> = s @ [[Xa]\<^sub>R]"
  assume assm3: "s \<in> tocks {x. x \<noteq> Tock}"
  assume assm4: "Tock \<notin> Xa"
  have 1: "\<exists>s\<in>tocks {x. x \<noteq> Tock}. \<rho> @ [X]\<^sub>R # \<sigma> = s \<or> (\<exists>Xa. \<rho> @ [X]\<^sub>R # \<sigma> = s @ [[Xa]\<^sub>R] \<and> Tock \<notin> Xa)"
    by (smt append_butlast_last_id assm2 assm3 assm4 butlast.simps(2) butlast_snoc last.simps last_snoc list.distinct(1) list.sel(3) tocks.simps)
  have 2: "Y \<inter> {e. e \<noteq> Tock \<and> \<rho> @ [[e]\<^sub>E] \<in> tocks {x. x \<noteq> Tock} \<or> e = Tock \<and> \<rho> @ [[X]\<^sub>R, [e]\<^sub>E] \<in> tocks {x. x \<noteq> Tock}} = {}"
    by (smt assm1 assm2 assm3 butlast.simps(2) butlast_snoc disjoint_iff_not_equal list.distinct(1) list.inject mem_Collect_eq tocks.simps)
  have 3: "\<exists>s'. s = [Z]\<^sub>R # [Tock]\<^sub>E # s'"
    using assm2 by (induct s rule:cttWF.induct, auto)
  have "\<exists>s\<in>tocks {x. x \<noteq> Tock}. \<rho> @ [X \<union> Y]\<^sub>R # \<sigma> = s \<or> (\<exists>Xa. \<rho> @ [X \<union> Y]\<^sub>R # \<sigma> = s @ [[Xa]\<^sub>R] \<and> Tock \<notin> Xa)"
    using "1" "2" ind_hyp by linarith
  then show "\<exists>s\<in>tocks {x. x \<noteq> Tock}. [Z]\<^sub>R # [Tock]\<^sub>E # \<rho> @ [X \<union> Y]\<^sub>R # \<sigma> = s \<or> (\<exists>Xa. [Z]\<^sub>R # [Tock]\<^sub>E # \<rho> @ [X \<union> Y]\<^sub>R # \<sigma> = s @ [[Xa]\<^sub>R] \<and> Tock \<notin> Xa)"
    apply (auto, rule_tac x="[Z]\<^sub>R # [Tock]\<^sub>E # \<rho> @ [X \<union> Y]\<^sub>R # \<sigma>" in bexI, simp_all)
    apply (metis (no_types, lifting) assm2 assm3 butlast.simps(2) butlast_snoc list.distinct(1) list.inject tocks.simps)
    using 3 by (safe, (rule_tac x="[Z]\<^sub>R # [Tock]\<^sub>E # sa" in bexI, simp_all, metis assm3 ctt_subset.simps(1) ctt_subset.simps(8) list.sel(1) tocks.simps)+)
qed

lemma CT3_Stop: "CT3 STOP\<^sub>C"
  unfolding CT3_def
proof (auto)
  fix x
  have "\<forall>s \<in> tocks {x. x \<noteq> Tock}. CT3_trace s"
    by (metis (mono_tags, lifting) CT3_def CT3_tocks mem_Collect_eq)
  then show "x \<in> STOP\<^sub>C \<Longrightarrow> CT3_trace x"
    unfolding StopCTT_def using CT3_append CT3_trace.simps(2) cttWF.simps(2) by (auto, blast)
qed

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

subsection {* Untimed Stop *}

definition UntimedStopCTT :: "'e cttobs list set" ("STOP\<^sub>U") where
  "STOP\<^sub>U = {t. t = [] \<or> (\<exists> X. t = [[X]\<^sub>R])}"

lemma UntimedStopCTT_wf: "\<forall> t\<in>STOP\<^sub>U. cttWF t"
  unfolding UntimedStopCTT_def by auto

lemma CT2s_UntimedStop: "CT2s STOP\<^sub>U"
  unfolding UntimedStopCTT_def CT2s_def by (auto simp add: append_eq_Cons_conv)

lemma CT4s_UntimedStop: "CT4s STOP\<^sub>U"
  unfolding UntimedStopCTT_def CT4s_def by auto

lemma CT_UntimedStop: "CT STOP\<^sub>U"
  unfolding UntimedStopCTT_def CT_defs apply (auto simp add: ctt_prefix_subset_antisym)
  by (metis ctt_prefix_subset.simps(2) ctt_prefix_subset.simps(4) ctt_prefix_subset.simps(6) cttobs.exhaust list.exhaust)

subsection {* Skip *}

definition SkipCTT :: "'e cttobs list set" ("SKIP\<^sub>C") where
  "SKIP\<^sub>C = {[], [[Tick]\<^sub>E]}"
  (*{[], [[Tick]\<^sub>E]} \<union> {t. \<exists> Y. Tick \<notin> Y \<and> t = [[Y]\<^sub>R]} \<union> {t. \<exists> n s. (t = s \<or> t = s @ [[Tick]\<^sub>E]) \<and> s \<in> ntock {x. x \<noteq> Tick} n}*)

lemma SkipCTT_wf: "\<forall> t\<in>SKIP\<^sub>C. cttWF t"
  unfolding SkipCTT_def by auto

lemma CT2s_Skip: "CT2s SKIP\<^sub>C"
  unfolding SkipCTT_def CT2s_def by (auto, metis Cons_eq_append_conv append_is_Nil_conv cttobs.distinct(1) list.inject list.simps(3))

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

lemma CT2s_Wait: "CT2s wait\<^sub>C[n]"
  unfolding CT2s_def
proof auto
  fix \<rho> \<sigma> :: "'a cttobs list"
  fix X Y :: "'a cttevent set"
  assume assm1: "\<rho> @ [X]\<^sub>R # \<sigma> \<in> wait\<^sub>C[n]"
  assume assm2: "Y \<inter> {e. e \<noteq> Tock \<and> \<rho> @ [[e]\<^sub>E] \<in> wait\<^sub>C[n] \<or> e = Tock \<and> \<rho> @ [[X]\<^sub>R, [e]\<^sub>E] \<in> wait\<^sub>C[n]} = {}"
  have 1: "Tock \<notin> X \<and> (\<forall> Z. Tock \<notin> Z \<longrightarrow> \<rho> @ [Z]\<^sub>R # \<sigma> \<in> wait\<^sub>C[n])"
    using assm1 unfolding WaitCTT_def
  proof (auto)
    show "\<rho> @ [X]\<^sub>R # \<sigma> \<in> tocks {x. x \<noteq> Tock} \<Longrightarrow> Tock \<in> X \<Longrightarrow> False"
      using tocks_mid_refusal by fastforce
  next
    fix Z
    assume "\<rho> @ [X]\<^sub>R # \<sigma> \<in> tocks {x. x \<noteq> Tock}" "length [x\<leftarrow>\<rho> . x = [Tock]\<^sub>E] + length [x\<leftarrow>\<sigma> . x = [Tock]\<^sub>E] < n"
    then show "Tock \<notin> Z \<Longrightarrow>\<exists>s\<in>tocks {x. x \<noteq> Tock}. length [x\<leftarrow>s . x = [Tock]\<^sub>E] < n \<and> (\<rho> @ [Z]\<^sub>R # \<sigma> = s \<or> (\<exists>X. Tock \<notin> X \<and> \<rho> @ [Z]\<^sub>R # \<sigma> = s @ [[X]\<^sub>R]))"
      using tocks_mid_refusal_change by (rule_tac x="\<rho> @ [Z]\<^sub>R # \<sigma>" in bexI, auto, fastforce)
  next
    fix s Xa
    assume assm1: "\<rho> @ [X]\<^sub>R # \<sigma> = s @ [[Xa]\<^sub>R]"
    assume assm2: "length [x\<leftarrow>s . x = [Tock]\<^sub>E] < n"
    assume assm3: "s \<in> tocks {x. x \<noteq> Tock}"
    assume assm4: "Tock \<notin> Xa"
    have "(\<exists>\<sigma>'. s = \<rho> @ [X]\<^sub>R # \<sigma>') \<or> (s = \<rho> \<and> X = Xa)"
      using assm1 by (metis butlast.simps(2) butlast_append butlast_snoc cttobs.inject(2) last_snoc list.distinct(1))
    then show "Tock \<in> X \<Longrightarrow> False"
      using assm3 assm4 tocks_mid_refusal by fastforce
  next
    fix s Xa Z
    assume assm1: "\<rho> @ [X]\<^sub>R # \<sigma> = s @ [[Xa]\<^sub>R]"
    assume assm2: "length [x\<leftarrow>s . x = [Tock]\<^sub>E] < n"
    assume assm3: "s \<in> tocks {x. x \<noteq> Tock}"
    assume assm4: "Tock \<notin> Xa"
    have "(\<exists>\<sigma>'. s = \<rho> @ [X]\<^sub>R # \<sigma>') \<or> (s = \<rho> \<and> X = Xa)"
      using assm1 by (metis butlast.simps(2) butlast_append butlast_snoc cttobs.inject(2) last_snoc list.distinct(1))
    then show "Tock \<notin> Z \<Longrightarrow> \<exists>s\<in>tocks {x. x \<noteq> Tock}. length [x\<leftarrow>s . x = [Tock]\<^sub>E] < n \<and> (\<rho> @ [Z]\<^sub>R # \<sigma> = s \<or> (\<exists>X. Tock \<notin> X \<and> \<rho> @ [Z]\<^sub>R # \<sigma> = s @ [[X]\<^sub>R]))"
      using assm1 assm2 assm3 assm4 apply (auto, rule_tac x="\<rho> @ [Z]\<^sub>R # \<sigma>'" in bexI, auto)
      using tocks_mid_refusal_change by fastforce
  next
    show "\<rho> @ [X]\<^sub>R # \<sigma> \<in> tocks {x. x \<noteq> Tock} \<Longrightarrow> Tock \<in> X \<Longrightarrow> False"
      using tocks_mid_refusal by fastforce
  next
    fix Z :: "'a cttevent set"
    assume "\<rho> @ [X]\<^sub>R # \<sigma> \<in> tocks {x. x \<noteq> Tock}" "n = length [x\<leftarrow>\<rho> . x = [Tock]\<^sub>E] + length [x\<leftarrow>\<sigma> . x = [Tock]\<^sub>E]" "Tock \<notin> Z"
    then show "\<forall>s\<in>tocks {x. x \<noteq> Tock}. length [x\<leftarrow>s . x = [Tock]\<^sub>E] = length [x\<leftarrow>\<rho> . x = [Tock]\<^sub>E] + length [x\<leftarrow>\<sigma> . x = [Tock]\<^sub>E] \<longrightarrow>
            \<rho> @ [Z]\<^sub>R # \<sigma> \<noteq> s \<and> \<rho> @ [Z]\<^sub>R # \<sigma> \<noteq> s @ [[Tick]\<^sub>E] \<Longrightarrow>
         \<exists>s\<in>tocks {x. x \<noteq> Tock}. length [x\<leftarrow>s . x = [Tock]\<^sub>E] < length [x\<leftarrow>\<rho> . x = [Tock]\<^sub>E] + length [x\<leftarrow>\<sigma> . x = [Tock]\<^sub>E] \<and>
            (\<rho> @ [Z]\<^sub>R # \<sigma> = s \<or> (\<exists>X. Tock \<notin> X \<and> \<rho> @ [Z]\<^sub>R # \<sigma> = s @ [[X]\<^sub>R]))"
      using tocks_mid_refusal_change by (erule_tac x="\<rho> @ [Z]\<^sub>R # \<sigma>" in ballE, simp_all, fastforce)
  next
    fix s
    assume "\<rho> @ [X]\<^sub>R # \<sigma> = s @ [[Tick]\<^sub>E]"
    then obtain \<sigma>' where "s = \<rho> @ [X]\<^sub>R # \<sigma>'"
      by (metis butlast.simps(2) butlast_append butlast_snoc cttobs.distinct(1) last_snoc list.distinct(1))
    then show "s \<in> tocks {x. x \<noteq> Tock} \<Longrightarrow> Tock \<in> X \<Longrightarrow> False"
      using tocks_mid_refusal by fastforce
  next
    fix s :: "'a cttobs list"
    fix Z :: "'a cttevent set"
    assume assms: "s \<in> tocks {x. x \<noteq> Tock}" "n = length [x\<leftarrow>s . x = [Tock]\<^sub>E]" "Tock \<notin> Z" "\<rho> @ [X]\<^sub>R # \<sigma> = s @ [[Tick]\<^sub>E]"
    then obtain \<sigma>' where "s = \<rho> @ [X]\<^sub>R # \<sigma>'"
      by (metis butlast.simps(2) butlast_append butlast_snoc cttobs.distinct(1) last_snoc list.distinct(1))
    then show "\<forall>sa\<in>tocks {x. x \<noteq> Tock}.
              length [x\<leftarrow>sa . x = [Tock]\<^sub>E] = length [x\<leftarrow>s . x = [Tock]\<^sub>E] \<longrightarrow> \<rho> @ [Z]\<^sub>R # \<sigma> \<noteq> sa \<and> \<rho> @ [Z]\<^sub>R # \<sigma> \<noteq> sa @ [[Tick]\<^sub>E] \<Longrightarrow>
           \<exists>sa\<in>tocks {x. x \<noteq> Tock}.
              length [x\<leftarrow>sa . x = [Tock]\<^sub>E] < length [x\<leftarrow>s . x = [Tock]\<^sub>E] \<and> (\<rho> @ [Z]\<^sub>R # \<sigma> = sa \<or> (\<exists>X. Tock \<notin> X \<and> \<rho> @ [Z]\<^sub>R # \<sigma> = sa @ [[X]\<^sub>R]))"
      using assms apply (erule_tac x="\<rho> @ [Z]\<^sub>R # \<sigma>'" in ballE, auto)
      using tocks_mid_refusal_change by fastforce
  qed
  also have \<rho>_in_tocks: "\<rho> \<in> tocks {x. x \<noteq> Tock}"
    using assm1 unfolding WaitCTT_def apply auto
    using tocks_mid_refusal_front_in_tocks apply blast
    apply (metis butlast.simps(2) butlast_append butlast_snoc list.distinct(1) tocks_mid_refusal_front_in_tocks)
    using tocks_mid_refusal_front_in_tocks apply blast
    by (metis butlast.simps(2) butlast_append butlast_snoc list.distinct(1) tocks_mid_refusal_front_in_tocks)
  then have "Tock \<in> {e. e \<noteq> Tock \<and> \<rho> @ [[e]\<^sub>E] \<in> wait\<^sub>C[n] \<or> e = Tock \<and> \<rho> @ [[X]\<^sub>R, [e]\<^sub>E] \<in> wait\<^sub>C[n]}"
    unfolding WaitCTT_def
  proof auto
    show "\<rho> \<in> tocks {x. x \<noteq> Tock} \<Longrightarrow> \<rho> @ [[X]\<^sub>R, [Tock]\<^sub>E] \<notin> tocks {x. x \<noteq> Tock} \<Longrightarrow> False"
      by (metis (mono_tags, lifting) calculation mem_Collect_eq subset_eq tocks.simps tocks_append_tocks)
  next
    show "\<rho> \<in> tocks {x. x \<noteq> Tock} \<Longrightarrow> \<rho> @ [[X]\<^sub>R, [Tock]\<^sub>E] \<notin> tocks {x. x \<noteq> Tock} \<Longrightarrow> Suc (length [x\<leftarrow>\<rho> . x = [Tock]\<^sub>E]) < n"
      by (metis (mono_tags, lifting) CollectI calculation subsetI tocks.empty_in_tocks tocks.tock_insert_in_tocks tocks_append_tocks)
  next
    show "\<rho> \<in> tocks {x. x \<noteq> Tock} \<Longrightarrow> Suc (length [x\<leftarrow>\<rho> . x = [Tock]\<^sub>E]) \<noteq> n \<Longrightarrow> \<rho> @ [[X]\<^sub>R, [Tock]\<^sub>E] \<in> tocks {x. x \<noteq> Tock}"
      by (metis (mono_tags, lifting) calculation mem_Collect_eq subsetI tocks.empty_in_tocks tocks.tock_insert_in_tocks tocks_append_tocks)
  next
    show "\<rho> \<in> tocks {x. x \<noteq> Tock} \<Longrightarrow> Suc (length [x\<leftarrow>\<rho> . x = [Tock]\<^sub>E]) \<noteq> n \<Longrightarrow> Suc (length [x\<leftarrow>\<rho> . x = [Tock]\<^sub>E]) < n"
      using assm1 unfolding WaitCTT_def
    proof auto
      fix s Xa
      assume "\<rho> @ [X]\<^sub>R # \<sigma> = s @ [[Xa]\<^sub>R]"
      then obtain \<sigma>' where "s = \<rho> @ [X]\<^sub>R # \<sigma>' \<or> s = \<rho>"
        by (metis butlast.simps(2) butlast_append butlast_snoc list.distinct(1))
      then show "Suc (length [x\<leftarrow>\<rho> . x = [Tock]\<^sub>E]) \<noteq> n \<Longrightarrow> length [x\<leftarrow>s . x = [Tock]\<^sub>E] < n \<Longrightarrow> Suc (length [x\<leftarrow>\<rho> . x = [Tock]\<^sub>E]) < n"
        by auto
    next
      assume "\<rho> @ [X]\<^sub>R # \<sigma> \<in> tocks {x. x \<noteq> Tock}"
      then have "\<exists> \<sigma>'. \<sigma> = [Tock]\<^sub>E # \<sigma>'"
        by (metis \<rho>_in_tocks list.inject list.simps(3) tocks.cases tocks_append_nontocks)
      then show "Suc 0 \<noteq> length [x\<leftarrow>\<sigma> . x = [Tock]\<^sub>E] \<Longrightarrow> n = length [x\<leftarrow>\<rho> . x = [Tock]\<^sub>E] + length [x\<leftarrow>\<sigma> . x = [Tock]\<^sub>E] \<Longrightarrow> Suc 0 < length [x\<leftarrow>\<sigma> . x = [Tock]\<^sub>E]"
        by auto
    next
      fix s
      assume assms: "\<rho> @ [X]\<^sub>R # \<sigma> = s @ [[Tick]\<^sub>E]" "s \<in> tocks {x. x \<noteq> Tock}"
      then obtain \<sigma>' where 1: "s = \<rho> @ [X]\<^sub>R # \<sigma>'"
        by (metis butlast.simps(2) butlast_append butlast_snoc cttobs.distinct(1) last.simps last_appendR list.distinct(1))
      then have 2: "\<exists> \<sigma>''. \<sigma>' = [Tock]\<^sub>E # \<sigma>''"
        by (metis \<rho>_in_tocks assms(2) list.inject list.simps(3) tocks.cases tocks_append_nontocks)
      then show "Suc (length [x\<leftarrow>\<rho> . x = [Tock]\<^sub>E]) \<noteq> length [x\<leftarrow>s . x = [Tock]\<^sub>E] \<Longrightarrow> Suc (length [x\<leftarrow>\<rho> . x = [Tock]\<^sub>E]) < length [x\<leftarrow>s . x = [Tock]\<^sub>E]"
        using 1 by auto
    qed
  qed
  then have "Tock \<notin> Y"
    using assm2 by auto
  then show "\<rho> @ [X \<union> Y]\<^sub>R # \<sigma> \<in> wait\<^sub>C[n]"
    using 1 by auto
qed

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

subsection {* Guard *}

definition GuardCTT :: "bool \<Rightarrow> 'e cttobs list set \<Rightarrow> 'e cttobs list set" (infixr "&\<^sub>C" 61) where
  "g &\<^sub>C P = {x\<in>P. g} \<union> {x\<in>STOP\<^sub>C. \<not> g}"

lemma GuardCTT_wf: "\<forall>t\<in>P. cttWF t \<Longrightarrow> \<forall>t\<in>(g &\<^sub>C P). cttWF t"
  unfolding GuardCTT_def using StopCTT_wf by blast

lemma CT0_Guard: "CT0 P \<Longrightarrow> CT0 (g &\<^sub>C P)"
  using CT0_Stop unfolding CT0_def GuardCTT_def by auto

lemma CT1_Guard: "CT1 P \<Longrightarrow> CT1 (g &\<^sub>C P)"
  using CT1_Stop unfolding CT1_def GuardCTT_def by auto

lemma CT2_Guard: "CT2 P \<Longrightarrow> CT2 (g &\<^sub>C P)"
  using CT2_Stop unfolding CT2_def GuardCTT_def by (auto, blast+)

lemma CT2s_Guard: "CT2s P \<Longrightarrow> CT2s (g &\<^sub>C P)"
  using CT2s_Stop unfolding CT2s_def GuardCTT_def by (auto, blast+)

lemma CT3_Guard: "CT3 P \<Longrightarrow> CT3 (g &\<^sub>C P)"
  using CT3_Stop unfolding CT3_def GuardCTT_def by blast

lemma CT4s_Guard: "CT4s P \<Longrightarrow> CT4s (g &\<^sub>C P)"
  using CT4s_Stop unfolding CT4s_def GuardCTT_def by blast

lemma CT_Guard: "CT P \<Longrightarrow> CT (g &\<^sub>C P)"
  using GuardCTT_wf CT0_Guard CT1_Guard CT2_Guard CT3_Guard  unfolding CT_def GuardCTT_def by auto

end