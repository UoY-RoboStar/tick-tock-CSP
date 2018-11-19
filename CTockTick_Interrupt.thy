theory CTockTick_Interrupt
  imports CTockTick_Core
begin

subsection {* Untimed Interrupt *}

(*function interrupt_trace_merge :: "'e cttobs list \<Rightarrow> 'e cttobs list \<Rightarrow> 'e cttobs list" where
  "interrupt_trace_merge [] [] = []" | 
  "interrupt_trace_merge [] [[Y]\<^sub>R] = []" | 
  "interrupt_trace_merge [] [[Tick]\<^sub>E] = True" | 
  "interrupt_trace_merge [] ([Event f]\<^sub>E # \<sigma>) = interrupt_trace_merge2 [] \<sigma>" | 
  "interrupt_trace_merge [] ([Y]\<^sub>R # [Tock]\<^sub>E # \<sigma>) = interrupt_trace_merge2 [] \<sigma>" | 
  "interrupt_trace_merge [[X]\<^sub>R] [] = True" | 
  "interrupt_trace_merge [[X]\<^sub>R] [[Y]\<^sub>R] = True" | 
  "interrupt_trace_merge [[X]\<^sub>R] [[Tick]\<^sub>E] = True" | 
  "interrupt_trace_merge [[X]\<^sub>R] ([Event f]\<^sub>E # \<sigma>) = interrupt_trace_merge2 [] \<sigma>" | 
  "interrupt_trace_merge [[X]\<^sub>R] ([Y]\<^sub>R # [Tock]\<^sub>E # \<sigma>) = interrupt_trace_merge2 [] \<sigma>" | 
  "interrupt_trace_merge [[Tick]\<^sub>E] [] = True" | 
  "interrupt_trace_merge [[Tick]\<^sub>E] [[Y]\<^sub>R] = True" | 
  "interrupt_trace_merge [[Tick]\<^sub>E] [[Tick]\<^sub>E] = True" | 
  "interrupt_trace_merge [[Tick]\<^sub>E] ([Event f]\<^sub>E # \<sigma>) = interrupt_trace_merge2 [] \<sigma>" | 
  "interrupt_trace_merge [[Tick]\<^sub>E] ([Y]\<^sub>R # [Tock]\<^sub>E # \<sigma>) = interrupt_trace_merge2 [] \<sigma>" | 
  "interrupt_trace_merge ([Event e]\<^sub>E # \<sigma>) [] = interrupt_trace_merge2 \<sigma> []" | 
  "interrupt_trace_merge ([Event e]\<^sub>E # \<sigma>) [[Y]\<^sub>R] = interrupt_trace_merge2 \<sigma> []" | 
  "interrupt_trace_merge ([Event e]\<^sub>E # \<sigma>) [[Tick]\<^sub>E] = interrupt_trace_merge2 \<sigma> []" | 
  "interrupt_trace_merge ([Event e]\<^sub>E # \<rho>) ([Event f]\<^sub>E # \<sigma>) = interrupt_trace_merge2 \<rho> \<sigma>" | 
  "interrupt_trace_merge ([Event e]\<^sub>E # \<rho>) ([Y]\<^sub>R # [Tock]\<^sub>E # \<sigma>) = interrupt_trace_merge2 \<rho> \<sigma>" | 
  "interrupt_trace_merge ([X]\<^sub>R # [Tock]\<^sub>E # \<sigma>) [] = interrupt_trace_merge2 \<sigma> []" | 
  "interrupt_trace_merge ([X]\<^sub>R # [Tock]\<^sub>E # \<sigma>) [[Y]\<^sub>R] = interrupt_trace_merge2 \<sigma> []" | 
  "interrupt_trace_merge ([X]\<^sub>R # [Tock]\<^sub>E # \<sigma>) [[Tick]\<^sub>E] = interrupt_trace_merge2 \<sigma> []" | 
  "interrupt_trace_merge ([X]\<^sub>R # [Tock]\<^sub>E # \<rho>) ([Event f]\<^sub>E # \<sigma>) = interrupt_trace_merge2 \<rho> \<sigma>" | 
  "interrupt_trace_merge ([X]\<^sub>R # [Tock]\<^sub>E # \<rho>) ([Y]\<^sub>R # [Tock]\<^sub>E # \<sigma>) = interrupt_trace_merge2 \<rho> \<sigma>" |
  "interrupt_trace_merge ([X]\<^sub>R # [Tick]\<^sub>E # \<rho>) \<sigma> = False" |
  "interrupt_trace_merge ([X]\<^sub>R # [Event e]\<^sub>E # \<rho>) \<sigma> = False" |
  "interrupt_trace_merge ([X]\<^sub>R # [Y]\<^sub>R # \<rho>) \<sigma> = False" |
  "interrupt_trace_merge \<rho> ([X]\<^sub>R # [Tick]\<^sub>E # \<sigma>) = False" |
  "interrupt_trace_merge \<rho> ([X]\<^sub>R # [Event e]\<^sub>E # \<sigma>) = False" |
  "interrupt_trace_merge \<rho> ([X]\<^sub>R # [Y]\<^sub>R # \<sigma>) = False" |
  "interrupt_trace_merge ([Tick]\<^sub>E # x # \<rho>) \<sigma> = False" |
  "interrupt_trace_merge \<rho> ([Tick]\<^sub>E # y # \<sigma>) = False" |
  "interrupt_trace_merge ([Tock]\<^sub>E # \<rho>) \<sigma> = False" |
  "interrupt_trace_merge \<rho> ([Tock]\<^sub>E # \<sigma>) = False"
  by (pat_completeness, simp_all)
termination by lexicographic_order
*)

thm cttWF.simps

fun intersect_refusal_trace :: "'e cttevent set \<Rightarrow> 'e cttobs list \<Rightarrow> 'e cttobs list" where
  "intersect_refusal_trace X [] = []" |
  "intersect_refusal_trace X ([e]\<^sub>E # s) = [e]\<^sub>E # intersect_refusal_trace X s" |
  "intersect_refusal_trace X ([Y]\<^sub>R # s) = [X \<inter> Y]\<^sub>R # intersect_refusal_trace X s"

lemma intersect_refusal_trace_wf:
  "cttWF t \<Longrightarrow> cttWF (intersect_refusal_trace X t)"
  by (induct t rule:cttWF.induct, auto)

lemma intersect_refusal_trace_prefix_subset:
  "intersect_refusal_trace X t \<lesssim>\<^sub>C t"
  by (induct t, auto, case_tac a, auto)

lemma prefix_subset_of_intersect_refusal_trace:
  "s \<lesssim>\<^sub>C intersect_refusal_trace X t \<Longrightarrow> \<exists> r. r \<lesssim>\<^sub>C t \<and> s = intersect_refusal_trace X r"
  apply (induct s t rule:ctt_prefix_subset.induct, auto)
  using ctt_prefix_subset.simps(1) apply fastforce
  apply (metis Int_absorb1 ctt_prefix_subset.simps(2) intersect_refusal_trace.simps(3))
  apply (metis ctt_prefix_subset.simps(3) intersect_refusal_trace.simps(2))
  done

lemma ctt_subset_of_intersect_refusal_trace:
  "s \<subseteq>\<^sub>C intersect_refusal_trace X t \<Longrightarrow> \<exists> r. r \<subseteq>\<^sub>C t \<and> s = intersect_refusal_trace X r"
  apply (induct s t rule:ctt_subset.induct, auto)
  using ctt_subset.simps(1) apply fastforce
  apply (metis Int_absorb1 ctt_subset.simps(2) intersect_refusal_trace.simps(3))
  apply (metis ctt_subset.simps(3) intersect_refusal_trace.simps(2))
  using ctt_subset_refl ctt_subset_same_length apply force
  done
  
lemma intersect_refusal_trace_subset:
  "intersect_refusal_trace X t \<subseteq>\<^sub>C t"
  by (induct t, auto, case_tac a, auto)

lemma intersect_refusal_trace_UNIV_subset_imp_subset:
  "intersect_refusal_trace UNIV s \<subseteq>\<^sub>C intersect_refusal_trace X t \<Longrightarrow> s \<subseteq>\<^sub>C t"
  apply (induct s t rule:ctt_subset.induct, auto)
  apply (metis ctt_subset.simps(6) ctt_subset.simps(8) intersect_refusal_trace_subset list.exhaust)
  using ctt_subset.simps(8) ctt_subset_trans intersect_refusal_trace_subset by blast

lemma intersect_refusal_trace_append_subset:
  "intersect_refusal_trace X t @ s \<subseteq>\<^sub>C t @ s"
  by (simp add: ctt_subset_combine ctt_subset_refl intersect_refusal_trace_subset)

lemma intersect_refusal_trace_eq_imp_subset:
  "s = intersect_refusal_trace X t \<Longrightarrow> s \<subseteq>\<^sub>C t"
  by (induct s t rule:ctt_subset.induct, auto, case_tac v, auto)

lemma intersect_refusal_trace_append_prefix_subset:
  "intersect_refusal_trace X t @ s \<lesssim>\<^sub>C t @ s"
  by (simp add: ctt_subset_imp_prefix_subset intersect_refusal_trace_append_subset)

lemma intersect_refusal_trace_append_wf:
  "cttWF (t @ s) \<Longrightarrow> cttWF (intersect_refusal_trace X t @ s)"
  using ctt_prefix_subset_cttWF intersect_refusal_trace_append_prefix_subset by blast

lemma intersect_refusal_trace_UNIV_identity:
  "intersect_refusal_trace UNIV t = t"
  by (induct t, auto, case_tac a, auto)  

lemma intersect_refusal_trace_idempotent:
  "intersect_refusal_trace X (intersect_refusal_trace X t) = intersect_refusal_trace X t"
  by (induct t, auto, case_tac a, auto)

lemma eq_intersect_refusal_trace_identity:
  "s = intersect_refusal_trace X t \<Longrightarrow> s = intersect_refusal_trace X s"
  by (induct s t rule:ctt_subset.induct, auto)

lemma intersect_refusal_trace_end_ref_imp_intersect_refusal_trace_end_event:
  "s @ [[X]\<^sub>R] = intersect_refusal_trace Z (t @ [[Y]\<^sub>R]) \<Longrightarrow> s @ [[e]\<^sub>E] = intersect_refusal_trace Z (t @ [[e]\<^sub>E])"
  by (induct s t rule:ctt_subset.induct, auto, case_tac v, auto, case_tac va, auto, case_tac a, auto)

lemma intersect_refusal_trace_end_ref_imp_intersect_refusal_trace_end_ref_tock:
  "s @ [[X]\<^sub>R] = intersect_refusal_trace Z (t @ [[Y]\<^sub>R]) \<Longrightarrow> s @ [[X]\<^sub>R, [Tock]\<^sub>E] = intersect_refusal_trace Z (t @ [[X]\<^sub>R, [Tock]\<^sub>E])"
  by (induct s t rule:ctt_subset.induct, auto, case_tac v, auto, case_tac va, auto, case_tac a, auto)

lemma ctt_prefix_subset_intersect_refusal_trace_concat:
  "r \<lesssim>\<^sub>C intersect_refusal_trace Y s @ t \<Longrightarrow>
    r \<lesssim>\<^sub>C intersect_refusal_trace Y s
    \<or> (\<exists> t' s'. intersect_refusal_trace UNIV s' \<subseteq>\<^sub>C intersect_refusal_trace Y s \<and> t' \<lesssim>\<^sub>C t \<and> r = intersect_refusal_trace Y s' @ t')"
  using ctt_prefix_subset_concat2[where r="r", where t="t", where s="intersect_refusal_trace Y s"]
proof (auto, erule_tac x="t'" in allE, auto, erule_tac x="s'" in allE, auto)
  fix t' s' t'a s'a t'b s'b
  assume "s' \<subseteq>\<^sub>C intersect_refusal_trace Y s" "\<not> intersect_refusal_trace UNIV s' \<subseteq>\<^sub>C intersect_refusal_trace Y s"
  then have "False"
    by (induct s' s rule:ctt_subset.induct, auto)
  then show "s'b @ t'b \<lesssim>\<^sub>C intersect_refusal_trace Y s"
    by auto
next
  fix t' s' t'a s'a t'b s'b
  assume "s' \<subseteq>\<^sub>C intersect_refusal_trace Y s" "s' \<noteq> intersect_refusal_trace Y s'"
  then have "False"
    by (induct s' s rule:ctt_subset.induct, auto)
  then show "s'b @ t'b \<lesssim>\<^sub>C intersect_refusal_trace Y s"
    by auto
qed

lemma eq_intersect_refusal_trace_append:
  "s @ t = intersect_refusal_trace X (s' @ t) \<Longrightarrow> s = intersect_refusal_trace X s'"
proof (induct s s' rule:ctt_subset.induct, auto)
  fix vb va
  assume "[vb]\<^sub>E # va @ t = intersect_refusal_trace X t"
  then have "[vb]\<^sub>E # va @ t \<subseteq>\<^sub>C t"
    using intersect_refusal_trace_eq_imp_subset by auto
  then have "length ([vb]\<^sub>E # va @ t) = length t"
    using ctt_subset_same_length by blast
  then show "False"
    by auto
next
  fix v va
  assume "v # va @ t = intersect_refusal_trace X t"
  then have "v # va @ t \<subseteq>\<^sub>C t"
    using intersect_refusal_trace_eq_imp_subset by auto
  then have "length (v # va @ t) = length t"
    using ctt_subset_same_length by blast
  then show "False"
    by auto
next
  fix v va
  assume "t = intersect_refusal_trace X (v # va @ t)"
  then have "t \<subseteq>\<^sub>C v # va @ t"
    using intersect_refusal_trace_eq_imp_subset by auto
  then have "length t = length (v # va @ t)"
    using ctt_subset_same_length by blast
  then show "[] = intersect_refusal_trace X (v # va)"
    by auto
next
  fix vb va
  assume case_assm: "t = [vb]\<^sub>E # intersect_refusal_trace X (va @ t)"
  then obtain vc where vc_assms: "vc = intersect_refusal_trace X (va @ t) \<and> length vc = length t - 1"
    by (cases t, auto)
  then have "vc \<subseteq>\<^sub>C va @ t"
    using intersect_refusal_trace_eq_imp_subset by auto
  then have "length vc = length (va @ t)"
    using ctt_subset_same_length by blast
  then show "False"
    using vc_assms by (auto, metis case_assm diff_Suc_less length_greater_0_conv list.simps(3) not_add_less2)
qed

lemma eq_intersect_refusal_trace_same_front:
  "s @ t = intersect_refusal_trace X (s @ t') \<Longrightarrow> t = intersect_refusal_trace X t'"
  by (induct s, auto, case_tac a, auto)

definition UntimedInterruptCTT :: "'e cttobs list set \<Rightarrow> 'e cttobs list set \<Rightarrow> 'e cttobs list set" (infixl "\<triangle>\<^sub>U" 58) where
  "P \<triangle>\<^sub>U Q = {t. \<exists> p X. p @ [[Tick]\<^sub>E] \<in> P (* if something in P ends in tick...*)
      \<and> ([[X]\<^sub>R] \<in> Q \<or> ((\<forall> Y. [[Y]\<^sub>R] \<notin> Q) \<and> X = UNIV)) \<and> t = intersect_refusal_trace X (p @ [[Tick]\<^sub>E])} (* ...then we just keep the trace, intersecting any refusals *)
    \<union> {t. \<exists> p X Y q. p @ [[X]\<^sub>R] \<in> P (* if something in P ends in a refusal...*)
      \<and> ([Y]\<^sub>R # q \<in> Q \<or> ((\<forall> Z q'. [Z]\<^sub>R # q' \<notin> Q) \<and> Y = UNIV \<and> q = [])) \<and> t = intersect_refusal_trace Y (p @ [[X]\<^sub>R]) @ q} (* ...then we just keep the trace, intersecting the refusals *)
    \<union> {t. \<exists> p q X. p \<in> P \<and> (\<nexists> p'. p = p' @ [[Tick]\<^sub>E]) \<and> (\<nexists> p' Y. p = p' @ [[Y]\<^sub>R]) (* for everything in P that doesn't end in tick or a refusal... *)
    \<and> ([[X]\<^sub>R] \<in> Q \<or> ((\<forall> Y. [[Y]\<^sub>R] \<notin> Q) \<and> X = UNIV)) (* and there is also an initial refusal Y in Q or we take Y = UNIV *)
    \<and> q \<in> Q \<and> (\<nexists> q' Y. q = [Y]\<^sub>R # q') (* and there is some trace in Q which doesn't start with a refusal *)
    \<and> t = intersect_refusal_trace X p @ q} (* ...then we just keep the trace, intersecting any refusals *)"

lemma UntimedInterruptCTT_def2:
  "P \<triangle>\<^sub>U Q = {t. \<exists> p X. p @ [[Tick]\<^sub>E] \<in> P \<and> [[X]\<^sub>R] \<in> Q \<and> t = intersect_refusal_trace X (p @ [[Tick]\<^sub>E])}
    \<union> {t. \<exists> p. p @ [[Tick]\<^sub>E] \<in> P \<and> (\<forall> Y. [[Y]\<^sub>R] \<notin> Q) \<and> t = p @ [[Tick]\<^sub>E]}
    \<union> {t. \<exists> p X Y q. p @ [[X]\<^sub>R] \<in> P \<and> [Y]\<^sub>R # q \<in> Q \<and> t = intersect_refusal_trace Y (p @ [[X]\<^sub>R]) @ q}
    \<union> {t. \<exists> p X Y q. p @ [[X]\<^sub>R] \<in> P \<and> (\<forall> Z q'. [Z]\<^sub>R # q' \<notin> Q) \<and> t = p @ [[X]\<^sub>R]}
    \<union> {t. \<exists> p q X. p \<in> P \<and> (\<nexists> p'. p = p' @ [[Tick]\<^sub>E]) \<and> (\<nexists> p' Y. p = p' @ [[Y]\<^sub>R]) \<and> [[X]\<^sub>R] \<in> Q
      \<and> q \<in> Q \<and> (\<nexists> q' Y. q = [Y]\<^sub>R # q') \<and> t = intersect_refusal_trace X p @ q}
    \<union> {t. \<exists> p q X. p \<in> P \<and> (\<nexists> p'. p = p' @ [[Tick]\<^sub>E]) \<and> (\<nexists> p' Y. p = p' @ [[Y]\<^sub>R]) \<and> (\<forall> Y. [[Y]\<^sub>R] \<notin> Q)
      \<and> q \<in> Q \<and> (\<nexists> q' Y. q = [Y]\<^sub>R # q') \<and> t = p @ q}"
  unfolding UntimedInterruptCTT_def
proof (safe, simp_all, blast)
  fix p
  assume case_assms: "p @ [[Tick]\<^sub>E] \<in> P" "\<forall>Y. [[Y]\<^sub>R] \<notin> Q"
  show "\<forall>pa. pa @ [[Tick]\<^sub>E] \<in> P \<longrightarrow> intersect_refusal_trace UNIV (p @ [[Tick]\<^sub>E]) \<noteq> pa @ [[Tick]\<^sub>E] \<Longrightarrow> False"
    by (erule_tac x="p" in allE, auto simp add: case_assms intersect_refusal_trace_UNIV_identity)
next
  fix p X Y q
  assume case_assms: "p @ [[X]\<^sub>R] \<in> P" "[Y]\<^sub>R # q \<in> Q"
  then show "\<forall>pa Xa. pa @ [[Xa]\<^sub>R] \<in> P \<longrightarrow>
      (\<forall>Ya qa. [Ya]\<^sub>R # qa \<in> Q \<longrightarrow> intersect_refusal_trace Y (p @ [[X]\<^sub>R]) @ q \<noteq> intersect_refusal_trace Ya (pa @ [[Xa]\<^sub>R]) @ qa) \<Longrightarrow>
    \<exists>pa. pa @ [[Tick]\<^sub>E] \<in> P \<and> (\<exists>Xa. [[Xa]\<^sub>R] \<in> Q \<and> intersect_refusal_trace Y (p @ [[X]\<^sub>R]) @ q = intersect_refusal_trace Xa (pa @ [[Tick]\<^sub>E]))"
    by (erule_tac x="p" in allE, erule_tac x="X" in allE, auto)
next
  fix p X
  assume case_assms: "p @ [[X]\<^sub>R] \<in> P" "\<forall>Z q'. [Z]\<^sub>R # q' \<notin> Q"
  then show "\<forall>pa Xa. pa @ [[Xa]\<^sub>R] \<in> P \<longrightarrow> intersect_refusal_trace UNIV (p @ [[X]\<^sub>R]) \<noteq> pa @ [[Xa]\<^sub>R] \<Longrightarrow> False"
    by (erule_tac x="p" in allE, erule_tac x="X" in allE, auto simp add: case_assms intersect_refusal_trace_UNIV_identity)
next
  fix p q X
  assume case_assms: "p \<in> P" "\<forall>p'. p \<noteq> p' @ [[Tick]\<^sub>E]" "\<forall>p' Y. p \<noteq> p' @ [[Y]\<^sub>R]" "q \<in> Q" "\<forall>q' Y. q \<noteq> [Y]\<^sub>R # q'" "[[X]\<^sub>R] \<in> Q"
  then show "\<forall>pa. pa \<in> P \<longrightarrow> (\<exists>p'. pa = p' @ [[Tick]\<^sub>E]) \<or> (\<exists>p' Y. pa = p' @ [[Y]\<^sub>R])
      \<or> (\<forall>qa. qa \<in> Q \<longrightarrow> (\<forall>Xa. [[Xa]\<^sub>R] \<in> Q \<longrightarrow> (\<exists>q' Y. qa = [Y]\<^sub>R # q') \<or> intersect_refusal_trace X p @ q \<noteq> intersect_refusal_trace Xa pa @ qa)) \<Longrightarrow> 
    \<exists>pa. pa @ [[Tick]\<^sub>E] \<in> P \<and> (\<exists>Xa. [[Xa]\<^sub>R] \<in> Q \<and> intersect_refusal_trace X p @ q = intersect_refusal_trace Xa (pa @ [[Tick]\<^sub>E]))"
    by (erule_tac x="p" in allE, auto, erule_tac x="q" in allE, auto)
next
  fix p q
  assume case_assms: "p \<in> P" "\<forall>p'. p \<noteq> p' @ [[Tick]\<^sub>E]" "\<forall>p' Y. p \<noteq> p' @ [[Y]\<^sub>R]" "q \<in> Q" "\<forall>q' Y. q \<noteq> [Y]\<^sub>R # q'" "\<forall>Y. [[Y]\<^sub>R] \<notin> Q"
  then show "\<forall>pa. pa \<in> P \<longrightarrow> (\<exists>p'. pa = p' @ [[Tick]\<^sub>E]) \<or> (\<exists>p' Y. pa = p' @ [[Y]\<^sub>R]) \<or> 
    (\<forall>qa. qa \<in> Q \<longrightarrow> (\<exists>q' Y. qa = [Y]\<^sub>R # q') \<or> intersect_refusal_trace UNIV p @ q \<noteq> pa @ qa) \<Longrightarrow> False"
    by (erule_tac x="p" in allE, auto, erule_tac x="q" in allE, auto simp add: intersect_refusal_trace_UNIV_identity)
next
  fix p X
  assume "p @ [[Tick]\<^sub>E] \<in> P" "[[X]\<^sub>R] \<in> Q"
  then show "\<exists>pa. pa @ [[Tick]\<^sub>E] \<in> P \<and> (\<exists>Xa. ([[Xa]\<^sub>R] \<in> Q \<or> (\<forall>Y. [[Y]\<^sub>R] \<notin> Q) \<and> Xa = UNIV) \<and>
    intersect_refusal_trace X (p @ [[Tick]\<^sub>E]) = intersect_refusal_trace Xa (pa @ [[Tick]\<^sub>E]))"
    by (rule_tac x="p" in exI, auto)
next
  fix p
  assume "p @ [[Tick]\<^sub>E] \<in> P" "\<forall>Y. [[Y]\<^sub>R] \<notin> Q"
  then show "\<exists>pa. pa @ [[Tick]\<^sub>E] \<in> P \<and> p @ [[Tick]\<^sub>E] = intersect_refusal_trace UNIV (pa @ [[Tick]\<^sub>E])"
    by (rule_tac x="p" in exI, auto simp add: intersect_refusal_trace_UNIV_identity)
next
  fix p X Y q
  assume "p @ [[X]\<^sub>R] \<in> P" "[Y]\<^sub>R # q \<in> Q"
  then show "\<forall>pa Xa. pa @ [[Xa]\<^sub>R] \<in> P \<longrightarrow> (\<forall>Ya qa. [Ya]\<^sub>R # qa \<notin> Q \<and> (Ya = UNIV \<longrightarrow> (\<exists>Z q'. [Z]\<^sub>R # q' \<in> Q) \<or> qa \<noteq> []) \<or>
      intersect_refusal_trace Y (p @ [[X]\<^sub>R]) @ q \<noteq> intersect_refusal_trace Ya (pa @ [[Xa]\<^sub>R]) @ qa) \<Longrightarrow>
    \<exists>pa. pa @ [[Tick]\<^sub>E] \<in> P \<and> (\<exists>Xa. ([[Xa]\<^sub>R] \<in> Q \<or> (\<forall>Y. [[Y]\<^sub>R] \<notin> Q) \<and> Xa = UNIV) \<and>
      intersect_refusal_trace Y (p @ [[X]\<^sub>R]) @ q = intersect_refusal_trace Xa (pa @ [[Tick]\<^sub>E]))"
    by (erule_tac x="p" in allE, erule_tac x="X" in allE, auto)
next
  fix p X
  assume "p @ [[X]\<^sub>R] \<in> P" "\<forall>Z q'. [Z]\<^sub>R # q' \<notin> Q"
  then show "\<forall>pa Xa. pa @ [[Xa]\<^sub>R] \<in> P \<longrightarrow> p @ [[X]\<^sub>R] \<noteq> intersect_refusal_trace UNIV (pa @ [[Xa]\<^sub>R]) \<Longrightarrow>
    \<exists>pa. pa @ [[Tick]\<^sub>E] \<in> P \<and> p @ [[X]\<^sub>R] = intersect_refusal_trace UNIV (pa @ [[Tick]\<^sub>E])"
    by (erule_tac x="p" in allE, auto simp add: intersect_refusal_trace_UNIV_identity)
next
  fix p q X
  assume "p \<in> P" "\<forall>p'. p \<noteq> p' @ [[Tick]\<^sub>E]" "\<forall>p' Y. p \<noteq> p' @ [[Y]\<^sub>R]" "[[X]\<^sub>R] \<in> Q" "q \<in> Q" "\<forall>q' Y. q \<noteq> [Y]\<^sub>R # q'"
  then show "\<forall>pa. pa \<in> P \<longrightarrow> (\<exists>p'. pa = p' @ [[Tick]\<^sub>E]) \<or> (\<exists>p' Y. pa = p' @ [[Y]\<^sub>R]) \<or>
      (\<forall>qa. qa \<in> Q \<longrightarrow> (\<forall>Xa. [[Xa]\<^sub>R] \<notin> Q \<and> ((\<exists>Y. [[Y]\<^sub>R] \<in> Q) \<or> Xa \<noteq> UNIV) \<or>
        (\<exists>q' Y. qa = [Y]\<^sub>R # q') \<or> intersect_refusal_trace X p @ q \<noteq> intersect_refusal_trace Xa pa @ qa)) \<Longrightarrow>
      \<exists>pa. pa @ [[Tick]\<^sub>E] \<in> P \<and> (\<exists>Xa. ([[Xa]\<^sub>R] \<in> Q \<or> (\<forall>Y. [[Y]\<^sub>R] \<notin> Q) \<and> Xa = UNIV)
        \<and> intersect_refusal_trace X p @ q = intersect_refusal_trace Xa (pa @ [[Tick]\<^sub>E]))"
    by (erule_tac x="p" in allE, auto, erule_tac x="q" in allE, auto)
next
  fix p q
  assume "p \<in> P" "\<forall>p'. p \<noteq> p' @ [[Tick]\<^sub>E]" "\<forall>p' Y. p \<noteq> p' @ [[Y]\<^sub>R]" "\<forall>Y. [[Y]\<^sub>R] \<notin> Q" "q \<in> Q" "\<forall>q' Y. q \<noteq> [Y]\<^sub>R # q'"
  then show "\<forall>pa. pa \<in> P \<longrightarrow> (\<exists>p'. pa = p' @ [[Tick]\<^sub>E]) \<or> (\<exists>p' Y. pa = p' @ [[Y]\<^sub>R])
      \<or> (\<forall>qa. qa \<in> Q \<longrightarrow> (\<exists>q' Y. qa = [Y]\<^sub>R # q') \<or> p @ q \<noteq> intersect_refusal_trace UNIV pa @ qa) \<Longrightarrow>
    \<exists>pa. pa @ [[Tick]\<^sub>E] \<in> P \<and> p @ q = intersect_refusal_trace UNIV (pa @ [[Tick]\<^sub>E])"
    by (erule_tac x="p" in allE, auto simp add: intersect_refusal_trace_UNIV_identity)    
qed

lemma event_append_wf:
  "\<And>q. \<exists> p' e. p = p' @ [[Event e]\<^sub>E] \<Longrightarrow> cttWF (p) \<Longrightarrow> cttWF (q) \<Longrightarrow> cttWF (p @ q)"
proof (auto, induct p rule:cttWF.induct, auto)
  fix q p' \<sigma> :: "'a cttobs list"
  fix e ea
  assume assm1: "\<And>q p' e. cttWF (p' @ [[Event e]\<^sub>E]) \<Longrightarrow> cttWF q \<Longrightarrow> \<sigma> = p' @ [[Event e]\<^sub>E] \<Longrightarrow> cttWF (p' @ [Event e]\<^sub>E # q)"
  assume assm2: "cttWF q"
  assume assm3: "cttWF (p' @ [[Event ea]\<^sub>E])" "[Event e]\<^sub>E # \<sigma> = p' @ [[Event ea]\<^sub>E]"
  then have "p' = [] \<or> (\<exists> p''. p' = [Event e]\<^sub>E # p'' \<and> \<sigma> = p'' @ [[Event ea]\<^sub>E])"
    by (cases p' rule:cttWF.cases, auto)
  then show "cttWF (p' @ [Event ea]\<^sub>E # q)"
    using assm2
  proof auto
    fix p''
    assume case_assm1: "\<sigma> = p'' @ [[Event ea]\<^sub>E]"
    assume case_assm2: "p' = [Event e]\<^sub>E # p''"
    have "cttWF (p'' @ [[Event ea]\<^sub>E])"
      using assm3 case_assm1 by auto
    then show "cttWF (p'' @ [Event ea]\<^sub>E # q)"
      using assm1 assm2 case_assm1 by simp
  qed
next
  fix q p' \<sigma> :: "'a cttobs list"
  fix ea X
  assume assm1: "\<And>q p' e. cttWF (p' @ [[Event e]\<^sub>E]) \<Longrightarrow> cttWF q \<Longrightarrow> \<sigma> = p' @ [[Event e]\<^sub>E] \<Longrightarrow> cttWF (p' @ [Event e]\<^sub>E # q)"
  assume assm2: "cttWF q"
  assume assm3: "cttWF (p' @ [[Event ea]\<^sub>E])" "[X]\<^sub>R # [Tock]\<^sub>E # \<sigma> = p' @ [[Event ea]\<^sub>E]"
  then have "p' = [] \<or> (\<exists> p''. p' = [X]\<^sub>R # [Tock]\<^sub>E # p'' \<and> \<sigma> = p'' @ [[Event ea]\<^sub>E])"
    by (cases p' rule:cttWF.cases, auto)
  then show "cttWF (p' @ [Event ea]\<^sub>E # q)"
    using assm2
  proof auto
    fix p''
    assume case_assm1: "\<sigma> = p'' @ [[Event ea]\<^sub>E]"
    assume case_assm2: "p' = [X]\<^sub>R # [Tock]\<^sub>E # p''"
    have "cttWF (p'' @ [[Event ea]\<^sub>E])"
      using assm3 case_assm1 by auto
    then show "cttWF (p'' @ [Event ea]\<^sub>E # q)"
      using assm1 assm2 case_assm1 by simp
  qed
next
  fix va q p' e
  assume "[Tock]\<^sub>E # va = p' @ [[Event e]\<^sub>E]"
  then obtain vb where "p' = [Tock]\<^sub>E # vb"
    by (cases p' rule:cttWF.cases, auto)
  also assume "cttWF (p' @ [[Event e]\<^sub>E])"
  then show "cttWF (p' @ [Event e]\<^sub>E # q)"
    using calculation by auto
next
  fix va q p' e
  assume "[Tock]\<^sub>E # va = p' @ [[Event e]\<^sub>E]"
  then obtain vb where "p' = [Tock]\<^sub>E # vb"
    by (cases p' rule:cttWF.cases, auto)
  also assume "cttWF (p' @ [[Event e]\<^sub>E])"
  then show "cttWF (p' @ [Event e]\<^sub>E # q)"
    using calculation by auto
next
  fix va q p' e
  assume "[Tock]\<^sub>E # va = p' @ [[Event e]\<^sub>E]"
  then obtain vb where "p' = [Tock]\<^sub>E # vb"
    by (cases p' rule:cttWF.cases, auto)
  also assume "cttWF (p' @ [[Event e]\<^sub>E])"
  then show "cttWF (p' @ [Event e]\<^sub>E # q)"
    using calculation by auto
next
  fix v vc q p' e
  assume "[Tick]\<^sub>E # v # vc = p' @ [[Event e]\<^sub>E]"
  then obtain vb where "p' = [Tick]\<^sub>E # vb"
    by (cases p' rule:cttWF.cases, auto)
  also assume "cttWF (p' @ [[Event e]\<^sub>E])"
  then show "cttWF (p' @ [Event e]\<^sub>E # q)"
    using calculation by (auto, cases vb, auto)
next
  fix v vc q p' e
  assume "[Tick]\<^sub>E # v # vc = p' @ [[Event e]\<^sub>E]"
  then obtain vb where "p' = [Tick]\<^sub>E # vb"
    by (cases p' rule:cttWF.cases, auto)
  also assume "cttWF (p' @ [[Event e]\<^sub>E])"
  then show "cttWF (p' @ [Event e]\<^sub>E # q)"
    using calculation by (auto, cases vb, auto)
next
  fix va vd vc q p' e
  assume "[va]\<^sub>R # [Event vd]\<^sub>E # vc = p' @ [[Event e]\<^sub>E]"
  then obtain vb where "p' = [va]\<^sub>R # [Event vd]\<^sub>E # vb \<or> p' = [[va]\<^sub>R]"
    by (cases p' rule:cttWF.cases, auto)
  also assume "cttWF (p' @ [[Event e]\<^sub>E])"
  then show "cttWF (p' @ [Event e]\<^sub>E # q)"
    using calculation by (auto)
next
  fix va vd vc q p' e
  assume "[va]\<^sub>R # [Tick]\<^sub>E # vc = p' @ [[Event e]\<^sub>E]"
  then obtain vb where "p' = [va]\<^sub>R # [Tick]\<^sub>E # vb \<or> p' = [[va]\<^sub>R]"
    by (cases p' rule:cttWF.cases, auto)
  also assume "cttWF (p' @ [[Event e]\<^sub>E])"
  then show "cttWF (p' @ [Event e]\<^sub>E # q)"
    using calculation by (auto)
next
  fix va v vc q p' e
  assume "[va]\<^sub>R # [v]\<^sub>R # vc = p' @ [[Event e]\<^sub>E]"
  then obtain vb where "p' = [va]\<^sub>R # [v]\<^sub>R # vb \<or> p' = [[va]\<^sub>R]"
    by (cases p' rule:cttWF.cases, auto)
  also assume "cttWF (p' @ [[Event e]\<^sub>E])"
  then show "cttWF (p' @ [Event e]\<^sub>E # q)"
    using calculation by (auto)
qed
  

lemma refusal_tock_append_wf:
  "\<And>q. \<exists> p' X. p = p' @ [[X]\<^sub>R, [Tock]\<^sub>E] \<Longrightarrow> cttWF (p) \<Longrightarrow> cttWF (q) \<Longrightarrow> cttWF (p @ q)"
proof (auto, induct p rule:cttWF.induct, auto)
  fix q p' \<sigma> :: "'a cttobs list"
  fix e X
  assume assm1: "\<And>q p' X. cttWF (p' @ [[X]\<^sub>R, [Tock]\<^sub>E]) \<Longrightarrow> cttWF q \<Longrightarrow> \<sigma> = p' @ [[X]\<^sub>R, [Tock]\<^sub>E] \<Longrightarrow> cttWF (p' @ [X]\<^sub>R # [Tock]\<^sub>E # q)"
  assume assm2: "cttWF q"
  assume assm3: "cttWF (p' @ [[X]\<^sub>R, [Tock]\<^sub>E])" "[Event e]\<^sub>E # \<sigma> = p' @ [[X]\<^sub>R, [Tock]\<^sub>E]"
  then have "p' = [] \<or> (\<exists> p''. p' = [Event e]\<^sub>E # p'' \<and> \<sigma> = p'' @ [[X]\<^sub>R, [Tock]\<^sub>E])"
    by (cases p' rule:cttWF.cases, auto)
  then show "cttWF (p' @ [X]\<^sub>R # [Tock]\<^sub>E # q)"
    using assm2
  proof auto
    fix p''
    assume case_assm1: "\<sigma> = p'' @ [[X]\<^sub>R, [Tock]\<^sub>E]"
    assume case_assm2: "p' = [Event e]\<^sub>E # p''"
    have "cttWF (p'' @ [[X]\<^sub>R, [Tock]\<^sub>E])"
      using assm3 case_assm1 by auto
    then show "cttWF (p'' @ [X]\<^sub>R # [Tock]\<^sub>E # q)"
      using assm1 assm2 case_assm1 by simp
  qed
next
  fix q p' \<sigma> :: "'a cttobs list"
  fix X Xa
  assume assm1: "\<And>q p' X. cttWF (p' @ [[X]\<^sub>R, [Tock]\<^sub>E]) \<Longrightarrow> cttWF q \<Longrightarrow> \<sigma> = p' @ [[X]\<^sub>R, [Tock]\<^sub>E] \<Longrightarrow> cttWF (p' @ [X]\<^sub>R # [Tock]\<^sub>E # q)"
  assume assm2: "cttWF q"
  assume assm3: "cttWF (p' @ [[Xa]\<^sub>R, [Tock]\<^sub>E])" "[X]\<^sub>R # [Tock]\<^sub>E # \<sigma> = p' @ [[Xa]\<^sub>R, [Tock]\<^sub>E] "
  then have "p' = [] \<or> (\<exists> p''. p' = [X]\<^sub>R # [Tock]\<^sub>E # p'' \<and> \<sigma> = p'' @ [[Xa]\<^sub>R, [Tock]\<^sub>E])"
    by (cases p' rule:cttWF.cases, auto)
  then show "cttWF (p' @ [Xa]\<^sub>R # [Tock]\<^sub>E # q)"
    using assm2
  proof auto
    fix p''
    assume case_assm1: "\<sigma> = p'' @ [[Xa]\<^sub>R, [Tock]\<^sub>E]"
    assume case_assm2: "p' = [X]\<^sub>R # [Tock]\<^sub>E # p''"
    have "cttWF (p'' @ [[Xa]\<^sub>R, [Tock]\<^sub>E])"
      using assm3 case_assm1 by auto
    then show "cttWF (p'' @ [Xa]\<^sub>R # [Tock]\<^sub>E # q)"
      using assm1 assm2 case_assm1 by simp
  qed
next
  fix va q p' X
  assume "[Tock]\<^sub>E # va = p' @ [[X]\<^sub>R, [Tock]\<^sub>E]"
  then obtain vb where "p' = [Tock]\<^sub>E # vb"
    by (cases p' rule:cttWF.cases, auto)
  also assume "cttWF (p' @ [[X]\<^sub>R, [Tock]\<^sub>E])"
  then show "cttWF (p' @ [X]\<^sub>R # [Tock]\<^sub>E # q)"
    using calculation by auto
next
  fix va q p' X
  assume "[Tock]\<^sub>E # va = p' @ [[X]\<^sub>R, [Tock]\<^sub>E]"
  then obtain vb where "p' = [Tock]\<^sub>E # vb"
    by (cases p' rule:cttWF.cases, auto)
  also assume "cttWF (p' @ [[X]\<^sub>R, [Tock]\<^sub>E])"
  then show "cttWF (p' @ [X]\<^sub>R # [Tock]\<^sub>E # q)"
    using calculation by auto
next
  fix va q p' X
  assume "[Tock]\<^sub>E # va = p' @ [[X]\<^sub>R, [Tock]\<^sub>E]"
  then obtain vb where "p' = [Tock]\<^sub>E # vb"
    by (cases p' rule:cttWF.cases, auto)
  also assume "cttWF (p' @ [[X]\<^sub>R, [Tock]\<^sub>E])"
  then show "cttWF (p' @ [X]\<^sub>R # [Tock]\<^sub>E # q)"
    using calculation by auto
next
  fix v vc q p' X
  assume "[Tick]\<^sub>E # v # vc = p' @ [[X]\<^sub>R, [Tock]\<^sub>E]"
  then obtain vb where "p' = [Tick]\<^sub>E # vb"
    by (cases p' rule:cttWF.cases, auto)
  also assume "cttWF (p' @ [[X]\<^sub>R, [Tock]\<^sub>E])"
  then show "cttWF (p' @ [X]\<^sub>R # [Tock]\<^sub>E # q)"
    using calculation by (auto, cases vb, auto)
next
  fix v vc q p' X
  assume "[Tick]\<^sub>E # v # vc = p' @ [[X]\<^sub>R, [Tock]\<^sub>E]"
  then obtain vb where "p' = [Tick]\<^sub>E # vb"
    by (cases p' rule:cttWF.cases, auto)
  also assume "cttWF (p' @ [[X]\<^sub>R, [Tock]\<^sub>E])"
  then show "cttWF (p' @ [X]\<^sub>R # [Tock]\<^sub>E # q)"
    using calculation by (auto, cases vb, auto)
next
  fix va vd vc q p' X
  assume "[va]\<^sub>R # [Event vd]\<^sub>E # vc = p' @ [[X]\<^sub>R, [Tock]\<^sub>E]"
  then obtain vb where "p' = [va]\<^sub>R # [Event vd]\<^sub>E # vb \<or> p' = [[va]\<^sub>R]"
    by (cases p' rule:cttWF.cases, auto)
  also assume "cttWF (p' @ [[X]\<^sub>R, [Tock]\<^sub>E])"
  then show "cttWF (p' @ [X]\<^sub>R # [Tock]\<^sub>E # q)"
    using calculation by (auto)
next
  fix va vc q p' X
  assume "[va]\<^sub>R # [Tick]\<^sub>E # vc = p' @ [[X]\<^sub>R, [Tock]\<^sub>E]"
  then obtain vb where "p' = [va]\<^sub>R # [Tick]\<^sub>E # vb \<or> p' = [[va]\<^sub>R]"
    by (cases p' rule:cttWF.cases, auto)
  also assume "cttWF (p' @ [[X]\<^sub>R, [Tock]\<^sub>E])"
  then show "cttWF (p' @ [X]\<^sub>R # [Tock]\<^sub>E # q)"
    using calculation by (auto)
next
  fix va v vc q p' X
  assume "[va]\<^sub>R # [v]\<^sub>R # vc = p' @ [[X]\<^sub>R, [Tock]\<^sub>E]"
  then obtain vb where "p' = [va]\<^sub>R # [v]\<^sub>R # vb \<or> p' = [[va]\<^sub>R]"
    by (cases p' rule:cttWF.cases, auto)
  also assume "cttWF (p' @ [[X]\<^sub>R, [Tock]\<^sub>E])"
  then show "cttWF (p' @ [X]\<^sub>R # [Tock]\<^sub>E # q)"
    using calculation by (auto)
qed

lemma tock_append_wf:
  "\<exists> p' X. p = p' @ [[Tock]\<^sub>E] \<Longrightarrow> cttWF (p) \<Longrightarrow> cttWF (q) \<Longrightarrow> cttWF (p @ q)"
proof auto
  fix p'
  assume "cttWF (p' @ [[Tock]\<^sub>E])" "p = p' @ [[Tock]\<^sub>E]"
  also have "\<And> p. cttWF (p' @ [[Tock]\<^sub>E]) \<Longrightarrow> p = p' @ [[Tock]\<^sub>E] \<Longrightarrow> \<exists> X p''. p = p'' @ [[X]\<^sub>R, [Tock]\<^sub>E]"
    by (induct p' rule:cttWF.induct, auto, fastforce+)
  then have "\<exists> p'' X. p = p'' @ [[X]\<^sub>R, [Tock]\<^sub>E]"
    using calculation by fastforce
  then show "cttWF (p' @ [[Tock]\<^sub>E]) \<Longrightarrow> cttWF q \<Longrightarrow> p = p' @ [[Tock]\<^sub>E] \<Longrightarrow> cttWF (p' @ [Tock]\<^sub>E # q)"
    using refusal_tock_append_wf by fastforce
qed

lemma end_refusal_start_refusal_append_wf:
  "cttWF (p @ [[X]\<^sub>R]) \<Longrightarrow> cttWF ([Y]\<^sub>R # q) \<Longrightarrow> cttWF ((p @ [[Z]\<^sub>R]) @ q)"
  by (induct p rule:cttWF.induct, auto, induct q rule:cttWF.induct, auto)

lemma nontick_event_end_append_wf:
  assumes "cttWF p" "cttWF q"
  assumes "\<forall>p'. p \<noteq> p' @ [[Tick]\<^sub>E]" "\<forall>p' Y. p \<noteq> p' @ [[Y]\<^sub>R]"
  shows "cttWF (p @ q)"
proof -
  have "p = [] \<or> (\<exists> p' x. p = p' @ [x])"
    by (induct p, auto)
  then have "p = [] \<or> (\<exists> p' e. p = p' @ [[Event e]\<^sub>E]) \<or> (\<exists> p' X. p = p' @ [[Tock]\<^sub>E])"
    using assms(3) assms(4) by (auto, (case_tac x, auto, case_tac x1, auto)+)
  then show ?thesis
    using assms(1) assms(2) event_append_wf tock_append_wf by (auto, fastforce+)
qed
    
lemma UntimedInterruptCTT_wf:
  assumes "\<forall>x\<in>P. cttWF x" "\<forall>x\<in>Q. cttWF x"
  shows "\<forall>x\<in>(P \<triangle>\<^sub>U Q). cttWF x"
  using assms unfolding UntimedInterruptCTT_def
proof auto
  fix p X
  assume "\<forall>x\<in>P. cttWF x" "\<forall>x\<in>Q. cttWF x" "p @ [[Tick]\<^sub>E] \<in> P" "[[X]\<^sub>R] \<in> Q"
  then show "cttWF (intersect_refusal_trace X (p @ [[Tick]\<^sub>E]))"
    using intersect_refusal_trace_wf by (blast)
next
  fix p 
  assume "\<forall>x\<in>P. cttWF x" "\<forall>x\<in>Q. cttWF x" "p @ [[Tick]\<^sub>E] \<in> P" "\<forall>Y. [[Y]\<^sub>R] \<notin> Q"
  then show "cttWF (intersect_refusal_trace UNIV (p @ [[Tick]\<^sub>E]))"
    using intersect_refusal_trace_wf by (blast)
next
  fix p X Y q
  assume "\<forall>x\<in>P. cttWF x" "\<forall>x\<in>Q. cttWF x" "p @ [[X]\<^sub>R] \<in> P" "[Y]\<^sub>R # q \<in> Q"
  then show "cttWF (intersect_refusal_trace Y (p @ [[X]\<^sub>R]) @ q)"
    using end_refusal_start_refusal_append_wf intersect_refusal_trace_append_wf by (blast)
next
  fix p X
  assume "\<forall>x\<in>P. cttWF x" "\<forall>x\<in>Q. cttWF x" "p @ [[X]\<^sub>R] \<in> P" "\<forall>Z q'. [Z]\<^sub>R # q' \<notin> Q"
  then show "cttWF (intersect_refusal_trace UNIV (p @ [[X]\<^sub>R]))"
    using intersect_refusal_trace_wf by (blast)
next
  fix p q X
  assume "\<forall>x\<in>P. cttWF x" "\<forall>x\<in>Q. cttWF x" "p \<in> P" "\<forall>p'. p \<noteq> p' @ [[Tick]\<^sub>E]" "\<forall>p' Y. p \<noteq> p' @ [[Y]\<^sub>R]" "q \<in> Q"
  then also have "cttWF (p @ q)"
    using nontick_event_end_append_wf by blast
  then show "cttWF (intersect_refusal_trace X p @ q)"
    using intersect_refusal_trace_append_wf by blast
next
  fix p q
  assume "\<forall>x\<in>P. cttWF x" "\<forall>x\<in>Q. cttWF x" "p \<in> P" "\<forall>p'. p \<noteq> p' @ [[Tick]\<^sub>E]" "\<forall>p' Y. p \<noteq> p' @ [[Y]\<^sub>R]" "q \<in> Q"
  then also have "cttWF (p @ q)"
    using nontick_event_end_append_wf by blast
  then show "cttWF (intersect_refusal_trace UNIV p @ q)"
    using intersect_refusal_trace_append_wf by blast
qed

lemma CT0_UntimedInterrupt:
  assumes "CT0 P" "CT1 P" "CT0 Q" "CT1 Q"
  shows "CT0 (P \<triangle>\<^sub>U Q)"
  unfolding UntimedInterruptCTT_def CT0_def
proof auto
  have empty_in_P_Q: "[] \<in> P" "[] \<in> Q"
    by (simp_all add: CT0_CT1_empty assms)
  assume "\<forall>x p. p \<in> P \<longrightarrow> (\<exists>p'. p = p' @ [[Tick]\<^sub>E]) \<or> (\<exists>p' Y. p = p' @ [[Y]\<^sub>R]) \<or>
      (\<forall>q. q \<in> Q \<longrightarrow> (\<forall>X. [[X]\<^sub>R] \<notin> Q \<and> ((\<exists>Y. [[Y]\<^sub>R] \<in> Q) \<or> X \<noteq> UNIV) \<or>
      (\<exists>q' Y. q = [Y]\<^sub>R # q') \<or> x \<noteq> intersect_refusal_trace X p @ q))"
  then have "\<forall>p. p \<in> P \<longrightarrow> (\<exists>p'. p = p' @ [[Tick]\<^sub>E]) \<or> (\<exists>p' Y. p = p' @ [[Y]\<^sub>R]) \<or>
      (\<forall>q. q \<in> Q \<longrightarrow> (\<forall>X. [[X]\<^sub>R] \<notin> Q \<and> ((\<exists>Y. [[Y]\<^sub>R] \<in> Q) \<or> X \<noteq> UNIV) \<or>
      (\<exists>q' Y. q = [Y]\<^sub>R # q') \<or> [] \<noteq> intersect_refusal_trace X p @ q))"
    by auto
  then have "(\<forall>q. q \<in> Q \<longrightarrow> (\<forall>X. [[X]\<^sub>R] \<notin> Q \<and> ((\<exists>Y. [[Y]\<^sub>R] \<in> Q) \<or> X \<noteq> UNIV) \<or>
      (\<exists>q' Y. q = [Y]\<^sub>R # q') \<or> [] \<noteq> intersect_refusal_trace X [] @ q))"
    using empty_in_P_Q by blast
  then have "\<forall>X. [[X]\<^sub>R] \<notin> Q \<and> ((\<exists>Y. [[Y]\<^sub>R] \<in> Q) \<or> X \<noteq> UNIV)"
    using empty_in_P_Q by auto
  then have "False"
    by blast
  then show "\<exists>x p X. p @ [[X]\<^sub>R] \<in> P \<and> (\<exists>Y q. ([Y]\<^sub>R # q \<in> Q \<or> Y = UNIV \<and> (\<forall>Z q'. [Z]\<^sub>R # q' \<notin> Q) \<and> q = []) \<and>
      x = intersect_refusal_trace Y (p @ [[X]\<^sub>R]) @ q)"
    by auto
qed

lemma CT1_UntimedInterrupt:
  assumes P_wf: "\<forall>x\<in>P. cttWF x"
  assumes CT1_P: "CT1 P" and CT0_Q: "CT0 Q" and CT1_Q: "CT1 Q"
  shows "CT1 (P \<triangle>\<^sub>U Q)"
  unfolding CT1_def
proof (auto)
  fix \<rho> \<sigma>
  assume "\<sigma> \<in> P \<triangle>\<^sub>U Q"
  (*then have "(\<exists>p X. p @ [[Tick]\<^sub>E] \<in> P \<and> [[X]\<^sub>R] \<in> Q \<and> \<rho> = intersect_refusal_trace X (p @ [[Tick]\<^sub>E]))
    \<or> (\<exists>p X Y. p @ [[X]\<^sub>R] \<in> P \<and> [[Y]\<^sub>R] \<in> Q \<and> \<rho> = intersect_refusal_trace Y (p @ [[X]\<^sub>R]))
    \<or> (\<exists>p X e. p @ [[Event e]\<^sub>E] \<in> P \<and> [[X]\<^sub>R] \<in> Q \<and> \<rho> = intersect_refusal_trace X (p @ [[Event e]\<^sub>E]))
    \<or> (\<exists>p X e. p @ [[Tock]\<^sub>E] \<in> P \<and> [[X]\<^sub>R] \<in> Q \<and> \<rho> = intersect_refusal_trace X (p @ [[Tock]\<^sub>E]))
    \<or> (\<exists>p X. p @ [[Tick]\<^sub>E] \<in> P \<and> (\<forall>Y. [[Y]\<^sub>R] \<notin> Q) \<and> \<rho> = intersect_refusal_trace UNIV (p @ [[Tick]\<^sub>E]))
    \<or> (\<exists>p X Y. p @ [[X]\<^sub>R] \<in> P \<and> (\<forall>Z. [[Z]\<^sub>R] \<notin> Q) \<and> \<rho> = intersect_refusal_trace UNIV (p @ [[X]\<^sub>R]))
    \<or> (\<exists>p X e. p @ [[Event e]\<^sub>E] \<in> P \<and> (\<forall>Y. [[Y]\<^sub>R] \<notin> Q) \<and> \<rho> = intersect_refusal_trace UNIV (p @ [[Event e]\<^sub>E]))
    \<or> (\<exists>p X e. p @ [[Tock]\<^sub>E] \<in> P \<and> (\<forall>Y. [[Y]\<^sub>R] \<notin> Q) \<and> \<rho> = intersect_refusal_trace UNIV (p @ [[Tock]\<^sub>E]))
    \<or> (\<exists>p X Y q. p @ [[X]\<^sub>R] \<in> P \<and> [Y]\<^sub>R # q \<in> Q \<and> \<rho> = intersect_refusal_trace Y (p @ [[X]\<^sub>R]) @ q)
    \<or> (\<exists>p X Y. p @ [[X]\<^sub>R] \<in> P \<and> (\<forall>Z q'. [Z]\<^sub>R # q' \<notin> Q) \<and> \<rho> = intersect_refusal_trace UNIV (p @ [[X]\<^sub>R]))
    \<or> (\<exists>p q X. p \<in> P \<and> (\<nexists>p'. p = p' @ [[Tick]\<^sub>E]) \<and> (\<nexists>p' Y. p = p' @ [[Y]\<^sub>R]) \<and> [[X]\<^sub>R] \<in> Q \<and>
            q \<in> Q \<and> (\<nexists>q' Y. q = [Y]\<^sub>R # q') \<and> \<rho> = intersect_refusal_trace X p @ q)
    \<or> (\<exists>p q X. p \<in> P \<and> (\<nexists>p'. p = p' @ [[Tick]\<^sub>E]) \<and> (\<nexists>p' Y. p = p' @ [[Y]\<^sub>R]) \<and> (\<forall>Y. [[Y]\<^sub>R] \<notin> Q) \<and>
            q \<in> Q \<and> (\<nexists>q' Y. q = [Y]\<^sub>R # q') \<and> \<rho> = intersect_refusal_trace UNIV p @ q)"*)
  thm UntimedInterruptCTT_def
  then have "(\<exists>p X. p @ [[Tick]\<^sub>E] \<in> P \<and> [[X]\<^sub>R] \<in> Q \<and> \<sigma> = intersect_refusal_trace X (p @ [[Tick]\<^sub>E]))
      \<or> (\<exists>p X. p @ [[Tick]\<^sub>E] \<in> P \<and> (\<forall>Y. [[Y]\<^sub>R] \<notin> Q) \<and> X = UNIV \<and> \<sigma> = intersect_refusal_trace X (p @ [[Tick]\<^sub>E]))
      \<or> (\<exists>p X Y q. p @ [[X]\<^sub>R] \<in> P \<and> [Y]\<^sub>R # q \<in> Q \<and> \<sigma> = intersect_refusal_trace Y (p @ [[X]\<^sub>R]) @ q)
      \<or> (\<exists>p X Y q. p @ [[X]\<^sub>R] \<in> P \<and> (\<forall>Z q'. [Z]\<^sub>R # q' \<notin> Q) \<and> Y = UNIV \<and> q = [] \<and> \<sigma> = intersect_refusal_trace Y (p @ [[X]\<^sub>R]) @ q)
      \<or> (\<exists>p q X. p \<in> P \<and> (\<nexists>p'. p = p' @ [[Tick]\<^sub>E]) \<and> (\<nexists>p' Y. p = p' @ [[Y]\<^sub>R]) \<and> [[X]\<^sub>R] \<in> Q \<and> q \<in> Q \<and> (\<nexists>q' Y. q = [Y]\<^sub>R # q') \<and> \<sigma> = intersect_refusal_trace X p @ q)
      \<or> (\<exists>p q X. p \<in> P \<and> (\<nexists>p'. p = p' @ [[Tick]\<^sub>E]) \<and> (\<nexists>p' Y. p = p' @ [[Y]\<^sub>R]) \<and> (\<forall>Y. [[Y]\<^sub>R] \<notin> Q) \<and> X = UNIV \<and> q \<in> Q \<and> (\<nexists>q' Y. q = [Y]\<^sub>R # q') \<and> \<sigma> = intersect_refusal_trace X p @ q)"
    unfolding UntimedInterruptCTT_def apply safe by blast+
  then show "\<rho> \<lesssim>\<^sub>C \<sigma> \<Longrightarrow> \<rho> \<in> P \<triangle>\<^sub>U Q"
  proof auto
    fix p X
    assume in_P: "p @ [[Tick]\<^sub>E] \<in> P"
    assume "\<rho> \<lesssim>\<^sub>C intersect_refusal_trace X (p @ [[Tick]\<^sub>E])"
    then obtain p' where p'_assms: "p' \<lesssim>\<^sub>C p @ [[Tick]\<^sub>E] \<and> \<rho> = intersect_refusal_trace X p'"
      using prefix_subset_of_intersect_refusal_trace by blast
    have p'_cases: "(\<exists>p''. p' = p'' @ [[Tick]\<^sub>E]) \<or> (\<exists>p'' Y. p' = p'' @ [[Y]\<^sub>R])
        \<or> ((\<nexists>p''. p' = p'' @ [[Tick]\<^sub>E]) \<and> (\<nexists>p'' Y. p' = p'' @ [[Y]\<^sub>R]))"
      by auto
    have p'_in_P: "p' \<in> P"
      using p'_assms CT1_P in_P unfolding CT1_def by auto
    assume Q_assm: "[[X]\<^sub>R] \<in> Q" 
    show "\<rho> \<in> P \<triangle>\<^sub>U Q"
      using p'_cases p'_in_P Q_assm p'_assms unfolding UntimedInterruptCTT_def
    proof auto
      assume case_assms: "p' \<in> P" "[[X]\<^sub>R] \<in> Q" "\<forall>p''. p' \<noteq> p'' @ [[Tick]\<^sub>E]" "\<forall>p'' Y. p' \<noteq> p'' @ [[Y]\<^sub>R]"
      show "\<forall>p. p \<in> P \<longrightarrow> (\<exists>p'. p = p' @ [[Tick]\<^sub>E]) \<or> (\<exists>p' Y. p = p' @ [[Y]\<^sub>R]) \<or>
        (\<forall>q. q \<in> Q \<longrightarrow> (\<forall>Xa. [[Xa]\<^sub>R] \<notin> Q \<and> ((\<exists>Y. [[Y]\<^sub>R] \<in> Q) \<or> Xa \<noteq> UNIV) \<or>
          (\<exists>q' Y. q = [Y]\<^sub>R # q') \<or> intersect_refusal_trace X p' \<noteq> intersect_refusal_trace Xa p @ q)) \<Longrightarrow>
        \<exists>p Xa. p @ [[Xa]\<^sub>R] \<in> P \<and>
          (\<exists>Y q. ([Y]\<^sub>R # q \<in> Q \<or> (\<forall>Z q'. [Z]\<^sub>R # q' \<notin> Q) \<and> Y = UNIV \<and> q = []) \<and>
            intersect_refusal_trace X p' = intersect_refusal_trace Y (p @ [[Xa]\<^sub>R]) @ q)"
        apply (erule_tac x="p'" in allE, simp_all add: case_assms)
        apply (erule_tac x="[]" in allE, simp_all add: case_assms)
        using CT1_Q CT1_def Q_assm ctt_prefix_subset.simps(1) by blast
    qed
  next
    fix p
    assume in_P: "p @ [[Tick]\<^sub>E] \<in> P"
    assume "\<rho> \<lesssim>\<^sub>C intersect_refusal_trace UNIV (p @ [[Tick]\<^sub>E])"
    then obtain p' where p'_assms: "p' \<lesssim>\<^sub>C p @ [[Tick]\<^sub>E] \<and> \<rho> = intersect_refusal_trace UNIV p'"
      using prefix_subset_of_intersect_refusal_trace by blast
    have p'_cases: "(\<exists>p''. p' = p'' @ [[Tick]\<^sub>E]) \<or> (\<exists>p'' Y. p' = p'' @ [[Y]\<^sub>R])
        \<or> ((\<nexists>p''. p' = p'' @ [[Tick]\<^sub>E]) \<and> (\<nexists>p'' Y. p' = p'' @ [[Y]\<^sub>R]))"
      by auto
    have p'_in_P: "p' \<in> P"
      using p'_assms CT1_P in_P unfolding CT1_def by auto
    assume "\<forall>Y. [[Y]\<^sub>R] \<notin> Q"
    then have Q_assm: "\<forall>Z q'. [Z]\<^sub>R # q' \<notin> Q"
    proof auto
      fix Z q'
      assume "[Z]\<^sub>R # q' \<in> Q"
      then have "[[Z]\<^sub>R] \<in> Q"
        using CT1_Q unfolding CT1_def apply auto by (erule_tac x="[[Z]\<^sub>R]" in allE, auto)
      also assume " \<forall>Y. [[Y]\<^sub>R] \<notin> Q"
      then show "False"
        using calculation by auto
    qed
    show "\<rho> \<in> P \<triangle>\<^sub>U Q"
      using p'_cases p'_in_P Q_assm p'_assms unfolding UntimedInterruptCTT_def
    proof auto
      assume case_assms: "p' \<in> P" "\<forall>Z q'. [Z]\<^sub>R # q' \<notin> Q" "\<forall>p''. p' \<noteq> p'' @ [[Tick]\<^sub>E]" "\<forall>p'' Y. p' \<noteq> p'' @ [[Y]\<^sub>R]"
      then show "\<forall>p. p \<in> P \<longrightarrow> (\<exists>p'. p = p' @ [[Tick]\<^sub>E]) \<or> (\<exists>p' Y. p = p' @ [[Y]\<^sub>R]) \<or>
        (\<forall>q. q \<in> Q \<longrightarrow> (\<exists>q' Y. q = [Y]\<^sub>R # q') \<or> intersect_refusal_trace UNIV p' \<noteq> intersect_refusal_trace UNIV p @ q) \<Longrightarrow>
         \<exists>p X. p @ [[X]\<^sub>R] \<in> P \<and> intersect_refusal_trace UNIV p' = intersect_refusal_trace UNIV (p @ [[X]\<^sub>R])"
        apply (erule_tac x="p'" in allE, simp_all add: case_assms)
        apply (erule_tac x="[]" in allE, simp_all add: case_assms)
        using CT0_CT1_empty CT0_Q CT1_Q by blast
    qed
  next
    fix p q
    fix X Y
    assume in_P: "p @ [[X]\<^sub>R] \<in> P"
    assume in_Q: "[Y]\<^sub>R # q \<in> Q"
    then have Y_in_Q: "[[Y]\<^sub>R] \<in> Q"
      by (meson CT1_Q CT1_def ctt_prefix_subset.simps(1) ctt_prefix_subset.simps(2) ctt_prefix_subset_refl)
    assume "\<rho> \<lesssim>\<^sub>C intersect_refusal_trace Y (p @ [[X]\<^sub>R]) @ q"
    then have  "\<rho> \<lesssim>\<^sub>C intersect_refusal_trace Y (p @ [[X]\<^sub>R])
      \<or> (\<exists> q' p'. intersect_refusal_trace UNIV p' \<subseteq>\<^sub>C intersect_refusal_trace Y (p @ [[X]\<^sub>R]) 
        \<and> q' \<lesssim>\<^sub>C q \<and> \<rho> = intersect_refusal_trace Y p' @ q')"
      using ctt_prefix_subset_intersect_refusal_trace_concat by auto
    then have  "\<rho> \<lesssim>\<^sub>C intersect_refusal_trace Y (p @ [[X]\<^sub>R])
      \<or> (\<exists> q' p' X'. intersect_refusal_trace Y (p' @ [[X']\<^sub>R]) \<subseteq>\<^sub>C intersect_refusal_trace Y (p @ [[X]\<^sub>R]) 
        \<and> p' @ [[X']\<^sub>R] \<subseteq>\<^sub>C p @ [[X]\<^sub>R] \<and> q' \<lesssim>\<^sub>C q \<and> \<rho> = intersect_refusal_trace Y (p' @ [[X']\<^sub>R]) @ q')"
    proof (auto, erule_tac x="q'" in allE, auto)
      fix q' p' q'a p'a
      assume case_assm: "intersect_refusal_trace UNIV p' \<subseteq>\<^sub>C intersect_refusal_trace Y (p @ [[X]\<^sub>R])"
      then have 1: "p' \<subseteq>\<^sub>C p @ [[X]\<^sub>R]"
        using intersect_refusal_trace_UNIV_subset_imp_subset by blast
      then obtain p'' X' where "p' = p'' @ [[X']\<^sub>R]"
        using ctt_subset_same_length by (-, induct p' p rule:ctt_subset.induct, auto, case_tac v, auto, fastforce)
      then show "\<forall>p'a X'. p'a @ [[X']\<^sub>R] \<subseteq>\<^sub>C p @ [[X]\<^sub>R] \<longrightarrow>
                intersect_refusal_trace Y (p'a @ [[X']\<^sub>R]) \<subseteq>\<^sub>C intersect_refusal_trace Y (p @ [[X]\<^sub>R]) \<longrightarrow>
                intersect_refusal_trace Y p' \<noteq> intersect_refusal_trace Y (p'a @ [[X']\<^sub>R]) \<Longrightarrow>
        intersect_refusal_trace Y p'a @ q'a \<lesssim>\<^sub>C intersect_refusal_trace Y (p @ [[X]\<^sub>R])"
        using case_assm 1 apply (erule_tac x="p''" in allE, auto, erule_tac x="X'" in allE, auto)
        by (metis ctt_subset_trans intersect_refusal_trace_UNIV_identity intersect_refusal_trace_subset)
    qed
    then show "\<rho> \<in> P \<triangle>\<^sub>U Q"
    proof auto
      have cttWF_p_ref: "cttWF (p @ [[X]\<^sub>R])"
        by (simp add: P_wf in_P)
      assume "\<rho> \<lesssim>\<^sub>C intersect_refusal_trace Y (p @ [[X]\<^sub>R])"
      then obtain p' where p'_assms: "p' \<lesssim>\<^sub>C p @ [[X]\<^sub>R] \<and> \<rho> = intersect_refusal_trace Y p'"
        using prefix_subset_of_intersect_refusal_trace by blast
      then have p'_in_P: "p' \<in> P"
        using CT1_P CT1_def in_P by blast
      then have cttWF_p': "cttWF p'"
        using P_wf by blast
      have p'_cases: "(\<exists>p'' Z. p' = p'' @ [[Z]\<^sub>R]) \<or> ((\<nexists>p''. p' = p'' @ [[Tick]\<^sub>E]) \<and> (\<nexists>p'' Z. p' = p'' @ [[Z]\<^sub>R]))"
        using p'_assms cttWF_p_ref cttWF_end_refusal_prefix_subset by fastforce
      then show "\<rho> \<in> P \<triangle>\<^sub>U Q"
        unfolding UntimedInterruptCTT_def
      proof auto
        fix p'' Z
        show "p' = p'' @ [[Z]\<^sub>R] \<Longrightarrow>
          \<exists>p X. p @ [[X]\<^sub>R] \<in> P \<and> (\<exists>Y q. ([Y]\<^sub>R # q \<in> Q \<or> (\<forall>Z q'. [Z]\<^sub>R # q' \<notin> Q) \<and> Y = UNIV \<and> q = []) \<and>
            \<rho> = intersect_refusal_trace Y (p @ [[X]\<^sub>R]) @ q)"
          using p'_in_P Y_in_Q p'_assms
          by (rule_tac x="p''" in exI, rule_tac x="Z" in exI, auto)
      next
        assume case_assm: "\<forall>p''. p' \<noteq> p'' @ [[Tick]\<^sub>E]" "\<forall>p'' Z. p' \<noteq> p'' @ [[Z]\<^sub>R]"
        show "\<forall>p. p \<in> P \<longrightarrow> (\<exists>p'. p = p' @ [[Tick]\<^sub>E]) \<or> (\<exists>p' Y. p = p' @ [[Y]\<^sub>R]) \<or>
          (\<forall>q. q \<in> Q \<longrightarrow> (\<forall>X. [[X]\<^sub>R] \<notin> Q \<and> ((\<exists>Y. [[Y]\<^sub>R] \<in> Q) \<or> X \<noteq> UNIV) \<or>
            (\<exists>q' Y. q = [Y]\<^sub>R # q') \<or> \<rho> \<noteq> intersect_refusal_trace X p @ q)) \<Longrightarrow>
          \<exists>p X. p @ [[X]\<^sub>R] \<in> P \<and> (\<exists>Y q. ([Y]\<^sub>R # q \<in> Q \<or> (\<forall>Z q'. [Z]\<^sub>R # q' \<notin> Q) \<and> Y = UNIV \<and> q = []) \<and>
                 \<rho> = intersect_refusal_trace Y (p @ [[X]\<^sub>R]) @ q) "
          using p'_in_P Y_in_Q p'_assms case_assm
          apply (erule_tac x="p'" in allE, auto)
          using CT0_CT1_empty CT0_Q CT1_Q by blast
      qed
    next
      fix q' p' X'
      assume case_assms: "intersect_refusal_trace Y (p' @ [[X']\<^sub>R]) \<subseteq>\<^sub>C intersect_refusal_trace Y (p @ [[X]\<^sub>R])" "q' \<lesssim>\<^sub>C q" "p' @ [[X']\<^sub>R] \<subseteq>\<^sub>C p @ [[X]\<^sub>R]"
      then have "p' @ [[X']\<^sub>R] \<in> P"
        using CT1_P CT1_def ctt_subset_imp_prefix_subset in_P by blast
      then show "intersect_refusal_trace Y (p' @ [[X']\<^sub>R]) @ q' \<in> P \<triangle>\<^sub>U Q"
        unfolding UntimedInterruptCTT_def using case_assms in_Q
        apply (auto, rule_tac x="p'" in exI, rule_tac x="X'" in exI, auto)
        apply (rule_tac x="Y" in exI, rule_tac x="q'" in exI, auto)
        apply (metis CT1_Q CT1_def append.left_neutral append_Cons ctt_prefix_subset_same_front)+
        done
    qed
  next
    fix p X
    assume in_P: "p @ [[X]\<^sub>R] \<in> P"
    assume in_Q: "\<forall>Z q'. [Z]\<^sub>R # q' \<notin> Q"
    assume "\<rho> \<lesssim>\<^sub>C intersect_refusal_trace UNIV (p @ [[X]\<^sub>R])"
    then obtain p' where p'_assms: "p' \<lesssim>\<^sub>C p @ [[X]\<^sub>R] \<and> \<rho> = intersect_refusal_trace UNIV p'"
      using prefix_subset_of_intersect_refusal_trace by blast
    have cttWF_p_ref: "cttWF (p @ [[X]\<^sub>R])"
        by (simp add: P_wf in_P)
    then have p'_in_P: "p' \<in> P"
      using CT1_P CT1_def in_P p'_assms by blast
    then have cttWF_p': "cttWF p'"
      using P_wf by blast
    have p'_cases: "(\<exists>p'' Z. p' = p'' @ [[Z]\<^sub>R]) \<or> ((\<nexists>p''. p' = p'' @ [[Tick]\<^sub>E]) \<and> (\<nexists>p'' Z. p' = p'' @ [[Z]\<^sub>R]))"
      using p'_assms cttWF_p_ref cttWF_end_refusal_prefix_subset by fastforce
    then show "\<rho> \<in> P \<triangle>\<^sub>U Q"
      unfolding UntimedInterruptCTT_def
    proof auto
      fix p'' Z
      show "p' = p'' @ [[Z]\<^sub>R] \<Longrightarrow>
        \<exists>p X. p @ [[X]\<^sub>R] \<in> P \<and> (\<exists>Y q. ([Y]\<^sub>R # q \<in> Q \<or> (\<forall>Z q'. [Z]\<^sub>R # q' \<notin> Q) \<and> Y = UNIV \<and> q = []) \<and>
          \<rho> = intersect_refusal_trace Y (p @ [[X]\<^sub>R]) @ q)"
        using p'_in_P in_Q p'_assms by (rule_tac x="p''" in exI, rule_tac x="Z" in exI, auto)
    next
      assume case_assm: "\<forall>p''. p' \<noteq> p'' @ [[Tick]\<^sub>E]" "\<forall>p'' Z. p' \<noteq> p'' @ [[Z]\<^sub>R]"
      show "\<forall>p. p \<in> P \<longrightarrow> (\<exists>p'. p = p' @ [[Tick]\<^sub>E]) \<or> (\<exists>p' Y. p = p' @ [[Y]\<^sub>R]) \<or>
        (\<forall>q. q \<in> Q \<longrightarrow> (\<forall>X. [[X]\<^sub>R] \<notin> Q \<and> ((\<exists>Y. [[Y]\<^sub>R] \<in> Q) \<or> X \<noteq> UNIV) \<or>
          (\<exists>q' Y. q = [Y]\<^sub>R # q') \<or> \<rho> \<noteq> intersect_refusal_trace X p @ q)) \<Longrightarrow>
        \<exists>p X. p @ [[X]\<^sub>R] \<in> P \<and> (\<exists>Y q. ([Y]\<^sub>R # q \<in> Q \<or> (\<forall>Z q'. [Z]\<^sub>R # q' \<notin> Q) \<and> Y = UNIV \<and> q = []) \<and>
          \<rho> = intersect_refusal_trace Y (p @ [[X]\<^sub>R]) @ q)"
        using p'_in_P in_Q p'_assms case_assm CT0_CT1_empty CT0_Q CT1_Q by (erule_tac x="p'" in allE, auto)
    qed
  next
    fix p q :: "'a cttobs list"
    fix X
    assume case_assms: "\<forall>p'. p \<noteq> p' @ [[Tick]\<^sub>E]" "\<forall>p' Y. p \<noteq> p' @ [[Y]\<^sub>R]"
    assume ref_in_Q: "[[X]\<^sub>R] \<in> Q"
    assume q_in_Q: "q \<in> Q"
    assume q_nonref: "\<forall>q' Y. q \<noteq> [Y]\<^sub>R # q'"
    assume p_in_P: "p \<in> P"
    then have cttWF_p: "cttWF p"
      using P_wf by blast
    assume "\<rho> \<lesssim>\<^sub>C intersect_refusal_trace X p @ q"
    then have "\<rho> \<lesssim>\<^sub>C intersect_refusal_trace X p \<or>
      (\<exists>t' s'. intersect_refusal_trace UNIV s' \<subseteq>\<^sub>C intersect_refusal_trace X p \<and>
         t' \<lesssim>\<^sub>C q \<and> \<rho> = intersect_refusal_trace X s' @ t')"
      using ctt_prefix_subset_intersect_refusal_trace_concat by fastforce
    then show "\<rho> \<in> P \<triangle>\<^sub>U Q"
    proof auto
      assume "\<rho> \<lesssim>\<^sub>C intersect_refusal_trace X p"
      then obtain p' where p'_assms: "p' \<lesssim>\<^sub>C p" "\<rho> = intersect_refusal_trace X p'"
        using prefix_subset_of_intersect_refusal_trace by fastforce
      then have p'_in_P: "p' \<in> P"
        using CT1_P CT1_def p_in_P by blast
      have "(\<exists> s e. p = s @ [[Event e]\<^sub>E]) \<or> (\<exists> s. p = s @ [[Tock]\<^sub>E]) \<or> p = []"
        using case_assms by (auto, metis cttevent.exhaust cttobs.exhaust rev_exhaust)
      then have "(\<exists> p'' Y. p' = p'' @ [[Y]\<^sub>R]) \<or> ((\<nexists>p''. p' = p'' @ [[Tick]\<^sub>E]) \<and> (\<nexists>p'' Y. p' = p'' @ [[Y]\<^sub>R]))"
        using cttWF_p p'_assms(1) apply auto
        using cttWF_end_Event_prefix_subset apply fastforce
        using cttWF_end_Tock_prefix_subset apply fastforce
        using ctt_prefix_subset.elims(2) by auto
      then show "\<rho> \<in> P \<triangle>\<^sub>U Q"
        unfolding UntimedInterruptCTT_def
      proof auto
        fix p'' Y
        show "p' = p'' @ [[Y]\<^sub>R] \<Longrightarrow>
            \<exists>p X. p @ [[X]\<^sub>R] \<in> P \<and>
                  (\<exists>Y q. ([Y]\<^sub>R # q \<in> Q \<or> (\<forall>Z q'. [Z]\<^sub>R # q' \<notin> Q) \<and> Y = UNIV \<and> q = []) \<and>
                         \<rho> = intersect_refusal_trace Y (p @ [[X]\<^sub>R]) @ q)"
          using ref_in_Q p'_in_P p'_assms by (rule_tac x="p''" in exI, rule_tac x="Y" in exI, auto)
      next
        assume case_assms: "\<forall>p''. p' \<noteq> p'' @ [[Tick]\<^sub>E]" "\<forall>p'' Y. p' \<noteq> p'' @ [[Y]\<^sub>R]"
        show "\<forall>p. p \<in> P \<longrightarrow> (\<exists>p'. p = p' @ [[Tick]\<^sub>E]) \<or> (\<exists>p' Y. p = p' @ [[Y]\<^sub>R]) \<or>
          (\<forall>q. q \<in> Q \<longrightarrow> (\<forall>X. [[X]\<^sub>R] \<notin> Q \<and> ((\<exists>Y. [[Y]\<^sub>R] \<in> Q) \<or> X \<noteq> UNIV) \<or>
            (\<exists>q' Y. q = [Y]\<^sub>R # q') \<or> \<rho> \<noteq> intersect_refusal_trace X p @ q)) \<Longrightarrow>
          \<exists>p X. p @ [[X]\<^sub>R] \<in> P \<and> (\<exists>Y q. ([Y]\<^sub>R # q \<in> Q \<or> (\<forall>Z q'. [Z]\<^sub>R # q' \<notin> Q) \<and> Y = UNIV \<and> q = []) \<and>
                 \<rho> = intersect_refusal_trace Y (p @ [[X]\<^sub>R]) @ q)"
          using ref_in_Q p'_in_P p'_assms CT0_CT1_empty CT0_Q CT1_Q
          by (erule_tac x="p'" in allE, auto simp add: case_assms, erule_tac x="[]" in allE, auto, blast)
      qed
    next
      fix t' s'
      assume "t' \<lesssim>\<^sub>C q"
      then have t'_assms: "t' \<in> Q \<and> (\<nexists>q' Y. t' = [Y]\<^sub>R # q')"
        apply auto
        using CT1_Q CT1_def q_in_Q apply blast
        using ctt_prefix_subset.elims(2) q_nonref by blast
      assume "intersect_refusal_trace UNIV s' \<subseteq>\<^sub>C intersect_refusal_trace X p"
      then have s'_ctt_subset: "s' \<subseteq>\<^sub>C p"
        using intersect_refusal_trace_UNIV_subset_imp_subset by blast
      then have s'_assms: "(\<nexists>p'. s' = p' @ [[Tick]\<^sub>E]) \<and> (\<nexists>p' Y. s' = p' @ [[Y]\<^sub>R])"
        using case_assms apply -
      proof (induct s' p rule:ctt_subset.induct,auto)
        fix X xa Y ya p'
        assume "\<forall>p'. [Y]\<^sub>R # ya \<noteq> p' @ [[Tick]\<^sub>E]"
        then have 1: "\<forall>p'. ya \<noteq> p' @ [[Tick]\<^sub>E]"
          by auto
        assume "\<forall>p' Ya. [Y]\<^sub>R # ya \<noteq> p' @ [[Ya]\<^sub>R]"
        then have 2: "\<forall>p' Y. ya \<noteq> p' @ [[Y]\<^sub>R]"
          by auto
        show "(\<forall>p'. ya \<noteq> p' @ [[Tick]\<^sub>E] \<Longrightarrow>
          \<forall>p' Y. ya \<noteq> p' @ [[Y]\<^sub>R] \<Longrightarrow> (\<forall>p'. xa \<noteq> p' @ [[Tick]\<^sub>E]) \<and> (\<forall>p' Y. xa \<noteq> p' @ [[Y]\<^sub>R])) \<Longrightarrow>
          X \<subseteq> Y \<Longrightarrow> xa \<subseteq>\<^sub>C ya \<Longrightarrow> [X]\<^sub>R # xa = p' @ [[Tick]\<^sub>E] \<Longrightarrow> False"
          using 1 2 by (auto, metis append_eq_Cons_conv cttobs.distinct(1) list.inject)
      next
        fix X xa Y ya p' Ya
        assume "\<forall>p'. [Y]\<^sub>R # ya \<noteq> p' @ [[Tick]\<^sub>E]"
        then have 1: "\<forall>p'. ya \<noteq> p' @ [[Tick]\<^sub>E]"
          by auto
        assume 2: "\<forall>p' Ya. [Y]\<^sub>R # ya \<noteq> p' @ [[Ya]\<^sub>R]"
        then have 3: "\<forall>p' Ya. ya \<noteq> p' @ [[Ya]\<^sub>R]"
          by auto
        show "(\<forall>p'. ya \<noteq> p' @ [[Tick]\<^sub>E] \<Longrightarrow>
          \<forall>p' Y. ya \<noteq> p' @ [[Y]\<^sub>R] \<Longrightarrow> (\<forall>p'. xa \<noteq> p' @ [[Tick]\<^sub>E]) \<and> (\<forall>p' Y. xa \<noteq> p' @ [[Y]\<^sub>R])) \<Longrightarrow>
          X \<subseteq> Y \<Longrightarrow> xa \<subseteq>\<^sub>C ya \<Longrightarrow> [X]\<^sub>R # xa = p' @ [[Ya]\<^sub>R] \<Longrightarrow> False"
          using 1 2 3 by (auto, metis (no_types, lifting) append_eq_Cons_conv ctt_subset_same_length length_0_conv list.inject)
      next
        fix xa y ya p'
        assume 1: "\<forall>p'. [y]\<^sub>E # ya \<noteq> p' @ [[Tick]\<^sub>E]"
        then have 2: "\<forall>p'. ya \<noteq> p' @ [[Tick]\<^sub>E]"
          by auto
        assume 3: "\<forall>p' Y. [y]\<^sub>E # ya \<noteq> p' @ [[Y]\<^sub>R]"
        then have 4: "\<forall>p' Ya. ya \<noteq> p' @ [[Ya]\<^sub>R]"
          by auto
        show "(\<forall>p'. ya \<noteq> p' @ [[Tick]\<^sub>E] \<Longrightarrow>
          \<forall>p' Y. ya \<noteq> p' @ [[Y]\<^sub>R] \<Longrightarrow> (\<forall>p'. xa \<noteq> p' @ [[Tick]\<^sub>E]) \<and> (\<forall>p' Y. xa \<noteq> p' @ [[Y]\<^sub>R])) \<Longrightarrow>
          xa \<subseteq>\<^sub>C ya \<Longrightarrow> [y]\<^sub>E # xa = p' @ [[Tick]\<^sub>E] \<Longrightarrow> False"
          using 1 2 3 4 by (metis append_eq_Cons_conv ctt_subset_same_length length_0_conv list.inject)
      next
        fix xa y ya p' Y
        assume 1: "\<forall>p'. [y]\<^sub>E # ya \<noteq> p' @ [[Tick]\<^sub>E]"
        then have 2: "\<forall>p'. ya \<noteq> p' @ [[Tick]\<^sub>E]"
          by auto
        assume 3: "\<forall>p' Y. [y]\<^sub>E # ya \<noteq> p' @ [[Y]\<^sub>R]"
        then have 4: "\<forall>p' Ya. ya \<noteq> p' @ [[Ya]\<^sub>R]"
          by auto
        show "(\<forall>p'. ya \<noteq> p' @ [[Tick]\<^sub>E] \<Longrightarrow>
          \<forall>p' Y. ya \<noteq> p' @ [[Y]\<^sub>R] \<Longrightarrow> (\<forall>p'. xa \<noteq> p' @ [[Tick]\<^sub>E]) \<and> (\<forall>p' Y. xa \<noteq> p' @ [[Y]\<^sub>R])) \<Longrightarrow>
          xa \<subseteq>\<^sub>C ya \<Longrightarrow> [y]\<^sub>E # xa = p' @ [[Y]\<^sub>R] \<Longrightarrow> False"
          using 1 2 3 4 by (metis append_eq_Cons_conv ctt_subset_same_length length_0_conv list.inject)
      qed
      have s'_in_P: "s' \<in> P"
        using s'_ctt_subset CT1_P CT1_def ctt_subset_imp_prefix_subset p_in_P by blast 
      show  "\<rho> = intersect_refusal_trace X s' @ t' \<Longrightarrow> intersect_refusal_trace X s' @ t' \<in> P \<triangle>\<^sub>U Q"
        unfolding UntimedInterruptCTT_def
      proof auto
        show "\<rho> = intersect_refusal_trace X s' @ t' \<Longrightarrow>
          \<forall>p. p \<in> P \<longrightarrow> (\<exists>p'. p = p' @ [[Tick]\<^sub>E]) \<or> (\<exists>p' Y. p = p' @ [[Y]\<^sub>R]) \<or>
            (\<forall>q. q \<in> Q \<longrightarrow> (\<forall>Xa. [[Xa]\<^sub>R] \<notin> Q \<and> ((\<exists>Y. [[Y]\<^sub>R] \<in> Q) \<or> Xa \<noteq> UNIV) \<or>
            (\<exists>q' Y. q = [Y]\<^sub>R # q') \<or> intersect_refusal_trace X s' @ t' \<noteq> intersect_refusal_trace Xa p @ q)) \<Longrightarrow>
          \<exists>p Xa. p @ [[Xa]\<^sub>R] \<in> P \<and> (\<exists>Y q. ([Y]\<^sub>R # q \<in> Q \<or> (\<forall>Z q'. [Z]\<^sub>R # q' \<notin> Q) \<and> Y = UNIV \<and> q = []) \<and>
            intersect_refusal_trace X s' @ t' = intersect_refusal_trace Y (p @ [[Xa]\<^sub>R]) @ q)"
          using s'_assms t'_assms ref_in_Q s'_in_P
          by (erule_tac x="s'" in allE, auto, erule_tac x="t'" in allE, auto)
      qed
    qed
  next
    fix p q :: "'a cttobs list"
    assume case_assms: "\<forall>p'. p \<noteq> p' @ [[Tick]\<^sub>E]" "\<forall>p' Y. p \<noteq> p' @ [[Y]\<^sub>R]"
    assume Q_assm: "\<forall>Y. [[Y]\<^sub>R] \<notin> Q"
    assume q_in_Q: "q \<in> Q"
    assume q_nonref: "\<forall>q' Y. q \<noteq> [Y]\<^sub>R # q'"
    assume p_in_P: "p \<in> P"
    then have cttWF_p: "cttWF p"
      using P_wf by blast
    assume "\<rho> \<lesssim>\<^sub>C intersect_refusal_trace UNIV p @ q"
    then have "\<rho> \<lesssim>\<^sub>C intersect_refusal_trace UNIV p \<or>
      (\<exists>t' s'. intersect_refusal_trace UNIV s' \<subseteq>\<^sub>C intersect_refusal_trace UNIV p \<and>
         t' \<lesssim>\<^sub>C q \<and> \<rho> = intersect_refusal_trace UNIV s' @ t')"
      using ctt_prefix_subset_intersect_refusal_trace_concat by fastforce
    then show "\<rho> \<in> P \<triangle>\<^sub>U Q"
    proof auto
      assume "\<rho> \<lesssim>\<^sub>C intersect_refusal_trace UNIV p"
      then obtain p' where p'_assms: "p' \<lesssim>\<^sub>C p" "\<rho> = intersect_refusal_trace UNIV p'"
        using prefix_subset_of_intersect_refusal_trace by fastforce
      then have p'_in_P: "p' \<in> P"
        using CT1_P CT1_def p_in_P by blast
      have "(\<exists> s e. p = s @ [[Event e]\<^sub>E]) \<or> (\<exists> s. p = s @ [[Tock]\<^sub>E]) \<or> p = []"
        using case_assms by (auto, metis cttevent.exhaust cttobs.exhaust rev_exhaust)
      then have "(\<exists> p'' Y. p' = p'' @ [[Y]\<^sub>R]) \<or> ((\<nexists>p''. p' = p'' @ [[Tick]\<^sub>E]) \<and> (\<nexists>p'' Y. p' = p'' @ [[Y]\<^sub>R]))"
        using cttWF_p p'_assms(1) apply auto
        using cttWF_end_Event_prefix_subset apply fastforce
        using cttWF_end_Tock_prefix_subset apply fastforce
        using ctt_prefix_subset.elims(2) by auto
      then show "\<rho> \<in> P \<triangle>\<^sub>U Q"
        unfolding UntimedInterruptCTT_def
      proof auto
        fix p'' Y
        show "p' = p'' @ [[Y]\<^sub>R] \<Longrightarrow>
            \<exists>p X. p @ [[X]\<^sub>R] \<in> P \<and>
                  (\<exists>Y q. ([Y]\<^sub>R # q \<in> Q \<or> (\<forall>Z q'. [Z]\<^sub>R # q' \<notin> Q) \<and> Y = UNIV \<and> q = []) \<and>
                         \<rho> = intersect_refusal_trace Y (p @ [[X]\<^sub>R]) @ q)"
          using Q_assm p'_in_P p'_assms 
          apply (rule_tac x="p''" in exI, rule_tac x="Y" in exI, auto)
          apply (rule_tac x="UNIV" in exI, rule_tac x="[]" in exI, auto)
          apply (meson CT1_Q CT1_def ctt_prefix_subset.simps(1) ctt_prefix_subset.simps(2) ctt_prefix_subset_refl)
          done
      next
        assume case_assms: "\<forall>p''. p' \<noteq> p'' @ [[Tick]\<^sub>E]" "\<forall>p'' Y. p' \<noteq> p'' @ [[Y]\<^sub>R]"
        show "\<forall>p. p \<in> P \<longrightarrow> (\<exists>p'. p = p' @ [[Tick]\<^sub>E]) \<or> (\<exists>p' Y. p = p' @ [[Y]\<^sub>R]) \<or>
          (\<forall>q. q \<in> Q \<longrightarrow> (\<forall>X. [[X]\<^sub>R] \<notin> Q \<and> ((\<exists>Y. [[Y]\<^sub>R] \<in> Q) \<or> X \<noteq> UNIV) \<or>
            (\<exists>q' Y. q = [Y]\<^sub>R # q') \<or> \<rho> \<noteq> intersect_refusal_trace X p @ q)) \<Longrightarrow>
          \<exists>p X. p @ [[X]\<^sub>R] \<in> P \<and> (\<exists>Y q. ([Y]\<^sub>R # q \<in> Q \<or> (\<forall>Z q'. [Z]\<^sub>R # q' \<notin> Q) \<and> Y = UNIV \<and> q = []) \<and>
                 \<rho> = intersect_refusal_trace Y (p @ [[X]\<^sub>R]) @ q)"
          using Q_assm p'_in_P p'_assms CT0_CT1_empty CT0_Q CT1_Q
          by (erule_tac x="p'" in allE, auto simp add: case_assms, erule_tac x="[]" in allE, auto, blast)
      qed
    next
      fix t' s'
      assume "t' \<lesssim>\<^sub>C q"
      then have t'_assms: "t' \<in> Q \<and> (\<nexists>q' Y. t' = [Y]\<^sub>R # q')"
        apply auto
        using CT1_Q CT1_def q_in_Q apply blast
        using ctt_prefix_subset.elims(2) q_nonref by blast
      assume "intersect_refusal_trace UNIV s' \<subseteq>\<^sub>C intersect_refusal_trace UNIV p"
      then have s'_ctt_subset: "s' \<subseteq>\<^sub>C p"
        using intersect_refusal_trace_UNIV_subset_imp_subset by blast
      then have s'_assms: "(\<nexists>p'. s' = p' @ [[Tick]\<^sub>E]) \<and> (\<nexists>p' Y. s' = p' @ [[Y]\<^sub>R])"
        using case_assms apply -
      proof (induct s' p rule:ctt_subset.induct,auto)
        fix X xa Y ya p'
        assume "\<forall>p'. [Y]\<^sub>R # ya \<noteq> p' @ [[Tick]\<^sub>E]"
        then have 1: "\<forall>p'. ya \<noteq> p' @ [[Tick]\<^sub>E]"
          by auto
        assume "\<forall>p' Ya. [Y]\<^sub>R # ya \<noteq> p' @ [[Ya]\<^sub>R]"
        then have 2: "\<forall>p' Y. ya \<noteq> p' @ [[Y]\<^sub>R]"
          by auto
        show "(\<forall>p'. ya \<noteq> p' @ [[Tick]\<^sub>E] \<Longrightarrow>
          \<forall>p' Y. ya \<noteq> p' @ [[Y]\<^sub>R] \<Longrightarrow> (\<forall>p'. xa \<noteq> p' @ [[Tick]\<^sub>E]) \<and> (\<forall>p' Y. xa \<noteq> p' @ [[Y]\<^sub>R])) \<Longrightarrow>
          X \<subseteq> Y \<Longrightarrow> xa \<subseteq>\<^sub>C ya \<Longrightarrow> [X]\<^sub>R # xa = p' @ [[Tick]\<^sub>E] \<Longrightarrow> False"
          using 1 2 by (auto, metis append_eq_Cons_conv cttobs.distinct(1) list.inject)
      next
        fix X xa Y ya p' Ya
        assume "\<forall>p'. [Y]\<^sub>R # ya \<noteq> p' @ [[Tick]\<^sub>E]"
        then have 1: "\<forall>p'. ya \<noteq> p' @ [[Tick]\<^sub>E]"
          by auto
        assume 2: "\<forall>p' Ya. [Y]\<^sub>R # ya \<noteq> p' @ [[Ya]\<^sub>R]"
        then have 3: "\<forall>p' Ya. ya \<noteq> p' @ [[Ya]\<^sub>R]"
          by auto
        show "(\<forall>p'. ya \<noteq> p' @ [[Tick]\<^sub>E] \<Longrightarrow>
          \<forall>p' Y. ya \<noteq> p' @ [[Y]\<^sub>R] \<Longrightarrow> (\<forall>p'. xa \<noteq> p' @ [[Tick]\<^sub>E]) \<and> (\<forall>p' Y. xa \<noteq> p' @ [[Y]\<^sub>R])) \<Longrightarrow>
          X \<subseteq> Y \<Longrightarrow> xa \<subseteq>\<^sub>C ya \<Longrightarrow> [X]\<^sub>R # xa = p' @ [[Ya]\<^sub>R] \<Longrightarrow> False"
          using 1 2 3 by (auto, metis (no_types, lifting) append_eq_Cons_conv ctt_subset_same_length length_0_conv list.inject)
      next
        fix xa y ya p'
        assume 1: "\<forall>p'. [y]\<^sub>E # ya \<noteq> p' @ [[Tick]\<^sub>E]"
        then have 2: "\<forall>p'. ya \<noteq> p' @ [[Tick]\<^sub>E]"
          by auto
        assume 3: "\<forall>p' Y. [y]\<^sub>E # ya \<noteq> p' @ [[Y]\<^sub>R]"
        then have 4: "\<forall>p' Ya. ya \<noteq> p' @ [[Ya]\<^sub>R]"
          by auto
        show "(\<forall>p'. ya \<noteq> p' @ [[Tick]\<^sub>E] \<Longrightarrow>
          \<forall>p' Y. ya \<noteq> p' @ [[Y]\<^sub>R] \<Longrightarrow> (\<forall>p'. xa \<noteq> p' @ [[Tick]\<^sub>E]) \<and> (\<forall>p' Y. xa \<noteq> p' @ [[Y]\<^sub>R])) \<Longrightarrow>
          xa \<subseteq>\<^sub>C ya \<Longrightarrow> [y]\<^sub>E # xa = p' @ [[Tick]\<^sub>E] \<Longrightarrow> False"
          using 1 2 3 4 by (metis append_eq_Cons_conv ctt_subset_same_length length_0_conv list.inject)
      next
        fix xa y ya p' Y
        assume 1: "\<forall>p'. [y]\<^sub>E # ya \<noteq> p' @ [[Tick]\<^sub>E]"
        then have 2: "\<forall>p'. ya \<noteq> p' @ [[Tick]\<^sub>E]"
          by auto
        assume 3: "\<forall>p' Y. [y]\<^sub>E # ya \<noteq> p' @ [[Y]\<^sub>R]"
        then have 4: "\<forall>p' Ya. ya \<noteq> p' @ [[Ya]\<^sub>R]"
          by auto
        show "(\<forall>p'. ya \<noteq> p' @ [[Tick]\<^sub>E] \<Longrightarrow>
          \<forall>p' Y. ya \<noteq> p' @ [[Y]\<^sub>R] \<Longrightarrow> (\<forall>p'. xa \<noteq> p' @ [[Tick]\<^sub>E]) \<and> (\<forall>p' Y. xa \<noteq> p' @ [[Y]\<^sub>R])) \<Longrightarrow>
          xa \<subseteq>\<^sub>C ya \<Longrightarrow> [y]\<^sub>E # xa = p' @ [[Y]\<^sub>R] \<Longrightarrow> False"
          using 1 2 3 4 by (metis append_eq_Cons_conv ctt_subset_same_length length_0_conv list.inject)
      qed
      have s'_in_P: "s' \<in> P"
        using s'_ctt_subset CT1_P CT1_def ctt_subset_imp_prefix_subset p_in_P by blast 
      show  "\<rho> = intersect_refusal_trace UNIV s' @ t' \<Longrightarrow> intersect_refusal_trace UNIV s' @ t' \<in> P \<triangle>\<^sub>U Q"
        unfolding UntimedInterruptCTT_def
        (*using s'_assms t'_assms ref_in_Q s'_in_P*)
      proof auto
        show "\<rho> = intersect_refusal_trace UNIV s' @ t' \<Longrightarrow>
          \<forall>p. p \<in> P \<longrightarrow> (\<exists>p'. p = p' @ [[Tick]\<^sub>E]) \<or> (\<exists>p' Y. p = p' @ [[Y]\<^sub>R]) \<or>
            (\<forall>q. q \<in> Q \<longrightarrow> (\<forall>Xa. [[Xa]\<^sub>R] \<notin> Q \<and> ((\<exists>Y. [[Y]\<^sub>R] \<in> Q) \<or> Xa \<noteq> UNIV) \<or>
            (\<exists>q' Y. q = [Y]\<^sub>R # q') \<or> intersect_refusal_trace UNIV s' @ t' \<noteq> intersect_refusal_trace Xa p @ q)) \<Longrightarrow>
          \<exists>p Xa. p @ [[Xa]\<^sub>R] \<in> P \<and> (\<exists>Y q. ([Y]\<^sub>R # q \<in> Q \<or> (\<forall>Z q'. [Z]\<^sub>R # q' \<notin> Q) \<and> Y = UNIV \<and> q = []) \<and>
            intersect_refusal_trace UNIV s' @ t' = intersect_refusal_trace Y (p @ [[Xa]\<^sub>R]) @ q)"
          using s'_assms t'_assms Q_assm s'_in_P by (erule_tac x="s'" in allE, auto)
      qed
    qed
  qed
qed

lemma CT2_UntimedInterrupt:
  assumes P_wf: "\<forall> x\<in>P. cttWF x"
  assumes CT0_Q: "CT0 Q"
  assumes CT1_P: "CT1 P" and CT1_Q: "CT1 Q"
  assumes CT2_P: "CT2 P" and CT2_Q: "CT2 Q"
  shows "CT2 (P \<triangle>\<^sub>U Q)"
  unfolding CT2_def
proof (auto)
  fix \<rho> X Y
  assume assm1: "\<rho> @ [[X]\<^sub>R] \<in> P \<triangle>\<^sub>U Q"
  then have \<rho>_cases: "(\<forall>Z q'. \<rho> @ [[X]\<^sub>R] \<in> P \<and> [Z]\<^sub>R # q' \<notin> Q)
    \<or> (\<exists>p Z Y. p @ [[Z]\<^sub>R] \<in> P \<and> [[Y]\<^sub>R] \<in> Q \<and> \<rho> @ [[X]\<^sub>R] = intersect_refusal_trace Y (p @ [[Z]\<^sub>R]))
    \<or> (\<exists>p Z Y q. p @ [[Z]\<^sub>R] \<in> P \<and> [Y]\<^sub>R # q @ [[X]\<^sub>R] \<in> Q \<and> \<rho> = intersect_refusal_trace Y (p @ [[Z]\<^sub>R]) @ q)
    \<or> (\<exists>p q Z. p \<in> P \<and> (\<nexists>p'. p = p' @ [[Tick]\<^sub>E]) \<and> (\<nexists>p' Y. p = p' @ [[Y]\<^sub>R])
      \<and> [[Z]\<^sub>R] \<in> Q \<and> q @ [[X]\<^sub>R] \<in> Q \<and> q \<noteq> [] \<and> (\<nexists>q' Y. q = [Y]\<^sub>R # q') \<and> \<rho> = intersect_refusal_trace Z p @ q)
    \<or> (\<exists>p q. p \<in> P \<and> (\<nexists>p'. p = p' @ [[Tick]\<^sub>E]) \<and> (\<nexists>p' Y. p = p' @ [[Y]\<^sub>R])
      \<and> (\<forall>Y. [[Y]\<^sub>R] \<notin> Q) \<and> q @ [[X]\<^sub>R] \<in> Q \<and> (\<nexists>q' Y. q = [Y]\<^sub>R # q') \<and> \<rho> = p @ q)"
    unfolding UntimedInterruptCTT_def
  proof (safe, simp_all)
    fix p Xa
    assume "\<rho> @ [[X]\<^sub>R] = intersect_refusal_trace Xa (p @ [[Tick]\<^sub>E])"
    then have "\<rho> @ [[X]\<^sub>R] \<subseteq>\<^sub>C p @ [[Tick]\<^sub>E]"
      by (simp add: intersect_refusal_trace_subset)
    then have "False"
      using ctt_subset_same_length by (induct \<rho> p rule:ctt_subset.induct, auto, fastforce+)
    then show "intersect_refusal_trace Xa (p @ [[Tick]\<^sub>E]) \<in> P"
      by auto
  next
    fix p Xa
    assume "\<rho> @ [[X]\<^sub>R] = intersect_refusal_trace Xa (p @ [[Tick]\<^sub>E])"
    then have "\<rho> @ [[X]\<^sub>R] \<subseteq>\<^sub>C p @ [[Tick]\<^sub>E]"
      by (simp add: intersect_refusal_trace_subset)
    then have "False"
      using ctt_subset_same_length by (induct \<rho> p rule:ctt_subset.induct, auto, fastforce+)
    then show "intersect_refusal_trace Xa (p @ [[Tick]\<^sub>E]) \<in> P"
      by auto
  next
    fix p Xa
    assume "\<rho> @ [[X]\<^sub>R] = intersect_refusal_trace Xa (p @ [[Tick]\<^sub>E])"
    then have "\<rho> @ [[X]\<^sub>R] \<subseteq>\<^sub>C p @ [[Tick]\<^sub>E]"
      by (simp add: intersect_refusal_trace_subset)
    then show "False"
      using ctt_subset_same_length by (induct \<rho> p rule:ctt_subset.induct, auto, fastforce+)
  next
    fix p Xa
    assume "\<rho> @ [[X]\<^sub>R] = intersect_refusal_trace Xa (p @ [[Tick]\<^sub>E])"
    then have "\<rho> @ [[X]\<^sub>R] \<subseteq>\<^sub>C p @ [[Tick]\<^sub>E]"
      by (simp add: intersect_refusal_trace_subset)
    then show "False"
      using ctt_subset_same_length by (induct \<rho> p rule:ctt_subset.induct, auto, fastforce+)
  next
    fix p Xa Y q
    assume case_assms: "\<rho> @ [[X]\<^sub>R] = intersect_refusal_trace Y (p @ [[Xa]\<^sub>R]) @ q" "p @ [[Xa]\<^sub>R] \<in> P" "[Y]\<^sub>R # q \<in> Q"
    then have "(\<exists> q'. q = q' @ [[X]\<^sub>R]) \<or> q = []"
      by (metis append_butlast_last_id last_appendR last_snoc)
    then show "\<forall>pa Z. pa @ [[Z]\<^sub>R] \<in> P \<longrightarrow>
              (\<forall>Ya. [[Ya]\<^sub>R] \<in> Q \<longrightarrow> intersect_refusal_trace Y (p @ [[Xa]\<^sub>R]) @ q \<noteq> intersect_refusal_trace Ya (pa @ [[Z]\<^sub>R])) \<Longrightarrow>
      \<forall>p Z. p @ [[Z]\<^sub>R] \<in> P \<longrightarrow> (\<forall>Y q. [Y]\<^sub>R # q @ [[X]\<^sub>R] \<in> Q \<longrightarrow> \<rho> \<noteq> intersect_refusal_trace Y (p @ [[Z]\<^sub>R]) @ q) \<Longrightarrow>
      intersect_refusal_trace Y (p @ [[Xa]\<^sub>R]) @ q \<in> P"
    proof auto
      fix q'
      show "\<forall>p Z. p @ [[Z]\<^sub>R] \<in> P \<longrightarrow> (\<forall>Y q. [Y]\<^sub>R # q @ [[X]\<^sub>R] \<in> Q \<longrightarrow> \<rho> \<noteq> intersect_refusal_trace Y (p @ [[Z]\<^sub>R]) @ q) \<Longrightarrow>
          q = q' @ [[X]\<^sub>R] \<Longrightarrow> intersect_refusal_trace Y (p @ [[Xa]\<^sub>R]) @ q' @ [[X]\<^sub>R] \<in> P"
        using case_assms by (erule_tac x="p" in allE, erule_tac x="Xa" in allE, auto)
    next
      show "\<forall>pa Z. pa @ [[Z]\<^sub>R] \<in> P \<longrightarrow>
           (\<forall>Yaa. [[Yaa]\<^sub>R] \<in> Q \<longrightarrow> intersect_refusal_trace Y (p @ [[Xa]\<^sub>R]) \<noteq> intersect_refusal_trace Yaa (pa @ [[Z]\<^sub>R])) \<Longrightarrow>
        q = [] \<Longrightarrow> intersect_refusal_trace Y (p @ [[Xa]\<^sub>R]) \<in> P"
        using case_assms by (erule_tac x="p" in allE, erule_tac x="Xa" in allE, auto)
    qed
  next
    fix Z q' p Xa Y q
    assume case_assms: "p @ [[Xa]\<^sub>R] \<in> P" "\<rho> @ [[X]\<^sub>R] = intersect_refusal_trace Y (p @ [[Xa]\<^sub>R]) @ q" "[Y]\<^sub>R # q \<in> Q"
    then have "(\<exists> q'. q = q' @ [[X]\<^sub>R]) \<or> q = []"
      by (metis append_butlast_last_id last_appendR last_snoc)
    then show "\<forall>pa Z. pa @ [[Z]\<^sub>R] \<in> P \<longrightarrow>
              (\<forall>Ya. [[Ya]\<^sub>R] \<in> Q \<longrightarrow> intersect_refusal_trace Y (p @ [[Xa]\<^sub>R]) @ q \<noteq> intersect_refusal_trace Ya (pa @ [[Z]\<^sub>R])) \<Longrightarrow>
      \<forall>p Z. p @ [[Z]\<^sub>R] \<in> P \<longrightarrow> (\<forall>Y q. [Y]\<^sub>R # q @ [[X]\<^sub>R] \<in> Q \<longrightarrow> \<rho> \<noteq> intersect_refusal_trace Y (p @ [[Z]\<^sub>R]) @ q) \<Longrightarrow> False"
    proof auto
      fix q'
      show "\<forall>p Z. p @ [[Z]\<^sub>R] \<in> P \<longrightarrow> (\<forall>Y q. [Y]\<^sub>R # q @ [[X]\<^sub>R] \<in> Q \<longrightarrow> \<rho> \<noteq> intersect_refusal_trace Y (p @ [[Z]\<^sub>R]) @ q) \<Longrightarrow>
          q = q' @ [[X]\<^sub>R] \<Longrightarrow> False"
        using case_assms by (erule_tac x="p" in allE, erule_tac x="Xa" in allE, auto)
    next
      show "\<forall>pa Z. pa @ [[Z]\<^sub>R] \<in> P \<longrightarrow>
           (\<forall>Yaa. [[Yaa]\<^sub>R] \<in> Q \<longrightarrow> intersect_refusal_trace Y (p @ [[Xa]\<^sub>R]) \<noteq> intersect_refusal_trace Yaa (pa @ [[Z]\<^sub>R])) \<Longrightarrow>
        q = [] \<Longrightarrow> False"
        using case_assms by (erule_tac x="p" in allE, erule_tac x="Xa" in allE, auto)
    qed
  next
    fix p Xa Y q
    assume case_assms: "\<rho> @ [[X]\<^sub>R] = intersect_refusal_trace Y (p @ [[Xa]\<^sub>R])" "p @ [[Xa]\<^sub>R] \<in> P" "\<forall>Z q'. [Z]\<^sub>R # q' \<notin> Q"
    then show "intersect_refusal_trace Y (p @ [[Xa]\<^sub>R]) \<in> P"
      using CT1_P CT1_def intersect_refusal_trace_prefix_subset by blast
  next
    fix p q Xa
    assume case_assms: "p \<in> P" "\<forall>p'. p \<noteq> p' @ [[Tick]\<^sub>E]" "\<forall>p' Y. p \<noteq> p' @ [[Y]\<^sub>R]" "q \<in> Q"
      "\<forall>q' Y. q \<noteq> [Y]\<^sub>R # q'" "\<rho> @ [[X]\<^sub>R] = intersect_refusal_trace Xa p @ q" "[[Xa]\<^sub>R] \<in> Q"
    then have "(\<exists> q'. q = q' @ [[X]\<^sub>R]) \<or> q = []"
      by (metis append_butlast_last_id last_appendR last_snoc)
    then show "\<forall>pa Z. pa @ [[Z]\<^sub>R] \<in> P \<longrightarrow>
        (\<forall>Y. [[Y]\<^sub>R] \<in> Q \<longrightarrow> intersect_refusal_trace Xa p @ q \<noteq> intersect_refusal_trace Y (pa @ [[Z]\<^sub>R])) \<Longrightarrow>
      \<forall>p. p \<in> P \<longrightarrow> (\<exists>p'. p = p' @ [[Tick]\<^sub>E]) \<or> (\<exists>p' Y. p = p' @ [[Y]\<^sub>R]) \<or>
        (\<forall>q. q @ [[X]\<^sub>R] \<in> Q \<longrightarrow> (\<forall>Z. [[Z]\<^sub>R] \<in> Q \<longrightarrow> q = [] \<or> (\<exists>q' Y. q = [Y]\<^sub>R # q') \<or> \<rho> \<noteq> intersect_refusal_trace Z p @ q)) \<Longrightarrow>
      intersect_refusal_trace Xa p @ q \<in> P"
    proof auto
      fix q'
      show "\<forall>p. p \<in> P \<longrightarrow> (\<exists>p'. p = p' @ [[Tick]\<^sub>E]) \<or> (\<exists>p' Y. p = p' @ [[Y]\<^sub>R]) \<or>
          (\<forall>q. q @ [[X]\<^sub>R] \<in> Q \<longrightarrow> (\<forall>Z. [[Z]\<^sub>R] \<in> Q \<longrightarrow> q = [] \<or> (\<exists>q' Y. q = [Y]\<^sub>R # q') \<or> \<rho> \<noteq> intersect_refusal_trace Z p @ q)) \<Longrightarrow>
        q = q' @ [[X]\<^sub>R] \<Longrightarrow> intersect_refusal_trace Xa p @ q' @ [[X]\<^sub>R] \<in> P"
        using case_assms by (erule_tac x="p" in allE, auto, erule_tac x="q'" in allE, auto)
    next
      assume "q = []"
      then have "\<rho> @ [[X]\<^sub>R] \<subseteq>\<^sub>C p"
        by (simp add: case_assms(6) intersect_refusal_trace_subset)
      then have "\<exists> p' Z. p = p' @ [[Z]\<^sub>R]"
        using case_assms(3) apply auto 
        by (induct \<rho> p rule:ctt_subset.induct, auto, fastforce+, case_tac v, auto, case_tac va rule:cttWF.cases, auto)
      then show "\<forall>pa Z. pa @ [[Z]\<^sub>R] \<in> P \<longrightarrow> (\<forall>Y. [[Y]\<^sub>R] \<in> Q \<longrightarrow> intersect_refusal_trace Xa p \<noteq> intersect_refusal_trace Y (pa @ [[Z]\<^sub>R])) \<Longrightarrow>
        q = [] \<Longrightarrow> intersect_refusal_trace Xa p \<in> P"
        using case_assms by auto
    qed
  next
    fix p q Xa
    assume case_assms: "p \<in> P" "\<forall>p'. p \<noteq> p' @ [[Tick]\<^sub>E]" "\<forall>p' Y. p \<noteq> p' @ [[Y]\<^sub>R]" "q \<in> Q"
      "\<forall>q' Y. q \<noteq> [Y]\<^sub>R # q'" "\<rho> @ [[X]\<^sub>R] = intersect_refusal_trace Xa p @ q" "[[Xa]\<^sub>R] \<in> Q"
    then have "(\<exists> q'. q = q' @ [[X]\<^sub>R]) \<or> q = []"
      by (metis append_butlast_last_id last_appendR last_snoc)
    then show "\<forall>pa Z. pa @ [[Z]\<^sub>R] \<in> P \<longrightarrow>
        (\<forall>Y. [[Y]\<^sub>R] \<in> Q \<longrightarrow> intersect_refusal_trace Xa p @ q \<noteq> intersect_refusal_trace Y (pa @ [[Z]\<^sub>R])) \<Longrightarrow>
      \<forall>p. p \<in> P \<longrightarrow> (\<exists>p'. p = p' @ [[Tick]\<^sub>E]) \<or> (\<exists>p' Y. p = p' @ [[Y]\<^sub>R]) \<or>
        (\<forall>q. q @ [[X]\<^sub>R] \<in> Q \<longrightarrow> (\<forall>Z. [[Z]\<^sub>R] \<in> Q \<longrightarrow> q = [] \<or> (\<exists>q' Y. q = [Y]\<^sub>R # q') \<or> \<rho> \<noteq> intersect_refusal_trace Z p @ q)) \<Longrightarrow>
      False"
    proof auto
      fix q'
      show "\<forall>p. p \<in> P \<longrightarrow> (\<exists>p'. p = p' @ [[Tick]\<^sub>E]) \<or> (\<exists>p' Y. p = p' @ [[Y]\<^sub>R]) \<or>
          (\<forall>q. q @ [[X]\<^sub>R] \<in> Q \<longrightarrow> (\<forall>Z. [[Z]\<^sub>R] \<in> Q \<longrightarrow> q = [] \<or> (\<exists>q' Y. q = [Y]\<^sub>R # q') \<or> \<rho> \<noteq> intersect_refusal_trace Z p @ q)) \<Longrightarrow>
        q = q' @ [[X]\<^sub>R] \<Longrightarrow> False"
        using case_assms by (erule_tac x="p" in allE, auto, erule_tac x="q'" in allE, auto)
    next
      assume "q = []"
      then have "\<rho> @ [[X]\<^sub>R] \<subseteq>\<^sub>C p"
        by (simp add: case_assms(6) intersect_refusal_trace_subset)
      then have "\<exists> p' Z. p = p' @ [[Z]\<^sub>R]"
        using case_assms(3) apply auto 
        by (induct \<rho> p rule:ctt_subset.induct, auto, fastforce+, case_tac v, auto, case_tac va rule:cttWF.cases, auto)
      then show "\<forall>pa Z. pa @ [[Z]\<^sub>R] \<in> P \<longrightarrow> (\<forall>Y. [[Y]\<^sub>R] \<in> Q \<longrightarrow> intersect_refusal_trace Xa p \<noteq> intersect_refusal_trace Y (pa @ [[Z]\<^sub>R])) \<Longrightarrow>
        q = [] \<Longrightarrow> False"
        using case_assms by auto
    qed
  next
    fix p q
    assume case_assms: "p \<in> P" "\<forall>p'. p \<noteq> p' @ [[Tick]\<^sub>E]" "\<forall>p' Y. p \<noteq> p' @ [[Y]\<^sub>R]" "q \<in> Q"
      "\<forall>q' Y. q \<noteq> [Y]\<^sub>R # q'" "\<rho> @ [[X]\<^sub>R] = intersect_refusal_trace UNIV p @ q"
    then have "(\<exists> q'. q = q' @ [[X]\<^sub>R]) \<or> q = []"
      by (metis append_butlast_last_id last_appendR last_snoc)
    then show "\<forall>p. p \<in> P \<longrightarrow>
        (\<exists>p'. p = p' @ [[Tick]\<^sub>E]) \<or> (\<exists>p' Y. p = p' @ [[Y]\<^sub>R]) \<or> (\<forall>q. q @ [[X]\<^sub>R] \<in> Q \<longrightarrow> (\<exists>q' Y. q = [Y]\<^sub>R # q') \<or> \<rho> \<noteq> p @ q) \<Longrightarrow>
      intersect_refusal_trace UNIV p @ q \<in> P"
    proof auto
      fix q'
      show "\<forall>p. p \<in> P \<longrightarrow>
          (\<exists>p'. p = p' @ [[Tick]\<^sub>E]) \<or> (\<exists>p' Y. p = p' @ [[Y]\<^sub>R]) \<or> (\<forall>q. q @ [[X]\<^sub>R] \<in> Q \<longrightarrow> (\<exists>q' Y. q = [Y]\<^sub>R # q') \<or> \<rho> \<noteq> p @ q) \<Longrightarrow>
        q = q' @ [[X]\<^sub>R] \<Longrightarrow> intersect_refusal_trace UNIV p @ q' @ [[X]\<^sub>R] \<in> P"
        using case_assms by (erule_tac x="p" in allE, auto, erule_tac x="q'" in allE, auto simp add: intersect_refusal_trace_UNIV_identity)
    next
      assume "q = []"
      then have "\<rho> @ [[X]\<^sub>R] \<subseteq>\<^sub>C p"
        by (simp add: case_assms(6) intersect_refusal_trace_subset)
      then have "\<exists> p' Z. p = p' @ [[Z]\<^sub>R]"
        using case_assms(3) apply auto 
        by (induct \<rho> p rule:ctt_subset.induct, auto, fastforce+, case_tac v, auto, case_tac va rule:cttWF.cases, auto)
      then show "q = [] \<Longrightarrow> intersect_refusal_trace UNIV p \<in> P"
        using case_assms by (auto simp add: intersect_refusal_trace_UNIV_identity)
    qed
  next
    fix Z q' p q
    assume case_assms: "\<forall>Y. [[Y]\<^sub>R] \<notin> Q" "[Z]\<^sub>R # q' \<in> Q"
    then show "False"
      using CT1_Q unfolding CT1_def by (erule_tac x="[[Z]\<^sub>R]" in allE, simp_all)
  qed
  assume assm2: "Y \<inter> {e. e \<noteq> Tock \<and> \<rho> @ [[e]\<^sub>E] \<in> P \<triangle>\<^sub>U Q \<or> e = Tock \<and> \<rho> @ [[X]\<^sub>R, [e]\<^sub>E] \<in> P \<triangle>\<^sub>U Q} = {}"
  show "\<rho> @ [[X \<union> Y]\<^sub>R] \<in> P \<triangle>\<^sub>U Q"
    using \<rho>_cases
  proof auto
    assume case_assms: "\<rho> @ [[X]\<^sub>R] \<in> P" "\<forall>Z q'. [Z]\<^sub>R # q' \<notin> Q"
    then have "{e. e \<noteq> Tock \<and> \<rho> @ [[e]\<^sub>E] \<in> P \<or> e = Tock \<and> \<rho> @ [[X]\<^sub>R, [e]\<^sub>E] \<in> P} \<subseteq> {e. e \<noteq> Tock \<and> \<rho> @ [[e]\<^sub>E] \<in> P \<triangle>\<^sub>U Q \<or> e = Tock \<and> \<rho> @ [[X]\<^sub>R, [e]\<^sub>E] \<in> P \<triangle>\<^sub>U Q}"
      unfolding UntimedInterruptCTT_def
    proof (safe, simp_all)
      fix x
      assume case_assms2: "\<rho> @ [[x]\<^sub>E] \<in> P" "x \<noteq> Tock" "\<rho> @ [[X]\<^sub>R] \<in> P" "\<forall>Z q'. [Z]\<^sub>R # q' \<notin> Q"
      then have "x = Tick \<or> (\<exists> e. x = Event e)"
        by (cases x, auto)
      then show "\<forall>p. p \<in> P \<longrightarrow> (\<exists>p'. p = p' @ [[Tick]\<^sub>E]) \<or> (\<exists>p' Y. p = p' @ [[Y]\<^sub>R])
          \<or> (\<forall>q. q \<in> Q \<longrightarrow> (\<exists>q' Y. q = [Y]\<^sub>R # q') \<or> \<rho> @ [[x]\<^sub>E] \<noteq> intersect_refusal_trace UNIV p @ q) \<Longrightarrow>
        \<exists>p. p @ [[Tick]\<^sub>E] \<in> P \<and> \<rho> @ [[x]\<^sub>E] = intersect_refusal_trace UNIV (p @ [[Tick]\<^sub>E])"
        using case_assms2 CT0_CT1_empty CT0_Q CT1_Q apply auto
        by (rule_tac x="\<rho>" in exI, auto simp add: intersect_refusal_trace_UNIV_identity, erule_tac x="\<rho> @ [[Event e]\<^sub>E]" in allE, auto)
    next
      fix x
      assume case_assms2: "\<rho> @ [[x]\<^sub>E] \<in> P" "x \<noteq> Tock" "\<rho> @ [[X]\<^sub>R] \<in> P" "\<forall>Z q'. [Z]\<^sub>R # q' \<notin> Q"
      then have "x = Tick \<or> (\<exists> e. x = Event e)"
        by (cases x, auto)
      then show "\<forall>p. p \<in> P \<longrightarrow> (\<exists>p'. p = p' @ [[Tick]\<^sub>E]) \<or> (\<exists>p' Y. p = p' @ [[Y]\<^sub>R])
          \<or> (\<forall>q. q \<in> Q \<longrightarrow> (\<exists>q' Y. q = [Y]\<^sub>R # q') \<or> \<rho> @ [[x]\<^sub>E] \<noteq> intersect_refusal_trace UNIV p @ q) \<Longrightarrow>
        \<exists>p. p @ [[Tick]\<^sub>E] \<in> P \<and> \<rho> @ [[x]\<^sub>E] = intersect_refusal_trace UNIV (p @ [[Tick]\<^sub>E])"
        using case_assms2 CT0_CT1_empty CT0_Q CT1_Q apply auto
        by (rule_tac x="\<rho>" in exI, auto simp add: intersect_refusal_trace_UNIV_identity, erule_tac x="\<rho> @ [[Event e]\<^sub>E]" in allE, auto)
    next
      assume case_assms2: "\<rho> @ [[X]\<^sub>R, [Tock]\<^sub>E] \<in> P" "\<rho> @ [[X]\<^sub>R] \<in> P" "\<forall>Z q'. [Z]\<^sub>R # q' \<notin> Q"
      then show "\<forall>p. p \<in> P \<longrightarrow> (\<exists>p'. p = p' @ [[Tick]\<^sub>E]) \<or> (\<exists>p' Y. p = p' @ [[Y]\<^sub>R]) \<or>
          (\<forall>q. q \<in> Q \<longrightarrow> (\<exists>q' Y. q = [Y]\<^sub>R # q') \<or> \<rho> @ [[X]\<^sub>R, [Tock]\<^sub>E] \<noteq> intersect_refusal_trace UNIV p @ q)
        \<Longrightarrow> False"
        using case_assms2 CT0_CT1_empty CT0_Q CT1_Q apply auto
        by (erule_tac x="\<rho> @ [[X]\<^sub>R, [Tock]\<^sub>E]" in allE, auto simp add: intersect_refusal_trace_UNIV_identity)
    next
      assume case_assms2: "\<rho> @ [[X]\<^sub>R, [Tock]\<^sub>E] \<in> P" "\<rho> @ [[X]\<^sub>R] \<in> P" "\<forall>Z q'. [Z]\<^sub>R # q' \<notin> Q"
      then show "\<forall>p. p \<in> P \<longrightarrow> (\<exists>p'. p = p' @ [[Tick]\<^sub>E]) \<or> (\<exists>p' Y. p = p' @ [[Y]\<^sub>R]) \<or>
          (\<forall>q. q \<in> Q \<longrightarrow> (\<exists>q' Y. q = [Y]\<^sub>R # q') \<or> \<rho> @ [[X]\<^sub>R, [Tock]\<^sub>E] \<noteq> intersect_refusal_trace UNIV p @ q)
        \<Longrightarrow> \<exists>p. p @ [[Tick]\<^sub>E] \<in> P \<and> \<rho> @ [[Tock]\<^sub>E] = intersect_refusal_trace UNIV (p @ [[Tick]\<^sub>E])"
        using case_assms2 CT0_CT1_empty CT0_Q CT1_Q apply auto
        by (erule_tac x="\<rho> @ [[X]\<^sub>R, [Tock]\<^sub>E]" in allE, auto simp add: intersect_refusal_trace_UNIV_identity)
    qed
    then have "Y \<inter> {e. e \<noteq> Tock \<and> \<rho> @ [[e]\<^sub>E] \<in> P \<or> e = Tock \<and> \<rho> @ [[X]\<^sub>R, [e]\<^sub>E] \<in> P} = {}"
      using assm2 by auto
    then have "\<rho> @ [[X \<union> Y]\<^sub>R] \<in> P"
      using CT2_P case_assms(1) unfolding CT2_def by auto
    then show "\<rho> @ [[X \<union> Y]\<^sub>R] \<in> P \<triangle>\<^sub>U Q"
      unfolding UntimedInterruptCTT_def
    proof auto
      show "\<rho> @ [[X \<union> Y]\<^sub>R] \<in> P \<Longrightarrow> \<exists>p Xa. p @ [[Xa]\<^sub>R] \<in> P \<and>
           (\<exists>Ya q. ([Ya]\<^sub>R # q \<in> Q \<or> (\<forall>Z q'. [Z]\<^sub>R # q' \<notin> Q) \<and> Ya = UNIV \<and> q = []) \<and>
                   \<rho> @ [[X \<union> Y]\<^sub>R] = intersect_refusal_trace Ya (p @ [[Xa]\<^sub>R]) @ q)"
        using case_assms by (rule_tac x="\<rho>" in exI, rule_tac x="X \<union> Y" in exI, auto simp add: intersect_refusal_trace_UNIV_identity)
    qed
  next
    fix p Z Ya
    assume case_assms: "p @ [[Z]\<^sub>R] \<in> P" "[[Ya]\<^sub>R] \<in> Q" "\<rho> @ [[X]\<^sub>R] = intersect_refusal_trace Ya (p @ [[Z]\<^sub>R])"
    have "{e. e \<noteq> Tock \<and> \<rho> @ [[e]\<^sub>E] \<in> P \<or> e = Tock \<and> \<rho> @ [[X]\<^sub>R, [e]\<^sub>E] \<in> P} \<subseteq> {e. e \<noteq> Tock \<and> \<rho> @ [[e]\<^sub>E] \<in> P \<triangle>\<^sub>U Q \<or> e = Tock \<and> \<rho> @ [[X]\<^sub>R, [e]\<^sub>E] \<in> P \<triangle>\<^sub>U Q}"
      unfolding UntimedInterruptCTT_def
    proof (safe, simp_all)
      fix x
      assume case_assms2: "\<rho> @ [[x]\<^sub>E] \<in> P" "x \<noteq> Tock"
      from case_assms have 1: "\<rho> @ [[x]\<^sub>E] = intersect_refusal_trace Ya (p @ [[x]\<^sub>E])"
        by (simp add: intersect_refusal_trace_end_ref_imp_intersect_refusal_trace_end_event)
      then have 2: "\<rho> @ [[x]\<^sub>E] = intersect_refusal_trace Ya (\<rho> @ [[x]\<^sub>E])"
        by (simp add: intersect_refusal_trace_idempotent)
      from case_assms2 have "x = Tick \<or> (\<exists> e. x = Event e)"
        by (cases x, auto)
      then show "\<forall>p. p \<in> P \<longrightarrow> (\<exists>p'. p = p' @ [[Tick]\<^sub>E]) \<or> (\<exists>p' Y. p = p' @ [[Y]\<^sub>R]) \<or>
          (\<forall>q. q \<in> Q \<longrightarrow> (\<forall>X. [[X]\<^sub>R] \<notin> Q \<and> ((\<exists>Y. [[Y]\<^sub>R] \<in> Q) \<or> X \<noteq> UNIV) \<or>
            (\<exists>q' Y. q = [Y]\<^sub>R # q') \<or> \<rho> @ [[x]\<^sub>E] \<noteq> intersect_refusal_trace X p @ q)) \<Longrightarrow>
        \<exists>p. p @ [[Tick]\<^sub>E] \<in> P \<and>
             (\<exists>X. ([[X]\<^sub>R] \<in> Q \<or> (\<forall>Y. [[Y]\<^sub>R] \<notin> Q) \<and> X = UNIV) \<and> \<rho> @ [[x]\<^sub>E] = intersect_refusal_trace X (p @ [[Tick]\<^sub>E]))"
        using case_assms case_assms2 CT0_CT1_empty CT0_Q CT1_Q 2 apply auto
        by (erule_tac x="\<rho> @ [[Event e]\<^sub>E]" in allE, auto, erule_tac x="[]" in allE, auto)
    next
      fix x
      assume case_assms2: "\<rho> @ [[x]\<^sub>E] \<in> P" "x \<noteq> Tock"
      thm case_assms
      from case_assms have 1: "\<rho> @ [[x]\<^sub>E] = intersect_refusal_trace Ya (p @ [[x]\<^sub>E])"
        by (simp add: intersect_refusal_trace_end_ref_imp_intersect_refusal_trace_end_event)
      then have 2: "\<rho> @ [[x]\<^sub>E] = intersect_refusal_trace Ya (\<rho> @ [[x]\<^sub>E])"
        by (simp add: intersect_refusal_trace_idempotent)
      from case_assms2 have "x = Tick \<or> (\<exists> e. x = Event e)"
        by (cases x, auto)
      then show "\<forall>p. p \<in> P \<longrightarrow> (\<exists>p'. p = p' @ [[Tick]\<^sub>E]) \<or> (\<exists>p' Y. p = p' @ [[Y]\<^sub>R]) \<or>
          (\<forall>q. q \<in> Q \<longrightarrow> (\<forall>X. [[X]\<^sub>R] \<notin> Q \<and> ((\<exists>Y. [[Y]\<^sub>R] \<in> Q) \<or> X \<noteq> UNIV) \<or>
            (\<exists>q' Y. q = [Y]\<^sub>R # q') \<or> \<rho> @ [[x]\<^sub>E] \<noteq> intersect_refusal_trace X p @ q)) \<Longrightarrow>
        \<exists>p. p @ [[Tick]\<^sub>E] \<in> P \<and>
             (\<exists>X. ([[X]\<^sub>R] \<in> Q \<or> (\<forall>Y. [[Y]\<^sub>R] \<notin> Q) \<and> X = UNIV) \<and> \<rho> @ [[x]\<^sub>E] = intersect_refusal_trace X (p @ [[Tick]\<^sub>E]))"
        using case_assms case_assms2 CT0_CT1_empty CT0_Q CT1_Q 2 apply auto
        by (erule_tac x="\<rho> @ [[Event e]\<^sub>E]" in allE, auto, erule_tac x="[]" in allE, auto)
    next
      assume case_assms2: "\<rho> @ [[X]\<^sub>R, [Tock]\<^sub>E] \<in> P"
      from case_assms have 1: "\<rho> @ [[X]\<^sub>R, [Tock]\<^sub>E] = intersect_refusal_trace Ya (p @ [[X]\<^sub>R, [Tock]\<^sub>E])"
        by (simp add: intersect_refusal_trace_end_ref_imp_intersect_refusal_trace_end_ref_tock)
      then have 2: "\<rho> @ [[X]\<^sub>R, [Tock]\<^sub>E] = intersect_refusal_trace Ya (\<rho> @ [[X]\<^sub>R, [Tock]\<^sub>E])"
        by (simp add: intersect_refusal_trace_idempotent)
      then show "\<forall>p. p \<in> P \<longrightarrow> (\<exists>p'. p = p' @ [[Tick]\<^sub>E]) \<or> (\<exists>p' Y. p = p' @ [[Y]\<^sub>R]) \<or>
          (\<forall>q. q \<in> Q \<longrightarrow> (\<forall>Xa. [[Xa]\<^sub>R] \<notin> Q \<and> ((\<exists>Y. [[Y]\<^sub>R] \<in> Q) \<or> Xa \<noteq> UNIV) \<or>
            (\<exists>q' Y. q = [Y]\<^sub>R # q') \<or> \<rho> @ [[X]\<^sub>R, [Tock]\<^sub>E] \<noteq> intersect_refusal_trace Xa p @ q)) \<Longrightarrow> False"
        using case_assms case_assms2 CT0_CT1_empty CT0_Q CT1_Q 1 2 apply auto
        by (erule_tac x="\<rho> @ [[X]\<^sub>R, [Tock]\<^sub>E]" in allE, auto, erule_tac x="[]" in allE, auto)
    next
      assume case_assms2: "\<rho> @ [[X]\<^sub>R, [Tock]\<^sub>E] \<in> P"
      from case_assms have 1: "\<rho> @ [[X]\<^sub>R, [Tock]\<^sub>E] = intersect_refusal_trace Ya (p @ [[X]\<^sub>R, [Tock]\<^sub>E])"
        by (simp add: intersect_refusal_trace_end_ref_imp_intersect_refusal_trace_end_ref_tock)
      then have 2: "\<rho> @ [[X]\<^sub>R, [Tock]\<^sub>E] = intersect_refusal_trace Ya (\<rho> @ [[X]\<^sub>R, [Tock]\<^sub>E])"
        by (simp add: intersect_refusal_trace_idempotent)
      then show "\<forall>p. p \<in> P \<longrightarrow> (\<exists>p'. p = p' @ [[Tick]\<^sub>E]) \<or> (\<exists>p' Y. p = p' @ [[Y]\<^sub>R]) \<or>
          (\<forall>q. q \<in> Q \<longrightarrow> (\<forall>Xa. [[Xa]\<^sub>R] \<notin> Q \<and> ((\<exists>Y. [[Y]\<^sub>R] \<in> Q) \<or> Xa \<noteq> UNIV) \<or>
            (\<exists>q' Y. q = [Y]\<^sub>R # q') \<or> \<rho> @ [[X]\<^sub>R, [Tock]\<^sub>E] \<noteq> intersect_refusal_trace Xa p @ q)) \<Longrightarrow> 
        \<exists>p. p @ [[Tick]\<^sub>E] \<in> P \<and>
          (\<exists>X. ([[X]\<^sub>R] \<in> Q \<or> (\<forall>Y. [[Y]\<^sub>R] \<notin> Q) \<and> X = UNIV) \<and> \<rho> @ [[Tock]\<^sub>E] = intersect_refusal_trace X (p @ [[Tick]\<^sub>E]))"
        using case_assms case_assms2 CT0_CT1_empty CT0_Q CT1_Q 1 2 apply auto
        by (erule_tac x="\<rho> @ [[X]\<^sub>R, [Tock]\<^sub>E]" in allE, auto, erule_tac x="[]" in allE, auto)
    qed
    then have 1: "Y \<inter> {e. e \<noteq> Tock \<and> \<rho> @ [[e]\<^sub>E] \<in> P \<or> e = Tock \<and> \<rho> @ [[X]\<^sub>R, [e]\<^sub>E] \<in> P} = {}"
      using assm2 by auto
    have 2: "\<rho> @ [[X]\<^sub>R] \<in> P"
      using CT1_P CT1_def case_assms(1) case_assms(3) intersect_refusal_trace_prefix_subset by fastforce
    then have 3: "\<rho> @ [[X \<union> Y]\<^sub>R] \<in> P"
      using CT2_P 1 unfolding CT2_def by auto
    have "{e. e \<noteq> Tock \<and> [[e]\<^sub>E] \<in> Q \<or> e = Tock \<and> [[Ya]\<^sub>R, [e]\<^sub>E] \<in> Q} \<subseteq> {e. e \<noteq> Tock \<and> \<rho> @ [[e]\<^sub>E] \<in> P \<triangle>\<^sub>U Q \<or> e = Tock \<and> \<rho> @ [[X]\<^sub>R, [e]\<^sub>E] \<in> P \<triangle>\<^sub>U Q}"
      unfolding UntimedInterruptCTT_def
    proof (safe, simp_all)
      fix x 
      assume case_assms2: "[[x]\<^sub>E] \<in> Q" "x \<noteq> Tock"
      have p_in_P: "p \<in> P"
        by (metis CT1_P CT1_def append_Nil2 case_assms(1) ctt_prefix_subset.simps(1) ctt_prefix_subset_same_front)
      have "(\<exists>p'. p = p' @ [[Tick]\<^sub>E]) \<or> (\<exists>p' Y. p = p' @ [[Y]\<^sub>R]) \<or> ((\<forall>p'. p \<noteq> p' @ [[Tick]\<^sub>E]) \<and> (\<forall>p' Y. p \<noteq> p' @ [[Y]\<^sub>R]))"
        by auto
      then have p_case: "(\<forall>p'. p \<noteq> p' @ [[Tick]\<^sub>E]) \<and> (\<forall>p' Y. p \<noteq> p' @ [[Y]\<^sub>R])"
        using case_assms(1) 
      proof auto
        fix p'a
        assume "p'a @ [[Tick]\<^sub>E, [Z]\<^sub>R] \<in> P"
        then have "cttWF (p'a @ [[Tick]\<^sub>E, [Z]\<^sub>R])"
          using P_wf by blast
        then show False
          by (induct p'a rule:cttWF.induct, auto)
      next
        fix p'a Ya
        assume "p'a @ [[Ya]\<^sub>R, [Z]\<^sub>R] \<in> P"
        then have "cttWF (p'a @ [[Ya]\<^sub>R, [Z]\<^sub>R])"
          using P_wf by blast
        then show False
          by (induct p'a rule:cttWF.induct, auto)
      qed
      then show "\<forall>p. p \<in> P \<longrightarrow> (\<exists>p'. p = p' @ [[Tick]\<^sub>E]) \<or> (\<exists>p' Y. p = p' @ [[Y]\<^sub>R]) \<or>
             (\<forall>q. q \<in> Q \<longrightarrow> (\<forall>X. [[X]\<^sub>R] \<notin> Q \<and> ((\<exists>Y. [[Y]\<^sub>R] \<in> Q) \<or> X \<noteq> UNIV) \<or>
                       (\<exists>q' Y. q = [Y]\<^sub>R # q') \<or> \<rho> @ [[x]\<^sub>E] \<noteq> intersect_refusal_trace X p @ q)) \<Longrightarrow>
         \<exists>p. p @ [[Tick]\<^sub>E] \<in> P \<and>
             (\<exists>X. ([[X]\<^sub>R] \<in> Q \<or> (\<forall>Y. [[Y]\<^sub>R] \<notin> Q) \<and> X = UNIV) \<and> \<rho> @ [[x]\<^sub>E] = intersect_refusal_trace X (p @ [[Tick]\<^sub>E]))"
        using p_in_P case_assms2 case_assms apply (erule_tac x="p" in allE, auto, erule_tac x="[[x]\<^sub>E]" in allE, auto)
        by (erule_tac x="Ya" in allE, auto, meson eq_intersect_refusal_trace_append intersect_refusal_trace_end_ref_imp_intersect_refusal_trace_end_event)
    next
      fix x 
      assume case_assms2: "[[x]\<^sub>E] \<in> Q" "x \<noteq> Tock"
      have p_in_P: "p \<in> P"
        by (metis CT1_P CT1_def append_Nil2 case_assms(1) ctt_prefix_subset.simps(1) ctt_prefix_subset_same_front)
      have "(\<exists>p'. p = p' @ [[Tick]\<^sub>E]) \<or> (\<exists>p' Y. p = p' @ [[Y]\<^sub>R]) \<or> ((\<forall>p'. p \<noteq> p' @ [[Tick]\<^sub>E]) \<and> (\<forall>p' Y. p \<noteq> p' @ [[Y]\<^sub>R]))"
        by auto
      then have p_case: "(\<forall>p'. p \<noteq> p' @ [[Tick]\<^sub>E]) \<and> (\<forall>p' Y. p \<noteq> p' @ [[Y]\<^sub>R])"
        using case_assms(1) 
      proof auto
        fix p'a
        assume "p'a @ [[Tick]\<^sub>E, [Z]\<^sub>R] \<in> P"
        then have "cttWF (p'a @ [[Tick]\<^sub>E, [Z]\<^sub>R])"
          using P_wf by blast
        then show False
          by (induct p'a rule:cttWF.induct, auto)
      next
        fix p'a Ya
        assume "p'a @ [[Ya]\<^sub>R, [Z]\<^sub>R] \<in> P"
        then have "cttWF (p'a @ [[Ya]\<^sub>R, [Z]\<^sub>R])"
          using P_wf by blast
        then show False
          by (induct p'a rule:cttWF.induct, auto)
      qed
      then show "\<forall>p. p \<in> P \<longrightarrow> (\<exists>p'. p = p' @ [[Tick]\<^sub>E]) \<or> (\<exists>p' Y. p = p' @ [[Y]\<^sub>R]) \<or>
             (\<forall>q. q \<in> Q \<longrightarrow> (\<forall>X. [[X]\<^sub>R] \<notin> Q \<and> ((\<exists>Y. [[Y]\<^sub>R] \<in> Q) \<or> X \<noteq> UNIV) \<or>
                       (\<exists>q' Y. q = [Y]\<^sub>R # q') \<or> \<rho> @ [[x]\<^sub>E] \<noteq> intersect_refusal_trace X p @ q)) \<Longrightarrow>
         \<exists>p. p @ [[Tick]\<^sub>E] \<in> P \<and>
             (\<exists>X. ([[X]\<^sub>R] \<in> Q \<or> (\<forall>Y. [[Y]\<^sub>R] \<notin> Q) \<and> X = UNIV) \<and> \<rho> @ [[x]\<^sub>E] = intersect_refusal_trace X (p @ [[Tick]\<^sub>E]))"
        using p_in_P case_assms2 case_assms apply (erule_tac x="p" in allE, auto, erule_tac x="[[x]\<^sub>E]" in allE, auto)
        by (erule_tac x="Ya" in allE, auto, meson eq_intersect_refusal_trace_append intersect_refusal_trace_end_ref_imp_intersect_refusal_trace_end_event)
    next
      assume "[[Ya]\<^sub>R, [Tock]\<^sub>E] \<in> Q"
      then show "\<forall>p Xa. p @ [[Xa]\<^sub>R] \<in> P \<longrightarrow> (\<forall>Y q. [Y]\<^sub>R # q \<notin> Q \<and> (Y = UNIV \<longrightarrow> (\<exists>Z q'. [Z]\<^sub>R # q' \<in> Q) \<or> q \<noteq> []) \<or>
        \<rho> @ [[X]\<^sub>R, [Tock]\<^sub>E] \<noteq> intersect_refusal_trace Y (p @ [[Xa]\<^sub>R]) @ q) \<Longrightarrow> False"
        using case_assms apply (erule_tac x="p" in allE, erule_tac x="Z" in allE, auto)
        by (erule_tac x="Ya" in allE, erule_tac x="[[Tock]\<^sub>E]" in allE, auto)
    next
      assume "[[Ya]\<^sub>R, [Tock]\<^sub>E] \<in> Q"
      then show "\<forall>p Xa. p @ [[Xa]\<^sub>R] \<in> P \<longrightarrow> (\<forall>Y q. [Y]\<^sub>R # q \<notin> Q \<and> (Y = UNIV \<longrightarrow> (\<exists>Z q'. [Z]\<^sub>R # q' \<in> Q) \<or> q \<noteq> []) \<or>
          \<rho> @ [[X]\<^sub>R, [Tock]\<^sub>E] \<noteq> intersect_refusal_trace Y (p @ [[Xa]\<^sub>R]) @ q) \<Longrightarrow>
        \<exists>p. p @ [[Tick]\<^sub>E] \<in> P \<and>
          (\<exists>X. ([[X]\<^sub>R] \<in> Q \<or> (\<forall>Y. [[Y]\<^sub>R] \<notin> Q) \<and> X = UNIV) \<and> \<rho> @ [[Tock]\<^sub>E] = intersect_refusal_trace X (p @ [[Tick]\<^sub>E]))"
        using case_assms apply (erule_tac x="p" in allE, erule_tac x="Z" in allE, auto)
        by (erule_tac x="Ya" in allE, erule_tac x="[[Tock]\<^sub>E]" in allE, auto)
    qed
    then have "Y \<inter> {e. e \<noteq> Tock \<and> [[e]\<^sub>E] \<in> Q \<or> e = Tock \<and> [[Ya]\<^sub>R, [e]\<^sub>E] \<in> Q} = {}"
      using assm2 by auto
    then have 4: "[[Ya \<union> Y]\<^sub>R] \<in> Q"
      using CT2_Q case_assms(2) unfolding CT2_def by (erule_tac x="[]" in allE, auto)
    show "\<rho> @ [[X \<union> Y]\<^sub>R] \<in> P \<triangle>\<^sub>U Q"
      using case_assms 1 2 3 4 unfolding UntimedInterruptCTT_def apply auto
    proof (rule_tac x="\<rho>" in exI, rule_tac x="X \<union> Y" in exI, auto, rule_tac x="Ya \<union> Y" in exI, rule_tac x="[]" in exI, auto)
      assume "\<rho> @ [[X]\<^sub>R] = intersect_refusal_trace Ya (p @ [[Z]\<^sub>R])"
      then have "\<rho> @ [[X]\<^sub>R] = intersect_refusal_trace Ya (\<rho> @ [[X]\<^sub>R])"
        by (simp add: intersect_refusal_trace_idempotent)
      then show "\<rho> @ [[X \<union> Y]\<^sub>R] = intersect_refusal_trace (Ya \<union> Y) (\<rho> @ [[X \<union> Y]\<^sub>R])"
        by (induct \<rho>, auto, case_tac a, auto)
    qed
  next
    fix p Z Ya q
    thm assm2
    assume case_assms: "[Ya]\<^sub>R # q @ [[X]\<^sub>R] \<in> Q" "p @ [[Z]\<^sub>R] \<in> P" "\<rho> = intersect_refusal_trace Ya (p @ [[Z]\<^sub>R]) @ q"
    have "{e. e \<noteq> Tock \<and> [Ya]\<^sub>R # q @ [[e]\<^sub>E] \<in> Q \<or> e = Tock \<and> [Ya]\<^sub>R # q @ [[X]\<^sub>R, [e]\<^sub>E] \<in> Q} 
      \<subseteq> {e. e \<noteq> Tock \<and> \<rho> @ [[e]\<^sub>E] \<in> P \<triangle>\<^sub>U Q \<or> e = Tock \<and> \<rho> @ [[X]\<^sub>R, [e]\<^sub>E] \<in> P \<triangle>\<^sub>U Q}"
      unfolding UntimedInterruptCTT_def
    proof auto
      fix x
      assume "[Ya]\<^sub>R # q @ [[x]\<^sub>E] \<in> Q" "x \<noteq> Tock"
      then show "\<exists>p X. p @ [[X]\<^sub>R] \<in> P \<and> (\<exists>Y q. ([Y]\<^sub>R # q \<in> Q \<or> (\<forall>Z q'. [Z]\<^sub>R # q' \<notin> Q) \<and> Y = UNIV \<and> q = []) \<and>
        \<rho> @ [[x]\<^sub>E] = intersect_refusal_trace Y (p @ [[X]\<^sub>R]) @ q)"
        using case_assms by auto
    next
      fix x
      assume "[Ya]\<^sub>R # q @ [[x]\<^sub>E] \<in> Q" "x \<noteq> Tock"
      then show "\<exists>p X. p @ [[X]\<^sub>R] \<in> P \<and> (\<exists>Y q. ([Y]\<^sub>R # q \<in> Q \<or> (\<forall>Z q'. [Z]\<^sub>R # q' \<notin> Q) \<and> Y = UNIV \<and> q = []) \<and>
        \<rho> @ [[x]\<^sub>E] = intersect_refusal_trace Y (p @ [[X]\<^sub>R]) @ q)"
        using case_assms by auto
    next
      fix x
      assume "[Ya]\<^sub>R # q @ [[X]\<^sub>R, [Tock]\<^sub>E] \<in> Q"
      then show "\<forall>p Xa. p @ [[Xa]\<^sub>R] \<in> P \<longrightarrow> (\<forall>Y q. [Y]\<^sub>R # q \<notin> Q \<and> (Y = UNIV \<longrightarrow> (\<exists>Z q'. [Z]\<^sub>R # q' \<in> Q) \<or> q \<noteq> []) \<or>
        \<rho> @ [[X]\<^sub>R, [Tock]\<^sub>E] \<noteq> intersect_refusal_trace Y (p @ [[Xa]\<^sub>R]) @ q) \<Longrightarrow> False"
        using case_assms by auto
    next
      fix x
      assume "[Ya]\<^sub>R # q @ [[X]\<^sub>R, [Tock]\<^sub>E] \<in> Q"
      then show "\<forall>p Xa. p @ [[Xa]\<^sub>R] \<in> P \<longrightarrow> (\<forall>Y q. [Y]\<^sub>R # q \<notin> Q \<and> (Y = UNIV \<longrightarrow> (\<exists>Z q'. [Z]\<^sub>R # q' \<in> Q) \<or> q \<noteq> []) \<or>
          \<rho> @ [[X]\<^sub>R, [Tock]\<^sub>E] \<noteq> intersect_refusal_trace Y (p @ [[Xa]\<^sub>R]) @ q) \<Longrightarrow>
        \<exists>p X. p @ [[X]\<^sub>R] \<in> P \<and> (\<exists>Y q. ([Y]\<^sub>R # q \<in> Q \<or> (\<forall>Z q'. [Z]\<^sub>R # q' \<notin> Q) \<and> Y = UNIV \<and> q = []) \<and>
          \<rho> @ [[Tock]\<^sub>E] = intersect_refusal_trace Y (p @ [[X]\<^sub>R]) @ q)"
        using case_assms by (erule_tac x="p" in allE, erule_tac x="Z" in allE, auto)
    qed
    then have "Y \<inter> {e. e \<noteq> Tock \<and> [Ya]\<^sub>R # q @ [[e]\<^sub>E] \<in> Q \<or> e = Tock \<and> [Ya]\<^sub>R # q @ [[X]\<^sub>R, [e]\<^sub>E] \<in> Q} = {}"
      using assm2 by auto
    then have "[Ya]\<^sub>R # q @ [[X \<union> Y]\<^sub>R] \<in> Q"
      using case_assms CT2_Q unfolding CT2_def by (erule_tac x="[Ya]\<^sub>R # q" in allE, auto)
    then show "intersect_refusal_trace Ya (p @ [[Z]\<^sub>R]) @ q @ [[X \<union> Y]\<^sub>R] \<in> P \<triangle>\<^sub>U Q"
      using case_assms unfolding UntimedInterruptCTT_def by auto 
  next
    fix p q Z
    assume case_assms: "p \<in> P" "\<forall>p'. p \<noteq> p' @ [[Tick]\<^sub>E]" "\<forall>p' Y. p \<noteq> p' @ [[Y]\<^sub>R]" "[[Z]\<^sub>R] \<in> Q"
      "q @ [[X]\<^sub>R] \<in> Q" "\<forall>q' Y. q \<noteq> [Y]\<^sub>R # q'" "\<rho> = intersect_refusal_trace Z p @ q" "q \<noteq> []"
    have "{e. e \<noteq> Tock \<and> q @ [[e]\<^sub>E] \<in> Q \<or> e = Tock \<and> q @ [[X]\<^sub>R, [e]\<^sub>E] \<in> Q} 
      \<subseteq> {e. e \<noteq> Tock \<and> \<rho> @ [[e]\<^sub>E] \<in> P \<triangle>\<^sub>U Q \<or> e = Tock \<and> \<rho> @ [[X]\<^sub>R, [e]\<^sub>E] \<in> P \<triangle>\<^sub>U Q}"
      unfolding UntimedInterruptCTT_def
    proof auto
      fix x
      assume "q @ [[x]\<^sub>E] \<in> Q" "x \<noteq> Tock"
      then show "\<forall>p. p \<in> P \<longrightarrow> (\<exists>p'. p = p' @ [[Tick]\<^sub>E]) \<or> (\<exists>p' Y. p = p' @ [[Y]\<^sub>R]) \<or>
          (\<forall>q. q \<in> Q \<longrightarrow> (\<forall>X. [[X]\<^sub>R] \<notin> Q \<and> ((\<exists>Y. [[Y]\<^sub>R] \<in> Q) \<or> X \<noteq> UNIV) \<or>
            (\<exists>q' Y. q = [Y]\<^sub>R # q') \<or> \<rho> @ [[x]\<^sub>E] \<noteq> intersect_refusal_trace X p @ q)) \<Longrightarrow>
        \<exists>p X. p @ [[X]\<^sub>R] \<in> P \<and> (\<exists>Y q. ([Y]\<^sub>R # q \<in> Q \<or> (\<forall>Z q'. [Z]\<^sub>R # q' \<notin> Q) \<and> Y = UNIV \<and> q = []) \<and>
          \<rho> @ [[x]\<^sub>E] = intersect_refusal_trace Y (p @ [[X]\<^sub>R]) @ q)"
        using case_assms apply (erule_tac x="p" in allE, auto)
        by (erule_tac x="q @ [[x]\<^sub>E]" in allE, auto, erule_tac x="Z" in allE, auto simp add: append_eq_Cons_conv)
    next
      fix x
      assume "q @ [[x]\<^sub>E] \<in> Q" "x \<noteq> Tock"
      then show "\<forall>p. p \<in> P \<longrightarrow> (\<exists>p'. p = p' @ [[Tick]\<^sub>E]) \<or> (\<exists>p' Y. p = p' @ [[Y]\<^sub>R]) \<or>
          (\<forall>q. q \<in> Q \<longrightarrow> (\<forall>X. [[X]\<^sub>R] \<notin> Q \<and> ((\<exists>Y. [[Y]\<^sub>R] \<in> Q) \<or> X \<noteq> UNIV) \<or>
            (\<exists>q' Y. q = [Y]\<^sub>R # q') \<or> \<rho> @ [[x]\<^sub>E] \<noteq> intersect_refusal_trace X p @ q)) \<Longrightarrow>
        \<exists>p X. p @ [[X]\<^sub>R] \<in> P \<and> (\<exists>Y q. ([Y]\<^sub>R # q \<in> Q \<or> (\<forall>Z q'. [Z]\<^sub>R # q' \<notin> Q) \<and> Y = UNIV \<and> q = []) \<and>
          \<rho> @ [[x]\<^sub>E] = intersect_refusal_trace Y (p @ [[X]\<^sub>R]) @ q)"
        using case_assms apply (erule_tac x="p" in allE, auto)
        by (erule_tac x="q @ [[x]\<^sub>E]" in allE, auto, erule_tac x="Z" in allE, auto simp add: append_eq_Cons_conv)
    next
      fix x
      assume "q @ [[X]\<^sub>R, [Tock]\<^sub>E] \<in> Q"
      then show "\<forall>p. p \<in> P \<longrightarrow> (\<exists>p'. p = p' @ [[Tick]\<^sub>E]) \<or> (\<exists>p' Y. p = p' @ [[Y]\<^sub>R]) \<or>
        (\<forall>q. q \<in> Q \<longrightarrow> (\<forall>Xa. [[Xa]\<^sub>R] \<notin> Q \<and> ((\<exists>Y. [[Y]\<^sub>R] \<in> Q) \<or> Xa \<noteq> UNIV) \<or>
          (\<exists>q' Y. q = [Y]\<^sub>R # q') \<or> \<rho> @ [[X]\<^sub>R, [Tock]\<^sub>E] \<noteq> intersect_refusal_trace Xa p @ q)) \<Longrightarrow> False"
        using case_assms
      proof (erule_tac x="p" in allE, auto, erule_tac x="q @ [[X]\<^sub>R, [Tock]\<^sub>E]" in allE, auto, erule_tac x="Z" in allE, auto)
        fix q' Y
        assume "q @ [[X]\<^sub>R, [Tock]\<^sub>E] = [Y]\<^sub>R # q'"
        then have "(\<exists> q''. q = [Y]\<^sub>R # q'')"
          using case_assms by (induct q, auto)
        then show "\<forall>q' Y. q \<noteq> [Y]\<^sub>R # q' \<Longrightarrow> False"
          by auto
      qed
    next
      fix x
      assume "q @ [[X]\<^sub>R, [Tock]\<^sub>E] \<in> Q"
      then show "\<forall>p. p \<in> P \<longrightarrow> (\<exists>p'. p = p' @ [[Tick]\<^sub>E]) \<or> (\<exists>p' Y. p = p' @ [[Y]\<^sub>R]) \<or>
        (\<forall>q. q \<in> Q \<longrightarrow> (\<forall>Xa. [[Xa]\<^sub>R] \<notin> Q \<and> ((\<exists>Y. [[Y]\<^sub>R] \<in> Q) \<or> Xa \<noteq> UNIV) \<or>
          (\<exists>q' Y. q = [Y]\<^sub>R # q') \<or> \<rho> @ [[X]\<^sub>R, [Tock]\<^sub>E] \<noteq> intersect_refusal_trace Xa p @ q)) \<Longrightarrow>
        \<exists>p X. p @ [[X]\<^sub>R] \<in> P \<and> (\<exists>Y q. ([Y]\<^sub>R # q \<in> Q \<or> (\<forall>Z q'. [Z]\<^sub>R # q' \<notin> Q) \<and> Y = UNIV \<and> q = []) \<and>
          \<rho> @ [[Tock]\<^sub>E] = intersect_refusal_trace Y (p @ [[X]\<^sub>R]) @ q)"
        using case_assms
      proof (erule_tac x="p" in allE, auto, erule_tac x="q @ [[X]\<^sub>R, [Tock]\<^sub>E]" in allE, auto, erule_tac x="Z" in allE, auto)
        fix q' Y
        assume "q @ [[X]\<^sub>R, [Tock]\<^sub>E] = [Y]\<^sub>R # q'"
        then have "(\<exists> q''. q = [Y]\<^sub>R # q'')"
          using case_assms by (induct q, auto)
        then show "\<forall>q' Y. q \<noteq> [Y]\<^sub>R # q' \<Longrightarrow>
          \<exists>pa X. pa @ [[X]\<^sub>R] \<in> P \<and> (\<exists>Y qa. ([Y]\<^sub>R # qa \<in> Q \<or> (\<forall>Z q'. [Z]\<^sub>R # q' \<notin> Q) \<and> Y = UNIV \<and> qa = []) \<and>
            intersect_refusal_trace Z p @ q @ [[Tock]\<^sub>E] = intersect_refusal_trace Y (pa @ [[X]\<^sub>R]) @ qa)"
          by auto
      qed
    qed
    then have "Y \<inter> {e. e \<noteq> Tock \<and> q @ [[e]\<^sub>E] \<in> Q \<or> e = Tock \<and> q @ [[X]\<^sub>R, [e]\<^sub>E] \<in> Q} = {}"
      using assm2 by auto
    then have "q @ [[X \<union> Y]\<^sub>R] \<in> Q"
      using case_assms CT2_Q unfolding CT2_def by (erule_tac x="q" in allE, auto)
    then show "intersect_refusal_trace Z p @ q @ [[X \<union> Y]\<^sub>R] \<in> P \<triangle>\<^sub>U Q"
      using case_assms unfolding UntimedInterruptCTT_def
    proof auto
      show "q @ [[X \<union> Y]\<^sub>R] \<in> Q \<Longrightarrow>
        \<forall>pa. pa \<in> P \<longrightarrow> (\<exists>p'. pa = p' @ [[Tick]\<^sub>E]) \<or> (\<exists>p' Y. pa = p' @ [[Y]\<^sub>R]) \<or>
          (\<forall>qa. qa \<in> Q \<longrightarrow> (\<forall>Xa. [[Xa]\<^sub>R] \<notin> Q \<and> ((\<exists>Y. [[Y]\<^sub>R] \<in> Q) \<or> Xa \<noteq> UNIV) \<or>
            (\<exists>q' Y. qa = [Y]\<^sub>R # q') \<or> intersect_refusal_trace Z p @ q @ [[X \<union> Y]\<^sub>R] \<noteq> intersect_refusal_trace Xa pa @ qa)) \<Longrightarrow>
        \<exists>pa Xa. pa @ [[Xa]\<^sub>R] \<in> P \<and> (\<exists>Ya qa. ([Ya]\<^sub>R # qa \<in> Q \<or> (\<forall>Z q'. [Z]\<^sub>R # q' \<notin> Q) \<and> Ya = UNIV \<and> qa = []) \<and>
          intersect_refusal_trace Z p @ q @ [[X \<union> Y]\<^sub>R] = intersect_refusal_trace Ya (pa @ [[Xa]\<^sub>R]) @ qa)"
        using case_assms apply (erule_tac x="p" in allE, auto)
        apply (erule_tac x="q @ [[X \<union> Y]\<^sub>R]" in allE, auto)
        apply (erule_tac x="Z" in allE, auto)
        by (metis butlast.simps(2) butlast_snoc)
    qed
  next
    fix p q
    assume case_assms: "p \<in> P" "\<forall>p'. p \<noteq> p' @ [[Tick]\<^sub>E]" "\<forall>p' Y. p \<noteq> p' @ [[Y]\<^sub>R]" "\<forall>Y. [[Y]\<^sub>R] \<notin> Q" "q @ [[X]\<^sub>R] \<in> Q" "\<rho> = p @ q"
    have "{e. e \<noteq> Tock \<and> q @ [[e]\<^sub>E] \<in> Q \<or> e = Tock \<and> q @ [[X]\<^sub>R, [e]\<^sub>E] \<in> Q} 
      \<subseteq> {e. e \<noteq> Tock \<and> \<rho> @ [[e]\<^sub>E] \<in> P \<triangle>\<^sub>U Q \<or> e = Tock \<and> \<rho> @ [[X]\<^sub>R, [e]\<^sub>E] \<in> P \<triangle>\<^sub>U Q}"
      unfolding UntimedInterruptCTT_def
    proof auto
      fix x
      assume "q @ [[x]\<^sub>E] \<in> Q"
      then show "\<forall>p. p \<in> P \<longrightarrow> (\<exists>p'. p = p' @ [[Tick]\<^sub>E]) \<or> (\<exists>p' Y. p = p' @ [[Y]\<^sub>R]) \<or>
          (\<forall>q. q \<in> Q \<longrightarrow> (\<forall>X. [[X]\<^sub>R] \<notin> Q \<and> ((\<exists>Y. [[Y]\<^sub>R] \<in> Q) \<or> X \<noteq> UNIV) \<or>
            (\<exists>q' Y. q = [Y]\<^sub>R # q') \<or> \<rho> @ [[x]\<^sub>E] \<noteq> intersect_refusal_trace X p @ q)) \<Longrightarrow>
        \<exists>p X. p @ [[X]\<^sub>R] \<in> P \<and>(\<exists>Y q. ([Y]\<^sub>R # q \<in> Q \<or> (\<forall>Z q'. [Z]\<^sub>R # q' \<notin> Q) \<and> Y = UNIV \<and> q = []) \<and>
          \<rho> @ [[x]\<^sub>E] = intersect_refusal_trace Y (p @ [[X]\<^sub>R]) @ q)"
        using case_assms 
      proof (erule_tac x="p" in allE, auto, erule_tac x="q @ [[x]\<^sub>E]" in allE, auto)
        fix q' Y
        assume "[Y]\<^sub>R # q' \<in> Q"
        then have "[[Y]\<^sub>R] \<in> Q"
          by (meson CT1_Q CT1_def ctt_prefix_subset.simps(1) ctt_prefix_subset.simps(2) subsetI)
        then show "\<forall>Y. [[Y]\<^sub>R] \<notin> Q \<Longrightarrow>
          \<exists>pa X. pa @ [[X]\<^sub>R] \<in> P \<and> (\<exists>Ya q. ([Ya]\<^sub>R # q \<in> Q \<or> (\<forall>Z q'. [Z]\<^sub>R # q' \<notin> Q) \<and> Ya = UNIV \<and> q = []) \<and>
            p @ [Y]\<^sub>R # q' = intersect_refusal_trace Ya (pa @ [[X]\<^sub>R]) @ q)"
          by auto
      next
        show "p \<noteq> intersect_refusal_trace UNIV p \<Longrightarrow>
          \<exists>pa X. pa @ [[X]\<^sub>R] \<in> P \<and> (\<exists>Y qa. ([Y]\<^sub>R # qa \<in> Q \<or> (\<forall>Z q'. [Z]\<^sub>R # q' \<notin> Q) \<and> Y = UNIV \<and> qa = []) \<and>
            p @ q @ [[x]\<^sub>E] = intersect_refusal_trace Y (pa @ [[X]\<^sub>R]) @ qa)"
          by (simp add: intersect_refusal_trace_UNIV_identity)
      qed
    next
      fix x
      assume "q @ [[x]\<^sub>E] \<in> Q"
      then show "\<forall>p. p \<in> P \<longrightarrow> (\<exists>p'. p = p' @ [[Tick]\<^sub>E]) \<or> (\<exists>p' Y. p = p' @ [[Y]\<^sub>R]) \<or>
          (\<forall>q. q \<in> Q \<longrightarrow> (\<forall>X. [[X]\<^sub>R] \<notin> Q \<and> ((\<exists>Y. [[Y]\<^sub>R] \<in> Q) \<or> X \<noteq> UNIV) \<or>
            (\<exists>q' Y. q = [Y]\<^sub>R # q') \<or> \<rho> @ [[x]\<^sub>E] \<noteq> intersect_refusal_trace X p @ q)) \<Longrightarrow>
        \<exists>p X. p @ [[X]\<^sub>R] \<in> P \<and>(\<exists>Y q. ([Y]\<^sub>R # q \<in> Q \<or> (\<forall>Z q'. [Z]\<^sub>R # q' \<notin> Q) \<and> Y = UNIV \<and> q = []) \<and>
          \<rho> @ [[x]\<^sub>E] = intersect_refusal_trace Y (p @ [[X]\<^sub>R]) @ q)"
        using case_assms 
      proof (erule_tac x="p" in allE, auto, erule_tac x="q @ [[x]\<^sub>E]" in allE, auto)
        fix q' Y
        assume "[Y]\<^sub>R # q' \<in> Q"
        then have "[[Y]\<^sub>R] \<in> Q"
          by (meson CT1_Q CT1_def ctt_prefix_subset.simps(1) ctt_prefix_subset.simps(2) subsetI)
        then show "\<forall>Y. [[Y]\<^sub>R] \<notin> Q \<Longrightarrow>
          \<exists>pa X. pa @ [[X]\<^sub>R] \<in> P \<and> (\<exists>Ya q. ([Ya]\<^sub>R # q \<in> Q \<or> (\<forall>Z q'. [Z]\<^sub>R # q' \<notin> Q) \<and> Ya = UNIV \<and> q = []) \<and>
            p @ [Y]\<^sub>R # q' = intersect_refusal_trace Ya (pa @ [[X]\<^sub>R]) @ q)"
          by auto
      next
        show "p \<noteq> intersect_refusal_trace UNIV p \<Longrightarrow>
          \<exists>pa X. pa @ [[X]\<^sub>R] \<in> P \<and> (\<exists>Y qa. ([Y]\<^sub>R # qa \<in> Q \<or> (\<forall>Z q'. [Z]\<^sub>R # q' \<notin> Q) \<and> Y = UNIV \<and> qa = []) \<and>
            p @ q @ [[x]\<^sub>E] = intersect_refusal_trace Y (pa @ [[X]\<^sub>R]) @ qa)"
          by (simp add: intersect_refusal_trace_UNIV_identity)
      qed
    next
      assume "q @ [[X]\<^sub>R, [Tock]\<^sub>E] \<in> Q"
      then show "\<forall>p. p \<in> P \<longrightarrow> (\<exists>p'. p = p' @ [[Tick]\<^sub>E]) \<or> (\<exists>p' Y. p = p' @ [[Y]\<^sub>R]) \<or>
        (\<forall>q. q \<in> Q \<longrightarrow> (\<forall>Xa. [[Xa]\<^sub>R] \<notin> Q \<and> ((\<exists>Y. [[Y]\<^sub>R] \<in> Q) \<or> Xa \<noteq> UNIV) \<or>
          (\<exists>q' Y. q = [Y]\<^sub>R # q') \<or> \<rho> @ [[X]\<^sub>R, [Tock]\<^sub>E] \<noteq> intersect_refusal_trace Xa p @ q)) \<Longrightarrow> False"
        using case_assms 
      proof (erule_tac x="p" in allE, auto, erule_tac x="q @ [[X]\<^sub>R, [Tock]\<^sub>E]" in allE, auto)
        fix q' Y
        assume "[Y]\<^sub>R # q' \<in> Q"
        then have "[[Y]\<^sub>R] \<in> Q"
          by (meson CT1_Q CT1_def ctt_prefix_subset.simps(1) ctt_prefix_subset.simps(2) subsetI)
        then show "\<forall>Y. [[Y]\<^sub>R] \<notin> Q \<Longrightarrow> False"
          by auto
      next
        show "p \<noteq> intersect_refusal_trace UNIV p \<Longrightarrow> False"
          by (simp add: intersect_refusal_trace_UNIV_identity)
      qed
    next
      assume "q @ [[X]\<^sub>R, [Tock]\<^sub>E] \<in> Q"
      then show "\<forall>p. p \<in> P \<longrightarrow> (\<exists>p'. p = p' @ [[Tick]\<^sub>E]) \<or> (\<exists>p' Y. p = p' @ [[Y]\<^sub>R]) \<or>
          (\<forall>q. q \<in> Q \<longrightarrow> (\<forall>Xa. [[Xa]\<^sub>R] \<notin> Q \<and> ((\<exists>Y. [[Y]\<^sub>R] \<in> Q) \<or> Xa \<noteq> UNIV) \<or>
            (\<exists>q' Y. q = [Y]\<^sub>R # q') \<or> \<rho> @ [[X]\<^sub>R, [Tock]\<^sub>E] \<noteq> intersect_refusal_trace Xa p @ q)) \<Longrightarrow> 
        \<exists>p X. p @ [[X]\<^sub>R] \<in> P \<and> (\<exists>Y q. ([Y]\<^sub>R # q \<in> Q \<or> (\<forall>Z q'. [Z]\<^sub>R # q' \<notin> Q) \<and> Y = UNIV \<and> q = []) \<and>
          \<rho> @ [[Tock]\<^sub>E] = intersect_refusal_trace Y (p @ [[X]\<^sub>R]) @ q)"
        using case_assms 
      proof (erule_tac x="p" in allE, auto, erule_tac x="q @ [[X]\<^sub>R, [Tock]\<^sub>E]" in allE, auto)
        fix q' Y
        assume "[Y]\<^sub>R # q' \<in> Q"
        then have "[[Y]\<^sub>R] \<in> Q"
          by (meson CT1_Q CT1_def ctt_prefix_subset.simps(1) ctt_prefix_subset.simps(2) subsetI)
        then show "\<forall>Y. [[Y]\<^sub>R] \<notin> Q \<Longrightarrow> 
          \<exists>pa X. pa @ [[X]\<^sub>R] \<in> P \<and> (\<exists>Y qa. ([Y]\<^sub>R # qa \<in> Q \<or> (\<forall>Z q'. [Z]\<^sub>R # q' \<notin> Q) \<and> Y = UNIV \<and> qa = []) \<and>
            p @ q @ [[Tock]\<^sub>E] = intersect_refusal_trace Y (pa @ [[X]\<^sub>R]) @ qa)"
          by auto
      next
        show "p \<noteq> intersect_refusal_trace UNIV p \<Longrightarrow> 
          \<exists>pa X. pa @ [[X]\<^sub>R] \<in> P \<and> (\<exists>Y qa. ([Y]\<^sub>R # qa \<in> Q \<or> (\<forall>Z q'. [Z]\<^sub>R # q' \<notin> Q) \<and> Y = UNIV \<and> qa = []) \<and>
            p @ q @ [[Tock]\<^sub>E] = intersect_refusal_trace Y (pa @ [[X]\<^sub>R]) @ qa)"
          by (simp add: intersect_refusal_trace_UNIV_identity)
      qed
    qed
    then have "Y \<inter> {e. e \<noteq> Tock \<and> q @ [[e]\<^sub>E] \<in> Q \<or> e = Tock \<and> q @ [[X]\<^sub>R, [e]\<^sub>E] \<in> Q} = {}"
      using assm2 by auto
    then have "q @ [[X \<union> Y]\<^sub>R] \<in> Q"
      using case_assms CT2_Q CT2_def by blast
    then show "p @ q @ [[X \<union> Y]\<^sub>R] \<in> P \<triangle>\<^sub>U Q"
      unfolding UntimedInterruptCTT_def 
    proof auto
      show "q @ [[X \<union> Y]\<^sub>R] \<in> Q \<Longrightarrow>
          \<forall>pa. pa \<in> P \<longrightarrow> (\<exists>p'. pa = p' @ [[Tick]\<^sub>E]) \<or> (\<exists>p' Y. pa = p' @ [[Y]\<^sub>R]) \<or>
            (\<forall>qa. qa \<in> Q \<longrightarrow> (\<forall>Xa. [[Xa]\<^sub>R] \<notin> Q \<and> ((\<exists>Y. [[Y]\<^sub>R] \<in> Q) \<or> Xa \<noteq> UNIV) \<or>
              (\<exists>q' Y. qa = [Y]\<^sub>R # q') \<or> p @ q @ [[X \<union> Y]\<^sub>R] \<noteq> intersect_refusal_trace Xa pa @ qa)) \<Longrightarrow>
        \<exists>pa Xa. pa @ [[Xa]\<^sub>R] \<in> P \<and> (\<exists>Ya qa. ([Ya]\<^sub>R # qa \<in> Q \<or> (\<forall>Z q'. [Z]\<^sub>R # q' \<notin> Q) \<and> Ya = UNIV \<and> qa = []) \<and>
          p @ q @ [[X \<union> Y]\<^sub>R] = intersect_refusal_trace Ya (pa @ [[Xa]\<^sub>R]) @ qa)"
        using case_assms 
      proof (erule_tac x="p" in allE, auto, erule_tac x="q @ [[X \<union> Y]\<^sub>R]" in allE, auto)
        fix q' Ya
        assume "[Ya]\<^sub>R # q' \<in> Q"
        then have "[[Ya]\<^sub>R] \<in> Q"
          by (meson CT1_Q CT1_def ctt_prefix_subset.simps(1) ctt_prefix_subset.simps(2) subsetI)
        then show "\<forall>Y. [[Y]\<^sub>R] \<notin> Q \<Longrightarrow>
          \<exists>pa Xa. pa @ [[Xa]\<^sub>R] \<in> P \<and> (\<exists>Yaa qa. ([Yaa]\<^sub>R # qa \<in> Q \<or> (\<forall>Z q'. [Z]\<^sub>R # q' \<notin> Q) \<and> Yaa = UNIV \<and> qa = []) \<and>
            p @ [Ya]\<^sub>R # q' = intersect_refusal_trace Yaa (pa @ [[Xa]\<^sub>R]) @ qa)"
          by auto
      next
        show "p \<noteq> intersect_refusal_trace UNIV p \<Longrightarrow>
          \<exists>pa Xa. pa @ [[Xa]\<^sub>R] \<in> P \<and> (\<exists>Ya qa. ([Ya]\<^sub>R # qa \<in> Q \<or> (\<forall>Z q'. [Z]\<^sub>R # q' \<notin> Q) \<and> Ya = UNIV \<and> qa = []) \<and>
            p @ q @ [[X \<union> Y]\<^sub>R] = intersect_refusal_trace Ya (pa @ [[Xa]\<^sub>R]) @ qa)"
          by (simp add: intersect_refusal_trace_UNIV_identity)
      qed
    qed
  qed
qed

lemma CT3_trace_intersect_refusal_trace:
  "CT3_trace t \<Longrightarrow> CT3_trace (intersect_refusal_trace X t)"
  by (induct t rule:CT3_trace.induct, auto, case_tac x, auto, case_tac vb, auto)

lemma CT3_UntimedInterrupt:
  assumes Q_wf: "\<forall>q\<in>Q. cttWF q"
  assumes CT1_P: "CT1 P" and CT1_Q: "CT1 Q"
  assumes CT3_P: "CT3 P" and CT3_Q: "CT3 Q"
  shows "CT3 (P \<triangle>\<^sub>U Q)"
  unfolding UntimedInterruptCTT_def CT3_def 
proof auto
  fix p X
  show "p @ [[Tick]\<^sub>E] \<in> P \<Longrightarrow> CT3_trace (intersect_refusal_trace X (p @ [[Tick]\<^sub>E]))"
    using CT3_def CT3_trace_intersect_refusal_trace CT3_P by auto
next
  fix p X
  show "p @ [[Tick]\<^sub>E] \<in> P \<Longrightarrow> CT3_trace (intersect_refusal_trace UNIV (p @ [[Tick]\<^sub>E]))"
    by (metis CT3_def CT3_P intersect_refusal_trace_UNIV_identity)
next
  fix p q X Y
  assume case_assms: "[Y]\<^sub>R # q \<in> Q" "p @ [[X]\<^sub>R] \<in> P"
  have "intersect_refusal_trace Y (p @ [[X]\<^sub>R]) @ q = intersect_refusal_trace Y p @ intersect_refusal_trace Y [[X]\<^sub>R] @ q"
    by (induct p rule:intersect_refusal_trace.induct, auto)
  then have 1: "intersect_refusal_trace Y (p @ [[X]\<^sub>R]) @ q = intersect_refusal_trace Y p @ [X \<inter> Y]\<^sub>R # q"
    by auto
  then have "[X \<inter> Y]\<^sub>R # q \<in> Q"
    by (metis CT1_Q CT1_def Int_commute Int_left_absorb case_assms(1) ctt_prefix_subset.simps(2) ctt_prefix_subset_refl inf.absorb_iff2)
  then have 2: "cttWF ([X \<inter> Y]\<^sub>R # q) \<and> CT3_trace ([X \<inter> Y]\<^sub>R # q)"
    using CT3_Q CT3_def Q_wf by blast
  have 3: "CT3_trace p"
    by (meson CT3_P CT3_def CT3_trace_cons_left case_assms(2))
  show "CT3_trace (intersect_refusal_trace Y (p @ [[X]\<^sub>R]) @ q)"
    by (simp add: "1" "2" "3" CT3_append CT3_trace_intersect_refusal_trace)
next
  fix p X
  show "p @ [[X]\<^sub>R] \<in> P \<Longrightarrow> CT3_trace (intersect_refusal_trace UNIV (p @ [[X]\<^sub>R]))"
    by (metis CT3_P CT3_def intersect_refusal_trace_UNIV_identity)
next
  fix p q X
  show "p \<in> P \<Longrightarrow> q \<in> Q \<Longrightarrow> CT3_trace (intersect_refusal_trace X p @ q)"
    by (meson CT3_P CT3_Q CT3_append CT3_def CT3_trace_intersect_refusal_trace Q_wf)
next
  fix p q
  show "p \<in> P \<Longrightarrow> q \<in> Q \<Longrightarrow> CT3_trace (intersect_refusal_trace UNIV p @ q)"
    by (meson CT3_P CT3_Q CT3_append CT3_def CT3_trace_intersect_refusal_trace Q_wf)
qed

lemma CT_UntimedInterrupt:
  assumes "CT P" "CT Q"
  shows "CT (P \<triangle>\<^sub>U Q)"
  using assms unfolding CT_def apply auto
  using UntimedInterruptCTT_wf apply blast
  using CT0_UntimedInterrupt apply blast
  using CT1_UntimedInterrupt apply blast
  using CT2_UntimedInterrupt apply blast
  using CT3_UntimedInterrupt apply blast
  done

end