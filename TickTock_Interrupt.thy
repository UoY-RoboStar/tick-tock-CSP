theory TickTock_Interrupt
  imports TickTock_Core
begin

subsection {* Untimed Interrupt *}

fun intersect_refusal_trace :: "'e cttevent set \<Rightarrow> 'e cttobs list \<Rightarrow> 'e cttobs list" where
  "intersect_refusal_trace X [] = []" |
  "intersect_refusal_trace X ([e]\<^sub>E # s) = [e]\<^sub>E # intersect_refusal_trace X s" |
  "intersect_refusal_trace X ([Y]\<^sub>R # s) = [X \<inter> Y]\<^sub>R # intersect_refusal_trace X s"

lemma intersect_refusal_trace_wf:
  "ttWF t \<Longrightarrow> ttWF (intersect_refusal_trace X t)"
  by (induct t rule:ttWF.induct, auto)

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
  "ttWF (t @ s) \<Longrightarrow> ttWF (intersect_refusal_trace X t @ s)"
  using ctt_prefix_subset_ttWF intersect_refusal_trace_append_prefix_subset by blast

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

lemma intersect_refusal_trace_refusal_subset: "\<rho> @ [X]\<^sub>R # \<sigma> = intersect_refusal_trace Y t \<Longrightarrow> X \<subseteq> Y"
  by (induct \<rho> t rule:ctt_subset.induct, auto, case_tac v, auto)

lemma subset_intersect_refusal_trace_idempotent:
  "Y \<subseteq> Z \<Longrightarrow> intersect_refusal_trace Y t = intersect_refusal_trace Z (intersect_refusal_trace Y t)"
  by (induct t rule:intersect_refusal_trace.induct, auto)

lemma intersect_refusal_trace_refusal_subset_idempotent:
  "\<rho> @ [X]\<^sub>R # \<sigma> = intersect_refusal_trace Y t \<Longrightarrow> \<rho> @ [X \<union> Z]\<^sub>R # \<sigma> = intersect_refusal_trace (Y \<union> Z) (\<rho> @ [X \<union> Z]\<^sub>R # \<sigma>)"
  by (induct \<rho> t rule:ctt_subset.induct, auto, case_tac v, auto, case_tac v, auto simp add: subset_intersect_refusal_trace_idempotent)

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

lemma intersect_refusal_trace_idempotent_widen_refusal:
  "s = intersect_refusal_trace X s \<Longrightarrow> s = intersect_refusal_trace (X \<union> Y) s"
  by (induct s, auto, case_tac a, auto)

lemma intersect_refusal_trace_concat:
  "s = intersect_refusal_trace X s' \<Longrightarrow> t = intersect_refusal_trace X t' \<Longrightarrow> s @ t = intersect_refusal_trace X (s' @ t') "
  by (induct s s' rule:ctt_subset.induct, auto, case_tac v, auto)

fun contains_refusal :: "'e cttobs list \<Rightarrow> bool" where
  "contains_refusal [] = False" |
  "contains_refusal ([X]\<^sub>R # s) = True" |
  "contains_refusal ([e]\<^sub>E # s) = contains_refusal s"

lemma not_contains_refusal_ctt_prefix_subset:
  "\<not> contains_refusal t \<Longrightarrow> s \<lesssim>\<^sub>C t \<Longrightarrow> \<not> contains_refusal s"
  by (induct s t rule:ctt_prefix_subset.induct, auto)

lemma not_contains_refusal_ctt_prefix_subset_end_nonref:
  "\<not> contains_refusal t \<Longrightarrow> s \<lesssim>\<^sub>C t \<Longrightarrow> \<nexists> s' X. s = s' @ [[X]\<^sub>R]"
  by (induct s t rule:ctt_prefix_subset.induct, auto simp add: Cons_eq_append_conv)

lemma not_contains_refusal_intersect_refusal_trace:
  "\<not> contains_refusal t \<Longrightarrow> intersect_refusal_trace X t = t"
  by (induct t rule:contains_refusal.induct, auto)

lemma not_contains_refusal_append_event:
  "\<not> contains_refusal t \<Longrightarrow> \<not> contains_refusal (t @ [[e]\<^sub>E])"
  by (induct t rule:contains_refusal.induct, auto)

lemma contains_refusal_ctt_subset:
  "contains_refusal t \<Longrightarrow> s \<subseteq>\<^sub>C t \<Longrightarrow> contains_refusal s"
  by (induct s t rule:ctt_subset.induct, auto)

lemma not_contains_refusal_ctt_subset:
  "\<not> contains_refusal t \<Longrightarrow> s \<subseteq>\<^sub>C t \<Longrightarrow> \<not> contains_refusal s"
  by (induct s t rule:ctt_subset.induct, auto)

definition UntimedInterruptTTT :: "'e cttobs list set \<Rightarrow> 'e cttobs list set \<Rightarrow> 'e cttobs list set" (infixl "\<triangle>\<^sub>U" 58) where
  "P \<triangle>\<^sub>U Q = {t. \<exists> p X. p @ [[Tick]\<^sub>E] \<in> P \<and> contains_refusal p (* if something in P ends in tick and contains a refusal...*)
      \<and> [[X]\<^sub>R] \<in> Q \<and> t = intersect_refusal_trace X (p @ [[Tick]\<^sub>E])} (* ...then we require a refusal in Q and intersect refusals *)
    \<union> {t. \<exists> p. p @ [[Tick]\<^sub>E] \<in> P \<and> \<not> contains_refusal p (* if something in P ends in tick and does not contain a refusal...*)
      \<and> t = p @ [[Tick]\<^sub>E]} (* ...then we just keep the trace, nothing to intersect *)
    \<union> {t. \<exists> p X Y q. p @ [[X]\<^sub>R] \<in> P (* if something in P ends in a refusal...*)
      \<and> [Y]\<^sub>R # q \<in> Q (* ...we require something in Q that starts in a refusal... *)
      \<and> t = intersect_refusal_trace Y (p @ [[X]\<^sub>R]) @ q} (* ... and we append the traces, intersecting the refusals *)
    \<union> {t. \<exists> p q X. p \<in> P \<and> (\<nexists> p'. p = p' @ [[Tick]\<^sub>E]) \<and> (\<nexists> p' Y. p = p' @ [[Y]\<^sub>R]) (* for everything in P that doesn't end in tick or a refusal... *)
    \<and> contains_refusal p (* ...but does contain a refusal... *)
    \<and> [[X]\<^sub>R] \<in> Q (*...then we require a refusal in Q... *)
    \<and> q \<in> Q \<and> (\<nexists> q' Y. q = [Y]\<^sub>R # q') (* ...and some trace in Q which doesn't start with a refusal... *)
    \<and> t = intersect_refusal_trace X p @ q} (* ...and we append the traces, intersecting any refusals *)
    \<union> {t. \<exists> p q. p \<in> P \<and> (\<nexists> p'. p = p' @ [[Tick]\<^sub>E]) \<and> (\<nexists> p' Y. p = p' @ [[Y]\<^sub>R]) (* for everything in P that doesn't end in tick or a refusal... *)
    \<and> \<not> contains_refusal p (* ...and does not contain a refusal... *)
    \<and> q \<in> Q \<and> (\<nexists> q' Y. q = [Y]\<^sub>R # q') (* ...then we require some trace in Q which doesn't start with a refusal... *)
    \<and> t = p @ q} (* ...and we append the traces *)"

lemma event_append_wf:
  "\<And>q. \<exists> p' e. p = p' @ [[Event e]\<^sub>E] \<Longrightarrow> ttWF (p) \<Longrightarrow> ttWF (q) \<Longrightarrow> ttWF (p @ q)"
proof (auto, induct p rule:ttWF.induct, auto)
  fix q p' \<sigma> :: "'a cttobs list"
  fix e ea
  assume assm1: "\<And>q p' e. ttWF (p' @ [[Event e]\<^sub>E]) \<Longrightarrow> ttWF q \<Longrightarrow> \<sigma> = p' @ [[Event e]\<^sub>E] \<Longrightarrow> ttWF (p' @ [Event e]\<^sub>E # q)"
  assume assm2: "ttWF q"
  assume assm3: "ttWF (p' @ [[Event ea]\<^sub>E])" "[Event e]\<^sub>E # \<sigma> = p' @ [[Event ea]\<^sub>E]"
  then have "p' = [] \<or> (\<exists> p''. p' = [Event e]\<^sub>E # p'' \<and> \<sigma> = p'' @ [[Event ea]\<^sub>E])"
    by (cases p' rule:ttWF.cases, auto)
  then show "ttWF (p' @ [Event ea]\<^sub>E # q)"
    using assm2
  proof auto
    fix p''
    assume case_assm1: "\<sigma> = p'' @ [[Event ea]\<^sub>E]"
    assume case_assm2: "p' = [Event e]\<^sub>E # p''"
    have "ttWF (p'' @ [[Event ea]\<^sub>E])"
      using assm3 case_assm1 by auto
    then show "ttWF (p'' @ [Event ea]\<^sub>E # q)"
      using assm1 assm2 case_assm1 by simp
  qed
next
  fix q p' \<sigma> :: "'a cttobs list"
  fix ea X
  assume assm1: "\<And>q p' e. ttWF (p' @ [[Event e]\<^sub>E]) \<Longrightarrow> ttWF q \<Longrightarrow> \<sigma> = p' @ [[Event e]\<^sub>E] \<Longrightarrow> ttWF (p' @ [Event e]\<^sub>E # q)"
  assume assm2: "ttWF q"
  assume assm3: "ttWF (p' @ [[Event ea]\<^sub>E])" "[X]\<^sub>R # [Tock]\<^sub>E # \<sigma> = p' @ [[Event ea]\<^sub>E]"
  then have "p' = [] \<or> (\<exists> p''. p' = [X]\<^sub>R # [Tock]\<^sub>E # p'' \<and> \<sigma> = p'' @ [[Event ea]\<^sub>E])"
    by (cases p' rule:ttWF.cases, auto)
  then show "ttWF (p' @ [Event ea]\<^sub>E # q)"
    using assm2
  proof auto
    fix p''
    assume case_assm1: "\<sigma> = p'' @ [[Event ea]\<^sub>E]"
    assume case_assm2: "p' = [X]\<^sub>R # [Tock]\<^sub>E # p''"
    have "ttWF (p'' @ [[Event ea]\<^sub>E])"
      using assm3 case_assm1 by auto
    then show "ttWF (p'' @ [Event ea]\<^sub>E # q)"
      using assm1 assm2 case_assm1 by simp
  qed
next
  fix va q p' e
  assume "[Tock]\<^sub>E # va = p' @ [[Event e]\<^sub>E]"
  then obtain vb where "p' = [Tock]\<^sub>E # vb"
    by (cases p' rule:ttWF.cases, auto)
  also assume "ttWF (p' @ [[Event e]\<^sub>E])"
  then show "ttWF (p' @ [Event e]\<^sub>E # q)"
    using calculation by auto
next
  fix va q p' e
  assume "[Tock]\<^sub>E # va = p' @ [[Event e]\<^sub>E]"
  then obtain vb where "p' = [Tock]\<^sub>E # vb"
    by (cases p' rule:ttWF.cases, auto)
  also assume "ttWF (p' @ [[Event e]\<^sub>E])"
  then show "ttWF (p' @ [Event e]\<^sub>E # q)"
    using calculation by auto
next
  fix va q p' e
  assume "[Tock]\<^sub>E # va = p' @ [[Event e]\<^sub>E]"
  then obtain vb where "p' = [Tock]\<^sub>E # vb"
    by (cases p' rule:ttWF.cases, auto)
  also assume "ttWF (p' @ [[Event e]\<^sub>E])"
  then show "ttWF (p' @ [Event e]\<^sub>E # q)"
    using calculation by auto
next
  fix v vc q p' e
  assume "[Tick]\<^sub>E # v # vc = p' @ [[Event e]\<^sub>E]"
  then obtain vb where "p' = [Tick]\<^sub>E # vb"
    by (cases p' rule:ttWF.cases, auto)
  also assume "ttWF (p' @ [[Event e]\<^sub>E])"
  then show "ttWF (p' @ [Event e]\<^sub>E # q)"
    using calculation by (auto, cases vb, auto)
next
  fix v vc q p' e
  assume "[Tick]\<^sub>E # v # vc = p' @ [[Event e]\<^sub>E]"
  then obtain vb where "p' = [Tick]\<^sub>E # vb"
    by (cases p' rule:ttWF.cases, auto)
  also assume "ttWF (p' @ [[Event e]\<^sub>E])"
  then show "ttWF (p' @ [Event e]\<^sub>E # q)"
    using calculation by (auto, cases vb, auto)
next
  fix va vd vc q p' e
  assume "[va]\<^sub>R # [Event vd]\<^sub>E # vc = p' @ [[Event e]\<^sub>E]"
  then obtain vb where "p' = [va]\<^sub>R # [Event vd]\<^sub>E # vb \<or> p' = [[va]\<^sub>R]"
    by (cases p' rule:ttWF.cases, auto)
  also assume "ttWF (p' @ [[Event e]\<^sub>E])"
  then show "ttWF (p' @ [Event e]\<^sub>E # q)"
    using calculation by (auto)
next
  fix va vd vc q p' e
  assume "[va]\<^sub>R # [Tick]\<^sub>E # vc = p' @ [[Event e]\<^sub>E]"
  then obtain vb where "p' = [va]\<^sub>R # [Tick]\<^sub>E # vb \<or> p' = [[va]\<^sub>R]"
    by (cases p' rule:ttWF.cases, auto)
  also assume "ttWF (p' @ [[Event e]\<^sub>E])"
  then show "ttWF (p' @ [Event e]\<^sub>E # q)"
    using calculation by (auto)
next
  fix va v vc q p' e
  assume "[va]\<^sub>R # [v]\<^sub>R # vc = p' @ [[Event e]\<^sub>E]"
  then obtain vb where "p' = [va]\<^sub>R # [v]\<^sub>R # vb \<or> p' = [[va]\<^sub>R]"
    by (cases p' rule:ttWF.cases, auto)
  also assume "ttWF (p' @ [[Event e]\<^sub>E])"
  then show "ttWF (p' @ [Event e]\<^sub>E # q)"
    using calculation by (auto)
qed
  

lemma refusal_tock_append_wf:
  "\<And>q. \<exists> p' X. p = p' @ [[X]\<^sub>R, [Tock]\<^sub>E] \<Longrightarrow> ttWF (p) \<Longrightarrow> ttWF (q) \<Longrightarrow> ttWF (p @ q)"
proof (auto, induct p rule:ttWF.induct, auto)
  fix q p' \<sigma> :: "'a cttobs list"
  fix e X
  assume assm1: "\<And>q p' X. ttWF (p' @ [[X]\<^sub>R, [Tock]\<^sub>E]) \<Longrightarrow> ttWF q \<Longrightarrow> \<sigma> = p' @ [[X]\<^sub>R, [Tock]\<^sub>E] \<Longrightarrow> ttWF (p' @ [X]\<^sub>R # [Tock]\<^sub>E # q)"
  assume assm2: "ttWF q"
  assume assm3: "ttWF (p' @ [[X]\<^sub>R, [Tock]\<^sub>E])" "[Event e]\<^sub>E # \<sigma> = p' @ [[X]\<^sub>R, [Tock]\<^sub>E]"
  then have "p' = [] \<or> (\<exists> p''. p' = [Event e]\<^sub>E # p'' \<and> \<sigma> = p'' @ [[X]\<^sub>R, [Tock]\<^sub>E])"
    by (cases p' rule:ttWF.cases, auto)
  then show "ttWF (p' @ [X]\<^sub>R # [Tock]\<^sub>E # q)"
    using assm2
  proof auto
    fix p''
    assume case_assm1: "\<sigma> = p'' @ [[X]\<^sub>R, [Tock]\<^sub>E]"
    assume case_assm2: "p' = [Event e]\<^sub>E # p''"
    have "ttWF (p'' @ [[X]\<^sub>R, [Tock]\<^sub>E])"
      using assm3 case_assm1 by auto
    then show "ttWF (p'' @ [X]\<^sub>R # [Tock]\<^sub>E # q)"
      using assm1 assm2 case_assm1 by simp
  qed
next
  fix q p' \<sigma> :: "'a cttobs list"
  fix X Xa
  assume assm1: "\<And>q p' X. ttWF (p' @ [[X]\<^sub>R, [Tock]\<^sub>E]) \<Longrightarrow> ttWF q \<Longrightarrow> \<sigma> = p' @ [[X]\<^sub>R, [Tock]\<^sub>E] \<Longrightarrow> ttWF (p' @ [X]\<^sub>R # [Tock]\<^sub>E # q)"
  assume assm2: "ttWF q"
  assume assm3: "ttWF (p' @ [[Xa]\<^sub>R, [Tock]\<^sub>E])" "[X]\<^sub>R # [Tock]\<^sub>E # \<sigma> = p' @ [[Xa]\<^sub>R, [Tock]\<^sub>E] "
  then have "p' = [] \<or> (\<exists> p''. p' = [X]\<^sub>R # [Tock]\<^sub>E # p'' \<and> \<sigma> = p'' @ [[Xa]\<^sub>R, [Tock]\<^sub>E])"
    by (cases p' rule:ttWF.cases, auto)
  then show "ttWF (p' @ [Xa]\<^sub>R # [Tock]\<^sub>E # q)"
    using assm2
  proof auto
    fix p''
    assume case_assm1: "\<sigma> = p'' @ [[Xa]\<^sub>R, [Tock]\<^sub>E]"
    assume case_assm2: "p' = [X]\<^sub>R # [Tock]\<^sub>E # p''"
    have "ttWF (p'' @ [[Xa]\<^sub>R, [Tock]\<^sub>E])"
      using assm3 case_assm1 by auto
    then show "ttWF (p'' @ [Xa]\<^sub>R # [Tock]\<^sub>E # q)"
      using assm1 assm2 case_assm1 by simp
  qed
next
  fix va q p' X
  assume "[Tock]\<^sub>E # va = p' @ [[X]\<^sub>R, [Tock]\<^sub>E]"
  then obtain vb where "p' = [Tock]\<^sub>E # vb"
    by (cases p' rule:ttWF.cases, auto)
  also assume "ttWF (p' @ [[X]\<^sub>R, [Tock]\<^sub>E])"
  then show "ttWF (p' @ [X]\<^sub>R # [Tock]\<^sub>E # q)"
    using calculation by auto
next
  fix va q p' X
  assume "[Tock]\<^sub>E # va = p' @ [[X]\<^sub>R, [Tock]\<^sub>E]"
  then obtain vb where "p' = [Tock]\<^sub>E # vb"
    by (cases p' rule:ttWF.cases, auto)
  also assume "ttWF (p' @ [[X]\<^sub>R, [Tock]\<^sub>E])"
  then show "ttWF (p' @ [X]\<^sub>R # [Tock]\<^sub>E # q)"
    using calculation by auto
next
  fix va q p' X
  assume "[Tock]\<^sub>E # va = p' @ [[X]\<^sub>R, [Tock]\<^sub>E]"
  then obtain vb where "p' = [Tock]\<^sub>E # vb"
    by (cases p' rule:ttWF.cases, auto)
  also assume "ttWF (p' @ [[X]\<^sub>R, [Tock]\<^sub>E])"
  then show "ttWF (p' @ [X]\<^sub>R # [Tock]\<^sub>E # q)"
    using calculation by auto
next
  fix v vc q p' X
  assume "[Tick]\<^sub>E # v # vc = p' @ [[X]\<^sub>R, [Tock]\<^sub>E]"
  then obtain vb where "p' = [Tick]\<^sub>E # vb"
    by (cases p' rule:ttWF.cases, auto)
  also assume "ttWF (p' @ [[X]\<^sub>R, [Tock]\<^sub>E])"
  then show "ttWF (p' @ [X]\<^sub>R # [Tock]\<^sub>E # q)"
    using calculation by (auto, cases vb, auto)
next
  fix v vc q p' X
  assume "[Tick]\<^sub>E # v # vc = p' @ [[X]\<^sub>R, [Tock]\<^sub>E]"
  then obtain vb where "p' = [Tick]\<^sub>E # vb"
    by (cases p' rule:ttWF.cases, auto)
  also assume "ttWF (p' @ [[X]\<^sub>R, [Tock]\<^sub>E])"
  then show "ttWF (p' @ [X]\<^sub>R # [Tock]\<^sub>E # q)"
    using calculation by (auto, cases vb, auto)
next
  fix va vd vc q p' X
  assume "[va]\<^sub>R # [Event vd]\<^sub>E # vc = p' @ [[X]\<^sub>R, [Tock]\<^sub>E]"
  then obtain vb where "p' = [va]\<^sub>R # [Event vd]\<^sub>E # vb \<or> p' = [[va]\<^sub>R]"
    by (cases p' rule:ttWF.cases, auto)
  also assume "ttWF (p' @ [[X]\<^sub>R, [Tock]\<^sub>E])"
  then show "ttWF (p' @ [X]\<^sub>R # [Tock]\<^sub>E # q)"
    using calculation by (auto)
next
  fix va vc q p' X
  assume "[va]\<^sub>R # [Tick]\<^sub>E # vc = p' @ [[X]\<^sub>R, [Tock]\<^sub>E]"
  then obtain vb where "p' = [va]\<^sub>R # [Tick]\<^sub>E # vb \<or> p' = [[va]\<^sub>R]"
    by (cases p' rule:ttWF.cases, auto)
  also assume "ttWF (p' @ [[X]\<^sub>R, [Tock]\<^sub>E])"
  then show "ttWF (p' @ [X]\<^sub>R # [Tock]\<^sub>E # q)"
    using calculation by (auto)
next
  fix va v vc q p' X
  assume "[va]\<^sub>R # [v]\<^sub>R # vc = p' @ [[X]\<^sub>R, [Tock]\<^sub>E]"
  then obtain vb where "p' = [va]\<^sub>R # [v]\<^sub>R # vb \<or> p' = [[va]\<^sub>R]"
    by (cases p' rule:ttWF.cases, auto)
  also assume "ttWF (p' @ [[X]\<^sub>R, [Tock]\<^sub>E])"
  then show "ttWF (p' @ [X]\<^sub>R # [Tock]\<^sub>E # q)"
    using calculation by (auto)
qed

lemma tock_append_wf:
  "\<exists> p' X. p = p' @ [[Tock]\<^sub>E] \<Longrightarrow> ttWF (p) \<Longrightarrow> ttWF (q) \<Longrightarrow> ttWF (p @ q)"
proof auto
  fix p'
  assume "ttWF (p' @ [[Tock]\<^sub>E])" "p = p' @ [[Tock]\<^sub>E]"
  also have "\<And> p. ttWF (p' @ [[Tock]\<^sub>E]) \<Longrightarrow> p = p' @ [[Tock]\<^sub>E] \<Longrightarrow> \<exists> X p''. p = p'' @ [[X]\<^sub>R, [Tock]\<^sub>E]"
    by (induct p' rule:ttWF.induct, auto, fastforce+)
  then have "\<exists> p'' X. p = p'' @ [[X]\<^sub>R, [Tock]\<^sub>E]"
    using calculation by fastforce
  then show "ttWF (p' @ [[Tock]\<^sub>E]) \<Longrightarrow> ttWF q \<Longrightarrow> p = p' @ [[Tock]\<^sub>E] \<Longrightarrow> ttWF (p' @ [Tock]\<^sub>E # q)"
    using refusal_tock_append_wf by fastforce
qed

lemma end_refusal_start_refusal_append_wf:
  "ttWF (p @ [[X]\<^sub>R]) \<Longrightarrow> ttWF ([Y]\<^sub>R # q) \<Longrightarrow> ttWF ((p @ [[Z]\<^sub>R]) @ q)"
  by (induct p rule:ttWF.induct, auto, induct q rule:ttWF.induct, auto)

lemma nontick_event_end_append_wf:
  assumes "ttWF p" "ttWF q"
  assumes "\<forall>p'. p \<noteq> p' @ [[Tick]\<^sub>E]" "\<forall>p' Y. p \<noteq> p' @ [[Y]\<^sub>R]"
  shows "ttWF (p @ q)"
proof -
  have "p = [] \<or> (\<exists> p' x. p = p' @ [x])"
    by (induct p, auto)
  then have "p = [] \<or> (\<exists> p' e. p = p' @ [[Event e]\<^sub>E]) \<or> (\<exists> p' X. p = p' @ [[Tock]\<^sub>E])"
    using assms(3) assms(4) by (auto, (case_tac x, auto, case_tac x1, auto)+)
  then show ?thesis
    using assms(1) assms(2) event_append_wf tock_append_wf by (auto, fastforce+)
qed
    
lemma UntimedInterruptTTT_wf:
  assumes "\<forall>x\<in>P. ttWF x" "\<forall>x\<in>Q. ttWF x"
  shows "\<forall>x\<in>(P \<triangle>\<^sub>U Q). ttWF x"
  using assms unfolding UntimedInterruptTTT_def
proof auto
  fix p X
  assume "\<forall>x\<in>P. ttWF x" "\<forall>x\<in>Q. ttWF x" "p @ [[Tick]\<^sub>E] \<in> P" "[[X]\<^sub>R] \<in> Q"
  then show "ttWF (intersect_refusal_trace X (p @ [[Tick]\<^sub>E]))"
    using intersect_refusal_trace_wf by (blast)
next
  fix p X Y q
  assume "\<forall>x\<in>P. ttWF x" "\<forall>x\<in>Q. ttWF x" "p @ [[X]\<^sub>R] \<in> P" "[Y]\<^sub>R # q \<in> Q"
  then show "ttWF (intersect_refusal_trace Y (p @ [[X]\<^sub>R]) @ q)"
    using end_refusal_start_refusal_append_wf intersect_refusal_trace_append_wf by (blast)
next
  fix p q X
  assume "\<forall>x\<in>P. ttWF x" "\<forall>x\<in>Q. ttWF x" "p \<in> P" "\<forall>p'. p \<noteq> p' @ [[Tick]\<^sub>E]" "\<forall>p' Y. p \<noteq> p' @ [[Y]\<^sub>R]" "q \<in> Q"
  then also have "ttWF (p @ q)"
    using nontick_event_end_append_wf by blast
  then show "ttWF (intersect_refusal_trace X p @ q)"
    using intersect_refusal_trace_append_wf by blast
next
  fix p q
  assume "\<forall>x\<in>P. ttWF x" "\<forall>x\<in>Q. ttWF x" "p \<in> P" "\<forall>p'. p \<noteq> p' @ [[Tick]\<^sub>E]" "\<forall>p' Y. p \<noteq> p' @ [[Y]\<^sub>R]" "q \<in> Q"
  then show "ttWF (p @ q)"
    using nontick_event_end_append_wf by blast
qed

lemma TT0_UntimedInterrupt:
  assumes "TT0 P" "TT1 P" "TT0 Q" "TT1 Q"
  shows "TT0 (P \<triangle>\<^sub>U Q)"
  unfolding UntimedInterruptTTT_def TT0_def
proof auto
  have empty_in_P_Q: "[] \<in> P" "[] \<in> Q"
    by (simp_all add: TT0_TT1_empty assms)
  assume "\<forall>x p. p \<in> P \<longrightarrow> (\<exists>p'. p = p' @ [[Tick]\<^sub>E]) \<or> (\<exists>p' Y. p = p' @ [[Y]\<^sub>R]) \<or> contains_refusal p
    \<or> (\<forall>q. q \<in> Q \<longrightarrow> (\<exists>q' Y. q = [Y]\<^sub>R # q') \<or> x \<noteq> p @ q)"
  then have "False"
    using empty_in_P_Q by (erule_tac x="[]" in allE, auto)
  then show "\<exists>x p. contains_refusal p \<and>
          p \<in> P \<and>
          (\<forall>p'. p \<noteq> p' @ [[Tick]\<^sub>E]) \<and>
          (\<forall>p' Y. p \<noteq> p' @ [[Y]\<^sub>R]) \<and> (\<exists>q. q \<in> Q \<and> (\<exists>X. [[X]\<^sub>R] \<in> Q \<and> (\<forall>q' Y. q \<noteq> [Y]\<^sub>R # q') \<and> x = intersect_refusal_trace X p @ q))"
    by auto
qed

lemma TT1_UntimedInterrupt:
  assumes P_wf: "\<forall>x\<in>P. ttWF x"
  assumes TT1_P: "TT1 P" and TT0_Q: "TT0 Q" and TT1_Q: "TT1 Q"
  shows "TT1 (P \<triangle>\<^sub>U Q)"
  unfolding TT1_def
proof (auto)
  fix \<rho> \<sigma>
  assume "\<sigma> \<in> P \<triangle>\<^sub>U Q"
  thm UntimedInterruptTTT_def[where P=P, where Q=Q]
  then have "(\<exists>p X. p @ [[Tick]\<^sub>E] \<in> P \<and> contains_refusal p \<and> [[X]\<^sub>R] \<in> Q \<and> \<sigma> = intersect_refusal_trace X (p @ [[Tick]\<^sub>E]))
      \<or> (\<exists>p. p @ [[Tick]\<^sub>E] \<in> P \<and> \<not> contains_refusal p \<and> \<sigma> = p @ [[Tick]\<^sub>E])
      \<or> (\<exists>p X Y q. p @ [[X]\<^sub>R] \<in> P \<and> [Y]\<^sub>R # q \<in> Q \<and> \<sigma> = intersect_refusal_trace Y (p @ [[X]\<^sub>R]) @ q)
      \<or> (\<exists>p q X. p \<in> P \<and> (\<nexists>p'. p = p' @ [[Tick]\<^sub>E]) \<and> (\<nexists>p' Y. p = p' @ [[Y]\<^sub>R]) \<and>
            contains_refusal p \<and> [[X]\<^sub>R] \<in> Q \<and> q \<in> Q \<and> (\<nexists>q' Y. q = [Y]\<^sub>R # q') \<and> \<sigma> = intersect_refusal_trace X p @ q)
      \<or> (\<exists>p q. p \<in> P \<and> (\<nexists>p'. p = p' @ [[Tick]\<^sub>E]) \<and> (\<nexists>p' Y. p = p' @ [[Y]\<^sub>R]) \<and> 
            \<not> contains_refusal p \<and> q \<in> Q \<and> (\<nexists>q' Y. q = [Y]\<^sub>R # q') \<and> \<sigma> = p @ q)"
    unfolding UntimedInterruptTTT_def by safe
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
      using p'_assms TT1_P in_P unfolding TT1_def by auto
    assume Q_assm: "[[X]\<^sub>R] \<in> Q" 
    show "\<rho> \<in> P \<triangle>\<^sub>U Q"
      using p'_cases p'_in_P Q_assm p'_assms unfolding UntimedInterruptTTT_def
    proof auto
      fix p''
      assume case_assms: "p'' @ [[Tick]\<^sub>E] \<in> P" "[[X]\<^sub>R] \<in> Q" 
      then show "\<forall>p. contains_refusal p \<longrightarrow> p @ [[Tick]\<^sub>E] \<in> P \<longrightarrow>
          (\<forall>Xa. [[Xa]\<^sub>R] \<in> Q \<longrightarrow> intersect_refusal_trace X (p'' @ [[Tick]\<^sub>E]) \<noteq> intersect_refusal_trace Xa (p @ [[Tick]\<^sub>E])) \<Longrightarrow>
        \<forall>p. p @ [[Tick]\<^sub>E] \<in> P \<longrightarrow> contains_refusal p \<or> intersect_refusal_trace X (p'' @ [[Tick]\<^sub>E]) \<noteq> p @ [[Tick]\<^sub>E] \<Longrightarrow>
        \<exists>p. p \<in> P \<and> (\<forall>p'. p \<noteq> p' @ [[Tick]\<^sub>E]) \<and> (\<forall>p' Y. p \<noteq> p' @ [[Y]\<^sub>R]) \<and> contains_refusal p \<and>
          (\<exists>q Xa. [[Xa]\<^sub>R] \<in> Q \<and> q \<in> Q \<and> (\<forall>q' Y. q \<noteq> [Y]\<^sub>R # q') \<and>
            intersect_refusal_trace X (p'' @ [[Tick]\<^sub>E]) = intersect_refusal_trace Xa p @ q)"
        apply (cases "contains_refusal p''", auto)
        apply (erule_tac x="p''" in allE, auto, erule_tac x="p''" in allE, auto)
        by (simp add: not_contains_refusal_append_event not_contains_refusal_intersect_refusal_trace)
    next
      fix p'' Y
      assume "p'' @ [[Y]\<^sub>R] \<in> P" "[[X]\<^sub>R] \<in> Q"
      then show "\<forall>p Xa. p @ [[Xa]\<^sub>R] \<in> P \<longrightarrow>
          (\<forall>Ya q. [Ya]\<^sub>R # q \<in> Q \<longrightarrow> intersect_refusal_trace X (p'' @ [[Y]\<^sub>R]) \<noteq> intersect_refusal_trace Ya (p @ [[Xa]\<^sub>R]) @ q) \<Longrightarrow>
        \<exists>p. p \<in> P \<and> (\<forall>p'. p \<noteq> p' @ [[Tick]\<^sub>E]) \<and> (\<forall>p' Y. p \<noteq> p' @ [[Y]\<^sub>R]) \<and> contains_refusal p \<and>
          (\<exists>q Xa. [[Xa]\<^sub>R] \<in> Q \<and> q \<in> Q \<and> (\<forall>q' Y. q \<noteq> [Y]\<^sub>R # q') \<and> 
            intersect_refusal_trace X (p'' @ [[Y]\<^sub>R]) = intersect_refusal_trace Xa p @ q)"
        by (erule_tac x="p''" in allE, erule_tac x="Y" in allE, auto)
    next
      assume case_assms: "p' \<in> P" "[[X]\<^sub>R] \<in> Q" "\<forall>p''. p' \<noteq> p'' @ [[Tick]\<^sub>E]" "\<forall>p'' Y. p' \<noteq> p'' @ [[Y]\<^sub>R]"
      then show "\<forall>p. p \<in> P \<longrightarrow> (\<exists>p'. p = p' @ [[Tick]\<^sub>E]) \<or> (\<exists>p' Y. p = p' @ [[Y]\<^sub>R]) \<or> 
          contains_refusal p \<or> (\<forall>q. q \<in> Q \<longrightarrow> (\<exists>q' Y. q = [Y]\<^sub>R # q') \<or> intersect_refusal_trace X p' \<noteq> p @ q) \<Longrightarrow>
        \<exists>p. p \<in> P \<and> (\<forall>p'. p \<noteq> p' @ [[Tick]\<^sub>E]) \<and> (\<forall>p' Y. p \<noteq> p' @ [[Y]\<^sub>R]) \<and> contains_refusal p \<and>
          (\<exists>q Xa. [[Xa]\<^sub>R] \<in> Q \<and> q \<in> Q \<and> (\<forall>q' Y. q \<noteq> [Y]\<^sub>R # q') \<and> 
            intersect_refusal_trace X p' = intersect_refusal_trace Xa p @ q)"
        apply (cases "contains_refusal p'")
        apply (rule_tac x="p'" in exI, auto, rule_tac x="[]" in exI, rule_tac x="X" in exI, auto simp add: TT0_TT1_empty TT0_Q TT1_Q)
        apply (erule_tac x="p'" in allE, simp_all add: case_assms, erule_tac x="[]" in allE, simp_all add: case_assms)
        by (simp add: TT0_TT1_empty TT0_Q TT1_Q not_contains_refusal_intersect_refusal_trace)
    qed
  next
    fix p
    assume in_P: "p @ [[Tick]\<^sub>E] \<in> P"
    assume not_contains_refusal_p: "\<not> contains_refusal p"
    assume \<rho>_assm: "\<rho> \<lesssim>\<^sub>C p @ [[Tick]\<^sub>E]"
    then have \<rho>_cases: "(\<exists>p'. \<rho> = p' @ [[Tick]\<^sub>E])
        \<or> ((\<nexists>p'. \<rho> = p' @ [[Tick]\<^sub>E]) \<and> (\<nexists>p' Y. \<rho> = p' @ [[Y]\<^sub>R]))"
      using not_contains_refusal_append_event not_contains_refusal_ctt_prefix_subset_end_nonref not_contains_refusal_p by (auto, blast)
    have \<rho>_in_P: "\<rho> \<in> P"
      using \<rho>_assm TT1_P in_P unfolding TT1_def by auto
    have not_contains_refusal_\<rho>: "\<not> contains_refusal \<rho>"
      using \<rho>_assm not_contains_refusal_append_event not_contains_refusal_ctt_prefix_subset not_contains_refusal_p by auto
    show "\<rho> \<in> P \<triangle>\<^sub>U Q"
      using \<rho>_cases \<rho>_in_P \<rho>_assm unfolding UntimedInterruptTTT_def
    proof auto
      fix p' 
      assume "p' @ [[Tick]\<^sub>E] \<in> P" "contains_refusal p'" "\<rho> = p' @ [[Tick]\<^sub>E]"
      then show "\<exists>p. p \<in> P \<and> (\<forall>p'. p \<noteq> p' @ [[Tick]\<^sub>E]) \<and> (\<forall>p' Y. p \<noteq> p' @ [[Y]\<^sub>R]) \<and> contains_refusal p 
        \<and> (\<exists>q X. [[X]\<^sub>R] \<in> Q \<and> q \<in> Q \<and> (\<forall>q' Y. q \<noteq> [Y]\<^sub>R # q') \<and> p' @ [[Tick]\<^sub>E] = intersect_refusal_trace X p @ q)"
        using ctt_prefix_concat ctt_prefix_imp_prefix_subset not_contains_refusal_\<rho> not_contains_refusal_ctt_prefix_subset by blast
    next
      assume "\<forall>p'. \<rho> \<noteq> p' @ [[Tick]\<^sub>E]" "\<forall>p' Y. \<rho> \<noteq> p' @ [[Y]\<^sub>R]"
      then show "\<forall>p. p \<in> P \<longrightarrow> (\<exists>p'. p = p' @ [[Tick]\<^sub>E]) \<or> (\<exists>p' Y. p = p' @ [[Y]\<^sub>R]) \<or> 
          contains_refusal p \<or> (\<forall>q. q \<in> Q \<longrightarrow> (\<exists>q' Y. q = [Y]\<^sub>R # q') \<or> \<rho> \<noteq> p @ q) \<Longrightarrow>
        \<exists>p. p \<in> P \<and> (\<forall>p'. p \<noteq> p' @ [[Tick]\<^sub>E]) \<and> (\<forall>p' Y. p \<noteq> p' @ [[Y]\<^sub>R]) \<and> contains_refusal p \<and>
          (\<exists>q X. [[X]\<^sub>R] \<in> Q \<and> q \<in> Q \<and> (\<forall>q' Y. q \<noteq> [Y]\<^sub>R # q') \<and> \<rho> = intersect_refusal_trace X p @ q)"
        using \<rho>_in_P \<rho>_assm not_contains_refusal_\<rho>
        by (erule_tac x="\<rho>" in allE, auto, erule_tac x="[]" in allE, auto simp add: TT0_TT1_empty TT0_Q TT1_Q)
    qed
  next
    fix p q
    fix X Y
    assume in_P: "p @ [[X]\<^sub>R] \<in> P"
    assume in_Q: "[Y]\<^sub>R # q \<in> Q"
    then have Y_in_Q: "[[Y]\<^sub>R] \<in> Q"
      by (meson TT1_Q TT1_def ctt_prefix_subset.simps(1) ctt_prefix_subset.simps(2) ctt_prefix_subset_refl)
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
      have ttWF_p_ref: "ttWF (p @ [[X]\<^sub>R])"
        by (simp add: P_wf in_P)
      assume "\<rho> \<lesssim>\<^sub>C intersect_refusal_trace Y (p @ [[X]\<^sub>R])"
      then obtain p' where p'_assms: "p' \<lesssim>\<^sub>C p @ [[X]\<^sub>R] \<and> \<rho> = intersect_refusal_trace Y p'"
        using prefix_subset_of_intersect_refusal_trace by blast
      then have p'_in_P: "p' \<in> P"
        using TT1_P TT1_def in_P by blast
      then have ttWF_p': "ttWF p'"
        using P_wf by blast
      have p'_cases: "(\<exists>p'' Z. p' = p'' @ [[Z]\<^sub>R]) \<or> ((\<nexists>p''. p' = p'' @ [[Tick]\<^sub>E]) \<and> (\<nexists>p'' Z. p' = p'' @ [[Z]\<^sub>R]))"
        using p'_assms ttWF_p_ref ttWF_end_refusal_prefix_subset by fastforce
      then show "\<rho> \<in> P \<triangle>\<^sub>U Q"
        unfolding UntimedInterruptTTT_def
      proof auto
        fix p'' Z
        show "p' = p'' @ [[Z]\<^sub>R] \<Longrightarrow>
          \<forall>p X. p @ [[X]\<^sub>R] \<in> P \<longrightarrow> (\<forall>Y q. [Y]\<^sub>R # q \<in> Q \<longrightarrow> \<rho> \<noteq> intersect_refusal_trace Y (p @ [[X]\<^sub>R]) @ q) \<Longrightarrow>
          \<exists>p. p \<in> P \<and> (\<forall>p'. p \<noteq> p' @ [[Tick]\<^sub>E]) \<and> (\<forall>p' Y. p \<noteq> p' @ [[Y]\<^sub>R]) \<and> contains_refusal p \<and>
            (\<exists>q X. [[X]\<^sub>R] \<in> Q \<and> q \<in> Q \<and> (\<forall>q' Y. q \<noteq> [Y]\<^sub>R # q') \<and> \<rho> = intersect_refusal_trace X p @ q)"
          using p'_in_P Y_in_Q p'_assms
          by (erule_tac x="p''" in allE, erule_tac x="Z" in allE, auto)
      next
        assume case_assm: "\<forall>p''. p' \<noteq> p'' @ [[Tick]\<^sub>E]" "\<forall>p'' Z. p' \<noteq> p'' @ [[Z]\<^sub>R]"
        show "\<forall>p. p \<in> P \<longrightarrow> (\<exists>p'. p = p' @ [[Tick]\<^sub>E]) \<or> (\<exists>p' Y. p = p' @ [[Y]\<^sub>R]) \<or>
            contains_refusal p \<or> (\<forall>q. q \<in> Q \<longrightarrow> (\<exists>q' Y. q = [Y]\<^sub>R # q') \<or> \<rho> \<noteq> p @ q) \<Longrightarrow>
          \<exists>p. p \<in> P \<and> (\<forall>p'. p \<noteq> p' @ [[Tick]\<^sub>E]) \<and> (\<forall>p' Y. p \<noteq> p' @ [[Y]\<^sub>R]) \<and> contains_refusal p \<and>
            (\<exists>q X. [[X]\<^sub>R] \<in> Q \<and> q \<in> Q \<and> (\<forall>q' Y. q \<noteq> [Y]\<^sub>R # q') \<and> \<rho> = intersect_refusal_trace X p @ q)"
          using p'_in_P Y_in_Q p'_assms case_assm
          apply (cases "contains_refusal p'", auto)
          apply (rule_tac x="p'" in exI, auto)
          apply (metis TT1_Q TT1_def append_Nil2 ctt_prefix_concat ctt_prefix_imp_prefix_subset list.distinct(1) self_append_conv2)
          apply (erule_tac x="p'" in allE, auto)
          by (metis TT0_TT1_empty TT0_Q TT1_Q append_Nil2 contains_refusal.simps(1) contains_refusal.simps(2) not_contains_refusal_intersect_refusal_trace)
      qed
    next
      fix q' p' X'
      assume case_assms: "intersect_refusal_trace Y (p' @ [[X']\<^sub>R]) \<subseteq>\<^sub>C intersect_refusal_trace Y (p @ [[X]\<^sub>R])" "q' \<lesssim>\<^sub>C q" "p' @ [[X']\<^sub>R] \<subseteq>\<^sub>C p @ [[X]\<^sub>R]"
      then have "p' @ [[X']\<^sub>R] \<in> P"
        using TT1_P TT1_def ctt_subset_imp_prefix_subset in_P by blast
      then show "intersect_refusal_trace Y (p' @ [[X']\<^sub>R]) @ q' \<in> P \<triangle>\<^sub>U Q"
        unfolding UntimedInterruptTTT_def using case_assms in_Q
      proof (auto)
        show "p' @ [[X']\<^sub>R] \<in> P \<Longrightarrow> intersect_refusal_trace Y (p' @ [[X']\<^sub>R]) \<subseteq>\<^sub>C intersect_refusal_trace Y (p @ [[X]\<^sub>R]) \<Longrightarrow>
          q' \<lesssim>\<^sub>C q \<Longrightarrow> p' @ [[X']\<^sub>R] \<subseteq>\<^sub>C p @ [[X]\<^sub>R] \<Longrightarrow> [Y]\<^sub>R # q \<in> Q \<Longrightarrow>
          \<forall>p X. p @ [[X]\<^sub>R] \<in> P \<longrightarrow>
            (\<forall>Ya q. [Ya]\<^sub>R # q \<in> Q \<longrightarrow> intersect_refusal_trace Y (p' @ [[X']\<^sub>R]) @ q' \<noteq> intersect_refusal_trace Ya (p @ [[X]\<^sub>R]) @ q) \<Longrightarrow>
          \<exists>p. p \<in> P \<and> (\<forall>p'. p \<noteq> p' @ [[Tick]\<^sub>E]) \<and> (\<forall>p' Y. p \<noteq> p' @ [[Y]\<^sub>R]) \<and> contains_refusal p \<and>
            (\<exists>q X. [[X]\<^sub>R] \<in> Q \<and> q \<in> Q \<and> (\<forall>q' Y. q \<noteq> [Y]\<^sub>R # q') \<and> 
              intersect_refusal_trace Y (p' @ [[X']\<^sub>R]) @ q' = intersect_refusal_trace X p @ q)"
          by (metis TT1_Q TT1_def append.left_neutral append_Cons ctt_prefix_subset_same_front)+
      qed
    qed
  next
    fix p q :: "'a cttobs list"
    fix X
    assume case_assms: "\<forall>p'. p \<noteq> p' @ [[Tick]\<^sub>E]" "\<forall>p' Y. p \<noteq> p' @ [[Y]\<^sub>R]"
    assume ref_in_Q: "[[X]\<^sub>R] \<in> Q"
    assume q_in_Q: "q \<in> Q"
    assume q_nonref: "\<forall>q' Y. q \<noteq> [Y]\<^sub>R # q'"
    assume p_contains_refusal: "contains_refusal p"
    assume p_in_P: "p \<in> P"
    then have ttWF_p: "ttWF p"
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
        using TT1_P TT1_def p_in_P by blast
      have "(\<exists> s e. p = s @ [[Event e]\<^sub>E]) \<or> (\<exists> s. p = s @ [[Tock]\<^sub>E]) \<or> p = []"
        using case_assms by (auto, metis cttevent.exhaust cttobs.exhaust rev_exhaust)
      then have "(\<exists> p'' Y. p' = p'' @ [[Y]\<^sub>R]) \<or> ((\<nexists>p''. p' = p'' @ [[Tick]\<^sub>E]) \<and> (\<nexists>p'' Y. p' = p'' @ [[Y]\<^sub>R]))"
        using ttWF_p p'_assms(1) apply auto
        using ttWF_end_Event_prefix_subset apply fastforce
        using ttWF_end_Tock_prefix_subset apply fastforce
        using ctt_prefix_subset.elims(2) by auto
      then show "\<rho> \<in> P \<triangle>\<^sub>U Q"
        unfolding UntimedInterruptTTT_def
      proof auto
        fix p'' Y
        show "p' = p'' @ [[Y]\<^sub>R] \<Longrightarrow>
          \<forall>p X. p @ [[X]\<^sub>R] \<in> P \<longrightarrow> (\<forall>Y q. [Y]\<^sub>R # q \<in> Q \<longrightarrow> \<rho> \<noteq> intersect_refusal_trace Y (p @ [[X]\<^sub>R]) @ q) \<Longrightarrow>
          \<exists>p. p \<in> P \<and> (\<forall>p'. p \<noteq> p' @ [[Tick]\<^sub>E]) \<and> (\<forall>p' Y. p \<noteq> p' @ [[Y]\<^sub>R]) \<and> contains_refusal p \<and>
            (\<exists>q X. [[X]\<^sub>R] \<in> Q \<and> q \<in> Q \<and> (\<forall>q' Y. q \<noteq> [Y]\<^sub>R # q') \<and> \<rho> = intersect_refusal_trace X p @ q)"
          using ref_in_Q p'_in_P p'_assms by (erule_tac x="p''" in allE, erule_tac x="Y" in allE, auto)
      next
        assume case_assms: "\<forall>p''. p' \<noteq> p'' @ [[Tick]\<^sub>E]" "\<forall>p'' Y. p' \<noteq> p'' @ [[Y]\<^sub>R]"
        show "\<forall>p. p \<in> P \<longrightarrow> (\<exists>p'. p = p' @ [[Tick]\<^sub>E]) \<or> (\<exists>p' Y. p = p' @ [[Y]\<^sub>R]) \<or> contains_refusal p \<or>
            (\<forall>q. q \<in> Q \<longrightarrow> (\<exists>q' Y. q = [Y]\<^sub>R # q') \<or> \<rho> \<noteq> p @ q) \<Longrightarrow>
          \<exists>p. p \<in> P \<and> (\<forall>p'. p \<noteq> p' @ [[Tick]\<^sub>E]) \<and> (\<forall>p' Y. p \<noteq> p' @ [[Y]\<^sub>R]) \<and> contains_refusal p \<and>
            (\<exists>q X. [[X]\<^sub>R] \<in> Q \<and> q \<in> Q \<and> (\<forall>q' Y. q \<noteq> [Y]\<^sub>R # q') \<and> \<rho> = intersect_refusal_trace X p @ q)"
          using ref_in_Q p'_in_P p'_assms TT0_TT1_empty TT0_Q TT1_Q
          apply (cases "contains_refusal p'")
          apply (rule_tac x="p'" in exI, auto simp add: case_assms, rule_tac x="[]" in exI, auto)
          by (erule_tac x="p'" in allE, auto simp add: case_assms not_contains_refusal_intersect_refusal_trace, erule_tac x="[]" in allE, auto)
      qed
    next
      fix t' s'
      assume "t' \<lesssim>\<^sub>C q"
      then have t'_assms: "t' \<in> Q \<and> (\<nexists>q' Y. t' = [Y]\<^sub>R # q')"
        apply auto
        using TT1_Q TT1_def q_in_Q apply blast
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
        using s'_ctt_subset TT1_P TT1_def ctt_subset_imp_prefix_subset p_in_P by blast 
      have s'_contains_refusal: "contains_refusal s'"
        using contains_refusal_ctt_subset p_contains_refusal s'_ctt_subset by auto
      show  "\<rho> = intersect_refusal_trace X s' @ t' \<Longrightarrow> intersect_refusal_trace X s' @ t' \<in> P \<triangle>\<^sub>U Q"
        unfolding UntimedInterruptTTT_def
      proof auto
        show "\<exists>p. p \<in> P \<and> (\<forall>p'. p \<noteq> p' @ [[Tick]\<^sub>E]) \<and> (\<forall>p' Y. p \<noteq> p' @ [[Y]\<^sub>R]) \<and> contains_refusal p \<and>
          (\<exists>q Xa. [[Xa]\<^sub>R] \<in> Q \<and> q \<in> Q \<and> (\<forall>q' Y. q \<noteq> [Y]\<^sub>R # q') \<and> 
            intersect_refusal_trace X s' @ t' = intersect_refusal_trace Xa p @ q)"
          using s'_assms t'_assms ref_in_Q s'_in_P s'_contains_refusal by (rule_tac x="s'" in exI, auto)
      qed
    qed
  next
    fix p q :: "'a cttobs list"
    assume case_assms: "\<forall>p'. p \<noteq> p' @ [[Tick]\<^sub>E]" "\<forall>p' Y. p \<noteq> p' @ [[Y]\<^sub>R]"
    assume q_in_Q: "q \<in> Q"
    assume q_nonref: "\<forall>q' Y. q \<noteq> [Y]\<^sub>R # q'"
    assume p_not_contains_refusal: "\<not> contains_refusal p"
    assume p_in_P: "p \<in> P"
    then have ttWF_p: "ttWF p"
      using P_wf by blast
    assume "\<rho> \<lesssim>\<^sub>C p @ q"
    then have "\<rho> \<lesssim>\<^sub>C p \<or> (\<exists>t' s'. s' \<subseteq>\<^sub>C p \<and> t' \<lesssim>\<^sub>C q \<and> \<rho> = s' @ t')"
      by (simp add: ctt_prefix_subset_concat2)
    then show "\<rho> \<in> P \<triangle>\<^sub>U Q"
    proof auto
      assume \<rho>_assms: "\<rho> \<lesssim>\<^sub>C p"
      then have \<rho>_in_P: "\<rho> \<in> P"
        using TT1_P TT1_def p_in_P by blast
      have "(\<exists> s e. p = s @ [[Event e]\<^sub>E]) \<or> (\<exists> s. p = s @ [[Tock]\<^sub>E]) \<or> p = []"
        using case_assms by (auto, metis cttevent.exhaust cttobs.exhaust rev_exhaust)
      then have \<rho>_end_assms: "(\<nexists>p'. \<rho> = p' @ [[Tick]\<^sub>E]) \<and> (\<nexists>p' Y. \<rho> = p' @ [[Y]\<^sub>R])"
        using ttWF_p \<rho>_assms not_contains_refusal_ctt_prefix_subset_end_nonref p_not_contains_refusal apply auto
        using ttWF_end_Event_prefix_subset ttWF_end_Tock_prefix_subset ctt_prefix_subset_antisym by fastforce+
      have \<rho>_not_contains_refusal: "\<not> contains_refusal \<rho>"
        using \<rho>_assms not_contains_refusal_ctt_prefix_subset p_not_contains_refusal by auto
      show "\<rho> \<in> P \<triangle>\<^sub>U Q"
        unfolding UntimedInterruptTTT_def
      proof auto
        show "\<forall>p. p \<in> P \<longrightarrow> (\<exists>p'. p = p' @ [[Tick]\<^sub>E]) \<or> (\<exists>p' Y. p = p' @ [[Y]\<^sub>R]) \<or> contains_refusal p \<or>
            (\<forall>q. q \<in> Q \<longrightarrow> (\<exists>q' Y. q = [Y]\<^sub>R # q') \<or> \<rho> \<noteq> p @ q) \<Longrightarrow>
          \<exists>p. p \<in> P \<and> (\<forall>p'. p \<noteq> p' @ [[Tick]\<^sub>E]) \<and> (\<forall>p' Y. p \<noteq> p' @ [[Y]\<^sub>R]) \<and> contains_refusal p \<and>
            (\<exists>q X. [[X]\<^sub>R] \<in> Q \<and> q \<in> Q \<and> (\<forall>q' Y. q \<noteq> [Y]\<^sub>R # q') \<and> \<rho> = intersect_refusal_trace X p @ q)"
          using \<rho>_in_P \<rho>_assms \<rho>_not_contains_refusal \<rho>_end_assms
          by (erule_tac x="\<rho>" in allE, auto, erule_tac x="[]" in allE, auto simp add: TT0_TT1_empty TT0_Q TT1_Q)
      qed
    next
      fix t' s'
      assume "t' \<lesssim>\<^sub>C q"
      then have t'_assms: "t' \<in> Q \<and> (\<nexists>q' Y. t' = [Y]\<^sub>R # q')"
        apply auto
        using TT1_Q TT1_def q_in_Q apply blast
        using ctt_prefix_subset.elims(2) q_nonref by blast
      assume s'_ctt_subset: "s' \<subseteq>\<^sub>C p"
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
      have s'_not_contains_refusal: "\<not> contains_refusal s'"
        using not_contains_refusal_ctt_subset p_not_contains_refusal s'_ctt_subset by auto
      have s'_in_P: "s' \<in> P"
        using s'_ctt_subset TT1_P TT1_def ctt_subset_imp_prefix_subset p_in_P by blast 
      show  "\<rho> = s' @ t' \<Longrightarrow> s' @ t' \<in> P \<triangle>\<^sub>U Q"
        unfolding UntimedInterruptTTT_def
        (*using s'_assms t'_assms ref_in_Q s'_in_P*)
      proof auto
        show "\<rho> = s' @ t' \<Longrightarrow>
          \<forall>p. p \<in> P \<longrightarrow> (\<exists>p'. p = p' @ [[Tick]\<^sub>E]) \<or> (\<exists>p' Y. p = p' @ [[Y]\<^sub>R]) \<or> contains_refusal p \<or>
            (\<forall>q. q \<in> Q \<longrightarrow> (\<exists>q' Y. q = [Y]\<^sub>R # q') \<or> s' @ t' \<noteq> p @ q) \<Longrightarrow>
          \<exists>p. p \<in> P \<and> (\<forall>p'. p \<noteq> p' @ [[Tick]\<^sub>E]) \<and> (\<forall>p' Y. p \<noteq> p' @ [[Y]\<^sub>R]) \<and> contains_refusal p \<and>
            (\<exists>q X. [[X]\<^sub>R] \<in> Q \<and> q \<in> Q \<and> (\<forall>q' Y. q \<noteq> [Y]\<^sub>R # q') \<and> s' @ t' = intersect_refusal_trace X p @ q) "
          using s'_assms t'_assms s'_not_contains_refusal s'_in_P by (erule_tac x="s'" in allE, auto)
      qed
    qed
  qed
qed

lemma TT2_UntimedInterrupt:
  assumes P_wf: "\<forall> x\<in>P. ttWF x"
  assumes TT0_Q: "TT0 Q"
  assumes TT1_P: "TT1 P" and TT1_Q: "TT1 Q"
  assumes TT2_P: "TT2 P" and TT2_Q: "TT2 Q"
  shows "TT2 (P \<triangle>\<^sub>U Q)"
  unfolding TT2_def
proof (auto)
  fix \<rho> X Y
  assume assm1: "\<rho> @ [[X]\<^sub>R] \<in> P \<triangle>\<^sub>U Q"
  then have \<rho>_cases: "(\<exists>p Z W q. p @ [[Z]\<^sub>R] \<in> P \<and> [W]\<^sub>R # q \<in> Q \<and> \<rho> @ [[X]\<^sub>R] = intersect_refusal_trace W (p @ [[Z]\<^sub>R]) @ q)
    \<or> (\<exists>p q Z. p \<in> P \<and> (\<nexists>p'. p = p' @ [[Tick]\<^sub>E]) \<and> (\<nexists>p' Y. p = p' @ [[Y]\<^sub>R]) \<and> contains_refusal p
      \<and> [[Z]\<^sub>R] \<in> Q \<and> q @ [[X]\<^sub>R] \<in> Q \<and> q \<noteq> [] \<and> (\<nexists>q' Y. q = [Y]\<^sub>R # q') \<and> \<rho> = intersect_refusal_trace Z p @ q)
    \<or> (\<exists>p q. p \<in> P \<and> (\<nexists>p'. p = p' @ [[Tick]\<^sub>E]) \<and> (\<nexists>p' Y. p = p' @ [[Y]\<^sub>R]) \<and> \<not> contains_refusal p
      \<and> q @ [[X]\<^sub>R] \<in> Q \<and> q \<noteq> [] \<and> (\<nexists>q' Y. q = [Y]\<^sub>R # q') \<and> \<rho> = p @ q)"
    unfolding UntimedInterruptTTT_def
  proof (safe, simp_all)
    fix p Xa
    assume "\<rho> @ [[X]\<^sub>R] = intersect_refusal_trace Xa (p @ [[Tick]\<^sub>E])"
    then have "\<rho> @ [[X]\<^sub>R] \<subseteq>\<^sub>C p @ [[Tick]\<^sub>E]"
      by (simp add: intersect_refusal_trace_subset)
    then have "False"
      using ctt_subset_same_length by (induct \<rho> p rule:ctt_subset.induct, auto, fastforce+)
    then show "\<exists>p. p \<in> P \<and> (\<forall>p'. p \<noteq> p' @ [[Tick]\<^sub>E]) \<and> (\<forall>p' Y. p \<noteq> p' @ [[Y]\<^sub>R]) \<and> contains_refusal p \<and>
      (\<exists>q Z. [[Z]\<^sub>R] \<in> Q \<and> q @ [[X]\<^sub>R] \<in> Q \<and> q \<noteq> [] \<and> (\<forall>q' Y. q \<noteq> [Y]\<^sub>R # q') \<and> \<rho> = intersect_refusal_trace Z p @ q)"
      by auto
  next
    fix p q Xa
    assume case_assms: "p \<in> P" "\<forall>p'. p \<noteq> p' @ [[Tick]\<^sub>E]" "\<forall>p' Y. p \<noteq> p' @ [[Y]\<^sub>R]" "q \<in> Q" "contains_refusal p"
      "\<forall>q' Y. q \<noteq> [Y]\<^sub>R # q'" "\<rho> @ [[X]\<^sub>R] = intersect_refusal_trace Xa p @ q" "[[Xa]\<^sub>R] \<in> Q"
    then have "(\<exists> q'. q = q' @ [[X]\<^sub>R]) \<or> q = []"
      by (metis append_butlast_last_id last_appendR last_snoc)
    then have "\<exists> q'. q = q' @ [[X]\<^sub>R]"
      using case_assms
    proof (safe, simp)
      assume "q = []"
      then have "\<rho> @ [[X]\<^sub>R] \<subseteq>\<^sub>C p"
        by (simp add: case_assms(7) intersect_refusal_trace_subset)
      then obtain p' Z where "p = p' @ [[Z]\<^sub>R]"
        using ctt_subset_same_length by (induct \<rho> p rule:ctt_subset.induct, auto, case_tac v, auto, fastforce)
      then show "\<forall>p' Y. p \<noteq> p' @ [[Y]\<^sub>R] \<Longrightarrow> False"
        by auto
    qed
    then show "\<exists>p. p \<in> P \<and> (\<forall>p'. p \<noteq> p' @ [[Tick]\<^sub>E]) \<and> (\<forall>p' Y. p \<noteq> p' @ [[Y]\<^sub>R]) \<and> contains_refusal p \<and>
      (\<exists>q Z. [[Z]\<^sub>R] \<in> Q \<and> q @ [[X]\<^sub>R] \<in> Q \<and> q \<noteq> [] \<and> (\<forall>q' Y. q \<noteq> [Y]\<^sub>R # q') \<and> \<rho> = intersect_refusal_trace Z p @ q)"
      using case_assms by (rule_tac x="p" in exI, auto, rule_tac x="q'" in exI, auto)
  next
    fix p q
    assume case_assms: "p \<in> P" "\<forall>p'. p \<noteq> p' @ [[Tick]\<^sub>E]" "\<forall>p' Y. p \<noteq> p' @ [[Y]\<^sub>R]" "q \<in> Q"
      "\<forall>q' Y. q \<noteq> [Y]\<^sub>R # q'" "\<rho> @ [[X]\<^sub>R] = p @ q" "\<not> contains_refusal p"
    then have "(\<exists> q'. q = q' @ [[X]\<^sub>R]) \<or> q = []"
      by (metis append_butlast_last_id last_appendR last_snoc)
    then have "\<exists> q'. q = q' @ [[X]\<^sub>R]"
      using case_assms(3) case_assms(6) by auto
    then show "\<forall>p. p \<in> P \<longrightarrow> (\<exists>p'. p = p' @ [[Tick]\<^sub>E]) \<or> (\<exists>p' Y. p = p' @ [[Y]\<^sub>R]) \<or> contains_refusal p \<or>
        (\<forall>q. q @ [[X]\<^sub>R] \<in> Q \<longrightarrow> q = [] \<or> (\<exists>q' Y. q = [Y]\<^sub>R # q') \<or> \<rho> \<noteq> p @ q) \<Longrightarrow>
      \<exists>p. p \<in> P \<and> (\<forall>p'. p \<noteq> p' @ [[Tick]\<^sub>E]) \<and> (\<forall>p' Y. p \<noteq> p' @ [[Y]\<^sub>R]) \<and> contains_refusal p \<and>
        (\<exists>q Z. [[Z]\<^sub>R] \<in> Q \<and> q @ [[X]\<^sub>R] \<in> Q \<and> q \<noteq> [] \<and> (\<forall>q' Y. q \<noteq> [Y]\<^sub>R # q') \<and> \<rho> = intersect_refusal_trace Z p @ q)"
      using case_assms by (erule_tac x="p" in allE, auto)
  qed
  assume assm2: "Y \<inter> {e. e \<noteq> Tock \<and> \<rho> @ [[e]\<^sub>E] \<in> P \<triangle>\<^sub>U Q \<or> e = Tock \<and> \<rho> @ [[X]\<^sub>R, [e]\<^sub>E] \<in> P \<triangle>\<^sub>U Q} = {}"
  show "\<rho> @ [[X \<union> Y]\<^sub>R] \<in> P \<triangle>\<^sub>U Q"
    using \<rho>_cases
  proof auto
    fix p Z W q
    assume case_assms: "p @ [[Z]\<^sub>R] \<in> P" "[W]\<^sub>R # q \<in> Q" "\<rho> @ [[X]\<^sub>R] = intersect_refusal_trace W (p @ [[Z]\<^sub>R]) @ q"
    then have "q = [] \<or> (\<exists> q'. q =  q' @ [[X]\<^sub>R])"
      by (metis append_butlast_last_id last_appendR last_snoc)
    then show "\<rho> @ [[X \<union> Y]\<^sub>R] \<in> P \<triangle>\<^sub>U Q"
    proof auto
      assume case_assms2: "q = []"
      have "{e. e \<noteq> Tock \<and> \<rho> @ [[e]\<^sub>E] \<in> P \<or> e = Tock \<and> \<rho> @ [[X]\<^sub>R, [e]\<^sub>E] \<in> P} \<subseteq> {e. e \<noteq> Tock \<and> \<rho> @ [[e]\<^sub>E] \<in> P \<triangle>\<^sub>U Q \<or> e = Tock \<and> \<rho> @ [[X]\<^sub>R, [e]\<^sub>E] \<in> P \<triangle>\<^sub>U Q}"
      proof (cases "contains_refusal \<rho>", auto)
        fix x
        assume case_assms3: "\<rho> @ [[x]\<^sub>E] \<in> P" "x \<noteq> Tock" "contains_refusal \<rho>"
        then have "(x = Tick \<or> (\<exists> e. x = Event e))"
          by (cases x, auto)
        then show "\<rho> @ [[x]\<^sub>E] \<in> P \<triangle>\<^sub>U Q"
        proof (auto)
          show "x = Tick \<Longrightarrow> \<rho> @ [[Tick]\<^sub>E] \<in> P \<triangle>\<^sub>U Q"
            unfolding UntimedInterruptTTT_def apply auto
            using case_assms3(1) apply blast
            by (metis append_self_conv case_assms(2) case_assms(3) case_assms2 case_assms3(1) intersect_refusal_trace_end_ref_imp_intersect_refusal_trace_end_event intersect_refusal_trace_idempotent)
        next
          fix e
          show "x = Event e \<Longrightarrow> \<rho> @ [[Event e]\<^sub>E] \<in> P \<triangle>\<^sub>U Q"
            unfolding UntimedInterruptTTT_def apply auto
            using case_assms case_assms2 case_assms3 apply (rule_tac x="\<rho> @ [[Event e]\<^sub>E]" in exI, auto)
            apply (meson ctt_prefix_concat ctt_prefix_imp_prefix_subset not_contains_refusal_ctt_prefix_subset)
            by (metis (no_types, hide_lams) TT1_Q TT1_def append_Nil2 ctt_prefix_subset.simps(1) intersect_refusal_trace_end_ref_imp_intersect_refusal_trace_end_event intersect_refusal_trace_idempotent list.distinct(1))
        qed
      next
        fix x
        assume case_assms3: "\<rho> @ [[x]\<^sub>E] \<in> P" "x \<noteq> Tock" "contains_refusal \<rho>"
        then have "(x = Tick \<or> (\<exists> e. x = Event e))"
          by (cases x, auto)
        then show "\<rho> @ [[x]\<^sub>E] \<in> P \<triangle>\<^sub>U Q"
        proof (auto)
          show "x = Tick \<Longrightarrow> \<rho> @ [[Tick]\<^sub>E] \<in> P \<triangle>\<^sub>U Q"
            unfolding UntimedInterruptTTT_def apply auto
            using case_assms3(1) apply blast
            by (metis append_self_conv case_assms(2) case_assms(3) case_assms2 case_assms3(1) intersect_refusal_trace_end_ref_imp_intersect_refusal_trace_end_event intersect_refusal_trace_idempotent)
        next
          fix e
          show "x = Event e \<Longrightarrow> \<rho> @ [[Event e]\<^sub>E] \<in> P \<triangle>\<^sub>U Q"
            unfolding UntimedInterruptTTT_def apply auto
            using case_assms case_assms2 case_assms3 apply (rule_tac x="\<rho> @ [[Event e]\<^sub>E]" in exI, auto)
            apply (meson ctt_prefix_concat ctt_prefix_imp_prefix_subset not_contains_refusal_ctt_prefix_subset)
            by (metis (no_types, hide_lams) TT1_Q TT1_def append_Nil2 ctt_prefix_subset.simps(1) intersect_refusal_trace_end_ref_imp_intersect_refusal_trace_end_event intersect_refusal_trace_idempotent list.distinct(1))
        qed
      next
        fix x
        assume case_assms3: "\<rho> @ [[x]\<^sub>E] \<in> P" "x \<noteq> Tock" "\<not> contains_refusal \<rho>"
        then have "(x = Tick \<or> (\<exists> e. x = Event e))"
          by (cases x, auto)
        then show "\<rho> @ [[x]\<^sub>E] \<in> P \<triangle>\<^sub>U Q"
        proof (auto)
          show "x = Tick \<Longrightarrow> \<rho> @ [[Tick]\<^sub>E] \<in> P \<triangle>\<^sub>U Q"
            unfolding UntimedInterruptTTT_def apply auto
            using case_assms3(1) apply blast
            by (metis append_self_conv case_assms(2) case_assms(3) case_assms2 case_assms3(1) intersect_refusal_trace_end_ref_imp_intersect_refusal_trace_end_event intersect_refusal_trace_idempotent)
        next
          fix e
          show "x = Event e \<Longrightarrow> \<rho> @ [[Event e]\<^sub>E] \<in> P \<triangle>\<^sub>U Q"
            unfolding UntimedInterruptTTT_def
          proof auto
            show "x = Event e \<Longrightarrow>
              \<forall>p. p \<in> P \<longrightarrow> (\<exists>p'. p = p' @ [[Tick]\<^sub>E]) \<or> (\<exists>p' Y. p = p' @ [[Y]\<^sub>R]) \<or> contains_refusal p \<or>
                (\<forall>q. q \<in> Q \<longrightarrow> (\<exists>q' Y. q = [Y]\<^sub>R # q') \<or> \<rho> @ [[Event e]\<^sub>E] \<noteq> p @ q) \<Longrightarrow>
              \<exists>p. p \<in> P \<and> (\<forall>p'. p \<noteq> p' @ [[Tick]\<^sub>E]) \<and> (\<forall>p' Y. p \<noteq> p' @ [[Y]\<^sub>R]) \<and> contains_refusal p \<and>
                (\<exists>q X. [[X]\<^sub>R] \<in> Q \<and> q \<in> Q \<and> (\<forall>q' Y. q \<noteq> [Y]\<^sub>R # q') \<and> \<rho> @ [[Event e]\<^sub>E] = intersect_refusal_trace X p @ q)"
              using case_assms case_assms2 case_assms3 apply (erule_tac x="\<rho> @ [[Event e]\<^sub>E]" in allE, auto)
              apply (simp add: not_contains_refusal_append_event)
              using TT0_TT1_empty TT0_Q TT1_Q by blast
          qed
        qed
      next
        fix x
        assume case_assms3: "\<rho> @ [[x]\<^sub>E] \<in> P" "x \<noteq> Tock" "\<not> contains_refusal \<rho>"
        then have "(x = Tick \<or> (\<exists> e. x = Event e))"
          by (cases x, auto)
        then show "\<rho> @ [[x]\<^sub>E] \<in> P \<triangle>\<^sub>U Q"
        proof (auto)
          show "x = Tick \<Longrightarrow> \<rho> @ [[Tick]\<^sub>E] \<in> P \<triangle>\<^sub>U Q"
            unfolding UntimedInterruptTTT_def apply auto
            using case_assms3(1) apply blast
            by (metis append_self_conv case_assms(2) case_assms(3) case_assms2 case_assms3(1) intersect_refusal_trace_end_ref_imp_intersect_refusal_trace_end_event intersect_refusal_trace_idempotent)
        next
          fix e
          show "x = Event e \<Longrightarrow> \<rho> @ [[Event e]\<^sub>E] \<in> P \<triangle>\<^sub>U Q"
            unfolding UntimedInterruptTTT_def
          proof auto
            show "x = Event e \<Longrightarrow>
              \<forall>p. p \<in> P \<longrightarrow> (\<exists>p'. p = p' @ [[Tick]\<^sub>E]) \<or> (\<exists>p' Y. p = p' @ [[Y]\<^sub>R]) \<or> contains_refusal p \<or>
                (\<forall>q. q \<in> Q \<longrightarrow> (\<exists>q' Y. q = [Y]\<^sub>R # q') \<or> \<rho> @ [[Event e]\<^sub>E] \<noteq> p @ q) \<Longrightarrow>
              \<exists>p. p \<in> P \<and> (\<forall>p'. p \<noteq> p' @ [[Tick]\<^sub>E]) \<and> (\<forall>p' Y. p \<noteq> p' @ [[Y]\<^sub>R]) \<and> contains_refusal p \<and>
                (\<exists>q X. [[X]\<^sub>R] \<in> Q \<and> q \<in> Q \<and> (\<forall>q' Y. q \<noteq> [Y]\<^sub>R # q') \<and> \<rho> @ [[Event e]\<^sub>E] = intersect_refusal_trace X p @ q)"
              using case_assms case_assms2 case_assms3 apply (erule_tac x="\<rho> @ [[Event e]\<^sub>E]" in allE, auto)
              apply (simp add: not_contains_refusal_append_event)
              using TT0_TT1_empty TT0_Q TT1_Q by blast
          qed
        qed
      next
        show "contains_refusal \<rho> \<Longrightarrow> \<rho> @ [[X]\<^sub>R, [Tock]\<^sub>E] \<in> P \<Longrightarrow> \<rho> @ [[X]\<^sub>R, [Tock]\<^sub>E] \<notin> P \<triangle>\<^sub>U Q \<Longrightarrow> False"
          unfolding UntimedInterruptTTT_def
        proof auto
          show "contains_refusal \<rho> \<Longrightarrow> \<rho> @ [[X]\<^sub>R, [Tock]\<^sub>E] \<in> P \<Longrightarrow>
            \<forall>p. contains_refusal p \<longrightarrow> p \<in> P \<longrightarrow> (\<exists>p'. p = p' @ [[Tick]\<^sub>E]) \<or> (\<exists>p' Y. p = p' @ [[Y]\<^sub>R]) \<or>
              (\<forall>q. q \<in> Q \<longrightarrow> (\<forall>Xa. [[Xa]\<^sub>R] \<in> Q \<longrightarrow> (\<exists>q' Y. q = [Y]\<^sub>R # q') \<or> 
                \<rho> @ [[X]\<^sub>R, [Tock]\<^sub>E] \<noteq> intersect_refusal_trace Xa p @ q)) \<Longrightarrow> False"
            using case_assms case_assms2 apply (erule_tac x="\<rho> @ [[X]\<^sub>R, [Tock]\<^sub>E]" in allE, auto)
            using ctt_prefix_concat ctt_prefix_imp_prefix_subset not_contains_refusal_ctt_prefix_subset apply blast
            apply (erule_tac x="[]" in allE, auto)
            using TT0_TT1_empty TT0_Q TT1_Q apply blast
            by (metis intersect_refusal_trace_end_ref_imp_intersect_refusal_trace_end_ref_tock intersect_refusal_trace_idempotent)
        qed
      next
        have "contains_refusal \<rho> \<Longrightarrow> \<rho> @ [[X]\<^sub>R, [Tock]\<^sub>E] \<in> P \<Longrightarrow> \<rho> @ [[X]\<^sub>R, [Tock]\<^sub>E] \<notin> P \<triangle>\<^sub>U Q \<Longrightarrow> False"
          unfolding UntimedInterruptTTT_def
        proof auto
          show "contains_refusal \<rho> \<Longrightarrow> \<rho> @ [[X]\<^sub>R, [Tock]\<^sub>E] \<in> P \<Longrightarrow>
            \<forall>p. contains_refusal p \<longrightarrow> p \<in> P \<longrightarrow> (\<exists>p'. p = p' @ [[Tick]\<^sub>E]) \<or> (\<exists>p' Y. p = p' @ [[Y]\<^sub>R]) \<or>
              (\<forall>q. q \<in> Q \<longrightarrow> (\<forall>Xa. [[Xa]\<^sub>R] \<in> Q \<longrightarrow> (\<exists>q' Y. q = [Y]\<^sub>R # q') \<or> 
                \<rho> @ [[X]\<^sub>R, [Tock]\<^sub>E] \<noteq> intersect_refusal_trace Xa p @ q)) \<Longrightarrow> False"
            using case_assms case_assms2 apply (erule_tac x="\<rho> @ [[X]\<^sub>R, [Tock]\<^sub>E]" in allE, auto)
            using ctt_prefix_concat ctt_prefix_imp_prefix_subset not_contains_refusal_ctt_prefix_subset apply blast
            apply (erule_tac x="[]" in allE, auto)
            using TT0_TT1_empty TT0_Q TT1_Q apply blast
            by (metis intersect_refusal_trace_end_ref_imp_intersect_refusal_trace_end_ref_tock intersect_refusal_trace_idempotent)
        qed
        then show "contains_refusal \<rho> \<Longrightarrow> \<rho> @ [[X]\<^sub>R, [Tock]\<^sub>E] \<in> P \<Longrightarrow> \<rho> @ [[X]\<^sub>R, [Tock]\<^sub>E] \<notin> P \<triangle>\<^sub>U Q \<Longrightarrow> \<rho> @ [[Tock]\<^sub>E] \<in> P \<triangle>\<^sub>U Q"
          by auto
      next
        show "\<not> contains_refusal \<rho> \<Longrightarrow> \<rho> @ [[X]\<^sub>R, [Tock]\<^sub>E] \<in> P \<Longrightarrow> \<rho> @ [[X]\<^sub>R, [Tock]\<^sub>E] \<notin> P \<triangle>\<^sub>U Q \<Longrightarrow> False"
          unfolding UntimedInterruptTTT_def
        proof auto
          show "\<not> contains_refusal \<rho> \<Longrightarrow> \<rho> @ [[X]\<^sub>R, [Tock]\<^sub>E] \<in> P \<Longrightarrow>
            \<forall>p. contains_refusal p \<longrightarrow> p \<in> P \<longrightarrow> (\<exists>p'. p = p' @ [[Tick]\<^sub>E]) \<or> (\<exists>p' Y. p = p' @ [[Y]\<^sub>R]) \<or>
              (\<forall>q. q \<in> Q \<longrightarrow> (\<forall>Xa. [[Xa]\<^sub>R] \<in> Q \<longrightarrow> (\<exists>q' Y. q = [Y]\<^sub>R # q') \<or> 
                \<rho> @ [[X]\<^sub>R, [Tock]\<^sub>E] \<noteq> intersect_refusal_trace Xa p @ q)) \<Longrightarrow> False"
            using case_assms case_assms2 apply (erule_tac x="\<rho> @ [[X]\<^sub>R, [Tock]\<^sub>E]" in allE, auto)
            apply (metis append.assoc append.left_neutral append_Cons ctt_prefix_concat ctt_prefix_imp_prefix_subset not_contains_refusal_ctt_prefix_subset_end_nonref)
            apply (erule_tac x="[]" in allE, auto)
            using TT0_TT1_empty TT0_Q TT1_Q apply blast
            by (metis intersect_refusal_trace_end_ref_imp_intersect_refusal_trace_end_ref_tock intersect_refusal_trace_idempotent)
        qed
      next
        have "\<not> contains_refusal \<rho> \<Longrightarrow> \<rho> @ [[X]\<^sub>R, [Tock]\<^sub>E] \<in> P \<Longrightarrow> \<rho> @ [[X]\<^sub>R, [Tock]\<^sub>E] \<notin> P \<triangle>\<^sub>U Q \<Longrightarrow> False"
          unfolding UntimedInterruptTTT_def
        proof auto
          show "\<not> contains_refusal \<rho> \<Longrightarrow> \<rho> @ [[X]\<^sub>R, [Tock]\<^sub>E] \<in> P \<Longrightarrow>
            \<forall>p. contains_refusal p \<longrightarrow> p \<in> P \<longrightarrow> (\<exists>p'. p = p' @ [[Tick]\<^sub>E]) \<or> (\<exists>p' Y. p = p' @ [[Y]\<^sub>R]) \<or>
              (\<forall>q. q \<in> Q \<longrightarrow> (\<forall>Xa. [[Xa]\<^sub>R] \<in> Q \<longrightarrow> (\<exists>q' Y. q = [Y]\<^sub>R # q') \<or> 
                \<rho> @ [[X]\<^sub>R, [Tock]\<^sub>E] \<noteq> intersect_refusal_trace Xa p @ q)) \<Longrightarrow> False"
            using case_assms case_assms2 apply (erule_tac x="\<rho> @ [[X]\<^sub>R, [Tock]\<^sub>E]" in allE, auto)
            apply (metis append.assoc append.left_neutral append_Cons ctt_prefix_concat ctt_prefix_imp_prefix_subset not_contains_refusal_ctt_prefix_subset_end_nonref)
            apply (erule_tac x="[]" in allE, auto)
            using TT0_TT1_empty TT0_Q TT1_Q apply blast
            by (metis intersect_refusal_trace_end_ref_imp_intersect_refusal_trace_end_ref_tock intersect_refusal_trace_idempotent)
        qed
        then show "\<not> contains_refusal \<rho> \<Longrightarrow> \<rho> @ [[X]\<^sub>R, [Tock]\<^sub>E] \<in> P \<Longrightarrow> \<rho> @ [[X]\<^sub>R, [Tock]\<^sub>E] \<notin> P \<triangle>\<^sub>U Q \<Longrightarrow> \<rho> @ [[Tock]\<^sub>E] \<in> P \<triangle>\<^sub>U Q"
          by auto
      qed
      then have 1: "Y \<inter> {e. e \<noteq> Tock \<and> \<rho> @ [[e]\<^sub>E] \<in> P \<or> e = Tock \<and> \<rho> @ [[X]\<^sub>R, [e]\<^sub>E] \<in> P} = {}"
        using assm2 by auto
      have p_in_P: "p \<in> P"
        using case_assms TT1_P TT1_def ctt_prefix_concat ctt_prefix_imp_prefix_subset by blast
      have p_end: "(\<nexists>p'. p = p' @ [[Tick]\<^sub>E]) \<and> (\<nexists>p' Y. p = p' @ [[Y]\<^sub>R])"
      proof -
        have "ttWF (p @ [[Z]\<^sub>R])"
          by (simp add: P_wf case_assms(1))
        also have "(\<exists>p'. p = p' @ [[Tick]\<^sub>E]) \<or> (\<exists>p' Y. p = p' @ [[Y]\<^sub>R]) \<or> (\<exists>p'. p = p' @ [[Tock]\<^sub>E]) \<or> (\<exists>p' e. p = p' @ [[Event e]\<^sub>E]) \<or> p = []"
          by (metis cttevent.exhaust cttobs.exhaust rev_exhaust)
        then show ?thesis
          using calculation
        proof auto
          fix p'a
          show "ttWF (p'a @ [[Tick]\<^sub>E, [Z]\<^sub>R]) \<Longrightarrow> False"
            by (induct p'a rule:ttWF.induct, auto)
        next
          fix p'a Ya
          show "ttWF (p'a @ [[Ya]\<^sub>R, [Z]\<^sub>R]) \<Longrightarrow> False"
            by (induct p'a rule:ttWF.induct, auto)
        qed
      qed
      have \<rho>_contains_refusal_imp_p_contains_refusal: "contains_refusal \<rho> \<Longrightarrow> contains_refusal p"
        by (metis append_Nil2 case_assms(3) case_assms2 ctt_prefix_concat ctt_prefix_imp_prefix_subset intersect_refusal_trace_end_ref_imp_intersect_refusal_trace_end_event not_contains_refusal_append_event not_contains_refusal_ctt_prefix_subset not_contains_refusal_intersect_refusal_trace)
      have \<rho>_not_contains_refusal_imp_p_not_contains_refusal: "\<not> contains_refusal \<rho> \<Longrightarrow> \<not> contains_refusal p"
        by (metis append_Nil2 case_assms(3) case_assms2 contains_refusal_ctt_subset ctt_prefix_concat ctt_prefix_imp_prefix_subset intersect_refusal_trace_end_ref_imp_intersect_refusal_trace_end_event intersect_refusal_trace_subset not_contains_refusal_append_event not_contains_refusal_ctt_prefix_subset)
      have "{e. e \<noteq> Tock \<and> [[e]\<^sub>E] \<in> Q \<or> e = Tock \<and> [[W]\<^sub>R, [e]\<^sub>E] \<in> Q}
        \<subseteq> {e. e \<noteq> Tock \<and> \<rho> @ [[e]\<^sub>E] \<in> P \<triangle>\<^sub>U Q \<or> e = Tock \<and> \<rho> @ [[X]\<^sub>R, [e]\<^sub>E] \<in> P \<triangle>\<^sub>U Q}"
        unfolding UntimedInterruptTTT_def
      proof (cases "contains_refusal \<rho>", safe, simp_all)
        fix x
        assume case_assms3: "[[x]\<^sub>E] \<in> Q" "x \<noteq> Tock" "contains_refusal \<rho>"
        then show "\<forall>p. contains_refusal p \<longrightarrow> p \<in> P \<longrightarrow> (\<exists>p'. p = p' @ [[Tick]\<^sub>E]) \<or> (\<exists>p' Y. p = p' @ [[Y]\<^sub>R]) \<or>
            (\<forall>q. q \<in> Q \<longrightarrow> (\<forall>X. [[X]\<^sub>R] \<in> Q \<longrightarrow> (\<exists>q' Y. q = [Y]\<^sub>R # q') \<or> \<rho> @ [[x]\<^sub>E] \<noteq> intersect_refusal_trace X p @ q)) \<Longrightarrow>
          \<exists>p. p @ [[Tick]\<^sub>E] \<in> P \<and> contains_refusal p \<and> (\<exists>X. [[X]\<^sub>R] \<in> Q \<and> \<rho> @ [[x]\<^sub>E] = intersect_refusal_trace X (p @ [[Tick]\<^sub>E]))"
          using p_in_P \<rho>_contains_refusal_imp_p_contains_refusal p_end case_assms case_assms2
          apply (erule_tac x="p" in allE, auto, erule_tac x="[[x]\<^sub>E]" in allE, auto, erule_tac x="[[W]\<^sub>R]" in allE, auto)
          by (meson eq_intersect_refusal_trace_append intersect_refusal_trace_end_ref_imp_intersect_refusal_trace_end_event)
      next
        fix x
        assume case_assms3: "[[x]\<^sub>E] \<in> Q" "x \<noteq> Tock" "contains_refusal \<rho>"
        then show "\<forall>p. contains_refusal p \<longrightarrow> p \<in> P \<longrightarrow> (\<exists>p'. p = p' @ [[Tick]\<^sub>E]) \<or> (\<exists>p' Y. p = p' @ [[Y]\<^sub>R]) \<or>
            (\<forall>q. q \<in> Q \<longrightarrow> (\<forall>X. [[X]\<^sub>R] \<in> Q \<longrightarrow> (\<exists>q' Y. q = [Y]\<^sub>R # q') \<or> \<rho> @ [[x]\<^sub>E] \<noteq> intersect_refusal_trace X p @ q)) \<Longrightarrow>
          \<exists>p. p @ [[Tick]\<^sub>E] \<in> P \<and> contains_refusal p \<and> (\<exists>X. [[X]\<^sub>R] \<in> Q \<and> \<rho> @ [[x]\<^sub>E] = intersect_refusal_trace X (p @ [[Tick]\<^sub>E]))"
          using p_in_P \<rho>_contains_refusal_imp_p_contains_refusal p_end case_assms case_assms2
          apply (erule_tac x="p" in allE, auto, erule_tac x="[[x]\<^sub>E]" in allE, auto, erule_tac x="[[W]\<^sub>R]" in allE, auto)
          by (meson eq_intersect_refusal_trace_append intersect_refusal_trace_end_ref_imp_intersect_refusal_trace_end_event)
      next
        fix x
        assume case_assms3: "[[x]\<^sub>E] \<in> Q" "x \<noteq> Tock" "\<not> contains_refusal \<rho>"
        then show "\<forall>p. p \<in> P \<longrightarrow> (\<exists>p'. p = p' @ [[Tick]\<^sub>E]) \<or> (\<exists>p' Y. p = p' @ [[Y]\<^sub>R]) \<or> contains_refusal p \<or>
            (\<forall>q. q \<in> Q \<longrightarrow> (\<exists>q' Y. q = [Y]\<^sub>R # q') \<or> \<rho> @ [[x]\<^sub>E] \<noteq> p @ q) \<Longrightarrow>
          \<exists>p. p @ [[Tick]\<^sub>E] \<in> P \<and> contains_refusal p \<and> (\<exists>X. [[X]\<^sub>R] \<in> Q \<and> \<rho> @ [[x]\<^sub>E] = intersect_refusal_trace X (p @ [[Tick]\<^sub>E]))"
          using p_in_P \<rho>_not_contains_refusal_imp_p_not_contains_refusal p_end case_assms case_assms2
          apply (erule_tac x="p" in allE, auto, erule_tac x="[[x]\<^sub>E]" in allE, auto, erule_tac x="[[W]\<^sub>R]" in allE, auto)
          by (metis butlast_snoc intersect_refusal_trace_end_ref_imp_intersect_refusal_trace_end_event not_contains_refusal_append_event not_contains_refusal_intersect_refusal_trace)
      next
        fix x
        assume case_assms3: "[[x]\<^sub>E] \<in> Q" "x \<noteq> Tock" "\<not> contains_refusal \<rho>"
        then show "\<forall>p. p \<in> P \<longrightarrow> (\<exists>p'. p = p' @ [[Tick]\<^sub>E]) \<or> (\<exists>p' Y. p = p' @ [[Y]\<^sub>R]) \<or> contains_refusal p \<or>
            (\<forall>q. q \<in> Q \<longrightarrow> (\<exists>q' Y. q = [Y]\<^sub>R # q') \<or> \<rho> @ [[x]\<^sub>E] \<noteq> p @ q) \<Longrightarrow>
          \<exists>p. p @ [[Tick]\<^sub>E] \<in> P \<and> contains_refusal p \<and> (\<exists>X. [[X]\<^sub>R] \<in> Q \<and> \<rho> @ [[x]\<^sub>E] = intersect_refusal_trace X (p @ [[Tick]\<^sub>E]))"
          using p_in_P \<rho>_not_contains_refusal_imp_p_not_contains_refusal p_end case_assms case_assms2
          apply (erule_tac x="p" in allE, auto, erule_tac x="[[x]\<^sub>E]" in allE, auto, erule_tac x="[[W]\<^sub>R]" in allE, auto)
          by (metis butlast_snoc intersect_refusal_trace_end_ref_imp_intersect_refusal_trace_end_event not_contains_refusal_append_event not_contains_refusal_intersect_refusal_trace)
      next
        assume "[[W]\<^sub>R, [Tock]\<^sub>E] \<in> Q"
        then show "\<forall>p Xa. p @ [[Xa]\<^sub>R] \<in> P \<longrightarrow> (\<forall>Y q. [Y]\<^sub>R # q \<in> Q \<longrightarrow> \<rho> @ [[X]\<^sub>R, [Tock]\<^sub>E] \<noteq> intersect_refusal_trace Y (p @ [[Xa]\<^sub>R]) @ q) \<Longrightarrow> False"
          using case_assms case_assms2 by (erule_tac x="p" in allE, auto, erule_tac x="Z" in allE, auto, erule_tac x="W" in allE, erule_tac x="[[Tock]\<^sub>E]" in allE, auto)
      next
        assume "[[W]\<^sub>R, [Tock]\<^sub>E] \<in> Q"
        then show "\<forall>p Xa. p @ [[Xa]\<^sub>R] \<in> P \<longrightarrow> (\<forall>Y q. [Y]\<^sub>R # q \<in> Q \<longrightarrow> \<rho> @ [[X]\<^sub>R, [Tock]\<^sub>E] \<noteq> intersect_refusal_trace Y (p @ [[Xa]\<^sub>R]) @ q) \<Longrightarrow> False"
          using case_assms case_assms2 by (erule_tac x="p" in allE, auto, erule_tac x="Z" in allE, auto, erule_tac x="W" in allE, erule_tac x="[[Tock]\<^sub>E]" in allE, auto)
      next
        assume "[[W]\<^sub>R, [Tock]\<^sub>E] \<in> Q"
        then show "\<forall>p Xa. p @ [[Xa]\<^sub>R] \<in> P \<longrightarrow> (\<forall>Y q. [Y]\<^sub>R # q \<in> Q \<longrightarrow> \<rho> @ [[X]\<^sub>R, [Tock]\<^sub>E] \<noteq> intersect_refusal_trace Y (p @ [[Xa]\<^sub>R]) @ q) \<Longrightarrow>
          \<exists>p. p @ [[Tick]\<^sub>E] \<in> P \<and> contains_refusal p \<and> (\<exists>X. [[X]\<^sub>R] \<in> Q \<and> \<rho> @ [[Tock]\<^sub>E] = intersect_refusal_trace X (p @ [[Tick]\<^sub>E]))"
          using case_assms case_assms2 by (erule_tac x="p" in allE, auto, erule_tac x="Z" in allE, auto, erule_tac x="W" in allE, erule_tac x="[[Tock]\<^sub>E]" in allE, auto)
      next
        assume "[[W]\<^sub>R, [Tock]\<^sub>E] \<in> Q"
        then show "\<forall>p Xa. p @ [[Xa]\<^sub>R] \<in> P \<longrightarrow> (\<forall>Y q. [Y]\<^sub>R # q \<in> Q \<longrightarrow> \<rho> @ [[X]\<^sub>R, [Tock]\<^sub>E] \<noteq> intersect_refusal_trace Y (p @ [[Xa]\<^sub>R]) @ q) \<Longrightarrow>
          \<exists>p. p @ [[Tick]\<^sub>E] \<in> P \<and> contains_refusal p \<and> (\<exists>X. [[X]\<^sub>R] \<in> Q \<and> \<rho> @ [[Tock]\<^sub>E] = intersect_refusal_trace X (p @ [[Tick]\<^sub>E]))"
          using case_assms case_assms2 by (erule_tac x="p" in allE, auto, erule_tac x="Z" in allE, auto, erule_tac x="W" in allE, erule_tac x="[[Tock]\<^sub>E]" in allE, auto)
      qed
      then have 2: "Y \<inter> {e. e \<noteq> Tock \<and> [[e]\<^sub>E] \<in> Q \<or> e = Tock \<and> [[W]\<^sub>R, [e]\<^sub>E] \<in> Q} = {}"
        using assm2 by auto
      have 3: "\<rho> @ [[X]\<^sub>R] \<in> P"
        using TT1_P TT1_def case_assms(1) case_assms(3) case_assms2 intersect_refusal_trace_prefix_subset by fastforce
      have 4: "\<rho> @ [[X \<union> Y]\<^sub>R] \<in> P"
        using 1 3 TT2_P case_assms case_assms2 unfolding TT2_def by auto
      have 5: "[[W \<union> Y]\<^sub>R] \<in> Q"
        using 2 TT2_Q case_assms(2) case_assms2 unfolding TT2_def by (erule_tac x="[]" in allE, auto)
      have 6: "\<rho> @ [[X \<union> Y]\<^sub>R] = intersect_refusal_trace (W \<union> Y) (\<rho> @ [[X \<union> Y]\<^sub>R])"
      proof -
        have 1: "\<rho> @ [[X]\<^sub>R] = intersect_refusal_trace W (\<rho> @ [[X]\<^sub>R])"
          by (simp add: case_assms(3) case_assms2 intersect_refusal_trace_idempotent)
        have 2: "\<rho> = intersect_refusal_trace W \<rho>"
          using "1" eq_intersect_refusal_trace_append by auto
        then have 3: "\<rho> = intersect_refusal_trace (W \<union> Y) \<rho>"
          using intersect_refusal_trace_idempotent_widen_refusal by blast
        have 4: "[[X]\<^sub>R] = intersect_refusal_trace W [[X]\<^sub>R]"
          using "1" eq_intersect_refusal_trace_same_front by blast
        then have 5: "[[X \<union> Y]\<^sub>R] = intersect_refusal_trace (W \<union> Y) [[X \<union> Y]\<^sub>R]"
          by auto
        then show ?thesis
          using "3" intersect_refusal_trace_concat by blast
      qed
      show "\<rho> @ [[X \<union> Y]\<^sub>R] \<in> P \<triangle>\<^sub>U Q"
        unfolding UntimedInterruptTTT_def
      proof auto
        show "\<forall>p Xa. p @ [[Xa]\<^sub>R] \<in> P \<longrightarrow> (\<forall>Ya q. [Ya]\<^sub>R # q \<in> Q \<longrightarrow> \<rho> @ [[X \<union> Y]\<^sub>R] \<noteq> intersect_refusal_trace Ya (p @ [[Xa]\<^sub>R]) @ q) \<Longrightarrow>
          \<exists>p. p \<in> P \<and> (\<forall>p'. p \<noteq> p' @ [[Tick]\<^sub>E]) \<and> (\<forall>p' Y. p \<noteq> p' @ [[Y]\<^sub>R]) \<and> contains_refusal p \<and>
            (\<exists>q Xa. [[Xa]\<^sub>R] \<in> Q \<and> q \<in> Q \<and> (\<forall>q' Y. q \<noteq> [Y]\<^sub>R # q') \<and> \<rho> @ [[X \<union> Y]\<^sub>R] = intersect_refusal_trace Xa p @ q) "
          using case_assms case_assms2 4 5 6 by (erule_tac x="\<rho>" in allE, erule_tac x="X \<union> Y" in allE, auto, erule_tac x="W \<union> Y" in allE, auto)
      qed
    next
      fix q'
      assume case_assms2: "q = q' @ [[X]\<^sub>R]"
      have "{e. e \<noteq> Tock \<and> [W]\<^sub>R # q' @ [[e]\<^sub>E] \<in> Q \<or> e = Tock \<and> [W]\<^sub>R # q' @ [[X]\<^sub>R, [e]\<^sub>E] \<in> Q} \<subseteq> {e. e \<noteq> Tock \<and> \<rho> @ [[e]\<^sub>E] \<in> P \<triangle>\<^sub>U Q \<or> e = Tock \<and> \<rho> @ [[X]\<^sub>R, [e]\<^sub>E] \<in> P \<triangle>\<^sub>U Q}"
        unfolding UntimedInterruptTTT_def
      proof (safe, simp_all)
        fix x
        assume "[W]\<^sub>R # q' @ [[x]\<^sub>E] \<in> Q" "x \<noteq> Tock"
        then show "\<forall>p X. p @ [[X]\<^sub>R] \<in> P \<longrightarrow> (\<forall>Y q. [Y]\<^sub>R # q \<in> Q \<longrightarrow> \<rho> @ [[x]\<^sub>E] \<noteq> intersect_refusal_trace Y (p @ [[X]\<^sub>R]) @ q) \<Longrightarrow>
          \<exists>p. p @ [[Tick]\<^sub>E] \<in> P \<and> contains_refusal p \<and> (\<exists>X. [[X]\<^sub>R] \<in> Q \<and> \<rho> @ [[x]\<^sub>E] = intersect_refusal_trace X (p @ [[Tick]\<^sub>E]))"
          using case_assms case_assms2 by (erule_tac x="p" in allE, erule_tac x="Z" in allE, auto)
      next
        fix x
        assume "[W]\<^sub>R # q' @ [[x]\<^sub>E] \<in> Q" "x \<noteq> Tock"
        then show "\<forall>p X. p @ [[X]\<^sub>R] \<in> P \<longrightarrow> (\<forall>Y q. [Y]\<^sub>R # q \<in> Q \<longrightarrow> \<rho> @ [[x]\<^sub>E] \<noteq> intersect_refusal_trace Y (p @ [[X]\<^sub>R]) @ q) \<Longrightarrow>
          \<exists>p. p @ [[Tick]\<^sub>E] \<in> P \<and> contains_refusal p \<and> (\<exists>X. [[X]\<^sub>R] \<in> Q \<and> \<rho> @ [[x]\<^sub>E] = intersect_refusal_trace X (p @ [[Tick]\<^sub>E]))"
          using case_assms case_assms2 by (erule_tac x="p" in allE, erule_tac x="Z" in allE, auto)
      next
        assume "[W]\<^sub>R # q' @ [[X]\<^sub>R, [Tock]\<^sub>E] \<in> Q"
        then show "\<forall>p Xa. p @ [[Xa]\<^sub>R] \<in> P \<longrightarrow> (\<forall>Y q. [Y]\<^sub>R # q \<in> Q \<longrightarrow> \<rho> @ [[X]\<^sub>R, [Tock]\<^sub>E] \<noteq> intersect_refusal_trace Y (p @ [[Xa]\<^sub>R]) @ q) \<Longrightarrow> False"
          using case_assms case_assms2 by (erule_tac x="p" in allE, erule_tac x="Z" in allE, auto)
      next
        assume "[W]\<^sub>R # q' @ [[X]\<^sub>R, [Tock]\<^sub>E] \<in> Q"
        then show "\<forall>p Xa. p @ [[Xa]\<^sub>R] \<in> P \<longrightarrow> (\<forall>Y q. [Y]\<^sub>R # q \<in> Q \<longrightarrow> \<rho> @ [[X]\<^sub>R, [Tock]\<^sub>E] \<noteq> intersect_refusal_trace Y (p @ [[Xa]\<^sub>R]) @ q) \<Longrightarrow>
          \<exists>p. p @ [[Tick]\<^sub>E] \<in> P \<and> contains_refusal p \<and> (\<exists>X. [[X]\<^sub>R] \<in> Q \<and> \<rho> @ [[Tock]\<^sub>E] = intersect_refusal_trace X (p @ [[Tick]\<^sub>E]))"
          using case_assms case_assms2 by (erule_tac x="p" in allE, erule_tac x="Z" in allE, auto)
      qed
      then have "Y \<inter> {e. e \<noteq> Tock \<and> [W]\<^sub>R # q' @ [[e]\<^sub>E] \<in> Q \<or> e = Tock \<and> [W]\<^sub>R # q' @ [[X]\<^sub>R, [e]\<^sub>E] \<in> Q} = {}"
        using assm2 by auto
      then have "[W]\<^sub>R # q' @ [[X \<union> Y]\<^sub>R] \<in> Q"
        using case_assms case_assms2 TT2_Q unfolding TT2_def by (erule_tac x="[W]\<^sub>R # q'" in allE, auto)
      then show "\<rho> @ [[X \<union> Y]\<^sub>R] \<in> P \<triangle>\<^sub>U Q"
        unfolding UntimedInterruptTTT_def
      proof auto
        show "[W]\<^sub>R # q' @ [[X \<union> Y]\<^sub>R] \<in> Q \<Longrightarrow>
          \<forall>p Xa. p @ [[Xa]\<^sub>R] \<in> P \<longrightarrow> (\<forall>Ya q. [Ya]\<^sub>R # q \<in> Q \<longrightarrow> \<rho> @ [[X \<union> Y]\<^sub>R] \<noteq> intersect_refusal_trace Ya (p @ [[Xa]\<^sub>R]) @ q) \<Longrightarrow>
          \<exists>p. p \<in> P \<and> (\<forall>p'. p \<noteq> p' @ [[Tick]\<^sub>E]) \<and> (\<forall>p' Y. p \<noteq> p' @ [[Y]\<^sub>R]) \<and> contains_refusal p \<and> 
            (\<exists>q Xa. [[Xa]\<^sub>R] \<in> Q \<and> q \<in> Q \<and> (\<forall>q' Y. q \<noteq> [Y]\<^sub>R # q') \<and> \<rho> @ [[X \<union> Y]\<^sub>R] = intersect_refusal_trace Xa p @ q)"
          using case_assms case_assms2 by (erule_tac x="p" in allE, erule_tac x="Z" in allE, auto)
      qed
    qed
  next
    fix p q Z
    assume case_assms: "p \<in> P" "\<forall>p'. p \<noteq> p' @ [[Tick]\<^sub>E]" "\<forall>p' Y. p \<noteq> p' @ [[Y]\<^sub>R]" "contains_refusal p" "[[Z]\<^sub>R] \<in> Q"
      "q @ [[X]\<^sub>R] \<in> Q" "q \<noteq> []" "\<forall>q' Y. q \<noteq> [Y]\<^sub>R # q'" "\<rho> = intersect_refusal_trace Z p @ q"
    have "{e. e \<noteq> Tock \<and> q @ [[e]\<^sub>E] \<in> Q \<or> e = Tock \<and> q @ [[X]\<^sub>R, [e]\<^sub>E] \<in> Q} \<subseteq> {e. e \<noteq> Tock \<and> \<rho> @ [[e]\<^sub>E] \<in> P \<triangle>\<^sub>U Q \<or> e = Tock \<and> \<rho> @ [[X]\<^sub>R, [e]\<^sub>E] \<in> P \<triangle>\<^sub>U Q}"
      unfolding UntimedInterruptTTT_def
    proof (safe, simp_all)
      fix x
      assume "q @ [[x]\<^sub>E] \<in> Q" "x \<noteq> Tock"
      then show "\<forall>p. contains_refusal p \<longrightarrow> p \<in> P \<longrightarrow> (\<exists>p'. p = p' @ [[Tick]\<^sub>E]) \<or> (\<exists>p' Y. p = p' @ [[Y]\<^sub>R]) \<or>
          (\<forall>q. q \<in> Q \<longrightarrow> (\<forall>X. [[X]\<^sub>R] \<in> Q \<longrightarrow> (\<exists>q' Y. q = [Y]\<^sub>R # q') \<or> \<rho> @ [[x]\<^sub>E] \<noteq> intersect_refusal_trace X p @ q)) \<Longrightarrow>
        \<exists>p. p @ [[Tick]\<^sub>E] \<in> P \<and> contains_refusal p \<and> (\<exists>X. [[X]\<^sub>R] \<in> Q \<and> \<rho> @ [[x]\<^sub>E] = intersect_refusal_trace X (p @ [[Tick]\<^sub>E]))"
        using case_assms by (erule_tac x="p" in allE, auto, metis butlast.simps(2) butlast_snoc)
    next
      fix x
      assume "q @ [[x]\<^sub>E] \<in> Q" "x \<noteq> Tock"
      then show "\<forall>p. contains_refusal p \<longrightarrow> p \<in> P \<longrightarrow> (\<exists>p'. p = p' @ [[Tick]\<^sub>E]) \<or> (\<exists>p' Y. p = p' @ [[Y]\<^sub>R]) \<or>
          (\<forall>q. q \<in> Q \<longrightarrow> (\<forall>X. [[X]\<^sub>R] \<in> Q \<longrightarrow> (\<exists>q' Y. q = [Y]\<^sub>R # q') \<or> \<rho> @ [[x]\<^sub>E] \<noteq> intersect_refusal_trace X p @ q)) \<Longrightarrow>
        \<exists>p. p @ [[Tick]\<^sub>E] \<in> P \<and> contains_refusal p \<and> (\<exists>X. [[X]\<^sub>R] \<in> Q \<and> \<rho> @ [[x]\<^sub>E] = intersect_refusal_trace X (p @ [[Tick]\<^sub>E]))"
        using case_assms by (erule_tac x="p" in allE, auto, metis butlast.simps(2) butlast_snoc)
    next
      assume "q @ [[X]\<^sub>R, [Tock]\<^sub>E] \<in> Q"
      then show "\<forall>p. contains_refusal p \<longrightarrow> p \<in> P \<longrightarrow> (\<exists>p'. p = p' @ [[Tick]\<^sub>E]) \<or> (\<exists>p' Y. p = p' @ [[Y]\<^sub>R]) \<or>
        (\<forall>q. q \<in> Q \<longrightarrow> (\<forall>Xa. [[Xa]\<^sub>R] \<in> Q \<longrightarrow> (\<exists>q' Y. q = [Y]\<^sub>R # q') \<or> \<rho> @ [[X]\<^sub>R, [Tock]\<^sub>E] \<noteq> intersect_refusal_trace Xa p @ q)) \<Longrightarrow> False"
        using case_assms by (erule_tac x="p" in allE, auto, metis append_eq_Cons_conv)
    next
      assume "q @ [[X]\<^sub>R, [Tock]\<^sub>E] \<in> Q"
      then show "\<forall>p. contains_refusal p \<longrightarrow> p \<in> P \<longrightarrow> (\<exists>p'. p = p' @ [[Tick]\<^sub>E]) \<or> (\<exists>p' Y. p = p' @ [[Y]\<^sub>R]) \<or>
          (\<forall>q. q \<in> Q \<longrightarrow> (\<forall>Xa. [[Xa]\<^sub>R] \<in> Q \<longrightarrow> (\<exists>q' Y. q = [Y]\<^sub>R # q') \<or> \<rho> @ [[X]\<^sub>R, [Tock]\<^sub>E] \<noteq> intersect_refusal_trace Xa p @ q)) \<Longrightarrow>
        \<exists>p. p @ [[Tick]\<^sub>E] \<in> P \<and> contains_refusal p \<and> (\<exists>X. [[X]\<^sub>R] \<in> Q \<and> \<rho> @ [[Tock]\<^sub>E] = intersect_refusal_trace X (p @ [[Tick]\<^sub>E]))"
        using case_assms by (erule_tac x="p" in allE, auto, metis append_eq_Cons_conv)
    qed
    then have "Y \<inter> {e. e \<noteq> Tock \<and> q @ [[e]\<^sub>E] \<in> Q \<or> e = Tock \<and> q @ [[X]\<^sub>R, [e]\<^sub>E] \<in> Q} = {}"
      using assm2 by auto
    then have "q @ [[X \<union> Y]\<^sub>R] \<in> Q"
      using TT2_Q case_assms(6) unfolding TT2_def by auto
    then show "intersect_refusal_trace Z p @ q @ [[X \<union> Y]\<^sub>R] \<in> P \<triangle>\<^sub>U Q"
      unfolding UntimedInterruptTTT_def
    proof (safe, simp)
      show "q @ [[X \<union> Y]\<^sub>R] \<in> Q \<Longrightarrow>
        \<forall>pa. contains_refusal pa \<longrightarrow> pa \<in> P \<longrightarrow> (\<exists>p'. pa = p' @ [[Tick]\<^sub>E]) \<or> (\<exists>p' Y. pa = p' @ [[Y]\<^sub>R]) \<or>
          (\<forall>qa. qa \<in> Q \<longrightarrow> (\<forall>Xa. [[Xa]\<^sub>R] \<in> Q \<longrightarrow> (\<exists>q' Y. qa = [Y]\<^sub>R # q') \<or>
            intersect_refusal_trace Z p @ q @ [[X \<union> Y]\<^sub>R] \<noteq> intersect_refusal_trace Xa pa @ qa)) \<Longrightarrow>
        \<exists>pa. pa @ [[Tick]\<^sub>E] \<in> P \<and> contains_refusal pa \<and>
          (\<exists>Xa. [[Xa]\<^sub>R] \<in> Q \<and> intersect_refusal_trace Z p @ q @ [[X \<union> Y]\<^sub>R] = intersect_refusal_trace Xa (pa @ [[Tick]\<^sub>E]))"
        using case_assms by (erule_tac x="p" in allE, auto, metis append_eq_Cons_conv)
    qed
  next
    fix p q
    assume case_assms: "p \<in> P" "\<forall>p'. p \<noteq> p' @ [[Tick]\<^sub>E]" "\<forall>p' Y. p \<noteq> p' @ [[Y]\<^sub>R]" "\<not> contains_refusal p"
      "q @ [[X]\<^sub>R] \<in> Q" "\<forall>q' Y. q \<noteq> [Y]\<^sub>R # q'" "\<rho> = p @ q" "q \<noteq> []"
    have "{e. e \<noteq> Tock \<and> q @ [[e]\<^sub>E] \<in> Q \<or> e = Tock \<and> q @ [[X]\<^sub>R, [e]\<^sub>E] \<in> Q} \<subseteq> {e. e \<noteq> Tock \<and> \<rho> @ [[e]\<^sub>E] \<in> P \<triangle>\<^sub>U Q \<or> e = Tock \<and> \<rho> @ [[X]\<^sub>R, [e]\<^sub>E] \<in> P \<triangle>\<^sub>U Q}"
      unfolding UntimedInterruptTTT_def
    proof (safe, simp_all)
      fix x
      assume "q @ [[x]\<^sub>E] \<in> Q" "x \<noteq> Tock"
      then show "\<forall>p. p \<in> P \<longrightarrow> (\<exists>p'. p = p' @ [[Tick]\<^sub>E]) \<or> (\<exists>p' Y. p = p' @ [[Y]\<^sub>R]) \<or> contains_refusal p \<or>
          (\<forall>q. q \<in> Q \<longrightarrow> (\<exists>q' Y. q = [Y]\<^sub>R # q') \<or> \<rho> @ [[x]\<^sub>E] \<noteq> p @ q) \<Longrightarrow>
        \<exists>p. p @ [[Tick]\<^sub>E] \<in> P \<and> contains_refusal p \<and> (\<exists>X. [[X]\<^sub>R] \<in> Q \<and> \<rho> @ [[x]\<^sub>E] = intersect_refusal_trace X (p @ [[Tick]\<^sub>E]))"
        using case_assms by (erule_tac x="p" in allE, auto, metis Cons_eq_append_conv)
    next
      fix x
      assume "q @ [[x]\<^sub>E] \<in> Q" "x \<noteq> Tock"
      then show "\<forall>p. p \<in> P \<longrightarrow> (\<exists>p'. p = p' @ [[Tick]\<^sub>E]) \<or> (\<exists>p' Y. p = p' @ [[Y]\<^sub>R]) \<or> contains_refusal p \<or>
          (\<forall>q. q \<in> Q \<longrightarrow> (\<exists>q' Y. q = [Y]\<^sub>R # q') \<or> \<rho> @ [[x]\<^sub>E] \<noteq> p @ q) \<Longrightarrow>
        \<exists>p. p @ [[Tick]\<^sub>E] \<in> P \<and> contains_refusal p \<and> (\<exists>X. [[X]\<^sub>R] \<in> Q \<and> \<rho> @ [[x]\<^sub>E] = intersect_refusal_trace X (p @ [[Tick]\<^sub>E]))"
        using case_assms by (erule_tac x="p" in allE, auto, metis Cons_eq_append_conv)
    next
      assume case_assms2: "q @ [[X]\<^sub>R, [Tock]\<^sub>E] \<in> Q"
      then show "\<forall>p. p \<in> P \<longrightarrow> (\<exists>p'. p = p' @ [[Tick]\<^sub>E]) \<or> (\<exists>p' Y. p = p' @ [[Y]\<^sub>R]) \<or> contains_refusal p \<or>
          (\<forall>q. q \<in> Q \<longrightarrow> (\<exists>q' Y. q = [Y]\<^sub>R # q') \<or> \<rho> @ [[X]\<^sub>R, [Tock]\<^sub>E] \<noteq> p @ q) \<Longrightarrow> False"
        using case_assms by (erule_tac x="p" in allE, auto, metis Cons_eq_append_conv)
    next
      assume case_assms2: "q @ [[X]\<^sub>R, [Tock]\<^sub>E] \<in> Q"
      then show "\<forall>p. p \<in> P \<longrightarrow> (\<exists>p'. p = p' @ [[Tick]\<^sub>E]) \<or> (\<exists>p' Y. p = p' @ [[Y]\<^sub>R]) \<or> contains_refusal p \<or>
          (\<forall>q. q \<in> Q \<longrightarrow> (\<exists>q' Y. q = [Y]\<^sub>R # q') \<or> \<rho> @ [[X]\<^sub>R, [Tock]\<^sub>E] \<noteq> p @ q) \<Longrightarrow>
        \<exists>p. p @ [[Tick]\<^sub>E] \<in> P \<and> contains_refusal p \<and> (\<exists>X. [[X]\<^sub>R] \<in> Q \<and> \<rho> @ [[Tock]\<^sub>E] = intersect_refusal_trace X (p @ [[Tick]\<^sub>E]))"
        using case_assms by (erule_tac x="p" in allE, auto, erule_tac x="q @ [[X]\<^sub>R, [Tock]\<^sub>E]" in allE, auto, metis Cons_eq_append_conv)
    qed
    then have "Y \<inter> {e. e \<noteq> Tock \<and> q @ [[e]\<^sub>E] \<in> Q \<or> e = Tock \<and> q @ [[X]\<^sub>R, [e]\<^sub>E] \<in> Q} = {}"
      using assm2 by auto
    then have "q @ [[X \<union> Y]\<^sub>R] \<in> Q"
      using TT2_Q case_assms unfolding TT2_def by auto
    then show "p @ q @ [[X \<union> Y]\<^sub>R] \<in> P \<triangle>\<^sub>U Q"
      unfolding UntimedInterruptTTT_def
    proof (safe, simp)
      show "q @ [[X \<union> Y]\<^sub>R] \<in> Q \<Longrightarrow>
        \<forall>pa. pa \<in> P \<longrightarrow> (\<exists>p'. pa = p' @ [[Tick]\<^sub>E]) \<or> (\<exists>p' Y. pa = p' @ [[Y]\<^sub>R]) \<or> contains_refusal pa \<or>
          (\<forall>qa. qa \<in> Q \<longrightarrow> (\<exists>q' Y. qa = [Y]\<^sub>R # q') \<or> p @ q @ [[X \<union> Y]\<^sub>R] \<noteq> pa @ qa) \<Longrightarrow>
        \<exists>pa. pa @ [[Tick]\<^sub>E] \<in> P \<and> contains_refusal pa \<and>
          (\<exists>Xa. [[Xa]\<^sub>R] \<in> Q \<and> p @ q @ [[X \<union> Y]\<^sub>R] = intersect_refusal_trace Xa (pa @ [[Tick]\<^sub>E]))"
        using case_assms by (erule_tac x="p" in allE, auto, metis append_eq_Cons_conv)
    qed
  qed
qed 

lemma TT2s_UntimedInterrupt:
  assumes P_wf: "\<forall> x\<in>P. ttWF x" and Q_wf: "\<forall> x\<in>Q. ttWF x"
  assumes TT0_Q: "TT0 Q"
  assumes TT1_P: "TT1 P" and TT1_Q: "TT1 Q"
  assumes TT2_P: "TT2 P" and TT2_Q: "TT2 Q"
  assumes TT2s_P: "TT2s P" and TT2s_Q: "TT2s Q"
  shows "TT2s (P \<triangle>\<^sub>U Q)"
  unfolding TT2s_def
proof (auto)
  fix \<rho> \<sigma> X Y
  assume assm1: "\<rho> @ [X]\<^sub>R # \<sigma> \<in> P \<triangle>\<^sub>U Q"
  assume assm2: "Y \<inter> {e. e \<noteq> Tock \<and> \<rho> @ [[e]\<^sub>E] \<in> P \<triangle>\<^sub>U Q \<or> e = Tock \<and> \<rho> @ [[X]\<^sub>R, [e]\<^sub>E] \<in> P \<triangle>\<^sub>U Q} = {}"
  have \<rho>_X_\<sigma>_wf: "ttWF (\<rho> @ [X]\<^sub>R # \<sigma>)"
    using P_wf Q_wf UntimedInterruptTTT_wf assm1 by blast
  then have \<sigma>_cases: "\<sigma> = [] \<or> (\<exists> \<sigma>'. \<sigma> = [Tock]\<^sub>E # \<sigma>')"
    by (cases \<sigma> rule:ttWF.cases, auto, (induct \<rho> rule:ttWF.induct, auto)+)
  have "ttWF (\<rho> @ [[X]\<^sub>R])"
    using \<rho>_X_\<sigma>_wf append_self_conv2 ttWF_prefix_is_ttWF by fastforce
  then have \<rho>_non_tick_refusal: "(\<forall>p'. \<rho> \<noteq> p' @ [[Tick]\<^sub>E]) \<and> (\<forall>p' Y. \<rho> \<noteq> p' @ [[Y]\<^sub>R])"
  proof auto
    fix p'
    show "ttWF (p' @ [[Tick]\<^sub>E, [X]\<^sub>R]) \<Longrightarrow> False"
      by (induct p' rule:ttWF.induct, auto)
  next
    fix p' Y
    show "ttWF (p' @ [[Y]\<^sub>R, [X]\<^sub>R]) \<Longrightarrow> False"
      by (induct p' rule:ttWF.induct, auto)
  qed
  show "\<rho> @ [X \<union> Y]\<^sub>R # \<sigma> \<in> P \<triangle>\<^sub>U Q"
    using \<sigma>_cases
  proof auto
    assume case_assm: "\<sigma> = []"
    have "TT2 (P \<triangle>\<^sub>U Q)"
      using TT0_Q TT1_P TT1_Q TT2_P TT2_Q TT2_UntimedInterrupt P_wf by blast
    then show "\<sigma> = [] \<Longrightarrow> \<rho> @ [[X \<union> Y]\<^sub>R] \<in> P \<triangle>\<^sub>U Q"
      using assm1 assm2 case_assm unfolding TT2_def by auto
  next
    fix \<sigma>'
    assume case_assm: "\<sigma> = [Tock]\<^sub>E # \<sigma>'"
    have "(\<exists> p Z. p @ [[Tick]\<^sub>E] \<in> P \<and> contains_refusal p \<and> [[Z]\<^sub>R] \<in> Q \<and> \<rho> @ [X]\<^sub>R # [Tock]\<^sub>E # \<sigma>' = intersect_refusal_trace Z (p @ [[Tick]\<^sub>E]))
    \<or> (\<exists>p Z W q. p @ [[Z]\<^sub>R] \<in> P \<and> [W]\<^sub>R # q \<in> Q \<and> \<rho> @ [X]\<^sub>R # [Tock]\<^sub>E # \<sigma>' = intersect_refusal_trace W (p @ [[Z]\<^sub>R]) @ q)
    \<or> (\<exists>p q Z. p \<in> P \<and> (\<nexists>p'. p = p' @ [[Tick]\<^sub>E]) \<and> (\<nexists>p' Y. p = p' @ [[Y]\<^sub>R]) \<and> contains_refusal p
      \<and> [[Z]\<^sub>R] \<in> Q \<and> q \<in> Q \<and> (\<nexists>q' Y. q = [Y]\<^sub>R # q') \<and> \<rho> @ [X]\<^sub>R # [Tock]\<^sub>E # \<sigma>' = intersect_refusal_trace Z p @ q)
    \<or> (\<exists>p q. p \<in> P \<and> (\<nexists>p'. p = p' @ [[Tick]\<^sub>E]) \<and> (\<nexists>p' Y. p = p' @ [[Y]\<^sub>R]) \<and> \<not> contains_refusal p
      \<and> q \<in> Q \<and> (\<nexists>q' Y. q = [Y]\<^sub>R # q') \<and> \<rho> @ [X]\<^sub>R # [Tock]\<^sub>E # \<sigma>' = p @ q)"
      using case_assm assm1 unfolding UntimedInterruptTTT_def apply simp
    proof (safe, simp_all)
      fix p
      assume case_assm2: "p @ [[Tick]\<^sub>E] \<in> P" "\<not> contains_refusal p" "\<rho> @ [X]\<^sub>R # [Tock]\<^sub>E # \<sigma>' = p @ [[Tick]\<^sub>E]"
      obtain \<sigma>'' where "p = \<rho> @ [X]\<^sub>R # [Tock]\<^sub>E # \<sigma>''"
        by (metis butlast.simps(2) butlast_append butlast_snoc case_assm2(3) cttevent.distinct(5) cttobs.simps(1) last.simps last_appendR list.simps(3))
      then have "contains_refusal p"
        by (metis append.assoc append.left_neutral append_Cons ctt_prefix_concat ctt_prefix_imp_prefix_subset not_contains_refusal_ctt_prefix_subset_end_nonref)
      then show "\<exists>pa. pa \<in> P \<and> (\<forall>p'. pa \<noteq> p' @ [[Tick]\<^sub>E]) \<and> (\<forall>p' Y. pa \<noteq> p' @ [[Y]\<^sub>R]) \<and> contains_refusal pa \<and>
              (\<exists>q Z. [[Z]\<^sub>R] \<in> Q \<and> q \<in> Q \<and> (\<forall>q' Y. q \<noteq> [Y]\<^sub>R # q') \<and> p @ [[Tick]\<^sub>E] = intersect_refusal_trace Z pa @ q)"
        using case_assm2(2) by auto
    qed
    then show "\<rho> @ [X \<union> Y]\<^sub>R # [Tock]\<^sub>E # \<sigma>' \<in> P \<triangle>\<^sub>U Q"
    proof auto
      fix p Z
      assume case_assms: "p @ [[Tick]\<^sub>E] \<in> P" "contains_refusal p" "[[Z]\<^sub>R] \<in> Q" "\<rho> @ [X]\<^sub>R # [Tock]\<^sub>E # \<sigma>' = intersect_refusal_trace Z (p @ [[Tick]\<^sub>E])"
      have \<rho>_X_\<sigma>_ctt_subset_p: "\<rho> @ [X]\<^sub>R # [Tock]\<^sub>E # \<sigma>' \<subseteq>\<^sub>C p @ [[Tick]\<^sub>E]"
        using case_assms(4) intersect_refusal_trace_eq_imp_subset by blast
      have "\<exists> W \<rho>' \<sigma>''. p = \<rho>' @ [W]\<^sub>R # [Tock]\<^sub>E # \<sigma>''"
        using \<rho>_X_\<sigma>_ctt_subset_p apply -
        apply (induct \<rho> p rule:ctt_subset.induct, auto, metis append_Cons, metis append_Cons)
        using ctt_subset_same_length apply force
        apply (metis Nil_is_append_conv ctt_subset.simps(3) ctt_subset.simps(6) ctt_subset.simps(7) cttobs.exhaust neq_Nil_conv)
        apply (case_tac v, auto, case_tac va, auto, case_tac a, auto)
        by (rule_tac x="x2" in exI, rule_tac x="[]" in exI, rule_tac x="list" in exI, auto)
      then obtain W \<rho>' \<sigma>'' where p_def: "p = \<rho>' @ [W]\<^sub>R # [Tock]\<^sub>E # \<sigma>''"
        by auto
      have 1: "\<rho> @ [X]\<^sub>R # [Tock]\<^sub>E # \<sigma>' \<in> P"
        using TT1_P TT1_def case_assms(1) \<rho>_X_\<sigma>_ctt_subset_p ctt_subset_imp_prefix_subset by blast
      have "{e. e \<noteq> Tock \<and> \<rho> @ [[e]\<^sub>E] \<in> P \<or> e = Tock \<and> \<rho> @ [[X]\<^sub>R, [e]\<^sub>E] \<in> P}
          \<subseteq> {e. e \<noteq> Tock \<and> \<rho> @ [[e]\<^sub>E] \<in> P \<triangle>\<^sub>U Q \<or> e = Tock \<and> \<rho> @ [[X]\<^sub>R, [e]\<^sub>E] \<in> P \<triangle>\<^sub>U Q}"
      proof (auto)
        fix x
        assume case_assms2: "\<rho> @ [[x]\<^sub>E] \<in> P" "x \<noteq> Tock"
        then show "\<rho> @ [[x]\<^sub>E] \<in> P \<triangle>\<^sub>U Q"
          unfolding UntimedInterruptTTT_def
        proof (cases x, cases "contains_refusal \<rho>", safe, simp_all)
          fix x1
          assume case_assms3: "contains_refusal \<rho>" "\<rho> @ [[Event x1]\<^sub>E] \<in> P"
          then show "\<forall>p. contains_refusal p \<longrightarrow> p \<in> P \<longrightarrow> (\<exists>p'. p = p' @ [[Tick]\<^sub>E]) \<or> (\<exists>p' Y. p = p' @ [[Y]\<^sub>R]) \<or>
              (\<forall>q. q \<in> Q \<longrightarrow> (\<forall>X. [[X]\<^sub>R] \<in> Q \<longrightarrow> (\<exists>q' Y. q = [Y]\<^sub>R # q') \<or> \<rho> @ [[Event x1]\<^sub>E] \<noteq> intersect_refusal_trace X p @ q)) \<Longrightarrow>
            \<exists>p. p @ [[Tick]\<^sub>E] \<in> P \<and> contains_refusal p \<and> (\<exists>X. [[X]\<^sub>R] \<in> Q \<and> \<rho> @ [[Event x1]\<^sub>E] = intersect_refusal_trace X (p @ [[Tick]\<^sub>E]))"
            apply (erule_tac x="\<rho> @ [[Event x1]\<^sub>E]" in allE, auto)
            using ctt_prefix_concat ctt_prefix_imp_prefix_subset not_contains_refusal_ctt_prefix_subset apply blast
            apply (erule_tac x="[]" in allE, auto, simp add: TT0_TT1_empty TT0_Q TT1_Q)
            apply (erule_tac x="Z" in allE, auto)
            using case_assms(3) apply blast
            by (metis case_assms(4) eq_intersect_refusal_trace_append intersect_refusal_trace.simps(1) intersect_refusal_trace.simps(2) intersect_refusal_trace_concat intersect_refusal_trace_idempotent)
        next
          fix x1
          assume case_assms3: "\<not> contains_refusal \<rho>" "\<rho> @ [[Event x1]\<^sub>E] \<in> P"
          show "\<forall>p. p \<in> P \<longrightarrow> (\<exists>p'. p = p' @ [[Tick]\<^sub>E]) \<or> (\<exists>p' Y. p = p' @ [[Y]\<^sub>R]) \<or> contains_refusal p \<or>
              (\<forall>q. q \<in> Q \<longrightarrow> (\<exists>q' Y. q = [Y]\<^sub>R # q') \<or> \<rho> @ [[Event x1]\<^sub>E] \<noteq> p @ q) \<Longrightarrow>
            \<exists>p. p @ [[Tick]\<^sub>E] \<in> P \<and> contains_refusal p \<and> (\<exists>X. [[X]\<^sub>R] \<in> Q \<and> \<rho> @ [[Event x1]\<^sub>E] = intersect_refusal_trace X (p @ [[Tick]\<^sub>E]))"
            apply (erule_tac x="\<rho> @ [[Event x1]\<^sub>E]" in allE, auto)
            using TT0_TT1_empty TT0_Q TT1_Q case_assms3 not_contains_refusal_append_event by blast+
        next
          assume "\<rho> @ [[Tick]\<^sub>E] \<in> P" "contains_refusal \<rho>"
          then show "\<exists>p. p @ [[Tick]\<^sub>E] \<in> P \<and> contains_refusal p \<and> (\<exists>X. [[X]\<^sub>R] \<in> Q \<and> \<rho> @ [[Tick]\<^sub>E] = intersect_refusal_trace X (p @ [[Tick]\<^sub>E]))"
            apply (rule_tac x="\<rho>" in exI, auto, rule_tac x="Z" in exI, auto simp add: case_assms(3))
            by (metis case_assms(4) eq_intersect_refusal_trace_append intersect_refusal_trace.simps(1) intersect_refusal_trace.simps(2) intersect_refusal_trace_concat intersect_refusal_trace_idempotent)
        qed
      next
        fix x
        assume case_assms2: "\<rho> @ [[x]\<^sub>E] \<in> P" "x \<noteq> Tock"
        then show "\<rho> @ [[x]\<^sub>E] \<in> P \<triangle>\<^sub>U Q"
          unfolding UntimedInterruptTTT_def
        proof (cases x, cases "contains_refusal \<rho>", safe, simp_all)
          fix x1
          assume case_assms3: "contains_refusal \<rho>" "\<rho> @ [[Event x1]\<^sub>E] \<in> P"
          then show "\<forall>p. contains_refusal p \<longrightarrow> p \<in> P \<longrightarrow> (\<exists>p'. p = p' @ [[Tick]\<^sub>E]) \<or> (\<exists>p' Y. p = p' @ [[Y]\<^sub>R]) \<or>
              (\<forall>q. q \<in> Q \<longrightarrow> (\<forall>X. [[X]\<^sub>R] \<in> Q \<longrightarrow> (\<exists>q' Y. q = [Y]\<^sub>R # q') \<or> \<rho> @ [[Event x1]\<^sub>E] \<noteq> intersect_refusal_trace X p @ q)) \<Longrightarrow>
            \<exists>p. p @ [[Tick]\<^sub>E] \<in> P \<and> contains_refusal p \<and> (\<exists>X. [[X]\<^sub>R] \<in> Q \<and> \<rho> @ [[Event x1]\<^sub>E] = intersect_refusal_trace X (p @ [[Tick]\<^sub>E]))"
            apply (erule_tac x="\<rho> @ [[Event x1]\<^sub>E]" in allE, auto)
            using ctt_prefix_concat ctt_prefix_imp_prefix_subset not_contains_refusal_ctt_prefix_subset apply blast
            apply (erule_tac x="[]" in allE, auto, simp add: TT0_TT1_empty TT0_Q TT1_Q)
            apply (erule_tac x="Z" in allE, auto)
            using case_assms(3) apply blast
            by (metis case_assms(4) eq_intersect_refusal_trace_append intersect_refusal_trace.simps(1) intersect_refusal_trace.simps(2) intersect_refusal_trace_concat intersect_refusal_trace_idempotent)
        next
          fix x1
          assume case_assms3: "\<not> contains_refusal \<rho>" "\<rho> @ [[Event x1]\<^sub>E] \<in> P"
          show "\<forall>p. p \<in> P \<longrightarrow> (\<exists>p'. p = p' @ [[Tick]\<^sub>E]) \<or> (\<exists>p' Y. p = p' @ [[Y]\<^sub>R]) \<or> contains_refusal p \<or>
              (\<forall>q. q \<in> Q \<longrightarrow> (\<exists>q' Y. q = [Y]\<^sub>R # q') \<or> \<rho> @ [[Event x1]\<^sub>E] \<noteq> p @ q) \<Longrightarrow>
            \<exists>p. p @ [[Tick]\<^sub>E] \<in> P \<and> contains_refusal p \<and> (\<exists>X. [[X]\<^sub>R] \<in> Q \<and> \<rho> @ [[Event x1]\<^sub>E] = intersect_refusal_trace X (p @ [[Tick]\<^sub>E]))"
            apply (erule_tac x="\<rho> @ [[Event x1]\<^sub>E]" in allE, auto)
            using TT0_TT1_empty TT0_Q TT1_Q case_assms3 not_contains_refusal_append_event by blast+
        next
          assume "\<rho> @ [[Tick]\<^sub>E] \<in> P" "contains_refusal \<rho>"
          then show "\<exists>p. p @ [[Tick]\<^sub>E] \<in> P \<and> contains_refusal p \<and> (\<exists>X. [[X]\<^sub>R] \<in> Q \<and> \<rho> @ [[Tick]\<^sub>E] = intersect_refusal_trace X (p @ [[Tick]\<^sub>E]))"
            apply (rule_tac x="\<rho>" in exI, auto, rule_tac x="Z" in exI, auto simp add: case_assms(3))
            by (metis case_assms(4) eq_intersect_refusal_trace_append intersect_refusal_trace.simps(1) intersect_refusal_trace.simps(2) intersect_refusal_trace_concat intersect_refusal_trace_idempotent)
        qed
      next
        assume case_assms2: "\<rho> @ [[X]\<^sub>R, [Tock]\<^sub>E] \<in> P" "\<rho> @ [[X]\<^sub>R, [Tock]\<^sub>E] \<notin> P \<triangle>\<^sub>U Q"
        have 1: "\<rho> @ [X]\<^sub>R # [Tock]\<^sub>E # \<sigma>' = intersect_refusal_trace Z (\<rho> @ [X]\<^sub>R # [Tock]\<^sub>E # \<sigma>')"
            by (simp add: case_assms(4) intersect_refusal_trace_idempotent) 
        have "\<forall>p. contains_refusal p \<longrightarrow> p \<in> P \<longrightarrow> (\<exists>p'. p = p' @ [[Tick]\<^sub>E]) \<or> (\<exists>p' Y. p = p' @ [[Y]\<^sub>R]) \<or>
          (\<forall>q. q \<in> Q \<longrightarrow> (\<forall>Xa. [[Xa]\<^sub>R] \<in> Q \<longrightarrow> (\<exists>q' Y. q = [Y]\<^sub>R # q') \<or> \<rho> @ [[X]\<^sub>R, [Tock]\<^sub>E] \<noteq> intersect_refusal_trace Xa p @ q))"
          using case_assms2(2) unfolding UntimedInterruptTTT_def by (auto)
        then show "False"
          using case_assms case_assms2 apply (erule_tac x="\<rho> @ [[X]\<^sub>R, [Tock]\<^sub>E]" in allE, auto)
          apply (meson ctt_prefix_subset.simps(1) ctt_prefix_subset.simps(2) ctt_prefix_subset_same_front not_contains_refusal_ctt_prefix_subset_end_nonref subsetI)
          apply (erule_tac x="[]" in allE, auto)+
          using TT0_TT1_empty TT0_Q TT1_Q apply blast
          apply (erule_tac x="Z" in allE, auto)
          by (metis (no_types, lifting) "1" eq_intersect_refusal_trace_append eq_intersect_refusal_trace_same_front intersect_refusal_trace.simps(1) intersect_refusal_trace.simps(2) intersect_refusal_trace.simps(3) intersect_refusal_trace_concat list.inject)
      next
        assume case_assms2: "\<rho> @ [[X]\<^sub>R, [Tock]\<^sub>E] \<in> P" "\<rho> @ [[X]\<^sub>R, [Tock]\<^sub>E] \<notin> P \<triangle>\<^sub>U Q"
        have 1: "\<rho> @ [X]\<^sub>R # [Tock]\<^sub>E # \<sigma>' = intersect_refusal_trace Z (\<rho> @ [X]\<^sub>R # [Tock]\<^sub>E # \<sigma>')"
            by (simp add: case_assms(4) intersect_refusal_trace_idempotent) 
        have "\<forall>p. contains_refusal p \<longrightarrow> p \<in> P \<longrightarrow> (\<exists>p'. p = p' @ [[Tick]\<^sub>E]) \<or> (\<exists>p' Y. p = p' @ [[Y]\<^sub>R]) \<or>
          (\<forall>q. q \<in> Q \<longrightarrow> (\<forall>Xa. [[Xa]\<^sub>R] \<in> Q \<longrightarrow> (\<exists>q' Y. q = [Y]\<^sub>R # q') \<or> \<rho> @ [[X]\<^sub>R, [Tock]\<^sub>E] \<noteq> intersect_refusal_trace Xa p @ q))"
          using case_assms2(2) unfolding UntimedInterruptTTT_def by (auto)
        then show "\<rho> @ [[Tock]\<^sub>E] \<in> P \<triangle>\<^sub>U Q"
          using case_assms case_assms2 apply (erule_tac x="\<rho> @ [[X]\<^sub>R, [Tock]\<^sub>E]" in allE, auto)
          apply (meson ctt_prefix_subset.simps(1) ctt_prefix_subset.simps(2) ctt_prefix_subset_same_front not_contains_refusal_ctt_prefix_subset_end_nonref subsetI)
          apply (erule_tac x="[]" in allE, auto)+
          using TT0_TT1_empty TT0_Q TT1_Q apply blast
          apply (erule_tac x="Z" in allE, auto)
          by (metis (no_types, lifting) "1" eq_intersect_refusal_trace_append eq_intersect_refusal_trace_same_front intersect_refusal_trace.simps(1) intersect_refusal_trace.simps(2) intersect_refusal_trace.simps(3) intersect_refusal_trace_concat list.inject)
      qed
      then have 2: "Y \<inter> {e. e \<noteq> Tock \<and> \<rho> @ [[e]\<^sub>E] \<in> P \<or> e = Tock \<and> \<rho> @ [[X]\<^sub>R, [e]\<^sub>E] \<in> P} = {}"
        using assm2 subsetCE by auto
      have "{e. e \<noteq> Tock \<and> [[e]\<^sub>E] \<in> Q \<or> e = Tock \<and> [[Z]\<^sub>R, [e]\<^sub>E] \<in> Q}
          \<subseteq> {e. e \<noteq> Tock \<and> \<rho> @ [[e]\<^sub>E] \<in> P \<triangle>\<^sub>U Q \<or> e = Tock \<and> \<rho> @ [[X]\<^sub>R, [e]\<^sub>E] \<in> P \<triangle>\<^sub>U Q}"
      proof auto
        fix x
        assume case_assms2: "[[x]\<^sub>E] \<in> Q" "x \<noteq> Tock"
        then show "\<rho> @ [[x]\<^sub>E] \<in> P \<triangle>\<^sub>U Q"
        proof (cases "contains_refusal \<rho>", auto)
          assume case_assms3: "contains_refusal \<rho>"
          show "\<rho> @ [[x]\<^sub>E] \<in> P \<triangle>\<^sub>U Q"
            unfolding UntimedInterruptTTT_def
          proof (auto)
            show "\<forall>p. contains_refusal p \<longrightarrow> p \<in> P \<longrightarrow> (\<exists>p'. p = p' @ [[Tick]\<^sub>E]) \<or> (\<exists>p' Y. p = p' @ [[Y]\<^sub>R]) \<or>
              (\<forall>q. q \<in> Q \<longrightarrow> (\<forall>X. [[X]\<^sub>R] \<in> Q \<longrightarrow> (\<exists>q' Y. q = [Y]\<^sub>R # q') \<or> \<rho> @ [[x]\<^sub>E] \<noteq> intersect_refusal_trace X p @ q)) \<Longrightarrow>
              \<rho> @ [[Tick]\<^sub>E] \<in> P"
              using case_assms case_assms2 case_assms3 apply (erule_tac x="\<rho>" in allE, auto)
              apply (metis TT1_P TT1_def case_assms(1) case_assms(4) ctt_prefix_subset_front intersect_refusal_trace_prefix_subset)
              using \<rho>_non_tick_refusal apply (blast, blast)
              apply (erule_tac x="[[x]\<^sub>E]" in allE, auto) apply (erule_tac x="Z" in allE, auto)
              by (metis eq_intersect_refusal_trace_append intersect_refusal_trace_idempotent)
          next
            show "\<forall>p. contains_refusal p \<longrightarrow> p \<in> P \<longrightarrow> (\<exists>p'. p = p' @ [[Tick]\<^sub>E]) \<or> (\<exists>p' Y. p = p' @ [[Y]\<^sub>R]) \<or>
              (\<forall>q. q \<in> Q \<longrightarrow> (\<forall>X. [[X]\<^sub>R] \<in> Q \<longrightarrow> (\<exists>q' Y. q = [Y]\<^sub>R # q') \<or> \<rho> @ [[x]\<^sub>E] \<noteq> intersect_refusal_trace X p @ q)) \<Longrightarrow>
              False"
              using case_assms case_assms2 case_assms3 apply (erule_tac x="\<rho>" in allE, auto)
              apply (metis TT1_P TT1_def case_assms(1) case_assms(4) ctt_prefix_subset_front intersect_refusal_trace_prefix_subset)
              using \<rho>_non_tick_refusal apply (blast, blast)
              apply (erule_tac x="[[x]\<^sub>E]" in allE, auto) apply (erule_tac x="Z" in allE, auto)
              by (metis eq_intersect_refusal_trace_append intersect_refusal_trace_idempotent)
          next
            show "\<forall>p. contains_refusal p \<longrightarrow> p \<in> P \<longrightarrow> (\<exists>p'. p = p' @ [[Tick]\<^sub>E]) \<or> (\<exists>p' Y. p = p' @ [[Y]\<^sub>R]) \<or>
              (\<forall>q. q \<in> Q \<longrightarrow> (\<forall>X. [[X]\<^sub>R] \<in> Q \<longrightarrow> (\<exists>q' Y. q = [Y]\<^sub>R # q') \<or> \<rho> @ [[x]\<^sub>E] \<noteq> intersect_refusal_trace X p @ q)) \<Longrightarrow>
              x = Tick"
              using case_assms case_assms2 case_assms3 apply (erule_tac x="\<rho>" in allE, auto)
              apply (metis TT1_P TT1_def case_assms(1) case_assms(4) ctt_prefix_subset_front intersect_refusal_trace_prefix_subset)
              using \<rho>_non_tick_refusal apply (blast, blast)
              apply (erule_tac x="[[x]\<^sub>E]" in allE, auto) apply (erule_tac x="Z" in allE, auto)
              by (metis eq_intersect_refusal_trace_append intersect_refusal_trace_idempotent)
          qed
        next
          assume case_assms3: "\<not> contains_refusal \<rho>"
          show " \<rho> @ [[x]\<^sub>E] \<in> P \<triangle>\<^sub>U Q"
            unfolding UntimedInterruptTTT_def
          proof (auto)
            show "\<forall>p. p \<in> P \<longrightarrow> (\<exists>p'. p = p' @ [[Tick]\<^sub>E]) \<or> (\<exists>p' Y. p = p' @ [[Y]\<^sub>R]) \<or> contains_refusal p \<or>
              (\<forall>q. q \<in> Q \<longrightarrow> (\<exists>q' Y. q = [Y]\<^sub>R # q') \<or> \<rho> @ [[x]\<^sub>E] \<noteq> p @ q) \<Longrightarrow> \<rho> @ [[Tick]\<^sub>E] \<in> P"
              using case_assms case_assms2 case_assms3 apply (erule_tac x="\<rho>" in allE, auto)
              apply (metis TT1_P TT1_def case_assms(1) case_assms(4) ctt_prefix_subset_front intersect_refusal_trace_prefix_subset)
              using \<rho>_non_tick_refusal by (blast, blast)
          next
            show "\<forall>p. p \<in> P \<longrightarrow> (\<exists>p'. p = p' @ [[Tick]\<^sub>E]) \<or> (\<exists>p' Y. p = p' @ [[Y]\<^sub>R]) \<or> contains_refusal p \<or>
              (\<forall>q. q \<in> Q \<longrightarrow> (\<exists>q' Y. q = [Y]\<^sub>R # q') \<or> \<rho> @ [[x]\<^sub>E] \<noteq> p @ q) \<Longrightarrow> False"
              using case_assms case_assms2 case_assms3 apply (erule_tac x="\<rho>" in allE, auto)
              apply (metis TT1_P TT1_def case_assms(1) case_assms(4) ctt_prefix_subset_front intersect_refusal_trace_prefix_subset)
              using \<rho>_non_tick_refusal by (blast, blast)
          next
            show "\<forall>p. p \<in> P \<longrightarrow> (\<exists>p'. p = p' @ [[Tick]\<^sub>E]) \<or> (\<exists>p' Y. p = p' @ [[Y]\<^sub>R]) \<or> contains_refusal p \<or>
              (\<forall>q. q \<in> Q \<longrightarrow> (\<exists>q' Y. q = [Y]\<^sub>R # q') \<or> \<rho> @ [[x]\<^sub>E] \<noteq> p @ q) \<Longrightarrow> x = Tick"
              using case_assms case_assms2 case_assms3 apply (erule_tac x="\<rho>" in allE, auto)
              apply (metis TT1_P TT1_def case_assms(1) case_assms(4) ctt_prefix_subset_front intersect_refusal_trace_prefix_subset)
              using \<rho>_non_tick_refusal by (blast, blast)
          qed
        qed
      next
        fix x
        assume case_assms2: "[[x]\<^sub>E] \<in> Q" "x \<noteq> Tock"
        then show "\<rho> @ [[x]\<^sub>E] \<in> P \<triangle>\<^sub>U Q"
        proof (cases "contains_refusal \<rho>", auto)
          assume case_assms3: "contains_refusal \<rho>"
          show "\<rho> @ [[x]\<^sub>E] \<in> P \<triangle>\<^sub>U Q"
            unfolding UntimedInterruptTTT_def
          proof (auto)
            show "\<forall>p. contains_refusal p \<longrightarrow> p \<in> P \<longrightarrow> (\<exists>p'. p = p' @ [[Tick]\<^sub>E]) \<or> (\<exists>p' Y. p = p' @ [[Y]\<^sub>R]) \<or>
              (\<forall>q. q \<in> Q \<longrightarrow> (\<forall>X. [[X]\<^sub>R] \<in> Q \<longrightarrow> (\<exists>q' Y. q = [Y]\<^sub>R # q') \<or> \<rho> @ [[x]\<^sub>E] \<noteq> intersect_refusal_trace X p @ q)) \<Longrightarrow>
              \<rho> @ [[Tick]\<^sub>E] \<in> P"
              using case_assms case_assms2 case_assms3 apply (erule_tac x="\<rho>" in allE, auto)
              apply (metis TT1_P TT1_def case_assms(1) case_assms(4) ctt_prefix_subset_front intersect_refusal_trace_prefix_subset)
              using \<rho>_non_tick_refusal apply (blast, blast)
              apply (erule_tac x="[[x]\<^sub>E]" in allE, auto) apply (erule_tac x="Z" in allE, auto)
              by (metis eq_intersect_refusal_trace_append intersect_refusal_trace_idempotent)
          next
            show "\<forall>p. contains_refusal p \<longrightarrow> p \<in> P \<longrightarrow> (\<exists>p'. p = p' @ [[Tick]\<^sub>E]) \<or> (\<exists>p' Y. p = p' @ [[Y]\<^sub>R]) \<or>
              (\<forall>q. q \<in> Q \<longrightarrow> (\<forall>X. [[X]\<^sub>R] \<in> Q \<longrightarrow> (\<exists>q' Y. q = [Y]\<^sub>R # q') \<or> \<rho> @ [[x]\<^sub>E] \<noteq> intersect_refusal_trace X p @ q)) \<Longrightarrow>
              False"
              using case_assms case_assms2 case_assms3 apply (erule_tac x="\<rho>" in allE, auto)
              apply (metis TT1_P TT1_def case_assms(1) case_assms(4) ctt_prefix_subset_front intersect_refusal_trace_prefix_subset)
              using \<rho>_non_tick_refusal apply (blast, blast)
              apply (erule_tac x="[[x]\<^sub>E]" in allE, auto) apply (erule_tac x="Z" in allE, auto)
              by (metis eq_intersect_refusal_trace_append intersect_refusal_trace_idempotent)
          next
            show "\<forall>p. contains_refusal p \<longrightarrow> p \<in> P \<longrightarrow> (\<exists>p'. p = p' @ [[Tick]\<^sub>E]) \<or> (\<exists>p' Y. p = p' @ [[Y]\<^sub>R]) \<or>
              (\<forall>q. q \<in> Q \<longrightarrow> (\<forall>X. [[X]\<^sub>R] \<in> Q \<longrightarrow> (\<exists>q' Y. q = [Y]\<^sub>R # q') \<or> \<rho> @ [[x]\<^sub>E] \<noteq> intersect_refusal_trace X p @ q)) \<Longrightarrow>
              x = Tick"
              using case_assms case_assms2 case_assms3 apply (erule_tac x="\<rho>" in allE, auto)
              apply (metis TT1_P TT1_def case_assms(1) case_assms(4) ctt_prefix_subset_front intersect_refusal_trace_prefix_subset)
              using \<rho>_non_tick_refusal apply (blast, blast)
              apply (erule_tac x="[[x]\<^sub>E]" in allE, auto) apply (erule_tac x="Z" in allE, auto)
              by (metis eq_intersect_refusal_trace_append intersect_refusal_trace_idempotent)
          qed
        next
          assume case_assms3: "\<not> contains_refusal \<rho>"
          show " \<rho> @ [[x]\<^sub>E] \<in> P \<triangle>\<^sub>U Q"
            unfolding UntimedInterruptTTT_def
          proof (auto)
            show "\<forall>p. p \<in> P \<longrightarrow> (\<exists>p'. p = p' @ [[Tick]\<^sub>E]) \<or> (\<exists>p' Y. p = p' @ [[Y]\<^sub>R]) \<or> contains_refusal p \<or>
              (\<forall>q. q \<in> Q \<longrightarrow> (\<exists>q' Y. q = [Y]\<^sub>R # q') \<or> \<rho> @ [[x]\<^sub>E] \<noteq> p @ q) \<Longrightarrow> \<rho> @ [[Tick]\<^sub>E] \<in> P"
              using case_assms case_assms2 case_assms3 apply (erule_tac x="\<rho>" in allE, auto)
              apply (metis TT1_P TT1_def case_assms(1) case_assms(4) ctt_prefix_subset_front intersect_refusal_trace_prefix_subset)
              using \<rho>_non_tick_refusal by (blast, blast)
          next
            show "\<forall>p. p \<in> P \<longrightarrow> (\<exists>p'. p = p' @ [[Tick]\<^sub>E]) \<or> (\<exists>p' Y. p = p' @ [[Y]\<^sub>R]) \<or> contains_refusal p \<or>
              (\<forall>q. q \<in> Q \<longrightarrow> (\<exists>q' Y. q = [Y]\<^sub>R # q') \<or> \<rho> @ [[x]\<^sub>E] \<noteq> p @ q) \<Longrightarrow> False"
              using case_assms case_assms2 case_assms3 apply (erule_tac x="\<rho>" in allE, auto)
              apply (metis TT1_P TT1_def case_assms(1) case_assms(4) ctt_prefix_subset_front intersect_refusal_trace_prefix_subset)
              using \<rho>_non_tick_refusal by (blast, blast)
          next
            show "\<forall>p. p \<in> P \<longrightarrow> (\<exists>p'. p = p' @ [[Tick]\<^sub>E]) \<or> (\<exists>p' Y. p = p' @ [[Y]\<^sub>R]) \<or> contains_refusal p \<or>
              (\<forall>q. q \<in> Q \<longrightarrow> (\<exists>q' Y. q = [Y]\<^sub>R # q') \<or> \<rho> @ [[x]\<^sub>E] \<noteq> p @ q) \<Longrightarrow> x = Tick"
              using case_assms case_assms2 case_assms3 apply (erule_tac x="\<rho>" in allE, auto)
              apply (metis TT1_P TT1_def case_assms(1) case_assms(4) ctt_prefix_subset_front intersect_refusal_trace_prefix_subset)
              using \<rho>_non_tick_refusal by (blast, blast)
          qed
        qed
      next
        fix x
        assume case_assms2: "[[Z]\<^sub>R, [Tock]\<^sub>E] \<in> Q"
        show "\<rho> @ [[X]\<^sub>R, [Tock]\<^sub>E] \<notin> P \<triangle>\<^sub>U Q \<Longrightarrow> False"
          unfolding UntimedInterruptTTT_def
        proof (auto)
          show "\<forall>p Xa. p @ [[Xa]\<^sub>R] \<in> P \<longrightarrow> (\<forall>Y q. [Y]\<^sub>R # q \<in> Q \<longrightarrow> \<rho> @ [[X]\<^sub>R, [Tock]\<^sub>E] \<noteq> intersect_refusal_trace Y (p @ [[Xa]\<^sub>R]) @ q) \<Longrightarrow>
            False"
            using case_assms case_assms2 apply (erule_tac x="\<rho>" in allE, auto, erule_tac x="X" in allE, auto)
            apply (meson TT1_P TT1_def \<rho>_X_\<sigma>_ctt_subset_p ctt_prefix_subset.simps(1) ctt_prefix_subset.simps(2) ctt_prefix_subset_same_front ctt_subset_imp_prefix_subset subsetI)
            apply (erule_tac x="Z" in allE, erule_tac x="[[Tock]\<^sub>E]" in allE, auto)
            by (metis (no_types, lifting) eq_intersect_refusal_trace_append eq_intersect_refusal_trace_same_front intersect_refusal_trace.simps(1) intersect_refusal_trace.simps(3) intersect_refusal_trace_concat intersect_refusal_trace_idempotent list.inject)
        qed
      next
        fix x
        assume case_assms2: "[[Z]\<^sub>R, [Tock]\<^sub>E] \<in> Q"
        show "\<rho> @ [[X]\<^sub>R, [Tock]\<^sub>E] \<notin> P \<triangle>\<^sub>U Q \<Longrightarrow> \<rho> @ [[Tock]\<^sub>E] \<in> P \<triangle>\<^sub>U Q"
          unfolding UntimedInterruptTTT_def
        proof (auto)
          show "\<forall>p Xa. p @ [[Xa]\<^sub>R] \<in> P \<longrightarrow> (\<forall>Y q. [Y]\<^sub>R # q \<in> Q \<longrightarrow> \<rho> @ [[X]\<^sub>R, [Tock]\<^sub>E] \<noteq> intersect_refusal_trace Y (p @ [[Xa]\<^sub>R]) @ q) \<Longrightarrow>
            \<exists>p. p \<in> P \<and> (\<forall>p'. p \<noteq> p' @ [[Tick]\<^sub>E]) \<and> (\<forall>p' Y. p \<noteq> p' @ [[Y]\<^sub>R]) \<and> contains_refusal p \<and>
            (\<exists>q X. [[X]\<^sub>R] \<in> Q \<and> q \<in> Q \<and> (\<forall>q' Y. q \<noteq> [Y]\<^sub>R # q') \<and> \<rho> @ [[Tock]\<^sub>E] = intersect_refusal_trace X p @ q)"
            using case_assms case_assms2 apply (erule_tac x="\<rho>" in allE, auto, erule_tac x="X" in allE, auto)
            apply (meson TT1_P TT1_def \<rho>_X_\<sigma>_ctt_subset_p ctt_prefix_subset.simps(1) ctt_prefix_subset.simps(2) ctt_prefix_subset_same_front ctt_subset_imp_prefix_subset subsetI)
            apply (erule_tac x="Z" in allE, erule_tac x="[[Tock]\<^sub>E]" in allE, auto)
            by (metis (no_types, lifting) eq_intersect_refusal_trace_append eq_intersect_refusal_trace_same_front intersect_refusal_trace.simps(1) intersect_refusal_trace.simps(3) intersect_refusal_trace_concat intersect_refusal_trace_idempotent list.inject)
        qed
      qed
      then have 3: "Y \<inter> {e. e \<noteq> Tock \<and> [[e]\<^sub>E] \<in> Q \<or> e = Tock \<and> [[Z]\<^sub>R, [e]\<^sub>E] \<in> Q} = {}"
        using assm2 subsetCE by auto
      have 4:  "[[Z \<union> Y]\<^sub>R] \<in> Q"
        using 3 case_assms TT2s_Q unfolding TT2s_def
        by (erule_tac x="[]" in allE, erule_tac x="[]" in allE, erule_tac x="Z" in allE, erule_tac x="Y" in allE, auto)
      have 5: "\<rho> @ [X \<union> Y]\<^sub>R # [Tock]\<^sub>E # \<sigma>' \<in> P"
        using 1 2 TT2s_P unfolding TT2s_def
        by (erule_tac x="\<rho>" in allE, erule_tac x="\<sigma>'" in allE, erule_tac x="Z" in allE, erule_tac x="Y" in allE, auto)
      obtain \<sigma>'' where \<sigma>'_def: "\<sigma>' = \<sigma>'' @ [[Tick]\<^sub>E]"
        by (metis (no_types, hide_lams) case_assms(4) ttWF.simps(3) ttWF.simps(6) intersect_refusal_trace.simps(1) intersect_refusal_trace.simps(2) intersect_refusal_trace_concat last.simps last_appendR list.distinct(1) rev_exhaust)
      show "\<rho> @ [X \<union> Y]\<^sub>R # [Tock]\<^sub>E # \<sigma>' \<in> P \<triangle>\<^sub>U Q"
        unfolding UntimedInterruptTTT_def
      proof auto
        show "\<forall>p. contains_refusal p \<longrightarrow> p @ [[Tick]\<^sub>E] \<in> P \<longrightarrow> (\<forall>Xa. [[Xa]\<^sub>R] \<in> Q \<longrightarrow> \<rho> @ [X \<union> Y]\<^sub>R # [Tock]\<^sub>E # \<sigma>' \<noteq> intersect_refusal_trace Xa (p @ [[Tick]\<^sub>E])) \<Longrightarrow>
          \<exists>p. p \<in> P \<and> (\<forall>p'. p \<noteq> p' @ [[Tick]\<^sub>E]) \<and> (\<forall>p' Y. p \<noteq> p' @ [[Y]\<^sub>R]) \<and> contains_refusal p \<and>
            (\<exists>q Xa. [[Xa]\<^sub>R] \<in> Q \<and> q \<in> Q \<and> (\<forall>q' Y. q \<noteq> [Y]\<^sub>R # q') \<and> \<rho> @ [X \<union> Y]\<^sub>R # [Tock]\<^sub>E # \<sigma>' = intersect_refusal_trace Xa p @ q)"
          using 5 \<sigma>'_def apply (erule_tac x="\<rho> @ [X \<union> Y]\<^sub>R # [Tock]\<^sub>E # \<sigma>''" in allE, auto)
          apply (metis append.assoc append.left_neutral append_Cons ctt_prefix_concat ctt_prefix_imp_prefix_subset not_contains_refusal_ctt_prefix_subset_end_nonref)
          apply (erule_tac x="Z \<union> Y" in allE, auto simp add: 4)
          using case_assms(4) intersect_refusal_trace_refusal_subset_idempotent by blast
      qed
    next
      fix p Z W q
      assume case_assms: "p @ [[Z]\<^sub>R] \<in> P" "[W]\<^sub>R # q \<in> Q" "\<rho> @ [X]\<^sub>R # [Tock]\<^sub>E # \<sigma>' = intersect_refusal_trace W (p @ [[Z]\<^sub>R]) @ q"
      have "(intersect_refusal_trace W p = \<rho> \<and> X = W \<inter> Z \<and> q = [Tock]\<^sub>E # \<sigma>')
        \<or> (\<exists> \<rho>1 \<rho>2 A. p = \<rho>1 @ [A]\<^sub>R # \<rho>2 \<and> X = A \<inter> W \<and> intersect_refusal_trace W \<rho>1 = \<rho> \<and> [Tock]\<^sub>E # \<sigma>' = intersect_refusal_trace W (\<rho>2 @ [[Z]\<^sub>R]) @ q)
        \<or> (\<exists> \<sigma>1 \<sigma>2. q = \<sigma>1 @ [X]\<^sub>R # \<sigma>2 \<and> \<rho> = intersect_refusal_trace W (p @ [[Z]\<^sub>R]) @ \<sigma>1 \<and> \<sigma>2 = [Tock]\<^sub>E # \<sigma>')"
        using case_assms(3) apply -
        apply (induct \<rho> p rule:ctt_subset.induct, simp_all, safe, simp_all)
        apply (metis append_Cons intersect_refusal_trace.simps(3))
        apply (metis append_Cons intersect_refusal_trace.simps(3))
        apply (metis append_Cons intersect_refusal_trace.simps(3))
        apply (metis append_Cons intersect_refusal_trace.simps(3))
        apply (metis append_Cons intersect_refusal_trace.simps(2))
        apply (metis append_Cons intersect_refusal_trace.simps(2))
        apply (metis append_Cons intersect_refusal_trace.simps(2))
        apply (metis append_Cons intersect_refusal_trace.simps(2))
        apply (case_tac v, auto, metis Int_commute append.left_neutral intersect_refusal_trace.simps(1))
        apply (case_tac v, auto)
        apply (case_tac v, auto, metis Int_commute append.left_neutral intersect_refusal_trace.simps(1))
        apply (case_tac v, auto, metis Int_commute append.left_neutral intersect_refusal_trace.simps(1))
        apply (case_tac v, auto, metis Int_commute append.left_neutral intersect_refusal_trace.simps(1))
        done
      then show "\<rho> @ [X \<union> Y]\<^sub>R # [Tock]\<^sub>E # \<sigma>' \<in> P \<triangle>\<^sub>U Q"
      proof auto
        assume case_assms2: "\<rho> = intersect_refusal_trace W p" "q = [Tock]\<^sub>E # \<sigma>'" "X = W \<inter> Z"
        have "{e. e \<noteq> Tock \<and> \<rho> @ [[e]\<^sub>E] \<in> P \<or> e = Tock \<and> \<rho> @ [[X]\<^sub>R, [e]\<^sub>E] \<in> P}
          \<subseteq> {e. e \<noteq> Tock \<and> \<rho> @ [[e]\<^sub>E] \<in> P \<triangle>\<^sub>U Q \<or> e = Tock \<and> \<rho> @ [[X]\<^sub>R, [e]\<^sub>E] \<in> P \<triangle>\<^sub>U Q}"
        proof (auto)
          fix x
          assume case_assms3: "\<rho> @ [[x]\<^sub>E] \<in> P" "x \<noteq> Tock"
          then show "\<rho> @ [[x]\<^sub>E] \<in> P \<triangle>\<^sub>U Q"
            unfolding UntimedInterruptTTT_def
          proof (cases x, cases "contains_refusal \<rho>", safe, simp_all)
            fix x1
            assume case_assms4: "contains_refusal \<rho>" "\<rho> @ [[Event x1]\<^sub>E] \<in> P"
            then show "\<forall>p. contains_refusal p \<longrightarrow> p \<in> P \<longrightarrow> (\<exists>p'. p = p' @ [[Tick]\<^sub>E]) \<or> (\<exists>p' Y. p = p' @ [[Y]\<^sub>R]) \<or>
                (\<forall>q. q \<in> Q \<longrightarrow> (\<forall>X. [[X]\<^sub>R] \<in> Q \<longrightarrow> (\<exists>q' Y. q = [Y]\<^sub>R # q') \<or> \<rho> @ [[Event x1]\<^sub>E] \<noteq> intersect_refusal_trace X p @ q)) \<Longrightarrow>
              \<exists>p. p @ [[Tick]\<^sub>E] \<in> P \<and> contains_refusal p \<and> (\<exists>X. [[X]\<^sub>R] \<in> Q \<and> \<rho> @ [[Event x1]\<^sub>E] = intersect_refusal_trace X (p @ [[Tick]\<^sub>E]))"
              apply (erule_tac x="\<rho> @ [[Event x1]\<^sub>E]" in allE, auto)
              using ctt_prefix_concat ctt_prefix_imp_prefix_subset not_contains_refusal_ctt_prefix_subset apply blast
              apply (erule_tac x="[]" in allE, auto, simp add: TT0_TT1_empty TT0_Q TT1_Q)
              apply (erule_tac x="W" in allE, auto)
              apply (meson TT1_Q TT1_def case_assms(2) ctt_prefix_subset.simps(1) ctt_prefix_subset.simps(2) subset_iff)
              by (simp add: case_assms2(1) intersect_refusal_trace_concat intersect_refusal_trace_idempotent)
          next
            fix x1
            assume case_assms4: "\<not> contains_refusal \<rho>" "\<rho> @ [[Event x1]\<^sub>E] \<in> P"
            show "\<forall>p. p \<in> P \<longrightarrow> (\<exists>p'. p = p' @ [[Tick]\<^sub>E]) \<or> (\<exists>p' Y. p = p' @ [[Y]\<^sub>R]) \<or> contains_refusal p \<or>
                (\<forall>q. q \<in> Q \<longrightarrow> (\<exists>q' Y. q = [Y]\<^sub>R # q') \<or> \<rho> @ [[Event x1]\<^sub>E] \<noteq> p @ q) \<Longrightarrow>
              \<exists>p. p @ [[Tick]\<^sub>E] \<in> P \<and> contains_refusal p \<and> (\<exists>X. [[X]\<^sub>R] \<in> Q \<and> \<rho> @ [[Event x1]\<^sub>E] = intersect_refusal_trace X (p @ [[Tick]\<^sub>E]))"
              apply (erule_tac x="\<rho> @ [[Event x1]\<^sub>E]" in allE, auto)
              using TT0_TT1_empty TT0_Q TT1_Q case_assms4 not_contains_refusal_append_event by blast+
          next
            assume "\<rho> @ [[Tick]\<^sub>E] \<in> P" "contains_refusal \<rho>"
            then show "\<exists>p. p @ [[Tick]\<^sub>E] \<in> P \<and> contains_refusal p \<and> (\<exists>X. [[X]\<^sub>R] \<in> Q \<and> \<rho> @ [[Tick]\<^sub>E] = intersect_refusal_trace X (p @ [[Tick]\<^sub>E]))"
              apply (rule_tac x="\<rho>" in exI, auto, rule_tac x="W" in exI, auto)
              apply (meson TT1_Q TT1_def case_assms(2) ctt_prefix_subset.simps(1) ctt_prefix_subset.simps(2) subset_iff)
              by (simp add: case_assms2(1) intersect_refusal_trace_concat intersect_refusal_trace_idempotent)
          qed
        next
          fix x
          assume case_assms3: "\<rho> @ [[x]\<^sub>E] \<in> P" "x \<noteq> Tock"
          then show "\<rho> @ [[x]\<^sub>E] \<in> P \<triangle>\<^sub>U Q"
            unfolding UntimedInterruptTTT_def
          proof (cases x, cases "contains_refusal \<rho>", safe, simp_all)
            fix x1
            assume case_assms4: "contains_refusal \<rho>" "\<rho> @ [[Event x1]\<^sub>E] \<in> P"
            then show "\<forall>p. contains_refusal p \<longrightarrow> p \<in> P \<longrightarrow> (\<exists>p'. p = p' @ [[Tick]\<^sub>E]) \<or> (\<exists>p' Y. p = p' @ [[Y]\<^sub>R]) \<or>
                (\<forall>q. q \<in> Q \<longrightarrow> (\<forall>X. [[X]\<^sub>R] \<in> Q \<longrightarrow> (\<exists>q' Y. q = [Y]\<^sub>R # q') \<or> \<rho> @ [[Event x1]\<^sub>E] \<noteq> intersect_refusal_trace X p @ q)) \<Longrightarrow>
              \<exists>p. p @ [[Tick]\<^sub>E] \<in> P \<and> contains_refusal p \<and> (\<exists>X. [[X]\<^sub>R] \<in> Q \<and> \<rho> @ [[Event x1]\<^sub>E] = intersect_refusal_trace X (p @ [[Tick]\<^sub>E]))"
              apply (erule_tac x="\<rho> @ [[Event x1]\<^sub>E]" in allE, auto)
              using ctt_prefix_concat ctt_prefix_imp_prefix_subset not_contains_refusal_ctt_prefix_subset apply blast
              apply (erule_tac x="[]" in allE, auto, simp add: TT0_TT1_empty TT0_Q TT1_Q)
              apply (erule_tac x="W" in allE, auto)
              apply (meson TT1_Q TT1_def case_assms(2) ctt_prefix_subset.simps(1) ctt_prefix_subset.simps(2) subset_iff)
              by (simp add: case_assms2(1) intersect_refusal_trace_concat intersect_refusal_trace_idempotent)
          next
            fix x1
            assume case_assms4: "\<not> contains_refusal \<rho>" "\<rho> @ [[Event x1]\<^sub>E] \<in> P"
            show "\<forall>p. p \<in> P \<longrightarrow> (\<exists>p'. p = p' @ [[Tick]\<^sub>E]) \<or> (\<exists>p' Y. p = p' @ [[Y]\<^sub>R]) \<or> contains_refusal p \<or>
                (\<forall>q. q \<in> Q \<longrightarrow> (\<exists>q' Y. q = [Y]\<^sub>R # q') \<or> \<rho> @ [[Event x1]\<^sub>E] \<noteq> p @ q) \<Longrightarrow>
              \<exists>p. p @ [[Tick]\<^sub>E] \<in> P \<and> contains_refusal p \<and> (\<exists>X. [[X]\<^sub>R] \<in> Q \<and> \<rho> @ [[Event x1]\<^sub>E] = intersect_refusal_trace X (p @ [[Tick]\<^sub>E]))"
              apply (erule_tac x="\<rho> @ [[Event x1]\<^sub>E]" in allE, auto)
              using TT0_TT1_empty TT0_Q TT1_Q case_assms4 not_contains_refusal_append_event by blast+
          next
            assume "\<rho> @ [[Tick]\<^sub>E] \<in> P" "contains_refusal \<rho>"
            then show "\<exists>p. p @ [[Tick]\<^sub>E] \<in> P \<and> contains_refusal p \<and> (\<exists>X. [[X]\<^sub>R] \<in> Q \<and> \<rho> @ [[Tick]\<^sub>E] = intersect_refusal_trace X (p @ [[Tick]\<^sub>E]))"
              apply (rule_tac x="\<rho>" in exI, auto, rule_tac x="W" in exI, auto)
              apply (meson TT1_Q TT1_def case_assms(2) ctt_prefix_subset.simps(1) ctt_prefix_subset.simps(2) subset_iff)
              by (simp add: case_assms2(1) intersect_refusal_trace_concat intersect_refusal_trace_idempotent)
          qed
        next
          assume case_assms3: "\<rho> @ [[X]\<^sub>R, [Tock]\<^sub>E] \<in> P" "\<rho> @ [[X]\<^sub>R, [Tock]\<^sub>E] \<notin> P \<triangle>\<^sub>U Q"
          have "\<forall>p. contains_refusal p \<longrightarrow> p \<in> P \<longrightarrow> (\<exists>p'. p = p' @ [[Tick]\<^sub>E]) \<or> (\<exists>p' Y. p = p' @ [[Y]\<^sub>R]) \<or>
            (\<forall>q. q \<in> Q \<longrightarrow> (\<forall>Xa. [[Xa]\<^sub>R] \<in> Q \<longrightarrow> (\<exists>q' Y. q = [Y]\<^sub>R # q') \<or> \<rho> @ [[X]\<^sub>R, [Tock]\<^sub>E] \<noteq> intersect_refusal_trace Xa p @ q))"
            using case_assms3(2) unfolding UntimedInterruptTTT_def by (auto)
          then show "False"
            using case_assms case_assms2 apply (erule_tac x="\<rho> @ [[X]\<^sub>R, [Tock]\<^sub>E]" in allE, auto)
            apply (meson ctt_prefix_subset.simps(1) ctt_prefix_subset.simps(2) ctt_prefix_subset_same_front not_contains_refusal_ctt_prefix_subset_end_nonref subsetI)
            using case_assms3(1) apply blast
            apply (erule_tac x="[]" in allE, auto)+
            using TT0_TT1_empty TT0_Q TT1_Q apply blast
            apply (erule_tac x="W" in allE, auto)
            apply (metis TT1_Q TT1_def append.left_neutral append_Cons ctt_prefix_concat ctt_prefix_imp_prefix_subset)
            by (simp add: intersect_refusal_trace_end_ref_imp_intersect_refusal_trace_end_ref_tock intersect_refusal_trace_idempotent)
        next
          assume case_assms3: "\<rho> @ [[X]\<^sub>R, [Tock]\<^sub>E] \<in> P" "\<rho> @ [[X]\<^sub>R, [Tock]\<^sub>E] \<notin> P \<triangle>\<^sub>U Q"
          have "\<forall>p. contains_refusal p \<longrightarrow> p \<in> P \<longrightarrow> (\<exists>p'. p = p' @ [[Tick]\<^sub>E]) \<or> (\<exists>p' Y. p = p' @ [[Y]\<^sub>R]) \<or>
            (\<forall>q. q \<in> Q \<longrightarrow> (\<forall>Xa. [[Xa]\<^sub>R] \<in> Q \<longrightarrow> (\<exists>q' Y. q = [Y]\<^sub>R # q') \<or> \<rho> @ [[X]\<^sub>R, [Tock]\<^sub>E] \<noteq> intersect_refusal_trace Xa p @ q))"
            using case_assms3(2) unfolding UntimedInterruptTTT_def by (auto)
          then show "\<rho> @ [[Tock]\<^sub>E] \<in> P \<triangle>\<^sub>U Q"
            using case_assms case_assms2 apply (erule_tac x="\<rho> @ [[X]\<^sub>R, [Tock]\<^sub>E]" in allE, auto)
            apply (meson ctt_prefix_subset.simps(1) ctt_prefix_subset.simps(2) ctt_prefix_subset_same_front not_contains_refusal_ctt_prefix_subset_end_nonref subsetI)
            using case_assms3(1) apply blast
            apply (erule_tac x="[]" in allE, auto)+
            using TT0_TT1_empty TT0_Q TT1_Q apply blast
            apply (erule_tac x="W" in allE, auto)
            apply (metis TT1_Q TT1_def append.left_neutral append_Cons ctt_prefix_concat ctt_prefix_imp_prefix_subset)
            by (simp add: intersect_refusal_trace_end_ref_imp_intersect_refusal_trace_end_ref_tock intersect_refusal_trace_idempotent)
        qed
        then have 1: "Y \<inter> {e. e \<noteq> Tock \<and> \<rho> @ [[e]\<^sub>E] \<in> P \<or> e = Tock \<and> \<rho> @ [[X]\<^sub>R, [e]\<^sub>E] \<in> P} = {}"
          using assm2 by auto

        have p_in_P: "p \<in> P"
          using TT1_P TT1_def case_assms(1) ctt_prefix_concat ctt_prefix_imp_prefix_subset by blast
        have \<rho>_in_P: "\<rho> \<in> P"
          using TT1_P TT1_def case_assms2(1) intersect_refusal_trace_prefix_subset p_in_P by blast
        have \<rho>_intersect_refusal_trace_idempotent: "\<rho> = intersect_refusal_trace W \<rho>"
          by (simp add: case_assms2(1) intersect_refusal_trace_idempotent)
        have \<rho>_X_in_P: "\<rho> @ [[X]\<^sub>R] \<in> P"
          by (metis (no_types, lifting) TT1_P TT1_def case_assms(1) case_assms2(1) case_assms2(3) intersect_refusal_trace.simps(1) intersect_refusal_trace.simps(3) intersect_refusal_trace_concat intersect_refusal_trace_prefix_subset)
        have \<rho>_X_intersect_refusal_trace_idempotent: "\<rho> @ [[X]\<^sub>R] = intersect_refusal_trace W (\<rho> @ [[X]\<^sub>R])"
          by (metis Int_left_absorb \<rho>_intersect_refusal_trace_idempotent case_assms2(3) intersect_refusal_trace.simps(1) intersect_refusal_trace.simps(3) intersect_refusal_trace_concat)
        
        have "{e. e \<noteq> Tock \<and> [[e]\<^sub>E] \<in> Q \<or> e = Tock \<and> [[W]\<^sub>R, [e]\<^sub>E] \<in> Q}
            \<subseteq> {e. e \<noteq> Tock \<and> \<rho> @ [[e]\<^sub>E] \<in> P \<triangle>\<^sub>U Q \<or> e = Tock \<and> \<rho> @ [[X]\<^sub>R, [e]\<^sub>E] \<in> P \<triangle>\<^sub>U Q}"
        proof auto
          fix x
          assume case_assms2: "[[x]\<^sub>E] \<in> Q" "x \<noteq> Tock"
          then show "\<rho> @ [[x]\<^sub>E] \<in> P \<triangle>\<^sub>U Q"
          proof (cases "contains_refusal \<rho>", auto)
            assume case_assms3: "contains_refusal \<rho>"
            show "\<rho> @ [[x]\<^sub>E] \<in> P \<triangle>\<^sub>U Q"
              unfolding UntimedInterruptTTT_def
            proof (auto)
              show "\<forall>p. contains_refusal p \<longrightarrow> p \<in> P \<longrightarrow> (\<exists>p'. p = p' @ [[Tick]\<^sub>E]) \<or> (\<exists>p' Y. p = p' @ [[Y]\<^sub>R]) \<or>
                (\<forall>q. q \<in> Q \<longrightarrow> (\<forall>X. [[X]\<^sub>R] \<in> Q \<longrightarrow> (\<exists>q' Y. q = [Y]\<^sub>R # q') \<or> \<rho> @ [[x]\<^sub>E] \<noteq> intersect_refusal_trace X p @ q)) \<Longrightarrow>
                \<rho> @ [[Tick]\<^sub>E] \<in> P"
                apply (erule_tac x="\<rho>" in allE, auto simp add: case_assms3 \<rho>_in_P \<rho>_non_tick_refusal)
                apply (erule_tac x="[[x]\<^sub>E]" in allE, auto simp add: case_assms2)
                apply (erule_tac x="W" in allE, auto)
                apply (meson TT1_Q TT1_def case_assms(2) ctt_prefix_subset.simps(1) ctt_prefix_subset.simps(2) ctt_prefix_subset_refl)
                using \<rho>_intersect_refusal_trace_idempotent by blast
            next
              show "\<forall>p. contains_refusal p \<longrightarrow> p \<in> P \<longrightarrow> (\<exists>p'. p = p' @ [[Tick]\<^sub>E]) \<or> (\<exists>p' Y. p = p' @ [[Y]\<^sub>R]) \<or>
                (\<forall>q. q \<in> Q \<longrightarrow> (\<forall>X. [[X]\<^sub>R] \<in> Q \<longrightarrow> (\<exists>q' Y. q = [Y]\<^sub>R # q') \<or> \<rho> @ [[x]\<^sub>E] \<noteq> intersect_refusal_trace X p @ q)) \<Longrightarrow>
                False"
                apply (erule_tac x="\<rho>" in allE, auto simp add: case_assms3 \<rho>_in_P \<rho>_non_tick_refusal)
                apply (erule_tac x="[[x]\<^sub>E]" in allE, auto simp add: case_assms2)
                apply (erule_tac x="W" in allE, auto)
                apply (meson TT1_Q TT1_def case_assms(2) ctt_prefix_subset.simps(1) ctt_prefix_subset.simps(2) ctt_prefix_subset_refl)
                using \<rho>_intersect_refusal_trace_idempotent by blast
            next
              show "\<forall>p. contains_refusal p \<longrightarrow> p \<in> P \<longrightarrow> (\<exists>p'. p = p' @ [[Tick]\<^sub>E]) \<or> (\<exists>p' Y. p = p' @ [[Y]\<^sub>R]) \<or>
                (\<forall>q. q \<in> Q \<longrightarrow> (\<forall>X. [[X]\<^sub>R] \<in> Q \<longrightarrow> (\<exists>q' Y. q = [Y]\<^sub>R # q') \<or> \<rho> @ [[x]\<^sub>E] \<noteq> intersect_refusal_trace X p @ q)) \<Longrightarrow>
                x = Tick"
                apply (erule_tac x="\<rho>" in allE, auto simp add: case_assms3 \<rho>_in_P \<rho>_non_tick_refusal)
                apply (erule_tac x="[[x]\<^sub>E]" in allE, auto simp add: case_assms2)
                apply (erule_tac x="W" in allE, auto)
                apply (meson TT1_Q TT1_def case_assms(2) ctt_prefix_subset.simps(1) ctt_prefix_subset.simps(2) ctt_prefix_subset_refl)
                using \<rho>_intersect_refusal_trace_idempotent by blast
            qed
          next
            assume case_assms3: "\<not> contains_refusal \<rho>"
            show " \<rho> @ [[x]\<^sub>E] \<in> P \<triangle>\<^sub>U Q"
              unfolding UntimedInterruptTTT_def
            proof (auto)
              show "\<forall>p. p \<in> P \<longrightarrow> (\<exists>p'. p = p' @ [[Tick]\<^sub>E]) \<or> (\<exists>p' Y. p = p' @ [[Y]\<^sub>R]) \<or> contains_refusal p \<or>
                (\<forall>q. q \<in> Q \<longrightarrow> (\<exists>q' Y. q = [Y]\<^sub>R # q') \<or> \<rho> @ [[x]\<^sub>E] \<noteq> p @ q) \<Longrightarrow> \<rho> @ [[Tick]\<^sub>E] \<in> P"
                using case_assms case_assms2 case_assms3 apply (erule_tac x="\<rho>" in allE, auto)
                using \<rho>_in_P \<rho>_non_tick_refusal by blast+
            next
              show "\<forall>p. p \<in> P \<longrightarrow> (\<exists>p'. p = p' @ [[Tick]\<^sub>E]) \<or> (\<exists>p' Y. p = p' @ [[Y]\<^sub>R]) \<or> contains_refusal p \<or>
                (\<forall>q. q \<in> Q \<longrightarrow> (\<exists>q' Y. q = [Y]\<^sub>R # q') \<or> \<rho> @ [[x]\<^sub>E] \<noteq> p @ q) \<Longrightarrow> False"
                using case_assms case_assms2 case_assms3 apply (erule_tac x="\<rho>" in allE, auto)
                using \<rho>_in_P \<rho>_non_tick_refusal by blast+
            next
              show "\<forall>p. p \<in> P \<longrightarrow> (\<exists>p'. p = p' @ [[Tick]\<^sub>E]) \<or> (\<exists>p' Y. p = p' @ [[Y]\<^sub>R]) \<or> contains_refusal p \<or>
                (\<forall>q. q \<in> Q \<longrightarrow> (\<exists>q' Y. q = [Y]\<^sub>R # q') \<or> \<rho> @ [[x]\<^sub>E] \<noteq> p @ q) \<Longrightarrow> x = Tick"
                using case_assms case_assms2 case_assms3 apply (erule_tac x="\<rho>" in allE, auto)
                using \<rho>_in_P \<rho>_non_tick_refusal by blast+
            qed
          qed
        next
          fix x
          assume case_assms2: "[[x]\<^sub>E] \<in> Q" "x \<noteq> Tock"
          then show "\<rho> @ [[x]\<^sub>E] \<in> P \<triangle>\<^sub>U Q"
          proof (cases "contains_refusal \<rho>", auto)
            assume case_assms3: "contains_refusal \<rho>"
            show "\<rho> @ [[x]\<^sub>E] \<in> P \<triangle>\<^sub>U Q"
              unfolding UntimedInterruptTTT_def
            proof (auto)
              show "\<forall>p. contains_refusal p \<longrightarrow> p \<in> P \<longrightarrow> (\<exists>p'. p = p' @ [[Tick]\<^sub>E]) \<or> (\<exists>p' Y. p = p' @ [[Y]\<^sub>R]) \<or>
                (\<forall>q. q \<in> Q \<longrightarrow> (\<forall>X. [[X]\<^sub>R] \<in> Q \<longrightarrow> (\<exists>q' Y. q = [Y]\<^sub>R # q') \<or> \<rho> @ [[x]\<^sub>E] \<noteq> intersect_refusal_trace X p @ q)) \<Longrightarrow>
                \<rho> @ [[Tick]\<^sub>E] \<in> P"
                apply (erule_tac x="\<rho>" in allE, auto simp add: case_assms3 \<rho>_in_P \<rho>_non_tick_refusal)
                apply (erule_tac x="[[x]\<^sub>E]" in allE, auto simp add: case_assms2)
                apply (erule_tac x="W" in allE, auto)
                apply (meson TT1_Q TT1_def case_assms(2) ctt_prefix_subset.simps(1) ctt_prefix_subset.simps(2) ctt_prefix_subset_refl)
                using \<rho>_intersect_refusal_trace_idempotent by blast
            next
              show "\<forall>p. contains_refusal p \<longrightarrow> p \<in> P \<longrightarrow> (\<exists>p'. p = p' @ [[Tick]\<^sub>E]) \<or> (\<exists>p' Y. p = p' @ [[Y]\<^sub>R]) \<or>
                (\<forall>q. q \<in> Q \<longrightarrow> (\<forall>X. [[X]\<^sub>R] \<in> Q \<longrightarrow> (\<exists>q' Y. q = [Y]\<^sub>R # q') \<or> \<rho> @ [[x]\<^sub>E] \<noteq> intersect_refusal_trace X p @ q)) \<Longrightarrow>
                False"
                apply (erule_tac x="\<rho>" in allE, auto simp add: case_assms3 \<rho>_in_P \<rho>_non_tick_refusal)
                apply (erule_tac x="[[x]\<^sub>E]" in allE, auto simp add: case_assms2)
                apply (erule_tac x="W" in allE, auto)
                apply (meson TT1_Q TT1_def case_assms(2) ctt_prefix_subset.simps(1) ctt_prefix_subset.simps(2) ctt_prefix_subset_refl)
                using \<rho>_intersect_refusal_trace_idempotent by blast
            next
              show "\<forall>p. contains_refusal p \<longrightarrow> p \<in> P \<longrightarrow> (\<exists>p'. p = p' @ [[Tick]\<^sub>E]) \<or> (\<exists>p' Y. p = p' @ [[Y]\<^sub>R]) \<or>
                (\<forall>q. q \<in> Q \<longrightarrow> (\<forall>X. [[X]\<^sub>R] \<in> Q \<longrightarrow> (\<exists>q' Y. q = [Y]\<^sub>R # q') \<or> \<rho> @ [[x]\<^sub>E] \<noteq> intersect_refusal_trace X p @ q)) \<Longrightarrow>
                x = Tick"
                apply (erule_tac x="\<rho>" in allE, auto simp add: case_assms3 \<rho>_in_P \<rho>_non_tick_refusal)
                apply (erule_tac x="[[x]\<^sub>E]" in allE, auto simp add: case_assms2)
                apply (erule_tac x="W" in allE, auto)
                apply (meson TT1_Q TT1_def case_assms(2) ctt_prefix_subset.simps(1) ctt_prefix_subset.simps(2) ctt_prefix_subset_refl)
                using \<rho>_intersect_refusal_trace_idempotent by blast
            qed
          next
            assume case_assms3: "\<not> contains_refusal \<rho>"
            show " \<rho> @ [[x]\<^sub>E] \<in> P \<triangle>\<^sub>U Q"
              unfolding UntimedInterruptTTT_def
            proof (auto)
              show "\<forall>p. p \<in> P \<longrightarrow> (\<exists>p'. p = p' @ [[Tick]\<^sub>E]) \<or> (\<exists>p' Y. p = p' @ [[Y]\<^sub>R]) \<or> contains_refusal p \<or>
                (\<forall>q. q \<in> Q \<longrightarrow> (\<exists>q' Y. q = [Y]\<^sub>R # q') \<or> \<rho> @ [[x]\<^sub>E] \<noteq> p @ q) \<Longrightarrow> \<rho> @ [[Tick]\<^sub>E] \<in> P"
                using case_assms case_assms2 case_assms3 apply (erule_tac x="\<rho>" in allE, auto)
                using \<rho>_in_P \<rho>_non_tick_refusal by blast+
            next
              show "\<forall>p. p \<in> P \<longrightarrow> (\<exists>p'. p = p' @ [[Tick]\<^sub>E]) \<or> (\<exists>p' Y. p = p' @ [[Y]\<^sub>R]) \<or> contains_refusal p \<or>
                (\<forall>q. q \<in> Q \<longrightarrow> (\<exists>q' Y. q = [Y]\<^sub>R # q') \<or> \<rho> @ [[x]\<^sub>E] \<noteq> p @ q) \<Longrightarrow> False"
                using case_assms case_assms2 case_assms3 apply (erule_tac x="\<rho>" in allE, auto)
                using \<rho>_in_P \<rho>_non_tick_refusal by blast+
            next
              show "\<forall>p. p \<in> P \<longrightarrow> (\<exists>p'. p = p' @ [[Tick]\<^sub>E]) \<or> (\<exists>p' Y. p = p' @ [[Y]\<^sub>R]) \<or> contains_refusal p \<or>
                (\<forall>q. q \<in> Q \<longrightarrow> (\<exists>q' Y. q = [Y]\<^sub>R # q') \<or> \<rho> @ [[x]\<^sub>E] \<noteq> p @ q) \<Longrightarrow> x = Tick"
                using case_assms case_assms2 case_assms3 apply (erule_tac x="\<rho>" in allE, auto)
                using \<rho>_in_P \<rho>_non_tick_refusal by blast+
            qed
          qed
        next
          fix x
          assume case_assms3: "[[W]\<^sub>R, [Tock]\<^sub>E] \<in> Q"
          show "\<rho> @ [[X]\<^sub>R, [Tock]\<^sub>E] \<notin> P \<triangle>\<^sub>U Q \<Longrightarrow> False"
            unfolding UntimedInterruptTTT_def
          proof (auto)
            show "\<forall>p Xa. p @ [[Xa]\<^sub>R] \<in> P \<longrightarrow> (\<forall>Y q. [Y]\<^sub>R # q \<in> Q \<longrightarrow> \<rho> @ [[X]\<^sub>R, [Tock]\<^sub>E] \<noteq> intersect_refusal_trace Y (p @ [[Xa]\<^sub>R]) @ q) \<Longrightarrow>
              False"
              using case_assms case_assms3 apply (erule_tac x="\<rho>" in allE, auto, erule_tac x="X" in allE, auto)
              using \<rho>_X_in_P apply blast
              apply (erule_tac x="W" in allE, erule_tac x="[[Tock]\<^sub>E]" in allE, auto)
              using \<rho>_X_intersect_refusal_trace_idempotent by blast
          qed
        next
          fix x
          assume case_assms3: "[[W]\<^sub>R, [Tock]\<^sub>E] \<in> Q"
          show "\<rho> @ [[X]\<^sub>R, [Tock]\<^sub>E] \<notin> P \<triangle>\<^sub>U Q \<Longrightarrow> \<rho> @ [[Tock]\<^sub>E] \<in> P \<triangle>\<^sub>U Q"
            unfolding UntimedInterruptTTT_def
          proof (auto)
            show "\<forall>p Xa. p @ [[Xa]\<^sub>R] \<in> P \<longrightarrow> (\<forall>Y q. [Y]\<^sub>R # q \<in> Q \<longrightarrow> \<rho> @ [[X]\<^sub>R, [Tock]\<^sub>E] \<noteq> intersect_refusal_trace Y (p @ [[Xa]\<^sub>R]) @ q) \<Longrightarrow>
              \<exists>p. p \<in> P \<and> (\<forall>p'. p \<noteq> p' @ [[Tick]\<^sub>E]) \<and> (\<forall>p' Y. p \<noteq> p' @ [[Y]\<^sub>R]) \<and> contains_refusal p \<and>
                (\<exists>q X. [[X]\<^sub>R] \<in> Q \<and> q \<in> Q \<and> (\<forall>q' Y. q \<noteq> [Y]\<^sub>R # q') \<and> \<rho> @ [[Tock]\<^sub>E] = intersect_refusal_trace X p @ q) "
              using case_assms case_assms3 apply (erule_tac x="\<rho>" in allE, auto, erule_tac x="X" in allE, auto)
              using \<rho>_X_in_P apply blast
              apply (erule_tac x="W" in allE, erule_tac x="[[Tock]\<^sub>E]" in allE, auto)
              using \<rho>_X_intersect_refusal_trace_idempotent by blast
          qed
        qed
        then have 2: "Y \<inter> {e. e \<noteq> Tock \<and> [[e]\<^sub>E] \<in> Q \<or> e = Tock \<and> [[W]\<^sub>R, [e]\<^sub>E] \<in> Q} = {}"
          using assm2 by auto
        have 3: "\<rho> @ [[X \<union> Y]\<^sub>R] \<in> P"
          using "1" TT2_P TT2_def \<rho>_X_in_P by blast
        have 4: "[W \<union> Y]\<^sub>R # q \<in> Q"
          using TT2s_Q case_assms(2) 2 unfolding TT2s_def by (erule_tac x="[]" in allE, auto)
        show "intersect_refusal_trace W p @ [W \<inter> Z \<union> Y]\<^sub>R # [Tock]\<^sub>E # \<sigma>' \<in> P \<triangle>\<^sub>U Q"
          unfolding UntimedInterruptTTT_def
        proof auto
          show "\<forall>pa X. pa @ [[X]\<^sub>R] \<in> P \<longrightarrow> (\<forall>Ya q. [Ya]\<^sub>R # q \<in> Q \<longrightarrow>
              intersect_refusal_trace W p @ [W \<inter> Z \<union> Y]\<^sub>R # [Tock]\<^sub>E # \<sigma>' \<noteq> intersect_refusal_trace Ya (pa @ [[X]\<^sub>R]) @ q) \<Longrightarrow>
            \<exists>pa. pa \<in> P \<and> (\<forall>p'. pa \<noteq> p' @ [[Tick]\<^sub>E]) \<and> (\<forall>p' Y. pa \<noteq> p' @ [[Y]\<^sub>R]) \<and> contains_refusal pa \<and>
              (\<exists>q X. [[X]\<^sub>R] \<in> Q \<and> q \<in> Q \<and> (\<forall>q' Y. q \<noteq> [Y]\<^sub>R # q') \<and> intersect_refusal_trace W p @ [W \<inter> Z \<union> Y]\<^sub>R # [Tock]\<^sub>E # \<sigma>' = intersect_refusal_trace X pa @ q)"
            using case_assms case_assms2 3 4 apply (erule_tac x="\<rho>" in allE, erule_tac x="X \<union> Y" in allE, auto)
            apply (erule_tac x="W \<union> Y" in allE, erule_tac x="[Tock]\<^sub>E # \<sigma>'" in allE, auto)
            using intersect_refusal_trace_refusal_subset_idempotent by blast
        qed
      next
        fix \<rho>1 \<rho>2 A
        assume case_assms2: "p = \<rho>1 @ [A]\<^sub>R # \<rho>2" "X = A \<inter> W" "[Tock]\<^sub>E # \<sigma>' = intersect_refusal_trace W (\<rho>2 @ [[Z]\<^sub>R]) @ q" "\<rho> = intersect_refusal_trace W \<rho>1"

        have "{e. e \<noteq> Tock \<and> \<rho>1 @ [[e]\<^sub>E] \<in> P \<or> e = Tock \<and> \<rho>1 @ [[X]\<^sub>R, [e]\<^sub>E] \<in> P}
          \<subseteq> {e. e \<noteq> Tock \<and> \<rho> @ [[e]\<^sub>E] \<in> P \<triangle>\<^sub>U Q \<or> e = Tock \<and> \<rho> @ [[X]\<^sub>R, [e]\<^sub>E] \<in> P \<triangle>\<^sub>U Q}"
        proof (auto)
          fix x
          assume case_assms3: "\<rho>1 @ [[x]\<^sub>E] \<in> P" "x \<noteq> Tock"
          then show "\<rho> @ [[x]\<^sub>E] \<in> P \<triangle>\<^sub>U Q"
            unfolding UntimedInterruptTTT_def
          proof (cases x, cases "contains_refusal \<rho>1", safe, simp_all)
            fix x1
            assume case_assms4: "contains_refusal \<rho>1" "\<rho>1 @ [[Event x1]\<^sub>E] \<in> P"
            then show "\<forall>p. contains_refusal p \<longrightarrow> p \<in> P \<longrightarrow> (\<exists>p'. p = p' @ [[Tick]\<^sub>E]) \<or> (\<exists>p' Y. p = p' @ [[Y]\<^sub>R]) \<or>
                (\<forall>q. q \<in> Q \<longrightarrow> (\<forall>X. [[X]\<^sub>R] \<in> Q \<longrightarrow> (\<exists>q' Y. q = [Y]\<^sub>R # q') \<or> \<rho> @ [[Event x1]\<^sub>E] \<noteq> intersect_refusal_trace X p @ q)) \<Longrightarrow>
              \<exists>p. p @ [[Tick]\<^sub>E] \<in> P \<and> contains_refusal p \<and> (\<exists>X. [[X]\<^sub>R] \<in> Q \<and> \<rho> @ [[Event x1]\<^sub>E] = intersect_refusal_trace X (p @ [[Tick]\<^sub>E]))"
              apply (erule_tac x="\<rho>1 @ [[Event x1]\<^sub>E]" in allE, auto)
              using ctt_prefix_concat ctt_prefix_imp_prefix_subset not_contains_refusal_ctt_prefix_subset apply blast
              apply (erule_tac x="[]" in allE, auto, simp add: TT0_TT1_empty TT0_Q TT1_Q)
              apply (erule_tac x="W" in allE, auto)
              apply (meson TT1_Q TT1_def case_assms(2) ctt_prefix_subset.simps(1) ctt_prefix_subset.simps(2) subset_iff)
              by (simp add: case_assms2(4) intersect_refusal_trace_concat)
          next
            fix x1
            assume case_assms4: "\<not> contains_refusal \<rho>1" "\<rho>1 @ [[Event x1]\<^sub>E] \<in> P"
            show "\<forall>p. p \<in> P \<longrightarrow> (\<exists>p'. p = p' @ [[Tick]\<^sub>E]) \<or> (\<exists>p' Y. p = p' @ [[Y]\<^sub>R]) \<or> contains_refusal p \<or>
                (\<forall>q. q \<in> Q \<longrightarrow> (\<exists>q' Y. q = [Y]\<^sub>R # q') \<or> \<rho> @ [[Event x1]\<^sub>E] \<noteq> p @ q) \<Longrightarrow>
              \<exists>p. p @ [[Tick]\<^sub>E] \<in> P \<and> contains_refusal p \<and> (\<exists>X. [[X]\<^sub>R] \<in> Q \<and> \<rho> @ [[Event x1]\<^sub>E] = intersect_refusal_trace X (p @ [[Tick]\<^sub>E]))"
              apply (erule_tac x="\<rho>1 @ [[Event x1]\<^sub>E]" in allE, auto)
              using case_assms4(2) apply blast
              apply (simp add: case_assms4(1) not_contains_refusal_append_event)
              using TT0_TT1_empty TT0_Q TT1_Q case_assms2(4) case_assms4(1) not_contains_refusal_intersect_refusal_trace by blast
          next
            assume "\<rho>1 @ [[Tick]\<^sub>E] \<in> P" "\<rho> @ [[Tick]\<^sub>E] \<in> P \<longrightarrow> contains_refusal \<rho>"
            then show "\<exists>p. p @ [[Tick]\<^sub>E] \<in> P \<and> contains_refusal p \<and> (\<exists>X. [[X]\<^sub>R] \<in> Q \<and> \<rho> @ [[Tick]\<^sub>E] = intersect_refusal_trace X (p @ [[Tick]\<^sub>E]))"
              apply (rule_tac x="\<rho>1" in exI, auto)
              using case_assms2(4) not_contains_refusal_intersect_refusal_trace apply fastforce
              apply (rule_tac x="W" in exI, auto)
              apply (meson TT1_Q TT1_def case_assms(2) ctt_prefix_subset.simps(1) ctt_prefix_subset.simps(2) subset_iff)
              apply (simp add: case_assms2(4) intersect_refusal_trace_concat)
              using case_assms2(4) not_contains_refusal_intersect_refusal_trace apply fastforce
              apply (rule_tac x="W" in exI, auto)
              apply (meson TT1_Q TT1_def case_assms(2) ctt_prefix_subset.simps(1) ctt_prefix_subset.simps(2) subset_iff)
              apply (simp add: case_assms2(4) intersect_refusal_trace_concat)
              done
          qed
        next
          fix x
          assume case_assms3: "\<rho>1 @ [[x]\<^sub>E] \<in> P" "x \<noteq> Tock"
          then show "\<rho> @ [[x]\<^sub>E] \<in> P \<triangle>\<^sub>U Q"
            unfolding UntimedInterruptTTT_def
          proof (cases x, cases "contains_refusal \<rho>1", safe, simp_all)
            fix x1
            assume case_assms4: "contains_refusal \<rho>1" "\<rho>1 @ [[Event x1]\<^sub>E] \<in> P"
            then show "\<forall>p. contains_refusal p \<longrightarrow> p \<in> P \<longrightarrow> (\<exists>p'. p = p' @ [[Tick]\<^sub>E]) \<or> (\<exists>p' Y. p = p' @ [[Y]\<^sub>R]) \<or>
                (\<forall>q. q \<in> Q \<longrightarrow> (\<forall>X. [[X]\<^sub>R] \<in> Q \<longrightarrow> (\<exists>q' Y. q = [Y]\<^sub>R # q') \<or> \<rho> @ [[Event x1]\<^sub>E] \<noteq> intersect_refusal_trace X p @ q)) \<Longrightarrow>
              \<exists>p. p @ [[Tick]\<^sub>E] \<in> P \<and> contains_refusal p \<and> (\<exists>X. [[X]\<^sub>R] \<in> Q \<and> \<rho> @ [[Event x1]\<^sub>E] = intersect_refusal_trace X (p @ [[Tick]\<^sub>E]))"
              apply (erule_tac x="\<rho>1 @ [[Event x1]\<^sub>E]" in allE, auto)
              using ctt_prefix_concat ctt_prefix_imp_prefix_subset not_contains_refusal_ctt_prefix_subset apply blast
              apply (erule_tac x="[]" in allE, auto, simp add: TT0_TT1_empty TT0_Q TT1_Q)
              apply (erule_tac x="W" in allE, auto)
              apply (meson TT1_Q TT1_def case_assms(2) ctt_prefix_subset.simps(1) ctt_prefix_subset.simps(2) subset_iff)
              by (simp add: case_assms2(4) intersect_refusal_trace_concat)
          next
            fix x1
            assume case_assms4: "\<not> contains_refusal \<rho>1" "\<rho>1 @ [[Event x1]\<^sub>E] \<in> P"
            show "\<forall>p. p \<in> P \<longrightarrow> (\<exists>p'. p = p' @ [[Tick]\<^sub>E]) \<or> (\<exists>p' Y. p = p' @ [[Y]\<^sub>R]) \<or> contains_refusal p \<or>
                (\<forall>q. q \<in> Q \<longrightarrow> (\<exists>q' Y. q = [Y]\<^sub>R # q') \<or> \<rho> @ [[Event x1]\<^sub>E] \<noteq> p @ q) \<Longrightarrow>
              \<exists>p. p @ [[Tick]\<^sub>E] \<in> P \<and> contains_refusal p \<and> (\<exists>X. [[X]\<^sub>R] \<in> Q \<and> \<rho> @ [[Event x1]\<^sub>E] = intersect_refusal_trace X (p @ [[Tick]\<^sub>E]))"
              apply (erule_tac x="\<rho>1 @ [[Event x1]\<^sub>E]" in allE, auto)
              using case_assms4(2) apply blast
              apply (simp add: case_assms4(1) not_contains_refusal_append_event)
              using TT0_TT1_empty TT0_Q TT1_Q case_assms2(4) case_assms4(1) not_contains_refusal_intersect_refusal_trace by blast
          next
            assume "\<rho>1 @ [[Tick]\<^sub>E] \<in> P" "\<rho> @ [[Tick]\<^sub>E] \<in> P \<longrightarrow> contains_refusal \<rho>"
            then show "\<exists>p. p @ [[Tick]\<^sub>E] \<in> P \<and> contains_refusal p \<and> (\<exists>X. [[X]\<^sub>R] \<in> Q \<and> \<rho> @ [[Tick]\<^sub>E] = intersect_refusal_trace X (p @ [[Tick]\<^sub>E]))"
              apply (rule_tac x="\<rho>1" in exI, auto)
              using case_assms2(4) not_contains_refusal_intersect_refusal_trace apply fastforce
              apply (rule_tac x="W" in exI, auto)
              apply (meson TT1_Q TT1_def case_assms(2) ctt_prefix_subset.simps(1) ctt_prefix_subset.simps(2) subset_iff)
              apply (simp add: case_assms2(4) intersect_refusal_trace_concat)
              using case_assms2(4) not_contains_refusal_intersect_refusal_trace apply fastforce
              apply (rule_tac x="W" in exI, auto)
              apply (meson TT1_Q TT1_def case_assms(2) ctt_prefix_subset.simps(1) ctt_prefix_subset.simps(2) subset_iff)
              apply (simp add: case_assms2(4) intersect_refusal_trace_concat)
              done
          qed
        next
          assume case_assms3: "\<rho>1 @ [[X]\<^sub>R, [Tock]\<^sub>E] \<in> P" "\<rho> @ [[X]\<^sub>R, [Tock]\<^sub>E] \<notin> P \<triangle>\<^sub>U Q"
          have A: "intersect_refusal_trace W \<rho>1 @ [[A \<inter> W]\<^sub>R, [Tock]\<^sub>E] = intersect_refusal_trace W (intersect_refusal_trace W \<rho>1 @ [[A \<inter> W]\<^sub>R, [Tock]\<^sub>E])"
          proof -
            have "\<And>C Ca. intersect_refusal_trace C [[Ca]\<^sub>R::'a cttobs] = [[Ca \<inter> C]\<^sub>R]"
              by (simp add: Int_commute)
            then have "\<exists>C. intersect_refusal_trace W (\<rho>1 @ [[C]\<^sub>R]) = intersect_refusal_trace W \<rho>1 @ [[A \<inter> W]\<^sub>R]"
              by (metis (full_types) intersect_refusal_trace_concat)
            then show ?thesis
              by (metis (no_types) intersect_refusal_trace_end_ref_imp_intersect_refusal_trace_end_ref_tock intersect_refusal_trace_idempotent)
          qed 
          have "\<forall>p. contains_refusal p \<longrightarrow> p \<in> P \<longrightarrow> (\<exists>p'. p = p' @ [[Tick]\<^sub>E]) \<or> (\<exists>p' Y. p = p' @ [[Y]\<^sub>R]) \<or>
            (\<forall>q. q \<in> Q \<longrightarrow> (\<forall>Xa. [[Xa]\<^sub>R] \<in> Q \<longrightarrow> (\<exists>q' Y. q = [Y]\<^sub>R # q') \<or> \<rho> @ [[X]\<^sub>R, [Tock]\<^sub>E] \<noteq> intersect_refusal_trace Xa p @ q))"
            using case_assms3(2) unfolding UntimedInterruptTTT_def by (auto)
          then show "False"
            using case_assms case_assms2 apply (erule_tac x="\<rho> @ [[X]\<^sub>R, [Tock]\<^sub>E]" in allE, auto)
            apply (meson ctt_prefix_subset.simps(1) ctt_prefix_subset.simps(2) ctt_prefix_subset_same_front not_contains_refusal_ctt_prefix_subset_end_nonref subsetI)
            apply (metis TT1_P TT1_def case_assms3(1) intersect_refusal_trace_append_prefix_subset)
            apply (erule_tac x="[]" in allE, auto)+
            using TT0_TT1_empty TT0_Q TT1_Q apply blast
            apply (erule_tac x="W" in allE, auto)
             apply (metis TT1_Q TT1_def append.left_neutral append_Cons ctt_prefix_concat ctt_prefix_imp_prefix_subset)
            using case_assms case_assms2 A by (auto)
        next
          assume case_assms3: "\<rho>1 @ [[X]\<^sub>R, [Tock]\<^sub>E] \<in> P" "\<rho> @ [[X]\<^sub>R, [Tock]\<^sub>E] \<notin> P \<triangle>\<^sub>U Q"
          have A: "intersect_refusal_trace W \<rho>1 @ [[A \<inter> W]\<^sub>R, [Tock]\<^sub>E] = intersect_refusal_trace W (intersect_refusal_trace W \<rho>1 @ [[A \<inter> W]\<^sub>R, [Tock]\<^sub>E])"
          proof -
            have "\<And>C Ca. intersect_refusal_trace C [[Ca]\<^sub>R::'a cttobs] = [[Ca \<inter> C]\<^sub>R]"
              by (simp add: Int_commute)
            then have "\<exists>C. intersect_refusal_trace W (\<rho>1 @ [[C]\<^sub>R]) = intersect_refusal_trace W \<rho>1 @ [[A \<inter> W]\<^sub>R]"
              by (metis (full_types) intersect_refusal_trace_concat)
            then show ?thesis
              by (metis (no_types) intersect_refusal_trace_end_ref_imp_intersect_refusal_trace_end_ref_tock intersect_refusal_trace_idempotent)
          qed 
          have "\<forall>p. contains_refusal p \<longrightarrow> p \<in> P \<longrightarrow> (\<exists>p'. p = p' @ [[Tick]\<^sub>E]) \<or> (\<exists>p' Y. p = p' @ [[Y]\<^sub>R]) \<or>
            (\<forall>q. q \<in> Q \<longrightarrow> (\<forall>Xa. [[Xa]\<^sub>R] \<in> Q \<longrightarrow> (\<exists>q' Y. q = [Y]\<^sub>R # q') \<or> \<rho> @ [[X]\<^sub>R, [Tock]\<^sub>E] \<noteq> intersect_refusal_trace Xa p @ q))"
            using case_assms3(2) unfolding UntimedInterruptTTT_def by (auto)
          then show "\<rho> @ [[Tock]\<^sub>E] \<in> P \<triangle>\<^sub>U Q"
            using case_assms case_assms2 apply (erule_tac x="\<rho> @ [[X]\<^sub>R, [Tock]\<^sub>E]" in allE, auto)
            apply (meson ctt_prefix_subset.simps(1) ctt_prefix_subset.simps(2) ctt_prefix_subset_same_front not_contains_refusal_ctt_prefix_subset_end_nonref subsetI)
            apply (metis TT1_P TT1_def case_assms3(1) intersect_refusal_trace_append_prefix_subset)
            apply (erule_tac x="[]" in allE, auto)+
            using TT0_TT1_empty TT0_Q TT1_Q apply blast
            apply (erule_tac x="W" in allE, auto)
             apply (metis TT1_Q TT1_def append.left_neutral append_Cons ctt_prefix_concat ctt_prefix_imp_prefix_subset)
            using case_assms case_assms2 A by (auto)
        qed
        then have 1: "Y \<inter> {e. e \<noteq> Tock \<and> \<rho>1 @ [[e]\<^sub>E] \<in> P \<or> e = Tock \<and> \<rho>1 @ [[X]\<^sub>R, [e]\<^sub>E] \<in> P} = {}"
          using assm2 by auto

        have p_in_P: "p \<in> P"
          using TT1_P TT1_def case_assms(1) ctt_prefix_concat ctt_prefix_imp_prefix_subset by blast
        have \<rho>1_in_P: "\<rho>1 \<in> P"
          using TT1_P TT1_def case_assms2(1) ctt_prefix_concat ctt_prefix_imp_prefix_subset p_in_P by blast
        have \<rho>_in_P: "\<rho> \<in> P"
          using TT1_P TT1_def \<rho>1_in_P case_assms2(4) intersect_refusal_trace_prefix_subset by blast
        have \<rho>_intersect_refusal_trace_idempotent: "\<rho> = intersect_refusal_trace W \<rho>"
          by (simp add: case_assms2(4) intersect_refusal_trace_idempotent)
        have \<rho>1_A_in_P: "\<rho>1 @ [[A]\<^sub>R] \<in> P"
          by (metis TT1_P TT1_def case_assms2(1) ctt_prefix_subset.simps(1) ctt_prefix_subset.simps(2) ctt_prefix_subset_same_front p_in_P subsetI)
        have \<rho>_X_in_P: "\<rho>1 @ [[X]\<^sub>R] \<in> P"
          using TT1_P unfolding TT1_def apply auto apply (erule_tac x="\<rho>1 @ [[X]\<^sub>R]" in allE, auto, erule_tac x="\<rho>1 @ [[A]\<^sub>R]" in allE, auto)
          using \<rho>1_A_in_P case_assms2(2) ctt_prefix_subset_same_front by fastforce+
        have \<rho>1_A_intersect_refusal_trace: "\<rho> @ [[X]\<^sub>R] = intersect_refusal_trace W (\<rho>1 @ [[A]\<^sub>R])"
          by (simp add: Int_commute case_assms2(2) case_assms2(4) intersect_refusal_trace_concat)
        have \<rho>1_X_intersect_refusal_trace_idempotent: "\<rho> @ [[X]\<^sub>R] = intersect_refusal_trace W (\<rho> @ [[X]\<^sub>R])"
          by (simp add: \<rho>1_A_intersect_refusal_trace intersect_refusal_trace_idempotent)

        have "{e. e \<noteq> Tock \<and> [[e]\<^sub>E] \<in> Q \<or> e = Tock \<and> [[W]\<^sub>R, [e]\<^sub>E] \<in> Q}
            \<subseteq> {e. e \<noteq> Tock \<and> \<rho> @ [[e]\<^sub>E] \<in> P \<triangle>\<^sub>U Q \<or> e = Tock \<and> \<rho> @ [[X]\<^sub>R, [e]\<^sub>E] \<in> P \<triangle>\<^sub>U Q}"
        proof auto
          fix x
          assume case_assms2: "[[x]\<^sub>E] \<in> Q" "x \<noteq> Tock"
          then show "\<rho> @ [[x]\<^sub>E] \<in> P \<triangle>\<^sub>U Q"
          proof (cases "contains_refusal \<rho>", auto)
            assume case_assms3: "contains_refusal \<rho>"
            show "\<rho> @ [[x]\<^sub>E] \<in> P \<triangle>\<^sub>U Q"
              unfolding UntimedInterruptTTT_def
            proof (auto)
              show "\<forall>p. contains_refusal p \<longrightarrow> p \<in> P \<longrightarrow> (\<exists>p'. p = p' @ [[Tick]\<^sub>E]) \<or> (\<exists>p' Y. p = p' @ [[Y]\<^sub>R]) \<or>
                (\<forall>q. q \<in> Q \<longrightarrow> (\<forall>X. [[X]\<^sub>R] \<in> Q \<longrightarrow> (\<exists>q' Y. q = [Y]\<^sub>R # q') \<or> \<rho> @ [[x]\<^sub>E] \<noteq> intersect_refusal_trace X p @ q)) \<Longrightarrow>
                \<rho> @ [[Tick]\<^sub>E] \<in> P"
                apply (erule_tac x="\<rho>" in allE, auto simp add: case_assms3 \<rho>_in_P \<rho>_non_tick_refusal)
                apply (erule_tac x="[[x]\<^sub>E]" in allE, auto simp add: case_assms2)
                apply (erule_tac x="W" in allE, auto)
                apply (meson TT1_Q TT1_def case_assms(2) ctt_prefix_subset.simps(1) ctt_prefix_subset.simps(2) ctt_prefix_subset_refl)
                using \<rho>_intersect_refusal_trace_idempotent by blast
            next
              show "\<forall>p. contains_refusal p \<longrightarrow> p \<in> P \<longrightarrow> (\<exists>p'. p = p' @ [[Tick]\<^sub>E]) \<or> (\<exists>p' Y. p = p' @ [[Y]\<^sub>R]) \<or>
                (\<forall>q. q \<in> Q \<longrightarrow> (\<forall>X. [[X]\<^sub>R] \<in> Q \<longrightarrow> (\<exists>q' Y. q = [Y]\<^sub>R # q') \<or> \<rho> @ [[x]\<^sub>E] \<noteq> intersect_refusal_trace X p @ q)) \<Longrightarrow>
                False"
                apply (erule_tac x="\<rho>" in allE, auto simp add: case_assms3 \<rho>_in_P \<rho>_non_tick_refusal)
                apply (erule_tac x="[[x]\<^sub>E]" in allE, auto simp add: case_assms2)
                apply (erule_tac x="W" in allE, auto)
                apply (meson TT1_Q TT1_def case_assms(2) ctt_prefix_subset.simps(1) ctt_prefix_subset.simps(2) ctt_prefix_subset_refl)
                using \<rho>_intersect_refusal_trace_idempotent by blast
            next
              show "\<forall>p. contains_refusal p \<longrightarrow> p \<in> P \<longrightarrow> (\<exists>p'. p = p' @ [[Tick]\<^sub>E]) \<or> (\<exists>p' Y. p = p' @ [[Y]\<^sub>R]) \<or>
                (\<forall>q. q \<in> Q \<longrightarrow> (\<forall>X. [[X]\<^sub>R] \<in> Q \<longrightarrow> (\<exists>q' Y. q = [Y]\<^sub>R # q') \<or> \<rho> @ [[x]\<^sub>E] \<noteq> intersect_refusal_trace X p @ q)) \<Longrightarrow>
                x = Tick"
                apply (erule_tac x="\<rho>" in allE, auto simp add: case_assms3 \<rho>_in_P \<rho>_non_tick_refusal)
                apply (erule_tac x="[[x]\<^sub>E]" in allE, auto simp add: case_assms2)
                apply (erule_tac x="W" in allE, auto)
                apply (meson TT1_Q TT1_def case_assms(2) ctt_prefix_subset.simps(1) ctt_prefix_subset.simps(2) ctt_prefix_subset_refl)
                using \<rho>_intersect_refusal_trace_idempotent by blast
            qed
          next
            assume case_assms3: "\<not> contains_refusal \<rho>"
            show " \<rho> @ [[x]\<^sub>E] \<in> P \<triangle>\<^sub>U Q"
              unfolding UntimedInterruptTTT_def
            proof (auto)
              show "\<forall>p. p \<in> P \<longrightarrow> (\<exists>p'. p = p' @ [[Tick]\<^sub>E]) \<or> (\<exists>p' Y. p = p' @ [[Y]\<^sub>R]) \<or> contains_refusal p \<or>
                (\<forall>q. q \<in> Q \<longrightarrow> (\<exists>q' Y. q = [Y]\<^sub>R # q') \<or> \<rho> @ [[x]\<^sub>E] \<noteq> p @ q) \<Longrightarrow> \<rho> @ [[Tick]\<^sub>E] \<in> P"
                using case_assms case_assms2 case_assms3 apply (erule_tac x="\<rho>" in allE, auto)
                using \<rho>_in_P \<rho>_non_tick_refusal by blast+
            next
              show "\<forall>p. p \<in> P \<longrightarrow> (\<exists>p'. p = p' @ [[Tick]\<^sub>E]) \<or> (\<exists>p' Y. p = p' @ [[Y]\<^sub>R]) \<or> contains_refusal p \<or>
                (\<forall>q. q \<in> Q \<longrightarrow> (\<exists>q' Y. q = [Y]\<^sub>R # q') \<or> \<rho> @ [[x]\<^sub>E] \<noteq> p @ q) \<Longrightarrow> False"
                using case_assms case_assms2 case_assms3 apply (erule_tac x="\<rho>" in allE, auto)
                using \<rho>_in_P \<rho>_non_tick_refusal by blast+
            next
              show "\<forall>p. p \<in> P \<longrightarrow> (\<exists>p'. p = p' @ [[Tick]\<^sub>E]) \<or> (\<exists>p' Y. p = p' @ [[Y]\<^sub>R]) \<or> contains_refusal p \<or>
                (\<forall>q. q \<in> Q \<longrightarrow> (\<exists>q' Y. q = [Y]\<^sub>R # q') \<or> \<rho> @ [[x]\<^sub>E] \<noteq> p @ q) \<Longrightarrow> x = Tick"
                using case_assms case_assms2 case_assms3 apply (erule_tac x="\<rho>" in allE, auto)
                using \<rho>_in_P \<rho>_non_tick_refusal by blast+
            qed
          qed
        next
          fix x
          assume case_assms2: "[[x]\<^sub>E] \<in> Q" "x \<noteq> Tock"
          then show "\<rho> @ [[x]\<^sub>E] \<in> P \<triangle>\<^sub>U Q"
          proof (cases "contains_refusal \<rho>", auto)
            assume case_assms3: "contains_refusal \<rho>"
            show "\<rho> @ [[x]\<^sub>E] \<in> P \<triangle>\<^sub>U Q"
              unfolding UntimedInterruptTTT_def
            proof (auto)
              show "\<forall>p. contains_refusal p \<longrightarrow> p \<in> P \<longrightarrow> (\<exists>p'. p = p' @ [[Tick]\<^sub>E]) \<or> (\<exists>p' Y. p = p' @ [[Y]\<^sub>R]) \<or>
                (\<forall>q. q \<in> Q \<longrightarrow> (\<forall>X. [[X]\<^sub>R] \<in> Q \<longrightarrow> (\<exists>q' Y. q = [Y]\<^sub>R # q') \<or> \<rho> @ [[x]\<^sub>E] \<noteq> intersect_refusal_trace X p @ q)) \<Longrightarrow>
                \<rho> @ [[Tick]\<^sub>E] \<in> P"
                apply (erule_tac x="\<rho>" in allE, auto simp add: case_assms3 \<rho>_in_P \<rho>_non_tick_refusal)
                apply (erule_tac x="[[x]\<^sub>E]" in allE, auto simp add: case_assms2)
                apply (erule_tac x="W" in allE, auto)
                apply (meson TT1_Q TT1_def case_assms(2) ctt_prefix_subset.simps(1) ctt_prefix_subset.simps(2) ctt_prefix_subset_refl)
                using \<rho>_intersect_refusal_trace_idempotent by blast
            next
              show "\<forall>p. contains_refusal p \<longrightarrow> p \<in> P \<longrightarrow> (\<exists>p'. p = p' @ [[Tick]\<^sub>E]) \<or> (\<exists>p' Y. p = p' @ [[Y]\<^sub>R]) \<or>
                (\<forall>q. q \<in> Q \<longrightarrow> (\<forall>X. [[X]\<^sub>R] \<in> Q \<longrightarrow> (\<exists>q' Y. q = [Y]\<^sub>R # q') \<or> \<rho> @ [[x]\<^sub>E] \<noteq> intersect_refusal_trace X p @ q)) \<Longrightarrow>
                False"
                apply (erule_tac x="\<rho>" in allE, auto simp add: case_assms3 \<rho>_in_P \<rho>_non_tick_refusal)
                apply (erule_tac x="[[x]\<^sub>E]" in allE, auto simp add: case_assms2)
                apply (erule_tac x="W" in allE, auto)
                apply (meson TT1_Q TT1_def case_assms(2) ctt_prefix_subset.simps(1) ctt_prefix_subset.simps(2) ctt_prefix_subset_refl)
                using \<rho>_intersect_refusal_trace_idempotent by blast
            next
              show "\<forall>p. contains_refusal p \<longrightarrow> p \<in> P \<longrightarrow> (\<exists>p'. p = p' @ [[Tick]\<^sub>E]) \<or> (\<exists>p' Y. p = p' @ [[Y]\<^sub>R]) \<or>
                (\<forall>q. q \<in> Q \<longrightarrow> (\<forall>X. [[X]\<^sub>R] \<in> Q \<longrightarrow> (\<exists>q' Y. q = [Y]\<^sub>R # q') \<or> \<rho> @ [[x]\<^sub>E] \<noteq> intersect_refusal_trace X p @ q)) \<Longrightarrow>
                x = Tick"
                apply (erule_tac x="\<rho>" in allE, auto simp add: case_assms3 \<rho>_in_P \<rho>_non_tick_refusal)
                apply (erule_tac x="[[x]\<^sub>E]" in allE, auto simp add: case_assms2)
                apply (erule_tac x="W" in allE, auto)
                apply (meson TT1_Q TT1_def case_assms(2) ctt_prefix_subset.simps(1) ctt_prefix_subset.simps(2) ctt_prefix_subset_refl)
                using \<rho>_intersect_refusal_trace_idempotent by blast
            qed
          next
            assume case_assms3: "\<not> contains_refusal \<rho>"
            show " \<rho> @ [[x]\<^sub>E] \<in> P \<triangle>\<^sub>U Q"
              unfolding UntimedInterruptTTT_def
            proof (auto)
              show "\<forall>p. p \<in> P \<longrightarrow> (\<exists>p'. p = p' @ [[Tick]\<^sub>E]) \<or> (\<exists>p' Y. p = p' @ [[Y]\<^sub>R]) \<or> contains_refusal p \<or>
                (\<forall>q. q \<in> Q \<longrightarrow> (\<exists>q' Y. q = [Y]\<^sub>R # q') \<or> \<rho> @ [[x]\<^sub>E] \<noteq> p @ q) \<Longrightarrow> \<rho> @ [[Tick]\<^sub>E] \<in> P"
                using case_assms case_assms2 case_assms3 apply (erule_tac x="\<rho>" in allE, auto)
                using \<rho>_in_P \<rho>_non_tick_refusal by blast+
            next
              show "\<forall>p. p \<in> P \<longrightarrow> (\<exists>p'. p = p' @ [[Tick]\<^sub>E]) \<or> (\<exists>p' Y. p = p' @ [[Y]\<^sub>R]) \<or> contains_refusal p \<or>
                (\<forall>q. q \<in> Q \<longrightarrow> (\<exists>q' Y. q = [Y]\<^sub>R # q') \<or> \<rho> @ [[x]\<^sub>E] \<noteq> p @ q) \<Longrightarrow> False"
                using case_assms case_assms2 case_assms3 apply (erule_tac x="\<rho>" in allE, auto)
                using \<rho>_in_P \<rho>_non_tick_refusal by blast+
            next
              show "\<forall>p. p \<in> P \<longrightarrow> (\<exists>p'. p = p' @ [[Tick]\<^sub>E]) \<or> (\<exists>p' Y. p = p' @ [[Y]\<^sub>R]) \<or> contains_refusal p \<or>
                (\<forall>q. q \<in> Q \<longrightarrow> (\<exists>q' Y. q = [Y]\<^sub>R # q') \<or> \<rho> @ [[x]\<^sub>E] \<noteq> p @ q) \<Longrightarrow> x = Tick"
                using case_assms case_assms2 case_assms3 apply (erule_tac x="\<rho>" in allE, auto)
                using \<rho>_in_P \<rho>_non_tick_refusal by blast+
            qed
          qed
        next
          fix x
          assume case_assms3: "[[W]\<^sub>R, [Tock]\<^sub>E] \<in> Q"
          show "\<rho> @ [[X]\<^sub>R, [Tock]\<^sub>E] \<notin> P \<triangle>\<^sub>U Q \<Longrightarrow> False"
            unfolding UntimedInterruptTTT_def
          proof (auto)
            show "\<forall>p Xa. p @ [[Xa]\<^sub>R] \<in> P \<longrightarrow> (\<forall>Y q. [Y]\<^sub>R # q \<in> Q \<longrightarrow> \<rho> @ [[X]\<^sub>R, [Tock]\<^sub>E] \<noteq> intersect_refusal_trace Y (p @ [[Xa]\<^sub>R]) @ q) \<Longrightarrow>
              False"
              using case_assms case_assms3 apply (erule_tac x="\<rho>" in allE, auto, erule_tac x="X" in allE, auto)
              using TT1_P TT1_def \<rho>_X_in_P case_assms2(4) intersect_refusal_trace_append_prefix_subset apply blast
              apply (erule_tac x="W" in allE, erule_tac x="[[Tock]\<^sub>E]" in allE, auto)
              using \<rho>1_X_intersect_refusal_trace_idempotent by linarith
          qed
        next
          fix x
          assume case_assms3: "[[W]\<^sub>R, [Tock]\<^sub>E] \<in> Q"
          show "\<rho> @ [[X]\<^sub>R, [Tock]\<^sub>E] \<notin> P \<triangle>\<^sub>U Q \<Longrightarrow> \<rho> @ [[Tock]\<^sub>E] \<in> P \<triangle>\<^sub>U Q"
            unfolding UntimedInterruptTTT_def
          proof (auto)
            show "\<forall>p Xa. p @ [[Xa]\<^sub>R] \<in> P \<longrightarrow> (\<forall>Y q. [Y]\<^sub>R # q \<in> Q \<longrightarrow> \<rho> @ [[X]\<^sub>R, [Tock]\<^sub>E] \<noteq> intersect_refusal_trace Y (p @ [[Xa]\<^sub>R]) @ q) \<Longrightarrow>
              \<exists>p. p \<in> P \<and> (\<forall>p'. p \<noteq> p' @ [[Tick]\<^sub>E]) \<and> (\<forall>p' Y. p \<noteq> p' @ [[Y]\<^sub>R]) \<and> contains_refusal p \<and>
                (\<exists>q X. [[X]\<^sub>R] \<in> Q \<and> q \<in> Q \<and> (\<forall>q' Y. q \<noteq> [Y]\<^sub>R # q') \<and> \<rho> @ [[Tock]\<^sub>E] = intersect_refusal_trace X p @ q) "
              using case_assms case_assms3 apply (erule_tac x="\<rho>" in allE, auto, erule_tac x="X" in allE, auto)
              apply (metis TT1_P TT1_def \<rho>_X_in_P case_assms2(4) intersect_refusal_trace_append_prefix_subset)
              apply (erule_tac x="W" in allE, erule_tac x="[[Tock]\<^sub>E]" in allE, auto)
              using \<rho>1_X_intersect_refusal_trace_idempotent by linarith
          qed
        qed
        then have 2: "Y \<inter> {e. e \<noteq> Tock \<and> [[e]\<^sub>E] \<in> Q \<or> e = Tock \<and> [[W]\<^sub>R, [e]\<^sub>E] \<in> Q} = {}"
          using assm2 by auto

        have 3: "\<rho>1 @ [A]\<^sub>R # \<rho>2 @ [[Z]\<^sub>R] \<in> P"
          using case_assms(1) case_assms2(1) by auto
        have 4: "\<rho>1 @ [X]\<^sub>R # \<rho>2 @ [[Z]\<^sub>R] \<in> P"
          using TT1_P 3 unfolding TT1_def apply auto apply (erule_tac x="\<rho>1 @ [X]\<^sub>R # \<rho>2 @ [[Z]\<^sub>R]" in allE, auto)
          by (metis case_assms2(2) ctt_prefix_subset.simps(2) ctt_prefix_subset_refl ctt_prefix_subset_same_front inf_le1)
        have 5: "\<rho>1 @ [X \<union> Y]\<^sub>R # \<rho>2 @ [[Z]\<^sub>R] \<in> P"
          using 1 4 TT2s_P unfolding TT2s_def by auto
        have 6: "\<rho>1 @ [X \<union> Y]\<^sub>R # \<rho>2 @ [[Z \<inter> W]\<^sub>R] \<in> P"
          using 5 TT1_P unfolding TT1_def apply auto apply (erule_tac x="\<rho>1 @ [X \<union> Y]\<^sub>R # \<rho>2 @ [[Z \<inter> W]\<^sub>R]" in allE, auto)
          by (metis append_Cons ctt_prefix_subset.simps(1) ctt_prefix_subset.simps(2) ctt_prefix_subset_same_front inf_le1)
        have 7: "[W \<union> Y]\<^sub>R # q \<in> Q"
          using case_assms(2) 2 TT2s_Q unfolding TT2s_def apply auto
          apply (erule_tac x="[]" in allE, erule_tac x="q" in allE)
          by (erule_tac x="W" in allE, erule_tac x="Y" in allE, auto)
        obtain \<rho>3 where 8: "\<rho>3 = intersect_refusal_trace W \<rho>2"
          by auto
        have 11: "\<rho> @ [X \<union> Y]\<^sub>R # \<rho>3 @ [[Z \<inter> W]\<^sub>R] \<subseteq>\<^sub>C \<rho>1 @ [X \<union> Y]\<^sub>R # \<rho>2 @ [[Z \<inter> W]\<^sub>R]"
          by (simp add: "8" case_assms2(4) ctt_subset_combine intersect_refusal_trace_subset)
        have 12: "\<rho> @ [X \<union> Y]\<^sub>R # \<rho>3 @ [[Z \<inter> W]\<^sub>R] \<in> P"
          using TT1_P ctt_subset_imp_prefix_subset 6 11 unfolding TT1_def by auto
        have 13: "intersect_refusal_trace W \<rho>1 @ [A \<inter> W \<union> Y]\<^sub>R # intersect_refusal_trace W (\<rho>2 @ [[Z]\<^sub>R]) =
          intersect_refusal_trace (W \<union> Y) (\<rho> @ [X \<union> Y]\<^sub>R # \<rho>3 @ [[Z \<inter> W]\<^sub>R])"
          by (smt "8" Int_commute Un_Int_distrib2 \<rho>_intersect_refusal_trace_idempotent case_assms2(2) case_assms2(4)
              intersect_refusal_trace.simps(1) intersect_refusal_trace.simps(3) intersect_refusal_trace_concat
              intersect_refusal_trace_idempotent intersect_refusal_trace_idempotent_widen_refusal)

        show "intersect_refusal_trace W \<rho>1 @ [A \<inter> W \<union> Y]\<^sub>R # intersect_refusal_trace W (\<rho>2 @ [[Z]\<^sub>R]) @ q \<in> P \<triangle>\<^sub>U Q"
          unfolding UntimedInterruptTTT_def
        proof auto
          show "\<forall>p X. p @ [[X]\<^sub>R] \<in> P \<longrightarrow> (\<forall>Ya qa. [Ya]\<^sub>R # qa \<in> Q \<longrightarrow>
              intersect_refusal_trace W \<rho>1 @ [A \<inter> W \<union> Y]\<^sub>R # intersect_refusal_trace W (\<rho>2 @ [[Z]\<^sub>R]) @ q \<noteq> intersect_refusal_trace Ya (p @ [[X]\<^sub>R]) @ qa) \<Longrightarrow>
            \<exists>p. p \<in> P \<and> (\<forall>p'. p \<noteq> p' @ [[Tick]\<^sub>E]) \<and> (\<forall>p' Y. p \<noteq> p' @ [[Y]\<^sub>R]) \<and> contains_refusal p \<and>
              (\<exists>qa X. [[X]\<^sub>R] \<in> Q \<and> qa \<in> Q \<and> (\<forall>q' Y. qa \<noteq> [Y]\<^sub>R # q') \<and>
              intersect_refusal_trace W \<rho>1 @ [A \<inter> W \<union> Y]\<^sub>R # intersect_refusal_trace W (\<rho>2 @ [[Z]\<^sub>R]) @ q = intersect_refusal_trace X p @ qa)"
            using 7 12 13 apply (erule_tac x="\<rho> @ [X \<union> Y]\<^sub>R # \<rho>3" in allE, erule_tac x="Z \<inter> W" in allE, auto)
            by (erule_tac x="W \<union> Y" in allE, erule_tac x="q" in allE, auto)
        qed
      next
        fix \<sigma>1
        assume case_assms2: "q = \<sigma>1 @ [X]\<^sub>R # [Tock]\<^sub>E # \<sigma>'" "\<rho> = intersect_refusal_trace W (p @ [[Z]\<^sub>R]) @ \<sigma>1"

        have "{e. e \<noteq> Tock \<and> [W]\<^sub>R # \<sigma>1 @ [[e]\<^sub>E] \<in> Q \<or> e = Tock \<and> [W]\<^sub>R # \<sigma>1 @ [[X]\<^sub>R, [e]\<^sub>E] \<in> Q}
          \<subseteq> {e. e \<noteq> Tock \<and> \<rho> @ [[e]\<^sub>E] \<in> P \<triangle>\<^sub>U Q \<or> e = Tock \<and> \<rho> @ [[X]\<^sub>R, [e]\<^sub>E] \<in> P \<triangle>\<^sub>U Q}"
        proof auto
          fix x
          assume case_assms3: "[W]\<^sub>R # \<sigma>1 @ [[x]\<^sub>E] \<in> Q" "x \<noteq> Tock"
          show "\<rho> @ [[x]\<^sub>E] \<in> P \<triangle>\<^sub>U Q"
            unfolding UntimedInterruptTTT_def
          proof (safe, simp_all)
            show "\<forall>p X. p @ [[X]\<^sub>R] \<in> P \<longrightarrow> (\<forall>Y q. [Y]\<^sub>R # q \<in> Q \<longrightarrow> \<rho> @ [[x]\<^sub>E] \<noteq> intersect_refusal_trace Y (p @ [[X]\<^sub>R]) @ q) \<Longrightarrow>
              \<exists>p. p @ [[Tick]\<^sub>E] \<in> P \<and> contains_refusal p \<and> (\<exists>X. [[X]\<^sub>R] \<in> Q \<and> \<rho> @ [[x]\<^sub>E] = intersect_refusal_trace X (p @ [[Tick]\<^sub>E]))"
              using case_assms(1) case_assms2(2) case_assms3(1) by (erule_tac x="p" in allE, erule_tac x="Z" in allE, auto)
          qed
        next
          fix x
          assume case_assms3: "[W]\<^sub>R # \<sigma>1 @ [[x]\<^sub>E] \<in> Q" "x \<noteq> Tock"
          show "\<rho> @ [[x]\<^sub>E] \<in> P \<triangle>\<^sub>U Q"
            unfolding UntimedInterruptTTT_def
          proof (safe, simp_all)
            show "\<forall>p X. p @ [[X]\<^sub>R] \<in> P \<longrightarrow> (\<forall>Y q. [Y]\<^sub>R # q \<in> Q \<longrightarrow> \<rho> @ [[x]\<^sub>E] \<noteq> intersect_refusal_trace Y (p @ [[X]\<^sub>R]) @ q) \<Longrightarrow>
              \<exists>p. p @ [[Tick]\<^sub>E] \<in> P \<and> contains_refusal p \<and> (\<exists>X. [[X]\<^sub>R] \<in> Q \<and> \<rho> @ [[x]\<^sub>E] = intersect_refusal_trace X (p @ [[Tick]\<^sub>E]))"
              using case_assms(1) case_assms2(2) case_assms3(1) by (erule_tac x="p" in allE, erule_tac x="Z" in allE, auto)
          qed
        next
          assume case_assms3: "[W]\<^sub>R # \<sigma>1 @ [[X]\<^sub>R, [Tock]\<^sub>E] \<in> Q" "\<rho> @ [[X]\<^sub>R, [Tock]\<^sub>E] \<notin> P \<triangle>\<^sub>U Q"
          have "\<forall>p Xa. p @ [[Xa]\<^sub>R] \<in> P \<longrightarrow> (\<forall>Y q. [Y]\<^sub>R # q \<in> Q \<longrightarrow> \<rho> @ [[X]\<^sub>R, [Tock]\<^sub>E] \<noteq> intersect_refusal_trace Y (p @ [[Xa]\<^sub>R]) @ q)"
            using case_assms3(2) unfolding UntimedInterruptTTT_def by auto
          then show "False"
            using case_assms(1) case_assms2(2) case_assms3(1) by (erule_tac x="p" in allE, erule_tac x="Z" in allE, auto)
        next
          assume case_assms3: "[W]\<^sub>R # \<sigma>1 @ [[X]\<^sub>R, [Tock]\<^sub>E] \<in> Q" "\<rho> @ [[X]\<^sub>R, [Tock]\<^sub>E] \<notin> P \<triangle>\<^sub>U Q"
          have "\<forall>p Xa. p @ [[Xa]\<^sub>R] \<in> P \<longrightarrow> (\<forall>Y q. [Y]\<^sub>R # q \<in> Q \<longrightarrow> \<rho> @ [[X]\<^sub>R, [Tock]\<^sub>E] \<noteq> intersect_refusal_trace Y (p @ [[Xa]\<^sub>R]) @ q)"
            using case_assms3(2) unfolding UntimedInterruptTTT_def by auto
          then show "\<rho> @ [[Tock]\<^sub>E] \<in> P \<triangle>\<^sub>U Q"
            using case_assms(1) case_assms2(2) case_assms3(1) by (erule_tac x="p" in allE, erule_tac x="Z" in allE, auto)
        qed
        then have "Y \<inter> {e. e \<noteq> Tock \<and> [W]\<^sub>R # \<sigma>1 @ [[e]\<^sub>E] \<in> Q \<or> e = Tock \<and> [W]\<^sub>R # \<sigma>1 @ [[X]\<^sub>R, [e]\<^sub>E] \<in> Q} = {}"
          using assm2 by auto
        then have "[W]\<^sub>R # \<sigma>1 @ [X \<union> Y]\<^sub>R # [Tock]\<^sub>E # \<sigma>' \<in> Q"
          using TT2s_Q case_assms(2) case_assms2(1) unfolding TT2s_def apply auto
          apply (erule_tac x="[W]\<^sub>R # \<sigma>1" in allE, erule_tac x="[Tock]\<^sub>E # \<sigma>'" in allE)
          by (erule_tac x="X" in allE, erule_tac x="Y" in allE, auto)
        then show "intersect_refusal_trace W (p @ [[Z]\<^sub>R]) @ \<sigma>1 @ [X \<union> Y]\<^sub>R # [Tock]\<^sub>E # \<sigma>' \<in> P \<triangle>\<^sub>U Q"
          unfolding UntimedInterruptTTT_def using case_assms(1) by blast
      qed
    next
      fix p q Z
      assume case_assms: "p \<in> P" "\<forall>p'. p \<noteq> p' @ [[Tick]\<^sub>E]" "\<forall>p' Y. p \<noteq> p' @ [[Y]\<^sub>R]" "contains_refusal p"
        "[[Z]\<^sub>R] \<in> Q" "q \<in> Q" "\<forall>q' Y. q \<noteq> [Y]\<^sub>R # q'" "\<rho> @ [X]\<^sub>R # [Tock]\<^sub>E # \<sigma>' = intersect_refusal_trace Z p @ q"

      have "(\<exists> p1 p2 A. p = p1 @ [A]\<^sub>R # p2 \<and> \<rho> = intersect_refusal_trace Z p1 \<and> X = A \<inter> Z \<and> [Tock]\<^sub>E # \<sigma>' = intersect_refusal_trace Z p2 @ q)
        \<or> (\<exists> q1 q2. q = q1 @ [X]\<^sub>R # q2 \<and> q2 = [Tock]\<^sub>E # \<sigma>' \<and> \<rho> = intersect_refusal_trace Z p @ q1)"
        using case_assms(8) apply - apply (induct \<rho> p rule:ctt_subset.induct, auto)
        apply (rule_tac x="[Y]\<^sub>R # p1" in exI, auto)
        apply (rule_tac x="[y]\<^sub>E # p1" in exI, auto)
        apply (rule_tac x="[]" in exI, auto, case_tac v, auto)
        done
      then show "\<rho> @ [X \<union> Y]\<^sub>R # [Tock]\<^sub>E # \<sigma>' \<in> P \<triangle>\<^sub>U Q"
      proof auto
        fix p1 p2 A
        assume case_assms2: "p = p1 @ [A]\<^sub>R # p2" "\<rho> = intersect_refusal_trace Z p1" "[Tock]\<^sub>E # \<sigma>' = intersect_refusal_trace Z p2 @ q" "X = A \<inter> Z"

        have "{e. e \<noteq> Tock \<and> p1 @ [[e]\<^sub>E] \<in> P \<or> e = Tock \<and> p1 @ [[X]\<^sub>R, [e]\<^sub>E] \<in> P}
          \<subseteq> {e. e \<noteq> Tock \<and> \<rho> @ [[e]\<^sub>E] \<in> P \<triangle>\<^sub>U Q \<or> e = Tock \<and> \<rho> @ [[X]\<^sub>R, [e]\<^sub>E] \<in> P \<triangle>\<^sub>U Q}"
        proof auto
          fix x
          assume case_assms3: "p1 @ [[x]\<^sub>E] \<in> P" "x \<noteq> Tock"
          show "\<rho> @ [[x]\<^sub>E] \<in> P \<triangle>\<^sub>U Q"
            unfolding UntimedInterruptTTT_def
          proof (safe, simp_all, cases x, cases "contains_refusal p1")
            fix x1
            assume "x = Event x1" "contains_refusal p1"
            then show "\<forall>p. contains_refusal p \<longrightarrow> p \<in> P \<longrightarrow> (\<exists>p'. p = p' @ [[Tick]\<^sub>E]) \<or> (\<exists>p' Y. p = p' @ [[Y]\<^sub>R]) \<or>
                (\<forall>q. q \<in> Q \<longrightarrow> (\<forall>X. [[X]\<^sub>R] \<in> Q \<longrightarrow> (\<exists>q' Y. q = [Y]\<^sub>R # q') \<or> \<rho> @ [[x]\<^sub>E] \<noteq> intersect_refusal_trace X p @ q)) \<Longrightarrow>
              \<exists>p. p @ [[Tick]\<^sub>E] \<in> P \<and> contains_refusal p \<and> (\<exists>X. [[X]\<^sub>R] \<in> Q \<and> \<rho> @ [[x]\<^sub>E] = intersect_refusal_trace X (p @ [[Tick]\<^sub>E]))"
              using case_assms3 apply (erule_tac x="p1 @ [[x]\<^sub>E]" in allE, auto)
              using ctt_prefix_concat ctt_prefix_imp_prefix_subset not_contains_refusal_ctt_prefix_subset apply blast
              apply (erule_tac x="[]" in allE, auto)
              using TT0_TT1_empty TT0_Q TT1_Q apply blast
              by (metis case_assms(5) case_assms2(2) contains_refusal.simps(1) contains_refusal.simps(3) intersect_refusal_trace_concat not_contains_refusal_intersect_refusal_trace)
          next
            fix x1
            assume "x = Event x1" "\<not> contains_refusal p1"
            then show "\<forall>p. p \<in> P \<longrightarrow> (\<exists>p'. p = p' @ [[Tick]\<^sub>E]) \<or> (\<exists>p' Y. p = p' @ [[Y]\<^sub>R]) \<or> contains_refusal p \<or>
                (\<forall>q. q \<in> Q \<longrightarrow> (\<exists>q' Y. q = [Y]\<^sub>R # q') \<or> \<rho> @ [[x]\<^sub>E] \<noteq> p @ q) \<Longrightarrow>
              \<exists>p. p @ [[Tick]\<^sub>E] \<in> P \<and> contains_refusal p \<and> (\<exists>X. [[X]\<^sub>R] \<in> Q \<and> \<rho> @ [[x]\<^sub>E] = intersect_refusal_trace X (p @ [[Tick]\<^sub>E]))"
              using case_assms3 apply (erule_tac x="p1 @ [[x]\<^sub>E]" in allE, auto simp add: not_contains_refusal_append_event)
              using TT0_TT1_empty TT0_Q TT1_Q apply (erule_tac x="[]" in allE, auto)
              by (simp add: case_assms2(2) not_contains_refusal_intersect_refusal_trace)
          next
            show "x = Tock \<Longrightarrow> \<exists>p. p @ [[Tick]\<^sub>E] \<in> P \<and> contains_refusal p \<and> (\<exists>X. [[X]\<^sub>R] \<in> Q \<and> \<rho> @ [[x]\<^sub>E] = intersect_refusal_trace X (p @ [[Tick]\<^sub>E]))"
              using case_assms3(2) by blast
          next
            assume " \<rho> @ [[Tick]\<^sub>E] \<in> P \<longrightarrow> contains_refusal \<rho> \<or> x \<noteq> Tick" "x = Tick"
            then show "\<exists>p. p @ [[Tick]\<^sub>E] \<in> P \<and> contains_refusal p \<and> (\<exists>X. [[X]\<^sub>R] \<in> Q \<and> \<rho> @ [[x]\<^sub>E] = intersect_refusal_trace X (p @ [[Tick]\<^sub>E]))"
              using case_assms case_assms2 case_assms3 apply auto
              apply (meson TT1_P TT1_def intersect_refusal_trace_append_prefix_subset)
              using not_contains_refusal_intersect_refusal_trace apply (rule_tac x="p1" in exI, auto, fastforce)
              by (smt contains_refusal.simps(1) contains_refusal.simps(3) intersect_refusal_trace_concat)
          qed
        next
          fix x
          assume case_assms3: "p1 @ [[x]\<^sub>E] \<in> P" "x \<noteq> Tock"
          show "\<rho> @ [[x]\<^sub>E] \<in> P \<triangle>\<^sub>U Q"
            unfolding UntimedInterruptTTT_def
          proof (safe, simp_all, cases x, cases "contains_refusal p1")
            fix x1
            assume "x = Event x1" "contains_refusal p1"
            then show "\<forall>p. contains_refusal p \<longrightarrow> p \<in> P \<longrightarrow> (\<exists>p'. p = p' @ [[Tick]\<^sub>E]) \<or> (\<exists>p' Y. p = p' @ [[Y]\<^sub>R]) \<or>
                (\<forall>q. q \<in> Q \<longrightarrow> (\<forall>X. [[X]\<^sub>R] \<in> Q \<longrightarrow> (\<exists>q' Y. q = [Y]\<^sub>R # q') \<or> \<rho> @ [[x]\<^sub>E] \<noteq> intersect_refusal_trace X p @ q)) \<Longrightarrow>
              \<exists>p. p @ [[Tick]\<^sub>E] \<in> P \<and> contains_refusal p \<and> (\<exists>X. [[X]\<^sub>R] \<in> Q \<and> \<rho> @ [[x]\<^sub>E] = intersect_refusal_trace X (p @ [[Tick]\<^sub>E]))"
              using case_assms3 apply (erule_tac x="p1 @ [[x]\<^sub>E]" in allE, auto)
              using ctt_prefix_concat ctt_prefix_imp_prefix_subset not_contains_refusal_ctt_prefix_subset apply blast
              apply (erule_tac x="[]" in allE, auto)
              using TT0_TT1_empty TT0_Q TT1_Q apply blast
              by (metis case_assms(5) case_assms2(2) contains_refusal.simps(1) contains_refusal.simps(3) intersect_refusal_trace_concat not_contains_refusal_intersect_refusal_trace)
          next
            fix x1
            assume "x = Event x1" "\<not> contains_refusal p1"
            then show "\<forall>p. p \<in> P \<longrightarrow> (\<exists>p'. p = p' @ [[Tick]\<^sub>E]) \<or> (\<exists>p' Y. p = p' @ [[Y]\<^sub>R]) \<or> contains_refusal p \<or>
                (\<forall>q. q \<in> Q \<longrightarrow> (\<exists>q' Y. q = [Y]\<^sub>R # q') \<or> \<rho> @ [[x]\<^sub>E] \<noteq> p @ q) \<Longrightarrow>
              \<exists>p. p @ [[Tick]\<^sub>E] \<in> P \<and> contains_refusal p \<and> (\<exists>X. [[X]\<^sub>R] \<in> Q \<and> \<rho> @ [[x]\<^sub>E] = intersect_refusal_trace X (p @ [[Tick]\<^sub>E]))"
              using case_assms3 apply (erule_tac x="p1 @ [[x]\<^sub>E]" in allE, auto simp add: not_contains_refusal_append_event)
              using TT0_TT1_empty TT0_Q TT1_Q apply (erule_tac x="[]" in allE, auto)
              by (simp add: case_assms2(2) not_contains_refusal_intersect_refusal_trace)
          next
            show "x = Tock \<Longrightarrow> \<exists>p. p @ [[Tick]\<^sub>E] \<in> P \<and> contains_refusal p \<and> (\<exists>X. [[X]\<^sub>R] \<in> Q \<and> \<rho> @ [[x]\<^sub>E] = intersect_refusal_trace X (p @ [[Tick]\<^sub>E]))"
              using case_assms3(2) by blast
          next
            assume " \<rho> @ [[Tick]\<^sub>E] \<in> P \<longrightarrow> contains_refusal \<rho> \<or> x \<noteq> Tick" "x = Tick"
            then show "\<exists>p. p @ [[Tick]\<^sub>E] \<in> P \<and> contains_refusal p \<and> (\<exists>X. [[X]\<^sub>R] \<in> Q \<and> \<rho> @ [[x]\<^sub>E] = intersect_refusal_trace X (p @ [[Tick]\<^sub>E]))"
              using case_assms case_assms2 case_assms3 apply auto
              apply (meson TT1_P TT1_def intersect_refusal_trace_append_prefix_subset)
              using not_contains_refusal_intersect_refusal_trace apply (rule_tac x="p1" in exI, auto, fastforce)
              by (smt contains_refusal.simps(1) contains_refusal.simps(3) intersect_refusal_trace_concat)
          qed
        next
          assume case_assms3: "p1 @ [[X]\<^sub>R, [Tock]\<^sub>E] \<in> P" "\<rho> @ [[X]\<^sub>R, [Tock]\<^sub>E] \<notin> P \<triangle>\<^sub>U Q"
          have "\<forall>p. contains_refusal p \<longrightarrow> p \<in> P \<longrightarrow> (\<exists>p'. p = p' @ [[Tick]\<^sub>E]) \<or> (\<exists>p' Y. p = p' @ [[Y]\<^sub>R]) \<or>
            (\<forall>q. q \<in> Q \<longrightarrow> (\<forall>Xa. [[Xa]\<^sub>R] \<in> Q \<longrightarrow> (\<exists>q' Y. q = [Y]\<^sub>R # q') \<or> \<rho> @ [[X]\<^sub>R, [Tock]\<^sub>E] \<noteq> intersect_refusal_trace Xa p @ q))"
            using case_assms3(2) unfolding UntimedInterruptTTT_def by auto
          then show "False"
            using case_assms3 apply (erule_tac x="p1 @ [[X]\<^sub>R, [Tock]\<^sub>E]" in allE, auto)
            apply (metis append.assoc append.left_neutral append_Cons ctt_prefix_concat ctt_prefix_imp_prefix_subset not_contains_refusal_ctt_prefix_subset_end_nonref)
            apply ((erule_tac x="[]" in allE)+, auto)
            using TT0_TT1_empty TT0_Q TT1_Q apply blast
            apply (erule_tac x="Z" in allE, auto)
            using case_assms(5) apply blast
            by (smt Int_commute Int_left_absorb case_assms2(2) case_assms2(4) contains_refusal.simps(1) contains_refusal.simps(3)
                intersect_refusal_trace.simps(3) intersect_refusal_trace_concat not_contains_refusal_intersect_refusal_trace)
        next
          assume case_assms3: "p1 @ [[X]\<^sub>R, [Tock]\<^sub>E] \<in> P" "\<rho> @ [[X]\<^sub>R, [Tock]\<^sub>E] \<notin> P \<triangle>\<^sub>U Q"
          have "\<forall>p. contains_refusal p \<longrightarrow> p \<in> P \<longrightarrow> (\<exists>p'. p = p' @ [[Tick]\<^sub>E]) \<or> (\<exists>p' Y. p = p' @ [[Y]\<^sub>R]) \<or>
            (\<forall>q. q \<in> Q \<longrightarrow> (\<forall>Xa. [[Xa]\<^sub>R] \<in> Q \<longrightarrow> (\<exists>q' Y. q = [Y]\<^sub>R # q') \<or> \<rho> @ [[X]\<^sub>R, [Tock]\<^sub>E] \<noteq> intersect_refusal_trace Xa p @ q))"
            using case_assms3(2) unfolding UntimedInterruptTTT_def by auto
          then show "\<rho> @ [[Tock]\<^sub>E] \<in> P \<triangle>\<^sub>U Q"
            using case_assms3 apply (erule_tac x="p1 @ [[X]\<^sub>R, [Tock]\<^sub>E]" in allE, auto)
            apply (metis append.assoc append.left_neutral append_Cons ctt_prefix_concat ctt_prefix_imp_prefix_subset not_contains_refusal_ctt_prefix_subset_end_nonref)
            apply ((erule_tac x="[]" in allE)+, auto)
            using TT0_TT1_empty TT0_Q TT1_Q apply blast
            apply (erule_tac x="Z" in allE, auto)
            using case_assms(5) apply blast
            by (smt Int_commute Int_left_absorb case_assms2(2) case_assms2(4) contains_refusal.simps(1) contains_refusal.simps(3)
                intersect_refusal_trace.simps(3) intersect_refusal_trace_concat not_contains_refusal_intersect_refusal_trace)
        qed
        then have "Y \<inter> {e. e \<noteq> Tock \<and> p1 @ [[e]\<^sub>E] \<in> P \<or> e = Tock \<and> p1 @ [[X]\<^sub>R, [e]\<^sub>E] \<in> P} = {}"
          using assm2 by auto
        then have 1: "p1 @ [X \<union> Y]\<^sub>R # p2 \<in> P"
          using TT2s_P unfolding TT2s_def apply auto
          apply (erule_tac x="p1" in allE, erule_tac x="p2" in allE)
          apply (erule_tac x="X" in allE, erule_tac x="Y" in allE, auto)
          by (metis TT1_P TT1_def case_assms(1) case_assms2(1) case_assms2(4) ctt_prefix_subset.simps(2) ctt_prefix_subset_refl ctt_prefix_subset_same_front inf_le1)
        
        have "{e. e \<noteq> Tock \<and> [[e]\<^sub>E] \<in> Q \<or> e = Tock \<and> [[Z]\<^sub>R, [e]\<^sub>E] \<in> Q}
          \<subseteq> {e. e \<noteq> Tock \<and> \<rho> @ [[e]\<^sub>E] \<in> P \<triangle>\<^sub>U Q \<or> e = Tock \<and> \<rho> @ [[X]\<^sub>R, [e]\<^sub>E] \<in> P \<triangle>\<^sub>U Q}"
        proof auto
          fix x
          assume case_assms3: "[[x]\<^sub>E] \<in> Q" "x \<noteq> Tock"
          show "\<rho> @ [[x]\<^sub>E] \<in> P \<triangle>\<^sub>U Q"
            unfolding UntimedInterruptTTT_def
          proof (safe, simp_all, cases "contains_refusal p1")
            assume "contains_refusal p1"
            then show "\<forall>p. contains_refusal p \<longrightarrow> p \<in> P \<longrightarrow> (\<exists>p'. p = p' @ [[Tick]\<^sub>E]) \<or> (\<exists>p' Y. p = p' @ [[Y]\<^sub>R]) \<or>
                (\<forall>q. q \<in> Q \<longrightarrow> (\<forall>X. [[X]\<^sub>R] \<in> Q \<longrightarrow> (\<exists>q' Y. q = [Y]\<^sub>R # q') \<or> \<rho> @ [[x]\<^sub>E] \<noteq> intersect_refusal_trace X p @ q)) \<Longrightarrow>
              \<exists>p. p @ [[Tick]\<^sub>E] \<in> P \<and> contains_refusal p \<and> (\<exists>X. [[X]\<^sub>R] \<in> Q \<and> \<rho> @ [[x]\<^sub>E] = intersect_refusal_trace X (p @ [[Tick]\<^sub>E]))"
              apply (erule_tac x="p1" in allE, auto)
              using TT1_P TT1_def case_assms(1) case_assms2(1) ctt_prefix_concat ctt_prefix_imp_prefix_subset apply fastforce
              apply (metis (no_types, lifting) \<rho>_non_tick_refusal case_assms2(2) contains_refusal.simps(1) contains_refusal.simps(3) intersect_refusal_trace_concat not_contains_refusal_intersect_refusal_trace)
              apply (metis \<rho>_non_tick_refusal case_assms2(2) intersect_refusal_trace.simps(1) intersect_refusal_trace.simps(3) intersect_refusal_trace_concat)
              using case_assms(5) case_assms2(2) case_assms3(1) by blast
          next
            assume "\<not> contains_refusal p1"
            then show "\<forall>p. p \<in> P \<longrightarrow> (\<exists>p'. p = p' @ [[Tick]\<^sub>E]) \<or> (\<exists>p' Y. p = p' @ [[Y]\<^sub>R]) \<or> contains_refusal p \<or>
                (\<forall>q. q \<in> Q \<longrightarrow> (\<exists>q' Y. q = [Y]\<^sub>R # q') \<or> \<rho> @ [[x]\<^sub>E] \<noteq> p @ q) \<Longrightarrow>
              \<exists>p. p @ [[Tick]\<^sub>E] \<in> P \<and> contains_refusal p \<and> (\<exists>X. [[X]\<^sub>R] \<in> Q \<and> \<rho> @ [[x]\<^sub>E] = intersect_refusal_trace X (p @ [[Tick]\<^sub>E]))"
              apply (erule_tac x="p1" in allE, auto)
              using TT1_P TT1_def case_assms(1) case_assms2(1) ctt_prefix_concat ctt_prefix_imp_prefix_subset apply fastforce
              apply (metis (no_types, lifting) \<rho>_non_tick_refusal case_assms2(2) not_contains_refusal_intersect_refusal_trace)
              apply (metis \<rho>_non_tick_refusal case_assms2(2) intersect_refusal_trace.simps(1) intersect_refusal_trace.simps(3) intersect_refusal_trace_concat)
              using case_assms2(2) case_assms3(1) not_contains_refusal_intersect_refusal_trace by blast
          qed
        next
          fix x
          assume case_assms3: "[[x]\<^sub>E] \<in> Q" "x \<noteq> Tock"
          show "\<rho> @ [[x]\<^sub>E] \<in> P \<triangle>\<^sub>U Q"
            unfolding UntimedInterruptTTT_def
          proof (safe, simp_all, cases "contains_refusal p1")
            assume "contains_refusal p1"
            then show "\<forall>p. contains_refusal p \<longrightarrow> p \<in> P \<longrightarrow> (\<exists>p'. p = p' @ [[Tick]\<^sub>E]) \<or> (\<exists>p' Y. p = p' @ [[Y]\<^sub>R]) \<or>
                (\<forall>q. q \<in> Q \<longrightarrow> (\<forall>X. [[X]\<^sub>R] \<in> Q \<longrightarrow> (\<exists>q' Y. q = [Y]\<^sub>R # q') \<or> \<rho> @ [[x]\<^sub>E] \<noteq> intersect_refusal_trace X p @ q)) \<Longrightarrow>
              \<exists>p. p @ [[Tick]\<^sub>E] \<in> P \<and> contains_refusal p \<and> (\<exists>X. [[X]\<^sub>R] \<in> Q \<and> \<rho> @ [[x]\<^sub>E] = intersect_refusal_trace X (p @ [[Tick]\<^sub>E]))"
              apply (erule_tac x="p1" in allE, auto)
              using TT1_P TT1_def case_assms(1) case_assms2(1) ctt_prefix_concat ctt_prefix_imp_prefix_subset apply fastforce
              apply (metis (no_types, lifting) \<rho>_non_tick_refusal case_assms2(2) contains_refusal.simps(1) contains_refusal.simps(3) intersect_refusal_trace_concat not_contains_refusal_intersect_refusal_trace)
              apply (metis \<rho>_non_tick_refusal case_assms2(2) intersect_refusal_trace.simps(1) intersect_refusal_trace.simps(3) intersect_refusal_trace_concat)
              using case_assms(5) case_assms2(2) case_assms3(1) by blast
          next
            assume "\<not> contains_refusal p1"
            then show "\<forall>p. p \<in> P \<longrightarrow> (\<exists>p'. p = p' @ [[Tick]\<^sub>E]) \<or> (\<exists>p' Y. p = p' @ [[Y]\<^sub>R]) \<or> contains_refusal p \<or>
                (\<forall>q. q \<in> Q \<longrightarrow> (\<exists>q' Y. q = [Y]\<^sub>R # q') \<or> \<rho> @ [[x]\<^sub>E] \<noteq> p @ q) \<Longrightarrow>
              \<exists>p. p @ [[Tick]\<^sub>E] \<in> P \<and> contains_refusal p \<and> (\<exists>X. [[X]\<^sub>R] \<in> Q \<and> \<rho> @ [[x]\<^sub>E] = intersect_refusal_trace X (p @ [[Tick]\<^sub>E]))"
              apply (erule_tac x="p1" in allE, auto)
              using TT1_P TT1_def case_assms(1) case_assms2(1) ctt_prefix_concat ctt_prefix_imp_prefix_subset apply fastforce
              apply (metis (no_types, lifting) \<rho>_non_tick_refusal case_assms2(2) not_contains_refusal_intersect_refusal_trace)
              apply (metis \<rho>_non_tick_refusal case_assms2(2) intersect_refusal_trace.simps(1) intersect_refusal_trace.simps(3) intersect_refusal_trace_concat)
              using case_assms2(2) case_assms3(1) not_contains_refusal_intersect_refusal_trace by blast
          qed
        next
          assume case_assms3: "[[Z]\<^sub>R, [Tock]\<^sub>E] \<in> Q"
          show "\<rho> @ [[X]\<^sub>R, [Tock]\<^sub>E] \<notin> P \<triangle>\<^sub>U Q \<Longrightarrow> False"
            unfolding UntimedInterruptTTT_def
          proof (safe, simp_all)
            show "\<forall>p Xa. p @ [[Xa]\<^sub>R] \<in> P \<longrightarrow> (\<forall>Y q. [Y]\<^sub>R # q \<in> Q \<longrightarrow> \<rho> @ [[X]\<^sub>R, [Tock]\<^sub>E] \<noteq> intersect_refusal_trace Y (p @ [[Xa]\<^sub>R]) @ q) \<Longrightarrow>
              \<exists>p. p @ [[Tick]\<^sub>E] \<in> P \<and> contains_refusal p \<and> (\<exists>Xa. [[Xa]\<^sub>R] \<in> Q \<and> \<rho> @ [[X]\<^sub>R, [Tock]\<^sub>E] = intersect_refusal_trace Xa (p @ [[Tick]\<^sub>E]))"
              apply (erule_tac x="p1" in allE, erule_tac x="A" in allE, auto)
              apply (metis TT1_P TT1_def case_assms(1) case_assms2(1) ctt_prefix_subset.simps(1) ctt_prefix_subset.simps(2) ctt_prefix_subset_same_front subset_iff)
              using case_assms3 apply (erule_tac x="Z" in allE, erule_tac x="[[Tock]\<^sub>E]" in allE, auto)
              by (simp add: Int_commute case_assms2(2) case_assms2(4) intersect_refusal_trace_concat)
          qed
        next
          assume case_assms3: "[[Z]\<^sub>R, [Tock]\<^sub>E] \<in> Q"
          show "\<rho> @ [[X]\<^sub>R, [Tock]\<^sub>E] \<notin> P \<triangle>\<^sub>U Q \<Longrightarrow> \<rho> @ [[Tock]\<^sub>E] \<in> P \<triangle>\<^sub>U Q"
            unfolding UntimedInterruptTTT_def
          proof (safe, simp_all)
            show "\<forall>p Xa. p @ [[Xa]\<^sub>R] \<in> P \<longrightarrow> (\<forall>Y q. [Y]\<^sub>R # q \<in> Q \<longrightarrow> \<rho> @ [[X]\<^sub>R, [Tock]\<^sub>E] \<noteq> intersect_refusal_trace Y (p @ [[Xa]\<^sub>R]) @ q) \<Longrightarrow>
              \<exists>p. p @ [[Tick]\<^sub>E] \<in> P \<and> contains_refusal p \<and> (\<exists>X. [[X]\<^sub>R] \<in> Q \<and> \<rho> @ [[Tock]\<^sub>E] = intersect_refusal_trace X (p @ [[Tick]\<^sub>E]))"
              apply (erule_tac x="p1" in allE, erule_tac x="A" in allE, auto)
              apply (metis TT1_P TT1_def case_assms(1) case_assms2(1) ctt_prefix_subset.simps(1) ctt_prefix_subset.simps(2) ctt_prefix_subset_same_front subset_iff)
              using case_assms3 apply (erule_tac x="Z" in allE, erule_tac x="[[Tock]\<^sub>E]" in allE, auto)
              by (simp add: Int_commute case_assms2(2) case_assms2(4) intersect_refusal_trace_concat)
          qed
        qed
        then have "Y \<inter> {e. e \<noteq> Tock \<and> [[e]\<^sub>E] \<in> Q \<or> e = Tock \<and> [[Z]\<^sub>R, [e]\<^sub>E] \<in> Q} = {}"
          using assm2 by auto
        then have 2: "[[Z \<union> Y]\<^sub>R] \<in> Q"
          using case_assms(5) TT2s_Q unfolding TT2s_def apply auto
          by (erule_tac x="[]" in allE, erule_tac x="[]" in allE, auto)

       
        have 3: "(\<forall>p'. p1 @ [X \<union> Y]\<^sub>R # p2 \<noteq> p' @ [[Tick]\<^sub>E]) \<and> (\<forall>p' Y. p1 @ [X \<union> Y]\<^sub>R # p2 \<noteq> p' @ [[Y]\<^sub>R])"
          using case_assms(1) case_assms(2) apply auto
          apply (metis append_butlast_last_id append_is_Nil_conv case_assms2(1) cttobs.simps(4) last.simps last_appendR list.simps(3))
          by (metis append_butlast_last_id append_is_Nil_conv case_assms(3) case_assms2(1) last.simps last_appendR list.distinct(1))

        have 4: "contains_refusal (p1 @ [X \<union> Y]\<^sub>R # p2)"
          by (metis append.assoc append.left_neutral append_Cons ctt_prefix_concat ctt_prefix_imp_prefix_subset not_contains_refusal_ctt_prefix_subset_end_nonref)

        obtain \<rho>1 where \<rho>1_def: "\<rho>1 = intersect_refusal_trace Z p1"
          by auto
        obtain \<rho>2 where \<rho>2_def: "\<rho>2 = intersect_refusal_trace Z p2"
          by auto

        have 5: "\<rho>1 @ [X \<union> Y]\<^sub>R # \<rho>2 \<in> P"
          using TT1_P unfolding TT1_def apply auto
          apply (erule_tac x="\<rho>1 @ [X \<union> Y]\<^sub>R # \<rho>2" in allE, auto, erule_tac x="p1 @ [X \<union> Y]\<^sub>R # p2" in allE, auto)
          by (simp_all add: 1 \<rho>1_def \<rho>2_def ctt_subset_combine ctt_subset_imp_prefix_subset intersect_refusal_trace_subset)
  
        have 6: "contains_refusal (\<rho>1 @ [X \<union> Y]\<^sub>R # \<rho>2)"
          by (meson ctt_prefix_subset.simps(1) ctt_prefix_subset.simps(2) ctt_prefix_subset_same_front inf_le1 not_contains_refusal_ctt_prefix_subset_end_nonref)

        have 7: "(\<forall>p'. \<rho>1 @ [X \<union> Y]\<^sub>R # \<rho>2 \<noteq> p' @ [[Tick]\<^sub>E]) \<and> (\<forall>p' Y1. \<rho>1 @ [X \<union> Y]\<^sub>R # \<rho>2 \<noteq> p' @ [[Y1]\<^sub>R])"
        proof auto
          fix p'
          assume "\<rho>1 @ [X \<union> Y]\<^sub>R # \<rho>2 = p' @ [[Tick]\<^sub>E]"
          then obtain \<rho>2' where "\<rho>2 = \<rho>2' @ [[Tick]\<^sub>E]"
            by (metis append_butlast_last_id cttobs.distinct(1) last.simps last_appendR list.distinct(1))
          then have "\<rho>2' @ [[Tick]\<^sub>E] \<subseteq>\<^sub>C p2"
            by (simp add: \<rho>2_def intersect_refusal_trace_subset, metis intersect_refusal_trace_subset)
          then have "\<exists> p2'. p2 = p2' @ [[Tick]\<^sub>E]"
            apply (induct \<rho>2' p2 rule:ctt_subset.induct, auto, case_tac v, auto)
            by (metis Cons_eq_append_conv ctt_subset_same_length length_0_conv)+
          then show False
            using "3" by auto
        next
          fix p' Y1
          assume "\<rho>1 @ [X \<union> Y]\<^sub>R # \<rho>2 = p' @ [[Y1]\<^sub>R]"
          then obtain \<rho>2' where "\<rho>2 = \<rho>2' @ [[Y1]\<^sub>R]"
            by (metis \<rho>2_def append_butlast_last_id case_assms(3) case_assms2(1) intersect_refusal_trace.elims last.simps last_appendR list.distinct(1))
          then have "\<rho>2' @ [[Y1]\<^sub>R] \<subseteq>\<^sub>C p2"
            by (simp add: \<rho>2_def intersect_refusal_trace_subset, metis intersect_refusal_trace_subset)
          then have "\<exists> p2' X. p2 = p2' @ [[X]\<^sub>R]"
            apply -
            apply (induct \<rho>2' p2 rule:ctt_subset.induct, auto, case_tac v, auto)
            using ctt_subset.elims(2) by fastforce
          then show False
            using case_assms(3) case_assms2(1) by auto
        qed 

        show "intersect_refusal_trace Z p1 @ [A \<inter> Z \<union> Y]\<^sub>R # intersect_refusal_trace Z p2 @ q \<in> P \<triangle>\<^sub>U Q"
          unfolding UntimedInterruptTTT_def apply auto
          apply (rule_tac x="\<rho>1 @ [X \<union> Y]\<^sub>R # \<rho>2" in exI, auto)
          using 5 6 7 apply (blast, blast, blast, blast)
          apply (rule_tac x="q" in exI, rule_tac x="Z \<union> Y" in exI, auto)
          using 2 case_assms(6) case_assms(7) apply (blast, blast, blast)
        proof -
          have "intersect_refusal_trace Z p1 @ [A \<inter> Z]\<^sub>R # intersect_refusal_trace Z p2 = intersect_refusal_trace Z (p1 @ [A]\<^sub>R # p2)"
            by (simp add: Int_commute intersect_refusal_trace_concat)
          then show "intersect_refusal_trace Z p1 @ [A \<inter> Z \<union> Y]\<^sub>R # intersect_refusal_trace Z p2 = intersect_refusal_trace (Z \<union> Y) (\<rho>1 @ [X \<union> Y]\<^sub>R # \<rho>2)"
            using \<rho>1_def \<rho>2_def case_assms2(4) intersect_refusal_trace_refusal_subset_idempotent by blast
        qed
      next
        fix q1
        assume case_assms2: "q = q1 @ [X]\<^sub>R # [Tock]\<^sub>E # \<sigma>'" "\<rho> = intersect_refusal_trace Z p @ q1"

        have "{e. e \<noteq> Tock \<and> q1 @ [[e]\<^sub>E] \<in> Q \<or> e = Tock \<and> q1 @ [[X]\<^sub>R, [e]\<^sub>E] \<in> Q}
          \<subseteq> {e. e \<noteq> Tock \<and> \<rho> @ [[e]\<^sub>E] \<in> P \<triangle>\<^sub>U Q \<or> e = Tock \<and> \<rho> @ [[X]\<^sub>R, [e]\<^sub>E] \<in> P \<triangle>\<^sub>U Q}"
        proof auto
          fix x
          assume case_assms3: "q1 @ [[x]\<^sub>E] \<in> Q" "x \<noteq> Tock"
          show "\<rho> @ [[x]\<^sub>E] \<in> P \<triangle>\<^sub>U Q"
            unfolding UntimedInterruptTTT_def
          proof (safe, simp_all)
            show "\<forall>p. contains_refusal p \<longrightarrow> p \<in> P \<longrightarrow> (\<exists>p'. p = p' @ [[Tick]\<^sub>E]) \<or> (\<exists>p' Y. p = p' @ [[Y]\<^sub>R]) \<or>
                (\<forall>q. q \<in> Q \<longrightarrow> (\<forall>X. [[X]\<^sub>R] \<in> Q \<longrightarrow> (\<exists>q' Y. q = [Y]\<^sub>R # q') \<or> \<rho> @ [[x]\<^sub>E] \<noteq> intersect_refusal_trace X p @ q)) \<Longrightarrow>
              \<exists>p. p @ [[Tick]\<^sub>E] \<in> P \<and> contains_refusal p \<and> (\<exists>X. [[X]\<^sub>R] \<in> Q \<and> \<rho> @ [[x]\<^sub>E] = intersect_refusal_trace X (p @ [[Tick]\<^sub>E]))"
              apply (erule_tac x="p" in allE, auto simp add: case_assms)
              apply (erule_tac x="q1 @ [[x]\<^sub>E]" in allE, auto simp add: case_assms3)
              apply (erule_tac x="Z" in allE, auto simp add: case_assms case_assms2)
              by (metis append_eq_Cons_conv case_assms(7) case_assms2(1))
          qed
        next
          fix x
          assume case_assms3: "q1 @ [[x]\<^sub>E] \<in> Q" "x \<noteq> Tock"
          show "\<rho> @ [[x]\<^sub>E] \<in> P \<triangle>\<^sub>U Q"
            unfolding UntimedInterruptTTT_def
          proof (safe, simp_all)
            show "\<forall>p. contains_refusal p \<longrightarrow> p \<in> P \<longrightarrow> (\<exists>p'. p = p' @ [[Tick]\<^sub>E]) \<or> (\<exists>p' Y. p = p' @ [[Y]\<^sub>R]) \<or>
                (\<forall>q. q \<in> Q \<longrightarrow> (\<forall>X. [[X]\<^sub>R] \<in> Q \<longrightarrow> (\<exists>q' Y. q = [Y]\<^sub>R # q') \<or> \<rho> @ [[x]\<^sub>E] \<noteq> intersect_refusal_trace X p @ q)) \<Longrightarrow>
              \<exists>p. p @ [[Tick]\<^sub>E] \<in> P \<and> contains_refusal p \<and> (\<exists>X. [[X]\<^sub>R] \<in> Q \<and> \<rho> @ [[x]\<^sub>E] = intersect_refusal_trace X (p @ [[Tick]\<^sub>E]))"
              apply (erule_tac x="p" in allE, auto simp add: case_assms)
              apply (erule_tac x="q1 @ [[x]\<^sub>E]" in allE, auto simp add: case_assms3)
              apply (erule_tac x="Z" in allE, auto simp add: case_assms case_assms2)
              by (metis append_eq_Cons_conv case_assms(7) case_assms2(1))
          qed
        next
          assume case_assms3: "q1 @ [[X]\<^sub>R, [Tock]\<^sub>E] \<in> Q" "\<rho> @ [[X]\<^sub>R, [Tock]\<^sub>E] \<notin> P \<triangle>\<^sub>U Q"
          have "\<forall>p. contains_refusal p \<longrightarrow> p \<in> P \<longrightarrow> (\<exists>p'. p = p' @ [[Tick]\<^sub>E]) \<or> (\<exists>p' Y. p = p' @ [[Y]\<^sub>R]) \<or>
            (\<forall>q. q \<in> Q \<longrightarrow> (\<forall>Xa. [[Xa]\<^sub>R] \<in> Q \<longrightarrow> (\<exists>q' Y. q = [Y]\<^sub>R # q') \<or> \<rho> @ [[X]\<^sub>R, [Tock]\<^sub>E] \<noteq> intersect_refusal_trace Xa p @ q))"
            using case_assms3(2) unfolding UntimedInterruptTTT_def by auto
          then show "False"
            apply (erule_tac x="p" in allE, auto simp add: case_assms)
            apply (erule_tac x="q1 @ [[X]\<^sub>R, [Tock]\<^sub>E]" in allE, auto simp add: case_assms3)
            apply (erule_tac x="Z" in allE, auto simp add: case_assms case_assms2)
            by (metis append_eq_Cons_conv case_assms(7) case_assms2(1))
        next
          assume case_assms3: "q1 @ [[X]\<^sub>R, [Tock]\<^sub>E] \<in> Q" "\<rho> @ [[X]\<^sub>R, [Tock]\<^sub>E] \<notin> P \<triangle>\<^sub>U Q"
          have "\<forall>p. contains_refusal p \<longrightarrow> p \<in> P \<longrightarrow> (\<exists>p'. p = p' @ [[Tick]\<^sub>E]) \<or> (\<exists>p' Y. p = p' @ [[Y]\<^sub>R]) \<or>
            (\<forall>q. q \<in> Q \<longrightarrow> (\<forall>Xa. [[Xa]\<^sub>R] \<in> Q \<longrightarrow> (\<exists>q' Y. q = [Y]\<^sub>R # q') \<or> \<rho> @ [[X]\<^sub>R, [Tock]\<^sub>E] \<noteq> intersect_refusal_trace Xa p @ q))"
            using case_assms3(2) unfolding UntimedInterruptTTT_def by auto
          then show "\<rho> @ [[Tock]\<^sub>E] \<in> P \<triangle>\<^sub>U Q"
            apply (erule_tac x="p" in allE, auto simp add: case_assms)
            apply (erule_tac x="q1 @ [[X]\<^sub>R, [Tock]\<^sub>E]" in allE, auto simp add: case_assms3)
            apply (erule_tac x="Z" in allE, auto simp add: case_assms case_assms2)
            by (metis append_eq_Cons_conv case_assms(7) case_assms2(1))
        qed
        then have "Y \<inter> {e. e \<noteq> Tock \<and> q1 @ [[e]\<^sub>E] \<in> Q \<or> e = Tock \<and> q1 @ [[X]\<^sub>R, [e]\<^sub>E] \<in> Q} = {}"
          using assm2 by auto
        then have "q1 @ [X \<union> Y]\<^sub>R # [Tock]\<^sub>E # \<sigma>' \<in> Q"
          using TT2s_Q case_assms case_assms2 unfolding TT2s_def by auto
        then show "intersect_refusal_trace Z p @ q1 @ [X \<union> Y]\<^sub>R # [Tock]\<^sub>E # \<sigma>' \<in> P \<triangle>\<^sub>U Q"
          unfolding UntimedInterruptTTT_def apply auto
          apply (rule_tac x="p" in exI, auto simp add: case_assms case_assms2)
          apply (rule_tac x="q1 @ [X \<union> Y]\<^sub>R # [Tock]\<^sub>E # \<sigma>'" in exI, auto simp add: case_assms case_assms2)
          apply (rule_tac x="Z" in exI, auto simp add: case_assms case_assms2)
          by (metis Cons_eq_append_conv append_Cons case_assms(7) case_assms2(1))
      qed
    next
      fix p q
      assume case_assms: "p \<in> P" "\<forall>p'. p \<noteq> p' @ [[Tick]\<^sub>E]" "\<forall>p' Y. p \<noteq> p' @ [[Y]\<^sub>R]" "\<not> contains_refusal p"
        "q \<in> Q" "\<forall>q' Y. q \<noteq> [Y]\<^sub>R # q'" "\<rho> @ [X]\<^sub>R # [Tock]\<^sub>E # \<sigma>' = p @ q"
      obtain q1 where "q = q1 @ [X]\<^sub>R # [Tock]\<^sub>E # \<sigma>' \<and> \<rho> = p @ q1"
        using case_assms(4) case_assms(7) apply - by (induct \<rho> p rule:ctt_subset.induct, auto)
      also have "{e. e \<noteq> Tock \<and> q1 @ [[e]\<^sub>E] \<in> Q \<or> e = Tock \<and> q1 @ [[X]\<^sub>R, [e]\<^sub>E] \<in> Q}
        \<subseteq> {e. e \<noteq> Tock \<and> \<rho> @ [[e]\<^sub>E] \<in> P \<triangle>\<^sub>U Q \<or> e = Tock \<and> \<rho> @ [[X]\<^sub>R, [e]\<^sub>E] \<in> P \<triangle>\<^sub>U Q}"
      proof auto
        fix x
        assume case_assms2: "q1 @ [[x]\<^sub>E] \<in> Q" "x \<noteq> Tock"
        show "\<rho> @ [[x]\<^sub>E] \<in> P \<triangle>\<^sub>U Q"
          unfolding UntimedInterruptTTT_def
        proof (safe, simp_all)
          show "\<forall>p. p \<in> P \<longrightarrow> (\<exists>p'. p = p' @ [[Tick]\<^sub>E]) \<or> (\<exists>p' Y. p = p' @ [[Y]\<^sub>R]) \<or> contains_refusal p \<or>
              (\<forall>q. q \<in> Q \<longrightarrow> (\<exists>q' Y. q = [Y]\<^sub>R # q') \<or> \<rho> @ [[x]\<^sub>E] \<noteq> p @ q) \<Longrightarrow>
            \<exists>p. p @ [[Tick]\<^sub>E] \<in> P \<and> contains_refusal p \<and> (\<exists>X. [[X]\<^sub>R] \<in> Q \<and> \<rho> @ [[x]\<^sub>E] = intersect_refusal_trace X (p @ [[Tick]\<^sub>E]))"
            apply (erule_tac x="p" in allE, auto simp add: case_assms)
            apply (erule_tac x="q1 @ [[x]\<^sub>E]" in allE, auto simp add: case_assms case_assms2 calculation)
            by (metis append_eq_Cons_conv calculation case_assms(6))
        qed
      next
        fix x
        assume case_assms2: "q1 @ [[x]\<^sub>E] \<in> Q" "x \<noteq> Tock"
        show "\<rho> @ [[x]\<^sub>E] \<in> P \<triangle>\<^sub>U Q"
          unfolding UntimedInterruptTTT_def
        proof (safe, simp_all)
          show "\<forall>p. p \<in> P \<longrightarrow> (\<exists>p'. p = p' @ [[Tick]\<^sub>E]) \<or> (\<exists>p' Y. p = p' @ [[Y]\<^sub>R]) \<or> contains_refusal p \<or>
              (\<forall>q. q \<in> Q \<longrightarrow> (\<exists>q' Y. q = [Y]\<^sub>R # q') \<or> \<rho> @ [[x]\<^sub>E] \<noteq> p @ q) \<Longrightarrow>
            \<exists>p. p @ [[Tick]\<^sub>E] \<in> P \<and> contains_refusal p \<and> (\<exists>X. [[X]\<^sub>R] \<in> Q \<and> \<rho> @ [[x]\<^sub>E] = intersect_refusal_trace X (p @ [[Tick]\<^sub>E]))"
            apply (erule_tac x="p" in allE, auto simp add: case_assms)
            apply (erule_tac x="q1 @ [[x]\<^sub>E]" in allE, auto simp add: case_assms case_assms2 calculation)
            by (metis append_eq_Cons_conv calculation case_assms(6))
        qed
      next
        assume case_assms2: "q1 @ [[X]\<^sub>R, [Tock]\<^sub>E] \<in> Q" "\<rho> @ [[X]\<^sub>R, [Tock]\<^sub>E] \<notin> P \<triangle>\<^sub>U Q"
        have "\<forall>p. p \<in> P \<longrightarrow> (\<exists>p'. p = p' @ [[Tick]\<^sub>E]) \<or> (\<exists>p' Y. p = p' @ [[Y]\<^sub>R]) \<or> contains_refusal p \<or>
          (\<forall>q. q \<in> Q \<longrightarrow> (\<exists>q' Y. q = [Y]\<^sub>R # q') \<or> \<rho> @ [[X]\<^sub>R, [Tock]\<^sub>E] \<noteq> p @ q)"
          using case_assms2(2) unfolding UntimedInterruptTTT_def by auto
        then show "False"
            apply (erule_tac x="p" in allE, auto simp add: case_assms)
            apply (erule_tac x="q1 @ [[X]\<^sub>R, [Tock]\<^sub>E]" in allE, auto simp add: case_assms case_assms2 calculation)
          by (metis append_eq_Cons_conv calculation case_assms(6))
      next
        assume case_assms2: "q1 @ [[X]\<^sub>R, [Tock]\<^sub>E] \<in> Q" "\<rho> @ [[X]\<^sub>R, [Tock]\<^sub>E] \<notin> P \<triangle>\<^sub>U Q"
        have "\<forall>p. p \<in> P \<longrightarrow> (\<exists>p'. p = p' @ [[Tick]\<^sub>E]) \<or> (\<exists>p' Y. p = p' @ [[Y]\<^sub>R]) \<or> contains_refusal p \<or>
          (\<forall>q. q \<in> Q \<longrightarrow> (\<exists>q' Y. q = [Y]\<^sub>R # q') \<or> \<rho> @ [[X]\<^sub>R, [Tock]\<^sub>E] \<noteq> p @ q)"
          using case_assms2(2) unfolding UntimedInterruptTTT_def by auto
        then show "\<rho> @ [[Tock]\<^sub>E] \<in> P \<triangle>\<^sub>U Q"
            apply (erule_tac x="p" in allE, auto simp add: case_assms)
            apply (erule_tac x="q1 @ [[X]\<^sub>R, [Tock]\<^sub>E]" in allE, auto simp add: case_assms case_assms2 calculation)
          by (metis append_eq_Cons_conv calculation case_assms(6))
      qed
      then have "Y \<inter> {e. e \<noteq> Tock \<and> q1 @ [[e]\<^sub>E] \<in> Q \<or> e = Tock \<and> q1 @ [[X]\<^sub>R, [e]\<^sub>E] \<in> Q} = {}"
        using assm2 by auto
      then have "q1 @ [X \<union> Y]\<^sub>R # [Tock]\<^sub>E # \<sigma>' \<in> Q"
        using TT2s_Q case_assms calculation unfolding TT2s_def by auto
      then show "\<rho> @ [X \<union> Y]\<^sub>R # [Tock]\<^sub>E # \<sigma>' \<in> P \<triangle>\<^sub>U Q"
        unfolding UntimedInterruptTTT_def
      proof auto
        show "q1 @ [X \<union> Y]\<^sub>R # [Tock]\<^sub>E # \<sigma>' \<in> Q \<Longrightarrow>
          \<forall>p. p \<in> P \<longrightarrow> (\<exists>p'. p = p' @ [[Tick]\<^sub>E]) \<or> (\<exists>p' Y. p = p' @ [[Y]\<^sub>R]) \<or> contains_refusal p \<or>
            (\<forall>q. q \<in> Q \<longrightarrow> (\<exists>q' Y. q = [Y]\<^sub>R # q') \<or> \<rho> @ [X \<union> Y]\<^sub>R # [Tock]\<^sub>E # \<sigma>' \<noteq> p @ q) \<Longrightarrow>
          \<exists>p. p \<in> P \<and> (\<forall>p'. p \<noteq> p' @ [[Tick]\<^sub>E]) \<and> (\<forall>p' Y. p \<noteq> p' @ [[Y]\<^sub>R]) \<and> contains_refusal p \<and>
            (\<exists>q Xa. [[Xa]\<^sub>R] \<in> Q \<and> q \<in> Q \<and> (\<forall>q' Y. q \<noteq> [Y]\<^sub>R # q') \<and> \<rho> @ [X \<union> Y]\<^sub>R # [Tock]\<^sub>E # \<sigma>' = intersect_refusal_trace Xa p @ q)"
          apply (erule_tac x="p" in allE, auto simp add: case_assms)
          apply (erule_tac x="q1 @ [X \<union> Y]\<^sub>R # [Tock]\<^sub>E # \<sigma>'" in allE, auto simp add: case_assms calculation)
          by (metis append_eq_Cons_conv calculation case_assms(6))
      qed
    qed
  qed
qed

lemma TT3_trace_intersect_refusal_trace:
  "TT3_trace t \<Longrightarrow> TT3_trace (intersect_refusal_trace X t)"
  by (induct t rule:TT3_trace.induct, auto, case_tac x, auto, case_tac vb, auto)

lemma TT3_UntimedInterrupt:
  assumes Q_wf: "\<forall>q\<in>Q. ttWF q"
  assumes TT1_P: "TT1 P" and TT1_Q: "TT1 Q"
  assumes TT3_P: "TT3 P" and TT3_Q: "TT3 Q"
  shows "TT3 (P \<triangle>\<^sub>U Q)"
  unfolding UntimedInterruptTTT_def TT3_def 
proof auto
  fix p X
  show "p @ [[Tick]\<^sub>E] \<in> P \<Longrightarrow> TT3_trace (intersect_refusal_trace X (p @ [[Tick]\<^sub>E]))"
    using TT3_def TT3_trace_intersect_refusal_trace TT3_P by auto
next
  fix p X
  show "p @ [[Tick]\<^sub>E] \<in> P \<Longrightarrow> TT3_trace (p @ [[Tick]\<^sub>E])"
    by (metis TT3_def TT3_P)
next
  fix p q X Y
  assume case_assms: "[Y]\<^sub>R # q \<in> Q" "p @ [[X]\<^sub>R] \<in> P"
  have "intersect_refusal_trace Y (p @ [[X]\<^sub>R]) @ q = intersect_refusal_trace Y p @ intersect_refusal_trace Y [[X]\<^sub>R] @ q"
    by (induct p rule:intersect_refusal_trace.induct, auto)
  then have 1: "intersect_refusal_trace Y (p @ [[X]\<^sub>R]) @ q = intersect_refusal_trace Y p @ [X \<inter> Y]\<^sub>R # q"
    by auto
  then have "[X \<inter> Y]\<^sub>R # q \<in> Q"
    by (metis TT1_Q TT1_def Int_commute Int_left_absorb case_assms(1) ctt_prefix_subset.simps(2) ctt_prefix_subset_refl inf.absorb_iff2)
  then have 2: "ttWF ([X \<inter> Y]\<^sub>R # q) \<and> TT3_trace ([X \<inter> Y]\<^sub>R # q)"
    using TT3_Q TT3_def Q_wf by blast
  have 3: "TT3_trace p"
    by (meson TT3_P TT3_def TT3_trace_cons_left case_assms(2))
  show "TT3_trace (intersect_refusal_trace Y (p @ [[X]\<^sub>R]) @ q)"
    by (simp add: "1" "2" "3" TT3_append TT3_trace_intersect_refusal_trace)
next
  fix p q X
  show "p \<in> P \<Longrightarrow> q \<in> Q \<Longrightarrow> TT3_trace (intersect_refusal_trace X p @ q)"
    by (meson TT3_P TT3_Q TT3_append TT3_def TT3_trace_intersect_refusal_trace Q_wf)
next
  fix p q
  show "p \<in> P \<Longrightarrow> q \<in> Q \<Longrightarrow> TT3_trace (p @ q)"
    by (meson TT3_P TT3_Q TT3_append TT3_def TT3_trace_intersect_refusal_trace Q_wf)
qed

lemma add_Tick_refusal_trace_intersect_refusal_trace:
  "add_Tick_refusal_trace (intersect_refusal_trace X p) = intersect_refusal_trace (X \<union> {Tick}) (add_Tick_refusal_trace p)"
  by (induct p rule:add_Tick_refusal_trace.induct, auto)

lemma contains_refusal_add_Tick_refusal_trace:
  "contains_refusal (add_Tick_refusal_trace t) = contains_refusal t"
  by (induct t rule:add_Tick_refusal_trace.induct, auto)

lemma add_Tick_refusal_trace_not_end_tick:
  "\<nexists> s. t = s  @ [[Tick]\<^sub>E] \<Longrightarrow> \<nexists> s. add_Tick_refusal_trace t = s  @ [[Tick]\<^sub>E]"
  apply (auto, induct t rule:add_Tick_refusal_trace.induct, auto)
  apply (metis (no_types, hide_lams) add_Tick_refusal_trace.simps(2) append_Cons append_butlast_last_id contains_refusal.elims(3) contains_refusal.simps(1) contains_refusal_add_Tick_refusal_trace last.simps last_appendR list.distinct(1))
  by (metis append.left_neutral append_Cons append_butlast_last_id cttobs.distinct(1) last_snoc)

lemma add_Tick_refusal_trace_not_end_refusal:
  "\<nexists> s X. t = s  @ [[X]\<^sub>R] \<Longrightarrow> \<nexists> s X. add_Tick_refusal_trace t = s  @ [[X]\<^sub>R]"
  apply (auto, induct t rule:add_Tick_refusal_trace.induct, auto)
  apply (metis (no_types, hide_lams) add_Tick_refusal_trace.simps(2) append_Cons append_butlast_last_id contains_refusal.elims(3) contains_refusal.simps(1) contains_refusal_add_Tick_refusal_trace last.simps last_appendR list.distinct(1))
  by (case_tac s, auto, case_tac t rule:add_Tick_refusal_trace.cases, auto, fastforce)
  
lemma TT4s_UntimedInterrupt:
  assumes TT4s_P: "TT4s P" and TT4s_Q: "TT4s Q"
  shows "TT4s (P \<triangle>\<^sub>U Q)"
  unfolding TT4s_def UntimedInterruptTTT_def
proof (safe, simp_all)
  fix p X
  assume case_assms: "p @ [[Tick]\<^sub>E] \<in> P" "contains_refusal p" "[[X]\<^sub>R] \<in> Q"
  have 1: "add_Tick_refusal_trace p @ [[Tick]\<^sub>E] \<in> P"
    by (metis TT4s_P TT4s_def add_Tick_refusal_trace_end_event case_assms(1))
  have 2: "[[X \<union> {Tick}]\<^sub>R] \<in> Q"
    using TT4s_Q TT4s_def case_assms(3) by fastforce
  show "\<exists>pa. pa @ [[Tick]\<^sub>E] \<in> P \<and> contains_refusal pa \<and> (\<exists>Xa. [[Xa]\<^sub>R] \<in> Q \<and>
    add_Tick_refusal_trace (intersect_refusal_trace X (p @ [[Tick]\<^sub>E])) = intersect_refusal_trace Xa (pa @ [[Tick]\<^sub>E]))"
    using 1 2 contains_refusal_add_Tick_refusal_trace case_assms
    apply (rule_tac x="add_Tick_refusal_trace p" in exI, auto, rule_tac x="X \<union> {Tick}" in exI, auto)
    by (simp add: add_Tick_refusal_trace_end_event add_Tick_refusal_trace_intersect_refusal_trace)
next
  fix p
  assume case_assms: "p @ [[Tick]\<^sub>E] \<in> P" "\<not> contains_refusal p"
  have "add_Tick_refusal_trace p @ [[Tick]\<^sub>E] \<in> P"
    by (metis TT4s_P TT4s_def add_Tick_refusal_trace_end_event case_assms(1))
  then show "\<forall>pa. pa @ [[Tick]\<^sub>E] \<in> P \<longrightarrow> contains_refusal pa \<or> add_Tick_refusal_trace (p @ [[Tick]\<^sub>E]) \<noteq> pa @ [[Tick]\<^sub>E] \<Longrightarrow>
    \<exists>pa. pa @ [[Tick]\<^sub>E] \<in> P \<and> contains_refusal pa \<and>
      (\<exists>X. [[X]\<^sub>R] \<in> Q \<and> add_Tick_refusal_trace (p @ [[Tick]\<^sub>E]) = intersect_refusal_trace X (pa @ [[Tick]\<^sub>E]))"
    by (erule_tac x="add_Tick_refusal_trace p" in allE, metis add_Tick_refusal_trace_end_event case_assms(2) contains_refusal_add_Tick_refusal_trace)
next
  fix p X Y q
  assume case_assms: "p @ [[X]\<^sub>R] \<in> P" "[Y]\<^sub>R # q \<in> Q"
  have 1: "add_Tick_refusal_trace p @ [[X \<union> {Tick}]\<^sub>R] \<in> P"
    by (metis TT4s_P TT4s_def add_Tick_refusal_trace_end_refusal case_assms(1))
  have 2: "[Y \<union> {Tick}]\<^sub>R # add_Tick_refusal_trace q \<in> Q"
    using TT4s_Q TT4s_def case_assms(2) by fastforce
  show "\<forall>pa Xa. pa @ [[Xa]\<^sub>R] \<in> P \<longrightarrow> (\<forall>Ya qa. [Ya]\<^sub>R # qa \<in> Q \<longrightarrow>
      add_Tick_refusal_trace (intersect_refusal_trace Y (p @ [[X]\<^sub>R]) @ q) \<noteq> intersect_refusal_trace Ya (pa @ [[Xa]\<^sub>R]) @ qa) \<Longrightarrow>
    \<exists>pa. pa @ [[Tick]\<^sub>E] \<in> P \<and> contains_refusal pa \<and> (\<exists>Xa. [[Xa]\<^sub>R] \<in> Q \<and>
      add_Tick_refusal_trace (intersect_refusal_trace Y (p @ [[X]\<^sub>R]) @ q) = intersect_refusal_trace Xa (pa @ [[Tick]\<^sub>E]))"
    using 1 2 apply (erule_tac x="add_Tick_refusal_trace p" in allE, erule_tac x="X \<union> {Tick}" in allE, auto)
    apply (erule_tac x="Y \<union> {Tick}" in allE, erule_tac x="add_Tick_refusal_trace q" in allE, auto)
    by (simp add: add_Tick_refusal_trace_concat add_Tick_refusal_trace_intersect_refusal_trace)
next
  fix p q X
  assume case_assms: "p \<in> P" "\<forall>p'. p \<noteq> p' @ [[Tick]\<^sub>E]" "\<forall>p' Y. p \<noteq> p' @ [[Y]\<^sub>R]" "contains_refusal p"
    "[[X]\<^sub>R] \<in> Q" "q \<in> Q" "\<forall>q' Y. q \<noteq> [Y]\<^sub>R # q'"
  have 1: "add_Tick_refusal_trace p \<in> P"
    using TT4s_P TT4s_def case_assms(1) by blast
  have 2: "(\<forall>p'. add_Tick_refusal_trace p \<noteq> p' @ [[Tick]\<^sub>E]) \<and> (\<forall>p' Y. add_Tick_refusal_trace p \<noteq> p' @ [[Y]\<^sub>R])"
    using add_Tick_refusal_trace_not_end_refusal add_Tick_refusal_trace_not_end_tick case_assms by blast
  have 3: "contains_refusal (add_Tick_refusal_trace p)"
    by (simp add: case_assms(4) contains_refusal_add_Tick_refusal_trace)
  have 4: "[[X \<union> {Tick}]\<^sub>R] \<in> Q"
    using TT4s_Q TT4s_def case_assms(5) by force
  have 5: "add_Tick_refusal_trace q \<in> Q"
    using TT4s_Q TT4s_def case_assms(6) by blast
  have 6: "\<forall>q' Y. add_Tick_refusal_trace q \<noteq> [Y]\<^sub>R # q'"
    using add_Tick_refusal_trace.elims case_assms(7) by blast
  show "\<forall>pa. contains_refusal pa \<longrightarrow> pa \<in> P \<longrightarrow> (\<exists>p'. pa = p' @ [[Tick]\<^sub>E]) \<or> (\<exists>p' Y. pa = p' @ [[Y]\<^sub>R]) \<or>
      (\<forall>qa. qa \<in> Q \<longrightarrow> (\<forall>Xa. [[Xa]\<^sub>R] \<in> Q \<longrightarrow> (\<exists>q' Y. qa = [Y]\<^sub>R # q') \<or>
        add_Tick_refusal_trace (intersect_refusal_trace X p @ q) \<noteq> intersect_refusal_trace Xa pa @ qa)) \<Longrightarrow>
    \<exists>pa. pa @ [[Tick]\<^sub>E] \<in> P \<and> contains_refusal pa \<and> (\<exists>Xa. [[Xa]\<^sub>R] \<in> Q \<and>
      add_Tick_refusal_trace (intersect_refusal_trace X p @ q) = intersect_refusal_trace Xa (pa @ [[Tick]\<^sub>E]))"
    using 1 2 3 4 5 6 apply (erule_tac x="add_Tick_refusal_trace p" in allE, auto)
    apply (erule_tac x="add_Tick_refusal_trace q" in allE, auto, erule_tac x="X \<union> {Tick}" in allE, auto)
    by (simp add: add_Tick_refusal_trace_concat add_Tick_refusal_trace_intersect_refusal_trace)
next
  fix p q
  assume case_assms: "p \<in> P" "\<forall>p'. p \<noteq> p' @ [[Tick]\<^sub>E]" "\<forall>p' Y. p \<noteq> p' @ [[Y]\<^sub>R]" "\<not> contains_refusal p" "q \<in> Q" "\<forall>q' Y. q \<noteq> [Y]\<^sub>R # q'"
  have 1: "add_Tick_refusal_trace p \<in> P"
    using TT4s_P TT4s_def case_assms(1) by blast
  have 2: "(\<forall>p'. add_Tick_refusal_trace p \<noteq> p' @ [[Tick]\<^sub>E]) \<and> (\<forall>p' Y. add_Tick_refusal_trace p \<noteq> p' @ [[Y]\<^sub>R])"
    using add_Tick_refusal_trace_not_end_refusal add_Tick_refusal_trace_not_end_tick case_assms by blast
  have 3: "\<not> contains_refusal (add_Tick_refusal_trace p)"
    by (simp add: case_assms(4) contains_refusal_add_Tick_refusal_trace)
  have 4: "add_Tick_refusal_trace q \<in> Q"
    using TT4s_Q TT4s_def case_assms(5) by blast
  have 5: "\<forall>q' Y. add_Tick_refusal_trace q \<noteq> [Y]\<^sub>R # q'"
    using add_Tick_refusal_trace.elims case_assms(6) by blast
  show "\<forall>pa. pa \<in> P \<longrightarrow> (\<exists>p'. pa = p' @ [[Tick]\<^sub>E]) \<or> (\<exists>p' Y. pa = p' @ [[Y]\<^sub>R]) \<or> contains_refusal pa \<or>
      (\<forall>qa. qa \<in> Q \<longrightarrow> (\<exists>q' Y. qa = [Y]\<^sub>R # q') \<or> add_Tick_refusal_trace (p @ q) \<noteq> pa @ qa) \<Longrightarrow>
    \<exists>pa. pa @ [[Tick]\<^sub>E] \<in> P \<and> contains_refusal pa \<and>
      (\<exists>X. [[X]\<^sub>R] \<in> Q \<and> add_Tick_refusal_trace (p @ q) = intersect_refusal_trace X (pa @ [[Tick]\<^sub>E]))"
    using 1 2 3 4 5 apply (erule_tac x="add_Tick_refusal_trace p" in allE, auto)
    by (erule_tac x="add_Tick_refusal_trace q" in allE, auto simp add: add_Tick_refusal_trace_concat)
qed

lemma TT_UntimedInterrupt:
  assumes "TT P" "TT Q"
  shows "TT (P \<triangle>\<^sub>U Q)"
  using assms unfolding TT_def apply auto
  using UntimedInterruptTTT_wf apply blast
  using TT0_UntimedInterrupt apply blast
  using TT1_UntimedInterrupt apply blast
  using TT2_UntimedInterrupt apply blast
  using TT3_UntimedInterrupt apply blast
  done

subsection {* Time-synchronising Interrupt *}

fun filter_tocks :: "'e cttobs list \<Rightarrow> 'e cttobs list" where
  "filter_tocks ([X]\<^sub>R # [Tock]\<^sub>E # t) = [X]\<^sub>R # [Tock]\<^sub>E # filter_tocks t" |
  "filter_tocks [] = []" |
  "filter_tocks (x # t) = filter_tocks t"

thm filter_tocks.simps
thm filter_tocks.induct

lemma filter_tocks_in_tocks:
  "filter_tocks t \<in> tocks UNIV"
  by (induct t rule:filter_tocks.induct, auto simp add: tocks.intros)

lemma filter_tocks_end_event:
  "filter_tocks (s @ [[Event e]\<^sub>E]) = filter_tocks s"
  by (induct_tac s rule:filter_tocks.induct, auto)

lemma filter_tocks_end_tick:
  "filter_tocks (s @ [[Tick]\<^sub>E]) = filter_tocks s"
  by (induct_tac s rule:filter_tocks.induct, auto)

lemma filter_tocks_end_ref_tock:
  "filter_tocks (s @ [[X]\<^sub>R, [Tock]\<^sub>E]) = filter_tocks s @ [[X]\<^sub>R, [Tock]\<^sub>E]"
  by (induct_tac s rule:filter_tocks.induct, auto)

lemma ctt_prefix_subset_filter_tocks:
  "ttWF s \<Longrightarrow> ttWF t \<Longrightarrow> s \<lesssim>\<^sub>C t \<Longrightarrow> filter_tocks s \<lesssim>\<^sub>C filter_tocks t"
  by (induct s t rule:ttWF2.induct, auto)

lemma ctt_subset_filter_tocks:
  "ttWF s \<Longrightarrow> ttWF t \<Longrightarrow> s \<subseteq>\<^sub>C t \<Longrightarrow> filter_tocks s \<subseteq>\<^sub>C filter_tocks t"
  by (induct s t rule:ttWF2.induct, auto)

definition TimeSyncInterruptTTT :: "'e cttobs list set \<Rightarrow> 'e cttobs list set \<Rightarrow> 'e cttobs list set" (infixl "\<triangle>\<^sub>T" 58) where
  "P \<triangle>\<^sub>T Q = {t. \<exists> p q. p @ [[Tick]\<^sub>E] \<in> P \<and> q \<in> Q \<and> filter_tocks p = q \<and> t = p @ [[Tick]\<^sub>E]}
    \<union> {t. \<exists> p X Y Z q. p @ [[X]\<^sub>R] \<in> P \<and> filter_tocks p = q \<and> q @ [[Y]\<^sub>R] \<in> Q
      \<and> Z \<subseteq> X \<union> Y \<and> {e\<in>X. e \<noteq> Tock} = {e\<in>Y. e \<noteq> Tock} \<and> t = p @ [[Z]\<^sub>R]}
    \<union> {t. \<exists> p q1 q2. p \<in> P \<and> (\<nexists> p'. p = p' @ [[Tick]\<^sub>E]) \<and> (\<nexists> p' Y. p = p' @ [[Y]\<^sub>R])
      \<and> filter_tocks p = q1 \<and> q1 @ q2 \<in> Q \<and> (\<nexists> q' Y. q2 = [Y]\<^sub>R # q') \<and> t =  p @ q2}"

lemma TimeSyncInterruptTTT_wf:
  assumes "\<forall>x\<in>P. ttWF x" "\<forall>x\<in>Q. ttWF x"
  shows "\<forall>x\<in>(P \<triangle>\<^sub>T Q). ttWF x"
  unfolding TimeSyncInterruptTTT_def
proof (safe, simp_all)
  fix p
  show "p @ [[Tick]\<^sub>E] \<in> P \<Longrightarrow> ttWF (p @ [[Tick]\<^sub>E])"
    using assms by auto
next
  fix p X Y Z
  show "p @ [[X]\<^sub>R] \<in> P \<Longrightarrow> ttWF (p @ [[Z]\<^sub>R])"
    using assms(1) end_refusal_start_refusal_append_wf by fastforce
next
  fix p q2
  assume "filter_tocks p @ q2 \<in> Q"
  then have "ttWF q2"
    using assms(2) filter_tocks_in_tocks tocks_append_wf2 by blast
  then show "p \<in> P \<Longrightarrow> \<forall>p'. p \<noteq> p' @ [[Tick]\<^sub>E] \<Longrightarrow> \<forall>p' Y. p \<noteq> p' @ [[Y]\<^sub>R] \<Longrightarrow> ttWF (p @ q2)"
    using assms(1) nontick_event_end_append_wf by blast
qed

lemma TT0_TimeSyncInterrupt:
  assumes "TT0 P" "TT0 Q" "TT1 P" "TT1 Q"
  shows "TT0 (P \<triangle>\<^sub>T Q)"
  unfolding TimeSyncInterruptTTT_def TT0_def
proof auto
  have "[] \<in> P \<and> [] \<in> Q"
    by (simp add: TT0_TT1_empty assms)
  then show "\<forall>x p. p \<in> P \<longrightarrow> (\<exists>p'. p = p' @ [[Tick]\<^sub>E]) \<or>
      (\<exists>p' Y. p = p' @ [[Y]\<^sub>R]) \<or> (\<forall>q2. filter_tocks p @ q2 \<in> Q \<longrightarrow> (\<exists>q' Y. q2 = [Y]\<^sub>R # q') \<or> x \<noteq> p @ q2) \<Longrightarrow>
    \<exists>x p. (\<exists>X. p @ [[X]\<^sub>R] \<in> P \<and> (\<exists>Y. {e \<in> X. e \<noteq> Tock} = {e \<in> Y. e \<noteq> Tock} \<and> filter_tocks p @ [[Y]\<^sub>R] \<in> Q \<and> (\<exists>Z\<subseteq>X \<union> Y. x = p @ [[Z]\<^sub>R])))"
    by (erule_tac x="[]" in allE, erule_tac x="[]" in allE, auto simp add: tocks.intros)
qed

lemma TT1_TimeSyncInterrupt:
  assumes "\<forall>x\<in>P. ttWF x" "\<forall>x\<in>Q. ttWF x"
  assumes "TT1 P" "TT1 Q"
  shows "TT1 (P \<triangle>\<^sub>T Q)"
  unfolding TT1_def
proof (auto)
  fix \<rho> \<sigma> :: "'a cttobs list"
  assume assm1: "\<rho> \<lesssim>\<^sub>C \<sigma>"
  assume assm2: "\<sigma> \<in> P \<triangle>\<^sub>T Q"
  then have "(\<exists>p q. p @ [[Tick]\<^sub>E] \<in> P \<and> q \<in> Q \<and> filter_tocks p = q \<and> \<sigma> = p @ [[Tick]\<^sub>E])
    \<or> (\<exists>p X Y Z q. p @ [[X]\<^sub>R] \<in> P \<and>  filter_tocks p = q \<and> q @ [[Y]\<^sub>R] \<in> Q
      \<and> Z \<subseteq> X \<union> Y \<and> {e \<in> X. e \<noteq> Tock} = {e \<in> Y. e \<noteq> Tock} \<and> \<sigma> = p @ [[Z]\<^sub>R])
    \<or> (\<exists>p q1 q2. p \<in> P \<and> (\<nexists>p'. p = p' @ [[Tick]\<^sub>E]) \<and> (\<nexists>p' Y. p = p' @ [[Y]\<^sub>R])
      \<and> filter_tocks p = q1 \<and> q1 @ q2 \<in> Q \<and> (\<nexists>q' Y. q2 = [Y]\<^sub>R # q') \<and> \<sigma> = p @ q2)"
    unfolding TimeSyncInterruptTTT_def by auto
  then show "\<rho> \<in> P \<triangle>\<^sub>T Q"
  proof (safe, simp_all)
    fix p
    assume case_assms: "p @ [[Tick]\<^sub>E] \<in> P" "filter_tocks p \<in> Q" "\<sigma> = p @ [[Tick]\<^sub>E]"
    then have \<rho>_in_P: "\<rho> \<in> P"
      using TT1_def assm1 assms(3) by blast
    have 1: "filter_tocks \<rho> \<lesssim>\<^sub>C filter_tocks \<sigma>"
      using \<rho>_in_P assm1 assms(1) case_assms(1) case_assms(3) ctt_prefix_subset_filter_tocks by blast
    have 2: "filter_tocks \<sigma> = filter_tocks p"
      by (simp add: case_assms, induct p rule:filter_tocks.induct, auto)
    have filter_tocks_\<rho>_in_Q: "filter_tocks \<rho> \<in> Q"
      using 1 2 TT1_def assms(4) case_assms(2) by auto
    have \<rho>_cases: "(\<exists> p' X. \<rho> = p' @ [[Tick]\<^sub>E]) \<or> (\<exists> p' X. \<rho> = p' @ [[X]\<^sub>R]) \<or> ((\<nexists>p'. \<rho> = p' @ [[Tick]\<^sub>E]) \<and> (\<nexists>p' Y. \<rho> = p' @ [[Y]\<^sub>R]))"
      by auto
    then show "\<rho> \<in> P \<triangle>\<^sub>T Q"
      unfolding TimeSyncInterruptTTT_def
    proof auto
      fix p'
      show "\<rho> = p' @ [[Tick]\<^sub>E] \<Longrightarrow> p' @ [[Tick]\<^sub>E] \<notin> P \<Longrightarrow> False"
        using \<rho>_in_P by blast
    next
      fix p'
      assume case_assm2: "\<rho> = p' @ [[Tick]\<^sub>E]"
      have "filter_tocks \<rho> = filter_tocks p'"
        by (simp add: case_assm2, induct p' rule:filter_tocks.induct, auto)
      then show "filter_tocks p' \<notin> Q \<Longrightarrow> False"
        using filter_tocks_\<rho>_in_Q by auto
    next
      fix p' X
      have ttWF_\<sigma>: "ttWF (p @ [[Tick]\<^sub>E])"
        by (simp add: assms(1) case_assms(1))
      assume "\<rho> = p' @ [[X]\<^sub>R]"
      then have "p' @ [[X]\<^sub>R] \<lesssim>\<^sub>C p @ [[Tick]\<^sub>E]"
        using case_assms assm1 by auto
      then have "p' @ [[X]\<^sub>R, [Tock]\<^sub>E] \<lesssim>\<^sub>C p @ [[Tick]\<^sub>E]"
        using ttWF_\<sigma> apply - 
        apply (induct p' p rule:ttWF2.induct, auto)
        using ttWF.simps(12) ctt_prefix_subset_ttWF apply blast
        apply (meson ttWF.simps(11) ctt_prefix_subset_ttWF)
        using ttWF.simps(13) ctt_prefix_subset_ttWF apply blast
        using ttWF.simps(8) ctt_prefix_subset_ttWF apply blast
        using ttWF.simps(6) ctt_prefix_subset_ttWF by blast
      then have 1: "filter_tocks (p' @ [[X]\<^sub>R, [Tock]\<^sub>E]) \<lesssim>\<^sub>C filter_tocks (p @ [[Tick]\<^sub>E])"
        using ttWF_\<sigma> ctt_prefix_subset_ttWF ctt_prefix_subset_filter_tocks by blast
      have 2: "filter_tocks (p @ [[Tick]\<^sub>E]) = filter_tocks (p)"
        by (induct p rule:filter_tocks.induct, auto)
      have 3: "filter_tocks (p' @ [[X]\<^sub>R, [Tock]\<^sub>E]) = filter_tocks p' @ [[X]\<^sub>R, [Tock]\<^sub>E]"
        by (induct p' rule:filter_tocks.induct, auto)
      have 4: "filter_tocks p' @ [[X]\<^sub>R, [Tock]\<^sub>E]  \<lesssim>\<^sub>C filter_tocks p"
        using 1 2 3 by auto
      have 5: "filter_tocks p' @ [[X]\<^sub>R]  \<lesssim>\<^sub>C filter_tocks p' @ [[X]\<^sub>R, [Tock]\<^sub>E]"
        by (induct p' rule:filter_tocks.induct, auto)
      then have "filter_tocks p' @ [[X]\<^sub>R]  \<lesssim>\<^sub>C filter_tocks p"
        using 4 ctt_prefix_subset_trans by blast
      then have "filter_tocks p' @ [[X]\<^sub>R] \<in> Q"
        using TT1_def assms(4) case_assms(2) by blast
      then show "\<rho> = p' @ [[X]\<^sub>R] \<Longrightarrow>
        \<exists>p Xa. p @ [[Xa]\<^sub>R] \<in> P \<and>
          (\<exists>Y. filter_tocks p @ [[Y]\<^sub>R] \<in> Q \<and> X \<subseteq> Xa \<union> Y \<and> {e \<in> Xa. e \<noteq> Tock} = {e \<in> Y. e \<noteq> Tock} \<and> p' = p)"
        using \<rho>_in_P filter_tocks_in_tocks by (rule_tac x="p'" in exI, rule_tac x="X" in exI, auto)
    next
      show "\<forall>p. p \<in> P \<longrightarrow>
          (\<exists>p'. p = p' @ [[Tick]\<^sub>E]) \<or> (\<exists>p' Y. p = p' @ [[Y]\<^sub>R]) \<or> (\<forall>q2. filter_tocks p @ q2 \<in> Q \<longrightarrow> (\<exists>q' Y. q2 = [Y]\<^sub>R # q') \<or> \<rho> \<noteq> p @ q2) \<Longrightarrow>
        \<forall>p'. \<rho> \<noteq> p' @ [[Tick]\<^sub>E] \<Longrightarrow> \<forall>p' Y. \<rho> \<noteq> p' @ [[Y]\<^sub>R] \<Longrightarrow> False"
        using \<rho>_in_P filter_tocks_in_tocks
      proof (erule_tac x="\<rho>" in allE, auto)
        show "\<forall>q2. filter_tocks \<rho> @ q2 \<in> Q \<longrightarrow> (\<exists>q' Y. q2 = [Y]\<^sub>R # q') \<or> q2 \<noteq> [] \<Longrightarrow> False"
          by (erule_tac x="[]" in allE, auto simp add: filter_tocks_\<rho>_in_Q)
      qed
    qed
  next
    fix p X Y Z
    assume case_assms: "p @ [[X]\<^sub>R] \<in> P" "\<sigma> = p @ [[Z]\<^sub>R]" "filter_tocks p @ [[Y]\<^sub>R] \<in> Q" "Z \<subseteq> X \<union> Y" "{e \<in> X. e \<noteq> Tock} = {e \<in> Y. e \<noteq> Tock}"
    then have "\<rho> \<lesssim>\<^sub>C p @ [[Z]\<^sub>R]"
      using assm1 by auto
    thm ctt_prefix_subset_filter_tocks
    then have "\<rho> \<lesssim>\<^sub>C p \<or> \<rho> \<subseteq>\<^sub>C p @ [[Z]\<^sub>R]"
      apply (induct \<rho> p rule:ctt_prefix_subset.induct, auto, case_tac x, auto)
      using ctt_prefix_subset.simps(1) ctt_prefix_subset_antisym ctt_subset_refl by blast
    also have "\<rho> \<subseteq>\<^sub>C p @ [[Z]\<^sub>R] \<Longrightarrow> \<exists> p' Z'. Z' \<subseteq> X \<union> Y \<and> \<rho> = p' @ [[Z']\<^sub>R] \<and> p' \<subseteq>\<^sub>C p"
      apply (induct \<rho> p rule:ctt_subset.induct, auto, rule_tac x="[]" in exI, simp, case_tac v, auto)
      using case_assms(4) ctt_subset_same_length by (auto, force)
    then have "\<rho> \<lesssim>\<^sub>C p \<or> (\<exists> p' Z'. Z' \<subseteq> X \<union> Y \<and> \<rho> = p' @ [[Z']\<^sub>R] \<and> p' \<subseteq>\<^sub>C p)"
      using calculation by auto
    then show "\<rho> \<in> P \<triangle>\<^sub>T Q"
    proof auto
      assume case_assms2: "\<rho> \<lesssim>\<^sub>C p"
      then have \<rho>_in_P: "\<rho> \<in> P"
        using assms(3) case_assms(1) unfolding TT1_def by (meson ctt_prefix_concat ctt_prefix_imp_prefix_subset) 
      have 1: "filter_tocks \<rho> \<lesssim>\<^sub>C filter_tocks \<sigma>"
        by (metis TimeSyncInterruptTTT_wf \<rho>_in_P assm1 assm2 assms(1) assms(2) ctt_prefix_subset_filter_tocks)
      have 2: "filter_tocks \<sigma> = filter_tocks p"
        by (simp add: case_assms, induct p rule:filter_tocks.induct, auto)
      have filter_tocks_\<rho>_in_Q: "filter_tocks \<rho> \<in> Q"
        by (metis "1" "2" TT1_def assms(4) case_assms(3) ctt_prefix_concat ctt_prefix_subset_ctt_prefix_trans)
      have \<rho>_cases: "(\<exists> p' X. \<rho> = p' @ [[Tick]\<^sub>E]) \<or> (\<exists> p' X. \<rho> = p' @ [[X]\<^sub>R]) \<or> ((\<nexists>p'. \<rho> = p' @ [[Tick]\<^sub>E]) \<and> (\<nexists>p' Y. \<rho> = p' @ [[Y]\<^sub>R]))"
        by auto
      then have \<rho>_cases: " (\<exists> p' X. \<rho> = p' @ [[X]\<^sub>R]) \<or> ((\<nexists>p'. \<rho> = p' @ [[Tick]\<^sub>E]) \<and> (\<nexists>p' Y. \<rho> = p' @ [[Y]\<^sub>R]))"
      proof auto
        fix p'a
        assume case_assm3: "\<rho> = p'a @ [[Tick]\<^sub>E]"
        have "\<exists> \<rho>'. \<rho>' \<le>\<^sub>C p \<and> \<rho> \<subseteq>\<^sub>C \<rho>'"
          using case_assms2 ctt_prefix_subset_imp_ctt_subset_ctt_prefix by blast
        then have "\<exists> \<rho>' p'. p = \<rho>' @ p' \<and> \<rho> \<subseteq>\<^sub>C \<rho>'"
          using ctt_prefix_decompose by blast
        then obtain \<rho>' p' where 1: "p = \<rho>' @ p' \<and> \<rho> \<subseteq>\<^sub>C \<rho>'"
          by auto
        then have "\<exists> p'a'. \<rho>' = p'a' @ [[Tick]\<^sub>E]"
          using case_assm3
        proof auto
          fix \<rho>' p'
          show "p'a @ [[Tick]\<^sub>E] \<subseteq>\<^sub>C \<rho>' \<Longrightarrow> \<exists>p'a'. \<rho>' = p'a' @ [[Tick]\<^sub>E]"
            apply (induct p'a \<rho>' rule:ctt_subset.induct, auto, case_tac v, auto)
            using ctt_subset.elims(2) by fastforce+
        qed
        then obtain p'a' where "ttWF (p'a' @ [[Tick]\<^sub>E] @ p' @ [[X]\<^sub>R])"
          using 1 assms(1) case_assms(1) ttWF_prefix_is_ttWF by fastforce
        then show False
          by (induct p'a' rule:ttWF.induct, auto, induct p' rule:ttWF.induct, auto)
      qed
      then show "\<rho> \<in> P \<triangle>\<^sub>T Q"
        unfolding TimeSyncInterruptTTT_def
      proof auto
        fix p' X'
        have ttWF_\<sigma>: "ttWF (p @ [[Z]\<^sub>R])"
          using TimeSyncInterruptTTT_wf assm2 assms(1) assms(2) case_assms(2) by blast
        assume case_assms3: "\<rho> = p' @ [[X']\<^sub>R]"
        then have \<rho>_prefix_subset_\<sigma>: "p' @ [[X']\<^sub>R] \<lesssim>\<^sub>C p @ [[Z]\<^sub>R]"
          using assm1 case_assms(2) by blast
        then have 1: "p' @ [[X']\<^sub>R, [Tock]\<^sub>E] \<lesssim>\<^sub>C p @ [[Z]\<^sub>R]"
          using ttWF_\<sigma> case_assms2 case_assms3
        proof auto
          show "p' @ [[X']\<^sub>R] \<lesssim>\<^sub>C p @ [[Z]\<^sub>R] \<Longrightarrow> ttWF (p @ [[Z]\<^sub>R]) \<Longrightarrow> p' @ [[X']\<^sub>R] \<lesssim>\<^sub>C p \<Longrightarrow> p' @ [[X']\<^sub>R, [Tock]\<^sub>E] \<lesssim>\<^sub>C p @ [[Z]\<^sub>R]"
            apply (induct p' p rule:ttWF2.induct, auto)
            using ttWF.simps(12) ctt_prefix_subset_ttWF apply blast
            apply (meson ttWF.simps(11) ctt_prefix_subset_ttWF)
            using ttWF.simps(13) ctt_prefix_subset_ttWF apply blast
            using ttWF.simps(8) ctt_prefix_subset_ttWF apply blast
            using ttWF.simps(6) ctt_prefix_subset_ttWF by blast
        qed
        then have 2: "p' @ [[X']\<^sub>R, [Tock]\<^sub>E] \<lesssim>\<^sub>C p"
          using ttWF_\<sigma> case_assms3 case_assms2
        proof auto
          show "p' @ [[X']\<^sub>R, [Tock]\<^sub>E] \<lesssim>\<^sub>C p @ [[Z]\<^sub>R] \<Longrightarrow> ttWF (p @ [[Z]\<^sub>R]) \<Longrightarrow> p' @ [[X']\<^sub>R] \<lesssim>\<^sub>C p \<Longrightarrow> p' @ [[X']\<^sub>R, [Tock]\<^sub>E] \<lesssim>\<^sub>C p"
            apply (induct p' p rule:ttWF2.induct, auto)
            using ttWF.simps(12) ctt_prefix_subset_ttWF apply blast
            apply (meson ttWF.simps(11) ctt_prefix_subset_ttWF)
            using ttWF.simps(13) ctt_prefix_subset_ttWF apply blast
            using ttWF.simps(8) ctt_prefix_subset_ttWF apply blast
            using ttWF.simps(6) ctt_prefix_subset_ttWF by blast
        qed
        then have 3: "filter_tocks (p' @ [[X']\<^sub>R, [Tock]\<^sub>E]) \<lesssim>\<^sub>C filter_tocks p"
          using ttWF_\<sigma> ttWF_prefix_is_ttWF ctt_prefix_subset_ttWF ctt_prefix_subset_filter_tocks by blast
        have 4: "filter_tocks (p' @ [[X']\<^sub>R, [Tock]\<^sub>E]) = filter_tocks p' @ [[X']\<^sub>R, [Tock]\<^sub>E]"
          by (induct p' rule:filter_tocks.induct, auto)
        have 5: "filter_tocks p' @ [[X']\<^sub>R, [Tock]\<^sub>E]  \<lesssim>\<^sub>C filter_tocks p"
          using 3 4 by auto
        have 6: "filter_tocks p' @ [[X']\<^sub>R]  \<lesssim>\<^sub>C filter_tocks p' @ [[X']\<^sub>R, [Tock]\<^sub>E]"
          by (induct p' rule:filter_tocks.induct, auto)
        then have "filter_tocks p' @ [[X']\<^sub>R]  \<lesssim>\<^sub>C filter_tocks p"
          using 5 ctt_prefix_subset_trans by blast
        then have "filter_tocks p' @ [[X']\<^sub>R] \<in> Q"
          by (meson TT1_def assms(4) case_assms(3) ctt_prefix_concat ctt_prefix_imp_prefix_subset)
        then show "\<rho> = p' @ [[X']\<^sub>R] \<Longrightarrow>
          \<exists>p Xa. p @ [[Xa]\<^sub>R] \<in> P \<and> (\<exists>Y. filter_tocks p @ [[Y]\<^sub>R] \<in> Q \<and> X' \<subseteq> Xa \<union> Y \<and> {e \<in> Xa. e \<noteq> Tock} = {e \<in> Y. e \<noteq> Tock} \<and> p' = p)"
          using \<rho>_in_P by (rule_tac x="p'" in exI, rule_tac x="X'" in exI, auto)
      next
        show "\<forall>p. p \<in> P \<longrightarrow> (\<exists>p'. p = p' @ [[Tick]\<^sub>E]) \<or> (\<exists>p' Y. p = p' @ [[Y]\<^sub>R]) \<or>
            (\<forall>q2. filter_tocks p @ q2 \<in> Q \<longrightarrow> (\<exists>q' Y. q2 = [Y]\<^sub>R # q') \<or> \<rho> \<noteq> p @ q2) \<Longrightarrow>
          \<forall>p'. \<rho> \<noteq> p' @ [[Tick]\<^sub>E] \<Longrightarrow> \<forall>p' Y. \<rho> \<noteq> p' @ [[Y]\<^sub>R] \<Longrightarrow> False"
          using \<rho>_in_P filter_tocks_\<rho>_in_Q by (erule_tac x="\<rho>" in allE, auto, force)
      qed
    next
      fix p' Z'
      thm case_assms
      assume case_assms2: "Z' \<subseteq> X \<union> Y" "p' \<subseteq>\<^sub>C p" "\<rho> = p' @ [[Z']\<^sub>R]"
      have "p' @ [[X]\<^sub>R] \<subseteq>\<^sub>C p @ [[X]\<^sub>R]"
        by (simp add: case_assms2(2) ctt_subset_combine)
      then have p'_X_in_P: "p' @ [[X]\<^sub>R] \<in> P"
        using assms(3) case_assms(1) ctt_subset_imp_prefix_subset unfolding TT1_def by blast
      have "filter_tocks p' \<subseteq>\<^sub>C filter_tocks p"
        using assms(1) case_assms(1) case_assms2(2) ttWF_prefix_is_ttWF ctt_prefix_subset_ttWF ctt_subset_filter_tocks ctt_subset_imp_prefix_subset by blast
      then have "filter_tocks p' @ [[Y]\<^sub>R] \<subseteq>\<^sub>C filter_tocks p @ [[Y]\<^sub>R]"
        by (simp add: ctt_subset_combine)
      then have "filter_tocks p' @ [[Y]\<^sub>R] \<lesssim>\<^sub>C filter_tocks p @ [[Y]\<^sub>R]"
        using ctt_subset_imp_prefix_subset by blast 
      then have "filter_tocks p' @ [[Y]\<^sub>R] \<in> Q"
        using assms(4) case_assms(3) ctt_subset_imp_prefix_subset unfolding TT1_def by blast
      then show "p' @ [[Z']\<^sub>R] \<in> P \<triangle>\<^sub>T Q"
        unfolding TimeSyncInterruptTTT_def using p'_X_in_P case_assms case_assms2 by auto
    qed
  next
    fix p q2
    assume case_assms: "p \<in> P" "\<forall>p'. p \<noteq> p' @ [[Tick]\<^sub>E]" "\<forall>p' Y. p \<noteq> p' @ [[Y]\<^sub>R]"
        "filter_tocks p @ q2 \<in> Q" "\<forall>q' Y. q2 \<noteq> [Y]\<^sub>R # q'" "\<sigma> = p @ q2"
    have "\<rho> \<lesssim>\<^sub>C p \<or> (\<exists> p' q'. q' \<lesssim>\<^sub>C q2 \<and> p' \<subseteq>\<^sub>C p \<and> \<rho> = p' @ q')"
      using assm1 case_assms(6) ctt_prefix_subset_concat2 by blast
    then show "\<rho> \<in> P \<triangle>\<^sub>T Q"
      unfolding TimeSyncInterruptTTT_def
    proof auto
      assume case_assms2: "\<rho> \<lesssim>\<^sub>C p"
      have "(\<exists>p' Y. \<rho> = p' @ [[Y]\<^sub>R]) \<or> ((\<forall>p'. \<rho> \<noteq> p' @ [[Tick]\<^sub>E]) \<and> (\<forall>p' Y. \<rho> \<noteq> p' @ [[Y]\<^sub>R]))"
      proof auto
        fix p'
        have p_wf: "ttWF p"
          by (simp add: assms(1) case_assms(1))
        assume "\<rho> = p' @ [[Tick]\<^sub>E]"
        then have 1: "p' @ [[Tick]\<^sub>E] \<lesssim>\<^sub>C p"
          using case_assms2 by auto
        then have "ttWF (p' @ [[Tick]\<^sub>E])"
          using ctt_prefix_subset_ttWF p_wf by blast
        then show False
          using case_assms(2) p_wf 1 by (induct p' p rule:ttWF2.induct, auto, fastforce+)
      qed
      then show " \<forall>p. p \<in> P \<longrightarrow> (\<exists>p'. p = p' @ [[Tick]\<^sub>E]) \<or> (\<exists>p' Y. p = p' @ [[Y]\<^sub>R]) \<or>
          (\<forall>q2. filter_tocks p @ q2 \<in> Q \<longrightarrow> (\<exists>q' Y. q2 = [Y]\<^sub>R # q') \<or> \<rho> \<noteq> p @ q2) \<Longrightarrow>
        \<exists>p X. p @ [[X]\<^sub>R] \<in> P \<and> (\<exists>Y. filter_tocks p @ [[Y]\<^sub>R] \<in> Q \<and>
          (\<exists>Z\<subseteq>X \<union> Y. {e \<in> X. e \<noteq> Tock} = {e \<in> Y. e \<noteq> Tock} \<and> \<rho> = p @ [[Z]\<^sub>R]))"
      proof auto
        fix p' Y
        assume case_assms3: "\<rho> = p' @ [[Y]\<^sub>R]"
        have "filter_tocks p' @ [[Y]\<^sub>R] \<in> Q"
        proof -
          have p_wf: "ttWF p"
            by (simp add: assms(1) case_assms(1))
          have p'_wf: "ttWF (p' @ [[Y]\<^sub>R])"
            using case_assms2 case_assms3 ctt_prefix_subset_ttWF p_wf by blast
          have "p' @ [[Y]\<^sub>R] \<lesssim>\<^sub>C p"
            using case_assms2 case_assms3 by auto
          then have "p' @ [[Y]\<^sub>R, [Tock]\<^sub>E] \<lesssim>\<^sub>C p"
            using case_assms(3) p_wf p'_wf by (induct p' p rule:ttWF2.induct, auto, fastforce+)
          then have 1: "filter_tocks (p' @ [[Y]\<^sub>R, [Tock]\<^sub>E]) \<lesssim>\<^sub>C filter_tocks p"
            using ctt_prefix_subset_ttWF ctt_prefix_subset_filter_tocks p_wf by blast
          have "filter_tocks (p' @ [[Y]\<^sub>R, [Tock]\<^sub>E]) = filter_tocks p' @ [[Y]\<^sub>R, [Tock]\<^sub>E]"
            by (induct p' rule:filter_tocks.induct, auto)
          then have "filter_tocks p' @ [[Y]\<^sub>R]  \<lesssim>\<^sub>C filter_tocks (p' @ [[Y]\<^sub>R, [Tock]\<^sub>E])"
            using ctt_prefix_subset_same_front by fastforce
          then have "filter_tocks p' @ [[Y]\<^sub>R] \<lesssim>\<^sub>C filter_tocks p"
            using "1" ctt_prefix_subset_trans by blast
          then show "filter_tocks p' @ [[Y]\<^sub>R] \<in> Q"
            by (meson TT1_def assms(4) case_assms(4) ctt_prefix_concat ctt_prefix_imp_prefix_subset)
        qed
        then show "\<exists>p X. p @ [[X]\<^sub>R] \<in> P \<and> (\<exists>Ya. filter_tocks p @ [[Ya]\<^sub>R] \<in> Q \<and> Y \<subseteq> X \<union> Ya \<and> {e \<in> X. e \<noteq> Tock} = {e \<in> Ya. e \<noteq> Tock} \<and> p' = p)"
          using TT1_def assms(3) case_assms(1) case_assms2 case_assms3 by blast
      next
        assume case_assms3: "\<forall>p'. \<rho> \<noteq> p' @ [[Tick]\<^sub>E]" "\<forall>p' Y. \<rho> \<noteq> p' @ [[Y]\<^sub>R]"
        have "filter_tocks \<rho> \<lesssim>\<^sub>C filter_tocks p"
          using assms(1) case_assms(1) case_assms2 ctt_prefix_subset_ttWF ctt_prefix_subset_filter_tocks by blast
        then have "filter_tocks \<rho> \<in> Q"
          by (meson TT1_def assms(4) case_assms(4) ctt_prefix_concat ctt_prefix_imp_prefix_subset)
        also have "\<rho> \<in> P"
          using TT1_def assms(3) case_assms(1) case_assms2 by blast
        then show "\<forall>p. p \<in> P \<longrightarrow> (\<exists>p'. p = p' @ [[Tick]\<^sub>E]) \<or> (\<exists>p' Y. p = p' @ [[Y]\<^sub>R]) \<or>
          (\<forall>q2. filter_tocks p @ q2 \<in> Q \<longrightarrow> (\<exists>q' Y. q2 = [Y]\<^sub>R # q') \<or> \<rho> \<noteq> p @ q2) \<Longrightarrow> False"
          by (metis append_self_conv calculation case_assms3(1) case_assms3(2) list.discI)
      qed
    next
      fix p' q'
      assume case_assms2: "q' \<lesssim>\<^sub>C q2" "p' \<subseteq>\<^sub>C p" "\<rho> = p' @ q'"
      have 1: "(\<forall>p''. p' \<noteq> p'' @ [[Tick]\<^sub>E]) \<and> (\<forall>p'' Y. p' \<noteq> p'' @ [[Y]\<^sub>R])"
        using case_assms2(2) case_assms(2) case_assms(3) apply (induct p' p rule:ctt_subset.induct, auto)
        by (smt append_butlast_last_id ctt_subset_same_length last.simps last_appendR length_0_conv list.distinct(1))+
      have p'_in_P: "p' \<in> P"
        using TT1_def assms(3) case_assms(1) case_assms2(2) ctt_subset_imp_prefix_subset by blast
      then have 2: "filter_tocks p' \<subseteq>\<^sub>C filter_tocks p"
        by (simp add: assms(1) case_assms(1) case_assms2(2) ctt_subset_filter_tocks)
      then have "filter_tocks p' @ q' \<lesssim>\<^sub>C filter_tocks p' @ q2"
        using case_assms2(1) ctt_prefix_subset_same_front by blast
      then have "filter_tocks p' @ q' \<lesssim>\<^sub>C filter_tocks p @ q2"
        using "2" ctt_prefix_subset_trans ctt_subset_combine ctt_subset_imp_prefix_subset ctt_subset_refl by blast
      then have "filter_tocks p' @ q' \<in> Q"
        using TT1_def assms(4) case_assms(4) by blast
      then show "\<forall>p. p \<in> P \<longrightarrow> (\<exists>p'. p = p' @ [[Tick]\<^sub>E]) \<or> (\<exists>p' Y. p = p' @ [[Y]\<^sub>R]) \<or>
          (\<forall>q2. filter_tocks p @ q2 \<in> Q \<longrightarrow> (\<exists>q' Y. q2 = [Y]\<^sub>R # q') \<or> p' @ q' \<noteq> p @ q2) \<Longrightarrow>
        \<exists>p X. p @ [[X]\<^sub>R] \<in> P \<and> (\<exists>Y. filter_tocks p @ [[Y]\<^sub>R] \<in> Q \<and> (\<exists>Z\<subseteq>X \<union> Y. {e \<in> X. e \<noteq> Tock} = {e \<in> Y. e \<noteq> Tock} \<and> p' @ q' = p @ [[Z]\<^sub>R]))"
        using p'_in_P 1 apply (erule_tac x="p'" in allE, auto, erule_tac x="q'" in allE, auto)
        by (metis case_assms(5) case_assms2(1) contains_refusal.cases ctt_prefix_subset.simps(1) ctt_prefix_subset.simps(5) ctt_prefix_subset_antisym)
    qed
  qed
qed

lemma TT2_TimeSyncInterrupt:
  assumes P_wf: "\<forall>x\<in>P. ttWF x"
  assumes TT1_P: "TT1 P" and TT1_Q: "TT1 Q"
  assumes TT2_P: "TT2 P" and TT2_Q: "TT2 Q"
  assumes TT3_P: "TT3 P" and TT3_Q: "TT3 Q"
  shows "TT2 (P \<triangle>\<^sub>T Q)"
  unfolding TT2_def
proof auto
  fix \<rho> X Y
  assume assm1: "\<rho> @ [[X]\<^sub>R] \<in> P \<triangle>\<^sub>T Q"
  assume assm2: "Y \<inter> {e. e \<noteq> Tock \<and> \<rho> @ [[e]\<^sub>E] \<in> P \<triangle>\<^sub>T Q \<or> e = Tock \<and> \<rho> @ [[X]\<^sub>R, [e]\<^sub>E] \<in> P \<triangle>\<^sub>T Q} = {}"
  have "(\<exists> Z W q. \<rho> @ [[Z]\<^sub>R] \<in> P \<and> filter_tocks \<rho> = q \<and> q @ [[W]\<^sub>R] \<in> Q \<and> X \<subseteq> Z \<union> W \<and> {e \<in> Z. e \<noteq> Tock} = {e \<in> W. e \<noteq> Tock})
    \<or> (\<exists>p q1 q2. p \<in> P \<and> (\<nexists>p'. p = p' @ [[Tick]\<^sub>E]) \<and> (\<nexists>p' Y. p = p' @ [[Y]\<^sub>R]) \<and> filter_tocks p = q1 \<and>
      q1 @ q2 @ [[X]\<^sub>R] \<in> Q \<and> (\<nexists>q' Y. q2 @ [[X]\<^sub>R] = [Y]\<^sub>R # q') \<and> \<rho> @ [[X]\<^sub>R] = p @ q2 @ [[X]\<^sub>R])"
    using assm1 unfolding TimeSyncInterruptTTT_def
  proof (safe, simp_all)
    fix Xa Y
    assume "\<rho> @ [[Xa]\<^sub>R] \<in> P" "filter_tocks \<rho> @ [[Y]\<^sub>R] \<in> Q" "X \<subseteq> Xa \<union> Y" "{e \<in> Xa. e \<noteq> Tock} = {e \<in> Y. e \<noteq> Tock}"
    then show "\<exists>Z. \<rho> @ [[Z]\<^sub>R] \<in> P \<and> (\<exists>W. filter_tocks \<rho> @ [[W]\<^sub>R] \<in> Q \<and> X \<subseteq> Z \<union> W \<and> {e \<in> Z. e \<noteq> Tock} = {e \<in> W. e \<noteq> Tock})"
      by (rule_tac x="Xa" in exI, auto)
  next
    fix p q2
    assume case_assms: "p \<in> P" "\<forall>p'. p \<noteq> p' @ [[Tick]\<^sub>E]" "\<forall>p' Y. p \<noteq> p' @ [[Y]\<^sub>R]"
      "filter_tocks p @ q2 \<in> Q" "\<forall>q' Y. q2 \<noteq> [Y]\<^sub>R # q'" "\<rho> @ [[X]\<^sub>R] = p @ q2"
    have "\<exists> q'. \<rho> @ [[X]\<^sub>R] = p @ q' @ [[X]\<^sub>R]"
      using case_assms(6) by (auto, metis append_butlast_last_id append_self_conv case_assms(3) last_appendR last_snoc) 
    then show "\<forall>pa. pa \<in> P \<longrightarrow> (\<exists>p'. pa = p' @ [[Tick]\<^sub>E]) \<or> (\<exists>p' Y. pa = p' @ [[Y]\<^sub>R]) \<or>
        (\<forall>q2a. filter_tocks pa @ q2a @ [[X]\<^sub>R] \<in> Q \<longrightarrow> (\<exists>q' Y. q2a @ [[X]\<^sub>R] = [Y]\<^sub>R # q') \<or> p @ q2 \<noteq> pa @ q2a @ [[X]\<^sub>R]) \<Longrightarrow>
      \<exists>Z. \<rho> @ [[Z]\<^sub>R] \<in> P \<and> (\<exists>W. filter_tocks \<rho> @ [[W]\<^sub>R] \<in> Q \<and> X \<subseteq> Z \<union> W \<and> {e \<in> Z. e \<noteq> Tock} = {e \<in> W. e \<noteq> Tock})"
      using case_assms by (erule_tac x=p in allE, auto)
  qed
  then show "\<rho> @ [[X \<union> Y]\<^sub>R] \<in> P \<triangle>\<^sub>T Q"
  proof (safe, simp_all)
    fix Z W
    assume case_assms: "\<rho> @ [[Z]\<^sub>R] \<in> P" "filter_tocks \<rho> @ [[W]\<^sub>R] \<in> Q" "X \<subseteq> Z \<union> W" "{e \<in> Z. e \<noteq> Tock} = {e \<in> W. e \<noteq> Tock}"
    have \<rho>_in_P: "\<rho> \<in> P"
      using TT1_P TT1_def case_assms(1) ctt_prefix_concat ctt_prefix_imp_prefix_subset by blast
    have \<rho>_end_assms: "(\<nexists> \<rho>'. \<rho> = \<rho>' @ [[Tick]\<^sub>E]) \<and> (\<nexists> \<rho>' X. \<rho> = \<rho>' @ [[X]\<^sub>R])"
    proof auto
      fix \<rho>'
      assume "\<rho> = \<rho>' @ [[Tick]\<^sub>E]"
      then have "ttWF (\<rho>' @ [[Tick]\<^sub>E, [Z]\<^sub>R])"
        using case_assms(1) P_wf by auto
      then show False
        by (induct \<rho>' rule:ttWF.induct, auto)
    next
      fix \<rho>' X
      assume "\<rho> = \<rho>' @ [[X]\<^sub>R]"
      then have "ttWF (\<rho>' @ [[X]\<^sub>R, [Z]\<^sub>R])"
        using case_assms(1) P_wf by auto
      then show False
        by (induct \<rho>' rule:ttWF.induct, auto)
    qed
    have "{e. e \<noteq> Tock \<and> \<rho> @ [[e]\<^sub>E] \<in> P} \<union> {e. e \<noteq> Tock \<and> filter_tocks \<rho> @ [[e]\<^sub>E] \<in> Q}
          \<subseteq> {e. e \<noteq> Tock \<and> \<rho> @ [[e]\<^sub>E] \<in> P \<triangle>\<^sub>T Q}"
      unfolding TimeSyncInterruptTTT_def
    proof (safe, simp_all)
      fix x
      assume "\<rho> @ [[x]\<^sub>E] \<in> P" "x \<noteq> Tock"
      then show "\<forall>p. p \<in> P \<longrightarrow> (\<exists>p'. p = p' @ [[Tick]\<^sub>E]) \<or> (\<exists>p' Y. p = p' @ [[Y]\<^sub>R]) \<or>
          (\<forall>q2. filter_tocks p @ q2 \<in> Q \<longrightarrow> (\<exists>q' Y. q2 = [Y]\<^sub>R # q') \<or> \<rho> @ [[x]\<^sub>E] \<noteq> p @ q2) \<Longrightarrow>
        \<rho> @ [[Tick]\<^sub>E] \<in> P \<and> filter_tocks \<rho> \<in> Q \<and> x = Tick"
        apply (cases x, auto, erule_tac x="\<rho> @ [[Event x1]\<^sub>E]" in allE, auto)
        apply (metis TT1_Q TT1_def append_Nil2 case_assms(2) ctt_prefix_concat ctt_prefix_imp_prefix_subset filter_tocks_end_event list.simps(3))
        by (meson TT1_Q TT1_def case_assms(2) ctt_prefix_concat ctt_prefix_imp_prefix_subset)
    next
      fix x
      assume "filter_tocks \<rho> @ [[x]\<^sub>E] \<in> Q" "x \<noteq> Tock"
      then show "\<forall>p. p \<in> P \<longrightarrow> (\<exists>p'. p = p' @ [[Tick]\<^sub>E]) \<or> (\<exists>p' Y. p = p' @ [[Y]\<^sub>R]) \<or>
          (\<forall>q2. filter_tocks p @ q2 \<in> Q \<longrightarrow> (\<exists>q' Y. q2 = [Y]\<^sub>R # q') \<or> \<rho> @ [[x]\<^sub>E] \<noteq> p @ q2) \<Longrightarrow>
        \<rho> @ [[Tick]\<^sub>E] \<in> P \<and> filter_tocks \<rho> \<in> Q \<and> x = Tick"
        apply (cases x, auto)
        using \<rho>_end_assms \<rho>_in_P by blast+
    qed
    then have P_nontock_inter: "{e\<in>Y. e \<noteq> Tock} \<inter> {e. e \<noteq> Tock \<and> \<rho> @ [[e]\<^sub>E] \<in> P} = {}"
      and Q_nontock_inter: "{e\<in>Y. e \<noteq> Tock} \<inter> {e. e \<noteq> Tock \<and> filter_tocks \<rho> @ [[e]\<^sub>E] \<in> Q} = {}"
      using assm2 inf.orderE mem_Collect_eq by fastforce+
    thm assm2
    thm case_assms
    have "{e. e = Tock \<and> \<rho> @ [[Z]\<^sub>R, [e]\<^sub>E] \<in> P} \<inter> {e. e = Tock \<and> filter_tocks \<rho> @ [[W]\<^sub>R, [e]\<^sub>E] \<in> Q}
          \<subseteq> {e. e = Tock \<and> \<rho> @ [[X]\<^sub>R, [e]\<^sub>E] \<in> P \<triangle>\<^sub>T Q}"
      unfolding TimeSyncInterruptTTT_def
    proof (safe, simp_all)  
      assume assm: "\<rho> @ [[Z]\<^sub>R, [Tock]\<^sub>E] \<in> P" "filter_tocks \<rho> @ [[W]\<^sub>R, [Tock]\<^sub>E] \<in> Q"
      then have Tock_notin_Z: "Tock \<notin> Z \<and> Tock \<notin> W"
        using TT3_P TT3_Q TT3_any_cons_end_tock by blast
      then have "Z = W"
        using Collect_mono Collect_mono_iff case_assms(4) by auto
      then have "\<rho> @ [[X]\<^sub>R, [Tock]\<^sub>E] \<in> P \<and> filter_tocks \<rho> @ [[X]\<^sub>R, [Tock]\<^sub>E] \<in> Q"
        using case_assms(3) apply auto
        apply (metis TT1_P TT1_def assm(1) ctt_prefix_subset.simps(2) ctt_prefix_subset_refl ctt_prefix_subset_same_front)
        by (metis TT1_Q TT1_def assm(2) ctt_prefix_subset.simps(2) ctt_prefix_subset_refl ctt_prefix_subset_same_front)
      then show "\<forall>p. p \<in> P \<longrightarrow> (\<exists>p'. p = p' @ [[Tick]\<^sub>E]) \<or> (\<exists>p' Y. p = p' @ [[Y]\<^sub>R]) \<or>
        (\<forall>q2. filter_tocks p @ q2 \<in> Q \<longrightarrow> (\<exists>q' Y. q2 = [Y]\<^sub>R # q') \<or> \<rho> @ [[X]\<^sub>R, [Tock]\<^sub>E] \<noteq> p @ q2) \<Longrightarrow> False"
        by (erule_tac x="\<rho> @ [[X]\<^sub>R, [Tock]\<^sub>E]" in allE, auto, erule_tac x="[]" in allE, auto simp add: case_assms(4) filter_tocks_end_ref_tock)
    qed
    then have tock_inter_cases: "{e\<in>Y. e = Tock} \<inter> {e. e = Tock \<and> \<rho> @ [[Z]\<^sub>R, [e]\<^sub>E] \<in> P} = {} \<or> {e\<in>Y. e = Tock} \<inter> {e. e = Tock \<and> filter_tocks \<rho> @ [[W]\<^sub>R, [e]\<^sub>E] \<in> Q} = {}"
      using assm2 by auto
    show "\<rho> @ [[X \<union> Y]\<^sub>R] \<in> P \<triangle>\<^sub>T Q"
    proof (cases "Tock \<in> Y")
      assume Tock_in_Y: "Tock \<in> Y"
      show "\<rho> @ [[X \<union> Y]\<^sub>R] \<in> P \<triangle>\<^sub>T Q"
        using tock_inter_cases
      proof safe
        assume case_assms2: "{e \<in> Y. e = Tock} \<inter> {e. e = Tock \<and> \<rho> @ [[Z]\<^sub>R, [e]\<^sub>E] \<in> P} = {}"
        then have "Y \<inter> {e. e \<noteq> Tock \<and> \<rho> @ [[e]\<^sub>E] \<in> P \<or> e = Tock \<and> \<rho> @ [[Z]\<^sub>R, [e]\<^sub>E] \<in> P} = {}"
          using P_nontock_inter by auto
        then have \<rho>_Z_Y_in_P: "\<rho> @ [[Z \<union> Y]\<^sub>R] \<in> P"
          using TT2_P case_assms(1) unfolding TT2_def by auto
        have "{e\<in>Y. e \<noteq> Tock} \<inter> {e. e \<noteq> Tock \<and> filter_tocks \<rho> @ [[e]\<^sub>E] \<in> Q \<or> e = Tock \<and> filter_tocks \<rho> @ [[W]\<^sub>R, [e]\<^sub>E] \<in> Q} = {}"
          using Q_nontock_inter by auto
        then have \<rho>_W_Y_in_Q: "filter_tocks \<rho> @ [[W \<union> {e\<in>Y. e \<noteq> Tock}]\<^sub>R] \<in> Q"
          using TT2_Q case_assms(2) unfolding TT2_def by auto
        show "\<rho> @ [[X \<union> Y]\<^sub>R] \<in> P \<triangle>\<^sub>T Q"
          using \<rho>_Z_Y_in_P \<rho>_W_Y_in_Q unfolding TimeSyncInterruptTTT_def apply (auto)
          apply (rule_tac x="\<rho>" in exI, auto, rule_tac x="Z \<union> Y" in exI, auto)
          using case_assms by (rule_tac x="W \<union> {e\<in>Y. e \<noteq> Tock}" in exI, auto)
      next
        assume case_assms2: "{e \<in> Y. e = Tock} \<inter> {e. e = Tock \<and> filter_tocks \<rho> @ [[W]\<^sub>R, [e]\<^sub>E] \<in> Q} = {}"
        then have "Y \<inter> {e. e \<noteq> Tock \<and> filter_tocks \<rho> @ [[e]\<^sub>E] \<in> Q \<or> e = Tock \<and> filter_tocks \<rho> @ [[W]\<^sub>R, [e]\<^sub>E] \<in> Q} = {}"
          using Q_nontock_inter by auto
        then have \<rho>_W_Y_in_Q: "filter_tocks \<rho> @ [[W \<union> Y]\<^sub>R] \<in> Q"
          using TT2_Q case_assms(2) unfolding TT2_def by auto
        have "{e\<in>Y. e \<noteq> Tock} \<inter> {e. e \<noteq> Tock \<and> \<rho> @ [[e]\<^sub>E] \<in> P \<or> e = Tock \<and> \<rho> @ [[Z]\<^sub>R, [e]\<^sub>E] \<in> P} = {}"
          using P_nontock_inter by auto
        then have \<rho>_Z_Y_in_P: "\<rho> @ [[Z \<union> {e\<in>Y. e \<noteq> Tock}]\<^sub>R] \<in> P"
          using TT2_P case_assms(1) unfolding TT2_def by auto
        show "\<rho> @ [[X \<union> Y]\<^sub>R] \<in> P \<triangle>\<^sub>T Q"
          using \<rho>_Z_Y_in_P \<rho>_W_Y_in_Q unfolding TimeSyncInterruptTTT_def apply (auto)
          apply (rule_tac x="\<rho>" in exI, auto, rule_tac x="Z \<union> {e\<in>Y. e \<noteq> Tock}" in exI, auto)
          using case_assms by (rule_tac x="W \<union> Y" in exI, auto)
      qed
    next
      assume Tock_notin_Y: "Tock \<notin> Y"
      have "{e\<in>Y. e \<noteq> Tock} \<inter> {e. e \<noteq> Tock \<and> \<rho> @ [[e]\<^sub>E] \<in> P \<or> e = Tock \<and> \<rho> @ [[Z]\<^sub>R, [e]\<^sub>E] \<in> P} = {}"
        using P_nontock_inter by auto
      then have \<rho>_Z_Y_in_P: "\<rho> @ [[Z \<union> {e\<in>Y. e \<noteq> Tock}]\<^sub>R] \<in> P"
        using TT2_P case_assms(1) unfolding TT2_def by auto
      have "{e\<in>Y. e \<noteq> Tock} \<inter> {e. e \<noteq> Tock \<and> filter_tocks \<rho> @ [[e]\<^sub>E] \<in> Q \<or> e = Tock \<and> filter_tocks \<rho> @ [[W]\<^sub>R, [e]\<^sub>E] \<in> Q} = {}"
        using Q_nontock_inter by auto
      then have \<rho>_W_Y_in_Q: "filter_tocks \<rho> @ [[W \<union> {e\<in>Y. e \<noteq> Tock}]\<^sub>R] \<in> Q"
        using TT2_Q case_assms(2) unfolding TT2_def by auto
      show "\<rho> @ [[X \<union> Y]\<^sub>R] \<in> P \<triangle>\<^sub>T Q"
        using \<rho>_Z_Y_in_P \<rho>_W_Y_in_Q unfolding TimeSyncInterruptTTT_def apply (auto)
        apply (rule_tac x="\<rho>" in exI, auto, rule_tac x="Z \<union> {e\<in>Y. e \<noteq> Tock}" in exI, auto)
        using case_assms Tock_notin_Y by (rule_tac x="W \<union> {e\<in>Y. e \<noteq> Tock}" in exI, auto)
    qed
  next
    fix p q2
    assume case_assms: "p \<in> P" "\<forall>p'. p \<noteq> p' @ [[Tick]\<^sub>E]" "\<forall>p' Y. p \<noteq> p' @ [[Y]\<^sub>R]"
      "filter_tocks p @ q2 @ [[X]\<^sub>R] \<in> Q" "\<forall>q' Y. q2 @ [[X]\<^sub>R] \<noteq> [Y]\<^sub>R # q'" "\<rho> = p @ q2"
    have "{e. e \<noteq> Tock \<and> filter_tocks p @ q2 @ [[e]\<^sub>E] \<in> Q \<or> e = Tock \<and> filter_tocks p @ q2 @ [[X]\<^sub>R, [e]\<^sub>E] \<in> Q}
        \<subseteq> {e. e \<noteq> Tock \<and> \<rho> @ [[e]\<^sub>E] \<in> P \<triangle>\<^sub>T Q \<or> e = Tock \<and> \<rho> @ [[X]\<^sub>R, [e]\<^sub>E] \<in> P \<triangle>\<^sub>T Q}"
      unfolding TimeSyncInterruptTTT_def
    proof (safe, simp_all)
      fix x
      assume "filter_tocks p @ q2 @ [[x]\<^sub>E] \<in> Q" "x \<noteq> Tock"
      then show "\<forall>p. p \<in> P \<longrightarrow> (\<exists>p'. p = p' @ [[Tick]\<^sub>E]) \<or> (\<exists>p' Y. p = p' @ [[Y]\<^sub>R]) \<or>
          (\<forall>q2. filter_tocks p @ q2 \<in> Q \<longrightarrow> (\<exists>q' Y. q2 = [Y]\<^sub>R # q') \<or> \<rho> @ [[x]\<^sub>E] \<noteq> p @ q2) \<Longrightarrow>
        \<rho> @ [[Tick]\<^sub>E] \<in> P \<and> filter_tocks \<rho> \<in> Q \<and> x = Tick"
        using case_assms apply (erule_tac x="p" in allE, auto)
        by (erule_tac x="q2 @ [[x]\<^sub>E]" in allE, auto, metis Cons_eq_append_conv append_Cons case_assms(5))+
    next
      fix x
      assume "filter_tocks p @ q2 @ [[x]\<^sub>E] \<in> Q" "x \<noteq> Tock"
      then show "\<forall>p. p \<in> P \<longrightarrow> (\<exists>p'. p = p' @ [[Tick]\<^sub>E]) \<or> (\<exists>p' Y. p = p' @ [[Y]\<^sub>R]) \<or>
          (\<forall>q2. filter_tocks p @ q2 \<in> Q \<longrightarrow> (\<exists>q' Y. q2 = [Y]\<^sub>R # q') \<or> \<rho> @ [[x]\<^sub>E] \<noteq> p @ q2) \<Longrightarrow>
        \<rho> @ [[Tick]\<^sub>E] \<in> P \<and> filter_tocks \<rho> \<in> Q \<and> x = Tick"
        using case_assms apply (erule_tac x="p" in allE, auto)
        by (erule_tac x="q2 @ [[x]\<^sub>E]" in allE, auto, metis Cons_eq_append_conv append_Cons case_assms(5))+
    next
      assume "filter_tocks p @ q2 @ [[X]\<^sub>R, [Tock]\<^sub>E] \<in> Q"
      then show "\<forall>p. p \<in> P \<longrightarrow> (\<exists>p'. p = p' @ [[Tick]\<^sub>E]) \<or> (\<exists>p' Y. p = p' @ [[Y]\<^sub>R]) \<or>
        (\<forall>q2. filter_tocks p @ q2 \<in> Q \<longrightarrow> (\<exists>q' Y. q2 = [Y]\<^sub>R # q') \<or> \<rho> @ [[X]\<^sub>R, [Tock]\<^sub>E] \<noteq> p @ q2) \<Longrightarrow> False"
        using case_assms apply (erule_tac x="p" in allE, auto)
        by (erule_tac x="q2 @ [[X]\<^sub>R, [Tock]\<^sub>E]" in allE, auto, metis Cons_eq_append_conv append_Cons case_assms(5))+
    next
      assume "filter_tocks p @ q2 @ [[X]\<^sub>R, [Tock]\<^sub>E] \<in> Q"
      then show "\<forall>p. p \<in> P \<longrightarrow> (\<exists>p'. p = p' @ [[Tick]\<^sub>E]) \<or> (\<exists>p' Y. p = p' @ [[Y]\<^sub>R]) \<or>
        (\<forall>q2. filter_tocks p @ q2 \<in> Q \<longrightarrow> (\<exists>q' Y. q2 = [Y]\<^sub>R # q') \<or> \<rho> @ [[X]\<^sub>R, [Tock]\<^sub>E] \<noteq> p @ q2) \<Longrightarrow> False"
        using case_assms apply (erule_tac x="p" in allE, auto)
        by (erule_tac x="q2 @ [[X]\<^sub>R, [Tock]\<^sub>E]" in allE, auto, metis Cons_eq_append_conv append_Cons case_assms(5))+
    qed
    then have "Y \<inter> {e. e \<noteq> Tock \<and> filter_tocks p @ q2 @ [[e]\<^sub>E] \<in> Q \<or> e = Tock \<and> filter_tocks p @ q2 @ [[X]\<^sub>R, [e]\<^sub>E] \<in> Q} = {}"
      using assm2 by auto
    then have "filter_tocks p @ q2 @ [[X \<union> Y]\<^sub>R] \<in> Q"
      using TT2_Q case_assms unfolding TT2_def by (erule_tac x="filter_tocks p @ q2" in allE, auto)
    then show "p @ q2 @ [[X \<union> Y]\<^sub>R] \<in> P \<triangle>\<^sub>T Q"
      unfolding TimeSyncInterruptTTT_def
      apply (auto, erule_tac x=p in allE, auto simp add: case_assms, erule_tac x="q2 @ [[X \<union> Y]\<^sub>R]" in allE, auto simp add: case_assms)
      by (metis (no_types, lifting) Cons_eq_append_conv append_Cons case_assms(5))
  qed
qed

lemma TT2s_TimeSyncInterrupt:
  assumes P_wf: "\<forall>x\<in>P. ttWF x" assumes Q_wf: "\<forall>x\<in>Q. ttWF x"
  assumes TT1_P: "TT1 P" and TT1_Q: "TT1 Q"
  assumes TT2_P: "TT2 P" and TT2_Q: "TT2 Q"
  assumes TT2s_P: "TT2s P" and TT2s_Q: "TT2s Q"
  assumes TT3_P: "TT3 P" and TT3_Q: "TT3 Q"
  shows "TT2s (P \<triangle>\<^sub>T Q)"
  unfolding TT2s_def
proof auto
  fix \<rho> \<sigma> X Y
  assume assm1: "\<rho> @ [X]\<^sub>R # \<sigma> \<in> P \<triangle>\<^sub>T Q"
  assume assm2: "Y \<inter> {e. e \<noteq> Tock \<and> \<rho> @ [[e]\<^sub>E] \<in> P \<triangle>\<^sub>T Q \<or> e = Tock \<and> \<rho> @ [[X]\<^sub>R, [e]\<^sub>E] \<in> P \<triangle>\<^sub>T Q} = {}"
  have "ttWF (\<rho> @ [X]\<^sub>R # \<sigma>)"
    using P_wf Q_wf TimeSyncInterruptTTT_wf assm1 by blast
  then have "\<sigma> = [] \<or> (\<exists> \<sigma>'. \<sigma> = [Tock]\<^sub>E # \<sigma>')"
    by (induct \<rho> rule:ttWF.induct, auto, cases \<sigma> rule:ttWF.cases, auto)
  then show "\<rho> @ [X \<union> Y]\<^sub>R # \<sigma> \<in> P \<triangle>\<^sub>T Q"
  proof auto
    assume "\<sigma> = []"
    then show "\<rho> @ [[X \<union> Y]\<^sub>R] \<in> P \<triangle>\<^sub>T Q"
      using TT1_P TT1_Q TT2_P TT2_Q TT2_TimeSyncInterrupt TT2_def TT3_P TT3_Q P_wf assm1 assm2 by blast
  next
    fix \<sigma>'
    assume case_assm: "\<sigma> = [Tock]\<^sub>E # \<sigma>'"
    have "(\<exists> \<sigma>'' q1 q2. \<sigma>' = \<sigma>'' @ [[Tick]\<^sub>E] \<and> \<rho> @ [X]\<^sub>R # [Tock]\<^sub>E # \<sigma>' \<in> P \<and> q1 @ [X]\<^sub>R # [Tock]\<^sub>E # q2 \<in> Q
        \<and> filter_tocks \<rho> = q1 \<and> filter_tocks \<sigma>'' = q2)
      \<or> (\<exists> \<sigma>'' q1 q2 Y Z W. \<sigma>' = \<sigma>'' @ [[W]\<^sub>R] \<and> \<rho> @ [X]\<^sub>R # [Tock]\<^sub>E # \<sigma>'' @ [[Y]\<^sub>R] \<in> P \<and> q1 @ [X]\<^sub>R # [Tock]\<^sub>E # q2 @ [[Z]\<^sub>R] \<in> Q
        \<and> filter_tocks \<rho> = q1 \<and> filter_tocks \<sigma>'' = q2 \<and> W \<subseteq> Y \<union> Z \<and> {e \<in> Y. e \<noteq> Tock} = {e \<in> Z. e \<noteq> Tock})
      \<or> (\<exists> p2 q1 q2 q3. \<sigma>' = p2 @ q3 \<and> \<rho> @ [X]\<^sub>R # [Tock]\<^sub>E # p2 \<in> P \<and> filter_tocks \<rho> = q1 \<and> filter_tocks p2 = q2 \<and> (\<nexists> Ya q'. q3 = [Ya]\<^sub>R # q')
        \<and> q1 @ [X]\<^sub>R # [Tock]\<^sub>E # q2 @ q3 \<in> Q \<and> (\<nexists>p'. \<rho> @ [X]\<^sub>R # [Tock]\<^sub>E # p2 = p' @ [[Tick]\<^sub>E]) \<and> (\<nexists>p' Y. \<rho> @ [X]\<^sub>R # [Tock]\<^sub>E # p2 = p' @ [[Y]\<^sub>R]))
      \<or> (\<exists> p q1 q2. \<rho> = p @ q2 \<and> p \<in> P \<and> filter_tocks p = q1 \<and> q1 @ q2 @ [X]\<^sub>R # [Tock]\<^sub>E # \<sigma>' \<in> Q \<and> (\<nexists> Ya q'. q2 = [Ya]\<^sub>R # q') \<and> q2 \<noteq> []
        \<and> (\<nexists>p'. p = p' @ [[Tick]\<^sub>E]) \<and> (\<nexists>p' Y. p = p' @ [[Y]\<^sub>R]))"
      using assm1 case_assm unfolding TimeSyncInterruptTTT_def
    proof (safe, simp_all)
      fix p
      assume case_assms2: "p @ [[Tick]\<^sub>E] \<in> P" "filter_tocks p \<in> Q" "\<rho> @ [X]\<^sub>R # [Tock]\<^sub>E # \<sigma>' = p @ [[Tick]\<^sub>E]" "\<sigma> = [Tock]\<^sub>E # \<sigma>'"
      obtain \<sigma>'' where 1: "p = \<rho> @ [X]\<^sub>R # [Tock]\<^sub>E # \<sigma>''"
        by (metis butlast.simps(2) butlast_append butlast_snoc case_assms2(3) ttWF.simps(3) ttWF.simps(6) last.simps last_appendR list.distinct(1))
      have 2: "filter_tocks (\<rho> @ [X]\<^sub>R # [Tock]\<^sub>E # \<sigma>'') = filter_tocks \<rho> @ filter_tocks ([X]\<^sub>R # [Tock]\<^sub>E # \<sigma>'')"
          by (induct \<rho> rule:filter_tocks.induct, auto)
      show "\<forall>\<sigma>''. \<sigma>' = \<sigma>'' @ [[Tick]\<^sub>E] \<longrightarrow> filter_tocks \<rho> @ [X]\<^sub>R # [Tock]\<^sub>E # filter_tocks \<sigma>'' \<notin> Q \<Longrightarrow>
        \<exists>p2 q3. \<sigma>' = p2 @ q3 \<and> \<rho> @ [X]\<^sub>R # [Tock]\<^sub>E # p2 \<in> P \<and> (\<forall>Ya q'. q3 \<noteq> [Ya]\<^sub>R # q') \<and> filter_tocks \<rho> @ [X]\<^sub>R # [Tock]\<^sub>E # filter_tocks p2 @ q3 \<in> Q \<and>
          (\<forall>p'. \<rho> @ [X]\<^sub>R # [Tock]\<^sub>E # p2 \<noteq> p' @ [[Tick]\<^sub>E]) \<and> (\<forall>p' Y. \<rho> @ [X]\<^sub>R # [Tock]\<^sub>E # p2 \<noteq> p' @ [[Y]\<^sub>R])"
        using 1 2 case_assms2 by (erule_tac x="\<sigma>''" in allE, auto)
    next
      fix p Xa Y Z
      assume case_assms2: "p @ [[Xa]\<^sub>R] \<in> P" "filter_tocks p @ [[Y]\<^sub>R] \<in> Q" "Z \<subseteq> Xa \<union> Y" "{e \<in> Xa. e \<noteq> Tock} = {e \<in> Y. e \<noteq> Tock}"
        "\<rho> @ [X]\<^sub>R # [Tock]\<^sub>E # \<sigma>' = p @ [[Z]\<^sub>R]" "\<sigma> = [Tock]\<^sub>E # \<sigma>'"
      obtain \<sigma>'' where 1: "\<sigma>' = \<sigma>'' @ [[Z]\<^sub>R]"
        by (metis append_butlast_last_id case_assms2(5) cttobs.distinct(1) last.simps last_appendR list.simps(3))
      have 2: "filter_tocks (\<rho> @ [X]\<^sub>R # [Tock]\<^sub>E # \<sigma>'') = filter_tocks \<rho> @ [X]\<^sub>R # [Tock]\<^sub>E # filter_tocks \<sigma>''"
        by (induct \<rho> rule:filter_tocks.induct, auto)
      show "\<forall>\<sigma>'' Y Z W. W \<subseteq> Y \<union> Z \<longrightarrow> filter_tocks \<rho> @ [X]\<^sub>R # [Tock]\<^sub>E # filter_tocks \<sigma>'' @ [[Z]\<^sub>R] \<in> Q \<longrightarrow>
          \<rho> @ [X]\<^sub>R # [Tock]\<^sub>E # \<sigma>'' @ [[Y]\<^sub>R] \<in> P \<longrightarrow> \<sigma>' = \<sigma>'' @ [[W]\<^sub>R] \<longrightarrow> {e \<in> Y. e \<noteq> Tock} \<noteq> {e \<in> Z. e \<noteq> Tock} \<Longrightarrow>
        \<exists>p2 q3. \<sigma>' = p2 @ q3 \<and> \<rho> @ [X]\<^sub>R # [Tock]\<^sub>E # p2 \<in> P \<and> (\<forall>Ya q'. q3 \<noteq> [Ya]\<^sub>R # q') \<and> filter_tocks \<rho> @ [X]\<^sub>R # [Tock]\<^sub>E # filter_tocks p2 @ q3 \<in> Q \<and>
          (\<forall>p'. \<rho> @ [X]\<^sub>R # [Tock]\<^sub>E # p2 \<noteq> p' @ [[Tick]\<^sub>E]) \<and> (\<forall>p' Y. \<rho> @ [X]\<^sub>R # [Tock]\<^sub>E # p2 \<noteq> p' @ [[Y]\<^sub>R])"
        using 1 2 case_assms2 by auto
    next
      fix p q2
      assume case_assms2: "p \<in> P" "\<forall>p'. p \<noteq> p' @ [[Tick]\<^sub>E]" "\<forall>p' Y. p \<noteq> p' @ [[Y]\<^sub>R]" "filter_tocks p @ q2 \<in> Q"
        "\<forall>q' Y. q2 \<noteq> [Y]\<^sub>R # q'" "\<rho> @ [X]\<^sub>R # [Tock]\<^sub>E # \<sigma>' = p @ q2" "\<sigma> = [Tock]\<^sub>E # \<sigma>'"
      have "(\<exists> p2. p = \<rho> @ [X]\<^sub>R # [Tock]\<^sub>E # p2 \<and> \<sigma>' = p2 @ q2)
        \<or> (\<exists> q21 q22. \<rho> = p @ q21 \<and> q2 = q21 @ [X]\<^sub>R # [Tock]\<^sub>E # q22)"
        using case_assms2(6) by (induct \<rho> p rule:ctt_subset.induct, auto, metis Cons_eq_append_conv case_assms2(3))
      then show "\<forall>p q2. filter_tocks p @ q2 @ [X]\<^sub>R # [Tock]\<^sub>E # \<sigma>' \<in> Q \<longrightarrow>
          p \<in> P \<longrightarrow> \<rho> = p @ q2 \<longrightarrow> (\<exists>Ya q'. q2 = [Ya]\<^sub>R # q') \<or> q2 = [] \<or> (\<exists>p'. p = p' @ [[Tick]\<^sub>E]) \<or> (\<exists>p' Y. p = p' @ [[Y]\<^sub>R]) \<Longrightarrow>
        \<exists>p2 q3. \<sigma>' = p2 @ q3 \<and> \<rho> @ [X]\<^sub>R # [Tock]\<^sub>E # p2 \<in> P \<and> (\<forall>Ya q'. q3 \<noteq> [Ya]\<^sub>R # q') \<and> filter_tocks \<rho> @ [X]\<^sub>R # [Tock]\<^sub>E # filter_tocks p2 @ q3 \<in> Q \<and>
          (\<forall>p'. \<rho> @ [X]\<^sub>R # [Tock]\<^sub>E # p2 \<noteq> p' @ [[Tick]\<^sub>E]) \<and> (\<forall>p' Y. \<rho> @ [X]\<^sub>R # [Tock]\<^sub>E # p2 \<noteq> p' @ [[Y]\<^sub>R])"
      proof auto
        fix p2
        assume case_assms3: "p = \<rho> @ [X]\<^sub>R # [Tock]\<^sub>E # p2" "\<sigma>' = p2 @ q2"
        have 1: "filter_tocks (\<rho> @ [X]\<^sub>R # [Tock]\<^sub>E # p2) = filter_tocks \<rho> @ filter_tocks ([X]\<^sub>R # [Tock]\<^sub>E # p2)"
            by (induct \<rho> rule:filter_tocks.induct, auto)
        show "\<exists>p2a q3. p2 @ q2 = p2a @ q3 \<and> \<rho> @ [X]\<^sub>R # [Tock]\<^sub>E # p2a \<in> P \<and> (\<forall>Ya q'. q3 \<noteq> [Ya]\<^sub>R # q') \<and> filter_tocks \<rho> @ [X]\<^sub>R # [Tock]\<^sub>E # filter_tocks p2a @ q3 \<in> Q \<and>
          (\<forall>p'. \<rho> @ [X]\<^sub>R # [Tock]\<^sub>E # p2a \<noteq> p' @ [[Tick]\<^sub>E]) \<and> (\<forall>p' Y. \<rho> @ [X]\<^sub>R # [Tock]\<^sub>E # p2a \<noteq> p' @ [[Y]\<^sub>R])"
          using case_assms2 case_assms3 1 by auto
      next
        fix q21 q22
        assume case_assms3: "\<rho> = p @ q21" "q2 = q21 @ [X]\<^sub>R # [Tock]\<^sub>E # q22"
        have 1: "filter_tocks p @ q21 @ [X]\<^sub>R # [Tock]\<^sub>E # q22 \<in> Q"
          using case_assms2(4) case_assms3(2) by blast
        have 2: "(\<nexists>p'. q21 = p' @ [[Tick]\<^sub>E]) \<and> (\<nexists>p' Y. q21 = p' @ [[Y]\<^sub>R])"
        proof auto
          fix p'
          assume "q21 = p' @ [[Tick]\<^sub>E]"
          then have "filter_tocks p @ p' @ [Tick]\<^sub>E # [X]\<^sub>R # [Tock]\<^sub>E # q22 \<in> Q"
            using 1 case_assms3 by auto
          then have "ttWF (filter_tocks p @ p' @ [Tick]\<^sub>E # [X]\<^sub>R # [Tock]\<^sub>E # q22)"
            using Q_wf by blast
          then have "ttWF (p' @ [Tick]\<^sub>E # [X]\<^sub>R # [Tock]\<^sub>E # q22)"
            by (induct p rule:filter_tocks.induct, auto)
          then show "False"
            by (induct p' rule:ttWF.induct, auto)
        next
          fix p' Y
          assume "q21 = p' @ [[Y]\<^sub>R]"
          then have "filter_tocks p @ p' @ [Y]\<^sub>R # [X]\<^sub>R # [Tock]\<^sub>E # q22 \<in> Q"
            using 1 case_assms3 by auto
          then have "ttWF (filter_tocks p @ p' @ [Y]\<^sub>R # [X]\<^sub>R # [Tock]\<^sub>E # q22)"
            using Q_wf by blast
          then have "ttWF (p' @ [Y]\<^sub>R # [X]\<^sub>R # [Tock]\<^sub>E # q22)"
            by (induct p rule:filter_tocks.induct, auto)
          then show "False"
            by (induct p' rule:ttWF.induct, auto)
        qed
        show "\<forall>pa q2. filter_tocks pa @ q2 @ [X]\<^sub>R # [Tock]\<^sub>E # \<sigma>' \<in> Q \<longrightarrow> pa \<in> P \<longrightarrow>
            p @ q21 = pa @ q2 \<longrightarrow> (\<exists>Ya q'. q2 = [Ya]\<^sub>R # q') \<or> q2 = [] \<or> (\<exists>p'. pa = p' @ [[Tick]\<^sub>E]) \<or> (\<exists>p' Y. pa = p' @ [[Y]\<^sub>R]) \<Longrightarrow>
          \<exists>p2 q3. \<sigma>' = p2 @ q3 \<and> p @ q21 @ [X]\<^sub>R # [Tock]\<^sub>E # p2 \<in> P \<and> (\<forall>Ya q'. q3 \<noteq> [Ya]\<^sub>R # q') \<and> filter_tocks (p @ q21) @ [X]\<^sub>R # [Tock]\<^sub>E # filter_tocks p2 @ q3 \<in> Q \<and>
            (\<forall>p'. p @ q21 @ [X]\<^sub>R # [Tock]\<^sub>E # p2 \<noteq> p' @ [[Tick]\<^sub>E]) \<and> (\<forall>p' Y. p @ q21 @ [X]\<^sub>R # [Tock]\<^sub>E # p2 \<noteq> p' @ [[Y]\<^sub>R])"
          using 1 case_assms2 case_assms3 by (erule_tac x="p" in allE, auto)
      qed
    qed
    then show "\<rho> @ [X \<union> Y]\<^sub>R # [Tock]\<^sub>E # \<sigma>' \<in> P \<triangle>\<^sub>T Q"
    proof (safe)
      fix \<sigma>''
      assume case_assms2: "\<sigma>' = \<sigma>'' @ [[Tick]\<^sub>E]" "\<rho> @ [X]\<^sub>R # [Tock]\<^sub>E # \<sigma>'' @ [[Tick]\<^sub>E] \<in> P" "filter_tocks \<rho> @ [X]\<^sub>R # [Tock]\<^sub>E # filter_tocks \<sigma>'' \<in> Q"
      have 1: "(\<nexists>p'. \<rho> = p' @ [[Tick]\<^sub>E]) \<and> (\<nexists>p' Y. \<rho> = p' @ [[Y]\<^sub>R])"
      proof auto
        fix p'
        assume "\<rho> = p' @ [[Tick]\<^sub>E]"
        then have "p' @ [Tick]\<^sub>E # [X]\<^sub>R # [Tock]\<^sub>E # \<sigma>'' @ [[Tick]\<^sub>E] \<in> P"
          using case_assms2 by auto
        then have "ttWF (p' @ [Tick]\<^sub>E # [X]\<^sub>R # [Tock]\<^sub>E # \<sigma>'' @ [[Tick]\<^sub>E])"
          using P_wf by blast
        then show False
          by (induct p' rule:ttWF.induct, auto)
      next
        fix p' Y
        assume "\<rho> = p' @ [[Y]\<^sub>R]"
        then have "p' @ [Y]\<^sub>R # [X]\<^sub>R # [Tock]\<^sub>E # \<sigma>'' @ [[Tick]\<^sub>E] \<in> P"
          using case_assms2 by auto
        then have "ttWF (p' @ [Y]\<^sub>R # [X]\<^sub>R # [Tock]\<^sub>E # \<sigma>'' @ [[Tick]\<^sub>E])"
          using P_wf by blast
        then show False
          by (induct p' rule:ttWF.induct, auto)
      qed
      have 2: "\<rho> \<in> P"
        using TT1_P TT1_def case_assms2(2) ctt_prefix_concat ctt_prefix_imp_prefix_subset by blast
      have 3: "\<rho> @ [[X]\<^sub>R, [Tock]\<^sub>E] \<in> P"
        using TT1_P case_assms2(2) ctt_prefix_subset_same_front unfolding TT1_def by fastforce
      have "{e. e \<noteq> Tock \<and> \<rho> @ [[e]\<^sub>E] \<in> P \<or> e = Tock \<and> \<rho> @ [[X]\<^sub>R, [e]\<^sub>E] \<in> P}
        \<subseteq> {e. e \<noteq> Tock \<and> \<rho> @ [[e]\<^sub>E] \<in> P \<triangle>\<^sub>T Q \<or> e = Tock \<and> \<rho> @ [[X]\<^sub>R, [e]\<^sub>E] \<in> P \<triangle>\<^sub>T Q}"
      proof auto
        fix x
        assume case_assms3:  "\<rho> @ [[x]\<^sub>E] \<in> P" "x \<noteq> Tock"
        have "filter_tocks (\<rho> @ [X]\<^sub>R # [Tock]\<^sub>E # \<sigma>'') = filter_tocks \<rho> @ filter_tocks ([X]\<^sub>R # [Tock]\<^sub>E # \<sigma>'')"
          by (induct \<rho> rule:filter_tocks.induct, auto)
        then have "filter_tocks \<rho> @ filter_tocks ([X]\<^sub>R # [Tock]\<^sub>E # \<sigma>'') \<in> Q"
          using case_assms2(3) by auto
        then have 1: "filter_tocks \<rho> \<in> Q"
          using TT1_Q TT1_def ctt_prefix_concat ctt_prefix_imp_prefix_subset by blast
        show "\<rho> @ [[x]\<^sub>E] \<in> P \<triangle>\<^sub>T Q"
          using case_assms3 unfolding TimeSyncInterruptTTT_def
        proof (cases x, auto)
          fix x1
          assume case_assms4: "\<rho> @ [[Event x1]\<^sub>E] \<in> P" "x = Event x1"
          show "\<exists>p. p \<in> P \<and> (\<forall>p'. p \<noteq> p' @ [[Tick]\<^sub>E]) \<and> (\<forall>p' Y. p \<noteq> p' @ [[Y]\<^sub>R]) \<and>
            (\<exists>q2. filter_tocks p @ q2 \<in> Q \<and> (\<forall>q' Y. q2 \<noteq> [Y]\<^sub>R # q') \<and> \<rho> @ [[Event x1]\<^sub>E] = p @ q2)"
            using 1 case_assms4 by (rule_tac x="\<rho> @ [[Event x1]\<^sub>E]" in exI, auto simp add: filter_tocks_end_event)
        next
          show "filter_tocks \<rho> \<in> Q"
            using 1 by auto
        qed
      next
        fix x
        assume case_assms3:  "\<rho> @ [[x]\<^sub>E] \<in> P" "x \<noteq> Tock"
        have "filter_tocks (\<rho> @ [X]\<^sub>R # [Tock]\<^sub>E # \<sigma>'') = filter_tocks \<rho> @ filter_tocks ([X]\<^sub>R # [Tock]\<^sub>E # \<sigma>'')"
          by (induct \<rho> rule:filter_tocks.induct, auto)
        then have "filter_tocks \<rho> @ filter_tocks ([X]\<^sub>R # [Tock]\<^sub>E # \<sigma>'') \<in> Q"
          using case_assms2(3) by auto
        then have 1: "filter_tocks \<rho> \<in> Q"
          using TT1_Q TT1_def ctt_prefix_concat ctt_prefix_imp_prefix_subset by blast
        show "\<rho> @ [[x]\<^sub>E] \<in> P \<triangle>\<^sub>T Q"
          using case_assms3 unfolding TimeSyncInterruptTTT_def
        proof (cases x, auto)
          fix x1
          assume case_assms4: "\<rho> @ [[Event x1]\<^sub>E] \<in> P" "x = Event x1"
          show "\<exists>p. p \<in> P \<and> (\<forall>p'. p \<noteq> p' @ [[Tick]\<^sub>E]) \<and> (\<forall>p' Y. p \<noteq> p' @ [[Y]\<^sub>R]) \<and>
            (\<exists>q2. filter_tocks p @ q2 \<in> Q \<and> (\<forall>q' Y. q2 \<noteq> [Y]\<^sub>R # q') \<and> \<rho> @ [[Event x1]\<^sub>E] = p @ q2)"
            using 1 case_assms4 by (rule_tac x="\<rho> @ [[Event x1]\<^sub>E]" in exI, auto simp add: filter_tocks_end_event)
        next
          show "filter_tocks \<rho> \<in> Q"
            using 1 by auto
        qed
      next
        assume case_assms3: "\<rho> @ [[X]\<^sub>R, [Tock]\<^sub>E] \<in> P"
        have "filter_tocks (\<rho> @ [X]\<^sub>R # [Tock]\<^sub>E # \<sigma>'') = filter_tocks \<rho> @ filter_tocks ([X]\<^sub>R # [Tock]\<^sub>E # \<sigma>'')"
          by (induct \<rho> rule:filter_tocks.induct, auto)
        then have "filter_tocks \<rho> @ filter_tocks ([X]\<^sub>R # [Tock]\<^sub>E # \<sigma>'') \<in> Q"
          using case_assms2(3) by auto
        then have "filter_tocks \<rho> @ [[X]\<^sub>R, [Tock]\<^sub>E] \<in> Q"
          using TT1_Q unfolding TT1_def apply auto
          by (meson ctt_prefix_subset.simps(1) ctt_prefix_subset.simps(2) ctt_prefix_subset.simps(3) ctt_prefix_subset_same_front subsetI) 
        then show "\<rho> @ [[X]\<^sub>R, [Tock]\<^sub>E] \<notin> P \<triangle>\<^sub>T Q \<Longrightarrow> False"
          unfolding TimeSyncInterruptTTT_def apply (auto)
          apply (erule_tac x="\<rho> @ [[X]\<^sub>R, [Tock]\<^sub>E]" in allE, auto simp add: case_assms3)
          by (erule_tac x="[]" in allE, auto simp add: filter_tocks_end_ref_tock)
      next
        assume case_assms3: "\<rho> @ [[X]\<^sub>R, [Tock]\<^sub>E] \<in> P"
        have "filter_tocks (\<rho> @ [X]\<^sub>R # [Tock]\<^sub>E # \<sigma>'') = filter_tocks \<rho> @ filter_tocks ([X]\<^sub>R # [Tock]\<^sub>E # \<sigma>'')"
          by (induct \<rho> rule:filter_tocks.induct, auto)
        then have "filter_tocks \<rho> @ filter_tocks ([X]\<^sub>R # [Tock]\<^sub>E # \<sigma>'') \<in> Q"
          using case_assms2(3) by auto
        then have "filter_tocks \<rho> @ [[X]\<^sub>R, [Tock]\<^sub>E] \<in> Q"
          using TT1_Q unfolding TT1_def apply auto
          by (meson ctt_prefix_subset.simps(1) ctt_prefix_subset.simps(2) ctt_prefix_subset.simps(3) ctt_prefix_subset_same_front subsetI) 
        then show "\<rho> @ [[X]\<^sub>R, [Tock]\<^sub>E] \<notin> P \<triangle>\<^sub>T Q \<Longrightarrow> \<rho> @ [[Tock]\<^sub>E] \<in> P \<triangle>\<^sub>T Q"
          unfolding TimeSyncInterruptTTT_def apply (auto)
          apply (erule_tac x="\<rho> @ [[X]\<^sub>R, [Tock]\<^sub>E]" in allE, auto simp add: case_assms3)
          by (erule_tac x="[]" in allE, auto simp add: filter_tocks_end_ref_tock)
      qed
      then have 4: "Y \<inter> {e. e \<noteq> Tock \<and> \<rho> @ [[e]\<^sub>E] \<in> P \<or> e = Tock \<and> \<rho> @ [[X]\<^sub>R, [e]\<^sub>E] \<in> P} = {}"
        using assm2 by auto
      have "{e. e \<noteq> Tock \<and> filter_tocks \<rho> @ [[e]\<^sub>E] \<in> Q \<or> e = Tock \<and> filter_tocks \<rho> @ [[X]\<^sub>R, [e]\<^sub>E] \<in> Q}
        \<subseteq> {e. e \<noteq> Tock \<and> \<rho> @ [[e]\<^sub>E] \<in> P \<triangle>\<^sub>T Q \<or> e = Tock \<and> \<rho> @ [[X]\<^sub>R, [e]\<^sub>E] \<in> P \<triangle>\<^sub>T Q}"
      proof auto
        fix x
        assume case_assms3: "filter_tocks \<rho> @ [[x]\<^sub>E] \<in> Q" "x \<noteq> Tock"
        show "\<rho> @ [[x]\<^sub>E] \<in> P \<triangle>\<^sub>T Q"
          unfolding TimeSyncInterruptTTT_def using 1 2 case_assms3 by auto
      next
        fix x
        assume case_assms3: "filter_tocks \<rho> @ [[x]\<^sub>E] \<in> Q" "x \<noteq> Tock"
        show "\<rho> @ [[x]\<^sub>E] \<in> P \<triangle>\<^sub>T Q"
          unfolding TimeSyncInterruptTTT_def using 1 2 case_assms3 by auto
      next
        assume case_assms3: "filter_tocks \<rho> @ [[X]\<^sub>R, [Tock]\<^sub>E] \<in> Q"
        show "\<rho> @ [[X]\<^sub>R, [Tock]\<^sub>E] \<notin> P \<triangle>\<^sub>T Q \<Longrightarrow> False"
          unfolding TimeSyncInterruptTTT_def case_assms3 filter_tocks_end_ref_tock 1 2 3 apply auto
          apply (erule_tac x="\<rho> @ [[X]\<^sub>R, [Tock]\<^sub>E]" in allE, auto simp add: 1 2 3)
          by (erule_tac x="[]" in allE, auto simp add: case_assms3 filter_tocks_end_ref_tock)
      next
        assume case_assms3: "filter_tocks \<rho> @ [[X]\<^sub>R, [Tock]\<^sub>E] \<in> Q"
        show "\<rho> @ [[X]\<^sub>R, [Tock]\<^sub>E] \<notin> P \<triangle>\<^sub>T Q \<Longrightarrow> \<rho> @ [[Tock]\<^sub>E] \<in> P \<triangle>\<^sub>T Q"
          unfolding TimeSyncInterruptTTT_def case_assms3 filter_tocks_end_ref_tock 1 2 3 apply auto
          apply (erule_tac x="\<rho> @ [[X]\<^sub>R, [Tock]\<^sub>E]" in allE, auto simp add: 1 2 3)
          by (erule_tac x="[]" in allE, auto simp add: case_assms3 filter_tocks_end_ref_tock)
      qed
      then have 5: "Y \<inter> {e. e \<noteq> Tock \<and> filter_tocks \<rho> @ [[e]\<^sub>E] \<in> Q \<or> e = Tock \<and> filter_tocks \<rho> @ [[X]\<^sub>R, [e]\<^sub>E] \<in> Q} = {}"
        using assm2 by auto
      have 6: "\<rho> @ [X \<union> Y]\<^sub>R # [Tock]\<^sub>E # \<sigma>'' @ [[Tick]\<^sub>E] \<in> P"
        using TT2s_P case_assms2 4 unfolding TT2s_def by auto
      have 7: "filter_tocks \<rho> @ [X \<union> Y]\<^sub>R # [Tock]\<^sub>E # filter_tocks \<sigma>'' \<in> Q"
        using TT2s_Q case_assms2 5 unfolding TT2s_def by auto
      have 8: "filter_tocks (\<rho> @ [X \<union> Y]\<^sub>R # [Tock]\<^sub>E # \<sigma>'') = filter_tocks \<rho> @ [X \<union> Y]\<^sub>R # [Tock]\<^sub>E # filter_tocks \<sigma>''"
        by (induct \<rho> rule:filter_tocks.induct, auto)
      show "\<rho> @ [X \<union> Y]\<^sub>R # [Tock]\<^sub>E # \<sigma>'' @ [[Tick]\<^sub>E] \<in> P \<triangle>\<^sub>T Q"
        unfolding TimeSyncInterruptTTT_def using 6 7 8 by auto
    next
      fix \<sigma>'' Ya Z W
      assume case_assms2: "\<sigma>' = \<sigma>'' @ [[W]\<^sub>R]" "\<rho> @ [X]\<^sub>R # [Tock]\<^sub>E # \<sigma>'' @ [[Ya]\<^sub>R] \<in> P"
        "filter_tocks \<rho> @ [X]\<^sub>R # [Tock]\<^sub>E # filter_tocks \<sigma>'' @ [[Z]\<^sub>R] \<in> Q" "W \<subseteq> Ya \<union> Z" "{e \<in> Ya. e \<noteq> Tock} = {e \<in> Z. e \<noteq> Tock}"
      have 1: "(\<nexists>p'. \<rho> = p' @ [[Tick]\<^sub>E]) \<and> (\<nexists>p' Y. \<rho> = p' @ [[Y]\<^sub>R])"
      proof auto
        fix p'
        assume "\<rho> = p' @ [[Tick]\<^sub>E]"
        then have "p' @ [Tick]\<^sub>E # [X]\<^sub>R # [Tock]\<^sub>E # \<sigma>'' @ [[Ya]\<^sub>R] \<in> P"
          using case_assms2 by auto
        then have "ttWF (p' @ [Tick]\<^sub>E # [X]\<^sub>R # [Tock]\<^sub>E # \<sigma>'' @ [[Ya]\<^sub>R])"
          using P_wf by blast
        then show False
          by (induct p' rule:ttWF.induct, auto)
      next
        fix p' Y
        assume "\<rho> = p' @ [[Y]\<^sub>R]"
        then have "p' @ [Y]\<^sub>R # [X]\<^sub>R # [Tock]\<^sub>E # \<sigma>'' @ [[Ya]\<^sub>R] \<in> P"
          using case_assms2 by auto
        then have "ttWF (p' @ [Y]\<^sub>R # [X]\<^sub>R # [Tock]\<^sub>E # \<sigma>'' @ [[Ya]\<^sub>R])"
          using P_wf by blast
        then show False
          by (induct p' rule:ttWF.induct, auto)
      qed
      have 2: "\<rho> \<in> P"
        using TT1_P TT1_def case_assms2(2) ctt_prefix_concat ctt_prefix_imp_prefix_subset by blast
      have 3: "\<rho> @ [[X]\<^sub>R, [Tock]\<^sub>E] \<in> P"
        using TT1_P case_assms2(2) ctt_prefix_subset_same_front unfolding TT1_def by fastforce
      have "{e. e \<noteq> Tock \<and> \<rho> @ [[e]\<^sub>E] \<in> P \<or> e = Tock \<and> \<rho> @ [[X]\<^sub>R, [e]\<^sub>E] \<in> P}
        \<subseteq> {e. e \<noteq> Tock \<and> \<rho> @ [[e]\<^sub>E] \<in> P \<triangle>\<^sub>T Q \<or> e = Tock \<and> \<rho> @ [[X]\<^sub>R, [e]\<^sub>E] \<in> P \<triangle>\<^sub>T Q}"
      proof auto
        fix x
        assume case_assms3:  "\<rho> @ [[x]\<^sub>E] \<in> P" "x \<noteq> Tock"
        have "filter_tocks (\<rho> @ [X]\<^sub>R # [Tock]\<^sub>E # \<sigma>'') = filter_tocks \<rho> @ filter_tocks ([X]\<^sub>R # [Tock]\<^sub>E # \<sigma>'')"
          by (induct \<rho> rule:filter_tocks.induct, auto)
        then have "filter_tocks \<rho> @ filter_tocks ([X]\<^sub>R # [Tock]\<^sub>E # \<sigma>'') @ [[Z]\<^sub>R] \<in> Q"
          using case_assms2 by auto
        then have 1: "filter_tocks \<rho> \<in> Q"
          using TT1_Q TT1_def ctt_prefix_concat ctt_prefix_imp_prefix_subset by blast
        show "\<rho> @ [[x]\<^sub>E] \<in> P \<triangle>\<^sub>T Q"
          using case_assms3 unfolding TimeSyncInterruptTTT_def
        proof (cases x, auto)
          fix x1
          assume case_assms4: "\<rho> @ [[Event x1]\<^sub>E] \<in> P" "x = Event x1"
          show "\<exists>p. p \<in> P \<and> (\<forall>p'. p \<noteq> p' @ [[Tick]\<^sub>E]) \<and> (\<forall>p' Y. p \<noteq> p' @ [[Y]\<^sub>R]) \<and>
            (\<exists>q2. filter_tocks p @ q2 \<in> Q \<and> (\<forall>q' Y. q2 \<noteq> [Y]\<^sub>R # q') \<and> \<rho> @ [[Event x1]\<^sub>E] = p @ q2)"
            using 1 case_assms4 by (rule_tac x="\<rho> @ [[Event x1]\<^sub>E]" in exI, auto simp add: filter_tocks_end_event)
        next
          show "filter_tocks \<rho> \<in> Q"
            using 1 by auto
        qed
      next
        fix x
        assume case_assms3:  "\<rho> @ [[x]\<^sub>E] \<in> P" "x \<noteq> Tock"
        have "filter_tocks (\<rho> @ [X]\<^sub>R # [Tock]\<^sub>E # \<sigma>'') = filter_tocks \<rho> @ filter_tocks ([X]\<^sub>R # [Tock]\<^sub>E # \<sigma>'')"
          by (induct \<rho> rule:filter_tocks.induct, auto)
        then have "filter_tocks \<rho> @ filter_tocks ([X]\<^sub>R # [Tock]\<^sub>E # \<sigma>'') @ [[Z]\<^sub>R] \<in> Q"
          using case_assms2 by auto
        then have 1: "filter_tocks \<rho> \<in> Q"
          using TT1_Q TT1_def ctt_prefix_concat ctt_prefix_imp_prefix_subset by blast
        show "\<rho> @ [[x]\<^sub>E] \<in> P \<triangle>\<^sub>T Q"
          using case_assms3 unfolding TimeSyncInterruptTTT_def
        proof (cases x, auto)
          fix x1
          assume case_assms4: "\<rho> @ [[Event x1]\<^sub>E] \<in> P" "x = Event x1"
          show "\<exists>p. p \<in> P \<and> (\<forall>p'. p \<noteq> p' @ [[Tick]\<^sub>E]) \<and> (\<forall>p' Y. p \<noteq> p' @ [[Y]\<^sub>R]) \<and>
            (\<exists>q2. filter_tocks p @ q2 \<in> Q \<and> (\<forall>q' Y. q2 \<noteq> [Y]\<^sub>R # q') \<and> \<rho> @ [[Event x1]\<^sub>E] = p @ q2)"
            using 1 case_assms4 by (rule_tac x="\<rho> @ [[Event x1]\<^sub>E]" in exI, auto simp add: filter_tocks_end_event)
        next
          show "filter_tocks \<rho> \<in> Q"
            using 1 by auto
        qed
      next
        assume case_assms3: "\<rho> @ [[X]\<^sub>R, [Tock]\<^sub>E] \<in> P"
        have "filter_tocks (\<rho> @ [X]\<^sub>R # [Tock]\<^sub>E # \<sigma>'') = filter_tocks \<rho> @ filter_tocks ([X]\<^sub>R # [Tock]\<^sub>E # \<sigma>'')"
          by (induct \<rho> rule:filter_tocks.induct, auto)
        then have "filter_tocks \<rho> @ filter_tocks ([X]\<^sub>R # [Tock]\<^sub>E # \<sigma>'') @ [[Z]\<^sub>R] \<in> Q"
          using case_assms2(3) case_assms2(4) by auto
        then have "filter_tocks \<rho> @ [[X]\<^sub>R, [Tock]\<^sub>E] \<in> Q"
          using TT1_Q unfolding TT1_def apply auto
          by (meson ctt_prefix_subset.simps(1) ctt_prefix_subset.simps(2) ctt_prefix_subset.simps(3) ctt_prefix_subset_same_front subsetI) 
        then show "\<rho> @ [[X]\<^sub>R, [Tock]\<^sub>E] \<notin> P \<triangle>\<^sub>T Q \<Longrightarrow> False"
          unfolding TimeSyncInterruptTTT_def apply (auto)
          apply (erule_tac x="\<rho> @ [[X]\<^sub>R, [Tock]\<^sub>E]" in allE, auto simp add: case_assms3)
          by (erule_tac x="[]" in allE, auto simp add: filter_tocks_end_ref_tock)
      next
        assume case_assms3: "\<rho> @ [[X]\<^sub>R, [Tock]\<^sub>E] \<in> P"
        have "filter_tocks (\<rho> @ [X]\<^sub>R # [Tock]\<^sub>E # \<sigma>'') = filter_tocks \<rho> @ filter_tocks ([X]\<^sub>R # [Tock]\<^sub>E # \<sigma>'')"
          by (induct \<rho> rule:filter_tocks.induct, auto)
        then have "filter_tocks \<rho> @ filter_tocks ([X]\<^sub>R # [Tock]\<^sub>E # \<sigma>'') @ [[Z]\<^sub>R] \<in> Q"
          using case_assms2(3) case_assms2(4) by auto
        then have "filter_tocks \<rho> @ [[X]\<^sub>R, [Tock]\<^sub>E] \<in> Q"
          using TT1_Q unfolding TT1_def apply auto
          by (meson ctt_prefix_subset.simps(1) ctt_prefix_subset.simps(2) ctt_prefix_subset.simps(3) ctt_prefix_subset_same_front subsetI) 
        then show "\<rho> @ [[X]\<^sub>R, [Tock]\<^sub>E] \<notin> P \<triangle>\<^sub>T Q \<Longrightarrow> \<rho> @ [[Tock]\<^sub>E] \<in> P \<triangle>\<^sub>T Q"
          unfolding TimeSyncInterruptTTT_def apply (auto)
          apply (erule_tac x="\<rho> @ [[X]\<^sub>R, [Tock]\<^sub>E]" in allE, auto simp add: case_assms3)
          by (erule_tac x="[]" in allE, auto simp add: filter_tocks_end_ref_tock)
      qed
      then have 4: "Y \<inter> {e. e \<noteq> Tock \<and> \<rho> @ [[e]\<^sub>E] \<in> P \<or> e = Tock \<and> \<rho> @ [[X]\<^sub>R, [e]\<^sub>E] \<in> P} = {}"
        using assm2 by auto
      have "{e. e \<noteq> Tock \<and> filter_tocks \<rho> @ [[e]\<^sub>E] \<in> Q \<or> e = Tock \<and> filter_tocks \<rho> @ [[X]\<^sub>R, [e]\<^sub>E] \<in> Q}
        \<subseteq> {e. e \<noteq> Tock \<and> \<rho> @ [[e]\<^sub>E] \<in> P \<triangle>\<^sub>T Q \<or> e = Tock \<and> \<rho> @ [[X]\<^sub>R, [e]\<^sub>E] \<in> P \<triangle>\<^sub>T Q}"
      proof auto
        fix x
        assume case_assms3: "filter_tocks \<rho> @ [[x]\<^sub>E] \<in> Q" "x \<noteq> Tock"
        show "\<rho> @ [[x]\<^sub>E] \<in> P \<triangle>\<^sub>T Q"
          unfolding TimeSyncInterruptTTT_def using 1 2 case_assms3 by auto
      next
        fix x
        assume case_assms3: "filter_tocks \<rho> @ [[x]\<^sub>E] \<in> Q" "x \<noteq> Tock"
        show "\<rho> @ [[x]\<^sub>E] \<in> P \<triangle>\<^sub>T Q"
          unfolding TimeSyncInterruptTTT_def using 1 2 case_assms3 by auto
      next
        assume case_assms3: "filter_tocks \<rho> @ [[X]\<^sub>R, [Tock]\<^sub>E] \<in> Q"
        show "\<rho> @ [[X]\<^sub>R, [Tock]\<^sub>E] \<notin> P \<triangle>\<^sub>T Q \<Longrightarrow> False"
          unfolding TimeSyncInterruptTTT_def case_assms3 filter_tocks_end_ref_tock 1 2 3 apply auto
          apply (erule_tac x="\<rho> @ [[X]\<^sub>R, [Tock]\<^sub>E]" in allE, auto simp add: 1 2 3)
          by (erule_tac x="[]" in allE, auto simp add: case_assms3 filter_tocks_end_ref_tock)
      next
        assume case_assms3: "filter_tocks \<rho> @ [[X]\<^sub>R, [Tock]\<^sub>E] \<in> Q"
        show "\<rho> @ [[X]\<^sub>R, [Tock]\<^sub>E] \<notin> P \<triangle>\<^sub>T Q \<Longrightarrow> \<rho> @ [[Tock]\<^sub>E] \<in> P \<triangle>\<^sub>T Q"
          unfolding TimeSyncInterruptTTT_def case_assms3 filter_tocks_end_ref_tock 1 2 3 apply auto
          apply (erule_tac x="\<rho> @ [[X]\<^sub>R, [Tock]\<^sub>E]" in allE, auto simp add: 1 2 3)
          by (erule_tac x="[]" in allE, auto simp add: case_assms3 filter_tocks_end_ref_tock)
      qed
      then have 5: "Y \<inter> {e. e \<noteq> Tock \<and> filter_tocks \<rho> @ [[e]\<^sub>E] \<in> Q \<or> e = Tock \<and> filter_tocks \<rho> @ [[X]\<^sub>R, [e]\<^sub>E] \<in> Q} = {}"
        using assm2 by auto
      have 6: "\<rho> @ [X \<union> Y]\<^sub>R # [Tock]\<^sub>E # \<sigma>'' @ [[Ya]\<^sub>R] \<in> P"
        using TT2s_P case_assms2 4 unfolding TT2s_def by auto
      have 7: "filter_tocks \<rho> @ [X \<union> Y]\<^sub>R # [Tock]\<^sub>E # filter_tocks \<sigma>'' @ [[Z]\<^sub>R] \<in> Q"
        using TT2s_Q case_assms2 5 unfolding TT2s_def by auto
      have 8: "filter_tocks (\<rho> @ [X \<union> Y]\<^sub>R # [Tock]\<^sub>E # \<sigma>'') = filter_tocks \<rho> @ [X \<union> Y]\<^sub>R # [Tock]\<^sub>E # filter_tocks \<sigma>''"
        by (induct \<rho> rule:filter_tocks.induct, auto)
      show "\<rho> @ [X \<union> Y]\<^sub>R # [Tock]\<^sub>E # \<sigma>'' @ [[W]\<^sub>R] \<in> P \<triangle>\<^sub>T Q"
        unfolding TimeSyncInterruptTTT_def using case_assms2 6 7 8 by force
    next
      fix p2 q3
      assume case_assms2: "\<sigma>' = p2 @ q3" "\<rho> @ [X]\<^sub>R # [Tock]\<^sub>E # p2 \<in> P" "filter_tocks \<rho> @ [X]\<^sub>R # [Tock]\<^sub>E # filter_tocks p2 @ q3 \<in> Q"
        "\<nexists>p'. \<rho> @ [X]\<^sub>R # [Tock]\<^sub>E # p2 = p' @ [[Tick]\<^sub>E]" "\<nexists>p' Y. \<rho> @ [X]\<^sub>R # [Tock]\<^sub>E # p2 = p' @ [[Y]\<^sub>R]" "\<nexists>Ya q'. q3 = [Ya]\<^sub>R # q'"
      have 1: "(\<nexists>p'. \<rho> = p' @ [[Tick]\<^sub>E]) \<and> (\<nexists>p' Y. \<rho> = p' @ [[Y]\<^sub>R])"
      proof auto
        fix p'
        assume "\<rho> = p' @ [[Tick]\<^sub>E]"
        then have "p' @ [Tick]\<^sub>E # [X]\<^sub>R # [Tock]\<^sub>E # p2 \<in> P"
          using case_assms2 by auto
        then have "ttWF (p' @ [Tick]\<^sub>E # [X]\<^sub>R # [Tock]\<^sub>E # p2)"
          using P_wf by blast
        then show False
          by (induct p' rule:ttWF.induct, auto)
      next
        fix p' Y
        assume "\<rho> = p' @ [[Y]\<^sub>R]"
        then have "p' @ [Y]\<^sub>R # [X]\<^sub>R # [Tock]\<^sub>E # p2 \<in> P"
          using case_assms2 by auto
        then have "ttWF (p' @ [Y]\<^sub>R # [X]\<^sub>R # [Tock]\<^sub>E # p2)"
          using P_wf by blast
        then show False
          by (induct p' rule:ttWF.induct, auto)
      qed
      have 2: "\<rho> \<in> P"
        using TT1_P TT1_def case_assms2(2) ctt_prefix_concat ctt_prefix_imp_prefix_subset by blast
      have 3: "\<rho> @ [[X]\<^sub>R, [Tock]\<^sub>E] \<in> P"
        using TT1_P case_assms2(2) ctt_prefix_subset_same_front unfolding TT1_def by fastforce
      have "{e. e \<noteq> Tock \<and> \<rho> @ [[e]\<^sub>E] \<in> P \<or> e = Tock \<and> \<rho> @ [[X]\<^sub>R, [e]\<^sub>E] \<in> P}
        \<subseteq> {e. e \<noteq> Tock \<and> \<rho> @ [[e]\<^sub>E] \<in> P \<triangle>\<^sub>T Q \<or> e = Tock \<and> \<rho> @ [[X]\<^sub>R, [e]\<^sub>E] \<in> P \<triangle>\<^sub>T Q}"
      proof auto
        fix x
        assume case_assms3:  "\<rho> @ [[x]\<^sub>E] \<in> P" "x \<noteq> Tock"
        have "filter_tocks (\<rho> @ [X]\<^sub>R # [Tock]\<^sub>E # p2) = filter_tocks \<rho> @ filter_tocks ([X]\<^sub>R # [Tock]\<^sub>E # p2)"
          by (induct \<rho> rule:filter_tocks.induct, auto)
        then have "filter_tocks \<rho> @ filter_tocks ([X]\<^sub>R # [Tock]\<^sub>E # p2) @ q3 \<in> Q"
          using case_assms2 by auto
        then have 1: "filter_tocks \<rho> \<in> Q"
          using TT1_Q TT1_def ctt_prefix_concat ctt_prefix_imp_prefix_subset by blast
        show "\<rho> @ [[x]\<^sub>E] \<in> P \<triangle>\<^sub>T Q"
          using case_assms3 unfolding TimeSyncInterruptTTT_def
        proof (cases x, auto)
          fix x1
          assume case_assms4: "\<rho> @ [[Event x1]\<^sub>E] \<in> P" "x = Event x1"
          show "\<exists>p. p \<in> P \<and> (\<forall>p'. p \<noteq> p' @ [[Tick]\<^sub>E]) \<and> (\<forall>p' Y. p \<noteq> p' @ [[Y]\<^sub>R]) \<and>
            (\<exists>q2. filter_tocks p @ q2 \<in> Q \<and> (\<forall>q' Y. q2 \<noteq> [Y]\<^sub>R # q') \<and> \<rho> @ [[Event x1]\<^sub>E] = p @ q2)"
            using 1 case_assms4 by (rule_tac x="\<rho> @ [[Event x1]\<^sub>E]" in exI, auto simp add: filter_tocks_end_event)
        next
          show "filter_tocks \<rho> \<in> Q"
            using 1 by auto
        qed
      next
        fix x
        assume case_assms3:  "\<rho> @ [[x]\<^sub>E] \<in> P" "x \<noteq> Tock"
        have "filter_tocks (\<rho> @ [X]\<^sub>R # [Tock]\<^sub>E # p2) = filter_tocks \<rho> @ filter_tocks ([X]\<^sub>R # [Tock]\<^sub>E # p2)"
          by (induct \<rho> rule:filter_tocks.induct, auto)
        then have "filter_tocks \<rho> @ filter_tocks ([X]\<^sub>R # [Tock]\<^sub>E # p2) @ q3 \<in> Q"
          using case_assms2 by auto
        then have 1: "filter_tocks \<rho> \<in> Q"
          using TT1_Q TT1_def ctt_prefix_concat ctt_prefix_imp_prefix_subset by blast
        show "\<rho> @ [[x]\<^sub>E] \<in> P \<triangle>\<^sub>T Q"
          using case_assms3 unfolding TimeSyncInterruptTTT_def
        proof (cases x, auto)
          fix x1
          assume case_assms4: "\<rho> @ [[Event x1]\<^sub>E] \<in> P" "x = Event x1"
          show "\<exists>p. p \<in> P \<and> (\<forall>p'. p \<noteq> p' @ [[Tick]\<^sub>E]) \<and> (\<forall>p' Y. p \<noteq> p' @ [[Y]\<^sub>R]) \<and>
            (\<exists>q2. filter_tocks p @ q2 \<in> Q \<and> (\<forall>q' Y. q2 \<noteq> [Y]\<^sub>R # q') \<and> \<rho> @ [[Event x1]\<^sub>E] = p @ q2)"
            using 1 case_assms4 by (rule_tac x="\<rho> @ [[Event x1]\<^sub>E]" in exI, auto simp add: filter_tocks_end_event)
        next
          show "filter_tocks \<rho> \<in> Q"
            using 1 by auto
        qed
      next
        assume case_assms3: "\<rho> @ [[X]\<^sub>R, [Tock]\<^sub>E] \<in> P"
        have "filter_tocks (\<rho> @ [X]\<^sub>R # [Tock]\<^sub>E # p2) = filter_tocks \<rho> @ filter_tocks ([X]\<^sub>R # [Tock]\<^sub>E # p2)"
          by (induct \<rho> rule:filter_tocks.induct, auto)
        then have "filter_tocks \<rho> @ filter_tocks ([X]\<^sub>R # [Tock]\<^sub>E # p2) @ q3 \<in> Q"
          using case_assms2(3) case_assms2(4) by auto
        then have "filter_tocks \<rho> @ [[X]\<^sub>R, [Tock]\<^sub>E] \<in> Q"
          using TT1_Q unfolding TT1_def apply auto
          by (meson ctt_prefix_subset.simps(1) ctt_prefix_subset.simps(2) ctt_prefix_subset.simps(3) ctt_prefix_subset_same_front subsetI) 
        then show "\<rho> @ [[X]\<^sub>R, [Tock]\<^sub>E] \<notin> P \<triangle>\<^sub>T Q \<Longrightarrow> False"
          unfolding TimeSyncInterruptTTT_def apply (auto)
          apply (erule_tac x="\<rho> @ [[X]\<^sub>R, [Tock]\<^sub>E]" in allE, auto simp add: case_assms3)
          by (erule_tac x="[]" in allE, auto simp add: filter_tocks_end_ref_tock)
      next
        assume case_assms3: "\<rho> @ [[X]\<^sub>R, [Tock]\<^sub>E] \<in> P"
        have "filter_tocks (\<rho> @ [X]\<^sub>R # [Tock]\<^sub>E # p2) = filter_tocks \<rho> @ filter_tocks ([X]\<^sub>R # [Tock]\<^sub>E # p2)"
          by (induct \<rho> rule:filter_tocks.induct, auto)
        then have "filter_tocks \<rho> @ filter_tocks ([X]\<^sub>R # [Tock]\<^sub>E # p2) @ q3 \<in> Q"
          using case_assms2(3) case_assms2(4) by auto
        then have "filter_tocks \<rho> @ [[X]\<^sub>R, [Tock]\<^sub>E] \<in> Q"
          using TT1_Q unfolding TT1_def apply auto
          by (meson ctt_prefix_subset.simps(1) ctt_prefix_subset.simps(2) ctt_prefix_subset.simps(3) ctt_prefix_subset_same_front subsetI) 
        then show "\<rho> @ [[X]\<^sub>R, [Tock]\<^sub>E] \<notin> P \<triangle>\<^sub>T Q \<Longrightarrow> \<rho> @ [[Tock]\<^sub>E] \<in> P \<triangle>\<^sub>T Q"
          unfolding TimeSyncInterruptTTT_def apply (auto)
          apply (erule_tac x="\<rho> @ [[X]\<^sub>R, [Tock]\<^sub>E]" in allE, auto simp add: case_assms3)
          by (erule_tac x="[]" in allE, auto simp add: filter_tocks_end_ref_tock)
      qed
      then have 4: "Y \<inter> {e. e \<noteq> Tock \<and> \<rho> @ [[e]\<^sub>E] \<in> P \<or> e = Tock \<and> \<rho> @ [[X]\<^sub>R, [e]\<^sub>E] \<in> P} = {}"
        using assm2 by auto
      have "{e. e \<noteq> Tock \<and> filter_tocks \<rho> @ [[e]\<^sub>E] \<in> Q \<or> e = Tock \<and> filter_tocks \<rho> @ [[X]\<^sub>R, [e]\<^sub>E] \<in> Q}
        \<subseteq> {e. e \<noteq> Tock \<and> \<rho> @ [[e]\<^sub>E] \<in> P \<triangle>\<^sub>T Q \<or> e = Tock \<and> \<rho> @ [[X]\<^sub>R, [e]\<^sub>E] \<in> P \<triangle>\<^sub>T Q}"
      proof auto
        fix x
        assume case_assms3: "filter_tocks \<rho> @ [[x]\<^sub>E] \<in> Q" "x \<noteq> Tock"
        show "\<rho> @ [[x]\<^sub>E] \<in> P \<triangle>\<^sub>T Q"
          unfolding TimeSyncInterruptTTT_def using 1 2 case_assms3 by auto
      next
        fix x
        assume case_assms3: "filter_tocks \<rho> @ [[x]\<^sub>E] \<in> Q" "x \<noteq> Tock"
        show "\<rho> @ [[x]\<^sub>E] \<in> P \<triangle>\<^sub>T Q"
          unfolding TimeSyncInterruptTTT_def using 1 2 case_assms3 by auto
      next
        assume case_assms3: "filter_tocks \<rho> @ [[X]\<^sub>R, [Tock]\<^sub>E] \<in> Q"
        show "\<rho> @ [[X]\<^sub>R, [Tock]\<^sub>E] \<notin> P \<triangle>\<^sub>T Q \<Longrightarrow> False"
          unfolding TimeSyncInterruptTTT_def case_assms3 filter_tocks_end_ref_tock 1 2 3 apply auto
          apply (erule_tac x="\<rho> @ [[X]\<^sub>R, [Tock]\<^sub>E]" in allE, auto simp add: 1 2 3)
          by (erule_tac x="[]" in allE, auto simp add: case_assms3 filter_tocks_end_ref_tock)
      next
        assume case_assms3: "filter_tocks \<rho> @ [[X]\<^sub>R, [Tock]\<^sub>E] \<in> Q"
        show "\<rho> @ [[X]\<^sub>R, [Tock]\<^sub>E] \<notin> P \<triangle>\<^sub>T Q \<Longrightarrow> \<rho> @ [[Tock]\<^sub>E] \<in> P \<triangle>\<^sub>T Q"
          unfolding TimeSyncInterruptTTT_def case_assms3 filter_tocks_end_ref_tock 1 2 3 apply auto
          apply (erule_tac x="\<rho> @ [[X]\<^sub>R, [Tock]\<^sub>E]" in allE, auto simp add: 1 2 3)
          by (erule_tac x="[]" in allE, auto simp add: case_assms3 filter_tocks_end_ref_tock)
      qed
      then have 5: "Y \<inter> {e. e \<noteq> Tock \<and> filter_tocks \<rho> @ [[e]\<^sub>E] \<in> Q \<or> e = Tock \<and> filter_tocks \<rho> @ [[X]\<^sub>R, [e]\<^sub>E] \<in> Q} = {}"
        using assm2 by auto
      have 6: "\<rho> @ [X \<union> Y]\<^sub>R # [Tock]\<^sub>E # p2 \<in> P"
        using TT2s_P case_assms2 4 unfolding TT2s_def by auto
      have 7: "filter_tocks \<rho> @ [X \<union> Y]\<^sub>R # [Tock]\<^sub>E # filter_tocks p2 @ q3 \<in> Q"
        using TT2s_Q case_assms2 5 unfolding TT2s_def by auto
      have 8: "filter_tocks (\<rho> @ [X \<union> Y]\<^sub>R # [Tock]\<^sub>E # p2) = filter_tocks \<rho> @ [X \<union> Y]\<^sub>R # [Tock]\<^sub>E # filter_tocks p2"
        by (induct \<rho> rule:filter_tocks.induct, auto)
      have 9: "(\<forall>p'. \<rho> @ [X \<union> Y]\<^sub>R # [Tock]\<^sub>E # p2 \<noteq> p' @ [[Tick]\<^sub>E]) \<and> (\<forall>p' Ya. \<rho> @ [X \<union> Y]\<^sub>R # [Tock]\<^sub>E # p2 \<noteq> p' @ [[Ya]\<^sub>R])"
      proof auto
        fix p'
        assume "\<rho> @ [X \<union> Y]\<^sub>R # [Tock]\<^sub>E # p2 = p' @ [[Tick]\<^sub>E]"
        then have "\<exists> p''. p2 = p'' @ [[Tick]\<^sub>E]"
          by (metis append_butlast_last_id cttevent.simps(7) cttobs.inject(1) last.simps last_appendR list.distinct(1))
        then show False
          using case_assms2(4) by auto
      next
        fix p' Ya
        assume "\<rho> @ [X \<union> Y]\<^sub>R # [Tock]\<^sub>E # p2 = p' @ [[Ya]\<^sub>R]"
        then have "\<exists> p''. p2 = p'' @ [[Ya]\<^sub>R]"
          by (metis append_butlast_last_id cttobs.distinct(1) last.simps last_appendR list.distinct(1))
        then show False
          using case_assms2(5) by auto
      qed
      show "\<rho> @ [X \<union> Y]\<^sub>R # [Tock]\<^sub>E # p2 @ q3 \<in> P \<triangle>\<^sub>T Q"
        unfolding TimeSyncInterruptTTT_def using case_assms2 6 7 8 9 by auto
    next
      fix p q2
      assume case_assms2: "\<rho> = p @ q2" "p \<in> P" "filter_tocks p @ q2 @ [X]\<^sub>R # [Tock]\<^sub>E # \<sigma>' \<in> Q" "\<nexists>Ya q'. q2 = [Ya]\<^sub>R # q'"
        "q2 \<noteq> []" "\<nexists>p'. p = p' @ [[Tick]\<^sub>E]" "\<nexists>p' Y. p = p' @ [[Y]\<^sub>R]"
      have "{e. e \<noteq> Tock \<and> filter_tocks p @ q2 @ [[e]\<^sub>E] \<in> Q \<or> e = Tock \<and> filter_tocks p @ q2 @ [[X]\<^sub>R, [e]\<^sub>E] \<in> Q}
        \<subseteq> {e. e \<noteq> Tock \<and> \<rho> @ [[e]\<^sub>E] \<in> P \<triangle>\<^sub>T Q \<or> e = Tock \<and> \<rho> @ [[X]\<^sub>R, [e]\<^sub>E] \<in> P \<triangle>\<^sub>T Q}"
      proof auto
        fix x
        assume case_assms3: "filter_tocks p @ q2 @ [[x]\<^sub>E] \<in> Q" "x \<noteq> Tock"
        show "\<rho> @ [[x]\<^sub>E] \<in> P \<triangle>\<^sub>T Q"
          unfolding TimeSyncInterruptTTT_def using case_assms3 apply (safe, simp_all)
          apply (erule_tac x="p" in allE, simp add: case_assms2)
          apply (erule_tac x="q2 @ [[x]\<^sub>E]" in allE, simp add: case_assms3)
          by (simp add: append_eq_Cons_conv case_assms2(4))
      next
        fix x
        assume case_assms3: "filter_tocks p @ q2 @ [[x]\<^sub>E] \<in> Q" "x \<noteq> Tock"
        show "\<rho> @ [[x]\<^sub>E] \<in> P \<triangle>\<^sub>T Q"
          unfolding TimeSyncInterruptTTT_def using case_assms3 apply (safe, simp_all)
          apply (erule_tac x="p" in allE, simp add: case_assms2)
          apply (erule_tac x="q2 @ [[x]\<^sub>E]" in allE, simp add: case_assms3)
          by (simp add: append_eq_Cons_conv case_assms2(4))
      next
        assume case_assms3: "filter_tocks p @ q2 @ [[X]\<^sub>R, [Tock]\<^sub>E] \<in> Q"
        show "\<rho> @ [[X]\<^sub>R, [Tock]\<^sub>E] \<notin> P \<triangle>\<^sub>T Q \<Longrightarrow> False"
          unfolding TimeSyncInterruptTTT_def case_assms3 filter_tocks_end_ref_tock apply auto
          apply (erule_tac x="p" in allE, auto simp add: case_assms2)
          apply (erule_tac x="q2 @ [[X]\<^sub>R, [Tock]\<^sub>E]" in allE, auto simp add: case_assms3)
          by (meson append_eq_Cons_conv case_assms2(4) case_assms2(5))
      next
        assume case_assms3: "filter_tocks p @ q2 @ [[X]\<^sub>R, [Tock]\<^sub>E] \<in> Q"
        show "\<rho> @ [[X]\<^sub>R, [Tock]\<^sub>E] \<notin> P \<triangle>\<^sub>T Q \<Longrightarrow> \<rho> @ [[Tock]\<^sub>E] \<in> P \<triangle>\<^sub>T Q"
          unfolding TimeSyncInterruptTTT_def case_assms3 filter_tocks_end_ref_tock apply auto
          apply (erule_tac x="p" in allE, auto simp add: case_assms2)
          apply (erule_tac x="q2 @ [[X]\<^sub>R, [Tock]\<^sub>E]" in allE, auto simp add: case_assms3)
          by (meson append_eq_Cons_conv case_assms2(4) case_assms2(5))
      qed
      then have 1: "Y \<inter> {e. e \<noteq> Tock \<and> filter_tocks p @ q2 @ [[e]\<^sub>E] \<in> Q \<or> e = Tock \<and> filter_tocks p @ q2 @ [[X]\<^sub>R, [e]\<^sub>E] \<in> Q} = {}"
        using assm2 by auto
      thm case_assms2
      have 2: "filter_tocks p @ q2 @ [X \<union> Y]\<^sub>R # [Tock]\<^sub>E # \<sigma>' \<in> Q"
        using TT2s_Q unfolding TT2s_def apply auto
        by (erule_tac x="filter_tocks p @ q2" in allE, erule_tac x="[Tock]\<^sub>E # \<sigma>'" in allE, auto simp add: 1 case_assms2)
      have 3: "\<nexists> Ya q'. q2 @ [X \<union> Y]\<^sub>R # [Tock]\<^sub>E # \<sigma>' = [Ya]\<^sub>R # q'"
        by (simp add: append_eq_Cons_conv case_assms2(4) case_assms2(5))
        thm case_assms2
      show "(p @ q2) @ [X \<union> Y]\<^sub>R # [Tock]\<^sub>E # \<sigma>' \<in> P \<triangle>\<^sub>T Q"
        unfolding TimeSyncInterruptTTT_def using case_assms2 2 3 by (auto)
    qed
  qed
qed

lemma TT3_TimeSyncInterrupt:
  assumes "TT3 P" "TT3 Q" "\<forall>x\<in>Q. ttWF x"
  shows "TT3 (P \<triangle>\<^sub>T Q)"
  unfolding TT3_def TimeSyncInterruptTTT_def
proof (safe, simp_all)
  fix p
  assume "p @ [[Tick]\<^sub>E] \<in> P"
  then show "TT3_trace (p @ [[Tick]\<^sub>E])"
    using assms(1) unfolding TT3_def by auto
next
  fix p X Y Z
  assume "p @ [[X]\<^sub>R] \<in> P"
  then have "TT3_trace (p @ [[X]\<^sub>R])"
    using assms(1) unfolding TT3_def by auto
  then show "TT3_trace (p @ [[Z]\<^sub>R])"
    using TT3_trace_end_refusal_change by blast
next
  fix p q2
  assume "p \<in> P"
  then have "TT3_trace p"
    using assms(1) unfolding TT3_def by auto
  also assume assm2: "filter_tocks p @ q2 \<in> Q"
  then have "TT3_trace (filter_tocks p @ q2)"
    using assms(2) unfolding TT3_def by auto
  then have "TT3_trace q2"
    using TT3_trace_cons_right by blast
  then show "TT3_trace (p @ q2)"
    using calculation TT3_append assm2 assms(3) filter_tocks_in_tocks tocks_append_wf2 by blast
qed

lemma add_Tick_refusal_trace_filter_tocks:
  "add_Tick_refusal_trace (filter_tocks t) = filter_tocks (add_Tick_refusal_trace t)"
  by (induct t rule:filter_tocks.induct, auto, (case_tac x, auto)+)

lemma TT4s_TimeSyncInterrupt:
  assumes TT4s_P: "TT4s P" and TT4s_Q: "TT4s Q"
  shows "TT4s (P \<triangle>\<^sub>T Q)"
  unfolding TT4s_def TimeSyncInterruptTTT_def
proof (safe, simp_all)
  fix p
  assume case_assms: "p @ [[Tick]\<^sub>E] \<in> P" "filter_tocks p \<in> Q"
  have 1: "add_Tick_refusal_trace p @ [[Tick]\<^sub>E] \<in> P"
    by (metis TT4s_P TT4s_def add_Tick_refusal_trace_end_event case_assms(1))
  have 2: "filter_tocks (add_Tick_refusal_trace p) \<in> Q"
    by (metis TT4s_Q TT4s_def add_Tick_refusal_trace_filter_tocks case_assms(2))
  show "\<exists>pa. pa @ [[Tick]\<^sub>E] \<in> P \<and> filter_tocks pa \<in> Q \<and> add_Tick_refusal_trace (p @ [[Tick]\<^sub>E]) = pa @ [[Tick]\<^sub>E]"
    using 1 2 by (rule_tac x="add_Tick_refusal_trace p" in exI, auto simp add: add_Tick_refusal_trace_end_event)
next
  fix p X Y Z
  assume case_assms: "p @ [[X]\<^sub>R] \<in> P" "filter_tocks p @ [[Y]\<^sub>R] \<in> Q" "Z \<subseteq> X \<union> Y" "{e \<in> X. e \<noteq> Tock} = {e \<in> Y. e \<noteq> Tock}"
  have 1: "add_Tick_refusal_trace p @ [[X \<union> {Tick}]\<^sub>R] \<in> P"
    by (metis TT4s_P TT4s_def add_Tick_refusal_trace_end_refusal case_assms(1))
  have 2: "filter_tocks (add_Tick_refusal_trace p) @ [[Y \<union> {Tick}]\<^sub>R] \<in> Q"
    by (metis TT4s_Q TT4s_def add_Tick_refusal_trace_end_refusal add_Tick_refusal_trace_filter_tocks case_assms(2))
  show "\<forall>pa X. pa @ [[X]\<^sub>R] \<in> P \<longrightarrow> (\<forall>Y. {e \<in> X. e \<noteq> Tock} = {e \<in> Y. e \<noteq> Tock} \<longrightarrow>
      filter_tocks pa @ [[Y]\<^sub>R] \<in> Q \<longrightarrow> (\<forall>Za\<subseteq>X \<union> Y. add_Tick_refusal_trace (p @ [[Z]\<^sub>R]) \<noteq> pa @ [[Za]\<^sub>R])) \<Longrightarrow>
    \<exists>pa. pa @ [[Tick]\<^sub>E] \<in> P \<and> filter_tocks pa \<in> Q \<and> add_Tick_refusal_trace (p @ [[Z]\<^sub>R]) = pa @ [[Tick]\<^sub>E]"
    using 1 2 case_assms apply (erule_tac x="add_Tick_refusal_trace p" in allE, erule_tac x="X \<union> {Tick}" in allE, safe, simp_all)
    apply (erule_tac x="Y \<union> {Tick}" in allE, safe, simp_all, blast, blast)
    by (erule_tac x="Z \<union> {Tick}" in allE, safe, simp, blast, simp add: add_Tick_refusal_trace_end_refusal)
next
  fix p q2
  assume case_assms: "p \<in> P" "\<forall>p'. p \<noteq> p' @ [[Tick]\<^sub>E]" "\<forall>p' Y. p \<noteq> p' @ [[Y]\<^sub>R]" "filter_tocks p @ q2 \<in> Q" "\<forall>q' Y. q2 \<noteq> [Y]\<^sub>R # q'"
  have 1: "add_Tick_refusal_trace p \<in> P"
    using TT4s_P TT4s_def case_assms(1) by blast
  have 2: "(\<forall>p'. add_Tick_refusal_trace p \<noteq> p' @ [[Tick]\<^sub>E]) \<and> (\<forall>p' Y. add_Tick_refusal_trace p \<noteq> p' @ [[Y]\<^sub>R])"
    using add_Tick_refusal_trace_not_end_refusal add_Tick_refusal_trace_not_end_tick case_assms by blast
  have 3: "filter_tocks (add_Tick_refusal_trace p) @ add_Tick_refusal_trace q2 \<in> Q"
    by (metis TT4s_Q TT4s_def add_Tick_refusal_trace_concat add_Tick_refusal_trace_filter_tocks case_assms(4))
  have 4: "\<forall>q' Y. add_Tick_refusal_trace q2 \<noteq> [Y]\<^sub>R # q'"
    by (metis add_Tick_refusal_trace.simps(2) case_assms(5) contains_refusal.elims(2) contains_refusal.elims(3) contains_refusal_add_Tick_refusal_trace cttobs.distinct(1) list.inject)
  show "\<forall>pa. pa \<in> P \<longrightarrow> (\<exists>p'. pa = p' @ [[Tick]\<^sub>E]) \<or> (\<exists>p' Y. pa = p' @ [[Y]\<^sub>R]) \<or>
      (\<forall>q2a. filter_tocks pa @ q2a \<in> Q \<longrightarrow> (\<exists>q' Y. q2a = [Y]\<^sub>R # q') \<or> add_Tick_refusal_trace (p @ q2) \<noteq> pa @ q2a) \<Longrightarrow>
    \<exists>pa. pa @ [[Tick]\<^sub>E] \<in> P \<and> filter_tocks pa \<in> Q \<and> add_Tick_refusal_trace (p @ q2) = pa @ [[Tick]\<^sub>E]"
    using 1 2 3 4 add_Tick_refusal_trace_concat
    by (erule_tac x="add_Tick_refusal_trace p" in allE, auto, erule_tac x="add_Tick_refusal_trace q2" in allE, auto)
qed

lemma TT_TimeSyncInterrupt:
  assumes "TT P" "TT Q"
  shows "TT (P \<triangle>\<^sub>T Q)"
  using assms unfolding TT_def apply auto
  using TimeSyncInterruptTTT_wf apply blast
  using TT0_TimeSyncInterrupt apply blast
  using TT1_TimeSyncInterrupt apply blast
  using TT2_TimeSyncInterrupt apply blast
  using TT3_TimeSyncInterrupt apply blast
  done

end