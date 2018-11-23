theory CTockTick_Interrupt
  imports CTockTick_Core
begin

subsection {* Untimed Interrupt *}

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

definition UntimedInterruptCTT :: "'e cttobs list set \<Rightarrow> 'e cttobs list set \<Rightarrow> 'e cttobs list set" (infixl "\<triangle>\<^sub>U" 58) where
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
  fix p X Y q
  assume "\<forall>x\<in>P. cttWF x" "\<forall>x\<in>Q. cttWF x" "p @ [[X]\<^sub>R] \<in> P" "[Y]\<^sub>R # q \<in> Q"
  then show "cttWF (intersect_refusal_trace Y (p @ [[X]\<^sub>R]) @ q)"
    using end_refusal_start_refusal_append_wf intersect_refusal_trace_append_wf by (blast)
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
  then show "cttWF (p @ q)"
    using nontick_event_end_append_wf by blast
qed

lemma CT0_UntimedInterrupt:
  assumes "CT0 P" "CT1 P" "CT0 Q" "CT1 Q"
  shows "CT0 (P \<triangle>\<^sub>U Q)"
  unfolding UntimedInterruptCTT_def CT0_def
proof auto
  have empty_in_P_Q: "[] \<in> P" "[] \<in> Q"
    by (simp_all add: CT0_CT1_empty assms)
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

lemma CT1_UntimedInterrupt:
  assumes P_wf: "\<forall>x\<in>P. cttWF x"
  assumes CT1_P: "CT1 P" and CT0_Q: "CT0 Q" and CT1_Q: "CT1 Q"
  shows "CT1 (P \<triangle>\<^sub>U Q)"
  unfolding CT1_def
proof (auto)
  fix \<rho> \<sigma>
  assume "\<sigma> \<in> P \<triangle>\<^sub>U Q"
  thm UntimedInterruptCTT_def[where P=P, where Q=Q]
  then have "(\<exists>p X. p @ [[Tick]\<^sub>E] \<in> P \<and> contains_refusal p \<and> [[X]\<^sub>R] \<in> Q \<and> \<sigma> = intersect_refusal_trace X (p @ [[Tick]\<^sub>E]))
      \<or> (\<exists>p. p @ [[Tick]\<^sub>E] \<in> P \<and> \<not> contains_refusal p \<and> \<sigma> = p @ [[Tick]\<^sub>E])
      \<or> (\<exists>p X Y q. p @ [[X]\<^sub>R] \<in> P \<and> [Y]\<^sub>R # q \<in> Q \<and> \<sigma> = intersect_refusal_trace Y (p @ [[X]\<^sub>R]) @ q)
      \<or> (\<exists>p q X. p \<in> P \<and> (\<nexists>p'. p = p' @ [[Tick]\<^sub>E]) \<and> (\<nexists>p' Y. p = p' @ [[Y]\<^sub>R]) \<and>
            contains_refusal p \<and> [[X]\<^sub>R] \<in> Q \<and> q \<in> Q \<and> (\<nexists>q' Y. q = [Y]\<^sub>R # q') \<and> \<sigma> = intersect_refusal_trace X p @ q)
      \<or> (\<exists>p q. p \<in> P \<and> (\<nexists>p'. p = p' @ [[Tick]\<^sub>E]) \<and> (\<nexists>p' Y. p = p' @ [[Y]\<^sub>R]) \<and> 
            \<not> contains_refusal p \<and> q \<in> Q \<and> (\<nexists>q' Y. q = [Y]\<^sub>R # q') \<and> \<sigma> = p @ q)"
    unfolding UntimedInterruptCTT_def by safe
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
        apply (rule_tac x="p'" in exI, auto, rule_tac x="[]" in exI, rule_tac x="X" in exI, auto simp add: CT0_CT1_empty CT0_Q CT1_Q)
        apply (erule_tac x="p'" in allE, simp_all add: case_assms, erule_tac x="[]" in allE, simp_all add: case_assms)
        by (simp add: CT0_CT1_empty CT0_Q CT1_Q not_contains_refusal_intersect_refusal_trace)
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
      using \<rho>_assm CT1_P in_P unfolding CT1_def by auto
    have not_contains_refusal_\<rho>: "\<not> contains_refusal \<rho>"
      using \<rho>_assm not_contains_refusal_append_event not_contains_refusal_ctt_prefix_subset not_contains_refusal_p by auto
    show "\<rho> \<in> P \<triangle>\<^sub>U Q"
      using \<rho>_cases \<rho>_in_P \<rho>_assm unfolding UntimedInterruptCTT_def
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
        by (erule_tac x="\<rho>" in allE, auto, erule_tac x="[]" in allE, auto simp add: CT0_CT1_empty CT0_Q CT1_Q)
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
          apply (metis CT1_Q CT1_def append_Nil2 ctt_prefix_concat ctt_prefix_imp_prefix_subset list.distinct(1) self_append_conv2)
          apply (erule_tac x="p'" in allE, auto)
          by (metis CT0_CT1_empty CT0_Q CT1_Q append_Nil2 contains_refusal.simps(1) contains_refusal.simps(2) not_contains_refusal_intersect_refusal_trace)
      qed
    next
      fix q' p' X'
      assume case_assms: "intersect_refusal_trace Y (p' @ [[X']\<^sub>R]) \<subseteq>\<^sub>C intersect_refusal_trace Y (p @ [[X]\<^sub>R])" "q' \<lesssim>\<^sub>C q" "p' @ [[X']\<^sub>R] \<subseteq>\<^sub>C p @ [[X]\<^sub>R]"
      then have "p' @ [[X']\<^sub>R] \<in> P"
        using CT1_P CT1_def ctt_subset_imp_prefix_subset in_P by blast
      then show "intersect_refusal_trace Y (p' @ [[X']\<^sub>R]) @ q' \<in> P \<triangle>\<^sub>U Q"
        unfolding UntimedInterruptCTT_def using case_assms in_Q
      proof (auto)
        show "p' @ [[X']\<^sub>R] \<in> P \<Longrightarrow> intersect_refusal_trace Y (p' @ [[X']\<^sub>R]) \<subseteq>\<^sub>C intersect_refusal_trace Y (p @ [[X]\<^sub>R]) \<Longrightarrow>
          q' \<lesssim>\<^sub>C q \<Longrightarrow> p' @ [[X']\<^sub>R] \<subseteq>\<^sub>C p @ [[X]\<^sub>R] \<Longrightarrow> [Y]\<^sub>R # q \<in> Q \<Longrightarrow>
          \<forall>p X. p @ [[X]\<^sub>R] \<in> P \<longrightarrow>
            (\<forall>Ya q. [Ya]\<^sub>R # q \<in> Q \<longrightarrow> intersect_refusal_trace Y (p' @ [[X']\<^sub>R]) @ q' \<noteq> intersect_refusal_trace Ya (p @ [[X]\<^sub>R]) @ q) \<Longrightarrow>
          \<exists>p. p \<in> P \<and> (\<forall>p'. p \<noteq> p' @ [[Tick]\<^sub>E]) \<and> (\<forall>p' Y. p \<noteq> p' @ [[Y]\<^sub>R]) \<and> contains_refusal p \<and>
            (\<exists>q X. [[X]\<^sub>R] \<in> Q \<and> q \<in> Q \<and> (\<forall>q' Y. q \<noteq> [Y]\<^sub>R # q') \<and> 
              intersect_refusal_trace Y (p' @ [[X']\<^sub>R]) @ q' = intersect_refusal_trace X p @ q)"
          by (metis CT1_Q CT1_def append.left_neutral append_Cons ctt_prefix_subset_same_front)+
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
          using ref_in_Q p'_in_P p'_assms CT0_CT1_empty CT0_Q CT1_Q
          apply (cases "contains_refusal p'")
          apply (rule_tac x="p'" in exI, auto simp add: case_assms, rule_tac x="[]" in exI, auto)
          by (erule_tac x="p'" in allE, auto simp add: case_assms not_contains_refusal_intersect_refusal_trace, erule_tac x="[]" in allE, auto)
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
      have s'_contains_refusal: "contains_refusal s'"
        using contains_refusal_ctt_subset p_contains_refusal s'_ctt_subset by auto
      show  "\<rho> = intersect_refusal_trace X s' @ t' \<Longrightarrow> intersect_refusal_trace X s' @ t' \<in> P \<triangle>\<^sub>U Q"
        unfolding UntimedInterruptCTT_def
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
    then have cttWF_p: "cttWF p"
      using P_wf by blast
    assume "\<rho> \<lesssim>\<^sub>C p @ q"
    then have "\<rho> \<lesssim>\<^sub>C p \<or> (\<exists>t' s'. s' \<subseteq>\<^sub>C p \<and> t' \<lesssim>\<^sub>C q \<and> \<rho> = s' @ t')"
      by (simp add: ctt_prefix_subset_concat2)
    then show "\<rho> \<in> P \<triangle>\<^sub>U Q"
    proof auto
      assume \<rho>_assms: "\<rho> \<lesssim>\<^sub>C p"
      then have \<rho>_in_P: "\<rho> \<in> P"
        using CT1_P CT1_def p_in_P by blast
      have "(\<exists> s e. p = s @ [[Event e]\<^sub>E]) \<or> (\<exists> s. p = s @ [[Tock]\<^sub>E]) \<or> p = []"
        using case_assms by (auto, metis cttevent.exhaust cttobs.exhaust rev_exhaust)
      then have \<rho>_end_assms: "(\<nexists>p'. \<rho> = p' @ [[Tick]\<^sub>E]) \<and> (\<nexists>p' Y. \<rho> = p' @ [[Y]\<^sub>R])"
        using cttWF_p \<rho>_assms not_contains_refusal_ctt_prefix_subset_end_nonref p_not_contains_refusal apply auto
        using cttWF_end_Event_prefix_subset cttWF_end_Tock_prefix_subset ctt_prefix_subset_antisym by fastforce+
      have \<rho>_not_contains_refusal: "\<not> contains_refusal \<rho>"
        using \<rho>_assms not_contains_refusal_ctt_prefix_subset p_not_contains_refusal by auto
      show "\<rho> \<in> P \<triangle>\<^sub>U Q"
        unfolding UntimedInterruptCTT_def
      proof auto
        show "\<forall>p. p \<in> P \<longrightarrow> (\<exists>p'. p = p' @ [[Tick]\<^sub>E]) \<or> (\<exists>p' Y. p = p' @ [[Y]\<^sub>R]) \<or> contains_refusal p \<or>
            (\<forall>q. q \<in> Q \<longrightarrow> (\<exists>q' Y. q = [Y]\<^sub>R # q') \<or> \<rho> \<noteq> p @ q) \<Longrightarrow>
          \<exists>p. p \<in> P \<and> (\<forall>p'. p \<noteq> p' @ [[Tick]\<^sub>E]) \<and> (\<forall>p' Y. p \<noteq> p' @ [[Y]\<^sub>R]) \<and> contains_refusal p \<and>
            (\<exists>q X. [[X]\<^sub>R] \<in> Q \<and> q \<in> Q \<and> (\<forall>q' Y. q \<noteq> [Y]\<^sub>R # q') \<and> \<rho> = intersect_refusal_trace X p @ q)"
          using \<rho>_in_P \<rho>_assms \<rho>_not_contains_refusal \<rho>_end_assms
          by (erule_tac x="\<rho>" in allE, auto, erule_tac x="[]" in allE, auto simp add: CT0_CT1_empty CT0_Q CT1_Q)
      qed
    next
      fix t' s'
      assume "t' \<lesssim>\<^sub>C q"
      then have t'_assms: "t' \<in> Q \<and> (\<nexists>q' Y. t' = [Y]\<^sub>R # q')"
        apply auto
        using CT1_Q CT1_def q_in_Q apply blast
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
        using s'_ctt_subset CT1_P CT1_def ctt_subset_imp_prefix_subset p_in_P by blast 
      show  "\<rho> = s' @ t' \<Longrightarrow> s' @ t' \<in> P \<triangle>\<^sub>U Q"
        unfolding UntimedInterruptCTT_def
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
  then have \<rho>_cases: "(\<exists>p Z W q. p @ [[Z]\<^sub>R] \<in> P \<and> [W]\<^sub>R # q \<in> Q \<and> \<rho> @ [[X]\<^sub>R] = intersect_refusal_trace W (p @ [[Z]\<^sub>R]) @ q)
    \<or> (\<exists>p q Z. p \<in> P \<and> (\<nexists>p'. p = p' @ [[Tick]\<^sub>E]) \<and> (\<nexists>p' Y. p = p' @ [[Y]\<^sub>R]) \<and> contains_refusal p
      \<and> [[Z]\<^sub>R] \<in> Q \<and> q @ [[X]\<^sub>R] \<in> Q \<and> q \<noteq> [] \<and> (\<nexists>q' Y. q = [Y]\<^sub>R # q') \<and> \<rho> = intersect_refusal_trace Z p @ q)
    \<or> (\<exists>p q. p \<in> P \<and> (\<nexists>p'. p = p' @ [[Tick]\<^sub>E]) \<and> (\<nexists>p' Y. p = p' @ [[Y]\<^sub>R]) \<and> \<not> contains_refusal p
      \<and> q @ [[X]\<^sub>R] \<in> Q \<and> q \<noteq> [] \<and> (\<nexists>q' Y. q = [Y]\<^sub>R # q') \<and> \<rho> = p @ q)"
    unfolding UntimedInterruptCTT_def
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
            unfolding UntimedInterruptCTT_def apply auto
            using case_assms3(1) apply blast
            by (metis append_self_conv case_assms(2) case_assms(3) case_assms2 case_assms3(1) intersect_refusal_trace_end_ref_imp_intersect_refusal_trace_end_event intersect_refusal_trace_idempotent)
        next
          fix e
          show "x = Event e \<Longrightarrow> \<rho> @ [[Event e]\<^sub>E] \<in> P \<triangle>\<^sub>U Q"
            unfolding UntimedInterruptCTT_def apply auto
            using case_assms case_assms2 case_assms3 apply (rule_tac x="\<rho> @ [[Event e]\<^sub>E]" in exI, auto)
            apply (meson ctt_prefix_concat ctt_prefix_imp_prefix_subset not_contains_refusal_ctt_prefix_subset)
            by (metis (no_types, hide_lams) CT1_Q CT1_def append_Nil2 ctt_prefix_subset.simps(1) intersect_refusal_trace_end_ref_imp_intersect_refusal_trace_end_event intersect_refusal_trace_idempotent list.distinct(1))
        qed
      next
        fix x
        assume case_assms3: "\<rho> @ [[x]\<^sub>E] \<in> P" "x \<noteq> Tock" "contains_refusal \<rho>"
        then have "(x = Tick \<or> (\<exists> e. x = Event e))"
          by (cases x, auto)
        then show "\<rho> @ [[x]\<^sub>E] \<in> P \<triangle>\<^sub>U Q"
        proof (auto)
          show "x = Tick \<Longrightarrow> \<rho> @ [[Tick]\<^sub>E] \<in> P \<triangle>\<^sub>U Q"
            unfolding UntimedInterruptCTT_def apply auto
            using case_assms3(1) apply blast
            by (metis append_self_conv case_assms(2) case_assms(3) case_assms2 case_assms3(1) intersect_refusal_trace_end_ref_imp_intersect_refusal_trace_end_event intersect_refusal_trace_idempotent)
        next
          fix e
          show "x = Event e \<Longrightarrow> \<rho> @ [[Event e]\<^sub>E] \<in> P \<triangle>\<^sub>U Q"
            unfolding UntimedInterruptCTT_def apply auto
            using case_assms case_assms2 case_assms3 apply (rule_tac x="\<rho> @ [[Event e]\<^sub>E]" in exI, auto)
            apply (meson ctt_prefix_concat ctt_prefix_imp_prefix_subset not_contains_refusal_ctt_prefix_subset)
            by (metis (no_types, hide_lams) CT1_Q CT1_def append_Nil2 ctt_prefix_subset.simps(1) intersect_refusal_trace_end_ref_imp_intersect_refusal_trace_end_event intersect_refusal_trace_idempotent list.distinct(1))
        qed
      next
        fix x
        assume case_assms3: "\<rho> @ [[x]\<^sub>E] \<in> P" "x \<noteq> Tock" "\<not> contains_refusal \<rho>"
        then have "(x = Tick \<or> (\<exists> e. x = Event e))"
          by (cases x, auto)
        then show "\<rho> @ [[x]\<^sub>E] \<in> P \<triangle>\<^sub>U Q"
        proof (auto)
          show "x = Tick \<Longrightarrow> \<rho> @ [[Tick]\<^sub>E] \<in> P \<triangle>\<^sub>U Q"
            unfolding UntimedInterruptCTT_def apply auto
            using case_assms3(1) apply blast
            by (metis append_self_conv case_assms(2) case_assms(3) case_assms2 case_assms3(1) intersect_refusal_trace_end_ref_imp_intersect_refusal_trace_end_event intersect_refusal_trace_idempotent)
        next
          fix e
          show "x = Event e \<Longrightarrow> \<rho> @ [[Event e]\<^sub>E] \<in> P \<triangle>\<^sub>U Q"
            unfolding UntimedInterruptCTT_def
          proof auto
            show "x = Event e \<Longrightarrow>
              \<forall>p. p \<in> P \<longrightarrow> (\<exists>p'. p = p' @ [[Tick]\<^sub>E]) \<or> (\<exists>p' Y. p = p' @ [[Y]\<^sub>R]) \<or> contains_refusal p \<or>
                (\<forall>q. q \<in> Q \<longrightarrow> (\<exists>q' Y. q = [Y]\<^sub>R # q') \<or> \<rho> @ [[Event e]\<^sub>E] \<noteq> p @ q) \<Longrightarrow>
              \<exists>p. p \<in> P \<and> (\<forall>p'. p \<noteq> p' @ [[Tick]\<^sub>E]) \<and> (\<forall>p' Y. p \<noteq> p' @ [[Y]\<^sub>R]) \<and> contains_refusal p \<and>
                (\<exists>q X. [[X]\<^sub>R] \<in> Q \<and> q \<in> Q \<and> (\<forall>q' Y. q \<noteq> [Y]\<^sub>R # q') \<and> \<rho> @ [[Event e]\<^sub>E] = intersect_refusal_trace X p @ q)"
              using case_assms case_assms2 case_assms3 apply (erule_tac x="\<rho> @ [[Event e]\<^sub>E]" in allE, auto)
              apply (simp add: not_contains_refusal_append_event)
              using CT0_CT1_empty CT0_Q CT1_Q by blast
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
            unfolding UntimedInterruptCTT_def apply auto
            using case_assms3(1) apply blast
            by (metis append_self_conv case_assms(2) case_assms(3) case_assms2 case_assms3(1) intersect_refusal_trace_end_ref_imp_intersect_refusal_trace_end_event intersect_refusal_trace_idempotent)
        next
          fix e
          show "x = Event e \<Longrightarrow> \<rho> @ [[Event e]\<^sub>E] \<in> P \<triangle>\<^sub>U Q"
            unfolding UntimedInterruptCTT_def
          proof auto
            show "x = Event e \<Longrightarrow>
              \<forall>p. p \<in> P \<longrightarrow> (\<exists>p'. p = p' @ [[Tick]\<^sub>E]) \<or> (\<exists>p' Y. p = p' @ [[Y]\<^sub>R]) \<or> contains_refusal p \<or>
                (\<forall>q. q \<in> Q \<longrightarrow> (\<exists>q' Y. q = [Y]\<^sub>R # q') \<or> \<rho> @ [[Event e]\<^sub>E] \<noteq> p @ q) \<Longrightarrow>
              \<exists>p. p \<in> P \<and> (\<forall>p'. p \<noteq> p' @ [[Tick]\<^sub>E]) \<and> (\<forall>p' Y. p \<noteq> p' @ [[Y]\<^sub>R]) \<and> contains_refusal p \<and>
                (\<exists>q X. [[X]\<^sub>R] \<in> Q \<and> q \<in> Q \<and> (\<forall>q' Y. q \<noteq> [Y]\<^sub>R # q') \<and> \<rho> @ [[Event e]\<^sub>E] = intersect_refusal_trace X p @ q)"
              using case_assms case_assms2 case_assms3 apply (erule_tac x="\<rho> @ [[Event e]\<^sub>E]" in allE, auto)
              apply (simp add: not_contains_refusal_append_event)
              using CT0_CT1_empty CT0_Q CT1_Q by blast
          qed
        qed
      next
        show "contains_refusal \<rho> \<Longrightarrow> \<rho> @ [[X]\<^sub>R, [Tock]\<^sub>E] \<in> P \<Longrightarrow> \<rho> @ [[X]\<^sub>R, [Tock]\<^sub>E] \<notin> P \<triangle>\<^sub>U Q \<Longrightarrow> False"
          unfolding UntimedInterruptCTT_def
        proof auto
          show "contains_refusal \<rho> \<Longrightarrow> \<rho> @ [[X]\<^sub>R, [Tock]\<^sub>E] \<in> P \<Longrightarrow>
            \<forall>p. contains_refusal p \<longrightarrow> p \<in> P \<longrightarrow> (\<exists>p'. p = p' @ [[Tick]\<^sub>E]) \<or> (\<exists>p' Y. p = p' @ [[Y]\<^sub>R]) \<or>
              (\<forall>q. q \<in> Q \<longrightarrow> (\<forall>Xa. [[Xa]\<^sub>R] \<in> Q \<longrightarrow> (\<exists>q' Y. q = [Y]\<^sub>R # q') \<or> 
                \<rho> @ [[X]\<^sub>R, [Tock]\<^sub>E] \<noteq> intersect_refusal_trace Xa p @ q)) \<Longrightarrow> False"
            using case_assms case_assms2 apply (erule_tac x="\<rho> @ [[X]\<^sub>R, [Tock]\<^sub>E]" in allE, auto)
            using ctt_prefix_concat ctt_prefix_imp_prefix_subset not_contains_refusal_ctt_prefix_subset apply blast
            apply (erule_tac x="[]" in allE, auto)
            using CT0_CT1_empty CT0_Q CT1_Q apply blast
            by (metis intersect_refusal_trace_end_ref_imp_intersect_refusal_trace_end_ref_tock intersect_refusal_trace_idempotent)
        qed
      next
        have "contains_refusal \<rho> \<Longrightarrow> \<rho> @ [[X]\<^sub>R, [Tock]\<^sub>E] \<in> P \<Longrightarrow> \<rho> @ [[X]\<^sub>R, [Tock]\<^sub>E] \<notin> P \<triangle>\<^sub>U Q \<Longrightarrow> False"
          unfolding UntimedInterruptCTT_def
        proof auto
          show "contains_refusal \<rho> \<Longrightarrow> \<rho> @ [[X]\<^sub>R, [Tock]\<^sub>E] \<in> P \<Longrightarrow>
            \<forall>p. contains_refusal p \<longrightarrow> p \<in> P \<longrightarrow> (\<exists>p'. p = p' @ [[Tick]\<^sub>E]) \<or> (\<exists>p' Y. p = p' @ [[Y]\<^sub>R]) \<or>
              (\<forall>q. q \<in> Q \<longrightarrow> (\<forall>Xa. [[Xa]\<^sub>R] \<in> Q \<longrightarrow> (\<exists>q' Y. q = [Y]\<^sub>R # q') \<or> 
                \<rho> @ [[X]\<^sub>R, [Tock]\<^sub>E] \<noteq> intersect_refusal_trace Xa p @ q)) \<Longrightarrow> False"
            using case_assms case_assms2 apply (erule_tac x="\<rho> @ [[X]\<^sub>R, [Tock]\<^sub>E]" in allE, auto)
            using ctt_prefix_concat ctt_prefix_imp_prefix_subset not_contains_refusal_ctt_prefix_subset apply blast
            apply (erule_tac x="[]" in allE, auto)
            using CT0_CT1_empty CT0_Q CT1_Q apply blast
            by (metis intersect_refusal_trace_end_ref_imp_intersect_refusal_trace_end_ref_tock intersect_refusal_trace_idempotent)
        qed
        then show "contains_refusal \<rho> \<Longrightarrow> \<rho> @ [[X]\<^sub>R, [Tock]\<^sub>E] \<in> P \<Longrightarrow> \<rho> @ [[X]\<^sub>R, [Tock]\<^sub>E] \<notin> P \<triangle>\<^sub>U Q \<Longrightarrow> \<rho> @ [[Tock]\<^sub>E] \<in> P \<triangle>\<^sub>U Q"
          by auto
      next
        show "\<not> contains_refusal \<rho> \<Longrightarrow> \<rho> @ [[X]\<^sub>R, [Tock]\<^sub>E] \<in> P \<Longrightarrow> \<rho> @ [[X]\<^sub>R, [Tock]\<^sub>E] \<notin> P \<triangle>\<^sub>U Q \<Longrightarrow> False"
          unfolding UntimedInterruptCTT_def
        proof auto
          show "\<not> contains_refusal \<rho> \<Longrightarrow> \<rho> @ [[X]\<^sub>R, [Tock]\<^sub>E] \<in> P \<Longrightarrow>
            \<forall>p. contains_refusal p \<longrightarrow> p \<in> P \<longrightarrow> (\<exists>p'. p = p' @ [[Tick]\<^sub>E]) \<or> (\<exists>p' Y. p = p' @ [[Y]\<^sub>R]) \<or>
              (\<forall>q. q \<in> Q \<longrightarrow> (\<forall>Xa. [[Xa]\<^sub>R] \<in> Q \<longrightarrow> (\<exists>q' Y. q = [Y]\<^sub>R # q') \<or> 
                \<rho> @ [[X]\<^sub>R, [Tock]\<^sub>E] \<noteq> intersect_refusal_trace Xa p @ q)) \<Longrightarrow> False"
            using case_assms case_assms2 apply (erule_tac x="\<rho> @ [[X]\<^sub>R, [Tock]\<^sub>E]" in allE, auto)
            apply (metis append.assoc append.left_neutral append_Cons ctt_prefix_concat ctt_prefix_imp_prefix_subset not_contains_refusal_ctt_prefix_subset_end_nonref)
            apply (erule_tac x="[]" in allE, auto)
            using CT0_CT1_empty CT0_Q CT1_Q apply blast
            by (metis intersect_refusal_trace_end_ref_imp_intersect_refusal_trace_end_ref_tock intersect_refusal_trace_idempotent)
        qed
      next
        have "\<not> contains_refusal \<rho> \<Longrightarrow> \<rho> @ [[X]\<^sub>R, [Tock]\<^sub>E] \<in> P \<Longrightarrow> \<rho> @ [[X]\<^sub>R, [Tock]\<^sub>E] \<notin> P \<triangle>\<^sub>U Q \<Longrightarrow> False"
          unfolding UntimedInterruptCTT_def
        proof auto
          show "\<not> contains_refusal \<rho> \<Longrightarrow> \<rho> @ [[X]\<^sub>R, [Tock]\<^sub>E] \<in> P \<Longrightarrow>
            \<forall>p. contains_refusal p \<longrightarrow> p \<in> P \<longrightarrow> (\<exists>p'. p = p' @ [[Tick]\<^sub>E]) \<or> (\<exists>p' Y. p = p' @ [[Y]\<^sub>R]) \<or>
              (\<forall>q. q \<in> Q \<longrightarrow> (\<forall>Xa. [[Xa]\<^sub>R] \<in> Q \<longrightarrow> (\<exists>q' Y. q = [Y]\<^sub>R # q') \<or> 
                \<rho> @ [[X]\<^sub>R, [Tock]\<^sub>E] \<noteq> intersect_refusal_trace Xa p @ q)) \<Longrightarrow> False"
            using case_assms case_assms2 apply (erule_tac x="\<rho> @ [[X]\<^sub>R, [Tock]\<^sub>E]" in allE, auto)
            apply (metis append.assoc append.left_neutral append_Cons ctt_prefix_concat ctt_prefix_imp_prefix_subset not_contains_refusal_ctt_prefix_subset_end_nonref)
            apply (erule_tac x="[]" in allE, auto)
            using CT0_CT1_empty CT0_Q CT1_Q apply blast
            by (metis intersect_refusal_trace_end_ref_imp_intersect_refusal_trace_end_ref_tock intersect_refusal_trace_idempotent)
        qed
        then show "\<not> contains_refusal \<rho> \<Longrightarrow> \<rho> @ [[X]\<^sub>R, [Tock]\<^sub>E] \<in> P \<Longrightarrow> \<rho> @ [[X]\<^sub>R, [Tock]\<^sub>E] \<notin> P \<triangle>\<^sub>U Q \<Longrightarrow> \<rho> @ [[Tock]\<^sub>E] \<in> P \<triangle>\<^sub>U Q"
          by auto
      qed
      then have 1: "Y \<inter> {e. e \<noteq> Tock \<and> \<rho> @ [[e]\<^sub>E] \<in> P \<or> e = Tock \<and> \<rho> @ [[X]\<^sub>R, [e]\<^sub>E] \<in> P} = {}"
        using assm2 by auto
      have p_in_P: "p \<in> P"
        using case_assms CT1_P CT1_def ctt_prefix_concat ctt_prefix_imp_prefix_subset by blast
      have p_end: "(\<nexists>p'. p = p' @ [[Tick]\<^sub>E]) \<and> (\<nexists>p' Y. p = p' @ [[Y]\<^sub>R])"
      proof -
        have "cttWF (p @ [[Z]\<^sub>R])"
          by (simp add: P_wf case_assms(1))
        also have "(\<exists>p'. p = p' @ [[Tick]\<^sub>E]) \<or> (\<exists>p' Y. p = p' @ [[Y]\<^sub>R]) \<or> (\<exists>p'. p = p' @ [[Tock]\<^sub>E]) \<or> (\<exists>p' e. p = p' @ [[Event e]\<^sub>E]) \<or> p = []"
          by (metis cttevent.exhaust cttobs.exhaust rev_exhaust)
        then show ?thesis
          using calculation
        proof auto
          fix p'a
          show "cttWF (p'a @ [[Tick]\<^sub>E, [Z]\<^sub>R]) \<Longrightarrow> False"
            by (induct p'a rule:cttWF.induct, auto)
        next
          fix p'a Ya
          show "cttWF (p'a @ [[Ya]\<^sub>R, [Z]\<^sub>R]) \<Longrightarrow> False"
            by (induct p'a rule:cttWF.induct, auto)
        qed
      qed
      have \<rho>_contains_refusal_imp_p_contains_refusal: "contains_refusal \<rho> \<Longrightarrow> contains_refusal p"
        by (metis append_Nil2 case_assms(3) case_assms2 ctt_prefix_concat ctt_prefix_imp_prefix_subset intersect_refusal_trace_end_ref_imp_intersect_refusal_trace_end_event not_contains_refusal_append_event not_contains_refusal_ctt_prefix_subset not_contains_refusal_intersect_refusal_trace)
      have \<rho>_not_contains_refusal_imp_p_not_contains_refusal: "\<not> contains_refusal \<rho> \<Longrightarrow> \<not> contains_refusal p"
        by (metis append_Nil2 case_assms(3) case_assms2 contains_refusal_ctt_subset ctt_prefix_concat ctt_prefix_imp_prefix_subset intersect_refusal_trace_end_ref_imp_intersect_refusal_trace_end_event intersect_refusal_trace_subset not_contains_refusal_append_event not_contains_refusal_ctt_prefix_subset)
      have "{e. e \<noteq> Tock \<and> [[e]\<^sub>E] \<in> Q \<or> e = Tock \<and> [[W]\<^sub>R, [e]\<^sub>E] \<in> Q}
        \<subseteq> {e. e \<noteq> Tock \<and> \<rho> @ [[e]\<^sub>E] \<in> P \<triangle>\<^sub>U Q \<or> e = Tock \<and> \<rho> @ [[X]\<^sub>R, [e]\<^sub>E] \<in> P \<triangle>\<^sub>U Q}"
        unfolding UntimedInterruptCTT_def
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
        using CT1_P CT1_def case_assms(1) case_assms(3) case_assms2 intersect_refusal_trace_prefix_subset by fastforce
      have 4: "\<rho> @ [[X \<union> Y]\<^sub>R] \<in> P"
        using 1 3 CT2_P case_assms case_assms2 unfolding CT2_def by auto
      have 5: "[[W \<union> Y]\<^sub>R] \<in> Q"
        using 2 CT2_Q case_assms(2) case_assms2 unfolding CT2_def by (erule_tac x="[]" in allE, auto)
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
        unfolding UntimedInterruptCTT_def
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
        unfolding UntimedInterruptCTT_def
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
        using case_assms case_assms2 CT2_Q unfolding CT2_def by (erule_tac x="[W]\<^sub>R # q'" in allE, auto)
      then show "\<rho> @ [[X \<union> Y]\<^sub>R] \<in> P \<triangle>\<^sub>U Q"
        unfolding UntimedInterruptCTT_def
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
      unfolding UntimedInterruptCTT_def
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
      using CT2_Q case_assms(6) unfolding CT2_def by auto
    then show "intersect_refusal_trace Z p @ q @ [[X \<union> Y]\<^sub>R] \<in> P \<triangle>\<^sub>U Q"
      unfolding UntimedInterruptCTT_def
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
      unfolding UntimedInterruptCTT_def
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
      using CT2_Q case_assms unfolding CT2_def by auto
    then show "p @ q @ [[X \<union> Y]\<^sub>R] \<in> P \<triangle>\<^sub>U Q"
      unfolding UntimedInterruptCTT_def
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
  show "p @ [[Tick]\<^sub>E] \<in> P \<Longrightarrow> CT3_trace (p @ [[Tick]\<^sub>E])"
    by (metis CT3_def CT3_P)
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
  fix p q X
  show "p \<in> P \<Longrightarrow> q \<in> Q \<Longrightarrow> CT3_trace (intersect_refusal_trace X p @ q)"
    by (meson CT3_P CT3_Q CT3_append CT3_def CT3_trace_intersect_refusal_trace Q_wf)
next
  fix p q
  show "p \<in> P \<Longrightarrow> q \<in> Q \<Longrightarrow> CT3_trace (p @ q)"
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