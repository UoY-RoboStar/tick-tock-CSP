theory TickTock_Interrupt
  imports TickTock_Core TickTock_Basic_Ops TickTock_SeqComp
begin

subsection {* Intersecting a refusal with refusals in a trace *}

fun intersect_refusal_trace :: "'e ttevent set \<Rightarrow> 'e ttobs list \<Rightarrow> 'e ttobs list" where
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
  apply (induct s t rule:tt_prefix_subset.induct, auto)
  using tt_prefix_subset.simps(1) apply fastforce
  apply (metis Int_absorb1 tt_prefix_subset.simps(2) intersect_refusal_trace.simps(3))
  apply (metis tt_prefix_subset.simps(3) intersect_refusal_trace.simps(2))
  done

lemma tt_subset_of_intersect_refusal_trace:
  "s \<subseteq>\<^sub>C intersect_refusal_trace X t \<Longrightarrow> \<exists> r. r \<subseteq>\<^sub>C t \<and> s = intersect_refusal_trace X r"
  apply (induct s t rule:tt_subset.induct, auto)
  using tt_subset.simps(1) apply fastforce
  apply (metis Int_absorb1 tt_subset.simps(2) intersect_refusal_trace.simps(3))
  apply (metis tt_subset.simps(3) intersect_refusal_trace.simps(2))
  using tt_subset_refl tt_subset_same_length apply force
  done
  
lemma intersect_refusal_trace_subset:
  "intersect_refusal_trace X t \<subseteq>\<^sub>C t"
  by (induct t, auto, case_tac a, auto)

lemma intersect_refusal_trace_UNIV_subset_imp_subset:
  "intersect_refusal_trace UNIV s \<subseteq>\<^sub>C intersect_refusal_trace X t \<Longrightarrow> s \<subseteq>\<^sub>C t"
  apply (induct s t rule:tt_subset.induct, auto)
  apply (metis tt_subset.simps(6) tt_subset.simps(8) intersect_refusal_trace_subset list.exhaust)
  using tt_subset.simps(8) tt_subset_trans intersect_refusal_trace_subset by blast

lemma intersect_refusal_trace_append_subset:
  "intersect_refusal_trace X t @ s \<subseteq>\<^sub>C t @ s"
  by (simp add: tt_subset_combine tt_subset_refl intersect_refusal_trace_subset)

lemma intersect_refusal_trace_eq_imp_subset:
  "s = intersect_refusal_trace X t \<Longrightarrow> s \<subseteq>\<^sub>C t"
  by (induct s t rule:tt_subset.induct, auto, case_tac v, auto)

lemma intersect_refusal_trace_append_prefix_subset:
  "intersect_refusal_trace X t @ s \<lesssim>\<^sub>C t @ s"
  by (simp add: tt_subset_imp_prefix_subset intersect_refusal_trace_append_subset)

lemma intersect_refusal_trace_append_wf:
  "ttWF (t @ s) \<Longrightarrow> ttWF (intersect_refusal_trace X t @ s)"
  using tt_prefix_subset_ttWF intersect_refusal_trace_append_prefix_subset by blast

lemma intersect_refusal_trace_UNIV_identity:
  "intersect_refusal_trace UNIV t = t"
  by (induct t, auto, case_tac a, auto)  

lemma intersect_refusal_trace_idempotent:
  "intersect_refusal_trace X (intersect_refusal_trace X t) = intersect_refusal_trace X t"
  by (induct t, auto, case_tac a, auto)

lemma eq_intersect_refusal_trace_identity:
  "s = intersect_refusal_trace X t \<Longrightarrow> s = intersect_refusal_trace X s"
  by (induct s t rule:tt_subset.induct, auto)

lemma intersect_refusal_trace_end_ref_imp_intersect_refusal_trace_end_event:
  "s @ [[X]\<^sub>R] = intersect_refusal_trace Z (t @ [[Y]\<^sub>R]) \<Longrightarrow> s @ [[e]\<^sub>E] = intersect_refusal_trace Z (t @ [[e]\<^sub>E])"
  by (induct s t rule:tt_subset.induct, auto, case_tac v, auto, case_tac va, auto, case_tac a, auto)

lemma intersect_refusal_trace_end_ref_imp_intersect_refusal_trace_end_ref_tock:
  "s @ [[X]\<^sub>R] = intersect_refusal_trace Z (t @ [[Y]\<^sub>R]) \<Longrightarrow> s @ [[X]\<^sub>R, [Tock]\<^sub>E] = intersect_refusal_trace Z (t @ [[X]\<^sub>R, [Tock]\<^sub>E])"
  by (induct s t rule:tt_subset.induct, auto, case_tac v, auto, case_tac va, auto, case_tac a, auto)

lemma intersect_refusal_trace_refusal_subset: "\<rho> @ [X]\<^sub>R # \<sigma> = intersect_refusal_trace Y t \<Longrightarrow> X \<subseteq> Y"
  by (induct \<rho> t rule:tt_subset.induct, auto, case_tac v, auto)

lemma subset_intersect_refusal_trace_idempotent:
  "Y \<subseteq> Z \<Longrightarrow> intersect_refusal_trace Y t = intersect_refusal_trace Z (intersect_refusal_trace Y t)"
  by (induct t rule:intersect_refusal_trace.induct, auto)

lemma intersect_refusal_trace_refusal_subset_idempotent:
  "\<rho> @ [X]\<^sub>R # \<sigma> = intersect_refusal_trace Y t \<Longrightarrow> \<rho> @ [X \<union> Z]\<^sub>R # \<sigma> = intersect_refusal_trace (Y \<union> Z) (\<rho> @ [X \<union> Z]\<^sub>R # \<sigma>)"
  by (induct \<rho> t rule:tt_subset.induct, auto, case_tac v, auto, case_tac v, auto simp add: subset_intersect_refusal_trace_idempotent)

lemma tt_prefix_subset_intersect_refusal_trace_concat:
  "r \<lesssim>\<^sub>C intersect_refusal_trace Y s @ t \<Longrightarrow>
    r \<lesssim>\<^sub>C intersect_refusal_trace Y s
    \<or> (\<exists> t' s'. intersect_refusal_trace UNIV s' \<subseteq>\<^sub>C intersect_refusal_trace Y s \<and> t' \<lesssim>\<^sub>C t \<and> r = intersect_refusal_trace Y s' @ t')"
  using tt_prefix_subset_concat2[where r="r", where t="t", where s="intersect_refusal_trace Y s"]
proof (auto, erule_tac x="t'" in allE, auto, erule_tac x="s'" in allE, auto)
  fix t' s' t'a s'a t'b s'b
  assume "s' \<subseteq>\<^sub>C intersect_refusal_trace Y s" "\<not> intersect_refusal_trace UNIV s' \<subseteq>\<^sub>C intersect_refusal_trace Y s"
  then have "False"
    by (induct s' s rule:tt_subset.induct, auto)
  then show "s'b @ t'b \<lesssim>\<^sub>C intersect_refusal_trace Y s"
    by auto
next
  fix t' s' t'a s'a t'b s'b
  assume "s' \<subseteq>\<^sub>C intersect_refusal_trace Y s" "s' \<noteq> intersect_refusal_trace Y s'"
  then have "False"
    by (induct s' s rule:tt_subset.induct, auto)
  then show "s'b @ t'b \<lesssim>\<^sub>C intersect_refusal_trace Y s"
    by auto
qed

lemma eq_intersect_refusal_trace_append:
  "s @ t = intersect_refusal_trace X (s' @ t) \<Longrightarrow> s = intersect_refusal_trace X s'"
proof (induct s s' rule:tt_subset.induct, auto)
  fix vb va
  assume "[vb]\<^sub>E # va @ t = intersect_refusal_trace X t"
  then have "[vb]\<^sub>E # va @ t \<subseteq>\<^sub>C t"
    using intersect_refusal_trace_eq_imp_subset by auto
  then have "length ([vb]\<^sub>E # va @ t) = length t"
    using tt_subset_same_length by blast
  then show "False"
    by auto
next
  fix v va
  assume "v # va @ t = intersect_refusal_trace X t"
  then have "v # va @ t \<subseteq>\<^sub>C t"
    using intersect_refusal_trace_eq_imp_subset by auto
  then have "length (v # va @ t) = length t"
    using tt_subset_same_length by blast
  then show "False"
    by auto
next
  fix v va
  assume "t = intersect_refusal_trace X (v # va @ t)"
  then have "t \<subseteq>\<^sub>C v # va @ t"
    using intersect_refusal_trace_eq_imp_subset by auto
  then have "length t = length (v # va @ t)"
    using tt_subset_same_length by blast
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
    using tt_subset_same_length by blast
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
  by (induct s s' rule:tt_subset.induct, auto, case_tac v, auto)

subsection {* Checking if a trace contains a refusal *}

fun contains_refusal :: "'e ttobs list \<Rightarrow> bool" where
  "contains_refusal [] = False" |
  "contains_refusal ([X]\<^sub>R # s) = True" |
  "contains_refusal ([e]\<^sub>E # s) = contains_refusal s"

lemma not_contains_refusal_tt_prefix_subset:
  "\<not> contains_refusal t \<Longrightarrow> s \<lesssim>\<^sub>C t \<Longrightarrow> \<not> contains_refusal s"
  by (induct s t rule:tt_prefix_subset.induct, auto)

lemma not_contains_refusal_tt_prefix_subset_end_nonref:
  "\<not> contains_refusal t \<Longrightarrow> s \<lesssim>\<^sub>C t \<Longrightarrow> \<nexists> s' X. s = s' @ [[X]\<^sub>R]"
  by (induct s t rule:tt_prefix_subset.induct, auto simp add: Cons_eq_append_conv)

lemma not_contains_refusal_intersect_refusal_trace:
  "\<not> contains_refusal t \<Longrightarrow> intersect_refusal_trace X t = t"
  by (induct t rule:contains_refusal.induct, auto)

lemma not_contains_refusal_append_event:
  "\<not> contains_refusal t \<Longrightarrow> \<not> contains_refusal (t @ [[e]\<^sub>E])"
  by (induct t rule:contains_refusal.induct, auto)

lemma contains_refusal_tt_subset:
  "contains_refusal t \<Longrightarrow> s \<subseteq>\<^sub>C t \<Longrightarrow> contains_refusal s"
  by (induct s t rule:tt_subset.induct, auto)

lemma not_contains_refusal_tt_subset:
  "\<not> contains_refusal t \<Longrightarrow> s \<subseteq>\<^sub>C t \<Longrightarrow> \<not> contains_refusal s"
  by (induct s t rule:tt_subset.induct, auto)

lemma event_append_wf:
  "\<And>q. \<exists> p' e. p = p' @ [[Event e]\<^sub>E] \<Longrightarrow> ttWF (p) \<Longrightarrow> ttWF (q) \<Longrightarrow> ttWF (p @ q)"
proof (auto, induct p rule:ttWF.induct, auto)
  fix q p' \<sigma> :: "'a ttobs list"
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
  fix q p' \<sigma> :: "'a ttobs list"
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
  next
    fix p''
    assume "p' = [X]\<^sub>R # [Tock]\<^sub>E # p''" "Tock \<in> X"
    then show "False"
      using assm3(1) by auto
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
  fix q p' \<sigma> :: "'a ttobs list"
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
  next
    show "Tock \<in> X \<Longrightarrow> False"
      using assm3(1) by (induct p' rule:ttWF.induct, auto)
  qed
next
  fix q p' \<sigma> :: "'a ttobs list"
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
  next
    show "Tock \<in> X \<Longrightarrow> False"
      using assm3 by (induct p' rule:ttWF.induct, auto)
  next
    show "Tock \<in> Xa \<Longrightarrow> False"
      using assm3(1) by (induct p' rule:ttWF.induct, auto)
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

lemma end_refusal_start_refusal_append_wfw:
  "ttWFw (p @ [[X]\<^sub>R]) \<Longrightarrow> ttWFw ([Y]\<^sub>R # q) \<Longrightarrow> ttWFw ((p @ [[Z]\<^sub>R]) @ q)"
  by (induct p rule:ttWFw.induct, auto, induct q rule:ttWFw.induct, auto)

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
    using assms apply auto
    using event_append_wf apply fastforce
    using tock_append_wf by fastforce
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
  by (metis append.left_neutral append_Cons append_butlast_last_id ttobs.distinct(1) last_snoc)

lemma add_Tick_refusal_trace_not_end_refusal:
  "\<nexists> s X. t = s  @ [[X]\<^sub>R] \<Longrightarrow> \<nexists> s X. add_Tick_refusal_trace t = s  @ [[X]\<^sub>R]"
  apply (auto, induct t rule:add_Tick_refusal_trace.induct, auto)
  apply (metis (no_types, hide_lams) add_Tick_refusal_trace.simps(2) append_Cons append_butlast_last_id contains_refusal.elims(3) contains_refusal.simps(1) contains_refusal_add_Tick_refusal_trace last.simps last_appendR list.distinct(1))
  by (case_tac s, auto, case_tac t rule:add_Tick_refusal_trace.cases, auto, fastforce)


subsection {* Time-synchronising Interrupt *}

fun filter_tocks :: "'e ttobs list \<Rightarrow> 'e ttobs list" where
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

lemma tt_prefix_subset_filter_tocks:
  "ttWF s \<Longrightarrow> ttWF t \<Longrightarrow> s \<lesssim>\<^sub>C t \<Longrightarrow> filter_tocks s \<lesssim>\<^sub>C filter_tocks t"
  by (induct s t rule:ttWF2.induct, auto)

lemma tt_subset_filter_tocks:
  "ttWF s \<Longrightarrow> ttWF t \<Longrightarrow> s \<subseteq>\<^sub>C t \<Longrightarrow> filter_tocks s \<subseteq>\<^sub>C filter_tocks t"
  by (induct s t rule:ttWF2.induct, auto)

definition TimeSyncInterruptTT :: "'e ttobs list set \<Rightarrow> 'e ttobs list set \<Rightarrow> 'e ttobs list set" (infixl "\<triangle>\<^sub>T" 58) where
  "P \<triangle>\<^sub>T Q = {t. \<exists> p q. p @ [[Tick]\<^sub>E] \<in> P \<and> q \<in> Q \<and> filter_tocks p = q \<and> t = p @ [[Tick]\<^sub>E]}
    \<union> {t. \<exists> p X Y Z q. p @ [[X]\<^sub>R] \<in> P \<and> filter_tocks p = q \<and> q @ [[Y]\<^sub>R] \<in> Q
      \<and> Z \<subseteq> X \<union> Y \<and> {e\<in>X. e \<noteq> Tock} = {e\<in>Y. e \<noteq> Tock} \<and> t = p @ [[Z]\<^sub>R]}
    \<union> {t. \<exists> p q1 q2. p \<in> P \<and> (\<nexists> p'. p = p' @ [[Tick]\<^sub>E]) \<and> (\<nexists> p' Y. p = p' @ [[Y]\<^sub>R])
      \<and> filter_tocks p = q1 \<and> q1 @ q2 \<in> Q \<and> (\<nexists> q' Y. q2 = [Y]\<^sub>R # q') \<and> t =  p @ q2}"

lemma TimeSyncInterruptTT_wf:
  assumes "\<forall>x\<in>P. ttWF x" "\<forall>x\<in>Q. ttWF x"
  shows "\<forall>x\<in>(P \<triangle>\<^sub>T Q). ttWF x"
  unfolding TimeSyncInterruptTT_def
proof (safe, simp_all)
  fix p
  show "p @ [[Tick]\<^sub>E] \<in> P \<Longrightarrow> ttWF (p @ [[Tick]\<^sub>E])"
    using assms by auto
next
  fix p X Y Z
  show "p @ [[X]\<^sub>R] \<in> P \<Longrightarrow> ttWF (p @ [[Z]\<^sub>R])"
    using assms(1) end_refusal_start_refusal_append_wfw ttWF_is_ttWFw_ttWFx ttWFx_trace_end_refusal_change by fastforce
next
  fix p q2
  assume "filter_tocks p @ q2 \<in> Q"
  then have "ttWF q2"
    using assms(2) filter_tocks_in_tocks tocks_append_wf2 by blast
  then show "p \<in> P \<Longrightarrow> \<forall>p'. p \<noteq> p' @ [[Tick]\<^sub>E] \<Longrightarrow> \<forall>p' Y. p \<noteq> p' @ [[Y]\<^sub>R] \<Longrightarrow> ttWF (p @ q2)"
    by (metis Collect_mono_iff assms(1) nontick_event_end_append_wf order_refl ttWF_is_ttWFw_ttWFx ttWFx_append)
qed

lemma TT0_TimeSyncInterrupt:
  assumes "TT0 P" "TT0 Q" "TT1 P" "TT1 Q"
  shows "TT0 (P \<triangle>\<^sub>T Q)"
  unfolding TimeSyncInterruptTT_def TT0_def
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
  fix \<rho> \<sigma> :: "'a ttobs list"
  assume assm1: "\<rho> \<lesssim>\<^sub>C \<sigma>"
  assume assm2: "\<sigma> \<in> P \<triangle>\<^sub>T Q"
  then have "(\<exists>p q. p @ [[Tick]\<^sub>E] \<in> P \<and> q \<in> Q \<and> filter_tocks p = q \<and> \<sigma> = p @ [[Tick]\<^sub>E])
    \<or> (\<exists>p X Y Z q. p @ [[X]\<^sub>R] \<in> P \<and>  filter_tocks p = q \<and> q @ [[Y]\<^sub>R] \<in> Q
      \<and> Z \<subseteq> X \<union> Y \<and> {e \<in> X. e \<noteq> Tock} = {e \<in> Y. e \<noteq> Tock} \<and> \<sigma> = p @ [[Z]\<^sub>R])
    \<or> (\<exists>p q1 q2. p \<in> P \<and> (\<nexists>p'. p = p' @ [[Tick]\<^sub>E]) \<and> (\<nexists>p' Y. p = p' @ [[Y]\<^sub>R])
      \<and> filter_tocks p = q1 \<and> q1 @ q2 \<in> Q \<and> (\<nexists>q' Y. q2 = [Y]\<^sub>R # q') \<and> \<sigma> = p @ q2)"
    unfolding TimeSyncInterruptTT_def by auto
  then show "\<rho> \<in> P \<triangle>\<^sub>T Q"
  proof (safe, simp_all)
    fix p
    assume case_assms: "p @ [[Tick]\<^sub>E] \<in> P" "filter_tocks p \<in> Q" "\<sigma> = p @ [[Tick]\<^sub>E]"
    then have \<rho>_in_P: "\<rho> \<in> P"
      using TT1_def assm1 assms(3) by blast
    have 1: "filter_tocks \<rho> \<lesssim>\<^sub>C filter_tocks \<sigma>"
      using \<rho>_in_P assm1 assms(1) case_assms(1) case_assms(3) tt_prefix_subset_filter_tocks by blast
    have 2: "filter_tocks \<sigma> = filter_tocks p"
      by (simp add: case_assms, induct p rule:filter_tocks.induct, auto)
    have filter_tocks_\<rho>_in_Q: "filter_tocks \<rho> \<in> Q"
      using 1 2 TT1_def assms(4) case_assms(2) by auto
    have \<rho>_cases: "(\<exists> p' X. \<rho> = p' @ [[Tick]\<^sub>E]) \<or> (\<exists> p' X. \<rho> = p' @ [[X]\<^sub>R]) \<or> ((\<nexists>p'. \<rho> = p' @ [[Tick]\<^sub>E]) \<and> (\<nexists>p' Y. \<rho> = p' @ [[Y]\<^sub>R]))"
      by auto
    then show "\<rho> \<in> P \<triangle>\<^sub>T Q"
      unfolding TimeSyncInterruptTT_def
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
        using ttWF.simps(12) tt_prefix_subset_ttWF apply blast
        apply (meson ttWF.simps(11) tt_prefix_subset_ttWF)
        using ttWF.simps(13) tt_prefix_subset_ttWF apply blast
        using ttWF.simps(8) tt_prefix_subset_ttWF apply blast
        using ttWF.simps(6) tt_prefix_subset_ttWF by blast
      then have 1: "filter_tocks (p' @ [[X]\<^sub>R, [Tock]\<^sub>E]) \<lesssim>\<^sub>C filter_tocks (p @ [[Tick]\<^sub>E])"
        using ttWF_\<sigma> tt_prefix_subset_ttWF tt_prefix_subset_filter_tocks by blast
      have 2: "filter_tocks (p @ [[Tick]\<^sub>E]) = filter_tocks (p)"
        by (induct p rule:filter_tocks.induct, auto)
      have 3: "filter_tocks (p' @ [[X]\<^sub>R, [Tock]\<^sub>E]) = filter_tocks p' @ [[X]\<^sub>R, [Tock]\<^sub>E]"
        by (induct p' rule:filter_tocks.induct, auto)
      have 4: "filter_tocks p' @ [[X]\<^sub>R, [Tock]\<^sub>E]  \<lesssim>\<^sub>C filter_tocks p"
        using 1 2 3 by auto
      have 5: "filter_tocks p' @ [[X]\<^sub>R]  \<lesssim>\<^sub>C filter_tocks p' @ [[X]\<^sub>R, [Tock]\<^sub>E]"
        by (induct p' rule:filter_tocks.induct, auto)
      then have "filter_tocks p' @ [[X]\<^sub>R]  \<lesssim>\<^sub>C filter_tocks p"
        using 4 tt_prefix_subset_trans by blast
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
    thm tt_prefix_subset_filter_tocks
    then have "\<rho> \<lesssim>\<^sub>C p \<or> \<rho> \<subseteq>\<^sub>C p @ [[Z]\<^sub>R]"
      apply (induct \<rho> p rule:tt_prefix_subset.induct, auto, case_tac x, auto)
      using tt_prefix_subset.simps(1) tt_prefix_subset_antisym tt_subset_refl by blast
    also have "\<rho> \<subseteq>\<^sub>C p @ [[Z]\<^sub>R] \<Longrightarrow> \<exists> p' Z'. Z' \<subseteq> X \<union> Y \<and> \<rho> = p' @ [[Z']\<^sub>R] \<and> p' \<subseteq>\<^sub>C p"
      apply (induct \<rho> p rule:tt_subset.induct, auto, rule_tac x="[]" in exI, simp, case_tac v, auto)
      using case_assms(4) tt_subset_same_length by (auto, force)
    then have "\<rho> \<lesssim>\<^sub>C p \<or> (\<exists> p' Z'. Z' \<subseteq> X \<union> Y \<and> \<rho> = p' @ [[Z']\<^sub>R] \<and> p' \<subseteq>\<^sub>C p)"
      using calculation by auto
    then show "\<rho> \<in> P \<triangle>\<^sub>T Q"
    proof auto
      assume case_assms2: "\<rho> \<lesssim>\<^sub>C p"
      then have \<rho>_in_P: "\<rho> \<in> P"
        using assms(3) case_assms(1) unfolding TT1_def by (meson tt_prefix_concat tt_prefix_imp_prefix_subset) 
      have 1: "filter_tocks \<rho> \<lesssim>\<^sub>C filter_tocks \<sigma>"
        by (metis TimeSyncInterruptTT_wf \<rho>_in_P assm1 assm2 assms(1) assms(2) tt_prefix_subset_filter_tocks)
      have 2: "filter_tocks \<sigma> = filter_tocks p"
        by (simp add: case_assms, induct p rule:filter_tocks.induct, auto)
      have filter_tocks_\<rho>_in_Q: "filter_tocks \<rho> \<in> Q"
        by (metis "1" "2" TT1_def assms(4) case_assms(3) tt_prefix_concat tt_prefix_subset_tt_prefix_trans)
      have \<rho>_cases: "(\<exists> p' X. \<rho> = p' @ [[Tick]\<^sub>E]) \<or> (\<exists> p' X. \<rho> = p' @ [[X]\<^sub>R]) \<or> ((\<nexists>p'. \<rho> = p' @ [[Tick]\<^sub>E]) \<and> (\<nexists>p' Y. \<rho> = p' @ [[Y]\<^sub>R]))"
        by auto
      then have \<rho>_cases: " (\<exists> p' X. \<rho> = p' @ [[X]\<^sub>R]) \<or> ((\<nexists>p'. \<rho> = p' @ [[Tick]\<^sub>E]) \<and> (\<nexists>p' Y. \<rho> = p' @ [[Y]\<^sub>R]))"
      proof auto
        fix p'a
        assume case_assm3: "\<rho> = p'a @ [[Tick]\<^sub>E]"
        have "\<exists> \<rho>'. \<rho>' \<le>\<^sub>C p \<and> \<rho> \<subseteq>\<^sub>C \<rho>'"
          using case_assms2 tt_prefix_subset_imp_tt_subset_tt_prefix by blast
        then have "\<exists> \<rho>' p'. p = \<rho>' @ p' \<and> \<rho> \<subseteq>\<^sub>C \<rho>'"
          using tt_prefix_decompose by blast
        then obtain \<rho>' p' where 1: "p = \<rho>' @ p' \<and> \<rho> \<subseteq>\<^sub>C \<rho>'"
          by auto
        then have "\<exists> p'a'. \<rho>' = p'a' @ [[Tick]\<^sub>E]"
          using case_assm3
        proof auto
          fix \<rho>' p'
          show "p'a @ [[Tick]\<^sub>E] \<subseteq>\<^sub>C \<rho>' \<Longrightarrow> \<exists>p'a'. \<rho>' = p'a' @ [[Tick]\<^sub>E]"
            apply (induct p'a \<rho>' rule:tt_subset.induct, auto, case_tac v, auto)
            using tt_subset.elims(2) by fastforce+
        qed
        then obtain p'a' where "ttWF (p'a' @ [[Tick]\<^sub>E] @ p' @ [[X]\<^sub>R])"
          using 1 assms(1) case_assms(1) ttWF_prefix_is_ttWF by fastforce
        then show False
          by (induct p'a' rule:ttWF.induct, auto, induct p' rule:ttWF.induct, auto)
      qed
      then show "\<rho> \<in> P \<triangle>\<^sub>T Q"
        unfolding TimeSyncInterruptTT_def
      proof auto
        fix p' X'
        have ttWF_\<sigma>: "ttWF (p @ [[Z]\<^sub>R])"
          using TimeSyncInterruptTT_wf assm2 assms(1) assms(2) case_assms(2) by blast
        assume case_assms3: "\<rho> = p' @ [[X']\<^sub>R]"
        then have \<rho>_prefix_subset_\<sigma>: "p' @ [[X']\<^sub>R] \<lesssim>\<^sub>C p @ [[Z]\<^sub>R]"
          using assm1 case_assms(2) by blast
        then have 1: "p' @ [[X']\<^sub>R, [Tock]\<^sub>E] \<lesssim>\<^sub>C p @ [[Z]\<^sub>R]"
          using ttWF_\<sigma> case_assms2 case_assms3
        proof auto
          show "p' @ [[X']\<^sub>R] \<lesssim>\<^sub>C p @ [[Z]\<^sub>R] \<Longrightarrow> ttWF (p @ [[Z]\<^sub>R]) \<Longrightarrow> p' @ [[X']\<^sub>R] \<lesssim>\<^sub>C p \<Longrightarrow> p' @ [[X']\<^sub>R, [Tock]\<^sub>E] \<lesssim>\<^sub>C p @ [[Z]\<^sub>R]"
            apply (induct p' p rule:ttWF2.induct, auto)
            using ttWF.simps(12) tt_prefix_subset_ttWF apply blast
            apply (meson ttWF.simps(11) tt_prefix_subset_ttWF)
            using ttWF.simps(13) tt_prefix_subset_ttWF apply blast
            using ttWF.simps(8) tt_prefix_subset_ttWF apply blast
            using ttWF.simps(6) tt_prefix_subset_ttWF by blast
        qed
        then have 2: "p' @ [[X']\<^sub>R, [Tock]\<^sub>E] \<lesssim>\<^sub>C p"
          using ttWF_\<sigma> case_assms3 case_assms2
        proof auto
          show "p' @ [[X']\<^sub>R, [Tock]\<^sub>E] \<lesssim>\<^sub>C p @ [[Z]\<^sub>R] \<Longrightarrow> ttWF (p @ [[Z]\<^sub>R]) \<Longrightarrow> p' @ [[X']\<^sub>R] \<lesssim>\<^sub>C p \<Longrightarrow> p' @ [[X']\<^sub>R, [Tock]\<^sub>E] \<lesssim>\<^sub>C p"
            apply (induct p' p rule:ttWF2.induct, auto)
            using ttWF.simps(12) tt_prefix_subset_ttWF apply blast
            apply (meson ttWF.simps(11) tt_prefix_subset_ttWF)
            using ttWF.simps(13) tt_prefix_subset_ttWF apply blast
            using ttWF.simps(8) tt_prefix_subset_ttWF apply blast
            using ttWF.simps(6) tt_prefix_subset_ttWF by blast
        qed
        then have 3: "filter_tocks (p' @ [[X']\<^sub>R, [Tock]\<^sub>E]) \<lesssim>\<^sub>C filter_tocks p"
          using ttWF_\<sigma> ttWF_prefix_is_ttWF tt_prefix_subset_ttWF tt_prefix_subset_filter_tocks by blast
        have 4: "filter_tocks (p' @ [[X']\<^sub>R, [Tock]\<^sub>E]) = filter_tocks p' @ [[X']\<^sub>R, [Tock]\<^sub>E]"
          by (induct p' rule:filter_tocks.induct, auto)
        have 5: "filter_tocks p' @ [[X']\<^sub>R, [Tock]\<^sub>E]  \<lesssim>\<^sub>C filter_tocks p"
          using 3 4 by auto
        have 6: "filter_tocks p' @ [[X']\<^sub>R]  \<lesssim>\<^sub>C filter_tocks p' @ [[X']\<^sub>R, [Tock]\<^sub>E]"
          by (induct p' rule:filter_tocks.induct, auto)
        then have "filter_tocks p' @ [[X']\<^sub>R]  \<lesssim>\<^sub>C filter_tocks p"
          using 5 tt_prefix_subset_trans by blast
        then have "filter_tocks p' @ [[X']\<^sub>R] \<in> Q"
          by (meson TT1_def assms(4) case_assms(3) tt_prefix_concat tt_prefix_imp_prefix_subset)
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
        by (simp add: case_assms2(2) tt_subset_combine)
      then have p'_X_in_P: "p' @ [[X]\<^sub>R] \<in> P"
        using assms(3) case_assms(1) tt_subset_imp_prefix_subset unfolding TT1_def by blast
      have "filter_tocks p' \<subseteq>\<^sub>C filter_tocks p"
        using assms(1) case_assms(1) case_assms2(2) ttWF_prefix_is_ttWF tt_prefix_subset_ttWF tt_subset_filter_tocks tt_subset_imp_prefix_subset by blast
      then have "filter_tocks p' @ [[Y]\<^sub>R] \<subseteq>\<^sub>C filter_tocks p @ [[Y]\<^sub>R]"
        by (simp add: tt_subset_combine)
      then have "filter_tocks p' @ [[Y]\<^sub>R] \<lesssim>\<^sub>C filter_tocks p @ [[Y]\<^sub>R]"
        using tt_subset_imp_prefix_subset by blast 
      then have "filter_tocks p' @ [[Y]\<^sub>R] \<in> Q"
        using assms(4) case_assms(3) tt_subset_imp_prefix_subset unfolding TT1_def by blast
      then show "p' @ [[Z']\<^sub>R] \<in> P \<triangle>\<^sub>T Q"
        unfolding TimeSyncInterruptTT_def using p'_X_in_P case_assms case_assms2 by auto
    qed
  next
    fix p q2
    assume case_assms: "p \<in> P" "\<forall>p'. p \<noteq> p' @ [[Tick]\<^sub>E]" "\<forall>p' Y. p \<noteq> p' @ [[Y]\<^sub>R]"
        "filter_tocks p @ q2 \<in> Q" "\<forall>q' Y. q2 \<noteq> [Y]\<^sub>R # q'" "\<sigma> = p @ q2"
    have "\<rho> \<lesssim>\<^sub>C p \<or> (\<exists> p' q'. q' \<lesssim>\<^sub>C q2 \<and> p' \<subseteq>\<^sub>C p \<and> \<rho> = p' @ q')"
      using assm1 case_assms(6) tt_prefix_subset_concat2 by blast
    then show "\<rho> \<in> P \<triangle>\<^sub>T Q"
      unfolding TimeSyncInterruptTT_def
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
          using tt_prefix_subset_ttWF p_wf by blast
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
            using case_assms2 case_assms3 tt_prefix_subset_ttWF p_wf by blast
          have "p' @ [[Y]\<^sub>R] \<lesssim>\<^sub>C p"
            using case_assms2 case_assms3 by auto
          then have "p' @ [[Y]\<^sub>R, [Tock]\<^sub>E] \<lesssim>\<^sub>C p"
            using case_assms(3) p_wf p'_wf by (induct p' p rule:ttWF2.induct, auto, fastforce+)
          then have 1: "filter_tocks (p' @ [[Y]\<^sub>R, [Tock]\<^sub>E]) \<lesssim>\<^sub>C filter_tocks p"
            using tt_prefix_subset_ttWF tt_prefix_subset_filter_tocks p_wf by blast
          have "filter_tocks (p' @ [[Y]\<^sub>R, [Tock]\<^sub>E]) = filter_tocks p' @ [[Y]\<^sub>R, [Tock]\<^sub>E]"
            by (induct p' rule:filter_tocks.induct, auto)
          then have "filter_tocks p' @ [[Y]\<^sub>R]  \<lesssim>\<^sub>C filter_tocks (p' @ [[Y]\<^sub>R, [Tock]\<^sub>E])"
            using tt_prefix_subset_same_front by fastforce
          then have "filter_tocks p' @ [[Y]\<^sub>R] \<lesssim>\<^sub>C filter_tocks p"
            using "1" tt_prefix_subset_trans by blast
          then show "filter_tocks p' @ [[Y]\<^sub>R] \<in> Q"
            by (meson TT1_def assms(4) case_assms(4) tt_prefix_concat tt_prefix_imp_prefix_subset)
        qed
        then show "\<exists>p X. p @ [[X]\<^sub>R] \<in> P \<and> (\<exists>Ya. filter_tocks p @ [[Ya]\<^sub>R] \<in> Q \<and> Y \<subseteq> X \<union> Ya \<and> {e \<in> X. e \<noteq> Tock} = {e \<in> Ya. e \<noteq> Tock} \<and> p' = p)"
          using TT1_def assms(3) case_assms(1) case_assms2 case_assms3 by blast
      next
        assume case_assms3: "\<forall>p'. \<rho> \<noteq> p' @ [[Tick]\<^sub>E]" "\<forall>p' Y. \<rho> \<noteq> p' @ [[Y]\<^sub>R]"
        have "filter_tocks \<rho> \<lesssim>\<^sub>C filter_tocks p"
          using assms(1) case_assms(1) case_assms2 tt_prefix_subset_ttWF tt_prefix_subset_filter_tocks by blast
        then have "filter_tocks \<rho> \<in> Q"
          by (meson TT1_def assms(4) case_assms(4) tt_prefix_concat tt_prefix_imp_prefix_subset)
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
        using case_assms2(2) case_assms(2) case_assms(3) apply (induct p' p rule:tt_subset.induct, auto)
        by (smt append_butlast_last_id tt_subset_same_length last.simps last_appendR length_0_conv list.distinct(1))+
      have p'_in_P: "p' \<in> P"
        using TT1_def assms(3) case_assms(1) case_assms2(2) tt_subset_imp_prefix_subset by blast
      then have 2: "filter_tocks p' \<subseteq>\<^sub>C filter_tocks p"
        by (simp add: assms(1) case_assms(1) case_assms2(2) tt_subset_filter_tocks)
      then have "filter_tocks p' @ q' \<lesssim>\<^sub>C filter_tocks p' @ q2"
        using case_assms2(1) tt_prefix_subset_same_front by blast
      then have "filter_tocks p' @ q' \<lesssim>\<^sub>C filter_tocks p @ q2"
        using "2" tt_prefix_subset_trans tt_subset_combine tt_subset_imp_prefix_subset tt_subset_refl by blast
      then have "filter_tocks p' @ q' \<in> Q"
        using TT1_def assms(4) case_assms(4) by blast
      then show "\<forall>p. p \<in> P \<longrightarrow> (\<exists>p'. p = p' @ [[Tick]\<^sub>E]) \<or> (\<exists>p' Y. p = p' @ [[Y]\<^sub>R]) \<or>
          (\<forall>q2. filter_tocks p @ q2 \<in> Q \<longrightarrow> (\<exists>q' Y. q2 = [Y]\<^sub>R # q') \<or> p' @ q' \<noteq> p @ q2) \<Longrightarrow>
        \<exists>p X. p @ [[X]\<^sub>R] \<in> P \<and> (\<exists>Y. filter_tocks p @ [[Y]\<^sub>R] \<in> Q \<and> (\<exists>Z\<subseteq>X \<union> Y. {e \<in> X. e \<noteq> Tock} = {e \<in> Y. e \<noteq> Tock} \<and> p' @ q' = p @ [[Z]\<^sub>R]))"
        using p'_in_P 1 apply (erule_tac x="p'" in allE, auto, erule_tac x="q'" in allE, auto)
        by (metis case_assms(5) case_assms2(1) contains_refusal.cases tt_prefix_subset.simps(1) tt_prefix_subset.simps(5) tt_prefix_subset_antisym)
    qed
  qed
qed

lemma TT2w_TimeSyncInterrupt:
  assumes P_wf: "\<forall>x\<in>P. ttWF x"
  assumes TT1_P: "TT1 P" and TT1_Q: "TT1 Q"
  assumes TT2w_P: "TT2w P" and TT2w_Q: "TT2w Q"
  assumes ttWFx_P: "ttWFx P" and ttWFx_Q: "ttWFx Q"
  shows "TT2w (P \<triangle>\<^sub>T Q)"
  unfolding TT2w_def
proof auto
  fix \<rho> X Y
  assume assm1: "\<rho> @ [[X]\<^sub>R] \<in> P \<triangle>\<^sub>T Q"
  assume assm2: "Y \<inter> {e. e \<noteq> Tock \<and> \<rho> @ [[e]\<^sub>E] \<in> P \<triangle>\<^sub>T Q \<or> e = Tock \<and> \<rho> @ [[X]\<^sub>R, [e]\<^sub>E] \<in> P \<triangle>\<^sub>T Q} = {}"
  have "(\<exists> Z W q. \<rho> @ [[Z]\<^sub>R] \<in> P \<and> filter_tocks \<rho> = q \<and> q @ [[W]\<^sub>R] \<in> Q \<and> X \<subseteq> Z \<union> W \<and> {e \<in> Z. e \<noteq> Tock} = {e \<in> W. e \<noteq> Tock})
    \<or> (\<exists>p q1 q2. p \<in> P \<and> (\<nexists>p'. p = p' @ [[Tick]\<^sub>E]) \<and> (\<nexists>p' Y. p = p' @ [[Y]\<^sub>R]) \<and> filter_tocks p = q1 \<and>
      q1 @ q2 @ [[X]\<^sub>R] \<in> Q \<and> (\<nexists>q' Y. q2 @ [[X]\<^sub>R] = [Y]\<^sub>R # q') \<and> \<rho> @ [[X]\<^sub>R] = p @ q2 @ [[X]\<^sub>R])"
    using assm1 unfolding TimeSyncInterruptTT_def
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
      using TT1_P TT1_def case_assms(1) tt_prefix_concat tt_prefix_imp_prefix_subset by blast
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
      unfolding TimeSyncInterruptTT_def
    proof (safe, simp_all)
      fix x
      assume "\<rho> @ [[x]\<^sub>E] \<in> P" "x \<noteq> Tock"
      then show "\<forall>p. p \<in> P \<longrightarrow> (\<exists>p'. p = p' @ [[Tick]\<^sub>E]) \<or> (\<exists>p' Y. p = p' @ [[Y]\<^sub>R]) \<or>
          (\<forall>q2. filter_tocks p @ q2 \<in> Q \<longrightarrow> (\<exists>q' Y. q2 = [Y]\<^sub>R # q') \<or> \<rho> @ [[x]\<^sub>E] \<noteq> p @ q2) \<Longrightarrow>
        \<rho> @ [[Tick]\<^sub>E] \<in> P \<and> filter_tocks \<rho> \<in> Q \<and> x = Tick"
        apply (cases x, auto, erule_tac x="\<rho> @ [[Event x1]\<^sub>E]" in allE, auto)
        apply (metis TT1_Q TT1_def append_Nil2 case_assms(2) tt_prefix_concat tt_prefix_imp_prefix_subset filter_tocks_end_event list.simps(3))
        by (meson TT1_Q TT1_def case_assms(2) tt_prefix_concat tt_prefix_imp_prefix_subset)
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
      unfolding TimeSyncInterruptTT_def
    proof (safe, simp_all)  
      assume assm: "\<rho> @ [[Z]\<^sub>R, [Tock]\<^sub>E] \<in> P" "filter_tocks \<rho> @ [[W]\<^sub>R, [Tock]\<^sub>E] \<in> Q"
      then have Tock_notin_Z: "Tock \<notin> Z \<and> Tock \<notin> W"
        using ttWFx_P ttWFx_Q ttWFx_any_cons_end_tock by blast
      then have "Z = W"
        using Collect_mono Collect_mono_iff case_assms(4) by auto
      then have "\<rho> @ [[X]\<^sub>R, [Tock]\<^sub>E] \<in> P \<and> filter_tocks \<rho> @ [[X]\<^sub>R, [Tock]\<^sub>E] \<in> Q"
        using case_assms(3) apply auto
        apply (metis TT1_P TT1_def assm(1) tt_prefix_subset.simps(2) tt_prefix_subset_refl tt_prefix_subset_same_front)
        by (metis TT1_Q TT1_def assm(2) tt_prefix_subset.simps(2) tt_prefix_subset_refl tt_prefix_subset_same_front)
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
          using TT2w_P case_assms(1) unfolding TT2w_def by auto
        have "{e\<in>Y. e \<noteq> Tock} \<inter> {e. e \<noteq> Tock \<and> filter_tocks \<rho> @ [[e]\<^sub>E] \<in> Q \<or> e = Tock \<and> filter_tocks \<rho> @ [[W]\<^sub>R, [e]\<^sub>E] \<in> Q} = {}"
          using Q_nontock_inter by auto
        then have \<rho>_W_Y_in_Q: "filter_tocks \<rho> @ [[W \<union> {e\<in>Y. e \<noteq> Tock}]\<^sub>R] \<in> Q"
          using TT2w_Q case_assms(2) unfolding TT2w_def by auto
        show "\<rho> @ [[X \<union> Y]\<^sub>R] \<in> P \<triangle>\<^sub>T Q"
          using \<rho>_Z_Y_in_P \<rho>_W_Y_in_Q unfolding TimeSyncInterruptTT_def apply (auto)
          apply (rule_tac x="\<rho>" in exI, auto, rule_tac x="Z \<union> Y" in exI, auto)
          using case_assms by (rule_tac x="W \<union> {e\<in>Y. e \<noteq> Tock}" in exI, auto)
      next
        assume case_assms2: "{e \<in> Y. e = Tock} \<inter> {e. e = Tock \<and> filter_tocks \<rho> @ [[W]\<^sub>R, [e]\<^sub>E] \<in> Q} = {}"
        then have "Y \<inter> {e. e \<noteq> Tock \<and> filter_tocks \<rho> @ [[e]\<^sub>E] \<in> Q \<or> e = Tock \<and> filter_tocks \<rho> @ [[W]\<^sub>R, [e]\<^sub>E] \<in> Q} = {}"
          using Q_nontock_inter by auto
        then have \<rho>_W_Y_in_Q: "filter_tocks \<rho> @ [[W \<union> Y]\<^sub>R] \<in> Q"
          using TT2w_Q case_assms(2) unfolding TT2w_def by auto
        have "{e\<in>Y. e \<noteq> Tock} \<inter> {e. e \<noteq> Tock \<and> \<rho> @ [[e]\<^sub>E] \<in> P \<or> e = Tock \<and> \<rho> @ [[Z]\<^sub>R, [e]\<^sub>E] \<in> P} = {}"
          using P_nontock_inter by auto
        then have \<rho>_Z_Y_in_P: "\<rho> @ [[Z \<union> {e\<in>Y. e \<noteq> Tock}]\<^sub>R] \<in> P"
          using TT2w_P case_assms(1) unfolding TT2w_def by auto
        show "\<rho> @ [[X \<union> Y]\<^sub>R] \<in> P \<triangle>\<^sub>T Q"
          using \<rho>_Z_Y_in_P \<rho>_W_Y_in_Q unfolding TimeSyncInterruptTT_def apply (auto)
          apply (rule_tac x="\<rho>" in exI, auto, rule_tac x="Z \<union> {e\<in>Y. e \<noteq> Tock}" in exI, auto)
          using case_assms by (rule_tac x="W \<union> Y" in exI, auto)
      qed
    next
      assume Tock_notin_Y: "Tock \<notin> Y"
      have "{e\<in>Y. e \<noteq> Tock} \<inter> {e. e \<noteq> Tock \<and> \<rho> @ [[e]\<^sub>E] \<in> P \<or> e = Tock \<and> \<rho> @ [[Z]\<^sub>R, [e]\<^sub>E] \<in> P} = {}"
        using P_nontock_inter by auto
      then have \<rho>_Z_Y_in_P: "\<rho> @ [[Z \<union> {e\<in>Y. e \<noteq> Tock}]\<^sub>R] \<in> P"
        using TT2w_P case_assms(1) unfolding TT2w_def by auto
      have "{e\<in>Y. e \<noteq> Tock} \<inter> {e. e \<noteq> Tock \<and> filter_tocks \<rho> @ [[e]\<^sub>E] \<in> Q \<or> e = Tock \<and> filter_tocks \<rho> @ [[W]\<^sub>R, [e]\<^sub>E] \<in> Q} = {}"
        using Q_nontock_inter by auto
      then have \<rho>_W_Y_in_Q: "filter_tocks \<rho> @ [[W \<union> {e\<in>Y. e \<noteq> Tock}]\<^sub>R] \<in> Q"
        using TT2w_Q case_assms(2) unfolding TT2w_def by auto
      show "\<rho> @ [[X \<union> Y]\<^sub>R] \<in> P \<triangle>\<^sub>T Q"
        using \<rho>_Z_Y_in_P \<rho>_W_Y_in_Q unfolding TimeSyncInterruptTT_def apply (auto)
        apply (rule_tac x="\<rho>" in exI, auto, rule_tac x="Z \<union> {e\<in>Y. e \<noteq> Tock}" in exI, auto)
        using case_assms Tock_notin_Y by (rule_tac x="W \<union> {e\<in>Y. e \<noteq> Tock}" in exI, auto)
    qed
  next
    fix p q2
    assume case_assms: "p \<in> P" "\<forall>p'. p \<noteq> p' @ [[Tick]\<^sub>E]" "\<forall>p' Y. p \<noteq> p' @ [[Y]\<^sub>R]"
      "filter_tocks p @ q2 @ [[X]\<^sub>R] \<in> Q" "\<forall>q' Y. q2 @ [[X]\<^sub>R] \<noteq> [Y]\<^sub>R # q'" "\<rho> = p @ q2"
    have "{e. e \<noteq> Tock \<and> filter_tocks p @ q2 @ [[e]\<^sub>E] \<in> Q \<or> e = Tock \<and> filter_tocks p @ q2 @ [[X]\<^sub>R, [e]\<^sub>E] \<in> Q}
        \<subseteq> {e. e \<noteq> Tock \<and> \<rho> @ [[e]\<^sub>E] \<in> P \<triangle>\<^sub>T Q \<or> e = Tock \<and> \<rho> @ [[X]\<^sub>R, [e]\<^sub>E] \<in> P \<triangle>\<^sub>T Q}"
      unfolding TimeSyncInterruptTT_def
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
      using TT2w_Q case_assms unfolding TT2w_def by (erule_tac x="filter_tocks p @ q2" in allE, auto)
    then show "p @ q2 @ [[X \<union> Y]\<^sub>R] \<in> P \<triangle>\<^sub>T Q"
      unfolding TimeSyncInterruptTT_def
      apply (auto, erule_tac x=p in allE, auto simp add: case_assms, erule_tac x="q2 @ [[X \<union> Y]\<^sub>R]" in allE, auto simp add: case_assms)
      by (metis (no_types, lifting) Cons_eq_append_conv append_Cons case_assms(5))
  qed
qed

lemma TT2_TimeSyncInterrupt:
  assumes P_wf: "\<forall>x\<in>P. ttWF x" assumes Q_wf: "\<forall>x\<in>Q. ttWF x"
  assumes TT1_P: "TT1 P" and TT1_Q: "TT1 Q"
  assumes TT2_P: "TT2 P" and TT2_Q: "TT2 Q"
  assumes ttWFx_P: "ttWFx P" and ttWFx_Q: "ttWFx Q"
  shows "TT2 (P \<triangle>\<^sub>T Q)"
  unfolding TT2_def
proof auto
  fix \<rho> \<sigma> X Y
  assume assm1: "\<rho> @ [X]\<^sub>R # \<sigma> \<in> P \<triangle>\<^sub>T Q"
  assume assm2: "Y \<inter> {e. e \<noteq> Tock \<and> \<rho> @ [[e]\<^sub>E] \<in> P \<triangle>\<^sub>T Q \<or> e = Tock \<and> \<rho> @ [[X]\<^sub>R, [e]\<^sub>E] \<in> P \<triangle>\<^sub>T Q} = {}"
  
  have TT2w_P: "TT2w P"
    by (simp add: TT2_P TT2_imp_TT2w)
  have TT2w_Q: "TT2w Q"
    by (simp add: TT2_Q TT2_imp_TT2w)

  have "ttWF (\<rho> @ [X]\<^sub>R # \<sigma>)"
    using P_wf Q_wf TimeSyncInterruptTT_wf assm1 by blast
  then have "\<sigma> = [] \<or> (\<exists> \<sigma>'. \<sigma> = [Tock]\<^sub>E # \<sigma>')"
    by (induct \<rho> rule:ttWF.induct, auto, cases \<sigma> rule:ttWF.cases, auto)
  then show "\<rho> @ [X \<union> Y]\<^sub>R # \<sigma> \<in> P \<triangle>\<^sub>T Q"
  proof auto
    assume "\<sigma> = []"
    then show "\<rho> @ [[X \<union> Y]\<^sub>R] \<in> P \<triangle>\<^sub>T Q"
      using TT1_P TT1_Q TT2w_P TT2w_Q TT2w_TimeSyncInterrupt TT2w_def ttWFx_P ttWFx_Q P_wf assm1 assm2 by blast
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
      using assm1 case_assm unfolding TimeSyncInterruptTT_def
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
        by (metis append_butlast_last_id case_assms2(5) ttobs.distinct(1) last.simps last_appendR list.simps(3))
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
        using case_assms2(6) by (induct \<rho> p rule:tt_subset.induct, auto, metis Cons_eq_append_conv case_assms2(3))
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
        using TT1_P TT1_def case_assms2(2) tt_prefix_concat tt_prefix_imp_prefix_subset by blast
      have 3: "\<rho> @ [[X]\<^sub>R, [Tock]\<^sub>E] \<in> P"
        using TT1_P case_assms2(2) tt_prefix_subset_same_front unfolding TT1_def by fastforce
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
          using TT1_Q TT1_def tt_prefix_concat tt_prefix_imp_prefix_subset by blast
        show "\<rho> @ [[x]\<^sub>E] \<in> P \<triangle>\<^sub>T Q"
          using case_assms3 unfolding TimeSyncInterruptTT_def
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
          using TT1_Q TT1_def tt_prefix_concat tt_prefix_imp_prefix_subset by blast
        show "\<rho> @ [[x]\<^sub>E] \<in> P \<triangle>\<^sub>T Q"
          using case_assms3 unfolding TimeSyncInterruptTT_def
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
          by (meson tt_prefix_subset.simps(1) tt_prefix_subset.simps(2) tt_prefix_subset.simps(3) tt_prefix_subset_same_front subsetI) 
        then show "\<rho> @ [[X]\<^sub>R, [Tock]\<^sub>E] \<notin> P \<triangle>\<^sub>T Q \<Longrightarrow> False"
          unfolding TimeSyncInterruptTT_def apply (auto)
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
          by (meson tt_prefix_subset.simps(1) tt_prefix_subset.simps(2) tt_prefix_subset.simps(3) tt_prefix_subset_same_front subsetI) 
        then show "\<rho> @ [[X]\<^sub>R, [Tock]\<^sub>E] \<notin> P \<triangle>\<^sub>T Q \<Longrightarrow> \<rho> @ [[Tock]\<^sub>E] \<in> P \<triangle>\<^sub>T Q"
          unfolding TimeSyncInterruptTT_def apply (auto)
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
          unfolding TimeSyncInterruptTT_def using 1 2 case_assms3 by auto
      next
        fix x
        assume case_assms3: "filter_tocks \<rho> @ [[x]\<^sub>E] \<in> Q" "x \<noteq> Tock"
        show "\<rho> @ [[x]\<^sub>E] \<in> P \<triangle>\<^sub>T Q"
          unfolding TimeSyncInterruptTT_def using 1 2 case_assms3 by auto
      next
        assume case_assms3: "filter_tocks \<rho> @ [[X]\<^sub>R, [Tock]\<^sub>E] \<in> Q"
        show "\<rho> @ [[X]\<^sub>R, [Tock]\<^sub>E] \<notin> P \<triangle>\<^sub>T Q \<Longrightarrow> False"
          unfolding TimeSyncInterruptTT_def case_assms3 filter_tocks_end_ref_tock 1 2 3 apply auto
          apply (erule_tac x="\<rho> @ [[X]\<^sub>R, [Tock]\<^sub>E]" in allE, auto simp add: 1 2 3)
          by (erule_tac x="[]" in allE, auto simp add: case_assms3 filter_tocks_end_ref_tock)
      next
        assume case_assms3: "filter_tocks \<rho> @ [[X]\<^sub>R, [Tock]\<^sub>E] \<in> Q"
        show "\<rho> @ [[X]\<^sub>R, [Tock]\<^sub>E] \<notin> P \<triangle>\<^sub>T Q \<Longrightarrow> \<rho> @ [[Tock]\<^sub>E] \<in> P \<triangle>\<^sub>T Q"
          unfolding TimeSyncInterruptTT_def case_assms3 filter_tocks_end_ref_tock 1 2 3 apply auto
          apply (erule_tac x="\<rho> @ [[X]\<^sub>R, [Tock]\<^sub>E]" in allE, auto simp add: 1 2 3)
          by (erule_tac x="[]" in allE, auto simp add: case_assms3 filter_tocks_end_ref_tock)
      qed
      then have 5: "Y \<inter> {e. e \<noteq> Tock \<and> filter_tocks \<rho> @ [[e]\<^sub>E] \<in> Q \<or> e = Tock \<and> filter_tocks \<rho> @ [[X]\<^sub>R, [e]\<^sub>E] \<in> Q} = {}"
        using assm2 by auto
      have 6: "\<rho> @ [X \<union> Y]\<^sub>R # [Tock]\<^sub>E # \<sigma>'' @ [[Tick]\<^sub>E] \<in> P"
        using TT2_P case_assms2 4 unfolding TT2_def by auto
      have 7: "filter_tocks \<rho> @ [X \<union> Y]\<^sub>R # [Tock]\<^sub>E # filter_tocks \<sigma>'' \<in> Q"
        using TT2_Q case_assms2 5 unfolding TT2_def by auto
      have 8: "filter_tocks (\<rho> @ [X \<union> Y]\<^sub>R # [Tock]\<^sub>E # \<sigma>'') = filter_tocks \<rho> @ [X \<union> Y]\<^sub>R # [Tock]\<^sub>E # filter_tocks \<sigma>''"
        by (induct \<rho> rule:filter_tocks.induct, auto)
      show "\<rho> @ [X \<union> Y]\<^sub>R # [Tock]\<^sub>E # \<sigma>'' @ [[Tick]\<^sub>E] \<in> P \<triangle>\<^sub>T Q"
        unfolding TimeSyncInterruptTT_def using 6 7 8 by auto
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
        using TT1_P TT1_def case_assms2(2) tt_prefix_concat tt_prefix_imp_prefix_subset by blast
      have 3: "\<rho> @ [[X]\<^sub>R, [Tock]\<^sub>E] \<in> P"
        using TT1_P case_assms2(2) tt_prefix_subset_same_front unfolding TT1_def by fastforce
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
          using TT1_Q TT1_def tt_prefix_concat tt_prefix_imp_prefix_subset by blast
        show "\<rho> @ [[x]\<^sub>E] \<in> P \<triangle>\<^sub>T Q"
          using case_assms3 unfolding TimeSyncInterruptTT_def
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
          using TT1_Q TT1_def tt_prefix_concat tt_prefix_imp_prefix_subset by blast
        show "\<rho> @ [[x]\<^sub>E] \<in> P \<triangle>\<^sub>T Q"
          using case_assms3 unfolding TimeSyncInterruptTT_def
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
          by (meson tt_prefix_subset.simps(1) tt_prefix_subset.simps(2) tt_prefix_subset.simps(3) tt_prefix_subset_same_front subsetI) 
        then show "\<rho> @ [[X]\<^sub>R, [Tock]\<^sub>E] \<notin> P \<triangle>\<^sub>T Q \<Longrightarrow> False"
          unfolding TimeSyncInterruptTT_def apply (auto)
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
          by (meson tt_prefix_subset.simps(1) tt_prefix_subset.simps(2) tt_prefix_subset.simps(3) tt_prefix_subset_same_front subsetI) 
        then show "\<rho> @ [[X]\<^sub>R, [Tock]\<^sub>E] \<notin> P \<triangle>\<^sub>T Q \<Longrightarrow> \<rho> @ [[Tock]\<^sub>E] \<in> P \<triangle>\<^sub>T Q"
          unfolding TimeSyncInterruptTT_def apply (auto)
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
          unfolding TimeSyncInterruptTT_def using 1 2 case_assms3 by auto
      next
        fix x
        assume case_assms3: "filter_tocks \<rho> @ [[x]\<^sub>E] \<in> Q" "x \<noteq> Tock"
        show "\<rho> @ [[x]\<^sub>E] \<in> P \<triangle>\<^sub>T Q"
          unfolding TimeSyncInterruptTT_def using 1 2 case_assms3 by auto
      next
        assume case_assms3: "filter_tocks \<rho> @ [[X]\<^sub>R, [Tock]\<^sub>E] \<in> Q"
        show "\<rho> @ [[X]\<^sub>R, [Tock]\<^sub>E] \<notin> P \<triangle>\<^sub>T Q \<Longrightarrow> False"
          unfolding TimeSyncInterruptTT_def case_assms3 filter_tocks_end_ref_tock 1 2 3 apply auto
          apply (erule_tac x="\<rho> @ [[X]\<^sub>R, [Tock]\<^sub>E]" in allE, auto simp add: 1 2 3)
          by (erule_tac x="[]" in allE, auto simp add: case_assms3 filter_tocks_end_ref_tock)
      next
        assume case_assms3: "filter_tocks \<rho> @ [[X]\<^sub>R, [Tock]\<^sub>E] \<in> Q"
        show "\<rho> @ [[X]\<^sub>R, [Tock]\<^sub>E] \<notin> P \<triangle>\<^sub>T Q \<Longrightarrow> \<rho> @ [[Tock]\<^sub>E] \<in> P \<triangle>\<^sub>T Q"
          unfolding TimeSyncInterruptTT_def case_assms3 filter_tocks_end_ref_tock 1 2 3 apply auto
          apply (erule_tac x="\<rho> @ [[X]\<^sub>R, [Tock]\<^sub>E]" in allE, auto simp add: 1 2 3)
          by (erule_tac x="[]" in allE, auto simp add: case_assms3 filter_tocks_end_ref_tock)
      qed
      then have 5: "Y \<inter> {e. e \<noteq> Tock \<and> filter_tocks \<rho> @ [[e]\<^sub>E] \<in> Q \<or> e = Tock \<and> filter_tocks \<rho> @ [[X]\<^sub>R, [e]\<^sub>E] \<in> Q} = {}"
        using assm2 by auto
      have 6: "\<rho> @ [X \<union> Y]\<^sub>R # [Tock]\<^sub>E # \<sigma>'' @ [[Ya]\<^sub>R] \<in> P"
        using TT2_P case_assms2 4 unfolding TT2_def by auto
      have 7: "filter_tocks \<rho> @ [X \<union> Y]\<^sub>R # [Tock]\<^sub>E # filter_tocks \<sigma>'' @ [[Z]\<^sub>R] \<in> Q"
        using TT2_Q case_assms2 5 unfolding TT2_def by auto
      have 8: "filter_tocks (\<rho> @ [X \<union> Y]\<^sub>R # [Tock]\<^sub>E # \<sigma>'') = filter_tocks \<rho> @ [X \<union> Y]\<^sub>R # [Tock]\<^sub>E # filter_tocks \<sigma>''"
        by (induct \<rho> rule:filter_tocks.induct, auto)
      show "\<rho> @ [X \<union> Y]\<^sub>R # [Tock]\<^sub>E # \<sigma>'' @ [[W]\<^sub>R] \<in> P \<triangle>\<^sub>T Q"
        unfolding TimeSyncInterruptTT_def using case_assms2 6 7 8 by force
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
        using TT1_P TT1_def case_assms2(2) tt_prefix_concat tt_prefix_imp_prefix_subset by blast
      have 3: "\<rho> @ [[X]\<^sub>R, [Tock]\<^sub>E] \<in> P"
        using TT1_P case_assms2(2) tt_prefix_subset_same_front unfolding TT1_def by fastforce
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
          using TT1_Q TT1_def tt_prefix_concat tt_prefix_imp_prefix_subset by blast
        show "\<rho> @ [[x]\<^sub>E] \<in> P \<triangle>\<^sub>T Q"
          using case_assms3 unfolding TimeSyncInterruptTT_def
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
          using TT1_Q TT1_def tt_prefix_concat tt_prefix_imp_prefix_subset by blast
        show "\<rho> @ [[x]\<^sub>E] \<in> P \<triangle>\<^sub>T Q"
          using case_assms3 unfolding TimeSyncInterruptTT_def
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
          by (meson tt_prefix_subset.simps(1) tt_prefix_subset.simps(2) tt_prefix_subset.simps(3) tt_prefix_subset_same_front subsetI) 
        then show "\<rho> @ [[X]\<^sub>R, [Tock]\<^sub>E] \<notin> P \<triangle>\<^sub>T Q \<Longrightarrow> False"
          unfolding TimeSyncInterruptTT_def apply (auto)
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
          by (meson tt_prefix_subset.simps(1) tt_prefix_subset.simps(2) tt_prefix_subset.simps(3) tt_prefix_subset_same_front subsetI) 
        then show "\<rho> @ [[X]\<^sub>R, [Tock]\<^sub>E] \<notin> P \<triangle>\<^sub>T Q \<Longrightarrow> \<rho> @ [[Tock]\<^sub>E] \<in> P \<triangle>\<^sub>T Q"
          unfolding TimeSyncInterruptTT_def apply (auto)
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
          unfolding TimeSyncInterruptTT_def using 1 2 case_assms3 by auto
      next
        fix x
        assume case_assms3: "filter_tocks \<rho> @ [[x]\<^sub>E] \<in> Q" "x \<noteq> Tock"
        show "\<rho> @ [[x]\<^sub>E] \<in> P \<triangle>\<^sub>T Q"
          unfolding TimeSyncInterruptTT_def using 1 2 case_assms3 by auto
      next
        assume case_assms3: "filter_tocks \<rho> @ [[X]\<^sub>R, [Tock]\<^sub>E] \<in> Q"
        show "\<rho> @ [[X]\<^sub>R, [Tock]\<^sub>E] \<notin> P \<triangle>\<^sub>T Q \<Longrightarrow> False"
          unfolding TimeSyncInterruptTT_def case_assms3 filter_tocks_end_ref_tock 1 2 3 apply auto
          apply (erule_tac x="\<rho> @ [[X]\<^sub>R, [Tock]\<^sub>E]" in allE, auto simp add: 1 2 3)
          by (erule_tac x="[]" in allE, auto simp add: case_assms3 filter_tocks_end_ref_tock)
      next
        assume case_assms3: "filter_tocks \<rho> @ [[X]\<^sub>R, [Tock]\<^sub>E] \<in> Q"
        show "\<rho> @ [[X]\<^sub>R, [Tock]\<^sub>E] \<notin> P \<triangle>\<^sub>T Q \<Longrightarrow> \<rho> @ [[Tock]\<^sub>E] \<in> P \<triangle>\<^sub>T Q"
          unfolding TimeSyncInterruptTT_def case_assms3 filter_tocks_end_ref_tock 1 2 3 apply auto
          apply (erule_tac x="\<rho> @ [[X]\<^sub>R, [Tock]\<^sub>E]" in allE, auto simp add: 1 2 3)
          by (erule_tac x="[]" in allE, auto simp add: case_assms3 filter_tocks_end_ref_tock)
      qed
      then have 5: "Y \<inter> {e. e \<noteq> Tock \<and> filter_tocks \<rho> @ [[e]\<^sub>E] \<in> Q \<or> e = Tock \<and> filter_tocks \<rho> @ [[X]\<^sub>R, [e]\<^sub>E] \<in> Q} = {}"
        using assm2 by auto
      have 6: "\<rho> @ [X \<union> Y]\<^sub>R # [Tock]\<^sub>E # p2 \<in> P"
        using TT2_P case_assms2 4 unfolding TT2_def by auto
      have 7: "filter_tocks \<rho> @ [X \<union> Y]\<^sub>R # [Tock]\<^sub>E # filter_tocks p2 @ q3 \<in> Q"
        using TT2_Q case_assms2 5 unfolding TT2_def by auto
      have 8: "filter_tocks (\<rho> @ [X \<union> Y]\<^sub>R # [Tock]\<^sub>E # p2) = filter_tocks \<rho> @ [X \<union> Y]\<^sub>R # [Tock]\<^sub>E # filter_tocks p2"
        by (induct \<rho> rule:filter_tocks.induct, auto)
      have 9: "(\<forall>p'. \<rho> @ [X \<union> Y]\<^sub>R # [Tock]\<^sub>E # p2 \<noteq> p' @ [[Tick]\<^sub>E]) \<and> (\<forall>p' Ya. \<rho> @ [X \<union> Y]\<^sub>R # [Tock]\<^sub>E # p2 \<noteq> p' @ [[Ya]\<^sub>R])"
      proof auto
        fix p'
        assume "\<rho> @ [X \<union> Y]\<^sub>R # [Tock]\<^sub>E # p2 = p' @ [[Tick]\<^sub>E]"
        then have "\<exists> p''. p2 = p'' @ [[Tick]\<^sub>E]"
          by (metis append_butlast_last_id ttevent.simps(7) ttobs.inject(1) last.simps last_appendR list.distinct(1))
        then show False
          using case_assms2(4) by auto
      next
        fix p' Ya
        assume "\<rho> @ [X \<union> Y]\<^sub>R # [Tock]\<^sub>E # p2 = p' @ [[Ya]\<^sub>R]"
        then have "\<exists> p''. p2 = p'' @ [[Ya]\<^sub>R]"
          by (metis append_butlast_last_id ttobs.distinct(1) last.simps last_appendR list.distinct(1))
        then show False
          using case_assms2(5) by auto
      qed
      show "\<rho> @ [X \<union> Y]\<^sub>R # [Tock]\<^sub>E # p2 @ q3 \<in> P \<triangle>\<^sub>T Q"
        unfolding TimeSyncInterruptTT_def using case_assms2 6 7 8 9 by auto
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
          unfolding TimeSyncInterruptTT_def using case_assms3 apply (safe, simp_all)
          apply (erule_tac x="p" in allE, simp add: case_assms2)
          apply (erule_tac x="q2 @ [[x]\<^sub>E]" in allE, simp add: case_assms3)
          by (simp add: append_eq_Cons_conv case_assms2(4))
      next
        fix x
        assume case_assms3: "filter_tocks p @ q2 @ [[x]\<^sub>E] \<in> Q" "x \<noteq> Tock"
        show "\<rho> @ [[x]\<^sub>E] \<in> P \<triangle>\<^sub>T Q"
          unfolding TimeSyncInterruptTT_def using case_assms3 apply (safe, simp_all)
          apply (erule_tac x="p" in allE, simp add: case_assms2)
          apply (erule_tac x="q2 @ [[x]\<^sub>E]" in allE, simp add: case_assms3)
          by (simp add: append_eq_Cons_conv case_assms2(4))
      next
        assume case_assms3: "filter_tocks p @ q2 @ [[X]\<^sub>R, [Tock]\<^sub>E] \<in> Q"
        show "\<rho> @ [[X]\<^sub>R, [Tock]\<^sub>E] \<notin> P \<triangle>\<^sub>T Q \<Longrightarrow> False"
          unfolding TimeSyncInterruptTT_def case_assms3 filter_tocks_end_ref_tock apply auto
          apply (erule_tac x="p" in allE, auto simp add: case_assms2)
          apply (erule_tac x="q2 @ [[X]\<^sub>R, [Tock]\<^sub>E]" in allE, auto simp add: case_assms3)
          by (meson append_eq_Cons_conv case_assms2(4) case_assms2(5))
      next
        assume case_assms3: "filter_tocks p @ q2 @ [[X]\<^sub>R, [Tock]\<^sub>E] \<in> Q"
        show "\<rho> @ [[X]\<^sub>R, [Tock]\<^sub>E] \<notin> P \<triangle>\<^sub>T Q \<Longrightarrow> \<rho> @ [[Tock]\<^sub>E] \<in> P \<triangle>\<^sub>T Q"
          unfolding TimeSyncInterruptTT_def case_assms3 filter_tocks_end_ref_tock apply auto
          apply (erule_tac x="p" in allE, auto simp add: case_assms2)
          apply (erule_tac x="q2 @ [[X]\<^sub>R, [Tock]\<^sub>E]" in allE, auto simp add: case_assms3)
          by (meson append_eq_Cons_conv case_assms2(4) case_assms2(5))
      qed
      then have 1: "Y \<inter> {e. e \<noteq> Tock \<and> filter_tocks p @ q2 @ [[e]\<^sub>E] \<in> Q \<or> e = Tock \<and> filter_tocks p @ q2 @ [[X]\<^sub>R, [e]\<^sub>E] \<in> Q} = {}"
        using assm2 by auto
      thm case_assms2
      have 2: "filter_tocks p @ q2 @ [X \<union> Y]\<^sub>R # [Tock]\<^sub>E # \<sigma>' \<in> Q"
        using TT2_Q unfolding TT2_def apply auto
        by (erule_tac x="filter_tocks p @ q2" in allE, erule_tac x="[Tock]\<^sub>E # \<sigma>'" in allE, auto simp add: 1 case_assms2)
      have 3: "\<nexists> Ya q'. q2 @ [X \<union> Y]\<^sub>R # [Tock]\<^sub>E # \<sigma>' = [Ya]\<^sub>R # q'"
        by (simp add: append_eq_Cons_conv case_assms2(4) case_assms2(5))
        thm case_assms2
      show "(p @ q2) @ [X \<union> Y]\<^sub>R # [Tock]\<^sub>E # \<sigma>' \<in> P \<triangle>\<^sub>T Q"
        unfolding TimeSyncInterruptTT_def using case_assms2 2 3 by (auto)
    qed
  qed
qed

lemma ttWFx_TimeSyncInterrupt:
  assumes "ttWFx P" "ttWFx Q" "\<forall>x\<in>Q. ttWF x"
  shows "ttWFx (P \<triangle>\<^sub>T Q)"
  unfolding ttWFx_def TimeSyncInterruptTT_def
proof (safe, simp_all)
  fix p
  assume "p @ [[Tick]\<^sub>E] \<in> P"
  then show "ttWFx_trace (p @ [[Tick]\<^sub>E])"
    using assms(1) unfolding ttWFx_def by auto
next
  fix p X Y Z
  assume "p @ [[X]\<^sub>R] \<in> P"
  then have "ttWFx_trace (p @ [[X]\<^sub>R])"
    using assms(1) unfolding ttWFx_def by auto
  then show "ttWFx_trace (p @ [[Z]\<^sub>R])"
    using ttWFx_trace_end_refusal_change by blast
next
  fix p q2
  assume "p \<in> P"
  then have "ttWFx_trace p"
    using assms(1) unfolding ttWFx_def by auto
  also assume assm2: "filter_tocks p @ q2 \<in> Q"
  then have "ttWFx_trace (filter_tocks p @ q2)"
    using assms(2) unfolding ttWFx_def by auto
  then have "ttWFx_trace q2"
    using ttWFx_trace_cons_right by blast
  then show "ttWFx_trace (p @ q2)"
    using calculation ttWFx_append assm2 assms(3) filter_tocks_in_tocks tocks_append_wf2 by blast
qed

lemma add_Tick_refusal_trace_filter_tocks:
  "add_Tick_refusal_trace (filter_tocks t) = filter_tocks (add_Tick_refusal_trace t)"
  by (induct t rule:filter_tocks.induct, auto, (case_tac x, auto)+)

lemma TT3w_TimeSyncInterrupt:
  assumes TT3w_P: "TT3w P" and TT3w_Q: "TT3w Q"
  shows "TT3w (P \<triangle>\<^sub>T Q)"
  unfolding TT3w_def TimeSyncInterruptTT_def
proof (safe, simp_all)
  fix p
  assume case_assms: "p @ [[Tick]\<^sub>E] \<in> P" "filter_tocks p \<in> Q"
  have 1: "add_Tick_refusal_trace p @ [[Tick]\<^sub>E] \<in> P"
    by (metis TT3w_P TT3w_def add_Tick_refusal_trace_end_event case_assms(1))
  have 2: "filter_tocks (add_Tick_refusal_trace p) \<in> Q"
    by (metis TT3w_Q TT3w_def add_Tick_refusal_trace_filter_tocks case_assms(2))
  show "\<exists>pa. pa @ [[Tick]\<^sub>E] \<in> P \<and> filter_tocks pa \<in> Q \<and> add_Tick_refusal_trace (p @ [[Tick]\<^sub>E]) = pa @ [[Tick]\<^sub>E]"
    using 1 2 by (rule_tac x="add_Tick_refusal_trace p" in exI, auto simp add: add_Tick_refusal_trace_end_event)
next
  fix p X Y Z
  assume case_assms: "p @ [[X]\<^sub>R] \<in> P" "filter_tocks p @ [[Y]\<^sub>R] \<in> Q" "Z \<subseteq> X \<union> Y" "{e \<in> X. e \<noteq> Tock} = {e \<in> Y. e \<noteq> Tock}"
  have 1: "add_Tick_refusal_trace p @ [[X \<union> {Tick}]\<^sub>R] \<in> P"
    by (metis TT3w_P TT3w_def add_Tick_refusal_trace_end_refusal case_assms(1))
  have 2: "filter_tocks (add_Tick_refusal_trace p) @ [[Y \<union> {Tick}]\<^sub>R] \<in> Q"
    by (metis TT3w_Q TT3w_def add_Tick_refusal_trace_end_refusal add_Tick_refusal_trace_filter_tocks case_assms(2))
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
    using TT3w_P TT3w_def case_assms(1) by blast
  have 2: "(\<forall>p'. add_Tick_refusal_trace p \<noteq> p' @ [[Tick]\<^sub>E]) \<and> (\<forall>p' Y. add_Tick_refusal_trace p \<noteq> p' @ [[Y]\<^sub>R])"
    using add_Tick_refusal_trace_not_end_refusal add_Tick_refusal_trace_not_end_tick case_assms by blast
  have 3: "filter_tocks (add_Tick_refusal_trace p) @ add_Tick_refusal_trace q2 \<in> Q"
    by (metis TT3w_Q TT3w_def add_Tick_refusal_trace_concat add_Tick_refusal_trace_filter_tocks case_assms(4))
  have 4: "\<forall>q' Y. add_Tick_refusal_trace q2 \<noteq> [Y]\<^sub>R # q'"
    by (metis add_Tick_refusal_trace.simps(2) case_assms(5) contains_refusal.elims(2) contains_refusal.elims(3) contains_refusal_add_Tick_refusal_trace ttobs.distinct(1) list.inject)
  show "\<forall>pa. pa \<in> P \<longrightarrow> (\<exists>p'. pa = p' @ [[Tick]\<^sub>E]) \<or> (\<exists>p' Y. pa = p' @ [[Y]\<^sub>R]) \<or>
      (\<forall>q2a. filter_tocks pa @ q2a \<in> Q \<longrightarrow> (\<exists>q' Y. q2a = [Y]\<^sub>R # q') \<or> add_Tick_refusal_trace (p @ q2) \<noteq> pa @ q2a) \<Longrightarrow>
    \<exists>pa. pa @ [[Tick]\<^sub>E] \<in> P \<and> filter_tocks pa \<in> Q \<and> add_Tick_refusal_trace (p @ q2) = pa @ [[Tick]\<^sub>E]"
    using 1 2 3 4 add_Tick_refusal_trace_concat
    by (erule_tac x="add_Tick_refusal_trace p" in allE, auto, erule_tac x="add_Tick_refusal_trace q2" in allE, auto)
qed

lemma TT3_TimeSyncInterrupt:
  assumes "\<forall>x\<in>P. ttWF x" "\<forall>x\<in>Q. ttWF x"
  assumes "TT1 P" "TT1 Q"
  assumes "TT3 P" "TT3 Q"
  shows "TT3 (P \<triangle>\<^sub>T Q)"
  by (metis TT1_TT3w_equiv_TT3 TT1_TimeSyncInterrupt TT3w_TimeSyncInterrupt assms)

lemma TT_TimeSyncInterrupt:
  assumes "TT P" "TT Q"
  shows "TT (P \<triangle>\<^sub>T Q)"
  using assms unfolding TT_def apply auto
  using TimeSyncInterruptTT_wf apply blast
  using TT0_TimeSyncInterrupt apply blast
  using TT1_TimeSyncInterrupt apply blast
  using TT2w_TimeSyncInterrupt apply blast
  using ttWFx_TimeSyncInterrupt apply blast
  done

lemma TimeSyncInterrupt_Union_dist1:
  assumes S_nonempty: "S \<noteq> {}"
  shows "(P \<triangle>\<^sub>T \<Union>S) = \<Union>{R. \<exists>Q. Q \<in> S \<and> R = P \<triangle>\<^sub>T Q}"
    using S_nonempty unfolding TimeSyncInterruptTT_def apply (safe, simp_all)
    apply (rule_tac x="P \<triangle>\<^sub>T X" in exI, unfold TimeSyncInterruptTT_def, simp, blast)
    apply (rule_tac x="P \<triangle>\<^sub>T Xa" in exI, unfold TimeSyncInterruptTT_def, simp, blast)
    apply (rule_tac x="P \<triangle>\<^sub>T X" in exI, unfold TimeSyncInterruptTT_def, simp, blast, blast, force)
    by (metis (no_types, hide_lams))
  
lemma TimeSyncInterrupt_Union_dist2:
  assumes S_nonempty: "S \<noteq> {}"
  shows "(\<Union>S \<triangle>\<^sub>T Q) = \<Union>{R. \<exists>P. P \<in> S \<and> R = P \<triangle>\<^sub>T Q}"
  using S_nonempty unfolding TimeSyncInterruptTT_def apply (safe, simp_all)
  apply (rule_tac x="X \<triangle>\<^sub>T Q" in exI, unfold TimeSyncInterruptTT_def, simp, blast)
  apply (rule_tac x="Xa \<triangle>\<^sub>T Q" in exI, unfold TimeSyncInterruptTT_def, simp, blast)
  apply (rule_tac x="X \<triangle>\<^sub>T Q" in exI, unfold TimeSyncInterruptTT_def, simp, blast, metis, force)
  by (metis (no_types, hide_lams))

subsection {* Strict Timed Interrupt *}

definition StrictTimedInterruptTT :: "'e ttobs list set \<Rightarrow> nat \<Rightarrow> 'e ttobs list set \<Rightarrow> 'e ttobs list set" (infixl "\<triangle>\<^bsub>_\<^esub>" 58) where
  "(P \<triangle>\<^bsub>n\<^esub> Q) = {t\<in>P. length (filter (\<lambda> x. x = [Tock]\<^sub>E) t) < n}
    \<union> {t\<in>Q. n = 0}
    \<union> {t. \<exists>p\<in>P. \<exists>q\<in>Q. n > 0 \<and> last p = [Tock]\<^sub>E \<and> length (filter (\<lambda> x. x = [Tock]\<^sub>E) p) = n \<and> t = p @ q}"

lemma StrictTimedInterrupt_zero_deadline: "(P \<triangle>\<^bsub>0\<^esub> Q) = Q"
  unfolding StrictTimedInterruptTT_def by auto

lemma StrictTimedInterruptTT_wf:
  assumes "\<forall>t\<in>P. ttWF t" "\<forall>t\<in>Q. ttWF t"
  shows "\<forall>t\<in>(P \<triangle>\<^bsub>n\<^esub> Q). ttWF t"
  using assms unfolding StrictTimedInterruptTT_def
proof (auto)
  fix p q
  assume "p \<in> P" "q \<in> Q" "last p = [Tock]\<^sub>E"
  then have "ttWF p" "ttWF q" "\<forall>p'. p \<noteq> p' @ [[Tick]\<^sub>E]" "\<forall>p' Y. p \<noteq> p' @ [[Y]\<^sub>R]"
    using assms by auto
  then show "ttWF (p @ q)"
    by (simp add: nontick_event_end_append_wf)
qed

lemma TT0_StrictTimedInterrupt:
  assumes "TT0 P" "TT0 Q" "TT1 P" "TT1 Q"
  shows "TT0 (P \<triangle>\<^bsub>n\<^esub> Q)"
  unfolding StrictTimedInterruptTT_def TT0_def using assms TT0_TT1_empty by fastforce

lemma TT1_StrictTimedInterrupt:
  assumes "TT1 P" "TT1 Q"
  shows "TT1 (P \<triangle>\<^bsub>n\<^esub> Q)"
  unfolding TT1_def
proof auto
  fix \<rho> \<sigma> :: "'a ttobs list"
  assume assm1: "\<rho> \<lesssim>\<^sub>C \<sigma>"
  assume assm2: "\<sigma> \<in> P \<triangle>\<^bsub>n\<^esub> Q"
  then have "(\<sigma>\<in>P \<and> length (filter (\<lambda> x. x = [Tock]\<^sub>E) \<sigma>) < n)
    \<or> (\<sigma> \<in> Q \<and> n = 0)
    \<or> (\<exists>p\<in>P. \<exists>q\<in>Q. n > 0 \<and> last p = [Tock]\<^sub>E \<and> length (filter (\<lambda> x. x = [Tock]\<^sub>E) p) = n \<and> \<sigma> = p @ q)"
    unfolding StrictTimedInterruptTT_def by auto
  then show "\<rho> \<in> P \<triangle>\<^bsub>n\<^esub> Q"
  proof auto
    assume case_assms: "\<sigma> \<in> P" "length (filter (\<lambda>x. x = [Tock]\<^sub>E) \<sigma>) < n"
    have 1: "\<rho> \<in> P"
      using TT1_def assm1 assms(1) case_assms(1) by blast
    have 2: "length (filter (\<lambda>x. x = [Tock]\<^sub>E) \<rho>) < n"
      using assm1 case_assms(2) tt_prefix_subset_Tock_filter_length by fastforce
    then show "\<rho> \<in> P \<triangle>\<^bsub>n\<^esub> Q"
      using 1 2 unfolding StrictTimedInterruptTT_def by auto
  next
    assume case_assms: "\<sigma> \<in> Q" "n = 0"
    have "\<rho> \<in> Q"
      using TT1_def assm1 assms(2) case_assms(1) by blast
    then show "\<rho> \<in> P \<triangle>\<^bsub>0\<^esub> Q"
      unfolding StrictTimedInterruptTT_def by auto
  next
    fix p q :: "'a ttobs list"
    assume case_assms: "p \<in> P" "last p = [Tock]\<^sub>E" "n = length (filter (\<lambda>x. x = [Tock]\<^sub>E) p)"
      "filter (\<lambda>x. x = [Tock]\<^sub>E) p \<noteq> []" "q \<in> Q" "\<sigma> = p @ q"
    then have "(\<exists> p' q'. \<rho> = p' @ q' \<and> p' \<subseteq>\<^sub>C p \<and> q' \<lesssim>\<^sub>C q) \<or> (\<rho> \<lesssim>\<^sub>C p)"
      using assm1 apply (auto, induct \<rho> p rule:tt_prefix_subset.induct, auto)
      apply (metis append_Cons tt_prefix_subset_concat2 tt_subset.simps(2))
      by (metis append_Cons tt_prefix_subset_concat2 tt_subset.simps(3))
    then show "\<rho> \<in> P \<triangle>\<^bsub>length (filter (\<lambda>x. x = [Tock]\<^sub>E) p)\<^esub> Q"
    proof auto
      fix p' q'
      assume case_assms2: "\<rho> = p' @ q'" "p' \<subseteq>\<^sub>C p" "q' \<lesssim>\<^sub>C q"
      have 1: "p' \<in> P"
        using TT1_def assms(1) case_assms(1) case_assms2(2) tt_subset_imp_prefix_subset by blast
      have 2: "last p' = [Tock]\<^sub>E"
        using case_assms(2) case_assms2(2) apply (induct p' p rule:tt_subset.induct, auto)
        using tt_subset_same_length apply force
        apply (metis ttobs.distinct(1))
        using tt_subset_same_length apply force
        by (metis length_0_conv tt_subset_same_length)
      have 3: "length (filter (\<lambda>x. x = [Tock]\<^sub>E) p') = length (filter (\<lambda>x. x = [Tock]\<^sub>E) p)"
        using case_assms2(2) by (induct p' p rule:tt_subset.induct, auto)
      have 4: "q' \<in> Q"
        using TT1_def assms(2) case_assms(5) case_assms2(3) by blast
      then show "p' @ q' \<in> P \<triangle>\<^bsub>length (filter (\<lambda>x. x = [Tock]\<^sub>E) p)\<^esub> Q"
        using 1 2 3 4 case_assms(4) unfolding StrictTimedInterruptTT_def by auto
    next
      assume case_assms2: "\<rho> \<lesssim>\<^sub>C p"
      have 1: "\<rho> \<in> P"
        using TT1_def assms(1) case_assms(1) case_assms2 by blast
      have 2: "length (filter (\<lambda>x. x = [Tock]\<^sub>E) \<rho>) \<le> length (filter (\<lambda>x. x = [Tock]\<^sub>E) p)"
        using case_assms2 by (induct \<rho> p rule:tt_prefix_subset.induct, auto)
      (*have 3: "filter (\<lambda>x. x = [Tock]\<^sub>E) \<rho> \<noteq> []"
        using case_assms(4) case_assms2 apply auto apply (induct \<rho> p rule:tt_prefix_subset.induct, auto)*)
      (*have 3: "length (filter (\<lambda>x. x = [Tock]\<^sub>E) \<rho>) = length (filter (\<lambda>x. x = [Tock]\<^sub>E) p) \<Longrightarrow> last \<rho> = [Tock]\<^sub>E"
        using case_assms(4) case_assms2 apply - apply (induct \<rho> p rule:tt_prefix.induct, auto)
        using length_0_conv apply fastforce
        apply (case_tac "x = [Tock]\<^sub>E", auto)
         apply (case_tac "y = [Tock]\<^sub>E", auto)
        apply (case_tac "filter (\<lambda>x. x = [Tock]\<^sub>E) ya \<noteq> []", auto)*)

      show "\<rho> \<in> P \<triangle>\<^bsub>length (filter (\<lambda>x. x = [Tock]\<^sub>E) p)\<^esub> Q"
        using 1 2 unfolding StrictTimedInterruptTT_def
      proof auto
        show "filter (\<lambda>x. x = [Tock]\<^sub>E) p = [] \<Longrightarrow> \<rho> \<in> Q"
          using case_assms(4) by blast
      next
        assume case_assms3: "length (filter (\<lambda>x. x = [Tock]\<^sub>E) \<rho>) = length (filter (\<lambda>x. x = [Tock]\<^sub>E) p)"
          "\<forall>pa\<in>P. length (filter (\<lambda>x. x = [Tock]\<^sub>E) pa) = length (filter (\<lambda>x. x = [Tock]\<^sub>E) p) \<longrightarrow>
            last pa = [Tock]\<^sub>E \<longrightarrow> (\<forall>q\<in>Q. \<rho> \<noteq> pa @ q)"
        obtain p' where p'_assms: "p = p' @ [[Tock]\<^sub>E]"
          by (metis case_assms(2) case_assms(4) filter.simps(1) snoc_eq_iff_butlast)
        then have p'_tock_length: "length (filter (\<lambda>x. x = [Tock]\<^sub>E) p') < length (filter (\<lambda>x. x = [Tock]\<^sub>E) p)"
          using case_assms(4) case_assms3(1) by auto
        have \<rho>_p'_cases: "\<rho> \<lesssim>\<^sub>C p' \<or> \<rho> \<subseteq>\<^sub>C p' @ [[Tock]\<^sub>E]"
          using p'_assms case_assms2 apply auto apply (thin_tac "p = p' @ [[Tock]\<^sub>E]")
          apply (induct \<rho> p' rule:tt_prefix_subset.induct, auto)
          by (case_tac x, auto, case_tac xa, auto)
        have "\<rho> \<lesssim>\<^sub>C p' \<Longrightarrow> length (filter (\<lambda>x. x = [Tock]\<^sub>E) \<rho>) \<le> length (filter (\<lambda>x. x = [Tock]\<^sub>E) p')"
          using tt_prefix_subset_Tock_filter_length by blast
        then have "\<rho> \<subseteq>\<^sub>C p' @ [[Tock]\<^sub>E]"
          using \<rho>_p'_cases case_assms3(1) p'_tock_length by linarith
        then obtain \<rho>' where "\<rho> = \<rho>' @ [[Tock]\<^sub>E]"
          apply - apply (induct \<rho> p' rule:tt_subset.induct, auto)
          apply (insert tt_subset_same_length, fastforce)
          by (case_tac v, auto, insert tt_subset_same_length, fastforce)
        then have "last \<rho> = [Tock]\<^sub>E"
          by auto
        then have "\<forall>q\<in>Q. \<rho> \<noteq> \<rho> @ q"
          using "1" case_assms3(1) case_assms3(2) by blast
        then show "\<rho> \<in> Q"
          using TT0_TT1_empty TT0_def assms(2) case_assms(5) by auto
      next
        assume case_assms3: "length (filter (\<lambda>x. x = [Tock]\<^sub>E) \<rho>) = length (filter (\<lambda>x. x = [Tock]\<^sub>E) p)"
          "\<forall>pa\<in>P. length (filter (\<lambda>x. x = [Tock]\<^sub>E) pa) = length (filter (\<lambda>x. x = [Tock]\<^sub>E) p) \<longrightarrow>
            last pa = [Tock]\<^sub>E \<longrightarrow> (\<forall>q\<in>Q. \<rho> \<noteq> pa @ q)"
        obtain p' where p'_assms: "p = p' @ [[Tock]\<^sub>E]"
          by (metis case_assms(2) case_assms(4) filter.simps(1) snoc_eq_iff_butlast)
        then have p'_tock_length: "length (filter (\<lambda>x. x = [Tock]\<^sub>E) p') < length (filter (\<lambda>x. x = [Tock]\<^sub>E) p)"
          using case_assms(4) case_assms3(1) by auto
        have \<rho>_p'_cases: "\<rho> \<lesssim>\<^sub>C p' \<or> \<rho> \<subseteq>\<^sub>C p' @ [[Tock]\<^sub>E]"
          using p'_assms case_assms2 apply auto apply (thin_tac "p = p' @ [[Tock]\<^sub>E]")
          apply (induct \<rho> p' rule:tt_prefix_subset.induct, auto)
          by (case_tac x, auto, case_tac xa, auto)
        have "\<rho> \<lesssim>\<^sub>C p' \<Longrightarrow> length (filter (\<lambda>x. x = [Tock]\<^sub>E) \<rho>) \<le> length (filter (\<lambda>x. x = [Tock]\<^sub>E) p')"
          using tt_prefix_subset_Tock_filter_length by blast
        then have "\<rho> \<subseteq>\<^sub>C p' @ [[Tock]\<^sub>E]"
          using \<rho>_p'_cases case_assms3(1) p'_tock_length by linarith
        then obtain \<rho>' where "\<rho> = \<rho>' @ [[Tock]\<^sub>E]"
          apply - apply (induct \<rho> p' rule:tt_subset.induct, auto)
          apply (insert tt_subset_same_length, fastforce)
          by (case_tac v, auto, insert tt_subset_same_length, fastforce)
        then have "last \<rho> = [Tock]\<^sub>E"
          by auto
        then have "\<forall>q\<in>Q. \<rho> \<noteq> \<rho> @ q"
          using "1" case_assms3(1) case_assms3(2) by blast
        then show "filter (\<lambda>x. x = [Tock]\<^sub>E) p = []"
          using TT0_TT1_empty TT0_def assms(2) case_assms(5) by auto
      qed
    qed
  qed
qed

lemma TT2_StrictTimedInterrupt:
  assumes "TT2 P" "TT2 Q" "TT0 Q" "TT1 Q"
  shows "TT2 (P \<triangle>\<^bsub>n\<^esub> Q)"
  unfolding TT2_def
proof auto
  fix \<rho> \<sigma> X Y
  assume assm1: "\<rho> @ [X]\<^sub>R # \<sigma> \<in> P \<triangle>\<^bsub>n\<^esub> Q"
  assume assm2: "Y \<inter> {e. e \<noteq> Tock \<and> \<rho> @ [[e]\<^sub>E] \<in> (P \<triangle>\<^bsub>n\<^esub> Q) \<or> e = Tock \<and> \<rho> @ [[X]\<^sub>R, [e]\<^sub>E] \<in> (P \<triangle>\<^bsub>n\<^esub> Q)} = {}"
  from assm1 have
    "(\<rho> @ [X]\<^sub>R # \<sigma> \<in> P \<and> length (filter (\<lambda>x. x = [Tock]\<^sub>E) (\<rho> @ [X]\<^sub>R # \<sigma>)) < n)
      \<or> (\<rho> @ [X]\<^sub>R # \<sigma> \<in> Q \<and> n = 0)
      \<or> \<rho> @ [X]\<^sub>R # \<sigma> \<in> {t. \<exists>p\<in>P. \<exists>q\<in>Q. 0 < n \<and> last p = [Tock]\<^sub>E \<and> length (filter (\<lambda>x. x = [Tock]\<^sub>E) p) = n \<and> t = p @ q}"
    unfolding StrictTimedInterruptTT_def by auto
  then show "\<rho> @ [X \<union> Y]\<^sub>R # \<sigma> \<in> P \<triangle>\<^bsub>n\<^esub> Q"
  proof auto
    assume case_assms: "\<rho> @ [X]\<^sub>R # \<sigma> \<in> P" "length (filter (\<lambda>x. x = [Tock]\<^sub>E) \<rho>) + length (filter (\<lambda>x. x = [Tock]\<^sub>E) \<sigma>) < n"
    have 1: "\<And> e. e \<noteq> Tock \<and> \<rho> @ [[e]\<^sub>E] \<in> P \<Longrightarrow> \<rho> @ [[e]\<^sub>E] \<in> P \<triangle>\<^bsub>n\<^esub> Q"
      unfolding StrictTimedInterruptTT_def apply auto
      using add_lessD1 case_assms(2) by blast+  
    have 2: "\<rho> @ [[X]\<^sub>R, [Tock]\<^sub>E] \<in> P \<Longrightarrow> \<rho> @ [[X]\<^sub>R, [Tock]\<^sub>E] \<in> P \<triangle>\<^bsub>n\<^esub> Q"
      unfolding StrictTimedInterruptTT_def apply auto
      using case_assms(2) apply blast
      apply (erule_tac x="\<rho> @ [[X]\<^sub>R, [Tock]\<^sub>E]" in ballE, simp)
      using Suc_lessI TT0_TT1_empty add_lessD1 assms(3) assms(4) case_assms(2) apply (blast, blast)
      apply (erule_tac x="\<rho> @ [[X]\<^sub>R, [Tock]\<^sub>E]" in ballE, simp)
      using Suc_lessI TT0_TT1_empty add_lessD1 assms(3) assms(4) case_assms(2) apply (blast, blast)
      done
    have "{e. e \<noteq> Tock \<and> \<rho> @ [[e]\<^sub>E] \<in> P \<or> e = Tock \<and> \<rho> @ [[X]\<^sub>R, [e]\<^sub>E] \<in> P}
      \<subseteq> {e. e \<noteq> Tock \<and> \<rho> @ [[e]\<^sub>E] \<in> (P \<triangle>\<^bsub>n\<^esub> Q) \<or> e = Tock \<and> \<rho> @ [[X]\<^sub>R, [e]\<^sub>E] \<in> (P \<triangle>\<^bsub>n\<^esub> Q)}"
      using 1 2 by auto
    then have "Y \<inter> {e. e \<noteq> Tock \<and> \<rho> @ [[e]\<^sub>E] \<in> P \<or> e = Tock \<and> \<rho> @ [[X]\<^sub>R, [e]\<^sub>E] \<in> P} = {}"
      using assm2 by auto
    then have "\<rho> @ [X \<union> Y]\<^sub>R # \<sigma> \<in> P"
      using TT2_aux1 assms(1) case_assms(1) by fastforce
    then show "\<rho> @ [X \<union> Y]\<^sub>R # \<sigma> \<in> P \<triangle>\<^bsub>n\<^esub> Q"
      unfolding StrictTimedInterruptTT_def using case_assms(2) by auto
  next
    assume case_assms: "\<rho> @ [X]\<^sub>R # \<sigma> \<in> Q" "n = 0"
    then have "{e. e \<noteq> Tock \<and> \<rho> @ [[e]\<^sub>E] \<in> (P \<triangle>\<^bsub>n\<^esub> Q) \<or> e = Tock \<and> \<rho> @ [[X]\<^sub>R, [e]\<^sub>E] \<in> (P \<triangle>\<^bsub>n\<^esub> Q)}
      = {e. e \<noteq> Tock \<and> \<rho> @ [[e]\<^sub>E] \<in> Q \<or> e = Tock \<and> \<rho> @ [[X]\<^sub>R, [e]\<^sub>E] \<in> Q}"
      by (simp add: StrictTimedInterrupt_zero_deadline)
    then have "Y \<inter> {e. e \<noteq> Tock \<and> \<rho> @ [[e]\<^sub>E] \<in> Q \<or> e = Tock \<and> \<rho> @ [[X]\<^sub>R, [e]\<^sub>E] \<in> Q} = {}"
      using assm2 by auto
    then have "\<rho> @ [X \<union> Y]\<^sub>R # \<sigma> \<in> Q"
      using TT2_aux1 assms(2) case_assms(1) by fastforce
    then show "\<rho> @ [X \<union> Y]\<^sub>R # \<sigma> \<in> P \<triangle>\<^bsub>0\<^esub> Q"
      using StrictTimedInterrupt_zero_deadline by blast
  next
    fix p q
    assume case_assms: "p \<in> P" "last p = [Tock]\<^sub>E" "n = length (filter (\<lambda>x. x = [Tock]\<^sub>E) p)"
      "filter (\<lambda>x. x = [Tock]\<^sub>E) p \<noteq> []" "q \<in> Q" "\<rho> @ [X]\<^sub>R # \<sigma> = p @ q"
    have "(\<exists> \<rho>2. \<rho> = p @ \<rho>2 \<and> q = \<rho>2 @ [X]\<^sub>R # \<sigma>) \<or> (\<exists> \<sigma>1. p = \<rho> @ [X]\<^sub>R # \<sigma>1 \<and> \<sigma> = \<sigma>1 @ q)"
      using case_assms(6) by (induct \<rho> p rule:tt_prefix_subset.induct, auto, metis Cons_eq_append_conv)
    then show "\<rho> @ [X \<union> Y]\<^sub>R # \<sigma> \<in> P \<triangle>\<^bsub>length (filter (\<lambda>x. x = [Tock]\<^sub>E) p)\<^esub> Q"
    proof auto
      fix \<rho>2
      assume case_assms2: "q = \<rho>2 @ [X]\<^sub>R # \<sigma>" "\<rho> = p @ \<rho>2"
      have "{e. e \<noteq> Tock \<and> \<rho>2 @ [[e]\<^sub>E] \<in> Q \<or> e = Tock \<and> \<rho>2 @ [[X]\<^sub>R, [e]\<^sub>E] \<in> Q} 
        \<subseteq> {e. e \<noteq> Tock \<and> \<rho> @ [[e]\<^sub>E] \<in> (P \<triangle>\<^bsub>n\<^esub> Q) \<or> e = Tock \<and> \<rho> @ [[X]\<^sub>R, [e]\<^sub>E] \<in> (P \<triangle>\<^bsub>n\<^esub> Q)}"
        unfolding StrictTimedInterruptTT_def using append_assoc case_assms case_assms2(2) by auto
      then have "Y \<inter> {e. e \<noteq> Tock \<and> \<rho>2 @ [[e]\<^sub>E] \<in> Q \<or> e = Tock \<and> \<rho>2 @ [[X]\<^sub>R, [e]\<^sub>E] \<in> Q} = {}"
        using assm2 by auto
      then have "\<rho>2 @ [X \<union> Y]\<^sub>R # \<sigma> \<in> Q"
        using TT2_aux1 assms(2) case_assms(5) case_assms2(1) by fastforce
      then show "p @ \<rho>2 @ [X \<union> Y]\<^sub>R # \<sigma> \<in> P \<triangle>\<^bsub>length (filter (\<lambda>x. x = [Tock]\<^sub>E) p)\<^esub> Q"
        unfolding StrictTimedInterruptTT_def using case_assms(1) case_assms(2) case_assms(4) by blast
    next
      fix \<sigma>1
      assume case_assms2: "\<sigma> = \<sigma>1 @ q" "p = \<rho> @ [X]\<^sub>R # \<sigma>1"
      have 1: "length (filter (\<lambda>x. x = [Tock]\<^sub>E) \<rho>) \<le> n"
        by (simp add: case_assms(3) case_assms2(2))
      have 2: "\<sigma>1 \<noteq> [] \<and> last \<sigma>1 = [Tock]\<^sub>E"
        by (metis case_assms(2) case_assms2(2) last.simps last_appendR list.distinct(1) ttobs.simps(4))
      then have 3: "\<exists> \<sigma>1'. \<sigma>1 = \<sigma>1' @ [[Tock]\<^sub>E]"
        by (metis append_butlast_last_id)
      then have 4: "length (filter (\<lambda>x. x = [Tock]\<^sub>E) \<sigma>1) > 0"
        by auto
      then have 5: "length (filter (\<lambda>x. x = [Tock]\<^sub>E) \<rho>) < n"
        by (simp add: case_assms(3) case_assms2(2))
      have 6: "\<And>e. e \<noteq> Tock \<and> \<rho> @ [[e]\<^sub>E] \<in> P \<Longrightarrow> \<rho> @ [[e]\<^sub>E] \<in> (P \<triangle>\<^bsub>n\<^esub> Q)"
        unfolding StrictTimedInterruptTT_def by (auto, simp add: case_assms(3) case_assms(4), insert 5, blast+)
      have 7: "\<rho> @ [[X]\<^sub>R, [Tock]\<^sub>E] \<in> P \<Longrightarrow> \<rho> @ [[X]\<^sub>R, [Tock]\<^sub>E] \<in> (P \<triangle>\<^bsub>n\<^esub> Q)"
        unfolding StrictTimedInterruptTT_def apply auto
        using "5" apply blast+
        apply (erule_tac x="\<rho> @ [[X]\<^sub>R, [Tock]\<^sub>E]" in ballE, auto, insert 5, linarith)
        using TT0_TT1_empty assms(3) assms(4) apply blast
        apply (erule_tac x="\<rho> @ [[X]\<^sub>R, [Tock]\<^sub>E]" in ballE, auto)
        using TT0_TT1_empty assms(3) assms(4) apply blast
        done
      have "{e. e \<noteq> Tock \<and> \<rho> @ [[e]\<^sub>E] \<in> P \<or> e = Tock \<and> \<rho> @ [[X]\<^sub>R, [e]\<^sub>E] \<in> P} 
        \<subseteq> {e. e \<noteq> Tock \<and> \<rho> @ [[e]\<^sub>E] \<in> (P \<triangle>\<^bsub>n\<^esub> Q) \<or> e = Tock \<and> \<rho> @ [[X]\<^sub>R, [e]\<^sub>E] \<in> (P \<triangle>\<^bsub>n\<^esub> Q)}"
        using 6 7 by auto
      then have "Y \<inter> {e. e \<noteq> Tock \<and> \<rho> @ [[e]\<^sub>E] \<in> P \<or> e = Tock \<and> \<rho> @ [[X]\<^sub>R, [e]\<^sub>E] \<in> P} = {}"
        using assm2 by auto
      then  have "\<rho> @ [X \<union> Y]\<^sub>R # \<sigma>1 \<in> P"
        using TT2_aux1 assms(1) case_assms(1) case_assms2(2) by fastforce
      then show "\<rho> @ [X \<union> Y]\<^sub>R # \<sigma>1 @ q \<in> P \<triangle>\<^bsub>length (filter (\<lambda>x. x = [Tock]\<^sub>E) \<rho>) + length (filter (\<lambda>x. x = [Tock]\<^sub>E) \<sigma>1)\<^esub> Q"
        unfolding StrictTimedInterruptTT_def apply auto
        using "4" apply blast
        by (erule_tac x="\<rho> @ [X \<union> Y]\<^sub>R # \<sigma>1" in ballE, insert "2" case_assms(5), auto)+
    qed
  qed
qed

lemma ttWFx_StrictTimedInterrupt:
  assumes "ttWFx P" "ttWFx Q"
  shows "ttWFx (P \<triangle>\<^bsub>n\<^esub> Q)"
  unfolding ttWFx_def StrictTimedInterruptTT_def
proof auto
  fix x
  assume "x \<in> P"
  then show "ttWFx_trace x"
    using ttWFx_def assms(1) by blast
next
  fix x
  assume "x \<in> Q"
  then show "ttWFx_trace x"
    using ttWFx_def assms(2) by blast
next
  fix p q
  assume case_assms: "p \<in> P" "q \<in> Q" "last p = [Tock]\<^sub>E" "n = length (filter (\<lambda>x. x = [Tock]\<^sub>E) p)" "filter (\<lambda>x. x = [Tock]\<^sub>E) p \<noteq> []"
  have "\<And> P Q. ttWFx P \<Longrightarrow> ttWFx Q \<Longrightarrow> p \<in> P \<Longrightarrow> q \<in> Q \<Longrightarrow> last p = [Tock]\<^sub>E \<Longrightarrow> ttWFx_trace (p @ q)"
    apply (induct p rule:ttWFx_trace.induct, auto)
    using ttWFx_def apply (blast)
    apply (induct q rule:ttWFx_trace.induct, auto)
    using ttWFx_def ttWFx_trace.simps(3) apply blast
    apply (meson ttWFx_def ttWFx_trace.simps(3))
    apply (meson ttWFx_def ttWFx_trace_cons_imp_cons)
    apply (meson ttWFx_def ttWFx_trace_cons_imp_cons)
    apply (meson ttWFx_def ttWFx_trace_cons_imp_cons)
    apply (meson ttWFx_def ttWFx_trace_cons_imp_cons)
    apply (induct q rule:ttWFx_trace.induct, auto)
    apply (meson ttWFx_def ttWFx_trace.simps(3))
    apply (meson ttWFx_def ttWFx_trace.simps(3))
    apply (meson ttWFx_def ttWFx_trace.simps(3))
    apply (meson ttWFx_def ttWFx_trace.simps(3))
    apply (meson ttWFx_def ttWFx_trace.simps(3))
    apply (meson ttWFx_def ttWFx_trace.simps(3))
    apply (meson ttWFx_def ttWFx_trace.simps(3))
    apply (induct q rule:ttWFx_trace.induct, auto)
    apply (meson ttWFx_def ttWFx_trace.simps(3))
    apply (metis ttWFx_def ttWFx_trace.simps(3) append_Nil mem_Collect_eq)
    apply (metis ttWFx_def ttWFx_trace.simps(3) append_Nil mem_Collect_eq)
    apply (metis ttWFx_def ttWFx_trace.simps(3) append_Nil mem_Collect_eq)
    apply (metis ttWFx_def ttWFx_trace.simps(3) append_Nil mem_Collect_eq)
    apply (metis ttWFx_def ttWFx_trace.simps(3) append_Nil mem_Collect_eq)
    apply (metis ttWFx_def ttWFx_trace.simps(3) append_Nil mem_Collect_eq)
    apply (induct q rule:ttWFx_trace.induct, auto)
    apply (meson ttWFx_def ttWFx_trace_cons_imp_cons)
    apply (metis ttWFx_def ttWFx_trace_cons_imp_cons mem_Collect_eq)+
    done
  then show "ttWFx_trace (p @ q)"
    using assms case_assms by auto
qed

lemma TT3w_StrictTimedInterrupt:
  assumes "TT3w P" "TT3w Q"
  shows "TT3w (P \<triangle>\<^bsub>n\<^esub> Q)"
  unfolding TT3w_def StrictTimedInterruptTT_def apply auto
  using TT3w_def assms(1) apply blast
  apply (metis add_Tick_refusal_trace_filter_Tock_same_length)
  using TT3w_def assms(2) apply blast
  apply (metis TT3w_def add_Tick_refusal_trace.simps(1) add_Tick_refusal_trace.simps(2) add_Tick_refusal_trace_concat add_Tick_refusal_trace_filter_Tock_same_length append_butlast_last_id assms(1) assms(2) last_appendR list.distinct(1))
  by (metis TT3w_def add_Tick_refusal_trace_concat add_Tick_refusal_trace_end_event add_Tick_refusal_trace_filter_Tock_same_length append_butlast_last_id assms(1) assms(2) filter.simps(1) last_snoc)

lemma TT3_StrictTimedInterrupt:
  assumes "TT1 P" "TT1 Q"
  assumes "TT3 P" "TT3 Q"
  shows "TT3 (P \<triangle>\<^bsub>n\<^esub> Q)"
  by (meson TT1_StrictTimedInterrupt TT1_TT3w_equiv_TT3 TT3w_StrictTimedInterrupt assms)

lemma Stop_StrictTimedInterrupt:
  assumes "TT0 Q" "TT1 Q"
  shows "(STOP\<^sub>C \<triangle>\<^bsub>n\<^esub> Q) = wait\<^sub>C[n] ;\<^sub>C Q"
  unfolding StrictTimedInterruptTT_def
proof (auto)
  fix x
  show "x \<in> STOP\<^sub>C \<Longrightarrow> length (filter (\<lambda>x. x = [Tock]\<^sub>E) x) < n \<Longrightarrow> x \<in> wait\<^sub>C[n] ;\<^sub>C Q"
    unfolding StopTT_def WaitTT_def SeqCompTT_def using end_tick_notin_tocks by auto
next
  fix x
  show "x \<in> Q \<Longrightarrow> n = 0 \<Longrightarrow> x \<in> wait\<^sub>C[0] ;\<^sub>C Q"
    unfolding WaitTT_def SeqCompTT_def using tocks.empty_in_tocks by fastforce 
next
  fix p q
  show "p \<in> STOP\<^sub>C \<Longrightarrow> q \<in> Q \<Longrightarrow> last p = [Tock]\<^sub>E \<Longrightarrow> p @ q \<in> wait\<^sub>C[length (filter (\<lambda>x. x = [Tock]\<^sub>E) p)] ;\<^sub>C Q"
    unfolding StopTT_def WaitTT_def SeqCompTT_def by auto
next
  fix x
  show "x \<in> wait\<^sub>C[0] ;\<^sub>C Q \<Longrightarrow> n = 0 \<Longrightarrow> x \<notin> Q \<Longrightarrow> x \<in> STOP\<^sub>C"
    unfolding StopTT_def WaitTT_def SeqCompTT_def apply auto
    using end_tick_notin_tocks apply blast
    using tocks_length_eq by fastforce
next
  fix x
  show "x \<in> wait\<^sub>C[0] ;\<^sub>C Q \<Longrightarrow> n = 0 \<Longrightarrow> x \<notin> Q \<Longrightarrow> False"
    unfolding  WaitTT_def SeqCompTT_def apply auto
    using TT0_TT1_empty assms(1) assms(2) tocks_length_eq apply fastforce
    using end_tick_notin_tocks apply blast
    using tocks_length_eq by fastforce
next
  fix x
  show "x \<in> wait\<^sub>C[n] ;\<^sub>C Q \<Longrightarrow>
    \<forall>p\<in>STOP\<^sub>C. length (filter (\<lambda>x. x = [Tock]\<^sub>E) p) = n \<longrightarrow> last p = [Tock]\<^sub>E \<longrightarrow> (\<forall>q\<in>Q. x \<noteq> p @ q)
    \<Longrightarrow> x \<notin> Q \<Longrightarrow> x \<in> STOP\<^sub>C"
    unfolding SeqCompTT_def apply auto
    unfolding WaitTT_def StopTT_def apply blast
    apply (auto simp add: end_tick_notin_tocks)
    apply (erule_tac x="sa" in allE, auto)
    apply (rule_tac x="sa" in bexI, auto)
    by (metis append_Nil in_tocks_last)
next
  fix x
  show "x \<in> wait\<^sub>C[n] ;\<^sub>C Q \<Longrightarrow>
    \<forall>p\<in>STOP\<^sub>C. length (filter (\<lambda>x. x = [Tock]\<^sub>E) p) = n \<longrightarrow> last p = [Tock]\<^sub>E \<longrightarrow> (\<forall>q\<in>Q. x \<noteq> p @ q)
    \<Longrightarrow> x \<notin> Q \<Longrightarrow> length (filter (\<lambda>x. x = [Tock]\<^sub>E) x) < n"
    unfolding SeqCompTT_def apply auto
    unfolding WaitTT_def StopTT_def apply (auto simp add: end_tick_notin_tocks)
    apply (metis TT0_TT1_empty append.right_neutral assms(1) assms(2) in_tocks_last)
    apply (erule_tac x="sa" in allE, auto)
    by (metis append_Nil in_tocks_last)
next
  fix x
  show "x \<in> wait\<^sub>C[n] ;\<^sub>C Q \<Longrightarrow>
    \<forall>p\<in>STOP\<^sub>C. length (filter (\<lambda>x. x = [Tock]\<^sub>E) p) = n \<longrightarrow> last p = [Tock]\<^sub>E \<longrightarrow> (\<forall>q\<in>Q. x \<noteq> p @ q)
    \<Longrightarrow> 0 < n \<Longrightarrow> x \<in> STOP\<^sub>C"
    unfolding SeqCompTT_def apply auto
    unfolding WaitTT_def StopTT_def apply (auto simp add: end_tick_notin_tocks)
    by (metis filter.simps(1) in_tocks_last)
next
  fix x
  show "x \<in> wait\<^sub>C[n] ;\<^sub>C Q \<Longrightarrow>
    \<forall>p\<in>STOP\<^sub>C. length (filter (\<lambda>x. x = [Tock]\<^sub>E) p) = n \<longrightarrow> last p = [Tock]\<^sub>E \<longrightarrow> (\<forall>q\<in>Q. x \<noteq> p @ q)
    \<Longrightarrow> 0 < n \<Longrightarrow> length (filter (\<lambda>x. x = [Tock]\<^sub>E) x) < n"
    unfolding SeqCompTT_def apply auto
    unfolding WaitTT_def StopTT_def apply (auto simp add: end_tick_notin_tocks)
    apply (metis TT0_TT1_empty append_Nil2 assms(1) assms(2) filter.simps(1) in_tocks_last)
    by (metis filter.simps(1) in_tocks_last)
qed

lemma Skip_StrictTimedInterrupt:
  shows "n > 0 \<Longrightarrow> (SKIP\<^sub>C \<triangle>\<^bsub>n\<^esub> Q) = SKIP\<^sub>C"
  unfolding StrictTimedInterruptTT_def SkipTT_def by auto

lemma Wait_less_StrictTimedInterrupt:
  assumes "TT0 Q" "TT1 Q"
  shows "m < n \<Longrightarrow> ((wait\<^sub>C[m] ;\<^sub>C P) \<triangle>\<^bsub>n\<^esub> Q) = wait\<^sub>C[m] ;\<^sub>C (P \<triangle>\<^bsub>n-m\<^esub> Q)"
proof auto
  fix x
  assume case_assms: "m < n" "x \<in> wait\<^sub>C[m] ;\<^sub>C P \<triangle>\<^bsub>n\<^esub> Q"
  then have "(x \<in> wait\<^sub>C[m] ;\<^sub>C P \<and> length (filter (\<lambda>x. x = [Tock]\<^sub>E) x) < n) 
    \<or> (\<exists> p q. p \<in> wait\<^sub>C[m] ;\<^sub>C P \<and> length (filter (\<lambda>x. x = [Tock]\<^sub>E) p) = n \<and> last p = [Tock]\<^sub>E \<and> q \<in> Q \<and> x = p @ q)"
    unfolding StrictTimedInterruptTT_def by auto
  then show "x \<in> wait\<^sub>C[m] ;\<^sub>C (P \<triangle>\<^bsub>n - m\<^esub> Q)"
  proof auto
    assume case_assms2: "x \<in> wait\<^sub>C[m] ;\<^sub>C P" "length (filter (\<lambda>x. x = [Tock]\<^sub>E) x) < n"
    then have "(x \<in> wait\<^sub>C[m] \<and> (\<nexists>s. x = s @ [[Tick]\<^sub>E])) \<or> (\<exists> w p. w @ [[Tick]\<^sub>E] \<in> wait\<^sub>C[m] \<and> p \<in> P \<and> x = w @ p)"
      unfolding SeqCompTT_def by auto
    then show "x \<in> wait\<^sub>C[m] ;\<^sub>C (P \<triangle>\<^bsub>n - m\<^esub> Q)"
    proof auto
      assume "x \<in> wait\<^sub>C[m]" "\<forall>s. x \<noteq> s @ [[Tick]\<^sub>E]"
      then show "x \<in> wait\<^sub>C[m] ;\<^sub>C (P \<triangle>\<^bsub>n - m\<^esub> Q)"
        unfolding SeqCompTT_def by auto
    next
      fix w p
      assume case_assms3: "w @ [[Tick]\<^sub>E] \<in> wait\<^sub>C[m]" "p \<in> P" "x = w @ p"
      have "length (filter (\<lambda>x. x = [Tock]\<^sub>E) w) = m"
        using case_assms3(1) unfolding WaitTT_def by (auto simp add: notin_tocks)
      then have "p \<in> (P \<triangle>\<^bsub>n - m\<^esub> Q)"
        unfolding StrictTimedInterruptTT_def using case_assms case_assms2 case_assms3 by auto
      then show "w @ p \<in> wait\<^sub>C[m] ;\<^sub>C (P \<triangle>\<^bsub>n - m\<^esub> Q)"
        unfolding SeqCompTT_def using case_assms3 by auto
    qed
  next
    fix p q
    assume case_assms2: "p \<in> wait\<^sub>C[m] ;\<^sub>C P" "n = length (filter (\<lambda>x. x = [Tock]\<^sub>E) p)"
      "last p = [Tock]\<^sub>E" "q \<in> Q" "x = p @ q"
    have "(\<exists> w p'. w @ [[Tick]\<^sub>E] \<in> wait\<^sub>C[m] \<and> p' \<in> P \<and> p = w @ p') \<or> (p \<in> wait\<^sub>C[m] \<and> (\<nexists>s. p = s @ [[Tick]\<^sub>E]))"
      using case_assms2(1) unfolding SeqCompTT_def by auto
    then show "p @ q \<in> wait\<^sub>C[m] ;\<^sub>C (P \<triangle>\<^bsub>length (filter (\<lambda>x. x = [Tock]\<^sub>E) p) - m\<^esub> Q)"
    proof auto
      fix w p'
      assume case_assms3: "w @ [[Tick]\<^sub>E] \<in> wait\<^sub>C[m]" "p' \<in> P" "p = w @ p'"
      have w_Tock_length: "length (filter (\<lambda>x. x = [Tock]\<^sub>E) w) = m"
        using case_assms3(1) unfolding WaitTT_def by (auto simp add: notin_tocks)
      have 1: "length (filter (\<lambda>x. x = [Tock]\<^sub>E) p') = n-m"
        using case_assms2(2) case_assms3(3) by (auto simp add: w_Tock_length)
      have 2: "last p' = [Tock]\<^sub>E"
        using case_assms2(3) case_assms3(3) 1 apply auto
        by (metis append_Nil2 case_assms(1) case_assms2(2) last_appendR nat_less_le w_Tock_length)
      have "p' @ q \<in> P \<triangle>\<^bsub>length (filter (\<lambda>x. x = [Tock]\<^sub>E) w) + length (filter (\<lambda>x. x = [Tock]\<^sub>E) p') - m\<^esub> Q"
        unfolding StrictTimedInterruptTT_def using 1 2 case_assms case_assms2 case_assms3 by auto
      then show "w @ p' @ q \<in> wait\<^sub>C[m] ;\<^sub>C (P \<triangle>\<^bsub>length (filter (\<lambda>x. x = [Tock]\<^sub>E) w) + length (filter (\<lambda>x. x = [Tock]\<^sub>E) p') - m\<^esub> Q)"
        unfolding SeqCompTT_def using case_assms3 by auto
    next
      assume case_assms3: "p \<in> wait\<^sub>C[m]" "\<forall>s. p \<noteq> s @ [[Tick]\<^sub>E]"
      have "p @ [[Tick]\<^sub>E] \<in> wait\<^sub>C[m]"
        using case_assms case_assms2 case_assms3 unfolding WaitTT_def by auto
      then have "length (filter (\<lambda>x. x = [Tock]\<^sub>E) p) = m"
        unfolding WaitTT_def by (auto simp add: notin_tocks)
      then have "n = m"
        using case_assms2(2) by blast
      then show "p @ q \<in> wait\<^sub>C[m] ;\<^sub>C (P \<triangle>\<^bsub>length (filter (\<lambda>x. x = [Tock]\<^sub>E) p) - m\<^esub> Q)"
        using case_assms(1) by auto
    qed
  qed
next
  fix x
  assume case_assms: "m < n" "x \<in> wait\<^sub>C[m] ;\<^sub>C (P \<triangle>\<^bsub>n - m\<^esub> Q)"
  then have "(x \<in> wait\<^sub>C[m] \<and> (\<nexists>s. x = s @ [[Tick]\<^sub>E])) \<or> (\<exists> w pq. w @ [[Tick]\<^sub>E] \<in> wait\<^sub>C[m] \<and> pq \<in> (P \<triangle>\<^bsub>n - m\<^esub> Q) \<and> x = w @ pq)"
    unfolding SeqCompTT_def by auto
  then show "x \<in> wait\<^sub>C[m] ;\<^sub>C P \<triangle>\<^bsub>n\<^esub> Q"
  proof auto
    assume case_assms2: "x \<in> wait\<^sub>C[m]" "\<forall>s. x \<noteq> s @ [[Tick]\<^sub>E]"
    have 1: "length (filter (\<lambda>x. x = [Tock]\<^sub>E) x) \<le> m"
      using case_assms2 unfolding WaitTT_def by auto
    have 2:  "x \<in> wait\<^sub>C[m] ;\<^sub>C P"
      using case_assms2 unfolding SeqCompTT_def by auto
    show "x \<in> wait\<^sub>C[m] ;\<^sub>C P \<triangle>\<^bsub>n\<^esub> Q"
      unfolding StrictTimedInterruptTT_def using case_assms 1 2 by auto
  next
    fix w pq
    assume case_assms2: "w @ [[Tick]\<^sub>E] \<in> wait\<^sub>C[m]" "pq \<in> P \<triangle>\<^bsub>n - m\<^esub> Q" "x = w @ pq"
    then have "(pq \<in> P \<and> length (filter (\<lambda>x. x = [Tock]\<^sub>E) pq) < n-m)
      \<or> (\<exists> p q. p \<in> P \<and> q \<in> Q \<and> last p = [Tock]\<^sub>E \<and> length (filter (\<lambda>x. x = [Tock]\<^sub>E) p) = n-m \<and> pq = p @ q)"
      unfolding StrictTimedInterruptTT_def using case_assms(1) by auto
    then show "w @ pq \<in> wait\<^sub>C[m] ;\<^sub>C P \<triangle>\<^bsub>n\<^esub> Q"
    proof auto
      assume case_assms3: "pq \<in> P" "length (filter (\<lambda>x. x = [Tock]\<^sub>E) pq) < n - m"
      have 1: "w @ pq \<in> wait\<^sub>C[m] ;\<^sub>C P"
        unfolding SeqCompTT_def using case_assms2(1) case_assms3(1) by blast
      have 2: "length (filter (\<lambda>x. x = [Tock]\<^sub>E) (w @ pq)) < n"
        using case_assms2 case_assms3 unfolding WaitTT_def by auto
      show "w @ pq \<in> wait\<^sub>C[m] ;\<^sub>C P \<triangle>\<^bsub>n\<^esub> Q"
        unfolding StrictTimedInterruptTT_def using 1 2 by auto
    next
      fix p q
      assume case_assms3: "p \<in> P" "q \<in> Q" "last p = [Tock]\<^sub>E"
        "length (filter (\<lambda>x. x = [Tock]\<^sub>E) p) = n - m" "pq = p @ q"
      have 1: "length (filter (\<lambda>x. x = [Tock]\<^sub>E) (w @ p)) = n"
        using case_assms case_assms2 case_assms3 unfolding WaitTT_def by (auto simp add: notin_tocks)
      have 2: "last (w @ p) = [Tock]\<^sub>E"
        by (metis case_assms(1) case_assms3(3) case_assms3(4) diff_is_0_eq filter.simps(1) last_appendR leD list.size(3))
      have 3: "w @ p \<in> wait\<^sub>C[m] ;\<^sub>C P"
        unfolding SeqCompTT_def using case_assms2(1) case_assms3(1) by blast
      show "w @ p @ q \<in> wait\<^sub>C[m] ;\<^sub>C P \<triangle>\<^bsub>n\<^esub> Q"
        unfolding StrictTimedInterruptTT_def using 1 2 3 case_assms using case_assms3(2) by auto
    qed
  qed
qed

lemma Wait_geq_StrictTimedInterrupt:
  assumes "TT0 Q" "TT1 Q"
  shows "m \<ge> n \<Longrightarrow> ((wait\<^sub>C[m] ;\<^sub>C P) \<triangle>\<^bsub>n\<^esub> Q) = wait\<^sub>C[n] ;\<^sub>C Q"
proof auto
  fix x
  assume case_assms: "n \<le> m" "x \<in> wait\<^sub>C[m] ;\<^sub>C P \<triangle>\<^bsub>n\<^esub> Q"
  then have "(x \<in> wait\<^sub>C[m] ;\<^sub>C P \<and> length (filter (\<lambda>x. x = [Tock]\<^sub>E) x) < n)
    \<or> (n = 0 \<and> x \<in> Q)
    \<or> (\<exists> p q. p \<in> wait\<^sub>C[m] ;\<^sub>C P \<and> q \<in> Q \<and> last p = [Tock]\<^sub>E \<and> length (filter (\<lambda>x. x = [Tock]\<^sub>E) p) = n \<and> x = p @ q)"
    unfolding StrictTimedInterruptTT_def by auto
  then show "x \<in> wait\<^sub>C[n] ;\<^sub>C Q"
  proof auto
    assume case_assms2: "x \<in> wait\<^sub>C[m] ;\<^sub>C P" "length (filter (\<lambda>x. x = [Tock]\<^sub>E) x) < n"
    have 1: "x \<in> wait\<^sub>C[n]"
      using case_assms(1) case_assms2 unfolding WaitTT_def SeqCompTT_def by (auto simp add: notin_tocks)
    then have 2: "\<nexists>s. x = s @ [[Tick]\<^sub>E]"
      using case_assms2 unfolding WaitTT_def by (auto simp add: notin_tocks)
    then show "x \<in> wait\<^sub>C[n] ;\<^sub>C Q"
      using case_assms2 1 2 unfolding SeqCompTT_def by auto
  next
    show "x \<in> Q \<Longrightarrow> x \<in> wait\<^sub>C[0] ;\<^sub>C Q"
      unfolding WaitTT_def SeqCompTT_def using tocks.intros by (auto, fastforce+)
  next
    fix p q
    assume case_assms2: "p \<in> wait\<^sub>C[m] ;\<^sub>C P" "q \<in> Q" "last p = [Tock]\<^sub>E" "x = p @ q" "n = length (filter (\<lambda>x. x = [Tock]\<^sub>E) p)"
    have 1: "p \<in> wait\<^sub>C[n]"
      using case_assms case_assms2 unfolding SeqCompTT_def apply auto
      unfolding WaitTT_def apply (auto simp add: notin_tocks)
      by (smt append_butlast_last_id append_is_Nil_conv append_self_conv filter.simps(1) filter.simps(2) filter_append last_append not_Cons_self2)
    then have 2: "p @ [[Tick]\<^sub>E] \<in> wait\<^sub>C[n]"
      unfolding WaitTT_def using case_assms2(3) by (auto simp add: case_assms2(5))
    then show "p @ q \<in> wait\<^sub>C[length (filter (\<lambda>x. x = [Tock]\<^sub>E) p)] ;\<^sub>C Q"
      using case_assms2 unfolding SeqCompTT_def by auto
  qed
next
  fix x
  assume case_assms: "n \<le> m" "x \<in> wait\<^sub>C[n] ;\<^sub>C Q"
  then have "(x \<in> wait\<^sub>C[n] \<and> (\<nexists>s. x = s @ [[Tick]\<^sub>E]))
    \<or> (\<exists> w q. w @ [[Tick]\<^sub>E] \<in> wait\<^sub>C[n] \<and> q \<in> Q \<and> x = w @ q)"
    unfolding SeqCompTT_def by auto
  then show "x \<in> wait\<^sub>C[m] ;\<^sub>C P \<triangle>\<^bsub>n\<^esub> Q"
  proof auto
    assume case_assms2: "x \<in> wait\<^sub>C[n]" "\<forall>s. x \<noteq> s @ [[Tick]\<^sub>E]"
    have 1: "length (filter (\<lambda>x. x = [Tock]\<^sub>E) x) \<le> n"
      using case_assms2 unfolding WaitTT_def by auto
    have 2: "length (filter (\<lambda>x. x = [Tock]\<^sub>E) x) = n \<Longrightarrow> n > 0 \<Longrightarrow> last x = [Tock]\<^sub>E"
      using case_assms2 unfolding WaitTT_def apply auto
      apply (induct x rule:ttWF.induct, auto simp add: notin_tocks)
      by (metis in_tocks_last last.simps list.distinct(1))
    have 3: "x \<in> wait\<^sub>C[m]"
      using case_assms case_assms2 unfolding WaitTT_def apply auto
      using less_le_trans le_neq_implies_less by blast+
    have 4: "x \<in> wait\<^sub>C[m] ;\<^sub>C P"
      using case_assms2 3 unfolding SeqCompTT_def by auto
    show "x \<in> wait\<^sub>C[m] ;\<^sub>C P \<triangle>\<^bsub>n\<^esub> Q"
      using case_assms case_assms2 1 2 4 unfolding StrictTimedInterruptTT_def apply auto
      using Stop_StrictTimedInterrupt StrictTimedInterrupt_zero_deadline assms apply blast
      using Stop_StrictTimedInterrupt StrictTimedInterrupt_zero_deadline TT0_TT1_empty assms by fastforce+
  next
    fix w q
    assume case_assms2: "w @ [[Tick]\<^sub>E] \<in> wait\<^sub>C[n]" "q \<in> Q" "x = w @ q"
    have 1: "n > 0 \<Longrightarrow> last w = [Tock]\<^sub>E"
      using case_assms2 unfolding WaitTT_def apply (auto simp add: notin_tocks)
      by (induct w rule:ttWF.induct, auto simp add: notin_tocks, metis in_tocks_last last.simps neq_Nil_conv)
    have 2: "length (filter (\<lambda>x. x = [Tock]\<^sub>E) w) = n"
      using case_assms2 unfolding WaitTT_def by (auto simp add: notin_tocks)
    have 3: "w \<in> wait\<^sub>C[m]"
      using case_assms case_assms2 2 unfolding WaitTT_def apply (auto simp add: notin_tocks)
      using nat_less_le by blast
    have 4: "w \<in> wait\<^sub>C[m] ;\<^sub>C P"
      using case_assms case_assms2 3 unfolding SeqCompTT_def 
    proof auto
      fix s :: "'a ttobs list"
      show "s @ [[Tick]\<^sub>E, [Tick]\<^sub>E] \<in> wait\<^sub>C[n] \<Longrightarrow> False"
        using WaitTT_wf using ttWF_dist_notTock_cons by (induct s rule:ttWF.induct, fastforce+)
    next
      fix s :: "'a ttobs list"
      show "s @ [[Tick]\<^sub>E, [Tick]\<^sub>E] \<in> wait\<^sub>C[n] \<Longrightarrow> False"
        using WaitTT_wf using ttWF_dist_notTock_cons by (induct s rule:ttWF.induct, fastforce+)
    qed
    show "w @ q \<in> wait\<^sub>C[m] ;\<^sub>C P \<triangle>\<^bsub>n\<^esub> Q"
      using case_assms case_assms2 1 2 4 unfolding StrictTimedInterruptTT_def apply auto
      using Stop_StrictTimedInterrupt StrictTimedInterrupt_zero_deadline assms(1) assms(2) apply blast
      using Stop_StrictTimedInterrupt StrictTimedInterrupt_zero_deadline assms(1) assms(2) by fastforce
  qed
qed

lemma StrictTimedInterrupt_union_dist1:
  "(P \<triangle>\<^bsub>n\<^esub> (Q \<union> R)) = (P \<triangle>\<^bsub>n\<^esub> Q) \<union> (P \<triangle>\<^bsub>n\<^esub> R)"
  unfolding StrictTimedInterruptTT_def by auto

lemma StrictTimedInterrupt_union_dist2:
  "((P \<union> Q) \<triangle>\<^bsub>n\<^esub> R) = (P \<triangle>\<^bsub>n\<^esub> R) \<union> (Q \<triangle>\<^bsub>n\<^esub> R)"
  unfolding StrictTimedInterruptTT_def by auto

lemma StrictTimedInterrupt_Union_dist1:
  "S \<noteq> {} \<Longrightarrow> (P \<triangle>\<^bsub>n\<^esub> \<Union>S) = \<Union>{R. \<exists>Q. Q \<in> S \<and> R = P \<triangle>\<^bsub>n\<^esub> Q}"
  unfolding StrictTimedInterruptTT_def by auto

lemma StrictTimedInterrupt_Union_dist2:
  "S \<noteq> {} \<Longrightarrow> (\<Union>S \<triangle>\<^bsub>n\<^esub> Q) = \<Union>{R. \<exists>P. P \<in> S \<and> R = P \<triangle>\<^bsub>n\<^esub> Q}"
  unfolding StrictTimedInterruptTT_def by auto

end
