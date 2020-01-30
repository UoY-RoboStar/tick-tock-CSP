theory IOTickTock_SeqComp
  imports IOTickTock_Core
begin

lemma IOTT0_SeqCompTT:
  "IOTT0 Outs P \<Longrightarrow> IOTT0 Outs Q \<Longrightarrow> IOTT0 Outs (P ;\<^sub>C Q)"
  unfolding IOTT0_def SeqCompTT_def
proof auto
  fix x s
  assume case_assms: "\<forall>x. x \<in> P \<longrightarrow> IOTT0_trace Outs x \<in> P" "x \<in> P" "\<forall>s. x \<noteq> s @ [[Tick]\<^sub>E]" "IOTT0_trace Outs x = s @ [[Tick]\<^sub>E]"
  have "\<And>s. IOTT0_trace Outs x = s @ [[Tick]\<^sub>E] \<Longrightarrow> \<exists> x'. x = x' @ [[Tick]\<^sub>E]"
    apply (induct x rule:IOTT0_trace.induct, auto)
    apply (metis IOTT0_trace.elims last.simps list.distinct(1) snoc_eq_iff_butlast)
    by (metis append_Cons last.simps snoc_eq_iff_butlast ttobs.distinct(1))
  then obtain x' where "x = x' @ [[Tick]\<^sub>E]"
    using case_assms(4) by auto
  then show False
    using case_assms(3) by auto
next
  fix s t
  assume case_assms: "\<forall>x. x \<in> P \<longrightarrow> IOTT0_trace Outs x \<in> P" "\<forall>x. x \<in> Q \<longrightarrow> IOTT0_trace Outs x \<in> Q"
    "s @ [[Tick]\<^sub>E] \<in> P" "t \<in> Q"
  have 1: "IOTT0_trace Outs s @ [[Tick]\<^sub>E] \<in> P"
    by (metis IOTT0_trace_append_event case_assms(1) case_assms(3))
  have 2: "IOTT0_trace Outs t \<in> Q"
    by (simp add: case_assms(2) case_assms(4))
  show "\<forall>sa. sa @ [[Tick]\<^sub>E] \<in> P \<longrightarrow> (\<forall>ta. ta \<in> Q \<longrightarrow> IOTT0_trace Outs (s @ t) \<noteq> sa @ ta)
      \<Longrightarrow> IOTT0_trace Outs (s @ t) \<in> P"
    using 1 2 apply (erule_tac x="IOTT0_trace Outs s" in allE, auto)
    by (erule_tac x="IOTT0_trace Outs t" in allE, auto simp add: IOTT0_trace_append)
next
  fix s t sa
  assume case_assms: "\<forall>x. x \<in> P \<longrightarrow> IOTT0_trace Outs x \<in> P" "\<forall>x. x \<in> Q \<longrightarrow> IOTT0_trace Outs x \<in> Q"
    "s @ [[Tick]\<^sub>E] \<in> P" "t \<in> Q" "IOTT0_trace Outs (s @ t) = sa @ [[Tick]\<^sub>E]"
    "\<forall>s. s @ [[Tick]\<^sub>E] \<in> P \<longrightarrow> (\<forall>t. t \<in> Q \<longrightarrow> sa @ [[Tick]\<^sub>E] \<noteq> s @ t)"
  have 1: "IOTT0_trace Outs s @ [[Tick]\<^sub>E] \<in> P"
    by (metis IOTT0_trace_append_event case_assms(1) case_assms(3))
  have 2: "IOTT0_trace Outs t \<in> Q"
    by (simp add: case_assms(2) case_assms(4))
  have 3: "IOTT0_trace Outs s @ IOTT0_trace Outs t = sa @ [[Tick]\<^sub>E]"
    by (metis IOTT0_trace_append case_assms(5))
  show "False"
    using 1 2 3 case_assms(6) by force
qed


end