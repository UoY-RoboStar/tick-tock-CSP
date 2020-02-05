theory IOTickTock_Core
  imports TickTock.TickTock
begin

section \<open>IO-Tick-Tock Healthiness Condition\<close>

fun IOTT0_trace :: "'e set \<Rightarrow> 'e tttrace \<Rightarrow> 'e tttrace" where
  "IOTT0_trace Outs [] = []" |
  "IOTT0_trace Outs ([e]\<^sub>E # t) = [e]\<^sub>E # IOTT0_trace Outs t" |
  "IOTT0_trace Outs ([X]\<^sub>R # t) = [X \<union> Event ` Outs]\<^sub>R # IOTT0_trace Outs t"

(* IOTT0: In a stable state, all output events must be refused of them must be refused *)
definition IOTT0 :: "'e set \<Rightarrow> 'e ttprocess \<Rightarrow> bool" where
  "IOTT0 Outs P = (\<forall> x. x \<in> P \<longrightarrow> IOTT0_trace Outs x \<in> P)"

lemma IOTT0_trace_tocks_imp1:
  assumes "Event ` Outs \<subseteq> X"
  shows "x \<in> tocks X \<Longrightarrow> IOTT0_trace Outs x \<in> tocks X"
  by (induct x rule: tocks.induct, auto simp add: tocks.intros assms)

lemma IOTT0_trace_tocks_imp2:
  shows "IOTT0_trace Outs x \<in> tocks X \<Longrightarrow> x \<in> tocks X"
  apply (induct x rule:ttWF.induct, auto simp add: notin_tocks)
  by (metis le_supE list.distinct(1) list.inject tocks.simps ttobs.inject(2))

lemma IOTT0_tocks:
  "Event ` Outs \<subseteq> X \<Longrightarrow> IOTT0 Outs (tocks X)"
  unfolding IOTT0_def by (simp add: IOTT0_trace_tocks_imp1) 

lemma IOTT0_trace_append_refusal:
  "IOTT0_trace Outs (t @ [[X]\<^sub>R]) = IOTT0_trace Outs t @ [[X \<union> Event ` Outs]\<^sub>R]"
  by (induct t rule:IOTT0_trace.induct, auto)

lemma IOTT0_trace_append_event:
  "IOTT0_trace Outs (t @ [[e]\<^sub>E]) = IOTT0_trace Outs t @ [[e]\<^sub>E]"
  by (induct t rule:IOTT0_trace.induct, auto)

lemma IOTT0_trace_append:
  "IOTT0_trace Outs (s @ t) = IOTT0_trace Outs s @ IOTT0_trace Outs t"
  by (induct s rule:IOTT0_trace.induct, auto)

lemma IOTT0_trace_prefix_eq:
  "t \<le>\<^sub>C IOTT0_trace Outs s \<Longrightarrow> t = IOTT0_trace Outs t"
  by (induct t s rule:tt_prefix_subset.induct, auto)

lemma IOTT0_trace_prefix_monotonic:
  "t \<le>\<^sub>C s \<Longrightarrow> IOTT0_trace Outs t \<le>\<^sub>C IOTT0_trace Outs s"
  by (induct t s rule:tt_prefix_subset.induct, auto)

lemma IOTT0_trace_prefix_monotonic_inv:
  "t \<le>\<^sub>C IOTT0_trace Outs s \<Longrightarrow> \<exists> t'. t = IOTT0_trace Outs t' \<and> t' \<le>\<^sub>C s"
  apply (induct t s rule:tt_prefix_subset.induct, auto)
  apply (metis IOTT0_trace.simps(1) tt_prefix.simps(1))
  apply (metis IOTT0_trace.simps(3) tt_prefix.simps(2))
  apply (metis IOTT0_trace.simps(2) tt_prefix.simps(2))
  done

lemma IOTT0_trace_same_length:
  "length t = length (IOTT0_trace Outs t)"
  by (induct t rule:IOTT0_trace.induct, auto)

lemma IOTT0_trace_same_tock_length:
  "length (filter (\<lambda>x. x = [Tock]\<^sub>E) t) = length (filter (\<lambda>x. x = [Tock]\<^sub>E) (IOTT0_trace Outs t))"
  by (induct t rule:IOTT0_trace.induct, auto)

section \<open>Refinement and Conformance\<close>

(* Refinement from tick-tock can be reused *)

subsection \<open>Traces Refinement\<close>

fun tttrace_to_event_trace :: "'e tttrace \<Rightarrow> 'e ttevent list" where
  "tttrace_to_event_trace [] = []" |
  "tttrace_to_event_trace ([X]\<^sub>R # t) = tttrace_to_event_trace t" |
  "tttrace_to_event_trace ([e]\<^sub>E # t) = e # tttrace_to_event_trace t"

definition tracesTT :: "'e ttprocess \<Rightarrow> 'e ttevent list set" where
  "tracesTT P = {t. \<exists> s\<in>P. t = tttrace_to_event_trace s}"

definition TracesRefinementTT :: "'e ttprocess \<Rightarrow> 'e ttprocess \<Rightarrow> bool" (infix "\<sqsubseteq>\<^sub>T" 50) where
  "P \<sqsubseteq>\<^sub>T Q = (tracesTT Q \<subseteq> tracesTT P)"

subsection \<open>Conformance\<close>

definition ConfTT :: "'e ttprocess \<Rightarrow> 'e ttprocess \<Rightarrow> bool" (infix "conf\<^sub>C" 50) where
  "P conf\<^sub>C Q = 
    (\<forall> t \<in> (tracesTT P) \<inter> (tracesTT Q). 
      {s\<in>Q. tttrace_to_event_trace s = t} \<subseteq> {s\<in>P. tttrace_to_event_trace s = t})"

lemma refines_eq_traces_refines_and_conf:
  "P \<sqsubseteq>\<^sub>C Q = (P \<sqsubseteq>\<^sub>T Q \<and> P conf\<^sub>C Q)"
  unfolding RefinesTT_def TracesRefinementTT_def ConfTT_def tracesTT_def by auto

end