theory IOTickTock_Core
  imports TickTock.TickTock
begin

fun IOTT0_trace :: "'e set \<Rightarrow> 'e tttrace \<Rightarrow> 'e tttrace" where
  "IOTT0_trace Outs [] = []" |
  "IOTT0_trace Outs ([e]\<^sub>E # t) = [e]\<^sub>E # IOTT0_trace Outs t" |
  "IOTT0_trace Outs ([X]\<^sub>R # t) = [X \<union> Event ` Outs]\<^sub>R # IOTT0_trace Outs t"

(* IOTT0: In a stable state, all output events must be refused of them must be refused *)
definition IOTT0 :: "'e set \<Rightarrow> 'e ttprocess \<Rightarrow> bool" where
  "IOTT0 Outs P = (\<forall> x. x \<in> P \<longrightarrow> IOTT0_trace Outs x \<in> P)"

lemma IOTT0_tocks:
  "Event ` Outs \<subseteq> X \<Longrightarrow> IOTT0 Outs (tocks X)"
  unfolding IOTT0_def
proof auto
  fix x
  assume assm: "Event ` Outs \<subseteq> X"
  show "x \<in> tocks X \<Longrightarrow> IOTT0_trace Outs x \<in> tocks X"
    by (induct x rule: tocks.induct, auto simp add: tocks.intros  assm)
qed

lemma IOTT0_trace_append_refusal:
  "IOTT0_trace Outs (t @ [[X]\<^sub>R]) = IOTT0_trace Outs t @ [[X \<union> Event ` Outs]\<^sub>R]"
  by (induct t rule:IOTT0_trace.induct, auto)

lemma IOTT0_trace_append_event:
  "IOTT0_trace Outs (t @ [[e]\<^sub>E]) = IOTT0_trace Outs t @ [[e]\<^sub>E]"
  by (induct t rule:IOTT0_trace.induct, auto)

lemma IOTT0_trace_append:
  "IOTT0_trace Outs (s @ t) = IOTT0_trace Outs s @ IOTT0_trace Outs t"
  by (induct s rule:IOTT0_trace.induct, auto)

lemma IOTT0_trace_same_length:
  "length t = length (IOTT0_trace Outs t)"
  by (induct t rule:IOTT0_trace.induct, auto)

lemma IOTT0_trace_same_tock_length:
  "length (filter (\<lambda>x. x = [Tock]\<^sub>E) t) = length (filter (\<lambda>x. x = [Tock]\<^sub>E) (IOTT0_trace Outs t))"
  by (induct t rule:IOTT0_trace.induct, auto)

end