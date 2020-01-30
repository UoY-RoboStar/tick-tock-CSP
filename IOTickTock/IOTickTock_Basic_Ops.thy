theory IOTickTock_Basic_Ops
  imports IOTickTock_Core
begin

section \<open>Divergence\<close>

lemma IOTT0_DivTT:
 "IOTT0 Outs div\<^sub>C"
  unfolding IOTT0_def DivTT_def by auto

section \<open>Termination\<close>

lemma IOTT0_SkipTT:
  "IOTT0 Outs SKIP\<^sub>C"
  unfolding IOTT0_def SkipTT_def by (auto simp add: append_eq_Cons_conv)

section \<open>Timed Stop\<close>

lemma IOTT0_StopTT:
  "IOTT0 Outs STOP\<^sub>C"
  unfolding IOTT0_def StopTT_def
proof auto
  fix s :: "'a tttrace"
  assume case_assm: "s \<in> tocks {x. x \<noteq> Tock}"
  have "IOTT0 Outs (tocks {x. x \<noteq> Tock})"
    by (simp add: IOTT0_tocks image_subsetI)
  then have "IOTT0_trace Outs s \<in> tocks {x. x \<noteq> Tock}"
    unfolding IOTT0_def using case_assm by blast
  then show "\<exists>sa\<in>tocks {x. x \<noteq> Tock}. IOTT0_trace Outs s = sa \<or> (\<exists>X. IOTT0_trace Outs s = sa @ [[X]\<^sub>R] \<and> Tock \<notin> X)"
    by auto
next
  fix X :: "'a ttevent set"
  fix s :: "'a tttrace"
  assume case_assms: "s \<in> tocks {x. x \<noteq> Tock}" "Tock \<notin> X"
  have "IOTT0 Outs (tocks {x. x \<noteq> Tock})"
    by (simp add: IOTT0_tocks image_subsetI)
  then have "IOTT0_trace Outs s \<in> tocks {x. x \<noteq> Tock}"
    unfolding IOTT0_def using case_assms(1) by blast
  then show "\<exists>sa\<in>tocks {x. x \<noteq> Tock}.
              IOTT0_trace Outs (s @ [[X]\<^sub>R]) = sa \<or> (\<exists>Xa. IOTT0_trace Outs (s @ [[X]\<^sub>R]) = sa @ [[Xa]\<^sub>R] \<and> Tock \<notin> Xa)"
    apply (rule_tac x="IOTT0_trace Outs s" in bexI, auto, erule_tac x="X \<union> Event ` Outs" in allE)
    by (auto simp add: IOTT0_trace_append_refusal case_assms)
qed

section \<open>Untimed Stop\<close>

lemma IOTT0_UntimedStopTT:
  "IOTT0 Outs STOP\<^sub>U"
  unfolding IOTT0_def UntimedStopTT_def by auto

section \<open>Delay\<close>

lemma IOTT0_WaitTT:
  "IOTT0 Outs wait\<^sub>C[x]"
  unfolding IOTT0_def WaitTT_def
proof auto
  fix s :: "'a tttrace"
  assume case_assms: "s \<in> tocks {x. x \<noteq> Tock}" "length (filter (\<lambda>x. x = [Tock]\<^sub>E) s) < x"
  have "IOTT0 Outs (tocks {x. x \<noteq> Tock})"
    by (simp add: IOTT0_tocks image_subsetI)
  then have "IOTT0_trace Outs s \<in> tocks {x. x \<noteq> Tock}"
    using IOTT0_def case_assms(1) by blast
  then show "\<exists>sa\<in>tocks {x. x \<noteq> Tock}. length (filter (\<lambda>x. x = [Tock]\<^sub>E) sa) < x
      \<and> (IOTT0_trace Outs s = sa \<or> (\<exists>X. Tock \<notin> X \<and> IOTT0_trace Outs s = sa @ [[X]\<^sub>R]))"
    by (rule_tac x="IOTT0_trace Outs s" in bexI, auto, metis IOTT0_trace_same_tock_length case_assms(2))
next
  fix X :: "'a ttevent set"
  fix s :: "'a tttrace"
  assume case_assms: "s \<in> tocks {x. x \<noteq> Tock}" "length (filter (\<lambda>x. x = [Tock]\<^sub>E) s) < x" "Tock \<notin> X"
  have "IOTT0 Outs (tocks {x. x \<noteq> Tock})"
    by (simp add: IOTT0_tocks image_subsetI)
  then have "IOTT0_trace Outs s \<in> tocks {x. x \<noteq> Tock}"
    using IOTT0_def case_assms(1) by blast
  then show "\<exists>sa\<in>tocks {x. x \<noteq> Tock}. length (filter (\<lambda>x. x = [Tock]\<^sub>E) sa) < x
    \<and> (IOTT0_trace Outs (s @ [[X]\<^sub>R]) = sa \<or> (\<exists>Xa. Tock \<notin> Xa \<and> IOTT0_trace Outs (s @ [[X]\<^sub>R]) = sa @ [[Xa]\<^sub>R]))"
    apply (rule_tac x="IOTT0_trace Outs s" in bexI, safe, simp_all)
    apply (metis IOTT0_trace_same_tock_length case_assms(2))
    by (meson IOTT0_trace_append_refusal Un_iff case_assms(3) imageE ttevent.simps(3))
next
  fix s :: "'a tttrace"
  assume case_assms: "s \<in> tocks {x. x \<noteq> Tock}" "x = length (filter (\<lambda>x. x = [Tock]\<^sub>E) s)"
  have "IOTT0 Outs (tocks {x. x \<noteq> Tock})"
    by (simp add: IOTT0_tocks image_subsetI)
  then have "IOTT0_trace Outs s \<in> tocks {x. x \<noteq> Tock}"
    using IOTT0_def case_assms(1) by blast
  then show "\<forall>sa\<in>tocks {x. x \<noteq> Tock}.
            length (filter (\<lambda>x. x = [Tock]\<^sub>E) sa) = length (filter (\<lambda>x. x = [Tock]\<^sub>E) s) \<longrightarrow>
            IOTT0_trace Outs s \<noteq> sa \<and> IOTT0_trace Outs s \<noteq> sa @ [[Tick]\<^sub>E] \<Longrightarrow>
         \<exists>sa\<in>tocks {x. x \<noteq> Tock}.
            length (filter (\<lambda>x. x = [Tock]\<^sub>E) sa) < length (filter (\<lambda>x. x = [Tock]\<^sub>E) s) \<and>
            (IOTT0_trace Outs s = sa \<or> (\<exists>X. Tock \<notin> X \<and> IOTT0_trace Outs s = sa @ [[X]\<^sub>R]))"
    by (erule_tac x="IOTT0_trace Outs s" in ballE, auto, metis IOTT0_trace_same_tock_length)
next
  fix s :: "'a tttrace"
  assume case_assms: "s \<in> tocks {x. x \<noteq> Tock}" "x = length (filter (\<lambda>x. x = [Tock]\<^sub>E) s)"
  have "IOTT0 Outs (tocks {x. x \<noteq> Tock})"
    by (simp add: IOTT0_tocks image_subsetI)
  then have "IOTT0_trace Outs s \<in> tocks {x. x \<noteq> Tock}"
    using IOTT0_def case_assms(1) by blast
  then show "\<forall>sa\<in>tocks {x. x \<noteq> Tock}.
            length (filter (\<lambda>x. x = [Tock]\<^sub>E) sa) = length (filter (\<lambda>x. x = [Tock]\<^sub>E) s) \<longrightarrow>
            IOTT0_trace Outs (s @ [[Tick]\<^sub>E]) \<noteq> sa \<and> IOTT0_trace Outs (s @ [[Tick]\<^sub>E]) \<noteq> sa @ [[Tick]\<^sub>E] \<Longrightarrow>
         \<exists>sa\<in>tocks {x. x \<noteq> Tock}.
            length (filter (\<lambda>x. x = [Tock]\<^sub>E) sa) < length (filter (\<lambda>x. x = [Tock]\<^sub>E) s) \<and>
            (IOTT0_trace Outs (s @ [[Tick]\<^sub>E]) = sa \<or> (\<exists>X. Tock \<notin> X \<and> IOTT0_trace Outs (s @ [[Tick]\<^sub>E]) = sa @ [[X]\<^sub>R]))"
    apply (erule_tac x="IOTT0_trace Outs s" in ballE, insert , auto)
    apply (metis IOTT0_trace_same_tock_length)
    using IOTT0_trace_append_event by blast
qed

section \<open>Guard\<close>

lemma IOTT0_GuardTT:
  "IOTT0 Outs P \<Longrightarrow> IOTT0 Outs (b &\<^sub>C P)"
  using IOTT0_StopTT unfolding GuardTT_def IOTT0_def by blast

end
