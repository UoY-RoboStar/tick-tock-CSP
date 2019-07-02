theory 
  TickTock_Max
imports
  "TickTock.TickTock_Core"
begin

section \<open> Healthiness conditions of Tick-Tock processes whose refusals are maximal. \<close>

text \<open> TTM1 requires that every event e that is not refused can be performed. \<close>

definition TTM1 :: "'e ttobs list set \<Rightarrow> bool" where
  "TTM1 P = (\<forall> \<rho> X e. (\<rho> @ [[X]\<^sub>R] \<in> P \<and> e \<notin> X \<and> e \<noteq> Tock) \<longrightarrow> \<rho> @ [[e]\<^sub>E] \<in> P)"

lemma TTM1_union_empty_trace:
  "TTM1(P \<union> {[]}) = TTM1(P)"
  unfolding TTM1_def by auto

definition mkTTM1 :: "'e ttobs list set \<Rightarrow> 'e ttobs list set" where
"mkTTM1 P = P \<union> {\<rho> @ [[e]\<^sub>E]|\<rho> X e. \<rho> @ [[X]\<^sub>R] \<in> P \<and> e \<notin> X \<and> e \<noteq> Tock}"

lemma TTM1_mkTTM1 [simp]: "TTM1 (mkTTM1 P)"
  unfolding mkTTM1_def TTM1_def by auto

lemma TT1w_mkTTM1:
  assumes "TT1w P"
  shows "TT1w (mkTTM1 P)"
  using assms unfolding mkTTM1_def TT1w_def apply auto
  by (meson tt_prefix_concat tt_prefix_notfront_is_whole)

text \<open> TTM2 is similar to TTM1, but requires Tock to happen after the refusal. \<close>

definition TTM2 :: "'e ttobs list set \<Rightarrow> bool" where
  "TTM2 P = (\<forall> \<rho> X e. (\<rho> @ [[X]\<^sub>R] \<in> P \<and> e \<notin> X \<and> e = Tock) \<longrightarrow> \<rho> @ [[X]\<^sub>R,[e]\<^sub>E] \<in> P)"

lemma TTM2_union_empty_trace:
  "TTM2(P \<union> {[]}) = TTM2(P)"
  unfolding TTM2_def by auto

definition mkTTM2 :: "'e ttobs list set \<Rightarrow> 'e ttobs list set" where
"mkTTM2 P = P \<union> {\<rho> @ [[X]\<^sub>R,[Tock]\<^sub>E]|\<rho> X. \<rho> @ [[X]\<^sub>R] \<in> P \<and> Tock \<notin> X}"

lemma TTM2_mkTTM2 [simp]: "TTM2 (mkTTM2 P)"
  unfolding mkTTM2_def TTM2_def by auto

lemma mkTTM2_mkTTM1_commute: "mkTTM2 (mkTTM1 P) = mkTTM1 (mkTTM2 P)"
  unfolding mkTTM2_def mkTTM1_def by auto

lemma mkTTM2_dist_union:
  "mkTTM2(P \<union> Q) = (mkTTM2(P) \<union> mkTTM2(Q))"
  unfolding mkTTM2_def by auto

lemma mkTTM2_in_mkTT1w_for_TT1w:
  assumes "TT1w P"
  shows "mkTTM2({\<rho>|\<rho> \<sigma>. \<rho> \<le>\<^sub>C \<sigma> \<and> \<sigma> \<in> P}) = ({\<rho>|\<rho> \<sigma>. \<rho> \<le>\<^sub>C \<sigma> \<and> \<sigma> \<in> mkTTM2(P)})"
  unfolding mkTTM2_def apply auto
  apply (rule_tac x="\<rho> @ [[X]\<^sub>R, [Tock]\<^sub>E]" in exI, auto)
  apply (simp add: tt_prefix_refl)
  using TT1w_def assms apply blast
  by (smt TT1w_prefix_concat_in Nil_is_append_conv append_Cons append_Nil2 append_eq_append_conv2 append_self_conv2 assms ttWF.simps(1) tt_prefix_append_split tt_prefix_notfront_is_whole tt_prefix_refl tt_prefix_same_front same_append_eq split_tocks)

lemma mkTTM2_mkTT1w_commute:
  assumes "TT1w P"
  shows "mkTTM2(mkTT1w(P)) = mkTT1w(mkTTM2(P))"
proof -
  have "mkTTM2(mkTT1w(P)) = mkTTM2(P \<union> {\<rho>|\<rho> \<sigma>. \<rho> \<le>\<^sub>C \<sigma> \<and> \<sigma> \<in> P})"
    unfolding mkTT1w_def by auto
  also have "... = mkTTM2(P) \<union> mkTTM2({\<rho>|\<rho> \<sigma>. \<rho> \<le>\<^sub>C \<sigma> \<and> \<sigma> \<in> P})"
    using mkTTM2_dist_union by auto
  also have "... = mkTTM2(P) \<union> {\<rho>|\<rho> \<sigma>. \<rho> \<le>\<^sub>C \<sigma> \<and> \<sigma> \<in> mkTTM2(P)}"
    using assms mkTTM2_in_mkTT1w_for_TT1w by blast
  also have "... = mkTT1w(mkTTM2(P))"
    unfolding mkTT1w_def by auto
  finally show ?thesis .
qed

lemma TT1w_mkTTM2:
  assumes "TT1w P"
  shows "TT1w (mkTTM2 P)"
proof -
  have "TT1w P = (P = mkTT1w(P))"
    using TT1w_fixpoint_mkTT1w by blast
  then have "TT1w (mkTTM2 P) = TT1w (mkTTM2(mkTT1w(P)))"
    using assms by auto
  also have "... = TT1w(mkTT1w(mkTTM2(P)))"
    using assms by (simp add: mkTTM2_mkTT1w_commute)
  also have "... = True"
    by (metis TT1w_fixpoint_mkTT1w assms mkTTM2_mkTT1w_commute)
  then show ?thesis using calculation by auto
qed

lemma TT1w_mkTTM1_mkTTM2_mkTT1w:
  "TT1w (mkTTM1 (mkTTM2 (mkTT1w P)))"
proof -
  have "TT1w (mkTTM2 (mkTT1w P))"
    using TT1w_mkTTM2 TT1w_mkTT1w by blast
  then have "TT1w (mkTTM1 (mkTTM2 (mkTT1w P)))"
    using TT1w_mkTTM1 by blast
  then show ?thesis .
qed

fun TTickTrace :: "('a ttobs) list \<Rightarrow> bool" where
"TTickTrace [] = True" |
"TTickTrace ([e]\<^sub>E # xs) = TTickTrace xs" |
"TTickTrace ([r]\<^sub>R # xs) = (Tick \<in> r \<and> TTickTrace xs)"

lemma TTickTrace_eq_add_Tick_refusal_trace_fixpoint:
  "TTickTrace t \<longleftrightarrow> add_Tick_refusal_trace t = t"
  by (induct t rule:add_Tick_refusal_trace.induct, auto)

lemma TTickTrace_dist_concat:
  "TTickTrace (xs @ ys) = (TTickTrace xs \<and> TTickTrace ys)"
  by (induct xs rule:TTickTrace.induct, auto)

lemma TTickTrace_prefix:
  assumes "TTickTrace s" "t \<le>\<^sub>C s" 
  shows "TTickTrace t"
  using assms apply (induct t s rule:tt_prefix.induct, auto)
  by (case_tac y, auto)

text \<open> TTM3 requires that every refusal in every trace contains Tick. \<close>

definition TTM3 :: "('a ttobs) list set \<Rightarrow> bool" where
"TTM3 P = (\<forall>t. t \<in> P \<longrightarrow> TTickTrace t)"

lemma TTM3_dist_union:
  "TTM3 (P \<union> Q) = (TTM3(P) \<and> TTM3(Q))"
  unfolding TTM3_def by auto

lemma TTM3_dist_empty_trace: "TTM3(P \<union> {[]}) = TTM3(P)"
  unfolding TTM3_def by auto

lemma TTM3_singleton_imp_prefixes:
  assumes "TTM3 {s}"
  shows "TTM3 {x. x \<le>\<^sub>C s}"
  using assms unfolding TTM3_def apply auto
  using TTickTrace_prefix by blast

lemma TTM3_singleton_mkTTM1:
  assumes "TTM3 {s}"
  shows "TTM3(mkTTM1 {x. x \<le>\<^sub>C s})"
  using assms unfolding mkTTM1_def TTM3_def apply auto
  using TTickTrace_prefix apply blast
  by (metis TTickTrace.simps(1) TTickTrace.simps(2) TTickTrace_dist_concat TTickTrace_prefix)

lemma TTM3_singleton_mkTTM2:
  assumes "TTM3 {s}"
  shows "TTM3(mkTTM2 {x. x \<le>\<^sub>C s})"
  using assms unfolding mkTTM2_def TTM3_def apply auto
  using TTickTrace_prefix apply blast
  by (metis TTickTrace.simps(2) TTickTrace.simps(3) TTickTrace_dist_concat TTickTrace_prefix)

lemma TTM3_imp_TTM3_mkTTM1_mkTTM2:
  assumes "TTM3 {s}"
  shows "TTM3 (mkTTM1 (mkTTM2 {x. x \<le>\<^sub>C s}))"
  using assms unfolding mkTTM1_def mkTTM2_def TTM3_def apply auto
  using TTickTrace_prefix apply blast
  apply (metis TTickTrace.simps(2) TTickTrace.simps(3) TTickTrace_dist_concat TTickTrace_prefix)
  by (metis TTickTrace.simps(1) TTickTrace.simps(2) TTickTrace_dist_concat TTickTrace_prefix)

lemma TTM3_imp_TTM3_mkTTM1_mkTTM2_mkTT1w:
  assumes "TTM3 {s}"
  shows "TTM3 (mkTTM1 (mkTTM2 (mkTT1w{s})))"
  using assms unfolding mkTTM1_def mkTTM2_def mkTT1w_def TTM3_def apply auto
  using TTickTrace_prefix apply blast
     apply (metis TTickTrace.simps(2) TTickTrace.simps(3) TTickTrace_dist_concat)
  apply (metis TTickTrace.simps(2) TTickTrace.simps(3) TTickTrace_dist_concat TTickTrace_prefix)
  apply (metis TTickTrace.simps(1) TTickTrace.simps(2) TTickTrace_dist_concat)
  by (metis TTickTrace.simps(2) TTickTrace.simps(3) TTickTrace_dist_concat TTickTrace_prefix)
  

text \<open> A useful weaker variant is defined by TTick, that considers a
       single refusal at the end of a trace to contain Tick. This is
       useful in some proofs. \<close>

definition TTick :: "('a ttobs) list set \<Rightarrow> bool" where
"TTick P = (\<forall>t X. t @ [[X]\<^sub>R] \<in> P \<longrightarrow> Tick \<in> X)"

lemma TTick_dist_union:
  "TTick (P \<union> Q) = (TTick(P) \<and> TTick(Q))"
  unfolding TTick_def by auto

lemma TTick_imp_TTick_mkTTM1_mkTTM2:
  assumes "TTick {s}"
  shows "TTick (mkTTM1 (mkTTM2 {s}))"
  using assms unfolding mkTTM2_def mkTTM1_def TTick_def by auto

lemma TTick_Nil [simp]:
  "TTick {[]}"
  unfolding TTick_def by auto

lemma TTick_dist_empty_trace: "TTick(P \<union> {[]}) = TTick(P)"
  unfolding TTick_def by auto

lemma TTick_Refusal_Tock [simp]:
  assumes "TTick {saa}"
  shows "TTick {[S]\<^sub>R # [Tock]\<^sub>E # saa}"
  using assms unfolding TTick_def apply auto                               
  by (metis (no_types, hide_lams) append.left_neutral append1_eq_conv append_Cons ttobs.distinct(1) rev_exhaust)                            

lemma TTick_Refusal_Tock':
  assumes "TTick {[S]\<^sub>R # [Tock]\<^sub>E # saa}"
  shows "TTick {saa}"
  using assms unfolding TTick_def by auto

lemma TTick_event [simp]:
  assumes "TTick {saa}"
  shows "TTick {[e]\<^sub>E # saa}"
  using assms unfolding TTick_def apply auto  
  by (metis Cons_eq_append_conv ttobs.distinct(1) list.inject)

end