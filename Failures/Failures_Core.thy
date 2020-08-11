theory Failures_Core

imports
 Main
 HOL.List
 "HOL-Library.Sublist"
begin

section \<open> Type Definitions\<close>

datatype 'a evt = tick | evt 'a

type_synonym 'a trace = "'a evt list"
type_synonym 'a failure = "('a trace * 'a evt set)"
type_synonym 'a state = "('a failure) option"
type_synonym 'a prel = "('a state * 'a state) set"

text \<open> In Failures a CSP process is denoted by a pair of
        failures (set of failures) and traces (set of traces).\<close>

type_synonym 'a process = "('a failure) set \<times> ('a trace) set"

section \<open> Healthiness Conditions \<close>

definition traces :: "'a process \<Rightarrow> ('a trace) set" ("traces'(_')")
  where "traces P = snd P"

text \<open> T0: tick can only be the last event of a trace \<close>

fun Tick_last :: "'a trace \<Rightarrow> bool" where
"Tick_last [] = True" |
"Tick_last [tick] = True" |
"Tick_last (x#xs) = ((x \<noteq> tick) \<and> Tick_last xs)"

definition T0 :: "'a process \<Rightarrow> bool"
  where "T0 P \<equiv> \<forall>s. s \<in> traces(P) \<longrightarrow> Tick_last s"

lemma Tick_last_last:
  assumes "Tick_last (s@[tick])" "s \<noteq> []"
  shows "last s \<noteq> tick"
  using assms by (induct s rule:Tick_last.induct, auto)
 
text \<open> T1: traces is non-empty and prefix-closed \<close>

definition T1 :: "'a process \<Rightarrow> bool"
  where "T1 P \<equiv> traces(P) \<noteq> {} \<and> (\<forall>t s. t \<in> traces(P) \<and> prefix s t \<longrightarrow> s \<in> traces(P))"

text \<open> T2: Every trace associated with a failure is a trace. \<close>

definition T2 :: "'a process \<Rightarrow> bool"
  where "T2 P \<equiv> \<forall>s X. (s, X) \<in> (fst P) \<longrightarrow> s \<in> traces(P)"
 
text \<open> F2: Failures are subset-closed. \<close>
 
definition F2 :: "'a process \<Rightarrow> bool"
 where "F2 P \<equiv> \<forall>s X Y. (s, X) \<in> (fst P) \<and> Y \<subseteq> X \<longrightarrow> (s, Y) \<in> (fst P)"
 
text \<open> F3: When a process refuses $x$ it also refuses all events that
            it can never perform after the same trace. \<close>
 
definition F3 :: "'a process \<Rightarrow> bool"
  where "F3 P \<equiv> \<forall>s X Y. ((s, X) \<in> (fst P) \<and> (Y \<inter> {x. (s@[x]) \<in> traces(P)} = {})) \<longrightarrow> (s, X \<union> Y) \<in> (fst P)"

text \<open> F4: When a process can terminate it can refuse to do anything else,
           and it is assumed to refuse everything after tick. \<close>

definition F4 :: "'a process \<Rightarrow> bool"
  where "F4 P \<equiv> \<forall>s. (s@[tick]) \<in> traces(P) \<longrightarrow> {(s,UNIV-{tick}),(s@[tick],UNIV)} \<subseteq> fst P"

text \<open> F5: A stable process must also refuse to terminate. \<close>

definition F5 :: "'a process \<Rightarrow> bool"
  where "F5 P \<equiv> \<forall>s X. (s,X) \<in> fst P \<longrightarrow> (s,X\<union>{tick}) \<in> fst P"

definition mkFailuresF5 :: "('a failure) set \<Rightarrow> ('a failure) set"
  where "mkFailuresF5 F = (F \<union> {(t,X). \<exists>Y. (t,Y) \<in> F \<and> X \<subseteq> Y\<union>{tick}})"

definition mkF25 :: "'a process \<Rightarrow> 'a process"
  where "mkF25 P = (fst P \<union> {(t,X). \<exists>Y. (t,Y) \<in> fst P \<and> X \<subseteq> Y\<union>{tick}}, snd P)"

lemma F5_F2_imp_mkF25_fixpoint:
  assumes "F5 P" "F2 P"
  shows "mkF25 P = P"
  using assms unfolding mkF25_def apply auto
  by (smt F2_def F5_def Un_absorb2 case_prod_beta' insert_is_Un mem_Collect_eq prod.collapse subsetI sup_commute)

lemma mkF25_fixpoint_imp_F5:
  assumes "mkF25 P = P"
  shows "F5 P"
  using assms unfolding F5_def apply auto 
  by (metis (mono_tags, lifting) Un_insert_right boolean_algebra_cancel.sup0 case_prod_conv fst_conv mem_Collect_eq mkF25_def subset_eq sup.cobounded2)

text \<open> F6: No refusals after tick. \<close>

definition F6 :: "'a process \<Rightarrow> bool"
  where "F6 P == \<forall>s X. (s@[tick],X) \<notin> fst P"

text \<open> Is it possible to define a sub-theory where Skip is unstable? ie. Without F4?
       Not sure which function is easier to define. \<close>

definition mkF4 :: "'a process \<Rightarrow> 'a process"
  where "mkF4 P = (fst P \<union> {(t,X). (\<exists>s. s@[tick] \<in> traces(P) \<and> ((t = s \<and> X = UNIV-{tick}) \<or> (t = s@[tick] \<and> X = UNIV)))},traces(P)) "

definition mkF24 :: "'a process \<Rightarrow> 'a process"
  where "mkF24 P = (fst P \<union> {(t,X). (\<exists>s. s@[tick] \<in> traces(P) \<and> ((t = s \<and> X \<subseteq> UNIV-{tick}) \<or> (t = s@[tick] \<and> X \<subseteq> UNIV)))},traces(P)) "

abbreviation "mkF24_Failure P == {(t,X). (\<exists>s. s@[tick] \<in> traces(P) \<and> ((t = s \<and> X \<subseteq> UNIV-{tick}) \<or> (t = s@[tick] \<and> X \<subseteq> UNIV)))}"

lemma T0_mkFailuresF5[simp]:
  assumes "T0 P"
  shows "T0 (mkFailuresF5 (fst P), snd P)"
  using assms unfolding mkFailuresF5_def T0_def traces_def by auto

lemma T1_mkFailuresF5[simp]:
  assumes "T1 P"
  shows "T1 (mkFailuresF5 (fst P), snd P)"
  using assms unfolding mkFailuresF5_def T1_def traces_def by auto

lemma T2_mkFailuresF5[simp]:
  assumes "T2 P"
  shows "T2 (mkFailuresF5 (fst P), snd P)"
  using assms unfolding mkFailuresF5_def T2_def traces_def by auto

lemma F2_mkFailuresF5[simp]:
  assumes "F2 P"
  shows "F2 (mkFailuresF5 (fst P), snd P)"
  using assms unfolding mkFailuresF5_def F2_def traces_def apply auto
  by (meson subset_trans)

lemma F3_mkFailuresF5[simp]:
  assumes "F3 P"
  shows "F3 (mkFailuresF5 (fst P), snd P)"
  using assms unfolding mkFailuresF5_def F3_def traces_def apply auto
  proof -
  fix s :: "'a evt list" and X :: "'a evt set" and Y :: "'a evt set" and Ya :: "'a evt set"
  assume a1: "\<forall>s X Y. (s, X) \<in> fst P \<and> Y \<inter> {x. s @ [x] \<in> snd P} = {} \<longrightarrow> (s, X \<union> Y) \<in> fst P"
  assume a2: "Y \<inter> {x. s @ [x] \<in> snd P} = {}"
    assume a3: "(s, Ya) \<in> fst P"
    assume a4: "X \<subseteq> insert tick Ya"
  assume a5: "\<forall>Ya. X \<subseteq> insert tick Ya \<longrightarrow> (s, Ya) \<in> fst P \<longrightarrow> \<not> Y \<subseteq> insert tick Ya"
    have "(s, Y \<union> Ya) \<in> fst P"
      using a3 a2 a1 by (metis Un_commute)
  then show "(s, X \<union> Y) \<in> fst P"
    using a5 a4 by (metis (no_types) Un_insert_right Un_subset_iff subset_refl subset_trans)
  qed
 
lemma F4_mkFailuresF5[simp]:
  assumes "F4 P"
  shows "F4 (mkFailuresF5 (fst P), snd P)"
  using assms unfolding mkFailuresF5_def F4_def traces_def by auto

lemma F5_mkFailuresF5[simp]:
  shows "F5 (mkFailuresF5 (fst P), snd P)"
  unfolding mkFailuresF5_def F5_def traces_def by auto

lemma F4_mkF4: "F4 (mkF4 P)"
  unfolding mkF4_def F4_def traces_def by auto

lemma F4_mkF24: "F4 (mkF24 P)"
  unfolding mkF24_def F4_def traces_def by auto

lemma F2_mkF24:
  assumes "F2 P"
  shows "F2 (mkF24 P)"
  using assms unfolding mkF24_def F2_def traces_def 
  apply auto
  by blast

lemma F4_imp_tick_failures:
  assumes "F4 P"
  shows "{(t, X). \<exists>s. s @ [tick] \<in> snd P \<and> (t = s \<and> X = UNIV - {tick} \<or> t = s @ [tick] \<and> X = UNIV)} \<subseteq> fst P"
  using assms 
  unfolding F4_def traces_def by auto

lemma mkF4_fixpoint:
  shows "mkF4 P = P \<longleftrightarrow> F4 P"
  apply auto
   apply (metis F4_mkF4) 
  unfolding mkF4_def traces_def 
  using F4_imp_tick_failures
  by (simp add: F4_imp_tick_failures Un_absorb2)

lemma F4_F2_imp_tick_failures:
  assumes "F4 P" "F2 P"
  shows "{(t, X). \<exists>s. s @ [tick] \<in> snd P \<and> (t = s \<and> X \<subseteq> UNIV - {tick} \<or> t = s @ [tick] \<and> X \<subseteq> UNIV)} \<subseteq> fst P"
  using assms 
  unfolding F4_def F2_def traces_def apply auto
  by blast

lemma F5_F2_imp_tick_failures:
  assumes "F5 P" "F2 P"
  shows "{(t, X). \<exists>Y. (t, Y) \<in> fst P \<and> X \<subseteq> insert tick Y} \<subseteq> fst P"
  using assms 
  unfolding F5_def F2_def traces_def apply auto
  by blast

lemma mkF24_fixpoint_imp:
  assumes "F4 P" "F2 P"
  shows "mkF24 P = P"
  using assms
  unfolding mkF24_def traces_def 
  using F4_F2_imp_tick_failures
  by (metis (mono_tags, lifting) Un_absorb2 mem_Collect_eq prod.collapse prod.simps(2) subset_eq)

lemma T1_mkF24:
  assumes "T1 P"
  shows "T1 (mkF24 P)"
  using assms unfolding T1_def traces_def mkF24_def by auto

lemma T1_prefix:
  assumes "T1 P" "s@[x] \<in> traces(P)"
  shows "s \<in> traces(P)"
  using assms T1_def prefixI by blast

lemma T2_mkF24:
  assumes "T2 P" "T1 P"
  shows "T2 (mkF24 P)"
  using assms(1) unfolding T1_def T2_def traces_def mkF24_def apply auto
  using assms(2) T1_prefix unfolding traces_def by blast

lemma F3_mkF24:
  assumes "F3 P"
  shows "F3 (mkF24 P)"
  using assms unfolding mkF24_def F3_def traces_def by auto

definition refines :: "'a process \<Rightarrow> 'a process \<Rightarrow> bool" (infix "\<sqsubseteq>" 60)
  where "P \<sqsubseteq> Q == fst Q \<subseteq> fst P \<and> snd Q \<subseteq> snd P"

lemma refines_rule:
  assumes "fst Q \<subseteq> fst P" "snd Q \<subseteq> snd P"
  shows "P \<sqsubseteq> Q"
  using assms unfolding refines_def by auto

lemma refines_refl:
  "P \<sqsubseteq> P"
  unfolding refines_def by auto

lemma refines_tran:
  assumes "P \<sqsubseteq> Q" "Q \<sqsubseteq> R"
  shows "P \<sqsubseteq> R"
  using assms unfolding refines_def by auto

lemma refines_asym:
  assumes "P \<sqsubseteq> Q" "Q \<sqsubseteq> P"
  shows "P = Q"
  using assms unfolding refines_def apply auto
  by (simp add: prod_eq_iff)


end