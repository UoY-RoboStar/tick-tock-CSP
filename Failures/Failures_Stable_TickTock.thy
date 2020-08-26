theory Failures_Stable_TickTock
  imports Failures_TickTock Failures
begin

thm sf2f_def F2f_def mkF24_def ttproc2F_def

(* mapping from  tick-tock to stable failures (with stable tick) *)
definition tt2sf :: "'a ttprocess \<Rightarrow> 'a process" where
  "tt2sf P = 
    ({ (t, X) | t X. (map (\<lambda> e. [ttevt2F e]\<^sub>E) t) @ [[ttevt2F ` X]\<^sub>R] \<in> P }
      \<union> {(t, X) | t X. (map (\<lambda> e. [ttevt2F e]\<^sub>E) t) @ [[Tick]\<^sub>E] \<in> P \<and> X \<subseteq> UNIV-{tick}}
      \<union> {(t @ [tick], X) | t X. (map (\<lambda> e. [ttevt2F e]\<^sub>E) t) @ [[Tick]\<^sub>E] \<in> P \<and> X \<subseteq> UNIV}, 
    {tt2T y |y. y \<in> P})"

lemma end_tick_in_traces:
  "\<And>P. ttWF (map (\<lambda>e. [ttevt2F e]\<^sub>E) a @ [[Tick]\<^sub>E]) \<Longrightarrow>
       map (\<lambda>e. [ttevt2F e]\<^sub>E) a @ [[Tick]\<^sub>E] \<in> P \<Longrightarrow>
  a @ [tick] \<in> traces(({(s, X). \<exists>y. Some (s, X) = tt2F y \<and> y \<in> P}, {tt2T y |y. y \<in> P}))"
  apply (induct a, simp_all)
  using traces_def apply force
  apply (case_tac a1, simp_all)
  apply (metis Nil_is_append_conv neq_Nil_conv ttWF.simps(8))
proof -
  fix a1 a2 P x2
  assume ind_hyp: "\<And>P. map (\<lambda>e. [ttevt2F e]\<^sub>E) a2 @ [[Tick]\<^sub>E] \<in> P \<Longrightarrow>
           a2 @ [tick] \<in> traces(({(s, X). \<exists>y. Some (s, X) = tt2F y \<and> y \<in> P}, {tt2T y |y. y \<in> P}))"
  assume "[Event x2]\<^sub>E # map (\<lambda>e. [ttevt2F e]\<^sub>E) a2 @ [[Tick]\<^sub>E] \<in> P"
  then have "a2 @ [tick] \<in> traces(({(s, X). \<exists>y. Some (s, X) = tt2F y \<and> y \<in> {t. [Event x2]\<^sub>E # t \<in> P}},
         {tt2T y |y. y \<in> {t. [Event x2]\<^sub>E # t \<in> P}}))"
    using ind_hyp by force
  then show "evt x2 # a2 @ [tick] \<in> traces(({(s, X). \<exists>y. Some (s, X) = tt2F y \<and> y \<in> P}, {tt2T y |y. y \<in> P}))"
    by (smt mem_Collect_eq snd_conv traces_def tt2T.simps(2))
qed

lemma end_refusal_ttWF_eq:
  "ttWF (map (\<lambda>e. [ttevt2F e]\<^sub>E) a @ [[ttevt2F ` b]\<^sub>R])
    \<Longrightarrow> Some (a, b) = tt2F (map (\<lambda>e. [ttevt2F e]\<^sub>E) a @ [[ttevt2F ` b]\<^sub>R])"
  apply (induct a, auto)
  using Some_tt2F_set apply fastforce
  apply (case_tac a1, auto)
  apply (metis Nil_is_append_conv neq_Nil_conv ttWF.simps(8))
  by (metis fst_conv option.simps(5) snd_conv)

lemma tt2F_Some_ref_end_refusal:
  "\<And>a. Some (a, b) = tt2F y \<Longrightarrow>
    y = map (\<lambda>e. [ttevt2F e]\<^sub>E) a @ [[ttevt2F ` b]\<^sub>R]
    \<or> y = map (\<lambda>e. [ttevt2F e]\<^sub>E) a @ [[(ttevt2F ` b) \<union> {Tock}]\<^sub>R]"
  apply (induct y rule:ttWF.induct, auto)
    apply (smt image_def mem_Collect_eq ttevent.exhaust ttevt2F.simps(1) ttevt2F.simps(2))
  apply (case_tac xa, auto)
  apply (metis image_eqI mem_Collect_eq ttevt2F.simps(1))
   apply (metis mem_Collect_eq rev_image_eqI ttevt2F.simps(2))
  by (case_tac "tt2F \<sigma>", auto)

lemma tt2F_Some_ref_end_refusal_in_TT1:
  "TT1 P \<Longrightarrow> Some (a, b) = tt2F y \<Longrightarrow> y \<in> P \<Longrightarrow>
    map (\<lambda>e. [ttevt2F e]\<^sub>E) a @ [[ttevt2F ` b]\<^sub>R] \<in> P"
proof -
  assume TT1_P: "TT1 P"
  assume y_in_P: "y \<in> P"
  assume tt2F_y_Some: "Some (a, b) = tt2F y"

  have "y = map (\<lambda>e. [ttevt2F e]\<^sub>E) a @ [[ttevt2F ` b]\<^sub>R]
    \<or> y = map (\<lambda>e. [ttevt2F e]\<^sub>E) a @ [[(ttevt2F ` b) \<union> {Tock}]\<^sub>R]"
    using tt2F_Some_ref_end_refusal tt2F_y_Some by blast
  then show "map (\<lambda>e. [ttevt2F e]\<^sub>E) a @ [[ttevt2F ` b]\<^sub>R] \<in> P"
    using y_in_P
  proof auto
    have "map (\<lambda>e. [ttevt2F e]\<^sub>E) a @ [[ttevt2F ` b]\<^sub>R]
      \<lesssim>\<^sub>C map (\<lambda>e. [ttevt2F e]\<^sub>E) a @ [[insert Tock (ttevt2F ` b)]\<^sub>R]"
      by (induct a, auto)
    then show "map (\<lambda>e. [ttevt2F e]\<^sub>E) a @ [[insert Tock (ttevt2F ` b)]\<^sub>R] \<in> P
      \<Longrightarrow> map (\<lambda>e. [ttevt2F e]\<^sub>E) a @ [[ttevt2F ` b]\<^sub>R] \<in> P"
      using TT1_P TT1_def by blast
  qed
qed

lemma end_tick_in_traces_imp_in_ttproc:
  "\<And>P. s @ [tick] \<in> traces(({(s, X). \<exists>y. Some (s, X) = tt2F y \<and> y \<in> P}, {tt2T y |y. y \<in> P}))
    \<Longrightarrow> map (\<lambda>e. [ttevt2F e]\<^sub>E) s @ [[Tick]\<^sub>E] \<in> P"
proof (induct s, auto)
  fix P
  show "[tick] \<in> traces(({(s, X). \<exists>y. Some (s, X) = tt2F y \<and> y \<in> P}, {tt2T y |y. y \<in> P})) \<Longrightarrow> [[Tick]\<^sub>E] \<in> P"
    by (smt append_Nil mem_Collect_eq snd_conv tick_tt2T_concat_TickE traces_def tt2T_tick_exists_Cons)
next
  fix a s P
  assume ind_hyp: "\<And>P. s @ [tick] \<in> traces(({(s, X). \<exists>y. Some (s, X) = tt2F y \<and> y \<in> P}, {tt2T y |y. y \<in> P})) \<Longrightarrow>
             map (\<lambda>e. [ttevt2F e]\<^sub>E) s @ [[Tick]\<^sub>E] \<in> P"
  assume "a # s @ [tick] \<in> traces(({(s, X). \<exists>y. Some (s, X) = tt2F y \<and> y \<in> P}, {tt2T y |y. y \<in> P}))"
  then have "s @ [tick]
    \<in> traces(({(s, X). \<exists>y. Some (s, X) = tt2F y \<and> y \<in> {t. [ttevt2F a]\<^sub>E # t \<in> P}},
               {tt2T y |y. y \<in> {t. [ttevt2F a]\<^sub>E # t \<in> P}}))"
    unfolding traces_def
  proof auto
    fix y
    assume case_assms: "a # s @ [tick] = tt2T y" "y \<in> P"
    then obtain y' where y'_assms: "s @ [tick] = tt2T y' \<and> y = [ttevt2F a]\<^sub>E # y'"
      apply (cases y, auto, cases a, auto, case_tac aa, auto, case_tac x1, auto)
      apply (metis append_Cons neq_Nil_conv self_append_conv2 tt2T.simps(1) tt2T.simps(7))
      apply (case_tac aa, auto, case_tac x1, auto)
      by (metis append_Cons neq_Nil_conv self_append_conv2 tt2T.simps(1) tt2T.simps(7))
    then have "map (\<lambda>e. [ttevt2F e]\<^sub>E) s @ [[Tick]\<^sub>E] \<in> {t. [ttevt2F a]\<^sub>E # t \<in> P}"
      using ind_hyp[where P="{t. [ttevt2F a]\<^sub>E # t \<in> P}"] case_assms(2) traces_def by fastforce
    then show "\<exists>y. s @ [tick] = tt2T y \<and> [ttevt2F a]\<^sub>E # y \<in> P"
      using y'_assms case_assms(2) by blast
  qed
  then show "a # s @ [tick] \<in> traces(({(s, X). \<exists>y. Some (s, X) = tt2F y \<and> y \<in> P}, {tt2T y |y. y \<in> P})) \<Longrightarrow>
       [ttevt2F a]\<^sub>E # map (\<lambda>e. [ttevt2F e]\<^sub>E) s @ [[Tick]\<^sub>E] \<in> P"
    using ind_hyp by blast
qed

lemma tt2sf_eq_mkF24_ttproc2F:
  assumes P_wf: "\<forall>x\<in>P. ttWF x" and TT1_P: "TT1 P"
  shows "tt2sf P = mkF24 (ttproc2F P)"
  unfolding mkF24_def tt2sf_def ttproc2F_def
  apply auto
  using assms end_refusal_ttWF_eq apply blast
  using assms end_tick_in_traces apply blast
  using assms end_tick_in_traces apply blast
  apply (simp add: TT1_P tt2F_Some_ref_end_refusal_in_TT1)
  apply (simp add: TT1_P tt2F_Some_ref_end_refusal_in_TT1)
  using end_tick_in_traces_imp_in_ttproc apply blast
  using end_tick_in_traces_imp_in_ttproc apply blast
  using end_tick_in_traces_imp_in_ttproc apply blast
  by (auto simp add: traces_def)
  
end
  