theory Failures_TickTock_Interrupt

imports
  Failures_TickTock
begin

lemma Tock_not_in_set_empty_filter_tocks:
  assumes "[Tock]\<^sub>E \<notin> set xs" 
  shows "filter_tocks xs = []"
  using assms by (induct xs rule:filter_tocks.induct, auto)

lemma subset_Ref_trace_TT1_prefix:
  assumes "xs @ [[R]\<^sub>R] \<in> P" "TT1 P" "S \<subseteq> R"
  shows "xs @ [[S]\<^sub>R] \<in> P"
  using assms
  by (meson TT1_def empty_subsetI tt_prefix_subset.simps(1) tt_prefix_subset.simps(2) tt_prefix_subset_same_front)

lemma Tock_not_image_iff_ttevt2F_Set:
  assumes "Tock \<notin> R"
  shows "ttevt2F`{x. ttevt2F x \<in> R} = R"
  using assms unfolding image_def
    apply auto
  by (metis ttevent.exhaust ttevt2F.simps(1) ttevt2F.simps(2))

lemma ttevt2F_eq_Sets_diff_Tock:
  assumes "{x. ttevt2F x \<in> R} = {x. ttevt2F x \<in> Z}"
  shows "R-{Tock} = Z-{Tock}"
proof -
    have "tt2F [[Z]\<^sub>R] = tt2F [[R]\<^sub>R]"
    using assms by force
  then show ?thesis
    by (metis (no_types) DiffE list.inject singletonI tt2F_refusal_eq tt2F_refusal_without_Tock ttobs.inject(2))
qed

lemma Some_tt2F_tt2T:
  assumes "Some (t, b) = tt2F ya"  "t \<noteq> []" "tick \<notin> set (tt2T y)" "\<not>(\<exists>R. [R]\<^sub>R \<in> set y)" "ttWF y"
  shows "Some (tt2T y @ t, b) = tt2F (y @ ya)"
  using assms apply (induct y arbitrary: ya b, auto)
  apply (case_tac a, auto)
  apply (case_tac x1, auto)
  apply (metis (mono_tags, lifting) fst_conv option.simps(5) snd_conv)
  by (metis list.exhaust_sel list.set_intros(1) tt2T.simps(1) ttWF.simps(8))

lemma ttWF_no_Ref_no_Tock:
  assumes "\<not>(\<exists>R. [R]\<^sub>R \<in> set ys)" "ttWF ys"
  shows "[Tock]\<^sub>E \<notin> set ys"
  using assms by (induct ys rule:ttWF.induct, auto)

lemma exists_Refusal_tt2T_concat_Ref_end:
  assumes "\<exists>R. [R]\<^sub>R \<in> set y" "tick \<notin> set (tt2T y)" "ttWF y"
  shows "\<exists>ys R. tt2T y = tt2T (ys@[[R]\<^sub>R]) \<and> \<not>(\<exists>R. [R]\<^sub>R \<in> set ys) \<and> [Tick]\<^sub>E \<notin> set ys \<and> ttWF (ys@[[R]\<^sub>R]) \<and> [Tock]\<^sub>E \<notin> set ys \<and> ys@[[R]\<^sub>R] \<lesssim>\<^sub>C y"
  using assms apply (induct y rule:rev_induct, auto)
  by (smt ttWF_no_Ref_no_Tock Ref_in_concat_lhs Tick_set_ends_in_Tick Un_iff append1_eq_conv set_append ttWF_prefix_is_ttWF tt_prefix_concat tt_prefix_subset_refl tt_prefix_subset_tt_prefix_trans)+

lemma tt2T_Tick_concat_lhs:
  assumes "[Tick]\<^sub>E \<notin> set ys" 
  shows "tt2T (ys @ [[Y]\<^sub>R]) = tt2T ys"
  using Ref_in_concat_lhs Tock_in_concat_lhs assms tt2T_concat_dist by fastforce

lemma ttproc2F_InterruptF_failures_subseteq_TimeSyncInterruptTT:
  assumes ttWF_P: "TTwf P" and TT0_P: "TT0 P" and TT1_P: "TT1 P"
      and ttWF_Q: "TTwf Q" and TT0_Q: "TT0 Q" and TT1_Q: "TT1 Q"
  shows "fst ((ttproc2F P) \<triangle>\<^sub>F (ttproc2F Q)) \<subseteq> fst (ttproc2F (P \<triangle>\<^sub>T Q))" 
  using assms unfolding ttproc2F_def TimeSyncInterruptTT_def InterruptF_def 
proof (auto)
  fix a b y ya
  assume "Some (a, b) = tt2F y"
       "y \<in> P"
       "Some ([], b) = tt2F ya"
       "ya \<in> Q"
  then obtain xs R where xs_X:"y = xs@[[R]\<^sub>R] \<and> tt2T xs = a \<and> b = {x. ttevt2F x \<in> R} \<and> [Tock]\<^sub>E \<notin> set xs \<and> ttWF(xs@[[R]\<^sub>R])"
    using Some_tt2F_concat_refusal by blast
  then obtain Z where "ya = [[Z]\<^sub>R] \<and> Z -{Tock} = R -{Tock}"
    using \<open>Some ([], b) = tt2F ya\<close> tt2F_some_exists ttevt2F_eq_Sets_diff_Tock
    by (smt Some_tt2F_concat_refusal \<open>\<And>thesis. (\<And>xs R. y = xs @ [[R]\<^sub>R] \<and> tt2T xs = a \<and> b = {x. ttevt2F x \<in> R} \<and> [Tock]\<^sub>E \<notin> set xs \<and> ttWF (xs @ [[R]\<^sub>R]) \<Longrightarrow> thesis) \<Longrightarrow> thesis\<close> append1_eq_conv tt2F.simps(1) ttobs.inject(2))
  
  from xs_X show"
       \<exists>ya. tt2F y = tt2F ya \<and>
            ((\<exists>p. p @ [[Tick]\<^sub>E] \<in> P \<and> filter_tocks p \<in> Q \<and> ya = p @ [[Tick]\<^sub>E]) \<or>
             (\<exists>p X. p @ [[X]\<^sub>R] \<in> P \<and>
                    (\<exists>Y. filter_tocks p @ [[Y]\<^sub>R] \<in> Q \<and>
                         (\<exists>Z\<subseteq>X \<union> Y. {e \<in> X. e \<noteq> Tock} = {e \<in> Y. e \<noteq> Tock} \<and> ya = p @ [[Z]\<^sub>R]))) \<or>
             (\<exists>p. p \<in> P \<and>
                  (\<forall>p'. p \<noteq> p' @ [[Tick]\<^sub>E]) \<and>
                  (\<forall>p' Y. p \<noteq> p' @ [[Y]\<^sub>R]) \<and> (\<exists>q2. filter_tocks p @ q2 \<in> Q \<and> (\<forall>q' Y. q2 \<noteq> [Y]\<^sub>R # q') \<and> ya = p @ q2)))"
    apply (rule_tac x="xs@[[R]\<^sub>R]" in exI, auto)
    apply (rule_tac x="xs" in exI, auto)  
    apply (rule_tac x="R" in exI, auto)
    using \<open>y \<in> P\<close> TT1_P subset_Ref_trace_TT1_prefix 
    apply blast
    apply (rule_tac x="Z" in exI, auto)
    using Tock_not_in_set_empty_filter_tocks
    using \<open>ya = [[Z]\<^sub>R] \<and> Z - {Tock} = R - {Tock}\<close> \<open>ya \<in> Q\<close> by force+
next
  fix b t y ya
  assume assm1:"t \<noteq> []"
  and    assm2:"y \<in> P"
  and    assm3:"Some (t, b) = tt2F ya"
  and    assm4:"ya \<in> Q"
  and    assm5:"tick \<notin> set (tt2T y)"
  then obtain xs R where xs_X:"ya = xs@[[R]\<^sub>R] \<and> tt2T xs = t \<and> b = {x. ttevt2F x \<in> R} \<and> [Tock]\<^sub>E \<notin> set xs \<and> ttWF(xs@[[R]\<^sub>R])"
    using Some_tt2F_concat_refusal by blast

  have tt2T_ya:"tt2T ya = t"
    using assm3 Some_tt2F_imp_tt2T' by blast

  show "\<exists>ya. Some (tt2T y @ t, b) = tt2F ya \<and>
            ((\<exists>p. p @ [[Tick]\<^sub>E] \<in> P \<and> filter_tocks p \<in> Q \<and> ya = p @ [[Tick]\<^sub>E]) \<or>
             (\<exists>p X. p @ [[X]\<^sub>R] \<in> P \<and>
                    (\<exists>Y. filter_tocks p @ [[Y]\<^sub>R] \<in> Q \<and>
                         (\<exists>Z\<subseteq>X \<union> Y. {e \<in> X. e \<noteq> Tock} = {e \<in> Y. e \<noteq> Tock} \<and> ya = p @ [[Z]\<^sub>R]))) \<or>
             (\<exists>p. p \<in> P \<and>
                  (\<forall>p'. p \<noteq> p' @ [[Tick]\<^sub>E]) \<and>
                  (\<forall>p' Y. p \<noteq> p' @ [[Y]\<^sub>R]) \<and> (\<exists>q2. filter_tocks p @ q2 \<in> Q \<and> (\<forall>q' Y. q2 \<noteq> [Y]\<^sub>R # q') \<and> ya = p @ q2)))"
  proof (cases "\<exists>R. [R]\<^sub>R \<in> set y")
    case True (* Can obtain the first refusal somewhere in the trace *)
    then obtain ys Y where ys_Y:"tt2T y = tt2T (ys@[[Y]\<^sub>R]) \<and> \<not>(\<exists>R. [R]\<^sub>R \<in> set ys) \<and> [Tick]\<^sub>E \<notin> set ys \<and> ttWF (ys@[[Y]\<^sub>R]) \<and> [Tock]\<^sub>E \<notin> set ys \<and> ys@[[Y]\<^sub>R] \<lesssim>\<^sub>C y"
      using exists_Refusal_tt2T_concat_Ref_end
      by (metis TTwf_def assm2 assm5 ttWF_P)
    then have "tt2T (ys) @ tt2T ya = tt2T (ys @ ya)"
      by (simp add: tt2T_concat_dist)
    then show ?thesis
      using ys_Y tt2T_ya  apply (rule_tac x="ys@ya" in exI, auto)
      using ys_Y tt2T_Tick_concat_lhs apply (metis Some_concat_extend assm3)
      apply (rule_tac x="ys" in exI, auto)
      apply (rule_tac x="Y" in exI, auto)
      using TT1_P TT1_def assm2 apply blast
      by (smt TT1_P TT1_def Tock_not_in_set_empty_filter_tocks append.left_neutral assm1 assm2 assm4 in_set_conv_decomp tt2T.simps(5) tt_prefix_subset_front)
  next
    case False (* y is only events, no Tocks, Refusals or Ticks *)
    then show ?thesis
      apply (rule_tac x="y@ya" in exI, auto)
      using assm1 assm2 assm5 Some_tt2F_tt2T TTwf_def assm3 ttWF_P apply blast
      using xs_X apply auto
      apply (rule_tac x="y" in exI, auto)
      by (smt Some_tt2F_imp_tt2T' Some_tt2F_no_Tick Some_tt2F_no_Tock Some_tt2F_tt2T TTwf_def Tock_not_in_set_empty_filter_tocks Un_iff append.left_neutral assm1 assm2 assm3 assm4 assm5 list.set_intros(1) set_append tt2T.simps(5) ttWF_P)
  qed
qed

lemma no_Tock_end_Ref_no_Tock_before:
  assumes "p = xs@[[R]\<^sub>R]" "[Tock]\<^sub>E \<notin> set xs"
  shows "[Tock]\<^sub>E \<notin> set p"
  using assms by (induct p arbitrary:, auto)

lemma tt2F_refusal_minus_Tock:
  shows "tt2F (p @ [[Z]\<^sub>R]) = tt2F (p @ [[Z - {Tock}]\<^sub>R])"
  apply (induct p rule:tt2F.induct, auto)
  by (metis evt.exhaust ttevent.distinct(1) ttevent.distinct(5) ttevt2F.simps(1) ttevt2F.simps(2))

lemma ttproc2F_TimeSyncInterruptTT_failures_subseteq_InterruptF:
  assumes TTWF_P: "TTwf P" and TT0_P: "TT0 P" and TT1_P: "TT1 P"
      and TTWF_Q: "TTwf Q" and TT0_Q: "TT0 Q" and TT1_Q: "TT1 Q"
  shows "fst (ttproc2F (P \<triangle>\<^sub>T Q)) \<subseteq> fst ((ttproc2F P) \<triangle>\<^sub>F (ttproc2F Q))" 
  using assms unfolding ttproc2F_def TimeSyncInterruptTT_def InterruptF_def 
proof (simp_all, safe, blast)
  fix a b y p
  assume "\<nexists>s t. a = s @ t \<and> (\<exists>y. s = tt2T y \<and> y \<in> P) \<and> (\<exists>y. Some (t, b) = tt2F y \<and> y \<in> Q) \<and> t \<noteq> [] \<and> tick \<notin> set s"
         "Some (a, b) = tt2F (p @ [[Tick]\<^sub>E])" 
         "p @ [[Tick]\<^sub>E] \<in> P" 
         "filter_tocks p \<in> Q"
  then show "\<exists>y. Some ([], b) = tt2F y \<and> y \<in> Q"
    by (meson Some_tt2F_no_Tick Tick_no_eq)
next
  fix a b y p X Y Z
  assume assm1:"\<nexists>s t. a = s @ t \<and> (\<exists>y. s = tt2T y \<and> y \<in> P) \<and> (\<exists>y. Some (t, b) = tt2F y \<and> y \<in> Q) \<and> t \<noteq> [] \<and> tick \<notin> set s"
  and    assm2:"Some (a, b) = tt2F (p @ [[Z]\<^sub>R])"
  and    assm3:"p @ [[X]\<^sub>R] \<in> P"
  and    assm4:"filter_tocks p @ [[Y]\<^sub>R] \<in> Q"
  and    assm5:"Z \<subseteq> X \<union> Y"
  and    assm6:"{e \<in> X. e \<noteq> Tock} = {e \<in> Y. e \<noteq> Tock}"
  then have "Z-{Tock} \<subseteq> X"
    by blast 
  then have "p @ [[Z-{Tock}]\<^sub>R] \<in> P"
    using TT1_P \<open>p @ [[X]\<^sub>R] \<in> P\<close> subset_Ref_trace_TT1_prefix by blast
  then show "\<exists>y. Some (a, b) = tt2F y \<and> y \<in> P"
    using assm2 assm3 apply (rule_tac x="p @ [[Z-{Tock}]\<^sub>R]" in exI, simp)
    using tt2F_refusal_minus_Tock by blast
next
  fix a b y p X Y Z
  assume assm1:"\<nexists>s t. a = s @ t \<and> (\<exists>y. s = tt2T y \<and> y \<in> P) \<and> (\<exists>y. Some (t, b) = tt2F y \<and> y \<in> Q) \<and> t \<noteq> [] \<and> tick \<notin> set s"
  and    assm2:"Some (a, b) = tt2F (p @ [[Z]\<^sub>R])"
  and    assm3:"p @ [[X]\<^sub>R] \<in> P"
  and    assm4:"filter_tocks p @ [[Y]\<^sub>R] \<in> Q"
  and    assm5:"Z \<subseteq> X \<union> Y"
  and    assm6:"{e \<in> X. e \<noteq> Tock} = {e \<in> Y. e \<noteq> Tock}"
  then have "[Tock]\<^sub>E \<notin> set p"
    using Some_tt2F_concat_refusal by force
  then have ft_p_Nil:"filter_tocks p = []"
    using Tock_not_in_set_empty_filter_tocks by blast

  have "Z-{Tock} \<subseteq> Y"
    using assm5 assm6 by auto
  then have "[[Z-{Tock}]\<^sub>R] \<in> Q"
    by (metis TT1_Q assm4 eq_Nil_appendI ft_p_Nil subset_Ref_trace_TT1_prefix)
  then show "\<exists>y. Some ([], b) = tt2F y \<and> y \<in> Q"
    using assm2 apply (rule_tac x="[[Z-{Tock}]\<^sub>R]" in exI, simp, safe)
    using Some_tt2F_concat_refusal apply force
     apply (metis evt.exhaust ttevent.distinct(1) ttevent.distinct(5) ttevt2F.simps(1) ttevt2F.simps(2))
    using Some_tt2F_concat_refusal by force
next
  fix a b y p q2
  assume assm1:"\<nexists>s t. a = s @ t \<and> (\<exists>y. s = tt2T y \<and> y \<in> P) \<and> (\<exists>y. Some (t, b) = tt2F y \<and> y \<in> Q) \<and> t \<noteq> [] \<and> tick \<notin> set s"
  and    assm2:"Some (a, b) = tt2F (p @ q2)"
  and    assm3:"p \<in> P"
  and    assm4:"\<forall>p'. p \<noteq> p' @ [[Tick]\<^sub>E]"
  and    assm5:"\<forall>p' Y. p \<noteq> p' @ [[Y]\<^sub>R]"
  and    assm6:"filter_tocks p @ q2 \<in> Q"
  and    assm7:"\<forall>q' Y. q2 \<noteq> [Y]\<^sub>R # q'"
  then have assm8:"\<forall>s t. a = s @ t \<longrightarrow> (\<forall>y. s = tt2T y \<longrightarrow> y \<notin> P) \<or> (\<forall>y. Some (t, b) = tt2F y \<longrightarrow> y \<notin> Q) \<or> t = [] \<or> tick \<in> set s"
    by auto
  then obtain xs R where xs_X:"(p @ q2) = xs@[[R]\<^sub>R] \<and> tt2T xs = a \<and> b = {x. ttevt2F x \<in> R} \<and> [Tock]\<^sub>E \<notin> set xs \<and> ttWF(xs@[[R]\<^sub>R])"
    using assm2 Some_tt2F_concat_refusal by metis
  then have no_Tick_Tock:
              "[Tock]\<^sub>E \<notin> set p" 
              "[Tick]\<^sub>E \<notin> set p"
     apply (metis UnCI no_Tock_end_Ref_no_Tock_before set_append)
    using TTWF_P TTwf_def Tick_set_ends_in_Tick assm3 assm4 by auto
  then have "filter_tocks p = []"
    using Tock_not_in_set_empty_filter_tocks by blast
  then have q2_in_Q:"q2 \<in> Q"
    using assm6 by auto

  then have no_Tick:"tick \<notin> set (tt2T p)"
    using Tick_set_tt2T_in no_Tick_Tock by blast
  then have a_p_q2:"a = (tt2T p) @ (tt2T q2)"
    using no_Tick_Tock by (metis Some_tt2F_imp_tt2T' Some_tt2F_no_prev_refusals TTWF_P TTwf_def assm2 assm3 assm4 assm5 nontick_event_end_append_wf tt2T_concat_dist ttWF.simps(2) ttWF_tt2F_last_refusal_concat)
  then have "(tt2T p) \<noteq> []"
            "(tt2T q2) \<noteq> []"
     apply (metis TTWF_P TTwf_def Tick_set_tt2T_in Tock_not_in_set_empty_filter_tocks \<open>[Tick]\<^sub>E \<notin> set p\<close> \<open>[Tock]\<^sub>E \<notin> set p\<close> append_self_conv2 assm1 assm2 assm3 assm4 assm5 assm6 assm7 nontick_event_end_append_wf tt2F_Some_concat_Nil ttWF.simps(2) ttWF_tt2F_last_refusal_concat xs_X)
  proof -
    obtain tts :: "'a ttobs list \<Rightarrow> 'a ttobs list" and TT :: "'a ttobs list \<Rightarrow> 'a ttevent set" where
      f1: "\<forall>x1. (\<exists>v2 v3. x1 = v2 @ [[v3]\<^sub>R]) = (x1 = tts x1 @ [[TT x1]\<^sub>R])"
      by moura
    obtain ttsa :: "'a ttobs list \<Rightarrow> 'a ttobs list" where
      "\<forall>x1. (\<exists>v2. x1 = v2 @ [[Tick]\<^sub>E]) = (x1 = ttsa x1 @ [[Tick]\<^sub>E])"
      by moura
    then have f2: "\<forall>ts tsa. (\<not> ttWF ts \<or> \<not> ttWF tsa \<or> ts = ttsa ts @ [[Tick]\<^sub>E] \<or> ts = tts ts @ [[TT ts]\<^sub>R]) \<or> ttWF (ts @ tsa)"
      using f1 by (meson nontick_event_end_append_wf)
    have "q2 \<noteq> ttsa q2 @ [[Tick]\<^sub>E]"
      by (metis Some_tt2F_no_Tick UnCI \<open>\<And>thesis. (\<And>xs R. p @ q2 = xs @ [[R]\<^sub>R] \<and> tt2T xs = a \<and> b = {x. ttevt2F x \<in> R} \<and> [Tock]\<^sub>E \<notin> set xs \<and> ttWF (xs @ [[R]\<^sub>R]) \<Longrightarrow> thesis) \<Longrightarrow> thesis\<close> in_set_conv_decomp set_append ttWF_tt2F_last_refusal_concat)
    then show "tt2T q2 \<noteq> []"
      using f2 by (metis Some_tt2F_imp_tt2T' TTWF_Q TTwf_def Tock_not_in_set_empty_filter_tocks UnCI \<open>\<And>thesis. (\<And>xs R. p @ q2 = xs @ [[R]\<^sub>R] \<and> tt2T xs = a \<and> b = {x. ttevt2F x \<in> R} \<and> [Tock]\<^sub>E \<notin> set xs \<and> ttWF (xs @ [[R]\<^sub>R]) \<Longrightarrow> thesis) \<Longrightarrow> thesis\<close> append_Nil2 append_self_conv2 assm5 assm6 assm7 no_Tock_end_Ref_no_Tock_before set_append tt2F_Some_concat_Nil ttWF.simps(2) ttWF_tt2F_last_refusal_concat)
  qed
  then have "(\<forall>y. (tt2T p) = tt2T y \<longrightarrow> y \<notin> P) \<or> (\<forall>y. Some ((tt2T q2), b) = tt2F y \<longrightarrow> y \<notin> Q) "
    using assm8 a_p_q2 no_Tick by auto
  then have "p \<notin> P \<or> q2 \<notin> Q"
  proof -
    have "Some ((tt2T q2), b) = tt2F q2"
      using xs_X assm2 assm4 assm5 assm7 apply (induct q2 rule:rev_induct, simp, safe)
      using \<open>tt2T q2 \<noteq> []\<close> tt2T.simps(3) 
      by (smt Ref_in_concat_lhs TTWF_Q TTwf_def Tock_not_in_set_empty_filter_tocks Un_iff \<open>\<And>thesis. (\<And>xs R. p @ q2 = xs @ [[R]\<^sub>R] \<and> tt2T xs = a \<and> b = {x. ttevt2F x \<in> R} \<and> [Tock]\<^sub>E \<notin> set xs \<and> ttWF (xs @ [[R]\<^sub>R]) \<Longrightarrow> thesis) \<Longrightarrow> thesis\<close> a_p_q2 append_self_conv2 assm6 butlast_append butlast_snoc last_appendR last_snoc no_Tick_Tock(2) same_append_eq self_append_conv set_append tt2T_concat_dist ttWF_tt2F_last_refusal_concat)
    then show ?thesis
      using \<open>tt2T q2 \<noteq> []\<close> a_p_q2 assm8 no_Tick by blast
  qed
  then have "False"
    using assm3 q2_in_Q by auto
   then show "\<exists>y. Some (a, b) = tt2F y \<and> y \<in> P"
     by auto
next
  fix a b y p q2
  assume assm1:"\<nexists>s t. a = s @ t \<and> (\<exists>y. s = tt2T y \<and> y \<in> P) \<and> (\<exists>y. Some (t, b) = tt2F y \<and> y \<in> Q) \<and> t \<noteq> [] \<and> tick \<notin> set s"
  and    assm2:"Some (a, b) = tt2F (p @ q2)"
  and    assm3:"p \<in> P"
  and    assm4:"\<forall>p'. p \<noteq> p' @ [[Tick]\<^sub>E]"
  and    assm5:"\<forall>p' Y. p \<noteq> p' @ [[Y]\<^sub>R]"
  and    assm6:"filter_tocks p @ q2 \<in> Q"
  and    assm7:"\<forall>q' Y. q2 \<noteq> [Y]\<^sub>R # q'"
  then have assm8:"\<forall>s t. a = s @ t \<longrightarrow> (\<forall>y. s = tt2T y \<longrightarrow> y \<notin> P) \<or> (\<forall>y. Some (t, b) = tt2F y \<longrightarrow> y \<notin> Q) \<or> t = [] \<or> tick \<in> set s"
    by auto
  then obtain xs R where xs_X:"(p @ q2) = xs@[[R]\<^sub>R] \<and> tt2T xs = a \<and> b = {x. ttevt2F x \<in> R} \<and> [Tock]\<^sub>E \<notin> set xs \<and> ttWF(xs@[[R]\<^sub>R])"
    using assm2 Some_tt2F_concat_refusal by metis
  then have no_Tick_Tock:
              "[Tock]\<^sub>E \<notin> set p" 
              "[Tick]\<^sub>E \<notin> set p"
     apply (metis UnCI no_Tock_end_Ref_no_Tock_before set_append)
    using TTWF_P TTwf_def Tick_set_ends_in_Tick assm3 assm4 by auto
  then have "filter_tocks p = []"
    using Tock_not_in_set_empty_filter_tocks by blast
  then have q2_in_Q:"q2 \<in> Q"
    using assm6 by auto

  then have no_Tick:"tick \<notin> set (tt2T p)"
    using Tick_set_tt2T_in no_Tick_Tock by blast
  then have a_p_q2:"a = (tt2T p) @ (tt2T q2)"
    using no_Tick_Tock by (metis Some_tt2F_imp_tt2T' Some_tt2F_no_prev_refusals TTWF_P TTwf_def assm2 assm3 assm4 assm5 nontick_event_end_append_wf tt2T_concat_dist ttWF.simps(2) ttWF_tt2F_last_refusal_concat)
  then have "(tt2T p) \<noteq> []"
            "(tt2T q2) \<noteq> []"
     apply (metis TTWF_P TTwf_def Tick_set_tt2T_in Tock_not_in_set_empty_filter_tocks \<open>[Tick]\<^sub>E \<notin> set p\<close> \<open>[Tock]\<^sub>E \<notin> set p\<close> append_self_conv2 assm1 assm2 assm3 assm4 assm5 assm6 assm7 nontick_event_end_append_wf tt2F_Some_concat_Nil ttWF.simps(2) ttWF_tt2F_last_refusal_concat xs_X)
  proof -
    obtain tts :: "'a ttobs list \<Rightarrow> 'a ttobs list" and TT :: "'a ttobs list \<Rightarrow> 'a ttevent set" where
      f1: "\<forall>x1. (\<exists>v2 v3. x1 = v2 @ [[v3]\<^sub>R]) = (x1 = tts x1 @ [[TT x1]\<^sub>R])"
      by moura
    obtain ttsa :: "'a ttobs list \<Rightarrow> 'a ttobs list" where
      "\<forall>x1. (\<exists>v2. x1 = v2 @ [[Tick]\<^sub>E]) = (x1 = ttsa x1 @ [[Tick]\<^sub>E])"
      by moura
    then have f2: "\<forall>ts tsa. (\<not> ttWF ts \<or> \<not> ttWF tsa \<or> ts = ttsa ts @ [[Tick]\<^sub>E] \<or> ts = tts ts @ [[TT ts]\<^sub>R]) \<or> ttWF (ts @ tsa)"
      using f1 by (meson nontick_event_end_append_wf)
    have "q2 \<noteq> ttsa q2 @ [[Tick]\<^sub>E]"
      by (metis Some_tt2F_no_Tick UnCI \<open>\<And>thesis. (\<And>xs R. p @ q2 = xs @ [[R]\<^sub>R] \<and> tt2T xs = a \<and> b = {x. ttevt2F x \<in> R} \<and> [Tock]\<^sub>E \<notin> set xs \<and> ttWF (xs @ [[R]\<^sub>R]) \<Longrightarrow> thesis) \<Longrightarrow> thesis\<close> in_set_conv_decomp set_append ttWF_tt2F_last_refusal_concat)
    then show "tt2T q2 \<noteq> []"
      using f2 by (metis Some_tt2F_imp_tt2T' TTWF_Q TTwf_def Tock_not_in_set_empty_filter_tocks UnCI \<open>\<And>thesis. (\<And>xs R. p @ q2 = xs @ [[R]\<^sub>R] \<and> tt2T xs = a \<and> b = {x. ttevt2F x \<in> R} \<and> [Tock]\<^sub>E \<notin> set xs \<and> ttWF (xs @ [[R]\<^sub>R]) \<Longrightarrow> thesis) \<Longrightarrow> thesis\<close> append_Nil2 append_self_conv2 assm5 assm6 assm7 no_Tock_end_Ref_no_Tock_before set_append tt2F_Some_concat_Nil ttWF.simps(2) ttWF_tt2F_last_refusal_concat)
  qed
  then have "(\<forall>y. (tt2T p) = tt2T y \<longrightarrow> y \<notin> P) \<or> (\<forall>y. Some ((tt2T q2), b) = tt2F y \<longrightarrow> y \<notin> Q) "
    using assm8 a_p_q2 no_Tick by auto
  then have "p \<notin> P \<or> q2 \<notin> Q"
  proof -
    have "Some ((tt2T q2), b) = tt2F q2"
      using xs_X assm2 assm4 assm5 assm7 apply (induct q2 rule:rev_induct, simp, safe)
      using \<open>tt2T q2 \<noteq> []\<close> tt2T.simps(3) 
      by (smt Ref_in_concat_lhs TTWF_Q TTwf_def Tock_not_in_set_empty_filter_tocks Un_iff \<open>\<And>thesis. (\<And>xs R. p @ q2 = xs @ [[R]\<^sub>R] \<and> tt2T xs = a \<and> b = {x. ttevt2F x \<in> R} \<and> [Tock]\<^sub>E \<notin> set xs \<and> ttWF (xs @ [[R]\<^sub>R]) \<Longrightarrow> thesis) \<Longrightarrow> thesis\<close> a_p_q2 append_self_conv2 assm6 butlast_append butlast_snoc last_appendR last_snoc no_Tick_Tock(2) same_append_eq self_append_conv set_append tt2T_concat_dist ttWF_tt2F_last_refusal_concat)
    then show ?thesis
      using \<open>tt2T q2 \<noteq> []\<close> a_p_q2 assm8 no_Tick by blast
  qed
  then have "False"
    using assm3 q2_in_Q by auto
   then show "\<exists>y. Some ([], b) = tt2F y \<and> y \<in> Q"
     by auto
  qed


lemma ttproc2F_TimeSyncInterruptTT_traces_subseteq_InterruptF:
  assumes TTWF_P: "TTwf P" and TT0_P: "TT0 P" and TT1_P: "TT1 P"
      and TTWF_Q: "TTwf Q" and TT0_Q: "TT0 Q" and TT1_Q: "TT1 Q"
  shows "snd (ttproc2F (P \<triangle>\<^sub>T Q)) \<subseteq> snd ((ttproc2F P) \<triangle>\<^sub>F (ttproc2F Q))" 
  using assms unfolding ttproc2F_def TimeSyncInterruptTT_def InterruptF_def 
proof (simp_all, safe, blast)
  fix x y p X Y Z
  assume assm1:"\<nexists>s t. tt2T (p @ [[Z]\<^sub>R]) = s @ t \<and> tick \<notin> set s \<and> (\<exists>y. s = tt2T y \<and> y \<in> P) \<and> (\<exists>y. t = tt2T y \<and> y \<in> Q)"
  and    assm2:"p @ [[X]\<^sub>R] \<in> P"
  and    assm3:"filter_tocks p @ [[Y]\<^sub>R] \<in> Q"
  and    assm4:"Z \<subseteq> X \<union> Y"
  and    assm5:"{e \<in> X. e \<noteq> Tock} = {e \<in> Y. e \<noteq> Tock}"
  then show "\<exists>y. tt2T (p @ [[Z]\<^sub>R]) = tt2T y \<and> y \<in> P"
    by (metis TTWF_P TTwf_concat_prefix_of_ref_set_no_Tick tt2T_Tick_concat_lhs)
next
  fix x y p q2
  assume assm1:"\<nexists>s t. tt2T (p @ q2) = s @ t \<and> tick \<notin> set s \<and> (\<exists>y. s = tt2T y \<and> y \<in> P) \<and> (\<exists>y. t = tt2T y \<and> y \<in> Q)"
  and    assm2:"p \<in> P"
  and    assm3:"\<forall>p'. p \<noteq> p' @ [[Tick]\<^sub>E]"
  and    assm4:"\<forall>p' Y. p \<noteq> p' @ [[Y]\<^sub>R]"
  and    assm5:"filter_tocks p @ q2 \<in> Q"
  and    assm6:"\<forall>q' Y. q2 \<noteq> [Y]\<^sub>R # q'"
  then show "\<exists>y. tt2T (p @ q2) = tt2T y \<and> y \<in> P"
    by (metis Ref_in_concat_lhs TTWF_P TTwf_def Tick_set_ends_in_Tick Tick_set_tt2T_in Tock_in_concat_lhs Tock_not_in_set_empty_filter_tocks append_self_conv2 tt2T_concat_dist)
qed

lemma Refusal_in_lhs_concat_tt2T:
  assumes "[R]\<^sub>R \<in> set xs"
  shows "tt2T (xs @ [[Event ev]\<^sub>E]) = tt2T xs"
  using assms by (induct xs rule:tt2T.induct, auto)

lemma last_event_prefix_in_set:
  assumes "p @ [[e]\<^sub>E] \<lesssim>\<^sub>C xs"
  shows "[e]\<^sub>E \<in> set xs"
  using assms apply (induct p xs rule:tt_prefix_subset.induct, auto)
  using tt_prefix_subset.elims(2) by fastforce

lemma last_Ref_prefix_in_set:
  assumes "p @ [[R]\<^sub>R] \<lesssim>\<^sub>C xs"
  shows "\<exists>R. [R]\<^sub>R \<in> set xs"
  using assms apply (induct p xs rule:tt_prefix_subset.induct, auto)
  by (metis list.exhaust list.set_intros(1) tt_prefix_subset.simps(1) tt_prefix_subset.simps(5) tt_prefix_subset_antisym ttobs.exhaust)

lemma ttproc2F_InterruptF_traces_subseteq_TimeSyncInterruptTT:
  assumes ttWF_P: "TTwf P" and TT0_P: "TT0 P" and TT1_P: "TT1 P"
      and ttWF_Q: "TTwf Q" and TT0_Q: "TT0 Q" and TT1_Q: "TT1 Q"
  shows "snd ((ttproc2F P) \<triangle>\<^sub>F (ttproc2F Q)) \<subseteq> snd (ttproc2F (P \<triangle>\<^sub>T Q))" 
  using assms unfolding ttproc2F_def TimeSyncInterruptTT_def InterruptF_def 
proof (auto)
  fix y
  assume y_in_P:"y \<in> P"

  text \<open> Here the issue is splitting cases on y:

         When y ends on tick; ends with a Refusal; is events only;
         For each of these get the actual trace before such an element,
         and then prove. \<close>

  have ttWF_y:"ttWF y"
    using TTwf_def \<open>y \<in> P\<close> ttWF_P by blast

  have "\<exists>ya. tt2T y = tt2T ya \<and>
            ((\<exists>p. p @ [[Tick]\<^sub>E] \<lesssim>\<^sub>C y \<and> filter_tocks p \<in> Q \<and> ya = p @ [[Tick]\<^sub>E]) \<or>
             (\<exists>p X. p @ [[X]\<^sub>R] \<lesssim>\<^sub>C y \<and>
                    (\<exists>Y. filter_tocks p @ [[Y]\<^sub>R] \<in> Q \<and>
                         (\<exists>Z\<subseteq>X \<union> Y. {e \<in> X. e \<noteq> Tock} = {e \<in> Y. e \<noteq> Tock} \<and> ya = p @ [[Z]\<^sub>R]))) \<or>
             (\<exists>p. p \<lesssim>\<^sub>C y \<and>
                  (\<forall>p'. p \<noteq> p' @ [[Tick]\<^sub>E]) \<and>
                  (\<forall>p' Y. p \<noteq> p' @ [[Y]\<^sub>R]) \<and> (\<exists>q2. filter_tocks p @ q2 \<in> Q \<and> (\<forall>q' Y. q2 \<noteq> [Y]\<^sub>R # q') \<and> ya = p @ q2)))"
    using ttWF_y
  proof (cases "\<exists>R. [R]\<^sub>R \<in> set y")
    case True (* Can obtain the first refusal somewhere in the trace *)
    then obtain ys Y where ys_Y:"tt2T y = tt2T (ys@[[Y]\<^sub>R]) \<and> \<not>(\<exists>R. [R]\<^sub>R \<in> set ys) \<and> [Tick]\<^sub>E \<notin> set ys \<and> ttWF (ys@[[Y]\<^sub>R]) \<and> [Tock]\<^sub>E \<notin> set ys \<and> ys@[[Y]\<^sub>R] \<lesssim>\<^sub>C y"
      by (smt Tick_set_ends_in_Tick Tick_set_tt2T_in Tock_in_trace_Refusal_no_Tick UnE empty_set exists_Refusal_tt2T_concat_Ref_end list.simps(15) set_append singletonD ttWF_y ttobs.distinct(1))
    then have "\<exists>ya. tt2T y = tt2T ya \<and> (\<exists>p. p \<lesssim>\<^sub>C y \<and>
                  (\<forall>p'. p \<noteq> p' @ [[Tick]\<^sub>E]) \<and>
                  (\<forall>p' Y. p \<noteq> p' @ [[Y]\<^sub>R]) \<and> (\<exists>q2. filter_tocks p @ q2 \<in> Q \<and> (\<forall>q' Y. q2 \<noteq> [Y]\<^sub>R # q') \<and> ya = p @ q2))"  
      apply auto
      by (metis TT0_Q TT0_TT1_empty TT1_Q Tock_not_in_set_empty_filter_tocks append_Nil2 in_set_conv_decomp tt2T_Tick_concat_lhs tt_prefix_subset_front)
    then show ?thesis
      by blast
  next
    case no_Ref:False
    then show ?thesis
    proof (cases "[Tick]\<^sub>E \<in> set y")
      case True
      then show ?thesis
        by (metis (no_types, hide_lams) no_Ref TT0_Q TT0_TT1_empty TT1_Q Tick_set_ends_in_Tick Tock_not_in_set_empty_filter_tocks filter_tocks_end_tick ttWF_no_Ref_no_Tock ttWF_y tt_prefix_subset_refl)
    next
      case False
      then have "\<exists>ya. (\<exists>p. p \<lesssim>\<^sub>C y \<and>
                  (\<forall>p'. p \<noteq> p' @ [[Tick]\<^sub>E]) \<and>
                  (\<forall>p' Y. p \<noteq> p' @ [[Y]\<^sub>R]) \<and> (\<exists>q2. filter_tocks p @ q2 \<in> Q \<and> (\<forall>q' Y. q2 \<noteq> [Y]\<^sub>R # q') \<and> ya = p @ q2))"
        apply (rule_tac x="y" in exI, auto)
        apply (rule_tac x="y" in exI, auto)
        using tt_prefix_subset_refl apply blast
        using no_Ref apply auto
        by (simp add: TT0_Q TT0_TT1_empty TT1_Q Tock_not_in_set_empty_filter_tocks ttWF_no_Ref_no_Tock ttWF_y)
      then show ?thesis
        by (metis (no_types, hide_lams) False TT0_Q TT0_TT1_empty TT1_Q Tock_not_in_set_empty_filter_tocks append_Nil2 in_set_conv_decomp no_Ref ttWF_no_Ref_no_Tock ttWF_y tt_prefix_subset_refl)
    qed
  qed

  then show "\<exists>ya. tt2T y = tt2T ya \<and>
              ((\<exists>p. p @ [[Tick]\<^sub>E] \<in> P \<and> filter_tocks p \<in> Q \<and> ya = p @ [[Tick]\<^sub>E]) \<or>
               (\<exists>p X. p @ [[X]\<^sub>R] \<in> P \<and>
                      (\<exists>Y. filter_tocks p @ [[Y]\<^sub>R] \<in> Q \<and>
                           (\<exists>Z\<subseteq>X \<union> Y. {e \<in> X. e \<noteq> Tock} = {e \<in> Y. e \<noteq> Tock} \<and> ya = p @ [[Z]\<^sub>R]))) \<or>
               (\<exists>p. p \<in> P \<and>
                    (\<forall>p'. p \<noteq> p' @ [[Tick]\<^sub>E]) \<and>
                    (\<forall>p' Y. p \<noteq> p' @ [[Y]\<^sub>R]) \<and> (\<exists>q2. filter_tocks p @ q2 \<in> Q \<and> (\<forall>q' Y. q2 \<noteq> [Y]\<^sub>R # q') \<and> ya = p @ q2)))"
    using TT1_P y_in_P apply safe
    apply (simp_all)
    using TT1_def by smt+
next
  fix y ya
  assume assm1:"y \<in> P"
  and    assm2:"ya \<in> Q"
  and    assm3:"tick \<notin> set (tt2T y)"

  have ttWF_y:"ttWF y"
    using TTwf_def \<open>y \<in> P\<close> ttWF_P by blast

  have "\<exists>yb. tt2T y @ tt2T ya = tt2T yb \<and>
            ((\<exists>p. p @ [[Tick]\<^sub>E] \<lesssim>\<^sub>C y \<and> filter_tocks p \<in> Q \<and> yb = p @ [[Tick]\<^sub>E]) \<or>
             (\<exists>p X. p @ [[X]\<^sub>R] \<lesssim>\<^sub>C y \<and>
                    (\<exists>Y. filter_tocks p @ [[Y]\<^sub>R] \<in> Q \<and>
                         (\<exists>Z\<subseteq>X \<union> Y. {e \<in> X. e \<noteq> Tock} = {e \<in> Y. e \<noteq> Tock} \<and> yb = p @ [[Z]\<^sub>R]))) \<or>
             (\<exists>p. p \<lesssim>\<^sub>C y \<and>
                  (\<forall>p'. p \<noteq> p' @ [[Tick]\<^sub>E]) \<and>
                  (\<forall>p' Y. p \<noteq> p' @ [[Y]\<^sub>R]) \<and> (\<exists>q2. filter_tocks p @ q2 \<in> Q \<and> (\<forall>q' Y. q2 \<noteq> [Y]\<^sub>R # q') \<and> yb = p @ q2)))"
  proof (cases "\<exists>R. [R]\<^sub>R \<in> set y")
    case True (* Can obtain the first refusal somewhere in the trace *)
    then obtain ys Y where ys_Y:"tt2T y = tt2T (ys@[[Y]\<^sub>R]) \<and> \<not>(\<exists>R. [R]\<^sub>R \<in> set ys) \<and> [Tick]\<^sub>E \<notin> set ys \<and> ttWF (ys@[[Y]\<^sub>R]) \<and> [Tock]\<^sub>E \<notin> set ys \<and> ys@[[Y]\<^sub>R] \<lesssim>\<^sub>C y"
      using exists_Refusal_tt2T_concat_Ref_end
      using assm3 ttWF_y by blast
    then have "tt2T y = tt2T ys"
              "tt2T (ys) @ tt2T ya = tt2T (ys @ ya)"
       apply (simp add: tt2T_Tick_concat_lhs)
       using ys_Y by (simp add: tt2T_concat_dist)
    then have "\<exists>yb. tt2T y @ tt2T ya = tt2T yb \<and> (\<exists>p. p \<lesssim>\<^sub>C y \<and>
               (\<forall>p'. p \<noteq> p' @ [[Tick]\<^sub>E]) \<and>
               (\<forall>p' Y. p \<noteq> p' @ [[Y]\<^sub>R]) \<and> (\<exists>q2. filter_tocks p @ q2 \<in> Q \<and> (\<forall>q' Y. q2 \<noteq> [Y]\<^sub>R # q') \<and> yb = p @ q2))"
      by (metis (no_types, hide_lams) TT0_Q TT0_TT1_empty TT1_Q Tock_not_in_set_empty_filter_tocks append_Nil append_Nil2 assm2 in_set_conv_decomp tt2T.simps(5) tt_prefix_subset_front ys_Y)
    then show ?thesis
      by blast
  next
    case no_Ref:False
    then show ?thesis
    proof (cases "[Tick]\<^sub>E \<in> set y")
      case True
      then show ?thesis using assm3 
        by (smt TTwf_concat_prefix_set_no_Tick TTwf_def Tick_set_ends_in_Tick Un_iff assm1 in_set_conv_decomp no_Ref set_append tt2T.simps(1) tt2T_concat_dist ttWF_P ttWF_no_Ref_no_Tock)
    next
      case False
      then have "\<exists>yb. tt2T y @ tt2T ya = tt2T yb \<and> (\<exists>p. p \<lesssim>\<^sub>C y \<and>
                  (\<forall>p'. p \<noteq> p' @ [[Tick]\<^sub>E]) \<and>
                  (\<forall>p' Y. p \<noteq> p' @ [[Y]\<^sub>R]) \<and> (\<exists>q2. filter_tocks p @ q2 \<in> Q \<and> (\<forall>q' Y. q2 \<noteq> [Y]\<^sub>R # q') \<and> yb = p @ q2))"
        by (metis TT0_Q TT0_TT1_empty TT1_Q Tock_not_in_set_empty_filter_tocks append.left_neutral assm2 last_in_set list.distinct(1) no_Ref snoc_eq_iff_butlast tt2T.simps(3) tt2T.simps(5) tt2T_concat_dist ttWF_no_Ref_no_Tock ttWF_y tt_prefix_subset_refl)
      then show ?thesis
        by blast
    qed
  qed
  
  then show "\<exists>yb. tt2T y @ tt2T ya = tt2T yb \<and>
            ((\<exists>p. p @ [[Tick]\<^sub>E] \<in> P \<and> filter_tocks p \<in> Q \<and> yb = p @ [[Tick]\<^sub>E]) \<or>
             (\<exists>p X. p @ [[X]\<^sub>R] \<in> P \<and>
                    (\<exists>Y. filter_tocks p @ [[Y]\<^sub>R] \<in> Q \<and>
                         (\<exists>Z\<subseteq>X \<union> Y. {e \<in> X. e \<noteq> Tock} = {e \<in> Y. e \<noteq> Tock} \<and> yb = p @ [[Z]\<^sub>R]))) \<or>
             (\<exists>p. p \<in> P \<and>
                  (\<forall>p'. p \<noteq> p' @ [[Tick]\<^sub>E]) \<and>
                  (\<forall>p' Y. p \<noteq> p' @ [[Y]\<^sub>R]) \<and> (\<exists>q2. filter_tocks p @ q2 \<in> Q \<and> (\<forall>q' Y. q2 \<noteq> [Y]\<^sub>R # q') \<and> yb = p @ q2)))"
    using TT1_P assm1 apply safe
    apply (simp_all)
    using TT1_def by smt+
qed

lemma ttproc2F_InterruptF_eq_TimeSyncInterruptTT:
  assumes ttWF_P: "TTwf P" and TT0_P: "TT0 P" and TT1_P: "TT1 P"
      and ttWF_Q: "TTwf Q" and TT0_Q: "TT0 Q" and TT1_Q: "TT1 Q"
  shows "((ttproc2F P) \<triangle>\<^sub>F (ttproc2F Q)) = (ttproc2F (P \<triangle>\<^sub>T Q))" 
  using assms 
  by (metis dual_order.antisym prod.collapse ttproc2F_InterruptF_failures_subseteq_TimeSyncInterruptTT ttproc2F_InterruptF_traces_subseteq_TimeSyncInterruptTT ttproc2F_TimeSyncInterruptTT_failures_subseteq_InterruptF ttproc2F_TimeSyncInterruptTT_traces_subseteq_InterruptF)

end
