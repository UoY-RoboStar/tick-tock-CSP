theory Failures_TickTock_SeqComp

imports
  Failures_TickTock
begin

lemma ttproc2F_SeqCompTT_failures_subseteq_SeqCompF:
  assumes TTwf_P: "TTwf P" and TT0_P: "TT0 P" and TT1_P: "TT1 P"
      and TTwf_Q: "TTwf Q" and TT0_Q: "TT0 Q" and TT1_Q: "TT1 Q"
  shows "fst (ttproc2F (P ;\<^sub>C Q)) \<subseteq>  fst ((ttproc2F P) ;\<^sub>F (ttproc2F Q))" 
  using assms unfolding ttproc2F_def SeqCompTT_def SeqCompF_def
proof (auto)
  fix a b s t
  assume assm1:"\<forall>s t. a = s @ t \<longrightarrow> (\<forall>y. s @ [tick] = tt2T y \<longrightarrow> y \<notin> P) \<or> (\<forall>y. Some (t, b) = tt2F y \<longrightarrow> y \<notin> Q)"
    and  assm2:"Some (a, b) = tt2F (s @ t)" 
    and  assm3:"s @ [[Tick]\<^sub>E] \<in> P" 
    and  assm4:"t \<in> Q"

  have "a = tt2T (s@t)"
    using Some_tt2F_imp_tt2T' assm2 by blast

  have "\<exists>y. tt2F (s @ t) = tt2F y \<and> y \<lesssim>\<^sub>C s"
    using assm1 assm2 assm3 assm4
  proof (induct t arbitrary:s a b rule:rev_induct)
    case Nil
    then show ?case
      apply (rule_tac x="s" in exI, auto)
      using tt_prefix_subset_refl by blast
  next
    case (snoc x t)
    then show ?case
      proof (cases x)
        case (ObsEvent x1)
        then have "tt2F (s @ t @ [x]) = None"
          using snoc
          by (metis Some_tt2F_concat_refusal append_is_Nil_conv last_appendR last_snoc ttobs.distinct(1))
        then show ?thesis using snoc by auto
      next
        case (Ref x2)
        then have "[Tick]\<^sub>E \<notin> set s" "[Tock]\<^sub>E \<notin> set s" "\<not>(\<exists>R. [R]\<^sub>R \<in> set s)"
          using TTwf_P TTwf_concat_prefix_set_no_Tick snoc.prems(3) apply blast
          using Some_tt2F_no_Tock snoc.prems(2) apply fastforce
          using snoc Some_tt2F_no_prev_refusals Ref 
          by (metis (no_types) Some_tt2F_no_prev_refusals UnCI append.assoc set_append)
        then have "a = (tt2T s) @ (tt2T t)"
          by (smt Some_tt2F_concat_refusal append.assoc append_same_eq last_snoc snoc.prems(2) tt2T_concat_dist)

        then have pp:"(\<forall>y. (tt2T s) @ [tick] = tt2T y \<longrightarrow> y \<notin> P) \<or> (\<forall>y. Some ((tt2T t), b) = tt2F y \<longrightarrow> y \<notin> Q)"
          using snoc by blast

        have "(tt2T s) @ [tick] = tt2T (s@[[Tick]\<^sub>E])"
          by (simp add: \<open>[Tick]\<^sub>E \<notin> set s\<close> \<open>[Tock]\<^sub>E \<notin> set s\<close> \<open>\<nexists>R. [R]\<^sub>R \<in> set s\<close> tt2T_concat_dist)

        then have "s @ [[Tick]\<^sub>E] \<notin> P \<or> t @ [x] \<notin> Q"
          using pp
          by (smt Nil_is_append_conv Some_tt2F_concat_refusal Some_tt2F_no_Tock TTwf_Q TTwf_def UnCI last_appendR last_snoc set_append snoc.prems(2) snoc.prems(4) ttWF_tt2F_last_refusal_concat)
          
        then show ?thesis using snoc by auto
      qed
  qed
  then show "\<exists>y. tt2F (s @ t) = tt2F y \<and> y \<in> P"
    by (meson TT1_P TT1_def assm3 tt_prefix_concat tt_prefix_imp_prefix_subset)
qed

lemma ttproc2F_SeqCompF_failures_subseteq_SeqCompTT:
  assumes TTwf_P: "TTwf P" and TT0_P: "TT0 P" and TT1_P: "TT1 P"
      and TTwf_Q: "TTwf Q" and TT0_Q: "TT0 Q" and TT1_Q: "TT1 Q"
  shows "fst ((ttproc2F P) ;\<^sub>F (ttproc2F Q)) \<subseteq> fst (ttproc2F (P ;\<^sub>C Q))" 
  using assms unfolding ttproc2F_def SeqCompTT_def SeqCompF_def
proof (auto)
  fix a b y
  assume assm2:"Some (a, b) = tt2F y"
   and   assm3:"y \<in> P"
  show "\<exists>ya. tt2F y = tt2F ya \<and> (ya \<in> P \<and> (\<forall>s. ya \<noteq> s @ [[Tick]\<^sub>E]) \<or> (\<exists>s. s @ [[Tick]\<^sub>E] \<in> P \<and> (\<exists>t. t \<in> Q \<and> ya = s @ t)))"
    using assm2 assm3 Some_tt2F_no_Tick by fastforce
next
  fix b s t y ya
  assume assm1:"s @ [tick] = tt2T y"
  and    assm2:"y \<in> P"
  and    assm3:"Some (t, b) = tt2F ya"
  and    assm4:"ya \<in> Q"

  obtain z where z:"y = z@[[Tick]\<^sub>E]"
    using assm1 assm2 tt2T_tick_exists_Cons by blast
  
  show "\<exists>y. Some (s @ t, b) = tt2F y \<and> 
            (y \<in> P \<and> (\<forall>s. y \<noteq> s @ [[Tick]\<^sub>E]) \<or> (\<exists>s. s @ [[Tick]\<^sub>E] \<in> P \<and> (\<exists>t. t \<in> Q \<and> y = s @ t)))"
    using assm1 assm2 assm3 assm4
    apply (rule_tac x="z@ya" in exI, auto simp add:z)
    using Some_concat_extend Some_tt2F_imp_tt2T' Some_concat_extend' tt2T_tick_butlast by fastforce
qed

lemma ttproc2F_SeqCompTT_traces_subseteq_SeqCompF:
  assumes TTwf_P: "TTwf P" and TT0_P: "TT0 P" and TT1_P: "TT1 P" 
      and TTwf_Q: "TTwf Q" and TT0_Q: "TT0 Q" and TT1_Q: "TT1 Q"
  shows "snd (ttproc2F (P ;\<^sub>C Q)) \<subseteq> snd ((ttproc2F P) ;\<^sub>F (ttproc2F Q))" 
  using assms unfolding ttproc2F_def SeqCompTT_def SeqCompF_def
proof (auto)
  fix y
  assume assm1:"\<forall>s t. tt2T y = s @ t \<longrightarrow> (\<forall>y. s @ [tick] = tt2T y \<longrightarrow> y \<notin> P) \<or> (\<forall>y. t = tt2T y \<longrightarrow> y \<notin> Q)"
    and  assm2:"y \<in> P"
    and  assm3:"\<forall>s. y \<noteq> s @ [[Tick]\<^sub>E]"
    and  assm4:"tick \<in> set (tt2T y)"
  have ttWF_y:"ttWF y"
    using TTwf_P TTwf_def assm2 by blast
  have Tick_set:"[Tick]\<^sub>E \<in> set y"
    using assm4 Tick_set_tt2T_in by blast

  show "False"
    using assm1 assm2 assm3 assm4
  proof (cases "y = []")
    case True
    then show ?thesis using assm1 assm2 assm3 assm4 by auto
  next
    case False
    then obtain xs where xs:"y = xs@[[Tick]\<^sub>E]"
      using False ttWF_y Tick_set Tick_set_ends_in_Tick by blast
    then show ?thesis using assm3 by auto
  qed
next
  fix s t
  assume assm1:"\<forall>sa ta. tt2T (s @ t) = sa @ ta \<longrightarrow> (\<forall>y. sa @ [tick] = tt2T y \<longrightarrow> y \<notin> P) \<or> (\<forall>y. ta = tt2T y \<longrightarrow> y \<notin> Q)"
    and  assm2:"s @ [[Tick]\<^sub>E] \<in> P"
    and  assm3:"t \<in> Q"
    and  assm4:"tick \<in> set (tt2T (s @ t))"
  have "[Tick]\<^sub>E \<notin> set s"
    using TTwf_P TTwf_concat_prefix_set_no_Tick assm2 by blast
  then show "False"
    using assm1 assm2 assm3 Tock_in_trace_Tick_no_Tick Tock_in_trace_Refusal_no_Tick
    by (metis TTwf_P TTwf_def assm4 tt2T.simps(1) tt2T_concat_dist)
next
  fix s t
  assume assm1:"\<forall>sa ta. tt2T (s @ t) = sa @ ta \<longrightarrow> (\<forall>y. sa @ [tick] = tt2T y \<longrightarrow> y \<notin> P) \<or> (\<forall>y. ta = tt2T y \<longrightarrow> y \<notin> Q)"
    and  assm2:"s @ [[Tick]\<^sub>E] \<in> P"
    and  assm3:"t \<in> Q"
  have "[Tick]\<^sub>E \<notin> set s"
    using TTwf_P TTwf_concat_prefix_set_no_Tick assm2 by blast

  text \<open> It's basically by case analysis on whether Tock or Refs exist in s. \<close>

  show "\<exists>y. tt2T (s @ t) = tt2T y \<and> y \<in> P"
    using assm1 assm2 assm3
    by (metis Ref_in_concat_lhs Tock_in_concat_lhs \<open>[Tick]\<^sub>E \<notin> set s\<close> tt2T.simps(1) tt2T_concat_dist)
qed

lemma
  assumes "tick \<notin> set (tt2T y)" "ttWF y" "[Tock]\<^sub>E \<notin> set y"
  shows "[Tick]\<^sub>E \<notin> set y"
  using assms apply (induct y rule:tt2T.induct, auto)
  apply (smt hd_in_set list.distinct(1) list.inject list.sel(1) list.set_cases ttWF.elims(2) ttobs.distinct(1))
  using ttWF.elims(2) by auto

lemma ttproc2F_SeqCompF_traces_subseteq_SeqCompTT:
  assumes TTwf_P: "TTwf P" and TT0_P: "TT0 P" and TT1_P: "TT1 P" 
      and TTwf_Q: "TTwf Q" and TT0_Q: "TT0 Q" and TT1_Q: "TT1 Q" 
  shows "snd ((ttproc2F P) ;\<^sub>F (ttproc2F Q)) \<subseteq> snd (ttproc2F (P ;\<^sub>C Q))" 
  unfolding ttproc2F_def SeqCompTT_def SeqCompF_def
proof (auto)
  fix y x 
  assume assm1:"tick \<notin> set (tt2T y)"
  and    assm2:"y \<in> P"
  have "\<exists>ya. tt2T y = tt2T ya \<and> (ya \<lesssim>\<^sub>C y \<and> (\<forall>s. ya \<noteq> s @ [[Tick]\<^sub>E]) \<or> ya @ [[Tick]\<^sub>E] \<lesssim>\<^sub>C y)"
    using assm1
    apply (induct y rule:tt2T.induct, auto)
       apply (metis (no_types, hide_lams) Cons_eq_append_conv tt2T.simps(2) tt_prefix_subset.simps(3) ttevent.distinct(3))
      apply (metis (no_types, hide_lams) Cons_eq_append_conv tt2T.simps(2) tt_prefix_subset.simps(3) ttevent.distinct(3))
  by (rule_tac x="[]" in exI, auto)+
  then show "\<exists>ya. tt2T y = tt2T ya \<and> (ya \<in> P \<and> (\<forall>s. ya \<noteq> s @ [[Tick]\<^sub>E]) \<or> (\<exists>s. s @ [[Tick]\<^sub>E] \<in> P \<and> (\<exists>t. t \<in> Q \<and> ya = s @ t)))"
    by (metis TT0_Q TT0_TT1_empty TT1_P TT1_Q TT1_def append.right_neutral assm2)
next
  fix s y ya
  assume assm1:"s @ [tick] = tt2T y"
  and    assm2:"y \<in> P"
  and    assm3:"ya \<in> Q"
  then show "\<exists>y. s @ tt2T ya = tt2T y \<and> (y \<in> P \<and> (\<forall>s. y \<noteq> s @ [[Tick]\<^sub>E]) \<or> (\<exists>s. s @ [[Tick]\<^sub>E] \<in> P \<and> (\<exists>t. t \<in> Q \<and> y = s @ t)))"
    using assm1 assm2 assm3 apply (rule_tac x="butlast y@ya" in exI, auto)
    apply (smt Nil_is_append_conv TTwf_P TTwf_def Tick_set_ends_in_Tick Tick_set_tt2T_in append_butlast_last_id last_in_set last_snoc not_Cons_self2 tt2T_concat_Tick_no_Ref_set tt2T_concat_Tick_no_Tick_set tt2T_concat_Tick_no_Tock_set tt2T_concat_dist tt2T_tick_butlast)
    using tt2T_tick_exists_Cons by force+
qed

lemma ttproc2F_SeqCompTT_eq_SeqCompF:
  assumes TTwf_P: "TTwf P" and TT0_P: "TT0 P" and TT1_P: "TT1 P" 
      and TTwf_Q: "TTwf Q" and TT0_Q: "TT0 Q" and TT1_Q: "TT1 Q"
  shows "(ttproc2F (P ;\<^sub>C Q)) = ((ttproc2F P) ;\<^sub>F (ttproc2F Q))" 
  using assms
  by (simp add: refines_asym refines_def ttproc2F_SeqCompF_failures_subseteq_SeqCompTT ttproc2F_SeqCompF_traces_subseteq_SeqCompTT ttproc2F_SeqCompTT_failures_subseteq_SeqCompF ttproc2F_SeqCompTT_traces_subseteq_SeqCompF)

end