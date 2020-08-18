theory Failures_TickTock_SeqComp

imports
  Failures_TickTock
begin


lemma Some_no_tick_trace[simp]:
  assumes "Some (a, b) = tt2F y" 
  shows "tick \<notin> set a"
  using assms apply (induct a arbitrary:b y, auto)
  using Some_no_tt2F_tick apply blast
  using Some_tt2F_tail by blast

lemma tt2T_concat_dist:
  assumes "[Tick]\<^sub>E \<notin> set s" "[Tock]\<^sub>E \<notin> set s" "\<not>(\<exists>R. [R]\<^sub>R \<in> set s)"
  shows "tt2T (s @ t) = (tt2T s) @ (tt2T t)"
  using assms apply (induct s arbitrary: t, auto)
  apply (case_tac a, auto)
  by (case_tac x1, auto)

lemma Some_tt2F_no_prev_refusals:
  assumes "Some (a, b) = tt2F (s @ [[R]\<^sub>R])"
  shows "\<not>(\<exists>R. [R]\<^sub>R \<in> set s)"
  using assms apply (induct s arbitrary:a b R, auto)
   apply (metis list.exhaust_sel option.distinct(1) snoc_eq_iff_butlast tt2F.simps(8))
  by (metis (no_types, hide_lams) Some_tt2F_tail append_Cons append_Nil list.sel(3) neq_Nil_conv tt2F_some_exists)

lemma ttproc2F_SeqCompTT_failures_subseteq_SeqCompF:
  assumes TTwf_P: "TTwf P" and TT0_P: "TT0 P" and TT1_P: "TT1 P" and TT2_P: "TT2 P" and TT3_P: "TT3 P"
      and TTwf_Q: "TTwf Q" and TT0_Q: "TT0 Q" and TT1_Q: "TT1 Q" and TT2_Q: "TT2 Q" and TT3_Q: "TT3 Q"
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

lemma tt2T_tick_butlast:
  assumes "s @ [tick] = tt2T y"
  shows "tt2T (butlast y) = s"
  using assms apply (induct y arbitrary:s, auto)
   apply (case_tac a, auto)
   apply (case_tac x1, auto)
  apply (case_tac a, auto)
   apply (case_tac x1, auto)
   apply (metis (no_types, lifting) append_eq_Cons_conv evt.distinct(1) list.inject)
  by (metis list.exhaust_sel snoc_eq_iff_butlast tt2T.simps(7))

lemma tt2T_tick_exists_Cons:
  assumes "s @ [tick] = tt2T y"
  shows "\<exists>z. z@[[Tick]\<^sub>E] = y"
  using assms apply (induct y arbitrary:s, auto)
  apply (case_tac a, auto)
  apply (case_tac x1, auto)
   apply (metis Cons_eq_append_conv evt.distinct(1) list.inject)
  by (metis append_Nil list.exhaust_sel snoc_eq_iff_butlast tt2T.simps(7))


lemma
  assumes "s @ [tick] = tt2T (z @ [[Tick]\<^sub>E])"
  shows "s = tt2T z"
  using assms
  using tt2T_tick_butlast by fastforce

lemma tick_tt2T_concat_TickE[intro?]:
  assumes "[tick] = tt2T (za @ [[Tick]\<^sub>E])"
  shows "za = []"
  using assms apply (induct za, auto)
  apply (case_tac a, auto)
  apply (case_tac x1, auto)
  by (metis list.distinct(1) list.exhaust_sel snoc_eq_iff_butlast tt2T.simps(7))

lemma Some_concat_extend:
  assumes "Some (t, b) = tt2F ya" "[Tick]\<^sub>E \<notin> set z" "[Tock]\<^sub>E \<notin> set z" "\<not>(\<exists>R. [R]\<^sub>R \<in> set z)" (* *)
  shows "Some (tt2T z @ t, b) = tt2F (z @ ya)"
  using assms apply (induct z arbitrary:t ya b rule:tt2F.induct , auto)
  by (smt fst_conv option.simps(5) snd_conv)

lemma tt2T_concat_Tick_no_Tick_set:
  assumes "s @ [tick] = tt2T (z @ [[Tick]\<^sub>E])"
  shows "[Tick]\<^sub>E \<notin> set z"
  using assms apply (induct z arbitrary:s, auto)
   apply (metis list.exhaust_sel snoc_eq_iff_butlast tt2T.simps(7))
  apply (case_tac a, auto)
  apply (case_tac x1, auto)
   apply (metis append_Nil evt.distinct(1) list.sel(1) list.sel(3) tl_append2)
  by (metis list.exhaust_sel snoc_eq_iff_butlast tt2T.simps(7))

lemma tt2T_concat_Tick_no_Ref_set:
  assumes "s @ [tick] = tt2T (z @ [[Tick]\<^sub>E])"
  shows "\<not>(\<exists>R. [R]\<^sub>R \<in> set z)"
  using assms apply (induct z arbitrary:s, auto)
  apply (case_tac a, auto)
  apply (case_tac x1, auto)
   apply (metis append_Nil evt.distinct(1) list.sel(1) list.sel(3) tl_append2)
  by (metis list.exhaust_sel snoc_eq_iff_butlast tt2T.simps(7))

lemma tt2T_concat_Tick_no_Tock_set:
  assumes "s @ [tick] = tt2T (z @ [[Tick]\<^sub>E])"
  shows "[Tock]\<^sub>E \<notin> set z"
  using assms apply (induct z arbitrary:s, auto)
  apply (case_tac a, auto)
  apply (case_tac x1, auto)
   apply (metis append_Nil evt.distinct(1) list.sel(1) list.sel(3) tl_append2)
  by (metis list.exhaust_sel snoc_eq_iff_butlast tt2T.simps(7))

lemma Some_concat_extend':
  assumes "Some (t, b) = tt2F ya" "s @ [tick] = tt2T (z @ [[Tick]\<^sub>E])"
  shows "Some (tt2T z @ t, b) = tt2F (z @ ya)"
  using assms Some_concat_extend tt2T_concat_Tick_no_Tick_set tt2T_concat_Tick_no_Ref_set tt2T_concat_Tick_no_Tock_set
  by blast

lemma ttproc2F_SeqCompF_failures_subseteq_SeqCompTT:
  assumes TTwf_P: "TTwf P" and TT0_P: "TT0 P" and TT1_P: "TT1 P" and TT2_P: "TT2 P" and TT3_P: "TT3 P"
      and TTwf_Q: "TTwf Q" and TT0_Q: "TT0 Q" and TT1_Q: "TT1 Q" and TT2_Q: "TT2 Q" and TT3_Q: "TT3 Q"
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

end