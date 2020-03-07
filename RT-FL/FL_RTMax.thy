theory FL_RTMax
  imports RT FL.Finite_Linear FL.Finite_Linear_Tick_Param
begin

section \<open>Mapping from FL to RTMax\<close>

fun acc2maxref :: "'e acceptance \<Rightarrow> 'e rtrefusal" where
  "acc2maxref \<bullet> = \<bullet>\<^sub>\<R>\<^sub>\<T>" |
  "acc2maxref [X]\<^sub>\<F>\<^sub>\<L> = [{e. e \<notin> X}]\<^sub>\<R>\<^sub>\<T>"

fun fl2rtm_trace :: "'e fltrace \<Rightarrow> 'e rttrace" where
  "fl2rtm_trace \<langle>X\<rangle>\<^sub>\<F>\<^sub>\<L> = \<langle>acc2maxref(X)\<rangle>\<^sub>\<R>\<^sub>\<T>" |
  "fl2rtm_trace (A #\<^sub>\<F>\<^sub>\<L> \<rho>) = ((acc2maxref (acceptance A)) #\<^sub>\<R>\<^sub>\<T> (event A) #\<^sub>\<R>\<^sub>\<T> (fl2rtm_trace \<rho>))"

(* need to enforce RT4 here, due to the differences in tick handling between our FL and RT *)
definition fl2rtm :: "'e rtevent fltraces \<Rightarrow> 'e rtevent rtprocess" where
  "fl2rtm P = {\<rho>. \<exists>\<sigma>\<in>P. \<rho> = fl2rtm_trace \<sigma> }
    \<union> {\<rho>. \<exists>\<sigma>\<in>P. \<exists>\<rho>' y. fl2rtm_trace \<sigma> = \<rho>' @\<^sub>\<R>\<^sub>\<T> \<langle>\<bullet>\<^sub>\<R>\<^sub>\<T>\<rangle>\<^sub>\<R>\<^sub>\<T> @\<^sub>\<R>\<^sub>\<T> TickRT ##\<^sub>\<R>\<^sub>\<T> \<langle>y\<rangle>\<^sub>\<R>\<^sub>\<T> \<and> \<rho> = \<rho>' @\<^sub>\<R>\<^sub>\<T> \<langle>\<bullet>\<^sub>\<R>\<^sub>\<T>\<rangle>\<^sub>\<R>\<^sub>\<T> @\<^sub>\<R>\<^sub>\<T> TickRT ##\<^sub>\<R>\<^sub>\<T> \<langle>[UNIV]\<^sub>\<R>\<^sub>\<T>\<rangle>\<^sub>\<R>\<^sub>\<T> }"

lemma fl2rtm_rtWF:
  "\<forall>x\<in>(fl2rtm P). rtWF x"
  unfolding fl2rtm_def
proof (safe, simp_all)
  fix \<sigma> :: "'a rtevent fltrace"
  show "\<And>P. \<sigma> \<in> P \<Longrightarrow> rtWF (fl2rtm_trace \<sigma>)"
    apply (induct \<sigma>, simp_all)
    by (smt acc2maxref.simps(1) acc2maxref.simps(2) amember.elims(2) event_in_acceptance in_rtrefusal.elims(2) in_rtrefusal.simps(1) mem_Collect_eq rtrefusal.inject)
next
  fix \<sigma> :: "'a rtevent fltrace" and \<rho>' y
  show "\<And> P \<rho>'. \<sigma> \<in> P \<Longrightarrow> fl2rtm_trace \<sigma> = \<rho>' @\<^sub>\<R>\<^sub>\<T> \<langle>\<bullet>\<^sub>\<R>\<^sub>\<T>\<rangle>\<^sub>\<R>\<^sub>\<T> @\<^sub>\<R>\<^sub>\<T> TickRT ##\<^sub>\<R>\<^sub>\<T> \<langle>y\<rangle>\<^sub>\<R>\<^sub>\<T>
      \<Longrightarrow> rtWF (\<rho>' @\<^sub>\<R>\<^sub>\<T> \<langle>\<bullet>\<^sub>\<R>\<^sub>\<T>\<rangle>\<^sub>\<R>\<^sub>\<T> @\<^sub>\<R>\<^sub>\<T> TickRT ##\<^sub>\<R>\<^sub>\<T> \<langle>[UNIV]\<^sub>\<R>\<^sub>\<T>\<rangle>\<^sub>\<R>\<^sub>\<T>)"
  proof (induct \<sigma>, auto, case_tac \<rho>', auto)
    fix x1a \<sigma> \<rho>'
    assume ind_hyp: "\<And>P \<rho>'. \<sigma> \<in> P \<Longrightarrow> fl2rtm_trace \<sigma> = \<rho>' @\<^sub>\<R>\<^sub>\<T> \<langle>\<bullet>\<^sub>\<R>\<^sub>\<T>\<rangle>\<^sub>\<R>\<^sub>\<T> @\<^sub>\<R>\<^sub>\<T> TickRT ##\<^sub>\<R>\<^sub>\<T> \<langle>y\<rangle>\<^sub>\<R>\<^sub>\<T> \<Longrightarrow>
           rtWF (\<rho>' @\<^sub>\<R>\<^sub>\<T> \<langle>\<bullet>\<^sub>\<R>\<^sub>\<T>\<rangle>\<^sub>\<R>\<^sub>\<T> @\<^sub>\<R>\<^sub>\<T> TickRT ##\<^sub>\<R>\<^sub>\<T> \<langle>[UNIV]\<^sub>\<R>\<^sub>\<T>\<rangle>\<^sub>\<R>\<^sub>\<T>)"
    show "((acc2maxref (acceptance x1a)) #\<^sub>\<R>\<^sub>\<T> event x1a #\<^sub>\<R>\<^sub>\<T> (fl2rtm_trace \<sigma>)) = \<rho>' @\<^sub>\<R>\<^sub>\<T> \<langle>\<bullet>\<^sub>\<R>\<^sub>\<T>\<rangle>\<^sub>\<R>\<^sub>\<T> @\<^sub>\<R>\<^sub>\<T> TickRT ##\<^sub>\<R>\<^sub>\<T> \<langle>y\<rangle>\<^sub>\<R>\<^sub>\<T> \<Longrightarrow>
       rtWF (\<rho>' @\<^sub>\<R>\<^sub>\<T> \<langle>\<bullet>\<^sub>\<R>\<^sub>\<T>\<rangle>\<^sub>\<R>\<^sub>\<T> @\<^sub>\<R>\<^sub>\<T> TickRT ##\<^sub>\<R>\<^sub>\<T> \<langle>[UNIV]\<^sub>\<R>\<^sub>\<T>\<rangle>\<^sub>\<R>\<^sub>\<T>)"
      apply (induct \<rho>', auto)
      apply (metis (no_types, lifting) acc2maxref.elims acc2maxref.simps(1) amember.simps(2) event_in_acceptance in_rtrefusal.elims(2) in_rtrefusal.simps(1) mem_Collect_eq rtrefusal.inject)
      using ind_hyp by blast
  qed
qed

lemma fl2rtm_MRT0:
  assumes "FL0 P" "FL1 P"
  shows "MRT0 (fl2rtm P)"
proof -
  have "\<langle>\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L> \<in> P"
    using FL0_FL1_bullet_in assms by blast
  then have "\<langle>\<bullet>\<^sub>\<R>\<^sub>\<T>\<rangle>\<^sub>\<R>\<^sub>\<T> \<in> (fl2rtm P)"
    unfolding fl2rtm_def by (safe, simp_all, rule_tac x="\<langle>\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>" in bexI, simp_all)
  then show "MRT0 (fl2rtm P)"
    unfolding MRT0_def by auto
qed

lemma RTM1_init_event:
  assumes "RTM1 P"
  shows "RTM1 {\<rho>. (x #\<^sub>\<R>\<^sub>\<T> a #\<^sub>\<R>\<^sub>\<T> \<rho>) \<in> P}"
  using assms unfolding RTM1_def apply auto
  by (metis leq_rttrace_max.simps(6) leq_rttrace_max.simps(8) rtrefusal.exhaust)

lemma fl2rtm_trace_monotonic:
  "(\<rho>' \<le> \<rho>) = (fl2rtm_trace \<rho>' \<le>\<^sub>\<R>\<^sub>\<T>\<^sub>\<M> fl2rtm_trace \<rho>)"
  apply (induct \<rho>' \<rho> rule:less_eq_fltrace.induct, auto)
  apply (metis (full_types) acc2maxref.simps(1) acc2maxref.simps(2) leq_rttrace_max.simps(1) leq_rttrace_max.simps(2) less_eq_acceptance.elims(2))
  apply (case_tac x, auto, case_tac y, auto)
  apply (case_tac x, auto, case_tac y, auto, case_tac a, auto, presburger+)
  apply (case_tac x, auto, case_tac y, auto, case_tac a, auto)
  apply (case_tac x, auto, case_tac y, auto)
  apply (metis acc2maxref.elims acceptance_event acceptance_set aevent_less_eq_iff_components amember.simps(1) leq_rttrace_max.simps(8))
  apply (metis acceptance_set aevent_less_eq_iff_components amember.simps(1))
  apply (metis acc2maxref.elims acceptance_event leq_rttrace_max.simps(6) leq_rttrace_max.simps(7) less_eq_aevent_def)
  apply (case_tac x, auto, case_tac y, auto, case_tac a, auto, case_tac aa, simp_all)
  apply (metis dual_order.refl equalityI mem_Collect_eq subsetI)
  apply (metis acc2maxref.simps(2) amember.elims(2) leq_rttrace_max.simps(9))
  apply (metis acc2maxref.elims acceptance_event acceptance_set leq_rttrace_max.simps(6) leq_rttrace_max.simps(7) less_eq_acceptance.simps(1) less_eq_aevent_def)
  apply (metis acc2maxref.elims leq_rttrace_max.simps(6) leq_rttrace_max.simps(7) leq_rttrace_max.simps(8) leq_rttrace_max.simps(9))
  by (metis acc2maxref.elims leq_rttrace_max.simps(6) leq_rttrace_max.simps(7) leq_rttrace_max.simps(8) leq_rttrace_max.simps(9))

lemma leq_rttrace_max_fl2rtm_trace_exists:
  "\<And>\<rho>'. \<rho>' \<le>\<^sub>\<R>\<^sub>\<T>\<^sub>\<M> fl2rtm_trace \<sigma> \<Longrightarrow> \<exists>\<sigma>'. \<rho>' = fl2rtm_trace \<sigma>' \<and> \<sigma>' \<le> \<sigma>"
proof (induct \<sigma>, auto)
  fix x and \<rho>' :: "'a rttrace"
  show "\<rho>' \<le>\<^sub>\<R>\<^sub>\<T>\<^sub>\<M> \<langle>acc2maxref x\<rangle>\<^sub>\<R>\<^sub>\<T> \<Longrightarrow> \<exists>\<sigma>'. \<rho>' = fl2rtm_trace \<sigma>' \<and> \<sigma>' \<le> \<langle>x\<rangle>\<^sub>\<F>\<^sub>\<L>"
    apply (induct \<rho>', auto, cases x, auto)
    apply (metis acc2maxref.simps(1) fl2rtm_trace.simps(1) leq_rttrace_max.simps(3) order_refl rtrefusal.exhaust)
    by (metis (full_types) acc2maxref.simps(1) acc2maxref.simps(2) fl2rtm_trace.simps(1) fl2rtm_trace_monotonic leq_rttrace_max.simps(2) rtrefusal.exhaust)
next
  fix x1a and \<sigma> :: "'a fltrace" and \<rho>' :: "'a rttrace"
  assume ind_hyp: "\<And>\<rho>'. \<rho>' \<le>\<^sub>\<R>\<^sub>\<T>\<^sub>\<M> fl2rtm_trace \<sigma> \<Longrightarrow> \<exists>\<sigma>'. \<rho>' = fl2rtm_trace \<sigma>' \<and> \<sigma>' \<le> \<sigma>"
  show "\<rho>' \<le>\<^sub>\<R>\<^sub>\<T>\<^sub>\<M> ((acc2maxref (acceptance x1a)) #\<^sub>\<R>\<^sub>\<T> event x1a #\<^sub>\<R>\<^sub>\<T> (fl2rtm_trace \<sigma>)) \<Longrightarrow> \<exists>\<sigma>'. \<rho>' = fl2rtm_trace \<sigma>' \<and> \<sigma>' \<le> x1a #\<^sub>\<F>\<^sub>\<L> \<sigma>"
    apply (induct \<rho>', cases x1a, auto, case_tac a, auto)
    apply (metis (full_types) acc2maxref.simps(2) acceptance_set amember.simps(2) fl2rtm_trace.simps(1) fl2rtm_trace.simps(2) fl2rtm_trace_monotonic ind_hyp leq_rttrace_max.simps(1) leq_rttrace_max.simps(4) rtrefusal.exhaust)
    apply (metis fl2rtm_trace_monotonic ind_hyp leq_rttrace_max.simps(1) leq_rttrace_max.simps(5) rtrefusal.exhaust)
    apply (cases x1a, auto, case_tac a, auto)
    apply (smt acc2maxref.simps(1) acc2maxref.simps(2) acceptance_event acceptance_set amember.simps(2) bullet_event_acceptance fl2rtm_trace.simps(2) ind_hyp leq_rttrace_max.simps(7) leq_rttrace_max.simps(8) less_eq_fltrace.simps(3) order_refl rtrefusal.exhaust)
    by (metis acc2maxref.simps(1) acceptance_event acceptance_set bullet_event_acceptance fl2rtm_trace.simps(2) ind_hyp leq_rttrace_max.simps(6) leq_rttrace_max.simps(9) less_eq_fltrace.simps(3) rtrefusal.exhaust)
qed

lemma fl2rtm_RTM1:
  assumes "FL1 P"
  shows "RTM1 (fl2rtm P)"
  unfolding RTM1_def fl2rtm_def
proof auto
  fix \<rho> \<sigma>'
  show "\<rho> \<le>\<^sub>\<R>\<^sub>\<T>\<^sub>\<M> fl2rtm_trace \<sigma>' \<Longrightarrow> \<sigma>' \<in> P \<Longrightarrow> \<exists>\<sigma>\<in>P. \<rho> = fl2rtm_trace \<sigma>"
    by (meson FL1_def assms leq_rttrace_max_fl2rtm_trace_exists)
next
  fix \<rho> :: "'a rtevent rttrace" and \<sigma>' \<rho>' y
  assume \<rho>_leq: "\<rho> \<le>\<^sub>\<R>\<^sub>\<T>\<^sub>\<M> \<rho>' @\<^sub>\<R>\<^sub>\<T> \<langle>\<bullet>\<^sub>\<R>\<^sub>\<T>\<rangle>\<^sub>\<R>\<^sub>\<T> @\<^sub>\<R>\<^sub>\<T> TickRT ##\<^sub>\<R>\<^sub>\<T> \<langle>[UNIV]\<^sub>\<R>\<^sub>\<T>\<rangle>\<^sub>\<R>\<^sub>\<T>"
  assume fl2rtm_trace_\<sigma>'_eq: "fl2rtm_trace \<sigma>' = \<rho>' @\<^sub>\<R>\<^sub>\<T> \<langle>\<bullet>\<^sub>\<R>\<^sub>\<T>\<rangle>\<^sub>\<R>\<^sub>\<T> @\<^sub>\<R>\<^sub>\<T> TickRT ##\<^sub>\<R>\<^sub>\<T> \<langle>y\<rangle>\<^sub>\<R>\<^sub>\<T>"
  assume \<sigma>'_in_P: "\<sigma>' \<in> P"

  have "\<rho> \<le>\<^sub>\<R>\<^sub>\<T>\<^sub>\<M> \<rho>' @\<^sub>\<R>\<^sub>\<T> \<langle>\<bullet>\<^sub>\<R>\<^sub>\<T>\<rangle>\<^sub>\<R>\<^sub>\<T> @\<^sub>\<R>\<^sub>\<T> TickRT ##\<^sub>\<R>\<^sub>\<T> \<langle>y\<rangle>\<^sub>\<R>\<^sub>\<T>
    \<or> (\<exists> \<rho>'' y'. \<rho> = \<rho>'' @\<^sub>\<R>\<^sub>\<T> \<langle>\<bullet>\<^sub>\<R>\<^sub>\<T>\<rangle>\<^sub>\<R>\<^sub>\<T> @\<^sub>\<R>\<^sub>\<T> TickRT ##\<^sub>\<R>\<^sub>\<T> \<langle>[UNIV]\<^sub>\<R>\<^sub>\<T>\<rangle>\<^sub>\<R>\<^sub>\<T> \<and> \<rho>'' @\<^sub>\<R>\<^sub>\<T> \<langle>\<bullet>\<^sub>\<R>\<^sub>\<T>\<rangle>\<^sub>\<R>\<^sub>\<T> @\<^sub>\<R>\<^sub>\<T> TickRT ##\<^sub>\<R>\<^sub>\<T> \<langle>y\<rangle>\<^sub>\<R>\<^sub>\<T>  \<le>\<^sub>\<R>\<^sub>\<T>\<^sub>\<M> \<rho>' @\<^sub>\<R>\<^sub>\<T> \<langle>\<bullet>\<^sub>\<R>\<^sub>\<T>\<rangle>\<^sub>\<R>\<^sub>\<T> @\<^sub>\<R>\<^sub>\<T> TickRT ##\<^sub>\<R>\<^sub>\<T> \<langle>y\<rangle>\<^sub>\<R>\<^sub>\<T>)"
    using \<rho>_leq apply auto 
  proof (induct \<rho> \<rho>' rule:leq_rttrace_rttrace_init_max.induct, auto)
    fix x
    show "\<langle>x\<rangle>\<^sub>\<R>\<^sub>\<T> \<le>\<^sub>\<R>\<^sub>\<T>\<^sub>\<M> (\<bullet>\<^sub>\<R>\<^sub>\<T> #\<^sub>\<R>\<^sub>\<T> TickRT #\<^sub>\<R>\<^sub>\<T> \<langle>[UNIV]\<^sub>\<R>\<^sub>\<T>\<rangle>\<^sub>\<R>\<^sub>\<T>) \<Longrightarrow> \<langle>x\<rangle>\<^sub>\<R>\<^sub>\<T> \<le>\<^sub>\<R>\<^sub>\<T>\<^sub>\<M> (\<bullet>\<^sub>\<R>\<^sub>\<T> #\<^sub>\<R>\<^sub>\<T> TickRT #\<^sub>\<R>\<^sub>\<T> \<langle>y\<rangle>\<^sub>\<R>\<^sub>\<T>)"
      by (metis leq_rttrace_max.simps(1) leq_rttrace_max.simps(5) rtrefusal.exhaust)
  next
    fix v va vb
    show "(v #\<^sub>\<R>\<^sub>\<T> va #\<^sub>\<R>\<^sub>\<T> vb) \<le>\<^sub>\<R>\<^sub>\<T>\<^sub>\<M> (\<bullet>\<^sub>\<R>\<^sub>\<T> #\<^sub>\<R>\<^sub>\<T> TickRT #\<^sub>\<R>\<^sub>\<T> \<langle>[UNIV]\<^sub>\<R>\<^sub>\<T>\<rangle>\<^sub>\<R>\<^sub>\<T>) \<Longrightarrow>
       \<forall>\<rho>''. (v #\<^sub>\<R>\<^sub>\<T> va #\<^sub>\<R>\<^sub>\<T> vb) = \<rho>'' @\<^sub>\<R>\<^sub>\<T> \<langle>\<bullet>\<^sub>\<R>\<^sub>\<T>\<rangle>\<^sub>\<R>\<^sub>\<T> @\<^sub>\<R>\<^sub>\<T> TickRT ##\<^sub>\<R>\<^sub>\<T> \<langle>[UNIV]\<^sub>\<R>\<^sub>\<T>\<rangle>\<^sub>\<R>\<^sub>\<T> \<longrightarrow>
             \<not> \<rho>'' @\<^sub>\<R>\<^sub>\<T> \<langle>\<bullet>\<^sub>\<R>\<^sub>\<T>\<rangle>\<^sub>\<R>\<^sub>\<T> @\<^sub>\<R>\<^sub>\<T> TickRT ##\<^sub>\<R>\<^sub>\<T> \<langle>y\<rangle>\<^sub>\<R>\<^sub>\<T> \<le>\<^sub>\<R>\<^sub>\<T>\<^sub>\<M> (\<bullet>\<^sub>\<R>\<^sub>\<T> #\<^sub>\<R>\<^sub>\<T> TickRT #\<^sub>\<R>\<^sub>\<T> \<langle>y\<rangle>\<^sub>\<R>\<^sub>\<T>) \<Longrightarrow>
       (v #\<^sub>\<R>\<^sub>\<T> va #\<^sub>\<R>\<^sub>\<T> vb) \<le>\<^sub>\<R>\<^sub>\<T>\<^sub>\<M> (\<bullet>\<^sub>\<R>\<^sub>\<T> #\<^sub>\<R>\<^sub>\<T> TickRT #\<^sub>\<R>\<^sub>\<T> \<langle>y\<rangle>\<^sub>\<R>\<^sub>\<T>)"
      by (metis leq_rttrace_max.simps(1) leq_rttrace_max.simps(10) leq_rttrace_max.simps(2)
          leq_rttrace_max.simps(6) leq_rttrace_max.simps(9) rtrefusal.exhaust rttrace.exhaust rttrace_with_refusal.simps(2))
  next
    fix vc v va vb
    show "\<langle>vc\<rangle>\<^sub>\<R>\<^sub>\<T> \<le>\<^sub>\<R>\<^sub>\<T>\<^sub>\<M> (v #\<^sub>\<R>\<^sub>\<T> va #\<^sub>\<R>\<^sub>\<T> (vb @\<^sub>\<R>\<^sub>\<T> \<langle>\<bullet>\<^sub>\<R>\<^sub>\<T>\<rangle>\<^sub>\<R>\<^sub>\<T> @\<^sub>\<R>\<^sub>\<T> (TickRT ##\<^sub>\<R>\<^sub>\<T> \<langle>[UNIV]\<^sub>\<R>\<^sub>\<T>\<rangle>\<^sub>\<R>\<^sub>\<T>))) \<Longrightarrow>
       \<langle>vc\<rangle>\<^sub>\<R>\<^sub>\<T> \<le>\<^sub>\<R>\<^sub>\<T>\<^sub>\<M> (v #\<^sub>\<R>\<^sub>\<T> va #\<^sub>\<R>\<^sub>\<T> (vb @\<^sub>\<R>\<^sub>\<T> \<langle>\<bullet>\<^sub>\<R>\<^sub>\<T>\<rangle>\<^sub>\<R>\<^sub>\<T> @\<^sub>\<R>\<^sub>\<T> (TickRT ##\<^sub>\<R>\<^sub>\<T> \<langle>y\<rangle>\<^sub>\<R>\<^sub>\<T>)))"
      by (metis leq_rttrace_max.simps(1) leq_rttrace_max.simps(4) leq_rttrace_max.simps(5) rtrefusal.exhaust)
  next
    fix v va vb vc vd ve
    assume ind_hyp: "vb \<le>\<^sub>\<R>\<^sub>\<T>\<^sub>\<M> ve @\<^sub>\<R>\<^sub>\<T> \<langle>\<bullet>\<^sub>\<R>\<^sub>\<T>\<rangle>\<^sub>\<R>\<^sub>\<T> @\<^sub>\<R>\<^sub>\<T> TickRT ##\<^sub>\<R>\<^sub>\<T> \<langle>[UNIV]\<^sub>\<R>\<^sub>\<T>\<rangle>\<^sub>\<R>\<^sub>\<T> \<Longrightarrow>
        \<forall>\<rho>''. vb = \<rho>'' @\<^sub>\<R>\<^sub>\<T> \<langle>\<bullet>\<^sub>\<R>\<^sub>\<T>\<rangle>\<^sub>\<R>\<^sub>\<T> @\<^sub>\<R>\<^sub>\<T> TickRT ##\<^sub>\<R>\<^sub>\<T> \<langle>[UNIV]\<^sub>\<R>\<^sub>\<T>\<rangle>\<^sub>\<R>\<^sub>\<T> \<longrightarrow>
              \<not> \<rho>'' @\<^sub>\<R>\<^sub>\<T> \<langle>\<bullet>\<^sub>\<R>\<^sub>\<T>\<rangle>\<^sub>\<R>\<^sub>\<T> @\<^sub>\<R>\<^sub>\<T> TickRT ##\<^sub>\<R>\<^sub>\<T> \<langle>y\<rangle>\<^sub>\<R>\<^sub>\<T> \<le>\<^sub>\<R>\<^sub>\<T>\<^sub>\<M> ve @\<^sub>\<R>\<^sub>\<T> \<langle>\<bullet>\<^sub>\<R>\<^sub>\<T>\<rangle>\<^sub>\<R>\<^sub>\<T> @\<^sub>\<R>\<^sub>\<T> TickRT ##\<^sub>\<R>\<^sub>\<T> \<langle>y\<rangle>\<^sub>\<R>\<^sub>\<T> \<Longrightarrow>
        vb \<le>\<^sub>\<R>\<^sub>\<T>\<^sub>\<M> ve @\<^sub>\<R>\<^sub>\<T> \<langle>\<bullet>\<^sub>\<R>\<^sub>\<T>\<rangle>\<^sub>\<R>\<^sub>\<T> @\<^sub>\<R>\<^sub>\<T> TickRT ##\<^sub>\<R>\<^sub>\<T> \<langle>y\<rangle>\<^sub>\<R>\<^sub>\<T>"
    assume case_assm1: "(v #\<^sub>\<R>\<^sub>\<T> va #\<^sub>\<R>\<^sub>\<T> vb) \<le>\<^sub>\<R>\<^sub>\<T>\<^sub>\<M> (vc #\<^sub>\<R>\<^sub>\<T> vd #\<^sub>\<R>\<^sub>\<T> (ve @\<^sub>\<R>\<^sub>\<T> \<langle>\<bullet>\<^sub>\<R>\<^sub>\<T>\<rangle>\<^sub>\<R>\<^sub>\<T> @\<^sub>\<R>\<^sub>\<T> TickRT ##\<^sub>\<R>\<^sub>\<T> \<langle>[UNIV]\<^sub>\<R>\<^sub>\<T>\<rangle>\<^sub>\<R>\<^sub>\<T>))"
    assume case_assm2: "\<forall>\<rho>''. (v #\<^sub>\<R>\<^sub>\<T> va #\<^sub>\<R>\<^sub>\<T> vb) = \<rho>'' @\<^sub>\<R>\<^sub>\<T> \<langle>\<bullet>\<^sub>\<R>\<^sub>\<T>\<rangle>\<^sub>\<R>\<^sub>\<T> @\<^sub>\<R>\<^sub>\<T> TickRT ##\<^sub>\<R>\<^sub>\<T> \<langle>[UNIV]\<^sub>\<R>\<^sub>\<T>\<rangle>\<^sub>\<R>\<^sub>\<T> \<longrightarrow>
             \<not> (\<rho>'' @\<^sub>\<R>\<^sub>\<T> \<langle>\<bullet>\<^sub>\<R>\<^sub>\<T>\<rangle>\<^sub>\<R>\<^sub>\<T> @\<^sub>\<R>\<^sub>\<T> TickRT ##\<^sub>\<R>\<^sub>\<T> \<langle>y\<rangle>\<^sub>\<R>\<^sub>\<T>) \<le>\<^sub>\<R>\<^sub>\<T>\<^sub>\<M> (vc #\<^sub>\<R>\<^sub>\<T> vd #\<^sub>\<R>\<^sub>\<T> (ve @\<^sub>\<R>\<^sub>\<T> \<langle>\<bullet>\<^sub>\<R>\<^sub>\<T>\<rangle>\<^sub>\<R>\<^sub>\<T> @\<^sub>\<R>\<^sub>\<T> TickRT ##\<^sub>\<R>\<^sub>\<T> \<langle>y\<rangle>\<^sub>\<R>\<^sub>\<T>))"

    have 1: "vb \<le>\<^sub>\<R>\<^sub>\<T>\<^sub>\<M> ve @\<^sub>\<R>\<^sub>\<T> \<langle>\<bullet>\<^sub>\<R>\<^sub>\<T>\<rangle>\<^sub>\<R>\<^sub>\<T> @\<^sub>\<R>\<^sub>\<T> TickRT ##\<^sub>\<R>\<^sub>\<T> \<langle>[UNIV]\<^sub>\<R>\<^sub>\<T>\<rangle>\<^sub>\<R>\<^sub>\<T>"
      by (metis case_assm1 leq_rttrace_max.simps(6) leq_rttrace_max.simps(7) leq_rttrace_max.simps(8) leq_rttrace_max.simps(9) rtrefusal.exhaust)

    have 2: "\<forall>\<rho>''. vb = \<rho>'' @\<^sub>\<R>\<^sub>\<T> \<langle>\<bullet>\<^sub>\<R>\<^sub>\<T>\<rangle>\<^sub>\<R>\<^sub>\<T> @\<^sub>\<R>\<^sub>\<T> TickRT ##\<^sub>\<R>\<^sub>\<T> \<langle>[UNIV]\<^sub>\<R>\<^sub>\<T>\<rangle>\<^sub>\<R>\<^sub>\<T> \<longrightarrow>
              \<not> \<rho>'' @\<^sub>\<R>\<^sub>\<T> \<langle>\<bullet>\<^sub>\<R>\<^sub>\<T>\<rangle>\<^sub>\<R>\<^sub>\<T> @\<^sub>\<R>\<^sub>\<T> TickRT ##\<^sub>\<R>\<^sub>\<T> \<langle>y\<rangle>\<^sub>\<R>\<^sub>\<T> \<le>\<^sub>\<R>\<^sub>\<T>\<^sub>\<M> ve @\<^sub>\<R>\<^sub>\<T> \<langle>\<bullet>\<^sub>\<R>\<^sub>\<T>\<rangle>\<^sub>\<R>\<^sub>\<T> @\<^sub>\<R>\<^sub>\<T> TickRT ##\<^sub>\<R>\<^sub>\<T> \<langle>y\<rangle>\<^sub>\<R>\<^sub>\<T>"
      using case_assm2 apply (auto, erule_tac x="RTEventInit v va \<rho>''" in allE, auto)
      by (metis case_assm1 leq_rttrace_max.simps(6) leq_rttrace_max.simps(7) leq_rttrace_max.simps(8) leq_rttrace_max.simps(9) rtrefusal.exhaust)

    have "vb \<le>\<^sub>\<R>\<^sub>\<T>\<^sub>\<M> ve @\<^sub>\<R>\<^sub>\<T> \<langle>\<bullet>\<^sub>\<R>\<^sub>\<T>\<rangle>\<^sub>\<R>\<^sub>\<T> @\<^sub>\<R>\<^sub>\<T> TickRT ##\<^sub>\<R>\<^sub>\<T> \<langle>y\<rangle>\<^sub>\<R>\<^sub>\<T>"
      using "1" "2" ind_hyp by blast
    then show "(v #\<^sub>\<R>\<^sub>\<T> va #\<^sub>\<R>\<^sub>\<T> vb) \<le>\<^sub>\<R>\<^sub>\<T>\<^sub>\<M> (vc #\<^sub>\<R>\<^sub>\<T> vd #\<^sub>\<R>\<^sub>\<T> (ve @\<^sub>\<R>\<^sub>\<T> \<langle>\<bullet>\<^sub>\<R>\<^sub>\<T>\<rangle>\<^sub>\<R>\<^sub>\<T> @\<^sub>\<R>\<^sub>\<T> TickRT ##\<^sub>\<R>\<^sub>\<T> \<langle>y\<rangle>\<^sub>\<R>\<^sub>\<T>))"
      by (metis case_assm1 leq_rttrace_max.simps(6) leq_rttrace_max.simps(7) leq_rttrace_max.simps(8) leq_rttrace_max.simps(9) rtrefusal.exhaust)
  qed
  then show "\<forall>\<sigma>\<in>P. \<forall>\<rho>'. (\<forall>y. fl2rtm_trace \<sigma> \<noteq> \<rho>' @\<^sub>\<R>\<^sub>\<T> \<langle>\<bullet>\<^sub>\<R>\<^sub>\<T>\<rangle>\<^sub>\<R>\<^sub>\<T> @\<^sub>\<R>\<^sub>\<T> TickRT ##\<^sub>\<R>\<^sub>\<T> \<langle>y\<rangle>\<^sub>\<R>\<^sub>\<T>) \<or>
                   \<rho> \<noteq> \<rho>' @\<^sub>\<R>\<^sub>\<T> \<langle>\<bullet>\<^sub>\<R>\<^sub>\<T>\<rangle>\<^sub>\<R>\<^sub>\<T> @\<^sub>\<R>\<^sub>\<T> TickRT ##\<^sub>\<R>\<^sub>\<T> \<langle>[UNIV]\<^sub>\<R>\<^sub>\<T>\<rangle>\<^sub>\<R>\<^sub>\<T> \<Longrightarrow> \<exists>\<sigma>\<in>P. \<rho> = fl2rtm_trace \<sigma>"
  proof auto
    assume "\<rho> \<le>\<^sub>\<R>\<^sub>\<T>\<^sub>\<M> \<rho>' @\<^sub>\<R>\<^sub>\<T> \<langle>\<bullet>\<^sub>\<R>\<^sub>\<T>\<rangle>\<^sub>\<R>\<^sub>\<T> @\<^sub>\<R>\<^sub>\<T> TickRT ##\<^sub>\<R>\<^sub>\<T> \<langle>y\<rangle>\<^sub>\<R>\<^sub>\<T>"
    then show "\<forall>\<sigma>\<in>P. \<forall>\<rho>'. (\<forall>y. fl2rtm_trace \<sigma> \<noteq> \<rho>' @\<^sub>\<R>\<^sub>\<T> \<langle>\<bullet>\<^sub>\<R>\<^sub>\<T>\<rangle>\<^sub>\<R>\<^sub>\<T> @\<^sub>\<R>\<^sub>\<T> TickRT ##\<^sub>\<R>\<^sub>\<T> \<langle>y\<rangle>\<^sub>\<R>\<^sub>\<T>) \<or>
                   \<rho> \<noteq> \<rho>' @\<^sub>\<R>\<^sub>\<T> \<langle>\<bullet>\<^sub>\<R>\<^sub>\<T>\<rangle>\<^sub>\<R>\<^sub>\<T> @\<^sub>\<R>\<^sub>\<T> TickRT ##\<^sub>\<R>\<^sub>\<T> \<langle>[UNIV]\<^sub>\<R>\<^sub>\<T>\<rangle>\<^sub>\<R>\<^sub>\<T> \<Longrightarrow> \<exists>\<sigma>\<in>P. \<rho> = fl2rtm_trace \<sigma>"
      by (metis FL1_def \<sigma>'_in_P assms fl2rtm_trace_\<sigma>'_eq leq_rttrace_max_fl2rtm_trace_exists)
  next
    fix \<rho>''
    assume case_assm1: "\<rho>'' @\<^sub>\<R>\<^sub>\<T> \<langle>\<bullet>\<^sub>\<R>\<^sub>\<T>\<rangle>\<^sub>\<R>\<^sub>\<T> @\<^sub>\<R>\<^sub>\<T> TickRT ##\<^sub>\<R>\<^sub>\<T> \<langle>y\<rangle>\<^sub>\<R>\<^sub>\<T> \<le>\<^sub>\<R>\<^sub>\<T>\<^sub>\<M> \<rho>' @\<^sub>\<R>\<^sub>\<T> \<langle>\<bullet>\<^sub>\<R>\<^sub>\<T>\<rangle>\<^sub>\<R>\<^sub>\<T> @\<^sub>\<R>\<^sub>\<T> TickRT ##\<^sub>\<R>\<^sub>\<T> \<langle>y\<rangle>\<^sub>\<R>\<^sub>\<T>"
    assume case_assm2: "\<rho> = \<rho>'' @\<^sub>\<R>\<^sub>\<T> \<langle>\<bullet>\<^sub>\<R>\<^sub>\<T>\<rangle>\<^sub>\<R>\<^sub>\<T> @\<^sub>\<R>\<^sub>\<T> TickRT ##\<^sub>\<R>\<^sub>\<T> \<langle>[UNIV]\<^sub>\<R>\<^sub>\<T>\<rangle>\<^sub>\<R>\<^sub>\<T>"

    have "\<exists>\<sigma>''\<in>P. \<rho>'' @\<^sub>\<R>\<^sub>\<T> \<langle>\<bullet>\<^sub>\<R>\<^sub>\<T>\<rangle>\<^sub>\<R>\<^sub>\<T> @\<^sub>\<R>\<^sub>\<T> TickRT ##\<^sub>\<R>\<^sub>\<T> \<langle>y\<rangle>\<^sub>\<R>\<^sub>\<T> = fl2rtm_trace \<sigma>''"
      by (metis FL1_def \<sigma>'_in_P assms case_assm1 fl2rtm_trace_\<sigma>'_eq leq_rttrace_max_fl2rtm_trace_exists)
    then show "\<forall>\<sigma>\<in>P. \<forall>\<rho>'. (\<forall>y. fl2rtm_trace \<sigma> \<noteq> \<rho>' @\<^sub>\<R>\<^sub>\<T> \<langle>\<bullet>\<^sub>\<R>\<^sub>\<T>\<rangle>\<^sub>\<R>\<^sub>\<T> @\<^sub>\<R>\<^sub>\<T> TickRT ##\<^sub>\<R>\<^sub>\<T> \<langle>y\<rangle>\<^sub>\<R>\<^sub>\<T>) \<or>
                      \<rho>'' @\<^sub>\<R>\<^sub>\<T> \<langle>\<bullet>\<^sub>\<R>\<^sub>\<T>\<rangle>\<^sub>\<R>\<^sub>\<T> @\<^sub>\<R>\<^sub>\<T> TickRT ##\<^sub>\<R>\<^sub>\<T> \<langle>[UNIV]\<^sub>\<R>\<^sub>\<T>\<rangle>\<^sub>\<R>\<^sub>\<T> \<noteq> \<rho>' @\<^sub>\<R>\<^sub>\<T> \<langle>\<bullet>\<^sub>\<R>\<^sub>\<T>\<rangle>\<^sub>\<R>\<^sub>\<T> @\<^sub>\<R>\<^sub>\<T> TickRT ##\<^sub>\<R>\<^sub>\<T> \<langle>[UNIV]\<^sub>\<R>\<^sub>\<T>\<rangle>\<^sub>\<R>\<^sub>\<T>
        \<Longrightarrow> \<exists>\<sigma>\<in>P. \<rho>'' @\<^sub>\<R>\<^sub>\<T> \<langle>\<bullet>\<^sub>\<R>\<^sub>\<T>\<rangle>\<^sub>\<R>\<^sub>\<T> @\<^sub>\<R>\<^sub>\<T> TickRT ##\<^sub>\<R>\<^sub>\<T> \<langle>[UNIV]\<^sub>\<R>\<^sub>\<T>\<rangle>\<^sub>\<R>\<^sub>\<T> = fl2rtm_trace \<sigma>"
      by (metis case_assm2)
  qed
qed
  

lemma fl2rtm_trace_concat2_acceptance:
  "last \<beta> = A \<Longrightarrow> fl2rtm_trace (\<beta> &\<^sub>\<F>\<^sub>\<L> \<langle>B\<rangle>\<^sub>\<F>\<^sub>\<L>) = (rttrace2init (fl2rtm_trace \<beta>)) @\<^sub>\<R>\<^sub>\<T> \<langle>acc2maxref (A+B)\<rangle>\<^sub>\<R>\<^sub>\<T> @\<^sub>\<R>\<^sub>\<T> RTEmptyTail"
  by (induct \<beta>, auto)

lemma "A \<noteq> \<bullet> \<longrightarrow> e \<in>\<^sub>\<F>\<^sub>\<L> A \<Longrightarrow> acceptance (A,e)\<^sub>\<F>\<^sub>\<L> = A"
proof -
  assume assm: "A \<noteq> \<bullet> \<longrightarrow> e \<in>\<^sub>\<F>\<^sub>\<L> A"
  have "acceptance (A,e)\<^sub>\<F>\<^sub>\<L> = fst (Rep_aevent (A,e)\<^sub>\<F>\<^sub>\<L>)"
    by (simp add: acceptance.rep_eq)
  also have "... = A"
    by (subst Abs_aevent_inverse, auto simp add: assm)
  then show ?thesis
    using calculation by auto
qed

lemma fl2rtm_trace_concat2_event:
  "last \<beta> = \<bullet> \<Longrightarrow> e \<in>\<^sub>\<F>\<^sub>\<L> A \<Longrightarrow> fl2rtm_trace (\<beta> &\<^sub>\<F>\<^sub>\<L> \<langle>(A,e)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>) = (rttrace2init (fl2rtm_trace \<beta>)) @\<^sub>\<R>\<^sub>\<T> \<langle>acc2maxref (A)\<rangle>\<^sub>\<R>\<^sub>\<T> @\<^sub>\<R>\<^sub>\<T> e ##\<^sub>\<R>\<^sub>\<T> \<langle>\<bullet>\<^sub>\<R>\<^sub>\<T>\<rangle>\<^sub>\<R>\<^sub>\<T>"
  by (induct \<beta>, auto)

lemma fl2rtm_RTM2:
  assumes FL2_P: "FL2 P"
  shows "RTM2 (fl2rtm P)"
  unfolding RTM2_def fl2rtm_def
proof auto
  fix \<rho> X e \<sigma>
  assume assms: "e \<notin> X" "\<sigma> \<in> P" "\<rho> @\<^sub>\<R>\<^sub>\<T> \<langle>[X]\<^sub>\<R>\<^sub>\<T>\<rangle>\<^sub>\<R>\<^sub>\<T> @\<^sub>\<R>\<^sub>\<T> RTEmptyTail = fl2rtm_trace \<sigma>"
  then obtain \<beta> A where \<sigma>_def: "\<sigma> = \<beta> &\<^sub>\<F>\<^sub>\<L> \<langle>A\<rangle>\<^sub>\<F>\<^sub>\<L> \<and> last \<beta> = \<bullet>"
    by (metis last_rev3_is_bullet rev3_rev3_const2_last)
  then have 1: "fl2rtm_trace \<sigma> = (rttrace2init (fl2rtm_trace \<beta>)) @\<^sub>\<R>\<^sub>\<T> \<langle>acc2maxref (A)\<rangle>\<^sub>\<R>\<^sub>\<T> @\<^sub>\<R>\<^sub>\<T> RTEmptyTail"
    by (simp add: fl2rtm_trace_concat2_acceptance)
  then have 2: "\<rho> @\<^sub>\<R>\<^sub>\<T> \<langle>[X]\<^sub>\<R>\<^sub>\<T>\<rangle>\<^sub>\<R>\<^sub>\<T> @\<^sub>\<R>\<^sub>\<T> RTEmptyTail = (rttrace2init (fl2rtm_trace \<beta>)) @\<^sub>\<R>\<^sub>\<T> \<langle>acc2maxref (A)\<rangle>\<^sub>\<R>\<^sub>\<T> @\<^sub>\<R>\<^sub>\<T> RTEmptyTail"
    using assms(3) by auto
  then have 3: "[X]\<^sub>\<R>\<^sub>\<T> = acc2maxref (A)"
    using rttrace_with_refusal_eq2 by blast
  then have 4: "\<beta> &\<^sub>\<F>\<^sub>\<L> \<langle>(A,e)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L> \<in> P"
    using FL2_P assms \<sigma>_def unfolding FL2_def apply auto
    apply (erule_tac x="\<beta>" in allE, erule_tac x="A" in allE, erule_tac x="e" in allE, auto)
    by (metis CollectI acc2maxref.elims amember.simps(2) rtrefusal.distinct(1) rtrefusal.inject)
  then show "\<exists>\<sigma>\<in>P. \<rho> @\<^sub>\<R>\<^sub>\<T> \<langle>[X]\<^sub>\<R>\<^sub>\<T>\<rangle>\<^sub>\<R>\<^sub>\<T> @\<^sub>\<R>\<^sub>\<T> e ##\<^sub>\<R>\<^sub>\<T> \<langle>\<bullet>\<^sub>\<R>\<^sub>\<T>\<rangle>\<^sub>\<R>\<^sub>\<T> = fl2rtm_trace \<sigma>"
    apply (rule_tac x="\<beta> &\<^sub>\<F>\<^sub>\<L> \<langle>(A,e)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>" in bexI, auto)
    by (metis 2 3 CollectI \<sigma>_def acc2maxref.elims amember.simps(2) assms(1)
        fl2rtm_trace_concat2_event rtrefusal.distinct(1) rtrefusal.inject rttrace_with_refusal_eq1)
next
  fix \<rho> X e \<sigma> \<rho>' y
  assume assms: "e \<notin> X" "\<sigma> \<in> P" "fl2rtm_trace \<sigma> = \<rho>' @\<^sub>\<R>\<^sub>\<T> \<langle>\<bullet>\<^sub>\<R>\<^sub>\<T>\<rangle>\<^sub>\<R>\<^sub>\<T> @\<^sub>\<R>\<^sub>\<T> TickRT ##\<^sub>\<R>\<^sub>\<T> \<langle>y\<rangle>\<^sub>\<R>\<^sub>\<T>"
    "\<rho> @\<^sub>\<R>\<^sub>\<T> \<langle>[X]\<^sub>\<R>\<^sub>\<T>\<rangle>\<^sub>\<R>\<^sub>\<T> @\<^sub>\<R>\<^sub>\<T> RTEmptyTail = \<rho>' @\<^sub>\<R>\<^sub>\<T> \<langle>\<bullet>\<^sub>\<R>\<^sub>\<T>\<rangle>\<^sub>\<R>\<^sub>\<T> @\<^sub>\<R>\<^sub>\<T> TickRT ##\<^sub>\<R>\<^sub>\<T> \<langle>[UNIV]\<^sub>\<R>\<^sub>\<T>\<rangle>\<^sub>\<R>\<^sub>\<T>"

  have "X = UNIV"
    using assms(4) apply (auto, induct \<rho> \<rho>' rule:leq_rttrace_init.induct, auto)
    apply (metis (full_types) rttrace.distinct(1) rttrace_with_refusal.elims rttrace_with_refusal.simps(2))
    by (metis UNIV_I rtrefusal.inject rttrace_with_refusal.simps(3) rttrace_with_refusal_eq2)
  then have "False"
    using assms(1) by auto
  then show "\<exists>\<sigma>\<in>P. \<rho> @\<^sub>\<R>\<^sub>\<T> \<langle>[X]\<^sub>\<R>\<^sub>\<T>\<rangle>\<^sub>\<R>\<^sub>\<T> @\<^sub>\<R>\<^sub>\<T> e ##\<^sub>\<R>\<^sub>\<T> \<langle>\<bullet>\<^sub>\<R>\<^sub>\<T>\<rangle>\<^sub>\<R>\<^sub>\<T> = fl2rtm_trace \<sigma>"
    by auto
qed

lemma no_tick_lemma: "\<And>P \<rho>. \<sigma> \<in> P \<Longrightarrow> tickWF TickRT \<sigma> \<Longrightarrow> \<rho> @\<^sub>\<R>\<^sub>\<T> \<langle>x\<rangle>\<^sub>\<R>\<^sub>\<T> @\<^sub>\<R>\<^sub>\<T> e ##\<^sub>\<R>\<^sub>\<T> \<langle>y\<rangle>\<^sub>\<R>\<^sub>\<T> = fl2rtm_trace \<sigma> \<Longrightarrow> no_tick \<rho>"
proof (induct \<sigma>, simp_all)
  fix xa P \<rho>
  show "TickRT \<notin>\<^sub>\<F>\<^sub>\<L> xa \<Longrightarrow> \<rho> @\<^sub>\<R>\<^sub>\<T> \<langle>x\<rangle>\<^sub>\<R>\<^sub>\<T> @\<^sub>\<R>\<^sub>\<T> e ##\<^sub>\<R>\<^sub>\<T> \<langle>y\<rangle>\<^sub>\<R>\<^sub>\<T> = \<langle>acc2maxref xa\<rangle>\<^sub>\<R>\<^sub>\<T> \<Longrightarrow>  no_tick \<rho>"
    using rttrace_with_refusal.elims by blast
next
  fix x1a :: "'a rtevent aevent" and \<sigma> :: "'a rtevent fltrace" and \<rho> :: "'a rtevent rttrace_init" and P
  assume ind_hyp: "\<And>P \<rho>. \<sigma> \<in> P \<Longrightarrow> tickWF TickRT \<sigma> \<Longrightarrow> \<rho> @\<^sub>\<R>\<^sub>\<T> \<langle>x\<rangle>\<^sub>\<R>\<^sub>\<T> @\<^sub>\<R>\<^sub>\<T> e ##\<^sub>\<R>\<^sub>\<T> \<langle>y\<rangle>\<^sub>\<R>\<^sub>\<T> = fl2rtm_trace \<sigma> \<Longrightarrow> no_tick \<rho>"
  assume assm1: "TickRT \<notin>\<^sub>\<F>\<^sub>\<L> acceptance x1a \<and> (if event x1a = TickRT then \<sigma> = \<langle>\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L> else tickWF TickRT \<sigma>)"
  assume assm2: "(\<rho> @\<^sub>\<R>\<^sub>\<T> \<langle>x\<rangle>\<^sub>\<R>\<^sub>\<T> @\<^sub>\<R>\<^sub>\<T> e ##\<^sub>\<R>\<^sub>\<T> \<langle>y\<rangle>\<^sub>\<R>\<^sub>\<T>) = ((acc2maxref (acceptance x1a)) #\<^sub>\<R>\<^sub>\<T> event x1a #\<^sub>\<R>\<^sub>\<T> (fl2rtm_trace \<sigma>))"
  assume assm3: "x1a #\<^sub>\<F>\<^sub>\<L> \<sigma> \<in> P"

  show "no_tick \<rho>"
    using assm2
  proof (cases \<rho>, simp_all)
    fix \<rho>'
    assume \<rho>_def: "\<rho> = RTEventInit (acc2maxref (acceptance x1a)) (event x1a) \<rho>'"

    have x1a_no_tick: "event x1a \<noteq> TickRT"
      using assm1 assm2 \<rho>_def by (auto, cases \<rho>', auto)
    then have "no_tick \<rho>'"
      using \<rho>_def assm1 assm2 assm3 ind_hyp by auto
    then show "no_tick (RTEventInit (acc2maxref (acceptance x1a)) (event x1a) \<rho>')"
      using no_tick.elims(3) x1a_no_tick by blast
  qed
qed

thm FLTick0_def tickWF.simps RT4_def

lemma fl2rtm_RT3:
  assumes "FLTick0 TickRT P" "FL2 P"
  shows "RT3 (fl2rtm P)"
  using assms no_tick_lemma unfolding FLTick0_def RT3_def fl2rtm_def
  by (auto, blast, metis rttrace_with_refusal_eq3)

lemma fltrace_TickRT_end_exists:
  "\<And> \<rho>. \<rho> @\<^sub>\<R>\<^sub>\<T> \<langle>x\<rangle>\<^sub>\<R>\<^sub>\<T> @\<^sub>\<R>\<^sub>\<T> TickRT ##\<^sub>\<R>\<^sub>\<T> \<langle>y\<rangle>\<^sub>\<R>\<^sub>\<T> = fl2rtm_trace \<sigma> \<Longrightarrow> 
  \<exists> A B \<sigma>'. \<sigma> = \<sigma>' &\<^sub>\<F>\<^sub>\<L> \<langle>(A,TickRT)\<^sub>\<F>\<^sub>\<L>,B\<rangle>\<^sub>\<F>\<^sub>\<L> \<and> fl2rtm_trace \<sigma>' = \<rho> @\<^sub>\<R>\<^sub>\<T> \<langle>\<bullet>\<^sub>\<R>\<^sub>\<T>\<rangle>\<^sub>\<R>\<^sub>\<T> @\<^sub>\<R>\<^sub>\<T> RTEmptyTail
    \<and> (TickRT \<in>\<^sub>\<F>\<^sub>\<L> A \<or> A = \<bullet>) \<and> acc2maxref A = x \<and> acc2maxref B = y"
proof (induct \<sigma>, auto)
  fix xa \<rho>
  show "\<rho> @\<^sub>\<R>\<^sub>\<T> \<langle>x\<rangle>\<^sub>\<R>\<^sub>\<T> @\<^sub>\<R>\<^sub>\<T> TickRT ##\<^sub>\<R>\<^sub>\<T> \<langle>y\<rangle>\<^sub>\<R>\<^sub>\<T> = \<langle>acc2maxref xa\<rangle>\<^sub>\<R>\<^sub>\<T> \<Longrightarrow>
       \<exists>A B \<sigma>'. \<langle>xa\<rangle>\<^sub>\<F>\<^sub>\<L> = \<sigma>' &\<^sub>\<F>\<^sub>\<L> \<langle>(A,TickRT)\<^sub>\<F>\<^sub>\<L>,B\<rangle>\<^sub>\<F>\<^sub>\<L> \<and>
          fl2rtm_trace \<sigma>' = \<rho> @\<^sub>\<R>\<^sub>\<T> \<langle>\<bullet>\<^sub>\<R>\<^sub>\<T>\<rangle>\<^sub>\<R>\<^sub>\<T> @\<^sub>\<R>\<^sub>\<T> RTEmptyTail \<and> (TickRT \<in>\<^sub>\<F>\<^sub>\<L> A \<or> A = \<bullet>) \<and> acc2maxref A = x \<and> acc2maxref B = y"
    using rttrace_with_refusal.elims by blast
next
  fix x1a \<sigma> \<rho>
  assume ind_hyp: "\<And>\<rho>. \<rho> @\<^sub>\<R>\<^sub>\<T> \<langle>x\<rangle>\<^sub>\<R>\<^sub>\<T> @\<^sub>\<R>\<^sub>\<T> TickRT ##\<^sub>\<R>\<^sub>\<T> \<langle>y\<rangle>\<^sub>\<R>\<^sub>\<T> = fl2rtm_trace \<sigma> \<Longrightarrow>
              \<exists>A B \<sigma>'. \<sigma> = \<sigma>' &\<^sub>\<F>\<^sub>\<L> \<langle>(A,TickRT)\<^sub>\<F>\<^sub>\<L>,B\<rangle>\<^sub>\<F>\<^sub>\<L> \<and> fl2rtm_trace \<sigma>' = \<rho> @\<^sub>\<R>\<^sub>\<T> \<langle>\<bullet>\<^sub>\<R>\<^sub>\<T>\<rangle>\<^sub>\<R>\<^sub>\<T> @\<^sub>\<R>\<^sub>\<T> RTEmptyTail \<and>
                (TickRT \<in>\<^sub>\<F>\<^sub>\<L> A \<or> A = \<bullet>) \<and> acc2maxref A = x \<and> acc2maxref B = y"
  assume assm: "(\<rho> @\<^sub>\<R>\<^sub>\<T> \<langle>x\<rangle>\<^sub>\<R>\<^sub>\<T> @\<^sub>\<R>\<^sub>\<T> TickRT ##\<^sub>\<R>\<^sub>\<T> \<langle>y\<rangle>\<^sub>\<R>\<^sub>\<T>) = ((acc2maxref (acceptance x1a)) #\<^sub>\<R>\<^sub>\<T> event x1a #\<^sub>\<R>\<^sub>\<T> (fl2rtm_trace \<sigma>))"
  then show "\<exists>A B \<sigma>'. x1a #\<^sub>\<F>\<^sub>\<L> \<sigma> = \<sigma>' &\<^sub>\<F>\<^sub>\<L> \<langle>(A,TickRT)\<^sub>\<F>\<^sub>\<L>,B\<rangle>\<^sub>\<F>\<^sub>\<L> \<and>
          fl2rtm_trace \<sigma>' = \<rho> @\<^sub>\<R>\<^sub>\<T> \<langle>\<bullet>\<^sub>\<R>\<^sub>\<T>\<rangle>\<^sub>\<R>\<^sub>\<T> @\<^sub>\<R>\<^sub>\<T> RTEmptyTail \<and> (TickRT \<in>\<^sub>\<F>\<^sub>\<L> A \<or> A = \<bullet>) \<and> acc2maxref A = x \<and> acc2maxref B = y"
    apply -
  proof (induct \<rho>, auto)
    assume case_assms: "x = acc2maxref (acceptance x1a)" "TickRT = event x1a" "\<langle>y\<rangle>\<^sub>\<R>\<^sub>\<T> = fl2rtm_trace \<sigma>"
    then show "\<exists>A B \<sigma>''. x1a #\<^sub>\<F>\<^sub>\<L> \<sigma> = \<sigma>'' &\<^sub>\<F>\<^sub>\<L> \<langle>(A,TickRT)\<^sub>\<F>\<^sub>\<L>,B\<rangle>\<^sub>\<F>\<^sub>\<L> \<and>fl2rtm_trace \<sigma>'' = \<langle>\<bullet>\<^sub>\<R>\<^sub>\<T>\<rangle>\<^sub>\<R>\<^sub>\<T>
      \<and> (TickRT \<in>\<^sub>\<F>\<^sub>\<L> A \<or> A = \<bullet>) \<and> acc2maxref A = acc2maxref (acceptance x1a) \<and> acc2maxref B = y"
      apply (cases x1a, clarsimp, rule_tac x="a" in exI, simp)
      by (metis acc2maxref.simps(1) bullet_left_zero2 fl2rtm_trace.elims fl2rtm_trace.simps(1) rttrace.distinct(1) rttrace.inject(1))
  next
    fix \<rho>
    assume "\<rho> @\<^sub>\<R>\<^sub>\<T> \<langle>x\<rangle>\<^sub>\<R>\<^sub>\<T> @\<^sub>\<R>\<^sub>\<T> TickRT ##\<^sub>\<R>\<^sub>\<T> \<langle>y\<rangle>\<^sub>\<R>\<^sub>\<T> = fl2rtm_trace \<sigma>"
    then obtain A B \<sigma>' where "\<sigma> = \<sigma>' &\<^sub>\<F>\<^sub>\<L> \<langle>(A,TickRT)\<^sub>\<F>\<^sub>\<L>,B\<rangle>\<^sub>\<F>\<^sub>\<L> \<and>
                (TickRT \<in>\<^sub>\<F>\<^sub>\<L> A \<or> A = \<bullet>) \<and> fl2rtm_trace \<sigma>' = \<rho> @\<^sub>\<R>\<^sub>\<T> \<langle>\<bullet>\<^sub>\<R>\<^sub>\<T>\<rangle>\<^sub>\<R>\<^sub>\<T> @\<^sub>\<R>\<^sub>\<T> RTEmptyTail \<and> acc2maxref A = x \<and> acc2maxref B = y"
      using ind_hyp by blast
    then show "\<exists>A B \<sigma>''. (x1a #\<^sub>\<F>\<^sub>\<L> \<sigma>) = \<sigma>'' &\<^sub>\<F>\<^sub>\<L> \<langle>(A,TickRT)\<^sub>\<F>\<^sub>\<L>,B\<rangle>\<^sub>\<F>\<^sub>\<L> \<and>
            fl2rtm_trace \<sigma>'' = ((acc2maxref (acceptance x1a)) #\<^sub>\<R>\<^sub>\<T> event x1a #\<^sub>\<R>\<^sub>\<T> (\<rho> @\<^sub>\<R>\<^sub>\<T> \<langle>\<bullet>\<^sub>\<R>\<^sub>\<T>\<rangle>\<^sub>\<R>\<^sub>\<T> @\<^sub>\<R>\<^sub>\<T> RTEmptyTail)) \<and>
            (TickRT \<in>\<^sub>\<F>\<^sub>\<L> A \<or> A = \<bullet>) \<and> acc2maxref A = x \<and> acc2maxref B = y"
      by (metis fl2rtm_trace.simps(2) fltrace_concat2.simps(2))
  qed
qed

term "Abs_aevent"
term "Rep_aevent"
thm Abs_aevent_cases

lemma fltrace_TickRT_end_butlast_bullet:
  "\<rho> @\<^sub>\<R>\<^sub>\<T> \<langle>x\<rangle>\<^sub>\<R>\<^sub>\<T> @\<^sub>\<R>\<^sub>\<T> TickRT ##\<^sub>\<R>\<^sub>\<T> \<langle>y\<rangle>\<^sub>\<R>\<^sub>\<T> = fl2rtm_trace \<sigma> \<Longrightarrow> tickWF TickRT \<sigma> \<Longrightarrow> x = \<bullet>\<^sub>\<R>\<^sub>\<T>"
proof -
  assume \<sigma>_assm: "\<rho> @\<^sub>\<R>\<^sub>\<T> \<langle>x\<rangle>\<^sub>\<R>\<^sub>\<T> @\<^sub>\<R>\<^sub>\<T> TickRT ##\<^sub>\<R>\<^sub>\<T> \<langle>y\<rangle>\<^sub>\<R>\<^sub>\<T> = fl2rtm_trace \<sigma>"
  assume \<sigma>_tickWF: "tickWF TickRT \<sigma>"
  obtain \<sigma>' A B where \<sigma>'_assms:
    "\<sigma> = \<sigma>' &\<^sub>\<F>\<^sub>\<L> \<langle>(A,TickRT)\<^sub>\<F>\<^sub>\<L>,B\<rangle>\<^sub>\<F>\<^sub>\<L> \<and> fl2rtm_trace \<sigma>' = \<rho> @\<^sub>\<R>\<^sub>\<T> \<langle>\<bullet>\<^sub>\<R>\<^sub>\<T>\<rangle>\<^sub>\<R>\<^sub>\<T> @\<^sub>\<R>\<^sub>\<T> RTEmptyTail \<and> acc2maxref A = x \<and> acc2maxref B = y \<and> (TickRT \<in>\<^sub>\<F>\<^sub>\<L> A \<or> A = \<bullet>)"
    using \<sigma>_assm fltrace_TickRT_end_exists by blast
  have "\<And>\<rho>. fl2rtm_trace \<sigma>' = \<rho> @\<^sub>\<R>\<^sub>\<T> \<langle>\<bullet>\<^sub>\<R>\<^sub>\<T>\<rangle>\<^sub>\<R>\<^sub>\<T> @\<^sub>\<R>\<^sub>\<T> RTEmptyTail \<Longrightarrow> Finite_Linear_Model.last \<sigma>' = \<bullet>"
  proof (induct \<sigma>', auto)
    fix x :: "'a rtevent acceptance" and \<rho>
    show "\<langle>acc2maxref x\<rangle>\<^sub>\<R>\<^sub>\<T> = \<rho> @\<^sub>\<R>\<^sub>\<T> \<langle>\<bullet>\<^sub>\<R>\<^sub>\<T>\<rangle>\<^sub>\<R>\<^sub>\<T> @\<^sub>\<R>\<^sub>\<T> RTEmptyTail \<Longrightarrow> x = \<bullet>"
      by (induct \<rho>, auto, metis acc2maxref.simps(2) acceptance.exhaust rtrefusal.distinct(1))
  next
    fix x1a :: "'a rtevent aevent" and \<sigma>' :: "'a rtevent fltrace" and  \<rho>
    assume ind_hyp: "\<And>\<rho>. fl2rtm_trace \<sigma>' = \<rho> @\<^sub>\<R>\<^sub>\<T> \<langle>\<bullet>\<^sub>\<R>\<^sub>\<T>\<rangle>\<^sub>\<R>\<^sub>\<T> @\<^sub>\<R>\<^sub>\<T> RTEmptyTail \<Longrightarrow> Finite_Linear_Model.last \<sigma>' = \<bullet>"
    assume "((acc2maxref (acceptance x1a)) #\<^sub>\<R>\<^sub>\<T> event x1a #\<^sub>\<R>\<^sub>\<T> (fl2rtm_trace \<sigma>')) = \<rho> @\<^sub>\<R>\<^sub>\<T> \<langle>\<bullet>\<^sub>\<R>\<^sub>\<T>\<rangle>\<^sub>\<R>\<^sub>\<T> @\<^sub>\<R>\<^sub>\<T> RTEmptyTail"
    then obtain \<rho>' where "fl2rtm_trace \<sigma>' = \<rho>' @\<^sub>\<R>\<^sub>\<T> \<langle>\<bullet>\<^sub>\<R>\<^sub>\<T>\<rangle>\<^sub>\<R>\<^sub>\<T> @\<^sub>\<R>\<^sub>\<T> RTEmptyTail"
      apply - by (induct \<rho>, auto)
    then show "Finite_Linear_Model.last \<sigma>' = \<bullet>"
      using ind_hyp by blast
  qed
  then have last_\<sigma>'_bullet: "Finite_Linear_Model.last \<sigma>' = \<bullet>"
    by (simp add: \<sigma>'_assms)
  have "tickWF TickRT (\<sigma>' &\<^sub>\<F>\<^sub>\<L> \<langle>(A,TickRT)\<^sub>\<F>\<^sub>\<L>,B\<rangle>\<^sub>\<F>\<^sub>\<L>) \<Longrightarrow> TickRT \<notin>\<^sub>\<F>\<^sub>\<L> A"
    using last_\<sigma>'_bullet apply - by (induct \<sigma>', auto, metis amember.simps(1) tickWF.simps(1))
  then have TickRT_notin_A: "TickRT \<notin>\<^sub>\<F>\<^sub>\<L> A"
    using \<sigma>'_assms \<sigma>_tickWF by blast
  then have "A = \<bullet>"
    using \<sigma>'_assms by (cases A, auto)
  then show "x = \<bullet>\<^sub>\<R>\<^sub>\<T>"
    using \<sigma>'_assms acc2maxref.simps(1) by blast
qed

lemma fl2rtm_RT4:
  assumes "FLTick0 TickRT P"
  shows "RT4 (fl2rtm P)"
  using assms unfolding FLTick0_def RT4_def fl2rtm_def
proof (safe, simp_all)
  fix \<rho> :: "'a rtevent rttrace_init" and x y \<sigma>
  assume \<sigma>_assm: "\<rho> @\<^sub>\<R>\<^sub>\<T> \<langle>x\<rangle>\<^sub>\<R>\<^sub>\<T> @\<^sub>\<R>\<^sub>\<T> TickRT ##\<^sub>\<R>\<^sub>\<T> \<langle>y\<rangle>\<^sub>\<R>\<^sub>\<T> = fl2rtm_trace \<sigma>"
  assume \<sigma>_in_P: "\<sigma> \<in> P"
  assume FLTick0_P: "\<forall>x. x \<in> P \<longrightarrow> tickWF TickRT x"
  have \<sigma>_tickWF: "tickWF TickRT \<sigma>"
    using FLTick0_P \<sigma>_in_P by blast
  then show "x = \<bullet>\<^sub>\<R>\<^sub>\<T>"
    using \<sigma>_assm fltrace_TickRT_end_butlast_bullet by blast
next
  fix \<rho> :: "'a rtevent rttrace_init" and x y \<sigma>
  assume \<sigma>_assm: "\<rho> @\<^sub>\<R>\<^sub>\<T> \<langle>x\<rangle>\<^sub>\<R>\<^sub>\<T> @\<^sub>\<R>\<^sub>\<T> TickRT ##\<^sub>\<R>\<^sub>\<T> \<langle>y\<rangle>\<^sub>\<R>\<^sub>\<T> = fl2rtm_trace \<sigma>"
  assume \<sigma>_in_P: "\<sigma> \<in> P"
  assume FLTick0_P: "\<forall>x. x \<in> P \<longrightarrow> tickWF TickRT x"
  have \<sigma>_tickWF: "tickWF TickRT \<sigma>"
    using FLTick0_P \<sigma>_in_P by blast
  have x_bullet: "x = \<bullet>\<^sub>\<R>\<^sub>\<T>"
    using \<sigma>_assm \<sigma>_tickWF fltrace_TickRT_end_butlast_bullet by blast
  show "\<forall>\<sigma>\<in>P. \<forall>\<rho>'. (\<forall>y. fl2rtm_trace \<sigma> \<noteq> \<rho>' @\<^sub>\<R>\<^sub>\<T> \<langle>\<bullet>\<^sub>\<R>\<^sub>\<T>\<rangle>\<^sub>\<R>\<^sub>\<T> @\<^sub>\<R>\<^sub>\<T> TickRT ##\<^sub>\<R>\<^sub>\<T> \<langle>y\<rangle>\<^sub>\<R>\<^sub>\<T>) \<or>
      \<rho> @\<^sub>\<R>\<^sub>\<T> \<langle>\<bullet>\<^sub>\<R>\<^sub>\<T>\<rangle>\<^sub>\<R>\<^sub>\<T> @\<^sub>\<R>\<^sub>\<T> TickRT ##\<^sub>\<R>\<^sub>\<T> \<langle>[UNIV]\<^sub>\<R>\<^sub>\<T>\<rangle>\<^sub>\<R>\<^sub>\<T> \<noteq> \<rho>' @\<^sub>\<R>\<^sub>\<T> \<langle>\<bullet>\<^sub>\<R>\<^sub>\<T>\<rangle>\<^sub>\<R>\<^sub>\<T> @\<^sub>\<R>\<^sub>\<T> TickRT ##\<^sub>\<R>\<^sub>\<T> \<langle>[UNIV]\<^sub>\<R>\<^sub>\<T>\<rangle>\<^sub>\<R>\<^sub>\<T> \<Longrightarrow>
    \<exists>\<sigma>\<in>P. \<rho> @\<^sub>\<R>\<^sub>\<T> \<langle>\<bullet>\<^sub>\<R>\<^sub>\<T>\<rangle>\<^sub>\<R>\<^sub>\<T> @\<^sub>\<R>\<^sub>\<T> TickRT ##\<^sub>\<R>\<^sub>\<T> \<langle>[UNIV]\<^sub>\<R>\<^sub>\<T>\<rangle>\<^sub>\<R>\<^sub>\<T> = fl2rtm_trace \<sigma>"
    using \<sigma>_assm x_bullet \<sigma>_in_P
    by (erule_tac x=\<sigma> in ballE, erule_tac x=\<rho> in allE, safe, erule_tac x=y in allE, simp_all)
next
  fix \<rho> :: "'a rtevent rttrace_init" and x y \<sigma> \<rho>' ya
  show "\<rho> @\<^sub>\<R>\<^sub>\<T> \<langle>x\<rangle>\<^sub>\<R>\<^sub>\<T> @\<^sub>\<R>\<^sub>\<T> TickRT ##\<^sub>\<R>\<^sub>\<T> \<langle>y\<rangle>\<^sub>\<R>\<^sub>\<T> = \<rho>' @\<^sub>\<R>\<^sub>\<T> \<langle>\<bullet>\<^sub>\<R>\<^sub>\<T>\<rangle>\<^sub>\<R>\<^sub>\<T> @\<^sub>\<R>\<^sub>\<T> TickRT ##\<^sub>\<R>\<^sub>\<T> \<langle>[UNIV]\<^sub>\<R>\<^sub>\<T>\<rangle>\<^sub>\<R>\<^sub>\<T> \<Longrightarrow> x = \<bullet>\<^sub>\<R>\<^sub>\<T>"
    by (induct \<rho> \<rho>' rule:leq_rttrace_init.induct, auto, case_tac \<rho>, auto, case_tac x23, auto, case_tac \<rho>, auto)
next
  fix \<rho> \<rho>' :: "'a rtevent rttrace_init" and x y \<sigma> ya
  assume \<sigma>_assm: "fl2rtm_trace \<sigma> = \<rho>' @\<^sub>\<R>\<^sub>\<T> \<langle>\<bullet>\<^sub>\<R>\<^sub>\<T>\<rangle>\<^sub>\<R>\<^sub>\<T> @\<^sub>\<R>\<^sub>\<T> TickRT ##\<^sub>\<R>\<^sub>\<T> \<langle>ya\<rangle>\<^sub>\<R>\<^sub>\<T>"
  assume \<rho>_\<rho>'_assm: "\<rho> @\<^sub>\<R>\<^sub>\<T> \<langle>x\<rangle>\<^sub>\<R>\<^sub>\<T> @\<^sub>\<R>\<^sub>\<T> TickRT ##\<^sub>\<R>\<^sub>\<T> \<langle>y\<rangle>\<^sub>\<R>\<^sub>\<T> = \<rho>' @\<^sub>\<R>\<^sub>\<T> \<langle>\<bullet>\<^sub>\<R>\<^sub>\<T>\<rangle>\<^sub>\<R>\<^sub>\<T> @\<^sub>\<R>\<^sub>\<T> TickRT ##\<^sub>\<R>\<^sub>\<T> \<langle>[UNIV]\<^sub>\<R>\<^sub>\<T>\<rangle>\<^sub>\<R>\<^sub>\<T>"
  assume \<sigma>_in_P: "\<sigma> \<in> P"
  assume FLTick0_P: "\<forall>x. x \<in> P \<longrightarrow> tickWF TickRT x"
  have \<sigma>_tickWF: "tickWF TickRT \<sigma>"
    using FLTick0_P \<sigma>_in_P by blast
  have "\<rho>' @\<^sub>\<R>\<^sub>\<T> \<langle>\<bullet>\<^sub>\<R>\<^sub>\<T>\<rangle>\<^sub>\<R>\<^sub>\<T> @\<^sub>\<R>\<^sub>\<T> TickRT ##\<^sub>\<R>\<^sub>\<T> \<langle>ya\<rangle>\<^sub>\<R>\<^sub>\<T> = \<rho> @\<^sub>\<R>\<^sub>\<T> \<langle>\<bullet>\<^sub>\<R>\<^sub>\<T>\<rangle>\<^sub>\<R>\<^sub>\<T> @\<^sub>\<R>\<^sub>\<T> TickRT ##\<^sub>\<R>\<^sub>\<T> \<langle>ya\<rangle>\<^sub>\<R>\<^sub>\<T>"
    using \<rho>_\<rho>'_assm apply - apply (induct \<rho> \<rho>' rule:leq_rttrace_init.induct, auto)
    apply (metis rttrace_with_refusal.simps(2) rttrace_with_refusal_eq3)
    using rttrace_with_refusal.elims by blast
  then show "\<forall>\<sigma>\<in>P. \<forall>\<rho>'. (\<forall>y. fl2rtm_trace \<sigma> \<noteq> \<rho>' @\<^sub>\<R>\<^sub>\<T> \<langle>\<bullet>\<^sub>\<R>\<^sub>\<T>\<rangle>\<^sub>\<R>\<^sub>\<T> @\<^sub>\<R>\<^sub>\<T> TickRT ##\<^sub>\<R>\<^sub>\<T> \<langle>y\<rangle>\<^sub>\<R>\<^sub>\<T>) \<or>
      \<rho> @\<^sub>\<R>\<^sub>\<T> \<langle>\<bullet>\<^sub>\<R>\<^sub>\<T>\<rangle>\<^sub>\<R>\<^sub>\<T> @\<^sub>\<R>\<^sub>\<T> TickRT ##\<^sub>\<R>\<^sub>\<T> \<langle>[UNIV]\<^sub>\<R>\<^sub>\<T>\<rangle>\<^sub>\<R>\<^sub>\<T> \<noteq> \<rho>' @\<^sub>\<R>\<^sub>\<T> \<langle>\<bullet>\<^sub>\<R>\<^sub>\<T>\<rangle>\<^sub>\<R>\<^sub>\<T> @\<^sub>\<R>\<^sub>\<T> TickRT ##\<^sub>\<R>\<^sub>\<T> \<langle>[UNIV]\<^sub>\<R>\<^sub>\<T>\<rangle>\<^sub>\<R>\<^sub>\<T> \<Longrightarrow>
    \<exists>\<sigma>\<in>P. \<rho> @\<^sub>\<R>\<^sub>\<T> \<langle>\<bullet>\<^sub>\<R>\<^sub>\<T>\<rangle>\<^sub>\<R>\<^sub>\<T> @\<^sub>\<R>\<^sub>\<T> TickRT ##\<^sub>\<R>\<^sub>\<T> \<langle>[UNIV]\<^sub>\<R>\<^sub>\<T>\<rangle>\<^sub>\<R>\<^sub>\<T> = fl2rtm_trace \<sigma>"
    using \<sigma>_assm  \<sigma>_in_P
    by (erule_tac x=\<sigma> in ballE, erule_tac x=\<rho> in allE, safe, erule_tac x=ya in allE, simp_all)
qed

lemma fl2rtm_RTM:
  assumes "FL0 P" "FL1 P" "FL2 P" "FLTick0 TickRT P"
  shows "RTM (fl2rtm P)"
  unfolding RTM_def
  by (simp add: assms fl2rtm_MRT0 fl2rtm_RT3 fl2rtm_RT4 fl2rtm_RTM1 fl2rtm_RTM2 fl2rtm_rtWF) 

lemma fl2rtm_mono: "P \<sqsubseteq>\<^sub>\<F>\<^sub>\<L> Q \<Longrightarrow> fl2rtm P \<sqsubseteq>\<^sub>\<R>\<^sub>\<T> fl2rtm Q"
  unfolding refinesRT_def fl2rtm_def by (safe, simp_all, blast+)

section \<open>Mapping from RTMax to FL\<close>

fun maxref2acc :: "'e rtrefusal \<Rightarrow> 'e acceptance" where
  "maxref2acc \<bullet>\<^sub>\<R>\<^sub>\<T> = \<bullet>" |
  "maxref2acc [X]\<^sub>\<R>\<^sub>\<T> = [{e. e \<notin> X}]\<^sub>\<F>\<^sub>\<L>"

fun rtm2fl_trace :: "'e rtevent rttrace \<Rightarrow> 'e rtevent fltrace" where
  "rtm2fl_trace \<langle>X\<rangle>\<^sub>\<R>\<^sub>\<T> = \<langle>maxref2acc X\<rangle>\<^sub>\<F>\<^sub>\<L>" |
  "rtm2fl_trace (X #\<^sub>\<R>\<^sub>\<T> EventRT e #\<^sub>\<R>\<^sub>\<T> \<rho>) = ((maxref2acc X, EventRT e)\<^sub>\<F>\<^sub>\<L> #\<^sub>\<F>\<^sub>\<L> rtm2fl_trace \<rho>)" |
  "rtm2fl_trace (X #\<^sub>\<R>\<^sub>\<T> TickRT #\<^sub>\<R>\<^sub>\<T> \<rho>) = ((maxref2acc X, TickRT)\<^sub>\<F>\<^sub>\<L> #\<^sub>\<F>\<^sub>\<L> \<langle>\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>)"

definition rtm2fl :: "'e rtevent rtprocess \<Rightarrow> 'e rtevent fltraces" where
  "rtm2fl P = {rtm2fl_trace x |x. x \<in> P }"

lemma rtm2fl_FL0:
  assumes "MRT0 P"
  shows "FL0 (rtm2fl P)"
  using assms unfolding MRT0_def FL0_def rtm2fl_def by auto

lemma rtm2fl_FL1:
  assumes "RTM1 P" "\<forall>x\<in>P. rtWF x"
  shows "FL1 (rtm2fl P)"
  using assms unfolding RTM1_def FL1_def rtm2fl_def
proof auto
  fix x :: "'e rtevent rttrace"
  show "\<And>P s. \<forall>\<rho>. (\<exists>\<sigma>. \<sigma> \<in> P \<and> \<rho> \<le>\<^sub>\<R>\<^sub>\<T>\<^sub>\<M> \<sigma>) \<longrightarrow> \<rho> \<in> P \<Longrightarrow> \<forall>x\<in>P. rtWF x \<Longrightarrow> s \<le> rtm2fl_trace x \<Longrightarrow> x \<in> P \<Longrightarrow> \<exists>x. s = rtm2fl_trace x \<and> x \<in> P"
  proof (induct x, auto)
    fix P :: "'e rtevent rtprocess" and x s
    show "\<forall>\<rho>. (\<exists>\<sigma>. \<sigma> \<in> P \<and> \<rho> \<le>\<^sub>\<R>\<^sub>\<T>\<^sub>\<M> \<sigma>) \<longrightarrow> \<rho> \<in> P \<Longrightarrow> s \<le> \<langle>maxref2acc x\<rangle>\<^sub>\<F>\<^sub>\<L> \<Longrightarrow> \<langle>x\<rangle>\<^sub>\<R>\<^sub>\<T> \<in> P \<Longrightarrow> \<exists>x. s = rtm2fl_trace x \<and> x \<in> P"
      by (metis fltrace.exhaust leq_rttrace_max.simps(1) less_eq_acceptance.elims(2) less_eq_fltrace.simps(1) less_eq_fltrace.simps(4) maxref2acc.simps(1) rtm2fl_trace.simps(1))
  next
    fix P :: "'e rtevent rtprocess" and x :: "'e rtevent rttrace" and x1a x2 s
    assume ind_hyp: "\<And>P s. \<forall>\<rho>. (\<exists>\<sigma>. \<sigma> \<in> P \<and> \<rho> \<le>\<^sub>\<R>\<^sub>\<T>\<^sub>\<M> \<sigma>) \<longrightarrow> \<rho> \<in> P \<Longrightarrow> \<forall>x\<in>P. rtWF x \<Longrightarrow> s \<le> rtm2fl_trace x \<Longrightarrow> x \<in> P
        \<Longrightarrow> \<exists>x. s = rtm2fl_trace x \<and> x \<in> P"
    assume case_assms: "\<forall>\<rho>. (\<exists>\<sigma>. \<sigma> \<in> P \<and> \<rho> \<le>\<^sub>\<R>\<^sub>\<T>\<^sub>\<M> \<sigma>) \<longrightarrow> \<rho> \<in> P" "\<forall>x\<in>P. rtWF x"
      "s \<le> rtm2fl_trace (x1a #\<^sub>\<R>\<^sub>\<T> x2 #\<^sub>\<R>\<^sub>\<T> x)" "(x1a #\<^sub>\<R>\<^sub>\<T> x2 #\<^sub>\<R>\<^sub>\<T> x) \<in> P"
    have 1: "\<forall>\<rho>. (\<exists>\<sigma>. \<sigma> \<in> {x. (x1a #\<^sub>\<R>\<^sub>\<T> x2 #\<^sub>\<R>\<^sub>\<T> x) \<in> P} \<and> \<rho> \<le>\<^sub>\<R>\<^sub>\<T>\<^sub>\<M> \<sigma>) \<longrightarrow> \<rho> \<in> {x. (x1a #\<^sub>\<R>\<^sub>\<T> x2 #\<^sub>\<R>\<^sub>\<T> x) \<in> P}"
      by (metis (mono_tags) RTM1_def RTM1_init_event case_assms(1))
    have x1a_x2_assms1: "\<not> x2 \<in>\<^sub>\<R>\<^sub>\<T> x1a"
      using case_assms(2) case_assms(4) by auto
    then have x1a_x2_assms2: "x2 \<in>\<^sub>\<F>\<^sub>\<L> maxref2acc x1a \<or> maxref2acc x1a = \<bullet>"
      by (metis (no_types, lifting) acceptance.inject amember.elims(3) in_rtrefusal.elims(3) maxref2acc.simps(1) maxref2acc.simps(2) mem_Collect_eq)
    have 2: "\<forall>t\<in>{t. (x1a #\<^sub>\<R>\<^sub>\<T> x2 #\<^sub>\<R>\<^sub>\<T> t) \<in> P}. rtWF t"
      using case_assms(2) by auto
    have "(\<exists>s'. s = (maxref2acc x1a, x2)\<^sub>\<F>\<^sub>\<L> #\<^sub>\<F>\<^sub>\<L> s') \<or> (\<exists>s'. s = (\<bullet>, x2)\<^sub>\<F>\<^sub>\<L> #\<^sub>\<F>\<^sub>\<L> s') \<or> s = \<langle>maxref2acc x1a\<rangle>\<^sub>\<F>\<^sub>\<L> \<or> s = \<langle>\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>"
      using case_assms(3) apply -
    proof (induct s, auto)
      fix xa
      assume "\<langle>xa\<rangle>\<^sub>\<F>\<^sub>\<L> \<le> rtm2fl_trace (x1a #\<^sub>\<R>\<^sub>\<T> x2 #\<^sub>\<R>\<^sub>\<T> x)"
      then have "\<langle>xa\<rangle>\<^sub>\<F>\<^sub>\<L> \<le> (maxref2acc x1a, x2)\<^sub>\<F>\<^sub>\<L> #\<^sub>\<F>\<^sub>\<L> rtm2fl_trace x"
        by (cases x2, auto)        
      then have "xa \<le> maxref2acc x1a"
        by (simp add: x1a_x2_assms2)
      then show "xa \<noteq> \<bullet> \<Longrightarrow> xa = maxref2acc x1a"
        using less_eq_acceptance.elims(2) by fastforce
    next
      fix x1aa s
      assume ind_hyp: "s \<le> rtm2fl_trace (x1a #\<^sub>\<R>\<^sub>\<T> x2 #\<^sub>\<R>\<^sub>\<T> x) \<Longrightarrow>
        (\<exists>s'. s = (maxref2acc x1a,x2)\<^sub>\<F>\<^sub>\<L> #\<^sub>\<F>\<^sub>\<L> s') \<or> (\<exists>s'. s = (\<bullet>,x2)\<^sub>\<F>\<^sub>\<L> #\<^sub>\<F>\<^sub>\<L> s') \<or> s = \<langle>maxref2acc x1a\<rangle>\<^sub>\<F>\<^sub>\<L> \<or> s = \<langle>\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>"
      show "x1aa #\<^sub>\<F>\<^sub>\<L> s \<le> rtm2fl_trace (x1a #\<^sub>\<R>\<^sub>\<T> x2 #\<^sub>\<R>\<^sub>\<T> x) \<Longrightarrow> x1aa \<noteq> (\<bullet>,x2)\<^sub>\<F>\<^sub>\<L> \<Longrightarrow> x1aa = (maxref2acc x1a,x2)\<^sub>\<F>\<^sub>\<L>"
        using aevent_less_eq_iff_components x1a_x2_assms2 by (cases x2, auto, fastforce+)
    qed
    then show "\<exists>x. s = rtm2fl_trace x \<and> x \<in> P"
    proof auto
      fix s'
      assume case_assm2: "s = (maxref2acc x1a,x2)\<^sub>\<F>\<^sub>\<L> #\<^sub>\<F>\<^sub>\<L> s'"
      have 3: "s' \<le> rtm2fl_trace x"
        using case_assms(3) case_assm2 apply auto apply (cases x2, auto, cases x, auto)
        using prefixFL_induct2 by fastforce+
      have 4: "x \<in> {x. (x1a #\<^sub>\<R>\<^sub>\<T> x2 #\<^sub>\<R>\<^sub>\<T> x) \<in> P}"
        using case_assms(4) by blast
      have "\<exists>x. s' = rtm2fl_trace x \<and> x \<in> {x. (x1a #\<^sub>\<R>\<^sub>\<T> x2 #\<^sub>\<R>\<^sub>\<T> x) \<in> P}"
        using 1 2 3 4 ind_hyp by blast
      then show "\<exists>x. (maxref2acc x1a,x2)\<^sub>\<F>\<^sub>\<L> #\<^sub>\<F>\<^sub>\<L> s' = rtm2fl_trace x \<and> x \<in> P"
        apply auto apply (rule_tac x="x1a #\<^sub>\<R>\<^sub>\<T> x2 #\<^sub>\<R>\<^sub>\<T> x" in exI, auto, cases x2, auto)
        by (metis FL_concat_equiv antisym_conv case_assm2 case_assms(3) fltrace.inject(2) rtm2fl_trace.simps(3) x_le_x_concat2)
    next
      fix s'
      assume case_assm2: "s = (\<bullet>,x2)\<^sub>\<F>\<^sub>\<L> #\<^sub>\<F>\<^sub>\<L> s'"
      have 1: "\<forall>\<rho>. (\<exists>\<sigma>. \<sigma> \<in> {x. (\<bullet>\<^sub>\<R>\<^sub>\<T> #\<^sub>\<R>\<^sub>\<T> x2 #\<^sub>\<R>\<^sub>\<T> x) \<in> P} \<and> \<rho> \<le>\<^sub>\<R>\<^sub>\<T>\<^sub>\<M> \<sigma>) \<longrightarrow> \<rho> \<in> {x. (\<bullet>\<^sub>\<R>\<^sub>\<T> #\<^sub>\<R>\<^sub>\<T> x2 #\<^sub>\<R>\<^sub>\<T> x) \<in> P}"
        by (metis (mono_tags) RTM1_def RTM1_init_event case_assms(1))
      have 2: "\<forall>t\<in>{t. (\<bullet>\<^sub>\<R>\<^sub>\<T> #\<^sub>\<R>\<^sub>\<T> x2 #\<^sub>\<R>\<^sub>\<T> t) \<in> P}. rtWF t"
        using case_assms(2) by auto
      have 3: "s' \<le> rtm2fl_trace x"
        using case_assms(3) case_assm2 apply auto apply (cases x2, auto, cases x, auto)
        by (simp add: fltrace_trans, metis fltrace_trans prefixFL_induct21)
      have "(\<bullet>\<^sub>\<R>\<^sub>\<T> #\<^sub>\<R>\<^sub>\<T> x2 #\<^sub>\<R>\<^sub>\<T> x) \<le>\<^sub>\<R>\<^sub>\<T>\<^sub>\<M> (x1a #\<^sub>\<R>\<^sub>\<T> x2 #\<^sub>\<R>\<^sub>\<T> x)"
        by (cases x1a, auto simp add: leq_rttrace_max_refl)
      then have 4: "x \<in> {x. (\<bullet>\<^sub>\<R>\<^sub>\<T> #\<^sub>\<R>\<^sub>\<T> x2 #\<^sub>\<R>\<^sub>\<T> x) \<in> P}"
        using case_assms(1) case_assms(4) by blast
      have "\<exists>x. s' = rtm2fl_trace x \<and> x \<in> {x. (\<bullet>\<^sub>\<R>\<^sub>\<T> #\<^sub>\<R>\<^sub>\<T> x2 #\<^sub>\<R>\<^sub>\<T> x) \<in> P}"
        using 1 2 3 4 ind_hyp[where P="{x. (\<bullet>\<^sub>\<R>\<^sub>\<T> #\<^sub>\<R>\<^sub>\<T> x2 #\<^sub>\<R>\<^sub>\<T> x) \<in> P}", where s=s'] by force
      then show "\<exists>x. (\<bullet>,x2)\<^sub>\<F>\<^sub>\<L> #\<^sub>\<F>\<^sub>\<L> s' = rtm2fl_trace x \<and> x \<in> P"
        apply (auto, rule_tac x="\<bullet>\<^sub>\<R>\<^sub>\<T> #\<^sub>\<R>\<^sub>\<T> x2 #\<^sub>\<R>\<^sub>\<T> x" in exI, auto, cases x2, auto)
        by (metis FL_concat_equiv case_assm2 case_assms(3) dual_order.antisym less_eq_fltrace.simps(3) rtm2fl_trace.simps(3) x_le_x_concat2)
    next
      show "s = \<langle>maxref2acc x1a\<rangle>\<^sub>\<F>\<^sub>\<L> \<Longrightarrow> \<exists>x. \<langle>maxref2acc x1a\<rangle>\<^sub>\<F>\<^sub>\<L> = rtm2fl_trace x \<and> x \<in> P"
        by (metis case_assms(1) case_assms(4) leq_rttrace_max.simps(1) leq_rttrace_max.simps(4) rtm2fl_trace.simps(1) rtrefusal.exhaust)
    next
      show "s = \<langle>\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L> \<Longrightarrow> \<exists>x. \<langle>\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L> = rtm2fl_trace x \<and> x \<in> P"
        by (metis case_assms(1) case_assms(4) leq_rttrace_max.simps(1) maxref2acc.simps(1) rtm2fl_trace.simps(1))
    qed
  qed
qed

thm FL2_def
thm RT4_def

lemma rtm2fl_trace_aevent_prefix:
  "rtWF x \<Longrightarrow> a #\<^sub>\<F>\<^sub>\<L> \<rho> = rtm2fl_trace x \<Longrightarrow> 
    \<exists> x'. x = ((acc2maxref (acceptance a)) #\<^sub>\<R>\<^sub>\<T> (event a) #\<^sub>\<R>\<^sub>\<T> x') \<and> (rtm2fl_trace x' = \<rho> \<or> event a = TickRT)"
proof (induct x, auto)
  fix x1a x2 x
  show "a #\<^sub>\<F>\<^sub>\<L> \<rho> = rtm2fl_trace (x1a #\<^sub>\<R>\<^sub>\<T> x2 #\<^sub>\<R>\<^sub>\<T> x) \<Longrightarrow> \<not> x2 \<in>\<^sub>\<R>\<^sub>\<T> x1a \<Longrightarrow> x1a = acc2maxref (acceptance a)"
    by (cases x2, auto, (cases x1a, auto)+)
next
  fix x1a x2 x
  show "a #\<^sub>\<F>\<^sub>\<L> \<rho> = rtm2fl_trace (x1a #\<^sub>\<R>\<^sub>\<T> x2 #\<^sub>\<R>\<^sub>\<T> x) \<Longrightarrow> \<not> x2 \<in>\<^sub>\<R>\<^sub>\<T> x1a \<Longrightarrow> rtWF x \<Longrightarrow> x2 = event a"
    by (cases x2, auto, (cases x1a, auto)+)
next
  fix x1a x2 x
  show "a #\<^sub>\<F>\<^sub>\<L> \<rho> = rtm2fl_trace (x1a #\<^sub>\<R>\<^sub>\<T> x2 #\<^sub>\<R>\<^sub>\<T> x) \<Longrightarrow> \<not> x2 \<in>\<^sub>\<R>\<^sub>\<T> x1a \<Longrightarrow> event a \<noteq> TickRT \<Longrightarrow> rtm2fl_trace x = \<rho>"
    by (cases x2, auto, cases x1a, auto)
qed

lemma rtmfl_trace_acceptance: "\<langle>A\<rangle>\<^sub>\<F>\<^sub>\<L> = rtm2fl_trace x \<Longrightarrow> x = \<langle>acc2maxref A\<rangle>\<^sub>\<R>\<^sub>\<T>"
  by (cases x, auto, case_tac x1, auto, case_tac x22, auto)

lemma rtm2fl_trace_fltrace_concat2_acceptance: 
  "\<And>x. rtWF x \<Longrightarrow> \<beta> &\<^sub>\<F>\<^sub>\<L> \<langle>[A]\<^sub>\<F>\<^sub>\<L>\<rangle>\<^sub>\<F>\<^sub>\<L> = rtm2fl_trace x \<Longrightarrow>
    \<exists> x' X. x = x' @\<^sub>\<R>\<^sub>\<T> \<langle>X\<rangle>\<^sub>\<R>\<^sub>\<T> @\<^sub>\<R>\<^sub>\<T> RTEmptyTail \<and> X = acc2maxref (last \<beta> + [A]\<^sub>\<F>\<^sub>\<L>)"
proof (induct \<beta>, auto)
  fix x xa
  show "rtWF xa \<Longrightarrow> \<langle>x + [A]\<^sub>\<F>\<^sub>\<L>\<rangle>\<^sub>\<F>\<^sub>\<L> = rtm2fl_trace xa \<Longrightarrow> \<exists>x'. xa = x' @\<^sub>\<R>\<^sub>\<T> \<langle>acc2maxref (x + [A]\<^sub>\<F>\<^sub>\<L>)\<rangle>\<^sub>\<R>\<^sub>\<T> @\<^sub>\<R>\<^sub>\<T> RTEmptyTail"
    by (metis rtmfl_trace_acceptance rttrace_with_refusal.simps(3))
next
  fix x1a \<beta> x
  assume ind_hyp: "\<And>x. rtWF x \<Longrightarrow> \<beta> &\<^sub>\<F>\<^sub>\<L> \<langle>[A]\<^sub>\<F>\<^sub>\<L>\<rangle>\<^sub>\<F>\<^sub>\<L> = rtm2fl_trace x \<Longrightarrow>
    \<exists>x'. x = x' @\<^sub>\<R>\<^sub>\<T> \<langle>acc2maxref (Finite_Linear_Model.last \<beta> + [A]\<^sub>\<F>\<^sub>\<L>)\<rangle>\<^sub>\<R>\<^sub>\<T> @\<^sub>\<R>\<^sub>\<T> RTEmptyTail"
  assume case_assms: "rtWF x" "x1a #\<^sub>\<F>\<^sub>\<L> (\<beta> &\<^sub>\<F>\<^sub>\<L> \<langle>[A]\<^sub>\<F>\<^sub>\<L>\<rangle>\<^sub>\<F>\<^sub>\<L>) = rtm2fl_trace x"
  
  obtain x' where x_def: "x = ((acc2maxref (acceptance x1a)) #\<^sub>\<R>\<^sub>\<T> (event x1a) #\<^sub>\<R>\<^sub>\<T> x')"
      using case_assms rtm2fl_trace_aevent_prefix by blast
  then have "rtm2fl_trace x' = \<beta> &\<^sub>\<F>\<^sub>\<L> \<langle>[A]\<^sub>\<F>\<^sub>\<L>\<rangle>\<^sub>\<F>\<^sub>\<L> \<and> rtWF x'"
    using case_assms by (cases "event x1a", auto, cases \<beta>, auto, case_tac x1, auto)
  then have "\<exists>x''. x' = x'' @\<^sub>\<R>\<^sub>\<T> \<langle>acc2maxref (Finite_Linear_Model.last \<beta> + [A]\<^sub>\<F>\<^sub>\<L>)\<rangle>\<^sub>\<R>\<^sub>\<T> @\<^sub>\<R>\<^sub>\<T> RTEmptyTail"
    by (simp add: ind_hyp)
  then show "\<exists>x'. x = x' @\<^sub>\<R>\<^sub>\<T> \<langle>acc2maxref (Finite_Linear_Model.last \<beta> + [A]\<^sub>\<F>\<^sub>\<L>)\<rangle>\<^sub>\<R>\<^sub>\<T> @\<^sub>\<R>\<^sub>\<T> RTEmptyTail"
    by (metis rttrace_with_refusal.simps(1) x_def)
qed

lemma rtm2fl_FL2:
  assumes "\<forall>x\<in>P. rtWF x" "RTM2 P"
  shows "FL2 (rtm2fl P)"
  using assms unfolding RTM1_def RTM2_def FL2_def rtm2fl_def
proof auto
  fix \<beta> A a x
  assume P_wf: "\<forall>x\<in>P. rtWF x"
  assume RTM2_P: "\<forall>\<rho> X e. \<rho> @\<^sub>\<R>\<^sub>\<T> \<langle>[X]\<^sub>\<R>\<^sub>\<T>\<rangle>\<^sub>\<R>\<^sub>\<T> @\<^sub>\<R>\<^sub>\<T> RTEmptyTail \<in> P \<and> e \<notin> X \<longrightarrow> \<rho> @\<^sub>\<R>\<^sub>\<T> \<langle>[X]\<^sub>\<R>\<^sub>\<T>\<rangle>\<^sub>\<R>\<^sub>\<T> @\<^sub>\<R>\<^sub>\<T> e ##\<^sub>\<R>\<^sub>\<T> \<langle>\<bullet>\<^sub>\<R>\<^sub>\<T>\<rangle>\<^sub>\<R>\<^sub>\<T> \<in> P"
  assume x_in_P: "x \<in> P"
  assume rtm2fl_trace_x_is_\<beta>_A: "\<beta> &\<^sub>\<F>\<^sub>\<L> \<langle>A\<rangle>\<^sub>\<F>\<^sub>\<L> = rtm2fl_trace x"
  assume a_in_A: "a \<in>\<^sub>\<F>\<^sub>\<L> A"

  obtain A' where A_not_bullet: "A = [A']\<^sub>\<F>\<^sub>\<L>"
    by (meson a_in_A amember.elims(2))

  obtain x' X where x'_X_def: "x = x' @\<^sub>\<R>\<^sub>\<T> \<langle>X\<rangle>\<^sub>\<R>\<^sub>\<T> @\<^sub>\<R>\<^sub>\<T> RTEmptyTail \<and> X = acc2maxref (last \<beta> + [A']\<^sub>\<F>\<^sub>\<L>)"
    using A_not_bullet P_wf rtm2fl_trace_fltrace_concat2_acceptance rtm2fl_trace_x_is_\<beta>_A x_in_P by blast

  show "\<exists>x. \<beta> &\<^sub>\<F>\<^sub>\<L> \<langle>(A,a)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L> = rtm2fl_trace x \<and> x \<in> P"
  proof (cases "last \<beta>")
    assume last_\<beta>_bullet: "last \<beta> = \<bullet>"
    then have X_def: "X = [{e. e \<notin> A'}]\<^sub>\<R>\<^sub>\<T>"
      by (simp add: x'_X_def)
    then have "x' @\<^sub>\<R>\<^sub>\<T> \<langle>[{e. e \<notin> A'}]\<^sub>\<R>\<^sub>\<T>\<rangle>\<^sub>\<R>\<^sub>\<T> @\<^sub>\<R>\<^sub>\<T> a ##\<^sub>\<R>\<^sub>\<T> \<langle>\<bullet>\<^sub>\<R>\<^sub>\<T>\<rangle>\<^sub>\<R>\<^sub>\<T> \<in> P"
      using A_not_bullet RTM2_P a_in_A x'_X_def x_in_P by auto
    then show "\<exists>x. \<beta> &\<^sub>\<F>\<^sub>\<L> \<langle>(A,a)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L> = rtm2fl_trace x \<and> x \<in> P"
    proof (rule_tac x="x' @\<^sub>\<R>\<^sub>\<T> \<langle>[{e. e \<notin> A'}]\<^sub>\<R>\<^sub>\<T>\<rangle>\<^sub>\<R>\<^sub>\<T> @\<^sub>\<R>\<^sub>\<T> a ##\<^sub>\<R>\<^sub>\<T> \<langle>\<bullet>\<^sub>\<R>\<^sub>\<T>\<rangle>\<^sub>\<R>\<^sub>\<T>" in exI, auto)
      have "\<And> x'. rtWF (x' @\<^sub>\<R>\<^sub>\<T> \<langle>[{e. e \<notin> A'}]\<^sub>\<R>\<^sub>\<T>\<rangle>\<^sub>\<R>\<^sub>\<T> @\<^sub>\<R>\<^sub>\<T> RTEmptyTail) \<Longrightarrow> last \<beta> = \<bullet> \<Longrightarrow> \<beta> &\<^sub>\<F>\<^sub>\<L> \<langle>A\<rangle>\<^sub>\<F>\<^sub>\<L> = rtm2fl_trace (x' @\<^sub>\<R>\<^sub>\<T> \<langle>[{e. e \<notin> A'}]\<^sub>\<R>\<^sub>\<T>\<rangle>\<^sub>\<R>\<^sub>\<T> @\<^sub>\<R>\<^sub>\<T> RTEmptyTail) \<Longrightarrow>
        \<beta> &\<^sub>\<F>\<^sub>\<L> \<langle>(A,a)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L> = rtm2fl_trace (x' @\<^sub>\<R>\<^sub>\<T> \<langle>[{e. e \<notin> A'}]\<^sub>\<R>\<^sub>\<T>\<rangle>\<^sub>\<R>\<^sub>\<T> @\<^sub>\<R>\<^sub>\<T> a ##\<^sub>\<R>\<^sub>\<T> \<langle>\<bullet>\<^sub>\<R>\<^sub>\<T>\<rangle>\<^sub>\<R>\<^sub>\<T>)"
      proof (induct \<beta>, auto)
        fix x'
        show "\<langle>A\<rangle>\<^sub>\<F>\<^sub>\<L> = rtm2fl_trace (x' @\<^sub>\<R>\<^sub>\<T> \<langle>[{e. e \<notin> A'}]\<^sub>\<R>\<^sub>\<T>\<rangle>\<^sub>\<R>\<^sub>\<T> @\<^sub>\<R>\<^sub>\<T> RTEmptyTail) \<Longrightarrow>
            \<langle>(A,a)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L> = rtm2fl_trace (x' @\<^sub>\<R>\<^sub>\<T> \<langle>[{e. e \<notin> A'}]\<^sub>\<R>\<^sub>\<T>\<rangle>\<^sub>\<R>\<^sub>\<T> @\<^sub>\<R>\<^sub>\<T> a ##\<^sub>\<R>\<^sub>\<T> \<langle>\<bullet>\<^sub>\<R>\<^sub>\<T>\<rangle>\<^sub>\<R>\<^sub>\<T>)"
          by (case_tac x', auto, cases a, auto, case_tac x22, auto)
      next
        fix x1a \<beta> x'
        assume ind_hyp: "\<And>x'. rtWF (x' @\<^sub>\<R>\<^sub>\<T> \<langle>[{e. e \<notin> A'}]\<^sub>\<R>\<^sub>\<T>\<rangle>\<^sub>\<R>\<^sub>\<T> @\<^sub>\<R>\<^sub>\<T> RTEmptyTail) \<Longrightarrow>
                \<beta> &\<^sub>\<F>\<^sub>\<L> \<langle>A\<rangle>\<^sub>\<F>\<^sub>\<L> = rtm2fl_trace (x' @\<^sub>\<R>\<^sub>\<T> \<langle>[{e. e \<notin> A'}]\<^sub>\<R>\<^sub>\<T>\<rangle>\<^sub>\<R>\<^sub>\<T> @\<^sub>\<R>\<^sub>\<T> RTEmptyTail) \<Longrightarrow>
              \<beta> &\<^sub>\<F>\<^sub>\<L> \<langle>(A,a)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L> = rtm2fl_trace (x' @\<^sub>\<R>\<^sub>\<T> \<langle>[{e. e \<notin> A'}]\<^sub>\<R>\<^sub>\<T>\<rangle>\<^sub>\<R>\<^sub>\<T> @\<^sub>\<R>\<^sub>\<T> a ##\<^sub>\<R>\<^sub>\<T> \<langle>\<bullet>\<^sub>\<R>\<^sub>\<T>\<rangle>\<^sub>\<R>\<^sub>\<T>)"
        assume case_assm1: "x1a #\<^sub>\<F>\<^sub>\<L> (\<beta> &\<^sub>\<F>\<^sub>\<L> \<langle>A\<rangle>\<^sub>\<F>\<^sub>\<L>) = rtm2fl_trace (x' @\<^sub>\<R>\<^sub>\<T> \<langle>[{e. e \<notin> A'}]\<^sub>\<R>\<^sub>\<T>\<rangle>\<^sub>\<R>\<^sub>\<T> @\<^sub>\<R>\<^sub>\<T> RTEmptyTail)"
        assume case_assm2: "rtWF (x' @\<^sub>\<R>\<^sub>\<T> \<langle>[{e. e \<notin> A'}]\<^sub>\<R>\<^sub>\<T>\<rangle>\<^sub>\<R>\<^sub>\<T> @\<^sub>\<R>\<^sub>\<T> RTEmptyTail)"
        have "\<exists> x''. x' @\<^sub>\<R>\<^sub>\<T> \<langle>[{e. e \<notin> A'}]\<^sub>\<R>\<^sub>\<T>\<rangle>\<^sub>\<R>\<^sub>\<T> @\<^sub>\<R>\<^sub>\<T> RTEmptyTail = ((acc2maxref (acceptance x1a)) #\<^sub>\<R>\<^sub>\<T> event x1a #\<^sub>\<R>\<^sub>\<T> x'') \<and>
          (rtm2fl_trace x'' = \<beta> &\<^sub>\<F>\<^sub>\<L> \<langle>A\<rangle>\<^sub>\<F>\<^sub>\<L> \<or> event x1a = TickRT)"
          using case_assm1 case_assm2 rtm2fl_trace_aevent_prefix by blast
        then obtain x'' where x''_assms: "x' @\<^sub>\<R>\<^sub>\<T> \<langle>[{e. e \<notin> A'}]\<^sub>\<R>\<^sub>\<T>\<rangle>\<^sub>\<R>\<^sub>\<T> @\<^sub>\<R>\<^sub>\<T> RTEmptyTail = ((acc2maxref (acceptance x1a)) #\<^sub>\<R>\<^sub>\<T> event x1a #\<^sub>\<R>\<^sub>\<T> x'') \<and>
          rtm2fl_trace x'' = \<beta> &\<^sub>\<F>\<^sub>\<L> \<langle>A\<rangle>\<^sub>\<F>\<^sub>\<L> \<and> event x1a \<noteq> TickRT"
          by (metis A_not_bullet Finite_Linear_Model.last.simps(2) case_assm1 last_cons_acceptance_not_bullet last_fltrace_acceptance rtm2fl_trace.simps(3))
        then obtain x''' where x'''_assms: "rtWF (x''' @\<^sub>\<R>\<^sub>\<T> \<langle>[{e. e \<notin> A'}]\<^sub>\<R>\<^sub>\<T>\<rangle>\<^sub>\<R>\<^sub>\<T> @\<^sub>\<R>\<^sub>\<T> RTEmptyTail)
          \<and> \<beta> &\<^sub>\<F>\<^sub>\<L> \<langle>A\<rangle>\<^sub>\<F>\<^sub>\<L> = rtm2fl_trace (x''' @\<^sub>\<R>\<^sub>\<T> \<langle>[{e. e \<notin> A'}]\<^sub>\<R>\<^sub>\<T>\<rangle>\<^sub>\<R>\<^sub>\<T> @\<^sub>\<R>\<^sub>\<T> RTEmptyTail)
          \<and> x'' =  x''' @\<^sub>\<R>\<^sub>\<T> \<langle>[{e. e \<notin> A'}]\<^sub>\<R>\<^sub>\<T>\<rangle>\<^sub>\<R>\<^sub>\<T> @\<^sub>\<R>\<^sub>\<T> RTEmptyTail "
          using case_assm2 apply (auto) apply (cases x1a, auto)
          apply (smt A_not_bullet rtm2fl_trace_fltrace_concat2_acceptance rttrace_with_refusal.simps(1) rttrace_with_refusal_eq2)
          by (cases x', auto, fastforce)
        then have 1: "\<beta> &\<^sub>\<F>\<^sub>\<L> \<langle>(A,a)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L> = rtm2fl_trace (x''' @\<^sub>\<R>\<^sub>\<T> \<langle>[{e. e \<notin> A'}]\<^sub>\<R>\<^sub>\<T>\<rangle>\<^sub>\<R>\<^sub>\<T> @\<^sub>\<R>\<^sub>\<T> a ##\<^sub>\<R>\<^sub>\<T> \<langle>\<bullet>\<^sub>\<R>\<^sub>\<T>\<rangle>\<^sub>\<R>\<^sub>\<T>)"
          by (simp add: ind_hyp)
        then show "x1a #\<^sub>\<F>\<^sub>\<L> (\<beta> &\<^sub>\<F>\<^sub>\<L> \<langle>(A,a)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>) = rtm2fl_trace (x' @\<^sub>\<R>\<^sub>\<T> \<langle>[{e. e \<notin> A'}]\<^sub>\<R>\<^sub>\<T>\<rangle>\<^sub>\<R>\<^sub>\<T> @\<^sub>\<R>\<^sub>\<T> a ##\<^sub>\<R>\<^sub>\<T> \<langle>\<bullet>\<^sub>\<R>\<^sub>\<T>\<rangle>\<^sub>\<R>\<^sub>\<T>)"
          (is "?lhs = ?rhs")
        proof -
          have "?rhs = rtm2fl_trace ((acc2maxref (acceptance x1a)) #\<^sub>\<R>\<^sub>\<T> event x1a #\<^sub>\<R>\<^sub>\<T> (x''' @\<^sub>\<R>\<^sub>\<T> \<langle>[{e. e \<notin> A'}]\<^sub>\<R>\<^sub>\<T>\<rangle>\<^sub>\<R>\<^sub>\<T> @\<^sub>\<R>\<^sub>\<T> a ##\<^sub>\<R>\<^sub>\<T> \<langle>\<bullet>\<^sub>\<R>\<^sub>\<T>\<rangle>\<^sub>\<R>\<^sub>\<T>))"
            by (metis rttrace_with_refusal.simps(1) rttrace_with_refusal_eq1 x'''_assms x''_assms)
          also have "... = x1a #\<^sub>\<F>\<^sub>\<L> rtm2fl_trace (x''' @\<^sub>\<R>\<^sub>\<T> \<langle>[{e. e \<notin> A'}]\<^sub>\<R>\<^sub>\<T>\<rangle>\<^sub>\<R>\<^sub>\<T> @\<^sub>\<R>\<^sub>\<T> a ##\<^sub>\<R>\<^sub>\<T> \<langle>\<bullet>\<^sub>\<R>\<^sub>\<T>\<rangle>\<^sub>\<R>\<^sub>\<T>)"
            by (metis case_assm1 fltrace.inject(2) rtevent.exhaust rtm2fl_trace.simps(2) x''_assms)
          also have "... = ?lhs"
            using "1" by auto
          then show ?thesis
            using calculation by auto
        qed
      qed
      then show "\<beta> &\<^sub>\<F>\<^sub>\<L> \<langle>(A,a)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L> = rtm2fl_trace (x' @\<^sub>\<R>\<^sub>\<T> \<langle>[{e. e \<notin> A'}]\<^sub>\<R>\<^sub>\<T>\<rangle>\<^sub>\<R>\<^sub>\<T> @\<^sub>\<R>\<^sub>\<T> a ##\<^sub>\<R>\<^sub>\<T> \<langle>\<bullet>\<^sub>\<R>\<^sub>\<T>\<rangle>\<^sub>\<R>\<^sub>\<T>)"
        using P_wf X_def last_\<beta>_bullet rtm2fl_trace_x_is_\<beta>_A x'_X_def x_in_P by blast
    qed
  next
    fix x2
    assume last_beta_not_bullet: "last \<beta> = [x2]\<^sub>\<F>\<^sub>\<L>"
    have 1: "\<beta> &\<^sub>\<F>\<^sub>\<L> \<langle>A\<rangle>\<^sub>\<F>\<^sub>\<L> = \<beta>"
      using last_beta_not_bullet by (induct \<beta>, auto simp add: A_not_bullet)
    have 2:  "\<beta> &\<^sub>\<F>\<^sub>\<L> \<langle>(A,a)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L> = \<beta>"
      using last_beta_not_bullet by (induct \<beta>, auto simp add: A_not_bullet)
    show "\<exists>x. \<beta> &\<^sub>\<F>\<^sub>\<L> \<langle>(A,a)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L> = rtm2fl_trace x \<and> x \<in> P"
      using 1 2 rtm2fl_trace_x_is_\<beta>_A x_in_P by auto
  qed
qed

lemma rtm2fl_FLTick0:
  assumes "\<forall>x\<in>P. rtWF x" "RTM1 P" "RTM2 P" "RT3 P" "RT4 P"
  shows "FLTick0 TickRT (rtm2fl P)"
  using assms unfolding FLTick0_def rtm2fl_def
proof auto
  fix xa :: "'a rtevent rttrace"
  show "\<And> P. \<forall>x\<in>P. rtWF x \<Longrightarrow> RTM1 P \<Longrightarrow> RTM2 P \<Longrightarrow> RT3 P \<Longrightarrow> RT4 P \<Longrightarrow> xa \<in> P \<Longrightarrow> tickWF TickRT (rtm2fl_trace xa)"
  proof (induct xa, auto)
    fix P :: "'a rtevent rtprocess" and x
    assume RTM2_P: "RTM2 P" and RT3_P: "RT3 P" and RT4_P: "RT4 P"
    show "\<langle>x\<rangle>\<^sub>\<R>\<^sub>\<T> \<in> P \<Longrightarrow> TickRT \<in>\<^sub>\<F>\<^sub>\<L> maxref2acc x \<Longrightarrow> False"
    proof (cases x, auto)
      fix x2
      assume case_assms: "\<langle>[x2]\<^sub>\<R>\<^sub>\<T>\<rangle>\<^sub>\<R>\<^sub>\<T> \<in> P" "TickRT \<notin> x2"
      then have "RTEmptyInit @\<^sub>\<R>\<^sub>\<T> \<langle>[x2]\<^sub>\<R>\<^sub>\<T>\<rangle>\<^sub>\<R>\<^sub>\<T> @\<^sub>\<R>\<^sub>\<T> TickRT ##\<^sub>\<R>\<^sub>\<T> \<langle>\<bullet>\<^sub>\<R>\<^sub>\<T>\<rangle>\<^sub>\<R>\<^sub>\<T> \<in> P"
        using RTM2_P unfolding RTM2_def by (metis rttrace_with_refusal.simps(3))
      then show "False"
        using RT4_P unfolding RT4_def by blast
    qed
  next
    fix P :: "'a rtevent rtprocess"
    fix x1a :: "'a rtevent rtrefusal" and x2 :: "'a rtevent" and xa :: "'a rtevent rttrace"
    assume ind_hyp: "\<And>P. \<forall>x\<in>P. rtWF x \<Longrightarrow> RTM1 P \<Longrightarrow> RTM2 P \<Longrightarrow> RT3 P \<Longrightarrow> RT4 P \<Longrightarrow> xa \<in> P \<Longrightarrow> tickWF TickRT (rtm2fl_trace xa)"
    assume P_wf: "\<forall>x\<in>P. rtWF x" and RTM1_P: "RTM1 P" and RTM2_P: "RTM2 P" and RT3_P: "RT3 P" and RT4_P: "RT4 P"
    assume case_assm: "(x1a #\<^sub>\<R>\<^sub>\<T> x2 #\<^sub>\<R>\<^sub>\<T> xa) \<in> P"

    have 0: "RTM1 {x. (x1a #\<^sub>\<R>\<^sub>\<T> x2 #\<^sub>\<R>\<^sub>\<T> x) \<in> P}"
      by (simp add: RTM1_P RTM1_init_event)
    have 1: "RTM2 {x. (x1a #\<^sub>\<R>\<^sub>\<T> x2 #\<^sub>\<R>\<^sub>\<T> x) \<in> P}"
      using RTM2_P unfolding RTM2_def by (auto, metis rttrace_with_refusal.simps(1))
    have 2: "RT3 {x. (x1a #\<^sub>\<R>\<^sub>\<T> x2 #\<^sub>\<R>\<^sub>\<T> x) \<in> P}"
      using RT3_P unfolding RT3_def
      by (auto, metis no_tick.simps(2) no_tick.simps(3) rtevent.exhaust rttrace_with_refusal.simps(1))
    have 3: "RT4 {x. (x1a #\<^sub>\<R>\<^sub>\<T> x2 #\<^sub>\<R>\<^sub>\<T> x) \<in> P}"
      using RT4_P unfolding RT4_def by (metis mem_Collect_eq rttrace_with_refusal.simps(1))
    have 4: "\<forall>x\<in>{x. (x1a #\<^sub>\<R>\<^sub>\<T> x2 #\<^sub>\<R>\<^sub>\<T> x) \<in> P}. rtWF x"
      using P_wf by auto
    have xa_wf: "tickWF TickRT (rtm2fl_trace xa)"
      using ind_hyp[where P="{x. (x1a #\<^sub>\<R>\<^sub>\<T> x2 #\<^sub>\<R>\<^sub>\<T> x) \<in> P}"] 0 1 2 3 4 case_assm by force
    then show "tickWF TickRT (rtm2fl_trace (x1a #\<^sub>\<R>\<^sub>\<T> x2 #\<^sub>\<R>\<^sub>\<T> xa))"
    proof (cases x2, auto)
      assume x2_tick: "x2 = TickRT"
      then have "\<exists> X. xa = \<langle>X\<rangle>\<^sub>\<R>\<^sub>\<T>"
        using case_assm RT3_P xa_wf unfolding RT3_def
      proof (auto, induct xa, auto)
        fix x1aa x2a and xaa :: "'a rtevent rttrace"
        assume in_P: "(x1a #\<^sub>\<R>\<^sub>\<T> TickRT #\<^sub>\<R>\<^sub>\<T> (x1aa #\<^sub>\<R>\<^sub>\<T> x2a #\<^sub>\<R>\<^sub>\<T> xaa)) \<in> P"
        assume RT3_P: "\<forall>\<rho>. (\<exists>x y e. \<rho> @\<^sub>\<R>\<^sub>\<T> \<langle>x\<rangle>\<^sub>\<R>\<^sub>\<T> @\<^sub>\<R>\<^sub>\<T> e ##\<^sub>\<R>\<^sub>\<T> \<langle>y\<rangle>\<^sub>\<R>\<^sub>\<T> \<in> P) \<longrightarrow> no_tick \<rho>"
        obtain \<rho> x y e where "(x1a #\<^sub>\<R>\<^sub>\<T> TickRT #\<^sub>\<R>\<^sub>\<T> (x1aa #\<^sub>\<R>\<^sub>\<T> x2a #\<^sub>\<R>\<^sub>\<T> xaa)) = (RTEventInit x1a TickRT \<rho>) @\<^sub>\<R>\<^sub>\<T> \<langle>x\<rangle>\<^sub>\<R>\<^sub>\<T> @\<^sub>\<R>\<^sub>\<T> (e ##\<^sub>\<R>\<^sub>\<T> \<langle>y\<rangle>\<^sub>\<R>\<^sub>\<T>)"
          apply (induct xaa, auto, metis rttrace_with_refusal.simps(2))
          by (smt rttrace.inject(2) rttrace_init.exhaust rttrace_with_refusal.simps(1) rttrace_with_refusal.simps(2))
        then have "no_tick (RTEventInit x1a TickRT \<rho>)"
          by (metis RT3_P in_P no_tick.simps(3) x2_tick)
        then show "False"
          by auto
      qed
      then have "x1a = \<bullet>\<^sub>\<R>\<^sub>\<T>"
        using RT4_P case_assm unfolding RT4_def apply auto
        by (metis rttrace_with_refusal.simps(2) x2_tick)
      then show "TickRT \<in>\<^sub>\<F>\<^sub>\<L> acceptance (maxref2acc x1a,TickRT)\<^sub>\<F>\<^sub>\<L> \<Longrightarrow> False"
        by auto
    next
      fix x2a
      assume x2_event: "x2 = EventRT x2a"
      then have "\<not> EventRT x2a \<in>\<^sub>\<R>\<^sub>\<T> x1a"
        using P_wf case_assm by auto
      then show "event (maxref2acc x1a,EventRT x2a)\<^sub>\<F>\<^sub>\<L> = TickRT \<Longrightarrow> False"
        using P_wf case_assm rtm2fl_trace_aevent_prefix x2_event by force
    next
      fix x2a
      assume x2_event: "x2 = EventRT x2a"
      then have "\<not> EventRT x2a \<in>\<^sub>\<R>\<^sub>\<T> x1a"
        using P_wf case_assm by auto
      then show "event (maxref2acc x1a,EventRT x2a)\<^sub>\<F>\<^sub>\<L> = TickRT \<Longrightarrow> rtm2fl_trace xa = \<langle>\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>"
        using P_wf case_assm rtm2fl_trace_aevent_prefix x2_event by force
    next
      fix x2a
      assume x2_event: "x2 = EventRT x2a"
      then have event_notin_refusal: "\<not> EventRT x2a \<in>\<^sub>\<R>\<^sub>\<T> x1a"
        using P_wf case_assm by auto
      assume "TickRT \<in>\<^sub>\<F>\<^sub>\<L> acceptance (maxref2acc x1a,EventRT x2a)\<^sub>\<F>\<^sub>\<L>"
      then have "TickRT \<in>\<^sub>\<F>\<^sub>\<L> maxref2acc x1a"
        using event_notin_refusal by (cases x1a, auto)
      then have x1a_not_bullet: "\<exists> X. x1a = [X]\<^sub>\<R>\<^sub>\<T> \<and> TickRT \<notin> X"
        by (cases x1a, auto)
      have "\<langle>x1a\<rangle>\<^sub>\<R>\<^sub>\<T> \<in> P"
        using RTM1_P RTM1_def case_assm x1a_not_bullet by force
      then have "(x1a #\<^sub>\<R>\<^sub>\<T> TickRT #\<^sub>\<R>\<^sub>\<T> \<langle>\<bullet>\<^sub>\<R>\<^sub>\<T>\<rangle>\<^sub>\<R>\<^sub>\<T>) \<in> P"
        using RTM2_P unfolding RTM2_def
        by (metis rttrace_with_refusal.simps(2) rttrace_with_refusal.simps(3) x1a_not_bullet)
      then have "x1a = \<bullet>\<^sub>\<R>\<^sub>\<T>"
        using RT4_P unfolding RT4_def by (metis (full_types) rttrace_with_refusal.simps(2))
      then show "False"
        using x1a_not_bullet by blast
    qed
  qed
qed

definition FLTick :: "'a \<Rightarrow> 'a fltraces \<Rightarrow> bool" where
  "FLTick tick P = (FL0 P \<and> FL1 P \<and> FL2 P \<and> FLTick0 tick P)"

lemma rtm2fl_FLTick:
  assumes "RTM P"
  shows "FLTick TickRT (rtm2fl P)"
  using assms unfolding RTM_def FLTick_def apply auto
  using rtm2fl_FL0 rtm2fl_FL1 rtm2fl_FL2 rtm2fl_FLTick0 by blast+

lemma rtm2fl_mono: "P \<sqsubseteq>\<^sub>\<R>\<^sub>\<T> Q \<Longrightarrow> rtm2fl P \<sqsubseteq>\<^sub>\<F>\<^sub>\<L> rtm2fl Q"
  unfolding refinesRT_def rtm2fl_def by auto

end