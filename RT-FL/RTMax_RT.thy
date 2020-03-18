theory RTMax_RT
  imports RT
begin

section \<open>Mapping from RTMax to RT\<close>

definition mkRT1 :: "'a rtprocess \<Rightarrow> 'a rtprocess" where
  "mkRT1 P = {x. \<exists>y\<in>P. x \<le>\<^sub>\<R>\<^sub>\<T> y}"

lemma subset_mkRT1:
  "P \<subseteq> mkRT1 P"
  unfolding mkRT1_def using leq_rttrace_refl by blast

lemma mkRT1_wf:
  assumes "\<forall>x\<in>P. rtWF x"
  shows "\<forall> x \<in> mkRT1 P. rtWF x"
  using assms unfolding mkRT1_def 
proof auto
  fix x xa :: "'a rttrace"
  have "rtWF xa \<Longrightarrow> x \<le>\<^sub>\<R>\<^sub>\<T> xa \<Longrightarrow> rtWF x"
    by (induct x xa rule:leq_rttrace.induct, auto)
  then show "\<forall>x\<in>P. rtWF x \<Longrightarrow> xa \<in> P \<Longrightarrow> x \<le>\<^sub>\<R>\<^sub>\<T> xa \<Longrightarrow> rtWF x"
    by auto
qed

lemma RT1_mkRT1:
  "RT1 (mkRT1 P)"
  unfolding RT1_def mkRT1_def using leq_rttrace_trans by blast

lemma RT2_mkRT1:
  assumes "RTM1 P" "RTM2 P"
  shows "RT2 (mkRT1 P)"
  using assms unfolding RTM1_def RTM2_def RT2_def mkRT1_def
proof auto
  fix \<rho> \<sigma> X Y x
  assume RTM1_P: "\<forall>\<rho>. (\<exists>\<sigma>. \<sigma> \<in> P \<and> \<rho> \<le>\<^sub>\<R>\<^sub>\<T>\<^sub>\<M> \<sigma>) \<longrightarrow> \<rho> \<in> P"
  assume RTM2_P: "\<forall>\<rho> X e. \<rho> @\<^sub>\<R>\<^sub>\<T> \<langle>[X]\<^sub>\<R>\<^sub>\<T>\<rangle>\<^sub>\<R>\<^sub>\<T> @\<^sub>\<R>\<^sub>\<T> RTEmptyTail \<in> P \<and> e \<notin> X \<longrightarrow> \<rho> @\<^sub>\<R>\<^sub>\<T> \<langle>[X]\<^sub>\<R>\<^sub>\<T>\<rangle>\<^sub>\<R>\<^sub>\<T> @\<^sub>\<R>\<^sub>\<T> e ##\<^sub>\<R>\<^sub>\<T> \<langle>\<bullet>\<^sub>\<R>\<^sub>\<T>\<rangle>\<^sub>\<R>\<^sub>\<T> \<in> P"
  assume Y_assm: "\<forall>e\<in>Y. \<forall>x\<in>P. \<not> \<rho> @\<^sub>\<R>\<^sub>\<T> \<langle>[X]\<^sub>\<R>\<^sub>\<T>\<rangle>\<^sub>\<R>\<^sub>\<T> @\<^sub>\<R>\<^sub>\<T> e ##\<^sub>\<R>\<^sub>\<T> \<langle>\<bullet>\<^sub>\<R>\<^sub>\<T>\<rangle>\<^sub>\<R>\<^sub>\<T> \<le>\<^sub>\<R>\<^sub>\<T> x"
  assume x_assm: "\<rho> @\<^sub>\<R>\<^sub>\<T> \<langle>[X]\<^sub>\<R>\<^sub>\<T>\<rangle>\<^sub>\<R>\<^sub>\<T> @\<^sub>\<R>\<^sub>\<T> \<sigma> \<le>\<^sub>\<R>\<^sub>\<T> x"
  assume x_in_P: "x \<in> P"

  have "\<exists> x\<rho> xX x\<sigma>. x = x\<rho> @\<^sub>\<R>\<^sub>\<T> \<langle>[xX]\<^sub>\<R>\<^sub>\<T>\<rangle>\<^sub>\<R>\<^sub>\<T> @\<^sub>\<R>\<^sub>\<T> x\<sigma> \<and> X \<subseteq> xX \<and> subset_rttrace_init \<rho> x\<rho>"
    using x_assm apply -
  proof (induct x \<rho> rule:leq_rttrace_rttrace_init_max.induct, auto)
    fix x
    assume "RTEmptyInit @\<^sub>\<R>\<^sub>\<T> \<langle>[X]\<^sub>\<R>\<^sub>\<T>\<rangle>\<^sub>\<R>\<^sub>\<T> @\<^sub>\<R>\<^sub>\<T> \<sigma> \<le>\<^sub>\<R>\<^sub>\<T> \<langle>x\<rangle>\<^sub>\<R>\<^sub>\<T>"
    then show "\<exists>x\<rho> xX. (\<exists>x\<sigma>. \<langle>x\<rangle>\<^sub>\<R>\<^sub>\<T> = x\<rho> @\<^sub>\<R>\<^sub>\<T> \<langle>[xX]\<^sub>\<R>\<^sub>\<T>\<rangle>\<^sub>\<R>\<^sub>\<T> @\<^sub>\<R>\<^sub>\<T> x\<sigma>) \<and> X \<subseteq> xX \<and> subset_rttrace_init RTEmptyInit x\<rho>"
      apply (rule_tac x=RTEmptyInit in exI, auto, cases x, auto, cases \<sigma>, auto)
      by (rule_tac x=x2 in exI, auto, metis rttrace_with_refusal.simps(3), cases \<sigma>, auto)
  next
    fix v va vb
    assume "RTEmptyInit @\<^sub>\<R>\<^sub>\<T> \<langle>[X]\<^sub>\<R>\<^sub>\<T>\<rangle>\<^sub>\<R>\<^sub>\<T> @\<^sub>\<R>\<^sub>\<T> \<sigma> \<le>\<^sub>\<R>\<^sub>\<T> (v #\<^sub>\<R>\<^sub>\<T> va #\<^sub>\<R>\<^sub>\<T> vb)"
    then show "\<exists>x\<rho> xX. (\<exists>x\<sigma>. (v #\<^sub>\<R>\<^sub>\<T> va #\<^sub>\<R>\<^sub>\<T> vb) = x\<rho> @\<^sub>\<R>\<^sub>\<T> \<langle>[xX]\<^sub>\<R>\<^sub>\<T>\<rangle>\<^sub>\<R>\<^sub>\<T> @\<^sub>\<R>\<^sub>\<T> x\<sigma>) \<and> X \<subseteq> xX \<and> subset_rttrace_init RTEmptyInit x\<rho>"
      apply (rule_tac x=RTEmptyInit in exI, auto, cases v, auto, cases \<sigma>, auto)
      by (rule_tac x=x2 in exI, auto, metis rttrace_with_refusal.simps(2), cases \<sigma>, auto)
  next
    fix v va vb vc vd ve
    assume ind_hyp: "ve @\<^sub>\<R>\<^sub>\<T> \<langle>[X]\<^sub>\<R>\<^sub>\<T>\<rangle>\<^sub>\<R>\<^sub>\<T> @\<^sub>\<R>\<^sub>\<T> \<sigma> \<le>\<^sub>\<R>\<^sub>\<T> vb \<Longrightarrow>
        \<exists>x\<rho> xX. (\<exists>x\<sigma>. vb = x\<rho> @\<^sub>\<R>\<^sub>\<T> \<langle>[xX]\<^sub>\<R>\<^sub>\<T>\<rangle>\<^sub>\<R>\<^sub>\<T> @\<^sub>\<R>\<^sub>\<T> x\<sigma>) \<and> X \<subseteq> xX \<and> subset_rttrace_init ve x\<rho>"
    assume case_assm: "(vc #\<^sub>\<R>\<^sub>\<T> vd #\<^sub>\<R>\<^sub>\<T> (ve @\<^sub>\<R>\<^sub>\<T> \<langle>[X]\<^sub>\<R>\<^sub>\<T>\<rangle>\<^sub>\<R>\<^sub>\<T> @\<^sub>\<R>\<^sub>\<T> \<sigma>)) \<le>\<^sub>\<R>\<^sub>\<T> (v #\<^sub>\<R>\<^sub>\<T> va #\<^sub>\<R>\<^sub>\<T> vb)"
    then have "(ve @\<^sub>\<R>\<^sub>\<T> \<langle>[X]\<^sub>\<R>\<^sub>\<T>\<rangle>\<^sub>\<R>\<^sub>\<T> @\<^sub>\<R>\<^sub>\<T> \<sigma>) \<le>\<^sub>\<R>\<^sub>\<T> vb"
      by (cases vc, auto, (cases v, auto)+)
    then obtain x\<rho> xX x\<sigma> where "vb = x\<rho> @\<^sub>\<R>\<^sub>\<T> \<langle>[xX]\<^sub>\<R>\<^sub>\<T>\<rangle>\<^sub>\<R>\<^sub>\<T> @\<^sub>\<R>\<^sub>\<T> x\<sigma> \<and> X \<subseteq> xX \<and> subset_rttrace_init ve x\<rho>"
      using ind_hyp by auto
    then show "\<exists>x\<rho> xX. (\<exists>x\<sigma>. (v #\<^sub>\<R>\<^sub>\<T> va #\<^sub>\<R>\<^sub>\<T> vb) = x\<rho> @\<^sub>\<R>\<^sub>\<T> \<langle>[xX]\<^sub>\<R>\<^sub>\<T>\<rangle>\<^sub>\<R>\<^sub>\<T> @\<^sub>\<R>\<^sub>\<T> x\<sigma>) \<and> X \<subseteq> xX \<and> subset_rttrace_init (RTEventInit vc vd ve) x\<rho>"
      using case_assm apply (rule_tac x="RTEventInit v va x\<rho>" in exI, auto, cases v, auto)
      apply (metis leq_rttrace.simps(6) leq_rttrace.simps(9) rtrefusal.exhaust subset_rttrace_init.simps(2))
      by (rule_tac x=xX in exI, auto, cases vc, auto)
  qed
  then obtain x\<rho> xX x\<sigma> where x_def: "x = x\<rho> @\<^sub>\<R>\<^sub>\<T> \<langle>[xX]\<^sub>\<R>\<^sub>\<T>\<rangle>\<^sub>\<R>\<^sub>\<T> @\<^sub>\<R>\<^sub>\<T> x\<sigma> \<and> X \<subseteq> xX \<and> subset_rttrace_init \<rho> x\<rho>"
    by auto
  then have "x\<rho> @\<^sub>\<R>\<^sub>\<T> \<langle>[xX]\<^sub>\<R>\<^sub>\<T>\<rangle>\<^sub>\<R>\<^sub>\<T> @\<^sub>\<R>\<^sub>\<T> RTEmptyTail \<in> P"
    using x_in_P
  proof auto
    assume "x\<rho> @\<^sub>\<R>\<^sub>\<T> \<langle>[xX]\<^sub>\<R>\<^sub>\<T>\<rangle>\<^sub>\<R>\<^sub>\<T> @\<^sub>\<R>\<^sub>\<T> x\<sigma> \<in> P"
    also have "x\<rho> @\<^sub>\<R>\<^sub>\<T> \<langle>[xX]\<^sub>\<R>\<^sub>\<T>\<rangle>\<^sub>\<R>\<^sub>\<T> @\<^sub>\<R>\<^sub>\<T> RTEmptyTail \<le>\<^sub>\<R>\<^sub>\<T>\<^sub>\<M> x\<rho> @\<^sub>\<R>\<^sub>\<T> \<langle>[xX]\<^sub>\<R>\<^sub>\<T>\<rangle>\<^sub>\<R>\<^sub>\<T> @\<^sub>\<R>\<^sub>\<T> x\<sigma>"
      by (induct x\<rho>, auto, cases x\<sigma>, auto, case_tac x1, auto)
    then show "x\<rho> @\<^sub>\<R>\<^sub>\<T> \<langle>[xX]\<^sub>\<R>\<^sub>\<T>\<rangle>\<^sub>\<R>\<^sub>\<T> @\<^sub>\<R>\<^sub>\<T> RTEmptyTail \<in> P"
      using RTM1_P calculation by blast
  qed
  then have "Y \<subseteq> xX"
    apply (auto)
  proof (rule ccontr)
    fix e
    assume inner_assms: "x\<rho> @\<^sub>\<R>\<^sub>\<T> \<langle>[xX]\<^sub>\<R>\<^sub>\<T>\<rangle>\<^sub>\<R>\<^sub>\<T> @\<^sub>\<R>\<^sub>\<T> RTEmptyTail \<in> P" "e \<in> Y" "e \<notin> xX"
    then have "x\<rho> @\<^sub>\<R>\<^sub>\<T> \<langle>[xX]\<^sub>\<R>\<^sub>\<T>\<rangle>\<^sub>\<R>\<^sub>\<T> @\<^sub>\<R>\<^sub>\<T> e ##\<^sub>\<R>\<^sub>\<T> \<langle>\<bullet>\<^sub>\<R>\<^sub>\<T>\<rangle>\<^sub>\<R>\<^sub>\<T> \<in> P"
      using RTM2_P by auto
    then have "\<not> \<rho> @\<^sub>\<R>\<^sub>\<T> \<langle>[X]\<^sub>\<R>\<^sub>\<T>\<rangle>\<^sub>\<R>\<^sub>\<T> @\<^sub>\<R>\<^sub>\<T> e ##\<^sub>\<R>\<^sub>\<T> \<langle>\<bullet>\<^sub>\<R>\<^sub>\<T>\<rangle>\<^sub>\<R>\<^sub>\<T> \<le>\<^sub>\<R>\<^sub>\<T> x\<rho> @\<^sub>\<R>\<^sub>\<T> \<langle>[xX]\<^sub>\<R>\<^sub>\<T>\<rangle>\<^sub>\<R>\<^sub>\<T> @\<^sub>\<R>\<^sub>\<T> e ##\<^sub>\<R>\<^sub>\<T> \<langle>\<bullet>\<^sub>\<R>\<^sub>\<T>\<rangle>\<^sub>\<R>\<^sub>\<T>"
      using Y_assm inner_assms(2) by blast
    also have "subset_rttrace_init \<rho> x\<rho> \<and> X \<subseteq> xX"
      using x_def by auto
    then have "\<rho> @\<^sub>\<R>\<^sub>\<T> \<langle>[X]\<^sub>\<R>\<^sub>\<T>\<rangle>\<^sub>\<R>\<^sub>\<T> @\<^sub>\<R>\<^sub>\<T> e ##\<^sub>\<R>\<^sub>\<T> \<langle>\<bullet>\<^sub>\<R>\<^sub>\<T>\<rangle>\<^sub>\<R>\<^sub>\<T> \<le>\<^sub>\<R>\<^sub>\<T> x\<rho> @\<^sub>\<R>\<^sub>\<T> \<langle>[xX]\<^sub>\<R>\<^sub>\<T>\<rangle>\<^sub>\<R>\<^sub>\<T> @\<^sub>\<R>\<^sub>\<T> e ##\<^sub>\<R>\<^sub>\<T> \<langle>\<bullet>\<^sub>\<R>\<^sub>\<T>\<rangle>\<^sub>\<R>\<^sub>\<T>"
      by (induct \<rho> x\<rho> rule:subset_rttrace_init.induct, auto, case_tac Y, auto)
    then show False
      using calculation by auto
  qed
  then have "X \<union> Y \<subseteq> xX \<and> subset_rttrace_init \<rho> x\<rho> \<and> \<rho> @\<^sub>\<R>\<^sub>\<T> \<langle>[X]\<^sub>\<R>\<^sub>\<T>\<rangle>\<^sub>\<R>\<^sub>\<T> @\<^sub>\<R>\<^sub>\<T> \<sigma> \<le>\<^sub>\<R>\<^sub>\<T> x\<rho> @\<^sub>\<R>\<^sub>\<T> \<langle>[xX]\<^sub>\<R>\<^sub>\<T>\<rangle>\<^sub>\<R>\<^sub>\<T> @\<^sub>\<R>\<^sub>\<T> x\<sigma>"
    using x_assm x_def by blast
  then have "\<rho> @\<^sub>\<R>\<^sub>\<T> \<langle>[X \<union> Y]\<^sub>\<R>\<^sub>\<T>\<rangle>\<^sub>\<R>\<^sub>\<T> @\<^sub>\<R>\<^sub>\<T> \<sigma> \<le>\<^sub>\<R>\<^sub>\<T> x\<rho> @\<^sub>\<R>\<^sub>\<T> \<langle>[xX]\<^sub>\<R>\<^sub>\<T>\<rangle>\<^sub>\<R>\<^sub>\<T> @\<^sub>\<R>\<^sub>\<T> x\<sigma>"
    apply (induct \<rho> x\<rho> rule:subset_rttrace_init.induct, auto)
    by (cases \<sigma>, auto, cases x\<sigma>, auto, cases x\<sigma>, auto, case_tac Ya, auto)
  then show "\<exists>x\<in>P. \<rho> @\<^sub>\<R>\<^sub>\<T> \<langle>[X \<union> Y]\<^sub>\<R>\<^sub>\<T>\<rangle>\<^sub>\<R>\<^sub>\<T> @\<^sub>\<R>\<^sub>\<T> \<sigma> \<le>\<^sub>\<R>\<^sub>\<T> x"
    using x_def x_in_P by (rule_tac x="x\<rho> @\<^sub>\<R>\<^sub>\<T> \<langle>[xX]\<^sub>\<R>\<^sub>\<T>\<rangle>\<^sub>\<R>\<^sub>\<T> @\<^sub>\<R>\<^sub>\<T> x\<sigma>" in bexI, auto)
qed

lemma leq_rttrace_leq_rttrace_max:
  "\<rho> @\<^sub>\<R>\<^sub>\<T> \<langle>x\<rangle>\<^sub>\<R>\<^sub>\<T> @\<^sub>\<R>\<^sub>\<T> e ##\<^sub>\<R>\<^sub>\<T> \<langle>y\<rangle>\<^sub>\<R>\<^sub>\<T> \<le>\<^sub>\<R>\<^sub>\<T> xa \<Longrightarrow>
    \<exists> xa\<rho> X Y. xa\<rho> @\<^sub>\<R>\<^sub>\<T> \<langle>X\<rangle>\<^sub>\<R>\<^sub>\<T> @\<^sub>\<R>\<^sub>\<T> e ##\<^sub>\<R>\<^sub>\<T> \<langle>Y\<rangle>\<^sub>\<R>\<^sub>\<T> \<le>\<^sub>\<R>\<^sub>\<T>\<^sub>\<M> xa \<and> subset_rttrace_init \<rho> xa\<rho> \<and> x \<subseteq>\<^sub>\<R>\<^sub>\<T> X \<and> y \<subseteq>\<^sub>\<R>\<^sub>\<T> Y"
proof (induct xa \<rho> rule:leq_rttrace_rttrace_init_max.induct, auto)
  fix v va vb
  assume "x #\<^sub>\<R>\<^sub>\<T> e #\<^sub>\<R>\<^sub>\<T> \<langle>y\<rangle>\<^sub>\<R>\<^sub>\<T> \<le>\<^sub>\<R>\<^sub>\<T> v #\<^sub>\<R>\<^sub>\<T> va #\<^sub>\<R>\<^sub>\<T> vb"
  then show "\<exists>xa\<rho> X Y. xa\<rho> @\<^sub>\<R>\<^sub>\<T> \<langle>X\<rangle>\<^sub>\<R>\<^sub>\<T> @\<^sub>\<R>\<^sub>\<T> e ##\<^sub>\<R>\<^sub>\<T> \<langle>Y\<rangle>\<^sub>\<R>\<^sub>\<T> \<le>\<^sub>\<R>\<^sub>\<T>\<^sub>\<M> v #\<^sub>\<R>\<^sub>\<T> va #\<^sub>\<R>\<^sub>\<T> vb \<and> subset_rttrace_init RTEmptyInit xa\<rho> \<and> x \<subseteq>\<^sub>\<R>\<^sub>\<T> X \<and> y \<subseteq>\<^sub>\<R>\<^sub>\<T> Y"
    apply (cases "(x #\<^sub>\<R>\<^sub>\<T> e #\<^sub>\<R>\<^sub>\<T> \<langle>y\<rangle>\<^sub>\<R>\<^sub>\<T>, v #\<^sub>\<R>\<^sub>\<T> va #\<^sub>\<R>\<^sub>\<T> vb)" rule:leq_rttrace.cases, auto)
    apply (cases vb, auto, rule_tac x="RTEmptyInit" in exI, auto)
    apply (metis leq_rttrace.simps(2) leq_rttrace.simps(3) leq_rttrace_max_refl subset_refusal.elims(3))
    apply (cases vb, auto, rule_tac x="RTEmptyInit" in exI, auto, case_tac "(y, x21)" rule:rtrefusal_cases2, auto)
    apply (metis (mono_tags) leq_rttrace_max.simps(1) leq_rttrace_max.simps(6))+
    apply (metis leq_rttrace_max.simps(4) leq_rttrace_max.simps(6) subset_refusal.simps(3))
    apply (cases vb, auto, rule_tac x="RTEmptyInit" in exI, auto, case_tac "(y, x1)" rule:rtrefusal_cases2, auto)
    apply (metis (mono_tags) leq_rttrace_max_refl)+
    apply (metis leq_rttrace_max_refl subset_refusal.simps(3))
    apply (cases vb, auto, rule_tac x="RTEmptyInit" in exI, auto, case_tac "(y, x21)" rule:rtrefusal_cases2, auto)
    apply (metis leq_rttrace_max.simps(1) leq_rttrace_max.simps(8))
    apply (metis leq_rttrace_max.simps(1) leq_rttrace_max.simps(7))
    apply (metis leq_rttrace_max.simps(4) leq_rttrace_max.simps(8) subset_refusal.simps(3))
    apply (cases vb, auto, rule_tac x="RTEmptyInit" in exI, auto, case_tac "(y, x1)" rule:rtrefusal_cases2, auto)
    apply (metis (mono_tags) leq_rttrace_max_refl subset_refusal.simps(3))+
    apply (case_tac "(y, x21)" rule:rtrefusal_cases2, auto)
    apply (metis (mono_tags) leq_rttrace_max.simps(1) leq_rttrace_max.simps(8) rttrace_with_refusal.simps(2) subset_refusal.simps(3) subset_rttrace_init.simps(1))+
    by (metis leq_rttrace_max.simps(4) leq_rttrace_max.simps(8) rttrace_with_refusal.simps(2) subset_refusal.simps(3) subset_rttrace_init.simps(1))
next
  fix v va vb vc vd ve
  assume ind_hyp: "ve @\<^sub>\<R>\<^sub>\<T> \<langle>x\<rangle>\<^sub>\<R>\<^sub>\<T> @\<^sub>\<R>\<^sub>\<T> e ##\<^sub>\<R>\<^sub>\<T> \<langle>y\<rangle>\<^sub>\<R>\<^sub>\<T> \<le>\<^sub>\<R>\<^sub>\<T> vb \<Longrightarrow>
      \<exists>xa\<rho> X Y. xa\<rho> @\<^sub>\<R>\<^sub>\<T> \<langle>X\<rangle>\<^sub>\<R>\<^sub>\<T> @\<^sub>\<R>\<^sub>\<T> e ##\<^sub>\<R>\<^sub>\<T> \<langle>Y\<rangle>\<^sub>\<R>\<^sub>\<T> \<le>\<^sub>\<R>\<^sub>\<T>\<^sub>\<M> vb \<and> subset_rttrace_init ve xa\<rho> \<and> x \<subseteq>\<^sub>\<R>\<^sub>\<T> X \<and> y \<subseteq>\<^sub>\<R>\<^sub>\<T> Y"
  assume case_assm: "vc #\<^sub>\<R>\<^sub>\<T> vd #\<^sub>\<R>\<^sub>\<T> (ve @\<^sub>\<R>\<^sub>\<T> \<langle>x\<rangle>\<^sub>\<R>\<^sub>\<T> @\<^sub>\<R>\<^sub>\<T> e ##\<^sub>\<R>\<^sub>\<T> \<langle>y\<rangle>\<^sub>\<R>\<^sub>\<T>) \<le>\<^sub>\<R>\<^sub>\<T> v #\<^sub>\<R>\<^sub>\<T> va #\<^sub>\<R>\<^sub>\<T> vb"
  then have "ve @\<^sub>\<R>\<^sub>\<T> \<langle>x\<rangle>\<^sub>\<R>\<^sub>\<T> @\<^sub>\<R>\<^sub>\<T> e ##\<^sub>\<R>\<^sub>\<T> \<langle>y\<rangle>\<^sub>\<R>\<^sub>\<T> \<le>\<^sub>\<R>\<^sub>\<T> vb"
    by (cases "(vc,v)" rule:rtrefusal_cases2, auto)
  then obtain xa\<rho> X Y where "xa\<rho> @\<^sub>\<R>\<^sub>\<T> \<langle>X\<rangle>\<^sub>\<R>\<^sub>\<T> @\<^sub>\<R>\<^sub>\<T> e ##\<^sub>\<R>\<^sub>\<T> \<langle>Y\<rangle>\<^sub>\<R>\<^sub>\<T> \<le>\<^sub>\<R>\<^sub>\<T>\<^sub>\<M> vb \<and> subset_rttrace_init ve xa\<rho> \<and> x \<subseteq>\<^sub>\<R>\<^sub>\<T> X \<and> y \<subseteq>\<^sub>\<R>\<^sub>\<T> Y"
    by (metis ind_hyp)
  then show "\<exists>xa\<rho> X Y.
        xa\<rho> @\<^sub>\<R>\<^sub>\<T> \<langle>X\<rangle>\<^sub>\<R>\<^sub>\<T> @\<^sub>\<R>\<^sub>\<T> e ##\<^sub>\<R>\<^sub>\<T> \<langle>Y\<rangle>\<^sub>\<R>\<^sub>\<T> \<le>\<^sub>\<R>\<^sub>\<T>\<^sub>\<M> v #\<^sub>\<R>\<^sub>\<T> va #\<^sub>\<R>\<^sub>\<T> vb \<and> subset_rttrace_init (RTEventInit vc vd ve) xa\<rho> \<and> x \<subseteq>\<^sub>\<R>\<^sub>\<T> X \<and> y \<subseteq>\<^sub>\<R>\<^sub>\<T> Y"
    using case_assm apply (cases "(vc,v)" rule:rtrefusal_cases2, auto)
    apply (metis leq_rttrace_max.simps(6) rttrace_with_refusal.simps(1) subset_rttrace_init.simps(2))
    apply (metis leq_rttrace_max.simps(7) rttrace_with_refusal.simps(1) subset_rttrace_init.simps(2))
    apply (metis leq_rttrace_max.simps(8) rttrace_with_refusal.simps(1) subset_rttrace_init.simps(4))
    done
qed

lemma RT3_mkRT1:
  assumes "RTM1 P" "RT3 P"
  shows "RT3 (mkRT1 P)"
  using assms unfolding RTM1_def RT3_def mkRT1_def
proof auto
  fix \<rho> x y e xa 
  assume RTM1_P: "\<forall>\<rho>. (\<exists>\<sigma>. \<sigma> \<in> P \<and> \<rho> \<le>\<^sub>\<R>\<^sub>\<T>\<^sub>\<M> \<sigma>) \<longrightarrow> \<rho> \<in> P"
  assume RT3_P: "\<forall>\<rho>. (\<exists>x y e. \<rho> @\<^sub>\<R>\<^sub>\<T> \<langle>x\<rangle>\<^sub>\<R>\<^sub>\<T> @\<^sub>\<R>\<^sub>\<T> e ##\<^sub>\<R>\<^sub>\<T> \<langle>y\<rangle>\<^sub>\<R>\<^sub>\<T> \<in> P) \<longrightarrow> no_tick \<rho>"
  assume xa_in_P: "xa \<in> P"
  assume xa_assm: "\<rho> @\<^sub>\<R>\<^sub>\<T> \<langle>x\<rangle>\<^sub>\<R>\<^sub>\<T> @\<^sub>\<R>\<^sub>\<T> e ##\<^sub>\<R>\<^sub>\<T> \<langle>y\<rangle>\<^sub>\<R>\<^sub>\<T> \<le>\<^sub>\<R>\<^sub>\<T> xa"

  obtain xa\<rho> X Y where xa\<rho>_assms: "xa\<rho> @\<^sub>\<R>\<^sub>\<T> \<langle>X\<rangle>\<^sub>\<R>\<^sub>\<T> @\<^sub>\<R>\<^sub>\<T> e ##\<^sub>\<R>\<^sub>\<T> \<langle>Y\<rangle>\<^sub>\<R>\<^sub>\<T> \<le>\<^sub>\<R>\<^sub>\<T>\<^sub>\<M> xa \<and> subset_rttrace_init \<rho> xa\<rho> \<and> x \<subseteq>\<^sub>\<R>\<^sub>\<T> X \<and> y \<subseteq>\<^sub>\<R>\<^sub>\<T> Y"
    by (metis leq_rttrace_leq_rttrace_max xa_assm)
  then have "xa\<rho> @\<^sub>\<R>\<^sub>\<T> \<langle>X\<rangle>\<^sub>\<R>\<^sub>\<T> @\<^sub>\<R>\<^sub>\<T> e ##\<^sub>\<R>\<^sub>\<T> \<langle>Y\<rangle>\<^sub>\<R>\<^sub>\<T> \<in> P"
    by (metis RTM1_P xa_in_P)
  then have "no_tick xa\<rho>"
    by (metis RT3_P)
  then show "no_tick \<rho>"
    by (metis subset_rttrace_init_no_tick2 xa\<rho>_assms)
qed

thm RT4_def

lemma RT4_mkRT1:
  assumes "RTM1 P" "RT4 P"
  shows "RT4 (mkRT1 P)"
  using assms unfolding RTM1_def RT4_def mkRT1_def
proof (clarsimp)
  fix \<rho> x y xa
  assume RTM1_P: "\<forall>\<rho>. (\<exists>\<sigma>. \<sigma> \<in> P \<and> \<rho> \<le>\<^sub>\<R>\<^sub>\<T>\<^sub>\<M> \<sigma>) \<longrightarrow> \<rho> \<in> P"
  assume RT3_P: "\<forall>\<rho> x. (\<exists>y. \<rho> @\<^sub>\<R>\<^sub>\<T> \<langle>x\<rangle>\<^sub>\<R>\<^sub>\<T> @\<^sub>\<R>\<^sub>\<T> TickRT ##\<^sub>\<R>\<^sub>\<T> \<langle>y\<rangle>\<^sub>\<R>\<^sub>\<T> \<in> P) \<longrightarrow> x = \<bullet>\<^sub>\<R>\<^sub>\<T> \<and> \<rho> @\<^sub>\<R>\<^sub>\<T> \<langle>\<bullet>\<^sub>\<R>\<^sub>\<T>\<rangle>\<^sub>\<R>\<^sub>\<T> @\<^sub>\<R>\<^sub>\<T> TickRT ##\<^sub>\<R>\<^sub>\<T> \<langle>[UNIV]\<^sub>\<R>\<^sub>\<T>\<rangle>\<^sub>\<R>\<^sub>\<T> \<in> P"
  assume xa_in_P: "xa \<in> P"
  assume xa_assm: "\<rho> @\<^sub>\<R>\<^sub>\<T> \<langle>x\<rangle>\<^sub>\<R>\<^sub>\<T> @\<^sub>\<R>\<^sub>\<T> TickRT ##\<^sub>\<R>\<^sub>\<T> \<langle>y\<rangle>\<^sub>\<R>\<^sub>\<T> \<le>\<^sub>\<R>\<^sub>\<T> xa"

  

  obtain xa\<rho> X Y where xa\<rho>_assms: "xa\<rho> @\<^sub>\<R>\<^sub>\<T> \<langle>X\<rangle>\<^sub>\<R>\<^sub>\<T> @\<^sub>\<R>\<^sub>\<T> TickRT ##\<^sub>\<R>\<^sub>\<T> \<langle>Y\<rangle>\<^sub>\<R>\<^sub>\<T> \<le>\<^sub>\<R>\<^sub>\<T>\<^sub>\<M> xa \<and> subset_rttrace_init \<rho> xa\<rho> \<and> x \<subseteq>\<^sub>\<R>\<^sub>\<T> X \<and> y \<subseteq>\<^sub>\<R>\<^sub>\<T> Y"
    by (metis leq_rttrace_leq_rttrace_max xa_assm)
  then have "xa\<rho> @\<^sub>\<R>\<^sub>\<T> \<langle>X\<rangle>\<^sub>\<R>\<^sub>\<T> @\<^sub>\<R>\<^sub>\<T> TickRT ##\<^sub>\<R>\<^sub>\<T> \<langle>Y\<rangle>\<^sub>\<R>\<^sub>\<T> \<in> P"
    by (metis RTM1_P xa_in_P)
  then have "x = \<bullet>\<^sub>\<R>\<^sub>\<T> \<and> xa\<rho> @\<^sub>\<R>\<^sub>\<T> \<langle>\<bullet>\<^sub>\<R>\<^sub>\<T>\<rangle>\<^sub>\<R>\<^sub>\<T> @\<^sub>\<R>\<^sub>\<T> TickRT ##\<^sub>\<R>\<^sub>\<T> \<langle>[UNIV]\<^sub>\<R>\<^sub>\<T>\<rangle>\<^sub>\<R>\<^sub>\<T> \<in> P \<and> subset_rttrace_init \<rho> xa\<rho>"
    by (metis RT3_P rtrefusal.exhaust subset_refusal.simps(2) xa\<rho>_assms)
  then have "x = \<bullet>\<^sub>\<R>\<^sub>\<T> \<and> xa\<rho> @\<^sub>\<R>\<^sub>\<T> \<langle>\<bullet>\<^sub>\<R>\<^sub>\<T>\<rangle>\<^sub>\<R>\<^sub>\<T> @\<^sub>\<R>\<^sub>\<T> TickRT ##\<^sub>\<R>\<^sub>\<T> \<langle>[UNIV]\<^sub>\<R>\<^sub>\<T>\<rangle>\<^sub>\<R>\<^sub>\<T> \<in> P
    \<and> \<rho> @\<^sub>\<R>\<^sub>\<T> \<langle>\<bullet>\<^sub>\<R>\<^sub>\<T>\<rangle>\<^sub>\<R>\<^sub>\<T> @\<^sub>\<R>\<^sub>\<T> TickRT ##\<^sub>\<R>\<^sub>\<T> \<langle>[UNIV]\<^sub>\<R>\<^sub>\<T>\<rangle>\<^sub>\<R>\<^sub>\<T> \<le>\<^sub>\<R>\<^sub>\<T> xa\<rho> @\<^sub>\<R>\<^sub>\<T> \<langle>\<bullet>\<^sub>\<R>\<^sub>\<T>\<rangle>\<^sub>\<R>\<^sub>\<T> @\<^sub>\<R>\<^sub>\<T> TickRT ##\<^sub>\<R>\<^sub>\<T> \<langle>[UNIV]\<^sub>\<R>\<^sub>\<T>\<rangle>\<^sub>\<R>\<^sub>\<T>"
  proof auto
    show "subset_rttrace_init \<rho> xa\<rho> \<Longrightarrow>
      \<rho> @\<^sub>\<R>\<^sub>\<T> \<langle>\<bullet>\<^sub>\<R>\<^sub>\<T>\<rangle>\<^sub>\<R>\<^sub>\<T> @\<^sub>\<R>\<^sub>\<T> TickRT ##\<^sub>\<R>\<^sub>\<T> \<langle>[UNIV]\<^sub>\<R>\<^sub>\<T>\<rangle>\<^sub>\<R>\<^sub>\<T> \<le>\<^sub>\<R>\<^sub>\<T> xa\<rho> @\<^sub>\<R>\<^sub>\<T> \<langle>\<bullet>\<^sub>\<R>\<^sub>\<T>\<rangle>\<^sub>\<R>\<^sub>\<T> @\<^sub>\<R>\<^sub>\<T> TickRT ##\<^sub>\<R>\<^sub>\<T> \<langle>[UNIV]\<^sub>\<R>\<^sub>\<T>\<rangle>\<^sub>\<R>\<^sub>\<T>"
      by (induct \<rho> xa\<rho> rule:subset_rttrace_init.induct, auto, case_tac Y, auto)
  qed
  then show "x = \<bullet>\<^sub>\<R>\<^sub>\<T> \<and> (\<exists>x\<in>P. \<rho> @\<^sub>\<R>\<^sub>\<T> \<langle>\<bullet>\<^sub>\<R>\<^sub>\<T>\<rangle>\<^sub>\<R>\<^sub>\<T> @\<^sub>\<R>\<^sub>\<T> TickRT ##\<^sub>\<R>\<^sub>\<T> \<langle>[UNIV]\<^sub>\<R>\<^sub>\<T>\<rangle>\<^sub>\<R>\<^sub>\<T> \<le>\<^sub>\<R>\<^sub>\<T> x)"
    by (auto)
qed

lemma RT_mkRT1:
  assumes "RTM P"
  shows "RT (mkRT1 P)"
  using assms unfolding RTM_def RT_def
  by (metis (mono_tags, lifting) CollectI MRT0_def RT1_mkRT1 RT2_mkRT1 RT3_mkRT1 RT4_mkRT1 leq_rttrace.simps(1) mkRT1_def mkRT1_wf)

lemma mkRT1_mono:
  "P \<sqsubseteq>\<^sub>\<R>\<^sub>\<T> Q \<Longrightarrow> mkRT1 P \<sqsubseteq>\<^sub>\<R>\<^sub>\<T> mkRT1 Q"
  unfolding mkRT1_def refinesRT_def by auto

section \<open>Mapping from RT to RTMax\<close>

definition unRT1 :: "'a rtevent rtprocess \<Rightarrow> 'a rtevent rtprocess" where
  "unRT1 P = \<Union>{x. RTM1 x \<and> RTM2 x \<and> RT4 x \<and> (mkRT1 x) \<subseteq> P}"

lemma unRT1_subset:
  "unRT1 P \<subseteq> P"
  unfolding unRT1_def mkRT1_def
proof auto
  fix x :: "'a rtevent rttrace" and X
  assume x_in_X: "x \<in> X"
  assume P_subset: "{x. \<exists>xa\<in>X. x \<le>\<^sub>\<R>\<^sub>\<T> xa} \<subseteq> P"

  have "x \<in> {x. \<exists>xa\<in>X. x \<le>\<^sub>\<R>\<^sub>\<T> xa}"
    by (metis (no_types, lifting) CollectI leq_rttrace_refl x_in_X)
  then show "x \<in> P"
    by (metis (no_types, lifting) P_subset rev_subsetD)
qed

lemma unRT1_wf:
  assumes "\<forall>x\<in>P. rtWF x"
  shows "\<forall>x\<in>(unRT1 P). rtWF x"
  using assms unRT1_subset by auto 

lemma MRT0_unRT1:
  assumes "MRT0 P" "RT1 P"
  shows "MRT0 (unRT1 P)"
  using assms unfolding unRT1_def MRT0_def 
proof auto
  assume MRT0_P: "\<langle>\<bullet>\<^sub>\<R>\<^sub>\<T>\<rangle>\<^sub>\<R>\<^sub>\<T> \<in> P"
  assume RT1_P: "RT1 P"

  show "\<exists>x. RTM1 x \<and> RTM2 x \<and> RT4 x \<and> mkRT1 x \<subseteq> P \<and> \<langle>\<bullet>\<^sub>\<R>\<^sub>\<T>\<rangle>\<^sub>\<R>\<^sub>\<T> \<in> x"
    apply (rule_tac x="{\<langle>\<bullet>\<^sub>\<R>\<^sub>\<T>\<rangle>\<^sub>\<R>\<^sub>\<T>}" in exI, auto)
    apply (metis RTM1_def leq_rttrace_max.simps(1) leq_rttrace_max_antisym singletonD)
    apply (metis RTM2_def leq_rttrace_max.simps(1) leq_rttrace_max.simps(3) rttrace.simps(4) rttrace_with_refusal.elims rttrace_with_refusal.simps(3) singletonD)
    apply (metis RT4_def rttrace.distinct(1) rttrace_with_refusal.elims rttrace_with_refusal.simps(2) singletonD)
    by (smt MRT0_P RT1_P RT1_def mem_Collect_eq mkRT1_def singletonD)
qed 

lemma RTM1_unRT1: "RTM1 (unRT1 P)"
  unfolding unRT1_def RTM1_def by auto

lemma RTM2_unRT1: "RTM2 (unRT1 P)"
  unfolding unRT1_def RTM2_def by auto

lemma RT3_unRT1:
  assumes "RT3 P"
  shows "RT3 (unRT1 P)"
  using assms unfolding RT3_def by (auto, metis contra_subsetD unRT1_subset)

lemma RT4_unRT1: "RT4 (unRT1 P)"
  unfolding unRT1_def RT4_def by auto

lemma RTM_unRT1:
  assumes "RT P"
  shows "RTM (unRT1 P)"
  using assms unfolding RT_def RTM_def
  by (metis MRT0_unRT1 RT3_unRT1 RT4_unRT1 RTM1_unRT1 RTM2_unRT1 unRT1_wf) 

lemma unRT1_mono:
  "P \<sqsubseteq>\<^sub>\<R>\<^sub>\<T> Q \<Longrightarrow> unRT1 P \<sqsubseteq>\<^sub>\<R>\<^sub>\<T> unRT1 Q"
  unfolding refinesRT_def unRT1_def by auto

section \<open>Galois connection between RTMax and RT\<close>

lemma unRT1_mkRT1_Galois:
  assumes RT1_P: "RT1 P"
  assumes RTM1_Q: "RTM1 Q" and RTM2_Q: "RTM2 Q" and RT4_Q: "RT4 Q"
  shows "(unRT1 P \<sqsubseteq>\<^sub>\<R>\<^sub>\<T> Q) = (P \<sqsubseteq>\<^sub>\<R>\<^sub>\<T> mkRT1 Q)"
  unfolding mkRT1_def refinesRT_def 
proof auto
  fix x xa
  assume Q_subset_unRT1_P: "Q \<subseteq> unRT1 P"
  assume xa_in_Q: "xa \<in> Q"
  assume x_leqRT_xa: "x \<le>\<^sub>\<R>\<^sub>\<T> xa"

  have "Q \<subseteq> P"
    using Q_subset_unRT1_P unRT1_subset by blast
  then have "xa \<in> P"
    using xa_in_Q by blast
  then show "x \<in> P"
    using RT1_P x_leqRT_xa unfolding RT1_def by blast
next
  fix x
  assume "{x. \<exists>xa\<in>Q. x \<le>\<^sub>\<R>\<^sub>\<T> xa} \<subseteq> P" "x \<in> Q"
  then show "x \<in> unRT1 P"
    unfolding unRT1_def mkRT1_def by (auto, rule_tac x=Q in exI, auto simp add: assms)
qed
  
end