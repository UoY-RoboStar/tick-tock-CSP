theory CTockTick_Prefix
  imports CTockTick_Core
begin

subsection {* Prefix *}

definition PrefixCTT :: "'e \<Rightarrow> 'e cttobs list set \<Rightarrow> 'e cttobs list set" (infixr "\<rightarrow>\<^sub>C" 61) where
  "PrefixCTT e P = 
    {t. \<exists> s\<in>tocks({x. x \<noteq> Tock \<and> x \<noteq> Event e}). t = s \<or> (\<exists> X. Tock \<notin> X \<and> Event e \<notin> X \<and> t = s @ [[X]\<^sub>R])}
     \<union> {t. \<exists> s\<in>tocks({x. x \<noteq> Tock \<and> x \<noteq> Event e}). t = s \<or> (\<exists> \<sigma>\<in>P. t = s @ [[Event e]\<^sub>E] @ \<sigma>)}"

lemma PrefixCTT_wf: "\<forall> t\<in>P. ttWF t \<Longrightarrow> \<forall> t\<in>PrefixCTT e P. ttWF t"
  unfolding PrefixCTT_def by (auto simp add: tocks_wf tocks_append_wf)

lemma CT2s_Prefix:
  assumes CT0_P: "CT0 P" and CT1_P: "CT1 P"
  assumes CT2s_P: "CT2s P"
  shows "CT2s (e \<rightarrow>\<^sub>C P)"
  unfolding CT2s_def
proof auto
  fix \<rho> \<sigma> X Y
  assume assm1: "\<rho> @ [X]\<^sub>R # \<sigma> \<in> e \<rightarrow>\<^sub>C P"
  assume assm2: "Y \<inter> {ea. ea \<noteq> Tock \<and> \<rho> @ [[ea]\<^sub>E] \<in> e \<rightarrow>\<^sub>C P \<or> ea = Tock \<and> \<rho> @ [[X]\<^sub>R, [ea]\<^sub>E] \<in> e \<rightarrow>\<^sub>C P} = {}"
  show "\<rho> @ [X \<union> Y]\<^sub>R # \<sigma> \<in> e \<rightarrow>\<^sub>C P"
    using assm1 unfolding PrefixCTT_def
  proof auto
    assume case_assms: "\<rho> @ [X]\<^sub>R # \<sigma> \<in> tocks {x. x \<noteq> Tock \<and> x \<noteq> Event e}"
    then have 1: "\<rho> \<in> tocks {x. x \<noteq> Tock \<and> x \<noteq> Event e}"
      using tocks_mid_refusal_front_in_tocks by blast
    then have "Tock \<in> {ea. ea \<noteq> Tock \<and> \<rho> @ [[ea]\<^sub>E] \<in> e \<rightarrow>\<^sub>C P \<or> ea = Tock \<and> \<rho> @ [[X]\<^sub>R, [ea]\<^sub>E] \<in> e \<rightarrow>\<^sub>C P}"
      unfolding PrefixCTT_def apply auto
      by (metis (no_types, lifting) case_assms tocks.empty_in_tocks tocks.tock_insert_in_tocks tocks_append_tocks tocks_mid_refusal)
    then have 2: "Tock \<notin> Y"
      using assm2 by blast
    then have "Event e \<in> {ea. ea \<noteq> Tock \<and> \<rho> @ [[ea]\<^sub>E] \<in> e \<rightarrow>\<^sub>C P \<or> ea = Tock \<and> \<rho> @ [[X]\<^sub>R, [ea]\<^sub>E] \<in> e \<rightarrow>\<^sub>C P}"
      using 1 unfolding PrefixCTT_def apply auto
      using CT0_CT1_empty CT0_P CT1_P by (erule_tac x="\<rho>" in ballE, auto)+
    then have 3: "Event e \<notin> Y"
      using assm2 by blast
    have 4: "Tock \<notin> X"
      using case_assms tocks_mid_refusal by fastforce
    have 5: "Event e \<notin> X"
      using case_assms tocks_mid_refusal by fastforce
    then have "X \<union> Y \<subseteq> {x. x \<noteq> Tock \<and> x \<noteq> Event e}"
      using 1 2 3 4 5 by auto
    then show "\<forall>s\<in>tocks {x. x \<noteq> Tock \<and> x \<noteq> Event e}. \<rho> @ [X \<union> Y]\<^sub>R # \<sigma> \<noteq> s \<and> (\<forall>\<sigma>'\<in>P. \<rho> @ [X \<union> Y]\<^sub>R # \<sigma> \<noteq> s @ [Event e]\<^sub>E # \<sigma>') \<Longrightarrow>
      \<exists>s\<in>tocks {x. x \<noteq> Tock \<and> x \<noteq> Event e}. \<exists>Xa. Tock \<notin> Xa \<and> Event e \<notin> Xa \<and> \<rho> @ [X \<union> Y]\<^sub>R # \<sigma> = s @ [[Xa]\<^sub>R]"
      using case_assms apply (erule_tac x="\<rho> @ [X \<union> Y]\<^sub>R # \<sigma>" in ballE, auto)
      using tocks_mid_refusal_change by fastforce
  next
    assume case_assms: "\<rho> @ [X]\<^sub>R # \<sigma> \<in> tocks {x. x \<noteq> Tock \<and> x \<noteq> Event e}"
    then have 1: "\<rho> \<in> tocks {x. x \<noteq> Tock \<and> x \<noteq> Event e}"
      using tocks_mid_refusal_front_in_tocks by blast
    then have "Tock \<in> {ea. ea \<noteq> Tock \<and> \<rho> @ [[ea]\<^sub>E] \<in> e \<rightarrow>\<^sub>C P \<or> ea = Tock \<and> \<rho> @ [[X]\<^sub>R, [ea]\<^sub>E] \<in> e \<rightarrow>\<^sub>C P}"
      unfolding PrefixCTT_def apply auto
      by (metis (no_types, lifting) case_assms tocks.empty_in_tocks tocks.tock_insert_in_tocks tocks_append_tocks tocks_mid_refusal)
    then have 2: "Tock \<notin> Y"
      using assm2 by blast
    then have "Event e \<in> {ea. ea \<noteq> Tock \<and> \<rho> @ [[ea]\<^sub>E] \<in> e \<rightarrow>\<^sub>C P \<or> ea = Tock \<and> \<rho> @ [[X]\<^sub>R, [ea]\<^sub>E] \<in> e \<rightarrow>\<^sub>C P}"
      using 1 unfolding PrefixCTT_def apply auto
      using CT0_CT1_empty CT0_P CT1_P by (erule_tac x="\<rho>" in ballE, auto)+
    then have 3: "Event e \<notin> Y"
      using assm2 by blast
    have 4: "Tock \<notin> X"
      using case_assms tocks_mid_refusal by fastforce
    have 5: "Event e \<notin> X"
      using case_assms tocks_mid_refusal by fastforce
    then have "X \<union> Y \<subseteq> {x. x \<noteq> Tock \<and> x \<noteq> Event e}"
      using 1 2 3 4 5 by auto
    then show "\<forall>s\<in>tocks {x. x \<noteq> Tock \<and> x \<noteq> Event e}. \<rho> @ [X \<union> Y]\<^sub>R # \<sigma> \<noteq> s \<and> (\<forall>\<sigma>'\<in>P. \<rho> @ [X \<union> Y]\<^sub>R # \<sigma> \<noteq> s @ [Event e]\<^sub>E # \<sigma>') \<Longrightarrow>
      \<exists>s\<in>tocks {x. x \<noteq> Tock \<and> x \<noteq> Event e}. \<exists>Xa. Tock \<notin> Xa \<and> Event e \<notin> Xa \<and> \<rho> @ [X \<union> Y]\<^sub>R # \<sigma> = s @ [[Xa]\<^sub>R]"
      using case_assms apply (erule_tac x="\<rho> @ [X \<union> Y]\<^sub>R # \<sigma>" in ballE, auto)
      using tocks_mid_refusal_change by fastforce
  next
    fix s Xa
    assume case_assms: "s \<in> tocks {x. x \<noteq> Tock \<and> x \<noteq> Event e}" "Tock \<notin> Xa" "Event e \<notin> Xa" "\<rho> @ [X]\<^sub>R # \<sigma> = s @ [[Xa]\<^sub>R]"
    then have "(\<exists> \<sigma>'. s = \<rho> @ [X]\<^sub>R # \<sigma>') \<or> (s = \<rho> \<and> X = Xa \<and> \<sigma> = [])"
      by (metis append.right_neutral butlast.simps(2) butlast_append cttobs.inject(2) last_snoc list.distinct(1))
    then show "\<exists>s\<in>tocks {x. x \<noteq> Tock \<and> x \<noteq> Event e}. \<exists>Xa. Tock \<notin> Xa \<and> Event e \<notin> Xa \<and> \<rho> @ [X \<union> Y]\<^sub>R # \<sigma> = s @ [[Xa]\<^sub>R]"
      using case_assms
    proof auto
      fix \<sigma>'
      assume case_assms2: "s = \<rho> @ [X]\<^sub>R # \<sigma>'"
      have 1: "\<rho> \<in> tocks {x. x \<noteq> Tock \<and> x \<noteq> Event e}"
        using case_assms(1) case_assms2 tocks_mid_refusal_front_in_tocks by auto
      have "Tock \<in> {ea. ea \<noteq> Tock \<and> \<rho> @ [[ea]\<^sub>E] \<in> e \<rightarrow>\<^sub>C P \<or> ea = Tock \<and> \<rho> @ [[X]\<^sub>R, [ea]\<^sub>E] \<in> e \<rightarrow>\<^sub>C P}"
         unfolding PrefixCTT_def apply auto
         using case_assms case_assms2 1 by (simp add: empty_in_tocks tock_insert_in_tocks tocks_append_tocks tocks_mid_refusal)
       then have 2:"Tock \<notin> Y"
         using assm2 by auto
      have "Event e \<in> {ea. ea \<noteq> Tock \<and> \<rho> @ [[ea]\<^sub>E] \<in> e \<rightarrow>\<^sub>C P \<or> ea = Tock \<and> \<rho> @ [[X]\<^sub>R, [ea]\<^sub>E] \<in> e \<rightarrow>\<^sub>C P}"
        unfolding PrefixCTT_def using "1" CT0_CT1_empty CT0_P CT1_P by auto
      then have 3: "Event e \<notin> Y"
        using assm2 by auto
      have 4: "Tock \<notin> X"
        using case_assms(1) case_assms2 tocks_mid_refusal by fastforce
      have 5: "Event e \<notin> X"
        using case_assms(1) case_assms2 tocks_mid_refusal by fastforce
      have "X \<union> Y \<subseteq> {x. x \<noteq> Tock \<and> x \<noteq> Event e}"
        using 2 3 4 5 by auto
      then show "\<rho> @ [X \<union> Y]\<^sub>R # \<sigma>' \<in> tocks {x. x \<noteq> Tock \<and> x \<noteq> Event e}"
        using case_assms case_assms2 tocks_mid_refusal_change by fastforce
    next
      assume "\<rho> \<in> tocks {x. x \<noteq> Tock \<and> x \<noteq> Event e}" "s = \<rho>" "X = Xa" "\<sigma> = []"
      then have "Tock \<in> {ea. ea \<noteq> Tock \<and> \<rho> @ [[ea]\<^sub>E] \<in> e \<rightarrow>\<^sub>C P \<or> ea = Tock \<and> \<rho> @ [[X]\<^sub>R, [ea]\<^sub>E] \<in> e \<rightarrow>\<^sub>C P}"
         unfolding PrefixCTT_def using case_assms apply auto
         by (metis (mono_tags, lifting) CollectI subsetI tocks.empty_in_tocks tocks.tock_insert_in_tocks tocks_append_tocks)
       then show "Tock \<in> Y \<Longrightarrow> False"
         using assm2 by auto
    next
      assume "\<rho> \<in> tocks {x. x \<noteq> Tock \<and> x \<noteq> Event e}" "s = \<rho>" "X = Xa" "\<sigma> = []"
      then have "Event e \<in> {ea. ea \<noteq> Tock \<and> \<rho> @ [[ea]\<^sub>E] \<in> e \<rightarrow>\<^sub>C P \<or> ea = Tock \<and> \<rho> @ [[X]\<^sub>R, [ea]\<^sub>E] \<in> e \<rightarrow>\<^sub>C P}"
         unfolding PrefixCTT_def using case_assms CT0_CT1_empty CT0_P CT1_P by auto
      then show "Event e \<in> Y \<Longrightarrow> False"
        using assm2 by auto
    qed
  next
    fix s \<sigma>'
    assume case_assms: "s \<in> tocks {x. x \<noteq> Tock \<and> x \<noteq> Event e}" "\<sigma>' \<in> P" "\<rho> @ [X]\<^sub>R # \<sigma> = s @ [Event e]\<^sub>E # \<sigma>'"
    then have "(\<exists>t. \<rho> = s @ [Event e]\<^sub>E # t \<and> t \<le>\<^sub>C \<sigma>') \<or> (\<exists>t. s = \<rho> @ [X]\<^sub>R # t \<and> t \<le>\<^sub>C \<sigma>)"
      by (simp add: event_refusal_split)
    then show "\<forall>s\<in>tocks {x. x \<noteq> Tock \<and> x \<noteq> Event e}. \<rho> @ [X \<union> Y]\<^sub>R # \<sigma> \<noteq> s \<and> (\<forall>\<sigma>'\<in>P. \<rho> @ [X \<union> Y]\<^sub>R # \<sigma> \<noteq> s @ [Event e]\<^sub>E # \<sigma>') \<Longrightarrow>
            \<exists>s\<in>tocks {x. x \<noteq> Tock \<and> x \<noteq> Event e}. \<exists>Xa. Tock \<notin> Xa \<and> Event e \<notin> Xa \<and> \<rho> @ [X \<union> Y]\<^sub>R # \<sigma> = s @ [[Xa]\<^sub>R]"
    proof auto  
      fix t
      assume case_assms2: "t \<le>\<^sub>C \<sigma>'" "\<rho> = s @ [Event e]\<^sub>E # t"
      then obtain \<rho>' where \<sigma>'_def: "\<sigma>' = \<rho>' @ [X]\<^sub>R # \<sigma>"
        using case_assms(3) by auto
      then have \<rho>_def: "\<rho> = s @ [Event e]\<^sub>E # \<rho>'"
        using case_assms(3) by auto
      then have "{ea. ea \<noteq> Tock \<and> \<rho>' @ [[ea]\<^sub>E] \<in> P \<or> ea = Tock \<and> \<rho>' @ [[X]\<^sub>R, [ea]\<^sub>E] \<in> P}
        \<subseteq> {ea. ea \<noteq> Tock \<and> \<rho> @ [[ea]\<^sub>E] \<in> e \<rightarrow>\<^sub>C P \<or> ea = Tock \<and> \<rho> @ [[X]\<^sub>R, [ea]\<^sub>E] \<in> e \<rightarrow>\<^sub>C P}"
      proof auto
        fix x
        assume "\<rho> = s @ [Event e]\<^sub>E # \<rho>'" "\<rho>' @ [[x]\<^sub>E] \<in> P" "x \<noteq> Tock"
        then show "s @ [Event e]\<^sub>E # \<rho>' @ [[x]\<^sub>E] \<in> e \<rightarrow>\<^sub>C P"
          unfolding PrefixCTT_def using case_assms by auto 
      next
          fix x
        assume "\<rho> = s @ [Event e]\<^sub>E # \<rho>'" "\<rho>' @ [[x]\<^sub>E] \<in> P" "x \<noteq> Tock"
        then show "s @ [Event e]\<^sub>E # \<rho>' @ [[x]\<^sub>E] \<in> e \<rightarrow>\<^sub>C P"
          unfolding PrefixCTT_def using case_assms by auto 
      next
        assume "\<rho> = s @ [Event e]\<^sub>E # \<rho>'" "\<rho>' @ [[X]\<^sub>R, [Tock]\<^sub>E] \<in> P"
        then show "s @ [Event e]\<^sub>E # \<rho>' @ [[X]\<^sub>R, [Tock]\<^sub>E] \<notin> e \<rightarrow>\<^sub>C P \<Longrightarrow> False"
          unfolding PrefixCTT_def using case_assms by auto
       
      next
        assume "\<rho> = s @ [Event e]\<^sub>E # \<rho>'" "\<rho>' @ [[X]\<^sub>R, [Tock]\<^sub>E] \<in> P"
        then show "s @ [Event e]\<^sub>E # \<rho>' @ [[X]\<^sub>R, [Tock]\<^sub>E] \<notin> e \<rightarrow>\<^sub>C P \<Longrightarrow> s @ [Event e]\<^sub>E # \<rho>' @ [[Tock]\<^sub>E] \<in> e \<rightarrow>\<^sub>C P"
          unfolding PrefixCTT_def using case_assms by auto
      qed
      then have 1: "Y \<inter> {ea. ea \<noteq> Tock \<and> \<rho>' @ [[ea]\<^sub>E] \<in> P \<or> ea = Tock \<and> \<rho>' @ [[X]\<^sub>R, [ea]\<^sub>E] \<in> P} = {}"
        using assm2 subsetCE by auto
      have 2: "\<rho>' @ [X]\<^sub>R # \<sigma> \<in> P"
        using \<sigma>'_def case_assms(2) by auto
      have "\<rho>' @ [X \<union> Y]\<^sub>R # \<sigma> \<in> P"
        using 1 2 CT2s_P unfolding CT2s_def by auto
      then show "\<forall>sa\<in>tocks {x. x \<noteq> Tock \<and> x \<noteq> Event e}.
          s @ [Event e]\<^sub>E # t @ [X \<union> Y]\<^sub>R # \<sigma> \<noteq> sa \<and> (\<forall>\<sigma>'\<in>P. s @ [Event e]\<^sub>E # t @ [X \<union> Y]\<^sub>R # \<sigma> \<noteq> sa @ [Event e]\<^sub>E # \<sigma>') \<Longrightarrow>
        \<exists>sa\<in>tocks {x. x \<noteq> Tock \<and> x \<noteq> Event e}. \<exists>Xa. Tock \<notin> Xa \<and> Event e \<notin> Xa \<and> s @ [Event e]\<^sub>E # t @ [X \<union> Y]\<^sub>R # \<sigma> = sa @ [[Xa]\<^sub>R]"
        using \<rho>_def case_assms(1) case_assms2(2) by blast
    next
      fix t
      assume case_assms2: "s = \<rho> @ [X]\<^sub>R # t" "t \<le>\<^sub>C \<sigma>"
      have 1: "\<rho> @ [X]\<^sub>R # t \<in> tocks {x. x \<noteq> Tock \<and> x \<noteq> Event e}"
        using case_assms(1) case_assms2(1) by auto
      then have 2: "\<rho> \<in> tocks {x. x \<noteq> Tock \<and> x \<noteq> Event e}"
        using tocks_mid_refusal_front_in_tocks by auto
      then have 3: "\<rho> @ [[Event e]\<^sub>E] \<in> e \<rightarrow>\<^sub>C P"
        unfolding PrefixCTT_def using CT0_CT1_empty CT0_P CT1_P by fastforce
      have 4: "\<rho> @ [[X]\<^sub>R, [Tock]\<^sub>E] \<in> e \<rightarrow>\<^sub>C P"
        unfolding PrefixCTT_def by (metis (mono_tags, lifting) "1" "2" CollectI UnI2 tocks.empty_in_tocks tocks.tock_insert_in_tocks tocks_append_tocks tocks_mid_refusal)
      have 5: "Y \<subseteq> {x. x \<noteq> Tock \<and> x \<noteq> Event e}"
        using assm2 3 4 by auto
      then have "\<rho> @ [X \<union> Y]\<^sub>R # t \<in> tocks {x. x \<noteq> Tock \<and> x \<noteq> Event e}"
        using "1" tocks_mid_refusal tocks_mid_refusal_change by fastforce
      then show "\<forall>s\<in>tocks {x. x \<noteq> Tock \<and> x \<noteq> Event e}. \<rho> @ [X \<union> Y]\<^sub>R # \<sigma> \<noteq> s \<and> (\<forall>\<sigma>'\<in>P. \<rho> @ [X \<union> Y]\<^sub>R # \<sigma> \<noteq> s @ [Event e]\<^sub>E # \<sigma>') \<Longrightarrow>
        \<exists>s\<in>tocks {x. x \<noteq> Tock \<and> x \<noteq> Event e}. \<exists>Xa. Tock \<notin> Xa \<and> Event e \<notin> Xa \<and> \<rho> @ [X \<union> Y]\<^sub>R # \<sigma> = s @ [[Xa]\<^sub>R]"
        using case_assms(2) case_assms(3) case_assms2(1) by fastforce
    qed
  qed
qed

lemma CT4s_Prefix:
  "CT4s P \<Longrightarrow> CT4s (e \<rightarrow>\<^sub>C P)"
  unfolding PrefixCTT_def CT4s_def
proof auto
  fix s
  assume "s \<in> tocks {x. x \<noteq> Tock \<and> x \<noteq> Event e}"
  then show "\<forall>sa\<in>tocks {x. x \<noteq> Tock \<and> x \<noteq> Event e}. add_Tick_refusal_trace s \<noteq> sa \<and>
      (\<forall>\<sigma>\<in>P. add_Tick_refusal_trace s \<noteq> sa @ [Event e]\<^sub>E # \<sigma>) \<Longrightarrow>
    \<exists>sa\<in>tocks {x. x \<noteq> Tock \<and> x \<noteq> Event e}. \<exists>X. Tock \<notin> X \<and> Event e \<notin> X \<and> add_Tick_refusal_trace s = sa @ [[X]\<^sub>R]"
    apply (erule_tac x="add_Tick_refusal_trace s" in ballE, auto)
    by (metis (mono_tags, lifting) CT4s_def CT4s_tocks cttevent.distinct(3) cttevent.simps(7) mem_Collect_eq)
next
  fix s X
  assume "s \<in> tocks {x. x \<noteq> Tock \<and> x \<noteq> Event e}" "Tock \<notin> X" "Event e \<notin> X"
  then show "\<exists>sa\<in>tocks {x. x \<noteq> Tock \<and> x \<noteq> Event e}.
    \<exists>Xa. Tock \<notin> Xa \<and> Event e \<notin> Xa \<and> add_Tick_refusal_trace (s @ [[X]\<^sub>R]) = sa @ [[Xa]\<^sub>R]"
    apply (rule_tac x="add_Tick_refusal_trace s" in bexI, rule_tac x="X \<union> {Tick}" in exI, auto simp add: add_Tick_refusal_trace_end_refusal)
    by (metis (mono_tags, lifting) CT4s_def CT4s_tocks cttevent.distinct(3) cttevent.simps(7) mem_Collect_eq)
next
  fix s
  assume "s \<in> tocks {x. x \<noteq> Tock \<and> x \<noteq> Event e}"
  then show "\<forall>sa\<in>tocks {x. x \<noteq> Tock \<and> x \<noteq> Event e}. add_Tick_refusal_trace s \<noteq> sa \<and>
      (\<forall>\<sigma>\<in>P. add_Tick_refusal_trace s \<noteq> sa @ [Event e]\<^sub>E # \<sigma>) \<Longrightarrow>
    \<exists>sa\<in>tocks {x. x \<noteq> Tock \<and> x \<noteq> Event e}. \<exists>X. Tock \<notin> X \<and> Event e \<notin> X \<and> add_Tick_refusal_trace s = sa @ [[X]\<^sub>R]"
    apply (erule_tac x="add_Tick_refusal_trace s" in ballE, auto)
    by (metis (mono_tags, lifting) CT4s_def CT4s_tocks cttevent.distinct(3) cttevent.simps(7) mem_Collect_eq)
next
  fix s \<sigma>
  assume "s \<in> tocks {x. x \<noteq> Tock \<and> x \<noteq> Event e}" "\<sigma> \<in> P"
  also assume "\<forall>\<rho>. \<rho> \<in> P \<longrightarrow> add_Tick_refusal_trace \<rho> \<in> P"
  then have "add_Tick_refusal_trace \<sigma> \<in> P"
    using calculation by auto
  then show "\<forall>sa\<in>tocks {x. x \<noteq> Tock \<and> x \<noteq> Event e}. add_Tick_refusal_trace (s @ [Event e]\<^sub>E # \<sigma>) \<noteq> sa \<and>
      (\<forall>\<sigma>'\<in>P. add_Tick_refusal_trace (s @ [Event e]\<^sub>E # \<sigma>) \<noteq> sa @ [Event e]\<^sub>E # \<sigma>') \<Longrightarrow>
    \<exists>sa\<in>tocks {x. x \<noteq> Tock \<and> x \<noteq> Event e}.
      \<exists>X. Tock \<notin> X \<and> Event e \<notin> X \<and> add_Tick_refusal_trace (s @ [Event e]\<^sub>E # \<sigma>) = sa @ [[X]\<^sub>R]"
    using calculation apply (erule_tac x="add_Tick_refusal_trace s" in ballE, auto)
    apply (erule_tac x="add_Tick_refusal_trace \<sigma>" in ballE, auto simp add: add_Tick_refusal_trace_end_event_trace)
    by (metis (mono_tags, lifting) CT4s_def CT4s_tocks cttevent.distinct(3) cttevent.simps(7) mem_Collect_eq)
qed

lemma CT_Prefix:
  assumes "CT P"
  shows "CT (e \<rightarrow>\<^sub>C P)"
  unfolding CT_defs
proof auto
  fix x
  show "x \<in> e \<rightarrow>\<^sub>C P \<Longrightarrow> ttWF x"
    by (meson CT_def PrefixCTT_wf assms)
next
  show "e \<rightarrow>\<^sub>C P = {} \<Longrightarrow> False"
    unfolding PrefixCTT_def using tocks.empty_in_tocks by (blast)
next
  fix \<rho> \<sigma> :: "'a cttobs list"
  show "\<rho> \<lesssim>\<^sub>C \<sigma> \<Longrightarrow> \<sigma> \<in> e \<rightarrow>\<^sub>C P \<Longrightarrow> \<rho> \<in> e \<rightarrow>\<^sub>C P"
    unfolding PrefixCTT_def
  proof auto
    assume assm1: "\<rho> \<lesssim>\<^sub>C \<sigma>"
    assume assm2: "\<forall>s\<in>tocks {x. x \<noteq> Tock \<and> x \<noteq> Event e}. \<rho> \<noteq> s \<and> (\<forall>\<sigma>\<in>P. \<rho> \<noteq> s @ [Event e]\<^sub>E # \<sigma>)"
    assume assm3: "\<sigma> \<in> tocks {x. x \<noteq> Tock \<and> x \<noteq> Event e}"
    obtain s where "s\<in>tocks {x. x \<noteq> Tock \<and> x \<noteq> Event e}" "\<rho> = s \<or> (\<exists>Y. \<rho> = s @ [[Y]\<^sub>R] \<and> Y \<subseteq> {x. x \<noteq> Tock \<and> x \<noteq> Event e})"
      using assm1 assm3 ctt_prefix_subset_tocks by blast
    then show "\<exists>s\<in>tocks {x. x \<noteq> Tock \<and> x \<noteq> Event e}. \<exists>X. Tock \<notin> X \<and> Event e \<notin> X \<and> \<rho> = s @ [[X]\<^sub>R]"
      using assm2 by auto
  next
    fix s X
    assume assm1: "\<rho> \<lesssim>\<^sub>C s @ [[X]\<^sub>R]"
    assume assm2: "\<forall>s\<in>tocks {x. x \<noteq> Tock \<and> x \<noteq> Event e}. \<rho> \<noteq> s \<and> (\<forall>\<sigma>\<in>P. \<rho> \<noteq> s @ [Event e]\<^sub>E # \<sigma>)"
    assume assm3: "s \<in> tocks {x. x \<noteq> Tock \<and> x \<noteq> Event e}"
    assume assm4: "Tock \<notin> X"
    assume assm5: "Event e \<notin> X"
    obtain t Z where "t\<in>tocks {x. x \<noteq> Tock \<and> x \<noteq> Event e}" "\<rho> = t \<or> \<rho> = t @ [[Z]\<^sub>R]" "Z \<subseteq> {x. x \<noteq> Tock \<and> x \<noteq> Event e} \<or> Z \<subseteq> X"
      using assm1 assm3 ctt_prefix_subset_tocks_refusal by blast
    then show "\<exists>s\<in>tocks {x. x \<noteq> Tock \<and> x \<noteq> Event e}. \<exists>X. Tock \<notin> X \<and> Event e \<notin> X \<and> \<rho> = s @ [[X]\<^sub>R]"
      using assm2 assm4 assm5 by auto
  next
    assume assm1: "\<rho> \<lesssim>\<^sub>C \<sigma>"
    assume assm2: "\<forall>s\<in>tocks {x. x \<noteq> Tock \<and> x \<noteq> Event e}. \<rho> \<noteq> s \<and> (\<forall>\<sigma>\<in>P. \<rho> \<noteq> s @ [Event e]\<^sub>E # \<sigma>)"
    assume assm3: "\<sigma> \<in> tocks {x. x \<noteq> Tock \<and> x \<noteq> Event e}"
    obtain s where "s\<in>tocks {x. x \<noteq> Tock \<and> x \<noteq> Event e}" "\<rho> = s \<or> (\<exists>Y. \<rho> = s @ [[Y]\<^sub>R] \<and> Y \<subseteq> {x. x \<noteq> Tock \<and> x \<noteq> Event e})"
      using assm1 assm3 ctt_prefix_subset_tocks by blast
    then show "\<exists>s\<in>tocks {x. x \<noteq> Tock \<and> x \<noteq> Event e}. \<exists>X. Tock \<notin> X \<and> Event e \<notin> X \<and> \<rho> = s @ [[X]\<^sub>R]"
      using assm2 by auto
  next
    fix s \<sigma>'
    assume assm1: "\<rho> \<lesssim>\<^sub>C s @ [Event e]\<^sub>E # \<sigma>'"
    assume assm2: "\<forall>s\<in>tocks {x. x \<noteq> Tock \<and> x \<noteq> Event e}. \<rho> \<noteq> s \<and> (\<forall>\<sigma>\<in>P. \<rho> \<noteq> s @ [Event e]\<^sub>E # \<sigma>)"
    assume assm3: "s \<in> tocks {x. x \<noteq> Tock \<and> x \<noteq> Event e}"
    assume assm4: "\<sigma>' \<in> P"
    thm ctt_prefix_subset_append_split
    from assm1 have "\<rho> \<lesssim>\<^sub>C (s @ [[Event e]\<^sub>E]) @ \<sigma>'"
      by simp
    then obtain a b where a_b_assms: "\<rho> = a @ b" "a \<lesssim>\<^sub>C s @ [[Event e]\<^sub>E]" "b \<lesssim>\<^sub>C \<sigma>'"
      "length a = length (s @ [[Event e]\<^sub>E]) \<and> length [x\<leftarrow>a . x = [Tock]\<^sub>E] = length [x\<leftarrow>(s @ [[Event e]\<^sub>E]) . x = [Tock]\<^sub>E] \<or> b = []"
      using ctt_prefix_subset_append_split by blast
    then obtain s' where s'_assms: "s'\<in>tocks {x. x \<noteq> Tock \<and> x \<noteq> Event e}"
            "s' \<lesssim>\<^sub>C s"
             "a = s' \<or>
              (\<exists>Y. a = s' @ [[Y]\<^sub>R] \<and> Y \<subseteq> {x. x \<noteq> Tock \<and> x \<noteq> Event e} \<and> length [x\<leftarrow>s' . x = [Tock]\<^sub>E] < length [x\<leftarrow>s . x = [Tock]\<^sub>E]) \<or>
              a = s' @ [[Event e]\<^sub>E] \<and> length [x\<leftarrow>s' . x = [Tock]\<^sub>E] = length [x\<leftarrow>s . x = [Tock]\<^sub>E]"
      using ctt_prefix_subset_tocks_event assm3 by blast
    have b_in_P: "b \<in> P"
      using CT1_def CT_CT1 a_b_assms(3) assm4 assms by blast
    from s'_assms have "b \<noteq> [] \<longrightarrow> a = s' @ [[Event e]\<^sub>E] \<and> length [x\<leftarrow>s' . x = [Tock]\<^sub>E] = length [x\<leftarrow>s . x = [Tock]\<^sub>E]"
      using a_b_assms(4) ctt_prefix_subset_length by (auto, fastforce+)
    then have b_empty: "b = []"
      using b_in_P a_b_assms(1) assm2 s'_assms(1) by fastforce
    then have "\<exists>Y. a = s' @ [[Y]\<^sub>R] \<and> Y \<subseteq> {x. x \<noteq> Tock \<and> x \<noteq> Event e} \<and> length [x\<leftarrow>s' . x = [Tock]\<^sub>E] < length [x\<leftarrow>s . x = [Tock]\<^sub>E]"
      using a_b_assms(1) assm2 b_in_P s'_assms(1) s'_assms(3) by blast
    then show "\<exists>s\<in>tocks {x. x \<noteq> Tock \<and> x \<noteq> Event e}. \<exists>X. Tock \<notin> X \<and> Event e \<notin> X \<and> \<rho> = s @ [[X]\<^sub>R]"
      apply (auto, rule_tac x="s'" in bexI, rule_tac x="Y" in exI)
      using b_empty a_b_assms(1) s'_assms(1) by blast+
  qed
next
  fix \<rho> X Y
  assume assm1: "Y \<inter> {ea. ea \<noteq> Tock \<and> \<rho> @ [[ea]\<^sub>E] \<in> e \<rightarrow>\<^sub>C P \<or> ea = Tock \<and> \<rho> @ [[X]\<^sub>R, [ea]\<^sub>E] \<in> e \<rightarrow>\<^sub>C P} = {}"
  assume "\<rho> @ [[X]\<^sub>R] \<in> e \<rightarrow>\<^sub>C P"
  then have "(\<rho> \<in> tocks {x. x \<noteq> Tock \<and> x \<noteq> Event e} \<and> Tock \<notin> X \<and> Event e \<notin> X) \<or>
    (\<exists> s \<sigma>. s \<in> tocks {x. x \<noteq> Tock \<and> x \<noteq> Event e} \<and> \<sigma> \<in> P \<and> \<rho> @ [[X]\<^sub>R] = s @ [Event e]\<^sub>E # \<sigma>)"
    unfolding PrefixCTT_def using end_refusal_notin_tocks by auto
  then show "\<rho> @ [[X \<union> Y]\<^sub>R] \<in> e \<rightarrow>\<^sub>C P"
  proof auto
    assume assm2: "\<rho> \<in> tocks {x. x \<noteq> Tock \<and> x \<noteq> Event e}"
    assume assm3: "Tock \<notin> X"
    assume assm4: "Event e \<notin> X"

    have "Tock \<in> {ea. ea \<noteq> Tock \<and> \<rho> @ [[ea]\<^sub>E] \<in> e \<rightarrow>\<^sub>C P \<or> ea = Tock \<and> \<rho> @ [[X]\<^sub>R, [ea]\<^sub>E] \<in> e \<rightarrow>\<^sub>C P}"
      unfolding PrefixCTT_def by (auto, smt assm2 assm3 assm4 mem_Collect_eq subset_iff tocks.simps tocks_append_tocks)
    then have 1: "Tock \<notin> Y"
      using assm1 by auto
    have "Event e \<in> {ea. ea \<noteq> Tock \<and> \<rho> @ [[ea]\<^sub>E] \<in> e \<rightarrow>\<^sub>C P \<or> ea = Tock \<and> \<rho> @ [[X]\<^sub>R, [ea]\<^sub>E] \<in> e \<rightarrow>\<^sub>C P}"
      unfolding PrefixCTT_def apply (auto)
      using CT_empty assm2 assms by blast
    then have 2: "Event e \<notin> Y"
      using assm1 by auto
    show "\<rho> @ [[X \<union> Y]\<^sub>R] \<in> e \<rightarrow>\<^sub>C P"
      unfolding PrefixCTT_def using 1 2 assm2 assm3 assm4 by (auto)
  next
    fix s \<sigma>
    assume assm2: "s \<in> tocks {x. x \<noteq> Tock \<and> x \<noteq> Event e}"
    assume assm3: "\<sigma> \<in> P"
    assume assm4: "\<rho> @ [[X]\<^sub>R] = s @ [Event e]\<^sub>E # \<sigma>"
    obtain \<sigma>' where \<sigma>'_assm: "\<sigma> = \<sigma>' @ [[X]\<^sub>R]"
      by (metis append_butlast_last_id assm4 cttobs.distinct(1) last.simps last_appendR list.distinct(1))
    have \<rho>_def: "\<rho> = s @ [Event e]\<^sub>E # \<sigma>'"
      using \<sigma>'_assm assm4 by auto
    have 1: "\<And>x. s @ [Event e]\<^sub>E # \<sigma>' @ [[x]\<^sub>E] \<notin> tocks {x. x \<noteq> Tock \<and> x \<noteq> Event e}"
      using mid_event_notin_tocks by force
    have 2: "s @ [Event e]\<^sub>E # \<sigma>' @ [[X]\<^sub>R, [Tock]\<^sub>E] \<notin> tocks {x. x \<noteq> Tock \<and> x \<noteq> Event e}"
      using mid_event_notin_tocks by force
    have "{ea. ea \<noteq> Tock \<and> \<sigma>' @ [[ea]\<^sub>E] \<in> P \<or> ea = Tock \<and> \<sigma>' @ [[X]\<^sub>R, [ea]\<^sub>E] \<in> P} = {ea. ea \<noteq> Tock \<and> \<rho> @ [[ea]\<^sub>E] \<in> e \<rightarrow>\<^sub>C P \<or> ea = Tock \<and> \<rho> @ [[X]\<^sub>R, [ea]\<^sub>E] \<in> e \<rightarrow>\<^sub>C P}"
      unfolding PrefixCTT_def apply auto
      using \<sigma>'_assm assm2 assm4  apply (auto simp add: 1 2)
      by (metis (lifting) append_Cons append_Nil equal_traces_imp_equal_tocks)+
    then have "Y \<inter> {ea. ea \<noteq> Tock \<and> \<sigma>' @ [[ea]\<^sub>E] \<in> P \<or> ea = Tock \<and> \<sigma>' @ [[X]\<^sub>R, [ea]\<^sub>E] \<in> P} = {}"
      using assm1 by auto
    then have "\<sigma>' @ [[X \<union> Y]\<^sub>R] \<in> P"
      using \<sigma>'_assm assm3 assms by (auto simp add: CT2_def CT_def)
    then show "\<rho> @ [[X \<union> Y]\<^sub>R] \<in> e \<rightarrow>\<^sub>C P"
      unfolding PrefixCTT_def using \<rho>_def assm2 by auto
  qed
next
  fix x
  have "\<forall>x\<in>P. CT3_trace x"
    using CT3_def CT_CT3 assms by blast
  also have "\<forall>x \<in> tocks {x. x \<noteq> Tock \<and> x \<noteq> Event e}. CT3_trace x"
    by (metis (mono_tags, lifting) CT3_def CT3_tocks mem_Collect_eq) 
  then show "x \<in> e \<rightarrow>\<^sub>C P \<Longrightarrow> CT3_trace x"
    unfolding PrefixCTT_def using calculation apply auto
    using CT3_append CT3_trace.simps(2) ttWF.simps(2) apply blast
    by (metis (no_types, lifting) CT3_append CT3_trace.simps(2) CT3_trace.simps(4) CT_wf assms ttWF.elims(2) ttWF.simps(4)) 
qed

definition TockPrefixCTT :: "'e cttobs list set \<Rightarrow> 'e cttobs list set" ("tock \<rightarrow>\<^sub>C _") where
  "TockPrefixCTT P = {t. \<exists> s\<in>tocks({x. x \<noteq> Tock \<and> x \<noteq> Tock}). t = s \<or> (\<exists> X. Tock \<notin> X \<and> Tock \<notin> X \<and> t = s @ [[X]\<^sub>R])}
     \<union> {t. \<exists> s\<in>tocks({x. x \<noteq> Tock \<and> x \<noteq> Tock}). t = s \<or> (\<exists> \<sigma>\<in>P. \<exists> X. Tock \<notin> X \<and> t = s @ [[X]\<^sub>R, [Tock]\<^sub>E] @ \<sigma>)}"

lemma TockPrefixCTT_wf: "(\<forall> t\<in>P. ttWF t) \<Longrightarrow> \<forall> t\<in>(tock \<rightarrow>\<^sub>C P). ttWF t"
  unfolding TockPrefixCTT_def using tocks_wf apply auto
  using ttWF.simps(2) ttWF.simps(5) tocks_append_wf by blast+

lemma CT0_TockPrefixCTT: "CT0 P \<Longrightarrow> CT0 (tock \<rightarrow>\<^sub>C P)"
  unfolding TockPrefixCTT_def CT0_def apply auto
  using tocks.simps by blast

lemma CT1_TockPrefixCTT:
  assumes "CT1 P"
  shows "CT1 (tock \<rightarrow>\<^sub>C P)"
  unfolding CT1_def TockPrefixCTT_def
proof auto
  fix \<rho> s :: "'a cttobs list"
  show "\<rho> \<lesssim>\<^sub>C s \<Longrightarrow> s \<in> tocks {x. x \<noteq> Tock} \<Longrightarrow>
    \<forall>s\<in>tocks {x. x \<noteq> Tock}. \<rho> \<noteq> s \<and> (\<forall>\<sigma>\<in>P. \<forall>X. Tock \<in> X \<or> \<rho> \<noteq> s @ [X]\<^sub>R # [Tock]\<^sub>E # \<sigma>) \<Longrightarrow>
    \<exists>s\<in>tocks {x. x \<noteq> Tock}. \<exists>X. Tock \<notin> X \<and> \<rho> = s @ [[X]\<^sub>R]"
    using ctt_prefix_subset_tocks2[where s=s, where t=\<rho>, where X="{x. x \<noteq> Tock}"] by auto
next
  fix \<rho> s X
  show "\<rho> \<lesssim>\<^sub>C s @ [[X]\<^sub>R] \<Longrightarrow>
    \<forall>s\<in>tocks {x. x \<noteq> Tock}. \<rho> \<noteq> s \<and> (\<forall>\<sigma>\<in>P. \<forall>X. Tock \<in> X \<or> \<rho> \<noteq> s @ [X]\<^sub>R # [Tock]\<^sub>E # \<sigma>) \<Longrightarrow>
    s \<in> tocks {x. x \<noteq> Tock} \<Longrightarrow> Tock \<notin> X \<Longrightarrow> \<exists>s\<in>tocks {x. x \<noteq> Tock}. \<exists>X. Tock \<notin> X \<and> \<rho> = s @ [[X]\<^sub>R]"
    using ctt_prefix_subset_tocks_refusal2[where s=s, where \<rho>=\<rho>, where X="{x. x \<noteq> Tock}", where Y=X] by auto
next
  fix \<rho> s
  show "\<rho> \<lesssim>\<^sub>C s \<Longrightarrow>
    \<forall>s\<in>tocks {x. x \<noteq> Tock}. \<rho> \<noteq> s \<and> (\<forall>\<sigma>\<in>P. \<forall>X. Tock \<in> X \<or> \<rho> \<noteq> s @ [X]\<^sub>R # [Tock]\<^sub>E # \<sigma>) \<Longrightarrow>
    s \<in> tocks {x. x \<noteq> Tock} \<Longrightarrow> \<exists>s\<in>tocks {x. x \<noteq> Tock}. \<exists>X. Tock \<notin> X \<and> \<rho> = s @ [[X]\<^sub>R]"
    using ctt_prefix_subset_tocks2[where s=s, where t=\<rho>, where X="{x. x \<noteq> Tock}"] by auto
next
  fix \<rho> s \<sigma>' X
  assume case_assms: "\<rho> \<lesssim>\<^sub>C s @ [X]\<^sub>R # [Tock]\<^sub>E # \<sigma>'" "s \<in> tocks {x. x \<noteq> Tock}" "\<sigma>' \<in> P" "Tock \<notin> X"
  have "\<rho> \<lesssim>\<^sub>C s @ [[X]\<^sub>R, [Tock]\<^sub>E] \<or> (\<exists>t'. t' \<lesssim>\<^sub>C \<sigma>' \<and> \<rho> \<subseteq>\<^sub>C (s @ [[X]\<^sub>R, [Tock]\<^sub>E]) @ t')"
    using case_assms ctt_prefix_subset_concat[where r="\<rho>", where s="s @ [[X]\<^sub>R, [Tock]\<^sub>E]", where t=\<sigma>'] by auto
  then show "\<forall>s\<in>tocks {x. x \<noteq> Tock}. \<rho> \<noteq> s \<and> (\<forall>\<sigma>\<in>P. \<forall>X. Tock \<in> X \<or> \<rho> \<noteq> s @ [X]\<^sub>R # [Tock]\<^sub>E # \<sigma>) \<Longrightarrow>
    \<exists>s\<in>tocks {x. x \<noteq> Tock}. \<exists>X. Tock \<notin> X \<and> \<rho> = s @ [[X]\<^sub>R]"
  proof auto
    have "s @ [[X]\<^sub>R, [Tock]\<^sub>E] \<in> tocks {x. x \<noteq> Tock}"
      by (metis (mono_tags, lifting) case_assms(2) case_assms(4) mem_Collect_eq subsetI tocks.simps tocks_append_tocks)
    then show "\<forall>s\<in>tocks {x. x \<noteq> Tock}. \<rho> \<noteq> s \<and> (\<forall>\<sigma>\<in>P. \<forall>X. Tock \<in> X \<or> \<rho> \<noteq> s @ [X]\<^sub>R # [Tock]\<^sub>E # \<sigma>) \<Longrightarrow>
      \<rho> \<lesssim>\<^sub>C s @ [[X]\<^sub>R, [Tock]\<^sub>E] \<Longrightarrow> \<exists>s\<in>tocks {x. x \<noteq> Tock}. \<exists>X. Tock \<notin> X \<and> \<rho> = s @ [[X]\<^sub>R]"
      using ctt_prefix_subset_tocks2[where s="s @ [[X]\<^sub>R, [Tock]\<^sub>E]", where t=\<rho>, where X="{x. x \<noteq> Tock}"] by auto
  next
    fix t'
    assume case_assms2: "t' \<lesssim>\<^sub>C \<sigma>'" "\<rho> \<subseteq>\<^sub>C s @ [X]\<^sub>R # [Tock]\<^sub>E # t'"
    then obtain s' t'' Y where obtain1:  "\<rho> = s' @ t'' \<and> s' \<subseteq>\<^sub>C s @ [[X]\<^sub>R, [Tock]\<^sub>E] \<and> t'' \<subseteq>\<^sub>C t'"
      using ctt_subset_split[where r=\<rho>, where s="s @ [[X]\<^sub>R, [Tock]\<^sub>E]", where t=t'] by auto
    then obtain s'' Y where obtain2: "s' = s'' @ [[Y]\<^sub>R, [Tock]\<^sub>E] \<and> s'' \<subseteq>\<^sub>C s \<and> Y \<subseteq> X"
      using ctt_subset_split[where r=s', where s=s, where t="[[X]\<^sub>R, [Tock]\<^sub>E]"] apply auto
      by (case_tac t'a rule:ttWF.cases, auto, metis ctt_subset.simps(6) neq_Nil_conv)
    have "t'' \<in> P"
      by (meson CT1_def assms case_assms(3) case_assms2(1) ctt_subset_imp_prefix_subset obtain1)
    then show "\<forall>s\<in>tocks {x. x \<noteq> Tock}. \<rho> \<noteq> s \<and> (\<forall>\<sigma>\<in>P. \<forall>X. Tock \<in> X \<or> \<rho> \<noteq> s @ [X]\<^sub>R # [Tock]\<^sub>E # \<sigma>) \<Longrightarrow>
      \<exists>s\<in>tocks {x. x \<noteq> Tock}. \<exists>X. Tock \<notin> X \<and> \<rho> = s @ [[X]\<^sub>R]"
      by (smt obtain2 append.assoc append_Cons case_assms(2) case_assms(4) contra_subsetD ctt_subset_in_tocks obtain1 self_append_conv2)
  qed
qed

thm TockPrefixCTT_def

lemma CT2s_TockPrefix: 
  assumes "CT2s P"
  shows "CT2s (tock \<rightarrow>\<^sub>C P)"
  unfolding CT2s_def
proof auto
  fix \<rho> \<sigma> X Y
  assume assm1: "\<rho> @ [X]\<^sub>R # \<sigma> \<in> tock \<rightarrow>\<^sub>C P"
  assume assm2: "Y \<inter> {e. e \<noteq> Tock \<and> \<rho> @ [[e]\<^sub>E] \<in> tock \<rightarrow>\<^sub>C P \<or> e = Tock \<and> \<rho> @ [[X]\<^sub>R, [e]\<^sub>E] \<in> tock \<rightarrow>\<^sub>C P} = {}"
  show "\<rho> @ [X \<union> Y]\<^sub>R # \<sigma> \<in> tock \<rightarrow>\<^sub>C P"
    using assm1 unfolding TockPrefixCTT_def
  proof auto
    assume case_assms: "\<rho> @ [X]\<^sub>R # \<sigma> \<in> tocks {x. x \<noteq> Tock}"
    then have 1: "\<rho> \<in> tocks {x. x \<noteq> Tock}"
      using tocks_mid_refusal_front_in_tocks by blast
    then have "Tock \<in> {ea. ea \<noteq> Tock \<and> \<rho> @ [[ea]\<^sub>E] \<in> tock \<rightarrow>\<^sub>C P \<or> ea = Tock \<and> \<rho> @ [[X]\<^sub>R, [ea]\<^sub>E] \<in> tock \<rightarrow>\<^sub>C P}"
      unfolding TockPrefixCTT_def apply auto
      by (metis (no_types, lifting) case_assms tocks.empty_in_tocks tocks.tock_insert_in_tocks tocks_append_tocks tocks_mid_refusal)
    then have 2: "Tock \<notin> Y"
      using assm2 by blast
    then have "Tock \<in> {ea. ea \<noteq> Tock \<and> \<rho> @ [[ea]\<^sub>E] \<in> tock \<rightarrow>\<^sub>C P \<or> ea = Tock \<and> \<rho> @ [[X]\<^sub>R, [ea]\<^sub>E] \<in> tock \<rightarrow>\<^sub>C P}"
      using 1 unfolding TockPrefixCTT_def apply auto
      by (metis case_assms tocks.empty_in_tocks tocks.tock_insert_in_tocks tocks_append_tocks tocks_mid_refusal)
    have 3: "Tock \<notin> X"
      using case_assms tocks_mid_refusal by fastforce
    then have "X \<union> Y \<subseteq> {x. x \<noteq> Tock}"
      using 1 2 3 by auto
    then show "\<forall>s\<in>tocks {x. x \<noteq> Tock}. \<rho> @ [X \<union> Y]\<^sub>R # \<sigma> \<noteq> s \<and> (\<forall>\<sigma>'\<in>P. \<forall>Xa. Tock \<in> Xa \<or> \<rho> @ [X \<union> Y]\<^sub>R # \<sigma> \<noteq> s @ [Xa]\<^sub>R # [Tock]\<^sub>E # \<sigma>') \<Longrightarrow>
      \<exists>s\<in>tocks {x. x \<noteq> Tock}. \<exists>Xa. Tock \<notin> Xa \<and> \<rho> @ [X \<union> Y]\<^sub>R # \<sigma> = s @ [[Xa]\<^sub>R]"
      using case_assms apply (erule_tac x="\<rho> @ [X \<union> Y]\<^sub>R # \<sigma>" in ballE, auto)
      using tocks_mid_refusal_change by fastforce
  next
    assume case_assms: "\<rho> @ [X]\<^sub>R # \<sigma> \<in> tocks {x. x \<noteq> Tock}"
    then have 1: "\<rho> \<in> tocks {x. x \<noteq> Tock}"
      using tocks_mid_refusal_front_in_tocks by blast
    then have "Tock \<in> {ea. ea \<noteq> Tock \<and> \<rho> @ [[ea]\<^sub>E] \<in> tock \<rightarrow>\<^sub>C P \<or> ea = Tock \<and> \<rho> @ [[X]\<^sub>R, [ea]\<^sub>E] \<in> tock \<rightarrow>\<^sub>C P}"
      unfolding TockPrefixCTT_def apply auto
      by (metis (no_types, lifting) case_assms tocks.empty_in_tocks tocks.tock_insert_in_tocks tocks_append_tocks tocks_mid_refusal)
    then have 2: "Tock \<notin> Y"
      using assm2 by blast
    have 3: "Tock \<notin> X"
      using case_assms tocks_mid_refusal by fastforce
    then have "X \<union> Y \<subseteq> {x. x \<noteq> Tock}"
      using 1 2 3 by auto
    then show "\<forall>s\<in>tocks {x. x \<noteq> Tock}. \<rho> @ [X \<union> Y]\<^sub>R # \<sigma> \<noteq> s \<and> (\<forall>\<sigma>'\<in>P. \<forall>Xa. Tock \<in> Xa \<or> \<rho> @ [X \<union> Y]\<^sub>R # \<sigma> \<noteq> s @ [Xa]\<^sub>R # [Tock]\<^sub>E # \<sigma>') \<Longrightarrow>
      \<rho> @ [X]\<^sub>R # \<sigma> \<in> tocks {x. x \<noteq> Tock} \<Longrightarrow> \<exists>s\<in>tocks {x. x \<noteq> Tock}. \<exists>Xa. Tock \<notin> Xa \<and> \<rho> @ [X \<union> Y]\<^sub>R # \<sigma> = s @ [[Xa]\<^sub>R]"
      using case_assms apply (erule_tac x="\<rho> @ [X \<union> Y]\<^sub>R # \<sigma>" in ballE, auto)
      using tocks_mid_refusal_change by fastforce
  next
    fix s Xa
    assume case_assms: "s \<in> tocks {x. x \<noteq> Tock}" "Tock \<notin> Xa" "\<rho> @ [X]\<^sub>R # \<sigma> = s @ [[Xa]\<^sub>R]"
    then have "(\<exists> \<sigma>'. s = \<rho> @ [X]\<^sub>R # \<sigma>') \<or> (s = \<rho> \<and> X = Xa \<and> \<sigma> = [])"
      by (metis append.right_neutral butlast.simps(2) butlast_append cttobs.inject(2) last_snoc list.distinct(1))
    then show "\<exists>s\<in>tocks {x. x \<noteq> Tock}. \<exists>Xa. Tock \<notin> Xa \<and> \<rho> @ [X \<union> Y]\<^sub>R # \<sigma> = s @ [[Xa]\<^sub>R]"
      using case_assms
    proof auto
      fix \<sigma>'
      assume case_assms2: "s = \<rho> @ [X]\<^sub>R # \<sigma>'"
      have 1: "\<rho> \<in> tocks {x. x \<noteq> Tock}"
        using case_assms(1) case_assms2 tocks_mid_refusal_front_in_tocks by auto
      have "Tock \<in> {ea. ea \<noteq> Tock \<and> \<rho> @ [[ea]\<^sub>E] \<in> tock \<rightarrow>\<^sub>C P \<or> ea = Tock \<and> \<rho> @ [[X]\<^sub>R, [ea]\<^sub>E] \<in> tock \<rightarrow>\<^sub>C P}"
         unfolding TockPrefixCTT_def apply auto
         using case_assms case_assms2 1 by (simp add: empty_in_tocks tock_insert_in_tocks tocks_append_tocks tocks_mid_refusal)
       then have 2:"Tock \<notin> Y"
         using assm2 by auto
      have 3: "Tock \<notin> X"
        using case_assms(1) case_assms2 tocks_mid_refusal by fastforce
      have "X \<union> Y \<subseteq> {x. x \<noteq> Tock}"
        using 2 3 by auto
      then show "\<rho> @ [X \<union> Y]\<^sub>R # \<sigma>' \<in> tocks {x. x \<noteq> Tock}"
        using case_assms case_assms2 tocks_mid_refusal_change by fastforce
    next
      assume "\<rho> \<in> tocks {x. x \<noteq> Tock}" "s = \<rho>" "X = Xa" "\<sigma> = []"
      then have "Tock \<in> {ea. ea \<noteq> Tock \<and> \<rho> @ [[ea]\<^sub>E] \<in> tock \<rightarrow>\<^sub>C P \<or> ea = Tock \<and> \<rho> @ [[X]\<^sub>R, [ea]\<^sub>E] \<in> tock \<rightarrow>\<^sub>C P}"
         unfolding TockPrefixCTT_def using case_assms apply auto
         by (metis (mono_tags, lifting) CollectI subsetI tocks.empty_in_tocks tocks.tock_insert_in_tocks tocks_append_tocks)
       then show "Tock \<in> Y \<Longrightarrow> False"
         using assm2 by auto
    qed
  next
    fix s \<sigma>' Xa
    assume case_assms: "s \<in> tocks {x. x \<noteq> Tock}" "\<sigma>' \<in> P" "\<rho> @ [X]\<^sub>R # \<sigma> = s @ [Xa]\<^sub>R # [Tock]\<^sub>E # \<sigma>'" "Tock \<notin> Xa"
    then have "(\<exists>t2'. \<rho> = (s @ [[Xa]\<^sub>R]) @ [Tock]\<^sub>E # t2' \<and> t2' \<le>\<^sub>C \<sigma>') \<or> (\<exists>s2'. s @ [[Xa]\<^sub>R] = \<rho> @ [X]\<^sub>R # s2' \<and> s2' \<le>\<^sub>C \<sigma>)"
      using event_refusal_split[where ?s1.0=\<rho>, where ?s2.0=\<sigma>, where X=X, where ?t1.0="s @ [[Xa]\<^sub>R]", where e=Tock, where ?t2.0=\<sigma>']
      by (simp)
    then show "\<forall>s\<in>tocks {x. x \<noteq> Tock}.
        \<rho> @ [X \<union> Y]\<^sub>R # \<sigma> \<noteq> s \<and> (\<forall>\<sigma>'\<in>P. \<forall>Xa. Tock \<in> Xa \<or> \<rho> @ [X \<union> Y]\<^sub>R # \<sigma> \<noteq> s @ [Xa]\<^sub>R # [Tock]\<^sub>E # \<sigma>') \<Longrightarrow>
      \<rho> @ [X]\<^sub>R # \<sigma> = s @ [Xa]\<^sub>R # [Tock]\<^sub>E # \<sigma>' \<Longrightarrow> \<exists>s\<in>tocks {x. x \<noteq> Tock}. \<exists>Xa. Tock \<notin> Xa \<and> \<rho> @ [X \<union> Y]\<^sub>R # \<sigma> = s @ [[Xa]\<^sub>R]"
    proof auto
      fix t2'
      assume case_assms2: "\<rho> = s @ [Xa]\<^sub>R # [Tock]\<^sub>E # t2'" "\<sigma>' = t2' @ [X]\<^sub>R # \<sigma>"
      then have "{ea. ea \<noteq> Tock \<and> t2' @ [[ea]\<^sub>E] \<in> P \<or> ea = Tock \<and> t2' @ [[X]\<^sub>R, [ea]\<^sub>E] \<in> P}
        \<subseteq> {ea. ea \<noteq> Tock \<and> \<rho> @ [[ea]\<^sub>E] \<in> tock \<rightarrow>\<^sub>C P \<or> ea = Tock \<and> \<rho> @ [[X]\<^sub>R, [ea]\<^sub>E] \<in> tock \<rightarrow>\<^sub>C P}"
      proof auto
        fix x :: "'a cttevent"
        assume "\<rho> = s @ [Xa]\<^sub>R # [Tock]\<^sub>E # t2'" "\<sigma>' = t2' @ [X]\<^sub>R # \<sigma>" "t2' @ [[x]\<^sub>E] \<in> P" "x \<noteq> Tock"
        then show "s @ [Xa]\<^sub>R # [Tock]\<^sub>E # t2' @ [[x]\<^sub>E] \<in> tock \<rightarrow>\<^sub>C P"
          unfolding TockPrefixCTT_def using case_assms by auto
      next
        fix x :: "'a cttevent"
        assume "\<rho> = s @ [Xa]\<^sub>R # [Tock]\<^sub>E # t2'" "\<sigma>' = t2' @ [X]\<^sub>R # \<sigma>" "t2' @ [[x]\<^sub>E] \<in> P" "x \<noteq> Tock"
        then show "s @ [Xa]\<^sub>R # [Tock]\<^sub>E # t2' @ [[x]\<^sub>E] \<in> tock \<rightarrow>\<^sub>C P"
          unfolding TockPrefixCTT_def using case_assms by auto
      next
        assume "\<rho> = s @ [Xa]\<^sub>R # [Tock]\<^sub>E # t2'" "t2' @ [[X]\<^sub>R, [Tock]\<^sub>E] \<in> P"
        then show "s @ [Xa]\<^sub>R # [Tock]\<^sub>E # t2' @ [[X]\<^sub>R, [Tock]\<^sub>E] \<notin> tock \<rightarrow>\<^sub>C P \<Longrightarrow> False"
          unfolding TockPrefixCTT_def using case_assms by auto
      next
        assume "\<rho> = s @ [Xa]\<^sub>R # [Tock]\<^sub>E # t2'" "t2' @ [[X]\<^sub>R, [Tock]\<^sub>E] \<in> P"
        then show "s @ [Xa]\<^sub>R # [Tock]\<^sub>E # t2' @ [[X]\<^sub>R, [Tock]\<^sub>E] \<notin> tock \<rightarrow>\<^sub>C P \<Longrightarrow>
          s @ [Xa]\<^sub>R # [Tock]\<^sub>E # t2' @ [[Tock]\<^sub>E] \<in> tock \<rightarrow>\<^sub>C P"
          unfolding TockPrefixCTT_def using case_assms by auto
      qed
      then have 1: "Y \<inter> {ea. ea \<noteq> Tock \<and> t2' @ [[ea]\<^sub>E] \<in> P \<or> ea = Tock \<and> t2' @ [[X]\<^sub>R, [ea]\<^sub>E] \<in> P} = {}"
        using assm2 subsetCE by auto
      have 2: "t2' @ [X]\<^sub>R # \<sigma> \<in> P"
        using case_assms(2) case_assms2 by auto
      have "t2' @ [X \<union> Y]\<^sub>R # \<sigma> \<in> P"
        using 1 2 assms unfolding CT2s_def by auto
      then show "\<forall>sa\<in>tocks {x. x \<noteq> Tock}. s @ [Xa]\<^sub>R # [Tock]\<^sub>E # t2' @ [X \<union> Y]\<^sub>R # \<sigma> \<noteq> sa \<and>
          (\<forall>\<sigma>'\<in>P. \<forall>Xaa. Tock \<in> Xaa \<or> s @ [Xa]\<^sub>R # [Tock]\<^sub>E # t2' @ [X \<union> Y]\<^sub>R # \<sigma> \<noteq> sa @ [Xaa]\<^sub>R # [Tock]\<^sub>E # \<sigma>') \<Longrightarrow>
        \<exists>sa\<in>tocks {x. x \<noteq> Tock}. \<exists>Xaa. Tock \<notin> Xaa \<and> s @ [Xa]\<^sub>R # [Tock]\<^sub>E # t2' @ [X \<union> Y]\<^sub>R # \<sigma> = sa @ [[Xaa]\<^sub>R]"
        using case_assms case_assms2 by blast
    next
      fix s2'
      assume case_assms2: "\<rho> @ [X]\<^sub>R # \<sigma> = s @ [Xa]\<^sub>R # [Tock]\<^sub>E # \<sigma>'" "s @ [[Xa]\<^sub>R] = \<rho> @ [X]\<^sub>R # s2'" "s2' \<le>\<^sub>C \<sigma>"
      obtain s2'' where s2''_cases: "s2' = s2'' @ [[Xa]\<^sub>R] \<or> (s2' = [] \<and> Xa = X)"
        by (metis append_butlast_last_id case_assms2(2) cttobs.inject(2) last.simps last_appendR list.distinct(1))
      then have 1: "\<rho> @ [X]\<^sub>R # s2'' \<in> tocks {x. x \<noteq> Tock} \<or> \<rho> \<in> tocks {x. x \<noteq> Tock}"
        using case_assms case_assms2 by auto
      then have 2: "\<rho> \<in> tocks {x. x \<noteq> Tock}"
        using tocks_mid_refusal_front_in_tocks by auto
      have 3: "\<rho> @ [[X]\<^sub>R, [Tock]\<^sub>E] \<in> tock \<rightarrow>\<^sub>C P"
        unfolding TockPrefixCTT_def using s2''_cases apply auto
        apply (metis (no_types, lifting) "2" Nil_is_append_conv butlast.simps(2) butlast_append butlast_snoc case_assms(1) case_assms2(2) tocks.empty_in_tocks tocks.tock_insert_in_tocks tocks_append_tocks tocks_mid_refusal)
        by (metis (mono_tags, lifting) "2" CollectI case_assms(4) subsetI tocks.empty_in_tocks tocks.tock_insert_in_tocks tocks_append_tocks)
      have 5: "Y \<subseteq> {x. x \<noteq> Tock}"
        using assm2 3 by auto
      then have 6: "X \<union> Y \<subseteq> {x. x \<noteq> Tock}"
        by (smt Cons_eq_appendI append_assoc append_same_eq case_assms(1) case_assms(4) case_assms2(2) mem_Collect_eq s2''_cases subsetI sup.boundedI tocks_mid_refusal)
      show "\<forall>s\<in>tocks {x. x \<noteq> Tock}.
          \<rho> @ [X \<union> Y]\<^sub>R # \<sigma> \<noteq> s \<and> (\<forall>\<sigma>'\<in>P. \<forall>Xa. Tock \<in> Xa \<or> \<rho> @ [X \<union> Y]\<^sub>R # \<sigma> \<noteq> s @ [Xa]\<^sub>R # [Tock]\<^sub>E # \<sigma>') \<Longrightarrow>
        \<exists>s\<in>tocks {x. x \<noteq> Tock}. \<exists>Xa. Tock \<notin> Xa \<and> \<rho> @ [X \<union> Y]\<^sub>R # \<sigma> = s @ [[Xa]\<^sub>R]"
        using s2''_cases
      proof auto
        assume case_assms3: "s2' = s2'' @ [[Xa]\<^sub>R]"
        obtain s2''' where s2'''_def: "s2'' = [Tock]\<^sub>E # s2'''"
          apply (cases s2'' rule:ttWF.cases, auto)
          using case_assms(1) case_assms2(2) case_assms3 end_refusal_notin_tocks apply force
          using "2" case_assms(1) case_assms2(2) case_assms3 ttWF.simps(2) tocks_append_wf tocks_append_wf2 apply fastforce
          using "2" case_assms(1) case_assms2(2) case_assms3 tocks_append_nontocks tocks_wf by fastforce+
        then have "s2''' \<in> tocks {x. x \<noteq> Tock}"
          by (metis (no_types, lifting) "2" Nil_is_append_conv butlast.simps(2) butlast_append butlast_snoc case_assms(1) case_assms2(2) case_assms3 list.distinct(1) list.sel(3) tocks.cases tocks_append_nontocks)
        then show "\<forall>s\<in>tocks {x. x \<noteq> Tock}.
            \<rho> @ [X \<union> Y]\<^sub>R # \<sigma> \<noteq> s \<and> (\<forall>\<sigma>'\<in>P. \<forall>Xa. Tock \<in> Xa \<or> \<rho> @ [X \<union> Y]\<^sub>R # \<sigma> \<noteq> s @ [Xa]\<^sub>R # [Tock]\<^sub>E # \<sigma>') \<Longrightarrow>
          \<exists>s\<in>tocks {x. x \<noteq> Tock}. \<exists>Xa. Tock \<notin> Xa \<and> \<rho> @ [X \<union> Y]\<^sub>R # \<sigma> = s @ [[Xa]\<^sub>R]"
          apply (erule_tac x="\<rho> @ [X \<union> Y]\<^sub>R # [Tock]\<^sub>E # s2'''" in ballE, auto)
          apply (erule_tac x="\<sigma>'" in ballE, erule_tac x="Xa" in allE, auto simp add: case_assms)
          using case_assms2(1) case_assms2(2) case_assms3 s2'''_def apply auto
          using "6" case_assms(1) tocks_mid_refusal_change by fastforce
      next
        assume case_assms3: "s2' = []" "Xa = X"
        then show "\<forall>s\<in>tocks {x. x \<noteq> Tock}.
            \<rho> @ [X \<union> Y]\<^sub>R # \<sigma> \<noteq> s \<and> (\<forall>\<sigma>'\<in>P. \<forall>Xa. Tock \<in> Xa \<or> \<rho> @ [X \<union> Y]\<^sub>R # \<sigma> \<noteq> s @ [Xa]\<^sub>R # [Tock]\<^sub>E # \<sigma>') \<Longrightarrow>
          \<exists>s\<in>tocks {x. x \<noteq> Tock}. \<exists>Xa. Tock \<notin> Xa \<and> \<rho> @ [X \<union> Y]\<^sub>R # \<sigma> = s @ [[Xa]\<^sub>R]"
          using case_assms(4) case_assms2 2 5 apply (erule_tac x="\<rho>" in ballE, auto)
          by (erule_tac x="\<sigma>'" in ballE, auto simp add: case_assms)
      qed
    qed
  qed
qed

lemma CT3_TockPrefix: 
  assumes "CT3 P"
  shows "CT3 (tock \<rightarrow>\<^sub>C P)"
  unfolding TockPrefixCTT_def CT3_def
proof (safe, simp_all)
  show "\<And>s. s \<in> tocks {x. x \<noteq> Tock} \<Longrightarrow> CT3_trace s"
    by (metis (mono_tags, lifting) CT3_def CT3_tocks mem_Collect_eq)
next
  show "\<And>s X. s \<in> tocks {x. x \<noteq> Tock} \<Longrightarrow> Tock \<notin> X \<Longrightarrow> CT3_trace (s @ [[X]\<^sub>R])"
    by (metis (mono_tags, lifting) CT3_append CT3_def CT3_tocks CT3_trace.simps(2) ttWF.simps(2) mem_Collect_eq)
next
  show "\<And>s. s \<in> tocks {x. x \<noteq> Tock} \<Longrightarrow> CT3_trace s"
    by (metis (mono_tags, lifting) CT3_def CT3_tocks mem_Collect_eq)
next
  fix s \<sigma> :: "'a cttobs list"
  fix X :: "'a cttevent set"
  assume case_assms: "s \<in> tocks {x. x \<noteq> Tock}" "\<sigma> \<in> P" "Tock \<notin> X"  
  have "CT3_trace \<sigma>"
    using case_assms assms unfolding CT3_def by blast
  then show "CT3_trace (s @ [X]\<^sub>R # [Tock]\<^sub>E # \<sigma>)"
    using case_assms(1) case_assms(3) apply - apply (induct s rule:CT3_trace.induct, simp_all add: notin_tocks)
    using list.distinct(1) tocks.cases apply blast
    apply (smt CT3_trace.simps(3) append_Cons list.inject list.simps(3) mem_Collect_eq subset_eq tocks.simps)
    apply (metis cttobs.simps(4) list.inject list.simps(3) tocks.simps)
    done
qed

lemma CT4s_TockPrefix:
  assumes "CT4s P"
  shows "CT4s (tock \<rightarrow>\<^sub>C P)"
  unfolding TockPrefixCTT_def CT4s_def
proof auto
  fix s :: "'a cttobs list"
  assume "s \<in> tocks {x. x \<noteq> Tock}"   
  then have "add_Tick_refusal_trace s \<in> tocks {x. x \<noteq> Tock}"
    by (induct s rule:tocks.induct, auto simp add: tocks.intros)
  then show "\<forall>sa\<in>tocks {x. x \<noteq> Tock}.
      add_Tick_refusal_trace s \<noteq> sa \<and> (\<forall>\<sigma>\<in>P. \<forall>X. Tock \<in> X \<or> add_Tick_refusal_trace s \<noteq> sa @ [X]\<^sub>R # [Tock]\<^sub>E # \<sigma>) \<Longrightarrow>
    \<exists>sa\<in>tocks {x. x \<noteq> Tock}. \<exists>X. Tock \<notin> X \<and> add_Tick_refusal_trace s = sa @ [[X]\<^sub>R]"
    by (erule_tac x="add_Tick_refusal_trace s" in ballE, auto)
next
  fix s :: "'a cttobs list"
  fix X :: "'a cttevent set"
  assume case_assms: "s \<in> tocks {x. x \<noteq> Tock}" "Tock \<notin> X"
  then have "add_Tick_refusal_trace s \<in> tocks {x. x \<noteq> Tock}"
    by (induct s rule:tocks.induct, auto simp add: tocks.intros)
  then show "\<exists>sa\<in>tocks {x. x \<noteq> Tock}. \<exists>Xa. Tock \<notin> Xa \<and> add_Tick_refusal_trace (s @ [[X]\<^sub>R]) = sa @ [[Xa]\<^sub>R]"
    using case_assms apply (rule_tac x="add_Tick_refusal_trace s" in bexI, rule_tac x="X \<union> {Tick}" in exI, simp_all)
    using add_Tick_refusal_trace_end_refusal by force
next
  fix s :: "'a cttobs list"
  assume "s \<in> tocks {x. x \<noteq> Tock}"   
  then have "add_Tick_refusal_trace s \<in> tocks {x. x \<noteq> Tock}"
    by (induct s rule:tocks.induct, auto simp add: tocks.intros)
  then show "\<forall>sa\<in>tocks {x. x \<noteq> Tock}.
      add_Tick_refusal_trace s \<noteq> sa \<and> (\<forall>\<sigma>\<in>P. \<forall>X. Tock \<in> X \<or> add_Tick_refusal_trace s \<noteq> sa @ [X]\<^sub>R # [Tock]\<^sub>E # \<sigma>) \<Longrightarrow>
    \<exists>sa\<in>tocks {x. x \<noteq> Tock}. \<exists>X. Tock \<notin> X \<and> add_Tick_refusal_trace s = sa @ [[X]\<^sub>R]"
    by (erule_tac x="add_Tick_refusal_trace s" in ballE, auto)
next
  fix s \<sigma> :: "'a cttobs list"
  fix X  :: "'a cttevent set"
  assume case_assms: "s \<in> tocks {x. x \<noteq> Tock}" "\<sigma> \<in> P" "Tock \<notin> X"
  then have 1: "add_Tick_refusal_trace s \<in> tocks {x. x \<noteq> Tock}"
    by (induct s rule:tocks.induct, auto simp add: tocks.intros)
  have 2: "add_Tick_refusal_trace \<sigma> \<in> P"
    using assms case_assms unfolding CT4s_def by auto
  show "\<forall>sa\<in>tocks {x. x \<noteq> Tock}. add_Tick_refusal_trace (s @ [X]\<^sub>R # [Tock]\<^sub>E # \<sigma>) \<noteq> sa \<and>
      (\<forall>\<sigma>'\<in>P. \<forall>Xa. Tock \<in> Xa \<or> add_Tick_refusal_trace (s @ [X]\<^sub>R # [Tock]\<^sub>E # \<sigma>) \<noteq> sa @ [Xa]\<^sub>R # [Tock]\<^sub>E # \<sigma>') \<Longrightarrow>
    \<exists>sa\<in>tocks {x. x \<noteq> Tock}. \<exists>Xa. Tock \<notin> Xa \<and> add_Tick_refusal_trace (s @ [X]\<^sub>R # [Tock]\<^sub>E # \<sigma>) = sa @ [[Xa]\<^sub>R]"
    using 1 2 case_assms(3) apply (erule_tac x="add_Tick_refusal_trace s" in ballE, auto) 
    apply (erule_tac x="add_Tick_refusal_trace \<sigma>" in ballE, erule_tac x="X \<union> {Tick}" in allE, auto)
    by (metis Un_commute add_Tick_refusal_trace.simps(2) add_Tick_refusal_trace.simps(3) add_Tick_refusal_trace_concat insert_is_Un)
qed

lemma CT_TockPrefix:
  assumes "CT P" "CT2s P" "CT4s P"
  shows "CT (tock \<rightarrow>\<^sub>C P)"
  using assms unfolding CT_def
  using CT0_TockPrefixCTT CT1_TockPrefixCTT CT2s_TockPrefix CT2s_imp_CT2 CT3_TockPrefix TockPrefixCTT_wf by blast

end