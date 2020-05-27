theory IOTickTock_Deadline
  imports IOTickTock_Core "TickTock-FL.TickTock_Pri"
begin

section \<open>Preliminary Lemmas\<close>

lemma filter_tocks_refusal_no_mid_event: "\<And>s. filter_tocks p @ [[Y]\<^sub>R] \<noteq> s @ [Event e]\<^sub>E # \<sigma>"
  by (induct p rule:filter_tocks.induct, auto simp add: notin_tocks Cons_eq_append_conv)

lemma RenamingTT_init_event:
  "inj f \<Longrightarrow> {t. [Event (f e)]\<^sub>E # t \<in> RenamingTT P f} = RenamingTT {t. [Event e]\<^sub>E # t \<in> P} f"
  unfolding RenamingTT_def inj_def by (auto, case_tac xa rule:ttWF.cases, auto, force)

lemma RenamingTT_init_tock: "{\<sigma>. [X]\<^sub>R # [Tock]\<^sub>E # \<sigma> \<in> RenamingTT P f}
          = RenamingTT {\<sigma>. [(lift_renaming_func f) -` X]\<^sub>R # [Tock]\<^sub>E # \<sigma> \<in> P} f"
  unfolding RenamingTT_def by (auto, case_tac xa rule:ttWF.cases, auto, force)

lemma lift_renaming_func_image_inverse:
  "inj f \<Longrightarrow> lift_renaming_func f -` lift_renaming_func f ` X = X"
  unfolding image_def vimage_def inj_def by (auto, case_tac x, auto, (case_tac xa, auto)+)

lemma rename_trace_nonempty: "inj f \<Longrightarrow> \<exists>x. x \<in> rename_trace f t"
  apply (induct f t rule:rename_trace.induct, auto)
  by (rule_tac x="lift_renaming_func f ` X" in exI, auto simp add: lift_renaming_func_image_inverse)

lemma RenamingTT_init_tock2:
  "inj f \<Longrightarrow>
    {\<sigma>. [(lift_renaming_func f) ` X]\<^sub>R # [Tock]\<^sub>E # \<sigma> \<in> RenamingTT P f} = RenamingTT {\<sigma>. [X]\<^sub>R # [Tock]\<^sub>E # \<sigma> \<in> P} f"
  unfolding  RenamingTT_def using lift_renaming_func_image_inverse
  by (auto, case_tac xa rule:ttWF.cases, auto, fastforce, rule_tac x="[X]\<^sub>R # [Tock]\<^sub>E # xa" in bexI, auto)

lemma TimeSyncInterruptTT_PrefixTT_init_event: "e \<noteq> f \<Longrightarrow> {t. [Event e]\<^sub>E # t \<in> P \<triangle>\<^sub>T f \<rightarrow>\<^sub>C Q} = {t. [Event e]\<^sub>E # t \<in> P} \<triangle>\<^sub>T f \<rightarrow>\<^sub>C Q"
  unfolding TimeSyncInterruptTT_def
proof (safe, simp_all)
  fix p x
  show "p @ [[Tick]\<^sub>E] \<in> P \<Longrightarrow> filter_tocks p \<in> f \<rightarrow>\<^sub>C Q \<Longrightarrow> [Event e]\<^sub>E # x = p @ [[Tick]\<^sub>E] \<Longrightarrow>
      \<exists>p. [Event e]\<^sub>E # p @ [[Tick]\<^sub>E] \<in> P \<and> filter_tocks p \<in> f \<rightarrow>\<^sub>C Q \<and> x = p @ [[Tick]\<^sub>E]"
    by (case_tac p rule:ttWF.cases, simp_all)
next
  fix x p X Y Z
  assume "p @ [[X]\<^sub>R] \<in> P" "filter_tocks p @ [[Y]\<^sub>R] \<in> f \<rightarrow>\<^sub>C Q" "Z \<subseteq> X \<union> Y" "{e \<in> X. e \<noteq> Tock} = {e \<in> Y. e \<noteq> Tock}" "[Event e]\<^sub>E # x = p @ [[Z]\<^sub>R]"
  then show "\<forall>p X. [Event e]\<^sub>E # p @ [[X]\<^sub>R] \<in> P \<longrightarrow>
             (\<forall>Y. {e \<in> X. e \<noteq> Tock} = {e \<in> Y. e \<noteq> Tock} \<longrightarrow> filter_tocks p @ [[Y]\<^sub>R] \<in> f \<rightarrow>\<^sub>C Q \<longrightarrow> (\<forall>Z\<subseteq>X \<union> Y. x \<noteq> p @ [[Z]\<^sub>R])) \<Longrightarrow>
       [Event e]\<^sub>E # x = p @ [[Z]\<^sub>R] \<Longrightarrow> \<exists>p. [Event e]\<^sub>E # p @ [[Tick]\<^sub>E] \<in> P \<and> filter_tocks p \<in> f \<rightarrow>\<^sub>C Q \<and> x = p @ [[Tick]\<^sub>E]"
    by (case_tac p rule:ttWF.cases, simp_all, blast)
next
  fix x p q2
  assume p_in_P: "p \<in> P" and filter_tocks_p_q2_in_PrefixTT_Q: "filter_tocks p @ q2 \<in> f \<rightarrow>\<^sub>C Q"
  assume p_no_end_tick: "\<forall>p'. p \<noteq> p' @ [[Tick]\<^sub>E]" and p_no_end_refusal: "\<forall>p' Y. p \<noteq> p' @ [[Y]\<^sub>R]"
  assume q2_no_init_refusal: "\<forall>q' Y. q2 \<noteq> [Y]\<^sub>R # q'"
  assume e_x_eq_p_q2: "[Event e]\<^sub>E # x = p @ q2"
  assume e_neq_f: "e \<noteq> f"

  have "(\<exists>p'. p = [Event e]\<^sub>E # p') \<or> p = []"
    using e_x_eq_p_q2 by (case_tac p rule:ttWF.cases, simp_all)
  then have "\<exists>p'. p = [Event e]\<^sub>E # p'"
    using e_x_eq_p_q2 filter_tocks_p_q2_in_PrefixTT_Q unfolding PrefixTT_def apply (auto simp add: notin_tocks)
    apply (metis (no_types, lifting) Cons_eq_append_conv list.inject start_event_notin_tocks ttobs.distinct(1))
    by (metis (no_types, lifting) Cons_eq_append_conv e_neq_f list.inject start_event_notin_tocks ttevent.inject ttobs.inject(1))
  then show "\<forall>p. [Event e]\<^sub>E # p \<in> P \<longrightarrow>
           (\<exists>p'. p = p' @ [[Tick]\<^sub>E]) \<or>
           (\<exists>p' Y. p = p' @ [[Y]\<^sub>R]) \<or> (\<forall>q2. filter_tocks p @ q2 \<in> f \<rightarrow>\<^sub>C Q \<longrightarrow> (\<exists>q' Y. q2 = [Y]\<^sub>R # q') \<or> x \<noteq> p @ q2) \<Longrightarrow>
      \<exists>p. [Event e]\<^sub>E # p @ [[Tick]\<^sub>E] \<in> P \<and> filter_tocks p \<in> f \<rightarrow>\<^sub>C Q \<and> x = p @ [[Tick]\<^sub>E]"
    by (metis append_Cons e_x_eq_p_q2 filter_tocks.simps(3) filter_tocks_p_q2_in_PrefixTT_Q
        list.inject p_in_P p_no_end_refusal p_no_end_tick q2_no_init_refusal)
next
  fix p X Y Z
  show " \<forall>pa X. pa @ [[X]\<^sub>R] \<in> P \<longrightarrow> (\<forall>Y. {e \<in> X. e \<noteq> Tock} = {e \<in> Y. e \<noteq> Tock} \<longrightarrow> Z \<subseteq> X \<union> Y \<longrightarrow> filter_tocks pa @ [[Y]\<^sub>R] \<in> f \<rightarrow>\<^sub>C Q \<longrightarrow> [Event e]\<^sub>E # p \<noteq> pa) \<Longrightarrow>
       [Event e]\<^sub>E # p @ [[X]\<^sub>R] \<in> P \<Longrightarrow> filter_tocks p @ [[Y]\<^sub>R] \<in> f \<rightarrow>\<^sub>C Q \<Longrightarrow> Z \<subseteq> X \<union> Y \<Longrightarrow> {e \<in> X. e \<noteq> Tock} = {e \<in> Y. e \<noteq> Tock} \<Longrightarrow> False"
    by (metis (no_types, lifting) append_Cons filter_tocks.simps(3))
next
  fix p q2
  assume "[Event e]\<^sub>E # p \<in> P" "\<forall>p'. p \<noteq> p' @ [[Tick]\<^sub>E]" "\<forall>p' Y. p \<noteq> p' @ [[Y]\<^sub>R]" "filter_tocks p @ q2 \<in> f \<rightarrow>\<^sub>C Q" "\<forall>q' Y. q2 \<noteq> [Y]\<^sub>R # q'"
  then show "\<forall>pa. pa \<in> P \<longrightarrow> (\<exists>p'. pa = p' @ [[Tick]\<^sub>E]) \<or> (\<exists>p' Y. pa = p' @ [[Y]\<^sub>R]) \<or>
            (\<forall>q2a. filter_tocks pa @ q2a \<in> f \<rightarrow>\<^sub>C Q \<longrightarrow> (\<exists>q' Y. q2a = [Y]\<^sub>R # q') \<or> [Event e]\<^sub>E # p @ q2 \<noteq> pa @ q2a) \<Longrightarrow>
        \<exists>pa. pa @ [[Tick]\<^sub>E] \<in> P \<and> filter_tocks pa \<in> f \<rightarrow>\<^sub>C Q \<and> [Event e]\<^sub>E # p @ q2 = pa @ [[Tick]\<^sub>E]"
    by (erule_tac x="[Event e]\<^sub>E # p" in allE, auto simp add: Cons_eq_append_conv)
qed

lemma TimeSyncInterruptTT_PrefixTT_init_tock:
  "\<forall>x\<in>P. ttWF x \<Longrightarrow> Event f \<notin> X \<Longrightarrow> {t. [X]\<^sub>R # [Tock]\<^sub>E # t \<in> P \<triangle>\<^sub>T f \<rightarrow>\<^sub>C Q} = {t. [X]\<^sub>R # [Tock]\<^sub>E # t \<in> P} \<triangle>\<^sub>T f \<rightarrow>\<^sub>C Q"
  unfolding TimeSyncInterruptTT_def
proof (safe, simp_all)
  fix x p
  show "p @ [[Tick]\<^sub>E] \<in> P \<Longrightarrow> filter_tocks p \<in> f \<rightarrow>\<^sub>C Q \<Longrightarrow> [X]\<^sub>R # [Tock]\<^sub>E # x = p @ [[Tick]\<^sub>E] \<Longrightarrow>
      \<exists>p. [X]\<^sub>R # [Tock]\<^sub>E # p @ [[Tick]\<^sub>E] \<in> P \<and> filter_tocks p \<in> f \<rightarrow>\<^sub>C Q \<and> x = p @ [[Tick]\<^sub>E]"
    unfolding PrefixTT_def apply (cases p rule:ttWF.cases, auto)
    apply (meson list.inject list.simps(3) tocks.simps)
    apply (metis end_refusal_notin_tocks filter_tocks.simps(1) filter_tocks_in_tocks)
    apply (meson list.inject list.simps(3) tocks.simps)
    by (metis append.left_neutral append_Cons filter_tocks.simps(1) filter_tocks_in_tocks mid_event_notin_tocks)
next
  fix x p Xa Y Z
  assume "p @ [[Xa]\<^sub>R] \<in> P" "filter_tocks p @ [[Y]\<^sub>R] \<in> f \<rightarrow>\<^sub>C Q" "Z \<subseteq> Xa \<union> Y"
    "{e \<in> Xa. e \<noteq> Tock} = {e \<in> Y. e \<noteq> Tock}" "[X]\<^sub>R # [Tock]\<^sub>E # x = p @ [[Z]\<^sub>R]"
  then show "\<forall>p Xa. [X]\<^sub>R # [Tock]\<^sub>E # p @ [[Xa]\<^sub>R] \<in> P \<longrightarrow> (\<forall>Y. {e \<in> Xa. e \<noteq> Tock} = {e \<in> Y. e \<noteq> Tock} \<longrightarrow>
        filter_tocks p @ [[Y]\<^sub>R] \<in> f \<rightarrow>\<^sub>C Q \<longrightarrow> (\<forall>Z\<subseteq>Xa \<union> Y. x \<noteq> p @ [[Z]\<^sub>R])) \<Longrightarrow>
      \<exists>p. [X]\<^sub>R # [Tock]\<^sub>E # p @ [[Tick]\<^sub>E] \<in> P \<and> filter_tocks p \<in> f \<rightarrow>\<^sub>C Q \<and> x = p @ [[Tick]\<^sub>E]"
    apply (cases p rule:ttWF.cases, safe, simp_all)
    apply (erule_tac x=\<sigma> in allE, erule_tac x=Xa in allE, safe, simp_all)
    apply (erule_tac x=Y in allE, safe)
    unfolding PrefixTT_def apply safe apply simp_all
    using in_tocks_last apply fastforce
    using tocks.cases apply force
    using in_tocks_last apply fastforce
    apply (metis (no_types, hide_lams) append.left_neutral append_Cons append_assoc filter_tocks.simps(1)
           filter_tocks_end_ref_tock filter_tocks_in_tocks mid_event_notin_tocks)
    by blast+
next
  fix x p q2
  assume " p \<in> P" "\<forall>p'. p \<noteq> p' @ [[Tick]\<^sub>E]" "\<forall>p' Y. p \<noteq> p' @ [[Y]\<^sub>R]" "filter_tocks p @ q2 \<in> f \<rightarrow>\<^sub>C Q" "\<forall>q' Y. q2 \<noteq> [Y]\<^sub>R # q'" "[X]\<^sub>R # [Tock]\<^sub>E # x = p @ q2"
  then show "\<forall>p. [X]\<^sub>R # [Tock]\<^sub>E # p \<in> P \<longrightarrow>
           (\<exists>p'. p = p' @ [[Tick]\<^sub>E]) \<or>
           (\<exists>p' Y. p = p' @ [[Y]\<^sub>R]) \<or> (\<forall>q2. filter_tocks p @ q2 \<in> f \<rightarrow>\<^sub>C Q \<longrightarrow> (\<exists>q' Y. q2 = [Y]\<^sub>R # q') \<or> x \<noteq> p @ q2) \<Longrightarrow>
       \<exists>p. [X]\<^sub>R # [Tock]\<^sub>E # p @ [[Tick]\<^sub>E] \<in> P \<and> filter_tocks p \<in> f \<rightarrow>\<^sub>C Q \<and> x = p @ [[Tick]\<^sub>E]"
    apply (cases p rule:ttWF.cases, safe, simp_all, blast)
    apply (erule_tac x=\<sigma> in allE, auto, erule_tac x=q2 in allE, auto, erule_tac x=q2 in allE, auto)
    unfolding PrefixTT_def apply safe apply simp_all
    apply (meson list.inject list.simps(3) tocks.simps)
    apply (smt append_butlast_last_id butlast.simps(2) butlast_snoc last.simps last_snoc list.distinct(1) list.inject tocks.cases)
    apply (meson list.inject list.simps(3) tocks.simps)
    apply (smt append_Cons filter_tocks.simps(1) filter_tocks_in_tocks list.inject self_append_conv2 start_event_notin_tocks tocks.cases)
    using \<open>\<forall>q' Y. q2 \<noteq> [Y]\<^sub>R # q'\<close> by blast+
next
  fix p
  assume P_wf: "Ball P ttWF" "[X]\<^sub>R # [Tock]\<^sub>E # p @ [[Tick]\<^sub>E] \<in> P"
  then have "Tock \<notin> X"
    using ttWF.simps(5) by blast
  then show "Event f \<notin> X \<Longrightarrow> filter_tocks p \<in> f \<rightarrow>\<^sub>C Q \<Longrightarrow> [X]\<^sub>R # [Tock]\<^sub>E # filter_tocks p \<in> f \<rightarrow>\<^sub>C Q"
    unfolding PrefixTT_def apply auto
    apply (erule_tac x="[X]\<^sub>R # [Tock]\<^sub>E # filter_tocks p" in ballE, auto)
    apply (smt Ball_Collect tocks.tock_insert_in_tocks)
    apply (metis end_refusal_notin_tocks filter_tocks_in_tocks)
    apply (erule_tac x="[X]\<^sub>R # [Tock]\<^sub>E # filter_tocks p" in ballE, auto)
    apply (smt Ball_Collect tocks.tock_insert_in_tocks)
    by (metis append.left_neutral append_Cons filter_tocks_in_tocks mid_event_notin_tocks)
next
  fix p Xa Y Z
  assume " Ball P ttWF" "Event f \<notin> X" "[X]\<^sub>R # [Tock]\<^sub>E # p @ [[Xa]\<^sub>R] \<in> P" "filter_tocks p @ [[Y]\<^sub>R] \<in> f \<rightarrow>\<^sub>C Q"
    "Z \<subseteq> Xa \<union> Y" "{e \<in> Xa. e \<noteq> Tock} = {e \<in> Y. e \<noteq> Tock}"
  then show "\<forall>pa Xa. pa @ [[Xa]\<^sub>R] \<in> P \<longrightarrow> (\<forall>Y. {e \<in> Xa. e \<noteq> Tock} = {e \<in> Y. e \<noteq> Tock} \<longrightarrow> Z \<subseteq> Xa \<union> Y \<longrightarrow>
      filter_tocks pa @ [[Y]\<^sub>R] \<in> f \<rightarrow>\<^sub>C Q \<longrightarrow> [X]\<^sub>R # [Tock]\<^sub>E # p \<noteq> pa) \<Longrightarrow> False"
    apply (erule_tac x="[X]\<^sub>R # [Tock]\<^sub>E # p" in allE)
    apply (erule_tac x="Xa" in allE, safe, simp_all)
    apply (erule_tac x="Y" in allE, simp)
    unfolding PrefixTT_def apply (safe, simp_all add: notin_tocks)
    apply (erule_tac x="[X]\<^sub>R # [Tock]\<^sub>E # filter_tocks p" in ballE, safe, simp_all)
    apply (smt Ball_Collect tocks.tock_insert_in_tocks ttWF.simps(5))
    apply (smt Ball_Collect tocks.tock_insert_in_tocks ttWF.simps(5))
    by (metis append.left_neutral append_Cons append_assoc filter_tocks_end_ref_tock filter_tocks_in_tocks mid_event_notin_tocks)
next
  fix p q2
  assume "Ball P ttWF" "Event f \<notin> X" "[X]\<^sub>R # [Tock]\<^sub>E # p \<in> P" "\<forall>p'. p \<noteq> p' @ [[Tick]\<^sub>E]"
    "\<forall>p' Y. p \<noteq> p' @ [[Y]\<^sub>R]" "filter_tocks p @ q2 \<in> f \<rightarrow>\<^sub>C Q" "\<forall>q' Y. q2 \<noteq> [Y]\<^sub>R # q'"
  then show "\<forall>pa. pa \<in> P \<longrightarrow>
            (\<exists>p'. pa = p' @ [[Tick]\<^sub>E]) \<or>
            (\<exists>p' Y. pa = p' @ [[Y]\<^sub>R]) \<or>
            (\<forall>q2a. filter_tocks pa @ q2a \<in> f \<rightarrow>\<^sub>C Q \<longrightarrow> (\<exists>q' Y. q2a = [Y]\<^sub>R # q') \<or> [X]\<^sub>R # [Tock]\<^sub>E # p @ q2 \<noteq> pa @ q2a) \<Longrightarrow>
       \<exists>pa. pa @ [[Tick]\<^sub>E] \<in> P \<and> filter_tocks pa \<in> f \<rightarrow>\<^sub>C Q \<and> [X]\<^sub>R # [Tock]\<^sub>E # p @ q2 = pa @ [[Tick]\<^sub>E]"
    apply (erule_tac x="[X]\<^sub>R # [Tock]\<^sub>E # p" in allE, auto simp add: Cons_eq_append_conv)
    apply (erule_tac x="q2" in allE, auto)
    unfolding PrefixTT_def
  proof (safe, simp_all)
    assume "Ball P ttWF" "[X]\<^sub>R # [Tock]\<^sub>E # p \<in> P"
    then have "Tock \<notin> X"
      by auto
    then show "Event f \<notin> X \<Longrightarrow> filter_tocks p @ q2 \<in> tocks {x. x \<noteq> Tock \<and> x \<noteq> Event f} \<Longrightarrow>
    \<forall>s\<in>tocks {x. x \<noteq> Tock \<and> x \<noteq> Event f}.
       [X]\<^sub>R # [Tock]\<^sub>E # filter_tocks p @ q2 \<noteq> s \<and> (\<forall>\<sigma>\<in>Q. [X]\<^sub>R # [Tock]\<^sub>E # filter_tocks p @ q2 \<noteq> s @ [Event f]\<^sub>E # \<sigma>) \<Longrightarrow>
    \<exists>s\<in>tocks {x. x \<noteq> Tock \<and> x \<noteq> Event f}. \<exists>Xa. Tock \<notin> Xa \<and> Event f \<notin> Xa \<and> [X]\<^sub>R # [Tock]\<^sub>E # filter_tocks p @ q2 = s @ [[Xa]\<^sub>R]"
      apply (erule_tac x="[X]\<^sub>R # [Tock]\<^sub>E # filter_tocks p @ q2" in ballE, auto)
      by (smt Ball_Collect tocks.tock_insert_in_tocks)
  next
    assume "Ball P ttWF" "[X]\<^sub>R # [Tock]\<^sub>E # p \<in> P"
    then have "Tock \<notin> X"
      by auto
    then show "Event f \<notin> X \<Longrightarrow> filter_tocks p @ q2 \<in> tocks {x. x \<noteq> Tock \<and> x \<noteq> Event f} \<Longrightarrow>
    \<forall>s\<in>tocks {x. x \<noteq> Tock \<and> x \<noteq> Event f}.
       [X]\<^sub>R # [Tock]\<^sub>E # filter_tocks p @ q2 \<noteq> s \<and> (\<forall>\<sigma>\<in>Q. [X]\<^sub>R # [Tock]\<^sub>E # filter_tocks p @ q2 \<noteq> s @ [Event f]\<^sub>E # \<sigma>) \<Longrightarrow>
    \<exists>s\<in>tocks {x. x \<noteq> Tock \<and> x \<noteq> Event f}. \<exists>Xa. Tock \<notin> Xa \<and> Event f \<notin> Xa \<and> [X]\<^sub>R # [Tock]\<^sub>E # filter_tocks p @ q2 = s @ [[Xa]\<^sub>R]"
      apply (erule_tac x="[X]\<^sub>R # [Tock]\<^sub>E # filter_tocks p @ q2" in ballE, auto)
      by (smt Ball_Collect tocks.tock_insert_in_tocks)
  next
    fix s
    assume "Ball P ttWF" "[X]\<^sub>R # [Tock]\<^sub>E # p \<in> P"
    then have "Tock \<notin> X"
      by auto
    then show "Event f \<notin> X \<Longrightarrow> s \<in> tocks {x. x \<noteq> Tock \<and> x \<noteq> Event f} \<Longrightarrow> [X]\<^sub>R # [Tock]\<^sub>E # s \<in> tocks {x. x \<noteq> Tock \<and> x \<noteq> Event f}"
      by (smt Ball_Collect tocks.tock_insert_in_tocks)
  next
    fix s \<sigma>
    assume "\<forall>x\<in>P. ttWF x" "[X]\<^sub>R # [Tock]\<^sub>E # p \<in> P"
    then have "Tock \<notin> X"
      by auto
    then show "Event f \<notin> X \<Longrightarrow>  s \<in> tocks {x. x \<noteq> Tock \<and> x \<noteq> Event f} \<Longrightarrow> \<sigma> \<in> Q \<Longrightarrow> filter_tocks p @ q2 = s @ [Event f]\<^sub>E # \<sigma> \<Longrightarrow>
          \<forall>sa\<in>tocks {x. x \<noteq> Tock \<and> x \<noteq> Event f}.
              [X]\<^sub>R # [Tock]\<^sub>E # s @ [Event f]\<^sub>E # \<sigma> \<noteq> sa \<and> (\<forall>\<sigma>'\<in>Q. [X]\<^sub>R # [Tock]\<^sub>E # s @ [Event f]\<^sub>E # \<sigma> \<noteq> sa @ [Event f]\<^sub>E # \<sigma>') \<Longrightarrow>
          \<exists>sa\<in>tocks {x. x \<noteq> Tock \<and> x \<noteq> Event f}. \<exists>Xa. Tock \<notin> Xa \<and> Event f \<notin> Xa \<and> [X]\<^sub>R # [Tock]\<^sub>E # s @ [Event f]\<^sub>E # \<sigma> = sa @ [[Xa]\<^sub>R]"
      by (erule_tac x="[X]\<^sub>R # [Tock]\<^sub>E # s" in ballE, auto, smt Ball_Collect tocks.tock_insert_in_tocks)
  qed
qed

lemma TimeSyncInterruptTT_PrefixTT_init_tock_any_refusal_subset:
  "\<forall>x\<in>P. ttWF x \<Longrightarrow> Event f \<notin> X \<Longrightarrow> {t. \<exists>X. [X]\<^sub>R # [Tock]\<^sub>E # t \<in> P \<triangle>\<^sub>T f \<rightarrow>\<^sub>C Q} \<subseteq> {t. \<exists>X. [X]\<^sub>R # [Tock]\<^sub>E # t \<in> P} \<triangle>\<^sub>T f \<rightarrow>\<^sub>C Q"
proof auto
  fix x Xa
  show "\<forall>x\<in>P. ttWF x \<Longrightarrow> Event f \<notin> X \<Longrightarrow> [Xa]\<^sub>R # [Tock]\<^sub>E # x \<in> P \<triangle>\<^sub>T f \<rightarrow>\<^sub>C Q \<Longrightarrow> x \<in> {t. \<exists>X. [X]\<^sub>R # [Tock]\<^sub>E # t \<in> P} \<triangle>\<^sub>T f \<rightarrow>\<^sub>C Q"
    unfolding TimeSyncInterruptTT_def apply safe
  proof simp_all
    fix p
    assume "[Xa]\<^sub>R # [Tock]\<^sub>E # x = p @ [[Tick]\<^sub>E]"
    then obtain p' where "p = [Xa]\<^sub>R # [Tock]\<^sub>E # p' \<and> x = p' @ [[Tick]\<^sub>E]"
      by (case_tac p rule:ttWF.cases, simp_all)
    then show "p @ [[Tick]\<^sub>E] \<in> P \<Longrightarrow> filter_tocks p \<in> f \<rightarrow>\<^sub>C Q \<Longrightarrow>
        \<exists>p. (\<exists>X. [X]\<^sub>R # [Tock]\<^sub>E # p @ [[Tick]\<^sub>E] \<in> P) \<and> filter_tocks p \<in> f \<rightarrow>\<^sub>C Q \<and> x = p @ [[Tick]\<^sub>E]"
      unfolding PrefixTT_def apply auto
      apply (meson list.inject list.simps(3) tocks.simps)
      apply (metis end_refusal_notin_tocks filter_tocks.simps(1) filter_tocks_in_tocks)
      apply (meson list.inject list.simps(3) tocks.simps)
      by (metis append.left_neutral append_Cons filter_tocks.simps(1) filter_tocks_in_tocks mid_event_notin_tocks)
  next
    fix p Xb Y Z
    assume case_assms: "Event f \<notin> X" "p @ [[Xb]\<^sub>R] \<in> P" "filter_tocks p @ [[Y]\<^sub>R] \<in> f \<rightarrow>\<^sub>C Q" "Z \<subseteq> Xb \<union> Y"
      "{e \<in> Xb. e \<noteq> Tock} = {e \<in> Y. e \<noteq> Tock}"
    assume "[Xa]\<^sub>R # [Tock]\<^sub>E # x = p @ [[Z]\<^sub>R]"
    then obtain p' where p_def: "p = [Xa]\<^sub>R # [Tock]\<^sub>E # p' \<and> x = p' @ [[Z]\<^sub>R]"
      by (case_tac p rule:ttWF.cases, simp_all)
    have 1: "[Xa]\<^sub>R # [Tock]\<^sub>E # p' @ [[Xb]\<^sub>R] \<in> P"
      using case_assms(2) p_def by auto
    have 2: "filter_tocks p' @ [[Y]\<^sub>R] \<in> f \<rightarrow>\<^sub>C Q"
      using case_assms(3) p_def unfolding PrefixTT_def using tocks.cases apply auto
      apply (simp add: Cons_eq_append_conv filter_tocks_refusal_no_mid_event)
      apply (metis append_Cons filter_tocks.simps(1) filter_tocks_refusal_no_mid_event)
      by (metis append_Cons filter_tocks.simps(1) filter_tocks_refusal_no_mid_event)
    show "\<forall>p X. (\<forall>Xa. [Xa]\<^sub>R # [Tock]\<^sub>E # p @ [[X]\<^sub>R] \<notin> P) \<or>
             (\<forall>Y. {e \<in> X. e \<noteq> Tock} = {e \<in> Y. e \<noteq> Tock} \<longrightarrow> filter_tocks p @ [[Y]\<^sub>R] \<in> f \<rightarrow>\<^sub>C Q \<longrightarrow> (\<forall>Z\<subseteq>X \<union> Y. x \<noteq> p @ [[Z]\<^sub>R])) \<Longrightarrow>
      \<exists>p. (\<exists>X. [X]\<^sub>R # [Tock]\<^sub>E # p @ [[Tick]\<^sub>E] \<in> P) \<and> filter_tocks p \<in> f \<rightarrow>\<^sub>C Q \<and> x = p @ [[Tick]\<^sub>E]"
      using 1 2 case_assms(4) case_assms(5) p_def apply (erule_tac x=p' in allE, erule_tac x=Xb in allE, safe, simp_all)
      by (erule_tac x=Y in allE, safe, blast)
  next
    fix p q2
    assume case_assms: "Event f \<notin> X" "p \<in> P" "\<forall>p'. p \<noteq> p' @ [[Tick]\<^sub>E]" "\<forall>p' Y. p \<noteq> p' @ [[Y]\<^sub>R]"
      "filter_tocks p @ q2 \<in> f \<rightarrow>\<^sub>C Q" "\<forall>q' Y. q2 \<noteq> [Y]\<^sub>R # q'"
    assume "[Xa]\<^sub>R # [Tock]\<^sub>E # x = p @ q2"
    then obtain p' where p_def: "p = [Xa]\<^sub>R # [Tock]\<^sub>E # p' \<and> x = p' @ q2"
      using case_assms(4) case_assms(6) by (cases p rule:ttWF.cases, auto)
    have 1: "[Xa]\<^sub>R # [Tock]\<^sub>E # p' \<in> P"
      using p_def case_assms(2) by auto
    have 2: "\<forall>p'. p \<noteq> p' @ [[Tick]\<^sub>E]"
      using case_assms(3) by blast
    have 3: "\<forall>p' Y. p \<noteq> p' @ [[Y]\<^sub>R]"
      using case_assms(4) by blast
    have 4: "filter_tocks p' @ q2 \<in> f \<rightarrow>\<^sub>C Q"
      using p_def case_assms(5) unfolding PrefixTT_def apply auto
         apply (meson list.inject neq_Nil_conv tocks.simps)
      apply (case_tac s rule:ttWF.cases, auto)
      apply (metis (no_types, lifting) list.inject list.simps(3) tocks.simps)
      apply (meson list.inject list.simps(3) tocks.simps)
      apply (case_tac s rule:ttWF.cases, auto)
      by (metis (no_types, lifting) list.distinct(1) list.inject tocks.simps)
    have 5: "\<forall>q' Y. q2 \<noteq> [Y]\<^sub>R # q'"
      using case_assms(6) by blast

    show "\<forall>p. (\<forall>X. [X]\<^sub>R # [Tock]\<^sub>E # p \<notin> P) \<or> (\<exists>p'. p = p' @ [[Tick]\<^sub>E]) \<or> (\<exists>p' Y. p = p' @ [[Y]\<^sub>R]) \<or>
        (\<forall>q2. filter_tocks p @ q2 \<in> f \<rightarrow>\<^sub>C Q \<longrightarrow> (\<exists>q' Y. q2 = [Y]\<^sub>R # q') \<or> x \<noteq> p @ q2) \<Longrightarrow>
      \<exists>p. (\<exists>X. [X]\<^sub>R # [Tock]\<^sub>E # p @ [[Tick]\<^sub>E] \<in> P) \<and> filter_tocks p \<in> f \<rightarrow>\<^sub>C Q \<and> x = p @ [[Tick]\<^sub>E]"
      using 1 2 3 4 5 p_def by (erule_tac x=p' in allE, auto)
  qed
qed

lemma ttWF_priTT_imp_ttWF1: "\<And>\<sigma> Q. ttWF x \<Longrightarrow> priTT p x y \<sigma> Q \<Longrightarrow> ttWF y"
  by (induct x y rule:ttWF2.induct, auto, unfold prirefTT_def, auto, (case_tac \<rho> rule:ttWF.cases, auto)+)

lemma ttWF_priTT_imp_ttWF2: "\<And>\<sigma> Q. ttWF y \<Longrightarrow> priTT p x y \<sigma> Q \<Longrightarrow> ttWF x"
  by (induct x y rule:ttWF2.induct, auto, (case_tac \<sigma> rule:ttWF.cases, auto)+)

lemma PriTT_wf: 
  "\<forall>x\<in>P. ttWF x \<Longrightarrow> \<forall>x\<in>PriTT p P. ttWF x"
  unfolding PriTT_def using ttWF_priTT_imp_ttWF2 by blast

lemma priTT_init_event_eq:
  "\<And>\<sigma>. ttWF x \<Longrightarrow> ttWF y \<Longrightarrow> x priTT\<^sub>[\<^sub>p\<^sub>,\<^sub>[Event e]\<^sub>E # \<sigma>\<^sub>,\<^sub>P\<^sub>] y = x priTT\<^sub>[\<^sub>p\<^sub>,\<^sub>\<sigma>\<^sub>,\<^sub>{\<sigma>. [Event e]\<^sub>E # \<sigma> \<in> P}\<^sub>] y"
  by (induct x y rule:ttWF2.induct, auto, unfold prirefTT_def, auto)

lemma priTT_prefix_eq: 
  "\<And>\<rho> \<sigma> P. ttWF y \<Longrightarrow> x priTT\<^sub>[\<^sub>p\<^sub>,\<^sub>\<sigma> @ \<rho>\<^sub>,\<^sub>P\<^sub>] y = x priTT\<^sub>[\<^sub>p\<^sub>,\<^sub>\<rho>\<^sub>,\<^sub>{t. \<sigma> @ t \<in> P}\<^sub>] y"
  apply (induct x y rule:ttWF2.induct, auto simp add: prirefTT_def)
  apply (case_tac \<sigma> rule:ttWF.cases, auto)
  using ttWF.simps(10) ttWF_priTT_imp_ttWF2 apply blast
  using ttWF.simps(6) ttWF_priTT_imp_ttWF2 by blast+

lemma PriTT_init_event:
  "\<forall>x\<in>P. ttWF x \<Longrightarrow> maximal(p,Event e) \<Longrightarrow> {t. [Event e]\<^sub>E # t \<in> PriTT p P} = PriTT p {t. [Event e]\<^sub>E # t \<in> P}"
  unfolding PriTT_def apply auto
  apply (case_tac s rule:ttWF.cases, auto, metis priTT_init_event_eq ttWF.simps(4) ttWF_priTT_imp_ttWF2)
  by (rule_tac x="[Event e]\<^sub>E # s" in exI, auto, metis priTT_init_event_eq ttWF.simps(4) ttWF_priTT_imp_ttWF2)

lemma prirefTT_subset: "P \<subseteq> Q \<Longrightarrow> prirefTT p \<sigma> P X \<subseteq> prirefTT p \<sigma> Q X"
  unfolding prirefTT_def by auto

lemma maximal_notin_prirefTT: "maximal(p, e) \<Longrightarrow> e \<notin> X \<Longrightarrow> e \<notin> prirefTT p \<sigma> P X"
  unfolding prirefTT_def by (auto simp add: some_higher_not_maximal)

lemma tt_prefix_subset_priTT: "\<And>P  \<rho>' t. ttWF \<rho> \<Longrightarrow> ttWF \<sigma> \<Longrightarrow> \<rho>' \<lesssim>\<^sub>C \<rho> \<Longrightarrow> \<rho> priTT\<^sub>[\<^sub>p\<^sub>,\<^sub>t\<^sub>,\<^sub>P\<^sub>] \<sigma> \<Longrightarrow> \<exists>\<sigma>'. \<rho>' priTT\<^sub>[\<^sub>p\<^sub>,\<^sub>t\<^sub>,\<^sub>P\<^sub>] \<sigma>' \<and> \<sigma>' \<lesssim>\<^sub>C \<sigma>"
  apply (induct \<rho> \<sigma> rule:ttWF2.induct, auto)
  using priTT.simps(1) tt_prefix_subset.simps(1) tt_prefix_subset_antisym apply blast
  apply (case_tac \<rho>' rule:ttWF.cases, auto)
  using priTT.simps(1) tt_prefix_subset.simps(1) apply blast
  apply (meson dual_order.trans priTT.simps(2) tt_prefix_subset_refl)
  apply (case_tac \<rho>' rule:ttWF.cases, auto)
  using priTT.simps(1) tt_prefix_subset.simps(1) apply blast
  using priTT.simps(1) priTT.simps(4) tt_prefix_subset_refl apply blast
  apply (case_tac \<rho>' rule:ttWF.cases, auto)
  using priTT.simps(1) tt_prefix_subset.simps(1) apply blast
  apply (meson priTT.simps(4) tt_prefix_subset.simps(3))
  apply (case_tac \<rho>' rule:ttWF.cases, auto)
  using priTT.simps(1) tt_prefix_subset.simps(1) apply blast
  apply (meson priTT.simps(4) tt_prefix_subset.simps(3) ttevent.distinct(3))
  apply (case_tac \<rho>' rule:ttWF.cases, auto)
  using priTT.simps(1) tt_prefix_subset.simps(1) apply blast
  apply (meson equalityD1 order_trans priTT.simps(2) tt_prefix_subset.simps(1) tt_prefix_subset.simps(2))
  by (meson dual_order.trans equalityE priTT.simps(3) tt_prefix_subset.simps(2) tt_prefix_subset.simps(3))

lemma TT1_PriTT: "\<forall>x\<in>P. ttWF x \<Longrightarrow> TT1 P \<Longrightarrow> TT1 (PriTT p P)"
  unfolding PriTT_def TT1_def
proof auto
  fix \<rho> \<sigma> s
  assume P_wf: "\<forall>x\<in>P. ttWF x"
  assume TT1_P: "\<forall>\<rho>. (\<exists>\<sigma>. \<rho> \<lesssim>\<^sub>C \<sigma> \<and> \<sigma> \<in> P) \<longrightarrow> \<rho> \<in> P"
  assume s_in_P: "s \<in> P"
  assume \<sigma>_priTT_s: "\<sigma> priTT\<^sub>[\<^sub>p\<^sub>,\<^sub>[]\<^sub>,\<^sub>P\<^sub>] s"
  assume \<rho>_tt_prefix_subset_\<sigma>: "\<rho> \<lesssim>\<^sub>C \<sigma>"

  have s_wf: "ttWF s"
    using P_wf s_in_P by blast
  have \<sigma>_wf: "ttWF \<sigma>"
    using P_wf \<sigma>_priTT_s s_in_P ttWF_priTT_imp_ttWF2 by blast
  obtain s' where "\<rho> priTT\<^sub>[\<^sub>p\<^sub>,\<^sub>[]\<^sub>,\<^sub>P\<^sub>] s' \<and> s' \<lesssim>\<^sub>C s"
    using \<rho>_tt_prefix_subset_\<sigma> \<sigma>_priTT_s \<sigma>_wf s_wf tt_prefix_subset_priTT by blast
  then show "\<exists>s. \<rho> priTT\<^sub>[\<^sub>p\<^sub>,\<^sub>[]\<^sub>,\<^sub>P\<^sub>] s \<and> s \<in> P"
    using TT1_P s_in_P by blast
qed

lemma hide_trace_end_refusal:
  "\<And>x. x @ [[X]\<^sub>R] \<in> hide_trace H y \<Longrightarrow> \<exists>y' Y. y = y' @ [[Y]\<^sub>R] \<and> X \<subseteq> Y \<and> H \<subseteq> Y"
proof (induct H y rule:hide_trace.induct, auto)
  fix e \<sigma> x Xa
  assume ind_hyp: "\<And>x. x @ [[X]\<^sub>R] \<in> hide_trace Xa \<sigma> \<Longrightarrow> \<exists>y' Y. \<sigma> = y' @ [[Y]\<^sub>R] \<and> X \<subseteq> Y \<and> Xa \<subseteq> Y"
  assume "x @ [[X]\<^sub>R] \<in> hide_trace Xa \<sigma>"
  then have "\<exists>y' Y. \<sigma> = y' @ [[Y]\<^sub>R] \<and> X \<subseteq> Y \<and> Xa \<subseteq> Y"
    using ind_hyp by auto
  then show "\<exists>y' Y. [Event e]\<^sub>E # \<sigma> = y' @ [[Y]\<^sub>R] \<and> X \<subseteq> Y \<and> Xa \<subseteq> Y"
    by auto
next
  fix e \<sigma> x s' Xa
  assume ind_hyp: "\<And>x. x @ [[X]\<^sub>R] \<in> hide_trace Xa \<sigma> \<Longrightarrow> \<exists>y' Y. \<sigma> = y' @ [[Y]\<^sub>R] \<and> X \<subseteq> Y \<and> Xa \<subseteq> Y"
  assume s'_in_hide_trace_\<sigma>: "s' \<in> hide_trace Xa \<sigma>" and x_X_eq_e_s': "x @ [[X]\<^sub>R] = [Event e]\<^sub>E # s'"
  obtain x' where x'_def: "s' = x' @ [[X]\<^sub>R] \<and> x = [Event e]\<^sub>E # x'"
    using x_X_eq_e_s' by (induct x rule:ttWF.induct, auto)
  then have "\<exists>y' Y. \<sigma> = y' @ [[Y]\<^sub>R] \<and> X \<subseteq> Y \<and> Xa \<subseteq> Y"
    using ind_hyp s'_in_hide_trace_\<sigma> by blast
  then show "\<exists>y' Y. [Event e]\<^sub>E # \<sigma> = y' @ [[Y]\<^sub>R] \<and> X \<subseteq> Y \<and> Xa \<subseteq> Y"
    by auto
next
  fix Xa Y s x
  assume ind_hyp: "\<And>x. x @ [[X]\<^sub>R] \<in> hide_trace Xa s \<Longrightarrow> \<exists>y' Y. s = y' @ [[Y]\<^sub>R] \<and> X \<subseteq> Y \<and> Xa \<subseteq> Y"
  assume "x @ [[X]\<^sub>R] \<in> hide_trace Xa s"
  then have "\<exists>y' Y. s = y' @ [[Y]\<^sub>R] \<and> X \<subseteq> Y \<and> Xa \<subseteq> Y"
    using ind_hyp by blast
  then show "\<exists>y' Ya. [Y]\<^sub>R # [Tock]\<^sub>E # s = y' @ [[Ya]\<^sub>R] \<and> X \<subseteq> Ya \<and> Xa \<subseteq> Ya"
    by auto
next
  fix Xa Y s x s' Z
  assume ind_hyp: "\<And>x. x @ [[X]\<^sub>R] \<in> hide_trace Xa s \<Longrightarrow> \<exists>y' Y. s = y' @ [[Y]\<^sub>R] \<and> X \<subseteq> Y \<and> Xa \<subseteq> Y"
  assume x_X_eq_Z_Tock_s': "x @ [[X]\<^sub>R] = [Z]\<^sub>R # [Tock]\<^sub>E # s'" and s'_in_hide_trace_\<sigma>': "s' \<in> hide_trace Xa s"
  obtain x' where x'_def: "s' = x' @ [[X]\<^sub>R] \<and> x = [Z]\<^sub>R # [Tock]\<^sub>E # x'"
    using x_X_eq_Z_Tock_s' by (induct x rule:ttWF.induct, auto)
  then have "\<exists>y' Y. s = y' @ [[Y]\<^sub>R] \<and> X \<subseteq> Y \<and> Xa \<subseteq> Y"
    using ind_hyp s'_in_hide_trace_\<sigma>' by auto
  then show "\<exists>y' Ya. [Y]\<^sub>R # [Tock]\<^sub>E # s = y' @ [[Ya]\<^sub>R] \<and> X \<subseteq> Ya \<and> Xa \<subseteq> Ya"
    by auto
qed

lemma priTT_end_refusal:
  "(x @ [[X]\<^sub>R]) priTT\<^sub>[\<^sub>p\<^sub>,\<^sub>\<sigma>\<^sub>,\<^sub>Q\<^sub>] y \<Longrightarrow> \<exists>y' Y. y = y' @ [[Y]\<^sub>R] \<and> X \<subseteq> prirefTT p (\<sigma> @ y') Q Y"
proof (induct p x y \<sigma> Q rule:priTT.induct, auto)
  fix p v va \<sigma> Q
  assume "[[X]\<^sub>R] priTT\<^sub>[\<^sub>p\<^sub>,\<^sub>\<sigma>\<^sub>,\<^sub>Q\<^sub>] (v # va)"
  then have "\<exists>Y. [[X]\<^sub>R] priTT\<^sub>[\<^sub>p\<^sub>,\<^sub>\<sigma>\<^sub>,\<^sub>Q\<^sub>] [[Y]\<^sub>R] \<and> v = [Y]\<^sub>R \<and> va = []"
    by (cases v, auto, (cases va, auto)+)
  then show "\<exists>y' Y. v # va = y' @ [[Y]\<^sub>R] \<and> X \<subseteq> prirefTT p (\<sigma> @ y') Q Y"
    by auto
qed

thm TimeSyncInterruptTT_def

lemma TimeSyncInterruptTT_PrefixTT_end_refusal:
  assumes Q_wf: "\<forall>x\<in>Q. ttWF x"
  shows "x @ [[X]\<^sub>R] \<in> P \<triangle>\<^sub>T (e \<rightarrow>\<^sub>C Q) \<Longrightarrow>
    (\<exists> x'. x' @ [[X]\<^sub>R] \<in> Q) 
    \<or> (\<exists>Xa. x @ [[Xa]\<^sub>R] \<in> P \<and> Event e \<notin> Xa \<and> X \<subseteq> Xa)"
  unfolding TimeSyncInterruptTT_def
proof (safe, simp_all)
  fix Xa Y
  assume case_assms: "x @ [[Xa]\<^sub>R] \<in> P" "filter_tocks x @ [[Y]\<^sub>R] \<in> e \<rightarrow>\<^sub>C Q" "X \<subseteq> Xa \<union> Y" "{e \<in> Xa. e \<noteq> Tock} = {e \<in> Y. e \<noteq> Tock}"
  have "Tock \<notin> Y \<and> Event e \<notin> Y"
    using case_assms(2) unfolding PrefixTT_def by (auto simp add: notin_tocks filter_tocks_refusal_no_mid_event)
  then have "X \<subseteq> Xa \<and> Event e \<notin> Xa"
    using case_assms(3) case_assms(4) by blast
  then show "\<forall>Xa. x @ [[Xa]\<^sub>R] \<in> P \<longrightarrow> Event e \<in> Xa \<or> \<not> X \<subseteq> Xa \<Longrightarrow> \<exists>x'. x' @ [[X]\<^sub>R] \<in> Q"
    using case_assms(1) by blast
next
  fix p q2
  assume case_assms: "\<forall>p' Y. p \<noteq> p' @ [[Y]\<^sub>R]" "filter_tocks p @ q2 \<in> e \<rightarrow>\<^sub>C Q" "\<forall>q' Y. q2 \<noteq> [Y]\<^sub>R # q'" "x @ [[X]\<^sub>R] = p @ q2"
  have q2_wf: "ttWF q2"
    using PrefixTT_wf assms case_assms(2) filter_tocks_in_tocks tocks_append_wf2 by fastforce
  have "\<exists>q'. q2 = q' @ [[X]\<^sub>R]"
    using case_assms apply - apply (induct x p rule:ttWF2.induct, auto,  fastforce)
    by (metis append_Nil2 append_butlast_last_id case_assms(1) case_assms(4) last_appendR last_snoc)+
  then have "\<exists>q''. q2 = [Event e]\<^sub>E # q'' @ [[X]\<^sub>R]"
    using case_assms(2) case_assms(3) q2_wf apply auto
    apply (case_tac q' rule:ttWF.cases, auto)
    unfolding PrefixTT_def apply auto
    using mid_event_notin_tocks apply force+
  proof -
    fix ea \<sigma> s \<sigma>'
    show "\<And>p. filter_tocks p @ [Event ea]\<^sub>E # \<sigma> @ [[X]\<^sub>R] = s @ [Event e]\<^sub>E # \<sigma>' \<Longrightarrow> s \<in> tocks {x. x \<noteq> Tock \<and> x \<noteq> Event e}
      \<Longrightarrow> ea = e"
      apply (induct s rule:ttWF.induct, auto simp add: notin_tocks)
      apply (case_tac p rule:ttWF.cases, auto)
      apply (metis (no_types, lifting) append_eq_Cons_conv filter_tocks_in_tocks list.inject start_event_notin_tocks ttevent.inject ttobs.inject(1))
      apply (metis (no_types, lifting) append_eq_Cons_conv filter_tocks_in_tocks list.inject start_event_notin_tocks ttevent.inject ttobs.inject(1))
      apply (metis (no_types, lifting) append_eq_Cons_conv filter_tocks_in_tocks list.inject start_event_notin_tocks ttevent.inject ttobs.inject(1))
      apply (metis (no_types, lifting) append_eq_Cons_conv filter_tocks_in_tocks list.inject start_event_notin_tocks ttevent.inject ttobs.inject(1))
      apply (metis (no_types, lifting) append_eq_Cons_conv filter_tocks_in_tocks list.inject start_event_notin_tocks ttevent.inject ttobs.inject(1))
      apply (metis (no_types, lifting) append_eq_Cons_conv filter_tocks_in_tocks list.inject start_event_notin_tocks ttevent.inject ttobs.inject(1))
      apply (metis (no_types, lifting) append_eq_Cons_conv filter_tocks_in_tocks list.inject start_event_notin_tocks ttevent.inject ttobs.inject(1))
      apply (metis (no_types, lifting) append_eq_Cons_conv filter_tocks_in_tocks list.inject start_event_notin_tocks ttevent.inject ttobs.inject(1))
    proof (metis (no_types, lifting) append_eq_Cons_conv filter_tocks_in_tocks list.inject start_event_notin_tocks ttevent.inject ttobs.inject(1))
      fix Xa \<sigma>'' p
      show "(\<And>p. filter_tocks p @ [Event ea]\<^sub>E # \<sigma> @ [[X]\<^sub>R] = \<sigma>'' @ [Event e]\<^sub>E # \<sigma>' \<Longrightarrow> \<sigma>'' \<in> tocks {x. x \<noteq> Tock \<and> x \<noteq> Event e} \<Longrightarrow> ea = e) \<Longrightarrow>
       filter_tocks p @ [Event ea]\<^sub>E # \<sigma> @ [[X]\<^sub>R] = [Xa]\<^sub>R # [Tock]\<^sub>E # \<sigma>'' @ [Event e]\<^sub>E # \<sigma>' \<Longrightarrow>
       [Xa]\<^sub>R # [Tock]\<^sub>E # \<sigma>'' \<in> tocks {x. x \<noteq> Tock \<and> x \<noteq> Event e} \<Longrightarrow> ea = e"
        apply (induct p rule:filter_tocks.induct, auto)
        by (metis (no_types, lifting) list.distinct(1) list.inject tocks.simps)
    qed
  qed
  then show "\<exists>x'. x' @ [[X]\<^sub>R] \<in> Q"
    using case_assms(2) unfolding PrefixTT_def apply auto
    using mid_event_notin_tocks apply force+
    by (metis (no_types, lifting) append_butlast_last_id append_is_Nil_conv last.simps last_appendR list.distinct(1) ttobs.simps(4))
qed

section \<open>Timelock Freedom\<close>

fun timelock_free_trace :: "'e tttrace \<Rightarrow> bool" where
  "timelock_free_trace [] = True" |
  "timelock_free_trace ([e]\<^sub>E # \<rho>) = timelock_free_trace \<rho>" |
  "timelock_free_trace ([X]\<^sub>R # \<rho>) = (Tock \<notin> X \<and> timelock_free_trace \<rho>)"

definition timelock_free :: "'e ttprocess \<Rightarrow> bool" where
  "timelock_free P = (\<forall>t\<in>P. timelock_free_trace t)"

lemma tt_prefix_subset_timelock_free:
  "\<rho> \<lesssim>\<^sub>C \<sigma> \<Longrightarrow> timelock_free_trace \<sigma> \<Longrightarrow> timelock_free_trace \<rho>"
  by (induct \<rho> \<sigma> rule:tt_prefix_subset.induct, auto)

lemma TT2_timelock_free_contains_tock: 
  assumes TT2_P: "TT2 P" and timelock_free_P: "timelock_free P" and s_X_in_P: "s @ [[X]\<^sub>R] \<in> P"
  shows "s @ [[X]\<^sub>R, [Tock]\<^sub>E] \<in> P"
proof -
  have "timelock_free_trace (s @ [[X]\<^sub>R]) \<Longrightarrow> Tock \<notin> X"
    by (induct s rule:timelock_free_trace.induct, auto)
  have "s @ [[X]\<^sub>R, [Tock]\<^sub>E] \<notin> P \<Longrightarrow> s @ [[X \<union> {Tock}]\<^sub>R] \<in> P"
    using TT2_P s_X_in_P unfolding TT2_def apply (auto)
    by (erule_tac x=s in allE, erule_tac x="[]" in allE, erule_tac x=X in allE, erule_tac x="{Tock}" in allE, auto)
  also have "timelock_free_trace (s @ [[X \<union> {Tock}]\<^sub>R]) \<Longrightarrow> False"
    by (induct s rule:timelock_free_trace.induct, auto)
  then show "s @ [[X]\<^sub>R, [Tock]\<^sub>E] \<in> P"
    using s_X_in_P timelock_free_P calculation unfolding timelock_free_def by auto
qed

lemma timelock_free_refusal_implies_tock:
  "timelock_free P \<Longrightarrow> TT2 P \<Longrightarrow> t @ [[Z]\<^sub>R] \<in> P \<Longrightarrow> t @ [[Z]\<^sub>R, [Tock]\<^sub>E] \<in> P"
  unfolding TT2_def timelock_free_def
proof (erule_tac x="t" in allE, erule_tac x="[]" in allE, auto, erule_tac x=Z in allE, erule_tac x="{Tock}" in allE, auto)
  assume "\<forall>x\<in>P. timelock_free_trace x" "t @ [[insert Tock Z]\<^sub>R] \<in> P"
  then have "timelock_free_trace (t @ [[insert Tock Z]\<^sub>R])"
    by auto
  then have "False"
    by (induct t rule:timelock_free_trace.induct, auto)
  then show "t @ [[Z]\<^sub>R, [Tock]\<^sub>E] \<in> P"
    by auto
qed

lemma timelock_free_StopTT: "timelock_free STOP\<^sub>C"
  unfolding timelock_free_def StopTT_def
proof auto
  fix s :: "'a tttrace"
  show "s \<in> tocks {x. x \<noteq> Tock} \<Longrightarrow> timelock_free_trace s"
    by (induct s rule:tocks.induct, auto)
next
  fix s :: "'a tttrace" and X
  show "s \<in> tocks {x. x \<noteq> Tock} \<Longrightarrow> Tock \<notin> X \<Longrightarrow> timelock_free_trace (s @ [[X]\<^sub>R])"
    by (induct s rule:tocks.induct, auto)
qed

lemma RenamingTT_timelock_free:
  "\<forall>x\<in>P. ttWF x \<Longrightarrow> timelock_free P \<Longrightarrow> timelock_free (RenamingTT P f)"
  unfolding timelock_free_def RenamingTT_def
proof auto
  fix x
  have "\<And>xa P. ttWF x \<Longrightarrow> \<forall>x\<in>P. timelock_free_trace x \<Longrightarrow> xa \<in> P \<Longrightarrow> x \<in> rename_trace f xa \<Longrightarrow> timelock_free_trace x"
    apply (induct x rule:ttWF.induct, auto, case_tac xa rule:ttWF.cases, auto)
    apply (case_tac xa rule:ttWF.cases, auto, metis insertI1 singletonD timelock_free_trace.simps(2))
    by (case_tac xa rule:ttWF.cases, auto, metis insertI1 singletonD timelock_free_trace.simps(2) timelock_free_trace.simps(3))
  then show "\<And>xa. \<forall>x\<in>P. ttWF x \<Longrightarrow> \<forall>x\<in>P. timelock_free_trace x \<Longrightarrow> xa \<in> P \<Longrightarrow> x \<in> rename_trace f xa \<Longrightarrow> timelock_free_trace x"
    using rename_trace_ttWF by blast
qed

lemma PrefixTT_timelock_free:
  "timelock_free P \<Longrightarrow> timelock_free (e \<rightarrow>\<^sub>C P)"
  unfolding timelock_free_def PrefixTT_def
proof auto
  fix s
  show "s \<in> tocks {x. x \<noteq> Tock \<and> x \<noteq> Event e} \<Longrightarrow> timelock_free_trace s"
    apply (induct s rule:ttWF.induct, auto simp add: notin_tocks)
    apply (metis (mono_tags, lifting) mem_Collect_eq tocks_wf ttWF.simps(5))
    using tocks.simps by auto
next
  fix s X
  show "s \<in> tocks {x. x \<noteq> Tock \<and> x \<noteq> Event e} \<Longrightarrow> Tock \<notin> X \<Longrightarrow> timelock_free_trace (s @ [[X]\<^sub>R])"
    apply (induct s rule:ttWF.induct, auto simp add: notin_tocks)
    apply (metis (mono_tags, lifting) mem_Collect_eq tocks_wf ttWF.simps(5))
    using tocks.simps by auto
next
  fix s
  show "s \<in> tocks {x. x \<noteq> Tock \<and> x \<noteq> Event e} \<Longrightarrow> timelock_free_trace s"
    apply (induct s rule:ttWF.induct, auto simp add: notin_tocks)
    apply (metis (mono_tags, lifting) mem_Collect_eq tocks_wf ttWF.simps(5))
    using tocks.simps by auto
next
  fix s \<sigma>
  show "\<forall>x\<in>P. timelock_free_trace x \<Longrightarrow> s \<in> tocks {x. x \<noteq> Tock \<and> x \<noteq> Event e} \<Longrightarrow> \<sigma> \<in> P \<Longrightarrow> timelock_free_trace (s @ [Event e]\<^sub>E # \<sigma>)"
    apply (induct s rule:ttWF.induct, auto simp add: notin_tocks)
    apply (metis (mono_tags, lifting) mem_Collect_eq tocks_wf ttWF.simps(5))
    using tocks.cases by auto
qed

lemma StrictTimedInterruptTT_timelock_free:
  "timelock_free P \<Longrightarrow> timelock_free Q \<Longrightarrow> timelock_free (P \<triangle>\<^bsub>n\<^esub> Q)"
  unfolding StrictTimedInterruptTT_def timelock_free_def
proof auto
  fix p q
  assume "\<forall>x\<in>P. timelock_free_trace x" "\<forall>x\<in>Q. timelock_free_trace x" "p \<in> P" "q \<in> Q"
  then have "timelock_free_trace p \<and> timelock_free_trace q"
    by auto
  then show "timelock_free_trace (p @ q)"
    by (induct p rule:timelock_free_trace.induct, auto)
qed

lemma TimeSyncInterruptTT_timelock_free:
  "timelock_free P \<Longrightarrow> timelock_free Q \<Longrightarrow> timelock_free (P \<triangle>\<^sub>T Q)"
  unfolding timelock_free_def TimeSyncInterruptTT_def
proof (safe, simp_all)
  fix p X Y Z
  assume "Ball Q timelock_free_trace" "filter_tocks p @ [[Y]\<^sub>R] \<in> Q"
  then have "timelock_free_trace (filter_tocks p @ [[Y]\<^sub>R])"
    by blast
  then have "Tock \<notin> Y"
    by (induct p rule:filter_tocks.induct, auto)
  then have "Z \<subseteq> X \<union> Y \<Longrightarrow> {e \<in> X. e \<noteq> Tock} = {e \<in> Y. e \<noteq> Tock} \<Longrightarrow> Z \<subseteq> X"
    by blast
  also assume "Ball P timelock_free_trace" "p @ [[X]\<^sub>R] \<in> P"
  then have "timelock_free_trace (p @ [[X]\<^sub>R])"
    by blast
  then show "Z \<subseteq> X \<union> Y \<Longrightarrow> {e \<in> X. e \<noteq> Tock} = {e \<in> Y. e \<noteq> Tock} \<Longrightarrow>
      timelock_free_trace (p @ [[Z]\<^sub>R])"
    using calculation by (induct p rule:timelock_free_trace.induct, auto)
next
  fix p q2
  assume "Ball P timelock_free_trace" "Ball Q timelock_free_trace" "p \<in> P" "filter_tocks p @ q2 \<in> Q"
  then have "timelock_free_trace p \<and> timelock_free_trace (filter_tocks p @ q2)"
    by blast
  then show "timelock_free_trace (p @ q2)"
    by (induct p rule:timelock_free_trace.induct, auto, case_tac \<rho> rule:ttWF.cases, auto)
qed


lemma PrefixTT_refusal_implies_tock: "[[Z]\<^sub>R] \<in> e \<rightarrow>\<^sub>C P \<Longrightarrow> [[Z]\<^sub>R, [Tock]\<^sub>E] \<in> e \<rightarrow>\<^sub>C P"
  unfolding PrefixTT_def using tocks.simps by (auto simp add: notin_tocks Cons_eq_append_conv)

lemma timelock_free_TimeSyncInterruptTT_PrefixTT_refusal_implies_tock:
  assumes TT1_P: "TT1 P" and TT2_P: "TT2 P" and P_timelock_free: "timelock_free P"
  assumes e_notin_Z: "Event e \<notin> Z"
  shows "[[Z]\<^sub>R] \<in> P \<triangle>\<^sub>T e \<rightarrow>\<^sub>C Q \<Longrightarrow> [[Z]\<^sub>R, [Tock]\<^sub>E] \<in> P \<triangle>\<^sub>T e \<rightarrow>\<^sub>C Q"
proof -
  assume "[[Z]\<^sub>R] \<in> P \<triangle>\<^sub>T e \<rightarrow>\<^sub>C Q"
  then obtain X Y where "[[X]\<^sub>R] \<in> P \<and> [[Y]\<^sub>R] \<in> e \<rightarrow>\<^sub>C Q \<and> Z \<subseteq> X \<union> Y \<and> {e \<in> X. e \<noteq> Tock} = {e \<in> Y. e \<noteq> Tock}"
    unfolding TimeSyncInterruptTT_def by (auto, metis (no_types, lifting) append_eq_Cons_conv append_is_Nil_conv)
  then have "Tock \<notin> X \<and> Tock \<notin> Y \<and> [[X]\<^sub>R] \<in> P \<and> [[Y]\<^sub>R] \<in> e \<rightarrow>\<^sub>C Q \<and> Z \<subseteq> X \<and> X = Y"
    unfolding PrefixTT_def apply (safe, simp_all add: notin_tocks Cons_eq_append_conv)
    using P_timelock_free timelock_free_def timelock_free_trace.simps(3) by fastforce+
  then have "Tock \<notin> X \<and> Tock \<notin> Y \<and> [[X]\<^sub>R, [Tock]\<^sub>E] \<in> P \<and> [[Y]\<^sub>R, [Tock]\<^sub>E] \<in> e \<rightarrow>\<^sub>C Q \<and> Z \<subseteq> X \<and> X = Y"
    by (metis P_timelock_free PrefixTT_refusal_implies_tock TT2_P append.left_neutral timelock_free_refusal_implies_tock)
  then show "[[Z]\<^sub>R, [Tock]\<^sub>E] \<in> P \<triangle>\<^sub>T e \<rightarrow>\<^sub>C Q"
    unfolding TimeSyncInterruptTT_def apply (auto, rule_tac x="[[Z]\<^sub>R, [Tock]\<^sub>E]" in exI, auto)
    using TT1_P TT1_def tt_prefix_subset.simps(2) tt_prefix_subset_refl apply blast
    by (smt PrefixTT_def PrefixTT_refusal_implies_tock Un_iff append_Nil e_notin_Z mem_Collect_eq subsetCE tocks.empty_in_tocks)
qed

subsection \<open>Timed Chaos\<close>

definition TChaosTT :: "'a ttprocess" where
  "TChaosTT = {t. ttWF t \<and> timelock_free_trace t}"

lemma TChaos_wf:
  "\<forall>x\<in>TChaosTT. ttWF x"
  unfolding TChaosTT_def by auto

lemma TT0_TChaos:
  "TT0 TChaosTT"
  unfolding TChaosTT_def TT0_def by (auto, rule_tac x="[]" in exI, auto)

lemma TT1_TChaos:
  "TT1 TChaosTT"
  unfolding TChaosTT_def TT1_def apply auto
  using tt_prefix_subset_ttWF apply blast
  using tt_prefix_subset_timelock_free by blast

lemma TT2_TChaos:
  "TT2 TChaosTT"
  unfolding TT2_def
proof auto
  fix \<rho> \<sigma> :: "'a tttrace" and X Y
  assume \<rho>_X_\<sigma>_in_TChaos: "\<rho> @ [X]\<^sub>R # \<sigma> \<in> TChaosTT"
  assume Y_disjoint: "Y \<inter> {e. e \<noteq> Tock \<and> \<rho> @ [[e]\<^sub>E] \<in> TChaosTT \<or> e = Tock \<and> \<rho> @ [[X]\<^sub>R, [e]\<^sub>E] \<in> TChaosTT} = {}"

  have "\<rho> @ [[X]\<^sub>R, [Tock]\<^sub>E] \<in> TChaosTT"
    using \<rho>_X_\<sigma>_in_TChaos unfolding TChaosTT_def by (simp, induct \<rho> rule:ttWF.induct, auto)
  then have "Tock \<notin> Y"
    using Y_disjoint by blast
  then show "\<rho> @ [X \<union> Y]\<^sub>R # \<sigma> \<in> TChaosTT"
    using \<rho>_X_\<sigma>_in_TChaos unfolding TChaosTT_def
    by (simp, induct \<rho> rule:ttWF.induct, auto, cases \<sigma> rule:ttWF.cases, auto)
qed

lemma TChaos_timelock_free:
  "timelock_free TChaosTT"
  unfolding TChaosTT_def timelock_free_def by auto

section \<open>Timelock event and partial ordering\<close>

datatype 'e timelock_event = Timelock | OtherEvent 'e

fun timelock_ordering :: "'e timelock_event ttevent \<Rightarrow> 'e timelock_event ttevent \<Rightarrow> bool" where
  "timelock_ordering (Event Timelock) Tock = True" |
  "timelock_ordering a b = (a=b)"

lemma timelock_ordering_is_order: "timelock_ordering \<in> {x. class.order x (Event_Priority.less x)}"
  unfolding class.order_def class.preorder_def class.order_axioms_def apply auto
  by (case_tac x, auto, case_tac x, auto, case_tac y, auto, case_tac x, auto)

lemma timelock_ordering_porder_cancel: "porder2f (f2porder timelock_ordering) = timelock_ordering"
   using timelock_ordering_is_order by (subst f2porder_inverse[where y = timelock_ordering], auto)

lemma Timelock_not_maximal: "\<not> maximal(f2porder timelock_ordering, Event Timelock)"
  unfolding maximal_def my_le_def by (auto, rule_tac x="Tock" in exI, auto simp add: timelock_ordering_porder_cancel)

lemma Tock_maximal: "maximal(f2porder timelock_ordering, Tock)"
  unfolding maximal_def my_le_def by (auto simp add: timelock_ordering_porder_cancel)

lemma Tick_maximal: "maximal(f2porder timelock_ordering, Tick)"
  unfolding maximal_def my_le_def by (auto simp add: timelock_ordering_porder_cancel)

lemma OtherEvent_maximal: "maximal(f2porder timelock_ordering, Event (OtherEvent e))"
  unfolding maximal_def my_le_def by (auto simp add: timelock_ordering_porder_cancel)

subsection \<open>Lemmas related to prioritisation using timelock_ordering\<close>

lemma timelock_ordering_prirefTT: "TT2 P \<Longrightarrow> timelock_free P \<Longrightarrow> \<sigma> @ [[X]\<^sub>R] \<in> P \<Longrightarrow>
  prirefTT (f2porder timelock_ordering) \<sigma> P X = X \<union> {Event Timelock}"
  unfolding prirefTT_def my_le_def my_lt_def apply (auto simp add: timelock_ordering_porder_cancel)
  using timelock_ordering.elims(2) apply blast+
  using timelock_free_refusal_implies_tock by blast

lemma PriTT_timelock_ordering_init_tock:
  "\<forall>x\<in>P. ttWF x \<Longrightarrow> TT1 P \<Longrightarrow> TT2 P \<Longrightarrow> timelock_free P \<Longrightarrow>
    {t. [X]\<^sub>R # [Tock]\<^sub>E # t \<in> PriTT (f2porder timelock_ordering) P}
      = PriTT (f2porder timelock_ordering) {t. [{e\<in>X. e \<noteq> Event Timelock}]\<^sub>R # [Tock]\<^sub>E # t \<in> P}"
  unfolding PriTT_def
proof auto
  fix x s
  assume P_wf: "\<forall>x\<in>P. ttWF x" and TT1_P: "TT1 P" and TT2_P: "TT2 P" and P_timelock_free: "timelock_free P"
  assume s_in_P: "s \<in> P"
  
  assume "([X]\<^sub>R # [Tock]\<^sub>E # x) priTT\<^sub>[\<^sub>f2porder timelock_ordering\<^sub>,\<^sub>[]\<^sub>,\<^sub>P\<^sub>] s"
  then obtain Y y where x_priTT_y: "x priTT\<^sub>[\<^sub>f2porder timelock_ordering\<^sub>,\<^sub>[[Y]\<^sub>R, [Tock]\<^sub>E]\<^sub>,\<^sub>P\<^sub>] y" and
      s_def: "s = [Y]\<^sub>R # [Tock]\<^sub>E # y" and
      X_subset_prirefTT_Y: "X \<subseteq> prirefTT (f2porder timelock_ordering) [] P Y"
    by (cases s rule:ttWF.cases, auto)

  have ttWF_y: "ttWF y"
    using P_wf s_def s_in_P ttWF.simps(5) by blast
  have ttWF_x: "ttWF x"
    using ttWF_priTT_imp_ttWF2 ttWF_y x_priTT_y by blast

  have 1: "x priTT\<^sub>[\<^sub>f2porder timelock_ordering\<^sub>,\<^sub>[]\<^sub>,\<^sub>{t. [Y]\<^sub>R # [Tock]\<^sub>E # t \<in> P}\<^sub>] y"
    using ttWF_y priTT_prefix_eq[where \<sigma>="[[Y]\<^sub>R, [Tock]\<^sub>E]", where \<rho>="[]"] x_priTT_y by auto

  have "{e\<in>prirefTT (f2porder timelock_ordering) [] P Y. e \<noteq> Event Timelock} = {e\<in>Y. e \<noteq> Event Timelock}"
    unfolding prirefTT_def apply auto
    by (metis OtherEvent_maximal Tick_maximal Tock_maximal some_higher_not_maximal timelock_event.exhaust ttevent.exhaust)+
  then have 2: "{e\<in>X. e \<noteq> Event Timelock} \<subseteq> Y"
    using X_subset_prirefTT_Y by auto
  then have "{t. [Y]\<^sub>R # [Tock]\<^sub>E # t \<in> P} \<subseteq> {t. [{e\<in>X. e \<noteq> Event Timelock}]\<^sub>R # [Tock]\<^sub>E # t \<in> P}"
    apply auto using TT1_P TT1_def tt_prefix_subset.simps(2) tt_prefix_subset_refl by blast
  then have "\<And>\<sigma>. x priTT\<^sub>[\<^sub>f2porder timelock_ordering\<^sub>,\<^sub>\<sigma>\<^sub>,\<^sub>{t. [Y]\<^sub>R # [Tock]\<^sub>E # t \<in> P}\<^sub>] y \<Longrightarrow>
      x priTT\<^sub>[\<^sub>f2porder timelock_ordering\<^sub>,\<^sub>\<sigma>\<^sub>,\<^sub>{t. [{e\<in>X. e \<noteq> Event Timelock}]\<^sub>R # [Tock]\<^sub>E # t \<in> P}\<^sub>] y"
    using ttWF_y ttWF_x apply -
  proof (induct x y rule:ttWF2.induct, auto)
    fix Xa Ya \<sigma> x
    show "Xa \<subseteq> prirefTT (f2porder timelock_ordering) \<sigma> {t. [Y]\<^sub>R # [Tock]\<^sub>E # t \<in> P} Ya \<Longrightarrow>
        {t. [Y]\<^sub>R # [Tock]\<^sub>E # t \<in> P} \<subseteq> {t. [{e \<in> X. e \<noteq> Event Timelock}]\<^sub>R # [Tock]\<^sub>E # t \<in> P} \<Longrightarrow>
        x \<in> Xa \<Longrightarrow> x \<in> prirefTT (f2porder timelock_ordering) \<sigma> {t. [{e \<in> X. e \<noteq> Event Timelock}]\<^sub>R # [Tock]\<^sub>E # t \<in> P} Ya"
      by (meson prirefTT_subset subset_iff)
  next
    fix \<rho> f \<sigma> \<sigma>' Z
    assume Z_in_P: "[Y]\<^sub>R # [Tock]\<^sub>E # \<sigma>' @ [[Z]\<^sub>R] \<in> P"
    assume f_in_prirefTT_Z: "Event f \<notin> prirefTT (f2porder timelock_ordering) \<sigma>' {t. [Y]\<^sub>R # [Tock]\<^sub>E # t \<in> P} Z"

    show "maximal(f2porder timelock_ordering,Event f)"
    proof (cases f, auto simp add: OtherEvent_maximal)
      have "timelock_free_trace ([Y]\<^sub>R # [Tock]\<^sub>E # \<sigma>' @ [[Z]\<^sub>R])"
        using Z_in_P P_timelock_free unfolding timelock_free_def by auto
      then have "Tock \<notin> Z"
        by (auto, induct \<sigma>' rule:timelock_free_trace.induct, auto)
      then have 1: "[Y]\<^sub>R # [Tock]\<^sub>E # \<sigma>' @ [[Z]\<^sub>R, [Tock]\<^sub>E] \<in> P"
        using TT2_P Z_in_P unfolding TT2_def apply auto
        apply (erule_tac x="[Y]\<^sub>R # [Tock]\<^sub>E # \<sigma>'" in allE, erule_tac x="[]" in allE)
      proof (erule_tac x="Z" in allE, erule_tac x="{Tock}" in allE, auto)
        assume "[Y]\<^sub>R # [Tock]\<^sub>E # \<sigma>' @ [[insert Tock Z]\<^sub>R] \<in> P"
        then have "timelock_free_trace ([Y]\<^sub>R # [Tock]\<^sub>E # \<sigma>' @ [[insert Tock Z]\<^sub>R])"
          using P_timelock_free unfolding timelock_free_def by auto
        then have "False"
          by (induct \<sigma>' rule:timelock_free_trace.induct, auto)
        then show "[Y]\<^sub>R # [Tock]\<^sub>E # \<sigma>' @ [[Z]\<^sub>R, [Tock]\<^sub>E] \<in> P"
          by auto
      qed

      assume "f  = Timelock"
      then have 2: "[Y]\<^sub>R # [Tock]\<^sub>E # \<sigma>' @ [[Z]\<^sub>R, [Tock]\<^sub>E] \<notin> P"
        using f_in_prirefTT_Z unfolding prirefTT_def my_lt_def my_le_def by (auto simp add: timelock_ordering_porder_cancel)

      show "maximal(f2porder timelock_ordering,Event Timelock)"
        using 1 2 by auto
    qed
  next
    fix Xa \<rho> Ya \<sigma> \<sigma>' x
    show "{t. [Y]\<^sub>R # [Tock]\<^sub>E # t \<in> P} \<subseteq> {t. [{e \<in> X. e \<noteq> Event Timelock}]\<^sub>R # [Tock]\<^sub>E # t \<in> P} \<Longrightarrow>
        Xa \<subseteq> prirefTT (f2porder timelock_ordering) \<sigma>' {t. [Y]\<^sub>R # [Tock]\<^sub>E # t \<in> P} Ya \<Longrightarrow>
        x \<in> Xa \<Longrightarrow> x \<in> prirefTT (f2porder timelock_ordering) \<sigma>' {t. [{e \<in> X. e \<noteq> Event Timelock}]\<^sub>R # [Tock]\<^sub>E # t \<in> P} Ya"
      by (meson prirefTT_subset subset_iff)
  next
    fix Xa \<rho> Ya \<sigma> \<sigma>'
    show "Tock \<in> prirefTT (f2porder timelock_ordering) \<sigma>' {t. [{e \<in> X. e \<noteq> Event Timelock}]\<^sub>R # [Tock]\<^sub>E # t \<in> P} Ya \<Longrightarrow> 
        Tock \<notin> Ya \<Longrightarrow> False"
      using Tock_maximal maximal_notin_prirefTT by blast
  qed
  then have 3: "x priTT\<^sub>[\<^sub>f2porder timelock_ordering\<^sub>,\<^sub>[]\<^sub>,\<^sub>{t. [{e\<in>X. e \<noteq> Event Timelock}]\<^sub>R # [Tock]\<^sub>E # t \<in> P}\<^sub>] y"
    using "1" by blast

  have 4: "[{e \<in> X. e \<noteq> Event Timelock}]\<^sub>R # [Tock]\<^sub>E # y \<in> P"
    using "2" TT1_P TT1_def s_def s_in_P tt_prefix_subset.simps(2) tt_prefix_subset_refl by blast

  show "\<exists>s. x priTT\<^sub>[\<^sub>(f2porder timelock_ordering)\<^sub>,\<^sub>[]\<^sub>,\<^sub>{t. [{e \<in> X. e \<noteq> Event Timelock}]\<^sub>R # [Tock]\<^sub>E # t \<in> P}\<^sub>] s \<and> [{e \<in> X. e \<noteq> Event Timelock}]\<^sub>R # [Tock]\<^sub>E # s \<in> P"
    using 3 4 by (rule_tac x="y" in exI, auto)
next
  fix x s
  assume P_wf: "\<forall>x\<in>P. ttWF x" and TT1_P: "TT1 P" and TT2_P: "TT2 P" and P_timelock_free: "timelock_free P"
  assume x_priTT_s: "x priTT\<^sub>[\<^sub>f2porder timelock_ordering\<^sub>,\<^sub>[]\<^sub>,\<^sub>{t. [{e \<in> X. e \<noteq> Event Timelock}]\<^sub>R # [Tock]\<^sub>E # t \<in> P}\<^sub>] s"
  assume tock_s_in_P: "[{e \<in> X. e \<noteq> Event Timelock}]\<^sub>R # [Tock]\<^sub>E # s \<in> P"
  then have 1: "prirefTT (f2porder timelock_ordering) [] P {e \<in> X. e \<noteq> Event Timelock} = X \<union> {Event Timelock}"
    unfolding prirefTT_def my_lt_def my_le_def apply safe apply (simp_all add: timelock_ordering_porder_cancel)
    apply (case_tac x, auto, case_tac x1, auto)
    using timelock_ordering.elims(2) apply blast
    apply (meson TT1_P TT1_def subset_iff tt_prefix_subset.simps(1) tt_prefix_subset.simps(2) tt_prefix_subset.simps(3))
    apply (meson TT1_P TT1_def tt_prefix_subset.simps(1) tt_prefix_subset.simps(2) tt_prefix_subset.simps(3) tt_prefix_subset_refl)
    by (meson TT1_P TT1_def equalityE tt_prefix_subset.simps(1) tt_prefix_subset.simps(2) tt_prefix_subset.simps(3))

  have ttWF_s: "ttWF s"
    using P_wf tock_s_in_P ttWF.simps(5) by blast
  have ttWF_x: "ttWF x"
    using ttWF_priTT_imp_ttWF2 ttWF_s x_priTT_s by blast

  have 2: "x priTT\<^sub>[\<^sub>f2porder timelock_ordering\<^sub>,\<^sub>[[{e \<in> X. e \<noteq> Event Timelock}]\<^sub>R, [Tock]\<^sub>E]\<^sub>,\<^sub>P\<^sub>] s"
    using x_priTT_s ttWF_s priTT_prefix_eq[where \<sigma>="[[{e \<in> X. e \<noteq> Event Timelock}]\<^sub>R, [Tock]\<^sub>E]"] by fastforce 
  
  show "x priTT\<^sub>[\<^sub>f2porder timelock_ordering\<^sub>,\<^sub>[]\<^sub>,\<^sub>{t. [{e \<in> X. e \<noteq> Event Timelock}]\<^sub>R # [Tock]\<^sub>E # t \<in> P}\<^sub>] s \<Longrightarrow>
      \<exists>s. ([X]\<^sub>R # [Tock]\<^sub>E # x) priTT\<^sub>[\<^sub>f2porder timelock_ordering\<^sub>,\<^sub>[]\<^sub>,\<^sub>P\<^sub>] s \<and> s \<in> P"
    using tock_s_in_P P_wf 1 2 by (rule_tac x="[{e \<in> X. e \<noteq> Event Timelock}]\<^sub>R # [Tock]\<^sub>E # s" in exI, auto)
qed

fun tttrace_contains_event :: "'a ttevent \<Rightarrow> 'a tttrace \<Rightarrow> bool" where
  "tttrace_contains_event x [] = False" |
  "tttrace_contains_event x ([X]\<^sub>R # \<rho>) = tttrace_contains_event x \<rho>" |
  "tttrace_contains_event x ([e]\<^sub>E # \<rho>) = (x = e \<or> tttrace_contains_event x \<rho>)"

fun tttrace_refusal_contains_event :: "'a ttevent \<Rightarrow> 'a tttrace \<Rightarrow> bool" where
  "tttrace_refusal_contains_event x [] = False" |
  "tttrace_refusal_contains_event x ([X]\<^sub>R # \<rho>) = (x \<in> X \<or> tttrace_refusal_contains_event x \<rho>)" |
  "tttrace_refusal_contains_event x ([e]\<^sub>E # \<rho>) = tttrace_refusal_contains_event x \<rho>"

fun tttrace_insert_event_refusal :: "'a ttevent \<Rightarrow> 'a tttrace \<Rightarrow> 'a tttrace" where
  "tttrace_insert_event_refusal x [] = []" |
  "tttrace_insert_event_refusal x ([X]\<^sub>R # \<rho>) = [insert x X]\<^sub>R # tttrace_insert_event_refusal x \<rho>" |
  "tttrace_insert_event_refusal x ([e]\<^sub>E # \<rho>) = [e]\<^sub>E # tttrace_insert_event_refusal x \<rho>"


lemma timelock_ordering_priTT_reflexive:
  "\<And>P \<sigma>. \<not> tttrace_contains_event (Event Timelock) \<rho> \<Longrightarrow> ttWF \<rho> \<Longrightarrow> \<rho> priTT\<^sub>[\<^sub>f2porder timelock_ordering\<^sub>,\<^sub>\<sigma>\<^sub>,\<^sub>P\<^sub>] \<rho>"
  apply (induct \<rho> rule:ttWF.induct, auto)
  unfolding prirefTT_def apply auto
  using Tick_maximal apply blast
  apply (metis OtherEvent_maximal timelock_event.exhaust)
  by (meson Tock_maximal some_higher_not_maximal)

section \<open>Function to add undefined behaviour after a deadline miss to a specification\<close>

definition remove_timelock_spec :: "'e ttprocess \<Rightarrow> 'e timelock_event ttprocess" where
  "remove_timelock_spec P =
    (PriTT (f2porder timelock_ordering) ((RenamingTT P OtherEvent) \<triangle>\<^sub>T (Timelock \<rightarrow>\<^sub>C (STOP\<^sub>C \<triangle>\<^bsub>1\<^esub> TChaosTT))) \<setminus>\<^sub>C {Event Timelock})"

lemma Timelock_prefix_deadline_miss_wf:
  "\<forall>x\<in>(Timelock \<rightarrow>\<^sub>C (STOP\<^sub>C \<triangle>\<^bsub>Suc 0\<^esub> TChaosTT)). ttWF x"
  by (metis (no_types, hide_lams) PrefixTT_wf StopTT_wf StrictTimedInterruptTT_wf TChaos_wf)

lemma Timelock_prefix_deadline_miss_ttWFx:
  "ttWFx (Timelock \<rightarrow>\<^sub>C (STOP\<^sub>C \<triangle>\<^bsub>Suc 0\<^esub> TChaosTT))"
  using Timelock_prefix_deadline_miss_wf ttWF_is_ttWFw_ttWFx ttWFx_def by blast

lemma unprioiritised_remove_timelock_spec_wf:
  "\<forall>x\<in>P. ttWF x \<Longrightarrow> \<forall>x\<in>(RenamingTT P OtherEvent \<triangle>\<^sub>T Timelock \<rightarrow>\<^sub>C (STOP\<^sub>C \<triangle>\<^bsub>Suc 0\<^esub> TChaosTT)). ttWF x"
  by (smt RenamingTT_wf TimeSyncInterruptTT_wf Timelock_prefix_deadline_miss_wf)

lemma Timelock_prefix_deadline_miss_TT1:
  "TT1 (Timelock \<rightarrow>\<^sub>C (STOP\<^sub>C \<triangle>\<^bsub>Suc 0\<^esub> TChaosTT))"
  by (simp add: TT1_Prefix TT1_Stop TT1_StrictTimedInterrupt TT1_TChaos)

lemma unprioiritised_remove_timelock_spec_TT1:
  "\<forall>x\<in>P. ttWF x \<Longrightarrow> TT1 P \<Longrightarrow> TT1 (RenamingTT P OtherEvent \<triangle>\<^sub>T Timelock \<rightarrow>\<^sub>C (STOP\<^sub>C \<triangle>\<^bsub>Suc 0\<^esub> TChaosTT))"
  by (simp add: RenamingTT_wf TT1_Renaming TT1_TimeSyncInterrupt Timelock_prefix_deadline_miss_TT1 Timelock_prefix_deadline_miss_wf)

lemma Timelock_prefix_deadline_miss_TT2:
  "TT2 (Timelock \<rightarrow>\<^sub>C (STOP\<^sub>C \<triangle>\<^bsub>Suc 0\<^esub> TChaosTT))"
  by (simp add: TT0_Stop TT0_StrictTimedInterrupt TT0_TChaos TT1_Stop TT1_StrictTimedInterrupt TT1_TChaos
        TT2_Prefix TT2_Stop TT2_StrictTimedInterrupt TT2_TChaos)

lemma Renaming_ttWFx:
  "\<forall>x\<in>P. ttWF x \<Longrightarrow> ttWFx (RenamingTT P OtherEvent)"
  using ttWF_is_ttWFw_ttWFx ttWFx_def RenamingTT_wf by blast

lemma unprioiritised_remove_timelock_spec_TT2:
  "\<forall>x\<in>P. ttWF x \<Longrightarrow> TT1 P \<Longrightarrow> TT2 P \<Longrightarrow> TT2 (RenamingTT P OtherEvent \<triangle>\<^sub>T Timelock \<rightarrow>\<^sub>C (STOP\<^sub>C \<triangle>\<^bsub>Suc 0\<^esub> TChaosTT))"
  by (simp add: RenamingTT_wf Renaming_ttWFx TT1_Renaming TT2_Renaming TT2_TimeSyncInterrupt Timelock_prefix_deadline_miss_TT1
        Timelock_prefix_deadline_miss_TT2 Timelock_prefix_deadline_miss_ttWFx Timelock_prefix_deadline_miss_wf)

lemma Timelock_prefix_deadline_miss_timelock_free:
  "timelock_free (Timelock \<rightarrow>\<^sub>C (STOP\<^sub>C \<triangle>\<^bsub>Suc 0\<^esub> TChaosTT))"
  by (simp add: PrefixTT_timelock_free StrictTimedInterruptTT_timelock_free TChaos_timelock_free timelock_free_StopTT)

lemma unprioiritised_remove_timelock_spec_timelock_free:
  "\<forall>x\<in>P. ttWF x \<Longrightarrow> timelock_free P \<Longrightarrow> timelock_free (RenamingTT P OtherEvent \<triangle>\<^sub>T Timelock \<rightarrow>\<^sub>C (STOP\<^sub>C \<triangle>\<^bsub>Suc 0\<^esub> TChaosTT))"
  by (simp add: RenamingTT_timelock_free TimeSyncInterruptTT_timelock_free Timelock_prefix_deadline_miss_timelock_free)

lemma unhidden_remove_timelock_spec_init_event:
  assumes P_wf: "\<forall>x\<in>P. ttWF x"
  shows "{t. [Event (OtherEvent e')]\<^sub>E # t \<in> PriTT (f2porder timelock_ordering) (RenamingTT P OtherEvent \<triangle>\<^sub>T Timelock \<rightarrow>\<^sub>C (STOP\<^sub>C \<triangle>\<^bsub>Suc 0\<^esub> TChaosTT))}
    = PriTT (f2porder timelock_ordering) (RenamingTT {t. [Event e']\<^sub>E # t \<in> P} OtherEvent \<triangle>\<^sub>T Timelock \<rightarrow>\<^sub>C (STOP\<^sub>C \<triangle>\<^bsub>Suc 0\<^esub> TChaosTT))"
  (is "?lhs = ?rhs")
proof -
  have "?lhs = PriTT (f2porder timelock_ordering) {t. [Event (OtherEvent e')]\<^sub>E # t \<in> RenamingTT P OtherEvent \<triangle>\<^sub>T Timelock \<rightarrow>\<^sub>C (STOP\<^sub>C \<triangle>\<^bsub>Suc 0\<^esub> TChaosTT)}"
    by (metis OtherEvent_maximal P_wf PriTT_init_event unprioiritised_remove_timelock_spec_wf)
  also have "... = PriTT (f2porder timelock_ordering) ({t. [Event (OtherEvent e')]\<^sub>E # t \<in> RenamingTT P OtherEvent} \<triangle>\<^sub>T Timelock \<rightarrow>\<^sub>C (STOP\<^sub>C \<triangle>\<^bsub>Suc 0\<^esub> TChaosTT))"
    by (simp add: TimeSyncInterruptTT_PrefixTT_init_event)
  also have "... = ?rhs"
    by (simp add: RenamingTT_init_event inj_def)
  then show ?thesis
    using calculation by auto
qed

lemma unhidden_remove_timelock_spec_init_tock:
  assumes P_wf: "\<forall>x\<in>P. ttWF x" and TT1_P: "TT1 P" and TT2_P: "TT2 P" and P_timelock_free: "timelock_free P"
  shows "{t. [X']\<^sub>R # [Tock]\<^sub>E # t \<in> PriTT (f2porder timelock_ordering) (RenamingTT P OtherEvent \<triangle>\<^sub>T Timelock \<rightarrow>\<^sub>C (STOP\<^sub>C \<triangle>\<^bsub>Suc 0\<^esub> TChaosTT))}
      = PriTT (f2porder timelock_ordering) (RenamingTT {t. [(lift_renaming_func OtherEvent) -` X']\<^sub>R # [Tock]\<^sub>E # t \<in> P} OtherEvent \<triangle>\<^sub>T Timelock \<rightarrow>\<^sub>C (STOP\<^sub>C \<triangle>\<^bsub>Suc 0\<^esub> TChaosTT))"
proof -
  have 1: "{t. [X']\<^sub>R # [Tock]\<^sub>E # t \<in> PriTT (f2porder timelock_ordering) (RenamingTT P OtherEvent \<triangle>\<^sub>T Timelock \<rightarrow>\<^sub>C (STOP\<^sub>C \<triangle>\<^bsub>Suc 0\<^esub> TChaosTT))}
    = PriTT (f2porder timelock_ordering) {t. [{e \<in> X'. e \<noteq> Event Timelock}]\<^sub>R # [Tock]\<^sub>E # t \<in> RenamingTT P OtherEvent \<triangle>\<^sub>T Timelock \<rightarrow>\<^sub>C (STOP\<^sub>C \<triangle>\<^bsub>Suc 0\<^esub> TChaosTT)}"
    using PriTT_timelock_ordering_init_tock[where P="RenamingTT P OtherEvent \<triangle>\<^sub>T Timelock \<rightarrow>\<^sub>C (STOP\<^sub>C \<triangle>\<^bsub>Suc 0\<^esub> TChaosTT)", where X=X']
      P_timelock_free P_wf TT1_P TT2_P unprioiritised_remove_timelock_spec_TT1 unprioiritised_remove_timelock_spec_TT2
      unprioiritised_remove_timelock_spec_timelock_free unprioiritised_remove_timelock_spec_wf by fastforce
  have 2: "{t. [{e \<in> X'. e \<noteq> Event Timelock}]\<^sub>R # [Tock]\<^sub>E # t \<in> RenamingTT P OtherEvent \<triangle>\<^sub>T Timelock \<rightarrow>\<^sub>C (STOP\<^sub>C \<triangle>\<^bsub>Suc 0\<^esub> TChaosTT)}
    = {t. [{e \<in> X'. e \<noteq> Event Timelock}]\<^sub>R # [Tock]\<^sub>E # t \<in> RenamingTT P OtherEvent} \<triangle>\<^sub>T Timelock \<rightarrow>\<^sub>C (STOP\<^sub>C \<triangle>\<^bsub>Suc 0\<^esub> TChaosTT)"
    apply (subst TimeSyncInterruptTT_PrefixTT_init_tock[where X="{e \<in> X'. e \<noteq> Event Timelock}", where P="RenamingTT P OtherEvent", where Q="STOP\<^sub>C \<triangle>\<^bsub>Suc 0\<^esub> TChaosTT", where f=Timelock])
    using P_wf RenamingTT_wf by auto
  have 3: "{t. [{e \<in> X'. e \<noteq> Event Timelock}]\<^sub>R # [Tock]\<^sub>E # t \<in> RenamingTT P OtherEvent}
    = {t. [X']\<^sub>R # [Tock]\<^sub>E # t \<in> RenamingTT P OtherEvent}"
    unfolding RenamingTT_def apply auto
    apply (case_tac xa rule:ttWF.cases, auto)
    apply (rule_tac x="[{y. lift_renaming_func OtherEvent y \<in> X' \<and> lift_renaming_func OtherEvent y \<noteq> Event Timelock}]\<^sub>R # [Tock]\<^sub>E # \<sigma>" in bexI, auto)
    apply (case_tac xa, auto)
    apply (case_tac xa rule:ttWF.cases, auto)
    apply (rule_tac x="[lift_renaming_func OtherEvent -` X']\<^sub>R # [Tock]\<^sub>E # \<sigma>" in bexI, auto)
    apply (case_tac xa, auto)
    done
  have 4: "{t. [X']\<^sub>R # [Tock]\<^sub>E # t \<in> RenamingTT P OtherEvent}
    = RenamingTT {t. [(lift_renaming_func OtherEvent) -` X']\<^sub>R # [Tock]\<^sub>E # t \<in> P} OtherEvent"
    by (simp add: RenamingTT_init_tock)
  show ?thesis
    by (simp add: "1" "2" "3" "4")
qed

lemma unhidden_remove_timelock_spec_timelock_free_no_init_Timelock:
  assumes P_wf: "\<forall>x\<in>P. ttWF x" and TT1_P: "TT1 P" and TT2_P: "TT2 P"
  assumes P_timelock_free: "timelock_free P"
  shows "[Event Timelock]\<^sub>E # \<sigma> \<notin> PriTT (f2porder timelock_ordering) (RenamingTT P OtherEvent \<triangle>\<^sub>T Timelock \<rightarrow>\<^sub>C (STOP\<^sub>C \<triangle>\<^bsub>Suc 0\<^esub> TChaosTT))"
proof auto
  assume "[Event Timelock]\<^sub>E # \<sigma> \<in> PriTT (f2porder timelock_ordering) (RenamingTT P OtherEvent \<triangle>\<^sub>T Timelock \<rightarrow>\<^sub>C (STOP\<^sub>C \<triangle>\<^bsub>Suc 0\<^esub> TChaosTT))"
  then have "(\<exists> \<sigma>'. [Event Timelock]\<^sub>E # \<sigma>' \<in> (RenamingTT P OtherEvent \<triangle>\<^sub>T Timelock \<rightarrow>\<^sub>C (STOP\<^sub>C \<triangle>\<^bsub>Suc 0\<^esub> TChaosTT))
    \<and> (\<exists>Z. [[Z]\<^sub>R] \<in> (RenamingTT P OtherEvent \<triangle>\<^sub>T Timelock \<rightarrow>\<^sub>C (STOP\<^sub>C \<triangle>\<^bsub>Suc 0\<^esub> TChaosTT))
        \<and> Event Timelock \<notin> prirefTT (f2porder timelock_ordering) [] (RenamingTT P OtherEvent \<triangle>\<^sub>T Timelock \<rightarrow>\<^sub>C (STOP\<^sub>C \<triangle>\<^bsub>Suc 0\<^esub> TChaosTT)) Z))"
    unfolding PriTT_def using Timelock_not_maximal by (safe, (case_tac s rule:ttWF.cases, auto)+)
  then obtain \<sigma>' Z where 
    Timelock_at_start: "[Event Timelock]\<^sub>E # \<sigma>' \<in> (RenamingTT P OtherEvent \<triangle>\<^sub>T Timelock \<rightarrow>\<^sub>C (STOP\<^sub>C \<triangle>\<^bsub>Suc 0\<^esub> TChaosTT))" and
    refusal_at_start: "[[Z]\<^sub>R] \<in> (RenamingTT P OtherEvent \<triangle>\<^sub>T Timelock \<rightarrow>\<^sub>C (STOP\<^sub>C \<triangle>\<^bsub>Suc 0\<^esub> TChaosTT))" and
    Timelock_not_eliminated: "Event Timelock \<notin> prirefTT (f2porder timelock_ordering) [] (RenamingTT P OtherEvent \<triangle>\<^sub>T Timelock \<rightarrow>\<^sub>C (STOP\<^sub>C \<triangle>\<^bsub>Suc 0\<^esub> TChaosTT)) Z"
    by auto

  have Tock_Timelock_notin_Z: "Tock \<notin> Z \<and> Event Timelock \<notin> Z"
    using refusal_at_start unfolding TimeSyncInterruptTT_def
  proof (safe, simp_all)
    fix X Y Za :: "'a timelock_event ttevent set"
    assume X_in_Renaming_P: "[[X]\<^sub>R] \<in> RenamingTT P OtherEvent"
    assume Y_in_Timelock_Prefix: "[[Y]\<^sub>R] \<in> Timelock \<rightarrow>\<^sub>C (STOP\<^sub>C \<triangle>\<^bsub>Suc 0\<^esub> TChaosTT)"
    assume Za_subset_X_Y: "Za \<subseteq> X \<union> Y"
    assume Tock_in_Za: "Tock \<in> Za"

    have "Tock \<in> X \<or> Tock \<in> Y"
      using Tock_in_Za Za_subset_X_Y by auto
    then show False
    proof(auto)
      assume Tock_in_X: "Tock \<in> X"
      then have "\<exists> X'. Tock \<in> X' \<and> [[X']\<^sub>R] \<in> P"
        using X_in_Renaming_P unfolding RenamingTT_def apply auto
        apply (case_tac x rule:ttWF.cases, simp_all)
        using lift_renaming_func.simps(2) by blast
      then show False
        using P_timelock_free unfolding timelock_free_def by auto
    next
      assume Tock_in_Y: "Tock \<in> Y"
      then show "False"
        using Y_in_Timelock_Prefix unfolding PrefixTT_def by (auto simp add: notin_tocks Cons_eq_append_conv)
    qed
  next
    fix X Y Za :: "'a timelock_event ttevent set"
    assume X_in_Renaming_P: "[[X]\<^sub>R] \<in> RenamingTT P OtherEvent"
    assume Y_in_Timelock_Prefix: "[[Y]\<^sub>R] \<in> Timelock \<rightarrow>\<^sub>C (STOP\<^sub>C \<triangle>\<^bsub>Suc 0\<^esub> TChaosTT)"
    assume Za_subset_X_Y: "Za \<subseteq> X \<union> Y"
    assume X_Y_same_events: "{e \<in> X. e \<noteq> Tock} = {e \<in> Y. e \<noteq> Tock}"
    assume Timelock_in_Za: "Event Timelock \<in> Za"
     
    have "Event Timelock \<in> X \<and> Event Timelock \<in> Y"
      using Timelock_in_Za Za_subset_X_Y X_Y_same_events by auto
    then show False
      using Y_in_Timelock_Prefix unfolding PrefixTT_def by (auto simp add: notin_tocks Cons_eq_append_conv)
  next
    fix p q2 :: "'a timelock_event tttrace"
    assume p_not_refusal: "\<forall>p' Y. p \<noteq> p' @ [[Y]\<^sub>R]"
    assume q2_not_refusal: "\<forall>q' Y. q2 \<noteq> [Y]\<^sub>R # q'"
    assume Z_eq_p_q2: "[[Z]\<^sub>R] = p @ q2"

    have "p = [[Z]\<^sub>R] \<or> q2 = [[Z]\<^sub>R]"
      by (metis Z_eq_p_q2 append_is_Nil_conv butlast.simps(2) butlast_append self_append_conv self_append_conv2)
    then show False
      using p_not_refusal q2_not_refusal by auto
  next
    fix p q2 :: "'a timelock_event tttrace"
    assume p_not_refusal: "\<forall>p' Y. p \<noteq> p' @ [[Y]\<^sub>R]"
    assume q2_not_refusal: "\<forall>q' Y. q2 \<noteq> [Y]\<^sub>R # q'"
    assume Z_eq_p_q2: "[[Z]\<^sub>R] = p @ q2"

    have "p = [[Z]\<^sub>R] \<or> q2 = [[Z]\<^sub>R]"
      by (metis Z_eq_p_q2 append_is_Nil_conv butlast.simps(2) butlast_append self_append_conv self_append_conv2)
    then show False
      using p_not_refusal q2_not_refusal by auto
  qed        

  have "[[Z]\<^sub>R, [Tock]\<^sub>E] \<notin> (RenamingTT P OtherEvent \<triangle>\<^sub>T Timelock \<rightarrow>\<^sub>C (STOP\<^sub>C \<triangle>\<^bsub>Suc 0\<^esub> TChaosTT))"
    using Timelock_not_eliminated unfolding prirefTT_def my_lt_def my_le_def by (auto simp add: timelock_ordering_porder_cancel)
  then have "[[Z]\<^sub>R, [Tock]\<^sub>E] \<notin> RenamingTT P OtherEvent"
    unfolding TimeSyncInterruptTT_def PrefixTT_def apply auto
    apply (erule_tac x="[[Z]\<^sub>R, [Tock]\<^sub>E]" in allE, auto, erule_tac x="[]" in allE, auto)
    apply (erule_tac x="[[Z]\<^sub>R, [Tock]\<^sub>E]" in ballE, auto)
    by (metis (mono_tags, lifting) Tock_Timelock_notin_Z mem_Collect_eq subsetI tocks.empty_in_tocks tocks.tock_insert_in_tocks)
  then have "\<exists>Z'. [[Z']\<^sub>R, [Tock]\<^sub>E] \<notin> P \<and> Z' = lift_renaming_func OtherEvent -` Z"
    unfolding RenamingTT_def by auto
  then obtain Z' where Z'_Tock_notin_P: "[[Z']\<^sub>R, [Tock]\<^sub>E] \<notin> P" and Z'_def: "Z' = lift_renaming_func OtherEvent -` Z"
    by auto

  have "[[Z]\<^sub>R] \<in> RenamingTT P OtherEvent"
    using refusal_at_start unfolding TimeSyncInterruptTT_def
  proof (safe, simp_all)
    fix X Y Za and p :: "'b timelock_event tttrace"
    assume X_in_Renaming_P:"[[X]\<^sub>R] \<in> RenamingTT P OtherEvent"
    assume Za_subset_X_Y: "Za \<subseteq> X \<union> Y"
    assume X_Y_same_events: "{e \<in> X. e \<noteq> Tock} = {e \<in> Y. e \<noteq> Tock}"
    assume Z_eq_Za: "[] = p \<and> Z = Za"

    have "Za \<subseteq> X"
    proof auto
      fix x
      assume "x \<in> Za"
      then have "(x \<in> X \<or> x \<in> Y) \<and> x \<noteq> Tock"
        using Za_subset_X_Y Tock_Timelock_notin_Z Z_eq_Za by auto
      then show "x \<in> X"
        using X_Y_same_events by auto
    qed
    also have "TT1 (RenamingTT P OtherEvent)"
      using TT1_Renaming TT1_P by blast
    then show "[[Za]\<^sub>R] \<in> RenamingTT P OtherEvent"
      using calculation X_in_Renaming_P unfolding TT1_def apply auto by (erule_tac x="[[Za]\<^sub>R]" in allE, auto)
  next
    fix p q2 :: "'a timelock_event tttrace"
    assume p_not_refusal: "\<forall>p' Y. p \<noteq> p' @ [[Y]\<^sub>R]"
    assume q_not_refusal: "\<forall>q' Y. q2 \<noteq> [Y]\<^sub>R # q'"
    assume Z_eq_p_q: "[[Z]\<^sub>R] = p @ q2"

    have "p = [[Z]\<^sub>R] \<or> q2 = [[Z]\<^sub>R]"
      by (metis Z_eq_p_q append_Nil append_is_Nil_conv butlast_append butlast_snoc)
    then show "p @ q2 \<in> RenamingTT P OtherEvent"
      using p_not_refusal q_not_refusal by auto
  qed
  then have Z'_in_P: "[[Z']\<^sub>R] \<in> P"
    unfolding RenamingTT_def by (auto, case_tac x rule:ttWF.cases, auto simp add: Z'_def)
  then have "[[Z' \<union> {Tock}]\<^sub>R] \<in> P"
    using TT2_P Z'_Tock_notin_P unfolding TT2_def 
    apply (erule_tac x="[]" in allE, erule_tac x="[]" in allE)
    by (erule_tac x="Z'" in allE, erule_tac x="{Tock}" in allE, auto)
  then show False
    using P_timelock_free timelock_free_def by fastforce
qed

lemma remove_timelock_spec_init_event:
  assumes P_wf: "\<forall>x\<in>P. ttWF x"
  shows "{t. [Event (OtherEvent e')]\<^sub>E # t \<in> remove_timelock_spec P}
    = remove_timelock_spec {t. [Event e']\<^sub>E # t \<in> P}"
  unfolding remove_timelock_spec_def HidingTT_def
proof auto
  fix p x
  assume p_in_PriTT: "p \<in> PriTT (f2porder timelock_ordering) (RenamingTT P OtherEvent \<triangle>\<^sub>T Timelock \<rightarrow>\<^sub>C (STOP\<^sub>C \<triangle>\<^bsub>Suc 0\<^esub> TChaosTT))"
  assume e'_x_in_hide_trace_p: "[Event (OtherEvent e')]\<^sub>E # x \<in> hide_trace {Event Timelock} p"

  have "\<exists>p'. p = [Event (OtherEvent e')]\<^sub>E # p'"
    using p_in_PriTT e'_x_in_hide_trace_p
  proof (cases p rule:ttWF.cases, auto, case_tac \<sigma> rule:ttWF.cases, auto)
    fix \<sigma>'
    assume "[Event Timelock]\<^sub>E # [Event Timelock]\<^sub>E # \<sigma>'
        \<in> PriTT (f2porder timelock_ordering) (RenamingTT P OtherEvent \<triangle>\<^sub>T Timelock \<rightarrow>\<^sub>C (STOP\<^sub>C \<triangle>\<^bsub>Suc 0\<^esub> TChaosTT))"
    then have "\<exists>s.  [Event Timelock]\<^sub>E # [Event Timelock]\<^sub>E # s \<in> RenamingTT P OtherEvent \<triangle>\<^sub>T Timelock \<rightarrow>\<^sub>C (STOP\<^sub>C \<triangle>\<^bsub>Suc 0\<^esub> TChaosTT)"
      unfolding PriTT_def apply (auto, case_tac s rule:ttWF.cases, auto simp add: Timelock_not_maximal)
      by (case_tac \<sigma> rule:ttWF.cases, auto simp add: Timelock_not_maximal)
    then show "False"
      unfolding TimeSyncInterruptTT_def apply safe apply simp_all
    proof -
      fix s p :: "'a timelock_event tttrace"
      assume "[Event Timelock]\<^sub>E # [Event Timelock]\<^sub>E # s = p @ [[Tick]\<^sub>E]"
      then show "p @ [[Tick]\<^sub>E] \<in> RenamingTT P OtherEvent \<Longrightarrow> False"
        unfolding RenamingTT_def by (cases p rule:ttWF.cases, auto, case_tac x rule:ttWF.cases, auto)
    next
      fix s p :: "'a timelock_event tttrace" and X Y Z
      assume "[Event Timelock]\<^sub>E # [Event Timelock]\<^sub>E # s = p @ [[Z]\<^sub>R]"
      then show "p @ [[X]\<^sub>R] \<in> RenamingTT P OtherEvent \<Longrightarrow> False"
        unfolding RenamingTT_def by (cases p rule:ttWF.cases, auto, case_tac x rule:ttWF.cases, auto)
    next
      fix s p q2 :: "'a timelock_event tttrace"
      assume p_in_P_renaming: "p \<in> RenamingTT P OtherEvent"
      assume q2_in_Timelock_prefix: "filter_tocks p @ q2 \<in> Timelock \<rightarrow>\<^sub>C (STOP\<^sub>C \<triangle>\<^bsub>Suc 0\<^esub> TChaosTT)"
      assume "[Event Timelock]\<^sub>E # [Event Timelock]\<^sub>E # s = p @ q2"
      then have "(\<exists>p'. p = [Event Timelock]\<^sub>E # p') \<or> (p = [] \<and> q2 = [Event Timelock]\<^sub>E # [Event Timelock]\<^sub>E # s)"
        by (induct p rule:ttWF.induct, auto)
      then have "p = [] \<and> q2 = [Event Timelock]\<^sub>E # [Event Timelock]\<^sub>E # s"
        using p_in_P_renaming unfolding RenamingTT_def by (auto, (case_tac x rule:ttWF.cases, auto)+)
      then show "False"
        using q2_in_Timelock_prefix unfolding PrefixTT_def apply (auto simp add: notin_tocks)
         apply (metis (no_types, lifting) butlast.simps(2) butlast_snoc start_event_notin_tocks)
        apply (case_tac sa rule:tocks.cases, auto)
        unfolding StopTT_def StrictTimedInterruptTT_def apply (auto simp add: notin_tocks)
        apply (metis butlast.simps(2) butlast_snoc last.simps last_snoc start_event_notin_tocks ttobs.simps(4))
        by (metis (no_types, lifting) filter.simps(1) length_0_conv n_not_Suc_n tocks.simps tt_prefix.simps(2) tt_prefix_concat ttobs.simps(4))
    qed
  next  
    fix \<sigma>'
    assume "[Event Timelock]\<^sub>E # [Event (OtherEvent e')]\<^sub>E # \<sigma>'
        \<in> PriTT (f2porder timelock_ordering) (RenamingTT P OtherEvent \<triangle>\<^sub>T Timelock \<rightarrow>\<^sub>C (STOP\<^sub>C \<triangle>\<^bsub>Suc 0\<^esub> TChaosTT))"
    then have "\<exists>s.  [Event Timelock]\<^sub>E # [Event (OtherEvent e')]\<^sub>E # s \<in> RenamingTT P OtherEvent \<triangle>\<^sub>T Timelock \<rightarrow>\<^sub>C (STOP\<^sub>C \<triangle>\<^bsub>Suc 0\<^esub> TChaosTT)"
      unfolding PriTT_def apply (auto, case_tac s rule:ttWF.cases, auto simp add: Timelock_not_maximal)
      by (case_tac \<sigma> rule:ttWF.cases, auto simp add: Timelock_not_maximal)
    then show "False"
      unfolding TimeSyncInterruptTT_def apply safe apply simp_all
    proof -
      fix s p :: "'a timelock_event tttrace"
      assume "[Event Timelock]\<^sub>E # [Event (OtherEvent e')]\<^sub>E # s = p @ [[Tick]\<^sub>E]"
      then show "p @ [[Tick]\<^sub>E] \<in> RenamingTT P OtherEvent \<Longrightarrow> False"
        unfolding RenamingTT_def by (cases p rule:ttWF.cases, auto, case_tac x rule:ttWF.cases, auto)
    next
      fix s p :: "'a timelock_event tttrace" and X Y Z
      assume "[Event Timelock]\<^sub>E # [Event (OtherEvent e')]\<^sub>E # s = p @ [[Z]\<^sub>R]"
      then show "p @ [[X]\<^sub>R] \<in> RenamingTT P OtherEvent \<Longrightarrow> False"
        unfolding RenamingTT_def by (cases p rule:ttWF.cases, auto, case_tac x rule:ttWF.cases, auto)
    next
      fix s p q2 :: "'a timelock_event tttrace"
      assume p_in_P_renaming: "p \<in> RenamingTT P OtherEvent"
      assume q2_in_Timelock_prefix: "filter_tocks p @ q2 \<in> Timelock \<rightarrow>\<^sub>C (STOP\<^sub>C \<triangle>\<^bsub>Suc 0\<^esub> TChaosTT)"
      assume "[Event Timelock]\<^sub>E # [Event (OtherEvent e')]\<^sub>E # s = p @ q2"
      then have "(\<exists>p'. p = [Event Timelock]\<^sub>E # p') \<or> (p = [] \<and> q2 = [Event Timelock]\<^sub>E # [Event (OtherEvent e')]\<^sub>E # s)"
        by (induct p rule:ttWF.induct, auto)
      then have "p = [] \<and> q2 = [Event Timelock]\<^sub>E # [Event (OtherEvent e')]\<^sub>E # s"
        using p_in_P_renaming unfolding RenamingTT_def by (auto, (case_tac x rule:ttWF.cases, auto)+)
      then show "False"
        using q2_in_Timelock_prefix unfolding PrefixTT_def apply (auto simp add: notin_tocks)
         apply (metis (no_types, lifting) butlast.simps(2) butlast_snoc start_event_notin_tocks)
        apply (case_tac sa rule:tocks.cases, auto)
        unfolding StopTT_def StrictTimedInterruptTT_def apply (auto simp add: notin_tocks)
        apply (metis butlast.simps(2) butlast_snoc last.simps last_snoc start_event_notin_tocks ttobs.simps(4))
        by (metis (no_types, lifting) filter.simps(1) length_0_conv n_not_Suc_n tocks.simps tt_prefix.simps(2) tt_prefix_concat ttobs.simps(4))
    qed
  qed
  then show "\<exists>xa. (\<exists>p. xa = hide_trace {Event Timelock} p \<and>
                     p \<in> PriTT (f2porder timelock_ordering)
                           (RenamingTT {t. [Event e']\<^sub>E # t \<in> P} OtherEvent \<triangle>\<^sub>T Timelock \<rightarrow>\<^sub>C (STOP\<^sub>C \<triangle>\<^bsub>Suc 0\<^esub> TChaosTT))) \<and>
                x \<in> xa"
    apply (auto, rule_tac x="hide_trace {Event Timelock} p'" in exI, auto, rule_tac x="p'" in exI, auto)
    using P_wf p_in_PriTT unhidden_remove_timelock_spec_init_event apply fastforce
    using e'_x_in_hide_trace_p by auto
next
  fix x p
  assume p_in_PriTT: "p \<in> PriTT (f2porder timelock_ordering)
      (RenamingTT {t. [Event e']\<^sub>E # t \<in> P} OtherEvent \<triangle>\<^sub>T Timelock \<rightarrow>\<^sub>C (STOP\<^sub>C \<triangle>\<^bsub>Suc 0\<^esub> TChaosTT))"
  assume x_in_hide_trace_p: "x \<in> hide_trace {Event Timelock} p"

  show "\<exists>xa. (\<exists>p. xa = hide_trace {Event Timelock} p \<and>
                     p \<in> PriTT (f2porder timelock_ordering) (RenamingTT P OtherEvent \<triangle>\<^sub>T Timelock \<rightarrow>\<^sub>C (STOP\<^sub>C \<triangle>\<^bsub>Suc 0\<^esub> TChaosTT))) \<and>
                [Event (OtherEvent e')]\<^sub>E # x \<in> xa"
    apply (rule_tac x="hide_trace {Event Timelock} ([Event (OtherEvent e')]\<^sub>E # p)" in exI, auto)
    apply (rule_tac x="[Event (OtherEvent e')]\<^sub>E # p" in exI, auto simp add: x_in_hide_trace_p)
    using P_wf p_in_PriTT unhidden_remove_timelock_spec_init_event by fastforce
qed

lemma remove_timelock_spec_init_tock:
  assumes P_wf: "\<forall>x\<in>P. ttWF x" and TT1_P: "TT1 P" and TT2_P: "TT2 P"
  assumes P_timelock_free: "timelock_free P"
  shows "{t. [X]\<^sub>R # [Tock]\<^sub>E # t \<in> remove_timelock_spec P}
    = remove_timelock_spec {t. [lift_renaming_func OtherEvent -` X]\<^sub>R # [Tock]\<^sub>E # t \<in> P}"
  (is "?lhs = ?rhs")
proof -
  have "?lhs = {t. [X]\<^sub>R # [Tock]\<^sub>E # t \<in> PriTT (f2porder timelock_ordering) (RenamingTT P OtherEvent \<triangle>\<^sub>T Timelock \<rightarrow>\<^sub>C (STOP\<^sub>C \<triangle>\<^bsub>1\<^esub> TChaosTT))} \<setminus>\<^sub>C {Event Timelock}"
    unfolding remove_timelock_spec_def HidingTT_def
  proof auto
    fix x p
    show "[X]\<^sub>R # [Tock]\<^sub>E # x \<in> hide_trace {Event Timelock} p \<Longrightarrow>
           p \<in> PriTT (f2porder timelock_ordering) (RenamingTT P OtherEvent \<triangle>\<^sub>T Timelock \<rightarrow>\<^sub>C (STOP\<^sub>C \<triangle>\<^bsub>Suc 0\<^esub> TChaosTT)) \<Longrightarrow>
           \<exists>xa. (\<exists>p. xa = hide_trace {Event Timelock} p \<and>
                     [X]\<^sub>R # [Tock]\<^sub>E # p
                     \<in> PriTT (f2porder timelock_ordering) (RenamingTT P OtherEvent \<triangle>\<^sub>T Timelock \<rightarrow>\<^sub>C (STOP\<^sub>C \<triangle>\<^bsub>Suc 0\<^esub> TChaosTT))) \<and>
                x \<in> xa"
      apply (case_tac p rule:ttWF.cases, auto)
      apply (simp add: P_timelock_free P_wf TT1_P TT2_P unhidden_remove_timelock_spec_timelock_free_no_init_Timelock)
      apply (rule_tac x="hide_trace {Event Timelock} \<sigma>" in exI, auto, rule_tac x=\<sigma> in exI, auto)
      by (meson P_wf TT1_P TT1_PriTT TT1_def tt_prefix_subset.simps(2) tt_prefix_subset_refl unprioiritised_remove_timelock_spec_TT1 unprioiritised_remove_timelock_spec_wf)
  next
    fix x p
    assume "[X]\<^sub>R # [Tock]\<^sub>E # p \<in> PriTT (f2porder timelock_ordering) (RenamingTT P OtherEvent \<triangle>\<^sub>T Timelock \<rightarrow>\<^sub>C (STOP\<^sub>C \<triangle>\<^bsub>Suc 0\<^esub> TChaosTT))"
    then have "[X \<union> {Event Timelock}]\<^sub>R # [Tock]\<^sub>E # p \<in> PriTT (f2porder timelock_ordering) (RenamingTT P OtherEvent \<triangle>\<^sub>T Timelock \<rightarrow>\<^sub>C (STOP\<^sub>C \<triangle>\<^bsub>Suc 0\<^esub> TChaosTT))"
      unfolding PriTT_def apply auto
      apply (case_tac s rule:ttWF.cases, auto)
    proof (rule_tac x="[Xa]\<^sub>R # [Tock]\<^sub>E # \<sigma>" in exI, auto)
      fix Xa \<sigma>
      assume "[Xa]\<^sub>R # [Tock]\<^sub>E # \<sigma> \<in> RenamingTT P OtherEvent \<triangle>\<^sub>T Timelock \<rightarrow>\<^sub>C (STOP\<^sub>C \<triangle>\<^bsub>Suc 0\<^esub> TChaosTT)"
      then have "[[Xa]\<^sub>R, [Tock]\<^sub>E] \<in> RenamingTT P OtherEvent \<triangle>\<^sub>T Timelock \<rightarrow>\<^sub>C (STOP\<^sub>C \<triangle>\<^bsub>Suc 0\<^esub> TChaosTT)"
        by (meson P_wf TT1_P TT1_def subsetI tt_prefix_subset.simps(1) tt_prefix_subset.simps(2) tt_prefix_subset.simps(3) unprioiritised_remove_timelock_spec_TT1)
      then show "Event Timelock \<in> prirefTT (f2porder timelock_ordering) [] (RenamingTT P OtherEvent \<triangle>\<^sub>T Timelock \<rightarrow>\<^sub>C (STOP\<^sub>C \<triangle>\<^bsub>Suc 0\<^esub> TChaosTT)) Xa"
        unfolding prirefTT_def my_le_def my_lt_def by (auto simp add: timelock_ordering_porder_cancel)
    qed
    then show "x \<in> hide_trace {Event Timelock} p \<Longrightarrow>
           \<exists>xa. (\<exists>p. xa = hide_trace {Event Timelock} p \<and>
                     p \<in> PriTT (f2porder timelock_ordering) (RenamingTT P OtherEvent \<triangle>\<^sub>T Timelock \<rightarrow>\<^sub>C (STOP\<^sub>C \<triangle>\<^bsub>Suc 0\<^esub> TChaosTT))) \<and>
                [X]\<^sub>R # [Tock]\<^sub>E # x \<in> xa"
      apply (rule_tac x="hide_trace {Event Timelock} ([X \<union> {Event Timelock}]\<^sub>R # [Tock]\<^sub>E # p)" in exI, auto)
      by (rule_tac x="[X \<union> {Event Timelock}]\<^sub>R # [Tock]\<^sub>E # p" in exI, auto)
  qed
  also have "... = ?rhs"
    by (simp add: P_timelock_free P_wf TT1_P TT2_P remove_timelock_spec_def unhidden_remove_timelock_spec_init_tock)
  then show ?thesis
    using calculation by auto
qed

lemma timelock_ordering_PriTT_init_tock_any_refusal_subset:
  assumes P_wf: "\<forall>x\<in>P. ttWF x"
  shows "PriTT (f2porder timelock_ordering) {t. [X]\<^sub>R # [Tock]\<^sub>E # t \<in> P}
      \<subseteq> {t. \<exists>X. [X]\<^sub>R # [Tock]\<^sub>E # t \<in> PriTT (f2porder timelock_ordering) P}"
  unfolding PriTT_def apply (auto, rule_tac x="{}" in exI, rule_tac x="[X]\<^sub>R # [Tock]\<^sub>E # s" in exI, auto)
  unfolding prirefTT_def using assms ttWF.simps(5) apply auto
  apply (meson Tock_maximal some_higher_not_maximal)
  using assms ttWF.simps(5) priTT_prefix_eq[where \<rho>="[]", where \<sigma>="[[X]\<^sub>R, [Tock]\<^sub>E]"] by auto

lemma remove_timelock_spec_init_tock_any_refusal_subset:
  assumes P_wf: "\<forall>x\<in>P. ttWF x" and TT1_P: "TT1 P"
  shows "remove_timelock_spec {t. [X]\<^sub>R # [Tock]\<^sub>E # t \<in> P}
      \<subseteq> {t. \<exists>X. [X]\<^sub>R # [Tock]\<^sub>E # t \<in> remove_timelock_spec P}"
  (is "?lhs \<subseteq> ?rhs")
proof -
  have "?lhs \<subseteq> PriTT (f2porder timelock_ordering) ({t. [lift_renaming_func OtherEvent ` X]\<^sub>R # [Tock]\<^sub>E # t \<in> RenamingTT P OtherEvent} \<triangle>\<^sub>T Timelock \<rightarrow>\<^sub>C (STOP\<^sub>C \<triangle>\<^bsub>1\<^esub> TChaosTT)) \<setminus>\<^sub>C {Event Timelock}"
    unfolding remove_timelock_spec_def by (auto simp add: RenamingTT_init_tock2 inj_def)
  also have "... \<subseteq> PriTT (f2porder timelock_ordering) {t. [lift_renaming_func OtherEvent ` X]\<^sub>R # [Tock]\<^sub>E # t \<in> RenamingTT P OtherEvent \<triangle>\<^sub>T Timelock \<rightarrow>\<^sub>C (STOP\<^sub>C \<triangle>\<^bsub>1\<^esub> TChaosTT)} \<setminus>\<^sub>C {Event Timelock}"    
    using RenamingTT_wf assms by (subst TimeSyncInterruptTT_PrefixTT_init_tock, auto, case_tac x, auto)
  also have "... \<subseteq> {t. \<exists>X. [X]\<^sub>R # [Tock]\<^sub>E # t \<in> PriTT (f2porder timelock_ordering) (RenamingTT P OtherEvent \<triangle>\<^sub>T Timelock \<rightarrow>\<^sub>C (STOP\<^sub>C \<triangle>\<^bsub>1\<^esub> TChaosTT)) \<setminus>\<^sub>C {Event Timelock}}"
    unfolding HidingTT_def PriTT_def
  proof auto
    fix x p s
    assume p_priTT_s: "p priTT\<^sub>[\<^sub>f2porder
                  timelock_ordering\<^sub>,\<^sub>[]\<^sub>,\<^sub>{t. [lift_renaming_func OtherEvent ` X]\<^sub>R # [Tock]\<^sub>E # t
                                               \<in> RenamingTT P OtherEvent \<triangle>\<^sub>T Timelock \<rightarrow>\<^sub>C (STOP\<^sub>C \<triangle>\<^bsub>Suc 0\<^esub> TChaosTT)}\<^sub>] s"
    assume x_in_hide_trace_p: "x \<in> hide_trace {Event Timelock} p"
    assume tock_S_in_TimeSyncInterrupt:
      "[lift_renaming_func OtherEvent ` X]\<^sub>R # [Tock]\<^sub>E # s
        \<in> RenamingTT P OtherEvent \<triangle>\<^sub>T Timelock \<rightarrow>\<^sub>C (STOP\<^sub>C \<triangle>\<^bsub>Suc 0\<^esub> TChaosTT)"

    have ttWF_s: "ttWF s"
      by (meson assms tock_S_in_TimeSyncInterrupt ttWF.simps(5) unprioiritised_remove_timelock_spec_wf)
    have ttWF_p: "ttWF p"
      using p_priTT_s ttWF_priTT_imp_ttWF2 ttWF_s by blast

    have p_priTT_s: "p priTT\<^sub>[\<^sub>f2porder timelock_ordering\<^sub>,\<^sub>[[lift_renaming_func OtherEvent ` X]\<^sub>R, [Tock]\<^sub>E]\<^sub>,\<^sub>RenamingTT P OtherEvent \<triangle>\<^sub>T Timelock \<rightarrow>\<^sub>C (STOP\<^sub>C \<triangle>\<^bsub>Suc 0\<^esub> TChaosTT)\<^sub>] s"
      using ttWF_s priTT_prefix_eq[where \<sigma>="[[lift_renaming_func OtherEvent ` X]\<^sub>R, [Tock]\<^sub>E]"] p_priTT_s by auto

    have rename_X_in_TimeSyncInterruptTT: "[[lift_renaming_func OtherEvent ` X]\<^sub>R] \<in> RenamingTT P OtherEvent \<triangle>\<^sub>T Timelock \<rightarrow>\<^sub>C (STOP\<^sub>C \<triangle>\<^bsub>Suc 0\<^esub> TChaosTT)"
      by (meson P_wf TT1_P TT1_def subset_iff tock_S_in_TimeSyncInterrupt tt_prefix_subset.simps(1) tt_prefix_subset.simps(2) unprioiritised_remove_timelock_spec_TT1)
      
    show "\<exists>X xa. (\<exists>p. xa = hide_trace {Event Timelock} p \<and>
      (\<exists>s. p priTT\<^sub>[\<^sub>f2porder timelock_ordering\<^sub>,\<^sub>[]\<^sub>,\<^sub>RenamingTT P OtherEvent \<triangle>\<^sub>T Timelock \<rightarrow>\<^sub>C (STOP\<^sub>C \<triangle>\<^bsub>Suc 0\<^esub> TChaosTT)\<^sub>] s \<and>
        s \<in> RenamingTT P OtherEvent \<triangle>\<^sub>T Timelock \<rightarrow>\<^sub>C (STOP\<^sub>C \<triangle>\<^bsub>Suc 0\<^esub> TChaosTT))) \<and> [X]\<^sub>R # [Tock]\<^sub>E # x \<in> xa"
    proof (cases "Event Timelock \<in> prirefTT (f2porder timelock_ordering) [] (RenamingTT P OtherEvent \<triangle>\<^sub>T Timelock \<rightarrow>\<^sub>C (STOP\<^sub>C \<triangle>\<^bsub>Suc 0\<^esub> TChaosTT)) (lift_renaming_func OtherEvent ` X)") 
      assume "Event Timelock \<in> prirefTT (f2porder timelock_ordering) [] (RenamingTT P OtherEvent \<triangle>\<^sub>T Timelock \<rightarrow>\<^sub>C (STOP\<^sub>C \<triangle>\<^bsub>Suc 0\<^esub> TChaosTT)) (lift_renaming_func OtherEvent ` X)"
      then have "([{Event Timelock}]\<^sub>R # [Tock]\<^sub>E # p)
        priTT\<^sub>[\<^sub>f2porder timelock_ordering\<^sub>,\<^sub>[]\<^sub>,\<^sub>RenamingTT P OtherEvent \<triangle>\<^sub>T Timelock \<rightarrow>\<^sub>C (STOP\<^sub>C \<triangle>\<^bsub>Suc 0\<^esub> TChaosTT)\<^sub>]
          ([lift_renaming_func OtherEvent ` X]\<^sub>R # [Tock]\<^sub>E # s)"
        using p_priTT_s apply auto
        by (meson Tock_maximal assms maximal_notin_prirefTT tock_S_in_TimeSyncInterrupt
            ttWF.simps(5) unprioiritised_remove_timelock_spec_wf)
      then show ?thesis
        apply (rule_tac x="{Event Timelock}" in exI, auto)
        apply (rule_tac x="hide_trace {Event Timelock} ([{Event Timelock}]\<^sub>R # [Tock]\<^sub>E # p)" in exI, auto)
        apply (rule_tac x="[{Event Timelock}]\<^sub>R # [Tock]\<^sub>E # p" in exI, auto)
        apply (rule_tac x="[lift_renaming_func OtherEvent ` X]\<^sub>R # [Tock]\<^sub>E # s" in exI)
        by (auto simp add: tock_S_in_TimeSyncInterrupt  x_in_hide_trace_p)
    next
      assume inner_assm: "Event Timelock
        \<notin> prirefTT (f2porder timelock_ordering) [] (RenamingTT P OtherEvent \<triangle>\<^sub>T Timelock \<rightarrow>\<^sub>C (STOP\<^sub>C \<triangle>\<^bsub>Suc 0\<^esub> TChaosTT))
          (lift_renaming_func OtherEvent ` X)"
      then have "[[lift_renaming_func OtherEvent ` X]\<^sub>R, [Tock]\<^sub>E] \<notin> RenamingTT P OtherEvent \<triangle>\<^sub>T Timelock \<rightarrow>\<^sub>C (STOP\<^sub>C \<triangle>\<^bsub>Suc 0\<^esub> TChaosTT)"
        unfolding prirefTT_def my_le_def my_lt_def by (auto simp add: timelock_ordering_porder_cancel)
      also have "TT1 (RenamingTT P OtherEvent \<triangle>\<^sub>T Timelock \<rightarrow>\<^sub>C (STOP\<^sub>C \<triangle>\<^bsub>Suc 0\<^esub> TChaosTT))"
        using P_wf TT1_P unprioiritised_remove_timelock_spec_TT1 by blast
      then have "[[lift_renaming_func OtherEvent ` X]\<^sub>R, [Tock]\<^sub>E] \<in> RenamingTT P OtherEvent \<triangle>\<^sub>T Timelock \<rightarrow>\<^sub>C (STOP\<^sub>C \<triangle>\<^bsub>Suc 0\<^esub> TChaosTT)"
        unfolding TT1_def apply auto
        by (meson subsetI tock_S_in_TimeSyncInterrupt tt_prefix_subset.simps(1) tt_prefix_subset.simps(2) tt_prefix_subset.simps(3))
      then show "\<exists>X xa. (\<exists>p. xa = hide_trace {Event Timelock} p \<and>
            (\<exists>s. p priTT\<^sub>[\<^sub>f2porder timelock_ordering\<^sub>,\<^sub>[]\<^sub>,\<^sub>RenamingTT P OtherEvent \<triangle>\<^sub>T Timelock \<rightarrow>\<^sub>C (STOP\<^sub>C \<triangle>\<^bsub>Suc 0\<^esub> TChaosTT)\<^sub>] s \<and>
                 s \<in> RenamingTT P OtherEvent \<triangle>\<^sub>T Timelock \<rightarrow>\<^sub>C (STOP\<^sub>C \<triangle>\<^bsub>Suc 0\<^esub> TChaosTT))) \<and> [X]\<^sub>R # [Tock]\<^sub>E # x \<in> xa"
        using calculation by auto
    qed
  qed
  also have "... \<subseteq> ?rhs"
    unfolding remove_timelock_spec_def by auto
  then show ?thesis
    using calculation by auto
qed

lemma remove_timelock_spec_wf: "\<forall>x\<in>P. ttWF x \<Longrightarrow> \<forall>x\<in>remove_timelock_spec P. ttWF x"
  unfolding remove_timelock_spec_def apply auto
  by (smt HidingTT_wf PriTT_wf unprioiritised_remove_timelock_spec_wf)

lemma remove_timelock_spec_timelock_free:
  assumes P_wf: "\<forall>x\<in>P. ttWF x" and TT1_P: "TT1 P"
  shows "timelock_free (remove_timelock_spec P)"
  unfolding timelock_free_def
proof (auto, rule ccontr)
  fix x :: "'a timelock_event tttrace"
  assume x_in_remove_timelock_spec_P: "x \<in> remove_timelock_spec P"

  have ttWF_x: "ttWF x"
    using P_wf remove_timelock_spec_wf x_in_remove_timelock_spec_P by blast

  assume "\<not> timelock_free_trace x"
  then have "\<exists>x' X. x = x' @ [[X]\<^sub>R] \<and> Tock \<in> X"
    using ttWF_x apply - by (induct x rule:ttWF.induct, auto)
  then obtain x' X where x_end_refusal: "x = x' @ [[X]\<^sub>R] \<and> Tock \<in> X"
    by auto
  then obtain x'2 X2 where 2: "x'2 @ [[X2]\<^sub>R] \<in> PriTT (f2porder timelock_ordering) (RenamingTT P OtherEvent \<triangle>\<^sub>T Timelock \<rightarrow>\<^sub>C (STOP\<^sub>C \<triangle>\<^bsub>1\<^esub> TChaosTT))
    \<and> Tock \<in> X2 \<and> Event Timelock \<in> X2"
    using x_in_remove_timelock_spec_P hide_trace_end_refusal unfolding remove_timelock_spec_def HidingTT_def by blast
  then obtain x'3 X3 where 3: "x'3 @ [[X3]\<^sub>R] \<in> (RenamingTT P OtherEvent \<triangle>\<^sub>T Timelock \<rightarrow>\<^sub>C (STOP\<^sub>C \<triangle>\<^bsub>1\<^esub> TChaosTT))
    \<and> Tock \<in> X3 \<and> X2 \<subseteq> prirefTT (f2porder timelock_ordering) x'3 (RenamingTT P OtherEvent \<triangle>\<^sub>T Timelock \<rightarrow>\<^sub>C (STOP\<^sub>C \<triangle>\<^bsub>1\<^esub> TChaosTT)) X3"
    unfolding PriTT_def using priTT_end_refusal apply auto
    by (smt Tock_maximal append_Nil maximal_notin_prirefTT priTT_end_refusal subsetCE)
  then have "(\<exists>x'. x' @ [[X3]\<^sub>R] \<in> (STOP\<^sub>C \<triangle>\<^bsub>1\<^esub> TChaosTT)) \<or> (\<exists>Xa. x'3 @ [[Xa]\<^sub>R] \<in> RenamingTT P OtherEvent \<and> Event Timelock \<notin> Xa \<and> X3 \<subseteq> Xa)"
    by (smt StopTT_wf StrictTimedInterruptTT_wf TChaos_wf TimeSyncInterruptTT_PrefixTT_end_refusal)
  then show False
  proof auto
    fix x'
    assume "x' @ [[X3]\<^sub>R] \<in> STOP\<^sub>C \<triangle>\<^bsub>Suc 0\<^esub> TChaosTT"
    then have "x' @ [[X3]\<^sub>R] \<in> STOP\<^sub>C \<or> (\<exists>x''. x'' @ [[X3]\<^sub>R] \<in> TChaosTT)"
      unfolding StrictTimedInterruptTT_def apply - apply (induct x' rule:ttWF.induct, auto)
      apply (metis Nil_is_append_conv append_Nil butlast_append butlast_snoc)
      apply (metis append_Nil2 append_butlast_last_id last.simps last_appendR)
      apply (metis append_Nil2 append_butlast_last_id last.simps last_appendR)
      apply (metis append_Nil2 last.simps last_appendR snoc_eq_iff_butlast)
      apply (metis append_Nil2 last.simps last_appendR list.distinct(1) snoc_eq_iff_butlast)
      apply (metis append_Nil2 last.simps last_appendR snoc_eq_iff_butlast)
      by (metis append_Nil2 last.simps last_appendR list.distinct(1) snoc_eq_iff_butlast)+
    then  show "False"
      unfolding StopTT_def TChaosTT_def
    proof (auto simp add: notin_tocks)
      show "Tock \<notin> X3 \<Longrightarrow> False"
        using 3 by blast
    next
      fix x''
      assume "timelock_free_trace (x'' @ [[X3]\<^sub>R])"
      then have "Tock \<notin> X3"
        by (induct x'' rule:timelock_free_trace.induct, auto)
      then show False
        using 3 by blast
    qed
  next
    fix Xa
    assume x'3_Xa_in_P_renaming: "x'3 @ [[Xa]\<^sub>R] \<in> RenamingTT P OtherEvent"
    assume Timelock_notin_Xa: "Event Timelock \<notin> Xa"
    assume X3_subset_Xa: "X3 \<subseteq> Xa"

    have Timelock_notin_X3: "Event Timelock \<notin> X3"
      using Timelock_notin_Xa X3_subset_Xa by blast
    have x'3_tock_notin_TimeSyncInterruptTT: "x'3 @ [[X3]\<^sub>R, [Tock]\<^sub>E] \<notin> (RenamingTT P OtherEvent \<triangle>\<^sub>T Timelock \<rightarrow>\<^sub>C (STOP\<^sub>C \<triangle>\<^bsub>1\<^esub> TChaosTT))"
      using "3" P_wf ttWF_dist_cons_refusal unprioiritised_remove_timelock_spec_wf by fastforce

    have Timelock_in_prirefTT_X3: 
      "Event Timelock \<in> prirefTT (f2porder timelock_ordering) x'3 (RenamingTT P OtherEvent \<triangle>\<^sub>T Timelock \<rightarrow>\<^sub>C (STOP\<^sub>C \<triangle>\<^bsub>1\<^esub> TChaosTT)) X3"
      using "2" "3" by blast
    have Timelock_notin_prirefTT_X3: 
      "Event Timelock \<notin> prirefTT (f2porder timelock_ordering) x'3 (RenamingTT P OtherEvent \<triangle>\<^sub>T Timelock \<rightarrow>\<^sub>C (STOP\<^sub>C \<triangle>\<^bsub>1\<^esub> TChaosTT)) X3"
      using Timelock_notin_X3 x'3_tock_notin_TimeSyncInterruptTT unfolding prirefTT_def apply auto
      unfolding my_le_def my_lt_def by (auto simp add: timelock_ordering_porder_cancel, case_tac b, auto)

    show False
      using Timelock_notin_prirefTT_X3 Timelock_in_prirefTT_X3 by blast
  qed
qed

lemma remove_timelock_spec_timelock_free_no_effect:
  assumes P_wf: "\<forall>x\<in>P. ttWF x" and TT1_P: "TT1 P" and TT2_P: "TT2 P"
  assumes P_timelock_free: "timelock_free P" 
  shows "remove_timelock_spec P = RenamingTT P OtherEvent"
proof auto
  fix x
  assume x_in_remove_timelock_spec: "x \<in> remove_timelock_spec P"

  have 1:  "\<And>P. \<forall>x\<in>P. ttWF x \<Longrightarrow> TT1 P \<Longrightarrow> TT2 P \<Longrightarrow> timelock_free P \<Longrightarrow> ttWF x \<Longrightarrow>
    x \<in> remove_timelock_spec P \<Longrightarrow> x \<in> PriTT (f2porder timelock_ordering) (RenamingTT P OtherEvent \<triangle>\<^sub>T Timelock \<rightarrow>\<^sub>C (STOP\<^sub>C \<triangle>\<^bsub>1\<^esub> TChaosTT))"
    unfolding remove_timelock_spec_def HidingTT_def
  proof (auto, induct x rule:ttWF.induct, auto)
    fix p and P :: "'b ttprocess"
    assume P_wf: "\<forall>x\<in>P. ttWF x" and TT1_P: "TT1 P" and TT2_P: "TT2 P"
    assume P_timelock_free: "timelock_free P"
    assume p_in_PriTT: "p \<in> PriTT (f2porder timelock_ordering) (RenamingTT P OtherEvent \<triangle>\<^sub>T Timelock \<rightarrow>\<^sub>C (STOP\<^sub>C \<triangle>\<^bsub>Suc 0\<^esub> TChaosTT))"
    assume empty_in_p_hiding: "[] \<in> hide_trace {Event Timelock} p"
    then have "p = [] \<or> (\<exists>p'. p = [Event Timelock]\<^sub>E # p')"
      by (cases p rule:ttWF.cases, auto)
    then have "p = []"
      using P_timelock_free P_wf TT1_P TT2_P unhidden_remove_timelock_spec_timelock_free_no_init_Timelock p_in_PriTT by blast
    then show "[] \<in> PriTT (f2porder timelock_ordering) (RenamingTT P OtherEvent \<triangle>\<^sub>T Timelock \<rightarrow>\<^sub>C (STOP\<^sub>C \<triangle>\<^bsub>Suc 0\<^esub> TChaosTT))"
      using p_in_PriTT by blast
  next
    fix X p and P :: "'b ttprocess"
    assume P_wf: "\<forall>x\<in>P. ttWF x" and TT1_P: "TT1 P" and TT2_P: "TT2 P"
    assume P_timelock_free: "timelock_free P"
    assume p_in_PriTT: "p \<in> PriTT (f2porder timelock_ordering) (RenamingTT P OtherEvent \<triangle>\<^sub>T Timelock \<rightarrow>\<^sub>C (STOP\<^sub>C \<triangle>\<^bsub>Suc 0\<^esub> TChaosTT))"
    assume X_in_p_hiding: "[[X]\<^sub>R] \<in> hide_trace {Event Timelock} p"
    then have "\<exists>Y. p = [[Y]\<^sub>R] \<and> X \<subseteq> Y \<and> Event Timelock \<in> Y"
      using P_timelock_free P_wf TT1_P TT2_P unhidden_remove_timelock_spec_timelock_free_no_init_Timelock p_in_PriTT by (cases p rule:ttWF.cases, auto)
    then obtain Y where "p = [[Y]\<^sub>R] \<and> X \<subseteq> Y \<and> Event Timelock \<in> Y"
      by auto
    also have Timelock_prefix_wf: "\<forall>x\<in>(Timelock \<rightarrow>\<^sub>C (STOP\<^sub>C \<triangle>\<^bsub>Suc 0\<^esub> TChaosTT)). ttWF x"
      using Timelock_prefix_deadline_miss_wf by blast
    have TimeSyncInterruptTT_wf: "\<forall>x\<in>(RenamingTT P OtherEvent \<triangle>\<^sub>T Timelock \<rightarrow>\<^sub>C (STOP\<^sub>C \<triangle>\<^bsub>Suc 0\<^esub> TChaosTT)). ttWF x"
      by (smt P_wf RenamingTT_wf TimeSyncInterruptTT_wf Timelock_prefix_wf)
    have TT1_Timelock_prefix: "TT1 (Timelock \<rightarrow>\<^sub>C (STOP\<^sub>C \<triangle>\<^bsub>Suc 0\<^esub> TChaosTT))"
      using Timelock_prefix_deadline_miss_TT1 by blast
    then have "TT1 (Timelock \<rightarrow>\<^sub>C (STOP\<^sub>C \<triangle>\<^bsub>Suc 0\<^esub> TChaosTT))"
      by (smt PrefixTT_wf StopTT_wf StrictTimedInterruptTT_wf mem_Collect_eq)
    then have "TT1 (RenamingTT P OtherEvent \<triangle>\<^sub>T Timelock \<rightarrow>\<^sub>C (STOP\<^sub>C \<triangle>\<^bsub>Suc 0\<^esub> TChaosTT))"
      by (metis P_wf RenamingTT_wf TT1_P TT1_Renaming TT1_TimeSyncInterrupt Timelock_prefix_wf)
    then have "TT1  (PriTT (f2porder timelock_ordering) (RenamingTT P OtherEvent \<triangle>\<^sub>T Timelock \<rightarrow>\<^sub>C (STOP\<^sub>C \<triangle>\<^bsub>Suc 0\<^esub> TChaosTT)))"
      by (simp add: TT1_PriTT TimeSyncInterruptTT_wf)
    then show "[[X]\<^sub>R] \<in> PriTT (f2porder timelock_ordering) (RenamingTT P OtherEvent \<triangle>\<^sub>T Timelock \<rightarrow>\<^sub>C (STOP\<^sub>C \<triangle>\<^bsub>Suc 0\<^esub> TChaosTT))"
      by (metis TT1_def calculation p_in_PriTT tt_prefix_subset.simps(1) tt_prefix_subset.simps(2))
  next
    fix p :: "'b timelock_event tttrace" and P :: "'b ttprocess"
    assume P_wf: "\<forall>x\<in>P. ttWF x" and TT1_P: "TT1 P" and TT2_P: "TT2 P"
    assume P_timelock_free: "timelock_free P"
    assume "[[Tick]\<^sub>E] \<in> hide_trace {Event Timelock} p" "p \<in> PriTT (f2porder timelock_ordering) (RenamingTT P OtherEvent \<triangle>\<^sub>T Timelock \<rightarrow>\<^sub>C (STOP\<^sub>C \<triangle>\<^bsub>Suc 0\<^esub> TChaosTT))"
    then have "p = [[Tick]\<^sub>E]"
      by (cases p rule:ttWF.cases, auto simp add: P_timelock_free P_wf TT1_P TT2_P unhidden_remove_timelock_spec_timelock_free_no_init_Timelock)
    then show "p \<in> PriTT (f2porder timelock_ordering) (RenamingTT P OtherEvent \<triangle>\<^sub>T Timelock \<rightarrow>\<^sub>C (STOP\<^sub>C \<triangle>\<^bsub>Suc 0\<^esub> TChaosTT)) \<Longrightarrow>
        [[Tick]\<^sub>E] \<in> PriTT (f2porder timelock_ordering) (RenamingTT P OtherEvent \<triangle>\<^sub>T Timelock \<rightarrow>\<^sub>C (STOP\<^sub>C \<triangle>\<^bsub>Suc 0\<^esub> TChaosTT))"
      by blast
  next
    fix e and \<sigma> p :: "'b timelock_event tttrace" and P :: "'b ttprocess"
    assume P_wf: "\<forall>x\<in>P. ttWF x" and TT1_P: "TT1 P" and TT2_P: "TT2 P"
    assume P_timelock_free: "timelock_free P"
    assume e_\<sigma>_in_hide_trace_p: "[Event e]\<^sub>E # \<sigma> \<in> hide_trace {Event Timelock} p"
    assume p_in_PriTT: "p \<in> PriTT (f2porder timelock_ordering) (RenamingTT P OtherEvent \<triangle>\<^sub>T Timelock \<rightarrow>\<^sub>C (STOP\<^sub>C \<triangle>\<^bsub>Suc 0\<^esub> TChaosTT))"
    assume ind_hyp: "\<And>P p. \<forall>x\<in>P. ttWF x \<Longrightarrow> TT1 P \<Longrightarrow> TT2 P \<Longrightarrow> timelock_free P \<Longrightarrow> \<sigma> \<in> hide_trace {Event Timelock} p \<Longrightarrow>
      p \<in> PriTT (f2porder timelock_ordering) (RenamingTT P OtherEvent \<triangle>\<^sub>T Timelock \<rightarrow>\<^sub>C (STOP\<^sub>C \<triangle>\<^bsub>Suc 0\<^esub> TChaosTT)) \<Longrightarrow>
      \<sigma> \<in> PriTT (f2porder timelock_ordering) (RenamingTT P OtherEvent \<triangle>\<^sub>T Timelock \<rightarrow>\<^sub>C (STOP\<^sub>C \<triangle>\<^bsub>Suc 0\<^esub> TChaosTT))"

    obtain p' e' where 1: "p = [Event e]\<^sub>E # p' \<and> \<sigma> \<in> hide_trace {Event Timelock} p' \<and> e = OtherEvent e'"
      using e_\<sigma>_in_hide_trace_p apply (cases p rule:ttWF.cases, auto)
      using P_timelock_free P_wf TT1_P TT2_P unhidden_remove_timelock_spec_timelock_free_no_init_Timelock p_in_PriTT by (blast, meson timelock_event.exhaust)
    have 2: "\<forall>x\<in>{t. [Event e']\<^sub>E # t \<in> P}. ttWF x"
      using P_wf by auto
    have 3: "TT1 {t. [Event e']\<^sub>E # t \<in> P}"
      by (simp add: TT1_P TT1_init_event)
    have 4: "TT2 {t. [Event e']\<^sub>E # t \<in> P}"
      by (simp add: TT2_P TT2_init_event)
    have 5: "timelock_free {t. [Event e']\<^sub>E # t \<in> P}"
      by (metis (mono_tags, lifting) P_timelock_free mem_Collect_eq timelock_free_def timelock_free_trace.simps(2))

    have 6: "p' \<in> PriTT (f2porder timelock_ordering) (RenamingTT {t. [Event e']\<^sub>E # t \<in> P} OtherEvent \<triangle>\<^sub>T Timelock \<rightarrow>\<^sub>C (STOP\<^sub>C \<triangle>\<^bsub>Suc 0\<^esub> TChaosTT))"
      using "1" P_wf p_in_PriTT unhidden_remove_timelock_spec_init_event by fastforce

    have "\<sigma> \<in> PriTT (f2porder timelock_ordering) (RenamingTT {t. [Event e']\<^sub>E # t \<in> P} OtherEvent \<triangle>\<^sub>T Timelock \<rightarrow>\<^sub>C (STOP\<^sub>C \<triangle>\<^bsub>Suc 0\<^esub> TChaosTT))"
      using ind_hyp 1 2 3 4 5 6 by auto
    then have "\<sigma> \<in> {t. [Event (OtherEvent e')]\<^sub>E # t \<in> PriTT (f2porder timelock_ordering) (RenamingTT P OtherEvent \<triangle>\<^sub>T Timelock \<rightarrow>\<^sub>C (STOP\<^sub>C \<triangle>\<^bsub>Suc 0\<^esub> TChaosTT))}"
      by (simp add: P_wf unhidden_remove_timelock_spec_init_event)
    then show "[Event e]\<^sub>E # \<sigma> \<in> PriTT (f2porder timelock_ordering) (RenamingTT P OtherEvent \<triangle>\<^sub>T Timelock \<rightarrow>\<^sub>C (STOP\<^sub>C \<triangle>\<^bsub>Suc 0\<^esub> TChaosTT))"
      using "1" by blast
  next
    fix X and \<sigma> p :: "'b timelock_event tttrace" and P :: "'b ttprocess"
    assume P_wf: "\<forall>x\<in>P. ttWF x" and TT1_P: "TT1 P" and TT2_P: "TT2 P"
    assume P_timelock_free: "timelock_free P"
    assume p_in_PriTT: "p \<in> PriTT (f2porder timelock_ordering) (RenamingTT P OtherEvent \<triangle>\<^sub>T Timelock \<rightarrow>\<^sub>C (STOP\<^sub>C \<triangle>\<^bsub>Suc 0\<^esub> TChaosTT))"
    assume X_Tock_\<sigma>_in_hide_trace_p: "[X]\<^sub>R # [Tock]\<^sub>E # \<sigma> \<in> hide_trace {Event Timelock} p"
    assume ttWF_\<sigma>: "ttWF \<sigma>"
    assume Tock_notin_X: "Tock \<notin> X"
    assume ind_hyp: "\<And>P p. \<forall>x\<in>P. ttWF x \<Longrightarrow> TT1 P \<Longrightarrow> TT2 P \<Longrightarrow> timelock_free P \<Longrightarrow> \<sigma> \<in> hide_trace {Event Timelock} p \<Longrightarrow>
        p \<in> PriTT (f2porder timelock_ordering) (RenamingTT P OtherEvent \<triangle>\<^sub>T Timelock \<rightarrow>\<^sub>C (STOP\<^sub>C \<triangle>\<^bsub>Suc 0\<^esub> TChaosTT)) \<Longrightarrow>
        \<sigma> \<in> PriTT (f2porder timelock_ordering) (RenamingTT P OtherEvent \<triangle>\<^sub>T Timelock \<rightarrow>\<^sub>C (STOP\<^sub>C \<triangle>\<^bsub>Suc 0\<^esub> TChaosTT))"

    obtain p' X' where p_def: "p = [X']\<^sub>R # [Tock]\<^sub>E # p' \<and> X \<subseteq> X'"
      using X_Tock_\<sigma>_in_hide_trace_p apply (cases p rule:ttWF.cases, auto)
      using P_timelock_free P_wf TT1_P TT2_P unhidden_remove_timelock_spec_timelock_free_no_init_Timelock p_in_PriTT by blast

    have 1: "\<forall>x\<in>{t. [(lift_renaming_func OtherEvent) -` X']\<^sub>R # [Tock]\<^sub>E # t \<in> P}. ttWF x"
      using P_wf by fastforce
    have 2: "TT1 {t. [(lift_renaming_func OtherEvent) -` X']\<^sub>R # [Tock]\<^sub>E # t \<in> P}"
      by (simp add: TT1_P TT1_init_tock)
    have 3: "TT2 {t. [(lift_renaming_func OtherEvent) -` X']\<^sub>R # [Tock]\<^sub>E # t \<in> P}"
      by (simp add: TT2_P TT2_init_tock)
    have 4: "timelock_free {t. [(lift_renaming_func OtherEvent) -` X']\<^sub>R # [Tock]\<^sub>E # t \<in> P}"
      by (metis (no_types, lifting) P_timelock_free mem_Collect_eq timelock_free_def timelock_free_trace.simps(2) timelock_free_trace.simps(3))

    have 5: "\<sigma> \<in> hide_trace {Event Timelock} p'"
      using X_Tock_\<sigma>_in_hide_trace_p p_def by auto

    have 6: "p' \<in> PriTT (f2porder timelock_ordering) (RenamingTT {t. [(lift_renaming_func OtherEvent) -` X']\<^sub>R # [Tock]\<^sub>E # t \<in> P} OtherEvent \<triangle>\<^sub>T Timelock \<rightarrow>\<^sub>C (STOP\<^sub>C \<triangle>\<^bsub>Suc 0\<^esub> TChaosTT))"
      using P_timelock_free P_wf TT1_P TT2_P p_def p_in_PriTT unhidden_remove_timelock_spec_init_tock by fastforce
    
    have "\<sigma> \<in> PriTT (f2porder timelock_ordering) (RenamingTT {t. [(lift_renaming_func OtherEvent) -` X']\<^sub>R # [Tock]\<^sub>E # t \<in> P} OtherEvent \<triangle>\<^sub>T Timelock \<rightarrow>\<^sub>C (STOP\<^sub>C \<triangle>\<^bsub>Suc 0\<^esub> TChaosTT))"
      using ind_hyp[where P="{t. [(lift_renaming_func OtherEvent) -` X']\<^sub>R # [Tock]\<^sub>E # t \<in> P}", where p=p'] 1 2 3 4 5 6 by auto
    then have "\<sigma> \<in> {t. [X']\<^sub>R # [Tock]\<^sub>E # t \<in> PriTT (f2porder timelock_ordering) (RenamingTT P OtherEvent \<triangle>\<^sub>T Timelock \<rightarrow>\<^sub>C (STOP\<^sub>C \<triangle>\<^bsub>Suc 0\<^esub> TChaosTT))}"
      by (simp add: P_timelock_free P_wf TT1_P TT2_P unhidden_remove_timelock_spec_init_tock)
    also have "TT1 (PriTT (f2porder timelock_ordering) (RenamingTT P OtherEvent \<triangle>\<^sub>T Timelock \<rightarrow>\<^sub>C (STOP\<^sub>C \<triangle>\<^bsub>Suc 0\<^esub> TChaosTT)))"
      by (meson P_wf TT1_P TT1_PriTT unprioiritised_remove_timelock_spec_TT1 unprioiritised_remove_timelock_spec_wf)
    then show "[X]\<^sub>R # [Tock]\<^sub>E # \<sigma> \<in> PriTT (f2porder timelock_ordering) (RenamingTT P OtherEvent \<triangle>\<^sub>T Timelock \<rightarrow>\<^sub>C (STOP\<^sub>C \<triangle>\<^bsub>Suc 0\<^esub> TChaosTT))"
      using calculation p_def tt_prefix_subset_refl unfolding TT1_def apply auto
      by (erule_tac x="[X]\<^sub>R # [Tock]\<^sub>E # \<sigma>" in allE, auto, erule_tac x="[X']\<^sub>R # [Tock]\<^sub>E # \<sigma>" in allE, auto)
  qed
      
  have 2: "\<And>P. \<forall>x\<in>P. ttWF x \<Longrightarrow> TT1 P \<Longrightarrow> TT2 P \<Longrightarrow> timelock_free P \<Longrightarrow> ttWF x \<Longrightarrow>
    x \<in> PriTT (f2porder timelock_ordering) (RenamingTT P OtherEvent \<triangle>\<^sub>T Timelock \<rightarrow>\<^sub>C (STOP\<^sub>C \<triangle>\<^bsub>1\<^esub> TChaosTT)) \<Longrightarrow>
    x \<in> RenamingTT P OtherEvent"
  proof (induct x rule:ttWF.induct, auto)
    fix P :: "'b ttprocess"
    assume "[] \<in> PriTT (f2porder timelock_ordering) (RenamingTT P OtherEvent \<triangle>\<^sub>T Timelock \<rightarrow>\<^sub>C (STOP\<^sub>C \<triangle>\<^bsub>Suc 0\<^esub> TChaosTT))"
    then show "[] \<in> RenamingTT P OtherEvent"
      unfolding PriTT_def apply (auto, case_tac s rule:ttWF.cases, auto)
      unfolding TimeSyncInterruptTT_def by auto
  next
    fix P :: "'b ttprocess" and X
    assume TT1_P: "TT1 P"
    assume "[[X]\<^sub>R] \<in> PriTT (f2porder timelock_ordering) (RenamingTT P OtherEvent \<triangle>\<^sub>T Timelock \<rightarrow>\<^sub>C (STOP\<^sub>C \<triangle>\<^bsub>Suc 0\<^esub> TChaosTT))"
    then obtain X' where X'_assms: "X \<subseteq> X' \<union> {Event Timelock} \<and> [[X']\<^sub>R] \<in> RenamingTT P OtherEvent \<triangle>\<^sub>T Timelock \<rightarrow>\<^sub>C (STOP\<^sub>C \<triangle>\<^bsub>Suc 0\<^esub> TChaosTT)"
      unfolding PriTT_def apply (safe, case_tac s rule:ttWF.cases, auto)
      by (smt OtherEvent_maximal Tick_maximal Tock_maximal insertCI maximal_notin_prirefTT subset_iff timelock_event.exhaust ttevent.exhaust)
    then have "[[X']\<^sub>R] \<in> RenamingTT P OtherEvent"
      unfolding TimeSyncInterruptTT_def
    proof (safe, simp_all)
      fix p and Xa Y Z :: "'b timelock_event ttevent set"
      assume "[[Y]\<^sub>R] \<in> Timelock \<rightarrow>\<^sub>C (STOP\<^sub>C \<triangle>\<^bsub>Suc 0\<^esub> TChaosTT)"
      then have "Tock \<notin> Y"
        unfolding PrefixTT_def by (auto simp add:notin_tocks Cons_eq_append_conv)
      then have "Z \<subseteq> Xa \<union> Y \<Longrightarrow> {e \<in> Xa. e \<noteq> Tock} = {e \<in> Y. e \<noteq> Tock} \<Longrightarrow> Z \<subseteq> Xa"
        by blast
      then show "Z \<subseteq> Xa \<union> Y \<Longrightarrow> {e \<in> Xa. e \<noteq> Tock} = {e \<in> Y. e \<noteq> Tock} \<Longrightarrow>
          [[Xa]\<^sub>R] \<in> RenamingTT P OtherEvent \<Longrightarrow> [[Z]\<^sub>R] \<in> RenamingTT P OtherEvent"
        by (meson TT1_P TT1_Renaming TT1_def tt_prefix_subset.simps(1) tt_prefix_subset.simps(2))
    next
      fix p q2
      assume "\<forall>p' Y. p \<noteq> p' @ [[Y]\<^sub>R]" "\<forall>q' Y. q2 \<noteq> [Y]\<^sub>R # q'" "[[X']\<^sub>R] = p @ q2"
      then have "False"
        by (cases p rule:ttWF.cases, auto)
      then show "p @ q2 \<in> RenamingTT P OtherEvent"
        by auto
    qed
    also have "TT1 (RenamingTT P OtherEvent)"
      by (simp add: TT1_P TT1_Renaming)
    then have "[[{e\<in>X. e \<noteq> Event Timelock}]\<^sub>R] \<in> RenamingTT P OtherEvent"
      using calculation X'_assms unfolding TT1_def apply auto
      by (erule_tac x="[[{e\<in>X. e \<noteq> Event Timelock}]\<^sub>R]" in allE, auto, erule_tac x="[[X']\<^sub>R]" in allE, auto)
    then show "[[X]\<^sub>R] \<in> RenamingTT P OtherEvent"
    proof (cases "Event Timelock \<in> X", auto)
      assume "Event Timelock \<notin> X"
      then have "{e \<in> X. e \<noteq> Event Timelock} = X"
        by auto
      then show "[[{e \<in> X. e \<noteq> Event Timelock}]\<^sub>R] \<in> RenamingTT P OtherEvent \<Longrightarrow> [[X]\<^sub>R] \<in> RenamingTT P OtherEvent"
        by auto
    next
      show "Event Timelock \<in> X \<Longrightarrow> [[{e \<in> X. e \<noteq> Event Timelock}]\<^sub>R] \<in> RenamingTT P OtherEvent \<Longrightarrow> [[X]\<^sub>R] \<in> RenamingTT P OtherEvent"
        unfolding RenamingTT_def apply (auto, case_tac x rule:ttWF.cases, auto)
        apply (rule_tac x="[[{y. lift_renaming_func OtherEvent y \<in> X \<and> lift_renaming_func OtherEvent y \<noteq> Event Timelock}]\<^sub>R]" in bexI, auto)
        by (case_tac x, auto)
    qed
  next
    fix P :: "'b ttprocess"
    assume "[[Tick]\<^sub>E] \<in> PriTT (f2porder timelock_ordering) (RenamingTT P OtherEvent \<triangle>\<^sub>T Timelock \<rightarrow>\<^sub>C (STOP\<^sub>C \<triangle>\<^bsub>Suc 0\<^esub> TChaosTT))"
    then show "[[Tick]\<^sub>E] \<in> RenamingTT P OtherEvent"
      unfolding PriTT_def apply auto apply (case_tac s rule:ttWF.cases, auto)
      unfolding TimeSyncInterruptTT_def
    proof auto
      fix p q2 :: "'b timelock_event tttrace"
      assume assm: "[[Tick]\<^sub>E] = p @ q2"
      then have "(p = [[Tick]\<^sub>E] \<and> q2 = []) \<or> (p = [] \<and> q2 = [[Tick]\<^sub>E])"
        by (case_tac p rule:ttWF.cases, simp, simp, blast, simp_all)
      then show "p \<in> RenamingTT P OtherEvent \<Longrightarrow>
          filter_tocks p @ q2 \<in> Timelock \<rightarrow>\<^sub>C (STOP\<^sub>C \<triangle>\<^bsub>Suc 0\<^esub> TChaosTT) \<Longrightarrow>
          p @ q2 \<in> RenamingTT P OtherEvent"
      unfolding PrefixTT_def apply (auto simp add: notin_tocks)
      by (metis Nil_is_append_conv append_Nil butlast.simps(2) butlast_append last.simps list.distinct(1) ttevent.distinct(3) ttobs.inject(1))
    qed
  next
    fix P :: "'b ttprocess" and e \<sigma>
    assume P_wf: "\<forall>x\<in>P. ttWF x" and TT1_P: "TT1 P" and TT2_P: "TT2 P" and P_timelock_free: "timelock_free P"
    assume e_\<sigma>_in_PriTT: "[Event e]\<^sub>E # \<sigma> \<in> PriTT (f2porder timelock_ordering) (RenamingTT P OtherEvent \<triangle>\<^sub>T Timelock \<rightarrow>\<^sub>C (STOP\<^sub>C \<triangle>\<^bsub>Suc 0\<^esub> TChaosTT))"
    assume ind_hyp: "\<And>P. \<forall>x\<in>P. ttWF x \<Longrightarrow> TT1 P \<Longrightarrow> TT2 P \<Longrightarrow> timelock_free P \<Longrightarrow>
             \<sigma> \<in> PriTT (f2porder timelock_ordering) (RenamingTT P OtherEvent \<triangle>\<^sub>T Timelock \<rightarrow>\<^sub>C (STOP\<^sub>C \<triangle>\<^bsub>Suc 0\<^esub> TChaosTT)) \<Longrightarrow>
             \<sigma> \<in> RenamingTT P OtherEvent"

    obtain e' where e_is_OtherEvent: "e = OtherEvent e'"
      using e_\<sigma>_in_PriTT apply (cases e, auto)
      by (simp add: P_timelock_free P_wf TT1_P TT2_P unhidden_remove_timelock_spec_timelock_free_no_init_Timelock)
    
    have 1: "\<forall>x\<in>{t. [Event e']\<^sub>E # t \<in> P}. ttWF x"
      using P_wf by auto
    have 2: "TT1 {t. [Event e']\<^sub>E # t \<in> P}"
      by (simp add: TT1_P TT1_init_event)
    have 3: "TT2 {t. [Event e']\<^sub>E # t \<in> P}"
      by (simp add: TT2_P TT2_init_event)
    have 4: "timelock_free {t. [Event e']\<^sub>E # t \<in> P}"
      by (metis (no_types, lifting) P_timelock_free mem_Collect_eq timelock_free_def timelock_free_trace.simps(2))

    have "\<sigma> \<in> PriTT (f2porder timelock_ordering) (RenamingTT {t. [Event e']\<^sub>E # t \<in> P} OtherEvent \<triangle>\<^sub>T Timelock \<rightarrow>\<^sub>C (STOP\<^sub>C \<triangle>\<^bsub>Suc 0\<^esub> TChaosTT))"
      using P_wf e_\<sigma>_in_PriTT e_is_OtherEvent unhidden_remove_timelock_spec_init_event by fastforce
    then have "\<sigma> \<in> RenamingTT {t. [Event e']\<^sub>E # t \<in> P} OtherEvent"
      using "1" "2" "3" "4" ind_hyp by blast
    then show "[Event e]\<^sub>E # \<sigma> \<in> RenamingTT P OtherEvent"
      by (metis (mono_tags, lifting) RenamingTT_init_event e_is_OtherEvent inj_def mem_Collect_eq timelock_event.inject)
  next
    fix P :: "'b ttprocess" and X \<sigma>
    assume P_wf: "\<forall>x\<in>P. ttWF x" and TT1_P: "TT1 P" and TT2_P: "TT2 P" and P_timelock_free: "timelock_free P"
    assume X_Tock_\<sigma>_in_PriTT: "[X]\<^sub>R # [Tock]\<^sub>E # \<sigma> \<in> PriTT (f2porder timelock_ordering) (RenamingTT P OtherEvent \<triangle>\<^sub>T Timelock \<rightarrow>\<^sub>C (STOP\<^sub>C \<triangle>\<^bsub>Suc 0\<^esub> TChaosTT))"
    assume ind_hyp: "(\<And>P. \<forall>x\<in>P. ttWF x \<Longrightarrow> TT1 P \<Longrightarrow> TT2 P \<Longrightarrow> timelock_free P \<Longrightarrow>
             \<sigma> \<in> PriTT (f2porder timelock_ordering) (RenamingTT P OtherEvent \<triangle>\<^sub>T Timelock \<rightarrow>\<^sub>C (STOP\<^sub>C \<triangle>\<^bsub>Suc 0\<^esub> TChaosTT)) \<Longrightarrow>
             \<sigma> \<in> RenamingTT P OtherEvent)"

    have 1: "\<forall>x\<in>{\<sigma>. [lift_renaming_func OtherEvent -` X]\<^sub>R # [Tock]\<^sub>E # \<sigma> \<in> P}. ttWF x"
      using P_wf by auto
    have 2: "TT1 {\<sigma>. [lift_renaming_func OtherEvent -` X]\<^sub>R # [Tock]\<^sub>E # \<sigma> \<in> P}"
      by (simp add: TT1_P TT1_init_tock)
    have 3: "TT2 {\<sigma>. [lift_renaming_func OtherEvent -` X]\<^sub>R # [Tock]\<^sub>E # \<sigma> \<in> P}"
      by (simp add: TT2_P TT2_init_tock)
    have 4: "timelock_free {\<sigma>. [lift_renaming_func OtherEvent -` X]\<^sub>R # [Tock]\<^sub>E # \<sigma> \<in> P}"
      by (metis (mono_tags, lifting) P_timelock_free mem_Collect_eq timelock_free_def timelock_free_trace.simps(2) timelock_free_trace.simps(3))

    have 5: "\<sigma> \<in> PriTT (f2porder timelock_ordering) (RenamingTT {\<sigma>. [lift_renaming_func OtherEvent -` X]\<^sub>R # [Tock]\<^sub>E # \<sigma> \<in> P} OtherEvent \<triangle>\<^sub>T Timelock \<rightarrow>\<^sub>C (STOP\<^sub>C \<triangle>\<^bsub>Suc 0\<^esub> TChaosTT))"
      using P_timelock_free P_wf TT1_P TT2_P X_Tock_\<sigma>_in_PriTT unhidden_remove_timelock_spec_init_tock by auto

    have "\<sigma> \<in> RenamingTT {\<sigma>. [lift_renaming_func OtherEvent -` X]\<^sub>R # [Tock]\<^sub>E # \<sigma> \<in> P} OtherEvent"
      using "1" "2" "3" "4" "5" ind_hyp by blast
    then show "[X]\<^sub>R # [Tock]\<^sub>E # \<sigma> \<in> RenamingTT P OtherEvent"
      using RenamingTT_init_tock by blast
  qed

  have x_wf: "ttWF x"
    using P_wf remove_timelock_spec_wf x_in_remove_timelock_spec by blast

  show "x \<in> RenamingTT P OtherEvent"
    using x_in_remove_timelock_spec 1 2 x_wf assms by auto
next
  fix x :: "'a timelock_event tttrace"
  have "\<And>P. \<forall>x\<in>P. ttWF x \<Longrightarrow> TT1 P \<Longrightarrow> TT2 P \<Longrightarrow> timelock_free P \<Longrightarrow> ttWF x \<Longrightarrow> x \<in> RenamingTT P OtherEvent \<Longrightarrow>
    x \<in> remove_timelock_spec P"
  proof (induct x rule:ttWF.induct, simp_all)
    fix P :: "'b ttprocess"
    assume P_wf: "\<forall>x\<in>P. ttWF x" and TT1_P: "TT1 P" and TT2_P: "TT2 P" and P_timelock_free: "timelock_free P"
    assume "[] \<in> RenamingTT P OtherEvent"
    then have "[] \<in> RenamingTT P OtherEvent \<triangle>\<^sub>T Timelock \<rightarrow>\<^sub>C (STOP\<^sub>C \<triangle>\<^bsub>1\<^esub> TChaosTT)"
      unfolding TimeSyncInterruptTT_def PrefixTT_def by (auto simp add: tocks.empty_in_tocks)
    then have "[] \<in> PriTT (f2porder timelock_ordering) (RenamingTT P OtherEvent \<triangle>\<^sub>T Timelock \<rightarrow>\<^sub>C (STOP\<^sub>C \<triangle>\<^bsub>1\<^esub> TChaosTT))"
      unfolding PriTT_def by (auto, rule_tac x="[]" in exI, auto)
    then show "[] \<in> remove_timelock_spec P"
      unfolding remove_timelock_spec_def HidingTT_def by auto
  next
    fix P :: "'b ttprocess" and X
    assume P_wf: "\<forall>x\<in>P. ttWF x" and TT1_P: "TT1 P" and TT2_P: "TT2 P" and P_timelock_free: "timelock_free P"
    assume "[[X]\<^sub>R] \<in> RenamingTT P OtherEvent"
    then have "[[{e\<in>X. e \<noteq> Event Timelock}]\<^sub>R] \<in> RenamingTT P OtherEvent"
      by (metis (mono_tags, lifting) TT1_P TT1_Renaming TT1_def mem_Collect_eq subsetI tt_prefix_subset.simps(1) tt_prefix_subset.simps(2))
    then have "[[{e\<in>X. e \<noteq> Event Timelock}]\<^sub>R] \<in> RenamingTT P OtherEvent \<triangle>\<^sub>T Timelock \<rightarrow>\<^sub>C (STOP\<^sub>C \<triangle>\<^bsub>1\<^esub> TChaosTT)"
      unfolding TimeSyncInterruptTT_def PrefixTT_def apply auto
      apply (rule_tac x="[]" in exI, rule_tac x="{e\<in>X. e \<noteq> Event Timelock}" in exI, auto)
      by (rule_tac x="{e \<in> X. e \<noteq> Event Timelock \<and> e \<noteq> Tock}" in exI, auto simp add: tocks.empty_in_tocks)
    then have "[[X \<union> {Event Timelock}]\<^sub>R] \<in> PriTT (f2porder timelock_ordering) (RenamingTT P OtherEvent \<triangle>\<^sub>T Timelock \<rightarrow>\<^sub>C (STOP\<^sub>C \<triangle>\<^bsub>1\<^esub> TChaosTT))"
      unfolding PriTT_def apply auto apply (rule_tac x="[[{e \<in> X. e \<noteq> Event Timelock}]\<^sub>R]" in exI, auto)
      apply (subst timelock_ordering_prirefTT, simp_all add: P_wf TT1_P TT2_P unprioiritised_remove_timelock_spec_TT2)
      using P_timelock_free P_wf unprioiritised_remove_timelock_spec_timelock_free apply blast
      using P_timelock_free P_wf TT1_P TT2_P timelock_ordering_prirefTT unprioiritised_remove_timelock_spec_TT2
              unprioiritised_remove_timelock_spec_timelock_free by fastforce
    then show "[[X]\<^sub>R] \<in> remove_timelock_spec P"
      unfolding remove_timelock_spec_def HidingTT_def by auto
  next
    fix P :: "'b ttprocess"
    assume P_wf: "\<forall>x\<in>P. ttWF x" and TT1_P: "TT1 P" and TT2_P: "TT2 P" and P_timelock_free: "timelock_free P"
    assume "[[Tick]\<^sub>E] \<in> RenamingTT P OtherEvent"
    then have "[[Tick]\<^sub>E] \<in> (RenamingTT P OtherEvent \<triangle>\<^sub>T Timelock \<rightarrow>\<^sub>C (STOP\<^sub>C \<triangle>\<^bsub>1\<^esub> TChaosTT))"
      unfolding TimeSyncInterruptTT_def PrefixTT_def by (auto simp add: tocks.empty_in_tocks)
    then have "[[Tick]\<^sub>E] \<in>  PriTT (f2porder timelock_ordering) (RenamingTT P OtherEvent \<triangle>\<^sub>T Timelock \<rightarrow>\<^sub>C (STOP\<^sub>C \<triangle>\<^bsub>1\<^esub> TChaosTT))"
      unfolding PriTT_def by (auto, rule_tac x="[[Tick]\<^sub>E]" in exI, auto simp add: Tick_maximal)
    then show "[[Tick]\<^sub>E] \<in> remove_timelock_spec P"
      unfolding remove_timelock_spec_def HidingTT_def by auto
  next
    fix P :: "'b ttprocess" and e \<sigma>
    assume P_wf: "\<forall>x\<in>P. ttWF x" and TT1_P: "TT1 P" and TT2_P: "TT2 P" and P_timelock_free: "timelock_free P"
    assume e_\<sigma>_in_renaming_P: "[Event e]\<^sub>E # \<sigma> \<in> RenamingTT P OtherEvent"
    assume ind_hyp: "\<And>P. \<forall>x\<in>P. ttWF x \<Longrightarrow> TT1 P \<Longrightarrow> TT2 P \<Longrightarrow> timelock_free P \<Longrightarrow> \<sigma> \<in> RenamingTT P OtherEvent \<Longrightarrow> \<sigma> \<in> remove_timelock_spec P"

    obtain e' where e_OtherEvent: "e = OtherEvent e'"
      using e_\<sigma>_in_renaming_P unfolding RenamingTT_def by (cases e, auto, case_tac x rule:ttWF.cases, auto)

    have 1: "\<forall>x\<in>{t. [Event e']\<^sub>E # t \<in> P}. ttWF x"
      using P_wf by auto
    have 2: "TT1 {t. [Event e']\<^sub>E # t \<in> P}"
      by (simp add: TT1_P TT1_init_event)
    have 3: "TT2 {t. [Event e']\<^sub>E # t \<in> P}"
      by (simp add: TT2_P TT2_init_event)
    have 4: "timelock_free {t. [Event e']\<^sub>E # t \<in> P}"
      by (metis (mono_tags, lifting) P_timelock_free mem_Collect_eq timelock_free_def timelock_free_trace.simps(2))
    have 5: "\<sigma> \<in> RenamingTT {t. [Event e']\<^sub>E # t \<in> P} OtherEvent"
      by (metis (mono_tags, lifting) RenamingTT_init_event e_OtherEvent e_\<sigma>_in_renaming_P inj_def mem_Collect_eq timelock_event.inject)

    have "\<sigma> \<in> remove_timelock_spec {t. [Event e']\<^sub>E # t \<in> P}"
      using "1" "2" "3" "4" "5" ind_hyp by blast
    then have "\<sigma> \<in> {t. [Event (OtherEvent e')]\<^sub>E # t \<in> remove_timelock_spec P}"
      by (simp add: P_timelock_free P_wf TT1_P TT2_P remove_timelock_spec_init_event)
    then show "[Event e]\<^sub>E # \<sigma> \<in> remove_timelock_spec P"
      using e_OtherEvent by blast
  next
    fix P :: "'b ttprocess" and X \<sigma>
    assume P_wf: "\<forall>x\<in>P. ttWF x" and TT1_P: "TT1 P" and TT2_P: "TT2 P" and P_timelock_free: "timelock_free P"
    assume X_Tock_\<sigma>_in_renaming_P: "[X]\<^sub>R # [Tock]\<^sub>E # \<sigma> \<in> RenamingTT P OtherEvent"
    assume ind_hyp: "\<And>P. \<forall>x\<in>P. ttWF x \<Longrightarrow> TT1 P \<Longrightarrow> TT2 P \<Longrightarrow> timelock_free P \<Longrightarrow> \<sigma> \<in> RenamingTT P OtherEvent \<Longrightarrow> \<sigma> \<in> remove_timelock_spec P"

    have 1: "\<forall>x\<in>{t. [(lift_renaming_func OtherEvent) -` X]\<^sub>R # [Tock]\<^sub>E # t \<in> P}. ttWF x"
      using P_wf by auto
    have 2: "TT1 {t. [(lift_renaming_func OtherEvent) -` X]\<^sub>R # [Tock]\<^sub>E # t \<in> P}"
      by (simp add: TT1_P TT1_init_tock)
    have 3: "TT2 {t. [(lift_renaming_func OtherEvent) -` X]\<^sub>R # [Tock]\<^sub>E # t \<in> P}"
      by (simp add: TT2_P TT2_init_tock)
    have 4: "timelock_free {t. [(lift_renaming_func OtherEvent) -` X]\<^sub>R # [Tock]\<^sub>E # t \<in> P}"
      by (metis (no_types, lifting) P_timelock_free mem_Collect_eq timelock_free_def timelock_free_trace.simps(2) timelock_free_trace.simps(3))
    have 5: "\<sigma> \<in> RenamingTT {t. [(lift_renaming_func OtherEvent) -` X]\<^sub>R # [Tock]\<^sub>E # t \<in> P} OtherEvent"
      using RenamingTT_init_tock X_Tock_\<sigma>_in_renaming_P by blast

    have "\<sigma> \<in> remove_timelock_spec {t. [(lift_renaming_func OtherEvent) -` X]\<^sub>R # [Tock]\<^sub>E # t \<in> P}"
      using "1" "2" "3" "4" "5" ind_hyp by blast
    then have "\<sigma> \<in> {t. [X]\<^sub>R # [Tock]\<^sub>E # t \<in> remove_timelock_spec P}"
      by (simp add: P_timelock_free P_wf TT1_P TT2_P remove_timelock_spec_init_tock)
    then show "[X]\<^sub>R # [Tock]\<^sub>E # \<sigma> \<in> remove_timelock_spec P"
      by auto
  qed
  then show "x \<in> RenamingTT P OtherEvent \<Longrightarrow> x \<in> remove_timelock_spec P"
    by (meson P_timelock_free P_wf RenamingTT_wf TT1_P TT2_P)
qed

section \<open>Constrained tick-tock traces refinement\<close>

definition ConstrainedTracesRefinesTT :: "'a ttprocess \<Rightarrow> 'a ttprocess \<Rightarrow> bool" (infix "\<sqsubseteq>\<^sub>C\<^sub>T\<^sub>T\<^sub>T" 50) where
  "P \<sqsubseteq>\<^sub>C\<^sub>T\<^sub>T\<^sub>T Q = (remove_timelock_spec P \<sqsubseteq>\<^sub>T\<^sub>T\<^sub>T RenamingTT Q OtherEvent)"
    
lemma in_traces_renaming_implies_in_traces_remove_timelock_spec:
  assumes P_wf: "\<forall>x\<in>P. ttWF x" and TT1_P "TT1 P"
  shows "x \<in> tracesTT (RenamingTT P OtherEvent) \<Longrightarrow> x \<in> tracesTT (remove_timelock_spec P)"
  unfolding tracesTT_def
proof auto
  fix s :: "'a timelock_event tttrace"

  have empty_implication: "\<And>P. [] \<in> RenamingTT P OtherEvent \<Longrightarrow> [] \<in> remove_timelock_spec P"
  proof -
    fix P :: "'b ttprocess"
    assume "[] \<in> RenamingTT P OtherEvent"
    then have "[] \<in> RenamingTT P OtherEvent \<triangle>\<^sub>T Timelock \<rightarrow>\<^sub>C (STOP\<^sub>C \<triangle>\<^bsub>1\<^esub> TChaosTT)"
      unfolding TimeSyncInterruptTT_def PrefixTT_def by (auto simp add: tocks.empty_in_tocks)
    then have "[] \<in> PriTT (f2porder timelock_ordering) (RenamingTT P OtherEvent \<triangle>\<^sub>T Timelock \<rightarrow>\<^sub>C (STOP\<^sub>C \<triangle>\<^bsub>1\<^esub> TChaosTT))"
      unfolding PriTT_def by (auto, rule_tac x="[]" in exI, auto)
    then show "[] \<in> remove_timelock_spec P"
      unfolding remove_timelock_spec_def HidingTT_def by auto
  qed

  have "\<And>P x. ttWF s \<Longrightarrow> \<forall>x\<in>P. ttWF x \<Longrightarrow> TT1 P \<Longrightarrow> s \<in> RenamingTT P OtherEvent \<Longrightarrow> x = tttrace_to_event_trace s \<Longrightarrow>
    \<exists>sa\<in>remove_timelock_spec P. tttrace_to_event_trace s = tttrace_to_event_trace sa"
  proof (induct s rule:ttWF.induct, auto)
    fix P :: "'b ttprocess"
    show "[] \<in> RenamingTT P OtherEvent \<Longrightarrow> \<exists>sa\<in>remove_timelock_spec P. [] = tttrace_to_event_trace sa"
      using empty_implication by (rule_tac x="[]" in bexI, auto)
  next
    fix P :: "'b ttprocess" and X
    assume TT1_P: "TT1 P"
    assume "[[X]\<^sub>R] \<in> RenamingTT P OtherEvent"
    then have "[] \<in> RenamingTT P OtherEvent"
      using TT1_P TT1_Renaming TT1_def tt_prefix_subset.simps(1) by blast
    then show "\<exists>sa\<in>remove_timelock_spec P. [] = tttrace_to_event_trace sa"
      by (rule_tac x="[]" in bexI, auto simp add: empty_implication)
  next
    fix P :: "'b ttprocess"
    assume "[[Tick]\<^sub>E] \<in> RenamingTT P OtherEvent"
    then have "[[Tick]\<^sub>E] \<in> RenamingTT P OtherEvent \<triangle>\<^sub>T Timelock \<rightarrow>\<^sub>C (STOP\<^sub>C \<triangle>\<^bsub>1\<^esub> TChaosTT)"
      unfolding TimeSyncInterruptTT_def PrefixTT_def by (auto simp add: tocks.empty_in_tocks)
    then have "[[Tick]\<^sub>E] \<in> PriTT (f2porder timelock_ordering) (RenamingTT P OtherEvent \<triangle>\<^sub>T Timelock \<rightarrow>\<^sub>C (STOP\<^sub>C \<triangle>\<^bsub>1\<^esub> TChaosTT))"
      unfolding PriTT_def by (auto, rule_tac x="[[Tick]\<^sub>E]" in exI, auto simp add: Tick_maximal)
    then have "[[Tick]\<^sub>E] \<in> remove_timelock_spec P"
      unfolding remove_timelock_spec_def HidingTT_def by auto
    then show "\<exists>sa\<in>remove_timelock_spec P. [Tick] = tttrace_to_event_trace sa"
      by (rule_tac x="[[Tick]\<^sub>E]" in bexI, auto)
  next
    fix P :: "'b ttprocess" and e \<sigma>
    assume P_wf: "\<forall>x\<in>P. ttWF x" and TT1_P: "TT1 P"
    assume e_\<sigma>_in_P_renaming: "[Event e]\<^sub>E # \<sigma> \<in> RenamingTT P OtherEvent"
    assume ind_hyp: "\<And>P x. \<forall>x\<in>P. ttWF x \<Longrightarrow> TT1 P \<Longrightarrow> \<sigma> \<in> RenamingTT P OtherEvent \<Longrightarrow> x = tttrace_to_event_trace \<sigma> \<Longrightarrow>
      \<exists>sa\<in>remove_timelock_spec P. tttrace_to_event_trace \<sigma> = tttrace_to_event_trace sa"

    obtain e' where e_OtherEvent: "e = OtherEvent e'"
      using e_\<sigma>_in_P_renaming unfolding RenamingTT_def by (auto, case_tac x rule:ttWF.cases, auto)

    have 1: "\<forall>x\<in>{t. [Event e']\<^sub>E # t \<in> P}. ttWF x"
      using P_wf by auto
    have 2: "TT1 {t. [Event e']\<^sub>E # t \<in> P}"
      by (simp add: TT1_P TT1_init_event)
    have 3: "\<sigma> \<in> RenamingTT {t. [Event e']\<^sub>E # t \<in> P} OtherEvent"
      by (metis (mono_tags, lifting) RenamingTT_init_event e_OtherEvent e_\<sigma>_in_P_renaming inj_def mem_Collect_eq timelock_event.inject)

    have "\<exists>sa\<in>remove_timelock_spec {t. [Event e']\<^sub>E # t \<in> P}. tttrace_to_event_trace \<sigma> = tttrace_to_event_trace sa"
      using 1 2 3 ind_hyp by blast
    then obtain sa where "sa\<in>remove_timelock_spec {t. [Event e']\<^sub>E # t \<in> P} \<and> tttrace_to_event_trace \<sigma> = tttrace_to_event_trace sa"
      by blast
    then have "sa \<in> {t. [Event e]\<^sub>E # t \<in> remove_timelock_spec P} \<and> tttrace_to_event_trace \<sigma> = tttrace_to_event_trace sa"
      using P_wf e_OtherEvent remove_timelock_spec_init_event by fastforce
    then show "\<exists>sa\<in>remove_timelock_spec P. Event e # tttrace_to_event_trace \<sigma> = tttrace_to_event_trace sa"
      by force
  next
    fix P :: "'b ttprocess" and X \<sigma>
    assume P_wf: "\<forall>x\<in>P. ttWF x" and TT1_P: "TT1 P"
    assume X_Tock_\<sigma>_in_P_renaming: "[X]\<^sub>R # [Tock]\<^sub>E # \<sigma> \<in> RenamingTT P OtherEvent"
    assume ind_hyp: "\<And>P x. \<forall>x\<in>P. ttWF x \<Longrightarrow> TT1 P \<Longrightarrow> \<sigma> \<in> RenamingTT P OtherEvent \<Longrightarrow>
               x = tttrace_to_event_trace \<sigma> \<Longrightarrow> \<exists>sa\<in>remove_timelock_spec P. tttrace_to_event_trace \<sigma> = tttrace_to_event_trace sa"

    have 1: "\<forall>x\<in>{t. [lift_renaming_func OtherEvent -` X]\<^sub>R # [Tock]\<^sub>E # t \<in> P}. ttWF x"
      using P_wf by auto
    have 2: "TT1 {t. [lift_renaming_func OtherEvent -` X]\<^sub>R # [Tock]\<^sub>E # t \<in> P}"
      by (simp add: TT1_P TT1_init_tock)
    have 3: "\<sigma> \<in> RenamingTT {t. [lift_renaming_func OtherEvent -` X]\<^sub>R # [Tock]\<^sub>E # t \<in> P} OtherEvent"
      using RenamingTT_init_tock X_Tock_\<sigma>_in_P_renaming by blast
    
    have "\<exists>sa\<in>remove_timelock_spec {t. [lift_renaming_func OtherEvent -` X]\<^sub>R # [Tock]\<^sub>E # t \<in> P}. tttrace_to_event_trace \<sigma> = tttrace_to_event_trace sa"
      using 1 2 3 ind_hyp by blast
    then obtain sa where "sa \<in> remove_timelock_spec {t. [lift_renaming_func OtherEvent -` X]\<^sub>R # [Tock]\<^sub>E # t \<in> P} \<and> tttrace_to_event_trace \<sigma> = tttrace_to_event_trace sa"
      by auto
    then have "sa \<in> {t. \<exists>X. [X]\<^sub>R # [Tock]\<^sub>E # t \<in> remove_timelock_spec P} \<and> tttrace_to_event_trace \<sigma> = tttrace_to_event_trace sa"
      using P_wf TT1_P remove_timelock_spec_init_tock_any_refusal_subset by blast
    then show "\<exists>sa\<in>remove_timelock_spec P. Tock # tttrace_to_event_trace \<sigma> = tttrace_to_event_trace sa"
      by (auto, rule_tac x="[X]\<^sub>R # [Tock]\<^sub>E # sa" in bexI, auto)
  qed
  then show "s \<in> RenamingTT P OtherEvent \<Longrightarrow> x = tttrace_to_event_trace s \<Longrightarrow>
    \<exists>sa\<in>remove_timelock_spec P. tttrace_to_event_trace s = tttrace_to_event_trace sa"
    using P_wf RenamingTT_wf assms(3) by blast
qed

lemma same_event_trace_implies_same_renamed_event_trace:
  "\<And>y. tttrace_to_event_trace x = tttrace_to_event_trace y \<Longrightarrow> 
    \<forall>x'\<in>rename_trace f x. \<forall>y'\<in>rename_trace f y.
      tttrace_to_event_trace x' = tttrace_to_event_trace y'"
proof (induct x rule:tttrace_to_event_trace.induct, simp_all)
  fix y :: "'a tttrace"
  show "[] = tttrace_to_event_trace y \<Longrightarrow> \<forall>y'\<in>rename_trace f y. [] = tttrace_to_event_trace y'"
    by (induct y rule:tttrace_to_event_trace.induct, auto)
next
  fix X and t y :: "'a tttrace"
  assume ind_hyp: "\<And>ya. tttrace_to_event_trace y = tttrace_to_event_trace ya \<Longrightarrow>
    \<forall>x'\<in>rename_trace f t. \<forall>y'\<in>rename_trace f ya. tttrace_to_event_trace x' = tttrace_to_event_trace y'"
  assume "tttrace_to_event_trace (t) = tttrace_to_event_trace y"
  then have "\<forall>x'\<in>rename_trace f t. \<forall>y'\<in>rename_trace f y. tttrace_to_event_trace x' = tttrace_to_event_trace y'"
    using ind_hyp by blast
  then show "\<forall>x'. (\<exists>s' Y. x' = [Y]\<^sub>R # s' \<and> X = lift_renaming_func f -` Y \<and> s' \<in> rename_trace f t) \<longrightarrow>
            (\<forall>y'\<in>rename_trace f y. tttrace_to_event_trace x' = tttrace_to_event_trace y')"
    by auto
next
  fix e and t y :: "'a tttrace"
  assume ind_hyp: "\<And>y. tttrace_to_event_trace t = tttrace_to_event_trace y \<Longrightarrow>
             \<forall>x'\<in>rename_trace f t. \<forall>y'\<in>rename_trace f y. tttrace_to_event_trace x' = tttrace_to_event_trace y'"
  assume "e # tttrace_to_event_trace t = tttrace_to_event_trace y"
  then show "\<forall>x'. (\<exists>s'. x' = [lift_renaming_func f e]\<^sub>E # s' \<and> s' \<in> rename_trace f t) \<longrightarrow>
            (\<forall>y'\<in>rename_trace f y. tttrace_to_event_trace x' = tttrace_to_event_trace y')"
    using ind_hyp apply - apply (induct y rule:tttrace_to_event_trace.induct, simp_all)
    by (metis tttrace_to_event_trace.simps(2), auto)
qed

lemma tracesTT_refinement_implies_constrained_tracesTT_refinement:
  assumes P_wf: "\<forall>x\<in>P. ttWF x" and TT1_P: "TT1 P" and Q_wf: "\<forall>x\<in>Q. ttWF x"
  shows "P \<sqsubseteq>\<^sub>T\<^sub>T\<^sub>T Q \<Longrightarrow> P \<sqsubseteq>\<^sub>C\<^sub>T\<^sub>T\<^sub>T Q"
  unfolding TracesRefinementTT_def ConstrainedTracesRefinesTT_def
proof auto
  fix x :: "'a timelock_event ttevent list"
  assume traces_Q_subset_traces_P: "tracesTT Q \<subseteq> tracesTT P"
  assume x_in_traces_renaming_Q: "x \<in> tracesTT (RenamingTT Q OtherEvent)"
  then obtain y z where "x = tttrace_to_event_trace y \<and> y \<in> rename_trace OtherEvent z \<and> z \<in> Q"
    unfolding tracesTT_def RenamingTT_def by auto
  then have "x = tttrace_to_event_trace y \<and> y \<in> rename_trace OtherEvent z \<and> tttrace_to_event_trace z \<in> tracesTT Q"
    unfolding tracesTT_def using Q_wf by auto
  then have "x = tttrace_to_event_trace y \<and> y \<in> rename_trace OtherEvent z \<and> tttrace_to_event_trace z \<in> tracesTT P"
    using traces_Q_subset_traces_P by auto
  then obtain w where "x = tttrace_to_event_trace y \<and> y \<in> rename_trace OtherEvent z
      \<and> tttrace_to_event_trace z = tttrace_to_event_trace w \<and> w \<in> P"
    unfolding tracesTT_def by auto
  then obtain y' where "x = tttrace_to_event_trace y \<and> y \<in> rename_trace OtherEvent z
      \<and> tttrace_to_event_trace z = tttrace_to_event_trace w \<and> w \<in> P \<and> y' \<in> rename_trace OtherEvent w"
    using rename_trace_nonempty[where f=OtherEvent] unfolding inj_def by auto
  then have "x = tttrace_to_event_trace y' \<and> y' \<in> rename_trace OtherEvent w \<and> w \<in> P"
    using same_event_trace_implies_same_renamed_event_trace by blast
  then have "x \<in> tracesTT (RenamingTT P OtherEvent)"
    unfolding tracesTT_def RenamingTT_def by auto
  then show "x \<in> tracesTT (remove_timelock_spec P)"
    using P_wf TT1_P in_traces_renaming_implies_in_traces_remove_timelock_spec by blast
qed

section \<open>Constrained tick-tock refinement\<close>

definition ConstrainedRefinesTT :: "'a ttprocess \<Rightarrow> 'a ttprocess \<Rightarrow> bool" (infix "\<sqsubseteq>\<^sub>C\<^sub>T\<^sub>T" 50) where
  "P \<sqsubseteq>\<^sub>C\<^sub>T\<^sub>T Q = (P \<sqsubseteq>\<^sub>C\<^sub>T\<^sub>T\<^sub>T Q \<and> P conf\<^sub>C Q)"

lemma tracesTT_refinement_implies_constrained_tt_refinement:
  assumes P_wf: "\<forall>x\<in>P. ttWF x" and TT1_P: "TT1 P" and Q_wf: "\<forall>x\<in>Q. ttWF x"
  shows "P \<sqsubseteq>\<^sub>C Q \<Longrightarrow> P \<sqsubseteq>\<^sub>C\<^sub>T\<^sub>T Q"
  unfolding ConstrainedRefinesTT_def refines_eq_traces_refines_and_conf
  using assms tracesTT_refinement_implies_constrained_tracesTT_refinement by auto

section \<open>Equivalent definition using a specialised function\<close>

fun add_deadline_miss_trace :: "'e tttrace \<Rightarrow> 'e tttrace set" where
  "add_deadline_miss_trace [] = {[]}" |
  "add_deadline_miss_trace ([e]\<^sub>E # \<rho>) = {[e]\<^sub>E # \<sigma> |\<sigma>. \<sigma> \<in> add_deadline_miss_trace \<rho>}" |
  "add_deadline_miss_trace ([X]\<^sub>R # \<rho>) = 
    {[X]\<^sub>R # \<sigma> |\<sigma>. Tock \<notin> X \<and> \<sigma> \<in> add_deadline_miss_trace \<rho>} \<union>
    {t. Tock \<in> X \<and> (\<exists> X'. X' \<subseteq> {e. e \<in> X \<and> e = Tock} \<and>
      (t = [[X']\<^sub>R] \<or> t = [[X']\<^sub>R, [Tock]\<^sub>E] \<or> (\<exists> \<sigma>. ttWF \<sigma> \<and> t = [[X']\<^sub>R, [Tock]\<^sub>E] @ \<sigma>)))}"

definition add_deadline_miss :: "'e ttprocess \<Rightarrow> 'e ttprocess" where
  "add_deadline_miss P = \<Union>{add_deadline_miss_trace t |t. t \<in> P }"

lemma
  assumes "\<forall>x\<in>P. ttWF x"
  shows "\<forall>x\<in>(add_deadline_miss P). ttWF x"
  using assms unfolding add_deadline_miss_def
proof auto