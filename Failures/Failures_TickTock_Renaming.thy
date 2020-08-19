theory Failures_TickTock_Renaming
  imports Failures_TickTock
begin

lemma inv_map_evt_tick: "inv (map_evt f) tick = tick"
  unfolding inv_def by (rule some_equality, auto, case_tac x, auto)

lemma ttevt2F_map_evt:
  "ttevt2F (map_evt f x) = lift_renaming_func f (ttevt2F x)"
  by (metis evt.exhaust evt.simps(8) evt.simps(9) lift_renaming_func.simps(1) lift_renaming_func.simps(3) ttevt2F.simps(1) ttevt2F.simps(2))

lemma ttproc2F_ExtChoiceTT_eq_ExtChoiceF:
  assumes P_wf: "TTwf P" and Q_wf: "TTwf Q" and TT1_P: "TT1 P" and TT1_Q: "TT1 Q"
  shows "ttproc2F (RenamingTT P f) = RenamingF (ttproc2F P) f"
  unfolding RenamingTT_def RenamingF_def ttproc2F_def
proof auto
  fix a b y x
  assume case_assms: "Some (a, b) = tt2F y" "x \<in> P" "y \<in> rename_trace f x"

  thm map_evt_def

  have "\<And>a b y. Some (a, b) = tt2F y \<Longrightarrow> y \<in> rename_trace f x \<Longrightarrow>
    \<exists>s. map (map_evt f) s = a \<and> (\<exists>y. Some (s, map_evt f -` b) = tt2F y \<and> y \<lesssim>\<^sub>C x)"
  proof (induct x rule:ttWF.induct, auto)
    fix Y
    show "\<exists>y. Some ([], {y. ttevt2F (map_evt f y) \<in> Y}) = tt2F y \<and> y \<lesssim>\<^sub>C [[lift_renaming_func f -` Y]\<^sub>R]"
      by (rule_tac x="[[lift_renaming_func f -` Y]\<^sub>R]" in exI, auto, (case_tac x, auto)+)
  next
    fix e \<sigma> a b s'
    assume ind_hyp: "\<And>a b y. Some (a, b) = tt2F y \<Longrightarrow> y \<in> rename_trace f \<sigma> \<Longrightarrow>
      \<exists>s. map (map_evt f) s = a \<and> (\<exists>y. Some (s, map_evt f -` b) = tt2F y \<and> y \<lesssim>\<^sub>C \<sigma>)"
    assume "Some (a, b) = (case tt2F s' of None \<Rightarrow> None | Some fl \<Rightarrow> Some (evt (f e) # fst fl, snd fl))" "s' \<in> rename_trace f \<sigma>"
    then have case_assms2: "Some (a, b) = tt2F ([Event (f e)]\<^sub>E # s')" "s' \<in> rename_trace f \<sigma>"
      by (cases "tt2F s'", auto)

    obtain a' where a'_assms: "a = evt (f e) # a' \<and> Some (a', b) = tt2F s'"
      using case_assms2(1) by (cases a, auto, (cases "tt2F s'", auto)+)

    obtain s y where s_y_assms: "map (map_evt f) s = a' \<and> Some (s, map_evt f -` b) = tt2F y \<and> y \<lesssim>\<^sub>C \<sigma>"
      using a'_assms case_assms2(2) ind_hyp by blast
    then show "\<exists>s. map (map_evt f) s = a \<and> (\<exists>y. Some (s, map_evt f -` b) = tt2F y \<and> y \<lesssim>\<^sub>C [Event e]\<^sub>E # \<sigma>)"
      using a'_assms by (rule_tac x="evt e # s" in exI, auto, rule_tac x="[Event e]\<^sub>E # y" in exI, auto, cases "tt2F y", auto)
  qed
  then have "\<exists>s. map (map_evt f) s = a \<and> (\<exists>y. Some (s, map_evt f -` b) = tt2F y \<and> y \<lesssim>\<^sub>C x)"
    using case_assms(1) case_assms(3) by blast
  then show "\<exists>s. map (map_evt f) s = a \<and> (\<exists>y. Some (s, map_evt f -` b) = tt2F y \<and> y \<in> P)"
    using TT1_P case_assms(2) unfolding TT1_def by blast
next
  fix b s y
  assume case_assms: "Some (s, map_evt f -` b) = tt2F y" "y \<in> P"

  have "\<And>b s. Some (s, map_evt f -` b) = tt2F y \<Longrightarrow>  \<exists>y'. Some (map (map_evt f) s, b) = tt2F y' \<and> (\<exists>x. y' \<in> rename_trace f x \<and> x \<lesssim>\<^sub>C y)"
  proof (induct y rule:ttWF.induct, auto)
    fix X b
    assume case_assm2: "map_evt f -` b = {x. ttevt2F x \<in> X}"
    then obtain Y where Y_assm: "b = {x. ttevt2F x \<in> Y}"
      unfolding vimage_def by (smt Some_tt2F_concat_refusal Some_tt2F_set)
    then show "\<exists>y'. Some ([], b) = tt2F y' \<and> (\<exists>x. y' \<in> rename_trace f x \<and> x \<lesssim>\<^sub>C [[X]\<^sub>R])"
      apply (rule_tac x="[[{e\<in>Y. e \<noteq> Tock}]\<^sub>R]" in exI, auto)
      apply (metis evt.exhaust ttevent.simps(3) ttevent.simps(7) ttevt2F.simps(1) ttevt2F.simps(2))
      apply (rule_tac x="[[{e\<in>X. e \<noteq> Tock}]\<^sub>R]" in exI, auto)
      apply (case_tac x, auto)
      apply (metis Y_assm case_assm2 evt.simps(9) mem_Collect_eq ttevt2F.simps(1) vimage_eq)
      apply (metis case_assm2 evt.simps(8) mem_Collect_eq ttevt2F.simps(2) vimage_def)
      using lift_renaming_func.elims apply blast
      apply (case_tac x, auto)
      apply (metis (mono_tags, lifting) Collect_mem_eq Collect_mono_iff Y_assm case_assm2 evt.simps(9) mem_Collect_eq ttevt2F.simps(1) vimage_def)
      by (metis case_assm2 evt.simps(8) mem_Collect_eq ttevt2F.simps(2) vimage_def)
  next
    fix e \<sigma> b s
    assume ind_hyp: "\<And>b s. Some (s, map_evt f -` b) = tt2F \<sigma> \<Longrightarrow>
               \<exists>y'. Some (map (map_evt f) s, b) = tt2F y' \<and> (\<exists>x. y' \<in> rename_trace f x \<and> x \<lesssim>\<^sub>C \<sigma>)"
    assume "Some (s, map_evt f -` b) = (case tt2F \<sigma> of None \<Rightarrow> None | Some fl \<Rightarrow> Some (evt e # fst fl, snd fl))"
    then obtain s' where s'_assms: "tt2F \<sigma> = Some (s', map_evt f -` b) \<and> s = evt e # s'"
      by (cases "tt2F \<sigma>", auto)

    obtain y' x where "Some (map (map_evt f) s', b) = tt2F y' \<and> y' \<in> rename_trace f x \<and> x \<lesssim>\<^sub>C \<sigma>"
      using ind_hyp s'_assms by presburger
    then show "\<exists>y'. Some (map (map_evt f) s, b) = tt2F y' \<and> (\<exists>x. y' \<in> rename_trace f x \<and> x \<lesssim>\<^sub>C [Event e]\<^sub>E # \<sigma>)"
      apply (rule_tac x="[Event (f e)]\<^sub>E # y'" in exI, auto)
      apply (metis (mono_tags, lifting) evt.simps(9) fst_conv list.simps(9) option.simps(5) s'_assms snd_conv)
      by (rule_tac x="[Event e]\<^sub>E # x" in exI, auto)
  qed
  then have "\<exists>y'. Some (map (map_evt f) s, b) = tt2F y' \<and> (\<exists>x. y' \<in> rename_trace f x \<and> x \<lesssim>\<^sub>C y)"
    using case_assms(1) by blast
  then show "\<exists>y. Some (map (map_evt f) s, b) = tt2F y \<and> (\<exists>x\<in>P. y \<in> rename_trace f x)"
    using TT1_P TT1_def case_assms(2) by blast
next
  fix y xa
  assume case_assms: "xa \<in> P" "y \<in> rename_trace f xa"

  have "\<And>y. ttWF xa \<Longrightarrow> y \<in> rename_trace f xa \<Longrightarrow> \<exists>s. map (map_evt f) s = tt2T y \<and> (\<exists>y'. s = tt2T y' \<and> y' \<lesssim>\<^sub>C xa)"
  proof (induct xa rule:ttWF.induct, auto)
    show "\<exists>y'. [] = tt2T y' \<and> y' \<lesssim>\<^sub>C []"
      by (rule_tac x="[]" in exI, auto)
  next
    fix Y
    show "\<exists>y'. [] = tt2T y' \<and> y' \<lesssim>\<^sub>C [[lift_renaming_func f -` Y]\<^sub>R]"
      by (rule_tac x="[]" in exI, auto)
  next
    show "\<exists>s. map (map_evt f) s = [tick] \<and> (\<exists>y'. s = tt2T y' \<and> y' \<lesssim>\<^sub>C [[Tick]\<^sub>E])"
      by (rule_tac x="[tick]" in exI, auto, rule_tac x="[[Tick]\<^sub>E]" in exI, auto)
  next
    fix e \<sigma> s'
    assume ind_hyp: "\<And>y. y \<in> rename_trace f \<sigma> \<Longrightarrow> \<exists>s. map (map_evt f) s = tt2T y \<and> (\<exists>y'. s = tt2T y' \<and> y' \<lesssim>\<^sub>C \<sigma>)"
    assume case_assms2: "ttWF \<sigma>" "s' \<in> rename_trace f \<sigma>"
    then obtain s y' where "map (map_evt f) s = tt2T s' \<and> s = tt2T y' \<and> y' \<lesssim>\<^sub>C \<sigma>"
      using ind_hyp by blast
    then show "\<exists>s. map (map_evt f) s = evt (f e) # tt2T s' \<and> (\<exists>y'. s = tt2T y' \<and> y' \<lesssim>\<^sub>C [Event e]\<^sub>E # \<sigma>)"
      by (rule_tac x="evt e # s" in exI, auto, rule_tac x="[Event e]\<^sub>E # y'" in exI, auto)
  next
    fix \<sigma> Y s'a
    show "\<exists>y'. [] = tt2T y' \<and> y' \<lesssim>\<^sub>C [lift_renaming_func f -` Y]\<^sub>R # [Tock]\<^sub>E # \<sigma>"
      by (rule_tac x="[]" in exI, auto)
  qed
  then have "\<exists>s. map (map_evt f) s = tt2T y \<and> (\<exists>y'. s = tt2T y' \<and> y' \<lesssim>\<^sub>C xa)"
    using P_wf TTwf_def case_assms(1) case_assms(2) by blast
  then show "\<exists>s. map (map_evt f) s = tt2T y \<and> (\<exists>y. s = tt2T y \<and> y \<in> P)"
    using TT1_P TT1_def case_assms(1) by blast
next
  fix y
  assume case_assms: "y \<in> P"

  have "ttWF y \<Longrightarrow> \<exists>ya. map (map_evt f) (tt2T y) = tt2T ya \<and> (\<exists>x. ya \<in> rename_trace f x \<and> x \<lesssim>\<^sub>C y)"
  proof (induct y rule:ttWF.induct, auto)
    show "\<exists>ya. [] = tt2T ya \<and> (\<exists>x. ya \<in> rename_trace f x \<and> x \<lesssim>\<^sub>C [])"
      by (rule_tac x="[]" in exI, auto, rule_tac x="[]" in exI, auto)
  next
    fix X
    show "\<exists>ya. [] = tt2T ya \<and> (\<exists>x. ya \<in> rename_trace f x \<and> x \<lesssim>\<^sub>C [[X]\<^sub>R])"
      by (rule_tac x="[]" in exI, auto, rule_tac x="[]" in exI, auto)
  next
    show "\<exists>ya. [tick] = tt2T ya \<and> (\<exists>x. ya \<in> rename_trace f x \<and> x \<lesssim>\<^sub>C [[Tick]\<^sub>E])"
      by (rule_tac x="[[Tick]\<^sub>E]" in exI, auto, rule_tac x="[[Tick]\<^sub>E]" in exI, auto)
  next
    fix e \<sigma> ya x
    assume "ttWF \<sigma>" "map (map_evt f) (tt2T \<sigma>) = tt2T ya" "ya \<in> rename_trace f x" "x \<lesssim>\<^sub>C \<sigma>"
    then show "\<exists>yaa. evt (f e) # tt2T ya = tt2T yaa \<and> (\<exists>x. yaa \<in> rename_trace f x \<and> x \<lesssim>\<^sub>C [Event e]\<^sub>E # \<sigma>)"
      by (rule_tac x="[Event (f e)]\<^sub>E # ya" in exI, auto, rule_tac x="[Event e]\<^sub>E # x" in exI, auto)
  next
    fix X and ya :: "'c tttrace" and x \<sigma> :: "'a tttrace"
    assume "ttWF \<sigma>" "map (map_evt f) (tt2T \<sigma>) = tt2T ya" "ya \<in> rename_trace f x" "x \<lesssim>\<^sub>C \<sigma>"
    then show "\<exists>ya. [] = tt2T ya \<and> (\<exists>x. ya \<in> rename_trace f x \<and> x \<lesssim>\<^sub>C [X]\<^sub>R # [Tock]\<^sub>E # \<sigma>)"
      by (rule_tac x="[]" in exI, auto, rule_tac x="[]" in exI, auto)
  qed
  then show "\<exists>ya. map (map_evt f) (tt2T y) = tt2T ya \<and> (\<exists>x\<in>P. ya \<in> rename_trace f x)"
    using P_wf TT1_P TT1_def TTwf_def case_assms by blast
qed

end