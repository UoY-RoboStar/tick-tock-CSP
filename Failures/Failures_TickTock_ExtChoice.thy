theory Failures_TickTock_ExtChoice

imports
  Failures_TickTock
begin

lemma ttproc2F_ExtChoiceTT_eq_ExtChoiceF:
  assumes TT0_P: "TT0 P"
      and TT0_Q: "TT0 Q"
      and TT1_P: "TT1 P" 
      and TT1_Q: "TT1 Q"
  shows "ttproc2F (P \<box>\<^sub>C Q) = (ttproc2F P) \<box>\<^sub>F (ttproc2F Q)"
  using assms unfolding ttproc2F_def ExtChoiceTT_def ExtChoiceF_def 
proof (auto)
  fix b \<rho> \<sigma> \<tau>
    assume  assm1:"Some ([], b) = tt2F (\<rho> @ \<sigma>)"
    and     assm2:"\<rho> \<in> tocks UNIV"
    and     assm3:"\<rho> @ \<sigma> \<in> P"
    and     assm4:"\<rho> @ \<tau> \<in> Q"
    and     assm5:"\<forall>\<rho>'\<in>tocks UNIV. \<rho>' \<le>\<^sub>C \<rho> @ \<sigma> \<longrightarrow> \<rho>' \<le>\<^sub>C \<rho>"
    and     assm6:"\<forall>\<rho>'\<in>tocks UNIV. \<rho>' \<le>\<^sub>C \<rho> @ \<tau> \<longrightarrow> \<rho>' \<le>\<^sub>C \<rho>"
    and     assm7:"\<forall>X. \<sigma> = [[X]\<^sub>R] \<longrightarrow> (\<exists>Y. \<tau> = [[Y]\<^sub>R] \<and> (\<forall>e. (e \<in> X) = (e \<in> Y) \<or> e = Tock))"
    and     assm8:"\<forall>X. \<tau> = [[X]\<^sub>R] \<longrightarrow> (\<exists>Y. \<sigma> = [[Y]\<^sub>R] \<and> (\<forall>e. (e \<in> X) = (e \<in> Y) \<or> e = Tock))"
    show "\<exists>y. tt2F (\<rho> @ \<sigma>) = tt2F y \<and> y \<in> Q"
    proof (cases "\<rho>")
      case Nil
      then have Some_b:"Some ([], b) = tt2F \<sigma>" 
        using assm1 by auto
      then obtain X where X:"\<sigma> = [[X]\<^sub>R]"
        using tt2F_some_exists by blast
      then obtain Y where Y:"\<tau> = [[Y]\<^sub>R]"
        using assm7 assm4 by auto
      then show ?thesis
        using tt2F_eq_eqsets_or_Tock
        by (metis X assm4 assm7 local.Nil self_append_conv2)
    next
      case (Cons a list)
      then show ?thesis using assm1 assm2 tt2F_tocks_simp by fastforce
    qed
next
  fix b \<rho> \<sigma> \<tau>
    assume  assm1:"Some ([], b) = tt2F (\<rho> @ \<tau>)"
    and     assm2:"\<rho> \<in> tocks UNIV"
    and     assm3:"\<rho> @ \<sigma> \<in> P"
    and     assm4:"\<rho> @ \<tau> \<in> Q"
    and     assm5:"\<forall>\<rho>'\<in>tocks UNIV. \<rho>' \<le>\<^sub>C \<rho> @ \<sigma> \<longrightarrow> \<rho>' \<le>\<^sub>C \<rho>"
    and     assm6:"\<forall>\<rho>'\<in>tocks UNIV. \<rho>' \<le>\<^sub>C \<rho> @ \<tau> \<longrightarrow> \<rho>' \<le>\<^sub>C \<rho>"
    and     assm7:"\<forall>X. \<sigma> = [[X]\<^sub>R] \<longrightarrow> (\<exists>Y. \<tau> = [[Y]\<^sub>R] \<and> (\<forall>e. (e \<in> X) = (e \<in> Y) \<or> e = Tock))"
    and     assm8:"\<forall>X. \<tau> = [[X]\<^sub>R] \<longrightarrow> (\<exists>Y. \<sigma> = [[Y]\<^sub>R] \<and> (\<forall>e. (e \<in> X) = (e \<in> Y) \<or> e = Tock))"
    show "\<exists>y. tt2F (\<rho> @ \<tau>) = tt2F y \<and> y \<in> P"
    proof (cases "\<rho>")
      case Nil
      then have Some_b:"Some ([], b) = tt2F \<tau>" 
        using assm1 by auto
      then obtain X where X:"\<tau> = [[X]\<^sub>R]"
        using tt2F_some_exists by blast
      then obtain Y where Y:"\<sigma> = [[Y]\<^sub>R]"
        using assm8 assm4 by auto
      then show ?thesis
        using tt2F_eq_eqsets_or_Tock
        by (metis X assm3 assm8 local.Nil self_append_conv2)
    next
      case (Cons a list)
      then show ?thesis using assm1 assm2 tt2F_tocks_simp by fastforce
    qed
next
  fix b y ya
  assume  assm1: "tt2F ya = tt2F y"
  and     assm2: "y \<in> P"
  and     assm3: "Some ([], b) = tt2F y"
  and     assm4: "ya \<in> Q"
  then obtain X where X:"y = [[X]\<^sub>R]"
    using tt2F_some_exists by blast
  then obtain Y where Y:"ya = [[Y]\<^sub>R]"
    by (metis assm1 assm3 tt2F_some_exists)

  obtain \<rho>::"'a ttobs list" where \<rho>:"\<rho> = []"
    by auto

  have p0:"\<rho>\<in>tocks UNIV"
    using \<rho> tocks.empty_in_tocks by blast

  have p1:"(\<forall>\<rho>'\<in>tocks UNIV. \<rho>' \<le>\<^sub>C \<rho> @ y \<longrightarrow> \<rho>' \<le>\<^sub>C \<rho>)"
    using \<rho> X refusal_notin_tocks tt_prefix_notfront_is_whole by force

  have p2:"(\<forall>\<rho>'\<in>tocks UNIV. \<rho>' \<le>\<^sub>C \<rho> @ ya \<longrightarrow> \<rho>' \<le>\<^sub>C \<rho>)"
    using \<rho> Y refusal_notin_tocks tt_prefix_notfront_is_whole by force

  have p3:"(\<forall>X. y = [[X]\<^sub>R] \<longrightarrow> (\<exists>Y. ya = [[Y]\<^sub>R] \<and> (\<forall>e. (e \<in> X) = (e \<in> Y) \<or> e = Tock)))"
  proof (cases "Tock \<in> X \<longleftrightarrow> Tock \<in> Y")
    case True
    then show ?thesis using tt2F_refusal_eq assm1 X Y by blast
  next
    case False
    then show ?thesis 
      by (metis (no_types, lifting) Diff_iff Y assm1 insert_Diff insert_iff list.inject tt2F_refusal_eq tt2F_refusal_without_Tock ttobs.inject(2))
  qed

  then have p4:"(\<forall>X. ya = [[X]\<^sub>R] \<longrightarrow> (\<exists>Y. y = [[Y]\<^sub>R] \<and> (\<forall>e. (e \<in> X) = (e \<in> Y) \<or> e = Tock)))"
    using X by auto

  then have "tt2F y = tt2F ya \<and> 
              \<rho>\<in>tocks UNIV \<and>
                \<rho> @ y \<in> P \<and> 
                  \<rho> @ ya \<in> Q \<and> 
                    (\<forall>\<rho>'\<in>tocks UNIV. \<rho>' \<le>\<^sub>C \<rho> @ y \<longrightarrow> \<rho>' \<le>\<^sub>C \<rho>) \<and>
                         (\<forall>\<rho>'\<in>tocks UNIV. \<rho>' \<le>\<^sub>C \<rho> @ ya \<longrightarrow> \<rho>' \<le>\<^sub>C \<rho>) \<and>
                         (\<forall>X. y = [[X]\<^sub>R] \<longrightarrow> (\<exists>Y. ya = [[Y]\<^sub>R] \<and> (\<forall>e. (e \<in> X) = (e \<in> Y) \<or> e = Tock))) \<and>
                         (\<forall>X. ya = [[X]\<^sub>R] \<longrightarrow> (\<exists>Y. y = [[Y]\<^sub>R] \<and> (\<forall>e. (e \<in> X) = (e \<in> Y) \<or> e = Tock))) \<and>
                         (ya = \<rho> @ y \<or> ya = \<rho> @ ya)"
      using \<rho> assm2 assm3 assm4 tt2F_tocks_simp tt_prefix_split p0 p1 p2 p3 p4
      by (simp add: assm1)

  then show "\<exists>ya. tt2F y = tt2F ya \<and>
            (\<exists>\<rho>\<in>tocks UNIV.
                \<exists>\<sigma>. \<rho> @ \<sigma> \<in> P \<and>
                    (\<exists>\<tau>. \<rho> @ \<tau> \<in> Q \<and>
                         (\<forall>\<rho>'\<in>tocks UNIV. \<rho>' \<le>\<^sub>C \<rho> @ \<sigma> \<longrightarrow> \<rho>' \<le>\<^sub>C \<rho>) \<and>
                         (\<forall>\<rho>'\<in>tocks UNIV. \<rho>' \<le>\<^sub>C \<rho> @ \<tau> \<longrightarrow> \<rho>' \<le>\<^sub>C \<rho>) \<and>
                         (\<forall>X. \<sigma> = [[X]\<^sub>R] \<longrightarrow> (\<exists>Y. \<tau> = [[Y]\<^sub>R] \<and> (\<forall>e. (e \<in> X) = (e \<in> Y) \<or> e = Tock))) \<and>
                         (\<forall>X. \<tau> = [[X]\<^sub>R] \<longrightarrow> (\<exists>Y. \<sigma> = [[Y]\<^sub>R] \<and> (\<forall>e. (e \<in> X) = (e \<in> Y) \<or> e = Tock))) \<and>
                         (ya = \<rho> @ \<sigma> \<or> ya = \<rho> @ \<tau>)))"
    by auto
next
  fix a b y
  assume  TT0_Q: "TT0 Q"
  and     assm1: "a \<noteq> []"
  and     assm2: "Some (a, b) = tt2F y"
  and     assm3: "y \<in> P"

  then have y_no_singleton_Ref: "\<forall>X. y \<noteq> [[X]\<^sub>R]"
    using assm1 assm2 by (cases y, auto)

  obtain \<sigma>::"'a ttobs list"  where \<sigma>:"\<sigma> = y"
    by auto

  obtain \<rho>::"'a ttobs list"  where \<rho>:"\<rho> = []"
    by auto  

  obtain \<tau>::"'a ttobs list"  where \<tau>:"\<tau> = []"
    by auto

  obtain ya where "ya = y"
    by auto

  have empty_trace_Q:"[] \<in> Q"
    using TT0_Q TT0_TT1_empty TT1_Q by blast

  have "(\<forall>\<rho>'\<in>tocks UNIV. \<rho>' \<le>\<^sub>C \<rho> @ \<sigma> \<longrightarrow> \<rho>' \<le>\<^sub>C \<rho>)"
    using \<sigma> \<rho> tocks_Some_prefix_tt2F assm2 by fastforce

  then have "tt2F y = tt2F y \<and>
            (\<rho>\<in>tocks UNIV \<and>
                 \<rho> @ \<sigma> \<in> P \<and>
                   (\<rho> @ \<tau> \<in> Q \<and>
                         (\<forall>\<rho>'\<in>tocks UNIV. \<rho>' \<le>\<^sub>C \<rho> @ \<sigma> \<longrightarrow> \<rho>' \<le>\<^sub>C \<rho>) \<and>
                         (\<forall>\<rho>'\<in>tocks UNIV. \<rho>' \<le>\<^sub>C \<rho> @ \<tau> \<longrightarrow> \<rho>' \<le>\<^sub>C \<rho>) \<and>
                         (\<forall>X. \<sigma> = [[X]\<^sub>R] \<longrightarrow> (\<exists>Y. \<tau> = [[Y]\<^sub>R] \<and> (\<forall>e. (e \<in> X) = (e \<in> Y) \<or> e = Tock))) \<and>
                         (\<forall>X. \<tau> = [[X]\<^sub>R] \<longrightarrow> (\<exists>Y. \<rho> = [[Y]\<^sub>R] \<and> (\<forall>e. (e \<in> X) = (e \<in> Y) \<or> e = Tock))) \<and>
                         (y = \<rho> @ \<sigma> \<or> y = \<rho> @ \<tau>)))"
    using \<sigma> \<tau> \<rho> y_no_singleton_Ref empty_trace_Q assm3 apply auto
    by (simp add: tocks.empty_in_tocks)
  
  then show "\<exists>ya. tt2F y = tt2F ya \<and>
            (\<exists>\<rho>\<in>tocks UNIV.
                \<exists>\<sigma>. \<rho> @ \<sigma> \<in> P \<and>
                    (\<exists>\<tau>. \<rho> @ \<tau> \<in> Q \<and>
                         (\<forall>\<rho>'\<in>tocks UNIV. \<rho>' \<le>\<^sub>C \<rho> @ \<sigma> \<longrightarrow> \<rho>' \<le>\<^sub>C \<rho>) \<and>
                         (\<forall>\<rho>'\<in>tocks UNIV. \<rho>' \<le>\<^sub>C \<rho> @ \<tau> \<longrightarrow> \<rho>' \<le>\<^sub>C \<rho>) \<and>
                         (\<forall>X. \<sigma> = [[X]\<^sub>R] \<longrightarrow> (\<exists>Y. \<tau> = [[Y]\<^sub>R] \<and> (\<forall>e. (e \<in> X) = (e \<in> Y) \<or> e = Tock))) \<and>
                         (\<forall>X. \<tau> = [[X]\<^sub>R] \<longrightarrow> (\<exists>Y. \<sigma> = [[Y]\<^sub>R] \<and> (\<forall>e. (e \<in> X) = (e \<in> Y) \<or> e = Tock))) \<and>
                         (ya = \<rho> @ \<sigma> \<or> ya = \<rho> @ \<tau>)))"
    using \<sigma> \<tau> by blast
next
  fix a b y
  assume  TT0_P: "TT0 P"
  and     assm1: "a \<noteq> []"
  and     assm2: "Some (a, b) = tt2F y"
  and     assm3: "y \<in> Q"

  then have y_no_singleton_Ref: "\<forall>X. y \<noteq> [[X]\<^sub>R]"
    using assm1 assm2 by (cases y, auto)

  obtain \<sigma>::"'a ttobs list"  where \<sigma>:"\<sigma> = []"
    by auto

  obtain \<rho>::"'a ttobs list"  where \<rho>:"\<rho> = []"
    by auto  

  obtain \<tau>::"'a ttobs list"  where \<tau>:"\<tau> = y"
    by auto

  obtain ya where ya:"ya = y"
    by auto

  have empty_trace_P:"[] \<in> P"
    using TT0_P TT0_TT1_empty TT1_P assms(3) by blast

  have "(\<forall>\<rho>'\<in>tocks UNIV. \<rho>' \<le>\<^sub>C \<rho> @ \<tau> \<longrightarrow> \<rho>' \<le>\<^sub>C \<rho>)"
    using \<tau> \<rho> tocks_Some_prefix_tt2F assm2 by fastforce

  then have "tt2F y = tt2F ya \<and>
            (\<rho>\<in>tocks UNIV \<and>
                 \<rho> @ \<sigma> \<in> P \<and>
                   (\<rho> @ \<tau> \<in> Q \<and>
                         (\<forall>\<rho>'\<in>tocks UNIV. \<rho>' \<le>\<^sub>C \<rho> @ \<sigma> \<longrightarrow> \<rho>' \<le>\<^sub>C \<rho>) \<and>
                         (\<forall>\<rho>'\<in>tocks UNIV. \<rho>' \<le>\<^sub>C \<rho> @ \<tau> \<longrightarrow> \<rho>' \<le>\<^sub>C \<rho>) \<and>
                         (\<forall>X. \<sigma> = [[X]\<^sub>R] \<longrightarrow> (\<exists>Y. \<tau> = [[Y]\<^sub>R] \<and> (\<forall>e. (e \<in> X) = (e \<in> Y) \<or> e = Tock))) \<and>
                         (\<forall>X. \<tau> = [[X]\<^sub>R] \<longrightarrow> (\<exists>Y. \<rho> = [[Y]\<^sub>R] \<and> (\<forall>e. (e \<in> X) = (e \<in> Y) \<or> e = Tock))) \<and>
                         (ya = \<rho> @ \<sigma> \<or> ya = \<rho> @ \<tau>)))"
    using \<sigma> \<tau> \<rho> ya y_no_singleton_Ref empty_trace_P assm3 apply auto
    by (simp add: tocks.empty_in_tocks)
  
  then show "\<exists>ya. tt2F y = tt2F ya \<and>
            (\<exists>\<rho>\<in>tocks UNIV.
                \<exists>\<sigma>. \<rho> @ \<sigma> \<in> P \<and>
                    (\<exists>\<tau>. \<rho> @ \<tau> \<in> Q \<and>
                         (\<forall>\<rho>'\<in>tocks UNIV. \<rho>' \<le>\<^sub>C \<rho> @ \<sigma> \<longrightarrow> \<rho>' \<le>\<^sub>C \<rho>) \<and>
                         (\<forall>\<rho>'\<in>tocks UNIV. \<rho>' \<le>\<^sub>C \<rho> @ \<tau> \<longrightarrow> \<rho>' \<le>\<^sub>C \<rho>) \<and>
                         (\<forall>X. \<sigma> = [[X]\<^sub>R] \<longrightarrow> (\<exists>Y. \<tau> = [[Y]\<^sub>R] \<and> (\<forall>e. (e \<in> X) = (e \<in> Y) \<or> e = Tock))) \<and>
                         (\<forall>X. \<tau> = [[X]\<^sub>R] \<longrightarrow> (\<exists>Y. \<sigma> = [[Y]\<^sub>R] \<and> (\<forall>e. (e \<in> X) = (e \<in> Y) \<or> e = Tock))) \<and>
                         (ya = \<rho> @ \<sigma> \<or> ya = \<rho> @ \<tau>)))"
    apply simp
    apply (rule_tac x="ya" in exI, auto)
    using \<rho> by blast+ (* Struggling unification here *)
next
  fix y
  assume  assm1: "y \<in> P"

  obtain \<sigma>::"'a ttobs list"  where \<sigma>:"\<sigma> = y"
    by auto

  obtain \<rho>::"'a ttobs list"  where \<rho>:"\<rho> = []"
    by auto  

  obtain \<tau>::"'a ttobs list"  where \<tau>:"\<tau> = []"
    by auto

  obtain ya where ya:"ya = y"
    by auto

  have empty_trace_Q:"[] \<in> Q"
    using TT0_Q TT0_TT1_empty TT1_Q assms(3) by blast

  have "(\<forall>\<rho>'\<in>tocks UNIV. \<rho>' \<le>\<^sub>C \<rho> @ \<tau> \<longrightarrow> \<rho>' \<le>\<^sub>C \<rho>)"
    using \<tau> \<rho> tocks_Some_prefix_tt2F assm1 by simp

  obtain exp where exp:"exp == tt2T y = tt2T ya \<and>
              (\<rho>\<in>tocks UNIV \<and>
                  \<rho> @ \<sigma> \<in> P \<and>
                      (\<rho> @ \<tau> \<in> Q \<and>
                           (\<forall>\<rho>'\<in>tocks UNIV. \<rho>' \<le>\<^sub>C \<rho> @ \<sigma> \<longrightarrow> \<rho>' \<le>\<^sub>C \<rho>) \<and>
                           (\<forall>\<rho>'\<in>tocks UNIV. \<rho>' \<le>\<^sub>C \<rho> @ \<tau> \<longrightarrow> \<rho>' \<le>\<^sub>C \<rho>) \<and>
                           (\<forall>X. \<sigma> = [[X]\<^sub>R] \<longrightarrow> (\<exists>Y. \<tau> = [[Y]\<^sub>R] \<and> (\<forall>e. (e \<in> X) = (e \<in> Y) \<or> e = Tock))) \<and>
                           (\<forall>X. \<tau> = [[X]\<^sub>R] \<longrightarrow> (\<exists>Y. \<sigma> = [[Y]\<^sub>R] \<and> (\<forall>e. (e \<in> X) = (e \<in> Y) \<or> e = Tock))) \<and>
                           (ya = \<rho> @ \<sigma> \<or> ya = \<rho> @ \<tau>)))"
    by auto

  show "\<exists>ya. tt2T y = tt2T ya \<and>
              (\<exists>\<rho>\<in>tocks UNIV.
                  \<exists>\<sigma>. \<rho> @ \<sigma> \<in> P \<and>
                      (\<exists>\<tau>. \<rho> @ \<tau> \<in> Q \<and>
                           (\<forall>\<rho>'\<in>tocks UNIV. \<rho>' \<le>\<^sub>C \<rho> @ \<sigma> \<longrightarrow> \<rho>' \<le>\<^sub>C \<rho>) \<and>
                           (\<forall>\<rho>'\<in>tocks UNIV. \<rho>' \<le>\<^sub>C \<rho> @ \<tau> \<longrightarrow> \<rho>' \<le>\<^sub>C \<rho>) \<and>
                           (\<forall>X. \<sigma> = [[X]\<^sub>R] \<longrightarrow> (\<exists>Y. \<tau> = [[Y]\<^sub>R] \<and> (\<forall>e. (e \<in> X) = (e \<in> Y) \<or> e = Tock))) \<and>
                           (\<forall>X. \<tau> = [[X]\<^sub>R] \<longrightarrow> (\<exists>Y. \<sigma> = [[Y]\<^sub>R] \<and> (\<forall>e. (e \<in> X) = (e \<in> Y) \<or> e = Tock))) \<and>
                           (ya = \<rho> @ \<sigma> \<or> ya = \<rho> @ \<tau>)))"
  proof (cases y rule:tt2T.cases)
    case 1
    then have "exp"
      using \<rho> \<sigma> \<tau> ya assm1 empty_trace_Q exp
      apply (simp add: tocks.empty_in_tocks)
      by (metis list.distinct(1) tt2T.simps(1) tt2T_tocks_simp tt_prefix_refl tt_prefix_split)
    then show ?thesis 
      using exp by auto
  next
    case (2 e \<sigma>2)
    then have y_no_singleton_Ref: "\<forall>X. y \<noteq> [[X]\<^sub>R]"
      using assm1 by (cases y, auto)
    then have "exp"
      using \<rho> \<sigma> \<tau> ya assm1 empty_trace_Q 2 exp
      apply (auto simp add: tocks.empty_in_tocks)
      by (metis list.distinct(1) tt2T.simps(2) tt2T_tocks_simp tt_prefix_refl tt_prefix_split)
    then show ?thesis 
      using exp by auto
  next
    case "3_1"
    then show ?thesis
      using assm1 empty_trace_Q tocks.empty_in_tocks by force
  next
    case ("3_2" va)
    then show ?thesis
      using TT0_P TT0_TT1_empty TT1_P empty_trace_Q tocks.empty_in_tocks by force
    next
      case ("3_3" vb va)
      then show ?thesis using TT0_P TT0_TT1_empty TT1_P empty_trace_Q tocks.empty_in_tocks by force
    next
      case ("3_4" vb vc)
      then show ?thesis using TT0_P TT0_TT1_empty TT1_P empty_trace_Q tocks.empty_in_tocks by force
    next
      case ("3_5" vb vc)
      then show ?thesis using TT0_P TT0_TT1_empty TT1_P empty_trace_Q tocks.empty_in_tocks by force
    next
      case ("3_6" va vb vc)
      then show ?thesis using TT0_P TT0_TT1_empty TT1_P empty_trace_Q tocks.empty_in_tocks by force
  qed
next
  fix y
  assume  assm1: "y \<in> Q"

  obtain \<sigma>::"'a ttobs list"  where \<sigma>:"\<sigma> = []"
    by auto

  obtain \<rho>::"'a ttobs list"  where \<rho>:"\<rho> = []"
    by auto  

  obtain \<tau>::"'a ttobs list"  where \<tau>:"\<tau> = y"
    by auto

  obtain ya where ya:"ya = y"
    by auto

  have empty_trace_P:"[] \<in> P"
    using TT0_P TT0_TT1_empty TT1_P assms(3) by blast

  have "(\<forall>\<rho>'\<in>tocks UNIV. \<rho>' \<le>\<^sub>C \<rho> @ \<sigma> \<longrightarrow> \<rho>' \<le>\<^sub>C \<rho>)"
    using \<sigma> \<rho> tocks_Some_prefix_tt2F assm1 by simp

  obtain exp where exp:"exp == tt2T y = tt2T ya \<and>
              (\<rho>\<in>tocks UNIV \<and>
                  \<rho> @ \<sigma> \<in> P \<and>
                      (\<rho> @ \<tau> \<in> Q \<and>
                           (\<forall>\<rho>'\<in>tocks UNIV. \<rho>' \<le>\<^sub>C \<rho> @ \<sigma> \<longrightarrow> \<rho>' \<le>\<^sub>C \<rho>) \<and>
                           (\<forall>\<rho>'\<in>tocks UNIV. \<rho>' \<le>\<^sub>C \<rho> @ \<tau> \<longrightarrow> \<rho>' \<le>\<^sub>C \<rho>) \<and>
                           (\<forall>X. \<sigma> = [[X]\<^sub>R] \<longrightarrow> (\<exists>Y. \<tau> = [[Y]\<^sub>R] \<and> (\<forall>e. (e \<in> X) = (e \<in> Y) \<or> e = Tock))) \<and>
                           (\<forall>X. \<tau> = [[X]\<^sub>R] \<longrightarrow> (\<exists>Y. \<sigma> = [[Y]\<^sub>R] \<and> (\<forall>e. (e \<in> X) = (e \<in> Y) \<or> e = Tock))) \<and>
                           (ya = \<rho> @ \<sigma> \<or> ya = \<rho> @ \<tau>)))"
    by auto

  show "\<exists>ya. tt2T y = tt2T ya \<and>
              (\<exists>\<rho>\<in>tocks UNIV.
                  \<exists>\<sigma>. \<rho> @ \<sigma> \<in> P \<and>
                      (\<exists>\<tau>. \<rho> @ \<tau> \<in> Q \<and>
                           (\<forall>\<rho>'\<in>tocks UNIV. \<rho>' \<le>\<^sub>C \<rho> @ \<sigma> \<longrightarrow> \<rho>' \<le>\<^sub>C \<rho>) \<and>
                           (\<forall>\<rho>'\<in>tocks UNIV. \<rho>' \<le>\<^sub>C \<rho> @ \<tau> \<longrightarrow> \<rho>' \<le>\<^sub>C \<rho>) \<and>
                           (\<forall>X. \<sigma> = [[X]\<^sub>R] \<longrightarrow> (\<exists>Y. \<tau> = [[Y]\<^sub>R] \<and> (\<forall>e. (e \<in> X) = (e \<in> Y) \<or> e = Tock))) \<and>
                           (\<forall>X. \<tau> = [[X]\<^sub>R] \<longrightarrow> (\<exists>Y. \<sigma> = [[Y]\<^sub>R] \<and> (\<forall>e. (e \<in> X) = (e \<in> Y) \<or> e = Tock))) \<and>
                           (ya = \<rho> @ \<sigma> \<or> ya = \<rho> @ \<tau>)))"
  proof (cases y rule:tt2T.cases)
    case 1
    then have "exp"
      using \<rho> \<sigma> \<tau> ya assm1 empty_trace_P exp
      apply (simp add: tocks.empty_in_tocks)
      by (metis list.distinct(1) tt2T.simps(1) tt2T_tocks_simp tt_prefix_refl tt_prefix_split)
    then show ?thesis 
      using exp by auto
  next
    case (2 e \<sigma>2)
    then have y_no_singleton_Ref: "\<forall>X. y \<noteq> [[X]\<^sub>R]"
      using assm1 by (cases y, auto)
    then have "exp"
      using \<rho> \<sigma> \<tau> ya assm1 empty_trace_P 2 exp
      apply (auto simp add: tocks.empty_in_tocks)
      by (metis list.distinct(1) tt2T.simps(2) tt2T_tocks_simp tt_prefix_refl tt_prefix_split)
    then show ?thesis 
      using exp by auto
  next
    case "3_1"
    then show ?thesis
      using assm1 empty_trace_P tocks.empty_in_tocks by force
  next
    case ("3_2" va)
    then show ?thesis
      using TT0_Q TT0_TT1_empty TT1_Q empty_trace_P tocks.empty_in_tocks by force
    next
      case ("3_3" vb va)
      then show ?thesis using TT0_Q TT0_TT1_empty TT1_Q empty_trace_P tocks.empty_in_tocks by force
    next
      case ("3_4" vb vc)
      then show ?thesis using TT0_Q TT0_TT1_empty TT1_Q empty_trace_P tocks.empty_in_tocks by force
    next
      case ("3_5" vb vc)
      then show ?thesis using TT0_Q TT0_TT1_empty TT1_Q empty_trace_P tocks.empty_in_tocks by force
    next
      case ("3_6" va vb vc)
      then show ?thesis using TT0_Q TT0_TT1_empty TT1_Q empty_trace_P tocks.empty_in_tocks by force
    qed
  qed

end