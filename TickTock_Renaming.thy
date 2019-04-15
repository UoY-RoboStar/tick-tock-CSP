theory TickTock_Renaming
  imports TickTock_Core
begin

fun lift_renaming_func :: "('a \<Rightarrow> 'b) \<Rightarrow> ('a ttevent \<Rightarrow> 'b ttevent)" where
  "lift_renaming_func f (Event e) = Event (f e)" |
  "lift_renaming_func f Tock = Tock" |
  "lift_renaming_func f Tick = Tick"

lemma lift_renaming_func_mono: "X \<subseteq> Y \<Longrightarrow> {lift_renaming_func f e |e. e \<in> X} \<subseteq> {lift_renaming_func f e |e. e \<in> Y}"
  by auto

lemma lift_renaming_func_subset: "Xa \<subseteq> {lift_renaming_func f e |e. e \<in> X} \<Longrightarrow> \<exists>Y. Xa = {lift_renaming_func f e |e. e \<in> Y} \<and> Y \<subseteq> X"
  by (rule_tac x="{e. lift_renaming_func f e \<in> Xa \<and> e \<in> X}" in exI, auto)

lemma lift_renaming_func_vimage_insert_Tick: "lift_renaming_func f -` (insert Tick Y) = insert Tick (lift_renaming_func f -` Y)"
  using lift_renaming_func.elims by blast

fun rename_trace :: "('a \<Rightarrow> 'b) \<Rightarrow> 'a ttobs list \<Rightarrow> 'b ttobs list set" where
  "rename_trace f [] = {[]}" |
  "rename_trace f ([e]\<^sub>E # t) = {s. \<exists>s'. s = [lift_renaming_func f e]\<^sub>E # s' \<and> s' \<in> rename_trace f t}" |
  "rename_trace f ([X]\<^sub>R # t) = {s. \<exists>s' Y. s = [Y]\<^sub>R # s' \<and> X = (lift_renaming_func f) -` Y \<and> s' \<in> rename_trace f t}"

lemma rename_trace_ttWF: "ttWF t \<Longrightarrow> \<forall>s\<in>(rename_trace f t). ttWF s"
  by (induct t rule:ttWF.induct, auto)
   
definition RenamingTT :: "'a ttobs list set \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> 'b ttobs list set" where
  "RenamingTT P f = {t. \<exists>x\<in>P. t \<in> rename_trace f x}"

lemma RenamingTT_wf: 
  assumes "\<forall>x\<in>P. ttWF x"
  shows "\<forall>x\<in>RenamingTT P f. ttWF x"
  unfolding RenamingTT_def using assms rename_trace_ttWF by auto

lemma TT0_Renaming:
  assumes "TT1 P" "TT0 P"
  shows "TT0 (RenamingTT P f)"
  unfolding RenamingTT_def TT0_def using TT0_TT1_empty assms by force

lemma TT1_Renaming:
  assumes "TT1 P"
  shows "TT1 (RenamingTT P f)"
  unfolding RenamingTT_def TT1_def
proof auto
  fix \<rho> \<sigma> x
  have "\<And>P \<rho> \<sigma>. TT1 P \<Longrightarrow> \<rho> \<lesssim>\<^sub>C \<sigma> \<Longrightarrow> x \<in> P \<Longrightarrow> \<sigma> \<in> rename_trace f x \<Longrightarrow> \<exists>x\<in>P. \<rho> \<in> rename_trace f x"
  proof (induct f x rule:rename_trace.induct, auto)
    fix f P \<rho>                                
    show "\<rho> \<lesssim>\<^sub>C [] \<Longrightarrow> [] \<in> P \<Longrightarrow> \<exists>x\<in>P. \<rho> \<in> rename_trace f x"
      using tt_prefix_subset_antisym by force
  next
    fix f e t P \<rho> s'
    assume ind_hyp: "\<And>P \<rho> \<sigma>. TT1 P \<Longrightarrow> \<rho> \<lesssim>\<^sub>C \<sigma> \<Longrightarrow> t \<in> P \<Longrightarrow> \<sigma> \<in> rename_trace f t \<Longrightarrow> \<exists>x\<in>P. \<rho> \<in> rename_trace f x"
    assume case_assms: "TT1 P" "\<rho> \<lesssim>\<^sub>C [lift_renaming_func f e]\<^sub>E # s'" "[e]\<^sub>E # t \<in> P" "s' \<in> rename_trace f t"
    have "\<rho> = [] \<or> (\<exists> s. \<rho> = [lift_renaming_func f e]\<^sub>E # s)"
      using case_assms(2) by (cases \<rho> rule:ttWF.cases, auto)
    then show "\<exists>x\<in>P. \<rho> \<in> rename_trace f x"
    proof auto
      show "\<rho> = [] \<Longrightarrow> \<exists>x\<in>P. [] \<in> rename_trace f x"
        using TT0_TT1_empty TT0_def case_assms(1) case_assms(3) by (rule_tac x="[]" in bexI, auto)
    next
      fix s
      assume case_assm2: "\<rho> = [lift_renaming_func f e]\<^sub>E # s"
      have 1: "TT1 {x. [e]\<^sub>E # x \<in> P}"
        using case_assms(1) tt_prefix_subset.simps(3) unfolding TT1_def by blast
      have 2: "s \<lesssim>\<^sub>C s'"
        using case_assm2 case_assms(2) by auto
      have "\<exists>x\<in>{x. [e]\<^sub>E # x \<in> P}. s \<in> rename_trace f x"
        using 1 2 case_assms ind_hyp[where P="{x. [e]\<^sub>E # x \<in> P}", where \<rho>=s] by auto
      then show "\<exists>x\<in>P. [lift_renaming_func f e]\<^sub>E # s \<in> rename_trace f x"
        by (auto, rule_tac x="[e]\<^sub>E # x" in bexI, auto)
    qed
  next
    fix f t P \<rho> s' Y
    assume ind_hyp: "\<And>P \<rho> \<sigma>. TT1 P \<Longrightarrow> \<rho> \<lesssim>\<^sub>C \<sigma> \<Longrightarrow> t \<in> P \<Longrightarrow> \<sigma> \<in> rename_trace f t \<Longrightarrow> \<exists>x\<in>P. \<rho> \<in> rename_trace f x"
    assume case_assms: "TT1 P" "\<rho> \<lesssim>\<^sub>C [Y]\<^sub>R # s'" "[lift_renaming_func f -` Y]\<^sub>R # t \<in> P" "s' \<in> rename_trace f t"
    have "\<rho> = [] \<or> (\<exists> s Z. \<rho> = [Z]\<^sub>R # s \<and> Z \<subseteq> Y)"
      using case_assms(2) by (cases \<rho> rule:ttWF.cases, auto)
    then show "\<exists>x\<in>P. \<rho> \<in> rename_trace f x"
    proof auto
      show "\<rho> = [] \<Longrightarrow> \<exists>x\<in>P. [] \<in> rename_trace f x"
        using TT0_TT1_empty TT0_def case_assms by (rule_tac x="[]" in bexI, auto)
    next
      fix s Z
      assume case_assms2: "Z \<subseteq> Y" "\<rho> = [Z]\<^sub>R # s"
      thm ind_hyp[where P="{x. [lift_renaming_func f -` Z]\<^sub>R # x \<in> P}", where \<rho>=s, where \<sigma>=s']
      have 1: "TT1 {x. [lift_renaming_func f -` Z]\<^sub>R # x \<in> P}"
        using case_assms(1) tt_prefix_subset.simps(2) unfolding TT1_def by blast
      have 2: "s \<lesssim>\<^sub>C s'"
        using case_assms2 case_assms(2) by auto
      have "[lift_renaming_func f -` Z]\<^sub>R # t \<lesssim>\<^sub>C [lift_renaming_func f -` Y]\<^sub>R # t"
        by (simp add: case_assms2(1) tt_prefix_subset_refl vimage_mono)   
      then have 3: "t \<in> {x. [lift_renaming_func f -` Z]\<^sub>R # x \<in> P}"
        using case_assms(1) case_assms(3) unfolding TT1_def by fastforce
     have "\<exists>x\<in>{x. [lift_renaming_func f -` Z]\<^sub>R # x \<in> P}. s \<in> rename_trace f x"
        using 1 2 3 case_assms ind_hyp[where P="{x. [lift_renaming_func f -` Z]\<^sub>R # x \<in> P}", where \<rho>=s] by auto
      then show "\<exists>x\<in>P. [Z]\<^sub>R # s \<in> rename_trace f x"
        using case_assms(4) case_assms2(1) by (auto, rule_tac x="[lift_renaming_func f -` Z]\<^sub>R # x" in bexI, auto)
    qed
  qed
  then show "\<rho> \<lesssim>\<^sub>C \<sigma> \<Longrightarrow> x \<in> P \<Longrightarrow> \<sigma> \<in> rename_trace f x \<Longrightarrow> \<exists>x\<in>P. \<rho> \<in> rename_trace f x"
    using assms by auto
qed

lemma TT2s_Renaming:
  assumes "TT2s P"
  shows "TT2s (RenamingTT P f)"
  unfolding TT2s_def RenamingTT_def
proof (auto)
  fix \<rho> \<sigma> X Y x
  have "\<And>P \<rho>. Y \<inter> {e. e \<noteq> Tock \<and> (\<exists>x\<in>P. \<rho> @ [[e]\<^sub>E] \<in> rename_trace f x) \<or> e = Tock \<and> (\<exists>x\<in>P. \<rho> @ [[X]\<^sub>R, [e]\<^sub>E] \<in> rename_trace f x)} = {} \<Longrightarrow>
       TT2s P \<Longrightarrow> x \<in> P \<Longrightarrow> \<rho> @ [X]\<^sub>R # \<sigma> \<in> rename_trace f x \<Longrightarrow> \<exists>x\<in>P. \<rho> @ [X \<union> Y]\<^sub>R # \<sigma> \<in> rename_trace f x"
  proof (induct f x rule:rename_trace.induct, simp_all)
    fix f e t P \<rho>
    assume ind_hyp: "\<And>P \<rho>. Y \<inter> {e. e \<noteq> Tock \<and> (\<exists>x\<in>P. \<rho> @ [[e]\<^sub>E] \<in> rename_trace f x) \<or> e = Tock \<and> (\<exists>x\<in>P. \<rho> @ [[X]\<^sub>R, [e]\<^sub>E] \<in> rename_trace f x)} = {} \<Longrightarrow>
               TT2s P \<Longrightarrow> t \<in> P \<Longrightarrow> \<rho> @ [X]\<^sub>R # \<sigma> \<in> rename_trace f t \<Longrightarrow> \<exists>x\<in>P. \<rho> @ [X \<union> Y]\<^sub>R # \<sigma> \<in> rename_trace f x"
    assume case_assms: "Y \<inter> {e. e \<noteq> Tock \<and> (\<exists>x\<in>P. \<rho> @ [[e]\<^sub>E] \<in> rename_trace f x) \<or> e = Tock \<and> (\<exists>x\<in>P. \<rho> @ [[X]\<^sub>R, [e]\<^sub>E] \<in> rename_trace f x)} = {}"
       "TT2s P" "[e]\<^sub>E # t \<in> P" "\<exists>s'. \<rho> @ [X]\<^sub>R # \<sigma> = [lift_renaming_func f e]\<^sub>E # s' \<and> s' \<in> rename_trace f t"
    obtain \<rho>' where \<rho>_def: "\<rho> = [lift_renaming_func f e]\<^sub>E # \<rho>'"
      using case_assms(4) by (cases \<rho> rule:ttWF.cases, auto)
    have 1: "TT2s {x. [e]\<^sub>E # x \<in> P}"
      using case_assms(2) unfolding TT2s_def by (auto, erule_tac x="[e]\<^sub>E # \<rho>" in allE, auto)
    have "{ea. ea \<noteq> Tock \<and> (\<exists>x\<in>{x. [e]\<^sub>E # x \<in> P}. \<rho>' @ [[ea]\<^sub>E] \<in> rename_trace f x) \<or> ea = Tock \<and> (\<exists>x\<in>{x. [e]\<^sub>E # x \<in> P}. \<rho>' @ [[X]\<^sub>R, [ea]\<^sub>E] \<in> rename_trace f x)}
      \<subseteq> {e. e \<noteq> Tock \<and> (\<exists>x\<in>P. \<rho> @ [[e]\<^sub>E] \<in> rename_trace f x) \<or> e = Tock \<and> (\<exists>x\<in>P. \<rho> @ [[X]\<^sub>R, [e]\<^sub>E] \<in> rename_trace f x)}"
      using \<rho>_def by force
    then have 2: "Y \<inter> {ea. ea \<noteq> Tock \<and> (\<exists>x\<in>{x. [e]\<^sub>E # x \<in> P}. \<rho>' @ [[ea]\<^sub>E] \<in> rename_trace f x) \<or> ea = Tock \<and> (\<exists>x\<in>{x. [e]\<^sub>E # x \<in> P}. \<rho>' @ [[X]\<^sub>R, [ea]\<^sub>E] \<in> rename_trace f x)} = {}"
      using case_assms(1) by auto
    have 3: "\<rho>' @ [X]\<^sub>R # \<sigma> \<in> rename_trace f t"
      using \<rho>_def case_assms(4) by auto
    have "\<exists>x\<in>{x. [e]\<^sub>E # x \<in> P}. \<rho>' @ [X \<union> Y]\<^sub>R # \<sigma> \<in> rename_trace f x"
      using case_assms \<rho>_def 1 2 3 ind_hyp[where P="{x. [e]\<^sub>E # x \<in> P}", where \<rho>=\<rho>'] by auto
    then show "\<exists>x\<in>P. \<rho> @ [X \<union> Y]\<^sub>R # \<sigma> \<in> rename_trace f x"
      using \<rho>_def by force
  next
    fix f Xa t P \<rho>
    assume ind_hyp: "\<And>P \<rho>. Y \<inter> {e. e \<noteq> Tock \<and> (\<exists>x\<in>P. \<rho> @ [[e]\<^sub>E] \<in> rename_trace f x) \<or> e = Tock \<and> (\<exists>x\<in>P. \<rho> @ [[X]\<^sub>R, [e]\<^sub>E] \<in> rename_trace f x)} = {} \<Longrightarrow>
               TT2s P \<Longrightarrow> t \<in> P \<Longrightarrow> \<rho> @ [X]\<^sub>R # \<sigma> \<in> rename_trace f t \<Longrightarrow> \<exists>x\<in>P. \<rho> @ [X \<union> Y]\<^sub>R # \<sigma> \<in> rename_trace f x"
    assume case_assms: "Y \<inter> {e. e \<noteq> Tock \<and> (\<exists>x\<in>P. \<rho> @ [[e]\<^sub>E] \<in> rename_trace f x) \<or> e = Tock \<and> (\<exists>x\<in>P. \<rho> @ [[X]\<^sub>R, [e]\<^sub>E] \<in> rename_trace f x)} = {}"
      "TT2s P" "[Xa]\<^sub>R # t \<in> P" "\<exists>s' Y. \<rho> @ [X]\<^sub>R # \<sigma> = [Y]\<^sub>R # s' \<and> Xa = lift_renaming_func f -` Y \<and> s' \<in> rename_trace f t"
    have 1: "TT2s {x. [Xa]\<^sub>R # x \<in> P}"
      using case_assms(2) unfolding TT2s_def by (auto, erule_tac x="[Xa]\<^sub>R # \<rho>" in allE, auto)
    obtain Z s' where Z_assms: "\<rho> @ [X]\<^sub>R # \<sigma> = [Z]\<^sub>R # s' \<and> Xa = lift_renaming_func f -` Z \<and> s' \<in> rename_trace f t"
      using case_assms(4) by auto
    then have "(\<exists>\<rho>'. \<rho> = [Z]\<^sub>R # \<rho>') \<or> (X = Z \<and> \<rho> = [])"
      by (cases \<rho> rule:ttWF.cases, auto)
    then show "\<exists>x\<in>P. \<rho> @ [X \<union> Y]\<^sub>R # \<sigma> \<in> rename_trace f x"
    proof auto
      fix \<rho>''
      assume case_assm2: "\<rho> = [Z]\<^sub>R # \<rho>''"
      have 1: "TT2s {x. [Xa]\<^sub>R # x \<in> P}"
        using case_assms(2) unfolding TT2s_def by (auto, erule_tac x="[Xa]\<^sub>R # \<rho>" in allE, auto)
      have "{e. e \<noteq> Tock \<and> (\<exists>x\<in>{x. [Xa]\<^sub>R # x \<in> P}. \<rho>'' @ [[e]\<^sub>E] \<in> rename_trace f x) \<or> e = Tock \<and> (\<exists>x\<in>{x. [Xa]\<^sub>R # x \<in> P}. \<rho>'' @ [[X]\<^sub>R, [e]\<^sub>E] \<in> rename_trace f x)}
        \<subseteq> {e. e \<noteq> Tock \<and> (\<exists>x\<in>P. \<rho> @ [[e]\<^sub>E] \<in> rename_trace f x) \<or> e = Tock \<and> (\<exists>x\<in>P. \<rho> @ [[X]\<^sub>R, [e]\<^sub>E] \<in> rename_trace f x)}"
        using case_assm2 Z_assms by (auto, (smt CollectI Z_assms case_assms(4) list.inject rename_trace.simps(3))+)
      then have 2: "Y \<inter> {e. e \<noteq> Tock \<and> (\<exists>x\<in>{x. [Xa]\<^sub>R # x \<in> P}. \<rho>'' @ [[e]\<^sub>E] \<in> rename_trace f x) \<or> e = Tock \<and> (\<exists>x\<in>{x. [Xa]\<^sub>R # x \<in> P}. \<rho>'' @ [[X]\<^sub>R, [e]\<^sub>E] \<in> rename_trace f x)} = {}"
        using case_assms(1) by auto
      have 3: "\<rho>'' @ [X]\<^sub>R # \<sigma> \<in> rename_trace f t"
        using case_assm2 case_assms(4) by auto
      have "\<exists>x\<in>{x. [Xa]\<^sub>R # x \<in> P}. \<rho>'' @ [X \<union> Y]\<^sub>R # \<sigma> \<in> rename_trace f x"
        using case_assms case_assm2 1 2 3 ind_hyp[where P="{x. [Xa]\<^sub>R # x \<in> P}", where \<rho>=\<rho>''] by auto
      then show "\<exists>x\<in>P. [Z]\<^sub>R # \<rho>'' @ [X \<union> Y]\<^sub>R # \<sigma> \<in> rename_trace f x"
        using case_assm2 Z_assms apply (auto)
        by (smt CollectI Z_assms case_assms(4) list.inject rename_trace.simps(3))
    next
      assume case_assms2: "\<rho> = []" "X = Z"
      obtain Y' where Y'_def: "Y' = lift_renaming_func f -` Y"
        by auto
      have "Y' \<inter> {e. e \<noteq> Tock \<and> [[e]\<^sub>E] \<in> P \<or> e = Tock \<and> [[Xa]\<^sub>R, [e]\<^sub>E] \<in> P} = {}"
      proof auto
        fix x
        assume case_assms3: "x \<in> Y'" "x \<noteq> Tock" "[[x]\<^sub>E] \<in> P"
        have "lift_renaming_func f x \<in> Y"
          using case_assms3 Y'_def by auto
        then have "lift_renaming_func f x \<notin> {e. e \<noteq> Tock \<and> (\<exists>x\<in>P. \<rho> @ [[e]\<^sub>E] \<in> rename_trace f x) \<or> e = Tock \<and> (\<exists>x\<in>P. \<rho> @ [[X]\<^sub>R, [e]\<^sub>E] \<in> rename_trace f x)}"
          using case_assms(1) by blast
        then show "False"
          using case_assms2(1) case_assms3 lift_renaming_func.elims by auto
      next
        assume case_assms3: "Tock \<in> Y'" "[[Xa]\<^sub>R, [Tock]\<^sub>E] \<in> P"
        have "lift_renaming_func f Tock \<in> Y"
          using case_assms3 Y'_def by auto
        then have "lift_renaming_func f Tock \<notin> {e. e \<noteq> Tock \<and> (\<exists>x\<in>P. \<rho> @ [[e]\<^sub>E] \<in> rename_trace f x) \<or> e = Tock \<and> (\<exists>x\<in>P. \<rho> @ [[X]\<^sub>R, [e]\<^sub>E] \<in> rename_trace f x)}"
          using case_assms(1) by blast
        then show "False"
          using Z_assms case_assms3(2) case_assms2 by auto
      qed
      then have "[Xa \<union> Y']\<^sub>R # t \<in> P"
        using case_assms(2) case_assms(3) unfolding TT2s_def by (erule_tac x="[]" in allE, auto)
      then show "\<exists>x\<in>P. [Z \<union> Y]\<^sub>R # \<sigma> \<in> rename_trace f x"
        using Z_assms Y'_def case_assms2(1) by (rule_tac x="[Xa \<union> Y']\<^sub>R # t" in bexI, auto)
    qed
  qed
  then show "Y \<inter> {e. e \<noteq> Tock \<and> (\<exists>x\<in>P. \<rho> @ [[e]\<^sub>E] \<in> rename_trace f x) \<or> e = Tock \<and> (\<exists>x\<in>P. \<rho> @ [[X]\<^sub>R, [e]\<^sub>E] \<in> rename_trace f x)} = {} \<Longrightarrow>
       x \<in> P \<Longrightarrow> \<rho> @ [X]\<^sub>R # \<sigma> \<in> rename_trace f x \<Longrightarrow> \<exists>x\<in>P. \<rho> @ [X \<union> Y]\<^sub>R # \<sigma> \<in> rename_trace f x"
    using assms by auto
qed

lemma TT3_Renaming: "TT3 P \<Longrightarrow> TT3 (RenamingTT P f)"
  unfolding TT3_def RenamingTT_def
proof (simp, safe)
  fix x xa
  have "\<And>P x. \<forall>x\<in>P. TT3_trace x \<Longrightarrow> xa \<in> P \<Longrightarrow> x \<in> rename_trace f xa \<Longrightarrow> TT3_trace x"
  proof (induct xa rule:TT3_trace.induct)
    fix P x
    show "Ball P TT3_trace \<Longrightarrow> [] \<in> P \<Longrightarrow> x \<in> rename_trace f [] \<Longrightarrow> TT3_trace x"
      by simp
  next
    fix x P xa 
    show "Ball P TT3_trace \<Longrightarrow> [x] \<in> P \<Longrightarrow> xa \<in> rename_trace f [x] \<Longrightarrow> TT3_trace xa"
      by (cases x, auto)
  next
    fix X \<rho> P x
    assume ind_hyp: "\<And>P x. Ball P TT3_trace \<Longrightarrow> \<rho> \<in> P \<Longrightarrow> x \<in> rename_trace f \<rho> \<Longrightarrow> TT3_trace x"
    assume case_assms: "Ball P TT3_trace" "[X]\<^sub>R # [Tock]\<^sub>E # \<rho> \<in> P" "x \<in> rename_trace f ([X]\<^sub>R # [Tock]\<^sub>E # \<rho>)"
    obtain x' Y where x_def: "x = [Y]\<^sub>R # [Tock]\<^sub>E # x' \<and> X = lift_renaming_func f -` Y"
      using case_assms(3) by (cases x rule:ttWF.cases, auto)
    have 1: "Ball {x. [X]\<^sub>R # [Tock]\<^sub>E # x \<in> P} TT3_trace"
      using case_assms(1) by auto
    have 2: "\<rho> \<in> {x. [X]\<^sub>R # [Tock]\<^sub>E # x \<in> P}"
      using case_assms(2) by auto
    have 3: "x' \<in> rename_trace f \<rho>"
      using x_def case_assms(3) by auto
    have "TT3_trace x'"
      using 1 2 3 ind_hyp[where x=x', where P="{x. [X]\<^sub>R # [Tock]\<^sub>E # x \<in> P}"] by fastforce
    then show "TT3_trace x"
      by (metis TT3_trace.simps(3) case_assms(1) case_assms(2) lift_renaming_func.simps(2) vimageI x_def)
  next
    fix va vb vc P x
    assume ind_hyp: "\<And>P x. Ball P TT3_trace \<Longrightarrow> vb # vc \<in> P \<Longrightarrow> x \<in> rename_trace f (vb # vc) \<Longrightarrow> TT3_trace x"
    assume case_assms: "Ball P TT3_trace" "[va]\<^sub>E # vb # vc \<in> P" "x \<in> rename_trace f ([va]\<^sub>E # vb # vc)"
    obtain va' vb' x' where x_def: "x = [va']\<^sub>E # vb' # x'"
      using case_assms(3) by (cases x rule:TT3_trace.cases, auto, cases vb, auto)
    have 1: "Ball {x. [va]\<^sub>E # x \<in> P} TT3_trace"
      using case_assms(1) TT3_trace_cons_imp_cons by blast
    have "TT3_trace (vb' # x')"
      using 1 case_assms(2) case_assms(3) x_def ind_hyp[where x="vb' # x'", where P="{x. [va]\<^sub>E # x \<in> P}"] by fastforce
    then show "TT3_trace x"
      using x_def case_assms(3) by simp
  next
    fix va vd vc P x
    assume ind_hyp: "\<And>P x. Ball P TT3_trace \<Longrightarrow> [Event vd]\<^sub>E # vc \<in> P \<Longrightarrow> x \<in> rename_trace f ([Event vd]\<^sub>E # vc) \<Longrightarrow> TT3_trace x"
    assume case_assms: "Ball P TT3_trace" "[va]\<^sub>R # [Event vd]\<^sub>E # vc \<in> P" "x \<in> rename_trace f ([va]\<^sub>R # [Event vd]\<^sub>E # vc)"
    obtain va' vd' x' where x_def: "x = [va']\<^sub>R # [Event vd']\<^sub>E # x'"
      using case_assms(3) by (cases x rule:ttWF.cases, auto)
    have 1: "Ball {x. [va]\<^sub>R # x \<in> P} TT3_trace"
      using case_assms(1) TT3_trace_cons_imp_cons by auto
    have "TT3_trace ([Event vd']\<^sub>E # x')"
      using 1 case_assms(2) case_assms(3) x_def ind_hyp[where x="[Event vd']\<^sub>E # x'", where P="{x. [va]\<^sub>R # x \<in> P}"] by fastforce
    then show "TT3_trace x"
      using x_def case_assms(3) by simp
  next
    fix va vc P x
    assume ind_hyp: "\<And>P x. Ball P TT3_trace \<Longrightarrow> [Tick]\<^sub>E # vc \<in> P \<Longrightarrow> x \<in> rename_trace f ([Tick]\<^sub>E # vc) \<Longrightarrow> TT3_trace x"
    assume case_assms: "Ball P TT3_trace" "[va]\<^sub>R # [Tick]\<^sub>E # vc \<in> P" "x \<in> rename_trace f ([va]\<^sub>R # [Tick]\<^sub>E # vc)"
    obtain va' x' where x_def: "x = [va']\<^sub>R # [Tick]\<^sub>E # x'"
      using case_assms(3) by (cases x rule:ttWF.cases, auto)
    have 1: "Ball {x. [va]\<^sub>R # x \<in> P} TT3_trace"
      using case_assms(1) TT3_trace_cons_imp_cons by auto
    have "TT3_trace ([Tick]\<^sub>E # x')"
      using 1 case_assms(2) case_assms(3) x_def ind_hyp[where x="[Tick]\<^sub>E # x'", where P="{x. [va]\<^sub>R # x \<in> P}"] by fastforce
    then show "TT3_trace x"
      using x_def case_assms(3) by simp
  next
    fix vb va vc P x
    assume ind_hyp: "\<And>P x. Ball P TT3_trace \<Longrightarrow> [va]\<^sub>R # vc \<in> P \<Longrightarrow> x \<in> rename_trace f ([va]\<^sub>R # vc) \<Longrightarrow> TT3_trace x"
    assume case_assms: "Ball P TT3_trace" "[vb]\<^sub>R # [va]\<^sub>R # vc \<in> P" "x \<in> rename_trace f ([vb]\<^sub>R # [va]\<^sub>R # vc)"
    obtain va' vb' x' where x_def: "x = [vb']\<^sub>R # [va']\<^sub>R # x'"
      using case_assms(3) by (cases x rule:ttWF.cases, auto)
    have 1: "Ball {x. [vb]\<^sub>R # x \<in> P} TT3_trace"
      using case_assms(1) TT3_trace_cons_imp_cons by auto
    have "TT3_trace ([va']\<^sub>R # x')"
      using 1 case_assms(2) case_assms(3) x_def ind_hyp[where x="[va']\<^sub>R # x'", where P="{x. [vb]\<^sub>R # x \<in> P}"] by fastforce
    then show "TT3_trace x"
      using x_def case_assms(3) by simp
  qed
  then show "\<forall>x\<in>P. TT3_trace x \<Longrightarrow> xa \<in> P \<Longrightarrow> x \<in> rename_trace f xa \<Longrightarrow> TT3_trace x"
    by blast
qed

lemma TT4s_Renaming: 
  assumes "TT4s P"
  shows "TT4s (RenamingTT P f)"
  unfolding RenamingTT_def TT4s_def
proof auto
  fix \<rho> x
  have "\<And>P \<rho>. x \<in> P \<Longrightarrow> \<rho> \<in> rename_trace f x \<Longrightarrow> add_Tick_refusal_trace \<rho> \<in> rename_trace f (add_Tick_refusal_trace x)"
    using UNIV_I lift_renaming_func.elims by (induct f x rule:rename_trace.induct, auto, blast+)
  then show "x \<in> P \<Longrightarrow> \<rho> \<in> rename_trace f x \<Longrightarrow> \<exists>x\<in>P. add_Tick_refusal_trace \<rho> \<in> rename_trace f x"
    using assms unfolding TT4s_def by (rule_tac x="add_Tick_refusal_trace x" in bexI, auto)
qed

lemma TT_Renaming:
  shows "TT P \<Longrightarrow> TT2s P \<Longrightarrow> TT (RenamingTT P f)"
  unfolding TT_def by (auto simp add: RenamingTT_wf TT0_Renaming TT1_Renaming TT2s_Renaming TT2s_imp_TT2 TT3_Renaming)

end