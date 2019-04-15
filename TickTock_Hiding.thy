theory TickTock_Hiding
  imports TickTock_Core
begin

subsection {* Hiding *}

fun hide_trace :: "'a cttevent set \<Rightarrow> 'a cttobs list \<Rightarrow> 'a cttobs list set" where
  "hide_trace X [] = {[]}" |
  "hide_trace X ([Event e]\<^sub>E # s) =
    {t. (Event e \<in> X \<and> t \<in> hide_trace X s) \<or> (\<exists>s'. Event e \<notin> X \<and> s' \<in> hide_trace X s \<and> t = [Event e]\<^sub>E # s')}" |
  "hide_trace X ([[Tick]\<^sub>E]) =
    {t. (Tick \<in> X \<and> t = []) \<or> (Tick \<notin> X \<and> t = [[Tick]\<^sub>E])}" |
  "hide_trace X ([Y]\<^sub>R # [Tock]\<^sub>E # s) =
    {t. (Tock \<in> X \<and> t \<in> hide_trace X s)
    \<or> (\<exists> s'. \<exists> Z\<subseteq>Y. Tock \<notin> X \<and> X \<subseteq> Y \<and> t = [Z]\<^sub>R # [Tock]\<^sub>E # s' \<and> s' \<in> hide_trace X s)}" | (* fill in subsets to account for removed sets *)
    (* if X \<subseteq> Y is not true an event in X could happen so the hidden event takes priority over tock *)
  "hide_trace X [[Y]\<^sub>R] = {t. \<exists> Z\<subseteq>Y. X \<subseteq> Y \<and> t = [[Z]\<^sub>R]}" | (* fill in subsets to account for removed sets *)
    (* if X \<subseteq> Y is not true an event in X could happen so instability is introduced when it is hidden *)
  "hide_trace X ([Tock]\<^sub>E # t) = {}" |
  "hide_trace X ([Y]\<^sub>R # [Event e]\<^sub>E # t) = {}" |
  "hide_trace X ([Y]\<^sub>R # [Tick]\<^sub>E # t) = {}" |
  "hide_trace X ([Y]\<^sub>R # [Z]\<^sub>R # t) = {}" |
  "hide_trace X ([Tick]\<^sub>E # x # t) = {}"

definition HidingTT :: "'a cttobs list set \<Rightarrow> 'a cttevent set \<Rightarrow> 'a cttobs list set" (infixl "\<setminus>\<^sub>C" 53) where
  "HidingTT P X = \<Union> {hide_trace X p | p. p \<in> P}"

lemma HidingTT_wf:
  assumes "\<forall>x\<in>P. ttWF x"
  shows "\<forall>x\<in>(P \<setminus>\<^sub>C X). ttWF x"
  using assms unfolding HidingTT_def
proof auto
  fix x p
  show "\<And> P x. \<forall>x\<in>P. ttWF x \<Longrightarrow> x \<in> hide_trace X p \<Longrightarrow> p \<in> P \<Longrightarrow> ttWF x"
    apply (induct p rule:hide_trace.induct, simp_all)
    apply (metis ttWF.simps(4) mem_Collect_eq)
    using ttWF.simps(1) apply blast
    apply (metis ttWF.simps(5) mem_Collect_eq)
    using ttWF.simps(2) by blast
qed

lemma TT0_Hiding:
  assumes "TT0 P" "TT1 P"  
  shows "TT0 (P \<setminus>\<^sub>C X)"
  unfolding HidingTT_def TT0_def
proof auto
  have "[] \<in> P"
    by (simp add: TT0_TT1_empty assms(1) assms(2))
  then show "\<exists>x. (\<exists>p. x = hide_trace X p \<and> p \<in> P) \<and> x \<noteq> {}"
    using hide_trace.simps(1) by blast
qed

lemma TT1_Hiding:
  shows "TT1 P \<Longrightarrow> TT1 (P \<setminus>\<^sub>C X)"
  unfolding HidingTT_def TT1_def
proof auto
  fix p
  show "\<And>P \<rho> \<sigma>. \<forall>\<rho>. (\<exists>\<sigma>. \<rho> \<lesssim>\<^sub>C \<sigma> \<and> \<sigma> \<in> P) \<longrightarrow> \<rho> \<in> P \<Longrightarrow> \<rho> \<lesssim>\<^sub>C \<sigma> \<Longrightarrow> \<sigma> \<in> hide_trace X p \<Longrightarrow> p \<in> P \<Longrightarrow> \<exists>x. (\<exists>p. x = hide_trace X p \<and> p \<in> P) \<and> \<rho> \<in> x"
  proof (induct p rule:hide_trace.induct, simp_all, safe, simp_all)
    fix X :: "'a cttevent set"
    fix \<rho> :: "'a cttobs list"
    fix P :: "'a cttobs list set" 
    assume case_assms: "\<rho> \<lesssim>\<^sub>C []" "[] \<in> P"
    then have "\<rho> = []"
      by (induct \<rho>, auto)
    then show "\<exists>x. (\<exists>p. x = hide_trace X p \<and> p \<in> P) \<and> \<rho> \<in> x"
      using case_assms by auto
  next
    fix X e s P \<rho> \<sigma>
    assume ind_hyp: "\<And>P \<rho> \<sigma>. \<forall>\<rho>. (\<exists>\<sigma>. \<rho> \<lesssim>\<^sub>C \<sigma> \<and> \<sigma> \<in> P) \<longrightarrow> \<rho> \<in> P \<Longrightarrow>
                 \<rho> \<lesssim>\<^sub>C \<sigma> \<Longrightarrow> \<sigma> \<in> hide_trace X s \<Longrightarrow> s \<in> P \<Longrightarrow> \<exists>x. (\<exists>p. x = hide_trace X p \<and> p \<in> P) \<and> \<rho> \<in> x"
    assume case_assms: "\<forall>\<rho>. (\<exists>\<sigma>. \<rho> \<lesssim>\<^sub>C \<sigma> \<and> \<sigma> \<in> P) \<longrightarrow> \<rho> \<in> P" "\<rho> \<lesssim>\<^sub>C \<sigma>" "[Event e]\<^sub>E # s \<in> P" "Event e \<in> X" "\<sigma> \<in> hide_trace X s"
    have 1: "\<forall>\<rho>. (\<exists>\<sigma>. \<rho> \<lesssim>\<^sub>C \<sigma> \<and> \<sigma> \<in> {t. [Event e]\<^sub>E # t \<in> P}) \<longrightarrow> \<rho> \<in> {t. [Event e]\<^sub>E # t \<in> P}"
      using case_assms(1) ctt_prefix_subset.simps(3) by blast
    have 2: "s \<in> {t. [Event e]\<^sub>E # t \<in> P}"
      using case_assms by auto
    obtain x p  where "x = hide_trace X p \<and> p \<in> {t. [Event e]\<^sub>E # t \<in> P} \<and> \<rho> \<in> x"
      using 1 2 case_assms ind_hyp[where P="{t. [Event e]\<^sub>E # t \<in> P}", where \<rho>=\<rho>, where \<sigma>=\<sigma>] by blast
    then show "\<exists>x. (\<exists>p. x = hide_trace X p \<and> p \<in> P) \<and> \<rho> \<in> x"
      apply (rule_tac x="hide_trace X ([Event e]\<^sub>E # p)" in exI)
      by (metis (no_types, lifting) case_assms(4) hide_trace.simps(2) mem_Collect_eq)
  next
    fix X e s P \<rho> s'
    assume ind_hyp: "\<And>P \<rho> \<sigma>. \<forall>\<rho>. (\<exists>\<sigma>. \<rho> \<lesssim>\<^sub>C \<sigma> \<and> \<sigma> \<in> P) \<longrightarrow> \<rho> \<in> P \<Longrightarrow>
                 \<rho> \<lesssim>\<^sub>C \<sigma> \<Longrightarrow> \<sigma> \<in> hide_trace X s \<Longrightarrow> s \<in> P \<Longrightarrow> \<exists>x. (\<exists>p. x = hide_trace X p \<and> p \<in> P) \<and> \<rho> \<in> x"
    assume case_assms: "\<forall>\<rho>. (\<exists>\<sigma>. \<rho> \<lesssim>\<^sub>C \<sigma> \<and> \<sigma> \<in> P) \<longrightarrow> \<rho> \<in> P" "\<rho> \<lesssim>\<^sub>C [Event e]\<^sub>E # s'"
      "[Event e]\<^sub>E # s \<in> P" "Event e \<notin> X" "s' \<in> hide_trace X s"
    have "(\<exists>\<rho>'. \<rho>' \<lesssim>\<^sub>C s' \<and> \<rho> = [Event e]\<^sub>E # \<rho>') \<or> \<rho> = []"
      using case_assms(2) by (cases \<rho>, auto, (case_tac a, auto)+)
    then show "\<exists>x. (\<exists>p. x = hide_trace X p \<and> p \<in> P) \<and> \<rho> \<in> x"
    proof auto
      fix \<rho>'
      assume case_assms2: "\<rho>' \<lesssim>\<^sub>C s'" "\<rho> = [Event e]\<^sub>E # \<rho>'"
      have 1: "\<forall>\<rho>. (\<exists>\<sigma>. \<rho> \<lesssim>\<^sub>C \<sigma> \<and> \<sigma> \<in> {t. [Event e]\<^sub>E # t \<in> P}) \<longrightarrow> \<rho> \<in> {t. [Event e]\<^sub>E # t \<in> P}"
        using case_assms(1) ctt_prefix_subset.simps(3) by blast
      have 2: "s \<in> {t. [Event e]\<^sub>E # t \<in> P}"
        by (simp add: case_assms(3))
      obtain x p where "x = hide_trace X p \<and> p \<in> {t. [Event e]\<^sub>E # t \<in> P} \<and> \<rho>' \<in> x"
        using ind_hyp[where P="{t. [Event e]\<^sub>E # t \<in> P}", where \<rho>=\<rho>', where \<sigma>=s'] 1 2 case_assms2 case_assms(5) by blast
      then show "\<exists>x. (\<exists>p. x = hide_trace X p \<and> p \<in> P) \<and> [Event e]\<^sub>E # \<rho>' \<in> x"
        by (rule_tac x="hide_trace X ([Event e]\<^sub>E # p)" in exI, auto, rule_tac x="[Event e]\<^sub>E # p" in exI, auto simp add: case_assms)
    next
      show "\<rho> = [] \<Longrightarrow> \<exists>x. (\<exists>p. x = hide_trace X p \<and> p \<in> P) \<and> [] \<in> x"
        apply (rule_tac x="hide_trace X []" in exI, auto, rule_tac x="[]" in exI, auto)
        using case_assms(1) case_assms(3) ctt_prefix_subset.simps(1) by blast
    qed
  next
    fix X :: "'a cttevent set"
    fix \<rho> :: "'a cttobs list"
    fix P :: "'a cttobs list set" 
    assume case_assms: "\<rho> \<lesssim>\<^sub>C []" "[[Tick]\<^sub>E] \<in> P" "\<forall>\<rho>. (\<exists>\<sigma>. \<rho> \<lesssim>\<^sub>C \<sigma> \<and> \<sigma> \<in> P) \<longrightarrow> \<rho> \<in> P"
    then have "\<rho> = []"
      by (cases \<rho>, auto)
    then show "\<exists>x. (\<exists>p. x = hide_trace X p \<and> p \<in> P) \<and> \<rho> \<in> x"
      apply (rule_tac x="hide_trace X []" in exI, auto, rule_tac x="[]" in exI, auto)
      using case_assms(2) case_assms(3) ctt_prefix_subset.simps(1) by blast
  next
    fix X :: "'a cttevent set"
    fix \<rho> :: "'a cttobs list"
    fix P :: "'a cttobs list set" 
    assume case_assms: "\<forall>\<rho>. (\<exists>\<sigma>. \<rho> \<lesssim>\<^sub>C \<sigma> \<and> \<sigma> \<in> P) \<longrightarrow> \<rho> \<in> P" "\<rho> \<lesssim>\<^sub>C [[Tick]\<^sub>E]" "[[Tick]\<^sub>E] \<in> P" "Tick \<notin> X"
    then have "\<rho> = [] \<or> \<rho> = [[Tick]\<^sub>E]"
      by (cases \<rho>, simp, case_tac a, simp_all, case_tac list, simp_all)
    then show "\<exists>x. (\<exists>p. x = hide_trace X p \<and> p \<in> P) \<and> \<rho> \<in> x"
      apply (auto, rule_tac x="hide_trace X []" in exI, auto, rule_tac x="[]" in exI, auto)
      using case_assms ctt_prefix_subset.simps(1) by (blast, auto)
  next
    fix X Y s P \<rho> \<sigma>
    assume ind_hyp: "\<And>P \<rho> \<sigma>. \<forall>\<rho>. (\<exists>\<sigma>. \<rho> \<lesssim>\<^sub>C \<sigma> \<and> \<sigma> \<in> P) \<longrightarrow> \<rho> \<in> P \<Longrightarrow>
                 \<rho> \<lesssim>\<^sub>C \<sigma> \<Longrightarrow> \<sigma> \<in> hide_trace X s \<Longrightarrow> s \<in> P \<Longrightarrow> \<exists>x. (\<exists>p. x = hide_trace X p \<and> p \<in> P) \<and> \<rho> \<in> x"
    assume case_assms: "\<forall>\<rho>. (\<exists>\<sigma>. \<rho> \<lesssim>\<^sub>C \<sigma> \<and> \<sigma> \<in> P) \<longrightarrow> \<rho> \<in> P" "\<rho> \<lesssim>\<^sub>C \<sigma>" "[Y]\<^sub>R # [Tock]\<^sub>E # s \<in> P" "Tock \<in> X" "\<sigma> \<in> hide_trace X s"
    have 1: "\<forall>\<rho>. (\<exists>\<sigma>. \<rho> \<lesssim>\<^sub>C \<sigma> \<and> \<sigma> \<in> {t. [Y]\<^sub>R # [Tock]\<^sub>E # t \<in> P}) \<longrightarrow> \<rho> \<in> {t. [Y]\<^sub>R # [Tock]\<^sub>E # t \<in> P}"
      by (metis case_assms(1) ctt_prefix_subset.simps(2) ctt_prefix_subset.simps(3) ctt_subset.simps(2) ctt_subset_refl mem_Collect_eq)
    have 2: "s \<in> {t. [Y]\<^sub>R # [Tock]\<^sub>E # t \<in> P}"
      by (simp add: case_assms(3))
    obtain x p where "x = hide_trace X p \<and> p \<in> {t. [Y]\<^sub>R # [Tock]\<^sub>E # t \<in> P} \<and> \<rho> \<in> x"
      using ind_hyp[where P="{t. [Y]\<^sub>R # [Tock]\<^sub>E # t \<in> P}", where \<rho>=\<rho>, where \<sigma>=\<sigma>] 1 2 case_assms by blast
    then show "\<exists>x. (\<exists>p. x = hide_trace X p \<and> p \<in> P) \<and> \<rho> \<in> x"
      apply (rule_tac x="hide_trace X ([Y]\<^sub>R # [Tock]\<^sub>E # p)" in exI, auto)
      by (rule_tac x="[Y]\<^sub>R # [Tock]\<^sub>E # p" in exI, auto simp add: case_assms(4))
  next
    fix X Y s P \<rho> s' Z
    assume ind_hyp: "\<And>P \<rho> \<sigma>. \<forall>\<rho>. (\<exists>\<sigma>. \<rho> \<lesssim>\<^sub>C \<sigma> \<and> \<sigma> \<in> P) \<longrightarrow> \<rho> \<in> P \<Longrightarrow>
                 \<rho> \<lesssim>\<^sub>C \<sigma> \<Longrightarrow> \<sigma> \<in> hide_trace X s \<Longrightarrow> s \<in> P \<Longrightarrow> \<exists>x. (\<exists>p. x = hide_trace X p \<and> p \<in> P) \<and> \<rho> \<in> x"
    assume case_assms: "\<forall>\<rho>. (\<exists>\<sigma>. \<rho> \<lesssim>\<^sub>C \<sigma> \<and> \<sigma> \<in> P) \<longrightarrow> \<rho> \<in> P" "\<rho> \<lesssim>\<^sub>C [Z]\<^sub>R # [Tock]\<^sub>E # s'"
      "[Y]\<^sub>R # [Tock]\<^sub>E # s \<in> P" "Z \<subseteq> Y" "Tock \<notin> X" "X \<subseteq> Y" "s' \<in> hide_trace X s"
    have 1: "\<forall>\<rho>. (\<exists>\<sigma>. \<rho> \<lesssim>\<^sub>C \<sigma> \<and> \<sigma> \<in> {t. [Y]\<^sub>R # [Tock]\<^sub>E # t \<in> P}) \<longrightarrow> \<rho> \<in> {t. [Y]\<^sub>R # [Tock]\<^sub>E # t \<in> P}"
      by (metis case_assms(1) ctt_prefix_subset.simps(2) ctt_prefix_subset.simps(3) mem_Collect_eq subset_refl)
    have 2: "s \<in> {t. [Y]\<^sub>R # [Tock]\<^sub>E # t \<in> P}"
      by (simp add: case_assms(3))
    have "(\<exists> \<rho>' W. \<rho> = [W]\<^sub>R # [Tock]\<^sub>E # \<rho>' \<and> W \<subseteq> Z) \<or> (\<exists> W. \<rho> = [[W]\<^sub>R] \<and> W \<subseteq> Z) \<or> (\<rho> = [])"
      using case_assms(2) by (cases \<rho> rule:ttWF.cases, simp_all)
    then show "\<exists>x. (\<exists>p. x = hide_trace X p \<and> p \<in> P) \<and> \<rho> \<in> x"
    proof auto
      fix \<rho>' W
      assume case_assms2: "W \<subseteq> Z" "\<rho> = [W]\<^sub>R # [Tock]\<^sub>E # \<rho>'"
      have "\<rho>' \<lesssim>\<^sub>C s'"
        using case_assms(2) case_assms2(2) by auto
      then obtain x p where "x = hide_trace X p \<and> p \<in> {t. [Y]\<^sub>R # [Tock]\<^sub>E # t \<in> P} \<and> \<rho>' \<in> x"
        using ind_hyp[where P="{t. [Y]\<^sub>R # [Tock]\<^sub>E # t \<in> P}", where \<rho>=\<rho>', where \<sigma>=s'] 1 2 case_assms(7) by blast 
      then show "\<exists>x. (\<exists>p. x = hide_trace X p \<and> p \<in> P) \<and> [W]\<^sub>R # [Tock]\<^sub>E # \<rho>' \<in> x"
        apply (rule_tac x="hide_trace X ([Y]\<^sub>R # [Tock]\<^sub>E # p)" in exI, safe)
        using case_assms2(1) case_assms(4) case_assms(5) case_assms(6) by (rule_tac x="[Y]\<^sub>R # [Tock]\<^sub>E # p" in exI, auto)
    next
      fix W
      assume case_assms2: "W \<subseteq> Z" "\<rho> = [[W]\<^sub>R]"
      then show "\<exists>x. (\<exists>p. x = hide_trace X p \<and> p \<in> P) \<and> [[W]\<^sub>R] \<in> x"
        apply (rule_tac x="hide_trace X ([[Y]\<^sub>R])" in exI, safe)
        using case_assms(4) case_assms(5) case_assms(6) apply (rule_tac x="[[Y]\<^sub>R]" in exI, auto)
        using case_assms(1) case_assms(3) ctt_prefix_subset.simps(1) ctt_prefix_subset.simps(2) by blast
    next
      show "\<rho> = [] \<Longrightarrow> \<exists>x. (\<exists>p. x = hide_trace X p \<and> p \<in> P) \<and> [] \<in> x"
        using case_assms(1) case_assms(3) ctt_prefix_subset.simps(1) hide_trace.simps(1) by blast
    qed
  next
    fix X Y P \<rho> Z
    assume case_assms: "\<forall>\<rho>. (\<exists>\<sigma>. \<rho> \<lesssim>\<^sub>C \<sigma> \<and> \<sigma> \<in> P) \<longrightarrow> \<rho> \<in> P" "\<rho> \<lesssim>\<^sub>C [[Z]\<^sub>R]" "[[Y]\<^sub>R] \<in> P" "Z \<subseteq> Y" "X \<subseteq> Y "
    then have "(\<exists> W. \<rho> = [[W]\<^sub>R] \<and> W \<subseteq> Z) \<or> (\<rho> = [])"
      using case_assms(2) by (cases \<rho> rule:ttWF.cases, simp_all)
    then show "\<exists>x. (\<exists>p. x = hide_trace X p \<and> p \<in> P) \<and> \<rho> \<in> x"
      apply auto apply (rule_tac x="hide_trace X ([[Y]\<^sub>R])" in exI, safe)
      using case_assms apply (rule_tac x="[[Y]\<^sub>R]" in exI, auto)
      apply (rule_tac x="{[]}" in exI, simp, rule_tac x="[]" in exI, simp)
      using ctt_prefix_subset.simps(1) by blast
  qed
qed

lemma TT2_Hiding:
  assumes "TT2 P"
  shows "TT2 (P \<setminus>\<^sub>C X)"
  unfolding TT2_def HidingTT_def
proof auto
  fix Xa Y p
  show "\<And> \<rho>. Y \<inter> {e. e \<noteq> Tock \<and> (\<exists>x. (\<exists>p. x = hide_trace X p \<and> p \<in> P) \<and> \<rho> @ [[e]\<^sub>E] \<in> x) \<or>
      e = Tock \<and> (\<exists>x. (\<exists>p. x = hide_trace X p \<and> p \<in> P) \<and> \<rho> @ [[Xa]\<^sub>R, [e]\<^sub>E] \<in> x)} = {} \<Longrightarrow>
    \<rho> @ [[Xa]\<^sub>R] \<in> hide_trace X p \<Longrightarrow> p \<in> P \<Longrightarrow> \<exists>x. (\<exists>p. x = hide_trace X p \<and> p \<in> P) \<and> \<rho> @ [[Xa \<union> Y]\<^sub>R] \<in> x"
    using assms
  proof -
    show "\<And>P \<rho>. Y \<inter> {e. e \<noteq> Tock \<and> (\<exists>x. (\<exists>p. x = hide_trace X p \<and> p \<in> P) \<and> \<rho> @ [[e]\<^sub>E] \<in> x) \<or>
        e = Tock \<and> (\<exists>x. (\<exists>p. x = hide_trace X p \<and> p \<in> P) \<and> \<rho> @ [[Xa]\<^sub>R, [e]\<^sub>E] \<in> x)} = {} \<Longrightarrow>
      \<rho> @ [[Xa]\<^sub>R] \<in> hide_trace X p \<Longrightarrow> p \<in> P \<Longrightarrow> TT2 P \<Longrightarrow> \<exists>x. (\<exists>p. x = hide_trace X p \<and> p \<in> P) \<and> \<rho> @ [[Xa \<union> Y]\<^sub>R] \<in> x"
    proof (induct p rule:ttWF.induct, simp_all, safe, simp_all)
      fix Xb P
      assume case_assms: "Y \<inter> {e. e \<noteq> Tock \<and> (\<exists>x. (\<exists>p. x = hide_trace X p \<and> p \<in> P) \<and> [[e]\<^sub>E] \<in> x) \<or>
                      e = Tock \<and> (\<exists>x. (\<exists>p. x = hide_trace X p \<and> p \<in> P) \<and> [[Xa]\<^sub>R, [e]\<^sub>E] \<in> x)} = {}"
        "[[Xb]\<^sub>R] \<in> P" "TT2 P" "Xa \<subseteq> Xb" "X \<subseteq> Xb"
      have "{e. e\<notin>X \<and> (e \<noteq> Tock \<and> [[e]\<^sub>E] \<in> P \<or> e = Tock \<and> [[Xb]\<^sub>R, [e]\<^sub>E] \<in> P)} \<subseteq>
        {e. e \<noteq> Tock \<and> (\<exists>x. (\<exists>p. x = hide_trace X p \<and> p \<in> P) \<and> [[e]\<^sub>E] \<in> x) \<or>
          e = Tock \<and> (\<exists>x. (\<exists>p. x = hide_trace X p \<and> p \<in> P) \<and> [[Xa]\<^sub>R, [e]\<^sub>E] \<in> x)}"
      proof auto
        fix x
        show "x \<notin> X \<Longrightarrow> [[x]\<^sub>E] \<in> P \<Longrightarrow> x \<noteq> Tock \<Longrightarrow> \<exists>xa. (\<exists>p. xa = hide_trace X p \<and> p \<in> P) \<and> [[x]\<^sub>E] \<in> xa"
          by (rule_tac x="hide_trace X [[x]\<^sub>E]" in exI, auto, cases x, auto)
      next
        fix x
        show "x \<notin> X \<Longrightarrow> [[x]\<^sub>E] \<in> P \<Longrightarrow> x \<noteq> Tock \<Longrightarrow> \<exists>xa. (\<exists>p. xa = hide_trace X p \<and> p \<in> P) \<and> [[x]\<^sub>E] \<in> xa"
          by (rule_tac x="hide_trace X [[x]\<^sub>E]" in exI, auto, cases x, auto)
      next
        show "Tock \<notin> X \<Longrightarrow> [[Xb]\<^sub>R, [Tock]\<^sub>E] \<in> P \<Longrightarrow> \<forall>x. (\<forall>p. x = hide_trace X p \<longrightarrow> p \<notin> P) \<or> [[Xa]\<^sub>R, [Tock]\<^sub>E] \<notin> x \<Longrightarrow> False"
          using case_assms by (erule_tac x="hide_trace X [[Xb]\<^sub>R, [Tock]\<^sub>E]" in allE, auto)
      next
        show "Tock \<notin> X \<Longrightarrow> [[Xb]\<^sub>R, [Tock]\<^sub>E] \<in> P \<Longrightarrow> \<forall>x. (\<forall>p. x = hide_trace X p \<longrightarrow> p \<notin> P) \<or> [[Xa]\<^sub>R, [Tock]\<^sub>E] \<notin> x \<Longrightarrow> \<exists>x. (\<exists>p. x = hide_trace X p \<and> p \<in> P) \<and> [[Tock]\<^sub>E] \<in> x"
          using case_assms by (erule_tac x="hide_trace X [[Xb]\<^sub>R, [Tock]\<^sub>E]" in allE, auto)
      qed
      then have "{x. x \<notin> X} \<inter> Y \<inter> {e. e\<notin>X \<and> (e \<noteq> Tock \<and> [[e]\<^sub>E] \<in> P \<or> e = Tock \<and> [[Xb]\<^sub>R, [e]\<^sub>E] \<in> P)} = {}"
        using Int_empty_right case_assms(1) by auto
      then have "[[Xb \<union> ({x. x \<notin> X} \<inter> Y)]\<^sub>R] \<in> P"
        using case_assms unfolding TT2_def by (erule_tac x="[]" in allE, erule_tac x="Xb" in allE, erule_tac x="{x. x \<notin> X} \<inter> Y" in allE, auto)
      also have "Xb \<union> ({x. x \<notin> X} \<inter> Y) = Xb \<union> Y"
        using case_assms by auto
      then have "[[Xb \<union> Y]\<^sub>R] \<in> P"
        using calculation by auto
      then show "\<exists>x. (\<exists>p. x = hide_trace X p \<and> p \<in> P) \<and> [[Xa \<union> Y]\<^sub>R] \<in> x"
        using case_assms by (rule_tac x="hide_trace X [[Xb \<union> Y]\<^sub>R]" in exI, auto)
    next
      fix e \<sigma> P \<rho>
      assume ind_hyp: "\<And>P \<rho>. Y \<inter> {e. e \<noteq> Tock \<and> (\<exists>x. (\<exists>p. x = hide_trace X p \<and> p \<in> P) \<and> \<rho> @ [[e]\<^sub>E] \<in> x) \<or>
                       e = Tock \<and> (\<exists>x. (\<exists>p. x = hide_trace X p \<and> p \<in> P) \<and> \<rho> @ [[Xa]\<^sub>R, [e]\<^sub>E] \<in> x)} = {} \<Longrightarrow>
        \<rho> @ [[Xa]\<^sub>R] \<in> hide_trace X \<sigma> \<Longrightarrow> \<sigma> \<in> P \<Longrightarrow> TT2 P \<Longrightarrow> \<exists>x. (\<exists>p. x = hide_trace X p \<and> p \<in> P) \<and> \<rho> @ [[Xa \<union> Y]\<^sub>R] \<in> x"
      assume case_assms: "Y \<inter> {e. e \<noteq> Tock \<and> (\<exists>x. (\<exists>p. x = hide_trace X p \<and> p \<in> P) \<and> \<rho> @ [[e]\<^sub>E] \<in> x) \<or>
                e = Tock \<and> (\<exists>x. (\<exists>p. x = hide_trace X p \<and> p \<in> P) \<and> \<rho> @ [[Xa]\<^sub>R, [e]\<^sub>E] \<in> x)} = {}"
        "[Event e]\<^sub>E # \<sigma> \<in> P" "TT2 P" "Event e \<in> X" "\<rho> @ [[Xa]\<^sub>R] \<in> hide_trace X \<sigma>"
      have "{ea. ea \<noteq> Tock \<and> (\<exists>x. (\<exists>p. x = hide_trace X p \<and> p \<in> {\<sigma>. [Event e]\<^sub>E # \<sigma> \<in> P}) \<and> \<rho> @ [[ea]\<^sub>E] \<in> x) \<or>
              ea = Tock \<and> (\<exists>x. (\<exists>p. x = hide_trace X p \<and> p \<in> {\<sigma>. [Event e]\<^sub>E # \<sigma> \<in> P}) \<and> \<rho> @ [[Xa]\<^sub>R, [ea]\<^sub>E] \<in> x)} \<subseteq>
        {e. e \<noteq> Tock \<and> (\<exists>x. (\<exists>p. x = hide_trace X p \<and> p \<in> P) \<and> \<rho> @ [[e]\<^sub>E] \<in> x) \<or>
                e = Tock \<and> (\<exists>x. (\<exists>p. x = hide_trace X p \<and> p \<in> P) \<and> \<rho> @ [[Xa]\<^sub>R, [e]\<^sub>E] \<in> x)}"
        using case_assms(4) apply (safe, simp_all)
        apply (rule_tac x="hide_trace X ([Event e]\<^sub>E # p)" in exI, simp, rule_tac x="[Event e]\<^sub>E # p" in exI, simp)
        apply (rule_tac x="hide_trace X ([Event e]\<^sub>E # p)" in exI, simp, rule_tac x="[Event e]\<^sub>E # p" in exI, simp)
        apply (erule_tac x="hide_trace X ([Event e]\<^sub>E # p)" in allE, simp)
        by (erule_tac x="hide_trace X ([Event e]\<^sub>E # p)" in allE, simp)
      then have 1: "Y \<inter> {ea. ea \<noteq> Tock \<and> (\<exists>x. (\<exists>p. x = hide_trace X p \<and> p \<in> {\<sigma>. [Event e]\<^sub>E # \<sigma> \<in> P}) \<and> \<rho> @ [[ea]\<^sub>E] \<in> x) \<or>
              ea = Tock \<and> (\<exists>x. (\<exists>p. x = hide_trace X p \<and> p \<in> {\<sigma>. [Event e]\<^sub>E # \<sigma> \<in> P}) \<and> \<rho> @ [[Xa]\<^sub>R, [ea]\<^sub>E] \<in> x)} = {}"
        by (smt case_assms(1) disjoint_iff_not_equal subsetCE)
      have 2: "TT2 {\<sigma>. [Event e]\<^sub>E # \<sigma> \<in> P}"
        using case_assms(3) unfolding TT2_def by (auto, erule_tac x="[Event e]\<^sub>E # \<rho>" in allE, auto)
      show "\<exists>x. (\<exists>p. x = hide_trace X p \<and> p \<in> P) \<and> \<rho> @ [[Xa \<union> Y]\<^sub>R] \<in> x"
        using ind_hyp[where P="{\<sigma>. [Event e]\<^sub>E # \<sigma> \<in> P}", where \<rho>=\<rho>] 1 2 case_assms by auto
    next
      fix e \<sigma> P \<rho> s'
      assume ind_hyp: "\<And>P \<rho>. Y \<inter> {e. e \<noteq> Tock \<and> (\<exists>x. (\<exists>p. x = hide_trace X p \<and> p \<in> P) \<and> \<rho> @ [[e]\<^sub>E] \<in> x) \<or>
                       e = Tock \<and> (\<exists>x. (\<exists>p. x = hide_trace X p \<and> p \<in> P) \<and> \<rho> @ [[Xa]\<^sub>R, [e]\<^sub>E] \<in> x)} = {} \<Longrightarrow>
        \<rho> @ [[Xa]\<^sub>R] \<in> hide_trace X \<sigma> \<Longrightarrow> \<sigma> \<in> P \<Longrightarrow> TT2 P \<Longrightarrow> \<exists>x. (\<exists>p. x = hide_trace X p \<and> p \<in> P) \<and> \<rho> @ [[Xa \<union> Y]\<^sub>R] \<in> x"
      assume case_assms: "Y \<inter> {e. e \<noteq> Tock \<and> (\<exists>x. (\<exists>p. x = hide_trace X p \<and> p \<in> P) \<and> \<rho> @ [[e]\<^sub>E] \<in> x) \<or>
                e = Tock \<and> (\<exists>x. (\<exists>p. x = hide_trace X p \<and> p \<in> P) \<and> \<rho> @ [[Xa]\<^sub>R, [e]\<^sub>E] \<in> x)} = {}"
        "[Event e]\<^sub>E # \<sigma> \<in> P" "TT2 P" "Event e \<notin> X" "s' \<in> hide_trace X \<sigma>" "\<rho> @ [[Xa]\<^sub>R] = [Event e]\<^sub>E # s'"
      then obtain \<rho>' where \<rho>'_assms: "\<rho> = [Event e]\<^sub>E # \<rho>' \<and> \<rho>' @ [[Xa]\<^sub>R] \<in> hide_trace X \<sigma>"
        by (cases \<rho> rule:ttWF.cases, simp_all, blast)
      have "{ea. ea \<noteq> Tock \<and> (\<exists>x. (\<exists>p. x = hide_trace X p \<and> p \<in> {\<sigma>. [Event e]\<^sub>E # \<sigma> \<in> P}) \<and> \<rho>' @ [[ea]\<^sub>E] \<in> x) \<or>
          ea = Tock \<and> (\<exists>x. (\<exists>p. x = hide_trace X p \<and> p \<in> {\<sigma>. [Event e]\<^sub>E # \<sigma> \<in> P}) \<and> \<rho>' @ [[Xa]\<^sub>R, [ea]\<^sub>E] \<in> x)} \<subseteq>
        {e. e \<noteq> Tock \<and> (\<exists>x. (\<exists>p. x = hide_trace X p \<and> p \<in> P) \<and> \<rho> @ [[e]\<^sub>E] \<in> x) \<or>
          e = Tock \<and> (\<exists>x. (\<exists>p. x = hide_trace X p \<and> p \<in> P) \<and> \<rho> @ [[Xa]\<^sub>R, [e]\<^sub>E] \<in> x)}"
        using \<rho>'_assms case_assms(4) by auto
      then have 1: "Y \<inter> {ea. ea \<noteq> Tock \<and> (\<exists>x. (\<exists>p. x = hide_trace X p \<and> p \<in> {\<sigma>. [Event e]\<^sub>E # \<sigma> \<in> P}) \<and> \<rho>' @ [[ea]\<^sub>E] \<in> x) \<or>
          ea = Tock \<and> (\<exists>x. (\<exists>p. x = hide_trace X p \<and> p \<in> {\<sigma>. [Event e]\<^sub>E # \<sigma> \<in> P}) \<and> \<rho>' @ [[Xa]\<^sub>R, [ea]\<^sub>E] \<in> x)} = {}"
        by (smt case_assms(1) disjoint_iff_not_equal subsetCE)
      have 2: "TT2 {\<sigma>. [Event e]\<^sub>E # \<sigma> \<in> P}"
        using case_assms(3) unfolding TT2_def by (auto, erule_tac x="[Event e]\<^sub>E # \<rho>" in allE, auto)
      have "\<exists>x. (\<exists>p. x = hide_trace X p \<and> p \<in> {\<sigma>. [Event e]\<^sub>E # \<sigma> \<in> P}) \<and> \<rho>' @ [[Xa \<union> Y]\<^sub>R] \<in> x"
        using ind_hyp[where P="{\<sigma>. [Event e]\<^sub>E # \<sigma> \<in> P}", where \<rho>="\<rho>'"] 1 2 \<rho>'_assms case_assms by auto
      then obtain x p where "x = hide_trace X p \<and> p \<in> {\<sigma>. [Event e]\<^sub>E # \<sigma> \<in> P} \<and> \<rho>' @ [[Xa \<union> Y]\<^sub>R] \<in> x"
        by auto
      then show "\<exists>x. (\<exists>p. x = hide_trace X p \<and> p \<in> P) \<and> \<rho> @ [[Xa \<union> Y]\<^sub>R] \<in> x"
        using case_assms \<rho>'_assms by (rule_tac x="hide_trace X ([Event e]\<^sub>E # p)" in exI, auto)
    next
      fix Xb \<sigma> P \<rho>
      assume ind_hyp: "\<And>P \<rho>. Y \<inter> {e. e \<noteq> Tock \<and> (\<exists>x. (\<exists>p. x = hide_trace X p \<and> p \<in> P) \<and> \<rho> @ [[e]\<^sub>E] \<in> x) \<or>
                       e = Tock \<and> (\<exists>x. (\<exists>p. x = hide_trace X p \<and> p \<in> P) \<and> \<rho> @ [[Xa]\<^sub>R, [e]\<^sub>E] \<in> x)} = {} \<Longrightarrow>
        \<rho> @ [[Xa]\<^sub>R] \<in> hide_trace X \<sigma> \<Longrightarrow> \<sigma> \<in> P \<Longrightarrow> TT2 P \<Longrightarrow> \<exists>x. (\<exists>p. x = hide_trace X p \<and> p \<in> P) \<and> \<rho> @ [[Xa \<union> Y]\<^sub>R] \<in> x"
      assume case_assms: "Y \<inter> {e. e \<noteq> Tock \<and> (\<exists>x. (\<exists>p. x = hide_trace X p \<and> p \<in> P) \<and> \<rho> @ [[e]\<^sub>E] \<in> x) \<or>
                e = Tock \<and> (\<exists>x. (\<exists>p. x = hide_trace X p \<and> p \<in> P) \<and> \<rho> @ [[Xa]\<^sub>R, [e]\<^sub>E] \<in> x)} = {}"
        "[Xb]\<^sub>R # [Tock]\<^sub>E # \<sigma> \<in> P" "TT2 P" "Tock \<in> X" "\<rho> @ [[Xa]\<^sub>R] \<in> hide_trace X \<sigma>"
      have "{e. e \<noteq> Tock \<and> (\<exists>x. (\<exists>p. x = hide_trace X p \<and> p \<in> {\<sigma>. [Xb]\<^sub>R # [Tock]\<^sub>E # \<sigma> \<in> P}) \<and> \<rho> @ [[e]\<^sub>E] \<in> x) \<or>
          e = Tock \<and> (\<exists>x. (\<exists>p. x = hide_trace X p \<and> p \<in> {\<sigma>. [Xb]\<^sub>R # [Tock]\<^sub>E # \<sigma> \<in> P}) \<and> \<rho> @ [[Xa]\<^sub>R, [e]\<^sub>E] \<in> x)} \<subseteq>
        {e. e \<noteq> Tock \<and> (\<exists>x. (\<exists>p. x = hide_trace X p \<and> p \<in> P) \<and> \<rho> @ [[e]\<^sub>E] \<in> x) \<or>
          e = Tock \<and> (\<exists>x. (\<exists>p. x = hide_trace X p \<and> p \<in> P) \<and> \<rho> @ [[Xa]\<^sub>R, [e]\<^sub>E] \<in> x)}"
        using case_assms(2) case_assms(4) case_assms(5) by (auto)
      then have 1: "Y \<inter> {e. e \<noteq> Tock \<and> (\<exists>x. (\<exists>p. x = hide_trace X p \<and> p \<in> {\<sigma>. [Xb]\<^sub>R # [Tock]\<^sub>E # \<sigma> \<in> P}) \<and> \<rho> @ [[e]\<^sub>E] \<in> x) \<or>
          e = Tock \<and> (\<exists>x. (\<exists>p. x = hide_trace X p \<and> p \<in> {\<sigma>. [Xb]\<^sub>R # [Tock]\<^sub>E # \<sigma> \<in> P}) \<and> \<rho> @ [[Xa]\<^sub>R, [e]\<^sub>E] \<in> x)} = {}"
        by (smt case_assms(1) disjoint_iff_not_equal subsetCE)
      have 2: "TT2 {\<sigma>. [Xb]\<^sub>R # [Tock]\<^sub>E # \<sigma> \<in> P}"
        using case_assms(3) unfolding TT2_def by (auto, erule_tac x="[Xb]\<^sub>R # [Tock]\<^sub>E # \<rho>" in allE, auto)
      have "\<exists>x. (\<exists>p. x = hide_trace X p \<and> p \<in> {\<sigma>. [Xb]\<^sub>R # [Tock]\<^sub>E # \<sigma> \<in> P}) \<and> \<rho> @ [[Xa \<union> Y]\<^sub>R] \<in> x"
        using ind_hyp[where P="{\<sigma>. [Xb]\<^sub>R # [Tock]\<^sub>E # \<sigma> \<in> P}", where \<rho>=\<rho>] 1 2 case_assms by auto
      then obtain x p where "x = hide_trace X p \<and> p \<in> {\<sigma>. [Xb]\<^sub>R # [Tock]\<^sub>E # \<sigma> \<in> P} \<and> \<rho> @ [[Xa \<union> Y]\<^sub>R] \<in> x"
        by auto
      then show "\<exists>x. (\<exists>p. x = hide_trace X p \<and> p \<in> P) \<and> \<rho> @ [[Xa \<union> Y]\<^sub>R] \<in> x"
        using case_assms by (rule_tac x="hide_trace X ([Xb]\<^sub>R # [Tock]\<^sub>E # p)" in exI, simp, rule_tac x="[Xb]\<^sub>R # [Tock]\<^sub>E # p" in exI, simp)
    next
      fix Xb \<sigma> P \<rho> s' Z
      assume ind_hyp: "\<And>P \<rho>. Y \<inter> {e. e \<noteq> Tock \<and> (\<exists>x. (\<exists>p. x = hide_trace X p \<and> p \<in> P) \<and> \<rho> @ [[e]\<^sub>E] \<in> x) \<or>
                       e = Tock \<and> (\<exists>x. (\<exists>p. x = hide_trace X p \<and> p \<in> P) \<and> \<rho> @ [[Xa]\<^sub>R, [e]\<^sub>E] \<in> x)} = {} \<Longrightarrow>
        \<rho> @ [[Xa]\<^sub>R] \<in> hide_trace X \<sigma> \<Longrightarrow> \<sigma> \<in> P \<Longrightarrow> TT2 P \<Longrightarrow> \<exists>x. (\<exists>p. x = hide_trace X p \<and> p \<in> P) \<and> \<rho> @ [[Xa \<union> Y]\<^sub>R] \<in> x"
      assume case_assms: "Y \<inter> {e. e \<noteq> Tock \<and> (\<exists>x. (\<exists>p. x = hide_trace X p \<and> p \<in> P) \<and> \<rho> @ [[e]\<^sub>E] \<in> x) \<or>
                e = Tock \<and> (\<exists>x. (\<exists>p. x = hide_trace X p \<and> p \<in> P) \<and> \<rho> @ [[Xa]\<^sub>R, [e]\<^sub>E] \<in> x)} = {}"
        "[Xb]\<^sub>R # [Tock]\<^sub>E # \<sigma> \<in> P" "TT2 P" "Z \<subseteq> Xb" "Tock \<notin> X" "X \<subseteq> Xb" "\<rho> @ [[Xa]\<^sub>R] = [Z]\<^sub>R # [Tock]\<^sub>E # s'" "s' \<in> hide_trace X \<sigma>"
      then obtain \<rho>' where \<rho>'_assms: "\<rho> = [Z]\<^sub>R # [Tock]\<^sub>E # \<rho>' \<and> \<rho>' @ [[Xa]\<^sub>R] \<in> hide_trace X \<sigma>"
        by (cases \<rho> rule:ttWF.cases, simp_all, blast)
      have "{e. e \<noteq> Tock \<and> (\<exists>x. (\<exists>p. x = hide_trace X p \<and> p \<in> {\<sigma>. [Xb]\<^sub>R # [Tock]\<^sub>E # \<sigma> \<in> P}) \<and> \<rho>' @ [[e]\<^sub>E] \<in> x) \<or>
          e = Tock \<and> (\<exists>x. (\<exists>p. x = hide_trace X p \<and> p \<in> {\<sigma>. [Xb]\<^sub>R # [Tock]\<^sub>E # \<sigma> \<in> P}) \<and> \<rho>' @ [[Xa]\<^sub>R, [e]\<^sub>E] \<in> x)} \<subseteq>
        {e. e \<noteq> Tock \<and> (\<exists>x. (\<exists>p. x = hide_trace X p \<and> p \<in> P) \<and> \<rho> @ [[e]\<^sub>E] \<in> x) \<or>
          e = Tock \<and> (\<exists>x. (\<exists>p. x = hide_trace X p \<and> p \<in> P) \<and> \<rho> @ [[Xa]\<^sub>R, [e]\<^sub>E] \<in> x)}"
        using case_assms \<rho>'_assms apply (safe, simp_all)
        apply (rule_tac x="hide_trace X ([Xb]\<^sub>R # [Tock]\<^sub>E # p)" in exI, simp, safe, rule_tac x="[Xb]\<^sub>R # [Tock]\<^sub>E # p" in exI, simp)
        apply (rule_tac x="hide_trace X ([Xb]\<^sub>R # [Tock]\<^sub>E # p)" in exI, simp, rule_tac x="[Xb]\<^sub>R # [Tock]\<^sub>E # p" in exI, simp)
        apply (erule_tac x="hide_trace X ([Xb]\<^sub>R # [Tock]\<^sub>E # p)" in allE, simp)
        by (erule_tac x="hide_trace X ([Xb]\<^sub>R # [Tock]\<^sub>E # p)" in allE, simp)
      then have 1: "Y \<inter> {e. e \<noteq> Tock \<and> (\<exists>x. (\<exists>p. x = hide_trace X p \<and> p \<in> {\<sigma>. [Xb]\<^sub>R # [Tock]\<^sub>E # \<sigma> \<in> P}) \<and> \<rho>' @ [[e]\<^sub>E] \<in> x) \<or>
          e = Tock \<and> (\<exists>x. (\<exists>p. x = hide_trace X p \<and> p \<in> {\<sigma>. [Xb]\<^sub>R # [Tock]\<^sub>E # \<sigma> \<in> P}) \<and> \<rho>' @ [[Xa]\<^sub>R, [e]\<^sub>E] \<in> x)} = {}"
        by (smt case_assms(1) disjoint_iff_not_equal subsetCE)
      have 2: "TT2 {\<sigma>. [Xb]\<^sub>R # [Tock]\<^sub>E # \<sigma> \<in> P}"
        using case_assms(3) unfolding TT2_def by (auto, erule_tac x="[Xb]\<^sub>R # [Tock]\<^sub>E # \<rho>" in allE, auto)
      have "\<exists>x. (\<exists>p. x = hide_trace X p \<and> p \<in> {\<sigma>. [Xb]\<^sub>R # [Tock]\<^sub>E # \<sigma> \<in> P}) \<and> \<rho>' @ [[Xa \<union> Y]\<^sub>R] \<in> x"
        using ind_hyp[where P="{\<sigma>. [Xb]\<^sub>R # [Tock]\<^sub>E # \<sigma> \<in> P}", where \<rho>=\<rho>'] 1 2 case_assms \<rho>'_assms by auto
      then obtain x p where "x = hide_trace X p \<and> p \<in> {\<sigma>. [Xb]\<^sub>R # [Tock]\<^sub>E # \<sigma> \<in> P} \<and> \<rho>' @ [[Xa \<union> Y]\<^sub>R] \<in> x"
        by auto
      then show "\<exists>x. (\<exists>p. x = hide_trace X p \<and> p \<in> P) \<and> \<rho> @ [[Xa \<union> Y]\<^sub>R] \<in> x"
        using case_assms \<rho>'_assms by (rule_tac x="hide_trace X ([Xb]\<^sub>R # [Tock]\<^sub>E # p)" in exI, auto)
    qed
  qed
qed

lemma TT2s_Hiding:
  assumes "TT2s P"
  shows "TT2s (P \<setminus>\<^sub>C X)"
  unfolding TT2s_def HidingTT_def
proof auto
  fix Xa Y p
  show "\<And> \<rho> \<sigma>. Y \<inter> {e. e \<noteq> Tock \<and> (\<exists>x. (\<exists>p. x = hide_trace X p \<and> p \<in> P) \<and> \<rho> @ [[e]\<^sub>E] \<in> x) \<or>
                e = Tock \<and> (\<exists>x. (\<exists>p. x = hide_trace X p \<and> p \<in> P) \<and> \<rho> @ [[Xa]\<^sub>R, [e]\<^sub>E] \<in> x)} = {} \<Longrightarrow>
    \<rho> @ [Xa]\<^sub>R # \<sigma> \<in> hide_trace X p \<Longrightarrow> p \<in> P \<Longrightarrow> \<exists>x. (\<exists>p. x = hide_trace X p \<and> p \<in> P) \<and> \<rho> @ [Xa \<union> Y]\<^sub>R # \<sigma> \<in> x"
    using assms
  proof -
    show "\<And>P \<rho> \<sigma>. Y \<inter> {e. e \<noteq> Tock \<and> (\<exists>x. (\<exists>p. x = hide_trace X p \<and> p \<in> P) \<and> \<rho> @ [[e]\<^sub>E] \<in> x) \<or>
                   e = Tock \<and> (\<exists>x. (\<exists>p. x = hide_trace X p \<and> p \<in> P) \<and> \<rho> @ [[Xa]\<^sub>R, [e]\<^sub>E] \<in> x)} = {} \<Longrightarrow>
           \<rho> @ [Xa]\<^sub>R # \<sigma> \<in> hide_trace X p \<Longrightarrow> p \<in> P \<Longrightarrow> TT2s P \<Longrightarrow> \<exists>x. (\<exists>p. x = hide_trace X p \<and> p \<in> P) \<and> \<rho> @ [Xa \<union> Y]\<^sub>R # \<sigma> \<in> x"
    proof (induct p rule:ttWF.induct, simp_all, safe)
      fix Xb P \<rho> \<sigma> Z
      assume case_assms: "Y \<inter> {e. e \<noteq> Tock \<and> (\<exists>x. (\<exists>p. x = hide_trace X p \<and> p \<in> P) \<and> \<rho> @ [[e]\<^sub>E] \<in> x) \<or>
                e = Tock \<and> (\<exists>x. (\<exists>p. x = hide_trace X p \<and> p \<in> P) \<and> \<rho> @ [[Xa]\<^sub>R, [e]\<^sub>E] \<in> x)} = {}"
        "[[Xb]\<^sub>R] \<in> P" "TT2s P" "Z \<subseteq> Xb" "X \<subseteq> Xb" "\<rho> @ [Xa]\<^sub>R # \<sigma> = [[Z]\<^sub>R]"
      have 1: "Z = Xa \<and> \<rho> = [] \<and> \<sigma> = []"
        by (metis (no_types, lifting) Nil_is_append_conv append_eq_Cons_conv case_assms(6) cttobs.inject(2) list.distinct(1) list.inject)
      then have "{e. e \<notin> X \<and> (e \<noteq> Tock \<and> \<rho> @ [[e]\<^sub>E] \<in> P \<or> e = Tock \<and> \<rho> @ [[Xb]\<^sub>R, [e]\<^sub>E] \<in> P)}
        \<subseteq> {e. e \<noteq> Tock \<and> (\<exists>x. (\<exists>p. x = hide_trace X p \<and> p \<in> P) \<and> \<rho> @ [[e]\<^sub>E] \<in> x) \<or>
          e = Tock \<and> (\<exists>x. (\<exists>p. x = hide_trace X p \<and> p \<in> P) \<and> \<rho> @ [[Xa]\<^sub>R, [e]\<^sub>E] \<in> x)}"
      proof auto
        fix x
        assume "[[x]\<^sub>E] \<in> P" "x \<noteq> Tock" "x \<notin> X"
        then show "\<exists>xa. (\<exists>p. xa = hide_trace X p \<and> p \<in> P) \<and> [[x]\<^sub>E] \<in> xa"
          by (rule_tac x="hide_trace X [[x]\<^sub>E]" in exI, cases x, force+)
      next
        fix x
        assume "[[x]\<^sub>E] \<in> P" "x \<noteq> Tock" "x \<notin> X"
        then show "\<exists>xa. (\<exists>p. xa = hide_trace X p \<and> p \<in> P) \<and> [[x]\<^sub>E] \<in> xa"
          by (rule_tac x="hide_trace X [[x]\<^sub>E]" in exI, cases x, force+)
      next
        assume "[[Xb]\<^sub>R, [Tock]\<^sub>E] \<in> P" "Tock \<notin> X"
        then show "\<forall>x. (\<forall>p. x = hide_trace X p \<longrightarrow> p \<notin> P) \<or> [[Xa]\<^sub>R, [Tock]\<^sub>E] \<notin> x \<Longrightarrow> False"
          using 1 case_assms by (erule_tac x="hide_trace X [[Xb]\<^sub>R, [Tock]\<^sub>E]" in allE, auto)
      next
        assume "[[Xb]\<^sub>R, [Tock]\<^sub>E] \<in> P" "Tock \<notin> X"
        then show "\<forall>x. (\<forall>p. x = hide_trace X p \<longrightarrow> p \<notin> P) \<or> [[Xa]\<^sub>R, [Tock]\<^sub>E] \<notin> x \<Longrightarrow>
          \<exists>x. (\<exists>p. x = hide_trace X p \<and> p \<in> P) \<and> [[Tock]\<^sub>E] \<in> x"
          using 1 case_assms by (erule_tac x="hide_trace X [[Xb]\<^sub>R, [Tock]\<^sub>E]" in allE, auto)
      qed
      then have "{e. e \<in> Y \<and> e \<notin> X} \<inter> {e. (e \<noteq> Tock \<and> \<rho> @ [[e]\<^sub>E] \<in> P \<or> e = Tock \<and> \<rho> @ [[Xb]\<^sub>R, [e]\<^sub>E] \<in> P)} = {}"
        using case_assms(1) by auto
      then have "[[Xb \<union> {e. e \<in> Y \<and> e \<notin> X}]\<^sub>R] \<in> P"
        using case_assms 1 unfolding TT2s_def by (erule_tac x="[]" in allE, force)
      then have "Xb \<union> {e. e \<in> Y \<and> e \<notin> X} = Xb \<union> Y \<Longrightarrow> [[Xb \<union> Y]\<^sub>R] \<in> P"
        by auto
      then have "[[Xb \<union> Y]\<^sub>R] \<in> P"
        using case_assms by force
      then show "\<exists>x. (\<exists>p. x = hide_trace X p \<and> p \<in> P) \<and> \<rho> @ [Xa \<union> Y]\<^sub>R # \<sigma> \<in> x"
        using 1 case_assms by force
    next
      fix P \<rho> \<sigma>
      assume "\<rho> @ [Xa]\<^sub>R # \<sigma> = [[Tick]\<^sub>E]"
      then have "False"
        by (meson append_eq_Cons_conv append_is_Nil_conv cttobs.simps(4) list.inject list.simps(3))
      then show "\<exists>x. (\<exists>p. x = hide_trace X p \<and> p \<in> P) \<and> \<rho> @ [Xa \<union> Y]\<^sub>R # \<sigma> \<in> x"
        by auto
    next
      fix e \<sigma> P \<rho> \<sigma>'
      assume ind_hyp: "\<And>P \<rho> \<sigma>'. Y \<inter> {e. e \<noteq> Tock \<and> (\<exists>x. (\<exists>p. x = hide_trace X p \<and> p \<in> P) \<and> \<rho> @ [[e]\<^sub>E] \<in> x) \<or>
                          e = Tock \<and> (\<exists>x. (\<exists>p. x = hide_trace X p \<and> p \<in> P) \<and> \<rho> @ [[Xa]\<^sub>R, [e]\<^sub>E] \<in> x)} = {} \<Longrightarrow>
        \<rho> @ [Xa]\<^sub>R # \<sigma>' \<in> hide_trace X \<sigma> \<Longrightarrow> \<sigma> \<in> P \<Longrightarrow> TT2s P \<Longrightarrow> \<exists>x. (\<exists>p. x = hide_trace X p \<and> p \<in> P) \<and> \<rho> @ [Xa \<union> Y]\<^sub>R # \<sigma>' \<in> x"
      assume case_assms: "Y \<inter> {e. e \<noteq> Tock \<and> (\<exists>x. (\<exists>p. x = hide_trace X p \<and> p \<in> P) \<and> \<rho> @ [[e]\<^sub>E] \<in> x) \<or>
                e = Tock \<and> (\<exists>x. (\<exists>p. x = hide_trace X p \<and> p \<in> P) \<and> \<rho> @ [[Xa]\<^sub>R, [e]\<^sub>E] \<in> x)} = {}"
        "[Event e]\<^sub>E # \<sigma> \<in> P" "TT2s P" "Event e \<in> X" "\<rho> @ [Xa]\<^sub>R # \<sigma>' \<in> hide_trace X \<sigma>"
      have  1: "TT2s {x. [Event e]\<^sub>E # x \<in> P}"
        by (simp add: TT2s_init_event case_assms(3))
      then have "\<exists>x. (\<exists>p. x = hide_trace X p \<and> p \<in> {x. [Event e]\<^sub>E # x \<in> P}) \<and> \<rho> @ [Xa \<union> Y]\<^sub>R # \<sigma>' \<in> x"
        using case_assms 1 ind_hyp[where P ="{x. [Event e]\<^sub>E # x \<in> P}", where \<rho>=\<rho>, where \<sigma>'=\<sigma>'] by force
      then show "\<exists>x. (\<exists>p. x = hide_trace X p \<and> p \<in> P) \<and> \<rho> @ [Xa \<union> Y]\<^sub>R # \<sigma>' \<in> x"
        using case_assms by auto
    next
      fix e \<sigma> P \<rho> \<sigma>' s'
      assume ind_hyp: "\<And>P \<rho> \<sigma>'. Y \<inter> {e. e \<noteq> Tock \<and> (\<exists>x. (\<exists>p. x = hide_trace X p \<and> p \<in> P) \<and> \<rho> @ [[e]\<^sub>E] \<in> x) \<or>
                          e = Tock \<and> (\<exists>x. (\<exists>p. x = hide_trace X p \<and> p \<in> P) \<and> \<rho> @ [[Xa]\<^sub>R, [e]\<^sub>E] \<in> x)} = {} \<Longrightarrow>
        \<rho> @ [Xa]\<^sub>R # \<sigma>' \<in> hide_trace X \<sigma> \<Longrightarrow> \<sigma> \<in> P \<Longrightarrow> TT2s P \<Longrightarrow> \<exists>x. (\<exists>p. x = hide_trace X p \<and> p \<in> P) \<and> \<rho> @ [Xa \<union> Y]\<^sub>R # \<sigma>' \<in> x"
      assume case_assms: "Y \<inter> {e. e \<noteq> Tock \<and> (\<exists>x. (\<exists>p. x = hide_trace X p \<and> p \<in> P) \<and> \<rho> @ [[e]\<^sub>E] \<in> x) \<or>
                e = Tock \<and> (\<exists>x. (\<exists>p. x = hide_trace X p \<and> p \<in> P) \<and> \<rho> @ [[Xa]\<^sub>R, [e]\<^sub>E] \<in> x)} = {}"
        "[Event e]\<^sub>E # \<sigma> \<in> P" "TT2s P" "Event e \<notin> X" "s' \<in> hide_trace X \<sigma>" "\<rho> @ [Xa]\<^sub>R # \<sigma>' = [Event e]\<^sub>E # s'"
      obtain \<rho>' where s'_def: "s' = \<rho>' @ [Xa]\<^sub>R # \<sigma>'"
        using case_assms(6) by (cases \<rho> rule:ttWF.cases, auto)
      have "{ea. ea \<noteq> Tock \<and> (\<exists>x. (\<exists>p. x = hide_trace X p \<and> p \<in> {x. [Event e]\<^sub>E # x \<in> P}) \<and> \<rho>' @ [[ea]\<^sub>E] \<in> x) \<or>
          ea = Tock \<and> (\<exists>x. (\<exists>p. x = hide_trace X p \<and> p \<in> {x. [Event e]\<^sub>E # x \<in> P}) \<and> \<rho>' @ [[Xa]\<^sub>R, [ea]\<^sub>E] \<in> x)}
        \<subseteq> {e. e \<noteq> Tock \<and> (\<exists>x. (\<exists>p. x = hide_trace X p \<and> p \<in> P) \<and> \<rho> @ [[e]\<^sub>E] \<in> x) \<or>
          e = Tock \<and> (\<exists>x. (\<exists>p. x = hide_trace X p \<and> p \<in> P) \<and> \<rho> @ [[Xa]\<^sub>R, [e]\<^sub>E] \<in> x)}"
        using s'_def case_assms(4) case_assms(6) by auto
      then have 1: "Y \<inter> {ea. ea \<noteq> Tock \<and> (\<exists>x. (\<exists>p. x = hide_trace X p \<and> p \<in> {x. [Event e]\<^sub>E # x \<in> P}) \<and> \<rho>' @ [[ea]\<^sub>E] \<in> x) \<or>
          ea = Tock \<and> (\<exists>x. (\<exists>p. x = hide_trace X p \<and> p \<in> {x. [Event e]\<^sub>E # x \<in> P}) \<and> \<rho>' @ [[Xa]\<^sub>R, [ea]\<^sub>E] \<in> x)} = {}"
        by (smt case_assms(1) disjoint_iff_not_equal subsetCE)
      have 2: "TT2s {x. [Event e]\<^sub>E # x \<in> P}"
        by (simp add: TT2s_init_event case_assms(3))
      have "\<exists>x. (\<exists>p. x = hide_trace X p \<and> p \<in> {x. [Event e]\<^sub>E # x \<in> P}) \<and> \<rho>' @ [Xa \<union> Y]\<^sub>R # \<sigma>' \<in> x"
        using case_assms 1 2 s'_def ind_hyp[where P ="{x. [Event e]\<^sub>E # x \<in> P}", where \<rho>=\<rho>', where \<sigma>'=\<sigma>'] by force
      then show "\<exists>x. (\<exists>p. x = hide_trace X p \<and> p \<in> P) \<and> \<rho> @ [Xa \<union> Y]\<^sub>R # \<sigma>' \<in> x"
        using case_assms s'_def by force
    next
      fix Xb \<sigma> P \<rho> \<sigma>'
      assume ind_hyp: "\<And>P \<rho> \<sigma>'. Y \<inter> {e. e \<noteq> Tock \<and> (\<exists>x. (\<exists>p. x = hide_trace X p \<and> p \<in> P) \<and> \<rho> @ [[e]\<^sub>E] \<in> x) \<or>
          e = Tock \<and> (\<exists>x. (\<exists>p. x = hide_trace X p \<and> p \<in> P) \<and> \<rho> @ [[Xa]\<^sub>R, [e]\<^sub>E] \<in> x)} = {} \<Longrightarrow>
        \<rho> @ [Xa]\<^sub>R # \<sigma>' \<in> hide_trace X \<sigma> \<Longrightarrow> \<sigma> \<in> P \<Longrightarrow> TT2s P \<Longrightarrow> \<exists>x. (\<exists>p. x = hide_trace X p \<and> p \<in> P) \<and> \<rho> @ [Xa \<union> Y]\<^sub>R # \<sigma>' \<in> x"
      assume case_assms: "Y \<inter> {e. e \<noteq> Tock \<and> (\<exists>x. (\<exists>p. x = hide_trace X p \<and> p \<in> P) \<and> \<rho> @ [[e]\<^sub>E] \<in> x) \<or>
                e = Tock \<and> (\<exists>x. (\<exists>p. x = hide_trace X p \<and> p \<in> P) \<and> \<rho> @ [[Xa]\<^sub>R, [e]\<^sub>E] \<in> x)} = {}"
        "[Xb]\<^sub>R # [Tock]\<^sub>E # \<sigma> \<in> P" "TT2s P" "Tock \<in> X" "\<rho> @ [Xa]\<^sub>R # \<sigma>' \<in> hide_trace X \<sigma>"
      have 1: "TT2s {x. [Xb]\<^sub>R # [Tock]\<^sub>E # x \<in> P}"
        by (simp add: TT2s_init_tock case_assms(3))
      have "\<exists>x. (\<exists>p. x = hide_trace X p \<and> p \<in> {x. [Xb]\<^sub>R # [Tock]\<^sub>E # x \<in> P}) \<and> \<rho> @ [Xa \<union> Y]\<^sub>R # \<sigma>' \<in> x"
        using case_assms 1 ind_hyp[where P ="{x. [Xb]\<^sub>R # [Tock]\<^sub>E # x \<in> P}", where \<rho>=\<rho>, where \<sigma>'=\<sigma>'] by force
      then show "\<exists>x. (\<exists>p. x = hide_trace X p \<and> p \<in> P) \<and> \<rho> @ [Xa \<union> Y]\<^sub>R # \<sigma>' \<in> x"
        using case_assms by force
    next
      fix Xb \<sigma> P \<rho> \<sigma>' s' Z
      assume ind_hyp: "\<And>P \<rho> \<sigma>'. Y \<inter> {e. e \<noteq> Tock \<and> (\<exists>x. (\<exists>p. x = hide_trace X p \<and> p \<in> P) \<and> \<rho> @ [[e]\<^sub>E] \<in> x) \<or>
                          e = Tock \<and> (\<exists>x. (\<exists>p. x = hide_trace X p \<and> p \<in> P) \<and> \<rho> @ [[Xa]\<^sub>R, [e]\<^sub>E] \<in> x)} = {} \<Longrightarrow>
        \<rho> @ [Xa]\<^sub>R # \<sigma>' \<in> hide_trace X \<sigma> \<Longrightarrow> \<sigma> \<in> P \<Longrightarrow> TT2s P \<Longrightarrow> \<exists>x. (\<exists>p. x = hide_trace X p \<and> p \<in> P) \<and> \<rho> @ [Xa \<union> Y]\<^sub>R # \<sigma>' \<in> x"
      assume case_assms: "Y \<inter> {e. e \<noteq> Tock \<and> (\<exists>x. (\<exists>p. x = hide_trace X p \<and> p \<in> P) \<and> \<rho> @ [[e]\<^sub>E] \<in> x) \<or>
                e = Tock \<and> (\<exists>x. (\<exists>p. x = hide_trace X p \<and> p \<in> P) \<and> \<rho> @ [[Xa]\<^sub>R, [e]\<^sub>E] \<in> x)} = {}"
        "[Xb]\<^sub>R # [Tock]\<^sub>E # \<sigma> \<in> P" "TT2s P" "Z \<subseteq> Xb" "Tock \<notin> X" "X \<subseteq> Xb" "\<rho> @ [Xa]\<^sub>R # \<sigma>' = [Z]\<^sub>R # [Tock]\<^sub>E # s'" "s' \<in> hide_trace X \<sigma>"
      have 1: "TT2s {x. [Xb]\<^sub>R # [Tock]\<^sub>E # x \<in> P}"
          using TT2s_init_tock case_assms(3) by blast
      have "(\<exists> \<rho>'. s' = \<rho>' @ [Xa]\<^sub>R # \<sigma>') \<or> (\<rho> = [] \<and> Z = Xa \<and> \<sigma>' = [Tock]\<^sub>E # s')"
        using case_assms(7) by (cases \<rho> rule:ttWF.cases, auto)
      then show "\<exists>x. (\<exists>p. x = hide_trace X p \<and> p \<in> P) \<and> \<rho> @ [Xa \<union> Y]\<^sub>R # \<sigma>' \<in> x"
      proof auto
        fix \<rho>'
        assume case_assm2: "s' = \<rho>' @ [Xa]\<^sub>R # \<sigma>'"
        have "{ea. ea \<noteq> Tock \<and> (\<exists>x. (\<exists>p. x = hide_trace X p \<and> p \<in> {x. [Xb]\<^sub>R # [Tock]\<^sub>E #  x \<in> P}) \<and> \<rho>' @ [[ea]\<^sub>E] \<in> x) \<or>
          ea = Tock \<and> (\<exists>x. (\<exists>p. x = hide_trace X p \<and> p \<in> {x. [Xb]\<^sub>R # [Tock]\<^sub>E #  x \<in> P}) \<and> \<rho>' @ [[Xa]\<^sub>R, [ea]\<^sub>E] \<in> x)}
        \<subseteq> {e. e \<noteq> Tock \<and> (\<exists>x. (\<exists>p. x = hide_trace X p \<and> p \<in> P) \<and> \<rho> @ [[e]\<^sub>E] \<in> x) \<or>                                     
          e = Tock \<and> (\<exists>x. (\<exists>p. x = hide_trace X p \<and> p \<in> P) \<and> \<rho> @ [[Xa]\<^sub>R, [e]\<^sub>E] \<in> x)}"
          using case_assm2 case_assms by auto
        then have 2: "Y \<inter> {ea. ea \<noteq> Tock \<and> (\<exists>x. (\<exists>p. x = hide_trace X p \<and> p \<in> {x. [Xb]\<^sub>R # [Tock]\<^sub>E #  x \<in> P}) \<and> \<rho>' @ [[ea]\<^sub>E] \<in> x) \<or>
          ea = Tock \<and> (\<exists>x. (\<exists>p. x = hide_trace X p \<and> p \<in> {x. [Xb]\<^sub>R # [Tock]\<^sub>E #  x \<in> P}) \<and> \<rho>' @ [[Xa]\<^sub>R, [ea]\<^sub>E] \<in> x)} = {}"
          by (smt case_assms(1) disjoint_iff_not_equal subsetCE)
        have "\<exists>x. (\<exists>p. x = hide_trace X p \<and> p \<in> {x. [Xb]\<^sub>R # [Tock]\<^sub>E # x \<in> P}) \<and> \<rho>' @ [Xa \<union> Y]\<^sub>R # \<sigma>' \<in> x"
          using case_assms case_assm2 1 2 ind_hyp[where P ="{x. [Xb]\<^sub>R # [Tock]\<^sub>E # x \<in> P}", where \<rho>=\<rho>', where \<sigma>'=\<sigma>'] by force
        then show "\<exists>x. (\<exists>p. x = hide_trace X p \<and> p \<in> P) \<and> \<rho> @ [Xa \<union> Y]\<^sub>R # \<sigma>' \<in> x"
          using case_assms case_assm2 by force
      next
        assume case_assms2: "\<rho> = []" "Z = Xa" "\<sigma>' = [Tock]\<^sub>E # s'"
        have "{e. e \<notin> X \<and> (e \<noteq> Tock \<and> \<rho> @ [[e]\<^sub>E] \<in> P \<or> e = Tock \<and> \<rho> @ [[Xb]\<^sub>R, [e]\<^sub>E] \<in> P)}
          \<subseteq> {e. e \<noteq> Tock \<and> (\<exists>x. (\<exists>p. x = hide_trace X p \<and> p \<in> P) \<and> \<rho> @ [[e]\<^sub>E] \<in> x) \<or>
                e = Tock \<and> (\<exists>x. (\<exists>p. x = hide_trace X p \<and> p \<in> P) \<and> \<rho> @ [[Xa]\<^sub>R, [e]\<^sub>E] \<in> x)}"
          using case_assms case_assms2 by (auto, (case_tac x, auto)+)
        then have "{e. e \<notin> X \<and> e \<in> Y} \<inter> {e. e \<noteq> Tock \<and> \<rho> @ [[e]\<^sub>E] \<in> P \<or> e = Tock \<and> \<rho> @ [[Xb]\<^sub>R, [e]\<^sub>E] \<in> P} = {}"
          using case_assms(1) by auto
        then have "[Xb \<union> {e. e \<notin> X \<and> e \<in> Y}]\<^sub>R # [Tock]\<^sub>E # \<sigma> \<in> P"
          using case_assms case_assms2 unfolding TT2s_def by (erule_tac x="[]" in allE, force)
        then have "Xb \<union> {e. e \<notin> X \<and> e \<in> Y} = Xb \<union> Y \<Longrightarrow> [Xb \<union> Y]\<^sub>R # [Tock]\<^sub>E # \<sigma> \<in> P"
          by auto
        then have "[Xb \<union> Y]\<^sub>R # [Tock]\<^sub>E # \<sigma> \<in> P"
          using case_assms by force
        then show "\<exists>x. (\<exists>p. x = hide_trace X p \<and> p \<in> P) \<and> [Xa \<union> Y]\<^sub>R # [Tock]\<^sub>E # s' \<in> x"
          using case_assms case_assms2 by force
      qed
    qed
  qed
qed
 
lemma TT3_Hiding:
  "TT3 P \<Longrightarrow> TT3 (P \<setminus>\<^sub>C X)"
  unfolding TT3_def HidingTT_def
proof (safe, simp_all)
  fix p
  show "\<And>P x. Ball P TT3_trace \<Longrightarrow> x \<in> hide_trace X p \<Longrightarrow> p \<in> P \<Longrightarrow> TT3_trace x"
  proof (induct p rule:ttWF.induct)
    fix P x
    show "Ball P TT3_trace \<Longrightarrow> x \<in> hide_trace X [] \<Longrightarrow> [] \<in> P \<Longrightarrow> TT3_trace x"
      by (cases x, simp_all)
  next
    fix Xa P x
    show "Ball P TT3_trace \<Longrightarrow> x \<in> hide_trace X [[Xa]\<^sub>R] \<Longrightarrow> [[Xa]\<^sub>R] \<in> P \<Longrightarrow> TT3_trace x"
      by (cases x, simp_all, case_tac a, simp_all)
  next
    fix P x
    show "Ball P TT3_trace \<Longrightarrow> x \<in> hide_trace X [[Tick]\<^sub>E] \<Longrightarrow> [[Tick]\<^sub>E] \<in> P \<Longrightarrow> TT3_trace x"
      by (cases x, simp_all)
  next
    fix e \<sigma> P x
    assume ind_hyp: "\<And>P x. Ball P TT3_trace \<Longrightarrow> x \<in> hide_trace X \<sigma> \<Longrightarrow> \<sigma> \<in> P \<Longrightarrow> TT3_trace x"
    assume case_assms: "Ball P TT3_trace" "x \<in> hide_trace X ([Event e]\<^sub>E # \<sigma>)" "[Event e]\<^sub>E # \<sigma> \<in> P"
    have 1: "Ball {\<sigma>. [Event e]\<^sub>E # \<sigma> \<in> P} TT3_trace"
      using case_assms(1)
      using TT3_trace_cons_imp_cons by blast
    show "TT3_trace x"
    proof (cases "Event e \<in> X")
      assume case_assms2: "Event e \<in> X"
      then have "x \<in> hide_trace X \<sigma>"
        using case_assms(2) by auto
      then show "TT3_trace x"
        using ind_hyp[where P="{\<sigma>. [Event e]\<^sub>E # \<sigma> \<in> P}", where x=x] case_assms(3) case_assms2 1 by blast
    next
      assume case_assms2: "Event e \<notin> X"
      then obtain x' where x'_assms: "x = [Event e]\<^sub>E # x' \<and> x' \<in> hide_trace X \<sigma>"
        using case_assms(2) by (cases x, auto)
      then have "TT3_trace x'"
        using ind_hyp[where P="{\<sigma>. [Event e]\<^sub>E # \<sigma> \<in> P}", where x=x'] case_assms(3) case_assms2 1 by blast
      then show "TT3_trace x"
        using x'_assms by (cases x', simp_all)
    qed
  next
    fix Xa \<sigma> P x
    assume ind_hyp: "\<And>P x. Ball P TT3_trace \<Longrightarrow> x \<in> hide_trace X \<sigma> \<Longrightarrow> \<sigma> \<in> P \<Longrightarrow> TT3_trace x"
    assume case_assms: "Ball P TT3_trace" "x \<in> hide_trace X ([Xa]\<^sub>R # [Tock]\<^sub>E # \<sigma>)" "[Xa]\<^sub>R # [Tock]\<^sub>E # \<sigma> \<in> P"
    have 1: "Ball {\<sigma>. [Xa]\<^sub>R # [Tock]\<^sub>E # \<sigma> \<in> P} TT3_trace"
      using case_assms(1) by auto
    have 2: "\<sigma> \<in> {\<sigma>. [Xa]\<^sub>R # [Tock]\<^sub>E # \<sigma> \<in> P}"
      using case_assms(3) by auto
    have 3: "Tock \<notin> Xa"
      using case_assms(1) case_assms(3) by auto
    have "(\<exists>X' x'. x = [X']\<^sub>R # [Tock]\<^sub>E # x' \<and> x' \<in> hide_trace X \<sigma> \<and> X' \<subseteq> Xa) \<or> (x \<in> hide_trace X \<sigma>)"
      using case_assms(2) by (cases "X \<subseteq> Xa", auto)
    then show "TT3_trace x"
    proof safe
      fix X' x'
      assume case_assms2: "x = [X']\<^sub>R # [Tock]\<^sub>E # x'" "x' \<in> hide_trace X \<sigma>" "X' \<subseteq> Xa"
      then have "TT3_trace x'"
        using ind_hyp[where P="{\<sigma>. [Xa]\<^sub>R # [Tock]\<^sub>E # \<sigma> \<in> P}", where x=x'] 1 2 by blast
      then show "TT3_trace ([X']\<^sub>R # [Tock]\<^sub>E # x')"
        using case_assms2 3 by auto
    next
      assume case_assms2: "x \<in> hide_trace X \<sigma>"
      then show "TT3_trace x"
        using ind_hyp[where P="{\<sigma>. [Xa]\<^sub>R # [Tock]\<^sub>E # \<sigma> \<in> P}", where x=x] 1 2 by blast
    qed
  next
    fix va P x
    show "x \<in> hide_trace X ([Tock]\<^sub>E # va) \<Longrightarrow> TT3_trace x"
      by simp
  next
    fix va P x
    show "x \<in> hide_trace X ([Tock]\<^sub>E # va) \<Longrightarrow> TT3_trace x"
      by simp
  next
    fix va P x
    show "x \<in> hide_trace X ([Tock]\<^sub>E # va) \<Longrightarrow> TT3_trace x"
      by simp
  next
    fix v vc P x
    show "x \<in> hide_trace X ([Tick]\<^sub>E # v # vc) \<Longrightarrow> TT3_trace x"
      by simp
  next
    fix v vc P x
    show "x \<in> hide_trace X ([Tick]\<^sub>E # v # vc) \<Longrightarrow> TT3_trace x"
      by simp
  next
    fix va vd vc P x
    show "x \<in> hide_trace X ([va]\<^sub>R # [Event vd]\<^sub>E # vc) \<Longrightarrow> TT3_trace x"
      by simp
  next
    fix va vc P x
    show "x \<in> hide_trace X ([va]\<^sub>R # [Tick]\<^sub>E # vc) \<Longrightarrow> TT3_trace x"
      by simp
  next
    fix va v vc P x
    show "x \<in> hide_trace X ([va]\<^sub>R # [v]\<^sub>R # vc) \<Longrightarrow> TT3_trace x"
      by simp
  qed
qed

lemma TT4s_Hiding:
  "TT1 P \<Longrightarrow> TT4s P \<Longrightarrow> TT4s (P \<setminus>\<^sub>C X)"
  unfolding TT4s_def HidingTT_def
proof (safe, simp_all)
  fix p
  show "\<And> \<rho> P. TT1 P \<Longrightarrow> \<forall>\<rho>. \<rho> \<in> P \<longrightarrow> add_Tick_refusal_trace \<rho> \<in> P \<Longrightarrow> \<rho> \<in> hide_trace X p \<Longrightarrow> p \<in> P \<Longrightarrow>
    \<exists>x. (\<exists>p. x = hide_trace X p \<and> p \<in> P) \<and> add_Tick_refusal_trace \<rho> \<in> x"
  proof (induct p rule:hide_trace.induct, auto)
    fix X e s \<rho> P
    assume ind_hyp: "\<And>\<rho> P. TT1 P \<Longrightarrow> \<forall>\<rho>. \<rho> \<in> P \<longrightarrow> add_Tick_refusal_trace \<rho> \<in> P \<Longrightarrow>
               \<rho> \<in> hide_trace X s \<Longrightarrow> s \<in> P \<Longrightarrow> \<exists>x. (\<exists>p. x = hide_trace X p \<and> p \<in> P) \<and> add_Tick_refusal_trace \<rho> \<in> x"
    assume case_assms: "TT1 P" "\<forall>\<rho>. \<rho> \<in> P \<longrightarrow> add_Tick_refusal_trace \<rho> \<in> P" "[Event e]\<^sub>E # s \<in> P" "Event e \<in> X" "\<rho> \<in> hide_trace X s"
    have 1: "\<forall>\<rho>. \<rho> \<in> {s. [Event e]\<^sub>E # s \<in> P} \<longrightarrow> add_Tick_refusal_trace \<rho> \<in> {s. [Event e]\<^sub>E # s \<in> P}"
      using case_assms(2) by force
    have 2: "s \<in> {s. [Event e]\<^sub>E # s \<in> P}"
      by (simp add: case_assms(3))
    have 3: "TT1 {s. [Event e]\<^sub>E # s \<in> P}"
      using case_assms(1) unfolding TT1_def apply auto by (erule_tac x="[Event e]\<^sub>E # \<rho>" in allE, auto)
    have "\<exists>x. (\<exists>p. x = hide_trace X p \<and> p \<in> {s. [Event e]\<^sub>E # s \<in> P}) \<and> add_Tick_refusal_trace \<rho> \<in> x"
      using ind_hyp[where P="{s. [Event e]\<^sub>E # s \<in> P}", where \<rho>=\<rho>] 1 2 3 case_assms by blast
    then show "\<exists>x. (\<exists>p. x = hide_trace X p \<and> p \<in> P) \<and> add_Tick_refusal_trace \<rho> \<in> x"
      using case_assms by auto
  next
    fix X e s P s'
    assume ind_hyp: "\<And>\<rho> P. TT1 P \<Longrightarrow> \<forall>\<rho>. \<rho> \<in> P \<longrightarrow> add_Tick_refusal_trace \<rho> \<in> P \<Longrightarrow>
               \<rho> \<in> hide_trace X s \<Longrightarrow> s \<in> P \<Longrightarrow> \<exists>x. (\<exists>p. x = hide_trace X p \<and> p \<in> P) \<and> add_Tick_refusal_trace \<rho> \<in> x"
    assume case_assms: "TT1 P" "\<forall>\<rho>. \<rho> \<in> P \<longrightarrow> add_Tick_refusal_trace \<rho> \<in> P" "[Event e]\<^sub>E # s \<in> P" "Event e \<notin> X" "s' \<in> hide_trace X s"
    have 1: "\<forall>\<rho>. \<rho> \<in> {s. [Event e]\<^sub>E # s \<in> P} \<longrightarrow> add_Tick_refusal_trace \<rho> \<in> {s. [Event e]\<^sub>E # s \<in> P}"
      using case_assms(2) by force
    have 2: "s \<in> {s. [Event e]\<^sub>E # s \<in> P}"
      by (simp add: case_assms(3))
    have 3: "TT1 {s. [Event e]\<^sub>E # s \<in> P}"
      using case_assms(1) unfolding TT1_def apply auto by (erule_tac x="[Event e]\<^sub>E # \<rho>" in allE, auto)
    have "\<exists>x. (\<exists>p. x = hide_trace X p \<and> p \<in> {s. [Event e]\<^sub>E # s \<in> P}) \<and> add_Tick_refusal_trace s' \<in> x"
      using ind_hyp[where P="{s. [Event e]\<^sub>E # s \<in> P}", where \<rho>=s'] 1 2 3 case_assms by blast
    then show "\<exists>x. (\<exists>p. x = hide_trace X p \<and> p \<in> P) \<and> [Event e]\<^sub>E # add_Tick_refusal_trace s' \<in> x"
      using case_assms by auto
  next
    fix X Y s \<rho> P
    assume ind_hyp: "\<And>\<rho> P. TT1 P \<Longrightarrow> \<forall>\<rho>. \<rho> \<in> P \<longrightarrow> add_Tick_refusal_trace \<rho> \<in> P \<Longrightarrow>
               \<rho> \<in> hide_trace X s \<Longrightarrow> s \<in> P \<Longrightarrow> \<exists>x. (\<exists>p. x = hide_trace X p \<and> p \<in> P) \<and> add_Tick_refusal_trace \<rho> \<in> x"
    assume case_assms: "TT1 P" "\<forall>\<rho>. \<rho> \<in> P \<longrightarrow> add_Tick_refusal_trace \<rho> \<in> P" "[Y]\<^sub>R # [Tock]\<^sub>E # s \<in> P" "Tock \<in> X" "\<rho> \<in> hide_trace X s"
    have 1: "\<forall>\<rho>. \<rho> \<in> {s. [Y\<union>{Tick}]\<^sub>R # [Tock]\<^sub>E # s \<in> P} \<longrightarrow> add_Tick_refusal_trace \<rho> \<in> {s. [Y\<union>{Tick}]\<^sub>R # [Tock]\<^sub>E # s \<in> P}"
      using case_assms(2) by force
    have 2: "s \<in> {s. [Y\<union>{Tick}]\<^sub>R # [Tock]\<^sub>E # s \<in> P}"
      using TT4s_TT1_add_Tick_ref_Tock TT4s_def case_assms(1) case_assms(2) case_assms(3) by blast
    have 3: "TT1 {s. [Y\<union>{Tick}]\<^sub>R # [Tock]\<^sub>E # s \<in> P}"
      using case_assms(1) unfolding TT1_def apply auto by (erule_tac x="[insert Tick Y]\<^sub>R # [Tock]\<^sub>E # \<rho>" in allE, auto)
    have "\<exists>x. (\<exists>p. x = hide_trace X p \<and> p \<in> {s. [Y \<union> {Tick}]\<^sub>R # [Tock]\<^sub>E # s \<in> P}) \<and> add_Tick_refusal_trace \<rho> \<in> x"
      using ind_hyp[where P="{s. [Y\<union>{Tick}]\<^sub>R # [Tock]\<^sub>E # s \<in> P}", where \<rho>=\<rho>] 1 2 3 case_assms by blast
    then show "\<exists>x. (\<exists>p. x = hide_trace X p \<and> p \<in> P) \<and> add_Tick_refusal_trace \<rho> \<in> x"
      using case_assms(4) by auto
  next
    fix X Y s P s' Z
    assume ind_hyp: "\<And>\<rho> P. TT1 P \<Longrightarrow> \<forall>\<rho>. \<rho> \<in> P \<longrightarrow> add_Tick_refusal_trace \<rho> \<in> P \<Longrightarrow>
               \<rho> \<in> hide_trace X s \<Longrightarrow> s \<in> P \<Longrightarrow> \<exists>x. (\<exists>p. x = hide_trace X p \<and> p \<in> P) \<and> add_Tick_refusal_trace \<rho> \<in> x"
    assume case_assms: "TT1 P" "\<forall>\<rho>. \<rho> \<in> P \<longrightarrow> add_Tick_refusal_trace \<rho> \<in> P" "[Y]\<^sub>R # [Tock]\<^sub>E # s \<in> P" "Z \<subseteq> Y" "Tock \<notin> X" "X \<subseteq> Y" "s' \<in> hide_trace X s"
    have 1: "\<forall>\<rho>. \<rho> \<in> {s. [Y\<union>{Tick}]\<^sub>R # [Tock]\<^sub>E # s \<in> P} \<longrightarrow> add_Tick_refusal_trace \<rho> \<in> {s. [Y\<union>{Tick}]\<^sub>R # [Tock]\<^sub>E # s \<in> P}"
      using case_assms(2) by force
    have 2: "s \<in> {s. [Y\<union>{Tick}]\<^sub>R # [Tock]\<^sub>E # s \<in> P}"
      using TT4s_TT1_add_Tick_ref_Tock TT4s_def case_assms(1) case_assms(2) case_assms(3) by blast
    have 3: "TT1 {s. [Y\<union>{Tick}]\<^sub>R # [Tock]\<^sub>E # s \<in> P}"
      using case_assms(1) unfolding TT1_def apply auto by (erule_tac x="[insert Tick Y]\<^sub>R # [Tock]\<^sub>E # \<rho>" in allE, auto)
    have "\<exists>x. (\<exists>p. x = hide_trace X p \<and> p \<in> {s. [Y \<union> {Tick}]\<^sub>R # [Tock]\<^sub>E # s \<in> P}) \<and> add_Tick_refusal_trace s' \<in> x"
      using ind_hyp[where P="{s. [Y\<union>{Tick}]\<^sub>R # [Tock]\<^sub>E # s \<in> P}", where \<rho>=s'] 1 2 3 case_assms by blast
    then show "\<exists>x. (\<exists>p. x = hide_trace X p \<and> p \<in> P) \<and> [insert Tick Z]\<^sub>R # [Tock]\<^sub>E # add_Tick_refusal_trace s' \<in> x"
      using case_assms apply (auto) 
      by (rule_tac x="hide_trace X ([insert Tick Y]\<^sub>R # [Tock]\<^sub>E # p)" in exI, auto, rule_tac x="[insert Tick Y]\<^sub>R # [Tock]\<^sub>E # p" in exI, auto)
  next
    fix X Y P Z
    show "\<forall>\<rho>. \<rho> \<in> P \<longrightarrow> add_Tick_refusal_trace \<rho> \<in> P \<Longrightarrow> [[Y]\<^sub>R] \<in> P \<Longrightarrow> Z \<subseteq> Y \<Longrightarrow> X \<subseteq> Y \<Longrightarrow> \<exists>x. (\<exists>p. x = hide_trace X p \<and> p \<in> P) \<and> [[insert Tick Z]\<^sub>R] \<in> x"
      by (rule_tac x="hide_trace X [[Y\<union>{Tick}]\<^sub>R]" in exI, auto, rule_tac x="[[Y\<union>{Tick}]\<^sub>R]" in exI, auto)
  qed
qed

lemma Hiding_Mono: "P \<sqsubseteq>\<^sub>C Q \<Longrightarrow> P \<setminus>\<^sub>C X \<sqsubseteq>\<^sub>C Q \<setminus>\<^sub>C X"
  unfolding RefinesTT_def HidingTT_def by auto