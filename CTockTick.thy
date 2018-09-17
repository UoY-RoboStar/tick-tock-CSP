theory CTockTick
  imports Main
begin

section {* Types and Wellformedness Conditions *}

datatype 'e cttevent = Event 'e  | Tock | Tick
datatype 'e cttobs = ObsEvent "'e cttevent" ("[_]\<^sub>E") | Ref "'e cttevent set" ("[_]\<^sub>R") | TockRef "'e cttevent set" ("[_]\<^sub>T")

fun cttWF :: "'e cttobs list \<Rightarrow> bool" where
  "cttWF [] = True" | (* an empty trace is okay*)
  "cttWF [[X]\<^sub>R] = True" | (* a refusal at the end of a trace is okay *)
  "cttWF [[Tick]\<^sub>E] = True" | (* a tick at the end of a trace is okay *)
  "cttWF ([Event e]\<^sub>E # \<sigma>) = cttWF \<sigma>" | (* a (non-tick, non-tock) event is okay *)
  "cttWF ([Tock]\<^sub>E # \<sigma>) = cttWF \<sigma>" | (* a tock event on its own is okay *)
  "cttWF ([X]\<^sub>T # \<sigma>) = (cttWF \<sigma> \<and> Tock \<notin> X)" | (* a tock with a refusal is okay if tock is not refused *)
  "cttWF \<sigma> = False" (* everything else is not allowed *)

section {* Prefix Relations *}

fun ctt_prefix :: "'e cttobs list \<Rightarrow> 'e cttobs list \<Rightarrow> bool" (infix "\<le>\<^sub>C" 50) where
  "ctt_prefix [] x = True" |
  "ctt_prefix (x # xa) (y # ya) = (x = y \<and> ctt_prefix xa ya)" |
  "ctt_prefix (x # xa) [] = False"

lemma ctt_prefix_refl: "x \<le>\<^sub>C x"
  by (induct x, auto)

lemma ctt_prefix_trans: "x \<le>\<^sub>C y \<Longrightarrow> y \<le>\<^sub>C z \<Longrightarrow> x \<le>\<^sub>C z"
proof -
  have "\<exists> y. x \<le>\<^sub>C y \<and> y \<le>\<^sub>C z \<Longrightarrow> x \<le>\<^sub>C z"
    apply (induct rule:ctt_prefix.induct, auto)
    apply (metis ctt_prefix.elims(2) list.discI list.sel(1))
    apply (metis ctt_prefix.elims(2) list.discI list.sel(3))
    using ctt_prefix.elims(2) by force
  then show "x \<le>\<^sub>C y \<Longrightarrow> y \<le>\<^sub>C z \<Longrightarrow> x \<le>\<^sub>C z" by auto
qed

lemma ctt_prefix_antisym: "x \<le>\<^sub>C y \<Longrightarrow> y \<le>\<^sub>C x \<Longrightarrow> x = y"
  using ctt_prefix.elims(2) by (induct rule:ctt_prefix.induct, auto)

fun ctt_prefix_subset :: "'e cttobs list \<Rightarrow> 'e cttobs list \<Rightarrow> bool" (infix "\<lesssim>\<^sub>C" 50) where
  "ctt_prefix_subset [] x = True" |
  "ctt_prefix_subset ([X]\<^sub>T # xa) ([Y]\<^sub>T # ya) = (X \<subseteq> Y \<and> ctt_prefix_subset xa ya)" |
  "ctt_prefix_subset ([X]\<^sub>R # xa) ([Y]\<^sub>R # ya) = (X \<subseteq> Y \<and> ctt_prefix_subset xa ya)" |
  "ctt_prefix_subset ([Tock]\<^sub>E # xa) ([y]\<^sub>T # ya) = (ctt_prefix_subset xa ya)" |
  "ctt_prefix_subset ([x]\<^sub>E # xa) ([y]\<^sub>E # ya) = (x = y \<and> ctt_prefix_subset xa ya)" |
  "ctt_prefix_subset (x # xa) (y # ya) = False" |
  "ctt_prefix_subset (x # xa) [] = False"

lemma ctt_prefix_subset_refl: "x \<lesssim>\<^sub>C x"
  by (induct x, auto, case_tac a, auto)

lemma ctt_prefix_subset_trans: "x \<lesssim>\<^sub>C y \<Longrightarrow> y \<lesssim>\<^sub>C z \<Longrightarrow> x \<lesssim>\<^sub>C z"
proof -
  have "\<exists> y. x \<lesssim>\<^sub>C y \<and> y \<lesssim>\<^sub>C z \<Longrightarrow> x \<lesssim>\<^sub>C z"
    apply (induct rule:ctt_prefix_subset.induct, auto)
    apply (case_tac y, auto, case_tac a, auto)
    apply (case_tac y, auto, case_tac a, auto)
    apply (case_tac y, auto, case_tac a, auto)
    apply (case_tac y, auto, case_tac a, auto)
    apply (case_tac yb, auto, case_tac a, auto)
    apply (case_tac yb, auto, case_tac a, auto)
    apply (case_tac yb, auto, case_tac a, auto)
    apply (case_tac y, auto, case_tac a, auto)+
    by (metis ctt_prefix_subset.simps(17) neq_Nil_conv)
  then show "x \<lesssim>\<^sub>C y \<Longrightarrow> y \<lesssim>\<^sub>C z \<Longrightarrow> x \<lesssim>\<^sub>C z" by auto
qed

lemma ctt_prefix_subset_antisym: "x \<lesssim>\<^sub>C y \<Longrightarrow> y \<lesssim>\<^sub>C x \<Longrightarrow> x = y"
  using ctt_prefix_subset.elims(2) by (induct rule:ctt_prefix_subset.induct, auto)

lemma ctt_prefix_imp_prefix_subset: "x \<le>\<^sub>C y \<Longrightarrow> x \<lesssim>\<^sub>C y"
  by (induct rule:ctt_prefix_subset.induct, auto)

lemma ctt_prefix_decompose: "x \<le>\<^sub>C y \<Longrightarrow> \<exists> z. y = x @ z"
  apply (induct rule:ctt_prefix.induct, auto)
  using ctt_prefix.elims(2) by auto

section {* Initial sequences of tocks *}

fun ntock ::"'e cttevent set \<Rightarrow> nat \<Rightarrow> 'e cttobs list set" where
  "ntock X 0 = {[]}" |
  "ntock X (Suc n) = {t. \<exists> Y s. Tock \<notin> Y \<and> Y \<subseteq> X \<and> t = [[Y]\<^sub>T] @ s \<and> s \<in> ntock X n} \<union> {t. \<exists> s. t = [[Tock]\<^sub>E] @ s \<and> s \<in> ntock X n} "

lemma all_ntocks_cttWF: "\<forall>x. x \<in> ntock X n \<longrightarrow> cttWF x"
  by (induct n, auto)

lemma in_ntock_cttWF: "x \<in> ntock X n \<Longrightarrow> cttWF x"
  by (simp add: all_ntocks_cttWF)

lemma all_ntocks_append_cttWF: "cttWF s \<Longrightarrow> \<forall>x. x \<in> ntock X n \<longrightarrow> cttWF (x @ s)"
  by (induct n, auto)

lemma in_ntock_append_cttWF: "cttWF s \<Longrightarrow> x \<in> ntock X n \<longrightarrow> cttWF (x @ s)"
  by (simp add: all_ntocks_append_cttWF)

lemma ntock_subset: "X \<subseteq> Y \<Longrightarrow> ntock X n \<subseteq> ntock Y n"
  by (induct rule:ntock.induct, clarsimp+, blast)

lemma ntock_remove_Tock: "ntock X n = ntock {x. x \<in> X \<and> x \<noteq> Tock} n"
  by (induct n, clarsimp+, auto)
  
definition add_pretocks :: "'e cttevent set \<Rightarrow> 'e cttobs list set \<Rightarrow> 'e cttobs list set" where
  "add_pretocks X Y = {t. \<exists> n s x. t = s @ x \<and> x \<in> Y \<and> s \<in> ntock X n}"

lemma add_pretocks_cttWF: "(\<forall>s\<in>P. cttWF s) \<Longrightarrow> s \<in> add_pretocks X P \<Longrightarrow> cttWF s"
  unfolding add_pretocks_def by (auto simp add: in_ntock_append_cttWF)

lemma in_add_pretocks_decompose: "x \<in> add_pretocks X Y \<Longrightarrow> \<exists> s y. s \<in> add_pretocks X {[]} \<and> y \<in> Y \<and> x = s @ y "
  unfolding add_pretocks_def by auto

lemma concat_in_add_pretocks: "s \<in> add_pretocks X {[]} \<Longrightarrow> y \<in> Y \<Longrightarrow> s @ y \<in> add_pretocks X Y"
  unfolding add_pretocks_def by auto

lemma add_pretocks_subset1: "X1 \<subseteq> X2 \<Longrightarrow> add_pretocks X1 Y \<subseteq> add_pretocks X2 Y"
  unfolding add_pretocks_def using ntock_subset by blast

lemma add_pretocks_subset2: "Y1 \<subseteq> Y2 \<Longrightarrow> add_pretocks X Y1 \<subseteq> add_pretocks X Y2"
  unfolding add_pretocks_def by blast

lemma self_in_add_pretocks: "Y \<subseteq> add_pretocks X Y"
  unfolding add_pretocks_def by (auto, rule_tac x="0" in exI, auto)

section {* Operators *}

subsection {* Div *}

definition DivCTT :: "'e cttobs list set" ("div\<^sub>C") where
  "div\<^sub>C = {[]}"

lemma DivCTT_wf: "\<forall> t\<in>div\<^sub>C. cttWF t"
  unfolding DivCTT_def by auto

subsection {* Stop *}

definition StopCTT :: "'e cttobs list set" ("STOP\<^sub>C") where
  "STOP\<^sub>C = add_pretocks {x. x \<noteq> Tock} ({t. \<exists> Y. Tock \<notin> Y \<and> t = [[Y]\<^sub>R]} \<union> {[]})"

lemma StopCTT_wf: "\<forall> t\<in>STOP\<^sub>C. cttWF t"
  unfolding StopCTT_def
  by (auto, rule_tac P="({t. \<exists> Y. Tock \<notin> Y \<and> t = [[Y]\<^sub>R]} \<union> {[]})" and X="{x. x \<noteq> Tock}" in add_pretocks_cttWF, auto)

subsection {* Skip *}

definition SkipCTT :: "'e cttobs list set" ("SKIP\<^sub>C") where
  "SKIP\<^sub>C = {t. \<exists> Y. Tick \<notin> Y \<and> t = [[Y]\<^sub>R]} \<union> {[], [[Tick]\<^sub>E]}"
  (*{[], [[Tick]\<^sub>E]} \<union> {t. \<exists> Y. Tick \<notin> Y \<and> t = [[Y]\<^sub>R]} \<union> {t. \<exists> n s. (t = s \<or> t = s @ [[Tick]\<^sub>E]) \<and> s \<in> ntock {x. x \<noteq> Tick} n}*)

lemma SkipCTT_wf: "\<forall> t\<in>SKIP\<^sub>C. cttWF t"
  unfolding SkipCTT_def 
  by auto

subsection {* Prefix *}

definition PrefixCTT :: "'e \<Rightarrow> 'e cttobs list set \<Rightarrow> 'e cttobs list set" where
  "PrefixCTT e P = add_pretocks {x. x \<noteq> Event e \<and> x \<noteq> Tock} ({[], [[Event e]\<^sub>E]} \<union> {t. \<exists> Y. Tock \<notin> Y \<and> Event e \<notin> Y \<and> t = [[Y]\<^sub>R]})"

lemma PrefixCTT_wf: "\<forall> t\<in>P. cttWF t \<Longrightarrow> \<forall> t\<in>PrefixCTT e P. cttWF t"
  unfolding PrefixCTT_def 
  by (auto, rule_tac P="{[], [[Event e]\<^sub>E]} \<union> {t. \<exists> Y. Tock \<notin> Y \<and> Event e \<notin> Y \<and> t = [[Y]\<^sub>R]}" and X="{x. x \<noteq> Event e \<and> x \<noteq> Tock}" in add_pretocks_cttWF, auto)

subsection {* Internal Choice *}

definition IntChoiceCTT :: "'e cttobs list set \<Rightarrow> 'e cttobs list set \<Rightarrow> 'e cttobs list set" (infixl "\<sqinter>\<^sub>C" 70) where
  "P \<sqinter>\<^sub>C Q = P \<union> Q"

lemma IntChoiceCTT_wf: "\<forall> t\<in>P. cttWF t \<Longrightarrow> \<forall> t\<in>Q. cttWF t \<Longrightarrow> \<forall> t\<in>P \<sqinter>\<^sub>C Q. cttWF t"
  unfolding IntChoiceCTT_def by auto

subsection {* Wait *}

definition WaitCTT :: "nat \<Rightarrow> 'e cttobs list set" ("wait\<^sub>C[_]") where
  "wait\<^sub>C[n] = {t. \<exists> s x. t = s @ x \<and> x \<in> {[], [[Tick]\<^sub>E]} \<and> s \<in> ntock {x. x \<noteq> Tock} n}"

lemma WaitCTT_wf: "\<forall> t\<in>wait\<^sub>C[n]. cttWF t"
  unfolding WaitCTT_def by (auto simp add: in_ntock_cttWF in_ntock_append_cttWF)

subsection {* External Choice *}

definition longest_tock_ref_prefix :: "'e cttobs list \<Rightarrow> 'e cttobs list" where
  "longest_tock_ref_prefix x = (THE x'. x' \<le>\<^sub>C x \<and> x' \<in> add_pretocks UNIV ({[]} \<union> {t. \<exists> X. t = [[X]\<^sub>R]})
      \<and> (\<forall> x''. x'' \<le>\<^sub>C x \<and> x'' \<in> add_pretocks UNIV ({[]} \<union> {t. \<exists> X. t = [[X]\<^sub>R]}) \<longrightarrow> x'' \<le>\<^sub>C x'))"

definition consistent_ctttraces :: "'e cttobs list \<Rightarrow> 'e cttobs list \<Rightarrow> bool" where
  "consistent_ctttraces x y = (longest_tock_ref_prefix x = longest_tock_ref_prefix y)"

lemma consistent_ctttraces_trans: "consistent_ctttraces x y \<Longrightarrow> consistent_ctttraces y z \<Longrightarrow> consistent_ctttraces x z"
  unfolding consistent_ctttraces_def by auto

lemma consistent_ctttraces_refl: 
  "consistent_ctttraces x x"
  unfolding consistent_ctttraces_def by auto

lemma consistent_ctttraces_comm: "consistent_ctttraces x y \<Longrightarrow> consistent_ctttraces y x"
  unfolding consistent_ctttraces_def by auto

definition ExtChoiceCTT_aux :: "'e cttobs list set \<Rightarrow> 'e cttobs list set \<Rightarrow> 'e cttobs list set" where
  "ExtChoiceCTT_aux P Q = {p. p \<in> P \<and> (\<exists> q\<in>Q. consistent_ctttraces p q)} \<union> {q. q \<in> Q \<and> (\<exists> p\<in>P. consistent_ctttraces q p)}"

lemma ExtChoiceCTT_aux_wf: "\<forall> t\<in>P. cttWF t \<Longrightarrow> \<forall> t\<in>Q. cttWF t \<Longrightarrow> \<forall> t\<in>ExtChoiceCTT_aux P Q. cttWF t"
  unfolding ExtChoiceCTT_aux_def by auto

lemma ExtChoiceCTT_aux_comm: "ExtChoiceCTT_aux P Q = ExtChoiceCTT_aux Q P"
  unfolding ExtChoiceCTT_aux_def by auto

lemma ExtChoiceCTT_aux_assoc: "ExtChoiceCTT_aux (ExtChoiceCTT_aux P Q) R = ExtChoiceCTT_aux P (ExtChoiceCTT_aux Q R)"
  unfolding ExtChoiceCTT_aux_def apply safe
  using consistent_ctttraces_comm consistent_ctttraces_trans  by blast+

lemma ExtChoiceCTT_aux_union_dist1: "ExtChoiceCTT_aux (P \<union> Q) R = (ExtChoiceCTT_aux P R) \<union> (ExtChoiceCTT_aux Q R)"
  unfolding ExtChoiceCTT_aux_def by auto

lemma ExtChoiceCTT_aux_union_dist2: "ExtChoiceCTT_aux P (Q \<union> R) = (ExtChoiceCTT_aux P Q) \<union> (ExtChoiceCTT_aux P R)"
  unfolding ExtChoiceCTT_aux_def by auto

lemma longest_tock_ref_prefix_empty: "longest_tock_ref_prefix [] = []"
  unfolding longest_tock_ref_prefix_def apply (rule_tac a="[]" in theI2)
  using self_in_add_pretocks apply force
  using ctt_prefix.elims(2) by blast+

lemma self_in_add_pretocks2: "x \<in> Y \<Longrightarrow> x \<in> add_pretocks X Y"
  using self_in_add_pretocks by auto

lemma longest_tock_ref_prefix_refusal: "longest_tock_ref_prefix [[X]\<^sub>R] = [[X]\<^sub>R]"
  unfolding longest_tock_ref_prefix_def apply (rule_tac a="[[X]\<^sub>R]" in theI2)
  using self_in_add_pretocks apply force
   apply (case_tac x, auto)
  apply (erule_tac x="[[X]\<^sub>R]" in allE, auto)
  apply (simp add: self_in_add_pretocks2)
  using ctt_prefix.simps(1) ctt_prefix_antisym apply blast
   apply (case_tac x, auto)
  apply (erule_tac x="[[X]\<^sub>R]" in allE, auto)
  apply (simp add: self_in_add_pretocks2)
  using ctt_prefix.simps(1) ctt_prefix_antisym apply blast
  done

lemma longest_tock_ref_prefix_Tick: "longest_tock_ref_prefix [[Tick]\<^sub>E] = []"
  unfolding longest_tock_ref_prefix_def apply (rule_tac a="[]" in theI2, auto)
  using self_in_add_pretocks apply (force, case_tac x'', auto)
  unfolding add_pretocks_def apply auto
  apply (case_tac n, auto)+
  done

lemma "ExtChoiceCTT_aux SKIP\<^sub>C div\<^sub>C = {[], [[Tick]\<^sub>E]}"
  unfolding ExtChoiceCTT_aux_def SkipCTT_def DivCTT_def consistent_ctttraces_def
  by (auto, (simp add: longest_tock_ref_prefix_empty longest_tock_ref_prefix_refusal longest_tock_ref_prefix_Tick)+)

definition ExtChoiceCTT :: "'e cttobs list set \<Rightarrow> 'e cttobs list set \<Rightarrow> 'e cttobs list set" (infixl "\<box>\<^sub>C" 65) where
  "P \<box>\<^sub>C Q = ExtChoiceCTT_aux P Q
    \<union> {s. \<exists> t. t \<in> ExtChoiceCTT_aux P Q \<and> t \<in> add_pretocks UNIV {[[Tick]\<^sub>E]} \<and> 
      (\<exists> t' X. t' \<in> ExtChoiceCTT_aux P Q \<and> t' = longest_tock_ref_prefix t @ [[X]\<^sub>R]) \<and>
      (\<exists> X. Tick \<notin> X \<and> s = longest_tock_ref_prefix t @ [[X]\<^sub>R])}"

lemma "P \<box>\<^sub>C Q = Q \<box>\<^sub>C P"
  unfolding ExtChoiceCTT_def by (auto simp add: ExtChoiceCTT_aux_comm)

lemma Tock_start_imp_in_ntock: "[Tock]\<^sub>E # y \<in> ntock X (Suc n) \<Longrightarrow> y \<in> ntock X n"
  by auto

lemma consistent_ctttraces_pretocks_decompose: "t \<in> add_pretocks X {[]} \<Longrightarrow> consistent_ctttraces (t @ s) x \<Longrightarrow> 
  \<exists> t' s'. x = t' @ s' \<and> t' \<in> add_pretocks X {[]}"
  unfolding consistent_ctttraces_def longest_tock_ref_prefix_def using self_in_add_pretocks2 by auto

lemma cttWF_concat: "cttWF (s @ t) \<Longrightarrow> cttWF s"
  by (induct rule:cttWF.induct, auto)

lemma cttWF_last_replace: "cttWF (s @ [x]) \<Longrightarrow> cttWF [y] \<Longrightarrow> cttWF (s @ [y])"
  by (induct s rule:cttWF.induct, auto)

lemma ExtChoiceCTT_wf: 
  assumes "\<forall> t\<in>P. cttWF t" and "\<forall> t\<in>Q. cttWF t" 
  shows "\<forall> t\<in>P \<box>\<^sub>C Q. cttWF t"
  unfolding ExtChoiceCTT_def
proof (auto)
  fix t 
  assume "t \<in> ExtChoiceCTT_aux P Q"
  then show "cttWF t"
    using assms ExtChoiceCTT_aux_wf by blast
next
  fix ta X Xa
  assume "longest_tock_ref_prefix ta @ [[Xa]\<^sub>R] \<in> ExtChoiceCTT_aux P Q"
  then have "cttWF (longest_tock_ref_prefix ta @ [[Xa]\<^sub>R])"
    using assms ExtChoiceCTT_aux_wf by blast
  then show "cttWF (longest_tock_ref_prefix ta @ [[X]\<^sub>R])"
   by (simp add: cttWF_last_replace)
qed

lemma "(P \<box>\<^sub>C Q) \<box>\<^sub>C R = P \<box>\<^sub>C (Q \<box>\<^sub>C R)"
  oops

lemma "SKIP\<^sub>C \<box>\<^sub>C wait\<^sub>C[n] = SKIP\<^sub>C"
    oops

lemma "SKIP\<^sub>C \<box>\<^sub>C SKIP\<^sub>C = SKIP\<^sub>C"
    oops

lemma "wait\<^sub>C[m] \<box>\<^sub>C wait\<^sub>C[n] = wait\<^sub>C[min m n]"
  oops

section {* Refinement *}

definition RefinesCTT :: "'e cttobs list set \<Rightarrow> 'e cttobs list set \<Rightarrow> bool" (infix "\<sqsubseteq>\<^sub>C" 50) where
  "P \<sqsubseteq>\<^sub>C Q = (Q \<subseteq> P)"


