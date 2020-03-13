theory TickTock_UntimedPrefix
  imports TickTock_Prefix TickTock_ExtChoice TickTock_Basic_Ops
begin

subsection \<open>Instantaneous (Untimed) Prefix\<close>

definition UntimedPrefixTT :: "'e \<Rightarrow> 'e ttprocess \<Rightarrow> 'e ttprocess" (infixr "\<rightarrow>\<^sub>U" 61) where
  "e \<rightarrow>\<^sub>U P = (e \<rightarrow>\<^sub>C P \<box>\<^sub>C STOP\<^sub>U)"

lemma UntimedPrefixTT_def2:
  "e \<rightarrow>\<^sub>U P = {t. t = [] \<or> (\<exists> X. Event e \<notin> X \<and> t = [[X]\<^sub>R]) \<or> (\<exists> \<sigma>\<in>P. t = [[Event e]\<^sub>E] @ \<sigma>)}"
  unfolding UntimedPrefixTT_def PrefixTT_def ExtChoiceTT_def UntimedStopTT_def
proof (safe, simp_all)
  fix \<sigma>
  assume "\<forall>\<rho>'\<in>tocks UNIV. \<rho>' \<le>\<^sub>C \<sigma> \<longrightarrow> \<rho>' \<le>\<^sub>C []" "\<sigma> \<in> tocks {x. x \<noteq> Tock \<and> x \<noteq> Event e}"
  then show "\<sigma> = []"
    by (erule_tac x=\<sigma> in ballE, simp_all add: tt_prefix_antisym tt_prefix_refl tocks_tt_subset2 tt_subset_refl)
next
  fix \<sigma>
  assume "\<forall>\<rho>'\<in>tocks UNIV. \<rho>' \<le>\<^sub>C \<sigma> \<longrightarrow> \<rho>' \<le>\<^sub>C []" "\<sigma> \<in> tocks {x. x \<noteq> Tock \<and> x \<noteq> Event e}"
  then show "\<sigma> = []"
    by (erule_tac x=\<sigma> in ballE, simp_all add: tt_prefix_antisym tt_prefix_refl tocks_tt_subset2 tt_subset_refl)
next
  fix sa X
  assume "\<forall>\<rho>'\<in>tocks UNIV. \<rho>' \<le>\<^sub>C sa @ [[X]\<^sub>R] \<longrightarrow> \<rho>' \<le>\<^sub>C []" "sa \<in> tocks {x. x \<noteq> Tock \<and> x \<noteq> Event e}"
  then show "sa \<noteq> [] \<Longrightarrow> False"
    apply (erule_tac x=sa in ballE, simp add: tt_prefix_antisym tt_prefix_concat)
    using tocks_tt_subset2 tt_subset_refl by blast
next
  fix \<rho> \<sigma> \<tau> :: "'a tttrace" and X :: "'a ttevent set"
  assume "\<rho> @ \<tau> = [[X]\<^sub>R]" "\<rho> \<in> tocks UNIV"
  then show "\<rho> = []"
    by (cases \<rho> rule:ttWF.cases, auto simp add: notin_tocks)
next
  fix \<rho> \<sigma> \<tau> :: "'a tttrace" and X :: "'a ttevent set"
  assume "\<rho> @ \<tau> = [[X]\<^sub>R]" "\<rho> \<in> tocks UNIV"
  then show "\<rho> = []"
    by (cases \<rho> rule:ttWF.cases, auto simp add: notin_tocks)
next
  fix \<rho> \<sigma> \<tau> :: "'a tttrace" and X :: "'a ttevent set"
  assume "\<rho> @ \<tau> = [[X]\<^sub>R]" "\<rho> \<in> tocks UNIV"
  then show "\<rho> = []"
    by (cases \<rho> rule:ttWF.cases, auto simp add: notin_tocks)
next
  fix \<rho> \<sigma> \<tau> :: "'a tttrace" and X :: "'a ttevent set"
  assume "\<rho> @ \<tau> = [[X]\<^sub>R]" "\<rho> \<in> tocks UNIV"
  then show "\<rho> = []"
    by (cases \<rho> rule:ttWF.cases, auto simp add: notin_tocks)
next
  fix \<rho> \<sigma> \<tau> :: "'a tttrace" and X :: "'a ttevent set"
  assume "\<rho> @ \<tau> = [[X]\<^sub>R]" "\<rho> \<in> tocks UNIV"
  then show "\<rho> = []"
    by (cases \<rho> rule:ttWF.cases, auto simp add: notin_tocks)
next
  fix \<rho> \<sigma> \<tau> :: "'a tttrace" and X :: "'a ttevent set"
  assume "\<rho> @ \<tau> = [[X]\<^sub>R]" "\<rho> \<in> tocks UNIV"
  then show "\<rho> = []"
    by (cases \<rho> rule:ttWF.cases, auto simp add: notin_tocks)
next
  fix \<rho> \<sigma> \<tau> :: "'a tttrace" and X :: "'a ttevent set"
  assume "\<rho> @ \<tau> = [[X]\<^sub>R]" "\<rho> \<in> tocks UNIV"
  then show "\<rho> = []"
    by (cases \<rho> rule:ttWF.cases, auto simp add: notin_tocks)
next
  fix \<rho> \<sigma> \<tau> :: "'a tttrace" and X :: "'a ttevent set"
  assume "\<rho> @ \<tau> = [[X]\<^sub>R]" "\<rho> \<in> tocks UNIV"
  then show "\<rho> = []"
    by (cases \<rho> rule:ttWF.cases, auto simp add: notin_tocks)
next
  fix \<rho> \<sigma> \<tau> :: "'a tttrace" and X :: "'a ttevent set"
  assume \<rho>_\<sigma>_in_tocks: "\<rho> @ \<sigma> \<in> tocks {x. x \<noteq> Tock \<and> x \<noteq> Event e}"
  assume \<rho>_longest_tocks_sigma: "\<forall>\<rho>'\<in>tocks UNIV. \<rho>' \<le>\<^sub>C \<rho> @ \<sigma> \<longrightarrow> \<rho>' \<le>\<^sub>C \<rho>"
  assume "\<rho> @ \<tau> = [[X]\<^sub>R]" "\<rho> \<in> tocks UNIV"
  then have "\<rho> = []"
    by (cases \<rho> rule:ttWF.cases, auto simp add: notin_tocks)
  then have "\<sigma> \<in> tocks {x. x \<noteq> Tock \<and> x \<noteq> Event e} \<and> \<rho> = []"
    using \<rho>_\<sigma>_in_tocks by auto
  then show "\<sigma> = []"
    by (metis (full_types) \<rho>_longest_tocks_sigma append_Nil self_extension_tt_prefix tocks_tt_subset2 tt_prefix_refl tt_subset_refl)
next
  fix \<rho> \<sigma> \<tau> s :: "'a tttrace" and X Xa :: "'a ttevent set"
  assume \<rho>_longest_tocks_\<sigma>: "\<forall>\<rho>'\<in>tocks UNIV. \<rho>' \<le>\<^sub>C s @ [[Xa]\<^sub>R] \<longrightarrow> \<rho>' \<le>\<^sub>C \<rho>"
  assume \<rho>_in_tocks: "\<rho> \<in> tocks UNIV" and s_in_tocks: "s \<in> tocks {x. x \<noteq> Tock \<and> x \<noteq> Event e}"
  assume \<rho>_\<tau>_def: "\<rho> @ \<tau> = [[X]\<^sub>R]" and \<rho>_\<sigma>_def: "\<rho> @ \<sigma> = s @ [[Xa]\<^sub>R]"

  have "\<rho> = []"
    using \<rho>_in_tocks \<rho>_\<tau>_def by (induct \<rho> rule:ttWF.induct, auto simp add: notin_tocks)
  then have "s = []"
    by (metis (full_types) \<rho>_longest_tocks_\<sigma> neq_Nil_conv s_in_tocks tocks_subset top_greatest tt_prefix.simps(3) tt_prefix_concat)
  then show "s \<noteq> [] \<Longrightarrow> \<sigma> = []"
    by auto
next
  fix \<rho> \<sigma> \<tau> :: "'a tttrace" and X :: "'a ttevent set"
  assume \<rho>_longest_tocks_\<tau>: "\<forall>\<rho>'\<in>tocks UNIV. \<rho>' \<le>\<^sub>C [[X]\<^sub>R] \<longrightarrow> \<rho>' \<le>\<^sub>C \<rho>"
  assume \<tau>_refusal_imp_\<sigma>_refusal: "\<forall>X. \<tau> = [[X]\<^sub>R] \<longrightarrow> (\<exists>Y. \<sigma> = [[Y]\<^sub>R] \<and> (\<forall>e. (e \<in> X) = (e \<in> Y) \<or> e = Tock))"
  assume \<rho>_in_tocks: "\<rho> \<in> tocks UNIV" and \<rho>_\<sigma>_in_tocks: "\<rho> @ \<sigma> \<in> tocks {x. x \<noteq> Tock \<and> x \<noteq> Event e}"
  assume \<rho>_\<tau>_def: "\<rho> @ \<tau> = [[X]\<^sub>R]"

  have \<rho>_empty: "\<rho> = []"
    using \<rho>_\<tau>_def \<rho>_in_tocks append_eq_Cons_conv in_tocks_last by fastforce
  then have \<tau>_refusal: "\<tau> = [[X]\<^sub>R]"
    using \<rho>_\<tau>_def by auto
  then obtain Y where \<sigma>_refusal: "\<sigma> = [[Y]\<^sub>R]"
    using \<tau>_refusal_imp_\<sigma>_refusal by auto
  then have "[[X]\<^sub>R] \<in> tocks {x. x \<noteq> Tock \<and> x \<noteq> Event e}"
    using \<rho>_\<sigma>_in_tocks end_refusal_notin_tocks by blast
  then have False
    using refusal_notin_tocks by blast
  then show "\<tau> = []"
    by auto
next
  fix \<rho> \<sigma> \<tau> :: "'a tttrace" and X :: "'a ttevent set"
  assume \<rho>_longest_tocks_\<tau>: "\<forall>\<rho>'\<in>tocks UNIV. \<rho>' \<le>\<^sub>C [[X]\<^sub>R] \<longrightarrow> \<rho>' \<le>\<^sub>C \<rho>"
  assume \<tau>_refusal_imp_\<sigma>_refusal: "\<forall>X. \<tau> = [[X]\<^sub>R] \<longrightarrow> (\<exists>Y. \<sigma> = [[Y]\<^sub>R] \<and> (\<forall>e. (e \<in> X) = (e \<in> Y) \<or> e = Tock))"
  assume \<rho>_in_tocks: "\<rho> \<in> tocks UNIV" and \<rho>_\<sigma>_in_tocks: "\<rho> @ \<sigma> \<in> tocks {x. x \<noteq> Tock \<and> x \<noteq> Event e}"
  assume \<rho>_\<tau>_def: "\<rho> @ \<tau> = [[X]\<^sub>R]"

  have \<rho>_empty: "\<rho> = []"
    using \<rho>_\<tau>_def \<rho>_in_tocks append_eq_Cons_conv in_tocks_last by fastforce
  then have \<tau>_refusal: "\<tau> = [[X]\<^sub>R]"
    using \<rho>_\<tau>_def by auto
  then obtain Y where \<sigma>_refusal: "\<sigma> = [[Y]\<^sub>R]"
    using \<tau>_refusal_imp_\<sigma>_refusal by auto
  then have "[[X]\<^sub>R] \<in> tocks {x. x \<noteq> Tock \<and> x \<noteq> Event e}"
    using \<rho>_\<sigma>_in_tocks end_refusal_notin_tocks by blast
  then have False
    using refusal_notin_tocks by blast
  then show "\<tau> = []"
    by auto
next
  fix \<rho> \<sigma> \<tau> :: "'a tttrace" and X :: "'a ttevent set"
  assume \<rho>_longest_tocks_\<tau>: "\<forall>\<rho>'\<in>tocks UNIV. \<rho>' \<le>\<^sub>C [[X]\<^sub>R] \<longrightarrow> \<rho>' \<le>\<^sub>C \<rho>"
  assume \<tau>_refusal_imp_\<sigma>_refusal: "\<forall>X. \<tau> = [[X]\<^sub>R] \<longrightarrow> (\<exists>Y. \<sigma> = [[Y]\<^sub>R] \<and> (\<forall>e. (e \<in> X) = (e \<in> Y) \<or> e = Tock))"
  assume \<rho>_in_tocks: "\<rho> \<in> tocks UNIV" and \<rho>_\<sigma>_in_tocks: "\<rho> @ \<sigma> \<in> tocks {x. x \<noteq> Tock \<and> x \<noteq> Event e}"
  assume \<rho>_\<tau>_def: "\<rho> @ \<tau> = [[X]\<^sub>R]"

  have \<rho>_empty: "\<rho> = []"
    using \<rho>_\<tau>_def \<rho>_in_tocks append_eq_Cons_conv in_tocks_last by fastforce
  then have \<tau>_refusal: "\<tau> = [[X]\<^sub>R]"
    using \<rho>_\<tau>_def by auto
  then obtain Y where \<sigma>_refusal: "\<sigma> = [[Y]\<^sub>R]"
    using \<tau>_refusal_imp_\<sigma>_refusal by auto
  then have "[[X]\<^sub>R] \<in> tocks {x. x \<noteq> Tock \<and> x \<noteq> Event e}"
    using \<rho>_\<sigma>_in_tocks end_refusal_notin_tocks by blast
  then have False
    using refusal_notin_tocks by blast
  then show "\<sigma> = []"
    by auto
next
  fix \<rho> \<sigma> \<tau> s :: "'a tttrace" and X Xa :: "'a ttevent set"
  assume \<rho>_longest_tocks_\<tau>: "\<forall>\<rho>'\<in>tocks UNIV. \<rho>' \<le>\<^sub>C [[X]\<^sub>R] \<longrightarrow> \<rho>' \<le>\<^sub>C \<rho>"
  assume \<tau>_refusal_imp_\<sigma>_refusal: "\<forall>X. \<tau> = [[X]\<^sub>R] \<longrightarrow> (\<exists>Y. \<sigma> = [[Y]\<^sub>R] \<and> (\<forall>e. (e \<in> X) = (e \<in> Y) \<or> e = Tock))"
  assume \<rho>_in_tocks: "\<rho> \<in> tocks UNIV" and \<rho>_\<sigma>_in_tocks: "s \<in> tocks {x. x \<noteq> Tock \<and> x \<noteq> Event e}"
  assume \<rho>_\<tau>_def: "\<rho> @ \<tau> = [[X]\<^sub>R]" and \<rho>_\<sigma>_def: "\<rho> @ \<sigma> = s @ [[Xa]\<^sub>R]"
  assume e_in_X: "Event e \<in> X" and e_in_Xa: "Event e \<notin> Xa"

  have \<rho>_empty: "\<rho> = []"
    using \<rho>_\<tau>_def \<rho>_in_tocks append_eq_Cons_conv in_tocks_last by fastforce
  have \<tau>_refusal: "\<tau> = [[X]\<^sub>R]"
    using \<rho>_empty \<rho>_\<tau>_def by auto
  have \<sigma>_refusal: "\<sigma> = [[Xa]\<^sub>R] \<and> (\<forall>e. (e \<in> X) = (e \<in> Xa) \<or> e = Tock)"
    using \<rho>_\<sigma>_def \<tau>_refusal \<tau>_refusal_imp_\<sigma>_refusal by auto
  then have "Event e \<in> Xa"
    using e_in_X by blast
  then have "False"
    using e_in_Xa by blast
  then show "\<tau> = []"
    by auto
next
  fix \<sigma> s \<sigma>' :: "'a tttrace"
  assume \<rho>_longest_tocks_\<sigma>: "\<forall>\<rho>'\<in>tocks UNIV. \<rho>' \<le>\<^sub>C s @ [Event e]\<^sub>E # \<sigma>' \<longrightarrow> \<rho>' \<le>\<^sub>C []"
  assume s_in_tocks: "s \<in> tocks {x. x \<noteq> Tock \<and> x \<noteq> Event e}"
  assume \<rho>_\<sigma>_assm: "\<forall>\<sigma>\<in>P. s @ [Event e]\<^sub>E # \<sigma>' \<noteq> [Event e]\<^sub>E # \<sigma>"
  assume \<sigma>'_in_P: "\<sigma>' \<in> P"

  have "s = []"
    by (meson \<rho>_longest_tocks_\<sigma> s_in_tocks tocks_subset top_greatest tt_prefix.simps(1) tt_prefix_antisym tt_prefix_concat)
  then show "False"
    using \<rho>_\<sigma>_assm \<sigma>'_in_P by blast
next
  fix \<rho> \<sigma> \<tau> s \<sigma>' :: "'a tttrace" and X :: "'a ttevent set"
  assume \<rho>_longest_tocks_\<sigma>: "\<forall>\<rho>'\<in>tocks UNIV. \<rho>' \<le>\<^sub>C s @ [Event e]\<^sub>E # \<sigma>' \<longrightarrow> \<rho>' \<le>\<^sub>C \<rho>"
  assume \<rho>_in_tocks: "\<rho> \<in> tocks UNIV" and  s_in_tocks: "s \<in> tocks {x. x \<noteq> Tock \<and> x \<noteq> Event e}"
  assume \<rho>_\<tau>_def: "\<rho> @ \<tau> = [[X]\<^sub>R]"
  assume \<rho>_\<sigma>_assm: "\<forall>\<sigma>\<in>P. s @ [Event e]\<^sub>E # \<sigma>' \<noteq> [Event e]\<^sub>E # \<sigma>"
  assume \<sigma>'_in_P: "\<sigma>' \<in> P"

  have "\<rho> = []"
    by (metis Cons_eq_append_conv \<rho>_\<tau>_def \<rho>_in_tocks append_Nil2 append_is_Nil_conv refusal_notin_tocks)
  then have "s = []"
    by (metis (mono_tags) \<rho>_longest_tocks_\<sigma> s_in_tocks tocks_subset top_greatest tt_prefix.simps(1) tt_prefix_antisym tt_prefix_concat)
  then show " \<sigma> = []"
    using \<rho>_\<sigma>_assm \<sigma>'_in_P by blast
next
  fix \<rho> \<sigma> \<tau> s \<sigma>' :: "'a tttrace" and X :: "'a ttevent set"
  assume \<rho>_longest_tocks_\<sigma>: "\<forall>\<rho>'\<in>tocks UNIV. \<rho>' \<le>\<^sub>C s @ [Event e]\<^sub>E # \<sigma>' \<longrightarrow> \<rho>' \<le>\<^sub>C \<rho>"
  assume \<rho>_in_tocks: "\<rho> \<in> tocks UNIV" and  s_in_tocks: "s \<in> tocks {x. x \<noteq> Tock \<and> x \<noteq> Event e}"
  assume \<tau>_refusal_imp_\<sigma>_refusal: "\<forall>X. \<tau> = [[X]\<^sub>R] \<longrightarrow> (\<exists>Y. \<sigma> = [[Y]\<^sub>R] \<and> (\<forall>e. (e \<in> X) = (e \<in> Y) \<or> e = Tock))"
  assume \<rho>_\<tau>_def: "\<rho> @ \<tau> = [[X]\<^sub>R]" and \<rho>_\<sigma>_def: "\<rho> @ \<sigma> = s @ [Event e]\<^sub>E # \<sigma>'" 
  assume \<sigma>'_in_P: "\<sigma>' \<in> P"

  have \<rho>_empty: "\<rho> = []"
    by (metis Cons_eq_append_conv \<rho>_\<tau>_def \<rho>_in_tocks append_Nil2 append_is_Nil_conv refusal_notin_tocks)
  then have "s = []"
    by (metis (mono_tags) \<rho>_longest_tocks_\<sigma> s_in_tocks tocks_subset top_greatest tt_prefix.simps(1) tt_prefix_antisym tt_prefix_concat)
  also have "\<exists>Y. \<sigma> = [[Y]\<^sub>R]"
    using \<rho>_\<tau>_def \<rho>_empty \<tau>_refusal_imp_\<sigma>_refusal by auto
  then have False
    using calculation \<rho>_\<sigma>_def by (simp add: \<rho>_empty)
  then show "\<tau> = []"
    by blast
next
  show "\<exists>\<rho>\<in>tocks UNIV.
       \<exists>\<sigma>. ((\<exists>s\<in>tocks {x. x \<noteq> Tock \<and> x \<noteq> Event e}. \<rho> @ \<sigma> = s \<or> (\<exists>X. Tock \<notin> X \<and> Event e \<notin> X \<and> \<rho> @ \<sigma> = s @ [[X]\<^sub>R])) \<or>
            (\<exists>s\<in>tocks {x. x \<noteq> Tock \<and> x \<noteq> Event e}. \<rho> @ \<sigma> = s \<or> (\<exists>\<sigma>'\<in>P. \<rho> @ \<sigma> = s @ [Event e]\<^sub>E # \<sigma>'))) \<and>
           (\<exists>\<tau>. (\<rho> = [] \<and> \<tau> = [] \<or> (\<exists>X. \<rho> @ \<tau> = [[X]\<^sub>R])) \<and>
                (\<forall>\<rho>'\<in>tocks UNIV. \<rho>' \<le>\<^sub>C \<rho> @ \<sigma> \<longrightarrow> \<rho>' \<le>\<^sub>C \<rho>) \<and>
                (\<forall>\<rho>'\<in>tocks UNIV. \<rho>' \<le>\<^sub>C \<rho> @ \<tau> \<longrightarrow> \<rho>' \<le>\<^sub>C \<rho>) \<and>
                (\<forall>X. \<sigma> = [[X]\<^sub>R] \<longrightarrow> (\<exists>Y. \<tau> = [[Y]\<^sub>R] \<and> (\<forall>e. (e \<in> X) = (e \<in> Y) \<or> e = Tock))) \<and>
                (\<forall>X. \<tau> = [[X]\<^sub>R] \<longrightarrow> (\<exists>Y. \<sigma> = [[Y]\<^sub>R] \<and> (\<forall>e. (e \<in> X) = (e \<in> Y) \<or> e = Tock))) \<and> (\<rho> = [] \<and> \<sigma> = [] \<or> \<rho> = [] \<and> \<tau> = []))"
    by (rule_tac x="[]" in bexI, rule_tac x="[]" in exI, auto simp add: tocks.intros)
next
  fix X
  assume "Event e \<notin> X"
  then show "\<exists>\<rho>\<in>tocks UNIV.
            \<exists>\<sigma>. ((\<exists>s\<in>tocks {x. x \<noteq> Tock \<and> x \<noteq> Event e}. \<rho> @ \<sigma> = s \<or> (\<exists>X. Tock \<notin> X \<and> Event e \<notin> X \<and> \<rho> @ \<sigma> = s @ [[X]\<^sub>R])) \<or>
                 (\<exists>s\<in>tocks {x. x \<noteq> Tock \<and> x \<noteq> Event e}. \<rho> @ \<sigma> = s \<or> (\<exists>\<sigma>'\<in>P. \<rho> @ \<sigma> = s @ [Event e]\<^sub>E # \<sigma>'))) \<and>
                (\<exists>\<tau>. (\<rho> = [] \<and> \<tau> = [] \<or> (\<exists>X. \<rho> @ \<tau> = [[X]\<^sub>R])) \<and>
                     (\<forall>\<rho>'\<in>tocks UNIV. \<rho>' \<le>\<^sub>C \<rho> @ \<sigma> \<longrightarrow> \<rho>' \<le>\<^sub>C \<rho>) \<and>
                     (\<forall>\<rho>'\<in>tocks UNIV. \<rho>' \<le>\<^sub>C \<rho> @ \<tau> \<longrightarrow> \<rho>' \<le>\<^sub>C \<rho>) \<and>
                     (\<forall>X. \<sigma> = [[X]\<^sub>R] \<longrightarrow> (\<exists>Y. \<tau> = [[Y]\<^sub>R] \<and> (\<forall>e. (e \<in> X) = (e \<in> Y) \<or> e = Tock))) \<and>
                     (\<forall>X. \<tau> = [[X]\<^sub>R] \<longrightarrow> (\<exists>Y. \<sigma> = [[Y]\<^sub>R] \<and> (\<forall>e. (e \<in> X) = (e \<in> Y) \<or> e = Tock))) \<and> ([[X]\<^sub>R] = \<rho> @ \<sigma> \<or> [[X]\<^sub>R] = \<rho> @ \<tau>))"
    apply (rule_tac x="[]" in bexI, auto)
    apply (rule_tac x="[[{x\<in>X. x \<noteq> Tock}]\<^sub>R]" in exI, safe, simp_all add: tocks.intros)
    apply (rule_tac x="[[X]\<^sub>R]" in exI, auto)
    using refusal_notin_tocks tt_prefix_notfront_is_whole by force+
next
  fix \<sigma>
  assume "\<sigma> \<in> P"
  then show "\<exists>\<rho>\<in>tocks UNIV.
            \<exists>\<sigma>'. ((\<exists>s\<in>tocks {x. x \<noteq> Tock \<and> x \<noteq> Event e}. \<rho> @ \<sigma>' = s \<or> (\<exists>X. Tock \<notin> X \<and> Event e \<notin> X \<and> \<rho> @ \<sigma>' = s @ [[X]\<^sub>R])) \<or>
                  (\<exists>s\<in>tocks {x. x \<noteq> Tock \<and> x \<noteq> Event e}. \<rho> @ \<sigma>' = s \<or> (\<exists>\<sigma>\<in>P. \<rho> @ \<sigma>' = s @ [Event e]\<^sub>E # \<sigma>))) \<and>
                 (\<exists>\<tau>. (\<rho> = [] \<and> \<tau> = [] \<or> (\<exists>X. \<rho> @ \<tau> = [[X]\<^sub>R])) \<and>
                      (\<forall>\<rho>'\<in>tocks UNIV. \<rho>' \<le>\<^sub>C \<rho> @ \<sigma>' \<longrightarrow> \<rho>' \<le>\<^sub>C \<rho>) \<and>
                      (\<forall>\<rho>'\<in>tocks UNIV. \<rho>' \<le>\<^sub>C \<rho> @ \<tau> \<longrightarrow> \<rho>' \<le>\<^sub>C \<rho>) \<and>
                      (\<forall>X. \<sigma>' = [[X]\<^sub>R] \<longrightarrow> (\<exists>Y. \<tau> = [[Y]\<^sub>R] \<and> (\<forall>e. (e \<in> X) = (e \<in> Y) \<or> e = Tock))) \<and>
                      (\<forall>X. \<tau> = [[X]\<^sub>R] \<longrightarrow> (\<exists>Y. \<sigma>' = [[Y]\<^sub>R] \<and> (\<forall>e. (e \<in> X) = (e \<in> Y) \<or> e = Tock))) \<and>
                      ([Event e]\<^sub>E # \<sigma> = \<rho> @ \<sigma>' \<or> [Event e]\<^sub>E # \<sigma> = \<rho> @ \<tau>))"
    apply (rule_tac x="[]" in bexI, auto)
    apply (rule_tac x="[Event e]\<^sub>E # \<sigma>" in exI, safe, simp_all add: tocks.intros)
    apply (erule_tac x="[]" in ballE, safe, simp_all add: tocks.intros, blast)
    by (rule_tac x="[]" in exI, auto, metis tocks.simps tt_prefix.simps(2) tt_prefix_refl ttobs.simps(4))
qed

end