theory TickTock_Max_TT1

imports
  "TickTock.TickTock_Core"
  TickTock_Max_FL
begin

text \<open> This theory consists in the definition of a Galois connection between
       tick-tock (that is TT-healthy, and so TT1-healthy) and the superset 
       that is not TT1-healhty, where refusals are maximal. \<close>

section \<open> From Maximal Refusals to subset-closed traces of tick-tock. \<close>

subsection \<open> Closure properties of mkTT1 \<close>

lemma TT2w_mkTT1_part:
  assumes "Y \<inter> {e. e \<noteq> Tock \<and> (\<exists>\<sigma>. \<rho> @ [[e]\<^sub>E] \<lesssim>\<^sub>C \<sigma> \<and> \<sigma> \<in> P) \<or> e = Tock \<and> (\<exists>\<sigma>. \<rho> @ [[X]\<^sub>R, [e]\<^sub>E] \<lesssim>\<^sub>C \<sigma> \<and> \<sigma> \<in> P)} = {}"
          "\<rho> @ [[X]\<^sub>R] \<lesssim>\<^sub>C \<sigma>" "\<sigma> \<in> P" "TT1w P" "TTwf P" "TTM1 P" "TTM2 P" "TT2w P"
    shows "\<exists>\<sigma>. \<rho> @ [[X \<union> Y]\<^sub>R] \<lesssim>\<^sub>C \<sigma> \<and> \<sigma> \<in> P"
proof -
  have "size (\<rho> @ [[X]\<^sub>R]) \<le> size \<sigma>"
    apply auto
    using assms tt_prefix_subset_length by fastforce
  then obtain \<rho>\<^sub>2 X\<^sub>2 z where X2:"\<sigma> = \<rho>\<^sub>2 @ [[X\<^sub>2]\<^sub>R] @ z \<and> X \<subseteq> X\<^sub>2 \<and> \<rho> \<lesssim>\<^sub>C \<rho>\<^sub>2 \<and> size (\<rho>\<^sub>2 @ [[X\<^sub>2]\<^sub>R]) = size (\<rho> @ [[X]\<^sub>R]) \<and> (\<rho>\<^sub>2 @ [[X\<^sub>2]\<^sub>R] @ z) \<in> P"
    using assms(2,3,4)
    ttWF_tt_prefix_subset_exists_three_part_iff
    by (metis TTwf_def assms(5) length_append_singleton)
  then have "\<rho>\<^sub>2 @ [[X\<^sub>2]\<^sub>R] \<in> P"
    by (metis TT1w_prefix_concat_in append.assoc assms(4))
  then have "(\<forall>e. (\<rho>\<^sub>2 @ [[X\<^sub>2]\<^sub>R] \<in> P \<and> e \<notin> X\<^sub>2 \<and> e \<noteq> Tock) \<longrightarrow> \<rho>\<^sub>2 @ [[e]\<^sub>E] \<in> P)"
            "(\<forall>e. (\<rho>\<^sub>2 @ [[X\<^sub>2]\<^sub>R] \<in> P \<and> e \<notin> X\<^sub>2 \<and> e = Tock) \<longrightarrow> \<rho>\<^sub>2 @ [[X\<^sub>2]\<^sub>R,[e]\<^sub>E] \<in> P)"
    using assms by (auto simp add:TTM1_def TTM2_def)
  then have "\<forall>e. (\<rho>\<^sub>2 @ [[e]\<^sub>E] \<notin> P \<and> e \<noteq> Tock) \<longrightarrow> e \<in> X\<^sub>2"
    using assms \<open>\<rho>\<^sub>2 @ [[X\<^sub>2]\<^sub>R] \<in> P\<close> by blast
  then obtain Z where Z:"Z \<inter> {e. (e \<noteq> Tock \<and> \<rho>\<^sub>2 @ [[e]\<^sub>E] \<in> P) \<or> (e = Tock \<and> \<rho>\<^sub>2 @ [[X\<^sub>2]\<^sub>R, [e]\<^sub>E] \<in> P) } = {}"
    by blast
  then have "\<rho>\<^sub>2 @ [[X\<^sub>2 \<union> Z]\<^sub>R] \<in> P"
    using assms by (simp add: TT2w_def \<open>\<rho>\<^sub>2 @ [[X\<^sub>2]\<^sub>R] \<in> P\<close>)
  then have "\<forall>e. \<rho> @ [[e]\<^sub>E] \<lesssim>\<^sub>C \<rho>\<^sub>2 @ [[e]\<^sub>E]"
    by (metis Suc_le_mono X2 antisym_conv tt_prefix_subset_eq_length_common_prefix_eq tt_prefix_subset_length tt_prefix_subset_refl length_append_singleton)
  then have "\<forall>e. \<rho> @ [[X]\<^sub>R, [e]\<^sub>E] \<lesssim>\<^sub>C \<rho>\<^sub>2 @ [[X\<^sub>2]\<^sub>R, [e]\<^sub>E]"
    by (metis X2 tt_prefix_subset.simps(2) tt_prefix_subset_eq_length_common_prefix_eq length_append_singleton nat.simps(1))
  then have "{e. (e \<noteq> Tock \<and> \<rho>\<^sub>2 @ [[e]\<^sub>E] \<in> P) \<or> (e = Tock \<and> \<rho>\<^sub>2 @ [[X\<^sub>2]\<^sub>R, [e]\<^sub>E] \<in> P) }
             \<subseteq>
             {e. e \<noteq> Tock \<and> (\<exists>\<sigma>. \<rho> @ [[e]\<^sub>E] \<lesssim>\<^sub>C \<sigma> \<and> \<sigma> \<in> P) \<or> e = Tock \<and> (\<exists>\<sigma>. \<rho> @ [[X]\<^sub>R, [e]\<^sub>E] \<lesssim>\<^sub>C \<sigma> \<and> \<sigma> \<in> P)}
             "
    apply auto
    using \<open>\<forall>e. \<rho> @ [[e]\<^sub>E] \<lesssim>\<^sub>C \<rho>\<^sub>2 @ [[e]\<^sub>E]\<close> apply blast
    using \<open>\<forall>e. \<rho> @ [[e]\<^sub>E] \<lesssim>\<^sub>C \<rho>\<^sub>2 @ [[e]\<^sub>E]\<close> by blast
  then have "X \<union> Y \<subseteq> X\<^sub>2 \<union> Z"
    using X2 apply safe
    apply blast (* FIXME: The next step deserves a better understanding. *)
    by (smt CollectI \<open>\<forall>e. \<rho>\<^sub>2 @ [[X\<^sub>2]\<^sub>R] \<in> P \<and> e \<notin> X\<^sub>2 \<and> e = Tock \<longrightarrow> \<rho>\<^sub>2 @ [[X\<^sub>2]\<^sub>R, [e]\<^sub>E] \<in> P\<close> \<open>\<forall>e. \<rho>\<^sub>2 @ [[X\<^sub>2]\<^sub>R] \<in> P \<and> e \<notin> X\<^sub>2 \<and> e \<noteq> Tock \<longrightarrow> \<rho>\<^sub>2 @ [[e]\<^sub>E] \<in> P\<close> \<open>\<rho>\<^sub>2 @ [[X\<^sub>2]\<^sub>R] \<in> P\<close> assms(1) disjoint_iff_not_equal subsetCE)
  then have "\<rho> @ [[X \<union> Y]\<^sub>R] \<lesssim>\<^sub>C \<rho>\<^sub>2 @ [[X\<^sub>2 \<union> Z]\<^sub>R]"
    by (metis X2 tt_prefix_subset.simps(2) tt_prefix_subset_eq_length_common_prefix_eq tt_prefix_subset_refl length_append_singleton nat.simps(1))
  then show ?thesis
    using \<open>\<rho>\<^sub>2 @ [[X\<^sub>2 \<union> Z]\<^sub>R] \<in> P\<close> by blast
qed

abbreviation "TT2P \<rho> X P == {e. e \<noteq> Tock \<and> (\<exists>\<sigma>. \<rho> @ [[e]\<^sub>E] \<lesssim>\<^sub>C \<sigma> \<and> \<sigma> \<in> P) \<or> e = Tock \<and> (\<exists>\<sigma>. \<rho> @ [[X]\<^sub>R, [e]\<^sub>E] \<lesssim>\<^sub>C \<sigma> \<and> \<sigma> \<in> P)}"

lemma TT2_mkTT1_part:
  assumes "Y \<inter> TT2P \<rho> X P = {}"
          "\<rho> @ [[X]\<^sub>R] @ s \<lesssim>\<^sub>C \<sigma>" "\<sigma> \<in> P" "TT1w P" "TTM1 P" "TTM2 P" "TT2 P"
    shows "\<exists>\<sigma>. \<rho> @ [[X \<union> Y]\<^sub>R] @ s \<lesssim>\<^sub>C \<sigma> \<and> \<sigma> \<in> P"
proof -
  have "size (\<rho> @ [[X]\<^sub>R]) \<le> size \<sigma>"
    apply auto
    using assms tt_prefix_subset_length by fastforce
  then obtain \<rho>\<^sub>2 X\<^sub>2 z where X2:"\<sigma> = \<rho>\<^sub>2 @ [[X\<^sub>2]\<^sub>R] @ z \<and> X \<subseteq> X\<^sub>2 \<and> \<rho> \<lesssim>\<^sub>C \<rho>\<^sub>2 \<and> size (\<rho>\<^sub>2 @ [[X\<^sub>2]\<^sub>R]) = size (\<rho> @ [[X]\<^sub>R]) \<and> (\<rho>\<^sub>2 @ [[X\<^sub>2]\<^sub>R] @ z) \<in> P"
    using assms(2,3,4)
    ttWF_tt_prefix_subset_exists_three_part_concat
    by (metis length_append_singleton)
    (* by (metis TTwf_def assms(5) length_append_singleton) *)
  then have "\<rho>\<^sub>2 @ [[X\<^sub>2]\<^sub>R] @ z \<in> P"
      "\<rho>\<^sub>2 @ [[X\<^sub>2]\<^sub>R] \<in> P"
    by (metis TT1w_prefix_concat_in append.assoc assms(4))+
  then have "(\<forall>e. (\<rho>\<^sub>2 @ [[X\<^sub>2]\<^sub>R] \<in> P \<and> e \<notin> X\<^sub>2 \<and> e \<noteq> Tock) \<longrightarrow> \<rho>\<^sub>2 @ [[e]\<^sub>E] \<in> P)"
            "(\<forall>e. (\<rho>\<^sub>2 @ [[X\<^sub>2]\<^sub>R] \<in> P \<and> e \<notin> X\<^sub>2 \<and> e = Tock) \<longrightarrow> \<rho>\<^sub>2 @ [[X\<^sub>2]\<^sub>R,[e]\<^sub>E] \<in> P)"
    using assms by (auto simp add:TTM1_def TTM2_def)
  then have "\<forall>e. (\<rho>\<^sub>2 @ [[e]\<^sub>E] \<notin> P \<and> e \<noteq> Tock) \<longrightarrow> e \<in> X\<^sub>2"
    using assms \<open>\<rho>\<^sub>2 @ [[X\<^sub>2]\<^sub>R] \<in> P\<close> by blast
  then obtain Z where Z:"Z \<inter> {e. (e \<noteq> Tock \<and> \<rho>\<^sub>2 @ [[e]\<^sub>E] \<in> P) \<or> (e = Tock \<and> \<rho>\<^sub>2 @ [[X\<^sub>2]\<^sub>R, [e]\<^sub>E] \<in> P) } = {}"
    by blast
  then have "\<rho>\<^sub>2 @ [[X\<^sub>2 \<union> Z]\<^sub>R] @ z \<in> P"
    using assms TT2_def
    by (simp add: TT2_def Z X2)
  then have "\<forall>e. \<rho> @ [[e]\<^sub>E] @ z \<lesssim>\<^sub>C \<rho>\<^sub>2 @ [[e]\<^sub>E] @ z"
    by (metis Suc_le_mono X2 antisym_conv tt_prefix_subset_eq_length_common_prefix_eq tt_prefix_subset_length tt_prefix_subset_refl length_append_singleton)
  then have "\<forall>e. \<rho> @ [[X]\<^sub>R, [e]\<^sub>E] @ z \<lesssim>\<^sub>C \<rho>\<^sub>2 @ [[X\<^sub>2]\<^sub>R, [e]\<^sub>E] @ z"
    by (metis X2 append_Cons tt_prefix_subset.simps(2) tt_prefix_subset_eq_length_common_prefix_eq length_append_singleton nat.simps(1))
  then have "{e. (e \<noteq> Tock \<and> \<rho>\<^sub>2 @ [[e]\<^sub>E] \<in> P) \<or> (e = Tock \<and> \<rho>\<^sub>2 @ [[X\<^sub>2]\<^sub>R, [e]\<^sub>E] \<in> P) }
             \<subseteq>
             {e. e \<noteq> Tock \<and> (\<exists>\<sigma>. \<rho> @ [[e]\<^sub>E] \<lesssim>\<^sub>C \<sigma> \<and> \<sigma> \<in> P) \<or> e = Tock \<and> (\<exists>\<sigma>. \<rho> @ [[X]\<^sub>R, [e]\<^sub>E] \<lesssim>\<^sub>C \<sigma> \<and> \<sigma> \<in> P)}
             "
    apply auto 
    apply (metis X2 tt_prefix_subset_eq_length_common_prefix_eq tt_prefix_subset_refl length_append_singleton nat.simps(1))
      apply (metis X2 tt_prefix_subset_eq_length_common_prefix_eq tt_prefix_subset_refl length_append_singleton nat.simps(1))
      apply (metis X2 \<open>\<forall>e. \<rho> @ [[X]\<^sub>R, [e]\<^sub>E] @ z \<lesssim>\<^sub>C \<rho>\<^sub>2 @ [[X\<^sub>2]\<^sub>R, [e]\<^sub>E] @ z\<close> tt_prefix_subset_eq_length_common_prefix_eq length_Cons length_append_singleton nat.simps(1))
      by (metis X2 tt_prefix_subset.simps(2) tt_prefix_subset_eq_length_common_prefix_eq tt_prefix_subset_refl length_append_singleton nat.simps(1))
  then have "X \<union> Y \<subseteq> X\<^sub>2 \<union> Z"
    using X2 apply safe
    apply blast (* FIXME: The next step deserves a better understanding. *)
    by (smt CollectI \<open>\<forall>e. \<rho>\<^sub>2 @ [[X\<^sub>2]\<^sub>R] \<in> P \<and> e \<notin> X\<^sub>2 \<and> e = Tock \<longrightarrow> \<rho>\<^sub>2 @ [[X\<^sub>2]\<^sub>R, [e]\<^sub>E] \<in> P\<close> \<open>\<forall>e. \<rho>\<^sub>2 @ [[X\<^sub>2]\<^sub>R] \<in> P \<and> e \<notin> X\<^sub>2 \<and> e \<noteq> Tock \<longrightarrow> \<rho>\<^sub>2 @ [[e]\<^sub>E] \<in> P\<close> \<open>\<rho>\<^sub>2 @ [[X\<^sub>2]\<^sub>R] \<in> P\<close> assms(1) disjoint_iff_not_equal subsetCE)
  then have "\<rho> @ [[X \<union> Y]\<^sub>R] @ s \<lesssim>\<^sub>C \<rho>\<^sub>2 @ [[X\<^sub>2 \<union> Z]\<^sub>R] @ s"
    by (metis X2 append_Cons tt_prefix_subset.simps(2) tt_prefix_subset_eq_length_common_prefix_eq tt_prefix_subset_refl length_append_singleton nat.simps(1))
  then show ?thesis
  proof -
    have f1: "\<forall>cs c. [c::'a ttobs] @ cs = c # cs"
    by simp
      have "\<rho> @ [[X]\<^sub>R] @ s \<lesssim>\<^sub>C \<sigma>"
        using assms(2) by force
      then have "s \<lesssim>\<^sub>C z"
        by (metis (no_types) X2 append.assoc tt_prefix_subset_eq_length_common_prefix_eq)
      then show ?thesis
        using f1 by (metis (no_types) X2 \<open>X \<union> Y \<subseteq> X\<^sub>2 \<union> Z\<close> \<open>\<rho>\<^sub>2 @ [[X\<^sub>2 \<union> Z]\<^sub>R] @ z \<in> P\<close> tt_prefix_subset.simps(2) tt_prefix_subset_eq_length_common_prefix_eq length_append_singleton nat.simps(1))
    qed
qed

lemma TT2w_mkTT1:
  assumes "TT2w P" "TT1w P" "TTM1 P" "TTM2 P" "TTwf P"
  shows "TT2w(mkTT1(P))"
proof -
  have "TT2w(mkTT1(P)) = TT2w({\<rho>|\<rho> \<sigma>. \<rho> \<lesssim>\<^sub>C \<sigma> \<and> \<sigma> \<in> P})"
    by (simp add:mkTT1_simp)
  also have "... = True"
    unfolding TT2w_def apply auto
    using assms by (simp add: TT2w_mkTT1_part)
  finally show ?thesis by auto
qed

lemma TT2_mkTT1:
  assumes "TT2 P" "TT1w P" "TTM1 P" "TTM2 P"
  shows "TT2(mkTT1(P))"
proof -
  have "TT2(mkTT1(P)) = TT2({\<rho>|\<rho> \<sigma>. \<rho> \<lesssim>\<^sub>C \<sigma> \<and> \<sigma> \<in> P})"
    by (simp add:mkTT1_simp)
  also have "... = True"
    using assms TT2_mkTT1_part unfolding TT2_def apply auto
    by (insert TT2_mkTT1_part, blast)
  then show ?thesis using calculation by auto
qed

section \<open> From subset-closed tick-tock to maximal refusals. \<close>

text \<open> Here the adjoint is defined in terms of mkTT1, undoing as much
       as possible the effect of mkTT1. \<close>

definition unTT1 :: "'e ttobs list set \<Rightarrow> 'e ttobs list set" where
"unTT1 P = \<Union>{x. TTM1 x \<and> TTM2 x \<and> TTM3 x \<and> TT1w x \<and> (mkTT1 x) \<subseteq> P}"

text \<open> Although in this definition we do not use all the healthiness conditions
       of TickTock_Max (as standard for an adjoint of a Galois connection), note 
       that an equivalent definition can be obtained for healthy P, that is, when
       applied to tick-tock processes as proved in {@lemma unTT1_alt} in TickTock_FL.thy. 

       The fact we do not use the conjunction of all healthiness conditions in {@term unTT1}
       makes it simpler to construct unTT1 results, notably simplifying the proofs
       for the Galois connections. \<close>

lemma unTT1_mono:
  assumes "P \<subseteq> Q"
  shows "unTT1(P) \<subseteq> unTT1(Q)"
  using assms unfolding unTT1_def by auto

subsection \<open> Closure properties \<close>

lemma TTM1_unTT1:
  "TTM1(unTT1 P)"
  unfolding unTT1_def TTM1_def by auto

lemma TTwf_unTT1:
  assumes "TTwf P"
  shows "TTwf(unTT1 P)"
  using assms unfolding unTT1_def TTwf_def apply auto
  using TT1_mkTT1 TT1_mkTT1_simp by blast

lemma TT0_unTT1:
  assumes "TT0 P" "TT1 P"
  shows "TT0(unTT1(P))"
proof -
  have "[] \<in> P"
    using assms TT0_TT1_empty by blast
  then have "[] \<in> unTT1(P)"
    unfolding unTT1_def TT0_def apply auto
    apply (rule_tac x="{[]}" in exI, auto)
    unfolding TTM1_def TTM2_def TTM3_def TT1w_def apply auto
     apply (case_tac \<rho>, auto)
    unfolding mkTT1_def apply auto
    by (case_tac x, auto)
  then have "TT0(unTT1(P))"
    unfolding TT0_def by auto
  then show ?thesis .
qed

lemma TT1w_unTT1:
  "TT1w(unTT1(P))"
  unfolding unTT1_def TT1w_def by auto

lemma TTM1_mkTT3w:
  assumes "TTM1 P" "TTM3 P"
  shows "TTM1 (mkTT3w P)"
  using assms unfolding TTM1_def TTM3_def mkTT3w_def apply auto
  by (metis TTickTrace_eq_add_Tick_refusal_trace_fixpoint)

lemma TTM2_mkTT3w:
  assumes "TTM2 P" "TTM3 P"
  shows "TTM2 (mkTT3w P)"
  using assms unfolding TTM2_def TTM3_def mkTT3w_def apply auto
  by (metis TTickTrace_eq_add_Tick_refusal_trace_fixpoint)

lemma TTM3_mkTT3w:
  assumes "TTM3 P"
  shows "TTM3 (mkTT3w P)"
  using assms unfolding TTM3_def mkTT3w_def apply auto
  by (metis TTickTrace_eq_add_Tick_refusal_trace_fixpoint)

lemma TT1w_mkTT3w:
  assumes "TT1w P"
  shows "TT1w (mkTT3w P)"
  using assms unfolding TT1w_def TTM3_def mkTT3w_def apply auto
  by (smt add_Tick_refusal_trace_concat add_Tick_refusal_trace_tt_subset append_eq_append_conv tt_prefix_decompose tt_prefix_tt_subset tt_subset_same_length)

lemma TT3w_unTT1:
  assumes "TT1 P" "TT3w P" 
  shows "TT3w(unTT1(P))"
  using assms unfolding TT3w_def unTT1_def  apply auto
  apply (rule_tac x="mkTT3w(x)" in exI, auto)
  using TTM1_mkTT3w apply blast
  using TTM2_mkTT3w apply blast
  using TTM3_mkTT3w apply blast
  using TT1w_mkTT3w apply blast
   apply (smt TT1_fixpoint_mkTT1 TT1_mkTT1_simp UnE mem_Collect_eq mkTT1_mono mkTT3w_def subsetI)
  unfolding mkTT3w_def by auto

lemma TT2_unTT1_part:
  assumes "TT P"
          "Y \<inter> {e. e \<noteq> Tock \<and> \<rho> @ [[e]\<^sub>E] \<in> unTT1 P \<or> e = Tock \<and> \<rho> @ [[X]\<^sub>R, [e]\<^sub>E] \<in> unTT1 P} = {}"
          "\<rho> @ [X]\<^sub>R # \<sigma> \<in> unTT1 P"
  shows   "\<rho> @ [[X \<union> Y]\<^sub>R] @ \<sigma> \<in> unTT1 P"
proof -
  obtain x where x:"TTM1 x" "TTM2 x" "TTM3 x" "TT1w x" "mkTT1 x \<subseteq> P" "\<rho> @ [X]\<^sub>R # \<sigma> \<in> x"
    using assms unfolding unTT1_def by auto
  
  have def1:"(Y \<inter> {e. e \<noteq> Tock \<and> \<rho> @ [[e]\<^sub>E] \<in> unTT1 P \<or> e = Tock \<and> \<rho> @ [[X]\<^sub>R, [e]\<^sub>E] \<in> unTT1 P} = {})
              =
             (Y \<inter> {e. e \<noteq> Tock \<and> (\<exists>x. TTM1 x \<and> TTM2 x \<and> TTM3 x \<and> TT1w x \<and> mkTT1 x \<subseteq> P \<and> \<rho> @ [[e]\<^sub>E] \<in> x) \<or>
                 e = Tock \<and> (\<exists>x. TTM1 x \<and> TTM2 x \<and> TTM3 x \<and> TT1w x \<and> mkTT1 x \<subseteq> P \<and> \<rho> @ [[X]\<^sub>R, [e]\<^sub>E] \<in> x)} = {})"
    unfolding unTT1_def by auto

  have "\<rho> @ [[X]\<^sub>R] \<le>\<^sub>C \<rho> @ [X]\<^sub>R # \<sigma>"
    by (simp add: tt_prefix_same_front)
  then have "\<rho> @ [[X]\<^sub>R] \<in> x"
    using TT1w_def x assms by blast
  then have "\<rho> @ [[X]\<^sub>R] \<in> P"
    using assms x mkTT1_def by fastforce

  have "\<forall>e. (e \<noteq> Tock \<and> e \<in> Y) \<longrightarrow> \<not>(\<exists>x. TTM1 x \<and> TTM2 x \<and> TTM3 x \<and> TT1w x \<and> mkTT1 x \<subseteq> P \<and> \<rho> @ [[e]\<^sub>E] \<in> x)"
    using assms def1 by blast
  then have "\<forall>e. (e \<noteq> Tock \<and> e \<in> Y) \<longrightarrow> \<rho> @ [[e]\<^sub>E] \<notin> x"
    using assms x by blast
  then have "\<forall>e. (e \<noteq> Tock \<and> e \<in> Y) \<longrightarrow> (\<rho> @ [[X]\<^sub>R] \<in> P \<longrightarrow> e \<in> X)"
    using assms x TTM1_def \<open>\<rho> @ [[X]\<^sub>R] \<in> x\<close> by blast
  then have "\<forall>e. (e \<noteq> Tock \<and> e \<in> Y) \<longrightarrow> e \<in> X"
    using \<open>\<rho> @ [[X]\<^sub>R] \<in> P\<close> by blast
  
  have "\<forall>e. (e = Tock \<and> e \<in> Y) \<longrightarrow> \<not>(\<exists>x. TTM1 x \<and> TTM2 x \<and> TTM3 x \<and> TT1w x \<and> mkTT1 x \<subseteq> P \<and> \<rho> @ [[X]\<^sub>R, [e]\<^sub>E] \<in> x)"
    using assms def1 by blast
  then have "\<forall>e. (e = Tock \<and> e \<in> Y) \<longrightarrow> \<rho> @ [[X]\<^sub>R, [e]\<^sub>E] \<notin> x"
    using assms x by blast
  then have "\<forall>e. (e = Tock \<and> e \<in> Y) \<longrightarrow> (\<rho> @ [[X]\<^sub>R,[e]\<^sub>E] \<in> P \<longrightarrow> e \<in> X)"
    using TTM2_def \<open>\<rho> @ [[X]\<^sub>R] \<in> x\<close> assms x by auto
  then have "\<forall>e. (e = Tock \<and> e \<in> Y) \<longrightarrow> e \<in> X"
    using TTM2_def \<open>\<forall>e. e = Tock \<and> e \<in> Y \<longrightarrow> \<rho> @ [[X]\<^sub>R, [e]\<^sub>E] \<notin> x\<close> \<open>\<rho> @ [[X]\<^sub>R] \<in> x\<close> assms x by auto

  have "Y \<subseteq> X"
    using \<open>\<forall>e. e = Tock \<and> e \<in> Y \<longrightarrow> e \<in> X\<close> \<open>\<forall>e. e \<noteq> Tock \<and> e \<in> Y \<longrightarrow> e \<in> X\<close> by blast
  then show ?thesis using def1 x unfolding unTT1_def apply auto
    by (metis assms sup.order_iff)
qed

lemma TT2_unTT1:
  assumes "TT P"
  shows "TT2(unTT1(P))"
  using assms unfolding TT2_def apply auto
  using TT2_unTT1_part by fastforce

lemma ttWFx_unTT1:
  assumes "TT1 P" "ttWFx P" 
  shows "ttWFx(unTT1(P))"
  using assms unfolding ttWFx_def unTT1_def  apply auto
  using TT1_mkTT1_simp ttWFx_def TT_ttWFx by blast

lemma TTM2_unTT1:
  "TTM2(unTT1(P))"
  unfolding unTT1_def TTM2_def by auto

lemma TTM3_unTT1:
  "TTM3(unTT1(P))"
  unfolding unTT1_def TTM3_def by auto

lemma unTT1_TT_closure:
  assumes "TT P" "TT2 P" "TT3w P"
  shows "TT0 (unTT1 P)"
       "TTwf (unTT1 P)"
       "TT1w (unTT1 P)" 
       "TT2 (unTT1 P)" 
       "ttWFx (unTT1 P)" 
       "TT3w (unTT1 P)" 
       "TTM1 (unTT1 P)" 
       "TTM2 (unTT1 P)" 
       "TTM3 (unTT1 P)"
    using assms TT0_unTT1 TT_def apply blast
    using TTwf_unTT1 TT_def
    using TT_TTwf assms(1) apply blast
    apply (simp add: TT1w_unTT1)
         apply (simp add: TT2_unTT1 assms(1))
        apply (simp add: ttWFx_unTT1 TT_TT1 TT_ttWFx assms(1))
       apply (simp add: TT3w_unTT1 TT_TT1 assms(1) assms(3))
      apply (simp add: TTM1_unTT1)
   apply (simp add: TTM2_unTT1)
    by (simp add: TTM3_unTT1)

lemma mkTT1_TT_closure:
  assumes "TT0 P"
          "TTwf P"
          "TT1w P" 
          "TT2 P" 
          "ttWFx P" 
          "TT3w P" 
          "TTM1 P" 
          "TTM2 P" 
          "TTM3 P"
    shows "TTwf(mkTT1 P)" "TT0(mkTT1 P)" "TT1(mkTT1 P)" "TT2(mkTT1 P)" "ttWFx(mkTT1 P)" "TT3w(mkTT1 P)"
  using assms TTwf_mkTT1 apply blast
  using assms TT0_mkTT1 apply blast
  using assms TT1_mkTT1 apply blast
  using assms TT2_mkTT1 apply blast
  using assms ttWFx_mkTT1 apply blast
  using assms TT3w_mkTT1 by blast

lemma unTT1_subseteq:
  assumes "TT P"
  shows "unTT1 P \<subseteq> P"
  using assms apply (simp add:unTT1_def, auto)
  using TT1_mkTT1 TT1_mkTT1_simp by blast

lemma mkTT1_unTT1_subseteq:
  assumes "TT P"
  shows "mkTT1(unTT1 P) \<subseteq> P"
  by (metis TT1_fixpoint_mkTT1 TT_TT1 assms mkTT1_mono unTT1_subseteq)  

lemma less_eq_unTT1_mkTT1:
  assumes "TT0 P"
          "TTwf P"
          "TT1w P" 
          "TT2 P" 
          "ttWFx P" 
          "TT3w P" 
          "TTM1 P" 
          "TTM2 P" 
          "TTM3 P"
  shows "P \<subseteq> unTT1(mkTT1 P)"
  using assms by (simp add:unTT1_def, auto)

end