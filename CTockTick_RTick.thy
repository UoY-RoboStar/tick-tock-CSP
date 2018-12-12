theory CTockTick_RTick

imports
  CTockTick_Core
  CTockTick_FL
  CTockTick_Prioritise
begin

definition mkCT1 :: "'e cttobs list set \<Rightarrow> 'e cttobs list set" where
"mkCT1 P = P \<union> {\<rho>|\<rho> \<sigma>. \<rho> \<lesssim>\<^sub>C \<sigma> \<and> \<sigma> \<in> P}"

lemma CT1_fixpoint_mkCT1:
  "(mkCT1 P = P) = CT1 P"
  unfolding mkCT1_def CT1_def by auto

lemma mkCT1_simp:
  "mkCT1 P = {\<rho>|\<rho> \<sigma>. \<rho> \<lesssim>\<^sub>C \<sigma> \<and> \<sigma> \<in> P}"
  unfolding mkCT1_def apply auto
  using ctt_prefix_subset_refl by blast

lemma mkCT1_mono:
  assumes "P \<subseteq> Q"
  shows "mkCT1 P \<subseteq> mkCT1 Q"
  using assms unfolding mkCT1_def by auto

definition unCT1 :: "'e cttobs list set \<Rightarrow> 'e cttobs list set" where
"unCT1 P = \<Union>{x. CTM2a x \<and> CTM2b x \<and> CTTickAll x \<and> CT1c x \<and> (mkCT1 x) \<subseteq> P}"

lemma unCT1_mono:
  assumes "P \<subseteq> Q"
  shows "unCT1(P) \<subseteq> unCT1(Q)"
  using assms unfolding unCT1_def by auto

lemma
  assumes "CT4 P" "CT1 P"
  shows "P \<subseteq> mkCT1 (unCT1 P)"
  using assms unfolding mkCT1_def unCT1_def apply auto oops

lemma cttWF_Refusal_ctt_prefix:
  assumes "cttWF \<sigma>"
  shows "[[X]\<^sub>R] \<lesssim>\<^sub>C \<sigma> = (\<exists>Y z. \<sigma> = ([[Y]\<^sub>R] @ z) \<and> X \<subseteq> Y)"
  using assms apply auto
  apply (case_tac \<sigma>, auto)
  by (case_tac a, auto)

lemma ctt_prefix_eq_length_imp:
  assumes "xs @ [x] \<lesssim>\<^sub>C ys @ [y]"
          "List.length (xs @ [x]) = List.length (ys @ [y])"
    shows "[x] \<lesssim>\<^sub>C [y]"
  using assms by(induct xs ys rule:ctt_prefix_subset.induct, auto)

lemma ctt_prefix_eq_length_common_prefix:
  assumes "xs @ [x] \<lesssim>\<^sub>C ys @ [y]" "List.length (xs @ [x]) = List.length (ys @ [y])"
  shows "xs \<lesssim>\<^sub>C ys"
  using assms by(induct xs ys rule:ctt_prefix_subset.induct, auto)

lemma ctt_singleton_prefix_nonempty:
  assumes "[x] \<lesssim>\<^sub>C xa @ z" "xa \<noteq> []"
  shows "[x] \<lesssim>\<^sub>C xa"
  using assms apply (induct xa, auto)
  by (case_tac x, auto, case_tac a, auto, case_tac a, auto)

lemma ctt_prefix_gt_length_imp:
  assumes "xs @ [x] \<lesssim>\<^sub>C ys @ [y]"
          "List.length (xs @ [x]) < List.length (ys @ [y])"
    shows "xs @ [x] \<lesssim>\<^sub>C ys"
  using assms apply(induct xs ys rule:ctt_prefix_subset.induct, auto)
  using ctt_singleton_prefix_nonempty by blast 

lemma cttWF_ctt_prefix_subset_exists_three_part:
  assumes "cttWF \<sigma>" "\<rho> @ [[X]\<^sub>R] \<lesssim>\<^sub>C \<sigma>"
  shows "\<exists>Y z \<rho>\<^sub>2. \<sigma> = \<rho>\<^sub>2 @ ([[Y]\<^sub>R] @ z) \<and> X \<subseteq> Y \<and> \<rho> \<lesssim>\<^sub>C \<rho>\<^sub>2 \<and> size \<rho>\<^sub>2 = size \<rho>"
  using assms proof (induct \<sigma> arbitrary:X \<rho> rule:rev_induct)
  case Nil
  then show ?case using ctt_prefix_subset.simps(1) ctt_prefix_subset_antisym by blast
next
  case (snoc x xs)
  then show ?case
  proof (cases "size (\<rho> @ [[X]\<^sub>R]) = size (xs @ [x])")
    case True
    then have eq_lengths:"List.length (\<rho>) = List.length (xs)"
      by simp
    then show ?thesis
    proof (cases x)
      case (ObsEvent x1)
      then show ?thesis using snoc True
        by (meson ctt_prefix_eq_length_imp ctt_prefix_subset.simps(5))
    next
      case (Ref x2)
      then have xX2:"[[X]\<^sub>R] \<lesssim>\<^sub>C [[x2]\<^sub>R]"
                    "\<rho> \<lesssim>\<^sub>C xs"
        using True ctt_prefix_eq_length_imp snoc.prems(2) apply blast
        using True snoc ctt_prefix_eq_length_common_prefix by metis
      then have "X \<subseteq> x2" 
        by auto
      then have "xs @ [x] = xs @ [[x2]\<^sub>R] @ [] \<and> X \<subseteq> x2 \<and> \<rho> \<lesssim>\<^sub>C xs \<and> List.length (xs) = List.length (\<rho>)"
        using xX2 snoc eq_lengths Ref by auto
      then have "\<exists>\<rho>\<^sub>2. xs @ [x] = \<rho>\<^sub>2 @ [[x2]\<^sub>R] @ [] \<and> X \<subseteq> x2 \<and> \<rho> \<lesssim>\<^sub>C \<rho>\<^sub>2 \<and> List.length (\<rho>\<^sub>2) = List.length (\<rho>)"
        by blast
      then have "\<exists>Y \<rho>\<^sub>2. xs @ [x] = \<rho>\<^sub>2 @ [[Y]\<^sub>R] @ [] \<and> X \<subseteq> Y \<and> \<rho> \<lesssim>\<^sub>C \<rho>\<^sub>2 \<and> List.length (\<rho>\<^sub>2) = List.length (\<rho>)"
        by blast
      then have "\<exists>Y z \<rho>\<^sub>2. xs @ [x] = \<rho>\<^sub>2 @ [[Y]\<^sub>R] @ z \<and> X \<subseteq> Y \<and> \<rho> \<lesssim>\<^sub>C \<rho>\<^sub>2 \<and> List.length (\<rho>\<^sub>2) = List.length (\<rho>)"
        by blast
      then show ?thesis by blast
    qed
  next
    case False
    then have "List.length (\<rho> @ [[X]\<^sub>R]) < List.length (xs @ [x])"
      using snoc 
      by (meson ctt_prefix_subset_length le_neq_trans)
    then have "\<rho> @ [[X]\<^sub>R] \<lesssim>\<^sub>C xs"
      using snoc ctt_prefix_gt_length_imp by metis
    then have "\<exists>Y z \<rho>\<^sub>2. xs = \<rho>\<^sub>2 @ [[Y]\<^sub>R] @ z \<and> X \<subseteq> Y \<and> \<rho> \<lesssim>\<^sub>C \<rho>\<^sub>2 \<and> List.length \<rho>\<^sub>2 = List.length \<rho>"
      using snoc cttWF_prefix_is_cttWF by blast
    then have "\<exists>Y z \<rho>\<^sub>2. xs @ [x] = \<rho>\<^sub>2 @ [[Y]\<^sub>R] @ z @ [x] \<and> X \<subseteq> Y \<and> \<rho> \<lesssim>\<^sub>C \<rho>\<^sub>2 \<and> List.length \<rho>\<^sub>2 = List.length \<rho>"
      by auto
    then have "\<exists>Y z \<rho>\<^sub>2. xs @ [x] = \<rho>\<^sub>2 @ [[Y]\<^sub>R] @ z \<and> X \<subseteq> Y \<and> \<rho> \<lesssim>\<^sub>C \<rho>\<^sub>2 \<and> List.length \<rho>\<^sub>2 = List.length \<rho>"
      by blast
    then show ?thesis by blast
  qed
qed

lemma cttWF_ctt_prefix_subset_exists_three_part_concat:
  assumes "\<rho> @ [[X]\<^sub>R] @ s \<lesssim>\<^sub>C \<sigma>"
  shows "\<exists>Y z \<rho>\<^sub>2. \<sigma> = \<rho>\<^sub>2 @ ([[Y]\<^sub>R] @ z) \<and> X \<subseteq> Y \<and> \<rho> \<lesssim>\<^sub>C \<rho>\<^sub>2 \<and> s \<lesssim>\<^sub>C z \<and> size \<rho>\<^sub>2 = size \<rho>"
  using assms proof (induct \<rho> \<sigma> arbitrary:X s rule:ctt_prefix_subset.induct)
case (1 x)
  then show ?case 
    apply auto
    by (cases x, auto, case_tac a, auto)
next
  case (2 Z za Y ya)
  then have "za @ [[X]\<^sub>R] @ s \<lesssim>\<^sub>C ya"
    by simp
  then have "\<exists>Y z \<rho>\<^sub>2.
               ya = \<rho>\<^sub>2 @ [Y]\<^sub>R # z \<and>
               X \<subseteq> Y \<and> za \<lesssim>\<^sub>C \<rho>\<^sub>2 \<and> s \<lesssim>\<^sub>C z \<and> List.length \<rho>\<^sub>2 = List.length za"
    using 2 by auto
  then show ?case 
    apply auto
    by (metis "2.prems" append_Cons ctt_prefix_subset.simps(2) length_Cons)
next
  case (3 x xa y ya)
  then show ?case apply auto
    by (metis append_Cons ctt_prefix_subset.simps(3) length_Cons)
next
  case ("4_1" v xa va ya)
  then show ?case by auto
next
  case ("4_2" va xa v ya)
  then show ?case by auto
next
  case (5 x xa)
  then show ?case by auto
qed

lemma ctt_prefix_subset_eq_length_common_prefix_eq:
  assumes "List.length xs = List.length ys"
  shows "((xs @ z) \<lesssim>\<^sub>C (ys @ s)) = (xs \<lesssim>\<^sub>C ys \<and> z \<lesssim>\<^sub>C s)"
  using assms by(induct xs ys rule:ctt_prefix_subset.induct, auto)

lemma cttWF_ctt_prefix_subset_exists_three_part':
  assumes "\<sigma> = \<rho>\<^sub>2 @ ([[Y]\<^sub>R] @ z) \<and> X \<subseteq> Y \<and> \<rho> \<lesssim>\<^sub>C \<rho>\<^sub>2 \<and> size \<rho>\<^sub>2 = size \<rho>" "cttWF \<sigma>"
  shows "\<rho> @ [[X]\<^sub>R] \<lesssim>\<^sub>C \<sigma>"
  using assms apply auto 
  by (simp add: ctt_prefix_subset_eq_length_common_prefix_eq)

lemma cttWF_ctt_prefix_subset_exists_three_part_iff:
  assumes "cttWF \<sigma>"
  shows "\<rho> @ [[X]\<^sub>R] \<lesssim>\<^sub>C \<sigma> = (\<exists>Y z \<rho>\<^sub>2. \<sigma> = \<rho>\<^sub>2 @ ([[Y]\<^sub>R] @ z) \<and> X \<subseteq> Y \<and> \<rho> \<lesssim>\<^sub>C \<rho>\<^sub>2 \<and> size \<rho>\<^sub>2 = size \<rho>)"
  using assms
  by (meson cttWF_ctt_prefix_subset_exists_three_part cttWF_ctt_prefix_subset_exists_three_part')
 
lemma CT2_mkCT1_part:
  assumes "Y \<inter> {e. e \<noteq> Tock \<and> (\<exists>\<sigma>. \<rho> @ [[e]\<^sub>E] \<lesssim>\<^sub>C \<sigma> \<and> \<sigma> \<in> P) \<or> e = Tock \<and> (\<exists>\<sigma>. \<rho> @ [[X]\<^sub>R, [e]\<^sub>E] \<lesssim>\<^sub>C \<sigma> \<and> \<sigma> \<in> P)} = {}"
          "\<rho> @ [[X]\<^sub>R] \<lesssim>\<^sub>C \<sigma>" "\<sigma> \<in> P" "CT1c P" "CTwf P" "CTM2a P" "CTM2b P" "CT2 P"
    shows "\<exists>\<sigma>. \<rho> @ [[X \<union> Y]\<^sub>R] \<lesssim>\<^sub>C \<sigma> \<and> \<sigma> \<in> P"
proof -
  have "size (\<rho> @ [[X]\<^sub>R]) \<le> size \<sigma>"
    apply auto
    using assms ctt_prefix_subset_length by fastforce
  then obtain \<rho>\<^sub>2 X\<^sub>2 z where X2:"\<sigma> = \<rho>\<^sub>2 @ [[X\<^sub>2]\<^sub>R] @ z \<and> X \<subseteq> X\<^sub>2 \<and> \<rho> \<lesssim>\<^sub>C \<rho>\<^sub>2 \<and> size (\<rho>\<^sub>2 @ [[X\<^sub>2]\<^sub>R]) = size (\<rho> @ [[X]\<^sub>R]) \<and> (\<rho>\<^sub>2 @ [[X\<^sub>2]\<^sub>R] @ z) \<in> P"
    using assms(2,3,4)
    cttWF_ctt_prefix_subset_exists_three_part_iff
    by (metis CTwf_def assms(5) length_append_singleton)
  then have "\<rho>\<^sub>2 @ [[X\<^sub>2]\<^sub>R] \<in> P"
    by (metis CT1c_prefix_concat_in append.assoc assms(4))
  then have "(\<forall>e. (\<rho>\<^sub>2 @ [[X\<^sub>2]\<^sub>R] \<in> P \<and> e \<notin> X\<^sub>2 \<and> e \<noteq> Tock) \<longrightarrow> \<rho>\<^sub>2 @ [[e]\<^sub>E] \<in> P)"
            "(\<forall>e. (\<rho>\<^sub>2 @ [[X\<^sub>2]\<^sub>R] \<in> P \<and> e \<notin> X\<^sub>2 \<and> e = Tock) \<longrightarrow> \<rho>\<^sub>2 @ [[X\<^sub>2]\<^sub>R,[e]\<^sub>E] \<in> P)"
    using assms by (auto simp add:CTM2a_def CTM2b_def)
  then have "\<forall>e. (\<rho>\<^sub>2 @ [[e]\<^sub>E] \<notin> P \<and> e \<noteq> Tock) \<longrightarrow> e \<in> X\<^sub>2"
    using assms \<open>\<rho>\<^sub>2 @ [[X\<^sub>2]\<^sub>R] \<in> P\<close> by blast
  then obtain Z where Z:"Z \<inter> {e. (e \<noteq> Tock \<and> \<rho>\<^sub>2 @ [[e]\<^sub>E] \<in> P) \<or> (e = Tock \<and> \<rho>\<^sub>2 @ [[X\<^sub>2]\<^sub>R, [e]\<^sub>E] \<in> P) } = {}"
    by blast
  then have "\<rho>\<^sub>2 @ [[X\<^sub>2 \<union> Z]\<^sub>R] \<in> P"
    using assms by (simp add: CT2_def \<open>\<rho>\<^sub>2 @ [[X\<^sub>2]\<^sub>R] \<in> P\<close>)
  then have "\<forall>e. \<rho> @ [[e]\<^sub>E] \<lesssim>\<^sub>C \<rho>\<^sub>2 @ [[e]\<^sub>E]"
    by (metis Suc_le_mono X2 antisym_conv ctt_prefix_subset_eq_length_common_prefix_eq ctt_prefix_subset_length ctt_prefix_subset_refl length_append_singleton)
  then have "\<forall>e. \<rho> @ [[X]\<^sub>R, [e]\<^sub>E] \<lesssim>\<^sub>C \<rho>\<^sub>2 @ [[X\<^sub>2]\<^sub>R, [e]\<^sub>E]"
    by (metis X2 ctt_prefix_subset.simps(2) ctt_prefix_subset_eq_length_common_prefix_eq length_append_singleton nat.simps(1))
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
    by (metis X2 ctt_prefix_subset.simps(2) ctt_prefix_subset_eq_length_common_prefix_eq ctt_prefix_subset_refl length_append_singleton nat.simps(1))
  then show ?thesis
    using \<open>\<rho>\<^sub>2 @ [[X\<^sub>2 \<union> Z]\<^sub>R] \<in> P\<close> by blast
qed

abbreviation "CT2sP \<rho> X P == {e. e \<noteq> Tock \<and> (\<exists>\<sigma>. \<rho> @ [[e]\<^sub>E] \<lesssim>\<^sub>C \<sigma> \<and> \<sigma> \<in> P) \<or> e = Tock \<and> (\<exists>\<sigma>. \<rho> @ [[X]\<^sub>R, [e]\<^sub>E] \<lesssim>\<^sub>C \<sigma> \<and> \<sigma> \<in> P)}"

lemma CT2s_mkCT1_part:
  assumes "Y \<inter> CT2sP \<rho> X P = {}"
          "\<rho> @ [[X]\<^sub>R] @ s \<lesssim>\<^sub>C \<sigma>" "\<sigma> \<in> P" "CT1c P" "CTM2a P" "CTM2b P" "CT2s P"
    shows "\<exists>\<sigma>. \<rho> @ [[X \<union> Y]\<^sub>R] @ s \<lesssim>\<^sub>C \<sigma> \<and> \<sigma> \<in> P"
proof -
  have "size (\<rho> @ [[X]\<^sub>R]) \<le> size \<sigma>"
    apply auto
    using assms ctt_prefix_subset_length by fastforce
  then obtain \<rho>\<^sub>2 X\<^sub>2 z where X2:"\<sigma> = \<rho>\<^sub>2 @ [[X\<^sub>2]\<^sub>R] @ z \<and> X \<subseteq> X\<^sub>2 \<and> \<rho> \<lesssim>\<^sub>C \<rho>\<^sub>2 \<and> size (\<rho>\<^sub>2 @ [[X\<^sub>2]\<^sub>R]) = size (\<rho> @ [[X]\<^sub>R]) \<and> (\<rho>\<^sub>2 @ [[X\<^sub>2]\<^sub>R] @ z) \<in> P"
    using assms(2,3,4)
    cttWF_ctt_prefix_subset_exists_three_part_concat
    by (metis length_append_singleton)
    (* by (metis CTwf_def assms(5) length_append_singleton) *)
  then have "\<rho>\<^sub>2 @ [[X\<^sub>2]\<^sub>R] @ z \<in> P"
      "\<rho>\<^sub>2 @ [[X\<^sub>2]\<^sub>R] \<in> P"
    by (metis CT1c_prefix_concat_in append.assoc assms(4))+
  then have "(\<forall>e. (\<rho>\<^sub>2 @ [[X\<^sub>2]\<^sub>R] \<in> P \<and> e \<notin> X\<^sub>2 \<and> e \<noteq> Tock) \<longrightarrow> \<rho>\<^sub>2 @ [[e]\<^sub>E] \<in> P)"
            "(\<forall>e. (\<rho>\<^sub>2 @ [[X\<^sub>2]\<^sub>R] \<in> P \<and> e \<notin> X\<^sub>2 \<and> e = Tock) \<longrightarrow> \<rho>\<^sub>2 @ [[X\<^sub>2]\<^sub>R,[e]\<^sub>E] \<in> P)"
    using assms by (auto simp add:CTM2a_def CTM2b_def)
  then have "\<forall>e. (\<rho>\<^sub>2 @ [[e]\<^sub>E] \<notin> P \<and> e \<noteq> Tock) \<longrightarrow> e \<in> X\<^sub>2"
    using assms \<open>\<rho>\<^sub>2 @ [[X\<^sub>2]\<^sub>R] \<in> P\<close> by blast
  then obtain Z where Z:"Z \<inter> {e. (e \<noteq> Tock \<and> \<rho>\<^sub>2 @ [[e]\<^sub>E] \<in> P) \<or> (e = Tock \<and> \<rho>\<^sub>2 @ [[X\<^sub>2]\<^sub>R, [e]\<^sub>E] \<in> P) } = {}"
    by blast
  then have "\<rho>\<^sub>2 @ [[X\<^sub>2 \<union> Z]\<^sub>R] @ z \<in> P"
    using assms CT2s_def
    by (simp add: CT2s_def Z X2)
  then have "\<forall>e. \<rho> @ [[e]\<^sub>E] @ z \<lesssim>\<^sub>C \<rho>\<^sub>2 @ [[e]\<^sub>E] @ z"
    by (metis Suc_le_mono X2 antisym_conv ctt_prefix_subset_eq_length_common_prefix_eq ctt_prefix_subset_length ctt_prefix_subset_refl length_append_singleton)
  then have "\<forall>e. \<rho> @ [[X]\<^sub>R, [e]\<^sub>E] @ z \<lesssim>\<^sub>C \<rho>\<^sub>2 @ [[X\<^sub>2]\<^sub>R, [e]\<^sub>E] @ z"
    by (metis X2 append_Cons ctt_prefix_subset.simps(2) ctt_prefix_subset_eq_length_common_prefix_eq length_append_singleton nat.simps(1))
  then have "{e. (e \<noteq> Tock \<and> \<rho>\<^sub>2 @ [[e]\<^sub>E] \<in> P) \<or> (e = Tock \<and> \<rho>\<^sub>2 @ [[X\<^sub>2]\<^sub>R, [e]\<^sub>E] \<in> P) }
             \<subseteq>
             {e. e \<noteq> Tock \<and> (\<exists>\<sigma>. \<rho> @ [[e]\<^sub>E] \<lesssim>\<^sub>C \<sigma> \<and> \<sigma> \<in> P) \<or> e = Tock \<and> (\<exists>\<sigma>. \<rho> @ [[X]\<^sub>R, [e]\<^sub>E] \<lesssim>\<^sub>C \<sigma> \<and> \<sigma> \<in> P)}
             "
    apply auto 
    apply (metis X2 ctt_prefix_subset_eq_length_common_prefix_eq ctt_prefix_subset_refl length_append_singleton nat.simps(1))
      apply (metis X2 ctt_prefix_subset_eq_length_common_prefix_eq ctt_prefix_subset_refl length_append_singleton nat.simps(1))
      apply (metis X2 \<open>\<forall>e. \<rho> @ [[X]\<^sub>R, [e]\<^sub>E] @ z \<lesssim>\<^sub>C \<rho>\<^sub>2 @ [[X\<^sub>2]\<^sub>R, [e]\<^sub>E] @ z\<close> ctt_prefix_subset_eq_length_common_prefix_eq length_Cons length_append_singleton nat.simps(1))
      by (metis X2 ctt_prefix_subset.simps(2) ctt_prefix_subset_eq_length_common_prefix_eq ctt_prefix_subset_refl length_append_singleton nat.simps(1))
  then have "X \<union> Y \<subseteq> X\<^sub>2 \<union> Z"
    using X2 apply safe
    apply blast (* FIXME: The next step deserves a better understanding. *)
    by (smt CollectI \<open>\<forall>e. \<rho>\<^sub>2 @ [[X\<^sub>2]\<^sub>R] \<in> P \<and> e \<notin> X\<^sub>2 \<and> e = Tock \<longrightarrow> \<rho>\<^sub>2 @ [[X\<^sub>2]\<^sub>R, [e]\<^sub>E] \<in> P\<close> \<open>\<forall>e. \<rho>\<^sub>2 @ [[X\<^sub>2]\<^sub>R] \<in> P \<and> e \<notin> X\<^sub>2 \<and> e \<noteq> Tock \<longrightarrow> \<rho>\<^sub>2 @ [[e]\<^sub>E] \<in> P\<close> \<open>\<rho>\<^sub>2 @ [[X\<^sub>2]\<^sub>R] \<in> P\<close> assms(1) disjoint_iff_not_equal subsetCE)
  then have "\<rho> @ [[X \<union> Y]\<^sub>R] @ s \<lesssim>\<^sub>C \<rho>\<^sub>2 @ [[X\<^sub>2 \<union> Z]\<^sub>R] @ s"
    by (metis X2 append_Cons ctt_prefix_subset.simps(2) ctt_prefix_subset_eq_length_common_prefix_eq ctt_prefix_subset_refl length_append_singleton nat.simps(1))
  then show ?thesis
  proof -
    have f1: "\<forall>cs c. [c::'a cttobs] @ cs = c # cs"
    by simp
      have "\<rho> @ [[X]\<^sub>R] @ s \<lesssim>\<^sub>C \<sigma>"
        using assms(2) by force
      then have "s \<lesssim>\<^sub>C z"
        by (metis (no_types) X2 append.assoc ctt_prefix_subset_eq_length_common_prefix_eq)
      then show ?thesis
        using f1 by (metis (no_types) X2 \<open>X \<union> Y \<subseteq> X\<^sub>2 \<union> Z\<close> \<open>\<rho>\<^sub>2 @ [[X\<^sub>2 \<union> Z]\<^sub>R] @ z \<in> P\<close> ctt_prefix_subset.simps(2) ctt_prefix_subset_eq_length_common_prefix_eq length_append_singleton nat.simps(1))
    qed
qed

lemma CT2_mkCT1:
  assumes "CT2 P" "CT1c P" "CTM2a P" "CTM2b P" "CTwf P"
  shows "CT2(mkCT1(P))"
proof -
  have "CT2(mkCT1(P)) = CT2({\<rho>|\<rho> \<sigma>. \<rho> \<lesssim>\<^sub>C \<sigma> \<and> \<sigma> \<in> P})"
    by (simp add:mkCT1_simp)
  also have "... = True"
    unfolding CT2_def apply auto
    using assms by (simp add: CT2_mkCT1_part)
  finally show ?thesis by auto
qed

lemma CT2s_mkCT1:
  assumes "CT2s P" "CT1c P" "CTM2a P" "CTM2b P"
  shows "CT2s(mkCT1(P))"
proof -
  have "CT2s(mkCT1(P)) = CT2s({\<rho>|\<rho> \<sigma>. \<rho> \<lesssim>\<^sub>C \<sigma> \<and> \<sigma> \<in> P})"
    by (simp add:mkCT1_simp)
  also have "... = True"
    using assms CT2s_mkCT1_part unfolding CT2s_def apply auto
    by (insert CT2s_mkCT1_part, blast)
  then show ?thesis using calculation by auto
qed

lemma ctt_prefix_of_CT3_trace:
  assumes "x \<lesssim>\<^sub>C \<sigma>" "CT3_trace \<sigma>"
  shows "CT3_trace x"
  using assms 
proof (induct x \<sigma> rule:ctt_prefix_subset.induct)
  case (1 x)
  then show ?case by auto
next
  case (2 X xa Y ya)
  then show ?case
    apply (induct xa ya rule:ctt_prefix_subset.induct, auto)
    by (case_tac y, auto)
next
  case (3 x xa y ya)
  then show ?case by (induct xa ya rule:ctt_prefix_subset.induct, auto)
next
  case ("4_1" v xa va ya)
  then show ?case by auto
next
  case ("4_2" va xa v ya)
  then show ?case by auto
next
  case (5 x xa)
  then show ?case by auto
qed

lemma CT3_mkCT1:
  assumes "CT3 P"
  shows "CT3(mkCT1(P))"
  using assms unfolding mkCT1_def CT3_def apply auto
  using ctt_prefix_of_CT3_trace by blast

lemma add_Tick_refusal_trace_ctt_prefix_subset_mono:
  assumes "\<rho> \<lesssim>\<^sub>C \<sigma>"
  shows   "add_Tick_refusal_trace \<rho> \<lesssim>\<^sub>C add_Tick_refusal_trace \<sigma>"
  using assms by(induct \<rho> \<sigma> rule:ctt_prefix_subset.induct, auto)

lemma CT4s_mkCT1:
  assumes "CT4s P"
  shows "CT4s(mkCT1(P))"
  using assms unfolding mkCT1_def CT4s_def apply auto
  using add_Tick_refusal_trace_ctt_prefix_subset_mono by blast

lemma
  "CTM2a(unCT1 P)"
  unfolding unCT1_def CTM2a_def by auto

lemma
  "(s \<in> (\<Union>{x. CTTick x \<and> (mkCT1 x) \<subseteq> P})) = (s \<in> Q)"
  apply safe
  oops

(* A wild guess below: *)

fun RprirelRef :: "('e cttevent) partialorder \<Rightarrow> ('e cttobs) list \<Rightarrow> ('e cttobs) list \<Rightarrow> ('e cttobs) list \<Rightarrow> ('e cttobs) list set \<Rightarrow> bool" where
"RprirelRef p [] [] s Q = True" |
"RprirelRef p [[R]\<^sub>R] [[S]\<^sub>R] s Q = (R \<subseteq> prirelref p S)" |
"RprirelRef p ([R]\<^sub>R # [Tock]\<^sub>E # aa) ([S]\<^sub>R # [Tock]\<^sub>E # zz) s Q = ((R \<subseteq> prirelref p S) \<and> Tock \<notin> R \<and> RprirelRef p aa zz (s @ [[S]\<^sub>R,[Tock]\<^sub>E]) Q)" |
"RprirelRef p ([e\<^sub>1]\<^sub>E # aa) ([e\<^sub>2]\<^sub>E # zz) s Q
 = 
 (e\<^sub>1 = e\<^sub>2 \<and> RprirelRef p aa zz (s @ [[e\<^sub>1]\<^sub>E]) Q \<and>
  (maximal(p,e\<^sub>2) 
   \<or> 
  (\<exists>Z. s @ [[Z]\<^sub>R] \<in> Q \<and> e\<^sub>2 \<notin> Z \<and> \<not>(\<exists>b. b \<notin> Z \<and> e\<^sub>2 <\<^sup>*p b))))" |
"RprirelRef p x y s Q = False"

definition mkCT4 :: "'e cttobs list set \<Rightarrow> 'e cttobs list set" where
"mkCT4 P = P \<union> {\<rho> @ [[R \<union> {Tick}]\<^sub>R]|\<rho> R. \<rho> @ [[R]\<^sub>R] \<in> P}"

lemma CT4_fixpoint_mkCT4:
  "(mkCT4 P = P) = CT4 P"
  unfolding mkCT4_def CT4_def by auto

lemma mkCT1_mkCT4_iff_CT14:
  "(mkCT1(mkCT4 P) = P) = (CT1 P \<and> CT4 P)"
  apply auto
  using CT1_def mkCT1_simp mkCT4_def apply fastforce
  apply (metis (mono_tags, lifting) CT1_def CT1_fixpoint_mkCT1 CT4_fixpoint_mkCT4 CollectI UnI1 mkCT1_simp mkCT4_def)  
    apply (metis CT1_fixpoint_mkCT1 CT4_fixpoint_mkCT4)
    by (metis CT1_fixpoint_mkCT1 CT4_fixpoint_mkCT4)

lemma CT1_mkCT1_simp:
  assumes "CT1 P"
  shows "(\<exists>x. s \<in> x \<and> (mkCT1 x) \<subseteq> P) = (s \<in> P)"
  using assms apply safe
  using mkCT1_def apply fastforce
  using CT1_fixpoint_mkCT1 by blast

fun mkCTTick_Trace :: "'e cttobs list \<Rightarrow> 'e cttobs list" where
"mkCTTick_Trace [] = []" |
"mkCTTick_Trace ([x]\<^sub>R # xs) = (if xs = [] then ([x \<union> {Tick}]\<^sub>R # xs) else ([x]\<^sub>R # mkCTTick_Trace xs))" |
"mkCTTick_Trace ([e]\<^sub>E # xs) = ([e]\<^sub>E # mkCTTick_Trace xs)"

lemma CTTick_dist_union:
  "CTTick (P \<union> Q) = (CTTick(P) \<and> CTTick(Q))"
  unfolding CTTick_def by auto

lemma CTTickAll_dist_union:
  "CTTickAll (P \<union> Q) = (CTTickAll(P) \<and> CTTickAll(Q))"
  unfolding CTTickAll_def by auto

lemma CTTick_mkCT1_simp:
  assumes "CT1 P" "CT4 P"
  shows "(\<exists>x. s \<in> x \<and> CTTickAll x \<and> (mkCT1 x) \<subseteq> P) = (s \<in> P \<and> CTTickAll {s})"
  using assms apply safe
  using mkCT1_def apply fastforce
  using CTTickAll_dist_union
  apply (metis insert_Diff insert_is_Un)
  apply (rule_tac x="{s}" in exI, auto)
  unfolding mkCT1_def apply auto
  using CT1_def by blast

fun CTMPick :: "'e cttobs list \<Rightarrow> 'e cttobs list \<Rightarrow> 'e cttobs list set \<Rightarrow> bool" where
"CTMPick [] s P = True" |
"CTMPick ([X]\<^sub>R # xs) s P = ((\<forall>e. e \<notin> X \<and> e \<noteq> Tock \<longrightarrow> s @ [[e]\<^sub>E] \<in> P)
                           \<and>
                           (Tock \<notin> X \<longrightarrow> s @ [[X]\<^sub>R,[Tock]\<^sub>E] \<in> P) \<and> Tick \<in> X \<and> CTMPick xs (s @ [[X]\<^sub>R]) P)" |
"CTMPick ([e]\<^sub>E # xs) s P = CTMPick xs (s @ [[e]\<^sub>E]) P"

lemma CTMPick_extend_event_imp:
  assumes "CTMPick xs s P"
  shows "CTMPick (xs @ [[e]\<^sub>E]) s P"
  using assms by (induct xs s P arbitrary:e rule:CTMPick.induct, auto)

lemma CTMPick_extend_ref_imp:
  assumes "CTMPick xs s P" "Tick \<in> X"
          "\<forall>e. (e \<noteq> Tock \<and> e \<notin> X) \<longrightarrow> s @ xs @ [[e]\<^sub>E] \<in> P"
          "(Tock \<notin> X) \<longrightarrow> s @ xs @ [[X]\<^sub>R,[Tock]\<^sub>E] \<in> P"
  shows "CTMPick (xs @ [[X]\<^sub>R]) s P"
  using assms by (induct xs s P arbitrary: X rule:CTMPick.induct, auto)

lemma CTM2a_CTM2b_CT1c_mkCT1_imp_CTMPick:
  assumes "s \<in> x" "CTM2a x" "CTM2b x" "CT1c x" "mkCT1 x \<subseteq> P" "CTTickAll x"
  shows "CTMPick s [] P"
  using assms proof(induct s arbitrary:x rule:rev_induct)
  case Nil
  then show ?case by auto
next
  case (snoc z zs)
  then have "CTMPick zs [] P"
    using assms CT1c_prefix_concat_in by blast
  then show ?case
  proof (cases z)
    case (ObsEvent x1)
    then show ?thesis using snoc CTMPick_extend_event_imp
      using \<open>CTMPick zs [] P\<close> by blast
  next
    case (Ref x2)
    then have "CTMPick zs [] P"
      using \<open>CTMPick zs [] P\<close> by blast
    
    have a:"Tick \<in> x2"
      using snoc Ref
      by (metis CTTickAll_def CTTickTrace.elims(2) CTTickTrace_dist_concat cttobs.distinct(1) cttobs.inject(2) list.inject not_Cons_self2)
    have b:"\<forall>e. e \<noteq> Tock \<and> e \<notin> x2 \<longrightarrow> zs @ [[e]\<^sub>E] \<in> P"  
      using CTM2a_def Ref mkCT1_def snoc.prems(1) snoc.prems(2) snoc.prems(5) by fastforce
    have c:"Tock \<notin> x2 \<longrightarrow> zs @ [[x2]\<^sub>R, [Tock]\<^sub>E] \<in> P"
      using CTM2b_def Ref mkCT1_def snoc.prems(1) snoc.prems(3) snoc.prems(5) by fastforce

    then have "CTMPick (zs @ [[x2]\<^sub>R]) [] P"
      using a b c snoc \<open>CTMPick zs [] P\<close>
      by (simp add: CTMPick_extend_ref_imp)
    then show ?thesis using Ref by auto
   qed
qed

definition mkCTM2a :: "'e cttobs list set \<Rightarrow> 'e cttobs list set" where
"mkCTM2a P = P \<union> {\<rho> @ [[e]\<^sub>E]|\<rho> X e. \<rho> @ [[X]\<^sub>R] \<in> P \<and> e \<notin> X \<and> e \<noteq> Tock}"

definition mkCTM2b :: "'e cttobs list set \<Rightarrow> 'e cttobs list set" where
"mkCTM2b P = P \<union> {\<rho> @ [[X]\<^sub>R,[Tock]\<^sub>E]|\<rho> X. \<rho> @ [[X]\<^sub>R] \<in> P \<and> Tock \<notin> X}"

lemma CTM2a_mkCTM2a [simp]: "CTM2a (mkCTM2a P)"
  unfolding mkCTM2a_def CTM2a_def by auto

lemma CTM2b_mkCTM2b [simp]: "CTM2b (mkCTM2b P)"
  unfolding mkCTM2b_def CTM2b_def by auto

lemma mkCTM2b_mkCTM2a_commute: "mkCTM2b (mkCTM2a P) = mkCTM2a (mkCTM2b P)"
  unfolding mkCTM2b_def mkCTM2a_def by auto

definition mkCT1c :: "'e cttobs list set \<Rightarrow> 'e cttobs list set" where
"mkCT1c P = P \<union> {\<rho>|\<rho> \<sigma>. \<rho> \<le>\<^sub>C \<sigma> \<and> \<sigma> \<in> P}"

lemma CT1c_fixpoint_mkCT1c:
  "CT1c P = (P = mkCT1c(P))"
  unfolding CT1c_def mkCT1c_def by auto

lemma CTMPick_imp_in_mkCTM2b_mkCTM2a:
  assumes "CTMPick s [] P" 
  shows "s \<in> mkCTM2b (mkCTM2a {s})"
  using assms unfolding mkCTM2b_def mkCTM2a_def by auto

lemma CTMPick_imp_in_prefix_mkCTM2b_mkCTM2a:
  assumes "CTMPick s [] P" 
  shows "s \<in> mkCTM2b (mkCTM2a {x. x \<le>\<^sub>C s})"
  using assms unfolding mkCTM2b_def mkCTM2a_def apply auto
  by (simp add: ctt_prefix_refl)

lemma CTMPick_imp_in_prefix_mkCTM2b_mkCTM2a_CT1c:
  assumes "CTMPick s [] P" 
  shows "s \<in> mkCTM2b (mkCTM2a (mkCT1c{s}))"
  using assms unfolding mkCTM2b_def mkCTM2a_def mkCT1c_def by auto

lemma CTTick_imp_CTTick_mkCTM2a_mkCTM2b:
  assumes "CTTick {s}"
  shows "CTTick (mkCTM2a (mkCTM2b {s}))"
  using assms unfolding mkCTM2b_def mkCTM2a_def CTTick_def by auto

lemma CTTickTrace_prefix:
  assumes "CTTickTrace s" "t \<le>\<^sub>C s" 
  shows "CTTickTrace t"
  using assms apply (induct t s rule:ctt_prefix.induct, auto)
  by (case_tac y, auto)

lemma CTTickAll_singleton_imp_prefixes:
  assumes "CTTickAll {s}"
  shows "CTTickAll {x. x \<le>\<^sub>C s}"
  using assms unfolding CTTickAll_def apply auto
  using CTTickTrace_prefix by blast

lemma CTTickAll_singleton_mkCTM2a:
  assumes "CTTickAll {s}"
  shows "CTTickAll(mkCTM2a {x. x \<le>\<^sub>C s})"
  using assms unfolding mkCTM2a_def CTTickAll_def apply auto
  using CTTickTrace_prefix apply blast
  by (metis CTTickTrace.simps(1) CTTickTrace.simps(2) CTTickTrace_dist_concat CTTickTrace_prefix)

lemma CTTickAll_singleton_mkCTM2b:
  assumes "CTTickAll {s}"
  shows "CTTickAll(mkCTM2b {x. x \<le>\<^sub>C s})"
  using assms unfolding mkCTM2b_def CTTickAll_def apply auto
  using CTTickTrace_prefix apply blast
  by (metis CTTickTrace.simps(2) CTTickTrace.simps(3) CTTickTrace_dist_concat CTTickTrace_prefix)

lemma CTTickAll_imp_CTTickAll_mkCTM2a_mkCTM2b:
  assumes "CTTickAll {s}"
  shows "CTTickAll (mkCTM2a (mkCTM2b {x. x \<le>\<^sub>C s}))"
  using assms unfolding mkCTM2a_def mkCTM2b_def CTTickAll_def apply auto
  using CTTickTrace_prefix apply blast
  apply (metis CTTickTrace.simps(2) CTTickTrace.simps(3) CTTickTrace_dist_concat CTTickTrace_prefix)
  by (metis CTTickTrace.simps(1) CTTickTrace.simps(2) CTTickTrace_dist_concat CTTickTrace_prefix)

lemma CTTickAll_imp_CTTickAll_mkCTM2a_mkCTM2b_mkCT1c:
  assumes "CTTickAll {s}"
  shows "CTTickAll (mkCTM2a (mkCTM2b (mkCT1c{s})))"
  using assms unfolding mkCTM2a_def mkCTM2b_def mkCT1c_def CTTickAll_def apply auto
  using CTTickTrace_prefix apply blast
     apply (metis CTTickTrace.simps(2) CTTickTrace.simps(3) CTTickTrace_dist_concat)
  apply (metis CTTickTrace.simps(2) CTTickTrace.simps(3) CTTickTrace_dist_concat CTTickTrace_prefix)
  apply (metis CTTickTrace.simps(1) CTTickTrace.simps(2) CTTickTrace_dist_concat)
  by (metis CTTickTrace.simps(2) CTTickTrace.simps(3) CTTickTrace_dist_concat CTTickTrace_prefix)
  
lemma CT1c_mkCTM2a:
  assumes "CT1c P"
  shows "CT1c (mkCTM2a P)"
  using assms unfolding mkCTM2a_def CT1c_def apply auto
  by (meson ctt_prefix_concat ctt_prefix_notfront_is_whole)


lemma mkCTM2b_dist_union:
  "mkCTM2b(P \<union> Q) = (mkCTM2b(P) \<union> mkCTM2b(Q))"
  unfolding mkCTM2b_def by auto

lemma mkCTM2b_in_mkCT1c_for_CT1c:
  assumes "CT1c P"
  shows "mkCTM2b({\<rho>|\<rho> \<sigma>. \<rho> \<le>\<^sub>C \<sigma> \<and> \<sigma> \<in> P}) = ({\<rho>|\<rho> \<sigma>. \<rho> \<le>\<^sub>C \<sigma> \<and> \<sigma> \<in> mkCTM2b(P)})"
  unfolding mkCTM2b_def apply auto
  apply (rule_tac x="\<rho> @ [[X]\<^sub>R, [Tock]\<^sub>E]" in exI, auto)
  apply (simp add: ctt_prefix_refl)
  using CT1c_def assms apply blast
  by (smt CT1c_prefix_concat_in Nil_is_append_conv append_Cons append_Nil2 append_eq_append_conv2 append_self_conv2 assms cttWF.simps(1) ctt_prefix_append_split ctt_prefix_notfront_is_whole ctt_prefix_refl ctt_prefix_same_front same_append_eq split_tocks)

lemma mkCTM2b_mkCT1c_commute:
  assumes "CT1c P"
  shows "mkCTM2b(mkCT1c(P)) = mkCT1c(mkCTM2b(P))"
proof -
  have "mkCTM2b(mkCT1c(P)) = mkCTM2b(P \<union> {\<rho>|\<rho> \<sigma>. \<rho> \<le>\<^sub>C \<sigma> \<and> \<sigma> \<in> P})"
    unfolding mkCT1c_def by auto
  also have "... = mkCTM2b(P) \<union> mkCTM2b({\<rho>|\<rho> \<sigma>. \<rho> \<le>\<^sub>C \<sigma> \<and> \<sigma> \<in> P})"
    using mkCTM2b_dist_union by auto
  also have "... = mkCTM2b(P) \<union> {\<rho>|\<rho> \<sigma>. \<rho> \<le>\<^sub>C \<sigma> \<and> \<sigma> \<in> mkCTM2b(P)}"
    using assms mkCTM2b_in_mkCT1c_for_CT1c by blast
  also have "... = mkCT1c(mkCTM2b(P))"
    unfolding mkCT1c_def by auto
  finally show ?thesis .
qed

lemma CT1c_mkCTM2b:
  assumes "CT1c P"
  shows "CT1c (mkCTM2b P)"
proof -
  have "CT1c P = (P = mkCT1c(P))"
    using CT1c_fixpoint_mkCT1c by blast
  then have "CT1c (mkCTM2b P) = CT1c (mkCTM2b(mkCT1c(P)))"
    using assms by auto
  also have "... = CT1c(mkCT1c(mkCTM2b(P)))"
    using assms by (simp add: mkCTM2b_mkCT1c_commute)
  also have "... = True"
    by (metis CT1c_fixpoint_mkCT1c assms mkCTM2b_mkCT1c_commute)
  then show ?thesis using calculation by auto
qed

lemma CT1c_mkCT1c [simp]: "CT1c (mkCT1c P)"
  unfolding mkCT1c_def CT1c_def apply auto
  using ctt_prefix_trans by blast

lemma CT1c_mkCTM2a_mkCTM2b_mkCT1c:
  "CT1c (mkCTM2a (mkCTM2b (mkCT1c P)))"
proof -
  have "CT1c (mkCTM2b (mkCT1c P))"
    using CT1c_mkCTM2b CT1c_mkCT1c by blast
  then have "CT1c (mkCTM2a (mkCTM2b (mkCT1c P)))"
    using CT1c_mkCTM2a by blast
  then show ?thesis .
qed

lemma CTMPick_imp_RefTock_in:
  assumes "CTMPick (\<rho> @ [[X]\<^sub>R] @ x) s P" "Tock \<notin> X"
  shows "s @ \<rho> @ [[X]\<^sub>R, [Tock]\<^sub>E] \<in> P"
  using assms by (induct \<rho> s P rule:CTMPick.induct, auto)

lemma CTMPick_imp_Event_in:
  assumes "CTMPick (\<rho> @ [[X]\<^sub>R] @ x) s P" "e \<notin> X" "e \<noteq> Tock"
  shows "s @ \<rho> @ [[e]\<^sub>E] \<in> P"
  using assms by (induct \<rho> s P rule:CTMPick.induct, auto)

lemma
  assumes "CTMPick s z P" "x \<lesssim>\<^sub>C \<sigma>" "\<sigma> \<le>\<^sub>C s"
  shows "x \<in> P"
  using assms apply (induct s z P rule:CTMPick.induct, auto)
  oops
(*
lemma
  assumes "b \<noteq> []"
  shows "x \<le>\<^sub>C \<rho> @ b \<Longrightarrow> \<not> x \<le>\<^sub>C \<rho> \<Longrightarrow> x = \<rho> @ b"
  using assms apply (induct x \<rho> arbitrary:b rule:ctt_prefix.induct, auto)
    apply (case_tac x, auto, case_tac y, auto)
  apply (case_tac y, auto)
    apply (metis append.right_neutral ctt_prefix_subset_front ctt_prefix_subset_same_front)
   apply (case_tac y, auto)
    apply (metis ctt_prefix_subset.simps(3) ctt_prefix_subset.simps(5) cttobs.exhaust)
   apply (case_tac x, auto)
  apply (case_tac x, auto)
*)

(*
lemma
  assumes "CT1 P" "\<rho> @ [[X]\<^sub>R] \<in> P" "x \<lesssim>\<^sub>C \<rho> @ [[X]\<^sub>R, [Tock]\<^sub>E]" "Tock \<notin> X" "\<rho> @ [[X]\<^sub>R] \<le>\<^sub>C s"
  shows "x \<in> P"
proof -
  have "\<forall>x. x \<lesssim>\<^sub>C \<rho> @ [[X]\<^sub>R] \<longrightarrow> x \<in> P"
    using assms CT1_def by blast
  have "x \<lesssim>\<^sub>C \<rho> @ [[X]\<^sub>R, [Tock]\<^sub>E] = (x \<lesssim>\<^sub>C \<rho> @ [[X]\<^sub>R] \<or> (\<not> x \<lesssim>\<^sub>C \<rho> @ [[X]\<^sub>R] \<and> x = \<rho> @ [[X]\<^sub>R, [Tock]\<^sub>E]))"
    apply auto
    sledgehammer
  using assms apply (induct x arbitrary:X \<rho> s rule:rev_induct, auto)
  
*)

(* FIXME: Ugly proof *)
lemma CTTickAll_mkCT1_simp:
  assumes "CT1 P" "CT4 P"
  shows "(\<exists>x. s \<in> x \<and> CTM2a x \<and> CTM2b x \<and> CTTickAll x \<and> CT1c x \<and> (mkCT1 x) \<subseteq> P) 
         = 
         (s \<in> P \<and> CTTickAll {s} \<and> CTMPick s [] P)"
  using assms apply safe
  using mkCT1_def apply fastforce
  using CTTickAll_dist_union 
    apply (metis insert_Diff insert_is_Un)
  using CTM2a_CTM2b_CT1c_mkCT1_imp_CTMPick apply blast
  (* Need to define mkCTM2a mkCTM2b and mkCT1c then can prove the following goal. *)
  apply (rule_tac x="mkCTM2b(mkCTM2a(mkCT1c{s}))" in exI) 
  apply auto
      apply (simp add:CTMPick_imp_in_prefix_mkCTM2b_mkCTM2a_CT1c)
     apply (auto simp add:mkCTM2b_mkCTM2a_commute CTTickAll_imp_CTTickAll_mkCTM2a_mkCTM2b_mkCT1c)
  using CT1c_mkCTM2a_mkCTM2b_mkCT1c apply blast
  using CT1c_mkCTM2b CT1c_mkCTM2a assms 
  unfolding mkCTM2a_def mkCTM2b_def mkCT1_def apply auto
  unfolding mkCT1c_def apply auto 
  using CT1_def ctt_prefix_imp_prefix_subset apply blast
  using CTMPick_imp_RefTock_in apply fastforce
  using CTMPick_imp_RefTock_in append_assoc ctt_prefix_split apply fastforce
  using CTMPick_imp_Event_in apply fastforce
  using CTMPick_imp_Event_in append_assoc ctt_prefix_split apply fastforce

  using CT1_def apply blast
      apply (smt CT1_CT1c CT1_def CT1c_prefix_concat_in ctt_prefix_split)
  apply (case_tac "x \<lesssim>\<^sub>C \<rho> @ [[X]\<^sub>R]")
  using CT1_def apply blast
     apply (case_tac "x = \<rho> @ [[X]\<^sub>R, [Tock]\<^sub>E]", auto)
  using CTMPick_imp_RefTock_in apply fastforce
  apply (smt CT1_def CTMPick_extend_event_imp CTMPick_imp_RefTock_in append.left_neutral append_assoc assms(1))
    
    apply (smt CT1_def CTMPick_imp_RefTock_in append_Nil append_assoc ctt_prefix_split)
    
     apply (case_tac "x \<lesssim>\<^sub>C \<rho>")
  apply (smt CT1_CT1c CT1_def CT1c_prefix_concat_in)
   apply (case_tac "x = \<rho> @ [[e]\<^sub>E]", auto)
 
  using CTMPick_imp_Event_in Cons_eq_appendI append.assoc self_append_conv2 apply fastforce
proof -
  fix x :: "'a cttobs list" and \<rho> :: "'a cttobs list" and X :: "'a cttevent set" and e :: "'a cttevent"
  assume a1: "CTMPick (\<rho> @ [[X]\<^sub>R]) [] P"
  assume a2: "x \<lesssim>\<^sub>C \<rho> @ [[e]\<^sub>E]"
  assume a3: "e \<notin> X"
  assume a4: "e \<noteq> Tock"
  assume "s = \<rho> @ [[X]\<^sub>R]"
  have "\<rho> @ [[e]\<^sub>E] \<in> P"
    using a4 a3 a1 by (metis (no_types) CTMPick_imp_Event_in append_Cons append_Nil)
  then show "x \<in> P"
    using a2 CT1_fixpoint_mkCT1 assms(1) mkCT1_def by fastforce
next  
  fix x :: "'a cttobs list" and \<rho> :: "'a cttobs list" and X :: "'a cttevent set" and e :: "'a cttevent"
  assume 
      a0: "CT1 P"
  and a1: "CTMPick s [] P"
  and a2: "x \<lesssim>\<^sub>C \<rho> @ [[e]\<^sub>E]"
  and a3: "e \<notin> X"
  and a4: "e \<noteq> Tock"
  and a5:"\<rho> @ [[X]\<^sub>R] \<le>\<^sub>C s"
  then show "x \<in> P"
    apply (case_tac "x \<lesssim>\<^sub>C \<rho>")
    apply (smt CT1_def CTMPick_imp_Event_in a1 a2 a3 a4 append_assoc append_self_conv2 assms(1) ctt_prefix_decompose)
    apply (case_tac "x = \<rho> @ [[e]\<^sub>E]", auto)  
    using CTMPick_imp_Event_in ctt_prefix_split apply fastforce
  by (smt CT1_def CTMPick_imp_Event_in append_Nil append_assoc ctt_prefix_decompose)
qed

lemma CT14_CTTick_mkCT1_exists:
  assumes "CT1 P" "CT4 P"
  shows "(s @ [[Z]\<^sub>R] \<in> unCT1 P \<and> e\<^sub>2 \<notin> Z \<and> \<not>(\<exists>b. b \<notin> Z \<and> e\<^sub>2 <\<^sup>*p b))
         =
         (s @ [[Z]\<^sub>R] \<in> P \<and> CTTickAll {s @ [[Z]\<^sub>R]} \<and> CTMPick (s @ [[Z]\<^sub>R]) [] P \<and> e\<^sub>2 \<notin> Z \<and> \<not>(\<exists>b. b \<notin> Z \<and> e\<^sub>2 <\<^sup>*p b))"
proof -
  have "(s @ [[Z]\<^sub>R] \<in> unCT1 P \<and> e\<^sub>2 \<notin> Z \<and> \<not>(\<exists>b. b \<notin> Z \<and> e\<^sub>2 <\<^sup>*p b))
        =
        (s @ [[Z]\<^sub>R] \<in> (\<Union>{x. CTM2a x \<and> CTM2b x \<and> CTTickAll x \<and> CT1c x \<and> (mkCT1 x) \<subseteq> P}) \<and> e\<^sub>2 \<notin> Z \<and> \<not>(\<exists>b. b \<notin> Z \<and> e\<^sub>2 <\<^sup>*p b))"
    unfolding unCT1_def by auto
  also have "...
        =
        (\<exists>x. s @ [[Z]\<^sub>R] \<in> x \<and> CTM2a x \<and> CTM2b x \<and> CTTickAll x \<and> CT1c x \<and> (mkCT1 x) \<subseteq> P \<and> e\<^sub>2 \<notin> Z \<and> \<not>(\<exists>b. b \<notin> Z \<and> e\<^sub>2 <\<^sup>*p b))"
    by auto
  also have "... =
       (s @ [[Z]\<^sub>R] \<in> P \<and> CTTickAll {s @ [[Z]\<^sub>R]} \<and> CTMPick (s @ [[Z]\<^sub>R]) [] P \<and> e\<^sub>2 \<notin> Z \<and> \<not>(\<exists>b. b \<notin> Z \<and> e\<^sub>2 <\<^sup>*p b))"
    using assms CTTickAll_mkCT1_simp by auto
  (*also have "... =
       (\<exists>Z. s @ [[Z]\<^sub>R] \<in> P \<and> Tick \<in> Z \<and> e\<^sub>2 \<notin> Z \<and> \<not>(\<exists>b. b \<notin> Z \<and> e\<^sub>2 <\<^sup>*p b))"
    using assms
    using CTTickAll_def by blast*)
  (*also have "... =
       (\<exists>Z. s @ [[Z]\<^sub>R] \<in> P \<and> e\<^sub>2 \<notin> Z \<and> \<not>(\<exists>b. b \<notin> Z \<and> e\<^sub>2 <\<^sup>*p b))"
    apply auto 
    apply (rule_tac x="Z \<union> {Tick}" in exI, auto)
    using assms 
    using CT4_fixpoint_mkCT4 mkCT4_def apply fastforce*)
  finally show ?thesis .
qed

lemma
  "(\<exists>t. \<rho> \<lesssim>\<^sub>C t \<and> prirelRef p t s [] (unCT1 P) \<and> s \<in> P \<and> CTTick {s}) = (\<exists>t. \<rho> \<lesssim>\<^sub>C t \<and> RprirelRef p t s [] P \<and> s \<in> P \<and> CTTick {s})"
  nitpick
  oops

definition prirelrefSub :: "('e cttevent) partialorder \<Rightarrow> ('e cttevent) set \<Rightarrow> ('e cttobs) list \<Rightarrow> ('e cttobs) list set \<Rightarrow> ('e cttevent) set" where
"prirelrefSub pa S sa Q = 
  {z. ((z = Tock \<and> sa @ [[S]\<^sub>R, [Tock]\<^sub>E] \<in> Q) \<longrightarrow> (\<exists>b. b \<notin> S \<and> sa @ [[b]\<^sub>E] \<in> Q \<and> b \<noteq> Tock \<and> b \<noteq> Tick \<and> z <\<^sup>*pa b))
        \<and>
       ((z \<notin> S \<and> sa @ [[z]\<^sub>E] \<in> Q \<and> z \<noteq> Tock \<and> z \<noteq> Tick) \<longrightarrow>
          ((sa @ [[S]\<^sub>R, [Tock]\<^sub>E] \<in> Q \<and> z <\<^sup>*pa Tock)
            \<or>
           (\<exists>b. b \<notin> S \<and> sa @ [[b]\<^sub>E] \<in> Q \<and> b \<noteq> Tock \<and> b \<noteq> Tick \<and> z <\<^sup>*pa b)))}"

fun prirelRef2 :: "('e cttevent) partialorder \<Rightarrow> ('e cttobs) list \<Rightarrow> ('e cttobs) list \<Rightarrow> ('e cttobs) list \<Rightarrow> ('e cttobs) list set \<Rightarrow> bool" where
"prirelRef2 p [] [] s Q = True" |
"prirelRef2 p [[R]\<^sub>R] [[S]\<^sub>R] s Q = (R \<subseteq> prirelrefSub p S s Q)" |
"prirelRef2 p ([R]\<^sub>R # [Tock]\<^sub>E # aa) ([S]\<^sub>R # [Tock]\<^sub>E # zz) s Q =
   ((R \<subseteq> prirelrefSub p S s Q) \<and> Tock \<notin> prirelrefSub p S s Q \<and> prirelRef2 p aa zz (s @ [[S]\<^sub>R,[Tock]\<^sub>E]) Q)" |
"prirelRef2 p ([e\<^sub>1]\<^sub>E # aa) ([e\<^sub>2]\<^sub>E # zz) s Q
 = 
 (e\<^sub>1 = e\<^sub>2 \<and> prirelRef2 p aa zz (s @ [[e\<^sub>1]\<^sub>E]) Q \<and>
  (maximal(p,e\<^sub>2) 
   \<or> 
  (\<exists>Z. s @ [[Z]\<^sub>R] \<in> Q
      \<and> (\<forall>e. (e \<notin> Z \<and> e \<noteq> Tock) \<longrightarrow> s @ [[e]\<^sub>E] \<in> Q)
      \<and> (Tock \<notin> Z \<longrightarrow> s @ [[Z]\<^sub>R,[Tock]\<^sub>E] \<in> Q) \<and> Tick \<in> Z
      \<and> e\<^sub>2 \<notin> Z \<and> \<not>(\<exists>b. b \<notin> Z \<and> e\<^sub>2 <\<^sup>*p b))))" |
"prirelRef2 p x y s Q = False"





lemma CTwf_no_ill_Tock [simp]:
  assumes "CTwf P" "e \<noteq> Tock"
  shows "sa @ [[X]\<^sub>R, [e]\<^sub>E] \<notin> P"
  using assms unfolding CTwf_def apply (induct sa rule:cttWF.induct, auto)
    apply (cases e, auto)
  apply (metis assms(2) cttWF.simps(11) cttWF.simps(12) cttWF.simps(4) cttWF_dist_cons_refusal cttevent.exhaust cttobs.inject(1) cttobs.inject(2) list.inject)
  by (metis append.left_neutral append_Cons cttWF.simps(11) cttWF.simps(12) cttWF_dist_cons_refusal' cttevent.exhaust)

(* Problem below is from 's' how to achieve target 's'? Need a way to construct it
   explicitly, then just need to show that x \<lesssim>\<^sub>C t. *)
fun mkCTMP :: "'e cttobs list \<Rightarrow> 'e cttobs list \<Rightarrow> 'e cttobs list set \<Rightarrow> 'e cttobs list" where
"mkCTMP [] s P = []" |
"mkCTMP ([X]\<^sub>R # xs) s P =
        ([X \<union> {e. (e \<noteq> Tock \<and> s @ [[e]\<^sub>E] \<notin> P) \<or> (e = Tock \<and> s @ [[X]\<^sub>R,[Tock]\<^sub>E] \<notin> P)} \<union> {Tick}]\<^sub>R # 
         (mkCTMP xs (s @ [[X]\<^sub>R]) P))" |
"mkCTMP ([e]\<^sub>E # xs) s P = ([e]\<^sub>E # (mkCTMP xs (s @ [[e]\<^sub>E]) P))"


lemma CT4s_CT1_imp_Ref_Tock:
  assumes "s @ [[X]\<^sub>R, [Tock]\<^sub>E] \<in> P" "CT1 P" "CT4s P"
  shows "s @ [[X \<union> {Tick}]\<^sub>R,[Tock]\<^sub>E] \<in> P"
  using assms unfolding CT1_def CT4s_def
proof (auto)
  fix \<rho> X s
  assume CT1_P: "\<forall>\<rho>. (\<exists>\<sigma>. \<rho> \<lesssim>\<^sub>C \<sigma> \<and> \<sigma> \<in> P) \<longrightarrow> \<rho> \<in> P"
  assume "s @ [[X]\<^sub>R, [Tock]\<^sub>E] \<in> P" "\<forall>\<rho>. \<rho> \<in> P \<longrightarrow> add_Tick_refusal_trace \<rho> \<in> P"
  then have "add_Tick_refusal_trace (s @ [[X]\<^sub>R, [Tock]\<^sub>E]) \<in> P"
    by auto
  then have "add_Tick_refusal_trace s @ add_Tick_refusal_trace ([[X]\<^sub>R, [Tock]\<^sub>E]) \<in> P"
    by (simp add: add_Tick_refusal_trace_concat)
  then have "add_Tick_refusal_trace s @ [[X \<union> {Tick}]\<^sub>R,[Tock]\<^sub>E] \<in> P"
    by auto
  also have "s @ [[X \<union> {Tick}]\<^sub>R,[Tock]\<^sub>E] \<subseteq>\<^sub>C add_Tick_refusal_trace s @ [[X \<union> {Tick}]\<^sub>R,[Tock]\<^sub>E]"
    by (simp add: add_Tick_refusal_trace_ctt_subset ctt_subset_combine)
  then show "s @ [[insert Tick X]\<^sub>R, [Tock]\<^sub>E] \<in> P"
    using CT1_P calculation ctt_subset_imp_prefix_subset by auto
qed

lemma CT2s_Ref_Tock_augment:
  assumes "s @ [[X]\<^sub>R, [Tock]\<^sub>E] \<in> P" "CT2s P" "CT1 P" "CT4s P"
  shows "s @ [[X \<union> {e. e \<noteq> Tock \<and> s @ [[e]\<^sub>E] \<notin> P} \<union> {Tick}]\<^sub>R, [Tock]\<^sub>E] \<in> P"
proof -
  have "{e. e \<noteq> Tock \<and> s @ [[e]\<^sub>E] \<notin> P} \<inter> {e. (e \<noteq> Tock \<and> s @ [[e]\<^sub>E] \<in> P) \<or> (e = Tock \<and> s @ [[X]\<^sub>R, [e]\<^sub>E] \<in> P) } = {}"
    by auto
  then have "s @ [[X \<union> {e. e \<noteq> Tock \<and> s @ [[e]\<^sub>E] \<notin> P}]\<^sub>R] @ [[Tock]\<^sub>E] \<in> P"
    using assms by (simp add: CT2s_def) 
  then have "s @ [[X \<union> {e. e \<noteq> Tock \<and> s @ [[e]\<^sub>E] \<notin> P} \<union> {Tick}]\<^sub>R] @ [[Tock]\<^sub>E] \<in> P"
    using CT4s_CT1_imp_Ref_Tock assms
    by auto
  then show ?thesis by auto
qed


(*
lemma
  assumes "CTMPick xs (s @ [[X]\<^sub>R]) P" "CTwf P" "cttWF (xs)" "cttWF (s @ [[X]\<^sub>R])"
  shows "CTMPick xs (s @ [[X \<union> {e. e \<noteq> Tock \<and> s @ [[e]\<^sub>E] \<notin> P \<or> e = Tock \<and> s @ [[X]\<^sub>R, [Tock]\<^sub>E] \<notin> P}]\<^sub>R]) P"
  using assms nitpick 
  apply (induct xs arbitrary:X s, auto)
  apply (case_tac a, auto)
*)
  (*apply (induct xs _ P arbitrary:X s rule:CTMPick.induct, auto)
  sledgehammer
*)
(*
lemma
  assumes "CTMPick z (s @ [[X]\<^sub>R]) P" "cttWF (s @ [[X]\<^sub>R] @ z)"
  shows "CTMPick z (s @ [[insert Tick (X \<union> {e. e \<noteq> Tock \<and> s @ [[e]\<^sub>E] \<notin> P \<or> e = Tock \<and> s @ [[X]\<^sub>R, [Tock]\<^sub>E] \<notin> P})]\<^sub>R]) P"
  using assms apply(induct z _ P arbitrary:X s rule:CTMPick.induct)
    apply auto[1]*)
 (* apply (metis (no_types) append_Cons append_Nil cttWF.simps(13) cttWF_dist_cons_refusal')
*)

(*
lemma
  assumes "CTMPick zs (s @ [[X]\<^sub>R,[Tock]\<^sub>E]) P" "cttWF (s @ [[X]\<^sub>R,[Tock]\<^sub>E] @ zs)"
  shows "CTMPick zs (s @ [[insert Tick (X \<union> {e. e \<noteq> Tock \<and> s @ [[e]\<^sub>E] \<notin> P \<or> e = Tock \<and> s @ [[X]\<^sub>R, [Tock]\<^sub>E] \<notin> P})]\<^sub>R,[Tock]\<^sub>E]) P"
  using assms apply(induct zs s P arbitrary:X rule:CTMPick.induct, auto)
*)

lemma CTMPick_imp_prefix:
  assumes "CTMPick (xs @ [x]) zs P"
  shows "CTMPick xs zs P"
  using assms by (induct xs zs P rule:CTMPick.induct, auto)

lemma CTMPick_imp_prefix':
  assumes "CTMPick (xs @ ys) zs P"
  shows "CTMPick xs zs P"
  using assms by (induct xs zs P rule:CTMPick.induct, auto)

lemma CTMPick_imp_prefix'':
  assumes "CTMPick (xs @ ys) zs P"
  shows "CTMPick ys (zs @ xs) P"
  using assms by (induct xs zs P rule:CTMPick.induct, auto)

lemma CT2s_extends_Ref:
  assumes "CT2s P" "s @ [[X]\<^sub>R] @ xs \<in> P"
  shows "s @ [[X \<union> {e. e \<noteq> Tock \<and> s @ [[e]\<^sub>E] \<notin> P \<or> e = Tock \<and> s @ [[X]\<^sub>R, [Tock]\<^sub>E] \<notin> P}]\<^sub>R] @ xs \<in> P"
proof -
  obtain Y where Y:"Y = {e. e \<noteq> Tock \<and> s @ [[e]\<^sub>E] \<notin> P \<or> e = Tock \<and> s @ [[X]\<^sub>R, [Tock]\<^sub>E] \<notin> P}"
    by auto
  then have "Y \<inter> {e. (e \<noteq> Tock \<and> s @ [[e]\<^sub>E] \<in> P) \<or> (e = Tock \<and> s @ [[X]\<^sub>R, [e]\<^sub>E] \<in> P) } = {}"
    by auto
  then have "s @ [[X \<union> Y]\<^sub>R] @ xs \<in> P"
    using assms unfolding CT2s_def by auto
  then show ?thesis using Y by auto
qed

lemma ctt_prefix_common_concat:
  assumes "zs \<lesssim>\<^sub>C ys"
  shows "xs @ zs \<lesssim>\<^sub>C xs @ ys"
  using assms apply (induct zs ys arbitrary:xs rule:ctt_prefix_subset.induct, auto)
  using ctt_prefix_concat ctt_prefix_imp_prefix_subset apply blast
  apply (meson ctt_prefix_subset.simps(2) ctt_prefix_subset_same_front)
  by (meson ctt_prefix_subset.simps(3) ctt_prefix_subset_same_front)

lemma ctt_prefix_common_concat_eq_size:
  assumes "zs \<lesssim>\<^sub>C ys" "size zs = size ys"
  shows "zs @ xs \<lesssim>\<^sub>C ys @ xs"
  using assms apply (induct zs ys arbitrary:xs rule:ctt_prefix_subset.induct, auto)
  by (simp add: ctt_prefix_subset_refl)

lemma CT4s_middle_Ref_with_Tick:
  assumes "s @ [[X]\<^sub>R] @ xs \<in> P" "CT1 P" "CT4s P"
  shows "s @ [[X \<union> {Tick}]\<^sub>R] @ xs \<in> P"
proof -
  have add_Tick_in_P:"add_Tick_refusal_trace (s @ [[X]\<^sub>R] @ xs) \<in> P"
    using assms unfolding CT4s_def by blast

  have add_Tick_dist:"add_Tick_refusal_trace (s @ [[X]\<^sub>R] @ xs) =
     add_Tick_refusal_trace s @ [[X \<union> {Tick}]\<^sub>R] @ add_Tick_refusal_trace(xs)"
    by (simp add: add_Tick_refusal_trace_concat add_Tick_refusal_trace_end_refusal)
  
  have s_le_addTick:"s \<lesssim>\<^sub>C add_Tick_refusal_trace s"
    by (simp add: add_Tick_refusal_trace_ctt_subset ctt_subset_imp_prefix_subset)
  have "xs \<lesssim>\<^sub>C add_Tick_refusal_trace(xs)"
    by (simp add: add_Tick_refusal_trace_ctt_subset ctt_subset_imp_prefix_subset)

  then have a:"add_Tick_refusal_trace s @ [[X \<union> {Tick}]\<^sub>R] @ xs
              \<lesssim>\<^sub>C
              add_Tick_refusal_trace s @ [[X \<union> {Tick}]\<^sub>R] @ add_Tick_refusal_trace(xs)"
  using add_Tick_in_P add_Tick_dist ctt_prefix_common_concat
    by blast
  then have b:"s @ [[X \<union> {Tick}]\<^sub>R] @ xs \<lesssim>\<^sub>C add_Tick_refusal_trace s @ [[X \<union> {Tick}]\<^sub>R] @ xs"
    using ctt_prefix_common_concat_eq_size add_Tick_refusal_trace_same_length s_le_addTick by blast

  have "s @ [[X \<union> {Tick}]\<^sub>R] @ xs \<in> P"
    using a b add_Tick_in_P assms
    by (metis CT1_def add_Tick_dist)
  then show ?thesis by auto
qed

lemma CT2s_CT4s_extends_Ref:
  assumes "CT2s P" "CT4s P" "CT1 P" "s @ [[X]\<^sub>R] @ xs \<in> P"
  shows "s @ [[X \<union> {e. e \<noteq> Tock \<and> s @ [[e]\<^sub>E] \<notin> P \<or> e = Tock \<and> s @ [[X]\<^sub>R, [Tock]\<^sub>E] \<notin> P} \<union> {Tick}]\<^sub>R] @ xs \<in> P"
proof -
  obtain Y where Y:"Y = {e. e \<noteq> Tock \<and> s @ [[e]\<^sub>E] \<notin> P \<or> e = Tock \<and> s @ [[X]\<^sub>R, [Tock]\<^sub>E] \<notin> P}"
    by auto
  then have "Y \<inter> {e. (e \<noteq> Tock \<and> s @ [[e]\<^sub>E] \<in> P) \<or> (e = Tock \<and> s @ [[X]\<^sub>R, [e]\<^sub>E] \<in> P) } = {}"
    by auto
  then have "s @ [[X \<union> Y]\<^sub>R] @ xs \<in> P"
    using assms unfolding CT2s_def by auto
  then have "s @ [[X \<union> Y \<union> {Tick}]\<^sub>R] @ xs \<in> P"
    using assms CT4s_middle_Ref_with_Tick by blast
  then show ?thesis using Y by auto
qed

lemma CTMPick_extend_Ref:
  assumes "CTMPick zs (s @ [[X]\<^sub>R]) P" "CT4s P" "CT2s P" "CT1 P"
  shows "CTMPick zs (s @ [[insert Tick (X \<union> {e. e \<noteq> Tock \<and> s @ [[e]\<^sub>E] \<notin> P \<or> e = Tock \<and> s @ [[X]\<^sub>R, [Tock]\<^sub>E] \<notin> P})]\<^sub>R]) P"
  using assms 
proof (induct zs arbitrary:s X rule:rev_induct)
  case Nil
  then show ?case by auto
next
  case (snoc x xs)
  obtain z where z:"z = (s @ [[X \<union> {e. e \<noteq> Tock \<and> s @ [[e]\<^sub>E] \<notin> P \<or> e = Tock \<and> s @ [[X]\<^sub>R, [Tock]\<^sub>E] \<notin> P} \<union> {Tick}]\<^sub>R])"
      by auto
  then have CTMPick_prefix:"CTMPick xs (s @ [[X]\<^sub>R]) P"
    using snoc CTMPick_imp_prefix by blast
  (*then have "cttWF (s @ [[X]\<^sub>R] @ xs)"
    using snoc by (metis (no_types, hide_lams) append_assoc cttWF_prefix_is_cttWF)*)
  then have "CTMPick xs (s @ [[insert Tick (X \<union> {e. e \<noteq> Tock \<and> s @ [[e]\<^sub>E] \<notin> P \<or> e = Tock \<and> s @ [[X]\<^sub>R, [Tock]\<^sub>E] \<notin> P})]\<^sub>R]) P"
    using snoc CTMPick_prefix by blast
  then have CTMPick_xs_z:"CTMPick xs z P"
    using z by auto

  from snoc have "CTMPick xs (s @ [[X]\<^sub>R]) P"
    using  CTMPick_imp_prefix' by blast
  from snoc have CTMPick_x:"CTMPick [x] (s @ [[X]\<^sub>R] @ xs) P"
    using  CTMPick_imp_prefix''
    by (metis append.assoc)

  then show ?case using snoc
  proof (cases x)
    case (ObsEvent x1)
    then show ?thesis
      using CTMPick_extend_event_imp \<open>CTMPick xs (s @ [[insert Tick (X \<union> {e. e \<noteq> Tock \<and> s @ [[e]\<^sub>E] \<notin> P \<or> e = Tock \<and> s @ [[X]\<^sub>R, [Tock]\<^sub>E] \<notin> P})]\<^sub>R]) P\<close> by blast
  next
    case (Ref x2)
    
    then have "\<forall>e. e \<noteq> Tock \<and> e \<notin> x2 \<longrightarrow> s @ [[X]\<^sub>R] @ xs @ [[e]\<^sub>E] \<in> P"
      using CTMPick_x Ref by auto
    then have "\<forall>e. e \<noteq> Tock \<and> e \<notin> x2 \<longrightarrow> s @ [[X \<union> {e. e \<noteq> Tock \<and> s @ [[e]\<^sub>E] \<notin> P \<or> e = Tock \<and> s @ [[X]\<^sub>R, [Tock]\<^sub>E] \<notin> P} \<union> {Tick}]\<^sub>R] @ xs @ [[e]\<^sub>E] \<in> P"
      using assms CT2s_CT4s_extends_Ref by blast
    then have a:"\<forall>e. e \<noteq> Tock \<and> e \<notin> x2 \<longrightarrow> z @ xs @ [[e]\<^sub>E] \<in> P"
      using z by auto

    from z have "Tock \<notin> x2 \<longrightarrow> s @ [[X]\<^sub>R] @ xs @ [[x2]\<^sub>R, [Tock]\<^sub>E] \<in> P"
      using CTMPick_x Ref by auto
    then have "Tock \<notin> x2 \<longrightarrow> s @ [[X \<union> {e. e \<noteq> Tock \<and> s @ [[e]\<^sub>E] \<notin> P \<or> e = Tock \<and> s @ [[X]\<^sub>R, [Tock]\<^sub>E] \<notin> P} \<union> {Tick}]\<^sub>R] @ xs @ [[x2]\<^sub>R, [Tock]\<^sub>E] \<in> P"
      using assms CT2s_CT4s_extends_Ref by blast
    then have b:"Tock \<notin> x2 \<longrightarrow> z @ xs @ [[x2]\<^sub>R, [Tock]\<^sub>E] \<in> P"
      using z by auto

    have c:"Tick \<in> x2"
      using CTMPick_x Ref by auto
    then have "CTMPick (xs @ [[x2]\<^sub>R]) z P"
      using CTMPick_extend_ref_imp a b c Ref CTMPick_xs_z by blast
    then show ?thesis using Ref z by auto
  qed
qed
 
lemma CT2s_imp_CTMPick_mkCTMP:
  assumes "CT2s P" "CT4s P" "CT1 P"
  shows "CTMPick (mkCTMP xs z P) z P"
  using assms
proof (induct xs z P rule:mkCTMP.induct)
  case (1 s P)
  then show ?case by auto
next
  case (2 X xs s P)
  (*then have "CTMPick (mkCTMP xs (s @ [[X]\<^sub>R]) P) (s @ [[X]\<^sub>R]) P"
    by auto
  have "([X \<union> {e. (e \<noteq> Tock \<and> s @ [[e]\<^sub>E] \<notin> P) \<or> (e = Tock \<and> s @ [[X]\<^sub>R,[Tock]\<^sub>E] \<notin> P)} \<union> {Tick}]\<^sub>R 
        # mkCTMP xs (s @ [[X]\<^sub>R]) P) = (mkCTMP ([X]\<^sub>R # xs) s P)"
    by auto

  obtain Z where Z:"Z = X \<union> {e. (e \<noteq> Tock \<and> s @ [[e]\<^sub>E] \<notin> P) \<or> (e = Tock \<and> s @ [[X]\<^sub>R,[Tock]\<^sub>E] \<notin> P)} \<union> {Tick}"
    by auto
  have "CTMPick ([Z]\<^sub>R # (mkCTMP xs (s @ [[X]\<^sub>R]) P)) s P
        =
        ((\<forall>e. e \<notin> Z \<and> e \<noteq> Tock \<longrightarrow> s @ [[e]\<^sub>E] \<in> P)
         \<and>
         (Tock \<notin> Z \<longrightarrow> s @ [[Z]\<^sub>R,[Tock]\<^sub>E] \<in> P) \<and> Tick \<in> Z \<and> CTMPick (mkCTMP xs (s @ [[X]\<^sub>R]) P) (s @ [[Z]\<^sub>R]) P)"
    by auto
  from Z have "Tick \<in> Z"
    by auto
  from Z have "(Tock \<notin> Z \<longrightarrow> s @ [[Z]\<^sub>R,[Tock]\<^sub>E] \<in> P)"
    sledgehammer*)
  then show ?case
  proof (auto)
    assume "CT1 P" "CT4s P" "CT2s P" "s @ [[X]\<^sub>R, [Tock]\<^sub>E] \<in> P"
    then show "s @ [[insert Tick (X \<union> {e. e \<noteq> Tock \<and> s @ [[e]\<^sub>E] \<notin> P})]\<^sub>R, [Tock]\<^sub>E] \<in> P"
      using CT2s_Ref_Tock_augment assms by auto
  next
    assume healths:"CT1 P" "CT4s P" "CT2s P" "CTMPick (mkCTMP xs (s @ [[X]\<^sub>R]) P) (s @ [[X]\<^sub>R]) P"
    obtain z where z:"z = (mkCTMP xs (s @ [[X]\<^sub>R]) P)" by auto
    then have "CTMPick z (s @ [[insert Tick (X \<union> {e. e \<noteq> Tock \<and> s @ [[e]\<^sub>E] \<notin> P 
                                                      \<or> e = Tock \<and> s @ [[X]\<^sub>R, [Tock]\<^sub>E] \<notin> P})]\<^sub>R]) P"
      using healths CTMPick_extend_Ref by blast
    then show "CTMPick (mkCTMP xs (s @ [[X]\<^sub>R]) P)
     (s @ [[insert Tick (X \<union> {e. e \<noteq> Tock \<and> s @ [[e]\<^sub>E] \<notin> P \<or> e = Tock \<and> s @ [[X]\<^sub>R, [Tock]\<^sub>E] \<notin> P})]\<^sub>R])
     P"
      using z by auto
  qed
next
  case (3 e xs s P)
  then show ?case by auto
qed

(*
lemma
  "CTTickTrace (mkCTMP (add_Tick_refusal_trace s) i P)"
proof (induct s i P rule:mkCTMP.induct)
  case (1 s P)
then show ?case by auto
next
  case (2 X xs s P)
  then show ?case
    apply auto
next
case (3 e xs s P)
  then show ?case by auto
qed
  sledgehammer
*)
lemma CTTickAll_mkCTMP_singleton:
  "CTTickAll {(mkCTMP s i P)}"
  unfolding CTTickAll_def by (induct s i P rule:mkCTMP.induct, auto)

lemma prirelref_prirelrefSub_part:
  assumes "CT3 Q"
  shows 
  "z \<notin> S \<union> {e. e \<noteq> Tock \<and> sa @ [[e]\<^sub>E] \<notin> Q \<or> e = Tock \<and> sa @ [[S]\<^sub>R, [Tock]\<^sub>E] \<notin> Q} \<union> {Tick}
   =
   (((z = Tock \<and> sa @ [[S]\<^sub>R, [Tock]\<^sub>E] \<in> Q) 
                      \<or>
                      (z \<notin> S \<and> sa @ [[z]\<^sub>E] \<in> Q \<and> z \<noteq> Tock \<and> z \<noteq> Tick)
                      \<or>
                      (z \<notin> S \<and> sa @ [[z]\<^sub>E] \<in> Q \<and> sa @ [[S]\<^sub>R, [Tock]\<^sub>E] \<in> Q \<and> z \<noteq> Tock \<and> z \<noteq> Tick)))"
proof -
  have "z \<notin> S \<union> {e. e \<noteq> Tock \<and> sa @ [[e]\<^sub>E] \<notin> Q \<or> e = Tock \<and> sa @ [[S]\<^sub>R, [Tock]\<^sub>E] \<notin> Q} \<union> {Tick}
          =
          (\<not> (z \<in> S \<or> z \<in> {e. e \<noteq> Tock \<and> sa @ [[e]\<^sub>E] \<notin> Q \<or> e = Tock \<and> sa @ [[S]\<^sub>R, [Tock]\<^sub>E] \<notin> Q} \<or> z = Tick))"
      by blast
    also have "... = (\<not> (z \<in> S \<or> ((z \<noteq> Tock \<and> sa @ [[z]\<^sub>E] \<notin> Q) \<or> (z = Tock \<and> sa @ [[S]\<^sub>R, [Tock]\<^sub>E] \<notin> Q \<or> z = Tick))))"
      by auto
    also have "... = (z \<notin> S \<and> ((z = Tock \<or> sa @ [[z]\<^sub>E] \<in> Q) \<and> (z \<noteq> Tock \<or> sa @ [[S]\<^sub>R, [Tock]\<^sub>E] \<in> Q) \<and> z \<noteq> Tick))"
      by auto
    also have "... = (z \<notin> S \<and> z \<noteq> Tick \<and> ((z = Tock \<and> sa @ [[S]\<^sub>R, [Tock]\<^sub>E] \<in> Q) 
                                \<or>
                                (sa @ [[z]\<^sub>E] \<in> Q \<and> z \<noteq> Tock)
                                \<or>
                                (sa @ [[z]\<^sub>E] \<in> Q \<and> sa @ [[S]\<^sub>R, [Tock]\<^sub>E] \<in> Q)))"
      by auto
    also have "... = (((z = Tock \<and> sa @ [[S]\<^sub>R, [Tock]\<^sub>E] \<in> Q) 
                      \<or>
                      (z \<notin> S \<and> sa @ [[z]\<^sub>E] \<in> Q \<and> z \<noteq> Tock \<and> z \<noteq> Tick)
                      \<or>
                      (z \<notin> S \<and> sa @ [[z]\<^sub>E] \<in> Q \<and> sa @ [[S]\<^sub>R, [Tock]\<^sub>E] \<in> Q \<and> z \<noteq> Tock \<and> z \<noteq> Tick)))"
      using assms apply auto
      using CT3_any_cons_end_tock by blast
    finally show ?thesis .
  qed

lemma prirelref_prirelrefSub:
  assumes "CT3 Q"
  shows
  "prirelref pa (S \<union> {e. e \<noteq> Tock \<and> sa @ [[e]\<^sub>E] \<notin> Q \<or> e = Tock \<and> sa @ [[S]\<^sub>R, [Tock]\<^sub>E] \<notin> Q} \<union> {Tick})
   = 
   prirelrefSub pa S sa Q"
proof -
  have "prirelref pa (S \<union> {e. e \<noteq> Tock \<and> sa @ [[e]\<^sub>E] \<notin> Q \<or> e = Tock \<and> sa @ [[S]\<^sub>R, [Tock]\<^sub>E] \<notin> Q} \<union> {Tick})
        =
        {z. z \<notin> S \<union> {e. e \<noteq> Tock \<and> sa @ [[e]\<^sub>E] \<notin> Q \<or> e = Tock \<and> sa @ [[S]\<^sub>R, [Tock]\<^sub>E] \<notin> Q} \<union> {Tick} \<longrightarrow>
        (\<exists>b. b \<notin> S \<union> {e. e \<noteq> Tock \<and> sa @ [[e]\<^sub>E] \<notin> Q \<or> e = Tock \<and> sa @ [[S]\<^sub>R, [Tock]\<^sub>E] \<notin> Q} \<union> {Tick} \<and> z <\<^sup>*pa b)}"
    unfolding prirelref_def by auto
  also have "... =
        {z. ((((z = Tock \<and> sa @ [[S]\<^sub>R, [Tock]\<^sub>E] \<in> Q) 
              \<or>
              (z \<notin> S \<and> sa @ [[z]\<^sub>E] \<in> Q \<and> z \<noteq> Tock \<and> z \<noteq> Tick)
              \<or>
              (z \<notin> S \<and> sa @ [[z]\<^sub>E] \<in> Q \<and> sa @ [[S]\<^sub>R, [Tock]\<^sub>E] \<in> Q \<and> z \<noteq> Tock \<and> z \<noteq> Tick)))) \<longrightarrow>
        (\<exists>b. b \<notin> S \<union> {e. e \<noteq> Tock \<and> sa @ [[e]\<^sub>E] \<notin> Q \<or> e = Tock \<and> sa @ [[S]\<^sub>R, [Tock]\<^sub>E] \<notin> Q} \<union> {Tick} \<and> z <\<^sup>*pa b)}"
    using prirelref_prirelrefSub_part assms
    by blast
  also have "... =
        {z. ((((z = Tock \<and> sa @ [[S]\<^sub>R, [Tock]\<^sub>E] \<in> Q) 
              \<or>
              (z \<notin> S \<and> sa @ [[z]\<^sub>E] \<in> Q \<and> z \<noteq> Tock \<and> z \<noteq> Tick)
              \<or>
              (z \<notin> S \<and> sa @ [[z]\<^sub>E] \<in> Q \<and> sa @ [[S]\<^sub>R, [Tock]\<^sub>E] \<in> Q \<and> z \<noteq> Tock \<and> z \<noteq> Tick)))) \<longrightarrow>
        (\<exists>b. ((b = Tock \<and> sa @ [[S]\<^sub>R, [Tock]\<^sub>E] \<in> Q) 
                      \<or>
                      (b \<notin> S \<and> sa @ [[b]\<^sub>E] \<in> Q \<and> b \<noteq> Tock \<and> b \<noteq> Tick)
                      \<or>
                      (b \<notin> S \<and> sa @ [[b]\<^sub>E] \<in> Q \<and> sa @ [[S]\<^sub>R, [Tock]\<^sub>E] \<in> Q \<and> b \<noteq> Tock \<and> b \<noteq> Tick)) \<and> z <\<^sup>*pa b)}"
    using prirelref_prirelrefSub_part assms
    by blast
  also have "... =
        {z. ((z = Tock \<and> sa @ [[S]\<^sub>R, [Tock]\<^sub>E] \<in> Q) 
              \<or>
              (z \<notin> S \<and> sa @ [[z]\<^sub>E] \<in> Q \<and> z \<noteq> Tock \<and> z \<noteq> Tick)
              \<or>
              (z \<notin> S \<and> sa @ [[z]\<^sub>E] \<in> Q \<and> sa @ [[S]\<^sub>R, [Tock]\<^sub>E] \<in> Q \<and> z \<noteq> Tock \<and> z \<noteq> Tick)) \<longrightarrow>
           ((sa @ [[S]\<^sub>R, [Tock]\<^sub>E] \<in> Q \<and> z <\<^sup>*pa Tock)
            \<or>
            (\<exists>b. b \<notin> S \<and> sa @ [[b]\<^sub>E] \<in> Q \<and> b \<noteq> Tock \<and> b \<noteq> Tick \<and> z <\<^sup>*pa b)
            \<or>
            (\<exists>b. b \<notin> S \<and> sa @ [[b]\<^sub>E] \<in> Q \<and> sa @ [[S]\<^sub>R, [Tock]\<^sub>E] \<in> Q \<and> b \<noteq> Tock \<and> b \<noteq> Tick \<and> z <\<^sup>*pa b) )}"
    by blast
  also have "... =
        {z. ((z = Tock \<and> sa @ [[S]\<^sub>R, [Tock]\<^sub>E] \<in> Q)
             \<or>
             (z \<notin> S \<and> sa @ [[z]\<^sub>E] \<in> Q \<and> z \<noteq> Tock \<and> z \<noteq> Tick))
             \<longrightarrow>
            ((sa @ [[S]\<^sub>R, [Tock]\<^sub>E] \<in> Q \<and> z <\<^sup>*pa Tock)
              \<or>
             (\<exists>b. b \<notin> S \<and> sa @ [[b]\<^sub>E] \<in> Q \<and> b \<noteq> Tock \<and> b \<noteq> Tick \<and> z <\<^sup>*pa b))}"
    by blast
  also have "... =
        {z. ((z = Tock \<and> sa @ [[S]\<^sub>R, [Tock]\<^sub>E] \<in> Q) \<longrightarrow> (\<exists>b. b \<notin> S \<and> sa @ [[b]\<^sub>E] \<in> Q \<and> b \<noteq> Tock \<and> b \<noteq> Tick \<and> z <\<^sup>*pa b))
             \<and>
             ((z \<notin> S \<and> sa @ [[z]\<^sub>E] \<in> Q \<and> z \<noteq> Tock \<and> z \<noteq> Tick) \<longrightarrow>
              ((sa @ [[S]\<^sub>R, [Tock]\<^sub>E] \<in> Q \<and> z <\<^sup>*pa Tock)
              \<or>
              (\<exists>b. b \<notin> S \<and> sa @ [[b]\<^sub>E] \<in> Q \<and> b \<noteq> Tock \<and> b \<noteq> Tick \<and> z <\<^sup>*pa b)))}"
    by blast
  also have "... = prirelrefSub pa S sa Q"
    unfolding prirelrefSub_def by auto
  finally show ?thesis .
qed

(*
lemma prirelRef_start_Ref_extends:
  assumes "CT1 P" "CT2s P" "CT4s P" "prirelRef pa t s (sa @ zs) (unCT1 Q)"
  shows "prirelRef pa t s (sa @ (mkCTMP zs sa Q)) (unCT1 Q)"
  using assms apply (induct pa t s zs Q arbitrary: sa rule:prirelRef.induct, auto)
*)

lemma CTMPick_imp_CTTickTrace:
  assumes "CTMPick s i P"
  shows "CTTickTrace s"
  using assms by (induct s i P rule:CTMPick.induct, auto)

lemma CTTickAll_CTMPick:
  assumes "CTMPick (s) [] P"
  shows "CTTickAll {s}"
  using assms unfolding CTTickAll_def apply auto
  using CTMPick_imp_CTTickTrace by blast

lemma CTMPick_extends_concat:
  assumes "CTMPick ys (i @ xs) P" "CTMPick xs i P"
  shows "CTMPick (xs @ ys) i P"
  using assms by (induct xs i P rule:CTMPick.induct, auto)

(* How to remove CTMPick s [] P from the following lemma? I suspect the
   key result could only be proved when considering the full definition of
   priNS in this model, whereby we take specific 's' and not arbitrary ones. *)
lemma prirelRef_unCT1_case:
  assumes "CT1 P" "CT4 P"
  shows 
  "(s @ [[Z]\<^sub>R] \<in> unCT1 P \<and> e\<^sub>2 \<notin> Z \<and> \<not>(\<exists>b. b \<notin> Z \<and> e\<^sub>2 <\<^sup>*p b))
   =
   (s @ [[Z]\<^sub>R] \<in> P \<and> CTMPick s [] P \<and> e\<^sub>2 \<notin> Z \<and> \<not>(\<exists>b. b \<notin> Z \<and> e\<^sub>2 <\<^sup>*p b)
          \<and> (\<forall>e. e \<notin> Z \<and> e \<noteq> Tock \<longrightarrow> s @ [[e]\<^sub>E] \<in> P)
          \<and> (Tock \<notin> Z \<longrightarrow> s @ [[Z]\<^sub>R,[Tock]\<^sub>E] \<in> P) \<and> Tick \<in> Z)"
proof -
  have "(s @ [[Z]\<^sub>R] \<in> unCT1 P \<and> e\<^sub>2 \<notin> Z \<and> \<not>(\<exists>b. b \<notin> Z \<and> e\<^sub>2 <\<^sup>*p b))
        =
        (s @ [[Z]\<^sub>R] \<in> P \<and> CTTickAll {s @ [[Z]\<^sub>R]} \<and> CTMPick (s @ [[Z]\<^sub>R]) [] P \<and> e\<^sub>2 \<notin> Z \<and> \<not>(\<exists>b. b \<notin> Z \<and> e\<^sub>2 <\<^sup>*p b))"
    using assms CT14_CTTick_mkCT1_exists by blast
  also have "... = 
      (s @ [[Z]\<^sub>R] \<in> P \<and> CTMPick (s @ [[Z]\<^sub>R]) [] P \<and> e\<^sub>2 \<notin> Z \<and> \<not>(\<exists>b. b \<notin> Z \<and> e\<^sub>2 <\<^sup>*p b))"
    using CTTickAll_CTMPick by blast
    (* Here need to show that CTMPick is sufficient on the refusal Z, we do not need
       to find such 's'? *)
  also have "... = 
      (s @ [[Z]\<^sub>R] \<in> P \<and> CTMPick s [] P \<and> CTMPick [[Z]\<^sub>R] s P \<and> e\<^sub>2 \<notin> Z \<and> \<not>(\<exists>b. b \<notin> Z \<and> e\<^sub>2 <\<^sup>*p b))"
    by (metis CTMPick_extends_concat CTMPick_imp_prefix CTMPick_imp_prefix'' self_append_conv2)
  also have "... = 
      (s @ [[Z]\<^sub>R] \<in> P \<and> CTMPick s [] P \<and> e\<^sub>2 \<notin> Z \<and> \<not>(\<exists>b. b \<notin> Z \<and> e\<^sub>2 <\<^sup>*p b)
          \<and> (\<forall>e. e \<notin> Z \<and> e \<noteq> Tock \<longrightarrow> s @ [[e]\<^sub>E] \<in> P)
          \<and> (Tock \<notin> Z \<longrightarrow> s @ [[Z]\<^sub>R,[Tock]\<^sub>E] \<in> P) \<and> Tick \<in> Z)"
    by auto
  finally show ?thesis .
qed

lemma
  "aa \<lesssim>\<^sub>C (mkCTMP aa i P)"
  by (induct aa i P rule:mkCTMP.induct, auto)

lemma
  assumes "prirelRef2 p ([R]\<^sub>R # [Tock]\<^sub>E # aa) ([S]\<^sub>R # [Tock]\<^sub>E # zz) s Q" "CTMPick s [] Q" "CT1 Q" "CT2s Q" "CT4s Q"
  shows "CTMPick (s @ [[S]\<^sub>R,[Tock]\<^sub>E]) [] Q"
  using assms apply(induct p aa zz s Q arbitrary:S R rule:prirelRef2.induct, auto)
  oops

(* Too strong, as in general it is not possible to pick a trace 'aa' and apply
    mkCTMP to it and get a satisfactory result in prirelRef, I think? Because
    such closure woult be based on the trace in P, which are not necessarily
    available after prioritisation. So it is non-trivial to construct the 
    appropriate sets, in general. This has to come from prirelRef2 itself.
lemma
  assumes "prirelRef2 pa aa zz i P" "CT4s P" "CT3 P" "CT2s P" "CT1 P" 
  shows "prirelRef pa (mkCTMP aa i P) (mkCTMP zz i P) i (unCT1 P)"
  using assms proof(induct pa aa zz i P rule:prirelRef2.induct, simp_all)
  fix p 
  fix R::"'a cttevent set"
  fix S s Q
  assume CT4s_healthy: "CT4s Q"
     and CT3_healthy:  "CT3 Q"
     and CT2s_healthy: "CT2s Q"
     and CT1_healthy:  "CT1 Q"
     and prirelRef:    "R \<subseteq> prirelrefSub p S s Q"
  then show "prirelref p (insert Tick (S \<union> {e. e \<noteq> Tock \<and> s @ [[e]\<^sub>E] \<notin> Q \<or> e = Tock \<and> s @ [[S]\<^sub>R, [Tock]\<^sub>E] \<notin> Q})) =
       insert Tick (R \<union> {e. e \<noteq> Tock \<and> s @ [[e]\<^sub>E] \<notin> Q \<or> e = Tock \<and> s @ [[R]\<^sub>R, [Tock]\<^sub>E] \<notin> Q})"
  proof -
    have "prirelref p (insert Tick (S \<union> {e. e \<noteq> Tock \<and> s @ [[e]\<^sub>E] \<notin> Q \<or> e = Tock \<and> s @ [[S]\<^sub>R, [Tock]\<^sub>E] \<notin> Q}))
          =
          prirelrefSub p S s Q"
      using CT3_healthy prirelref_prirelrefSub by fastforce
    have "{e. e \<noteq> Tock \<and> s @ [[e]\<^sub>E] \<notin> Q \<or> e = Tock \<and> s @ [[S]\<^sub>R, [Tock]\<^sub>E] \<notin> Q} \<union> {Tick} \<subseteq> prirelrefSub p S s Q"
      using \<open>prirelref p (insert Tick (S \<union> {e. e \<noteq> Tock \<and> s @ [[e]\<^sub>E] \<notin> Q \<or> e = Tock \<and> s @ [[S]\<^sub>R, [Tock]\<^sub>E] \<notin> Q})) = prirelrefSub p S s Q\<close> prirelref_def by auto
    have "prirelrefSub p S s Q \<subseteq> R \<union> {e. e \<noteq> Tock \<and> s @ [[e]\<^sub>E] \<notin> Q \<or> e = Tock \<and> s @ [[R]\<^sub>R, [Tock]\<^sub>E] \<notin> Q} \<union> {Tick}"
      using prirelRef  apply auto
    apply (simp_all add: prirelrefSub_def)
  oops
*)

lemma mkCTMP_dist_concat:
  "mkCTMP (xs @ [x]) i P = (mkCTMP xs i P) @ mkCTMP [x] (i @ xs) P"
  by (induct xs i P arbitrary:x rule:mkCTMP.induct, auto)

lemma mkCTMP_fixpoint_eq_CTMPick:
  "(mkCTMP s i P = s) = CTMPick s i P"
  by (induct s i P rule:mkCTMP.induct, auto)

lemma CT2s_aux1:
  assumes "CT2s P" "\<rho> @ [[X]\<^sub>R] @ \<sigma> \<in> P" "Y \<inter> {e. (e \<noteq> Tock \<and> \<rho> @ [[e]\<^sub>E] \<in> P) \<or> (e = Tock \<and> \<rho> @ [[X]\<^sub>R, [e]\<^sub>E] \<in> P) } = {}"
  shows "\<rho> @ [[X \<union> Y]\<^sub>R] @ \<sigma> \<in> P"
  using assms CT2s_def by blast

lemma CT2s_aux2:
  assumes "CT2s P" "[[X]\<^sub>R] @ \<sigma> \<in> P" "Y \<inter> {e. (e \<noteq> Tock \<and> [[e]\<^sub>E] \<in> P) \<or> (e = Tock \<and> [[X]\<^sub>R, [e]\<^sub>E] \<in> P) } = {}"
  shows "[[X \<union> Y]\<^sub>R] @ \<sigma> \<in> P"
  using assms CT2s_def by (metis (no_types, lifting) Collect_cong append.left_neutral)

lemma CT2s_aux3:
  assumes "CT2s P" "[[X]\<^sub>R] \<in> P" "Y \<inter> {e. (e \<noteq> Tock \<and> [[e]\<^sub>E] \<in> P) \<or> (e = Tock \<and> [[X]\<^sub>R, [e]\<^sub>E] \<in> P) } = {}"
  shows "[[X \<union> Y]\<^sub>R] \<in> P"
  using CT2s_aux2 assms(1) assms(2) assms(3) by auto

thm list.induct
thm rev_induct
thm mkCTMP.induct
thm wf_CT2s_induct

lemma mkCTMP_absorb_event:
  "mkCTMP xs i P @ ([[x]\<^sub>E] @ z) = mkCTMP (xs @ [[x]\<^sub>E]) i P @ z"
  by (induct xs i P arbitrary:x z rule:mkCTMP.induct, auto)

lemma mkCTMP_absorb_ref:
(*  assumes "Tick \<in> x" 
          "\<forall>xa. (xa \<noteq> Tock \<and> xs @ [[xa]\<^sub>E] \<notin> P) \<longrightarrow> xa \<in> x"
          "xs @ [[x]\<^sub>R, [Tock]\<^sub>E] \<notin> P \<longrightarrow> Tock \<in> x"*)
  shows "mkCTMP xs i P @ ([[x \<union> {e. (e \<noteq> Tock \<and> i @ xs @ [[e]\<^sub>E] \<notin> P) 
                                \<or> (e = Tock \<and> i @ xs @ [[x]\<^sub>R,[Tock]\<^sub>E] \<notin> P)} 
                               \<union> {Tick}]\<^sub>R] @ z) 
         = 
         mkCTMP (xs @ [[x]\<^sub>R]) i P @ z"
  by (induct xs i P arbitrary:x z rule:mkCTMP.induct, simp_all)

lemma mkCTMP_absorb_ref':
(*  assumes "Tick \<in> x" 
          "\<forall>xa. (xa \<noteq> Tock \<and> xs @ [[xa]\<^sub>E] \<notin> P) \<longrightarrow> xa \<in> x"
          "xs @ [[x]\<^sub>R, [Tock]\<^sub>E] \<notin> P \<longrightarrow> Tock \<in> x"*)
  shows "mkCTMP xs i P @ ([[x \<union> {e. (e \<noteq> Tock \<and> i @ xs @ [[e]\<^sub>E] \<notin> P) 
                                \<or> (e = Tock \<and> i @ xs @ [[x]\<^sub>R,[Tock]\<^sub>E] \<notin> P)} 
                               \<union> {Tick}]\<^sub>R] ) 
         = 
         mkCTMP (xs @ [[x]\<^sub>R]) i P"
  by (induct xs i P arbitrary:x rule:mkCTMP.induct, simp_all)


lemma
  assumes "mkCTMP (xs @ [[e]\<^sub>E]) i P \<in> P"
  shows "i @ xs @ [[e]\<^sub>E] \<in> P"
  using assms apply (induct xs arbitrary:i e rule:rev_induct, auto)
  oops

lemma prefix_mkCTMP:
  "aa \<lesssim>\<^sub>C (mkCTMP aa i P)"
  by (induct aa i P rule:mkCTMP.induct, auto)

lemma mkCTMP_concat_event_CT1_imp:
  assumes "mkCTMP xs [] P @ [[e]\<^sub>E] \<in> P" "CT1 P"
  shows "xs @ [[e]\<^sub>E] \<in> P"
proof -
  have "xs \<lesssim>\<^sub>C mkCTMP xs [] P"
    using assms prefix_mkCTMP by auto
  then have "xs @ [[e]\<^sub>E] \<lesssim>\<^sub>C mkCTMP xs [] P @ [[e]\<^sub>E]"
    by (metis append.right_neutral mkCTMP_absorb_event prefix_mkCTMP)
  then show ?thesis using assms
    using CT1_def by blast
qed

lemma mkCTMP_eq_size:
  "size xs = (size (mkCTMP xs i P))"
  by (induct xs i P rule:mkCTMP.induct, auto)

lemma mkCTMP_concat_ref_Tock_CT1_imp:
  assumes "mkCTMP xs [] P @ [[x2]\<^sub>R, [Tock]\<^sub>E] \<in> P" "CT1 P"
  shows "xs @ [[x2]\<^sub>R, [Tock]\<^sub>E] \<in> P"
proof -
  have "xs \<lesssim>\<^sub>C mkCTMP xs [] P"
    using assms prefix_mkCTMP by auto
  then have "xs @ [[x2]\<^sub>R, [Tock]\<^sub>E] \<lesssim>\<^sub>C mkCTMP xs [] P @ [[x2]\<^sub>R, [Tock]\<^sub>E]"
    using mkCTMP_eq_size ctt_prefix_common_concat_eq_size by blast
  then show ?thesis using assms
    using CT1_def by blast
qed

lemma mkCTMP_in_P:
  assumes "s @ z \<in> P" "CT4s P" "CT3 P" "CT2s P" "CT1 P"
  shows "(mkCTMP s [] P) @ z \<in> P"
  using assms
proof (induct s arbitrary:z P rule:rev_induct)
  case Nil
  then show ?case by auto
next
  case (snoc x xs)
  then have mkCTMP_hyp:"mkCTMP xs [] P @ ([x] @ z) \<in> P"
    by auto
  then show ?case
  proof (cases x)
    case (ObsEvent x1)
    then have "mkCTMP xs [] P @ ([x] @ z) = mkCTMP (xs @ [x]) [] P @ z"
      using mkCTMP_absorb_event by auto
    then show ?thesis using mkCTMP_hyp
      by presburger
  next
    case (Ref x2)
    then obtain y where y:"y = mkCTMP xs [] P"
      by auto
    then have y_cons:"y @ [[x2]\<^sub>R] @ z \<in> P"
      using Ref mkCTMP_hyp by auto
    have "{e. (e \<noteq> Tock \<and> xs @ [[e]\<^sub>E] \<notin> P) \<or> (e = Tock \<and> xs @ [[x2]\<^sub>R,[Tock]\<^sub>E] \<notin> P)} 
            \<inter>
            {e. (e \<noteq> Tock \<and> y @ [[e]\<^sub>E] \<in> P) \<or> (e = Tock \<and> y @ [[x2]\<^sub>R, [e]\<^sub>E] \<in> P) } = {}"
      apply auto
      using snoc mkCTMP_concat_event_CT1_imp y apply blast
      using snoc mkCTMP_concat_ref_Tock_CT1_imp y by blast
    then have "y @ [[x2 \<union> {e. (e \<noteq> Tock \<and> xs @ [[e]\<^sub>E] \<notin> P) \<or> (e = Tock \<and> xs @ [[x2]\<^sub>R,[Tock]\<^sub>E] \<notin> P)}]\<^sub>R] @ z \<in> P"
      using y_cons CT2s_def snoc.prems(4) sup_set_def by blast
    then have "y @ [[x2 \<union> {e. (e \<noteq> Tock \<and> xs @ [[e]\<^sub>E] \<notin> P) \<or> (e = Tock \<and> xs @ [[x2]\<^sub>R,[Tock]\<^sub>E] \<notin> P)} \<union> {Tick}]\<^sub>R] @ z \<in> P"
      using CT4s_def by (meson CT4s_middle_Ref_with_Tick snoc.prems(2) snoc.prems(5))
    then have "mkCTMP (xs @ [[x2]\<^sub>R]) [] P @ z \<in> P"
      using y mkCTMP_absorb_ref
      by (smt Collect_cong append_self_conv2)
    then show ?thesis using Ref by blast
  qed
qed

lemma CTs_mkCTMP_in_P:
  assumes "s \<in> P" "CT4s P" "CT3 P" "CT2s P" "CT1 P"
  shows "(mkCTMP s [] P) \<in> P"
  using assms mkCTMP_in_P
  by (metis append_Nil2)

lemma prirelRef_unCT1_case_specific:
  assumes "CT4s P" "CT3 P" "CT2s P" "CT1 P"
          "(\<forall>e. e \<notin> Z \<and> e \<noteq> Tock \<longrightarrow> s @ [[e]\<^sub>E] \<in> P)"
          "(Tock \<notin> Z \<longrightarrow> s @ [[Z]\<^sub>R,[Tock]\<^sub>E] \<in> P)"
          "Tick \<in> Z"
          "(mkCTMP s [] P) @ [[Z]\<^sub>R] \<in> P"
  shows 
  "(mkCTMP s [] P) @ [[Z]\<^sub>R] \<in> unCT1 P"
proof -
  have "((mkCTMP s [] P) @ [[Z]\<^sub>R] \<in> unCT1 P)
        =
        ((mkCTMP s [] P) @ [[Z]\<^sub>R] \<in> (\<Union>{x. CTM2a x \<and> CTM2b x \<and> CTTickAll x \<and> CT1c x \<and> (mkCT1 x) \<subseteq> P}))"
    unfolding unCT1_def by auto
  also have "... = 
       (\<exists>x. (mkCTMP s [] P) @ [[Z]\<^sub>R] \<in> x \<and> CTM2a x \<and> CTM2b x \<and> CTTickAll x \<and> CT1c x \<and> (mkCT1 x) \<subseteq> P)"
    by auto
  also have "... =
       ((mkCTMP s [] P) @ [[Z]\<^sub>R] \<in> P \<and> CTTickAll {(mkCTMP s [] P) @ [[Z]\<^sub>R]} \<and> CTMPick ((mkCTMP s [] P) @ [[Z]\<^sub>R]) [] P)"
    using assms CTTickAll_mkCT1_simp CT4s_CT1_imp_CT4 by auto
  also have "... =
       ((mkCTMP s [] P) @ [[Z]\<^sub>R] \<in> P \<and> CTMPick ((mkCTMP s [] P) @ [[Z]\<^sub>R]) [] P)"
    using CTTickAll_CTMPick by blast
  also have "... =
       ((mkCTMP s [] P) @ [[Z]\<^sub>R] \<in> P)"
  proof -
    have "Z = Z \<union> {e. e \<noteq> Tock \<and> s @ [[e]\<^sub>E] \<notin> P \<or> e = Tock \<and> s @ [[Z]\<^sub>R, [Tock]\<^sub>E] \<notin> P} \<union> {Tick}"
      using assms by auto
    then have "(mkCTMP s [] P) @ [[Z]\<^sub>R] = (mkCTMP s [] P) @ [[Z \<union> {e. e \<noteq> Tock \<and> s @ [[e]\<^sub>E] \<notin> P \<or> e = Tock \<and> s @ [[Z]\<^sub>R, [Tock]\<^sub>E] \<notin> P} \<union> {Tick}]\<^sub>R]"
      by auto
    also have "... = (mkCTMP (s @ [[Z]\<^sub>R]) [] P)"
      using mkCTMP_absorb_ref'
      by (simp add: mkCTMP_dist_concat)
    then have "CTMPick ((mkCTMP s [] P) @ [[Z]\<^sub>R]) [] P"
      by (simp add: CT2s_imp_CTMPick_mkCTMP assms(1) assms(3) assms(4) calculation)
    then show ?thesis by auto
  qed

  finally show ?thesis using assms by auto 
qed

lemma CTMPick_Refusal_subset:
  assumes "CTMPick (xs @ [[Sa]\<^sub>R] @ ys) i Q"
  shows "{e. e \<noteq> Tock \<and> i @ xs @ [[e]\<^sub>E] \<notin> Q \<or> e = Tock \<and> i @ xs @ [[Sa]\<^sub>R, [Tock]\<^sub>E] \<notin> Q} \<union> {Tick} \<subseteq> Sa"
  using assms by (induct xs i Q rule:CTMPick.induct, auto)

lemma CTMPick_Refusal_extend:
  assumes "CTMPick (xs @ [[Sa]\<^sub>R] @ ys) i Q"
  shows "CTMPick (xs @ [[Sa \<union> {e. e \<noteq> Tock \<and> i @ xs @ [[e]\<^sub>E] \<notin> Q \<or> e = Tock \<and> i @ xs @ [[Sa]\<^sub>R, [Tock]\<^sub>E] \<notin> Q} \<union> {Tick}]\<^sub>R] @ ys) i Q"
  using assms CTMPick_Refusal_subset
  by (smt Un_absorb2 le_supE mem_Collect_eq subset_eq)

lemma concat_unCT1_extend_CT2s_Refusal:
  assumes "xs @ [[Sa]\<^sub>R] @ ys \<in> unCT1 Q" "CT2s Q" "CT1 Q" "CT4 Q"
  shows "xs @ [[Sa \<union> {e. e \<noteq> Tock \<and> xs @ [[e]\<^sub>E] \<notin> Q \<or> e = Tock \<and> xs @ [[Sa]\<^sub>R, [Tock]\<^sub>E] \<notin> Q} \<union> {Tick}]\<^sub>R] @ ys \<in> unCT1 Q"
proof -
  have "xs @ [[Sa]\<^sub>R] @ ys \<in> unCT1 Q 
        = 
        (xs @ [[Sa]\<^sub>R] @ ys \<in> (\<Union>{x. CTM2a x \<and> CTM2b x \<and> CTTickAll x \<and> CT1c x \<and> (mkCT1 x) \<subseteq> Q}))"
    unfolding unCT1_def by auto
  also have "... = (\<exists>x. xs @ [[Sa]\<^sub>R] @ ys \<in> x \<and> CTM2a x \<and> CTM2b x \<and> CTTickAll x \<and> CT1c x \<and> (mkCT1 x) \<subseteq> Q)"
    by auto
  also have "... = (xs @ [[Sa]\<^sub>R] @ ys \<in> Q \<and> CTTickAll {xs @ [[Sa]\<^sub>R] @ ys} \<and> CTMPick (xs @ [[Sa]\<^sub>R] @ ys) [] Q)"
    using CTTickAll_mkCT1_simp assms by blast
  also have "... = (xs @ [[Sa]\<^sub>R] @ ys \<in> Q \<and> CTMPick (xs @ [[Sa]\<^sub>R] @ ys) [] Q)"
    using assms CTTickAll_CTMPick by blast
  then have "(xs @ [[Sa]\<^sub>R] @ ys \<in> Q \<and> CTMPick (xs @ [[Sa]\<^sub>R] @ ys) [] Q)"
    using assms calculation by auto
  then have "(xs @ [[Sa \<union> {e. e \<noteq> Tock \<and> xs @ [[e]\<^sub>E] \<notin> Q \<or> e = Tock \<and> xs @ [[Sa]\<^sub>R, [Tock]\<^sub>E] \<notin> Q}]\<^sub>R] @ ys \<in> Q 
                    \<and> CTMPick (xs @ [[Sa]\<^sub>R] @ ys) [] Q)"
    using assms CT2s_extends_Ref by fastforce
  then have "(xs @ [[Sa \<union> {e. e \<noteq> Tock \<and> xs @ [[e]\<^sub>E] \<notin> Q \<or> e = Tock \<and> xs @ [[Sa]\<^sub>R, [Tock]\<^sub>E] \<notin> Q} \<union> {Tick}]\<^sub>R] @ ys \<in> Q 
                    \<and> CTMPick (xs @ [[Sa]\<^sub>R] @ ys) [] Q)"
    using CTMPick_imp_prefix'' insert_absorb by fastforce
  then have "(xs @ [[Sa \<union> {e. e \<noteq> Tock \<and> xs @ [[e]\<^sub>E] \<notin> Q \<or> e = Tock \<and> xs @ [[Sa]\<^sub>R, [Tock]\<^sub>E] \<notin> Q} \<union> {Tick}]\<^sub>R] @ ys \<in> Q 
                    \<and> CTMPick (xs @ [[Sa \<union> {e. e \<noteq> Tock \<and> xs @ [[e]\<^sub>E] \<notin> Q \<or> e = Tock \<and> xs @ [[Sa]\<^sub>R, [Tock]\<^sub>E] \<notin> Q} \<union> {Tick}]\<^sub>R] @ ys) [] Q)"
    using CTMPick_Refusal_extend by fastforce
  then have "(xs @ [[Sa \<union> {e. e \<noteq> Tock \<and> xs @ [[e]\<^sub>E] \<notin> Q \<or> e = Tock \<and> xs @ [[Sa]\<^sub>R, [Tock]\<^sub>E] \<notin> Q} \<union> {Tick}]\<^sub>R] @ ys \<in> Q 
                    \<and> CTTickAll {xs @ [[Sa \<union> {e. e \<noteq> Tock \<and> xs @ [[e]\<^sub>E] \<notin> Q \<or> e = Tock \<and> xs @ [[Sa]\<^sub>R, [Tock]\<^sub>E] \<notin> Q} \<union> {Tick}]\<^sub>R] @ ys}
                    \<and> CTMPick (xs @ [[Sa \<union> {e. e \<noteq> Tock \<and> xs @ [[e]\<^sub>E] \<notin> Q \<or> e = Tock \<and> xs @ [[Sa]\<^sub>R, [Tock]\<^sub>E] \<notin> Q} \<union> {Tick}]\<^sub>R] @ ys) [] Q)"
    using assms CTTickAll_CTMPick by blast
  then have a:"(\<exists>x. xs @ [[Sa \<union> {e. e \<noteq> Tock \<and> xs @ [[e]\<^sub>E] \<notin> Q \<or> e = Tock \<and> xs @ [[Sa]\<^sub>R, [Tock]\<^sub>E] \<notin> Q} \<union> {Tick}]\<^sub>R] @ ys \<in> Q 
                \<and> CTM2a x \<and> CTM2b x \<and> CTTickAll x \<and> CT1c x \<and> (mkCT1 x) \<subseteq> Q)"
    using CTTickAll_mkCT1_simp assms by blast

  then have "(\<exists>x. xs @ [[Sa \<union> {e. e \<noteq> Tock \<and> xs @ [[e]\<^sub>E] \<notin> Q \<or> e = Tock \<and> xs @ [[Sa]\<^sub>R, [Tock]\<^sub>E] \<notin> Q} \<union> {Tick}]\<^sub>R] @ ys \<in> Q 
                \<and> CTM2a x \<and> CTM2b x \<and> CTTickAll x \<and> CT1c x \<and> (mkCT1 x) \<subseteq> Q)
              =
              (xs @ [[Sa \<union> {e. e \<noteq> Tock \<and> xs @ [[e]\<^sub>E] \<notin> Q \<or> e = Tock \<and> xs @ [[Sa]\<^sub>R, [Tock]\<^sub>E] \<notin> Q} \<union> {Tick}]\<^sub>R] @ ys
              \<in> (\<Union>{x. CTM2a x \<and> CTM2b x \<and> CTTickAll x \<and> CT1c x \<and> (mkCT1 x) \<subseteq> Q}))"
    apply auto
    using CTTickAll_CTMPick CTTickAll_mkCT1_simp \<open>xs @ [[Sa \<union> {e. e \<noteq> Tock \<and> xs @ [[e]\<^sub>E] \<notin> Q \<or> e = Tock \<and> xs @ [[Sa]\<^sub>R, [Tock]\<^sub>E] \<notin> Q} \<union> {Tick}]\<^sub>R] @ ys \<in> Q \<and> CTMPick (xs @ [[Sa \<union> {e. e \<noteq> Tock \<and> xs @ [[e]\<^sub>E] \<notin> Q \<or> e = Tock \<and> xs @ [[Sa]\<^sub>R, [Tock]\<^sub>E] \<notin> Q} \<union> {Tick}]\<^sub>R] @ ys) [] Q\<close> assms(3) assms(4) by fastforce
  then have "(xs @ [[Sa \<union> {e. e \<noteq> Tock \<and> xs @ [[e]\<^sub>E] \<notin> Q \<or> e = Tock \<and> xs @ [[Sa]\<^sub>R, [Tock]\<^sub>E] \<notin> Q} \<union> {Tick}]\<^sub>R] @ ys
              \<in> (\<Union>{x. CTM2a x \<and> CTM2b x \<and> CTTickAll x \<and> CT1c x \<and> (mkCT1 x) \<subseteq> Q}))"
    using a by auto
  then have "xs @ [[Sa \<union> {e. e \<noteq> Tock \<and> xs @ [[e]\<^sub>E] \<notin> Q \<or> e = Tock \<and> xs @ [[Sa]\<^sub>R, [Tock]\<^sub>E] \<notin> Q} \<union> {Tick}]\<^sub>R] @ ys \<in> unCT1 Q"
    unfolding unCT1_def by auto
  then show ?thesis .
qed

lemma prirelRef_start_Ref_extends:
  assumes "CT1 Q" "CT2s Q" "CT4 Q" "prirelRef pa t s (sa @ [[S]\<^sub>R, [Tock]\<^sub>E] @ z) (unCT1 Q)" 
  shows "prirelRef pa t s (sa @ [[S \<union> {e. e \<noteq> Tock \<and> sa @ [[e]\<^sub>E] \<notin> Q \<or> e = Tock \<and> sa @ [[S]\<^sub>R, [Tock]\<^sub>E] \<notin> Q} \<union> {Tick}]\<^sub>R, [Tock]\<^sub>E] @ z) (unCT1 Q)"
  using assms proof(induct pa t s z Q arbitrary:S sa rule:prirelRef.induct, auto)
  fix p 
  fix aa::"'a cttobs list" 
  fix e\<^sub>2 zz sb Qa Sa saa Z
  assume 
    hyp:  "(\<And>S sa.
           prirelRef p aa zz (sa @ [S]\<^sub>R # [Tock]\<^sub>E # sb @ [[e\<^sub>2]\<^sub>E]) (unCT1 Qa) \<Longrightarrow>
           prirelRef p aa zz
            (sa @ [insert Tick (S \<union> {e. e \<noteq> Tock \<and> sa @ [[e]\<^sub>E] \<notin> Qa \<or> e = Tock \<and> sa @ [[S]\<^sub>R, [Tock]\<^sub>E] \<notin> Qa})]\<^sub>R # [Tock]\<^sub>E # sb @ [[e\<^sub>2]\<^sub>E])
            (unCT1 Qa))"
    and CT1_healthy:    "CT1 Qa" 
    and CT2s_healthy:   "CT2s Qa"
    and CT4_healthy:   "CT4 Qa"
    and prirelRef:      "prirelRef p aa zz (saa @ [Sa]\<^sub>R # [Tock]\<^sub>E # sb @ [[e\<^sub>2]\<^sub>E]) (unCT1 Qa)"
    and assm1:          "saa @ [Sa]\<^sub>R # [Tock]\<^sub>E # sb @ [[Z]\<^sub>R] \<in> unCT1 Qa"
    and assm2:          "e\<^sub>2 \<notin> Z"
    and assm3:          "\<forall>b. b \<in> Z \<or> \<not> e\<^sub>2 <\<^sup>*p b"
    and assm4:          "\<forall>Z. saa @ [insert Tick (Sa \<union> {e. e \<noteq> Tock \<and> saa @ [[e]\<^sub>E] \<notin> Qa \<or> e = Tock \<and> saa @ [[Sa]\<^sub>R, [Tock]\<^sub>E] \<notin> Qa})]\<^sub>R # [Tock]\<^sub>E # sb @ [[Z]\<^sub>R]
                            \<in> unCT1 Qa \<longrightarrow>
                              e\<^sub>2 \<in> Z \<or> (\<exists>b. b \<notin> Z \<and> e\<^sub>2 <\<^sup>*p b)"
  then show "maximal(p,e\<^sub>2)"
  proof -
    have "saa @ [[Sa]\<^sub>R] @ [Tock]\<^sub>E # sb @ [[Z]\<^sub>R] \<in> unCT1 Qa"
      using assm1 by auto
    then have "saa @ [[Sa \<union> {e. e \<noteq> Tock \<and> saa @ [[e]\<^sub>E] \<notin> Qa \<or> e = Tock \<and> saa @ [[Sa]\<^sub>R, [Tock]\<^sub>E] \<notin> Qa} \<union> {Tick}]\<^sub>R] @ [Tock]\<^sub>E # sb @ [[Z]\<^sub>R] \<in> unCT1 Qa"
      using CT1_healthy CT2s_healthy CT4_healthy concat_unCT1_extend_CT2s_Refusal by blast
    then have "saa @ [Sa \<union> {e. e \<noteq> Tock \<and> saa @ [[e]\<^sub>E] \<notin> Qa \<or> e = Tock \<and> saa @ [[Sa]\<^sub>R, [Tock]\<^sub>E] \<notin> Qa} \<union> {Tick}]\<^sub>R # [Tock]\<^sub>E # sb @ [[Z]\<^sub>R] \<in> unCT1 Qa"
      by auto
    then have "\<exists>Z. saa @ [Sa \<union> {e. e \<noteq> Tock \<and> saa @ [[e]\<^sub>E] \<notin> Qa \<or> e = Tock \<and> saa @ [[Sa]\<^sub>R, [Tock]\<^sub>E] \<notin> Qa} \<union> {Tick}]\<^sub>R # [Tock]\<^sub>E # sb @ [[Z]\<^sub>R] \<in> unCT1 Qa \<and> e\<^sub>2 \<notin> Z \<and> \<not>(\<exists>b. b \<notin> Z \<and> e\<^sub>2 <\<^sup>*p b)"
      using assm2 assm3 by blast
    then have "\<not>(\<forall>Z. saa @ [Sa \<union> {e. e \<noteq> Tock \<and> saa @ [[e]\<^sub>E] \<notin> Qa \<or> e = Tock \<and> saa @ [[Sa]\<^sub>R, [Tock]\<^sub>E] \<notin> Qa} \<union> {Tick}]\<^sub>R # [Tock]\<^sub>E # sb @ [[Z]\<^sub>R] \<in> unCT1 Qa \<longrightarrow> e\<^sub>2 \<in> Z \<or> (\<exists>b. b \<notin> Z \<and> e\<^sub>2 <\<^sup>*p b))"
      by blast
    (* Show contradiction *)
    then show ?thesis using assm4 by auto
  qed
qed

(*
lemma prirelRef_start_Ref_extends:
  assumes "CT1 Q" "CT2s Q" "CT4 Q" "prirelRef pa t s ((mkCTMP zs [] Q) @ z) (unCT1 Q)" 
  shows "prirelRef pa t s (zs @ z) (unCT1 Q)"
  using assms proof(induct pa t s z Q arbitrary:zs rule:prirelRef.induct, auto)
  fix p 
  fix aa::"'a cttobs list" 
  fix e\<^sub>2 zz sa Qa zsa Z
  assume 
    hyp:  "(\<And>zs. prirelRef p aa zz (mkCTMP zs [] Qa @ sa @ [[e\<^sub>2]\<^sub>E]) (unCT1 Qa) \<Longrightarrow> prirelRef p aa zz (zs @ sa @ [[e\<^sub>2]\<^sub>E]) (unCT1 Qa))"
    and CT1_healthy:    "CT1 Qa" 
    and CT2s_healthy:   "CT2s Qa"
    and CT4_healthy:   "CT4 Qa"
    and prirelRef:      "prirelRef p aa zz (mkCTMP zsa [] Qa @ sa @ [[e\<^sub>2]\<^sub>E]) (unCT1 Qa)"
    and assm1:          "mkCTMP zsa [] Qa @ sa @ [[Z]\<^sub>R] \<in> unCT1 Qa"
    and assm2:          "e\<^sub>2 \<notin> Z"
    and assm3:          "\<forall>b. b \<in> Z \<or> \<not> e\<^sub>2 <\<^sup>*p b"
    and assm4:          "\<forall>Z. zsa @ sa @ [[Z]\<^sub>R] \<in> unCT1 Qa \<longrightarrow> e\<^sub>2 \<in> Z \<or> (\<exists>b. b \<notin> Z \<and> e\<^sub>2 <\<^sup>*p b)"
  then show "maximal(p,e\<^sub>2)"
  proof -
    have "mkCTMP zsa [] Qa @ sa @ [[Z]\<^sub>R] \<in> unCT1 Qa"
      using assm1 by auto
    then have "prirelRef p aa zz (mkCTMP zsa [] Qa @ sa @ [[e\<^sub>2]\<^sub>E]) (unCT1 Qa)"
      using prirelRef by auto
    then have "prirelRef p ([e\<^sub>2]\<^sub>E # aa) ([e\<^sub>2]\<^sub>E # zz) (mkCTMP zsa [] Qa @ sa) (unCT1 Qa)"
      using assm2 assm3 assm1 by auto

    have "prirelRef p aa zz (zsa @ sa @ [[e\<^sub>2]\<^sub>E]) (unCT1 Qa)"
      using hyp prirelRef by auto

    then have "prirelRef p ([e\<^sub>2]\<^sub>E # aa) ([e\<^sub>2]\<^sub>E # zz) (zsa @ sa) (unCT1 Qa)"
      using assm2 assm3 assm1 assm4 apply auto
   
    then have "saa @ [[Sa \<union> {e. e \<noteq> Tock \<and> saa @ [[e]\<^sub>E] \<notin> Qa \<or> e = Tock \<and> saa @ [[Sa]\<^sub>R, [Tock]\<^sub>E] \<notin> Qa} \<union> {Tick}]\<^sub>R] @ [Tock]\<^sub>E # sb @ [[Z]\<^sub>R] \<in> unCT1 Qa"
      using CT1_healthy CT2s_healthy CT4_healthy concat_unCT1_extend_CT2s_Refusal by blast
    then have "saa @ [Sa \<union> {e. e \<noteq> Tock \<and> saa @ [[e]\<^sub>E] \<notin> Qa \<or> e = Tock \<and> saa @ [[Sa]\<^sub>R, [Tock]\<^sub>E] \<notin> Qa} \<union> {Tick}]\<^sub>R # [Tock]\<^sub>E # sb @ [[Z]\<^sub>R] \<in> unCT1 Qa"
      by auto
    then have "\<exists>Z. saa @ [Sa \<union> {e. e \<noteq> Tock \<and> saa @ [[e]\<^sub>E] \<notin> Qa \<or> e = Tock \<and> saa @ [[Sa]\<^sub>R, [Tock]\<^sub>E] \<notin> Qa} \<union> {Tick}]\<^sub>R # [Tock]\<^sub>E # sb @ [[Z]\<^sub>R] \<in> unCT1 Qa \<and> e\<^sub>2 \<notin> Z \<and> \<not>(\<exists>b. b \<notin> Z \<and> e\<^sub>2 <\<^sup>*p b)"
      using assm2 assm3 by blast
    then have "\<not>(\<forall>Z. saa @ [Sa \<union> {e. e \<noteq> Tock \<and> saa @ [[e]\<^sub>E] \<notin> Qa \<or> e = Tock \<and> saa @ [[Sa]\<^sub>R, [Tock]\<^sub>E] \<notin> Qa} \<union> {Tick}]\<^sub>R # [Tock]\<^sub>E # sb @ [[Z]\<^sub>R] \<in> unCT1 Qa \<longrightarrow> e\<^sub>2 \<in> Z \<or> (\<exists>b. b \<notin> Z \<and> e\<^sub>2 <\<^sup>*p b))"
      by blast
*)
(*
lemma
  assumes "prirelRef p xs ys (sa @ zs @ z) (unCT1 P)" "CT1 P" "CT3 P" "CT2s P" "CT4s P"
  shows "prirelRef p xs ys (sa @ (mkCTMP zs sa P) @ z) (unCT1 P)"
  using assms apply(induct p xs ys z P arbitrary:sa zs rule:prirelRef.induct, auto)
  sledgehammer
  oops

lemma prirelRef_start_Ref_extends:
  assumes "CT1 Q" "CT2s Q" "CT4s Q" "prirelRef pa t s (sa @ [[S]\<^sub>R, [Tock]\<^sub>E]) (unCT1 Q)"
  shows "prirelRef pa t s (sa @ [[S \<union> {e. e \<noteq> Tock \<and> sa @ [[e]\<^sub>E] \<notin> Q \<or> e = Tock \<and> sa @ [[S]\<^sub>R, [Tock]\<^sub>E] \<notin> Q} \<union> {Tick}]\<^sub>R, [Tock]\<^sub>E]) (unCT1 Q)"
  sorry (* FIXME: Proved above. *)
*)

(*
proof (induct s arbitrary:P rule:rev_induct)
  case Nil
  then show ?case by auto
next
  case (snoc x xs)
  then have "(mkCTMP xs [] P) \<in> P"
    by (meson CT1_def ctt_prefix_subset_front ctt_prefix_subset_refl)
  then have "CTMPick (mkCTMP xs [] P) [] P"
    by (simp add: CT2s_imp_CTMPick_mkCTMP snoc.prems(2) snoc.prems(4) snoc.prems(5))
(*  then have "\<forall>e X. (e \<notin> X \<and> e \<noteq> Tock \<and> ((mkCTMP xs [] P) @ [[X]\<^sub>R])) \<longrightarrow> ((mkCTMP xs [] P) @ [[e]\<^sub>E]) \<in> P"
*)
  have "mkCTMP (xs @ [x]) [] P = (mkCTMP xs [] P) @ mkCTMP [x] ([] @ xs) P"
    using mkCTMP_dist_concat by blast
  also have "... = (mkCTMP xs [] P) @ mkCTMP [x] xs P"
    by auto
  show ?case using snoc
  proof (induct xs rule:rev_induct)
    case Nil
    then show ?case 
    proof (cases x)
      case (ObsEvent x1)
      then show ?thesis using Nil by auto
    next
      case (Ref x2)
      then have x2_in_P:"[[x2]\<^sub>R] \<in> P"
        using Nil.prems(2) by auto
      have "{e. (e \<noteq> Tock \<and> [[e]\<^sub>E] \<notin> P) \<or> (e = Tock \<and> [[x2]\<^sub>R,[Tock]\<^sub>E] \<notin> P)} 
            \<inter>
            {e. (e \<noteq> Tock \<and> [[e]\<^sub>E] \<in> P) \<or> (e = Tock \<and> [[x2]\<^sub>R, [e]\<^sub>E] \<in> P) } = {}"
        by auto
      then have "[[x2 \<union> {e. (e \<noteq> Tock \<and> [[e]\<^sub>E] \<notin> P) \<or> (e = Tock \<and> [[x2]\<^sub>R,[Tock]\<^sub>E] \<notin> P)}]\<^sub>R] \<in> P"
        using snoc CT2s_aux2 x2_in_P by fastforce
      then have x2_TT:"[[x2 \<union> {e. (e \<noteq> Tock \<and> [[e]\<^sub>E] \<notin> P) \<or> (e = Tock \<and> [[x2]\<^sub>R,[Tock]\<^sub>E] \<notin> P)} \<union> {Tick}]\<^sub>R] \<in> P"
        using \<open>CT4s P\<close> CT4s_def by fastforce
      then have "mkCTMP ([] @ [x]) [] P = [[x2 \<union> {e. (e \<noteq> Tock \<and> [[e]\<^sub>E] \<notin> P) \<or> (e = Tock \<and> [[x2]\<^sub>R,[Tock]\<^sub>E] \<notin> P)} \<union> {Tick}]\<^sub>R]"
        using Ref by auto
      then show ?thesis using x2_TT by auto
    qed
  next
    case (snoc z zs)
    then show ?case sorry
  qed
  proof (cases x)
    case (ObsEvent x1)
    then have "mkCTMP [[x1]\<^sub>E] (xs) P = [[x1]\<^sub>E]"
      by simp
    then have "(mkCTMP xs [] P) @ [[x1]\<^sub>E] \<in> P"
      sledgehammer
    then show ?thesis sorry
  next
    case (Ref x2)
    then show ?thesis sorry
  qed
qed
  apply (case_tac x, auto)
  sledgehammer*)

lemma mkCTMP_absorb_Ref_Tock:
(*  assumes "Tick \<in> x" 
          "\<forall>xa. (xa \<noteq> Tock \<and> xs @ [[xa]\<^sub>E] \<notin> P) \<longrightarrow> xa \<in> x"
          "xs @ [[x]\<^sub>R, [Tock]\<^sub>E] \<notin> P \<longrightarrow> Tock \<in> x"*)
  shows "mkCTMP xs i P @ ([[x \<union> {e. (e \<noteq> Tock \<and> i @ xs @ [[e]\<^sub>E] \<notin> P) 
                                \<or> (e = Tock \<and> i @ xs @ [[x]\<^sub>R,[Tock]\<^sub>E] \<notin> P)} 
                               \<union> {Tick}]\<^sub>R,[Tock]\<^sub>E] @ z) 
         = 
         mkCTMP (xs @ [[x]\<^sub>R,[Tock]\<^sub>E]) i P @ z"
  by (induct xs i P arbitrary:x z rule:mkCTMP.induct, simp_all)

lemma mkCTMP_absorb_Ref_Tock':
(*  assumes "Tick \<in> x" 
          "\<forall>xa. (xa \<noteq> Tock \<and> xs @ [[xa]\<^sub>E] \<notin> P) \<longrightarrow> xa \<in> x"
          "xs @ [[x]\<^sub>R, [Tock]\<^sub>E] \<notin> P \<longrightarrow> Tock \<in> x"*)
  shows "mkCTMP xs i P @ ([[x \<union> {e. (e \<noteq> Tock \<and> i @ xs @ [[e]\<^sub>E] \<notin> P) 
                                \<or> (e = Tock \<and> i @ xs @ [[x]\<^sub>R,[Tock]\<^sub>E] \<notin> P)} 
                               \<union> {Tick}]\<^sub>R,[Tock]\<^sub>E]) 
         = 
         mkCTMP (xs @ [[x]\<^sub>R,[Tock]\<^sub>E]) i P"
  by (induct xs i P arbitrary:x rule:mkCTMP.induct, simp_all)

lemma
  "mkCTMP (sa @ [[S]\<^sub>R, [Tock]\<^sub>E]) [] Q
   =
   (mkCTMP sa [] Q) @ [[S \<union> {e. e \<noteq> Tock \<and> sa @ [[e]\<^sub>E] \<notin> Q \<or> e = Tock \<and> sa @ [[S]\<^sub>R, [Tock]\<^sub>E] \<notin> Q} \<union> {Tick}]\<^sub>R, [Tock]\<^sub>E]"
  using mkCTMP_absorb_Ref_Tock'
  by (smt Collect_cong append.left_neutral)

lemma prirelRef2_CTMPick_imp_prirelRef:
  assumes "prirelRef2 p x s i P" "CT4s P" "CT3 P" "CT2s P" "CT1 P"
  shows "\<exists>t. x \<lesssim>\<^sub>C t \<and> CTMPick (mkCTMP s i P) i P \<and> prirelRef p t (mkCTMP s i P) (mkCTMP i [] P) (unCT1 P)"
proof -
  have "(\<exists>t. x \<lesssim>\<^sub>C t \<and> CTMPick (mkCTMP s i P) i P \<and> prirelRef p t (mkCTMP s i P) (mkCTMP i [] P) (unCT1 P))
        =
        (\<exists>t. x \<lesssim>\<^sub>C t \<and> prirelRef p t (mkCTMP s i P) (mkCTMP i [] P) (unCT1 P))"
    using assms CT2s_imp_CTMPick_mkCTMP by blast
  also have "... = True"
    using assms proof (induct p x s i P rule:prirelRef2.induct, auto)
    fix pa sa 
    fix Q::"'a cttobs list set"
    assume CT4s_healthy: "CT4s Q"
     and    CT3_healthy: "CT3 Q"
     and   CT2s_healthy: "CT2s Q"
     and    CT1_healthy: "CT1 Q"
    show "\<exists>t. prirelRef pa t [] sa (unCT1 Q)"
      using prirelRef.simps(1) by blast
  next
    fix pa 
    fix R::"'a cttevent set"
    fix S sa Q
    assume R_subset:"R \<subseteq> prirelrefSub pa S sa Q"
     and  CT4s_healthy: "CT4s Q"
     and   CT3_healthy: "CT3 Q"
     and  CT2s_healthy: "CT2s Q"
     and   CT1_healthy: "CT1 Q"
    then show "\<exists>t. [[R]\<^sub>R] \<lesssim>\<^sub>C t \<and>
           prirelRef pa t [[insert Tick (S \<union> {e. e \<noteq> Tock \<and> sa @ [[e]\<^sub>E] \<notin> Q \<or> e = Tock \<and> sa @ [[S]\<^sub>R, [Tock]\<^sub>E] \<notin> Q})]\<^sub>R] (mkCTMP sa [] Q) (unCT1 Q)"
    proof -
      from R_subset have "R \<subseteq> prirelrefSub pa S sa Q"
        by auto
      then have "R \<subseteq> prirelref pa (S \<union> {e. e \<noteq> Tock \<and> sa @ [[e]\<^sub>E] \<notin> Q \<or> e = Tock \<and> sa @ [[S]\<^sub>R, [Tock]\<^sub>E] \<notin> Q} \<union> {Tick})"
        using prirelref_prirelrefSub CT3_healthy by blast
      then have "[[R]\<^sub>R] \<lesssim>\<^sub>C [[prirelref pa (S \<union> {e. e \<noteq> Tock \<and> sa @ [[e]\<^sub>E] \<notin> Q \<or> e = Tock \<and> sa @ [[S]\<^sub>R, [Tock]\<^sub>E] \<notin> Q} \<union> {Tick})]\<^sub>R]"
        by auto
      then have "[[R]\<^sub>R] \<lesssim>\<^sub>C [[prirelref pa (S \<union> {e. e \<noteq> Tock \<and> sa @ [[e]\<^sub>E] \<notin> Q \<or> e = Tock \<and> sa @ [[S]\<^sub>R, [Tock]\<^sub>E] \<notin> Q} \<union> {Tick})]\<^sub>R] \<and>
                  prirelRef pa [[prirelref pa (S \<union> {e. e \<noteq> Tock \<and> sa @ [[e]\<^sub>E] \<notin> Q \<or> e = Tock \<and> sa @ [[S]\<^sub>R, [Tock]\<^sub>E] \<notin> Q} \<union> {Tick})]\<^sub>R]
                               [[insert Tick (S \<union> {e. e \<noteq> Tock \<and> sa @ [[e]\<^sub>E] \<notin> Q \<or> e = Tock \<and> sa @ [[S]\<^sub>R, [Tock]\<^sub>E] \<notin> Q})]\<^sub>R] (mkCTMP sa [] Q) (unCT1 Q)"
        by auto
      then show ?thesis by blast
    qed
  next
    fix pa 
    fix R S::"'a cttevent set"
    fix aa zz sa t::"'a cttobs list"
    fix Q::"'a cttobs list set"
    assume R_subset:"R \<subseteq> prirelrefSub pa S sa Q"
     and  CT4s_healthy: "CT4s Q"
     and   CT3_healthy: "CT3 Q"
     and  CT2s_healthy: "CT2s Q"
     and   CT1_healthy: "CT1 Q"
     and aa_prefix_t:"aa \<lesssim>\<^sub>C t"
     and prirelRef_assm:"prirelRef pa t (mkCTMP zz (sa @ [[S]\<^sub>R, [Tock]\<^sub>E]) Q) (mkCTMP (sa @ [[S]\<^sub>R, [Tock]\<^sub>E]) [] Q) (unCT1 Q)"
     and Tock_not_in:"Tock \<notin> prirelrefSub pa S sa Q"
     and "prirelRef2 pa aa zz (sa @ [[S]\<^sub>R, [Tock]\<^sub>E]) Q"
    then have CT4_healthy: "CT4 Q" 
      using CT4s_healthy CT1_healthy CT4s_CT1_imp_CT4 by blast
    then obtain Y where Y:"Y = (mkCTMP zz (sa @ [[S]\<^sub>R, [Tock]\<^sub>E]) Q)" by auto
    then show "\<exists>t. [R]\<^sub>R # [Tock]\<^sub>E # aa \<lesssim>\<^sub>C t \<and>
           prirelRef pa t
            ([insert Tick
               (S \<union> {e. e \<noteq> Tock \<and> sa @ [[e]\<^sub>E] \<notin> Q \<or> e = Tock \<and> sa @ [[S]\<^sub>R, [Tock]\<^sub>E] \<notin> Q})]\<^sub>R #
             [Tock]\<^sub>E # mkCTMP zz (sa @ [[S]\<^sub>R, [Tock]\<^sub>E]) Q)
            (mkCTMP sa [] Q) (unCT1 Q)"
    proof -
      obtain Z where Z:"Z = S \<union> {e. e \<noteq> Tock \<and> sa @ [[e]\<^sub>E] \<notin> Q \<or> e = Tock \<and> sa @ [[S]\<^sub>R, [Tock]\<^sub>E] \<notin> Q} \<union> {Tick}" by auto
      from R_subset Tock_not_in have "R \<subseteq> prirelrefSub pa S sa Q \<and> Tock \<notin> prirelrefSub pa S sa Q"
        by auto
      then have "R \<subseteq> prirelref pa Z \<and> Tock \<notin> prirelref pa Z"
        using prirelref_prirelrefSub CT3_healthy Z by blast
      then have "[R]\<^sub>R # [Tock]\<^sub>E # aa \<lesssim>\<^sub>C [prirelref pa Z]\<^sub>R # [Tock]\<^sub>E # t \<and> Tock \<notin> prirelref pa Z"
        using aa_prefix_t by auto
      then have "[R]\<^sub>R # [Tock]\<^sub>E # aa \<lesssim>\<^sub>C [prirelref pa Z]\<^sub>R # [Tock]\<^sub>E # t
            \<and> Tock \<notin> prirelref pa Z
            \<and> prirelRef pa t Y (mkCTMP (sa @ [[S]\<^sub>R, [Tock]\<^sub>E]) [] Q) (unCT1 Q)"
        using Y prirelRef_assm by auto
      then have "[R]\<^sub>R # [Tock]\<^sub>E # aa \<lesssim>\<^sub>C [prirelref pa Z]\<^sub>R # [Tock]\<^sub>E # t
            \<and> Tock \<notin> prirelref pa Z
            \<and> prirelRef pa ([prirelref pa Z]\<^sub>R # [Tock]\<^sub>E # t) 
                           ([Z]\<^sub>R # [Tock]\<^sub>E # Y) (mkCTMP sa [] Q) (unCT1 Q)"
      proof -
        have "prirelRef pa t Y (mkCTMP (sa @ [[S]\<^sub>R, [Tock]\<^sub>E]) [] Q) (unCT1 Q)"
             using \<open>[R]\<^sub>R # [Tock]\<^sub>E # aa \<lesssim>\<^sub>C [prirelref pa Z]\<^sub>R # [Tock]\<^sub>E # t \<and> Tock \<notin> prirelref pa Z \<and> prirelRef pa t Y (mkCTMP (sa @ [[S]\<^sub>R, [Tock]\<^sub>E]) [] Q) (unCT1 Q)\<close> by blast
        then have "prirelRef pa t Y ((mkCTMP sa [] Q) @ [[S \<union> {e. e \<noteq> Tock \<and> sa @ [[e]\<^sub>E] \<notin> Q \<or> e = Tock \<and> sa @ [[S]\<^sub>R, [Tock]\<^sub>E] \<notin> Q} \<union> {Tick}]\<^sub>R, [Tock]\<^sub>E]) (unCT1 Q)"
          (*using CT1_healthy CT2s_healthy CT4_healthy Y Z prirelRef_start_Ref_extends sledgehammer by fastforce*)
          using mkCTMP_absorb_Ref_Tock'
          by (smt Collect_cong append_Nil)
        then have "prirelRef pa t Y ((mkCTMP sa [] Q) @ [[Z]\<^sub>R, [Tock]\<^sub>E]) (unCT1 Q)"
          using Z by auto
        then have "prirelRef pa ([prirelref pa Z]\<^sub>R # [Tock]\<^sub>E # t) ([Z]\<^sub>R # [Tock]\<^sub>E # Y) (mkCTMP sa [] Q) (unCT1 Q)"
          using \<open>[R]\<^sub>R # [Tock]\<^sub>E # aa \<lesssim>\<^sub>C [prirelref pa Z]\<^sub>R # [Tock]\<^sub>E # t \<and> Tock \<notin> prirelref pa Z \<and> prirelRef pa t Y (mkCTMP (sa @ [[S]\<^sub>R, [Tock]\<^sub>E]) [] Q) (unCT1 Q)\<close> 
          by auto
        then show ?thesis
          using \<open>[R]\<^sub>R # [Tock]\<^sub>E # aa \<lesssim>\<^sub>C [prirelref pa Z]\<^sub>R # [Tock]\<^sub>E # t \<and> Tock \<notin> prirelref pa Z \<and> prirelRef pa t Y (mkCTMP (sa @ [[S]\<^sub>R, [Tock]\<^sub>E]) [] Q) (unCT1 Q)\<close> 
          by auto
      qed
      then have "[R]\<^sub>R # [Tock]\<^sub>E # aa \<lesssim>\<^sub>C [prirelref pa Z]\<^sub>R # [Tock]\<^sub>E # t \<and>
        prirelRef pa ([prirelref pa Z]\<^sub>R # [Tock]\<^sub>E # t)
         ([insert Tick
            (S \<union> {e. e \<noteq> Tock \<and> sa @ [[e]\<^sub>E] \<notin> Q \<or> e = Tock \<and> sa @ [[S]\<^sub>R, [Tock]\<^sub>E] \<notin> Q})]\<^sub>R #
          [Tock]\<^sub>E # mkCTMP zz (sa @ [[S]\<^sub>R, [Tock]\<^sub>E]) Q)
         (mkCTMP sa [] Q) (unCT1 Q)"
        using Z Y by auto
      then show ?thesis by blast
    qed
  next
    fix pa 
    fix aa zz::"'a cttobs list"
    fix e\<^sub>2 sa t 
    fix Q::"'a cttobs list set"
    assume 
        CT4s_healthy: "CT4s Q"
    and CT3_healthy:  "CT3 Q"
    and CT2s_healthy: "CT2s Q"
    and CT1_healthy:  "CT1 Q"
    and prirelRef2:   "prirelRef2 pa aa zz (sa @ [[e\<^sub>2]\<^sub>E]) Q"
    and maximal:      "maximal(pa,e\<^sub>2)"
    and subsetctt:    "aa \<lesssim>\<^sub>C t"
    and prirelRef:    "prirelRef pa t (mkCTMP zz (sa @ [[e\<^sub>2]\<^sub>E]) Q) (mkCTMP (sa @ [[e\<^sub>2]\<^sub>E]) [] Q) (unCT1 Q)"
    then show "\<exists>t. [e\<^sub>2]\<^sub>E # aa \<lesssim>\<^sub>C t \<and> prirelRef pa t ([e\<^sub>2]\<^sub>E # mkCTMP zz (sa @ [[e\<^sub>2]\<^sub>E]) Q) (mkCTMP sa [] Q) (unCT1 Q)"
    proof -
      from subsetctt have e2_aa_t:"[e\<^sub>2]\<^sub>E # aa \<lesssim>\<^sub>C [e\<^sub>2]\<^sub>E # t"
        by auto
      have "prirelRef pa t (mkCTMP zz (sa @ [[e\<^sub>2]\<^sub>E]) Q) (mkCTMP (sa @ [[e\<^sub>2]\<^sub>E]) [] Q) (unCT1 Q)"
        using prirelRef by auto
      then have "prirelRef pa ([e\<^sub>2]\<^sub>E # t) ([e\<^sub>2]\<^sub>E # mkCTMP zz (sa @ [[e\<^sub>2]\<^sub>E]) Q) (mkCTMP sa [] Q) (unCT1 Q)"
        using mkCTMP_absorb_event maximal
        by (simp add: mkCTMP_dist_concat)
      then have "[e\<^sub>2]\<^sub>E # aa \<lesssim>\<^sub>C [e\<^sub>2]\<^sub>E # t \<and> prirelRef pa ([e\<^sub>2]\<^sub>E # t) ([e\<^sub>2]\<^sub>E # mkCTMP zz (sa @ [[e\<^sub>2]\<^sub>E]) Q) (mkCTMP sa [] Q) (unCT1 Q)"
        using e2_aa_t by auto
      then have "\<exists>t. [e\<^sub>2]\<^sub>E # aa \<lesssim>\<^sub>C t \<and> prirelRef pa t ([e\<^sub>2]\<^sub>E # mkCTMP zz (sa @ [[e\<^sub>2]\<^sub>E]) Q) (mkCTMP sa [] Q) (unCT1 Q)"
        by blast
      then show ?thesis
        by blast
    qed
  next
    fix pa 
    fix aa zz::"'a cttobs list"
    fix e\<^sub>2 sa Z t
    fix Q::"'a cttobs list set"
    assume 
        CT4s_healthy: "CT4s Q"
    and CT3_healthy:  "CT3 Q"
    and CT2s_healthy: "CT2s Q"
    and CT1_healthy:  "CT1 Q"
    and prirelRef2:   "prirelRef2 pa aa zz (sa @ [[e\<^sub>2]\<^sub>E]) Q"
    and sa_Z:         "sa @ [[Z]\<^sub>R] \<in> Q"
(*    and CTMPick_sa:   "CTMPick sa [] Q"*)
    and events_in_Z:  "\<forall>e. e \<notin> Z \<and> e \<noteq> Tock \<longrightarrow> sa @ [[e]\<^sub>E] \<in> Q"
    and Tick_in_Z:    "Tick \<in> Z"
    and e2_not_in_Z:  "e\<^sub>2 \<notin> Z"
    and no_pri_Z:     "\<forall>b. b \<in> Z \<or> \<not> e\<^sub>2 <\<^sup>*pa b"
    and not_prirelRef:"\<forall>t. [e\<^sub>2]\<^sub>E # aa \<lesssim>\<^sub>C t \<longrightarrow> \<not> prirelRef pa t ([e\<^sub>2]\<^sub>E # mkCTMP zz (sa @ [[e\<^sub>2]\<^sub>E]) Q) (mkCTMP sa [] Q) (unCT1 Q)"
    and Tock_in_Z:    "Tock \<in> Z"
    and subsetctt:    "aa \<lesssim>\<^sub>C t"
    and prirelRef:    "prirelRef pa t (mkCTMP zz (sa @ [[e\<^sub>2]\<^sub>E]) Q) (mkCTMP (sa @ [[e\<^sub>2]\<^sub>E]) [] Q) (unCT1 Q)"
    then show "False"
   proof -
      from subsetctt have e2_aa_t:"[e\<^sub>2]\<^sub>E # aa \<lesssim>\<^sub>C [e\<^sub>2]\<^sub>E # t"
        by auto

      have CT4_healthy:"CT4 Q"
        using CT1_healthy CT4s_healthy 
        by (simp add: CT4s_CT1_imp_CT4)

      have a:"(sa @ [[Z]\<^sub>R] \<in> Q \<and> e\<^sub>2 \<notin> Z \<and> \<not>(\<exists>b. b \<notin> Z \<and> e\<^sub>2 <\<^sup>*pa b)
          \<and> (\<forall>e. e \<notin> Z \<and> e \<noteq> Tock \<longrightarrow> sa @ [[e]\<^sub>E] \<in> Q)
          \<and> (Tock \<notin> Z \<longrightarrow> sa @ [[Z]\<^sub>R,[Tock]\<^sub>E] \<in> Q) \<and> Tick \<in> Z)"
        using  Tick_in_Z e2_not_in_Z events_in_Z no_pri_Z sa_Z Tock_in_Z by blast
      
      then have "(mkCTMP sa [] Q) \<in> Q"
        by (meson CT1_def CT1_healthy CT2s_healthy CT3_healthy CT4s_healthy CTs_mkCTMP_in_P ctt_prefix_subset_front ctt_prefix_subset_refl)
      then have b:"(mkCTMP sa [] Q) @ [[Z]\<^sub>R] \<in> unCT1 Q \<and> e\<^sub>2 \<notin> Z \<and> \<not>(\<exists>b. b \<notin> Z \<and> e\<^sub>2 <\<^sup>*pa b)"
        using a CT1_healthy CT4_healthy  
        by (simp add: prirelRef_unCT1_case_specific CT2s_healthy CT3_healthy CT4s_healthy mkCTMP_in_P)
        (* FIXME: Key result to prove *)
      have "prirelRef pa t (mkCTMP zz (sa @ [[e\<^sub>2]\<^sub>E]) Q) (mkCTMP (sa @ [[e\<^sub>2]\<^sub>E]) [] Q) (unCT1 Q)"
        using prirelRef by auto
      then have "prirelRef pa t (mkCTMP zz (sa @ [[e\<^sub>2]\<^sub>E]) Q) ((mkCTMP sa [] Q) @ [[e\<^sub>2]\<^sub>E]) (unCT1 Q)"
        by (simp add: mkCTMP_dist_concat)
      then have prirelRef_pa_t:"prirelRef pa ([e\<^sub>2]\<^sub>E # t) ([e\<^sub>2]\<^sub>E # mkCTMP zz (sa @ [[e\<^sub>2]\<^sub>E]) Q) (mkCTMP sa [] Q) (unCT1 Q)"
        using prirelRef sa_Z e2_not_in_Z events_in_Z b by auto
      then have "[e\<^sub>2]\<^sub>E # aa \<lesssim>\<^sub>C [e\<^sub>2]\<^sub>E # t"
        using subsetctt by auto
      then have not_prirelRef_pa_t:"\<not> prirelRef pa ([e\<^sub>2]\<^sub>E # t) ([e\<^sub>2]\<^sub>E # mkCTMP zz (sa @ [[e\<^sub>2]\<^sub>E]) Q) (mkCTMP sa [] Q) (unCT1 Q)"
        using not_prirelRef by blast
      then show ?thesis
        using prirelRef_pa_t not_prirelRef_pa_t by auto
    qed
  next
    fix pa 
    fix aa zz::"'a cttobs list"
    fix e\<^sub>2 sa t Z
    fix Q::"'a cttobs list set"
    assume 
        CT4s_healthy: "CT4s Q"
    and CT3_healthy:  "CT3 Q"
    and CT2s_healthy: "CT2s Q"
    and CT1_healthy:  "CT1 Q"
    and prirelRef2:   "prirelRef2 pa aa zz (sa @ [[e\<^sub>2]\<^sub>E]) Q"
    and sa_Z:         "sa @ [[Z]\<^sub>R] \<in> Q"
  (*  and CTMPick_sa:   "CTMPick sa [] Q"*)
    and e2_not_in_Z:   "e\<^sub>2 \<notin> Z"
    and nohigherpri:  "\<forall>b. b \<in> Z \<or> \<not> e\<^sub>2 <\<^sup>*pa b"
    and subsetctt:    "aa \<lesssim>\<^sub>C t"
    and events_in_Z:  "\<forall>e. e \<notin> Z \<and> e \<noteq> Tock \<longrightarrow> sa @ [[e]\<^sub>E] \<in> Q"
    and Tick_in_Z:    "Tick \<in> Z"
    and Tock_Z_in_Q:  "sa @ [[Z]\<^sub>R, [Tock]\<^sub>E] \<in> Q"
    and prirelRef:    "prirelRef pa t (mkCTMP zz (sa @ [[e\<^sub>2]\<^sub>E]) Q) (mkCTMP (sa @ [[e\<^sub>2]\<^sub>E]) [] Q) (unCT1 Q)"
    then show "\<exists>t. [e\<^sub>2]\<^sub>E # aa \<lesssim>\<^sub>C t \<and> prirelRef pa t ([e\<^sub>2]\<^sub>E # mkCTMP zz (sa @ [[e\<^sub>2]\<^sub>E]) Q) (mkCTMP sa [] Q) (unCT1 Q)"
    proof -
      from subsetctt have e2_aa_t:"[e\<^sub>2]\<^sub>E # aa \<lesssim>\<^sub>C [e\<^sub>2]\<^sub>E # t"
        by auto

      have CT4_healthy:"CT4 Q"
        using CT1_healthy CT4s_healthy 
        by (simp add: CT4s_CT1_imp_CT4)

      have a:"(sa @ [[Z]\<^sub>R] \<in> Q  \<and> e\<^sub>2 \<notin> Z \<and> \<not>(\<exists>b. b \<notin> Z \<and> e\<^sub>2 <\<^sup>*pa b)
          \<and> (\<forall>e. e \<notin> Z \<and> e \<noteq> Tock \<longrightarrow> sa @ [[e]\<^sub>E] \<in> Q)
          \<and> (Tock \<notin> Z \<longrightarrow> sa @ [[Z]\<^sub>R,[Tock]\<^sub>E] \<in> Q) \<and> Tick \<in> Z)"
        by (simp add:  Tick_in_Z Tock_Z_in_Q e2_not_in_Z events_in_Z nohigherpri sa_Z)
      then have "(mkCTMP sa [] Q) \<in> Q"
        by (meson CT1_def CT1_healthy CT2s_healthy CT3_healthy CT4s_healthy CTs_mkCTMP_in_P ctt_prefix_subset_front ctt_prefix_subset_refl)
      then have b:"(mkCTMP sa [] Q) @ [[Z]\<^sub>R] \<in> unCT1 Q \<and> e\<^sub>2 \<notin> Z \<and> \<not>(\<exists>b. b \<notin> Z \<and> e\<^sub>2 <\<^sup>*pa b)"
        using a CT1_healthy CT4_healthy  
        by (simp add: prirelRef_unCT1_case_specific CT2s_healthy CT3_healthy CT4s_healthy mkCTMP_in_P)
      have "prirelRef pa t (mkCTMP zz (sa @ [[e\<^sub>2]\<^sub>E]) Q) (mkCTMP (sa @ [[e\<^sub>2]\<^sub>E]) [] Q) (unCT1 Q)"
        using prirelRef by auto
      then have "prirelRef pa t (mkCTMP zz (sa @ [[e\<^sub>2]\<^sub>E]) Q) ((mkCTMP sa [] Q) @ [[e\<^sub>2]\<^sub>E]) (unCT1 Q)"
        by (simp add: mkCTMP_dist_concat)
      then have prirelRef_pa_t:"prirelRef pa ([e\<^sub>2]\<^sub>E # t) ([e\<^sub>2]\<^sub>E # mkCTMP zz (sa @ [[e\<^sub>2]\<^sub>E]) Q) (mkCTMP sa [] Q) (unCT1 Q)"
        using prirelRef sa_Z e2_not_in_Z events_in_Z b by auto
      then have "[e\<^sub>2]\<^sub>E # aa \<lesssim>\<^sub>C [e\<^sub>2]\<^sub>E # t \<and> prirelRef pa ([e\<^sub>2]\<^sub>E # t) ([e\<^sub>2]\<^sub>E # mkCTMP zz (sa @ [[e\<^sub>2]\<^sub>E]) Q) (mkCTMP sa [] Q) (unCT1 Q)"
        using subsetctt by auto
      then show ?thesis by blast
    qed
  qed
  
  finally show ?thesis by auto
qed

lemma prirelref_imp_subseteq_prirelrefSub:
  assumes "Z \<subseteq> prirelref pa S" "Tick \<in> S" "Tock \<in> S" "\<forall>e. e \<notin> S \<and> e \<noteq> Tock \<longrightarrow> sa @ [[e]\<^sub>E] \<in> Q" "CT3 Q"
  shows "Z \<subseteq> prirelrefSub pa S sa Q"
proof -
  have "S = S \<union> {e. e \<noteq> Tock \<and> sa @ [[e]\<^sub>E] \<notin> Q \<or> e = Tock \<and> sa @ [[S]\<^sub>R, [Tock]\<^sub>E] \<notin> Q} \<union> {Tick}"
    using assms by auto
  then have "prirelref pa S = prirelrefSub pa S sa Q"
    using assms prirelref_prirelrefSub by (metis (mono_tags, lifting))
  then show ?thesis using assms by auto
qed

lemma prirelref_imp_subseteq_prirelrefSub':
  assumes "Z \<subseteq> prirelref pa S" "Tick \<in> S" "sa @ [[S]\<^sub>R, [Tock]\<^sub>E] \<in> Q" "\<forall>e. e \<notin> S \<and> e \<noteq> Tock \<longrightarrow> sa @ [[e]\<^sub>E] \<in> Q" "CT3 Q"
  shows "Z \<subseteq> prirelrefSub pa S sa Q"
proof -
  have "S = S \<union> {e. e \<noteq> Tock \<and> sa @ [[e]\<^sub>E] \<notin> Q \<or> e = Tock \<and> sa @ [[S]\<^sub>R, [Tock]\<^sub>E] \<notin> Q} \<union> {Tick}"
    using assms by auto
  then have "prirelref pa S = prirelrefSub pa S sa Q"
    using assms prirelref_prirelrefSub by (metis (mono_tags, lifting))
  then show ?thesis using assms by auto
qed

lemma prirelref_imp_eq_prirelrefSub':
  assumes "Tick \<in> S" "sa @ [[S]\<^sub>R, [Tock]\<^sub>E] \<in> Q" "\<forall>e. e \<notin> S \<and> e \<noteq> Tock \<longrightarrow> sa @ [[e]\<^sub>E] \<in> Q" "CT3 Q"
  shows "prirelref pa S = prirelrefSub pa S sa Q"
proof -
  have "S = S \<union> {e. e \<noteq> Tock \<and> sa @ [[e]\<^sub>E] \<notin> Q \<or> e = Tock \<and> sa @ [[S]\<^sub>R, [Tock]\<^sub>E] \<notin> Q} \<union> {Tick}"
    using assms by auto
  then have "prirelref pa S = prirelrefSub pa S sa Q"
    using assms prirelref_prirelrefSub by (metis (mono_tags, lifting))
  then show ?thesis using assms by auto
qed

lemma prirelRef_imp_prirelRef2:
  assumes "x \<lesssim>\<^sub>C t" "CTMPick s i P" "prirelRef p t s i (unCT1 P)" "CT4s P" "CT3 P" "CT2s P" "CT1 P"
  shows "\<exists>z. prirelRef2 p x z i P \<and> z \<lesssim>\<^sub>C s"
  using assms 
proof (induct p t s i P arbitrary:x rule:prirelRef.induct, auto)
  fix pa sa Q 
  fix xa::"'a cttobs list"
  assume "xa \<lesssim>\<^sub>C []"
  then show "\<exists>z. prirelRef2 pa xa z sa Q \<and> z \<lesssim>\<^sub>C []"
    apply (cases xa, auto)
    by (rule_tac x="[]" in exI, auto)
next
  fix pa S sa Q
  fix xa::"'a cttobs list"
  assume 
      prirelref:    "xa \<lesssim>\<^sub>C [[prirelref pa S]\<^sub>R]"
  and events_in_Q:  "\<forall>e. e \<notin> S \<and> e \<noteq> Tock \<longrightarrow> sa @ [[e]\<^sub>E] \<in> Q"
  and Tick_in_S:    "Tick \<in> S"
  and prirelRef2:   "\<forall>z. prirelRef2 pa xa z sa Q \<longrightarrow> \<not> z \<lesssim>\<^sub>C [[S]\<^sub>R]"
  and Tock_in_S:    "Tock \<in> S"
  and  CT4s_healthy: "CT4s Q"
  and   CT3_healthy: "CT3 Q"
  and  CT2s_healthy: "CT2s Q"
  and   CT1_healthy: "CT1 Q"
  then show "False"
  proof(cases xa)
    case Nil
    then show ?thesis
      using ctt_prefix_subset.simps(1) prirelRef2 prirelRef2.simps(1) by blast
  next
    case (Cons a list)
    then obtain Z where "a = [Z]\<^sub>R"
      using ctt_prefix_subset.elims(2) prirelref by blast
    then have "[Z]\<^sub>R # list \<lesssim>\<^sub>C [[prirelref pa S]\<^sub>R]"
      using prirelref Cons by auto
    then have "list = []"
              "Z \<subseteq> prirelref pa S"
      using ctt_prefix_subset.simps(1) ctt_prefix_subset_antisym init_refusal_ctt_prefix_subset apply blast
      using \<open>a = [Z]\<^sub>R\<close> local.Cons prirelref by auto
    then have "prirelRef2 pa [[Z]\<^sub>R] [[S]\<^sub>R] sa Q"
      apply auto
      by (meson CT3_healthy Tick_in_S Tock_in_S events_in_Q prirelref_imp_subseteq_prirelrefSub subset_iff)
    then have "\<not> [[S]\<^sub>R] \<lesssim>\<^sub>C [[S]\<^sub>R]"
      using prirelRef2 Cons \<open>a = [Z]\<^sub>R\<close> \<open>list = []\<close> by blast
    then show ?thesis by auto
  qed
next
  fix pa S sa Q
  fix xa::"'a cttobs list"
  assume 
      prirelref:     "xa \<lesssim>\<^sub>C [[prirelref pa S]\<^sub>R]"
  and events_in_Q:   "\<forall>e. e \<notin> S \<and> e \<noteq> Tock \<longrightarrow> sa @ [[e]\<^sub>E] \<in> Q"
  and Tick_in_S:     "Tick \<in> S"
  and Tock_in_Q:     "sa @ [[S]\<^sub>R, [Tock]\<^sub>E] \<in> Q"
  and  CT4s_healthy: "CT4s Q"
  and   CT3_healthy: "CT3 Q"
  and  CT2s_healthy: "CT2s Q"
  and   CT1_healthy: "CT1 Q"
  then show "\<exists>z. prirelRef2 pa xa z sa Q \<and> z \<lesssim>\<^sub>C [[S]\<^sub>R]"
  proof(cases xa)
    case Nil
    then show ?thesis
      using ctt_prefix_subset.simps(1) prirelRef2.simps(1) by blast
  next
    case (Cons a list)
    then obtain Z where "a = [Z]\<^sub>R"
      using ctt_prefix_subset.elims(2) prirelref by blast
    then have "[Z]\<^sub>R # list \<lesssim>\<^sub>C [[prirelref pa S]\<^sub>R]"
      using prirelref Cons by auto
    then have "list = []"
              "Z \<subseteq> prirelref pa S"
      using ctt_prefix_subset.simps(1) ctt_prefix_subset_antisym init_refusal_ctt_prefix_subset apply blast
      using \<open>a = [Z]\<^sub>R\<close> local.Cons prirelref by auto
    then have "prirelRef2 pa [[Z]\<^sub>R] [[S]\<^sub>R] sa Q"
      apply auto
      by (meson CT3_healthy Tick_in_S events_in_Q Tock_in_Q prirelref_imp_subseteq_prirelrefSub' subset_iff)
    then have "prirelRef2 pa [[Z]\<^sub>R] [[S]\<^sub>R] sa Q \<and> [[S]\<^sub>R] \<lesssim>\<^sub>C [[S]\<^sub>R]"
      by auto
    then show ?thesis using Cons \<open>a = [Z]\<^sub>R\<close> \<open>list = []\<close> by blast
  qed
next
  fix pa aa S zz sa Q
  fix xa::"'a cttobs list"
  assume
      hyp:          "(\<And>x. x \<lesssim>\<^sub>C aa \<Longrightarrow> \<exists>z. prirelRef2 pa x z (sa @ [[S]\<^sub>R, [Tock]\<^sub>E]) Q \<and> z \<lesssim>\<^sub>C zz)"
  and xa_aa:        "xa \<lesssim>\<^sub>C [prirelref pa S]\<^sub>R # [Tock]\<^sub>E # aa"
  and CT4s_healthy: "CT4s Q"
  and CT3_healthy:  "CT3 Q"
  and CT2s_healthy: "CT2s Q"
  and CT1_healthy:  "CT1 Q"
  and events_in_Q:  "\<forall>e. e \<notin> S \<and> e \<noteq> Tock \<longrightarrow> sa @ [[e]\<^sub>E] \<in> Q"
  and Tock_not_in_p:"Tock \<notin> prirelref pa S"
  and prirelRef:    "prirelRef pa aa zz (sa @ [[S]\<^sub>R, [Tock]\<^sub>E]) (unCT1 Q)"
  and Tick_in_S:    "Tick \<in> S" 
  and CTMPick_zz:   "CTMPick zz (sa @ [[S]\<^sub>R, [Tock]\<^sub>E]) Q" 
  and hyp_False:    "\<forall>z. prirelRef2 pa xa z sa Q \<longrightarrow> \<not> z \<lesssim>\<^sub>C [S]\<^sub>R # [Tock]\<^sub>E # zz" 
  and Tock_in_S:    "Tock \<in> S"
  then show "False"
  proof (cases xa)
    case Nil
    then show ?thesis
      using ctt_prefix_subset.simps(1) hyp_False prirelRef2.simps(1) by blast
  next
    case a_list:(Cons a list)
    then have "xa = a # list"
      by auto
    then show ?thesis
    proof (cases a)
      case (ObsEvent x1)
      then show ?thesis
        using ctt_prefix_subset.simps(4) a_list xa_aa by blast
    next
      case (Ref x2)
      then show ?thesis 
      proof (cases list)
        case Nil
        then have xa:"xa = [[x2]\<^sub>R]"
          using a_list Ref by simp
        then have "[[x2]\<^sub>R] \<lesssim>\<^sub>C [prirelref pa S]\<^sub>R # [Tock]\<^sub>E # aa"
          using Cons xa_aa by auto
        then have "prirelRef2 pa xa [[S]\<^sub>R] sa Q"
          by (simp add: xa CT3_healthy Tick_in_S Tock_in_S events_in_Q prirelref_imp_subseteq_prirelrefSub)
        then have "\<not> [[S]\<^sub>R] \<lesssim>\<^sub>C [S]\<^sub>R # [Tock]\<^sub>E # zz"
          using hyp_False by auto
        then show ?thesis by auto
      next
        case (Cons b list')
        then have "xa = [x2]\<^sub>R # b # list'"
          using a_list Cons Ref by auto
        then have xa:"xa = [x2]\<^sub>R # [Tock]\<^sub>E # list'"
          using xa_aa
          by (metis ctt_prefix_subset.simps(3) ctt_prefix_subset.simps(5) cttobs.exhaust init_refusal_ctt_prefix_subset)
        then have "[x2]\<^sub>R # [Tock]\<^sub>E # list' \<lesssim>\<^sub>C [prirelref pa S]\<^sub>R # [Tock]\<^sub>E # aa"
          using Cons xa_aa by auto
        then have "list' \<lesssim>\<^sub>C aa"
          by auto
        then have "\<exists>z. prirelRef2 pa list' z (sa @ [[S]\<^sub>R, [Tock]\<^sub>E]) Q \<and> z \<lesssim>\<^sub>C zz"
          using hyp by auto
        then have "prirelRef2 pa ([x2]\<^sub>R # [Tock]\<^sub>E # list') ([S]\<^sub>R # [Tock]\<^sub>E # aa) sa Q"
          using Tock_in_S Tock_not_in_p prirelref_def by auto
        then have "\<not> [S]\<^sub>R # [Tock]\<^sub>E # aa \<lesssim>\<^sub>C [S]\<^sub>R # [Tock]\<^sub>E # zz"
          using xa hyp_False by blast
        then show ?thesis
          using Tock_in_S Tock_not_in_p prirelref_def by auto
      qed
    qed
  qed
next
  fix pa aa S zz sa Q
  fix xa::"'a cttobs list"
  assume
      hyp:          "(\<And>x. x \<lesssim>\<^sub>C aa \<Longrightarrow> \<exists>z. prirelRef2 pa x z (sa @ [[S]\<^sub>R, [Tock]\<^sub>E]) Q \<and> z \<lesssim>\<^sub>C zz)"
  and xa_aa:        "xa \<lesssim>\<^sub>C [prirelref pa S]\<^sub>R # [Tock]\<^sub>E # aa"
  and CT4s_healthy: "CT4s Q"
  and CT3_healthy:  "CT3 Q"
  and CT2s_healthy: "CT2s Q"
  and CT1_healthy:  "CT1 Q"
  and events_in_Q:  "\<forall>e. e \<notin> S \<and> e \<noteq> Tock \<longrightarrow> sa @ [[e]\<^sub>E] \<in> Q"
  and Tock_not_in_p:"Tock \<notin> prirelref pa S"
  and prirelRef:    "prirelRef pa aa zz (sa @ [[S]\<^sub>R, [Tock]\<^sub>E]) (unCT1 Q)"
  and Tick_in_S:    "Tick \<in> S" 
  and CTMPick_zz:   "CTMPick zz (sa @ [[S]\<^sub>R, [Tock]\<^sub>E]) Q" 
  and Tock_in_S:    "sa @ [[S]\<^sub>R, [Tock]\<^sub>E] \<in> Q"
  then show "\<exists>z. prirelRef2 pa xa z sa Q \<and> z \<lesssim>\<^sub>C [S]\<^sub>R # [Tock]\<^sub>E # zz"
  proof (cases xa)
    case Nil
    then show ?thesis
      using ctt_prefix_subset.simps(1) prirelRef2.simps(1) by blast
  next
    case a_list:(Cons a list)
    then have "xa = a # list"
      by auto
    then show ?thesis
    proof (cases a)
      case (ObsEvent x1)
      then show ?thesis
        using ctt_prefix_subset.simps(4) a_list xa_aa by blast
    next
      case (Ref x2)
      then show ?thesis 
      proof (cases list)
        case Nil
        then have xa:"xa = [[x2]\<^sub>R]"
          using a_list Ref by simp
        then have "[[x2]\<^sub>R] \<lesssim>\<^sub>C [prirelref pa S]\<^sub>R # [Tock]\<^sub>E # aa"
          using Cons xa_aa by auto
        then have "prirelRef2 pa xa [[S]\<^sub>R] sa Q"
          by (simp add: CT3_healthy Tick_in_S Tock_in_S events_in_Q prirelref_imp_subseteq_prirelrefSub' xa)
        then show ?thesis by auto
      next
        case (Cons b list')
        then have "xa = [x2]\<^sub>R # b # list'"
          using a_list Cons Ref by auto
        then have xa:"xa = [x2]\<^sub>R # [Tock]\<^sub>E # list'"
          using xa_aa
          by (metis ctt_prefix_subset.simps(3) ctt_prefix_subset.simps(5) cttobs.exhaust init_refusal_ctt_prefix_subset)
        then have list'_aa:"[x2]\<^sub>R # [Tock]\<^sub>E # list' \<lesssim>\<^sub>C [prirelref pa S]\<^sub>R # [Tock]\<^sub>E # aa"
          using Cons xa_aa by auto
        then have x2_subset:"x2 \<subseteq> prirelrefSub pa S sa Q"
          by (simp add: CT3_healthy Tick_in_S Tock_in_S events_in_Q prirelref_imp_subseteq_prirelrefSub')
        then have Tock_not_in_prirelrefSub:"Tock \<notin> prirelrefSub pa S sa Q"
          using Tock_not_in_p prirelref_imp_eq_prirelrefSub' CT3_healthy Tick_in_S Tock_in_S events_in_Q by blast
        then have "list' \<lesssim>\<^sub>C aa"
          using list'_aa by auto
        then have "\<exists>z. prirelRef2 pa list' z (sa @ [[S]\<^sub>R, [Tock]\<^sub>E]) Q \<and> z \<lesssim>\<^sub>C zz"
          using hyp by auto
        then have "\<exists>z. prirelRef2 pa ([x2]\<^sub>R # [Tock]\<^sub>E # list') ([S]\<^sub>R # [Tock]\<^sub>E # z) sa Q \<and> ([S]\<^sub>R # [Tock]\<^sub>E # z) \<lesssim>\<^sub>C [S]\<^sub>R # [Tock]\<^sub>E # zz"
          using x2_subset Tock_not_in_p Tock_not_in_prirelrefSub by auto
        then show ?thesis using xa by blast
      qed
    qed
  qed
next
  fix pa aa e\<^sub>2 zz sa Q
  fix xa::"'a cttobs list"
  assume
      hyp:          "(\<And>x. x \<lesssim>\<^sub>C aa \<Longrightarrow> \<exists>z. prirelRef2 pa x z (sa @ [[e\<^sub>2]\<^sub>E]) Q \<and> z \<lesssim>\<^sub>C zz)"
  and xa_aa:        "xa \<lesssim>\<^sub>C [e\<^sub>2]\<^sub>E # aa"
  and CTMPick:      "CTMPick zz (sa @ [[e\<^sub>2]\<^sub>E]) Q"
  and CT4s_healthy: "CT4s Q"
  and CT3_healthy:  "CT3 Q"
  and CT2s_healthy: "CT2s Q"
  and CT1_healthy:  "CT1 Q"
  and prirelRef:    "prirelRef pa aa zz (sa @ [[e\<^sub>2]\<^sub>E]) (unCT1 Q)"
  and maximal:      "maximal(pa,e\<^sub>2)"
  then show "\<exists>z. prirelRef2 pa xa z sa Q \<and> z \<lesssim>\<^sub>C [e\<^sub>2]\<^sub>E # zz"
  proof (cases xa)
    case Nil
    then show ?thesis
      using ctt_prefix_subset.simps(1) prirelRef2.simps(1) by blast
  next
    case a_list:(Cons a list)
    then have "xa = a # list"
      by auto
    then show ?thesis
      proof (cases a)
        case (ObsEvent x1)
        then have xa:"xa = [x1]\<^sub>E # list"
           using a_list ObsEvent by simp
        then have x1_list_subsetctt:"[x1]\<^sub>E # list \<lesssim>\<^sub>C [e\<^sub>2]\<^sub>E # aa"
           using Cons xa_aa by auto
        then have "x1 = e\<^sub>2" and xa_e2:"xa = [e\<^sub>2]\<^sub>E # list"
           using xa by auto+
        then have "\<exists>z. prirelRef2 pa list z (sa @ [[e\<^sub>2]\<^sub>E]) Q \<and> z \<lesssim>\<^sub>C zz"
           using hyp x1_list_subsetctt by auto
        then have "\<exists>z. prirelRef2 pa ([e\<^sub>2]\<^sub>E # list) ([e\<^sub>2]\<^sub>E # z) sa Q \<and> [e\<^sub>2]\<^sub>E # z \<lesssim>\<^sub>C [e\<^sub>2]\<^sub>E # zz"
           using maximal by auto
           then show ?thesis using xa_e2 ctt_prefix_subset.simps(1) ctt_prefix_subset.simps(3) by blast
      next
        case (Ref x2)
        then show ?thesis
          using a_list xa_aa by auto
      qed
    qed
next
  fix pa aa e\<^sub>2 zz sa Q Z
  fix xa::"'a cttobs list"
  assume
      hyp:          "(\<And>x. x \<lesssim>\<^sub>C aa \<Longrightarrow> \<exists>z. prirelRef2 pa x z (sa @ [[e\<^sub>2]\<^sub>E]) Q \<and> z \<lesssim>\<^sub>C zz)"
  and xa_aa:        "xa \<lesssim>\<^sub>C [e\<^sub>2]\<^sub>E # aa"
  and CTMPick:      "CTMPick zz (sa @ [[e\<^sub>2]\<^sub>E]) Q"
  and CT4s_healthy: "CT4s Q"
  and CT3_healthy:  "CT3 Q"
  and CT2s_healthy: "CT2s Q"
  and CT1_healthy:  "CT1 Q"
  and prirelRef:    "prirelRef pa aa zz (sa @ [[e\<^sub>2]\<^sub>E]) (unCT1 Q)"
  and Z_in_Q:       "sa @ [[Z]\<^sub>R] \<in> unCT1 Q"
  and e2_not_in_Z:  "e\<^sub>2 \<notin> Z"
  and no_higher_pri:"\<forall>b. b \<in> Z \<or> \<not> e\<^sub>2 <\<^sup>*pa b"
  then show "\<exists>z. prirelRef2 pa xa z sa Q \<and> z \<lesssim>\<^sub>C [e\<^sub>2]\<^sub>E # zz"
  proof (cases xa)
    case Nil
    then show ?thesis using ctt_prefix_subset.simps(1) prirelRef2.simps(1) by blast
  next
    case a_list:(Cons a list)
    then have "xa = a # list"
      by auto
    then show ?thesis
      proof (cases a)
        case (ObsEvent x1)
        then have xa:"xa = [x1]\<^sub>E # list"
           using a_list ObsEvent by simp
        then have x1_list_subsetctt:"[x1]\<^sub>E # list \<lesssim>\<^sub>C [e\<^sub>2]\<^sub>E # aa"
           using Cons xa_aa by auto
        then have "x1 = e\<^sub>2" and xa_e2:"xa = [e\<^sub>2]\<^sub>E # list"
           using xa by auto+
        then have exists_prirelRef2:"\<exists>z. prirelRef2 pa list z (sa @ [[e\<^sub>2]\<^sub>E]) Q \<and> z \<lesssim>\<^sub>C zz"
          using hyp x1_list_subsetctt by auto
        then have "\<exists>z. prirelRef2 pa ([e\<^sub>2]\<^sub>E # list) ([e\<^sub>2]\<^sub>E # z) sa Q \<and> [e\<^sub>2]\<^sub>E # z \<lesssim>\<^sub>C [e\<^sub>2]\<^sub>E # zz"
        proof -
          have CT4_healthy:"CT4 Q"
            using CT1_healthy CT4s_healthy 
            by (simp add: CT4s_CT1_imp_CT4)
          have "(sa @ [[Z]\<^sub>R] \<in> unCT1 Q \<and> e\<^sub>2 \<notin> Z \<and> \<not>(\<exists>b. b \<notin> Z \<and> e\<^sub>2 <\<^sup>*pa b))"
            using Z_in_Q e2_not_in_Z no_higher_pri by blast
          then have "(sa @ [[Z]\<^sub>R] \<in> Q \<and> CTMPick sa [] Q \<and> e\<^sub>2 \<notin> Z \<and> \<not>(\<exists>b. b \<notin> Z \<and> e\<^sub>2 <\<^sup>*pa b)
                      \<and> (\<forall>e. e \<notin> Z \<and> e \<noteq> Tock \<longrightarrow> sa @ [[e]\<^sub>E] \<in> Q)
                      \<and> (Tock \<notin> Z \<longrightarrow> sa @ [[Z]\<^sub>R,[Tock]\<^sub>E] \<in> Q) \<and> Tick \<in> Z)"
            using CT1_healthy CT4_healthy prirelRef_unCT1_case by blast
          then show ?thesis using exists_prirelRef2
            by auto
        qed
        then show ?thesis using xa_e2
          by blast
      next
        case (Ref x2)
        then show ?thesis using a_list xa_aa by auto
      qed
  qed
qed

definition priCT :: "('e cttevent) partialorder \<Rightarrow> ('e cttobs) list set \<Rightarrow> ('e cttobs) list set" where
"priCT p P = {\<rho>|\<rho> s. prirelRef2 p \<rho> s [] P \<and> s \<in> P}"

lemma mkCT1_priNS_unCT1_priCT:
  assumes "CT1 P" "CT4 P" "CT4s P" "CT3 P" "CT2s P"
  shows "mkCT1 (priNS p (unCT1 P)) = priCT p P"
proof -
  have "mkCT1 (priNS p (unCT1 P)) = mkCT1 ({t|s t. s \<in> (unCT1 P) \<and> prirelRef p t s [] (unCT1 P)})"
    unfolding priNS_def by auto
  also have "... = ({\<rho>|\<rho> s t. \<rho> \<lesssim>\<^sub>C t \<and> s \<in> (unCT1 P) \<and> prirelRef p t s [] (unCT1 P)})"
    by (auto simp add:mkCT1_simp)
  also have "... = ({\<rho>|\<rho> s t. \<rho> \<lesssim>\<^sub>C t 
                          \<and> s \<in> (\<Union>{x. CTM2a x \<and> CTM2b x \<and> CTTickAll x \<and> CT1c x \<and> (mkCT1 x) \<subseteq> P}) 
                          \<and> prirelRef p t s [] (unCT1 P)})"
    unfolding unCT1_def by auto
  also have "... = ({\<rho>|\<rho> s t. \<rho> \<lesssim>\<^sub>C t 
                          \<and> (\<exists>x. s \<in> x \<and> CTM2a x \<and> CTM2b x \<and> CTTickAll x \<and> CT1c x \<and> (mkCT1 x) \<subseteq> P)
                          \<and> prirelRef p t s [] (unCT1 P)})"
    by auto
  also have "... = ({\<rho>|\<rho> s t. \<rho> \<lesssim>\<^sub>C t 
                          \<and> s \<in> P \<and> CTTickAll {s} \<and> CTMPick s [] P
                          \<and> prirelRef p t s [] (unCT1 P)})"
    apply auto
    using assms CTTickAll_mkCT1_simp
    apply (metis (mono_tags, lifting))
    by (metis (mono_tags, lifting) CTTickAll_mkCT1_simp assms(1) assms(2))
  also have "... = ({\<rho>|\<rho> s t. \<rho> \<lesssim>\<^sub>C t 
                          \<and> s \<in> P \<and> CTMPick s [] P
                          \<and> prirelRef p t s [] (unCT1 P)})"
    using CTTickAll_CTMPick by auto
  also have "... = ({\<rho>|\<rho> s. prirelRef2 p \<rho> s [] P \<and> s \<in> P})"
    using assms apply auto
     apply (meson CT1_def prirelRef_imp_prirelRef2)
    using CTs_mkCTMP_in_P prirelRef2_CTMPick_imp_prirelRef by fastforce
  finally show ?thesis unfolding priCT_def by auto
qed

(* Redundant stuff below? *)

lemma CTTick_Nil [simp]:
  "CTTick {[]}"
  unfolding CTTick_def by auto

lemma CTTick_Refusal_Tock [simp]:
  assumes "CTTick {saa}"
  shows "CTTick {[S]\<^sub>R # [Tock]\<^sub>E # saa}"
  using assms unfolding CTTick_def apply auto                               
  by (metis (no_types, hide_lams) append.left_neutral append1_eq_conv append_Cons cttobs.distinct(1) rev_exhaust)                            

lemma CTTick_Refusal_Tock':
  assumes "CTTick {[S]\<^sub>R # [Tock]\<^sub>E # saa}"
  shows "CTTick {saa}"
  using assms unfolding CTTick_def by auto

lemma CTTick_event [simp]:
  assumes "CTTick {saa}"
  shows "CTTick {[e]\<^sub>E # saa}"
  using assms unfolding CTTick_def apply auto  
  by (metis Cons_eq_append_conv cttobs.distinct(1) list.inject)                            

lemma
  assumes "R \<subseteq> prirelref pa S" "Tick \<in> S"
  shows "R \<subseteq> prirelref pa (insert Tick S)"
  using assms 
  by (simp add: insert_absorb)

lemma
  assumes "CTTick {[S]\<^sub>R # [Tock]\<^sub>E # zz}"
  shows "CTTick {[[S]\<^sub>R]}"
  using assms unfolding CTTick_def apply auto
  oops

end