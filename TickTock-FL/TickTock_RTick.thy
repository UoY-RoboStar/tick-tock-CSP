theory TickTock_RTick

imports
  "TickTock.TickTock_Core"
  TickTock_FL
  "TickTock.TickTock_Prioritise"
begin

definition mkTT1 :: "'e ttobs list set \<Rightarrow> 'e ttobs list set" where
"mkTT1 P = P \<union> {\<rho>|\<rho> \<sigma>. \<rho> \<lesssim>\<^sub>C \<sigma> \<and> \<sigma> \<in> P}"

lemma TT1_fixpoint_mkTT1:
  "(mkTT1 P = P) = TT1 P"
  unfolding mkTT1_def TT1_def by auto

lemma mkTT1_simp:
  "mkTT1 P = {\<rho>|\<rho> \<sigma>. \<rho> \<lesssim>\<^sub>C \<sigma> \<and> \<sigma> \<in> P}"
  unfolding mkTT1_def apply auto
  using tt_prefix_subset_refl by blast

lemma mkTT1_mono:
  assumes "P \<subseteq> Q"
  shows "mkTT1 P \<subseteq> mkTT1 Q"
  using assms unfolding mkTT1_def by auto

definition unTT1 :: "'e ttobs list set \<Rightarrow> 'e ttobs list set" where
"unTT1 P = \<Union>{x. TTM1 x \<and> TTM2 x \<and> TTM3 x \<and> TT1w x \<and> (mkTT1 x) \<subseteq> P}"

lemma unTT1_mono:
  assumes "P \<subseteq> Q"
  shows "unTT1(P) \<subseteq> unTT1(Q)"
  using assms unfolding unTT1_def by auto

lemma
  assumes "TT4w P" "TT1 P"
  shows "P \<subseteq> mkTT1 (unTT1 P)"
  using assms unfolding mkTT1_def unTT1_def apply auto oops

lemma ttWF_Refusal_tt_prefix:
  assumes "ttWF \<sigma>"
  shows "[[X]\<^sub>R] \<lesssim>\<^sub>C \<sigma> = (\<exists>Y z. \<sigma> = ([[Y]\<^sub>R] @ z) \<and> X \<subseteq> Y)"
  using assms apply auto
  apply (case_tac \<sigma>, auto)
  by (case_tac a, auto)

lemma tt_prefix_eq_length_imp:
  assumes "xs @ [x] \<lesssim>\<^sub>C ys @ [y]"
          "List.length (xs @ [x]) = List.length (ys @ [y])"
    shows "[x] \<lesssim>\<^sub>C [y]"
  using assms by(induct xs ys rule:tt_prefix_subset.induct, auto)

lemma tt_prefix_eq_length_common_prefix:
  assumes "xs @ [x] \<lesssim>\<^sub>C ys @ [y]" "List.length (xs @ [x]) = List.length (ys @ [y])"
  shows "xs \<lesssim>\<^sub>C ys"
  using assms by(induct xs ys rule:tt_prefix_subset.induct, auto)

lemma tt_singleton_prefix_nonempty:
  assumes "[x] \<lesssim>\<^sub>C xa @ z" "xa \<noteq> []"
  shows "[x] \<lesssim>\<^sub>C xa"
  using assms apply (induct xa, auto)
  by (case_tac x, auto, case_tac a, auto, case_tac a, auto)

lemma tt_prefix_gt_length_imp:
  assumes "xs @ [x] \<lesssim>\<^sub>C ys @ [y]"
          "List.length (xs @ [x]) < List.length (ys @ [y])"
    shows "xs @ [x] \<lesssim>\<^sub>C ys"
  using assms apply(induct xs ys rule:tt_prefix_subset.induct, auto)
  using tt_singleton_prefix_nonempty by blast 

lemma ttWF_tt_prefix_subset_exists_three_part:
  assumes "ttWF \<sigma>" "\<rho> @ [[X]\<^sub>R] \<lesssim>\<^sub>C \<sigma>"
  shows "\<exists>Y z \<rho>\<^sub>2. \<sigma> = \<rho>\<^sub>2 @ ([[Y]\<^sub>R] @ z) \<and> X \<subseteq> Y \<and> \<rho> \<lesssim>\<^sub>C \<rho>\<^sub>2 \<and> size \<rho>\<^sub>2 = size \<rho>"
  using assms proof (induct \<sigma> arbitrary:X \<rho> rule:rev_induct)
  case Nil
  then show ?case using tt_prefix_subset.simps(1) tt_prefix_subset_antisym by blast
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
        by (meson tt_prefix_eq_length_imp tt_prefix_subset.simps(5))
    next
      case (Ref x2)
      then have xX2:"[[X]\<^sub>R] \<lesssim>\<^sub>C [[x2]\<^sub>R]"
                    "\<rho> \<lesssim>\<^sub>C xs"
        using True tt_prefix_eq_length_imp snoc.prems(2) apply blast
        using True snoc tt_prefix_eq_length_common_prefix by metis
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
      by (meson tt_prefix_subset_length le_neq_trans)
    then have "\<rho> @ [[X]\<^sub>R] \<lesssim>\<^sub>C xs"
      using snoc tt_prefix_gt_length_imp by metis
    then have "\<exists>Y z \<rho>\<^sub>2. xs = \<rho>\<^sub>2 @ [[Y]\<^sub>R] @ z \<and> X \<subseteq> Y \<and> \<rho> \<lesssim>\<^sub>C \<rho>\<^sub>2 \<and> List.length \<rho>\<^sub>2 = List.length \<rho>"
      using snoc ttWF_prefix_is_ttWF by blast
    then have "\<exists>Y z \<rho>\<^sub>2. xs @ [x] = \<rho>\<^sub>2 @ [[Y]\<^sub>R] @ z @ [x] \<and> X \<subseteq> Y \<and> \<rho> \<lesssim>\<^sub>C \<rho>\<^sub>2 \<and> List.length \<rho>\<^sub>2 = List.length \<rho>"
      by auto
    then have "\<exists>Y z \<rho>\<^sub>2. xs @ [x] = \<rho>\<^sub>2 @ [[Y]\<^sub>R] @ z \<and> X \<subseteq> Y \<and> \<rho> \<lesssim>\<^sub>C \<rho>\<^sub>2 \<and> List.length \<rho>\<^sub>2 = List.length \<rho>"
      by blast
    then show ?thesis by blast
  qed
qed

lemma ttWF_tt_prefix_subset_exists_three_part_concat:
  assumes "\<rho> @ [[X]\<^sub>R] @ s \<lesssim>\<^sub>C \<sigma>"
  shows "\<exists>Y z \<rho>\<^sub>2. \<sigma> = \<rho>\<^sub>2 @ ([[Y]\<^sub>R] @ z) \<and> X \<subseteq> Y \<and> \<rho> \<lesssim>\<^sub>C \<rho>\<^sub>2 \<and> s \<lesssim>\<^sub>C z \<and> size \<rho>\<^sub>2 = size \<rho>"
  using assms proof (induct \<rho> \<sigma> arbitrary:X s rule:tt_prefix_subset.induct)
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
    by (metis "2.prems" append_Cons tt_prefix_subset.simps(2) length_Cons)
next
  case (3 x xa y ya)
  then show ?case apply auto
    by (metis append_Cons tt_prefix_subset.simps(3) length_Cons)
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

lemma tt_prefix_subset_eq_length_common_prefix_eq:
  assumes "List.length xs = List.length ys"
  shows "((xs @ z) \<lesssim>\<^sub>C (ys @ s)) = (xs \<lesssim>\<^sub>C ys \<and> z \<lesssim>\<^sub>C s)"
  using assms by(induct xs ys rule:tt_prefix_subset.induct, auto)

lemma ttWF_tt_prefix_subset_exists_three_part':
  assumes "\<sigma> = \<rho>\<^sub>2 @ ([[Y]\<^sub>R] @ z) \<and> X \<subseteq> Y \<and> \<rho> \<lesssim>\<^sub>C \<rho>\<^sub>2 \<and> size \<rho>\<^sub>2 = size \<rho>" "ttWF \<sigma>"
  shows "\<rho> @ [[X]\<^sub>R] \<lesssim>\<^sub>C \<sigma>"
  using assms apply auto 
  by (simp add: tt_prefix_subset_eq_length_common_prefix_eq)

lemma ttWF_tt_prefix_subset_exists_three_part_iff:
  assumes "ttWF \<sigma>"
  shows "\<rho> @ [[X]\<^sub>R] \<lesssim>\<^sub>C \<sigma> = (\<exists>Y z \<rho>\<^sub>2. \<sigma> = \<rho>\<^sub>2 @ ([[Y]\<^sub>R] @ z) \<and> X \<subseteq> Y \<and> \<rho> \<lesssim>\<^sub>C \<rho>\<^sub>2 \<and> size \<rho>\<^sub>2 = size \<rho>)"
  using assms
  by (meson ttWF_tt_prefix_subset_exists_three_part ttWF_tt_prefix_subset_exists_three_part')
 
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

lemma tt_prefix_of_TT3_trace:
  assumes "x \<lesssim>\<^sub>C \<sigma>" "TT3_trace \<sigma>"
  shows "TT3_trace x"
  using assms 
proof (induct x \<sigma> rule:tt_prefix_subset.induct)
  case (1 x)
  then show ?case by auto
next
  case (2 X xa Y ya)
  then show ?case
    apply (induct xa ya rule:tt_prefix_subset.induct, auto)
    apply (case_tac y, auto)
    using TT3_trace.simps(3) TT3_trace_cons_imp_cons by blast
next
  case (3 x xa y ya)
  then show ?case by (induct xa ya rule:tt_prefix_subset.induct, auto)
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

lemma TT3_mkTT1:
  assumes "TT3 P"
  shows "TT3(mkTT1(P))"
  using assms unfolding mkTT1_def TT3_def apply auto
  using tt_prefix_of_TT3_trace by blast

lemma add_Tick_refusal_trace_tt_prefix_subset_mono:
  assumes "\<rho> \<lesssim>\<^sub>C \<sigma>"
  shows   "add_Tick_refusal_trace \<rho> \<lesssim>\<^sub>C add_Tick_refusal_trace \<sigma>"
  using assms by(induct \<rho> \<sigma> rule:tt_prefix_subset.induct, auto)

lemma TT4_mkTT1:
  assumes "TT4 P"
  shows "TT4(mkTT1(P))"
  using assms unfolding mkTT1_def TT4_def apply auto
  using add_Tick_refusal_trace_tt_prefix_subset_mono by blast

lemma
  "TTM1(unTT1 P)"
  unfolding unTT1_def TTM1_def by auto

lemma
  "(s \<in> (\<Union>{x. TTick x \<and> (mkTT1 x) \<subseteq> P})) = (s \<in> Q)"
  apply safe
  oops

(* A wild guess below: *)

fun RprirelRef :: "('e ttevent) partialorder \<Rightarrow> ('e ttobs) list \<Rightarrow> ('e ttobs) list \<Rightarrow> ('e ttobs) list \<Rightarrow> ('e ttobs) list set \<Rightarrow> bool" where
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

definition mkTT4w :: "'e ttobs list set \<Rightarrow> 'e ttobs list set" where
"mkTT4w P = P \<union> {\<rho> @ [[R \<union> {Tick}]\<^sub>R]|\<rho> R. \<rho> @ [[R]\<^sub>R] \<in> P}"

lemma TT4w_fixpoint_mkTT4w:
  "(mkTT4w P = P) = TT4w P"
  unfolding mkTT4w_def TT4w_def by auto

lemma mkTT1_mkTT4w_iff_TT14:
  "(mkTT1(mkTT4w P) = P) = (TT1 P \<and> TT4w P)"
  apply auto
  using TT1_def mkTT1_simp mkTT4w_def apply fastforce
  apply (metis (mono_tags, lifting) TT1_def TT1_fixpoint_mkTT1 TT4w_fixpoint_mkTT4w CollectI UnI1 mkTT1_simp mkTT4w_def)  
    apply (metis TT1_fixpoint_mkTT1 TT4w_fixpoint_mkTT4w)
    by (metis TT1_fixpoint_mkTT1 TT4w_fixpoint_mkTT4w)

lemma TT1_mkTT1_simp:
  assumes "TT1 P"
  shows "(\<exists>x. s \<in> x \<and> (mkTT1 x) \<subseteq> P) = (s \<in> P)"
  using assms apply safe
  using mkTT1_def apply fastforce
  using TT1_fixpoint_mkTT1 by blast

fun mkTTick_Trace :: "'e ttobs list \<Rightarrow> 'e ttobs list" where
"mkTTick_Trace [] = []" |
"mkTTick_Trace ([x]\<^sub>R # xs) = (if xs = [] then ([x \<union> {Tick}]\<^sub>R # xs) else ([x]\<^sub>R # mkTTick_Trace xs))" |
"mkTTick_Trace ([e]\<^sub>E # xs) = ([e]\<^sub>E # mkTTick_Trace xs)"

lemma TTick_dist_union:
  "TTick (P \<union> Q) = (TTick(P) \<and> TTick(Q))"
  unfolding TTick_def by auto

lemma TTM3_dist_union:
  "TTM3 (P \<union> Q) = (TTM3(P) \<and> TTM3(Q))"
  unfolding TTM3_def by auto

lemma TTick_mkTT1_simp:
  assumes "TT1 P" "TT4w P"
  shows "(\<exists>x. s \<in> x \<and> TTM3 x \<and> (mkTT1 x) \<subseteq> P) = (s \<in> P \<and> TTM3 {s})"
  using assms apply safe
  using mkTT1_def apply fastforce
  using TTM3_dist_union
  apply (metis insert_Diff insert_is_Un)
  apply (rule_tac x="{s}" in exI, auto)
  unfolding mkTT1_def apply auto
  using TT1_def by blast

fun TTMPick :: "'e ttobs list \<Rightarrow> 'e ttobs list \<Rightarrow> 'e ttobs list set \<Rightarrow> bool" where
"TTMPick [] s P = True" |
"TTMPick ([X]\<^sub>R # xs) s P = ((\<forall>e. e \<notin> X \<and> e \<noteq> Tock \<longrightarrow> s @ [[e]\<^sub>E] \<in> P)
                           \<and>
                           (Tock \<notin> X \<longrightarrow> s @ [[X]\<^sub>R,[Tock]\<^sub>E] \<in> P) \<and> Tick \<in> X \<and> TTMPick xs (s @ [[X]\<^sub>R]) P)" |
"TTMPick ([e]\<^sub>E # xs) s P = TTMPick xs (s @ [[e]\<^sub>E]) P"

lemma TTMPick_extend_event_imp:
  assumes "TTMPick xs s P"
  shows "TTMPick (xs @ [[e]\<^sub>E]) s P"
  using assms by (induct xs s P arbitrary:e rule:TTMPick.induct, auto)

lemma TTMPick_extend_ref_imp:
  assumes "TTMPick xs s P" "Tick \<in> X"
          "\<forall>e. (e \<noteq> Tock \<and> e \<notin> X) \<longrightarrow> s @ xs @ [[e]\<^sub>E] \<in> P"
          "(Tock \<notin> X) \<longrightarrow> s @ xs @ [[X]\<^sub>R,[Tock]\<^sub>E] \<in> P"
  shows "TTMPick (xs @ [[X]\<^sub>R]) s P"
  using assms by (induct xs s P arbitrary: X rule:TTMPick.induct, auto)

lemma TTM1_TTM2_TT1w_mkTT1_imp_TTMPick:
  assumes "s \<in> x" "TTM1 x" "TTM2 x" "TT1w x" "mkTT1 x \<subseteq> P" "TTM3 x"
  shows "TTMPick s [] P"
  using assms proof(induct s arbitrary:x rule:rev_induct)
  case Nil
  then show ?case by auto
next
  case (snoc z zs)
  then have "TTMPick zs [] P"
    using assms TT1w_prefix_concat_in by blast
  then show ?case
  proof (cases z)
    case (ObsEvent x1)
    then show ?thesis using snoc TTMPick_extend_event_imp
      using \<open>TTMPick zs [] P\<close> by blast
  next
    case (Ref x2)
    then have "TTMPick zs [] P"
      using \<open>TTMPick zs [] P\<close> by blast
    
    have a:"Tick \<in> x2"
      using snoc Ref
      by (metis TTM3_def TTickTrace.elims(2) TTickTrace_dist_concat ttobs.distinct(1) ttobs.inject(2) list.inject not_Cons_self2)
    have b:"\<forall>e. e \<noteq> Tock \<and> e \<notin> x2 \<longrightarrow> zs @ [[e]\<^sub>E] \<in> P"  
      using TTM1_def Ref mkTT1_def snoc.prems(1) snoc.prems(2) snoc.prems(5) by fastforce
    have c:"Tock \<notin> x2 \<longrightarrow> zs @ [[x2]\<^sub>R, [Tock]\<^sub>E] \<in> P"
      using TTM2_def Ref mkTT1_def snoc.prems(1) snoc.prems(3) snoc.prems(5) by fastforce

    then have "TTMPick (zs @ [[x2]\<^sub>R]) [] P"
      using a b c snoc \<open>TTMPick zs [] P\<close>
      by (simp add: TTMPick_extend_ref_imp)
    then show ?thesis using Ref by auto
   qed
qed

definition mkTTM1 :: "'e ttobs list set \<Rightarrow> 'e ttobs list set" where
"mkTTM1 P = P \<union> {\<rho> @ [[e]\<^sub>E]|\<rho> X e. \<rho> @ [[X]\<^sub>R] \<in> P \<and> e \<notin> X \<and> e \<noteq> Tock}"

definition mkTTM2 :: "'e ttobs list set \<Rightarrow> 'e ttobs list set" where
"mkTTM2 P = P \<union> {\<rho> @ [[X]\<^sub>R,[Tock]\<^sub>E]|\<rho> X. \<rho> @ [[X]\<^sub>R] \<in> P \<and> Tock \<notin> X}"

lemma TTM1_mkTTM1 [simp]: "TTM1 (mkTTM1 P)"
  unfolding mkTTM1_def TTM1_def by auto

lemma TTM2_mkTTM2 [simp]: "TTM2 (mkTTM2 P)"
  unfolding mkTTM2_def TTM2_def by auto

lemma mkTTM2_mkTTM1_commute: "mkTTM2 (mkTTM1 P) = mkTTM1 (mkTTM2 P)"
  unfolding mkTTM2_def mkTTM1_def by auto

definition mkTT1w :: "'e ttobs list set \<Rightarrow> 'e ttobs list set" where
"mkTT1w P = P \<union> {\<rho>|\<rho> \<sigma>. \<rho> \<le>\<^sub>C \<sigma> \<and> \<sigma> \<in> P}"

lemma TT1w_fixpoint_mkTT1w:
  "TT1w P = (P = mkTT1w(P))"
  unfolding TT1w_def mkTT1w_def by auto

lemma TTMPick_imp_in_mkTTM2_mkTTM1:
  assumes "TTMPick s [] P" 
  shows "s \<in> mkTTM2 (mkTTM1 {s})"
  using assms unfolding mkTTM2_def mkTTM1_def by auto

lemma TTMPick_imp_in_prefix_mkTTM2_mkTTM1:
  assumes "TTMPick s [] P" 
  shows "s \<in> mkTTM2 (mkTTM1 {x. x \<le>\<^sub>C s})"
  using assms unfolding mkTTM2_def mkTTM1_def apply auto
  by (simp add: tt_prefix_refl)

lemma TTMPick_imp_in_prefix_mkTTM2_mkTTM1_TT1w:
  assumes "TTMPick s [] P" 
  shows "s \<in> mkTTM2 (mkTTM1 (mkTT1w{s}))"
  using assms unfolding mkTTM2_def mkTTM1_def mkTT1w_def by auto

lemma TTick_imp_TTick_mkTTM1_mkTTM2:
  assumes "TTick {s}"
  shows "TTick (mkTTM1 (mkTTM2 {s}))"
  using assms unfolding mkTTM2_def mkTTM1_def TTick_def by auto

lemma TTickTrace_prefix:
  assumes "TTickTrace s" "t \<le>\<^sub>C s" 
  shows "TTickTrace t"
  using assms apply (induct t s rule:tt_prefix.induct, auto)
  by (case_tac y, auto)

lemma TTM3_singleton_imp_prefixes:
  assumes "TTM3 {s}"
  shows "TTM3 {x. x \<le>\<^sub>C s}"
  using assms unfolding TTM3_def apply auto
  using TTickTrace_prefix by blast

lemma TTM3_singleton_mkTTM1:
  assumes "TTM3 {s}"
  shows "TTM3(mkTTM1 {x. x \<le>\<^sub>C s})"
  using assms unfolding mkTTM1_def TTM3_def apply auto
  using TTickTrace_prefix apply blast
  by (metis TTickTrace.simps(1) TTickTrace.simps(2) TTickTrace_dist_concat TTickTrace_prefix)

lemma TTM3_singleton_mkTTM2:
  assumes "TTM3 {s}"
  shows "TTM3(mkTTM2 {x. x \<le>\<^sub>C s})"
  using assms unfolding mkTTM2_def TTM3_def apply auto
  using TTickTrace_prefix apply blast
  by (metis TTickTrace.simps(2) TTickTrace.simps(3) TTickTrace_dist_concat TTickTrace_prefix)

lemma TTM3_imp_TTM3_mkTTM1_mkTTM2:
  assumes "TTM3 {s}"
  shows "TTM3 (mkTTM1 (mkTTM2 {x. x \<le>\<^sub>C s}))"
  using assms unfolding mkTTM1_def mkTTM2_def TTM3_def apply auto
  using TTickTrace_prefix apply blast
  apply (metis TTickTrace.simps(2) TTickTrace.simps(3) TTickTrace_dist_concat TTickTrace_prefix)
  by (metis TTickTrace.simps(1) TTickTrace.simps(2) TTickTrace_dist_concat TTickTrace_prefix)

lemma TTM3_imp_TTM3_mkTTM1_mkTTM2_mkTT1w:
  assumes "TTM3 {s}"
  shows "TTM3 (mkTTM1 (mkTTM2 (mkTT1w{s})))"
  using assms unfolding mkTTM1_def mkTTM2_def mkTT1w_def TTM3_def apply auto
  using TTickTrace_prefix apply blast
     apply (metis TTickTrace.simps(2) TTickTrace.simps(3) TTickTrace_dist_concat)
  apply (metis TTickTrace.simps(2) TTickTrace.simps(3) TTickTrace_dist_concat TTickTrace_prefix)
  apply (metis TTickTrace.simps(1) TTickTrace.simps(2) TTickTrace_dist_concat)
  by (metis TTickTrace.simps(2) TTickTrace.simps(3) TTickTrace_dist_concat TTickTrace_prefix)
  
lemma TT1w_mkTTM1:
  assumes "TT1w P"
  shows "TT1w (mkTTM1 P)"
  using assms unfolding mkTTM1_def TT1w_def apply auto
  by (meson tt_prefix_concat tt_prefix_notfront_is_whole)


lemma mkTTM2_dist_union:
  "mkTTM2(P \<union> Q) = (mkTTM2(P) \<union> mkTTM2(Q))"
  unfolding mkTTM2_def by auto

lemma mkTTM2_in_mkTT1w_for_TT1w:
  assumes "TT1w P"
  shows "mkTTM2({\<rho>|\<rho> \<sigma>. \<rho> \<le>\<^sub>C \<sigma> \<and> \<sigma> \<in> P}) = ({\<rho>|\<rho> \<sigma>. \<rho> \<le>\<^sub>C \<sigma> \<and> \<sigma> \<in> mkTTM2(P)})"
  unfolding mkTTM2_def apply auto
  apply (rule_tac x="\<rho> @ [[X]\<^sub>R, [Tock]\<^sub>E]" in exI, auto)
  apply (simp add: tt_prefix_refl)
  using TT1w_def assms apply blast
  by (smt TT1w_prefix_concat_in Nil_is_append_conv append_Cons append_Nil2 append_eq_append_conv2 append_self_conv2 assms ttWF.simps(1) tt_prefix_append_split tt_prefix_notfront_is_whole tt_prefix_refl tt_prefix_same_front same_append_eq split_tocks)

lemma mkTTM2_mkTT1w_commute:
  assumes "TT1w P"
  shows "mkTTM2(mkTT1w(P)) = mkTT1w(mkTTM2(P))"
proof -
  have "mkTTM2(mkTT1w(P)) = mkTTM2(P \<union> {\<rho>|\<rho> \<sigma>. \<rho> \<le>\<^sub>C \<sigma> \<and> \<sigma> \<in> P})"
    unfolding mkTT1w_def by auto
  also have "... = mkTTM2(P) \<union> mkTTM2({\<rho>|\<rho> \<sigma>. \<rho> \<le>\<^sub>C \<sigma> \<and> \<sigma> \<in> P})"
    using mkTTM2_dist_union by auto
  also have "... = mkTTM2(P) \<union> {\<rho>|\<rho> \<sigma>. \<rho> \<le>\<^sub>C \<sigma> \<and> \<sigma> \<in> mkTTM2(P)}"
    using assms mkTTM2_in_mkTT1w_for_TT1w by blast
  also have "... = mkTT1w(mkTTM2(P))"
    unfolding mkTT1w_def by auto
  finally show ?thesis .
qed

lemma TT1w_mkTTM2:
  assumes "TT1w P"
  shows "TT1w (mkTTM2 P)"
proof -
  have "TT1w P = (P = mkTT1w(P))"
    using TT1w_fixpoint_mkTT1w by blast
  then have "TT1w (mkTTM2 P) = TT1w (mkTTM2(mkTT1w(P)))"
    using assms by auto
  also have "... = TT1w(mkTT1w(mkTTM2(P)))"
    using assms by (simp add: mkTTM2_mkTT1w_commute)
  also have "... = True"
    by (metis TT1w_fixpoint_mkTT1w assms mkTTM2_mkTT1w_commute)
  then show ?thesis using calculation by auto
qed

lemma TT1w_mkTT1w [simp]: "TT1w (mkTT1w P)"
  unfolding mkTT1w_def TT1w_def apply auto
  using tt_prefix_trans by blast

lemma TT1w_mkTTM1_mkTTM2_mkTT1w:
  "TT1w (mkTTM1 (mkTTM2 (mkTT1w P)))"
proof -
  have "TT1w (mkTTM2 (mkTT1w P))"
    using TT1w_mkTTM2 TT1w_mkTT1w by blast
  then have "TT1w (mkTTM1 (mkTTM2 (mkTT1w P)))"
    using TT1w_mkTTM1 by blast
  then show ?thesis .
qed

lemma TTMPick_imp_RefTock_in:
  assumes "TTMPick (\<rho> @ [[X]\<^sub>R] @ x) s P" "Tock \<notin> X"
  shows "s @ \<rho> @ [[X]\<^sub>R, [Tock]\<^sub>E] \<in> P"
  using assms by (induct \<rho> s P rule:TTMPick.induct, auto)

lemma TTMPick_imp_Event_in:
  assumes "TTMPick (\<rho> @ [[X]\<^sub>R] @ x) s P" "e \<notin> X" "e \<noteq> Tock"
  shows "s @ \<rho> @ [[e]\<^sub>E] \<in> P"
  using assms by (induct \<rho> s P rule:TTMPick.induct, auto)

lemma
  assumes "TTMPick s z P" "x \<lesssim>\<^sub>C \<sigma>" "\<sigma> \<le>\<^sub>C s"
  shows "x \<in> P"
  using assms apply (induct s z P rule:TTMPick.induct, auto)
  oops
(*
lemma
  assumes "b \<noteq> []"
  shows "x \<le>\<^sub>C \<rho> @ b \<Longrightarrow> \<not> x \<le>\<^sub>C \<rho> \<Longrightarrow> x = \<rho> @ b"
  using assms apply (induct x \<rho> arbitrary:b rule:tt_prefix.induct, auto)
    apply (case_tac x, auto, case_tac y, auto)
  apply (case_tac y, auto)
    apply (metis append.right_neutral tt_prefix_subset_front tt_prefix_subset_same_front)
   apply (case_tac y, auto)
    apply (metis tt_prefix_subset.simps(3) tt_prefix_subset.simps(5) ttobs.exhaust)
   apply (case_tac x, auto)
  apply (case_tac x, auto)
*)

(*
lemma
  assumes "TT1 P" "\<rho> @ [[X]\<^sub>R] \<in> P" "x \<lesssim>\<^sub>C \<rho> @ [[X]\<^sub>R, [Tock]\<^sub>E]" "Tock \<notin> X" "\<rho> @ [[X]\<^sub>R] \<le>\<^sub>C s"
  shows "x \<in> P"
proof -
  have "\<forall>x. x \<lesssim>\<^sub>C \<rho> @ [[X]\<^sub>R] \<longrightarrow> x \<in> P"
    using assms TT1_def by blast
  have "x \<lesssim>\<^sub>C \<rho> @ [[X]\<^sub>R, [Tock]\<^sub>E] = (x \<lesssim>\<^sub>C \<rho> @ [[X]\<^sub>R] \<or> (\<not> x \<lesssim>\<^sub>C \<rho> @ [[X]\<^sub>R] \<and> x = \<rho> @ [[X]\<^sub>R, [Tock]\<^sub>E]))"
    apply auto
    sledgehammer
  using assms apply (induct x arbitrary:X \<rho> s rule:rev_induct, auto)
  
*)

(* FIXME: Ugly proof *)
lemma TTM3_mkTT1_simp:
  assumes "TT1 P" "TT4w P"
  shows "(\<exists>x. s \<in> x \<and> TTM1 x \<and> TTM2 x \<and> TTM3 x \<and> TT1w x \<and> (mkTT1 x) \<subseteq> P) 
         = 
         (s \<in> P \<and> TTM3 {s} \<and> TTMPick s [] P)"
  using assms apply safe
  using mkTT1_def apply fastforce
  using TTM3_dist_union 
    apply (metis insert_Diff insert_is_Un)
  using TTM1_TTM2_TT1w_mkTT1_imp_TTMPick apply blast
  (* Need to define mkTTM1 mkTTM2 and mkTT1w then can prove the following goal. *)
  apply (rule_tac x="mkTTM2(mkTTM1(mkTT1w{s}))" in exI) 
  apply auto
      apply (simp add:TTMPick_imp_in_prefix_mkTTM2_mkTTM1_TT1w)
     apply (auto simp add:mkTTM2_mkTTM1_commute TTM3_imp_TTM3_mkTTM1_mkTTM2_mkTT1w)
  using TT1w_mkTTM1_mkTTM2_mkTT1w apply blast
  using TT1w_mkTTM2 TT1w_mkTTM1 assms 
  unfolding mkTTM1_def mkTTM2_def mkTT1_def apply auto
  unfolding mkTT1w_def apply auto 
  using TT1_def tt_prefix_imp_prefix_subset apply blast
  using TTMPick_imp_RefTock_in apply fastforce
  using TTMPick_imp_RefTock_in append_assoc tt_prefix_split apply fastforce
  using TTMPick_imp_Event_in apply fastforce
  using TTMPick_imp_Event_in append_assoc tt_prefix_split apply fastforce

  using TT1_def apply blast
      apply (smt TT1_TT1w TT1_def TT1w_prefix_concat_in tt_prefix_split)
  apply (case_tac "x \<lesssim>\<^sub>C \<rho> @ [[X]\<^sub>R]")
  using TT1_def apply blast
     apply (case_tac "x = \<rho> @ [[X]\<^sub>R, [Tock]\<^sub>E]", auto)
  using TTMPick_imp_RefTock_in apply fastforce
  apply (smt TT1_def TTMPick_extend_event_imp TTMPick_imp_RefTock_in append.left_neutral append_assoc assms(1))
    
    apply (smt TT1_def TTMPick_imp_RefTock_in append_Nil append_assoc tt_prefix_split)
    
     apply (case_tac "x \<lesssim>\<^sub>C \<rho>")
  apply (smt TT1_TT1w TT1_def TT1w_prefix_concat_in)
   apply (case_tac "x = \<rho> @ [[e]\<^sub>E]", auto)
 
  using TTMPick_imp_Event_in Cons_eq_appendI append.assoc self_append_conv2 apply fastforce
proof -
  fix x :: "'a ttobs list" and \<rho> :: "'a ttobs list" and X :: "'a ttevent set" and e :: "'a ttevent"
  assume a1: "TTMPick (\<rho> @ [[X]\<^sub>R]) [] P"
  assume a2: "x \<lesssim>\<^sub>C \<rho> @ [[e]\<^sub>E]"
  assume a3: "e \<notin> X"
  assume a4: "e \<noteq> Tock"
  assume "s = \<rho> @ [[X]\<^sub>R]"
  have "\<rho> @ [[e]\<^sub>E] \<in> P"
    using a4 a3 a1 by (metis (no_types) TTMPick_imp_Event_in append_Cons append_Nil)
  then show "x \<in> P"
    using a2 TT1_fixpoint_mkTT1 assms(1) mkTT1_def by fastforce
next  
  fix x :: "'a ttobs list" and \<rho> :: "'a ttobs list" and X :: "'a ttevent set" and e :: "'a ttevent"
  assume 
      a0: "TT1 P"
  and a1: "TTMPick s [] P"
  and a2: "x \<lesssim>\<^sub>C \<rho> @ [[e]\<^sub>E]"
  and a3: "e \<notin> X"
  and a4: "e \<noteq> Tock"
  and a5:"\<rho> @ [[X]\<^sub>R] \<le>\<^sub>C s"
  then show "x \<in> P"
    apply (case_tac "x \<lesssim>\<^sub>C \<rho>")
    apply (smt TT1_def TTMPick_imp_Event_in a1 a2 a3 a4 append_assoc append_self_conv2 assms(1) tt_prefix_decompose)
    apply (case_tac "x = \<rho> @ [[e]\<^sub>E]", auto)  
    using TTMPick_imp_Event_in tt_prefix_split apply fastforce
  by (smt TT1_def TTMPick_imp_Event_in append_Nil append_assoc tt_prefix_decompose)
qed

lemma TT14_TTick_mkTT1_exists:
  assumes "TT1 P" "TT4w P"
  shows "(s @ [[Z]\<^sub>R] \<in> unTT1 P \<and> e\<^sub>2 \<notin> Z \<and> \<not>(\<exists>b. b \<notin> Z \<and> e\<^sub>2 <\<^sup>*p b))
         =
         (s @ [[Z]\<^sub>R] \<in> P \<and> TTM3 {s @ [[Z]\<^sub>R]} \<and> TTMPick (s @ [[Z]\<^sub>R]) [] P \<and> e\<^sub>2 \<notin> Z \<and> \<not>(\<exists>b. b \<notin> Z \<and> e\<^sub>2 <\<^sup>*p b))"
proof -
  have "(s @ [[Z]\<^sub>R] \<in> unTT1 P \<and> e\<^sub>2 \<notin> Z \<and> \<not>(\<exists>b. b \<notin> Z \<and> e\<^sub>2 <\<^sup>*p b))
        =
        (s @ [[Z]\<^sub>R] \<in> (\<Union>{x. TTM1 x \<and> TTM2 x \<and> TTM3 x \<and> TT1w x \<and> (mkTT1 x) \<subseteq> P}) \<and> e\<^sub>2 \<notin> Z \<and> \<not>(\<exists>b. b \<notin> Z \<and> e\<^sub>2 <\<^sup>*p b))"
    unfolding unTT1_def by auto
  also have "...
        =
        (\<exists>x. s @ [[Z]\<^sub>R] \<in> x \<and> TTM1 x \<and> TTM2 x \<and> TTM3 x \<and> TT1w x \<and> (mkTT1 x) \<subseteq> P \<and> e\<^sub>2 \<notin> Z \<and> \<not>(\<exists>b. b \<notin> Z \<and> e\<^sub>2 <\<^sup>*p b))"
    by auto
  also have "... =
       (s @ [[Z]\<^sub>R] \<in> P \<and> TTM3 {s @ [[Z]\<^sub>R]} \<and> TTMPick (s @ [[Z]\<^sub>R]) [] P \<and> e\<^sub>2 \<notin> Z \<and> \<not>(\<exists>b. b \<notin> Z \<and> e\<^sub>2 <\<^sup>*p b))"
    using assms TTM3_mkTT1_simp by auto
  (*also have "... =
       (\<exists>Z. s @ [[Z]\<^sub>R] \<in> P \<and> Tick \<in> Z \<and> e\<^sub>2 \<notin> Z \<and> \<not>(\<exists>b. b \<notin> Z \<and> e\<^sub>2 <\<^sup>*p b))"
    using assms
    using TTM3_def by blast*)
  (*also have "... =
       (\<exists>Z. s @ [[Z]\<^sub>R] \<in> P \<and> e\<^sub>2 \<notin> Z \<and> \<not>(\<exists>b. b \<notin> Z \<and> e\<^sub>2 <\<^sup>*p b))"
    apply auto 
    apply (rule_tac x="Z \<union> {Tick}" in exI, auto)
    using assms 
    using TT4w_fixpoint_mkTT4w mkTT4w_def apply fastforce*)
  finally show ?thesis .
qed

lemma
  "(\<exists>t. \<rho> \<lesssim>\<^sub>C t \<and> prirelRef p t s [] (unTT1 P) \<and> s \<in> P \<and> TTick {s}) = (\<exists>t. \<rho> \<lesssim>\<^sub>C t \<and> RprirelRef p t s [] P \<and> s \<in> P \<and> TTick {s})"
  nitpick
  oops

definition prirelrefSub :: "('e ttevent) partialorder \<Rightarrow> ('e ttevent) set \<Rightarrow> ('e ttobs) list \<Rightarrow> ('e ttobs) list set \<Rightarrow> ('e ttevent) set" where
"prirelrefSub pa S sa Q = 
  {z. ((z = Tock \<and> sa @ [[S]\<^sub>R, [Tock]\<^sub>E] \<in> Q) \<longrightarrow> (\<exists>b. b \<notin> S \<and> sa @ [[b]\<^sub>E] \<in> Q \<and> b \<noteq> Tock \<and> b \<noteq> Tick \<and> z <\<^sup>*pa b))
        \<and>
       ((z \<notin> S \<and> sa @ [[z]\<^sub>E] \<in> Q \<and> z \<noteq> Tock \<and> z \<noteq> Tick) \<longrightarrow>
          ((sa @ [[S]\<^sub>R, [Tock]\<^sub>E] \<in> Q \<and> z <\<^sup>*pa Tock)
            \<or>
           (\<exists>b. b \<notin> S \<and> sa @ [[b]\<^sub>E] \<in> Q \<and> b \<noteq> Tock \<and> b \<noteq> Tick \<and> z <\<^sup>*pa b)))}"

fun prirelRef2 :: "('e ttevent) partialorder \<Rightarrow> ('e ttobs) list \<Rightarrow> ('e ttobs) list \<Rightarrow> ('e ttobs) list \<Rightarrow> ('e ttobs) list set \<Rightarrow> bool" where
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





lemma TTwf_no_ill_Tock [simp]:
  assumes "TTwf P" "e \<noteq> Tock"
  shows "sa @ [[X]\<^sub>R, [e]\<^sub>E] \<notin> P"
  using assms unfolding TTwf_def apply (induct sa rule:ttWF.induct, auto)
    apply (cases e, auto)
  apply (metis assms(2) ttWF.simps(11) ttWF.simps(12) ttWF.simps(4) ttWF_dist_cons_refusal ttevent.exhaust ttobs.inject(1) ttobs.inject(2) list.inject)
  by (metis append.left_neutral append_Cons ttWF.simps(11) ttWF.simps(12) ttWF_dist_cons_refusal' ttevent.exhaust)

(* Problem below is from 's' how to achieve target 's'? Need a way to construct it
   explicitly, then just need to show that x \<lesssim>\<^sub>C t. *)
fun mkTTMP :: "'e ttobs list \<Rightarrow> 'e ttobs list \<Rightarrow> 'e ttobs list set \<Rightarrow> 'e ttobs list" where
"mkTTMP [] s P = []" |
"mkTTMP ([X]\<^sub>R # xs) s P =
        ([X \<union> {e. (e \<noteq> Tock \<and> s @ [[e]\<^sub>E] \<notin> P) \<or> (e = Tock \<and> s @ [[X]\<^sub>R,[Tock]\<^sub>E] \<notin> P)} \<union> {Tick}]\<^sub>R # 
         (mkTTMP xs (s @ [[X]\<^sub>R]) P))" |
"mkTTMP ([e]\<^sub>E # xs) s P = ([e]\<^sub>E # (mkTTMP xs (s @ [[e]\<^sub>E]) P))"


lemma TT4_TT1_imp_Ref_Tock:
  assumes "s @ [[X]\<^sub>R, [Tock]\<^sub>E] \<in> P" "TT1 P" "TT4 P"
  shows "s @ [[X \<union> {Tick}]\<^sub>R,[Tock]\<^sub>E] \<in> P"
  using assms unfolding TT1_def TT4_def
proof (auto)
  fix \<rho> X s
  assume TT1_P: "\<forall>\<rho>. (\<exists>\<sigma>. \<rho> \<lesssim>\<^sub>C \<sigma> \<and> \<sigma> \<in> P) \<longrightarrow> \<rho> \<in> P"
  assume "s @ [[X]\<^sub>R, [Tock]\<^sub>E] \<in> P" "\<forall>\<rho>. \<rho> \<in> P \<longrightarrow> add_Tick_refusal_trace \<rho> \<in> P"
  then have "add_Tick_refusal_trace (s @ [[X]\<^sub>R, [Tock]\<^sub>E]) \<in> P"
    by auto
  then have "add_Tick_refusal_trace s @ add_Tick_refusal_trace ([[X]\<^sub>R, [Tock]\<^sub>E]) \<in> P"
    by (simp add: add_Tick_refusal_trace_concat)
  then have "add_Tick_refusal_trace s @ [[X \<union> {Tick}]\<^sub>R,[Tock]\<^sub>E] \<in> P"
    by auto
  also have "s @ [[X \<union> {Tick}]\<^sub>R,[Tock]\<^sub>E] \<subseteq>\<^sub>C add_Tick_refusal_trace s @ [[X \<union> {Tick}]\<^sub>R,[Tock]\<^sub>E]"
    by (simp add: add_Tick_refusal_trace_tt_subset tt_subset_combine)
  then show "s @ [[insert Tick X]\<^sub>R, [Tock]\<^sub>E] \<in> P"
    using TT1_P calculation tt_subset_imp_prefix_subset by auto
qed

lemma TT2_Ref_Tock_augment:
  assumes "s @ [[X]\<^sub>R, [Tock]\<^sub>E] \<in> P" "TT2 P" "TT1 P" "TT4 P"
  shows "s @ [[X \<union> {e. e \<noteq> Tock \<and> s @ [[e]\<^sub>E] \<notin> P} \<union> {Tick}]\<^sub>R, [Tock]\<^sub>E] \<in> P"
proof -
  have "{e. e \<noteq> Tock \<and> s @ [[e]\<^sub>E] \<notin> P} \<inter> {e. (e \<noteq> Tock \<and> s @ [[e]\<^sub>E] \<in> P) \<or> (e = Tock \<and> s @ [[X]\<^sub>R, [e]\<^sub>E] \<in> P) } = {}"
    by auto
  then have "s @ [[X \<union> {e. e \<noteq> Tock \<and> s @ [[e]\<^sub>E] \<notin> P}]\<^sub>R] @ [[Tock]\<^sub>E] \<in> P"
    using assms by (simp add: TT2_def) 
  then have "s @ [[X \<union> {e. e \<noteq> Tock \<and> s @ [[e]\<^sub>E] \<notin> P} \<union> {Tick}]\<^sub>R] @ [[Tock]\<^sub>E] \<in> P"
    using TT4_TT1_imp_Ref_Tock assms
    by auto
  then show ?thesis by auto
qed


(*
lemma
  assumes "TTMPick xs (s @ [[X]\<^sub>R]) P" "TTwf P" "ttWF (xs)" "ttWF (s @ [[X]\<^sub>R])"
  shows "TTMPick xs (s @ [[X \<union> {e. e \<noteq> Tock \<and> s @ [[e]\<^sub>E] \<notin> P \<or> e = Tock \<and> s @ [[X]\<^sub>R, [Tock]\<^sub>E] \<notin> P}]\<^sub>R]) P"
  using assms nitpick 
  apply (induct xs arbitrary:X s, auto)
  apply (case_tac a, auto)
*)
  (*apply (induct xs _ P arbitrary:X s rule:TTMPick.induct, auto)
  sledgehammer
*)
(*
lemma
  assumes "TTMPick z (s @ [[X]\<^sub>R]) P" "ttWF (s @ [[X]\<^sub>R] @ z)"
  shows "TTMPick z (s @ [[insert Tick (X \<union> {e. e \<noteq> Tock \<and> s @ [[e]\<^sub>E] \<notin> P \<or> e = Tock \<and> s @ [[X]\<^sub>R, [Tock]\<^sub>E] \<notin> P})]\<^sub>R]) P"
  using assms apply(induct z _ P arbitrary:X s rule:TTMPick.induct)
    apply auto[1]*)
 (* apply (metis (no_types) append_Cons append_Nil ttWF.simps(13) ttWF_dist_cons_refusal')
*)

(*
lemma
  assumes "TTMPick zs (s @ [[X]\<^sub>R,[Tock]\<^sub>E]) P" "ttWF (s @ [[X]\<^sub>R,[Tock]\<^sub>E] @ zs)"
  shows "TTMPick zs (s @ [[insert Tick (X \<union> {e. e \<noteq> Tock \<and> s @ [[e]\<^sub>E] \<notin> P \<or> e = Tock \<and> s @ [[X]\<^sub>R, [Tock]\<^sub>E] \<notin> P})]\<^sub>R,[Tock]\<^sub>E]) P"
  using assms apply(induct zs s P arbitrary:X rule:TTMPick.induct, auto)
*)

lemma TTMPick_imp_prefix:
  assumes "TTMPick (xs @ [x]) zs P"
  shows "TTMPick xs zs P"
  using assms by (induct xs zs P rule:TTMPick.induct, auto)

lemma TTMPick_imp_prefix':
  assumes "TTMPick (xs @ ys) zs P"
  shows "TTMPick xs zs P"
  using assms by (induct xs zs P rule:TTMPick.induct, auto)

lemma TTMPick_imp_prefix'':
  assumes "TTMPick (xs @ ys) zs P"
  shows "TTMPick ys (zs @ xs) P"
  using assms by (induct xs zs P rule:TTMPick.induct, auto)

lemma TT2_extends_Ref:
  assumes "TT2 P" "s @ [[X]\<^sub>R] @ xs \<in> P"
  shows "s @ [[X \<union> {e. e \<noteq> Tock \<and> s @ [[e]\<^sub>E] \<notin> P \<or> e = Tock \<and> s @ [[X]\<^sub>R, [Tock]\<^sub>E] \<notin> P}]\<^sub>R] @ xs \<in> P"
proof -
  obtain Y where Y:"Y = {e. e \<noteq> Tock \<and> s @ [[e]\<^sub>E] \<notin> P \<or> e = Tock \<and> s @ [[X]\<^sub>R, [Tock]\<^sub>E] \<notin> P}"
    by auto
  then have "Y \<inter> {e. (e \<noteq> Tock \<and> s @ [[e]\<^sub>E] \<in> P) \<or> (e = Tock \<and> s @ [[X]\<^sub>R, [e]\<^sub>E] \<in> P) } = {}"
    by auto
  then have "s @ [[X \<union> Y]\<^sub>R] @ xs \<in> P"
    using assms unfolding TT2_def by auto
  then show ?thesis using Y by auto
qed

lemma tt_prefix_common_concat:
  assumes "zs \<lesssim>\<^sub>C ys"
  shows "xs @ zs \<lesssim>\<^sub>C xs @ ys"
  using assms apply (induct zs ys arbitrary:xs rule:tt_prefix_subset.induct, auto)
  using tt_prefix_concat tt_prefix_imp_prefix_subset apply blast
  apply (meson tt_prefix_subset.simps(2) tt_prefix_subset_same_front)
  by (meson tt_prefix_subset.simps(3) tt_prefix_subset_same_front)

lemma tt_prefix_common_concat_eq_size:
  assumes "zs \<lesssim>\<^sub>C ys" "size zs = size ys"
  shows "zs @ xs \<lesssim>\<^sub>C ys @ xs"
  using assms apply (induct zs ys arbitrary:xs rule:tt_prefix_subset.induct, auto)
  by (simp add: tt_prefix_subset_refl)

lemma TT4_middle_Ref_with_Tick:
  assumes "s @ [[X]\<^sub>R] @ xs \<in> P" "TT1 P" "TT4 P"
  shows "s @ [[X \<union> {Tick}]\<^sub>R] @ xs \<in> P"
proof -
  have add_Tick_in_P:"add_Tick_refusal_trace (s @ [[X]\<^sub>R] @ xs) \<in> P"
    using assms unfolding TT4_def by blast

  have add_Tick_dist:"add_Tick_refusal_trace (s @ [[X]\<^sub>R] @ xs) =
     add_Tick_refusal_trace s @ [[X \<union> {Tick}]\<^sub>R] @ add_Tick_refusal_trace(xs)"
    by (simp add: add_Tick_refusal_trace_concat add_Tick_refusal_trace_end_refusal)
  
  have s_le_addTick:"s \<lesssim>\<^sub>C add_Tick_refusal_trace s"
    by (simp add: add_Tick_refusal_trace_tt_subset tt_subset_imp_prefix_subset)
  have "xs \<lesssim>\<^sub>C add_Tick_refusal_trace(xs)"
    by (simp add: add_Tick_refusal_trace_tt_subset tt_subset_imp_prefix_subset)

  then have a:"add_Tick_refusal_trace s @ [[X \<union> {Tick}]\<^sub>R] @ xs
              \<lesssim>\<^sub>C
              add_Tick_refusal_trace s @ [[X \<union> {Tick}]\<^sub>R] @ add_Tick_refusal_trace(xs)"
  using add_Tick_in_P add_Tick_dist tt_prefix_common_concat
    by blast
  then have b:"s @ [[X \<union> {Tick}]\<^sub>R] @ xs \<lesssim>\<^sub>C add_Tick_refusal_trace s @ [[X \<union> {Tick}]\<^sub>R] @ xs"
    using tt_prefix_common_concat_eq_size add_Tick_refusal_trace_same_length s_le_addTick by blast

  have "s @ [[X \<union> {Tick}]\<^sub>R] @ xs \<in> P"
    using a b add_Tick_in_P assms
    by (metis TT1_def add_Tick_dist)
  then show ?thesis by auto
qed

lemma TT2_TT4_extends_Ref:
  assumes "TT2 P" "TT4 P" "TT1 P" "s @ [[X]\<^sub>R] @ xs \<in> P"
  shows "s @ [[X \<union> {e. e \<noteq> Tock \<and> s @ [[e]\<^sub>E] \<notin> P \<or> e = Tock \<and> s @ [[X]\<^sub>R, [Tock]\<^sub>E] \<notin> P} \<union> {Tick}]\<^sub>R] @ xs \<in> P"
proof -
  obtain Y where Y:"Y = {e. e \<noteq> Tock \<and> s @ [[e]\<^sub>E] \<notin> P \<or> e = Tock \<and> s @ [[X]\<^sub>R, [Tock]\<^sub>E] \<notin> P}"
    by auto
  then have "Y \<inter> {e. (e \<noteq> Tock \<and> s @ [[e]\<^sub>E] \<in> P) \<or> (e = Tock \<and> s @ [[X]\<^sub>R, [e]\<^sub>E] \<in> P) } = {}"
    by auto
  then have "s @ [[X \<union> Y]\<^sub>R] @ xs \<in> P"
    using assms unfolding TT2_def by auto
  then have "s @ [[X \<union> Y \<union> {Tick}]\<^sub>R] @ xs \<in> P"
    using assms TT4_middle_Ref_with_Tick by blast
  then show ?thesis using Y by auto
qed

lemma TTMPick_extend_Ref:
  assumes "TTMPick zs (s @ [[X]\<^sub>R]) P" "TT4 P" "TT2 P" "TT1 P"
  shows "TTMPick zs (s @ [[insert Tick (X \<union> {e. e \<noteq> Tock \<and> s @ [[e]\<^sub>E] \<notin> P \<or> e = Tock \<and> s @ [[X]\<^sub>R, [Tock]\<^sub>E] \<notin> P})]\<^sub>R]) P"
  using assms 
proof (induct zs arbitrary:s X rule:rev_induct)
  case Nil
  then show ?case by auto
next
  case (snoc x xs)
  obtain z where z:"z = (s @ [[X \<union> {e. e \<noteq> Tock \<and> s @ [[e]\<^sub>E] \<notin> P \<or> e = Tock \<and> s @ [[X]\<^sub>R, [Tock]\<^sub>E] \<notin> P} \<union> {Tick}]\<^sub>R])"
      by auto
  then have TTMPick_prefix:"TTMPick xs (s @ [[X]\<^sub>R]) P"
    using snoc TTMPick_imp_prefix by blast
  (*then have "ttWF (s @ [[X]\<^sub>R] @ xs)"
    using snoc by (metis (no_types, hide_lams) append_assoc ttWF_prefix_is_ttWF)*)
  then have "TTMPick xs (s @ [[insert Tick (X \<union> {e. e \<noteq> Tock \<and> s @ [[e]\<^sub>E] \<notin> P \<or> e = Tock \<and> s @ [[X]\<^sub>R, [Tock]\<^sub>E] \<notin> P})]\<^sub>R]) P"
    using snoc TTMPick_prefix by blast
  then have TTMPick_xs_z:"TTMPick xs z P"
    using z by auto

  from snoc have "TTMPick xs (s @ [[X]\<^sub>R]) P"
    using  TTMPick_imp_prefix' by blast
  from snoc have TTMPick_x:"TTMPick [x] (s @ [[X]\<^sub>R] @ xs) P"
    using  TTMPick_imp_prefix''
    by (metis append.assoc)

  then show ?case using snoc
  proof (cases x)
    case (ObsEvent x1)
    then show ?thesis
      using TTMPick_extend_event_imp \<open>TTMPick xs (s @ [[insert Tick (X \<union> {e. e \<noteq> Tock \<and> s @ [[e]\<^sub>E] \<notin> P \<or> e = Tock \<and> s @ [[X]\<^sub>R, [Tock]\<^sub>E] \<notin> P})]\<^sub>R]) P\<close> by blast
  next
    case (Ref x2)
    
    then have "\<forall>e. e \<noteq> Tock \<and> e \<notin> x2 \<longrightarrow> s @ [[X]\<^sub>R] @ xs @ [[e]\<^sub>E] \<in> P"
      using TTMPick_x Ref by auto
    then have "\<forall>e. e \<noteq> Tock \<and> e \<notin> x2 \<longrightarrow> s @ [[X \<union> {e. e \<noteq> Tock \<and> s @ [[e]\<^sub>E] \<notin> P \<or> e = Tock \<and> s @ [[X]\<^sub>R, [Tock]\<^sub>E] \<notin> P} \<union> {Tick}]\<^sub>R] @ xs @ [[e]\<^sub>E] \<in> P"
      using assms TT2_TT4_extends_Ref by blast
    then have a:"\<forall>e. e \<noteq> Tock \<and> e \<notin> x2 \<longrightarrow> z @ xs @ [[e]\<^sub>E] \<in> P"
      using z by auto

    from z have "Tock \<notin> x2 \<longrightarrow> s @ [[X]\<^sub>R] @ xs @ [[x2]\<^sub>R, [Tock]\<^sub>E] \<in> P"
      using TTMPick_x Ref by auto
    then have "Tock \<notin> x2 \<longrightarrow> s @ [[X \<union> {e. e \<noteq> Tock \<and> s @ [[e]\<^sub>E] \<notin> P \<or> e = Tock \<and> s @ [[X]\<^sub>R, [Tock]\<^sub>E] \<notin> P} \<union> {Tick}]\<^sub>R] @ xs @ [[x2]\<^sub>R, [Tock]\<^sub>E] \<in> P"
      using assms TT2_TT4_extends_Ref by blast
    then have b:"Tock \<notin> x2 \<longrightarrow> z @ xs @ [[x2]\<^sub>R, [Tock]\<^sub>E] \<in> P"
      using z by auto

    have c:"Tick \<in> x2"
      using TTMPick_x Ref by auto
    then have "TTMPick (xs @ [[x2]\<^sub>R]) z P"
      using TTMPick_extend_ref_imp a b c Ref TTMPick_xs_z by blast
    then show ?thesis using Ref z by auto
  qed
qed
 
lemma TT2_imp_TTMPick_mkTTMP:
  assumes "TT2 P" "TT4 P" "TT1 P"
  shows "TTMPick (mkTTMP xs z P) z P"
  using assms
proof (induct xs z P rule:mkTTMP.induct)
  case (1 s P)
  then show ?case by auto
next
  case (2 X xs s P)
  (*then have "TTMPick (mkTTMP xs (s @ [[X]\<^sub>R]) P) (s @ [[X]\<^sub>R]) P"
    by auto
  have "([X \<union> {e. (e \<noteq> Tock \<and> s @ [[e]\<^sub>E] \<notin> P) \<or> (e = Tock \<and> s @ [[X]\<^sub>R,[Tock]\<^sub>E] \<notin> P)} \<union> {Tick}]\<^sub>R 
        # mkTTMP xs (s @ [[X]\<^sub>R]) P) = (mkTTMP ([X]\<^sub>R # xs) s P)"
    by auto

  obtain Z where Z:"Z = X \<union> {e. (e \<noteq> Tock \<and> s @ [[e]\<^sub>E] \<notin> P) \<or> (e = Tock \<and> s @ [[X]\<^sub>R,[Tock]\<^sub>E] \<notin> P)} \<union> {Tick}"
    by auto
  have "TTMPick ([Z]\<^sub>R # (mkTTMP xs (s @ [[X]\<^sub>R]) P)) s P
        =
        ((\<forall>e. e \<notin> Z \<and> e \<noteq> Tock \<longrightarrow> s @ [[e]\<^sub>E] \<in> P)
         \<and>
         (Tock \<notin> Z \<longrightarrow> s @ [[Z]\<^sub>R,[Tock]\<^sub>E] \<in> P) \<and> Tick \<in> Z \<and> TTMPick (mkTTMP xs (s @ [[X]\<^sub>R]) P) (s @ [[Z]\<^sub>R]) P)"
    by auto
  from Z have "Tick \<in> Z"
    by auto
  from Z have "(Tock \<notin> Z \<longrightarrow> s @ [[Z]\<^sub>R,[Tock]\<^sub>E] \<in> P)"
    sledgehammer*)
  then show ?case
  proof (auto)
    assume "TT1 P" "TT4 P" "TT2 P" "s @ [[X]\<^sub>R, [Tock]\<^sub>E] \<in> P"
    then show "s @ [[insert Tick (X \<union> {e. e \<noteq> Tock \<and> s @ [[e]\<^sub>E] \<notin> P})]\<^sub>R, [Tock]\<^sub>E] \<in> P"
      using TT2_Ref_Tock_augment assms by auto
  next
    assume healths:"TT1 P" "TT4 P" "TT2 P" "TTMPick (mkTTMP xs (s @ [[X]\<^sub>R]) P) (s @ [[X]\<^sub>R]) P"
    obtain z where z:"z = (mkTTMP xs (s @ [[X]\<^sub>R]) P)" by auto
    then have "TTMPick z (s @ [[insert Tick (X \<union> {e. e \<noteq> Tock \<and> s @ [[e]\<^sub>E] \<notin> P 
                                                      \<or> e = Tock \<and> s @ [[X]\<^sub>R, [Tock]\<^sub>E] \<notin> P})]\<^sub>R]) P"
      using healths TTMPick_extend_Ref by blast
    then show "TTMPick (mkTTMP xs (s @ [[X]\<^sub>R]) P)
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
  "TTickTrace (mkTTMP (add_Tick_refusal_trace s) i P)"
proof (induct s i P rule:mkTTMP.induct)
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
lemma TTM3_mkTTMP_singleton:
  "TTM3 {(mkTTMP s i P)}"
  unfolding TTM3_def by (induct s i P rule:mkTTMP.induct, auto)

lemma prirelref_prirelrefSub_part:
  assumes "TT3 Q"
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
      using TT3_any_cons_end_tock by blast
    finally show ?thesis .
  qed

lemma prirelref_prirelrefSub:
  assumes "TT3 Q"
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
  assumes "TT1 P" "TT2 P" "TT4 P" "prirelRef pa t s (sa @ zs) (unTT1 Q)"
  shows "prirelRef pa t s (sa @ (mkTTMP zs sa Q)) (unTT1 Q)"
  using assms apply (induct pa t s zs Q arbitrary: sa rule:prirelRef.induct, auto)
*)

lemma TTMPick_imp_TTickTrace:
  assumes "TTMPick s i P"
  shows "TTickTrace s"
  using assms by (induct s i P rule:TTMPick.induct, auto)

lemma TTM3_TTMPick:
  assumes "TTMPick (s) [] P"
  shows "TTM3 {s}"
  using assms unfolding TTM3_def apply auto
  using TTMPick_imp_TTickTrace by blast

lemma TTMPick_extends_concat:
  assumes "TTMPick ys (i @ xs) P" "TTMPick xs i P"
  shows "TTMPick (xs @ ys) i P"
  using assms by (induct xs i P rule:TTMPick.induct, auto)

(* How to remove TTMPick s [] P from the following lemma? I suspect the
   key result could only be proved when considering the full definition of
   priNS in this model, whereby we take specific 's' and not arbitrary ones. *)
lemma prirelRef_unTT1_case:
  assumes "TT1 P" "TT4w P"
  shows 
  "(s @ [[Z]\<^sub>R] \<in> unTT1 P \<and> e\<^sub>2 \<notin> Z \<and> \<not>(\<exists>b. b \<notin> Z \<and> e\<^sub>2 <\<^sup>*p b))
   =
   (s @ [[Z]\<^sub>R] \<in> P \<and> TTMPick s [] P \<and> e\<^sub>2 \<notin> Z \<and> \<not>(\<exists>b. b \<notin> Z \<and> e\<^sub>2 <\<^sup>*p b)
          \<and> (\<forall>e. e \<notin> Z \<and> e \<noteq> Tock \<longrightarrow> s @ [[e]\<^sub>E] \<in> P)
          \<and> (Tock \<notin> Z \<longrightarrow> s @ [[Z]\<^sub>R,[Tock]\<^sub>E] \<in> P) \<and> Tick \<in> Z)"
proof -
  have "(s @ [[Z]\<^sub>R] \<in> unTT1 P \<and> e\<^sub>2 \<notin> Z \<and> \<not>(\<exists>b. b \<notin> Z \<and> e\<^sub>2 <\<^sup>*p b))
        =
        (s @ [[Z]\<^sub>R] \<in> P \<and> TTM3 {s @ [[Z]\<^sub>R]} \<and> TTMPick (s @ [[Z]\<^sub>R]) [] P \<and> e\<^sub>2 \<notin> Z \<and> \<not>(\<exists>b. b \<notin> Z \<and> e\<^sub>2 <\<^sup>*p b))"
    using assms TT14_TTick_mkTT1_exists by blast
  also have "... = 
      (s @ [[Z]\<^sub>R] \<in> P \<and> TTMPick (s @ [[Z]\<^sub>R]) [] P \<and> e\<^sub>2 \<notin> Z \<and> \<not>(\<exists>b. b \<notin> Z \<and> e\<^sub>2 <\<^sup>*p b))"
    using TTM3_TTMPick by blast
    (* Here need to show that TTMPick is sufficient on the refusal Z, we do not need
       to find such 's'? *)
  also have "... = 
      (s @ [[Z]\<^sub>R] \<in> P \<and> TTMPick s [] P \<and> TTMPick [[Z]\<^sub>R] s P \<and> e\<^sub>2 \<notin> Z \<and> \<not>(\<exists>b. b \<notin> Z \<and> e\<^sub>2 <\<^sup>*p b))"
    by (metis TTMPick_extends_concat TTMPick_imp_prefix TTMPick_imp_prefix'' self_append_conv2)
  also have "... = 
      (s @ [[Z]\<^sub>R] \<in> P \<and> TTMPick s [] P \<and> e\<^sub>2 \<notin> Z \<and> \<not>(\<exists>b. b \<notin> Z \<and> e\<^sub>2 <\<^sup>*p b)
          \<and> (\<forall>e. e \<notin> Z \<and> e \<noteq> Tock \<longrightarrow> s @ [[e]\<^sub>E] \<in> P)
          \<and> (Tock \<notin> Z \<longrightarrow> s @ [[Z]\<^sub>R,[Tock]\<^sub>E] \<in> P) \<and> Tick \<in> Z)"
    by auto
  finally show ?thesis .
qed

lemma
  "aa \<lesssim>\<^sub>C (mkTTMP aa i P)"
  by (induct aa i P rule:mkTTMP.induct, auto)

lemma
  assumes "prirelRef2 p ([R]\<^sub>R # [Tock]\<^sub>E # aa) ([S]\<^sub>R # [Tock]\<^sub>E # zz) s Q" "TTMPick s [] Q" "TT1 Q" "TT2 Q" "TT4 Q"
  shows "TTMPick (s @ [[S]\<^sub>R,[Tock]\<^sub>E]) [] Q"
  using assms apply(induct p aa zz s Q arbitrary:S R rule:prirelRef2.induct, auto)
  oops

(* Too strong, as in general it is not possible to pick a trace 'aa' and apply
    mkTTMP to it and get a satisfactory result in prirelRef, I think? Because
    such closure woult be based on the trace in P, which are not necessarily
    available after prioritisation. So it is non-trivial to construct the 
    appropriate sets, in general. This has to come from prirelRef2 itself.
lemma
  assumes "prirelRef2 pa aa zz i P" "TT4 P" "TT3 P" "TT2 P" "TT1 P" 
  shows "prirelRef pa (mkTTMP aa i P) (mkTTMP zz i P) i (unTT1 P)"
  using assms proof(induct pa aa zz i P rule:prirelRef2.induct, simp_all)
  fix p 
  fix R::"'a ttevent set"
  fix S s Q
  assume TT4_healthy: "TT4 Q"
     and TT3_healthy:  "TT3 Q"
     and TT2_healthy: "TT2 Q"
     and TT1_healthy:  "TT1 Q"
     and prirelRef:    "R \<subseteq> prirelrefSub p S s Q"
  then show "prirelref p (insert Tick (S \<union> {e. e \<noteq> Tock \<and> s @ [[e]\<^sub>E] \<notin> Q \<or> e = Tock \<and> s @ [[S]\<^sub>R, [Tock]\<^sub>E] \<notin> Q})) =
       insert Tick (R \<union> {e. e \<noteq> Tock \<and> s @ [[e]\<^sub>E] \<notin> Q \<or> e = Tock \<and> s @ [[R]\<^sub>R, [Tock]\<^sub>E] \<notin> Q})"
  proof -
    have "prirelref p (insert Tick (S \<union> {e. e \<noteq> Tock \<and> s @ [[e]\<^sub>E] \<notin> Q \<or> e = Tock \<and> s @ [[S]\<^sub>R, [Tock]\<^sub>E] \<notin> Q}))
          =
          prirelrefSub p S s Q"
      using TT3_healthy prirelref_prirelrefSub by fastforce
    have "{e. e \<noteq> Tock \<and> s @ [[e]\<^sub>E] \<notin> Q \<or> e = Tock \<and> s @ [[S]\<^sub>R, [Tock]\<^sub>E] \<notin> Q} \<union> {Tick} \<subseteq> prirelrefSub p S s Q"
      using \<open>prirelref p (insert Tick (S \<union> {e. e \<noteq> Tock \<and> s @ [[e]\<^sub>E] \<notin> Q \<or> e = Tock \<and> s @ [[S]\<^sub>R, [Tock]\<^sub>E] \<notin> Q})) = prirelrefSub p S s Q\<close> prirelref_def by auto
    have "prirelrefSub p S s Q \<subseteq> R \<union> {e. e \<noteq> Tock \<and> s @ [[e]\<^sub>E] \<notin> Q \<or> e = Tock \<and> s @ [[R]\<^sub>R, [Tock]\<^sub>E] \<notin> Q} \<union> {Tick}"
      using prirelRef  apply auto
    apply (simp_all add: prirelrefSub_def)
  oops
*)

lemma mkTTMP_dist_concat:
  "mkTTMP (xs @ [x]) i P = (mkTTMP xs i P) @ mkTTMP [x] (i @ xs) P"
  by (induct xs i P arbitrary:x rule:mkTTMP.induct, auto)

lemma mkTTMP_fixpoint_eq_TTMPick:
  "(mkTTMP s i P = s) = TTMPick s i P"
  by (induct s i P rule:mkTTMP.induct, auto)

lemma TT2_aux1:
  assumes "TT2 P" "\<rho> @ [[X]\<^sub>R] @ \<sigma> \<in> P" "Y \<inter> {e. (e \<noteq> Tock \<and> \<rho> @ [[e]\<^sub>E] \<in> P) \<or> (e = Tock \<and> \<rho> @ [[X]\<^sub>R, [e]\<^sub>E] \<in> P) } = {}"
  shows "\<rho> @ [[X \<union> Y]\<^sub>R] @ \<sigma> \<in> P"
  using assms TT2_def by blast

lemma TT2_aux2:
  assumes "TT2 P" "[[X]\<^sub>R] @ \<sigma> \<in> P" "Y \<inter> {e. (e \<noteq> Tock \<and> [[e]\<^sub>E] \<in> P) \<or> (e = Tock \<and> [[X]\<^sub>R, [e]\<^sub>E] \<in> P) } = {}"
  shows "[[X \<union> Y]\<^sub>R] @ \<sigma> \<in> P"
  using assms TT2_def by (metis (no_types, lifting) Collect_cong append.left_neutral)

lemma TT2_aux3:
  assumes "TT2 P" "[[X]\<^sub>R] \<in> P" "Y \<inter> {e. (e \<noteq> Tock \<and> [[e]\<^sub>E] \<in> P) \<or> (e = Tock \<and> [[X]\<^sub>R, [e]\<^sub>E] \<in> P) } = {}"
  shows "[[X \<union> Y]\<^sub>R] \<in> P"
  using TT2_aux2 assms(1) assms(2) assms(3) by auto

thm list.induct
thm rev_induct
thm mkTTMP.induct
thm wf_TT2_induct

lemma mkTTMP_absorb_event:
  "mkTTMP xs i P @ ([[x]\<^sub>E] @ z) = mkTTMP (xs @ [[x]\<^sub>E]) i P @ z"
  by (induct xs i P arbitrary:x z rule:mkTTMP.induct, auto)

lemma mkTTMP_absorb_ref:
(*  assumes "Tick \<in> x" 
          "\<forall>xa. (xa \<noteq> Tock \<and> xs @ [[xa]\<^sub>E] \<notin> P) \<longrightarrow> xa \<in> x"
          "xs @ [[x]\<^sub>R, [Tock]\<^sub>E] \<notin> P \<longrightarrow> Tock \<in> x"*)
  shows "mkTTMP xs i P @ ([[x \<union> {e. (e \<noteq> Tock \<and> i @ xs @ [[e]\<^sub>E] \<notin> P) 
                                \<or> (e = Tock \<and> i @ xs @ [[x]\<^sub>R,[Tock]\<^sub>E] \<notin> P)} 
                               \<union> {Tick}]\<^sub>R] @ z) 
         = 
         mkTTMP (xs @ [[x]\<^sub>R]) i P @ z"
  by (induct xs i P arbitrary:x z rule:mkTTMP.induct, simp_all)

lemma mkTTMP_absorb_ref':
(*  assumes "Tick \<in> x" 
          "\<forall>xa. (xa \<noteq> Tock \<and> xs @ [[xa]\<^sub>E] \<notin> P) \<longrightarrow> xa \<in> x"
          "xs @ [[x]\<^sub>R, [Tock]\<^sub>E] \<notin> P \<longrightarrow> Tock \<in> x"*)
  shows "mkTTMP xs i P @ ([[x \<union> {e. (e \<noteq> Tock \<and> i @ xs @ [[e]\<^sub>E] \<notin> P) 
                                \<or> (e = Tock \<and> i @ xs @ [[x]\<^sub>R,[Tock]\<^sub>E] \<notin> P)} 
                               \<union> {Tick}]\<^sub>R] ) 
         = 
         mkTTMP (xs @ [[x]\<^sub>R]) i P"
  by (induct xs i P arbitrary:x rule:mkTTMP.induct, simp_all)


lemma
  assumes "mkTTMP (xs @ [[e]\<^sub>E]) i P \<in> P"
  shows "i @ xs @ [[e]\<^sub>E] \<in> P"
  using assms apply (induct xs arbitrary:i e rule:rev_induct, auto)
  oops

lemma prefix_mkTTMP:
  "aa \<lesssim>\<^sub>C (mkTTMP aa i P)"
  by (induct aa i P rule:mkTTMP.induct, auto)

lemma mkTTMP_concat_event_TT1_imp:
  assumes "mkTTMP xs [] P @ [[e]\<^sub>E] \<in> P" "TT1 P"
  shows "xs @ [[e]\<^sub>E] \<in> P"
proof -
  have "xs \<lesssim>\<^sub>C mkTTMP xs [] P"
    using assms prefix_mkTTMP by auto
  then have "xs @ [[e]\<^sub>E] \<lesssim>\<^sub>C mkTTMP xs [] P @ [[e]\<^sub>E]"
    by (metis append.right_neutral mkTTMP_absorb_event prefix_mkTTMP)
  then show ?thesis using assms
    using TT1_def by blast
qed

lemma mkTTMP_eq_size:
  "size xs = (size (mkTTMP xs i P))"
  by (induct xs i P rule:mkTTMP.induct, auto)

lemma mkTTMP_concat_ref_Tock_TT1_imp:
  assumes "mkTTMP xs [] P @ [[x2]\<^sub>R, [Tock]\<^sub>E] \<in> P" "TT1 P"
  shows "xs @ [[x2]\<^sub>R, [Tock]\<^sub>E] \<in> P"
proof -
  have "xs \<lesssim>\<^sub>C mkTTMP xs [] P"
    using assms prefix_mkTTMP by auto
  then have "xs @ [[x2]\<^sub>R, [Tock]\<^sub>E] \<lesssim>\<^sub>C mkTTMP xs [] P @ [[x2]\<^sub>R, [Tock]\<^sub>E]"
    using mkTTMP_eq_size tt_prefix_common_concat_eq_size by blast
  then show ?thesis using assms
    using TT1_def by blast
qed

lemma mkTTMP_in_P:
  assumes "s @ z \<in> P" "TT4 P" "TT3 P" "TT2 P" "TT1 P"
  shows "(mkTTMP s [] P) @ z \<in> P"
  using assms
proof (induct s arbitrary:z P rule:rev_induct)
  case Nil
  then show ?case by auto
next
  case (snoc x xs)
  then have mkTTMP_hyp:"mkTTMP xs [] P @ ([x] @ z) \<in> P"
    by auto
  then show ?case
  proof (cases x)
    case (ObsEvent x1)
    then have "mkTTMP xs [] P @ ([x] @ z) = mkTTMP (xs @ [x]) [] P @ z"
      using mkTTMP_absorb_event by auto
    then show ?thesis using mkTTMP_hyp
      by presburger
  next
    case (Ref x2)
    then obtain y where y:"y = mkTTMP xs [] P"
      by auto
    then have y_cons:"y @ [[x2]\<^sub>R] @ z \<in> P"
      using Ref mkTTMP_hyp by auto
    have "{e. (e \<noteq> Tock \<and> xs @ [[e]\<^sub>E] \<notin> P) \<or> (e = Tock \<and> xs @ [[x2]\<^sub>R,[Tock]\<^sub>E] \<notin> P)} 
            \<inter>
            {e. (e \<noteq> Tock \<and> y @ [[e]\<^sub>E] \<in> P) \<or> (e = Tock \<and> y @ [[x2]\<^sub>R, [e]\<^sub>E] \<in> P) } = {}"
      apply auto
      using snoc mkTTMP_concat_event_TT1_imp y apply blast
      using snoc mkTTMP_concat_ref_Tock_TT1_imp y by blast
    then have "y @ [[x2 \<union> {e. (e \<noteq> Tock \<and> xs @ [[e]\<^sub>E] \<notin> P) \<or> (e = Tock \<and> xs @ [[x2]\<^sub>R,[Tock]\<^sub>E] \<notin> P)}]\<^sub>R] @ z \<in> P"
      using y_cons TT2_def snoc.prems(4) sup_set_def by blast
    then have "y @ [[x2 \<union> {e. (e \<noteq> Tock \<and> xs @ [[e]\<^sub>E] \<notin> P) \<or> (e = Tock \<and> xs @ [[x2]\<^sub>R,[Tock]\<^sub>E] \<notin> P)} \<union> {Tick}]\<^sub>R] @ z \<in> P"
      using TT4_def by (meson TT4_middle_Ref_with_Tick snoc.prems(2) snoc.prems(5))
    then have "mkTTMP (xs @ [[x2]\<^sub>R]) [] P @ z \<in> P"
      using y mkTTMP_absorb_ref
      by (smt Collect_cong append_self_conv2)
    then show ?thesis using Ref by blast
  qed
qed

lemma TTs_mkTTMP_in_P:
  assumes "s \<in> P" "TT4 P" "TT3 P" "TT2 P" "TT1 P"
  shows "(mkTTMP s [] P) \<in> P"
  using assms mkTTMP_in_P
  by (metis append_Nil2)

lemma prirelRef_unTT1_case_specific:
  assumes "TT4 P" "TT3 P" "TT2 P" "TT1 P"
          "(\<forall>e. e \<notin> Z \<and> e \<noteq> Tock \<longrightarrow> s @ [[e]\<^sub>E] \<in> P)"
          "(Tock \<notin> Z \<longrightarrow> s @ [[Z]\<^sub>R,[Tock]\<^sub>E] \<in> P)"
          "Tick \<in> Z"
          "(mkTTMP s [] P) @ [[Z]\<^sub>R] \<in> P"
  shows 
  "(mkTTMP s [] P) @ [[Z]\<^sub>R] \<in> unTT1 P"
proof -
  have "((mkTTMP s [] P) @ [[Z]\<^sub>R] \<in> unTT1 P)
        =
        ((mkTTMP s [] P) @ [[Z]\<^sub>R] \<in> (\<Union>{x. TTM1 x \<and> TTM2 x \<and> TTM3 x \<and> TT1w x \<and> (mkTT1 x) \<subseteq> P}))"
    unfolding unTT1_def by auto
  also have "... = 
       (\<exists>x. (mkTTMP s [] P) @ [[Z]\<^sub>R] \<in> x \<and> TTM1 x \<and> TTM2 x \<and> TTM3 x \<and> TT1w x \<and> (mkTT1 x) \<subseteq> P)"
    by auto
  also have "... =
       ((mkTTMP s [] P) @ [[Z]\<^sub>R] \<in> P \<and> TTM3 {(mkTTMP s [] P) @ [[Z]\<^sub>R]} \<and> TTMPick ((mkTTMP s [] P) @ [[Z]\<^sub>R]) [] P)"
    using assms TTM3_mkTT1_simp TT4_TT1_imp_TT4w by auto
  also have "... =
       ((mkTTMP s [] P) @ [[Z]\<^sub>R] \<in> P \<and> TTMPick ((mkTTMP s [] P) @ [[Z]\<^sub>R]) [] P)"
    using TTM3_TTMPick by blast
  also have "... =
       ((mkTTMP s [] P) @ [[Z]\<^sub>R] \<in> P)"
  proof -
    have "Z = Z \<union> {e. e \<noteq> Tock \<and> s @ [[e]\<^sub>E] \<notin> P \<or> e = Tock \<and> s @ [[Z]\<^sub>R, [Tock]\<^sub>E] \<notin> P} \<union> {Tick}"
      using assms by auto
    then have "(mkTTMP s [] P) @ [[Z]\<^sub>R] = (mkTTMP s [] P) @ [[Z \<union> {e. e \<noteq> Tock \<and> s @ [[e]\<^sub>E] \<notin> P \<or> e = Tock \<and> s @ [[Z]\<^sub>R, [Tock]\<^sub>E] \<notin> P} \<union> {Tick}]\<^sub>R]"
      by auto
    also have "... = (mkTTMP (s @ [[Z]\<^sub>R]) [] P)"
      using mkTTMP_absorb_ref'
      by (simp add: mkTTMP_dist_concat)
    then have "TTMPick ((mkTTMP s [] P) @ [[Z]\<^sub>R]) [] P"
      by (simp add: TT2_imp_TTMPick_mkTTMP assms(1) assms(3) assms(4) calculation)
    then show ?thesis by auto
  qed

  finally show ?thesis using assms by auto 
qed

lemma TTMPick_Refusal_subset:
  assumes "TTMPick (xs @ [[Sa]\<^sub>R] @ ys) i Q"
  shows "{e. e \<noteq> Tock \<and> i @ xs @ [[e]\<^sub>E] \<notin> Q \<or> e = Tock \<and> i @ xs @ [[Sa]\<^sub>R, [Tock]\<^sub>E] \<notin> Q} \<union> {Tick} \<subseteq> Sa"
  using assms by (induct xs i Q rule:TTMPick.induct, auto)

lemma TTMPick_Refusal_extend:
  assumes "TTMPick (xs @ [[Sa]\<^sub>R] @ ys) i Q"
  shows "TTMPick (xs @ [[Sa \<union> {e. e \<noteq> Tock \<and> i @ xs @ [[e]\<^sub>E] \<notin> Q \<or> e = Tock \<and> i @ xs @ [[Sa]\<^sub>R, [Tock]\<^sub>E] \<notin> Q} \<union> {Tick}]\<^sub>R] @ ys) i Q"
  using assms TTMPick_Refusal_subset
  by (smt Un_absorb2 le_supE mem_Collect_eq subset_eq)

lemma concat_unTT1_extend_TT2_Refusal:
  assumes "xs @ [[Sa]\<^sub>R] @ ys \<in> unTT1 Q" "TT2 Q" "TT1 Q" "TT4w Q"
  shows "xs @ [[Sa \<union> {e. e \<noteq> Tock \<and> xs @ [[e]\<^sub>E] \<notin> Q \<or> e = Tock \<and> xs @ [[Sa]\<^sub>R, [Tock]\<^sub>E] \<notin> Q} \<union> {Tick}]\<^sub>R] @ ys \<in> unTT1 Q"
proof -
  have "xs @ [[Sa]\<^sub>R] @ ys \<in> unTT1 Q 
        = 
        (xs @ [[Sa]\<^sub>R] @ ys \<in> (\<Union>{x. TTM1 x \<and> TTM2 x \<and> TTM3 x \<and> TT1w x \<and> (mkTT1 x) \<subseteq> Q}))"
    unfolding unTT1_def by auto
  also have "... = (\<exists>x. xs @ [[Sa]\<^sub>R] @ ys \<in> x \<and> TTM1 x \<and> TTM2 x \<and> TTM3 x \<and> TT1w x \<and> (mkTT1 x) \<subseteq> Q)"
    by auto
  also have "... = (xs @ [[Sa]\<^sub>R] @ ys \<in> Q \<and> TTM3 {xs @ [[Sa]\<^sub>R] @ ys} \<and> TTMPick (xs @ [[Sa]\<^sub>R] @ ys) [] Q)"
    using TTM3_mkTT1_simp assms by blast
  also have "... = (xs @ [[Sa]\<^sub>R] @ ys \<in> Q \<and> TTMPick (xs @ [[Sa]\<^sub>R] @ ys) [] Q)"
    using assms TTM3_TTMPick by blast
  then have "(xs @ [[Sa]\<^sub>R] @ ys \<in> Q \<and> TTMPick (xs @ [[Sa]\<^sub>R] @ ys) [] Q)"
    using assms calculation by auto
  then have "(xs @ [[Sa \<union> {e. e \<noteq> Tock \<and> xs @ [[e]\<^sub>E] \<notin> Q \<or> e = Tock \<and> xs @ [[Sa]\<^sub>R, [Tock]\<^sub>E] \<notin> Q}]\<^sub>R] @ ys \<in> Q 
                    \<and> TTMPick (xs @ [[Sa]\<^sub>R] @ ys) [] Q)"
    using assms TT2_extends_Ref by fastforce
  then have "(xs @ [[Sa \<union> {e. e \<noteq> Tock \<and> xs @ [[e]\<^sub>E] \<notin> Q \<or> e = Tock \<and> xs @ [[Sa]\<^sub>R, [Tock]\<^sub>E] \<notin> Q} \<union> {Tick}]\<^sub>R] @ ys \<in> Q 
                    \<and> TTMPick (xs @ [[Sa]\<^sub>R] @ ys) [] Q)"
    using TTMPick_imp_prefix'' insert_absorb by fastforce
  then have "(xs @ [[Sa \<union> {e. e \<noteq> Tock \<and> xs @ [[e]\<^sub>E] \<notin> Q \<or> e = Tock \<and> xs @ [[Sa]\<^sub>R, [Tock]\<^sub>E] \<notin> Q} \<union> {Tick}]\<^sub>R] @ ys \<in> Q 
                    \<and> TTMPick (xs @ [[Sa \<union> {e. e \<noteq> Tock \<and> xs @ [[e]\<^sub>E] \<notin> Q \<or> e = Tock \<and> xs @ [[Sa]\<^sub>R, [Tock]\<^sub>E] \<notin> Q} \<union> {Tick}]\<^sub>R] @ ys) [] Q)"
    using TTMPick_Refusal_extend by fastforce
  then have "(xs @ [[Sa \<union> {e. e \<noteq> Tock \<and> xs @ [[e]\<^sub>E] \<notin> Q \<or> e = Tock \<and> xs @ [[Sa]\<^sub>R, [Tock]\<^sub>E] \<notin> Q} \<union> {Tick}]\<^sub>R] @ ys \<in> Q 
                    \<and> TTM3 {xs @ [[Sa \<union> {e. e \<noteq> Tock \<and> xs @ [[e]\<^sub>E] \<notin> Q \<or> e = Tock \<and> xs @ [[Sa]\<^sub>R, [Tock]\<^sub>E] \<notin> Q} \<union> {Tick}]\<^sub>R] @ ys}
                    \<and> TTMPick (xs @ [[Sa \<union> {e. e \<noteq> Tock \<and> xs @ [[e]\<^sub>E] \<notin> Q \<or> e = Tock \<and> xs @ [[Sa]\<^sub>R, [Tock]\<^sub>E] \<notin> Q} \<union> {Tick}]\<^sub>R] @ ys) [] Q)"
    using assms TTM3_TTMPick by blast
  then have a:"(\<exists>x. xs @ [[Sa \<union> {e. e \<noteq> Tock \<and> xs @ [[e]\<^sub>E] \<notin> Q \<or> e = Tock \<and> xs @ [[Sa]\<^sub>R, [Tock]\<^sub>E] \<notin> Q} \<union> {Tick}]\<^sub>R] @ ys \<in> Q 
                \<and> TTM1 x \<and> TTM2 x \<and> TTM3 x \<and> TT1w x \<and> (mkTT1 x) \<subseteq> Q)"
    using TTM3_mkTT1_simp assms by blast

  then have "(\<exists>x. xs @ [[Sa \<union> {e. e \<noteq> Tock \<and> xs @ [[e]\<^sub>E] \<notin> Q \<or> e = Tock \<and> xs @ [[Sa]\<^sub>R, [Tock]\<^sub>E] \<notin> Q} \<union> {Tick}]\<^sub>R] @ ys \<in> Q 
                \<and> TTM1 x \<and> TTM2 x \<and> TTM3 x \<and> TT1w x \<and> (mkTT1 x) \<subseteq> Q)
              =
              (xs @ [[Sa \<union> {e. e \<noteq> Tock \<and> xs @ [[e]\<^sub>E] \<notin> Q \<or> e = Tock \<and> xs @ [[Sa]\<^sub>R, [Tock]\<^sub>E] \<notin> Q} \<union> {Tick}]\<^sub>R] @ ys
              \<in> (\<Union>{x. TTM1 x \<and> TTM2 x \<and> TTM3 x \<and> TT1w x \<and> (mkTT1 x) \<subseteq> Q}))"
    apply auto
    using TTM3_TTMPick TTM3_mkTT1_simp \<open>xs @ [[Sa \<union> {e. e \<noteq> Tock \<and> xs @ [[e]\<^sub>E] \<notin> Q \<or> e = Tock \<and> xs @ [[Sa]\<^sub>R, [Tock]\<^sub>E] \<notin> Q} \<union> {Tick}]\<^sub>R] @ ys \<in> Q \<and> TTMPick (xs @ [[Sa \<union> {e. e \<noteq> Tock \<and> xs @ [[e]\<^sub>E] \<notin> Q \<or> e = Tock \<and> xs @ [[Sa]\<^sub>R, [Tock]\<^sub>E] \<notin> Q} \<union> {Tick}]\<^sub>R] @ ys) [] Q\<close> assms(3) assms(4) by fastforce
  then have "(xs @ [[Sa \<union> {e. e \<noteq> Tock \<and> xs @ [[e]\<^sub>E] \<notin> Q \<or> e = Tock \<and> xs @ [[Sa]\<^sub>R, [Tock]\<^sub>E] \<notin> Q} \<union> {Tick}]\<^sub>R] @ ys
              \<in> (\<Union>{x. TTM1 x \<and> TTM2 x \<and> TTM3 x \<and> TT1w x \<and> (mkTT1 x) \<subseteq> Q}))"
    using a by auto
  then have "xs @ [[Sa \<union> {e. e \<noteq> Tock \<and> xs @ [[e]\<^sub>E] \<notin> Q \<or> e = Tock \<and> xs @ [[Sa]\<^sub>R, [Tock]\<^sub>E] \<notin> Q} \<union> {Tick}]\<^sub>R] @ ys \<in> unTT1 Q"
    unfolding unTT1_def by auto
  then show ?thesis .
qed

lemma prirelRef_start_Ref_extends:
  assumes "TT1 Q" "TT2 Q" "TT4w Q" "prirelRef pa t s (sa @ [[S]\<^sub>R, [Tock]\<^sub>E] @ z) (unTT1 Q)" 
  shows "prirelRef pa t s (sa @ [[S \<union> {e. e \<noteq> Tock \<and> sa @ [[e]\<^sub>E] \<notin> Q \<or> e = Tock \<and> sa @ [[S]\<^sub>R, [Tock]\<^sub>E] \<notin> Q} \<union> {Tick}]\<^sub>R, [Tock]\<^sub>E] @ z) (unTT1 Q)"
  using assms proof(induct pa t s z Q arbitrary:S sa rule:prirelRef.induct, auto)
  fix p 
  fix aa::"'a ttobs list" 
  fix e\<^sub>2 zz sb Qa Sa saa Z
  assume 
    hyp:  "(\<And>S sa.
           prirelRef p aa zz (sa @ [S]\<^sub>R # [Tock]\<^sub>E # sb @ [[e\<^sub>2]\<^sub>E]) (unTT1 Qa) \<Longrightarrow>
           prirelRef p aa zz
            (sa @ [insert Tick (S \<union> {e. e \<noteq> Tock \<and> sa @ [[e]\<^sub>E] \<notin> Qa \<or> e = Tock \<and> sa @ [[S]\<^sub>R, [Tock]\<^sub>E] \<notin> Qa})]\<^sub>R # [Tock]\<^sub>E # sb @ [[e\<^sub>2]\<^sub>E])
            (unTT1 Qa))"
    and TT1_healthy:    "TT1 Qa" 
    and TT2_healthy:   "TT2 Qa"
    and TT4w_healthy:   "TT4w Qa"
    and prirelRef:      "prirelRef p aa zz (saa @ [Sa]\<^sub>R # [Tock]\<^sub>E # sb @ [[e\<^sub>2]\<^sub>E]) (unTT1 Qa)"
    and assm1:          "saa @ [Sa]\<^sub>R # [Tock]\<^sub>E # sb @ [[Z]\<^sub>R] \<in> unTT1 Qa"
    and assm2:          "e\<^sub>2 \<notin> Z"
    and assm3:          "\<forall>b. b \<in> Z \<or> \<not> e\<^sub>2 <\<^sup>*p b"
    and assm4:          "\<forall>Z. saa @ [insert Tick (Sa \<union> {e. e \<noteq> Tock \<and> saa @ [[e]\<^sub>E] \<notin> Qa \<or> e = Tock \<and> saa @ [[Sa]\<^sub>R, [Tock]\<^sub>E] \<notin> Qa})]\<^sub>R # [Tock]\<^sub>E # sb @ [[Z]\<^sub>R]
                            \<in> unTT1 Qa \<longrightarrow>
                              e\<^sub>2 \<in> Z \<or> (\<exists>b. b \<notin> Z \<and> e\<^sub>2 <\<^sup>*p b)"
  then show "maximal(p,e\<^sub>2)"
  proof -
    have "saa @ [[Sa]\<^sub>R] @ [Tock]\<^sub>E # sb @ [[Z]\<^sub>R] \<in> unTT1 Qa"
      using assm1 by auto
    then have "saa @ [[Sa \<union> {e. e \<noteq> Tock \<and> saa @ [[e]\<^sub>E] \<notin> Qa \<or> e = Tock \<and> saa @ [[Sa]\<^sub>R, [Tock]\<^sub>E] \<notin> Qa} \<union> {Tick}]\<^sub>R] @ [Tock]\<^sub>E # sb @ [[Z]\<^sub>R] \<in> unTT1 Qa"
      using TT1_healthy TT2_healthy TT4w_healthy concat_unTT1_extend_TT2_Refusal by blast
    then have "saa @ [Sa \<union> {e. e \<noteq> Tock \<and> saa @ [[e]\<^sub>E] \<notin> Qa \<or> e = Tock \<and> saa @ [[Sa]\<^sub>R, [Tock]\<^sub>E] \<notin> Qa} \<union> {Tick}]\<^sub>R # [Tock]\<^sub>E # sb @ [[Z]\<^sub>R] \<in> unTT1 Qa"
      by auto
    then have "\<exists>Z. saa @ [Sa \<union> {e. e \<noteq> Tock \<and> saa @ [[e]\<^sub>E] \<notin> Qa \<or> e = Tock \<and> saa @ [[Sa]\<^sub>R, [Tock]\<^sub>E] \<notin> Qa} \<union> {Tick}]\<^sub>R # [Tock]\<^sub>E # sb @ [[Z]\<^sub>R] \<in> unTT1 Qa \<and> e\<^sub>2 \<notin> Z \<and> \<not>(\<exists>b. b \<notin> Z \<and> e\<^sub>2 <\<^sup>*p b)"
      using assm2 assm3 by blast
    then have "\<not>(\<forall>Z. saa @ [Sa \<union> {e. e \<noteq> Tock \<and> saa @ [[e]\<^sub>E] \<notin> Qa \<or> e = Tock \<and> saa @ [[Sa]\<^sub>R, [Tock]\<^sub>E] \<notin> Qa} \<union> {Tick}]\<^sub>R # [Tock]\<^sub>E # sb @ [[Z]\<^sub>R] \<in> unTT1 Qa \<longrightarrow> e\<^sub>2 \<in> Z \<or> (\<exists>b. b \<notin> Z \<and> e\<^sub>2 <\<^sup>*p b))"
      by blast
    (* Show contradiction *)
    then show ?thesis using assm4 by auto
  qed
qed

(*
lemma prirelRef_start_Ref_extends:
  assumes "TT1 Q" "TT2 Q" "TT4w Q" "prirelRef pa t s ((mkTTMP zs [] Q) @ z) (unTT1 Q)" 
  shows "prirelRef pa t s (zs @ z) (unTT1 Q)"
  using assms proof(induct pa t s z Q arbitrary:zs rule:prirelRef.induct, auto)
  fix p 
  fix aa::"'a ttobs list" 
  fix e\<^sub>2 zz sa Qa zsa Z
  assume 
    hyp:  "(\<And>zs. prirelRef p aa zz (mkTTMP zs [] Qa @ sa @ [[e\<^sub>2]\<^sub>E]) (unTT1 Qa) \<Longrightarrow> prirelRef p aa zz (zs @ sa @ [[e\<^sub>2]\<^sub>E]) (unTT1 Qa))"
    and TT1_healthy:    "TT1 Qa" 
    and TT2_healthy:   "TT2 Qa"
    and TT4w_healthy:   "TT4w Qa"
    and prirelRef:      "prirelRef p aa zz (mkTTMP zsa [] Qa @ sa @ [[e\<^sub>2]\<^sub>E]) (unTT1 Qa)"
    and assm1:          "mkTTMP zsa [] Qa @ sa @ [[Z]\<^sub>R] \<in> unTT1 Qa"
    and assm2:          "e\<^sub>2 \<notin> Z"
    and assm3:          "\<forall>b. b \<in> Z \<or> \<not> e\<^sub>2 <\<^sup>*p b"
    and assm4:          "\<forall>Z. zsa @ sa @ [[Z]\<^sub>R] \<in> unTT1 Qa \<longrightarrow> e\<^sub>2 \<in> Z \<or> (\<exists>b. b \<notin> Z \<and> e\<^sub>2 <\<^sup>*p b)"
  then show "maximal(p,e\<^sub>2)"
  proof -
    have "mkTTMP zsa [] Qa @ sa @ [[Z]\<^sub>R] \<in> unTT1 Qa"
      using assm1 by auto
    then have "prirelRef p aa zz (mkTTMP zsa [] Qa @ sa @ [[e\<^sub>2]\<^sub>E]) (unTT1 Qa)"
      using prirelRef by auto
    then have "prirelRef p ([e\<^sub>2]\<^sub>E # aa) ([e\<^sub>2]\<^sub>E # zz) (mkTTMP zsa [] Qa @ sa) (unTT1 Qa)"
      using assm2 assm3 assm1 by auto

    have "prirelRef p aa zz (zsa @ sa @ [[e\<^sub>2]\<^sub>E]) (unTT1 Qa)"
      using hyp prirelRef by auto

    then have "prirelRef p ([e\<^sub>2]\<^sub>E # aa) ([e\<^sub>2]\<^sub>E # zz) (zsa @ sa) (unTT1 Qa)"
      using assm2 assm3 assm1 assm4 apply auto
   
    then have "saa @ [[Sa \<union> {e. e \<noteq> Tock \<and> saa @ [[e]\<^sub>E] \<notin> Qa \<or> e = Tock \<and> saa @ [[Sa]\<^sub>R, [Tock]\<^sub>E] \<notin> Qa} \<union> {Tick}]\<^sub>R] @ [Tock]\<^sub>E # sb @ [[Z]\<^sub>R] \<in> unTT1 Qa"
      using TT1_healthy TT2_healthy TT4w_healthy concat_unTT1_extend_TT2_Refusal by blast
    then have "saa @ [Sa \<union> {e. e \<noteq> Tock \<and> saa @ [[e]\<^sub>E] \<notin> Qa \<or> e = Tock \<and> saa @ [[Sa]\<^sub>R, [Tock]\<^sub>E] \<notin> Qa} \<union> {Tick}]\<^sub>R # [Tock]\<^sub>E # sb @ [[Z]\<^sub>R] \<in> unTT1 Qa"
      by auto
    then have "\<exists>Z. saa @ [Sa \<union> {e. e \<noteq> Tock \<and> saa @ [[e]\<^sub>E] \<notin> Qa \<or> e = Tock \<and> saa @ [[Sa]\<^sub>R, [Tock]\<^sub>E] \<notin> Qa} \<union> {Tick}]\<^sub>R # [Tock]\<^sub>E # sb @ [[Z]\<^sub>R] \<in> unTT1 Qa \<and> e\<^sub>2 \<notin> Z \<and> \<not>(\<exists>b. b \<notin> Z \<and> e\<^sub>2 <\<^sup>*p b)"
      using assm2 assm3 by blast
    then have "\<not>(\<forall>Z. saa @ [Sa \<union> {e. e \<noteq> Tock \<and> saa @ [[e]\<^sub>E] \<notin> Qa \<or> e = Tock \<and> saa @ [[Sa]\<^sub>R, [Tock]\<^sub>E] \<notin> Qa} \<union> {Tick}]\<^sub>R # [Tock]\<^sub>E # sb @ [[Z]\<^sub>R] \<in> unTT1 Qa \<longrightarrow> e\<^sub>2 \<in> Z \<or> (\<exists>b. b \<notin> Z \<and> e\<^sub>2 <\<^sup>*p b))"
      by blast
*)
(*
lemma
  assumes "prirelRef p xs ys (sa @ zs @ z) (unTT1 P)" "TT1 P" "TT3 P" "TT2 P" "TT4 P"
  shows "prirelRef p xs ys (sa @ (mkTTMP zs sa P) @ z) (unTT1 P)"
  using assms apply(induct p xs ys z P arbitrary:sa zs rule:prirelRef.induct, auto)
  sledgehammer
  oops

lemma prirelRef_start_Ref_extends:
  assumes "TT1 Q" "TT2 Q" "TT4 Q" "prirelRef pa t s (sa @ [[S]\<^sub>R, [Tock]\<^sub>E]) (unTT1 Q)"
  shows "prirelRef pa t s (sa @ [[S \<union> {e. e \<noteq> Tock \<and> sa @ [[e]\<^sub>E] \<notin> Q \<or> e = Tock \<and> sa @ [[S]\<^sub>R, [Tock]\<^sub>E] \<notin> Q} \<union> {Tick}]\<^sub>R, [Tock]\<^sub>E]) (unTT1 Q)"
  sorry (* FIXME: Proved above. *)
*)

(*
proof (induct s arbitrary:P rule:rev_induct)
  case Nil
  then show ?case by auto
next
  case (snoc x xs)
  then have "(mkTTMP xs [] P) \<in> P"
    by (meson TT1_def tt_prefix_subset_front tt_prefix_subset_refl)
  then have "TTMPick (mkTTMP xs [] P) [] P"
    by (simp add: TT2_imp_TTMPick_mkTTMP snoc.prems(2) snoc.prems(4) snoc.prems(5))
(*  then have "\<forall>e X. (e \<notin> X \<and> e \<noteq> Tock \<and> ((mkTTMP xs [] P) @ [[X]\<^sub>R])) \<longrightarrow> ((mkTTMP xs [] P) @ [[e]\<^sub>E]) \<in> P"
*)
  have "mkTTMP (xs @ [x]) [] P = (mkTTMP xs [] P) @ mkTTMP [x] ([] @ xs) P"
    using mkTTMP_dist_concat by blast
  also have "... = (mkTTMP xs [] P) @ mkTTMP [x] xs P"
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
        using snoc TT2_aux2 x2_in_P by fastforce
      then have x2_TT:"[[x2 \<union> {e. (e \<noteq> Tock \<and> [[e]\<^sub>E] \<notin> P) \<or> (e = Tock \<and> [[x2]\<^sub>R,[Tock]\<^sub>E] \<notin> P)} \<union> {Tick}]\<^sub>R] \<in> P"
        using \<open>TT4 P\<close> TT4_def by fastforce
      then have "mkTTMP ([] @ [x]) [] P = [[x2 \<union> {e. (e \<noteq> Tock \<and> [[e]\<^sub>E] \<notin> P) \<or> (e = Tock \<and> [[x2]\<^sub>R,[Tock]\<^sub>E] \<notin> P)} \<union> {Tick}]\<^sub>R]"
        using Ref by auto
      then show ?thesis using x2_TT by auto
    qed
  next
    case (snoc z zs)
    then show ?case sorry
  qed
  proof (cases x)
    case (ObsEvent x1)
    then have "mkTTMP [[x1]\<^sub>E] (xs) P = [[x1]\<^sub>E]"
      by simp
    then have "(mkTTMP xs [] P) @ [[x1]\<^sub>E] \<in> P"
      sledgehammer
    then show ?thesis sorry
  next
    case (Ref x2)
    then show ?thesis sorry
  qed
qed
  apply (case_tac x, auto)
  sledgehammer*)

lemma mkTTMP_absorb_Ref_Tock:
(*  assumes "Tick \<in> x" 
          "\<forall>xa. (xa \<noteq> Tock \<and> xs @ [[xa]\<^sub>E] \<notin> P) \<longrightarrow> xa \<in> x"
          "xs @ [[x]\<^sub>R, [Tock]\<^sub>E] \<notin> P \<longrightarrow> Tock \<in> x"*)
  shows "mkTTMP xs i P @ ([[x \<union> {e. (e \<noteq> Tock \<and> i @ xs @ [[e]\<^sub>E] \<notin> P) 
                                \<or> (e = Tock \<and> i @ xs @ [[x]\<^sub>R,[Tock]\<^sub>E] \<notin> P)} 
                               \<union> {Tick}]\<^sub>R,[Tock]\<^sub>E] @ z) 
         = 
         mkTTMP (xs @ [[x]\<^sub>R,[Tock]\<^sub>E]) i P @ z"
  by (induct xs i P arbitrary:x z rule:mkTTMP.induct, simp_all)

lemma mkTTMP_absorb_Ref_Tock':
(*  assumes "Tick \<in> x" 
          "\<forall>xa. (xa \<noteq> Tock \<and> xs @ [[xa]\<^sub>E] \<notin> P) \<longrightarrow> xa \<in> x"
          "xs @ [[x]\<^sub>R, [Tock]\<^sub>E] \<notin> P \<longrightarrow> Tock \<in> x"*)
  shows "mkTTMP xs i P @ ([[x \<union> {e. (e \<noteq> Tock \<and> i @ xs @ [[e]\<^sub>E] \<notin> P) 
                                \<or> (e = Tock \<and> i @ xs @ [[x]\<^sub>R,[Tock]\<^sub>E] \<notin> P)} 
                               \<union> {Tick}]\<^sub>R,[Tock]\<^sub>E]) 
         = 
         mkTTMP (xs @ [[x]\<^sub>R,[Tock]\<^sub>E]) i P"
  by (induct xs i P arbitrary:x rule:mkTTMP.induct, simp_all)

lemma
  "mkTTMP (sa @ [[S]\<^sub>R, [Tock]\<^sub>E]) [] Q
   =
   (mkTTMP sa [] Q) @ [[S \<union> {e. e \<noteq> Tock \<and> sa @ [[e]\<^sub>E] \<notin> Q \<or> e = Tock \<and> sa @ [[S]\<^sub>R, [Tock]\<^sub>E] \<notin> Q} \<union> {Tick}]\<^sub>R, [Tock]\<^sub>E]"
  using mkTTMP_absorb_Ref_Tock'
  by (smt Collect_cong append.left_neutral)

lemma prirelRef2_TTMPick_imp_prirelRef:
  assumes "prirelRef2 p x s i P" "TT4 P" "TT3 P" "TT2 P" "TT1 P"
  shows "\<exists>t. x \<lesssim>\<^sub>C t \<and> TTMPick (mkTTMP s i P) i P \<and> prirelRef p t (mkTTMP s i P) (mkTTMP i [] P) (unTT1 P)"
proof -
  have "(\<exists>t. x \<lesssim>\<^sub>C t \<and> TTMPick (mkTTMP s i P) i P \<and> prirelRef p t (mkTTMP s i P) (mkTTMP i [] P) (unTT1 P))
        =
        (\<exists>t. x \<lesssim>\<^sub>C t \<and> prirelRef p t (mkTTMP s i P) (mkTTMP i [] P) (unTT1 P))"
    using assms TT2_imp_TTMPick_mkTTMP by blast
  also have "... = True"
    using assms proof (induct p x s i P rule:prirelRef2.induct, auto)
    fix pa sa 
    fix Q::"'a ttobs list set"
    assume TT4_healthy: "TT4 Q"
     and    TT3_healthy: "TT3 Q"
     and   TT2_healthy: "TT2 Q"
     and    TT1_healthy: "TT1 Q"
    show "\<exists>t. prirelRef pa t [] sa (unTT1 Q)"
      using prirelRef.simps(1) by blast
  next
    fix pa 
    fix R::"'a ttevent set"
    fix S sa Q
    assume R_subset:"R \<subseteq> prirelrefSub pa S sa Q"
     and  TT4_healthy: "TT4 Q"
     and   TT3_healthy: "TT3 Q"
     and  TT2_healthy: "TT2 Q"
     and   TT1_healthy: "TT1 Q"
    then show "\<exists>t. [[R]\<^sub>R] \<lesssim>\<^sub>C t \<and>
           prirelRef pa t [[insert Tick (S \<union> {e. e \<noteq> Tock \<and> sa @ [[e]\<^sub>E] \<notin> Q \<or> e = Tock \<and> sa @ [[S]\<^sub>R, [Tock]\<^sub>E] \<notin> Q})]\<^sub>R] (mkTTMP sa [] Q) (unTT1 Q)"
    proof -
      from R_subset have "R \<subseteq> prirelrefSub pa S sa Q"
        by auto
      then have "R \<subseteq> prirelref pa (S \<union> {e. e \<noteq> Tock \<and> sa @ [[e]\<^sub>E] \<notin> Q \<or> e = Tock \<and> sa @ [[S]\<^sub>R, [Tock]\<^sub>E] \<notin> Q} \<union> {Tick})"
        using prirelref_prirelrefSub TT3_healthy by blast
      then have "[[R]\<^sub>R] \<lesssim>\<^sub>C [[prirelref pa (S \<union> {e. e \<noteq> Tock \<and> sa @ [[e]\<^sub>E] \<notin> Q \<or> e = Tock \<and> sa @ [[S]\<^sub>R, [Tock]\<^sub>E] \<notin> Q} \<union> {Tick})]\<^sub>R]"
        by auto
      then have "[[R]\<^sub>R] \<lesssim>\<^sub>C [[prirelref pa (S \<union> {e. e \<noteq> Tock \<and> sa @ [[e]\<^sub>E] \<notin> Q \<or> e = Tock \<and> sa @ [[S]\<^sub>R, [Tock]\<^sub>E] \<notin> Q} \<union> {Tick})]\<^sub>R] \<and>
                  prirelRef pa [[prirelref pa (S \<union> {e. e \<noteq> Tock \<and> sa @ [[e]\<^sub>E] \<notin> Q \<or> e = Tock \<and> sa @ [[S]\<^sub>R, [Tock]\<^sub>E] \<notin> Q} \<union> {Tick})]\<^sub>R]
                               [[insert Tick (S \<union> {e. e \<noteq> Tock \<and> sa @ [[e]\<^sub>E] \<notin> Q \<or> e = Tock \<and> sa @ [[S]\<^sub>R, [Tock]\<^sub>E] \<notin> Q})]\<^sub>R] (mkTTMP sa [] Q) (unTT1 Q)"
        by auto
      then show ?thesis by blast
    qed
  next
    fix pa 
    fix R S::"'a ttevent set"
    fix aa zz sa t::"'a ttobs list"
    fix Q::"'a ttobs list set"
    assume R_subset:"R \<subseteq> prirelrefSub pa S sa Q"
     and  TT4_healthy: "TT4 Q"
     and   TT3_healthy: "TT3 Q"
     and  TT2_healthy: "TT2 Q"
     and   TT1_healthy: "TT1 Q"
     and aa_prefix_t:"aa \<lesssim>\<^sub>C t"
     and prirelRef_assm:"prirelRef pa t (mkTTMP zz (sa @ [[S]\<^sub>R, [Tock]\<^sub>E]) Q) (mkTTMP (sa @ [[S]\<^sub>R, [Tock]\<^sub>E]) [] Q) (unTT1 Q)"
     and Tock_not_in:"Tock \<notin> prirelrefSub pa S sa Q"
     and "prirelRef2 pa aa zz (sa @ [[S]\<^sub>R, [Tock]\<^sub>E]) Q"
    then have TT4w_healthy: "TT4w Q" 
      using TT4_healthy TT1_healthy TT4_TT1_imp_TT4w by blast
    then obtain Y where Y:"Y = (mkTTMP zz (sa @ [[S]\<^sub>R, [Tock]\<^sub>E]) Q)" by auto
    then show "\<exists>t. [R]\<^sub>R # [Tock]\<^sub>E # aa \<lesssim>\<^sub>C t \<and>
           prirelRef pa t
            ([insert Tick
               (S \<union> {e. e \<noteq> Tock \<and> sa @ [[e]\<^sub>E] \<notin> Q \<or> e = Tock \<and> sa @ [[S]\<^sub>R, [Tock]\<^sub>E] \<notin> Q})]\<^sub>R #
             [Tock]\<^sub>E # mkTTMP zz (sa @ [[S]\<^sub>R, [Tock]\<^sub>E]) Q)
            (mkTTMP sa [] Q) (unTT1 Q)"
    proof -
      obtain Z where Z:"Z = S \<union> {e. e \<noteq> Tock \<and> sa @ [[e]\<^sub>E] \<notin> Q \<or> e = Tock \<and> sa @ [[S]\<^sub>R, [Tock]\<^sub>E] \<notin> Q} \<union> {Tick}" by auto
      from R_subset Tock_not_in have "R \<subseteq> prirelrefSub pa S sa Q \<and> Tock \<notin> prirelrefSub pa S sa Q"
        by auto
      then have "R \<subseteq> prirelref pa Z \<and> Tock \<notin> prirelref pa Z"
        using prirelref_prirelrefSub TT3_healthy Z by blast
      then have "[R]\<^sub>R # [Tock]\<^sub>E # aa \<lesssim>\<^sub>C [prirelref pa Z]\<^sub>R # [Tock]\<^sub>E # t \<and> Tock \<notin> prirelref pa Z"
        using aa_prefix_t by auto
      then have "[R]\<^sub>R # [Tock]\<^sub>E # aa \<lesssim>\<^sub>C [prirelref pa Z]\<^sub>R # [Tock]\<^sub>E # t
            \<and> Tock \<notin> prirelref pa Z
            \<and> prirelRef pa t Y (mkTTMP (sa @ [[S]\<^sub>R, [Tock]\<^sub>E]) [] Q) (unTT1 Q)"
        using Y prirelRef_assm by auto
      then have "[R]\<^sub>R # [Tock]\<^sub>E # aa \<lesssim>\<^sub>C [prirelref pa Z]\<^sub>R # [Tock]\<^sub>E # t
            \<and> Tock \<notin> prirelref pa Z
            \<and> prirelRef pa ([prirelref pa Z]\<^sub>R # [Tock]\<^sub>E # t) 
                           ([Z]\<^sub>R # [Tock]\<^sub>E # Y) (mkTTMP sa [] Q) (unTT1 Q)"
      proof -
        have "prirelRef pa t Y (mkTTMP (sa @ [[S]\<^sub>R, [Tock]\<^sub>E]) [] Q) (unTT1 Q)"
             using \<open>[R]\<^sub>R # [Tock]\<^sub>E # aa \<lesssim>\<^sub>C [prirelref pa Z]\<^sub>R # [Tock]\<^sub>E # t \<and> Tock \<notin> prirelref pa Z \<and> prirelRef pa t Y (mkTTMP (sa @ [[S]\<^sub>R, [Tock]\<^sub>E]) [] Q) (unTT1 Q)\<close> by blast
        then have "prirelRef pa t Y ((mkTTMP sa [] Q) @ [[S \<union> {e. e \<noteq> Tock \<and> sa @ [[e]\<^sub>E] \<notin> Q \<or> e = Tock \<and> sa @ [[S]\<^sub>R, [Tock]\<^sub>E] \<notin> Q} \<union> {Tick}]\<^sub>R, [Tock]\<^sub>E]) (unTT1 Q)"
          (*using TT1_healthy TT2_healthy TT4w_healthy Y Z prirelRef_start_Ref_extends sledgehammer by fastforce*)
          using mkTTMP_absorb_Ref_Tock'
          by (smt Collect_cong append_Nil)
        then have "prirelRef pa t Y ((mkTTMP sa [] Q) @ [[Z]\<^sub>R, [Tock]\<^sub>E]) (unTT1 Q)"
          using Z by auto
        then have "prirelRef pa ([prirelref pa Z]\<^sub>R # [Tock]\<^sub>E # t) ([Z]\<^sub>R # [Tock]\<^sub>E # Y) (mkTTMP sa [] Q) (unTT1 Q)"
          using \<open>[R]\<^sub>R # [Tock]\<^sub>E # aa \<lesssim>\<^sub>C [prirelref pa Z]\<^sub>R # [Tock]\<^sub>E # t \<and> Tock \<notin> prirelref pa Z \<and> prirelRef pa t Y (mkTTMP (sa @ [[S]\<^sub>R, [Tock]\<^sub>E]) [] Q) (unTT1 Q)\<close> 
          by auto
        then show ?thesis
          using \<open>[R]\<^sub>R # [Tock]\<^sub>E # aa \<lesssim>\<^sub>C [prirelref pa Z]\<^sub>R # [Tock]\<^sub>E # t \<and> Tock \<notin> prirelref pa Z \<and> prirelRef pa t Y (mkTTMP (sa @ [[S]\<^sub>R, [Tock]\<^sub>E]) [] Q) (unTT1 Q)\<close> 
          by auto
      qed
      then have "[R]\<^sub>R # [Tock]\<^sub>E # aa \<lesssim>\<^sub>C [prirelref pa Z]\<^sub>R # [Tock]\<^sub>E # t \<and>
        prirelRef pa ([prirelref pa Z]\<^sub>R # [Tock]\<^sub>E # t)
         ([insert Tick
            (S \<union> {e. e \<noteq> Tock \<and> sa @ [[e]\<^sub>E] \<notin> Q \<or> e = Tock \<and> sa @ [[S]\<^sub>R, [Tock]\<^sub>E] \<notin> Q})]\<^sub>R #
          [Tock]\<^sub>E # mkTTMP zz (sa @ [[S]\<^sub>R, [Tock]\<^sub>E]) Q)
         (mkTTMP sa [] Q) (unTT1 Q)"
        using Z Y by auto
      then show ?thesis by blast
    qed
  next
    fix pa 
    fix aa zz::"'a ttobs list"
    fix e\<^sub>2 sa t 
    fix Q::"'a ttobs list set"
    assume 
        TT4_healthy: "TT4 Q"
    and TT3_healthy:  "TT3 Q"
    and TT2_healthy: "TT2 Q"
    and TT1_healthy:  "TT1 Q"
    and prirelRef2:   "prirelRef2 pa aa zz (sa @ [[e\<^sub>2]\<^sub>E]) Q"
    and maximal:      "maximal(pa,e\<^sub>2)"
    and subsettt:    "aa \<lesssim>\<^sub>C t"
    and prirelRef:    "prirelRef pa t (mkTTMP zz (sa @ [[e\<^sub>2]\<^sub>E]) Q) (mkTTMP (sa @ [[e\<^sub>2]\<^sub>E]) [] Q) (unTT1 Q)"
    then show "\<exists>t. [e\<^sub>2]\<^sub>E # aa \<lesssim>\<^sub>C t \<and> prirelRef pa t ([e\<^sub>2]\<^sub>E # mkTTMP zz (sa @ [[e\<^sub>2]\<^sub>E]) Q) (mkTTMP sa [] Q) (unTT1 Q)"
    proof -
      from subsettt have e2_aa_t:"[e\<^sub>2]\<^sub>E # aa \<lesssim>\<^sub>C [e\<^sub>2]\<^sub>E # t"
        by auto
      have "prirelRef pa t (mkTTMP zz (sa @ [[e\<^sub>2]\<^sub>E]) Q) (mkTTMP (sa @ [[e\<^sub>2]\<^sub>E]) [] Q) (unTT1 Q)"
        using prirelRef by auto
      then have "prirelRef pa ([e\<^sub>2]\<^sub>E # t) ([e\<^sub>2]\<^sub>E # mkTTMP zz (sa @ [[e\<^sub>2]\<^sub>E]) Q) (mkTTMP sa [] Q) (unTT1 Q)"
        using mkTTMP_absorb_event maximal
        by (simp add: mkTTMP_dist_concat)
      then have "[e\<^sub>2]\<^sub>E # aa \<lesssim>\<^sub>C [e\<^sub>2]\<^sub>E # t \<and> prirelRef pa ([e\<^sub>2]\<^sub>E # t) ([e\<^sub>2]\<^sub>E # mkTTMP zz (sa @ [[e\<^sub>2]\<^sub>E]) Q) (mkTTMP sa [] Q) (unTT1 Q)"
        using e2_aa_t by auto
      then have "\<exists>t. [e\<^sub>2]\<^sub>E # aa \<lesssim>\<^sub>C t \<and> prirelRef pa t ([e\<^sub>2]\<^sub>E # mkTTMP zz (sa @ [[e\<^sub>2]\<^sub>E]) Q) (mkTTMP sa [] Q) (unTT1 Q)"
        by blast
      then show ?thesis
        by blast
    qed
  next
    fix pa 
    fix aa zz::"'a ttobs list"
    fix e\<^sub>2 sa Z t
    fix Q::"'a ttobs list set"
    assume 
        TT4_healthy: "TT4 Q"
    and TT3_healthy:  "TT3 Q"
    and TT2_healthy: "TT2 Q"
    and TT1_healthy:  "TT1 Q"
    and prirelRef2:   "prirelRef2 pa aa zz (sa @ [[e\<^sub>2]\<^sub>E]) Q"
    and sa_Z:         "sa @ [[Z]\<^sub>R] \<in> Q"
(*    and TTMPick_sa:   "TTMPick sa [] Q"*)
    and events_in_Z:  "\<forall>e. e \<notin> Z \<and> e \<noteq> Tock \<longrightarrow> sa @ [[e]\<^sub>E] \<in> Q"
    and Tick_in_Z:    "Tick \<in> Z"
    and e2_not_in_Z:  "e\<^sub>2 \<notin> Z"
    and no_pri_Z:     "\<forall>b. b \<in> Z \<or> \<not> e\<^sub>2 <\<^sup>*pa b"
    and not_prirelRef:"\<forall>t. [e\<^sub>2]\<^sub>E # aa \<lesssim>\<^sub>C t \<longrightarrow> \<not> prirelRef pa t ([e\<^sub>2]\<^sub>E # mkTTMP zz (sa @ [[e\<^sub>2]\<^sub>E]) Q) (mkTTMP sa [] Q) (unTT1 Q)"
    and Tock_in_Z:    "Tock \<in> Z"
    and subsettt:    "aa \<lesssim>\<^sub>C t"
    and prirelRef:    "prirelRef pa t (mkTTMP zz (sa @ [[e\<^sub>2]\<^sub>E]) Q) (mkTTMP (sa @ [[e\<^sub>2]\<^sub>E]) [] Q) (unTT1 Q)"
    then show "False"
   proof -
      from subsettt have e2_aa_t:"[e\<^sub>2]\<^sub>E # aa \<lesssim>\<^sub>C [e\<^sub>2]\<^sub>E # t"
        by auto

      have TT4w_healthy:"TT4w Q"
        using TT1_healthy TT4_healthy 
        by (simp add: TT4_TT1_imp_TT4w)

      have a:"(sa @ [[Z]\<^sub>R] \<in> Q \<and> e\<^sub>2 \<notin> Z \<and> \<not>(\<exists>b. b \<notin> Z \<and> e\<^sub>2 <\<^sup>*pa b)
          \<and> (\<forall>e. e \<notin> Z \<and> e \<noteq> Tock \<longrightarrow> sa @ [[e]\<^sub>E] \<in> Q)
          \<and> (Tock \<notin> Z \<longrightarrow> sa @ [[Z]\<^sub>R,[Tock]\<^sub>E] \<in> Q) \<and> Tick \<in> Z)"
        using  Tick_in_Z e2_not_in_Z events_in_Z no_pri_Z sa_Z Tock_in_Z by blast
      
      then have "(mkTTMP sa [] Q) \<in> Q"
        by (meson TT1_def TT1_healthy TT2_healthy TT3_healthy TT4_healthy TTs_mkTTMP_in_P tt_prefix_subset_front tt_prefix_subset_refl)
      then have b:"(mkTTMP sa [] Q) @ [[Z]\<^sub>R] \<in> unTT1 Q \<and> e\<^sub>2 \<notin> Z \<and> \<not>(\<exists>b. b \<notin> Z \<and> e\<^sub>2 <\<^sup>*pa b)"
        using a TT1_healthy TT4w_healthy  
        by (simp add: prirelRef_unTT1_case_specific TT2_healthy TT3_healthy TT4_healthy mkTTMP_in_P)
        (* FIXME: Key result to prove *)
      have "prirelRef pa t (mkTTMP zz (sa @ [[e\<^sub>2]\<^sub>E]) Q) (mkTTMP (sa @ [[e\<^sub>2]\<^sub>E]) [] Q) (unTT1 Q)"
        using prirelRef by auto
      then have "prirelRef pa t (mkTTMP zz (sa @ [[e\<^sub>2]\<^sub>E]) Q) ((mkTTMP sa [] Q) @ [[e\<^sub>2]\<^sub>E]) (unTT1 Q)"
        by (simp add: mkTTMP_dist_concat)
      then have prirelRef_pa_t:"prirelRef pa ([e\<^sub>2]\<^sub>E # t) ([e\<^sub>2]\<^sub>E # mkTTMP zz (sa @ [[e\<^sub>2]\<^sub>E]) Q) (mkTTMP sa [] Q) (unTT1 Q)"
        using prirelRef sa_Z e2_not_in_Z events_in_Z b by auto
      then have "[e\<^sub>2]\<^sub>E # aa \<lesssim>\<^sub>C [e\<^sub>2]\<^sub>E # t"
        using subsettt by auto
      then have not_prirelRef_pa_t:"\<not> prirelRef pa ([e\<^sub>2]\<^sub>E # t) ([e\<^sub>2]\<^sub>E # mkTTMP zz (sa @ [[e\<^sub>2]\<^sub>E]) Q) (mkTTMP sa [] Q) (unTT1 Q)"
        using not_prirelRef by blast
      then show ?thesis
        using prirelRef_pa_t not_prirelRef_pa_t by auto
    qed
  next
    fix pa 
    fix aa zz::"'a ttobs list"
    fix e\<^sub>2 sa t Z
    fix Q::"'a ttobs list set"
    assume 
        TT4_healthy: "TT4 Q"
    and TT3_healthy:  "TT3 Q"
    and TT2_healthy: "TT2 Q"
    and TT1_healthy:  "TT1 Q"
    and prirelRef2:   "prirelRef2 pa aa zz (sa @ [[e\<^sub>2]\<^sub>E]) Q"
    and sa_Z:         "sa @ [[Z]\<^sub>R] \<in> Q"
  (*  and TTMPick_sa:   "TTMPick sa [] Q"*)
    and e2_not_in_Z:   "e\<^sub>2 \<notin> Z"
    and nohigherpri:  "\<forall>b. b \<in> Z \<or> \<not> e\<^sub>2 <\<^sup>*pa b"
    and subsettt:    "aa \<lesssim>\<^sub>C t"
    and events_in_Z:  "\<forall>e. e \<notin> Z \<and> e \<noteq> Tock \<longrightarrow> sa @ [[e]\<^sub>E] \<in> Q"
    and Tick_in_Z:    "Tick \<in> Z"
    and Tock_Z_in_Q:  "sa @ [[Z]\<^sub>R, [Tock]\<^sub>E] \<in> Q"
    and prirelRef:    "prirelRef pa t (mkTTMP zz (sa @ [[e\<^sub>2]\<^sub>E]) Q) (mkTTMP (sa @ [[e\<^sub>2]\<^sub>E]) [] Q) (unTT1 Q)"
    then show "\<exists>t. [e\<^sub>2]\<^sub>E # aa \<lesssim>\<^sub>C t \<and> prirelRef pa t ([e\<^sub>2]\<^sub>E # mkTTMP zz (sa @ [[e\<^sub>2]\<^sub>E]) Q) (mkTTMP sa [] Q) (unTT1 Q)"
    proof -
      from subsettt have e2_aa_t:"[e\<^sub>2]\<^sub>E # aa \<lesssim>\<^sub>C [e\<^sub>2]\<^sub>E # t"
        by auto

      have TT4w_healthy:"TT4w Q"
        using TT1_healthy TT4_healthy 
        by (simp add: TT4_TT1_imp_TT4w)

      have a:"(sa @ [[Z]\<^sub>R] \<in> Q  \<and> e\<^sub>2 \<notin> Z \<and> \<not>(\<exists>b. b \<notin> Z \<and> e\<^sub>2 <\<^sup>*pa b)
          \<and> (\<forall>e. e \<notin> Z \<and> e \<noteq> Tock \<longrightarrow> sa @ [[e]\<^sub>E] \<in> Q)
          \<and> (Tock \<notin> Z \<longrightarrow> sa @ [[Z]\<^sub>R,[Tock]\<^sub>E] \<in> Q) \<and> Tick \<in> Z)"
        by (simp add:  Tick_in_Z Tock_Z_in_Q e2_not_in_Z events_in_Z nohigherpri sa_Z)
      then have "(mkTTMP sa [] Q) \<in> Q"
        by (meson TT1_def TT1_healthy TT2_healthy TT3_healthy TT4_healthy TTs_mkTTMP_in_P tt_prefix_subset_front tt_prefix_subset_refl)
      then have b:"(mkTTMP sa [] Q) @ [[Z]\<^sub>R] \<in> unTT1 Q \<and> e\<^sub>2 \<notin> Z \<and> \<not>(\<exists>b. b \<notin> Z \<and> e\<^sub>2 <\<^sup>*pa b)"
        using a TT1_healthy TT4w_healthy  
        by (simp add: prirelRef_unTT1_case_specific TT2_healthy TT3_healthy TT4_healthy mkTTMP_in_P)
      have "prirelRef pa t (mkTTMP zz (sa @ [[e\<^sub>2]\<^sub>E]) Q) (mkTTMP (sa @ [[e\<^sub>2]\<^sub>E]) [] Q) (unTT1 Q)"
        using prirelRef by auto
      then have "prirelRef pa t (mkTTMP zz (sa @ [[e\<^sub>2]\<^sub>E]) Q) ((mkTTMP sa [] Q) @ [[e\<^sub>2]\<^sub>E]) (unTT1 Q)"
        by (simp add: mkTTMP_dist_concat)
      then have prirelRef_pa_t:"prirelRef pa ([e\<^sub>2]\<^sub>E # t) ([e\<^sub>2]\<^sub>E # mkTTMP zz (sa @ [[e\<^sub>2]\<^sub>E]) Q) (mkTTMP sa [] Q) (unTT1 Q)"
        using prirelRef sa_Z e2_not_in_Z events_in_Z b by auto
      then have "[e\<^sub>2]\<^sub>E # aa \<lesssim>\<^sub>C [e\<^sub>2]\<^sub>E # t \<and> prirelRef pa ([e\<^sub>2]\<^sub>E # t) ([e\<^sub>2]\<^sub>E # mkTTMP zz (sa @ [[e\<^sub>2]\<^sub>E]) Q) (mkTTMP sa [] Q) (unTT1 Q)"
        using subsettt by auto
      then show ?thesis by blast
    qed
  qed
  
  finally show ?thesis by auto
qed

lemma prirelref_imp_subseteq_prirelrefSub:
  assumes "Z \<subseteq> prirelref pa S" "Tick \<in> S" "Tock \<in> S" "\<forall>e. e \<notin> S \<and> e \<noteq> Tock \<longrightarrow> sa @ [[e]\<^sub>E] \<in> Q" "TT3 Q"
  shows "Z \<subseteq> prirelrefSub pa S sa Q"
proof -
  have "S = S \<union> {e. e \<noteq> Tock \<and> sa @ [[e]\<^sub>E] \<notin> Q \<or> e = Tock \<and> sa @ [[S]\<^sub>R, [Tock]\<^sub>E] \<notin> Q} \<union> {Tick}"
    using assms by auto
  then have "prirelref pa S = prirelrefSub pa S sa Q"
    using assms prirelref_prirelrefSub by (metis (mono_tags, lifting))
  then show ?thesis using assms by auto
qed

lemma prirelref_imp_subseteq_prirelrefSub':
  assumes "Z \<subseteq> prirelref pa S" "Tick \<in> S" "sa @ [[S]\<^sub>R, [Tock]\<^sub>E] \<in> Q" "\<forall>e. e \<notin> S \<and> e \<noteq> Tock \<longrightarrow> sa @ [[e]\<^sub>E] \<in> Q" "TT3 Q"
  shows "Z \<subseteq> prirelrefSub pa S sa Q"
proof -
  have "S = S \<union> {e. e \<noteq> Tock \<and> sa @ [[e]\<^sub>E] \<notin> Q \<or> e = Tock \<and> sa @ [[S]\<^sub>R, [Tock]\<^sub>E] \<notin> Q} \<union> {Tick}"
    using assms by auto
  then have "prirelref pa S = prirelrefSub pa S sa Q"
    using assms prirelref_prirelrefSub by (metis (mono_tags, lifting))
  then show ?thesis using assms by auto
qed

lemma prirelref_imp_eq_prirelrefSub':
  assumes "Tick \<in> S" "sa @ [[S]\<^sub>R, [Tock]\<^sub>E] \<in> Q" "\<forall>e. e \<notin> S \<and> e \<noteq> Tock \<longrightarrow> sa @ [[e]\<^sub>E] \<in> Q" "TT3 Q"
  shows "prirelref pa S = prirelrefSub pa S sa Q"
proof -
  have "S = S \<union> {e. e \<noteq> Tock \<and> sa @ [[e]\<^sub>E] \<notin> Q \<or> e = Tock \<and> sa @ [[S]\<^sub>R, [Tock]\<^sub>E] \<notin> Q} \<union> {Tick}"
    using assms by auto
  then have "prirelref pa S = prirelrefSub pa S sa Q"
    using assms prirelref_prirelrefSub by (metis (mono_tags, lifting))
  then show ?thesis using assms by auto
qed

lemma prirelRef_imp_prirelRef2:
  assumes "x \<lesssim>\<^sub>C t" "TTMPick s i P" "prirelRef p t s i (unTT1 P)" "TT4 P" "TT3 P" "TT2 P" "TT1 P"
  shows "\<exists>z. prirelRef2 p x z i P \<and> z \<lesssim>\<^sub>C s"
  using assms 
proof (induct p t s i P arbitrary:x rule:prirelRef.induct, auto)
  fix pa sa Q 
  fix xa::"'a ttobs list"
  assume "xa \<lesssim>\<^sub>C []"
  then show "\<exists>z. prirelRef2 pa xa z sa Q \<and> z \<lesssim>\<^sub>C []"
    apply (cases xa, auto)
    by (rule_tac x="[]" in exI, auto)
next
  fix pa S sa Q
  fix xa::"'a ttobs list"
  assume 
      prirelref:    "xa \<lesssim>\<^sub>C [[prirelref pa S]\<^sub>R]"
  and events_in_Q:  "\<forall>e. e \<notin> S \<and> e \<noteq> Tock \<longrightarrow> sa @ [[e]\<^sub>E] \<in> Q"
  and Tick_in_S:    "Tick \<in> S"
  and prirelRef2:   "\<forall>z. prirelRef2 pa xa z sa Q \<longrightarrow> \<not> z \<lesssim>\<^sub>C [[S]\<^sub>R]"
  and Tock_in_S:    "Tock \<in> S"
  and  TT4_healthy: "TT4 Q"
  and   TT3_healthy: "TT3 Q"
  and  TT2_healthy: "TT2 Q"
  and   TT1_healthy: "TT1 Q"
  then show "False"
  proof(cases xa)
    case Nil
    then show ?thesis
      using tt_prefix_subset.simps(1) prirelRef2 prirelRef2.simps(1) by blast
  next
    case (Cons a list)
    then obtain Z where "a = [Z]\<^sub>R"
      using tt_prefix_subset.elims(2) prirelref by blast
    then have "[Z]\<^sub>R # list \<lesssim>\<^sub>C [[prirelref pa S]\<^sub>R]"
      using prirelref Cons by auto
    then have "list = []"
              "Z \<subseteq> prirelref pa S"
      using tt_prefix_subset.simps(1) tt_prefix_subset_antisym init_refusal_tt_prefix_subset apply blast
      using \<open>a = [Z]\<^sub>R\<close> local.Cons prirelref by auto
    then have "prirelRef2 pa [[Z]\<^sub>R] [[S]\<^sub>R] sa Q"
      apply auto
      by (meson TT3_healthy Tick_in_S Tock_in_S events_in_Q prirelref_imp_subseteq_prirelrefSub subset_iff)
    then have "\<not> [[S]\<^sub>R] \<lesssim>\<^sub>C [[S]\<^sub>R]"
      using prirelRef2 Cons \<open>a = [Z]\<^sub>R\<close> \<open>list = []\<close> by blast
    then show ?thesis by auto
  qed
next
  fix pa S sa Q
  fix xa::"'a ttobs list"
  assume 
      prirelref:     "xa \<lesssim>\<^sub>C [[prirelref pa S]\<^sub>R]"
  and events_in_Q:   "\<forall>e. e \<notin> S \<and> e \<noteq> Tock \<longrightarrow> sa @ [[e]\<^sub>E] \<in> Q"
  and Tick_in_S:     "Tick \<in> S"
  and Tock_in_Q:     "sa @ [[S]\<^sub>R, [Tock]\<^sub>E] \<in> Q"
  and  TT4_healthy: "TT4 Q"
  and   TT3_healthy: "TT3 Q"
  and  TT2_healthy: "TT2 Q"
  and   TT1_healthy: "TT1 Q"
  then show "\<exists>z. prirelRef2 pa xa z sa Q \<and> z \<lesssim>\<^sub>C [[S]\<^sub>R]"
  proof(cases xa)
    case Nil
    then show ?thesis
      using tt_prefix_subset.simps(1) prirelRef2.simps(1) by blast
  next
    case (Cons a list)
    then obtain Z where "a = [Z]\<^sub>R"
      using tt_prefix_subset.elims(2) prirelref by blast
    then have "[Z]\<^sub>R # list \<lesssim>\<^sub>C [[prirelref pa S]\<^sub>R]"
      using prirelref Cons by auto
    then have "list = []"
              "Z \<subseteq> prirelref pa S"
      using tt_prefix_subset.simps(1) tt_prefix_subset_antisym init_refusal_tt_prefix_subset apply blast
      using \<open>a = [Z]\<^sub>R\<close> local.Cons prirelref by auto
    then have "prirelRef2 pa [[Z]\<^sub>R] [[S]\<^sub>R] sa Q"
      apply auto
      by (meson TT3_healthy Tick_in_S events_in_Q Tock_in_Q prirelref_imp_subseteq_prirelrefSub' subset_iff)
    then have "prirelRef2 pa [[Z]\<^sub>R] [[S]\<^sub>R] sa Q \<and> [[S]\<^sub>R] \<lesssim>\<^sub>C [[S]\<^sub>R]"
      by auto
    then show ?thesis using Cons \<open>a = [Z]\<^sub>R\<close> \<open>list = []\<close> by blast
  qed
next
  fix pa aa S zz sa Q
  fix xa::"'a ttobs list"
  assume
      hyp:          "(\<And>x. x \<lesssim>\<^sub>C aa \<Longrightarrow> \<exists>z. prirelRef2 pa x z (sa @ [[S]\<^sub>R, [Tock]\<^sub>E]) Q \<and> z \<lesssim>\<^sub>C zz)"
  and xa_aa:        "xa \<lesssim>\<^sub>C [prirelref pa S]\<^sub>R # [Tock]\<^sub>E # aa"
  and TT4_healthy: "TT4 Q"
  and TT3_healthy:  "TT3 Q"
  and TT2_healthy: "TT2 Q"
  and TT1_healthy:  "TT1 Q"
  and events_in_Q:  "\<forall>e. e \<notin> S \<and> e \<noteq> Tock \<longrightarrow> sa @ [[e]\<^sub>E] \<in> Q"
  and Tock_not_in_p:"Tock \<notin> prirelref pa S"
  and prirelRef:    "prirelRef pa aa zz (sa @ [[S]\<^sub>R, [Tock]\<^sub>E]) (unTT1 Q)"
  and Tick_in_S:    "Tick \<in> S" 
  and TTMPick_zz:   "TTMPick zz (sa @ [[S]\<^sub>R, [Tock]\<^sub>E]) Q" 
  and hyp_False:    "\<forall>z. prirelRef2 pa xa z sa Q \<longrightarrow> \<not> z \<lesssim>\<^sub>C [S]\<^sub>R # [Tock]\<^sub>E # zz" 
  and Tock_in_S:    "Tock \<in> S"
  then show "False"
  proof (cases xa)
    case Nil
    then show ?thesis
      using tt_prefix_subset.simps(1) hyp_False prirelRef2.simps(1) by blast
  next
    case a_list:(Cons a list)
    then have "xa = a # list"
      by auto
    then show ?thesis
    proof (cases a)
      case (ObsEvent x1)
      then show ?thesis
        using tt_prefix_subset.simps(4) a_list xa_aa by blast
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
          by (simp add: xa TT3_healthy Tick_in_S Tock_in_S events_in_Q prirelref_imp_subseteq_prirelrefSub)
        then have "\<not> [[S]\<^sub>R] \<lesssim>\<^sub>C [S]\<^sub>R # [Tock]\<^sub>E # zz"
          using hyp_False by auto
        then show ?thesis by auto
      next
        case (Cons b list')
        then have "xa = [x2]\<^sub>R # b # list'"
          using a_list Cons Ref by auto
        then have xa:"xa = [x2]\<^sub>R # [Tock]\<^sub>E # list'"
          using xa_aa
          by (metis tt_prefix_subset.simps(3) tt_prefix_subset.simps(5) ttobs.exhaust init_refusal_tt_prefix_subset)
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
  fix xa::"'a ttobs list"
  assume
      hyp:          "(\<And>x. x \<lesssim>\<^sub>C aa \<Longrightarrow> \<exists>z. prirelRef2 pa x z (sa @ [[S]\<^sub>R, [Tock]\<^sub>E]) Q \<and> z \<lesssim>\<^sub>C zz)"
  and xa_aa:        "xa \<lesssim>\<^sub>C [prirelref pa S]\<^sub>R # [Tock]\<^sub>E # aa"
  and TT4_healthy: "TT4 Q"
  and TT3_healthy:  "TT3 Q"
  and TT2_healthy: "TT2 Q"
  and TT1_healthy:  "TT1 Q"
  and events_in_Q:  "\<forall>e. e \<notin> S \<and> e \<noteq> Tock \<longrightarrow> sa @ [[e]\<^sub>E] \<in> Q"
  and Tock_not_in_p:"Tock \<notin> prirelref pa S"
  and prirelRef:    "prirelRef pa aa zz (sa @ [[S]\<^sub>R, [Tock]\<^sub>E]) (unTT1 Q)"
  and Tick_in_S:    "Tick \<in> S" 
  and TTMPick_zz:   "TTMPick zz (sa @ [[S]\<^sub>R, [Tock]\<^sub>E]) Q" 
  and Tock_in_S:    "sa @ [[S]\<^sub>R, [Tock]\<^sub>E] \<in> Q"
  then show "\<exists>z. prirelRef2 pa xa z sa Q \<and> z \<lesssim>\<^sub>C [S]\<^sub>R # [Tock]\<^sub>E # zz"
  proof (cases xa)
    case Nil
    then show ?thesis
      using tt_prefix_subset.simps(1) prirelRef2.simps(1) by blast
  next
    case a_list:(Cons a list)
    then have "xa = a # list"
      by auto
    then show ?thesis
    proof (cases a)
      case (ObsEvent x1)
      then show ?thesis
        using tt_prefix_subset.simps(4) a_list xa_aa by blast
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
          by (simp add: TT3_healthy Tick_in_S Tock_in_S events_in_Q prirelref_imp_subseteq_prirelrefSub' xa)
        then show ?thesis by auto
      next
        case (Cons b list')
        then have "xa = [x2]\<^sub>R # b # list'"
          using a_list Cons Ref by auto
        then have xa:"xa = [x2]\<^sub>R # [Tock]\<^sub>E # list'"
          using xa_aa
          by (metis tt_prefix_subset.simps(3) tt_prefix_subset.simps(5) ttobs.exhaust init_refusal_tt_prefix_subset)
        then have list'_aa:"[x2]\<^sub>R # [Tock]\<^sub>E # list' \<lesssim>\<^sub>C [prirelref pa S]\<^sub>R # [Tock]\<^sub>E # aa"
          using Cons xa_aa by auto
        then have x2_subset:"x2 \<subseteq> prirelrefSub pa S sa Q"
          by (simp add: TT3_healthy Tick_in_S Tock_in_S events_in_Q prirelref_imp_subseteq_prirelrefSub')
        then have Tock_not_in_prirelrefSub:"Tock \<notin> prirelrefSub pa S sa Q"
          using Tock_not_in_p prirelref_imp_eq_prirelrefSub' TT3_healthy Tick_in_S Tock_in_S events_in_Q by blast
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
  fix xa::"'a ttobs list"
  assume
      hyp:          "(\<And>x. x \<lesssim>\<^sub>C aa \<Longrightarrow> \<exists>z. prirelRef2 pa x z (sa @ [[e\<^sub>2]\<^sub>E]) Q \<and> z \<lesssim>\<^sub>C zz)"
  and xa_aa:        "xa \<lesssim>\<^sub>C [e\<^sub>2]\<^sub>E # aa"
  and TTMPick:      "TTMPick zz (sa @ [[e\<^sub>2]\<^sub>E]) Q"
  and TT4_healthy: "TT4 Q"
  and TT3_healthy:  "TT3 Q"
  and TT2_healthy: "TT2 Q"
  and TT1_healthy:  "TT1 Q"
  and prirelRef:    "prirelRef pa aa zz (sa @ [[e\<^sub>2]\<^sub>E]) (unTT1 Q)"
  and maximal:      "maximal(pa,e\<^sub>2)"
  then show "\<exists>z. prirelRef2 pa xa z sa Q \<and> z \<lesssim>\<^sub>C [e\<^sub>2]\<^sub>E # zz"
  proof (cases xa)
    case Nil
    then show ?thesis
      using tt_prefix_subset.simps(1) prirelRef2.simps(1) by blast
  next
    case a_list:(Cons a list)
    then have "xa = a # list"
      by auto
    then show ?thesis
      proof (cases a)
        case (ObsEvent x1)
        then have xa:"xa = [x1]\<^sub>E # list"
           using a_list ObsEvent by simp
        then have x1_list_subsettt:"[x1]\<^sub>E # list \<lesssim>\<^sub>C [e\<^sub>2]\<^sub>E # aa"
           using Cons xa_aa by auto
        then have "x1 = e\<^sub>2" and xa_e2:"xa = [e\<^sub>2]\<^sub>E # list"
           using xa by auto+
        then have "\<exists>z. prirelRef2 pa list z (sa @ [[e\<^sub>2]\<^sub>E]) Q \<and> z \<lesssim>\<^sub>C zz"
           using hyp x1_list_subsettt by auto
        then have "\<exists>z. prirelRef2 pa ([e\<^sub>2]\<^sub>E # list) ([e\<^sub>2]\<^sub>E # z) sa Q \<and> [e\<^sub>2]\<^sub>E # z \<lesssim>\<^sub>C [e\<^sub>2]\<^sub>E # zz"
           using maximal by auto
           then show ?thesis using xa_e2 tt_prefix_subset.simps(1) tt_prefix_subset.simps(3) by blast
      next
        case (Ref x2)
        then show ?thesis
          using a_list xa_aa by auto
      qed
    qed
next
  fix pa aa e\<^sub>2 zz sa Q Z
  fix xa::"'a ttobs list"
  assume
      hyp:          "(\<And>x. x \<lesssim>\<^sub>C aa \<Longrightarrow> \<exists>z. prirelRef2 pa x z (sa @ [[e\<^sub>2]\<^sub>E]) Q \<and> z \<lesssim>\<^sub>C zz)"
  and xa_aa:        "xa \<lesssim>\<^sub>C [e\<^sub>2]\<^sub>E # aa"
  and TTMPick:      "TTMPick zz (sa @ [[e\<^sub>2]\<^sub>E]) Q"
  and TT4_healthy: "TT4 Q"
  and TT3_healthy:  "TT3 Q"
  and TT2_healthy: "TT2 Q"
  and TT1_healthy:  "TT1 Q"
  and prirelRef:    "prirelRef pa aa zz (sa @ [[e\<^sub>2]\<^sub>E]) (unTT1 Q)"
  and Z_in_Q:       "sa @ [[Z]\<^sub>R] \<in> unTT1 Q"
  and e2_not_in_Z:  "e\<^sub>2 \<notin> Z"
  and no_higher_pri:"\<forall>b. b \<in> Z \<or> \<not> e\<^sub>2 <\<^sup>*pa b"
  then show "\<exists>z. prirelRef2 pa xa z sa Q \<and> z \<lesssim>\<^sub>C [e\<^sub>2]\<^sub>E # zz"
  proof (cases xa)
    case Nil
    then show ?thesis using tt_prefix_subset.simps(1) prirelRef2.simps(1) by blast
  next
    case a_list:(Cons a list)
    then have "xa = a # list"
      by auto
    then show ?thesis
      proof (cases a)
        case (ObsEvent x1)
        then have xa:"xa = [x1]\<^sub>E # list"
           using a_list ObsEvent by simp
        then have x1_list_subsettt:"[x1]\<^sub>E # list \<lesssim>\<^sub>C [e\<^sub>2]\<^sub>E # aa"
           using Cons xa_aa by auto
        then have "x1 = e\<^sub>2" and xa_e2:"xa = [e\<^sub>2]\<^sub>E # list"
           using xa by auto+
        then have exists_prirelRef2:"\<exists>z. prirelRef2 pa list z (sa @ [[e\<^sub>2]\<^sub>E]) Q \<and> z \<lesssim>\<^sub>C zz"
          using hyp x1_list_subsettt by auto
        then have "\<exists>z. prirelRef2 pa ([e\<^sub>2]\<^sub>E # list) ([e\<^sub>2]\<^sub>E # z) sa Q \<and> [e\<^sub>2]\<^sub>E # z \<lesssim>\<^sub>C [e\<^sub>2]\<^sub>E # zz"
        proof -
          have TT4w_healthy:"TT4w Q"
            using TT1_healthy TT4_healthy 
            by (simp add: TT4_TT1_imp_TT4w)
          have "(sa @ [[Z]\<^sub>R] \<in> unTT1 Q \<and> e\<^sub>2 \<notin> Z \<and> \<not>(\<exists>b. b \<notin> Z \<and> e\<^sub>2 <\<^sup>*pa b))"
            using Z_in_Q e2_not_in_Z no_higher_pri by blast
          then have "(sa @ [[Z]\<^sub>R] \<in> Q \<and> TTMPick sa [] Q \<and> e\<^sub>2 \<notin> Z \<and> \<not>(\<exists>b. b \<notin> Z \<and> e\<^sub>2 <\<^sup>*pa b)
                      \<and> (\<forall>e. e \<notin> Z \<and> e \<noteq> Tock \<longrightarrow> sa @ [[e]\<^sub>E] \<in> Q)
                      \<and> (Tock \<notin> Z \<longrightarrow> sa @ [[Z]\<^sub>R,[Tock]\<^sub>E] \<in> Q) \<and> Tick \<in> Z)"
            using TT1_healthy TT4w_healthy prirelRef_unTT1_case by blast
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

definition priTT :: "('e ttevent) partialorder \<Rightarrow> ('e ttobs) list set \<Rightarrow> ('e ttobs) list set" where
"priTT p P = {\<rho>|\<rho> s. prirelRef2 p \<rho> s [] P \<and> s \<in> P}"

lemma mkTT1_priNS_unTT1_priTT:
  assumes "TT1 P" "TT4w P" "TT4 P" "TT3 P" "TT2 P"
  shows "mkTT1 (priNS p (unTT1 P)) = priTT p P"
proof -
  have "mkTT1 (priNS p (unTT1 P)) = mkTT1 ({t|s t. s \<in> (unTT1 P) \<and> prirelRef p t s [] (unTT1 P)})"
    unfolding priNS_def by auto
  also have "... = ({\<rho>|\<rho> s t. \<rho> \<lesssim>\<^sub>C t \<and> s \<in> (unTT1 P) \<and> prirelRef p t s [] (unTT1 P)})"
    by (auto simp add:mkTT1_simp)
  also have "... = ({\<rho>|\<rho> s t. \<rho> \<lesssim>\<^sub>C t 
                          \<and> s \<in> (\<Union>{x. TTM1 x \<and> TTM2 x \<and> TTM3 x \<and> TT1w x \<and> (mkTT1 x) \<subseteq> P}) 
                          \<and> prirelRef p t s [] (unTT1 P)})"
    unfolding unTT1_def by auto
  also have "... = ({\<rho>|\<rho> s t. \<rho> \<lesssim>\<^sub>C t 
                          \<and> (\<exists>x. s \<in> x \<and> TTM1 x \<and> TTM2 x \<and> TTM3 x \<and> TT1w x \<and> (mkTT1 x) \<subseteq> P)
                          \<and> prirelRef p t s [] (unTT1 P)})"
    by auto
  also have "... = ({\<rho>|\<rho> s t. \<rho> \<lesssim>\<^sub>C t 
                          \<and> s \<in> P \<and> TTM3 {s} \<and> TTMPick s [] P
                          \<and> prirelRef p t s [] (unTT1 P)})"
    apply auto
    using assms TTM3_mkTT1_simp
    apply (metis (mono_tags, lifting))
    by (metis (mono_tags, lifting) TTM3_mkTT1_simp assms(1) assms(2))
  also have "... = ({\<rho>|\<rho> s t. \<rho> \<lesssim>\<^sub>C t 
                          \<and> s \<in> P \<and> TTMPick s [] P
                          \<and> prirelRef p t s [] (unTT1 P)})"
    using TTM3_TTMPick by auto
  also have "... = ({\<rho>|\<rho> s. prirelRef2 p \<rho> s [] P \<and> s \<in> P})"
    using assms apply auto
     apply (meson TT1_def prirelRef_imp_prirelRef2)
    using TTs_mkTTMP_in_P prirelRef2_TTMPick_imp_prirelRef by fastforce
  finally show ?thesis unfolding priTT_def by auto
qed

(* Redundant stuff below? *)

lemma TTick_Nil [simp]:
  "TTick {[]}"
  unfolding TTick_def by auto

lemma TTick_Refusal_Tock [simp]:
  assumes "TTick {saa}"
  shows "TTick {[S]\<^sub>R # [Tock]\<^sub>E # saa}"
  using assms unfolding TTick_def apply auto                               
  by (metis (no_types, hide_lams) append.left_neutral append1_eq_conv append_Cons ttobs.distinct(1) rev_exhaust)                            

lemma TTick_Refusal_Tock':
  assumes "TTick {[S]\<^sub>R # [Tock]\<^sub>E # saa}"
  shows "TTick {saa}"
  using assms unfolding TTick_def by auto

lemma TTick_event [simp]:
  assumes "TTick {saa}"
  shows "TTick {[e]\<^sub>E # saa}"
  using assms unfolding TTick_def apply auto  
  by (metis Cons_eq_append_conv ttobs.distinct(1) list.inject)                            

lemma
  assumes "R \<subseteq> prirelref pa S" "Tick \<in> S"
  shows "R \<subseteq> prirelref pa (insert Tick S)"
  using assms 
  by (simp add: insert_absorb)

lemma
  assumes "TTick {[S]\<^sub>R # [Tock]\<^sub>E # zz}"
  shows "TTick {[[S]\<^sub>R]}"
  using assms unfolding TTick_def apply auto
  oops

end