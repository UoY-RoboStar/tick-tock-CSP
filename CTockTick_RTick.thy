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
                           (Tock \<notin> X \<longrightarrow> s @ [[X]\<^sub>R,[Tock]\<^sub>E] \<in> P) \<and> CTMPick xs (s @ [[X]\<^sub>R]) P)" |
"CTMPick ([e]\<^sub>E # xs) s P = CTMPick xs (s @ [[e]\<^sub>E]) P"

lemma CTMPick_extend_event_imp:
  assumes "CTMPick xs s P"
  shows "CTMPick (xs @ [[e]\<^sub>E]) s P"
  using assms by (induct xs s P arbitrary:e rule:CTMPick.induct, auto)

lemma CTMPick_extend_ref_imp:
  assumes "CTMPick xs s P" 
          "\<forall>e. (e \<noteq> Tock \<and> e \<notin> X) \<longrightarrow> s @ xs @ [[e]\<^sub>E] \<in> P"
          "(Tock \<notin> X) \<longrightarrow> s @ xs @ [[X]\<^sub>R,[Tock]\<^sub>E] \<in> P"
  shows "CTMPick (xs @ [[X]\<^sub>R]) s P"
  using assms by (induct xs s P arbitrary: X rule:CTMPick.induct, auto)

lemma CTM2a_CTM2b_CT1c_mkCT1_imp_CTMPick:
  assumes "s \<in> x" "CTM2a x" "CTM2b x" "CT1c x" "mkCT1 x \<subseteq> P"
  shows "CTMPick s [] P"
  using assms proof(induct s rule:rev_induct)
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
    then show ?thesis using snoc CTMPick_extend_ref_imp
    proof -
      obtain ccs :: "'a cttobs list set \<Rightarrow> 'a cttobs list" and CC :: "'a cttobs list set \<Rightarrow> 'a cttevent set" and cc :: "'a cttobs list set \<Rightarrow> 'a cttevent" where
        f1: "\<forall>x0. (\<exists>v1 v2 v3. (v1 @ [[v2]\<^sub>R] \<in> x0 \<and> v3 \<notin> v2 \<and> v3 \<noteq> Tock) \<and> v1 @ [[v3]\<^sub>E] \<notin> x0) = ((ccs x0 @ [[CC x0]\<^sub>R] \<in> x0 \<and> cc x0 \<notin> CC x0 \<and> cc x0 \<noteq> Tock) \<and> ccs x0 @ [[cc x0]\<^sub>E] \<notin> x0)"
        by moura
      have "x \<union> {cs. \<exists>csa csb. cs = csa \<and> csa \<lesssim>\<^sub>C csb \<and> csb \<in> x} \<subseteq> P"
        by (metis mkCT1_def snoc.prems(5))
      then have f2: "\<forall>cs. cs \<notin> x \<or> cs \<in> P"
        by (simp add: subset_iff)
      have "\<forall>C Ca cs csa. (CTMPick csa cs Ca \<and> (\<forall>c. (c::'a cttevent) \<noteq> Tock \<and> c \<notin> C \<longrightarrow> cs @ csa @ [[c]\<^sub>E] \<in> Ca) \<and> (Tock \<notin> C \<longrightarrow> cs @ csa @ [[C]\<^sub>R, [Tock]\<^sub>E] \<in> Ca) \<longrightarrow> CTMPick (csa @ [[C]\<^sub>R]) cs Ca) = ((\<not> CTMPick csa cs Ca \<or> (\<exists>c. (c \<noteq> Tock \<and> c \<notin> C) \<and> cs @ csa @ [[c]\<^sub>E] \<notin> Ca) \<or> Tock \<notin> C \<and> cs @ csa @ [[C]\<^sub>R, [Tock]\<^sub>E] \<notin> Ca) \<or> CTMPick (csa @ [[C]\<^sub>R]) cs Ca)"
        by blast
      then have f3: "\<forall>cs csa C Ca. (\<not> CTMPick cs csa C \<or> (\<exists>c. ((c::'a cttevent) \<noteq> Tock \<and> c \<notin> Ca) \<and> csa @ cs @ [[c]\<^sub>E] \<notin> C) \<or> Tock \<notin> Ca \<and> csa @ cs @ [[Ca]\<^sub>R, [Tock]\<^sub>E] \<notin> C) \<or> CTMPick (cs @ [[Ca]\<^sub>R]) csa C"
        by (simp add: CTMPick_extend_ref_imp)
      obtain cca :: "'a cttevent set \<Rightarrow> 'a cttobs list set \<Rightarrow> 'a cttobs list \<Rightarrow> 'a cttobs list \<Rightarrow> 'a cttevent" where
        "\<forall>x0 x1 x2a x3. (\<exists>v4. (v4 \<noteq> Tock \<and> v4 \<notin> x0) \<and> x2a @ x3 @ [[v4]\<^sub>E] \<notin> x1) = ((cca x0 x1 x2a x3 \<noteq> Tock \<and> cca x0 x1 x2a x3 \<notin> x0) \<and> x2a @ x3 @ [[cca x0 x1 x2a x3]\<^sub>E] \<notin> x1)"
        by moura
      then have "cca x2 P [] zs \<noteq> Tock \<and> cca x2 P [] zs \<notin> x2 \<and> [] @ zs @ [[cca x2 P [] zs]\<^sub>E] \<notin> P \<or> Tock \<notin> x2 \<and> [] @ zs @ [[x2]\<^sub>R, [Tock]\<^sub>E] \<notin> P \<or> CTMPick (zs @ [[x2]\<^sub>R]) [] P"
        using f3 \<open>CTMPick zs [] P\<close> by presburger
        then show ?thesis using f2 f1 by (metis CTM2a_def CTM2b_def Ref append_Nil snoc.prems(1) snoc.prems(2) snoc.prems(3))
      qed
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
  shows "(\<exists>Z. s @ [[Z]\<^sub>R] \<in> unCT1 P \<and> e\<^sub>2 \<notin> Z \<and> \<not>(\<exists>b. b \<notin> Z \<and> e\<^sub>2 <\<^sup>*p b))
         =
         (\<exists>Z. s @ [[Z]\<^sub>R] \<in> P \<and> CTTickAll {s @ [[Z]\<^sub>R]} \<and> CTMPick (s @ [[Z]\<^sub>R]) [] P \<and> e\<^sub>2 \<notin> Z \<and> \<not>(\<exists>b. b \<notin> Z \<and> e\<^sub>2 <\<^sup>*p b))"
proof -
  have "(\<exists>Z. s @ [[Z]\<^sub>R] \<in> unCT1 P \<and> e\<^sub>2 \<notin> Z \<and> \<not>(\<exists>b. b \<notin> Z \<and> e\<^sub>2 <\<^sup>*p b))
        =
        (\<exists>Z. s @ [[Z]\<^sub>R] \<in> (\<Union>{x. CTM2a x \<and> CTM2b x \<and> CTTickAll x \<and> CT1c x \<and> (mkCT1 x) \<subseteq> P}) \<and> e\<^sub>2 \<notin> Z \<and> \<not>(\<exists>b. b \<notin> Z \<and> e\<^sub>2 <\<^sup>*p b))"
    unfolding unCT1_def by auto
  also have "...
        =
        (\<exists>Z x. s @ [[Z]\<^sub>R] \<in> x \<and> CTM2a x \<and> CTM2b x \<and> CTTickAll x \<and> CT1c x \<and> (mkCT1 x) \<subseteq> P \<and> e\<^sub>2 \<notin> Z \<and> \<not>(\<exists>b. b \<notin> Z \<and> e\<^sub>2 <\<^sup>*p b))"
    by auto
  also have "... =
       (\<exists>Z. s @ [[Z]\<^sub>R] \<in> P \<and> CTTickAll {s @ [[Z]\<^sub>R]} \<and> CTMPick (s @ [[Z]\<^sub>R]) [] P \<and> e\<^sub>2 \<notin> Z \<and> \<not>(\<exists>b. b \<notin> Z \<and> e\<^sub>2 <\<^sup>*p b))"
    using assms CTTickAll_mkCT1_simp apply auto
    by metis
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

fun prirelRef2 :: "('e cttevent) partialorder \<Rightarrow> ('e cttobs) list \<Rightarrow> ('e cttobs) list \<Rightarrow> ('e cttobs) list \<Rightarrow> ('e cttobs) list set \<Rightarrow> bool" where
"prirelRef2 p [] [] s Q = True" |
"prirelRef2 p [[R]\<^sub>R] [[S]\<^sub>R] s Q = (R \<subseteq> prirelref p S)" |
"prirelRef2 p ([R]\<^sub>R # [Tock]\<^sub>E # aa) ([S]\<^sub>R # [Tock]\<^sub>E # zz) s Q =
   ((R \<subseteq> prirelref p S) \<and> Tock \<notin> prirelref p S \<and> prirelRef2 p aa zz (s @ [[S]\<^sub>R,[Tock]\<^sub>E]) Q)" |
"prirelRef2 p ([e\<^sub>1]\<^sub>E # aa) ([e\<^sub>2]\<^sub>E # zz) s Q
 = 
 (e\<^sub>1 = e\<^sub>2 \<and> prirelRef2 p aa zz (s @ [[e\<^sub>1]\<^sub>E]) Q \<and>
  (maximal(p,e\<^sub>2) 
   \<or> 
  (\<exists>Z. s @ [[Z]\<^sub>R] \<in> Q \<and> e\<^sub>2 \<notin> Z \<and> \<not>(\<exists>b. b \<notin> Z \<and> e\<^sub>2 <\<^sup>*p b))))" |
"prirelRef2 p x y s Q = False"

lemma
  assumes "CT1 P" "CT4 P"
  shows "mkCT1 (priNS p (unCT1 P)) = X p P"
  unfolding unCT1_def priNS_def apply auto
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
  also have "... = ({\<rho>|\<rho> s. prirelRef2 p \<rho> s [] P \<and> s \<in> P})"
    apply auto
    oops

(* Problem below is from 's' how to achieve target 's'? Need a way to construct it
   explicitly, then just need to show that x \<lesssim>\<^sub>C t. *)
fun mkCTMP :: "'e cttobs list \<Rightarrow> 'e cttobs list \<Rightarrow> 'e cttobs list set \<Rightarrow> 'e cttobs list" where
"mkCTMP [] s P = []" |
"mkCTMP ([X]\<^sub>R # xs) s P = ([X \<union> {e. (e \<noteq> Tock \<and> s @ [[e]\<^sub>E] \<notin> P) \<or> (e = Tock \<and> s @ [[X]\<^sub>R,[Tock]\<^sub>E] \<notin> P)}]\<^sub>R # (mkCTMP xs (s @ [[X]\<^sub>R]) P))" |
"mkCTMP ([e]\<^sub>E # xs) s P = ([e]\<^sub>E # (mkCTMP xs (s @ [[e]\<^sub>E]) P))"

lemma
  assumes "CT2 P"
  shows "CTMPick (mkCTMP xs z P) z P"
  using assms apply (induct xs z P rule:mkCTMP.induct, auto)
  sledgehammer

lemma
  assumes "prirelRef2 p x s [] P" "s \<in> P" "CT4 P"
  shows "\<exists>s t. x \<lesssim>\<^sub>C t \<and> s \<in> P \<and> CTTickAll {s} \<and> CTMPick s [] P \<and> prirelRef p t s [] (unCT1 P)"
  nitpick

lemma
  assumes "x \<lesssim>\<^sub>C t" "CTTickAll {s}" "CTMPick s i P" "prirelRef p t s i (unCT1 P)"
  shows "\<exists>z. prirelRef2 p x z i P \<and> z \<lesssim>\<^sub>C s"
  using assms apply (induct p t s i P arbitrary:x rule:prirelRef.induct, auto)
  using ctt_prefix_subset.simps(1) ctt_prefix_subset_antisym prirelRef2.simps(1) apply blast
  apply (case_tac xa, auto)
  using ctt_prefix_subset.simps(1) prirelRef2.simps(1) apply blast
  apply (case_tac list, auto, case_tac a, auto)
  using ctt_prefix_subset_refl prirelRef2.simps(2) apply blast
  using ctt_prefix_subset.elims(2) apply force
      apply (case_tac xa, auto)
  apply (rule_tac x="[]" in exI, auto)
  apply (rule_tac x="[[S]\<^sub>R]" in exI, auto)
  apply (metis ctt_prefix_subset.simps(1) ctt_prefix_subset.simps(2) ctt_prefix_subset.simps(4) ctt_prefix_subset_antisym cttobs.exhaust prirelRef2.simps(2))
  apply (case_tac xa, auto)
  using ctt_prefix_subset.simps(1) prirelRef2.simps(1) apply blast
     apply (case_tac a, auto, case_tac list, auto)
  
  apply (meson ctt_prefix_subset.simps(1) ctt_prefix_subset.simps(2) equalityD1 prirelRef2.simps(2))
  apply (case_tac a, auto, case_tac lista, auto)
    apply (meson ctt_prefix_subset.simps(1) ctt_prefix_subset.simps(2) ctt_prefix_subset.simps(3) order_refl prirelRef2.simps(1) prirelRef2.simps(3))
      sledgehammer
     
     apply (meson ctt_prefix_subset.simps(1) ctt_prefix_subset.simps(2) equalityD1 prirelRef2.simps(2))
  
  using ctt_prefix_subset.simps(1) prirelRef2.simps(1) apply blast
  apply (case_tac list, auto, case_tac a, auto)
  using ctt_prefix_subset_refl prirelRef2.simps(2) apply blast
using ctt_prefix_subset.elims(2) apply force
(*
lemma
  assumes "CT0 P" "CT1 P" "x \<lesssim>\<^sub>C t" "s \<in> P" "CTTick {s}" "prirelRef p t s [] (unCT1 P)"
  shows "\<exists>s. s \<in> P \<and> CTTick {s} \<and> prirelRef p x s [] (unCT1 P)"
  using assms 
proof(induct x arbitrary:t s rule:rev_induct)
  case Nil
  then show ?case
    apply (intro exI[where x="[]"], auto)
    using assms
    using CT0_CT1_empty apply blast
    unfolding CTTick_def by auto
next
  case (snoc z zs)
  then obtain y ys where tz:"t = ys @ [y]"
    apply auto
    by (metis ctt_prefix_subset.simps(6) list.exhaust rev_exhaust)
  then have pri_ys:"prirelRef p (ys @ [y]) s [] (unCT1 P)"
    using snoc by auto
  then obtain x xs where xs:"s = xs @ [x]"
    by (metis neq_Nil_conv prirelRef.simps(28) rev_exhaust)
  then have pri_ys_xs:"prirelRef p (ys @ [y]) (xs @ [x]) [] (unCT1 P)"
    using pri_ys by auto

  have "zs @ [z] \<lesssim>\<^sub>C ys @ [y]"
    using snoc tz by auto
  then have "zs \<lesssim>\<^sub>C ys @ [y]"
    using ctt_prefix_subset_front by blast
  then have hyp:"\<exists>s. s \<in> P \<and> CTTick {s} \<and> prirelRef p zs s [] (unCT1 P)"
    using snoc tz by blast

  (* Now how do we extend zs to (zs@[z])? *)

  then show ?case
  proof (cases z)
    case (Ref x2)
    then show ?thesis sledgehammer
  next
    case (ObsEvent x1)
    then show ?thesis sorry
  qed
qed
*)
  

fun preRprirelRef :: "('e cttevent) partialorder \<Rightarrow> ('e cttobs) list \<Rightarrow> ('e cttobs) list \<Rightarrow> ('e cttobs) list \<Rightarrow> ('e cttobs) list set \<Rightarrow> bool" where
"preRprirelRef p [] [] s Q = True" |
(*"preRprirelRef p [] [[S]\<^sub>R] s Q = True" |
"preRprirelRef p [] ([S]\<^sub>R # [Tock]\<^sub>E # zz) s Q = True" |*)
"preRprirelRef p [[R]\<^sub>R] [[S]\<^sub>R] s Q = (R \<subseteq> prirelref p S \<and> Tick \<in> S)" |
(*"preRprirelRef p [[R]\<^sub>R,[Tock]\<^sub>E] ([S]\<^sub>R # [Tock]\<^sub>E # zz) s Q = ((R \<subseteq> prirelref p S) \<and> Tock \<notin> R \<and> preRprirelRef p [] zz (s @ [[S]\<^sub>R,[Tock]\<^sub>E]) Q)" |
"preRprirelRef p [[R]\<^sub>R] ([S]\<^sub>R # [Tock]\<^sub>E # zz) s Q = ((R \<subseteq> prirelref p S) \<and> Tock \<notin> R \<and> preRprirelRef p [] zz (s @ [[S]\<^sub>R,[Tock]\<^sub>E]) Q)" |
*)"preRprirelRef p ([R]\<^sub>R # [Tock]\<^sub>E # aa) ([S]\<^sub>R # [Tock]\<^sub>E # zz) s Q =
   ((R \<subseteq> prirelref p S) \<and> Tock \<notin> prirelref p S \<and> preRprirelRef p aa zz (s @ [[S]\<^sub>R,[Tock]\<^sub>E]) Q)" |
"preRprirelRef p ([e\<^sub>1]\<^sub>E # aa) ([e\<^sub>2]\<^sub>E # zz) s Q
 = 
 (e\<^sub>1 = e\<^sub>2 \<and> preRprirelRef p aa zz (s @ [[e\<^sub>1]\<^sub>E]) Q \<and>
  (maximal(p,e\<^sub>2) 
   \<or> 
  (\<exists>Z. s @ [[Z]\<^sub>R] \<in> Q \<and> Tick \<in> Z \<and> e\<^sub>2 \<notin> Z \<and> \<not>(\<exists>b. b \<notin> Z \<and> e\<^sub>2 <\<^sup>*p b))))" |
"preRprirelRef p x y s Q = False"

lemma
  assumes "preRprirelRef p x s z P"
  shows "preRprirelRef p x (mkCTTick_Trace s) z P"
  using assms nitpick

lemma preRprirelRef_imp_prirelRef_suffix:
  assumes "preRprirelRef p x s z P" "CT1 P" "CT4 P"
  shows "\<exists>t. x \<lesssim>\<^sub>C t \<and> prirelRef p t s z (unCT1 P)"
  using assms proof (induct p x s _ P rule:preRprirelRef.induct, auto)
  fix pa::"'a cttevent partialorder"
  and sa Q
  show "\<exists>t. prirelRef pa t [] sa (unCT1 Q)"
  by (rule exI[where x="[]"], auto)
next
  fix pa::"'a cttevent partialorder"
  and R S sa Q
  assume assm1:"R \<subseteq> prirelref pa S"
  then show "\<exists>t. [[R]\<^sub>R] \<lesssim>\<^sub>C t \<and> prirelRef pa t [[S]\<^sub>R] sa (unCT1 Q)"
    by (rule_tac x="[[prirelref pa S]\<^sub>R]" in exI, auto)
next
  fix pa::"'a cttevent partialorder"
  fix R S ::"'a cttevent set"
  fix aa zz sa ::"'a cttobs list"
  fix Q t
  assume assm1:"R \<subseteq> prirelref pa S"
  and assm2:"aa \<lesssim>\<^sub>C t"
  and assm3:"prirelRef pa t zz (sa @ [[S]\<^sub>R, [Tock]\<^sub>E]) (unCT1 Q)"
  and assm4:"Tock \<notin> prirelref pa S"
  and assm6:"preRprirelRef pa aa zz (sa @ [[S]\<^sub>R, [Tock]\<^sub>E]) Q"
  then show "\<exists>t. [R]\<^sub>R # [Tock]\<^sub>E # aa \<lesssim>\<^sub>C t \<and>
           prirelRef pa t ([S]\<^sub>R # [Tock]\<^sub>E # zz) sa (unCT1 Q)"
    by (rule_tac x="[prirelref pa S]\<^sub>R # [Tock]\<^sub>E # t" in exI, auto)
next
  fix pa::"'a cttevent partialorder"
  fix aa zz sa ::"'a cttobs list"
  fix Q t e\<^sub>2
  assume assm1:"maximal(pa,e\<^sub>2)"
  and assm1:"aa \<lesssim>\<^sub>C t"
  and assm2:"prirelRef pa t zz (sa @ [[e\<^sub>2]\<^sub>E]) (unCT1 Q)"
  and assm3:"preRprirelRef pa aa zz (sa @ [[e\<^sub>2]\<^sub>E]) Q"
  then show "\<exists>t. [e\<^sub>2]\<^sub>E # aa \<lesssim>\<^sub>C t \<and> prirelRef pa t ([e\<^sub>2]\<^sub>E # zz) sa (unCT1 Q)"
    by (rule_tac x="[e\<^sub>2]\<^sub>E # t" in exI, auto)
next
  fix pa::"'a cttevent partialorder"
  fix aa zz sa ::"'a cttobs list"
  fix Q Z t e\<^sub>2
  assume assm1:"sa @ [[Z]\<^sub>R] \<in> Q"
  and assm2:"e\<^sub>2 \<notin> Z"
  and assm3:"\<forall>b. b \<in> Z \<or> \<not> e\<^sub>2 <\<^sup>*pa b"
  and assm4:"aa \<lesssim>\<^sub>C t"
  and assm5:"prirelRef pa t zz (sa @ [[e\<^sub>2]\<^sub>E]) (unCT1 Q)"
  and assm6:"CT1 Q"
  and assm7:"CT4 Q"
  and assm8:"Tick \<in> Z"
  then show "\<exists>t. [e\<^sub>2]\<^sub>E # aa \<lesssim>\<^sub>C t \<and> prirelRef pa t ([e\<^sub>2]\<^sub>E # zz) sa (unCT1 Q)"
    apply (rule_tac x="[e\<^sub>2]\<^sub>E # t" in exI, auto)
    unfolding unCT1_def apply auto
    using CTTick_mkCT1_simp
    by (smt CTTick_def append1_eq_conv cttobs.inject(2) singletonD)
qed

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

lemma preRprirelRef_imp_prirelRef_suffix':
  assumes "preRprirelRef p x s z P" "CT1 P" "CT4 P"
  shows "\<exists>s t. x \<lesssim>\<^sub>C t \<and> CTTick {s} \<and> prirelRef p t s z (unCT1 P)"
  using assms proof (induct p x s z P rule:preRprirelRef.induct, auto)
  fix pa::"'a cttevent partialorder"
  and sa Q
  show "\<exists>s. CTTick {s} \<and> (\<exists>t. prirelRef pa t s sa (unCT1 Q))"
    by (rule exI[where x="[]"], auto)+
next
  fix pa::"'a cttevent partialorder"
  and R S sa Q
  assume assm1:"R \<subseteq> prirelref pa S"
  then show "\<exists>s t. [[R]\<^sub>R] \<lesssim>\<^sub>C t \<and> CTTick {s} \<and> prirelRef pa t s sa (unCT1 Q)"
    apply (rule_tac x="[[UNIV]\<^sub>R]" in exI, auto)
    apply (rule_tac x="[[prirelref pa UNIV]\<^sub>R]" in exI, auto)
    unfolding prirelref_def apply auto
    unfolding CTTick_def by auto
next
  fix pa::"'a cttevent partialorder"
  fix R S ::"'a cttevent set"
  fix aa zz sa saa t ::"'a cttobs list"
  fix Q t
  assume assm1:"R \<subseteq> prirelref pa S"
  and assm2:"aa \<lesssim>\<^sub>C t"
  and assm3:"prirelRef pa t saa (sa @ [[S]\<^sub>R, [Tock]\<^sub>E]) (unCT1 Q)"
  and assm4:"Tock \<notin> prirelref pa S"
  and assm5:"CTTick {saa}"
  and assm6:"preRprirelRef pa aa zz (sa @ [[S]\<^sub>R, [Tock]\<^sub>E]) Q"
  then show "\<exists>s t. [R]\<^sub>R # [Tock]\<^sub>E # aa \<lesssim>\<^sub>C t \<and> CTTick {s} \<and> prirelRef pa t s sa (unCT1 Q)"
    apply (rule_tac x="[S]\<^sub>R # [Tock]\<^sub>E # saa" in exI, auto) 
    by (rule_tac x="[prirelref pa S]\<^sub>R # [Tock]\<^sub>E # t" in exI, auto) 
next
  fix pa::"'a cttevent partialorder"                                     
  fix aa zz sa saa ::"'a cttobs list"                               
  fix Q t e\<^sub>2                     
  assume assm1:"maximal(pa,e\<^sub>2)"
  and assm1:"aa \<lesssim>\<^sub>C t"                           
  and assm2:"prirelRef pa t saa (sa @ [[e\<^sub>2]\<^sub>E]) (unCT1 Q)"
  and assm3:"preRprirelRef pa aa zz (sa @ [[e\<^sub>2]\<^sub>E]) Q"  
  and assm4:"CTTick {saa}"       
  and assm5:"prirelRef pa t saa (sa @ [[e\<^sub>2]\<^sub>E]) (unCT1 Q)" 
  then show "\<exists>s t. [e\<^sub>2]\<^sub>E # aa \<lesssim>\<^sub>C t \<and> CTTick {s} \<and> prirelRef pa t s sa (unCT1 Q)"
    apply (rule_tac x="[e\<^sub>2]\<^sub>E # saa" in exI, auto) 
    by (rule_tac x="[e\<^sub>2]\<^sub>E # t" in exI, auto)
next
  fix pa::"'a cttevent partialorder"
  fix aa zz sa ::"'a cttobs list"
  fix Q Z t e\<^sub>2 saa  
  assume assm1:"sa @ [[Z]\<^sub>R] \<in> Q"
  and assm2:"e\<^sub>2 \<notin> Z"
  and assm3:"\<forall>b. b \<in> Z \<or> \<not> e\<^sub>2 <\<^sup>*pa b"
  and assm4:"aa \<lesssim>\<^sub>C t"             
  and assm5:"prirelRef pa t saa (sa @ [[e\<^sub>2]\<^sub>E]) (unCT1 Q)"
  and assm6:"CT1 Q"
  and assm7:"CT4 Q"
  and assm8:"Tick \<in> Z" 
  and assm9:"preRprirelRef pa aa zz (sa @ [[e\<^sub>2]\<^sub>E]) Q"
  and assm10:"CTTick {saa}"
  then show "\<exists>s t. [e\<^sub>2]\<^sub>E # aa \<lesssim>\<^sub>C t \<and> CTTick {s} \<and> prirelRef pa t s sa (unCT1 Q)" 
    apply (rule_tac x="[e\<^sub>2]\<^sub>E # saa" in exI, auto)
    apply (rule_tac x="[e\<^sub>2]\<^sub>E # t" in exI, auto)
    unfolding unCT1_def apply auto  
    using CTTick_mkCT1_simp 
    by (smt CTTick_def append1_eq_conv cttobs.inject(2) singletonD)
qed

lemma
  assumes "R \<subseteq> prirelref pa S" "Tick \<in> S"
  shows "R \<subseteq> prirelref pa (insert Tick S)"
  using assms 
  by (simp add: insert_absorb)

lemma preRprirelRef_imp_prirelRef_suffix'':
  assumes "preRprirelRef p x s z P" "CT1 P" "CT4 P"
  shows "\<exists>t. x \<lesssim>\<^sub>C t \<and> prirelRef p t (mkCTTick_Trace s) z (unCT1 P)"
  using assms proof (induct p x s z P rule:preRprirelRef.induct, auto)
  fix pa::"'a cttevent partialorder"
  and sa Q
  show "\<exists>t. prirelRef pa t [] sa (unCT1 Q)"
    by (rule exI[where x="[]"], auto)+
next
  fix pa::"'a cttevent partialorder"
  and R S sa Q
  assume assm1:"R \<subseteq> prirelref pa S"
  and assm2:"Tick \<in> S"
  then show "\<exists>t. [[R]\<^sub>R] \<lesssim>\<^sub>C t \<and> prirelRef pa t [[insert Tick S]\<^sub>R] sa (unCT1 Q)"
    apply (rule_tac x="[[prirelref pa (insert Tick S)]\<^sub>R]" in exI, auto)
    by (auto simp add: insert_absorb)
next
  fix pa::"'a cttevent partialorder"
  fix R S ::"'a cttevent set"
  fix aa zz sa saa t ::"'a cttobs list"
  fix Q
  assume assm1:"R \<subseteq> prirelref pa S"
  and assm2:"aa \<lesssim>\<^sub>C t"
  and assm3:"prirelRef pa t (mkCTTick_Trace zz) (sa @ [[S]\<^sub>R, [Tock]\<^sub>E]) (unCT1 Q)"
  and assm4:"Tock \<notin> prirelref pa S"
  and assm6:"preRprirelRef pa aa zz (sa @ [[S]\<^sub>R, [Tock]\<^sub>E]) Q"
  then show "\<exists>t. [R]\<^sub>R # [Tock]\<^sub>E # aa \<lesssim>\<^sub>C t \<and> prirelRef pa t ([S]\<^sub>R # [Tock]\<^sub>E # mkCTTick_Trace zz) sa (unCT1 Q)"
    (*apply (rule_tac x="[S]\<^sub>R # [Tock]\<^sub>E # saa" in exI, auto) *)
    by (rule_tac x="[prirelref pa S]\<^sub>R # [Tock]\<^sub>E # t" in exI, auto) 
next
  fix pa::"'a cttevent partialorder"                                     
  fix aa zz sa saa ::"'a cttobs list"                               
  fix Q t e\<^sub>2                     
  assume assm1:"maximal(pa,e\<^sub>2)"
  and assm1:"aa \<lesssim>\<^sub>C t"                           
  and assm3:"preRprirelRef pa aa zz (sa @ [[e\<^sub>2]\<^sub>E]) Q"  
  and assm5:"prirelRef pa t (mkCTTick_Trace zz) (sa @ [[e\<^sub>2]\<^sub>E]) (unCT1 Q)" 
  then show "\<exists>t. [e\<^sub>2]\<^sub>E # aa \<lesssim>\<^sub>C t \<and> prirelRef pa t ([e\<^sub>2]\<^sub>E # mkCTTick_Trace zz) sa (unCT1 Q)"
    (*apply (rule_tac x="[e\<^sub>2]\<^sub>E # saa" in exI, auto) *)
    by (rule_tac x="[e\<^sub>2]\<^sub>E # t" in exI, auto)
next
  fix pa::"'a cttevent partialorder"
  fix aa zz sa ::"'a cttobs list"
  fix Q Z t e\<^sub>2 saa  
  assume assm1:"sa @ [[Z]\<^sub>R] \<in> Q"
  and assm2:"e\<^sub>2 \<notin> Z"
  and assm3:"\<forall>b. b \<in> Z \<or> \<not> e\<^sub>2 <\<^sup>*pa b"
  and assm4:"aa \<lesssim>\<^sub>C t"             
  and assm5:"prirelRef pa t (mkCTTick_Trace zz) (sa @ [[e\<^sub>2]\<^sub>E]) (unCT1 Q)"
  and assm6:"CT1 Q"
  and assm7:"CT4 Q"
  and assm8:"Tick \<in> Z" 
  and assm9:"preRprirelRef pa aa zz (sa @ [[e\<^sub>2]\<^sub>E]) Q"
  then show "\<exists>t. [e\<^sub>2]\<^sub>E # aa \<lesssim>\<^sub>C t \<and> prirelRef pa t ([e\<^sub>2]\<^sub>E # mkCTTick_Trace zz) sa (unCT1 Q)" 
    (*apply (rule_tac x="[e\<^sub>2]\<^sub>E # saa" in exI, auto) *)
    apply (rule_tac x="[e\<^sub>2]\<^sub>E # t" in exI, auto)             
    unfolding unCT1_def apply auto  
    using CTTick_mkCT1_simp 
    by (smt CTTick_def append1_eq_conv cttobs.inject(2) singletonD)
qed

lemma preRprirelRef_imp_prirelRef_suffix_CTTick:
  assumes "preRprirelRef p x s z P" "CT1 P" "CT4 P" "CTTick {s}"
  shows "\<exists>t. x \<lesssim>\<^sub>C t \<and> prirelRef p t s z (unCT1 P)"
  using assms by(simp add:preRprirelRef_imp_prirelRef_suffix)


lemma
  assumes "preRprirelRef p x s [] P"
  shows "\<exists>x. preRprirelRef p x (mkCTTick_Trace s) [] P"
  using assms apply (induct p x s _ P rule:preRprirelRef.induct, auto)

lemma
  "CT1 P \<Longrightarrow> CT4 P \<Longrightarrow>
           s \<in> P \<Longrightarrow>
           CTTick {s} \<Longrightarrow>
           preRprirelRef p x s [] P \<Longrightarrow> \<exists>s t. x \<lesssim>\<^sub>C t \<and> s \<in> P \<and> CTTick {s} \<and> prirelRef p t s [] (unCT1 P)"
  using preRprirelRef_imp_prirelRef_suffix_CTTick
  by blast     





lemma
  assumes "CTTick {[S]\<^sub>R # [Tock]\<^sub>E # zz}"
  shows "CTTick {[[S]\<^sub>R]}"
  using assms unfolding CTTick_def apply auto
  oops

lemma prirelRef_imp_preRprirelRef:
  assumes "CT0 P" "CT1 P" "CT4 P" "x \<lesssim>\<^sub>C t" "CTTick {s}" "prirelRef p t s z (unCT1 P)"
  shows "\<exists>s\<^sub>0. s\<^sub>0 \<lesssim>\<^sub>C s \<and> preRprirelRef p x s\<^sub>0 z P"
  using assms proof (induct p t s z P arbitrary:x rule:prirelRef.induct, auto)
  fix pa::"'a cttevent partialorder" 
  and Q::"'a cttobs list set"
  and sa xa::"'a cttobs list"
  assume "CT0 Q "
         "CT1 Q"
         "CT4 Q "
         "xa \<lesssim>\<^sub>C []"
  then show "\<exists>s\<^sub>0. s\<^sub>0 \<lesssim>\<^sub>C [] \<and> preRprirelRef pa xa s\<^sub>0 sa Q"
    using CTTick_Nil ctt_prefix_subset.simps(1) ctt_prefix_subset_antisym preRprirelRef.simps(1) by blast
next
  fix pa::"'a cttevent partialorder" 
  and S 
  and Q::"'a cttobs list set"
  and sa xa::"'a cttobs list"
  assume "CT0 Q "
         "CT1 Q"
         "CT4 Q "
         "xa \<lesssim>\<^sub>C [[prirelref pa S]\<^sub>R]"
         "CTTick {[[S]\<^sub>R]}"
  then show "\<exists>s\<^sub>0. s\<^sub>0 \<lesssim>\<^sub>C [[S]\<^sub>R] \<and> preRprirelRef pa xa s\<^sub>0 sa Q"
    apply (case_tac xa, auto)
     apply (rule exI[where x="[]"], auto)
    
    by (metis CTTickTrace.cases CTTick_def \<open>CTTick {[[S]\<^sub>R]}\<close> \<open>xa \<lesssim>\<^sub>C [[prirelref pa S]\<^sub>R]\<close> append_self_conv2 ctt_prefix_subset.elims(2) ctt_prefix_subset.simps(2) ctt_prefix_subset.simps(4) ctt_prefix_subset.simps(5) ctt_prefix_subset.simps(6) ctt_prefix_subset_refl cttobs.distinct(1) cttobs.exhaust cttobs.inject(2) init_refusal_ctt_prefix_subset insert_Nil list.distinct(1) list.inject preRprirelRef.simps(2) remdups_adj.cases singleton_iff)
next
  fix pa::"'a cttevent partialorder" 
  and S 
  and Q::"'a cttobs list set"
  and aa zz sa xa::"'a cttobs list"
  assume assm0: "(\<And>x. x \<lesssim>\<^sub>C aa \<Longrightarrow> CTTick {zz} \<Longrightarrow> \<exists>s\<^sub>0. s\<^sub>0 \<lesssim>\<^sub>C zz \<and> preRprirelRef pa x s\<^sub>0 (sa @ [[S]\<^sub>R, [Tock]\<^sub>E]) Q)"
    and assm1: "CT0 Q"
    and assm2: "CT1 Q"
    and assm3: "CT4 Q"
    and assm4: "xa \<lesssim>\<^sub>C [prirelref pa S]\<^sub>R # [Tock]\<^sub>E # aa"
    and assm5: "CTTick {[S]\<^sub>R # [Tock]\<^sub>E # zz}"
    and assm6: "Tock \<notin> prirelref pa S"
    and assm7: "prirelRef pa aa zz (sa @ [[S]\<^sub>R, [Tock]\<^sub>E]) (unCT1 Q)"
  then show "\<exists>s\<^sub>0. s\<^sub>0 \<lesssim>\<^sub>C [S]\<^sub>R # [Tock]\<^sub>E # zz \<and> preRprirelRef pa xa s\<^sub>0 sa Q"
  proof (cases xa)
    case Nil
    then show ?thesis 
      by (intro exI[where x="[]"], auto)
  next
    case (Cons y ya)
    then show ?thesis 
      proof (induct ya)
        case xaNil:Nil
        then show ?case
          proof (cases y)
            case (ObsEvent x1)
            then show ?thesis
              using \<open>xa \<lesssim>\<^sub>C [prirelref pa S]\<^sub>R # [Tock]\<^sub>E # aa\<close> local.Cons by auto
          next
            case (Ref x2)
            then show ?thesis using Cons xaNil assm0 assm1 assm2 assm3 assm4 assm5 apply auto
              (* by (rule_tac x="[[S]\<^sub>R]" in exI, auto) Need CT4s *) sorry
          qed
      next
        case Consb:(Cons b xb)
        then show ?case
          proof (cases y)
            case (ObsEvent x1)
            then show ?thesis
              using assm4 ctt_prefix_subset.simps(4) local.Cons by blast
          next
            case (Ref x2)
            then have "CTTick {zz}"
              using assm5 CTTick_Refusal_Tock' by blast
            then have "\<exists>s\<^sub>0. s\<^sub>0 \<lesssim>\<^sub>C zz \<and> preRprirelRef pa xb s\<^sub>0 (sa @ [[S]\<^sub>R, [Tock]\<^sub>E]) Q"
              using Ref Consb Cons assm0 assm1 assm2 assm3 assm4 assm5 assm6 apply auto
              by (cases b, auto)
            then have "\<exists>s\<^sub>0. s\<^sub>0 \<lesssim>\<^sub>C zz \<and> preRprirelRef pa ([x2]\<^sub>R # [Tock]\<^sub>E # xb) ([S]\<^sub>R # [Tock]\<^sub>E # s\<^sub>0) sa Q"
              using Ref Consb Cons assm0 assm1 assm2 assm3 assm4 assm5 assm6 by auto
            then have "\<exists>s\<^sub>0. s\<^sub>0 \<lesssim>\<^sub>C zz \<and> ([S]\<^sub>R # [Tock]\<^sub>E # s\<^sub>0) \<lesssim>\<^sub>C ([S]\<^sub>R # [Tock]\<^sub>E # zz) \<and> preRprirelRef pa ([x2]\<^sub>R # [Tock]\<^sub>E # xb) ([S]\<^sub>R # [Tock]\<^sub>E # s\<^sub>0) sa Q"
              by auto
            then have "\<exists>s\<^sub>0. s\<^sub>0 \<lesssim>\<^sub>C ([S]\<^sub>R # [Tock]\<^sub>E # zz) \<and> preRprirelRef pa ([x2]\<^sub>R # [Tock]\<^sub>E # xb) s\<^sub>0 sa Q"
              by blast
            then show ?thesis using Ref Consb Cons assm0 assm1 assm2 assm3 assm4 assm5 assm6
              apply auto
              by (cases b, auto)
          qed
      qed
    qed
next
  fix pa::"'a cttevent partialorder" 
  and e\<^sub>2
  and Q::"'a cttobs list set"
  and aa zz sa xa::"'a cttobs list"
  assume assm0: "(\<And>x. x \<lesssim>\<^sub>C aa \<Longrightarrow> CTTick {zz} \<Longrightarrow> \<exists>s\<^sub>0. s\<^sub>0 \<lesssim>\<^sub>C zz \<and> preRprirelRef pa x s\<^sub>0 (sa @ [[e\<^sub>2]\<^sub>E]) Q)"
    and assm1: "CT0 Q"
    and assm2: "CT1 Q"
    and assm3: "CT4 Q"
    and assm4: "xa \<lesssim>\<^sub>C [e\<^sub>2]\<^sub>E # aa"
    and assm5: "CTTick {[e\<^sub>2]\<^sub>E # zz}"
    and assm6: "prirelRef pa aa zz (sa @ [[e\<^sub>2]\<^sub>E]) (unCT1 Q)"
    and assm7: "maximal(pa,e\<^sub>2)"
  then show "\<exists>s\<^sub>0. s\<^sub>0 \<lesssim>\<^sub>C [e\<^sub>2]\<^sub>E # zz \<and> preRprirelRef pa xa s\<^sub>0 sa Q"
  proof (cases xa)
    case Nil
    then show ?thesis
      using ctt_prefix_subset.simps(1) preRprirelRef.simps(1) by blast
  next
    case (Cons a list)
    then show ?thesis 
    proof (cases a)
      case (ObsEvent x1)
      from ObsEvent have "list \<lesssim>\<^sub>C aa"
        using assm4 local.Cons by auto
      then have "CTTick {zz}"
        using assm5
        by (metis (no_types, lifting) CTTick_Nil CTTick_def append_butlast_last_id last_ConsR last_snoc list.discI singletonD singletonI)
      then have "\<exists>s\<^sub>0. s\<^sub>0 \<lesssim>\<^sub>C zz \<and> preRprirelRef pa list s\<^sub>0 (sa @ [[e\<^sub>2]\<^sub>E]) Q"
        using assm0
        by (simp add: \<open>list \<lesssim>\<^sub>C aa\<close>)
      then have "\<exists>s\<^sub>0. s\<^sub>0 \<lesssim>\<^sub>C zz \<and> preRprirelRef pa ([e\<^sub>2]\<^sub>E # list) ([e\<^sub>2]\<^sub>E # s\<^sub>0) sa Q"
        using assm0 assm1 assm2 assm3 assm4 assm5 assm6 assm7 Cons by auto
      then have "\<exists>s\<^sub>0. s\<^sub>0 \<lesssim>\<^sub>C zz \<and> ([e\<^sub>2]\<^sub>E # s\<^sub>0) \<lesssim>\<^sub>C ([e\<^sub>2]\<^sub>E # zz) \<and> preRprirelRef pa ([e\<^sub>2]\<^sub>E # list) ([e\<^sub>2]\<^sub>E # s\<^sub>0) sa Q"
        by auto
      then have "\<exists>s\<^sub>0. s\<^sub>0 \<lesssim>\<^sub>C ([e\<^sub>2]\<^sub>E # zz) \<and> preRprirelRef pa ([e\<^sub>2]\<^sub>E # list) s\<^sub>0 sa Q"
        by blast
      then show ?thesis
        using assm0 assm1 assm2 assm3 assm4 assm5 assm6 assm7 Cons ObsEvent by auto
    next
      case (Ref x2)
      then show ?thesis
        using assm4 local.Cons by auto
    qed
  qed  
next
  fix pa::"'a cttevent partialorder" 
  and e\<^sub>2
  and Q::"'a cttobs list set"
  and Z
  and aa zz sa xa::"'a cttobs list"
  assume assm0: "(\<And>x. x \<lesssim>\<^sub>C aa \<Longrightarrow> CTTick {zz} \<Longrightarrow> \<exists>s\<^sub>0. s\<^sub>0 \<lesssim>\<^sub>C zz \<and> preRprirelRef pa x s\<^sub>0 (sa @ [[e\<^sub>2]\<^sub>E]) Q)"
    and assm1: "CT0 Q"
    and assm2: "CT1 Q"
    and assm3: "CT4 Q"
    and assm4: "xa \<lesssim>\<^sub>C [e\<^sub>2]\<^sub>E # aa"
    and assm5: "CTTick {[e\<^sub>2]\<^sub>E # zz}"
    and assm6: "prirelRef pa aa zz (sa @ [[e\<^sub>2]\<^sub>E]) (unCT1 Q)"
    and assm7: "sa @ [[Z]\<^sub>R] \<in> unCT1 Q"
    and assm8: "e\<^sub>2 \<notin> Z"
    and assm9: "\<forall>b. b \<in> Z \<or> \<not> e\<^sub>2 <\<^sup>*pa b"
  then show "\<exists>s\<^sub>0. s\<^sub>0 \<lesssim>\<^sub>C [e\<^sub>2]\<^sub>E # zz \<and> preRprirelRef pa xa s\<^sub>0 sa Q "
  proof (cases xa)
    case Nil
    then show ?thesis
      using ctt_prefix_subset.simps(1) preRprirelRef.simps(1) by blast
  next
    case (Cons a list)
    then show ?thesis 
    proof (cases a)
      case (ObsEvent x1)
      have "\<exists>x. sa @ [[Z]\<^sub>R] \<in> x \<and> CTTick x \<and> (mkCT1 x) \<subseteq> Q"
        using assm2 assm3 assm7 unfolding unCT1_def by auto
      then have sa_Z_Q:"sa @ [[Z]\<^sub>R] \<in> Q"
        using CT1_mkCT1_simp assm2 by auto

      from ObsEvent have "list \<lesssim>\<^sub>C aa"
        using assm4 local.Cons by auto
      then have "CTTick {zz}"
        using assm5
        by (metis (no_types, lifting) CTTick_Nil CTTick_def append_butlast_last_id last_ConsR last_snoc list.discI singletonD singletonI)
      then have "\<exists>s\<^sub>0. s\<^sub>0 \<lesssim>\<^sub>C zz \<and> preRprirelRef pa list s\<^sub>0 (sa @ [[e\<^sub>2]\<^sub>E]) Q"
        using assm0
        by (simp add: \<open>list \<lesssim>\<^sub>C aa\<close>)
      then have "\<exists>s\<^sub>0. s\<^sub>0 \<lesssim>\<^sub>C zz \<and> preRprirelRef pa ([e\<^sub>2]\<^sub>E # list) ([e\<^sub>2]\<^sub>E # s\<^sub>0) sa Q"
        using assm0 assm1 assm2 assm3 assm4 assm5 assm6 assm7 assm8 assm9 Cons sa_Z_Q apply auto
        by (meson CTTick_def \<open>\<exists>x. sa @ [[Z]\<^sub>R] \<in> x \<and> CTTick x \<and> mkCT1 x \<subseteq> Q\<close>)
      then have "\<exists>s\<^sub>0. s\<^sub>0 \<lesssim>\<^sub>C zz \<and> ([e\<^sub>2]\<^sub>E # s\<^sub>0) \<lesssim>\<^sub>C ([e\<^sub>2]\<^sub>E # zz) \<and> preRprirelRef pa ([e\<^sub>2]\<^sub>E # list) ([e\<^sub>2]\<^sub>E # s\<^sub>0) sa Q"
        by auto
      then have "\<exists>s\<^sub>0. s\<^sub>0 \<lesssim>\<^sub>C ([e\<^sub>2]\<^sub>E # zz) \<and> preRprirelRef pa ([e\<^sub>2]\<^sub>E # list) s\<^sub>0 sa Q"
        by blast
      then show ?thesis
        using assm0 assm1 assm2 assm3 assm4 assm5 assm6 assm7 Cons ObsEvent by auto
    next
      case (Ref x2)
      then show ?thesis
        using assm4 local.Cons by auto
    qed
  qed   
qed

lemma
  assumes "CT4 P" "x \<in> P"
  shows "mkCTTick_Trace x \<in> P"
  using assms sledgehammer

lemma
  assumes "CT0 P" "CT1 P" "CT4 P"
  shows
  "{\<rho>|\<rho> s t. \<rho> \<lesssim>\<^sub>C t \<and> s \<in> P \<and> CTTick {s} \<and> prirelRef p t s [] (unCT1 P)}
   =
   {t|s t. s \<in> P \<and> preRprirelRef p t s [] P}"
  using assms apply auto
  apply (meson CT1_def prirelRef_imp_preRprirelRef)
  using preRprirelRef_imp_prirelRef_suffix'' sledgehammer
  oops
(*
  apply(induct s arbitrary:t x rule:rev_induct)
proof(induct x arbitrary:t s rule:rev_induct)
  case Nil
  then show ?case
    apply (intro exI[where x="[]"], auto)
    using assms
    using CT0_CT1_empty apply blast
    unfolding CTTick_def by auto
next
  case (snoc z zs)
  then obtain y ys where tz:"t = ys @ [y]"
    apply auto
    by (metis ctt_prefix_subset.simps(6) list.exhaust rev_exhaust)
  then have pri_ys:"prirelRef p (ys @ [y]) s [] (unCT1 P)"
    using snoc by auto
  then obtain x xs where xs:"s = xs @ [x]"
    by (metis neq_Nil_conv prirelRef.simps(28) rev_exhaust)
  then have pri_ys_xs:"prirelRef p (ys @ [y]) (xs @ [x]) [] (unCT1 P)"
    using pri_ys by auto

  have "zs @ [z] \<lesssim>\<^sub>C ys @ [y]"
    using snoc tz by auto
  then have "zs \<lesssim>\<^sub>C ys @ [y]"
    using ctt_prefix_subset_front by blast
  then have hyp:"\<exists>s\<^sub>0. s\<^sub>0 \<lesssim>\<^sub>C s \<and> s\<^sub>0 \<in> P \<and> CTTick {s\<^sub>0} \<and> preRprirelRef p zs s\<^sub>0 [] (unCT1 P)"
    using snoc tz by blast

  (* Now how do we extend zs to (zs@[z])? *)

  then show ?case
  proof (cases z)
    case (Ref x2)
    then show ?thesis sledgehammer
  next
    case (ObsEvent x1)
    then show ?thesis sorry
  qed
qed*)

lemma
  "(\<exists>t. \<rho> \<lesssim>\<^sub>C t \<and> prirelRef p t s [] (unCT1 P) \<and> s \<in> P \<and> CTTick {s}) = (preRprirelRef p \<rho> s [] P \<and> s \<in> P \<and> CTTick {s})"
  apply auto

lemma prirelRef_imp_preRprirelRef:
  assumes "\<rho> \<lesssim>\<^sub>C t" "prirelRef p t s [] (unCT1 P)" "CT3 P" "CT4 P"
  shows "preRprirelRef p \<rho> s [] P"
  using assms apply (induct p t s _ P arbitrary:\<rho> rule:preRprirelRef.induct, auto)
  using ctt_prefix_subset.simps(1) ctt_prefix_subset_antisym preRprirelRef.simps(1) apply blast
      apply (case_tac \<rho>', auto, case_tac a, auto, case_tac list, auto)
     apply (case_tac \<rho>', auto)
  sledgehammer
(*
  apply (case_tac \<rho>', auto, case_tac a, auto)
  using ctt_prefix_subset.simps(1) ctt_prefix_subset_antisym preRprirelRef.simps(2) apply blast
     apply (case_tac \<rho>', auto, case_tac a, auto, case_tac list, auto)
     apply (case_tac a, auto, case_tac lista, auto)
    apply (case_tac \<rho>', auto, case_tac a, auto, case_tac list, auto)
    apply (case_tac a, auto, case_tac lista, auto)
   apply (case_tac \<rho>', auto, case_tac a, auto)
  apply (case_tac \<rho>', auto, case_tac a, auto) 
  unfolding unCT1_def apply auto
  using UnCI  mkCT1_def subsetCE
  by (metis (no_types, lifting))*)
  (* Likely need a weakened form of CT2 *)



lemma
  assumes "preRprirelRef p \<rho> s [] P" "CTTick {s}" "\<rho> \<lesssim>\<^sub>C t"
  shows "prirelRef p t s [] (unCT1 P)"
  using assms nitpick
  apply (induct p \<rho> s _ P arbitrary:t rule:preRprirelRef.induct, auto)
  apply (case_tac \<rho>', auto)
  sledgehammer

  thm preRprirelRef.induct

lemma
  assumes "preRprirelRef p \<rho> s [] P" (* "\<rho> \<lesssim>\