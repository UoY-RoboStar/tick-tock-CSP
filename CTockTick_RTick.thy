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
"unCT1 P = \<Union>{x. CTM2a x \<and> CTM2b x \<and> CTTick x \<and> CT1c x \<and> (mkCT1 x) \<subseteq> P}"

lemma unCT1_mono:
  assumes "P \<subseteq> Q"
  shows "unCT1(P) \<subseteq> unCT1(Q)"
  using assms unfolding unCT1_def by auto

lemma
  assumes "CT4 P" "CT1 P"
  shows "P \<subseteq> mkCT1 (unCT1 P)"
  using assms unfolding mkCT1_def unCT1_def apply auto oops

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

lemma CTTick_mkCT1_simp:
  assumes "CT1 P" "CT4 P"
  shows "(\<exists>x. s \<in> x \<and> CTTick x \<and> (mkCT1 x) \<subseteq> P) = (s \<in> P \<and> CTTick {s})"
  using assms apply safe
  using mkCT1_def apply fastforce
  using CTTick_dist_union 
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
  case (snoc x xs)
  then have "CTMPick xs [] P"
    using assms CT1c_prefix_concat_in by blast
  then show ?case
  proof (cases x)
    case (ObsEvent x1)
    then show ?thesis using snoc CTMPick_extend_event_imp
      using \<open>CTMPick xs [] P\<close> by blast
  next
    case (Ref x2)
    then show ?thesis using snoc CTMPick_extend_ref_imp
      by (smt CTM2a_def CTM2b_def \<open>CTMPick xs [] P\<close> append.left_neutral le_sup_iff mkCT1_def subsetCE)
  qed
qed

lemma
  assumes "CTMPick s [] P" "s \<in> P"
  shows "CTM2a {s}"
  nitpick



lemma CTTick_mkCT1_simp:
  assumes "CT1 P" "CT4 P"
  shows "(\<exists>x. s \<in> x \<and> CTM2a x \<and> CTM2b x \<and> CTTick x \<and> CT1c x \<and> (mkCT1 x) \<subseteq> P) 
         = 
         (s \<in> P \<and> CTTick {s} \<and> CTMPick s [] P)"
  using assms apply safe
  using mkCT1_def apply fastforce
  using CTTick_dist_union 
    apply (metis insert_Diff insert_is_Un)
  using CTM2a_CTM2b_CT1c_mkCT1_imp_CTMPick apply blast
  (* Need to define mkCTM2a mkCTM2b and mkCT1c then can prove the following goal. *)
  apply (rule_tac x="{s}" in exI, auto) 
  unfolding mkCT1_def apply auto
  oops

lemma CT14_CTTick_mkCT1_exists:
  assumes "CT1 P" "CT4 P"
  shows "(\<exists>Z. s @ [[Z]\<^sub>R] \<in> unCT1 P \<and> e\<^sub>2 \<notin> Z \<and> \<not>(\<exists>b. b \<notin> Z \<and> e\<^sub>2 <\<^sup>*p b))
         =
         (\<exists>Z. s @ [[Z]\<^sub>R] \<in> P \<and> Tick \<in> Z \<and> e\<^sub>2 \<notin> Z \<and> \<not>(\<exists>b. b \<notin> Z \<and> e\<^sub>2 <\<^sup>*p b))"
proof -
  have "(\<exists>Z. s @ [[Z]\<^sub>R] \<in> unCT1 P \<and> e\<^sub>2 \<notin> Z \<and> \<not>(\<exists>b. b \<notin> Z \<and> e\<^sub>2 <\<^sup>*p b))
        =
        (\<exists>Z. s @ [[Z]\<^sub>R] \<in> (\<Union>{x. CTTick x \<and> (mkCT1 x) \<subseteq> P}) \<and> e\<^sub>2 \<notin> Z \<and> \<not>(\<exists>b. b \<notin> Z \<and> e\<^sub>2 <\<^sup>*p b))"
    unfolding unCT1_def by auto
  also have "...
        =
        (\<exists>Z x. s @ [[Z]\<^sub>R] \<in> x \<and> CTTick x \<and> (mkCT1 x) \<subseteq> P \<and> e\<^sub>2 \<notin> Z \<and> \<not>(\<exists>b. b \<notin> Z \<and> e\<^sub>2 <\<^sup>*p b))"
    by auto
  also have "... =
       (\<exists>Z. s @ [[Z]\<^sub>R] \<in> P \<and> CTTick {s @ [[Z]\<^sub>R]} \<and> e\<^sub>2 \<notin> Z \<and> \<not>(\<exists>b. b \<notin> Z \<and> e\<^sub>2 <\<^sup>*p b))"
    using assms CTTick_mkCT1_simp apply auto
    by metis
  also have "... =
       (\<exists>Z. s @ [[Z]\<^sub>R] \<in> P \<and> Tick \<in> Z \<and> e\<^sub>2 \<notin> Z \<and> \<not>(\<exists>b. b \<notin> Z \<and> e\<^sub>2 <\<^sup>*p b))"
    using assms
    using CTTick_def by blast
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
                          \<and> s \<in> (\<Union>{x. CTTick x \<and> (mkCT1 x) \<subseteq> P}) 
                          \<and> prirelRef p t s [] (unCT1 P)})"
    unfolding unCT1_def by auto
  also have "... = ({\<rho>|\<rho> s t. \<rho> \<lesssim>\<^sub>C t 
                          \<and> (\<exists>x. s \<in> x \<and> CTTick x \<and> (mkCT1 x) \<subseteq> P)
                          \<and> prirelRef p t s [] (unCT1 P)})"
    by auto
  also have "... = ({\<rho>|\<rho> s t. \<rho> \<lesssim>\<^sub>C t 
                          \<and> s \<in> P \<and> CTTick {s}
                          \<and> prirelRef p t s [] (unCT1 P)})"
    apply auto
    using assms CTTick_mkCT1_simp
    apply (metis (mono_tags, lifting))
    by (metis (mono_tags, lifting) CTTick_mkCT1_simp assms(1) assms(2))
  also have "... = ({\<rho>|\<rho> s t. \<rho> \<lesssim>\<^sub>C t 
                          \<and> s \<in> P \<and> CTTick {s}
                          \<and> prirelRef p t s [] (unCT1 P)})"
    oops

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
  assumes "preRprirelRef p \<rho> s [] P" (* "\<rho> \<lesssim>\<^sub>C t" "size s = size t" *)
  shows "\<exists>t. size s = size t \<and> \<rho> \<lesssim>\<^sub>C t \<and> prirelRef p t s [] (unCT1 P)"
  using assms apply (induct p \<rho> s "[]::'a cttobs list" P rule:preRprirelRef.induct, auto)
  apply simp_all
  using prirelRef.simps(1) apply blast
                   apply (meson ctt_prefix_subset.simps(1) ctt_prefix_subset.simps(2) prirelRef.simps(2))
  apply (rule_tac x="[prirelref p S]\<^sub>R # [Tock]\<^sub>E # aa" in exI, auto)
sledgehammer
end