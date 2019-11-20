theory TickTock_Max_TT1_Pri

imports
  "TickTock_Max_TT1"
  "TickTock_Max_FL_Priority"
begin

text \<open> This theory defines an Pri operator for TickTock and shows that
       it can be obtained via the Galois connection with TickTock_Max_TT1. \<close>

section \<open> Preliminaries \<close>

subsection \<open> TTMPick \<close>

text \<open> To facilitate identifying maximal TickTock traces we define an 
       auxiliary function TTMPick below that is useful in later proofs. \<close>

fun TTMPick :: "'e ttobs list \<Rightarrow> 'e ttobs list \<Rightarrow> 'e ttobs list set \<Rightarrow> bool" where
"TTMPick [] s P = True" |
"TTMPick ([X]\<^sub>R # xs) s P = ((\<forall>e. e \<notin> X \<and> e \<noteq> Tock \<longrightarrow> s @ [[e]\<^sub>E] \<in> P)
                           \<and>
                           (Tock \<notin> X \<longrightarrow> s @ [[X]\<^sub>R,[Tock]\<^sub>E] \<in> P) \<and> Tick \<in> X \<and> TTMPick xs (s @ [[X]\<^sub>R]) P)" |
"TTMPick ([e]\<^sub>E # xs) s P = TTMPick xs (s @ [[e]\<^sub>E]) P"

text \<open> Given a trace fl, starting at trace 's', TTMPick ascertains whether fl
       is a maximal trace in process P. \<close>

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

lemma TTMPick_imp_RefTock_in:
  assumes "TTMPick (\<rho> @ [[X]\<^sub>R] @ x) s P" "Tock \<notin> X"
  shows "s @ \<rho> @ [[X]\<^sub>R, [Tock]\<^sub>E] \<in> P"
  using assms by (induct \<rho> s P rule:TTMPick.induct, auto)

lemma TTMPick_imp_Event_in:
  assumes "TTMPick (\<rho> @ [[X]\<^sub>R] @ x) s P" "e \<notin> X" "e \<noteq> Tock"
  shows "s @ \<rho> @ [[e]\<^sub>E] \<in> P"
  using assms by (induct \<rho> s P rule:TTMPick.induct, auto)

text \<open> The following key lemma enables the expansion of the quantification in unTT1(P)
       to a predicate involving TTMPick, which is easier for doing proofs by induction. \<close>

lemma TTM3_mkTT1_simp:
  assumes "TT1 P" "TT4w P"
  shows "(\<exists>x. s \<in> x \<and> TTM1 x \<and> TTM2 x \<and> TTM3 x \<and> TT1w x \<and> (mkTT1 x) \<subseteq> P) 
         = 
         (s \<in> P \<and> TTM3 {s} \<and> TTMPick s [] P)" (* FIXME: Ugly proof *)
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

subsection \<open> mkTTMP \<close>

text \<open> Similarly to TTMPick we also define a function that constructs maximal traces. \<close>

(* Problem below is from 's' how to achieve target 's'? Need a way to construct it
   explicitly, then just need to show that x \<lesssim>\<^sub>C t. *)
fun mkTTMP :: "'e ttobs list \<Rightarrow> 'e ttobs list \<Rightarrow> 'e ttobs list set \<Rightarrow> 'e ttobs list" where
"mkTTMP [] s P = []" |
"mkTTMP ([X]\<^sub>R # xs) s P =
        ([X \<union> {e. (e \<noteq> Tock \<and> s @ [[e]\<^sub>E] \<notin> P) \<or> (e = Tock \<and> s @ [[X]\<^sub>R,[Tock]\<^sub>E] \<notin> P)} \<union> {Tick}]\<^sub>R # 
         (mkTTMP xs (s @ [[X]\<^sub>R]) P))" |
"mkTTMP ([e]\<^sub>E # xs) s P = ([e]\<^sub>E # (mkTTMP xs (s @ [[e]\<^sub>E]) P))"

text \<open> Starting at a trace 's' in P, @{term mkTTMP} x s P, yields a trace that is the
       maximal version of 'x' in P. This function is useful in a number of proofs by
       induction. \<close>

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

lemma TTM3_mkTTMP_singleton:
  "TTM3 {(mkTTMP s i P)}"
  unfolding TTM3_def by (induct s i P rule:mkTTMP.induct, auto)

section \<open> PriTT1 \<close>

text \<open> The first version of Pri for TickTock induced by the Galois connection is defined below. \<close>

definition prirefTT1 :: "('e ttevent) partialorder \<Rightarrow> ('e ttevent) set \<Rightarrow> ('e ttobs) list \<Rightarrow> ('e ttobs) list set \<Rightarrow> ('e ttevent) set" where
"prirefTT1 pa S sa Q = 
  {z. ((z = Tock \<and> sa @ [[S]\<^sub>R, [Tock]\<^sub>E] \<in> Q) \<longrightarrow> (\<exists>b. b \<notin> S \<and> sa @ [[b]\<^sub>E] \<in> Q \<and> b \<noteq> Tock \<and> b \<noteq> Tick \<and> z <\<^sup>*pa b))
        \<and>
       ((z \<notin> S \<and> sa @ [[z]\<^sub>E] \<in> Q \<and> z \<noteq> Tock \<and> z \<noteq> Tick) \<longrightarrow>
          ((sa @ [[S]\<^sub>R, [Tock]\<^sub>E] \<in> Q \<and> z <\<^sup>*pa Tock)
            \<or>
           (\<exists>b. b \<notin> S \<and> sa @ [[b]\<^sub>E] \<in> Q \<and> b \<noteq> Tock \<and> b \<noteq> Tick \<and> z <\<^sup>*pa b)))}"

fun priTT1 :: "('e ttevent) partialorder \<Rightarrow> ('e ttobs) list \<Rightarrow> ('e ttobs) list \<Rightarrow> ('e ttobs) list \<Rightarrow> ('e ttobs) list set \<Rightarrow> bool" where
"priTT1 p [] [] s Q = True" |
"priTT1 p [[R]\<^sub>R] [[S]\<^sub>R] s Q = (R \<subseteq> prirefTT1 p S s Q)" |
"priTT1 p ([R]\<^sub>R # [Tock]\<^sub>E # aa) ([S]\<^sub>R # [Tock]\<^sub>E # zz) s Q =
   ((R \<subseteq> prirefTT1 p S s Q) \<and> Tock \<notin> prirefTT1 p S s Q \<and> priTT1 p aa zz (s @ [[S]\<^sub>R,[Tock]\<^sub>E]) Q)" |
"priTT1 p ([e\<^sub>1]\<^sub>E # aa) ([e\<^sub>2]\<^sub>E # zz) s Q
 = 
 (e\<^sub>1 = e\<^sub>2 \<and> priTT1 p aa zz (s @ [[e\<^sub>1]\<^sub>E]) Q \<and>
  (maximal(p,e\<^sub>2) 
   \<or> 
  (\<exists>Z. s @ [[Z]\<^sub>R] \<in> Q
      \<and> (\<forall>e. (e \<notin> Z \<and> e \<noteq> Tock) \<longrightarrow> s @ [[e]\<^sub>E] \<in> Q)
      \<and> (Tock \<notin> Z \<longrightarrow> s @ [[Z]\<^sub>R,[Tock]\<^sub>E] \<in> Q) \<and> Tick \<in> Z
      \<and> e\<^sub>2 \<notin> Z \<and> \<not>(\<exists>b. b \<notin> Z \<and> e\<^sub>2 <\<^sup>*p b))))" |
"priTT1 p x y s Q = False"

lemma prirefMaxTT_prirefTT1_part:
  assumes "ttWFx Q"
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
      using ttWFx_any_cons_end_tock by blast
    finally show ?thesis .
  qed

lemma prirefMaxTT_prirefTT1:
  assumes "ttWFx Q"
  shows
  "prirefMaxTT pa (S \<union> {e. e \<noteq> Tock \<and> sa @ [[e]\<^sub>E] \<notin> Q \<or> e = Tock \<and> sa @ [[S]\<^sub>R, [Tock]\<^sub>E] \<notin> Q} \<union> {Tick})
   = 
   prirefTT1 pa S sa Q"
proof -
  have "prirefMaxTT pa (S \<union> {e. e \<noteq> Tock \<and> sa @ [[e]\<^sub>E] \<notin> Q \<or> e = Tock \<and> sa @ [[S]\<^sub>R, [Tock]\<^sub>E] \<notin> Q} \<union> {Tick})
        =
        {z. z \<notin> S \<union> {e. e \<noteq> Tock \<and> sa @ [[e]\<^sub>E] \<notin> Q \<or> e = Tock \<and> sa @ [[S]\<^sub>R, [Tock]\<^sub>E] \<notin> Q} \<union> {Tick} \<longrightarrow>
        (\<exists>b. b \<notin> S \<union> {e. e \<noteq> Tock \<and> sa @ [[e]\<^sub>E] \<notin> Q \<or> e = Tock \<and> sa @ [[S]\<^sub>R, [Tock]\<^sub>E] \<notin> Q} \<union> {Tick} \<and> z <\<^sup>*pa b)}"
    unfolding prirefMaxTT_def by auto
  also have "... =
        {z. ((((z = Tock \<and> sa @ [[S]\<^sub>R, [Tock]\<^sub>E] \<in> Q) 
              \<or>
              (z \<notin> S \<and> sa @ [[z]\<^sub>E] \<in> Q \<and> z \<noteq> Tock \<and> z \<noteq> Tick)
              \<or>
              (z \<notin> S \<and> sa @ [[z]\<^sub>E] \<in> Q \<and> sa @ [[S]\<^sub>R, [Tock]\<^sub>E] \<in> Q \<and> z \<noteq> Tock \<and> z \<noteq> Tick)))) \<longrightarrow>
        (\<exists>b. b \<notin> S \<union> {e. e \<noteq> Tock \<and> sa @ [[e]\<^sub>E] \<notin> Q \<or> e = Tock \<and> sa @ [[S]\<^sub>R, [Tock]\<^sub>E] \<notin> Q} \<union> {Tick} \<and> z <\<^sup>*pa b)}"
    using prirefMaxTT_prirefTT1_part assms
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
    using prirefMaxTT_prirefTT1_part assms
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
  also have "... = prirefTT1 pa S sa Q"
    unfolding prirefTT1_def by auto
  finally show ?thesis .
qed

(*
lemma priMaxTT_start_Ref_extends:
  assumes "TT1 P" "TT2 P" "TT4 P" "priMaxTT pa t s (sa @ zs) (unTT1 Q)"
  shows "priMaxTT pa t s (sa @ (mkTTMP zs sa Q)) (unTT1 Q)"
  using assms apply (induct pa t s zs Q arbitrary: sa rule:priMaxTT.induct, auto)
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
   PriMax in this model, whereby we take specific 's' and not arbitrary ones. *)
lemma priMaxTT_unTT1_case:
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

(* Too strong, as in general it is not possible to pick a trace 'aa' and apply
    mkTTMP to it and get a satisfactory result in priMaxTT, I think? Because
    such closure woult be based on the trace in P, which are not necessarily
    available after prioritisation. So it is non-trivial to construct the 
    appropriate sets, in general. This has to come from priTT1 itself.
lemma
  assumes "priTT1 pa aa zz i P" "TT4 P" "ttWFx P" "TT2 P" "TT1 P" 
  shows "priMaxTT pa (mkTTMP aa i P) (mkTTMP zz i P) i (unTT1 P)"
  using assms proof(induct pa aa zz i P rule:priTT1.induct, simp_all)
  fix p 
  fix R::"'a ttevent set"
  fix S s Q
  assume TT4_healthy: "TT4 Q"
     and ttWFx_healthy:  "ttWFx Q"
     and TT2_healthy: "TT2 Q"
     and TT1_healthy:  "TT1 Q"
     and priMaxTT:    "R \<subseteq> prirefTT1 p S s Q"
  then show "prirefMaxTT p (insert Tick (S \<union> {e. e \<noteq> Tock \<and> s @ [[e]\<^sub>E] \<notin> Q \<or> e = Tock \<and> s @ [[S]\<^sub>R, [Tock]\<^sub>E] \<notin> Q})) =
       insert Tick (R \<union> {e. e \<noteq> Tock \<and> s @ [[e]\<^sub>E] \<notin> Q \<or> e = Tock \<and> s @ [[R]\<^sub>R, [Tock]\<^sub>E] \<notin> Q})"
  proof -
    have "prirefMaxTT p (insert Tick (S \<union> {e. e \<noteq> Tock \<and> s @ [[e]\<^sub>E] \<notin> Q \<or> e = Tock \<and> s @ [[S]\<^sub>R, [Tock]\<^sub>E] \<notin> Q}))
          =
          prirefTT1 p S s Q"
      using ttWFx_healthy prirefMaxTT_prirefTT1 by fastforce
    have "{e. e \<noteq> Tock \<and> s @ [[e]\<^sub>E] \<notin> Q \<or> e = Tock \<and> s @ [[S]\<^sub>R, [Tock]\<^sub>E] \<notin> Q} \<union> {Tick} \<subseteq> prirefTT1 p S s Q"
      using \<open>prirefMaxTT p (insert Tick (S \<union> {e. e \<noteq> Tock \<and> s @ [[e]\<^sub>E] \<notin> Q \<or> e = Tock \<and> s @ [[S]\<^sub>R, [Tock]\<^sub>E] \<notin> Q})) = prirefTT1 p S s Q\<close> prirefMaxTT_def by auto
    have "prirefTT1 p S s Q \<subseteq> R \<union> {e. e \<noteq> Tock \<and> s @ [[e]\<^sub>E] \<notin> Q \<or> e = Tock \<and> s @ [[R]\<^sub>R, [Tock]\<^sub>E] \<notin> Q} \<union> {Tick}"
      using priMaxTT  apply auto
    apply (simp_all add: prirefTT1_def)
  oops
*)

lemma mkTTMP_dist_concat:
  "mkTTMP (xs @ [x]) i P = (mkTTMP xs i P) @ mkTTMP [x] (i @ xs) P"
  by (induct xs i P arbitrary:x rule:mkTTMP.induct, auto)

lemma mkTTMP_fixpoint_eq_TTMPick:
  "(mkTTMP s i P = s) = TTMPick s i P"
  by (induct s i P rule:mkTTMP.induct, auto)

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
  assumes "s @ z \<in> P" "TT4 P" "ttWFx P" "TT2 P" "TT1 P"
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
  assumes "s \<in> P" "TT4 P" "ttWFx P" "TT2 P" "TT1 P"
  shows "(mkTTMP s [] P) \<in> P"
  using assms mkTTMP_in_P
  by (metis append_Nil2)

lemma priMaxTT_unTT1_case_specific:
  assumes "TT4 P" "ttWFx P" "TT2 P" "TT1 P"
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

lemma priMaxTT_start_Ref_extends:
  assumes "TT1 Q" "TT2 Q" "TT4w Q" "priMaxTT pa t s (sa @ [[S]\<^sub>R, [Tock]\<^sub>E] @ z) (unTT1 Q)" 
  shows "priMaxTT pa t s (sa @ [[S \<union> {e. e \<noteq> Tock \<and> sa @ [[e]\<^sub>E] \<notin> Q \<or> e = Tock \<and> sa @ [[S]\<^sub>R, [Tock]\<^sub>E] \<notin> Q} \<union> {Tick}]\<^sub>R, [Tock]\<^sub>E] @ z) (unTT1 Q)"
  using assms proof(induct pa t s z Q arbitrary:S sa rule:priMaxTT.induct, auto)
  fix p 
  fix aa::"'a ttobs list" 
  fix e\<^sub>2 zz sb Qa Sa saa Z
  assume 
    hyp:  "(\<And>S sa.
           priMaxTT p aa zz (sa @ [S]\<^sub>R # [Tock]\<^sub>E # sb @ [[e\<^sub>2]\<^sub>E]) (unTT1 Qa) \<Longrightarrow>
           priMaxTT p aa zz
            (sa @ [insert Tick (S \<union> {e. e \<noteq> Tock \<and> sa @ [[e]\<^sub>E] \<notin> Qa \<or> e = Tock \<and> sa @ [[S]\<^sub>R, [Tock]\<^sub>E] \<notin> Qa})]\<^sub>R # [Tock]\<^sub>E # sb @ [[e\<^sub>2]\<^sub>E])
            (unTT1 Qa))"
    and TT1_healthy:    "TT1 Qa" 
    and TT2_healthy:   "TT2 Qa"
    and TT4w_healthy:   "TT4w Qa"
    and priMaxTT:      "priMaxTT p aa zz (saa @ [Sa]\<^sub>R # [Tock]\<^sub>E # sb @ [[e\<^sub>2]\<^sub>E]) (unTT1 Qa)"
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

lemma priTT1_TTMPick_imp_priMaxTT:
  assumes "priTT1 p x s i P" "TT4 P" "ttWFx P" "TT2 P" "TT1 P"
  shows "\<exists>t. x \<lesssim>\<^sub>C t \<and> TTMPick (mkTTMP s i P) i P \<and> priMaxTT p t (mkTTMP s i P) (mkTTMP i [] P) (unTT1 P)"
proof -
  have "(\<exists>t. x \<lesssim>\<^sub>C t \<and> TTMPick (mkTTMP s i P) i P \<and> priMaxTT p t (mkTTMP s i P) (mkTTMP i [] P) (unTT1 P))
        =
        (\<exists>t. x \<lesssim>\<^sub>C t \<and> priMaxTT p t (mkTTMP s i P) (mkTTMP i [] P) (unTT1 P))"
    using assms TT2_imp_TTMPick_mkTTMP by blast
  also have "... = True"
    using assms proof (induct p x s i P rule:priTT1.induct, auto)
    fix pa sa 
    fix Q::"'a ttobs list set"
    assume TT4_healthy: "TT4 Q"
     and    ttWFx_healthy: "ttWFx Q"
     and   TT2_healthy: "TT2 Q"
     and    TT1_healthy: "TT1 Q"
    show "\<exists>t. priMaxTT pa t [] sa (unTT1 Q)"
      using priMaxTT.simps(1) by blast
  next
    fix pa 
    fix R::"'a ttevent set"
    fix S sa Q
    assume R_subset:"R \<subseteq> prirefTT1 pa S sa Q"
     and  TT4_healthy: "TT4 Q"
     and   ttWFx_healthy: "ttWFx Q"
     and  TT2_healthy: "TT2 Q"
     and   TT1_healthy: "TT1 Q"
    then show "\<exists>t. [[R]\<^sub>R] \<lesssim>\<^sub>C t \<and>
           priMaxTT pa t [[insert Tick (S \<union> {e. e \<noteq> Tock \<and> sa @ [[e]\<^sub>E] \<notin> Q \<or> e = Tock \<and> sa @ [[S]\<^sub>R, [Tock]\<^sub>E] \<notin> Q})]\<^sub>R] (mkTTMP sa [] Q) (unTT1 Q)"
    proof -
      from R_subset have "R \<subseteq> prirefTT1 pa S sa Q"
        by auto
      then have "R \<subseteq> prirefMaxTT pa (S \<union> {e. e \<noteq> Tock \<and> sa @ [[e]\<^sub>E] \<notin> Q \<or> e = Tock \<and> sa @ [[S]\<^sub>R, [Tock]\<^sub>E] \<notin> Q} \<union> {Tick})"
        using prirefMaxTT_prirefTT1 ttWFx_healthy by blast
      then have "[[R]\<^sub>R] \<lesssim>\<^sub>C [[prirefMaxTT pa (S \<union> {e. e \<noteq> Tock \<and> sa @ [[e]\<^sub>E] \<notin> Q \<or> e = Tock \<and> sa @ [[S]\<^sub>R, [Tock]\<^sub>E] \<notin> Q} \<union> {Tick})]\<^sub>R]"
        by auto
      then have "[[R]\<^sub>R] \<lesssim>\<^sub>C [[prirefMaxTT pa (S \<union> {e. e \<noteq> Tock \<and> sa @ [[e]\<^sub>E] \<notin> Q \<or> e = Tock \<and> sa @ [[S]\<^sub>R, [Tock]\<^sub>E] \<notin> Q} \<union> {Tick})]\<^sub>R] \<and>
                  priMaxTT pa [[prirefMaxTT pa (S \<union> {e. e \<noteq> Tock \<and> sa @ [[e]\<^sub>E] \<notin> Q \<or> e = Tock \<and> sa @ [[S]\<^sub>R, [Tock]\<^sub>E] \<notin> Q} \<union> {Tick})]\<^sub>R]
                               [[insert Tick (S \<union> {e. e \<noteq> Tock \<and> sa @ [[e]\<^sub>E] \<notin> Q \<or> e = Tock \<and> sa @ [[S]\<^sub>R, [Tock]\<^sub>E] \<notin> Q})]\<^sub>R] (mkTTMP sa [] Q) (unTT1 Q)"
        by auto
      then show ?thesis by blast
    qed
  next
    fix pa 
    fix R S::"'a ttevent set"
    fix aa zz sa t::"'a ttobs list"
    fix Q::"'a ttobs list set"
    assume R_subset:"R \<subseteq> prirefTT1 pa S sa Q"
     and  TT4_healthy: "TT4 Q"
     and   ttWFx_healthy: "ttWFx Q"
     and  TT2_healthy: "TT2 Q"
     and   TT1_healthy: "TT1 Q"
     and aa_prefix_t:"aa \<lesssim>\<^sub>C t"
     and priMaxTT_assm:"priMaxTT pa t (mkTTMP zz (sa @ [[S]\<^sub>R, [Tock]\<^sub>E]) Q) (mkTTMP (sa @ [[S]\<^sub>R, [Tock]\<^sub>E]) [] Q) (unTT1 Q)"
     and Tock_not_in:"Tock \<notin> prirefTT1 pa S sa Q"
     and "priTT1 pa aa zz (sa @ [[S]\<^sub>R, [Tock]\<^sub>E]) Q"
    then have TT4w_healthy: "TT4w Q" 
      using TT4_healthy TT1_healthy TT4_TT1_imp_TT4w by blast
    then obtain Y where Y:"Y = (mkTTMP zz (sa @ [[S]\<^sub>R, [Tock]\<^sub>E]) Q)" by auto
    then show "\<exists>t. [R]\<^sub>R # [Tock]\<^sub>E # aa \<lesssim>\<^sub>C t \<and>
           priMaxTT pa t
            ([insert Tick
               (S \<union> {e. e \<noteq> Tock \<and> sa @ [[e]\<^sub>E] \<notin> Q \<or> e = Tock \<and> sa @ [[S]\<^sub>R, [Tock]\<^sub>E] \<notin> Q})]\<^sub>R #
             [Tock]\<^sub>E # mkTTMP zz (sa @ [[S]\<^sub>R, [Tock]\<^sub>E]) Q)
            (mkTTMP sa [] Q) (unTT1 Q)"
    proof -
      obtain Z where Z:"Z = S \<union> {e. e \<noteq> Tock \<and> sa @ [[e]\<^sub>E] \<notin> Q \<or> e = Tock \<and> sa @ [[S]\<^sub>R, [Tock]\<^sub>E] \<notin> Q} \<union> {Tick}" by auto
      from R_subset Tock_not_in have "R \<subseteq> prirefTT1 pa S sa Q \<and> Tock \<notin> prirefTT1 pa S sa Q"
        by auto
      then have "R \<subseteq> prirefMaxTT pa Z \<and> Tock \<notin> prirefMaxTT pa Z"
        using prirefMaxTT_prirefTT1 ttWFx_healthy Z by blast
      then have "[R]\<^sub>R # [Tock]\<^sub>E # aa \<lesssim>\<^sub>C [prirefMaxTT pa Z]\<^sub>R # [Tock]\<^sub>E # t \<and> Tock \<notin> prirefMaxTT pa Z"
        using aa_prefix_t by auto
      then have "[R]\<^sub>R # [Tock]\<^sub>E # aa \<lesssim>\<^sub>C [prirefMaxTT pa Z]\<^sub>R # [Tock]\<^sub>E # t
            \<and> Tock \<notin> prirefMaxTT pa Z
            \<and> priMaxTT pa t Y (mkTTMP (sa @ [[S]\<^sub>R, [Tock]\<^sub>E]) [] Q) (unTT1 Q)"
        using Y priMaxTT_assm by auto
      then have "[R]\<^sub>R # [Tock]\<^sub>E # aa \<lesssim>\<^sub>C [prirefMaxTT pa Z]\<^sub>R # [Tock]\<^sub>E # t
            \<and> Tock \<notin> prirefMaxTT pa Z
            \<and> priMaxTT pa ([prirefMaxTT pa Z]\<^sub>R # [Tock]\<^sub>E # t) 
                           ([Z]\<^sub>R # [Tock]\<^sub>E # Y) (mkTTMP sa [] Q) (unTT1 Q)"
      proof -
        have "priMaxTT pa t Y (mkTTMP (sa @ [[S]\<^sub>R, [Tock]\<^sub>E]) [] Q) (unTT1 Q)"
             using \<open>[R]\<^sub>R # [Tock]\<^sub>E # aa \<lesssim>\<^sub>C [prirefMaxTT pa Z]\<^sub>R # [Tock]\<^sub>E # t \<and> Tock \<notin> prirefMaxTT pa Z \<and> priMaxTT pa t Y (mkTTMP (sa @ [[S]\<^sub>R, [Tock]\<^sub>E]) [] Q) (unTT1 Q)\<close> by blast
        then have "priMaxTT pa t Y ((mkTTMP sa [] Q) @ [[S \<union> {e. e \<noteq> Tock \<and> sa @ [[e]\<^sub>E] \<notin> Q \<or> e = Tock \<and> sa @ [[S]\<^sub>R, [Tock]\<^sub>E] \<notin> Q} \<union> {Tick}]\<^sub>R, [Tock]\<^sub>E]) (unTT1 Q)"
          (*using TT1_healthy TT2_healthy TT4w_healthy Y Z priMaxTT_start_Ref_extends sledgehammer by fastforce*)
          using mkTTMP_absorb_Ref_Tock'
          by (smt Collect_cong append_Nil)
        then have "priMaxTT pa t Y ((mkTTMP sa [] Q) @ [[Z]\<^sub>R, [Tock]\<^sub>E]) (unTT1 Q)"
          using Z by auto
        then have "priMaxTT pa ([prirefMaxTT pa Z]\<^sub>R # [Tock]\<^sub>E # t) ([Z]\<^sub>R # [Tock]\<^sub>E # Y) (mkTTMP sa [] Q) (unTT1 Q)"
          using \<open>[R]\<^sub>R # [Tock]\<^sub>E # aa \<lesssim>\<^sub>C [prirefMaxTT pa Z]\<^sub>R # [Tock]\<^sub>E # t \<and> Tock \<notin> prirefMaxTT pa Z \<and> priMaxTT pa t Y (mkTTMP (sa @ [[S]\<^sub>R, [Tock]\<^sub>E]) [] Q) (unTT1 Q)\<close> 
          by auto
        then show ?thesis
          using \<open>[R]\<^sub>R # [Tock]\<^sub>E # aa \<lesssim>\<^sub>C [prirefMaxTT pa Z]\<^sub>R # [Tock]\<^sub>E # t \<and> Tock \<notin> prirefMaxTT pa Z \<and> priMaxTT pa t Y (mkTTMP (sa @ [[S]\<^sub>R, [Tock]\<^sub>E]) [] Q) (unTT1 Q)\<close> 
          by auto
      qed
      then have "[R]\<^sub>R # [Tock]\<^sub>E # aa \<lesssim>\<^sub>C [prirefMaxTT pa Z]\<^sub>R # [Tock]\<^sub>E # t \<and>
        priMaxTT pa ([prirefMaxTT pa Z]\<^sub>R # [Tock]\<^sub>E # t)
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
    and ttWFx_healthy:  "ttWFx Q"
    and TT2_healthy: "TT2 Q"
    and TT1_healthy:  "TT1 Q"
    and priTT1:   "priTT1 pa aa zz (sa @ [[e\<^sub>2]\<^sub>E]) Q"
    and maximal:      "maximal(pa,e\<^sub>2)"
    and subsettt:    "aa \<lesssim>\<^sub>C t"
    and priMaxTT:    "priMaxTT pa t (mkTTMP zz (sa @ [[e\<^sub>2]\<^sub>E]) Q) (mkTTMP (sa @ [[e\<^sub>2]\<^sub>E]) [] Q) (unTT1 Q)"
    then show "\<exists>t. [e\<^sub>2]\<^sub>E # aa \<lesssim>\<^sub>C t \<and> priMaxTT pa t ([e\<^sub>2]\<^sub>E # mkTTMP zz (sa @ [[e\<^sub>2]\<^sub>E]) Q) (mkTTMP sa [] Q) (unTT1 Q)"
    proof -
      from subsettt have e2_aa_t:"[e\<^sub>2]\<^sub>E # aa \<lesssim>\<^sub>C [e\<^sub>2]\<^sub>E # t"
        by auto
      have "priMaxTT pa t (mkTTMP zz (sa @ [[e\<^sub>2]\<^sub>E]) Q) (mkTTMP (sa @ [[e\<^sub>2]\<^sub>E]) [] Q) (unTT1 Q)"
        using priMaxTT by auto
      then have "priMaxTT pa ([e\<^sub>2]\<^sub>E # t) ([e\<^sub>2]\<^sub>E # mkTTMP zz (sa @ [[e\<^sub>2]\<^sub>E]) Q) (mkTTMP sa [] Q) (unTT1 Q)"
        using mkTTMP_absorb_event maximal
        by (simp add: mkTTMP_dist_concat)
      then have "[e\<^sub>2]\<^sub>E # aa \<lesssim>\<^sub>C [e\<^sub>2]\<^sub>E # t \<and> priMaxTT pa ([e\<^sub>2]\<^sub>E # t) ([e\<^sub>2]\<^sub>E # mkTTMP zz (sa @ [[e\<^sub>2]\<^sub>E]) Q) (mkTTMP sa [] Q) (unTT1 Q)"
        using e2_aa_t by auto
      then have "\<exists>t. [e\<^sub>2]\<^sub>E # aa \<lesssim>\<^sub>C t \<and> priMaxTT pa t ([e\<^sub>2]\<^sub>E # mkTTMP zz (sa @ [[e\<^sub>2]\<^sub>E]) Q) (mkTTMP sa [] Q) (unTT1 Q)"
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
    and ttWFx_healthy:  "ttWFx Q"
    and TT2_healthy: "TT2 Q"
    and TT1_healthy:  "TT1 Q"
    and priTT1:   "priTT1 pa aa zz (sa @ [[e\<^sub>2]\<^sub>E]) Q"
    and sa_Z:         "sa @ [[Z]\<^sub>R] \<in> Q"
(*    and TTMPick_sa:   "TTMPick sa [] Q"*)
    and events_in_Z:  "\<forall>e. e \<notin> Z \<and> e \<noteq> Tock \<longrightarrow> sa @ [[e]\<^sub>E] \<in> Q"
    and Tick_in_Z:    "Tick \<in> Z"
    and e2_not_in_Z:  "e\<^sub>2 \<notin> Z"
    and no_pri_Z:     "\<forall>b. b \<in> Z \<or> \<not> e\<^sub>2 <\<^sup>*pa b"
    and not_priMaxTT:"\<forall>t. [e\<^sub>2]\<^sub>E # aa \<lesssim>\<^sub>C t \<longrightarrow> \<not> priMaxTT pa t ([e\<^sub>2]\<^sub>E # mkTTMP zz (sa @ [[e\<^sub>2]\<^sub>E]) Q) (mkTTMP sa [] Q) (unTT1 Q)"
    and Tock_in_Z:    "Tock \<in> Z"
    and subsettt:    "aa \<lesssim>\<^sub>C t"
    and priMaxTT:    "priMaxTT pa t (mkTTMP zz (sa @ [[e\<^sub>2]\<^sub>E]) Q) (mkTTMP (sa @ [[e\<^sub>2]\<^sub>E]) [] Q) (unTT1 Q)"
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
        by (meson TT1_def TT1_healthy TT2_healthy ttWFx_healthy TT4_healthy TTs_mkTTMP_in_P tt_prefix_subset_front tt_prefix_subset_refl)
      then have b:"(mkTTMP sa [] Q) @ [[Z]\<^sub>R] \<in> unTT1 Q \<and> e\<^sub>2 \<notin> Z \<and> \<not>(\<exists>b. b \<notin> Z \<and> e\<^sub>2 <\<^sup>*pa b)"
        using a TT1_healthy TT4w_healthy  
        by (simp add: priMaxTT_unTT1_case_specific TT2_healthy ttWFx_healthy TT4_healthy mkTTMP_in_P)
        (* FIXME: Key result to prove *)
      have "priMaxTT pa t (mkTTMP zz (sa @ [[e\<^sub>2]\<^sub>E]) Q) (mkTTMP (sa @ [[e\<^sub>2]\<^sub>E]) [] Q) (unTT1 Q)"
        using priMaxTT by auto
      then have "priMaxTT pa t (mkTTMP zz (sa @ [[e\<^sub>2]\<^sub>E]) Q) ((mkTTMP sa [] Q) @ [[e\<^sub>2]\<^sub>E]) (unTT1 Q)"
        by (simp add: mkTTMP_dist_concat)
      then have priMaxTT_pa_t:"priMaxTT pa ([e\<^sub>2]\<^sub>E # t) ([e\<^sub>2]\<^sub>E # mkTTMP zz (sa @ [[e\<^sub>2]\<^sub>E]) Q) (mkTTMP sa [] Q) (unTT1 Q)"
        using priMaxTT sa_Z e2_not_in_Z events_in_Z b by auto
      then have "[e\<^sub>2]\<^sub>E # aa \<lesssim>\<^sub>C [e\<^sub>2]\<^sub>E # t"
        using subsettt by auto
      then have not_priMaxTT_pa_t:"\<not> priMaxTT pa ([e\<^sub>2]\<^sub>E # t) ([e\<^sub>2]\<^sub>E # mkTTMP zz (sa @ [[e\<^sub>2]\<^sub>E]) Q) (mkTTMP sa [] Q) (unTT1 Q)"
        using not_priMaxTT by blast
      then show ?thesis
        using priMaxTT_pa_t not_priMaxTT_pa_t by auto
    qed
  next
    fix pa 
    fix aa zz::"'a ttobs list"
    fix e\<^sub>2 sa t Z
    fix Q::"'a ttobs list set"
    assume 
        TT4_healthy: "TT4 Q"
    and ttWFx_healthy:  "ttWFx Q"
    and TT2_healthy: "TT2 Q"
    and TT1_healthy:  "TT1 Q"
    and priTT1:   "priTT1 pa aa zz (sa @ [[e\<^sub>2]\<^sub>E]) Q"
    and sa_Z:         "sa @ [[Z]\<^sub>R] \<in> Q"
  (*  and TTMPick_sa:   "TTMPick sa [] Q"*)
    and e2_not_in_Z:   "e\<^sub>2 \<notin> Z"
    and nohigherpri:  "\<forall>b. b \<in> Z \<or> \<not> e\<^sub>2 <\<^sup>*pa b"
    and subsettt:    "aa \<lesssim>\<^sub>C t"
    and events_in_Z:  "\<forall>e. e \<notin> Z \<and> e \<noteq> Tock \<longrightarrow> sa @ [[e]\<^sub>E] \<in> Q"
    and Tick_in_Z:    "Tick \<in> Z"
    and Tock_Z_in_Q:  "sa @ [[Z]\<^sub>R, [Tock]\<^sub>E] \<in> Q"
    and priMaxTT:    "priMaxTT pa t (mkTTMP zz (sa @ [[e\<^sub>2]\<^sub>E]) Q) (mkTTMP (sa @ [[e\<^sub>2]\<^sub>E]) [] Q) (unTT1 Q)"
    then show "\<exists>t. [e\<^sub>2]\<^sub>E # aa \<lesssim>\<^sub>C t \<and> priMaxTT pa t ([e\<^sub>2]\<^sub>E # mkTTMP zz (sa @ [[e\<^sub>2]\<^sub>E]) Q) (mkTTMP sa [] Q) (unTT1 Q)"
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
        by (meson TT1_def TT1_healthy TT2_healthy ttWFx_healthy TT4_healthy TTs_mkTTMP_in_P tt_prefix_subset_front tt_prefix_subset_refl)
      then have b:"(mkTTMP sa [] Q) @ [[Z]\<^sub>R] \<in> unTT1 Q \<and> e\<^sub>2 \<notin> Z \<and> \<not>(\<exists>b. b \<notin> Z \<and> e\<^sub>2 <\<^sup>*pa b)"
        using a TT1_healthy TT4w_healthy  
        by (simp add: priMaxTT_unTT1_case_specific TT2_healthy ttWFx_healthy TT4_healthy mkTTMP_in_P)
      have "priMaxTT pa t (mkTTMP zz (sa @ [[e\<^sub>2]\<^sub>E]) Q) (mkTTMP (sa @ [[e\<^sub>2]\<^sub>E]) [] Q) (unTT1 Q)"
        using priMaxTT by auto
      then have "priMaxTT pa t (mkTTMP zz (sa @ [[e\<^sub>2]\<^sub>E]) Q) ((mkTTMP sa [] Q) @ [[e\<^sub>2]\<^sub>E]) (unTT1 Q)"
        by (simp add: mkTTMP_dist_concat)
      then have priMaxTT_pa_t:"priMaxTT pa ([e\<^sub>2]\<^sub>E # t) ([e\<^sub>2]\<^sub>E # mkTTMP zz (sa @ [[e\<^sub>2]\<^sub>E]) Q) (mkTTMP sa [] Q) (unTT1 Q)"
        using priMaxTT sa_Z e2_not_in_Z events_in_Z b by auto
      then have "[e\<^sub>2]\<^sub>E # aa \<lesssim>\<^sub>C [e\<^sub>2]\<^sub>E # t \<and> priMaxTT pa ([e\<^sub>2]\<^sub>E # t) ([e\<^sub>2]\<^sub>E # mkTTMP zz (sa @ [[e\<^sub>2]\<^sub>E]) Q) (mkTTMP sa [] Q) (unTT1 Q)"
        using subsettt by auto
      then show ?thesis by blast
    qed
  qed
  
  finally show ?thesis by auto
qed

lemma prirefMaxTT_imp_subseteq_prirefTT1:
  assumes "Z \<subseteq> prirefMaxTT pa S" "Tick \<in> S" "Tock \<in> S" "\<forall>e. e \<notin> S \<and> e \<noteq> Tock \<longrightarrow> sa @ [[e]\<^sub>E] \<in> Q" "ttWFx Q"
  shows "Z \<subseteq> prirefTT1 pa S sa Q"
proof -
  have "S = S \<union> {e. e \<noteq> Tock \<and> sa @ [[e]\<^sub>E] \<notin> Q \<or> e = Tock \<and> sa @ [[S]\<^sub>R, [Tock]\<^sub>E] \<notin> Q} \<union> {Tick}"
    using assms by auto
  then have "prirefMaxTT pa S = prirefTT1 pa S sa Q"
    using assms prirefMaxTT_prirefTT1 by (metis (mono_tags, lifting))
  then show ?thesis using assms by auto
qed

lemma prirefMaxTT_imp_subseteq_prirefTT1':
  assumes "Z \<subseteq> prirefMaxTT pa S" "Tick \<in> S" "sa @ [[S]\<^sub>R, [Tock]\<^sub>E] \<in> Q" "\<forall>e. e \<notin> S \<and> e \<noteq> Tock \<longrightarrow> sa @ [[e]\<^sub>E] \<in> Q" "ttWFx Q"
  shows "Z \<subseteq> prirefTT1 pa S sa Q"
proof -
  have "S = S \<union> {e. e \<noteq> Tock \<and> sa @ [[e]\<^sub>E] \<notin> Q \<or> e = Tock \<and> sa @ [[S]\<^sub>R, [Tock]\<^sub>E] \<notin> Q} \<union> {Tick}"
    using assms by auto
  then have "prirefMaxTT pa S = prirefTT1 pa S sa Q"
    using assms prirefMaxTT_prirefTT1 by (metis (mono_tags, lifting))
  then show ?thesis using assms by auto
qed

lemma prirefMaxTT_imp_eq_prirefTT1':
  assumes "Tick \<in> S" "sa @ [[S]\<^sub>R, [Tock]\<^sub>E] \<in> Q" "\<forall>e. e \<notin> S \<and> e \<noteq> Tock \<longrightarrow> sa @ [[e]\<^sub>E] \<in> Q" "ttWFx Q"
  shows "prirefMaxTT pa S = prirefTT1 pa S sa Q"
proof -
  have "S = S \<union> {e. e \<noteq> Tock \<and> sa @ [[e]\<^sub>E] \<notin> Q \<or> e = Tock \<and> sa @ [[S]\<^sub>R, [Tock]\<^sub>E] \<notin> Q} \<union> {Tick}"
    using assms by auto
  then have "prirefMaxTT pa S = prirefTT1 pa S sa Q"
    using assms prirefMaxTT_prirefTT1 by (metis (mono_tags, lifting))
  then show ?thesis using assms by auto
qed

lemma priMaxTT_imp_priTT1:
  assumes "x \<lesssim>\<^sub>C t" "TTMPick s i P" "priMaxTT p t s i (unTT1 P)" "TT4 P" "ttWFx P" "TT2 P" "TT1 P"
  shows "\<exists>z. priTT1 p x z i P \<and> z \<lesssim>\<^sub>C s"
  using assms 
proof (induct p t s i P arbitrary:x rule:priMaxTT.induct, auto)
  fix pa sa Q 
  fix xa::"'a ttobs list"
  assume "xa \<lesssim>\<^sub>C []"
  then show "\<exists>z. priTT1 pa xa z sa Q \<and> z \<lesssim>\<^sub>C []"
    apply (cases xa, auto)
    by (rule_tac x="[]" in exI, auto)
next
  fix pa S sa Q
  fix xa::"'a ttobs list"
  assume 
      prirefMaxTT:    "xa \<lesssim>\<^sub>C [[prirefMaxTT pa S]\<^sub>R]"
  and events_in_Q:  "\<forall>e. e \<notin> S \<and> e \<noteq> Tock \<longrightarrow> sa @ [[e]\<^sub>E] \<in> Q"
  and Tick_in_S:    "Tick \<in> S"
  and priTT1:   "\<forall>z. priTT1 pa xa z sa Q \<longrightarrow> \<not> z \<lesssim>\<^sub>C [[S]\<^sub>R]"
  and Tock_in_S:    "Tock \<in> S"
  and  TT4_healthy: "TT4 Q"
  and   ttWFx_healthy: "ttWFx Q"
  and  TT2_healthy: "TT2 Q"
  and   TT1_healthy: "TT1 Q"
  then show "False"
  proof(cases xa)
    case Nil
    then show ?thesis
      using tt_prefix_subset.simps(1) priTT1 priTT1.simps(1) by blast
  next
    case (Cons a list)
    then obtain Z where "a = [Z]\<^sub>R"
      using tt_prefix_subset.elims(2) prirefMaxTT by blast
    then have "[Z]\<^sub>R # list \<lesssim>\<^sub>C [[prirefMaxTT pa S]\<^sub>R]"
      using prirefMaxTT Cons by auto
    then have "list = []"
              "Z \<subseteq> prirefMaxTT pa S"
      using tt_prefix_subset.simps(1) tt_prefix_subset_antisym init_refusal_tt_prefix_subset apply blast
      using \<open>a = [Z]\<^sub>R\<close> local.Cons prirefMaxTT by auto
    then have "priTT1 pa [[Z]\<^sub>R] [[S]\<^sub>R] sa Q"
      apply auto
      by (meson ttWFx_healthy Tick_in_S Tock_in_S events_in_Q prirefMaxTT_imp_subseteq_prirefTT1 subset_iff)
    then have "\<not> [[S]\<^sub>R] \<lesssim>\<^sub>C [[S]\<^sub>R]"
      using priTT1 Cons \<open>a = [Z]\<^sub>R\<close> \<open>list = []\<close> by blast
    then show ?thesis by auto
  qed
next
  fix pa S sa Q
  fix xa::"'a ttobs list"
  assume 
      prirefMaxTT:     "xa \<lesssim>\<^sub>C [[prirefMaxTT pa S]\<^sub>R]"
  and events_in_Q:   "\<forall>e. e \<notin> S \<and> e \<noteq> Tock \<longrightarrow> sa @ [[e]\<^sub>E] \<in> Q"
  and Tick_in_S:     "Tick \<in> S"
  and Tock_in_Q:     "sa @ [[S]\<^sub>R, [Tock]\<^sub>E] \<in> Q"
  and  TT4_healthy: "TT4 Q"
  and   ttWFx_healthy: "ttWFx Q"
  and  TT2_healthy: "TT2 Q"
  and   TT1_healthy: "TT1 Q"
  then show "\<exists>z. priTT1 pa xa z sa Q \<and> z \<lesssim>\<^sub>C [[S]\<^sub>R]"
  proof(cases xa)
    case Nil
    then show ?thesis
      using tt_prefix_subset.simps(1) priTT1.simps(1) by blast
  next
    case (Cons a list)
    then obtain Z where "a = [Z]\<^sub>R"
      using tt_prefix_subset.elims(2) prirefMaxTT by blast
    then have "[Z]\<^sub>R # list \<lesssim>\<^sub>C [[prirefMaxTT pa S]\<^sub>R]"
      using prirefMaxTT Cons by auto
    then have "list = []"
              "Z \<subseteq> prirefMaxTT pa S"
      using tt_prefix_subset.simps(1) tt_prefix_subset_antisym init_refusal_tt_prefix_subset apply blast
      using \<open>a = [Z]\<^sub>R\<close> local.Cons prirefMaxTT by auto
    then have "priTT1 pa [[Z]\<^sub>R] [[S]\<^sub>R] sa Q"
      apply auto
      by (meson ttWFx_healthy Tick_in_S events_in_Q Tock_in_Q prirefMaxTT_imp_subseteq_prirefTT1' subset_iff)
    then have "priTT1 pa [[Z]\<^sub>R] [[S]\<^sub>R] sa Q \<and> [[S]\<^sub>R] \<lesssim>\<^sub>C [[S]\<^sub>R]"
      by auto
    then show ?thesis using Cons \<open>a = [Z]\<^sub>R\<close> \<open>list = []\<close> by blast
  qed
next
  fix pa aa S zz sa Q
  fix xa::"'a ttobs list"
  assume
      hyp:          "(\<And>x. x \<lesssim>\<^sub>C aa \<Longrightarrow> \<exists>z. priTT1 pa x z (sa @ [[S]\<^sub>R, [Tock]\<^sub>E]) Q \<and> z \<lesssim>\<^sub>C zz)"
  and xa_aa:        "xa \<lesssim>\<^sub>C [prirefMaxTT pa S]\<^sub>R # [Tock]\<^sub>E # aa"
  and TT4_healthy: "TT4 Q"
  and ttWFx_healthy:  "ttWFx Q"
  and TT2_healthy: "TT2 Q"
  and TT1_healthy:  "TT1 Q"
  and events_in_Q:  "\<forall>e. e \<notin> S \<and> e \<noteq> Tock \<longrightarrow> sa @ [[e]\<^sub>E] \<in> Q"
  and Tock_not_in_p:"Tock \<notin> prirefMaxTT pa S"
  and priMaxTT:    "priMaxTT pa aa zz (sa @ [[S]\<^sub>R, [Tock]\<^sub>E]) (unTT1 Q)"
  and Tick_in_S:    "Tick \<in> S" 
  and TTMPick_zz:   "TTMPick zz (sa @ [[S]\<^sub>R, [Tock]\<^sub>E]) Q" 
  and hyp_False:    "\<forall>z. priTT1 pa xa z sa Q \<longrightarrow> \<not> z \<lesssim>\<^sub>C [S]\<^sub>R # [Tock]\<^sub>E # zz" 
  and Tock_in_S:    "Tock \<in> S"
  then show "False"
  proof (cases xa)
    case Nil
    then show ?thesis
      using tt_prefix_subset.simps(1) hyp_False priTT1.simps(1) by blast
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
        then have "[[x2]\<^sub>R] \<lesssim>\<^sub>C [prirefMaxTT pa S]\<^sub>R # [Tock]\<^sub>E # aa"
          using Cons xa_aa by auto
        then have "priTT1 pa xa [[S]\<^sub>R] sa Q"
          by (simp add: xa ttWFx_healthy Tick_in_S Tock_in_S events_in_Q prirefMaxTT_imp_subseteq_prirefTT1)
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
        then have "[x2]\<^sub>R # [Tock]\<^sub>E # list' \<lesssim>\<^sub>C [prirefMaxTT pa S]\<^sub>R # [Tock]\<^sub>E # aa"
          using Cons xa_aa by auto
        then have "list' \<lesssim>\<^sub>C aa"
          by auto
        then have "\<exists>z. priTT1 pa list' z (sa @ [[S]\<^sub>R, [Tock]\<^sub>E]) Q \<and> z \<lesssim>\<^sub>C zz"
          using hyp by auto
        then have "priTT1 pa ([x2]\<^sub>R # [Tock]\<^sub>E # list') ([S]\<^sub>R # [Tock]\<^sub>E # aa) sa Q"
          using Tock_in_S Tock_not_in_p prirefMaxTT_def by auto
        then have "\<not> [S]\<^sub>R # [Tock]\<^sub>E # aa \<lesssim>\<^sub>C [S]\<^sub>R # [Tock]\<^sub>E # zz"
          using xa hyp_False by blast
        then show ?thesis
          using Tock_in_S Tock_not_in_p prirefMaxTT_def by auto
      qed
    qed
  qed
next
  fix pa aa S zz sa Q
  fix xa::"'a ttobs list"
  assume
      hyp:          "(\<And>x. x \<lesssim>\<^sub>C aa \<Longrightarrow> \<exists>z. priTT1 pa x z (sa @ [[S]\<^sub>R, [Tock]\<^sub>E]) Q \<and> z \<lesssim>\<^sub>C zz)"
  and xa_aa:        "xa \<lesssim>\<^sub>C [prirefMaxTT pa S]\<^sub>R # [Tock]\<^sub>E # aa"
  and TT4_healthy: "TT4 Q"
  and ttWFx_healthy:  "ttWFx Q"
  and TT2_healthy: "TT2 Q"
  and TT1_healthy:  "TT1 Q"
  and events_in_Q:  "\<forall>e. e \<notin> S \<and> e \<noteq> Tock \<longrightarrow> sa @ [[e]\<^sub>E] \<in> Q"
  and Tock_not_in_p:"Tock \<notin> prirefMaxTT pa S"
  and priMaxTT:    "priMaxTT pa aa zz (sa @ [[S]\<^sub>R, [Tock]\<^sub>E]) (unTT1 Q)"
  and Tick_in_S:    "Tick \<in> S" 
  and TTMPick_zz:   "TTMPick zz (sa @ [[S]\<^sub>R, [Tock]\<^sub>E]) Q" 
  and Tock_in_S:    "sa @ [[S]\<^sub>R, [Tock]\<^sub>E] \<in> Q"
  then show "\<exists>z. priTT1 pa xa z sa Q \<and> z \<lesssim>\<^sub>C [S]\<^sub>R # [Tock]\<^sub>E # zz"
  proof (cases xa)
    case Nil
    then show ?thesis
      using tt_prefix_subset.simps(1) priTT1.simps(1) by blast
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
        then have "[[x2]\<^sub>R] \<lesssim>\<^sub>C [prirefMaxTT pa S]\<^sub>R # [Tock]\<^sub>E # aa"
          using Cons xa_aa by auto
        then have "priTT1 pa xa [[S]\<^sub>R] sa Q"
          by (simp add: ttWFx_healthy Tick_in_S Tock_in_S events_in_Q prirefMaxTT_imp_subseteq_prirefTT1' xa)
        then show ?thesis by auto
      next
        case (Cons b list')
        then have "xa = [x2]\<^sub>R # b # list'"
          using a_list Cons Ref by auto
        then have xa:"xa = [x2]\<^sub>R # [Tock]\<^sub>E # list'"
          using xa_aa
          by (metis tt_prefix_subset.simps(3) tt_prefix_subset.simps(5) ttobs.exhaust init_refusal_tt_prefix_subset)
        then have list'_aa:"[x2]\<^sub>R # [Tock]\<^sub>E # list' \<lesssim>\<^sub>C [prirefMaxTT pa S]\<^sub>R # [Tock]\<^sub>E # aa"
          using Cons xa_aa by auto
        then have x2_subset:"x2 \<subseteq> prirefTT1 pa S sa Q"
          by (simp add: ttWFx_healthy Tick_in_S Tock_in_S events_in_Q prirefMaxTT_imp_subseteq_prirefTT1')
        then have Tock_not_in_prirefTT1:"Tock \<notin> prirefTT1 pa S sa Q"
          using Tock_not_in_p prirefMaxTT_imp_eq_prirefTT1' ttWFx_healthy Tick_in_S Tock_in_S events_in_Q by blast
        then have "list' \<lesssim>\<^sub>C aa"
          using list'_aa by auto
        then have "\<exists>z. priTT1 pa list' z (sa @ [[S]\<^sub>R, [Tock]\<^sub>E]) Q \<and> z \<lesssim>\<^sub>C zz"
          using hyp by auto
        then have "\<exists>z. priTT1 pa ([x2]\<^sub>R # [Tock]\<^sub>E # list') ([S]\<^sub>R # [Tock]\<^sub>E # z) sa Q \<and> ([S]\<^sub>R # [Tock]\<^sub>E # z) \<lesssim>\<^sub>C [S]\<^sub>R # [Tock]\<^sub>E # zz"
          using x2_subset Tock_not_in_p Tock_not_in_prirefTT1 by auto
        then show ?thesis using xa by blast
      qed
    qed
  qed
next
  fix pa aa e\<^sub>2 zz sa Q
  fix xa::"'a ttobs list"
  assume
      hyp:          "(\<And>x. x \<lesssim>\<^sub>C aa \<Longrightarrow> \<exists>z. priTT1 pa x z (sa @ [[e\<^sub>2]\<^sub>E]) Q \<and> z \<lesssim>\<^sub>C zz)"
  and xa_aa:        "xa \<lesssim>\<^sub>C [e\<^sub>2]\<^sub>E # aa"
  and TTMPick:      "TTMPick zz (sa @ [[e\<^sub>2]\<^sub>E]) Q"
  and TT4_healthy: "TT4 Q"
  and ttWFx_healthy:  "ttWFx Q"
  and TT2_healthy: "TT2 Q"
  and TT1_healthy:  "TT1 Q"
  and priMaxTT:    "priMaxTT pa aa zz (sa @ [[e\<^sub>2]\<^sub>E]) (unTT1 Q)"
  and maximal:      "maximal(pa,e\<^sub>2)"
  then show "\<exists>z. priTT1 pa xa z sa Q \<and> z \<lesssim>\<^sub>C [e\<^sub>2]\<^sub>E # zz"
  proof (cases xa)
    case Nil
    then show ?thesis
      using tt_prefix_subset.simps(1) priTT1.simps(1) by blast
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
        then have "\<exists>z. priTT1 pa list z (sa @ [[e\<^sub>2]\<^sub>E]) Q \<and> z \<lesssim>\<^sub>C zz"
           using hyp x1_list_subsettt by auto
        then have "\<exists>z. priTT1 pa ([e\<^sub>2]\<^sub>E # list) ([e\<^sub>2]\<^sub>E # z) sa Q \<and> [e\<^sub>2]\<^sub>E # z \<lesssim>\<^sub>C [e\<^sub>2]\<^sub>E # zz"
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
      hyp:          "(\<And>x. x \<lesssim>\<^sub>C aa \<Longrightarrow> \<exists>z. priTT1 pa x z (sa @ [[e\<^sub>2]\<^sub>E]) Q \<and> z \<lesssim>\<^sub>C zz)"
  and xa_aa:        "xa \<lesssim>\<^sub>C [e\<^sub>2]\<^sub>E # aa"
  and TTMPick:      "TTMPick zz (sa @ [[e\<^sub>2]\<^sub>E]) Q"
  and TT4_healthy: "TT4 Q"
  and ttWFx_healthy:  "ttWFx Q"
  and TT2_healthy: "TT2 Q"
  and TT1_healthy:  "TT1 Q"
  and priMaxTT:    "priMaxTT pa aa zz (sa @ [[e\<^sub>2]\<^sub>E]) (unTT1 Q)"
  and Z_in_Q:       "sa @ [[Z]\<^sub>R] \<in> unTT1 Q"
  and e2_not_in_Z:  "e\<^sub>2 \<notin> Z"
  and no_higher_pri:"\<forall>b. b \<in> Z \<or> \<not> e\<^sub>2 <\<^sup>*pa b"
  then show "\<exists>z. priTT1 pa xa z sa Q \<and> z \<lesssim>\<^sub>C [e\<^sub>2]\<^sub>E # zz"
  proof (cases xa)
    case Nil
    then show ?thesis using tt_prefix_subset.simps(1) priTT1.simps(1) by blast
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
        then have exists_priTT1:"\<exists>z. priTT1 pa list z (sa @ [[e\<^sub>2]\<^sub>E]) Q \<and> z \<lesssim>\<^sub>C zz"
          using hyp x1_list_subsettt by auto
        then have "\<exists>z. priTT1 pa ([e\<^sub>2]\<^sub>E # list) ([e\<^sub>2]\<^sub>E # z) sa Q \<and> [e\<^sub>2]\<^sub>E # z \<lesssim>\<^sub>C [e\<^sub>2]\<^sub>E # zz"
        proof -
          have TT4w_healthy:"TT4w Q"
            using TT1_healthy TT4_healthy 
            by (simp add: TT4_TT1_imp_TT4w)
          have "(sa @ [[Z]\<^sub>R] \<in> unTT1 Q \<and> e\<^sub>2 \<notin> Z \<and> \<not>(\<exists>b. b \<notin> Z \<and> e\<^sub>2 <\<^sup>*pa b))"
            using Z_in_Q e2_not_in_Z no_higher_pri by blast
          then have "(sa @ [[Z]\<^sub>R] \<in> Q \<and> TTMPick sa [] Q \<and> e\<^sub>2 \<notin> Z \<and> \<not>(\<exists>b. b \<notin> Z \<and> e\<^sub>2 <\<^sup>*pa b)
                      \<and> (\<forall>e. e \<notin> Z \<and> e \<noteq> Tock \<longrightarrow> sa @ [[e]\<^sub>E] \<in> Q)
                      \<and> (Tock \<notin> Z \<longrightarrow> sa @ [[Z]\<^sub>R,[Tock]\<^sub>E] \<in> Q) \<and> Tick \<in> Z)"
            using TT1_healthy TT4w_healthy priMaxTT_unTT1_case by blast
          then show ?thesis using exists_priTT1
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

definition PriTT1 :: "('e ttevent) partialorder \<Rightarrow> ('e ttobs) list set \<Rightarrow> ('e ttobs) list set" where
"PriTT1 p P = {\<rho>|\<rho> s. priTT1 p \<rho> s [] P \<and> s \<in> P}"

lemma mkTT1_PriMax_unTT1_priTT:
  assumes "TT1 P" "TT4w P" "TT4 P" "ttWFx P" "TT2 P"
  shows "mkTT1 (PriMax p (unTT1 P)) = PriTT1 p P"
proof -
  have "mkTT1 (PriMax p (unTT1 P)) = mkTT1 ({t|s t. s \<in> (unTT1 P) \<and> priMaxTT p t s [] (unTT1 P)})"
    unfolding PriMax_def by auto
  also have "... = ({\<rho>|\<rho> s t. \<rho> \<lesssim>\<^sub>C t \<and> s \<in> (unTT1 P) \<and> priMaxTT p t s [] (unTT1 P)})"
    by (auto simp add:mkTT1_simp)
  also have "... = ({\<rho>|\<rho> s t. \<rho> \<lesssim>\<^sub>C t 
                          \<and> s \<in> (\<Union>{x. TTM1 x \<and> TTM2 x \<and> TTM3 x \<and> TT1w x \<and> (mkTT1 x) \<subseteq> P}) 
                          \<and> priMaxTT p t s [] (unTT1 P)})"
    unfolding unTT1_def by auto
  also have "... = ({\<rho>|\<rho> s t. \<rho> \<lesssim>\<^sub>C t 
                          \<and> (\<exists>x. s \<in> x \<and> TTM1 x \<and> TTM2 x \<and> TTM3 x \<and> TT1w x \<and> (mkTT1 x) \<subseteq> P)
                          \<and> priMaxTT p t s [] (unTT1 P)})"
    by auto
  also have "... = ({\<rho>|\<rho> s t. \<rho> \<lesssim>\<^sub>C t 
                          \<and> s \<in> P \<and> TTM3 {s} \<and> TTMPick s [] P
                          \<and> priMaxTT p t s [] (unTT1 P)})"
    apply auto
    using assms TTM3_mkTT1_simp
    apply (metis (mono_tags, lifting))
    by (metis (mono_tags, lifting) TTM3_mkTT1_simp assms(1) assms(2))
  also have "... = ({\<rho>|\<rho> s t. \<rho> \<lesssim>\<^sub>C t 
                          \<and> s \<in> P \<and> TTMPick s [] P
                          \<and> priMaxTT p t s [] (unTT1 P)})"
    using TTM3_TTMPick by auto
  also have "... = ({\<rho>|\<rho> s. priTT1 p \<rho> s [] P \<and> s \<in> P})"
    using assms apply auto
     apply (meson TT1_def priMaxTT_imp_priTT1)
    using TTs_mkTTMP_in_P priTT1_TTMPick_imp_priMaxTT by fastforce
  finally show ?thesis unfolding PriTT1_def by auto
qed

lemma
  assumes "R \<subseteq> prirefMaxTT pa S" "Tick \<in> S"
  shows "R \<subseteq> prirefMaxTT pa (insert Tick S)"
  using assms 
  by (simp add: insert_absorb)

end