theory Failures_TickTock_Hiding

imports
  Failures_TickTock
begin
(*
lemma
  assumes "\<forall> P Q. (s2w (opS P Q)) = (opW (s2w P) (s2w Q))"
          "\<forall> P. s2w (w2s P) = P"
    shows "(w2s (opW P Q)) = (opS (w2s P) (w2s Q))"
proof -
  have "\<forall>P Q. (s2w (opS P Q)) = (opW (s2w P) (s2w Q))"
    using assms by auto
  then have "(s2w (opS (w2s P) (w2s Q))) = (opW (s2w (w2s P)) (s2w (w2s Q)))"
    by auto
  then have "(s2w (opS (w2s P) (w2s Q))) = (opW P Q)"
    using assms by auto
  then have "(w2s (s2w (opS (w2s P) (w2s Q)))) = (w2s (opW P Q))"
    by auto
  then have "(opS (w2s P) (w2s Q)) = (w2s (opW P Q))"
    using assms

  obtain p where p:"p = (w2s P)

  then have "\<forall> P Q. s2w (opS (w2s P) (w2s Q)) = (opW (s2w (w2s P)) (s2w (w2s Q)))"
    using *)

lemma Some_tt2F_tail:
  assumes "Some (a # s, b) = tt2F y"
  shows "Some (s,b) = tt2F (tl y)"
  using assms apply (induct y arbitrary:a b, auto)
  apply (case_tac aa, auto)
  apply (case_tac x1, auto)
  apply (metis (no_types, lifting) Pair_inject list.inject option.case_eq_if option.expand option.sel option.simps(3) prod.collapse)
  using Some_tt2F_imp_tt2T' by fastforce

lemma Some_no_tt2F_tick:
  assumes "Some (a # s, b) = tt2F y"
  shows "a \<noteq> tick"
  using assms apply (induct y arbitrary:s b, auto)
  apply (case_tac aa, auto)
   apply (case_tac x1, auto)
  apply (metis Some_tt2F_imp_tt2T' evt.distinct(1) list.sel(1) tt2F.simps(2) tt2T.simps(2))
    using Some_tt2F_imp_tt2T' by fastforce

lemma Some_tt2F_exists_filter:
  assumes "Some (s, b) = tt2F y"
  shows "\<exists>z. Some (filter (\<lambda>e. e \<notin> X) s, b) = tt2F z"
  using assms
proof (induct s arbitrary:b y X)
  case Nil
  then show ?case by auto
next
  case (Cons a s)
  then obtain z where z:"Some (filter (\<lambda>e. e \<notin> X) s, b) = tt2F z"
    using Some_tt2F_tail by blast
  then show ?case using Cons 
  proof (cases a)
    case tick
    then have "a \<noteq> tick"
      using Cons Some_no_tt2F_tick by blast
    then show ?thesis
      using tick by auto
  next
    case (evt x2)
    then show ?thesis
    proof (cases "evt x2 \<in> X")
      case True
      then show ?thesis 
        using Cons.hyps Cons.prems Some_tt2F_tail evt by fastforce
    next
      case False
      then have "filter (\<lambda>e. e \<notin> X) (a # s) = (a # filter (\<lambda>e. e \<notin> X) s)"
        using evt by auto
      then have "Some ((evt x2 # filter (\<lambda>e. e \<notin> X) s), b) = tt2F ([Event x2]\<^sub>E # z)"
        apply auto
        by (metis (no_types, lifting) fst_conv option.simps(5) snd_conv z)
      then show ?thesis 
        by (metis \<open>filter (\<lambda>e. e \<notin> X) (a # s) = a # filter (\<lambda>e. e \<notin> X) s\<close> evt)
    qed
  qed
qed

lemma Some_tt2T_exists_filter:
  assumes "Some (s, b) = tt2F y"
  shows "\<exists>z. tt2T z = filter (\<lambda>e. e \<notin> X) s \<and> z \<noteq> []"
  using assms
proof (induct s arbitrary:b y X)
  case Nil
  then show ?case 
    apply auto
    using tt2T.simps(5) by blast
next
  case (Cons a s)
  then obtain c z where cz:"Some (s, c) = tt2F z"
    using Cons
    apply (induct y, auto)
    using Some_tt2F_tail by blast
  then obtain z2 where z2:"tt2T z2 = filter (\<lambda>e. e \<notin> X) s"
    using Cons
    by blast
  then show ?case
  proof (cases a)
    case tick
    then have "a \<noteq> tick"
      using Cons Some_no_tt2F_tick by blast
    then show ?thesis
      using tick by auto
  next
    case (evt x2)
    then show ?thesis
      by (metis Cons.hyps \<open>\<And>thesis. (\<And>c z. Some (s, c) = tt2F z \<Longrightarrow> thesis) \<Longrightarrow> thesis\<close> filter.simps(2) list.distinct(1) tt2T.simps(2))
  qed
qed

lemma filter_empty_iff:
  "filter (\<lambda>e. e \<notin> HS) s = [] \<longleftrightarrow> (s = [] \<or> set s \<subseteq> HS)"
  apply auto
  by (auto simp add: filter_empty_conv)+

lemma Some_tt2F_event_tl:
  assumes "Some (s, X) = tt2F ([Event e]\<^sub>E # t)"
  shows "Some(tl s,X) = tt2F t"
  using assms apply (induct t arbitrary:e X, auto)
  by (metis (no_types, lifting) list.sel(3) option.case_eq_if option.distinct(1) option.expand option.sel prod.collapse prod.inject)

lemma tt2T_tl_evt:
  assumes "tt2T z = (evt e # xs)"
  shows "tt2T (tl z) = xs"
  using assms apply (induct z, auto)
  apply (case_tac a, auto)
  apply (case_tac x1, auto)
  using tt2T.elims by auto

lemma tt2T_hd_evt:
  assumes "tt2T z = (evt e # xs)"
  shows "hd z = [Event e]\<^sub>E"
  using assms apply (induct z, auto)
  apply (case_tac a, auto)
  apply (case_tac x1, auto)
  using tt2T.elims by auto

lemma Some_tt2F_concat_refusal:
  assumes "Some (s, X) = tt2F y"
  shows "\<exists>xs R. y = xs@[[R]\<^sub>R] \<and> tt2T xs = s \<and> X = {x. ttevt2F x \<in> R} \<and> [Tock]\<^sub>E \<notin> set xs \<and> ttWF(xs@[[R]\<^sub>R])"
  using assms
  proof (induct y arbitrary:s X rule:tt2F.induct)
    case (1 X)
    then show ?case by auto
  next
    case (2 e \<sigma>)
    then obtain t Z where s_R:"Some (t, Z) = tt2F \<sigma>"
      apply auto
      by (meson "2.prems" Some_tt2F_event_tl)
    then have "\<exists>xs R. \<sigma> = xs @ [[R]\<^sub>R] \<and> tt2T xs = t \<and> Z = {x. ttevt2F x \<in> R} \<and> [Tock]\<^sub>E \<notin> set xs \<and> ttWF(xs@[[R]\<^sub>R])"
      using 2 by auto
    then have "\<exists>xs R. [Event e]\<^sub>E # \<sigma> = [Event e]\<^sub>E # xs @ [[R]\<^sub>R] \<and> tt2T ([Event e]\<^sub>E # xs @ [[R]\<^sub>R]) = evt e # t \<and> Z = {x. ttevt2F x \<in> R} \<and> [Tock]\<^sub>E \<notin> set ([Event e]\<^sub>E # xs) \<and> ttWF ([Event e]\<^sub>E # xs @ [[R]\<^sub>R])"
      apply auto
      using ttWF_prefix_is_ttWF Some_tt2F_imp_tt2T' s_R by blast
    then show ?case
    proof -
      obtain tts :: "'a ttobs list" and TT :: "'a ttevent set" where
        f1: "[Event e]\<^sub>E # \<sigma> = [Event e]\<^sub>E # tts @ [[TT]\<^sub>R] \<and> tt2T ([Event e]\<^sub>E # tts @ [[TT]\<^sub>R]) = evt e # t \<and> Z = {e. ttevt2F e \<in> TT} \<and> [Tock]\<^sub>E \<notin> set ([Event e]\<^sub>E # tts) \<and> ttWF ([Event e]\<^sub>E # tts @ [[TT]\<^sub>R])"
        using \<open>\<exists>xs R. [Event e]\<^sub>E # \<sigma> = [Event e]\<^sub>E # xs @ [[R]\<^sub>R] \<and> tt2T ([Event e]\<^sub>E # xs @ [[R]\<^sub>R]) = evt e # t \<and> Z = {x. ttevt2F x \<in> R} \<and> [Tock]\<^sub>E \<notin> set ([Event e]\<^sub>E # xs) \<and> ttWF ([Event e]\<^sub>E # xs @ [[R]\<^sub>R])\<close> by blast
      have f2: "\<forall>es E ts. (Some (es, E) \<noteq> tt2F ts \<or> \<not> ttWF ts) \<or> (\<exists>tsa T. ts = tsa @ [[T]\<^sub>R] \<and> E = {e. ttevt2F (e::'a evt) \<in> T} \<and> tt2T tsa = es)"
        by (simp add: some_tt2F_ref_trace)
      obtain ttsa :: "'a ttobs list \<Rightarrow> 'a evt set \<Rightarrow> 'a evt list \<Rightarrow> 'a ttobs list" and TTa :: "'a ttobs list \<Rightarrow> 'a evt set \<Rightarrow> 'a evt list \<Rightarrow> 'a ttevent set" where
        "\<forall>x0 x1 x2. (\<exists>v3 v4. x0 = v3 @ [[v4]\<^sub>R] \<and> x1 = {uua. ttevt2F uua \<in> v4} \<and> tt2T v3 = x2) = (x0 = ttsa x0 x1 x2 @ [[TTa x0 x1 x2]\<^sub>R] \<and> x1 = {uua. ttevt2F uua \<in> TTa x0 x1 x2} \<and> tt2T (ttsa x0 x1 x2) = x2)"
        by moura
      then have f3: "[Event e]\<^sub>E # tts @ [[TT]\<^sub>R] = ttsa ([Event e]\<^sub>E # tts @ [[TT]\<^sub>R]) X s @ [[TTa ([Event e]\<^sub>E # tts @ [[TT]\<^sub>R]) X s]\<^sub>R] \<and> X = {ea. ttevt2F ea \<in> TTa ([Event e]\<^sub>E # tts @ [[TT]\<^sub>R]) X s} \<and> tt2T (ttsa ([Event e]\<^sub>E # tts @ [[TT]\<^sub>R]) X s) = s"
        using f2 f1 "2.prems" by presburger
      then have "[Tock]\<^sub>E \<notin> set (ttsa ([Event e]\<^sub>E # tts @ [[TT]\<^sub>R]) X s)"
        using f1 by simp
      then show ?thesis
        using f3 f1 by metis
    qed
  next
    case "3_1"
    then show ?case by auto
  next
    case ("3_2" va)
    then show ?case by auto
  next
    case ("3_3" va)
    then show ?case by auto
  next
    case ("3_4" vb vc)
    then show ?case by auto
  next
    case ("3_5" vb vc)
    then show ?case by auto
  next
    case ("3_6" va vb vc)
    then show ?case by auto
  qed

lemma
  assumes "Some (s, b) = tt2F (xs@[[X]\<^sub>R])"
  shows "s = tt2T xs \<and> b = {x. ttevt2F x \<in> X}"
  using assms
  using Some_tt2F_concat_refusal by force

lemma tt2F_Some_concat_Nil:
  assumes "[] = tt2T xs" "Some (s, b) = tt2F (xs@[[X]\<^sub>R])"
  shows "xs = []"
  using assms
  by (induct xs rule:ttWF.induct, auto)


lemma ttWF_Some_tt2F:
  assumes "ttWF (xs@[[X]\<^sub>R])" "[Tock]\<^sub>E \<notin> set xs"
  shows "Some (tt2T xs, {x. ttevt2F x \<in> X}) = tt2F (xs@[[X]\<^sub>R])"
  using assms
  apply (induct xs, auto)
  apply (case_tac a, auto)
    apply (case_tac x1, auto)
  apply (smt fst_conv option.simps(5) snd_conv)
   apply (metis list.exhaust_sel option.distinct(1) tt2F.simps(3) ttWF.simps(1) ttWF.simps(8))
  by (case_tac xsa, auto, case_tac a, auto, case_tac x1, auto)


lemma Some_tt2F_subset:
  assumes "Some (s, b \<union> HS) = tt2F y"
  shows "\<exists>z. Some (s, b) = tt2F z \<and> z \<lesssim>\<^sub>C y"
proof -
  obtain xs X where xs_X:"y = xs@[[X]\<^sub>R] \<and> b \<union> HS = {x. ttevt2F x \<in> X} \<and> [Tock]\<^sub>E \<notin> set xs \<and> ttWF(xs@[[X]\<^sub>R])"
    using Some_tt2F_concat_refusal assms by blast

  then have "ttevt2F`(b \<union> HS) \<subseteq> X"
    by auto

  then have "xs@[[ttevt2F`b]\<^sub>R] \<lesssim>\<^sub>C xs@[[X]\<^sub>R]"
    apply auto
    by (simp add: image_Un tt_prefix_common_concat)

  then have "Some (tt2T xs, b \<union> HS) = tt2F (xs@[[X]\<^sub>R])"
    apply auto
    using Some_tt2F_concat_refusal assms xs_X by blast

  have "ttWF (xs@[[ttevt2F`b]\<^sub>R])"
    using \<open>xs @ [[ttevt2F ` b]\<^sub>R] \<lesssim>\<^sub>C xs @ [[X]\<^sub>R]\<close> tt_prefix_subset_ttWF xs_X by blast

  have Tock_not_in_xs_b:"[Tock]\<^sub>E \<notin> set (xs@[[ttevt2F`b]\<^sub>R])"
    by (simp add: xs_X)

  have b_ttevt2F:"b = {x. ttevt2F x \<in> ttevt2F`b}"
    using Some_tt2F_set by fastforce

  then have "Some (tt2T xs, b) = tt2F (xs@[[ttevt2F`b]\<^sub>R])"
    using Tock_not_in_xs_b ttWF_Some_tt2F b_ttevt2F
    using \<open>ttWF (xs @ [[ttevt2F ` b]\<^sub>R])\<close> by fastforce

  then show ?thesis
    by (metis Pair_inject \<open>Some (tt2T xs, b \<union> HS) = tt2F (xs @ [[X]\<^sub>R])\<close> \<open>xs @ [[ttevt2F ` b]\<^sub>R] \<lesssim>\<^sub>C xs @ [[X]\<^sub>R]\<close> assms option.inject xs_X)
qed
  

lemma ttproc2F_HideF_failures_subseteq_HidingTT:
  assumes TTwf_P: "TTwf P" and TT0_P: "TT0 P" and TT1_P: "TT1 P" and TT2_P: "TT2 P" and TT3_P: "TT3 P"
      and TTwf_Q: "TTwf Q" and TT0_Q: "TT0 Q" and TT1_Q: "TT1 Q" and TT2_Q: "TT2 Q" and TT3_Q: "TT3 Q"
  shows "fst ((ttproc2F P) \<setminus>\<^sub>F HS) \<subseteq> fst (ttproc2F (P \<setminus>\<^sub>C (ttevt2F`HS)))" 
  using assms unfolding ttproc2F_def HidingTT_def HideF_def
proof (auto)
  fix b s y
  assume assm1:"Some (s, b \<union> HS) = tt2F y"
  and    assm2:"y \<in> P"

  text \<open> To proceed with the proof we need to remove HS, and keep b.
         This exists in P so long as P is TT1, because it is a subset refusal. \<close>

  then obtain z2 where z2:"Some (s, b) = tt2F z2 \<and> z2 \<in> P"
    using assm1 assm2 apply auto
    using Some_tt2F_subset TT1_P TT1_def by blast
  then have Some_z2:"Some (s, b) = tt2F z2"
    by auto

  text \<open> Then we can pick any z, where filtering the trace based on Some(s,b)
         is equivalent to getting a failure via tt2F. \<close>

  then obtain z where z:"tt2F z = Some (filter (\<lambda>e. e \<notin> HS) s, b)"
    using Some_tt2F_exists_filter assm1 z2
    by metis

  text \<open> Then it is sufficient to induce over the original hide_trace rule for the 
         following predicate that doesn't mention P at all. \<close>
                                            
  have "\<exists>z. z \<in> hide_trace (ttevt2F ` HS) y \<and> Some (filter (\<lambda>e. e \<notin> HS) s, b) = tt2F z"
    using assm1 z
  proof (induct "(ttevt2F `HS)" y arbitrary:b s z rule:hide_trace.induct)
    case 1
    then show ?case by auto
  next
    case (2 e xs) (* {t.  (Event e \<in> X \<and> t \<in> hide_trace X s) 
                        \<or> (\<exists>s'. Event e \<notin> X \<and> s' \<in> hide_trace X s \<and> t = [Event e]\<^sub>E # s')} *)
    have "Some (s, b \<union> HS) = tt2F ([Event e]\<^sub>E # xs)"
      using 2 by auto
    then have tt2F_xs:"Some(tl s,b \<union> HS) = tt2F xs"
      by (simp add: Some_tt2F_event_tl)
    then have tt2T_tl_s:"tt2T xs = tl s"
       using Some_tt2F_imp_tt2T' by blast

    have "s = tt2T ([Event e]\<^sub>E # xs)"
      using "2.prems"(1) Some_tt2F_imp_tt2T' by blast

    then have "tt2T z = filter (\<lambda>e. e \<notin> HS) (tt2T ([Event e]\<^sub>E # xs))"
      using 2
      by (simp add: Some_tt2F_imp_tt2T')
    then have tt2T_z:"tt2T z = filter (\<lambda>e. e \<notin> HS) (evt e # tt2T xs)"
      by auto
     
    then show ?case using 2 
      proof (cases "Event e \<in> (ttevt2F ` HS)")
        case True
        then have "evt e \<in> HS"
          apply auto
          by (metis evt.exhaust ttevent.distinct(3) ttevent.inject ttevt2F.simps(1) ttevt2F.simps(2))
        then have "tt2T z = filter (\<lambda>e. e \<notin> HS) (tt2T xs)"
          using tt2T_z by simp
        then have "tt2T z = filter (\<lambda>e. e \<notin> HS) (tl s)"
          using tt2T_tl_s by simp
        then have "\<exists>z. z \<in> hide_trace (ttevt2F ` HS) xs \<and> Some (filter (\<lambda>e. e \<notin> HS) s, b) = tt2F z"
          using 2 tt2F_xs 
          using \<open>s = tt2T ([Event e]\<^sub>E # xs)\<close> \<open>tt2T z = filter (\<lambda>e. e \<notin> HS) (tt2T ([Event e]\<^sub>E # xs))\<close> by auto
        then show ?thesis
          by (simp add: True)
      next
        case False
        then have "evt e \<notin> HS"
          using image_iff by fastforce
        then have "tt2T z = (evt e # (filter (\<lambda>e. e \<notin> HS) (tt2T xs)))"
          by (simp add: tt2T_z)
        then have "tt2T (tl z) = (filter (\<lambda>e. e \<notin> HS) (tt2T xs))" and
                  hd_z:"hd z = [Event e]\<^sub>E"
          apply (simp add: tt2T_tl_evt)
          by (simp add: \<open>tt2T z = evt e # filter (\<lambda>e. e \<notin> HS) (tt2T xs)\<close> tt2T_hd_evt)
        then have "\<exists>z. z \<in> hide_trace (ttevt2F ` HS) xs \<and> Some (filter (\<lambda>e. e \<notin> HS) (tl s), b) = tt2F z"
          using 2 tt2F_xs tt2T_tl_s
          by (smt Some_tt2F_tail \<open>s = tt2T ([Event e]\<^sub>E # xs)\<close> \<open>tt2T z = evt e # filter (\<lambda>e. e \<notin> HS) (tt2T xs)\<close> \<open>tt2T z = filter (\<lambda>e. e \<notin> HS) (tt2T ([Event e]\<^sub>E # xs))\<close>)
        then have "\<exists>z. [Event e]\<^sub>E # z \<in> hide_trace (ttevt2F ` HS) ([Event e]\<^sub>E # xs) \<and> Some (filter (\<lambda>e. e \<notin> HS) s, b) = tt2F ([Event e]\<^sub>E # z)"
          using hd_z apply auto
          using False
          by (metis (mono_tags, lifting) \<open>s = tt2T ([Event e]\<^sub>E # xs)\<close> \<open>tt2T z = evt e # filter (\<lambda>e. e \<notin> HS) (tt2T xs)\<close> \<open>tt2T z = filter (\<lambda>e. e \<notin> HS) (tt2T ([Event e]\<^sub>E # xs))\<close> eq_fst_iff eq_snd_iff option.simps(5) tt2T_tl_s)
        then have "\<exists>z. z \<in> hide_trace (ttevt2F ` HS) ([Event e]\<^sub>E # xs) \<and> Some (filter (\<lambda>e. e \<notin> HS) s, b) = tt2F z"
          by (metis \<open>tt2T z = evt e # filter (\<lambda>e. e \<notin> HS) (tt2T xs)\<close> hd_z list.distinct(1) list.exhaust_sel tt2T.simps(3))
        then show ?thesis 
          using hd_z by auto
      qed
  next
    case 3
    then show ?case by auto
  next
    case (4 Y s)
    then show ?case by auto
  next
    case (5 Y)
    then have "s = []"
      using Some_tt2F_imp_tt2T' tt2T.simps(5) by blast
    then obtain Z where Z:"z = [[Z]\<^sub>R] \<and> ttevt2F`b \<subseteq> Z"
      using 5 apply auto
      by (metis (no_types, lifting) image_Collect_subsetI old.prod.inject option.inject tt2F.simps(1) tt2F_some_exists)
  show ?case using 5
  proof (cases "(ttevt2F ` (b \<union> HS)) \<subseteq> Y")
      case True
      then show ?thesis using 5 Z
        apply auto
        by (rule_tac x="[[(ttevt2F`b)]\<^sub>R]" in exI, auto)
    next
      case False
      then show ?thesis using 5 Z  
        by auto
    qed
  next
    case (6 t)
    then show ?case by auto
  next
    case (7 Y e t)
    then show ?case by auto
  next
    case (8 Y t)
    then show ?case by auto
  next
    case (9 Y Z t)
    then show ?case by auto
  next
    case (10 x t)
    then show ?case by auto
  qed

  then have "\<exists>z. Some (filter (\<lambda>e. e \<notin> HS) s, b) = tt2F z \<and> (\<exists>x. x = hide_trace (ttevt2F ` HS) y \<and> y \<in> P \<and> z \<in> x)"
    using assm2 assm1 z
    by blast
  then show "\<exists>y. Some (filter (\<lambda>e. e \<notin> HS) s, b) = tt2F y \<and> (\<exists>x. (\<exists>p. x = hide_trace (ttevt2F ` HS) p \<and> p \<in> P) \<and> y \<in> x)"
    by auto
qed

lemma ttproc2F_HidingTT_failures_subseteq_HideF:
  assumes TTwf_P: "TTwf P" and TT0_P: "TT0 P" and TT1_P: "TT1 P" and TT2_P: "TT2 P" and TT3_P: "TT3 P"
      and TTwf_Q: "TTwf Q" and TT0_Q: "TT0 Q" and TT1_Q: "TT1 Q" and TT2_Q: "TT2 Q" and TT3_Q: "TT3 Q"
  shows "fst (ttproc2F (P \<setminus>\<^sub>C (ttevt2F`HS))) \<subseteq>  fst ((ttproc2F P) \<setminus>\<^sub>F HS)" 
  using assms unfolding ttproc2F_def HidingTT_def HideF_def
proof (auto)
  fix a b y p
  assume assm1:"Some (a, b) = tt2F y"
  and    assm2:"y \<in> hide_trace (ttevt2F ` HS) p"
  and    assm3:"p \<in> P"

  (* "\<exists>z. z \<in> hide_trace (ttevt2F ` HS) y \<and> Some (filter (\<lambda>e. e \<notin> HS) s, b) = tt2F z" *)

  

  have "\<exists>s. (Some (s, b \<union> HS) = tt2F p) \<and> a = filter (\<lambda>e. e \<notin> HS) s"
    using assm1 assm2
  proof (induct "(ttevt2F ` HS)" p arbitrary:y a b rule:hide_trace.induct)
    case (1 X)
    then show ?case by auto
  next
    case (2 X e s)
    then show ?case
    proof (cases "Event X \<in> (ttevt2F ` HS)")
      case True
      then have evt_X:"evt X \<in> HS"
        by (metis (no_types, hide_lams) evt.exhaust imageE ttevent.inject ttevent.simps(5) ttevt2F.simps(1) ttevt2F.simps(2))
      then have "s \<in> hide_trace (ttevt2F ` HS) e"
        using 2 True by auto
      then have "\<exists>s. Some (s, b \<union> HS) = tt2F e \<and> a = filter (\<lambda>e. e \<notin> HS) s"
        using 2 by auto
      then have "\<exists>s. Some (evt X # s, b \<union> HS) = tt2F ([Event X]\<^sub>E # e) \<and> a = filter (\<lambda>e. e \<notin> HS) (evt X # s)"
        using True evt_X apply auto
        by (metis (no_types, lifting) fst_conv option.simps(5) snd_conv)
      then show ?thesis by auto
    next
      case False
      then show ?thesis sorry
    qed
  next
    case (3 X)
    then show ?case by auto
  next
    case (4 X Y s)
    have "Tock \<notin> (ttevt2F ` HS)"
      apply auto
      by (metis evt.exhaust ttevent.distinct(1) ttevent.distinct(5) ttevt2F.simps(1) ttevt2F.simps(2))
    then have "tt2F s = None"
      using 4 by auto
    then show ?case
      using 4 by auto
  next
    case (5 X Y)
    then show ?case by auto
  next
    case (6 X t)
    then show ?case by auto
  next
    case (7 X Y e t)
    then show ?case by auto
  next
    case (8 X Y t)
    then show ?case by auto
  next
    case (9 X Y Z t)
    then show ?case by auto
  next
    case (10 X x t)
    then show ?case by auto
  qed

  then show "\<exists>s. (\<exists>y. Some (s, b \<union> HS) = tt2F y \<and> y \<in> P) \<and> a = filter (\<lambda>e. e \<notin> HS) s"
    using assm3 by blast
qed

end