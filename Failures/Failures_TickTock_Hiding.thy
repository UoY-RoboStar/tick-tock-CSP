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



lemma ttproc2F_HideF_failures_subseteq_HidingTT:
  assumes TTwf_P: "TTwf P" and TT0_P: "TT0 P" and TT1_P: "TT1 P" 
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
  assumes TTwf_P: "TTwf P" and TT0_P: "TT0 P" and TT1_P: "TT1 P"
  shows "fst (ttproc2F (P \<setminus>\<^sub>C (ttevt2F`HS))) \<subseteq> fst ((ttproc2F P) \<setminus>\<^sub>F HS)" 
  using assms unfolding ttproc2F_def HidingTT_def HideF_def
proof (auto)
  fix a b y p
  assume assm1:"Some (a, b) = tt2F y"
  and    assm2:"y \<in> hide_trace (ttevt2F ` HS) p"
  and    assm3:"p \<in> P"

  text \<open> Key to doing this proof without using p \<in> P is to use p
         and focus on showing that some prefix of it exists that
         satisfies the condition. \<close>
 
  have "\<exists>s. (\<exists>r. Some (s, b \<union> HS) = tt2F r \<and> r \<lesssim>\<^sub>C p) \<and> a = filter (\<lambda>e. e \<notin> HS) s"
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
      then have "\<exists>s. (\<exists>r.  Some (s, b \<union> HS) = tt2F r \<and> r \<lesssim>\<^sub>C e) \<and> a = filter (\<lambda>e. e \<notin> HS) s"
        using 2 by auto
      then have "\<exists>s. (\<exists>r. Some (evt X # s, b \<union> HS) = tt2F ([Event X]\<^sub>E # r) \<and> r \<lesssim>\<^sub>C e) \<and> a = filter (\<lambda>e. e \<notin> HS) (evt X # s)"
        using True evt_X apply auto
        by (metis (no_types, lifting) fst_conv option.simps(5) snd_conv)
      then show ?thesis 
        using tt_prefix_subset.simps(3) by blast
    next
      case False 
      then have "evt X \<notin> HS"
        using image_iff by fastforce
      then have tl_s:"(tl s) \<in> hide_trace (ttevt2F ` HS) e"
        using 2 False by auto

      then obtain ax where ax_bx:"Some (ax, b) = tt2F (tl s) \<and> evt X # ax = a"
        using "2.prems"(1) "2.prems"(2) False Some_tt2F_event_tl
        proof -
          assume a1: "\<And>ax. Some (ax, b) = tt2F (tl s) \<and> evt X # ax = a \<Longrightarrow> thesis"
          have "tt2T s = a"
            using "2.prems"(1) Some_tt2F_imp_tt2T' by blast
          then show ?thesis
            using a1 "2.prems"(1) "2.prems"(2) False Some_tt2F_event_tl by fastforce
        qed
      then have "\<exists>s. (\<exists>r. Some (s, b \<union> HS) = tt2F r \<and> r \<lesssim>\<^sub>C e) \<and> ax = filter (\<lambda>e. e \<notin> HS) s"
        using 2 tl_s by auto
      then have "\<exists>s. (\<exists>r. Some (s, b \<union> HS) = tt2F ([Event X]\<^sub>E # r) \<and> r \<lesssim>\<^sub>C e) \<and> (evt X # ax) = filter (\<lambda>e. e \<notin> HS) s"
        using 2 False
        by (smt \<open>evt X \<notin> HS\<close> filter.simps(2) fst_conv option.simps(5) snd_conv tt2F.simps(2))
      then show ?thesis using ax_bx
        using tt_prefix_subset.simps(3) by blast
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
    then have "a = []"
      using 5 by auto
    then obtain Z where Z:"Y = [[Z]\<^sub>R] \<and> ttevt2F`(b) \<subseteq> Z" (* {t. \<exists> Z\<subseteq>Y. X \<subseteq> Y \<and> t = [[Z]\<^sub>R]} *)
      using 5 apply simp
      apply safe 
      by auto
    then show ?case using 5
    proof (cases "(ttevt2F ` HS) \<subseteq> X")
      case True
      have "(ttevt2F ` (b \<union> HS)) \<subseteq> X"
        using 5 Z by auto
      have "Some (a, b) = tt2F [[Z]\<^sub>R] \<and> a = filter (\<lambda>e. e \<notin> HS) a"
        using 5 Z by auto
      then have "Some (a, (b \<union> HS)) = tt2F [[Z \<union> ttevt2F`HS]\<^sub>R] \<and> a = filter (\<lambda>e. e \<notin> HS) a"
       using 5 Z apply auto
       using Some_tt2F_set by fastforce
      then show ?thesis using 5 Z
        apply auto
        by (metis (no_types, lifting) \<open>Some (a, b \<union> HS) = tt2F [[Z \<union> ttevt2F ` HS]\<^sub>R] \<and> a = filter (\<lambda>e. e \<notin> HS) a\<close> sup.absorb_iff2 sup_assoc tt_prefix_subset.simps(2) tt_prefix_subset_refl)
    next
      case False
      then show ?thesis using 5 by auto
    qed  
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
    using assm3 TT1_P TT1_def by blast
qed

lemma ttproc2F_HideF_traces_subseteq_HidingTT:
  assumes TTwf_P: "TTwf P" and TT0_P: "TT0 P" and TT1_P: "TT1 P"
  shows "snd ((ttproc2F P) \<setminus>\<^sub>F HS) \<subseteq> snd (ttproc2F (P \<setminus>\<^sub>C (ttevt2F`HS)))" 
  using assms unfolding ttproc2F_def HidingTT_def HideF_def
proof(auto)
  fix y
  assume assm1:"y \<in> P"

  have "ttWF y"
    using TTwf_P TTwf_def assm1 by blast

  then have "\<exists>z r. filter (\<lambda>e. e \<notin> HS) (tt2T y) = tt2T z \<and> z \<in> hide_trace (ttevt2F ` HS) r \<and> r \<lesssim>\<^sub>C y"
  proof (induct "(ttevt2F `HS)" y rule:hide_trace.induct)
    case 1
    then show ?case   
      by (rule_tac x="[]" in exI, auto)+
  next
    case (2 e s)
    then have hyp:"\<exists>z r. filter (\<lambda>e. e \<notin> HS) (tt2T s) = tt2T z \<and> z \<in> hide_trace (ttevt2F ` HS) r \<and> r \<lesssim>\<^sub>C s"
      by auto
      
    then show ?case
    proof (cases "Event e \<in> (ttevt2F ` HS)")
      case True
      then have "\<exists>z r. filter (\<lambda>e. e \<notin> HS) (tt2T s) = tt2T z \<and> z \<in> hide_trace (ttevt2F ` HS) ([Event e]\<^sub>E # r) \<and> [Event e]\<^sub>E # r \<lesssim>\<^sub>C [Event e]\<^sub>E # s"
        using hyp by auto
      then have "\<exists>z r. filter (\<lambda>e. e \<notin> HS) (tt2T ([Event e]\<^sub>E # s)) = tt2T z \<and> z \<in> hide_trace (ttevt2F ` HS) ([Event e]\<^sub>E # r) \<and> [Event e]\<^sub>E # r \<lesssim>\<^sub>C [Event e]\<^sub>E # s"
        using True
        by (smt evt.exhaust filter.simps(2) imageE tt2T.simps(2) ttevent.distinct(3) ttevt2F.simps(1) ttevt2F.simps(2))
      then show ?thesis using 2 by blast
    next
      case False
      then have "\<exists>z r. filter (\<lambda>e. e \<notin> HS) (tt2T ([Event e]\<^sub>E # s)) = tt2T ([Event e]\<^sub>E # z) \<and> ([Event e]\<^sub>E # z) \<in> hide_trace (ttevt2F ` HS) ([Event e]\<^sub>E # r) \<and> [Event e]\<^sub>E # r \<lesssim>\<^sub>C [Event e]\<^sub>E # s"
        using hyp apply auto
        by (simp add: rev_image_eqI)
      then show ?thesis by blast
    qed
  next
    case 3
    then show ?case
      apply auto
      apply (smt evt.exhaust hide_trace.simps(3) image_iff mem_Collect_eq tt2T.simps(1) tt_prefix_subset_refl ttevent.distinct(3) ttevt2F.simps(1))
      by (metis filter.simps(1) hide_trace.simps(1) lists.Nil lists_empty tt2T.simps(3) tt_prefix_subset.simps(1))
    
  next
    case (4 Y s)
    then show ?case
    proof (cases "Tock \<in> (ttevt2F ` HS)")
      case True
      then show ?thesis
        by (metis evt.exhaust image_iff ttevent.distinct(1) ttevent.distinct(5) ttevt2F.simps(1) ttevt2F.simps(2))
    next
      case False
      then show ?thesis 
        using 4 False apply auto
        apply (rule_tac x="[]" in exI, simp)
        by (rule_tac x="[]" in exI, simp)
    qed
    
  next
    case (5 Y)
    then show ?case
      by (rule_tac x="[]" in exI, simp)+
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

  then show "\<exists>ya. filter (\<lambda>e. e \<notin> HS) (tt2T y) = tt2T ya \<and> (\<exists>x. (\<exists>p. x = hide_trace (ttevt2F ` HS) p \<and> p \<in> P) \<and> ya \<in> x)"
    using assm1  
    using TT1_P TT1_def by blast
qed   

lemma ttproc2F_HidingTT_traces_subseteq_HideF:
  assumes TTwf_P: "TTwf P" and TT0_P: "TT0 P" and TT1_P: "TT1 P"
  shows "snd (ttproc2F (P \<setminus>\<^sub>C (ttevt2F`HS))) \<subseteq> snd ((ttproc2F P) \<setminus>\<^sub>F HS)" 
  using assms unfolding ttproc2F_def HidingTT_def HideF_def
proof (auto)
  fix y p
  assume assm1:"y \<in> hide_trace (ttevt2F ` HS) p"
    and  assm2:"p \<in> P"

  have "\<exists>r. tt2T y = filter (\<lambda>e. e \<notin> HS) (tt2T r) \<and> r \<lesssim>\<^sub>C p"
    using assm1
  proof (induct "(ttevt2F ` HS)" p arbitrary:y rule:hide_trace.induct)
    case 1
    then show ?case
      apply auto
      by (rule_tac x="[]" in exI, auto)+
  next
    case (2 e s)
    then show ?case
    proof (cases "Event e \<in> (ttevt2F ` HS)")
      case True
      then have evt_HS:"evt e \<in> HS"
        by (metis (no_types, hide_lams) evt.exhaust imageE ttevent.inject ttevent.simps(5) ttevt2F.simps(1) ttevt2F.simps(2))
      then have "y \<in> hide_trace (ttevt2F ` HS) s"
        using 2 True by auto
 
      then have "\<exists>r. tt2T y = filter (\<lambda>e. e \<notin> HS) (tt2T r) \<and> r \<lesssim>\<^sub>C s"
        using 2 by auto
      then have "\<exists>r. tt2T y = filter (\<lambda>e. e \<notin> HS) (tt2T ([Event e]\<^sub>E # r)) \<and> ([Event e]\<^sub>E # r) \<lesssim>\<^sub>C [Event e]\<^sub>E # s"
        by (simp add: evt_HS)
      then show ?thesis by blast
    next
      case False
      then have evt_no_HS:"evt e \<notin> HS"
        using image_iff by fastforce
      then have tl_s:"(tl y) \<in> hide_trace (ttevt2F ` HS) s"
        using 2 False by auto
      then have "\<exists>r. tt2T (tl y) = filter (\<lambda>e. e \<notin> HS) (tt2T r) \<and> r \<lesssim>\<^sub>C s"
        using 2 by auto
      then have "\<exists>r. tt2T ([Event e]\<^sub>E # (tl y)) = filter (\<lambda>e. e \<notin> HS) (tt2T ([Event e]\<^sub>E # r)) \<and> ([Event e]\<^sub>E # r) \<lesssim>\<^sub>C ([Event e]\<^sub>E # s)"
        by (simp add: evt_no_HS)
      then show ?thesis
      proof -
        have "y = [Event e]\<^sub>E # tl y"
          using "2.prems" False by auto
        then show ?thesis
          by (metis (full_types) \<open>\<exists>r. tt2T ([Event e]\<^sub>E # tl y) = filter (\<lambda>e. e \<notin> HS) (tt2T ([Event e]\<^sub>E # r)) \<and> [Event e]\<^sub>E # r \<lesssim>\<^sub>C [Event e]\<^sub>E # s\<close>)
      qed
    qed
  next
    case 3
    then show ?case
      by (smt filter.simps(1) filter.simps(2) hide_trace.simps(3) image_eqI mem_Collect_eq tt2T.simps(1) tt2T.simps(3) tt_prefix_subset.simps(1) tt_prefix_subset_refl ttevt2F.simps(2))
  next
    case (4 Y s)
    then show ?case
      apply auto
       apply (metis evt.exhaust ttevent.distinct(1) ttevent.distinct(5) ttevt2F.simps(1) ttevt2F.simps(2))
      by (rule_tac x="[]" in exI, auto)
  next
    case (5 Y)
    then show ?case
      apply auto
      by (rule_tac x="[]" in exI, auto)
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

  then show "\<exists>z. tt2T y = filter (\<lambda>e. e \<notin> HS) z \<and> (\<exists>y. z = tt2T y \<and> y \<in> P)"
    using TT1_P TT1_def assm2 by blast
qed

lemma ttproc2F_HidingTT_eq_HideF:
  assumes TTwf_P: "TTwf P" and TT0_P: "TT0 P" and TT1_P: "TT1 P"
  shows "ttproc2F (P \<setminus>\<^sub>C (ttevt2F`HS)) = (ttproc2F P) \<setminus>\<^sub>F HS" 
  by (metis (no_types, lifting) HideF_def TT0_P TT1_P TTwf_P fst_conv snd_conv subset_antisym ttproc2F_HideF_failures_subseteq_HidingTT ttproc2F_HideF_traces_subseteq_HidingTT ttproc2F_HidingTT_failures_subseteq_HideF ttproc2F_HidingTT_traces_subseteq_HideF ttproc2F_def)

end