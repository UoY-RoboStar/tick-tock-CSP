theory
  CTockTick_FL_Priority_devel
imports
  CTockTick_FL_Priority
begin

fun flt2goodAcceptance :: "('e cttevent) fltrace \<Rightarrow> ('e cttevent) partialorder \<Rightarrow> bool" where
"flt2goodAcceptance \<langle>A\<rangle>\<^sub>\<F>\<^sub>\<L> p = True" |
"flt2goodAcceptance (A #\<^sub>\<F>\<^sub>\<L> fl) p = (if acceptance(A) \<noteq> \<bullet> \<and> \<not>(\<exists>b. b \<in>\<^sub>\<F>\<^sub>\<L> acceptance(A) \<and> event(A) <\<^sup>*p b) then (flt2goodAcceptance fl p) else
                            (if event(A) = Tock \<or> (event(A) \<noteq> Tick \<and> \<not>maximal(p,event(A))) then False else (flt2goodAcceptance fl p)))" 

lemma flt2goodAcceptance_imp_flt2goodTock:
  assumes "flt2goodAcceptance xs p"
  shows "flt2goodTock xs"
  using assms apply(induct xs, auto)
    apply (case_tac x1a, auto, case_tac a, auto)
  apply meson
   apply (case_tac x1a, auto, case_tac b, auto, case_tac a, auto, meson)
  apply (case_tac a, auto, meson)
  by presburger

primrec lasty :: "'a list \<Rightarrow> 'a list" where
"lasty [] = []" |
"lasty (x # xs) = (if xs = [] then [x] else lasty xs)"

lemma lasty_concat: 
  "lasty (xs @ [x]) = [x]"
  by (induct xs, auto)

lemma prirelRef_imp_butlast_of_prirelRefs:
  assumes "prirelRef p ar xs [] P"
  shows "prirelRef p (List.butlast ar) (List.butlast xs) [] P"
  using assms apply (induct p ar xs _ P rule:prirelRef.induct, auto)  
  apply (metis neq_Nil_conv prirelRef.simps(46))
      apply (metis neq_Nil_conv prirelRef.simps(28))
     apply (metis neq_Nil_conv prirelRef.simps(46))
    apply (metis neq_Nil_conv prirelRef.simps(28))
   apply (metis neq_Nil_conv prirelRef.simps(46))
  by (metis neq_Nil_conv prirelRef.simps(28))

lemma prirelRef_imp_one_butlast_of_prirelRef:
  assumes "prirelRef p ar (xs @ [x]) [] P"
  shows "prirelRef p (List.butlast ar) xs [] P"
  using assms prirelRef_imp_butlast_of_prirelRefs
  by fastforce

(*
lemma
  assumes "(s @ [[Z]\<^sub>R] \<in> Q \<and> (\<forall>b. (e\<^sub>2 <\<^sup>*p b) \<longrightarrow> b \<in> Z))"
  shows "e\<^sub>2 \<notin> Z"
  using assms nitpick*)

lemma FLTick0_Tick_Event:
  assumes "S = \<bullet> \<or> ((Event ev) \<in>\<^sub>\<F>\<^sub>\<L> S \<and> Tick \<notin>\<^sub>\<F>\<^sub>\<L> S)"
  shows "FLTick0 Tick {z. z \<le> \<langle>(S,Event ev)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>}"
  using assms unfolding FLTick0_def apply auto
   apply (case_tac x, auto)
       apply (case_tac x1, auto)
  apply (simp_all add: less_eq_aevent_def)
    apply (case_tac x21, auto, case_tac x22, auto, case_tac x1, auto, case_tac a, auto)
   apply (case_tac x22, auto, case_tac x1, auto)
  apply (case_tac x, auto)
       apply (case_tac x1, auto)
      apply (simp_all add: less_eq_aevent_def)
  apply (metis (full_types) amember.elims(2) amember.simps(2) less_eq_acceptance.simps(3))
   apply (metis amember.elims(2) cttevent.distinct(3) less_eq_acceptance.simps(3) singleton_iff)
  apply (case_tac x21, auto, case_tac x22, auto, case_tac x1, auto)
  by (case_tac x22, auto, case_tac x1, auto)

lemma fl_le_CT1c_ES_Event:
  assumes "fl \<le> \<langle>([{x. x \<notin> ES}]\<^sub>\<F>\<^sub>\<L>,Event ev)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>" "[[Event ev]\<^sub>E] \<in> P" "[[ES]\<^sub>R] \<in> P" "Event ev \<notin> ES" "CT1c P"
  shows "flt2cttobs fl \<in> P"
  using assms apply (cases fl, auto)
  apply (simp_all add: less_eq_aevent_def)
    apply (case_tac x1, auto)
  apply (metis (no_types, lifting) Collect_cong Collect_mem_eq mem_Collect_eq)
   apply (case_tac x21, auto, case_tac x22, auto, case_tac x1, auto)
  by (case_tac x22, auto, case_tac x1, auto)

lemma
  assumes "ys @ [[r1]\<^sub>R] = flt2cttobs fl" "flt2goodAcceptance fl p" "e \<notin> r1" "ys \<noteq> []"
  shows "\<not>(\<exists>b. b \<notin> r1 \<and> e <\<^sup>*p b)"
  using assms nitpick apply (induct fl p arbitrary:ys e r1 rule:flt2goodAcceptance.induct, auto)
   apply (case_tac A, auto)
  oops

lemma prirelref_imp_not_exists_higher_pri:
  assumes "(R = prirelref p S)" "e\<^sub>2 \<notin> R"
  shows "\<not>(\<exists>b. b \<notin> S \<and> e\<^sub>2 <\<^sup>*p b)"
  using assms unfolding prirelref_def by auto

lemma rev_induct_both:
  assumes "List.length xs = List.length ys"
          "P [] []"
          "(\<And>x y xs ys. P xs ys \<Longrightarrow> List.length xs = List.length ys \<Longrightarrow> P (xs @ [x]) (ys @ [y]))"
        shows "P xs ys"
proof -
  have revs:"P xs ys = P (List.rev (List.rev xs)) (List.rev (List.rev ys))"
    by auto
  
  have "P (List.rev (List.rev xs)) (List.rev (List.rev ys))"
    apply(rule_tac xs = "List.rev xs" and ys = "List.rev ys" in list_induct2, simp_all)
    using assms by auto
  then show ?thesis using revs by blast
qed

lemma prirelRef_both_cons_extend_refusal_imp_prefix:
  assumes "prirelRef p (x @ [[xs]\<^sub>R]) (y @ [[ys]\<^sub>R]) zs P" 
  shows "prirelRef p x y zs P"
  using assms apply (induct p x y zs P arbitrary:xs ys rule:prirelRef.induct, auto)
  apply (metis list.exhaust prirelRef.simps(57) snoc_eq_iff_butlast)
  by (metis list.exhaust prirelRef.simps(68) snoc_eq_iff_butlast)

lemma prirelRef_cannot_extend_refusal_rhs:
  assumes "prirelRef p x y zs P"
  shows "\<not> prirelRef p x (y @ [[ys]\<^sub>R]) zs P"
  using assms by (induct p x y zs P rule:prirelRef.induct, auto)

lemma prirelRef_cannot_extend_refusal_lhs:
  assumes "prirelRef p x y zs P"
  shows "\<not> prirelRef p (x @ [[xs]\<^sub>R]) y zs P"
  using assms by (induct p x y zs P rule:prirelRef.induct, auto)

lemma prirelRef_extend_cons_flt2cttobs_both:
  assumes "prirelRef p (flt2cttobs (xs &\<^sub>\<F>\<^sub>\<L> \<langle>x\<rangle>\<^sub>\<F>\<^sub>\<L>)) (flt2cttobs (ys &\<^sub>\<F>\<^sub>\<L> \<langle>y\<rangle>\<^sub>\<F>\<^sub>\<L>)) s P" "last xs = \<bullet>" "last ys = \<bullet>"
  shows "prirelRef p (flt2cttobs xs) (flt2cttobs ys) s P"
  (* FIXME: There must be a nicer proof. *)
  using assms apply (induct p xs ys arbitrary:x y s rule:prirel.induct, auto)
         apply (smt prirelRef.simps(29) prirelRef.simps(46) prirelRef.simps(68))
        apply (smt prirelRef.simps(29) prirelRef.simps(46))
       apply (smt prirelRef.simps(28) prirelRef.simps(57) prirelRef.simps(6))
      apply (smt prirelRef.simps(28) prirelRef.simps(47))
     apply (smt prirelRef.simps(29))
    apply (smt prirelRef.simps(28) prirelRef.simps(29))
   apply (smt prirelRef.simps(46))
  by (smt prirelRef.simps(46))

lemma prirelRef_extend_cons_acceptance_flt2cttobs_both:
  assumes "prirelRef p (flt2cttobs (xs &\<^sub>\<F>\<^sub>\<L> \<langle>x,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>)) (flt2cttobs (ys &\<^sub>\<F>\<^sub>\<L> \<langle>y,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>)) s P" "last xs = \<bullet>" "last ys = \<bullet>"
          "length xs = length ys"
  shows "prirelRef p (flt2cttobs xs) (flt2cttobs ys) s P"
  (* FIXME: There must be a nicer proof. *)
  using assms apply (induct p xs ys arbitrary:x y s rule:prirel.induct, auto)
     apply (smt prirelRef.simps(29))
    apply (smt prirelRef.simps(18) prirelRef.simps(19))
   apply (smt prirelRef.simps(46))
  by (smt prirelRef.simps(46))

lemma not_prirelRef_concat_refTock:
  assumes "v \<noteq> []"
  shows "\<not> prirelRef p (v @ [[x]\<^sub>R, [Tock]\<^sub>E]) [[y]\<^sub>R, [Tock]\<^sub>E] z P"
  using assms apply (induct p v "[]:: 'a cttobs list" z P rule:prirelRef.induct, auto)
  apply (case_tac va, auto, case_tac vb, auto, case_tac x1, auto)
   apply (metis append_Cons append_Nil neq_Nil_conv prirelRef.simps(28))
  apply (case_tac va, auto, case_tac va, auto, case_tac a, auto, case_tac x1, auto)
  by (metis append_Cons append_Nil neq_Nil_conv prirelRef.simps(28))

lemma not_prirelRef_concat_refTock':
  assumes "v \<noteq> []"
  shows "\<not> prirelRef p [[y]\<^sub>R, [Tock]\<^sub>E] (v @ [[x]\<^sub>R, [Tock]\<^sub>E]) z P"
  using assms apply (induct p "[]:: 'a cttobs list" v z P rule:prirelRef.induct, auto)
   apply (case_tac va, auto, case_tac va, auto, case_tac a, auto, case_tac x1, auto)
   apply (metis append_Cons neq_Nil_conv prirelRef.simps(46) self_append_conv2)
  apply (case_tac va, auto, case_tac vb, auto, case_tac x1, auto)
  by (metis append_Cons neq_Nil_conv prirelRef.simps(46) self_append_conv2)

lemma prirelRef_both_concat_refTock_imp_prefixes:
  assumes "prirelRef p (xs @ [[s]\<^sub>R, [Tock]\<^sub>E]) (ys @ [[t]\<^sub>R, [Tock]\<^sub>E]) z P" 
  shows "prirelRef p xs ys z P"
  using assms apply (induct p xs ys z P arbitrary:s t rule:prirelRef.induct, auto)
  using not_prirelRef_concat_refTock 
     apply (metis append_Cons list.discI)     
  using not_prirelRef_concat_refTock 
    apply fastforce
  using not_prirelRef_concat_refTock'
  by (metis append_Cons list.distinct(1))+

lemma prirelRef_length_eq:
  assumes "prirelRef p xs ys z P"
  shows "List.length xs = List.length ys"
  using assms by (induct p xs ys z P rule:prirelRef.induct, auto)

lemma
  assumes "prirelRef p (xs @ s) (ys @ t) [] P" "List.length s = List.length t"
  shows "prirelRef p s t (ys) P"
  using assms 
  apply (induct s t rule:rev_induct_both, auto)
  oops

lemma cttWF_cons_simp:
  assumes "e\<^sub>2 \<noteq> Tock" "e\<^sub>2 \<noteq> Tick" "cttWF ([e\<^sub>2]\<^sub>E # zz)"
  shows "cttWF(zz)"
  using assms
  using cttWF.elims(2) by blast

lemma prirelRef_concat_dist1:
  assumes "cttWF (ys @ [[S]\<^sub>R,[Tock]\<^sub>E])"
  shows
   "prirelRef p (xs @ [[R]\<^sub>R,[Tock]\<^sub>E]) (ys @ [[S]\<^sub>R,[Tock]\<^sub>E]) s P
    =
    (prirelRef p xs ys s P \<and> prirelRef p [[R]\<^sub>R,[Tock]\<^sub>E] [[S]\<^sub>R,[Tock]\<^sub>E] (s @ ys) P)"
  using assms apply auto 
      apply (induct p xs ys s P rule:prirelRef.induct, auto)
  using prirelRef_both_concat_refTock_imp_prefixes apply blast+
         apply (metis append_Cons list.distinct(1) not_prirelRef_concat_refTock)
  using not_prirelRef_concat_refTock apply fastforce
       apply (metis append_Cons list.distinct(1) not_prirelRef_concat_refTock')
      apply (metis append_Cons list.distinct(1) not_prirelRef_concat_refTock')
     apply (induct p xs ys s P rule:prirelRef.induct, auto)
          apply (metis cttWF.simps(1) cttWF.simps(4) cttWF.simps(6) cttWF.simps(8) cttevent.exhaust neq_Nil_conv)
         apply (metis append.left_neutral cttWF.simps(4) cttWF.simps(6) cttWF.simps(8) cttWF_prefix_is_cttWF cttevent.exhaust neq_Nil_conv)
        apply (metis Cons_eq_appendI neq_Nil_conv not_prirelRef_concat_refTock)
  using not_prirelRef_concat_refTock apply fastforce
      apply (metis Cons_eq_appendI neq_Nil_conv not_prirelRef_concat_refTock')
     apply (metis Cons_eq_appendI neq_Nil_conv not_prirelRef_concat_refTock')
    apply (induct p xs ys s P rule:prirelRef.induct, auto)
         apply (metis cttWF.simps(1) cttWF.simps(4) cttWF.simps(6) cttWF.simps(8) cttevent.exhaust neq_Nil_conv)
        apply (metis append.left_neutral cttWF.simps(4) cttWF.simps(6) cttWF.simps(8) cttWF_prefix_is_cttWF cttevent.exhaust neq_Nil_conv)
       apply (metis Cons_eq_appendI neq_Nil_conv not_prirelRef_concat_refTock)
      apply (metis Cons_eq_appendI neq_Nil_conv not_prirelRef_concat_refTock) 
     apply (metis Cons_eq_appendI neq_Nil_conv not_prirelRef_concat_refTock')
    apply (metis Cons_eq_appendI neq_Nil_conv not_prirelRef_concat_refTock')
   apply (induct p xs ys s P rule:prirelRef.induct, auto)
        apply (metis cttWF.simps(1) cttWF.simps(10) cttWF.simps(4) cttWF.simps(6) cttevent.exhaust neq_Nil_conv)
       apply (metis cttWF.simps(1) cttWF.simps(10) cttWF.simps(4) cttWF.simps(6) cttevent.exhaust neq_Nil_conv)
      apply (metis Cons_eq_appendI neq_Nil_conv not_prirelRef_concat_refTock)
     apply (metis Cons_eq_appendI neq_Nil_conv not_prirelRef_concat_refTock)
    apply (metis Cons_eq_appendI neq_Nil_conv not_prirelRef_concat_refTock')
   apply (metis Cons_eq_appendI neq_Nil_conv not_prirelRef_concat_refTock')
apply (induct p xs ys s P rule:prirelRef.induct, auto) 
  apply (metis Cons_eq_appendI prirelRef.simps(4) prirelRef_extend_both_tock_refusal_cttWF)
  by (metis cttWF.simps(1) cttWF.simps(10) cttWF.simps(4) cttWF.simps(6) cttevent.exhaust neq_Nil_conv)

lemma prirelRef_FIXME1:
  assumes "prirelRef p (xs @ [a,b]) (ys @ [[S]\<^sub>R, [Tock]\<^sub>E]) s P" "cttWF (ys @ [[S]\<^sub>R,[Tock]\<^sub>E])"
  shows "prirelRef p [a,b] [[S]\<^sub>R, [Tock]\<^sub>E] (s@ys) P"
  using assms apply (induct p xs ys s P rule:prirelRef.induct, auto)
  using cttWF.elims(2) apply blast
  using cttWF.elims(2) apply blast
              apply (case_tac v, auto, case_tac vb, auto, case_tac x1, auto)
  apply (metis append_Cons neq_Nil_conv prirelRef.simps(28) self_append_conv2)
  apply (case_tac v, auto, case_tac va, auto)
            apply (cases a) apply auto[1]
  apply (metis cttevent.exhaust prirelRef.simps(12) prirelRef.simps(28) prirelRef.simps(3) prirelRef.simps(9))
  apply auto[1]
           apply (case_tac aa) apply auto[1]
  apply (metis append.left_neutral append_Cons cttevent.exhaust neq_Nil_conv prirelRef.simps(12) prirelRef.simps(28) prirelRef.simps(3) prirelRef.simps(9))
  apply auto[1]
          apply (cases a) apply auto[1]
  apply (case_tac vb, case_tac vd) apply auto[2] 
  apply (case_tac x1, case_tac vd) apply auto[2]
  sorry (* LIKELY PROVABLE *)

lemma prirelRef_rhs_refTock_imp_no_gt_Tock_pri:
  assumes "prirelRef p ar (ys @ [[r1]\<^sub>R, [Tock]\<^sub>E]) [] P" "cttWF (ys @ [[r1]\<^sub>R, [Tock]\<^sub>E])"
  shows "\<not>(\<exists>b. b \<notin> r1 \<and> Tock <\<^sup>*p b)"
  using assms 
proof -
  from assms have ll:"List.length ar = List.length (ys @ [[r1]\<^sub>R, [Tock]\<^sub>E])"
    using prirelRef_length_eq by blast
  then show ?thesis
  using assms(1)
  proof (induct ar rule:rev_induct)
    case Nil
    then show ?case by auto
  next
    case (snoc z zs)
    then show ?case 
    proof (induct zs rule:rev_induct)
      case Nil
      then show ?case by auto
    next
      case (snoc x xs)
      then show ?case 
        apply (case_tac z, auto)
         apply (case_tac x1, auto)
           apply (case_tac x, auto)
            apply (meson assms(2) prirelRef.simps(50) prirelRef_FIXME1)
           apply (meson assms(2) prirelRef.simps(50) prirelRef_FIXME1)
          apply (case_tac x, auto)
        using assms(2) prirelRef.simps(47) prirelRef_FIXME1 apply blast
          apply (metis assms(2) prirelRef.simps(3) prirelRef_FIXME1 prirelref_imp_not_exists_higher_pri)
         apply (case_tac x, auto)
        using assms(2) prirelRef.simps(52) prirelRef_FIXME1 apply blast
        using assms(2) prirelRef.simps(52) prirelRef_FIXME1 apply blast
        using assms(2) prirelRef.simps(17) prirelRef_FIXME1 by blast
    qed
  qed
qed

lemma flt2goodAcceptance_extend_consFL_last_fl_e:
  assumes "flt2goodAcceptance fl p" "e \<in>\<^sub>\<F>\<^sub>\<L> last fl" "\<not>(\<exists>b. b \<in>\<^sub>\<F>\<^sub>\<L> last fl \<and> e <\<^sup>*p b)"
  shows "flt2goodAcceptance (fl @\<^sub>\<F>\<^sub>\<L> \<langle>(last fl,e)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>) p"
  using assms apply(induct fl p rule:flt2goodAcceptance.induct, auto)
   apply (case_tac A, auto, case_tac a, auto)
   apply (meson acceptance_event amember.simps(2))
  apply (case_tac A, auto, case_tac a, auto)
  by (metis acceptance_event amember.simps(2))

lemma flt2goodAcceptance_extend_consFL_last_fl_bullet_maximal_pri:
  assumes "flt2goodAcceptance fl p" "last fl = \<bullet>" "maximal(p,e)" "e \<noteq> Tock"
  shows "flt2goodAcceptance (fl @\<^sub>\<F>\<^sub>\<L> \<langle>(last fl,e)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>) p"
  using assms apply(induct fl p rule:flt2goodAcceptance.induct, auto)
   apply (case_tac A, auto, case_tac a, auto)
   apply (meson acceptance_event amember.simps(2))
  apply (case_tac A, auto, case_tac a, auto)
  by (metis acceptance_event amember.simps(2))

lemma CTwf_1c_3_imp_flt2cttobs_FL1_mod:
  assumes "x \<in> P" 
      and CTwf_healthy: "CTwf P" 
      and CT1c_healthy: "CT1c P"
      and CT3_healthy:  "CT3 P"
      and CTRMax_healthy: "CTRMax P"
      and CT4_healthy: "CT4 P"
      and pri:"prirelRef p ar x [] P \<and> x \<in> P"
      and tick_Max:"maximal(p,Tick)"
  shows "\<exists>fl. x = flt2cttobs fl \<and> flt2goodAcceptance fl p \<and> flt2goodTock fl \<and> (\<exists>x. FLTick0 Tick x \<and> FL1 x \<and> {flt2cttobs fl |fl. fl \<in> x} \<subseteq> P \<and> fl \<in> x)"
  using assms
proof(induct x arbitrary:ar rule:rev_induct)
  case Nil
  then show ?case 
    apply (intro exI[where x="\<langle>\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>"], auto)
    apply (rule exI[where x="{\<langle>\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>}"], auto)
    unfolding FL1_def apply auto
    unfolding FLTick0_def apply auto
    by (case_tac s, auto, case_tac x1, auto)
next
  case (snoc x xs)
  then have xs_x_in_P:"xs @ [x] \<in> P"
    by blast
  from snoc have "prirelRef p (List.butlast ar) xs [] P"
    using prirelRef_imp_one_butlast_of_prirelRef
    by metis
  then have "\<exists>ar. prirelRef p ar xs [] P \<and> xs \<in> P"
    using xs_x_in_P apply auto
    using CT1c_def ctt_prefix_concat
    using CT1c_healthy by blast
   
  then have xs_in_P:"xs \<in> P" "cttWF (xs @ [x])"
     apply auto
    using CTwf_def CTwf_healthy xs_x_in_P by blast

  from snoc show ?case
  proof (induct xs rule:rev_induct)
    case Nil
    then show ?case
    proof (cases x)
      case (Ref x1)
      then have "Tick \<in> x1"
        using CTRMax_CT4_Tick CT4_healthy CTRMax_healthy
        using snoc.prems(1) by blast
      then show ?thesis
          apply (intro exI[where x="\<langle>[{x. x \<notin> x1} - {Tick}]\<^sub>\<F>\<^sub>\<L>\<rangle>\<^sub>\<F>\<^sub>\<L>"], auto)
          using Ref apply auto
           apply (rule exI[where x="{z. z \<le> \<langle>[{z. z \<notin> x1} - {Tick}]\<^sub>\<F>\<^sub>\<L>\<rangle>\<^sub>\<F>\<^sub>\<L>}"], auto)
        unfolding FLTick0_def apply auto
          apply (case_tac x, auto)
        apply (metis (full_types) amember.elims(2) less_eq_acceptance.simps(3) mem_Collect_eq)
        using FL1_def dual_order.trans apply blast
        using fl_le_CT1c using Nil by auto
      (*next
        case False
        then show ?thesis
          using Ref apply (intro exI[where x="\<langle>[{x. x \<notin> x1} - {Tick}]\<^sub>\<F>\<^sub>\<L>\<rangle>\<^sub>\<F>\<^sub>\<L>"], auto)
          apply (rule exI[where x="{z. z \<le> \<langle>[{z. z \<notin> x1} - {Tick}]\<^sub>\<F>\<^sub>\<L>\<rangle>\<^sub>\<F>\<^sub>\<L>}"], auto)
        unfolding FLTick0_def apply auto
          apply (case_tac x, auto)
        apply (case_tac x1a, auto)
        sledgehammer
        using FL1_def dual_order.trans apply blast
        using fl_le_CT1c using Nil by auto
      qed*)
        
    next
      case (ObsEvent x2)
      then have pri_x:"prirelRef p ar [x] [] P"
        using Nil.prems(8) by auto
      then show ?thesis
      proof (cases x2)
        case (Event ev)
        then show ?thesis
        proof (cases "maximal(p,Event ev)")
          case True
          then show ?thesis using Event
            apply (intro exI[where x="\<langle>(\<bullet>,Event ev)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>"])
            apply (simp add:ObsEvent)
            apply (intro exI[where x="{z. z \<le> \<langle>(\<bullet>,Event ev)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>}"], auto)
            unfolding FLTick0_def apply auto
            apply (metis acceptance_set amember.simps(1) bullet_left_zero2 tickWF.simps(1) tickWF.simps(2) x_le_x_concat2 xs_less_eq_z_two_only)
            using FL1_def dual_order.trans apply blast
            using ObsEvent Nil by (simp add: fl_le_CT1c_Event)
        next
          case False
          then obtain ES where ES:"Event ev \<notin> ES \<and> (\<forall>b. ((Event ev) <\<^sup>*p b) \<longrightarrow> b \<in> ES) \<and> [[ES]\<^sub>R] \<in> P"
            using pri_x ObsEvent Event False 
            apply (case_tac ar, simp)
            apply (case_tac ar, simp, case_tac list, simp, case_tac a, simp)          
            apply blast
             apply simp
            using prirelRef_imp_butlast_of_prirelRefs by fastforce
          then have "Tick \<in> ES"
            using CT1c_healthy CT4_healthy CTRMax_CT4_CT1c_CTTickTrace CTRMax_healthy CTTickTrace.simps(3) by blast
          then show ?thesis using ObsEvent Event False ES
            apply (intro exI[where x="\<langle>([{x. x \<notin> ES}]\<^sub>\<F>\<^sub>\<L>,Event ev)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>"])
            apply (simp add:ObsEvent, auto)
            apply (intro exI[where x="{z. z \<le> \<langle>([{x. x \<notin> ES}]\<^sub>\<F>\<^sub>\<L>,Event ev)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>}"], auto)
              apply (simp add: FLTick0_Tick_Event)
              using FL1_def dual_order.trans apply blast
          using ObsEvent Nil by (simp add: fl_le_CT1c_ES_Event)
      qed
      next
        case Tock
        text \<open> There cannot be a Tock without a refusal before it following cttWF,
               so this case is automatically solved. \<close>
        then show ?thesis
          using Nil.prems(3) ObsEvent
          by (metis CTwf_def Nil.prems(2) append_Nil cttWF.simps(6))
      next
        case Tick
        then show ?thesis
          apply (intro exI[where x="\<langle>(\<bullet>,Tick)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>"])
          apply (auto simp add: ObsEvent)
          apply (intro exI[where x="{z. z \<le> \<langle>(\<bullet>,Tick)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>}"])
          apply auto
          unfolding FLTick0_def apply auto
          apply (metis acceptance_set amember.simps(1) bullet_left_zero2 tickWF.simps(1) tickWF.simps(2) x_le_x_concat2 xs_less_eq_z_two_only)
          using FL1_def dual_order.trans apply blast
          using ObsEvent Nil by (simp add:fl_le_CT1c_Tick)
      qed
    qed
  next
    case yys:(snoc y ys)
    then have prirelRefyys:"prirelRef p ar ((ys @ [y]) @ [x]) [] P \<and> (ys @ [y]) @ [x] \<in> P"
      by auto

    from yys have ys_y_inP:"ys @ [y] \<in> P" using CT1c_def
      by (metis ctt_prefix_concat)
    from yys have "prirelRef p (List.butlast ar) (ys @ [y]) [] P"
      using prirelRef_imp_one_butlast_of_prirelRef by blast
    then have ys_y_fl:"\<exists>fl. ys @ [y] = flt2cttobs fl \<and> flt2goodAcceptance fl p \<and> flt2goodTock fl \<and> (\<exists>x. FLTick0 Tick x \<and> FL1 x \<and> {flt2cttobs fl |fl. fl \<in> x} \<subseteq> P \<and> fl \<in> x)"
      using ys_y_inP yys by auto
    then have ys_y_x: "\<exists>fl. ys @ [y] @ [x] = flt2cttobs fl @ [x] \<and> flt2goodAcceptance fl p \<and> flt2goodTock fl \<and> (\<exists>x. FLTick0 Tick x \<and> FL1 x \<and> {flt2cttobs fl |fl. fl \<in> x} \<subseteq> P \<and> fl \<in> x)"
      by auto

    then show ?case
    proof (cases y)
      case r1:(Ref r1)
      then have exp:"\<exists>fl. ys @ [[r1]\<^sub>R] @ [x] = flt2cttobs fl @ [x] \<and> flt2goodAcceptance fl p \<and> (\<exists>x. FLTick0 Tick x \<and> FL1 x \<and> {flt2cttobs fl |fl. fl \<in> x} \<subseteq> P \<and> fl \<in> x)"
        using ys_y_fl by auto

      then show ?thesis
      proof (cases x)
        case (Ref r2) text \<open>Not allowed\<close>
        then have "\<not>cttWF (ys @ [Ref r1, Ref r2])"
          by (induct ys rule:cttWF.induct, auto)
        then have "ys @ [Ref r1, Ref r2] \<notin> P"
          using assms unfolding CTwf_def by auto
        then show ?thesis using Ref r1 yys by auto
      next
        case (ObsEvent e1)
        then show ?thesis
        proof (cases e1)
          case (Event e2)
          then have "\<not>cttWF (ys @ [Ref r1, [Event e2]\<^sub>E])"
            by (induct ys rule:cttWF.induct, auto)
          then show ?thesis
            using assms unfolding CTwf_def
            by (metis Cons_eq_append_conv Event ObsEvent append_eq_appendI r1 ys_y_x yys.prems(2))
        next
          case Tock
          then have tock_not_in_r1: "Tock \<notin> r1"
            using CT3_any_cons_end_tock CT3_healthy ObsEvent r1 yys.prems(2) by auto
          then have r1_good_pri:"\<not>(\<exists>b. b \<notin> r1 \<and> Tock <\<^sup>*p b)"
            using r1 ObsEvent Tock prirelRefyys prirelRef_rhs_refTock_imp_no_gt_Tock_pri
            by (metis CTwf_def CTwf_healthy append.assoc append_Cons append_Nil)
          
          text \<open>Then from the hypothesis we have the case:\<close>

          then obtain fl where fl:"ys @ [Ref r1] = flt2cttobs fl \<and> flt2goodAcceptance fl p \<and> flt2goodTock fl \<and> (\<exists>x. FLTick0 Tick x \<and> FL1 x \<and>  {flt2cttobs fl |fl. fl \<in> x} \<subseteq> P \<and> fl \<in> x)"
            using r1 ys_y_fl by blast
          then have last_fl_acceptance:"last fl = [{x. x \<notin> r1}]\<^sub>\<F>\<^sub>\<L>"
            by (metis (mono_tags, lifting) last_flt2cttobs_eq_ref_imp_last snoc_eq_iff_butlast)
          then have r1_good_pri_acceptance:"\<not>(\<exists>b. b \<in>\<^sub>\<F>\<^sub>\<L> [{x. x \<notin> r1}]\<^sub>\<F>\<^sub>\<L> \<and> e1 <\<^sup>*p b)"
            using ObsEvent Tock r1_good_pri 
            by simp
          then have tock_in_last_fl: "Tock \<in>\<^sub>\<F>\<^sub>\<L> last fl"
            using last_fl_acceptance tock_not_in_r1 by simp
          then have "ys @ [[r1]\<^sub>R] @ [[Tock]\<^sub>E] = flt2cttobs fl @ [[Tock]\<^sub>E] \<and> flt2goodAcceptance fl p \<and> flt2goodTock fl \<and> (\<exists>x. FLTick0 Tick x \<and> FL1 x \<and> {flt2cttobs fl |fl. fl \<in> x} \<subseteq> P \<and> fl \<in> x)"
            by (simp add: fl)
          then have "ys @ [[r1]\<^sub>R] @ [[Tock]\<^sub>E] = flt2cttobs (fl @\<^sub>\<F>\<^sub>\<L> \<langle>(last fl,Tock)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>) \<and> flt2goodAcceptance fl p \<and> flt2goodTock fl \<and> (\<exists>x. FLTick0 Tick x \<and> FL1 x \<and> {flt2cttobs fl |fl. fl \<in> x} \<subseteq> P \<and> fl \<in> x)"
            using tock_in_last_fl by (simp add: flt2cttobs_last_tock fl)

          have "{flt2cttobs fl\<^sub>0|fl\<^sub>0. fl\<^sub>0 \<le> fl} \<subseteq> P"
            using CT1c_healthy 
            using FL1_def fl subset_eq by blast

          have flt2cttobs_strongFL_subset:"{flt2cttobs fl\<^sub>0|fl\<^sub>0. fl\<^sub>0 \<le>\<^sub>\<F>\<^sub>\<L> (fl @\<^sub>\<F>\<^sub>\<L> \<langle>(last fl,Tock)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>)} \<subseteq> P"
            apply auto
            using strong_less_eq_fltrace_imp_flt2cttobs_ctt
            by (metis (no_types, lifting) CT1c_def CT1c_healthy ObsEvent Tock \<open>ys @ [[r1]\<^sub>R] @ [[Tock]\<^sub>E] = flt2cttobs (fl @\<^sub>\<F>\<^sub>\<L> \<langle>(Finite_Linear_Model.last fl,Tock)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>) \<and> flt2goodAcceptance fl p \<and> flt2goodTock fl \<and> (\<exists>x. FLTick0 Tick x \<and> FL1 x \<and> {flt2cttobs fl |fl. fl \<in> x} \<subseteq> P \<and> fl \<in> x)\<close> \<open>ys @ [[r1]\<^sub>R] @ [[Tock]\<^sub>E] = flt2cttobs fl @ [[Tock]\<^sub>E] \<and> flt2goodAcceptance fl p \<and> flt2goodTock fl \<and> (\<exists>x. FLTick0 Tick x \<and> FL1 x \<and> {flt2cttobs fl |fl. fl \<in> x} \<subseteq> P \<and> fl \<in> x)\<close> fl r1 yys.prems(2))

          have "(ys @ [[r1]\<^sub>R] @ [[Tock]\<^sub>E] = flt2cttobs(fl @\<^sub>\<F>\<^sub>\<L> \<langle>(last fl,Tock)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>) \<and> flt2goodAcceptance fl p \<and> flt2goodTock fl
                \<and> (\<exists>x. FLTick0 Tick x \<and> FL1 x \<and> {flt2cttobs fl |fl. fl \<in> x} \<subseteq> P \<and> fl \<in> x))"
            using \<open>ys @ [[r1]\<^sub>R] @ [[Tock]\<^sub>E] = flt2cttobs (fl @\<^sub>\<F>\<^sub>\<L> \<langle>(Finite_Linear_Model.last fl,Tock)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>) \<and> flt2goodAcceptance fl p \<and> flt2goodTock fl \<and> (\<exists>x. FLTick0 Tick x \<and> FL1 x \<and> {flt2cttobs fl |fl. fl \<in> x} \<subseteq> P \<and> fl \<in> x)\<close> tock_in_last_fl by blast
          then have 
               "ys @ [[r1]\<^sub>R] @ [[Tock]\<^sub>E] = flt2cttobs (fl @\<^sub>\<F>\<^sub>\<L> \<langle>(last fl,Tock)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>) \<and> flt2goodAcceptance fl p \<and> flt2goodTock fl  
                \<and> (\<exists>x. FLTick0 Tick x \<and> FL1 (x \<union> {fl\<^sub>0. fl\<^sub>0 \<le>\<^sub>\<F>\<^sub>\<L> (fl @\<^sub>\<F>\<^sub>\<L> \<langle>(last fl,Tock)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>)}) \<and> {flt2cttobs fl |fl. fl \<in> x} \<subseteq> P \<and> fl \<in> x)"
            using FL1_extends_strong_less_eq_fltrace_last tock_in_last_fl
            by (metis (mono_tags, lifting) Collect_cong \<open>ys @ [[r1]\<^sub>R] @ [[Tock]\<^sub>E] = flt2cttobs (fl @\<^sub>\<F>\<^sub>\<L> \<langle>(Finite_Linear_Model.last fl,Tock)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>) \<and> flt2goodAcceptance fl p \<and> flt2goodTock fl \<and> (\<exists>x. FLTick0 Tick x \<and> FL1 x \<and> {flt2cttobs fl |fl. fl \<in> x} \<subseteq> P \<and> fl \<in> x)\<close> fl)
          then have 
               "ys @ [[r1]\<^sub>R] @ [[Tock]\<^sub>E] = flt2cttobs (fl @\<^sub>\<F>\<^sub>\<L> \<langle>(last fl,Tock)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>) \<and> flt2goodAcceptance fl p \<and> flt2goodTock fl  
                \<and> (\<exists>x. FLTick0 Tick (x \<union> {fl\<^sub>0. fl\<^sub>0 \<le>\<^sub>\<F>\<^sub>\<L> (fl @\<^sub>\<F>\<^sub>\<L> \<langle>(last fl,Tock)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>)}) 
                        \<and> FL1 (x \<union> {fl\<^sub>0. fl\<^sub>0 \<le>\<^sub>\<F>\<^sub>\<L> (fl @\<^sub>\<F>\<^sub>\<L> \<langle>(last fl,Tock)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>)}) \<and> {flt2cttobs fl |fl. fl \<in> x} \<subseteq> P \<and> fl \<in> x)"
            using FLTick0_extends_strong_less_eq_fltrace_last tock_in_last_fl
            by auto
          then have 
               "ys @ [[r1]\<^sub>R] @ [[Tock]\<^sub>E] = flt2cttobs (fl @\<^sub>\<F>\<^sub>\<L> \<langle>(last fl,Tock)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>) \<and> flt2goodAcceptance fl p \<and> flt2goodTock fl 
                \<and> (\<exists>x. FLTick0 Tick (x \<union> {fl\<^sub>0. fl\<^sub>0 \<le>\<^sub>\<F>\<^sub>\<L> (fl @\<^sub>\<F>\<^sub>\<L> \<langle>(last fl,Tock)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>)}) 
                    \<and> FL1 (x \<union> {fl\<^sub>0. fl\<^sub>0 \<le>\<^sub>\<F>\<^sub>\<L> (fl @\<^sub>\<F>\<^sub>\<L> \<langle>(last fl,Tock)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>)})
                    \<and> {flt2cttobs fl\<^sub>0 |fl\<^sub>0. fl\<^sub>0 \<in> (x \<union> {fl\<^sub>0. fl\<^sub>0 \<le>\<^sub>\<F>\<^sub>\<L> (fl @\<^sub>\<F>\<^sub>\<L> \<langle>(last fl,Tock)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>)})} \<subseteq> P \<and> fl \<in> x)"
            using flt2cttobs_strongFL_subset
            by (smt Un_iff mem_Collect_eq subset_iff)
          then have 
               "ys @ [[r1]\<^sub>R] @ [[Tock]\<^sub>E] = flt2cttobs (fl @\<^sub>\<F>\<^sub>\<L> \<langle>(last fl,Tock)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>) \<and> flt2goodAcceptance fl p \<and> flt2goodTock fl 
                \<and> (\<exists>x. FLTick0 Tick (x \<union> {fl\<^sub>0. fl\<^sub>0 \<le>\<^sub>\<F>\<^sub>\<L> (fl @\<^sub>\<F>\<^sub>\<L> \<langle>(last fl,Tock)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>)}) 
                \<and> FL1 (x \<union> {fl\<^sub>0. fl\<^sub>0 \<le>\<^sub>\<F>\<^sub>\<L> (fl @\<^sub>\<F>\<^sub>\<L> \<langle>(last fl,Tock)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>)})
                \<and> {flt2cttobs fl\<^sub>0 |fl\<^sub>0. fl\<^sub>0 \<in> (x \<union> {fl\<^sub>0. fl\<^sub>0 \<le>\<^sub>\<F>\<^sub>\<L> (fl @\<^sub>\<F>\<^sub>\<L> \<langle>(last fl,Tock)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>)})} \<subseteq> P 
                \<and> fl \<in> x
                \<and> fl @\<^sub>\<F>\<^sub>\<L> \<langle>(last fl,Tock)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L> \<in> (x \<union> {fl\<^sub>0. fl\<^sub>0 \<le>\<^sub>\<F>\<^sub>\<L> (fl @\<^sub>\<F>\<^sub>\<L> \<langle>(last fl,Tock)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>)}))"
            by (simp add: strong_less_eq_fltrace_refl)
          then have 
               "ys @ [[r1]\<^sub>R] @ [[Tock]\<^sub>E] = flt2cttobs (fl @\<^sub>\<F>\<^sub>\<L> \<langle>(last fl,Tock)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>) \<and> flt2goodAcceptance fl p \<and> flt2goodTock fl 
                \<and> (\<exists>z. FLTick0 Tick z \<and> FL1 z
                \<and> {flt2cttobs fl\<^sub>0 |fl\<^sub>0. fl\<^sub>0 \<in> z} \<subseteq> P 
                \<and> fl @\<^sub>\<F>\<^sub>\<L> \<langle>(last fl,Tock)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L> \<in> z)"
            by blast
          then have 
               "ys @ [[r1]\<^sub>R] @ [[Tock]\<^sub>E] = flt2cttobs (fl @\<^sub>\<F>\<^sub>\<L> \<langle>(last fl,Tock)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>) \<and> flt2goodAcceptance fl p \<and> flt2goodTock fl 
                \<and> flt2goodTock (fl @\<^sub>\<F>\<^sub>\<L> \<langle>(last fl,Tock)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>)
                \<and> (\<exists>z. FLTick0 Tick z \<and> FL1 z
                \<and> {flt2cttobs fl\<^sub>0 |fl\<^sub>0. fl\<^sub>0 \<in> z} \<subseteq> P 
                \<and> fl @\<^sub>\<F>\<^sub>\<L> \<langle>(last fl,Tock)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L> \<in> z)"
            using tock_in_last_fl by (simp add:flt2goodTock_extend_consFL_last_fl_e)
          then have 
               "ys @ [[r1]\<^sub>R] @ [[Tock]\<^sub>E] = flt2cttobs (fl @\<^sub>\<F>\<^sub>\<L> \<langle>(last fl,Tock)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>) 
                \<and> flt2goodAcceptance fl p 
                \<and> flt2goodAcceptance (fl @\<^sub>\<F>\<^sub>\<L> \<langle>(last fl,Tock)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>) p
                \<and> flt2goodTock fl 
                \<and> flt2goodTock (fl @\<^sub>\<F>\<^sub>\<L> \<langle>(last fl,Tock)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>)
                \<and> (\<exists>z. FLTick0 Tick z \<and> FL1 z
                \<and> {flt2cttobs fl\<^sub>0 |fl\<^sub>0. fl\<^sub>0 \<in> z} \<subseteq> P 
                \<and> fl @\<^sub>\<F>\<^sub>\<L> \<langle>(last fl,Tock)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L> \<in> z)"
            using flt2goodAcceptance_extend_consFL_last_fl_e
            by (metis (mono_tags, lifting) Tock last_fl_acceptance r1_good_pri_acceptance tock_in_last_fl)
          then have 
               "\<exists>fl. ys @ [[r1]\<^sub>R] @ [[Tock]\<^sub>E] = flt2cttobs fl \<and> flt2goodAcceptance fl p \<and> flt2goodTock fl 
                \<and> (\<exists>z. FLTick0 Tick z \<and> FL1 z \<and> {flt2cttobs fl\<^sub>0 |fl\<^sub>0. fl\<^sub>0 \<in> z} \<subseteq> P \<and> fl \<in> z)"
            by blast
          then show ?thesis using Tock ObsEvent r1 by auto
        next
          case Tick
          then have "\<not>cttWF (ys @ [Ref r1, [Tick]\<^sub>E])"
            by (induct ys rule:cttWF.induct, auto)
          then show ?thesis
            using CTwf_healthy unfolding CTwf_def
            by (metis ObsEvent Tick append.assoc append_Cons append_Nil r1 ys_y_x yys.prems(2))
        qed
      qed
    next
      case e1:(ObsEvent e1)
      text \<open>Then from the hypothesis we have the case:\<close>
      then obtain fl where fl:"ys @ [[e1]\<^sub>E] = flt2cttobs fl \<and> flt2goodAcceptance fl p \<and> flt2goodTock fl \<and> (\<exists>x. FLTick0 Tick x \<and> FL1 x \<and> {flt2cttobs fl |fl. fl \<in> x} \<subseteq> P \<and> fl \<in> x)"
        using ys_y_fl by blast
      then have ys_e1_x:"ys @ [[e1]\<^sub>E] @ [x] = flt2cttobs fl @ [x] \<and> flt2goodAcceptance fl p \<and> flt2goodTock fl \<and> (\<exists>x. FLTick0 Tick x \<and> FL1 x \<and> {flt2cttobs fl |fl. fl \<in> x} \<subseteq> P \<and> fl \<in> x)"
        by auto
      then have last_fl:"last fl = \<bullet>"
        by (metis cttobs.distinct(1) fl flt2cttobs.simps(1) flt2cttobs_last_fl_not_bullet_dist_list_cons last_snoc)

      then show ?thesis
      proof (cases x)
        case e2:(ObsEvent e2)
        then have "ys @ [[e1]\<^sub>E] @ [[e2]\<^sub>E] \<in> P"
          using e1 fl ys_e1_x yys.prems(2) by presburger
        then have "[Tick]\<^sub>E \<notin> set (ys @ [[e1]\<^sub>E])" 
          using CTwf_healthy CTwf_concat_prefix_set_no_Tick
          using e1 e2 yys.prems(2) by blast
        then have Tick_not_in_events_fl: "Tick \<notin> events fl"
          by (simp add: event_not_in_set_of_flt2cttobs_imp_not_in_events fl)
          
        then show ?thesis
        proof (cases e2)
          case (Event e3)
          have "prirelRef p ar (ys @ [[e1]\<^sub>E,[Event e3]\<^sub>E]) [] P \<and> (ys @ [[e1]\<^sub>E,[Event e3]\<^sub>E]) \<in> P"
             using prirelRefyys e1 Event e2 by auto
          then show ?thesis
          proof (cases "maximal(p,Event e3)")
            case True
            then have flt2cttobs_strongFL_subset:"{flt2cttobs fl\<^sub>0|fl\<^sub>0. fl\<^sub>0 \<le>\<^sub>\<F>\<^sub>\<L> (fl @\<^sub>\<F>\<^sub>\<L> \<langle>(last fl,Event e3)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>)} \<subseteq> P"
              apply auto
              using strong_less_eq_fltrace_imp_flt2cttobs_ctt
              by (metis (no_types, lifting) CT1c_def CT1c_healthy Event cttevent.simps(3) e1 e2 fl flt2cttobs_last_non_tock last_fl last_snoc yys.prems(2))
          
            from fl have fl_e3: "ys @ [[e1]\<^sub>E] @ [[Event e3]\<^sub>E] = flt2cttobs fl @ [[Event e3]\<^sub>E]
                    \<and> flt2goodAcceptance fl p \<and> flt2goodTock fl \<and> (\<exists>x. FLTick0 Tick x \<and> FL1 x \<and> {flt2cttobs fl\<^sub>0 |fl\<^sub>0. fl\<^sub>0 \<in> x} \<subseteq> P \<and> fl \<in> x)"
              using ys_e1_x by auto
            also have "... =
                    (ys @ [[e1]\<^sub>E] @ [[Event e3]\<^sub>E] = flt2cttobs(fl @\<^sub>\<F>\<^sub>\<L> \<langle>(last fl,Event e3)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>)
                    \<and> flt2goodAcceptance fl p \<and> flt2goodTock fl \<and> (\<exists>x. FLTick0 Tick x \<and> FL1 x \<and> {flt2cttobs fl\<^sub>0 |fl\<^sub>0. fl\<^sub>0 \<in> x} \<subseteq> P \<and> fl \<in> x))"
              proof -
                from fl have "ys @ [[e1]\<^sub>E] = flt2cttobs fl"
                  by auto
                then have "List.last(flt2cttobs fl) = [e1]\<^sub>E"
                  by (metis last_snoc)
                then have "flt2cttobs fl @ [[Event e3]\<^sub>E] = flt2cttobs(fl @\<^sub>\<F>\<^sub>\<L> \<langle>(last fl,Event e3)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>)"
                  using fl last_fl flt2cttobs_last_non_tock
                  by (metis (no_types, lifting) cttevent.distinct(1))
                then show ?thesis using calculation  by auto
              qed
            finally have "
                    ys @ [[e1]\<^sub>E] @ [[Event e3]\<^sub>E] = flt2cttobs(fl @\<^sub>\<F>\<^sub>\<L> \<langle>(last fl,Event e3)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>)
                    \<and> flt2goodAcceptance fl p \<and> flt2goodTock fl 
                    \<and> (\<exists>x. FLTick0 Tick x \<and> FL1 (x \<union> {fl\<^sub>0. fl\<^sub>0 \<le>\<^sub>\<F>\<^sub>\<L> (fl @\<^sub>\<F>\<^sub>\<L> \<langle>(last fl,Event e3)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>)}) 
                        \<and> {flt2cttobs fl\<^sub>0 |fl\<^sub>0. fl\<^sub>0 \<in> x} \<subseteq> P \<and> fl \<in> x)"
                apply auto using FL1_extends_strong_less_eq_fltrace_last_bullet last_fl 
              by fastforce
            then have "
                    ys @ [[e1]\<^sub>E] @ [[Event e3]\<^sub>E] = flt2cttobs(fl @\<^sub>\<F>\<^sub>\<L> \<langle>(last fl,Event e3)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>)
                    \<and> flt2goodAcceptance fl p \<and> flt2goodTock fl 
                    \<and> (\<exists>x. FLTick0 Tick (x \<union> {fl\<^sub>0. fl\<^sub>0 \<le>\<^sub>\<F>\<^sub>\<L> (fl @\<^sub>\<F>\<^sub>\<L> \<langle>(last fl,Event e3)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>)}) 
                        \<and> FL1 (x \<union> {fl\<^sub>0. fl\<^sub>0 \<le>\<^sub>\<F>\<^sub>\<L> (fl @\<^sub>\<F>\<^sub>\<L> \<langle>(last fl,Event e3)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>)}) 
                        \<and> {flt2cttobs fl\<^sub>0 |fl\<^sub>0. fl\<^sub>0 \<in> x} \<subseteq> P \<and> fl \<in> x)"
              apply auto using FL0_Tick_extends_strong_less_eq_fltrace_last_bullet last_fl Tick_not_in_events_fl
              by blast
           then have "
                    ys @ [[e1]\<^sub>E] @ [[Event e3]\<^sub>E] = flt2cttobs(fl @\<^sub>\<F>\<^sub>\<L> \<langle>(last fl,Event e3)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>)
                    \<and> flt2goodAcceptance fl p \<and> flt2goodTock fl 
                    \<and> (\<exists>x. FLTick0 Tick (x \<union> {fl\<^sub>0. fl\<^sub>0 \<le>\<^sub>\<F>\<^sub>\<L> (fl @\<^sub>\<F>\<^sub>\<L> \<langle>(last fl,Event e3)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>)}) 
                        \<and> FL1 (x \<union> {fl\<^sub>0. fl\<^sub>0 \<le>\<^sub>\<F>\<^sub>\<L> (fl @\<^sub>\<F>\<^sub>\<L> \<langle>(last fl,Event e3)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>)}) 
                        \<and> {flt2cttobs fl\<^sub>0 |fl\<^sub>0. fl\<^sub>0 \<in> (x \<union> {fl\<^sub>0. fl\<^sub>0 \<le>\<^sub>\<F>\<^sub>\<L> (fl @\<^sub>\<F>\<^sub>\<L> \<langle>(last fl,Event e3)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>)})} \<subseteq> P \<and> fl \<in> x)"  
             using flt2cttobs_strongFL_subset 
             by (smt Un_iff mem_Collect_eq subset_iff)
           then have "
                    ys @ [[e1]\<^sub>E] @ [[Event e3]\<^sub>E] = flt2cttobs(fl @\<^sub>\<F>\<^sub>\<L> \<langle>(last fl,Event e3)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>)
                    \<and> flt2goodAcceptance fl p \<and> flt2goodTock fl 
                    \<and> (\<exists>x. FLTick0 Tick (x \<union> {fl\<^sub>0. fl\<^sub>0 \<le>\<^sub>\<F>\<^sub>\<L> (fl @\<^sub>\<F>\<^sub>\<L> \<langle>(last fl,Event e3)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>)}) 
                        \<and> FL1 (x \<union> {fl\<^sub>0. fl\<^sub>0 \<le>\<^sub>\<F>\<^sub>\<L> (fl @\<^sub>\<F>\<^sub>\<L> \<langle>(last fl,Event e3)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>)}) 
                        \<and> {flt2cttobs fl\<^sub>0 |fl\<^sub>0. fl\<^sub>0 \<in> (x \<union> {fl\<^sub>0. fl\<^sub>0 \<le>\<^sub>\<F>\<^sub>\<L> (fl @\<^sub>\<F>\<^sub>\<L> \<langle>(last fl,Event e3)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>)})} \<subseteq> P 
                        \<and> fl \<in> x
                        \<and> fl @\<^sub>\<F>\<^sub>\<L> \<langle>(last fl,Event e3)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L> \<in> (x \<union> {fl\<^sub>0. fl\<^sub>0 \<le>\<^sub>\<F>\<^sub>\<L> (fl @\<^sub>\<F>\<^sub>\<L> \<langle>(last fl,Event e3)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>)}))"
              by (simp add: strong_less_eq_fltrace_refl)  
           then have "
                    ys @ [[e1]\<^sub>E] @ [[Event e3]\<^sub>E] = flt2cttobs(fl @\<^sub>\<F>\<^sub>\<L> \<langle>(last fl,Event e3)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>)
                    \<and> flt2goodAcceptance fl p \<and> flt2goodTock fl 
                    \<and> (\<exists>z. FLTick0 Tick z \<and> FL1 z 
                        \<and> {flt2cttobs fl\<^sub>0 |fl\<^sub>0. fl\<^sub>0 \<in> z} \<subseteq> P 
                        \<and> fl @\<^sub>\<F>\<^sub>\<L> \<langle>(last fl,Event e3)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L> \<in> z)"
             by blast
           then have "
                    ys @ [[e1]\<^sub>E] @ [[Event e3]\<^sub>E] = flt2cttobs(fl @\<^sub>\<F>\<^sub>\<L> \<langle>(last fl,Event e3)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>)
                    \<and> flt2goodAcceptance fl p \<and> flt2goodTock fl 
                    \<and> flt2goodTock (fl @\<^sub>\<F>\<^sub>\<L> \<langle>(last fl,Event e3)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>)
                    \<and> (\<exists>z. FLTick0 Tick z \<and> FL1 z 
                        \<and> {flt2cttobs fl\<^sub>0 |fl\<^sub>0. fl\<^sub>0 \<in> z} \<subseteq> P 
                        \<and> fl @\<^sub>\<F>\<^sub>\<L> \<langle>(last fl,Event e3)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L> \<in> z)"
             using last_fl flt2goodTock_extend_consFL_last_fl_bullet
             by blast
           then have "
                    ys @ [[e1]\<^sub>E] @ [[Event e3]\<^sub>E] = flt2cttobs(fl @\<^sub>\<F>\<^sub>\<L> \<langle>(last fl,Event e3)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>)
                    \<and> flt2goodAcceptance fl p 
                    \<and> flt2goodAcceptance (fl @\<^sub>\<F>\<^sub>\<L> \<langle>(last fl,Event e3)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>) p
                    \<and> flt2goodTock fl 
                    \<and> flt2goodTock (fl @\<^sub>\<F>\<^sub>\<L> \<langle>(last fl,Event e3)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>)
                    \<and> (\<exists>z. FLTick0 Tick z \<and> FL1 z 
                        \<and> {flt2cttobs fl\<^sub>0 |fl\<^sub>0. fl\<^sub>0 \<in> z} \<subseteq> P 
                        \<and> fl @\<^sub>\<F>\<^sub>\<L> \<langle>(last fl,Event e3)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L> \<in> z)"
             using flt2goodAcceptance_extend_consFL_last_fl_bullet_maximal_pri
             by (metis (no_types, lifting) True acceptance_event acceptance_set append_self_conv bullet_right_zero2 butlast_last_cons2_FL fl_cons_acceptance_consFL fl_e3 flt2cttobs.simps(2) flt2cttobs_acceptance_cons_eq_list_cons last_fl not_Cons_self2)
           then have "
                    \<exists>fl. ys @ [[e1]\<^sub>E] @ [[Event e3]\<^sub>E] = flt2cttobs(fl)
                    \<and> flt2goodAcceptance fl p \<and> flt2goodTock fl 
                    \<and> (\<exists>z. FLTick0 Tick z \<and> FL1 z \<and> {flt2cttobs fl\<^sub>0 |fl\<^sub>0. fl\<^sub>0 \<in> z} \<subseteq> P \<and> fl \<in> z)"
             by blast
           then show ?thesis using Event e1 e2 by auto
          next
            case False
            then obtain Z where "ys @ [[e1]\<^sub>E] @ [[Z]\<^sub>R] \<in> P \<and> Event e3 \<notin> Z \<and> \<not>(\<exists>b. b \<notin> Z \<and> Event e3 <\<^sup>*p b)"
              apply auto sorry
            (* Need to pick a different last fl here, which is prioritised instead ! *)
            then show ?thesis sorry
          qed
          
        next
          case Tock
          then have "\<not>cttWF (ys @ [[e1]\<^sub>E, [Tock]\<^sub>E])"
            apply (induct ys rule:cttWF.induct, auto)
            using cttWF.elims(2) cttWF.simps(6) by blast+
          then show ?thesis
            using e1 e2 CTwf_healthy unfolding CTwf_def
            by (metis Tock append_eq_Cons_conv fl ys_e1_x yys.prems(2))
        next
          case Tick
          have flt2cttobs_strongFL_subset:"{flt2cttobs fl\<^sub>0|fl\<^sub>0. fl\<^sub>0 \<le>\<^sub>\<F>\<^sub>\<L> (fl @\<^sub>\<F>\<^sub>\<L> \<langle>(last fl,Tick)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>)} \<subseteq> P"
            apply auto
            using strong_less_eq_fltrace_imp_flt2cttobs_ctt
            by (metis (no_types, lifting) CT1c_def CT1c_healthy Tick cttevent.distinct(5) e1 e2 fl flt2cttobs_last_non_tock last_fl last_snoc yys.prems(2))
            
          from fl have fl_e3: "ys @ [[e1]\<^sub>E] @ [[Tick]\<^sub>E] = flt2cttobs fl @ [[Tick]\<^sub>E]
                  \<and> flt2goodAcceptance fl p \<and> flt2goodTock fl \<and> (\<exists>x. FLTick0 Tick x \<and> FL1 x \<and> {flt2cttobs fl\<^sub>0 |fl\<^sub>0. fl\<^sub>0 \<in> x} \<subseteq> P \<and> fl \<in> x)"
            using ys_e1_x by auto
          also have "... =
                  (ys @ [[e1]\<^sub>E] @ [[Tick]\<^sub>E] = flt2cttobs(fl @\<^sub>\<F>\<^sub>\<L> \<langle>(last fl,Tick)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>)
                  \<and> flt2goodAcceptance fl p \<and> flt2goodTock fl \<and> (\<exists>x. FLTick0 Tick x \<and> FL1 x \<and> {flt2cttobs fl\<^sub>0 |fl\<^sub>0. fl\<^sub>0 \<in> x} \<subseteq> P \<and> fl \<in> x))"
            proof -
              from fl have "ys @ [[e1]\<^sub>E] = flt2cttobs fl"
                by auto
              then have "List.last(flt2cttobs fl) = [e1]\<^sub>E"
                by (metis last_snoc)
              then have "flt2cttobs fl @ [[Tick]\<^sub>E] = flt2cttobs(fl @\<^sub>\<F>\<^sub>\<L> \<langle>(last fl,Tick)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>)"
                using fl last_fl flt2cttobs_last_non_tock
                by (metis (no_types, lifting) cttevent.simps(7))
              then show ?thesis using calculation  by auto
            qed
          finally have "
                  ys @ [[e1]\<^sub>E] @ [[Tick]\<^sub>E] = flt2cttobs(fl @\<^sub>\<F>\<^sub>\<L> \<langle>(last fl,Tick)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>)
                  \<and> flt2goodAcceptance fl p \<and> flt2goodTock fl 
                  \<and> (\<exists>x. FLTick0 Tick x \<and> FL1 (x \<union> {fl\<^sub>0. fl\<^sub>0 \<le>\<^sub>\<F>\<^sub>\<L> (fl @\<^sub>\<F>\<^sub>\<L> \<langle>(last fl,Tick)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>)}) 
                      \<and> {flt2cttobs fl\<^sub>0 |fl\<^sub>0. fl\<^sub>0 \<in> x} \<subseteq> P \<and> fl \<in> x)"
              apply auto using FL1_extends_strong_less_eq_fltrace_last_bullet last_fl 
            by fastforce
         then have "
                  ys @ [[e1]\<^sub>E] @ [[Tick]\<^sub>E] = flt2cttobs(fl @\<^sub>\<F>\<^sub>\<L> \<langle>(last fl,Tick)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>)
                  \<and> flt2goodAcceptance fl p \<and> flt2goodTock fl 
                  \<and> (\<exists>x. FLTick0 Tick (x \<union> {fl\<^sub>0. fl\<^sub>0 \<le>\<^sub>\<F>\<^sub>\<L> (fl @\<^sub>\<F>\<^sub>\<L> \<langle>(last fl,Tick)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>)}) 
                      \<and> FL1 (x \<union> {fl\<^sub>0. fl\<^sub>0 \<le>\<^sub>\<F>\<^sub>\<L> (fl @\<^sub>\<F>\<^sub>\<L> \<langle>(last fl,Tick)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>)}) 
                      \<and> {flt2cttobs fl\<^sub>0 |fl\<^sub>0. fl\<^sub>0 \<in> x} \<subseteq> P \<and> fl \<in> x)"
          apply auto using FL0_Tick_extends_strong_less_eq_fltrace_last_bullet last_fl Tick_not_in_events_fl
            by blast
         then have "
                  ys @ [[e1]\<^sub>E] @ [[Tick]\<^sub>E] = flt2cttobs(fl @\<^sub>\<F>\<^sub>\<L> \<langle>(last fl,Tick)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>)
                  \<and> flt2goodAcceptance fl p \<and> flt2goodTock fl 
                  \<and> (\<exists>x. FLTick0 Tick (x \<union> {fl\<^sub>0. fl\<^sub>0 \<le>\<^sub>\<F>\<^sub>\<L> (fl @\<^sub>\<F>\<^sub>\<L> \<langle>(last fl,Tick)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>)}) 
                      \<and> FL1 (x \<union> {fl\<^sub>0. fl\<^sub>0 \<le>\<^sub>\<F>\<^sub>\<L> (fl @\<^sub>\<F>\<^sub>\<L> \<langle>(last fl,Tick)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>)}) 
                      \<and> {flt2cttobs fl\<^sub>0 |fl\<^sub>0. fl\<^sub>0 \<in> (x \<union> {fl\<^sub>0. fl\<^sub>0 \<le>\<^sub>\<F>\<^sub>\<L> (fl @\<^sub>\<F>\<^sub>\<L> \<langle>(last fl,Tick)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>)})} \<subseteq> P \<and> fl \<in> x)"  
           using flt2cttobs_strongFL_subset 
           by (smt Un_iff mem_Collect_eq subset_iff)
         then have "
                  ys @ [[e1]\<^sub>E] @ [[Tick]\<^sub>E] = flt2cttobs(fl @\<^sub>\<F>\<^sub>\<L> \<langle>(last fl,Tick)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>)
                  \<and> flt2goodAcceptance fl p \<and> flt2goodTock fl 
                  \<and> (\<exists>x. FLTick0 Tick (x \<union> {fl\<^sub>0. fl\<^sub>0 \<le>\<^sub>\<F>\<^sub>\<L> (fl @\<^sub>\<F>\<^sub>\<L> \<langle>(last fl,Tick)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>)}) 
                      \<and> FL1 (x \<union> {fl\<^sub>0. fl\<^sub>0 \<le>\<^sub>\<F>\<^sub>\<L> (fl @\<^sub>\<F>\<^sub>\<L> \<langle>(last fl,Tick)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>)}) 
                      \<and> {flt2cttobs fl\<^sub>0 |fl\<^sub>0. fl\<^sub>0 \<in> (x \<union> {fl\<^sub>0. fl\<^sub>0 \<le>\<^sub>\<F>\<^sub>\<L> (fl @\<^sub>\<F>\<^sub>\<L> \<langle>(last fl,Tick)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>)})} \<subseteq> P 
                      \<and> fl \<in> x
                      \<and> fl @\<^sub>\<F>\<^sub>\<L> \<langle>(last fl,Tick)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L> \<in> (x \<union> {fl\<^sub>0. fl\<^sub>0 \<le>\<^sub>\<F>\<^sub>\<L> (fl @\<^sub>\<F>\<^sub>\<L> \<langle>(last fl,Tick)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>)}))"
            by (simp add: strong_less_eq_fltrace_refl)  
         then have "
                  ys @ [[e1]\<^sub>E] @ [[Tick]\<^sub>E] = flt2cttobs(fl @\<^sub>\<F>\<^sub>\<L> \<langle>(last fl,Tick)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>)
                  \<and> flt2goodAcceptance fl p \<and> flt2goodTock fl 
                  \<and> (\<exists>z. FLTick0 Tick z \<and> FL1 z 
                      \<and> {flt2cttobs fl\<^sub>0 |fl\<^sub>0. fl\<^sub>0 \<in> z} \<subseteq> P 
                      \<and> fl @\<^sub>\<F>\<^sub>\<L> \<langle>(last fl,Tick)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L> \<in> z)"
           by blast
         then have "
                  ys @ [[e1]\<^sub>E] @ [[Tick]\<^sub>E] = flt2cttobs(fl @\<^sub>\<F>\<^sub>\<L> \<langle>(last fl,Tick)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>)
                  \<and> flt2goodAcceptance fl p \<and> flt2goodTock fl 
                  \<and> flt2goodTock (fl @\<^sub>\<F>\<^sub>\<L> \<langle>(last fl,Tick)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>)
                  \<and> (\<exists>z. FLTick0 Tick z \<and> FL1 z 
                      \<and> {flt2cttobs fl\<^sub>0 |fl\<^sub>0. fl\<^sub>0 \<in> z} \<subseteq> P 
                      \<and> fl @\<^sub>\<F>\<^sub>\<L> \<langle>(last fl,Tick)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L> \<in> z)"
           using last_fl flt2goodTock_extend_consFL_last_fl_bullet
           by blast
         then have "
                  ys @ [[e1]\<^sub>E] @ [[Tick]\<^sub>E] = flt2cttobs(fl @\<^sub>\<F>\<^sub>\<L> \<langle>(last fl,Tick)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>)
                  \<and> flt2goodAcceptance fl p 
                  \<and> flt2goodAcceptance (fl @\<^sub>\<F>\<^sub>\<L> \<langle>(last fl,Tick)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>) p
                  \<and> flt2goodTock fl 
                  \<and> flt2goodTock (fl @\<^sub>\<F>\<^sub>\<L> \<langle>(last fl,Tick)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>)
                  \<and> (\<exists>z. FLTick0 Tick z \<and> FL1 z 
                      \<and> {flt2cttobs fl\<^sub>0 |fl\<^sub>0. fl\<^sub>0 \<in> z} \<subseteq> P 
                      \<and> fl @\<^sub>\<F>\<^sub>\<L> \<langle>(last fl,Tick)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L> \<in> z)"
           using flt2goodAcceptance_extend_consFL_last_fl_bullet_maximal_pri
           by (metis (no_types, lifting) acceptance_event acceptance_set append_self_conv bullet_right_zero2 butlast_last_cons2_FL fl_cons_acceptance_consFL fl_e3 flt2cttobs.simps(2) flt2cttobs_acceptance_cons_eq_list_cons last_fl not_Cons_self2 tick_Max)
         then have "
                  \<exists>fl. ys @ [[e1]\<^sub>E] @ [[Tick]\<^sub>E] = flt2cttobs(fl)
                  \<and> flt2goodAcceptance fl p \<and> flt2goodTock fl 
                  \<and> (\<exists>z. FLTick0 Tick z \<and> FL1 z \<and> {flt2cttobs fl\<^sub>0 |fl\<^sub>0. fl\<^sub>0 \<in> z} \<subseteq> P \<and> fl \<in> z)"
           by blast
         then show ?thesis using Tick e1 e2 by auto
        qed
      next
        case (Ref r2)
        have Tick_in_r2:"Tick \<in> r2"
          using CT4_healthy CTRMax_CT4_Tick CTRMax_healthy Ref snoc.prems(1) by blast
        then have "ys @ [[e1]\<^sub>E] @ [[r2]\<^sub>R] \<in> P"
          using e1 Ref yys.prems(2) by auto
        then have "[Tick]\<^sub>E \<notin> set (ys @ [[e1]\<^sub>E])" 
          using CTwf_healthy CTwf_concat_prefix_of_ref_set_no_Tick
          using e1 Ref
          by (metis fl ys_e1_x)
        then have Tick_not_in_events_fl: "Tick \<notin> events fl"
          by (simp add: event_not_in_set_of_flt2cttobs_imp_not_in_events fl)
       (* have flt2cttobs_strongFL_subset:"{flt2cttobs fl\<^sub>0|fl\<^sub>0. fl\<^sub>0 \<le>\<^sub>\<F>\<^sub>\<L> (fl @\<^sub>\<F>\<^sub>\<L> \<langle>[{x. x \<notin> r2}]\<^sub>\<F>\<^sub>\<L>\<rangle>\<^sub>\<F>\<^sub>\<L>)} \<subseteq> P"
            apply auto
          using strong_less_eq_fltrace_imp_flt2cttobs_ctt
          sledgehammer[debug=true]
          by (metis CT1c_def CT1c_healthy Collect_cong Ref e1 fl flt2cttobs_fl_acceptance last_snoc mem_Collect_eq snoc_eq_iff_butlast subsetI subset_iff yys.prems(2))
        *)
        from fl have fl_e3: "ys @ [[e1]\<^sub>E] @ [[r2]\<^sub>R] = flt2cttobs fl @ [[r2]\<^sub>R]
                  \<and> flt2goodAcceptance fl p \<and> flt2goodTock fl \<and> (\<exists>x. FLTick0 Tick x \<and> FL1 x \<and> {flt2cttobs fl\<^sub>0 |fl\<^sub>0. fl\<^sub>0 \<in> x} \<subseteq> P \<and> fl \<in> x)"
          using ys_e1_x by auto
        also have "... =
                  (ys @ [[e1]\<^sub>E] @ [[r2]\<^sub>R] = flt2cttobs(fl @\<^sub>\<F>\<^sub>\<L> \<langle>[{x. x \<notin> r2} - {Tick}]\<^sub>\<F>\<^sub>\<L>\<rangle>\<^sub>\<F>\<^sub>\<L>)
                  \<and> flt2goodAcceptance fl p \<and> flt2goodTock fl \<and> (\<exists>x. FLTick0 Tick x \<and> FL1 x \<and> {flt2cttobs fl\<^sub>0 |fl\<^sub>0. fl\<^sub>0 \<in> x} \<subseteq> P \<and> fl \<in> x))"
          proof -
              from fl have "ys @ [[e1]\<^sub>E] = flt2cttobs fl"
                by auto
              then have "List.last(flt2cttobs fl) = [e1]\<^sub>E"
                by (metis last_snoc)
              then have "flt2cttobs fl @ [[r2]\<^sub>R] = flt2cttobs(fl @\<^sub>\<F>\<^sub>\<L> \<langle>[{x. x \<notin> r2} - {Tick}]\<^sub>\<F>\<^sub>\<L>\<rangle>\<^sub>\<F>\<^sub>\<L>)"
                using fl last_fl flt2cttobs_fl_acceptance Tick_in_r2
              proof -
                have "flt2cttobs fl \<noteq> []"
                  by (metis (no_types) append_is_Nil_conv fl not_Cons_self2)
                then show ?thesis
                  by (simp add: Tick_in_r2 \<open>List.last (flt2cttobs fl) = [e1]\<^sub>E\<close> fl flt2cttobs_fl_acceptance)
                qed
              then show ?thesis using calculation by auto
            qed
         finally have "
                  ys @ [[e1]\<^sub>E] @ [[r2]\<^sub>R] = flt2cttobs(fl @\<^sub>\<F>\<^sub>\<L> \<langle>[{x. x \<notin> r2} - {Tick}]\<^sub>\<F>\<^sub>\<L>\<rangle>\<^sub>\<F>\<^sub>\<L>)
                  \<and> flt2goodAcceptance fl p \<and> flt2goodTock fl 
                  \<and> (\<exists>x. FLTick0 Tick x \<and> FL1 (x \<union> {fl\<^sub>0. fl\<^sub>0 \<le>\<^sub>\<F>\<^sub>\<L> (fl @\<^sub>\<F>\<^sub>\<L> \<langle>[{x. x \<notin> r2} - {Tick}]\<^sub>\<F>\<^sub>\<L>\<rangle>\<^sub>\<F>\<^sub>\<L>)}) 
                      \<and> {flt2cttobs fl\<^sub>0 |fl\<^sub>0. fl\<^sub>0 \<in> x} \<subseteq> P \<and> fl \<in> x)"
              apply auto using FL1_extends_strong_less_eq_fltrace_acceptance last_fl 
           by fastforce 
         then have "
                  ys @ [[e1]\<^sub>E] @ [[r2]\<^sub>R] = flt2cttobs(fl @\<^sub>\<F>\<^sub>\<L> \<langle>[{x. x \<notin> r2} - {Tick}]\<^sub>\<F>\<^sub>\<L>\<rangle>\<^sub>\<F>\<^sub>\<L>)
                  \<and> flt2goodAcceptance fl p \<and> flt2goodTock fl 
                  \<and> (\<exists>x. FLTick0 Tick (x \<union> {fl\<^sub>0. fl\<^sub>0 \<le>\<^sub>\<F>\<^sub>\<L> (fl @\<^sub>\<F>\<^sub>\<L> \<langle>[{x. x \<notin> r2} - {Tick}]\<^sub>\<F>\<^sub>\<L>\<rangle>\<^sub>\<F>\<^sub>\<L>)})
                      \<and> FL1 (x \<union> {fl\<^sub>0. fl\<^sub>0 \<le>\<^sub>\<F>\<^sub>\<L> (fl @\<^sub>\<F>\<^sub>\<L> \<langle>[{x. x \<notin> r2}- {Tick}]\<^sub>\<F>\<^sub>\<L>\<rangle>\<^sub>\<F>\<^sub>\<L>)}) 
                      \<and> {flt2cttobs fl\<^sub>0 |fl\<^sub>0. fl\<^sub>0 \<in> x} \<subseteq> P \<and> fl \<in> x)"
            apply auto using FL0Tick_extends_strong_less_eq_fltrace_acceptance last_fl Tick_in_r2 Tick_not_in_events_fl
           by (smt Collect_cong Diff_empty Diff_insert0 FLTick0_def Un_iff amember.simps(2) mem_Collect_eq tickWF_concatFL_acceptance_imp tickWF_prefix_imp)
         then have "
                  ys @ [[e1]\<^sub>E] @ [[r2]\<^sub>R] = flt2cttobs(fl @\<^sub>\<F>\<^sub>\<L> \<langle>[{x. x \<notin> r2} - {Tick}]\<^sub>\<F>\<^sub>\<L>\<rangle>\<^sub>\<F>\<^sub>\<L>)
                  \<and> flt2goodAcceptance fl p \<and> flt2goodTock fl 
                  \<and> (\<exists>x. FLTick0 Tick (x \<union> {fl\<^sub>0. fl\<^sub>0 \<le>\<^sub>\<F>\<^sub>\<L> (fl @\<^sub>\<F>\<^sub>\<L> \<langle>[{x. x \<notin> r2} - {Tick}]\<^sub>\<F>\<^sub>\<L>\<rangle>\<^sub>\<F>\<^sub>\<L>)})
                      \<and> FL1 (x \<union> {fl\<^sub>0. fl\<^sub>0 \<le>\<^sub>\<F>\<^sub>\<L> (fl @\<^sub>\<F>\<^sub>\<L> \<langle>[{x. x \<notin> r2} - {Tick}]\<^sub>\<F>\<^sub>\<L>\<rangle>\<^sub>\<F>\<^sub>\<L>)}) 
                      \<and> {flt2cttobs fl\<^sub>0 |fl\<^sub>0. fl\<^sub>0 \<in> (x \<union> {fl\<^sub>0. fl\<^sub>0 \<le>\<^sub>\<F>\<^sub>\<L> (fl @\<^sub>\<F>\<^sub>\<L> \<langle>[{x. x \<notin> r2} - {Tick}]\<^sub>\<F>\<^sub>\<L>\<rangle>\<^sub>\<F>\<^sub>\<L>)})} \<subseteq> P \<and> fl \<in> x)"  
         proof -
           have
            "{flt2cttobs fl\<^sub>0|fl\<^sub>0. fl\<^sub>0 \<le>\<^sub>\<F>\<^sub>\<L> (fl @\<^sub>\<F>\<^sub>\<L> \<langle>[{x. x \<notin> r2} - {Tick}]\<^sub>\<F>\<^sub>\<L>\<rangle>\<^sub>\<F>\<^sub>\<L>)} \<subseteq> P"
            apply auto
            using strong_less_eq_fltrace_imp_flt2cttobs_ctt
            by (metis (no_types, lifting) CT1c_def CT1c_healthy Ref \<open>ys @ [[e1]\<^sub>E] @ [[r2]\<^sub>R] = flt2cttobs (fl @\<^sub>\<F>\<^sub>\<L> \<langle>[{x. x \<notin> r2} - {Tick}]\<^sub>\<F>\<^sub>\<L>\<rangle>\<^sub>\<F>\<^sub>\<L>) \<and> flt2goodAcceptance fl p \<and> flt2goodTock fl \<and> (\<exists>x. FLTick0 Tick x \<and> FL1 (x \<union> {fl\<^sub>0. fl\<^sub>0 \<le>\<^sub>\<F>\<^sub>\<L> fl @\<^sub>\<F>\<^sub>\<L> \<langle>[{x. x \<notin> r2} - {Tick}]\<^sub>\<F>\<^sub>\<L>\<rangle>\<^sub>\<F>\<^sub>\<L>}) \<and> {flt2cttobs fl\<^sub>0 |fl\<^sub>0. fl\<^sub>0 \<in> x} \<subseteq> P \<and> fl \<in> x)\<close> e1 fl fl_e3 yys.prems(2))
          then show ?thesis 
            by (smt Un_iff \<open>ys @ [[e1]\<^sub>E] @ [[r2]\<^sub>R] = flt2cttobs (fl @\<^sub>\<F>\<^sub>\<L> \<langle>[{x. x \<notin> r2} - {Tick}]\<^sub>\<F>\<^sub>\<L>\<rangle>\<^sub>\<F>\<^sub>\<L>) \<and> flt2goodAcceptance fl p \<and> flt2goodTock fl \<and> (\<exists>x. FLTick0 Tick (x \<union> {fl\<^sub>0. fl\<^sub>0 \<le>\<^sub>\<F>\<^sub>\<L> fl @\<^sub>\<F>\<^sub>\<L> \<langle>[{x. x \<notin> r2} - {Tick}]\<^sub>\<F>\<^sub>\<L>\<rangle>\<^sub>\<F>\<^sub>\<L>}) \<and> FL1 (x \<union> {fl\<^sub>0. fl\<^sub>0 \<le>\<^sub>\<F>\<^sub>\<L> fl @\<^sub>\<F>\<^sub>\<L> \<langle>[{x. x \<notin> r2} - {Tick}]\<^sub>\<F>\<^sub>\<L>\<rangle>\<^sub>\<F>\<^sub>\<L>}) \<and> {flt2cttobs fl\<^sub>0 |fl\<^sub>0. fl\<^sub>0 \<in> x} \<subseteq> P \<and> fl \<in> x)\<close> mem_Collect_eq subset_eq)
        qed
        then have "
                  ys @ [[e1]\<^sub>E] @ [[r2]\<^sub>R] = flt2cttobs(fl @\<^sub>\<F>\<^sub>\<L> \<langle>[{x. x \<notin> r2} - {Tick}]\<^sub>\<F>\<^sub>\<L>\<rangle>\<^sub>\<F>\<^sub>\<L>)
                  \<and> flt2goodAcceptance fl p \<and> flt2goodTock fl 
                  \<and> (\<exists>x. FLTick0 Tick (x \<union> {fl\<^sub>0. fl\<^sub>0 \<le>\<^sub>\<F>\<^sub>\<L> (fl @\<^sub>\<F>\<^sub>\<L> \<langle>[{x. x \<notin> r2} - {Tick}]\<^sub>\<F>\<^sub>\<L>\<rangle>\<^sub>\<F>\<^sub>\<L>)})
                      \<and> FL1 (x \<union> {fl\<^sub>0. fl\<^sub>0 \<le>\<^sub>\<F>\<^sub>\<L> (fl @\<^sub>\<F>\<^sub>\<L> \<langle>[{x. x \<notin> r2} - {Tick}]\<^sub>\<F>\<^sub>\<L>\<rangle>\<^sub>\<F>\<^sub>\<L>)}) 
                      \<and> {flt2cttobs fl\<^sub>0 |fl\<^sub>0. fl\<^sub>0 \<in> (x \<union> {fl\<^sub>0. fl\<^sub>0 \<le>\<^sub>\<F>\<^sub>\<L> (fl @\<^sub>\<F>\<^sub>\<L> \<langle>[{x. x \<notin> r2} - {Tick}]\<^sub>\<F>\<^sub>\<L>\<rangle>\<^sub>\<F>\<^sub>\<L>)})} \<subseteq> P 
                      \<and> fl \<in> x
                      \<and> (fl @\<^sub>\<F>\<^sub>\<L> \<langle>[{x. x \<notin> r2} - {Tick}]\<^sub>\<F>\<^sub>\<L>\<rangle>\<^sub>\<F>\<^sub>\<L>) \<in> (x \<union> {fl\<^sub>0. fl\<^sub>0 \<le>\<^sub>\<F>\<^sub>\<L> (fl @\<^sub>\<F>\<^sub>\<L> \<langle>[{x. x \<notin> r2} - {Tick}]\<^sub>\<F>\<^sub>\<L>\<rangle>\<^sub>\<F>\<^sub>\<L>)}))"  
         by (simp add: strong_less_eq_fltrace_refl)  
        then have "
                  ys @ [[e1]\<^sub>E] @ [[r2]\<^sub>R] = flt2cttobs(fl @\<^sub>\<F>\<^sub>\<L> \<langle>[{x. x \<notin> r2} - {Tick}]\<^sub>\<F>\<^sub>\<L>\<rangle>\<^sub>\<F>\<^sub>\<L>)
                  \<and> flt2goodAcceptance fl p \<and> flt2goodTock fl 
                  \<and> (\<exists>z. FLTick0 Tick z \<and> FL1 z 
                      \<and> {flt2cttobs fl\<^sub>0 |fl\<^sub>0. fl\<^sub>0 \<in> z} \<subseteq> P 
                      \<and> fl @\<^sub>\<F>\<^sub>\<L> \<langle>[{x. x \<notin> r2} - {Tick}]\<^sub>\<F>\<^sub>\<L>\<rangle>\<^sub>\<F>\<^sub>\<L> \<in> z)"
          by blast
        then have "
                  ys @ [[e1]\<^sub>E] @ [[r2]\<^sub>R] = flt2cttobs(fl @\<^sub>\<F>\<^sub>\<L> \<langle>[{x. x \<notin> r2} - {Tick}]\<^sub>\<F>\<^sub>\<L>\<rangle>\<^sub>\<F>\<^sub>\<L>)
                  \<and> flt2goodAcceptance fl p \<and> flt2goodTock fl
                  \<and> flt2goodTock (fl @\<^sub>\<F>\<^sub>\<L> \<langle>[{x. x \<notin> r2} - {Tick}]\<^sub>\<F>\<^sub>\<L>\<rangle>\<^sub>\<F>\<^sub>\<L>) 
                  \<and> (\<exists>z. FLTick0 Tick z \<and> FL1 z 
                      \<and> {flt2cttobs fl\<^sub>0 |fl\<^sub>0. fl\<^sub>0 \<in> z} \<subseteq> P 
                      \<and> fl @\<^sub>\<F>\<^sub>\<L> \<langle>[{x. x \<notin> r2} - {Tick}]\<^sub>\<F>\<^sub>\<L>\<rangle>\<^sub>\<F>\<^sub>\<L> \<in> z)"
          using flt2goodTock_extend_consFL_acceptance by blast
        then have "
                  \<exists>fl. ys @ [[e1]\<^sub>E] @ [[r2]\<^sub>R] = flt2cttobs(fl)
                  \<and> flt2goodTock fl
                  \<and> (\<exists>z. FLTick0 Tick z \<and> FL1 z 
                      \<and> {flt2cttobs fl\<^sub>0 |fl\<^sub>0. fl\<^sub>0 \<in> z} \<subseteq> P 
                      \<and> fl \<in> z)"
          by blast
        then show ?thesis using Ref e1 by auto
        qed
    qed
  qed
qed


lemma
  shows "(\<exists>Z fl\<^sub>0 fl. prirel p fl Z \<and> Z \<in> fl\<^sub>0 \<and> fl2ctt fl\<^sub>0 \<subseteq> P \<and> flt2cttobs(Z) \<in> P \<and> flt2cttobs(fl) = ar) 
         = 
         (\<exists>zr. prirelRef p ar zr [] P \<and> zr \<in> P)"
  apply auto
  oops


  
lemma
  "(\<exists>Z fl. prirel p fl Z \<and> Z \<in> fl\<^sub>0 \<and> flt2cttobs(Z) \<in> P \<and> x = flt2cttobs fl)
   =
   (\<exists>Z fl. prirel p fl Z \<and> Z \<in> fl\<^sub>0 \<and> flt2cttobs(Z) \<in> P \<and> flt2goodTock fl \<and> x = flt2cttobs fl)"
  oops



(* FIXME: Change flt2goodS to accommodate tickWF *)
fun flt2goodS :: "('e cttevent) partialorder \<Rightarrow> ('e cttevent) fltrace \<Rightarrow> bool" where
"flt2goodS p \<langle>A\<rangle>\<^sub>\<F>\<^sub>\<L> = True" |
"flt2goodS p (A #\<^sub>\<F>\<^sub>\<L> fl) = 
  ((case event(A) of  Tock \<Rightarrow> Tock \<in>\<^sub>\<F>\<^sub>\<L> acceptance(A)
                    | Tick \<Rightarrow> acceptance(A) = \<bullet> 
                    | Event a \<Rightarrow> Event a \<in>\<^sub>\<F>\<^sub>\<L> acceptance(A) 
                                 \<and> (acceptance(A) = [{a. a \<in>\<^sub>\<F>\<^sub>\<L> acceptance(A) \<and> \<not>(\<exists>b. b\<in>\<^sub>\<F>\<^sub>\<L>acceptance(A) \<and> a <\<^sup>*p b)}]\<^sub>\<F>\<^sub>\<L>)) \<and> (flt2goodS p fl))" 

lemma flt2cttobs_flt2goodTock_less_eq_exists:
  assumes "prirel p fl Z"
  shows "flt2goodS p fl"
  nitpick

(*
lemma flt2cttobs_exists_flt2goodS_for_cttWF_CT3_trace:
  assumes "cttWF fl" "CT3_trace fl"
  shows "\<exists>zr. (flt2cttobs zr) = fl \<and> flt2goodS p zr"
  using assms
proof (induct fl rule:cttWF.induct, auto)
  show "\<exists>zr. flt2cttobs zr = [] \<and> flt2goodS p zr"
    by (intro exI[where x="\<langle>\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>"], auto)
next
  fix X
  show "\<exists>zr. flt2cttobs zr = [[X]\<^sub>R] \<and> flt2goodS p zr"
    by (intro exI[where x="\<langle>[{x. x \<notin> X}]\<^sub>\<F>\<^sub>\<L>\<rangle>\<^sub>\<F>\<^sub>\<L>"], auto)
next
  show "\<exists>zr. flt2cttobs zr = [[Tick]\<^sub>E] \<and> flt2goodS p zr"
    by (intro exI[where x="\<langle>(\<bullet>,Tick)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>"], auto)
next
  fix e \<sigma>
  assume hyp:"(CT3_trace \<sigma> \<Longrightarrow> \<exists>zr. flt2cttobs zr = \<sigma> \<and> flt2goodS p zr)"
  assume assm1:"cttWF \<sigma>"
  assume assm2:"CT3_trace ([Event e]\<^sub>E # \<sigma>)"
  show "\<exists>zr. flt2cttobs zr = [Event e]\<^sub>E # \<sigma> \<and> flt2goodS p zr"
  proof -
    from assm2 have "CT3_trace \<sigma>"
      using CT3_trace_cons_imp_cons by blast
    then have "\<exists>zr. flt2cttobs zr = \<sigma> \<and> flt2goodS p zr"
      using hyp by auto
    then have "\<exists>zr. flt2cttobs(\<langle>([{Event e}]\<^sub>\<F>\<^sub>\<L>,Event e)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>) @ flt2cttobs zr = [Event e]\<^sub>E # \<sigma> \<and> flt2goodS p zr"
      by auto
    then have "\<exists>zr. flt2cttobs(\<langle>([{Event e}]\<^sub>\<F>\<^sub>\<L>,Event e)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L> &\<^sub>\<F>\<^sub>\<L> zr) = [Event e]\<^sub>E # \<sigma> \<and> flt2goodS p (\<langle>([{Event e}]\<^sub>\<F>\<^sub>\<L>,Event e)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L> &\<^sub>\<F>\<^sub>\<L> zr)"
      by auto
    then show ?thesis by blast
  qed
next
  fix X::"'a cttevent set"
  fix zr::"'a cttevent fltrace"
  assume assm1:"cttWF (flt2cttobs zr)"
  assume assm2:"Tock \<notin> X"
  assume assm3:"CT3_trace (flt2cttobs zr)"
  assume assm4:"flt2goodS p zr"
  show "\<exists>zra. flt2cttobs zra = [X]\<^sub>R # [Tock]\<^sub>E # flt2cttobs zr \<and> flt2goodS p zra"
  proof -
    have "\<exists>zra. flt2cttobs zra = flt2cttobs zr \<and> flt2goodS p zra"
      using assm4 by auto
    then have "\<exists>zra. flt2cttobs(\<langle>([{x. x \<notin> X}]\<^sub>\<F>\<^sub>\<L>,Tock)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>) @ flt2cttobs zra = [X]\<^sub>R # [Tock]\<^sub>E # flt2cttobs zr \<and> flt2goodS p zra"
      using assm2 by auto
    then have "\<exists>zra. flt2cttobs(\<langle>([{x. x \<notin> X}]\<^sub>\<F>\<^sub>\<L>,Tock)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L> &\<^sub>\<F>\<^sub>\<L> zra) = [X]\<^sub>R # [Tock]\<^sub>E # flt2cttobs zr \<and> flt2goodS p (\<langle>([{x. x \<notin> X}]\<^sub>\<F>\<^sub>\<L>,Tock)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L> &\<^sub>\<F>\<^sub>\<L> zra)"
      using assm2 by auto
    then show ?thesis by blast
  qed
qed*)



lemma 
 "{flt2cttobs fl|fl. (\<exists>zr. prirelRef p (flt2cttobs(fl)) zr [] P \<and> zr \<in> P)}
  =
  {ar|ar. (\<exists>zr. prirelRef p ar zr [] P \<and> zr \<in> P)}"
  apply auto
  oops

lemma xp:
  assumes "prirelRef p x zr s P"
    shows "\<exists>fl. x = flt2cttobs fl \<and> (\<exists>zr. prirelRef p (flt2cttobs fl) zr s P)"
  using assms nitpick apply (induct p x zr s P rule:prirelRef.induct, auto)
  
      apply (metis flt2cttobs.simps(1) prirelRef.simps(1))
   apply (metis CT3_trace.simps(2) cttWF.simps(2) flt2cttobs_exists_flt2goodS_for_cttWF_CT3_trace insert_Nil prirelRef.simps(2))
sledgehammer
  sorry

lemma
  assumes "prirelRef p x zr [] P"
          "zr \<in> P"
    shows "\<exists>fl. x = flt2cttobs fl \<and> (\<exists>zr. prirelRef p (flt2cttobs fl) zr [] P \<and> zr \<in> P)"
  using assms using xp apply (induct p x zr _ P rule:prirelRef.induct, auto)
  oops

lemma FL1_ctt2fl:
  shows "FL1 (ctt2fl(P))"
  unfolding FL1_def ctt2fl_def by blast

lemma FL2_ctt2fl:
  "FL2 (ctt2fl(P))"
  unfolding FL2_def ctt2fl_def apply auto
  (* Simplifying what needs to be proved *)
  apply (case_tac A, auto)
  apply (case_tac "last \<beta> \<noteq> \<bullet>", auto)
   apply (metis concat_FL_last_not_bullet_absorb)
  (* Requires property on P, namely CT2, to show this now. *)
  oops

lemma
  shows "(\<exists>Z fl fl\<^sub>0. FL1 fl\<^sub>0 \<and> prirel p fl Z \<and> Z \<in> fl\<^sub>0 \<and> fl2ctt fl\<^sub>0 \<subseteq> P \<and> flt2cttobs(Z) \<in> P \<and> flt2cttobs(fl) = ar) 
         = 
         (\<exists>zr. prirelRef p ar zr [] P \<and> zr \<in> P)"
  nitpick

lemma prirel_same_length:
  assumes "prirel p fl Y"
  shows "length fl = length Y"
  using assms by (induct fl Y rule:prirel.induct, auto)

lemma
  assumes "prirel p (xs &\<^sub>\<F>\<^sub>\<L> \<langle>x\<rangle>\<^sub>\<F>\<^sub>\<L>) (ys &\<^sub>\<F>\<^sub>\<L> \<langle>y\<rangle>\<^sub>\<F>\<^sub>\<L>)" "length xs = length ys"
  shows "prirel p xs ys"
  nitpick
  oops

fun goodPriRels :: "'a cttobs list \<Rightarrow> 'a cttobs list \<Rightarrow> bool" where
"goodPriRels [] [] = True" |
"goodPriRels [[R]\<^sub>R] [[S]\<^sub>R] = True" |
"goodPriRels (x # xs) (y # ys) = (goodPriRels xs ys)" |
"goodPriRels xs ys = False"

lemma goodTocks_goodPriRels:
  assumes "flt2goodTock xs" "flt2goodTock ys"
          "prirel p xs ys"
    shows "goodPriRels (flt2cttobs xs) (flt2cttobs ys)"
  using assms apply(induct p xs ys rule:prirel.induct, auto)
  by (case_tac A, auto)+

lemma
  assumes "flt2goodTock xs" "flt2goodTock ys" "prirel p xs ys"
  shows "(flt2cttobs xs) \<le>\<^sub>C (flt2cttobs ys)"
  nitpick

lemma 
  assumes "prirel p fl Y" "flt2goodTock Y"
  shows "flt2goodTock fl"
  using assms nitpick

lemma
  assumes "cttWF (flt2cttobs xs)"
  shows "cttWF ((flt2cttobs xs) @ (flt2cttobs \<langle>x,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>))"
  nitpick

  

lemma
  assumes "size xs = size ys"
    shows "(prirelRef p xs ys [] P \<and> prirelRef p x y ys P) = prirelRef p (xs@x) (ys@y) [] P"
  using assms nitpick[card=4]
  (*apply (induct p xs ys _ P arbitrary:x y rule:prirelRef.induct)
  apply (simp_all)
  sledgehammer[debug=true]
     apply (metis cttWF.elims(2) cttWF.simps(11) cttWF.simps(12) cttWF.simps(13) prirelRef.simps(1) prirelRef.simps(2))
 
    apply auto
  apply (induct x rule:rev_induct, auto)
  apply (metis append_Nil2 cttWF.elims(2) prirelRef.simps(46))
  sledgehammer[debug=true]
  thm prirelRef.induct*)

(*
lemma
  assumes "prirelRef p xs ys [] P" "size xs = size ys"
          "prirelRef p x y ys P" "cttWF (xs@x)" "cttWF (ys@y)"
    shows "prirelRef p (xs@x) (ys@y) [] P"
  using assms
proof (induct p xs ys "[]::'a cttobs list" P arbitrary:x y rule:prirelRef.induct, simp_all)
  fix pa S R xa ya Q
  assume "prirelref pa S = R"
         "prirelRef pa xa ya [[S]\<^sub>R] Q"
         "cttWF ([R]\<^sub>R # xa)"
         "cttWF ([S]\<^sub>R # ya)"
  then show "prirelRef pa ([R]\<^sub>R # xa) ([S]\<^sub>R # ya) [] Q"
    apply auto
    apply (case_tac xa, auto)
     apply (case_tac ya, auto)
    apply (case_tac ya, auto)
    apply (case_tac a, auto, case_tac aa, auto)
     apply (case_tac x1a, auto)
    by (case_tac x1a, auto)
next
  fix pa R aa S zz Q ya xa
  assume "(\<And>y x. [S]\<^sub>R # [Tock]\<^sub>E # zz @ ya @ [[S]\<^sub>R, [Tock]\<^sub>E] = zz @ y \<Longrightarrow>
               prirelRef pa aa zz [] Q \<Longrightarrow> prirelRef pa x y zz Q \<Longrightarrow> cttWF (aa @ x) \<Longrightarrow> cttWF (zz @ y) \<Longrightarrow> prirelRef pa (aa @ x) (zz @ y) [] Q)"
      "R = prirelref pa S \<and> prirelRef pa aa zz [[S]\<^sub>R, [Tock]\<^sub>E] Q"
      "List.length aa = List.length zz"
      "prirelRef pa xa ya ([S]\<^sub>R # [Tock]\<^sub>E # zz) Q"
      "cttWF (aa @ xa)"
      "cttWF (zz @ ya)"
  then show "prirelRef pa (aa @ xa) (zz @ ya) [[S]\<^sub>R, [Tock]\<^sub>E] Q"
    oops

lemma
  assumes "prirelRef p xs ys [] P" "cttWF xs" "cttWF ys" "cttWF x" "cttWF y" "CTwf P" "ys \<in> P" "CT1c P"
          "prirelRef p x y ys P" "cttWF (xs@x)" "cttWF (ys@y)" "(ys@y) \<in> P"
    shows "prirelRef p (xs@x) (ys@y) [] P"
  using assms 
  apply (induct p xs ys "[]::'a cttobs list" P rule:prirelRef.induct)
  apply (simp_all)
(*    apply auto
  apply (metis cttWF.elims(2) cttWF.simps(11) cttWF.simps(12) cttWF.simps(13) prirelRef.simps(2))
sledgehammer[debug=true]
apply (case_tac s, auto)
  apply (induct xs rule:rev_induct, auto)
  apply (induct ys rule:rev_induct, auto)
  apply (case_tac xsa, auto)
  apply (induct ys rule:rev_induct, auto)
   apply (case_tac xsa, auto)
  sledgehammer[debug=true] *)
  (*apply(induct p x y xs P rule:prirelRef.induct)
  apply (simp_all)
  apply auto
     apply (case_tac s, auto)
      apply (metis append_self_conv2 assms(3) cttWF.elims(2) prirelRef.simps(2) prirelRef.simps(46))
  apply (induct ys rule:rev_induct, auto)
  sledgehammer[debug=true]*)
(*  apply (metis cttWF.elims(2) prirelRef.simps(2) prirelRef.simps(28))
  apply (metis cttWF.elims(2) cttWF.simps(11) cttWF.simps(12) cttWF.simps(13) prirelRef.simps(46))
  sledgehammer[debug=true]*)
*)
lemma
  assumes "length xs = length ys" "last ys = \<bullet>"
          "prirel p xs (ys &\<^sub>\<F>\<^sub>\<L> \<langle>y\<rangle>\<^sub>\<F>\<^sub>\<L>)"
        shows "prirel p xs ys"
  oops



lemma flt2cttobs_cons_no_extend_not_flt2goodTock:
  assumes "\<not> flt2goodTock fl"
  shows "flt2cttobs (fl &\<^sub>\<F>\<^sub>\<L> xs) = flt2cttobs(fl)"
  using assms apply (induct fl rule:flt2cttobs.induct, auto)
  by (case_tac A, auto)

lemma flt2cttobs_cons_acceptance_eq_cons:
  assumes "last fl = \<bullet>" "flt2goodTock fl"
  shows "flt2cttobs (fl &\<^sub>\<F>\<^sub>\<L> \<langle>y\<rangle>\<^sub>\<F>\<^sub>\<L>) = flt2cttobs(fl) @ flt2cttobs(\<langle>y\<rangle>\<^sub>\<F>\<^sub>\<L>)"
  using assms by (induct fl rule:flt2cttobs.induct, auto)

lemma prirel_flt2goodTock_tgt_imp_src:
  assumes "prirel p fl Y" "flt2goodTock fl"
  shows "flt2goodTock Y"
  using assms apply (induct p fl Y rule:prirel.induct, auto)
  by (case_tac A, auto, case_tac a, auto)+

(*
lemma
  assumes "prirelRef p (flt2cttobs xs) (flt2cttobs ys) [] P" "flt2goodTock ys" "length ys = length xs"
  shows "flt2goodTock xs"
  using assms apply (induct xs ys rule:ftrace_cons_induct_both_eq_length2, auto)
  apply (simp add: concat_FL_last_not_bullet_absorb)
  sledgehammer[debug=true]
  apply (simp add: concat_FL_last_not_bullet_absorb)
  apply (induct ys rule:flt2cttobs.induct, auto)*)


(* It would be nice to show the following, but the conclusion is stronger
   than necessary to establish the correspondence we want. It may, however,
   be easier to prove depending on the definition of prirelRef. *)

(*
lemma prirelRef_extend_rhs_cttWF:
  assumes "prirelRef p xs ys s P" "cttWF (ys @ [[R]\<^sub>R])"
  shows "prirelRef p xs (ys @ [[R]\<^sub>R]) s P"
  using assms apply (induct p xs ys s P rule:prirelRef.induct, auto)
  by (metis cttWF.simps(10) cttWF.simps(4) cttWF.simps(6) cttevent.exhaust list.exhaust snoc_eq_iff_butlast)+
*)



lemma prirelRef_extend_both_events_non_maximal_cttWF:
  assumes "prirelRef p xs ys s P" "cttWF (xs @ [[e\<^sub>1]\<^sub>E])" "cttWF (ys @ [[e\<^sub>1]\<^sub>E])" "CTwf P"
          "(\<exists>Z. s @ ys @ [[Z]\<^sub>R] \<in> P \<and> e\<^sub>1 \<notin> Z \<and> \<not>(\<exists>b. b \<notin> Z \<and> e\<^sub>1 <\<^sup>*p b))" 
  shows "prirelRef p (xs @ [[e\<^sub>1]\<^sub>E]) (ys @ [[e\<^sub>1]\<^sub>E]) s P"
  using assms apply (induct p xs ys s P rule:prirelRef.induct, auto)
    apply (cases e\<^sub>1, auto)
  using CTwf_cons_end_not_refusal_refusal apply blast
  by (metis append_Nil cttWF.simps(10) cttWF.simps(4) cttWF.simps(6) cttWF_prefix_is_cttWF cttevent.exhaust list.exhaust)+


lemma flt2cttobs_exists_for_cttWF_CT3_trace:
  assumes "cttWF fl" "CT3_trace fl"
  shows "\<exists>zr. (flt2cttobs zr) = fl"
  using assms
proof (induct fl rule:cttWF.induct, auto)
  show "\<exists>zr. flt2cttobs zr = []"
    by (intro exI[where x="\<langle>\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>"], auto)
next
  fix X
  show "\<exists>zr. flt2cttobs zr = [[X]\<^sub>R]"
    by (intro exI[where x="\<langle>[{x. x \<notin> X}]\<^sub>\<F>\<^sub>\<L>\<rangle>\<^sub>\<F>\<^sub>\<L>"], auto)
next
  show "\<exists>zr. flt2cttobs zr = [[Tick]\<^sub>E]"
    by (intro exI[where x="\<langle>(\<bullet>,Tick)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>"], auto)
next
  fix e \<sigma>
  assume hyp:"(CT3_trace \<sigma> \<Longrightarrow> \<exists>zr. flt2cttobs zr = \<sigma>)"
  assume assm1:"cttWF \<sigma>"
  assume assm2:"CT3_trace ([Event e]\<^sub>E # \<sigma>)"
  show "\<exists>zr. flt2cttobs zr = [Event e]\<^sub>E # \<sigma>"
  proof -
    from assm2 have "CT3_trace \<sigma>"
      using CT3_trace_cons_imp_cons by blast
    then have "\<exists>zr. flt2cttobs zr = \<sigma>"
      using hyp by auto
    then have "\<exists>zr. flt2cttobs(\<langle>(\<bullet>,Event e)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>) @ flt2cttobs zr = [Event e]\<^sub>E # \<sigma>"
      by auto
    then have "\<exists>zr. flt2cttobs(\<langle>(\<bullet>,Event e)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L> &\<^sub>\<F>\<^sub>\<L> zr) = [Event e]\<^sub>E # \<sigma>"
      by auto
    then show ?thesis by blast
  qed
next
  fix X::"'a cttevent set"
  fix zr::"'a cttevent fltrace"
  assume assm1:"cttWF (flt2cttobs zr)"
  assume assm2:"Tock \<notin> X"
  assume assm3:"CT3_trace (flt2cttobs zr)"
  show "\<exists>zra. flt2cttobs zra = [X]\<^sub>R # [Tock]\<^sub>E # flt2cttobs zr"
  proof -
    have "\<exists>zra. flt2cttobs zra = flt2cttobs zr"
      by auto
    then have "\<exists>zra. flt2cttobs(\<langle>([{x. x \<notin> X}]\<^sub>\<F>\<^sub>\<L>,Tock)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>) @ flt2cttobs zra = [X]\<^sub>R # [Tock]\<^sub>E # flt2cttobs zr"
      using assm2 by auto
    then have "\<exists>zra. flt2cttobs(\<langle>([{x. x \<notin> X}]\<^sub>\<F>\<^sub>\<L>,Tock)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L> &\<^sub>\<F>\<^sub>\<L> zra) = [X]\<^sub>R # [Tock]\<^sub>E # flt2cttobs zr"
      using assm2 by auto
    then show ?thesis by blast
  qed
qed

lemma tt:
  assumes "prirel p fl Y" "FL1 fl\<^sub>0" "FLTick0 Tick fl\<^sub>0"
          "Y \<in> fl\<^sub>0"
          "fl2ctt fl\<^sub>0 \<subseteq> P"
          "flt2cttobs Y \<in> P" "size (flt2cttobs fl) = size (flt2cttobs Y)"
    shows "prirelRef p (flt2cttobs fl) (flt2cttobs Y) [] P"
  sorry

lemma
  assumes "prirel p fl Y" "FL1 fl\<^sub>0" "FLTick0 Tick fl\<^sub>0"
          "Y \<in> fl\<^sub>0"
          "fl2ctt fl\<^sub>0 \<subseteq> P"
          "flt2cttobs Y \<in> P"
    shows "\<exists>zr. prirelRef p (flt2cttobs fl) zr [] P  \<and> zr \<in> P"
  using tt oops

lemma flt2goodTock_cons_imp_prefix:
  assumes "flt2goodTock (xs &\<^sub>\<F>\<^sub>\<L> ys)"
  shows "flt2goodTock (xs)"
  using assms by(induct xs, auto)

lemma prirel_rhs_tickWF_imp_lhs_tickWF:
  assumes "prirel p xs ys" "tickWF Tick ys"
  shows "tickWF Tick xs"
  using assms apply (induct p xs ys rule:prirel.induct, auto)
  apply (case_tac Z, auto)
            apply (metis amember.elims(2) prirelacc.simps(3))
            apply (case_tac A, auto)
  apply (case_tac A, auto)
  using acceptance_not_bullet_imp_prirelacc event_in_acceptance apply force
    apply (metis amember.elims(3) prirel.simps(1) prirel.simps(3) prirelacc.simps(3) tickWF.elims(2))
  apply (metis (mono_tags, lifting) acceptance.distinct(1) acceptance_not_bullet_imp_prirelacc amember.elims(2) amember.simps(2) mem_Collect_eq prirelacc_acceptances_eq)
  using event_in_acceptance apply force
  using event_in_acceptance apply force
  apply (metis (mono_tags, lifting) amember.simps(1) amember.simps(2) mem_Collect_eq prirelacc_acceptances_eq) 
    using acceptance_not_bullet_imp_prirelacc event_in_acceptance apply force
    using acceptance_not_bullet_imp_prirelacc event_in_acceptance apply force
      apply (case_tac A, auto, case_tac a, auto, case_tac Z, auto, case_tac a, auto)
     apply (case_tac Z, auto, case_tac A, auto, case_tac aa, auto, case_tac x1, auto)
    by (case_tac A, auto, case_tac Z, auto)

(* TODO: Move these to Finite_Linear_Model.thy *)
lemma fltrace_cons_extend_prefix:
  assumes "ys &\<^sub>\<F>\<^sub>\<L> xs \<le> ys &\<^sub>\<F>\<^sub>\<L> zs" "last ys = \<bullet>"
  shows "xs \<le> zs"
  using assms
  apply (induct ys arbitrary: xs zs rule:fltrace_induct, auto)
  apply (metis Finite_Linear_Model.last.simps(1) bullet_left_zero2 concat_FL_last_not_bullet_absorb fltrace_concat2_assoc last_bullet_then_last_cons)
  by (metis FL_concat_equiv fltrace_concat2_assoc last_cons_bullet_iff less_eq_fltrace.simps(3)) 

lemma fltrace_cons_prefix_common:
  assumes "xs \<le> zs" 
  shows "ys &\<^sub>\<F>\<^sub>\<L> xs \<le> ys &\<^sub>\<F>\<^sub>\<L> zs"
  using assms 
  apply (induct ys, auto)
  apply (case_tac x, auto)
  by (simp add: concat_FL_last_not_bullet_absorb)

lemma fltrace_FL1_cons_acceptance_prefix:
  assumes "ys &\<^sub>\<F>\<^sub>\<L> \<langle>y,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L> \<in> P" "FL1 P"
  shows "ys &\<^sub>\<F>\<^sub>\<L> \<langle>acceptance(y)\<rangle>\<^sub>\<F>\<^sub>\<L> \<in> P"
  
proof -
  have "ys &\<^sub>\<F>\<^sub>\<L> \<langle>acceptance(y)\<rangle>\<^sub>\<F>\<^sub>\<L> \<le> ys &\<^sub>\<F>\<^sub>\<L> \<langle>y,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>"
    by (simp add: fltrace_cons_prefix_common)
  then show ?thesis
    using assms
    using FL1_def by blast
qed

lemma prirel_cons_lasts_bullet_cons_bullet_iff:
  assumes "last xs = \<bullet>" "last ys = \<bullet>"
          "prirel p (xs &\<^sub>\<F>\<^sub>\<L> \<langle>x\<rangle>\<^sub>\<F>\<^sub>\<L>) (ys &\<^sub>\<F>\<^sub>\<L> \<langle>y\<rangle>\<^sub>\<F>\<^sub>\<L>)"
        shows "x = \<bullet> \<longleftrightarrow> y = \<bullet>"
  using assms apply(induct p xs ys rule:prirel.induct, auto)
  by (cases x, auto)+

lemma flt2cttobs_is_CT3_trace [simp]:
  "CT3_trace (flt2cttobs xs)"
  apply (induct xs)
   apply (case_tac x, simp)
   apply auto[1]
  apply (case_tac x1a, case_tac y, case_tac a)
   apply auto[1]
   apply (metis CT3_trace.simps(2) CT3_trace.simps(4) neq_Nil_conv)
  apply (case_tac b, auto)
  apply (metis CT3_trace.simps(2) CT3_trace.simps(4) neq_Nil_conv)
  by (metis CT3_trace.simps(2) CT3_trace.simps(4) neq_Nil_conv)

lemma pp:
  assumes "prirel p fl Y" "FL1 fl\<^sub>0" "FLTick0 Tick fl\<^sub>0"
          "Y \<in> fl\<^sub>0"
          "fl2ctt fl\<^sub>0 \<subseteq> P"
          "flt2cttobs Y \<in> P"
          "flt2goodTock fl" "CTwf P"
    shows "prirelRef p (flt2cttobs fl) (flt2cttobs Y) [] P"
  using assms  
proof (induct fl Y rule:ftrace_cons_induct_both_eq_length)
  case 1
  then show ?case using assms(1) prirel_same_length by blast
next
  case (2 x y)
  then show ?case 
    apply (cases y, auto)
       apply (cases x, auto)
     apply (cases x, auto)
    unfolding prirelref_def apply auto
    by (cases x, auto)
next
  case (3 x y xs ys)
  then have prirelRef:"prirelRef p (flt2cttobs xs) (flt2cttobs ys) [] P"
    by (metis (mono_tags, lifting) flt2goodTock_cons_imp_prefix flt2cttobs_extn mem_Collect_eq subset_eq x_le_concat2_FL1 prirel_cons_eq_length_imp_prirel_eq_prefix)
  then show ?case using 3
  proof (cases "flt2goodTock xs")
    case True
    then have "flt2goodTock ys"
      using 3 prirel_cons_eq_length_imp_prirel_eq_prefix prirel_flt2goodTock_tgt_imp_src by blast
    then have flt2_ys_y:"flt2cttobs (ys &\<^sub>\<F>\<^sub>\<L> \<langle>y\<rangle>\<^sub>\<F>\<^sub>\<L>) = flt2cttobs (ys) @ flt2cttobs(\<langle>y\<rangle>\<^sub>\<F>\<^sub>\<L>)"
      using 3 by (simp add: flt2cttobs_cons_acceptance_eq_cons)
    then have "flt2cttobs (ys) @ flt2cttobs(\<langle>y\<rangle>\<^sub>\<F>\<^sub>\<L>) \<in> P"
      using 3 by (simp)
    then show ?thesis using 3
      proof (cases x)
        case xnil:acnil
        then have "y = \<bullet>"
          using prirel_cons_lasts_bullet_cons_bullet_iff
          using "3.hyps"(3) "3.hyps"(4) "3.prems"(1) by blast
        then show ?thesis 
          using prirelRef xnil by auto
        (*  proof (cases y)
            case acnil
            then show ?thesis using 3 prirelRef xnil by auto
          next
            case (acset x2)
            
           (* then obtain yR where yR:"flt2cttobs(\<langle>y\<rangle>\<^sub>\<F>\<^sub>\<L>) = [[yR]\<^sub>R]"
              by simp
            then have "cttWF (flt2cttobs (ys &\<^sub>\<F>\<^sub>\<L> \<langle>y\<rangle>\<^sub>\<F>\<^sub>\<L>))"
              by (meson "3.prems"(4) FLTick0_def assms(3) flt2cttobs_is_cttWF)
            then have "prirelRef p (flt2cttobs xs) ((flt2cttobs ys) @ [[yR]\<^sub>R]) [] P"
              using acset 3 prirelRef xnil flt2_ys_y prirelRef_extend_rhs_cttWF 
              by (metis yR)*)
            then show ?thesis using acset 3 xnil flt2_ys_y prirel_cons_lasts_bullet_cons_bullet_iff by auto
          qed*)
      next
        case (acset x2)
        then obtain yA where yA:"y = [yA]\<^sub>\<F>\<^sub>\<L>"
          using "3.hyps"(3) "3.hyps"(4) "3.prems"(1) prirel_last_bullets_cons_imp by blast
        then have "prirel p \<langle>[x2]\<^sub>\<F>\<^sub>\<L>\<rangle>\<^sub>\<F>\<^sub>\<L> \<langle>[yA]\<^sub>\<F>\<^sub>\<L>\<rangle>\<^sub>\<F>\<^sub>\<L>"
          using "3.hyps"(2) "3.hyps"(3) "3.hyps"(4) "3.prems"(1) acset prirel_cons_eq_length_imp_prirel_acceptances_eq by blast
        then have "prirelref p {x. x \<notin> yA} = {x. x \<notin> x2}"
          by (metis (no_types, lifting) Collect_cong acceptance.distinct(1) amember.simps(2) flt2cttobs.simps(1) prirel.simps(1) prirelacc_eq_prirelref_via_flt2cttobs)
        then obtain xR where xR:"flt2cttobs(\<langle>x\<rangle>\<^sub>\<F>\<^sub>\<L>) = [[xR]\<^sub>R]"
          by (simp add: acset)
        then obtain yR where yR:"flt2cttobs(\<langle>y\<rangle>\<^sub>\<F>\<^sub>\<L>) = [[yR]\<^sub>R] \<and> prirelref p yR = xR"
          using 3 yA
          by (metis (no_types, lifting) \<open>prirel p \<langle>[x2]\<^sub>\<F>\<^sub>\<L>\<rangle>\<^sub>\<F>\<^sub>\<L> \<langle>[yA]\<^sub>\<F>\<^sub>\<L>\<rangle>\<^sub>\<F>\<^sub>\<L>\<close> acceptance.distinct(1) acset flt2cttobs.simps(1) prirel.simps(1) prirelacc_eq_prirelref_via_flt2cttobs)

        have "cttWF (flt2cttobs (ys &\<^sub>\<F>\<^sub>\<L> \<langle>y\<rangle>\<^sub>\<F>\<^sub>\<L>))"
          by (meson "3.prems"(4) FLTick0_def assms(3) flt2cttobs_is_cttWF)
        then have "cttWF ((flt2cttobs ys) @ [[yR]\<^sub>R])"
          by (metis flt2_ys_y yR)
        then have "prirelRef p ((flt2cttobs xs) @ [[xR]\<^sub>R]) ((flt2cttobs ys) @ [[yR]\<^sub>R]) [] P"
          using prirelRef_extend_both_refusal_cttWF
          using prirelRef yR by blast
        then show ?thesis
          using "3.hyps"(3) True flt2_ys_y flt2cttobs_cons_acceptance_eq_cons xR yR by fastforce
      qed
  next
    case False
    then have flt2_xsx:"flt2cttobs (xs &\<^sub>\<F>\<^sub>\<L> \<langle>x\<rangle>\<^sub>\<F>\<^sub>\<L>) = flt2cttobs (xs)"
      by (simp add: flt2cttobs_cons_no_extend_not_flt2goodTock)
    then have "y = \<bullet>"
      using prirel_cons_lasts_bullet_cons_bullet_iff
      using "3.prems"(7) False flt2goodTock_cons_imp_prefix by blast
    then show ?thesis
      by (simp add: flt2_xsx prirelRef)
   (* proof (cases y)
      case acnil
      then show ?thesis using 3 prirelRef flt2_xsx by auto
    next
      case (acset x2)
      then obtain yR where yR:"flt2cttobs(\<langle>y\<rangle>\<^sub>\<F>\<^sub>\<L>) = [[yR]\<^sub>R]"
        by simp
      then have cttWF_ys_y:"cttWF (flt2cttobs (ys &\<^sub>\<F>\<^sub>\<L> \<langle>y\<rangle>\<^sub>\<F>\<^sub>\<L>))"
        by (meson "3.prems"(4) FLTick0_def assms(3) flt2cttobs_is_cttWF)
      then show ?thesis
      proof (cases "flt2goodTock ys")
        case True
        then have "prirelRef p (flt2cttobs xs) ((flt2cttobs ys) @ [[yR]\<^sub>R]) [] P"
          using acset 3 prirelRef flt2_xsx prirelRef_extend_rhs_cttWF
          by (metis cttWF_ys_y flt2cttobs_cons_acceptance_eq_cons yR)
        then show ?thesis
          using "3.hyps"(4) True flt2_xsx flt2cttobs_cons_acceptance_eq_cons yR by fastforce
      next
        case False
        then have "flt2cttobs (ys &\<^sub>\<F>\<^sub>\<L> \<langle>y\<rangle>\<^sub>\<F>\<^sub>\<L>) = flt2cttobs (ys)"
          by (simp add: flt2cttobs_cons_no_extend_not_flt2goodTock)
        then show ?thesis
          by (simp add: flt2_xsx prirelRef)
      qed
    qed*)
  qed
next
  case (4 x y xs ys)
  then have xs_is_flt2goodTock:"flt2goodTock xs"
    using flt2goodTock_cons_imp_prefix by blast
  then have ys_is_flt2goodTock:"flt2goodTock ys"
    using "4.hyps"(2) "4.prems"(1) prirel_cons_eq_length_imp prirel_flt2goodTock_tgt_imp_src by blast
  then have prirelRef:"prirelRef p (flt2cttobs xs) (flt2cttobs ys) [] P"
    using prirel_cons_eq_length_imp 4
    by (metis (mono_tags, lifting) xs_is_flt2goodTock flt2cttobs_extn mem_Collect_eq subset_eq x_le_concat2_FL1)
  then have "prirel p \<langle>x,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L> \<langle>y,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>"
    using "4.hyps"(2) "4.hyps"(3) "4.prems"(1) prirel_cons_eq_length_imp_prirel_acceptances by blast
  then have "goodPriRels (flt2cttobs xs) (flt2cttobs ys)"
    using "4.hyps"(2) "4.prems"(1) xs_is_flt2goodTock goodTocks_goodPriRels prirel_cons_eq_length_imp prirel_flt2goodTock_tgt_imp_src by blast

  from xs_is_flt2goodTock ys_is_flt2goodTock
  have flt2_ys_y:"flt2cttobs (ys &\<^sub>\<F>\<^sub>\<L> \<langle>y,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>) = flt2cttobs (ys) @ flt2cttobs(\<langle>y,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>)"
    using 4 flt2cttobs_acceptance_cons_eq_list_cons by blast
  then have "flt2cttobs (ys) @ flt2cttobs(\<langle>y,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>) \<in> P"
    using 4 by (simp)

  from xs_is_flt2goodTock ys_is_flt2goodTock
  have flt2_xs_x:"flt2cttobs (xs &\<^sub>\<F>\<^sub>\<L> \<langle>x,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>) = flt2cttobs (xs) @ flt2cttobs(\<langle>x,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>)"
    using 4 flt2cttobs_acceptance_cons_eq_list_cons
    by blast

  then obtain yA yEvent where 
    yAE:"y = (yA,yEvent)\<^sub>\<F>\<^sub>\<L> \<and> (yA = \<bullet> \<or> yEvent \<in>\<^sub>\<F>\<^sub>\<L> yA)"
    by (cases y, auto)
  then obtain xA where 
    xAE:"x = (xA,yEvent)\<^sub>\<F>\<^sub>\<L> \<and> (xA = \<bullet> \<or> yEvent \<in>\<^sub>\<F>\<^sub>\<L> xA)"
    apply (cases x, auto)
    using 4 \<open>prirel p \<langle>x,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L> \<langle>y,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>\<close> by auto

  then show ?case
    proof (cases "yEvent = Tock")
      case True 
      then have xA_not_bullet:"xA \<noteq> \<bullet>"
        using \<open>flt2goodTock (xs &\<^sub>\<F>\<^sub>\<L> \<langle>x,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>)\<close> \<open>last xs = \<bullet>\<close>
        proof (induct xs)
          case (Acceptance z)
          then show ?case using xAE by auto
        next
          case (AEvent x1a xs)
          then show ?case apply auto
            by presburger
        qed
      then have yA_not_bullet:"yA \<noteq> \<bullet>"
        by (metis \<open>prirel p \<langle>x,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L> \<langle>y,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>\<close> acceptance.exhaust acceptance_set prirel.simps(4) prirelacc.simps(3) xAE yAE)
      
      then obtain xR where xR:"flt2cttobs(\<langle>x,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>) = [[xR]\<^sub>R,[Tock]\<^sub>E]"
        using True xAE xA_not_bullet by auto
      then obtain yR where yR:"flt2cttobs(\<langle>y,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>) = [[yR]\<^sub>R,[Tock]\<^sub>E] \<and> prirelref p yR = xR"
        using True xAE yAE xA_not_bullet apply auto
        using yA_not_bullet apply simp
        using yA_not_bullet apply simp
        by (metis (no_types, lifting) Collect_cong \<open>prirel p \<langle>x,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L> \<langle>y,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>\<close> acceptance_set flt2cttobs.simps(1) prirel.simps(4) prirelacc_eq_prirelref_via_flt2cttobs)

      then have "cttWF (flt2cttobs (ys) @ [[yR]\<^sub>R,[Tock]\<^sub>E])"
        by (metis "4.prems"(4) FLTick0_def True assms(3) flt2_ys_y flt2cttobs_is_cttWF)
      then have "prirelRef p (flt2cttobs (xs) @ [[xR]\<^sub>R,[Tock]\<^sub>E]) (flt2cttobs (ys) @ [[yR]\<^sub>R,[Tock]\<^sub>E]) [] P"
        using prirelRef prirelRef_extend_both_tock_refusal_cttWF
        using yR
        by (metis CT3_trace.simps(3) flt2cttobs_is_CT3_trace xR)
      then have "prirelRef p (flt2cttobs (xs &\<^sub>\<F>\<^sub>\<L> \<langle>x,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>)) (flt2cttobs (ys &\<^sub>\<F>\<^sub>\<L> \<langle>y,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>)) [] P"
        using flt2_xs_x flt2_ys_y xR yR by auto
      then show ?thesis by auto
    next
      case False
      then have "flt2cttobs(\<langle>x,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>) = [[yEvent]\<^sub>E]"
        using xAE by auto
      then have "flt2cttobs(\<langle>y,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>) = [[yEvent]\<^sub>E]"
        using xAE yAE
        using False by fastforce

      then have cttWF_ys_y:"cttWF (flt2cttobs (ys &\<^sub>\<F>\<^sub>\<L> \<langle>y,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>))"
        using 4 
        by (meson FLTick0_def flt2cttobs_is_cttWF)

      then have cttWF_xs_x:"cttWF (flt2cttobs (xs &\<^sub>\<F>\<^sub>\<L> \<langle>x,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>))"
        using 4 
        using prirel_rhs_tickWF_imp_lhs_tickWF
        by (metis FLTick0_def flt2cttobs_is_cttWF)

      then have "prirelRef p (flt2cttobs (xs) @ [[yEvent]\<^sub>E]) (flt2cttobs (ys) @ [[yEvent]\<^sub>E]) [] P"
        using prirelRef
      proof (cases "maximal(p,yEvent)")
        case True
        then show ?thesis
          by (metis \<open>flt2cttobs \<langle>x,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L> = [[yEvent]\<^sub>E]\<close> \<open>flt2cttobs \<langle>y,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L> = [[yEvent]\<^sub>E]\<close> cttWF_xs_x cttWF_ys_y flt2_xs_x flt2_ys_y flt2cttobs_is_CT3_trace prirelRef prirelRef_extend_both_events_maximal_cttWF)
      next
        case False
        then show ?thesis
          proof (cases "xA")
            case acnil
            then have "yA \<noteq> \<bullet>"
              using False \<open>prirel p \<langle>x,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L> \<langle>y,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>\<close> xAE yAE by auto
            then have "\<not>(\<exists>b. b \<in>\<^sub>\<F>\<^sub>\<L> yA \<and> yEvent <\<^sup>*p b)"
              by (metis \<open>prirel p \<langle>x,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L> \<langle>y,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>\<close> amember.elims(2) amember.simps(2) not_prirelAlt_less_eq_both_events yAE)

            from 4 have "ys &\<^sub>\<F>\<^sub>\<L> \<langle>y,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L> \<in> fl\<^sub>0"
              by auto
            then have "ys &\<^sub>\<F>\<^sub>\<L> \<langle>yA\<rangle>\<^sub>\<F>\<^sub>\<L> \<in> fl\<^sub>0"
              using 4 fltrace_FL1_cons_acceptance_prefix yAE
              by (metis acceptance_set)
            then have "flt2cttobs(ys &\<^sub>\<F>\<^sub>\<L> \<langle>yA\<rangle>\<^sub>\<F>\<^sub>\<L>) \<in> P"
              using 4 fl2ctt_def by blast
            then obtain yR where yR:"flt2cttobs (ys) @ [[yR]\<^sub>R] \<in> P \<and> flt2cttobs(\<langle>yA\<rangle>\<^sub>\<F>\<^sub>\<L>) = [[yR]\<^sub>R] \<and> yEvent \<notin> yR"
              using "4.hyps"(4) \<open>yA \<noteq> \<bullet>\<close> flt2cttobs_cons_acceptance_eq_cons yAE ys_is_flt2goodTock by fastforce
            then have "flt2cttobs (ys) @ [[yR]\<^sub>R] \<in> P \<and> yEvent \<notin> yR \<and> \<not>(\<exists>b. b \<notin> yR \<and> yEvent <\<^sup>*p b)"
              using \<open>\<nexists>b. b \<in>\<^sub>\<F>\<^sub>\<L> yA \<and> yEvent <\<^sup>*p b\<close> \<open>yA \<noteq> \<bullet>\<close> by auto
            then show ?thesis
              by (metis \<open>flt2cttobs \<langle>x,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L> = [[yEvent]\<^sub>E]\<close> \<open>flt2cttobs \<langle>y,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L> = [[yEvent]\<^sub>E]\<close> append_Nil assms(8) cttWF_xs_x cttWF_ys_y flt2_xs_x flt2_ys_y prirelRef prirelRef_extend_both_events_non_maximal_cttWF)
              
          next
            case (acset x2)
            then have "yA \<noteq> \<bullet>"
              using \<open>prirel p \<langle>x,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L> \<langle>y,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>\<close> xAE yAE by auto
            then obtain yASet where yASet:"[yASet]\<^sub>\<F>\<^sub>\<L> = yA \<and> yEvent \<in> yASet"
              using yAE by (cases yA, auto)
            then have "x2 = {a. a \<in> yASet \<and> \<not>(\<exists>b. b\<in>yASet \<and> a <\<^sup>*p b)}"
              using \<open>prirel p \<langle>x,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L> \<langle>y,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>\<close> acset xAE yAE by auto
            then have "flt2cttobs(ys &\<^sub>\<F>\<^sub>\<L> \<langle>[yASet]\<^sub>\<F>\<^sub>\<L>\<rangle>\<^sub>\<F>\<^sub>\<L>) \<in> P"
              by (metis (mono_tags, lifting) "4"(6) "4"(8) "4"(9) acceptance_set contra_subsetD fl2ctt_def fltrace_FL1_cons_acceptance_prefix mem_Collect_eq yAE yASet)
            then obtain yR where yR:"flt2cttobs (ys) @ [[yR]\<^sub>R] \<in> P \<and> flt2cttobs(\<langle>[yASet]\<^sub>\<F>\<^sub>\<L>\<rangle>\<^sub>\<F>\<^sub>\<L>) = [[yR]\<^sub>R] \<and> yEvent \<notin> yR"
              using "4.hyps"(4) \<open>yA \<noteq> \<bullet>\<close> flt2cttobs_cons_acceptance_eq_cons yAE yASet ys_is_flt2goodTock by fastforce
            then have "flt2cttobs (ys) @ [[yR]\<^sub>R] \<in> P \<and> yEvent \<notin> yR \<and> \<not>(\<exists>b. b \<notin> yR \<and> yEvent <\<^sup>*p b)"
              using \<open>prirel p \<langle>x,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L> \<langle>y,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>\<close> acset xAE yAE yASet by auto
            then show ?thesis
              by (metis \<open>flt2cttobs \<langle>x,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L> = [[yEvent]\<^sub>E]\<close> \<open>flt2cttobs \<langle>y,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L> = [[yEvent]\<^sub>E]\<close> append_Nil assms(8) cttWF_xs_x cttWF_ys_y flt2_xs_x flt2_ys_y prirelRef prirelRef_extend_both_events_non_maximal_cttWF)
              
          qed
        qed
        then show ?thesis
          using \<open>flt2cttobs \<langle>x,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L> = [[yEvent]\<^sub>E]\<close> \<open>flt2cttobs \<langle>y,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L> = [[yEvent]\<^sub>E]\<close> flt2_xs_x flt2_ys_y by auto
      qed
    qed

lemma
  assumes "prirel p fl Y" "FL1 fl\<^sub>0" "FLTick0 Tick fl\<^sub>0"
          "Y \<in> fl\<^sub>0"
          "fl2ctt fl\<^sub>0 \<subseteq> P"
          "flt2cttobs Y \<in> P"
          "ar = flt2cttobs fl" "flt2goodTock fl" "CTwf P"
        shows "\<exists>zr. prirelRef p (flt2cttobs fl) zr [] P \<and> zr \<in> P"
  using pp 
  using assms(1) assms(2) assms(3) assms(4) assms(5) assms(6) assms(8) assms(9) by blast

(*proof (induct fl)
  case Nil
  then show ?case by (intro exI[where x="\<langle>\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>"], auto)
next
  case (Cons a fl)
  then show ?case
    proof (cases a)
      case (ObsEvent oe)
      then obtain x xA where xA:"x = (xA,oe)\<^sub>\<F>\<^sub>\<L> \<and> (xA = \<bullet> \<or> oe \<in>\<^sub>\<F>\<^sub>\<L> xA)"
        by auto
      then show ?thesis 
      proof (cases oe)
        case (Event e1)
        then have "\<exists>z. flt2cttobs(x #\<^sub>\<F>\<^sub>\<L> z) = a # fl \<and> cttWF fl \<and> CT3_trace fl"
          using xA Event ObsEvent Cons
          by (metis CT3_trace.simps(1) CT3_trace.simps(4) acceptance_event cttWF.simps(11) cttWF.simps(4) cttWF.simps(5) flt2cttobs.simps(2) list.exhaust)
        then have "\<exists>z. [oe]\<^sub>E # (flt2cttobs z) = a # fl"
          using Cons.hyps ObsEvent by blast
        then show ?thesis  
          using \<open>\<exists>z. flt2cttobs (x #\<^sub>\<F>\<^sub>\<L> z) = a # fl \<and> cttWF fl \<and> CT3_trace fl\<close> by blast
      next
        case Tock
        then show ?thesis
        proof (cases "xA")
          case acnil
          then show ?thesis using ObsEvent Cons xA Tock by auto
        next
          case (acset x2)
          then have "\<exists>z. [{x. x \<notin> x2}]\<^sub>R # [Tock]\<^sub>E # (flt2cttobs z) = a # fl"
            using Cons.prems ObsEvent Tock by auto
          then show ?thesis
            by (simp add: ObsEvent)
        qed
      next
        case Tick
        then show ?thesis using ObsEvent Cons xA Tick
          using CT3_trace_cons_imp_cons
          by (metis acceptance_event cttWF.simps(1) cttWF.simps(10) cttWF.simps(12) cttWF.simps(5) flt2cttobs.simps(2) neq_Nil_conv)
      qed
    next
      case (Ref x2)
      then show ?thesis using Cons Ref assms
      proof (induct fl)
        case Nil
        then show ?case by (intro exI[where x="\<langle>[{x. x \<notin> x2}]\<^sub>\<F>\<^sub>\<L>\<rangle>\<^sub>\<F>\<^sub>\<L>"], auto)
      next
        case (Cons b fl)
        then have b_Tock:"b = [Tock]\<^sub>E"
          using Cons Ref assms apply auto
          using cttWF.elims(2) by blast
        then have "Tock \<notin> x2"
          using Ref Cons.prems(4) by auto
        then have "flt2cttobs(\<langle>([{x. x \<notin> x2}]\<^sub>\<F>\<^sub>\<L>,Tock)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>) = [a, b]"
          using b_Tock Ref by auto
        then have "\<exists>zr. flt2cttobs zr = fl"
        sledgehammer
      

        have "a # b # fl = [a,b] @ fl"
          by auto
        also have "... = flt2cttobs(\<langle>([{x. x \<notin> x2}]\<^sub>\<F>\<^sub>\<L>,Tock)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>) @ fl"
          using \<open>flt2cttobs \<langle>([{x. x \<notin> x2}]\<^sub>\<F>\<^sub>\<L>,Tock)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L> = [a, b]\<close> by auto
       (* then have "\<exists>z. flt2cttobs(\<langle>([{x. x \<notin> x2}]\<^sub>\<F>\<^sub>\<L>,Tock)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>) @ flt2cttobs(z) = 
                    flt2cttobs(\<langle>([{x. x \<notin> x2}]\<^sub>\<F>\<^sub>\<L>,Tock)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>) @ fl"
          oops*)
       (* then obtain x zz where xA:"x = ([{x. x \<notin> x2}]\<^sub>\<F>\<^sub>\<L>,Tock)\<^sub>\<F>\<^sub>\<L> #\<^sub>\<F>\<^sub>\<L> zz \<and> flt2cttobs zz = fl"
          apply auto 
        then have "\<exists>z. [{x. x \<notin> x2}]\<^sub>R # [Tock]\<^sub>E # (flt2cttobs z) = a # b # fl"
        using Cons Ref  sorry*)
          then show ?case sledgehammer
      qed

      proof (cases "fl = []")
        case True
        then show ?thesis using Ref Cons
          by (intro exI[where x="\<langle>[{x. x \<notin> x2}]\<^sub>\<F>\<^sub>\<L>\<rangle>\<^sub>\<F>\<^sub>\<L>"], auto)
      next
        case False
        then obtain tl_fl where tl_fl:"fl = [Tock]\<^sub>E # tl_fl"
          using Cons Ref assms apply auto sledgehammer
        then show ?thesis using Ref Cons
      qed
        using Cons 
    qed
qed
*)

lemma
  assumes "prirelRef p (flt2cttobs fl) (flt2cttobs zr) [] P"
  shows "prirelRef p (flt2cttobs fl) (flt2cttobs zr) [] P \<and> length fl = length zr"
  nitpick

lemma
  assumes "prirelRef p (flt2cttobs fl) (flt2cttobs xs) [] P"
  shows "\<exists>zr. prirelRef p (flt2cttobs fl) (flt2cttobs zr) [] P \<and> length fl = length zr \<and> (flt2cttobs zr) = (flt2cttobs xs)"
  using assms 
  apply (induct p fl xs rule:prirel.induct, auto)
  apply (intro exI[where x="\<langle>\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>"], auto)
                apply (rule_tac x="\<langle>Z\<rangle>\<^sub>\<F>\<^sub>\<L>" in exI, auto)
               apply (rule_tac x="\<langle>Z\<rangle>\<^sub>\<F>\<^sub>\<L>" in exI, auto)
           apply (intro exI[where x="\<langle>\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>"], auto)
  apply (intro exI[where x="\<langle>\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>"], auto)
          apply (smt prirelRef.simps(29) prirelRef.simps(33) prirelRef.simps(82))

         apply (smt prirelRef.simps(19) prirelRef.simps(22))

        apply (metis (mono_tags, lifting) prirelRef.simps(29) prirelRef.simps(7))
  sorry (* provable I think *)

lemma prirelRef_flt2cttobs_both_eq_length_flt2goodTock_both:
  assumes "prirelRef p (flt2cttobs xs) (flt2cttobs ys) zs P" "flt2goodTock xs" "length xs = length ys"
  shows "flt2goodTock ys"
  using assms apply (induct p xs ys arbitrary: zs rule:prirel.induct, auto)
  apply (smt prirelRef.simps(3) prirelRef.simps(30))
    apply (smt prirelRef.simps(18) prirelRef.simps(5))
  apply (case_tac A, auto, case_tac b, auto, case_tac a, auto)
       apply meson
      apply (case_tac a, auto)
     apply (case_tac a, auto)
    apply (case_tac a, auto)
   apply (case_tac b, auto)
  apply (case_tac A, auto, case_tac b, auto)
       apply (case_tac a, auto)
      apply (case_tac a, auto)
     apply (case_tac a, auto)
    apply (case_tac a, auto)
   apply (case_tac a, auto)
  by (case_tac b, auto)

lemma cttWF2_cttWF_imp:
  assumes "cttWF x" "cttWF y"
  shows "cttWF2 x y"
  using assms cttWF2_cttWF by blast

lemma not_prirelRef_cases [simp]:
  "\<not> prirelRef pa (x # xs # ys) [ysa] s P"
  apply (cases x, auto)
  by (cases ysa, auto)

lemma not_prirelRef_cases_2 [simp]:
  assumes "ys \<noteq> []"
  shows "\<not> prirelRef pa (x # xs @ ys) [ysa] s P"
  using assms apply (cases x, auto)
   apply (cases xs, auto, cases ys, auto)
  by (cases xs, auto, cases ys, auto)

lemma
  assumes "prirelRef p (flt2cttobs fl) (flt2cttobs zr) [] P" "length fl = length zr"
  shows "size (flt2cttobs fl) = size (flt2cttobs zr)"
  using assms
  apply (induct fl zr rule:ftrace_cons_induct_both_eq_length, auto)
    apply (case_tac y, auto)
  oops



lemma CT1c_prefix_is_in:
  assumes "CT1c P" "s @ t \<in> P"
  shows "s \<in> P"
  using assms unfolding CT1c_def 
  using ctt_prefix_concat by blast

lemma prirelRef_of_both_flt2cttobs_cons_acceptance_imp_prirel_acceptance:
  assumes "prirelRef p (flt2cttobs (xs &\<^sub>\<F>\<^sub>\<L> \<langle>x\<rangle>\<^sub>\<F>\<^sub>\<L>)) (flt2cttobs (ys &\<^sub>\<F>\<^sub>\<L> \<langle>y\<rangle>\<^sub>\<F>\<^sub>\<L>)) s P" 
          "last xs = \<bullet>" "last ys = \<bullet>"
          "flt2goodTock xs" "flt2goodTock ys"
  shows "prirel p \<langle>x\<rangle>\<^sub>\<F>\<^sub>\<L> \<langle>y\<rangle>\<^sub>\<F>\<^sub>\<L>" (* FIXME: better proof please.. *)
  using assms apply (induct p xs ys arbitrary:s x y rule:prirel.induct, auto)
  
  apply (smt Collect_cong acceptance_left_zero flt2cttobs.simps(1) prirelRef.simps(2) prirelRef.simps(28) prirelacc.simps(1) prirelacc_eq_prirelref_via_flt2cttobs)
  
        apply (metis (mono_tags) prirelRef.simps(46))

  apply (smt prirelRef.simps(29) prirelRef.simps(46) prirelRef.simps(68))
  
      apply (smt prirelRef.simps(46))   
     
     apply (smt not_prirelRef_cases prirelRef.simps(28) prirelRef.simps(47))
  
    apply (smt not_prirelRef_cases prirelRef.simps(47))
  apply (case_tac Z, auto, case_tac A, auto, case_tac ba, auto, case_tac b, auto)
    
    apply meson 
  apply meson 
       apply (smt acceptance_event prirelRef.simps(47))

      apply (smt acceptance_event acceptance_set prirelRef.simps(29) prirelRef.simps(3))
  apply (case_tac b, auto)

  apply (smt acceptance_event acceptance_set prirelRef.simps(4) prirelRef.simps(47))
    apply (smt acceptance_event acceptance_set prirelRef.simps(29) prirelRef.simps(3) prirelRef.simps(4) prirelRef.simps(47))
    apply (smt prirelRef.simps(29) prirelRef.simps(3) prirelRef.simps(4) prirelRef.simps(47))
  apply (case_tac ba, auto, case_tac b, auto) 
         apply meson
        apply meson
    apply (case_tac a, auto, case_tac b, auto, case_tac a, auto, case_tac a, auto)
      apply meson
    apply (case_tac A, auto, case_tac ba, auto, case_tac b, auto, case_tac a, auto)
        apply meson
    apply (case_tac b, auto, case_tac a, auto, case_tac a, auto, case_tac b, auto)
       apply meson
      apply meson
     apply (case_tac ba, auto, case_tac b, auto, case_tac b, auto)
    apply (case_tac A, auto, case_tac b, auto, case_tac Z, auto, case_tac b, auto)
          apply (case_tac a, auto, case_tac ab, auto)
    
    apply force 
         apply (metis bullet_right_zero2)

        apply (smt acceptance_event prirelRef.simps(47))
    apply (case_tac b, auto, case_tac a, auto)
        apply (smt bullet_right_zero2 prirelRef.simps(4))
  
       apply (metis bullet_right_zero2)
    apply (case_tac Z, auto, case_tac b, auto, case_tac a, auto, case_tac ab, auto)
        apply (case_tac a, auto)
        apply force
       apply (case_tac a, auto, case_tac b, auto, case_tac a, auto, case_tac a, auto)
 apply (case_tac Z, auto, case_tac b, auto, case_tac a, auto, case_tac ab, auto)
        apply (case_tac a, auto, case_tac ab, auto)
        apply force
      apply (case_tac a, auto, case_tac ab, auto)
      apply force
     apply (case_tac b, auto, case_tac a, auto)
      apply force
     apply (case_tac a, auto, force)
    apply (case_tac Z, auto, case_tac b, auto, case_tac a, auto, case_tac ba, auto, force)
      apply force
     apply (case_tac ba, auto, case_tac a, auto, case_tac a, auto,force)
     apply (case_tac a, auto, force)
  proof -
    fix pa :: "'a cttevent partialorder" and aa :: "'a cttevent fltrace" and zz :: "'a cttevent fltrace" and sa :: "'a cttobs list" and ya :: "'a cttevent acceptance" and b :: "'a cttevent" and ba :: "'a cttevent"
    assume a1: "prirelRef pa (if b = Tock then if acceptance (\<bullet>,b)\<^sub>\<F>\<^sub>\<L> \<noteq> \<bullet> then [{z. z \<notin>\<^sub>\<F>\<^sub>\<L> acceptance (\<bullet>,b)\<^sub>\<F>\<^sub>\<L>}]\<^sub>R # [Tock]\<^sub>E # flt2cttobs (aa &\<^sub>\<F>\<^sub>\<L> \<langle>\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>) else [] else [event (\<bullet>,b)\<^sub>\<F>\<^sub>\<L>]\<^sub>E # flt2cttobs (aa &\<^sub>\<F>\<^sub>\<L> \<langle>\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>)) (if ba = Tock then if acceptance (\<bullet>,ba)\<^sub>\<F>\<^sub>\<L> \<noteq> \<bullet> then [{z. z \<notin>\<^sub>\<F>\<^sub>\<L> acceptance (\<bullet>,ba)\<^sub>\<F>\<^sub>\<L>}]\<^sub>R # [Tock]\<^sub>E # flt2cttobs (zz &\<^sub>\<F>\<^sub>\<L> \<langle>ya\<rangle>\<^sub>\<F>\<^sub>\<L>) else [] else [event (\<bullet>,ba)\<^sub>\<F>\<^sub>\<L>]\<^sub>E # flt2cttobs (zz &\<^sub>\<F>\<^sub>\<L> \<langle>ya\<rangle>\<^sub>\<F>\<^sub>\<L>)) sa P"
    assume a2: "if b = Tock then False else flt2goodTock aa"
    assume a3: "if ba = Tock then False else flt2goodTock zz"
    assume a4: "\<And>s x y. \<lbrakk>prirelRef pa (flt2cttobs (aa &\<^sub>\<F>\<^sub>\<L> \<langle>x\<rangle>\<^sub>\<F>\<^sub>\<L>)) (flt2cttobs (zz &\<^sub>\<F>\<^sub>\<L> \<langle>y\<rangle>\<^sub>\<F>\<^sub>\<L>)) s P; flt2goodTock aa; flt2goodTock zz\<rbrakk> \<Longrightarrow> prirelacc pa x y \<and> (x = \<bullet> \<longrightarrow> y = \<bullet>)"
    have "b \<noteq> Tock \<and> ba \<noteq> Tock"
      using a3 a2 by presburger
    then show "ya = \<bullet>"
      using a4 a3 a2 a1 by force
  qed

lemma flt2goodS_imp_flt2goodTock [simp]:
  assumes "flt2goodS p xs"
  shows "flt2goodTock xs"
  using assms by (induct xs rule:flt2goodS.induct, auto)

(*
lemma
  assumes "prirelRef p (flt2cttobs xs) (flt2cttobs ys) s P" "flt2goodS ys" "length xs = length ys"
  shows "flt2goodS xs"
  nitpick*)

(* So we want... *)
lemma
  assumes "prirelRef p ar zr [] P" 
          "zr \<in> P" 
    shows "\<exists>Z fl\<^sub>0 fl. prirel p fl Z \<and> Z \<in> fl\<^sub>0 \<and> fl2ctt fl\<^sub>0 \<subseteq> P \<and> flt2cttobs Z \<in> P \<and> flt2cttobs fl = ar"
  (* But this is easier if done inductively over fl Z... *)
  oops

lemma prirel_extend_both_prefix_imp:
  assumes "prirel p fl zr" "prirel p fla zra"
  shows "prirel p (fla &\<^sub>\<F>\<^sub>\<L> fl) (zra &\<^sub>\<F>\<^sub>\<L> zr)"
  using assms apply (induct p fla zra rule:prirel.induct, auto)
   apply (case_tac A, auto, case_tac Z, auto)
  apply (smt Collect_cong Finite_Linear_Model.last.simps(1) acceptance.distinct(1) concat_FL_last_not_bullet_absorb prirelAlt.simps(1) prirelAlt_imp_prirel prirelaccAlt.simps(2))
  by (case_tac A, auto)

lemma pp1:
  assumes "prirelRef p (flt2cttobs fl) (flt2cttobs zr) [] P" "prirel p fl zr"
          "(flt2cttobs zr) \<in> P" 
    shows "\<exists>fl\<^sub>0. prirel p fl zr \<and> zr \<in> fl\<^sub>0 \<and> fl2ctt fl\<^sub>0 \<subseteq> P \<and> (flt2cttobs zr) \<in> P"
  using assms apply auto sorry

thm type_definition_aevent

(*
lemma "Rep_aevent (Abs_aevent x) = x"
  sledgehammer
of course not true in general
*)

lemma "Abs_aevent (Rep_aevent x) = x"
  by (simp add: Rep_aevent_inverse)

lemma
  "prirel p xs ys"

lemma prirelRef_is_CT3_trace_closed:
  assumes "prirelRef p xs ys s P" "CT3_trace ys"
  shows "CT3_trace xs"
  using assms apply(induct p xs ys s P rule:prirelRef.induct, auto)
  by (metis CT3_trace.simps(2) CT3_trace.simps(4) neq_Nil_conv)+

lemma
  assumes "\<exists>z. Tick <\<^sup>*p z"
  shows "\<not>prirel p x \<langle>(\<bullet>,Tick)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>"
  using assms apply (cases x, auto)
    apply (simp_all add: some_higher_not_maximal)
  using prirelacc.elims(2) by blast

lemma flt2goodAcceptance_pair_consFL:
  assumes "Event e \<in>\<^sub>\<F>\<^sub>\<L> aE" "flt2goodAcceptance (\<langle>(aE,Event e)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L> &\<^sub>\<F>\<^sub>\<L> tt) p"
  shows "(flt2goodAcceptance (\<langle>(aE,Event e)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>) p \<and> flt2goodAcceptance tt p)"
  using assms apply (induct tt p rule:flt2goodAcceptance.induct)
   apply (case_tac A, simp)
   apply auto[1]
   apply (metis acceptance_event cttevent.distinct(3))
  apply (case_tac A, safe)
     apply (cases aE)
      apply auto[2]
     apply (metis acceptance_event assms(1) cttevent.distinct(3))
  apply (metis acceptance_event acceptance_set amember.simps(1) assms(1) cttevent.distinct(3) flt2goodAcceptance.simps(2) fltrace_concat2.simps(2) fltrace_concat2.simps(3) some_higher_not_maximal)
   apply (case_tac b, safe) 
  apply auto[3]
     apply (metis acceptance_event cttevent.distinct(3))
  apply (metis acceptance_event cttevent.distinct(3))
  apply (metis acceptance_event cttevent.distinct(3))
  apply (case_tac b, safe) 
    apply (cases aE, auto)
  apply (metis acceptance_event acceptance_set cttevent.distinct(3) flt2goodAcceptance.simps(2))
    apply (metis (no_types, hide_lams) acceptance_event amember.simps(2) cttevent.distinct(3) flt2goodAcceptance.elims(2) flt2goodAcceptance.simps(2) fltrace.distinct(1) fltrace.inject(2) some_higher_not_maximal)
    apply (metis (no_types, hide_lams) acceptance_event acceptance_set flt2goodAcceptance.simps(2))
    by (metis acceptance_event acceptance_set cttevent.distinct(5) flt2goodAcceptance.simps(2))

(*
lemma
  assumes "e\<^sub>2 \<in>\<^sub>\<F>\<^sub>\<L> aE"
  shows
   "flt2goodAcceptance (\<langle>(aE,e\<^sub>2)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L> &\<^sub>\<F>\<^sub>\<L> tt) p
   = 
   (flt2goodAcceptance (\<langle>(aE,e\<^sub>2)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>) p \<and> flt2goodAcceptance tt p)"
  using assms apply auto
  *)

lemma pp20:
  assumes "prirelRef p xs ys s P" "CT3_trace ys" "cttWF ys" "(flt2cttobs zr) = ys" 
          "flt2goodTock zr"
          "flt2goodAcceptance zr p"
          "maximal(p,Tick)"
  shows "\<exists>fl. prirel p fl zr \<and> (flt2cttobs fl) = xs"
  using assms
proof (induct p xs ys s P arbitrary:zr rule:prirelRef.induct, auto)
  fix pa::"'a cttevent partialorder"
  fix zra::"'a cttevent fltrace"
  assume assm1:"flt2cttobs zra = []"
  assume assm2:"flt2goodTock zra"
  from assm1 assm2 have "zra = \<langle>\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>"
    by (metis flt2cttobs.simps(1) flt2cttobs_consFL_eq_Nil_imp_not_flt2goodTock list.simps(3))
  then show "\<exists>fl. prirel pa fl zra \<and> flt2cttobs fl = []"
    by (meson flt2cttobs.simps(1) prirel.simps(1) prirelacc.simps(1))
next
  fix pa::"'a cttevent partialorder"
  fix S
  fix zra::"'a cttevent fltrace"
  assume assm1:"flt2cttobs zra = [[S]\<^sub>R]"
  assume assm2:"flt2goodTock zra"
  from assm1 assm2 have "zra = \<langle>[{x. x \<notin> S}]\<^sub>\<F>\<^sub>\<L>\<rangle>\<^sub>\<F>\<^sub>\<L>"
    apply (cases zra, auto)
     apply (case_tac x1, auto)
    apply (case_tac x21, auto, case_tac b, auto, case_tac a, auto)
    by (case_tac b, auto)
  then show "\<exists>fl. prirel pa fl zra \<and> flt2cttobs fl = [[prirelref pa S]\<^sub>R]"
    apply (intro exI[where x="\<langle>[{x. x \<notin> (prirelref pa S)}]\<^sub>\<F>\<^sub>\<L>\<rangle>\<^sub>\<F>\<^sub>\<L>"])
    unfolding prirelref_def by auto 
next
  fix pa::"'a cttevent partialorder"
  fix aa S zz sa Q
  fix zra::"'a cttevent fltrace"
  assume hyp:"(\<And>zr. flt2cttobs zr = zz \<Longrightarrow> flt2goodTock zr \<Longrightarrow> flt2goodAcceptance zr pa \<Longrightarrow> \<exists>fl. prirel pa fl zr \<and> flt2cttobs fl = aa)"
  assume assm1:"prirelRef pa aa zz (sa @ [[S]\<^sub>R, [Tock]\<^sub>E]) Q"
  assume assm2:"cttWF zz"
  assume assm3:"flt2goodTock zra"
  assume assm4:"Tock \<notin> S"
  assume assm5:"Tock \<notin> prirelref pa S"
  assume assm6:"CT3_trace zz"
  assume assm7:"flt2cttobs zra = [S]\<^sub>R # [Tock]\<^sub>E # zz"
  then have tocks:"Tock \<in>\<^sub>\<F>\<^sub>\<L> [{x. x \<notin> prirelref pa S}]\<^sub>\<F>\<^sub>\<L>"
                  "Tock \<in>\<^sub>\<F>\<^sub>\<L> [{x. x \<notin> S}]\<^sub>\<F>\<^sub>\<L>"
    using assm4 assm5
    apply (metis amember.simps(2) mem_Collect_eq)
    by (simp_all add: assm4)
  assume assm8:"flt2goodAcceptance zra pa"
  have "flt2cttobs(\<langle>([{x. x \<notin> S}]\<^sub>\<F>\<^sub>\<L>,Tock)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>) = [S]\<^sub>R # [Tock]\<^sub>E # Nil"
    using tocks by auto
  then obtain tt where tt:"flt2cttobs tt = zz \<and> flt2goodTock tt \<and> flt2goodAcceptance tt pa \<and> zra = \<langle>([{x. x \<notin> S}]\<^sub>\<F>\<^sub>\<L>,Tock)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L> &\<^sub>\<F>\<^sub>\<L> tt"
    using assm7 tocks assm3 assm4 assm8 apply (induct zra, auto)
     apply (metis list.inject neq_Nil_conv)
    apply (case_tac x1a, auto, case_tac b, auto, case_tac a, auto)
     apply metis
    by (case_tac b, auto)
  then obtain flaa where flaa:"prirel pa flaa tt \<and> flt2cttobs flaa = aa"
    using hyp assm8 by blast
    
  show "\<exists>fl. prirel pa fl zra \<and> flt2cttobs fl = [prirelref pa S]\<^sub>R # [Tock]\<^sub>E # aa"
  proof -
    have "prirelRef pa ([prirelref pa S]\<^sub>R # [Tock]\<^sub>E # aa) 
                        ([S]\<^sub>R # [Tock]\<^sub>E # zz) sa Q"
      by (simp add: assm1 assm5)

    obtain fla where fla:"fla = \<langle>([{x. x \<notin> prirelref pa S}]\<^sub>\<F>\<^sub>\<L>,Tock)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>" by auto
    
    have "prirel pa fla \<langle>([{x. x \<notin> S}]\<^sub>\<F>\<^sub>\<L>,Tock)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>"
      using tocks fla unfolding prirelref_def by auto
    have flt2cttobs_fla_flaa:"flt2cttobs(fla &\<^sub>\<F>\<^sub>\<L> flaa) = [prirelref pa S]\<^sub>R # [Tock]\<^sub>E # aa"
      using tocks fla flaa by auto
    have "prirel pa (fla &\<^sub>\<F>\<^sub>\<L> flaa) zra"
      using tocks fla flaa apply auto
      by (metis FL_concat_equiv \<open>prirel pa fla \<langle>([{x. x \<notin> S}]\<^sub>\<F>\<^sub>\<L>,Tock)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>\<close> local.tt prirel_extend_both_prefix_imp)
    then show ?thesis using flt2cttobs_fla_flaa by blast
  qed
next
  fix pa::"'a cttevent partialorder"
  fix aa e\<^sub>2 zz sa Q zra
  assume hyp:"(\<And>zr. cttWF zz \<Longrightarrow>
              flt2cttobs zr = zz \<Longrightarrow> flt2goodTock zr \<Longrightarrow> flt2goodAcceptance zr pa \<Longrightarrow> \<exists>fl. prirel pa fl zr \<and> flt2cttobs fl = aa)"
  assume assm1:"CT3_trace ([e\<^sub>2]\<^sub>E # zz)"
  assume assm2:"cttWF ([e\<^sub>2]\<^sub>E # zz)"
  then have no_Tock:"e\<^sub>2 \<noteq> Tock"
    using cttWF.simps(6) by blast
  have zz_is_cttWF:"cttWF zz"
    using assm2
    by (metis cttWF.simps(1) cttWF.simps(4) cttWF.simps(8) cttevent.exhaust neq_Nil_conv no_Tock)
  assume assm3:"flt2cttobs zra = [e\<^sub>2]\<^sub>E # zz"
  assume assm4:"flt2goodTock zra"
  assume assm5:"prirelRef pa aa zz (sa @ [[e\<^sub>2]\<^sub>E]) Q"
  assume assm6:"maximal(pa,e\<^sub>2)"
  assume assm7:"flt2goodAcceptance zra pa"
  from assm3 obtain tt aE where tt:"flt2cttobs tt = zz \<and> flt2goodTock tt \<and> flt2goodAcceptance tt pa \<and> zra = \<langle>(aE,e\<^sub>2)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L> &\<^sub>\<F>\<^sub>\<L> tt \<and> (e\<^sub>2 \<in>\<^sub>\<F>\<^sub>\<L> aE \<or> aE = \<bullet>)"
    using assm3 assm4 assm7 no_Tock apply (induct zra, auto)
     apply (case_tac x, auto)
    apply (case_tac x1a, auto)
    apply (case_tac a, auto, case_tac b)
    apply (metis acceptance_event acceptance_set amember.simps(2) cttevent.distinct(1) cttevent.distinct(3) cttobs.inject(1) list.inject some_higher_not_maximal)
    
      apply auto[1]

  apply (metis acceptance_event acceptance_set amember.simps(2) cttevent.distinct(5) cttobs.inject(1) list.inject)
  apply (case_tac b)  
    apply (metis acceptance_event cttobs.inject(1) list.inject)
  by auto
  then obtain fl where fl:"prirel pa fl tt \<and> flt2cttobs fl = aa"
    using assm2 assm4 hyp zz_is_cttWF
    by blast
  show "\<exists>fl. prirel pa fl zra \<and> flt2cttobs fl = [e\<^sub>2]\<^sub>E # aa"
  proof -
    from assm5 assm6 have "prirelRef pa ([e\<^sub>2]\<^sub>E # aa) ([e\<^sub>2]\<^sub>E # zz) sa Q"
      by simp

    then show ?thesis
    proof (cases "aE = \<bullet>")
      case True
      obtain fle2 where "fle2 = \<langle>(\<bullet>,e\<^sub>2)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L> &\<^sub>\<F>\<^sub>\<L> fl" by auto
      then have "prirel pa fle2 zra"
        using assm6 fl local.tt by auto
      then show ?thesis
        using \<open>fle2 = \<langle>(\<bullet>,e\<^sub>2)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L> &\<^sub>\<F>\<^sub>\<L> fl\<close> fl no_Tock by auto
    next
      case False
      then obtain fle2 where fle2:"fle2 = \<langle>([{a. a \<in>\<^sub>\<F>\<^sub>\<L> aE \<and> \<not>(\<exists>b. b\<in>\<^sub>\<F>\<^sub>\<L>aE \<and> a <\<^sup>*pa b)}]\<^sub>\<F>\<^sub>\<L>,e\<^sub>2)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L> &\<^sub>\<F>\<^sub>\<L> fl \<and> e\<^sub>2 \<in>\<^sub>\<F>\<^sub>\<L> [{a. a \<in>\<^sub>\<F>\<^sub>\<L> aE \<and> \<not>(\<exists>b. b\<in>\<^sub>\<F>\<^sub>\<L>aE \<and> a <\<^sup>*pa b)}]\<^sub>\<F>\<^sub>\<L>"
        using assm6 local.tt some_higher_not_maximal by fastforce
      then have "prirel pa fle2 zra"
        using False fl tt by (cases aE, auto)
      then show ?thesis
        using fl fle2 no_Tock by auto
    qed
  qed
next
  fix pa::"'a cttevent partialorder"
  fix aa e\<^sub>2 zz sa Q zra Z
  assume hyp:"(\<And>zr. cttWF zz \<Longrightarrow> flt2cttobs zr = zz \<Longrightarrow> flt2goodTock zr \<Longrightarrow> flt2goodAcceptance zr pa \<Longrightarrow> \<exists>fl. prirel pa fl zr \<and> flt2cttobs fl = aa)"
  assume assm1:"CT3_trace ([e\<^sub>2]\<^sub>E # zz)"
  assume assm2:"cttWF ([e\<^sub>2]\<^sub>E # zz)"
  then have no_Tock:"e\<^sub>2 \<noteq> Tock"
    using cttWF.simps(6) by blast
  have zz_is_cttWF:"cttWF zz"
    using assm2
    by (metis cttWF.simps(1) cttWF.simps(4) cttWF.simps(8) cttevent.exhaust neq_Nil_conv no_Tock)
  assume assm3:"flt2cttobs zra = [e\<^sub>2]\<^sub>E # zz"
  assume assm4:"flt2goodTock zra"
  assume assm5:"prirelRef pa aa zz (sa @ [[e\<^sub>2]\<^sub>E]) Q"
  assume assm6:"sa @ [[Z]\<^sub>R] \<in> Q"
  assume assm7:"\<forall>b. b \<in> Z \<or> \<not> e\<^sub>2 <\<^sup>*pa b"
  assume assm8:"e\<^sub>2 \<notin> Z"
  assume assm9:"flt2goodAcceptance zra pa"
  assume assm10:"maximal(pa,Tick)" (* FIXME: Not needed, I think *)
  from assm3 obtain tt aE where tt:"flt2cttobs tt = zz \<and> flt2goodTock tt 
    \<and> flt2goodAcceptance tt pa \<and> zra = \<langle>(aE,e\<^sub>2)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L> &\<^sub>\<F>\<^sub>\<L> tt 
    \<and> (e\<^sub>2 \<in>\<^sub>\<F>\<^sub>\<L> aE \<or> aE = \<bullet>)"
    using assm3 assm4 assm9 no_Tock apply (induct zra, auto)
    apply (case_tac x, auto)
    apply (case_tac x1a, auto)
    apply (metis acceptance_event acceptance_set cttWF.simps(6) cttobs.inject(1) list.inject zz_is_cttWF)
    by (metis acceptance_event cttobs.inject(1) list.inject)
  then obtain fl where fl:"prirel pa fl tt \<and> flt2cttobs fl = aa"
    using assm2 assm4 hyp zz_is_cttWF
    by blast
  show "\<exists>fl. prirel pa fl zra \<and> flt2cttobs fl = [e\<^sub>2]\<^sub>E # aa"
  proof -
    from assm5 assm6 assm7 have prirelRef:"prirelRef pa ([e\<^sub>2]\<^sub>E # aa) ([e\<^sub>2]\<^sub>E # zz) sa Q"
      using prirelRef.simps(4) assm8 by blast

    then show ?thesis
    proof (cases "aE = \<bullet>")
      case aE_is_bullet:True
      then show ?thesis
      proof (cases "e\<^sub>2")
        case (Event x1)
          then show ?thesis
            proof (cases "maximal(pa,e\<^sub>2)")
              case True
              then show ?thesis using aE_is_bullet tt Event
                by (metis FL_concat_equiv acceptance_event fl flt2cttobs.simps(2) no_Tock prirel_cons_bullet_iff_exists)
            next
              case False
              then have "\<not> flt2goodAcceptance zra pa"
                using tt aE_is_bullet Event by auto
              then show ?thesis
                using assm9 by blast
            qed
      next
        case Tock
        then show ?thesis
          using no_Tock by blast
      next
        case Tick
        then show ?thesis
        proof -
          have f1: "[] = zz"
            by (metis (no_types) Tick assm2 cttWF.simps(8) neq_Nil_conv)
          then have f2: "\<forall>c cs ca C csa p. \<not> prirelRef p (c # ca # cs) (flt2cttobs zra) csa C"
            by (simp add: assm3)
          have f3: "prirelRef pa ([e\<^sub>2]\<^sub>E # aa) (flt2cttobs zra) sa Q"
            by (metis \<open>prirelRef pa ([e\<^sub>2]\<^sub>E # aa) ([e\<^sub>2]\<^sub>E # zz) sa Q\<close> assm3)
          then have f4: "aa = zz"
            using f2 f1 by (metis (no_types) neq_Nil_conv)
          have "flt2cttobs zra \<noteq> []"
            by (simp add: assm3)
          then show ?thesis
            using f4 f3 f2 by (metis (no_types) Tick aE_is_bullet \<open>\<And>thesis. (\<And>fl. prirel pa fl tt \<and> flt2cttobs fl = aa \<Longrightarrow> thesis) \<Longrightarrow> thesis\<close> assm10 assm3 bullet_left_zero2 flt2cttobs.simps(2) fltrace_concat2.simps(2) local.tt prirel_cons_bullet_iff_exists)
        qed
      qed
 (*     obtain fle2 where "fle2 = \<langle>(\<bullet>,e\<^sub>2)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L> &\<^sub>\<F>\<^sub>\<L> fl" by auto
      then have "prirel pa fle2 zra"
        using assm6 assm7 fl local.tt 
      then show ?thesis
        using \<open>fle2 = \<langle>(\<bullet>,e\<^sub>2)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L> &\<^sub>\<F>\<^sub>\<L> fl\<close> fl no_Tock by auto*)
    next
      case aE_not_bullet:False then 
      show ?thesis 
        proof (cases "maximal(pa,e\<^sub>2)")
          case True
          then show ?thesis
          proof -
            obtain ff :: "'a cttevent fltrace" and aaa :: "'a cttevent acceptance" where
              f1: "flt2cttobs ff = zz \<and> flt2goodTock ff \<and> flt2goodAcceptance ff pa \<and> zra = \<langle>(aaa,e\<^sub>2)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L> &\<^sub>\<F>\<^sub>\<L> ff \<and> (e\<^sub>2 \<in>\<^sub>\<F>\<^sub>\<L> aaa \<or> aaa = \<bullet>)"
              using \<open>\<And>thesis. (\<And>tt aE. flt2cttobs tt = zz \<and> flt2goodTock tt \<and> flt2goodAcceptance tt pa \<and> zra = \<langle>(aE,e\<^sub>2)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L> &\<^sub>\<F>\<^sub>\<L> tt \<and> (e\<^sub>2 \<in>\<^sub>\<F>\<^sub>\<L> aE \<or> aE = \<bullet>) \<Longrightarrow> thesis) \<Longrightarrow> thesis\<close> by blast
            obtain ffa :: "'a cttevent fltrace \<Rightarrow> 'a cttevent fltrace" where
              f2: "\<forall>f. flt2cttobs f \<noteq> zz \<or> \<not> flt2goodTock f \<or> \<not> flt2goodAcceptance f pa \<or> prirel pa (ffa f) f \<and> flt2cttobs (ffa f) = aa"
              by (metis hyp zz_is_cttWF)
            then have "flt2cttobs ((\<bullet>,e\<^sub>2)\<^sub>\<F>\<^sub>\<L> #\<^sub>\<F>\<^sub>\<L> ffa ff) = [e\<^sub>2]\<^sub>E # aa"
              using f1 by (simp add: no_Tock)
            then show ?thesis
              using f2 f1 by (metis (no_types) FL_concat_equiv True acceptance_event acceptance_set prirel.simps(4) prirelacc.simps(1))
          qed
        next
          case False
          then show ?thesis
          proof (cases "e\<^sub>2")
                case (Event x1)
                have "zra = \<langle>(aE,e\<^sub>2)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L> &\<^sub>\<F>\<^sub>\<L> tt"
                  using tt by auto
                have "flt2goodAcceptance (\<langle>(aE,e\<^sub>2)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L> &\<^sub>\<F>\<^sub>\<L> tt) pa"
                  using tt assm9 by blast
                then have "flt2goodAcceptance \<langle>(aE,e\<^sub>2)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L> pa"
                  using tt False assm9 flt2goodAcceptance_pair_consFL
                  by (metis Event aE_not_bullet)
                then have "\<not>(\<exists>b. b \<in>\<^sub>\<F>\<^sub>\<L> aE \<and> Event x1 <\<^sup>*pa b)"
                  using tt Event aE_not_bullet apply auto
                  by (metis False acceptance_event assm10)
                then have "Event x1 \<in>\<^sub>\<F>\<^sub>\<L> [{a. a \<in>\<^sub>\<F>\<^sub>\<L> aE \<and> \<not>(\<exists>b. b\<in>\<^sub>\<F>\<^sub>\<L>aE \<and> a <\<^sup>*pa b)}]\<^sub>\<F>\<^sub>\<L>"
                  using assm7 assm8
                  using Event aE_not_bullet local.tt by auto
                then obtain fle2 where fle2:
                  "fle2 = \<langle>([{a. a \<in>\<^sub>\<F>\<^sub>\<L> aE \<and> \<not>(\<exists>b. b\<in>\<^sub>\<F>\<^sub>\<L>aE \<and> a <\<^sup>*pa b)}]\<^sub>\<F>\<^sub>\<L>,Event x1)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L> &\<^sub>\<F>\<^sub>\<L> fl 
                   \<and> Event x1 \<in>\<^sub>\<F>\<^sub>\<L> [{a. a \<in>\<^sub>\<F>\<^sub>\<L> aE \<and> \<not>(\<exists>b. b\<in>\<^sub>\<F>\<^sub>\<L>aE \<and> a <\<^sup>*pa b)}]\<^sub>\<F>\<^sub>\<L>"
                  by auto
                then have "prirel pa fle2 zra"
                  using tt fl apply auto
                  apply (smt Collect_cong aE_not_bullet acceptance_set acceptances_same_set mem_Collect_eq prirelacc.simps(2))
                  by (smt Collect_cong Event FL_concat_equiv aE_not_bullet acceptance.distinct(1) acceptance_event acceptance_set fl local.tt prirel.simps(4) prirelacc_acceptances_eq)
                then show ?thesis
                  using Event fl fle2 by auto
              next
                case Tock
                then show ?thesis 
                  using no_Tock by blast
              next
                case Tick
                then show ?thesis 
                  using False assm10 by blast
              qed
        qed 
   (*Probably works, just neet to tweak it:
   then obtain fle2 where fle2:"fle2 = \<langle>([{a. a \<in>\<^sub>\<F>\<^sub>\<L> aE \<and> \<not>(\<exists>b. b\<in>\<^sub>\<F>\<^sub>\<L>aE \<and> a <\<^sup>*pa b)}]\<^sub>\<F>\<^sub>\<L>,e\<^sub>2)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L> &\<^sub>\<F>\<^sub>\<L> fl \<and> e\<^sub>2 \<in>\<^sub>\<F>\<^sub>\<L> [{a. a \<in>\<^sub>\<F>\<^sub>\<L> aE \<and> \<not>(\<exists>b. b\<in>\<^sub>\<F>\<^sub>\<L>aE \<and> a <\<^sup>*pa b)}]\<^sub>\<F>\<^sub>\<L>"
        using assm6 local.tt some_higher_not_maximal apply auto  by fastforce
      then have "prirel pa fle2 zra"
        using False fl tt by (cases aE, auto)
      then show ?thesis
        using fl fle2 no_Tock by auto
    qed*)
         
      qed
    qed
  qed

lemma pp2:
  assumes "prirelRef p xs ys s P" "CT3_trace ys" "cttWF ys"
  shows "\<exists>fl zr. prirel p fl zr \<and> (flt2cttobs fl) = xs \<and> (flt2cttobs zr) = ys"
  using assms proof (induct p xs ys s P rule:prirelRef.induct, auto)
  fix pa::"'a cttevent partialorder"
  show "\<exists>fl zr. prirel pa fl zr \<and> flt2cttobs fl = [] \<and> flt2cttobs zr = []"
    by (meson flt2cttobs.simps(1) prirel.simps(1) prirelacc.simps(1))
next
  fix pa::"'a cttevent partialorder"
  fix S
  show "\<exists>fl zr. prirel pa fl zr \<and> flt2cttobs fl = [[prirelref pa S]\<^sub>R] \<and> flt2cttobs zr = [[S]\<^sub>R]"
    apply (rule exI[where x="\<langle>[{x. x \<notin> (prirelref pa S)}]\<^sub>\<F>\<^sub>\<L>\<rangle>\<^sub>\<F>\<^sub>\<L>"])
    apply (rule exI[where x="\<langle>[{x. x \<notin> S}]\<^sub>\<F>\<^sub>\<L>\<rangle>\<^sub>\<F>\<^sub>\<L>"])
    unfolding prirelref_def by auto 
next
  fix pa::"'a cttevent partialorder"
  fix S sa Q fl zr
  assume assm1:"prirelRef pa (flt2cttobs fl) (flt2cttobs zr) (sa @ [[S]\<^sub>R, [Tock]\<^sub>E]) Q"
  assume assm2:"prirel pa fl zr"
  assume assm3:"Tock \<notin> prirelref pa S"
  assume assm4:"Tock \<notin> S"
  show "\<exists>fla zra. prirel pa fla zra 
          \<and> flt2cttobs fla = [prirelref pa S]\<^sub>R # [Tock]\<^sub>E # flt2cttobs fl 
          \<and> flt2cttobs zra = [S]\<^sub>R # [Tock]\<^sub>E # flt2cttobs zr"
  proof -
    have "prirelRef pa ([prirelref pa S]\<^sub>R # [Tock]\<^sub>E # (flt2cttobs fl)) 
                       ([S]\<^sub>R # [Tock]\<^sub>E # (flt2cttobs zr)) sa Q"
      by (simp add: assm1 assm3)
    have tocks:"Tock \<in>\<^sub>\<F>\<^sub>\<L> [{x. x \<notin> prirelref pa S}]\<^sub>\<F>\<^sub>\<L>"
               "Tock \<in>\<^sub>\<F>\<^sub>\<L> [{x. x \<notin> S}]\<^sub>\<F>\<^sub>\<L>"
      apply (metis CT3_trace.simps(3) flt2cttobs_is_CT3_trace \<open>prirelRef pa ([prirelref pa S]\<^sub>R # [Tock]\<^sub>E # flt2cttobs fl) ([S]\<^sub>R # [Tock]\<^sub>E # flt2cttobs zr) sa Q\<close> amember.simps(2) mem_Collect_eq xp)
      by (simp_all add:  assm4)

    obtain fla where fla:"fla = \<langle>([{x. x \<notin> prirelref pa S}]\<^sub>\<F>\<^sub>\<L>,Tock)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>" by auto
    obtain zra where zra:"zra = \<langle>([{x. x \<notin> S}]\<^sub>\<F>\<^sub>\<L>,Tock)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>" by auto

    have "flt2cttobs(fla) = [prirelref pa S]\<^sub>R # [Tock]\<^sub>E # Nil"
      using tocks fla by auto
    have "flt2cttobs(zra) = [S]\<^sub>R # [Tock]\<^sub>E # Nil"
      using tocks zra by auto
    have "flt2cttobs(fla &\<^sub>\<F>\<^sub>\<L> fl) = [prirelref pa S]\<^sub>R # [Tock]\<^sub>E # flt2cttobs fl"
      using tocks fla by auto
    have "flt2cttobs(zra &\<^sub>\<F>\<^sub>\<L> zr) = [S]\<^sub>R # [Tock]\<^sub>E # flt2cttobs zr"
      using tocks zra by auto

    have "prirel pa fla zra"
      using tocks fla zra unfolding prirelref_def by auto
    then have "prirel pa (fla &\<^sub>\<F>\<^sub>\<L> fl) (zra &\<^sub>\<F>\<^sub>\<L> zr)"
      using assm2 by (simp add: prirel_extend_both_prefix_imp)

    then have "prirel pa (fla &\<^sub>\<F>\<^sub>\<L> fl) (zra &\<^sub>\<F>\<^sub>\<L> zr) 
                \<and> flt2cttobs(fla &\<^sub>\<F>\<^sub>\<L> fl) = [prirelref pa S]\<^sub>R # [Tock]\<^sub>E # flt2cttobs fl 
                \<and> flt2cttobs(zra &\<^sub>\<F>\<^sub>\<L> zr) = [S]\<^sub>R # [Tock]\<^sub>E # flt2cttobs zr"
      using \<open>flt2cttobs (fla &\<^sub>\<F>\<^sub>\<L> fl) = [prirelref pa S]\<^sub>R # [Tock]\<^sub>E # flt2cttobs fl\<close> \<open>flt2cttobs (zra &\<^sub>\<F>\<^sub>\<L> zr) = [S]\<^sub>R # [Tock]\<^sub>E # flt2cttobs zr\<close> by blast
    then show ?thesis by blast
  qed
next
  fix pa::"'a cttevent partialorder"
  fix aa e\<^sub>2 zz sa Q
  assume assm0:"(cttWF zz \<Longrightarrow> \<exists>fl zr. prirel pa fl zr \<and> flt2cttobs fl = aa \<and> flt2cttobs zr = zz)"
  assume assm1:"prirelRef pa aa zz (sa @ [[e\<^sub>2]\<^sub>E]) Q"
  assume assm2:"maximal(pa,e\<^sub>2)"
  assume assm4:"CT3_trace ([e\<^sub>2]\<^sub>E # zz)"
  assume assm5:"cttWF ([e\<^sub>2]\<^sub>E # zz)"
  from assm5 have "cttWF zz"
    using cttWF.elims(2) cttWF.simps(1) by blast
  then have hyp:"\<exists>fl zr. prirel pa fl zr \<and> flt2cttobs fl = aa \<and> flt2cttobs zr = zz"
    using assm0 assm4 CT3_trace_cons_imp_cons by auto
  from assm5 have e2_not_Tock:"e\<^sub>2 \<noteq> Tock"
    by auto
  
  show "\<exists>fl zr. prirel pa fl zr \<and> flt2cttobs fl = [e\<^sub>2]\<^sub>E # aa \<and> flt2cttobs zr = [e\<^sub>2]\<^sub>E # zz"
  proof -
    from assm1 assm2 have "prirelRef pa ([e\<^sub>2]\<^sub>E # aa) ([e\<^sub>2]\<^sub>E # zz) sa Q"
      by simp

    obtain fla where fla:"fla = \<langle>(\<bullet>,e\<^sub>2)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>" by auto
    then have "flt2cttobs fla = [e\<^sub>2]\<^sub>E # Nil"
      using e2_not_Tock by auto
    from hyp have "\<exists>fl zr. prirel pa fl zr 
            \<and> ((flt2cttobs fla) @ (flt2cttobs fl)) = [e\<^sub>2]\<^sub>E # aa 
            \<and> ((flt2cttobs fla) @ (flt2cttobs zr)) = [e\<^sub>2]\<^sub>E # zz"
      by (simp add: \<open>flt2cttobs fla = [[e\<^sub>2]\<^sub>E]\<close>)
    then have "\<exists>fl zr. prirel pa (\<langle>(\<bullet>,e\<^sub>2)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L> &\<^sub>\<F>\<^sub>\<L> fl) (\<langle>(\<bullet>,e\<^sub>2)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L> &\<^sub>\<F>\<^sub>\<L> zr)
            \<and> ((flt2cttobs fla) @ (flt2cttobs fl)) = [e\<^sub>2]\<^sub>E # aa 
            \<and> ((flt2cttobs fla) @ (flt2cttobs zr)) = [e\<^sub>2]\<^sub>E # zz"
      using assm2 by auto
    then have "\<exists>fl zr. prirel pa (\<langle>(\<bullet>,e\<^sub>2)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L> &\<^sub>\<F>\<^sub>\<L> fl) (\<langle>(\<bullet>,e\<^sub>2)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L> &\<^sub>\<F>\<^sub>\<L> zr)
            \<and> flt2cttobs (fla &\<^sub>\<F>\<^sub>\<L> fl) = [e\<^sub>2]\<^sub>E # aa 
            \<and> flt2cttobs (fla &\<^sub>\<F>\<^sub>\<L> zr) = [e\<^sub>2]\<^sub>E # zz"
      using e2_not_Tock fla by auto
    then show ?thesis
      using fla by blast
  qed
next
  fix pa::"'a cttevent partialorder"
  fix aa e\<^sub>2 zz sa Q Z
  assume assm0:"(cttWF zz \<Longrightarrow> \<exists>fl zr. prirel pa fl zr \<and> flt2cttobs fl = aa \<and> flt2cttobs zr = zz)"

  assume assm2:"CT3_trace ([e\<^sub>2]\<^sub>E # zz)"
  assume assm3:"cttWF ([e\<^sub>2]\<^sub>E # zz)"
  assume assm4:"prirelRef pa aa zz (sa @ [[e\<^sub>2]\<^sub>E]) Q"
  assume assm5:"sa @ [[Z]\<^sub>R] \<in> Q"
  assume assm6:"\<forall>b. b \<in> Z \<or> \<not> e\<^sub>2 <\<^sup>*pa b"
  from  assm2 have CT3_traces:
      "CT3_trace zz"
    using CT3_trace_cons_imp_cons by blast
  from assm3 have "cttWF zz"
    using cttWF.elims(2) cttWF.simps(1) by blast
  
  then have hyp:"\<exists>fl zr. prirel pa fl zr \<and> flt2cttobs fl = aa \<and> flt2cttobs zr = zz"
    using CT3_traces assm0 by auto

  from assm3 have e2_not_Tock:"e\<^sub>2 \<noteq> Tock"
    by auto

  show "\<exists>fl zr. prirel pa fl zr \<and> flt2cttobs fl = [e\<^sub>2]\<^sub>E # aa \<and> flt2cttobs zr = [e\<^sub>2]\<^sub>E # zz"
  proof -
    from assm4 assm5 assm6 have "prirelRef pa ([e\<^sub>2]\<^sub>E # aa) ([e\<^sub>2]\<^sub>E # zz) sa Q"
      by auto
    obtain fla where fla:"fla = \<langle>([{e\<^sub>2}]\<^sub>\<F>\<^sub>\<L>,e\<^sub>2)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>" by auto
    then have "flt2cttobs fla = [e\<^sub>2]\<^sub>E # Nil"
      using e2_not_Tock by auto
    from hyp have "\<exists>fl zr. prirel pa fl zr 
            \<and> ((flt2cttobs fla) @ (flt2cttobs fl)) = [e\<^sub>2]\<^sub>E # aa 
            \<and> ((flt2cttobs fla) @ (flt2cttobs zr)) = [e\<^sub>2]\<^sub>E # zz"
      by (simp add: \<open>flt2cttobs fla = [[e\<^sub>2]\<^sub>E]\<close>)
    then have "\<exists>fl zr. prirel pa (\<langle>([{e\<^sub>2}]\<^sub>\<F>\<^sub>\<L>,e\<^sub>2)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L> &\<^sub>\<F>\<^sub>\<L> fl) (\<langle>([{e\<^sub>2}]\<^sub>\<F>\<^sub>\<L>,e\<^sub>2)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L> &\<^sub>\<F>\<^sub>\<L> zr)
            \<and> ((flt2cttobs fla) @ (flt2cttobs fl)) = [e\<^sub>2]\<^sub>E # aa 
            \<and> ((flt2cttobs fla) @ (flt2cttobs zr)) = [e\<^sub>2]\<^sub>E # zz"
      using assm4 assm5 assm6 
      by auto
    then have "\<exists>fl zr. prirel pa (\<langle>([{e\<^sub>2}]\<^sub>\<F>\<^sub>\<L>,e\<^sub>2)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L> &\<^sub>\<F>\<^sub>\<L> fl) (\<langle>([{e\<^sub>2}]\<^sub>\<F>\<^sub>\<L>,e\<^sub>2)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L> &\<^sub>\<F>\<^sub>\<L> zr)
            \<and> flt2cttobs (fla &\<^sub>\<F>\<^sub>\<L> fl) = [e\<^sub>2]\<^sub>E # aa 
            \<and> flt2cttobs (fla &\<^sub>\<F>\<^sub>\<L> zr) = [e\<^sub>2]\<^sub>E # zz"
      using e2_not_Tock fla by auto
    then show ?thesis
      using fla by blast
  qed
qed

lemma prirelRef_same_length:
  assumes "prirelRef p xs ys s P"
  shows "size xs = size ys"
  using assms by (induct p xs ys s P rule:prirelRef.induct, auto)

thm rev_induct

lemma pp21:
  assumes "prirelRef p xs ys s P" "CT3_trace ys" "cttWF ys" 
          "CT0 P" "CT1 P" "CTTickTrace ys"
  shows "\<exists>fl\<^sub>0 fl zr. prirel p fl zr \<and> (flt2cttobs fl) = xs \<and> (flt2cttobs zr) = ys \<and> zr \<in> fl\<^sub>0 \<and> FLTick0 Tick fl\<^sub>0 \<and> FL1 fl\<^sub>0"
  using assms 
    sorry
(*proof (induct p xs ys s P rule:prirelRef.induct, auto)
  fix pa::"'a cttevent partialorder"
  fix Q::"'a cttobs list set"
  assume assm1:"CT0 Q"
  assume assm2:"CT1 Q"
  show "\<exists>fl\<^sub>0 fl zr. prirel pa fl zr \<and> flt2cttobs fl = [] \<and> flt2cttobs zr = [] \<and> zr \<in> fl\<^sub>0 \<and> FLTick0 Tick fl\<^sub>0 \<and> FL1 fl\<^sub>0 \<and> fl2ctt fl\<^sub>0 \<subseteq> Q"
    apply (rule exI[where x="{\<langle>\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>}"], auto)
    unfolding FLTick0_def apply auto
    unfolding FL1_def fl2ctt_def apply auto
    apply (rule exI[where x="\<langle>\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>"], auto)
     apply (metis bullet_left_zero2 dual_order.antisym x_le_x_concat2)
    using assm1 assm2
    using CT0_CT1_empty by blast
next
  fix pa::"'a cttevent partialorder"
  fix S::"'a cttevent set"
  fix Q::"'a cttobs list set"
  assume assm1:"CT0 Q"
  assume assm2:"CT1 Q"
  assume assm3:"Tick \<in> S"
  then have "Tick \<in> prirelref pa S"
    unfolding prirelref_def by auto
  have pp:"prirel pa \<langle>[{fl. fl \<notin> prirelref pa S}]\<^sub>\<F>\<^sub>\<L>\<rangle>\<^sub>\<F>\<^sub>\<L> \<langle>[{zr. zr \<notin> S}]\<^sub>\<F>\<^sub>\<L>\<rangle>\<^sub>\<F>\<^sub>\<L>"
    unfolding prirelref_def by simp
  show "\<exists>fl\<^sub>0 fl zr. prirel pa fl zr \<and> flt2cttobs fl = [[prirelref pa S]\<^sub>R] \<and> flt2cttobs zr = [[S]\<^sub>R] 
    \<and> zr \<in> fl\<^sub>0 \<and> FLTick0 Tick fl\<^sub>0 \<and> FL1 fl\<^sub>0 \<and> fl2ctt fl\<^sub>0 \<subseteq> Q"
    apply (rule exI[where x="{\<langle>\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>,\<langle>[{x. x \<notin> S}]\<^sub>\<F>\<^sub>\<L>\<rangle>\<^sub>\<F>\<^sub>\<L>}"])
    apply (rule exI[where x="\<langle>[{x. x \<notin> (prirelref pa S)}]\<^sub>\<F>\<^sub>\<L>\<rangle>\<^sub>\<F>\<^sub>\<L>"])
    apply (rule exI[where x="\<langle>[{x. x \<notin> S}]\<^sub>\<F>\<^sub>\<L>\<rangle>\<^sub>\<F>\<^sub>\<L>"])
    unfolding prirelref_def apply auto 
    unfolding FLTick0_def using assm3 apply auto
    unfolding FL1_def apply auto
      apply (case_tac s, auto, case_tac x1, auto)
    apply (case_tac s, auto, case_tac x1, auto)
    sledgehammer
next
  fix pa::"'a cttevent partialorder"
  fix S sa Q fl zr
  assume assm1:"prirelRef pa (flt2cttobs fl) (flt2cttobs zr) (sa @ [[S]\<^sub>R, [Tock]\<^sub>E]) Q"
  assume assm2:"prirel pa fl zr"
  assume assm3:"Tock \<notin> prirelref pa S"
  assume assm4:"Tock \<notin> S"
  show "\<exists>fla zra. prirel pa fla zra 
          \<and> flt2cttobs fla = [prirelref pa S]\<^sub>R # [Tock]\<^sub>E # flt2cttobs fl 
          \<and> flt2cttobs zra = [S]\<^sub>R # [Tock]\<^sub>E # flt2cttobs zr"
  proof -
    have "prirelRef pa ([prirelref pa S]\<^sub>R # [Tock]\<^sub>E # (flt2cttobs fl)) 
                       ([S]\<^sub>R # [Tock]\<^sub>E # (flt2cttobs zr)) sa Q"
      by (simp add: assm1 assm3)
    have tocks:"Tock \<in>\<^sub>\<F>\<^sub>\<L> [{x. x \<notin> prirelref pa S}]\<^sub>\<F>\<^sub>\<L>"
               "Tock \<in>\<^sub>\<F>\<^sub>\<L> [{x. x \<notin> S}]\<^sub>\<F>\<^sub>\<L>"
      apply (metis CT3_trace.simps(3) flt2cttobs_is_CT3_trace \<open>prirelRef pa ([prirelref pa S]\<^sub>R # [Tock]\<^sub>E # flt2cttobs fl) ([S]\<^sub>R # [Tock]\<^sub>E # flt2cttobs zr) sa Q\<close> amember.simps(2) mem_Collect_eq xp)
      by (simp_all add:  assm4)

    obtain fla where fla:"fla = \<langle>([{x. x \<notin> prirelref pa S}]\<^sub>\<F>\<^sub>\<L>,Tock)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>" by auto
    obtain zra where zra:"zra = \<langle>([{x. x \<notin> S}]\<^sub>\<F>\<^sub>\<L>,Tock)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>" by auto

    have "flt2cttobs(fla) = [prirelref pa S]\<^sub>R # [Tock]\<^sub>E # Nil"
      using tocks fla by auto
    have "flt2cttobs(zra) = [S]\<^sub>R # [Tock]\<^sub>E # Nil"
      using tocks zra by auto
    have "flt2cttobs(fla &\<^sub>\<F>\<^sub>\<L> fl) = [prirelref pa S]\<^sub>R # [Tock]\<^sub>E # flt2cttobs fl"
      using tocks fla by auto
    have "flt2cttobs(zra &\<^sub>\<F>\<^sub>\<L> zr) = [S]\<^sub>R # [Tock]\<^sub>E # flt2cttobs zr"
      using tocks zra by auto

    have "prirel pa fla zra"
      using tocks fla zra unfolding prirelref_def by auto
    then have "prirel pa (fla &\<^sub>\<F>\<^sub>\<L> fl) (zra &\<^sub>\<F>\<^sub>\<L> zr)"
      using assm2 by (simp add: prirel_extend_both_prefix_imp)

    then have "prirel pa (fla &\<^sub>\<F>\<^sub>\<L> fl) (zra &\<^sub>\<F>\<^sub>\<L> zr) 
                \<and> flt2cttobs(fla &\<^sub>\<F>\<^sub>\<L> fl) = [prirelref pa S]\<^sub>R # [Tock]\<^sub>E # flt2cttobs fl 
                \<and> flt2cttobs(zra &\<^sub>\<F>\<^sub>\<L> zr) = [S]\<^sub>R # [Tock]\<^sub>E # flt2cttobs zr"
      using \<open>flt2cttobs (fla &\<^sub>\<F>\<^sub>\<L> fl) = [prirelref pa S]\<^sub>R # [Tock]\<^sub>E # flt2cttobs fl\<close> \<open>flt2cttobs (zra &\<^sub>\<F>\<^sub>\<L> zr) = [S]\<^sub>R # [Tock]\<^sub>E # flt2cttobs zr\<close> by blast
    then show ?thesis by blast
  qed
next
  fix pa::"'a cttevent partialorder"
  fix aa e\<^sub>2 zz sa Q
  assume assm0:"(cttWF zz \<Longrightarrow> \<exists>fl zr. prirel pa fl zr \<and> flt2cttobs fl = aa \<and> flt2cttobs zr = zz)"
  assume assm1:"prirelRef pa aa zz (sa @ [[e\<^sub>2]\<^sub>E]) Q"
  assume assm2:"maximal(pa,e\<^sub>2)"
  assume assm4:"CT3_trace ([e\<^sub>2]\<^sub>E # zz)"
  assume assm5:"cttWF ([e\<^sub>2]\<^sub>E # zz)"
  from assm5 have "cttWF zz"
    using cttWF.elims(2) cttWF.simps(1) by blast
  then have hyp:"\<exists>fl zr. prirel pa fl zr \<and> flt2cttobs fl = aa \<and> flt2cttobs zr = zz"
    using assm0 assm4 CT3_trace_cons_imp_cons by auto
  from assm5 have e2_not_Tock:"e\<^sub>2 \<noteq> Tock"
    by auto
  
  show "\<exists>fl zr. prirel pa fl zr \<and> flt2cttobs fl = [e\<^sub>2]\<^sub>E # aa \<and> flt2cttobs zr = [e\<^sub>2]\<^sub>E # zz"
  proof -
    from assm1 assm2 have "prirelRef pa ([e\<^sub>2]\<^sub>E # aa) ([e\<^sub>2]\<^sub>E # zz) sa Q"
      by simp

    obtain fla where fla:"fla = \<langle>(\<bullet>,e\<^sub>2)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>" by auto
    then have "flt2cttobs fla = [e\<^sub>2]\<^sub>E # Nil"
      using e2_not_Tock by auto
    from hyp have "\<exists>fl zr. prirel pa fl zr 
            \<and> ((flt2cttobs fla) @ (flt2cttobs fl)) = [e\<^sub>2]\<^sub>E # aa 
            \<and> ((flt2cttobs fla) @ (flt2cttobs zr)) = [e\<^sub>2]\<^sub>E # zz"
      by (simp add: \<open>flt2cttobs fla = [[e\<^sub>2]\<^sub>E]\<close>)
    then have "\<exists>fl zr. prirel pa (\<langle>(\<bullet>,e\<^sub>2)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L> &\<^sub>\<F>\<^sub>\<L> fl) (\<langle>(\<bullet>,e\<^sub>2)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L> &\<^sub>\<F>\<^sub>\<L> zr)
            \<and> ((flt2cttobs fla) @ (flt2cttobs fl)) = [e\<^sub>2]\<^sub>E # aa 
            \<and> ((flt2cttobs fla) @ (flt2cttobs zr)) = [e\<^sub>2]\<^sub>E # zz"
      using assm2 by auto
    then have "\<exists>fl zr. prirel pa (\<langle>(\<bullet>,e\<^sub>2)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L> &\<^sub>\<F>\<^sub>\<L> fl) (\<langle>(\<bullet>,e\<^sub>2)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L> &\<^sub>\<F>\<^sub>\<L> zr)
            \<and> flt2cttobs (fla &\<^sub>\<F>\<^sub>\<L> fl) = [e\<^sub>2]\<^sub>E # aa 
            \<and> flt2cttobs (fla &\<^sub>\<F>\<^sub>\<L> zr) = [e\<^sub>2]\<^sub>E # zz"
      using e2_not_Tock fla by auto
    then show ?thesis
      using fla by blast
  qed
next
  fix pa::"'a cttevent partialorder"
  fix aa e\<^sub>2 zz sa Q Z
  assume assm0:"(cttWF zz \<Longrightarrow> \<exists>fl zr. prirel pa fl zr \<and> flt2cttobs fl = aa \<and> flt2cttobs zr = zz)"

  assume assm2:"CT3_trace ([e\<^sub>2]\<^sub>E # zz)"
  assume assm3:"cttWF ([e\<^sub>2]\<^sub>E # zz)"
  assume assm4:"prirelRef pa aa zz (sa @ [[e\<^sub>2]\<^sub>E]) Q"
  assume assm5:"sa @ [[Z]\<^sub>R] \<in> Q"
  assume assm6:"\<forall>b. b \<in> Z \<or> \<not> e\<^sub>2 <\<^sup>*pa b"
  from  assm2 have CT3_traces:
      "CT3_trace zz"
    using CT3_trace_cons_imp_cons by blast
  from assm3 have "cttWF zz"
    using cttWF.elims(2) cttWF.simps(1) by blast
  
  then have hyp:"\<exists>fl zr. prirel pa fl zr \<and> flt2cttobs fl = aa \<and> flt2cttobs zr = zz"
    using CT3_traces assm0 by auto

  from assm3 have e2_not_Tock:"e\<^sub>2 \<noteq> Tock"
    by auto

  show "\<exists>fl zr. prirel pa fl zr \<and> flt2cttobs fl = [e\<^sub>2]\<^sub>E # aa \<and> flt2cttobs zr = [e\<^sub>2]\<^sub>E # zz"
  proof -
    from assm4 assm5 assm6 have "prirelRef pa ([e\<^sub>2]\<^sub>E # aa) ([e\<^sub>2]\<^sub>E # zz) sa Q"
      by auto
    obtain fla where fla:"fla = \<langle>([{e\<^sub>2}]\<^sub>\<F>\<^sub>\<L>,e\<^sub>2)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>" by auto
    then have "flt2cttobs fla = [e\<^sub>2]\<^sub>E # Nil"
      using e2_not_Tock by auto
    from hyp have "\<exists>fl zr. prirel pa fl zr 
            \<and> ((flt2cttobs fla) @ (flt2cttobs fl)) = [e\<^sub>2]\<^sub>E # aa 
            \<and> ((flt2cttobs fla) @ (flt2cttobs zr)) = [e\<^sub>2]\<^sub>E # zz"
      by (simp add: \<open>flt2cttobs fla = [[e\<^sub>2]\<^sub>E]\<close>)
    then have "\<exists>fl zr. prirel pa (\<langle>([{e\<^sub>2}]\<^sub>\<F>\<^sub>\<L>,e\<^sub>2)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L> &\<^sub>\<F>\<^sub>\<L> fl) (\<langle>([{e\<^sub>2}]\<^sub>\<F>\<^sub>\<L>,e\<^sub>2)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L> &\<^sub>\<F>\<^sub>\<L> zr)
            \<and> ((flt2cttobs fla) @ (flt2cttobs fl)) = [e\<^sub>2]\<^sub>E # aa 
            \<and> ((flt2cttobs fla) @ (flt2cttobs zr)) = [e\<^sub>2]\<^sub>E # zz"
      using assm4 assm5 assm6 
      by auto
    then have "\<exists>fl zr. prirel pa (\<langle>([{e\<^sub>2}]\<^sub>\<F>\<^sub>\<L>,e\<^sub>2)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L> &\<^sub>\<F>\<^sub>\<L> fl) (\<langle>([{e\<^sub>2}]\<^sub>\<F>\<^sub>\<L>,e\<^sub>2)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L> &\<^sub>\<F>\<^sub>\<L> zr)
            \<and> flt2cttobs (fla &\<^sub>\<F>\<^sub>\<L> fl) = [e\<^sub>2]\<^sub>E # aa 
            \<and> flt2cttobs (fla &\<^sub>\<F>\<^sub>\<L> zr) = [e\<^sub>2]\<^sub>E # zz"
      using e2_not_Tock fla by auto
    then show ?thesis
      using fla by blast
  qed
qed*)

lemma pp3:
  assumes "prirelRef p xs ys s P" "CT3_trace ys" "cttWF ys"
          "ys \<in> P" 
    shows "\<exists>Z fl\<^sub>0 fl. prirel p fl Z \<and> Z \<in> fl\<^sub>0 \<and> fl2ctt fl\<^sub>0 \<subseteq> P \<and> flt2cttobs Z \<in> P \<and> flt2cttobs fl = xs"
  using pp2 
  by (smt assms(1) assms(2) assms(3) assms(4) fl2ctt_def mem_Collect_eq singletonD singletonI subsetI)

lemma pp4:
  assumes "prirelRef p xs ys s P" "CT3_trace ys" "cttWF ys"
          "ys \<in> P" "CT1c P" "CT0 P" "CTTickTrace ys" "CTwf P" "CTRMax P" "CT4 P" "CT3 P" "maximal(p,Tick)"
    shows "\<exists>Z fl\<^sub>0 fl. FLTick0 Tick fl\<^sub>0 \<and> FL1 fl\<^sub>0 \<and> prirel p fl Z \<and> Z \<in> fl\<^sub>0 \<and> fl2ctt fl\<^sub>0 \<subseteq> P \<and> flt2cttobs Z \<in> P \<and> flt2cttobs fl = xs"
proof -
  obtain Z where fl:"ys = flt2cttobs Z \<and> flt2goodTock Z  \<and>
        (\<exists>fl\<^sub>0. FLTick0 Tick fl\<^sub>0 \<and> FL1 fl\<^sub>0 \<and> fl2ctt fl\<^sub>0 \<subseteq> P \<and> Z \<in> fl\<^sub>0) \<and> flt2cttobs Z \<in> P
        \<and> CT3_trace ys \<and> cttWF ys \<and> prirelRef p xs ys s P"
    unfolding fl2ctt_def using assms CTwf_1c_3_imp_flt2cttobs_FL1 by blast
  then have "\<exists>fl\<^sub>0. FLTick0 Tick fl\<^sub>0 \<and> FL1 fl\<^sub>0 \<and> fl2ctt fl\<^sub>0 \<subseteq> P \<and> Z \<in> fl\<^sub>0 \<and> flt2cttobs Z \<in> P \<and> flt2cttobs Z = ys
        \<and> CT3_trace ys \<and> cttWF ys \<and> prirelRef p xs ys s P"
    by auto
  then have "\<exists>fl\<^sub>0 fl. FLTick0 Tick fl\<^sub>0 \<and> FL1 fl\<^sub>0 \<and> fl2ctt fl\<^sub>0 \<subseteq> P \<and> flt2cttobs Z \<in> P \<and> flt2cttobs Z = ys 
        \<and> (\<exists>fl zr. prirel p fl Z \<and> flt2cttobs fl = xs)"
    using pp20 
    using assms   by blast

(* The key result we wish to establish is: *)
lemma
  fixes P :: "('e cttobs) list set"
  assumes CT0_healthy: "CT0 P" 
      and CTwf_healthy: "CTwf P" 
      and CT1c_healthy: "CT1c P"
      and CT3_healthy:  "CT3 P"
      and CTRMax_healthy: "CTRMax P"
      and CT4_healthy: "CT4 P"
  shows "fl2ctt(pri p (ctt2fl P)) = priNS p P"
  unfolding fl2ctt_def ctt2fl_def apply auto
proof -
  have "fl2ctt(pri p (ctt2fl P)) = {flt2cttobs fl|fl. fl \<in> (pri p (ctt2fl P)) \<and> flt2goodTock fl} \<union> {[]}"
    using fl2ctt_FL0_FL1_flt2goodTock
    by (simp add: fl2ctt_FL0_FL1_flt2goodTock CT0_healthy CT1c_healthy CTockTick_FL.FL0_ctt2fl CTockTick_FL_Priority_devel.FL1_ctt2fl pri_FL0 pri_FL1)
  also have "... = {flt2cttobs fl|fl. fl \<in> (pri p (\<Union>{fl. FLTick0 Tick fl \<and> FL1 fl \<and> (fl2ctt fl) \<subseteq> P})) \<and> flt2goodTock fl} \<union> {[]}"
    unfolding ctt2fl_def by auto
  also have "... = {flt2cttobs fl|fl. fl \<in> \<Union>{pri p fl|fl. FLTick0 Tick fl \<and> FL1 fl \<and> (fl2ctt fl) \<subseteq> P} \<and> flt2goodTock fl} \<union> {[]}"
  proof -
    have "pri p (\<Union>{fl. FLTick0 Tick fl \<and> FL1 fl \<and> (fl2ctt fl) \<subseteq> P}) = \<Union>{pri p fl|fl. fl \<in> {fl. FLTick0 Tick fl \<and> FL1 fl \<and> (fl2ctt fl) \<subseteq> P}}"
      using pri_univ_dist by (metis)
    also have "... = \<Union>{pri p fl|fl. FLTick0 Tick fl \<and> FL1 fl \<and> (fl2ctt fl) \<subseteq> P}"
      by auto
    then show ?thesis
      using calculation by auto
  qed
  also have "... = {flt2cttobs fl|fl. \<exists>x. (\<exists>fl. x = pri p fl \<and> FLTick0 Tick fl \<and> FL1 fl \<and> (fl2ctt fl) \<subseteq> P) \<and> fl \<in> x \<and> flt2goodTock fl} \<union> {[]}"
    unfolding fl2ctt_def by auto
  also have "... = {flt2cttobs fl|fl. \<exists>fl\<^sub>0. FLTick0 Tick fl\<^sub>0 \<and> FL1 fl\<^sub>0 \<and> (fl2ctt fl\<^sub>0) \<subseteq> P \<and> (\<exists>Z. prirel p fl Z \<and> Z \<in> fl\<^sub>0) \<and> flt2goodTock fl} \<union> {[]}"
    unfolding pri_def by auto
  also have "... = {ar|ar zr. prirelRef p ar zr [] P \<and> zr \<in> P}"
    using assms apply auto
    using CT0_CT1c_empty prirelRef.simps(1) apply blast

    
    apply (meson flt2cttobs_extn pp)
    using assms pp4 sledgehammer
    by (smt CT3_def CTwf_def FL1_prirel flt2cttobs_flt2goodTock_less_eq_exists)
    by (metis CT3_def CTwf_def FL1_prirel flt2cttobs_flt2goodTock_less_eq_exists)
  then have "... = {flt2cttobs fl|fl. \<exists>fl\<^sub>0. FL1 fl\<^sub>0 \<and> ({flt2cttobs fl|fl. fl \<in> fl\<^sub>0} \<subseteq> P) \<and>
              (\<exists>Z. prirel p fl Z \<and> Z \<in> fl\<^sub>0 \<and> flt2cttobs(Z) \<in> P)}"
  proof -
    have "\<forall>fl fl\<^sub>0. ((FL1 fl\<^sub>0 \<and> (fl2ctt fl\<^sub>0) \<subseteq> P \<and> (\<exists>Z. prirel p fl Z \<and> Z \<in> fl\<^sub>0))
          =
          (FL1 fl\<^sub>0 \<and> ({flt2cttobs fl|fl. fl \<in> fl\<^sub>0} \<subseteq> P) \<and>
              (\<exists>Z. prirel p fl Z \<and> Z \<in> fl\<^sub>0 \<and> flt2cttobs(Z) \<in> P)))"
      by (simp add: flt2cttobs_extn)
    then show ?thesis
      by auto
  qed

  then have "... = {flt2cttobs fl|fl. (\<exists>fl\<^sub>0 Z. prirel p fl Z \<and> Z \<in> fl\<^sub>0 \<and> flt2cttobs(Z) \<in> P)}"
    using assms 
  
  then have "... = {flt2cttobs fl|fl. \<exists>fl\<^sub>0. FL1 fl\<^sub>0 \<and> ({flt2cttobs fl|fl. fl \<in> fl\<^sub>0} \<subseteq> P) \<and>
                prirelRef p xs ys s P \<and> flt2cttobs(fl) = ys}
              (\<exists>Z. prirel p fl Z \<and> Z \<in> fl\<^sub>0 \<and> flt2cttobs(Z) \<in> P)}"

  oops


lemma prirelRef_of_both_flt2cttobs_cons_acceptance_imp_prirel_acceptances:
  assumes "prirelRef p (flt2cttobs (xs &\<^sub>\<F>\<^sub>\<L> \<langle>x,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>)) (flt2cttobs (ys &\<^sub>\<F>\<^sub>\<L> \<langle>y,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>)) s P" 
          "length xs = length ys" (*FIXME: Probably can deduce from the above assumption *)
          "last xs = \<bullet>" "last ys = \<bullet>"
          "flt2goodTock (xs &\<^sub>\<F>\<^sub>\<L> \<langle>x,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>)" "flt2goodS p (ys &\<^sub>\<F>\<^sub>\<L> \<langle>y,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>)" "prirel p xs ys"
          \<comment>\<open>Tick needs to be maximal so that when identifying traces in the FL-model
             we find a prioritisation that is compatible.\<close>
          "maximal(p,Tick)" "tickWF Tick (xs &\<^sub>\<F>\<^sub>\<L> \<langle>x,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>)"
    shows "prirel p (\<langle>x,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>) (\<langle>y,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>)"
  using assms nitpick
proof (induct p xs ys arbitrary:s x y rule:prirel.induct)
case (1 p A Z)
  obtain xA xEvent yA yEvent where 
    xyAE:"(xA,xEvent)\<^sub>\<F>\<^sub>\<L> = x \<and> (xEvent \<in>\<^sub>\<F>\<^sub>\<L> xA \<or> xA = \<bullet>)"
         "(yA,yEvent)\<^sub>\<F>\<^sub>\<L> = y \<and> (yEvent \<in>\<^sub>\<F>\<^sub>\<L> yA \<or> yA = \<bullet>)"
    by (metis Rep_aevent_inverse acceptance.rep_eq event.rep_eq event_in_acceptance prod.collapse)
  from 1 have "A = \<bullet>" "Z = \<bullet>" by auto
  then show ?case
  proof (cases xEvent)
    case xEvent:(Event x1)
    then show ?thesis
      proof (cases yEvent)
        case (Event y1)
        then show ?thesis using 1 xyAE xEvent apply auto
          apply (cases xA, auto)
      next
        case Tock
        then show ?thesis using 1 xyAE xEvent by (cases yA, auto)
      next
        case Tick
        then show ?thesis using 1 xyAE xEvent by auto
      qed
  next
    case xEvent:Tock
    then show ?thesis
      proof (cases yEvent)
        case (Event y1)
        then show ?thesis using 1 xyAE xEvent by (cases xA, auto)
      next
        case Tock
        then have pr:"prirelRef p (flt2cttobs (\<langle>(xA,Tock)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>)) (flt2cttobs (\<langle>(yA,Tock)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>)) s P"
          using 1 xyAE xEvent by auto
        then show ?thesis 
        proof (cases yA)
          case acnil
          then show ?thesis using 1 pr xyAE xEvent Tock by (cases xA, auto)
        next
          case (acset x2)
          then show ?thesis using 1 pr xyAE xEvent Tock unfolding prirelref_def 
            apply auto 
            apply (cases xA, simp)
            by (smt Finite_Linear_Model.last.simps(1) acceptance.simps(3) append_Cons flt2cttobs.simps(1) flt2cttobs_last_tock flt2goodTock.simps(1) fltrace_concat.simps(3) pr prirelRef.simps(3) prirelacc_eq_prirelref_via_flt2cttobs self_append_conv2 xyAE(2))
        qed
      next
        case Tick
        then show ?thesis using 1 xyAE xEvent by (cases xA, auto)
      qed
  next
    case xEvent:Tick
    then show ?thesis 
    proof (cases yEvent)
      case (Event x1)
      then show ?thesis using xEvent 1 xyAE by auto
    next
      case Tock
      then show ?thesis using xEvent 1 xyAE by (cases yA, auto)
    next
      case Tick
      then show ?thesis using xEvent 1 xyAE by auto
    qed
  qed
next
  case (2 p A Z zz)
  then show ?case by auto
next
  case (3 p A aa Z)
  then show ?case by auto
next
  case (4 p A aa Z zz)
  then have "flt2goodTock ((A #\<^sub>\<F>\<^sub>\<L> aa) &\<^sub>\<F>\<^sub>\<L> \<langle>x,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>)"
            "flt2goodTock ((Z #\<^sub>\<F>\<^sub>\<L> zz) &\<^sub>\<F>\<^sub>\<L> \<langle>y,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>)"
    by auto
  from 4 have "prirelRef p (flt2cttobs ((A #\<^sub>\<F>\<^sub>\<L> aa) &\<^sub>\<F>\<^sub>\<L> \<langle>x,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>)) (flt2cttobs ((Z #\<^sub>\<F>\<^sub>\<L> zz) &\<^sub>\<F>\<^sub>\<L> \<langle>y,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>)) s P"
    by auto
  
  then have "prirelRef p (flt2cttobs (aa &\<^sub>\<F>\<^sub>\<L> \<langle>x,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>)) (flt2cttobs (zz &\<^sub>\<F>\<^sub>\<L> \<langle>y,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>)) (s @ flt2cttobs (\<langle>Z,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>))P"
  proof -
    have A:"flt2cttobs ((A #\<^sub>\<F>\<^sub>\<L> aa) &\<^sub>\<F>\<^sub>\<L> \<langle>x,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>) = flt2cttobs (\<langle>A,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>) @ flt2cttobs(aa &\<^sub>\<F>\<^sub>\<L> \<langle>x,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>)"
    proof -
      have "flt2cttobs ((A #\<^sub>\<F>\<^sub>\<L> aa) &\<^sub>\<F>\<^sub>\<L> \<langle>x,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>) = flt2cttobs (A #\<^sub>\<F>\<^sub>\<L> (aa &\<^sub>\<F>\<^sub>\<L> \<langle>x,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>))"
        by simp
      also have "... = flt2cttobs (\<langle>A,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L> &\<^sub>\<F>\<^sub>\<L> (aa &\<^sub>\<F>\<^sub>\<L> \<langle>x,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>))"
        by simp
      also have "... = flt2cttobs (\<langle>A,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>) @ flt2cttobs(aa &\<^sub>\<F>\<^sub>\<L> \<langle>x,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>)"
        using \<open>flt2goodTock ((A #\<^sub>\<F>\<^sub>\<L> aa) &\<^sub>\<F>\<^sub>\<L> \<langle>x,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>)\<close> by auto
      then show ?thesis by auto
    qed

    have Z:"flt2cttobs ((Z #\<^sub>\<F>\<^sub>\<L> zz) &\<^sub>\<F>\<^sub>\<L> \<langle>y,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>) = flt2cttobs (\<langle>Z,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>) @ flt2cttobs(zz &\<^sub>\<F>\<^sub>\<L> \<langle>y,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>)"
    proof -
      have "flt2cttobs ((Z #\<^sub>\<F>\<^sub>\<L> zz) &\<^sub>\<F>\<^sub>\<L> \<langle>y,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>) = flt2cttobs (Z #\<^sub>\<F>\<^sub>\<L> (zz &\<^sub>\<F>\<^sub>\<L> \<langle>y,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>))"
        by simp
      also have "... = flt2cttobs (\<langle>Z,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L> &\<^sub>\<F>\<^sub>\<L> (zz &\<^sub>\<F>\<^sub>\<L> \<langle>y,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>))"
        by simp
      also have "... = flt2cttobs (\<langle>Z,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>) @ flt2cttobs(zz &\<^sub>\<F>\<^sub>\<L> \<langle>y,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>)"
        using \<open>flt2goodTock ((Z #\<^sub>\<F>\<^sub>\<L> zz) &\<^sub>\<F>\<^sub>\<L> \<langle>y,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>)\<close> by auto
      then show ?thesis by auto
    qed

    have "prirelRef p (flt2cttobs (\<langle>A,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>) @ flt2cttobs(aa &\<^sub>\<F>\<^sub>\<L> \<langle>x,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>)) (flt2cttobs (\<langle>Z,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>) @ flt2cttobs(zz &\<^sub>\<F>\<^sub>\<L> \<langle>y,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>)) s P"
      using "4.prems"(1) A Z by auto
    then have "prirelRef p (flt2cttobs(aa &\<^sub>\<F>\<^sub>\<L> \<langle>x,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>)) (flt2cttobs(zz &\<^sub>\<F>\<^sub>\<L> \<langle>y,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>)) (s @ flt2cttobs (\<langle>Z,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>)) P"
      apply auto
         apply (cases A, auto, cases Z, auto)
          apply (case_tac b, auto, case_tac a, auto, case_tac b, auto)
         apply (cases A, auto, cases Z, auto)
          apply (case_tac b, auto, case_tac a, auto)
      using \<open>flt2goodTock ((A #\<^sub>\<F>\<^sub>\<L> aa) &\<^sub>\<F>\<^sub>\<L> \<langle>x,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>)\<close> apply auto
        apply (cases A, auto, cases Z, auto)
         apply (case_tac b, auto, case_tac a, auto, case_tac b, auto)
       apply (cases A, auto, cases Z, auto) 
      using \<open>flt2goodTock ((Z #\<^sub>\<F>\<^sub>\<L> zz) &\<^sub>\<F>\<^sub>\<L> \<langle>y,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>)\<close> apply auto 
       apply (cases A, auto, cases Z, auto)
      by (case_tac b, auto, case_tac a, auto, case_tac b, auto)
    then show ?thesis by auto
  qed 
    then have "prirel p \<langle>x,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L> \<langle>y,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>"
      by (metis "4.hyps" "4.prems"(3) "4.prems"(4) "4.prems"(5) "4.prems"(6) "4.prems"(7) "4.prems"(8) Finite_Linear_Model.last.simps(2) flt2goodS.simps(2) fltrace_concat2.simps(2) prirel_cons_imp2 prirel_same_length)
    then show ?case by auto
qed

lemma prirel_extend_both_consFL:
  assumes "prirel p xs ys" "last xs = \<bullet>" "last ys = \<bullet>" "prirel p \<langle>x\<rangle>\<^sub>\<F>\<^sub>\<L> \<langle>y\<rangle>\<^sub>\<F>\<^sub>\<L>"
  shows "prirel p (xs &\<^sub>\<F>\<^sub>\<L> \<langle>x\<rangle>\<^sub>\<F>\<^sub>\<L>) (ys &\<^sub>\<F>\<^sub>\<L> \<langle>y\<rangle>\<^sub>\<F>\<^sub>\<L>)"
  using assms by (induct p xs ys rule:prirel.induct, auto)

lemma prirelRef_both_cons_extend_refusal_imp_prefix:
  assumes "prirelRef p x (y @ [[ys]\<^sub>R]) zs P" 
  shows "prirelRef p x y zs P"
  using assms apply (induct p x y zs P arbitrary:xs ys rule:prirelRef.induct, auto)
  oops

lemma flt2goodS_cons_imp_prefix [simp]:
  assumes "flt2goodS (ys &\<^sub>\<F>\<^sub>\<L> \<langle>y\<rangle>\<^sub>\<F>\<^sub>\<L>)"
  shows "flt2goodS ys"
  using assms by (induct ys, auto)

lemma flt2goodS_cons_acecptance_imp_prefix [simp]:
  assumes "flt2goodS (ys &\<^sub>\<F>\<^sub>\<L> \<langle>x,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>)"
  shows "flt2goodS ys"
  using assms by (induct ys, auto)

lemma prirel_both_and_both_acceptances_imp_cons_both:
  assumes "prirel p xs ys" "prirel p \<langle>x,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L> \<langle>y,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>"
  shows "prirel p (xs &\<^sub>\<F>\<^sub>\<L> \<langle>x,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>) (ys &\<^sub>\<F>\<^sub>\<L> \<langle>y,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>)"
  using assms apply (induct p xs ys rule:prirel.induct, simp_all)
   apply (case_tac A, simp, case_tac Z, simp)
  apply auto[2]
   apply (case_tac A, simp, case_tac Z, simp)
  by auto

lemma tt2:
  fixes ar ::"'a cttobs list"
  assumes "prirelRef p (flt2cttobs fl) (flt2cttobs zr) [] P" "length fl = length zr"
          "(flt2cttobs zr) \<in> P" "flt2goodTock fl" "CT1c P" (* Can I assume CT1c here? *)
          "maximal(p,Tick)"
    shows "prirel p fl zr \<and> (\<exists>fl\<^sub>0. zr \<in> fl\<^sub>0 \<and> fl2ctt fl\<^sub>0 \<subseteq> P \<and> flt2cttobs zr \<in> P)"
  using assms
proof (induct fl zr rule:ftrace_cons_induct_both_eq_length)
  case 1
  then show ?case
    using assms(2) by blast
next
  case (2 x y)
  then show ?case
    apply (cases y, auto)
       apply (cases x, auto)
    unfolding fl2ctt_def using assms(5) apply (intro exI[where x="{\<langle>\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>}"], simp)
     apply (cases x, simp)
    apply (metis (no_types, lifting) "2.prems"(1) acceptance.distinct(1) flt2cttobs.simps(1) prirelRef.simps(2) prirelacc_eq_prirelref_via_flt2cttobs)
      using "2.prems"(3) by blast
next
  case (3 x y xs ys)
  have flt2cttobs_xs_x:"flt2cttobs (xs &\<^sub>\<F>\<^sub>\<L> \<langle>x\<rangle>\<^sub>\<F>\<^sub>\<L>) = flt2cttobs (xs) @ flt2cttobs (\<langle>x\<rangle>\<^sub>\<F>\<^sub>\<L>)"
    using 3
    by (metis Finite_Linear_Model.last.simps(1) bullet_right_zero2 flt2cttobs_cons_acceptance_eq_cons flt2cttobs_last_fl_not_bullet_dist_list_cons last_bullet_butlast_last last_bullet_then_last_cons)

  from 3 have "flt2goodTock xs"
    using \<open>flt2goodTock (xs &\<^sub>\<F>\<^sub>\<L> \<langle>x\<rangle>\<^sub>\<F>\<^sub>\<L>)\<close>
    by (metis bullet_right_zero2 butlast_last_FL butlast_last_cons2_FL flt2goodTock_extend_consFL_acceptance fltrace_concat.simps(1) fltrace_concat_assoc last_bullet_butlast_last last_butlast_cons_bullet last_fltrace_acceptance)

 (* from 3 have "flt2goodS ys"
    using flt2goodS_cons_imp_prefix by blast
*)
  from 3 have "flt2goodTock (ys &\<^sub>\<F>\<^sub>\<L> \<langle>y\<rangle>\<^sub>\<F>\<^sub>\<L>)"
    using prirelRef_flt2cttobs_both_eq_length_flt2goodTock_both
    by blast
  then have "flt2goodTock ys"
    by (metis "3.hyps"(4) butlast_last_FL flt2goodTock_extend_consFL_acceptance fltrace_concat.simps(1) fltrace_concat_assoc last_bullet_butlast_last)
  then have flt2cttobs_ys_y:"flt2cttobs (ys &\<^sub>\<F>\<^sub>\<L> \<langle>y\<rangle>\<^sub>\<F>\<^sub>\<L>) = flt2cttobs (ys) @ flt2cttobs (\<langle>y\<rangle>\<^sub>\<F>\<^sub>\<L>)"
    using "3.hyps"(4) flt2cttobs_cons_acceptance_eq_cons by blast
  then have "flt2cttobs (ys) @ flt2cttobs (\<langle>y\<rangle>\<^sub>\<F>\<^sub>\<L>) \<in> P"
    using 3
    by presburger
  then have "flt2cttobs ys \<in> P"
    using 3
    using CT1c_prefix_is_in by blast

  then have "prirelRef p (flt2cttobs xs) (flt2cttobs ys) [] P"
  proof - 
    from 3 have "prirelRef p (flt2cttobs (xs &\<^sub>\<F>\<^sub>\<L> \<langle>x\<rangle>\<^sub>\<F>\<^sub>\<L>)) (flt2cttobs (ys &\<^sub>\<F>\<^sub>\<L> \<langle>y\<rangle>\<^sub>\<F>\<^sub>\<L>)) [] P"
      by blast
    (*then have "prirelRef p (flt2cttobs (xs) @ flt2cttobs (\<langle>x\<rangle>\<^sub>\<F>\<^sub>\<L>)) (flt2cttobs (ys) @ flt2cttobs (\<langle>y\<rangle>\<^sub>\<F>\<^sub>\<L>)) [] P"
      using flt2cttobs_ys_y flt2cttobs_xs_x by auto*)
    then show ?thesis using prirelRef_extend_cons_flt2cttobs_both
      using "3.hyps"(3) "3.hyps"(4) by blast
  qed

  then have "prirel p xs ys \<and> (\<exists>fl\<^sub>0. ys \<in> fl\<^sub>0 \<and> fl2ctt fl\<^sub>0 \<subseteq> P \<and> flt2cttobs ys \<in> P)"
    using 3
    using \<open>flt2cttobs ys \<in> P\<close> \<open>flt2goodTock xs\<close> by blast
  then have "prirel p (xs &\<^sub>\<F>\<^sub>\<L> \<langle>x\<rangle>\<^sub>\<F>\<^sub>\<L>) (ys &\<^sub>\<F>\<^sub>\<L> \<langle>y\<rangle>\<^sub>\<F>\<^sub>\<L>)"
    using "3.hyps"(3) "3.hyps"(4) "3.prems"(1) \<open>flt2goodTock xs\<close> \<open>flt2goodTock ys\<close> prirelRef_of_both_flt2cttobs_cons_acceptance_imp_prirel_acceptance prirel_extend_both_consFL by blast
  then show ?case
    by (smt \<open>flt2cttobs ys @ flt2cttobs \<langle>y\<rangle>\<^sub>\<F>\<^sub>\<L> \<in> P\<close> fl2ctt_def flt2cttobs_ys_y mem_Collect_eq singletonD singletonI subsetI)
next
  case (4 x y xs ys)
  from 4 have "prirelRef p (flt2cttobs xs) (flt2cttobs ys) [] P"
    using prirelRef_extend_cons_acceptance_flt2cttobs_both by blast
  from 4 have "flt2cttobs ys \<in> P"
    by (metis CT1c_prefix_is_in flt2cttobs_acceptance_cons_eq_list_cons flt2cttobs_cons_no_extend_not_flt2goodTock)
  from 4 have "flt2goodTock xs"
    using flt2goodTock_cons_imp_prefix by blast
  then have "prirel p xs ys \<and> (\<exists>fl\<^sub>0. ys \<in> fl\<^sub>0 \<and> fl2ctt fl\<^sub>0 \<subseteq> P \<and> flt2cttobs ys \<in> P)"
    using "4.hyps"(1) "4.hyps"(2) \<open>flt2goodTock xs\<close> \<open>flt2cttobs ys \<in> P\<close> \<open>prirelRef p (flt2cttobs xs) (flt2cttobs ys) [] P\<close> assms(5,7) by blast
 then have "prirel p \<langle>x,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L> \<langle>y,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>"                
   using 4 prirelRef_of_both_flt2cttobs_cons_acceptance_imp_prirel_acceptances sledgehammer
then have "prirel p (xs &\<^sub>\<F>\<^sub>\<L> \<langle>x,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>) (ys &\<^sub>\<F>\<^sub>\<L> \<langle>y,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>)"
  then show ?case sorry
qed
(* proof(induct p ar zr "[]::('a cttobs) list" P arbitrary:fl rule:prirelRef.induct, auto) *)


 


lemma flt2cttobs_exists_flt2goodTock_for_cttWF_CT3_trace:
  assumes "cttWF fl" "CT3_trace fl"
  shows "\<exists>zr. (flt2cttobs zr) = fl \<and> flt2goodTock zr"
  using assms
proof (induct fl rule:cttWF.induct, auto)
  show "\<exists>zr. flt2cttobs zr = [] \<and> flt2goodTock zr"
    by (intro exI[where x="\<langle>\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>"], auto)
next
  fix X
  show "\<exists>zr. flt2cttobs zr = [[X]\<^sub>R] \<and> flt2goodTock zr"
    by (intro exI[where x="\<langle>[{x. x \<notin> X}]\<^sub>\<F>\<^sub>\<L>\<rangle>\<^sub>\<F>\<^sub>\<L>"], auto)
next
  show "\<exists>zr. flt2cttobs zr = [[Tick]\<^sub>E] \<and> flt2goodTock zr"
    by (intro exI[where x="\<langle>(\<bullet>,Tick)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>"], auto)
next
  fix e \<sigma>
  assume hyp:"(CT3_trace \<sigma> \<Longrightarrow> \<exists>zr. flt2cttobs zr = \<sigma> \<and> flt2goodTock zr)"
  assume assm1:"cttWF \<sigma>"
  assume assm2:"CT3_trace ([Event e]\<^sub>E # \<sigma>)"
  show "\<exists>zr. flt2cttobs zr = [Event e]\<^sub>E # \<sigma> \<and> flt2goodTock zr"
  proof -
    from assm2 have "CT3_trace \<sigma>"
      using CT3_trace_cons_imp_cons by blast
    then have "\<exists>zr. flt2cttobs zr = \<sigma> \<and> flt2goodTock zr"
      using hyp by auto
    then have "\<exists>zr. flt2cttobs(\<langle>(\<bullet>,Event e)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>) @ flt2cttobs zr = [Event e]\<^sub>E # \<sigma> \<and> flt2goodTock zr"
      by auto
    then have "\<exists>zr. flt2cttobs(\<langle>(\<bullet>,Event e)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L> &\<^sub>\<F>\<^sub>\<L> zr) = [Event e]\<^sub>E # \<sigma> \<and> flt2goodTock (\<langle>(\<bullet>,Event e)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L> &\<^sub>\<F>\<^sub>\<L> zr)"
      by auto
    then show ?thesis by blast
  qed
next
  fix X::"'a cttevent set"
  fix zr::"'a cttevent fltrace"
  assume assm1:"cttWF (flt2cttobs zr)"
  assume assm2:"Tock \<notin> X"
  assume assm3:"CT3_trace (flt2cttobs zr)"
  assume assm4:"flt2goodTock zr"
  show "\<exists>zra. flt2cttobs zra = [X]\<^sub>R # [Tock]\<^sub>E # flt2cttobs zr \<and> flt2goodTock zra"
  proof -
    have "\<exists>zra. flt2cttobs zra = flt2cttobs zr \<and> flt2goodTock zra"
      using assm4 by auto
    then have "\<exists>zra. flt2cttobs(\<langle>([{x. x \<notin> X}]\<^sub>\<F>\<^sub>\<L>,Tock)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>) @ flt2cttobs zra = [X]\<^sub>R # [Tock]\<^sub>E # flt2cttobs zr \<and> flt2goodTock zra"
      using assm2 by auto
    then have "\<exists>zra. flt2cttobs(\<langle>([{x. x \<notin> X}]\<^sub>\<F>\<^sub>\<L>,Tock)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L> &\<^sub>\<F>\<^sub>\<L> zra) = [X]\<^sub>R # [Tock]\<^sub>E # flt2cttobs zr \<and> flt2goodTock (\<langle>([{x. x \<notin> X}]\<^sub>\<F>\<^sub>\<L>,Tock)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L> &\<^sub>\<F>\<^sub>\<L> zra)"
      using assm2 by auto
    then show ?thesis by blast
  qed
qed

lemma prirelRef_of_flt2cttobs_flt2goodTocks_is_eq_length:
  assumes "prirelRef p (flt2cttobs fl) (flt2cttobs zr) s P" "flt2goodTock fl" "flt2goodTock zr" (*"xs = (flt2cttobs fl)" "ys = (flt2cttobs zr)"*) 
  shows "length fl = length zr"
  using assms (* TODO: I'm sure there is a nicer proof... *)
  apply (induct p fl zr arbitrary:s rule:prirel.induct, auto)
  apply (case_tac A, auto, case_tac Z, auto, case_tac b, auto, case_tac a, auto)
     apply (case_tac b, auto, case_tac Z, auto, case_tac b, auto, case_tac a, auto)
    apply (case_tac b, auto, case_tac Z, auto, case_tac A, auto, case_tac b, auto, case_tac a, auto)
  apply (case_tac b, auto, case_tac A, auto, case_tac b, auto, case_tac a, auto)
   apply (case_tac b, auto)
  apply (case_tac A, auto, case_tac Z, auto, case_tac b, auto, case_tac a, auto, case_tac ba, auto, case_tac ab, auto)
       apply (case_tac ab, auto)
      apply (case_tac ab, auto)
  apply (case_tac a, auto, case_tac ba, auto)
     apply (case_tac ab, auto)
  apply (case_tac ba, auto, case_tac ab, auto)
     apply (case_tac a, auto, case_tac ab, auto)
    apply (case_tac a, auto, case_tac ab, auto)
   apply (case_tac b, auto, case_tac ba, auto, case_tac a, auto, case_tac a, auto, case_tac ba, auto)
     apply (case_tac a, auto, case_tac a, auto)
   apply (case_tac ba, auto, case_tac a, auto, case_tac a, auto)
  apply (case_tac b, auto, case_tac Z, auto, case_tac b, auto, case_tac a, auto, case_tac a, auto)
    apply (case_tac a, auto, case_tac b, auto)
  apply (case_tac Z, auto, case_tac b, auto, case_tac a, auto, case_tac a, auto, case_tac a, auto)
  by (case_tac b, auto)


lemma
  assumes "CT1c P" "CT3 P" "CTwf P" "prirelRef p (flt2cttobs fl) zr [] P" "zr \<in> P" "flt2goodTock fl"
  shows "\<exists>Z. prirel p fl Z \<and> (\<exists>fl\<^sub>0. Z \<in> fl\<^sub>0 \<and> fl2ctt fl\<^sub>0 \<subseteq> P \<and> flt2cttobs Z \<in> P)"
proof -
  have "\<exists>zr\<^sub>1. prirelRef p (flt2cttobs fl) (flt2cttobs zr\<^sub>1) [] P \<and> (flt2cttobs zr\<^sub>1) \<in> P \<and> flt2goodTock zr\<^sub>1"
  using assms flt2cttobs_exists_flt2goodTock_for_cttWF_CT3_trace 
    by (metis CT3_def CTwf_def)
  also have "\<exists>zr\<^sub>1. prirelRef p (flt2cttobs fl) (flt2cttobs zr\<^sub>1) [] P \<and> (flt2cttobs zr\<^sub>1) \<in> P \<and> length fl = length zr\<^sub>1 \<and> flt2goodTock zr\<^sub>1"
    using assms(6) calculation prirelRef_of_flt2cttobs_flt2goodTocks_is_eq_length by blast
  then show ?thesis
    using tt2 assms
    by metis
    oops

lemma
  assumes "prirel p xs ys" "flt2goodTock xs" "flt2goodTock ys" "prirelRef p (flt2cttobs (xs &\<^sub>\<F>\<^sub>\<L> \<langle>x\<rangle>\<^sub>\<F>\<^sub>\<L>)) (flt2cttobs (ys &\<^sub>\<F>\<^sub>\<L> \<langle>y\<rangle>\<^sub>\<F>\<^sub>\<L>)) [] P"
  shows "prirel p (xs &\<^sub>\<F>\<^sub>\<L> \<langle>x\<rangle>\<^sub>\<F>\<^sub>\<L>) (ys &\<^sub>\<F>\<^sub>\<L> \<langle>y\<rangle>\<^sub>\<F>\<^sub>\<L>)"
  nitpick[card=4]

lemma
  assumes "length (xs &\<^sub>\<F>\<^sub>\<L> \<langle>x\<rangle>\<^sub>\<F>\<^sub>\<L>) = length (ys &\<^sub>\<F>\<^sub>\<L> \<langle>y\<rangle>\<^sub>\<F>\<^sub>\<L>)" "last xs = \<bullet>" "last ys = \<bullet>" "x = \<bullet>" "xs \<noteq> \<langle>\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>"
  shows "y = \<bullet>"
  nitpick



lemma
  assumes "prirelRef p (x @ [[xs]\<^sub>R]) y zs P" 
  shows "prirelRef p x y zs P"
  using assms apply (induct p x y zs P rule:prirelRef.induct, auto)
  apply (case_tac v, auto)
  apply (case_tac va, auto)
  sledgehammer

lemma
  assumes "prirelRef p x (y @ [[ys]\<^sub>R]) zs P" 
  shows "prirelRef p x y zs P"
  using assms by (induct p x y zs P rule:prirelRef.induct, auto)
  apply (case_tac v, auto)
  apply (case_tac va)
  apply auto[1]

(*
   apply blast
sledgehammer
  by (metis cttWF.simps(10) cttWF.simps(4) cttWF.simps(6) cttevent.exhaust cttobs.inject(1) list.collapse list.inject snoc_eq_iff_butlast)
  by (smt Nil_is_append_conv cttWF.elims(2) cttobs.distinct(1) list.discI list.inject)
  apply (metis cttWF.simps(11) cttWF.simps(12) cttWF.simps(13) cttevent.exhaust cttobs.exhaust prirelRef.simps(4))
  
                   apply (metis append_Nil not_prirelRef_cases prirelRef.simps(1) remdups_adj.cases snoc_eq_iff_butlast)
  apply (case_tac zz, simp)
                  
                  apply (metis List.butlast.simps(2) not_prirelRef_cases prirelRef.simps(1) remdups_adj.cases snoc_eq_iff_butlast)
                  apply (metis append_Cons cttWF.simps(10) cttWF.simps(4) cttWF.simps(6) cttevent.exhaust neq_Nil_conv)
                 apply (case_tac va, simp, case_tac ysa, simp, case_tac vb, simp)
  
  apply (smt Nil_is_append_conv cttWF.elims(2) list.discI list.sel(1) list.sel(3) prirelRef.simps(20) prirelRef.simps(29) prirelRef.simps(4) prirelRef.simps(7))
                  apply (case_tac vb, simp)
                  apply auto[1]
                 apply (case_tac vb, simp)
                 apply auto[1]
                apply (case_tac v, simp, case_tac vb, simp, case_tac ysa, simp)
  apply auto[1]

  apply (smt Nil_is_append_conv cttWF.elims(2) list.discI list.sel(3) prirelRef.simps(20) prirelRef.simps(29) prirelRef.simps(4) prirelRef.simps(7))
  
  using cttWF.simps(13) apply blast
  using cttWF.simps(13) apply blast
apply (case_tac vb, simp, case_tac vd, simp, case_tac xsa, simp)
                 apply auto[1]
apply (case_tac x1a, simp, case_tac x1, simp)
  apply auto[1]
sledgehammer
  apply (smt List.butlast.simps(2) Nil_is_append_conv cttWF.elims(2) list.discI prirelRef.simps(20) prirelRef.simps(29) prirelRef.simps(4) prirelRef.simps(7))
    apply (smt cttWF.elims(2) list.discI list.inject prirelRef.simps(20) prirelRef.simps(4) prirelRef.simps(7))
  apply (smt cttWF.elims(2) cttobs.distinct(1) list.sel(1) list.simps(3) prirelRef.simps(21) prirelRef.simps(3) prirelRef.simps(32) prirelRef.simps(4))
    
                      apply (metis cttWF.simps(1) cttWF.simps(10) cttWF.simps(4) cttWF.simps(6) cttevent.exhaust neq_Nil_conv)
                 apply (case_tac va, simp, case_tac ysa, simp, case_tac vb, simp)
  
  apply (smt Nil_is_append_conv cttWF.elims(2) list.discI list.sel(3) prirelRef.simps(20) prirelRef.simps(29) prirelRef.simps(4) prirelRef.simps(7))
  
  using cttWF.simps(13) apply blast
    
  using cttWF.simps(13) apply blast

  apply (case_tac v, simp, case_tac vb, simp, case_tac ysa, simp)
   
   apply (metis cttWF.simps(11) cttWF.simps(12) cttevent.exhaust neq_Nil_conv prirelRef.simps(29) prirelRef.simps(4) snoc_eq_iff_butlast)
   
  using cttWF.simps(13) apply blast
                
  using cttWF.simps(13) apply blast
               apply (case_tac vb, simp, case_tac vd, simp, case_tac xsa, simp)
                 apply auto[1]
  apply (case_tac x1a, simp, case_tac x1, simp)
  apply auto[1]
  sledgehammer
                 apply (smt Nil_is_append_conv cttWF.elims(2) list.discI list.sel(3) prirelRef.simps(20) prirelRef.simps(29) prirelRef.simps(4) prirelRef.simps(7))
   apply (smt List.butlast.simps(2) Nil_is_append_conv cttWF.elims(2) list.discI prirelRef.simps(20) prirelRef.simps(29) prirelRef.simps(4) prirelRef.simps(7)) apply auto

  apply (metis cttWF.simps(4) cttWF.simps(6) cttWF.simps(8) cttevent.exhaust neq_Nil_conv snoc_eq_iff_butlast)

  apply (metis cttWF.simps(10) cttWF.simps(4) cttWF.simps(6) cttevent.exhaust neq_Nil_conv snoc_eq_iff_butlast)  
  apply (metis cttobs.exhaust neq_Nil_conv prirelRef.simps(29) prirelRef.simps(5) prirelRef.simps(7) snoc_eq_iff_butlast)
  apply (simp add:cttWF2_cttWF_imp)  
                      apply (metis cttobs.exhaust prirelRef.simps(29) prirelRef.simps(5) prirelRef.simps(57))
  apply (case_tac v, simp)
    
    apply (metis cttobs.exhaust insert_Nil prirelRef.simps(5) prirelRef.simps(57) prirelRef.simps(6) rotate1.simps(2))
    
    apply simp
    apply (case_tac v, simp)  
  apply (metis cttWF.simps(4) cttWF.simps(8) cttWF2.simps(35) cttWF2_cttWF cttevent.exhaust neq_Nil_conv snoc_eq_iff_butlast)                   apply (smt cttWF.elims(2) list.discI list.sel(3) prirelRef.simps(29) prirelRef.simps(5) prirelRef.simps(56) prirelRef.simps(7))
  apply (case_tac v, simp)  
  apply (metis cttobs.exhaust cttobs.inject(1) prirelRef.simps(29) prirelRef.simps(47) prirelRef.simps(5) rotate1.simps(2))
                    apply simp     
  apply (case_tac v, simp) 
  apply (metis cttobs.exhaust insert_Nil prirelRef.simps(29) prirelRef.simps(5) prirelRef.simps(57) rotate1.simps(2))
                   apply (simp)
                   apply (case_tac va, simp, case_tac vb, simp, case_tac ysa, simp)         
  
  apply (metis cttWF.simps(11) cttWF.simps(12) cttevent.exhaust neq_Nil_conv prirelRef.simps(29) prirelRef.simps(4) snoc_eq_iff_butlast)
                   apply (simp)
                  apply (case_tac va, simp, case_tac vb, simp, case_tac ysa, simp)
  
  using cttWF.simps(13) apply blast
                 apply (case_tac v)
                  apply auto[1]
                 apply (case_tac v, simp, case_tac vb, simp, case_tac ysa, simp)
  *)



lemma 
  fixes ar ::"'a cttobs list"
  assumes "prirelRef p ar zr [] P" "(flt2cttobs fl) = ar" 
          "zr \<in> P" "flt2goodTock fl" "CT1c P" (* Can I assume CT1c here? *)
    shows "\<exists>Z. prirel p fl Z \<and> (\<exists>fl\<^sub>0. Z \<in> fl\<^sub>0 \<and> fl2ctt fl\<^sub>0 \<subseteq> P \<and> flt2cttobs Z \<in> P)"
  using assms 
proof(induct p ar zr "[]::('a cttobs) list" P arbitrary:fl zr rule:prirelRef.induct, auto)

lemma 
  fixes ar ::"'a cttobs list"
  assumes "prirelRef p ar zr [] P" "(flt2cttobs fl) = ar" 
          "zr \<in> P" "flt2goodTock fl" "CT1c P" (* Can I assume CT1c here? *)
    shows "\<exists>Z. prirel p fl Z \<and> (\<exists>fl\<^sub>0. Z \<in> fl\<^sub>0 \<and> fl2ctt fl\<^sub>0 \<subseteq> P \<and> flt2cttobs Z \<in> P)"
  using assms(1,2,4,5)
proof(induct p ar zr "[]::('a cttobs) list" P arbitrary:fl rule:prirelRef.induct, auto)
\<comment> \<open>6 Cases left to be proved, so first case is:\<close>
  fix fla::"'a cttevent fltrace"
  fix pa
  fix Q::"'a cttobs list set"
  assume assm1:"flt2cttobs fla = []"
  assume assm2:"[] \<in> Q"
  assume assm3:"flt2goodTock fla"
  show "\<exists>Z. prirel pa fla Z \<and> (\<exists>fl\<^sub>0. Z \<in> fl\<^sub>0 \<and> fl2ctt fl\<^sub>0 \<subseteq> Q \<and> flt2cttobs Z \<in> Q)"
  proof (cases fla)
    case (Acceptance x1)
    then show ?thesis 
      using assm1 apply (cases x1, auto)
      apply (intro exI[where x="\<langle>\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>"], auto)
      unfolding fl2ctt_def using assm2 by (intro exI[where x="{\<langle>\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>}"], auto)
  next
    case (AEvent x21 x22)
    then have "x21 = (\<bullet>,Tock)\<^sub>\<F>\<^sub>\<L>"
      using assm1
      by (metis Rep_aevent_inverse acceptance.rep_eq event.rep_eq flt2cttobs_consFL_eq_Nil prod.collapse)
    then show ?thesis 
      using assm1 assm3 AEvent by auto
  qed
next
\<comment> \<open>Next case:\<close>
  fix pa R 
  fix Q::"'a cttobs list set" 
  fix fla::"'a cttevent fltrace"
  assume assm1:"flt2cttobs fla = []"
  assume assm2:"[[R]\<^sub>R] \<in> Q"
  assume assm3:"flt2goodTock fla"
  assume assm4:"CT1c Q"
  show "\<exists>Z. prirel pa fla Z \<and> (\<exists>fl\<^sub>0. Z \<in> fl\<^sub>0 \<and> fl2ctt fl\<^sub>0 \<subseteq> Q \<and> flt2cttobs Z \<in> Q)"
  proof (cases fla)
    case (Acceptance x1)
    then show ?thesis
      using assm1 apply (cases x1, auto)
      apply (intro exI[where x="\<langle>\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>"], auto)
      unfolding fl2ctt_def using assm2 apply (intro exI[where x="{\<langle>\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>}"], auto)
      using assm4 by auto
  next
    case (AEvent x21 x22)
    then have "x21 = (\<bullet>,Tock)\<^sub>\<F>\<^sub>\<L>"
    using assm1
      by (metis Rep_aevent_inverse acceptance.rep_eq event.rep_eq flt2cttobs_consFL_eq_Nil prod.collapse)
    then show ?thesis 
      using assm1 assm3 AEvent by auto
  qed
next
  fix pa S 
  fix Q::"'a cttobs list set" 
  fix fla::"'a cttevent fltrace"
  assume assm1:"flt2cttobs fla = [[prirelref pa S]\<^sub>R]"
  assume assm2:"[[S]\<^sub>R] \<in> Q"
  assume assm3:"flt2goodTock fla"
  assume assm4:"CT1c Q"
  show "\<exists>Z. prirel pa fla Z \<and> (\<exists>fl\<^sub>0. Z \<in> fl\<^sub>0 \<and> fl2ctt fl\<^sub>0 \<subseteq> Q \<and> flt2cttobs Z \<in> Q)"
  proof (cases fla)
    case (Acceptance x1)
    then show ?thesis
    proof (cases x1)
      case acnil
      then show ?thesis using assm1 Acceptance by (cases x1, auto)
    next
      case (acset x2)
      have flt2cttobs_SRef:"flt2cttobs (\<langle>[{Z. Z \<notin> S}]\<^sub>\<F>\<^sub>\<L>\<rangle>\<^sub>\<F>\<^sub>\<L>) = [[S]\<^sub>R]" by auto

      from acset have "flt2cttobs (\<langle>[x2]\<^sub>\<F>\<^sub>\<L>\<rangle>\<^sub>\<F>\<^sub>\<L>) = [[prirelref pa S]\<^sub>R]"
        using Acceptance assm1 by auto
      then have px2S:"prirel pa \<langle>[x2]\<^sub>\<F>\<^sub>\<L>\<rangle>\<^sub>\<F>\<^sub>\<L> \<langle>[{Z. Z \<notin> S}]\<^sub>\<F>\<^sub>\<L>\<rangle>\<^sub>\<F>\<^sub>\<L>"
      proof -
        have "flt2cttobs \<langle>[x2]\<^sub>\<F>\<^sub>\<L>\<rangle>\<^sub>\<F>\<^sub>\<L> = [[{c. c \<in>\<^sub>\<F>\<^sub>\<L> [{c. c \<notin> S}]\<^sub>\<F>\<^sub>\<L> \<longrightarrow> (\<exists>ca. ca \<in>\<^sub>\<F>\<^sub>\<L> [{c. c \<notin> S}]\<^sub>\<F>\<^sub>\<L> \<and> c <\<^sup>*pa ca)}]\<^sub>R]"
          using \<open>flt2cttobs \<langle>[x2]\<^sub>\<F>\<^sub>\<L>\<rangle>\<^sub>\<F>\<^sub>\<L> = [[prirelref pa S]\<^sub>R]\<close> prirelref_def by auto
          then show ?thesis
            by (simp add: flt2cttobs_base_Z_prirelacc_iff)
        qed
      then have "fl2ctt {\<langle>[{Z. Z \<notin> S}]\<^sub>\<F>\<^sub>\<L>\<rangle>\<^sub>\<F>\<^sub>\<L>} \<subseteq> Q \<and> flt2cttobs(\<langle>[{Z. Z \<notin> S}]\<^sub>\<F>\<^sub>\<L>\<rangle>\<^sub>\<F>\<^sub>\<L>) \<in> Q"
        using flt2cttobs_SRef assm2 unfolding fl2ctt_def by auto
      then show ?thesis using acset Acceptance px2S
        by blast
    qed
  next
    case (AEvent x21 x22)
    then show ?thesis using assm1 apply auto
      by (metis cttobs.distinct(1) list.discI list.inject)
  qed
next
  fix pa aa S zz Q fla
  assume assm1:"flt2cttobs fla = [prirelref pa S]\<^sub>R # [Tock]\<^sub>E # aa"
  assume assm2:"[S]\<^sub>R # [Tock]\<^sub>E # zz \<in> Q"
  assume assm3:"flt2goodTock fla"
  assume assm4:"CT1c Q"
  assume assm5:"prirelRef pa aa zz [[S]\<^sub>R, [Tock]\<^sub>E] Q"
  have "zz \<in> Q"
    sledgehammer
  obtain A xx where Axx:"fla = (A,Tock)\<^sub>\<F>\<^sub>\<L> #\<^sub>\<F>\<^sub>\<L> xx"
    using assm1
    by (metis (no_types, lifting) Rep_aevent_inverse assm3 cttobs.distinct(1) event.rep_eq flt2cttobs.simps(1) flt2cttobs.simps(2) flt2goodTock.elims(2) list.discI list.inject prod.collapse)
  show "\<exists>Z. prirel pa fla Z \<and> (\<exists>fl\<^sub>0. Z \<in> fl\<^sub>0 \<and> fl2ctt fl\<^sub>0 \<subseteq> Q \<and> flt2cttobs Z \<in> Q)"
  proof -
    have "prirel pa fla [S]\<^sub>R # [Tock]\<^sub>E # zz
    using assm1 assm2
    apply (intro exI[where x="\<langle>\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>"], auto)
     apply (case_tac fla, auto)
      apply (case_tac x1, auto)
    apply (case_tac x21, auto)
  case (1 p Q)
  then show ?case
  case (1 p R Q)
  case (3 p R S Q)                     apply auto
  sledgehammer


lemma
  assumes "prirelRef p (flt2cttobs xs) zr [] P \<and> zr \<in> P"
  shows "\<exists>S. prirelRef p ((flt2cttobs xs) @ [[{x. x \<notin> x2}]\<^sub>R]) (zr @ [[S]\<^sub>R]) [] P \<and> (zr @ [[S]\<^sub>R]) \<in> P \<and> prirelref p S = R"
  nitpick

lemma
  assumes "prirel p fl Y" "FL1 fl\<^sub>0"
          "Y \<in> fl\<^sub>0"
          "fl2ctt fl\<^sub>0 \<subseteq> P"
          "flt2cttobs Y \<in> P"
    shows "\<exists>zr. prirelRef p (flt2cttobs fl) zr [] P \<and> zr \<in> P"
  using assms  
proof (induct fl Y rule:ftrace_cons_induct_both_eq_length2)
  case 1
  then show ?case using assms(1) prirel_same_length by blast
next
  case (2 x y)
  then show ?case           
    apply (cases y, auto)
    apply (rule exI[where x="[]"], auto)
      apply (cases x, auto)
     apply (rule exI[where x="[]"], auto)
    apply (metis (mono_tags, lifting) FL0_FL1_bullet_in_so contra_subsetD fl2ctt_def flt2cttobs.simps(1) mem_Collect_eq)
     apply (cases x, auto)
    apply (rule_tac x="[[{z. z \<notin> x2}]\<^sub>R]" in exI, auto)
    unfolding prirelref_def by auto
next
  case (3 x y xs ys)
  then have "xs = xs &\<^sub>\<F>\<^sub>\<L> \<langle>x\<rangle>\<^sub>\<F>\<^sub>\<L>" "ys = ys &\<^sub>\<F>\<^sub>\<L> \<langle>y\<rangle>\<^sub>\<F>\<^sub>\<L>"
    by (simp_all add: concat_FL_last_not_bullet_absorb)
  then show ?case using 3 by auto
next
  case (4 x y xs ys)
  then have prirelRef:"\<exists>zr. prirelRef p (flt2cttobs xs) zr [] P \<and> zr \<in> P"
    by (metis (mono_tags, lifting) flt2cttobs_extn mem_Collect_eq subset_eq x_le_concat2_FL1 prirel_cons_eq_length_imp_prirel_eq_prefix)
  then show ?case using 4
  proof (cases "flt2goodTock xs")
    case True
    then have "flt2goodTock ys"
      using 4 prirel_cons_eq_length_imp_prirel_eq_prefix prirel_flt2goodTock_tgt_imp_src by blast
    then have "flt2cttobs (ys) @ flt2cttobs(\<langle>y\<rangle>\<^sub>\<F>\<^sub>\<L>) \<in> P"
      using 4 by (simp add: flt2cttobs_cons_acceptance_eq_cons)
    then show ?thesis using 4
    proof (cases x)
      case acnil
      then show ?thesis using 4 prirelRef by auto
    next
      case (acset x2)
      then have "\<exists>zr. prirelRef p ((flt2cttobs xs) @ [[{x. x \<notin> x2}]\<^sub>R]) zr [] P \<and> zr \<in> P"
      then show ?thesis using 4 apply auto
    qed
      sorry
  next
    case False
    then show ?thesis
      by (simp add: flt2cttobs_cons_no_extend_not_flt2goodTock prirelRef)   
  qed

  proof (cases "flt2goodTock ys")
    case True
    then show ?thesis using 4
    proof (cases "flt2goodTock xs")
      case True
      then obtain xA xY where xAY:"x = [xA]\<^sub>\<F>\<^sub>\<L> \<and> y = [xY]\<^sub>\<F>\<^sub>\<L>"
          
      then show ?thesis using 4
        apply (cases x, auto)
    next
      case False
      then show ?thesis sorry
    qed
  next
    case False
    then show ?thesis using 4
      by (metis flt2cttobs_cons_no_extend_not_flt2goodTock prirelRef prirel_cons_eq_length_imp_prirel_eq_prefix prirel_flt2goodTock_tgt_imp_src)
  qed
    
  then show ?case
    proof (cases "last xs\<noteq>\<bullet>")
      case True
      then have xs_eq:"xs = xs &\<^sub>\<F>\<^sub>\<L> \<langle>x\<rangle>\<^sub>\<F>\<^sub>\<L>"
        by (simp add: concat_FL_last_not_bullet_absorb)
      then show ?thesis
      proof (cases "last ys\<noteq>\<bullet>")
        case True
        then have "ys = ys &\<^sub>\<F>\<^sub>\<L> \<langle>y\<rangle>\<^sub>\<F>\<^sub>\<L>"
          by (simp add: concat_FL_last_not_bullet_absorb)
        then show ?thesis using xs_eq 3 by auto
      next
        case False
          then have "prirelRef p (flt2cttobs xs) (flt2cttobs ys) [] P"
              using xs_eq 3
              using "4.hyps"(3) True by blast

        then show ?thesis using xs_eq 3 apply auto
      qed
        
        using 3 apply auto
    next
      case False
      then show ?thesis sorry
    qed
    apply (cases x, auto)
    apply (cases y, auto)
    sledgehammer[debug=true]
next
  case (5 x y xs ys)
  then have "prirelRef p (flt2cttobs xs) (flt2cttobs ys) [] P"
    using prirel_cons_eq_length_imp
    by (metis (mono_tags, lifting) flt2cttobs_extn mem_Collect_eq subset_eq x_le_concat2_FL1)
  then show ?case
    proof (cases "last xs\<noteq>\<bullet>")
      case True
      then have "xs = xs &\<^sub>\<F>\<^sub>\<L> \<langle>x,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>" "ys = ys &\<^sub>\<F>\<^sub>\<L> \<langle>x,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>"
        apply (simp add: concat_FL_last_not_bullet_absorb)
        by (metis "4.hyps"(2) "4.prems"(1) True concat_FL_last_not_bullet_absorb prirel_cons_eq_length_imp_prirel_acceptances_last_bullet_eq)
      then show ?thesis using 4 True apply auto
        by (metis concat_FL_last_not_bullet_absorb prirel_cons_eq_length_imp_prirel_acceptances_last_bullet_eq)
    next
      case False
      then have "prirel p \<langle>x,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L> \<langle>y,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>"
        using "4.hyps"(2) "4.prems"(1) prirel_cons_eq_length_imp_prirel_acceptances by blast
      then have "prirelRef p ((flt2cttobs xs) @ (flt2cttobs \<langle>x,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>)) ((flt2cttobs ys) @ (flt2cttobs \<langle>y,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>)) [] P"
        
      then show ?thesis using 4 sorry
    qed 
qed


lemma
  assumes "prirel p fl Y" "FL1 fl\<^sub>0"
          "Y \<in> fl\<^sub>0"
          "fl2ctt fl\<^sub>0 \<subseteq> P"
          "flt2cttobs Y \<in> P"
    shows "\<exists>zr. prirelRef p (flt2cttobs fl) zr [] P \<and> zr \<in> P"
  using assms                   
proof (induct fl Y rule:ftrace_cons_induct_both_eq_length)
  case 1
  then show ?case using assms(1) prirel_same_length by blast
next
  case (2 x y)
  then show ?case sorry
next
  case (3 x y xs ys)
  then show ?case sorry
next
  case (4 x y xs ys)
  then obtain xA xEvent where xAE:"x = (xA,xEvent)\<^sub>\<F>\<^sub>\<L> \<and> (xEvent \<in>\<^sub>\<F>\<^sub>\<L> xA \<or> xA = \<bullet>)"
    by (smt acceptance_event acceptance_set aevent_less_eq_iff_components event_in_acceptance less_eq_acceptance.elims(3) less_eq_aevent_def order_refl)
  
  (*then have "flt2cttobs ys \<in> P"
      TODO: Introduce such a lemma. It is interesting that Isabelle can find a proof for the
            following, but not for this! Although it would seem from the hypothesis one would need this as well. *)
    (* by (metis FL1_def flt2cttobs_extn mem_Collect_eq order_refl subset_eq x_le_x_concat2) *)
  from 4 have "\<exists>zr. prirelRef p (flt2cttobs xs) zr [] P \<and> zr \<in> P"
    using prirel_cons_eq_length_imp
    by (metis (mono_tags, lifting) flt2cttobs_extn mem_Collect_eq subset_eq x_le_concat2_FL1)
  then have "\<exists>zr. prirelRef p (flt2cttobs xs) zr [] P \<and> zr \<in> P"
  then show ?case using 4
  proof (cases "xEvent = Tock \<and> xA \<noteq> \<bullet>")
    case True
    then have "\<exists>zr. prirelRef p ((flt2cttobs xs)@[[{z. z \<notin>\<^sub>\<F>\<^sub>\<L> xA}]\<^sub>R,[Tock]\<^sub>E]) zr [] P \<and> zr \<in> P"
      sledgehammer[debug=true]
    then show ?thesis sorry
  next
    case False
    then show ?thesis sorry
  qed
qed

(*proof (induct fl arbitrary:Z rule:prirel.induct)*)
proof (induct fl arbitrary:Y)
  case (Acceptance x)
  then show ?case 
    apply (cases Y, auto)
     apply (rule exI[where x="[]"], auto)
      apply (metis (mono_tags, lifting) FL0_FL1_bullet_in_so fl2ctt_def flt2cttobs.simps(1) mem_Collect_eq subsetCE)
    apply (cases x, auto, case_tac x1, auto) 
    apply (rule_tac x="[[{z. z \<notin> x2a}]\<^sub>R]" in exI, auto)
    unfolding prirelref_def by auto
next
  case (AEvent x1a fl)
  then obtain aY flY where flY:"Y = aY #\<^sub>\<F>\<^sub>\<L> flY \<and> prirel p fl flY \<and> flY \<in> fl\<^sub>0"
    by (metis fltrace.exhaust mem_Collect_eq prirel.simps(3) prirel_cons_imp2)
    then show ?case
  proof (cases "event x1a = Tock")
    case event_Tock:True
    then show ?thesis
    proof (cases "acceptance x1a \<noteq> \<bullet>")
      case True
      then have "\<exists>zr. prirelRef p (flt2cttobs fl) zr [] P \<and> zr \<in> P"
        using AEvent event_Tock flY sledgehammer[debug=true]
      then show ?thesis using 
    next
      case False
      then show ?thesis sorry
    qed
  next
    case False
    then show ?thesis sorry
  qed
    
    apply auto
    sledgehammer[debug=true]
qed



proof (induct fl arbitrary:Y rule:prirel.induct)
  case (1 p A Z)
  then show ?case 
(*    apply (cases Y)

    apply (cases A, auto, cases Y, auto)
      apply (rule exI[where x="[]"], auto)
     apply (metis (mono_tags, lifting) FL0_FL1_bullet_in_so fl2ctt_def flt2cttobs.simps(1) mem_Collect_eq subsetCE)
      apply (rule_tac x="[[{z. z \<notin>\<^sub>\<F>\<^sub>\<L> Y}]\<^sub>R]" in exI, auto)
  
    apply (metis (mono_tags, lifting) FL0_FL1_bullet_in_so fl2ctt_def flt2cttobs.simps(1) mem_Collect_eq subsetCE)
    apply (cases Z, auto)
    apply (rule_tac x="[[{z. z \<notin> x2a}]\<^sub>R]" in exI, auto)
    unfolding prirelref_def by auto*)
    sorry
next
  case (2 p A Z zz)
  then show ?case by auto
next
  case (3 p A aa Z)
  then show ?case by auto
next
  case (4 p A aa Z zz)
  then show ?case 
    sledgehammer[debug=true]
qed
lemma
  assumes (*"FL1 fl\<^sub>0" "fl2ctt fl\<^sub>0 \<subseteq> P"  *) "fl2ctt fl\<^sub>0 \<subseteq> P" "Z \<in> fl\<^sub>0"
        "flt2cttobs(A) = ar" "flt2cttobs(Z) = zr" "flt2goodTock Z" "flt2goodTock A"
  shows "prirel p A Z = prirelRef p ar zr [] P"
  



lemma
  assumes "prirel p A Z"
  shows "flt2cttobs(A) = ..."

lemma "prirel p \<langle>A\<rangle>\<^sub>\<F>\<^sub>\<L> \<langle>Z\<rangle>\<^sub>\<F>\<^sub>\<L> = (prirelacc p A Z) \<and> x = fl2ctt(\<langle>A\<rangle>\<^sub>\<F>\<^sub>\<L>) \<longleftrightarrow> True"

end