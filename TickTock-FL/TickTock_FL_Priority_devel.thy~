theory
  TickTock_FL_Priority_devel
imports
  TickTock_FL_Priority
begin

fun flt2goodAcceptance :: "('e ttevent) fltrace \<Rightarrow> ('e ttevent) partialorder \<Rightarrow> bool" where
"flt2goodAcceptance \<langle>A\<rangle>\<^sub>\<F>\<^sub>\<L> p = True" |
"flt2goodAcceptance (A #\<^sub>\<F>\<^sub>\<L> fl) p = 
  (if acceptance(A) \<noteq> \<bullet> \<and> \<not>(\<exists>b. b \<in>\<^sub>\<F>\<^sub>\<L> acceptance(A) \<and> event(A) <\<^sup>*p b) 
      then (flt2goodAcceptance fl p) 
      else (if event(A) = Tock \<or> (event(A) \<noteq> Tick \<and> \<not>maximal(p,event(A))) 
            then False else (flt2goodAcceptance fl p)))"

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
   apply (metis amember.elims(2) ttevent.distinct(3) less_eq_acceptance.simps(3) singleton_iff)
  apply (case_tac x21, auto, case_tac x22, auto, case_tac x1, auto)
  by (case_tac x22, auto, case_tac x1, auto)

lemma fl_le_TT1w_ES_Event:
  assumes "fl \<le> \<langle>([{x. x \<notin> ES}]\<^sub>\<F>\<^sub>\<L>,Event ev)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>" "[[Event ev]\<^sub>E] \<in> P" "[[ES]\<^sub>R] \<in> P" "Event ev \<notin> ES" "TT1w P"
  shows "flt2ttobs fl \<in> P"
  using assms apply (cases fl, auto)
  apply (simp_all add: less_eq_aevent_def)
    apply (case_tac x1, auto)
  apply (metis (no_types, lifting) Collect_cong Collect_mem_eq mem_Collect_eq)
   apply (case_tac x21, auto, case_tac x22, auto, case_tac x1, auto)
  by (case_tac x22, auto, case_tac x1, auto)

lemma
  assumes "ys @ [[r1]\<^sub>R] = flt2ttobs fl" "flt2goodAcceptance fl p" "e \<notin> r1" "ys \<noteq> []"
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

lemma prirelRef_extend_cons_flt2ttobs_both:
  assumes "prirelRef p (flt2ttobs (xs &\<^sub>\<F>\<^sub>\<L> \<langle>x\<rangle>\<^sub>\<F>\<^sub>\<L>)) (flt2ttobs (ys &\<^sub>\<F>\<^sub>\<L> \<langle>y\<rangle>\<^sub>\<F>\<^sub>\<L>)) s P" "last xs = \<bullet>" "last ys = \<bullet>"
  shows "prirelRef p (flt2ttobs xs) (flt2ttobs ys) s P"
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

lemma prirelRef_extend_cons_acceptance_flt2ttobs_both:
  assumes "prirelRef p (flt2ttobs (xs &\<^sub>\<F>\<^sub>\<L> \<langle>x,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>)) (flt2ttobs (ys &\<^sub>\<F>\<^sub>\<L> \<langle>y,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>)) s P" "last xs = \<bullet>" "last ys = \<bullet>"
          "length xs = length ys"
  shows "prirelRef p (flt2ttobs xs) (flt2ttobs ys) s P"
  (* FIXME: There must be a nicer proof. *)
  using assms apply (induct p xs ys arbitrary:x y s rule:prirel.induct, auto)
     apply (smt prirelRef.simps(29))
    apply (smt prirelRef.simps(18) prirelRef.simps(19))
   apply (smt prirelRef.simps(46))
  by (smt prirelRef.simps(46))

lemma not_prirelRef_concat_refTock:
  assumes "v \<noteq> []"
  shows "\<not> prirelRef p (v @ [[x]\<^sub>R, [Tock]\<^sub>E]) [[y]\<^sub>R, [Tock]\<^sub>E] z P"
  using assms apply (induct p v "[]:: 'a ttobs list" z P rule:prirelRef.induct, auto)
  apply (case_tac va, auto, case_tac vb, auto, case_tac x1, auto)
   apply (metis append_Cons append_Nil neq_Nil_conv prirelRef.simps(28))
  apply (case_tac va, auto, case_tac va, auto, case_tac a, auto, case_tac x1, auto)
  by (metis append_Cons append_Nil neq_Nil_conv prirelRef.simps(28))

lemma not_prirelRef_concat_refTock':
  assumes "v \<noteq> []"
  shows "\<not> prirelRef p [[y]\<^sub>R, [Tock]\<^sub>E] (v @ [[x]\<^sub>R, [Tock]\<^sub>E]) z P"
  using assms apply (induct p "[]:: 'a ttobs list" v z P rule:prirelRef.induct, auto)
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

lemma ttWF_cons_simp:
  assumes "e\<^sub>2 \<noteq> Tock" "e\<^sub>2 \<noteq> Tick" "ttWF ([e\<^sub>2]\<^sub>E # zz)"
  shows "ttWF(zz)"
  using assms
  using ttWF.elims(2) by blast

lemma prirelRef_concat_dist1:
  assumes "ttWF (ys @ [[S]\<^sub>R,[Tock]\<^sub>E])"
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
          apply (metis ttWF.simps(1) ttWF.simps(4) ttWF.simps(6) ttWF.simps(8) ttevent.exhaust neq_Nil_conv)
         apply (metis append.left_neutral ttWF.simps(4) ttWF.simps(6) ttWF.simps(8) ttWF_prefix_is_ttWF ttevent.exhaust neq_Nil_conv)
        apply (metis Cons_eq_appendI neq_Nil_conv not_prirelRef_concat_refTock)
  using not_prirelRef_concat_refTock apply fastforce
      apply (metis Cons_eq_appendI neq_Nil_conv not_prirelRef_concat_refTock')
     apply (metis Cons_eq_appendI neq_Nil_conv not_prirelRef_concat_refTock')
    apply (induct p xs ys s P rule:prirelRef.induct, auto)
         apply (metis ttWF.simps(1) ttWF.simps(4) ttWF.simps(6) ttWF.simps(8) ttevent.exhaust neq_Nil_conv)
        apply (metis append.left_neutral ttWF.simps(4) ttWF.simps(6) ttWF.simps(8) ttWF_prefix_is_ttWF ttevent.exhaust neq_Nil_conv)
       apply (metis Cons_eq_appendI neq_Nil_conv not_prirelRef_concat_refTock)
      apply (metis Cons_eq_appendI neq_Nil_conv not_prirelRef_concat_refTock) 
     apply (metis Cons_eq_appendI neq_Nil_conv not_prirelRef_concat_refTock')
    apply (metis Cons_eq_appendI neq_Nil_conv not_prirelRef_concat_refTock')
   apply (induct p xs ys s P rule:prirelRef.induct, auto)
        apply (metis ttWF.simps(1) ttWF.simps(10) ttWF.simps(4) ttWF.simps(6) ttevent.exhaust neq_Nil_conv)
       apply (metis ttWF.simps(1) ttWF.simps(10) ttWF.simps(4) ttWF.simps(6) ttevent.exhaust neq_Nil_conv)
      apply (metis Cons_eq_appendI neq_Nil_conv not_prirelRef_concat_refTock)
     apply (metis Cons_eq_appendI neq_Nil_conv not_prirelRef_concat_refTock)
    apply (metis Cons_eq_appendI neq_Nil_conv not_prirelRef_concat_refTock')
   apply (metis Cons_eq_appendI neq_Nil_conv not_prirelRef_concat_refTock')
apply (induct p xs ys s P rule:prirelRef.induct, auto) 
  apply (metis Cons_eq_appendI prirelRef.simps(4) prirelRef_extend_both_tock_refusal_ttWF)
  by (metis ttWF.simps(1) ttWF.simps(10) ttWF.simps(4) ttWF.simps(6) ttevent.exhaust neq_Nil_conv)

lemma not_prirelRef_simp1 [simp]:
  assumes "v \<noteq> []"
  shows "\<not> prirelRef p (v @ [a,b]) [c,d] s Q"
  using assms using prirelRef_length_eq by fastforce

lemma not_prirelRef_simp2 [simp]:
  shows "\<not> prirelRef p (x # y @ [a,b]) [c,d] s Q"
  using prirelRef_length_eq by fastforce

lemma not_prirelRef_simp2' [simp]:
  shows "\<not> prirelRef p [c,d] (x # y @ [a,b]) s Q"
  using prirelRef_length_eq by fastforce

lemma not_prirelRef_simp3 [simp]:
  shows "\<not> prirelRef p (x # y # z @ [a,b]) [c,d] s Q"
  using prirelRef_length_eq by fastforce

lemma not_prirelRef_simp3' [simp]:
  shows "\<not> prirelRef p [c,d] (x # y # z @ [a,b]) s Q"
  using prirelRef_length_eq by fastforce

lemma not_prirelRef_simp4 [simp]:
  shows "\<not> prirelRef p [a, b, c] (x # y # z @ [w, u]) s Q"
  using prirelRef_length_eq by fastforce

lemma not_prirelRef_simp4' [simp]:
  shows "\<not> prirelRef p (x # y # z @ [w, u]) [a, b, c]  s Q"
  using prirelRef_length_eq by fastforce

lemma prirelRef_concat_dist2:
  assumes "ttWF (ys @ [[S]\<^sub>R,[Tock]\<^sub>E])"
  shows
   "prirelRef p (xs @ [a,b]) (ys @ [[S]\<^sub>R,[Tock]\<^sub>E]) s P
    =
    (prirelRef p xs ys s P \<and> prirelRef p [a,b] [[S]\<^sub>R,[Tock]\<^sub>E] (s @ ys) P)"
  using assms apply auto 
      apply (induct p xs ys s P rule:prirelRef.induct, auto)
  using ttWF.elims(2) apply blast
  using ttWF.elims(2) apply blast
   apply (induct p xs ys s P rule:prirelRef.induct, auto)
  using ttWF.elims(2) apply blast
  using ttWF.elims(2) apply blast
  apply (induct p xs ys s P rule:prirelRef.induct, auto)
  using ttWF.elims(2) apply blast
  using ttWF.elims(2) by blast 

lemma prirelRef_FIXME1:
  assumes "prirelRef p (xs @ [a,b]) (ys @ [[S]\<^sub>R, [Tock]\<^sub>E]) s P" "ttWF (ys @ [[S]\<^sub>R,[Tock]\<^sub>E])"
  shows "prirelRef p [a,b] [[S]\<^sub>R, [Tock]\<^sub>E] (s@ys) P"
  using assms prirelRef_concat_dist2 by (simp add:prirelRef_concat_dist2)

lemma prirelRef_rhs_refTock_imp_no_gt_Tock_pri:
  assumes "prirelRef p ar (ys @ [[r1]\<^sub>R, [Tock]\<^sub>E]) [] P" "ttWF (ys @ [[r1]\<^sub>R, [Tock]\<^sub>E])"
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

lemma flt2goodAcceptance_extend_consFL:
  assumes "flt2goodAcceptance fl p" "e \<in>\<^sub>\<F>\<^sub>\<L> X" "\<not>(\<exists>b. b \<in>\<^sub>\<F>\<^sub>\<L> X \<and> e <\<^sup>*p b)"
  shows "flt2goodAcceptance (fl @\<^sub>\<F>\<^sub>\<L> \<langle>(X,e)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>) p"
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

lemma flt2goodAcceptance_extend_consFL_last_fl_bullet_Tick:
  assumes "flt2goodAcceptance fl p" "last fl = \<bullet>"
  shows "flt2goodAcceptance (fl @\<^sub>\<F>\<^sub>\<L> \<langle>(last fl,Tick)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>) p"
  using assms apply(induct fl p rule:flt2goodAcceptance.induct, auto)
   apply (case_tac A, auto, case_tac a, auto)
   apply (meson acceptance_event amember.simps(2))
  apply (case_tac A, auto, case_tac a, auto)
  by (metis acceptance_event amember.simps(2))

lemma flt2goodAcceptance_extend_consFL_acceptance:
  assumes "flt2goodAcceptance fl p"
  shows "flt2goodAcceptance (fl @\<^sub>\<F>\<^sub>\<L> \<langle>X\<rangle>\<^sub>\<F>\<^sub>\<L>) p"
  using assms apply(induct fl p rule:flt2goodAcceptance.induct, auto)
   apply (case_tac A, auto, case_tac a, auto)
   apply (meson acceptance_event amember.simps(2))
  apply (case_tac A, auto, case_tac a, auto)
  by (metis acceptance_event amember.simps(2))

lemma prirelRef_nonmax_Tock_imp_exists_refusal:
  assumes "prirelRef p ar (ys @ [[e1]\<^sub>E]) s P" "e1 \<noteq> Tock"
          "ttWF (ys @ [[e1]\<^sub>E])" "\<not>maximal(p,e1)"
  shows "(\<exists>Z. s @ ys @ [[Z]\<^sub>R] \<in> P \<and> e1 \<notin> Z \<and> \<not>(\<exists>b. b \<notin> Z \<and> e1 <\<^sup>*p b))"
  using assms apply(induct p ar ys s P rule:prirelRef.induct, auto)
            apply (metis ttWF.simps(1) ttWF.simps(10) ttWF.simps(6) ttWF_cons_simp neq_Nil_conv)
           apply (metis (full_types) append_Nil assms(2) ttWF.simps(10) ttWF.simps(5) ttWF.simps(6) ttWF_cons_simp ttWF_prefix_is_ttWF list.collapse rotate1.simps(2))
          apply (metis ttobs.exhaust prirelRef.simps(29) prirelRef.simps(4))
         apply (metis ttobs.exhaust prirelRef.simps(29) prirelRef.simps(4))
        apply (metis ttobs.exhaust prirelRef.simps(29) prirelRef.simps(4))
       apply (metis ttobs.exhaust prirelRef.simps(29) prirelRef.simps(4))
      apply (case_tac va, auto, case_tac vb, auto, case_tac x1, auto, case_tac e1, auto)
  using ttWF.elims(2) apply blast
  apply (metis (full_types) TTickTrace.cases ttobs.exhaust list.distinct(1) prirelRef.simps(29) prirelRef.simps(4))
  apply (case_tac v, auto)
  using ttWF.elims(2) by blast+


lemma TTwf_1c_3_imp_flt2ttobs_FL1_mod:
  assumes "x \<in> P" 
      and TTwf_healthy: "TTwf P" 
      and TT1w_healthy: "TT1w P"
      and TT3_healthy:  "TT3 P"
      and TTick_healthy: "TTick P"
      and TT4w_healthy: "TT4w P"
      and pri:"prirelRef p ar x [] P \<and> x \<in> P"
     (* and tick_Max:"maximal(p,Tick)"*)
  shows "\<exists>fl. x = flt2ttobs fl \<and> flt2goodAcceptance fl p \<and> flt2goodTock fl \<and> (\<exists>x. FLTick0 Tick x \<and> FL1 x \<and> {flt2ttobs fl |fl. fl \<in> x} \<subseteq> P \<and> fl \<in> x)"
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
    using TT1w_def tt_prefix_concat
    using TT1w_healthy by blast
   
  then have xs_in_P:"xs \<in> P" "ttWF (xs @ [x])"
     apply auto
    using TTwf_def TTwf_healthy xs_x_in_P by blast

  from snoc show ?case
  proof (induct xs rule:rev_induct)
    case Nil
    then show ?case
    proof (cases x)
      case (Ref x1)
      then have "Tick \<in> x1"
        using TTick_def TTick_healthy Nil.prems(8) by blast
      then show ?thesis
          apply (intro exI[where x="\<langle>[{x. x \<notin> x1} - {Tick}]\<^sub>\<F>\<^sub>\<L>\<rangle>\<^sub>\<F>\<^sub>\<L>"], auto)
          using Ref apply auto
           apply (rule exI[where x="{z. z \<le> \<langle>[{z. z \<notin> x1} - {Tick}]\<^sub>\<F>\<^sub>\<L>\<rangle>\<^sub>\<F>\<^sub>\<L>}"], auto)
        unfolding FLTick0_def apply auto
          apply (case_tac x, auto)
        apply (metis (full_types) amember.elims(2) less_eq_acceptance.simps(3) mem_Collect_eq)
        using FL1_def dual_order.trans apply blast
        using fl_le_TT1w using Nil by auto
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
        using fl_le_TT1w using Nil by auto
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
            using ObsEvent Nil by (simp add: fl_le_TT1w_Event)
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
            using TTick_healthy by (metis TTick_def append.left_neutral)
          then show ?thesis using ObsEvent Event False ES
            apply (intro exI[where x="\<langle>([{x. x \<notin> ES}]\<^sub>\<F>\<^sub>\<L>,Event ev)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>"])
            apply (simp add:ObsEvent, auto)
            apply (intro exI[where x="{z. z \<le> \<langle>([{x. x \<notin> ES}]\<^sub>\<F>\<^sub>\<L>,Event ev)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>}"], auto)
              apply (simp add: FLTick0_Tick_Event)
              using FL1_def dual_order.trans apply blast
          using ObsEvent Nil by (simp add: fl_le_TT1w_ES_Event)
      qed
      next
        case Tock
        text \<open> There cannot be a Tock without a refusal before it following ttWF,
               so this case is automatically solved. \<close>
        then show ?thesis
          using Nil.prems(3) ObsEvent
          by (metis TTwf_def Nil.prems(2) append_Nil ttWF.simps(6))
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
          using ObsEvent Nil by (simp add:fl_le_TT1w_Tick)
      qed
    qed
  next
    case yys:(snoc y ys)
    then have prirelRefyys:"prirelRef p ar ((ys @ [y]) @ [x]) [] P \<and> (ys @ [y]) @ [x] \<in> P"
      by auto

    from yys have ys_y_inP:"ys @ [y] \<in> P" using TT1w_def
      by (metis tt_prefix_concat)
    from yys have "prirelRef p (List.butlast ar) (ys @ [y]) [] P"
      using prirelRef_imp_one_butlast_of_prirelRef by blast
    then have ys_y_fl:"\<exists>fl. ys @ [y] = flt2ttobs fl \<and> flt2goodAcceptance fl p \<and> flt2goodTock fl \<and> (\<exists>x. FLTick0 Tick x \<and> FL1 x \<and> {flt2ttobs fl |fl. fl \<in> x} \<subseteq> P \<and> fl \<in> x)"
      using ys_y_inP yys by auto
    then have ys_y_x: "\<exists>fl. ys @ [y] @ [x] = flt2ttobs fl @ [x] \<and> flt2goodAcceptance fl p \<and> flt2goodTock fl \<and> (\<exists>x. FLTick0 Tick x \<and> FL1 x \<and> {flt2ttobs fl |fl. fl \<in> x} \<subseteq> P \<and> fl \<in> x)"
      by auto

    then show ?case
    proof (cases y)
      case r1:(Ref r1)
      then have exp:"\<exists>fl. ys @ [[r1]\<^sub>R] @ [x] = flt2ttobs fl @ [x] \<and> flt2goodAcceptance fl p \<and> (\<exists>x. FLTick0 Tick x \<and> FL1 x \<and> {flt2ttobs fl |fl. fl \<in> x} \<subseteq> P \<and> fl \<in> x)"
        using ys_y_fl by auto

      then show ?thesis
      proof (cases x)
        case (Ref r2) text \<open>Not allowed\<close>
        then have "\<not>ttWF (ys @ [Ref r1, Ref r2])"
          by (induct ys rule:ttWF.induct, auto)
        then have "ys @ [Ref r1, Ref r2] \<notin> P"
          using assms unfolding TTwf_def by auto
        then show ?thesis using Ref r1 yys by auto
      next
        case (ObsEvent e1)
        then show ?thesis
        proof (cases e1)
          case (Event e2)
          then have "\<not>ttWF (ys @ [Ref r1, [Event e2]\<^sub>E])"
            by (induct ys rule:ttWF.induct, auto)
          then show ?thesis
            using assms unfolding TTwf_def
            by (metis Cons_eq_append_conv Event ObsEvent append_eq_appendI r1 ys_y_x yys.prems(2))
        next
          case Tock
          then have tock_not_in_r1: "Tock \<notin> r1"
            using TT3_any_cons_end_tock TT3_healthy ObsEvent r1 yys.prems(2) by auto
          then have r1_good_pri:"\<not>(\<exists>b. b \<notin> r1 \<and> Tock <\<^sup>*p b)"
            using r1 ObsEvent Tock prirelRefyys prirelRef_rhs_refTock_imp_no_gt_Tock_pri
            by (metis TTwf_def TTwf_healthy append.assoc append_Cons append_Nil)
          
          text \<open>Then from the hypothesis we have the case:\<close>

          then obtain fl where fl:"ys @ [Ref r1] = flt2ttobs fl \<and> flt2goodAcceptance fl p \<and> flt2goodTock fl \<and> (\<exists>x. FLTick0 Tick x \<and> FL1 x \<and>  {flt2ttobs fl |fl. fl \<in> x} \<subseteq> P \<and> fl \<in> x)"
            using r1 ys_y_fl by blast
          then have last_fl_acceptance:"last fl = [{x. x \<notin> r1}]\<^sub>\<F>\<^sub>\<L>"
            by (metis (mono_tags, lifting) last_flt2ttobs_eq_ref_imp_last snoc_eq_iff_butlast)
          then have r1_good_pri_acceptance:"\<not>(\<exists>b. b \<in>\<^sub>\<F>\<^sub>\<L> [{x. x \<notin> r1}]\<^sub>\<F>\<^sub>\<L> \<and> e1 <\<^sup>*p b)"
            using ObsEvent Tock r1_good_pri 
            by simp
          then have tock_in_last_fl: "Tock \<in>\<^sub>\<F>\<^sub>\<L> last fl"
            using last_fl_acceptance tock_not_in_r1 by simp
          then have "ys @ [[r1]\<^sub>R] @ [[Tock]\<^sub>E] = flt2ttobs fl @ [[Tock]\<^sub>E] \<and> flt2goodAcceptance fl p \<and> flt2goodTock fl \<and> (\<exists>x. FLTick0 Tick x \<and> FL1 x \<and> {flt2ttobs fl |fl. fl \<in> x} \<subseteq> P \<and> fl \<in> x)"
            by (simp add: fl)
          then have "ys @ [[r1]\<^sub>R] @ [[Tock]\<^sub>E] = flt2ttobs (fl @\<^sub>\<F>\<^sub>\<L> \<langle>(last fl,Tock)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>) \<and> flt2goodAcceptance fl p \<and> flt2goodTock fl \<and> (\<exists>x. FLTick0 Tick x \<and> FL1 x \<and> {flt2ttobs fl |fl. fl \<in> x} \<subseteq> P \<and> fl \<in> x)"
            using tock_in_last_fl by (simp add: flt2ttobs_last_tock fl)

          have "{flt2ttobs fl\<^sub>0|fl\<^sub>0. fl\<^sub>0 \<le> fl} \<subseteq> P"
            using TT1w_healthy 
            using FL1_def fl subset_eq by blast

          have flt2ttobs_strongFL_subset:"{flt2ttobs fl\<^sub>0|fl\<^sub>0. fl\<^sub>0 \<le>\<^sub>\<F>\<^sub>\<L> (fl @\<^sub>\<F>\<^sub>\<L> \<langle>(last fl,Tock)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>)} \<subseteq> P"
            apply auto
            using strong_less_eq_fltrace_imp_flt2ttobs_tt
            by (metis (no_types, lifting) TT1w_def TT1w_healthy ObsEvent Tock \<open>ys @ [[r1]\<^sub>R] @ [[Tock]\<^sub>E] = flt2ttobs (fl @\<^sub>\<F>\<^sub>\<L> \<langle>(Finite_Linear_Model.last fl,Tock)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>) \<and> flt2goodAcceptance fl p \<and> flt2goodTock fl \<and> (\<exists>x. FLTick0 Tick x \<and> FL1 x \<and> {flt2ttobs fl |fl. fl \<in> x} \<subseteq> P \<and> fl \<in> x)\<close> \<open>ys @ [[r1]\<^sub>R] @ [[Tock]\<^sub>E] = flt2ttobs fl @ [[Tock]\<^sub>E] \<and> flt2goodAcceptance fl p \<and> flt2goodTock fl \<and> (\<exists>x. FLTick0 Tick x \<and> FL1 x \<and> {flt2ttobs fl |fl. fl \<in> x} \<subseteq> P \<and> fl \<in> x)\<close> fl r1 yys.prems(2))

          have "(ys @ [[r1]\<^sub>R] @ [[Tock]\<^sub>E] = flt2ttobs(fl @\<^sub>\<F>\<^sub>\<L> \<langle>(last fl,Tock)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>) \<and> flt2goodAcceptance fl p \<and> flt2goodTock fl
                \<and> (\<exists>x. FLTick0 Tick x \<and> FL1 x \<and> {flt2ttobs fl |fl. fl \<in> x} \<subseteq> P \<and> fl \<in> x))"
            using \<open>ys @ [[r1]\<^sub>R] @ [[Tock]\<^sub>E] = flt2ttobs (fl @\<^sub>\<F>\<^sub>\<L> \<langle>(Finite_Linear_Model.last fl,Tock)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>) \<and> flt2goodAcceptance fl p \<and> flt2goodTock fl \<and> (\<exists>x. FLTick0 Tick x \<and> FL1 x \<and> {flt2ttobs fl |fl. fl \<in> x} \<subseteq> P \<and> fl \<in> x)\<close> tock_in_last_fl by blast
          then have 
               "ys @ [[r1]\<^sub>R] @ [[Tock]\<^sub>E] = flt2ttobs (fl @\<^sub>\<F>\<^sub>\<L> \<langle>(last fl,Tock)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>) \<and> flt2goodAcceptance fl p \<and> flt2goodTock fl  
                \<and> (\<exists>x. FLTick0 Tick x \<and> FL1 (x \<union> {fl\<^sub>0. fl\<^sub>0 \<le>\<^sub>\<F>\<^sub>\<L> (fl @\<^sub>\<F>\<^sub>\<L> \<langle>(last fl,Tock)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>)}) \<and> {flt2ttobs fl |fl. fl \<in> x} \<subseteq> P \<and> fl \<in> x)"
            using FL1_extends_strong_less_eq_fltrace_last tock_in_last_fl
            by (metis (mono_tags, lifting) Collect_cong \<open>ys @ [[r1]\<^sub>R] @ [[Tock]\<^sub>E] = flt2ttobs (fl @\<^sub>\<F>\<^sub>\<L> \<langle>(Finite_Linear_Model.last fl,Tock)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>) \<and> flt2goodAcceptance fl p \<and> flt2goodTock fl \<and> (\<exists>x. FLTick0 Tick x \<and> FL1 x \<and> {flt2ttobs fl |fl. fl \<in> x} \<subseteq> P \<and> fl \<in> x)\<close> fl)
          then have 
               "ys @ [[r1]\<^sub>R] @ [[Tock]\<^sub>E] = flt2ttobs (fl @\<^sub>\<F>\<^sub>\<L> \<langle>(last fl,Tock)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>) \<and> flt2goodAcceptance fl p \<and> flt2goodTock fl  
                \<and> (\<exists>x. FLTick0 Tick (x \<union> {fl\<^sub>0. fl\<^sub>0 \<le>\<^sub>\<F>\<^sub>\<L> (fl @\<^sub>\<F>\<^sub>\<L> \<langle>(last fl,Tock)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>)}) 
                        \<and> FL1 (x \<union> {fl\<^sub>0. fl\<^sub>0 \<le>\<^sub>\<F>\<^sub>\<L> (fl @\<^sub>\<F>\<^sub>\<L> \<langle>(last fl,Tock)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>)}) \<and> {flt2ttobs fl |fl. fl \<in> x} \<subseteq> P \<and> fl \<in> x)"
            using FLTick0_extends_strong_less_eq_fltrace_last tock_in_last_fl
            by auto
          then have 
               "ys @ [[r1]\<^sub>R] @ [[Tock]\<^sub>E] = flt2ttobs (fl @\<^sub>\<F>\<^sub>\<L> \<langle>(last fl,Tock)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>) \<and> flt2goodAcceptance fl p \<and> flt2goodTock fl 
                \<and> (\<exists>x. FLTick0 Tick (x \<union> {fl\<^sub>0. fl\<^sub>0 \<le>\<^sub>\<F>\<^sub>\<L> (fl @\<^sub>\<F>\<^sub>\<L> \<langle>(last fl,Tock)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>)}) 
                    \<and> FL1 (x \<union> {fl\<^sub>0. fl\<^sub>0 \<le>\<^sub>\<F>\<^sub>\<L> (fl @\<^sub>\<F>\<^sub>\<L> \<langle>(last fl,Tock)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>)})
                    \<and> {flt2ttobs fl\<^sub>0 |fl\<^sub>0. fl\<^sub>0 \<in> (x \<union> {fl\<^sub>0. fl\<^sub>0 \<le>\<^sub>\<F>\<^sub>\<L> (fl @\<^sub>\<F>\<^sub>\<L> \<langle>(last fl,Tock)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>)})} \<subseteq> P \<and> fl \<in> x)"
            using flt2ttobs_strongFL_subset
            by (smt Un_iff mem_Collect_eq subset_iff)
          then have 
               "ys @ [[r1]\<^sub>R] @ [[Tock]\<^sub>E] = flt2ttobs (fl @\<^sub>\<F>\<^sub>\<L> \<langle>(last fl,Tock)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>) \<and> flt2goodAcceptance fl p \<and> flt2goodTock fl 
                \<and> (\<exists>x. FLTick0 Tick (x \<union> {fl\<^sub>0. fl\<^sub>0 \<le>\<^sub>\<F>\<^sub>\<L> (fl @\<^sub>\<F>\<^sub>\<L> \<langle>(last fl,Tock)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>)}) 
                \<and> FL1 (x \<union> {fl\<^sub>0. fl\<^sub>0 \<le>\<^sub>\<F>\<^sub>\<L> (fl @\<^sub>\<F>\<^sub>\<L> \<langle>(last fl,Tock)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>)})
                \<and> {flt2ttobs fl\<^sub>0 |fl\<^sub>0. fl\<^sub>0 \<in> (x \<union> {fl\<^sub>0. fl\<^sub>0 \<le>\<^sub>\<F>\<^sub>\<L> (fl @\<^sub>\<F>\<^sub>\<L> \<langle>(last fl,Tock)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>)})} \<subseteq> P 
                \<and> fl \<in> x
                \<and> fl @\<^sub>\<F>\<^sub>\<L> \<langle>(last fl,Tock)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L> \<in> (x \<union> {fl\<^sub>0. fl\<^sub>0 \<le>\<^sub>\<F>\<^sub>\<L> (fl @\<^sub>\<F>\<^sub>\<L> \<langle>(last fl,Tock)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>)}))"
            by (simp add: strong_less_eq_fltrace_refl)
          then have 
               "ys @ [[r1]\<^sub>R] @ [[Tock]\<^sub>E] = flt2ttobs (fl @\<^sub>\<F>\<^sub>\<L> \<langle>(last fl,Tock)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>) \<and> flt2goodAcceptance fl p \<and> flt2goodTock fl 
                \<and> (\<exists>z. FLTick0 Tick z \<and> FL1 z
                \<and> {flt2ttobs fl\<^sub>0 |fl\<^sub>0. fl\<^sub>0 \<in> z} \<subseteq> P 
                \<and> fl @\<^sub>\<F>\<^sub>\<L> \<langle>(last fl,Tock)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L> \<in> z)"
            by blast
          then have 
               "ys @ [[r1]\<^sub>R] @ [[Tock]\<^sub>E] = flt2ttobs (fl @\<^sub>\<F>\<^sub>\<L> \<langle>(last fl,Tock)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>) \<and> flt2goodAcceptance fl p \<and> flt2goodTock fl 
                \<and> flt2goodTock (fl @\<^sub>\<F>\<^sub>\<L> \<langle>(last fl,Tock)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>)
                \<and> (\<exists>z. FLTick0 Tick z \<and> FL1 z
                \<and> {flt2ttobs fl\<^sub>0 |fl\<^sub>0. fl\<^sub>0 \<in> z} \<subseteq> P 
                \<and> fl @\<^sub>\<F>\<^sub>\<L> \<langle>(last fl,Tock)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L> \<in> z)"
            using tock_in_last_fl by (simp add:flt2goodTock_extend_consFL_last_fl_e)
          then have 
               "ys @ [[r1]\<^sub>R] @ [[Tock]\<^sub>E] = flt2ttobs (fl @\<^sub>\<F>\<^sub>\<L> \<langle>(last fl,Tock)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>) 
                \<and> flt2goodAcceptance fl p 
                \<and> flt2goodAcceptance (fl @\<^sub>\<F>\<^sub>\<L> \<langle>(last fl,Tock)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>) p
                \<and> flt2goodTock fl 
                \<and> flt2goodTock (fl @\<^sub>\<F>\<^sub>\<L> \<langle>(last fl,Tock)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>)
                \<and> (\<exists>z. FLTick0 Tick z \<and> FL1 z
                \<and> {flt2ttobs fl\<^sub>0 |fl\<^sub>0. fl\<^sub>0 \<in> z} \<subseteq> P 
                \<and> fl @\<^sub>\<F>\<^sub>\<L> \<langle>(last fl,Tock)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L> \<in> z)"
            using flt2goodAcceptance_extend_consFL_last_fl_e
            by (metis (mono_tags, lifting) Tock last_fl_acceptance r1_good_pri_acceptance tock_in_last_fl)
          then have 
               "\<exists>fl. ys @ [[r1]\<^sub>R] @ [[Tock]\<^sub>E] = flt2ttobs fl \<and> flt2goodAcceptance fl p \<and> flt2goodTock fl 
                \<and> (\<exists>z. FLTick0 Tick z \<and> FL1 z \<and> {flt2ttobs fl\<^sub>0 |fl\<^sub>0. fl\<^sub>0 \<in> z} \<subseteq> P \<and> fl \<in> z)"
            by blast
          then show ?thesis using Tock ObsEvent r1 by auto
        next
          case Tick
          then have "\<not>ttWF (ys @ [Ref r1, [Tick]\<^sub>E])"
            by (induct ys rule:ttWF.induct, auto)
          then show ?thesis
            using TTwf_healthy unfolding TTwf_def
            by (metis ObsEvent Tick append.assoc append_Cons append_Nil r1 ys_y_x yys.prems(2))
        qed
      qed
    next
      case e1:(ObsEvent e1)
      text \<open>Then from the hypothesis we have the case:\<close>
      then obtain fl where fl:"ys @ [[e1]\<^sub>E] = flt2ttobs fl \<and> flt2goodAcceptance fl p \<and> flt2goodTock fl \<and> (\<exists>x. FLTick0 Tick x \<and> FL1 x \<and> {flt2ttobs fl |fl. fl \<in> x} \<subseteq> P \<and> fl \<in> x)"
        using ys_y_fl by blast
      then have ys_e1_x:"ys @ [[e1]\<^sub>E] @ [x] = flt2ttobs fl @ [x] \<and> flt2goodAcceptance fl p \<and> flt2goodTock fl \<and> (\<exists>x. FLTick0 Tick x \<and> FL1 x \<and> {flt2ttobs fl |fl. fl \<in> x} \<subseteq> P \<and> fl \<in> x)"
        by auto
      then have last_fl:"last fl = \<bullet>"
        by (metis ttobs.distinct(1) fl flt2ttobs.simps(1) flt2ttobs_last_fl_not_bullet_dist_list_cons last_snoc)

      then show ?thesis
      proof (cases x)
        case e2:(ObsEvent e2)
        then have "ys @ [[e1]\<^sub>E] @ [[e2]\<^sub>E] \<in> P"
          using e1 fl ys_e1_x yys.prems(2) by presburger
        then have "[Tick]\<^sub>E \<notin> set (ys @ [[e1]\<^sub>E])" 
          using TTwf_healthy TTwf_concat_prefix_set_no_Tick
          using e1 e2 yys.prems(2) by blast
        then have Tick_not_in_events_fl: "Tick \<notin> events fl"
          by (simp add: event_not_in_set_of_flt2ttobs_imp_not_in_events fl)
          
        then show ?thesis
        proof (cases e2)
          case (Event e3)
          have "prirelRef p ar (ys @ [[e1]\<^sub>E,[Event e3]\<^sub>E]) [] P \<and> (ys @ [[e1]\<^sub>E,[Event e3]\<^sub>E]) \<in> P"
             using prirelRefyys e1 Event e2 by auto
          then show ?thesis
          proof (cases "maximal(p,Event e3)")
            case True
            then have flt2ttobs_strongFL_subset:"{flt2ttobs fl\<^sub>0|fl\<^sub>0. fl\<^sub>0 \<le>\<^sub>\<F>\<^sub>\<L> (fl @\<^sub>\<F>\<^sub>\<L> \<langle>(last fl,Event e3)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>)} \<subseteq> P"
              apply auto
              using strong_less_eq_fltrace_imp_flt2ttobs_tt
              by (metis (no_types, lifting) TT1w_def TT1w_healthy Event ttevent.simps(3) e1 e2 fl flt2ttobs_last_non_tock last_fl last_snoc yys.prems(2))
          
            from fl have fl_e3: "ys @ [[e1]\<^sub>E] @ [[Event e3]\<^sub>E] = flt2ttobs fl @ [[Event e3]\<^sub>E]
                    \<and> flt2goodAcceptance fl p \<and> flt2goodTock fl \<and> (\<exists>x. FLTick0 Tick x \<and> FL1 x \<and> {flt2ttobs fl\<^sub>0 |fl\<^sub>0. fl\<^sub>0 \<in> x} \<subseteq> P \<and> fl \<in> x)"
              using ys_e1_x by auto
            also have "... =
                    (ys @ [[e1]\<^sub>E] @ [[Event e3]\<^sub>E] = flt2ttobs(fl @\<^sub>\<F>\<^sub>\<L> \<langle>(last fl,Event e3)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>)
                    \<and> flt2goodAcceptance fl p \<and> flt2goodTock fl \<and> (\<exists>x. FLTick0 Tick x \<and> FL1 x \<and> {flt2ttobs fl\<^sub>0 |fl\<^sub>0. fl\<^sub>0 \<in> x} \<subseteq> P \<and> fl \<in> x))"
              proof -
                from fl have "ys @ [[e1]\<^sub>E] = flt2ttobs fl"
                  by auto
                then have "List.last(flt2ttobs fl) = [e1]\<^sub>E"
                  by (metis last_snoc)
                then have "flt2ttobs fl @ [[Event e3]\<^sub>E] = flt2ttobs(fl @\<^sub>\<F>\<^sub>\<L> \<langle>(last fl,Event e3)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>)"
                  using fl last_fl flt2ttobs_last_non_tock
                  by (metis (no_types, lifting) ttevent.distinct(1))
                then show ?thesis using calculation  by auto
              qed
            finally have "
                    ys @ [[e1]\<^sub>E] @ [[Event e3]\<^sub>E] = flt2ttobs(fl @\<^sub>\<F>\<^sub>\<L> \<langle>(last fl,Event e3)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>)
                    \<and> flt2goodAcceptance fl p \<and> flt2goodTock fl 
                    \<and> (\<exists>x. FLTick0 Tick x \<and> FL1 (x \<union> {fl\<^sub>0. fl\<^sub>0 \<le>\<^sub>\<F>\<^sub>\<L> (fl @\<^sub>\<F>\<^sub>\<L> \<langle>(last fl,Event e3)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>)}) 
                        \<and> {flt2ttobs fl\<^sub>0 |fl\<^sub>0. fl\<^sub>0 \<in> x} \<subseteq> P \<and> fl \<in> x)"
                apply auto using FL1_extends_strong_less_eq_fltrace_last_bullet last_fl 
              by fastforce
            then have "
                    ys @ [[e1]\<^sub>E] @ [[Event e3]\<^sub>E] = flt2ttobs(fl @\<^sub>\<F>\<^sub>\<L> \<langle>(last fl,Event e3)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>)
                    \<and> flt2goodAcceptance fl p \<and> flt2goodTock fl 
                    \<and> (\<exists>x. FLTick0 Tick (x \<union> {fl\<^sub>0. fl\<^sub>0 \<le>\<^sub>\<F>\<^sub>\<L> (fl @\<^sub>\<F>\<^sub>\<L> \<langle>(last fl,Event e3)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>)}) 
                        \<and> FL1 (x \<union> {fl\<^sub>0. fl\<^sub>0 \<le>\<^sub>\<F>\<^sub>\<L> (fl @\<^sub>\<F>\<^sub>\<L> \<langle>(last fl,Event e3)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>)}) 
                        \<and> {flt2ttobs fl\<^sub>0 |fl\<^sub>0. fl\<^sub>0 \<in> x} \<subseteq> P \<and> fl \<in> x)"
              apply auto using FL0_Tick_extends_strong_less_eq_fltrace_last_bullet last_fl Tick_not_in_events_fl
              by blast
           then have "
                    ys @ [[e1]\<^sub>E] @ [[Event e3]\<^sub>E] = flt2ttobs(fl @\<^sub>\<F>\<^sub>\<L> \<langle>(last fl,Event e3)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>)
                    \<and> flt2goodAcceptance fl p \<and> flt2goodTock fl 
                    \<and> (\<exists>x. FLTick0 Tick (x \<union> {fl\<^sub>0. fl\<^sub>0 \<le>\<^sub>\<F>\<^sub>\<L> (fl @\<^sub>\<F>\<^sub>\<L> \<langle>(last fl,Event e3)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>)}) 
                        \<and> FL1 (x \<union> {fl\<^sub>0. fl\<^sub>0 \<le>\<^sub>\<F>\<^sub>\<L> (fl @\<^sub>\<F>\<^sub>\<L> \<langle>(last fl,Event e3)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>)}) 
                        \<and> {flt2ttobs fl\<^sub>0 |fl\<^sub>0. fl\<^sub>0 \<in> (x \<union> {fl\<^sub>0. fl\<^sub>0 \<le>\<^sub>\<F>\<^sub>\<L> (fl @\<^sub>\<F>\<^sub>\<L> \<langle>(last fl,Event e3)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>)})} \<subseteq> P \<and> fl \<in> x)"  
             using flt2ttobs_strongFL_subset TT3_trace_cons_imp_cons
             by (smt Un_iff mem_Collect_eq subset_iff)
           then have "
                    ys @ [[e1]\<^sub>E] @ [[Event e3]\<^sub>E] = flt2ttobs(fl @\<^sub>\<F>\<^sub>\<L> \<langle>(last fl,Event e3)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>)
                    \<and> flt2goodAcceptance fl p \<and> flt2goodTock fl 
                    \<and> (\<exists>x. FLTick0 Tick (x \<union> {fl\<^sub>0. fl\<^sub>0 \<le>\<^sub>\<F>\<^sub>\<L> (fl @\<^sub>\<F>\<^sub>\<L> \<langle>(last fl,Event e3)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>)}) 
                        \<and> FL1 (x \<union> {fl\<^sub>0. fl\<^sub>0 \<le>\<^sub>\<F>\<^sub>\<L> (fl @\<^sub>\<F>\<^sub>\<L> \<langle>(last fl,Event e3)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>)}) 
                        \<and> {flt2ttobs fl\<^sub>0 |fl\<^sub>0. fl\<^sub>0 \<in> (x \<union> {fl\<^sub>0. fl\<^sub>0 \<le>\<^sub>\<F>\<^sub>\<L> (fl @\<^sub>\<F>\<^sub>\<L> \<langle>(last fl,Event e3)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>)})} \<subseteq> P 
                        \<and> fl \<in> x
                        \<and> fl @\<^sub>\<F>\<^sub>\<L> \<langle>(last fl,Event e3)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L> \<in> (x \<union> {fl\<^sub>0. fl\<^sub>0 \<le>\<^sub>\<F>\<^sub>\<L> (fl @\<^sub>\<F>\<^sub>\<L> \<langle>(last fl,Event e3)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>)}))"
              by (simp add: strong_less_eq_fltrace_refl)  
           then have "
                    ys @ [[e1]\<^sub>E] @ [[Event e3]\<^sub>E] = flt2ttobs(fl @\<^sub>\<F>\<^sub>\<L> \<langle>(last fl,Event e3)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>)
                    \<and> flt2goodAcceptance fl p \<and> flt2goodTock fl 
                    \<and> (\<exists>z. FLTick0 Tick z \<and> FL1 z 
                        \<and> {flt2ttobs fl\<^sub>0 |fl\<^sub>0. fl\<^sub>0 \<in> z} \<subseteq> P 
                        \<and> fl @\<^sub>\<F>\<^sub>\<L> \<langle>(last fl,Event e3)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L> \<in> z)"
             by blast
           then have "
                    ys @ [[e1]\<^sub>E] @ [[Event e3]\<^sub>E] = flt2ttobs(fl @\<^sub>\<F>\<^sub>\<L> \<langle>(last fl,Event e3)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>)
                    \<and> flt2goodAcceptance fl p \<and> flt2goodTock fl 
                    \<and> flt2goodTock (fl @\<^sub>\<F>\<^sub>\<L> \<langle>(last fl,Event e3)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>)
                    \<and> (\<exists>z. FLTick0 Tick z \<and> FL1 z 
                        \<and> {flt2ttobs fl\<^sub>0 |fl\<^sub>0. fl\<^sub>0 \<in> z} \<subseteq> P 
                        \<and> fl @\<^sub>\<F>\<^sub>\<L> \<langle>(last fl,Event e3)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L> \<in> z)"
             using last_fl flt2goodTock_extend_consFL_last_fl_bullet
             by blast
           then have "
                    ys @ [[e1]\<^sub>E] @ [[Event e3]\<^sub>E] = flt2ttobs(fl @\<^sub>\<F>\<^sub>\<L> \<langle>(last fl,Event e3)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>)
                    \<and> flt2goodAcceptance fl p 
                    \<and> flt2goodAcceptance (fl @\<^sub>\<F>\<^sub>\<L> \<langle>(last fl,Event e3)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>) p
                    \<and> flt2goodTock fl 
                    \<and> flt2goodTock (fl @\<^sub>\<F>\<^sub>\<L> \<langle>(last fl,Event e3)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>)
                    \<and> (\<exists>z. FLTick0 Tick z \<and> FL1 z 
                        \<and> {flt2ttobs fl\<^sub>0 |fl\<^sub>0. fl\<^sub>0 \<in> z} \<subseteq> P 
                        \<and> fl @\<^sub>\<F>\<^sub>\<L> \<langle>(last fl,Event e3)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L> \<in> z)"
             using flt2goodAcceptance_extend_consFL_last_fl_bullet_maximal_pri
             by (metis (no_types, lifting) True acceptance_event acceptance_set append_self_conv bullet_right_zero2 butlast_last_cons2_FL fl_cons_acceptance_consFL fl_e3 flt2ttobs.simps(2) flt2ttobs_acceptance_cons_eq_list_cons last_fl not_Cons_self2)
           then have "
                    \<exists>fl. ys @ [[e1]\<^sub>E] @ [[Event e3]\<^sub>E] = flt2ttobs(fl)
                    \<and> flt2goodAcceptance fl p \<and> flt2goodTock fl 
                    \<and> (\<exists>z. FLTick0 Tick z \<and> FL1 z \<and> {flt2ttobs fl\<^sub>0 |fl\<^sub>0. fl\<^sub>0 \<in> z} \<subseteq> P \<and> fl \<in> z)"
             by blast
           then show ?thesis using Event e1 e2 by auto
          next
            case False
            then obtain Z where Z:"ys @ [[e1]\<^sub>E] @ [[Z]\<^sub>R] \<in> P \<and> Event e3 \<notin> Z \<and> \<not>(\<exists>b. b \<notin> Z \<and> Event e3 <\<^sup>*p b)"
              using prirelRef_nonmax_Tock_imp_exists_refusal
              by (metis TTwf_def TTwf_healthy Event append.assoc append_Nil ttevent.distinct(1) e1 e2 prirelRefyys)
            then have Tick_in_Z:"Tick \<in> Z"
              using TTick_healthy
              by (metis TTick_def append_assoc)
            
            have "flt2ttobs (fl @\<^sub>\<F>\<^sub>\<L> \<langle>[{x. x \<notin> Z}]\<^sub>\<F>\<^sub>\<L>\<rangle>\<^sub>\<F>\<^sub>\<L>) \<in> P"
              using fl Z
              by (metis (mono_tags, lifting) Nil_is_append_conv append.assoc flt2ttobs_fl_acceptance last_snoc not_Cons_self2)
            then have "flt2ttobs (fl @\<^sub>\<F>\<^sub>\<L> \<langle>([{x. x \<notin> Z}]\<^sub>\<F>\<^sub>\<L>,Event e3)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>) \<in> P"
            proof -
              have "flt2ttobs (fl @\<^sub>\<F>\<^sub>\<L> \<langle>([{x. x \<notin> Z}]\<^sub>\<F>\<^sub>\<L>,Event e3)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>) 
                    =
                    flt2ttobs (fl) @ flt2ttobs(\<langle>([{x. x \<notin> Z}]\<^sub>\<F>\<^sub>\<L>,Event e3)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>)"
                using fl e2 Event last_fl 
                by (metis (no_types, lifting) bullet_right_zero2 butlast_last_cons2_FL fl_cons_acceptance_consFL flt2ttobs_acceptance_cons_eq_list_cons)
              also have "... = ys @ [[e1]\<^sub>E] @ flt2ttobs(\<langle>([{x. x \<notin> Z}]\<^sub>\<F>\<^sub>\<L>,Event e3)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>)"
                using fl by auto
              also have "... = ys @ [[e1]\<^sub>E] @ [[Event e3]\<^sub>E]"
                using Z by auto
              then show ?thesis
                using Event \<open>ys @ [[e1]\<^sub>E] @ [[e2]\<^sub>E] \<in> P\<close> calculation by auto
            qed

            (* Need to pick a different last fl here, which is prioritised instead ! *)
            then have flt2ttobs_strongFL_subset:"{flt2ttobs fl\<^sub>0|fl\<^sub>0. fl\<^sub>0 \<le>\<^sub>\<F>\<^sub>\<L> (fl @\<^sub>\<F>\<^sub>\<L> \<langle>([{x. x \<notin> Z}]\<^sub>\<F>\<^sub>\<L>,Event e3)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>) \<or> fl\<^sub>0 \<le>\<^sub>\<F>\<^sub>\<L> (fl @\<^sub>\<F>\<^sub>\<L> \<langle>[{x. x \<notin> Z}]\<^sub>\<F>\<^sub>\<L>\<rangle>\<^sub>\<F>\<^sub>\<L>)} \<subseteq> P"
              using False strong_less_eq_fltrace_imp_flt2ttobs_tt TT1w_def TT1w_healthy Event ttevent.simps(3) e1 e2 fl flt2ttobs_last_non_tock last_fl last_snoc yys.prems(2)
              using \<open>flt2ttobs (fl @\<^sub>\<F>\<^sub>\<L> \<langle>[{x. x \<notin> Z}]\<^sub>\<F>\<^sub>\<L>\<rangle>\<^sub>\<F>\<^sub>\<L>) \<in> P\<close> by blast

            from fl have fl_e3: "ys @ [[e1]\<^sub>E] @ [[Event e3]\<^sub>E] = flt2ttobs fl @ [[Event e3]\<^sub>E]
                    \<and> flt2goodAcceptance fl p \<and> flt2goodTock fl \<and> (\<exists>x. FLTick0 Tick x \<and> FL1 x \<and> {flt2ttobs fl\<^sub>0 |fl\<^sub>0. fl\<^sub>0 \<in> x} \<subseteq> P \<and> fl \<in> x)"
              using ys_e1_x by auto
            also have "... =
                    (ys @ [[e1]\<^sub>E] @ [[Event e3]\<^sub>E] = flt2ttobs(fl @\<^sub>\<F>\<^sub>\<L> \<langle>([{x. x \<notin> Z}]\<^sub>\<F>\<^sub>\<L>,Event e3)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>)
                    \<and> flt2goodAcceptance fl p \<and> flt2goodTock fl \<and> (\<exists>x. FLTick0 Tick x \<and> FL1 x \<and> {flt2ttobs fl\<^sub>0 |fl\<^sub>0. fl\<^sub>0 \<in> x} \<subseteq> P \<and> fl \<in> x))"
              proof -
                from fl have "ys @ [[e1]\<^sub>E] = flt2ttobs fl"
                  by auto
                then have "List.last(flt2ttobs fl) = [e1]\<^sub>E"
                  by (metis last_snoc)
                then have "flt2ttobs fl @ [[Event e3]\<^sub>E] = flt2ttobs(fl) @ flt2ttobs(\<langle>([{x. x \<notin> Z}]\<^sub>\<F>\<^sub>\<L>,Event e3)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>)"
                  using Z by auto
                also have "... = ys @ [[e1]\<^sub>E] @ flt2ttobs(\<langle>([{x. x \<notin> Z}]\<^sub>\<F>\<^sub>\<L>,Event e3)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>)"
                  by (simp add: fl)
                also have "... = flt2ttobs (fl @\<^sub>\<F>\<^sub>\<L> \<langle>([{x. x \<notin> Z}]\<^sub>\<F>\<^sub>\<L>,Event e3)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>)"
                  using fl last_fl flt2ttobs_last_non_tock
                  by (metis (no_types, lifting) \<open>flt2ttobs fl @ flt2ttobs \<langle>([{x. x \<notin> Z}]\<^sub>\<F>\<^sub>\<L>,Event e3)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L> = ys @ [[e1]\<^sub>E] @ flt2ttobs \<langle>([{x. x \<notin> Z}]\<^sub>\<F>\<^sub>\<L>,Event e3)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>\<close> bullet_right_zero2 butlast_last_cons2_FL fl_cons_acceptance_consFL flt2ttobs_acceptance_cons_eq_list_cons)
                then show ?thesis using calculation
                  using fl_e3 by auto
              qed
            finally have "
                    ys @ [[e1]\<^sub>E] @ [[Event e3]\<^sub>E] = flt2ttobs(fl @\<^sub>\<F>\<^sub>\<L> \<langle>([{x. x \<notin> Z}]\<^sub>\<F>\<^sub>\<L>,Event e3)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>)
                    \<and> flt2goodAcceptance fl p \<and> flt2goodTock fl 
                    \<and> (\<exists>x. FLTick0 Tick x \<and> FL1(x \<union> {fl\<^sub>0. fl\<^sub>0 \<le>\<^sub>\<F>\<^sub>\<L> (fl @\<^sub>\<F>\<^sub>\<L> \<langle>[{x. x \<notin> Z}]\<^sub>\<F>\<^sub>\<L>\<rangle>\<^sub>\<F>\<^sub>\<L>) \<or> fl\<^sub>0 \<le>\<^sub>\<F>\<^sub>\<L> (fl @\<^sub>\<F>\<^sub>\<L> \<langle>([{x. x \<notin> Z}]\<^sub>\<F>\<^sub>\<L>,Event e3)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>)}) 
                        \<and> {flt2ttobs fl\<^sub>0 |fl\<^sub>0. fl\<^sub>0 \<in> x} \<subseteq> P \<and> fl \<in> x)"
              using FL1_extends_strong_less_eq_fltrace_last_bullet' last_fl
              proof -
                assume "ys @ [[e1]\<^sub>E] @ [[Event e3]\<^sub>E] = flt2ttobs fl @ [[Event e3]\<^sub>E] \<and> ys @ [[e1]\<^sub>E] @ [[Event e3]\<^sub>E] = flt2ttobs (fl @\<^sub>\<F>\<^sub>\<L> \<langle>([{x. x \<notin> Z}]\<^sub>\<F>\<^sub>\<L>,Event e3)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>) \<and> flt2goodAcceptance fl p \<and> flt2goodTock fl \<and> (\<exists>x. FLTick0 Tick x \<and> FL1 x \<and> {flt2ttobs fl\<^sub>0 |fl\<^sub>0. fl\<^sub>0 \<in> x} \<subseteq> P \<and> fl \<in> x)"
                then obtain FF :: "'a ttevent fltrace set" where
                  f1: "ys @ [[e1]\<^sub>E] @ [[Event e3]\<^sub>E] = flt2ttobs fl @ [[Event e3]\<^sub>E] \<and> ys @ [[e1]\<^sub>E] @ [[Event e3]\<^sub>E] = flt2ttobs (fl @\<^sub>\<F>\<^sub>\<L> \<langle>([{c. c \<notin> Z}]\<^sub>\<F>\<^sub>\<L>,Event e3)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>) \<and> flt2goodAcceptance fl p \<and> flt2goodTock fl \<and> FLTick0 Tick FF \<and> FL1 FF \<and> {flt2ttobs f |f. f \<in> FF} \<subseteq> P \<and> fl \<in> FF"
                  by blast
                have f2: "\<forall>f c a F. (((FL1 (F \<union> {fa. fa \<le>\<^sub>\<F>\<^sub>\<L> f @\<^sub>\<F>\<^sub>\<L> \<langle>a\<rangle>\<^sub>\<F>\<^sub>\<L> \<or> fa \<le>\<^sub>\<F>\<^sub>\<L> f @\<^sub>\<F>\<^sub>\<L> \<langle>(a,c)\<^sub>\<F>\<^sub>\<L>,Finite_Linear_Model.last fl\<rangle>\<^sub>\<F>\<^sub>\<L>}) \<or> Finite_Linear_Model.last f \<noteq> Finite_Linear_Model.last fl) \<or> f \<notin> F) \<or> c \<notin>\<^sub>\<F>\<^sub>\<L> a) \<or> \<not> FL1 F"
                  by (metis (no_types) FL1_extends_strong_less_eq_fltrace_last_bullet' last_fl)
                have "Event e3 \<in>\<^sub>\<F>\<^sub>\<L> [{c. c \<notin> Z}]\<^sub>\<F>\<^sub>\<L>"
                  by (simp add: Z)
                then have "\<exists>F. ((FL1 (F \<union> {f. f \<le>\<^sub>\<F>\<^sub>\<L> fl @\<^sub>\<F>\<^sub>\<L> \<langle>[{c. c \<notin> Z}]\<^sub>\<F>\<^sub>\<L>\<rangle>\<^sub>\<F>\<^sub>\<L> \<or> f \<le>\<^sub>\<F>\<^sub>\<L> fl @\<^sub>\<F>\<^sub>\<L> \<langle>([{c. c \<notin> Z}]\<^sub>\<F>\<^sub>\<L>,Event e3)\<^sub>\<F>\<^sub>\<L>,Finite_Linear_Model.last fl\<rangle>\<^sub>\<F>\<^sub>\<L>}) \<and> {flt2ttobs f |f. f \<in> F} \<subseteq> P) \<and> fl \<in> F) \<and> FLTick0 Tick F"
                  using f2 f1 by blast
                then show ?thesis
                  using f1 last_fl by auto
              qed
            then have "
                    ys @ [[e1]\<^sub>E] @ [[Event e3]\<^sub>E] = flt2ttobs(fl @\<^sub>\<F>\<^sub>\<L> \<langle>([{x. x \<notin> Z}]\<^sub>\<F>\<^sub>\<L>,Event e3)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>)
                    \<and> flt2goodAcceptance fl p \<and> flt2goodTock fl 
                    \<and> (\<exists>x. FLTick0 Tick (x \<union> {fl\<^sub>0. fl\<^sub>0 \<le>\<^sub>\<F>\<^sub>\<L> (fl @\<^sub>\<F>\<^sub>\<L> \<langle>[{x. x \<notin> Z}]\<^sub>\<F>\<^sub>\<L>\<rangle>\<^sub>\<F>\<^sub>\<L>) \<or> fl\<^sub>0 \<le>\<^sub>\<F>\<^sub>\<L> (fl @\<^sub>\<F>\<^sub>\<L> \<langle>([{x. x \<notin> Z}]\<^sub>\<F>\<^sub>\<L>,Event e3)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>)}) 
                        \<and> FL1(x \<union> {fl\<^sub>0. fl\<^sub>0 \<le>\<^sub>\<F>\<^sub>\<L> (fl @\<^sub>\<F>\<^sub>\<L> \<langle>[{x. x \<notin> Z}]\<^sub>\<F>\<^sub>\<L>\<rangle>\<^sub>\<F>\<^sub>\<L>) \<or> fl\<^sub>0 \<le>\<^sub>\<F>\<^sub>\<L> (fl @\<^sub>\<F>\<^sub>\<L> \<langle>([{x. x \<notin> Z}]\<^sub>\<F>\<^sub>\<L>,Event e3)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>)}) 
                        \<and> {flt2ttobs fl\<^sub>0 |fl\<^sub>0. fl\<^sub>0 \<in> x} \<subseteq> P \<and> fl \<in> x)"
              apply auto using FL0_Tick_extends_strong_less_eq_fltrace_last_bullet' last_fl Tick_not_in_events_fl
              proof -
                fix xb :: "'a ttevent fltrace set"
                assume a1: "FL1 (xb \<union> {fl\<^sub>0. fl\<^sub>0 \<le>\<^sub>\<F>\<^sub>\<L> fl @\<^sub>\<F>\<^sub>\<L> \<langle>[{x. x \<notin> Z}]\<^sub>\<F>\<^sub>\<L>\<rangle>\<^sub>\<F>\<^sub>\<L> \<or> fl\<^sub>0 \<le>\<^sub>\<F>\<^sub>\<L> fl @\<^sub>\<F>\<^sub>\<L> \<langle>([{x. x \<notin> Z}]\<^sub>\<F>\<^sub>\<L>,Event e3)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>})"
                  assume a2: "{flt2ttobs fl\<^sub>0 |fl\<^sub>0. fl\<^sub>0 \<in> xb} \<subseteq> P"
                  assume a3: "fl \<in> xb"
                  assume a4: "FLTick0 Tick xb"
                  have "Tick \<in> Z"
                    using Tick_in_Z by auto
                  then have "FLTick0 Tick (xb \<union> {f. f \<le>\<^sub>\<F>\<^sub>\<L> fl @\<^sub>\<F>\<^sub>\<L> \<langle>[{c. c \<notin> Z}]\<^sub>\<F>\<^sub>\<L>\<rangle>\<^sub>\<F>\<^sub>\<L> \<or> f \<le>\<^sub>\<F>\<^sub>\<L> fl @\<^sub>\<F>\<^sub>\<L> \<langle>([{c. c \<notin> Z}]\<^sub>\<F>\<^sub>\<L>,Event e3)\<^sub>\<F>\<^sub>\<L>,Finite_Linear_Model.last fl\<rangle>\<^sub>\<F>\<^sub>\<L>})"
                    using a4 a3 by (simp add: FL0_Tick_extends_strong_less_eq_fltrace_last_bullet' Tick_not_in_events_fl Z last_fl)
                  then show "\<exists>F. FLTick0 Tick (F \<union> {f. f \<le>\<^sub>\<F>\<^sub>\<L> fl @\<^sub>\<F>\<^sub>\<L> \<langle>[{c. c \<notin> Z}]\<^sub>\<F>\<^sub>\<L>\<rangle>\<^sub>\<F>\<^sub>\<L> \<or> f \<le>\<^sub>\<F>\<^sub>\<L> fl @\<^sub>\<F>\<^sub>\<L> \<langle>([{c. c \<notin> Z}]\<^sub>\<F>\<^sub>\<L>,Event e3)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>}) \<and> FL1 (F \<union> {f. f \<le>\<^sub>\<F>\<^sub>\<L> fl @\<^sub>\<F>\<^sub>\<L> \<langle>[{c. c \<notin> Z}]\<^sub>\<F>\<^sub>\<L>\<rangle>\<^sub>\<F>\<^sub>\<L> \<or> f \<le>\<^sub>\<F>\<^sub>\<L> fl @\<^sub>\<F>\<^sub>\<L> \<langle>([{c. c \<notin> Z}]\<^sub>\<F>\<^sub>\<L>,Event e3)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>}) \<and> {flt2ttobs f |f. f \<in> F} \<subseteq> P \<and> fl \<in> F"
                    using a3 a2 a1 last_fl by auto
                qed
           then have "
                    ys @ [[e1]\<^sub>E] @ [[Event e3]\<^sub>E] = flt2ttobs(fl @\<^sub>\<F>\<^sub>\<L> \<langle>([{x. x \<notin> Z}]\<^sub>\<F>\<^sub>\<L>,Event e3)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>)
                    \<and> flt2goodAcceptance fl p \<and> flt2goodTock fl 
                    \<and> (\<exists>x. FLTick0 Tick (x \<union> {fl\<^sub>0. fl\<^sub>0 \<le>\<^sub>\<F>\<^sub>\<L> (fl @\<^sub>\<F>\<^sub>\<L> \<langle>[{x. x \<notin> Z}]\<^sub>\<F>\<^sub>\<L>\<rangle>\<^sub>\<F>\<^sub>\<L>) \<or> fl\<^sub>0 \<le>\<^sub>\<F>\<^sub>\<L> (fl @\<^sub>\<F>\<^sub>\<L> \<langle>([{x. x \<notin> Z}]\<^sub>\<F>\<^sub>\<L>,Event e3)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>)}) 
                        \<and> FL1(x \<union> {fl\<^sub>0. fl\<^sub>0 \<le>\<^sub>\<F>\<^sub>\<L> (fl @\<^sub>\<F>\<^sub>\<L> \<langle>[{x. x \<notin> Z}]\<^sub>\<F>\<^sub>\<L>\<rangle>\<^sub>\<F>\<^sub>\<L>) \<or> fl\<^sub>0 \<le>\<^sub>\<F>\<^sub>\<L> (fl @\<^sub>\<F>\<^sub>\<L> \<langle>([{x. x \<notin> Z}]\<^sub>\<F>\<^sub>\<L>,Event e3)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>)}) 
                        \<and> {flt2ttobs fl\<^sub>0 |fl\<^sub>0. fl\<^sub>0 \<in> x \<union> {fl\<^sub>0. fl\<^sub>0 \<le>\<^sub>\<F>\<^sub>\<L> (fl @\<^sub>\<F>\<^sub>\<L> \<langle>[{x. x \<notin> Z}]\<^sub>\<F>\<^sub>\<L>\<rangle>\<^sub>\<F>\<^sub>\<L>) \<or> fl\<^sub>0 \<le>\<^sub>\<F>\<^sub>\<L> (fl @\<^sub>\<F>\<^sub>\<L> \<langle>([{x. x \<notin> Z}]\<^sub>\<F>\<^sub>\<L>,Event e3)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>)}} \<subseteq> P \<and> fl \<in> x)"    
             using flt2ttobs_strongFL_subset
             by (smt Un_iff mem_Collect_eq subset_iff)
           then have "
                    ys @ [[e1]\<^sub>E] @ [[Event e3]\<^sub>E] = flt2ttobs(fl @\<^sub>\<F>\<^sub>\<L> \<langle>([{x. x \<notin> Z}]\<^sub>\<F>\<^sub>\<L>,Event e3)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>)
                    \<and> flt2goodAcceptance fl p \<and> flt2goodTock fl 
                    \<and> (\<exists>x. FLTick0 Tick (x \<union> {fl\<^sub>0. fl\<^sub>0 \<le>\<^sub>\<F>\<^sub>\<L> (fl @\<^sub>\<F>\<^sub>\<L> \<langle>[{x. x \<notin> Z}]\<^sub>\<F>\<^sub>\<L>\<rangle>\<^sub>\<F>\<^sub>\<L>) \<or> fl\<^sub>0 \<le>\<^sub>\<F>\<^sub>\<L> (fl @\<^sub>\<F>\<^sub>\<L> \<langle>([{x. x \<notin> Z}]\<^sub>\<F>\<^sub>\<L>,Event e3)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>)}) 
                        \<and> FL1(x \<union> {fl\<^sub>0. fl\<^sub>0 \<le>\<^sub>\<F>\<^sub>\<L> (fl @\<^sub>\<F>\<^sub>\<L> \<langle>[{x. x \<notin> Z}]\<^sub>\<F>\<^sub>\<L>\<rangle>\<^sub>\<F>\<^sub>\<L>) \<or> fl\<^sub>0 \<le>\<^sub>\<F>\<^sub>\<L> (fl @\<^sub>\<F>\<^sub>\<L> \<langle>([{x. x \<notin> Z}]\<^sub>\<F>\<^sub>\<L>,Event e3)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>)}) 
                        \<and> {flt2ttobs fl\<^sub>0 |fl\<^sub>0. fl\<^sub>0 \<in> x \<union> {fl\<^sub>0. fl\<^sub>0 \<le>\<^sub>\<F>\<^sub>\<L> (fl @\<^sub>\<F>\<^sub>\<L> \<langle>[{x. x \<notin> Z}]\<^sub>\<F>\<^sub>\<L>\<rangle>\<^sub>\<F>\<^sub>\<L>) \<or> fl\<^sub>0 \<le>\<^sub>\<F>\<^sub>\<L> (fl @\<^sub>\<F>\<^sub>\<L> \<langle>([{x. x \<notin> Z}]\<^sub>\<F>\<^sub>\<L>,Event e3)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>)}} \<subseteq> P 
                        \<and> fl \<in> x
                        \<and> fl @\<^sub>\<F>\<^sub>\<L> \<langle>([{x. x \<notin> Z}]\<^sub>\<F>\<^sub>\<L>,Event e3)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L> \<in> (x \<union> {fl\<^sub>0. fl\<^sub>0 \<le>\<^sub>\<F>\<^sub>\<L> (fl @\<^sub>\<F>\<^sub>\<L> \<langle>[{x. x \<notin> Z}]\<^sub>\<F>\<^sub>\<L>\<rangle>\<^sub>\<F>\<^sub>\<L>) \<or> fl\<^sub>0 \<le>\<^sub>\<F>\<^sub>\<L> (fl @\<^sub>\<F>\<^sub>\<L> \<langle>([{x. x \<notin> Z}]\<^sub>\<F>\<^sub>\<L>,Event e3)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>)}))"    
             by (simp add: strong_less_eq_fltrace_refl)
           then have "
                    ys @ [[e1]\<^sub>E] @ [[Event e3]\<^sub>E] = flt2ttobs(fl @\<^sub>\<F>\<^sub>\<L> \<langle>([{x. x \<notin> Z}]\<^sub>\<F>\<^sub>\<L>,Event e3)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>)
                    \<and> flt2goodAcceptance fl p \<and> flt2goodTock fl 
                    \<and> (\<exists>z. FLTick0 Tick z 
                        \<and> FL1 z 
                        \<and> {flt2ttobs fl\<^sub>0 |fl\<^sub>0. fl\<^sub>0 \<in> z} \<subseteq> P 
                        \<and> fl @\<^sub>\<F>\<^sub>\<L> \<langle>([{x. x \<notin> Z}]\<^sub>\<F>\<^sub>\<L>,Event e3)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L> \<in> z)"   
             by blast
           then have "
                    ys @ [[e1]\<^sub>E] @ [[Event e3]\<^sub>E] = flt2ttobs(fl @\<^sub>\<F>\<^sub>\<L> \<langle>([{x. x \<notin> Z}]\<^sub>\<F>\<^sub>\<L>,Event e3)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>)
                    \<and> flt2goodAcceptance fl p 
                    \<and> flt2goodTock fl 
                    \<and> flt2goodTock (fl @\<^sub>\<F>\<^sub>\<L> \<langle>([{x. x \<notin> Z}]\<^sub>\<F>\<^sub>\<L>,Event e3)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>)
                    \<and> (\<exists>z. FLTick0 Tick z 
                        \<and> FL1 z 
                        \<and> {flt2ttobs fl\<^sub>0 |fl\<^sub>0. fl\<^sub>0 \<in> z} \<subseteq> P 
                        \<and> fl @\<^sub>\<F>\<^sub>\<L> \<langle>([{x. x \<notin> Z}]\<^sub>\<F>\<^sub>\<L>,Event e3)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L> \<in> z)"   
             using flt2goodTock_extend_consFL_last_e'
             by (simp add: flt2goodTock_extend_consFL_last_e' Z)
            then have "
                    ys @ [[e1]\<^sub>E] @ [[Event e3]\<^sub>E] = flt2ttobs(fl @\<^sub>\<F>\<^sub>\<L> \<langle>([{x. x \<notin> Z}]\<^sub>\<F>\<^sub>\<L>,Event e3)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>)
                    \<and> flt2goodAcceptance fl p 
                    \<and> flt2goodAcceptance (fl @\<^sub>\<F>\<^sub>\<L> \<langle>([{x. x \<notin> Z}]\<^sub>\<F>\<^sub>\<L>,Event e3)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>) p 
                    \<and> flt2goodTock fl 
                    \<and> flt2goodTock (fl @\<^sub>\<F>\<^sub>\<L> \<langle>([{x. x \<notin> Z}]\<^sub>\<F>\<^sub>\<L>,Event e3)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>)
                    \<and> (\<exists>z. FLTick0 Tick z 
                        \<and> FL1 z 
                        \<and> {flt2ttobs fl\<^sub>0 |fl\<^sub>0. fl\<^sub>0 \<in> z} \<subseteq> P 
                        \<and> fl @\<^sub>\<F>\<^sub>\<L> \<langle>([{x. x \<notin> Z}]\<^sub>\<F>\<^sub>\<L>,Event e3)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L> \<in> z)"   
              using Z
              by (simp add: flt2goodAcceptance_extend_consFL)
           then have "
                    \<exists>fl. ys @ [[e1]\<^sub>E] @ [[Event e3]\<^sub>E] = flt2ttobs fl
                    \<and> flt2goodAcceptance fl p 
                    \<and> flt2goodTock fl
                    \<and> (\<exists>z. FLTick0 Tick z 
                        \<and> FL1 z 
                        \<and> {flt2ttobs fl\<^sub>0 |fl\<^sub>0. fl\<^sub>0 \<in> z} \<subseteq> P 
                        \<and> fl \<in> z)"   
             by blast
           then show ?thesis 
             by (metis (no_types, lifting) Event e1 e2 fl fl_e3)
         qed
        next
          case Tock
          then have "\<not>ttWF (ys @ [[e1]\<^sub>E, [Tock]\<^sub>E])"
            apply (induct ys rule:ttWF.induct, auto)
            using ttWF.elims(2) ttWF.simps(6) by blast+
          then show ?thesis
            using e1 e2 TTwf_healthy unfolding TTwf_def
            by (metis Tock append_eq_Cons_conv fl ys_e1_x yys.prems(2))
        next
          case Tick
          have flt2ttobs_strongFL_subset:"{flt2ttobs fl\<^sub>0|fl\<^sub>0. fl\<^sub>0 \<le>\<^sub>\<F>\<^sub>\<L> (fl @\<^sub>\<F>\<^sub>\<L> \<langle>(last fl,Tick)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>)} \<subseteq> P"
            apply auto
            using strong_less_eq_fltrace_imp_flt2ttobs_tt
            by (metis (no_types, lifting) TT1w_def TT1w_healthy Tick ttevent.distinct(5) e1 e2 fl flt2ttobs_last_non_tock last_fl last_snoc yys.prems(2))
            
          from fl have fl_e3: "ys @ [[e1]\<^sub>E] @ [[Tick]\<^sub>E] = flt2ttobs fl @ [[Tick]\<^sub>E]
                  \<and> flt2goodAcceptance fl p \<and> flt2goodTock fl \<and> (\<exists>x. FLTick0 Tick x \<and> FL1 x \<and> {flt2ttobs fl\<^sub>0 |fl\<^sub>0. fl\<^sub>0 \<in> x} \<subseteq> P \<and> fl \<in> x)"
            using ys_e1_x by auto
          also have "... =
                  (ys @ [[e1]\<^sub>E] @ [[Tick]\<^sub>E] = flt2ttobs(fl @\<^sub>\<F>\<^sub>\<L> \<langle>(last fl,Tick)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>)
                  \<and> flt2goodAcceptance fl p \<and> flt2goodTock fl \<and> (\<exists>x. FLTick0 Tick x \<and> FL1 x \<and> {flt2ttobs fl\<^sub>0 |fl\<^sub>0. fl\<^sub>0 \<in> x} \<subseteq> P \<and> fl \<in> x))"
            proof -
              from fl have "ys @ [[e1]\<^sub>E] = flt2ttobs fl"
                by auto
              then have "List.last(flt2ttobs fl) = [e1]\<^sub>E"
                by (metis last_snoc)
              then have "flt2ttobs fl @ [[Tick]\<^sub>E] = flt2ttobs(fl @\<^sub>\<F>\<^sub>\<L> \<langle>(last fl,Tick)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>)"
                using fl last_fl flt2ttobs_last_non_tock
                by (metis (no_types, lifting) ttevent.simps(7))
              then show ?thesis using calculation  by auto
            qed
          finally have "
                  ys @ [[e1]\<^sub>E] @ [[Tick]\<^sub>E] = flt2ttobs(fl @\<^sub>\<F>\<^sub>\<L> \<langle>(last fl,Tick)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>)
                  \<and> flt2goodAcceptance fl p \<and> flt2goodTock fl 
                  \<and> (\<exists>x. FLTick0 Tick x \<and> FL1 (x \<union> {fl\<^sub>0. fl\<^sub>0 \<le>\<^sub>\<F>\<^sub>\<L> (fl @\<^sub>\<F>\<^sub>\<L> \<langle>(last fl,Tick)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>)}) 
                      \<and> {flt2ttobs fl\<^sub>0 |fl\<^sub>0. fl\<^sub>0 \<in> x} \<subseteq> P \<and> fl \<in> x)"
              apply auto using FL1_extends_strong_less_eq_fltrace_last_bullet last_fl 
            by fastforce
         then have "
                  ys @ [[e1]\<^sub>E] @ [[Tick]\<^sub>E] = flt2ttobs(fl @\<^sub>\<F>\<^sub>\<L> \<langle>(last fl,Tick)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>)
                  \<and> flt2goodAcceptance fl p \<and> flt2goodTock fl 
                  \<and> (\<exists>x. FLTick0 Tick (x \<union> {fl\<^sub>0. fl\<^sub>0 \<le>\<^sub>\<F>\<^sub>\<L> (fl @\<^sub>\<F>\<^sub>\<L> \<langle>(last fl,Tick)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>)}) 
                      \<and> FL1 (x \<union> {fl\<^sub>0. fl\<^sub>0 \<le>\<^sub>\<F>\<^sub>\<L> (fl @\<^sub>\<F>\<^sub>\<L> \<langle>(last fl,Tick)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>)}) 
                      \<and> {flt2ttobs fl\<^sub>0 |fl\<^sub>0. fl\<^sub>0 \<in> x} \<subseteq> P \<and> fl \<in> x)"
          apply auto using FL0_Tick_extends_strong_less_eq_fltrace_last_bullet last_fl Tick_not_in_events_fl
            by blast
         then have "
                  ys @ [[e1]\<^sub>E] @ [[Tick]\<^sub>E] = flt2ttobs(fl @\<^sub>\<F>\<^sub>\<L> \<langle>(last fl,Tick)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>)
                  \<and> flt2goodAcceptance fl p \<and> flt2goodTock fl 
                  \<and> (\<exists>x. FLTick0 Tick (x \<union> {fl\<^sub>0. fl\<^sub>0 \<le>\<^sub>\<F>\<^sub>\<L> (fl @\<^sub>\<F>\<^sub>\<L> \<langle>(last fl,Tick)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>)}) 
                      \<and> FL1 (x \<union> {fl\<^sub>0. fl\<^sub>0 \<le>\<^sub>\<F>\<^sub>\<L> (fl @\<^sub>\<F>\<^sub>\<L> \<langle>(last fl,Tick)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>)}) 
                      \<and> {flt2ttobs fl\<^sub>0 |fl\<^sub>0. fl\<^sub>0 \<in> (x \<union> {fl\<^sub>0. fl\<^sub>0 \<le>\<^sub>\<F>\<^sub>\<L> (fl @\<^sub>\<F>\<^sub>\<L> \<langle>(last fl,Tick)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>)})} \<subseteq> P \<and> fl \<in> x)"  
           using flt2ttobs_strongFL_subset 
           by (smt Un_iff mem_Collect_eq subset_iff)
         then have "
                  ys @ [[e1]\<^sub>E] @ [[Tick]\<^sub>E] = flt2ttobs(fl @\<^sub>\<F>\<^sub>\<L> \<langle>(last fl,Tick)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>)
                  \<and> flt2goodAcceptance fl p \<and> flt2goodTock fl 
                  \<and> (\<exists>x. FLTick0 Tick (x \<union> {fl\<^sub>0. fl\<^sub>0 \<le>\<^sub>\<F>\<^sub>\<L> (fl @\<^sub>\<F>\<^sub>\<L> \<langle>(last fl,Tick)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>)}) 
                      \<and> FL1 (x \<union> {fl\<^sub>0. fl\<^sub>0 \<le>\<^sub>\<F>\<^sub>\<L> (fl @\<^sub>\<F>\<^sub>\<L> \<langle>(last fl,Tick)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>)}) 
                      \<and> {flt2ttobs fl\<^sub>0 |fl\<^sub>0. fl\<^sub>0 \<in> (x \<union> {fl\<^sub>0. fl\<^sub>0 \<le>\<^sub>\<F>\<^sub>\<L> (fl @\<^sub>\<F>\<^sub>\<L> \<langle>(last fl,Tick)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>)})} \<subseteq> P 
                      \<and> fl \<in> x
                      \<and> fl @\<^sub>\<F>\<^sub>\<L> \<langle>(last fl,Tick)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L> \<in> (x \<union> {fl\<^sub>0. fl\<^sub>0 \<le>\<^sub>\<F>\<^sub>\<L> (fl @\<^sub>\<F>\<^sub>\<L> \<langle>(last fl,Tick)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>)}))"
            by (simp add: strong_less_eq_fltrace_refl)  
         then have "
                  ys @ [[e1]\<^sub>E] @ [[Tick]\<^sub>E] = flt2ttobs(fl @\<^sub>\<F>\<^sub>\<L> \<langle>(last fl,Tick)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>)
                  \<and> flt2goodAcceptance fl p \<and> flt2goodTock fl 
                  \<and> (\<exists>z. FLTick0 Tick z \<and> FL1 z 
                      \<and> {flt2ttobs fl\<^sub>0 |fl\<^sub>0. fl\<^sub>0 \<in> z} \<subseteq> P 
                      \<and> fl @\<^sub>\<F>\<^sub>\<L> \<langle>(last fl,Tick)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L> \<in> z)"
           by blast
         then have "
                  ys @ [[e1]\<^sub>E] @ [[Tick]\<^sub>E] = flt2ttobs(fl @\<^sub>\<F>\<^sub>\<L> \<langle>(last fl,Tick)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>)
                  \<and> flt2goodAcceptance fl p \<and> flt2goodTock fl 
                  \<and> flt2goodTock (fl @\<^sub>\<F>\<^sub>\<L> \<langle>(last fl,Tick)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>)
                  \<and> (\<exists>z. FLTick0 Tick z \<and> FL1 z 
                      \<and> {flt2ttobs fl\<^sub>0 |fl\<^sub>0. fl\<^sub>0 \<in> z} \<subseteq> P 
                      \<and> fl @\<^sub>\<F>\<^sub>\<L> \<langle>(last fl,Tick)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L> \<in> z)"
           using last_fl flt2goodTock_extend_consFL_last_fl_bullet
           by blast
         then have "
                  ys @ [[e1]\<^sub>E] @ [[Tick]\<^sub>E] = flt2ttobs(fl @\<^sub>\<F>\<^sub>\<L> \<langle>(last fl,Tick)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>)
                  \<and> flt2goodAcceptance fl p 
                  \<and> flt2goodAcceptance (fl @\<^sub>\<F>\<^sub>\<L> \<langle>(last fl,Tick)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>) p
                  \<and> flt2goodTock fl 
                  \<and> flt2goodTock (fl @\<^sub>\<F>\<^sub>\<L> \<langle>(last fl,Tick)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>)
                  \<and> (\<exists>z. FLTick0 Tick z \<and> FL1 z 
                      \<and> {flt2ttobs fl\<^sub>0 |fl\<^sub>0. fl\<^sub>0 \<in> z} \<subseteq> P 
                      \<and> fl @\<^sub>\<F>\<^sub>\<L> \<langle>(last fl,Tick)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L> \<in> z)"
           using flt2goodAcceptance_extend_consFL_last_fl_bullet_Tick
           by (metis (no_types, lifting) bullet_right_zero2 butlast_last_cons2_FL fl_cons_acceptance_consFL fl_e3 last_fl)
         then have "
                  \<exists>fl. ys @ [[e1]\<^sub>E] @ [[Tick]\<^sub>E] = flt2ttobs(fl)
                  \<and> flt2goodAcceptance fl p \<and> flt2goodTock fl 
                  \<and> (\<exists>z. FLTick0 Tick z \<and> FL1 z \<and> {flt2ttobs fl\<^sub>0 |fl\<^sub>0. fl\<^sub>0 \<in> z} \<subseteq> P \<and> fl \<in> z)"
           by blast
         then show ?thesis using Tick e1 e2 by auto
        qed
      next
        case (Ref r2)
        have Tick_in_r2:"Tick \<in> r2"
          using TTick_healthy Ref TTick_def xs_x_in_P by blast
        then have "ys @ [[e1]\<^sub>E] @ [[r2]\<^sub>R] \<in> P"
          using e1 Ref yys.prems(2) by auto
        then have "[Tick]\<^sub>E \<notin> set (ys @ [[e1]\<^sub>E])" 
          using TTwf_healthy TTwf_concat_prefix_of_ref_set_no_Tick
          using e1 Ref
          by (metis fl ys_e1_x)
        then have Tick_not_in_events_fl: "Tick \<notin> events fl"
          by (simp add: event_not_in_set_of_flt2ttobs_imp_not_in_events fl)
       (* have flt2ttobs_strongFL_subset:"{flt2ttobs fl\<^sub>0|fl\<^sub>0. fl\<^sub>0 \<le>\<^sub>\<F>\<^sub>\<L> (fl @\<^sub>\<F>\<^sub>\<L> \<langle>[{x. x \<notin> r2}]\<^sub>\<F>\<^sub>\<L>\<rangle>\<^sub>\<F>\<^sub>\<L>)} \<subseteq> P"
            apply auto
          using strong_less_eq_fltrace_imp_flt2ttobs_tt
          sledgehammer[debug=true]
          by (metis TT1w_def TT1w_healthy Collect_cong Ref e1 fl flt2ttobs_fl_acceptance last_snoc mem_Collect_eq snoc_eq_iff_butlast subsetI subset_iff yys.prems(2))
        *)
        from fl have fl_e3: "ys @ [[e1]\<^sub>E] @ [[r2]\<^sub>R] = flt2ttobs fl @ [[r2]\<^sub>R]
                  \<and> flt2goodAcceptance fl p \<and> flt2goodTock fl \<and> (\<exists>x. FLTick0 Tick x \<and> FL1 x \<and> {flt2ttobs fl\<^sub>0 |fl\<^sub>0. fl\<^sub>0 \<in> x} \<subseteq> P \<and> fl \<in> x)"
          using ys_e1_x by auto
        also have "... =
                  (ys @ [[e1]\<^sub>E] @ [[r2]\<^sub>R] = flt2ttobs(fl @\<^sub>\<F>\<^sub>\<L> \<langle>[{x. x \<notin> r2} - {Tick}]\<^sub>\<F>\<^sub>\<L>\<rangle>\<^sub>\<F>\<^sub>\<L>)
                  \<and> flt2goodAcceptance fl p \<and> flt2goodTock fl \<and> (\<exists>x. FLTick0 Tick x \<and> FL1 x \<and> {flt2ttobs fl\<^sub>0 |fl\<^sub>0. fl\<^sub>0 \<in> x} \<subseteq> P \<and> fl \<in> x))"
          proof -
              from fl have "ys @ [[e1]\<^sub>E] = flt2ttobs fl"
                by auto
              then have "List.last(flt2ttobs fl) = [e1]\<^sub>E"
                by (metis last_snoc)
              then have "flt2ttobs fl @ [[r2]\<^sub>R] = flt2ttobs(fl @\<^sub>\<F>\<^sub>\<L> \<langle>[{x. x \<notin> r2} - {Tick}]\<^sub>\<F>\<^sub>\<L>\<rangle>\<^sub>\<F>\<^sub>\<L>)"
                using fl last_fl flt2ttobs_fl_acceptance Tick_in_r2
              proof -
                have "flt2ttobs fl \<noteq> []"
                  by (metis (no_types) append_is_Nil_conv fl not_Cons_self2)
                then show ?thesis
                  by (simp add: Tick_in_r2 \<open>List.last (flt2ttobs fl) = [e1]\<^sub>E\<close> fl flt2ttobs_fl_acceptance)
                qed
              then show ?thesis using calculation by auto
            qed
         finally have "
                  ys @ [[e1]\<^sub>E] @ [[r2]\<^sub>R] = flt2ttobs(fl @\<^sub>\<F>\<^sub>\<L> \<langle>[{x. x \<notin> r2} - {Tick}]\<^sub>\<F>\<^sub>\<L>\<rangle>\<^sub>\<F>\<^sub>\<L>)
                  \<and> flt2goodAcceptance fl p \<and> flt2goodTock fl 
                  \<and> (\<exists>x. FLTick0 Tick x \<and> FL1 (x \<union> {fl\<^sub>0. fl\<^sub>0 \<le>\<^sub>\<F>\<^sub>\<L> (fl @\<^sub>\<F>\<^sub>\<L> \<langle>[{x. x \<notin> r2} - {Tick}]\<^sub>\<F>\<^sub>\<L>\<rangle>\<^sub>\<F>\<^sub>\<L>)}) 
                      \<and> {flt2ttobs fl\<^sub>0 |fl\<^sub>0. fl\<^sub>0 \<in> x} \<subseteq> P \<and> fl \<in> x)"
              apply auto using FL1_extends_strong_less_eq_fltrace_acceptance last_fl 
           by fastforce 
         then have "
                  ys @ [[e1]\<^sub>E] @ [[r2]\<^sub>R] = flt2ttobs(fl @\<^sub>\<F>\<^sub>\<L> \<langle>[{x. x \<notin> r2} - {Tick}]\<^sub>\<F>\<^sub>\<L>\<rangle>\<^sub>\<F>\<^sub>\<L>)
                  \<and> flt2goodAcceptance fl p \<and> flt2goodTock fl 
                  \<and> (\<exists>x. FLTick0 Tick (x \<union> {fl\<^sub>0. fl\<^sub>0 \<le>\<^sub>\<F>\<^sub>\<L> (fl @\<^sub>\<F>\<^sub>\<L> \<langle>[{x. x \<notin> r2} - {Tick}]\<^sub>\<F>\<^sub>\<L>\<rangle>\<^sub>\<F>\<^sub>\<L>)})
                      \<and> FL1 (x \<union> {fl\<^sub>0. fl\<^sub>0 \<le>\<^sub>\<F>\<^sub>\<L> (fl @\<^sub>\<F>\<^sub>\<L> \<langle>[{x. x \<notin> r2}- {Tick}]\<^sub>\<F>\<^sub>\<L>\<rangle>\<^sub>\<F>\<^sub>\<L>)}) 
                      \<and> {flt2ttobs fl\<^sub>0 |fl\<^sub>0. fl\<^sub>0 \<in> x} \<subseteq> P \<and> fl \<in> x)"
            apply auto using FL0Tick_extends_strong_less_eq_fltrace_acceptance last_fl Tick_in_r2 Tick_not_in_events_fl
           by (smt Collect_cong Diff_empty Diff_insert0 FLTick0_def Un_iff amember.simps(2) mem_Collect_eq tickWF_concatFL_acceptance_imp tickWF_prefix_imp)
         then have "
                  ys @ [[e1]\<^sub>E] @ [[r2]\<^sub>R] = flt2ttobs(fl @\<^sub>\<F>\<^sub>\<L> \<langle>[{x. x \<notin> r2} - {Tick}]\<^sub>\<F>\<^sub>\<L>\<rangle>\<^sub>\<F>\<^sub>\<L>)
                  \<and> flt2goodAcceptance fl p \<and> flt2goodTock fl 
                  \<and> (\<exists>x. FLTick0 Tick (x \<union> {fl\<^sub>0. fl\<^sub>0 \<le>\<^sub>\<F>\<^sub>\<L> (fl @\<^sub>\<F>\<^sub>\<L> \<langle>[{x. x \<notin> r2} - {Tick}]\<^sub>\<F>\<^sub>\<L>\<rangle>\<^sub>\<F>\<^sub>\<L>)})
                      \<and> FL1 (x \<union> {fl\<^sub>0. fl\<^sub>0 \<le>\<^sub>\<F>\<^sub>\<L> (fl @\<^sub>\<F>\<^sub>\<L> \<langle>[{x. x \<notin> r2} - {Tick}]\<^sub>\<F>\<^sub>\<L>\<rangle>\<^sub>\<F>\<^sub>\<L>)}) 
                      \<and> {flt2ttobs fl\<^sub>0 |fl\<^sub>0. fl\<^sub>0 \<in> (x \<union> {fl\<^sub>0. fl\<^sub>0 \<le>\<^sub>\<F>\<^sub>\<L> (fl @\<^sub>\<F>\<^sub>\<L> \<langle>[{x. x \<notin> r2} - {Tick}]\<^sub>\<F>\<^sub>\<L>\<rangle>\<^sub>\<F>\<^sub>\<L>)})} \<subseteq> P \<and> fl \<in> x)"  
         proof -
           have
            "{flt2ttobs fl\<^sub>0|fl\<^sub>0. fl\<^sub>0 \<le>\<^sub>\<F>\<^sub>\<L> (fl @\<^sub>\<F>\<^sub>\<L> \<langle>[{x. x \<notin> r2} - {Tick}]\<^sub>\<F>\<^sub>\<L>\<rangle>\<^sub>\<F>\<^sub>\<L>)} \<subseteq> P"
            apply auto
            using strong_less_eq_fltrace_imp_flt2ttobs_tt
            by (metis (no_types, lifting) TT1w_def TT1w_healthy Ref \<open>ys @ [[e1]\<^sub>E] @ [[r2]\<^sub>R] = flt2ttobs (fl @\<^sub>\<F>\<^sub>\<L> \<langle>[{x. x \<notin> r2} - {Tick}]\<^sub>\<F>\<^sub>\<L>\<rangle>\<^sub>\<F>\<^sub>\<L>) \<and> flt2goodAcceptance fl p \<and> flt2goodTock fl \<and> (\<exists>x. FLTick0 Tick x \<and> FL1 (x \<union> {fl\<^sub>0. fl\<^sub>0 \<le>\<^sub>\<F>\<^sub>\<L> fl @\<^sub>\<F>\<^sub>\<L> \<langle>[{x. x \<notin> r2} - {Tick}]\<^sub>\<F>\<^sub>\<L>\<rangle>\<^sub>\<F>\<^sub>\<L>}) \<and> {flt2ttobs fl\<^sub>0 |fl\<^sub>0. fl\<^sub>0 \<in> x} \<subseteq> P \<and> fl \<in> x)\<close> e1 fl fl_e3 yys.prems(2))
          then show ?thesis 
            by (smt Un_iff \<open>ys @ [[e1]\<^sub>E] @ [[r2]\<^sub>R] = flt2ttobs (fl @\<^sub>\<F>\<^sub>\<L> \<langle>[{x. x \<notin> r2} - {Tick}]\<^sub>\<F>\<^sub>\<L>\<rangle>\<^sub>\<F>\<^sub>\<L>) \<and> flt2goodAcceptance fl p \<and> flt2goodTock fl \<and> (\<exists>x. FLTick0 Tick (x \<union> {fl\<^sub>0. fl\<^sub>0 \<le>\<^sub>\<F>\<^sub>\<L> fl @\<^sub>\<F>\<^sub>\<L> \<langle>[{x. x \<notin> r2} - {Tick}]\<^sub>\<F>\<^sub>\<L>\<rangle>\<^sub>\<F>\<^sub>\<L>}) \<and> FL1 (x \<union> {fl\<^sub>0. fl\<^sub>0 \<le>\<^sub>\<F>\<^sub>\<L> fl @\<^sub>\<F>\<^sub>\<L> \<langle>[{x. x \<notin> r2} - {Tick}]\<^sub>\<F>\<^sub>\<L>\<rangle>\<^sub>\<F>\<^sub>\<L>}) \<and> {flt2ttobs fl\<^sub>0 |fl\<^sub>0. fl\<^sub>0 \<in> x} \<subseteq> P \<and> fl \<in> x)\<close> mem_Collect_eq subset_eq)
        qed
        then have "
                  ys @ [[e1]\<^sub>E] @ [[r2]\<^sub>R] = flt2ttobs(fl @\<^sub>\<F>\<^sub>\<L> \<langle>[{x. x \<notin> r2} - {Tick}]\<^sub>\<F>\<^sub>\<L>\<rangle>\<^sub>\<F>\<^sub>\<L>)
                  \<and> flt2goodAcceptance fl p \<and> flt2goodTock fl 
                  \<and> (\<exists>x. FLTick0 Tick (x \<union> {fl\<^sub>0. fl\<^sub>0 \<le>\<^sub>\<F>\<^sub>\<L> (fl @\<^sub>\<F>\<^sub>\<L> \<langle>[{x. x \<notin> r2} - {Tick}]\<^sub>\<F>\<^sub>\<L>\<rangle>\<^sub>\<F>\<^sub>\<L>)})
                      \<and> FL1 (x \<union> {fl\<^sub>0. fl\<^sub>0 \<le>\<^sub>\<F>\<^sub>\<L> (fl @\<^sub>\<F>\<^sub>\<L> \<langle>[{x. x \<notin> r2} - {Tick}]\<^sub>\<F>\<^sub>\<L>\<rangle>\<^sub>\<F>\<^sub>\<L>)}) 
                      \<and> {flt2ttobs fl\<^sub>0 |fl\<^sub>0. fl\<^sub>0 \<in> (x \<union> {fl\<^sub>0. fl\<^sub>0 \<le>\<^sub>\<F>\<^sub>\<L> (fl @\<^sub>\<F>\<^sub>\<L> \<langle>[{x. x \<notin> r2} - {Tick}]\<^sub>\<F>\<^sub>\<L>\<rangle>\<^sub>\<F>\<^sub>\<L>)})} \<subseteq> P 
                      \<and> fl \<in> x
                      \<and> (fl @\<^sub>\<F>\<^sub>\<L> \<langle>[{x. x \<notin> r2} - {Tick}]\<^sub>\<F>\<^sub>\<L>\<rangle>\<^sub>\<F>\<^sub>\<L>) \<in> (x \<union> {fl\<^sub>0. fl\<^sub>0 \<le>\<^sub>\<F>\<^sub>\<L> (fl @\<^sub>\<F>\<^sub>\<L> \<langle>[{x. x \<notin> r2} - {Tick}]\<^sub>\<F>\<^sub>\<L>\<rangle>\<^sub>\<F>\<^sub>\<L>)}))"  
         by (simp add: strong_less_eq_fltrace_refl)  
        then have "
                  ys @ [[e1]\<^sub>E] @ [[r2]\<^sub>R] = flt2ttobs(fl @\<^sub>\<F>\<^sub>\<L> \<langle>[{x. x \<notin> r2} - {Tick}]\<^sub>\<F>\<^sub>\<L>\<rangle>\<^sub>\<F>\<^sub>\<L>)
                  \<and> flt2goodAcceptance fl p \<and> flt2goodTock fl 
                  \<and> (\<exists>z. FLTick0 Tick z \<and> FL1 z 
                      \<and> {flt2ttobs fl\<^sub>0 |fl\<^sub>0. fl\<^sub>0 \<in> z} \<subseteq> P 
                      \<and> fl @\<^sub>\<F>\<^sub>\<L> \<langle>[{x. x \<notin> r2} - {Tick}]\<^sub>\<F>\<^sub>\<L>\<rangle>\<^sub>\<F>\<^sub>\<L> \<in> z)"
          by blast
        then have "
                  ys @ [[e1]\<^sub>E] @ [[r2]\<^sub>R] = flt2ttobs(fl @\<^sub>\<F>\<^sub>\<L> \<langle>[{x. x \<notin> r2} - {Tick}]\<^sub>\<F>\<^sub>\<L>\<rangle>\<^sub>\<F>\<^sub>\<L>)
                  \<and> flt2goodAcceptance fl p \<and> flt2goodTock fl
                  \<and> flt2goodTock (fl @\<^sub>\<F>\<^sub>\<L> \<langle>[{x. x \<notin> r2} - {Tick}]\<^sub>\<F>\<^sub>\<L>\<rangle>\<^sub>\<F>\<^sub>\<L>) 
                  \<and> (\<exists>z. FLTick0 Tick z \<and> FL1 z 
                      \<and> {flt2ttobs fl\<^sub>0 |fl\<^sub>0. fl\<^sub>0 \<in> z} \<subseteq> P 
                      \<and> fl @\<^sub>\<F>\<^sub>\<L> \<langle>[{x. x \<notin> r2} - {Tick}]\<^sub>\<F>\<^sub>\<L>\<rangle>\<^sub>\<F>\<^sub>\<L> \<in> z)"
          using flt2goodTock_extend_consFL_acceptance by blast
        then have "
                  ys @ [[e1]\<^sub>E] @ [[r2]\<^sub>R] = flt2ttobs(fl @\<^sub>\<F>\<^sub>\<L> \<langle>[{x. x \<notin> r2} - {Tick}]\<^sub>\<F>\<^sub>\<L>\<rangle>\<^sub>\<F>\<^sub>\<L>)
                  \<and> flt2goodAcceptance fl p 
                  \<and> flt2goodAcceptance (fl @\<^sub>\<F>\<^sub>\<L> \<langle>[{x. x \<notin> r2} - {Tick}]\<^sub>\<F>\<^sub>\<L>\<rangle>\<^sub>\<F>\<^sub>\<L>) p
                  \<and> flt2goodTock fl
                  \<and> flt2goodTock (fl @\<^sub>\<F>\<^sub>\<L> \<langle>[{x. x \<notin> r2} - {Tick}]\<^sub>\<F>\<^sub>\<L>\<rangle>\<^sub>\<F>\<^sub>\<L>) 
                  \<and> (\<exists>z. FLTick0 Tick z \<and> FL1 z 
                      \<and> {flt2ttobs fl\<^sub>0 |fl\<^sub>0. fl\<^sub>0 \<in> z} \<subseteq> P 
                      \<and> fl @\<^sub>\<F>\<^sub>\<L> \<langle>[{x. x \<notin> r2} - {Tick}]\<^sub>\<F>\<^sub>\<L>\<rangle>\<^sub>\<F>\<^sub>\<L> \<in> z)"
          by (simp add: flt2goodAcceptance_extend_consFL_acceptance)
        then have "
                  \<exists>fl. ys @ [[e1]\<^sub>E] @ [[r2]\<^sub>R] = flt2ttobs(fl)
                  \<and> flt2goodAcceptance fl p \<and> flt2goodTock fl
                  \<and> (\<exists>z. FLTick0 Tick z \<and> FL1 z 
                      \<and> {flt2ttobs fl\<^sub>0 |fl\<^sub>0. fl\<^sub>0 \<in> z} \<subseteq> P 
                      \<and> fl \<in> z)"
          by blast
        then show ?thesis using Ref e1 by auto
        qed
    qed
  qed
qed

lemma
  shows "(\<exists>Z fl\<^sub>0 fl. prirel p fl Z \<and> Z \<in> fl\<^sub>0 \<and> fl2tt fl\<^sub>0 \<subseteq> P \<and> flt2ttobs(Z) \<in> P \<and> flt2ttobs(fl) = ar) 
         = 
         (\<exists>zr. prirelRef p ar zr [] P \<and> zr \<in> P)"
  apply auto
  oops


  
lemma
  "(\<exists>Z fl. prirel p fl Z \<and> Z \<in> fl\<^sub>0 \<and> flt2ttobs(Z) \<in> P \<and> x = flt2ttobs fl)
   =
   (\<exists>Z fl. prirel p fl Z \<and> Z \<in> fl\<^sub>0 \<and> flt2ttobs(Z) \<in> P \<and> flt2goodTock fl \<and> x = flt2ttobs fl)"
  oops



(* FIXME: Change flt2goodS to accommodate tickWF *)
fun flt2goodS :: "('e ttevent) partialorder \<Rightarrow> ('e ttevent) fltrace \<Rightarrow> bool" where
"flt2goodS p \<langle>A\<rangle>\<^sub>\<F>\<^sub>\<L> = True" |
"flt2goodS p (A #\<^sub>\<F>\<^sub>\<L> fl) = 
  ((case event(A) of  Tock \<Rightarrow> Tock \<in>\<^sub>\<F>\<^sub>\<L> acceptance(A)
                    | Tick \<Rightarrow> acceptance(A) = \<bullet> 
                    | Event a \<Rightarrow> Event a \<in>\<^sub>\<F>\<^sub>\<L> acceptance(A) 
                                 \<and> (acceptance(A) = [{a. a \<in>\<^sub>\<F>\<^sub>\<L> acceptance(A) \<and> \<not>(\<exists>b. b\<in>\<^sub>\<F>\<^sub>\<L>acceptance(A) \<and> a <\<^sup>*p b)}]\<^sub>\<F>\<^sub>\<L>)) \<and> (flt2goodS p fl))" 

(*
lemma flt2ttobs_exists_flt2goodS_for_ttWF_TT3_trace:
  assumes "ttWF fl" "TT3_trace fl"
  shows "\<exists>zr. (flt2ttobs zr) = fl \<and> flt2goodS p zr"
  using assms
proof (induct fl rule:ttWF.induct, auto)
  show "\<exists>zr. flt2ttobs zr = [] \<and> flt2goodS p zr"
    by (intro exI[where x="\<langle>\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>"], auto)
next
  fix X
  show "\<exists>zr. flt2ttobs zr = [[X]\<^sub>R] \<and> flt2goodS p zr"
    by (intro exI[where x="\<langle>[{x. x \<notin> X}]\<^sub>\<F>\<^sub>\<L>\<rangle>\<^sub>\<F>\<^sub>\<L>"], auto)
next
  show "\<exists>zr. flt2ttobs zr = [[Tick]\<^sub>E] \<and> flt2goodS p zr"
    by (intro exI[where x="\<langle>(\<bullet>,Tick)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>"], auto)
next
  fix e \<sigma>
  assume hyp:"(TT3_trace \<sigma> \<Longrightarrow> \<exists>zr. flt2ttobs zr = \<sigma> \<and> flt2goodS p zr)"
  assume assm1:"ttWF \<sigma>"
  assume assm2:"TT3_trace ([Event e]\<^sub>E # \<sigma>)"
  show "\<exists>zr. flt2ttobs zr = [Event e]\<^sub>E # \<sigma> \<and> flt2goodS p zr"
  proof -
    from assm2 have "TT3_trace \<sigma>"
      using TT3_trace_cons_imp_cons by blast
    then have "\<exists>zr. flt2ttobs zr = \<sigma> \<and> flt2goodS p zr"
      using hyp by auto
    then have "\<exists>zr. flt2ttobs(\<langle>([{Event e}]\<^sub>\<F>\<^sub>\<L>,Event e)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>) @ flt2ttobs zr = [Event e]\<^sub>E # \<sigma> \<and> flt2goodS p zr"
      by auto
    then have "\<exists>zr. flt2ttobs(\<langle>([{Event e}]\<^sub>\<F>\<^sub>\<L>,Event e)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L> &\<^sub>\<F>\<^sub>\<L> zr) = [Event e]\<^sub>E # \<sigma> \<and> flt2goodS p (\<langle>([{Event e}]\<^sub>\<F>\<^sub>\<L>,Event e)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L> &\<^sub>\<F>\<^sub>\<L> zr)"
      by auto
    then show ?thesis by blast
  qed
next
  fix X::"'a ttevent set"
  fix zr::"'a ttevent fltrace"
  assume assm1:"ttWF (flt2ttobs zr)"
  assume assm2:"Tock \<notin> X"
  assume assm3:"TT3_trace (flt2ttobs zr)"
  assume assm4:"flt2goodS p zr"
  show "\<exists>zra. flt2ttobs zra = [X]\<^sub>R # [Tock]\<^sub>E # flt2ttobs zr \<and> flt2goodS p zra"
  proof -
    have "\<exists>zra. flt2ttobs zra = flt2ttobs zr \<and> flt2goodS p zra"
      using assm4 by auto
    then have "\<exists>zra. flt2ttobs(\<langle>([{x. x \<notin> X}]\<^sub>\<F>\<^sub>\<L>,Tock)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>) @ flt2ttobs zra = [X]\<^sub>R # [Tock]\<^sub>E # flt2ttobs zr \<and> flt2goodS p zra"
      using assm2 by auto
    then have "\<exists>zra. flt2ttobs(\<langle>([{x. x \<notin> X}]\<^sub>\<F>\<^sub>\<L>,Tock)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L> &\<^sub>\<F>\<^sub>\<L> zra) = [X]\<^sub>R # [Tock]\<^sub>E # flt2ttobs zr \<and> flt2goodS p (\<langle>([{x. x \<notin> X}]\<^sub>\<F>\<^sub>\<L>,Tock)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L> &\<^sub>\<F>\<^sub>\<L> zra)"
      using assm2 by auto
    then show ?thesis by blast
  qed
qed*)



lemma 
 "{flt2ttobs fl|fl. (\<exists>zr. prirelRef p (flt2ttobs(fl)) zr [] P \<and> zr \<in> P)}
  =
  {ar|ar. (\<exists>zr. prirelRef p ar zr [] P \<and> zr \<in> P)}"
  apply auto
  oops

(*
lemma xp:
  assumes "prirelRef p x zr s P"
    shows "\<exists>fl. x = flt2ttobs fl \<and> (\<exists>zr. prirelRef p (flt2ttobs fl) zr s P)"
  using assms  apply (induct p x zr s P rule:prirelRef.induct, auto)
  
      apply (metis flt2ttobs.simps(1) prirelRef.simps(1))
   apply (metis TT3_trace.simps(2) ttWF.simps(2) flt2ttobs_exists_flt2goodS_for_ttWF_TT3_trace insert_Nil prirelRef.simps(2))
  oops*)

lemma
  assumes "prirelRef p x zr [] P"
          "zr \<in> P"
    shows "\<exists>fl. x = flt2ttobs fl \<and> (\<exists>zr. prirelRef p (flt2ttobs fl) zr [] P \<and> zr \<in> P)"
  using assms apply (induct p x zr _ P rule:prirelRef.induct, auto)
  oops

lemma FL2_tt2fl:
  "FL2 (tt2fl(P))"
  unfolding FL2_def tt2fl_def apply auto
  (* Simplifying what needs to be proved *)
  apply (case_tac A, auto)
  apply (case_tac "last \<beta> \<noteq> \<bullet>", auto)
   apply (metis concat_FL_last_not_bullet_absorb)
  (* Requires property on P, namely TT2w, to show this now. *)
  oops

(*
fun goodPriRels :: "'a ttobs list \<Rightarrow> 'a ttobs list \<Rightarrow> bool" where
"goodPriRels [] [] = True" |
"goodPriRels [[R]\<^sub>R] [[S]\<^sub>R] = True" |
"goodPriRels (x # xs) (y # ys) = (goodPriRels xs ys)" |
"goodPriRels xs ys = False"

lemma goodTocks_goodPriRels:
  assumes "flt2goodTock xs" "flt2goodTock ys"
          "prirel p xs ys"
    shows "goodPriRels (flt2ttobs xs) (flt2ttobs ys)"
  using assms apply(induct p xs ys rule:prirel.induct, auto)
  by (case_tac A, auto)+

lemma
  assumes "flt2goodTock xs" "flt2goodTock ys" "prirel p xs ys"
  shows "(flt2ttobs xs) \<le>\<^sub>C (flt2ttobs ys)"
  nitpick

lemma 
  assumes "prirel p fl Y" "flt2goodTock Y"
  shows "flt2goodTock fl"
  using assms nitpick

lemma
  assumes "ttWF (flt2ttobs xs)"
  shows "ttWF ((flt2ttobs xs) @ (flt2ttobs \<langle>x,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>))"
  nitpick

  

lemma
  assumes "size xs = size ys"
    shows "(prirelRef p xs ys [] P \<and> prirelRef p x y ys P) = prirelRef p (xs@x) (ys@y) [] P"
  using assms nitpick[card=4]
  (*apply (induct p xs ys _ P arbitrary:x y rule:prirelRef.induct)
  apply (simp_all)
  sledgehammer[debug=true]
     apply (metis ttWF.elims(2) ttWF.simps(11) ttWF.simps(12) ttWF.simps(13) prirelRef.simps(1) prirelRef.simps(2))
 
    apply auto
  apply (induct x rule:rev_induct, auto)
  apply (metis append_Nil2 ttWF.elims(2) prirelRef.simps(46))
  sledgehammer[debug=true]
  thm prirelRef.induct*)
*)
(*
lemma
  assumes "prirelRef p xs ys [] P" "size xs = size ys"
          "prirelRef p x y ys P" "ttWF (xs@x)" "ttWF (ys@y)"
    shows "prirelRef p (xs@x) (ys@y) [] P"
  using assms
proof (induct p xs ys "[]::'a ttobs list" P arbitrary:x y rule:prirelRef.induct, simp_all)
  fix pa S R xa ya Q
  assume "prirelref pa S = R"
         "prirelRef pa xa ya [[S]\<^sub>R] Q"
         "ttWF ([R]\<^sub>R # xa)"
         "ttWF ([S]\<^sub>R # ya)"
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
               prirelRef pa aa zz [] Q \<Longrightarrow> prirelRef pa x y zz Q \<Longrightarrow> ttWF (aa @ x) \<Longrightarrow> ttWF (zz @ y) \<Longrightarrow> prirelRef pa (aa @ x) (zz @ y) [] Q)"
      "R = prirelref pa S \<and> prirelRef pa aa zz [[S]\<^sub>R, [Tock]\<^sub>E] Q"
      "List.length aa = List.length zz"
      "prirelRef pa xa ya ([S]\<^sub>R # [Tock]\<^sub>E # zz) Q"
      "ttWF (aa @ xa)"
      "ttWF (zz @ ya)"
  then show "prirelRef pa (aa @ xa) (zz @ ya) [[S]\<^sub>R, [Tock]\<^sub>E] Q"
    oops

lemma
  assumes "prirelRef p xs ys [] P" "ttWF xs" "ttWF ys" "ttWF x" "ttWF y" "TTwf P" "ys \<in> P" "TT1w P"
          "prirelRef p x y ys P" "ttWF (xs@x)" "ttWF (ys@y)" "(ys@y) \<in> P"
    shows "prirelRef p (xs@x) (ys@y) [] P"
  using assms 
  apply (induct p xs ys "[]::'a ttobs list" P rule:prirelRef.induct)
  apply (simp_all)
(*    apply auto
  apply (metis ttWF.elims(2) ttWF.simps(11) ttWF.simps(12) ttWF.simps(13) prirelRef.simps(2))
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
      apply (metis append_self_conv2 assms(3) ttWF.elims(2) prirelRef.simps(2) prirelRef.simps(46))
  apply (induct ys rule:rev_induct, auto)
  sledgehammer[debug=true]*)
(*  apply (metis ttWF.elims(2) prirelRef.simps(2) prirelRef.simps(28))
  apply (metis ttWF.elims(2) ttWF.simps(11) ttWF.simps(12) ttWF.simps(13) prirelRef.simps(46))
  sledgehammer[debug=true]*)
*)
lemma
  assumes "length xs = length ys" "last ys = \<bullet>"
          "prirel p xs (ys &\<^sub>\<F>\<^sub>\<L> \<langle>y\<rangle>\<^sub>\<F>\<^sub>\<L>)"
        shows "prirel p xs ys"
  oops



lemma flt2ttobs_cons_no_extend_not_flt2goodTock:
  assumes "\<not> flt2goodTock fl"
  shows "flt2ttobs (fl &\<^sub>\<F>\<^sub>\<L> xs) = flt2ttobs(fl)"
  using assms apply (induct fl rule:flt2ttobs.induct, auto)
  by (case_tac A, auto)

lemma flt2ttobs_cons_acceptance_eq_cons:
  assumes "last fl = \<bullet>" "flt2goodTock fl"
  shows "flt2ttobs (fl &\<^sub>\<F>\<^sub>\<L> \<langle>y\<rangle>\<^sub>\<F>\<^sub>\<L>) = flt2ttobs(fl) @ flt2ttobs(\<langle>y\<rangle>\<^sub>\<F>\<^sub>\<L>)"
  using assms by (induct fl rule:flt2ttobs.induct, auto)

lemma prirel_flt2goodTock_tgt_imp_src:
  assumes "prirel p fl Y" "flt2goodTock fl"
  shows "flt2goodTock Y"
  using assms apply (induct p fl Y rule:prirel.induct, auto)
  by (case_tac A, auto, case_tac a, auto)+

(*
lemma
  assumes "prirelRef p (flt2ttobs xs) (flt2ttobs ys) [] P" "flt2goodTock ys" "length ys = length xs"
  shows "flt2goodTock xs"
  using assms apply (induct xs ys rule:ftrace_cons_induct_both_eq_length2, auto)
  apply (simp add: concat_FL_last_not_bullet_absorb)
  sledgehammer[debug=true]
  apply (simp add: concat_FL_last_not_bullet_absorb)
  apply (induct ys rule:flt2ttobs.induct, auto)*)


(* It would be nice to show the following, but the conclusion is stronger
   than necessary to establish the correspondence we want. It may, however,
   be easier to prove depending on the definition of prirelRef. *)

(*
lemma prirelRef_extend_rhs_ttWF:
  assumes "prirelRef p xs ys s P" "ttWF (ys @ [[R]\<^sub>R])"
  shows "prirelRef p xs (ys @ [[R]\<^sub>R]) s P"
  using assms apply (induct p xs ys s P rule:prirelRef.induct, auto)
  by (metis ttWF.simps(10) ttWF.simps(4) ttWF.simps(6) ttevent.exhaust list.exhaust snoc_eq_iff_butlast)+
*)



lemma prirelRef_extend_both_events_non_maximal_ttWF:
  assumes "prirelRef p xs ys s P" "ttWF (xs @ [[e\<^sub>1]\<^sub>E])" "ttWF (ys @ [[e\<^sub>1]\<^sub>E])" "TTwf P"
          "(\<exists>Z. s @ ys @ [[Z]\<^sub>R] \<in> P \<and> e\<^sub>1 \<notin> Z \<and> \<not>(\<exists>b. b \<notin> Z \<and> e\<^sub>1 <\<^sup>*p b))" 
  shows "prirelRef p (xs @ [[e\<^sub>1]\<^sub>E]) (ys @ [[e\<^sub>1]\<^sub>E]) s P"
  using assms apply (induct p xs ys s P rule:prirelRef.induct, auto)
    apply (cases e\<^sub>1) apply auto[1]
  using TTwf_cons_end_not_refusal_refusal apply blast+
  by (metis append_Nil ttWF.simps(10) ttWF.simps(4) ttWF.simps(6) ttWF_prefix_is_ttWF ttevent.exhaust list.exhaust)+

(* FIXME 
lemma flt2ttobs_exists_for_ttWF_TT3_trace:
  assumes "ttWF fl" "TT3_trace fl"
  shows "\<exists>zr. (flt2ttobs zr) = fl"
  using assms
proof (induct fl rule:ttWF.induct, auto)
  show "\<exists>zr. flt2ttobs zr = []"
    by (intro exI[where x="\<langle>\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>"], auto)
next
  fix X
  show "\<exists>zr. flt2ttobs zr = [[X]\<^sub>R]"
    by (intro exI[where x="\<langle>[{x. x \<notin> X}]\<^sub>\<F>\<^sub>\<L>\<rangle>\<^sub>\<F>\<^sub>\<L>"], auto)
next
  show "\<exists>zr. flt2ttobs zr = [[Tick]\<^sub>E]"
    by (intro exI[where x="\<langle>(\<bullet>,Tick)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>"], auto)
next
  fix e \<sigma>
  assume hyp:"(TT3_trace \<sigma> \<Longrightarrow> \<exists>zr. flt2ttobs zr = \<sigma>)"
  assume assm1:"ttWF \<sigma>"
  assume assm2:"TT3_trace ([Event e]\<^sub>E # \<sigma>)"
  show "\<exists>zr. flt2ttobs zr = [Event e]\<^sub>E # \<sigma>"
  proof -
    from assm2 have "TT3_trace \<sigma>"
      using TT3_trace_cons_imp_cons by blast
    then have "\<exists>zr. flt2ttobs zr = \<sigma>"
      using hyp by auto
    then have "\<exists>zr. flt2ttobs(\<langle>(\<bullet>,Event e)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>) @ flt2ttobs zr = [Event e]\<^sub>E # \<sigma>"
      by auto
    then have "\<exists>zr. flt2ttobs(\<langle>(\<bullet>,Event e)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L> &\<^sub>\<F>\<^sub>\<L> zr) = [Event e]\<^sub>E # \<sigma>"
      by auto
    then show ?thesis by blast
  qed
next
  fix X::"'a ttevent set"
  fix zr::"'a ttevent fltrace"
  assume assm1:"ttWF (flt2ttobs zr)"
  assume assm2:"Tock \<notin> X"
  assume assm3:"TT3_trace (flt2ttobs zr)"
  show "\<exists>zra. flt2ttobs zra = [X]\<^sub>R # [Tock]\<^sub>E # flt2ttobs zr"
  proof -
    have "\<exists>zra. flt2ttobs zra = flt2ttobs zr"
      by auto
    then have "\<exists>zra. flt2ttobs(\<langle>([{x. x \<notin> X}]\<^sub>\<F>\<^sub>\<L>,Tock)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>) @ flt2ttobs zra = [X]\<^sub>R # [Tock]\<^sub>E # flt2ttobs zr"
      using assm2 by auto
    then have "\<exists>zra. flt2ttobs(\<langle>([{x. x \<notin> X}]\<^sub>\<F>\<^sub>\<L>,Tock)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L> &\<^sub>\<F>\<^sub>\<L> zra) = [X]\<^sub>R # [Tock]\<^sub>E # flt2ttobs zr"
      using assm2 by auto
    then show ?thesis by blast
  qed
qed
*)

lemma tt:
  assumes "prirel p fl Y" "FL1 fl\<^sub>0" "FLTick0 Tick fl\<^sub>0"
          "Y \<in> fl\<^sub>0"
          "fl2tt fl\<^sub>0 \<subseteq> P"
          "flt2ttobs Y \<in> P" "size (flt2ttobs fl) = size (flt2ttobs Y)"
    shows "prirelRef p (flt2ttobs fl) (flt2ttobs Y) [] P"
  oops

lemma
  assumes "prirel p fl Y" "FL1 fl\<^sub>0" "FLTick0 Tick fl\<^sub>0"
          "Y \<in> fl\<^sub>0"
          "fl2tt fl\<^sub>0 \<subseteq> P"
          "flt2ttobs Y \<in> P"
    shows "\<exists>zr. prirelRef p (flt2ttobs fl) zr [] P  \<and> zr \<in> P"
  oops

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

lemma flt2ttobs_is_TT3_trace [simp]:
  "TT3_trace (flt2ttobs xs)"
  apply (induct xs)
   apply (case_tac x, simp)
   apply auto[1]
  apply (case_tac x1a, case_tac y, case_tac a)
   apply auto[1]
   apply (metis TT3_trace.simps(2) TT3_trace.simps(4) neq_Nil_conv)
  apply (case_tac b, auto)
  apply (metis TT3_trace.simps(2) TT3_trace.simps(4) neq_Nil_conv)
  by (metis TT3_trace.simps(2) TT3_trace.simps(4) neq_Nil_conv)

lemma pp:
  assumes "prirel p fl Y" "FL1 fl\<^sub>0" "FLTick0 Tick fl\<^sub>0"
          "Y \<in> fl\<^sub>0"
          "fl2tt fl\<^sub>0 \<subseteq> P"
          "flt2ttobs Y \<in> P"
          "flt2goodTock fl" "TTwf P"
    shows "prirelRef p (flt2ttobs fl) (flt2ttobs Y) [] P"
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
  then have prirelRef:"prirelRef p (flt2ttobs xs) (flt2ttobs ys) [] P"
    by (metis (mono_tags, lifting) flt2goodTock_cons_imp_prefix flt2ttobs_extn mem_Collect_eq subset_eq x_le_concat2_FL1 prirel_cons_eq_length_imp_prirel_eq_prefix)
  then show ?case using 3
  proof (cases "flt2goodTock xs")
    case True
    then have "flt2goodTock ys"
      using 3 prirel_cons_eq_length_imp_prirel_eq_prefix prirel_flt2goodTock_tgt_imp_src by blast
    then have flt2_ys_y:"flt2ttobs (ys &\<^sub>\<F>\<^sub>\<L> \<langle>y\<rangle>\<^sub>\<F>\<^sub>\<L>) = flt2ttobs (ys) @ flt2ttobs(\<langle>y\<rangle>\<^sub>\<F>\<^sub>\<L>)"
      using 3 by (simp add: flt2ttobs_cons_acceptance_eq_cons)
    then have "flt2ttobs (ys) @ flt2ttobs(\<langle>y\<rangle>\<^sub>\<F>\<^sub>\<L>) \<in> P"
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
            
           (* then obtain yR where yR:"flt2ttobs(\<langle>y\<rangle>\<^sub>\<F>\<^sub>\<L>) = [[yR]\<^sub>R]"
              by simp
            then have "ttWF (flt2ttobs (ys &\<^sub>\<F>\<^sub>\<L> \<langle>y\<rangle>\<^sub>\<F>\<^sub>\<L>))"
              by (meson "3.prems"(4) FLTick0_def assms(3) flt2ttobs_is_ttWF)
            then have "prirelRef p (flt2ttobs xs) ((flt2ttobs ys) @ [[yR]\<^sub>R]) [] P"
              using acset 3 prirelRef xnil flt2_ys_y prirelRef_extend_rhs_ttWF 
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
          by (metis (no_types, lifting) Collect_cong acceptance.distinct(1) amember.simps(2) flt2ttobs.simps(1) prirel.simps(1) prirelacc_eq_prirelref_via_flt2ttobs)
        then obtain xR where xR:"flt2ttobs(\<langle>x\<rangle>\<^sub>\<F>\<^sub>\<L>) = [[xR]\<^sub>R]"
          by (simp add: acset)
        then obtain yR where yR:"flt2ttobs(\<langle>y\<rangle>\<^sub>\<F>\<^sub>\<L>) = [[yR]\<^sub>R] \<and> prirelref p yR = xR"
          using 3 yA
          by (metis (no_types, lifting) \<open>prirel p \<langle>[x2]\<^sub>\<F>\<^sub>\<L>\<rangle>\<^sub>\<F>\<^sub>\<L> \<langle>[yA]\<^sub>\<F>\<^sub>\<L>\<rangle>\<^sub>\<F>\<^sub>\<L>\<close> acceptance.distinct(1) acset flt2ttobs.simps(1) prirel.simps(1) prirelacc_eq_prirelref_via_flt2ttobs)

        have "ttWF (flt2ttobs (ys &\<^sub>\<F>\<^sub>\<L> \<langle>y\<rangle>\<^sub>\<F>\<^sub>\<L>))"
          by (meson "3.prems"(4) FLTick0_def assms(3) flt2ttobs_is_ttWF)
        then have "ttWF ((flt2ttobs ys) @ [[yR]\<^sub>R])"
          by (metis flt2_ys_y yR)
        then have "prirelRef p ((flt2ttobs xs) @ [[xR]\<^sub>R]) ((flt2ttobs ys) @ [[yR]\<^sub>R]) [] P"
          using prirelRef_extend_both_refusal_ttWF
          using prirelRef yR by blast
        then show ?thesis
          using "3.hyps"(3) True flt2_ys_y flt2ttobs_cons_acceptance_eq_cons xR yR by fastforce
      qed
  next
    case False
    then have flt2_xsx:"flt2ttobs (xs &\<^sub>\<F>\<^sub>\<L> \<langle>x\<rangle>\<^sub>\<F>\<^sub>\<L>) = flt2ttobs (xs)"
      by (simp add: flt2ttobs_cons_no_extend_not_flt2goodTock)
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
      then obtain yR where yR:"flt2ttobs(\<langle>y\<rangle>\<^sub>\<F>\<^sub>\<L>) = [[yR]\<^sub>R]"
        by simp
      then have ttWF_ys_y:"ttWF (flt2ttobs (ys &\<^sub>\<F>\<^sub>\<L> \<langle>y\<rangle>\<^sub>\<F>\<^sub>\<L>))"
        by (meson "3.prems"(4) FLTick0_def assms(3) flt2ttobs_is_ttWF)
      then show ?thesis
      proof (cases "flt2goodTock ys")
        case True
        then have "prirelRef p (flt2ttobs xs) ((flt2ttobs ys) @ [[yR]\<^sub>R]) [] P"
          using acset 3 prirelRef flt2_xsx prirelRef_extend_rhs_ttWF
          by (metis ttWF_ys_y flt2ttobs_cons_acceptance_eq_cons yR)
        then show ?thesis
          using "3.hyps"(4) True flt2_xsx flt2ttobs_cons_acceptance_eq_cons yR by fastforce
      next
        case False
        then have "flt2ttobs (ys &\<^sub>\<F>\<^sub>\<L> \<langle>y\<rangle>\<^sub>\<F>\<^sub>\<L>) = flt2ttobs (ys)"
          by (simp add: flt2ttobs_cons_no_extend_not_flt2goodTock)
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
  then have prirelRef:"prirelRef p (flt2ttobs xs) (flt2ttobs ys) [] P"
    using prirel_cons_eq_length_imp 4
    by (metis (mono_tags, lifting) xs_is_flt2goodTock flt2ttobs_extn mem_Collect_eq subset_eq x_le_concat2_FL1)
  then have "prirel p \<langle>x,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L> \<langle>y,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>"
    using "4.hyps"(2) "4.hyps"(3) "4.prems"(1) prirel_cons_eq_length_imp_prirel_acceptances by blast
 
  from xs_is_flt2goodTock ys_is_flt2goodTock
  have flt2_ys_y:"flt2ttobs (ys &\<^sub>\<F>\<^sub>\<L> \<langle>y,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>) = flt2ttobs (ys) @ flt2ttobs(\<langle>y,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>)"
    using 4 flt2ttobs_acceptance_cons_eq_list_cons by blast
  then have "flt2ttobs (ys) @ flt2ttobs(\<langle>y,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>) \<in> P"
    using 4 by (simp)

  from xs_is_flt2goodTock ys_is_flt2goodTock
  have flt2_xs_x:"flt2ttobs (xs &\<^sub>\<F>\<^sub>\<L> \<langle>x,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>) = flt2ttobs (xs) @ flt2ttobs(\<langle>x,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>)"
    using 4 flt2ttobs_acceptance_cons_eq_list_cons
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
      
      then obtain xR where xR:"flt2ttobs(\<langle>x,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>) = [[xR]\<^sub>R,[Tock]\<^sub>E]"
        using True xAE xA_not_bullet by auto
      then obtain yR where yR:"flt2ttobs(\<langle>y,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>) = [[yR]\<^sub>R,[Tock]\<^sub>E] \<and> prirelref p yR = xR"
        using True xAE yAE xA_not_bullet apply auto
        using yA_not_bullet apply simp
        using yA_not_bullet apply simp
        by (metis (no_types, lifting) Collect_cong \<open>prirel p \<langle>x,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L> \<langle>y,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>\<close> acceptance_set flt2ttobs.simps(1) prirel.simps(4) prirelacc_eq_prirelref_via_flt2ttobs)

      then have "ttWF (flt2ttobs (ys) @ [[yR]\<^sub>R,[Tock]\<^sub>E])"
        by (metis "4.prems"(4) FLTick0_def True assms(3) flt2_ys_y flt2ttobs_is_ttWF)
      then have "prirelRef p (flt2ttobs (xs) @ [[xR]\<^sub>R,[Tock]\<^sub>E]) (flt2ttobs (ys) @ [[yR]\<^sub>R,[Tock]\<^sub>E]) [] P"
        using prirelRef prirelRef_extend_both_tock_refusal_ttWF
        using yR
        by (metis TT3_trace.simps(3) flt2ttobs_is_TT3_trace xR)
      then have "prirelRef p (flt2ttobs (xs &\<^sub>\<F>\<^sub>\<L> \<langle>x,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>)) (flt2ttobs (ys &\<^sub>\<F>\<^sub>\<L> \<langle>y,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>)) [] P"
        using flt2_xs_x flt2_ys_y xR yR by auto
      then show ?thesis by auto
    next
      case False
      then have "flt2ttobs(\<langle>x,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>) = [[yEvent]\<^sub>E]"
        using xAE by auto
      then have "flt2ttobs(\<langle>y,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>) = [[yEvent]\<^sub>E]"
        using xAE yAE
        using False by fastforce

      then have ttWF_ys_y:"ttWF (flt2ttobs (ys &\<^sub>\<F>\<^sub>\<L> \<langle>y,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>))"
        using 4 
        by (meson FLTick0_def flt2ttobs_is_ttWF)

      then have ttWF_xs_x:"ttWF (flt2ttobs (xs &\<^sub>\<F>\<^sub>\<L> \<langle>x,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>))"
        using 4 
        using prirel_rhs_tickWF_imp_lhs_tickWF
        by (metis FLTick0_def flt2ttobs_is_ttWF)

      then have "prirelRef p (flt2ttobs (xs) @ [[yEvent]\<^sub>E]) (flt2ttobs (ys) @ [[yEvent]\<^sub>E]) [] P"
        using prirelRef
      proof (cases "maximal(p,yEvent)")
        case True
        then show ?thesis
          by (metis \<open>flt2ttobs \<langle>x,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L> = [[yEvent]\<^sub>E]\<close> \<open>flt2ttobs \<langle>y,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L> = [[yEvent]\<^sub>E]\<close> ttWF_xs_x ttWF_ys_y flt2_xs_x flt2_ys_y flt2ttobs_is_TT3_trace prirelRef prirelRef_extend_both_events_maximal_ttWF)
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
            then have "flt2ttobs(ys &\<^sub>\<F>\<^sub>\<L> \<langle>yA\<rangle>\<^sub>\<F>\<^sub>\<L>) \<in> P"
              using 4 fl2tt_def by blast
            then obtain yR where yR:"flt2ttobs (ys) @ [[yR]\<^sub>R] \<in> P \<and> flt2ttobs(\<langle>yA\<rangle>\<^sub>\<F>\<^sub>\<L>) = [[yR]\<^sub>R] \<and> yEvent \<notin> yR"
              using "4.hyps"(4) \<open>yA \<noteq> \<bullet>\<close> flt2ttobs_cons_acceptance_eq_cons yAE ys_is_flt2goodTock by fastforce
            then have "flt2ttobs (ys) @ [[yR]\<^sub>R] \<in> P \<and> yEvent \<notin> yR \<and> \<not>(\<exists>b. b \<notin> yR \<and> yEvent <\<^sup>*p b)"
              using \<open>\<nexists>b. b \<in>\<^sub>\<F>\<^sub>\<L> yA \<and> yEvent <\<^sup>*p b\<close> \<open>yA \<noteq> \<bullet>\<close> by auto
            then show ?thesis
              by (metis \<open>flt2ttobs \<langle>x,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L> = [[yEvent]\<^sub>E]\<close> \<open>flt2ttobs \<langle>y,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L> = [[yEvent]\<^sub>E]\<close> append_Nil assms(8) ttWF_xs_x ttWF_ys_y flt2_xs_x flt2_ys_y prirelRef prirelRef_extend_both_events_non_maximal_ttWF)
              
          next
            case (acset x2)
            then have "yA \<noteq> \<bullet>"
              using \<open>prirel p \<langle>x,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L> \<langle>y,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>\<close> xAE yAE by auto
            then obtain yASet where yASet:"[yASet]\<^sub>\<F>\<^sub>\<L> = yA \<and> yEvent \<in> yASet"
              using yAE by (cases yA, auto)
            then have "x2 = {a. a \<in> yASet \<and> \<not>(\<exists>b. b\<in>yASet \<and> a <\<^sup>*p b)}"
              using \<open>prirel p \<langle>x,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L> \<langle>y,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>\<close> acset xAE yAE by auto
            then have "flt2ttobs(ys &\<^sub>\<F>\<^sub>\<L> \<langle>[yASet]\<^sub>\<F>\<^sub>\<L>\<rangle>\<^sub>\<F>\<^sub>\<L>) \<in> P"
              by (metis (mono_tags, lifting) "4"(6) "4"(8) "4"(9) acceptance_set contra_subsetD fl2tt_def fltrace_FL1_cons_acceptance_prefix mem_Collect_eq yAE yASet)
            then obtain yR where yR:"flt2ttobs (ys) @ [[yR]\<^sub>R] \<in> P \<and> flt2ttobs(\<langle>[yASet]\<^sub>\<F>\<^sub>\<L>\<rangle>\<^sub>\<F>\<^sub>\<L>) = [[yR]\<^sub>R] \<and> yEvent \<notin> yR"
              using "4.hyps"(4) \<open>yA \<noteq> \<bullet>\<close> flt2ttobs_cons_acceptance_eq_cons yAE yASet ys_is_flt2goodTock by fastforce
            then have "flt2ttobs (ys) @ [[yR]\<^sub>R] \<in> P \<and> yEvent \<notin> yR \<and> \<not>(\<exists>b. b \<notin> yR \<and> yEvent <\<^sup>*p b)"
              using \<open>prirel p \<langle>x,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L> \<langle>y,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>\<close> acset xAE yAE yASet by auto
            then show ?thesis
              by (metis \<open>flt2ttobs \<langle>x,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L> = [[yEvent]\<^sub>E]\<close> \<open>flt2ttobs \<langle>y,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L> = [[yEvent]\<^sub>E]\<close> append_Nil assms(8) ttWF_xs_x ttWF_ys_y flt2_xs_x flt2_ys_y prirelRef prirelRef_extend_both_events_non_maximal_ttWF)
              
          qed
        qed
        then show ?thesis
          using \<open>flt2ttobs \<langle>x,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L> = [[yEvent]\<^sub>E]\<close> \<open>flt2ttobs \<langle>y,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L> = [[yEvent]\<^sub>E]\<close> flt2_xs_x flt2_ys_y by auto
      qed
    qed

lemma
  assumes "prirel p fl Y" "FL1 fl\<^sub>0" "FLTick0 Tick fl\<^sub>0"
          "Y \<in> fl\<^sub>0"
          "fl2tt fl\<^sub>0 \<subseteq> P"
          "flt2ttobs Y \<in> P"
          "ar = flt2ttobs fl" "flt2goodTock fl" "TTwf P"
        shows "\<exists>zr. prirelRef p (flt2ttobs fl) zr [] P \<and> zr \<in> P"
  using pp 
  using assms(1) assms(2) assms(3) assms(4) assms(5) assms(6) assms(8) assms(9) by blast

lemma
  assumes "prirelRef p (flt2ttobs fl) (flt2ttobs zr) [] P"
  shows "prirelRef p (flt2ttobs fl) (flt2ttobs zr) [] P \<and> length fl = length zr"
  nitpick
  oops

lemma prirelRef_flt2ttobs_both_eq_length_flt2goodTock_both:
  assumes "prirelRef p (flt2ttobs xs) (flt2ttobs ys) zs P" "flt2goodTock xs" "length xs = length ys"
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

lemma ttWF2_ttWF_imp:
  assumes "ttWF x" "ttWF y"
  shows "ttWF2 x y"
  using assms ttWF2_ttWF by blast

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
  assumes "prirelRef p (flt2ttobs fl) (flt2ttobs zr) [] P" "length fl = length zr"
  shows "size (flt2ttobs fl) = size (flt2ttobs zr)"
  using assms
  apply (induct fl zr rule:ftrace_cons_induct_both_eq_length, auto)
    apply (case_tac y, auto)
  oops



lemma TT1w_prefix_is_in:
  assumes "TT1w P" "s @ t \<in> P"
  shows "s \<in> P"
  using assms unfolding TT1w_def 
  using tt_prefix_concat by blast

lemma
  assumes "prirelRef p (x @ xs) (y @ ys) s P" "size x = size y"
  shows "prirelRef p xs ys (s @ x) P"
  using assms apply (induct p x y s P arbitrary:xs ys rule:prirelRef.induct, auto)
   apply (case_tac xsa, auto, case_tac ysa, auto, case_tac ysa, auto)
   apply (case_tac a, auto, case_tac aa, auto)
     apply (case_tac x1, auto, case_tac x1a, auto)
    apply (case_tac x1, auto, case_tac x1a, auto)
  oops

lemma prirelRef_Event_common_extend:
  assumes "prirelRef p ([[Event x1]\<^sub>E] @ xs) ([[Event x1]\<^sub>E] @ ys) s P"
  shows "prirelRef p xs ys (s@[[Event x1]\<^sub>E]) P"
  using assms by (induct p xs ys s P arbitrary:xs ys rule:prirelRef.induct, auto)

lemma prirelRef_of_both_flt2ttobs_cons_acceptance_imp_prirel_acceptance:
  assumes "prirelRef p (flt2ttobs (xs &\<^sub>\<F>\<^sub>\<L> \<langle>x\<rangle>\<^sub>\<F>\<^sub>\<L>)) (flt2ttobs (ys &\<^sub>\<F>\<^sub>\<L> \<langle>y\<rangle>\<^sub>\<F>\<^sub>\<L>)) s P" 
          "last xs = \<bullet>" "last ys = \<bullet>"
          "flt2goodTock xs" "flt2goodTock ys"
  shows "prirel p \<langle>x\<rangle>\<^sub>\<F>\<^sub>\<L> \<langle>y\<rangle>\<^sub>\<F>\<^sub>\<L>" (* FIXME: better proof please.. *)
  using assms 
proof (induct p xs ys arbitrary:s x y rule:prirel.induct)
  case (1 p A Z)
  then show ?case 
  proof (cases y)
    case acnil
    then show ?thesis using 1
      apply auto
      by (cases x, auto)
  next
    case (acset x2)
    then show ?thesis using 1 
      apply auto
      apply (cases x, safe)
      apply force
      by (metis (no_types, lifting) "1.prems"(1) acceptance.simps(3) bullet_left_zero2 flt2ttobs.simps(1) prirelRef.simps(2) prirelacc_eq_prirelref_via_flt2ttobs)
  qed
next
case (2 p A Z zz)
  then show ?case
    apply (cases x, auto, cases A, auto)
    by (cases Z, auto, case_tac a, auto, case_tac b, auto, case_tac b, auto)+
next
case (3 p A aa Z)
  then show ?case
    apply (cases y, auto, cases Z, auto)
    by (cases A, auto, case_tac a, auto, case_tac b, auto, case_tac b, auto)+
next
  case (4 p A aa Z zz)
  then obtain Aa a Zz z where A:"A = (Aa,a)\<^sub>\<F>\<^sub>\<L> \<and> (Aa = \<bullet> \<or> a \<in>\<^sub>\<F>\<^sub>\<L> Aa)"
                          and Z:"Z = (Zz,z)\<^sub>\<F>\<^sub>\<L> \<and> (Zz = \<bullet> \<or> z \<in>\<^sub>\<F>\<^sub>\<L> Zz)"
    by (metis fltrace.inject(2) fltrace_add_idem plus_aevent_def plus_fltrace.simps(3))

  have flt2goodTocks:
        "flt2goodTock \<langle>A,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>" "flt2goodTock (aa &\<^sub>\<F>\<^sub>\<L> \<langle>x\<rangle>\<^sub>\<F>\<^sub>\<L>)"
        "flt2goodTock \<langle>Z,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>" "flt2goodTock (zz &\<^sub>\<F>\<^sub>\<L> \<langle>y\<rangle>\<^sub>\<F>\<^sub>\<L>)"
    using "4.prems" apply auto
    by (metis Finite_Linear_Model.last.simps(1) butlast_last_FL flt2goodTock_extend_consFL_acceptance last_bullet_butlast_last)+
    
  from 4 have "prirelRef p (flt2ttobs ((A #\<^sub>\<F>\<^sub>\<L> aa) &\<^sub>\<F>\<^sub>\<L> \<langle>x\<rangle>\<^sub>\<F>\<^sub>\<L>)) (flt2ttobs ((Z #\<^sub>\<F>\<^sub>\<L> zz) &\<^sub>\<F>\<^sub>\<L> \<langle>y\<rangle>\<^sub>\<F>\<^sub>\<L>)) s P"
    by auto
  then have "prirelRef p (flt2ttobs (\<langle>A,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L> &\<^sub>\<F>\<^sub>\<L> (aa &\<^sub>\<F>\<^sub>\<L> \<langle>x\<rangle>\<^sub>\<F>\<^sub>\<L>))) (flt2ttobs (\<langle>Z,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L> &\<^sub>\<F>\<^sub>\<L> (zz &\<^sub>\<F>\<^sub>\<L> \<langle>y\<rangle>\<^sub>\<F>\<^sub>\<L>))) s P"
    by auto
  then have "prirelRef p (flt2ttobs (\<langle>A,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>) @ flt2ttobs(aa &\<^sub>\<F>\<^sub>\<L> \<langle>x\<rangle>\<^sub>\<F>\<^sub>\<L>)) (flt2ttobs (\<langle>Z,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>) @ flt2ttobs(zz &\<^sub>\<F>\<^sub>\<L> \<langle>y\<rangle>\<^sub>\<F>\<^sub>\<L>)) s P"
  proof -
    have "flt2ttobs (\<langle>A,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L> &\<^sub>\<F>\<^sub>\<L> (aa &\<^sub>\<F>\<^sub>\<L> \<langle>x\<rangle>\<^sub>\<F>\<^sub>\<L>)) = flt2ttobs (\<langle>A,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>) @ flt2ttobs(aa &\<^sub>\<F>\<^sub>\<L> \<langle>x\<rangle>\<^sub>\<F>\<^sub>\<L>)"
              "flt2ttobs (\<langle>Z,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L> &\<^sub>\<F>\<^sub>\<L> (zz &\<^sub>\<F>\<^sub>\<L> \<langle>y\<rangle>\<^sub>\<F>\<^sub>\<L>)) = flt2ttobs (\<langle>Z,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>) @ flt2ttobs(zz &\<^sub>\<F>\<^sub>\<L> \<langle>y\<rangle>\<^sub>\<F>\<^sub>\<L>)"
      using flt2goodTocks by auto
    then show ?thesis
      using \<open>prirelRef p (flt2ttobs (\<langle>A,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L> &\<^sub>\<F>\<^sub>\<L> (aa &\<^sub>\<F>\<^sub>\<L> \<langle>x\<rangle>\<^sub>\<F>\<^sub>\<L>))) (flt2ttobs (\<langle>Z,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L> &\<^sub>\<F>\<^sub>\<L> (zz &\<^sub>\<F>\<^sub>\<L> \<langle>y\<rangle>\<^sub>\<F>\<^sub>\<L>))) s P\<close> by auto 
  qed

  then have pp:"prirelRef p (flt2ttobs (\<langle>(Aa,a)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>) @ flt2ttobs(aa &\<^sub>\<F>\<^sub>\<L> \<langle>x\<rangle>\<^sub>\<F>\<^sub>\<L>)) (flt2ttobs (\<langle>(Zz,z)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>) @ flt2ttobs(zz &\<^sub>\<F>\<^sub>\<L> \<langle>y\<rangle>\<^sub>\<F>\<^sub>\<L>)) s P"
    using A Z by auto

  (* Aim is to deduce prirelRef p (flt2ttobs (aa &\<^sub>\<F>\<^sub>\<L> \<langle>?x\<rangle>\<^sub>\<F>\<^sub>\<L>)) (flt2ttobs (zz &\<^sub>\<F>\<^sub>\<L> \<langle>?y\<rangle>\<^sub>\<F>\<^sub>\<L>)) ?s P *)
  then show ?case
  proof (cases a)
    case (Event x1)
    then have p1:"prirelRef p ([[Event x1]\<^sub>E] @ flt2ttobs(aa &\<^sub>\<F>\<^sub>\<L> \<langle>x\<rangle>\<^sub>\<F>\<^sub>\<L>)) (flt2ttobs (\<langle>(Zz,z)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>) @ flt2ttobs(zz &\<^sub>\<F>\<^sub>\<L> \<langle>y\<rangle>\<^sub>\<F>\<^sub>\<L>)) s P"
      using pp A by auto
    then have "flt2ttobs (\<langle>(Zz,z)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>) = [[Event x1]\<^sub>E]"
      using Z flt2goodTocks by (cases z, auto)
    
    then have "prirelRef p ([[Event x1]\<^sub>E] @ flt2ttobs(aa &\<^sub>\<F>\<^sub>\<L> \<langle>x\<rangle>\<^sub>\<F>\<^sub>\<L>)) ([[Event x1]\<^sub>E] @ flt2ttobs(zz &\<^sub>\<F>\<^sub>\<L> \<langle>y\<rangle>\<^sub>\<F>\<^sub>\<L>)) s P"
      using p1 by auto
    then have "prirelRef p (flt2ttobs (aa &\<^sub>\<F>\<^sub>\<L> \<langle>x\<rangle>\<^sub>\<F>\<^sub>\<L>)) (flt2ttobs (zz &\<^sub>\<F>\<^sub>\<L> \<langle>y\<rangle>\<^sub>\<F>\<^sub>\<L>)) (s@[[Event x1]\<^sub>E]) P"
      by auto

    then have "prirel p \<langle>x\<rangle>\<^sub>\<F>\<^sub>\<L> \<langle>y\<rangle>\<^sub>\<F>\<^sub>\<L>"
      using 4 
      by (metis Finite_Linear_Model.last.simps(2) flt2goodTock_cons_imp_prefix flt2goodTocks(2) flt2goodTocks(4))

    then show ?thesis by auto
  next
    case Tock
    then have "Aa \<noteq> \<bullet>"
      using "4.prems"(4) A by auto
    then have p1:"prirelRef p ([[{x. x \<notin>\<^sub>\<F>\<^sub>\<L> Aa}]\<^sub>R,[Tock]\<^sub>E] @ flt2ttobs(aa &\<^sub>\<F>\<^sub>\<L> \<langle>x\<rangle>\<^sub>\<F>\<^sub>\<L>)) (flt2ttobs (\<langle>(Zz,z)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>) @ flt2ttobs(zz &\<^sub>\<F>\<^sub>\<L> \<langle>y\<rangle>\<^sub>\<F>\<^sub>\<L>)) s P"
      using pp A Tock by (cases Aa, auto)
    then have "flt2ttobs (\<langle>(Zz,z)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>) = [[{x. x \<notin>\<^sub>\<F>\<^sub>\<L> Zz}]\<^sub>R,[Tock]\<^sub>E]"
      using Z flt2goodTocks by (cases z, auto)
    
    then have "prirelRef p ([[{x. x \<notin>\<^sub>\<F>\<^sub>\<L> Aa}]\<^sub>R,[Tock]\<^sub>E] @ flt2ttobs(aa &\<^sub>\<F>\<^sub>\<L> \<langle>x\<rangle>\<^sub>\<F>\<^sub>\<L>)) ([[{x. x \<notin>\<^sub>\<F>\<^sub>\<L> Zz}]\<^sub>R,[Tock]\<^sub>E] @ flt2ttobs(zz &\<^sub>\<F>\<^sub>\<L> \<langle>y\<rangle>\<^sub>\<F>\<^sub>\<L>)) s P"
      using p1 by auto
    then have "prirelRef p (flt2ttobs (aa &\<^sub>\<F>\<^sub>\<L> \<langle>x\<rangle>\<^sub>\<F>\<^sub>\<L>)) (flt2ttobs (zz &\<^sub>\<F>\<^sub>\<L> \<langle>y\<rangle>\<^sub>\<F>\<^sub>\<L>)) (s@[[{x. x \<notin>\<^sub>\<F>\<^sub>\<L> Zz}]\<^sub>R,[Tock]\<^sub>E]) P"
      by auto

    then have "prirel p \<langle>x\<rangle>\<^sub>\<F>\<^sub>\<L> \<langle>y\<rangle>\<^sub>\<F>\<^sub>\<L>"
      using 4 
      by (metis Finite_Linear_Model.last.simps(2) flt2goodTock_cons_imp_prefix flt2goodTocks(2) flt2goodTocks(4))

    then show ?thesis by auto
  next
    case Tick
    then have p1:"prirelRef p ([[Tick]\<^sub>E] @ flt2ttobs(aa &\<^sub>\<F>\<^sub>\<L> \<langle>x\<rangle>\<^sub>\<F>\<^sub>\<L>)) (flt2ttobs (\<langle>(Zz,z)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>) @ flt2ttobs(zz &\<^sub>\<F>\<^sub>\<L> \<langle>y\<rangle>\<^sub>\<F>\<^sub>\<L>)) s P"
      using pp A by auto
    then have "flt2ttobs (\<langle>(Zz,z)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>) = [[Tick]\<^sub>E]"
      using Z flt2goodTocks by (cases z, auto)
    
    then have "prirelRef p ([[Tick]\<^sub>E] @ flt2ttobs(aa &\<^sub>\<F>\<^sub>\<L> \<langle>x\<rangle>\<^sub>\<F>\<^sub>\<L>)) ([[Tick]\<^sub>E] @ flt2ttobs(zz &\<^sub>\<F>\<^sub>\<L> \<langle>y\<rangle>\<^sub>\<F>\<^sub>\<L>)) s P"
      using p1 by auto
    then have "prirelRef p (flt2ttobs (aa &\<^sub>\<F>\<^sub>\<L> \<langle>x\<rangle>\<^sub>\<F>\<^sub>\<L>)) (flt2ttobs (zz &\<^sub>\<F>\<^sub>\<L> \<langle>y\<rangle>\<^sub>\<F>\<^sub>\<L>)) (s@[[Tick]\<^sub>E]) P"
      by auto

    then have "prirel p \<langle>x\<rangle>\<^sub>\<F>\<^sub>\<L> \<langle>y\<rangle>\<^sub>\<F>\<^sub>\<L>"
      using 4 
      by (metis Finite_Linear_Model.last.simps(2) flt2goodTock_cons_imp_prefix flt2goodTocks(2) flt2goodTocks(4))

    then show ?thesis by auto
  qed
qed    

lemma flt2goodS_imp_flt2goodTock [simp]:
  assumes "flt2goodS p xs"
  shows "flt2goodTock xs"
  using assms by (induct xs rule:flt2goodS.induct, auto)

(*
lemma
  assumes "prirelRef p (flt2ttobs xs) (flt2ttobs ys) s P" "flt2goodS ys" "length xs = length ys"
  shows "flt2goodS xs"
  nitpick*)

(* So we want... *)
lemma
  assumes "prirelRef p ar zr [] P" 
          "zr \<in> P" 
    shows "\<exists>Z fl\<^sub>0 fl. prirel p fl Z \<and> Z \<in> fl\<^sub>0 \<and> fl2tt fl\<^sub>0 \<subseteq> P \<and> flt2ttobs Z \<in> P \<and> flt2ttobs fl = ar"
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
  assumes "prirelRef p (flt2ttobs fl) (flt2ttobs zr) [] P" "prirel p fl zr"
          "(flt2ttobs zr) \<in> P" 
    shows "\<exists>fl\<^sub>0. prirel p fl zr \<and> zr \<in> fl\<^sub>0 \<and> fl2tt fl\<^sub>0 \<subseteq> P \<and> (flt2ttobs zr) \<in> P"
  using assms apply auto oops

lemma prirelRef_is_TT3_trace_closed:
  assumes "prirelRef p xs ys s P" "TT3_trace ys"
  shows "TT3_trace xs"
  using assms apply(induct p xs ys s P rule:prirelRef.induct, auto)
  using TT3_trace_cons_imp_cons by (metis TT3_trace.simps(2) TT3_trace.simps(4) neq_Nil_conv)+

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
   apply (metis acceptance_event ttevent.distinct(3))
  apply (case_tac A, safe)
     apply (cases aE)
      apply auto[2]
     apply (metis acceptance_event assms(1) ttevent.distinct(3))
  apply (metis acceptance_event acceptance_set amember.simps(1) assms(1) ttevent.distinct(3) flt2goodAcceptance.simps(2) fltrace_concat2.simps(2) fltrace_concat2.simps(3) some_higher_not_maximal)
   apply (case_tac b, safe) 
  apply auto[3]
     apply (metis acceptance_event ttevent.distinct(3))
  apply (metis acceptance_event ttevent.distinct(3))
  apply (metis acceptance_event ttevent.distinct(3))
  apply (case_tac b, safe) 
    apply (cases aE, auto)
  apply (metis acceptance_event acceptance_set ttevent.distinct(3) flt2goodAcceptance.simps(2))
    apply (metis (no_types, hide_lams) acceptance_event amember.simps(2) ttevent.distinct(3) flt2goodAcceptance.elims(2) flt2goodAcceptance.simps(2) fltrace.distinct(1) fltrace.inject(2) some_higher_not_maximal)
    apply (metis (no_types, hide_lams) acceptance_event acceptance_set flt2goodAcceptance.simps(2))
    by (metis acceptance_event acceptance_set ttevent.distinct(5) flt2goodAcceptance.simps(2))

lemma flt2goodTock_of_consFL_also_flt2goodTock:
  assumes "flt2goodTock xs" "flt2goodTock ys"
  shows "flt2goodTock (xs &\<^sub>\<F>\<^sub>\<L> ys)"
  using assms apply(induct xs, auto)
  apply (case_tac x, auto)
  by (induct ys, auto)

lemma pp20:
  assumes "prirelRef p xs ys s P" "TT3_trace ys" "ttWF ys" "(flt2ttobs zr) = ys" 
          "flt2goodTock zr"
          "flt2goodAcceptance zr p"
          "TTickAll P"
        (*  "maximal(p,Tick)"*) (* FIXME: probably not needed *)
  shows "\<exists>fl. prirel p fl zr \<and> (flt2ttobs fl) = xs \<and> flt2goodTock fl"
  using assms 
proof (induct p xs ys s P arbitrary:zr rule:prirelRef.induct, auto simp add:TT3_trace_cons_imp_cons)
  fix pa::"'a ttevent partialorder"
  fix zra::"'a ttevent fltrace"
  assume assm1:"flt2ttobs zra = []"
  assume assm2:"flt2goodTock zra"
  from assm1 assm2 have "zra = \<langle>\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>"
    by (metis flt2ttobs.simps(1) flt2ttobs_consFL_eq_Nil_imp_not_flt2goodTock list.simps(3))
  then show "\<exists>fl. prirel pa fl zra \<and> flt2ttobs fl = [] \<and> flt2goodTock fl"
    using assm1 assm2 prirel.simps(1) prirelacc.simps(1) by blast
next
  fix pa::"'a ttevent partialorder"
  fix S
  fix zra::"'a ttevent fltrace"
  assume assm1:"flt2ttobs zra = [[S]\<^sub>R]"
  assume assm2:"flt2goodTock zra"
  from assm1 assm2 have "zra = \<langle>[{x. x \<notin> S}]\<^sub>\<F>\<^sub>\<L>\<rangle>\<^sub>\<F>\<^sub>\<L>"
    apply (cases zra, auto)
     apply (case_tac x1, auto)
    apply (case_tac x21, auto, case_tac b, auto, case_tac a, auto)
    by (case_tac b, auto)
  then show "\<exists>fl. prirel pa fl zra \<and> flt2ttobs fl = [[prirelref pa S]\<^sub>R] \<and> flt2goodTock fl"
    apply (intro exI[where x="\<langle>[{x. x \<notin> (prirelref pa S)}]\<^sub>\<F>\<^sub>\<L>\<rangle>\<^sub>\<F>\<^sub>\<L>"])
    unfolding prirelref_def by auto 
next
  fix pa::"'a ttevent partialorder"
  fix aa S zz sa Q
  fix zra::"'a ttevent fltrace"
  assume hyp:"(\<And>zr. flt2ttobs zr = zz \<Longrightarrow> flt2goodTock zr \<Longrightarrow> flt2goodAcceptance zr pa \<Longrightarrow> \<exists>fl. prirel pa fl zr \<and> flt2ttobs fl = aa \<and> flt2goodTock fl)"
  assume assm1:"prirelRef pa aa zz (sa @ [[S]\<^sub>R, [Tock]\<^sub>E]) Q"
  assume assm2:"ttWF zz"
  assume assm3:"flt2goodTock zra"
  assume assm4:"Tock \<notin> S"
  assume assm5:"Tock \<notin> prirelref pa S"
  assume assm6:"TT3_trace zz"
  assume assm7:"flt2ttobs zra = [S]\<^sub>R # [Tock]\<^sub>E # zz"
  then have tocks:"Tock \<in>\<^sub>\<F>\<^sub>\<L> [{x. x \<notin> prirelref pa S}]\<^sub>\<F>\<^sub>\<L>"
                  "Tock \<in>\<^sub>\<F>\<^sub>\<L> [{x. x \<notin> S}]\<^sub>\<F>\<^sub>\<L>"
    using assm4 assm5
    apply (metis amember.simps(2) mem_Collect_eq)
    by (simp_all add: assm4)
  assume assm8:"flt2goodAcceptance zra pa"
  have "flt2ttobs(\<langle>([{x. x \<notin> S}]\<^sub>\<F>\<^sub>\<L>,Tock)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>) = [S]\<^sub>R # [Tock]\<^sub>E # Nil"
    using tocks by auto
  then obtain tt where tt:"flt2ttobs tt = zz \<and> flt2goodTock tt \<and> flt2goodAcceptance tt pa \<and> zra = \<langle>([{x. x \<notin> S}]\<^sub>\<F>\<^sub>\<L>,Tock)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L> &\<^sub>\<F>\<^sub>\<L> tt"
    using assm7 tocks assm3 assm4 assm8 apply (induct zra, auto)
     apply (metis list.inject neq_Nil_conv)
    apply (case_tac x1a, auto, case_tac b, auto, case_tac a, auto)
     apply metis
    by (case_tac b, auto)
  then obtain flaa where flaa:"prirel pa flaa tt \<and> flt2ttobs flaa = aa \<and> flt2goodTock flaa"
    using hyp assm8 by blast
    
  show "\<exists>fl. prirel pa fl zra \<and> flt2ttobs fl = [prirelref pa S]\<^sub>R # [Tock]\<^sub>E # aa \<and> flt2goodTock fl"
  proof -
    have "prirelRef pa ([prirelref pa S]\<^sub>R # [Tock]\<^sub>E # aa) 
                        ([S]\<^sub>R # [Tock]\<^sub>E # zz) sa Q"
      by (simp add: assm1 assm5)

    obtain fla where fla:"fla = \<langle>([{x. x \<notin> prirelref pa S}]\<^sub>\<F>\<^sub>\<L>,Tock)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>" by auto

    have "flt2goodTock fla"
      using fla tocks(1) by auto
    then have "flt2goodTock (fla &\<^sub>\<F>\<^sub>\<L> flaa)"
      using flt2goodTock_of_consFL_also_flt2goodTock flaa by blast
    have "prirel pa fla \<langle>([{x. x \<notin> S}]\<^sub>\<F>\<^sub>\<L>,Tock)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>"
      using tocks fla unfolding prirelref_def by auto
    have flt2ttobs_fla_flaa:"flt2ttobs(fla &\<^sub>\<F>\<^sub>\<L> flaa) = [prirelref pa S]\<^sub>R # [Tock]\<^sub>E # aa"
      using tocks fla flaa by auto
    have "prirel pa (fla &\<^sub>\<F>\<^sub>\<L> flaa) zra"
      using tocks fla flaa apply auto
      by (metis FL_concat_equiv \<open>prirel pa fla \<langle>([{x. x \<notin> S}]\<^sub>\<F>\<^sub>\<L>,Tock)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>\<close> local.tt prirel_extend_both_prefix_imp)
    then show ?thesis using flt2ttobs_fla_flaa
      using \<open>flt2goodTock (fla &\<^sub>\<F>\<^sub>\<L> flaa)\<close> by blast
  qed
next
  fix pa::"'a ttevent partialorder"
  fix aa e\<^sub>2 zz sa Q zra
  assume hyp:"(\<And>zr. ttWF zz \<Longrightarrow>
              flt2ttobs zr = zz \<Longrightarrow> flt2goodTock zr \<Longrightarrow> flt2goodAcceptance zr pa \<Longrightarrow> \<exists>fl. prirel pa fl zr \<and> flt2ttobs fl = aa \<and> flt2goodTock fl)"
  assume assm1:"TT3_trace ([e\<^sub>2]\<^sub>E # zz)"
  assume assm2:"ttWF ([e\<^sub>2]\<^sub>E # zz)"
  then have no_Tock:"e\<^sub>2 \<noteq> Tock"
    using ttWF.simps(6) by blast
  have zz_is_ttWF:"ttWF zz"
    using assm2
    by (metis ttWF.simps(1) ttWF.simps(4) ttWF.simps(8) ttevent.exhaust neq_Nil_conv no_Tock)
  assume assm3:"flt2ttobs zra = [e\<^sub>2]\<^sub>E # zz"
  assume assm4:"flt2goodTock zra"
  assume assm5:"prirelRef pa aa zz (sa @ [[e\<^sub>2]\<^sub>E]) Q"
  assume assm6:"maximal(pa,e\<^sub>2)"
  assume assm7:"flt2goodAcceptance zra pa"
  from assm3 obtain tt aE where tt:"flt2ttobs tt = zz \<and> flt2goodTock tt \<and> flt2goodAcceptance tt pa \<and> zra = \<langle>(aE,e\<^sub>2)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L> &\<^sub>\<F>\<^sub>\<L> tt \<and> (e\<^sub>2 \<in>\<^sub>\<F>\<^sub>\<L> aE \<or> aE = \<bullet>)"
    using assm3 assm4 assm7 no_Tock apply (induct zra, auto)
     apply (case_tac x, auto)
    apply (case_tac x1a, auto)
    apply (case_tac a, auto, case_tac b)
    apply (metis acceptance_event acceptance_set amember.simps(2) ttevent.distinct(1) ttevent.distinct(3) ttobs.inject(1) list.inject some_higher_not_maximal)
    
      apply auto[1]

  apply (metis acceptance_event acceptance_set amember.simps(2) ttevent.distinct(5) ttobs.inject(1) list.inject)
  apply (case_tac b)  
    apply (metis acceptance_event ttobs.inject(1) list.inject)
  by auto
  then obtain fl where fl:"prirel pa fl tt \<and> flt2ttobs fl = aa \<and> flt2goodTock fl"
    using assm2 assm4 hyp zz_is_ttWF
    by blast
  show "\<exists>fl. prirel pa fl zra \<and> flt2ttobs fl = [e\<^sub>2]\<^sub>E # aa \<and> flt2goodTock fl"
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
  fix pa::"'a ttevent partialorder"
  fix aa e\<^sub>2 zz sa Q zra Z
  assume hyp:"(\<And>zr. ttWF zz \<Longrightarrow> flt2ttobs zr = zz \<Longrightarrow> flt2goodTock zr \<Longrightarrow> flt2goodAcceptance zr pa \<Longrightarrow> \<exists>fl. prirel pa fl zr \<and> flt2ttobs fl = aa \<and> flt2goodTock fl)"
  assume assm1:"TT3_trace ([e\<^sub>2]\<^sub>E # zz)"
  assume assm2:"ttWF ([e\<^sub>2]\<^sub>E # zz)"
  then have no_Tock:"e\<^sub>2 \<noteq> Tock"
    using ttWF.simps(6) by blast
  have zz_is_ttWF:"ttWF zz"
    using assm2
    by (metis ttWF.simps(1) ttWF.simps(4) ttWF.simps(8) ttevent.exhaust neq_Nil_conv no_Tock)
  assume assm3:"flt2ttobs zra = [e\<^sub>2]\<^sub>E # zz"
  assume assm4:"flt2goodTock zra"
  assume assm5:"prirelRef pa aa zz (sa @ [[e\<^sub>2]\<^sub>E]) Q"
  assume assm6:"sa @ [[Z]\<^sub>R] \<in> Q"
  assume assm7:"\<forall>b. b \<in> Z \<or> \<not> e\<^sub>2 <\<^sup>*pa b"
  assume assm8:"e\<^sub>2 \<notin> Z"
  assume assm9:"flt2goodAcceptance zra pa"
  assume assm10:"TTickAll Q"
  (*assume assm10:"maximal(pa,Tick)"*) (* FIXME: Not needed, I think *)
  from assm3 obtain tt aE where tt:"flt2ttobs tt = zz \<and> flt2goodTock tt 
    \<and> flt2goodAcceptance tt pa \<and> zra = \<langle>(aE,e\<^sub>2)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L> &\<^sub>\<F>\<^sub>\<L> tt 
    \<and> (e\<^sub>2 \<in>\<^sub>\<F>\<^sub>\<L> aE \<or> aE = \<bullet>)"
    using assm3 assm4 assm9 no_Tock apply (induct zra, auto)
    apply (case_tac x, auto)
    apply (case_tac x1a, auto)
    apply (metis acceptance_event acceptance_set ttWF.simps(6) ttobs.inject(1) list.inject zz_is_ttWF)
    by (metis acceptance_event ttobs.inject(1) list.inject)
  then obtain fl where fl:"prirel pa fl tt \<and> flt2ttobs fl = aa \<and> flt2goodTock fl"
    using assm2 assm4 hyp zz_is_ttWF
    by blast
  show "\<exists>fl. prirel pa fl zra \<and> flt2ttobs fl = [e\<^sub>2]\<^sub>E # aa \<and> flt2goodTock fl"
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
              then obtain fla where fla:"fla = \<langle>(\<bullet>,e\<^sub>2)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L> &\<^sub>\<F>\<^sub>\<L> fl"
                by auto
              then have flt2goodTock_fla:"flt2goodTock fla"
                using fla fl aE_is_bullet assm4 flt2goodTock_cons_imp_prefix flt2goodTock_of_consFL_also_flt2goodTock tt by blast
              
              have "prirel pa fla zra"
                using fla True fl tt by auto
              then have "prirel pa fla zra \<and> flt2goodTock fla"
                using flt2goodTock_fla by auto
              then show ?thesis
                using fl fla no_Tock by auto
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
        then obtain fla where fla:"fla = \<langle>(\<bullet>,e\<^sub>2)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L> &\<^sub>\<F>\<^sub>\<L> fl"
          by auto
        then have flt2goodTock_fla:"flt2goodTock fla"
          using fla fl aE_is_bullet assm4 flt2goodTock_cons_imp_prefix flt2goodTock_of_consFL_also_flt2goodTock tt by blast

        then show ?thesis
        proof (cases "maximal(pa,Tick)")
          case True
          then have "prirel pa fla zra"
            using fla Tick fl tt by auto
          then have "prirel pa fla zra \<and> flt2goodTock fla"
            using flt2goodTock_fla by auto
          then show ?thesis using fl fla no_Tock by auto
        next
          case False
          then have Tick_not_in:"Tick \<notin> Z"
            using assm8 Tick by auto
          have "Tick \<in> Z"
            using assm6 assm10 unfolding TTickAll_def 
            apply (induct sa, auto)
            using TTickTrace.simps(3) TTickTrace_dist_concat by blast
          then show ?thesis using Tick_not_in by auto
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
            obtain ff :: "'a ttevent fltrace" and aaa :: "'a ttevent acceptance" where
              f1: "flt2ttobs ff = zz \<and> flt2goodTock ff \<and> flt2goodAcceptance ff pa \<and> zra = \<langle>(aaa,e\<^sub>2)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L> &\<^sub>\<F>\<^sub>\<L> ff \<and> (e\<^sub>2 \<in>\<^sub>\<F>\<^sub>\<L> aaa \<or> aaa = \<bullet>)"
              using \<open>\<And>thesis. (\<And>tt aE. flt2ttobs tt = zz \<and> flt2goodTock tt \<and> flt2goodAcceptance tt pa \<and> zra = \<langle>(aE,e\<^sub>2)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L> &\<^sub>\<F>\<^sub>\<L> tt \<and> (e\<^sub>2 \<in>\<^sub>\<F>\<^sub>\<L> aE \<or> aE = \<bullet>) \<Longrightarrow> thesis) \<Longrightarrow> thesis\<close> by blast
            then obtain ffa :: "'a ttevent fltrace \<Rightarrow> 'a ttevent fltrace" where
              f2: "prirel pa (ffa ff) ff \<and> flt2ttobs (ffa ff) = aa \<and> flt2goodTock (ffa ff)"
              by (metis (full_types) hyp zz_is_ttWF)
            then have "flt2ttobs ((\<bullet>,e\<^sub>2)\<^sub>\<F>\<^sub>\<L> #\<^sub>\<F>\<^sub>\<L> ffa ff) = [e\<^sub>2]\<^sub>E # aa"
              by (simp add: no_Tock)
            then show ?thesis
              using f2 f1 by (metis (no_types) FL_concat_equiv True acceptance_event acceptance_set flt2goodTock.simps(2) no_Tock prirel.simps(4) prirelacc.simps(1))
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
                  by (metis Event False acceptance_event ttevent.distinct(3))
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
                then have Tick_not_in:"Tick \<notin> Z"
                    using assm8 Tick by auto
                have "Tick \<in> Z"
                    using assm6 assm10 unfolding TTickAll_def 
                    apply (induct sa, auto)
                    using TTickTrace.simps(3) TTickTrace_dist_concat by blast
               then show ?thesis using Tick_not_in by auto
           qed
        qed 
      qed
    qed
  qed

(*proof (induct p xs ys s P rule:prirelRef.induct, auto)
  fix pa::"'a ttevent partialorder"
  fix Q::"'a ttobs list set"
  assume assm1:"TT0 Q"
  assume assm2:"TT1 Q"
  show "\<exists>fl\<^sub>0 fl zr. prirel pa fl zr \<and> flt2ttobs fl = [] \<and> flt2ttobs zr = [] \<and> zr \<in> fl\<^sub>0 \<and> FLTick0 Tick fl\<^sub>0 \<and> FL1 fl\<^sub>0 \<and> fl2tt fl\<^sub>0 \<subseteq> Q"
    apply (rule exI[where x="{\<langle>\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>}"], auto)
    unfolding FLTick0_def apply auto
    unfolding FL1_def fl2tt_def apply auto
    apply (rule exI[where x="\<langle>\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>"], auto)
     apply (metis bullet_left_zero2 dual_order.antisym x_le_x_concat2)
    using assm1 assm2
    using TT0_TT1_empty by blast
next
  fix pa::"'a ttevent partialorder"
  fix S::"'a ttevent set"
  fix Q::"'a ttobs list set"
  assume assm1:"TT0 Q"
  assume assm2:"TT1 Q"
  assume assm3:"Tick \<in> S"
  then have "Tick \<in> prirelref pa S"
    unfolding prirelref_def by auto
  have pp:"prirel pa \<langle>[{fl. fl \<notin> prirelref pa S}]\<^sub>\<F>\<^sub>\<L>\<rangle>\<^sub>\<F>\<^sub>\<L> \<langle>[{zr. zr \<notin> S}]\<^sub>\<F>\<^sub>\<L>\<rangle>\<^sub>\<F>\<^sub>\<L>"
    unfolding prirelref_def by simp
  show "\<exists>fl\<^sub>0 fl zr. prirel pa fl zr \<and> flt2ttobs fl = [[prirelref pa S]\<^sub>R] \<and> flt2ttobs zr = [[S]\<^sub>R] 
    \<and> zr \<in> fl\<^sub>0 \<and> FLTick0 Tick fl\<^sub>0 \<and> FL1 fl\<^sub>0 \<and> fl2tt fl\<^sub>0 \<subseteq> Q"
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
  fix pa::"'a ttevent partialorder"
  fix S sa Q fl zr
  assume assm1:"prirelRef pa (flt2ttobs fl) (flt2ttobs zr) (sa @ [[S]\<^sub>R, [Tock]\<^sub>E]) Q"
  assume assm2:"prirel pa fl zr"
  assume assm3:"Tock \<notin> prirelref pa S"
  assume assm4:"Tock \<notin> S"
  show "\<exists>fla zra. prirel pa fla zra 
          \<and> flt2ttobs fla = [prirelref pa S]\<^sub>R # [Tock]\<^sub>E # flt2ttobs fl 
          \<and> flt2ttobs zra = [S]\<^sub>R # [Tock]\<^sub>E # flt2ttobs zr"
  proof -
    have "prirelRef pa ([prirelref pa S]\<^sub>R # [Tock]\<^sub>E # (flt2ttobs fl)) 
                       ([S]\<^sub>R # [Tock]\<^sub>E # (flt2ttobs zr)) sa Q"
      by (simp add: assm1 assm3)
    have tocks:"Tock \<in>\<^sub>\<F>\<^sub>\<L> [{x. x \<notin> prirelref pa S}]\<^sub>\<F>\<^sub>\<L>"
               "Tock \<in>\<^sub>\<F>\<^sub>\<L> [{x. x \<notin> S}]\<^sub>\<F>\<^sub>\<L>"
      apply (metis TT3_trace.simps(3) flt2ttobs_is_TT3_trace \<open>prirelRef pa ([prirelref pa S]\<^sub>R # [Tock]\<^sub>E # flt2ttobs fl) ([S]\<^sub>R # [Tock]\<^sub>E # flt2ttobs zr) sa Q\<close> amember.simps(2) mem_Collect_eq xp)
      by (simp_all add:  assm4)

    obtain fla where fla:"fla = \<langle>([{x. x \<notin> prirelref pa S}]\<^sub>\<F>\<^sub>\<L>,Tock)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>" by auto
    obtain zra where zra:"zra = \<langle>([{x. x \<notin> S}]\<^sub>\<F>\<^sub>\<L>,Tock)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>" by auto

    have "flt2ttobs(fla) = [prirelref pa S]\<^sub>R # [Tock]\<^sub>E # Nil"
      using tocks fla by auto
    have "flt2ttobs(zra) = [S]\<^sub>R # [Tock]\<^sub>E # Nil"
      using tocks zra by auto
    have "flt2ttobs(fla &\<^sub>\<F>\<^sub>\<L> fl) = [prirelref pa S]\<^sub>R # [Tock]\<^sub>E # flt2ttobs fl"
      using tocks fla by auto
    have "flt2ttobs(zra &\<^sub>\<F>\<^sub>\<L> zr) = [S]\<^sub>R # [Tock]\<^sub>E # flt2ttobs zr"
      using tocks zra by auto

    have "prirel pa fla zra"
      using tocks fla zra unfolding prirelref_def by auto
    then have "prirel pa (fla &\<^sub>\<F>\<^sub>\<L> fl) (zra &\<^sub>\<F>\<^sub>\<L> zr)"
      using assm2 by (simp add: prirel_extend_both_prefix_imp)

    then have "prirel pa (fla &\<^sub>\<F>\<^sub>\<L> fl) (zra &\<^sub>\<F>\<^sub>\<L> zr) 
                \<and> flt2ttobs(fla &\<^sub>\<F>\<^sub>\<L> fl) = [prirelref pa S]\<^sub>R # [Tock]\<^sub>E # flt2ttobs fl 
                \<and> flt2ttobs(zra &\<^sub>\<F>\<^sub>\<L> zr) = [S]\<^sub>R # [Tock]\<^sub>E # flt2ttobs zr"
      using \<open>flt2ttobs (fla &\<^sub>\<F>\<^sub>\<L> fl) = [prirelref pa S]\<^sub>R # [Tock]\<^sub>E # flt2ttobs fl\<close> \<open>flt2ttobs (zra &\<^sub>\<F>\<^sub>\<L> zr) = [S]\<^sub>R # [Tock]\<^sub>E # flt2ttobs zr\<close> by blast
    then show ?thesis by blast
  qed
next
  fix pa::"'a ttevent partialorder"
  fix aa e\<^sub>2 zz sa Q
  assume assm0:"(ttWF zz \<Longrightarrow> \<exists>fl zr. prirel pa fl zr \<and> flt2ttobs fl = aa \<and> flt2ttobs zr = zz)"
  assume assm1:"prirelRef pa aa zz (sa @ [[e\<^sub>2]\<^sub>E]) Q"
  assume assm2:"maximal(pa,e\<^sub>2)"
  assume assm4:"TT3_trace ([e\<^sub>2]\<^sub>E # zz)"
  assume assm5:"ttWF ([e\<^sub>2]\<^sub>E # zz)"
  from assm5 have "ttWF zz"
    using ttWF.elims(2) ttWF.simps(1) by blast
  then have hyp:"\<exists>fl zr. prirel pa fl zr \<and> flt2ttobs fl = aa \<and> flt2ttobs zr = zz"
    using assm0 assm4 TT3_trace_cons_imp_cons by auto
  from assm5 have e2_not_Tock:"e\<^sub>2 \<noteq> Tock"
    by auto
  
  show "\<exists>fl zr. prirel pa fl zr \<and> flt2ttobs fl = [e\<^sub>2]\<^sub>E # aa \<and> flt2ttobs zr = [e\<^sub>2]\<^sub>E # zz"
  proof -
    from assm1 assm2 have "prirelRef pa ([e\<^sub>2]\<^sub>E # aa) ([e\<^sub>2]\<^sub>E # zz) sa Q"
      by simp

    obtain fla where fla:"fla = \<langle>(\<bullet>,e\<^sub>2)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>" by auto
    then have "flt2ttobs fla = [e\<^sub>2]\<^sub>E # Nil"
      using e2_not_Tock by auto
    from hyp have "\<exists>fl zr. prirel pa fl zr 
            \<and> ((flt2ttobs fla) @ (flt2ttobs fl)) = [e\<^sub>2]\<^sub>E # aa 
            \<and> ((flt2ttobs fla) @ (flt2ttobs zr)) = [e\<^sub>2]\<^sub>E # zz"
      by (simp add: \<open>flt2ttobs fla = [[e\<^sub>2]\<^sub>E]\<close>)
    then have "\<exists>fl zr. prirel pa (\<langle>(\<bullet>,e\<^sub>2)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L> &\<^sub>\<F>\<^sub>\<L> fl) (\<langle>(\<bullet>,e\<^sub>2)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L> &\<^sub>\<F>\<^sub>\<L> zr)
            \<and> ((flt2ttobs fla) @ (flt2ttobs fl)) = [e\<^sub>2]\<^sub>E # aa 
            \<and> ((flt2ttobs fla) @ (flt2ttobs zr)) = [e\<^sub>2]\<^sub>E # zz"
      using assm2 by auto
    then have "\<exists>fl zr. prirel pa (\<langle>(\<bullet>,e\<^sub>2)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L> &\<^sub>\<F>\<^sub>\<L> fl) (\<langle>(\<bullet>,e\<^sub>2)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L> &\<^sub>\<F>\<^sub>\<L> zr)
            \<and> flt2ttobs (fla &\<^sub>\<F>\<^sub>\<L> fl) = [e\<^sub>2]\<^sub>E # aa 
            \<and> flt2ttobs (fla &\<^sub>\<F>\<^sub>\<L> zr) = [e\<^sub>2]\<^sub>E # zz"
      using e2_not_Tock fla by auto
    then show ?thesis
      using fla by blast
  qed
next
  fix pa::"'a ttevent partialorder"
  fix aa e\<^sub>2 zz sa Q Z
  assume assm0:"(ttWF zz \<Longrightarrow> \<exists>fl zr. prirel pa fl zr \<and> flt2ttobs fl = aa \<and> flt2ttobs zr = zz)"

  assume assm2:"TT3_trace ([e\<^sub>2]\<^sub>E # zz)"
  assume assm3:"ttWF ([e\<^sub>2]\<^sub>E # zz)"
  assume assm4:"prirelRef pa aa zz (sa @ [[e\<^sub>2]\<^sub>E]) Q"
  assume assm5:"sa @ [[Z]\<^sub>R] \<in> Q"
  assume assm6:"\<forall>b. b \<in> Z \<or> \<not> e\<^sub>2 <\<^sup>*pa b"
  from  assm2 have TT3_traces:
      "TT3_trace zz"
    using TT3_trace_cons_imp_cons by blast
  from assm3 have "ttWF zz"
    using ttWF.elims(2) ttWF.simps(1) by blast
  
  then have hyp:"\<exists>fl zr. prirel pa fl zr \<and> flt2ttobs fl = aa \<and> flt2ttobs zr = zz"
    using TT3_traces assm0 by auto

  from assm3 have e2_not_Tock:"e\<^sub>2 \<noteq> Tock"
    by auto

  show "\<exists>fl zr. prirel pa fl zr \<and> flt2ttobs fl = [e\<^sub>2]\<^sub>E # aa \<and> flt2ttobs zr = [e\<^sub>2]\<^sub>E # zz"
  proof -
    from assm4 assm5 assm6 have "prirelRef pa ([e\<^sub>2]\<^sub>E # aa) ([e\<^sub>2]\<^sub>E # zz) sa Q"
      by auto
    obtain fla where fla:"fla = \<langle>([{e\<^sub>2}]\<^sub>\<F>\<^sub>\<L>,e\<^sub>2)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>" by auto
    then have "flt2ttobs fla = [e\<^sub>2]\<^sub>E # Nil"
      using e2_not_Tock by auto
    from hyp have "\<exists>fl zr. prirel pa fl zr 
            \<and> ((flt2ttobs fla) @ (flt2ttobs fl)) = [e\<^sub>2]\<^sub>E # aa 
            \<and> ((flt2ttobs fla) @ (flt2ttobs zr)) = [e\<^sub>2]\<^sub>E # zz"
      by (simp add: \<open>flt2ttobs fla = [[e\<^sub>2]\<^sub>E]\<close>)
    then have "\<exists>fl zr. prirel pa (\<langle>([{e\<^sub>2}]\<^sub>\<F>\<^sub>\<L>,e\<^sub>2)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L> &\<^sub>\<F>\<^sub>\<L> fl) (\<langle>([{e\<^sub>2}]\<^sub>\<F>\<^sub>\<L>,e\<^sub>2)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L> &\<^sub>\<F>\<^sub>\<L> zr)
            \<and> ((flt2ttobs fla) @ (flt2ttobs fl)) = [e\<^sub>2]\<^sub>E # aa 
            \<and> ((flt2ttobs fla) @ (flt2ttobs zr)) = [e\<^sub>2]\<^sub>E # zz"
      using assm4 assm5 assm6 
      by auto
    then have "\<exists>fl zr. prirel pa (\<langle>([{e\<^sub>2}]\<^sub>\<F>\<^sub>\<L>,e\<^sub>2)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L> &\<^sub>\<F>\<^sub>\<L> fl) (\<langle>([{e\<^sub>2}]\<^sub>\<F>\<^sub>\<L>,e\<^sub>2)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L> &\<^sub>\<F>\<^sub>\<L> zr)
            \<and> flt2ttobs (fla &\<^sub>\<F>\<^sub>\<L> fl) = [e\<^sub>2]\<^sub>E # aa 
            \<and> flt2ttobs (fla &\<^sub>\<F>\<^sub>\<L> zr) = [e\<^sub>2]\<^sub>E # zz"
      using e2_not_Tock fla by auto
    then show ?thesis
      using fla by blast
  qed
qed*)

(*
lemma pp3:
  assumes "prirelRef p xs ys s P" "TT3_trace ys" "ttWF ys"
          "ys \<in> P" 
    shows "\<exists>Z fl\<^sub>0 fl. prirel p fl Z \<and> Z \<in> fl\<^sub>0 \<and> fl2tt fl\<^sub>0 \<subseteq> P \<and> flt2ttobs Z \<in> P \<and> flt2ttobs fl = xs"
  using pp2 
  by (smt assms(1) assms(2) assms(3) assms(4) fl2tt_def mem_Collect_eq singletonD singletonI subsetI)
*)

lemma pp4:
  assumes "prirelRef p xs ys [] P" "ys \<in> P" 
          "TT0 P" "TTwf P" "TT1w P" "TT3 P" "TTick P" "TTickAll P" "TT4w P"
    shows "\<exists>fl. flt2ttobs fl = xs \<and> (\<exists>fl\<^sub>0. FLTick0 Tick fl\<^sub>0 \<and> FL1 fl\<^sub>0 \<and> fl2tt fl\<^sub>0 \<subseteq> P \<and> (\<exists>Z. prirel p fl Z \<and> Z \<in> fl\<^sub>0)) \<and> flt2goodTock fl"
proof -
  have "ttWF ys"
    using TTwf_def assms by blast
  then obtain Z where fl:"ys = flt2ttobs Z \<and> flt2goodTock Z  \<and>
        (\<exists>fl\<^sub>0. FLTick0 Tick fl\<^sub>0 \<and> FL1 fl\<^sub>0 \<and> fl2tt fl\<^sub>0 \<subseteq> P \<and> Z \<in> fl\<^sub>0) \<and> flt2ttobs Z \<in> P \<and> flt2goodAcceptance Z p \<and> flt2goodTock Z 
        \<and> ttWF ys \<and> prirelRef p xs ys [] P"
    unfolding fl2tt_def using assms TTwf_1c_3_imp_flt2ttobs_FL1_mod by blast
  then have "\<exists>fl\<^sub>0. FLTick0 Tick fl\<^sub>0 \<and> FL1 fl\<^sub>0 \<and> fl2tt fl\<^sub>0 \<subseteq> P \<and> Z \<in> fl\<^sub>0 \<and> flt2ttobs Z \<in> P \<and> flt2ttobs Z = ys \<and> flt2goodAcceptance Z p 
        \<and> flt2goodTock Z 
        \<and> TT3_trace ys \<and> ttWF ys \<and> prirelRef p xs ys [] P"
    by auto
  then have "\<exists>fl\<^sub>0. FLTick0 Tick fl\<^sub>0 \<and> FL1 fl\<^sub>0 \<and> fl2tt fl\<^sub>0 \<subseteq> P \<and> Z \<in> fl\<^sub>0 \<and> flt2ttobs Z \<in> P \<and> flt2ttobs Z = ys \<and> flt2goodAcceptance Z p 
        \<and> flt2goodTock Z 
        \<and> TT3_trace ys \<and> ttWF ys \<and> prirelRef p xs ys [] P
        \<and> (\<exists>fl. prirel p fl Z \<and> flt2ttobs fl = xs \<and> flt2goodTock fl)"
    using pp20 assms
    by metis
  then have "\<exists>fl\<^sub>0. FLTick0 Tick fl\<^sub>0 \<and> FL1 fl\<^sub>0 \<and> fl2tt fl\<^sub>0 \<subseteq> P \<and> Z \<in> fl\<^sub>0 \<and> flt2ttobs Z \<in> P \<and> flt2goodTock Z 
        \<and> (\<exists>fl. prirel p fl Z \<and> flt2ttobs fl = xs \<and> flt2goodTock fl)"
    by blast
  then show ?thesis using fl by blast
qed

(* The key result we wish to establish is: *)
lemma fl2tt_pri_tt2fl_priNS:
  fixes P :: "('e ttobs) list set"
  assumes TT0_healthy:  "TT0 P" 
      and TTwf_healthy: "TTwf P" 
      and TT1w_healthy: "TT1w P"
      and TT3_healthy:  "TT3 P"
      and TTick_healthy: "TTick P"
      and TTickAll:   "TTickAll P"
      and TT4w_healthy:    "TT4w P"
     (* and Tick_max:"maximal(p,Tick)"*)
  shows "fl2tt(pri p (tt2fl P)) = priNS p P"
proof -
  have "fl2tt(pri p (tt2fl P)) = {flt2ttobs fl|fl. fl \<in> (pri p (tt2fl P)) \<and> flt2goodTock fl} \<union> {[]}"
    using fl2tt_FL0_FL1_flt2goodTock
    by (simp add: fl2tt_FL0_FL1_flt2goodTock TT0_healthy TT1w_healthy TickTock_FL.FL0_tt2fl FL1_tt2fl pri_FL0 pri_FL1)
  also have "... = {flt2ttobs fl|fl. fl \<in> (pri p (\<Union>{fl. FLTick0 Tick fl \<and> FL1 fl \<and> (fl2tt fl) \<subseteq> P})) \<and> flt2goodTock fl} \<union> {[]}"
    unfolding tt2fl_def by auto
  also have "... = {flt2ttobs fl|fl. fl \<in> \<Union>{pri p fl|fl. FLTick0 Tick fl \<and> FL1 fl \<and> (fl2tt fl) \<subseteq> P} \<and> flt2goodTock fl} \<union> {[]}"
  proof -
    have "pri p (\<Union>{fl. FLTick0 Tick fl \<and> FL1 fl \<and> (fl2tt fl) \<subseteq> P}) = \<Union>{pri p fl|fl. fl \<in> {fl. FLTick0 Tick fl \<and> FL1 fl \<and> (fl2tt fl) \<subseteq> P}}"
      using pri_univ_dist by (metis)
    also have "... = \<Union>{pri p fl|fl. FLTick0 Tick fl \<and> FL1 fl \<and> (fl2tt fl) \<subseteq> P}"
      by auto
    then show ?thesis
      using calculation by auto
  qed
  also have "... = {flt2ttobs fl|fl. \<exists>x. (\<exists>fl. x = pri p fl \<and> FLTick0 Tick fl \<and> FL1 fl \<and> (fl2tt fl) \<subseteq> P) \<and> fl \<in> x \<and> flt2goodTock fl} \<union> {[]}"
    unfolding fl2tt_def by auto
  also have "... = {flt2ttobs fl|fl. \<exists>fl\<^sub>0. FLTick0 Tick fl\<^sub>0 \<and> FL1 fl\<^sub>0 \<and> (fl2tt fl\<^sub>0) \<subseteq> P \<and> (\<exists>Z. prirel p fl Z \<and> Z \<in> fl\<^sub>0) \<and> flt2goodTock fl} \<union> {[]}"
    unfolding pri_def by auto
  also have "... = {ar|ar zr. prirelRef p ar zr [] P \<and> zr \<in> P}"
    using assms apply auto
    using TT0_TT1w_empty prirelRef.simps(1) apply blast
    apply (meson flt2ttobs_extn pp)
    using assms pp4 by metis 
  also have "... = priNS p P"
    unfolding priNS_def by auto
  finally show ?thesis .
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

lemma prirel_both_and_both_acceptances_imp_cons_both:
  assumes "prirel p xs ys" "prirel p \<langle>x,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L> \<langle>y,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>"
  shows "prirel p (xs &\<^sub>\<F>\<^sub>\<L> \<langle>x,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>) (ys &\<^sub>\<F>\<^sub>\<L> \<langle>y,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>)"
  using assms apply (induct p xs ys rule:prirel.induct, simp_all)
   apply (case_tac A, simp, case_tac Z, simp)
  apply auto[2]
   apply (case_tac A, simp, case_tac Z, simp)
  oops

lemma flt2ttobs_exists_flt2goodTock_for_ttWF_TT3_trace:
  assumes "ttWF fl" "TT3_trace fl"
  shows "\<exists>zr. (flt2ttobs zr) = fl \<and> flt2goodTock zr"
  using assms
proof (induct fl rule:ttWF.induct, auto)
  show "\<exists>zr. flt2ttobs zr = [] \<and> flt2goodTock zr"
    by (intro exI[where x="\<langle>\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>"], auto)
next
  fix X
  show "\<exists>zr. flt2ttobs zr = [[X]\<^sub>R] \<and> flt2goodTock zr"
    by (intro exI[where x="\<langle>[{x. x \<notin> X}]\<^sub>\<F>\<^sub>\<L>\<rangle>\<^sub>\<F>\<^sub>\<L>"], auto)
next
  show "\<exists>zr. flt2ttobs zr = [[Tick]\<^sub>E] \<and> flt2goodTock zr"
    by (intro exI[where x="\<langle>(\<bullet>,Tick)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>"], auto)
next
  fix e \<sigma>
  assume hyp:"(TT3_trace \<sigma> \<Longrightarrow> \<exists>zr. flt2ttobs zr = \<sigma> \<and> flt2goodTock zr)"
  assume assm1:"ttWF \<sigma>"
  assume assm2:"TT3_trace ([Event e]\<^sub>E # \<sigma>)"
  show "\<exists>zr. flt2ttobs zr = [Event e]\<^sub>E # \<sigma> \<and> flt2goodTock zr"
  proof -
    from assm2 have "TT3_trace \<sigma>"
      using TT3_trace_cons_imp_cons by blast
    then have "\<exists>zr. flt2ttobs zr = \<sigma> \<and> flt2goodTock zr"
      using hyp by auto
    then have "\<exists>zr. flt2ttobs(\<langle>(\<bullet>,Event e)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>) @ flt2ttobs zr = [Event e]\<^sub>E # \<sigma> \<and> flt2goodTock zr"
      by auto
    then have "\<exists>zr. flt2ttobs(\<langle>(\<bullet>,Event e)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L> &\<^sub>\<F>\<^sub>\<L> zr) = [Event e]\<^sub>E # \<sigma> \<and> flt2goodTock (\<langle>(\<bullet>,Event e)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L> &\<^sub>\<F>\<^sub>\<L> zr)"
      by auto
    then show ?thesis by blast
  qed
next
  fix X::"'a ttevent set"
  fix zr::"'a ttevent fltrace"
  assume assm1:"ttWF (flt2ttobs zr)"
  assume assm2:"Tock \<notin> X"
  assume assm4:"flt2goodTock zr"
  show "\<exists>zra. flt2ttobs zra = [X]\<^sub>R # [Tock]\<^sub>E # flt2ttobs zr \<and> flt2goodTock zra"
  proof -
    have "\<exists>zra. flt2ttobs zra = flt2ttobs zr \<and> flt2goodTock zra"
      using assm4 by auto
    then have "\<exists>zra. flt2ttobs(\<langle>([{x. x \<notin> X}]\<^sub>\<F>\<^sub>\<L>,Tock)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>) @ flt2ttobs zra = [X]\<^sub>R # [Tock]\<^sub>E # flt2ttobs zr \<and> flt2goodTock zra"
      using assm2 by auto
    then have "\<exists>zra. flt2ttobs(\<langle>([{x. x \<notin> X}]\<^sub>\<F>\<^sub>\<L>,Tock)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L> &\<^sub>\<F>\<^sub>\<L> zra) = [X]\<^sub>R # [Tock]\<^sub>E # flt2ttobs zr \<and> flt2goodTock (\<langle>([{x. x \<notin> X}]\<^sub>\<F>\<^sub>\<L>,Tock)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L> &\<^sub>\<F>\<^sub>\<L> zra)"
      using assm2 by auto
    then show ?thesis by blast
  qed
qed

lemma prirelRef_of_flt2ttobs_flt2goodTocks_is_eq_length:
  assumes "prirelRef p (flt2ttobs fl) (flt2ttobs zr) s P" "flt2goodTock fl" "flt2goodTock zr" (*"xs = (flt2ttobs fl)" "ys = (flt2ttobs zr)"*) 
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

end