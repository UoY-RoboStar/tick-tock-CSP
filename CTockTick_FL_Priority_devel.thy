theory
  CTockTick_FL_Priority_devel
imports
  CTockTick_FL_Priority
begin

lemma
  assumes "flt2cttobs(fl) = ar"
  shows "(\<exists>Z fl\<^sub>0. prirel p fl Z \<and> Z \<in> fl\<^sub>0 \<and> fl2ctt fl\<^sub>0 \<subseteq> P \<and> flt2cttobs(Z) \<in> P) 
         = 
         (\<exists>zr. prirelRef p ar zr [] P \<and> zr \<in> P)"
  using assms apply auto
  oops

lemma
  "(\<exists>Z fl. prirel p fl Z \<and> Z \<in> fl\<^sub>0 \<and> flt2cttobs(Z) \<in> P \<and> x = flt2cttobs fl)
   =
   (\<exists>Z fl. prirel p fl Z \<and> Z \<in> fl\<^sub>0 \<and> flt2cttobs(Z) \<in> P \<and> flt2goodTock fl \<and> x = flt2cttobs fl)"
  oops

lemma flt2cttobs_flt2goodTock_less_eq_exists:
  assumes "flt2cttobs fl \<noteq> []"
  shows "\<exists>fla. flt2cttobs fl = flt2cttobs fla \<and> fla \<le> fl \<and> flt2goodTock fla"
  using assms
proof (induct fl rule:flt2goodTock.induct)
  case (1 A)
  then show ?case 
    apply auto
    by (rule exI[where x="\<langle>A\<rangle>\<^sub>\<F>\<^sub>\<L>"], auto)
next
  case (2 A fl)
  then show ?case
  proof (cases "flt2cttobs fl \<noteq> []")
    case flt2cttobs_not_Nil:True
    then show ?thesis
      proof (cases "acceptance(A) \<noteq> \<bullet>")
      case True
        then have "\<exists>flaa. flt2cttobs fl = flt2cttobs flaa \<and> flaa \<le> fl \<and> flt2goodTock flaa"
          using flt2cttobs_not_Nil 2 by auto
        then show ?thesis using 2 True
          by (metis flt2cttobs.simps(2) flt2goodTock.simps(2) less_eq_fltrace.simps(3) order_refl)
      next
        case False
        then show ?thesis 
          using flt2cttobs_not_Nil 2 apply auto
          by (metis flt2cttobs.simps(2) flt2goodTock.simps(2) less_eq_fltrace.simps(3) order_refl)
      qed
  next
    case fl2cttobs_is_Nil:False
    then show ?thesis
      proof (cases "acceptance(A) \<noteq> \<bullet>")
        case True
        then show ?thesis using fl2cttobs_is_Nil 2 apply auto
          apply (rule exI[where x="\<langle>A,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>"], auto)
           apply (metis dual_order.refl dual_order.trans prefixFL_induct2)
          apply (rule exI[where x="\<langle>A,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>"], auto)
          by (metis dual_order.refl dual_order.trans prefixFL_induct2)
      next
      case False
      then show ?thesis using fl2cttobs_is_Nil 2 apply auto
        apply (rule exI[where x="\<langle>A,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>"], auto)
        by (metis dual_order.refl dual_order.trans prefixFL_induct2)
      qed
    qed
qed

lemma flt2cttobs_FL1_exists_flt2goodTock:
  assumes "flt2cttobs fl \<noteq> []" "fl \<in> P" "FL1 P"
  shows "\<exists>fla. flt2cttobs fl = flt2cttobs fla \<and> fla \<in> P \<and> flt2goodTock fla"
  using assms
  by (meson FL1_def flt2cttobs_flt2goodTock_less_eq_exists)

lemma 
  assumes "FL0 P" "FL1 P"
  shows "fl2ctt P = {flt2cttobs fl|fl. fl \<in> P \<and> flt2goodTock fl} \<union> {[]}"
  using assms unfolding fl2ctt_def apply auto
  using flt2cttobs_FL1_exists_flt2goodTock apply blast
  by (rule exI[where x="\<langle>\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>"], auto)

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

lemma prirelRef_extend_rhs_cttWF:
  assumes "prirelRef p xs ys s P" "cttWF (ys @ [[R]\<^sub>R])"
  shows "prirelRef p xs (ys @ [[R]\<^sub>R]) s P"
  using assms apply (induct p xs ys s P rule:prirelRef.induct, auto)
  by (smt Nil_is_append_conv cttWF.elims(2) cttobs.distinct(1) list.discI list.inject)+




lemma prirelRef_extend_both_refusal_cttWF:
  assumes "prirelRef p xs ys s P" "cttWF (ys @ [[S]\<^sub>R])" "prirelref p S = R"
  shows "prirelRef p (xs @ [[R]\<^sub>R]) (ys @ [[S]\<^sub>R]) s P"
  using assms  apply (induct p xs ys s P rule:prirelRef.induct)
  apply (auto)
  by (smt Nil_is_append_conv cttWF.elims(2) cttobs.distinct(1) list.discI list.inject)+

lemma
  assumes "prirelRef p [] zz s Q" "cttWF (zz @ [[S]\<^sub>R])" "cttWF s"
  shows "\<not> prirelRef p [[prirelref p S]\<^sub>R] (zz @ [[S]\<^sub>R]) s Q"
  nitpick

lemma prirelRef_extend_both_tock_refusal_cttWF:
  assumes "prirelRef p xs ys s P" "cttWF (ys @ [[S]\<^sub>R,[Tock]\<^sub>E])" "prirelref p S = R"
  shows "prirelRef p (xs @ [[R]\<^sub>R,[Tock]\<^sub>E]) (ys @ [[S]\<^sub>R,[Tock]\<^sub>E]) s P"
  using assms apply (induct p xs ys s P rule:prirelRef.induct, auto)
  by (smt Nil_is_append_conv cttWF.elims(2) cttobs.distinct(1) list.discI list.inject)+

lemma prirelRef_extend_both_events_eq_size_maximal_cttWF:
  assumes "prirelRef p xs ys s P" "cttWF (ys @ [[e\<^sub>1]\<^sub>E])" "maximal(p,e\<^sub>1)" "size xs = size ys"
  shows "prirelRef p (xs @ [[e\<^sub>1]\<^sub>E]) (ys @ [[e\<^sub>1]\<^sub>E]) s P"
  using assms apply (induct p xs ys s P rule:prirelRef.induct, auto)
  apply (smt cttWF.elims(2) cttobs.distinct(1) list.discI list.inject prirelRef.simps(1) prirelRef.simps(5))
  apply (smt Nil_is_append_conv cttWF.elims(2) cttobs.distinct(1) list.discI list.inject)
  apply (smt cttWF.elims(2) cttobs.distinct(1) list.discI list.inject prirelRef.simps(1) prirelRef.simps(4))
  by (smt Nil_is_append_conv cttWF.elims(2) cttobs.distinct(1) list.discI list.inject)+
 
lemma prirelRef_extend_both_events_maximal_cttWF:
  assumes "prirelRef p xs ys s P" "cttWF (xs @ [[e\<^sub>1]\<^sub>E])" "cttWF (ys @ [[e\<^sub>1]\<^sub>E])" "maximal(p,e\<^sub>1)"
  shows "prirelRef p (xs @ [[e\<^sub>1]\<^sub>E]) (ys @ [[e\<^sub>1]\<^sub>E]) s P"
  using assms apply (induct p xs ys s P rule:prirelRef.induct, auto)
  apply (metis cttWF.elims(2) cttWF.simps(11) cttWF.simps(12) cttWF.simps(13) list.discI)
  apply (smt cttWF.elims(2) cttobs.distinct(1) list.discI list.inject prirelRef.simps(1) prirelRef.simps(4))
  by (smt Nil_is_append_conv cttWF.elims(2) cttobs.distinct(1) list.discI list.inject)+
  
lemma prirelRef_extend_both_events_non_maximal_cttWF:
  assumes "prirelRef p xs ys s P" "cttWF (xs @ [[e\<^sub>1]\<^sub>E])" "cttWF (ys @ [[e\<^sub>1]\<^sub>E])" 
          "(\<exists>Z. s @ ys @ [[Z]\<^sub>R] \<in> P \<and> \<not>(\<exists>b. b \<notin> Z \<and> e\<^sub>1 <\<^sup>*p b))" 
  shows "prirelRef p (xs @ [[e\<^sub>1]\<^sub>E]) (ys @ [[e\<^sub>1]\<^sub>E]) s P"
  using assms apply (induct p xs ys s P rule:prirelRef.induct, auto)
  apply (metis cttWF.elims(2) cttWF.simps(11) cttWF.simps(12) cttWF.simps(13) list.discI)
  apply (smt cttWF.elims(2) cttobs.distinct(1) list.discI list.inject prirelRef.simps(1) prirelRef.simps(4))
  by (smt Nil_is_append_conv cttWF.elims(2) cttobs.distinct(1) list.discI list.inject)+
  
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
  using tt sledgehammer[debug=true]

lemma
  assumes "prirel p fl Y" "FL1 fl\<^sub>0" "FLTick0 Tick fl\<^sub>0"
          "Y \<in> fl\<^sub>0"
          "fl2ctt fl\<^sub>0 \<subseteq> P"
          "flt2cttobs Y \<in> P"
    shows "prirelRef p (flt2cttobs fl) (flt2cttobs Y) [] P"
  using assms  
proof (induct fl Y rule:ftrace_cons_induct_both_eq_length2)
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
  then have "xs = xs &\<^sub>\<F>\<^sub>\<L> \<langle>x\<rangle>\<^sub>\<F>\<^sub>\<L>" "ys = ys &\<^sub>\<F>\<^sub>\<L> \<langle>y\<rangle>\<^sub>\<F>\<^sub>\<L>"
    by (simp_all add: concat_FL_last_not_bullet_absorb)
  then show ?case using 3 by auto
next
  case (4 x y xs ys)
  then have prirelRef:"prirelRef p (flt2cttobs xs) (flt2cttobs ys) [] P"
    by (metis (mono_tags, lifting) flt2cttobs_extn mem_Collect_eq subset_eq x_le_concat2_FL1 prirel_cons_eq_length_imp_prirel_eq_prefix)
  then show ?case using 4
  proof (cases "flt2goodTock xs")
    case True
    then have "flt2goodTock ys"
      using 4 prirel_cons_eq_length_imp_prirel_eq_prefix prirel_flt2goodTock_tgt_imp_src by blast
    then have flt2_ys_y:"flt2cttobs (ys &\<^sub>\<F>\<^sub>\<L> \<langle>y\<rangle>\<^sub>\<F>\<^sub>\<L>) = flt2cttobs (ys) @ flt2cttobs(\<langle>y\<rangle>\<^sub>\<F>\<^sub>\<L>)"
      using 4 by (simp add: flt2cttobs_cons_acceptance_eq_cons)
    then have "flt2cttobs (ys) @ flt2cttobs(\<langle>y\<rangle>\<^sub>\<F>\<^sub>\<L>) \<in> P"
      using 4 by (simp)
    then show ?thesis using 4
      proof (cases x)
        case xnil:acnil
        then show ?thesis 
          proof (cases y)
            case acnil
            then show ?thesis using 4 prirelRef xnil by auto
          next
            case (acset x2)
            then obtain yR where yR:"flt2cttobs(\<langle>y\<rangle>\<^sub>\<F>\<^sub>\<L>) = [[yR]\<^sub>R]"
              by simp
            then have "cttWF (flt2cttobs (ys &\<^sub>\<F>\<^sub>\<L> \<langle>y\<rangle>\<^sub>\<F>\<^sub>\<L>))"
              by (meson "4.prems"(4) FLTick0_def assms(3) flt2cttobs_is_cttWF)
            then have "prirelRef p (flt2cttobs xs) ((flt2cttobs ys) @ [[yR]\<^sub>R]) [] P"
              using acset 4 prirelRef xnil flt2_ys_y prirelRef_extend_rhs_cttWF 
              by (metis yR)
            then show ?thesis using acset 4 xnil flt2_ys_y yR by auto
          qed
      next
        case (acset x2)
        then obtain yA where yA:"y = [yA]\<^sub>\<F>\<^sub>\<L>"
          using "4.hyps"(3) "4.hyps"(4) "4.prems"(1) prirel_last_bullets_cons_imp by blast
        then have "prirel p \<langle>[x2]\<^sub>\<F>\<^sub>\<L>\<rangle>\<^sub>\<F>\<^sub>\<L> \<langle>[yA]\<^sub>\<F>\<^sub>\<L>\<rangle>\<^sub>\<F>\<^sub>\<L>"
          using "4.hyps"(2) "4.hyps"(3) "4.hyps"(4) "4.prems"(1) acset prirel_cons_eq_length_imp_prirel_acceptances_eq by blast
        then have "prirelref p {x. x \<notin> yA} = {x. x \<notin> x2}"
          by (metis (no_types, lifting) Collect_cong acceptance.distinct(1) amember.simps(2) flt2cttobs.simps(1) prirel.simps(1) prirelacc_eq_prirelref_via_flt2cttobs)
        then obtain xR where xR:"flt2cttobs(\<langle>x\<rangle>\<^sub>\<F>\<^sub>\<L>) = [[xR]\<^sub>R]"
          by (simp add: acset)
        then obtain yR where yR:"flt2cttobs(\<langle>y\<rangle>\<^sub>\<F>\<^sub>\<L>) = [[yR]\<^sub>R] \<and> prirelref p yR = xR"
          using 4 yA
          by (metis (no_types, lifting) \<open>prirel p \<langle>[x2]\<^sub>\<F>\<^sub>\<L>\<rangle>\<^sub>\<F>\<^sub>\<L> \<langle>[yA]\<^sub>\<F>\<^sub>\<L>\<rangle>\<^sub>\<F>\<^sub>\<L>\<close> acceptance.distinct(1) acset flt2cttobs.simps(1) prirel.simps(1) prirelacc_eq_prirelref_via_flt2cttobs)

        have "cttWF (flt2cttobs (ys &\<^sub>\<F>\<^sub>\<L> \<langle>y\<rangle>\<^sub>\<F>\<^sub>\<L>))"
          by (meson "4.prems"(4) FLTick0_def assms(3) flt2cttobs_is_cttWF)
        then have "cttWF ((flt2cttobs ys) @ [[yR]\<^sub>R])"
          by (metis flt2_ys_y yR)
        then have "prirelRef p ((flt2cttobs xs) @ [[xR]\<^sub>R]) ((flt2cttobs ys) @ [[yR]\<^sub>R]) [] P"
          using prirelRef_extend_both_refusal_cttWF
          using prirelRef yR by blast
        then show ?thesis
          using "4.hyps"(3) True flt2_ys_y flt2cttobs_cons_acceptance_eq_cons xR yR by fastforce
      qed
  next
    case False
    then have flt2_xsx:"flt2cttobs (xs &\<^sub>\<F>\<^sub>\<L> \<langle>x\<rangle>\<^sub>\<F>\<^sub>\<L>) = flt2cttobs (xs)"
      by (simp add: flt2cttobs_cons_no_extend_not_flt2goodTock)
    then show ?thesis 
    proof (cases y)
      case acnil
      then show ?thesis using 4 prirelRef flt2_xsx by auto
    next
      case (acset x2)
      then obtain yR where yR:"flt2cttobs(\<langle>y\<rangle>\<^sub>\<F>\<^sub>\<L>) = [[yR]\<^sub>R]"
        by simp
      then have cttWF_ys_y:"cttWF (flt2cttobs (ys &\<^sub>\<F>\<^sub>\<L> \<langle>y\<rangle>\<^sub>\<F>\<^sub>\<L>))"
        by (meson "4.prems"(4) FLTick0_def assms(3) flt2cttobs_is_cttWF)
      then show ?thesis
      proof (cases "flt2goodTock ys")
        case True
        then have "prirelRef p (flt2cttobs xs) ((flt2cttobs ys) @ [[yR]\<^sub>R]) [] P"
          using acset 4 prirelRef flt2_xsx prirelRef_extend_rhs_cttWF
          by (metis cttWF_ys_y flt2cttobs_cons_acceptance_eq_cons yR)
        then show ?thesis
          using "4.hyps"(4) True flt2_xsx flt2cttobs_cons_acceptance_eq_cons yR by fastforce
      next
        case False
        then have "flt2cttobs (ys &\<^sub>\<F>\<^sub>\<L> \<langle>y\<rangle>\<^sub>\<F>\<^sub>\<L>) = flt2cttobs (ys)"
          by (simp add: flt2cttobs_cons_no_extend_not_flt2goodTock)
        then show ?thesis
          by (simp add: flt2_xsx prirelRef)
      qed
    qed
  qed
(*
  proof (cases "flt2goodTock ys")
    case True
    then show ?thesis using 4
    proof (cases "flt2goodTock xs")
      case True
      then obtain xA xY where xAY:"x = [xA]\<^sub>\<F>\<^sub>\<L> \<and> y = [xY]\<^sub>\<F>\<^sub>\<L>"
        sledgehammer[debug=true]
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
    *)(*
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
    sledgehammer[debug=true]*)
next
  case (5 x y xs ys)
  then have prirelRef:"prirelRef p (flt2cttobs xs) (flt2cttobs ys) [] P"
    using prirel_cons_eq_length_imp
    by (metis (mono_tags, lifting) flt2cttobs_extn mem_Collect_eq subset_eq x_le_concat2_FL1)
  then show ?case
    proof (cases "last xs\<noteq>\<bullet>")
      case True
      then have "xs = xs &\<^sub>\<F>\<^sub>\<L> \<langle>x,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>" "ys = ys &\<^sub>\<F>\<^sub>\<L> \<langle>y,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>"
        apply (simp add: concat_FL_last_not_bullet_absorb)
        by (metis "5.hyps"(2) "5.prems"(1) True concat_FL_last_not_bullet_absorb prirel_cons_eq_length_imp_prirel_acceptances_last_bullet_eq)
      then show ?thesis using 5 True by auto
    next
      case last_xs_bullet:False
      then have "prirel p \<langle>x,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L> \<langle>y,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>"
        using "5.hyps"(2) "5.prems"(1) prirel_cons_eq_length_imp_prirel_acceptances by blast
      then show ?thesis using 5 
      proof (cases "last ys\<noteq>\<bullet>")
        case True
        then have "ys = ys &\<^sub>\<F>\<^sub>\<L> \<langle>x,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>"
          by (metis True concat_FL_last_not_bullet_absorb)
        then show ?thesis using 5
          using last_xs_bullet True prirel_cons_eq_length_imp_prirel_acceptances_last_bullet_eq by blast
      next
        case False
        then show ?thesis 
           proof (cases "flt2goodTock xs")
             case True
             then have "flt2goodTock ys"
               using "5.hyps"(2) "5.prems"(1) prirel_cons_eq_length_imp prirel_flt2goodTock_tgt_imp_src by blast
             then have flt2_ys_y:"flt2cttobs (ys &\<^sub>\<F>\<^sub>\<L> \<langle>y,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>) = flt2cttobs (ys) @ flt2cttobs(\<langle>y,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>)"
               using 5 False flt2cttobs_acceptance_cons_eq_list_cons by blast
             then have "flt2cttobs (ys) @ flt2cttobs(\<langle>y,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>) \<in> P"
               using 5 by (simp)

             (* A few things to worry about here, namely that if event(y) = Tock, then if 
                acceptance(y) = \<bullet> we have that flt2cttobs(\<langle>y,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>) = []. Similar problem arises
                on the x side. *)
             then show ?thesis sorry
           next
             case False
             then show ?thesis sorry
           qed
          using 5 last_xs_bullet sorry
      qed
        sorry
      then have "prirelRef p ((flt2cttobs xs) @ (flt2cttobs \<langle>x,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>)) ((flt2cttobs ys) @ (flt2cttobs \<langle>y,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>)) [] P"
        
      then show ?thesis using 4 sorry
    qed 
qed  

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