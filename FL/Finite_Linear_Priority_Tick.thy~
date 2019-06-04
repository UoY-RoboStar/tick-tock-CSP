theory Finite_Linear_Priority_Tick

imports
  Finite_Linear_Priority
  Finite_Linear_Tick_Param
begin

lemma prirelacc_not_in_imp [simp]:
  assumes "prirelacc p A Z" "e \<notin>\<^sub>\<F>\<^sub>\<L> Z"
  shows "e \<notin>\<^sub>\<F>\<^sub>\<L> A"
  using assms by(induct p A Z rule:prirelacc.induct, auto)

lemma pri_tickWF:
  assumes "prirel p x Z" "tickWF tick Z"
  shows "tickWF tick x"
  using assms apply (induct p x Z arbitrary:tick rule:prirel.induct, auto)
  by (case_tac aa, auto, case_tac x1, auto)

lemma FLTick0_pri:
  assumes "FLTick0 tick P"
  shows "FLTick0 tick (pri p P)"
  using assms unfolding FLTick0_def pri_def apply auto
  by (simp add: pri_tickWF)

lemma prirel_extend_both_last_null_imp:
  assumes "prirel p (\<beta> &\<^sub>\<F>\<^sub>\<L> \<langle>A\<rangle>\<^sub>\<F>\<^sub>\<L>) (\<Gamma> &\<^sub>\<F>\<^sub>\<L> \<langle>A\<rangle>\<^sub>\<F>\<^sub>\<L>)" "length \<beta> = length \<Gamma>" "a \<in>\<^sub>\<F>\<^sub>\<L> A" "last \<beta> = \<bullet>" "last \<Gamma> = \<bullet>"
  shows "prirel p (\<beta> &\<^sub>\<F>\<^sub>\<L> \<langle>(A,a)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>) (\<Gamma> &\<^sub>\<F>\<^sub>\<L> \<langle>(A,a)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>)"
  using assms by (induct \<beta> \<Gamma> rule:prirel.induct, auto)

lemma prirel_extend_both_last_null_imp2:
  assumes "prirel p (\<beta> &\<^sub>\<F>\<^sub>\<L> \<langle>A\<rangle>\<^sub>\<F>\<^sub>\<L>) (\<Gamma> &\<^sub>\<F>\<^sub>\<L> \<langle>B\<rangle>\<^sub>\<F>\<^sub>\<L>)" "length \<beta> = length \<Gamma>" "a \<in>\<^sub>\<F>\<^sub>\<L> A" "last \<beta> = \<bullet>" "last \<Gamma> = \<bullet>" "\<forall>e. e \<in>\<^sub>\<F>\<^sub>\<L> A  \<longrightarrow> e \<in>\<^sub>\<F>\<^sub>\<L> B"
  shows "prirel p (\<beta> &\<^sub>\<F>\<^sub>\<L> \<langle>(A,a)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>) (\<Gamma> &\<^sub>\<F>\<^sub>\<L> \<langle>(B,a)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>)"
  using assms by (induct \<beta> \<Gamma> rule:prirel.induct, auto)

lemma prirel_eq_length_imp_last_member:
  assumes "length xs = length ys" "last xs = \<bullet>" "last ys \<noteq> \<bullet>" "prirel p (xs &\<^sub>\<F>\<^sub>\<L> \<langle>x\<rangle>\<^sub>\<F>\<^sub>\<L>) ys"
  shows  "\<forall>e. e \<in>\<^sub>\<F>\<^sub>\<L> x  \<longrightarrow> e \<in>\<^sub>\<F>\<^sub>\<L> last ys"
  using assms
proof(induct p xs ys rule:prirel.induct)
  case (1 p A Z)
  then show ?case apply auto
    apply (cases x, auto)
    apply (cases A, auto)
    by (cases Z, auto)
next
  case (2 p A Z zz)
then show ?case by auto
next
  case (3 p A aa Z)
  then show ?case by auto
next
  case (4 p A aa Z zz)
  then show ?case by auto
qed
 
lemma pri_FL2:
  assumes "FL2 P" "a \<in>\<^sub>\<F>\<^sub>\<L> A" "prirel p (\<beta> &\<^sub>\<F>\<^sub>\<L> \<langle>A\<rangle>\<^sub>\<F>\<^sub>\<L>) Z" "Z \<in> P"
  shows "\<exists>Z. prirel p (\<beta> &\<^sub>\<F>\<^sub>\<L> \<langle>(A,a)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>) Z \<and> Z \<in> P"
  using assms
proof (cases "last \<beta> = \<bullet>")
  case True
  then obtain \<Gamma> where pGama:"prirel p (\<beta> &\<^sub>\<F>\<^sub>\<L> \<langle>A\<rangle>\<^sub>\<F>\<^sub>\<L>) (\<Gamma> &\<^sub>\<F>\<^sub>\<L> \<langle>A\<rangle>\<^sub>\<F>\<^sub>\<L>) \<and> \<Gamma> &\<^sub>\<F>\<^sub>\<L> \<langle>A\<rangle>\<^sub>\<F>\<^sub>\<L> = Z \<and> length \<beta> = length \<Gamma>"
    using assms 
    by (metis Finite_Linear_Model.last.simps(1) acceptance.distinct(1) add_cancel_right_right amember.elims(2) concat_FL_last_not_bullet_absorb last_bullet_then_last_cons length.simps(1) length_cons prirel_cons_eq_length_imp_prirel_acceptances_last_bullet_eq prirel_cons_eq_length_imp_prirel_acceptances_last_not_bullet prirel_same_length)
  then show ?thesis
  proof (cases "last \<Gamma> = \<bullet>")
    case True
    then show ?thesis 
      by (metis FL2_def pGama assms(1) assms(2) assms(4) concat_FL_last_not_bullet_absorb prirel_extend_both_last_null_imp)
  next
    case False
    then have "\<Gamma> = Z"
      using concat_FL_last_not_bullet_absorb pGama by fastforce
    then have "\<forall>e. e \<in>\<^sub>\<F>\<^sub>\<L> A \<longrightarrow> e \<in>\<^sub>\<F>\<^sub>\<L> last \<Gamma>"
      using True pGama False assms(3) prirel_eq_length_imp_last_member by blast
    then have "\<Gamma> = butlast \<Gamma> &\<^sub>\<F>\<^sub>\<L> \<langle>last \<Gamma>\<rangle>\<^sub>\<F>\<^sub>\<L>"
      by (simp add: butlast_last_cons2_FL)
    then have "butlast \<Gamma> &\<^sub>\<F>\<^sub>\<L> \<langle>(last \<Gamma>,a)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L> \<in> P"
      by (metis FL2_def \<open>\<Gamma> = Z\<close> \<open>\<forall>e. e \<in>\<^sub>\<F>\<^sub>\<L> A \<longrightarrow> e \<in>\<^sub>\<F>\<^sub>\<L> Finite_Linear_Model.last \<Gamma>\<close> assms(1) assms(2) assms(4))

    have "prirel p (\<beta> &\<^sub>\<F>\<^sub>\<L> \<langle>A\<rangle>\<^sub>\<F>\<^sub>\<L>) \<Gamma>"
      using pGama \<open>\<Gamma> = Z\<close> by auto
    then have "prirel p (\<beta> &\<^sub>\<F>\<^sub>\<L> \<langle>A\<rangle>\<^sub>\<F>\<^sub>\<L>) (butlast \<Gamma> &\<^sub>\<F>\<^sub>\<L> \<langle>last \<Gamma>\<rangle>\<^sub>\<F>\<^sub>\<L>)"
      by (simp add: butlast_last_cons2_FL)
    have "length \<beta> = length (butlast \<Gamma>)"
      by (metis butlast_last_cons2_FL pGama rev_rev_butlast strong_less_eq_fltrace_cons_imp_lhs strong_less_eq_fltrace_eq_length strong_less_eq_fltrace_refl)

    then have "prirel p (\<beta> &\<^sub>\<F>\<^sub>\<L> \<langle>(A,a)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>) (butlast \<Gamma> &\<^sub>\<F>\<^sub>\<L> \<langle>(last \<Gamma>,a)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>)"
      using True \<open>\<forall>e. e \<in>\<^sub>\<F>\<^sub>\<L> A \<longrightarrow> e \<in>\<^sub>\<F>\<^sub>\<L> Finite_Linear_Model.last \<Gamma>\<close> \<open>prirel p (\<beta> &\<^sub>\<F>\<^sub>\<L> \<langle>A\<rangle>\<^sub>\<F>\<^sub>\<L>) (Finite_Linear_Model.butlast \<Gamma> &\<^sub>\<F>\<^sub>\<L> \<langle>Finite_Linear_Model.last \<Gamma>\<rangle>\<^sub>\<F>\<^sub>\<L>)\<close> assms(2) last_butlast_cons_bullet prirel_extend_both_last_null_imp2 by fastforce
    then show ?thesis
      using \<open>Finite_Linear_Model.butlast \<Gamma> &\<^sub>\<F>\<^sub>\<L> \<langle>(Finite_Linear_Model.last \<Gamma>,a)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L> \<in> P\<close> by blast
  qed
next
case False
  then show ?thesis 
    using assms
    by (metis concat_FL_last_not_bullet_absorb)
qed

lemma FL2_pri:
  assumes "FL2 P"
  shows "FL2 (pri p P)"
  using assms unfolding FL2_def pri_def apply auto
  by (simp add: assms pri_FL2)

text \<open>Does pri distribute through sequential composition in this model?\<close>

lemma prirel_consFL_both_imp:
  assumes "prirel p (x &\<^sub>\<F>\<^sub>\<L>y) (s &\<^sub>\<F>\<^sub>\<L> t)" "length x = length s" "last x = \<bullet>" "last s = \<bullet>"
  shows "prirel p x s"
  using assms by(induct x s rule:prirel.induct, auto)

lemma prirel_consFL_both_imp':
  assumes "prirel p x s" "prirel p y t" 
  shows "prirel p (x &\<^sub>\<F>\<^sub>\<L>y) (s &\<^sub>\<F>\<^sub>\<L> t)" 
  using assms apply(induct x s rule:prirel.induct, auto)
   apply (case_tac A, auto, case_tac Z, auto)
  apply (smt Collect_cong Finite_Linear_Model.last.simps(1) acceptance.distinct(1) concat_FL_last_not_bullet_absorb prirel.simps(1) prirelacc.simps(2))
  by (case_tac A, auto)

lemma prirel_consFL_exists:
  assumes "prirel p x (s &\<^sub>\<F>\<^sub>\<L> t)"
  shows "\<exists>y. prirel p y s"
  using assms apply(induct x s rule:prirel.induct, auto)     
        apply (metis Finite_Linear_Model.last.simps(1) concat_FL_last_not_bullet_absorb prirelAlt_bullet_refl prirelAlt_imp_prirel)
       apply (metis Finite_Linear_Model.last.simps(1) concat_FL_last_not_bullet_absorb prirelAlt_bullet_refl prirelAlt_imp_prirel)
  using prirel.simps(4) apply fastforce
     apply (metis prirel.simps(4))
  using prirel.simps(4) apply fastforce
  using prirel.simps(4) apply fastforce
  by (metis prirel.simps(4) prirelacc.simps(1))
  

lemma prirel_consFL_last_bullet_exists:
  assumes "prirel p x (s &\<^sub>\<F>\<^sub>\<L> t)" "last s = \<bullet>"
  shows "\<exists>s0 t0. x = s0 &\<^sub>\<F>\<^sub>\<L> t0 \<and> prirel p s0 s \<and> prirel p t0 t"
  using assms apply(induct x s rule:prirel.induct, auto)
        apply (metis bullet_left_zero2 prirelAlt_bullet_refl prirelAlt_imp_prirel)
       apply (metis bullet_left_zero2 prirelAlt_bullet_refl prirelAlt_imp_prirel)
      apply (metis fltrace_concat2.simps(2) prirel.simps(4))
     apply (metis acceptance.rep_eq amember.simps(1) event.rep_eq fltrace_concat2.simps(2) prirel.simps(4))
    apply (metis acceptance.rep_eq event.rep_eq fltrace_concat2.simps(2) prirel.simps(4))
   apply (metis acceptance.rep_eq fltrace_concat2.simps(2) prirel.simps(4) prirelacc.simps(1))
  by (metis fltrace_concat2.simps(2) prirel.simps(4) prirelacc.simps(1))

lemma prirel_consFL_last_bullet_exists':
  assumes "prirel p (s &\<^sub>\<F>\<^sub>\<L> t) x" "last s = \<bullet>"
  shows "\<exists>s0 t0. x = s0 &\<^sub>\<F>\<^sub>\<L> t0 \<and> prirel p s s0 \<and> prirel p t t0"
  using assms apply(induct x s rule:prirel.induct, auto)
  apply (metis bullet_left_zero2 prirelAlt_bullet_refl prirelAlt_imp_prirel)
       apply (metis bullet_left_zero2 prirelAlt_bullet_refl prirelAlt_imp_prirel)
      apply (metis fltrace_concat2.simps(2) prirel.simps(4))
     apply (metis acceptance.rep_eq amember.simps(1) event.rep_eq fltrace_concat2.simps(2) prirel.simps(4))
    apply (metis acceptance.rep_eq event.rep_eq fltrace_concat2.simps(2) prirel.simps(4))
   apply (metis acceptance.rep_eq fltrace_concat2.simps(2) prirel.simps(4) prirelacc.simps(1))
  by (metis fltrace_concat2.simps(2) prirel.simps(4) prirelacc.simps(1))
(* non trivial *)

lemma prirel_not_events:
  assumes "prirel p x s" "tick \<notin> events s"
  shows "tick \<notin> events x"
  using assms by (induct p x s rule:prirel.induct, auto)

lemma prirel_not_events':
  assumes "prirel p x s" "tick \<notin> events x"
  shows "tick \<notin> events s"
  using assms by (induct p x s rule:prirel.induct, auto)

lemma prirel_consFL_both_imp_prirel:
  assumes "prirel p (s &\<^sub>\<F>\<^sub>\<L> t) (u &\<^sub>\<F>\<^sub>\<L> v)" "last s = \<bullet>" "last u = \<bullet>" "length s = length u"
  shows "prirel p t v"
  using assms by(induct p s u rule:prirel.induct, auto)

lemma prirel_consFL_last_bullet_both:
  assumes "prirel p (s &\<^sub>\<F>\<^sub>\<L> \<langle>(\<bullet>,b)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>) (ys &\<^sub>\<F>\<^sub>\<L> \<langle>(a,c)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>)" "last s = \<bullet>" "last ys = \<bullet>" "maximal(p,b)" "c \<in>\<^sub>\<F>\<^sub>\<L> a \<or> a = \<bullet>"
  shows "b = c"
  using assms apply(induct p s ys rule:prirel.induct, auto)
         apply (case_tac Z, auto)
          apply (metis (no_types, hide_lams) Finite_Linear_Model.butlast.simps(1) butlast_last_cons2_FL concat_FL_last_not_bullet_absorb fltrace.exhaust prirel.simps(1) prirel.simps(2) rev3.simps(1) rev3_little_more_extra)
         apply (metis fltrace.distinct(1) fltrace.exhaust prirel.simps(2) rev3.simps(1) rev3_little_more_extra)
  apply (metis Finite_Linear_Model.butlast.simps(1) bullet_left_zero2 butlast_last_cons2_FL fltrace.exhaust fltrace_concat2.simps(2) prirel.simps(2))
  by (metis Finite_Linear_Model.butlast.simps(1) bullet_right_zero2 butlast_last_cons2_FL fltrace.exhaust fltrace_concat2.simps(2) prirel.simps(3) s_and_tick_iff)+

lemma tickWF_consFL_tick_imp_bullet:
  assumes "tickWF tick (ys &\<^sub>\<F>\<^sub>\<L> \<langle>(y,tick)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>)" "last ys = \<bullet>" "tick \<in>\<^sub>\<F>\<^sub>\<L> y \<or> y = \<bullet>"
  shows "y = \<bullet>"
  using assms apply (induct ys rule:tickWF.induct, auto)
  by (metis fltrace.distinct(1) rev3.simps(1) rev3_little_more)

lemma prirel_exists_tick_max:
  assumes "prirel p S Z" "last s = \<bullet>" "maximal(p,tick)" "S = (s &\<^sub>\<F>\<^sub>\<L> \<langle>(\<bullet>,tick)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>)" "tickWF tick Z"
  shows "\<exists>z. last z = \<bullet> \<and> Z = (z &\<^sub>\<F>\<^sub>\<L> \<langle>(\<bullet>,tick)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>) \<and> length s = length z"
  using assms 
proof (induct S Z rule:ftrace_cons_induct_both_eq_length)
  case 1
  then show ?case 
    using assms(1) prirel_same_length by blast
next
  case (2 x y)
  then show ?case 
    by (metis fltrace.distinct(1) rev3.simps(1) rev3_little_more)
next
  case (3 x y xs ys)
  then show ?case 
    by (metis Finite_Linear_Model.last.simps(1) bullet_right_zero2 last_bullet_then_last_cons last_cons_bullet_iff prirel.simps(1) prirel_consFL_both_imp_prirel)
next
  case (4 x y xs ys)
  then have "prirel p (s &\<^sub>\<F>\<^sub>\<L> \<langle>(\<bullet>,tick)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>) (ys &\<^sub>\<F>\<^sub>\<L> \<langle>y,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>)"
    by auto
  then obtain yA yEvent where yA:"y = (yA,yEvent)\<^sub>\<F>\<^sub>\<L> \<and> (yEvent \<in>\<^sub>\<F>\<^sub>\<L> yA \<or> yA = \<bullet>)"
    proof -
      assume a1: "\<And>yA yEvent. y = (yA,yEvent)\<^sub>\<F>\<^sub>\<L> \<and> (yEvent \<in>\<^sub>\<F>\<^sub>\<L> yA \<or> yA = \<bullet>) \<Longrightarrow> thesis"
      have "y \<le> (acceptance y,event y)\<^sub>\<F>\<^sub>\<L>"
        by (simp add: less_eq_aevent_def)
      then show ?thesis
        using a1 by (metis aevent_less_eq_iff_components event_in_acceptance)
    qed
  then have "prirel p (s &\<^sub>\<F>\<^sub>\<L> \<langle>(\<bullet>,tick)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>) (ys &\<^sub>\<F>\<^sub>\<L> \<langle>(yA,yEvent)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>)"
    using "4.prems"(1) "4.prems"(4) by auto
  then have "yEvent = tick"
            "yA = \<bullet>"
    using prirel_consFL_last_bullet_both "4.hyps"(4) yA assms(2) assms(3) apply fastforce
    using 4 tickWF_consFL_tick_imp_bullet 
    by (metis prirel_consFL_last_bullet_both yA)
  then have "ys &\<^sub>\<F>\<^sub>\<L> \<langle>y,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L> = ys &\<^sub>\<F>\<^sub>\<L> \<langle>(\<bullet>,tick)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L> \<and> Finite_Linear_Model.length s = Finite_Linear_Model.length ys"
    by (metis "4.hyps"(2) "4.hyps"(3) "4.prems"(4) assms(2) fltrace.inject(2) rev3_little_more rev3_rev3_const2_last yA)
  then show ?case
    using "4.hyps"(4) by blast
qed

lemma pri_dist_SeqComp:
  assumes "FLTick0 tick P" "maximal(p,tick)"
  shows "pri p (P (tick);\<^sub>\<F>\<^sub>\<L> Q) = ((pri p P) (tick);\<^sub>\<F>\<^sub>\<L> (pri p Q))"
  using assms unfolding pri_def SeqComp_def
proof (auto)
  fix "x" "s" "t"
  assume  assm0:"FLTick0 tick P"
      and assm1:"prirel p x (s &\<^sub>\<F>\<^sub>\<L> t)"
      and assm2:"s &\<^sub>\<F>\<^sub>\<L> \<langle>(\<bullet>,tick)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L> \<in> P"
      and assm3:"t \<in> Q"
  show "\<exists>s. (\<exists>Z. prirel p (s &\<^sub>\<F>\<^sub>\<L> \<langle>(\<bullet>,tick)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>) Z \<and> Z \<in> P) \<and> (\<exists>t. (\<exists>Z. prirel p t Z \<and> Z \<in> Q) \<and> x = s &\<^sub>\<F>\<^sub>\<L> t) \<or>
           (\<exists>Z. prirel p s Z \<and> Z \<in> P) \<and> tick \<notin> events s \<and> x = s"
  proof (cases "last s = \<bullet>")
    case True
    then obtain s0 t0 where s0t0:"x = s0 &\<^sub>\<F>\<^sub>\<L> t0 \<and> prirel p s0 s \<and> prirel p t0 t"
      using assm1 prirel_consFL_last_bullet_exists by blast
    then have "prirel p \<langle>(\<bullet>,tick)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L> \<langle>(\<bullet>,tick)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>"
      using assms(2) by auto
    then have "prirel p (s0 &\<^sub>\<F>\<^sub>\<L> \<langle>(\<bullet>,tick)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>) (s &\<^sub>\<F>\<^sub>\<L> \<langle>(\<bullet>,tick)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>)"
      using s0t0 prirel_consFL_both_imp' by blast    
    then show ?thesis
      using assm2 assm3 s0t0 by blast
  next
    case False
    then show ?thesis
      by (smt FLTick0_def assm1 assm2 assms bullet_right_zero2 concat_FL_last_not_bullet_absorb last_rev3_is_bullet length.simps(1) length_cons pri_tickWF prirel.simps(1) prirel_cons_eq_length_imp_prirel_acceptances_eq prirel_same_length rev3_rev3_const2_last tickWF_last_x_is_emptyset)
  qed
next
  fix "x" "s"
  assume  assm0:"FLTick0 tick P"
    and   assm1:"maximal(p,tick)"
    and   assm2:"prirel p x s"
    and   assm3:"s \<in> P"
    and   assm4:"tick \<notin> events s"
  show "\<exists>s. (\<exists>Z. prirel p (s &\<^sub>\<F>\<^sub>\<L> \<langle>(\<bullet>,tick)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>) Z \<and> Z \<in> P) \<and> (\<exists>t. (\<exists>Z. prirel p t Z \<and> Z \<in> Q) \<and> x = s &\<^sub>\<F>\<^sub>\<L> t) \<or>
            (\<exists>Z. prirel p s Z \<and> Z \<in> P) \<and> tick \<notin> events s \<and> x = s"
  proof -
    have "tick \<notin> events x"
      using assm2 assm4 prirel_not_events
      by fastforce
    then show ?thesis
      using assm2 assm3 by blast
  qed
next
  fix "s" "t" "Z" "Za"
  assume 
      assm0: "FLTick0 tick P"
  and assm1: "maximal(p,tick)"
  and assm2: "prirel p (s &\<^sub>\<F>\<^sub>\<L> \<langle>(\<bullet>,tick)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>) Z"
  and assm3: "Z \<in> P"
  and assm4: "prirel p t Za"
  and assm5: "Za \<in> Q"
  show "\<exists>Z. prirel p (s &\<^sub>\<F>\<^sub>\<L> t) Z \<and> (\<exists>s. s &\<^sub>\<F>\<^sub>\<L> \<langle>(\<bullet>,tick)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L> \<in> P \<and> (\<exists>t. t \<in> Q \<and> Z = s &\<^sub>\<F>\<^sub>\<L> t) \<or> s \<in> P \<and> tick \<notin> events s \<and> Z = s)"
  proof (cases "last s = \<bullet>")
    case True
    then obtain s0 where s0:"prirel p (s &\<^sub>\<F>\<^sub>\<L> \<langle>(\<bullet>,tick)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>) (s0 &\<^sub>\<F>\<^sub>\<L> \<langle>(\<bullet>,tick)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>) \<and> last s0 = \<bullet> \<and> length s = length s0 \<and> Z = (s0 &\<^sub>\<F>\<^sub>\<L> \<langle>(\<bullet>,tick)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>)"
      by (metis FLTick0_def assm0 assm1 assm2 assm3 prirel_exists_tick_max)
    then have "prirel p s s0"
      using True prirel_consFL_both_imp by blast
    then have "prirel p (s &\<^sub>\<F>\<^sub>\<L> t) (s0 &\<^sub>\<F>\<^sub>\<L> Za)"
      by (simp add: assm4 prirel_consFL_both_imp')
    then have "\<exists>Z. prirel p (s &\<^sub>\<F>\<^sub>\<L> t) (s0 &\<^sub>\<F>\<^sub>\<L> Za) \<and> s0 &\<^sub>\<F>\<^sub>\<L> \<langle>(\<bullet>,tick)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L> \<in> P \<and> Za \<in> Q \<and> Z = s0 &\<^sub>\<F>\<^sub>\<L> Za"
      using s0 assm5 assm3 by blast
    then show ?thesis
      by blast
  next
    case False
    then show ?thesis 
      by (metis FLTick0_def \<open>Z \<in> P\<close> \<open>prirel p (s &\<^sub>\<F>\<^sub>\<L> \<langle>(\<bullet>,tick)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>) Z\<close> assms(1) concat_FL_last_not_bullet_absorb prirel_cons_eq_length_imp_prirel_acceptances_last_bullet_eq prirel_cons_eq_length_imp_prirel_acceptances_last_not_bullet prirel_same_length tickWF_last_x_is_emptyset)
  qed
next
  fix "s" "Z"
  assume 
       assm0: "FLTick0 tick P"
  and  assm1: "maximal(p,tick)"
  and  assm2: "tick \<notin> events s"
  and  assm3: "prirel p s Z"
  and  assm4: "Z \<in> P"
  show "\<exists>Z. prirel p s Z \<and> (\<exists>s. s &\<^sub>\<F>\<^sub>\<L> \<langle>(\<bullet>,tick)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L> \<in> P \<and> (\<exists>t. t \<in> Q \<and> Z = s &\<^sub>\<F>\<^sub>\<L> t) \<or> s \<in> P \<and> tick \<notin> events s \<and> Z = s)"
    using assm3 assm4 assm2 apply (rule_tac x="Z" in exI, auto)
    apply (rule_tac x="Z" in exI, auto)
    by (simp add: prirel_not_events')+
qed

end