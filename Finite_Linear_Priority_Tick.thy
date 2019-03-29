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

(* non trivial
lemma
  shows "pri p (P (tick);\<^sub>\<F>\<^sub>\<L> Q) = ((pri p P) (tick);\<^sub>\<F>\<^sub>\<L> (pri p Q))"
  unfolding pri_def SeqComp_def apply auto*)
  


end