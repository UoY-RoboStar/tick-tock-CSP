theory Finite_Linear_Tick_Param

imports
  Finite_Linear_Model
begin
  
text \<open>This theory extends the finite linear model to capture termination by
      considering the special event 'tick' and where termination is unstable. \<close>

type_synonym 'e tick = "'e fltrace \<Rightarrow> 'e"
type_synonym 'e fltracetick = "'e \<Rightarrow> 'e fltrace"

(* Do we actually need to refuse everything after tick?*)

(* Problem with this treatment of tick, rather than at the
   data-type level is that we need to enforce tick as the
   last event possible for a trace via a healthiness
   condition. *)

primrec events :: "'e fltrace \<Rightarrow> 'e set" where
"events \<langle>A\<rangle>\<^sub>\<F>\<^sub>\<L> = {}" |
"events (A #\<^sub>\<F>\<^sub>\<L> xs) = {event(A)} \<union> events(xs)"

definition Skip :: "'e \<Rightarrow> 'e fltrace set" where
"Skip tick = {\<langle>\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>,\<langle>(\<bullet>,tick)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>}"

definition SeqComp :: "'e fltrace set \<Rightarrow> 'e \<Rightarrow> 'e fltrace set \<Rightarrow> 'e fltrace set" ("(_/ '(_');\<^sub>\<F>\<^sub>\<L> _)" [51, 51, 51] 50) where (*(infixl ";\<^sub>\<F>\<^sub>\<L>" 65) where*)
"P (tick);\<^sub>\<F>\<^sub>\<L> Q = {x|x s t. (s &\<^sub>\<F>\<^sub>\<L> \<langle>(\<bullet>,tick)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L> \<in> P \<and> t \<in> Q \<and> x = s &\<^sub>\<F>\<^sub>\<L> t) \<or> (s \<in> P \<and> tick \<notin> events(s) \<and> x = s)}" (*  \<union> {s|s. s\<in> P \<and> tick \<notin> events(s)}" *)

fun tickWF :: "'e \<Rightarrow> 'e fltrace \<Rightarrow> bool" where
"tickWF tick \<langle>A\<rangle>\<^sub>\<F>\<^sub>\<L> = (tick \<notin>\<^sub>\<F>\<^sub>\<L> A)" |
"tickWF tick (A #\<^sub>\<F>\<^sub>\<L> xs) = (tick \<notin>\<^sub>\<F>\<^sub>\<L> acceptance(A) \<and> (if event(A) = tick then (xs = \<langle>\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>) else tickWF tick xs))"

definition FLTick0 :: "'e \<Rightarrow> 'e fltrace set \<Rightarrow> bool" where
"FLTick0 tick P \<equiv> \<forall>x. x \<in> P \<longrightarrow> tickWF tick x"

lemma FLTick0_Skip:
  "FLTick0 tick (Skip tick)"
  unfolding Skip_def FLTick0_def by auto

lemma tickWF_last_x_is_emptyset:
  assumes "tickWF tick x" "tick \<in> events x"
  shows "last x = \<bullet>"
  using assms apply (induct x rule:tickWF.induct, auto)
  by fastforce

lemma tickWF_consFL_iff_fixpoint:
  assumes "tick \<in> events x" "tickWF tick (x &\<^sub>\<F>\<^sub>\<L> \<langle>(\<bullet>,tick)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>)"
  shows "x = x &\<^sub>\<F>\<^sub>\<L> \<langle>(\<bullet>,tick)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>"
  using assms apply (induct x, auto, case_tac xa, auto, case_tac x1, auto)
  apply (case_tac x1a, auto)
   apply (case_tac a, auto)
  apply presburger
  by (metis amember.simps(1) tickWF.simps(1))

fun butlastaevent :: "'a fltrace \<Rightarrow> 'a fltrace" where
"butlastaevent \<langle>x\<rangle>\<^sub>\<F>\<^sub>\<L> = \<langle>x\<rangle>\<^sub>\<F>\<^sub>\<L>" |
"butlastaevent (x #\<^sub>\<F>\<^sub>\<L> \<langle>y\<rangle>\<^sub>\<F>\<^sub>\<L>) = \<langle>y\<rangle>\<^sub>\<F>\<^sub>\<L>" |
"butlastaevent (x #\<^sub>\<F>\<^sub>\<L> xs) = x #\<^sub>\<F>\<^sub>\<L> butlastaevent xs"

lemma tickWF_tick_events_butlastaevent:
  assumes "tick \<in> events x" "tickWF tick x"
  shows "x = butlastaevent x &\<^sub>\<F>\<^sub>\<L> \<langle>(\<bullet>,tick)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>"
  using assms apply (induct x)
   apply (case_tac x, auto, case_tac x1a, auto)
  apply (case_tac x1a, auto)
   apply (case_tac "b = tick", auto)
   apply (case_tac x, auto)
   apply (case_tac "b = tick", auto)
  by (case_tac x, auto)

lemma x_in_P_tickWF_exists:
  assumes "x \<in> P" "tickWF tick x"
  shows "\<exists>s. s &\<^sub>\<F>\<^sub>\<L> \<langle>(\<bullet>,tick)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L> \<in> P \<and> (\<exists>t. (t = \<langle>\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L> \<or> t = \<langle>(\<bullet>,tick)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>) \<and> x = s &\<^sub>\<F>\<^sub>\<L> t) \<or> s \<in> P \<and> tick \<notin> events s \<and> x = s"
  using assms
proof (cases "tick \<in> events(x)")
  case True
  then have butlastaevent:"x = butlastaevent x &\<^sub>\<F>\<^sub>\<L> \<langle>(\<bullet>,tick)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>"
    by (simp add: assms(2) tickWF_tick_events_butlastaevent)
  then have "(\<exists>t. (t = \<langle>\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L> \<or> t = \<langle>(\<bullet>,tick)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>) \<and> x = butlastaevent x &\<^sub>\<F>\<^sub>\<L> t)"
    by blast
  then have "butlastaevent x &\<^sub>\<F>\<^sub>\<L> \<langle>(\<bullet>,tick)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L> \<in> P \<and> (\<exists>t. (t = \<langle>\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L> \<or> t = \<langle>(\<bullet>,tick)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>) \<and> x = butlastaevent x &\<^sub>\<F>\<^sub>\<L> t)"
    using butlastaevent assms(1) by auto
  then have "\<exists>s. s &\<^sub>\<F>\<^sub>\<L> \<langle>(\<bullet>,tick)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L> \<in> P \<and> (\<exists>t. (t = \<langle>\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L> \<or> t = \<langle>(\<bullet>,tick)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>) \<and> x = s &\<^sub>\<F>\<^sub>\<L> t \<and> s = butlastaevent x)"
    by blast
  then have "\<exists>s. s &\<^sub>\<F>\<^sub>\<L> \<langle>(\<bullet>,tick)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L> \<in> P \<and> (\<exists>t. (t = \<langle>\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L> \<or> t = \<langle>(\<bullet>,tick)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>) \<and> x = s &\<^sub>\<F>\<^sub>\<L> t)"
    by blast
  then show ?thesis
    by auto
next
  case False
  then show ?thesis using assms by auto
qed

lemma Skip_right_unit:
  assumes "FL1 P" "FLTick0 tick P"
  shows "(P (tick);\<^sub>\<F>\<^sub>\<L> (Skip tick)) = P"
  using assms unfolding SeqComp_def Skip_def apply auto
  using x_in_P_tickWF_exists
  by (metis FLTick0_def)

lemma s_and_tick_iff:
  "s &\<^sub>\<F>\<^sub>\<L> \<langle>(\<bullet>,tick)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L> = \<langle>(\<bullet>,tick)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L> \<longleftrightarrow> (s = \<langle>\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>)"
  by (induct s, auto, case_tac x, auto, case_tac s, auto, case_tac x1, auto)

lemma Stop_is_left_zero:
  shows "(Stop (tick);\<^sub>\<F>\<^sub>\<L> P) = Stop"
  unfolding Stop_def SeqComp_def apply auto
   apply (case_tac s, auto, case_tac x1, auto, case_tac t, auto, case_tac x1, auto)
  by (case_tac s, auto, case_tac x1, auto)

lemma Div_is_left_zero:
  shows "(Div (tick);\<^sub>\<F>\<^sub>\<L> P) = Div"
  unfolding Div_def SeqComp_def apply auto
  by (metis Finite_Linear_Model.last.simps(1) Finite_Linear_Model.last.simps(2) bullet_right_zero2 fltrace.distinct(1) last_dist_plus rev3.simps(1) rev3_little_more)

lemma Skip_left_unit:
  assumes "FL0 P" "FL1 P" 
  shows "(Skip tick (tick);\<^sub>\<F>\<^sub>\<L> P) = P"
  using assms unfolding SeqComp_def Skip_def apply auto
  apply (auto simp add:s_and_tick_iff)
  by (metis Finite_Linear_Model.last.simps(1) Finite_Linear_Model.last.simps(2) bullet_right_zero2 fltrace.distinct(1) last_dist_plus rev3.simps(1) rev3_little_more)

lemma SeqComp_dist_IntChoice_left:
  shows "P (tick);\<^sub>\<F>\<^sub>\<L> (Q \<sqinter>\<^sub>\<F>\<^sub>\<L> R) = (P (tick);\<^sub>\<F>\<^sub>\<L> Q) \<sqinter>\<^sub>\<F>\<^sub>\<L> (P (tick);\<^sub>\<F>\<^sub>\<L> R)"
  unfolding SeqComp_def IntChoice_def by auto

lemma SeqComp_dist_IntChoice_right:
  shows "(P \<sqinter>\<^sub>\<F>\<^sub>\<L> Q) (tick);\<^sub>\<F>\<^sub>\<L> R = (P (tick);\<^sub>\<F>\<^sub>\<L> R) \<sqinter>\<^sub>\<F>\<^sub>\<L> (Q (tick);\<^sub>\<F>\<^sub>\<L> R)"
  unfolding SeqComp_def IntChoice_def by auto

lemma
  shows "(P \<box>\<^sub>\<F>\<^sub>\<L> Q) (tick);\<^sub>\<F>\<^sub>\<L> R = (P (tick);\<^sub>\<F>\<^sub>\<L> R) \<box>\<^sub>\<F>\<^sub>\<L> (Q (tick);\<^sub>\<F>\<^sub>\<L> R)"
  unfolding SeqComp_def ExtChoice_def apply auto
  oops

lemma not_in_events_not_in_butlast_twice:
  assumes "tick \<notin> events(x)"
  shows "tick \<notin> events(butlast(butlast x))"
  using assms by (induct x, auto)

end
