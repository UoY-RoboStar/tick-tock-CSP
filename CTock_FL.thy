theory TTock_FL

imports
  TTock
  "HOL-Library.Sublist"
  Finite_Linear_Model
begin

text \<open>Function mapping to non-subset closed refusals.\<close>

fun funFLTTockl :: "('a tockevent) fltrace \<Rightarrow> 'a ctockl" where
"funFLTTockl \<langle>A\<rangle>\<^sub>\<F>\<^sub>\<L> = (if A = \<bullet> then [] else [Ref {z. z \<notin>\<^sub>\<F>\<^sub>\<L> A}])" |
"funFLTTockl (A #\<^sub>\<F>\<^sub>\<L> fl) = (if event(A) = tock \<and> acceptance(A) \<noteq> \<bullet> then
                             (Ref {z. z \<notin>\<^sub>\<F>\<^sub>\<L> acceptance(A)} # REvent tock # (funFLTTockl fl)) 
                          else ((REvent (event A)) # funFLTTockl fl))" 

lemma funFLTTockl_is_ctockWD[simp]:
  "ctockWD (funFLTTockl fltrace)"
  apply (induct fltrace rule:funFLTTockl.induct, auto)
  using event_in_acceptance by fastforce

lift_definition funFLTTock :: "('a tockevent) fltrace \<Rightarrow> 'a ctock" is funFLTTockl by auto

definition fFL2Tock :: "('a tockevent) fltrace set \<Rightarrow> 'a ctock set" where
"fFL2Tock P = {funFLTTock fl|fl. fl \<in> P}"

lemma fFL2Tock_univ_disj: 
  "fFL2Tock (\<Union> P) = \<Union>{fFL2Tock fl|fl. fl \<in> P}"
  unfolding fFL2Tock_def by auto

definition TTock2FLf :: "'a ctock set \<Rightarrow> ('a tockevent) fltrace set" where
"TTock2FLf P = \<Union>{fl. (fFL2Tock fl) \<subseteq> P}"

lemma "mkFL1(TTock2FLf(P)) = \<Union>{mkFL1(fl)| fl. (fFL2Tock fl) \<subseteq> P}"
  unfolding mkFL1_def TTock2FLf_def by auto

lemma fFL2Tock_mono:
  assumes "P \<subseteq> Q"
  shows "fFL2Tock(P) \<subseteq> fFL2Tock(Q)"
  using assms unfolding fFL2Tock_def by auto

lemma TTock2FLf_mono:
  assumes "P \<subseteq> Q"
  shows "TTock2FLf(P) \<subseteq> TTock2FLf(Q)"
  using assms unfolding TTock2FLf_def by auto

lemma prefix_exists_funFLTTockl:
  assumes "prefix s (funFLTTockl fl)" (*"FL1 P" "FL0 P"*)
  shows "\<exists>fl\<^sub>0. s = funFLTTockl fl\<^sub>0 \<and> fl\<^sub>0 \<le> fl"
  using assms proof(induct fl arbitrary:s rule:funFLTTockl.induct)
  case (1 A)
  then show ?case
  proof (cases A)
    case acnil
    then show ?thesis using 1
      apply auto 
      by (rule exI[where x="\<langle>\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>"], auto)
  next
    case (acset x2)
    then show ?thesis using 1
     proof (cases s)
      case Nil
      then show ?thesis by (intro exI[where x="\<langle>\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>"], auto)
    next
      case (Cons a list)
      then show ?thesis using 1 acset by (intro exI[where x="\<langle>[x2]\<^sub>\<F>\<^sub>\<L>\<rangle>\<^sub>\<F>\<^sub>\<L>"], auto)
    qed
  qed
next
  case (2 A fl)
  then show ?case
  proof(induct s)
    case Nil
    then show ?case by (auto, intro exI[where x="\<langle>\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>"], auto)
  next
    case C1:(Cons a x)
    then show ?case 
    proof(cases "event A = tock \<and> acceptance A \<noteq> \<bullet>")
      case True
      then show ?thesis using C1
        proof (induct x)
          case Nil
          then show ?case 
            using C1
            apply (auto, intro exI[where x="\<langle>acceptance(A)\<rangle>\<^sub>\<F>\<^sub>\<L>"])
            by auto
        next
          case C2:(Cons aa ss)
          then have AA: 
            "[a,aa] = funFLTTockl(\<langle>A,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>)"
            by (simp add: C2.prems(4))

          have "prefix ss (funFLTTockl fl)" 
                       "\<exists>fl\<^sub>0. ss = funFLTTockl fl\<^sub>0 \<and> fl\<^sub>0 \<le> fl"
            using C2 by auto
          then have "\<exists>fl\<^sub>0. a # aa # ss = a # aa # funFLTTockl fl\<^sub>0 \<and> fl\<^sub>0 \<le> fl"
            by auto
          then have "\<exists>fl\<^sub>0. a # aa # ss = funFLTTockl (A #\<^sub>\<F>\<^sub>\<L> fl\<^sub>0) \<and> fl\<^sub>0 \<le> fl"
            using AA by auto
          then show ?case
            using less_eq_fltrace.simps(3) by blast
        qed
    next
      case False
      then show ?thesis
        by (metis C1.prems(2) C1.prems(3) Cons_prefix_Cons dual_order.refl funFLTTockl.simps(2) less_eq_fltrace.simps(3))
    qed
  qed
qed

lemma funFLTTockl_consC_mutual_extend:
  assumes "xs = funFLTTockl fl"
  shows "\<exists>z. xs @\<^sub>C [y] = funFLTTockl (fl @\<^sub>\<F>\<^sub>\<L> z)"
  using assms 
proof (induct fl arbitrary: xs y rule:funFLTTockl.induct)
  case (1 A)
  then show ?case
  proof (cases A)
    case acnil
    {
      then have "\<exists>z. [y] = funFLTTockl z"
      proof (cases y)
      case (Ref x1)
      then show ?thesis 
        apply auto
        apply (rule exI[where x="\<langle>[{x. x \<notin> x1}]\<^sub>\<F>\<^sub>\<L>\<rangle>\<^sub>\<F>\<^sub>\<L>"])
        by auto
      next
      case (REvent x2)
      then show ?thesis 
      proof (cases x2)
        case (Event ev)
        then show ?thesis 
          using acnil apply (intro exI[where x="\<langle>([{Event ev}]\<^sub>\<F>\<^sub>\<L>,Event ev)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>"])
          apply auto
          by (simp add: REvent)
      next
        case tock
        then show ?thesis 
          using acnil apply (intro exI[where x="\<langle>(\<bullet>,tock)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>"])
          apply auto
          by (simp add: REvent)
      qed
      qed
      then show ?thesis using "1" acnil by auto
    }
  next
    case (acset x2)
    then show ?thesis using "1"
    proof (cases y)
      case (Ref x1)
      then show ?thesis using 1 acset apply auto
        apply (rule exI[where x="\<langle>[{x. x \<notin> x1}]\<^sub>\<F>\<^sub>\<L>\<rangle>\<^sub>\<F>\<^sub>\<L>"])
          by auto
    next
      case (REvent rev)
      then show ?thesis 
        proof (cases rev)
          case (Event x1)
          then show ?thesis using 1 acset REvent apply auto
            by (rule exI[where x="\<langle>(\<bullet>,Event x1)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>"], auto)
        next
          case tock
          then show ?thesis using 1 acset REvent apply auto
             apply (rule exI[where x="\<langle>([x2]\<^sub>\<F>\<^sub>\<L>,tock)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>"], auto)
            by (rule exI[where x="\<langle>(\<bullet>,tock)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>"], auto)
        qed 
    qed
  qed
next
  case (2 A fl)
  then show ?case by auto
qed

thm rev_induct

lemma ctockWD_concat_eq_some_concatC:
  assumes "ctockWD (xs @ [y])"
  shows "\<exists>z. xs @\<^sub>C [z] = xs @ [y]"
  using assms apply (induct xs arbitrary: y rule:ctockWD.induct, auto)
  apply (case_tac ya, auto)
  by (metis (full_types) ctockWD.simps(4) ctockWD.simps(6) ctockl_append.simps(4) tockevent.exhaust)

lemma funFLTTockl_consC_mutual_extend2:
  assumes "xs = funFLTTockl fl" "ctockWD (xs @ [y])"
  shows "\<exists>z. xs @ [y] = funFLTTockl (fl @\<^sub>\<F>\<^sub>\<L> z)"
  by (metis assms(1) assms(2) ctockWD_concat_eq_some_concatC funFLTTockl_consC_mutual_extend)

(* We could have instead established the following rev induction theorem,
   but with the above two theorems we can transfer the equality on @\<^sub>C to one
   over standard @. This is key to showing that we have a bijection under
   fFL2Tock(TTock2FLf(P)). *)

lemma tockl_is_in_funFLTTockl:
  assumes "ctockWD x" "TTockl2 P" (*"\<forall>s t. (t \<in> P \<and> list_le s t) \<longrightarrow> (s \<in> P)"*)
      and "\<forall>x\<in>P. ctockWD x"
      and "x \<in> P"
    shows "\<exists>fl. x = funFLTTockl fl \<and> (\<exists>x. {xa. (\<exists>fl. xa = funFLTTockl fl \<and> fl \<in> x) \<and> ctockWD xa} \<subseteq> P \<and> fl \<in> x)"
  using assms proof(induct x rule:rev_induct)
  case Nil
  then show ?case apply auto
     by (smt funFLTTockl.simps(1) mem_Collect_eq singletonD singletonI subsetI)
next
  case (snoc x xs)
  then have "xs \<in> P"
    apply auto
    using list_le_concat_prefix TTockl2_def by blast
  then show ?case using "snoc.hyps"
    apply auto
    using assms(2) funFLTTockl_consC_mutual_extend2 
    by (smt assms(2) funFLTTockl_consC_mutual_extend2 mem_Collect_eq singletonD singletonI snoc.prems(3) snoc.prems(4) subsetI)
qed

lemma fFL2Tock_TTock2FLf_refines: "fFL2Tock(TTock2FLf(P)) \<subseteq> P"
  unfolding TTock2FLf_def fFL2Tock_def by auto

lemma xTTock2_refines_fFL2Tock_TTock2FLf:
  assumes "xTTock2 P"
  shows "P \<subseteq> fFL2Tock(TTock2FLf(P))"
  using assms unfolding TTock2FLf_def fFL2Tock_def apply auto
  apply transfer 
  apply auto
  using tockl_is_in_funFLTTockl by blast

lemma xTTock2_bij:
  assumes "xTTock2 P"
  shows "fFL2Tock(TTock2FLf(P)) = P"
  using assms
  by (simp add: fFL2Tock_TTock2FLf_refines subset_antisym xTTock2_refines_fFL2Tock_TTock2FLf)

lemma fFL2Tock_TTock2FLf_is_xTTock1:
  assumes "xTTock1 P"
  shows "xTTock1(fFL2Tock(TTock2FLf(P)))"
  using assms
  by (simp add: xTTock1_imp_xTTock2 xTTock2_bij)

lemma
  assumes "prefix s t" "FL0 P" "FL1 P" 
      and "t \<in> {funFLTTockl fl|fl. fl \<in> P \<and> ctockWD(funFLTTockl fl)}"
    shows "s \<in> {funFLTTockl fl|fl. fl \<in> P \<and> ctockWD(funFLTTockl fl)}"
  using assms 
  by (smt FL1_def ctockWD_list_le mem_Collect_eq prefix_exists_funFLTTockl)

lemma TTockl2_prefix_help1:
  assumes "X # Y # Z \<in> P" "TTockl2 P"
  shows "[X, Y] \<in> P"
  using assms
  by (metis TTockl2_def append.left_neutral append_Cons list_le_concat_prefix_also_prefix prefix_Cons prefix_order.dual_order.refl)

lemma TTockl2_prefix_help2:
  assumes "X # Y \<in> P" "TTockl2 P"
  shows "[X] \<in> P"
  using assms 
  by (meson TTockl2_def Cons_prefix_Cons prefix_code(1))

lemma funFLTTockl_prefix_help:
  assumes "funFLTTockl (x1a #\<^sub>\<F>\<^sub>\<L> t) \<in> P" "TTockl2 P"
  shows "funFLTTockl \<langle>x1a,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L> \<in> P"
  using assms TTockl2_prefix_help2 TTockl2_prefix_help1 
  by fastforce

lemma fFL2Tock_is_xTTock2:
  assumes "FL1 P"
  shows "xTTock2(fFL2Tock(P))"
  using assms unfolding fFL2Tock_def apply transfer
  unfolding TTockl2_def apply auto
   apply (meson FL1_def prefix_exists_funFLTTockl)
  using ctockWD_list_le funFLTTockl_is_ctockWD by blast

(* Work in progress below *)

definition TTock2FL1 :: "'a ctock set \<Rightarrow> ('a tockevent) fltrace set" where
"TTock2FL1 P = \<Union>{fl. FL1 fl \<and> (fFL2Tock fl) \<subseteq> P}"

lemma TTock2FL1_mono:
  assumes "P \<subseteq> Q"
  shows   "TTock2FL1(P) \<subseteq> TTock2FL1(Q)"
  using assms unfolding TTock2FL1_def by auto

lemma fFL2Tock_TTock2FL1_refines: "fFL2Tock(TTock2FL1(P)) \<subseteq> P"
  unfolding TTock2FL1_def fFL2Tock_def by auto

lemma xTTock2_refines_fFL2Tock_TTock2FL1:
  assumes "xTTock2 P"
  shows "P \<subseteq> fFL2Tock(TTock2FL1(P))"
  using assms unfolding TTock2FL1_def fFL2Tock_def apply auto
  apply transfer 
  apply auto
  oops

lemma
  assumes "xTTock2 P"
  shows "fFL2Tock(TTock2FL1(P)) = P"
  using assms unfolding TTock2FL1_def
  apply auto
  oops

lemma FL1_two_element_set:
  shows "FL1 {\<langle>\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>, \<langle>(\<bullet>,x1)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>}"
proof -
  have "FL1 {\<langle>\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>, \<langle>(\<bullet>,x1)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>}
        =
        (mkFL1 ({\<langle>\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>, \<langle>(\<bullet>,x1)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>}) = {\<langle>\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>, \<langle>(\<bullet>,x1)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>})"
    using FL1_fixpoint by auto
  also have "... = True"
    unfolding mkFL1_def apply auto
     apply (metis dual_order.refl fltrace_antisym fltrace_trans prefixFL_induct2)
    apply (case_tac x, auto)  
      apply (case_tac x1, auto) 
     apply (case_tac x21, auto) 
    apply (case_tac a, auto) 
      apply (simp_all add: Abs_aevent_inverse less_eq_aevent_def)
    by (metis antisym_conv dual_order.refl order.trans prefixFL_induct2)
  finally show ?thesis by auto
qed

lemma FL1_prefix_set:
 "FL1 {z. z \<le> Y}"
  unfolding FL1_def by auto

lemma 
  assumes "funFLTTockl ys \<in> P" "xs \<le> ys" "TTockl2 P"
  shows "funFLTTockl xs \<in> P"
  using assms
  oops

lemma Ref_tock_le_in_funFLTTockl:
  assumes "[Ref {z. z \<notin> x2}, REvent tock] \<in> P" "TTockl2 P" "tock \<in> x2" 
          -- \<open>The following healthiness condition was introduced because of this lemma\<close>
          "TTockl3 P"
  shows "fl \<le> \<langle>([x2]\<^sub>\<F>\<^sub>\<L>,tock)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L> \<longrightarrow> funFLTTockl fl \<in> P"
  using assms 
proof (induct fl)
  have Nil_in:"[] \<in> P" using assms unfolding TTockl2_def apply auto
    using Nil_prefix by blast
   case (Acceptance x)
  then show ?case 
    apply (case_tac x, auto simp add:Nil_in)
    using TTockl2_prefix_help2 by blast
next
  case (AEvent x1a fl)
  then show ?case apply auto
         apply (case_tac fl, auto, case_tac x1a, auto, case_tac x1, auto)
        apply (case_tac fl, auto, case_tac x1a, auto, case_tac x1, auto, case_tac x1, auto)
       apply (case_tac fl, auto, case_tac x1a, auto, case_tac x1, auto)
      apply (case_tac fl, auto, case_tac x1a, auto, case_tac a, auto)
       apply (metis Collect_cong acceptance_set amember.simps(2) less_eq_acceptance.simps(3) less_eq_aevent_def)
      apply (case_tac fl, auto, case_tac x1a, auto, case_tac x1, auto)
     apply (case_tac fl, auto, case_tac x1a, auto, case_tac a, auto)
    apply (simp_all add: less_eq_aevent_def) 
    apply (case_tac fl, auto, case_tac x1a, auto)
    apply (metis (no_types, lifting) TTockl3_def append_eq_Cons_conv assms(1) assms(4))
    using less_eq_acceptance.elims(2) by blast
qed

(*
lemma xpp3:
  assumes "xs = funFLTTockl fl" "ctockWD (xs @ [y])" 
  shows "\<exists>z. xs @ [y] = funFLTTockl (fl @\<^sub>\<F>\<^sub>\<L> z) \<and> (\<exists>x. FL1 x \<and> fl \<in> x \<and> (fl @\<^sub>\<F>\<^sub>\<L> z) \<in> x)"
  using assms sorry

lemma xpp21:
  assumes "xs = funFLTTockl fl"
  shows "\<exists>z. xs @\<^sub>C [y] = funFLTTockl (fl @\<^sub>\<F>\<^sub>\<L> z) \<and> (\<exists>x. FL1 x \<and> (fl @\<^sub>\<F>\<^sub>\<L> z) \<in> x)"
  using assms sorry
*)

lemma some_x_then_nil_TTockl2:
  assumes "x \<in> P" "TTockl2 P"
  shows "[] \<in> P"
  using assms 
  using TTl0s_TTl2s_imp_nil TTockl0_def empty_iff by blast

lemma fl_le_TTockl2:
  assumes "fl \<le> \<langle>[{z. z \<notin> x1}]\<^sub>\<F>\<^sub>\<L>\<rangle>\<^sub>\<F>\<^sub>\<L>" "[Ref x1] \<in> P" "TTockl2 P"
  shows "funFLTTockl fl \<in> P"
  using assms apply (cases fl, auto)
  using some_x_then_nil_TTockl2 apply auto
  apply (case_tac x1a, auto)
  by (smt Collect_cong Collect_mem_eq mem_Collect_eq) 


lemma fl_le_TTockl2_Event:
  assumes "fl \<le> \<langle>(\<bullet>,(Event ev))\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>" "[REvent (Event ev)] \<in> P" "TTockl2 P"
  shows "funFLTTockl fl \<in> P"
  using assms apply (cases fl, auto)
  using some_x_then_nil_TTockl2 apply auto
  apply (case_tac x1, auto)
    apply (case_tac x21, auto)
  apply (simp_all add: less_eq_aevent_def)
   apply (case_tac x21, auto)
  by (case_tac x22, auto, case_tac x1, auto)+

lemma fl_le_TTockl2_tock:
  assumes "fl \<le> \<langle>(\<bullet>,tock)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>" "[REvent tock] \<in> P" "TTockl2 P"
  shows "funFLTTockl fl \<in> P"
  using assms apply (cases fl, auto)
  using some_x_then_nil_TTockl2 apply auto
  apply (case_tac x1, auto)
    apply (case_tac x21, auto)
    apply (simp_all add: less_eq_aevent_def)
   apply (case_tac a, auto)
  by (case_tac x22, auto, case_tac x1, auto)


lemma funFLTTockl_last_tock:
  assumes "tock \<in>\<^sub>\<F>\<^sub>\<L> last fl"
  shows "funFLTTockl (fl @\<^sub>\<F>\<^sub>\<L> \<langle>(last fl,tock)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>) = funFLTTockl fl @ funFLTTockl(\<langle>(\<bullet>,tock)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>)"
  using assms by (induct fl, auto)

end