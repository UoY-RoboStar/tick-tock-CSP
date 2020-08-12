theory Failures_TickTock

imports
  Failures_BasicOps
  TickTock.TickTock
begin

text \<open> In calculating the failures, we drop tock events, both in the trace
       and the refusals? We could still include it as part of the refusals
       considering it as a regular event.. but that's probably unnecessary? \<close>

primrec ttevt2F :: "'e evt \<Rightarrow> 'e ttevent" where
"ttevt2F (evt a) = Event a" |
"ttevt2F tick = Tick"

lemma
  "ttevt2F`(A \<union> B) = ttevt2F`A \<union> ttevt2F`B"
  by auto

lemma ttevt2F_evt_set:
  "ttevt2F`evt ` A = (Event`A)"
  by (auto simp add: image_iff)

fun tt2T :: "'a tttrace \<Rightarrow> 'a trace" where
"tt2T [[Tick]\<^sub>E] = [tick]" |
"tt2T ([Event e]\<^sub>E # \<sigma>) = evt e # tt2T \<sigma>" |
"tt2T \<sigma> = []"

lemma tt2T_tocks_simp [simp]:
  assumes "\<rho> \<in> tocks P" "\<rho> \<noteq> []"
  shows "tt2T (\<rho> @ \<sigma>) = []"
  using assms 
  using tocks.simps by fastforce

lemma tt2T_empty_concat [simp]:
  assumes "\<rho> = []"
  shows "tt2T (\<rho> @ \<sigma>) = tt2T \<sigma>"
  using assms by auto

fun tt2F :: "'a tttrace \<Rightarrow> 'a failure option" where
"tt2F [[X]\<^sub>R] = Some ([],{x. ttevt2F x \<in> X})" |
"tt2F ([Event e]\<^sub>E # \<sigma>) = (case (tt2F \<sigma>) of (Some fl) \<Rightarrow> Some (evt e # fst fl,snd fl) | None \<Rightarrow> None)" |
"tt2F \<sigma> = None"

text \<open> Below is an attempt at breaking the definition of tt2F in concatenations. \<close>

fun tt2Fconcat :: "'a failure option \<Rightarrow> 'a failure option \<Rightarrow> 'a failure option" (infix "@\<^sub>F" 56) where
"None @\<^sub>F x = None" |
"x @\<^sub>F None = None" |
"(Some fl1) @\<^sub>F (Some fl2) = Some (fst fl1 @ fst fl2,snd fl2)"

lemma tt2F_Event_dist_tt2Fconcat:
  "tt2F ([Event x1]\<^sub>E # x) = Some([evt x1],Z) @\<^sub>F tt2F(x)"
  apply (induct x rule:tt2F.induct, auto)
  by (simp add: option.case_eq_if)

lemma tt2Fconcat_assoc:
  "x @\<^sub>F (y @\<^sub>F z) = (x @\<^sub>F y) @\<^sub>F z"
  apply (induct x, auto)
  apply (induct y, auto)
  by (induct z, auto)
 
lemma tt2F_ev_neq_None:
  assumes "tt2F ([ev]\<^sub>E # x) \<noteq> None"
  shows "tt2F x \<noteq> None"
  using assms 
  apply (cases ev, auto)
  by (smt option.exhaust option.simps(4) surj_pair)

lemma tt2F_dist_tt2Fcontact:
  assumes "set x \<inter> {[X]\<^sub>R | X. True} = {}" "(tt2F x) \<noteq> None" "ttWF(x@y)"
  shows "tt2F (x@y) = (tt2F x) @\<^sub>F (tt2F y)"
  using assms
  proof (induct x)
    case Nil
    then show ?case by auto
  next
    case (Cons a x)
    then show ?case
    proof (cases a)
      case (ObsEvent ev)
      then have "tt2F x \<noteq> None"
        using Cons.prems(2) tt2F_ev_neq_None by blast
      then have tt2F_xy:"tt2F (x @ y) = tt2F x @\<^sub>F tt2F y"
        using Cons ObsEvent
        by (smt Cons.hyps Cons.prems Cons.prems(2) Set.is_empty_def append_Cons empty_set insert_disjoint(1) is_empty_set list.inject list.simps(15) null_rec(1) ttWF.elims(2) ttWF.simps(1) ttobs.distinct(1))

      then show ?thesis
      proof (cases ev)
        case (Event x1)
        then obtain Z where "tt2F ([Event x1]\<^sub>E # (x @ y)) = Some([evt x1],Z) @\<^sub>F tt2F(x @ y)"      
            using tt2F_Event_dist_tt2Fconcat by force
        then have "Some([evt x1],Z) @\<^sub>F tt2F(x @ y) = Some([evt x1],Z) @\<^sub>F ((tt2F x) @\<^sub>F (tt2F y))"
          using tt2F_xy by simp
        then show ?thesis
        proof (cases "tt2F x = None")
          case True
          then show ?thesis 
            using Event ObsEvent tt2F_xy by auto
        next
          case False
          then show ?thesis
            by (metis Cons_eq_appendI Event ObsEvent tt2F_Event_dist_tt2Fconcat tt2F_xy tt2Fconcat_assoc)
        qed
      next
        case Tock
        then show ?thesis 
          using Cons.prems(2) ObsEvent by auto
      next
        case Tick
        then show ?thesis 
          by (metis Cons.prems(2) Nil_is_append_conv ObsEvent append_Cons list.exhaust tt2F.simps(3) tt2F.simps(5) tt2Fconcat.simps(1) ttWF.simps(10))
        qed
    next
      case (Ref x2)
      then show ?thesis
        using Cons.prems(1) by auto
    qed
  qed

lemma tt2F_refusal_eq:
  assumes "tt2F [[X]\<^sub>R] = tt2F [[Y]\<^sub>R]" "Tock \<in> X \<longleftrightarrow> Tock \<in> Y"
  shows "[[X]\<^sub>R] = [[Y]\<^sub>R]"
  using assms apply auto
  by (metis mem_Collect_eq ttevent.exhaust ttevt2F.simps(1) ttevt2F.simps(2))+

lemma tt2F_eq_eqsets_or_Tock:
  assumes "(\<forall>e. (e \<in> X) = (e \<in> Y) \<or> e = Tock)"
  shows "tt2F [[X]\<^sub>R] = tt2F [[Y]\<^sub>R]"
  using assms apply auto
  by (metis evt.exhaust ttevent.distinct(1) ttevent.distinct(5) ttevt2F.simps(1) ttevt2F.simps(2))+

lemma tt2F_some_exists:
  assumes "Some ([], b) = tt2F \<sigma>" 
  shows "\<exists>X. \<sigma> = [[X]\<^sub>R]"
  using assms apply (cases \<sigma> rule:tt2F.cases, auto)
  by (metis (no_types, lifting) Pair_inject list.simps(3) not_Some_eq option.case(1) option.inject option.simps(5))

lemma tt2F_tocks_simp [simp]:
  assumes "\<rho> \<in> tocks P" "\<rho> \<noteq> []"
  shows "tt2F (\<rho> @ \<sigma>) = None"
  using assms 
  using tocks.simps by fastforce

lemma tt2F_refusal_without_Tock: "tt2F [[X]\<^sub>R] = tt2F [[X-{Tock}]\<^sub>R]"
  apply auto
  by (metis evt.exhaust ttevent.distinct(1) ttevent.distinct(5) ttevt2F.simps(1) ttevt2F.simps(2))

lemma tt2F_refusal_no_Tock: "tt2F [[X\<union>{Tock}]\<^sub>R] = tt2F [[X]\<^sub>R]"
  apply auto
  by (metis evt.exhaust ttevent.distinct(1) ttevent.distinct(5) ttevt2F.simps(1) ttevt2F.simps(2))

text \<open> The function mapping tick-tock processes to failures is then defined as follows. \<close>

definition ttproc2F :: "'a ttprocess \<Rightarrow> 'a process" where
  "ttproc2F P = ({(s,X). \<exists>y. Some (s,X) = tt2F y \<and> y \<in> P},{s. \<exists>y. s = tt2T y \<and> y \<in> P})"


lemma Some_tt2F_set:
  "Some ([], b) = tt2F [[{y. \<exists>x. y = ttevt2F x \<and> x \<in> b}]\<^sub>R]"
  apply auto
  by (metis evt.exhaust ttevent.distinct(3) ttevent.inject ttevt2F.simps(1) ttevt2F.simps(2))
  
lemma TT1_subset_single_ref:
  assumes "TT1 P" "[[X]\<^sub>R] \<in> P"
  shows "[[X-Y]\<^sub>R] \<in> P"
proof -
  have "X-Y \<subseteq> X" by auto

  then have "[[X-Y]\<^sub>R] \<lesssim>\<^sub>C [[X]\<^sub>R]"
    by auto

  then show ?thesis
    using assms unfolding TT1_def by blast
qed

lemma
  shows "tt2T ([Event x]\<^sub>E # ys) = (tt2T [[Event x]\<^sub>E]) @ (tt2T ys)"
  by auto

lemma Some_tt2F_imp_tt2T:
  assumes "Some (a, b) = tt2F y"
  shows "tt2T y = a"
  using assms apply (induct a y arbitrary:b rule:list_induct2', auto)
  using tt2F_some_exists tt2T.simps(5) apply blast
  apply (case_tac ya, auto, case_tac x1, auto)
    apply (metis (mono_tags, lifting) Pair_inject list.inject option.case_eq_if option.inject option.simps(3))
   apply (smt Pair_inject list.inject option.case_eq_if option.collapse option.inject option.simps(3) prod.collapse)
  by (metis neq_Nil_conv not_Some_eq option.inject prod.inject tt2F.simps(1) tt2F.simps(8))

lemma tt2F_None_merge_traces:
  assumes "([] \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q) \<noteq> {}"
  shows "tt2F`([] \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q) = {None}"
  using assms apply (induct q arbitrary:A rule:ttWF.induct, auto)
  apply (metis (no_types, lifting) Set.set_insert equals0D image_insert insertI1 option.case_eq_if singletonD)
  by (metis (mono_tags, lifting) equals0D image_eqI mem_Collect_eq option.simps(4) singleton_iff tt2F.simps(2))

lemma tt2F_None_merge_traces':
  assumes "y \<in> ([] \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q)"
  shows "tt2F y = None"
  using assms tt2F_None_merge_traces by blast

lemma tt2F_ending_Event_eq_None:
  "tt2F (xs @ [[Event e]\<^sub>E]) = None"
  apply (induct xs, auto)
  by (metis list.exhaust rotate1.simps(2) rotate1_is_Nil_conv tt2F.simps(8) tt2F_ev_neq_None ttobs.exhaust)

lemma ttWF_tt2F_last_refusal_concat:
  assumes "ttWF (xs@[[R]\<^sub>R])" "[Tock]\<^sub>E \<notin> set xs"
  shows "tt2F (xs@[[R]\<^sub>R]) = Some(tt2T xs,{x. ttevt2F x \<in> R})"
  using assms apply (induct xs, auto)
  apply (case_tac a, auto, case_tac x1, auto)
  using ttWF.elims(2) apply auto[1]
  by (smt append_eq_append_conv2 list.distinct(1) list.inject list.set_intros(1) same_append_eq ttWF.elims(2) tt_prefix.elims(2) tt_prefix_concat ttobs.distinct(1))

lemma Some_tt2F_no_Tock:
  assumes "Some (s, Y) = tt2F y"
  shows "[Tock]\<^sub>E \<notin> set y"
  using assms apply(induct y arbitrary:s Y, auto)
  apply (case_tac a, auto)
  apply (smt option.collapse option.simps(4) prod.collapse tt2F.simps(2) tt2F.simps(4) tt2F.simps(5) ttevent.exhaust)
  by (metis list.set_cases option.distinct(1) tt2F.simps(8))

lemma Some_tt2F_no_Tick:
  assumes "Some (s, Y) = tt2F y"
  shows "[Tick]\<^sub>E \<notin> set y"
  using assms apply(induct y arbitrary:s Y, auto)
  apply (case_tac a, auto)
  apply (smt option.collapse option.simps(4) prod.collapse tt2F.simps(2) tt2F.simps(4) tt2F.simps(5) ttevent.exhaust)
  by (metis list.set_cases option.distinct(1) tt2F.simps(8))

lemma some_tt2F_ref_trace:
  assumes "Some (s, Y) = tt2F y" "ttWF y"
  shows "\<exists>ys R. y = ys@[[R]\<^sub>R] \<and> Y = {x. ttevt2F x \<in> R} \<and> tt2T ys = s"
  using assms
proof (induct y rule:rev_induct)
  case Nil
  then show ?case by auto
next
  case (snoc x xs)
  then show ?case
  proof (cases x)
    case (ObsEvent ev)
    then show ?thesis 
    proof (cases ev)
      case (Event x1)
      then have "tt2F (xs @ [x]) = None"
        using ObsEvent snoc
        by (simp add: tt2F_ending_Event_eq_None)
      then show ?thesis
        using snoc.prems(1) by auto
    next
      case Tock
      then show ?thesis 
        using ObsEvent Some_tt2F_no_Tock snoc.prems(1) by fastforce
    next
      case Tick
      then show ?thesis
        using ObsEvent Some_tt2F_no_Tick snoc.prems(1) by fastforce
    qed
  next
    case (Ref x2)
    then have "[Tock]\<^sub>E \<notin> set xs"
      by (metis Some_tt2F_no_Tock Un_iff set_append snoc.prems(1))
    then show ?thesis using ttWF_tt2F_last_refusal_concat assms
      by (metis Ref old.prod.inject option.inject snoc.prems(1) snoc.prems(2)) 
  qed
qed

lemma Some_tt2F_imp_tt2T':
  assumes "Some (a, b) = tt2F y"
  shows "tt2T y = a"
  using assms apply (induct a y arbitrary:b rule:list_induct2', auto)
  using tt2F_some_exists tt2T.simps(5) apply blast
  apply (case_tac ya, auto, case_tac x1, auto)
    apply (metis (mono_tags, lifting) Pair_inject list.inject option.case_eq_if option.inject option.simps(3))
   apply (smt Pair_inject list.inject option.case_eq_if option.collapse option.inject option.simps(3) prod.collapse)
  by (metis neq_Nil_conv not_Some_eq option.inject prod.inject tt2F.simps(1) tt2F.simps(8))

lemma tocks_Some_prefix_tt2F:
  assumes "x\<in>tocks P" "x \<le>\<^sub>C y" "Some (a, b) = tt2F y"
  shows "x = []"
  using assms 
  apply (induct y rule:tt2F.induct, auto) 
  using tocks.simps apply fastforce
  using tt2F_tocks_simp tt_prefix_decompose by fastforce

end