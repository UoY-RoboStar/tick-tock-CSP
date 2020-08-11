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

text \<open> Below an attempt at breaking the definition of tt2F in concatenations. \<close>

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

definition ttproc2F :: "'a ttprocess \<Rightarrow> 'a process" where
  "ttproc2F P = ({(s,X). \<exists>y. Some (s,X) = tt2F y \<and> y \<in> P},{s. \<exists>y. s = tt2T y \<and> y \<in> P})"

lemma ttproc2F_DivC_eq_DivF:
  "ttproc2F div\<^sub>C = div\<^sub>F"
  unfolding DivTT_def DivF_def ttproc2F_def by auto 

lemma ttproc2F_SkipC_SkipUF:
  "ttproc2F SKIP\<^sub>C = Skip\<^sub>U\<^sub>F"
  unfolding SkipTT_def ttproc2F_def SkipUF_def apply auto
  by force+

lemma Some_tt2F_set:
  "Some ([], b) = tt2F [[{y. \<exists>x. y = ttevt2F x \<and> x \<in> b}]\<^sub>R]"
  apply auto
  by (metis evt.exhaust ttevent.distinct(3) ttevent.inject ttevt2F.simps(1) ttevt2F.simps(2))
  
lemma ttproc2F_StopC_eq_StopF:
  "ttproc2F STOP\<^sub>C = Stop\<^sub>F"
proof -
  text \<open> Untimed traces \<close>

  have traces:"snd Stop\<^sub>F = snd (ttproc2F STOP\<^sub>C)"
    unfolding StopTT_def ttproc2F_def StopF_def apply auto
      apply (rule exI[where x="[]"], auto)
      apply (simp add: tocks.empty_in_tocks)
    using tocks.cases tt2T.simps(3) tt2T.simps(5) apply blast
    by (metis append.simps(1) append.simps(2) tocks.simps tt2T.simps(5))

  text \<open> Untimed failures \<close>
  have failures:"fst Stop\<^sub>F = fst (ttproc2F STOP\<^sub>C)"
    unfolding StopTT_def ttproc2F_def StopF_def
  proof (auto)
    fix b
    obtain X where X:"Some ([],b) = tt2F [[X]\<^sub>R] \<and> Tock \<notin> X"
      using Some_tt2F_set tt2F_refusal_without_Tock
      by (metis (no_types, lifting) Diff_iff singletonI tt2F_refusal_without_Tock)
    then show "\<exists>y. Some ([], b) = tt2F y \<and> (\<exists>s\<in>tocks {x. x \<noteq> Tock}. y = s \<or> (\<exists>X. y = s @ [[X]\<^sub>R] \<and> Tock \<notin> X))"
      using tocks.empty_in_tocks by fastforce
  next
    fix a b s
    assume a1:"Some (a, b) = tt2F s"
      and a2:"s \<in> tocks {x. x \<noteq> Tock}"
    show "a = []"
      by (metis a1 a2 option.simps(3) tocks.cases tt2F.simps(3) tt2F.simps(8))
  next
    fix a b s X
    assume a1:"Some (a, b) = tt2F (s @ [[X]\<^sub>R])"
     and a2:"s \<in> tocks {x. x \<noteq> Tock}"
     and a3:"Tock \<notin> X"
    show "a = []"
      using a1 apply (cases s, auto)
      by (metis a2 append_Cons list.distinct(1) option.simps(3) tocks.cases tt2F.simps(8))
  qed

  show ?thesis by (simp add: failures traces prod_eq_iff)
qed

lemma ttproc2F_PrefixTT_eq_PrefixF:
  "ttproc2F (PrefixTT e P) = PrefixF e (ttproc2F P)"
  unfolding ttproc2F_def PrefixTT_def PrefixF_def 
proof (auto)
  fix a b s
  assume assm1:"Some (a, b) = tt2F s"
    and  assm2:"s \<in> tocks {x. x \<noteq> Tock \<and> x \<noteq> Event e}" 
    and  assm3: "\<forall>s. a = evt e # s \<longrightarrow> (\<forall>y. Some (s, b) = tt2F y \<longrightarrow> y \<notin> P)"
  show "a = []"
    using assm1 assm2 by (metis (mono_tags, lifting) option.simps(3) tocks.cases tt2F.simps(3) tt2F.simps(8))
next
  fix a b s
  assume assm1: "Some (a, b) = tt2F s"
    and  assm2: "s \<in> tocks {x. x \<noteq> Tock \<and> x \<noteq> Event e}" 
    and  assm3: "\<forall>s. a = evt e # s \<longrightarrow> (\<forall>y. Some (s, b) = tt2F y \<longrightarrow> y \<notin> P)"
    and  assm4: "evt e \<in> b"
  show "False"
    using assm1 assm2 assm3 assm4 by (metis (mono_tags, lifting) option.simps(3) tocks.cases tt2F.simps(3) tt2F.simps(8))
next
  fix a b s X
  assume assm1: "Some (a, b) = tt2F (s @ [[X]\<^sub>R])"
   and   assm2: "s \<in> tocks {x. x \<noteq> Tock \<and> x \<noteq> Event e}"
   and   assm3: "Tock \<notin> X" 
   and   assm4: "Event e \<notin> X" 
   and   assm5: "\<forall>s. a = evt e # s \<longrightarrow> (\<forall>y. Some (s, b) = tt2F y \<longrightarrow> y \<notin> P)"
  show "a = []"
    using assm1 assm2 by (cases s, auto, metis (mono_tags, lifting) append_Cons list.distinct(1) option.simps(3) tocks.cases tt2F.simps(8))
next
  fix a b s X
  assume assm1: "Some (a, b) = tt2F (s @ [[X]\<^sub>R])"
   and   assm2: "s \<in> tocks {x. x \<noteq> Tock \<and> x \<noteq> Event e}"
   and   assm3: "Tock \<notin> X" 
   and   assm4: "Event e \<notin> X" 
   and   assm5: "\<forall>s. a = evt e # s \<longrightarrow> (\<forall>y. Some (s, b) = tt2F y \<longrightarrow> y \<notin> P)"
   and   assm6: "evt e \<in> b"
  show "False"
    using assm1 assm2 assm3 assm4 assm6 by (cases s, auto, metis (mono_tags, lifting) append_Cons list.distinct(1) option.simps(3) tocks.cases tt2F.simps(8))
next
  fix a b s
  assume assm1: "Some (a, b) = tt2F s"
   and   assm2: "s \<in> tocks {x. x \<noteq> Tock \<and> x \<noteq> Event e}"
   and   assm3: "\<forall>s. a = evt e # s \<longrightarrow> (\<forall>y. Some (s, b) = tt2F y \<longrightarrow> y \<notin> P)"
  show "a = []"
    using assm1 assm2 by (cases s, auto, metis (mono_tags, lifting) list.distinct(1) option.simps(3) tocks.cases tt2F.simps(8))
next
  fix a b s
  assume assm1: "Some (a, b) = tt2F s"
   and   assm2: "s \<in> tocks {x. x \<noteq> Tock \<and> x \<noteq> Event e}"
   and   assm3: "\<forall>s. a = evt e # s \<longrightarrow> (\<forall>y. Some (s, b) = tt2F y \<longrightarrow> y \<notin> P)"
   and   assm4: "evt e \<in> b"
  show "False"
    using assm1 assm2 by (cases s, auto, metis (mono_tags, lifting) list.distinct(1) option.simps(3) tocks.cases tt2F.simps(8))
next
  fix a b s \<sigma>
  assume assm1: "Some (a, b) = tt2F (s @ [Event e]\<^sub>E # \<sigma>)"
   and   assm2: "s \<in> tocks {x. x \<noteq> Tock \<and> x \<noteq> Event e}"
   and   assm3: "\<sigma> \<in> P"
   and   assm4: "\<forall>s. a = evt e # s \<longrightarrow> (\<forall>y. Some (s, b) = tt2F y \<longrightarrow> y \<notin> P)"
  show "a = []"
  proof (cases s)
    case Nil
    then have "Some (a, b) = tt2F ([Event e]\<^sub>E # \<sigma>)"
      using assm1 by auto
    then obtain fl where fl:"Some (fst fl, b) = Some (evt e # fst fl,snd fl)"
      apply auto
      by (smt assm3 assm4 fst_conv not_Some_eq old.prod.exhaust option.inject option.simps(4) option.simps(5) prod.inject snd_conv)
    then have "a = evt e # fst fl"
      by auto
    then have "\<sigma> \<notin> P"
      using assm4 fl by auto
    then show ?thesis 
      using assm3 by auto
  next
    case (Cons z list)
    then show ?thesis using assm1 assm2 apply auto
      by (metis (mono_tags, lifting) append_Cons list.simps(3) option.simps(3) tocks.cases tt2F.simps(8))
  qed
next
  fix a b s \<sigma>
  assume assm1: "Some (a, b) = tt2F (s @ [Event e]\<^sub>E # \<sigma>)"
   and   assm2: "s \<in> tocks {x. x \<noteq> Tock \<and> x \<noteq> Event e}"
   and   assm3: "\<sigma> \<in> P"
   and   assm4: "\<forall>s. a = evt e # s \<longrightarrow> (\<forall>y. Some (s, b) = tt2F y \<longrightarrow> y \<notin> P)"
   and   assm5: "evt e \<in> b"
  show "False"
  proof (cases s)
    case Nil
    then have "Some (a, b) = tt2F ([Event e]\<^sub>E # \<sigma>)"
      using assm1 by auto
    then obtain fl where fl:"Some (fst fl, b) = Some (evt e # fst fl,snd fl)"
      apply auto
      by (smt assm3 assm4 fst_conv not_Some_eq old.prod.exhaust option.inject option.simps(4) option.simps(5) prod.inject snd_conv)
    then have "a = evt e # fst fl"
      by auto
    then have "\<sigma> \<notin> P"
      using assm4 fl by auto
    then show ?thesis 
      using assm3 by auto
  next
    case (Cons z list)
    then show ?thesis using assm1 assm2 apply auto
      by (metis (mono_tags, lifting) append_Cons list.simps(3) option.simps(3) tocks.cases tt2F.simps(8))
  qed
next
  fix b
  assume assm1:"evt e \<notin> b"
  obtain X where X:"Some ([], b) = tt2F [[X]\<^sub>R]"
    using Some_tt2F_set by auto
  then have "Event e \<notin> X"
    using assm1 by auto
  then show "\<exists>y. Some ([], b) = tt2F y \<and>
             ((\<exists>s\<in>tocks {x. x \<noteq> Tock \<and> x \<noteq> Event e}. y = s \<or> (\<exists>X. Tock \<notin> X \<and> Event e \<notin> X \<and> y = s @ [[X]\<^sub>R])) \<or>
              (\<exists>s\<in>tocks {x. x \<noteq> Tock \<and> x \<noteq> Event e}. y = s \<or> (\<exists>\<sigma>\<in>P. y = s @ [Event e]\<^sub>E # \<sigma>)))"
    by (metis (no_types) Diff_iff X \<open>Event e \<notin> X\<close> append.left_neutral singletonI tocks.empty_in_tocks tt2F_refusal_without_Tock)
next
  fix b s y
  assume assm1: "Some (s, b) = tt2F y"
    and  assm2: "y \<in> P"
  obtain z where z:"Some (evt e # s, b) = tt2F (z @ [Event e]\<^sub>E # y) \<and> z = []"
    using assm1
    by (smt append.left_neutral fst_conv option.simps(5) snd_conv tt2F.simps(2))
  then have "\<exists>y. Some (evt e # s, b) = tt2F y \<and> (\<exists>s\<in>tocks {x. x \<noteq> Tock \<and> x \<noteq> Event e}. (\<exists>\<sigma>\<in>P. y = s @ [Event e]\<^sub>E # \<sigma>))"
    using assm2 tocks.empty_in_tocks by blast
  then show "\<exists>y. Some (evt e # s, b) = tt2F y \<and>
           ((\<exists>s\<in>tocks {x. x \<noteq> Tock \<and> x \<noteq> Event e}. y = s \<or> (\<exists>X. Tock \<notin> X \<and> Event e \<notin> X \<and> y = s @ [[X]\<^sub>R])) \<or>
            (\<exists>s\<in>tocks {x. x \<noteq> Tock \<and> x \<noteq> Event e}. y = s \<or> (\<exists>\<sigma>\<in>P. y = s @ [Event e]\<^sub>E # \<sigma>)))"
    by blast
next   
  fix s
  assume assm1: "tt2T s \<noteq> []"
    and  assm2: "s \<in> tocks {x. x \<noteq> Tock \<and> x \<noteq> Event e}"
  have "tt2T s = []"
    using assm2 tocks.cases tt2T.simps(3) tt2T.simps(5) by blast
  then have "False"   
    using assm1 by auto
  then show "\<exists>sa. tt2T s = evt e # sa \<and> (\<exists>y. sa = tt2T y \<and> y \<in> P)"
    by auto
next
  fix s X
  assume assm1:"tt2T (s @ [[X]\<^sub>R]) \<noteq> []"
    and  assm2:"s \<in> tocks {x. x \<noteq> Tock \<and> x \<noteq> Event e}"
    and  assm3:"Tock \<notin> X" 
    and  assm4:"Event e \<notin> X"
  have "tt2T s = []"
    using assm2 tocks.cases tt2T.simps(3) tt2T.simps(5) by blast
  then have "tt2T (s @ [[X]\<^sub>R]) = []"
    by (metis (no_types, lifting) append_Cons append_eq_Cons_conv assm2 tocks.simps tt2T.simps(5))
  then have "False"
    using assm1 by auto
  then show "\<exists>sa. tt2T (s @ [[X]\<^sub>R]) = evt e # sa \<and> (\<exists>y. sa = tt2T y \<and> y \<in> P)"
    by auto
next
  fix s
  assume assm1: "tt2T s \<noteq> []"
    and  assm2: "s \<in> tocks {x. x \<noteq> Tock \<and> x \<noteq> Event e}"
  have "tt2T s = []"
    using assm2 tocks.cases tt2T.simps(3) tt2T.simps(5) by blast
  then have "False"   
    using assm1 by auto
  then show "\<exists>sa. tt2T s = evt e # sa \<and> (\<exists>y. sa = tt2T y \<and> y \<in> P)"
    by auto
next
  fix s \<sigma>
  assume assm1:"tt2T (s @ [Event e]\<^sub>E # \<sigma>) \<noteq> []"
   and   assm2:"s \<in> tocks {x. x \<noteq> Tock \<and> x \<noteq> Event e}"
   and   assm3:"\<sigma> \<in> P"
  have "tt2T s = []"
    using assm2 tocks.cases tt2T.simps(3) tt2T.simps(5) by blast
  then have "tt2T (s @ [Event e]\<^sub>E # \<sigma>) = evt e # tt2T \<sigma>"
    by (metis (mono_tags, lifting) append_Cons append_self_conv2 assm1 assm2 mem_Collect_eq tocks_def tocksp.cases tt2T.simps(2) tt2T.simps(5))
  then show "\<exists>sa. tt2T (s @ [Event e]\<^sub>E # \<sigma>) = evt e # sa \<and> (\<exists>y. sa = tt2T y \<and> y \<in> P)"
    using assm3 by auto
next
  show "\<exists>y. [] = tt2T y \<and>
        ((\<exists>s\<in>tocks {x. x \<noteq> Tock \<and> x \<noteq> Event e}. y = s \<or> (\<exists>X. Tock \<notin> X \<and> Event e \<notin> X \<and> y = s @ [[X]\<^sub>R])) \<or>
         (\<exists>s\<in>tocks {x. x \<noteq> Tock \<and> x \<noteq> Event e}. y = s \<or> (\<exists>\<sigma>\<in>P. y = s @ [Event e]\<^sub>E # \<sigma>)))"
    using tocks.empty_in_tocks by force
next
  fix y
  assume assm1: "y \<in> P"
  then show "\<exists>ya. evt e # tt2T y = tt2T ya \<and>
              ((\<exists>s\<in>tocks {x. x \<noteq> Tock \<and> x \<noteq> Event e}. ya = s \<or> (\<exists>X. Tock \<notin> X \<and> Event e \<notin> X \<and> ya = s @ [[X]\<^sub>R])) \<or>
               (\<exists>s\<in>tocks {x. x \<noteq> Tock \<and> x \<noteq> Event e}. ya = s \<or> (\<exists>\<sigma>\<in>P. ya = s @ [Event e]\<^sub>E # \<sigma>)))"
    using tocks.empty_in_tocks by force
qed

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

lemma tocks_Some_prefix_tt2F:
  assumes "x\<in>tocks P" "x \<le>\<^sub>C y" "Some (a, b) = tt2F y"
  shows "x = []"
  using assms 
  apply (induct y rule:tt2F.induct, auto) 
  using tocks.simps apply fastforce
  using tt2F_tocks_simp tt_prefix_decompose by fastforce

lemma ttproc2F_ExtChoiceTT_eq_ExtChoiceF:
  assumes TT0_P: "TT0 P"
      and TT0_Q: "TT0 Q"
      and TT1_P: "TT1 P" 
      and TT1_Q: "TT1 Q"
  shows "ttproc2F (P \<box>\<^sub>C Q) = (ttproc2F P) \<box>\<^sub>F (ttproc2F Q)"
  using assms unfolding ttproc2F_def ExtChoiceTT_def ExtChoiceF_def 
proof (auto)
  fix b \<rho> \<sigma> \<tau>
    assume  assm1:"Some ([], b) = tt2F (\<rho> @ \<sigma>)"
    and     assm2:"\<rho> \<in> tocks UNIV"
    and     assm3:"\<rho> @ \<sigma> \<in> P"
    and     assm4:"\<rho> @ \<tau> \<in> Q"
    and     assm5:"\<forall>\<rho>'\<in>tocks UNIV. \<rho>' \<le>\<^sub>C \<rho> @ \<sigma> \<longrightarrow> \<rho>' \<le>\<^sub>C \<rho>"
    and     assm6:"\<forall>\<rho>'\<in>tocks UNIV. \<rho>' \<le>\<^sub>C \<rho> @ \<tau> \<longrightarrow> \<rho>' \<le>\<^sub>C \<rho>"
    and     assm7:"\<forall>X. \<sigma> = [[X]\<^sub>R] \<longrightarrow> (\<exists>Y. \<tau> = [[Y]\<^sub>R] \<and> (\<forall>e. (e \<in> X) = (e \<in> Y) \<or> e = Tock))"
    and     assm8:"\<forall>X. \<tau> = [[X]\<^sub>R] \<longrightarrow> (\<exists>Y. \<sigma> = [[Y]\<^sub>R] \<and> (\<forall>e. (e \<in> X) = (e \<in> Y) \<or> e = Tock))"
    show "\<exists>y. tt2F (\<rho> @ \<sigma>) = tt2F y \<and> y \<in> Q"
    proof (cases "\<rho>")
      case Nil
      then have Some_b:"Some ([], b) = tt2F \<sigma>" 
        using assm1 by auto
      then obtain X where X:"\<sigma> = [[X]\<^sub>R]"
        using tt2F_some_exists by blast
      then obtain Y where Y:"\<tau> = [[Y]\<^sub>R]"
        using assm7 assm4 by auto
      then show ?thesis
        using tt2F_eq_eqsets_or_Tock
        by (metis X assm4 assm7 local.Nil self_append_conv2)
    next
      case (Cons a list)
      then show ?thesis using assm1 assm2 tt2F_tocks_simp by fastforce
    qed
next
  fix b \<rho> \<sigma> \<tau>
    assume  assm1:"Some ([], b) = tt2F (\<rho> @ \<tau>)"
    and     assm2:"\<rho> \<in> tocks UNIV"
    and     assm3:"\<rho> @ \<sigma> \<in> P"
    and     assm4:"\<rho> @ \<tau> \<in> Q"
    and     assm5:"\<forall>\<rho>'\<in>tocks UNIV. \<rho>' \<le>\<^sub>C \<rho> @ \<sigma> \<longrightarrow> \<rho>' \<le>\<^sub>C \<rho>"
    and     assm6:"\<forall>\<rho>'\<in>tocks UNIV. \<rho>' \<le>\<^sub>C \<rho> @ \<tau> \<longrightarrow> \<rho>' \<le>\<^sub>C \<rho>"
    and     assm7:"\<forall>X. \<sigma> = [[X]\<^sub>R] \<longrightarrow> (\<exists>Y. \<tau> = [[Y]\<^sub>R] \<and> (\<forall>e. (e \<in> X) = (e \<in> Y) \<or> e = Tock))"
    and     assm8:"\<forall>X. \<tau> = [[X]\<^sub>R] \<longrightarrow> (\<exists>Y. \<sigma> = [[Y]\<^sub>R] \<and> (\<forall>e. (e \<in> X) = (e \<in> Y) \<or> e = Tock))"
    show "\<exists>y. tt2F (\<rho> @ \<tau>) = tt2F y \<and> y \<in> P"
    proof (cases "\<rho>")
      case Nil
      then have Some_b:"Some ([], b) = tt2F \<tau>" 
        using assm1 by auto
      then obtain X where X:"\<tau> = [[X]\<^sub>R]"
        using tt2F_some_exists by blast
      then obtain Y where Y:"\<sigma> = [[Y]\<^sub>R]"
        using assm8 assm4 by auto
      then show ?thesis
        using tt2F_eq_eqsets_or_Tock
        by (metis X assm3 assm8 local.Nil self_append_conv2)
    next
      case (Cons a list)
      then show ?thesis using assm1 assm2 tt2F_tocks_simp by fastforce
    qed
next
  fix b y ya
  assume  assm1: "tt2F ya = tt2F y"
  and     assm2: "y \<in> P"
  and     assm3: "Some ([], b) = tt2F y"
  and     assm4: "ya \<in> Q"
  then obtain X where X:"y = [[X]\<^sub>R]"
    using tt2F_some_exists by blast
  then obtain Y where Y:"ya = [[Y]\<^sub>R]"
    by (metis assm1 assm3 tt2F_some_exists)

  obtain \<rho>::"'a ttobs list" where \<rho>:"\<rho> = []"
    by auto

  have p0:"\<rho>\<in>tocks UNIV"
    using \<rho> tocks.empty_in_tocks by blast

  have p1:"(\<forall>\<rho>'\<in>tocks UNIV. \<rho>' \<le>\<^sub>C \<rho> @ y \<longrightarrow> \<rho>' \<le>\<^sub>C \<rho>)"
    using \<rho> X refusal_notin_tocks tt_prefix_notfront_is_whole by force

  have p2:"(\<forall>\<rho>'\<in>tocks UNIV. \<rho>' \<le>\<^sub>C \<rho> @ ya \<longrightarrow> \<rho>' \<le>\<^sub>C \<rho>)"
    using \<rho> Y refusal_notin_tocks tt_prefix_notfront_is_whole by force

  have p3:"(\<forall>X. y = [[X]\<^sub>R] \<longrightarrow> (\<exists>Y. ya = [[Y]\<^sub>R] \<and> (\<forall>e. (e \<in> X) = (e \<in> Y) \<or> e = Tock)))"
  proof (cases "Tock \<in> X \<longleftrightarrow> Tock \<in> Y")
    case True
    then show ?thesis using tt2F_refusal_eq assm1 X Y by blast
  next
    case False
    then show ?thesis 
      by (metis (no_types, lifting) Diff_iff Y assm1 insert_Diff insert_iff list.inject tt2F_refusal_eq tt2F_refusal_without_Tock ttobs.inject(2))
  qed

  then have p4:"(\<forall>X. ya = [[X]\<^sub>R] \<longrightarrow> (\<exists>Y. y = [[Y]\<^sub>R] \<and> (\<forall>e. (e \<in> X) = (e \<in> Y) \<or> e = Tock)))"
    using X by auto

  then have "tt2F y = tt2F ya \<and> 
              \<rho>\<in>tocks UNIV \<and>
                \<rho> @ y \<in> P \<and> 
                  \<rho> @ ya \<in> Q \<and> 
                    (\<forall>\<rho>'\<in>tocks UNIV. \<rho>' \<le>\<^sub>C \<rho> @ y \<longrightarrow> \<rho>' \<le>\<^sub>C \<rho>) \<and>
                         (\<forall>\<rho>'\<in>tocks UNIV. \<rho>' \<le>\<^sub>C \<rho> @ ya \<longrightarrow> \<rho>' \<le>\<^sub>C \<rho>) \<and>
                         (\<forall>X. y = [[X]\<^sub>R] \<longrightarrow> (\<exists>Y. ya = [[Y]\<^sub>R] \<and> (\<forall>e. (e \<in> X) = (e \<in> Y) \<or> e = Tock))) \<and>
                         (\<forall>X. ya = [[X]\<^sub>R] \<longrightarrow> (\<exists>Y. y = [[Y]\<^sub>R] \<and> (\<forall>e. (e \<in> X) = (e \<in> Y) \<or> e = Tock))) \<and>
                         (ya = \<rho> @ y \<or> ya = \<rho> @ ya)"
      using \<rho> assm2 assm3 assm4 tt2F_tocks_simp tt_prefix_split p0 p1 p2 p3 p4
      by (simp add: assm1)

  then show "\<exists>ya. tt2F y = tt2F ya \<and>
            (\<exists>\<rho>\<in>tocks UNIV.
                \<exists>\<sigma>. \<rho> @ \<sigma> \<in> P \<and>
                    (\<exists>\<tau>. \<rho> @ \<tau> \<in> Q \<and>
                         (\<forall>\<rho>'\<in>tocks UNIV. \<rho>' \<le>\<^sub>C \<rho> @ \<sigma> \<longrightarrow> \<rho>' \<le>\<^sub>C \<rho>) \<and>
                         (\<forall>\<rho>'\<in>tocks UNIV. \<rho>' \<le>\<^sub>C \<rho> @ \<tau> \<longrightarrow> \<rho>' \<le>\<^sub>C \<rho>) \<and>
                         (\<forall>X. \<sigma> = [[X]\<^sub>R] \<longrightarrow> (\<exists>Y. \<tau> = [[Y]\<^sub>R] \<and> (\<forall>e. (e \<in> X) = (e \<in> Y) \<or> e = Tock))) \<and>
                         (\<forall>X. \<tau> = [[X]\<^sub>R] \<longrightarrow> (\<exists>Y. \<sigma> = [[Y]\<^sub>R] \<and> (\<forall>e. (e \<in> X) = (e \<in> Y) \<or> e = Tock))) \<and>
                         (ya = \<rho> @ \<sigma> \<or> ya = \<rho> @ \<tau>)))"
    by auto
next
  fix a b y
  assume  TT0_Q: "TT0 Q"
  and     assm1: "a \<noteq> []"
  and     assm2: "Some (a, b) = tt2F y"
  and     assm3: "y \<in> P"

  then have y_no_singleton_Ref: "\<forall>X. y \<noteq> [[X]\<^sub>R]"
    using assm1 assm2 by (cases y, auto)

  obtain \<sigma>::"'a ttobs list"  where \<sigma>:"\<sigma> = y"
    by auto

  obtain \<rho>::"'a ttobs list"  where \<rho>:"\<rho> = []"
    by auto  

  obtain \<tau>::"'a ttobs list"  where \<tau>:"\<tau> = []"
    by auto

  obtain ya where "ya = y"
    by auto

  have empty_trace_Q:"[] \<in> Q"
    using TT0_Q TT0_TT1_empty TT1_Q by blast

  have "(\<forall>\<rho>'\<in>tocks UNIV. \<rho>' \<le>\<^sub>C \<rho> @ \<sigma> \<longrightarrow> \<rho>' \<le>\<^sub>C \<rho>)"
    using \<sigma> \<rho> tocks_Some_prefix_tt2F assm2 by fastforce

  then have "tt2F y = tt2F y \<and>
            (\<rho>\<in>tocks UNIV \<and>
                 \<rho> @ \<sigma> \<in> P \<and>
                   (\<rho> @ \<tau> \<in> Q \<and>
                         (\<forall>\<rho>'\<in>tocks UNIV. \<rho>' \<le>\<^sub>C \<rho> @ \<sigma> \<longrightarrow> \<rho>' \<le>\<^sub>C \<rho>) \<and>
                         (\<forall>\<rho>'\<in>tocks UNIV. \<rho>' \<le>\<^sub>C \<rho> @ \<tau> \<longrightarrow> \<rho>' \<le>\<^sub>C \<rho>) \<and>
                         (\<forall>X. \<sigma> = [[X]\<^sub>R] \<longrightarrow> (\<exists>Y. \<tau> = [[Y]\<^sub>R] \<and> (\<forall>e. (e \<in> X) = (e \<in> Y) \<or> e = Tock))) \<and>
                         (\<forall>X. \<tau> = [[X]\<^sub>R] \<longrightarrow> (\<exists>Y. \<rho> = [[Y]\<^sub>R] \<and> (\<forall>e. (e \<in> X) = (e \<in> Y) \<or> e = Tock))) \<and>
                         (y = \<rho> @ \<sigma> \<or> y = \<rho> @ \<tau>)))"
    using \<sigma> \<tau> \<rho> y_no_singleton_Ref empty_trace_Q assm3 apply auto
    by (simp add: tocks.empty_in_tocks)
  
  then show "\<exists>ya. tt2F y = tt2F ya \<and>
            (\<exists>\<rho>\<in>tocks UNIV.
                \<exists>\<sigma>. \<rho> @ \<sigma> \<in> P \<and>
                    (\<exists>\<tau>. \<rho> @ \<tau> \<in> Q \<and>
                         (\<forall>\<rho>'\<in>tocks UNIV. \<rho>' \<le>\<^sub>C \<rho> @ \<sigma> \<longrightarrow> \<rho>' \<le>\<^sub>C \<rho>) \<and>
                         (\<forall>\<rho>'\<in>tocks UNIV. \<rho>' \<le>\<^sub>C \<rho> @ \<tau> \<longrightarrow> \<rho>' \<le>\<^sub>C \<rho>) \<and>
                         (\<forall>X. \<sigma> = [[X]\<^sub>R] \<longrightarrow> (\<exists>Y. \<tau> = [[Y]\<^sub>R] \<and> (\<forall>e. (e \<in> X) = (e \<in> Y) \<or> e = Tock))) \<and>
                         (\<forall>X. \<tau> = [[X]\<^sub>R] \<longrightarrow> (\<exists>Y. \<sigma> = [[Y]\<^sub>R] \<and> (\<forall>e. (e \<in> X) = (e \<in> Y) \<or> e = Tock))) \<and>
                         (ya = \<rho> @ \<sigma> \<or> ya = \<rho> @ \<tau>)))"
    using \<sigma> \<tau> by blast
next
  fix a b y
  assume  TT0_P: "TT0 P"
  and     assm1: "a \<noteq> []"
  and     assm2: "Some (a, b) = tt2F y"
  and     assm3: "y \<in> Q"

  then have y_no_singleton_Ref: "\<forall>X. y \<noteq> [[X]\<^sub>R]"
    using assm1 assm2 by (cases y, auto)

  obtain \<sigma>::"'a ttobs list"  where \<sigma>:"\<sigma> = []"
    by auto

  obtain \<rho>::"'a ttobs list"  where \<rho>:"\<rho> = []"
    by auto  

  obtain \<tau>::"'a ttobs list"  where \<tau>:"\<tau> = y"
    by auto

  obtain ya where ya:"ya = y"
    by auto

  have empty_trace_P:"[] \<in> P"
    using TT0_P TT0_TT1_empty TT1_P assms(3) by blast

  have "(\<forall>\<rho>'\<in>tocks UNIV. \<rho>' \<le>\<^sub>C \<rho> @ \<tau> \<longrightarrow> \<rho>' \<le>\<^sub>C \<rho>)"
    using \<tau> \<rho> tocks_Some_prefix_tt2F assm2 by fastforce

  then have "tt2F y = tt2F ya \<and>
            (\<rho>\<in>tocks UNIV \<and>
                 \<rho> @ \<sigma> \<in> P \<and>
                   (\<rho> @ \<tau> \<in> Q \<and>
                         (\<forall>\<rho>'\<in>tocks UNIV. \<rho>' \<le>\<^sub>C \<rho> @ \<sigma> \<longrightarrow> \<rho>' \<le>\<^sub>C \<rho>) \<and>
                         (\<forall>\<rho>'\<in>tocks UNIV. \<rho>' \<le>\<^sub>C \<rho> @ \<tau> \<longrightarrow> \<rho>' \<le>\<^sub>C \<rho>) \<and>
                         (\<forall>X. \<sigma> = [[X]\<^sub>R] \<longrightarrow> (\<exists>Y. \<tau> = [[Y]\<^sub>R] \<and> (\<forall>e. (e \<in> X) = (e \<in> Y) \<or> e = Tock))) \<and>
                         (\<forall>X. \<tau> = [[X]\<^sub>R] \<longrightarrow> (\<exists>Y. \<rho> = [[Y]\<^sub>R] \<and> (\<forall>e. (e \<in> X) = (e \<in> Y) \<or> e = Tock))) \<and>
                         (ya = \<rho> @ \<sigma> \<or> ya = \<rho> @ \<tau>)))"
    using \<sigma> \<tau> \<rho> ya y_no_singleton_Ref empty_trace_P assm3 apply auto
    by (simp add: tocks.empty_in_tocks)
  
  then show "\<exists>ya. tt2F y = tt2F ya \<and>
            (\<exists>\<rho>\<in>tocks UNIV.
                \<exists>\<sigma>. \<rho> @ \<sigma> \<in> P \<and>
                    (\<exists>\<tau>. \<rho> @ \<tau> \<in> Q \<and>
                         (\<forall>\<rho>'\<in>tocks UNIV. \<rho>' \<le>\<^sub>C \<rho> @ \<sigma> \<longrightarrow> \<rho>' \<le>\<^sub>C \<rho>) \<and>
                         (\<forall>\<rho>'\<in>tocks UNIV. \<rho>' \<le>\<^sub>C \<rho> @ \<tau> \<longrightarrow> \<rho>' \<le>\<^sub>C \<rho>) \<and>
                         (\<forall>X. \<sigma> = [[X]\<^sub>R] \<longrightarrow> (\<exists>Y. \<tau> = [[Y]\<^sub>R] \<and> (\<forall>e. (e \<in> X) = (e \<in> Y) \<or> e = Tock))) \<and>
                         (\<forall>X. \<tau> = [[X]\<^sub>R] \<longrightarrow> (\<exists>Y. \<sigma> = [[Y]\<^sub>R] \<and> (\<forall>e. (e \<in> X) = (e \<in> Y) \<or> e = Tock))) \<and>
                         (ya = \<rho> @ \<sigma> \<or> ya = \<rho> @ \<tau>)))"
    apply simp
    apply (rule_tac x="ya" in exI, auto)
    using \<rho> by blast+ (* Struggling unification here *)
next
  fix y
  assume  assm1: "y \<in> P"

  obtain \<sigma>::"'a ttobs list"  where \<sigma>:"\<sigma> = y"
    by auto

  obtain \<rho>::"'a ttobs list"  where \<rho>:"\<rho> = []"
    by auto  

  obtain \<tau>::"'a ttobs list"  where \<tau>:"\<tau> = []"
    by auto

  obtain ya where ya:"ya = y"
    by auto

  have empty_trace_Q:"[] \<in> Q"
    using TT0_Q TT0_TT1_empty TT1_Q assms(3) by blast

  have "(\<forall>\<rho>'\<in>tocks UNIV. \<rho>' \<le>\<^sub>C \<rho> @ \<tau> \<longrightarrow> \<rho>' \<le>\<^sub>C \<rho>)"
    using \<tau> \<rho> tocks_Some_prefix_tt2F assm1 by simp

  obtain exp where exp:"exp == tt2T y = tt2T ya \<and>
              (\<rho>\<in>tocks UNIV \<and>
                  \<rho> @ \<sigma> \<in> P \<and>
                      (\<rho> @ \<tau> \<in> Q \<and>
                           (\<forall>\<rho>'\<in>tocks UNIV. \<rho>' \<le>\<^sub>C \<rho> @ \<sigma> \<longrightarrow> \<rho>' \<le>\<^sub>C \<rho>) \<and>
                           (\<forall>\<rho>'\<in>tocks UNIV. \<rho>' \<le>\<^sub>C \<rho> @ \<tau> \<longrightarrow> \<rho>' \<le>\<^sub>C \<rho>) \<and>
                           (\<forall>X. \<sigma> = [[X]\<^sub>R] \<longrightarrow> (\<exists>Y. \<tau> = [[Y]\<^sub>R] \<and> (\<forall>e. (e \<in> X) = (e \<in> Y) \<or> e = Tock))) \<and>
                           (\<forall>X. \<tau> = [[X]\<^sub>R] \<longrightarrow> (\<exists>Y. \<sigma> = [[Y]\<^sub>R] \<and> (\<forall>e. (e \<in> X) = (e \<in> Y) \<or> e = Tock))) \<and>
                           (ya = \<rho> @ \<sigma> \<or> ya = \<rho> @ \<tau>)))"
    by auto

  show "\<exists>ya. tt2T y = tt2T ya \<and>
              (\<exists>\<rho>\<in>tocks UNIV.
                  \<exists>\<sigma>. \<rho> @ \<sigma> \<in> P \<and>
                      (\<exists>\<tau>. \<rho> @ \<tau> \<in> Q \<and>
                           (\<forall>\<rho>'\<in>tocks UNIV. \<rho>' \<le>\<^sub>C \<rho> @ \<sigma> \<longrightarrow> \<rho>' \<le>\<^sub>C \<rho>) \<and>
                           (\<forall>\<rho>'\<in>tocks UNIV. \<rho>' \<le>\<^sub>C \<rho> @ \<tau> \<longrightarrow> \<rho>' \<le>\<^sub>C \<rho>) \<and>
                           (\<forall>X. \<sigma> = [[X]\<^sub>R] \<longrightarrow> (\<exists>Y. \<tau> = [[Y]\<^sub>R] \<and> (\<forall>e. (e \<in> X) = (e \<in> Y) \<or> e = Tock))) \<and>
                           (\<forall>X. \<tau> = [[X]\<^sub>R] \<longrightarrow> (\<exists>Y. \<sigma> = [[Y]\<^sub>R] \<and> (\<forall>e. (e \<in> X) = (e \<in> Y) \<or> e = Tock))) \<and>
                           (ya = \<rho> @ \<sigma> \<or> ya = \<rho> @ \<tau>)))"
  proof (cases y rule:tt2T.cases)
    case 1
    then have "exp"
      using \<rho> \<sigma> \<tau> ya assm1 empty_trace_Q exp
      apply (simp add: tocks.empty_in_tocks)
      by (metis list.distinct(1) tt2T.simps(1) tt2T_tocks_simp tt_prefix_refl tt_prefix_split)
    then show ?thesis 
      using exp by auto
  next
    case (2 e \<sigma>2)
    then have y_no_singleton_Ref: "\<forall>X. y \<noteq> [[X]\<^sub>R]"
      using assm1 by (cases y, auto)
    then have "exp"
      using \<rho> \<sigma> \<tau> ya assm1 empty_trace_Q 2 exp
      apply (auto simp add: tocks.empty_in_tocks)
      by (metis list.distinct(1) tt2T.simps(2) tt2T_tocks_simp tt_prefix_refl tt_prefix_split)
    then show ?thesis 
      using exp by auto
  next
    case "3_1"
    then show ?thesis
      using assm1 empty_trace_Q tocks.empty_in_tocks by force
  next
    case ("3_2" va)
    then show ?thesis
      using TT0_P TT0_TT1_empty TT1_P empty_trace_Q tocks.empty_in_tocks by force
    next
      case ("3_3" vb va)
      then show ?thesis using TT0_P TT0_TT1_empty TT1_P empty_trace_Q tocks.empty_in_tocks by force
    next
      case ("3_4" vb vc)
      then show ?thesis using TT0_P TT0_TT1_empty TT1_P empty_trace_Q tocks.empty_in_tocks by force
    next
      case ("3_5" vb vc)
      then show ?thesis using TT0_P TT0_TT1_empty TT1_P empty_trace_Q tocks.empty_in_tocks by force
    next
      case ("3_6" va vb vc)
      then show ?thesis using TT0_P TT0_TT1_empty TT1_P empty_trace_Q tocks.empty_in_tocks by force
  qed
next
  fix y
  assume  assm1: "y \<in> Q"

  obtain \<sigma>::"'a ttobs list"  where \<sigma>:"\<sigma> = []"
    by auto

  obtain \<rho>::"'a ttobs list"  where \<rho>:"\<rho> = []"
    by auto  

  obtain \<tau>::"'a ttobs list"  where \<tau>:"\<tau> = y"
    by auto

  obtain ya where ya:"ya = y"
    by auto

  have empty_trace_P:"[] \<in> P"
    using TT0_P TT0_TT1_empty TT1_P assms(3) by blast

  have "(\<forall>\<rho>'\<in>tocks UNIV. \<rho>' \<le>\<^sub>C \<rho> @ \<sigma> \<longrightarrow> \<rho>' \<le>\<^sub>C \<rho>)"
    using \<sigma> \<rho> tocks_Some_prefix_tt2F assm1 by simp

  obtain exp where exp:"exp == tt2T y = tt2T ya \<and>
              (\<rho>\<in>tocks UNIV \<and>
                  \<rho> @ \<sigma> \<in> P \<and>
                      (\<rho> @ \<tau> \<in> Q \<and>
                           (\<forall>\<rho>'\<in>tocks UNIV. \<rho>' \<le>\<^sub>C \<rho> @ \<sigma> \<longrightarrow> \<rho>' \<le>\<^sub>C \<rho>) \<and>
                           (\<forall>\<rho>'\<in>tocks UNIV. \<rho>' \<le>\<^sub>C \<rho> @ \<tau> \<longrightarrow> \<rho>' \<le>\<^sub>C \<rho>) \<and>
                           (\<forall>X. \<sigma> = [[X]\<^sub>R] \<longrightarrow> (\<exists>Y. \<tau> = [[Y]\<^sub>R] \<and> (\<forall>e. (e \<in> X) = (e \<in> Y) \<or> e = Tock))) \<and>
                           (\<forall>X. \<tau> = [[X]\<^sub>R] \<longrightarrow> (\<exists>Y. \<sigma> = [[Y]\<^sub>R] \<and> (\<forall>e. (e \<in> X) = (e \<in> Y) \<or> e = Tock))) \<and>
                           (ya = \<rho> @ \<sigma> \<or> ya = \<rho> @ \<tau>)))"
    by auto

  show "\<exists>ya. tt2T y = tt2T ya \<and>
              (\<exists>\<rho>\<in>tocks UNIV.
                  \<exists>\<sigma>. \<rho> @ \<sigma> \<in> P \<and>
                      (\<exists>\<tau>. \<rho> @ \<tau> \<in> Q \<and>
                           (\<forall>\<rho>'\<in>tocks UNIV. \<rho>' \<le>\<^sub>C \<rho> @ \<sigma> \<longrightarrow> \<rho>' \<le>\<^sub>C \<rho>) \<and>
                           (\<forall>\<rho>'\<in>tocks UNIV. \<rho>' \<le>\<^sub>C \<rho> @ \<tau> \<longrightarrow> \<rho>' \<le>\<^sub>C \<rho>) \<and>
                           (\<forall>X. \<sigma> = [[X]\<^sub>R] \<longrightarrow> (\<exists>Y. \<tau> = [[Y]\<^sub>R] \<and> (\<forall>e. (e \<in> X) = (e \<in> Y) \<or> e = Tock))) \<and>
                           (\<forall>X. \<tau> = [[X]\<^sub>R] \<longrightarrow> (\<exists>Y. \<sigma> = [[Y]\<^sub>R] \<and> (\<forall>e. (e \<in> X) = (e \<in> Y) \<or> e = Tock))) \<and>
                           (ya = \<rho> @ \<sigma> \<or> ya = \<rho> @ \<tau>)))"
  proof (cases y rule:tt2T.cases)
    case 1
    then have "exp"
      using \<rho> \<sigma> \<tau> ya assm1 empty_trace_P exp
      apply (simp add: tocks.empty_in_tocks)
      by (metis list.distinct(1) tt2T.simps(1) tt2T_tocks_simp tt_prefix_refl tt_prefix_split)
    then show ?thesis 
      using exp by auto
  next
    case (2 e \<sigma>2)
    then have y_no_singleton_Ref: "\<forall>X. y \<noteq> [[X]\<^sub>R]"
      using assm1 by (cases y, auto)
    then have "exp"
      using \<rho> \<sigma> \<tau> ya assm1 empty_trace_P 2 exp
      apply (auto simp add: tocks.empty_in_tocks)
      by (metis list.distinct(1) tt2T.simps(2) tt2T_tocks_simp tt_prefix_refl tt_prefix_split)
    then show ?thesis 
      using exp by auto
  next
    case "3_1"
    then show ?thesis
      using assm1 empty_trace_P tocks.empty_in_tocks by force
  next
    case ("3_2" va)
    then show ?thesis
      using TT0_Q TT0_TT1_empty TT1_Q empty_trace_P tocks.empty_in_tocks by force
    next
      case ("3_3" vb va)
      then show ?thesis using TT0_Q TT0_TT1_empty TT1_Q empty_trace_P tocks.empty_in_tocks by force
    next
      case ("3_4" vb vc)
      then show ?thesis using TT0_Q TT0_TT1_empty TT1_Q empty_trace_P tocks.empty_in_tocks by force
    next
      case ("3_5" vb vc)
      then show ?thesis using TT0_Q TT0_TT1_empty TT1_Q empty_trace_P tocks.empty_in_tocks by force
    next
      case ("3_6" va vb vc)
      then show ?thesis using TT0_Q TT0_TT1_empty TT1_Q empty_trace_P tocks.empty_in_tocks by force
    qed
  qed

  thm merge_traces.cases

lemma merge_traces_imp_mergeF:
  assumes "z \<in> p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q" "None \<noteq> tt2F z" "tt2F p = None"
  shows "(tt2T p \<lbrakk>insert tick (evt ` A)\<rbrakk>\<^sup>T\<^sub>F tt2T q) = {}"
  using assms  apply (induct p A q arbitrary:z rule:merge_traces.induct, simp_all)
  apply (smt Collect_empty_eq equals0D merge_traceF.simps(2) merge_traceF.simps(3) option.simps(4) tt2F.simps(2) tt2F.simps(3))
  apply (smt Collect_empty_eq equals0D evt.distinct(1) insertI1 merge_traceF.simps(6) merge_traceF.simps(8) option.simps(4) tt2F.simps(2) tt2F.simps(3)) apply (smt insert_Diff insert_not_empty mem_Collect_eq merge_traceF.simps(2) merge_traceF.simps(3) option.simps(4))
  oops

lemma merge_traces_imp_mergeF':
  assumes "Some (a, b) = tt2F z" "tt2F p \<noteq> None" "tt2F q \<noteq> None" "z \<in> p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q"
  shows "a \<in> (tt2T p \<lbrakk>insert tick (evt ` A)\<rbrakk>\<^sup>T\<^sub>F tt2T q)"
  using assms nitpick apply (induct p A q rule:merge_traces.induct, simp_all)
          apply auto
                apply (cases a, auto)
  using assms(1) tt2F_some_exists apply blast
        apply (case_tac ac, auto)
         apply (case_tac \<sigma>, auto)
        apply (case_tac ac, auto)
  oops

lemma ttevt2F_diff_no_Tock:
  assumes "Tock \<notin> ttevt2F`Y" "Tock \<notin> ttevt2F`Z" "Y - ({tick}\<union>(evt ` A)) = Z - ({tick}\<union>(evt ` A))"
  shows "(ttevt2F`Y - ((Event`A) \<union> {Tock,Tick})) = (ttevt2F`Z - ((Event ` A) \<union> {Tock, Tick}))"
  using assms apply safe
  by (metis (no_types, lifting) Diff_subset image_eqI insert_Diff insert_Diff_if insert_iff insert_is_Un subsetD ttevt2F.simps(2) ttevt2F_evt_set)+

thm rev_induct

lemma rev_little_induct: 
  assumes "P [] []"
          "\<And>x xs ys. P (xs@[x]) ys"
          "\<And>y ys xs. P xs (ys@[y])"
          "\<And>x y xs ys. P xs ys  \<Longrightarrow> P (xs@[x]) (ys@[y])"
   shows  "P xs ys"
  using assms
  apply (induct xs arbitrary: ys)
   apply auto
   apply (simp add: rev_induct)
  by (metis rev_exhaust)

lemma ttproc2F_ExtChoiceTT_eq_ExtChoiceF:
  assumes ttWFx_P: "ttWFx P" and TT0_P: "TT0 P" and TT1_P: "TT1 P" and TT2_P: "TT2 P" and TT3_P: "TT3 P"
      and ttWFx_Q: "ttWFx Q" and TT0_Q: "TT0 Q" and TT1_Q: "TT1 Q" and TT2_Q: "TT2 Q" and TT3_Q: "TT3 Q"
  shows "fst ((ttproc2F P) \<lbrakk>A\<rbrakk>\<^sub>F (ttproc2F Q)) \<subseteq> fst (ttproc2F (P \<lbrakk>A\<rbrakk>\<^sub>C Q))" 
  using assms unfolding ttproc2F_def ParCompTT_def ParCompF_def 
proof (simp_all, safe)
  oops

lemma
  assumes "y \<in> [] \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C xs @ [x]" "xs \<noteq> []"
  shows "y \<in> [] \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C xs"
  nitpick
  oops

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
(*
lemma tt2F_None_merge_traces:
  assumes "([[Tick]\<^sub>E] \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q) \<noteq> {}"
  shows "tt2F`([[Tick]\<^sub>E] \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q) = {None}"
  using assms apply (induct q arbitrary:A rule:ttWF.induct, auto)
  oops
*)
lemma tt2F_None_merge_traces_both_None:
  assumes "(p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q) \<noteq> {}" "tt2F p = None" "tt2F q = None"
  shows "tt2F`(p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q) = {None}"
  using assms (* FIXME: ugly proof *)
  apply (induct p A q rule:merge_traces.induct, simp_all)
           apply (simp_all add:tt2F_None_merge_traces)
           apply auto[1]
            apply (smt empty_iff image_insert insertI1 insert_Diff option.case_eq_if singleton_iff tt2F_None_merge_traces)
           apply (metis (mono_tags, lifting) empty_iff imageI mem_Collect_eq option.simps(4) singletonD tt2F.simps(2) tt2F_None_merge_traces)
          apply auto[1]
           apply (metis (no_types, lifting) empty_iff insert_iff insert_image option.case_eq_if option.distinct(1))
          apply (smt equals0D image_eqI mem_Collect_eq option.case_eq_if option.simps(3) singleton_iff tt2F.simps(2))
         apply auto[1]
         apply (smt image_iff mem_Collect_eq tt2F.simps(8))
        apply auto[1]
         apply (metis (no_types, lifting) ex_in_conv insertI1 insert_image option.case_eq_if option.simps(3) singleton_iff)
        apply (metis (mono_tags, lifting) empty_iff imageI mem_Collect_eq merge_traces_comm option.simps(4) singletonD tt2F.simps(2) tt2F_None_merge_traces)
       apply auto[1]
        apply (metis (no_types, lifting) ex_in_conv insertI1 insert_image option.case_eq_if option.simps(3) singleton_iff)
       apply (smt ex_in_conv image_iff insertI1 mem_Collect_eq option.case_eq_if option.simps(3) tt2F.simps(2))
      apply auto[1]
                 apply (metis (no_types, lifting) ex_in_conv insertI1 insert_image option.case_eq_if option.simps(3) singleton_iff)
                apply (metis (no_types, lifting) ex_in_conv insertI1 insert_image option.case_eq_if option.distinct(1) singleton_iff)
               apply (metis (no_types, lifting) ex_in_conv insertI1 insert_image option.case_eq_if option.distinct(1) singleton_iff)
              apply (metis (no_types, lifting) ex_in_conv insertI1 insert_image option.case_eq_if option.distinct(1) singleton_iff)
             apply (metis (no_types, lifting) ex_in_conv insertI1 insert_image option.case_eq_if option.distinct(1) singleton_iff)
            apply (metis (no_types, lifting) ex_in_conv insertI1 insert_image option.case_eq_if option.distinct(1) singleton_iff)
           apply (metis (no_types, lifting) ex_in_conv insertI1 insert_image option.case_eq_if option.distinct(1) singleton_iff)
          apply (smt ex_in_conv image_iff insertI1 mem_Collect_eq option.case_eq_if option.simps(3) tt2F.simps(2))
         apply (smt ex_in_conv image_iff insertI1 mem_Collect_eq option.case_eq_if option.simps(3) tt2F.simps(2))
        apply (smt ex_in_conv image_iff insertI1 mem_Collect_eq option.case_eq_if option.simps(3) tt2F.simps(2))
       apply (smt ex_in_conv image_iff insertI1 mem_Collect_eq option.case_eq_if option.simps(3) tt2F.simps(2))
      apply (smt ex_in_conv image_iff insertI1 mem_Collect_eq option.case_eq_if option.simps(3) tt2F.simps(2))
     apply auto[1]
      apply (metis (no_types, lifting) ex_in_conv insertI1 insert_image option.case_eq_if option.distinct(1) singleton_iff)
     apply (smt ex_in_conv image_iff insertI1 mem_Collect_eq option.case_eq_if option.simps(3) tt2F.simps(2))
       apply auto[1]
    apply (smt image_iff mem_Collect_eq tt2F.simps(8))
       apply auto[1]
      apply (metis (no_types, lifting) ex_in_conv insertI1 insert_image option.case_eq_if option.distinct(1) singleton_iff)
   apply (smt ex_in_conv image_iff insertI1 mem_Collect_eq option.case_eq_if option.simps(3) tt2F.simps(2))
  apply safe
  apply simp
  by (metis (mono_tags, lifting) imageI mem_Collect_eq tt2F.simps(8))  

lemma tt2F_None_merge_traces_last_no_Tick:
  assumes "(p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q) \<noteq> {}" "tt2F p = None" "last p \<noteq> [Tick]\<^sub>E"
  shows "tt2F`(p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q) = {None}"
  using assms  (* FIXME: ugly proof *)
  apply (induct p A q rule:merge_traces.induct, simp_all add:image_def tt2F_None_merge_traces', safe, simp_all add:image_def , safe)

                      apply (metis (no_types, lifting) merge_traces_comm option.case_eq_if option.simps(3) tt2F_None_merge_traces')

  using merge_traces_comm tt2F_None_merge_traces' apply fastforce
                      apply (smt insert_absorb mem_Collect_eq option.case_eq_if option.collapse option.distinct(1) option.simps(15) set_empty_eq these_empty_eq these_insert_Some tt2F_None_merge_traces')
 (* possibly true *)
  sorry

lemma
  assumes "y \<in> p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q" "None \<noteq> tt2F q" "[Tick]\<^sub>E \<notin> set p" "[Tick]\<^sub>E \<notin> set q"
  shows "tt2T y \<in> (tt2T p) \<lbrakk>insert tick (evt ` A)\<rbrakk>\<^sup>T\<^sub>F (tt2T q)"
  nitpick

lemma ttproc2F_ExtChoiceTT_eq_ExtChoiceF:
  assumes ttWFx_P: "ttWFx P" and TT0_P: "TT0 P" and TT1_P: "TT1 P" and TT2_P: "TT2 P" and TT3_P: "TT3 P"
      and ttWFx_Q: "ttWFx Q" and TT0_Q: "TT0 Q" and TT1_Q: "TT1 Q" and TT2_Q: "TT2 Q" and TT3_Q: "TT3 Q"
  shows "fst (ttproc2F (P \<lbrakk>A\<rbrakk>\<^sub>C Q)) \<subseteq> fst ((ttproc2F P) \<lbrakk>A\<rbrakk>\<^sub>F (ttproc2F Q))" 
  using assms unfolding ttproc2F_def ParCompTT_def ParCompF_def 
proof (auto)
fix a b y p q
  assume  assm1:"\<forall>s t. a \<in> s \<lbrakk>insert tick (evt ` A)\<rbrakk>\<^sup>T\<^sub>F t \<longrightarrow>
             (\<forall>y. t @ [tick] = tt2T y \<longrightarrow> y \<notin> Q) \<or> (\<forall>y. Some (s, b) = tt2F y \<longrightarrow> y \<notin> P)"
    and   assm2:"\<forall>s t. a \<in> s \<lbrakk>insert tick (evt ` A)\<rbrakk>\<^sup>T\<^sub>F t \<longrightarrow>
             (\<forall>y. s @ [tick] = tt2T y \<longrightarrow> y \<notin> P) \<or> (\<forall>y. Some (t, b) = tt2F y \<longrightarrow> y \<notin> Q)"
    and   assm3:"Some (a, b) = tt2F y"
    and   assm4:"y \<in> p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q"
    and   assm5:"p \<in> P"
    and   assm6:"q \<in> Q"

  have a_tt2T:"a = tt2T y"
    using assm3 Some_tt2F_imp_tt2T by auto

  have "\<exists>Y Z. b = Y \<union> Z \<and>
             Y - insert tick (evt ` A) = Z - insert tick (evt ` A) \<and>
             (\<exists>s. (Some (s, Y) = tt2F p \<and> p \<in> P) \<and>
                  (\<exists>t. (Some (t, Z) = tt2F q \<and> q \<in> Q) \<and> a \<in> s \<lbrakk>insert tick (evt ` A)\<rbrakk>\<^sup>T\<^sub>F t))"
  proof (cases "tt2F p = None")
    case tt2F_p_None:True
    then show ?thesis
    proof (cases "tt2F q = None")
      case True
      then have "tt2F`(p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q) = {None}"
          using assm3 assm4 tt2F_p_None tt2F_None_merge_traces_both_None by fastforce
      then have "tt2F y = None"
        using assm4 by blast
      then show ?thesis 
        using assm3 by auto
    next
      case tt2F_q_None:False
      then show ?thesis 
      proof (cases "last p = [Tick]\<^sub>E") (* FIXME: need to use assm1/assm2 to contradict *)
        case True
        then show ?thesis sorry
      next
        case False
        then have "tt2F`(p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q) = {None}"
          using tt2F_q_None  
          by (metis assm4 insert_not_empty mk_disjoint_insert tt2F_None_merge_traces_last_no_Tick tt2F_p_None)
        then have "tt2F y = None"
          using assm4 by blast
        then show ?thesis 
          using assm3 by auto
      qed
    qed
  next
    case False
    then obtain s Y where sY:"Some (s, Y) = tt2F p"
      by auto

    then show ?thesis
    proof (cases "tt2F q = None")
      case True
      then show ?thesis sorry
    next
      case False
      then obtain t Z where sY:"Some (t, Z) = tt2F q"
        by auto
(*    FIXME: need to show the following whenever tt2F p and tt2F q are not None.
       then have "b = Y \<union> Z \<and> Y - insert tick (evt ` A) = Z - insert tick (evt ` A)"
        oops *)
      then show ?thesis sorry
    qed
  qed
  oops

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

lemma tt2F_last_refusal:
  assumes "Some (s, Y) = tt2F y" "ttWF y"
  shows "\<exists>R. last y = [R]\<^sub>R \<and> Y = {x. ttevt2F x \<in> R}"
  using assms apply (induct y arbitrary: Y s rule:rev_induct, auto)
  apply (case_tac x, auto)
  oops

lemma tt2F_ending_Event_eq_None:
  "tt2F (xs @ [[Event e]\<^sub>E]) = None"
  apply (induct xs, auto)
  by (metis list.exhaust rotate1.simps(2) rotate1_is_Nil_conv tt2F.simps(8) tt2F_ev_neq_None ttobs.exhaust)

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

lemma Some_tt2F_imp_tt2T:
  assumes "Some (a, b) = tt2F y"
  shows "tt2T y = a"
  using assms apply (induct a y arbitrary:b rule:list_induct2', auto)
  using tt2F_some_exists tt2T.simps(5) apply blast
  apply (case_tac ya, auto, case_tac x1, auto)
    apply (metis (mono_tags, lifting) Pair_inject list.inject option.case_eq_if option.inject option.simps(3))
   apply (smt Pair_inject list.inject option.case_eq_if option.collapse option.inject option.simps(3) prod.collapse)
  by (metis neq_Nil_conv not_Some_eq option.inject prod.inject tt2F.simps(1) tt2F.simps(8))

lemma
  assumes "ttWF ys" "tt2T (ys@[[RP]\<^sub>R]) = []" "tt2F ys \<noteq> None"
  shows "ys = []"
  nitpick

lemma ttproc2F_ExtChoiceTT_eq_ExtChoiceF:
  assumes ttWF_P: "TTwf P" and TT0_P: "TT0 P" and TT1_P: "TT1 P" and TT2_P: "TT2 P" and TT3_P: "TT3 P"
      and ttWF_Q: "TTwf Q" and TT0_Q: "TT0 Q" and TT1_Q: "TT1 Q" and TT2_Q: "TT2 Q" and TT3_Q: "TT3 Q"
  shows "fst ((ttproc2F P) \<lbrakk>A\<rbrakk>\<^sub>F (ttproc2F Q)) \<subseteq>  fst (ttproc2F (P \<lbrakk>A\<rbrakk>\<^sub>C Q))" 
  using assms unfolding ttproc2F_def ParCompTT_def ParCompF_def 
proof (simp_all, safe)
  fix a b Y Z s y t ya
  assume assm1:"Y - insert tick (evt ` A) = Z - insert tick (evt ` A)"
  and    assm2:"Some (s, Y) = tt2F y"
  and    assm3:"y \<in> P"
  and    assm4:"a \<in> s \<lbrakk>insert tick (evt ` A)\<rbrakk>\<^sup>T\<^sub>F t"
  and    assm5:"Some (t, Z) = tt2F ya"
  and    assm6:"ya \<in> Q"
  obtain X where X:"X = insert tick (evt ` A)"
    by auto

  have s_tt2T:"s = tt2T y"
              "t = tt2T ya"
    using assm2 Some_tt2F_imp_tt2T apply auto
    using assm5 Some_tt2F_imp_tt2T by auto

  have "ttWF y"
    using assm3 ttWF_P TTwf_def by blast
  then obtain ys RP where ysR:"y = ys@[[RP]\<^sub>R] \<and> Y = {x. ttevt2F x \<in> RP} \<and> tt2T ys = s"
    using assm2 assm3 some_tt2F_ref_trace by blast

  (* The failure is (tt2T(ys),Y), where 's' is the trace in the Failures model. *)

  have "ttWF ya"
    using assm6 ttWF_Q TTwf_def by blast
  then obtain zs RQ where ysR:"ya = zs@[[RQ]\<^sub>R] \<and> Z = {x. ttevt2F x \<in> RQ} \<and> tt2T zs = t"
    using assm5 assm6 some_tt2F_ref_trace by blast

  have s_tt2T_y:"s = tt2T y"
    using assm2 Some_tt2F_imp_tt2T by blast

  have t_tt2T_ya:"t = tt2T ya"
    using assm5 Some_tt2F_imp_tt2T by blast

  show "\<exists>y. Some (a, Y \<union> Z) = tt2F y \<and> (\<exists>x. (\<exists>p\<in>P. \<exists>q\<in>Q. x = p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q) \<and> y \<in> x)"
    using assm1 assm2 assm3 assm4 assm5 assm6 s_tt2T_y t_tt2T_ya X s_tt2T

  proof (induct s X t rule:merge_traceF.induct)
    case (1 X)
 (*   then have "ys=[]"
      using ysR assm2   
    then have "\<exists>z. z \<in> y \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C ya \<and> Some (a, Y \<union> Z) = tt2F z"
*)
    then show ?case sledgehammer
  next
    case (2 x X s)
    then show ?case sorry
  next
    case (3 x X s)
    then show ?case sorry
  next
    case (4 x s X)
    then show ?case sorry
  next
    case (5 y X y' s t)
    then show ?case sorry
  next
    case (6 x X y s t)
    then show ?case sorry
  next
  case (7 y X x t s)
    then show ?case sorry
  next
  case (8 x X x' s t)
    then show ?case sorry
  next
  case (9 x X s t)
    then show ?case sorry
  qed
    oops

(* old below *)
lemma ttproc2F_ExtChoiceTT_eq_ExtChoiceF:
  assumes ttWFx_P: "ttWFx P" and TT0_P: "TT0 P" and TT1_P: "TT1 P" and TT2_P: "TT2 P" and TT3_P: "TT3 P"
      and ttWFx_Q: "ttWFx Q" and TT0_Q: "TT0 Q" and TT1_Q: "TT1 Q" and TT2_Q: "TT2 Q" and TT3_Q: "TT3 Q"
  shows "fst ((ttproc2F P) \<lbrakk>A\<rbrakk>\<^sub>F (ttproc2F Q)) \<subseteq> fst (ttproc2F (P \<lbrakk>A\<rbrakk>\<^sub>C Q))" 
  using assms unfolding ttproc2F_def ParCompTT_def ParCompF_def 
proof (safe, simp_all)
  fix a b y p q
  assume assm1:"\<forall>s t. a \<in> s \<lbrakk>insert tick (evt ` A)\<rbrakk>\<^sup>T\<^sub>F t \<longrightarrow>
             (\<forall>y. t @ [tick] = tt2T y \<longrightarrow> y \<notin> Q) \<or> (\<forall>y. Some (s, b) = tt2F y \<longrightarrow> y \<notin> P)"
    and   assm2:"\<forall>s t. a \<in> s \<lbrakk>insert tick (evt ` A)\<rbrakk>\<^sup>T\<^sub>F t \<longrightarrow>
             (\<forall>y. s @ [tick] = tt2T y \<longrightarrow> y \<notin> P) \<or> (\<forall>y. Some (t, b) = tt2F y \<longrightarrow> y \<notin> Q)"
    and   assm3:"Some (a, b) = tt2F y"
    and   assm4:"y \<in> p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q"
    and   assm5:"p \<in> P"
    and   assm6:"q \<in> Q"

  obtain l where l:"l = (p,A,q)"
    by auto

  obtain G where G:"G = insert tick (evt ` A)"
    by auto

  thm merge_traces.induct
  thm merge_traces.cases
  thm ttWF2.induct
  have "\<exists>Y Z. b = Y \<union> Z \<and>
             Y - insert tick (evt ` A) = Z - insert tick (evt ` A) \<and>
             (\<exists>s. (Some (s, Y) = tt2F p \<and> p \<in> P) \<and>
                  (\<exists>t. (Some (t, Z) = tt2F q \<and> q \<in> Q) \<and> a \<in> s \<lbrakk>insert tick (evt ` A)\<rbrakk>\<^sup>T\<^sub>F t))"

  proof (cases y rule:tt2F.cases)
    case (1 X)
    then show ?thesis 
      using  assm3 assm4 assm5 assm6
    (*proof (induct p A q rule:merge_traces.induct, simp_all, safe)*)
      sorry
  next
    case evs:(2 e r)
    then show ?thesis 
    using assm1 assm2 assm3 assm4 assm5 assm6
    proof (induct p A q rule:merge_traces.induct)
case (1 Z)
  then show ?case sorry
next
  case (2 Z Y)
  then show ?case sorry
next
  case (3 Z)
  then show ?case sorry
next
  case (4 Z f \<sigma>)
  then show ?case sorry
next
  case (5 Z Y \<sigma>)
  then show ?case sorry
next
  case (6 X Z)
  then show ?case sorry
next
  case (7 X Z Y)
  then show ?case sorry
next
  case (8 X Z)
  then show ?case sorry
next
  case (9 X Z f \<sigma>)
  then show ?case sorry
next
  case (10 X Z Y \<sigma>)
  then show ?case sorry
next
  case (11 Z)
  then show ?case sorry
next
  case (12 Z Y)
  then show ?case sorry
next
  case (13 Z)
  then show ?case sorry
next
  case (14 Z f \<sigma>)
  then show ?case using evs apply auto sorry
next
  case (15 Z Y \<sigma>)
  then show ?case sorry
next
  case (16 e \<sigma> Z)
  then show ?case sorry
next
  case (17 e \<sigma> Z Y)
  then show ?case sorry
next
  case (18 e \<sigma> Z)
  then show ?case sorry
next
case (19 e \<rho> Z f \<sigma>)
  then show ?case sorry
next
  case (20 e \<rho> Z Y \<sigma>)
  then show ?case sorry
next
  case (21 X \<sigma> Z)
  then show ?case sorry
next
  case (22 X \<sigma> Z Y)
  then show ?case sorry
next
  case (23 X \<sigma> Z)
  then show ?case sorry
next
  case (24 X \<rho> Z f \<sigma>)
  then show ?case sorry
next
  case (25 X \<rho> Z Y \<sigma>)
  then show ?case sorry
next
  case (26 X \<rho> Z \<sigma>)
  then show ?case sorry
next
  case (27 X e \<rho> Z \<sigma>)
  then show ?case sorry
next
  case (28 X Y \<rho> Z \<sigma>)
  then show ?case sorry
next
  case (29 \<rho> Z X \<sigma>)
  then show ?case sorry
next
  case (30 \<rho> Z X e \<sigma>)
  then show ?case sorry
next
  case (31 \<rho> Z X Y \<sigma>)
  then show ?case sorry
next
  case (32 x \<rho> Z \<sigma>)
  then show ?case sorry
next
  case (33 \<rho> Z y \<sigma>)
  then show ?case sorry
next
  case (34 \<rho> Z \<sigma>)
  then show ?case sorry
next
  case (35 \<rho> Z \<sigma>)
  then show ?case sorry
qed
  
qed
  next
    case "3_1"
    then show ?thesis using assm1 assm2 assm3 assm4 assm5 assm6 by auto
  next
    case ("3_2" va)
    then show ?thesis using assm1 assm2 assm3 assm4 assm5 assm6 by auto
  next
    case ("3_3" va)
    then show ?thesis using assm1 assm2 assm3 assm4 assm5 assm6 by auto
  next
    case ("3_4" vb vc)
    then show ?thesis using assm1 assm2 assm3 assm4 assm5 assm6 by auto
  next
    case ("3_5" vb vc)
    then show ?thesis using assm1 assm2 assm3 assm4 assm5 assm6 by auto
  next
    case ("3_6" va vb vc)
    then show ?thesis using assm1 assm2 assm3 assm4 assm5 assm6 by auto
  qed
    apply auto
    apply (induct p q rule:ttWF2.induct, simp_all, safe)
             apply (induct q rule:ttWF.induct, safe)
apply (induct q rule:ttWF.induct, simp_all, safe)
  (*  apply (cases l rule:merge_traces.cases, auto)
    apply (case_tac s rule:tt2F.cases, simp_all) *)
  proof (induct p A q  rule:merge_traces.induct)
    case (1 Z)
    then show ?case by auto
  next
    case (2 Z Y)
    then show ?case by auto
  next
    case (3 Z)
    then show ?case by auto
  next
    case (4 Z f \<sigma>)
      then show ?case
      proof(cases y)
        case Nil
        then show ?thesis using 4 by auto
      next
        case (Cons e s) (* f \<notin> Z \<and> (\<exists> s. s \<in> merge_traces [] Z \<sigma> \<and> t = [Event f]\<^sub>E # s) *)
        then have "s \<in> merge_traces [] Z \<sigma>"
                  "e = [Event f]\<^sub>E"
                  "f \<notin> Z"
          using 4 by auto+
        then obtain rs where rs:"a = evt f # rs"
          using Cons 4 apply auto
          
        then show ?thesis using Cons 4 apply auto
          apply (cases s rule:tt2F.cases, auto)
          apply (cases \<sigma> rule:ttWF.cases, auto)
          
          apply (cases \<sigma>, auto, case_tac aa, auto, case_tac x1, auto)
          
          apply (cases s, auto, case_tac aa, auto)
          apply (case_tac "\<sigma> \<in> Q", auto)
           sorry
      qed
        sorry
  next
    case (5 Z Y \<sigma>)
    then show ?case by auto
  next
    case (6 X Z)
    then show ?case by auto
  next
    case (7 X Z Y)
    then show ?case sorry
  next
    case (8 X Z)
    then show ?case sorry
  next
    case (9 X Z f \<sigma>)
    then show ?case sorry
  next
    case (10 X Z Y \<sigma>)
    then show ?case by auto
  next
    case (11 Z)
    then show ?case by auto
  next
    case (12 Z Y)
    then show ?case sorry
  next
    case (13 Z)
    then show ?case by auto
  next
    case (14 Z f \<sigma>)
    then show ?case sorry
  next
    case (15 Z Y \<sigma>)
    then show ?case by auto
  next
    case (16 e \<sigma> Z)
    then show ?case sorry
  next
    case (17 e \<sigma> Z Y)
    then show ?case sorry
  next
    case (18 e \<sigma> Z)
    then show ?case sorry
  next
    case (19 e \<rho> Z f \<sigma>)
    then show ?case sorry
  next
    case (20 e \<rho> Z Y \<sigma>)
    then show ?case sorry
  next
    case (21 X \<sigma> Z)
    then show ?case by auto
  next
    case (22 X \<sigma> Z Y)
    then show ?case by auto
  next
    case (23 X \<sigma> Z)
    then show ?case by auto
  next
    case (24 X \<rho> Z f \<sigma>)
    then show ?case sorry
  next
    case (25 X \<rho> Z Y \<sigma>)
    then show ?case 
      by (metis ex_in_conv insertI1 merge_traceF.simps(1) merge_traces_imp_mergeF option.simps(3) tt2F.simps(8) tt2T.simps(5))
  next
    case (26 X \<rho> Z \<sigma>)
    then show ?case by auto
  next
    case (27 X e \<rho> Z \<sigma>)
    then show ?case by auto
  next
    case (28 X Y \<rho> Z \<sigma>)
    then show ?case by auto
  next
    case (29 \<rho> Z X \<sigma>)
    then show ?case by auto
  next
    case (30 \<rho> Z X e \<sigma>)
    then show ?case by auto
  next
    case (31 \<rho> Z X Y \<sigma>)
    then show ?case by auto
  next
    case (32 x \<rho> Z \<sigma>)
    then show ?case by auto
  next
    case (33 \<rho> Z y \<sigma>)
    then show ?case by auto
  next
    case (34 \<rho> Z \<sigma>)
    then show ?case by auto
  next
    case (35 \<rho> Z \<sigma>)
    then show ?case by auto
  qed
next
  fix a Y Z s t
  assume assm1:"Y - insert tick (evt ` A) = Z - insert tick (evt ` A)"
  and    assm2:"\<exists>y. Some (s, Y) = tt2F y \<and> y \<in> P"
  and    assm3:"\<exists>y. Some (t, Z) = tt2F y \<and> y \<in> Q"
  and    assm4:"a \<in> s \<lbrakk>insert tick (evt ` A)\<rbrakk>\<^sup>T\<^sub>F t"

  obtain X where X:"X = insert tick (evt ` A)"
    by auto
 
  show "\<exists>y. Some (a, Y \<union> Z) = tt2F y \<and> (\<exists>x. (\<exists>p\<in>P. \<exists>q\<in>Q. x = p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q) \<and> y \<in> x)"
    using assm1 assm2 assm3 assm4 X proof (induct s X t rule:merge_traceF.induct)
    case (1 X)
      then obtain Yp where Yp: "tt2F [[Yp]\<^sub>R] = Some ([], Y) \<and> [[Yp]\<^sub>R] \<in> P \<and> Tock \<notin> Yp"
        using tt2F_some_exists 1
        by (metis Diff_iff TT1_P TT1_subset_single_ref singletonI tt2F_refusal_without_Tock)
  
      then have "ttevt2F ` Y = Yp"
        apply auto
        by (smt Some_tt2F_set Yp list.inject mem_Collect_eq setcompr_eq_image tt2F_refusal_eq ttobs.inject(2))
  
      then obtain Yq where Yq: "tt2F [[Yq]\<^sub>R] = Some ([], Z) \<and> [[Yq]\<^sub>R] \<in> Q \<and> Tock \<notin> Yq"
        using tt2F_some_exists 1
        by (metis Diff_iff TT1_Q TT1_subset_single_ref singletonI tt2F_refusal_without_Tock)
  
      then have "ttevt2F ` Z = Yq"
        apply auto
        by (smt Some_tt2F_set Yq list.inject mem_Collect_eq setcompr_eq_image tt2F_refusal_eq ttobs.inject(2))
  
      have ttevt2F_eqs:
           "ttevt2F`{tick}  = {Tick}"
           "ttevt2F`evt ` A = (Event`A)"
        apply auto
        by (simp add: ttevt2F_evt_set)
      have "(Yp - ((Event`A) \<union> {Tock,Tick})) = (Yp - ((Event`A) \<union> {Tick}))"
        using Yp by auto
      then have "(Yp - ((Event`A) \<union> {Tock,Tick})) = (Yp - ttevt2F`({tick}\<union>evt`A))"
        using ttevt2F_eqs by auto
  
      have "(Yq - ((Event`A) \<union> {Tock,Tick})) = (Yq - ((Event`A) \<union> {Tick}))"
        using Yq by auto
      then have "(Yq - ((Event`A) \<union> {Tock,Tick})) = (Yq - ttevt2F`({tick}\<union>evt`A))"
        using ttevt2F_eqs by auto
  
      have "Y - ({tick} \<union> (evt ` A)) = Z - ({tick} \<union> (evt ` A))"
        using assm1 by auto
      then have Yp_diff:"(Yp - ((Event`A) \<union> {Tick})) = (Yq - ((Event`A) \<union> {Tick}))"
        using assm1 ttevt2F_diff_no_Tock Yp Yq
        by (metis \<open>Yp - (Event ` A \<union> {Tock, Tick}) = Yp - (Event ` A \<union> {Tick})\<close> \<open>Yq - (Event ` A \<union> {Tock, Tick}) = Yq - (Event ` A \<union> {Tick})\<close> \<open>ttevt2F ` Y = Yp\<close> \<open>ttevt2F ` Z = Yq\<close>)
  
      have "[[Yp]\<^sub>R] \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C [[Yq]\<^sub>R] 
            = 
            {t. \<exists> W. W \<subseteq> Yp \<union> Yq \<and> (Yp-((Event`A) \<union> {Tock,Tick})) = (Yq - ((Event ` A) \<union> {Tock, Tick})) \<and> t = [[W]\<^sub>R]}"
        by auto
      then have "[[Yp \<union> Yq]\<^sub>R] \<in> [[Yp]\<^sub>R] \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C [[Yq]\<^sub>R]"
        using Yp_diff by auto
      have "Some (a, Y \<union> Z) = tt2F [[Yp \<union> Yq]\<^sub>R]"
        using Yp Yq assm4 1 by auto
      then have "\<exists>y. Some (a, Y \<union> Z) = tt2F y \<and> (\<exists>x. (\<exists>p\<in>P. \<exists>q\<in>Q. x = p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q) \<and> y \<in> x)"
        using Yp Yq \<open>[[Yp \<union> Yq]\<^sub>R] \<in> [[Yp]\<^sub>R] \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C [[Yq]\<^sub>R]\<close> by blast
  
      then show ?case using 1 by auto
    next
      case (2 x X s)
      then show ?case by auto
    next
      case (3 x X s)
      then show ?case sorry
    next
      case (4 x s X)
      then show ?case sorry
    next
      case (5 y X y' s t)
      then show ?case sorry
    next
      case (6 x X y s t)
      then show ?case sorry
    next
      case (7 y X x t s)
      then show ?case sorry
    next
      case (8 x X x' s t)
      then show ?case by auto
    next
      case (9 x X s t)
      then show ?case sorry
    qed
next
  fix a b s t
  assume assm1:"a \<in> s \<lbrakk>insert tick (evt ` A)\<rbrakk>\<^sup>T\<^sub>F t"
  and    assm2:"\<exists>y. s @ [tick] = tt2T y \<and> y \<in> P"
  and    assm3:"\<exists>y. Some (t, b) = tt2F y \<and> y \<in> Q"
  show "\<exists>y. Some (a, b) = tt2F y \<and> (\<exists>x. (\<exists>p\<in>P. \<exists>q\<in>Q. x = p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q) \<and> y \<in> x)"
    sorry
next
  fix a b s t
  assume assm1:"a \<in> s \<lbrakk>insert tick (evt ` A)\<rbrakk>\<^sup>T\<^sub>F t"
  and    assm2:"\<exists>y. t @ [tick] = tt2T y \<and> y \<in> Q"
  and    assm3:"\<exists>y. Some (s, b) = tt2F y \<and> y \<in> P"

  obtain X where X:"X = insert tick (evt ` A)"
    by auto

  show "\<exists>y. Some (a, b) = tt2F y \<and> (\<exists>x. (\<exists>p\<in>P. \<exists>q\<in>Q. x = p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q) \<and> y \<in> x)"
    using assm1 assm2 assm3  apply (induct s X t rule:merge_traceF.induct, auto)
    sledgehammer
    sorry
next
  fix y p q
  assume assm1:"y \<in> p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q"
  and    assm2:"p \<in> P"
  and    assm3:"q \<in> Q"
  show "\<exists>x. (\<exists>s t. x = s \<lbrakk>insert tick (evt ` A)\<rbrakk>\<^sup>T\<^sub>F t \<and> (\<exists>y. s = tt2T y \<and> y \<in> P) \<and> (\<exists>y. t = tt2T y \<and> y \<in> Q)) \<and> tt2T y \<in> x"
    using assm1 assm2 assm3  apply (induct p _ q rule:merge_traces.induct, simp_all, safe)
                        apply fastforce
                        apply fastforce
    using TT0_Q TT0_TT1_empty TT1_Q apply fastforce


    sorry
next
  fix x s t
  assume assm1:"x \<in> s \<lbrakk>insert tick (evt ` A)\<rbrakk>\<^sup>T\<^sub>F t"
  and    assm2:"\<exists>y. s = tt2T y \<and> y \<in> P"
  and    assm3:"\<exists>y. t = tt2T y \<and> y \<in> Q"
  
  obtain X where X:"X = insert tick (evt ` A)"
    by auto
  
  show "\<exists>y. x = tt2T y \<and> (\<exists>x. (\<exists>p\<in>P. \<exists>q\<in>Q. x = p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q) \<and> y \<in> x)"
    using assm1 assm2 assm3 apply (induct s X t rule:merge_traceF.induct, auto)
           apply (metis TT0_P TT0_Q TT0_TT1_empty TT1_P TT1_Q insertI1 merge_traces.simps(1) tt2T.simps(3))
    sledgehammer
    sorry
qed


end