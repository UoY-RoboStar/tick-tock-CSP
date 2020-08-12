theory Failures_TickTock_BasicOps

imports
  Failures_TickTock
begin

lemma ttproc2F_DivC_eq_DivF:
  "ttproc2F div\<^sub>C = div\<^sub>F"
  unfolding DivTT_def DivF_def ttproc2F_def by auto 

lemma ttproc2F_SkipC_SkipUF:
  "ttproc2F SKIP\<^sub>C = Skip\<^sub>U\<^sub>F"
  unfolding SkipTT_def ttproc2F_def SkipUF_def apply auto
  by force+

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

end