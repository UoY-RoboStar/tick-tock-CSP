theory Failures_TickTock_ParComp

imports
  Failures_TickTock
begin

lemma ttevt2F_diff_no_Tock:
  assumes "Tock \<notin> ttevt2F`Y" "Tock \<notin> ttevt2F`Z" "Y - ({tick}\<union>(evt ` A)) = Z - ({tick}\<union>(evt ` A))"
  shows "(ttevt2F`Y - ((Event`A) \<union> {Tock,Tick})) = (ttevt2F`Z - ((Event ` A) \<union> {Tock, Tick}))"
  using assms apply safe
  by (metis (no_types, lifting) Diff_subset image_eqI insert_Diff insert_Diff_if insert_iff insert_is_Un subsetD ttevt2F.simps(2) ttevt2F_evt_set)+

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

lemma evt_notin_image [intro]:
  assumes "f \<notin> A"
  shows "evt f \<notin> insert tick (evt ` A)"
  using assms by auto

lemma constrained_eq_F2tt:
  "{x. ttevt2F x \<in> Xa} - insert tick (evt ` A) = {x. ttevt2F x \<in> Ya} - insert tick (evt ` A) \<Longrightarrow>
    {e \<in> Ya. e \<noteq> Tock \<and> e \<noteq> Tick \<and> e \<notin> Event ` A} = {e \<in> Xa. e \<noteq> Tock \<and> e \<noteq> Tick \<and> e \<notin> Event ` A}"
proof -
  assume assm: "{x. ttevt2F x \<in> Xa} - insert tick (evt ` A) = {x. ttevt2F x \<in> Ya} - insert tick (evt ` A)"
  have subset1: "{e \<in> Ya. e \<noteq> Tock \<and> e \<noteq> Tick \<and> e \<notin> Event ` A} \<subseteq> {e \<in> Xa. e \<noteq> Tock \<and> e \<noteq> Tick \<and> e \<notin> Event ` A}"
  proof (auto, case_tac x, auto)
    fix x1
    assume "Event x1 \<in> Ya" "Event x1 \<notin> Event ` A"
    then have "evt x1 \<in> {x. ttevt2F x \<in> Xa} - insert tick (evt ` A)"
      using assm by auto
    then show "Event x1 \<in> Xa"
      by auto
  qed
  have subset2: "{e \<in> Xa. e \<noteq> Tock \<and> e \<noteq> Tick \<and> e \<notin> Event ` A} \<subseteq> {e \<in> Ya. e \<noteq> Tock \<and> e \<noteq> Tick \<and> e \<notin> Event ` A}"
  proof (auto, case_tac x, auto)
    fix x1
    assume "Event x1 \<in> Xa" "Event x1 \<notin> Event ` A"
    then have "evt x1 \<in> {x. ttevt2F x \<in> Ya} - insert tick (evt ` A)"
      using assm by (metis Diff_iff evt_notin_image imageI mem_Collect_eq ttevt2F.simps(1)) 
    then show "Event x1 \<in> Ya"
      by auto
  qed
  show "{e \<in> Ya. e \<noteq> Tock \<and> e \<noteq> Tick \<and> e \<notin> Event ` A} = {e \<in> Xa. e \<noteq> Tock \<and> e \<noteq> Tick \<and> e \<notin> Event ` A}"
    using subset1 subset2 by auto
qed

lemma ttevt2F_refusals_eq_implies_nontock_refusals_eq:
  "{x. ttevt2F x \<in> X} = {x. ttevt2F x \<in> Y} \<Longrightarrow> {e\<in>X. e \<noteq> Tock} = {e\<in>Y. e \<noteq> Tock}"
  by (auto, (metis mem_Collect_eq ttevent.exhaust ttevt2F.simps(1) ttevt2F.simps(2))+)

lemma ttproc2F_ParCompTT_eq_ParCompF_trace1:
  "\<And> x y t a. ttWF x \<Longrightarrow> ttWF y \<Longrightarrow> X - insert tick (evt ` A) = Y - insert tick (evt ` A) \<Longrightarrow>
      Some (s, X) = tt2F x \<Longrightarrow> Some (t, Y) = tt2F y \<Longrightarrow> a \<in> s \<lbrakk>insert tick (evt ` A)\<rbrakk>\<^sup>T\<^sub>F t \<Longrightarrow> 
    \<exists>z. z \<in> (x \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C y) \<and> Some (a, X \<union> Y) = tt2F z"
proof (induct s, simp_all)
  fix t
  show "\<And>x y a. ttWF x \<Longrightarrow> ttWF y \<Longrightarrow> X - insert tick (evt ` A) = Y - insert tick (evt ` A) \<Longrightarrow>
       Some ([], X) = tt2F x \<Longrightarrow> Some (t, Y) = tt2F y \<Longrightarrow> a \<in> [] \<lbrakk>insert tick (evt ` A)\<rbrakk>\<^sup>T\<^sub>F t \<Longrightarrow>
        \<exists>z. z \<in> (x \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C y) \<and> Some (a, X \<union> Y) = tt2F z"
  proof (induct t, simp_all)
    fix x y a
    assume case_assms: "X - insert tick (evt ` A) = Y - insert tick (evt ` A)" "Some ([], X) = tt2F x" "Some ([], Y) = tt2F y"
    obtain Xa Ya where 
      X_def: "X = {x. ttevt2F x \<in> Xa}" and 
      Y_def: "Y = {x. ttevt2F x \<in> Ya}" and
      x_def: "x = [[Xa]\<^sub>R]" and
      y_def: "y = [[Ya]\<^sub>R]"
      by (metis (mono_tags, lifting) Pair_inject case_assms(2) case_assms(3) option.inject tt2F.simps(1) tt2F_some_exists)

    have Ya_Xa_eq: "{e \<in> Ya. e \<noteq> Tock \<and> e \<noteq> Tick \<and> e \<notin> Event ` A} = {e \<in> Xa. e \<noteq> Tock \<and> e \<noteq> Tick \<and> e \<notin> Event ` A}"
      using X_def Y_def case_assms(1) constrained_eq_F2tt by blast
      
    show "\<exists>z. z \<in> (x \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C y) \<and> Some ([], X \<union> Y) = tt2F z"
      using x_def y_def X_def Y_def apply (rule_tac x="[[Xa \<union> Ya]\<^sub>R]" in exI, auto)
        using Ya_Xa_eq apply blast
        using Ya_Xa_eq apply blast
      done
  next
    fix t a aa x y
    assume ind_hyp: "(\<And>xa y a. ttWF xa \<Longrightarrow> ttWF y \<Longrightarrow> tt2F x = tt2F xa \<Longrightarrow> Some (t, Y) = tt2F y \<Longrightarrow>
      a \<in> [] \<lbrakk>insert tick (evt ` A)\<rbrakk>\<^sup>T\<^sub>F t \<Longrightarrow> \<exists>z. z \<in> (xa \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C y) \<and> Some (a, X \<union> Y) = tt2F z)"

    assume case_assms: "ttWF x" "ttWF y" "X - insert tick (evt ` A) = Y - insert tick (evt ` A)"
      "Some ([], X) = tt2F x" "Some (a # t, Y) = tt2F y" "aa \<in> [] \<lbrakk>insert tick (evt ` A)\<rbrakk>\<^sup>T\<^sub>F a # t"

    show "\<exists>z. z \<in> (x \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C y) \<and> Some (aa, X \<union> Y) = tt2F z"
    proof (cases a)
      assume a_tick: "a = tick"
      
      obtain y' where y'_assms: "y = [Tick]\<^sub>E # y' \<and> Some (t, Y) = tt2F y' \<and> ttWF y'"
        using case_assms(1) case_assms(5) a_tick by (cases y rule:ttWF.cases, auto, case_tac "tt2F \<sigma>", auto)
      obtain aa' where aa'_assms: "aa = tick # aa' \<and> aa' \<in> [] \<lbrakk>insert tick (evt ` A)\<rbrakk>\<^sup>T\<^sub>F t"
        using a_tick case_assms(6) by auto

      obtain z where "z \<in> (x \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C y') \<and> Some (aa', X \<union> Y) = tt2F z"
        using aa'_assms case_assms(1) ind_hyp y'_assms by blast
      then show "\<exists>z. z \<in> (x \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C y) \<and> Some (aa, X \<union> Y) = tt2F z"
        apply (rule_tac x="[Tick]\<^sub>E # z" in exI, auto)
        using case_assms(5) y'_assms by auto
    next
      fix x2
      assume a_evt: "a = evt x2"

      obtain y' where y'_assms: "y = [Event x2]\<^sub>E # y' \<and> Some (t, Y) = tt2F y' \<and> ttWF y'"
        using case_assms(2) case_assms(5) a_evt by (cases y rule:ttWF.cases, auto, case_tac "tt2F \<sigma>", auto, fastforce)
      obtain aa' where aa'_assms: "aa = evt x2 # aa' \<and> aa' \<in> [] \<lbrakk>insert tick (evt ` A)\<rbrakk>\<^sup>T\<^sub>F t"
        using a_evt case_assms(6) apply auto
        by (smt empty_iff mem_Collect_eq merge_traceF.simps(2) merge_traceF.simps(3))

      have x2_notin_A: "x2 \<notin> A"
        using a_evt case_assms(6) by auto

      obtain z where "z \<in> (x \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C y') \<and> Some (aa', X \<union> Y) = tt2F z"
        using aa'_assms case_assms(1) ind_hyp y'_assms by blast
      then show "\<exists>z. z \<in> (x \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C y) \<and> Some (aa, X \<union> Y) = tt2F z"
        apply (rule_tac x="[Event x2]\<^sub>E # z" in exI, auto)
        using case_assms(4) y'_assms x2_notin_A apply auto
         apply (cases x rule:ttWF.cases, auto)
        apply (cases x rule:ttWF.cases, auto)
        apply (smt aa'_assms fst_conv option.simps(5) snd_conv)
        using Some_tt2F_imp_tt2T' case_assms(4) by fastforce
    qed
  qed
next
  fix t
  show "\<And>a s x y aa. (\<And>x y t a. ttWF x \<Longrightarrow> ttWF y \<Longrightarrow> Some (s, X) = tt2F x \<Longrightarrow> Some (t, Y) = tt2F y \<Longrightarrow>
      a \<in> s \<lbrakk>insert tick (evt ` A)\<rbrakk>\<^sup>T\<^sub>F t \<Longrightarrow> \<exists>z. z \<in> (x \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C y) \<and> Some (a, X \<union> Y) = tt2F z) \<Longrightarrow>
    ttWF x \<Longrightarrow> ttWF y \<Longrightarrow> X - insert tick (evt ` A) = Y - insert tick (evt ` A) \<Longrightarrow>
    Some (a # s, X) = tt2F x \<Longrightarrow> Some (t, Y) = tt2F y \<Longrightarrow> aa \<in> a # s \<lbrakk>insert tick (evt ` A)\<rbrakk>\<^sup>T\<^sub>F t \<Longrightarrow>
      \<exists>z. z \<in> (x \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C y) \<and> Some (aa, X \<union> Y) = tt2F z"
  proof (induct t, simp_all)
    fix a s x y aa
    assume ind_hyp: "\<And>x y t a. ttWF x \<Longrightarrow> ttWF y \<Longrightarrow> Some (s, X) = tt2F x \<Longrightarrow> Some (t, Y) = tt2F y \<Longrightarrow>
      a \<in> s \<lbrakk>insert tick (evt ` A)\<rbrakk>\<^sup>T\<^sub>F t \<Longrightarrow> \<exists>z. z \<in> (x \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C y) \<and> Some (a, X \<union> Y) = tt2F z"
    
    assume case_assms: "ttWF x" "ttWF y" "X - insert tick (evt ` A) = Y - insert tick (evt ` A)"
      "Some (a # s, X) = tt2F x" "Some ([], Y) = tt2F y" "aa \<in> [] \<lbrakk>insert tick (evt ` A)\<rbrakk>\<^sup>T\<^sub>F a # s"

    show "\<exists>z. z \<in> (x \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C y) \<and> Some (aa, X \<union> Y) = tt2F z"
    proof (cases a)
      assume a_tick: "a = tick"
      
      obtain x' where x'_assms: "x = [Tick]\<^sub>E # x' \<and> Some (t, Y) = tt2F x' \<and> ttWF x'"
        using case_assms(1) case_assms(4) a_tick by (cases x rule:ttWF.cases, auto, case_tac "tt2F \<sigma>", auto)
      obtain aa' where aa'_assms: "aa = tick # aa' \<and> aa' \<in> [] \<lbrakk>insert tick (evt ` A)\<rbrakk>\<^sup>T\<^sub>F t"
        using a_tick case_assms(6) by auto

      obtain z where "z \<in> (x' \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C y) \<and> Some (aa', X \<union> Y) = tt2F z"
        using case_assms(4) x'_assms by auto
      then show "\<exists>z. z \<in> (x \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C y) \<and> Some (aa, X \<union> Y) = tt2F z"
        apply (rule_tac x="[Tick]\<^sub>E # z" in exI, auto)
        using case_assms(4) x'_assms by auto
    next
      fix x2
      assume a_evt: "a = evt x2"

      obtain x' where x'_assms: "x = [Event x2]\<^sub>E # x' \<and> Some (s, X) = tt2F x' \<and> ttWF x'"
        using case_assms(1) case_assms(4) a_evt by (cases x rule:ttWF.cases, auto, case_tac "tt2F \<sigma>", auto, fastforce)
      obtain aa' where aa'_assms: "aa = evt x2 # aa' \<and> aa' \<in> [] \<lbrakk>insert tick (evt ` A)\<rbrakk>\<^sup>T\<^sub>F s"
        using a_evt case_assms(6) apply auto
        by (smt empty_iff mem_Collect_eq merge_traceF.simps(2) merge_traceF.simps(3))

      have x2_notin_A: "x2 \<notin> A"
        using a_evt case_assms(6) by auto

      obtain z where "z \<in> (x' \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C y) \<and> Some (aa', X \<union> Y) = tt2F z"
        using aa'_assms case_assms(2) case_assms(5) ind_hyp merge_traceF_comm x'_assms by blast
      then show "\<exists>z. z \<in> (x \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C y) \<and> Some (aa, X \<union> Y) = tt2F z"
        apply (rule_tac x="[Event x2]\<^sub>E # z" in exI, auto)
        using case_assms(5) x'_assms x2_notin_A apply auto
         apply (cases y rule:ttWF.cases, auto)
        apply (cases y rule:ttWF.cases, auto)
        apply (smt aa'_assms fst_conv option.simps(5) snd_conv)
        using Some_tt2F_imp_tt2T' case_assms(5) by fastforce
    qed
  next
    fix a t aa s x y aaa
    assume ind_hyp: "(\<And>a s x y aa. (\<And>x y t a. ttWF x \<Longrightarrow> ttWF y \<Longrightarrow> Some (s, X) = tt2F x \<Longrightarrow> Some (t, Y) = tt2F y \<Longrightarrow>
        a \<in> s \<lbrakk>insert tick (evt ` A)\<rbrakk>\<^sup>T\<^sub>F t \<Longrightarrow> \<exists>z. z \<in> (x \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C y) \<and> Some (a, X \<union> Y) = tt2F z) \<Longrightarrow>
      ttWF x \<Longrightarrow> ttWF y \<Longrightarrow> Some (a # s, X) = tt2F x \<Longrightarrow> Some (t, Y) = tt2F y \<Longrightarrow>
      aa \<in> a # s \<lbrakk>insert tick (evt ` A)\<rbrakk>\<^sup>T\<^sub>F t \<Longrightarrow> \<exists>z. z \<in> (x \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C y) \<and> Some (aa, X \<union> Y) = tt2F z)"
    assume ind_hyp': "\<And>x y t a. ttWF x \<Longrightarrow> ttWF y \<Longrightarrow> Some (s, X) = tt2F x \<Longrightarrow> Some (t, Y) = tt2F y \<Longrightarrow>
      a \<in> s \<lbrakk>insert tick (evt ` A)\<rbrakk>\<^sup>T\<^sub>F t \<Longrightarrow> \<exists>z. z \<in> (x \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C y) \<and> Some (a, X \<union> Y) = tt2F z"

    assume case_assms: "ttWF x" "ttWF y" "X - insert tick (evt ` A) = Y - insert tick (evt ` A)"
      "Some (aa # s, X) = tt2F x" "Some (a # t, Y) = tt2F y" "aaa \<in> aa # s \<lbrakk>insert tick (evt ` A)\<rbrakk>\<^sup>T\<^sub>F a # t"

    have a_aa_cases:
      "(aa \<notin> insert tick (evt ` A) \<and> a \<notin> insert tick (evt ` A))
      \<or> (aa \<in> insert tick (evt ` A) \<and> a \<notin> insert tick (evt ` A))
      \<or> (aa \<notin> insert tick (evt ` A) \<and> a \<in> insert tick (evt ` A))
      \<or> (aa \<in> insert tick (evt ` A) \<and> a \<in> insert tick (evt ` A))"
      by auto
    then show "\<exists>z. z \<in> (x \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C y) \<and> Some (aaa, X \<union> Y) = tt2F z"
    proof (auto)
      assume a_tick: "a = tick"
      assume aa_tick: "aa = tick"

      have x_Tick: "x = [[Tick]\<^sub>E] \<and> s = []"
        using case_assms(1) case_assms(4) aa_tick by (cases x rule:ttWF.cases, auto, case_tac "tt2F \<sigma>", auto)
      have y_Tick: "y = [[Tick]\<^sub>E] \<and> t = []"
        using case_assms(2) case_assms(5) a_tick by (cases y rule:ttWF.cases, auto, case_tac "tt2F \<sigma>", auto)

      have aaa_Tick: "aaa = [tick]"
        using case_assms(5) y_Tick by auto

      show "\<exists>z. z \<in> (x \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C y) \<and> Some (aaa, X \<union> Y) = tt2F z"
        using aaa_Tick x_Tick y_Tick case_assms(5) by auto
    next
      assume aa_nontick: "aa \<noteq> tick" 
      assume aa_notin_evt_A: "aa \<notin> evt ` A"
      assume a_nontick: "a \<noteq> tick"
      assume a_notin_evt_A: "a \<notin> evt ` A"

      then obtain aaa' where "(aaa = a # aaa' \<and> aaa' \<in> aa # s \<lbrakk>insert tick (evt ` A)\<rbrakk>\<^sup>T\<^sub>F t) \<or> (aaa = aa # aaa' \<and> aaa' \<in> s \<lbrakk>insert tick (evt ` A)\<rbrakk>\<^sup>T\<^sub>F a # t)"
        using case_assms(6) aa_nontick aa_notin_evt_A a_nontick a_notin_evt_A by (cases aaa, auto)
      then show "\<exists>z. z \<in> (x \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C y) \<and> Some (aaa, X \<union> Y) = tt2F z"
      proof auto
        assume case_assms2: "aaa' \<in> s \<lbrakk>insert tick (evt ` A)\<rbrakk>\<^sup>T\<^sub>F a # t" "aaa = aa # aaa'"

        obtain e1 where aa_evt: "aa = evt e1 \<and> e1 \<notin> A"
          by (metis aa_nontick aa_notin_evt_A evt.exhaust imageI)

        obtain x' where x'_assms: "x = [Event e1]\<^sub>E # x' \<and> Some (s, X) = tt2F x' \<and> ttWF x'"
          using case_assms(1) case_assms(4) aa_evt by (cases x rule:ttWF.cases, auto, case_tac "tt2F \<sigma>", auto, fastforce)

        obtain z where "z \<in> (x' \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C y) \<and> Some (aaa', X \<union> Y) = tt2F z"
          using case_assms(2) case_assms(5) case_assms2(1) ind_hyp' x'_assms by blast
        then show "\<exists>z. z \<in> (x \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C y) \<and> Some (aa # aaa', X \<union> Y) = tt2F z"
          apply (rule_tac x="[Event e1]\<^sub>E # z" in exI, auto simp add: x'_assms case_assms2 aa_evt)
           apply (cases y rule:ttWF.cases, auto simp add: aa_evt)
           apply (cases "tt2F z", auto)
          done
      next
        assume case_assms2: "aaa' \<in> aa # s \<lbrakk>insert tick (evt ` A)\<rbrakk>\<^sup>T\<^sub>F t" "aaa = a # aaa'"

        obtain e1 where a_evt: "a = evt e1 \<and> e1 \<notin> A"
          by (metis a_nontick a_notin_evt_A evt.exhaust imageI)

        obtain y' where y'_assms: "y = [Event e1]\<^sub>E # y' \<and> Some (t, Y) = tt2F y' \<and> ttWF y'"
          using case_assms(2) case_assms(5) a_evt by (cases y rule:ttWF.cases, auto, case_tac "tt2F \<sigma>", auto, fastforce)

        obtain z where "z \<in> (x \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C y') \<and> Some (aaa', X \<union> Y) = tt2F z"
          using case_assms(1) case_assms(4) case_assms2(1) ind_hyp ind_hyp' y'_assms by blast
        then show "\<exists>z. z \<in> (x \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C y) \<and> Some (a # aaa', X \<union> Y) = tt2F z"
          apply (rule_tac x="[Event e1]\<^sub>E # z" in exI, auto simp add: y'_assms case_assms2 a_evt)
           apply (cases x rule:ttWF.cases, auto simp add: a_evt)
           apply (cases "tt2F z", auto)
          done
      qed
    next
      assume case_assms2: "a \<noteq> tick" "a \<notin> evt ` A" "aa = tick"

      obtain e1 where a_evt: "a = evt e1 \<and> e1 \<notin> A"
        by (metis case_assms2(1) case_assms2(2) evt.exhaust imageI)
        
      obtain y' where y'_assms: "y = [Event e1]\<^sub>E # y' \<and> Some (t, Y) = tt2F y' \<and> ttWF y'"
        using case_assms(2) case_assms(5) a_evt by (cases y rule:ttWF.cases, auto, case_tac "tt2F \<sigma>", auto, fastforce)

      obtain aaa' where aaa'_assms: "aaa = a # aaa' \<and> aaa' \<in> aa # s \<lbrakk>insert tick (evt ` A)\<rbrakk>\<^sup>T\<^sub>F t"
        by (smt a_evt case_assms(6) case_assms2(3) evt_notin_image insertI1 mem_Collect_eq merge_traceF.simps(6))

      have "\<And>x y t a. ttWF x \<Longrightarrow> ttWF y \<Longrightarrow> Some (s, X) = tt2F x \<Longrightarrow> Some (t, Y) = tt2F y \<Longrightarrow>
        a \<in> s \<lbrakk>insert tick (evt ` A)\<rbrakk>\<^sup>T\<^sub>F t \<Longrightarrow> \<exists>z. z \<in> (x \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C y) \<and> Some (a, X \<union> Y) = tt2F z"
        by (simp add: ind_hyp')
      then obtain z where "z \<in> (x \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C y') \<and> Some (aaa', X \<union> Y) = tt2F z"
        using aaa'_assms case_assms(1) case_assms(4) ind_hyp y'_assms by blast
      then show "\<exists>z. z \<in> (x \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C y) \<and> Some (aaa, X \<union> Y) = tt2F z"
        apply (rule_tac x="[Event e1]\<^sub>E # z" in exI, auto simp add: y'_assms case_assms2 a_evt)
         apply (cases x rule:ttWF.cases, auto simp add: a_evt)
        apply (cases "tt2F z", auto)
        using a_evt aaa'_assms by blast
    next
      fix xa
      assume case_assms2: "a \<noteq> tick" "a \<notin> evt ` A" "aa = evt xa" "xa \<in> A"

      obtain e1 where a_evt: "a = evt e1 \<and> e1 \<notin> A"
        by (metis case_assms2(1) case_assms2(2) evt.exhaust imageI)
        
      obtain y' where y'_assms: "y = [Event e1]\<^sub>E # y' \<and> Some (t, Y) = tt2F y' \<and> ttWF y'"
        using case_assms(2) case_assms(5) a_evt by (cases y rule:ttWF.cases, auto, case_tac "tt2F \<sigma>", auto, fastforce)

      obtain aaa' where aaa'_assms: "aaa = a # aaa' \<and> aaa' \<in> aa # s \<lbrakk>insert tick (evt ` A)\<rbrakk>\<^sup>T\<^sub>F t"
        by (smt a_evt case_assms(6) case_assms2(3) case_assms2(4) evt_notin_image image_insert insert_iff mem_Collect_eq merge_traceF.simps(7) merge_traceF_comm mk_disjoint_insert)

      have "\<And>x y t a. ttWF x \<Longrightarrow> ttWF y \<Longrightarrow> Some (s, X) = tt2F x \<Longrightarrow> Some (t, Y) = tt2F y \<Longrightarrow>
        a \<in> s \<lbrakk>insert tick (evt ` A)\<rbrakk>\<^sup>T\<^sub>F t \<Longrightarrow> \<exists>z. z \<in> (x \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C y) \<and> Some (a, X \<union> Y) = tt2F z"
        by (simp add: ind_hyp')
      then obtain z where "z \<in> (x \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C y') \<and> Some (aaa', X \<union> Y) = tt2F z"
        using aaa'_assms case_assms(1) case_assms(4) ind_hyp y'_assms by blast
      then show "\<exists>z. z \<in> (x \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C y) \<and> Some (aaa, X \<union> Y) = tt2F z"
        apply (rule_tac x="[Event e1]\<^sub>E # z" in exI, auto simp add: y'_assms case_assms2 a_evt)
         apply (cases x rule:ttWF.cases, auto simp add: a_evt)
        apply (cases "tt2F z", auto)
        using a_evt aaa'_assms by blast
    next
      assume case_assms2: "aa \<noteq> tick" "aa \<notin> evt ` A" "a = tick"

      obtain e1 where a_evt: "aa = evt e1 \<and> e1 \<notin> A"
        by (metis case_assms2(1) case_assms2(2) evt.exhaust imageI)
        
      obtain x' where x'_assms: "x = [Event e1]\<^sub>E # x' \<and> Some (s, X) = tt2F x' \<and> ttWF x'"
        using case_assms(1) case_assms(4) a_evt by (cases x rule:ttWF.cases, auto, case_tac "tt2F \<sigma>", auto, fastforce)

      obtain aaa' where aaa'_assms: "aaa = aa # aaa' \<and> aaa' \<in> s \<lbrakk>insert tick (evt ` A)\<rbrakk>\<^sup>T\<^sub>F a # t"
        by (smt a_evt case_assms(6) case_assms2(3) evt_notin_image insertI1 mem_Collect_eq merge_traceF.simps(7))

      have "\<And>x y t a. ttWF x \<Longrightarrow> ttWF y \<Longrightarrow> Some (s, X) = tt2F x \<Longrightarrow> Some (t, Y) = tt2F y \<Longrightarrow>
        a \<in> s \<lbrakk>insert tick (evt ` A)\<rbrakk>\<^sup>T\<^sub>F t \<Longrightarrow> \<exists>z. z \<in> (x \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C y) \<and> Some (a, X \<union> Y) = tt2F z"
        by (simp add: ind_hyp')
      then obtain z where "z \<in> (x' \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C y) \<and> Some (aaa', X \<union> Y) = tt2F z"
        using aaa'_assms case_assms(2) case_assms(5) ind_hyp x'_assms by blast
      then show "\<exists>z. z \<in> (x \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C y) \<and> Some (aaa, X \<union> Y) = tt2F z"
        apply (rule_tac x="[Event e1]\<^sub>E # z" in exI, auto simp add: x'_assms case_assms2 a_evt)
         apply (cases y rule:ttWF.cases, auto simp add: a_evt)
        apply (cases "tt2F z", auto)
        using a_evt aaa'_assms by blast
    next
      fix xa
      assume case_assms2: "aa \<noteq> tick" "aa \<notin> evt ` A" "a = evt xa" "xa \<in> A"

      obtain e1 where a_evt: "aa = evt e1 \<and> e1 \<notin> A"
        by (metis case_assms2(1) case_assms2(2) evt.exhaust imageI)
        
      obtain x' where x'_assms: "x = [Event e1]\<^sub>E # x' \<and> Some (s, X) = tt2F x' \<and> ttWF x'"
        using case_assms(1) case_assms(4) a_evt by (cases x rule:ttWF.cases, auto, case_tac "tt2F \<sigma>", auto, fastforce)

      obtain aaa' where aaa'_assms: "aaa = aa # aaa' \<and> aaa' \<in> s \<lbrakk>insert tick (evt ` A)\<rbrakk>\<^sup>T\<^sub>F a # t"
        by (smt a_evt case_assms(6) case_assms2(3) case_assms2(4) evt_notin_image image_insert insert_iff mem_Collect_eq merge_traceF.simps(7) merge_traceF_comm mk_disjoint_insert)

      have "\<And>x y t a. ttWF x \<Longrightarrow> ttWF y \<Longrightarrow> Some (s, X) = tt2F x \<Longrightarrow> Some (t, Y) = tt2F y \<Longrightarrow>
        a \<in> s \<lbrakk>insert tick (evt ` A)\<rbrakk>\<^sup>T\<^sub>F t \<Longrightarrow> \<exists>z. z \<in> (x \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C y) \<and> Some (a, X \<union> Y) = tt2F z"
        by (simp add: ind_hyp')
      then obtain z where "z \<in> (x' \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C y) \<and> Some (aaa', X \<union> Y) = tt2F z"
        using aaa'_assms case_assms(2) case_assms(5) ind_hyp x'_assms by blast
      then show "\<exists>z. z \<in> (x \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C y) \<and> Some (aaa, X \<union> Y) = tt2F z"
        apply (rule_tac x="[Event e1]\<^sub>E # z" in exI, auto simp add: x'_assms case_assms2 a_evt)
         apply (cases y rule:ttWF.cases, auto simp add: a_evt)
        apply (cases "tt2F z", auto)
        using a_evt aaa'_assms by blast
    next
      fix xa
      assume "aa = tick" "a = evt xa" "xa \<in> A"
      then have False
        using case_assms(6) by auto
      then show "\<exists>z. z \<in> (x \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C y) \<and> Some (aaa, X \<union> Y) = tt2F z"
        by auto
    next
      fix xa
      assume "a = tick" "aa = evt xa" "xa \<in> A"
      then have False
        using case_assms(6) by auto
      then show "\<exists>z. z \<in> (x \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C y) \<and> Some (aaa, X \<union> Y) = tt2F z"
        by auto
    next
      fix xa xaa
      assume case_assms2: "aa = evt xa" "xa \<in> A" "a = evt xaa" "xaa \<in> A"

      obtain x' where x'_assms: "x = [Event xa]\<^sub>E # x' \<and> Some (s, X) = tt2F x' \<and> ttWF x'"
        using case_assms(1) case_assms(4) case_assms2(1) by (cases x rule:ttWF.cases, auto, case_tac "tt2F \<sigma>", auto, fastforce)
      obtain y' where y'_assms: "y = [Event xaa]\<^sub>E # y' \<and> Some (t, Y) = tt2F y' \<and> ttWF y'"
        using case_assms(2) case_assms(5) case_assms2(3) by (cases y rule:ttWF.cases, auto, case_tac "tt2F \<sigma>", auto, fastforce)

      obtain aaa' where aaa'_assms: "aaa = aa # aaa' \<and> aa = a \<and> aaa' \<in> s \<lbrakk>insert tick (evt ` A)\<rbrakk>\<^sup>T\<^sub>F t"
        using case_assms(6) case_assms2 by (cases "aa = a", auto)
      obtain z where "z \<in> (x' \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C y') \<and> Some (aaa', X \<union> Y) = tt2F z"
        using aaa'_assms ind_hyp' x'_assms y'_assms by blast
      then show "\<exists>z. z \<in> (x \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C y) \<and> Some (aaa, X \<union> Y) = tt2F z"
        apply (rule_tac x="[Event xa]\<^sub>E # z" in exI, auto)
        using aaa'_assms case_assms2(1) case_assms2(2) case_assms2(3) x'_assms y'_assms apply auto
        by (smt fst_conv option.simps(5) snd_conv)
    qed
  qed
qed

lemma ttproc2F_ParCompTT_eq_ParCompF_trace2:
 "\<And>a b t x y. a \<in> s \<lbrakk>insert tick (evt ` A)\<rbrakk>\<^sup>T\<^sub>F t \<Longrightarrow> s @ [tick] = tt2T x \<Longrightarrow>
    Some (t, b) = tt2F y \<Longrightarrow> ttWF x \<Longrightarrow> ttWF y \<Longrightarrow> Aa \<subseteq> A \<Longrightarrow>
    \<exists>z. Some (a, b \<union> evt ` Aa) = tt2F z \<and> (\<exists>w. (\<exists>p. \<exists>q. w = (p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q) \<and> p \<lesssim>\<^sub>C x \<and> q \<lesssim>\<^sub>C y) \<and> z \<in> w)"
proof (induct s, auto)
  fix b t and x :: "'a tttrace"
  assume case_assms: "[tick] = tt2T x"  "ttWF x" "Aa \<subseteq> A"

  have x_Tick: "x = [[Tick]\<^sub>E]"
    using case_assms by (cases x rule:ttWF.cases, simp, simp, blast, simp_all)

  show "\<And>y a. a \<in> [] \<lbrakk>insert tick (evt ` A)\<rbrakk>\<^sup>T\<^sub>F t \<Longrightarrow> Some (t, b) = tt2F y \<Longrightarrow> ttWF y \<Longrightarrow>
     \<exists>z. Some (a, b \<union> evt ` Aa) = tt2F z \<and> (\<exists>w. (\<exists>p q. w = (p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q) \<and> p \<lesssim>\<^sub>C x \<and> q \<lesssim>\<^sub>C y) \<and> z \<in> w)"
  proof (induct t, auto)
    fix y
    assume case_assms2: "Some ([], b) = tt2F y" "ttWF y"

    obtain Y where Y_assms: "b = {x. ttevt2F x \<in> Y} \<and> y = [[Y]\<^sub>R]"
      using case_assms2(1) case_assms2(2) by (cases y rule:ttWF.cases, auto, case_tac "tt2F \<sigma>", auto)

    show "\<exists>z. Some ([], b \<union> evt ` Aa) = tt2F z \<and> (\<exists>w. (\<exists>p q. w = (p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q) \<and> p \<lesssim>\<^sub>C x \<and> q \<lesssim>\<^sub>C y) \<and> z \<in> w)"
      using x_Tick Y_assms case_assms(3) apply (rule_tac x="[[Y \<union> Event ` Aa]\<^sub>R]" in exI, auto)
      apply (metis evt.exhaust imageI ttevent.distinct(3) ttevent.inject ttevt2F.simps(1) ttevt2F.simps(2))
      apply (rule_tac x="x \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C y" in exI, auto)
      by (rule_tac x="x" in exI, rule_tac x="y" in exI, auto)
  next
    fix a t y aa
    assume ind_hyp: "\<And>y a. a \<in> [] \<lbrakk>insert tick (evt ` A)\<rbrakk>\<^sup>T\<^sub>F t \<Longrightarrow> Some (t, b) = tt2F y \<Longrightarrow> ttWF y \<Longrightarrow>
      \<exists>z. Some (a, b \<union> evt ` Aa) = tt2F z \<and> (\<exists>w. (\<exists>p q. w = (p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q) \<and> p \<lesssim>\<^sub>C x \<and> q \<lesssim>\<^sub>C y) \<and> z \<in> w)"
    assume case_assms2: "aa \<in> [] \<lbrakk>insert tick (evt ` A)\<rbrakk>\<^sup>T\<^sub>F a # t" "Some (a # t, b) = tt2F y" "ttWF y"

    obtain e where a_evt: "a = evt e"
      by (metis case_assms2(1) empty_iff evt.exhaust insertI1 merge_traceF.simps(2))

    obtain y' where y'_assms: "Some (t, b) = tt2F y' \<and> ttWF y' \<and> y = [Event e]\<^sub>E # y'"
      using case_assms2(2) case_assms2(3) a_evt by (cases y rule:ttWF.cases, auto, case_tac "tt2F \<sigma>", auto, fastforce)

    obtain aa' where aa'_assms: "aa = a # aa' \<and> aa' \<in> [] \<lbrakk>insert tick (evt ` A)\<rbrakk>\<^sup>T\<^sub>F t"
      by (smt case_assms2(1) empty_iff mem_Collect_eq merge_traceF.simps(2) merge_traceF.simps(3))

    obtain z p q where "Some (aa', b \<union> evt ` Aa) = tt2F z \<and> z \<in> (p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q) \<and> p \<lesssim>\<^sub>C x \<and> q \<lesssim>\<^sub>C y'"
      by (metis aa'_assms ind_hyp y'_assms)
    then show "\<exists>z. Some (aa, b \<union> evt ` Aa) = tt2F z \<and> (\<exists>w. (\<exists>p q. w = (p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q) \<and> p \<lesssim>\<^sub>C x \<and> q \<lesssim>\<^sub>C y) \<and> z \<in> w)"
      apply (rule_tac x="[Event e]\<^sub>E # z" in exI, auto simp add: a_evt aa'_assms)
      apply (cases "tt2F z", auto)
      apply (rule_tac x="p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C ([Event e]\<^sub>E # q)" in exI, auto)
      using tt_prefix_subset.simps(3) y'_assms apply blast
      apply (cases p rule:ttWF.cases, auto simp add: x_Tick tt2F_None_merge_traces')
      using a_evt case_assms2(1) by auto
  qed
next
  fix s a aa b t x y

  show "\<And>a s aa b x y. (\<And>a b t x y. a \<in> s \<lbrakk>insert tick (evt ` A)\<rbrakk>\<^sup>T\<^sub>F t \<Longrightarrow> s @ [tick] = tt2T x \<Longrightarrow>
           Some (t, b) = tt2F y \<Longrightarrow> ttWF x \<Longrightarrow> ttWF y \<Longrightarrow>
           \<exists>z. Some (a, b \<union> evt ` Aa) = tt2F z \<and> (\<exists>w. (\<exists>p q. w = (p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q) \<and> p \<lesssim>\<^sub>C x \<and> q \<lesssim>\<^sub>C y) \<and> z \<in> w)) \<Longrightarrow>
       aa \<in> a # s \<lbrakk>insert tick (evt ` A)\<rbrakk>\<^sup>T\<^sub>F t \<Longrightarrow> a # s @ [tick] = tt2T x \<Longrightarrow> Some (t, b) = tt2F y \<Longrightarrow> ttWF x \<Longrightarrow> ttWF y \<Longrightarrow>
        \<exists>z. Some (aa, b \<union> evt ` Aa) = tt2F z \<and> (\<exists>w. (\<exists>p q. w = (p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q) \<and> p \<lesssim>\<^sub>C x \<and> q \<lesssim>\<^sub>C y) \<and> z \<in> w)"
  proof (induct t, auto)
    fix a s aa b and x y :: "'a tttrace"
    assume ind_hyp: "\<And>a b t x y. a \<in> s \<lbrakk>insert tick (evt ` A)\<rbrakk>\<^sup>T\<^sub>F t \<Longrightarrow> s @ [tick] = tt2T x \<Longrightarrow>
           Some (t, b) = tt2F y \<Longrightarrow> ttWF x \<Longrightarrow> ttWF y \<Longrightarrow>
            \<exists>z. Some (a, b \<union> evt ` Aa) = tt2F z \<and> (\<exists>w. (\<exists>p q. w = (p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q) \<and> p \<lesssim>\<^sub>C x \<and> q \<lesssim>\<^sub>C y) \<and> z \<in> w)"
    assume case_assms: "aa \<in> [] \<lbrakk>insert tick (evt ` A)\<rbrakk>\<^sup>T\<^sub>F a # s" "a # s @ [tick] = tt2T x" "Some ([], b) = tt2F y" "ttWF x" "ttWF y"

    obtain e where a_evt: "a = evt e"
      by (metis case_assms(1) empty_iff evt.exhaust insertI1 merge_traceF.simps(2))

    obtain x' where x'_assms: "s @ [tick] = tt2T x' \<and> x = [Event e]\<^sub>E # x' \<and> ttWF x'"
      using case_assms(2) case_assms(4) a_evt by (cases x rule:ttWF.cases, auto)

    obtain Y where Y_assms: "b = {x. ttevt2F x \<in> Y} \<and> y = [[Y]\<^sub>R]"
      using case_assms(3) case_assms(5) by (cases y rule:ttWF.cases, auto, case_tac "tt2F \<sigma>", auto)

    obtain aa' where aa'_assms: "aa = a # aa' \<and> aa' \<in> s \<lbrakk>insert tick (evt ` A)\<rbrakk>\<^sup>T\<^sub>F []"
      by (smt case_assms(1) empty_iff mem_Collect_eq merge_traceF.simps(2) merge_traceF.simps(3) merge_traceF_comm)

    obtain z p q where "Some (aa', b \<union> evt ` Aa) = tt2F z \<and> z \<in> (p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q) \<and> p \<lesssim>\<^sub>C x' \<and> q \<lesssim>\<^sub>C y"
      by (metis aa'_assms case_assms(3) case_assms(5) ind_hyp x'_assms)
    then show "\<exists>z. Some (aa, b \<union> evt ` Aa) = tt2F z \<and> (\<exists>w. (\<exists>p q. w = (p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q) \<and> p \<lesssim>\<^sub>C x \<and> q \<lesssim>\<^sub>C y) \<and> z \<in> w)"
      apply (rule_tac x="[Event e]\<^sub>E # z" in exI, auto)
      apply (cases "tt2F z", auto simp add: a_evt aa'_assms)
      apply (rule_tac x="[Event e]\<^sub>E # p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q" in exI, auto)
      using tt_prefix_subset.simps(3) x'_assms apply blast
      apply (cases q rule:ttWF.cases, auto simp add: Y_assms)
      apply (simp add: merge_traces_comm tt2F_None_merge_traces')
      using a_evt case_assms(1) by auto
  next
    fix a t aa s aaa b x y
    assume ind_hyp1: "\<And>a s aa b x y. (\<And>a b t x y. a \<in> (s \<lbrakk>insert tick (evt ` A)\<rbrakk>\<^sup>T\<^sub>F t) \<Longrightarrow>
        s @ [tick] = tt2T x \<Longrightarrow> Some (t, b) = tt2F y \<Longrightarrow> ttWF x \<Longrightarrow> ttWF y \<Longrightarrow>
        \<exists>z. Some (a, b \<union> evt ` Aa) = tt2F z \<and> (\<exists>w. (\<exists>p q. w = (p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q) \<and> p \<lesssim>\<^sub>C x \<and> q \<lesssim>\<^sub>C y) \<and> z \<in> w)) \<Longrightarrow>
      aa \<in> (a # s \<lbrakk>insert tick (evt ` A)\<rbrakk>\<^sup>T\<^sub>F t) \<Longrightarrow> a # s @ [tick] = tt2T x \<Longrightarrow> Some (t, b) = tt2F y \<Longrightarrow> ttWF x \<Longrightarrow> ttWF y \<Longrightarrow>
        \<exists>z. Some (aa, b \<union> evt ` Aa) = tt2F z \<and> (\<exists>w. (\<exists>p q. w = (p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q) \<and> p \<lesssim>\<^sub>C x \<and> q \<lesssim>\<^sub>C y) \<and> z \<in> w)"
    assume ind_hyp2: "\<And>a b t x y. a \<in> s \<lbrakk>insert tick (evt ` A)\<rbrakk>\<^sup>T\<^sub>F t \<Longrightarrow>
           s @ [tick] = tt2T x \<Longrightarrow> Some (t, b) = tt2F y \<Longrightarrow> ttWF x \<Longrightarrow> ttWF y \<Longrightarrow>
            \<exists>z. Some (a, b \<union> evt ` Aa) = tt2F z \<and> (\<exists>w. (\<exists>p q. w = (p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q) \<and> p \<lesssim>\<^sub>C x \<and> q \<lesssim>\<^sub>C y) \<and> z \<in> w)"
    assume case_assms: "aaa \<in> aa # s \<lbrakk>insert tick (evt ` A)\<rbrakk>\<^sup>T\<^sub>F a # t" "aa # s @ [tick] = tt2T x" "Some (a # t, b) = tt2F y" "ttWF x" "ttWF y"

    obtain e1 x' where x'_assms: "aa = evt e1 \<and> x = [Event e1]\<^sub>E # x' \<and> ttWF x' \<and> s @ [tick] = tt2T x'"
      using case_assms(2) case_assms(4) by (cases aa, auto, (induct x rule:ttWF.induct, auto)+)
    obtain e2 y' where y'_assms: "a = evt e2 \<and> y = [Event e2]\<^sub>E # y' \<and> ttWF y' \<and> Some (t, b) = tt2F y'"
      using case_assms(3) case_assms(5) apply (cases a, auto, cases y rule:ttWF.cases, auto, case_tac "tt2F \<sigma>", auto)
      by (cases y rule:ttWF.cases, auto, case_tac "tt2F \<sigma>", auto, fastforce)

    have e1_e2_cases: "(e1 \<in> A \<and> e2 \<in> A) \<or> (e1 \<notin> A \<and> e2 \<in> A) \<or> (e1 \<in> A \<and> e2 \<notin> A) \<or> (e1 \<notin> A \<and> e2 \<notin> A)"
      by auto
    then show "\<exists>z. Some (aaa, b \<union> evt ` Aa) = tt2F z \<and> (\<exists>w. (\<exists>p q. w = (p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q) \<and> p \<lesssim>\<^sub>C x \<and> q \<lesssim>\<^sub>C y) \<and> z \<in> w)"
    proof auto
      assume e1_in_A: "e1 \<in> A" and e2_in_A: "e2 \<in> A"

      have e1_eq_e2: "e1 = e2"
        using case_assms(1) x'_assms y'_assms e1_in_A e2_in_A by (auto, cases "e1 = e2", auto)
      then obtain aaa' where aaa'_assms: "aaa = evt e1 # aaa' \<and> aaa' \<in> s \<lbrakk>insert tick (evt ` A)\<rbrakk>\<^sup>T\<^sub>F t"
        using case_assms(1) x'_assms y'_assms e1_in_A e2_in_A by auto

      obtain z p q where "Some (aaa', b \<union> evt ` Aa) = tt2F z \<and> z \<in> (p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q) \<and> p \<lesssim>\<^sub>C x' \<and> q \<lesssim>\<^sub>C y'"
        by (metis aaa'_assms ind_hyp2 x'_assms y'_assms)
      then show "\<exists>z. Some (aaa, b \<union> evt ` Aa) = tt2F z \<and> (\<exists>w. (\<exists>p q. w = (p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q) \<and> p \<lesssim>\<^sub>C x \<and> q \<lesssim>\<^sub>C y) \<and> z \<in> w)"
        apply (rule_tac x="[Event e1]\<^sub>E # z" in exI, auto)
        apply (cases "tt2F z", auto)
        using aaa'_assms apply blast
        apply (rule_tac x="[Event e1]\<^sub>E # p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C [Event e1]\<^sub>E # q" in exI, auto)
        apply (rule_tac x="[Event e1]\<^sub>E # p" in exI, rule_tac x="[Event e1]\<^sub>E # q" in exI, auto simp add: x'_assms y'_assms)
        using e1_eq_e2 e1_in_A by auto
    next
      assume e1_in_A: "e1 \<in> A" and e2_notin_A: "e2 \<notin> A"

      obtain aaa' where aaa'_assms: "aaa = evt e2 # aaa' \<and> aaa' \<in> (evt e1 # s) \<lbrakk>insert tick (evt ` A)\<rbrakk>\<^sup>T\<^sub>F t"
        using case_assms(1) x'_assms y'_assms e1_in_A e2_notin_A apply auto
        by (smt evt_notin_image image_insert insertI1 insert_commute mem_Collect_eq merge_traceF.simps(6) mk_disjoint_insert)
      
      have "\<And>a b t x y. a \<in> s \<lbrakk>insert tick (evt ` A)\<rbrakk>\<^sup>T\<^sub>F t \<Longrightarrow> s @ [tick] = tt2T x \<Longrightarrow> Some (t, b) = tt2F y \<Longrightarrow>
        ttWF x \<Longrightarrow> ttWF y \<Longrightarrow> \<exists>z. Some (a, b \<union> evt ` Aa) = tt2F z \<and> (\<exists>w. (\<exists>p q. w = (p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q) \<and> p \<lesssim>\<^sub>C x \<and> q \<lesssim>\<^sub>C y) \<and> z \<in> w)"
        by (simp add: ind_hyp2)
      then obtain z p q where "Some (aaa', b \<union> evt ` Aa) = tt2F z \<and> z \<in> (p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q) \<and> p \<lesssim>\<^sub>C x \<and> q \<lesssim>\<^sub>C y'"
        using ind_hyp1[where s=s, where aa=aaa', where a="evt e1", where b=b, where x=x, where y=y']
        using aaa'_assms x'_assms y'_assms by auto
      then show "\<exists>z. Some (aaa, b \<union> evt ` Aa) = tt2F z \<and> (\<exists>w. (\<exists>p q. w = (p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q) \<and> p \<lesssim>\<^sub>C x \<and> q \<lesssim>\<^sub>C y) \<and> z \<in> w)"
        apply (rule_tac x="[Event e2]\<^sub>E # z" in exI, auto)
        apply (cases "tt2F z", auto)
        using aaa'_assms apply blast
        apply (rule_tac x="p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C [Event e2]\<^sub>E # q" in exI, auto)
        apply (rule_tac x="p" in exI, rule_tac x="[Event e2]\<^sub>E # q" in exI, auto simp add: x'_assms y'_assms)
        using y'_assms e2_notin_A by (auto, cases p rule:ttWF.cases, auto)
    next
      assume e1_notin_A: "e1 \<notin> A" and e2_in_A: "e2 \<in> A"

      obtain aaa' where aaa'_assms: "aaa = evt e1 # aaa' \<and> aaa' \<in> s \<lbrakk>insert tick (evt ` A)\<rbrakk>\<^sup>T\<^sub>F (evt e2 # t)"
        using case_assms(1) x'_assms y'_assms e1_notin_A e2_in_A apply auto
        by (smt evt_notin_image image_insert insertI1 insertI2 mem_Collect_eq merge_traceF.simps(7) mk_disjoint_insert)

      obtain z p q where "Some (aaa', b \<union> evt ` Aa) = tt2F z \<and> z \<in> (p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q) \<and> p \<lesssim>\<^sub>C x' \<and> q \<lesssim>\<^sub>C y"
        by (metis aaa'_assms case_assms(3) case_assms(5) ind_hyp2 x'_assms y'_assms)
      then show "\<exists>z. Some (aaa, b \<union> evt ` Aa) = tt2F z \<and> (\<exists>w. (\<exists>p q. w = (p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q) \<and> p \<lesssim>\<^sub>C x \<and> q \<lesssim>\<^sub>C y) \<and> z \<in> w)"
        apply (rule_tac x="[Event e1]\<^sub>E # z" in exI, auto)
        apply (cases "tt2F z", auto)
        using aaa'_assms apply blast
        apply (rule_tac x="[Event e1]\<^sub>E # p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q" in exI, auto)
        apply (rule_tac x="[Event e1]\<^sub>E # p" in exI, rule_tac x="q" in exI, auto simp add: x'_assms y'_assms)
        using y'_assms e1_notin_A by (auto, cases q rule:ttWF.cases, auto)
    next
      assume e1_notin_A: "e1 \<notin> A" and e2_notin_A: "e2 \<notin> A"

      obtain aaa' where  "(aaa = evt e1 # aaa' \<and> aaa' \<in> s \<lbrakk>insert tick (evt ` A)\<rbrakk>\<^sup>T\<^sub>F (evt e2 # t))
        \<or> (aaa = evt e2 # aaa' \<and> aaa' \<in> (evt e1 # s) \<lbrakk>insert tick (evt ` A)\<rbrakk>\<^sup>T\<^sub>F t)"
        by (smt UnE case_assms(1) e1_notin_A e2_notin_A evt_notin_image mem_Collect_eq merge_traceF.simps(5) x'_assms y'_assms)
      then show "\<exists>z. Some (aaa, b \<union> evt ` Aa) = tt2F z \<and> (\<exists>w. (\<exists>p q. w = (p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q) \<and> p \<lesssim>\<^sub>C x \<and> q \<lesssim>\<^sub>C y) \<and> z \<in> w)"
      proof auto
        assume case_assms3: "aaa' \<in> s \<lbrakk>insert tick (evt ` A)\<rbrakk>\<^sup>T\<^sub>F evt e2 # t" "aaa = evt e1 # aaa'"

        obtain z p q where "Some (aaa', b \<union> evt ` Aa) = tt2F z \<and> z \<in> (p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q) \<and> p \<lesssim>\<^sub>C x' \<and> q \<lesssim>\<^sub>C y"
          by (metis case_assms(3) case_assms(5) case_assms3(1) ind_hyp2 x'_assms y'_assms)
        then show "\<exists>z. Some (evt e1 # aaa', b \<union> evt ` Aa) = tt2F z \<and> (\<exists>w. (\<exists>p q. w = (p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q) \<and> p \<lesssim>\<^sub>C x \<and> q \<lesssim>\<^sub>C y) \<and> z \<in> w)"
          apply (rule_tac x="[Event e1]\<^sub>E # z" in exI, auto)
          apply (cases "tt2F z", auto)
          apply (rule_tac x="[Event e1]\<^sub>E # p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q" in exI, auto)
          apply (rule_tac x="[Event e1]\<^sub>E # p" in exI, rule_tac x="q" in exI, auto simp add: x'_assms y'_assms)
          using y'_assms e1_notin_A by (auto, cases q rule:ttWF.cases, auto)
      next
        assume case_assms3: "aaa' \<in> evt e1 # s \<lbrakk>insert tick (evt ` A)\<rbrakk>\<^sup>T\<^sub>F t" "aaa = evt e2 # aaa'"

        have "(\<And>a b t x y. a \<in> s \<lbrakk>insert tick (evt ` A)\<rbrakk>\<^sup>T\<^sub>F t \<Longrightarrow> s @ [tick] = tt2T x \<Longrightarrow> Some (t, b) = tt2F y \<Longrightarrow>
          ttWF x \<Longrightarrow> ttWF y \<Longrightarrow> \<exists>z. Some (a, b \<union> evt ` Aa) = tt2F z \<and> (\<exists>w. (\<exists>p q. w = (p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q) \<and> p \<lesssim>\<^sub>C x \<and> q \<lesssim>\<^sub>C y) \<and> z \<in> w))"
          by (simp add: ind_hyp2)
        obtain z p q where "Some (aaa', b \<union> evt ` Aa) = tt2F z \<and> z \<in> (p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q) \<and> p \<lesssim>\<^sub>C x \<and> q \<lesssim>\<^sub>C y'"
          using ind_hyp1[where s=s, where x=x, where b=b, where a="evt e1", where aa=aaa', where y=y']
          using case_assms3(1) ind_hyp2 x'_assms y'_assms by auto
        then show "\<exists>z. Some (evt e2 # aaa', b \<union> evt ` Aa) = tt2F z \<and> (\<exists>w. (\<exists>p q. w = (p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q) \<and> p \<lesssim>\<^sub>C x \<and> q \<lesssim>\<^sub>C y) \<and> z \<in> w)"
          apply (rule_tac x="[Event e2]\<^sub>E # z" in exI, auto)
           apply (cases "tt2F z", auto)
          apply (rule_tac x="p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C [Event e2]\<^sub>E # q" in exI, auto)
           apply (rule_tac x="p" in exI, rule_tac x="[Event e2]\<^sub>E #  q" in exI, auto simp add: x'_assms y'_assms)
          using x'_assms e2_notin_A by (auto, cases p rule:ttWF.cases, auto)
      qed
    qed
  qed
qed

lemma ttproc2F_ParCompTT_eq_ParCompF_trace3:
  "\<And> s t x y. z \<in> tt2T x \<lbrakk>insert tick (evt ` A)\<rbrakk>\<^sup>T\<^sub>F tt2T y \<Longrightarrow> ttWF x \<Longrightarrow> ttWF y \<Longrightarrow>
       \<exists>z'. z = tt2T z' \<and> (\<exists>w. (\<exists>p q. w = (p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q) \<and> p \<lesssim>\<^sub>C x \<and> q \<lesssim>\<^sub>C y) \<and> z' \<in> w)"
proof (induct z, auto)
  fix x y
  assume "[] \<in> tt2T x \<lbrakk>insert tick (evt ` A)\<rbrakk>\<^sup>T\<^sub>F tt2T y"
  show "\<exists>z'. [] = tt2T z' \<and> (\<exists>w. (\<exists>p q. w = (p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q) \<and> p \<lesssim>\<^sub>C x \<and> q \<lesssim>\<^sub>C y) \<and> z' \<in> w)"
    apply (rule_tac x="[]" in exI, auto, rule_tac x="{[]}" in exI, auto)
    by (rule_tac x="[]" in exI, rule_tac x="[]" in exI, auto)
next
  fix a z x y
  assume ind_hyp: "\<And>x y. z \<in> tt2T x \<lbrakk>insert tick (evt ` A)\<rbrakk>\<^sup>T\<^sub>F tt2T y \<Longrightarrow>
    ttWF x \<Longrightarrow> ttWF y \<Longrightarrow> \<exists>z'. z = tt2T z' \<and> (\<exists>w. (\<exists>p q. w = (p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q) \<and> p \<lesssim>\<^sub>C x \<and> q \<lesssim>\<^sub>C y) \<and> z' \<in> w)"

  assume case_assms: "a # z \<in> tt2T x \<lbrakk>insert tick (evt ` A)\<rbrakk>\<^sup>T\<^sub>F tt2T y" "ttWF x" "ttWF y"
  show "\<exists>z'. a # z = tt2T z' \<and> (\<exists>w. (\<exists>p q. w = (p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q) \<and> p \<lesssim>\<^sub>C x \<and> q \<lesssim>\<^sub>C y) \<and> z' \<in> w)"
  proof (cases a, auto)
    assume "a = tick"
    then have "x = [[Tick]\<^sub>E] \<and> y = [[Tick]\<^sub>E]"
      using case_assms apply (cases "(x, y)" rule:ttWF2.cases, auto)
      using merge_traceF_Nil_prefix apply fastforce+
      apply (smt empty_iff evt.distinct(1) insertI1 list.inject mem_Collect_eq merge_traceF.simps(6) merge_traceF.simps(8))
      apply (meson Cons_prefix_Cons evt.distinct(1) merge_traceF_Nil_prefix)
      apply (meson Cons_prefix_Cons evt.distinct(1) merge_traceF_Nil_prefix)
         apply (smt empty_iff evt.distinct(1) insertI1 list.inject mem_Collect_eq merge_traceF.simps(7) merge_traceF.simps(8))
      apply (case_tac "e \<in> A", case_tac "f \<in> A", case_tac "e = f", auto)
      using evt_notin_image apply fastforce
      apply (case_tac "f \<in> A")
      using evt_notin_image apply fastforce
        apply (smt UnE evt.distinct(1) evt_notin_image list.inject mem_Collect_eq merge_traceF.simps(5))
      apply (case_tac "e \<in> A", auto)
      using merge_traceF_Nil_prefix apply fastforce
      by (meson Cons_prefix_Cons evt.distinct(1) merge_traceF_Nil_prefix)
    then show "\<exists>z'. tick # z = tt2T z' \<and> (\<exists>w. (\<exists>p q. w = (p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q) \<and> p \<lesssim>\<^sub>C x \<and> q \<lesssim>\<^sub>C y) \<and> z' \<in> w)"
      using case_assms apply (rule_tac x="[[Tick]\<^sub>E]" in exI, auto, rule_tac x="{[[Tick]\<^sub>E]}" in exI, auto)
      by (rule_tac x="[[Tick]\<^sub>E]" in exI, rule_tac x="[[Tick]\<^sub>E]" in exI, auto)
  next
    fix x2
    assume a_evt: "a = evt x2"

    show "\<exists>z'. evt x2 # z = tt2T z' \<and> (\<exists>w. (\<exists>p q. w = (p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q) \<and> p \<lesssim>\<^sub>C x \<and> q \<lesssim>\<^sub>C y) \<and> z' \<in> w)"
    proof (cases "x2 \<in> A")
      assume x2_in_A: "x2 \<in> A"
      thm case_assms

      obtain x' y' where x'_y'_assms: "x = [Event x2]\<^sub>E # x' \<and> y = [Event x2]\<^sub>E # y' \<and> z \<in> tt2T x' \<lbrakk>insert tick (evt ` A)\<rbrakk>\<^sup>T\<^sub>F tt2T y'"
        using case_assms x2_in_A a_evt apply (induct x y rule:ttWF2.induct, auto simp add: case_assms x2_in_A a_evt)
        using merge_traceF_Nil_prefix x2_in_A apply fastforce
        using merge_traceF_Nil_prefix x2_in_A apply fastforce
        apply (smt empty_iff evt.distinct(1) image_insert insertI1 insertI2 list.inject mem_Collect_eq merge_traceF.simps(6) merge_traceF.simps(8) mk_disjoint_insert x2_in_A)
        using merge_traceF_Nil_prefix x2_in_A apply fastforce
        using merge_traceF_Nil_prefix x2_in_A apply fastforce
        apply (smt empty_iff evt.distinct(1) image_insert insertI1 insertI2 list.inject mem_Collect_eq merge_traceF.simps(7) merge_traceF.simps(8) mk_disjoint_insert x2_in_A)
        apply (case_tac "e \<in> A", case_tac "f \<in> A", case_tac "e = f", auto)
        using evt_notin_image x2_in_A apply fastforce
        apply (case_tac "f \<in> A")
        using evt_notin_image x2_in_A apply fastforce
        apply (smt UnE evt_notin_image image_insert insertCI list.inject mem_Collect_eq merge_traceF.simps(5) mk_disjoint_insert x2_in_A)
        using merge_traceF_Nil_prefix x2_in_A apply fastforce
        using merge_traceF_Nil_prefix x2_in_A by fastforce
      then have "\<exists>z'. z = tt2T z' \<and> (\<exists>w. (\<exists>p q. w = (p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q) \<and> p \<lesssim>\<^sub>C x' \<and> q \<lesssim>\<^sub>C y') \<and> z' \<in> w)"
        using case_assms(2) case_assms(3) ind_hyp by auto
      then show "\<exists>z'. evt x2 # z = tt2T z' \<and> (\<exists>w. (\<exists>p q. w = (p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q) \<and> p \<lesssim>\<^sub>C x \<and> q \<lesssim>\<^sub>C y) \<and> z' \<in> w)"
        apply auto apply (rule_tac x="[Event x2]\<^sub>E # z'" in exI, auto simp add: case_assms x'_y'_assms)
        apply (rule_tac x="[Event x2]\<^sub>E # p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C [Event x2]\<^sub>E # q" in exI, auto)
        apply (rule_tac x="[Event x2]\<^sub>E # p" in exI, rule_tac x="[Event x2]\<^sub>E # q" in exI, auto)
        using x2_in_A by blast+
    next
      assume x2_notin_A: "x2 \<notin> A"

      have "(\<exists>x'. x = [Event x2]\<^sub>E # x' \<and> z \<in> tt2T x' \<lbrakk>insert tick (evt ` A)\<rbrakk>\<^sup>T\<^sub>F tt2T y)
        \<or> (\<exists>y'. y = [Event x2]\<^sub>E # y' \<and> z \<in> tt2T x \<lbrakk>insert tick (evt ` A)\<rbrakk>\<^sup>T\<^sub>F tt2T y')"
        using merge_traceF_Nil_prefix evt_notin_image case_assms x2_notin_A a_evt apply (induct x y rule:ttWF2.induct, auto)
        apply fastforce
        apply fastforce
        apply fastforce
        apply fastforce
        using merge_traceF_singleton_prefix apply fastforce
        apply (smt equals0D evt.distinct(1) insertI1 list.inject mem_Collect_eq merge_traceF.simps(6) merge_traceF.simps(8))
        apply fastforce
        using merge_traceF_comm apply fastforce
        apply fastforce
        using merge_traceF_comm apply fastforce
        apply (smt Cons_prefix_Cons evt.inject insertI1 merge_traceF_comm merge_traceF_singleton_prefix)
        apply (smt Cons_prefix_Cons evt_notin_image insertI1 list.inject mem_Collect_eq merge_traceF.simps(7) merge_traceF_comm merge_traceF_singleton_prefix)
        apply (case_tac "e \<in> A", case_tac "f \<in> A", case_tac "e = f", auto)
        apply (smt UnE evt.inject evt_notin_image list.inject mem_Collect_eq merge_traceF.simps(5) merge_traceF.simps(7))
        apply (case_tac "e \<in> A", case_tac "f \<in> A", case_tac "e = f", auto)
        apply (smt UnE evt.inject evt_notin_image list.inject mem_Collect_eq merge_traceF.simps(5) merge_traceF.simps(7))
        apply (case_tac "e \<in> A", case_tac "f \<in> A", case_tac "e = f", auto)
        apply (smt UnE evt.inject evt_notin_image list.inject mem_Collect_eq merge_traceF.simps(5) merge_traceF.simps(7))
        apply (case_tac "e \<in> A", case_tac "f \<in> A", case_tac "e = f", auto)
        apply (smt UnE evt.inject evt_notin_image list.inject mem_Collect_eq merge_traceF.simps(5) merge_traceF.simps(7))
        apply fastforce
        using merge_traceF_comm apply fastforce
        apply fastforce
        by fastforce
      then show "\<exists>z'. evt x2 # z = tt2T z' \<and> (\<exists>w. (\<exists>p q. w = (p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q) \<and> p \<lesssim>\<^sub>C x \<and> q \<lesssim>\<^sub>C y) \<and> z' \<in> w)"
      proof auto
        fix x'
        assume "z \<in> tt2T x' \<lbrakk>insert tick (evt ` A)\<rbrakk>\<^sup>T\<^sub>F tt2T y" "x = [Event x2]\<^sub>E # x'"
        then have "\<exists>z'. z = tt2T z' \<and> (\<exists>w. (\<exists>p q. w = (p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q) \<and> p \<lesssim>\<^sub>C x' \<and> q \<lesssim>\<^sub>C y) \<and> z' \<in> w)"
          using case_assms(2) case_assms(3) ind_hyp by auto
        then show "\<exists>z'. evt x2 # z = tt2T z' \<and> (\<exists>w. (\<exists>p q. w = (p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q) \<and> p \<lesssim>\<^sub>C [Event x2]\<^sub>E # x' \<and> q \<lesssim>\<^sub>C y) \<and> z' \<in> w)"
          apply (auto) apply (rule_tac x="[Event x2]\<^sub>E # z'" in exI, auto)
          apply (rule_tac x="[Event x2]\<^sub>E # p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q" in exI, auto)
           apply (rule_tac x="[Event x2]\<^sub>E # p" in exI, rule_tac x="q" in exI, auto)
          apply (case_tac q rule:ttWF.cases, auto)
          using x2_notin_A by blast+
      next
        fix y'
        assume "z \<in> tt2T x \<lbrakk>insert tick (evt ` A)\<rbrakk>\<^sup>T\<^sub>F tt2T y'" " y = [Event x2]\<^sub>E # y'"
        then have "\<exists>z'. z = tt2T z' \<and> (\<exists>w. (\<exists>p q. w = (p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q) \<and> p \<lesssim>\<^sub>C x \<and> q \<lesssim>\<^sub>C y') \<and> z' \<in> w)"
          using case_assms(2) case_assms(3) ind_hyp by auto
        then show "\<exists>z'. evt x2 # z = tt2T z' \<and> (\<exists>w. (\<exists>p q. w = (p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q) \<and> p \<lesssim>\<^sub>C x \<and> q \<lesssim>\<^sub>C [Event x2]\<^sub>E # y') \<and> z' \<in> w)"
          apply (auto) apply (rule_tac x="[Event x2]\<^sub>E # z'" in exI, auto)
          apply (rule_tac x="p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C [Event x2]\<^sub>E # q" in exI, auto)
           apply (rule_tac x="p" in exI, rule_tac x="[Event x2]\<^sub>E # q" in exI, auto)
          apply (case_tac p rule:ttWF.cases, auto)
          using x2_notin_A by blast+
      qed
    qed
  qed
qed  

lemma ttproc2F_ParCompTT_eq_ParCompF_trace4:
  "\<And>p q. y \<in> p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q \<Longrightarrow> ttWF p \<Longrightarrow> ttWF q \<Longrightarrow>
    \<exists> p' q'. p' \<lesssim>\<^sub>C p \<and> q' \<lesssim>\<^sub>C q \<and> tt2T y \<in> tt2T p' \<lbrakk>insert tick (evt ` A)\<rbrakk>\<^sup>T\<^sub>F tt2T q'"
proof (auto)
  fix p q
  assume "y \<in> p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q" "ttWF p" "ttWF q"
  then have "ttWF y"
    using merge_traces_wf by blast
  then show "\<And>p q. y \<in> p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q \<Longrightarrow> ttWF p \<Longrightarrow> ttWF q \<Longrightarrow>
    \<exists>p'. p' \<lesssim>\<^sub>C p \<and> (\<exists>q'. q' \<lesssim>\<^sub>C q \<and> tt2T y \<in> tt2T p' \<lbrakk>insert tick (evt ` A)\<rbrakk>\<^sup>T\<^sub>F tt2T q')"
  proof (induct y rule:ttWF.induct, auto)
    fix p q
    show "\<exists>p'. p' \<lesssim>\<^sub>C p \<and> (\<exists>q'. q' \<lesssim>\<^sub>C q \<and> [] \<in> tt2T p' \<lbrakk>insert tick (evt ` A)\<rbrakk>\<^sup>T\<^sub>F tt2T q')"
      by (rule_tac x="[]" in exI, auto, rule_tac x="[]" in exI, auto)
  next
    fix X p q
    show "\<exists>p'. p' \<lesssim>\<^sub>C p \<and> (\<exists>q'. q' \<lesssim>\<^sub>C q \<and> [] \<in> tt2T p' \<lbrakk>insert tick (evt ` A)\<rbrakk>\<^sup>T\<^sub>F tt2T q')"
      by (rule_tac x="[]" in exI, auto, rule_tac x="[]" in exI, auto)
  next
    fix p q
    assume "[[Tick]\<^sub>E] \<in> p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q"
    then have "p = [[Tick]\<^sub>E] \<and> q = [[Tick]\<^sub>E]"
      by (cases "(p,q)" rule:ttWF2.cases, auto)
    then show "\<exists>p'. p' \<lesssim>\<^sub>C p \<and> (\<exists>q'. q' \<lesssim>\<^sub>C q \<and> [tick] \<in> tt2T p' \<lbrakk>insert tick (evt ` A)\<rbrakk>\<^sup>T\<^sub>F tt2T q')"
      by (rule_tac x="[[Tick]\<^sub>E]" in exI, auto, rule_tac x="[[Tick]\<^sub>E]" in exI, auto)
  next
    fix e \<sigma> p q
    assume ind_hyp: "\<And>p q. \<sigma> \<in> p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q \<Longrightarrow> ttWF p \<Longrightarrow> ttWF q \<Longrightarrow>
      \<exists>p'. p' \<lesssim>\<^sub>C p \<and> (\<exists>q'. q' \<lesssim>\<^sub>C q \<and> tt2T \<sigma> \<in> tt2T p' \<lbrakk>insert tick (evt ` A)\<rbrakk>\<^sup>T\<^sub>F tt2T q')"
    assume case_assms: "[Event e]\<^sub>E # \<sigma> \<in> p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q" "ttWF p" "ttWF q"
    then have "(\<exists> p'. p = [Event e]\<^sub>E # p' \<and> \<sigma> \<in> (p' \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q) \<and> ttWF p' \<and> e \<notin> A)
      \<or> (\<exists> q'. q = [Event e]\<^sub>E # q' \<and> \<sigma> \<in> (p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q') \<and> ttWF q' \<and> e \<notin> A)
      \<or> (\<exists> p' q'. p = [Event e]\<^sub>E # p' \<and> q = [Event e]\<^sub>E # q' \<and> \<sigma> \<in> (p' \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q') \<and> ttWF p' \<and> ttWF q' \<and> e \<in> A)"
      by (cases "(p,q)" rule:ttWF2.cases, auto)
    then show "\<exists>p'. p' \<lesssim>\<^sub>C p \<and> (\<exists>q'. q' \<lesssim>\<^sub>C q \<and> evt e # tt2T \<sigma> \<in> tt2T p' \<lbrakk>insert tick (evt ` A)\<rbrakk>\<^sup>T\<^sub>F tt2T q')"
    proof auto
      fix p'
      assume case_assms2: "p = [Event e]\<^sub>E # p'" "\<sigma> \<in> p' \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q" "ttWF p'" "e \<notin> A"
      then have "\<exists>p'a. p'a \<lesssim>\<^sub>C p' \<and> (\<exists>q'. q' \<lesssim>\<^sub>C q \<and> tt2T \<sigma> \<in> tt2T p'a \<lbrakk>insert tick (evt ` A)\<rbrakk>\<^sup>T\<^sub>F tt2T q')"
        using case_assms(3) ind_hyp by blast
      then show "\<exists>p'a. p'a \<lesssim>\<^sub>C [Event e]\<^sub>E # p' \<and> (\<exists>q'. q' \<lesssim>\<^sub>C q \<and> evt e # tt2T \<sigma> \<in> tt2T p'a \<lbrakk>insert tick (evt ` A)\<rbrakk>\<^sup>T\<^sub>F tt2T q')"
        apply auto apply (rule_tac x="[Event e]\<^sub>E # p'a" in exI, auto, rule_tac x="q'" in exI, auto)
        apply (case_tac q' rule:ttWF.cases, auto)
        using case_assms2(4) evt_notin_image merge_traceF_comm apply fastforce
        using case_assms2(4) evt_notin_image merge_traceF_comm apply fastforce
        using case_assms2(4) evt_notin_image merge_traceF_comm apply fastforce
        apply (case_tac "ea \<in> A")
        using case_assms2(4) evt_notin_image merge_traceF_comm apply fastforce
        apply (smt Un_iff case_assms2(4) evt_notin_image mem_Collect_eq merge_traceF.simps(5))
        using case_assms2(4) evt_notin_image merge_traceF_comm by fastforce+
    next
      fix q'
      assume case_assms2: "q = [Event e]\<^sub>E # q'" "\<sigma> \<in> p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q'" "ttWF q'" "e \<notin> A"
      then have "\<exists>p'. p' \<lesssim>\<^sub>C p \<and> (\<exists>q'a. q'a \<lesssim>\<^sub>C q' \<and> tt2T \<sigma> \<in> tt2T p' \<lbrakk>insert tick (evt ` A)\<rbrakk>\<^sup>T\<^sub>F tt2T q'a)"
        using case_assms(2) ind_hyp by blast
      then show "\<exists>p'. p' \<lesssim>\<^sub>C p \<and> (\<exists>q'a. q'a \<lesssim>\<^sub>C [Event e]\<^sub>E # q' \<and> evt e # tt2T \<sigma> \<in> tt2T p' \<lbrakk>insert tick (evt ` A)\<rbrakk>\<^sup>T\<^sub>F tt2T q'a)"
        apply auto apply (rule_tac x="p'" in exI, auto, rule_tac x="[Event e]\<^sub>E # q'a" in exI, auto)
        apply (case_tac p' rule:ttWF.cases, auto)
        using case_assms2(4) evt_notin_image merge_traceF_comm apply fastforce
        using case_assms2(4) evt_notin_image merge_traceF_comm apply fastforce
        using case_assms2(4) evt_notin_image merge_traceF_comm apply fastforce
        apply (case_tac "ea \<in> A")
        using case_assms2(4) evt_notin_image merge_traceF_comm apply fastforce
        apply (smt Un_iff case_assms2(4) evt_notin_image mem_Collect_eq merge_traceF.simps(5))
        using case_assms2(4) evt_notin_image merge_traceF_comm by fastforce+
    next
      fix p' q'
      assume case_assms2: "p = [Event e]\<^sub>E # p'" "q = [Event e]\<^sub>E # q'" "\<sigma> \<in> p' \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q'" "ttWF p'" "ttWF q'" "e \<in> A"
      then have "\<exists>p'a. p'a \<lesssim>\<^sub>C p' \<and> (\<exists>q'a. q'a \<lesssim>\<^sub>C q' \<and> tt2T \<sigma> \<in> tt2T p'a \<lbrakk>insert tick (evt ` A)\<rbrakk>\<^sup>T\<^sub>F tt2T q'a)"
        by (simp add: ind_hyp)
      then show "\<exists>p'a. p'a \<lesssim>\<^sub>C [Event e]\<^sub>E # p' \<and> (\<exists>q'a. q'a \<lesssim>\<^sub>C [Event e]\<^sub>E # q' \<and> evt e # tt2T \<sigma> \<in> tt2T p'a \<lbrakk>insert tick (evt ` A)\<rbrakk>\<^sup>T\<^sub>F tt2T q'a)"
        by (auto, rule_tac x="[Event e]\<^sub>E # p'a" in exI, auto, rule_tac x="[Event e]\<^sub>E # q'a" in exI, auto simp add: case_assms2(6))
    qed
  next
    fix X \<sigma> p q
    show "\<exists>p'. p' \<lesssim>\<^sub>C p \<and> (\<exists>q'. q' \<lesssim>\<^sub>C q \<and> [] \<in> tt2T p' \<lbrakk>insert tick (evt ` A)\<rbrakk>\<^sup>T\<^sub>F tt2T q')"
      by (rule_tac x="[]" in exI, auto, rule_tac x="[]" in exI, auto)
  qed
qed

lemma ttproc2F_ParCompTT_eq_ParCompF_trace5:
  "\<And> a b p q. Some (a, b) = tt2F y \<Longrightarrow> y \<in> p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q \<Longrightarrow> ttWF y \<Longrightarrow> ttWF p \<Longrightarrow> ttWF q \<Longrightarrow>
    \<exists> p' q' s t. p' \<lesssim>\<^sub>C p \<and> q' \<lesssim>\<^sub>C q \<and> a \<in> (s \<lbrakk>insert tick (evt ` A)\<rbrakk>\<^sup>T\<^sub>F t) \<and>
    ((\<exists>Aa G. Aa \<subseteq> A \<and> b = G \<union> evt ` Aa \<and> s @ [tick] = tt2T p' \<and> Some (t, G) = tt2F q')
      \<or> (\<exists>Aa G. Aa \<subseteq> A \<and> b = G \<union> evt ` Aa \<and> t @ [tick] = tt2T q' \<and> Some (s, G) = tt2F p')
      \<or> (\<exists> c d. b = c \<union> d \<and> c - insert tick (evt ` A) = d - insert tick (evt ` A) \<and> Some (s, c) = tt2F p' \<and> Some (t, d) = tt2F q'))"
proof (induct y rule:ttWF.induct, auto)
  fix X p q
  assume "[[X]\<^sub>R] \<in> p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q" "ttWF p" "ttWF q"
  then show " \<exists>p'. p' \<lesssim>\<^sub>C p \<and> (\<exists>q'. q' \<lesssim>\<^sub>C q \<and> (\<exists>s t. [] \<in> (s \<lbrakk>insert tick (evt ` A)\<rbrakk>\<^sup>T\<^sub>F t) \<and>
        ((\<exists>Aa\<subseteq>A. \<exists>G. {x. ttevt2F x \<in> X} = G \<union> evt ` Aa \<and> s @ [tick] = tt2T p' \<and> Some (t, G) = tt2F q') \<or>
         (\<exists>Aa\<subseteq>A. \<exists>G. {x. ttevt2F x \<in> X} = G \<union> evt ` Aa \<and> t @ [tick] = tt2T q' \<and> Some (s, G) = tt2F p') \<or>
         (\<exists>c d. {x. ttevt2F x \<in> X} = c \<union> d \<and>
            c - insert tick (evt ` A) = d - insert tick (evt ` A) \<and>
            Some (s, c) = tt2F p' \<and> Some (t, d) = tt2F q'))))"
  proof (cases "(p,q)" rule:ttWF2.cases, simp_all)
    fix Xa Y
    assume "X \<subseteq> Xa \<union> Y \<and> {e \<in> Y. e \<noteq> Tock \<and> e \<noteq> Tick \<and> e \<notin> Event ` A} = {e \<in> Xa. e \<noteq> Tock \<and> e \<noteq> Tick \<and> e \<notin> Event ` A}"
    then show "\<exists>p'. p' \<lesssim>\<^sub>C [[Xa]\<^sub>R] \<and> (\<exists>q'. q' \<lesssim>\<^sub>C [[Y]\<^sub>R] \<and> (\<exists>s t. [] \<in> (s \<lbrakk>insert tick (evt ` A)\<rbrakk>\<^sup>T\<^sub>F t) \<and> 
           ((\<exists>Aa\<subseteq>A. \<exists>G. {x. ttevt2F x \<in> X} = G \<union> evt ` Aa \<and> s @ [tick] = tt2T p' \<and> Some (t, G) = tt2F q') \<or>
            (\<exists>Aa\<subseteq>A. \<exists>G. {x. ttevt2F x \<in> X} = G \<union> evt ` Aa \<and> t @ [tick] = tt2T q' \<and> Some (s, G) = tt2F p') \<or>
            (\<exists>c d. {x. ttevt2F x \<in> X} = c \<union> d \<and>
              c - insert tick (evt ` A) = d - insert tick (evt ` A) \<and>
              Some (s, c) = tt2F p' \<and> Some (t, d) = tt2F q'))))"
    proof (rule_tac x="[[Xa \<inter> X]\<^sub>R]" in exI, safe, simp_all, rule_tac x="[[Y \<inter> X]\<^sub>R]" in exI, safe, simp_all, safe, simp_all, blast)
      fix x
      assume A: "X \<subseteq> Xa \<union> Y \<and> {e \<in> Y. e \<noteq> Tock \<and> e \<noteq> Tick \<and> e \<notin> Event ` A} = {e \<in> Xa. e \<noteq> Tock \<and> e \<noteq> Tick \<and> e \<notin> Event ` A}"
      assume "x \<notin> evt ` A" "ttevt2F x \<in> Xa" "x \<noteq> tick"
      then have "ttevt2F x \<in> {e \<in> Xa. e \<noteq> Tock \<and> e \<noteq> Tick \<and> e \<notin> Event ` A}"
        by (cases x, auto)
      then have "ttevt2F x \<in> {e \<in> Y. e \<noteq> Tock \<and> e \<noteq> Tick \<and> e \<notin> Event ` A}"
        using A by auto
      then show "ttevt2F x \<in> Y"
        by auto
    next
      fix x
      assume A: "X \<subseteq> Xa \<union> Y \<and> {e \<in> Y. e \<noteq> Tock \<and> e \<noteq> Tick \<and> e \<notin> Event ` A} = {e \<in> Xa. e \<noteq> Tock \<and> e \<noteq> Tick \<and> e \<notin> Event ` A}"
      assume "x \<notin> evt ` A" "ttevt2F x \<in> Y" "x \<noteq> tick"
      then have "ttevt2F x \<in> {e \<in> Y. e \<noteq> Tock \<and> e \<noteq> Tick \<and> e \<notin> Event ` A}"
        by (cases x, auto)
      then have "ttevt2F x \<in> {e \<in> Xa. e \<noteq> Tock \<and> e \<noteq> Tick \<and> e \<notin> Event ` A}"
        using A by auto
      then show "ttevt2F x \<in> Xa"
        by auto
    qed
  next
    fix Xa
    assume "\<exists>Aa\<subseteq>A. X = Xa \<union> Event ` Aa"
    then show "\<exists>p'. p' \<lesssim>\<^sub>C [[Xa]\<^sub>R] \<and> (\<exists>q'. q' \<lesssim>\<^sub>C [[Tick]\<^sub>E] \<and> (\<exists>s t. [] \<in> (s \<lbrakk>insert tick (evt ` A)\<rbrakk>\<^sup>T\<^sub>F t) \<and> 
                   ((\<exists>Aa\<subseteq>A. \<exists>G. {x. ttevt2F x \<in> X} = G \<union> evt ` Aa \<and> s @ [tick] = tt2T p' \<and> Some (t, G) = tt2F q') \<or>
                          (\<exists>Aa\<subseteq>A. \<exists>G. {x. ttevt2F x \<in> X} = G \<union> evt ` Aa \<and> t @ [tick] = tt2T q' \<and> Some (s, G) = tt2F p') \<or>
                          (\<exists>c d. {x. ttevt2F x \<in> X} = c \<union> d \<and>
                            c - insert tick (evt ` A) = d - insert tick (evt ` A) \<and>
                            Some (s, c) = tt2F p' \<and> Some (t, d) = tt2F q'))))"
      apply (rule_tac x="[[Xa]\<^sub>R]" in exI, safe, simp_all)
      apply (rule_tac x="[[Tick]\<^sub>E]" in exI, safe, simp_all)
      apply (rule_tac x="[]" in exI, rule_tac x="[]" in exI, safe, simp_all)
      apply (rule_tac x="Aa" in exI, safe, simp_all)
      apply (metis Un_iff evt.exhaust image_iff ttevent.distinct(3) ttevent.inject ttevt2F.simps(1) ttevt2F.simps(2))
      by blast
  next
    fix Y
    assume "\<exists>Aa\<subseteq>A. X = Y \<union> Event ` Aa"
    then show "\<exists>p'. p' \<lesssim>\<^sub>C [[Tick]\<^sub>E] \<and> (\<exists>q'. q' \<lesssim>\<^sub>C [[Y]\<^sub>R] \<and> (\<exists>s t. [] \<in> (s \<lbrakk>insert tick (evt ` A)\<rbrakk>\<^sup>T\<^sub>F t) \<and>
                   ((\<exists>Aa\<subseteq>A. \<exists>G. {x. ttevt2F x \<in> X} = G \<union> evt ` Aa \<and> s @ [tick] = tt2T p' \<and> Some (t, G) = tt2F q') \<or>
                    (\<exists>Aa\<subseteq>A. \<exists>G. {x. ttevt2F x \<in> X} = G \<union> evt ` Aa \<and> t @ [tick] = tt2T q' \<and> Some (s, G) = tt2F p') \<or>
                    (\<exists>c d. {x. ttevt2F x \<in> X} = c \<union> d \<and>
                      c - insert tick (evt ` A) = d - insert tick (evt ` A) \<and>
                      Some (s, c) = tt2F p' \<and> Some (t, d) = tt2F q'))))"
      apply (rule_tac x="[[Tick]\<^sub>E]" in exI, safe, simp_all)
      apply (rule_tac x="[[Y]\<^sub>R]" in exI, safe, simp_all)
      apply (rule_tac x="[]" in exI, rule_tac x="[]" in exI, safe, simp_all)
      apply (rule_tac x="Aa" in exI, safe, simp_all)
      apply (metis Un_iff evt.exhaust image_iff ttevent.distinct(3) ttevent.inject ttevt2F.simps(1) ttevt2F.simps(2))
      by blast
  qed
next
  fix e \<sigma> a b p q
  assume ind_hyp: "\<And>a b p q. Some (a, b) = tt2F \<sigma> \<Longrightarrow> \<sigma> \<in> p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q \<Longrightarrow> ttWF p \<Longrightarrow> ttWF q \<Longrightarrow>
         \<exists>p'. p' \<lesssim>\<^sub>C p \<and> (\<exists>q'. q' \<lesssim>\<^sub>C q \<and> (\<exists>s t. a \<in> (s \<lbrakk>insert tick (evt ` A)\<rbrakk>\<^sup>T\<^sub>F t) \<and>
            ((\<exists>Aa\<subseteq>A. \<exists>G. b = G \<union> evt ` Aa \<and> s @ [tick] = tt2T p' \<and> Some (t, G) = tt2F q') \<or>
             (\<exists>Aa\<subseteq>A. \<exists>G. b = G \<union> evt ` Aa \<and> t @ [tick] = tt2T q' \<and> Some (s, G) = tt2F p') \<or>
             (\<exists>c d. b = c \<union> d \<and> c - insert tick (evt ` A) = d - insert tick (evt ` A) \<and> Some (s, c) = tt2F p' \<and> Some (t, d) = tt2F q'))))"

  assume "[Event e]\<^sub>E # \<sigma> \<in> p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q" "ttWF \<sigma>" "ttWF p" "ttWF q"
    "Some (a, b) = (case tt2F \<sigma> of None \<Rightarrow> None | Some fl \<Rightarrow> Some (evt e # fst fl, snd fl))"
  then have case_assms2: "[Event e]\<^sub>E # \<sigma> \<in> p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q" "ttWF \<sigma>" "ttWF p" "ttWF q" "Some (a, b) = tt2F ([Event e]\<^sub>E # \<sigma>)"
    by (auto)

  obtain a' where a'_assms: "a = evt e # a' \<and> Some (a', b) = tt2F \<sigma>"
    using case_assms2(5) by (cases a, auto, (cases "tt2F \<sigma>", auto)+)
  
  have "(\<exists> p' q'. e \<in> A \<and> p = [Event e]\<^sub>E # p' \<and> q = [Event e]\<^sub>E # q' \<and> \<sigma> \<in> p' \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q')
    \<or> (\<exists> p'. e \<notin> A \<and> p = [Event e]\<^sub>E # p' \<and> \<sigma> \<in> p' \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q)
    \<or> (\<exists> q'. e \<notin> A \<and> q = [Event e]\<^sub>E # q' \<and> \<sigma> \<in> p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q')"
    using case_assms2(1) by (cases "(p,q)" rule:ttWF2.cases, auto)
  then show "\<exists>p'. p' \<lesssim>\<^sub>C p \<and> (\<exists>q'. q' \<lesssim>\<^sub>C q \<and> (\<exists>s t. a \<in> (s \<lbrakk>insert tick (evt ` A)\<rbrakk>\<^sup>T\<^sub>F t) \<and>
       ((\<exists>Aa\<subseteq>A. \<exists>G. b = G \<union> evt ` Aa \<and> s @ [tick] = tt2T p' \<and> Some (t, G) = tt2F q') \<or>
        (\<exists>Aa\<subseteq>A. \<exists>G. b = G \<union> evt ` Aa \<and> t @ [tick] = tt2T q' \<and> Some (s, G) = tt2F p') \<or>
        (\<exists>c d. b = c \<union> d \<and> c - insert tick (evt ` A) = d - insert tick (evt ` A) \<and> Some (s, c) = tt2F p' \<and> Some (t, d) = tt2F q'))))"
  proof auto
    fix p' q'
    assume case_assms3: "e \<in> A" "p = [Event e]\<^sub>E # p'" "\<sigma> \<in> p' \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q'" "q = [Event e]\<^sub>E # q'"

    have "\<exists>p'a. p'a \<lesssim>\<^sub>C p' \<and> (\<exists>q'a. q'a \<lesssim>\<^sub>C q' \<and> (\<exists>s t. a' \<in> (s \<lbrakk>insert tick (evt ` A)\<rbrakk>\<^sup>T\<^sub>F t) \<and>
         ((\<exists>Aa\<subseteq>A. \<exists>G. b = G \<union> evt ` Aa \<and> s @ [tick] = tt2T p'a \<and> Some (t, G) = tt2F q'a) \<or>
          (\<exists>Aa\<subseteq>A. \<exists>G. b = G \<union> evt ` Aa \<and> t @ [tick] = tt2T q'a \<and> Some (s, G) = tt2F p'a) \<or>
          (\<exists>c d. b = c \<union> d \<and> c - insert tick (evt ` A) = d - insert tick (evt ` A) \<and> Some (s, c) = tt2F p'a \<and> Some (t, d) = tt2F q'a))))"
      using ind_hyp[where p=p', where q=q', where b=b, where a=a']
      using a'_assms case_assms2(3) case_assms2(4) case_assms3 by auto 
    then show "\<exists>p'a. p'a \<lesssim>\<^sub>C [Event e]\<^sub>E # p' \<and> (\<exists>q'a. q'a \<lesssim>\<^sub>C [Event e]\<^sub>E # q' \<and> (\<exists>s t. a \<in> (s \<lbrakk>insert tick (evt ` A)\<rbrakk>\<^sup>T\<^sub>F t) \<and>
         ((\<exists>Aa\<subseteq>A. \<exists>G. b = G \<union> evt ` Aa \<and> s @ [tick] = tt2T p'a \<and> Some (t, G) = tt2F q'a) \<or>
          (\<exists>Aa\<subseteq>A. \<exists>G. b = G \<union> evt ` Aa \<and> t @ [tick] = tt2T q'a \<and> Some (s, G) = tt2F p'a) \<or>
          (\<exists>c d. b = c \<union> d \<and> c - insert tick (evt ` A) = d - insert tick (evt ` A) \<and> Some (s, c) = tt2F p'a \<and> Some (t, d) = tt2F q'a))))"
      apply clarsimp
      apply (rule_tac x="[Event e]\<^sub>E # p'a" in exI, clarsimp)
      apply (rule_tac x="[Event e]\<^sub>E # q'a" in exI, clarsimp)
      apply (rule_tac x="evt e # s" in exI, rule_tac x="evt e # t" in exI, safe, simp_all add: a'_assms case_assms3(1))
      by (metis (lifting) fst_conv option.simps(5) snd_conv)+
  next
    fix p'
    assume case_assms3: "e \<notin> A" "\<sigma> \<in> p' \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q" "p = [Event e]\<^sub>E # p'"

    have "\<exists>p'a. p'a \<lesssim>\<^sub>C p' \<and> (\<exists>q'. q' \<lesssim>\<^sub>C q \<and> (\<exists>s t. a' \<in> (s \<lbrakk>insert tick (evt ` A)\<rbrakk>\<^sup>T\<^sub>F t) \<and>
          ((\<exists>Aa\<subseteq>A. \<exists>G. b = G \<union> evt ` Aa \<and> s @ [tick] = tt2T p'a \<and> Some (t, G) = tt2F q') \<or>
           (\<exists>Aa\<subseteq>A. \<exists>G. b = G \<union> evt ` Aa \<and> t @ [tick] = tt2T q' \<and> Some (s, G) = tt2F p'a) \<or>
           (\<exists>c d. b = c \<union> d \<and> c - insert tick (evt ` A) = d - insert tick (evt ` A) \<and> Some (s, c) = tt2F p'a \<and> Some (t, d) = tt2F q'))))"
      using ind_hyp[where p=p', where q=q, where b=b, where a=a']
      using a'_assms case_assms2(3) case_assms2(4) case_assms3(2) case_assms3(3) by auto
    then show "\<exists>p'a. p'a \<lesssim>\<^sub>C [Event e]\<^sub>E # p' \<and> (\<exists>q'. q' \<lesssim>\<^sub>C q \<and> (\<exists>s t. a \<in> (s \<lbrakk>insert tick (evt ` A)\<rbrakk>\<^sup>T\<^sub>F t) \<and>
        ((\<exists>Aa\<subseteq>A. \<exists>G. b = G \<union> evt ` Aa \<and> s @ [tick] = tt2T p'a \<and> Some (t, G) = tt2F q') \<or>
         (\<exists>Aa\<subseteq>A. \<exists>G. b = G \<union> evt ` Aa \<and> t @ [tick] = tt2T q' \<and> Some (s, G) = tt2F p'a) \<or>
         (\<exists>c d. b = c \<union> d \<and> c - insert tick (evt ` A) = d - insert tick (evt ` A) \<and> Some (s, c) = tt2F p'a \<and> Some (t, d) = tt2F q'))))"
      apply clarsimp
      apply (rule_tac x="[Event e]\<^sub>E # p'a" in exI, clarsimp)
      apply (rule_tac x="q'" in exI, clarsimp)
      apply (rule_tac x="evt e # s" in exI, rule_tac x="t" in exI, safe, simp_all)
      apply (case_tac t, simp_all)
      using a'_assms case_assms3(1) evt_notin_image merge_traceF_comm apply fastforce
      apply (smt Un_iff a'_assms case_assms3(1) evt_notin_image mem_Collect_eq merge_traceF.simps(5) merge_traceF.simps(7))
      apply (case_tac t, simp_all)
      using a'_assms case_assms3(1) evt_notin_image merge_traceF_comm apply fastforce
      apply (smt Un_iff a'_assms case_assms3(1) evt_notin_image mem_Collect_eq merge_traceF.simps(5) merge_traceF.simps(7))
      apply (metis (mono_tags, lifting) fst_conv option.simps(5) snd_conv)
      apply (case_tac t, simp_all)
      using a'_assms case_assms3(1) evt_notin_image merge_traceF_comm apply fastforce
      apply (smt Un_iff a'_assms case_assms3(1) evt_notin_image mem_Collect_eq merge_traceF.simps(5) merge_traceF.simps(7))
      by (metis (no_types, lifting) fst_conv option.simps(5) snd_conv)
  next
    fix q'
    assume case_assms3: "e \<notin> A" "\<sigma> \<in> p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q'" "q = [Event e]\<^sub>E # q'"

    have "\<exists>p'. p' \<lesssim>\<^sub>C p \<and> (\<exists>q'a. q'a \<lesssim>\<^sub>C q' \<and> (\<exists>s t. a' \<in> (s \<lbrakk>insert tick (evt ` A)\<rbrakk>\<^sup>T\<^sub>F t) \<and>
          ((\<exists>Aa\<subseteq>A. \<exists>G. b = G \<union> evt ` Aa \<and> s @ [tick] = tt2T p' \<and> Some (t, G) = tt2F q'a) \<or>
           (\<exists>Aa\<subseteq>A. \<exists>G. b = G \<union> evt ` Aa \<and> t @ [tick] = tt2T q'a \<and> Some (s, G) = tt2F p') \<or>
           (\<exists>c d. b = c \<union> d \<and> c - insert tick (evt ` A) = d - insert tick (evt ` A) \<and> Some (s, c) = tt2F p' \<and> Some (t, d) = tt2F q'a))))"
      using ind_hyp[where p=p, where q=q', where b=b, where a=a']
      using a'_assms case_assms2(3) case_assms2(4) case_assms3(2) case_assms3(3) by auto
    then show "\<exists>p'. p' \<lesssim>\<^sub>C p \<and> (\<exists>q'a. q'a \<lesssim>\<^sub>C [Event e]\<^sub>E # q' \<and> (\<exists>s t. a \<in> (s \<lbrakk>insert tick (evt ` A)\<rbrakk>\<^sup>T\<^sub>F t) \<and>
        ((\<exists>Aa\<subseteq>A. \<exists>G. b = G \<union> evt ` Aa \<and> s @ [tick] = tt2T p' \<and> Some (t, G) = tt2F q'a) \<or>
         (\<exists>Aa\<subseteq>A. \<exists>G. b = G \<union> evt ` Aa \<and> t @ [tick] = tt2T q'a \<and> Some (s, G) = tt2F p') \<or>
         (\<exists>c d. b = c \<union> d \<and> c - insert tick (evt ` A) = d - insert tick (evt ` A) \<and> Some (s, c) = tt2F p' \<and> Some (t, d) = tt2F q'a))))"
      apply clarsimp
      apply (rule_tac x="p'" in exI, clarsimp)
      apply (rule_tac x="[Event e]\<^sub>E # q'a" in exI, clarsimp)
      apply (rule_tac x="s" in exI, rule_tac x="evt e # t" in exI, safe, simp_all)
      apply (case_tac s, simp_all)
      using a'_assms case_assms3(1) evt_notin_image merge_traceF_comm apply fastforce
      apply (smt Un_iff a'_assms case_assms3(1) evt_notin_image mem_Collect_eq merge_traceF.simps(5) merge_traceF.simps(6))
      apply (metis (mono_tags, lifting) fst_conv option.simps(5) snd_conv)
      apply (case_tac s, simp_all)
      using a'_assms case_assms3(1) evt_notin_image merge_traceF_comm apply fastforce
      apply (smt Un_iff a'_assms case_assms3(1) evt_notin_image mem_Collect_eq merge_traceF.simps(5) merge_traceF.simps(6))
      apply (case_tac s, simp_all)
      using a'_assms case_assms3(1) evt_notin_image merge_traceF_comm apply fastforce
      apply (smt Un_iff a'_assms case_assms3(1) evt_notin_image mem_Collect_eq merge_traceF.simps(5) merge_traceF.simps(6))
      apply (case_tac s, simp_all)
      using a'_assms case_assms3(1) evt_notin_image merge_traceF_comm apply fastforce
      apply (smt Un_iff a'_assms case_assms3(1) evt_notin_image mem_Collect_eq merge_traceF.simps(5) merge_traceF.simps(6))
      by (metis (no_types, lifting) fst_conv option.simps(5) snd_conv)
  qed
qed

thm ttproc2F_def
thm ParCompF_def

lemma ttproc2F_ParCompTT_eq_ParCompF:
  assumes ttWF_P: "TTwf P" and TT0_P: "TT0 P" and TT1_P: "TT1 P" and TT2_P: "TT2 P" and TT3_P: "TT3 P"
      and ttWF_Q: "TTwf Q" and TT0_Q: "TT0 Q" and TT1_Q: "TT1 Q" and TT2_Q: "TT2 Q" and TT3_Q: "TT3 Q"
  shows "((ttproc2F P) \<lbrakk>A\<rbrakk>\<^sub>F (ttproc2F Q)) =  ttproc2F (P \<lbrakk>A\<rbrakk>\<^sub>C Q)" 
  unfolding ttproc2F_def ParCompTT_def ParCompF_def 
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

  have y_wf: "ttWF y"
    using TTwf_def assm3 ttWF_P by blast
  have ya_wf: "ttWF ya"
    using TTwf_def assm6 ttWF_Q by blast

  show "\<exists>y. Some (a, Y \<union> Z) = tt2F y \<and> (\<exists>x. (\<exists>p\<in>P. \<exists>q\<in>Q. x = p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q) \<and> y \<in> x)"
    by (metis (mono_tags, lifting) assm1 assm2 assm3 assm4 assm5 assm6 ttproc2F_ParCompTT_eq_ParCompF_trace1 y_wf ya_wf)
next
  fix a b s t y ya G Aa
  assume case_assms: "a \<in> s \<lbrakk>insert tick (evt ` A)\<rbrakk>\<^sup>T\<^sub>F t" "s @ [tick] = tt2T y" "y \<in> P" "Some (t, G) = tt2F ya" "ya \<in> Q" "Aa \<subseteq> A"

  have "\<exists>z. Some (a, G \<union> evt ` Aa) = tt2F z \<and> (\<exists>w. (\<exists>p q. w = (p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q) \<and> p \<lesssim>\<^sub>C y \<and> q \<lesssim>\<^sub>C ya) \<and> z \<in> w)"
    by (meson TTwf_def case_assms(1) case_assms(2) case_assms(3) case_assms(4) case_assms(5) case_assms(6) ttWF_P ttWF_Q ttproc2F_ParCompTT_eq_ParCompF_trace2)
  then show "\<exists>y. Some (a, G \<union> evt ` Aa) = tt2F y \<and> (\<exists>x. (\<exists>p\<in>P. \<exists>q\<in>Q. x = p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q) \<and> y \<in> x)"
    using TT1_P TT1_Q case_assms(3) case_assms(5) unfolding TT1_def by (auto, blast)
next
  fix a b s t y ya Aa
  assume case_assms: "a \<in> s \<lbrakk>insert tick (evt ` A)\<rbrakk>\<^sup>T\<^sub>F t" "t @ [tick] = tt2T y" "y \<in> Q" "Some (s, b) = tt2F ya" "ya \<in> P" "Aa \<subseteq> A"

  have "a \<in> t \<lbrakk>insert tick (evt ` A)\<rbrakk>\<^sup>T\<^sub>F s"
    by (simp add: case_assms(1) merge_traceF_comm)
  then have "\<exists>z. Some (a, b \<union> evt ` Aa) = tt2F z \<and> (\<exists>w. (\<exists>p q. w = (p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q) \<and> p \<lesssim>\<^sub>C ya \<and> q \<lesssim>\<^sub>C y) \<and> z \<in> w)"
    by (metis TTwf_def case_assms(2) case_assms(3) case_assms(4) case_assms(5) case_assms(6) merge_traces_comm ttWF_P ttWF_Q ttproc2F_ParCompTT_eq_ParCompF_trace2)
  then show "\<exists>y. Some (a, b \<union> evt ` Aa) = tt2F y \<and> (\<exists>x. (\<exists>p\<in>P. \<exists>q\<in>Q. x = p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q) \<and> y \<in> x)"
    using TT1_P TT1_Q case_assms(3) case_assms(5) unfolding TT1_def by (auto, blast)
next
  fix x X s t y ya
  assume case_assms: "x \<in> tt2T y \<lbrakk>insert tick (evt ` A)\<rbrakk>\<^sup>T\<^sub>F tt2T ya" "y \<in> P" "ya \<in> Q"

  have "\<exists>z'. x = tt2T z' \<and> (\<exists>w. (\<exists>p q. w = (p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q) \<and> p \<lesssim>\<^sub>C y \<and> q \<lesssim>\<^sub>C ya) \<and> z' \<in> w)"
    by (meson TTwf_def case_assms(1) case_assms(2) case_assms(3) ttWF_P ttWF_Q ttproc2F_ParCompTT_eq_ParCompF_trace3)
  then show "\<exists>y. x = tt2T y \<and> (\<exists>x. (\<exists>p\<in>P. \<exists>q\<in>Q. x = p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q) \<and> y \<in> x)"
    using TT1_P TT1_Q case_assms unfolding TT1_def by (auto, blast)
next
  fix x y xa p q
  assume case_assms: "y \<in> p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q" "p \<in> P" "q \<in> Q"
 
  have "\<exists>p' q'. p' \<lesssim>\<^sub>C p \<and> q' \<lesssim>\<^sub>C q \<and> tt2T y \<in> tt2T p' \<lbrakk>insert tick (evt ` A)\<rbrakk>\<^sup>T\<^sub>F tt2T q'"
    by (meson TTwf_def case_assms(1) case_assms(2) case_assms(3) ttWF_P ttWF_Q ttproc2F_ParCompTT_eq_ParCompF_trace4)
  then show "tt2T y \<in> \<Union>{s \<lbrakk>insert tick (evt ` A)\<rbrakk>\<^sup>T\<^sub>F t |s t. (\<exists>y. s = tt2T y \<and> y \<in> P) \<and> (\<exists>y. t = tt2T y \<and> y \<in> Q)}"
    using case_assms TT1_P TT1_Q unfolding TT1_def by (auto, metis)
next
  fix a b y x p q
  assume case_assms: "Some (a, b) = tt2F y" "y \<in> p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q" "p \<in> P" "q \<in> Q"

  thm ttproc2F_ParCompTT_eq_ParCompF_trace5[where a=a, where b=b, where y=y, where p=p, where q=q, where A=A]
  have "ttWF y \<and> ttWF p \<and> ttWF q"
    by (meson TTwf_def case_assms(2) case_assms(3) case_assms(4) merge_traces_wf ttWF_P ttWF_Q)
  then have "\<exists>p' q' s t. p' \<lesssim>\<^sub>C p \<and> q' \<lesssim>\<^sub>C q \<and> a \<in> (s \<lbrakk>insert tick (evt ` A)\<rbrakk>\<^sup>T\<^sub>F t) \<and>
   ((\<exists>Aa G. Aa \<subseteq> A \<and> b = G \<union> evt ` Aa \<and> s @ [tick] = tt2T p' \<and> Some (t, G) = tt2F q') \<or>
    (\<exists>Aa G. Aa \<subseteq> A \<and> b = G \<union> evt ` Aa \<and> t @ [tick] = tt2T q' \<and> Some (s, G) = tt2F p') \<or>
    (\<exists>c d. b = c \<union> d \<and> c - insert tick (evt ` A) = d - insert tick (evt ` A) \<and> Some (s, c) = tt2F p' \<and> Some (t, d) = tt2F q'))"
    using ttproc2F_ParCompTT_eq_ParCompF_trace5 case_assms by blast
  then have "\<exists>p' q' s t. p' \<in> P \<and> q' \<in> Q \<and> a \<in> (s \<lbrakk>insert tick (evt ` A)\<rbrakk>\<^sup>T\<^sub>F t) \<and>
   ((\<exists>Aa G. Aa \<subseteq> A \<and> b = G \<union> evt ` Aa \<and> s @ [tick] = tt2T p' \<and> Some (t, G) = tt2F q') \<or>
    (\<exists>Aa G. Aa \<subseteq> A \<and> b = G \<union> evt ` Aa \<and> t @ [tick] = tt2T q' \<and> Some (s, G) = tt2F p') \<or>
    (\<exists>c d. b = c \<union> d \<and> c - insert tick (evt ` A) = d - insert tick (evt ` A) \<and> Some (s, c) = tt2F p' \<and> Some (t, d) = tt2F q'))"
      using TT1_P TT1_Q case_assms unfolding TT1_def apply (safe, simp_all) by meson+
  then show "\<nexists>s t Aa. Aa \<subseteq> A \<and> (\<exists>G. b = G \<union> evt ` Aa \<and>
               a \<in> (s \<lbrakk>insert tick (evt ` A)\<rbrakk>\<^sup>T\<^sub>F t) \<and> (\<exists>y. t @ [tick] = tt2T y \<and> y \<in> Q) \<and> (\<exists>y. Some (s, G) = tt2F y \<and> y \<in> P)) \<Longrightarrow>
       \<nexists>s t Aa. Aa \<subseteq> A \<and> (\<exists>G. b = G \<union> evt ` Aa \<and>
               a \<in> (s \<lbrakk>insert tick (evt ` A)\<rbrakk>\<^sup>T\<^sub>F t) \<and> (\<exists>y. s @ [tick] = tt2T y \<and> y \<in> P) \<and> (\<exists>y. Some (t, G) = tt2F y \<and> y \<in> Q)) \<Longrightarrow>
       \<exists>Y Z. b = Y \<union> Z \<and> Y - insert tick (evt ` A) = Z - insert tick (evt ` A) \<and>
             (\<exists>s. (\<exists>y. Some (s, Y) = tt2F y \<and> y \<in> P) \<and> (\<exists>t. (\<exists>y. Some (t, Z) = tt2F y \<and> y \<in> Q) \<and> a \<in> s \<lbrakk>insert tick (evt ` A)\<rbrakk>\<^sup>T\<^sub>F t))"
    by (safe, simp_all, metis+)
qed

end