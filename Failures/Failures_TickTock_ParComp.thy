theory Failures_TickTock_ParComp

imports
  Failures_TickTock
begin

lemma merge_traces_imp_mergeF:
  assumes "z \<in> p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q" "None \<noteq> tt2F z" "tt2F p = None"
  shows "(tt2T p \<lbrakk>insert tick (evt ` A)\<rbrakk>\<^sup>T\<^sub>F tt2T q) = {}"
  using assms  apply (induct p A q arbitrary:z rule:merge_traces.induct, simp_all)
  apply (smt Collect_empty_eq equals0D merge_traceF.simps(2) merge_traceF.simps(3) option.simps(4) tt2F.simps(2) tt2F.simps(3))
         apply (smt Collect_empty_eq equals0D evt.distinct(1) insertI1 merge_traceF.simps(6) merge_traceF.simps(8) option.simps(4) tt2F.simps(2) tt2F.simps(3)) 
  (* possibly true? *)
  oops

lemma merge_traces_imp_mergeF':
  assumes "Some (a, b) = tt2F z" "tt2F p \<noteq> None" "tt2F q \<noteq> None" "z \<in> p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q"
  shows "a \<in> (tt2T p \<lbrakk>insert tick (evt ` A)\<rbrakk>\<^sup>T\<^sub>F tt2T q)"
  using assms apply (induct p A q rule:merge_traces.induct, simp_all)
          apply auto
                apply (cases a, auto)
  using assms(1) tt2F_some_exists apply blast
        apply (case_tac ac, auto)
         apply (case_tac \<sigma>, auto)
         apply (case_tac ac, auto)
  (* possibly true? *)
  oops

lemma ttevt2F_diff_no_Tock:
  assumes "Tock \<notin> ttevt2F`Y" "Tock \<notin> ttevt2F`Z" "Y - ({tick}\<union>(evt ` A)) = Z - ({tick}\<union>(evt ` A))"
  shows "(ttevt2F`Y - ((Event`A) \<union> {Tock,Tick})) = (ttevt2F`Z - ((Event ` A) \<union> {Tock, Tick}))"
  using assms apply safe
  by (metis (no_types, lifting) Diff_subset image_eqI insert_Diff insert_Diff_if insert_iff insert_is_Un subsetD ttevt2F.simps(2) ttevt2F_evt_set)+

(* Q: Would the following rule help? It's a variant of rev_induct. *)

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

lemma tt2F_None_merge_traces_last_no_Tick:
  assumes "(p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q) \<noteq> {}" "tt2F p = None" "last p \<noteq> [Tick]\<^sub>E"
  shows "tt2F`(p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q) = {None}"
  using assms  (* FIXME: ugly proof *)
  apply (induct p A q rule:merge_traces.induct, simp_all add:image_def tt2F_None_merge_traces', safe, simp_all add:image_def , safe)
  apply (metis (no_types, lifting) merge_traces_comm option.case_eq_if option.simps(3) tt2F_None_merge_traces')
  using merge_traces_comm tt2F_None_merge_traces' apply fastforce
  apply (smt insert_absorb mem_Collect_eq option.case_eq_if option.collapse option.distinct(1) option.simps(15) set_empty_eq these_empty_eq these_insert_Some tt2F_None_merge_traces')
  (* possibly true *)
  oops

lemma evt_notin_image [intro]:
  assumes "f \<notin> A"
  shows "evt f \<notin> insert tick (evt ` A)"
  using assms by auto

thm rev_little_induct
thm rev_induct

(* Attempts below at proving failures (fst) *)

lemma ttproc2F_ParCompTT_failures_subseteq_ParCompF:
  assumes ttWFx_P: "ttWFx P" and TT0_P: "TT0 P" and TT1_P: "TT1 P" and TT2_P: "TT2 P" and TT3_P: "TT3 P"
      and ttWFx_Q: "ttWFx Q" and TT0_Q: "TT0 Q" and TT1_Q: "TT1 Q" and TT2_Q: "TT2 Q" and TT3_Q: "TT3 Q"
  shows "fst ((ttproc2F P) \<lbrakk>A\<rbrakk>\<^sub>F (ttproc2F Q)) \<subseteq> fst (ttproc2F (P \<lbrakk>A\<rbrakk>\<^sub>C Q))" 
  using assms unfolding ttproc2F_def ParCompTT_def ParCompF_def 
proof (simp_all, safe)
  oops

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

(* Attempts below at proving traces (snd) *)

lemma ttproc2F_ExtChoiceTT_traces_subseteq_ExtChoiceF:
  assumes ttWFx_P: "ttWFx P" and TT0_P: "TT0 P" and TT1_P: "TT1 P" and TT2_P: "TT2 P" and TT3_P: "TT3 P"
      and ttWFx_Q: "ttWFx Q" and TT0_Q: "TT0 Q" and TT1_Q: "TT1 Q" and TT2_Q: "TT2 Q" and TT3_Q: "TT3 Q"
  shows "snd (ttproc2F (P \<lbrakk>A\<rbrakk>\<^sub>C Q)) \<subseteq> snd ((ttproc2F P) \<lbrakk>A\<rbrakk>\<^sub>F (ttproc2F Q))" 
  using assms unfolding ttproc2F_def ParCompTT_def ParCompF_def 
proof (auto)
  fix y p q
  assume assm1: "y \<in> p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q"
  and    assm2: "p \<in> P"
  and    assm3: "q \<in> Q"

  obtain l where l:"l = (p,A,q)"
    by auto

  obtain Z where Z:"Z = insert tick (evt ` A)"
    by auto

  have evt_A_Z:"\<And>f. f \<notin> A \<Longrightarrow> evt f \<notin> Z"
    using Z by blast
    (* Induction on y using merge_traces.induct isn't really feasible, as in general
       y \<in> [] \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C xs @ [x] doesn't imply y \<in> [] \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C xs.

       Induction on p and q using forward rules also doesn't work well, because
       x # xs \<in> p doesn't imply xs \<in> p. Below I attempted to use the reverse rule. *)

  have  "\<exists>x. (\<exists>s t. x = s \<lbrakk>Z\<rbrakk>\<^sup>T\<^sub>F t \<and> (\<exists>y. s = tt2T y \<and> y \<in> P) \<and> (\<exists>y. t = tt2T y \<and> y \<in> Q)) \<and> tt2T y \<in> x"
    using assm1 assm2 assm3 l
  proof (induct p q rule:rev_little_induct)
      case 1
      then show ?case 
        apply auto
        by fastforce
    next
      case (2 x xs ys)
      then show ?case using 2 apply auto
        apply (cases l rule:merge_traces.cases, auto)
                            apply fastforce
          apply (rule_tac x="{[]}" in exI, simp)
                            apply (metis (no_types, hide_lams) merge_traceF.simps(1) tt2T.simps(5))
   apply (rule_tac x="{[]}" in exI, simp)

                            apply (metis TT0_Q TT0_TT1_empty TT1_Q merge_traceF.simps(1) tt2T.simps(3) tt2T.simps(5))
                            apply (rule_tac x="{evt f # tt2T s}" in exI, simp)
                            apply (rule_tac x="tt2T [[X]\<^sub>R]" in exI, simp)
                            apply (rule_tac x="tt2T ([Event f]\<^sub>E # \<sigma>)" in exI, simp)
                      apply (auto simp add:evt_A_Z)
        sorry
    next
      case (3 y ys xs)
      then show ?case sorry
    next
      case (4 x y xs ys)
      then show ?case sorry
    qed

lemma tt2F_last_refusal:
  assumes "Some (s, Y) = tt2F y" "ttWF y"
  shows "\<exists>R. last y = [R]\<^sub>R \<and> Y = {x. ttevt2F x \<in> R}"
  using assms apply (induct y arbitrary: Y s rule:rev_induct, auto)
  apply (case_tac x, auto)
  oops

lemma ttproc2F_ParCompTT_eq_ParCompF:
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

  (* FIXME: tbc *)
 oops

end