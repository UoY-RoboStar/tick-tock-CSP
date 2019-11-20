theory TickTock_Max_Pri

imports
  "TickTock.TickTock_Core"
  "Utils.Event_Priority"
begin

section \<open> Prioritise for maximal TickTock \<close>

definition prirefMaxTT :: "('e ttevent) partialorder \<Rightarrow> ('e ttevent) set \<Rightarrow> ('e ttevent) set" where
"prirefMaxTT p Z = {z. z \<notin> Z \<longrightarrow> (\<exists>b. b \<notin> Z \<and> z <\<^sup>*p b)}"

fun priMaxTT :: "('e ttevent) partialorder \<Rightarrow> ('e ttobs) list \<Rightarrow> ('e ttobs) list \<Rightarrow> ('e ttobs) list \<Rightarrow> ('e ttobs) list set \<Rightarrow> bool" where
"priMaxTT p [] [] s Q = True" |
"priMaxTT p [[R]\<^sub>R] [[S]\<^sub>R] s Q = (prirefMaxTT p S = R)" |
"priMaxTT p ([R]\<^sub>R # [Tock]\<^sub>E # aa) ([S]\<^sub>R # [Tock]\<^sub>E # zz) s Q = ((R = prirefMaxTT p S) \<and> Tock \<notin> R \<and> priMaxTT p aa zz (s @ [[S]\<^sub>R,[Tock]\<^sub>E]) Q)" |
"priMaxTT p ([e\<^sub>1]\<^sub>E # aa) ([e\<^sub>2]\<^sub>E # zz) s Q
 = 
 (e\<^sub>1 = e\<^sub>2 \<and> priMaxTT p aa zz (s @ [[e\<^sub>1]\<^sub>E]) Q \<and>
  (maximal(p,e\<^sub>2) 
   \<or> 
  (\<exists>Z. s @ [[Z]\<^sub>R] \<in> Q \<and> e\<^sub>2 \<notin> Z \<and> \<not>(\<exists>b. b \<notin> Z \<and> e\<^sub>2 <\<^sup>*p b))))" |
"priMaxTT p x y s Q = False"

definition PriMax :: "('e ttevent) partialorder \<Rightarrow> ('e ttobs) list set \<Rightarrow> ('e ttobs) list set" where
"PriMax p P = {t|s t. s \<in> P \<and> priMaxTT p t s [] P}"

subsection \<open> Properties of PriMax and priMaxTT \<close>

lemma priMaxTT_extend_both_refusal_ttWF:
  assumes "priMaxTT p xs ys s P" "ttWF (ys @ [[S]\<^sub>R])"  "prirefMaxTT p S = R"
  shows "priMaxTT p (xs @ [[R]\<^sub>R]) (ys @ [[S]\<^sub>R]) s P"
  using assms apply (induct p xs ys s P rule:priMaxTT.induct, auto)  
  apply (metis ttWF.simps(10) ttWF.simps(4) ttWF.simps(6) ttevent.exhaust neq_Nil_conv snoc_eq_iff_butlast)
  by (metis ttWF.simps(10) ttWF.simps(4) ttWF.simps(6) ttevent.exhaust neq_Nil_conv snoc_eq_iff_butlast)             

lemma priMaxTT_extend_both_tock_refusal_ttWF:
  assumes "priMaxTT p xs ys s P" "ttWF (ys @ [[S]\<^sub>R,[Tock]\<^sub>E])" "prirefMaxTT p S = R" "Tock \<notin> R"
  shows "priMaxTT p (xs @ [[R]\<^sub>R,[Tock]\<^sub>E]) (ys @ [[S]\<^sub>R,[Tock]\<^sub>E]) s P"
  using assms apply (induct p xs ys s P rule:priMaxTT.induct, auto)
  by (metis append_Cons append_Nil ttWF.simps(10) ttWF.simps(4) ttWF.simps(6) ttevent.exhaust neq_Nil_conv)+

lemma maximal_Tock_then_not_prirefMaxTT [simp]:
  assumes "maximal(p,Tock)" "Tock \<notin> S"
  shows "Tock \<notin> prirefMaxTT p S"
  using assms unfolding prirefMaxTT_def apply auto
  by (simp add: some_higher_not_maximal)

lemma priMaxTT_extend_both_events_eq_size_maximal_ttWF:
  assumes "priMaxTT p xs ys s P" "ttWF (ys @ [[e\<^sub>1]\<^sub>E])" "maximal(p,e\<^sub>1)" "size xs = size ys" "ttWFx_trace (ys @ [[e\<^sub>1]\<^sub>E])"
  shows "priMaxTT p (xs @ [[e\<^sub>1]\<^sub>E]) (ys @ [[e\<^sub>1]\<^sub>E]) s P"
  using assms apply (induct p xs ys s P rule:priMaxTT.induct, auto)
    apply (cases e\<^sub>1, auto)
  using ttWFx_trace_cons_imp_cons
  apply (metis append_Nil ttWF.simps(10) ttWF.simps(4) ttWF.simps(6) ttWF_prefix_is_ttWF ttevent.exhaust list.exhaust)
  using ttWFx_trace_cons_imp_cons by (metis append_Nil ttWF.simps(10) ttWF.simps(4) ttWF.simps(6) ttWF_prefix_is_ttWF ttevent.exhaust list.exhaust)
  
lemma priMaxTT_extend_both_events_maximal_ttWF:
  assumes "priMaxTT p xs ys s P" "ttWF (xs @ [[e\<^sub>1]\<^sub>E])" "ttWF (ys @ [[e\<^sub>1]\<^sub>E])" "maximal(p,e\<^sub>1)" "ttWFx_trace (ys @ [[e\<^sub>1]\<^sub>E])"
  shows "priMaxTT p (xs @ [[e\<^sub>1]\<^sub>E]) (ys @ [[e\<^sub>1]\<^sub>E]) s P"
  using assms apply (induct p xs ys s P rule:priMaxTT.induct, auto)
    apply (cases e\<^sub>1, auto)
  using ttWFx_trace_cons_imp_cons by (metis append_Nil ttWF.simps(10) ttWF.simps(4) ttWF.simps(6) ttWF_prefix_is_ttWF ttevent.exhaust list.exhaust)+

lemma priMaxTT_same_length:
  assumes "priMaxTT p xs ys s P"
  shows "size xs = size ys"
  using assms by (induct p xs ys s P rule:priMaxTT.induct, auto)

lemma priMaxTT_imp_butlast_of_priMaxTTs:
  assumes "priMaxTT p ar xs [] P"
  shows "priMaxTT p (List.butlast ar) (List.butlast xs) [] P"
  using assms apply (induct p ar xs _ P rule:priMaxTT.induct, auto)  
  apply (metis neq_Nil_conv priMaxTT.simps(46))
      apply (metis neq_Nil_conv priMaxTT.simps(28))
     apply (metis neq_Nil_conv priMaxTT.simps(46))
    apply (metis neq_Nil_conv priMaxTT.simps(28))
   apply (metis neq_Nil_conv priMaxTT.simps(46))
  by (metis neq_Nil_conv priMaxTT.simps(28))

lemma priMaxTT_imp_one_butlast_of_priMaxTT:
  assumes "priMaxTT p ar (xs @ [x]) [] P"
  shows "priMaxTT p (List.butlast ar) xs [] P"
  using assms priMaxTT_imp_butlast_of_priMaxTTs
  by fastforce

lemma prirefMaxTT_imp_not_exists_higher_pri:
  assumes "(R = prirefMaxTT p S)" "e\<^sub>2 \<notin> R"
  shows "\<not>(\<exists>b. b \<notin> S \<and> e\<^sub>2 <\<^sup>*p b)"
  using assms unfolding prirefMaxTT_def by auto

lemma priMaxTT_both_cons_extend_refusal_imp_prefix:
  assumes "priMaxTT p (x @ [[xs]\<^sub>R]) (y @ [[ys]\<^sub>R]) zs P" 
  shows "priMaxTT p x y zs P"
  using assms apply (induct p x y zs P arbitrary:xs ys rule:priMaxTT.induct, auto)
  apply (metis list.exhaust priMaxTT.simps(57) snoc_eq_iff_butlast)
  by (metis list.exhaust priMaxTT.simps(68) snoc_eq_iff_butlast)

lemma priMaxTT_cannot_extend_refusal_rhs:
  assumes "priMaxTT p x y zs P"
  shows "\<not> priMaxTT p x (y @ [[ys]\<^sub>R]) zs P"
  using assms by (induct p x y zs P rule:priMaxTT.induct, auto)

lemma priMaxTT_cannot_extend_refusal_lhs:
  assumes "priMaxTT p x y zs P"
  shows "\<not> priMaxTT p (x @ [[xs]\<^sub>R]) y zs P"
  using assms by (induct p x y zs P rule:priMaxTT.induct, auto)

lemma not_priMaxTT_concat_refTock:
  assumes "v \<noteq> []"
  shows "\<not> priMaxTT p (v @ [[x]\<^sub>R, [Tock]\<^sub>E]) [[y]\<^sub>R, [Tock]\<^sub>E] z P"
  using assms apply (induct p v "[]:: 'a ttobs list" z P rule:priMaxTT.induct, auto)
  apply (case_tac va, auto, case_tac vb, auto, case_tac x1, auto)
   apply (metis append_Cons append_Nil neq_Nil_conv priMaxTT.simps(28))
  apply (case_tac va, auto, case_tac va, auto, case_tac a, auto, case_tac x1, auto)
  by (metis append_Cons append_Nil neq_Nil_conv priMaxTT.simps(28))

lemma not_priMaxTT_concat_refTock':
  assumes "v \<noteq> []"
  shows "\<not> priMaxTT p [[y]\<^sub>R, [Tock]\<^sub>E] (v @ [[x]\<^sub>R, [Tock]\<^sub>E]) z P"
  using assms apply (induct p "[]:: 'a ttobs list" v z P rule:priMaxTT.induct, auto)
   apply (case_tac va, auto, case_tac va, auto, case_tac a, auto, case_tac x1, auto)
   apply (metis append_Cons neq_Nil_conv priMaxTT.simps(46) self_append_conv2)
  apply (case_tac va, auto, case_tac vb, auto, case_tac x1, auto)
  by (metis append_Cons neq_Nil_conv priMaxTT.simps(46) self_append_conv2)

lemma priMaxTT_both_concat_refTock_imp_prefixes:
  assumes "priMaxTT p (xs @ [[s]\<^sub>R, [Tock]\<^sub>E]) (ys @ [[t]\<^sub>R, [Tock]\<^sub>E]) z P" 
  shows "priMaxTT p xs ys z P"
  using assms apply (induct p xs ys z P arbitrary:s t rule:priMaxTT.induct, auto)
  using not_priMaxTT_concat_refTock 
     apply (metis append_Cons list.discI)     
  using not_priMaxTT_concat_refTock 
    apply fastforce
  using not_priMaxTT_concat_refTock'
  by (metis append_Cons list.distinct(1))+

lemma priMaxTT_length_eq:
  assumes "priMaxTT p xs ys z P"
  shows "List.length xs = List.length ys"
  using assms by (induct p xs ys z P rule:priMaxTT.induct, auto)

lemma ttWF_cons_simp:
  assumes "e\<^sub>2 \<noteq> Tock" "e\<^sub>2 \<noteq> Tick" "ttWF ([e\<^sub>2]\<^sub>E # zz)"
  shows "ttWF(zz)"
  using assms
  using ttWF.elims(2) by blast

lemma priMaxTT_concat_dist1:
  assumes "ttWF (ys @ [[S]\<^sub>R,[Tock]\<^sub>E])"
  shows
   "priMaxTT p (xs @ [[R]\<^sub>R,[Tock]\<^sub>E]) (ys @ [[S]\<^sub>R,[Tock]\<^sub>E]) s P
    =
    (priMaxTT p xs ys s P \<and> priMaxTT p [[R]\<^sub>R,[Tock]\<^sub>E] [[S]\<^sub>R,[Tock]\<^sub>E] (s @ ys) P)"
  using assms apply auto 
      apply (induct p xs ys s P rule:priMaxTT.induct, auto)
  using priMaxTT_both_concat_refTock_imp_prefixes apply blast+
         apply (metis append_Cons list.distinct(1) not_priMaxTT_concat_refTock)
  using not_priMaxTT_concat_refTock apply fastforce
       apply (metis append_Cons list.distinct(1) not_priMaxTT_concat_refTock')
      apply (metis append_Cons list.distinct(1) not_priMaxTT_concat_refTock')
     apply (induct p xs ys s P rule:priMaxTT.induct, auto)
          apply (metis ttWF.simps(1) ttWF.simps(4) ttWF.simps(6) ttWF.simps(8) ttevent.exhaust neq_Nil_conv)
         apply (metis append.left_neutral ttWF.simps(4) ttWF.simps(6) ttWF.simps(8) ttWF_prefix_is_ttWF ttevent.exhaust neq_Nil_conv)
        apply (metis Cons_eq_appendI neq_Nil_conv not_priMaxTT_concat_refTock)
  using not_priMaxTT_concat_refTock apply fastforce
      apply (metis Cons_eq_appendI neq_Nil_conv not_priMaxTT_concat_refTock')
     apply (metis Cons_eq_appendI neq_Nil_conv not_priMaxTT_concat_refTock')
    apply (induct p xs ys s P rule:priMaxTT.induct, auto)
         apply (metis ttWF.simps(1) ttWF.simps(4) ttWF.simps(6) ttWF.simps(8) ttevent.exhaust neq_Nil_conv)
        apply (metis append.left_neutral ttWF.simps(4) ttWF.simps(6) ttWF.simps(8) ttWF_prefix_is_ttWF ttevent.exhaust neq_Nil_conv)
       apply (metis Cons_eq_appendI neq_Nil_conv not_priMaxTT_concat_refTock)
      apply (metis Cons_eq_appendI neq_Nil_conv not_priMaxTT_concat_refTock) 
     apply (metis Cons_eq_appendI neq_Nil_conv not_priMaxTT_concat_refTock')
    apply (metis Cons_eq_appendI neq_Nil_conv not_priMaxTT_concat_refTock')
   apply (induct p xs ys s P rule:priMaxTT.induct, auto)
        apply (metis ttWF.simps(1) ttWF.simps(10) ttWF.simps(4) ttWF.simps(6) ttevent.exhaust neq_Nil_conv)
       apply (metis ttWF.simps(1) ttWF.simps(10) ttWF.simps(4) ttWF.simps(6) ttevent.exhaust neq_Nil_conv)
      apply (metis Cons_eq_appendI neq_Nil_conv not_priMaxTT_concat_refTock)
     apply (metis Cons_eq_appendI neq_Nil_conv not_priMaxTT_concat_refTock)
    apply (metis Cons_eq_appendI neq_Nil_conv not_priMaxTT_concat_refTock')
   apply (metis Cons_eq_appendI neq_Nil_conv not_priMaxTT_concat_refTock')
apply (induct p xs ys s P rule:priMaxTT.induct, auto) 
  apply (metis Cons_eq_appendI priMaxTT.simps(4) priMaxTT_extend_both_tock_refusal_ttWF)
  by (metis ttWF.simps(1) ttWF.simps(10) ttWF.simps(4) ttWF.simps(6) ttevent.exhaust neq_Nil_conv)

lemma not_priMaxTT_simp1 [elim]:
  assumes "v \<noteq> []"
  shows "\<not> priMaxTT p (v @ [a,b]) [c,d] s Q"
  using assms using priMaxTT_length_eq by fastforce

lemma not_priMaxTT_simp2 [simp]:
  shows "\<not> priMaxTT p (x # y @ [a,b]) [c,d] s Q"
  using priMaxTT_length_eq by fastforce

lemma not_priMaxTT_simp2' [simp]:
  shows "\<not> priMaxTT p [c,d] (x # y @ [a,b]) s Q"
  using priMaxTT_length_eq by fastforce

lemma not_priMaxTT_simp3 [simp]:
  shows "\<not> priMaxTT p (x # y # z @ [a,b]) [c,d] s Q"
  using priMaxTT_length_eq by fastforce

lemma not_priMaxTT_simp3' [simp]:
  shows "\<not> priMaxTT p [c,d] (x # y # z @ [a,b]) s Q"
  using priMaxTT_length_eq by fastforce

lemma not_priMaxTT_simp4 [simp]:
  shows "\<not> priMaxTT p [a, b, c] (x # y # z @ [w, u]) s Q"
  using priMaxTT_length_eq by fastforce

lemma not_priMaxTT_simp4' [simp]:
  shows "\<not> priMaxTT p (x # y # z @ [w, u]) [a, b, c]  s Q"
  using priMaxTT_length_eq by fastforce

lemma priMaxTT_concat_dist2:
  assumes "ttWF (ys @ [[S]\<^sub>R,[Tock]\<^sub>E])"
  shows
   "priMaxTT p (xs @ [a,b]) (ys @ [[S]\<^sub>R,[Tock]\<^sub>E]) s P
    =
    (priMaxTT p xs ys s P \<and> priMaxTT p [a,b] [[S]\<^sub>R,[Tock]\<^sub>E] (s @ ys) P)"
  using assms apply auto 
    apply (induct p xs ys s P rule:priMaxTT.induct, auto)
  using ttWF.elims(2) apply blast
  using ttWF.elims(2) apply blast
   apply (induct p xs ys s P rule:priMaxTT.induct, auto)
  using ttWF.elims(2) apply blast
  using ttWF.elims(2) apply blast
  apply (induct p xs ys s P rule:priMaxTT.induct, auto)
  using ttWF.elims(2) apply blast
  using ttWF.elims(2) by blast 

lemma priMaxTT_FIXME1:
  assumes "priMaxTT p (xs @ [a,b]) (ys @ [[S]\<^sub>R, [Tock]\<^sub>E]) s P" "ttWF (ys @ [[S]\<^sub>R,[Tock]\<^sub>E])"
  shows "priMaxTT p [a,b] [[S]\<^sub>R, [Tock]\<^sub>E] (s@ys) P"
  using assms priMaxTT_concat_dist2 by (simp add:priMaxTT_concat_dist2)

lemma priMaxTT_rhs_refTock_imp_no_gt_Tock_pri:
  assumes "priMaxTT p ar (ys @ [[r1]\<^sub>R, [Tock]\<^sub>E]) [] P" "ttWF (ys @ [[r1]\<^sub>R, [Tock]\<^sub>E])"
  shows "\<not>(\<exists>b. b \<notin> r1 \<and> Tock <\<^sup>*p b)"
  using assms 
proof -
  from assms have ll:"List.length ar = List.length (ys @ [[r1]\<^sub>R, [Tock]\<^sub>E])"
    using priMaxTT_length_eq by blast
  then show ?thesis
  using assms(1)
  proof (induct ar rule:rev_induct)
    case Nil
    then show ?case by auto
  next
    case (snoc z zs)
    then show ?case 
    proof (induct zs rule:rev_induct)
      case Nil
      then show ?case by auto
    next
      case (snoc x xs)
      then show ?case 
        apply (case_tac z, auto)
         apply (case_tac x1, auto)
           apply (case_tac x, auto)
            apply (meson assms(2) priMaxTT.simps(50) priMaxTT_FIXME1)
           apply (meson assms(2) priMaxTT.simps(50) priMaxTT_FIXME1)
          apply (case_tac x, auto)
        using assms(2) priMaxTT.simps(47) priMaxTT_FIXME1 apply blast
          apply (metis assms(2) priMaxTT.simps(3) priMaxTT_FIXME1 prirefMaxTT_imp_not_exists_higher_pri)
         apply (case_tac x, auto)
        using assms(2) priMaxTT.simps(52) priMaxTT_FIXME1 apply blast
        using assms(2) priMaxTT.simps(52) priMaxTT_FIXME1 apply blast
        using assms(2) priMaxTT.simps(17) priMaxTT_FIXME1 by blast
    qed
  qed
qed

lemma priMaxTT_nonmax_Tock_imp_exists_refusal:
  assumes "priMaxTT p ar (ys @ [[e1]\<^sub>E]) s P" "e1 \<noteq> Tock"
          "ttWF (ys @ [[e1]\<^sub>E])" "\<not>maximal(p,e1)"
  shows "(\<exists>Z. s @ ys @ [[Z]\<^sub>R] \<in> P \<and> e1 \<notin> Z \<and> \<not>(\<exists>b. b \<notin> Z \<and> e1 <\<^sup>*p b))"
  using assms apply(induct p ar ys s P rule:priMaxTT.induct, auto)
            apply (metis ttWF.simps(1) ttWF.simps(10) ttWF.simps(6) ttWF_cons_simp neq_Nil_conv)
           apply (metis (full_types) append_Nil assms(2) ttWF.simps(10) ttWF.simps(5) ttWF.simps(6) ttWF_cons_simp ttWF_prefix_is_ttWF list.collapse rotate1.simps(2))
          apply (metis ttobs.exhaust priMaxTT.simps(29) priMaxTT.simps(4))
         apply (metis ttobs.exhaust priMaxTT.simps(29) priMaxTT.simps(4))
        apply (metis ttobs.exhaust priMaxTT.simps(29) priMaxTT.simps(4))
       apply (metis ttobs.exhaust priMaxTT.simps(29) priMaxTT.simps(4))
      apply (case_tac va, auto, case_tac vb, auto, case_tac x1, auto, case_tac e1, auto)
  using ttWF.elims(2) apply blast
  using ttobs.exhaust  priMaxTT.simps(29) priMaxTT.simps(4) apply metis
  apply (case_tac v, auto)
  using ttWF.elims(2) by blast+

end