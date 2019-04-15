theory CTockTick_Prioritise
  imports 
    CTockTick_Core
    Event_Priority
begin

subsection \<open>Prioritise for non-subset closed CT.\<close>

definition prirelref :: "('e cttevent) partialorder \<Rightarrow> ('e cttevent) set \<Rightarrow> ('e cttevent) set" where
"prirelref p Z = {z. z \<notin> Z \<longrightarrow> (\<exists>b. b \<notin> Z \<and> z <\<^sup>*p b)}"

fun prirelRef :: "('e cttevent) partialorder \<Rightarrow> ('e cttobs) list \<Rightarrow> ('e cttobs) list \<Rightarrow> ('e cttobs) list \<Rightarrow> ('e cttobs) list set \<Rightarrow> bool" where
"prirelRef p [] [] s Q = True" |
(*"prirelRef p [] [[R]\<^sub>R] s Q = True" |*)
(* Very likely unnecessary case: 
"prirelRef p [] ([S]\<^sub>R # [Tock]\<^sub>E # zz) s Q = ((\<forall>b. (Tock <\<^sup>*p b) \<longrightarrow> b \<in> S) \<and> prirelRef p [] zz (s @ [[S]\<^sub>R,[Tock]\<^sub>E]) Q)" |*)
"prirelRef p [[R]\<^sub>R] [[S]\<^sub>R] s Q = (prirelref p S = R)" |
"prirelRef p ([R]\<^sub>R # [Tock]\<^sub>E # aa) ([S]\<^sub>R # [Tock]\<^sub>E # zz) s Q = ((R = prirelref p S) \<and> Tock \<notin> R \<and> prirelRef p aa zz (s @ [[S]\<^sub>R,[Tock]\<^sub>E]) Q)" |
"prirelRef p ([e\<^sub>1]\<^sub>E # aa) ([e\<^sub>2]\<^sub>E # zz) s Q
 = 
 (e\<^sub>1 = e\<^sub>2 \<and> prirelRef p aa zz (s @ [[e\<^sub>1]\<^sub>E]) Q \<and>
  (maximal(p,e\<^sub>2) 
   \<or> 
  (\<exists>Z. s @ [[Z]\<^sub>R] \<in> Q \<and> e\<^sub>2 \<notin> Z \<and> \<not>(\<exists>b. b \<notin> Z \<and> e\<^sub>2 <\<^sup>*p b))))" |
"prirelRef p x y s Q = False"

lemma prirelRef_extend_both_refusal_ttWF:
  assumes "prirelRef p xs ys s P" "ttWF (ys @ [[S]\<^sub>R])"  "prirelref p S = R"
  shows "prirelRef p (xs @ [[R]\<^sub>R]) (ys @ [[S]\<^sub>R]) s P"
  using assms apply (induct p xs ys s P rule:prirelRef.induct, auto)  
  apply (metis ttWF.simps(10) ttWF.simps(4) ttWF.simps(6) cttevent.exhaust neq_Nil_conv snoc_eq_iff_butlast)
  by (metis ttWF.simps(10) ttWF.simps(4) ttWF.simps(6) cttevent.exhaust neq_Nil_conv snoc_eq_iff_butlast)             
(*
lemma prirelRef_extend_both_refusal_ttWF:
  assumes "prirelRef p xs ys s P" "ttWF (xs @ [[R]\<^sub>R])" "ttWF (ys @ [[S]\<^sub>R])" "prirelref p S = R" 
          "xs \<noteq> [] \<and> ys \<noteq> [] \<and> List.last xs = [e\<^sub>1]\<^sub>E \<and> List.last ys = [e\<^sub>2]\<^sub>E"
  shows "prirelRef p (xs @ [[R]\<^sub>R]) (ys @ [[S]\<^sub>R]) s P"
  using assms apply (induct p xs ys s P rule:prirelRef.induct)
                      apply simp
                      apply simp
                      apply simp
                      apply auto
  sledgehammer
*)
(*lemma
  assumes "prirelRef p [] zz s Q" "ttWF (zz @ [[S]\<^sub>R])" "ttWF s"
  shows "\<not> prirelRef p [[prirelref p S]\<^sub>R] (zz @ [[S]\<^sub>R]) s Q"
  nitpick
*)
lemma prirelRef_extend_both_tock_refusal_ttWF:
  assumes "prirelRef p xs ys s P" "ttWF (ys @ [[S]\<^sub>R,[Tock]\<^sub>E])" "prirelref p S = R" "Tock \<notin> R"
  shows "prirelRef p (xs @ [[R]\<^sub>R,[Tock]\<^sub>E]) (ys @ [[S]\<^sub>R,[Tock]\<^sub>E]) s P"
  using assms apply (induct p xs ys s P rule:prirelRef.induct, auto)
(*  apply (metis append.assoc append_Cons append_Nil ttWF.simps(1) ttWF.simps(5) ttWF_prefix_is_ttWF prirelRef.simps(3) prirelRef.simps(34) prirelRef_extend_both_refusal_ttWF)
  apply (metis append.assoc append_Cons append_Nil ttWF.simps(1) ttWF.simps(5) ttWF_prefix_is_ttWF prirelRef.simps(3) prirelRef.simps(34) prirelRef_extend_both_refusal_ttWF)
  apply (metis append.assoc append_Cons append_Nil ttWF.simps(5) ttWF_prefix_is_ttWF prirelRef.simps(3) prirelRef.simps(34) prirelRef_extend_both_refusal_ttWF)
*)  by (metis append_Cons append_Nil ttWF.simps(10) ttWF.simps(4) ttWF.simps(6) cttevent.exhaust neq_Nil_conv)+

lemma maximal_Tock_then_not_prirelref [simp]:
  assumes "maximal(p,Tock)" "Tock \<notin> S"
  shows "Tock \<notin> prirelref p S"
  using assms unfolding prirelref_def apply auto
  by (simp add: some_higher_not_maximal)

lemma prirelRef_extend_both_events_eq_size_maximal_ttWF:
  assumes "prirelRef p xs ys s P" "ttWF (ys @ [[e\<^sub>1]\<^sub>E])" "maximal(p,e\<^sub>1)" "size xs = size ys" "CT3_trace (ys @ [[e\<^sub>1]\<^sub>E])"
  shows "prirelRef p (xs @ [[e\<^sub>1]\<^sub>E]) (ys @ [[e\<^sub>1]\<^sub>E]) s P"
  using assms apply (induct p xs ys s P rule:prirelRef.induct, auto)
    apply (cases e\<^sub>1, auto)
  using CT3_trace_cons_imp_cons
  apply (metis append_Nil ttWF.simps(10) ttWF.simps(4) ttWF.simps(6) ttWF_prefix_is_ttWF cttevent.exhaust list.exhaust)
  using CT3_trace_cons_imp_cons by (metis append_Nil ttWF.simps(10) ttWF.simps(4) ttWF.simps(6) ttWF_prefix_is_ttWF cttevent.exhaust list.exhaust)
  
lemma prirelRef_extend_both_events_maximal_ttWF:
  assumes "prirelRef p xs ys s P" "ttWF (xs @ [[e\<^sub>1]\<^sub>E])" "ttWF (ys @ [[e\<^sub>1]\<^sub>E])" "maximal(p,e\<^sub>1)" "CT3_trace (ys @ [[e\<^sub>1]\<^sub>E])"
  shows "prirelRef p (xs @ [[e\<^sub>1]\<^sub>E]) (ys @ [[e\<^sub>1]\<^sub>E]) s P"
  using assms apply (induct p xs ys s P rule:prirelRef.induct, auto)
    apply (cases e\<^sub>1, auto)
  using CT3_trace_cons_imp_cons by (metis append_Nil ttWF.simps(10) ttWF.simps(4) ttWF.simps(6) ttWF_prefix_is_ttWF cttevent.exhaust list.exhaust)+

lemma prirelRef_same_length:
  assumes "prirelRef p xs ys s P"
  shows "size xs = size ys"
  using assms by (induct p xs ys s P rule:prirelRef.induct, auto)

definition priNS :: "('e cttevent) partialorder \<Rightarrow> ('e cttobs) list set \<Rightarrow> ('e cttobs) list set" where
"priNS p P = {t|s t. s \<in> P \<and> prirelRef p t s [] P}"

subsection \<open>Prioritise for subset closed CT.\<close>

end