theory TickTock_Core
  imports Main
begin

section {* Types and Wellformedness Conditions *}

text_raw \<open>\DefineSnippet{ttevent}{\<close>
datatype 'e ttevent = Event 'e  | Tock | Tick
text_raw \<open>}%EndSnippet\<close>
text_raw \<open>\DefineSnippet{ttobs}{\<close>
datatype 'e ttobs = ObsEvent "'e ttevent" ("[_]\<^sub>E") | 
                    Ref "'e ttevent set" ("[_]\<^sub>R") (*| TockRef "'e ttevent set" ("[_]\<^sub>T")*)
text_raw \<open>}%EndSnippet\<close>

text_raw \<open>\DefineSnippet{tttrace}{\<close>
type_synonym 'e tttrace = "'e ttobs list"
text_raw \<open>}%EndSnippet\<close>
text_raw \<open>\DefineSnippet{ttprocess}{\<close>
type_synonym 'e ttprocess = "'e tttrace set"
text_raw \<open>}%EndSnippet\<close>

text_raw \<open>\DefineSnippet{ttWF}{\<close>
fun ttWF :: "'e tttrace \<Rightarrow> bool" where
  "ttWF [] = True" | (* an empty trace is okay*)
  "ttWF [[X]\<^sub>R] = True" | (* a refusal at the end of a trace is okay *)
  "ttWF [[Tick]\<^sub>E] = True" | (* a tick at the end of a trace is okay *)
  "ttWF ([Event e]\<^sub>E # \<sigma>) = ttWF \<sigma>" | (* a (non-tick, non-tock) event is okay *)
  "ttWF ([X]\<^sub>R # [Tock]\<^sub>E # \<sigma>) = (ttWF \<sigma> \<and> Tock \<notin> X)" | (* a tock event on its own is okay, provided its refusal does not contain Tock *)
  "ttWF \<sigma> = False" (* everything else is not allowed *)  
text_raw \<open>}%EndSnippet\<close>

(* weaker version of ttWF for some proofs *)
fun ttWFw :: "'e tttrace \<Rightarrow> bool" where
  "ttWFw [] = True" | (* an empty trace is okay*)
  "ttWFw [[X]\<^sub>R] = True" | (* a refusal at the end of a trace is okay *)
  "ttWFw [[Tick]\<^sub>E] = True" | (* a tick at the end of a trace is okay *)
  "ttWFw ([Event e]\<^sub>E # \<sigma>) = ttWFw \<sigma>" | (* a (non-tick, non-tock) event is okay *)
  "ttWFw ([X]\<^sub>R # [Tock]\<^sub>E # \<sigma>) = ttWFw \<sigma>" | (* a tock event on its own is okay*)
  "ttWFw \<sigma> = False" (* everything else is not allowed *)  

lemma ttWF_imp_ttWFw: "ttWF x \<Longrightarrow> ttWFw x"
  by (induct x rule:ttWFw.induct, auto)

(* not necessary as a function but very useful for its induction rule *)
function ttWF2 :: "'e ttobs list \<Rightarrow> 'e ttobs list \<Rightarrow> bool" where
  "ttWF2 [] [] = True" | 
  "ttWF2 [] [[Y]\<^sub>R] = True" | 
  "ttWF2 [] [[Tick]\<^sub>E] = True" | 
  "ttWF2 [] ([Event f]\<^sub>E # \<sigma>) = ttWF2 [] \<sigma>" | 
  "ttWF2 [] ([Y]\<^sub>R # [Tock]\<^sub>E # \<sigma>) = (ttWF2 [] \<sigma> \<and> Tock \<notin> Y)" | 
  "ttWF2 [[X]\<^sub>R] [] = True" | 
  "ttWF2 [[X]\<^sub>R] [[Y]\<^sub>R] = True" | 
  "ttWF2 [[X]\<^sub>R] [[Tick]\<^sub>E] = True" | 
  "ttWF2 [[X]\<^sub>R] ([Event f]\<^sub>E # \<sigma>) = ttWF2 [] \<sigma>" | 
  "ttWF2 [[X]\<^sub>R] ([Y]\<^sub>R # [Tock]\<^sub>E # \<sigma>) = (ttWF2 [] \<sigma> \<and> Tock \<notin> Y)" | 
  "ttWF2 [[Tick]\<^sub>E] [] = True" | 
  "ttWF2 [[Tick]\<^sub>E] [[Y]\<^sub>R] = True" | 
  "ttWF2 [[Tick]\<^sub>E] [[Tick]\<^sub>E] = True" | 
  "ttWF2 [[Tick]\<^sub>E] ([Event f]\<^sub>E # \<sigma>) = ttWF2 [] \<sigma>" | 
  "ttWF2 [[Tick]\<^sub>E] ([Y]\<^sub>R # [Tock]\<^sub>E # \<sigma>) = (ttWF2 [] \<sigma> \<and> Tock \<notin> Y)" | 
  "ttWF2 ([Event e]\<^sub>E # \<sigma>) [] = ttWF2 \<sigma> []" | 
  "ttWF2 ([Event e]\<^sub>E # \<sigma>) [[Y]\<^sub>R] = ttWF2 \<sigma> []" | 
  "ttWF2 ([Event e]\<^sub>E # \<sigma>) [[Tick]\<^sub>E] = ttWF2 \<sigma> []" | 
  "ttWF2 ([Event e]\<^sub>E # \<rho>) ([Event f]\<^sub>E # \<sigma>) = ttWF2 \<rho> \<sigma>" | 
  "ttWF2 ([Event e]\<^sub>E # \<rho>) ([Y]\<^sub>R # [Tock]\<^sub>E # \<sigma>) = (ttWF2 \<rho> \<sigma> \<and> Tock \<notin> Y)" | 
  "ttWF2 ([X]\<^sub>R # [Tock]\<^sub>E # \<sigma>) [] = (ttWF2 \<sigma> [] \<and> Tock \<notin> X)" | 
  "ttWF2 ([X]\<^sub>R # [Tock]\<^sub>E # \<sigma>) [[Y]\<^sub>R] = (ttWF2 \<sigma> [] \<and> Tock \<notin> X)" | 
  "ttWF2 ([X]\<^sub>R # [Tock]\<^sub>E # \<sigma>) [[Tick]\<^sub>E] = (ttWF2 \<sigma> [] \<and> Tock \<notin> X)" | 
  "ttWF2 ([X]\<^sub>R # [Tock]\<^sub>E # \<rho>) ([Event f]\<^sub>E # \<sigma>) = (ttWF2 \<rho> \<sigma>  \<and> Tock \<notin> X)" | 
  "ttWF2 ([X]\<^sub>R # [Tock]\<^sub>E # \<rho>) ([Y]\<^sub>R # [Tock]\<^sub>E # \<sigma>) = (ttWF2 \<rho> \<sigma> \<and> Tock \<notin> X \<and> Tock \<notin> Y)" |
  "ttWF2 ([X]\<^sub>R # [Tick]\<^sub>E # \<rho>) \<sigma> = False" |
  "ttWF2 ([X]\<^sub>R # [Event e]\<^sub>E # \<rho>) \<sigma> = False" |
  "ttWF2 ([X]\<^sub>R # [Y]\<^sub>R # \<rho>) \<sigma> = False" |
  "ttWF2 \<rho> ([X]\<^sub>R # [Tick]\<^sub>E # \<sigma>) = False" |
  "ttWF2 \<rho> ([X]\<^sub>R # [Event e]\<^sub>E # \<sigma>) = False" |
  "ttWF2 \<rho> ([X]\<^sub>R # [Y]\<^sub>R # \<sigma>) = False" |
  "ttWF2 ([Tick]\<^sub>E # x # \<rho>) \<sigma> = False" |
  "ttWF2 \<rho> ([Tick]\<^sub>E # y # \<sigma>) = False" |
  "ttWF2 ([Tock]\<^sub>E # \<rho>) \<sigma> = False" |
  "ttWF2 \<rho> ([Tock]\<^sub>E # \<sigma>) = False"
  by (pat_completeness, simp_all)
termination by lexicographic_order

lemma ttWF2_ttWF: "ttWF2 x y = (ttWF x \<and> ttWF y)"
  by (induct rule:ttWF2.induct, auto)

function ttWFw2 :: "'e ttobs list \<Rightarrow> 'e ttobs list \<Rightarrow> bool" where
  "ttWFw2 [] [] = True" | 
  "ttWFw2 [] [[Y]\<^sub>R] = True" | 
  "ttWFw2 [] [[Tick]\<^sub>E] = True" | 
  "ttWFw2 [] ([Event f]\<^sub>E # \<sigma>) = ttWFw2 [] \<sigma>" | 
  "ttWFw2 [] ([Y]\<^sub>R # [Tock]\<^sub>E # \<sigma>) = (ttWFw2 [] \<sigma>)" | 
  "ttWFw2 [[X]\<^sub>R] [] = True" | 
  "ttWFw2 [[X]\<^sub>R] [[Y]\<^sub>R] = True" | 
  "ttWFw2 [[X]\<^sub>R] [[Tick]\<^sub>E] = True" | 
  "ttWFw2 [[X]\<^sub>R] ([Event f]\<^sub>E # \<sigma>) = ttWFw2 [] \<sigma>" | 
  "ttWFw2 [[X]\<^sub>R] ([Y]\<^sub>R # [Tock]\<^sub>E # \<sigma>) = (ttWFw2 [] \<sigma>)" | 
  "ttWFw2 [[Tick]\<^sub>E] [] = True" | 
  "ttWFw2 [[Tick]\<^sub>E] [[Y]\<^sub>R] = True" | 
  "ttWFw2 [[Tick]\<^sub>E] [[Tick]\<^sub>E] = True" | 
  "ttWFw2 [[Tick]\<^sub>E] ([Event f]\<^sub>E # \<sigma>) = ttWFw2 [] \<sigma>" | 
  "ttWFw2 [[Tick]\<^sub>E] ([Y]\<^sub>R # [Tock]\<^sub>E # \<sigma>) = (ttWFw2 [] \<sigma>)" | 
  "ttWFw2 ([Event e]\<^sub>E # \<sigma>) [] = ttWFw2 \<sigma> []" | 
  "ttWFw2 ([Event e]\<^sub>E # \<sigma>) [[Y]\<^sub>R] = ttWFw2 \<sigma> []" | 
  "ttWFw2 ([Event e]\<^sub>E # \<sigma>) [[Tick]\<^sub>E] = ttWFw2 \<sigma> []" | 
  "ttWFw2 ([Event e]\<^sub>E # \<rho>) ([Event f]\<^sub>E # \<sigma>) = ttWFw2 \<rho> \<sigma>" | 
  "ttWFw2 ([Event e]\<^sub>E # \<rho>) ([Y]\<^sub>R # [Tock]\<^sub>E # \<sigma>) = (ttWFw2 \<rho> \<sigma>)" | 
  "ttWFw2 ([X]\<^sub>R # [Tock]\<^sub>E # \<sigma>) [] = (ttWFw2 \<sigma> [])" | 
  "ttWFw2 ([X]\<^sub>R # [Tock]\<^sub>E # \<sigma>) [[Y]\<^sub>R] = (ttWFw2 \<sigma> [])" | 
  "ttWFw2 ([X]\<^sub>R # [Tock]\<^sub>E # \<sigma>) [[Tick]\<^sub>E] = (ttWFw2 \<sigma> [])" | 
  "ttWFw2 ([X]\<^sub>R # [Tock]\<^sub>E # \<rho>) ([Event f]\<^sub>E # \<sigma>) = (ttWFw2 \<rho> \<sigma>)" | 
  "ttWFw2 ([X]\<^sub>R # [Tock]\<^sub>E # \<rho>) ([Y]\<^sub>R # [Tock]\<^sub>E # \<sigma>) = (ttWFw2 \<rho> \<sigma>)" |
  "ttWFw2 ([X]\<^sub>R # [Tick]\<^sub>E # \<rho>) \<sigma> = False" |
  "ttWFw2 ([X]\<^sub>R # [Event e]\<^sub>E # \<rho>) \<sigma> = False" |
  "ttWFw2 ([X]\<^sub>R # [Y]\<^sub>R # \<rho>) \<sigma> = False" |
  "ttWFw2 \<rho> ([X]\<^sub>R # [Tick]\<^sub>E # \<sigma>) = False" |
  "ttWFw2 \<rho> ([X]\<^sub>R # [Event e]\<^sub>E # \<sigma>) = False" |
  "ttWFw2 \<rho> ([X]\<^sub>R # [Y]\<^sub>R # \<sigma>) = False" |
  "ttWFw2 ([Tick]\<^sub>E # x # \<rho>) \<sigma> = False" |
  "ttWFw2 \<rho> ([Tick]\<^sub>E # y # \<sigma>) = False" |
  "ttWFw2 ([Tock]\<^sub>E # \<rho>) \<sigma> = False" |
  "ttWFw2 \<rho> ([Tock]\<^sub>E # \<sigma>) = False"
  by (pat_completeness, simp_all)
termination by lexicographic_order

text_raw \<open>\DefineSnippet{ttWFx_trace}{\<close>
fun ttWFx_trace :: "'e tttrace \<Rightarrow> bool" where
  "ttWFx_trace [] = True" |
  "ttWFx_trace [x] = True" |
  "ttWFx_trace ([X]\<^sub>R # [Tock]\<^sub>E # \<rho>) = (Tock \<notin> X \<and> ttWFx_trace \<rho>)" |
  "ttWFx_trace ([va]\<^sub>E # vb # vc) = ttWFx_trace (vb # vc)" |
  "ttWFx_trace (v # [Event vd]\<^sub>E # vc) = ttWFx_trace ([Event vd]\<^sub>E # vc)" |
  "ttWFx_trace (v # [Tick]\<^sub>E # vc) = ttWFx_trace ([Tick]\<^sub>E # vc)" |
  "ttWFx_trace ([vb]\<^sub>R # [va]\<^sub>R # vc) = ttWFx_trace ([va]\<^sub>R # vc)"
text_raw \<open>}%EndSnippet\<close>

lemma ttWF_is_ttWFw_ttWFx: "ttWF x = (ttWFw x \<and> ttWFx_trace x)"
  by (induct x rule:ttWF.induct, auto, (case_tac \<sigma>, auto)+)

lemma ttWF2_is_ttWFw2_ttWFx: "ttWF2 x y = (ttWFw2 x y \<and> ttWFx_trace x \<and> ttWFx_trace y)"
  apply (induct x y rule:ttWF2.induct, auto)
  apply (case_tac \<sigma>, auto, case_tac \<sigma>, auto, case_tac \<sigma>, auto, case_tac \<sigma>, auto, case_tac \<sigma>, auto)
  apply (case_tac \<sigma>, auto, case_tac \<sigma>, auto, case_tac \<sigma>, auto, case_tac \<sigma>, auto, case_tac \<sigma>, auto)
  apply (case_tac \<sigma>, auto, case_tac \<sigma>, auto, case_tac \<rho>, auto, case_tac \<sigma>, auto, case_tac \<sigma>, auto)
  apply (case_tac \<rho>, auto, case_tac \<rho>, auto, case_tac \<rho>, auto, case_tac \<rho>, auto, case_tac \<rho>, auto)
  by (case_tac \<sigma>, auto, case_tac \<sigma>, auto, case_tac \<rho>, auto, case_tac \<rho>, auto, case_tac \<sigma>, auto, case_tac \<sigma>, auto)

text_raw \<open>\DefineSnippet{ttWFx}{\<close>
definition ttWFx :: "'e ttprocess \<Rightarrow> bool" where
  "ttWFx P = (\<forall>\<rho>\<in>P. ttWFx_trace \<rho>)"
text_raw \<open>}%EndSnippet\<close>

lemma ttWFx_append: "ttWF t \<Longrightarrow> ttWFx_trace s \<Longrightarrow> ttWFx_trace t \<Longrightarrow> ttWFx_trace (s @ t)"
  apply (induct s rule:ttWFx_trace.induct, auto)
  apply (induct t, auto)
  apply (case_tac x, auto, case_tac a, auto, case_tac x1, auto)
  done

lemma ttWFx_end_tock: "ttWFx_trace (\<rho>) \<Longrightarrow> ttWFx P \<Longrightarrow> \<rho> @ [[X]\<^sub>R, [Tock]\<^sub>E] \<in> P \<Longrightarrow> Tock \<notin> X"
proof -
  assume "ttWFx P" "\<rho> @ [[X]\<^sub>R, [Tock]\<^sub>E] \<in> P"
  then have "ttWFx_trace (\<rho> @ [[X]\<^sub>R, [Tock]\<^sub>E])"
    unfolding ttWFx_def by auto 
  then show "ttWFx_trace (\<rho>) \<Longrightarrow> Tock \<notin> X"
    by (auto, induct \<rho> rule:ttWFx_trace.induct, auto, case_tac x, auto)
qed

lemma ttWFx_trace_cons_left:
  "ttWFx_trace (xs @ ys) \<Longrightarrow> ttWFx_trace xs"
  by (induct xs rule:ttWFx_trace.induct, auto)

lemma ttWFx_trace_cons_right:
  "ttWFx_trace (xs @ ys) \<Longrightarrow> ttWFx_trace ys"
  apply (induct xs rule:ttWFx_trace.induct, auto)
  apply (case_tac x, auto)
   apply (case_tac x1, auto)
  apply (metis ttWFx_trace.elims(3) ttWFx_trace.simps(4))
  apply (metis ttWFx_trace.elims(3) ttWFx_trace.simps(4))
  apply (metis ttWFx_trace.elims(3) ttWFx_trace.simps(4))
  using ttWFx_trace.elims(2) ttWFx_trace.elims(3) list.discI by auto

lemma ttWFx_any_cons_end_tock:
  assumes "ttWFx P" "\<rho> @ [[X]\<^sub>R, [Tock]\<^sub>E] \<in> P"
  shows "Tock \<notin> X"
proof -
  have "ttWFx_trace ([[X]\<^sub>R, [Tock]\<^sub>E])"
    using assms ttWFx_def ttWFx_trace_cons_right by blast
  then show ?thesis
    by simp
qed

lemma ttWFx_trace_end_refusal_change:
  "ttWFx_trace (t @ [[X]\<^sub>R]) \<Longrightarrow> ttWFx_trace (t @ [[Y]\<^sub>R])"
  by (induct t rule:ttWFx_trace.induct, auto, case_tac x, auto)

lemma ttWFx_trace_cons_imp_cons:
  assumes "ttWFx_trace (a # fl)"
  shows "ttWFx_trace fl"
  using assms apply (cases a, auto)
  apply(induct fl rule:ttWFx_trace.induct, auto)
  apply(induct fl rule:ttWFx_trace.induct, auto)
  by (case_tac va, auto)



section {* Prefix Relations *}

subsection {* Prefix *}

fun tt_prefix :: "'e ttobs list \<Rightarrow> 'e ttobs list \<Rightarrow> bool" (infix "\<le>\<^sub>C" 50) where
  "tt_prefix [] x = True" |
  "tt_prefix (x # xa) (y # ya) = (x = y \<and> tt_prefix xa ya)" |
  "tt_prefix (x # xa) [] = False"

lemma tt_prefix_refl: "x \<le>\<^sub>C x"
  by (induct x, auto)

lemma tt_prefix_trans: "x \<le>\<^sub>C y \<Longrightarrow> y \<le>\<^sub>C z \<Longrightarrow> x \<le>\<^sub>C z"
proof -
  have "\<exists> y. x \<le>\<^sub>C y \<and> y \<le>\<^sub>C z \<Longrightarrow> x \<le>\<^sub>C z"
    apply (induct rule:tt_prefix.induct, auto)
    apply (metis tt_prefix.elims(2) list.discI list.sel(1))
    apply (metis tt_prefix.elims(2) list.discI list.sel(3))
    using tt_prefix.elims(2) by force
  then show "x \<le>\<^sub>C y \<Longrightarrow> y \<le>\<^sub>C z \<Longrightarrow> x \<le>\<^sub>C z" by auto
qed

lemma tt_prefix_antisym: "x \<le>\<^sub>C y \<Longrightarrow> y \<le>\<^sub>C x \<Longrightarrow> x = y"
  using tt_prefix.elims(2) by (induct rule:tt_prefix.induct, auto)

lemma tt_prefix_concat: "x \<le>\<^sub>C x @ y"
  by (induct x, auto)

lemma tt_prefix_same_front: "(x @ y \<le>\<^sub>C x @ z) = (y \<le>\<^sub>C z)"
  by (induct x, auto)

lemma tt_prefix_append_split: "t \<le>\<^sub>C r @ s \<Longrightarrow> t \<le>\<^sub>C r \<or> (\<exists> t'. t = r @ t' \<and> t' \<le>\<^sub>C s)"
  by (induct t r rule:tt_prefix.induct, auto)

lemma tt_prefix_split: "t \<le>\<^sub>C s \<Longrightarrow> \<exists> r. s = t @ r"
  by (induct t s rule:tt_prefix.induct, auto)

lemma self_extension_tt_prefix: 
  "y \<noteq> [] \<Longrightarrow> x @ y \<le>\<^sub>C x \<Longrightarrow> False"
  apply (induct x, auto)
  using tt_prefix.elims(2) by blast

lemma tt_prefix_notfront_is_whole:
  "t \<le>\<^sub>C s @ [x] \<Longrightarrow> \<not> t \<le>\<^sub>C s \<Longrightarrow> t = s @ [x]"
  by (induct t s rule:tt_prefix.induct, auto simp add: tt_prefix_antisym)

lemma event_refusal_split: "s1 @ [X]\<^sub>R # s2 = t1 @ [e]\<^sub>E # t2 \<Longrightarrow>
  (\<exists>t2'. s1 = t1 @ [e]\<^sub>E # t2' \<and> t2' \<le>\<^sub>C t2) \<or> (\<exists> s2'. t1 = s1 @ [X]\<^sub>R # s2' \<and> s2' \<le>\<^sub>C s2)"
  by (induct t1 s1 rule:tt_prefix.induct, auto simp add: tt_prefix_concat, metis append_eq_Cons_conv tt_prefix_concat ttobs.distinct(1) list.inject)

subsection {* Subset *}

fun tt_subset :: "'e ttobs list \<Rightarrow> 'e ttobs list \<Rightarrow> bool" (infix "\<subseteq>\<^sub>C" 50) where
  "tt_subset [] [] = True" |
  "tt_subset ([X]\<^sub>R # xa) ([Y]\<^sub>R # ya) = (X \<subseteq> Y \<and> tt_subset xa ya)" |
  "tt_subset ([x]\<^sub>E # xa) ([y]\<^sub>E # ya) = (x = y \<and> tt_subset xa ya)" |
  "tt_subset x y = False"

lemma tt_subset_refl: "x \<subseteq>\<^sub>C x"
  by (induct x, auto, case_tac a, auto)

lemma tt_subset_trans: "x \<subseteq>\<^sub>C y \<Longrightarrow> y \<subseteq>\<^sub>C z \<Longrightarrow> x \<subseteq>\<^sub>C z"
proof -
  have "\<exists> y. x \<subseteq>\<^sub>C y \<and> y \<subseteq>\<^sub>C z \<Longrightarrow> x \<subseteq>\<^sub>C z"
    apply (induct rule:tt_subset.induct, auto)
    apply (case_tac y, auto, case_tac a, auto)
    apply (case_tac y, auto, case_tac a, auto)
    apply (case_tac yb, auto, case_tac a, auto)
    apply (case_tac yb, auto, case_tac a, auto)
    apply (case_tac y, auto, case_tac y, auto, case_tac a, auto)+
    done  
  then show "x \<subseteq>\<^sub>C y \<Longrightarrow> y \<subseteq>\<^sub>C z \<Longrightarrow> x \<subseteq>\<^sub>C z"
    by auto
qed

lemma tt_subset_antisym: "x \<subseteq>\<^sub>C y \<Longrightarrow> y \<subseteq>\<^sub>C x \<Longrightarrow> x = y"
  by (induct rule:tt_subset.induct, auto)

lemma tt_subset_same_length:
  "\<rho> \<subseteq>\<^sub>C \<sigma> \<Longrightarrow> length \<rho> = length \<sigma>"
  by (induct rule:tt_subset.induct, auto)

lemma tt_prefix_tt_subset: "\<sigma>' \<le>\<^sub>C \<sigma> \<Longrightarrow> \<rho> \<subseteq>\<^sub>C \<sigma> \<Longrightarrow> \<exists> \<rho>'. \<rho>' \<subseteq>\<^sub>C \<sigma>' \<and> \<rho>' \<le>\<^sub>C \<rho>"
proof -
  have "\<And> \<sigma>'. \<sigma>' \<le>\<^sub>C \<sigma> \<Longrightarrow> \<rho> \<subseteq>\<^sub>C \<sigma> \<Longrightarrow> \<exists> \<rho>'. \<rho>' \<subseteq>\<^sub>C \<sigma>' \<and> \<rho>' \<le>\<^sub>C \<rho>"
  proof (induct \<rho> \<sigma> rule:tt_subset.induct, auto)
    fix \<sigma>'
    show "\<sigma>' \<le>\<^sub>C [] \<Longrightarrow> \<exists>\<rho>'. \<rho>' \<subseteq>\<^sub>C \<sigma>' \<and> \<rho>' \<le>\<^sub>C []"
      using tt_subset_refl by blast
  next
    fix X xa Y ya \<sigma>'
    assume assm1: "\<sigma>' \<le>\<^sub>C [Y]\<^sub>R # ya"
    assume assm2: "(\<And>\<sigma>'. \<sigma>' \<le>\<^sub>C ya \<Longrightarrow> \<exists>\<rho>'. \<rho>' \<subseteq>\<^sub>C \<sigma>' \<and> \<rho>' \<le>\<^sub>C xa)"
    assume assm3: "X \<subseteq> Y"
    from assm1 have "\<sigma>' \<le>\<^sub>C [[Y]\<^sub>R] @ ya"
      by simp
    then have "\<sigma>' \<le>\<^sub>C [[Y]\<^sub>R]  \<or> (\<exists>t'. \<sigma>' = [[Y]\<^sub>R] @ t' \<and> t' \<le>\<^sub>C ya)"
      using tt_prefix_append_split by blast
    then have "\<sigma>' \<le>\<^sub>C [[Y]\<^sub>R]  \<or> (\<exists>t'. \<sigma>' = [Y]\<^sub>R # t' \<and> t' \<le>\<^sub>C ya)"
      by simp
    then obtain za where "\<sigma>' = [] \<or> (\<sigma>' = [Y]\<^sub>R # za \<and> za \<le>\<^sub>C ya)"
      by (metis (full_types) assm1 tt_prefix.simps(2) list.exhaust)
    then show "\<exists>\<rho>'. \<rho>' \<subseteq>\<^sub>C \<sigma>' \<and> \<rho>' \<le>\<^sub>C [X]\<^sub>R # xa"
    proof auto
      show "\<sigma>' = [] \<Longrightarrow> \<exists>\<rho>'. \<rho>' \<subseteq>\<^sub>C [] \<and> \<rho>' \<le>\<^sub>C [X]\<^sub>R # xa"
        using tt_prefix.simps(1) tt_subset.simps(1) by blast
    next
      assume "za \<le>\<^sub>C ya" "\<sigma>' = [Y]\<^sub>R # za"
      from this and assm2 obtain \<rho>' where "\<rho>' \<subseteq>\<^sub>C za \<and> \<rho>' \<le>\<^sub>C xa"
        by auto
      then show "\<exists>\<rho>'. \<rho>' \<subseteq>\<^sub>C [Y]\<^sub>R # za \<and> \<rho>' \<le>\<^sub>C [X]\<^sub>R # xa"
        by (rule_tac x="[X]\<^sub>R # \<rho>'" in exI, auto simp add: assm3)
    qed
  next
    fix xa y ya \<sigma>'
    assume assm1: "\<sigma>' \<le>\<^sub>C [y]\<^sub>E # ya"
    assume assm2: "(\<And>\<sigma>'. \<sigma>' \<le>\<^sub>C ya \<Longrightarrow> \<exists>\<rho>'. \<rho>' \<subseteq>\<^sub>C \<sigma>' \<and> \<rho>' \<le>\<^sub>C xa)"
    from assm1 have "\<sigma>' \<le>\<^sub>C [[y]\<^sub>E] @ ya"
      by simp
    then have "\<sigma>' \<le>\<^sub>C [[y]\<^sub>E]  \<or> (\<exists>t'. \<sigma>' = [[y]\<^sub>E] @ t' \<and> t' \<le>\<^sub>C ya)"
      using tt_prefix_append_split by blast
    then have "\<sigma>' \<le>\<^sub>C [[y]\<^sub>E]  \<or> (\<exists>t'. \<sigma>' = [y]\<^sub>E # t' \<and> t' \<le>\<^sub>C ya)"
      by simp
    then obtain za where "\<sigma>' = [] \<or> (\<sigma>' = [y]\<^sub>E # za \<and> za \<le>\<^sub>C ya)"
      by (metis (full_types) assm1 tt_prefix.simps(2) list.exhaust)
    then show "\<exists>\<rho>'. \<rho>' \<subseteq>\<^sub>C \<sigma>' \<and> \<rho>' \<le>\<^sub>C [y]\<^sub>E # xa"
    proof auto
      show "\<sigma>' = [] \<Longrightarrow> \<exists>\<rho>'. \<rho>' \<subseteq>\<^sub>C [] \<and> \<rho>' \<le>\<^sub>C [y]\<^sub>E # xa"
        using tt_prefix.simps(1) tt_subset.simps(1) by blast
    next
      assume "za \<le>\<^sub>C ya" "\<sigma>' = [y]\<^sub>E # za"
      from this and assm2 obtain \<rho>' where "\<rho>' \<subseteq>\<^sub>C za \<and> \<rho>' \<le>\<^sub>C xa"
        by auto
      then show "\<exists>\<rho>'. \<rho>' \<subseteq>\<^sub>C [y]\<^sub>E # za \<and> \<rho>' \<le>\<^sub>C [y]\<^sub>E # xa"
        by (rule_tac x="[y]\<^sub>E # \<rho>'" in exI, auto)
    qed
  qed    
  then show "\<sigma>' \<le>\<^sub>C \<sigma> \<Longrightarrow> \<rho> \<subseteq>\<^sub>C \<sigma> \<Longrightarrow> \<exists>\<rho>'. \<rho>' \<subseteq>\<^sub>C \<sigma>' \<and> \<rho>' \<le>\<^sub>C \<rho>"
    by auto
qed

lemma tt_subset_combine:
  "\<rho>' \<subseteq>\<^sub>C \<rho> \<Longrightarrow> \<sigma>' \<subseteq>\<^sub>C \<sigma> \<Longrightarrow> \<rho>' @ \<sigma>' \<subseteq>\<^sub>C \<rho> @ \<sigma>"
  by (induct \<rho>' \<rho> rule:tt_subset.induct, auto)

lemma tt_subset_end_event:
  "s' \<subseteq>\<^sub>C s \<Longrightarrow> s' @ [[e]\<^sub>E] \<subseteq>\<^sub>C s @ [[e]\<^sub>E]"
  by (induct s' s rule:tt_subset.induct, auto)   

lemma tt_subset_split: "r \<subseteq>\<^sub>C s @ t \<Longrightarrow> \<exists> s' t'. r = s' @ t' \<and> s' \<subseteq>\<^sub>C s \<and> t' \<subseteq>\<^sub>C t"
  apply (induct r s rule:tt_subset.induct, auto)
  apply (meson Cons_eq_appendI tt_subset.simps(2))
  apply (meson Cons_eq_appendI tt_subset.simps(3))
  using tt_subset.simps(1) by blast+

lemma tt_subset_split2: "r @ s \<subseteq>\<^sub>C t \<Longrightarrow> \<exists> r' s'. t =  r' @  s' \<and> r \<subseteq>\<^sub>C r' \<and> s \<subseteq>\<^sub>C s'"
  apply (induct r t rule:tt_subset.induct, auto)
  apply (metis append_Cons tt_subset.simps(2))
  apply (metis append_Cons tt_subset.simps(3))
  using tt_subset.simps(1) by blast+
  

subsection {* Prefix and Subset *}

fun tt_prefix_subset :: "'e ttobs list \<Rightarrow> 'e ttobs list \<Rightarrow> bool" (infix "\<lesssim>\<^sub>C" 50) where
  "tt_prefix_subset [] x = True" |
  "tt_prefix_subset ([X]\<^sub>R # xa) ([Y]\<^sub>R # ya) = (X \<subseteq> Y \<and> tt_prefix_subset xa ya)" |
  "tt_prefix_subset ([x]\<^sub>E # xa) ([y]\<^sub>E # ya) = (x = y \<and> tt_prefix_subset xa ya)" |
  "tt_prefix_subset (x # xa) (y # ya) = False" |
  "tt_prefix_subset (x # xa) [] = False"

lemma tt_prefix_subset_refl: "x \<lesssim>\<^sub>C x"
  by (induct x, auto, case_tac a, auto)

lemma tt_prefix_subset_trans: "x \<lesssim>\<^sub>C y \<Longrightarrow> y \<lesssim>\<^sub>C z \<Longrightarrow> x \<lesssim>\<^sub>C z"
proof -
  have "\<exists> y. x \<lesssim>\<^sub>C y \<and> y \<lesssim>\<^sub>C z \<Longrightarrow> x \<lesssim>\<^sub>C z"
    apply (induct rule:tt_prefix_subset.induct, auto)
    apply (case_tac y, auto, case_tac a, auto)
    apply (case_tac y, auto, case_tac a, auto)
    apply (case_tac yb, auto, case_tac a, auto)
    apply (case_tac yb, auto, case_tac a, auto)
    apply (case_tac y, auto, case_tac a, auto)+
    by (metis tt_prefix_subset.simps(6) neq_Nil_conv)
  then show "x \<lesssim>\<^sub>C y \<Longrightarrow> y \<lesssim>\<^sub>C z \<Longrightarrow> x \<lesssim>\<^sub>C z" by auto
qed

lemma tt_prefix_subset_antisym: "x \<lesssim>\<^sub>C y \<Longrightarrow> y \<lesssim>\<^sub>C x \<Longrightarrow> x = y"
  using tt_prefix_subset.elims(2) by (induct rule:tt_prefix_subset.induct, auto)

lemma tt_prefix_imp_prefix_subset: "x \<le>\<^sub>C y \<Longrightarrow> x \<lesssim>\<^sub>C y"
  by (induct rule:tt_prefix_subset.induct, auto)

lemma tt_subset_imp_prefix_subset: "x \<subseteq>\<^sub>C y \<Longrightarrow> x \<lesssim>\<^sub>C y"
  by (induct rule:tt_prefix_subset.induct, auto)

lemma tt_prefix_subset_imp_tt_prefix_tt_subset: "x \<lesssim>\<^sub>C y \<Longrightarrow> \<exists> z. x \<le>\<^sub>C z \<and> z \<subseteq>\<^sub>C y"
  apply (induct rule:tt_prefix_subset.induct, auto)
  using tt_subset_refl apply blast
  apply (rule_tac x="[X]\<^sub>R # z" in exI, auto)
  apply (rule_tac x="[y]\<^sub>E # z" in exI, auto)
  done

lemma tt_prefix_subset_imp_tt_subset_tt_prefix: "x \<lesssim>\<^sub>C y \<Longrightarrow> \<exists> z. x \<subseteq>\<^sub>C z \<and> z \<le>\<^sub>C y"
  apply (induct rule:tt_prefix_subset.induct, auto)
  apply (rule_tac x="[]" in exI, auto)
  apply (rule_tac x="[Y]\<^sub>R # z" in exI, auto)
  apply (rule_tac x="[y]\<^sub>E # z" in exI, auto)
  done

lemma tt_prefix_tt_prefix_subset_trans: "x \<le>\<^sub>C y \<Longrightarrow> y \<lesssim>\<^sub>C z \<Longrightarrow> x \<lesssim>\<^sub>C z"
  using tt_prefix_imp_prefix_subset tt_prefix_subset_trans by blast
 
lemma tt_prefix_subset_tt_prefix_trans: "x \<lesssim>\<^sub>C y \<Longrightarrow> y \<le>\<^sub>C z \<Longrightarrow> x \<lesssim>\<^sub>C z"
  using tt_prefix_imp_prefix_subset tt_prefix_subset_trans by blast

lemma tt_prefix_decompose: "x \<le>\<^sub>C y \<Longrightarrow> \<exists> z. y = x @ z"
  apply (induct rule:tt_prefix.induct, auto)
  using tt_prefix.elims(2) by auto

lemma tt_prefix_subset_ttWF: "ttWF s \<Longrightarrow> t \<lesssim>\<^sub>C s \<Longrightarrow> ttWF t"
  by (induct rule:ttWF2.induct, auto, (case_tac \<rho> rule:ttWF.cases, auto)+)

lemma tt_prefix_subset_ttWFw: "ttWFw s \<Longrightarrow> t \<lesssim>\<^sub>C s \<Longrightarrow> ttWFw t"
  by (induct rule:ttWFw2.induct, auto, (case_tac \<rho> rule:ttWFw.cases, auto)+)

lemma tt_prefix_subset_length: "t \<lesssim>\<^sub>C s \<Longrightarrow> length t \<le> length s"
  by (induct rule:tt_prefix_subset.induct, auto)

lemma tt_prefix_subset_Tock_filter_length: "t \<lesssim>\<^sub>C s \<Longrightarrow> length (filter (\<lambda> x. x = [Tock]\<^sub>E) t) \<le> length (filter (\<lambda> x. x = [Tock]\<^sub>E) s)"
  by (induct t s rule:tt_prefix_subset.induct, auto)

lemma tt_prefix_subset_append_split: "t \<lesssim>\<^sub>C r @ s \<Longrightarrow>
  \<exists> r' s'. t = r' @ s' \<and> r' \<lesssim>\<^sub>C r \<and> s' \<lesssim>\<^sub>C s \<and> ((length r' = length r \<and> length (filter (\<lambda> x. x = [Tock]\<^sub>E) r') = length (filter (\<lambda> x. x = [Tock]\<^sub>E) r)) \<or> s' = [])"
  apply (induct t "r" rule:tt_prefix_subset.induct, auto)
  apply (metis (mono_tags) append_Cons tt_prefix_subset.simps(2) ttobs.distinct(1) filter.simps(2) length_Cons, force)
  apply (metis (mono_tags, lifting) append_Cons tt_prefix_subset.simps(3) filter.simps(2) length_Cons)
  apply (metis (mono_tags, lifting) append_Cons tt_prefix_subset.simps(3) filter.simps(2) length_Cons, force+)
  done

lemma tt_prefix_subset_append_split_Tock_filter: "t \<lesssim>\<^sub>C r @ s \<Longrightarrow> \<exists> r' s'. t = r' @ s' \<and> r' \<lesssim>\<^sub>C r \<and> s' \<lesssim>\<^sub>C s \<and> (length r' = length r \<or> s' = [])"
  apply (induct t "r" rule:tt_prefix_subset.induct, auto)
  apply (metis append_Cons tt_prefix_subset.simps(2) length_Cons, force)
  apply (metis append_Cons tt_prefix_subset.simps(3) length_Cons, force)
  using tt_prefix_subset_refl by blast

lemma init_refusal_tt_prefix_subset: "[X]\<^sub>R # \<rho> \<lesssim>\<^sub>C [Y]\<^sub>R # \<sigma> \<Longrightarrow> \<rho> \<lesssim>\<^sub>C \<sigma>"
  by (induct \<rho> \<sigma> rule:tt_prefix_subset.induct, auto)

lemma init_event_tt_prefix_subset: "[e]\<^sub>E # \<rho> \<lesssim>\<^sub>C [f]\<^sub>E # \<sigma> \<Longrightarrow> \<rho> \<lesssim>\<^sub>C \<sigma>"
  by (induct \<rho> \<sigma> rule:tt_prefix_subset.induct, auto)

lemma tt_prefix_subset_front: "s @ t \<lesssim>\<^sub>C \<sigma> \<Longrightarrow> s \<lesssim>\<^sub>C \<sigma>"
  by (induct s \<sigma> rule:tt_prefix_subset.induct, auto)

lemma tt_prefix_subset_lift: "\<rho> \<lesssim>\<^sub>C \<sigma> \<Longrightarrow> \<exists> \<rho>'. \<rho>' \<le>\<^sub>C \<sigma> \<and> \<rho> \<lesssim>\<^sub>C \<rho>'"
  apply (induct \<rho> \<sigma> rule:tt_prefix_subset.induct, auto)
  using tt_prefix.simps(1) apply blast
  using tt_prefix_refl tt_prefix_subset.simps(2) apply blast
  using tt_prefix_refl tt_prefix_subset.simps(3) by blast

lemma tt_prefix_subset_same_front: "s \<lesssim>\<^sub>C t = (r @ s \<lesssim>\<^sub>C r @ t)"
  by (induct r, auto, (case_tac a, auto)+)

lemma tt_prefix_subset_concat: "r \<lesssim>\<^sub>C s @ t \<Longrightarrow> r \<lesssim>\<^sub>C s \<or> (\<exists> t'. t' \<lesssim>\<^sub>C t \<and> r \<subseteq>\<^sub>C s @ t')"
  by (induct r s rule:tt_prefix_subset.induct, auto, rule_tac x="x # xa" in exI, auto simp add: tt_subset_refl)

lemma tt_prefix_subset_concat2: "r \<lesssim>\<^sub>C s @ t \<Longrightarrow> r \<lesssim>\<^sub>C s \<or> (\<exists> t' s'. s' \<subseteq>\<^sub>C s \<and> t' \<lesssim>\<^sub>C t \<and> r = s' @ t')"
  apply (induct r s rule:tt_prefix_subset.induct, auto)
  apply (erule_tac x="t'" in allE, auto, erule_tac x="[X]\<^sub>R # s'" in allE, auto)
  apply (erule_tac x="t'" in allE, auto, erule_tac x="[y]\<^sub>E # s'" in allE, auto)
  apply (rule_tac x="x # xa" in exI, auto simp add: tt_subset_refl)
  done

lemma tt_prefix_common_concat:
  assumes "zs \<lesssim>\<^sub>C ys"
  shows "xs @ zs \<lesssim>\<^sub>C xs @ ys"
  using assms apply (induct zs ys arbitrary:xs rule:tt_prefix_subset.induct, auto)
  using tt_prefix_concat tt_prefix_imp_prefix_subset apply blast
  apply (meson tt_prefix_subset.simps(2) tt_prefix_subset_same_front)
  by (meson tt_prefix_subset.simps(3) tt_prefix_subset_same_front)

lemma tt_prefix_common_concat_eq_size:
  assumes "zs \<lesssim>\<^sub>C ys" "size zs = size ys"
  shows "zs @ xs \<lesssim>\<^sub>C ys @ xs"
  using assms apply (induct zs ys arbitrary:xs rule:tt_prefix_subset.induct, auto)
  by (simp add: tt_prefix_subset_refl)

lemma ttWF_prefix_is_ttWF: "ttWF (s @ t) \<Longrightarrow> ttWF s"
  using tt_prefix_concat tt_prefix_imp_prefix_subset tt_prefix_subset_ttWF by blast

lemma ttWF_end_refusal_prefix_subset: "ttWF (s @ [[X]\<^sub>R]) \<Longrightarrow> t \<lesssim>\<^sub>C s @ [[X]\<^sub>R] \<Longrightarrow> 
  (\<exists> r Y. t = r @ [[Y]\<^sub>R]) \<or> (\<exists> r Y. t = r @ [[Y]\<^sub>R, [Tock]\<^sub>E]) \<or> (\<exists> r e. t = r @ [[Event e]\<^sub>E]) \<or> t = []"
  apply (induct s t rule:ttWF2.induct, auto)
  using ttWF.simps(12) tt_prefix_subset_ttWF apply blast
  apply (meson ttWF.simps(11) tt_prefix_subset_ttWF)
  using ttWF.simps(13) tt_prefix_subset_ttWF apply blast
  using ttWF.simps(8) tt_prefix_subset_ttWF apply blast
  using ttWF.simps(6) tt_prefix_subset_ttWF by blast

lemma ttWF_end_Event_prefix_subset: "ttWF (s @ [[Event e]\<^sub>E]) \<Longrightarrow> t \<lesssim>\<^sub>C s @ [[Event e]\<^sub>E] \<Longrightarrow> 
  (\<exists> r Y. t = r @ [[Y]\<^sub>R]) \<or> (\<exists> r Y. t = r @ [[Y]\<^sub>R, [Tock]\<^sub>E]) \<or> (\<exists> r e. t = r @ [[Event e]\<^sub>E]) \<or> t = []"
  apply (induct s t rule:ttWF2.induct, auto)
  using tt_prefix_subset_antisym apply fastforce
  using ttWF.simps(12) tt_prefix_subset_ttWF apply blast
  apply (meson ttWF.simps(11) tt_prefix_subset_ttWF)
  using ttWF.simps(13) tt_prefix_subset_ttWF apply blast
  using ttWF.simps(8) tt_prefix_subset_ttWF apply blast
  using ttWF.simps(6) tt_prefix_subset_ttWF by blast

lemma ttWF_end_Tock_prefix_subset: "ttWF (s @ [[Tock]\<^sub>E]) \<Longrightarrow> t \<lesssim>\<^sub>C s @ [[Tock]\<^sub>E] \<Longrightarrow> 
  (\<exists> r Y. t = r @ [[Y]\<^sub>R]) \<or> (\<exists> r Y. t = r @ [[Y]\<^sub>R, [Tock]\<^sub>E]) \<or> (\<exists> r e. t = r @ [[Event e]\<^sub>E]) \<or> t = []"
  apply (induct s t rule:ttWF2.induct, auto)
  using tt_prefix_subset_antisym apply fastforce
  using ttWF.simps(12) tt_prefix_subset_ttWF apply blast
  apply (meson ttWF.simps(11) tt_prefix_subset_ttWF)
  using ttWF.simps(13) tt_prefix_subset_ttWF apply blast
  using ttWF.simps(8) tt_prefix_subset_ttWF apply blast
  using ttWF.simps(6) tt_prefix_subset_ttWF by blast

lemma ttWF_cons_hd_not_Tock_then_ttWF:
  assumes "ttWF (a # fl)" "hd fl \<noteq> [Tock]\<^sub>E"
  shows "ttWF fl"
  by (metis (no_types, lifting) assms(1) assms(2) ttWF.elims(2) ttWF.simps(1) list.discI list.inject list.sel(1))

lemma ttWF_dist_cons_refusal: 
  assumes "ttWF (s @ [[S]\<^sub>R,x])"
  shows "ttWF [[S]\<^sub>R,x]"
  using assms by(induct s rule:ttWF.induct, auto)

lemma ttWF_Refusal_tt_prefix:
  assumes "ttWF \<sigma>"
  shows "[[X]\<^sub>R] \<lesssim>\<^sub>C \<sigma> = (\<exists>Y z. \<sigma> = ([[Y]\<^sub>R] @ z) \<and> X \<subseteq> Y)"
  using assms apply auto
  apply (case_tac \<sigma>, auto)
  by (case_tac a, auto)

lemma tt_prefix_eq_length_imp:
  assumes "xs @ [x] \<lesssim>\<^sub>C ys @ [y]"
          "List.length (xs @ [x]) = List.length (ys @ [y])"
    shows "[x] \<lesssim>\<^sub>C [y]"
  using assms by(induct xs ys rule:tt_prefix_subset.induct, auto)

lemma tt_prefix_eq_length_common_prefix:
  assumes "xs @ [x] \<lesssim>\<^sub>C ys @ [y]" "List.length (xs @ [x]) = List.length (ys @ [y])"
  shows "xs \<lesssim>\<^sub>C ys"
  using assms by(induct xs ys rule:tt_prefix_subset.induct, auto)

lemma tt_singleton_prefix_nonempty:
  assumes "[x] \<lesssim>\<^sub>C xa @ z" "xa \<noteq> []"
  shows "[x] \<lesssim>\<^sub>C xa"
  using assms apply (induct xa, auto)
  by (case_tac x, auto, case_tac a, auto, case_tac a, auto)

lemma tt_prefix_gt_length_imp:
  assumes "xs @ [x] \<lesssim>\<^sub>C ys @ [y]"
          "List.length (xs @ [x]) < List.length (ys @ [y])"
    shows "xs @ [x] \<lesssim>\<^sub>C ys"
  using assms apply(induct xs ys rule:tt_prefix_subset.induct, auto)
  using tt_singleton_prefix_nonempty by blast 

lemma ttWF_tt_prefix_subset_exists_three_part:
  assumes "ttWF \<sigma>" "\<rho> @ [[X]\<^sub>R] \<lesssim>\<^sub>C \<sigma>"
  shows "\<exists>Y z \<rho>\<^sub>2. \<sigma> = \<rho>\<^sub>2 @ ([[Y]\<^sub>R] @ z) \<and> X \<subseteq> Y \<and> \<rho> \<lesssim>\<^sub>C \<rho>\<^sub>2 \<and> size \<rho>\<^sub>2 = size \<rho>"
  using assms proof (induct \<sigma> arbitrary:X \<rho> rule:rev_induct)
  case Nil
  then show ?case using tt_prefix_subset.simps(1) tt_prefix_subset_antisym by blast
next
  case (snoc x xs)
  then show ?case
  proof (cases "size (\<rho> @ [[X]\<^sub>R]) = size (xs @ [x])")
    case True
    then have eq_lengths:"List.length (\<rho>) = List.length (xs)"
      by simp
    then show ?thesis
    proof (cases x)
      case (ObsEvent x1)
      then show ?thesis using snoc True
        by (meson tt_prefix_eq_length_imp tt_prefix_subset.simps(5))
    next
      case (Ref x2)
      then have xX2:"[[X]\<^sub>R] \<lesssim>\<^sub>C [[x2]\<^sub>R]"
                    "\<rho> \<lesssim>\<^sub>C xs"
        using True tt_prefix_eq_length_imp snoc.prems(2) apply blast
        using True snoc tt_prefix_eq_length_common_prefix by metis
      then have "X \<subseteq> x2" 
        by auto
      then have "xs @ [x] = xs @ [[x2]\<^sub>R] @ [] \<and> X \<subseteq> x2 \<and> \<rho> \<lesssim>\<^sub>C xs \<and> List.length (xs) = List.length (\<rho>)"
        using xX2 snoc eq_lengths Ref by auto
      then have "\<exists>\<rho>\<^sub>2. xs @ [x] = \<rho>\<^sub>2 @ [[x2]\<^sub>R] @ [] \<and> X \<subseteq> x2 \<and> \<rho> \<lesssim>\<^sub>C \<rho>\<^sub>2 \<and> List.length (\<rho>\<^sub>2) = List.length (\<rho>)"
        by blast
      then have "\<exists>Y \<rho>\<^sub>2. xs @ [x] = \<rho>\<^sub>2 @ [[Y]\<^sub>R] @ [] \<and> X \<subseteq> Y \<and> \<rho> \<lesssim>\<^sub>C \<rho>\<^sub>2 \<and> List.length (\<rho>\<^sub>2) = List.length (\<rho>)"
        by blast
      then have "\<exists>Y z \<rho>\<^sub>2. xs @ [x] = \<rho>\<^sub>2 @ [[Y]\<^sub>R] @ z \<and> X \<subseteq> Y \<and> \<rho> \<lesssim>\<^sub>C \<rho>\<^sub>2 \<and> List.length (\<rho>\<^sub>2) = List.length (\<rho>)"
        by blast
      then show ?thesis by blast
    qed
  next
    case False
    then have "List.length (\<rho> @ [[X]\<^sub>R]) < List.length (xs @ [x])"
      using snoc 
      by (meson tt_prefix_subset_length le_neq_trans)
    then have "\<rho> @ [[X]\<^sub>R] \<lesssim>\<^sub>C xs"
      using snoc tt_prefix_gt_length_imp by metis
    then have "\<exists>Y z \<rho>\<^sub>2. xs = \<rho>\<^sub>2 @ [[Y]\<^sub>R] @ z \<and> X \<subseteq> Y \<and> \<rho> \<lesssim>\<^sub>C \<rho>\<^sub>2 \<and> List.length \<rho>\<^sub>2 = List.length \<rho>"
      using snoc ttWF_prefix_is_ttWF by blast
    then have "\<exists>Y z \<rho>\<^sub>2. xs @ [x] = \<rho>\<^sub>2 @ [[Y]\<^sub>R] @ z @ [x] \<and> X \<subseteq> Y \<and> \<rho> \<lesssim>\<^sub>C \<rho>\<^sub>2 \<and> List.length \<rho>\<^sub>2 = List.length \<rho>"
      by auto
    then have "\<exists>Y z \<rho>\<^sub>2. xs @ [x] = \<rho>\<^sub>2 @ [[Y]\<^sub>R] @ z \<and> X \<subseteq> Y \<and> \<rho> \<lesssim>\<^sub>C \<rho>\<^sub>2 \<and> List.length \<rho>\<^sub>2 = List.length \<rho>"
      by blast
    then show ?thesis by blast
  qed
qed

lemma ttWF_tt_prefix_subset_exists_three_part_concat:
  assumes "\<rho> @ [[X]\<^sub>R] @ s \<lesssim>\<^sub>C \<sigma>"
  shows "\<exists>Y z \<rho>\<^sub>2. \<sigma> = \<rho>\<^sub>2 @ ([[Y]\<^sub>R] @ z) \<and> X \<subseteq> Y \<and> \<rho> \<lesssim>\<^sub>C \<rho>\<^sub>2 \<and> s \<lesssim>\<^sub>C z \<and> size \<rho>\<^sub>2 = size \<rho>"
  using assms proof (induct \<rho> \<sigma> arbitrary:X s rule:tt_prefix_subset.induct)
case (1 x)
  then show ?case 
    apply auto
    by (cases x, auto, case_tac a, auto)
next
  case (2 Z za Y ya)
  then have "za @ [[X]\<^sub>R] @ s \<lesssim>\<^sub>C ya"
    by simp
  then have "\<exists>Y z \<rho>\<^sub>2.
               ya = \<rho>\<^sub>2 @ [Y]\<^sub>R # z \<and>
               X \<subseteq> Y \<and> za \<lesssim>\<^sub>C \<rho>\<^sub>2 \<and> s \<lesssim>\<^sub>C z \<and> List.length \<rho>\<^sub>2 = List.length za"
    using 2 by auto
  then show ?case 
    apply auto
    by (metis "2.prems" append_Cons tt_prefix_subset.simps(2) length_Cons)
next
  case (3 x xa y ya)
  then show ?case apply auto
    by (metis append_Cons tt_prefix_subset.simps(3) length_Cons)
next
  case ("4_1" v xa va ya)
  then show ?case by auto
next
  case ("4_2" va xa v ya)
  then show ?case by auto
next
  case (5 x xa)
  then show ?case by auto
qed

lemma tt_prefix_subset_eq_length_common_prefix_eq:
  assumes "List.length xs = List.length ys"
  shows "((xs @ z) \<lesssim>\<^sub>C (ys @ s)) = (xs \<lesssim>\<^sub>C ys \<and> z \<lesssim>\<^sub>C s)"
  using assms by(induct xs ys rule:tt_prefix_subset.induct, auto)

lemma ttWF_tt_prefix_subset_exists_three_part':
  assumes "\<sigma> = \<rho>\<^sub>2 @ ([[Y]\<^sub>R] @ z) \<and> X \<subseteq> Y \<and> \<rho> \<lesssim>\<^sub>C \<rho>\<^sub>2 \<and> size \<rho>\<^sub>2 = size \<rho>" "ttWF \<sigma>"
  shows "\<rho> @ [[X]\<^sub>R] \<lesssim>\<^sub>C \<sigma>"
  using assms apply auto 
  by (simp add: tt_prefix_subset_eq_length_common_prefix_eq)

lemma ttWF_tt_prefix_subset_exists_three_part_iff:
  assumes "ttWF \<sigma>"
  shows "\<rho> @ [[X]\<^sub>R] \<lesssim>\<^sub>C \<sigma> = (\<exists>Y z \<rho>\<^sub>2. \<sigma> = \<rho>\<^sub>2 @ ([[Y]\<^sub>R] @ z) \<and> X \<subseteq> Y \<and> \<rho> \<lesssim>\<^sub>C \<rho>\<^sub>2 \<and> size \<rho>\<^sub>2 = size \<rho>)"
  using assms
  by (meson ttWF_tt_prefix_subset_exists_three_part ttWF_tt_prefix_subset_exists_three_part')

lemma tt_prefix_of_ttWFx_trace:
  assumes "x \<lesssim>\<^sub>C \<sigma>" "ttWFx_trace \<sigma>"
  shows "ttWFx_trace x"
  using assms 
proof (induct x \<sigma> rule:tt_prefix_subset.induct)
  case (1 x)
  then show ?case by auto
next
  case (2 X xa Y ya)
  then show ?case
    apply (induct xa ya rule:tt_prefix_subset.induct, auto)
    apply (case_tac y, auto)
    using ttWFx_trace.simps(3) ttWFx_trace_cons_imp_cons by blast
next
  case (3 x xa y ya)
  then show ?case by (induct xa ya rule:tt_prefix_subset.induct, auto)
next
  case ("4_1" v xa va ya)
  then show ?case by auto
next
  case ("4_2" va xa v ya)
  then show ?case by auto
next
  case (5 x xa)
  then show ?case by auto
qed

section {* Healthiness Conditions *}

subsection \<open>TT0\<close>

text_raw \<open>\DefineSnippet{TT0}{\<close>
definition TT0 :: "'e ttprocess \<Rightarrow> bool" where
  "TT0 P = (P \<noteq> {})"
text_raw \<open>}%EndSnippet\<close>

subsection \<open>TT1\<close>

text_raw \<open>\DefineSnippet{TT1w}{\<close>
definition TT1w :: "'e ttprocess \<Rightarrow> bool" where
  "TT1w P = (\<forall> \<rho> \<sigma>. (\<rho> \<le>\<^sub>C \<sigma> \<and> \<sigma> \<in> P) \<longrightarrow> \<rho> \<in> P)"
text_raw \<open>}%EndSnippet\<close>

lemma some_x_then_nil_TT1w [elim]:
  assumes "x \<in> P" "TT1w P"
  shows "[] \<in> P"
  using assms 
  unfolding TT1w_def by force

definition mkTT1w :: "'e ttobs list set \<Rightarrow> 'e ttobs list set" where
"mkTT1w P = P \<union> {\<rho>|\<rho> \<sigma>. \<rho> \<le>\<^sub>C \<sigma> \<and> \<sigma> \<in> P}"

lemma TT1w_fixpoint_mkTT1w:
  "TT1w P = (P = mkTT1w(P))"
  unfolding TT1w_def mkTT1w_def by auto

lemma TT1w_prefix_concat_in:
  assumes "xs @ ys \<in> P" "TT1w P"
  shows "xs \<in> P"
proof -
  have "xs \<le>\<^sub>C xs @ ys"
    using tt_prefix_concat by blast
  then have "xs \<in> P"
    using assms TT1w_def by blast
  then show ?thesis .
qed

lemma TT1w_mkTT1w [simp]: "TT1w (mkTT1w P)"
  unfolding mkTT1w_def TT1w_def apply auto
  using tt_prefix_trans by blast

text_raw \<open>\DefineSnippet{TT1}{\<close>
definition TT1 :: "'e ttprocess \<Rightarrow> bool" where
  "TT1 P = (\<forall> \<rho> \<sigma>. (\<rho> \<lesssim>\<^sub>C \<sigma> \<and> \<sigma> \<in> P) \<longrightarrow> \<rho> \<in> P)"
text_raw \<open>}%EndSnippet\<close>

text \<open> mkTT1 is the fixed-point version of TT1 as established below. \<close>

definition mkTT1 :: "'e ttobs list set \<Rightarrow> 'e ttobs list set" where
"mkTT1 P = P \<union> {\<rho>|\<rho> \<sigma>. \<rho> \<lesssim>\<^sub>C \<sigma> \<and> \<sigma> \<in> P}"

lemma TT1_fixpoint_mkTT1:
  "(mkTT1 P = P) = TT1 P"
  unfolding mkTT1_def TT1_def by auto

lemma mkTT1_simp:
  "mkTT1 P = {\<rho>|\<rho> \<sigma>. \<rho> \<lesssim>\<^sub>C \<sigma> \<and> \<sigma> \<in> P}"
  unfolding mkTT1_def apply auto
  using tt_prefix_subset_refl by blast

lemma mkTT1_mono:
  assumes "P \<subseteq> Q"
  shows "mkTT1 P \<subseteq> mkTT1 Q"
  using assms unfolding mkTT1_def by auto

lemma TT0_mkTT1:
  assumes "TT0 P"
  shows "TT0(mkTT1(P))"
  using assms unfolding mkTT1_def TT0_def by auto

lemma TT1_mkTT1:
  shows "TT1(mkTT1(P))"
  by (smt TT1_def mem_Collect_eq mkTT1_simp tt_prefix_subset_trans)

lemma TT1_mkTT1_simp:
  assumes "TT1 P"
  shows "(\<exists>x. s \<in> x \<and> (mkTT1 x) \<subseteq> P) = (s \<in> P)"
  using assms apply safe
  using mkTT1_def apply fastforce
  using TT1_fixpoint_mkTT1 by blast

subsection \<open>TT2\<close>

text_raw \<open>\DefineSnippet{TT2w}{\<close>
definition TT2w :: "'e ttprocess \<Rightarrow> bool" where
  "TT2w P = (\<forall> \<rho> X Y. (\<rho> @ [[X]\<^sub>R] \<in> P \<and> (Y \<inter> {e. (e \<noteq> Tock \<and> \<rho> @ [[e]\<^sub>E] \<in> P) \<or> (e = Tock \<and> \<rho> @ [[X]\<^sub>R, [e]\<^sub>E] \<in> P) } = {}))
     \<longrightarrow> \<rho> @ [[X \<union> Y]\<^sub>R] \<in> P)"
text_raw \<open>}%EndSnippet\<close>

text_raw \<open>\DefineSnippet{TT2}{\<close>
definition TT2 :: "'e ttprocess \<Rightarrow> bool" where
  "TT2 P = (\<forall> \<rho> \<sigma> X Y. (\<rho> @ [[X]\<^sub>R] @ \<sigma> \<in> P \<and> (Y \<inter> {e. (e \<noteq> Tock \<and> \<rho> @ [[e]\<^sub>E] \<in> P) \<or> (e = Tock \<and> \<rho> @ [[X]\<^sub>R, [e]\<^sub>E] \<in> P) } = {}))
     \<longrightarrow> \<rho> @ [[X \<union> Y]\<^sub>R] @ \<sigma> \<in> P)"
text_raw \<open>}%EndSnippet\<close>

lemma wf_TT2_induct:
  "\<forall>x\<in>P. ttWF x \<Longrightarrow>
    (\<And> \<rho> \<sigma> X Y. ([[X]\<^sub>R] \<in> P \<and> (Y \<inter> {e. (e \<noteq> Tock \<and> [[e]\<^sub>E] \<in> P) \<or> (e = Tock \<and> [[X]\<^sub>R, [e]\<^sub>E] \<in> P) } = {})) \<Longrightarrow> [[X \<union> Y]\<^sub>R] \<in> P) \<Longrightarrow>
    (\<And> \<rho> \<sigma> X Y. ([[X]\<^sub>R, [Tock]\<^sub>E] @ \<sigma> \<in> P \<and> (Y \<inter> {e. e \<noteq> Tock \<and> [[e]\<^sub>E] \<in> P \<or> e = Tock \<and> [[X]\<^sub>R, [e]\<^sub>E] \<in> P} = {})) \<Longrightarrow> [[X \<union> Y]\<^sub>R, [Tock]\<^sub>E] @ \<sigma> \<in> P) \<Longrightarrow>
    (\<And>e \<rho> \<sigma> X Y. ((\<rho> @ [[X]\<^sub>R] @ \<sigma> \<in> P \<and> (Y \<inter> {e. (e \<noteq> Tock \<and> \<rho> @ [[e]\<^sub>E] \<in> P) \<or> (e = Tock \<and> \<rho> @ [[X]\<^sub>R, [e]\<^sub>E] \<in> P)} = {})) \<Longrightarrow> \<rho> @ [[X \<union> Y]\<^sub>R] @ \<sigma> \<in> P) \<Longrightarrow> 
      (([Event e]\<^sub>E # \<rho> @ [[X]\<^sub>R] @ \<sigma> \<in> P \<and> (Y \<inter> {ea. (ea \<noteq> Tock \<and> [Event e]\<^sub>E # \<rho> @ [[ea]\<^sub>E] \<in> P) \<or> (ea = Tock \<and> [Event e]\<^sub>E # \<rho> @ [[X]\<^sub>R, [ea]\<^sub>E] \<in> P)} = {})) \<Longrightarrow> 
        [Event e]\<^sub>E # \<rho> @ [[X \<union> Y]\<^sub>R] @ \<sigma> \<in> P)) \<Longrightarrow>
    (\<And>e \<rho> \<sigma> X Y Z. ((\<rho> @ [[X]\<^sub>R] @ \<sigma> \<in> P \<and> (Y \<inter> {e. (e \<noteq> Tock \<and> \<rho> @ [[e]\<^sub>E] \<in> P) \<or> (e = Tock \<and> \<rho> @ [[X]\<^sub>R, [e]\<^sub>E] \<in> P)} = {})) \<Longrightarrow> \<rho> @ [[X \<union> Y]\<^sub>R] @ \<sigma> \<in> P) \<Longrightarrow> 
      (([Z]\<^sub>R # [Tock]\<^sub>E # \<rho> @ [[X]\<^sub>R] @ \<sigma> \<in> P \<and> (Y \<inter> {e. (e \<noteq> Tock \<and> [Z]\<^sub>R # [Tock]\<^sub>E # \<rho> @ [[e]\<^sub>E] \<in> P) \<or> (e = Tock \<and> [Z]\<^sub>R # [Tock]\<^sub>E # \<rho> @ [[X]\<^sub>R, [e]\<^sub>E] \<in> P)} = {})) \<Longrightarrow>
        [Z]\<^sub>R # [Tock]\<^sub>E # \<rho> @ [[X \<union> Y]\<^sub>R] @ \<sigma> \<in> P)) \<Longrightarrow>
    TT2 P"
  unfolding TT2_def
proof auto
  fix \<rho> \<sigma> X Y
  assume P_wf: "\<forall>x\<in>P. ttWF x"
  show "\<forall>x\<in>P. ttWF x \<Longrightarrow>
       (\<And>X Y. [[X]\<^sub>R] \<in> P \<and> Y \<inter> {e. e \<noteq> Tock \<and> [[e]\<^sub>E] \<in> P \<or> e = Tock \<and> [[X]\<^sub>R, [e]\<^sub>E] \<in> P} = {} \<Longrightarrow> [[X \<union> Y]\<^sub>R] \<in> P) \<Longrightarrow>
       (\<And>\<sigma> X Y. [X]\<^sub>R # [Tock]\<^sub>E # \<sigma> \<in> P \<and> Y \<inter> {e. e \<noteq> Tock \<and> [[e]\<^sub>E] \<in> P \<or> e = Tock \<and> [[X]\<^sub>R, [e]\<^sub>E] \<in> P} = {} \<Longrightarrow> [X \<union> Y]\<^sub>R # [Tock]\<^sub>E # \<sigma> \<in> P) \<Longrightarrow>
       (\<And>e \<rho> \<sigma> X Y.
           (\<rho> @ [X]\<^sub>R # \<sigma> \<in> P \<and> Y \<inter> {e. e \<noteq> Tock \<and> \<rho> @ [[e]\<^sub>E] \<in> P \<or> e = Tock \<and> \<rho> @ [[X]\<^sub>R, [e]\<^sub>E] \<in> P} = {} \<Longrightarrow> \<rho> @ [X \<union> Y]\<^sub>R # \<sigma> \<in> P) \<Longrightarrow>
           [Event e]\<^sub>E # \<rho> @ [X]\<^sub>R # \<sigma> \<in> P \<and>
           Y \<inter> {ea. ea \<noteq> Tock \<and> [Event e]\<^sub>E # \<rho> @ [[ea]\<^sub>E] \<in> P \<or> ea = Tock \<and> [Event e]\<^sub>E # \<rho> @ [[X]\<^sub>R, [ea]\<^sub>E] \<in> P} = {} \<Longrightarrow>
           [Event e]\<^sub>E # \<rho> @ [X \<union> Y]\<^sub>R # \<sigma> \<in> P) \<Longrightarrow>
       (\<And>\<rho> \<sigma> X Y Z.
           (\<rho> @ [X]\<^sub>R # \<sigma> \<in> P \<and> Y \<inter> {e. e \<noteq> Tock \<and> \<rho> @ [[e]\<^sub>E] \<in> P \<or> e = Tock \<and> \<rho> @ [[X]\<^sub>R, [e]\<^sub>E] \<in> P} = {} \<Longrightarrow> \<rho> @ [X \<union> Y]\<^sub>R # \<sigma> \<in> P) \<Longrightarrow>
           [Z]\<^sub>R # [Tock]\<^sub>E # \<rho> @ [X]\<^sub>R # \<sigma> \<in> P \<and>
           Y \<inter> {e. e \<noteq> Tock \<and> [Z]\<^sub>R # [Tock]\<^sub>E # \<rho> @ [[e]\<^sub>E] \<in> P \<or> e = Tock \<and> [Z]\<^sub>R # [Tock]\<^sub>E # \<rho> @ [[X]\<^sub>R, [e]\<^sub>E] \<in> P} = {} \<Longrightarrow>
           [Z]\<^sub>R # [Tock]\<^sub>E # \<rho> @ [X \<union> Y]\<^sub>R # \<sigma> \<in> P) \<Longrightarrow>
       \<rho> @ [X]\<^sub>R # \<sigma> \<in> P \<Longrightarrow> Y \<inter> {e. e \<noteq> Tock \<and> \<rho> @ [[e]\<^sub>E] \<in> P \<or> e = Tock \<and> \<rho> @ [[X]\<^sub>R, [e]\<^sub>E] \<in> P} = {} \<Longrightarrow> \<rho> @ [X \<union> Y]\<^sub>R # \<sigma> \<in> P"
  proof (induct \<rho> rule:ttWF.induct, auto)
    assume assm1: "\<And>X Y. [[X]\<^sub>R] \<in> P \<and> Y \<inter> {e. e \<noteq> Tock \<and> [[e]\<^sub>E] \<in> P \<or> e = Tock \<and> [[X]\<^sub>R, [e]\<^sub>E] \<in> P} = {} \<Longrightarrow> [[X \<union> Y]\<^sub>R] \<in> P"
    assume assm2: "\<And>\<sigma> X Y. [X]\<^sub>R # [Tock]\<^sub>E # \<sigma> \<in> P \<and> Y \<inter> {e. e \<noteq> Tock \<and> [[e]\<^sub>E] \<in> P \<or> e = Tock \<and> [[X]\<^sub>R, [e]\<^sub>E] \<in> P} = {} \<Longrightarrow> [X \<union> Y]\<^sub>R # [Tock]\<^sub>E # \<sigma> \<in> P"
    assume "[X]\<^sub>R # \<sigma> \<in> P"
    then have "ttWF ([X]\<^sub>R # \<sigma>)"
      using P_wf by auto
    then show "[X]\<^sub>R # \<sigma> \<in> P \<Longrightarrow> Y \<inter> {e. e \<noteq> Tock \<and> [[e]\<^sub>E] \<in> P \<or> e = Tock \<and> [[X]\<^sub>R, [e]\<^sub>E] \<in> P} = {} \<Longrightarrow> [X \<union> Y]\<^sub>R # \<sigma> \<in> P "
      by (cases \<sigma> rule:ttWF.cases, simp_all add: assm1 assm2 disjoint_iff_not_equal)
  qed
qed

lemma TT2_imp_TT2w: "TT2 P \<Longrightarrow> TT2w P"
  unfolding TT2_def TT2w_def by auto

lemma TT2_extends_Ref:
  assumes "TT2 P" "s @ [[X]\<^sub>R] @ xs \<in> P"
  shows "s @ [[X \<union> {e. e \<noteq> Tock \<and> s @ [[e]\<^sub>E] \<notin> P \<or> e = Tock \<and> s @ [[X]\<^sub>R, [Tock]\<^sub>E] \<notin> P}]\<^sub>R] @ xs \<in> P"
proof -
  obtain Y where Y:"Y = {e. e \<noteq> Tock \<and> s @ [[e]\<^sub>E] \<notin> P \<or> e = Tock \<and> s @ [[X]\<^sub>R, [Tock]\<^sub>E] \<notin> P}"
    by auto
  then have "Y \<inter> {e. (e \<noteq> Tock \<and> s @ [[e]\<^sub>E] \<in> P) \<or> (e = Tock \<and> s @ [[X]\<^sub>R, [e]\<^sub>E] \<in> P) } = {}"
    by auto
  then have "s @ [[X \<union> Y]\<^sub>R] @ xs \<in> P"
    using assms unfolding TT2_def by auto
  then show ?thesis using Y by auto
qed

lemma TT2_aux1:
  assumes "TT2 P" "\<rho> @ [[X]\<^sub>R] @ \<sigma> \<in> P" "Y \<inter> {e. (e \<noteq> Tock \<and> \<rho> @ [[e]\<^sub>E] \<in> P) \<or> (e = Tock \<and> \<rho> @ [[X]\<^sub>R, [e]\<^sub>E] \<in> P) } = {}"
  shows "\<rho> @ [[X \<union> Y]\<^sub>R] @ \<sigma> \<in> P"
  using assms TT2_def by blast

lemma TT2_aux2:
  assumes "TT2 P" "[[X]\<^sub>R] @ \<sigma> \<in> P" "Y \<inter> {e. (e \<noteq> Tock \<and> [[e]\<^sub>E] \<in> P) \<or> (e = Tock \<and> [[X]\<^sub>R, [e]\<^sub>E] \<in> P) } = {}"
  shows "[[X \<union> Y]\<^sub>R] @ \<sigma> \<in> P"
  using assms TT2_def by (metis (no_types, lifting) Collect_cong append.left_neutral)

lemma TT2_aux3:
  assumes "TT2 P" "[[X]\<^sub>R] \<in> P" "Y \<inter> {e. (e \<noteq> Tock \<and> [[e]\<^sub>E] \<in> P) \<or> (e = Tock \<and> [[X]\<^sub>R, [e]\<^sub>E] \<in> P) } = {}"
  shows "[[X \<union> Y]\<^sub>R] \<in> P"
  using TT2_aux2 assms(1) assms(2) assms(3) by auto

subsection \<open>TT3\<close>

definition TT3ww :: "'e ttprocess \<Rightarrow> bool" where
"TT3ww P = (\<forall> \<rho> X. \<rho> @ [[X]\<^sub>R] \<in> P \<longrightarrow> \<rho> @ [[X \<union> {Tick}]\<^sub>R] \<in> P)"

definition mkTT3ww :: "'e ttobs list set \<Rightarrow> 'e ttobs list set" where
"mkTT3ww P = P \<union> {\<rho> @ [[R \<union> {Tick}]\<^sub>R]|\<rho> R. \<rho> @ [[R]\<^sub>R] \<in> P}"

lemma TT3ww_fixpoint_mkTT3ww:
  "(mkTT3ww P = P) = TT3ww P"
  unfolding mkTT3ww_def TT3ww_def by auto

lemma mkTT1_mkTT3ww_iff_TT14:
  "(mkTT1(mkTT3ww P) = P) = (TT1 P \<and> TT3ww P)"
  apply auto
  using TT1_def mkTT1_simp mkTT3ww_def apply fastforce
  apply (metis (mono_tags, lifting) TT1_def TT1_fixpoint_mkTT1 TT3ww_fixpoint_mkTT3ww CollectI UnI1 mkTT1_simp mkTT3ww_def)  
    apply (metis TT1_fixpoint_mkTT1 TT3ww_fixpoint_mkTT3ww)
    by (metis TT1_fixpoint_mkTT1 TT3ww_fixpoint_mkTT3ww)

text_raw \<open>\DefineSnippet{TT3}{\<close>
definition TT3 :: "'e ttprocess \<Rightarrow> bool" where
  "TT3 P = (\<forall> \<rho> \<sigma> X. \<rho> @ [[X]\<^sub>R] @ \<sigma> \<in> P \<longrightarrow> \<rho> @ [[X \<union> {Tick}]\<^sub>R] @ \<sigma> \<in> P)"
text_raw \<open>}%EndSnippet\<close>

text_raw \<open>\DefineSnippet{add_Tick_refusal_trace}{\<close>
fun add_Tick_refusal_trace :: "'e tttrace \<Rightarrow> 'e tttrace" where
  "add_Tick_refusal_trace [] = []" |
  "add_Tick_refusal_trace ([e]\<^sub>E # t) = [e]\<^sub>E # add_Tick_refusal_trace t" |
  "add_Tick_refusal_trace ([X]\<^sub>R # t) = [X \<union> {Tick}]\<^sub>R # add_Tick_refusal_trace t"
text_raw \<open>}%EndSnippet\<close>

lemma add_Tick_refusal_trace_idempotent:
  "add_Tick_refusal_trace (add_Tick_refusal_trace \<rho>) = add_Tick_refusal_trace \<rho>"
  by (induct \<rho> rule:add_Tick_refusal_trace.induct, auto)

lemma add_Tick_refusal_trace_end_refusal:
  "add_Tick_refusal_trace (\<rho> @ [[X]\<^sub>R]) = add_Tick_refusal_trace \<rho> @ [[X \<union> {Tick}]\<^sub>R]"
  by (induct \<rho> rule:add_Tick_refusal_trace.induct, auto)

lemma add_Tick_refusal_trace_end_event:
  "add_Tick_refusal_trace (\<rho> @ [[e]\<^sub>E]) = add_Tick_refusal_trace \<rho> @ [[e]\<^sub>E]"
  by (induct \<rho> rule:add_Tick_refusal_trace.induct, auto)

lemma add_Tick_refusal_trace_end_event_trace:
  "add_Tick_refusal_trace (\<rho> @ [e]\<^sub>E # \<sigma>) = add_Tick_refusal_trace \<rho> @ [e]\<^sub>E # add_Tick_refusal_trace \<sigma>"
  by (induct \<rho> rule:add_Tick_refusal_trace.induct, auto)

lemma add_Tick_refusal_trace_tt_subset:
  "\<rho> \<subseteq>\<^sub>C add_Tick_refusal_trace \<rho>"
  by (induct \<rho> rule:add_Tick_refusal_trace.induct, auto)

lemma add_Tick_refusal_trace_same_length:
  "length \<rho> = length (add_Tick_refusal_trace \<rho>)"
  by (simp add: add_Tick_refusal_trace_tt_subset tt_subset_same_length)

lemma add_Tick_refusal_trace_filter_Tock_same_length:
  "length (filter (\<lambda> x. x = [Tock]\<^sub>E) \<rho>) = length (filter (\<lambda> x. x = [Tock]\<^sub>E) (add_Tick_refusal_trace \<rho>))"
  by (induct \<rho> rule:add_Tick_refusal_trace.induct, auto)

lemma add_Tick_refusal_trace_concat:
  "add_Tick_refusal_trace (\<rho> @ \<sigma>) = add_Tick_refusal_trace \<rho> @ add_Tick_refusal_trace \<sigma>"
  by (induct \<rho> rule:add_Tick_refusal_trace.induct, auto)

lemma add_Tick_refusal_trace_tt_prefix_subset_mono:
  assumes "\<rho> \<lesssim>\<^sub>C \<sigma>"
  shows   "add_Tick_refusal_trace \<rho> \<lesssim>\<^sub>C add_Tick_refusal_trace \<sigma>"
  using assms by(induct \<rho> \<sigma> rule:tt_prefix_subset.induct, auto)

text_raw \<open>\DefineSnippet{TT3w}{\<close>
definition TT3w :: "'e ttprocess \<Rightarrow> bool" where
  "TT3w P = (\<forall> \<rho>. \<rho> \<in> P \<longrightarrow> add_Tick_refusal_trace \<rho> \<in> P)"
text_raw \<open>}%EndSnippet\<close>

lemma TT3w_union_empty_trace:
  assumes "TT0 P" "TT1w P"
  shows "TT3w(P \<union> {[]}) = TT3w(P)"
  using assms unfolding TT3w_def
  by fastforce

lemma TT3w_TT1_imp_TT3ww:
  "TT3w P \<Longrightarrow> TT1 P \<Longrightarrow> TT3ww P"
  unfolding TT3ww_def TT3w_def TT1_def
proof (safe, simp)
  fix \<rho> X
  assume TT1_P: "\<forall>\<rho>. (\<exists>\<sigma>. \<rho> \<lesssim>\<^sub>C \<sigma> \<and> \<sigma> \<in> P) \<longrightarrow> \<rho> \<in> P"
  assume "\<rho> @ [[X]\<^sub>R] \<in> P" "\<forall>\<rho>. \<rho> \<in> P \<longrightarrow> add_Tick_refusal_trace \<rho> \<in> P"
  then have "add_Tick_refusal_trace (\<rho> @ [[X]\<^sub>R]) \<in> P"
    by auto
  then have "add_Tick_refusal_trace \<rho> @ [[X \<union> {Tick}]\<^sub>R] \<in> P"
    by (simp add: add_Tick_refusal_trace_end_refusal)
  also have "\<rho> @ [[X \<union> {Tick}]\<^sub>R] \<subseteq>\<^sub>C add_Tick_refusal_trace \<rho> @ [[X \<union> {Tick}]\<^sub>R]"
    by (simp add: add_Tick_refusal_trace_tt_subset tt_subset_combine)
  then show "\<rho> @ [[insert Tick X]\<^sub>R] \<in> P"
    using TT1_P calculation tt_subset_imp_prefix_subset by auto
qed

lemma TT3w_TT1_add_Tick_ref_Tock:
  "TT3w P \<Longrightarrow> TT1 P \<Longrightarrow> [X]\<^sub>R # [Tock]\<^sub>E # t \<in> P \<Longrightarrow> [X \<union> {Tick}]\<^sub>R # [Tock]\<^sub>E # t \<in> P"
  by (metis TT1_def TT3w_def add_Tick_refusal_trace.simps(3) add_Tick_refusal_trace_tt_subset add_Tick_refusal_trace_idempotent tt_subset_imp_prefix_subset)

lemma TT3w_TT1_add_Tick:
  assumes TT1_P: "TT1 P" and TT3w_P: "TT3w P"
  shows "\<rho> @ [X]\<^sub>R # \<sigma> \<in> P \<Longrightarrow> \<rho> @ [X \<union> {Tick}]\<^sub>R # \<sigma> \<in> P"
proof auto
  assume "\<rho> @ [X]\<^sub>R # \<sigma> \<in> P"
  then have "add_Tick_refusal_trace (\<rho> @ [X]\<^sub>R # \<sigma>) \<in> P"
    using TT3w_P unfolding TT3w_def by auto
  then show "\<rho> @ [insert Tick X]\<^sub>R # \<sigma> \<in> P"
    using TT1_P unfolding TT1_def apply auto
    by (metis Un_insert_left Un_insert_right add_Tick_refusal_trace.simps(3) add_Tick_refusal_trace_concat add_Tick_refusal_trace_tt_subset tt_subset_imp_prefix_subset insert_absorb2)
qed

lemma add_Tick_TT3w:
  assumes "\<And> \<rho> \<sigma> X. \<rho> @ [X]\<^sub>R # \<sigma> \<in> P \<Longrightarrow> \<rho> @ [X \<union> {Tick}]\<^sub>R # \<sigma> \<in> P"
  shows "TT3w P"
  using assms unfolding TT3w_def
proof auto
  fix \<rho> :: "'a tttrace"
  show "\<And>P. (\<And>\<rho> X \<sigma>. \<rho> @ [X]\<^sub>R # \<sigma> \<in> P \<Longrightarrow> \<rho> @ [insert Tick X]\<^sub>R # \<sigma> \<in> P) \<Longrightarrow> \<rho> \<in> P
    \<Longrightarrow> add_Tick_refusal_trace \<rho> \<in> P"
  proof (induct \<rho> rule:add_Tick_refusal_trace.induct, simp_all)
    fix e t
    fix P :: "'a ttprocess"
    assume assm: "(\<And>\<rho> X \<sigma>. \<rho> @ [X]\<^sub>R # \<sigma> \<in> P \<Longrightarrow> \<rho> @ [insert Tick X]\<^sub>R # \<sigma> \<in> P)"
    assume in_P: "[e]\<^sub>E # t \<in> P"
    assume ind_hyp: "(\<And>P. (\<And>\<rho> X \<sigma>. \<rho> @ [X]\<^sub>R # \<sigma> \<in> P \<Longrightarrow> \<rho> @ [insert Tick X]\<^sub>R # \<sigma> \<in> P) \<Longrightarrow> t \<in> P
      \<Longrightarrow> add_Tick_refusal_trace t \<in> P)"
    have 1: "t \<in> {s. [e]\<^sub>E # s \<in> P}"
      using in_P by auto
    have 2: "(\<And>\<rho> X \<sigma>. \<rho> @ [X]\<^sub>R # \<sigma> \<in> {s. [e]\<^sub>E # s \<in> P} \<Longrightarrow> \<rho> @ [insert Tick X]\<^sub>R # \<sigma> \<in> {s. [e]\<^sub>E # s \<in> P})"
      by (auto, metis Cons_eq_appendI assm)
    show "[e]\<^sub>E # add_Tick_refusal_trace t \<in> P"
      using ind_hyp 1 2 by blast
  next
    fix X t
    fix P :: "'a ttprocess"
    assume assm: "(\<And>\<rho> X \<sigma>. \<rho> @ [X]\<^sub>R # \<sigma> \<in> P \<Longrightarrow> \<rho> @ [insert Tick X]\<^sub>R # \<sigma> \<in> P)"
    assume in_P: "[X]\<^sub>R # t \<in> P"
    assume ind_hyp: "(\<And>P. (\<And>\<rho> X \<sigma>. \<rho> @ [X]\<^sub>R # \<sigma> \<in> P \<Longrightarrow> \<rho> @ [insert Tick X]\<^sub>R # \<sigma> \<in> P) \<Longrightarrow> t \<in> P
      \<Longrightarrow> add_Tick_refusal_trace t \<in> P)"
    have 1: "t \<in> {s. [X]\<^sub>R # s \<in> P}"
      using in_P by auto
    have 2: "(\<And>\<rho> Y \<sigma>. \<rho> @ [Y]\<^sub>R # \<sigma> \<in> {s. [X]\<^sub>R # s \<in> P} \<Longrightarrow> \<rho> @ [insert Tick Y]\<^sub>R # \<sigma> \<in> {s. [X]\<^sub>R # s \<in> P})"
      by (auto, metis Cons_eq_appendI assm)
    have "[X]\<^sub>R # add_Tick_refusal_trace t \<in> P"
      using ind_hyp 1 2 by blast
    then show "[insert Tick X]\<^sub>R # add_Tick_refusal_trace t \<in> P"
      using assm[where \<rho>="[]"] by force
  qed
qed

lemma TT1_TT3w_equiv_TT3:
  assumes "TT1 P"
  shows "TT3 P = TT3w P"
  unfolding TT3_def using add_Tick_TT3w TT3w_TT1_add_Tick assms by auto

lemma TT3w_TT1_imp_Ref_Tock:
  assumes "s @ [[X]\<^sub>R, [Tock]\<^sub>E] \<in> P" "TT1 P" "TT3w P"
  shows "s @ [[X \<union> {Tick}]\<^sub>R,[Tock]\<^sub>E] \<in> P"
  using assms unfolding TT1_def TT3w_def
proof (auto)
  fix \<rho> X s
  assume TT1_P: "\<forall>\<rho>. (\<exists>\<sigma>. \<rho> \<lesssim>\<^sub>C \<sigma> \<and> \<sigma> \<in> P) \<longrightarrow> \<rho> \<in> P"
  assume "s @ [[X]\<^sub>R, [Tock]\<^sub>E] \<in> P" "\<forall>\<rho>. \<rho> \<in> P \<longrightarrow> add_Tick_refusal_trace \<rho> \<in> P"
  then have "add_Tick_refusal_trace (s @ [[X]\<^sub>R, [Tock]\<^sub>E]) \<in> P"
    by auto
  then have "add_Tick_refusal_trace s @ add_Tick_refusal_trace ([[X]\<^sub>R, [Tock]\<^sub>E]) \<in> P"
    by (simp add: add_Tick_refusal_trace_concat)
  then have "add_Tick_refusal_trace s @ [[X \<union> {Tick}]\<^sub>R,[Tock]\<^sub>E] \<in> P"
    by auto
  also have "s @ [[X \<union> {Tick}]\<^sub>R,[Tock]\<^sub>E] \<subseteq>\<^sub>C add_Tick_refusal_trace s @ [[X \<union> {Tick}]\<^sub>R,[Tock]\<^sub>E]"
    by (simp add: add_Tick_refusal_trace_tt_subset tt_subset_combine)
  then show "s @ [[insert Tick X]\<^sub>R, [Tock]\<^sub>E] \<in> P"
    using TT1_P calculation tt_subset_imp_prefix_subset by auto
qed

lemma TT2_Ref_Tock_augment:
  assumes "s @ [[X]\<^sub>R, [Tock]\<^sub>E] \<in> P" "TT2 P" "TT1 P" "TT3w P"
  shows "s @ [[X \<union> {e. e \<noteq> Tock \<and> s @ [[e]\<^sub>E] \<notin> P} \<union> {Tick}]\<^sub>R, [Tock]\<^sub>E] \<in> P"
proof -
  have "{e. e \<noteq> Tock \<and> s @ [[e]\<^sub>E] \<notin> P} \<inter> {e. (e \<noteq> Tock \<and> s @ [[e]\<^sub>E] \<in> P) \<or> (e = Tock \<and> s @ [[X]\<^sub>R, [e]\<^sub>E] \<in> P) } = {}"
    by auto
  then have "s @ [[X \<union> {e. e \<noteq> Tock \<and> s @ [[e]\<^sub>E] \<notin> P}]\<^sub>R] @ [[Tock]\<^sub>E] \<in> P"
    using assms by (simp add: TT2_def) 
  then have "s @ [[X \<union> {e. e \<noteq> Tock \<and> s @ [[e]\<^sub>E] \<notin> P} \<union> {Tick}]\<^sub>R] @ [[Tock]\<^sub>E] \<in> P"
    using TT3w_TT1_imp_Ref_Tock assms
    by auto
  then show ?thesis by auto
qed

lemma TT3w_middle_Ref_with_Tick:
  assumes "s @ [[X]\<^sub>R] @ xs \<in> P" "TT1 P" "TT3w P"
  shows "s @ [[X \<union> {Tick}]\<^sub>R] @ xs \<in> P"
proof -
  have add_Tick_in_P:"add_Tick_refusal_trace (s @ [[X]\<^sub>R] @ xs) \<in> P"
    using assms unfolding TT3w_def by blast

  have add_Tick_dist:"add_Tick_refusal_trace (s @ [[X]\<^sub>R] @ xs) =
     add_Tick_refusal_trace s @ [[X \<union> {Tick}]\<^sub>R] @ add_Tick_refusal_trace(xs)"
    by (simp add: add_Tick_refusal_trace_concat add_Tick_refusal_trace_end_refusal)
  
  have s_le_addTick:"s \<lesssim>\<^sub>C add_Tick_refusal_trace s"
    by (simp add: add_Tick_refusal_trace_tt_subset tt_subset_imp_prefix_subset)
  have "xs \<lesssim>\<^sub>C add_Tick_refusal_trace(xs)"
    by (simp add: add_Tick_refusal_trace_tt_subset tt_subset_imp_prefix_subset)

  then have a:"add_Tick_refusal_trace s @ [[X \<union> {Tick}]\<^sub>R] @ xs
              \<lesssim>\<^sub>C
              add_Tick_refusal_trace s @ [[X \<union> {Tick}]\<^sub>R] @ add_Tick_refusal_trace(xs)"
  using add_Tick_in_P add_Tick_dist tt_prefix_common_concat
    by blast
  then have b:"s @ [[X \<union> {Tick}]\<^sub>R] @ xs \<lesssim>\<^sub>C add_Tick_refusal_trace s @ [[X \<union> {Tick}]\<^sub>R] @ xs"
    using tt_prefix_common_concat_eq_size add_Tick_refusal_trace_same_length s_le_addTick by blast

  have "s @ [[X \<union> {Tick}]\<^sub>R] @ xs \<in> P"
    using a b add_Tick_in_P assms
    by (metis TT1_def add_Tick_dist)
  then show ?thesis by auto
qed

lemma TT2_TT3w_extends_Ref:
  assumes "TT2 P" "TT3w P" "TT1 P" "s @ [[X]\<^sub>R] @ xs \<in> P"
  shows "s @ [[X \<union> {e. e \<noteq> Tock \<and> s @ [[e]\<^sub>E] \<notin> P \<or> e = Tock \<and> s @ [[X]\<^sub>R, [Tock]\<^sub>E] \<notin> P} \<union> {Tick}]\<^sub>R] @ xs \<in> P"
proof -
  obtain Y where Y:"Y = {e. e \<noteq> Tock \<and> s @ [[e]\<^sub>E] \<notin> P \<or> e = Tock \<and> s @ [[X]\<^sub>R, [Tock]\<^sub>E] \<notin> P}"
    by auto
  then have "Y \<inter> {e. (e \<noteq> Tock \<and> s @ [[e]\<^sub>E] \<in> P) \<or> (e = Tock \<and> s @ [[X]\<^sub>R, [e]\<^sub>E] \<in> P) } = {}"
    by auto
  then have "s @ [[X \<union> Y]\<^sub>R] @ xs \<in> P"
    using assms unfolding TT2_def by auto
  then have "s @ [[X \<union> Y \<union> {Tick}]\<^sub>R] @ xs \<in> P"
    using assms TT3w_middle_Ref_with_Tick by blast
  then show ?thesis using Y by auto
qed

definition mkTT3w :: "'e ttobs list set \<Rightarrow> 'e ttobs list set" where
"mkTT3w P = P \<union> {add_Tick_refusal_trace \<rho>|\<rho>. \<rho> \<in> P}"

subsection \<open>Process Well-formedness\<close>

definition TTwf :: "'e ttobs list set \<Rightarrow> bool" where
  "TTwf P = (\<forall>x\<in>P. ttWF x)"

lemma TTwf_imp_dist:
  assumes "TTwf(P \<union> Q)" 
  shows "TTwf(P) \<and> TTwf(Q)"
  unfolding TTwf_def by (meson TTwf_def Un_iff assms)

lemma TTwf_cons_end_not_refusal_refusal:
  assumes "TTwf P"
  shows "\<not> sa @ [[S]\<^sub>R, [Z]\<^sub>R] \<in> P"
  using assms unfolding TTwf_def using ttWF_dist_cons_refusal
  using ttWF.simps(13) by blast

lemma TTwf_no_ill_Tock [simp]:
  assumes "TTwf P" "e \<noteq> Tock"
  shows "sa @ [[X]\<^sub>R, [e]\<^sub>E] \<notin> P"
  using assms unfolding TTwf_def apply (induct sa rule:ttWF.induct, auto)
    apply (cases e, auto)
  apply (metis assms(2) ttWF.simps(11) ttWF.simps(12) ttWF.simps(4) ttWF_dist_cons_refusal ttevent.exhaust)
  by (metis append_Cons ttWF.simps(11) ttWF.simps(12) ttWF_dist_cons_refusal ttevent.exhaust)

lemma ttWF_dist_notTock_cons:
  assumes "ttWF (xs @ ([[x]\<^sub>E] @ ys))" "x \<noteq> Tock"
  shows "ttWF ([[x]\<^sub>E] @ ys)"
  using assms apply (induct xs rule:ttWF.induct, auto)
  by (cases x, auto)

lemma ttWF_before_Tock_not_Tock:
  assumes "ttWF (xs @ [[x1]\<^sub>E, [Tock]\<^sub>E])"
  shows "x1 \<noteq> Tock"
  using assms by (induct xs rule:ttWF.induct, auto)

lemma TTwf_not_event_before_Tock:
  assumes "TTwf(Q)"
  shows "xs @ [[x1]\<^sub>E, [Tock]\<^sub>E] \<notin> Q"
  using assms
proof -
  have "\<not> ttWF (xs @ [[x1]\<^sub>E, [Tock]\<^sub>E])"
    using assms apply (induct xs rule:ttWF.induct, auto)
    using ttWF.elims(2) by auto
  then have "xs @ [[x1]\<^sub>E, [Tock]\<^sub>E] \<notin> Q"
    using assms TTwf_def by blast
  then show ?thesis .
qed


lemma TTwf_Refusal_imp_no_Tock:
  assumes "sa @ [[S]\<^sub>R] \<in> Q" "TTwf(Q)"
  shows "sa @ [[Tock]\<^sub>E] \<notin> Q"
  using assms apply (induct sa rule:rev_induct, auto)
  using TTwf_def ttWF.simps(6) apply blast
  by (metis TTwf_cons_end_not_refusal_refusal TTwf_not_event_before_Tock ttobs.exhaust)

lemma TTwf_mkTT1:
  assumes "TTwf P"
  shows "TTwf(mkTT1(P))"
  using assms unfolding mkTT1_def apply auto
  by (smt TTwf_def Un_iff mem_Collect_eq tt_prefix_subset_ttWF)

lemma ttWFx_mkTT1:
  assumes "ttWFx P"
  shows "ttWFx(mkTT1(P))"
  using assms unfolding mkTT1_def ttWFx_def apply auto
  using tt_prefix_of_ttWFx_trace by blast

lemma TT3w_mkTT1:
  assumes "TT3w P"
  shows "TT3w(mkTT1(P))"
  using assms unfolding mkTT1_def TT3w_def apply auto
  using add_Tick_refusal_trace_tt_prefix_subset_mono by blast

lemma TTwf_concat_two_events_not_Tick_butlast:
  assumes "ys @ [[e1]\<^sub>E] @ [[e2]\<^sub>E] \<in> P" "TTwf P" 
  shows "e1 \<noteq> Tick"
proof -
  have "ttWF (ys @ [[e1]\<^sub>E] @ [[e2]\<^sub>E])"
    using assms unfolding TTwf_def by auto
  then show ?thesis
    by (induct ys rule:ttWF.induct, auto)
qed

lemma TTwf_concat_prefix_set_no_Tick:
  assumes "ys @ [[e1]\<^sub>E] \<in> P" "TTwf P" 
  shows "[Tick]\<^sub>E \<notin> set ys"
proof -
  have "ttWF (ys @ [[e1]\<^sub>E])"
    using assms unfolding TTwf_def by auto
  then show ?thesis
    by (induct ys rule:ttWF.induct, auto)
qed

lemma TTwf_concat_prefix_of_ref_set_no_Tick:
  assumes "ys @ [[e1]\<^sub>R] \<in> P" "TTwf P" 
  shows "[Tick]\<^sub>E \<notin> set ys"
proof -
  have "ttWF (ys @ [[e1]\<^sub>R])"
    using assms unfolding TTwf_def by auto
  then show ?thesis
    by (induct ys rule:ttWF.induct, auto)
qed

subsection \<open>Combined Healthiness Conditions\<close>

definition TT :: "'e ttobs list set \<Rightarrow> bool" where
  "TT P = ((\<forall>x\<in>P. ttWF x) \<and> TT0 P \<and> TT1 P \<and> TT2w P \<and> ttWFx P)"

lemma TT_TT0: "TT P \<Longrightarrow> TT0 P"
  using TT_def by auto

lemma TT_TT1: "TT P \<Longrightarrow> TT1 P"
  using TT_def by auto

lemma TT1_TT1w: "TT1 P \<Longrightarrow> TT1w P"
  unfolding TT1_def TT1w_def
  using tt_prefix_imp_prefix_subset by blast

lemma TT_TT1w: "TT P \<Longrightarrow> TT1w P"
  unfolding TT_def using TT1_TT1w by auto

lemma TT_TT2w: "TT P \<Longrightarrow> TT2w P"
  using TT_def by auto

lemma TT_ttWFx: "TT P \<Longrightarrow> ttWFx P"
  using TT_def by auto

lemma TT_wf: "TT P \<Longrightarrow> \<forall>x\<in>P. ttWF x"
  using TT_def by auto

lemma TT_TTwf: "TT P \<Longrightarrow> TTwf P"
  unfolding TT_def TTwf_def by auto

lemma TT0_TT1w_empty: "TT0 P \<Longrightarrow> TT1w P \<Longrightarrow> [] \<in> P"
  unfolding TT0_def TT1w_def apply auto
  using tt_prefix.simps(1) by blast

lemma TT0_TT1_empty: "TT0 P \<Longrightarrow> TT1 P \<Longrightarrow> [] \<in> P"
  unfolding TT0_def TT1_def
proof auto
  fix x
  assume x_in_P: "x \<in> P"
  assume "\<forall>\<rho>. (\<exists>\<sigma>. \<rho> \<lesssim>\<^sub>C \<sigma> \<and> \<sigma> \<in> P) \<longrightarrow> \<rho> \<in> P"
  then have "(\<exists>\<sigma>. [] \<lesssim>\<^sub>C \<sigma> \<and> \<sigma> \<in> P) \<longrightarrow> [] \<in> P"
    by blast
  then have "[] \<in> P"
    using tt_prefix_subset.simps(1) x_in_P by blast
  also assume "[] \<notin> P"
  then show "False"
    using calculation by auto
qed

lemma TT_empty: "TT P \<Longrightarrow> [] \<in> P"
  by (simp add: TT0_TT1_empty TT_TT0 TT_TT1)

lemmas TT_defs = TT_def TT0_def TT1_def TT2w_def ttWFx_def

lemma TT_init_event:
  assumes "TT P" "\<exists> t. [Event e]\<^sub>E # t \<in> P"
  shows "TT {t. [Event e]\<^sub>E # t \<in> P}"
  unfolding TT_defs
proof auto
  fix x 
  assume "[Event e]\<^sub>E # x \<in> P"
  then have "ttWF ([Event e]\<^sub>E # x)"
    using TT_wf assms(1) by blast
  then show "ttWF x"
    by auto
next
  show "\<exists>x. [Event e]\<^sub>E # x \<in> P"
    using assms(2) by auto
next
  fix \<rho> \<sigma> :: "'a ttobs list"
  assume "\<rho> \<lesssim>\<^sub>C \<sigma>"
  then have "[Event e]\<^sub>E # \<rho> \<lesssim>\<^sub>C [Event e]\<^sub>E # \<sigma>"
    by auto
  then show "[Event e]\<^sub>E # \<sigma> \<in> P \<Longrightarrow> [Event e]\<^sub>E # \<rho> \<in> P"
    using TT1_def TT_TT1 assms(1) by blast
next
  fix \<rho> X Y
  have "\<forall>\<rho> X Y. \<rho> @ [[X]\<^sub>R] \<in> P \<and> Y \<inter> {e. e \<noteq> Tock \<and> \<rho> @ [[e]\<^sub>E] \<in> P \<or> e = Tock \<and> \<rho> @ [[X]\<^sub>R, [e]\<^sub>E] \<in> P} = {} \<longrightarrow>
         \<rho> @ [[X \<union> Y]\<^sub>R] \<in> P"
    using TT2w_def TT_TT2w assms(1) by auto
  then show "[Event e]\<^sub>E # \<rho> @ [[X]\<^sub>R] \<in> P \<Longrightarrow>
    Y \<inter> {ea. ea \<noteq> Tock \<and> [Event e]\<^sub>E # \<rho> @ [[ea]\<^sub>E] \<in> P \<or> ea = Tock \<and> [Event e]\<^sub>E # \<rho> @ [[X]\<^sub>R, [ea]\<^sub>E] \<in> P} = {} \<Longrightarrow>
      [Event e]\<^sub>E # \<rho> @ [[X \<union> Y]\<^sub>R] \<in> P"
    by (erule_tac x="[Event e]\<^sub>E # \<rho>" in allE, auto)
next
  fix x
  assume "[Event e]\<^sub>E # x \<in> P"
  then have "ttWFx_trace ([Event e]\<^sub>E # x)"
    using ttWFx_def TT_ttWFx assms(1) by blast
  then show "ttWFx_trace x"
    by (cases x, auto)
qed

lemma TT_init_tock:
  assumes "TT P" "\<exists> t. [X]\<^sub>R # [Tock]\<^sub>E # t \<in> P"
  shows "TT {t. [X]\<^sub>R # [Tock]\<^sub>E # t \<in> P}"
  unfolding TT_defs
proof auto
  fix x
  assume "[X]\<^sub>R # [Tock]\<^sub>E # x \<in> P"
  then have "ttWF ([X]\<^sub>R # [Tock]\<^sub>E # x)"
    using TT_wf assms(1) by blast
  then show "ttWF x"
    by auto
next
  show "\<exists>x. [X]\<^sub>R # [Tock]\<^sub>E # x \<in> P"
    using assms(2) by auto
next
  fix \<rho> \<sigma> :: "'a ttobs list"
  assume "\<rho> \<lesssim>\<^sub>C \<sigma>"
  then have "[X]\<^sub>R # [Tock]\<^sub>E # \<rho> \<lesssim>\<^sub>C [X]\<^sub>R # [Tock]\<^sub>E # \<sigma>"
    by auto
  also assume "[X]\<^sub>R # [Tock]\<^sub>E # \<sigma> \<in> P"
  then show "[X]\<^sub>R # [Tock]\<^sub>E # \<rho> \<in> P"
    using assms(1) calculation unfolding TT_def TT1_def apply auto 
    by (erule_tac x="[X]\<^sub>R # [Tock]\<^sub>E # \<rho>" in allE, auto)
next
  fix \<rho> Xa Y
  assume "[X]\<^sub>R # [Tock]\<^sub>E # \<rho> @ [[Xa]\<^sub>R] \<in> P"
  and "Y \<inter> {e. e \<noteq> Tock \<and> [X]\<^sub>R # [Tock]\<^sub>E # \<rho> @ [[e]\<^sub>E] \<in> P \<or> e = Tock \<and> [X]\<^sub>R # [Tock]\<^sub>E # \<rho> @ [[Xa]\<^sub>R, [e]\<^sub>E] \<in> P} = {}"
  then show "[X]\<^sub>R # [Tock]\<^sub>E # \<rho> @ [[Xa \<union> Y]\<^sub>R] \<in> P"
    using assms(1) unfolding TT_def TT2w_def apply auto
    by (erule_tac x="[X]\<^sub>R # [Tock]\<^sub>E # \<rho>" in allE, auto)
next
  fix x
  assume "[X]\<^sub>R # [Tock]\<^sub>E # x \<in> P"
  then have "ttWFx_trace ([X]\<^sub>R # [Tock]\<^sub>E # x)"
    using ttWFx_def TT_ttWFx assms(1) by blast
  then show "ttWFx_trace x"
    by auto
qed

lemma TT2w_init_event:
  assumes "TT2w P"
  shows "TT2w {t. [Event e]\<^sub>E # t \<in> P}"
  using assms unfolding TT2w_def apply (auto)
  by (erule_tac x="[Event e]\<^sub>E # \<rho>" in allE, auto)

lemma TT2w_init_tock:
  assumes "TT2w P"
  shows "TT2w {t. [X]\<^sub>R # [Tock]\<^sub>E # t \<in> P}"
  using assms unfolding TT2w_def apply (auto)
  by (erule_tac x="[X]\<^sub>R # [Tock]\<^sub>E # \<rho>" in allE, auto)

lemma TT2_init_event:
  assumes "TT2 P"
  shows "TT2 {t. [Event e]\<^sub>E # t \<in> P}"
  using assms unfolding TT2_def apply (auto)
  by (erule_tac x="[Event e]\<^sub>E # \<rho>" in allE, auto)

lemma TT2_init_tock:
  assumes "TT2 P"
  shows "TT2 {t. [X]\<^sub>R # [Tock]\<^sub>E # t \<in> P}"
  using assms unfolding TT2_def apply (auto)
  by (erule_tac x="[X]\<^sub>R # [Tock]\<^sub>E # \<rho>" in allE, auto)

section {* Initial sequences of tocks *}

inductive_set tocks :: "'e ttevent set \<Rightarrow> 'e ttobs list set" for X :: "'e ttevent set" where
  empty_in_tocks: "[] \<in> tocks X" |
  tock_insert_in_tocks: "Y \<subseteq> X \<Longrightarrow> \<rho> \<in> tocks X \<Longrightarrow> [Y]\<^sub>R # [Tock]\<^sub>E # \<rho> \<in> tocks X"

lemma tocks_wf: "Tock \<notin> X \<Longrightarrow> t\<in>tocks X \<Longrightarrow> ttWF t"
  by (induct t rule:ttWF.induct, auto, (cases rule:tocks.cases, auto)+)

lemma tocks_append_wf: "Tock \<notin> X \<Longrightarrow> ttWF s \<Longrightarrow> t\<in>tocks X \<Longrightarrow> ttWF (t @ s)"
  by (induct t rule:ttWF.induct, auto, (cases rule:tocks.cases, auto)+)

lemma tocks_append_wf2: "ttWF (t @ s) \<Longrightarrow> t\<in>tocks X \<Longrightarrow> ttWF s"
  by (induct t rule:ttWF.induct, auto, (cases rule:tocks.cases, auto)+)

lemma tocks_wfw: "t\<in>tocks X \<Longrightarrow> ttWFw t"
  by (induct t rule:ttWFw.induct, auto, (cases rule:tocks.cases, auto)+)

lemma tocks_append_wfw: "ttWFw s \<Longrightarrow> t\<in>tocks X \<Longrightarrow> ttWFw (t @ s)"
  by (induct t rule:ttWFw.induct, auto, (cases rule:tocks.cases, auto)+)

lemma tocks_append_wfw2: "ttWFw (t @ s) \<Longrightarrow> t\<in>tocks X \<Longrightarrow> ttWFw s"
  by (induct t rule:ttWFw.induct, auto, (cases rule:tocks.cases, auto)+)

lemma tocks_append_tocks: "t\<in>tocks X \<Longrightarrow> s\<in>tocks X \<Longrightarrow> t @ s \<in>tocks X"
  using tocks.cases by (induct t rule:ttWF.induct, auto, metis (no_types, lifting) list.inject list.simps(3) tocks.simps)

lemma tocks_append_nontocks: "t\<in>tocks X \<Longrightarrow> s\<notin>tocks X \<Longrightarrow> t @ s \<notin>tocks X"
  using tocks.cases by (induct t rule:ttWF.induct, auto)

lemma tocks_subset: "t\<in>tocks X \<Longrightarrow> X \<subseteq> Y \<Longrightarrow> t\<in>tocks Y"
  by (induct t rule:tocks.induct, auto simp add: tocks.intros)

lemma split_tocks:  "ttWF x \<Longrightarrow> \<exists> s. \<exists>t\<in>tocks UNIV. x = t @ s"
  using tocks.empty_in_tocks by (induct x rule:ttWF.induct, auto)

lemma split_tocks_longest:  "ttWF x \<Longrightarrow> \<exists> s. \<exists>t\<in>tocks UNIV. x = t @ s \<and> (\<forall>t'\<in>tocks UNIV. t' \<le>\<^sub>C x \<longrightarrow> t' \<le>\<^sub>C t)"
proof (induct x rule:ttWF.induct, auto)
  show "[] \<in> tocks UNIV" 
    using tocks.empty_in_tocks by auto
next
  fix X :: "'e ttevent set"
  show "\<exists>s. \<exists>t\<in>tocks UNIV. [[X]\<^sub>R] = t @ s \<and> (\<forall>t'\<in>tocks UNIV. t' \<le>\<^sub>C [[X]\<^sub>R] \<longrightarrow> t' \<le>\<^sub>C t)"
    apply (rule_tac x="[[X]\<^sub>R]" in exI) 
    apply (rule_tac x="[]" in bexI)
     apply (auto simp add: empty_in_tocks)
    apply (case_tac t', auto)
    using tt_prefix_decompose tocks.simps by auto
next
  show " \<exists>s. \<exists>t\<in>tocks UNIV. [[Tick]\<^sub>E] = t @ s \<and> (\<forall>t'\<in>tocks UNIV. t' \<le>\<^sub>C [[Tick]\<^sub>E] \<longrightarrow> t' \<le>\<^sub>C t)"
    apply (rule_tac x="[[Tick]\<^sub>E]" in exI, rule_tac x="[]" in bexI, auto simp add: empty_in_tocks)
    apply (case_tac t', auto)
    using tt_prefix_decompose tocks.simps by auto
next
  fix e s t
  show "\<exists>sa. \<exists>ta\<in>tocks UNIV. [Event e]\<^sub>E # t @ s = ta @ sa \<and> (\<forall>t'\<in>tocks UNIV. t' \<le>\<^sub>C [Event e]\<^sub>E # t @ s \<longrightarrow> t' \<le>\<^sub>C ta)"
    apply (rule_tac x="[Event e]\<^sub>E # t @ s" in exI, rule_tac x="[]" in bexI, auto)
    apply (case_tac t', auto)
    using tt_prefix_decompose tocks.simps by auto
next
  fix X s t
  assume case_assms: "t \<in> tocks UNIV" " \<forall>t'\<in>tocks UNIV. t' \<le>\<^sub>C t @ s \<longrightarrow> t' \<le>\<^sub>C t"
  then show "\<exists>sa. \<exists>ta\<in>tocks UNIV. [X]\<^sub>R # [Tock]\<^sub>E # t @ s = ta @ sa \<and> (\<forall>t'\<in>tocks UNIV. t' \<le>\<^sub>C [X]\<^sub>R # [Tock]\<^sub>E # t @ s \<longrightarrow> t' \<le>\<^sub>C ta)"
  proof (rule_tac x="s" in exI, rule_tac x="[X]\<^sub>R # [Tock]\<^sub>E # t" in bexI, auto)
    fix t' :: "'b ttobs list"
    assume "t' \<in> tocks UNIV" "t' \<le>\<^sub>C [X]\<^sub>R # [Tock]\<^sub>E # t @ s"
    then show "t' \<le>\<^sub>C [X]\<^sub>R # [Tock]\<^sub>E # t"
      by (cases rule:tocks.cases, auto simp add: case_assms(2))
  next
    show "t \<in> tocks UNIV \<Longrightarrow> [X]\<^sub>R # [Tock]\<^sub>E # t \<in> tocks UNIV"
      by (simp add: tocks.tock_insert_in_tocks)
  qed
qed

lemma tt_prefix_subset_tocks: "s \<in> tocks X \<Longrightarrow> t \<lesssim>\<^sub>C s \<Longrightarrow> t \<in> {t. \<exists>s\<in>tocks X. t = s \<or> (\<exists>Y. t = s @ [[Y]\<^sub>R] \<and> Y \<subseteq> X)}"
proof -
  assume "s \<in> tocks X"
  then have "ttWFw s"
    using tocks_wfw by blast
  also have "ttWFw s \<longrightarrow> s \<in> tocks X \<longrightarrow> t \<lesssim>\<^sub>C s \<longrightarrow> t \<in> {t. \<exists>s\<in>tocks X. t = s \<or> (\<exists>Y. t = s @ [[Y]\<^sub>R] \<and> Y \<subseteq> X)}"
    apply (induct t s rule:ttWFw2.induct)
    apply (simp_all add: empty_in_tocks)
    using tocks.simps apply auto[1]
    apply (case_tac \<sigma> rule:ttWFw.cases, auto)
    apply (rule_tac x="[]" in bexI, simp, insert tocks.cases, force, simp add: empty_in_tocks)
    apply (rule_tac x="[]" in bexI, simp, insert tocks.cases, force, simp add: empty_in_tocks)
    apply (metis list.inject list.simps(3) tocks.simps)
    apply (metis ttobs.inject(2) dual_order.trans list.inject list.simps(3) tocks.simps)
    apply (metis ttobs.inject(2) dual_order.trans list.inject list.simps(3) tocks.empty_in_tocks tocks.simps)
    apply (blast, blast, blast, blast)
    apply (rule_tac x="[Xa]\<^sub>R # [Tock]\<^sub>E # s" in bexI, simp)
    apply (metis ttobs.inject(2) list.inject list.simps(3) rev_subsetD subsetI tocks.simps)
    apply (rule_tac x="[Xa]\<^sub>R # [Tock]\<^sub>E # s" in bexI, simp)
    apply (metis ttobs.inject(2) list.inject list.simps(3) rev_subsetD subsetI tocks.simps)
    apply (case_tac \<sigma> rule:ttWFw.cases, auto)+
    done
  then show "s \<in> tocks X \<Longrightarrow> t \<lesssim>\<^sub>C s \<Longrightarrow> t \<in> {t. \<exists>s\<in>tocks X. t = s \<or> (\<exists>Y. t = s @ [[Y]\<^sub>R] \<and> Y \<subseteq> X)}" using calculation by auto
qed

lemma tt_prefix_tocks: "s \<in> tocks X \<Longrightarrow> t \<le>\<^sub>C s \<Longrightarrow> t \<in> {t. \<exists>s\<in>tocks X. t = s \<or> (\<exists>Y. t = s @ [[Y]\<^sub>R] \<and> Y \<subseteq> X)}"
  using tt_prefix_imp_prefix_subset tt_prefix_subset_tocks by blast

lemma tt_prefix_subset_tocks2: "s \<in> tocks X \<Longrightarrow> t \<lesssim>\<^sub>C s \<Longrightarrow> t \<in> {t. \<exists>s'\<in>tocks X. s'\<lesssim>\<^sub>C s \<and> (t = s' \<or> (\<exists>Y. t = s' @ [[Y]\<^sub>R] \<and> Y \<subseteq> X))}"
proof -
  assume "s \<in> tocks X"
  then have "ttWFw s"
    using tocks_wfw by blast
  also have "ttWFw s \<longrightarrow> s \<in> tocks X \<longrightarrow> t \<lesssim>\<^sub>C s \<longrightarrow> t \<in> {t. \<exists>s'\<in>tocks X. s'\<lesssim>\<^sub>C s \<and> (t = s' \<or> (\<exists>Y. t = s' @ [[Y]\<^sub>R] \<and> Y \<subseteq> X))}"
    apply (induct t s rule:ttWFw2.induct)
    apply (simp_all add: empty_in_tocks)
    using tocks.simps apply auto[1]
    apply (case_tac \<sigma> rule:ttWFw.cases, auto)
    apply (rule_tac x="[]" in bexI, simp, insert tocks.cases, force, simp add: empty_in_tocks)
    apply (rule_tac x="[]" in bexI, simp, insert tocks.cases, force, simp add: empty_in_tocks)
    apply (metis list.inject list.simps(3) tocks.simps)
    apply (metis ttobs.simps(4) list.inject list.simps(3) tocks.simps)
    apply (metis tt_prefix_subset.simps(1) ttobs.inject(2) list.distinct(1) list.inject subset_trans tocks.simps)
    apply (blast, blast, blast, blast)
    apply (rule_tac x="[Xa]\<^sub>R # [Tock]\<^sub>E # s'" in bexI, auto)
    apply (metis ttobs.inject(2) list.inject list.simps(3) rev_subsetD subsetI tocks.simps)
    apply (rule_tac x="[Xa]\<^sub>R # [Tock]\<^sub>E # s'" in bexI, simp)
    apply (metis ttobs.inject(2) list.inject list.simps(3) rev_subsetD subsetI tocks.simps)
    apply (case_tac \<sigma> rule:ttWFw.cases, auto)+
    done
  then show "s \<in> tocks X \<Longrightarrow> t \<lesssim>\<^sub>C s \<Longrightarrow> t \<in> {t. \<exists>s'\<in>tocks X. s' \<lesssim>\<^sub>C s \<and> (t = s' \<or> (\<exists>Y. t = s' @ [[Y]\<^sub>R] \<and> Y \<subseteq> X))}"
    using calculation by blast
qed

lemma tt_prefix_subset_tocks_refusal: "s \<in> tocks X \<Longrightarrow> \<rho> \<lesssim>\<^sub>C s @ [[Y]\<^sub>R] \<Longrightarrow> (\<exists> t \<in> tocks X. \<rho> = t \<or> (\<exists> Z. \<rho> = t @ [[Z]\<^sub>R] \<and> (Z \<subseteq> X \<or> Z \<subseteq> Y)))"
proof -
  assume "s \<in> tocks X"
  then have "ttWFw (s @ [[Y]\<^sub>R])"
    using ttWFw.simps(2) tocks_append_wfw by blast
  also have "s \<in> tocks X \<longrightarrow> ttWFw (s @ [[Y]\<^sub>R]) \<longrightarrow> \<rho> \<lesssim>\<^sub>C s @ [[Y]\<^sub>R] \<longrightarrow> (\<exists> t \<in> tocks X. \<rho> = t \<or> (\<exists> Z. \<rho> = t @ [[Z]\<^sub>R] \<and> (Z \<subseteq> X \<or> Z \<subseteq> Y)))"
    apply (induct \<rho> s rule:ttWFw2.induct, auto simp add: empty_in_tocks)
    apply (rule_tac x="[]" in bexI, auto simp add: empty_in_tocks)
    apply (metis contra_subsetD ttobs.inject(2) list.inject list.simps(3) tocks.simps)
    using tocks.cases apply auto
    apply blast
    apply blast
    apply blast
    apply (rule_tac x="[Xa]\<^sub>R # [Tock]\<^sub>E # t" in bexI, auto simp add: empty_in_tocks)
           apply (metis ttobs.inject(2) list.inject list.simps(3) rev_subsetD subsetI tocks.simps)
    apply (rule_tac x="[Xa]\<^sub>R # [Tock]\<^sub>E # t" in bexI, auto simp add: empty_in_tocks)
    apply (metis ttobs.inject(2) list.inject list.simps(3) rev_subsetD subsetI tocks.simps)
    apply (rule_tac x="[Xa]\<^sub>R # [Tock]\<^sub>E # t" in bexI, auto simp add: empty_in_tocks)
    apply (metis ttobs.inject(2) list.inject list.simps(3) rev_subsetD subsetI tocks.simps)
    apply (meson ttWFw.simps(12) tt_prefix_subset_ttWFw)
    apply (meson ttWFw.simps(11) tt_prefix_subset_ttWFw)
    apply (meson ttWFw.simps(13) tt_prefix_subset_ttWFw)
    apply (meson ttWFw.simps(10) tt_prefix_subset_ttWFw)
    by (meson ttWFw.simps(6) tt_prefix_subset_ttWFw)
  then show "s \<in> tocks X \<Longrightarrow> \<rho> \<lesssim>\<^sub>C s @ [[Y]\<^sub>R] \<Longrightarrow> \<exists>t\<in>tocks X. \<rho> = t \<or> (\<exists>Z. \<rho> = t @ [[Z]\<^sub>R] \<and> (Z \<subseteq> X \<or> Z \<subseteq> Y))"
    using calculation by auto
qed

lemma tt_prefix_subset_tocks_refusal2: "s \<in> tocks X \<Longrightarrow> \<rho> \<lesssim>\<^sub>C s @ [[Y]\<^sub>R] \<Longrightarrow>
  (\<exists> t \<in> tocks X. t \<lesssim>\<^sub>C s \<and> (\<rho> = t \<or> (\<exists> Z. \<rho> = t @ [[Z]\<^sub>R] \<and> ((Z \<subseteq> X \<and> length (filter (\<lambda> x. x = [Tock]\<^sub>E) t) < length (filter (\<lambda> x. x = [Tock]\<^sub>E) s)) \<or> (Z \<subseteq> Y \<and> length (filter (\<lambda> x. x = [Tock]\<^sub>E) t) = length (filter (\<lambda> x. x = [Tock]\<^sub>E) s))))))"
proof -
  assume "s \<in> tocks X"
  then have "ttWFw (s @ [[Y]\<^sub>R])"
    using ttWFw.simps(2) tocks_append_wfw by blast
  also have "s \<in> tocks X \<longrightarrow> ttWFw (s @ [[Y]\<^sub>R]) \<longrightarrow> \<rho> \<lesssim>\<^sub>C s @ [[Y]\<^sub>R] \<longrightarrow> 
    (\<exists>t\<in>tocks X.
       t \<lesssim>\<^sub>C s \<and>
       (\<rho> = t \<or>
        (\<exists>Z. \<rho> = t @ [[Z]\<^sub>R] \<and>
             (Z \<subseteq> X \<and> length [x\<leftarrow>t . x = [Tock]\<^sub>E] < length [x\<leftarrow>s . x = [Tock]\<^sub>E] \<or>
              Z \<subseteq> Y \<and> length [x\<leftarrow>t . x = [Tock]\<^sub>E] = length [x\<leftarrow>s . x = [Tock]\<^sub>E]))))"
    apply (induct \<rho> s rule:ttWFw2.induct, auto simp add: empty_in_tocks)
    apply (rule_tac x="[]" in bexI, auto simp add: empty_in_tocks)
    apply (metis tt_prefix_subset.simps(1) ttobs.inject(2) dual_order.trans filter.simps(1) list.distinct(1) list.inject list.size(3) tocks.cases tocks.empty_in_tocks zero_less_Suc)
    using tocks.cases apply auto
    apply blast
    apply blast
    apply blast
    apply (rule_tac x="[Xa]\<^sub>R # [Tock]\<^sub>E # t" in bexI, auto simp add: empty_in_tocks)
    apply (metis ttobs.inject(2) list.inject list.simps(3) rev_subsetD subsetI tocks.simps)
    apply (rule_tac x="[Xa]\<^sub>R # [Tock]\<^sub>E # t" in bexI, auto simp add: empty_in_tocks)
    apply (metis ttobs.inject(2) list.inject list.simps(3) rev_subsetD subsetI tocks.simps)
    apply (rule_tac x="[Xa]\<^sub>R # [Tock]\<^sub>E # t" in bexI, auto simp add: empty_in_tocks)
    apply (metis ttobs.inject(2) list.inject list.simps(3) rev_subsetD subsetI tocks.simps)
    apply (meson ttWFw.simps(12) tt_prefix_subset_ttWFw)
    apply (meson ttWFw.simps(11) tt_prefix_subset_ttWFw)
    apply (meson ttWFw.simps(13) tt_prefix_subset_ttWFw)
    apply (meson ttWFw.simps(8) tt_prefix_subset_ttWFw)
    by (meson ttWFw.simps(6) tt_prefix_subset_ttWFw)
  then show "s \<in> tocks X \<Longrightarrow> \<rho> \<lesssim>\<^sub>C s @ [[Y]\<^sub>R] \<Longrightarrow>
    \<exists>t\<in>tocks X.
       t \<lesssim>\<^sub>C s \<and>
       (\<rho> = t \<or>
        (\<exists>Z. \<rho> = t @ [[Z]\<^sub>R] \<and>
             (Z \<subseteq> X \<and> length [x\<leftarrow>t . x = [Tock]\<^sub>E] < length [x\<leftarrow>s . x = [Tock]\<^sub>E] \<or>        
              Z \<subseteq> Y \<and> length [x\<leftarrow>t . x = [Tock]\<^sub>E] = length [x\<leftarrow>s . x = [Tock]\<^sub>E])))"
    using calculation by auto
qed

lemma tt_prefix_subset_tocks_event: "e \<noteq> Tock \<Longrightarrow> s \<in> tocks X \<Longrightarrow> t \<lesssim>\<^sub>C s @ [[e]\<^sub>E] \<Longrightarrow>
  t \<in> {t. \<exists>s'\<in>tocks X. s'\<lesssim>\<^sub>C s \<and> 
    (t = s' \<or> 
      (\<exists>Y. t = s' @ [[Y]\<^sub>R] \<and> Y \<subseteq> X \<and> length (filter (\<lambda> x. x = [Tock]\<^sub>E) s') < length (filter (\<lambda> x. x = [Tock]\<^sub>E) s)) \<or>
      (t = s' @ [[e]\<^sub>E] \<and> length (filter (\<lambda> x. x = [Tock]\<^sub>E) s') = length (filter (\<lambda> x. x = [Tock]\<^sub>E) s)))}"
proof -
  assume "e \<noteq> Tock" "s \<in> tocks X"
  then have "ttWFw (s @ [[e]\<^sub>E])"
    by (cases e, auto simp add: tocks_append_wfw)
  also have "ttWFw (s @ [[e]\<^sub>E]) \<longrightarrow> s \<in> tocks X \<longrightarrow> t \<lesssim>\<^sub>C s @ [[e]\<^sub>E] \<longrightarrow>
    t \<in> {t. \<exists>s'\<in>tocks X. s'\<lesssim>\<^sub>C s \<and> 
      (t = s' \<or> 
        (\<exists>Y. t = s' @ [[Y]\<^sub>R] \<and> Y \<subseteq> X \<and> length (filter (\<lambda> x. x = [Tock]\<^sub>E) s') < length (filter (\<lambda> x. x = [Tock]\<^sub>E) s)) \<or>
        (t = s' @ [[e]\<^sub>E] \<and> length (filter (\<lambda> x. x = [Tock]\<^sub>E) s') = length (filter (\<lambda> x. x = [Tock]\<^sub>E) s)))}"
    apply auto
    apply (induct t s rule:ttWFw2.induct, auto simp add: empty_in_tocks)
    using tocks.simps apply auto
    apply (metis tt_prefix_subset.simps(1) ttobs.inject(2) filter.simps(1) list.distinct(1) list.inject list.size(3) order_trans tocks.cases tocks.empty_in_tocks zero_less_Suc)
    using tt_prefix_subset_refl filter.simps(1) apply blast
    using tt_prefix_subset_antisym apply fastforce
    apply (case_tac "\<sigma> \<in> tocks X", auto)
    apply (rule_tac x="[Xa]\<^sub>R # [Tock]\<^sub>E # s'" in bexI, auto)
    apply (metis ttobs.inject(2) list.distinct(1) list.inject subset_iff tocks.simps)
    apply (rule_tac x="[Xa]\<^sub>R # [Tock]\<^sub>E # s'" in bexI, auto, metis ttobs.inject(2) list.distinct(1) list.inject subset_iff tocks.simps)
    apply (rule_tac x="[Xa]\<^sub>R # [Tock]\<^sub>E # s'" in bexI, auto, metis ttobs.inject(2) list.distinct(1) list.inject subset_iff tocks.simps)
    apply blast
    apply (meson ttWFw.simps(12) tt_prefix_subset_ttWFw)
    apply (meson ttWFw.simps(11) tt_prefix_subset_ttWFw)
    apply (meson ttWFw.simps(13) tt_prefix_subset_ttWFw)
    apply (meson ttWFw.simps(8) tt_prefix_subset_ttWFw)
    using ttWFw.simps(6) tt_prefix_subset_ttWFw by blast
  then show "e \<noteq> Tock \<Longrightarrow>
    s \<in> tocks X \<Longrightarrow>
    t \<lesssim>\<^sub>C s @ [[e]\<^sub>E] \<Longrightarrow>
    t \<in> {t. \<exists>s'\<in>tocks X.
                s' \<lesssim>\<^sub>C s \<and>
                (t = s' \<or>
                 (\<exists>Y. t = s' @ [[Y]\<^sub>R] \<and> Y \<subseteq> X \<and> length [x\<leftarrow>s' . x = [Tock]\<^sub>E] < length [x\<leftarrow>s . x = [Tock]\<^sub>E]) \<or>
                 t = s' @ [[e]\<^sub>E] \<and> length [x\<leftarrow>s' . x = [Tock]\<^sub>E] = length [x\<leftarrow>s . x = [Tock]\<^sub>E])}"
    using calculation by auto
qed

lemma tocks_length_eq: "s \<in> tocks X \<Longrightarrow> length s = 2 * length (filter (\<lambda> x. x = [Tock]\<^sub>E) s)"
  by (induct s rule:tocks.induct, auto)

lemma equal_Tocks_tocks_imp:
  "length [x\<leftarrow>\<rho> . x = [Tock]\<^sub>E] = length [x\<leftarrow>\<sigma> . x = [Tock]\<^sub>E] \<Longrightarrow> \<rho> \<lesssim>\<^sub>C \<sigma> \<Longrightarrow> \<sigma> \<in> tocks {x. x \<noteq> Tock} \<Longrightarrow> \<rho> \<in> tocks {x. x \<noteq> Tock}"
  apply (induct \<rho> \<sigma> rule:ttWF2.induct, auto)
  using tocks.cases apply auto
  apply (metis (no_types, lifting) ttobs.inject(2) list.inject list.simps(3) order.trans tocks.simps)
  apply (metis tocks.cases tt_prefix_subset.simps(2) tt_prefix_subset.simps(3) tt_prefix_subset.simps(6) ttevent.simps(7))
  apply (metis init_refusal_tt_prefix_subset tocks.cases tt_prefix_subset.simps(3) tt_prefix_subset.simps(6) ttevent.distinct(1))
  apply (metis (full_types) mem_Collect_eq tocks_wf ttWF.simps(13) tt_prefix_subset_ttWF)
  apply (metis tocks.simps tt_prefix_subset.simps(4) tt_prefix_subset.simps(6))
  by (metis tocks.simps tt_prefix_subset.simps(4) tt_prefix_subset.simps(6))

lemma end_refusal_notin_tocks: "\<rho> @ [[X]\<^sub>R] \<notin> tocks Y"
  using tocks.cases by (induct \<rho> rule:ttWF.induct, auto)

lemma refusal_notin_tocks: "[[X]\<^sub>R] \<notin> tocks Y"
  using tocks.cases by auto
  
lemma end_event_notin_tocks: "s @ [[Event e]\<^sub>E] \<notin> tocks X"
  using tocks.cases by (induct s rule:ttWF.induct, auto)

lemma start_event_notin_tocks: "[Event e]\<^sub>E # s \<notin> tocks X"
  using tocks.cases by (induct s rule:ttWF.induct, auto)

lemma second_event_notin_tocks: "x # [Event e]\<^sub>E # s \<notin> tocks X"
  using tocks.cases by (induct s rule:ttWF.induct, auto)

lemma mid_event_notin_tocks: "s @ [[Event e]\<^sub>E] @ t \<notin> tocks X"
  using tocks.cases by (induct s rule:ttWF.induct, auto)

lemma event_notin_tocks: "[[Event e]\<^sub>E] \<notin> tocks X"
  using tocks.cases by (auto)

lemma start_tick_notin_tocks: "[Tick]\<^sub>E # s \<notin> tocks X"
  using tocks.cases by (induct s rule:ttWF.induct, auto)

lemma second_tick_notin_tocks: "x # [Tick]\<^sub>E # s \<notin> tocks X"
  using tocks.cases by (induct s rule:ttWF.induct, auto)

lemma end_tick_notin_tocks: "s @ [[Tick]\<^sub>E] \<notin> tocks X"
  using tocks.cases by (induct s rule:ttWF.induct, auto)

lemma mid_tick_notin_tocks: "s @ [[Tick]\<^sub>E] @ t \<notin> tocks X"
  using tocks.cases by (induct s rule:ttWF.induct, auto)

lemma tick_notin_tocks: "[[Tick]\<^sub>E] \<notin> tocks X"
  using tocks.cases by (auto)

lemma double_refusal_start_notin_tocks: "[Y]\<^sub>R # [Z]\<^sub>R # s \<notin> tocks X"
  using tocks.cases by (induct s rule:ttWF.induct, auto)

lemma start_tock_notin_tocks: "[Tock]\<^sub>E # s \<notin> tocks X"
  using tocks.cases by (induct s rule:ttWF.induct, auto)

lemmas notin_tocks = 
  end_refusal_notin_tocks refusal_notin_tocks double_refusal_start_notin_tocks
  start_event_notin_tocks second_event_notin_tocks mid_event_notin_tocks end_event_notin_tocks event_notin_tocks
  start_tick_notin_tocks second_tick_notin_tocks mid_tick_notin_tocks end_tick_notin_tocks tick_notin_tocks
  start_tock_notin_tocks

lemma tocks_tt_prefix_end_event: "t \<in> tocks X \<Longrightarrow> e \<noteq> Tock \<Longrightarrow> t \<le>\<^sub>C s @ [[e]\<^sub>E] \<Longrightarrow> t \<le>\<^sub>C s"
proof -
  assume assms: "t \<in> tocks X" "e \<noteq> Tock" "t \<le>\<^sub>C s @ [[e]\<^sub>E]"
  have "t = s @ [[e]\<^sub>E] \<or> t \<le>\<^sub>C s"
    using assms(3) tt_prefix_notfront_is_whole by blast
  then show "t \<le>\<^sub>C s"
    by (auto, cases e, insert assms notin_tocks, fastforce+)
qed

lemma nontocks_append_tocks: "t\<notin>tocks X \<Longrightarrow> s\<in>tocks X \<Longrightarrow> t @ s \<notin>tocks X"
  using tocks.cases apply (induct t rule:ttWF.induct, simp_all add: tocks.intros notin_tocks)
  apply (metis double_refusal_start_notin_tocks refusal_notin_tocks tocks.cases)
  by (metis list.distinct(1) list.inject tocks.simps)

lemma equal_traces_imp_equal_tocks: "s \<in> tocks X \<Longrightarrow> s' \<in> tocks X  \<Longrightarrow> 
  s @ [[Event e]\<^sub>E] @ t = s' @ [[Event e]\<^sub>E] @ t' \<Longrightarrow> s = s' \<and> t = t'"
  apply (induct s s' rule:ttWF2.induct, auto simp add: notin_tocks)
  using tocks.cases by auto

lemma tt_subset_remove_start: "\<rho>' @ \<sigma>' \<subseteq>\<^sub>C \<rho> @ \<sigma> \<Longrightarrow> \<rho>' \<subseteq>\<^sub>C \<rho> \<Longrightarrow> \<sigma>' \<subseteq>\<^sub>C \<sigma>"
  by (induct \<rho>' \<rho> rule:tt_subset.induct, simp_all)

thm ttWFw2.induct

lemma tt_prefix_subset_lift_tocks:
  "\<rho> \<lesssim>\<^sub>C \<sigma> \<Longrightarrow> \<rho> \<in> tocks UNIV \<Longrightarrow> \<exists> \<rho>' \<in> tocks UNIV. \<rho> \<lesssim>\<^sub>C \<rho>' \<and> \<rho>' \<le>\<^sub>C \<sigma>"
  apply (induct \<rho> \<sigma> rule:ttWFw2.induct, auto simp add: notin_tocks)
  using tt_prefix.simps apply (blast, blast, blast, blast, blast)
proof -
  fix Xa \<rho> Y \<sigma>
  assume assm1: "[Xa]\<^sub>R # [Tock]\<^sub>E # \<rho> \<in> tocks UNIV"
  then have "\<rho> \<in> tocks UNIV"
    using tocks.cases by auto
  also assume "\<rho> \<in> tocks UNIV \<Longrightarrow> \<exists>\<rho>'\<in>tocks UNIV. \<rho> \<lesssim>\<^sub>C \<rho>' \<and> \<rho>' \<le>\<^sub>C \<sigma>"
  then obtain \<rho>' where \<rho>'_assms: "\<rho>'\<in>tocks UNIV" "\<rho> \<lesssim>\<^sub>C \<rho>'" "\<rho>' \<le>\<^sub>C \<sigma>"
    using calculation by blast
  assume "Xa \<subseteq> Y"
  then show "\<exists>\<rho>'\<in>tocks UNIV. [Xa]\<^sub>R # [Tock]\<^sub>E # \<rho> \<lesssim>\<^sub>C \<rho>' \<and> \<rho>' \<le>\<^sub>C [Y]\<^sub>R # [Tock]\<^sub>E # \<sigma>"
    by (rule_tac x="[Y]\<^sub>R # [Tock]\<^sub>E # \<rho>'" in bexI, simp_all add: \<rho>'_assms tocks.tock_insert_in_tocks)
next
  fix X \<rho> \<sigma>
  assume "\<rho> \<lesssim>\<^sub>C [X]\<^sub>R # [Tick]\<^sub>E # \<sigma>" "\<rho> \<in> tocks UNIV"
  then have "\<rho> = []"
    using tocks.simps by fastforce
  then show "\<exists>\<rho>'\<in>tocks UNIV. \<rho> \<lesssim>\<^sub>C \<rho>' \<and> \<rho>' \<le>\<^sub>C [X]\<^sub>R # [Tick]\<^sub>E # \<sigma>"
    using tt_prefix.simps(1) tt_prefix_subset.simps(1) tocks.empty_in_tocks by blast
next
  fix \<rho> X e \<sigma>
  assume "\<rho> \<lesssim>\<^sub>C [X]\<^sub>R # [Event e]\<^sub>E # \<sigma>" "\<rho> \<in> tocks UNIV"
  then have "\<rho> = []"
    using tocks.simps by fastforce
  then show "\<exists>\<rho>'\<in>tocks UNIV. \<rho> \<lesssim>\<^sub>C \<rho>' \<and> \<rho>' \<le>\<^sub>C [X]\<^sub>R # [Event e]\<^sub>E # \<sigma>"
    using tt_prefix.simps(1) tt_prefix_subset.simps(1) tocks.empty_in_tocks by blast
next
  fix \<rho> X Y \<sigma>
  assume "\<rho> \<lesssim>\<^sub>C [X]\<^sub>R # [Y]\<^sub>R # \<sigma>" "\<rho> \<in> tocks UNIV"
  then have "\<rho> = []"
    using tocks.simps by fastforce
  then show "\<exists>\<rho>'\<in>tocks UNIV. \<rho> \<lesssim>\<^sub>C \<rho>' \<and> \<rho>' \<le>\<^sub>C [X]\<^sub>R # [Y]\<^sub>R # \<sigma>"
    using tt_prefix.simps(1) tt_prefix_subset.simps(1) tocks.empty_in_tocks by blast
next
  fix \<rho> y \<sigma>
  assume "\<rho> \<lesssim>\<^sub>C [Tick]\<^sub>E # y # \<sigma>" "\<rho> \<in> tocks UNIV"
  then have "\<rho> = []"
    using tocks.simps by fastforce
  then show "\<exists>\<rho>'\<in>tocks UNIV. \<rho> \<lesssim>\<^sub>C \<rho>' \<and> \<rho>' \<le>\<^sub>C [Tick]\<^sub>E # y # \<sigma>"
    using tt_prefix.simps(1) tt_prefix_subset.simps(1) tocks.empty_in_tocks by blast
next
  fix \<rho> \<sigma>
  assume "\<rho> \<lesssim>\<^sub>C [Tock]\<^sub>E # \<sigma>" "\<rho> \<in> tocks UNIV"
  then have "\<rho> = []"
    using tocks.simps by fastforce
  then show "\<exists>\<rho>'\<in>tocks UNIV. \<rho> \<lesssim>\<^sub>C \<rho>' \<and> \<rho>' \<le>\<^sub>C [Tock]\<^sub>E # \<sigma>"
    using tt_prefix.simps(1) tt_prefix_subset.simps(1) tocks.empty_in_tocks by blast
qed

lemma longest_pretocks_tt_prefix_subset:
  assumes "\<rho>' @ \<sigma>' \<lesssim>\<^sub>C \<rho> @ \<sigma>"
  assumes "\<rho> \<in> tocks UNIV" "\<forall>t\<in>tocks UNIV. t \<le>\<^sub>C \<rho> @ \<sigma> \<longrightarrow> t \<le>\<^sub>C \<rho>"
  assumes "\<rho>' \<in> tocks UNIV" "\<forall>t\<in>tocks UNIV. t \<le>\<^sub>C \<rho>' @ \<sigma>' \<longrightarrow> t \<le>\<^sub>C \<rho>'"
  shows "\<rho>' \<lesssim>\<^sub>C \<rho>"
proof (insert assms, induct "\<rho>'" "\<rho>" rule:ttWF2.induct, simp_all)
  fix X
  assume "\<forall>t\<in>tocks UNIV. t \<le>\<^sub>C \<sigma> \<longrightarrow> t \<le>\<^sub>C []" "[[X]\<^sub>R] \<in> tocks UNIV"
  then show "False"
    using tocks.cases by auto
next
  assume "\<forall>t\<in>tocks UNIV. t \<le>\<^sub>C \<sigma> \<longrightarrow> t \<le>\<^sub>C []" "[[Tick]\<^sub>E] \<in> tocks UNIV"
  then show "False"
    using tocks.cases by auto
next
  fix e \<sigma>''
  assume "\<forall>t\<in>tocks UNIV. t \<le>\<^sub>C \<sigma> \<longrightarrow> t \<le>\<^sub>C []" "[Event e]\<^sub>E # \<sigma>'' \<in> tocks UNIV"
  then show "False"
    using tocks.cases by auto
next
  fix e \<rho> f \<sigma>''
  assume "[Event f]\<^sub>E # \<sigma>'' \<in> tocks UNIV"
  then have "False"
    using tocks.cases by auto
  then show "\<rho> \<lesssim>\<^sub>C \<sigma>''"
    by simp
next
  fix X 
  fix \<sigma>'' :: "'a ttobs list"
  assume assm1: "[X]\<^sub>R # [Tock]\<^sub>E # \<sigma>'' \<in> tocks UNIV"
  assume assm2: "[X]\<^sub>R # [Tock]\<^sub>E # \<sigma>'' @ \<sigma>' \<lesssim>\<^sub>C \<sigma>"
  assume assm3: "\<forall>t\<in>tocks UNIV. t \<le>\<^sub>C \<sigma> \<longrightarrow> t \<le>\<^sub>C []"
  have assm2': "[X]\<^sub>R # [Tock]\<^sub>E # \<sigma>'' \<lesssim>\<^sub>C \<sigma>"
    using assm2 tt_prefix_subset_front by force
  then obtain \<rho>'' where \<rho>''_assms: "\<rho>'' \<le>\<^sub>C \<sigma>" "[X]\<^sub>R # [Tock]\<^sub>E # \<sigma>'' \<lesssim>\<^sub>C \<rho>''"
    using tt_prefix_subset_lift by blast
  then have "[[X]\<^sub>R, [Tock]\<^sub>E] \<lesssim>\<^sub>C \<rho>''"
    by (meson tt_prefix.simps(1) tt_prefix.simps(2) tt_prefix_tt_prefix_subset_trans)
  then obtain Y \<rho>''' where "\<rho>'' = [Y]\<^sub>R # [Tock]\<^sub>E # \<rho>'''"
    by (cases \<rho>'' rule:ttWF.cases, auto)
  then have "[Y]\<^sub>R # [Tock]\<^sub>E # \<rho>''' \<le>\<^sub>C []"
    using assm2' assm1 assm3 tt_prefix_subset.simps(6) tt_prefix_subset_tt_prefix_trans tt_prefix_subset_lift_tocks by blast
  then show "False"
    by simp
next
  fix Y
  assume "[[Y]\<^sub>R] \<in> tocks UNIV"
  then show "False"
    using tocks.cases by auto
next
  fix X :: "'a ttevent set"
  fix \<rho> Y \<sigma>''
  assume assm1: "(\<sigma>'' \<in> tocks UNIV \<Longrightarrow>
        \<forall>t\<in>tocks UNIV. t \<le>\<^sub>C \<sigma>'' @ \<sigma> \<longrightarrow> t \<le>\<^sub>C \<sigma>'' \<Longrightarrow>
        \<rho> \<in> tocks UNIV \<Longrightarrow> \<forall>t\<in>tocks UNIV. t \<le>\<^sub>C \<rho> @ \<sigma>' \<longrightarrow> t \<le>\<^sub>C \<rho> \<Longrightarrow> \<rho> \<lesssim>\<^sub>C \<sigma>'')"
  assume assm2: "X \<subseteq> Y \<and> \<rho> @ \<sigma>' \<lesssim>\<^sub>C \<sigma>'' @ \<sigma>"
  assume assm3: "[Y]\<^sub>R # [Tock]\<^sub>E # \<sigma>'' \<in> tocks UNIV"
  assume assm4: "\<forall>t\<in>tocks UNIV. t \<le>\<^sub>C [Y]\<^sub>R # [Tock]\<^sub>E # \<sigma>'' @ \<sigma> \<longrightarrow> t \<le>\<^sub>C [Y]\<^sub>R # [Tock]\<^sub>E # \<sigma>''"
  assume assm5: "[X]\<^sub>R # [Tock]\<^sub>E # \<rho> \<in> tocks UNIV"
  assume assm6: "\<forall>t\<in>tocks UNIV. t \<le>\<^sub>C [X]\<^sub>R # [Tock]\<^sub>E # \<rho> @ \<sigma>' \<longrightarrow> t \<le>\<^sub>C [X]\<^sub>R # [Tock]\<^sub>E # \<rho>"
  have 1: "\<sigma>'' \<in> tocks UNIV"
    using assm3 tocks.simps by auto
  have 2: "\<rho> \<in> tocks UNIV"
    using assm5 tocks.simps by auto
  have 3: "\<forall>t\<in>tocks UNIV. t \<le>\<^sub>C \<sigma>'' @ \<sigma> \<longrightarrow> t \<le>\<^sub>C \<sigma>''"
    using assm4 by (auto, erule_tac x="[Y]\<^sub>R # [Tock]\<^sub>E # t" in ballE, simp_all add: tocks.tock_insert_in_tocks)
  have 4: "\<forall>t\<in>tocks UNIV. t \<le>\<^sub>C \<rho> @ \<sigma>' \<longrightarrow> t \<le>\<^sub>C \<rho>"
    using assm6 by (auto, erule_tac x="[X]\<^sub>R # [Tock]\<^sub>E # t" in ballE, simp_all add: tocks.tock_insert_in_tocks)
  then show "\<rho> \<lesssim>\<^sub>C \<sigma>''"
    using 1 2 3 4 assm1 by auto
next
  fix X \<rho> \<sigma>''
  assume "[X]\<^sub>R # [Tick]\<^sub>E # \<rho> \<in> tocks UNIV"
  then have "False"
    using ttWFw.simps(12) tocks_wfw by blast
  then show "[X]\<^sub>R # [Tick]\<^sub>E # \<rho> \<lesssim>\<^sub>C \<sigma>''"
    by auto
next
  fix X e \<rho> \<sigma>''
  assume "[X]\<^sub>R # [Event e]\<^sub>E # \<rho> \<in> tocks UNIV"
  then have "False"
    by (meson ttWFw.simps(11) tocks_wfw)
  then show "[X]\<^sub>R # [Event e]\<^sub>E # \<rho> \<lesssim>\<^sub>C \<sigma>''"
    by auto
next
  fix X Y \<rho> \<sigma>''
  assume "[X]\<^sub>R # [Y]\<^sub>R # \<rho> \<in> tocks UNIV"
  then have "False"
    using ttWFw.simps(13) tocks_wfw by blast
  then show "[X]\<^sub>R # [Y]\<^sub>R # \<rho> \<lesssim>\<^sub>C \<sigma>''"
    by auto
next
  fix X \<rho> \<sigma>''
  assume "[X]\<^sub>R # [Tick]\<^sub>E # \<sigma>'' \<in> tocks UNIV"
  then have "False"
    using ttWFw.simps(12) tocks_wfw by blast
  then show "\<rho> \<lesssim>\<^sub>C [X]\<^sub>R # [Tick]\<^sub>E # \<sigma>''"
    by auto
next
  fix X e \<rho> \<sigma>''
  assume "[X]\<^sub>R # [Event e]\<^sub>E # \<sigma>'' \<in> tocks UNIV"
  then have "False"
    by (meson ttWFw.simps(11) tocks_wfw)
  then show "\<rho> \<lesssim>\<^sub>C [X]\<^sub>R # [Event e]\<^sub>E # \<sigma>''"
    by auto
next
  fix X Y \<rho> \<sigma>''
  assume "[X]\<^sub>R # [Y]\<^sub>R # \<sigma>'' \<in> tocks UNIV"
  then have "False"
    using ttWFw.simps(13) tocks_wfw by blast
  then show "\<rho> \<lesssim>\<^sub>C [X]\<^sub>R # [Y]\<^sub>R # \<sigma>''"
    by auto
next
  fix x \<rho> \<sigma>''
  assume "[Tick]\<^sub>E # x # \<rho> \<in> tocks UNIV"
  then have "False"
    using ttWFw.simps(10) tocks_wfw by blast
  then show "[Tick]\<^sub>E # x # \<rho> \<lesssim>\<^sub>C \<sigma>''"
    by auto
next
  fix y \<rho> \<sigma>''
  assume "[Tick]\<^sub>E # y # \<sigma>'' \<in> tocks UNIV"
  then have "False"
    using ttWFw.simps(10) tocks_wfw by blast
  then show "\<rho> \<lesssim>\<^sub>C [Tick]\<^sub>E # y # \<sigma>''"
    by auto
next
  fix \<rho> \<sigma>''
  assume "[Tock]\<^sub>E # \<rho> \<in> tocks UNIV"
  then have "False"
    using ttWFw.simps(6) tocks_wfw by blast
  then show "[Tock]\<^sub>E # \<rho> \<lesssim>\<^sub>C \<sigma>''"
    by auto
next
  fix \<rho> \<sigma>''
  assume "[Tock]\<^sub>E # \<sigma>'' \<in> tocks UNIV"
  then have "False"
    using ttWFw.simps(6) tocks_wfw by blast
  then show "\<rho> \<lesssim>\<^sub>C [Tock]\<^sub>E # \<sigma>''"
    by auto
qed

lemma longest_pretocks_tt_prefix_subset_split:
  assumes "\<rho> \<in> tocks UNIV" "\<forall>t\<in>tocks UNIV. t \<le>\<^sub>C \<rho> @ \<sigma> \<longrightarrow> t \<le>\<^sub>C \<rho>"
  shows "\<exists>\<rho>' \<sigma>'. \<rho>' \<in> tocks UNIV \<and> 
    (\<forall>t\<in>tocks UNIV. t \<le>\<^sub>C \<rho>' @ \<sigma>' \<longrightarrow> t \<le>\<^sub>C \<rho>') \<and> 
    \<rho>' @ \<sigma>' \<lesssim>\<^sub>C \<rho> @ \<sigma> \<and> 
    (\<sigma>' \<lesssim>\<^sub>C \<sigma> \<or> (\<exists> X. \<sigma>' \<lesssim>\<^sub>C [X]\<^sub>R # \<sigma>))"
proof (insert assms, simp_all)
  thm tt_prefix_subset_tocks
  obtain \<rho>' where \<rho>'_assms: "\<rho>' \<in> tocks UNIV" "(\<rho>' \<lesssim>\<^sub>C \<rho>) \<or> (\<exists>Y. \<rho>' @ [[Y]\<^sub>R] \<lesssim>\<^sub>C \<rho>)"
    using assms(1) tt_prefix_subset_refl by blast
  obtain \<sigma>' where \<sigma>'_assms: "\<sigma>' \<lesssim>\<^sub>C \<sigma>"
    using tt_prefix_subset.simps(1) by blast
  from \<rho>'_assms \<sigma>'_assms show "\<exists>\<rho>'. \<rho>' \<in> tocks UNIV \<and>
         (\<exists>\<sigma>'. (\<forall>t\<in>tocks UNIV. t \<le>\<^sub>C \<rho>' @ \<sigma>' \<longrightarrow> t \<le>\<^sub>C \<rho>') \<and> \<rho>' @ \<sigma>' \<lesssim>\<^sub>C \<rho> @ \<sigma> \<and> (\<sigma>' \<lesssim>\<^sub>C \<sigma> \<or> (\<exists>X. \<sigma>' \<lesssim>\<^sub>C [X]\<^sub>R # \<sigma>)))"
  proof (auto)
    assume assm1: "\<rho>' \<in> tocks UNIV"
    assume assm2: "\<sigma>' \<lesssim>\<^sub>C \<sigma>"
    assume assm2: "\<rho>' \<lesssim>\<^sub>C \<rho>"
    show "\<exists>\<rho>'. \<rho>' \<in> tocks UNIV \<and>
         (\<exists>\<sigma>'. (\<forall>t\<in>tocks UNIV. t \<le>\<^sub>C \<rho>' @ \<sigma>' \<longrightarrow> t \<le>\<^sub>C \<rho>') \<and> \<rho>' @ \<sigma>' \<lesssim>\<^sub>C \<rho> @ \<sigma> \<and> (\<sigma>' \<lesssim>\<^sub>C \<sigma> \<or> (\<exists>X. \<sigma>' \<lesssim>\<^sub>C [X]\<^sub>R # \<sigma>)))"
      apply (rule_tac x="\<rho>'" in exI, simp add: assm1)
      apply (rule_tac x="[]" in exI, auto)
      using assm2 tt_prefix_concat tt_prefix_subset_tt_prefix_trans by blast
  next
    fix Y
    assume assm1: "\<rho>' \<in> tocks UNIV"
    assume assm2: "\<sigma>' \<lesssim>\<^sub>C \<sigma>"
    assume assm3: "\<rho>' @ [[Y]\<^sub>R] \<lesssim>\<^sub>C \<rho>"
    show "\<exists>\<rho>'. \<rho>' \<in> tocks UNIV \<and>
         (\<exists>\<sigma>'. (\<forall>t\<in>tocks UNIV. t \<le>\<^sub>C \<rho>' @ \<sigma>' \<longrightarrow> t \<le>\<^sub>C \<rho>') \<and> \<rho>' @ \<sigma>' \<lesssim>\<^sub>C \<rho> @ \<sigma> \<and> (\<sigma>' \<lesssim>\<^sub>C \<sigma> \<or> (\<exists>X. \<sigma>' \<lesssim>\<^sub>C [X]\<^sub>R # \<sigma>)))"
      apply (rule_tac x="\<rho>'" in exI, simp add: assm1)
      apply (rule_tac x="[[Y]\<^sub>R]" in exI, auto)
      apply (metis butlast_append butlast_snoc tt_prefix_concat tt_prefix_decompose end_refusal_notin_tocks)
      using assm3 tt_prefix_concat tt_prefix_subset_tt_prefix_trans by blast
  qed
qed

lemma tocks_tt_subset_exists:
  "ttWF (\<rho> @ \<sigma>) \<Longrightarrow> ttWF \<sigma>' \<Longrightarrow> \<rho> \<in> tocks X \<and> \<sigma>' \<subseteq>\<^sub>C \<rho> @ \<sigma> \<Longrightarrow> \<exists> \<rho>' \<in> tocks X. \<rho>' \<subseteq>\<^sub>C \<rho> \<and> \<rho>' \<le>\<^sub>C \<sigma>'"
  apply (induct \<sigma>' \<rho> rule:ttWF2.induct)
  using tocks.cases
proof auto
  show "[] \<in> tocks X \<Longrightarrow> \<exists>\<rho>'\<in>tocks X. \<rho>' \<subseteq>\<^sub>C [] \<and> \<rho>' \<le>\<^sub>C []"
    by (rule_tac x="[]" in bexI, auto)
next
  fix Xa
  show "[] \<in> tocks X \<Longrightarrow> \<exists>\<rho>'\<in>tocks X. \<rho>' \<subseteq>\<^sub>C [] \<and> \<rho>' \<le>\<^sub>C [[Xa]\<^sub>R]"
    by (rule_tac x="[]" in bexI, auto)
next
  show "[] \<in> tocks X \<Longrightarrow> \<exists>\<rho>'\<in>tocks X. \<rho>' \<subseteq>\<^sub>C [] \<and> \<rho>' \<le>\<^sub>C [[Tick]\<^sub>E]"
    by (rule_tac x="[]" in bexI, auto)
next
  fix e \<sigma>'
  show "[] \<in> tocks X \<Longrightarrow> \<exists>\<rho>'\<in>tocks X. \<rho>' \<subseteq>\<^sub>C [] \<and> \<rho>' \<le>\<^sub>C [Event e]\<^sub>E # \<sigma>'"
    by (rule_tac x="[]" in bexI, auto)
next
  fix Xa \<sigma>'
  show "[] \<in> tocks X \<Longrightarrow> \<exists>\<rho>'\<in>tocks X. \<rho>' \<subseteq>\<^sub>C [] \<and> \<rho>' \<le>\<^sub>C [Xa]\<^sub>R # [Tock]\<^sub>E # \<sigma>'"
    by (rule_tac x="[]" in bexI, auto)
next
  fix Xa \<rho> Y \<sigma>'
  assume "[Y]\<^sub>R # [Tock]\<^sub>E # \<sigma>' \<in> tocks X"
  then have "\<sigma>' \<in> tocks X \<and> Y \<subseteq> X"
    using tocks.cases by blast
  also assume "\<sigma>' \<in> tocks X \<Longrightarrow> \<exists>\<rho>'\<in>tocks X. \<rho>' \<subseteq>\<^sub>C \<sigma>' \<and> \<rho>' \<le>\<^sub>C \<rho>"
  then obtain \<rho>' where "\<rho>'\<in>tocks X \<and> \<rho>' \<subseteq>\<^sub>C \<sigma>' \<and> \<rho>' \<le>\<^sub>C \<rho>"
    using calculation by blast
  then show "Xa \<subseteq> Y \<Longrightarrow> \<exists>\<rho>'\<in>tocks X. \<rho>' \<subseteq>\<^sub>C [Y]\<^sub>R # [Tock]\<^sub>E # \<sigma>' \<and> \<rho>' \<le>\<^sub>C [Xa]\<^sub>R # [Tock]\<^sub>E # \<rho>"
    by (rule_tac x="[Xa]\<^sub>R # [Tock]\<^sub>E # \<rho>'" in bexI, auto, meson calculation subset_eq tocks.tock_insert_in_tocks)
qed

lemma tocks_tt_subset_exists2:
  "ttWF (\<rho>' @ \<sigma>') \<Longrightarrow> ttWF \<sigma> \<Longrightarrow> \<rho>' \<in> tocks X \<and> \<rho>' @ \<sigma>' \<subseteq>\<^sub>C \<sigma> \<Longrightarrow> \<exists> \<rho> \<in> tocks UNIV. \<rho>' \<subseteq>\<^sub>C \<rho> \<and> \<rho> \<le>\<^sub>C \<sigma>"
  apply (induct \<rho>' \<sigma> rule:ttWF2.induct)
  using tocks.cases
proof auto
  show "[] \<in> tocks X \<Longrightarrow> \<exists>\<rho>\<in>tocks UNIV. [] \<subseteq>\<^sub>C \<rho> \<and> \<rho> \<le>\<^sub>C []"
    by (rule_tac x="[]" in bexI, auto simp add: empty_in_tocks)
next
  fix Y
  show "[] \<in> tocks X \<Longrightarrow> \<exists>\<rho>\<in>tocks UNIV. [] \<subseteq>\<^sub>C \<rho> \<and> \<rho> \<le>\<^sub>C [[Y]\<^sub>R]"
    by (rule_tac x="[]" in bexI, auto simp add: empty_in_tocks)
next
  show "[] \<in> tocks X \<Longrightarrow> \<exists>\<rho>\<in>tocks UNIV. [] \<subseteq>\<^sub>C \<rho> \<and> \<rho> \<le>\<^sub>C [[Tick]\<^sub>E]"  
    by (rule_tac x="[]" in bexI, auto simp add: empty_in_tocks)
next
  fix f \<sigma>
  show "[] \<in> tocks X \<Longrightarrow> \<exists>\<rho>\<in>tocks UNIV. [] \<subseteq>\<^sub>C \<rho> \<and> \<rho> \<le>\<^sub>C [Event f]\<^sub>E # \<sigma>"
    by (rule_tac x="[]" in bexI, auto simp add: empty_in_tocks)
next
  fix Y \<sigma>
  show "[] \<in> tocks X \<Longrightarrow> \<exists>\<rho>\<in>tocks UNIV. [] \<subseteq>\<^sub>C \<rho> \<and> \<rho> \<le>\<^sub>C [Y]\<^sub>R # [Tock]\<^sub>E # \<sigma>"
    by (rule_tac x="[]" in bexI, auto simp add: empty_in_tocks)
next
  fix Xa \<rho> Y \<sigma>
  assume "[Xa]\<^sub>R # [Tock]\<^sub>E # \<rho> \<in> tocks X"
  then have "\<rho> \<in> tocks X"
    using tocks.cases by blast
  also assume "\<rho> \<in> tocks X \<Longrightarrow> \<exists>\<rho>'\<in>tocks UNIV. \<rho> \<subseteq>\<^sub>C \<rho>' \<and> \<rho>' \<le>\<^sub>C \<sigma>"
  then obtain \<rho>' where "\<rho>'\<in>tocks UNIV \<and> \<rho> \<subseteq>\<^sub>C \<rho>' \<and> \<rho>' \<le>\<^sub>C \<sigma>"
    using calculation by blast
  then show "Xa \<subseteq> Y \<Longrightarrow> \<exists>\<rho>'\<in>tocks UNIV. [Xa]\<^sub>R # [Tock]\<^sub>E # \<rho> \<subseteq>\<^sub>C \<rho>' \<and> \<rho>' \<le>\<^sub>C [Y]\<^sub>R # [Tock]\<^sub>E # \<sigma>"
    by (rule_tac x="[Y]\<^sub>R # [Tock]\<^sub>E # \<rho>'" in bexI, auto simp add: tocks.tock_insert_in_tocks)
qed

lemma tt_subset_longest_tocks:
  assumes "ttWF (\<rho>' @ \<sigma>')" "ttWF (\<rho> @ \<sigma>)"
  assumes "\<rho> \<in> tocks X" "\<forall> t\<in>tocks UNIV. t \<le>\<^sub>C \<rho> @ \<sigma> \<longrightarrow> t \<le>\<^sub>C \<rho>"
  assumes "\<rho>' \<in> tocks X" "\<forall> t\<in>tocks UNIV. t \<le>\<^sub>C \<rho>' @ \<sigma>' \<longrightarrow> t \<le>\<^sub>C \<rho>'"
  assumes "\<rho>' @ \<sigma>' \<subseteq>\<^sub>C \<rho> @ \<sigma>"  
  shows "\<rho>' \<subseteq>\<^sub>C \<rho> \<and> \<sigma>' \<subseteq>\<^sub>C \<sigma>"
proof -
  obtain \<rho>'' where \<rho>''_assms: "\<rho>''\<in> tocks X \<and> \<rho>'' \<subseteq>\<^sub>C \<rho> \<and> \<rho>'' \<le>\<^sub>C \<rho>' @ \<sigma>'"
    using assms(1) assms(2) assms(3) assms(7) tocks_tt_subset_exists by blast
  then have 1: "\<rho>'' \<le>\<^sub>C \<rho>'"
    by (meson assms(6) subset_UNIV tocks_subset)
  obtain \<rho>''' where \<rho>'''_assms: "\<rho>''' \<in> tocks UNIV \<and> \<rho>' \<subseteq>\<^sub>C \<rho>''' \<and> \<rho>''' \<le>\<^sub>C \<rho> @ \<sigma>"
    using assms(1) assms(2) assms(5) assms(7) tocks_tt_subset_exists2 by blast
  then have 2: "\<rho>''' \<le>\<^sub>C \<rho>"
    by (meson assms(4) subset_UNIV tocks_subset)
  have 3: "length \<rho>' = length \<rho>'''"
    using \<rho>'''_assms tt_subset_same_length by blast
  have 4: "length \<rho> = length \<rho>''"
    using \<rho>''_assms tt_subset_same_length by fastforce
  have 5: "length \<rho> \<le> length \<rho>'"
    by (simp add: "1" "4" tt_prefix_imp_prefix_subset tt_prefix_subset_length)
  have 6: "length \<rho>' \<le> length \<rho>"
    by (simp add: "2" "3" tt_prefix_imp_prefix_subset tt_prefix_subset_length)
  have "length \<rho>' = length \<rho>"
    using 5 6 by auto
  then have "\<rho>' \<subseteq>\<^sub>C \<rho>"
    using assms(3) assms(5) assms(7) apply (induct \<rho>' \<rho> rule:ttWF2.induct)
    using tocks.cases by (auto simp add: notin_tocks)
  then show "\<rho>' \<subseteq>\<^sub>C \<rho> \<and> \<sigma>' \<subseteq>\<^sub>C \<sigma>"
    using assms(7) tt_subset_remove_start by auto
qed

lemma tt_subset_in_tocks:
  "t \<in> tocks X \<Longrightarrow> t' \<subseteq>\<^sub>C t \<Longrightarrow> t' \<in> tocks X"
proof (induct t' t rule:ttWF2.induct, auto simp add: notin_tocks)
  fix Xa \<rho> Y \<sigma>
  assume assms: "[Y]\<^sub>R # [Tock]\<^sub>E # \<sigma> \<in> tocks X" "Xa \<subseteq> Y" "\<sigma> \<in> tocks X \<Longrightarrow> \<rho> \<in> tocks X"
  then have "\<sigma> \<in> tocks X \<and> Y \<subseteq> X"
    by (metis ttobs.inject(2) list.inject list.simps(3) tocks.simps)
  then have "\<rho> \<in> tocks X \<and> Xa \<subseteq> X"
    using assms(2) assms(3) by blast
  then show "[Xa]\<^sub>R # [Tock]\<^sub>E # \<rho> \<in> tocks X"
    using tocks.tock_insert_in_tocks by blast
next
  fix Xa \<rho> \<sigma>
  assume assms: "\<sigma> \<in> tocks X" "[Xa]\<^sub>R # [Tick]\<^sub>E # \<rho> \<subseteq>\<^sub>C \<sigma>"
  then obtain \<sigma>' Y where "\<sigma> = [Y]\<^sub>R # [Tick]\<^sub>E # \<sigma>'"
    using ttWFw.simps(12) tt_prefix_subset_ttWFw tt_subset_imp_prefix_subset tocks_wfw by blast
  then show False
    using assms(1) second_tick_notin_tocks by blast
next
  fix Xa e \<rho> \<sigma>
  assume assms: "\<sigma> \<in> tocks X" "[Xa]\<^sub>R # [Event e]\<^sub>E # \<rho> \<subseteq>\<^sub>C \<sigma>"
  then obtain \<sigma>' Y where "\<sigma> = [Y]\<^sub>R # [Event e]\<^sub>E # \<sigma>'"
    by (meson ttWFw.simps(11) tt_prefix_subset_ttWFw tt_subset_imp_prefix_subset tocks_wfw)
  then show False
    using assms(1) second_event_notin_tocks by force
next
  fix Xa Y \<rho> \<sigma>
  assume assms: "\<sigma> \<in> tocks X" "[Xa]\<^sub>R # [Y]\<^sub>R # \<rho> \<subseteq>\<^sub>C \<sigma>"
  then obtain \<sigma>' Z W where "\<sigma> = [Z]\<^sub>R # [W]\<^sub>R # \<sigma>'"
    using ttWFw.simps(13) tt_prefix_subset_ttWFw tt_subset_imp_prefix_subset tocks_wfw by blast
  then show False
    using assms(1) double_refusal_start_notin_tocks by blast
next
  fix x \<rho> \<sigma>
  assume assms: "\<sigma> \<in> tocks X" "[Tick]\<^sub>E # x # \<rho> \<subseteq>\<^sub>C \<sigma>"
  then obtain \<sigma>' where "\<sigma> = [Tick]\<^sub>E # x # \<sigma>'"
    using ttWFw.simps(8) tt_prefix_subset_ttWFw tt_subset_imp_prefix_subset tocks_wfw by blast
  then show False
    using assms(1) start_tick_notin_tocks by blast
next
  fix \<rho> \<sigma>
  assume assms: "\<sigma> \<in> tocks X" "[Tock]\<^sub>E # \<rho> \<subseteq>\<^sub>C \<sigma>"
  then obtain \<sigma>' where "\<sigma> = [Tock]\<^sub>E # \<sigma>'"
    by (metis tt_subset.simps(5) tt_subset.simps(6) tocks.simps)
  then show False
    using assms(1) start_tock_notin_tocks by blast
qed

lemma tt_subset_in_tocks2:
  "t \<in> tocks X \<Longrightarrow> t \<subseteq>\<^sub>C t' \<Longrightarrow> t' \<in> tocks UNIV"
proof (induct t t' rule:ttWF2.induct, auto simp add: notin_tocks)
  fix Xa \<rho> Y \<sigma>
  assume assms: "[Xa]\<^sub>R # [Tock]\<^sub>E # \<rho> \<in> tocks X" "\<rho> \<in> tocks X \<Longrightarrow> \<sigma> \<in> tocks UNIV"
  then have "\<rho> \<in> tocks X"
    by (metis list.inject list.simps(3) tocks.simps)
  then have "\<sigma> \<in> tocks UNIV"
    using assms(2) by blast
  then show "[Y]\<^sub>R # [Tock]\<^sub>E # \<sigma> \<in> tocks UNIV"
    using tocks.tock_insert_in_tocks by blast
next
  show "[] \<in> tocks UNIV"
    by (simp add: tocks.empty_in_tocks)
next
  fix Xa e \<rho> \<sigma>
  assume assms: "\<rho> \<in> tocks X" "\<rho> \<subseteq>\<^sub>C [Xa]\<^sub>R # [Event e]\<^sub>E # \<sigma>"
  then obtain \<rho>' Y where "\<rho> = [Y]\<^sub>R # [Event e]\<^sub>E # \<rho>'"
    by (induct \<rho> rule:ttWF.induct, auto)
  then show False
    using assms(1) second_event_notin_tocks by force
next
  fix Xa Y \<rho> \<sigma>
  assume assms: "\<rho> \<in> tocks X" "\<rho> \<subseteq>\<^sub>C [Xa]\<^sub>R # [Y]\<^sub>R # \<sigma>"
  then obtain \<rho>' Z W where "\<rho> = [Z]\<^sub>R # [W]\<^sub>R # \<rho>'"
    by (induct \<rho> rule:ttWF.induct, auto)
  then show False
    using assms(1) double_refusal_start_notin_tocks by blast
next
  fix x \<rho> \<sigma>
  assume assms: "\<rho> \<in> tocks X" "\<rho> \<subseteq>\<^sub>C [Tick]\<^sub>E # x # \<sigma>"
  then obtain \<rho>' where "\<rho> = [Tick]\<^sub>E # \<rho>'"
    by (induct \<rho> rule:ttWF.induct, auto)
  then show False
    using assms(1) start_tick_notin_tocks by blast
next
  fix \<rho> \<sigma>
  assume assms: "\<rho> \<in> tocks X" "\<rho> \<subseteq>\<^sub>C [Tock]\<^sub>E # \<sigma>"
  then obtain \<rho>' where "\<rho> = [Tock]\<^sub>E # \<rho>'"
    by (induct \<rho> rule:ttWF.induct, auto)
  then show False
    using assms(1) start_tock_notin_tocks by blast
next
  fix \<rho> Xa \<sigma>
  assume assms: "\<rho> \<in> tocks X" "\<rho> \<subseteq>\<^sub>C [Xa]\<^sub>R # [Tick]\<^sub>E # \<sigma>"
  then obtain \<rho>' Y where "\<rho> = [Y]\<^sub>R # [Tick]\<^sub>E # \<rho>'"
    by (induct \<rho> rule:ttWF.induct, auto)
  then show False
    using assms(1) second_tick_notin_tocks by auto
qed

lemma tt_subset_longest_tocks2:
  "\<forall> t\<in>tocks UNIV. t \<le>\<^sub>C s1 @ s2  \<longrightarrow> t \<le>\<^sub>C s1 \<Longrightarrow> s2' \<subseteq>\<^sub>C s2 \<Longrightarrow> \<forall> t\<in>tocks UNIV. t \<le>\<^sub>C s1 @ s2' \<longrightarrow> t \<le>\<^sub>C s1"
proof auto
  fix t
  assume assms: "\<forall>t\<in>tocks UNIV. t \<le>\<^sub>C s1 @ s2 \<longrightarrow> t \<le>\<^sub>C s1" "s2' \<subseteq>\<^sub>C s2" "t \<in> tocks UNIV" "t \<le>\<^sub>C s1 @ s2'"
  then obtain t' where t'_assms: "t \<subseteq>\<^sub>C t' \<and> t' \<le>\<^sub>C s1 @ s2"
    by (meson tt_prefix_tt_prefix_subset_trans tt_prefix_subset_imp_tt_subset_tt_prefix tt_subset_combine tt_subset_imp_prefix_subset tt_subset_refl)
  then have "t' \<in> tocks UNIV"
    using assms(3) tt_subset_in_tocks2 by blast
  then have "t' \<le>\<^sub>C s1"
    by (simp add: assms(1) t'_assms)
  then show "t \<le>\<^sub>C s1"
    by (metis assms(4) tt_prefix_append_split tt_prefix_concat tt_prefix_imp_prefix_subset tt_prefix_subset_antisym tt_prefix_subset_tt_prefix_trans tt_subset_imp_prefix_subset t'_assms)
qed

lemma tt_subset_longest_tocks3:
  "\<forall> t\<in>tocks UNIV. t \<le>\<^sub>C s1 @ s2  \<longrightarrow> t \<le>\<^sub>C s1 \<Longrightarrow> s2 \<subseteq>\<^sub>C s2' \<Longrightarrow> \<forall> t\<in>tocks UNIV. t \<le>\<^sub>C s1 @ s2' \<longrightarrow> t \<le>\<^sub>C s1"
proof auto
  fix t
  assume assms: "\<forall>t\<in>tocks UNIV. t \<le>\<^sub>C s1 @ s2 \<longrightarrow> t \<le>\<^sub>C s1" "s2 \<subseteq>\<^sub>C s2'" "t \<in> tocks UNIV" "t \<le>\<^sub>C s1 @ s2'"
  then obtain t' where t'_assms: "t' \<subseteq>\<^sub>C t \<and> t' \<le>\<^sub>C s1 @ s2"
    by (meson tt_prefix_tt_subset tt_subset_combine tt_subset_refl)
  then have "t' \<in> tocks UNIV"
    using assms(3) tt_subset_in_tocks by blast
  then have "t' \<le>\<^sub>C s1"
    by (simp add: assms(1) t'_assms)
  then show "t \<le>\<^sub>C s1"
    by (smt append_assoc append_eq_append_conv assms(4) tt_prefix_split tt_subset_same_length t'_assms)
qed

lemma tt_subset_longest_tocks4:
  "\<And> s1'. \<forall> t\<in>tocks UNIV. t \<le>\<^sub>C s1 @ s2  \<longrightarrow> t \<le>\<^sub>C s1 \<Longrightarrow> s1 \<subseteq>\<^sub>C s1' \<Longrightarrow> \<forall> t\<in>tocks UNIV. t \<le>\<^sub>C s1' @ s2 \<longrightarrow> t \<le>\<^sub>C s1'"
proof (safe, induct s1 rule:ttWF.induct)
  fix t s1'
  assume assms: "\<forall>t\<in>tocks UNIV. t \<le>\<^sub>C [] @ s2 \<longrightarrow> t \<le>\<^sub>C []" "[] \<subseteq>\<^sub>C s1'" "t \<in> tocks UNIV" "t \<le>\<^sub>C s1' @ s2"
  then have "s1' = []"
    using tt_subset_same_length by force
  then show "t \<le>\<^sub>C s1'"
    using assms(1) assms(3) assms(4) by auto
next
  fix X s1' t
  assume assms: "\<forall>t\<in>tocks UNIV. t \<le>\<^sub>C [[X]\<^sub>R] @ s2 \<longrightarrow> t \<le>\<^sub>C [[X]\<^sub>R]" "[[X]\<^sub>R] \<subseteq>\<^sub>C s1'" "t \<in> tocks UNIV" "t \<le>\<^sub>C s1' @ s2"
  then obtain Y where s1'_def: "s1' = [[Y]\<^sub>R]"
    by (cases s1' rule:ttWF.cases, auto)
  then have "t = [] \<or> (\<exists> ta. t = [Y]\<^sub>R # ta)"
    using assms(4) tt_prefix.elims(2) by auto
  then show "t \<le>\<^sub>C s1'"
  proof auto
    fix ta
    assume case_assm: "t = [Y]\<^sub>R # ta"
    then obtain tb where ta_def: "ta = [Tock]\<^sub>E # tb"
      using assms(3) tocks.cases by blast
    then obtain s2a where s2_def: "s2 = [Tock]\<^sub>E # s2a"
      using assms(4) s1'_def case_assm by (cases s2 rule:ttWF.cases, auto)
    then have "[[X]\<^sub>R, [Tock]\<^sub>E] \<le>\<^sub>C [[X]\<^sub>R]"
      using assms(1) by (erule_tac x="[[X]\<^sub>R, [Tock]\<^sub>E]" in ballE, auto simp add: tocks.intros)
    then show "[Y]\<^sub>R # ta \<le>\<^sub>C s1'"
      by auto
  qed
next
  fix s1' t
  assume assms: "\<forall>t\<in>tocks UNIV. t \<le>\<^sub>C [[Tick]\<^sub>E] @ s2 \<longrightarrow> t \<le>\<^sub>C [[Tick]\<^sub>E]" "[[Tick]\<^sub>E] \<subseteq>\<^sub>C s1'" "t \<in> tocks UNIV" "t \<le>\<^sub>C s1' @ s2"
  then have s1'_def: "s1' = [[Tick]\<^sub>E]"
    by (cases s1' rule:ttWF.cases, auto)
  then have "t = [] \<or> (\<exists> ta. t = [Tick]\<^sub>E # ta)"
    using assms(4) tt_prefix.elims(2) by auto
  then show "t \<le>\<^sub>C s1'"
    using assms(3) start_tick_notin_tocks by auto
next
  fix e \<sigma> s1' t
  assume assms: "[Event e]\<^sub>E # \<sigma> \<subseteq>\<^sub>C s1'" "t \<in> tocks UNIV" "t \<le>\<^sub>C s1' @ s2"
  then obtain s1'a where s1'_def: "s1' = [Event e]\<^sub>E # s1'a"
    by (cases s1' rule:ttWF.cases, auto)
  then have "t = [] \<or> (\<exists> ta. t = [Event e]\<^sub>E # ta)"
    using assms(3) tt_prefix.elims(2) by auto
  then show "t \<le>\<^sub>C s1'"
    using assms(2) start_event_notin_tocks by force
next
  fix X \<sigma> s1' t
  assume ind_hyp: "\<And>s1' t. \<forall>t\<in>tocks UNIV. t \<le>\<^sub>C \<sigma> @ s2 \<longrightarrow> t \<le>\<^sub>C \<sigma> \<Longrightarrow> \<sigma> \<subseteq>\<^sub>C s1' \<Longrightarrow> t \<in> tocks UNIV \<Longrightarrow> t \<le>\<^sub>C s1' @ s2 \<Longrightarrow> t \<le>\<^sub>C s1'"
  assume assms: "\<forall>t\<in>tocks UNIV. t \<le>\<^sub>C ([X]\<^sub>R # [Tock]\<^sub>E # \<sigma>) @ s2 \<longrightarrow> t \<le>\<^sub>C [X]\<^sub>R # [Tock]\<^sub>E # \<sigma>" "[X]\<^sub>R # [Tock]\<^sub>E # \<sigma> \<subseteq>\<^sub>C s1'" "t \<in> tocks UNIV" "t \<le>\<^sub>C s1' @ s2"
  obtain Y s1'a where s1'_def: "s1' = [Y]\<^sub>R # [Tock]\<^sub>E # s1'a"
    using assms(2) by (cases s1' rule:ttWF.cases, auto)
  have 1: "\<forall>t\<in>tocks UNIV. t \<le>\<^sub>C \<sigma> @ s2 \<longrightarrow> t \<le>\<^sub>C \<sigma>"
    using assms(1) by (auto, erule_tac x="[X]\<^sub>R # [Tock]\<^sub>E # t" in ballE, auto simp add: tock_insert_in_tocks)
  have 2: "\<sigma> \<subseteq>\<^sub>C s1'a"
    using assms(2) s1'_def by auto
  have t_cases: "t = [] \<or> (\<exists> ta. t = [Y]\<^sub>R # [Tock]\<^sub>E # ta)"
    using assms(4) s1'_def assms(3) refusal_notin_tocks by (cases t rule:ttWF.cases, auto)
  then show "t \<le>\<^sub>C s1'"
  proof auto
    fix ta
    assume case_assm: "t = [Y]\<^sub>R # [Tock]\<^sub>E # ta"
    then have 3: "ta \<in> tocks UNIV"
      using assms(3) tocks.cases by auto
    then have 4: "ta \<le>\<^sub>C s1'a @ s2"
      using assms(4) case_assm s1'_def by auto
    have "ta \<le>\<^sub>C s1'a"
      using ind_hyp 1 2 3 4 by auto
    then show "[Y]\<^sub>R # [Tock]\<^sub>E # ta \<le>\<^sub>C s1'"
      using s1'_def by auto
  qed
next
  fix va s1' t
  assume assms: "[Tock]\<^sub>E # va \<subseteq>\<^sub>C s1'" "t \<in> tocks UNIV" "t \<le>\<^sub>C s1' @ s2"
  then obtain s1'a where "s1' = [Tock]\<^sub>E # s1'a"
    by (cases s1' rule:ttWF.cases, auto)
  then have "t = [] \<or> (\<exists> ta. t = [Tock]\<^sub>E # ta)"
    using assms(3) by (cases t rule:ttWF.cases, auto)
  then show "t \<le>\<^sub>C s1'"
    using assms(2) ttWFw.simps(6) tocks_wfw by (auto, blast)
next
  fix va s1' t
  assume assms: "[Tock]\<^sub>E # va \<subseteq>\<^sub>C s1'" "t \<in> tocks UNIV" "t \<le>\<^sub>C s1' @ s2"
  then obtain s1'a where "s1' = [Tock]\<^sub>E # s1'a"
    by (cases s1' rule:ttWF.cases, auto)
  then have "t = [] \<or> (\<exists> ta. t = [Tock]\<^sub>E # ta)"
    using assms(3) by (cases t rule:ttWF.cases, auto)
  then show "t \<le>\<^sub>C s1'"
    using assms(2) ttWFw.simps(6) tocks_wfw by (auto, blast)
next
  fix va s1' t
  assume assms: "[Tock]\<^sub>E # va \<subseteq>\<^sub>C s1'" "t \<in> tocks UNIV" "t \<le>\<^sub>C s1' @ s2"
  then obtain s1'a where "s1' = [Tock]\<^sub>E # s1'a"
    by (cases s1' rule:ttWF.cases, auto)
  then have "t = [] \<or> (\<exists> ta. t = [Tock]\<^sub>E # ta)"
    using assms(3) by (cases t rule:ttWF.cases, auto)
  then show "t \<le>\<^sub>C s1'"
    using assms(2) ttWFw.simps(6) tocks_wfw by (auto, blast)
next
  fix va s1' t
  assume assms: "[Tick]\<^sub>E # va \<subseteq>\<^sub>C s1'" "t \<in> tocks UNIV" "t \<le>\<^sub>C s1' @ s2"
  then obtain s1'a where "s1' = [Tick]\<^sub>E # s1'a"
    by (cases s1' rule:ttWF.cases, auto)
  then have "t = [] \<or> (\<exists> ta. t = [Tick]\<^sub>E # ta)"
    using assms(3) by (cases t rule:ttWF.cases, auto)
  then show "t \<le>\<^sub>C s1'"
    using assms(2) start_tick_notin_tocks by auto
next
  fix va s1' t
  assume assms: "[Tick]\<^sub>E # va \<subseteq>\<^sub>C s1'" "t \<in> tocks UNIV" "t \<le>\<^sub>C s1' @ s2"
  then obtain s1'a where "s1' = [Tick]\<^sub>E # s1'a"
    by (cases s1' rule:ttWF.cases, auto)
  then have "t = [] \<or> (\<exists> ta. t = [Tick]\<^sub>E # ta)"
    using assms(3) by (cases t rule:ttWF.cases, auto)
  then show "t \<le>\<^sub>C s1'"
    using assms(2) start_tick_notin_tocks by auto
next
  fix va vd vc s1' t
  assume assms: "[va]\<^sub>R # [Event vd]\<^sub>E # vc \<subseteq>\<^sub>C s1'" "t \<in> tocks UNIV" "t \<le>\<^sub>C s1' @ s2"
  then obtain s1'a X where "s1' = [X]\<^sub>R # [Event vd]\<^sub>E # s1'a"
    by (cases s1' rule:ttWF.cases, auto)
  then have "t = [] \<or> t = [[X]\<^sub>R] \<or> (\<exists> ta. t = [X]\<^sub>R # [Event vd]\<^sub>E # ta)"
    using assms(3) by (cases t rule:ttWF.cases, auto)
  then show "t \<le>\<^sub>C s1'"
    using assms(2) refusal_notin_tocks second_event_notin_tocks by force
next
  fix va vd vc s1' t
  assume assms: "[va]\<^sub>R # [Tick]\<^sub>E # vc \<subseteq>\<^sub>C s1'" "t \<in> tocks UNIV" "t \<le>\<^sub>C s1' @ s2"
  then obtain s1'a X where "s1' = [X]\<^sub>R # [Tick]\<^sub>E # s1'a"
    by (cases s1' rule:ttWF.cases, auto)
  then have "t = [] \<or> t = [[X]\<^sub>R] \<or> (\<exists> ta. t = [X]\<^sub>R # [Tick]\<^sub>E # ta)"
    using assms(3) by (cases t rule:ttWF.cases, auto)
  then show "t \<le>\<^sub>C s1'"
    using assms(2) refusal_notin_tocks second_tick_notin_tocks by force
next
  fix va v vc s1' t
  assume assms: "[va]\<^sub>R # [v]\<^sub>R # vc \<subseteq>\<^sub>C s1'" "t \<in> tocks UNIV" "t \<le>\<^sub>C s1' @ s2"
  then obtain s1'a X Y where "s1' = [X]\<^sub>R # [Y]\<^sub>R # s1'a"
    by (cases s1' rule:ttWF.cases, auto)
  then have "t = [] \<or> t = [[X]\<^sub>R] \<or> (\<exists> ta. t = [X]\<^sub>R # [Y]\<^sub>R # ta)"
    using assms(3) by (cases t rule:ttWF.cases, auto)
  then show "t \<le>\<^sub>C s1'"
    using assms(2) refusal_notin_tocks double_refusal_start_notin_tocks by force
qed

lemma tocks_tt_subset1:
  "\<sigma> \<in> tocks X \<Longrightarrow> \<rho> \<subseteq>\<^sub>C \<sigma> \<Longrightarrow> \<rho> \<in> tocks X"
proof (induct \<rho> \<sigma> rule:ttWF2.induct, auto simp add: notin_tocks)
  fix Xa \<rho> Y \<sigma>
  assume "[Y]\<^sub>R # [Tock]\<^sub>E # \<sigma> \<in> tocks X"
  then have "\<sigma> \<in> tocks X \<and> Y \<subseteq> X"
    by (cases rule:tocks.cases, auto)
  then show "(\<sigma> \<in> tocks X \<Longrightarrow> \<rho> \<in> tocks X) \<Longrightarrow> Xa \<subseteq> Y \<Longrightarrow> \<rho> \<subseteq>\<^sub>C \<sigma> \<Longrightarrow> [Xa]\<^sub>R # [Tock]\<^sub>E # \<rho> \<in> tocks X"
    by (meson order.trans tocks.tock_insert_in_tocks)
next
  fix Xa \<rho> \<sigma>
  show "\<sigma> \<in> tocks X \<Longrightarrow> [Xa]\<^sub>R # [Tick]\<^sub>E # \<rho> \<subseteq>\<^sub>C \<sigma> \<Longrightarrow> False"
    using ttWFw.simps(12) tt_prefix_subset_ttWFw tt_subset_imp_prefix_subset tocks_wfw by blast
next
  fix Xa e \<rho> \<sigma>
  show "\<sigma> \<in> tocks X \<Longrightarrow> [Xa]\<^sub>R # [Event e]\<^sub>E # \<rho> \<subseteq>\<^sub>C \<sigma> \<Longrightarrow> False"
    by (meson ttWFw.simps(11) tt_prefix_subset_ttWFw tt_subset_imp_prefix_subset tocks_wfw)
next
  fix Xa Y \<rho> \<sigma>
  show "\<sigma> \<in> tocks X \<Longrightarrow> [Xa]\<^sub>R # [Y]\<^sub>R # \<rho> \<subseteq>\<^sub>C \<sigma> \<Longrightarrow> False"
    using ttWFw.simps(13) tt_prefix_subset_ttWFw tt_subset_imp_prefix_subset tocks_wfw by blast
next
  fix x \<rho> \<sigma>
  show "\<sigma> \<in> tocks X \<Longrightarrow> [Tick]\<^sub>E # x # \<rho> \<subseteq>\<^sub>C \<sigma> \<Longrightarrow> False"
    using ttWFw.simps(8) tt_prefix_subset_ttWFw tt_subset_imp_prefix_subset tocks_wfw by blast
next
  fix \<rho> \<sigma>
  show "\<sigma> \<in> tocks X \<Longrightarrow> [Tock]\<^sub>E # \<rho> \<subseteq>\<^sub>C \<sigma> \<Longrightarrow> False"
    using ttWFw.simps(6) tt_prefix_subset_ttWFw tt_subset_imp_prefix_subset tocks_wfw by blast
qed

lemma tocks_tt_subset2:
  "\<rho> \<in> tocks X \<Longrightarrow> \<rho> \<subseteq>\<^sub>C \<sigma> \<Longrightarrow> \<sigma> \<in> tocks UNIV"
proof (induct \<rho> \<sigma> rule:ttWF2.induct, auto simp add: notin_tocks)
  show "[] \<in> tocks UNIV"
    by (simp add: tocks.empty_in_tocks)
next
  fix Xa \<rho> Y \<sigma>
  assume "[Xa]\<^sub>R # [Tock]\<^sub>E # \<rho> \<in> tocks X"
  then have "\<rho> \<in> tocks X \<and> Xa \<subseteq> X"
    by (cases rule:tocks.cases, auto)
  then show "(\<rho> \<in> tocks X \<Longrightarrow> \<sigma> \<in> tocks UNIV) \<Longrightarrow> Xa \<subseteq> Y \<Longrightarrow> \<rho> \<subseteq>\<^sub>C \<sigma> \<Longrightarrow> [Y]\<^sub>R # [Tock]\<^sub>E # \<sigma> \<in> tocks UNIV"
    by (simp add: tocks.tock_insert_in_tocks)
next
  fix Xa \<rho> \<sigma>
  show "\<rho> \<in> tocks X \<Longrightarrow> \<rho> \<subseteq>\<^sub>C [Xa]\<^sub>R # [Tick]\<^sub>E # \<sigma> \<Longrightarrow> False"
    by (metis ttWFw.simps(12) tt_subset.simps(2) tt_subset.simps(3) tt_subset.simps(8) tocks.simps tocks_wfw)
next
  fix Xa e \<rho> \<sigma>
  show "\<rho> \<in> tocks X \<Longrightarrow> \<rho> \<subseteq>\<^sub>C [Xa]\<^sub>R # [Event e]\<^sub>E # \<sigma> \<Longrightarrow> False"
    by (metis tt_subset.simps(2) tt_subset.simps(3) tt_subset.simps(8) second_event_notin_tocks tocks.cases)
next
  fix Xa Y \<rho> \<sigma>
  show "\<rho> \<in> tocks X \<Longrightarrow> \<rho> \<subseteq>\<^sub>C [Xa]\<^sub>R # [Y]\<^sub>R # \<sigma> \<Longrightarrow> False"
    by (metis tt_subset.simps(2) tt_subset.simps(8) tt_subset.simps(9) tocks.simps)
next
  fix y \<rho> \<sigma>
  show "\<rho> \<in> tocks X \<Longrightarrow> \<rho> \<subseteq>\<^sub>C [Tick]\<^sub>E # y # \<sigma> \<Longrightarrow> False"
    by (metis tt_subset.simps(11) tt_subset.simps(8) tocks.cases)
next
  fix \<rho> \<sigma>
  show "\<rho> \<in> tocks X \<Longrightarrow> \<rho> \<subseteq>\<^sub>C [Tock]\<^sub>E # \<sigma> \<Longrightarrow> False"
    by (metis tt_subset.simps(10) tt_subset.simps(11) tocks.simps)
qed

lemma tocks_mid_refusal:
  "\<rho> @ [X]\<^sub>R # \<sigma> \<in> tocks Y \<Longrightarrow> X \<subseteq> Y"
proof (induct \<rho> rule:ttWF.induct, auto simp add: notin_tocks)
  fix x
  show "[X]\<^sub>R # \<sigma> \<in> tocks Y \<Longrightarrow> x \<in> X \<Longrightarrow> x \<in> Y"
    using tocks.cases by (cases \<sigma> rule:ttWF.cases, auto simp add: notin_tocks)
next
  fix Xa \<sigma>' x
  assume ind_hyp: "\<sigma>' @ [X]\<^sub>R # \<sigma> \<in> tocks Y \<Longrightarrow> X \<subseteq> Y"
  assume "[Xa]\<^sub>R # [Tock]\<^sub>E # \<sigma>' @ [X]\<^sub>R # \<sigma> \<in> tocks Y"
  then have "\<sigma>' @ [X]\<^sub>R # \<sigma> \<in> tocks Y"
    using tocks.cases by auto
  then show "x \<in> X \<Longrightarrow> x \<in> Y"
    using ind_hyp by auto
qed

lemma tocks_mid_refusal_change:
  "\<rho> @ [X]\<^sub>R # \<sigma> \<in> tocks Y \<Longrightarrow> Z \<subseteq> Y \<Longrightarrow> \<rho> @ [Z]\<^sub>R # \<sigma> \<in> tocks Y"
proof (induct \<rho> rule:ttWF.induct, auto simp add: notin_tocks)
  show "[X]\<^sub>R # \<sigma> \<in> tocks Y \<Longrightarrow> Z \<subseteq> Y \<Longrightarrow> [Z]\<^sub>R # \<sigma> \<in> tocks Y"
  proof (cases \<sigma> rule:ttWF.cases, auto simp add: notin_tocks)
    fix va
    assume "[X]\<^sub>R # [Tock]\<^sub>E # va \<in> tocks Y"
    then have "va \<in> tocks Y"
      using tocks.cases by auto
    then show "Z \<subseteq> Y \<Longrightarrow> [Z]\<^sub>R # [Tock]\<^sub>E # va \<in> tocks Y"
      using tocks.intros by blast
  next
    fix va
    assume "[X]\<^sub>R # [Tock]\<^sub>E # va \<in> tocks Y"
    then have "va \<in> tocks Y"
      using tocks.cases by auto
    then show "Z \<subseteq> Y \<Longrightarrow> [Z]\<^sub>R # [Tock]\<^sub>E # va \<in> tocks Y"
      using tocks.intros by blast
  next
    fix va
    assume "[X]\<^sub>R # [Tock]\<^sub>E # va \<in> tocks Y"
    then have "va \<in> tocks Y"
      using tocks.cases by auto
    then show "Z \<subseteq> Y \<Longrightarrow> [Z]\<^sub>R # [Tock]\<^sub>E # va \<in> tocks Y"
      using tocks.intros by blast
  qed
next
  fix Xa \<sigma>'
  assume ind_hyp: "\<sigma>' @ [X]\<^sub>R # \<sigma> \<in> tocks Y \<Longrightarrow> \<sigma>' @ [Z]\<^sub>R # \<sigma> \<in> tocks Y"
  assume "[Xa]\<^sub>R # [Tock]\<^sub>E # \<sigma>' @ [X]\<^sub>R # \<sigma> \<in> tocks Y"
  then have "\<sigma>' @ [X]\<^sub>R # \<sigma> \<in> tocks Y \<and> Xa \<subseteq> Y"
    using tocks.cases by auto
  then have "\<sigma>' @ [Z]\<^sub>R # \<sigma> \<in> tocks Y \<and> Xa \<subseteq> Y"
    using ind_hyp by auto
  then show "Z \<subseteq> Y \<Longrightarrow> [Xa]\<^sub>R # [Tock]\<^sub>E # \<sigma>' @ [Z]\<^sub>R # \<sigma> \<in> tocks Y"
    using tocks.intros by blast
qed

lemma tocks_mid_refusal_front_in_tocks:
  "\<rho> @ [X]\<^sub>R # \<sigma> \<in> tocks Y \<Longrightarrow> \<rho> \<in> tocks Y"
  apply (induct \<rho> rule:ttWF.induct)
  using tocks.cases apply auto
  using tocks.simps apply blast
  by (metis (no_types, lifting) list.distinct(1) list.inject tocks.simps)

lemma TT0_tocks: "TT0 (tocks X)"
  unfolding TT0_def using tocks.empty_in_tocks by auto 

lemma TT2w_tocks: "TT2w (tocks X)"
  unfolding TT2w_def by (simp add: end_refusal_notin_tocks)

lemma ttWFx_tocks: "Tock \<notin> X \<Longrightarrow> ttWFx (tocks X)"
  unfolding ttWFx_def
proof auto
  fix x
  show "Tock \<notin> X \<Longrightarrow> x \<in> tocks X \<Longrightarrow> ttWFx_trace x"
    using tocks.cases by (induct rule:ttWFx_trace.induct, auto)
qed

lemma TT3w_tocks: "Tick \<in> X \<Longrightarrow> TT3w (tocks X)"
  unfolding TT3w_def
proof auto
  fix \<rho>
  assume assm: "Tick \<in> X"
  show "\<rho> \<in> tocks X \<Longrightarrow> add_Tick_refusal_trace \<rho> \<in> tocks X"
    by (induct \<rho> rule:tocks.induct, auto simp add: assm tocks.empty_in_tocks tocks.tock_insert_in_tocks)
qed

lemma in_tocks_last:
  "t \<noteq> [] \<Longrightarrow> t \<in> tocks X \<Longrightarrow> last t = [Tock]\<^sub>E"
  apply (induct t rule:ttWF.induct, auto simp add: notin_tocks)
  using tocks.simps by auto

section {* Refinement *}

definition RefinesTT :: "'e ttobs list set \<Rightarrow> 'e ttobs list set \<Rightarrow> bool" (infix "\<sqsubseteq>\<^sub>C" 50) where
  "P \<sqsubseteq>\<^sub>C Q = (Q \<subseteq> P)"

section {* Refinement lattice supplementary definitions and proofs *}

lemma ttWF_traces_TT0:
  "TT0 {t. ttWF t}"
  unfolding TT0_def by (auto, rule_tac x="[]" in exI, auto)

lemma ttWF_traces_TT1:
  "TT1 {t. ttWF t}"
  unfolding TT1_def using tt_prefix_subset_ttWF tt_prefix_of_ttWFx_trace by blast

lemma ttWF_traces_TT2:
  "TT2 {t. ttWF t}"
  unfolding TT2_def
proof auto
  fix \<rho> \<sigma> :: "'a ttobs list"
  fix X Y
  assume assm1: "ttWF (\<rho> @ [X]\<^sub>R # \<sigma>)"
  assume assm2: "Y \<inter> {e. e \<noteq> Tock \<and> ttWF (\<rho> @ [[e]\<^sub>E]) \<or> e = Tock \<and> ttWF (\<rho> @ [[X]\<^sub>R, [e]\<^sub>E])} = {}"
  have \<rho>_wf: "ttWF \<rho>"
    using assm1 ttWF_prefix_is_ttWF by blast
  show "ttWF (\<rho> @ [X \<union> Y]\<^sub>R # \<sigma>)"
  proof (cases "Tock \<in> X")
    assume case_assm: "Tock \<in> X"
    then have "Y \<inter> {e. e \<noteq> Tock \<and> ttWF (\<rho> @ [[e]\<^sub>E])} = {}"
      using assm2 by (induct \<rho> rule:ttWF.induct, auto)
    also have "{e. e \<noteq> Tock} \<subseteq> {e. e \<noteq> Tock \<and> ttWF (\<rho> @ [[e]\<^sub>E])}"
      using assm1 by (auto, case_tac x, auto, (induct \<rho> rule:ttWF.induct, auto)+)
    then have "Y \<inter> {e. e \<noteq> Tock} = {}"
      using calculation by auto
    then have "Y = {} \<or> Y = {Tock}"
      by auto
    then show "ttWF (\<rho> @ [X \<union> Y]\<^sub>R # \<sigma>)"
    proof auto
      show "ttWF (\<rho> @ [X]\<^sub>R # \<sigma>)"
        using assm1 by auto
    next
      have "insert Tock X = X"
        using case_assm by auto
      then show "ttWF (\<rho> @ [insert Tock X]\<^sub>R # \<sigma>)"
        using assm1 by auto
    qed
  next
    assume "Tock \<notin> X"
    then have "{e. e \<noteq> Tock \<and> ttWF (\<rho> @ [[e]\<^sub>E]) \<or> e = Tock \<and> ttWF (\<rho> @ [[X]\<^sub>R, [e]\<^sub>E])} = UNIV"
      using assm1 by (induct \<rho> rule:ttWF.induct, auto, (case_tac x, auto)+)
    then have "Y = {}"
      using assm2 by auto
    then show "ttWF (\<rho> @ [X \<union> Y]\<^sub>R # \<sigma>)"
      using assm1 by auto
  qed
qed

lemma ttWF_traces_TT3w:
  "TT3w {t. ttWF t}"
  unfolding TT3w_def
proof auto
  fix \<rho> :: "'a ttobs list"
  show "ttWF \<rho> \<Longrightarrow> ttWF (add_Tick_refusal_trace \<rho>)"
    by (induct \<rho> rule:ttWF.induct, auto)
qed

lemma bottom_healthy_process:
  assumes "\<forall> t\<in>P. ttWF t" "TT0 P" "TT1 P" "TT2 P" "TT3w P"
  shows "{t. ttWF t} \<sqsubseteq>\<^sub>C P"
  using assms unfolding RefinesTT_def by auto

definition SupremumTT :: "'a ttobs list set \<Rightarrow> 'a ttobs list set \<Rightarrow> 'a ttobs list set" where
  "SupremumTT P Q = {t\<in>P\<inter>Q. \<forall> \<rho> \<sigma> X Y. t = \<rho> @ [[X]\<^sub>R] @ \<sigma>
    \<and> Y \<inter> {e. e \<noteq> Tock \<and> \<rho> @ [[e]\<^sub>E] \<in> P \<inter> Q \<or> e = Tock \<and> \<rho> @ [[X]\<^sub>R, [e]\<^sub>E] \<in> P \<inter> Q} = {} \<longrightarrow>
      \<rho> @ [[X \<union> Y]\<^sub>R] @ \<sigma> \<in> P \<inter> Q}"

lemma SupremumTT_wf:
  assumes P_healthy: "\<forall> t\<in>P. ttWF t" and Q_healthy: "\<forall> t\<in>Q. ttWF t"
  shows "\<forall>t\<in>SupremumTT P Q. ttWF t"
  unfolding SupremumTT_def using assms by auto

lemma TT0_Supremum:
  assumes TT0_P: "TT0 P" and TT1_P: "TT1 P"
  assumes TT0_Q: "TT0 Q" and TT1_Q: "TT1 Q"
  shows "TT0 (SupremumTT P Q)"
proof -
  have "[] \<in> P"
    by (simp add: TT0_P TT0_TT1_empty TT1_P)
  also have "[] \<in> Q"
    by (simp add: TT0_Q TT0_TT1_empty TT1_Q)
  then show ?thesis
    using calculation unfolding TT0_def SupremumTT_def by auto
qed

lemma TT1_Supremum:
  assumes P_wf: "\<forall> t\<in>P. ttWF t" and TT1_P: "TT1 P" and TT2_P: "TT2 P"
  assumes P_wf: "\<forall> t\<in>P. ttWF t" and TT1_Q: "TT1 Q" and TT2_Q: "TT2 Q"
  shows "TT1 (SupremumTT P Q)"
  unfolding TT1_def SupremumTT_def
proof auto
  fix \<rho> \<sigma>
  show "\<rho> \<lesssim>\<^sub>C \<sigma> \<Longrightarrow> \<sigma> \<in> P \<Longrightarrow> \<rho> \<in> P"
    using TT1_P TT1_def by blast
next
  fix \<rho> \<sigma>
  show "\<rho> \<lesssim>\<^sub>C \<sigma> \<Longrightarrow> \<sigma> \<in> Q \<Longrightarrow> \<rho> \<in> Q"
    using TT1_Q TT1_def by blast
next
  fix \<sigma> \<rho>' \<sigma>' :: "'a ttobs list"
  fix X Y
  assume assm1: "Y \<inter> {e. e \<noteq> Tock \<and> \<rho>' @ [[e]\<^sub>E] \<in> P \<and> \<rho>' @ [[e]\<^sub>E] \<in> Q \<or> e = Tock \<and> \<rho>' @ [[X]\<^sub>R, [e]\<^sub>E] \<in> P \<and> \<rho>' @ [[X]\<^sub>R, [e]\<^sub>E] \<in> Q} = {}"
  assume assm2: "\<rho>' @ [X]\<^sub>R # \<sigma>' \<lesssim>\<^sub>C \<sigma>"
  assume assm3: "\<sigma> \<in> P"
  assume assm4: "\<sigma> \<in> Q"
  assume ind_hyp: "\<forall>\<rho> \<sigma>' X Y. \<sigma> = \<rho> @ [X]\<^sub>R # \<sigma>'
    \<and> Y \<inter> {e. e \<noteq> Tock \<and> \<rho> @ [[e]\<^sub>E] \<in> P \<and> \<rho> @ [[e]\<^sub>E] \<in> Q \<or> e = Tock \<and> \<rho> @ [[X]\<^sub>R, [e]\<^sub>E] \<in> P \<and> \<rho> @ [[X]\<^sub>R, [e]\<^sub>E] \<in> Q} = {} \<longrightarrow>
      \<rho> @ [X \<union> Y]\<^sub>R # \<sigma>' \<in> P \<and> \<rho> @ [X \<union> Y]\<^sub>R # \<sigma>' \<in> Q"
  obtain \<tau> where \<tau>_assms: "\<rho>' @ [X]\<^sub>R # \<sigma>' \<le>\<^sub>C \<tau> \<and> \<tau> \<subseteq>\<^sub>C \<sigma>"
    using assm2 tt_prefix_subset_imp_tt_prefix_tt_subset by blast
  then obtain \<tau>' where "\<tau> = \<rho>' @ [X]\<^sub>R # \<sigma>' @ \<tau>'"
    using tt_prefix_split by fastforce
  then have "\<exists> \<rho>'' \<sigma>''. \<sigma> = \<rho>'' @ \<sigma>'' \<and> \<rho>' \<subseteq>\<^sub>C \<rho>'' \<and> [X]\<^sub>R # \<sigma>' @ \<tau>' \<subseteq>\<^sub>C \<sigma>''"
    using \<tau>_assms by (auto simp add: tt_subset_split2)
  then have "\<exists> \<rho>'' \<sigma>'' X'. \<sigma> = \<rho>'' @ [X']\<^sub>R # \<sigma>'' \<and> \<rho>' \<subseteq>\<^sub>C \<rho>'' \<and> X \<subseteq> X' \<and> \<sigma>' @ \<tau>' \<subseteq>\<^sub>C \<sigma>''"
    by (auto, rule_tac x="\<rho>''" in exI, auto, case_tac \<sigma>'' rule:ttWF.cases, auto)
  then obtain \<rho>'' \<sigma>'' X' where \<sigma>_assms: "\<sigma> = \<rho>'' @ [X']\<^sub>R # \<sigma>'' \<and> \<rho>' \<subseteq>\<^sub>C \<rho>'' \<and> X \<subseteq> X' \<and> \<sigma>' @ \<tau>' \<subseteq>\<^sub>C \<sigma>''"
    by auto
  then have "\<rho>' @ [[X]\<^sub>R] \<subseteq>\<^sub>C \<rho>'' @ [[X']\<^sub>R]"
    by (simp add: tt_subset_combine)
  then have "{e. e \<noteq> Tock \<and> \<rho>'' @ [[e]\<^sub>E] \<in> P \<and> \<rho>'' @ [[e]\<^sub>E] \<in> Q \<or> e = Tock \<and> \<rho>'' @ [[X']\<^sub>R, [e]\<^sub>E] \<in> P \<and> \<rho>'' @ [[X']\<^sub>R, [e]\<^sub>E] \<in> Q}
    \<subseteq> {e. e \<noteq> Tock \<and> \<rho>' @ [[e]\<^sub>E] \<in> P \<and> \<rho>' @ [[e]\<^sub>E] \<in> Q \<or> e = Tock \<and> \<rho>' @ [[X]\<^sub>R, [e]\<^sub>E] \<in> P \<and> \<rho>' @ [[X]\<^sub>R, [e]\<^sub>E] \<in> Q}"
    using \<sigma>_assms
  proof auto
    fix x
    show "\<rho>' \<subseteq>\<^sub>C \<rho>'' \<Longrightarrow> \<rho>'' @ [[x]\<^sub>E] \<in> P \<Longrightarrow> \<rho>' @ [[x]\<^sub>E] \<in> P"
      using TT1_P TT1_def tt_subset_end_event tt_subset_imp_prefix_subset by blast
  next
    fix x
    show "\<rho>' \<subseteq>\<^sub>C \<rho>'' \<Longrightarrow> \<rho>'' @ [[x]\<^sub>E] \<in> P \<Longrightarrow> \<rho>' @ [[x]\<^sub>E] \<in> P"
      using TT1_P TT1_def tt_subset_end_event tt_subset_imp_prefix_subset by blast
  next
    fix x
    show "\<rho>' \<subseteq>\<^sub>C \<rho>'' \<Longrightarrow> \<rho>'' @ [[x]\<^sub>E] \<in> P \<Longrightarrow> \<rho>' @ [[x]\<^sub>E] \<in> P"
      using TT1_P TT1_def tt_subset_end_event tt_subset_imp_prefix_subset by blast
  next
    fix x
    show "\<rho>' \<subseteq>\<^sub>C \<rho>'' \<Longrightarrow> \<rho>'' @ [[x]\<^sub>E] \<in> Q \<Longrightarrow> \<rho>' @ [[x]\<^sub>E] \<in> Q"
      using TT1_Q TT1_def tt_subset_end_event tt_subset_imp_prefix_subset by blast
  next
    fix x
    show "\<rho>' \<subseteq>\<^sub>C \<rho>'' \<Longrightarrow> \<rho>'' @ [[x]\<^sub>E] \<in> Q \<Longrightarrow> \<rho>' @ [[x]\<^sub>E] \<in> Q"
      using TT1_Q TT1_def tt_subset_end_event tt_subset_imp_prefix_subset by blast
  next
    fix x
    show "\<rho>' \<subseteq>\<^sub>C \<rho>'' \<Longrightarrow> \<rho>'' @ [[x]\<^sub>E] \<in> Q \<Longrightarrow> \<rho>' @ [[x]\<^sub>E] \<in> Q"
      using TT1_Q TT1_def tt_subset_end_event tt_subset_imp_prefix_subset by blast
  next
    show "\<rho>' \<subseteq>\<^sub>C \<rho>'' \<Longrightarrow> X \<subseteq> X' \<Longrightarrow> \<rho>'' @ [[X']\<^sub>R, [Tock]\<^sub>E] \<in> P \<Longrightarrow> \<rho>' @ [[X]\<^sub>R, [Tock]\<^sub>E] \<in> P"
      by (meson TT1_P TT1_def tt_prefix_subset.simps(2) tt_prefix_subset_eq_length_common_prefix_eq tt_prefix_subset_refl tt_subset_imp_prefix_subset tt_subset_same_length)
  next
    show "\<rho>' \<subseteq>\<^sub>C \<rho>'' \<Longrightarrow> X \<subseteq> X' \<Longrightarrow> \<rho>'' @ [[X']\<^sub>R, [Tock]\<^sub>E] \<in> Q \<Longrightarrow> \<rho>' @ [[X]\<^sub>R, [Tock]\<^sub>E] \<in> Q"
      by (meson TT1_Q TT1_def tt_prefix_subset.simps(2) tt_prefix_subset_eq_length_common_prefix_eq tt_prefix_subset_refl tt_subset_imp_prefix_subset tt_subset_same_length)
  next
    show "\<rho>' \<subseteq>\<^sub>C \<rho>'' \<Longrightarrow> X \<subseteq> X' \<Longrightarrow> \<rho>'' @ [[X']\<^sub>R, [Tock]\<^sub>E] \<in> P \<Longrightarrow> \<rho>' @ [[X]\<^sub>R, [Tock]\<^sub>E] \<notin> P \<Longrightarrow> \<rho>' @ [[Tock]\<^sub>E] \<in> P"
      by (meson TT1_P TT1_def tt_prefix_subset.simps(2) tt_prefix_subset_eq_length_common_prefix_eq tt_prefix_subset_refl tt_subset_imp_prefix_subset tt_subset_same_length)
  next
    show "\<rho>' \<subseteq>\<^sub>C \<rho>'' \<Longrightarrow> X \<subseteq> X' \<Longrightarrow> \<rho>'' @ [[X']\<^sub>R, [Tock]\<^sub>E] \<in> P \<Longrightarrow> \<rho>' @ [[X]\<^sub>R, [Tock]\<^sub>E] \<notin> P \<Longrightarrow> \<rho>' @ [[Tock]\<^sub>E] \<in> Q"
      by (meson TT1_P TT1_def tt_prefix_subset.simps(2) tt_prefix_subset_eq_length_common_prefix_eq tt_prefix_subset_refl tt_subset_imp_prefix_subset tt_subset_same_length)
  next
    show "\<rho>' \<subseteq>\<^sub>C \<rho>'' \<Longrightarrow> X \<subseteq> X' \<Longrightarrow> \<rho>'' @ [[X']\<^sub>R, [Tock]\<^sub>E] \<in> Q \<Longrightarrow> \<rho>' @ [[X]\<^sub>R, [Tock]\<^sub>E] \<notin> Q \<Longrightarrow> \<rho>' @ [[Tock]\<^sub>E] \<in> P"
      by (meson TT1_Q TT1_def tt_prefix_subset.simps(2) tt_prefix_subset_eq_length_common_prefix_eq tt_prefix_subset_refl tt_subset_imp_prefix_subset tt_subset_same_length)
  next
    show "\<rho>' \<subseteq>\<^sub>C \<rho>'' \<Longrightarrow> X \<subseteq> X' \<Longrightarrow> \<rho>'' @ [[X']\<^sub>R, [Tock]\<^sub>E] \<in> Q \<Longrightarrow> \<rho>' @ [[X]\<^sub>R, [Tock]\<^sub>E] \<notin> Q \<Longrightarrow> \<rho>' @ [[Tock]\<^sub>E] \<in> Q"
      by (meson TT1_Q TT1_def tt_prefix_subset.simps(2) tt_prefix_subset_eq_length_common_prefix_eq tt_prefix_subset_refl tt_subset_imp_prefix_subset tt_subset_same_length)
  qed
  then have "Y \<inter> {e. e \<noteq> Tock \<and> \<rho>'' @ [[e]\<^sub>E] \<in> P \<and> \<rho>'' @ [[e]\<^sub>E] \<in> Q \<or> e = Tock \<and> \<rho>'' @ [[X']\<^sub>R, [e]\<^sub>E] \<in> P \<and> \<rho>'' @ [[X']\<^sub>R, [e]\<^sub>E] \<in> Q} = {}"
    using assm1 inf.order_iff by auto
  then have "\<rho>'' @ [X' \<union> Y]\<^sub>R # \<sigma>'' \<in> P \<and> \<rho>'' @ [X' \<union> Y]\<^sub>R # \<sigma>'' \<in> Q"
    by (simp add: \<sigma>_assms ind_hyp)
  also have "\<rho>' @ [X \<union> Y]\<^sub>R # \<sigma>' \<lesssim>\<^sub>C \<rho>'' @ [X' \<union> Y]\<^sub>R # \<sigma>''"
    using \<sigma>_assms apply auto
    by (metis (no_types, lifting) Un_commute sup.orderE sup_ge2 sup_left_commute tt_prefix_concat 
        tt_prefix_subset.simps(2) tt_prefix_subset_eq_length_common_prefix_eq tt_prefix_tt_prefix_subset_trans tt_subset_imp_prefix_subset tt_subset_same_length)
  then show "\<rho>' @ [X \<union> Y]\<^sub>R # \<sigma>' \<in> P"
    using TT1_P TT1_def calculation by blast
next
  fix \<sigma> \<rho>' \<sigma>' :: "'a ttobs list"
  fix X Y
  assume assm1: "Y \<inter> {e. e \<noteq> Tock \<and> \<rho>' @ [[e]\<^sub>E] \<in> P \<and> \<rho>' @ [[e]\<^sub>E] \<in> Q \<or> e = Tock \<and> \<rho>' @ [[X]\<^sub>R, [e]\<^sub>E] \<in> P \<and> \<rho>' @ [[X]\<^sub>R, [e]\<^sub>E] \<in> Q} = {}"
  assume assm2: "\<rho>' @ [X]\<^sub>R # \<sigma>' \<lesssim>\<^sub>C \<sigma>"
  assume assm3: "\<sigma> \<in> P"
  assume assm4: "\<sigma> \<in> Q"
  assume ind_hyp: "\<forall>\<rho> \<sigma>' X Y. \<sigma> = \<rho> @ [X]\<^sub>R # \<sigma>'
    \<and> Y \<inter> {e. e \<noteq> Tock \<and> \<rho> @ [[e]\<^sub>E] \<in> P \<and> \<rho> @ [[e]\<^sub>E] \<in> Q \<or> e = Tock \<and> \<rho> @ [[X]\<^sub>R, [e]\<^sub>E] \<in> P \<and> \<rho> @ [[X]\<^sub>R, [e]\<^sub>E] \<in> Q} = {} \<longrightarrow>
      \<rho> @ [X \<union> Y]\<^sub>R # \<sigma>' \<in> P \<and> \<rho> @ [X \<union> Y]\<^sub>R # \<sigma>' \<in> Q"
  obtain \<tau> where \<tau>_assms: "\<rho>' @ [X]\<^sub>R # \<sigma>' \<le>\<^sub>C \<tau> \<and> \<tau> \<subseteq>\<^sub>C \<sigma>"
    using assm2 tt_prefix_subset_imp_tt_prefix_tt_subset by blast
  then obtain \<tau>' where "\<tau> = \<rho>' @ [X]\<^sub>R # \<sigma>' @ \<tau>'"
    using tt_prefix_split by fastforce
  then have "\<exists> \<rho>'' \<sigma>''. \<sigma> = \<rho>'' @ \<sigma>'' \<and> \<rho>' \<subseteq>\<^sub>C \<rho>'' \<and> [X]\<^sub>R # \<sigma>' @ \<tau>' \<subseteq>\<^sub>C \<sigma>''"
    using \<tau>_assms by (auto simp add: tt_subset_split2)
  then have "\<exists> \<rho>'' \<sigma>'' X'. \<sigma> = \<rho>'' @ [X']\<^sub>R # \<sigma>'' \<and> \<rho>' \<subseteq>\<^sub>C \<rho>'' \<and> X \<subseteq> X' \<and> \<sigma>' @ \<tau>' \<subseteq>\<^sub>C \<sigma>''"
    by (auto, rule_tac x="\<rho>''" in exI, auto, case_tac \<sigma>'' rule:ttWF.cases, auto)
  then obtain \<rho>'' \<sigma>'' X' where \<sigma>_assms: "\<sigma> = \<rho>'' @ [X']\<^sub>R # \<sigma>'' \<and> \<rho>' \<subseteq>\<^sub>C \<rho>'' \<and> X \<subseteq> X' \<and> \<sigma>' @ \<tau>' \<subseteq>\<^sub>C \<sigma>''"
    by auto
  then have "\<rho>' @ [[X]\<^sub>R] \<subseteq>\<^sub>C \<rho>'' @ [[X']\<^sub>R]"
    by (simp add: tt_subset_combine)
  then have "{e. e \<noteq> Tock \<and> \<rho>'' @ [[e]\<^sub>E] \<in> P \<and> \<rho>'' @ [[e]\<^sub>E] \<in> Q \<or> e = Tock \<and> \<rho>'' @ [[X']\<^sub>R, [e]\<^sub>E] \<in> P \<and> \<rho>'' @ [[X']\<^sub>R, [e]\<^sub>E] \<in> Q}
    \<subseteq> {e. e \<noteq> Tock \<and> \<rho>' @ [[e]\<^sub>E] \<in> P \<and> \<rho>' @ [[e]\<^sub>E] \<in> Q \<or> e = Tock \<and> \<rho>' @ [[X]\<^sub>R, [e]\<^sub>E] \<in> P \<and> \<rho>' @ [[X]\<^sub>R, [e]\<^sub>E] \<in> Q}"
    using \<sigma>_assms
  proof auto
    fix x
    show "\<rho>' \<subseteq>\<^sub>C \<rho>'' \<Longrightarrow> \<rho>'' @ [[x]\<^sub>E] \<in> P \<Longrightarrow> \<rho>' @ [[x]\<^sub>E] \<in> P"
      using TT1_P TT1_def tt_subset_end_event tt_subset_imp_prefix_subset by blast
  next
    fix x
    show "\<rho>' \<subseteq>\<^sub>C \<rho>'' \<Longrightarrow> \<rho>'' @ [[x]\<^sub>E] \<in> P \<Longrightarrow> \<rho>' @ [[x]\<^sub>E] \<in> P"
      using TT1_P TT1_def tt_subset_end_event tt_subset_imp_prefix_subset by blast
  next
    fix x
    show "\<rho>' \<subseteq>\<^sub>C \<rho>'' \<Longrightarrow> \<rho>'' @ [[x]\<^sub>E] \<in> P \<Longrightarrow> \<rho>' @ [[x]\<^sub>E] \<in> P"
      using TT1_P TT1_def tt_subset_end_event tt_subset_imp_prefix_subset by blast
  next
    fix x
    show "\<rho>' \<subseteq>\<^sub>C \<rho>'' \<Longrightarrow> \<rho>'' @ [[x]\<^sub>E] \<in> Q \<Longrightarrow> \<rho>' @ [[x]\<^sub>E] \<in> Q"
      using TT1_Q TT1_def tt_subset_end_event tt_subset_imp_prefix_subset by blast
  next
    fix x
    show "\<rho>' \<subseteq>\<^sub>C \<rho>'' \<Longrightarrow> \<rho>'' @ [[x]\<^sub>E] \<in> Q \<Longrightarrow> \<rho>' @ [[x]\<^sub>E] \<in> Q"
      using TT1_Q TT1_def tt_subset_end_event tt_subset_imp_prefix_subset by blast
  next
    fix x
    show "\<rho>' \<subseteq>\<^sub>C \<rho>'' \<Longrightarrow> \<rho>'' @ [[x]\<^sub>E] \<in> Q \<Longrightarrow> \<rho>' @ [[x]\<^sub>E] \<in> Q"
      using TT1_Q TT1_def tt_subset_end_event tt_subset_imp_prefix_subset by blast
  next
    show "\<rho>' \<subseteq>\<^sub>C \<rho>'' \<Longrightarrow> X \<subseteq> X' \<Longrightarrow> \<rho>'' @ [[X']\<^sub>R, [Tock]\<^sub>E] \<in> P \<Longrightarrow> \<rho>' @ [[X]\<^sub>R, [Tock]\<^sub>E] \<in> P"
      by (meson TT1_P TT1_def tt_prefix_subset.simps(2) tt_prefix_subset_eq_length_common_prefix_eq tt_prefix_subset_refl tt_subset_imp_prefix_subset tt_subset_same_length)
  next
    show "\<rho>' \<subseteq>\<^sub>C \<rho>'' \<Longrightarrow> X \<subseteq> X' \<Longrightarrow> \<rho>'' @ [[X']\<^sub>R, [Tock]\<^sub>E] \<in> Q \<Longrightarrow> \<rho>' @ [[X]\<^sub>R, [Tock]\<^sub>E] \<in> Q"
      by (meson TT1_Q TT1_def tt_prefix_subset.simps(2) tt_prefix_subset_eq_length_common_prefix_eq tt_prefix_subset_refl tt_subset_imp_prefix_subset tt_subset_same_length)
  next
    show "\<rho>' \<subseteq>\<^sub>C \<rho>'' \<Longrightarrow> X \<subseteq> X' \<Longrightarrow> \<rho>'' @ [[X']\<^sub>R, [Tock]\<^sub>E] \<in> P \<Longrightarrow> \<rho>' @ [[X]\<^sub>R, [Tock]\<^sub>E] \<notin> P \<Longrightarrow> \<rho>' @ [[Tock]\<^sub>E] \<in> P"
      by (meson TT1_P TT1_def tt_prefix_subset.simps(2) tt_prefix_subset_eq_length_common_prefix_eq tt_prefix_subset_refl tt_subset_imp_prefix_subset tt_subset_same_length)
  next
    show "\<rho>' \<subseteq>\<^sub>C \<rho>'' \<Longrightarrow> X \<subseteq> X' \<Longrightarrow> \<rho>'' @ [[X']\<^sub>R, [Tock]\<^sub>E] \<in> P \<Longrightarrow> \<rho>' @ [[X]\<^sub>R, [Tock]\<^sub>E] \<notin> P \<Longrightarrow> \<rho>' @ [[Tock]\<^sub>E] \<in> Q"
      by (meson TT1_P TT1_def tt_prefix_subset.simps(2) tt_prefix_subset_eq_length_common_prefix_eq tt_prefix_subset_refl tt_subset_imp_prefix_subset tt_subset_same_length)
  next
    show "\<rho>' \<subseteq>\<^sub>C \<rho>'' \<Longrightarrow> X \<subseteq> X' \<Longrightarrow> \<rho>'' @ [[X']\<^sub>R, [Tock]\<^sub>E] \<in> Q \<Longrightarrow> \<rho>' @ [[X]\<^sub>R, [Tock]\<^sub>E] \<notin> Q \<Longrightarrow> \<rho>' @ [[Tock]\<^sub>E] \<in> P"
      by (meson TT1_Q TT1_def tt_prefix_subset.simps(2) tt_prefix_subset_eq_length_common_prefix_eq tt_prefix_subset_refl tt_subset_imp_prefix_subset tt_subset_same_length)
  next
    show "\<rho>' \<subseteq>\<^sub>C \<rho>'' \<Longrightarrow> X \<subseteq> X' \<Longrightarrow> \<rho>'' @ [[X']\<^sub>R, [Tock]\<^sub>E] \<in> Q \<Longrightarrow> \<rho>' @ [[X]\<^sub>R, [Tock]\<^sub>E] \<notin> Q \<Longrightarrow> \<rho>' @ [[Tock]\<^sub>E] \<in> Q"
      by (meson TT1_Q TT1_def tt_prefix_subset.simps(2) tt_prefix_subset_eq_length_common_prefix_eq tt_prefix_subset_refl tt_subset_imp_prefix_subset tt_subset_same_length)
  qed
  then have "Y \<inter> {e. e \<noteq> Tock \<and> \<rho>'' @ [[e]\<^sub>E] \<in> P \<and> \<rho>'' @ [[e]\<^sub>E] \<in> Q \<or> e = Tock \<and> \<rho>'' @ [[X']\<^sub>R, [e]\<^sub>E] \<in> P \<and> \<rho>'' @ [[X']\<^sub>R, [e]\<^sub>E] \<in> Q} = {}"
    using assm1 inf.order_iff by auto
  then have "\<rho>'' @ [X' \<union> Y]\<^sub>R # \<sigma>'' \<in> P \<and> \<rho>'' @ [X' \<union> Y]\<^sub>R # \<sigma>'' \<in> Q"
    by (simp add: \<sigma>_assms ind_hyp)
  also have "\<rho>' @ [X \<union> Y]\<^sub>R # \<sigma>' \<lesssim>\<^sub>C \<rho>'' @ [X' \<union> Y]\<^sub>R # \<sigma>''"
    using \<sigma>_assms apply auto
    by (metis (no_types, lifting) Un_commute sup.orderE sup_ge2 sup_left_commute tt_prefix_concat 
        tt_prefix_subset.simps(2) tt_prefix_subset_eq_length_common_prefix_eq tt_prefix_tt_prefix_subset_trans tt_subset_imp_prefix_subset tt_subset_same_length)
  then show "\<rho>' @ [X \<union> Y]\<^sub>R # \<sigma>' \<in> Q"
    using TT1_Q TT1_def calculation by blast
qed

lemma ttWFx_Supremum:
  assumes ttWFx_P: "ttWFx P" and ttWFx_Q: "ttWFx Q"
  shows "ttWFx (SupremumTT P Q)"
  using assms unfolding SupremumTT_def ttWFx_def by auto

lemma TT3w_Supremum:
  assumes TT3w_P: "TT3w P" and TT3w_Q: "TT3w Q"
  shows "TT3w (SupremumTT P Q)"
  using assms unfolding SupremumTT_def TT3w_def
proof auto
  fix \<rho> \<rho>' \<sigma> :: "'a ttobs list"
  fix X Y
  assume assm1: "add_Tick_refusal_trace \<rho> = \<rho>' @ [X]\<^sub>R # \<sigma>"
  assume assm2: "Y \<inter> {e. e \<noteq> Tock \<and> \<rho>' @ [[e]\<^sub>E] \<in> P \<and> \<rho>' @ [[e]\<^sub>E] \<in> Q \<or> e = Tock \<and> \<rho>' @ [[X]\<^sub>R, [e]\<^sub>E] \<in> P \<and> \<rho>' @ [[X]\<^sub>R, [e]\<^sub>E] \<in> Q} = {}"
  assume ind_hyp: "\<forall>\<rho>' \<sigma> X Y. \<rho> = \<rho>' @ [X]\<^sub>R # \<sigma>
    \<and> Y \<inter> {e. e \<noteq> Tock \<and> \<rho>' @ [[e]\<^sub>E] \<in> P \<and> \<rho>' @ [[e]\<^sub>E] \<in> Q \<or> e = Tock \<and> \<rho>' @ [[X]\<^sub>R, [e]\<^sub>E] \<in> P \<and> \<rho>' @ [[X]\<^sub>R, [e]\<^sub>E] \<in> Q} = {} \<longrightarrow>
      \<rho>' @ [X \<union> Y]\<^sub>R # \<sigma> \<in> P \<and> \<rho>' @ [X \<union> Y]\<^sub>R # \<sigma> \<in> Q"
  have "\<exists> \<rho>'' X' \<sigma>'. \<rho> = \<rho>'' @ [X']\<^sub>R # \<sigma>' \<and> add_Tick_refusal_trace \<rho>'' = \<rho>'"
    using assm1 apply (induct \<rho> \<rho>' rule:tt_subset.induct, auto)
    apply (metis Un_empty_right Un_insert_right add_Tick_refusal_trace.simps(3) append_Cons)
    apply (metis add_Tick_refusal_trace.simps(2) append_Cons)
    by (metis add_Tick_refusal_trace.elims append_Nil list.distinct(1) list.sel(1))
  then obtain \<rho>'' X' \<sigma>' where \<rho>_assms: "\<rho> = \<rho>'' @ [X']\<^sub>R # \<sigma>' \<and> add_Tick_refusal_trace \<rho>'' = \<rho>'"
    by auto
  then have "{e. e \<noteq> Tock \<and> \<rho>'' @ [[e]\<^sub>E] \<in> P \<and> \<rho>'' @ [[e]\<^sub>E] \<in> Q \<or> e = Tock \<and> \<rho>'' @ [[X']\<^sub>R, [e]\<^sub>E] \<in> P \<and> \<rho>'' @ [[X']\<^sub>R, [e]\<^sub>E] \<in> Q}
    \<subseteq> {e. e \<noteq> Tock \<and> \<rho>' @ [[e]\<^sub>E] \<in> P \<and> \<rho>' @ [[e]\<^sub>E] \<in> Q \<or> e = Tock \<and> \<rho>' @ [[X]\<^sub>R, [e]\<^sub>E] \<in> P \<and> \<rho>' @ [[X]\<^sub>R, [e]\<^sub>E] \<in> Q}"
    using assm2 apply (safe)
    apply (metis (mono_tags, lifting) TT3w_P TT3w_def add_Tick_refusal_trace_end_event)
    apply (metis (mono_tags, lifting) TT3w_Q TT3w_def add_Tick_refusal_trace_end_event)
    apply (metis (mono_tags, lifting) TT3w_P TT3w_def add_Tick_refusal_trace_end_event)
    apply (metis (mono_tags, lifting) TT3w_Q TT3w_def add_Tick_refusal_trace_end_event)
    apply (metis (mono_tags, lifting) TT3w_P TT3w_def add_Tick_refusal_trace_end_event)
    apply (metis (mono_tags, lifting) TT3w_Q TT3w_def add_Tick_refusal_trace_end_event)
    apply (smt TT3w_P TT3w_def add_Tick_refusal_trace.simps(1) add_Tick_refusal_trace.simps(2) add_Tick_refusal_trace.simps(3) add_Tick_refusal_trace_concat assm1 list.sel(1) same_append_eq)
    apply (smt TT3w_Q TT3w_def add_Tick_refusal_trace.simps(1) add_Tick_refusal_trace.simps(2) add_Tick_refusal_trace.simps(3) add_Tick_refusal_trace_concat assm1 list.sel(1) same_append_eq)
    apply (smt TT3w_P TT3w_def add_Tick_refusal_trace.simps(1) add_Tick_refusal_trace.simps(2) add_Tick_refusal_trace.simps(3) add_Tick_refusal_trace_concat assm1 list.sel(1) same_append_eq)
    apply (smt TT3w_P TT3w_def add_Tick_refusal_trace.simps(1) add_Tick_refusal_trace.simps(2) add_Tick_refusal_trace.simps(3) add_Tick_refusal_trace_concat assm1 list.sel(1) same_append_eq)
    apply (smt TT3w_Q TT3w_def add_Tick_refusal_trace.simps(1) add_Tick_refusal_trace.simps(2) add_Tick_refusal_trace.simps(3) add_Tick_refusal_trace_concat assm1 list.sel(1) same_append_eq)
    apply (smt TT3w_Q TT3w_def add_Tick_refusal_trace.simps(1) add_Tick_refusal_trace.simps(2) add_Tick_refusal_trace.simps(3) add_Tick_refusal_trace_concat assm1 list.sel(1) same_append_eq)
    done
  then have "Y \<inter> {e. e \<noteq> Tock \<and> \<rho>'' @ [[e]\<^sub>E] \<in> P \<and> \<rho>'' @ [[e]\<^sub>E] \<in> Q \<or> e = Tock \<and> \<rho>'' @ [[X']\<^sub>R, [e]\<^sub>E] \<in> P \<and> \<rho>'' @ [[X']\<^sub>R, [e]\<^sub>E] \<in> Q} = {}"
    using assm2 subsetCE by auto
  then have "\<rho>'' @ [X' \<union> Y]\<^sub>R # \<sigma>' \<in> P \<and> \<rho>'' @ [X' \<union> Y]\<^sub>R # \<sigma>' \<in> Q"
    using \<rho>_assms ind_hyp by blast
  then show "\<rho>' @ [X \<union> Y]\<^sub>R # \<sigma> \<in> P"
    by (smt TT3w_P TT3w_def Un_commute \<rho>_assms add_Tick_refusal_trace.simps(3) add_Tick_refusal_trace_concat append_eq_append_conv assm1 list.inject sup_assoc ttobs.inject(2))
next
  fix \<rho> \<rho>' \<sigma> :: "'a ttobs list"
  fix X Y
  assume assm1: "add_Tick_refusal_trace \<rho> = \<rho>' @ [X]\<^sub>R # \<sigma>"
  assume assm2: "Y \<inter> {e. e \<noteq> Tock \<and> \<rho>' @ [[e]\<^sub>E] \<in> P \<and> \<rho>' @ [[e]\<^sub>E] \<in> Q \<or> e = Tock \<and> \<rho>' @ [[X]\<^sub>R, [e]\<^sub>E] \<in> P \<and> \<rho>' @ [[X]\<^sub>R, [e]\<^sub>E] \<in> Q} = {}"
  assume ind_hyp: "\<forall>\<rho>' \<sigma> X Y. \<rho> = \<rho>' @ [X]\<^sub>R # \<sigma>
    \<and> Y \<inter> {e. e \<noteq> Tock \<and> \<rho>' @ [[e]\<^sub>E] \<in> P \<and> \<rho>' @ [[e]\<^sub>E] \<in> Q \<or> e = Tock \<and> \<rho>' @ [[X]\<^sub>R, [e]\<^sub>E] \<in> P \<and> \<rho>' @ [[X]\<^sub>R, [e]\<^sub>E] \<in> Q} = {} \<longrightarrow>
      \<rho>' @ [X \<union> Y]\<^sub>R # \<sigma> \<in> P \<and> \<rho>' @ [X \<union> Y]\<^sub>R # \<sigma> \<in> Q"
  have "\<exists> \<rho>'' X' \<sigma>'. \<rho> = \<rho>'' @ [X']\<^sub>R # \<sigma>' \<and> add_Tick_refusal_trace \<rho>'' = \<rho>'"
    using assm1 apply (induct \<rho> \<rho>' rule:tt_subset.induct, auto)
    apply (metis Un_empty_right Un_insert_right add_Tick_refusal_trace.simps(3) append_Cons)
    apply (metis add_Tick_refusal_trace.simps(2) append_Cons)
    by (metis add_Tick_refusal_trace.elims append_Nil list.distinct(1) list.sel(1))
  then obtain \<rho>'' X' \<sigma>' where \<rho>_assms: "\<rho> = \<rho>'' @ [X']\<^sub>R # \<sigma>' \<and> add_Tick_refusal_trace \<rho>'' = \<rho>'"
    by auto
  then have "{e. e \<noteq> Tock \<and> \<rho>'' @ [[e]\<^sub>E] \<in> P \<and> \<rho>'' @ [[e]\<^sub>E] \<in> Q \<or> e = Tock \<and> \<rho>'' @ [[X']\<^sub>R, [e]\<^sub>E] \<in> P \<and> \<rho>'' @ [[X']\<^sub>R, [e]\<^sub>E] \<in> Q}
    \<subseteq> {e. e \<noteq> Tock \<and> \<rho>' @ [[e]\<^sub>E] \<in> P \<and> \<rho>' @ [[e]\<^sub>E] \<in> Q \<or> e = Tock \<and> \<rho>' @ [[X]\<^sub>R, [e]\<^sub>E] \<in> P \<and> \<rho>' @ [[X]\<^sub>R, [e]\<^sub>E] \<in> Q}"
    using assm2 apply (safe)
    apply (metis (mono_tags, lifting) TT3w_P TT3w_def add_Tick_refusal_trace_end_event)
    apply (metis (mono_tags, lifting) TT3w_Q TT3w_def add_Tick_refusal_trace_end_event)
    apply (metis (mono_tags, lifting) TT3w_P TT3w_def add_Tick_refusal_trace_end_event)
    apply (metis (mono_tags, lifting) TT3w_Q TT3w_def add_Tick_refusal_trace_end_event)
    apply (metis (mono_tags, lifting) TT3w_P TT3w_def add_Tick_refusal_trace_end_event)
    apply (metis (mono_tags, lifting) TT3w_Q TT3w_def add_Tick_refusal_trace_end_event)
    apply (smt TT3w_P TT3w_def add_Tick_refusal_trace.simps(1) add_Tick_refusal_trace.simps(2) add_Tick_refusal_trace.simps(3) add_Tick_refusal_trace_concat assm1 list.sel(1) same_append_eq)
    apply (smt TT3w_Q TT3w_def add_Tick_refusal_trace.simps(1) add_Tick_refusal_trace.simps(2) add_Tick_refusal_trace.simps(3) add_Tick_refusal_trace_concat assm1 list.sel(1) same_append_eq)
    apply (smt TT3w_P TT3w_def add_Tick_refusal_trace.simps(1) add_Tick_refusal_trace.simps(2) add_Tick_refusal_trace.simps(3) add_Tick_refusal_trace_concat assm1 list.sel(1) same_append_eq)
    apply (smt TT3w_P TT3w_def add_Tick_refusal_trace.simps(1) add_Tick_refusal_trace.simps(2) add_Tick_refusal_trace.simps(3) add_Tick_refusal_trace_concat assm1 list.sel(1) same_append_eq)
    apply (smt TT3w_Q TT3w_def add_Tick_refusal_trace.simps(1) add_Tick_refusal_trace.simps(2) add_Tick_refusal_trace.simps(3) add_Tick_refusal_trace_concat assm1 list.sel(1) same_append_eq)
    apply (smt TT3w_Q TT3w_def add_Tick_refusal_trace.simps(1) add_Tick_refusal_trace.simps(2) add_Tick_refusal_trace.simps(3) add_Tick_refusal_trace_concat assm1 list.sel(1) same_append_eq)
    done
  then have "Y \<inter> {e. e \<noteq> Tock \<and> \<rho>'' @ [[e]\<^sub>E] \<in> P \<and> \<rho>'' @ [[e]\<^sub>E] \<in> Q \<or> e = Tock \<and> \<rho>'' @ [[X']\<^sub>R, [e]\<^sub>E] \<in> P \<and> \<rho>'' @ [[X']\<^sub>R, [e]\<^sub>E] \<in> Q} = {}"
    using assm2 subsetCE by auto
  then have "\<rho>'' @ [X' \<union> Y]\<^sub>R # \<sigma>' \<in> P \<and> \<rho>'' @ [X' \<union> Y]\<^sub>R # \<sigma>' \<in> Q"
    using \<rho>_assms ind_hyp by blast
  then show "\<rho>' @ [X \<union> Y]\<^sub>R # \<sigma> \<in> Q"
    by (smt TT3w_Q TT3w_def Un_commute \<rho>_assms add_Tick_refusal_trace.simps(3) add_Tick_refusal_trace_concat append_eq_append_conv assm1 list.inject sup_assoc ttobs.inject(2))
qed

lemma Supremum_upper_bound1:
  "P \<sqsubseteq>\<^sub>C SupremumTT P Q"
  unfolding RefinesTT_def SupremumTT_def by auto

lemma Supremum_upper_bound2:
  "Q \<sqsubseteq>\<^sub>C SupremumTT P Q"
  unfolding RefinesTT_def SupremumTT_def by auto

lemma Supremum_least_upper_bound:
  assumes "P \<sqsubseteq>\<^sub>C R" "Q \<sqsubseteq>\<^sub>C R" "TT2 R"
  shows "SupremumTT P Q \<sqsubseteq>\<^sub>C R"
  using assms unfolding RefinesTT_def SupremumTT_def
proof auto
  fix \<rho> \<sigma> X Y
  assume assm1: "\<rho> @ [X]\<^sub>R # \<sigma> \<in> R"
  assume assm2: "Y \<inter> {e. e \<noteq> Tock \<and> \<rho> @ [[e]\<^sub>E] \<in> P \<and> \<rho> @ [[e]\<^sub>E] \<in> Q \<or> e = Tock \<and> \<rho> @ [[X]\<^sub>R, [e]\<^sub>E] \<in> P \<and> \<rho> @ [[X]\<^sub>R, [e]\<^sub>E] \<in> Q} = {}"
  assume assm3: " R \<subseteq> P"
  assume assm4: " R \<subseteq> Q"
  have "{e. e \<noteq> Tock \<and> \<rho> @ [[e]\<^sub>E] \<in> R \<or> e = Tock \<and> \<rho> @ [[X]\<^sub>R, [e]\<^sub>E] \<in> R}
    \<subseteq> {e. e \<noteq> Tock \<and> \<rho> @ [[e]\<^sub>E] \<in> P \<and> \<rho> @ [[e]\<^sub>E] \<in> Q \<or> e = Tock \<and> \<rho> @ [[X]\<^sub>R, [e]\<^sub>E] \<in> P \<and> \<rho> @ [[X]\<^sub>R, [e]\<^sub>E] \<in> Q}"
    using assm3 assm4 by auto
  then have "Y \<inter> {e. e \<noteq> Tock \<and> \<rho> @ [[e]\<^sub>E] \<in> R \<or> e = Tock \<and> \<rho> @ [[X]\<^sub>R, [e]\<^sub>E] \<in> R} = {}"
    using assm2 by auto
  then have "\<rho> @ [X \<union> Y]\<^sub>R # \<sigma> \<in> R"
    using TT2_aux1 assm1 assms(3) by fastforce
  then show "\<rho> @ [X \<union> Y]\<^sub>R # \<sigma> \<in> P"
    using assm3 by blast
next
  fix \<rho> \<sigma> X Y
  assume assm1: "\<rho> @ [X]\<^sub>R # \<sigma> \<in> R"
  assume assm2: "Y \<inter> {e. e \<noteq> Tock \<and> \<rho> @ [[e]\<^sub>E] \<in> P \<and> \<rho> @ [[e]\<^sub>E] \<in> Q \<or> e = Tock \<and> \<rho> @ [[X]\<^sub>R, [e]\<^sub>E] \<in> P \<and> \<rho> @ [[X]\<^sub>R, [e]\<^sub>E] \<in> Q} = {}"
  assume assm3: " R \<subseteq> P"
  assume assm4: " R \<subseteq> Q"
  have "{e. e \<noteq> Tock \<and> \<rho> @ [[e]\<^sub>E] \<in> R \<or> e = Tock \<and> \<rho> @ [[X]\<^sub>R, [e]\<^sub>E] \<in> R}
    \<subseteq> {e. e \<noteq> Tock \<and> \<rho> @ [[e]\<^sub>E] \<in> P \<and> \<rho> @ [[e]\<^sub>E] \<in> Q \<or> e = Tock \<and> \<rho> @ [[X]\<^sub>R, [e]\<^sub>E] \<in> P \<and> \<rho> @ [[X]\<^sub>R, [e]\<^sub>E] \<in> Q}"
    using assm3 assm4 by auto
  then have "Y \<inter> {e. e \<noteq> Tock \<and> \<rho> @ [[e]\<^sub>E] \<in> R \<or> e = Tock \<and> \<rho> @ [[X]\<^sub>R, [e]\<^sub>E] \<in> R} = {}"
    using assm2 by auto
  then have "\<rho> @ [X \<union> Y]\<^sub>R # \<sigma> \<in> R"
    using TT2_aux1 assm1 assms(3) by fastforce
  then show "\<rho> @ [X \<union> Y]\<^sub>R # \<sigma> \<in> Q"
    using assm4 by blast
qed

lemma Supremum_idempotent:
  assumes "TT2 P"
  shows "SupremumTT P P = P"
  using assms unfolding SupremumTT_def TT2_def by auto

end