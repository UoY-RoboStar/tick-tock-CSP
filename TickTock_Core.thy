theory TickTock_Core
  imports Main
begin

section {* Types and Wellformedness Conditions *}

datatype 'e cttevent = Event 'e  | Tock | Tick
datatype 'e cttobs = ObsEvent "'e cttevent" ("[_]\<^sub>E") | Ref "'e cttevent set" ("[_]\<^sub>R") (*| TockRef "'e cttevent set" ("[_]\<^sub>T")*)

fun ttWF :: "'e cttobs list \<Rightarrow> bool" where
  "ttWF [] = True" | (* an empty trace is okay*)
  "ttWF [[X]\<^sub>R] = True" | (* a refusal at the end of a trace is okay *)
  "ttWF [[Tick]\<^sub>E] = True" | (* a tick at the end of a trace is okay *)
  "ttWF ([Event e]\<^sub>E # \<sigma>) = ttWF \<sigma>" | (* a (non-tick, non-tock) event is okay *)
  "ttWF ([X]\<^sub>R # [Tock]\<^sub>E # \<sigma>) = ttWF \<sigma>" | (* a tock event on its own is okay *)
  "ttWF \<sigma> = False" (* everything else is not allowed *)  

(* not necessary as a function but very useful for its induction rule *)
function ttWF2 :: "'e cttobs list \<Rightarrow> 'e cttobs list \<Rightarrow> bool" where
  "ttWF2 [] [] = True" | 
  "ttWF2 [] [[Y]\<^sub>R] = True" | 
  "ttWF2 [] [[Tick]\<^sub>E] = True" | 
  "ttWF2 [] ([Event f]\<^sub>E # \<sigma>) = ttWF2 [] \<sigma>" | 
  "ttWF2 [] ([Y]\<^sub>R # [Tock]\<^sub>E # \<sigma>) = ttWF2 [] \<sigma>" | 
  "ttWF2 [[X]\<^sub>R] [] = True" | 
  "ttWF2 [[X]\<^sub>R] [[Y]\<^sub>R] = True" | 
  "ttWF2 [[X]\<^sub>R] [[Tick]\<^sub>E] = True" | 
  "ttWF2 [[X]\<^sub>R] ([Event f]\<^sub>E # \<sigma>) = ttWF2 [] \<sigma>" | 
  "ttWF2 [[X]\<^sub>R] ([Y]\<^sub>R # [Tock]\<^sub>E # \<sigma>) = ttWF2 [] \<sigma>" | 
  "ttWF2 [[Tick]\<^sub>E] [] = True" | 
  "ttWF2 [[Tick]\<^sub>E] [[Y]\<^sub>R] = True" | 
  "ttWF2 [[Tick]\<^sub>E] [[Tick]\<^sub>E] = True" | 
  "ttWF2 [[Tick]\<^sub>E] ([Event f]\<^sub>E # \<sigma>) = ttWF2 [] \<sigma>" | 
  "ttWF2 [[Tick]\<^sub>E] ([Y]\<^sub>R # [Tock]\<^sub>E # \<sigma>) = ttWF2 [] \<sigma>" | 
  "ttWF2 ([Event e]\<^sub>E # \<sigma>) [] = ttWF2 \<sigma> []" | 
  "ttWF2 ([Event e]\<^sub>E # \<sigma>) [[Y]\<^sub>R] = ttWF2 \<sigma> []" | 
  "ttWF2 ([Event e]\<^sub>E # \<sigma>) [[Tick]\<^sub>E] = ttWF2 \<sigma> []" | 
  "ttWF2 ([Event e]\<^sub>E # \<rho>) ([Event f]\<^sub>E # \<sigma>) = ttWF2 \<rho> \<sigma>" | 
  "ttWF2 ([Event e]\<^sub>E # \<rho>) ([Y]\<^sub>R # [Tock]\<^sub>E # \<sigma>) = ttWF2 \<rho> \<sigma>" | 
  "ttWF2 ([X]\<^sub>R # [Tock]\<^sub>E # \<sigma>) [] = ttWF2 \<sigma> []" | 
  "ttWF2 ([X]\<^sub>R # [Tock]\<^sub>E # \<sigma>) [[Y]\<^sub>R] = ttWF2 \<sigma> []" | 
  "ttWF2 ([X]\<^sub>R # [Tock]\<^sub>E # \<sigma>) [[Tick]\<^sub>E] = ttWF2 \<sigma> []" | 
  "ttWF2 ([X]\<^sub>R # [Tock]\<^sub>E # \<rho>) ([Event f]\<^sub>E # \<sigma>) = ttWF2 \<rho> \<sigma>" | 
  "ttWF2 ([X]\<^sub>R # [Tock]\<^sub>E # \<rho>) ([Y]\<^sub>R # [Tock]\<^sub>E # \<sigma>) = ttWF2 \<rho> \<sigma>" |
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

print_theorems

lemma ttWF2_ttWF: "ttWF2 x y = (ttWF x \<and> ttWF y)"
  by (induct rule:ttWF2.induct, auto)

section {* Prefix Relations *}

subsection {* Prefix *}

fun ctt_prefix :: "'e cttobs list \<Rightarrow> 'e cttobs list \<Rightarrow> bool" (infix "\<le>\<^sub>C" 50) where
  "ctt_prefix [] x = True" |
  "ctt_prefix (x # xa) (y # ya) = (x = y \<and> ctt_prefix xa ya)" |
  "ctt_prefix (x # xa) [] = False"

lemma ctt_prefix_refl: "x \<le>\<^sub>C x"
  by (induct x, auto)

lemma ctt_prefix_trans: "x \<le>\<^sub>C y \<Longrightarrow> y \<le>\<^sub>C z \<Longrightarrow> x \<le>\<^sub>C z"
proof -
  have "\<exists> y. x \<le>\<^sub>C y \<and> y \<le>\<^sub>C z \<Longrightarrow> x \<le>\<^sub>C z"
    apply (induct rule:ctt_prefix.induct, auto)
    apply (metis ctt_prefix.elims(2) list.discI list.sel(1))
    apply (metis ctt_prefix.elims(2) list.discI list.sel(3))
    using ctt_prefix.elims(2) by force
  then show "x \<le>\<^sub>C y \<Longrightarrow> y \<le>\<^sub>C z \<Longrightarrow> x \<le>\<^sub>C z" by auto
qed

lemma ctt_prefix_antisym: "x \<le>\<^sub>C y \<Longrightarrow> y \<le>\<^sub>C x \<Longrightarrow> x = y"
  using ctt_prefix.elims(2) by (induct rule:ctt_prefix.induct, auto)

lemma ctt_prefix_concat: "x \<le>\<^sub>C x @ y"
  by (induct x, auto)

lemma ctt_prefix_same_front: "(x @ y \<le>\<^sub>C x @ z) = (y \<le>\<^sub>C z)"
  by (induct x, auto)

lemma ctt_prefix_append_split: "t \<le>\<^sub>C r @ s \<Longrightarrow> t \<le>\<^sub>C r \<or> (\<exists> t'. t = r @ t' \<and> t' \<le>\<^sub>C s)"
  by (induct t r rule:ctt_prefix.induct, auto)

lemma ctt_prefix_split: "t \<le>\<^sub>C s \<Longrightarrow> \<exists> r. s = t @ r"
  by (induct t s rule:ctt_prefix.induct, auto)

lemma self_extension_ctt_prefix: 
  "y \<noteq> [] \<Longrightarrow> x @ y \<le>\<^sub>C x \<Longrightarrow> False"
  apply (induct x, auto)
  using ctt_prefix.elims(2) by blast

lemma ctt_prefix_notfront_is_whole:
  "t \<le>\<^sub>C s @ [x] \<Longrightarrow> \<not> t \<le>\<^sub>C s \<Longrightarrow> t = s @ [x]"
  by (induct t s rule:ctt_prefix.induct, auto simp add: ctt_prefix_antisym)

lemma event_refusal_split: "s1 @ [X]\<^sub>R # s2 = t1 @ [e]\<^sub>E # t2 \<Longrightarrow>
  (\<exists>t2'. s1 = t1 @ [e]\<^sub>E # t2' \<and> t2' \<le>\<^sub>C t2) \<or> (\<exists> s2'. t1 = s1 @ [X]\<^sub>R # s2' \<and> s2' \<le>\<^sub>C s2)"
  by (induct t1 s1 rule:ctt_prefix.induct, auto simp add: ctt_prefix_concat, metis append_eq_Cons_conv ctt_prefix_concat cttobs.distinct(1) list.inject)

subsection {* Subset *}

fun ctt_subset :: "'e cttobs list \<Rightarrow> 'e cttobs list \<Rightarrow> bool" (infix "\<subseteq>\<^sub>C" 50) where
  "ctt_subset [] [] = True" |
  "ctt_subset ([X]\<^sub>R # xa) ([Y]\<^sub>R # ya) = (X \<subseteq> Y \<and> ctt_subset xa ya)" |
  "ctt_subset ([x]\<^sub>E # xa) ([y]\<^sub>E # ya) = (x = y \<and> ctt_subset xa ya)" |
  "ctt_subset x y = False"

lemma ctt_subset_refl: "x \<subseteq>\<^sub>C x"
  by (induct x, auto, case_tac a, auto)

lemma ctt_subset_trans: "x \<subseteq>\<^sub>C y \<Longrightarrow> y \<subseteq>\<^sub>C z \<Longrightarrow> x \<subseteq>\<^sub>C z"
proof -
  have "\<exists> y. x \<subseteq>\<^sub>C y \<and> y \<subseteq>\<^sub>C z \<Longrightarrow> x \<subseteq>\<^sub>C z"
    apply (induct rule:ctt_subset.induct, auto)
    apply (case_tac y, auto, case_tac a, auto)
    apply (case_tac y, auto, case_tac a, auto)
    apply (case_tac yb, auto, case_tac a, auto)
    apply (case_tac yb, auto, case_tac a, auto)
    apply (case_tac y, auto, case_tac y, auto, case_tac a, auto)+
    done  
  then show "x \<subseteq>\<^sub>C y \<Longrightarrow> y \<subseteq>\<^sub>C z \<Longrightarrow> x \<subseteq>\<^sub>C z"
    by auto
qed

lemma ctt_subset_antisym: "x \<subseteq>\<^sub>C y \<Longrightarrow> y \<subseteq>\<^sub>C x \<Longrightarrow> x = y"
  by (induct rule:ctt_subset.induct, auto)

lemma ctt_subset_same_length:
  "\<rho> \<subseteq>\<^sub>C \<sigma> \<Longrightarrow> length \<rho> = length \<sigma>"
  by (induct rule:ctt_subset.induct, auto)

lemma ctt_prefix_ctt_subset: "\<sigma>' \<le>\<^sub>C \<sigma> \<Longrightarrow> \<rho> \<subseteq>\<^sub>C \<sigma> \<Longrightarrow> \<exists> \<rho>'. \<rho>' \<subseteq>\<^sub>C \<sigma>' \<and> \<rho>' \<le>\<^sub>C \<rho>"
proof -
  have "\<And> \<sigma>'. \<sigma>' \<le>\<^sub>C \<sigma> \<Longrightarrow> \<rho> \<subseteq>\<^sub>C \<sigma> \<Longrightarrow> \<exists> \<rho>'. \<rho>' \<subseteq>\<^sub>C \<sigma>' \<and> \<rho>' \<le>\<^sub>C \<rho>"
  proof (induct \<rho> \<sigma> rule:ctt_subset.induct, auto)
    fix \<sigma>'
    show "\<sigma>' \<le>\<^sub>C [] \<Longrightarrow> \<exists>\<rho>'. \<rho>' \<subseteq>\<^sub>C \<sigma>' \<and> \<rho>' \<le>\<^sub>C []"
      using ctt_subset_refl by blast
  next
    fix X xa Y ya \<sigma>'
    assume assm1: "\<sigma>' \<le>\<^sub>C [Y]\<^sub>R # ya"
    assume assm2: "(\<And>\<sigma>'. \<sigma>' \<le>\<^sub>C ya \<Longrightarrow> \<exists>\<rho>'. \<rho>' \<subseteq>\<^sub>C \<sigma>' \<and> \<rho>' \<le>\<^sub>C xa)"
    assume assm3: "X \<subseteq> Y"
    from assm1 have "\<sigma>' \<le>\<^sub>C [[Y]\<^sub>R] @ ya"
      by simp
    then have "\<sigma>' \<le>\<^sub>C [[Y]\<^sub>R]  \<or> (\<exists>t'. \<sigma>' = [[Y]\<^sub>R] @ t' \<and> t' \<le>\<^sub>C ya)"
      using ctt_prefix_append_split by blast
    then have "\<sigma>' \<le>\<^sub>C [[Y]\<^sub>R]  \<or> (\<exists>t'. \<sigma>' = [Y]\<^sub>R # t' \<and> t' \<le>\<^sub>C ya)"
      by simp
    then obtain za where "\<sigma>' = [] \<or> (\<sigma>' = [Y]\<^sub>R # za \<and> za \<le>\<^sub>C ya)"
      by (metis (full_types) assm1 ctt_prefix.simps(2) list.exhaust)
    then show "\<exists>\<rho>'. \<rho>' \<subseteq>\<^sub>C \<sigma>' \<and> \<rho>' \<le>\<^sub>C [X]\<^sub>R # xa"
    proof auto
      show "\<sigma>' = [] \<Longrightarrow> \<exists>\<rho>'. \<rho>' \<subseteq>\<^sub>C [] \<and> \<rho>' \<le>\<^sub>C [X]\<^sub>R # xa"
        using ctt_prefix.simps(1) ctt_subset.simps(1) by blast
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
      using ctt_prefix_append_split by blast
    then have "\<sigma>' \<le>\<^sub>C [[y]\<^sub>E]  \<or> (\<exists>t'. \<sigma>' = [y]\<^sub>E # t' \<and> t' \<le>\<^sub>C ya)"
      by simp
    then obtain za where "\<sigma>' = [] \<or> (\<sigma>' = [y]\<^sub>E # za \<and> za \<le>\<^sub>C ya)"
      by (metis (full_types) assm1 ctt_prefix.simps(2) list.exhaust)
    then show "\<exists>\<rho>'. \<rho>' \<subseteq>\<^sub>C \<sigma>' \<and> \<rho>' \<le>\<^sub>C [y]\<^sub>E # xa"
    proof auto
      show "\<sigma>' = [] \<Longrightarrow> \<exists>\<rho>'. \<rho>' \<subseteq>\<^sub>C [] \<and> \<rho>' \<le>\<^sub>C [y]\<^sub>E # xa"
        using ctt_prefix.simps(1) ctt_subset.simps(1) by blast
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

lemma ctt_subset_combine:
  "\<rho>' \<subseteq>\<^sub>C \<rho> \<Longrightarrow> \<sigma>' \<subseteq>\<^sub>C \<sigma> \<Longrightarrow> \<rho>' @ \<sigma>' \<subseteq>\<^sub>C \<rho> @ \<sigma>"
  by (induct \<rho>' \<rho> rule:ctt_subset.induct, auto)

lemma ctt_subset_end_event:
  "s' \<subseteq>\<^sub>C s \<Longrightarrow> s' @ [[e]\<^sub>E] \<subseteq>\<^sub>C s @ [[e]\<^sub>E]"
  by (induct s' s rule:ctt_subset.induct, auto)   

lemma ctt_subset_split: "r \<subseteq>\<^sub>C s @ t \<Longrightarrow> \<exists> s' t'. r = s' @ t' \<and> s' \<subseteq>\<^sub>C s \<and> t' \<subseteq>\<^sub>C t"
  apply (induct r s rule:ctt_subset.induct, auto)
  apply (meson Cons_eq_appendI ctt_subset.simps(2))
  apply (meson Cons_eq_appendI ctt_subset.simps(3))
  using ctt_subset.simps(1) by blast+

lemma ctt_subset_split2: "r @ s \<subseteq>\<^sub>C t \<Longrightarrow> \<exists> r' s'. t =  r' @  s' \<and> r \<subseteq>\<^sub>C r' \<and> s \<subseteq>\<^sub>C s'"
  apply (induct r t rule:ctt_subset.induct, auto)
  apply (metis append_Cons ctt_subset.simps(2))
  apply (metis append_Cons ctt_subset.simps(3))
  using ctt_subset.simps(1) by blast+
  

subsection {* Prefix and Subset *}

fun ctt_prefix_subset :: "'e cttobs list \<Rightarrow> 'e cttobs list \<Rightarrow> bool" (infix "\<lesssim>\<^sub>C" 50) where
  "ctt_prefix_subset [] x = True" |
  "ctt_prefix_subset ([X]\<^sub>R # xa) ([Y]\<^sub>R # ya) = (X \<subseteq> Y \<and> ctt_prefix_subset xa ya)" |
  "ctt_prefix_subset ([x]\<^sub>E # xa) ([y]\<^sub>E # ya) = (x = y \<and> ctt_prefix_subset xa ya)" |
  "ctt_prefix_subset (x # xa) (y # ya) = False" |
  "ctt_prefix_subset (x # xa) [] = False"

lemma ctt_prefix_subset_refl: "x \<lesssim>\<^sub>C x"
  by (induct x, auto, case_tac a, auto)

lemma ctt_prefix_subset_trans: "x \<lesssim>\<^sub>C y \<Longrightarrow> y \<lesssim>\<^sub>C z \<Longrightarrow> x \<lesssim>\<^sub>C z"
proof -
  have "\<exists> y. x \<lesssim>\<^sub>C y \<and> y \<lesssim>\<^sub>C z \<Longrightarrow> x \<lesssim>\<^sub>C z"
    apply (induct rule:ctt_prefix_subset.induct, auto)
    apply (case_tac y, auto, case_tac a, auto)
    apply (case_tac y, auto, case_tac a, auto)
    apply (case_tac yb, auto, case_tac a, auto)
    apply (case_tac yb, auto, case_tac a, auto)
    apply (case_tac y, auto, case_tac a, auto)+
    by (metis ctt_prefix_subset.simps(6) neq_Nil_conv)
  then show "x \<lesssim>\<^sub>C y \<Longrightarrow> y \<lesssim>\<^sub>C z \<Longrightarrow> x \<lesssim>\<^sub>C z" by auto
qed

lemma ctt_prefix_subset_antisym: "x \<lesssim>\<^sub>C y \<Longrightarrow> y \<lesssim>\<^sub>C x \<Longrightarrow> x = y"
  using ctt_prefix_subset.elims(2) by (induct rule:ctt_prefix_subset.induct, auto)

lemma ctt_prefix_imp_prefix_subset: "x \<le>\<^sub>C y \<Longrightarrow> x \<lesssim>\<^sub>C y"
  by (induct rule:ctt_prefix_subset.induct, auto)

lemma ctt_subset_imp_prefix_subset: "x \<subseteq>\<^sub>C y \<Longrightarrow> x \<lesssim>\<^sub>C y"
  by (induct rule:ctt_prefix_subset.induct, auto)

lemma ctt_prefix_subset_imp_ctt_prefix_ctt_subset: "x \<lesssim>\<^sub>C y \<Longrightarrow> \<exists> z. x \<le>\<^sub>C z \<and> z \<subseteq>\<^sub>C y"
  apply (induct rule:ctt_prefix_subset.induct, auto)
  using ctt_subset_refl apply blast
  apply (rule_tac x="[X]\<^sub>R # z" in exI, auto)
  apply (rule_tac x="[y]\<^sub>E # z" in exI, auto)
  done

lemma ctt_prefix_subset_imp_ctt_subset_ctt_prefix: "x \<lesssim>\<^sub>C y \<Longrightarrow> \<exists> z. x \<subseteq>\<^sub>C z \<and> z \<le>\<^sub>C y"
  apply (induct rule:ctt_prefix_subset.induct, auto)
  apply (rule_tac x="[]" in exI, auto)
  apply (rule_tac x="[Y]\<^sub>R # z" in exI, auto)
  apply (rule_tac x="[y]\<^sub>E # z" in exI, auto)
  done

lemma ctt_prefix_ctt_prefix_subset_trans: "x \<le>\<^sub>C y \<Longrightarrow> y \<lesssim>\<^sub>C z \<Longrightarrow> x \<lesssim>\<^sub>C z"
  using ctt_prefix_imp_prefix_subset ctt_prefix_subset_trans by blast
 
lemma ctt_prefix_subset_ctt_prefix_trans: "x \<lesssim>\<^sub>C y \<Longrightarrow> y \<le>\<^sub>C z \<Longrightarrow> x \<lesssim>\<^sub>C z"
  using ctt_prefix_imp_prefix_subset ctt_prefix_subset_trans by blast

lemma ctt_prefix_decompose: "x \<le>\<^sub>C y \<Longrightarrow> \<exists> z. y = x @ z"
  apply (induct rule:ctt_prefix.induct, auto)
  using ctt_prefix.elims(2) by auto

lemma ctt_prefix_subset_ttWF: "ttWF s \<Longrightarrow> t \<lesssim>\<^sub>C s \<Longrightarrow> ttWF t"
  by (induct rule:ttWF2.induct, auto, (case_tac \<rho> rule:ttWF.cases, auto)+)

lemma ctt_prefix_subset_length: "t \<lesssim>\<^sub>C s \<Longrightarrow> length t \<le> length s"
  by (induct rule:ctt_prefix_subset.induct, auto)

lemma ctt_prefix_subset_Tock_filter_length: "t \<lesssim>\<^sub>C s \<Longrightarrow> length (filter (\<lambda> x. x = [Tock]\<^sub>E) t) \<le> length (filter (\<lambda> x. x = [Tock]\<^sub>E) s)"
  by (induct t s rule:ctt_prefix_subset.induct, auto)

lemma ctt_prefix_subset_append_split: "t \<lesssim>\<^sub>C r @ s \<Longrightarrow>
  \<exists> r' s'. t = r' @ s' \<and> r' \<lesssim>\<^sub>C r \<and> s' \<lesssim>\<^sub>C s \<and> ((length r' = length r \<and> length (filter (\<lambda> x. x = [Tock]\<^sub>E) r') = length (filter (\<lambda> x. x = [Tock]\<^sub>E) r)) \<or> s' = [])"
  apply (induct t "r" rule:ctt_prefix_subset.induct, auto)
  apply (metis (mono_tags) append_Cons ctt_prefix_subset.simps(2) cttobs.distinct(1) filter.simps(2) length_Cons, force)
  apply (metis (mono_tags, lifting) append_Cons ctt_prefix_subset.simps(3) filter.simps(2) length_Cons)
  apply (metis (mono_tags, lifting) append_Cons ctt_prefix_subset.simps(3) filter.simps(2) length_Cons, force+)
  done

lemma ctt_prefix_subset_append_split_Tock_filter: "t \<lesssim>\<^sub>C r @ s \<Longrightarrow> \<exists> r' s'. t = r' @ s' \<and> r' \<lesssim>\<^sub>C r \<and> s' \<lesssim>\<^sub>C s \<and> (length r' = length r \<or> s' = [])"
  apply (induct t "r" rule:ctt_prefix_subset.induct, auto)
  apply (metis append_Cons ctt_prefix_subset.simps(2) length_Cons, force)
  apply (metis append_Cons ctt_prefix_subset.simps(3) length_Cons, force)
  using ctt_prefix_subset_refl by blast

lemma init_refusal_ctt_prefix_subset: "[X]\<^sub>R # \<rho> \<lesssim>\<^sub>C [Y]\<^sub>R # \<sigma> \<Longrightarrow> \<rho> \<lesssim>\<^sub>C \<sigma>"
  by (induct \<rho> \<sigma> rule:ctt_prefix_subset.induct, auto)

lemma init_event_ctt_prefix_subset: "[e]\<^sub>E # \<rho> \<lesssim>\<^sub>C [f]\<^sub>E # \<sigma> \<Longrightarrow> \<rho> \<lesssim>\<^sub>C \<sigma>"
  by (induct \<rho> \<sigma> rule:ctt_prefix_subset.induct, auto)

lemma ctt_prefix_subset_front: "s @ t \<lesssim>\<^sub>C \<sigma> \<Longrightarrow> s \<lesssim>\<^sub>C \<sigma>"
  by (induct s \<sigma> rule:ctt_prefix_subset.induct, auto)

lemma ctt_prefix_subset_lift: "\<rho> \<lesssim>\<^sub>C \<sigma> \<Longrightarrow> \<exists> \<rho>'. \<rho>' \<le>\<^sub>C \<sigma> \<and> \<rho> \<lesssim>\<^sub>C \<rho>'"
  apply (induct \<rho> \<sigma> rule:ctt_prefix_subset.induct, auto)
  using ctt_prefix.simps(1) apply blast
  using ctt_prefix_refl ctt_prefix_subset.simps(2) apply blast
  using ctt_prefix_refl ctt_prefix_subset.simps(3) by blast

lemma ctt_prefix_subset_same_front: "s \<lesssim>\<^sub>C t = (r @ s \<lesssim>\<^sub>C r @ t)"
  by (induct r, auto, (case_tac a, auto)+)

lemma ctt_prefix_subset_concat: "r \<lesssim>\<^sub>C s @ t \<Longrightarrow> r \<lesssim>\<^sub>C s \<or> (\<exists> t'. t' \<lesssim>\<^sub>C t \<and> r \<subseteq>\<^sub>C s @ t')"
  by (induct r s rule:ctt_prefix_subset.induct, auto, rule_tac x="x # xa" in exI, auto simp add: ctt_subset_refl)

lemma ctt_prefix_subset_concat2: "r \<lesssim>\<^sub>C s @ t \<Longrightarrow> r \<lesssim>\<^sub>C s \<or> (\<exists> t' s'. s' \<subseteq>\<^sub>C s \<and> t' \<lesssim>\<^sub>C t \<and> r = s' @ t')"
  apply (induct r s rule:ctt_prefix_subset.induct, auto)
  apply (erule_tac x="t'" in allE, auto, erule_tac x="[X]\<^sub>R # s'" in allE, auto)
  apply (erule_tac x="t'" in allE, auto, erule_tac x="[y]\<^sub>E # s'" in allE, auto)
  apply (rule_tac x="x # xa" in exI, auto simp add: ctt_subset_refl)
  done

lemma ttWF_prefix_is_ttWF: "ttWF (s @ t) \<Longrightarrow> ttWF s"
  using ctt_prefix_concat ctt_prefix_imp_prefix_subset ctt_prefix_subset_ttWF by blast

lemma ttWF_end_refusal_prefix_subset: "ttWF (s @ [[X]\<^sub>R]) \<Longrightarrow> t \<lesssim>\<^sub>C s @ [[X]\<^sub>R] \<Longrightarrow> 
  (\<exists> r Y. t = r @ [[Y]\<^sub>R]) \<or> (\<exists> r Y. t = r @ [[Y]\<^sub>R, [Tock]\<^sub>E]) \<or> (\<exists> r e. t = r @ [[Event e]\<^sub>E]) \<or> t = []"
  apply (induct s t rule:ttWF2.induct, auto)
  using ttWF.simps(12) ctt_prefix_subset_ttWF apply blast
  apply (meson ttWF.simps(11) ctt_prefix_subset_ttWF)
  using ttWF.simps(13) ctt_prefix_subset_ttWF apply blast
  using ttWF.simps(8) ctt_prefix_subset_ttWF apply blast
  using ttWF.simps(6) ctt_prefix_subset_ttWF by blast

lemma ttWF_end_Event_prefix_subset: "ttWF (s @ [[Event e]\<^sub>E]) \<Longrightarrow> t \<lesssim>\<^sub>C s @ [[Event e]\<^sub>E] \<Longrightarrow> 
  (\<exists> r Y. t = r @ [[Y]\<^sub>R]) \<or> (\<exists> r Y. t = r @ [[Y]\<^sub>R, [Tock]\<^sub>E]) \<or> (\<exists> r e. t = r @ [[Event e]\<^sub>E]) \<or> t = []"
  apply (induct s t rule:ttWF2.induct, auto)
  using ctt_prefix_subset_antisym apply fastforce
  using ttWF.simps(12) ctt_prefix_subset_ttWF apply blast
  apply (meson ttWF.simps(11) ctt_prefix_subset_ttWF)
  using ttWF.simps(13) ctt_prefix_subset_ttWF apply blast
  using ttWF.simps(8) ctt_prefix_subset_ttWF apply blast
  using ttWF.simps(6) ctt_prefix_subset_ttWF by blast

lemma ttWF_end_Tock_prefix_subset: "ttWF (s @ [[Tock]\<^sub>E]) \<Longrightarrow> t \<lesssim>\<^sub>C s @ [[Tock]\<^sub>E] \<Longrightarrow> 
  (\<exists> r Y. t = r @ [[Y]\<^sub>R]) \<or> (\<exists> r Y. t = r @ [[Y]\<^sub>R, [Tock]\<^sub>E]) \<or> (\<exists> r e. t = r @ [[Event e]\<^sub>E]) \<or> t = []"
  apply (induct s t rule:ttWF2.induct, auto)
  using ctt_prefix_subset_antisym apply fastforce
  using ttWF.simps(12) ctt_prefix_subset_ttWF apply blast
  apply (meson ttWF.simps(11) ctt_prefix_subset_ttWF)
  using ttWF.simps(13) ctt_prefix_subset_ttWF apply blast
  using ttWF.simps(8) ctt_prefix_subset_ttWF apply blast
  using ttWF.simps(6) ctt_prefix_subset_ttWF by blast

lemma ttWF_cons_hd_not_Tock_then_ttWF:
  assumes "ttWF (a # fl)" "hd fl \<noteq> [Tock]\<^sub>E"
  shows "ttWF fl"
  by (metis (no_types, lifting) assms(1) assms(2) ttWF.elims(2) ttWF.simps(1) list.discI list.inject list.sel(1))

lemma ttWF_dist_cons_refusal: 
  assumes "ttWF (s @ [[S]\<^sub>R,x])"
  shows "ttWF [[S]\<^sub>R,x]"
  using assms by(induct s rule:ttWF.induct, auto)

section {* Healthiness Conditions *}

definition TT0 :: "'e cttobs list set \<Rightarrow> bool" where
  "TT0 P = (P \<noteq> {})"

definition TT1c :: "'e cttobs list set \<Rightarrow> bool" where
  "TT1c P = (\<forall> \<rho> \<sigma>. (\<rho> \<le>\<^sub>C \<sigma> \<and> \<sigma> \<in> P) \<longrightarrow> \<rho> \<in> P)"

definition TT1 :: "'e cttobs list set \<Rightarrow> bool" where
  "TT1 P = (\<forall> \<rho> \<sigma>. (\<rho> \<lesssim>\<^sub>C \<sigma> \<and> \<sigma> \<in> P) \<longrightarrow> \<rho> \<in> P)"

definition TT2 :: "'e cttobs list set \<Rightarrow> bool" where
  "TT2 P = (\<forall> \<rho> X Y. (\<rho> @ [[X]\<^sub>R] \<in> P \<and> (Y \<inter> {e. (e \<noteq> Tock \<and> \<rho> @ [[e]\<^sub>E] \<in> P) \<or> (e = Tock \<and> \<rho> @ [[X]\<^sub>R, [e]\<^sub>E] \<in> P) } = {}))
     \<longrightarrow> \<rho> @ [[X \<union> Y]\<^sub>R] \<in> P)"

definition TT2s :: "'e cttobs list set \<Rightarrow> bool" where
  "TT2s P = (\<forall> \<rho> \<sigma> X Y. (\<rho> @ [[X]\<^sub>R] @ \<sigma> \<in> P \<and> (Y \<inter> {e. (e \<noteq> Tock \<and> \<rho> @ [[e]\<^sub>E] \<in> P) \<or> (e = Tock \<and> \<rho> @ [[X]\<^sub>R, [e]\<^sub>E] \<in> P) } = {}))
     \<longrightarrow> \<rho> @ [[X \<union> Y]\<^sub>R] @ \<sigma> \<in> P)"

lemma wf_TT2s_induct:
  "\<forall>x\<in>P. ttWF x \<Longrightarrow>
    (\<And> \<rho> \<sigma> X Y. ([[X]\<^sub>R] \<in> P \<and> (Y \<inter> {e. (e \<noteq> Tock \<and> [[e]\<^sub>E] \<in> P) \<or> (e = Tock \<and> [[X]\<^sub>R, [e]\<^sub>E] \<in> P) } = {})) \<Longrightarrow> [[X \<union> Y]\<^sub>R] \<in> P) \<Longrightarrow>
    (\<And> \<rho> \<sigma> X Y. ([[X]\<^sub>R, [Tock]\<^sub>E] @ \<sigma> \<in> P \<and> (Y \<inter> {e. e \<noteq> Tock \<and> [[e]\<^sub>E] \<in> P \<or> e = Tock \<and> [[X]\<^sub>R, [e]\<^sub>E] \<in> P} = {})) \<Longrightarrow> [[X \<union> Y]\<^sub>R, [Tock]\<^sub>E] @ \<sigma> \<in> P) \<Longrightarrow>
    (\<And>e \<rho> \<sigma> X Y. ((\<rho> @ [[X]\<^sub>R] @ \<sigma> \<in> P \<and> (Y \<inter> {e. (e \<noteq> Tock \<and> \<rho> @ [[e]\<^sub>E] \<in> P) \<or> (e = Tock \<and> \<rho> @ [[X]\<^sub>R, [e]\<^sub>E] \<in> P)} = {})) \<Longrightarrow> \<rho> @ [[X \<union> Y]\<^sub>R] @ \<sigma> \<in> P) \<Longrightarrow> 
      (([Event e]\<^sub>E # \<rho> @ [[X]\<^sub>R] @ \<sigma> \<in> P \<and> (Y \<inter> {ea. (ea \<noteq> Tock \<and> [Event e]\<^sub>E # \<rho> @ [[ea]\<^sub>E] \<in> P) \<or> (ea = Tock \<and> [Event e]\<^sub>E # \<rho> @ [[X]\<^sub>R, [ea]\<^sub>E] \<in> P)} = {})) \<Longrightarrow> 
        [Event e]\<^sub>E # \<rho> @ [[X \<union> Y]\<^sub>R] @ \<sigma> \<in> P)) \<Longrightarrow>
    (\<And>e \<rho> \<sigma> X Y Z. ((\<rho> @ [[X]\<^sub>R] @ \<sigma> \<in> P \<and> (Y \<inter> {e. (e \<noteq> Tock \<and> \<rho> @ [[e]\<^sub>E] \<in> P) \<or> (e = Tock \<and> \<rho> @ [[X]\<^sub>R, [e]\<^sub>E] \<in> P)} = {})) \<Longrightarrow> \<rho> @ [[X \<union> Y]\<^sub>R] @ \<sigma> \<in> P) \<Longrightarrow> 
      (([Z]\<^sub>R # [Tock]\<^sub>E # \<rho> @ [[X]\<^sub>R] @ \<sigma> \<in> P \<and> (Y \<inter> {e. (e \<noteq> Tock \<and> [Z]\<^sub>R # [Tock]\<^sub>E # \<rho> @ [[e]\<^sub>E] \<in> P) \<or> (e = Tock \<and> [Z]\<^sub>R # [Tock]\<^sub>E # \<rho> @ [[X]\<^sub>R, [e]\<^sub>E] \<in> P)} = {})) \<Longrightarrow>
        [Z]\<^sub>R # [Tock]\<^sub>E # \<rho> @ [[X \<union> Y]\<^sub>R] @ \<sigma> \<in> P)) \<Longrightarrow>
    TT2s P"
  unfolding TT2s_def
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

lemma TT2s_imp_TT2: "TT2s P \<Longrightarrow> TT2 P"
  unfolding TT2s_def TT2_def by auto

fun TT3_trace :: "'e cttobs list \<Rightarrow> bool" where
  "TT3_trace [] = True" |
  "TT3_trace [x] = True" |
  "TT3_trace ([X]\<^sub>R # [Tock]\<^sub>E # \<rho>) = (Tock \<notin> X \<and> TT3_trace \<rho>)" |
  "TT3_trace ([va]\<^sub>E # vb # vc) = TT3_trace (vb # vc)" |
  "TT3_trace (v # [Event vd]\<^sub>E # vc) = TT3_trace ([Event vd]\<^sub>E # vc)" |
  "TT3_trace (v # [Tick]\<^sub>E # vc) = TT3_trace ([Tick]\<^sub>E # vc)" |
  "TT3_trace ([vb]\<^sub>R # [va]\<^sub>R # vc) = TT3_trace ([va]\<^sub>R # vc)"

definition TT3 :: "'e cttobs list set \<Rightarrow> bool" where
  "TT3 P = (\<forall>\<rho>\<in>P. TT3_trace \<rho>)"

lemma TT3_append: "ttWF t \<Longrightarrow> TT3_trace s \<Longrightarrow> TT3_trace t \<Longrightarrow> TT3_trace (s @ t)"
  apply (induct s rule:TT3_trace.induct, auto)
  apply (induct t, auto)
  apply (case_tac x, auto, case_tac a, auto, case_tac x1, auto)
  done

lemma TT3_end_tock: "TT3_trace (\<rho>) \<Longrightarrow> TT3 P \<Longrightarrow> \<rho> @ [[X]\<^sub>R, [Tock]\<^sub>E] \<in> P \<Longrightarrow> Tock \<notin> X"
proof -
  assume "TT3 P" "\<rho> @ [[X]\<^sub>R, [Tock]\<^sub>E] \<in> P"
  then have "TT3_trace (\<rho> @ [[X]\<^sub>R, [Tock]\<^sub>E])"
    unfolding TT3_def by auto 
  then show "TT3_trace (\<rho>) \<Longrightarrow> Tock \<notin> X"
    by (auto, induct \<rho> rule:TT3_trace.induct, auto, case_tac x, auto)
qed

lemma TT3_trace_cons_left:
  "TT3_trace (xs @ ys) \<Longrightarrow> TT3_trace xs"
  by (induct xs rule:TT3_trace.induct, auto)

lemma TT3_trace_cons_right:
  "TT3_trace (xs @ ys) \<Longrightarrow> TT3_trace ys"
  apply (induct xs rule:TT3_trace.induct, auto)
  apply (case_tac x, auto)
   apply (case_tac x1, auto)
  apply (metis TT3_trace.elims(3) TT3_trace.simps(4))
  apply (metis TT3_trace.elims(3) TT3_trace.simps(4))
  apply (metis TT3_trace.elims(3) TT3_trace.simps(4))
  using TT3_trace.elims(2) TT3_trace.elims(3) list.discI by auto

lemma TT3_any_cons_end_tock:
  assumes "TT3 P" "\<rho> @ [[X]\<^sub>R, [Tock]\<^sub>E] \<in> P"
  shows "Tock \<notin> X"
proof -
  have "TT3_trace ([[X]\<^sub>R, [Tock]\<^sub>E])"
    using assms TT3_def TT3_trace_cons_right by blast
  then show ?thesis
    by simp
qed

lemma TT3_trace_end_refusal_change:
  "TT3_trace (t @ [[X]\<^sub>R]) \<Longrightarrow> TT3_trace (t @ [[Y]\<^sub>R])"
  by (induct t rule:TT3_trace.induct, auto, case_tac x, auto)

lemma TT3_trace_cons_imp_cons:
  assumes "TT3_trace (a # fl)"
  shows "TT3_trace fl"
  using assms apply (cases a, auto)
  apply(induct fl rule:TT3_trace.induct, auto)
  apply(induct fl rule:TT3_trace.induct, auto)
  by (case_tac va, auto)

(*definition TT4 :: "'e cttobs list set \<Rightarrow> bool" where
  "TT4 P = (\<forall> \<rho>. \<rho> @ [[Tick]\<^sub>E] \<in> P \<longrightarrow> (\<nexists> X. \<rho> @ [[X]\<^sub>R] \<in> P))"*)

definition TT4 :: "'e cttobs list set \<Rightarrow> bool" where
"TT4 P = (\<forall> \<rho> X. \<rho> @ [[X]\<^sub>R] \<in> P \<longrightarrow> \<rho> @ [[X \<union> {Tick}]\<^sub>R] \<in> P)"

fun add_Tick_refusal_trace :: "'e cttobs list \<Rightarrow> 'e cttobs list" where
  "add_Tick_refusal_trace [] = []" |
  "add_Tick_refusal_trace ([e]\<^sub>E # t) = [e]\<^sub>E # add_Tick_refusal_trace t" |
  "add_Tick_refusal_trace ([X]\<^sub>R # t) = [X \<union> {Tick}]\<^sub>R # add_Tick_refusal_trace t"

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

lemma add_Tick_refusal_trace_ctt_subset:
  "\<rho> \<subseteq>\<^sub>C add_Tick_refusal_trace \<rho>"
  by (induct \<rho> rule:add_Tick_refusal_trace.induct, auto)

lemma add_Tick_refusal_trace_same_length:
  "length \<rho> = length (add_Tick_refusal_trace \<rho>)"
  by (simp add: add_Tick_refusal_trace_ctt_subset ctt_subset_same_length)

lemma add_Tick_refusal_trace_filter_Tock_same_length:
  "length (filter (\<lambda> x. x = [Tock]\<^sub>E) \<rho>) = length (filter (\<lambda> x. x = [Tock]\<^sub>E) (add_Tick_refusal_trace \<rho>))"
  by (induct \<rho> rule:add_Tick_refusal_trace.induct, auto)

lemma add_Tick_refusal_trace_concat:
  "add_Tick_refusal_trace (\<rho> @ \<sigma>) = add_Tick_refusal_trace \<rho> @ add_Tick_refusal_trace \<sigma>"
  by (induct \<rho> rule:add_Tick_refusal_trace.induct, auto)

definition TT4s :: "'e cttobs list set \<Rightarrow> bool" where
  "TT4s P = (\<forall> \<rho>. \<rho> \<in> P \<longrightarrow> add_Tick_refusal_trace \<rho> \<in> P)"

lemma TT4s_TT1_imp_TT4:
  "TT4s P \<Longrightarrow> TT1 P \<Longrightarrow> TT4 P"
  unfolding TT4_def TT4s_def TT1_def
proof (safe, simp)
  fix \<rho> X
  assume TT1_P: "\<forall>\<rho>. (\<exists>\<sigma>. \<rho> \<lesssim>\<^sub>C \<sigma> \<and> \<sigma> \<in> P) \<longrightarrow> \<rho> \<in> P"
  assume "\<rho> @ [[X]\<^sub>R] \<in> P" "\<forall>\<rho>. \<rho> \<in> P \<longrightarrow> add_Tick_refusal_trace \<rho> \<in> P"
  then have "add_Tick_refusal_trace (\<rho> @ [[X]\<^sub>R]) \<in> P"
    by auto
  then have "add_Tick_refusal_trace \<rho> @ [[X \<union> {Tick}]\<^sub>R] \<in> P"
    by (simp add: add_Tick_refusal_trace_end_refusal)
  also have "\<rho> @ [[X \<union> {Tick}]\<^sub>R] \<subseteq>\<^sub>C add_Tick_refusal_trace \<rho> @ [[X \<union> {Tick}]\<^sub>R]"
    by (simp add: add_Tick_refusal_trace_ctt_subset ctt_subset_combine)
  then show "\<rho> @ [[insert Tick X]\<^sub>R] \<in> P"
    using TT1_P calculation ctt_subset_imp_prefix_subset by auto
qed

lemma TT4s_TT1_add_Tick_ref_Tock:
  "TT4s P \<Longrightarrow> TT1 P \<Longrightarrow> [X]\<^sub>R # [Tock]\<^sub>E # t \<in> P \<Longrightarrow> [X \<union> {Tick}]\<^sub>R # [Tock]\<^sub>E # t \<in> P"
  by (metis TT1_def TT4s_def add_Tick_refusal_trace.simps(3) add_Tick_refusal_trace_ctt_subset add_Tick_refusal_trace_idempotent ctt_subset_imp_prefix_subset)

lemma "add_Tick_refusal_trace (\<rho> @ [X]\<^sub>R # \<sigma>) = add_Tick_refusal_trace \<rho> @ [X \<union> {Tick}]\<^sub>R # add_Tick_refusal_trace \<sigma>"
  oops

lemma TT4s_TT1_add_Tick:
  assumes TT1_P: "TT1 P" and TT4s_P: "TT4s P"
  shows "\<rho> @ [X]\<^sub>R # \<sigma> \<in> P \<Longrightarrow> \<rho> @ [X \<union> {Tick}]\<^sub>R # \<sigma> \<in> P"
proof auto
  assume "\<rho> @ [X]\<^sub>R # \<sigma> \<in> P"
  then have "add_Tick_refusal_trace (\<rho> @ [X]\<^sub>R # \<sigma>) \<in> P"
    using TT4s_P unfolding TT4s_def by auto
  then show "\<rho> @ [insert Tick X]\<^sub>R # \<sigma> \<in> P"
    using TT1_P unfolding TT1_def apply auto
    by (metis Un_insert_left Un_insert_right add_Tick_refusal_trace.simps(3) add_Tick_refusal_trace_concat add_Tick_refusal_trace_ctt_subset ctt_subset_imp_prefix_subset insert_absorb2)
qed  

definition TTwf :: "'e cttobs list set \<Rightarrow> bool" where
  "TTwf P = (\<forall>x\<in>P. ttWF x)"

lemma TTwf_cons_end_not_refusal_refusal:
  assumes "TTwf P"
  shows "\<not> sa @ [[S]\<^sub>R, [Z]\<^sub>R] \<in> P"
  using assms unfolding TTwf_def using ttWF_dist_cons_refusal
  using ttWF.simps(13) by blast

definition TT :: "'e cttobs list set \<Rightarrow> bool" where
  "TT P = ((\<forall>x\<in>P. ttWF x) \<and> TT0 P \<and> TT1 P \<and> TT2 P \<and> TT3 P)"

lemma TT_TT0: "TT P \<Longrightarrow> TT0 P"
  using TT_def by auto

lemma TT_TT1: "TT P \<Longrightarrow> TT1 P"
  using TT_def by auto

lemma TT1_TT1c: "TT1 P \<Longrightarrow> TT1c P"
  unfolding TT1_def TT1c_def
  using ctt_prefix_imp_prefix_subset by blast

lemma TT_TT1c: "TT P \<Longrightarrow> TT1c P"
  unfolding TT_def using TT1_TT1c by auto

lemma TT_TT2: "TT P \<Longrightarrow> TT2 P"
  using TT_def by auto

lemma TT_TT3: "TT P \<Longrightarrow> TT3 P"
  using TT_def by auto

lemma TT_wf: "TT P \<Longrightarrow> \<forall>x\<in>P. ttWF x"
  using TT_def by auto

lemma TT_TTwf: "TT P \<Longrightarrow> TTwf P"
  unfolding TT_def TTwf_def by auto

lemma TT0_TT1c_empty: "TT0 P \<Longrightarrow> TT1c P \<Longrightarrow> [] \<in> P"
  unfolding TT0_def TT1c_def apply auto
  using ctt_prefix.simps(1) by blast

lemma TT0_TT1_empty: "TT0 P \<Longrightarrow> TT1 P \<Longrightarrow> [] \<in> P"
  unfolding TT0_def TT1_def
proof auto
  fix x
  assume x_in_P: "x \<in> P"
  assume "\<forall>\<rho>. (\<exists>\<sigma>. \<rho> \<lesssim>\<^sub>C \<sigma> \<and> \<sigma> \<in> P) \<longrightarrow> \<rho> \<in> P"
  then have "(\<exists>\<sigma>. [] \<lesssim>\<^sub>C \<sigma> \<and> \<sigma> \<in> P) \<longrightarrow> [] \<in> P"
    by blast
  then have "[] \<in> P"
    using ctt_prefix_subset.simps(1) x_in_P by blast
  also assume "[] \<notin> P"
  then show "False"
    using calculation by auto
qed

lemma TT_empty: "TT P \<Longrightarrow> [] \<in> P"
  by (simp add: TT0_TT1_empty TT_TT0 TT_TT1)

lemmas TT_defs = TT_def TT0_def TT1_def TT2_def TT3_def

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
  fix \<rho> \<sigma> :: "'a cttobs list"
  assume "\<rho> \<lesssim>\<^sub>C \<sigma>"
  then have "[Event e]\<^sub>E # \<rho> \<lesssim>\<^sub>C [Event e]\<^sub>E # \<sigma>"
    by auto
  then show "[Event e]\<^sub>E # \<sigma> \<in> P \<Longrightarrow> [Event e]\<^sub>E # \<rho> \<in> P"
    using TT1_def TT_TT1 assms(1) by blast
next
  fix \<rho> X Y
  have "\<forall>\<rho> X Y. \<rho> @ [[X]\<^sub>R] \<in> P \<and> Y \<inter> {e. e \<noteq> Tock \<and> \<rho> @ [[e]\<^sub>E] \<in> P \<or> e = Tock \<and> \<rho> @ [[X]\<^sub>R, [e]\<^sub>E] \<in> P} = {} \<longrightarrow>
         \<rho> @ [[X \<union> Y]\<^sub>R] \<in> P"
    using TT2_def TT_TT2 assms(1) by auto
  then show "[Event e]\<^sub>E # \<rho> @ [[X]\<^sub>R] \<in> P \<Longrightarrow>
    Y \<inter> {ea. ea \<noteq> Tock \<and> [Event e]\<^sub>E # \<rho> @ [[ea]\<^sub>E] \<in> P \<or> ea = Tock \<and> [Event e]\<^sub>E # \<rho> @ [[X]\<^sub>R, [ea]\<^sub>E] \<in> P} = {} \<Longrightarrow>
      [Event e]\<^sub>E # \<rho> @ [[X \<union> Y]\<^sub>R] \<in> P"
    by (erule_tac x="[Event e]\<^sub>E # \<rho>" in allE, auto)
next
  fix x
  assume "[Event e]\<^sub>E # x \<in> P"
  then have "TT3_trace ([Event e]\<^sub>E # x)"
    using TT3_def TT_TT3 assms(1) by blast
  then show "TT3_trace x"
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
  fix \<rho> \<sigma> :: "'a cttobs list"
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
    using assms(1) unfolding TT_def TT2_def apply auto
    by (erule_tac x="[X]\<^sub>R # [Tock]\<^sub>E # \<rho>" in allE, auto)
next
  fix x
  assume "[X]\<^sub>R # [Tock]\<^sub>E # x \<in> P"
  then have "TT3_trace ([X]\<^sub>R # [Tock]\<^sub>E # x)"
    using TT3_def TT_TT3 assms(1) by blast
  then show "TT3_trace x"
    by auto
qed

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

lemma TT2s_init_event:
  assumes "TT2s P"
  shows "TT2s {t. [Event e]\<^sub>E # t \<in> P}"
  using assms unfolding TT2s_def apply (auto)
  by (erule_tac x="[Event e]\<^sub>E # \<rho>" in allE, auto)

lemma TT2s_init_tock:
  assumes "TT2s P"
  shows "TT2s {t. [X]\<^sub>R # [Tock]\<^sub>E # t \<in> P}"
  using assms unfolding TT2s_def apply (auto)
  by (erule_tac x="[X]\<^sub>R # [Tock]\<^sub>E # \<rho>" in allE, auto)

section {* Initial sequences of tocks *}

inductive_set tocks :: "'e cttevent set \<Rightarrow> 'e cttobs list set" for X :: "'e cttevent set" where
  empty_in_tocks: "[] \<in> tocks X" |
  tock_insert_in_tocks: "Y \<subseteq> X \<Longrightarrow> \<rho> \<in> tocks X \<Longrightarrow> [Y]\<^sub>R # [Tock]\<^sub>E # \<rho> \<in> tocks X"

lemma tocks_wf: "t\<in>tocks X \<Longrightarrow> ttWF t"
  by (induct t rule:ttWF.induct, auto, (cases rule:tocks.cases, auto)+)

lemma tocks_append_wf: "ttWF s \<Longrightarrow> t\<in>tocks X \<Longrightarrow> ttWF (t @ s)"
  by (induct t rule:ttWF.induct, auto, (cases rule:tocks.cases, auto)+)

lemma tocks_append_wf2: "ttWF (t @ s) \<Longrightarrow> t\<in>tocks X \<Longrightarrow> ttWF s"
  by (induct t rule:ttWF.induct, auto, (cases rule:tocks.cases, auto)+)

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
  fix X :: "'e cttevent set"
  show "\<exists>s. \<exists>t\<in>tocks UNIV. [[X]\<^sub>R] = t @ s \<and> (\<forall>t'\<in>tocks UNIV. t' \<le>\<^sub>C [[X]\<^sub>R] \<longrightarrow> t' \<le>\<^sub>C t)"
    apply (rule_tac x="[[X]\<^sub>R]" in exI) 
    apply (rule_tac x="[]" in bexI)
     apply (auto simp add: empty_in_tocks)
    apply (case_tac t', auto)
    using ctt_prefix_decompose tocks.simps by auto
next
  show " \<exists>s. \<exists>t\<in>tocks UNIV. [[Tick]\<^sub>E] = t @ s \<and> (\<forall>t'\<in>tocks UNIV. t' \<le>\<^sub>C [[Tick]\<^sub>E] \<longrightarrow> t' \<le>\<^sub>C t)"
    apply (rule_tac x="[[Tick]\<^sub>E]" in exI, rule_tac x="[]" in bexI, auto simp add: empty_in_tocks)
    apply (case_tac t', auto)
    using ctt_prefix_decompose tocks.simps by auto
next
  fix e s t
  show "\<exists>sa. \<exists>ta\<in>tocks UNIV. [Event e]\<^sub>E # t @ s = ta @ sa \<and> (\<forall>t'\<in>tocks UNIV. t' \<le>\<^sub>C [Event e]\<^sub>E # t @ s \<longrightarrow> t' \<le>\<^sub>C ta)"
    apply (rule_tac x="[Event e]\<^sub>E # t @ s" in exI, rule_tac x="[]" in bexI, auto)
    apply (case_tac t', auto)
    using ctt_prefix_decompose tocks.simps by auto
next
  fix X s t
  assume case_assms: "t \<in> tocks UNIV" " \<forall>t'\<in>tocks UNIV. t' \<le>\<^sub>C t @ s \<longrightarrow> t' \<le>\<^sub>C t"
  then show "\<exists>sa. \<exists>ta\<in>tocks UNIV. [X]\<^sub>R # [Tock]\<^sub>E # t @ s = ta @ sa \<and> (\<forall>t'\<in>tocks UNIV. t' \<le>\<^sub>C [X]\<^sub>R # [Tock]\<^sub>E # t @ s \<longrightarrow> t' \<le>\<^sub>C ta)"
  proof (rule_tac x="s" in exI, rule_tac x="[X]\<^sub>R # [Tock]\<^sub>E # t" in bexI, auto)
    fix t' :: "'b cttobs list"
    assume "t' \<in> tocks UNIV" "t' \<le>\<^sub>C [X]\<^sub>R # [Tock]\<^sub>E # t @ s"
    then show "t' \<le>\<^sub>C [X]\<^sub>R # [Tock]\<^sub>E # t"
      by (cases rule:tocks.cases, auto simp add: case_assms(2))
  next
    show "t \<in> tocks UNIV \<Longrightarrow> [X]\<^sub>R # [Tock]\<^sub>E # t \<in> tocks UNIV"
      by (simp add: tocks.tock_insert_in_tocks)
  qed
qed

lemma ctt_prefix_subset_tocks: "s \<in> tocks X \<Longrightarrow> t \<lesssim>\<^sub>C s \<Longrightarrow> t \<in> {t. \<exists>s\<in>tocks X. t = s \<or> (\<exists>Y. t = s @ [[Y]\<^sub>R] \<and> Y \<subseteq> X)}"
proof -
  assume "s \<in> tocks X" 
  then have "ttWF s"
    using tocks_wf by blast
  also have "ttWF s \<longrightarrow> s \<in> tocks X \<longrightarrow> t \<lesssim>\<^sub>C s \<longrightarrow> t \<in> {t. \<exists>s\<in>tocks X. t = s \<or> (\<exists>Y. t = s @ [[Y]\<^sub>R] \<and> Y \<subseteq> X)}"
    apply (induct t s rule:ttWF2.induct)
    apply (simp_all add: empty_in_tocks)
    using tocks.simps apply auto[1]
    apply (case_tac \<sigma> rule:ttWF.cases, auto)
    apply (rule_tac x="[]" in bexI, simp, insert tocks.cases, force, simp add: empty_in_tocks)
    apply (rule_tac x="[]" in bexI, simp, insert tocks.cases, force, simp add: empty_in_tocks)
    apply (metis list.inject list.simps(3) tocks.simps)
    apply (metis cttobs.inject(2) dual_order.trans list.inject list.simps(3) tocks.simps)
    apply (metis cttobs.inject(2) dual_order.trans list.inject list.simps(3) tocks.empty_in_tocks tocks.simps)
    apply (blast, blast, blast, blast)
    apply (rule_tac x="[Xa]\<^sub>R # [Tock]\<^sub>E # s" in bexI, simp)
    apply (metis cttobs.inject(2) list.inject list.simps(3) rev_subsetD subsetI tocks.simps)
    apply (rule_tac x="[Xa]\<^sub>R # [Tock]\<^sub>E # s" in bexI, simp)
    apply (metis cttobs.inject(2) list.inject list.simps(3) rev_subsetD subsetI tocks.simps)
    apply (case_tac \<sigma> rule:ttWF.cases, auto)+
    done
  then show "s \<in> tocks X \<Longrightarrow> t \<lesssim>\<^sub>C s \<Longrightarrow> t \<in> {t. \<exists>s\<in>tocks X. t = s \<or> (\<exists>Y. t = s @ [[Y]\<^sub>R] \<and> Y \<subseteq> X)}" using calculation by auto
qed

lemma ctt_prefix_tocks: "s \<in> tocks X \<Longrightarrow> t \<le>\<^sub>C s \<Longrightarrow> t \<in> {t. \<exists>s\<in>tocks X. t = s \<or> (\<exists>Y. t = s @ [[Y]\<^sub>R] \<and> Y \<subseteq> X)}"
  using ctt_prefix_imp_prefix_subset ctt_prefix_subset_tocks by blast

lemma ctt_prefix_subset_tocks2: "s \<in> tocks X \<Longrightarrow> t \<lesssim>\<^sub>C s \<Longrightarrow> t \<in> {t. \<exists>s'\<in>tocks X. s'\<lesssim>\<^sub>C s \<and> (t = s' \<or> (\<exists>Y. t = s' @ [[Y]\<^sub>R] \<and> Y \<subseteq> X))}"
proof -
  assume "s \<in> tocks X" 
  then have "ttWF s"
    using tocks_wf by blast
  also have "ttWF s \<longrightarrow> s \<in> tocks X \<longrightarrow> t \<lesssim>\<^sub>C s \<longrightarrow> t \<in> {t. \<exists>s'\<in>tocks X. s'\<lesssim>\<^sub>C s \<and> (t = s' \<or> (\<exists>Y. t = s' @ [[Y]\<^sub>R] \<and> Y \<subseteq> X))}"
    apply (induct t s rule:ttWF2.induct)
    apply (simp_all add: empty_in_tocks)
    using tocks.simps apply auto[1]
    apply (case_tac \<sigma> rule:ttWF.cases, auto)
    apply (rule_tac x="[]" in bexI, simp, insert tocks.cases, force, simp add: empty_in_tocks)
    apply (rule_tac x="[]" in bexI, simp, insert tocks.cases, force, simp add: empty_in_tocks)
    apply (metis list.inject list.simps(3) tocks.simps)
    apply (metis cttobs.simps(4) list.inject list.simps(3) tocks.simps)
    apply (metis ctt_prefix_subset.simps(1) cttobs.inject(2) list.distinct(1) list.inject subset_trans tocks.simps)
    apply (blast, blast, blast, blast)
    apply (rule_tac x="[Xa]\<^sub>R # [Tock]\<^sub>E # s'" in bexI, auto)
    apply (metis cttobs.inject(2) list.inject list.simps(3) rev_subsetD subsetI tocks.simps)
    apply (rule_tac x="[Xa]\<^sub>R # [Tock]\<^sub>E # s'" in bexI, simp)
    apply (metis cttobs.inject(2) list.inject list.simps(3) rev_subsetD subsetI tocks.simps)
    apply (case_tac \<sigma> rule:ttWF.cases, auto)+
    done
  then show "s \<in> tocks X \<Longrightarrow> t \<lesssim>\<^sub>C s \<Longrightarrow> t \<in> {t. \<exists>s'\<in>tocks X. s' \<lesssim>\<^sub>C s \<and> (t = s' \<or> (\<exists>Y. t = s' @ [[Y]\<^sub>R] \<and> Y \<subseteq> X))}"
    using calculation by blast
qed

lemma ctt_prefix_subset_tocks_refusal: "s \<in> tocks X \<Longrightarrow> \<rho> \<lesssim>\<^sub>C s @ [[Y]\<^sub>R] \<Longrightarrow> (\<exists> t \<in> tocks X. \<rho> = t \<or> (\<exists> Z. \<rho> = t @ [[Z]\<^sub>R] \<and> (Z \<subseteq> X \<or> Z \<subseteq> Y)))"
proof -
  assume "s \<in> tocks X"
  then have "ttWF (s @ [[Y]\<^sub>R])"
    using ttWF.simps(2) tocks_append_wf by blast
  also have "s \<in> tocks X \<longrightarrow> ttWF (s @ [[Y]\<^sub>R]) \<longrightarrow> \<rho> \<lesssim>\<^sub>C s @ [[Y]\<^sub>R] \<longrightarrow> (\<exists> t \<in> tocks X. \<rho> = t \<or> (\<exists> Z. \<rho> = t @ [[Z]\<^sub>R] \<and> (Z \<subseteq> X \<or> Z \<subseteq> Y)))"
    apply (induct \<rho> s rule:ttWF2.induct, auto simp add: empty_in_tocks)
    apply (rule_tac x="[]" in bexI, auto simp add: empty_in_tocks)
    apply (metis contra_subsetD cttobs.inject(2) list.inject list.simps(3) tocks.simps)
    using tocks.cases apply auto
    apply blast
    apply blast
    apply blast
    apply (rule_tac x="[Xa]\<^sub>R # [Tock]\<^sub>E # t" in bexI, auto simp add: empty_in_tocks)
           apply (metis cttobs.inject(2) list.inject list.simps(3) rev_subsetD subsetI tocks.simps)
    apply (rule_tac x="[Xa]\<^sub>R # [Tock]\<^sub>E # t" in bexI, auto simp add: empty_in_tocks)
    apply (metis cttobs.inject(2) list.inject list.simps(3) rev_subsetD subsetI tocks.simps)
    apply (rule_tac x="[Xa]\<^sub>R # [Tock]\<^sub>E # t" in bexI, auto simp add: empty_in_tocks)
    apply (metis cttobs.inject(2) list.inject list.simps(3) rev_subsetD subsetI tocks.simps)
    apply (meson ttWF.simps(12) ctt_prefix_subset_ttWF)
    apply (meson ttWF.simps(11) ctt_prefix_subset_ttWF)
    apply (meson ttWF.simps(13) ctt_prefix_subset_ttWF)
    apply (meson ttWF.simps(8) ctt_prefix_subset_ttWF)
    by (meson ttWF.simps(6) ctt_prefix_subset_ttWF)
  then show "s \<in> tocks X \<Longrightarrow> \<rho> \<lesssim>\<^sub>C s @ [[Y]\<^sub>R] \<Longrightarrow> \<exists>t\<in>tocks X. \<rho> = t \<or> (\<exists>Z. \<rho> = t @ [[Z]\<^sub>R] \<and> (Z \<subseteq> X \<or> Z \<subseteq> Y))"
    using calculation by auto
qed

lemma ctt_prefix_subset_tocks_refusal2: "s \<in> tocks X \<Longrightarrow> \<rho> \<lesssim>\<^sub>C s @ [[Y]\<^sub>R] \<Longrightarrow>
  (\<exists> t \<in> tocks X. t \<lesssim>\<^sub>C s \<and> (\<rho> = t \<or> (\<exists> Z. \<rho> = t @ [[Z]\<^sub>R] \<and> ((Z \<subseteq> X \<and> length (filter (\<lambda> x. x = [Tock]\<^sub>E) t) < length (filter (\<lambda> x. x = [Tock]\<^sub>E) s)) \<or> (Z \<subseteq> Y \<and> length (filter (\<lambda> x. x = [Tock]\<^sub>E) t) = length (filter (\<lambda> x. x = [Tock]\<^sub>E) s))))))"
proof -
  assume "s \<in> tocks X"
  then have "ttWF (s @ [[Y]\<^sub>R])"
    using ttWF.simps(2) tocks_append_wf by blast
  also have "s \<in> tocks X \<longrightarrow> ttWF (s @ [[Y]\<^sub>R]) \<longrightarrow> \<rho> \<lesssim>\<^sub>C s @ [[Y]\<^sub>R] \<longrightarrow> 
    (\<exists>t\<in>tocks X.
       t \<lesssim>\<^sub>C s \<and>
       (\<rho> = t \<or>
        (\<exists>Z. \<rho> = t @ [[Z]\<^sub>R] \<and>
             (Z \<subseteq> X \<and> length [x\<leftarrow>t . x = [Tock]\<^sub>E] < length [x\<leftarrow>s . x = [Tock]\<^sub>E] \<or>
              Z \<subseteq> Y \<and> length [x\<leftarrow>t . x = [Tock]\<^sub>E] = length [x\<leftarrow>s . x = [Tock]\<^sub>E]))))"
    apply (induct \<rho> s rule:ttWF2.induct, auto simp add: empty_in_tocks)
    apply (rule_tac x="[]" in bexI, auto simp add: empty_in_tocks)
    apply (metis ctt_prefix_subset.simps(1) cttobs.inject(2) dual_order.trans filter.simps(1) list.distinct(1) list.inject list.size(3) tocks.cases tocks.empty_in_tocks zero_less_Suc)
    using tocks.cases apply auto
    apply blast
    apply blast
    apply blast
    apply (rule_tac x="[Xa]\<^sub>R # [Tock]\<^sub>E # t" in bexI, auto simp add: empty_in_tocks)
           apply (metis cttobs.inject(2) list.inject list.simps(3) rev_subsetD subsetI tocks.simps)
    apply (rule_tac x="[Xa]\<^sub>R # [Tock]\<^sub>E # t" in bexI, auto simp add: empty_in_tocks)
    apply (metis cttobs.inject(2) list.inject list.simps(3) rev_subsetD subsetI tocks.simps)
    apply (rule_tac x="[Xa]\<^sub>R # [Tock]\<^sub>E # t" in bexI, auto simp add: empty_in_tocks)
    apply (metis cttobs.inject(2) list.inject list.simps(3) rev_subsetD subsetI tocks.simps)
    apply (meson ttWF.simps(12) ctt_prefix_subset_ttWF)
    apply (meson ttWF.simps(11) ctt_prefix_subset_ttWF)
    apply (meson ttWF.simps(13) ctt_prefix_subset_ttWF)
    apply (meson ttWF.simps(8) ctt_prefix_subset_ttWF)
    by (meson ttWF.simps(6) ctt_prefix_subset_ttWF)
  then show "s \<in> tocks X \<Longrightarrow> \<rho> \<lesssim>\<^sub>C s @ [[Y]\<^sub>R] \<Longrightarrow>
    \<exists>t\<in>tocks X.
       t \<lesssim>\<^sub>C s \<and>
       (\<rho> = t \<or>
        (\<exists>Z. \<rho> = t @ [[Z]\<^sub>R] \<and>
             (Z \<subseteq> X \<and> length [x\<leftarrow>t . x = [Tock]\<^sub>E] < length [x\<leftarrow>s . x = [Tock]\<^sub>E] \<or>        
              Z \<subseteq> Y \<and> length [x\<leftarrow>t . x = [Tock]\<^sub>E] = length [x\<leftarrow>s . x = [Tock]\<^sub>E])))"
    using calculation by auto
qed

lemma ctt_prefix_subset_tocks_event: "e \<noteq> Tock \<Longrightarrow> s \<in> tocks X \<Longrightarrow> t \<lesssim>\<^sub>C s @ [[e]\<^sub>E] \<Longrightarrow>
  t \<in> {t. \<exists>s'\<in>tocks X. s'\<lesssim>\<^sub>C s \<and> 
    (t = s' \<or> 
      (\<exists>Y. t = s' @ [[Y]\<^sub>R] \<and> Y \<subseteq> X \<and> length (filter (\<lambda> x. x = [Tock]\<^sub>E) s') < length (filter (\<lambda> x. x = [Tock]\<^sub>E) s)) \<or>
      (t = s' @ [[e]\<^sub>E] \<and> length (filter (\<lambda> x. x = [Tock]\<^sub>E) s') = length (filter (\<lambda> x. x = [Tock]\<^sub>E) s)))}"
proof -
  assume "e \<noteq> Tock" "s \<in> tocks X"
  then have "ttWF (s @ [[e]\<^sub>E])"
    by (cases e, auto simp add: tocks_append_wf)
  also have "ttWF (s @ [[e]\<^sub>E]) \<longrightarrow> s \<in> tocks X \<longrightarrow> t \<lesssim>\<^sub>C s @ [[e]\<^sub>E] \<longrightarrow>
    t \<in> {t. \<exists>s'\<in>tocks X. s'\<lesssim>\<^sub>C s \<and> 
      (t = s' \<or> 
        (\<exists>Y. t = s' @ [[Y]\<^sub>R] \<and> Y \<subseteq> X \<and> length (filter (\<lambda> x. x = [Tock]\<^sub>E) s') < length (filter (\<lambda> x. x = [Tock]\<^sub>E) s)) \<or>
        (t = s' @ [[e]\<^sub>E] \<and> length (filter (\<lambda> x. x = [Tock]\<^sub>E) s') = length (filter (\<lambda> x. x = [Tock]\<^sub>E) s)))}"
    apply auto
    apply (induct t s rule:ttWF2.induct, auto simp add: empty_in_tocks)
    using tocks.simps apply auto
    apply (metis ctt_prefix_subset.simps(1) cttobs.inject(2) filter.simps(1) list.distinct(1) list.inject list.size(3) order_trans tocks.cases tocks.empty_in_tocks zero_less_Suc)
    using ctt_prefix_subset_refl filter.simps(1) apply blast
    using ctt_prefix_subset_antisym apply fastforce
    apply (case_tac "\<sigma> \<in> tocks X", auto)
    apply (rule_tac x="[Xa]\<^sub>R # [Tock]\<^sub>E # s'" in bexI, auto)
    apply (metis cttobs.inject(2) list.distinct(1) list.inject subset_iff tocks.simps)
    apply (rule_tac x="[Xa]\<^sub>R # [Tock]\<^sub>E # s'" in bexI, auto, metis cttobs.inject(2) list.distinct(1) list.inject subset_iff tocks.simps)
    apply (rule_tac x="[Xa]\<^sub>R # [Tock]\<^sub>E # s'" in bexI, auto, metis cttobs.inject(2) list.distinct(1) list.inject subset_iff tocks.simps)
    apply blast
    apply (meson ttWF.simps(12) ctt_prefix_subset_ttWF)
    apply (meson ttWF.simps(11) ctt_prefix_subset_ttWF)
    apply (meson ttWF.simps(13) ctt_prefix_subset_ttWF)
    apply (meson ttWF.simps(8) ctt_prefix_subset_ttWF)
    using ttWF.simps(6) ctt_prefix_subset_ttWF by blast
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
  apply (metis (no_types, lifting) cttobs.inject(2) list.inject list.simps(3) order.trans tocks.simps)
  apply (meson ttWF.simps(12) ctt_prefix_subset_ttWF tocks_wf)
  apply (meson ttWF.simps(11) ctt_prefix_subset_ttWF tocks_wf)
  apply (meson ttWF.simps(13) ctt_prefix_subset_ttWF tocks_wf)
  apply (meson ttWF.simps(10) ctt_prefix_subset_ttWF tocks_wf)
  by (meson ttWF.simps(6) ctt_prefix_subset_ttWF tocks_wf)

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

lemma tocks_ctt_prefix_end_event: "t \<in> tocks X \<Longrightarrow> e \<noteq> Tock \<Longrightarrow> t \<le>\<^sub>C s @ [[e]\<^sub>E] \<Longrightarrow> t \<le>\<^sub>C s"
proof -
  assume assms: "t \<in> tocks X" "e \<noteq> Tock" "t \<le>\<^sub>C s @ [[e]\<^sub>E]"
  have "t = s @ [[e]\<^sub>E] \<or> t \<le>\<^sub>C s"
    using assms(3) ctt_prefix_notfront_is_whole by blast
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

lemma ctt_subset_remove_start: "\<rho>' @ \<sigma>' \<subseteq>\<^sub>C \<rho> @ \<sigma> \<Longrightarrow> \<rho>' \<subseteq>\<^sub>C \<rho> \<Longrightarrow> \<sigma>' \<subseteq>\<^sub>C \<sigma>"
  by (induct \<rho>' \<rho> rule:ctt_subset.induct, simp_all)

lemma ctt_prefix_subset_lift_tocks:
  "\<rho> \<lesssim>\<^sub>C \<sigma> \<Longrightarrow> \<rho> \<in> tocks UNIV \<Longrightarrow> \<exists> \<rho>' \<in> tocks UNIV. \<rho> \<lesssim>\<^sub>C \<rho>' \<and> \<rho>' \<le>\<^sub>C \<sigma>"
  apply (induct \<rho> \<sigma> rule:ttWF2.induct, auto)
  using tocks.simps apply auto
  using ctt_prefix.simps apply (blast, blast, blast, blast, blast)
proof -
  fix Xa \<rho> Y \<sigma>
  assume "[Xa]\<^sub>R # [Tock]\<^sub>E # \<rho> \<in> tocks UNIV"
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
  assume "[X]\<^sub>R # [Tick]\<^sub>E # \<rho> \<in> tocks UNIV"
  then have "False"
    using ttWF.simps(12) tocks_wf by blast
  then show "\<exists>\<rho>'\<in>tocks UNIV. [X]\<^sub>R # [Tick]\<^sub>E # \<rho> \<lesssim>\<^sub>C \<rho>' \<and> \<rho>' \<le>\<^sub>C \<sigma>"
    by auto
next
  fix X e \<rho> \<sigma>
  assume "[X]\<^sub>R # [Event e]\<^sub>E # \<rho> \<in> tocks UNIV"
  then have "False"
    by (meson ttWF.simps(11) tocks_wf)
  then show "\<exists>\<rho>'\<in>tocks UNIV. [X]\<^sub>R # [Event e]\<^sub>E # \<rho> \<lesssim>\<^sub>C \<rho>' \<and> \<rho>' \<le>\<^sub>C \<sigma>"
    by auto
next
  fix X Y \<rho> \<sigma>
  assume "[X]\<^sub>R # [Y]\<^sub>R # \<rho> \<in> tocks UNIV"
  then have "False"
    using ttWF.simps(13) tocks_wf by blast
  then show "\<exists>\<rho>'\<in>tocks UNIV. [X]\<^sub>R # [Y]\<^sub>R # \<rho> \<lesssim>\<^sub>C \<rho>' \<and> \<rho>' \<le>\<^sub>C \<sigma>"
    by auto
next
  fix X \<rho> \<sigma>
  assume "\<rho> \<lesssim>\<^sub>C [X]\<^sub>R # [Tick]\<^sub>E # \<sigma>" "\<rho> \<in> tocks UNIV"
  then have "\<rho> = []"
    using tocks.simps by fastforce
  then show "\<exists>\<rho>'\<in>tocks UNIV. \<rho> \<lesssim>\<^sub>C \<rho>' \<and> \<rho>' \<le>\<^sub>C [X]\<^sub>R # [Tick]\<^sub>E # \<sigma>"
    using ctt_prefix.simps(1) ctt_prefix_subset.simps(1) tocks.empty_in_tocks by blast
next
  fix \<rho> X e \<sigma>
  assume "\<rho> \<lesssim>\<^sub>C [X]\<^sub>R # [Event e]\<^sub>E # \<sigma>" "\<rho> \<in> tocks UNIV"
  then have "\<rho> = []"
    using tocks.simps by fastforce
  then show "\<exists>\<rho>'\<in>tocks UNIV. \<rho> \<lesssim>\<^sub>C \<rho>' \<and> \<rho>' \<le>\<^sub>C [X]\<^sub>R # [Event e]\<^sub>E # \<sigma>"
    using ctt_prefix.simps(1) ctt_prefix_subset.simps(1) tocks.empty_in_tocks by blast
next
  fix \<rho> X Y \<sigma>
  assume "\<rho> \<lesssim>\<^sub>C [X]\<^sub>R # [Y]\<^sub>R # \<sigma>" "\<rho> \<in> tocks UNIV"
  then have "\<rho> = []"
    using tocks.simps by fastforce
  then show "\<exists>\<rho>'\<in>tocks UNIV. \<rho> \<lesssim>\<^sub>C \<rho>' \<and> \<rho>' \<le>\<^sub>C [X]\<^sub>R # [Y]\<^sub>R # \<sigma>"
    using ctt_prefix.simps(1) ctt_prefix_subset.simps(1) tocks.empty_in_tocks by blast
next
  fix \<rho> y \<sigma>
  assume "\<rho> \<lesssim>\<^sub>C [Tick]\<^sub>E # y # \<sigma>" "\<rho> \<in> tocks UNIV"
  then have "\<rho> = []"
    using tocks.simps by fastforce
  then show "\<exists>\<rho>'\<in>tocks UNIV. \<rho> \<lesssim>\<^sub>C \<rho>' \<and> \<rho>' \<le>\<^sub>C [Tick]\<^sub>E # y # \<sigma>"
    using ctt_prefix.simps(1) ctt_prefix_subset.simps(1) tocks.empty_in_tocks by blast
next
  fix \<rho> \<sigma>
  assume "\<rho> \<lesssim>\<^sub>C [Tock]\<^sub>E # \<sigma>" "\<rho> \<in> tocks UNIV"
  then have "\<rho> = []"
    using tocks.simps by fastforce
  then show "\<exists>\<rho>'\<in>tocks UNIV. \<rho> \<lesssim>\<^sub>C \<rho>' \<and> \<rho>' \<le>\<^sub>C [Tock]\<^sub>E # \<sigma>"
    using ctt_prefix.simps(1) ctt_prefix_subset.simps(1) tocks.empty_in_tocks by blast
qed

lemma longest_pretocks_ctt_prefix_subset:
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
  fix \<sigma>'' :: "'a cttobs list"
  assume assm1: "[X]\<^sub>R # [Tock]\<^sub>E # \<sigma>'' \<in> tocks UNIV"
  assume assm2: "[X]\<^sub>R # [Tock]\<^sub>E # \<sigma>'' @ \<sigma>' \<lesssim>\<^sub>C \<sigma>"
  assume assm3: "\<forall>t\<in>tocks UNIV. t \<le>\<^sub>C \<sigma> \<longrightarrow> t \<le>\<^sub>C []"
  have assm2': "[X]\<^sub>R # [Tock]\<^sub>E # \<sigma>'' \<lesssim>\<^sub>C \<sigma>"
    using assm2 ctt_prefix_subset_front by force
  then obtain \<rho>'' where \<rho>''_assms: "\<rho>'' \<le>\<^sub>C \<sigma>" "[X]\<^sub>R # [Tock]\<^sub>E # \<sigma>'' \<lesssim>\<^sub>C \<rho>''"
    using ctt_prefix_subset_lift by blast
  then have "[[X]\<^sub>R, [Tock]\<^sub>E] \<lesssim>\<^sub>C \<rho>''"
    by (meson ctt_prefix.simps(1) ctt_prefix.simps(2) ctt_prefix_ctt_prefix_subset_trans)
  then obtain Y \<rho>''' where "\<rho>'' = [Y]\<^sub>R # [Tock]\<^sub>E # \<rho>'''"
    by (cases \<rho>'' rule:ttWF.cases, auto)
  then have "[Y]\<^sub>R # [Tock]\<^sub>E # \<rho>''' \<le>\<^sub>C []"
    using assm2' assm1 assm3 ctt_prefix_subset.simps(6) ctt_prefix_subset_ctt_prefix_trans ctt_prefix_subset_lift_tocks by blast
  then show "False"
    by simp
next
  fix Y
  assume "[[Y]\<^sub>R] \<in> tocks UNIV"
  then show "False"
    using tocks.cases by auto
next
  fix X :: "'a cttevent set"
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
    using ttWF.simps(12) tocks_wf by blast
  then show "[X]\<^sub>R # [Tick]\<^sub>E # \<rho> \<lesssim>\<^sub>C \<sigma>''"
    by auto
next
  fix X e \<rho> \<sigma>''
  assume "[X]\<^sub>R # [Event e]\<^sub>E # \<rho> \<in> tocks UNIV"
  then have "False"
    by (meson ttWF.simps(11) tocks_wf)
  then show "[X]\<^sub>R # [Event e]\<^sub>E # \<rho> \<lesssim>\<^sub>C \<sigma>''"
    by auto
next
  fix X Y \<rho> \<sigma>''
  assume "[X]\<^sub>R # [Y]\<^sub>R # \<rho> \<in> tocks UNIV"
  then have "False"
    using ttWF.simps(13) tocks_wf by blast
  then show "[X]\<^sub>R # [Y]\<^sub>R # \<rho> \<lesssim>\<^sub>C \<sigma>''"
    by auto
next
  fix X \<rho> \<sigma>''
  assume "[X]\<^sub>R # [Tick]\<^sub>E # \<sigma>'' \<in> tocks UNIV"
  then have "False"
    using ttWF.simps(12) tocks_wf by blast
  then show "\<rho> \<lesssim>\<^sub>C [X]\<^sub>R # [Tick]\<^sub>E # \<sigma>''"
    by auto
next
  fix X e \<rho> \<sigma>''
  assume "[X]\<^sub>R # [Event e]\<^sub>E # \<sigma>'' \<in> tocks UNIV"
  then have "False"
    by (meson ttWF.simps(11) tocks_wf)
  then show "\<rho> \<lesssim>\<^sub>C [X]\<^sub>R # [Event e]\<^sub>E # \<sigma>''"
    by auto
next
  fix X Y \<rho> \<sigma>''
  assume "[X]\<^sub>R # [Y]\<^sub>R # \<sigma>'' \<in> tocks UNIV"
  then have "False"
    using ttWF.simps(13) tocks_wf by blast
  then show "\<rho> \<lesssim>\<^sub>C [X]\<^sub>R # [Y]\<^sub>R # \<sigma>''"
    by auto
next
  fix x \<rho> \<sigma>''
  assume "[Tick]\<^sub>E # x # \<rho> \<in> tocks UNIV"
  then have "False"
    using ttWF.simps(10) tocks_wf by blast
  then show "[Tick]\<^sub>E # x # \<rho> \<lesssim>\<^sub>C \<sigma>''"
    by auto
next
  fix y \<rho> \<sigma>''
  assume "[Tick]\<^sub>E # y # \<sigma>'' \<in> tocks UNIV"
  then have "False"
    using ttWF.simps(10) tocks_wf by blast
  then show "\<rho> \<lesssim>\<^sub>C [Tick]\<^sub>E # y # \<sigma>''"
    by auto
next
  fix \<rho> \<sigma>''
  assume "[Tock]\<^sub>E # \<rho> \<in> tocks UNIV"
  then have "False"
    using ttWF.simps(6) tocks_wf by blast
  then show "[Tock]\<^sub>E # \<rho> \<lesssim>\<^sub>C \<sigma>''"
    by auto
next
  fix \<rho> \<sigma>''
  assume "[Tock]\<^sub>E # \<sigma>'' \<in> tocks UNIV"
  then have "False"
    using ttWF.simps(6) tocks_wf by blast
  then show "\<rho> \<lesssim>\<^sub>C [Tock]\<^sub>E # \<sigma>''"
    by auto
qed

lemma longest_pretocks_ctt_prefix_subset_split:
  assumes "\<rho> \<in> tocks UNIV" "\<forall>t\<in>tocks UNIV. t \<le>\<^sub>C \<rho> @ \<sigma> \<longrightarrow> t \<le>\<^sub>C \<rho>"
  shows "\<exists>\<rho>' \<sigma>'. \<rho>' \<in> tocks UNIV \<and> 
    (\<forall>t\<in>tocks UNIV. t \<le>\<^sub>C \<rho>' @ \<sigma>' \<longrightarrow> t \<le>\<^sub>C \<rho>') \<and> 
    \<rho>' @ \<sigma>' \<lesssim>\<^sub>C \<rho> @ \<sigma> \<and> 
    (\<sigma>' \<lesssim>\<^sub>C \<sigma> \<or> (\<exists> X. \<sigma>' \<lesssim>\<^sub>C [X]\<^sub>R # \<sigma>))"
proof (insert assms, simp_all)
  thm ctt_prefix_subset_tocks
  obtain \<rho>' where \<rho>'_assms: "\<rho>' \<in> tocks UNIV" "(\<rho>' \<lesssim>\<^sub>C \<rho>) \<or> (\<exists>Y. \<rho>' @ [[Y]\<^sub>R] \<lesssim>\<^sub>C \<rho>)"
    using assms(1) ctt_prefix_subset_refl by blast
  obtain \<sigma>' where \<sigma>'_assms: "\<sigma>' \<lesssim>\<^sub>C \<sigma>"
    using ctt_prefix_subset.simps(1) by blast
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
      using assm2 ctt_prefix_concat ctt_prefix_subset_ctt_prefix_trans by blast
  next
    fix Y
    assume assm1: "\<rho>' \<in> tocks UNIV"
    assume assm2: "\<sigma>' \<lesssim>\<^sub>C \<sigma>"
    assume assm3: "\<rho>' @ [[Y]\<^sub>R] \<lesssim>\<^sub>C \<rho>"
    show "\<exists>\<rho>'. \<rho>' \<in> tocks UNIV \<and>
         (\<exists>\<sigma>'. (\<forall>t\<in>tocks UNIV. t \<le>\<^sub>C \<rho>' @ \<sigma>' \<longrightarrow> t \<le>\<^sub>C \<rho>') \<and> \<rho>' @ \<sigma>' \<lesssim>\<^sub>C \<rho> @ \<sigma> \<and> (\<sigma>' \<lesssim>\<^sub>C \<sigma> \<or> (\<exists>X. \<sigma>' \<lesssim>\<^sub>C [X]\<^sub>R # \<sigma>)))"
      apply (rule_tac x="\<rho>'" in exI, simp add: assm1)
      apply (rule_tac x="[[Y]\<^sub>R]" in exI, auto)
      apply (metis butlast_append butlast_snoc ctt_prefix_concat ctt_prefix_decompose end_refusal_notin_tocks)
      using assm3 ctt_prefix_concat ctt_prefix_subset_ctt_prefix_trans by blast
  qed
qed

lemma tocks_ctt_subset_exists:
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

lemma tocks_ctt_subset_exists2:
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

lemma ctt_subset_longest_tocks:
  assumes "ttWF (\<rho>' @ \<sigma>')" "ttWF (\<rho> @ \<sigma>)"
  assumes "\<rho> \<in> tocks X" "\<forall> t\<in>tocks UNIV. t \<le>\<^sub>C \<rho> @ \<sigma> \<longrightarrow> t \<le>\<^sub>C \<rho>"
  assumes "\<rho>' \<in> tocks X" "\<forall> t\<in>tocks UNIV. t \<le>\<^sub>C \<rho>' @ \<sigma>' \<longrightarrow> t \<le>\<^sub>C \<rho>'"
  assumes "\<rho>' @ \<sigma>' \<subseteq>\<^sub>C \<rho> @ \<sigma>"  
  shows "\<rho>' \<subseteq>\<^sub>C \<rho> \<and> \<sigma>' \<subseteq>\<^sub>C \<sigma>"
proof -
  obtain \<rho>'' where \<rho>''_assms: "\<rho>''\<in> tocks X \<and> \<rho>'' \<subseteq>\<^sub>C \<rho> \<and> \<rho>'' \<le>\<^sub>C \<rho>' @ \<sigma>'"
    using assms(1) assms(2) assms(3) assms(7) tocks_ctt_subset_exists by blast
  then have 1: "\<rho>'' \<le>\<^sub>C \<rho>'"
    by (meson assms(6) subset_UNIV tocks_subset)
  obtain \<rho>''' where \<rho>'''_assms: "\<rho>''' \<in> tocks UNIV \<and> \<rho>' \<subseteq>\<^sub>C \<rho>''' \<and> \<rho>''' \<le>\<^sub>C \<rho> @ \<sigma>"
    using assms(1) assms(2) assms(5) assms(7) tocks_ctt_subset_exists2 by blast
  then have 2: "\<rho>''' \<le>\<^sub>C \<rho>"
    by (meson assms(4) subset_UNIV tocks_subset)
  have 3: "length \<rho>' = length \<rho>'''"
    using \<rho>'''_assms ctt_subset_same_length by blast
  have 4: "length \<rho> = length \<rho>''"
    using \<rho>''_assms ctt_subset_same_length by fastforce
  have 5: "length \<rho> \<le> length \<rho>'"
    by (simp add: "1" "4" ctt_prefix_imp_prefix_subset ctt_prefix_subset_length)
  have 6: "length \<rho>' \<le> length \<rho>"
    by (simp add: "2" "3" ctt_prefix_imp_prefix_subset ctt_prefix_subset_length)
  have "length \<rho>' = length \<rho>"
    using 5 6 by auto
  then have "\<rho>' \<subseteq>\<^sub>C \<rho>"
    using assms(3) assms(5) assms(7) apply (induct \<rho>' \<rho> rule:ttWF2.induct)
    using tocks.cases by (auto simp add: notin_tocks)
  then show "\<rho>' \<subseteq>\<^sub>C \<rho> \<and> \<sigma>' \<subseteq>\<^sub>C \<sigma>"
    using assms(7) ctt_subset_remove_start by auto
qed

lemma ctt_subset_in_tocks:
  "t \<in> tocks X \<Longrightarrow> t' \<subseteq>\<^sub>C t \<Longrightarrow> t' \<in> tocks X"
proof (induct t' t rule:ttWF2.induct, auto simp add: notin_tocks)
  fix Xa \<rho> Y \<sigma>
  assume assms: "[Y]\<^sub>R # [Tock]\<^sub>E # \<sigma> \<in> tocks X" "Xa \<subseteq> Y" "\<sigma> \<in> tocks X \<Longrightarrow> \<rho> \<in> tocks X"
  then have "\<sigma> \<in> tocks X \<and> Y \<subseteq> X"
    by (metis cttobs.inject(2) list.inject list.simps(3) tocks.simps)
  then have "\<rho> \<in> tocks X \<and> Xa \<subseteq> X"
    using assms(2) assms(3) by blast
  then show "[Xa]\<^sub>R # [Tock]\<^sub>E # \<rho> \<in> tocks X"
    using tocks.tock_insert_in_tocks by blast
next
  fix Xa \<rho> \<sigma>
  assume assms: "\<sigma> \<in> tocks X" "[Xa]\<^sub>R # [Tick]\<^sub>E # \<rho> \<subseteq>\<^sub>C \<sigma>"
  then obtain \<sigma>' Y where "\<sigma> = [Y]\<^sub>R # [Tick]\<^sub>E # \<sigma>'"
    using ttWF.simps(12) ctt_prefix_subset_ttWF ctt_subset_imp_prefix_subset tocks_wf by blast
  then show False
    using assms(1) second_tick_notin_tocks by blast
next
  fix Xa e \<rho> \<sigma>
  assume assms: "\<sigma> \<in> tocks X" "[Xa]\<^sub>R # [Event e]\<^sub>E # \<rho> \<subseteq>\<^sub>C \<sigma>"
  then obtain \<sigma>' Y where "\<sigma> = [Y]\<^sub>R # [Event e]\<^sub>E # \<sigma>'"
    by (meson ttWF.simps(11) ctt_prefix_subset_ttWF ctt_subset_imp_prefix_subset tocks_wf)
  then show False
    using assms(1) second_event_notin_tocks by force
next
  fix Xa Y \<rho> \<sigma>
  assume assms: "\<sigma> \<in> tocks X" "[Xa]\<^sub>R # [Y]\<^sub>R # \<rho> \<subseteq>\<^sub>C \<sigma>"
  then obtain \<sigma>' Z W where "\<sigma> = [Z]\<^sub>R # [W]\<^sub>R # \<sigma>'"
    using ttWF.simps(13) ctt_prefix_subset_ttWF ctt_subset_imp_prefix_subset tocks_wf by blast
  then show False
    using assms(1) double_refusal_start_notin_tocks by blast
next
  fix x \<rho> \<sigma>
  assume assms: "\<sigma> \<in> tocks X" "[Tick]\<^sub>E # x # \<rho> \<subseteq>\<^sub>C \<sigma>"
  then obtain \<sigma>' where "\<sigma> = [Tick]\<^sub>E # x # \<sigma>'"
    using ttWF.simps(8) ctt_prefix_subset_ttWF ctt_subset_imp_prefix_subset tocks_wf by blast
  then show False
    using assms(1) start_tick_notin_tocks by blast
next
  fix \<rho> \<sigma>
  assume assms: "\<sigma> \<in> tocks X" "[Tock]\<^sub>E # \<rho> \<subseteq>\<^sub>C \<sigma>"
  then obtain \<sigma>' where "\<sigma> = [Tock]\<^sub>E # \<sigma>'"
    by (metis ctt_subset.simps(5) ctt_subset.simps(6) tocks.simps)
  then show False
    using assms(1) start_tock_notin_tocks by blast
qed

lemma ctt_subset_in_tocks2:
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

lemma ctt_subset_longest_tocks2:
  "\<forall> t\<in>tocks UNIV. t \<le>\<^sub>C s1 @ s2  \<longrightarrow> t \<le>\<^sub>C s1 \<Longrightarrow> s2' \<subseteq>\<^sub>C s2 \<Longrightarrow> \<forall> t\<in>tocks UNIV. t \<le>\<^sub>C s1 @ s2' \<longrightarrow> t \<le>\<^sub>C s1"
proof auto
  fix t
  assume assms: "\<forall>t\<in>tocks UNIV. t \<le>\<^sub>C s1 @ s2 \<longrightarrow> t \<le>\<^sub>C s1" "s2' \<subseteq>\<^sub>C s2" "t \<in> tocks UNIV" "t \<le>\<^sub>C s1 @ s2'"
  then obtain t' where t'_assms: "t \<subseteq>\<^sub>C t' \<and> t' \<le>\<^sub>C s1 @ s2"
    by (meson ctt_prefix_ctt_prefix_subset_trans ctt_prefix_subset_imp_ctt_subset_ctt_prefix ctt_subset_combine ctt_subset_imp_prefix_subset ctt_subset_refl)
  then have "t' \<in> tocks UNIV"
    using assms(3) ctt_subset_in_tocks2 by blast
  then have "t' \<le>\<^sub>C s1"
    by (simp add: assms(1) t'_assms)
  then show "t \<le>\<^sub>C s1"
    by (metis assms(4) ctt_prefix_append_split ctt_prefix_concat ctt_prefix_imp_prefix_subset ctt_prefix_subset_antisym ctt_prefix_subset_ctt_prefix_trans ctt_subset_imp_prefix_subset t'_assms)
qed

lemma ctt_subset_longest_tocks3:
  "\<forall> t\<in>tocks UNIV. t \<le>\<^sub>C s1 @ s2  \<longrightarrow> t \<le>\<^sub>C s1 \<Longrightarrow> s2 \<subseteq>\<^sub>C s2' \<Longrightarrow> \<forall> t\<in>tocks UNIV. t \<le>\<^sub>C s1 @ s2' \<longrightarrow> t \<le>\<^sub>C s1"
proof auto
  fix t
  assume assms: "\<forall>t\<in>tocks UNIV. t \<le>\<^sub>C s1 @ s2 \<longrightarrow> t \<le>\<^sub>C s1" "s2 \<subseteq>\<^sub>C s2'" "t \<in> tocks UNIV" "t \<le>\<^sub>C s1 @ s2'"
  then obtain t' where t'_assms: "t' \<subseteq>\<^sub>C t \<and> t' \<le>\<^sub>C s1 @ s2"
    by (meson ctt_prefix_ctt_subset ctt_subset_combine ctt_subset_refl)
  then have "t' \<in> tocks UNIV"
    using assms(3) ctt_subset_in_tocks by blast
  then have "t' \<le>\<^sub>C s1"
    by (simp add: assms(1) t'_assms)
  then show "t \<le>\<^sub>C s1"
    by (smt append_assoc append_eq_append_conv assms(4) ctt_prefix_split ctt_subset_same_length t'_assms)
qed

lemma ctt_subset_longest_tocks4:
  "\<And> s1'. \<forall> t\<in>tocks UNIV. t \<le>\<^sub>C s1 @ s2  \<longrightarrow> t \<le>\<^sub>C s1 \<Longrightarrow> s1 \<subseteq>\<^sub>C s1' \<Longrightarrow> \<forall> t\<in>tocks UNIV. t \<le>\<^sub>C s1' @ s2 \<longrightarrow> t \<le>\<^sub>C s1'"
proof (safe, induct s1 rule:ttWF.induct)
  fix t s1'
  assume assms: "\<forall>t\<in>tocks UNIV. t \<le>\<^sub>C [] @ s2 \<longrightarrow> t \<le>\<^sub>C []" "[] \<subseteq>\<^sub>C s1'" "t \<in> tocks UNIV" "t \<le>\<^sub>C s1' @ s2"
  then have "s1' = []"
    using ctt_subset_same_length by force
  then show "t \<le>\<^sub>C s1'"
    using assms(1) assms(3) assms(4) by auto
next
  fix X s1' t
  assume assms: "\<forall>t\<in>tocks UNIV. t \<le>\<^sub>C [[X]\<^sub>R] @ s2 \<longrightarrow> t \<le>\<^sub>C [[X]\<^sub>R]" "[[X]\<^sub>R] \<subseteq>\<^sub>C s1'" "t \<in> tocks UNIV" "t \<le>\<^sub>C s1' @ s2"
  then obtain Y where s1'_def: "s1' = [[Y]\<^sub>R]"
    by (cases s1' rule:ttWF.cases, auto)
  then have "t = [] \<or> (\<exists> ta. t = [Y]\<^sub>R # ta)"
    using assms(4) ctt_prefix.elims(2) by auto
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
    using assms(4) ctt_prefix.elims(2) by auto
  then show "t \<le>\<^sub>C s1'"
    using assms(3) start_tick_notin_tocks by auto
next
  fix e \<sigma> s1' t
  assume assms: "[Event e]\<^sub>E # \<sigma> \<subseteq>\<^sub>C s1'" "t \<in> tocks UNIV" "t \<le>\<^sub>C s1' @ s2"
  then obtain s1'a where s1'_def: "s1' = [Event e]\<^sub>E # s1'a"
    by (cases s1' rule:ttWF.cases, auto)
  then have "t = [] \<or> (\<exists> ta. t = [Event e]\<^sub>E # ta)"
    using assms(3) ctt_prefix.elims(2) by auto
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
    using assms(2) ttWF.simps(6) tocks_wf by (auto, blast)
next
  fix va s1' t
  assume assms: "[Tock]\<^sub>E # va \<subseteq>\<^sub>C s1'" "t \<in> tocks UNIV" "t \<le>\<^sub>C s1' @ s2"
  then obtain s1'a where "s1' = [Tock]\<^sub>E # s1'a"
    by (cases s1' rule:ttWF.cases, auto)
  then have "t = [] \<or> (\<exists> ta. t = [Tock]\<^sub>E # ta)"
    using assms(3) by (cases t rule:ttWF.cases, auto)
  then show "t \<le>\<^sub>C s1'"
    using assms(2) ttWF.simps(6) tocks_wf by (auto, blast)
next
  fix va s1' t
  assume assms: "[Tock]\<^sub>E # va \<subseteq>\<^sub>C s1'" "t \<in> tocks UNIV" "t \<le>\<^sub>C s1' @ s2"
  then obtain s1'a where "s1' = [Tock]\<^sub>E # s1'a"
    by (cases s1' rule:ttWF.cases, auto)
  then have "t = [] \<or> (\<exists> ta. t = [Tock]\<^sub>E # ta)"
    using assms(3) by (cases t rule:ttWF.cases, auto)
  then show "t \<le>\<^sub>C s1'"
    using assms(2) ttWF.simps(6) tocks_wf by (auto, blast)
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

lemma tocks_ctt_subset1:
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
    using ttWF.simps(12) ctt_prefix_subset_ttWF ctt_subset_imp_prefix_subset tocks_wf by blast
next
  fix Xa e \<rho> \<sigma>
  show "\<sigma> \<in> tocks X \<Longrightarrow> [Xa]\<^sub>R # [Event e]\<^sub>E # \<rho> \<subseteq>\<^sub>C \<sigma> \<Longrightarrow> False"
    by (meson ttWF.simps(11) ctt_prefix_subset_ttWF ctt_subset_imp_prefix_subset tocks_wf)
next
  fix Xa Y \<rho> \<sigma>
  show "\<sigma> \<in> tocks X \<Longrightarrow> [Xa]\<^sub>R # [Y]\<^sub>R # \<rho> \<subseteq>\<^sub>C \<sigma> \<Longrightarrow> False"
    using ttWF.simps(13) ctt_prefix_subset_ttWF ctt_subset_imp_prefix_subset tocks_wf by blast
next
  fix x \<rho> \<sigma>
  show "\<sigma> \<in> tocks X \<Longrightarrow> [Tick]\<^sub>E # x # \<rho> \<subseteq>\<^sub>C \<sigma> \<Longrightarrow> False"
    using ttWF.simps(8) ctt_prefix_subset_ttWF ctt_subset_imp_prefix_subset tocks_wf by blast
next
  fix \<rho> \<sigma>
  show "\<sigma> \<in> tocks X \<Longrightarrow> [Tock]\<^sub>E # \<rho> \<subseteq>\<^sub>C \<sigma> \<Longrightarrow> False"
    using ttWF.simps(6) ctt_prefix_subset_ttWF ctt_subset_imp_prefix_subset tocks_wf by blast
qed

lemma tocks_ctt_subset2:
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
    by (metis ttWF.simps(12) ctt_subset.simps(2) ctt_subset.simps(3) ctt_subset.simps(8) tocks.simps tocks_wf)
next
  fix Xa e \<rho> \<sigma>
  show "\<rho> \<in> tocks X \<Longrightarrow> \<rho> \<subseteq>\<^sub>C [Xa]\<^sub>R # [Event e]\<^sub>E # \<sigma> \<Longrightarrow> False"
    by (metis ctt_subset.simps(2) ctt_subset.simps(3) ctt_subset.simps(8) second_event_notin_tocks tocks.cases)
next
  fix Xa Y \<rho> \<sigma>
  show "\<rho> \<in> tocks X \<Longrightarrow> \<rho> \<subseteq>\<^sub>C [Xa]\<^sub>R # [Y]\<^sub>R # \<sigma> \<Longrightarrow> False"
    by (metis ctt_subset.simps(2) ctt_subset.simps(8) ctt_subset.simps(9) tocks.simps)
next
  fix y \<rho> \<sigma>
  show "\<rho> \<in> tocks X \<Longrightarrow> \<rho> \<subseteq>\<^sub>C [Tick]\<^sub>E # y # \<sigma> \<Longrightarrow> False"
    by (metis ctt_subset.simps(11) ctt_subset.simps(8) tocks.cases)
next
  fix \<rho> \<sigma>
  show "\<rho> \<in> tocks X \<Longrightarrow> \<rho> \<subseteq>\<^sub>C [Tock]\<^sub>E # \<sigma> \<Longrightarrow> False"
    by (metis ctt_subset.simps(10) ctt_subset.simps(11) tocks.simps)
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

lemma TT2_tocks: "TT2 (tocks X)"
  unfolding TT2_def by (simp add: end_refusal_notin_tocks)

lemma TT3_tocks: "Tock \<notin> X \<Longrightarrow> TT3 (tocks X)"
  unfolding TT3_def
proof auto
  fix x
  show "Tock \<notin> X \<Longrightarrow> x \<in> tocks X \<Longrightarrow> TT3_trace x"
    using tocks.cases by (induct rule:TT3_trace.induct, auto)
qed

lemma TT4s_tocks: "Tick \<in> X \<Longrightarrow> TT4s (tocks X)"
  unfolding TT4s_def
proof auto
  fix \<rho>
  assume assm: "Tick \<in> X"
  show "\<rho> \<in> tocks X \<Longrightarrow> add_Tick_refusal_trace \<rho> \<in> tocks X"
    by (induct \<rho> rule:tocks.induct, auto simp add: assm tocks.empty_in_tocks tocks.tock_insert_in_tocks)
qed

section {* Refinement *}

definition RefinesTT :: "'e cttobs list set \<Rightarrow> 'e cttobs list set \<Rightarrow> bool" (infix "\<sqsubseteq>\<^sub>C" 50) where
  "P \<sqsubseteq>\<^sub>C Q = (Q \<subseteq> P)"

end