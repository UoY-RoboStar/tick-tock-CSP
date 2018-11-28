theory CTockTick_Core
  imports Main
begin

section {* Types and Wellformedness Conditions *}

datatype 'e cttevent = Event 'e  | Tock | Tick
datatype 'e cttobs = ObsEvent "'e cttevent" ("[_]\<^sub>E") | Ref "'e cttevent set" ("[_]\<^sub>R") (*| TockRef "'e cttevent set" ("[_]\<^sub>T")*)

fun cttWF :: "'e cttobs list \<Rightarrow> bool" where
  "cttWF [] = True" | (* an empty trace is okay*)
  "cttWF [[X]\<^sub>R] = True" | (* a refusal at the end of a trace is okay *)
  "cttWF [[Tick]\<^sub>E] = True" | (* a tick at the end of a trace is okay *)
  "cttWF ([Event e]\<^sub>E # \<sigma>) = cttWF \<sigma>" | (* a (non-tick, non-tock) event is okay *)
  "cttWF ([X]\<^sub>R # [Tock]\<^sub>E # \<sigma>) = cttWF \<sigma>" | (* a tock event on its own is okay *)
  "cttWF \<sigma> = False" (* everything else is not allowed *)  

(* not necessary as a function but very useful for its induction rule *)
function cttWF2 :: "'e cttobs list \<Rightarrow> 'e cttobs list \<Rightarrow> bool" where
  "cttWF2 [] [] = True" | 
  "cttWF2 [] [[Y]\<^sub>R] = True" | 
  "cttWF2 [] [[Tick]\<^sub>E] = True" | 
  "cttWF2 [] ([Event f]\<^sub>E # \<sigma>) = cttWF2 [] \<sigma>" | 
  "cttWF2 [] ([Y]\<^sub>R # [Tock]\<^sub>E # \<sigma>) = cttWF2 [] \<sigma>" | 
  "cttWF2 [[X]\<^sub>R] [] = True" | 
  "cttWF2 [[X]\<^sub>R] [[Y]\<^sub>R] = True" | 
  "cttWF2 [[X]\<^sub>R] [[Tick]\<^sub>E] = True" | 
  "cttWF2 [[X]\<^sub>R] ([Event f]\<^sub>E # \<sigma>) = cttWF2 [] \<sigma>" | 
  "cttWF2 [[X]\<^sub>R] ([Y]\<^sub>R # [Tock]\<^sub>E # \<sigma>) = cttWF2 [] \<sigma>" | 
  "cttWF2 [[Tick]\<^sub>E] [] = True" | 
  "cttWF2 [[Tick]\<^sub>E] [[Y]\<^sub>R] = True" | 
  "cttWF2 [[Tick]\<^sub>E] [[Tick]\<^sub>E] = True" | 
  "cttWF2 [[Tick]\<^sub>E] ([Event f]\<^sub>E # \<sigma>) = cttWF2 [] \<sigma>" | 
  "cttWF2 [[Tick]\<^sub>E] ([Y]\<^sub>R # [Tock]\<^sub>E # \<sigma>) = cttWF2 [] \<sigma>" | 
  "cttWF2 ([Event e]\<^sub>E # \<sigma>) [] = cttWF2 \<sigma> []" | 
  "cttWF2 ([Event e]\<^sub>E # \<sigma>) [[Y]\<^sub>R] = cttWF2 \<sigma> []" | 
  "cttWF2 ([Event e]\<^sub>E # \<sigma>) [[Tick]\<^sub>E] = cttWF2 \<sigma> []" | 
  "cttWF2 ([Event e]\<^sub>E # \<rho>) ([Event f]\<^sub>E # \<sigma>) = cttWF2 \<rho> \<sigma>" | 
  "cttWF2 ([Event e]\<^sub>E # \<rho>) ([Y]\<^sub>R # [Tock]\<^sub>E # \<sigma>) = cttWF2 \<rho> \<sigma>" | 
  "cttWF2 ([X]\<^sub>R # [Tock]\<^sub>E # \<sigma>) [] = cttWF2 \<sigma> []" | 
  "cttWF2 ([X]\<^sub>R # [Tock]\<^sub>E # \<sigma>) [[Y]\<^sub>R] = cttWF2 \<sigma> []" | 
  "cttWF2 ([X]\<^sub>R # [Tock]\<^sub>E # \<sigma>) [[Tick]\<^sub>E] = cttWF2 \<sigma> []" | 
  "cttWF2 ([X]\<^sub>R # [Tock]\<^sub>E # \<rho>) ([Event f]\<^sub>E # \<sigma>) = cttWF2 \<rho> \<sigma>" | 
  "cttWF2 ([X]\<^sub>R # [Tock]\<^sub>E # \<rho>) ([Y]\<^sub>R # [Tock]\<^sub>E # \<sigma>) = cttWF2 \<rho> \<sigma>" |
  "cttWF2 ([X]\<^sub>R # [Tick]\<^sub>E # \<rho>) \<sigma> = False" |
  "cttWF2 ([X]\<^sub>R # [Event e]\<^sub>E # \<rho>) \<sigma> = False" |
  "cttWF2 ([X]\<^sub>R # [Y]\<^sub>R # \<rho>) \<sigma> = False" |
  "cttWF2 \<rho> ([X]\<^sub>R # [Tick]\<^sub>E # \<sigma>) = False" |
  "cttWF2 \<rho> ([X]\<^sub>R # [Event e]\<^sub>E # \<sigma>) = False" |
  "cttWF2 \<rho> ([X]\<^sub>R # [Y]\<^sub>R # \<sigma>) = False" |
  "cttWF2 ([Tick]\<^sub>E # x # \<rho>) \<sigma> = False" |
  "cttWF2 \<rho> ([Tick]\<^sub>E # y # \<sigma>) = False" |
  "cttWF2 ([Tock]\<^sub>E # \<rho>) \<sigma> = False" |
  "cttWF2 \<rho> ([Tock]\<^sub>E # \<sigma>) = False"
  by (pat_completeness, simp_all)
termination by lexicographic_order

print_theorems

lemma cttWF2_cttWF: "cttWF2 x y = (cttWF x \<and> cttWF y)"
  by (induct rule:cttWF2.induct, auto)

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

lemma ctt_prefix_subset_cttWF: "cttWF s \<Longrightarrow> t \<lesssim>\<^sub>C s \<Longrightarrow> cttWF t"
  by (induct rule:cttWF2.induct, auto, (case_tac \<rho> rule:cttWF.cases, auto)+)

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

lemma cttWF_prefix_is_cttWF: "cttWF (s @ t) \<Longrightarrow> cttWF s"
  using ctt_prefix_concat ctt_prefix_imp_prefix_subset ctt_prefix_subset_cttWF by blast

lemma cttWF_end_refusal_prefix_subset: "cttWF (s @ [[X]\<^sub>R]) \<Longrightarrow> t \<lesssim>\<^sub>C s @ [[X]\<^sub>R] \<Longrightarrow> 
  (\<exists> r Y. t = r @ [[Y]\<^sub>R]) \<or> (\<exists> r Y. t = r @ [[Y]\<^sub>R, [Tock]\<^sub>E]) \<or> (\<exists> r e. t = r @ [[Event e]\<^sub>E]) \<or> t = []"
  apply (induct s t rule:cttWF2.induct, auto)
  using cttWF.simps(12) ctt_prefix_subset_cttWF apply blast
  apply (meson cttWF.simps(11) ctt_prefix_subset_cttWF)
  using cttWF.simps(13) ctt_prefix_subset_cttWF apply blast
  using cttWF.simps(8) ctt_prefix_subset_cttWF apply blast
  using cttWF.simps(6) ctt_prefix_subset_cttWF by blast

lemma cttWF_end_Event_prefix_subset: "cttWF (s @ [[Event e]\<^sub>E]) \<Longrightarrow> t \<lesssim>\<^sub>C s @ [[Event e]\<^sub>E] \<Longrightarrow> 
  (\<exists> r Y. t = r @ [[Y]\<^sub>R]) \<or> (\<exists> r Y. t = r @ [[Y]\<^sub>R, [Tock]\<^sub>E]) \<or> (\<exists> r e. t = r @ [[Event e]\<^sub>E]) \<or> t = []"
  apply (induct s t rule:cttWF2.induct, auto)
  using ctt_prefix_subset_antisym apply fastforce
  using cttWF.simps(12) ctt_prefix_subset_cttWF apply blast
  apply (meson cttWF.simps(11) ctt_prefix_subset_cttWF)
  using cttWF.simps(13) ctt_prefix_subset_cttWF apply blast
  using cttWF.simps(8) ctt_prefix_subset_cttWF apply blast
  using cttWF.simps(6) ctt_prefix_subset_cttWF by blast

lemma cttWF_end_Tock_prefix_subset: "cttWF (s @ [[Tock]\<^sub>E]) \<Longrightarrow> t \<lesssim>\<^sub>C s @ [[Tock]\<^sub>E] \<Longrightarrow> 
  (\<exists> r Y. t = r @ [[Y]\<^sub>R]) \<or> (\<exists> r Y. t = r @ [[Y]\<^sub>R, [Tock]\<^sub>E]) \<or> (\<exists> r e. t = r @ [[Event e]\<^sub>E]) \<or> t = []"
  apply (induct s t rule:cttWF2.induct, auto)
  using ctt_prefix_subset_antisym apply fastforce
  using cttWF.simps(12) ctt_prefix_subset_cttWF apply blast
  apply (meson cttWF.simps(11) ctt_prefix_subset_cttWF)
  using cttWF.simps(13) ctt_prefix_subset_cttWF apply blast
  using cttWF.simps(8) ctt_prefix_subset_cttWF apply blast
  using cttWF.simps(6) ctt_prefix_subset_cttWF by blast

lemma cttWF_cons_hd_not_Tock_then_cttWF:
  assumes "cttWF (a # fl)" "hd fl \<noteq> [Tock]\<^sub>E"
  shows "cttWF fl"
  by (metis (no_types, lifting) assms(1) assms(2) cttWF.elims(2) cttWF.simps(1) list.discI list.inject list.sel(1))

lemma cttWF_dist_cons_refusal: 
  assumes "cttWF (s @ [[S]\<^sub>R,x])"
  shows "cttWF [[S]\<^sub>R,x]"
  using assms by(induct s rule:cttWF.induct, auto)

section {* Healthiness Conditions *}

definition CT0 :: "'e cttobs list set \<Rightarrow> bool" where
  "CT0 P = (P \<noteq> {})"

definition CT1c :: "'e cttobs list set \<Rightarrow> bool" where
  "CT1c P = (\<forall> \<rho> \<sigma>. (\<rho> \<le>\<^sub>C \<sigma> \<and> \<sigma> \<in> P) \<longrightarrow> \<rho> \<in> P)"

definition CT1 :: "'e cttobs list set \<Rightarrow> bool" where
  "CT1 P = (\<forall> \<rho> \<sigma>. (\<rho> \<lesssim>\<^sub>C \<sigma> \<and> \<sigma> \<in> P) \<longrightarrow> \<rho> \<in> P)"

definition CT2 :: "'e cttobs list set \<Rightarrow> bool" where
  "CT2 P = (\<forall> \<rho> X Y. (\<rho> @ [[X]\<^sub>R] \<in> P \<and> (Y \<inter> {e. (e \<noteq> Tock \<and> \<rho> @ [[e]\<^sub>E] \<in> P) \<or> (e = Tock \<and> \<rho> @ [[X]\<^sub>R, [e]\<^sub>E] \<in> P) } = {}))
     \<longrightarrow> \<rho> @ [[X \<union> Y]\<^sub>R] \<in> P)"

fun CT3_trace :: "'e cttobs list \<Rightarrow> bool" where
  "CT3_trace [] = True" |
  "CT3_trace [x] = True" |
  "CT3_trace ([X]\<^sub>R # [Tock]\<^sub>E # \<rho>) = (Tock \<notin> X \<and> CT3_trace \<rho>)" |
  "CT3_trace ([va]\<^sub>E # vb # vc) = CT3_trace (vb # vc)" |
  "CT3_trace (v # [Event vd]\<^sub>E # vc) = CT3_trace ([Event vd]\<^sub>E # vc)" |
  "CT3_trace (v # [Tick]\<^sub>E # vc) = CT3_trace ([Tick]\<^sub>E # vc)" |
  "CT3_trace ([vb]\<^sub>R # [va]\<^sub>R # vc) = CT3_trace ([va]\<^sub>R # vc)"

definition CT3 :: "'e cttobs list set \<Rightarrow> bool" where
  "CT3 P = (\<forall>\<rho>\<in>P. CT3_trace \<rho>)"

lemma CT3_append: "cttWF t \<Longrightarrow> CT3_trace s \<Longrightarrow> CT3_trace t \<Longrightarrow> CT3_trace (s @ t)"
  apply (induct s rule:CT3_trace.induct, auto)
  apply (induct t, auto)
  apply (case_tac x, auto, case_tac a, auto, case_tac x1, auto)
  done

lemma CT3_end_tock: "CT3_trace (\<rho>) \<Longrightarrow> CT3 P \<Longrightarrow> \<rho> @ [[X]\<^sub>R, [Tock]\<^sub>E] \<in> P \<Longrightarrow> Tock \<notin> X"
proof -
  assume "CT3 P" "\<rho> @ [[X]\<^sub>R, [Tock]\<^sub>E] \<in> P"
  then have "CT3_trace (\<rho> @ [[X]\<^sub>R, [Tock]\<^sub>E])"
    unfolding CT3_def by auto 
  then show "CT3_trace (\<rho>) \<Longrightarrow> Tock \<notin> X"
    by (auto, induct \<rho> rule:CT3_trace.induct, auto, case_tac x, auto)
qed

lemma CT3_trace_cons_left:
  "CT3_trace (xs @ ys) \<Longrightarrow> CT3_trace xs"
  by (induct xs rule:CT3_trace.induct, auto)

lemma CT3_trace_cons_right:
  "CT3_trace (xs @ ys) \<Longrightarrow> CT3_trace ys"
  apply (induct xs rule:CT3_trace.induct, auto)
  apply (case_tac x, auto)
   apply (case_tac x1, auto)
  apply (metis CT3_trace.elims(3) CT3_trace.simps(4))
  apply (metis CT3_trace.elims(3) CT3_trace.simps(4))
  apply (metis CT3_trace.elims(3) CT3_trace.simps(4))
  using CT3_trace.elims(2) CT3_trace.elims(3) list.discI by auto

lemma CT3_any_cons_end_tock:
  assumes "CT3 P" "\<rho> @ [[X]\<^sub>R, [Tock]\<^sub>E] \<in> P"
  shows "Tock \<notin> X"
proof -
  have "CT3_trace ([[X]\<^sub>R, [Tock]\<^sub>E])"
    using assms CT3_def CT3_trace_cons_right by blast
  then show ?thesis
    by simp
qed

lemma CT3_trace_end_refusal_change:
  "CT3_trace (t @ [[X]\<^sub>R]) \<Longrightarrow> CT3_trace (t @ [[Y]\<^sub>R])"
  by (induct t rule:CT3_trace.induct, auto, case_tac x, auto)

lemma CT3_trace_cons_imp_cons [simp]:
  assumes "CT3_trace (a # fl)"
  shows "CT3_trace fl"
  using assms apply (cases a, auto)
  apply(induct fl rule:CT3_trace.induct, auto)
  apply(induct fl rule:CT3_trace.induct, auto)
  by (case_tac va, auto)

(*definition CT4 :: "'e cttobs list set \<Rightarrow> bool" where
  "CT4 P = (\<forall> \<rho>. \<rho> @ [[Tick]\<^sub>E] \<in> P \<longrightarrow> (\<nexists> X. \<rho> @ [[X]\<^sub>R] \<in> P))"*)

definition CT4 :: "'e cttobs list set \<Rightarrow> bool" where
"CT4 P = (\<forall> \<rho> X. \<rho> @ [[X]\<^sub>R] \<in> P \<longrightarrow> \<rho> @ [[X \<union> {Tick}]\<^sub>R] \<in> P)"

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

lemma add_Tick_refusal_trace_ctt_subset:
  "\<rho> \<subseteq>\<^sub>C add_Tick_refusal_trace \<rho>"
  by (induct \<rho> rule:add_Tick_refusal_trace.induct, auto)

lemma add_Tick_refusal_trace_same_length:
  "length \<rho> = length (add_Tick_refusal_trace \<rho>)"
  by (simp add: add_Tick_refusal_trace_ctt_subset ctt_subset_same_length)

lemma add_Tick_refusal_trace_filter_Tock_same_length:
  "length (filter (\<lambda> x. x = [Tock]\<^sub>E) \<rho>) = length (filter (\<lambda> x. x = [Tock]\<^sub>E) (add_Tick_refusal_trace \<rho>))"
  by (induct \<rho> rule:add_Tick_refusal_trace.induct, auto)

definition CT4s :: "'e cttobs list set \<Rightarrow> bool" where
  "CT4s P = (\<forall> \<rho>. \<rho> \<in> P \<longrightarrow> add_Tick_refusal_trace \<rho> \<in> P)"

lemma CT4s_CT1_imp_CT4:
  "CT4s P \<Longrightarrow> CT1 P \<Longrightarrow> CT4 P"
  unfolding CT4_def CT4s_def CT1_def
proof (safe, simp)
  fix \<rho> X
  assume CT1_P: "\<forall>\<rho>. (\<exists>\<sigma>. \<rho> \<lesssim>\<^sub>C \<sigma> \<and> \<sigma> \<in> P) \<longrightarrow> \<rho> \<in> P"
  assume "\<rho> @ [[X]\<^sub>R] \<in> P" "\<forall>\<rho>. \<rho> \<in> P \<longrightarrow> add_Tick_refusal_trace \<rho> \<in> P"
  then have "add_Tick_refusal_trace (\<rho> @ [[X]\<^sub>R]) \<in> P"
    by auto
  then have "add_Tick_refusal_trace \<rho> @ [[X \<union> {Tick}]\<^sub>R] \<in> P"
    by (simp add: add_Tick_refusal_trace_end_refusal)
  also have "\<rho> @ [[X \<union> {Tick}]\<^sub>R] \<subseteq>\<^sub>C add_Tick_refusal_trace \<rho> @ [[X \<union> {Tick}]\<^sub>R]"
    by (simp add: add_Tick_refusal_trace_ctt_subset ctt_subset_combine)
  then show "\<rho> @ [[insert Tick X]\<^sub>R] \<in> P"
    using CT1_P calculation ctt_subset_imp_prefix_subset by auto
qed
    

definition CTwf :: "'e cttobs list set \<Rightarrow> bool" where
  "CTwf P = (\<forall>x\<in>P. cttWF x)"

lemma CTwf_cons_end_not_refusal_refusal:
  assumes "CTwf P"
  shows "\<not> sa @ [[S]\<^sub>R, [Z]\<^sub>R] \<in> P"
  using assms unfolding CTwf_def using cttWF_dist_cons_refusal
  using cttWF.simps(13) by blast

definition CT :: "'e cttobs list set \<Rightarrow> bool" where
  "CT P = ((\<forall>x\<in>P. cttWF x) \<and> CT0 P \<and> CT1 P \<and> CT2 P \<and> CT3 P)"

lemma CT_CT0: "CT P \<Longrightarrow> CT0 P"
  using CT_def by auto

lemma CT_CT1: "CT P \<Longrightarrow> CT1 P"
  using CT_def by auto

lemma CT1_CT1c: "CT1 P \<Longrightarrow> CT1c P"
  unfolding CT1_def CT1c_def
  using ctt_prefix_imp_prefix_subset by blast

lemma CT_CT1c: "CT P \<Longrightarrow> CT1c P"
  unfolding CT_def using CT1_CT1c by auto

lemma CT_CT2: "CT P \<Longrightarrow> CT2 P"
  using CT_def by auto

lemma CT_CT3: "CT P \<Longrightarrow> CT3 P"
  using CT_def by auto

lemma CT_wf: "CT P \<Longrightarrow> \<forall>x\<in>P. cttWF x"
  using CT_def by auto

lemma CT_CTwf: "CT P \<Longrightarrow> CTwf P"
  unfolding CT_def CTwf_def by auto

lemma CT0_CT1c_empty: "CT0 P \<Longrightarrow> CT1c P \<Longrightarrow> [] \<in> P"
  unfolding CT0_def CT1c_def apply auto
  using ctt_prefix.simps(1) by blast

lemma CT0_CT1_empty: "CT0 P \<Longrightarrow> CT1 P \<Longrightarrow> [] \<in> P"
  unfolding CT0_def CT1_def
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

lemma CT_empty: "CT P \<Longrightarrow> [] \<in> P"
  by (simp add: CT0_CT1_empty CT_CT0 CT_CT1)

lemmas CT_defs = CT_def CT0_def CT1_def CT2_def CT3_def

section {* Initial sequences of tocks *}

inductive_set tocks :: "'e cttevent set \<Rightarrow> 'e cttobs list set" for X :: "'e cttevent set" where
  empty_in_tocks: "[] \<in> tocks X" |
  tock_insert_in_tocks: "Y \<subseteq> X \<Longrightarrow> \<rho> \<in> tocks X \<Longrightarrow> [Y]\<^sub>R # [Tock]\<^sub>E # \<rho> \<in> tocks X"

lemma tocks_wf: "t\<in>tocks X \<Longrightarrow> cttWF t"
  by (induct t rule:cttWF.induct, auto, (cases rule:tocks.cases, auto)+)

lemma tocks_append_wf: "cttWF s \<Longrightarrow> t\<in>tocks X \<Longrightarrow> cttWF (t @ s)"
  by (induct t rule:cttWF.induct, auto, (cases rule:tocks.cases, auto)+)

lemma tocks_append_wf2: "cttWF (t @ s) \<Longrightarrow> t\<in>tocks X \<Longrightarrow> cttWF s"
  by (induct t rule:cttWF.induct, auto, (cases rule:tocks.cases, auto)+)

lemma tocks_append_tocks: "t\<in>tocks X \<Longrightarrow> s\<in>tocks X \<Longrightarrow> t @ s \<in>tocks X"
  using tocks.cases by (induct t rule:cttWF.induct, auto, metis (no_types, lifting) list.inject list.simps(3) tocks.simps)

lemma tocks_append_nontocks: "t\<in>tocks X \<Longrightarrow> s\<notin>tocks X \<Longrightarrow> t @ s \<notin>tocks X"
  using tocks.cases by (induct t rule:cttWF.induct, auto)

lemma tocks_subset: "t\<in>tocks X \<Longrightarrow> X \<subseteq> Y \<Longrightarrow> t\<in>tocks Y"
  by (induct t rule:tocks.induct, auto simp add: tocks.intros)

lemma split_tocks:  "cttWF x \<Longrightarrow> \<exists> s. \<exists>t\<in>tocks UNIV. x = t @ s"
  using tocks.empty_in_tocks by (induct x rule:cttWF.induct, auto)

lemma split_tocks_longest:  "cttWF x \<Longrightarrow> \<exists> s. \<exists>t\<in>tocks UNIV. x = t @ s \<and> (\<forall>t'\<in>tocks UNIV. t' \<le>\<^sub>C x \<longrightarrow> t' \<le>\<^sub>C t)"
proof (induct x rule:cttWF.induct, auto)
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
  then have "cttWF s"
    using tocks_wf by blast
  also have "cttWF s \<longrightarrow> s \<in> tocks X \<longrightarrow> t \<lesssim>\<^sub>C s \<longrightarrow> t \<in> {t. \<exists>s\<in>tocks X. t = s \<or> (\<exists>Y. t = s @ [[Y]\<^sub>R] \<and> Y \<subseteq> X)}"
    apply (induct t s rule:cttWF2.induct)
    apply (simp_all add: empty_in_tocks)
    using tocks.simps apply auto[1]
    apply (case_tac \<sigma> rule:cttWF.cases, auto)
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
    apply (case_tac \<sigma> rule:cttWF.cases, auto)+
    done
  then show "s \<in> tocks X \<Longrightarrow> t \<lesssim>\<^sub>C s \<Longrightarrow> t \<in> {t. \<exists>s\<in>tocks X. t = s \<or> (\<exists>Y. t = s @ [[Y]\<^sub>R] \<and> Y \<subseteq> X)}" using calculation by auto
qed

lemma ctt_prefix_tocks: "s \<in> tocks X \<Longrightarrow> t \<le>\<^sub>C s \<Longrightarrow> t \<in> {t. \<exists>s\<in>tocks X. t = s \<or> (\<exists>Y. t = s @ [[Y]\<^sub>R] \<and> Y \<subseteq> X)}"
  using ctt_prefix_imp_prefix_subset ctt_prefix_subset_tocks by blast

lemma ctt_prefix_subset_tocks2: "s \<in> tocks X \<Longrightarrow> t \<lesssim>\<^sub>C s \<Longrightarrow> t \<in> {t. \<exists>s'\<in>tocks X. s'\<lesssim>\<^sub>C s \<and> (t = s' \<or> (\<exists>Y. t = s' @ [[Y]\<^sub>R] \<and> Y \<subseteq> X))}"
proof -
  assume "s \<in> tocks X" 
  then have "cttWF s"
    using tocks_wf by blast
  also have "cttWF s \<longrightarrow> s \<in> tocks X \<longrightarrow> t \<lesssim>\<^sub>C s \<longrightarrow> t \<in> {t. \<exists>s'\<in>tocks X. s'\<lesssim>\<^sub>C s \<and> (t = s' \<or> (\<exists>Y. t = s' @ [[Y]\<^sub>R] \<and> Y \<subseteq> X))}"
    apply (induct t s rule:cttWF2.induct)
    apply (simp_all add: empty_in_tocks)
    using tocks.simps apply auto[1]
    apply (case_tac \<sigma> rule:cttWF.cases, auto)
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
    apply (case_tac \<sigma> rule:cttWF.cases, auto)+
    done
  then show "s \<in> tocks X \<Longrightarrow> t \<lesssim>\<^sub>C s \<Longrightarrow> t \<in> {t. \<exists>s'\<in>tocks X. s' \<lesssim>\<^sub>C s \<and> (t = s' \<or> (\<exists>Y. t = s' @ [[Y]\<^sub>R] \<and> Y \<subseteq> X))}"
    using calculation by blast
qed

lemma ctt_prefix_subset_tocks_refusal: "s \<in> tocks X \<Longrightarrow> \<rho> \<lesssim>\<^sub>C s @ [[Y]\<^sub>R] \<Longrightarrow> (\<exists> t \<in> tocks X. \<rho> = t \<or> (\<exists> Z. \<rho> = t @ [[Z]\<^sub>R] \<and> (Z \<subseteq> X \<or> Z \<subseteq> Y)))"
proof -
  assume "s \<in> tocks X"
  then have "cttWF (s @ [[Y]\<^sub>R])"
    using cttWF.simps(2) tocks_append_wf by blast
  also have "s \<in> tocks X \<longrightarrow> cttWF (s @ [[Y]\<^sub>R]) \<longrightarrow> \<rho> \<lesssim>\<^sub>C s @ [[Y]\<^sub>R] \<longrightarrow> (\<exists> t \<in> tocks X. \<rho> = t \<or> (\<exists> Z. \<rho> = t @ [[Z]\<^sub>R] \<and> (Z \<subseteq> X \<or> Z \<subseteq> Y)))"
    apply (induct \<rho> s rule:cttWF2.induct, auto simp add: empty_in_tocks)
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
    apply (meson cttWF.simps(12) ctt_prefix_subset_cttWF)
    apply (meson cttWF.simps(11) ctt_prefix_subset_cttWF)
    apply (meson cttWF.simps(13) ctt_prefix_subset_cttWF)
    apply (meson cttWF.simps(8) ctt_prefix_subset_cttWF)
    by (meson cttWF.simps(6) ctt_prefix_subset_cttWF)
  then show "s \<in> tocks X \<Longrightarrow> \<rho> \<lesssim>\<^sub>C s @ [[Y]\<^sub>R] \<Longrightarrow> \<exists>t\<in>tocks X. \<rho> = t \<or> (\<exists>Z. \<rho> = t @ [[Z]\<^sub>R] \<and> (Z \<subseteq> X \<or> Z \<subseteq> Y))"
    using calculation by auto
qed

lemma ctt_prefix_subset_tocks_refusal2: "s \<in> tocks X \<Longrightarrow> \<rho> \<lesssim>\<^sub>C s @ [[Y]\<^sub>R] \<Longrightarrow>
  (\<exists> t \<in> tocks X. t \<lesssim>\<^sub>C s \<and> (\<rho> = t \<or> (\<exists> Z. \<rho> = t @ [[Z]\<^sub>R] \<and> ((Z \<subseteq> X \<and> length (filter (\<lambda> x. x = [Tock]\<^sub>E) t) < length (filter (\<lambda> x. x = [Tock]\<^sub>E) s)) \<or> (Z \<subseteq> Y \<and> length (filter (\<lambda> x. x = [Tock]\<^sub>E) t) = length (filter (\<lambda> x. x = [Tock]\<^sub>E) s))))))"
proof -
  assume "s \<in> tocks X"
  then have "cttWF (s @ [[Y]\<^sub>R])"
    using cttWF.simps(2) tocks_append_wf by blast
  also have "s \<in> tocks X \<longrightarrow> cttWF (s @ [[Y]\<^sub>R]) \<longrightarrow> \<rho> \<lesssim>\<^sub>C s @ [[Y]\<^sub>R] \<longrightarrow> 
    (\<exists>t\<in>tocks X.
       t \<lesssim>\<^sub>C s \<and>
       (\<rho> = t \<or>
        (\<exists>Z. \<rho> = t @ [[Z]\<^sub>R] \<and>
             (Z \<subseteq> X \<and> length [x\<leftarrow>t . x = [Tock]\<^sub>E] < length [x\<leftarrow>s . x = [Tock]\<^sub>E] \<or>
              Z \<subseteq> Y \<and> length [x\<leftarrow>t . x = [Tock]\<^sub>E] = length [x\<leftarrow>s . x = [Tock]\<^sub>E]))))"
    apply (induct \<rho> s rule:cttWF2.induct, auto simp add: empty_in_tocks)
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
    apply (meson cttWF.simps(12) ctt_prefix_subset_cttWF)
    apply (meson cttWF.simps(11) ctt_prefix_subset_cttWF)
    apply (meson cttWF.simps(13) ctt_prefix_subset_cttWF)
    apply (meson cttWF.simps(8) ctt_prefix_subset_cttWF)
    by (meson cttWF.simps(6) ctt_prefix_subset_cttWF)
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
  then have "cttWF (s @ [[e]\<^sub>E])"
    by (cases e, auto simp add: tocks_append_wf)
  also have "cttWF (s @ [[e]\<^sub>E]) \<longrightarrow> s \<in> tocks X \<longrightarrow> t \<lesssim>\<^sub>C s @ [[e]\<^sub>E] \<longrightarrow>
    t \<in> {t. \<exists>s'\<in>tocks X. s'\<lesssim>\<^sub>C s \<and> 
      (t = s' \<or> 
        (\<exists>Y. t = s' @ [[Y]\<^sub>R] \<and> Y \<subseteq> X \<and> length (filter (\<lambda> x. x = [Tock]\<^sub>E) s') < length (filter (\<lambda> x. x = [Tock]\<^sub>E) s)) \<or>
        (t = s' @ [[e]\<^sub>E] \<and> length (filter (\<lambda> x. x = [Tock]\<^sub>E) s') = length (filter (\<lambda> x. x = [Tock]\<^sub>E) s)))}"
    apply auto
    apply (induct t s rule:cttWF2.induct, auto simp add: empty_in_tocks)
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
    apply (meson cttWF.simps(12) ctt_prefix_subset_cttWF)
    apply (meson cttWF.simps(11) ctt_prefix_subset_cttWF)
    apply (meson cttWF.simps(13) ctt_prefix_subset_cttWF)
    apply (meson cttWF.simps(8) ctt_prefix_subset_cttWF)
    using cttWF.simps(6) ctt_prefix_subset_cttWF by blast
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
  apply (induct \<rho> \<sigma> rule:cttWF2.induct, auto)
  using tocks.cases apply auto
  apply (metis (no_types, lifting) cttobs.inject(2) list.inject list.simps(3) order.trans tocks.simps)
  apply (meson cttWF.simps(12) ctt_prefix_subset_cttWF tocks_wf)
  apply (meson cttWF.simps(11) ctt_prefix_subset_cttWF tocks_wf)
  apply (meson cttWF.simps(13) ctt_prefix_subset_cttWF tocks_wf)
  apply (meson cttWF.simps(10) ctt_prefix_subset_cttWF tocks_wf)
  by (meson cttWF.simps(6) ctt_prefix_subset_cttWF tocks_wf)

lemma end_refusal_notin_tocks: "\<rho> @ [[X]\<^sub>R] \<notin> tocks Y"
  using tocks.cases by (induct \<rho> rule:cttWF.induct, auto)

lemma refusal_notin_tocks: "[[X]\<^sub>R] \<notin> tocks Y"
  using tocks.cases by auto
  
lemma end_event_notin_tocks: "s @ [[Event e]\<^sub>E] \<notin> tocks X"
  using tocks.cases by (induct s rule:cttWF.induct, auto)

lemma start_event_notin_tocks: "[Event e]\<^sub>E # s \<notin> tocks X"
  using tocks.cases by (induct s rule:cttWF.induct, auto)

lemma second_event_notin_tocks: "x # [Event e]\<^sub>E # s \<notin> tocks X"
  using tocks.cases by (induct s rule:cttWF.induct, auto)

lemma mid_event_notin_tocks: "s @ [[Event e]\<^sub>E] @ t \<notin> tocks X"
  using tocks.cases by (induct s rule:cttWF.induct, auto)

lemma event_notin_tocks: "[[Event e]\<^sub>E] \<notin> tocks X"
  using tocks.cases by (auto)

lemma start_tick_notin_tocks: "[Tick]\<^sub>E # s \<notin> tocks X"
  using tocks.cases by (induct s rule:cttWF.induct, auto)

lemma second_tick_notin_tocks: "x # [Tick]\<^sub>E # s \<notin> tocks X"
  using tocks.cases by (induct s rule:cttWF.induct, auto)

lemma end_tick_notin_tocks: "s @ [[Tick]\<^sub>E] \<notin> tocks X"
  using tocks.cases by (induct s rule:cttWF.induct, auto)

lemma mid_tick_notin_tocks: "s @ [[Tick]\<^sub>E] @ t \<notin> tocks X"
  using tocks.cases by (induct s rule:cttWF.induct, auto)

lemma tick_notin_tocks: "[[Tick]\<^sub>E] \<notin> tocks X"
  using tocks.cases by (auto)

lemma double_refusal_start_notin_tocks: "[Y]\<^sub>R # [Z]\<^sub>R # s \<notin> tocks X"
  using tocks.cases by (induct s rule:cttWF.induct, auto)

lemma start_tock_notin_tocks: "[Tock]\<^sub>E # s \<notin> tocks X"
  using tocks.cases by (induct s rule:cttWF.induct, auto)

lemmas notin_tocks = 
  end_refusal_notin_tocks refusal_notin_tocks double_refusal_start_notin_tocks
  start_event_notin_tocks second_event_notin_tocks mid_event_notin_tocks end_event_notin_tocks event_notin_tocks
  start_tick_notin_tocks second_tick_notin_tocks mid_tick_notin_tocks end_tick_notin_tocks tick_notin_tocks
  start_tock_notin_tocks

lemma nontocks_append_tocks: "t\<notin>tocks X \<Longrightarrow> s\<in>tocks X \<Longrightarrow> t @ s \<notin>tocks X"
  using tocks.cases apply (induct t rule:cttWF.induct, simp_all add: tocks.intros notin_tocks)
  apply (metis double_refusal_start_notin_tocks refusal_notin_tocks tocks.cases)
  by (metis list.distinct(1) list.inject tocks.simps)

lemma equal_traces_imp_equal_tocks: "s \<in> tocks X \<Longrightarrow> s' \<in> tocks X  \<Longrightarrow> 
  s @ [[Event e]\<^sub>E] @ t = s' @ [[Event e]\<^sub>E] @ t' \<Longrightarrow> s = s' \<and> t = t'"
  apply (induct s s' rule:cttWF2.induct, auto simp add: notin_tocks)
  using tocks.cases by auto

lemma ctt_subset_remove_start: "\<rho>' @ \<sigma>' \<subseteq>\<^sub>C \<rho> @ \<sigma> \<Longrightarrow> \<rho>' \<subseteq>\<^sub>C \<rho> \<Longrightarrow> \<sigma>' \<subseteq>\<^sub>C \<sigma>"
  by (induct \<rho>' \<rho> rule:ctt_subset.induct, simp_all)

lemma ctt_prefix_subset_lift_tocks:
  "\<rho> \<lesssim>\<^sub>C \<sigma> \<Longrightarrow> \<rho> \<in> tocks UNIV \<Longrightarrow> \<exists> \<rho>' \<in> tocks UNIV. \<rho> \<lesssim>\<^sub>C \<rho>' \<and> \<rho>' \<le>\<^sub>C \<sigma>"
  apply (induct \<rho> \<sigma> rule:cttWF2.induct, auto)
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
    using cttWF.simps(12) tocks_wf by blast
  then show "\<exists>\<rho>'\<in>tocks UNIV. [X]\<^sub>R # [Tick]\<^sub>E # \<rho> \<lesssim>\<^sub>C \<rho>' \<and> \<rho>' \<le>\<^sub>C \<sigma>"
    by auto
next
  fix X e \<rho> \<sigma>
  assume "[X]\<^sub>R # [Event e]\<^sub>E # \<rho> \<in> tocks UNIV"
  then have "False"
    by (meson cttWF.simps(11) tocks_wf)
  then show "\<exists>\<rho>'\<in>tocks UNIV. [X]\<^sub>R # [Event e]\<^sub>E # \<rho> \<lesssim>\<^sub>C \<rho>' \<and> \<rho>' \<le>\<^sub>C \<sigma>"
    by auto
next
  fix X Y \<rho> \<sigma>
  assume "[X]\<^sub>R # [Y]\<^sub>R # \<rho> \<in> tocks UNIV"
  then have "False"
    using cttWF.simps(13) tocks_wf by blast
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
proof (insert assms, induct "\<rho>'" "\<rho>" rule:cttWF2.induct, simp_all)
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
    by (cases \<rho>'' rule:cttWF.cases, auto)
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
    using cttWF.simps(12) tocks_wf by blast
  then show "[X]\<^sub>R # [Tick]\<^sub>E # \<rho> \<lesssim>\<^sub>C \<sigma>''"
    by auto
next
  fix X e \<rho> \<sigma>''
  assume "[X]\<^sub>R # [Event e]\<^sub>E # \<rho> \<in> tocks UNIV"
  then have "False"
    by (meson cttWF.simps(11) tocks_wf)
  then show "[X]\<^sub>R # [Event e]\<^sub>E # \<rho> \<lesssim>\<^sub>C \<sigma>''"
    by auto
next
  fix X Y \<rho> \<sigma>''
  assume "[X]\<^sub>R # [Y]\<^sub>R # \<rho> \<in> tocks UNIV"
  then have "False"
    using cttWF.simps(13) tocks_wf by blast
  then show "[X]\<^sub>R # [Y]\<^sub>R # \<rho> \<lesssim>\<^sub>C \<sigma>''"
    by auto
next
  fix X \<rho> \<sigma>''
  assume "[X]\<^sub>R # [Tick]\<^sub>E # \<sigma>'' \<in> tocks UNIV"
  then have "False"
    using cttWF.simps(12) tocks_wf by blast
  then show "\<rho> \<lesssim>\<^sub>C [X]\<^sub>R # [Tick]\<^sub>E # \<sigma>''"
    by auto
next
  fix X e \<rho> \<sigma>''
  assume "[X]\<^sub>R # [Event e]\<^sub>E # \<sigma>'' \<in> tocks UNIV"
  then have "False"
    by (meson cttWF.simps(11) tocks_wf)
  then show "\<rho> \<lesssim>\<^sub>C [X]\<^sub>R # [Event e]\<^sub>E # \<sigma>''"
    by auto
next
  fix X Y \<rho> \<sigma>''
  assume "[X]\<^sub>R # [Y]\<^sub>R # \<sigma>'' \<in> tocks UNIV"
  then have "False"
    using cttWF.simps(13) tocks_wf by blast
  then show "\<rho> \<lesssim>\<^sub>C [X]\<^sub>R # [Y]\<^sub>R # \<sigma>''"
    by auto
next
  fix x \<rho> \<sigma>''
  assume "[Tick]\<^sub>E # x # \<rho> \<in> tocks UNIV"
  then have "False"
    using cttWF.simps(10) tocks_wf by blast
  then show "[Tick]\<^sub>E # x # \<rho> \<lesssim>\<^sub>C \<sigma>''"
    by auto
next
  fix y \<rho> \<sigma>''
  assume "[Tick]\<^sub>E # y # \<sigma>'' \<in> tocks UNIV"
  then have "False"
    using cttWF.simps(10) tocks_wf by blast
  then show "\<rho> \<lesssim>\<^sub>C [Tick]\<^sub>E # y # \<sigma>''"
    by auto
next
  fix \<rho> \<sigma>''
  assume "[Tock]\<^sub>E # \<rho> \<in> tocks UNIV"
  then have "False"
    using cttWF.simps(6) tocks_wf by blast
  then show "[Tock]\<^sub>E # \<rho> \<lesssim>\<^sub>C \<sigma>''"
    by auto
next
  fix \<rho> \<sigma>''
  assume "[Tock]\<^sub>E # \<sigma>'' \<in> tocks UNIV"
  then have "False"
    using cttWF.simps(6) tocks_wf by blast
  then show "\<rho> \<lesssim>\<^sub>C [Tock]\<^sub>E # \<sigma>''"
    by auto
qed

lemma longest_pretocks_ctt_prefix_subset2:
  assumes "\<rho>' @ \<sigma>' \<lesssim>\<^sub>C \<rho> @ \<sigma>"
  assumes "\<rho> \<in> tocks UNIV" "\<forall>t\<in>tocks UNIV. t \<le>\<^sub>C \<rho> @ \<sigma> \<longrightarrow> t \<le>\<^sub>C \<rho>"
  assumes "\<rho>' \<in> tocks UNIV" "\<forall>t\<in>tocks UNIV. t \<le>\<^sub>C \<rho>' @ \<sigma>' \<longrightarrow> t \<le>\<^sub>C \<rho>'"
  shows "\<rho>' \<lesssim>\<^sub>C \<rho> \<and> (\<sigma>' \<lesssim>\<^sub>C \<sigma> \<or> (\<exists> X. \<sigma>' \<lesssim>\<^sub>C [X]\<^sub>R # \<sigma>)) "
  sorry

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
  "cttWF (\<rho> @ \<sigma>) \<Longrightarrow> cttWF \<sigma>' \<Longrightarrow> \<rho> \<in> tocks X \<and> \<sigma>' \<subseteq>\<^sub>C \<rho> @ \<sigma> \<Longrightarrow> \<exists> \<rho>' \<in> tocks X. \<rho>' \<subseteq>\<^sub>C \<rho> \<and> \<rho>' \<le>\<^sub>C \<sigma>'"
  apply (induct \<sigma>' \<rho> rule:cttWF2.induct)
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
  "cttWF (\<rho>' @ \<sigma>') \<Longrightarrow> cttWF \<sigma> \<Longrightarrow> \<rho>' \<in> tocks X \<and> \<rho>' @ \<sigma>' \<subseteq>\<^sub>C \<sigma> \<Longrightarrow> \<exists> \<rho> \<in> tocks UNIV. \<rho>' \<subseteq>\<^sub>C \<rho> \<and> \<rho> \<le>\<^sub>C \<sigma>"
  apply (induct \<rho>' \<sigma> rule:cttWF2.induct)
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
  assumes "cttWF (\<rho>' @ \<sigma>')" "cttWF (\<rho> @ \<sigma>)"
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
    using assms(3) assms(5) assms(7) apply (induct \<rho>' \<rho> rule:cttWF2.induct)
    using tocks.cases by (auto simp add: notin_tocks)
  then show "\<rho>' \<subseteq>\<^sub>C \<rho> \<and> \<sigma>' \<subseteq>\<^sub>C \<sigma>"
    using assms(7) ctt_subset_remove_start by auto
qed

lemma CT0_tocks: "CT0 (tocks X)"
  unfolding CT0_def using tocks.empty_in_tocks by auto 

lemma CT2_tocks: "CT2 (tocks X)"
  unfolding CT2_def by (simp add: end_refusal_notin_tocks)  

lemma CT3_tocks: "Tock \<notin> X \<Longrightarrow> CT3 (tocks X)"
  unfolding CT3_def
proof auto
  fix x
  show "Tock \<notin> X \<Longrightarrow> x \<in> tocks X \<Longrightarrow> CT3_trace x"
    using tocks.cases by (induct rule:CT3_trace.induct, auto)
qed

lemma CT4s_tocks: "Tick \<in> X \<Longrightarrow> CT4s (tocks X)"
  unfolding CT4s_def
proof auto
  fix \<rho>
  assume assm: "Tick \<in> X"
  show "\<rho> \<in> tocks X \<Longrightarrow> add_Tick_refusal_trace \<rho> \<in> tocks X"
    by (induct \<rho> rule:tocks.induct, auto simp add: assm tocks.empty_in_tocks tocks.tock_insert_in_tocks)
qed



end