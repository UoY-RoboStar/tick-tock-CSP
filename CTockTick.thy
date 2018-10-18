theory CTockTick
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

lemma cttWF_prefix_is_cttWF: "cttWF (s @ t) \<Longrightarrow> cttWF s"
  using ctt_prefix_concat ctt_prefix_imp_prefix_subset ctt_prefix_subset_cttWF by blast

section {* Healthiness Conditions *}

definition CT0 :: "'e cttobs list set \<Rightarrow> bool" where
  "CT0 P = (P \<noteq> {})"

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

(*definition CT4 :: "'e cttobs list set \<Rightarrow> bool" where
  "CT4 P = (\<forall> \<rho>. \<rho> @ [[Tick]\<^sub>E] \<in> P \<longrightarrow> (\<nexists> X. \<rho> @ [[X]\<^sub>R] \<in> P))"*)

definition CT :: "'e cttobs list set \<Rightarrow> bool" where
  "CT P = ((\<forall>x\<in>P. cttWF x) \<and> CT0 P \<and> CT1 P \<and> CT2 P \<and> CT3 P)"

lemma CT_CT0: "CT P \<Longrightarrow> CT0 P"
  using CT_def by auto

lemma CT_CT1: "CT P \<Longrightarrow> CT1 P"
  using CT_def by auto

lemma CT_CT2: "CT P \<Longrightarrow> CT2 P"
  using CT_def by auto

lemma CT_CT3: "CT P \<Longrightarrow> CT3 P"
  using CT_def by auto

lemma CT_wf: "CT P \<Longrightarrow> \<forall>x\<in>P. cttWF x"
  using CT_def by auto

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

section {* Operators *}

subsection {* Div *}

definition DivCTT :: "'e cttobs list set" ("div\<^sub>C") where
  "div\<^sub>C = {[]}"

lemma DivCTT_wf: "\<forall> t\<in>div\<^sub>C. cttWF t"
  unfolding DivCTT_def by auto

lemma CT_Div: "CT div\<^sub>C"
  unfolding CT_defs DivCTT_def by (auto simp add: ctt_prefix_subset_antisym)

subsection {* Stop *}

definition StopCTT :: "'e cttobs list set" ("STOP\<^sub>C") where
  "STOP\<^sub>C = {t. \<exists> s\<in>tocks({x. x \<noteq> Tock}). t = s \<or> (\<exists> X. t = s @ [[X]\<^sub>R] \<and> Tock \<notin> X)}
  (*add_pretocks {x. x \<noteq> Tock} ({t. \<exists> Y. Tock \<notin> Y \<and> t = [[Y]\<^sub>R]} \<union> {[]})*)"

lemma StopCTT_wf: "\<forall> t\<in>STOP\<^sub>C. cttWF t"
  unfolding StopCTT_def by (auto simp add: tocks_append_wf tocks_wf)

lemma CT_Stop: "CT STOP\<^sub>C"
  unfolding CT_defs
proof (auto)
  fix x
  show "x \<in> STOP\<^sub>C \<Longrightarrow> cttWF x"
    using StopCTT_wf by auto
next
  show "STOP\<^sub>C = {} \<Longrightarrow> False"
    unfolding StopCTT_def by (auto, erule_tac x="[]" in allE, erule_tac x="[]" in ballE, auto simp add: empty_in_tocks)
next
  fix \<rho> \<sigma>
  show "\<rho> \<lesssim>\<^sub>C \<sigma> \<Longrightarrow> \<sigma> \<in> STOP\<^sub>C \<Longrightarrow> \<rho> \<in> STOP\<^sub>C"
    unfolding StopCTT_def using ctt_prefix_subset_tocks ctt_prefix_subset_tocks_refusal by (auto, fastforce+)
next
  fix \<rho> X Y
  show "\<rho> @ [[X]\<^sub>R] \<in> STOP\<^sub>C \<Longrightarrow>
             Y \<inter> {e. e \<noteq> Tock \<and> \<rho> @ [[e]\<^sub>E] \<in> STOP\<^sub>C \<or> e = Tock \<and> \<rho> @ [[X]\<^sub>R, [e]\<^sub>E] \<in> STOP\<^sub>C} = {} \<Longrightarrow> \<rho> @ [[X \<union> Y]\<^sub>R] \<in> STOP\<^sub>C"
    unfolding StopCTT_def
  proof auto
    assume "\<rho> @ [[X]\<^sub>R] \<in> tocks {x. x \<noteq> Tock}"
    then have "False"
      using tocks.cases by (induct \<rho> rule:cttWF.induct, auto)
    then show "\<exists>s\<in>tocks {x. x \<noteq> Tock}. \<rho> @ [[X \<union> Y]\<^sub>R] = s \<or> \<rho> = s \<and> Tock \<notin> X \<and> Tock \<notin> Y"
      by auto
  next
    assume Tock_notin_X: "Tock \<notin> X"
    assume rho_tocks: "\<rho> \<in> tocks {x. x \<noteq> Tock}"
    from rho_tocks have setA: "{e. e \<noteq> Tock \<and> \<rho> @ [[e]\<^sub>E] \<in> tocks {x. x \<noteq> Tock}} = {}"
      using tocks.cases by (auto, induct \<rho> rule:cttWF.induct, auto)
    from rho_tocks Tock_notin_X have setB: "{e. e = Tock \<and> \<rho> @ [[X]\<^sub>R, [e]\<^sub>E] \<in> tocks {x. x \<noteq> Tock}} = {Tock}"
      by (auto, intro tocks_append_tocks, auto, metis (mono_tags, lifting) mem_Collect_eq subsetI tocks.empty_in_tocks tocks.tock_insert_in_tocks)
    from setA setB have "{e. e \<noteq> Tock \<and> \<rho> @ [[e]\<^sub>E] \<in> tocks {x. x \<noteq> Tock} \<or> e = Tock \<and> \<rho> @ [[X]\<^sub>R, [e]\<^sub>E] \<in> tocks {x. x \<noteq> Tock}} = {Tock}"
      by (auto)
    also assume "Y \<inter> {e. e \<noteq> Tock \<and> \<rho> @ [[e]\<^sub>E] \<in> tocks {x. x \<noteq> Tock} \<or> e = Tock \<and> \<rho> @ [[X]\<^sub>R, [e]\<^sub>E] \<in> tocks {x. x \<noteq> Tock}} = {}"
    then have "Tock \<notin> Y"
      using calculation by (auto)
    from this and rho_tocks show "\<exists>s\<in>tocks {x. x \<noteq> Tock}. \<rho> @ [[X \<union> Y]\<^sub>R] = s \<or> \<rho> = s \<and> Tock \<notin> Y"
      by auto
  qed
next
  fix x
  have "\<forall>s \<in> tocks {x. x \<noteq> Tock}. CT3_trace s"
    by (metis (mono_tags, lifting) CT3_def CT3_tocks mem_Collect_eq)
  then show "x \<in> STOP\<^sub>C \<Longrightarrow> CT3_trace x"
    unfolding StopCTT_def using CT3_append CT3_trace.simps(2) cttWF.simps(2) by (auto, blast)
qed


subsection {* Skip *}

definition SkipCTT :: "'e cttobs list set" ("SKIP\<^sub>C") where
  "SKIP\<^sub>C = {[], [[Tick]\<^sub>E]}"
  (*{[], [[Tick]\<^sub>E]} \<union> {t. \<exists> Y. Tick \<notin> Y \<and> t = [[Y]\<^sub>R]} \<union> {t. \<exists> n s. (t = s \<or> t = s @ [[Tick]\<^sub>E]) \<and> s \<in> ntock {x. x \<noteq> Tick} n}*)

lemma SkipCTT_wf: "\<forall> t\<in>SKIP\<^sub>C. cttWF t"
  unfolding SkipCTT_def by auto

lemma CT_Skip: "CT SKIP\<^sub>C"
  unfolding CT_defs SkipCTT_def 
  apply (auto simp add: ctt_prefix_subset_antisym)
  apply (case_tac \<rho> rule:cttWF.cases, auto)
  done

subsection {* Wait *}

definition WaitCTT :: "nat \<Rightarrow> 'e cttobs list set" ("wait\<^sub>C[_]") where
  "wait\<^sub>C[n] = 
    {t. \<exists> s\<in>tocks({x. x \<noteq> Tock}). length (filter (\<lambda> x. x = [Tock]\<^sub>E) s) < n \<and> (t = s \<or> (\<exists> X. Tock \<notin> X \<and> t = s @ [[X]\<^sub>R]))}
     \<union> {t. \<exists> s\<in>tocks({x. x \<noteq> Tock}). length (filter (\<lambda> x. x = [Tock]\<^sub>E) s) = n \<and> (t = s \<or> t = s @ [[Tick]\<^sub>E])}"
  (*{t. \<exists> s x. t = s @ x \<and> x \<in> {[], [[Tick]\<^sub>E]} \<and> s \<in> ntock {x. x \<noteq> Tock} n}*)

lemma WaitCTT_wf: "\<forall> t\<in>wait\<^sub>C[n]. cttWF t"
  unfolding WaitCTT_def by (auto simp add: tocks_wf tocks_append_wf)

lemma CT_Wait: "CT wait\<^sub>C[n]"
  unfolding CT_defs
proof auto
  fix x
  show "x \<in> wait\<^sub>C[n] \<Longrightarrow> cttWF x"
    using WaitCTT_wf by auto
next
  show "wait\<^sub>C[n] = {} \<Longrightarrow> False"
    unfolding WaitCTT_def using tocks.empty_in_tocks by fastforce
next
  fix \<rho> \<sigma>
  show "\<rho> \<lesssim>\<^sub>C \<sigma> \<Longrightarrow> \<sigma> \<in> wait\<^sub>C[n] \<Longrightarrow> \<rho> \<in> wait\<^sub>C[n]"
    unfolding WaitCTT_def 
  proof auto
    assume assm1: "\<rho> \<lesssim>\<^sub>C \<sigma>"
    assume assm2: "\<sigma> \<in> tocks {x. x \<noteq> Tock}"
    assume assm3: "length [x\<leftarrow>\<sigma> . x = [Tock]\<^sub>E] < n"
    from assm1 assm2 have 1: "\<rho> \<in> {t. \<exists>s\<in>tocks {x. x \<noteq> Tock}. t = s \<or> (\<exists>Y. t = s @ [[Y]\<^sub>R] \<and> Y \<subseteq> {x. x \<noteq> Tock})}"
      using ctt_prefix_subset_tocks by blast
    from assm1 have "length [x\<leftarrow>\<rho> . x = [Tock]\<^sub>E] \<le> length [x\<leftarrow>\<sigma> . x = [Tock]\<^sub>E]"
      using ctt_prefix_subset_Tock_filter_length by auto
    from this assm3 have 2: "length [x\<leftarrow>\<rho> . x = [Tock]\<^sub>E] < n"
      by auto
    from 1 2 show "\<exists>s\<in>tocks {x. x \<noteq> Tock}. length [x\<leftarrow>s . x = [Tock]\<^sub>E] < n \<and> (\<rho> = s \<or> (\<exists>X. Tock \<notin> X \<and> \<rho> = s @ [[X]\<^sub>R]))"
      by (auto, rule_tac x="s" in bexI, auto)
  next
    fix s X
    assume assm1: "\<rho> \<lesssim>\<^sub>C s @ [[X]\<^sub>R]"
    assume assm2: "s \<in> tocks {x. x \<noteq> Tock}"
    assume assm3: "length [x\<leftarrow>s . x = [Tock]\<^sub>E] < n"
    assume assm4: "Tock \<notin> X"
    from assm1 assm2 have 1: "\<exists>t\<in>tocks {x. x \<noteq> Tock}. \<rho> = t \<or> (\<exists>Z. \<rho> = t @ [[Z]\<^sub>R] \<and> (Z \<subseteq> {x. x \<noteq> Tock} \<or> Z \<subseteq> X))"
      using ctt_prefix_subset_tocks_refusal by blast
    from assm1 have "length [x\<leftarrow>\<rho> . x = [Tock]\<^sub>E] \<le> length [x\<leftarrow>s @ [[X]\<^sub>R] . x = [Tock]\<^sub>E]"
      using ctt_prefix_subset_Tock_filter_length by blast
    from this assm3 have 2: "length [x\<leftarrow>\<rho> . x = [Tock]\<^sub>E] < n"
      by auto
    from 1 2 assm4 show "\<exists>s\<in>tocks {x. x \<noteq> Tock}. length [x\<leftarrow>s . x = [Tock]\<^sub>E] < n \<and> (\<rho> = s \<or> (\<exists>X. Tock \<notin> X \<and> \<rho> = s @ [[X]\<^sub>R]))"
      by (auto, rule_tac x="t" in bexI, auto)
  next
    assume assm1: "\<rho> \<lesssim>\<^sub>C \<sigma>"
    assume assm2: "\<sigma> \<in> tocks {x. x \<noteq> Tock}"
    assume assm3: "\<forall>s\<in>tocks {x. x \<noteq> Tock}. length [x\<leftarrow>s . x = [Tock]\<^sub>E] = length [x\<leftarrow>\<sigma> . x = [Tock]\<^sub>E] \<longrightarrow> \<rho> \<noteq> s \<and> \<rho> \<noteq> s @ [[Tick]\<^sub>E]"
    thm ctt_prefix_subset_tocks
    from assm1 assm2 have 1: "\<rho> \<in> {t. \<exists>s\<in>tocks {x. x \<noteq> Tock}. t = s \<or> (\<exists>Y. t = s @ [[Y]\<^sub>R] \<and> Y \<subseteq> {x. x \<noteq> Tock})}"
      using ctt_prefix_subset_tocks by auto
    from assm1 have 2: "length [x\<leftarrow>\<rho> . x = [Tock]\<^sub>E] \<le> length [x\<leftarrow>\<sigma> . x = [Tock]\<^sub>E]"
      using ctt_prefix_subset_Tock_filter_length by auto
    from equal_Tocks_tocks_imp assm1 assm2 have "length [x\<leftarrow>\<rho> . x = [Tock]\<^sub>E] = length [x\<leftarrow>\<sigma> . x = [Tock]\<^sub>E] \<Longrightarrow> \<rho> \<in> tocks {x. x \<noteq> Tock}"
      by auto
    from this assm3 have "length [x\<leftarrow>\<rho> . x = [Tock]\<^sub>E] = length [x\<leftarrow>\<sigma> . x = [Tock]\<^sub>E] \<Longrightarrow> False"
      by auto
    from this 2 have 3: "length [x\<leftarrow>\<rho> . x = [Tock]\<^sub>E] < length [x\<leftarrow>\<sigma> . x = [Tock]\<^sub>E]"
      by (cases "length [x\<leftarrow>\<rho> . x = [Tock]\<^sub>E] = length [x\<leftarrow>\<sigma> . x = [Tock]\<^sub>E]", auto)
    from 1 3 show "\<exists>s\<in>tocks {x. x \<noteq> Tock}.
       length [x\<leftarrow>s . x = [Tock]\<^sub>E] < length [x\<leftarrow>\<sigma> . x = [Tock]\<^sub>E] \<and> (\<rho> = s \<or> (\<exists>X. Tock \<notin> X \<and> \<rho> = s @ [[X]\<^sub>R]))"
      by (auto, rule_tac x="s" in bexI, auto)
  next
    fix s
    assume assm1: "\<rho> \<lesssim>\<^sub>C s @ [[Tick]\<^sub>E]"
    assume assm2: "s \<in> tocks {x. x \<noteq> Tock}"
    assume assm3: "\<forall>sa\<in>tocks {x. x \<noteq> Tock}.
            length [x\<leftarrow>sa . x = [Tock]\<^sub>E] = length [x\<leftarrow>s . x = [Tock]\<^sub>E] \<longrightarrow> \<rho> \<noteq> sa \<and> \<rho> \<noteq> sa @ [[Tick]\<^sub>E]"
    obtain s' where s'_assms: "s'\<in>tocks {x. x \<noteq> Tock}" "s' \<lesssim>\<^sub>C s" "\<rho> = s' \<or>
              (\<exists>Y. \<rho> = s' @ [[Y]\<^sub>R] \<and> Y \<subseteq> {x. x \<noteq> Tock} \<and> length [x\<leftarrow>s' . x = [Tock]\<^sub>E] < length [x\<leftarrow>s . x = [Tock]\<^sub>E]) \<or>
              \<rho> = s' @ [[Tick]\<^sub>E] \<and> length [x\<leftarrow>s' . x = [Tock]\<^sub>E] = length [x\<leftarrow>s . x = [Tock]\<^sub>E]"
      using assm1 assm2 ctt_prefix_subset_tocks_event by blast
    then have "length [x\<leftarrow>s' . x = [Tock]\<^sub>E] \<noteq> length [x\<leftarrow>s . x = [Tock]\<^sub>E]"
      using assm3 less_le by blast
    then show "\<exists>sa\<in>tocks {x. x \<noteq> Tock}.
            length [x\<leftarrow>sa . x = [Tock]\<^sub>E] < length [x\<leftarrow>s . x = [Tock]\<^sub>E] \<and> (\<rho> = sa \<or> (\<exists>X. Tock \<notin> X \<and> \<rho> = sa @ [[X]\<^sub>R]))"
      using ctt_prefix_subset_Tock_filter_length order.not_eq_order_implies_strict s'_assms s'_assms by (rule_tac x="s'" in bexI, auto)
  qed
next
  fix \<rho> :: "'e cttobs list" 
  fix X Y :: "'e cttevent set"
  assume assm1: "\<rho> @ [[X]\<^sub>R] \<in> wait\<^sub>C[n]"
  assume assm2: "Y \<inter> {e. e \<noteq> Tock \<and> \<rho> @ [[e]\<^sub>E] \<in> wait\<^sub>C[n] \<or> e = Tock \<and> \<rho> @ [[X]\<^sub>R, [e]\<^sub>E] \<in> wait\<^sub>C[n]} = {}"
  from assm1 have 1: "\<rho>\<in>tocks {x. x \<noteq> Tock}"
    unfolding WaitCTT_def using end_refusal_notin_tocks by blast
  from assm1 have 2: "length [x\<leftarrow>\<rho> . x = [Tock]\<^sub>E] < n \<and> Tock \<notin> X"
    unfolding WaitCTT_def using end_refusal_notin_tocks by blast
  have 3: "length [x\<leftarrow>\<rho> . x = [Tock]\<^sub>E] < n \<longrightarrow> Tock \<notin> Y"
  proof auto
    assume assm3: "length [x\<leftarrow>\<rho> . x = [Tock]\<^sub>E] < n"
    assume assm4: "Tock \<in> Y"
    have "Tock \<in> {e. e \<noteq> Tock \<and> \<rho> @ [[e]\<^sub>E] \<in> wait\<^sub>C[n] \<or> e = Tock \<and> \<rho> @ [[X]\<^sub>R, [e]\<^sub>E] \<in> wait\<^sub>C[n]}"
      unfolding WaitCTT_def apply auto
      apply (metis (mono_tags, lifting) "1" "2" assm3 less_not_refl mem_Collect_eq subset_iff tocks.simps tocks_append_tocks)
      apply (metis (mono_tags, lifting) "1" "2" assm3 less_not_refl mem_Collect_eq subset_iff tocks.simps tocks_append_tocks)
      apply (metis (mono_tags, lifting) "1" "2" assm3 less_not_refl mem_Collect_eq subset_iff tocks.simps tocks_append_tocks)
      using Suc_lessI assm3 by blast
    then have "Tock \<in> Y \<inter> {e. e \<noteq> Tock \<and> \<rho> @ [[e]\<^sub>E] \<in> wait\<^sub>C[n] \<or> e = Tock \<and> \<rho> @ [[X]\<^sub>R, [e]\<^sub>E] \<in> wait\<^sub>C[n]}"
      using assm4 by auto
    then show "False"
      using assm2 by auto
  qed
  show "\<rho> @ [[X \<union> Y]\<^sub>R] \<in> wait\<^sub>C[n]"
    using 1 2 3 unfolding WaitCTT_def by auto
next
  fix x
  have "\<forall>x \<in> tocks {x. x \<noteq> Tock}. CT3_trace x"
    by (metis (mono_tags, lifting) CT3_def CT3_tocks mem_Collect_eq)
  then show "x \<in> wait\<^sub>C[n] \<Longrightarrow> CT3_trace x"
    unfolding WaitCTT_def apply auto
    using CT3_append CT3_trace.simps(2) cttWF.simps(2) apply blast
    using CT3_append CT3_trace.simps(2) cttWF.simps(3) apply blast
    done
qed

subsection {* Prefix *}
  

definition PrefixCTT :: "'e \<Rightarrow> 'e cttobs list set \<Rightarrow> 'e cttobs list set" (infixr "\<rightarrow>\<^sub>C" 61) where
  "PrefixCTT e P = 
    {t. \<exists> s\<in>tocks({x. x \<noteq> Tock \<and> x \<noteq> Event e}). t = s \<or> (\<exists> X. Tock \<notin> X \<and> Event e \<notin> X \<and> t = s @ [[X]\<^sub>R])}
     \<union> {t. \<exists> s\<in>tocks({x. x \<noteq> Tock \<and> x \<noteq> Event e}). t = s \<or> (\<exists> \<sigma>\<in>P. t = s @ [[Event e]\<^sub>E] @ \<sigma>)}"
    (*add_pretocks {x. x \<noteq> Event e \<and> x \<noteq> Tock} ({[], [[Event e]\<^sub>E]} \<union> {t. \<exists> Y. Tock \<notin> Y \<and> Event e \<notin> Y \<and> t = [[Y]\<^sub>R]})*)

lemma PrefixCTT_wf: "\<forall> t\<in>P. cttWF t \<Longrightarrow> \<forall> t\<in>PrefixCTT e P. cttWF t"
  unfolding PrefixCTT_def by (auto simp add: tocks_wf tocks_append_wf)

lemma CT_Prefix:
  assumes "CT P"
  shows "CT (e \<rightarrow>\<^sub>C P)"
  unfolding CT_defs
proof auto
  fix x
  show "x \<in> e \<rightarrow>\<^sub>C P \<Longrightarrow> cttWF x"
    by (meson CT_def PrefixCTT_wf assms)
next
  show "e \<rightarrow>\<^sub>C P = {} \<Longrightarrow> False"
    unfolding PrefixCTT_def using tocks.empty_in_tocks by (blast)
next
  fix \<rho> \<sigma> :: "'a cttobs list"
  show "\<rho> \<lesssim>\<^sub>C \<sigma> \<Longrightarrow> \<sigma> \<in> e \<rightarrow>\<^sub>C P \<Longrightarrow> \<rho> \<in> e \<rightarrow>\<^sub>C P"
    unfolding PrefixCTT_def
  proof auto
    assume assm1: "\<rho> \<lesssim>\<^sub>C \<sigma>"
    assume assm2: "\<forall>s\<in>tocks {x. x \<noteq> Tock \<and> x \<noteq> Event e}. \<rho> \<noteq> s \<and> (\<forall>\<sigma>\<in>P. \<rho> \<noteq> s @ [Event e]\<^sub>E # \<sigma>)"
    assume assm3: "\<sigma> \<in> tocks {x. x \<noteq> Tock \<and> x \<noteq> Event e}"
    obtain s where "s\<in>tocks {x. x \<noteq> Tock \<and> x \<noteq> Event e}" "\<rho> = s \<or> (\<exists>Y. \<rho> = s @ [[Y]\<^sub>R] \<and> Y \<subseteq> {x. x \<noteq> Tock \<and> x \<noteq> Event e})"
      using assm1 assm3 ctt_prefix_subset_tocks by blast
    then show "\<exists>s\<in>tocks {x. x \<noteq> Tock \<and> x \<noteq> Event e}. \<exists>X. Tock \<notin> X \<and> Event e \<notin> X \<and> \<rho> = s @ [[X]\<^sub>R]"
      using assm2 by auto
  next
    fix s X
    assume assm1: "\<rho> \<lesssim>\<^sub>C s @ [[X]\<^sub>R]"
    assume assm2: "\<forall>s\<in>tocks {x. x \<noteq> Tock \<and> x \<noteq> Event e}. \<rho> \<noteq> s \<and> (\<forall>\<sigma>\<in>P. \<rho> \<noteq> s @ [Event e]\<^sub>E # \<sigma>)"
    assume assm3: "s \<in> tocks {x. x \<noteq> Tock \<and> x \<noteq> Event e}"
    assume assm4: "Tock \<notin> X"
    assume assm5: "Event e \<notin> X"
    obtain t Z where "t\<in>tocks {x. x \<noteq> Tock \<and> x \<noteq> Event e}" "\<rho> = t \<or> \<rho> = t @ [[Z]\<^sub>R]" "Z \<subseteq> {x. x \<noteq> Tock \<and> x \<noteq> Event e} \<or> Z \<subseteq> X"
      using assm1 assm3 ctt_prefix_subset_tocks_refusal by blast
    then show "\<exists>s\<in>tocks {x. x \<noteq> Tock \<and> x \<noteq> Event e}. \<exists>X. Tock \<notin> X \<and> Event e \<notin> X \<and> \<rho> = s @ [[X]\<^sub>R]"
      using assm2 assm4 assm5 by auto
  next
    assume assm1: "\<rho> \<lesssim>\<^sub>C \<sigma>"
    assume assm2: "\<forall>s\<in>tocks {x. x \<noteq> Tock \<and> x \<noteq> Event e}. \<rho> \<noteq> s \<and> (\<forall>\<sigma>\<in>P. \<rho> \<noteq> s @ [Event e]\<^sub>E # \<sigma>)"
    assume assm3: "\<sigma> \<in> tocks {x. x \<noteq> Tock \<and> x \<noteq> Event e}"
    obtain s where "s\<in>tocks {x. x \<noteq> Tock \<and> x \<noteq> Event e}" "\<rho> = s \<or> (\<exists>Y. \<rho> = s @ [[Y]\<^sub>R] \<and> Y \<subseteq> {x. x \<noteq> Tock \<and> x \<noteq> Event e})"
      using assm1 assm3 ctt_prefix_subset_tocks by blast
    then show "\<exists>s\<in>tocks {x. x \<noteq> Tock \<and> x \<noteq> Event e}. \<exists>X. Tock \<notin> X \<and> Event e \<notin> X \<and> \<rho> = s @ [[X]\<^sub>R]"
      using assm2 by auto
  next
    fix s \<sigma>'
    assume assm1: "\<rho> \<lesssim>\<^sub>C s @ [Event e]\<^sub>E # \<sigma>'"
    assume assm2: "\<forall>s\<in>tocks {x. x \<noteq> Tock \<and> x \<noteq> Event e}. \<rho> \<noteq> s \<and> (\<forall>\<sigma>\<in>P. \<rho> \<noteq> s @ [Event e]\<^sub>E # \<sigma>)"
    assume assm3: "s \<in> tocks {x. x \<noteq> Tock \<and> x \<noteq> Event e}"
    assume assm4: "\<sigma>' \<in> P"
    thm ctt_prefix_subset_append_split
    from assm1 have "\<rho> \<lesssim>\<^sub>C (s @ [[Event e]\<^sub>E]) @ \<sigma>'"
      by simp
    then obtain a b where a_b_assms: "\<rho> = a @ b" "a \<lesssim>\<^sub>C s @ [[Event e]\<^sub>E]" "b \<lesssim>\<^sub>C \<sigma>'"
      "length a = length (s @ [[Event e]\<^sub>E]) \<and> length [x\<leftarrow>a . x = [Tock]\<^sub>E] = length [x\<leftarrow>(s @ [[Event e]\<^sub>E]) . x = [Tock]\<^sub>E] \<or> b = []"
      using ctt_prefix_subset_append_split by blast
    then obtain s' where s'_assms: "s'\<in>tocks {x. x \<noteq> Tock \<and> x \<noteq> Event e}"
            "s' \<lesssim>\<^sub>C s"
             "a = s' \<or>
              (\<exists>Y. a = s' @ [[Y]\<^sub>R] \<and> Y \<subseteq> {x. x \<noteq> Tock \<and> x \<noteq> Event e} \<and> length [x\<leftarrow>s' . x = [Tock]\<^sub>E] < length [x\<leftarrow>s . x = [Tock]\<^sub>E]) \<or>
              a = s' @ [[Event e]\<^sub>E] \<and> length [x\<leftarrow>s' . x = [Tock]\<^sub>E] = length [x\<leftarrow>s . x = [Tock]\<^sub>E]"
      using ctt_prefix_subset_tocks_event assm3 by blast
    have b_in_P: "b \<in> P"
      using CT1_def CT_CT1 a_b_assms(3) assm4 assms by blast
    from s'_assms have "b \<noteq> [] \<longrightarrow> a = s' @ [[Event e]\<^sub>E] \<and> length [x\<leftarrow>s' . x = [Tock]\<^sub>E] = length [x\<leftarrow>s . x = [Tock]\<^sub>E]"
      using a_b_assms(4) ctt_prefix_subset_length by (auto, fastforce+)
    then have b_empty: "b = []"
      using b_in_P a_b_assms(1) assm2 s'_assms(1) by fastforce
    then have "\<exists>Y. a = s' @ [[Y]\<^sub>R] \<and> Y \<subseteq> {x. x \<noteq> Tock \<and> x \<noteq> Event e} \<and> length [x\<leftarrow>s' . x = [Tock]\<^sub>E] < length [x\<leftarrow>s . x = [Tock]\<^sub>E]"
      using a_b_assms(1) assm2 b_in_P s'_assms(1) s'_assms(3) by blast
    then show "\<exists>s\<in>tocks {x. x \<noteq> Tock \<and> x \<noteq> Event e}. \<exists>X. Tock \<notin> X \<and> Event e \<notin> X \<and> \<rho> = s @ [[X]\<^sub>R]"
      apply (auto, rule_tac x="s'" in bexI, rule_tac x="Y" in exI)
      using b_empty a_b_assms(1) s'_assms(1) by blast+
  qed
next
  fix \<rho> X Y
  assume assm1: "Y \<inter> {ea. ea \<noteq> Tock \<and> \<rho> @ [[ea]\<^sub>E] \<in> e \<rightarrow>\<^sub>C P \<or> ea = Tock \<and> \<rho> @ [[X]\<^sub>R, [ea]\<^sub>E] \<in> e \<rightarrow>\<^sub>C P} = {}"
  assume "\<rho> @ [[X]\<^sub>R] \<in> e \<rightarrow>\<^sub>C P"
  then have "(\<rho> \<in> tocks {x. x \<noteq> Tock \<and> x \<noteq> Event e} \<and> Tock \<notin> X \<and> Event e \<notin> X) \<or>
    (\<exists> s \<sigma>. s \<in> tocks {x. x \<noteq> Tock \<and> x \<noteq> Event e} \<and> \<sigma> \<in> P \<and> \<rho> @ [[X]\<^sub>R] = s @ [Event e]\<^sub>E # \<sigma>)"
    unfolding PrefixCTT_def using end_refusal_notin_tocks by auto
  then show "\<rho> @ [[X \<union> Y]\<^sub>R] \<in> e \<rightarrow>\<^sub>C P"
  proof auto
    assume assm2: "\<rho> \<in> tocks {x. x \<noteq> Tock \<and> x \<noteq> Event e}"
    assume assm3: "Tock \<notin> X"
    assume assm4: "Event e \<notin> X"

    have "Tock \<in> {ea. ea \<noteq> Tock \<and> \<rho> @ [[ea]\<^sub>E] \<in> e \<rightarrow>\<^sub>C P \<or> ea = Tock \<and> \<rho> @ [[X]\<^sub>R, [ea]\<^sub>E] \<in> e \<rightarrow>\<^sub>C P}"
      unfolding PrefixCTT_def by (auto, smt assm2 assm3 assm4 mem_Collect_eq subset_iff tocks.simps tocks_append_tocks)
    then have 1: "Tock \<notin> Y"
      using assm1 by auto
    have "Event e \<in> {ea. ea \<noteq> Tock \<and> \<rho> @ [[ea]\<^sub>E] \<in> e \<rightarrow>\<^sub>C P \<or> ea = Tock \<and> \<rho> @ [[X]\<^sub>R, [ea]\<^sub>E] \<in> e \<rightarrow>\<^sub>C P}"
      unfolding PrefixCTT_def apply (auto)
      using CT_empty assm2 assms by blast
    then have 2: "Event e \<notin> Y"
      using assm1 by auto
    show "\<rho> @ [[X \<union> Y]\<^sub>R] \<in> e \<rightarrow>\<^sub>C P"
      unfolding PrefixCTT_def using 1 2 assm2 assm3 assm4 by (auto)
  next
    fix s \<sigma>
    assume assm2: "s \<in> tocks {x. x \<noteq> Tock \<and> x \<noteq> Event e}"
    assume assm3: "\<sigma> \<in> P"
    assume assm4: "\<rho> @ [[X]\<^sub>R] = s @ [Event e]\<^sub>E # \<sigma>"
    obtain \<sigma>' where \<sigma>'_assm: "\<sigma> = \<sigma>' @ [[X]\<^sub>R]"
      by (metis append_butlast_last_id assm4 cttobs.distinct(1) last.simps last_appendR list.distinct(1))
    have \<rho>_def: "\<rho> = s @ [Event e]\<^sub>E # \<sigma>'"
      using \<sigma>'_assm assm4 by auto
    have 1: "\<And>x. s @ [Event e]\<^sub>E # \<sigma>' @ [[x]\<^sub>E] \<notin> tocks {x. x \<noteq> Tock \<and> x \<noteq> Event e}"
      using mid_event_notin_tocks by force
    have 2: "s @ [Event e]\<^sub>E # \<sigma>' @ [[X]\<^sub>R, [Tock]\<^sub>E] \<notin> tocks {x. x \<noteq> Tock \<and> x \<noteq> Event e}"
      using mid_event_notin_tocks by force
    have "{ea. ea \<noteq> Tock \<and> \<sigma>' @ [[ea]\<^sub>E] \<in> P \<or> ea = Tock \<and> \<sigma>' @ [[X]\<^sub>R, [ea]\<^sub>E] \<in> P} = {ea. ea \<noteq> Tock \<and> \<rho> @ [[ea]\<^sub>E] \<in> e \<rightarrow>\<^sub>C P \<or> ea = Tock \<and> \<rho> @ [[X]\<^sub>R, [ea]\<^sub>E] \<in> e \<rightarrow>\<^sub>C P}"
      unfolding PrefixCTT_def apply auto
      using \<sigma>'_assm assm2 assm4  apply (auto simp add: 1 2)
      by (metis (lifting) append_Cons append_Nil equal_traces_imp_equal_tocks)+
    then have "Y \<inter> {ea. ea \<noteq> Tock \<and> \<sigma>' @ [[ea]\<^sub>E] \<in> P \<or> ea = Tock \<and> \<sigma>' @ [[X]\<^sub>R, [ea]\<^sub>E] \<in> P} = {}"
      using assm1 by auto
    then have "\<sigma>' @ [[X \<union> Y]\<^sub>R] \<in> P"
      using \<sigma>'_assm assm3 assms by (auto simp add: CT2_def CT_def)
    then show "\<rho> @ [[X \<union> Y]\<^sub>R] \<in> e \<rightarrow>\<^sub>C P"
      unfolding PrefixCTT_def using \<rho>_def assm2 by auto
  qed
next
  fix x
  have "\<forall>x\<in>P. CT3_trace x"
    using CT3_def CT_CT3 assms by blast
  also have "\<forall>x \<in> tocks {x. x \<noteq> Tock \<and> x \<noteq> Event e}. CT3_trace x"
    by (metis (mono_tags, lifting) CT3_def CT3_tocks mem_Collect_eq) 
  then show "x \<in> e \<rightarrow>\<^sub>C P \<Longrightarrow> CT3_trace x"
    unfolding PrefixCTT_def using calculation apply auto
    using CT3_append CT3_trace.simps(2) cttWF.simps(2) apply blast
    by (metis (no_types, lifting) CT3_append CT3_trace.simps(2) CT3_trace.simps(4) CT_wf assms cttWF.elims(2) cttWF.simps(4))
    
qed

subsection {* Internal Choice *}

definition IntChoiceCTT :: "'e cttobs list set \<Rightarrow> 'e cttobs list set \<Rightarrow> 'e cttobs list set" (infixl "\<sqinter>\<^sub>C" 56) where
  "P \<sqinter>\<^sub>C Q = P \<union> Q"

lemma IntChoiceCTT_wf: "\<forall> t\<in>P. cttWF t \<Longrightarrow> \<forall> t\<in>Q. cttWF t \<Longrightarrow> \<forall> t\<in>P \<sqinter>\<^sub>C Q. cttWF t"
  unfolding IntChoiceCTT_def by auto

lemma CT_IntChoice:
  assumes "CT P" "CT Q"
  shows "CT (P \<sqinter>\<^sub>C Q)"
  unfolding CT_defs
proof auto
  fix x
  show "x \<in> P \<sqinter>\<^sub>C Q \<Longrightarrow> cttWF x"
    by (metis CT_wf IntChoiceCTT_def Un_iff assms(1) assms(2))
next
  show "P \<sqinter>\<^sub>C Q = {} \<Longrightarrow> False"
    using CT_empty IntChoiceCTT_def assms(1) by blast
next
  fix \<rho> \<sigma>
  show "\<rho> \<lesssim>\<^sub>C \<sigma> \<Longrightarrow> \<sigma> \<in> P \<sqinter>\<^sub>C Q \<Longrightarrow> \<rho> \<in> P \<sqinter>\<^sub>C Q"
    by (metis CT1_def CT_CT1 IntChoiceCTT_def Un_iff assms(1) assms(2))
next
  fix \<rho> X Y
  assume assm1: "\<rho> @ [[X]\<^sub>R] \<in> P \<sqinter>\<^sub>C Q"
  assume assm2: "Y \<inter> {e. e \<noteq> Tock \<and> \<rho> @ [[e]\<^sub>E] \<in> P \<sqinter>\<^sub>C Q \<or> e = Tock \<and> \<rho> @ [[X]\<^sub>R, [e]\<^sub>E] \<in> P \<sqinter>\<^sub>C Q} = {}"
  have 1: "\<rho> @ [[X]\<^sub>R] \<in> P \<or> \<rho> @ [[X]\<^sub>R] \<in> Q"
    using assm1 unfolding IntChoiceCTT_def by auto
  have 2: "{e. e \<noteq> Tock \<and> \<rho> @ [[e]\<^sub>E] \<in> P \<sqinter>\<^sub>C Q \<or> e = Tock \<and> \<rho> @ [[X]\<^sub>R, [e]\<^sub>E] \<in> P \<sqinter>\<^sub>C Q} = 
    {e. e \<noteq> Tock \<and> \<rho> @ [[e]\<^sub>E] \<in> P \<or> e = Tock \<and> \<rho> @ [[X]\<^sub>R, [e]\<^sub>E] \<in> P} \<union> {e. e \<noteq> Tock \<and> \<rho> @ [[e]\<^sub>E] \<in> Q \<or> e = Tock \<and> \<rho> @ [[X]\<^sub>R, [e]\<^sub>E] \<in> Q}"
    unfolding IntChoiceCTT_def by auto
  have 3: "Y \<inter> {e. e \<noteq> Tock \<and> \<rho> @ [[e]\<^sub>E] \<in> P \<or> e = Tock \<and> \<rho> @ [[X]\<^sub>R, [e]\<^sub>E] \<in> P} = {}"
    using 2 assm2 inf_sup_distrib1 by auto
  have 4: "Y \<inter> {e. e \<noteq> Tock \<and> \<rho> @ [[e]\<^sub>E] \<in> Q \<or> e = Tock \<and> \<rho> @ [[X]\<^sub>R, [e]\<^sub>E] \<in> Q} = {}"
    using 2 assm2 inf_sup_distrib1 by auto
  have 5: "\<rho> @ [[X]\<^sub>R] \<in> P \<Longrightarrow> \<rho> @ [[X \<union> Y]\<^sub>R] \<in> P"
    using "3" CT2_def CT_def assms(1) by blast
  have 6: "\<rho> @ [[X]\<^sub>R] \<in> Q \<Longrightarrow> \<rho> @ [[X \<union> Y]\<^sub>R] \<in> Q"
    using "4" CT2_def CT_def assms(2) by blast
  show "\<rho> @ [[X \<union> Y]\<^sub>R] \<in> P \<sqinter>\<^sub>C Q"
    using "1" "5" "6" IntChoiceCTT_def by blast
next
  fix x
  show "x \<in> P \<sqinter>\<^sub>C Q \<Longrightarrow> CT3_trace x"
    by (metis CT3_def CT_CT3 IntChoiceCTT_def UnE assms(1) assms(2))
qed 

subsection {* External Choice *}

definition ExtChoiceCTT :: "'e cttobs list set \<Rightarrow> 'e cttobs list set \<Rightarrow> 'e cttobs list set" (infixl "\<box>\<^sub>C" 57) where
  "P \<box>\<^sub>C Q = {t. \<exists> \<rho>\<in>tocks(UNIV). \<exists> \<sigma> \<tau>. 
    \<rho> @ \<sigma> \<in> P \<and> \<rho> @ \<tau> \<in> Q \<and>
    (\<forall>\<rho>'\<in>tocks(UNIV). \<rho>' \<le>\<^sub>C \<rho> @ \<sigma> \<longrightarrow> \<rho>' \<le>\<^sub>C \<rho>) \<and>
    (\<forall>\<rho>'\<in>tocks(UNIV). \<rho>' \<le>\<^sub>C \<rho> @ \<tau> \<longrightarrow> \<rho>' \<le>\<^sub>C \<rho>) \<and>
    (\<forall> X. \<sigma> = [[X]\<^sub>R] \<longrightarrow> (\<exists> Y. \<tau> = [[Y]\<^sub>R] \<and> (\<forall> e. (e \<in> X = (e \<in> Y)) \<or> (e = Tock)))) \<and>
    (\<forall> X. \<tau> = [[X]\<^sub>R] \<longrightarrow> (\<exists> Y. \<sigma> = [[Y]\<^sub>R] \<and> (\<forall> e. (e \<in> X = (e \<in> Y)) \<or> (e = Tock)))) \<and>
    (t = \<rho> @ \<sigma> \<or> t = \<rho> @ \<tau>)}"

lemma ExtChoiceCTT_wf: "\<forall> t\<in>P. cttWF t \<Longrightarrow> \<forall> t\<in>Q. cttWF t \<Longrightarrow> \<forall> t\<in>P \<box>\<^sub>C Q. cttWF t"
  unfolding ExtChoiceCTT_def by auto

lemma CT0_ExtChoice:
  assumes "CT P" "CT Q"
  shows "CT0 (P \<box>\<^sub>C Q)"
  unfolding CT0_def apply auto
  unfolding ExtChoiceCTT_def apply auto
  using CT_empty assms(1) assms(2) tocks.empty_in_tocks by fastforce

lemma CT1_ExtChoice:
  assumes "CT P" "CT Q"
  shows "CT1 (P \<box>\<^sub>C Q)"
  unfolding CT1_def
proof auto
  fix \<rho> \<sigma> :: "'a cttobs list"
  assume assm1: "\<rho> \<lesssim>\<^sub>C \<sigma>"
  assume assm2: "\<sigma> \<in> P \<box>\<^sub>C Q"
  obtain \<rho>2 where \<rho>2_assms: "\<rho>2 \<le>\<^sub>C \<sigma>" "\<rho> \<subseteq>\<^sub>C \<rho>2"
    using assm1 ctt_prefix_subset_imp_ctt_subset_ctt_prefix by auto
  from assm2 obtain \<sigma>' s t where assm2_assms:
    "\<sigma>'\<in>tocks UNIV"
    "\<sigma>' @ s \<in> P"
    "\<sigma>' @ t \<in> Q"
    "(\<forall>\<rho>'\<in>tocks UNIV. \<rho>' \<le>\<^sub>C \<sigma>' @ s \<longrightarrow> \<rho>' \<le>\<^sub>C \<sigma>')"
    "(\<forall>\<rho>'\<in>tocks UNIV. \<rho>' \<le>\<^sub>C \<sigma>' @ t \<longrightarrow> \<rho>' \<le>\<^sub>C \<sigma>')"
    "\<forall>X. s = [[X]\<^sub>R] \<longrightarrow> (\<exists>Y. t = [[Y]\<^sub>R] \<and> (\<forall>e. (e \<in> X) = (e \<in> Y) \<or> e = Tock))"
    "\<forall>X. t = [[X]\<^sub>R] \<longrightarrow> (\<exists>Y. s = [[Y]\<^sub>R] \<and> (\<forall>e. (e \<in> X) = (e \<in> Y) \<or> e = Tock))"
    "\<sigma> = \<sigma>' @ t \<or> \<sigma> = \<sigma>' @ s"
    unfolding ExtChoiceCTT_def by blast
  from assm2_assms(8) have "\<rho>2 \<in> P \<box>\<^sub>C Q"
  proof (auto)
    assume case_assm: "\<sigma> = \<sigma>' @ s"
    then have \<sigma>_in_P: "\<sigma> \<in> P"
      using assm2_assms(2) by blast
    have \<rho>2_in_P: "\<rho>2 \<in> P"
      using CT1_def CT_CT1 \<rho>2_assms(1) \<sigma>_in_P assms(1) ctt_prefix_imp_prefix_subset by blast
    have "\<rho>2 \<le>\<^sub>C \<sigma>' \<or> (\<exists> \<rho>2'. \<rho>2 = \<sigma>' @ \<rho>2' \<and> \<rho>2' \<le>\<^sub>C s)"
      using \<rho>2_assms(1) case_assm ctt_prefix_append_split by blast
    then show "\<rho>2 \<in> P \<box>\<^sub>C Q"
    proof auto
      assume case_assm2: "\<rho>2 \<le>\<^sub>C \<sigma>'"
      have \<rho>2_in_Q: "\<rho>2 \<in> Q"
        by (meson CT1_def CT_CT1 assm2_assms(3) assms(2) case_assm2 ctt_prefix_concat ctt_prefix_imp_prefix_subset)
      obtain \<rho>' where \<rho>'_assms: "\<rho>' \<in> tocks UNIV" "\<rho>2 = \<rho>' \<or> (\<exists>Y. \<rho>2 = \<rho>' @ [[Y]\<^sub>R])"
        using case_assm2 assm2_assms(1) ctt_prefix_tocks by blast
      then show "\<rho>2 \<in> P \<box>\<^sub>C Q"
      proof auto
        assume case_assm3: "\<rho>2 = \<rho>'"
        then show "\<rho>' \<in> P \<box>\<^sub>C Q"
          using \<rho>2_in_P \<rho>2_in_Q case_assm3 \<rho>'_assms(1) unfolding ExtChoiceCTT_def apply auto
          apply (rule_tac x="\<rho>'" in bexI, auto)
          apply (rule_tac x="[]" in exI, auto)
          apply (rule_tac x="[]" in exI, auto)
          done
      next
        fix Y
        assume case_assm3: "\<rho>2 = \<rho>' @ [[Y]\<^sub>R]"
        then show "\<rho>' @ [[Y]\<^sub>R] \<in> P \<box>\<^sub>C Q"
          using \<rho>2_in_P \<rho>2_in_Q \<rho>'_assms(1) unfolding ExtChoiceCTT_def apply auto
          apply (rule_tac x="\<rho>'" in bexI, auto)
          apply (rule_tac x="[[Y]\<^sub>R]" in exI, auto)
          apply (rule_tac x="[[Y]\<^sub>R]" in exI, auto)
          by (metis butlast_append butlast_snoc ctt_prefix_concat ctt_prefix_decompose end_refusal_notin_tocks)
      qed
    next
      fix \<rho>2'
      assume case_assm2: "\<rho>2' \<le>\<^sub>C s"
      assume case_assm3: "\<rho>2 = \<sigma>' @ \<rho>2'"
      have in_P: "\<sigma>' @ \<rho>2' \<in> P"
        using CT1_def CT_CT1 \<rho>2_assms(1) assm2_assms(2) assms(1) case_assm case_assm3 ctt_prefix_imp_prefix_subset by blast
      show "\<sigma>' @ \<rho>2' \<in> P \<box>\<^sub>C Q"
      proof (cases "\<exists>X. \<rho>2' = [[X]\<^sub>R]", auto)
        fix X
        assume case_assm4: "\<rho>2' = [[X]\<^sub>R]"
        then have case_assm5: "s = [[X]\<^sub>R]"
          using case_assm2
        proof -
          have "cttWF s"
            using CT_wf assm2_assms(1) assm2_assms(2) assms(1) tocks_append_wf2 by fastforce
          then show "\<rho>2' = [[X]\<^sub>R] \<Longrightarrow> \<rho>2' \<le>\<^sub>C s \<Longrightarrow> s = [[X]\<^sub>R]"
            apply (cases s rule:cttWF.cases, auto, insert assm2_assms(1) assm2_assms(4))
            apply (erule_tac x="\<sigma>' @ [[X]\<^sub>R, [Tock]\<^sub>E]" in ballE, auto simp add: ctt_prefix_same_front)
            using ctt_prefix_antisym ctt_prefix_concat apply blast
            apply (induct \<sigma>', auto simp add: tocks.tock_insert_in_tocks)
            by (metis append_Cons subset_UNIV tocks.empty_in_tocks tocks.tock_insert_in_tocks tocks_append_tocks)
        qed
        thm assm2_assms
        then obtain Y where "t = [[Y]\<^sub>R]" "\<forall>e. (e \<in> X) = (e \<in> Y) \<or> e = Tock"
          using assm2_assms(6) by auto
        then have "\<sigma>' @ [[{e\<in>X. e \<noteq> Tock}]\<^sub>R] \<in> Q"
        proof -
          assume "t = [[Y]\<^sub>R]"
          then have "\<sigma>' @ [[Y]\<^sub>R] \<in> Q"
            using assm2_assms(3) by auto
          also assume "\<forall>e. (e \<in> X) = (e \<in> Y) \<or> e = Tock"
          then have "\<sigma>' @ [[{e\<in>X. e \<noteq> Tock}]\<^sub>R] \<lesssim>\<^sub>C \<sigma>' @ [[Y]\<^sub>R]"
            using ctt_prefix_subset_same_front[where r=\<sigma>'] by auto
          then show "\<sigma>' @ [[{e\<in>X. e \<noteq> Tock}]\<^sub>R] \<in> Q"
            using calculation CT1_def CT_CT1 assms(2) by blast
        qed
        then show "\<sigma>' @ [[X]\<^sub>R] \<in> P \<box>\<^sub>C Q"
          unfolding ExtChoiceCTT_def apply auto
          apply (rule_tac x="\<sigma>'" in bexI, simp_all add: assm2_assms(1))
          apply (rule_tac x="[[X]\<^sub>R]" in exI, insert in_P case_assm4, simp)
          apply (rule_tac x="[[{e\<in>X. e \<noteq> Tock}]\<^sub>R]" in exI, insert assm2_assms(4) case_assm5, auto)
          by (metis (no_types, lifting) butlast_append butlast_snoc ctt_prefix_concat ctt_prefix_decompose end_refusal_notin_tocks)
      next
        have \<sigma>'_in_Q: "\<sigma>' \<in> Q"
          using CT1_def CT_CT1 assm2_assms(3) assms(2) ctt_prefix_concat ctt_prefix_imp_prefix_subset by blast
        then show "\<forall>X. \<rho>2' \<noteq> [[X]\<^sub>R] \<Longrightarrow> \<sigma>' @ \<rho>2' \<in> P \<box>\<^sub>C Q"
           unfolding ExtChoiceCTT_def apply auto
           apply (rule_tac x="\<sigma>'" in bexI, simp_all add: assm2_assms(1))
           apply (rule_tac x="\<rho>2'" in exI, simp add: in_P)
           apply (rule_tac x="[]" in exI, auto)
           using \<rho>2_assms(1) assm2_assms(4) case_assm case_assm3 ctt_prefix_trans by blast
       qed
     qed
   next
    assume case_assm: "\<sigma> = \<sigma>' @ t"
    then have \<sigma>_in_Q: "\<sigma> \<in> Q"
      using assm2_assms(3) by blast
    have \<rho>2_in_Q: "\<rho>2 \<in> Q"
      using CT1_def CT_CT1 \<rho>2_assms(1) \<sigma>_in_Q assms(2) ctt_prefix_imp_prefix_subset by blast
    have "\<rho>2 \<le>\<^sub>C \<sigma>' \<or> (\<exists> \<rho>2'. \<rho>2 = \<sigma>' @ \<rho>2' \<and> \<rho>2' \<le>\<^sub>C t)"
      using \<rho>2_assms(1) case_assm ctt_prefix_append_split by blast
    then show "\<rho>2 \<in> P \<box>\<^sub>C Q"
    proof auto
      assume case_assm2: "\<rho>2 \<le>\<^sub>C \<sigma>'"
      have \<rho>2_in_P: "\<rho>2 \<in> P"
        by (meson CT1_def CT_CT1 assm2_assms(2) assms(1) case_assm2 ctt_prefix_concat ctt_prefix_imp_prefix_subset)
      obtain \<rho>' where \<rho>'_assms: "\<rho>' \<in> tocks UNIV" "\<rho>2 = \<rho>' \<or> (\<exists>Y. \<rho>2 = \<rho>' @ [[Y]\<^sub>R])"
        using case_assm2 assm2_assms(1) ctt_prefix_tocks by blast
      then show "\<rho>2 \<in> P \<box>\<^sub>C Q"
      proof auto
        assume case_assm3: "\<rho>2 = \<rho>'"
        then show "\<rho>' \<in> P \<box>\<^sub>C Q"
          using \<rho>2_in_P \<rho>2_in_Q case_assm3 \<rho>'_assms(1) unfolding ExtChoiceCTT_def apply auto
          apply (rule_tac x="\<rho>'" in bexI, auto)
          apply (rule_tac x="[]" in exI, auto)
          apply (rule_tac x="[]" in exI, auto)
          done
      next
        fix Y
        assume case_assm3: "\<rho>2 = \<rho>' @ [[Y]\<^sub>R]"
        then show "\<rho>' @ [[Y]\<^sub>R] \<in> P \<box>\<^sub>C Q"
          using \<rho>2_in_P \<rho>2_in_Q \<rho>'_assms(1) unfolding ExtChoiceCTT_def apply auto
          apply (rule_tac x="\<rho>'" in bexI, auto)
          apply (rule_tac x="[[Y]\<^sub>R]" in exI, auto)
          apply (rule_tac x="[[Y]\<^sub>R]" in exI, auto)
          by (metis butlast_append butlast_snoc ctt_prefix_concat ctt_prefix_decompose end_refusal_notin_tocks)
      qed
    next
      fix \<rho>2'
      assume case_assm2: "\<rho>2' \<le>\<^sub>C t"
      assume case_assm3: "\<rho>2 = \<sigma>' @ \<rho>2'"
      have in_Q: "\<sigma>' @ \<rho>2' \<in> Q"
        using \<rho>2_in_Q case_assm3 by blast
      show "\<sigma>' @ \<rho>2' \<in> P \<box>\<^sub>C Q"
      proof (cases "\<exists>X. \<rho>2' = [[X]\<^sub>R]", auto)
        fix X
        assume case_assm4: "\<rho>2' = [[X]\<^sub>R]"
        then have case_assm5: "t = [[X]\<^sub>R]"
          using case_assm2
        proof -
          have "cttWF t"
            using CT_wf assm2_assms(1) assm2_assms(3) assms(2) tocks_append_wf2 by fastforce
          then show "\<rho>2' = [[X]\<^sub>R] \<Longrightarrow> \<rho>2' \<le>\<^sub>C t \<Longrightarrow> t = [[X]\<^sub>R]"
            apply (cases t rule:cttWF.cases, auto, insert assm2_assms(1) assm2_assms(5))
            apply (erule_tac x="\<sigma>' @ [[X]\<^sub>R, [Tock]\<^sub>E]" in ballE, auto simp add: ctt_prefix_same_front)
            using ctt_prefix_antisym ctt_prefix_concat apply blast
            apply (induct \<sigma>', auto simp add: tocks.tock_insert_in_tocks)
            by (metis append_Cons subset_UNIV tocks.empty_in_tocks tocks.tock_insert_in_tocks tocks_append_tocks)
        qed
        then obtain Y where "s = [[Y]\<^sub>R]" "\<forall>e. (e \<in> X) = (e \<in> Y) \<or> e = Tock"
          using assm2_assms(7) by auto
        then have "\<sigma>' @ [[{e\<in>X. e \<noteq> Tock}]\<^sub>R] \<in> P"
        proof -
          assume "s = [[Y]\<^sub>R]"
          then have "\<sigma>' @ [[Y]\<^sub>R] \<in> P"
            using assm2_assms(2) by auto
          also assume "\<forall>e. (e \<in> X) = (e \<in> Y) \<or> e = Tock"
          then have "\<sigma>' @ [[{e\<in>X. e \<noteq> Tock}]\<^sub>R] \<lesssim>\<^sub>C \<sigma>' @ [[Y]\<^sub>R]"
            using ctt_prefix_subset_same_front[where r=\<sigma>'] by auto
          then show "\<sigma>' @ [[{e\<in>X. e \<noteq> Tock}]\<^sub>R] \<in> P"
            using calculation CT1_def CT_CT1 assms(1) by blast
        qed
        then show "\<sigma>' @ [[X]\<^sub>R] \<in> P \<box>\<^sub>C Q"
          unfolding ExtChoiceCTT_def apply auto
          apply (rule_tac x="\<sigma>'" in bexI, simp_all add: assm2_assms(1))
          apply (rule_tac x="[[{e\<in>X. e \<noteq> Tock}]\<^sub>R]" in exI, insert assm2_assms(4) case_assm5, auto)
          apply (rule_tac x="[[X]\<^sub>R]" in exI, insert in_Q case_assm4 assm2_assms(5), auto)
          by (metis (no_types, lifting) butlast_append butlast_snoc ctt_prefix_concat ctt_prefix_decompose end_refusal_notin_tocks)
      next
        have \<sigma>'_in_P: "\<sigma>' \<in> P"
          using CT1_def CT_CT1 assm2_assms(2) assms(1) ctt_prefix_concat ctt_prefix_imp_prefix_subset by blast
        then show "\<forall>X. \<rho>2' \<noteq> [[X]\<^sub>R] \<Longrightarrow> \<sigma>' @ \<rho>2' \<in> P \<box>\<^sub>C Q"
           unfolding ExtChoiceCTT_def apply auto
           apply (rule_tac x="\<sigma>'" in bexI, simp_all add: assm2_assms(1))
           apply (rule_tac x="[]" in exI, auto)
           apply (rule_tac x="\<rho>2'" in exI, simp add: in_Q)
           using \<rho>2_assms(1) assm2_assms(5) case_assm case_assm3 ctt_prefix_trans by blast
       qed
     qed
   qed
   then obtain \<rho>2' s2 t2 where \<rho>2_split:
     "\<rho>2'\<in>tocks UNIV"
     "\<rho>2' @ s2 \<in> P"
     "\<rho>2' @ t2 \<in> Q"
     "(\<forall>\<rho>'\<in>tocks UNIV. \<rho>' \<le>\<^sub>C \<rho>2' @ s2 \<longrightarrow> \<rho>' \<le>\<^sub>C \<rho>2')"
     "(\<forall>\<rho>'\<in>tocks UNIV. \<rho>' \<le>\<^sub>C \<rho>2' @ t2 \<longrightarrow> \<rho>' \<le>\<^sub>C \<rho>2')"
     "\<forall>X. s2 = [[X]\<^sub>R] \<longrightarrow> (\<exists>Y. t2 = [[Y]\<^sub>R] \<and> (\<forall>e. (e \<in> X) = (e \<in> Y) \<or> e = Tock))"
     "\<forall>X. t2 = [[X]\<^sub>R] \<longrightarrow> (\<exists>Y. s2 = [[Y]\<^sub>R] \<and> (\<forall>e. (e \<in> X) = (e \<in> Y) \<or> e = Tock))"
     "\<rho>2 = \<rho>2' @ t2 \<or> \<rho>2 = \<rho>2' @ s2"
    unfolding ExtChoiceCTT_def by blast
  then show "\<rho> \<in>  P \<box>\<^sub>C Q"
  proof auto
    assume case_assm: "\<rho>2 = \<rho>2' @ t2"
    have \<rho>_wf: "cttWF \<rho>"
      using CT1_def CT_CT1 CT_wf \<rho>2_assms(2) \<rho>2_split(3) assms(2) case_assm ctt_subset_imp_prefix_subset by blast
    then obtain \<rho>' \<rho>'' where \<rho>'_\<rho>''_assms:
      "\<rho> = \<rho>' @ \<rho>''"
      "\<rho>' \<in> tocks UNIV"
      "\<forall>t\<in>tocks UNIV. t \<le>\<^sub>C \<rho>' @ \<rho>'' \<longrightarrow> t \<le>\<^sub>C \<rho>'"
      using split_tocks_longest by blast
    then have \<rho>'_\<rho>''_ctt_subset: "\<rho>' \<subseteq>\<^sub>C \<rho>2' \<and> \<rho>'' \<subseteq>\<^sub>C t2"
      using CT_wf \<rho>_wf \<rho>2_assms(2) \<rho>2_split(1) \<rho>2_split(3) \<rho>2_split(5) assms(2) case_assm ctt_subset_longest_tocks by blast
    then have \<rho>'_in_P_Q: "\<rho>' \<in> P \<and> \<rho>' \<in> Q"
      by (meson CT_CT1 CT_defs(3) \<rho>2_split(2) \<rho>2_split(3) assms(1) assms(2) ctt_prefix_concat ctt_prefix_subset_ctt_prefix_trans ctt_subset_imp_prefix_subset)
    show "\<rho> \<in> P \<box>\<^sub>C Q"
    proof (cases "\<exists> X. t2 = [[X]\<^sub>R]")
      assume case_assm2: "\<exists> X. t2 = [[X]\<^sub>R]"
      then obtain X where t2_def: "t2 = [[X]\<^sub>R]"
        by auto
      then have "\<exists> Y. Y \<subseteq> X \<and> \<rho>'' = [[Y]\<^sub>R]"
        using \<rho>'_\<rho>''_ctt_subset apply (simp, induct \<rho>'' t2 rule:ctt_subset.induct, simp_all)
        using ctt_subset_same_length by force
      then obtain Y where Y_assms: "Y \<subseteq> X \<and> \<rho>'' = [[Y]\<^sub>R]"
        by auto
      then obtain Z where Z_assms: "s2 = [[Z]\<^sub>R] \<and> (\<forall>e. (e \<in> X) = (e \<in> Z) \<or> e = Tock)"
        using t2_def \<rho>2_split(7) by blast
      then have "{e. e \<in> Y \<and> e \<noteq> Tock} \<subseteq> Z"
        using Y_assms by blast
      then have 1: "\<rho>' @ [[{e. e \<in> Y \<and> e \<noteq> Tock}]\<^sub>R] \<subseteq>\<^sub>C \<rho>2' @ [[Z]\<^sub>R]"
        by (simp add: \<rho>'_\<rho>''_ctt_subset ctt_subset_combine)
      have 2: "\<rho>' @ [[Y]\<^sub>R] \<subseteq>\<^sub>C \<rho>2' @ [[X]\<^sub>R]"
        using Y_assms \<rho>'_\<rho>''_assms(1) \<rho>2_assms(2) case_assm t2_def by blast
      have 3: "\<rho>' @ [[{e. e \<in> Y \<and> e \<noteq> Tock}]\<^sub>R] \<in> P"
        using "1" CT1_def CT_CT1 Z_assms \<rho>2_split(2) assms(1) ctt_subset_imp_prefix_subset by blast
      have 4: "\<rho>' @ [[Y]\<^sub>R] \<in> Q"
        using "2" CT1_def CT_CT1 \<rho>2_split(3) assms(2) ctt_subset_imp_prefix_subset t2_def by blast
      then show "\<rho> \<in> P \<box>\<^sub>C Q"
        unfolding ExtChoiceCTT_def apply auto
        apply (rule_tac x="\<rho>'" in bexI, auto simp add: \<rho>'_\<rho>''_assms)
        apply (rule_tac x="[[{e. e \<in> Y \<and> e \<noteq> Tock}]\<^sub>R]" in exI, auto simp add: 3)
        apply (rule_tac x="[[Y]\<^sub>R]" in exI, auto simp add: 4 Y_assms)
        apply (metis (no_types, lifting) butlast_append butlast_snoc ctt_prefix_concat ctt_prefix_decompose end_refusal_notin_tocks)
        by (simp add: Y_assms \<rho>'_\<rho>''_assms(3))
    next
      assume "\<nexists>X. t2 = [[X]\<^sub>R]"
      then have "\<nexists>X. \<rho>'' = [[X]\<^sub>R]"
        using \<rho>'_\<rho>''_ctt_subset by (auto, cases t2 rule:cttWF.cases, auto)
      then show "\<rho> \<in> P \<box>\<^sub>C Q"
        unfolding ExtChoiceCTT_def apply auto
        apply (rule_tac x="\<rho>'" in bexI, auto simp add: \<rho>'_\<rho>''_assms)
        apply (rule_tac x="[]" in exI, auto simp add: \<rho>'_in_P_Q)
        apply (rule_tac x="\<rho>''" in exI, auto)
        using CT1_def CT_CT1 \<rho>'_\<rho>''_assms(1) \<rho>2_assms(2) \<rho>2_split(3) assms(2) case_assm ctt_subset_imp_prefix_subset apply blast
        using \<rho>'_\<rho>''_assms(3) by blast
    qed
  next
    assume case_assm: "\<rho>2 = \<rho>2' @ s2"
    have \<rho>_wf: "cttWF \<rho>"
      by (metis CT_def ExtChoiceCTT_wf assm1 assm2 assms(1) assms(2) ctt_prefix_subset_cttWF)
    then obtain \<rho>' \<rho>'' where \<rho>'_\<rho>''_assms:
      "\<rho> = \<rho>' @ \<rho>''"
      "\<rho>' \<in> tocks UNIV"
      "\<forall>t\<in>tocks UNIV. t \<le>\<^sub>C \<rho>' @ \<rho>'' \<longrightarrow> t \<le>\<^sub>C \<rho>'"
      using split_tocks_longest by blast
    then have \<rho>'_\<rho>''_ctt_subset: "\<rho>' \<subseteq>\<^sub>C \<rho>2' \<and> \<rho>'' \<subseteq>\<^sub>C s2"
      using CT_wf \<rho>2_assms(2) \<rho>2_split(1) \<rho>2_split(2) \<rho>2_split(4) \<rho>_wf assms(1) case_assm ctt_subset_longest_tocks by blast
    then have \<rho>'_in_P_Q: "\<rho>' \<in> P \<and> \<rho>' \<in> Q"
      by (meson CT_CT1 CT_defs(3) \<rho>2_split(2) \<rho>2_split(3) assms(1) assms(2) ctt_prefix_concat ctt_prefix_subset_ctt_prefix_trans ctt_subset_imp_prefix_subset)
    show "\<rho> \<in> P \<box>\<^sub>C Q"
    proof (cases "\<exists> X. s2 = [[X]\<^sub>R]")
      assume case_assm2: "\<exists> X. s2 = [[X]\<^sub>R]"
      then obtain X where s2_def: "s2 = [[X]\<^sub>R]"
        by auto
      then have "\<exists> Y. Y \<subseteq> X \<and> \<rho>'' = [[Y]\<^sub>R]"
        using \<rho>'_\<rho>''_ctt_subset apply (simp, induct \<rho>'' s2 rule:ctt_subset.induct, simp_all)
        using ctt_subset_same_length by force
      then obtain Y where Y_assms: "Y \<subseteq> X \<and> \<rho>'' = [[Y]\<^sub>R]"
        by auto
      then obtain Z where Z_assms: "t2 = [[Z]\<^sub>R] \<and> (\<forall>e. (e \<in> X) = (e \<in> Z) \<or> e = Tock)"
        using s2_def \<rho>2_split(6) by blast
      then have "{e. e \<in> Y \<and> e \<noteq> Tock} \<subseteq> Z"
        using Y_assms by blast
      then have 1: "\<rho>' @ [[{e. e \<in> Y \<and> e \<noteq> Tock}]\<^sub>R] \<subseteq>\<^sub>C \<rho>2' @ [[Z]\<^sub>R]"
        by (simp add: \<rho>'_\<rho>''_ctt_subset ctt_subset_combine)
      have 2: "\<rho>' @ [[Y]\<^sub>R] \<subseteq>\<^sub>C \<rho>2' @ [[X]\<^sub>R]"
        using Y_assms \<rho>'_\<rho>''_assms(1) \<rho>2_assms(2) case_assm s2_def by blast
      have 3: "\<rho>' @ [[{e. e \<in> Y \<and> e \<noteq> Tock}]\<^sub>R] \<in> Q"
        using "1" CT1_def CT_CT1 Z_assms \<rho>2_split(3) assms(2) ctt_subset_imp_prefix_subset by blast
      have 4: "\<rho>' @ [[Y]\<^sub>R] \<in> P"
        using "2" CT1_def CT_CT1 \<rho>2_split(2) assms(1) ctt_subset_imp_prefix_subset s2_def by blast
      then show "\<rho> \<in> P \<box>\<^sub>C Q"
        unfolding ExtChoiceCTT_def apply auto
        apply (rule_tac x="\<rho>'" in bexI, auto simp add: \<rho>'_\<rho>''_assms)
        apply (rule_tac x="[[Y]\<^sub>R]" in exI, auto simp add: 4 Y_assms)
        apply (rule_tac x="[[{e. e \<in> Y \<and> e \<noteq> Tock}]\<^sub>R]" in exI, auto simp add: 3)
        using Y_assms \<rho>'_\<rho>''_assms(3) apply blast
        by (metis (no_types, lifting) butlast_append butlast_snoc ctt_prefix_concat ctt_prefix_decompose end_refusal_notin_tocks)
    next
      assume "\<nexists>X. s2 = [[X]\<^sub>R]"
      then have "\<nexists>X. \<rho>'' = [[X]\<^sub>R]"
        using \<rho>'_\<rho>''_ctt_subset by (auto, cases s2 rule:cttWF.cases, auto)
      then show "\<rho> \<in> P \<box>\<^sub>C Q"
        unfolding ExtChoiceCTT_def apply auto
        apply (rule_tac x="\<rho>'" in bexI, auto simp add: \<rho>'_\<rho>''_assms)
        apply (rule_tac x="\<rho>''" in exI, auto)
        using CT1_def CT_CT1 \<rho>'_\<rho>''_assms(1) \<rho>2_assms(2) \<rho>2_split(2) assms(1) case_assm ctt_subset_imp_prefix_subset apply blast
        apply (rule_tac x="[]" in exI, auto simp add: \<rho>'_in_P_Q)
        using \<rho>'_\<rho>''_assms(3) by blast
    qed
  qed
qed

lemma CT2_ExtChoice:
  assumes "CT P" "CT Q"
  shows "CT2 (P \<box>\<^sub>C Q)"
  unfolding CT2_def
proof auto
  fix \<rho> :: "'a cttobs list"
  fix X Y :: "'a cttevent set"
  assume assm1: "\<rho> @ [[X]\<^sub>R] \<in> P \<box>\<^sub>C Q"
  assume assm2: "Y \<inter> {e. e \<noteq> Tock \<and> \<rho> @ [[e]\<^sub>E] \<in> P \<box>\<^sub>C Q \<or> e = Tock \<and> \<rho> @ [[X]\<^sub>R, [e]\<^sub>E] \<in> P \<box>\<^sub>C Q} = {}"
  from assm1 have "cttWF \<rho>"
    by (metis CT_def ExtChoiceCTT_wf assms(1) assms(2) ctt_prefix_concat ctt_prefix_imp_prefix_subset ctt_prefix_subset_cttWF)
  then obtain \<rho>' \<rho>'' where \<rho>_split: "\<rho>'\<in>tocks UNIV \<and> \<rho> = \<rho>' @ \<rho>'' \<and> (\<forall>t'\<in>tocks UNIV. t' \<le>\<^sub>C \<rho> \<longrightarrow> t' \<le>\<^sub>C \<rho>')"
    using split_tocks_longest by blast
  have \<rho>'_in_P_Q: "\<rho>' \<in> P \<and> \<rho>' \<in> Q"
    using assm1 unfolding ExtChoiceCTT_def apply auto
    apply (metis CT1_def CT_CT1 \<rho>_split assms(1) ctt_prefix_concat ctt_prefix_imp_prefix_subset)
    apply (metis CT1_def CT_CT1 \<rho>_split append.assoc assms(2) ctt_prefix_concat ctt_prefix_imp_prefix_subset)
    apply (metis CT1_def CT_CT1 \<rho>_split append.assoc assms(1) ctt_prefix_concat ctt_prefix_imp_prefix_subset)
    by (metis CT1_def CT_CT1 \<rho>_split assms(2) ctt_prefix_concat ctt_prefix_imp_prefix_subset)
  have set1: "{e. e \<noteq> Tock \<and> \<rho> @ [[e]\<^sub>E] \<in> P \<box>\<^sub>C Q} = {e. e \<noteq> Tock \<and> \<rho> @ [[e]\<^sub>E] \<in> P} \<union> {e. e \<noteq> Tock \<and> \<rho> @ [[e]\<^sub>E] \<in> Q}"
  proof auto
    fix x :: "'a cttevent"
    assume "\<rho> @ [[x]\<^sub>E] \<in> P \<box>\<^sub>C Q"
    then have "\<rho> @ [[x]\<^sub>E] \<in> P \<or> \<rho> @ [[x]\<^sub>E] \<in> Q"
      unfolding ExtChoiceCTT_def by auto
    then show "\<rho> @ [[x]\<^sub>E] \<notin> Q \<Longrightarrow> \<rho> @ [[x]\<^sub>E] \<in> P"
      by auto
  next
    fix x :: "'a cttevent"
    assume "x \<noteq> Tock" "\<rho> @ [[x]\<^sub>E] \<in> P"
    then show "\<rho> @ [[x]\<^sub>E] \<in> P \<box>\<^sub>C Q"
      unfolding ExtChoiceCTT_def apply auto
      apply (rule_tac x="\<rho>'" in bexI, simp_all add: \<rho>_split)
      apply (rule_tac x="\<rho>'' @ [[x]\<^sub>E]" in exI, simp_all)
      apply (rule_tac x="[]" in exI, simp add: \<rho>'_in_P_Q)
      apply (auto, case_tac "\<rho>''' \<le>\<^sub>C \<rho>' @ \<rho>''")
      using \<rho>_split apply blast
      by (metis append.assoc append_Cons append_Nil ctt_prefix_notfront_is_whole cttevent.exhaust end_event_notin_tocks mid_tick_notin_tocks)
  next
    fix x :: "'a cttevent"
    assume "x \<noteq> Tock" "\<rho> @ [[x]\<^sub>E] \<in> Q"
    then show "\<rho> @ [[x]\<^sub>E] \<in> P \<box>\<^sub>C Q"
      unfolding ExtChoiceCTT_def apply auto
      apply (rule_tac x="\<rho>'" in bexI, simp_all add: \<rho>_split)
      apply (rule_tac x="[]" in exI, simp add: \<rho>'_in_P_Q)
      apply (auto, case_tac "\<rho>''' \<le>\<^sub>C \<rho>' @ \<rho>''")
      using \<rho>_split apply blast
      by (metis append.assoc append_Cons append_Nil ctt_prefix_notfront_is_whole cttevent.exhaust end_event_notin_tocks mid_tick_notin_tocks)
  qed
  have set2: "{e. e = Tock \<and> \<rho>'' = [] \<and> \<rho> @ [[X]\<^sub>R, [e]\<^sub>E] \<in> P \<box>\<^sub>C Q} = 
    {e. e = Tock \<and> \<rho>'' = [] \<and> \<rho> @ [[X]\<^sub>R, [e]\<^sub>E] \<in> P} \<inter> {e. e = Tock \<and> \<rho>'' = [] \<and> \<rho> @ [[X]\<^sub>R, [e]\<^sub>E] \<in> Q}"
  proof auto
    assume case_assms: "\<rho> @ [[X]\<^sub>R, [Tock]\<^sub>E] \<in> P \<box>\<^sub>C Q" "\<rho>'' = []"
    then have "\<rho>' @ [[X]\<^sub>R, [Tock]\<^sub>E] \<in> P \<box>\<^sub>C Q"
      by (simp add: \<rho>_split)
    then obtain r s t where rst_assms: 
      "r \<in> tocks UNIV"
      "r @ s \<in> P"
      "r @ t \<in> Q"
      "\<forall>x\<in>tocks UNIV. x \<le>\<^sub>C r @ s \<longrightarrow> x \<le>\<^sub>C r"
      "\<forall>x\<in>tocks UNIV. x \<le>\<^sub>C r @ t \<longrightarrow> x \<le>\<^sub>C r"
      "(\<rho>' @ [[X]\<^sub>R, [Tock]\<^sub>E] = r @ s \<or> \<rho>' @ [[X]\<^sub>R, [Tock]\<^sub>E] = r @ t)"
      unfolding ExtChoiceCTT_def by auto
    have in_tocks: "\<rho>' @ [[X]\<^sub>R, [Tock]\<^sub>E] \<in> tocks UNIV"
      by (simp add: \<rho>_split tocks.empty_in_tocks tocks.tock_insert_in_tocks tocks_append_tocks)
    then have r_def: "r = \<rho>' @ [[X]\<^sub>R, [Tock]\<^sub>E]"
      using ctt_prefix_refl rst_assms(4) rst_assms(5) rst_assms(6) self_extension_ctt_prefix by fastforce
    then have "r \<in> P \<and> r \<in> Q"
      by (smt CT1_def CT_CT1 rst_assms assms(1) assms(2) ctt_prefix_concat ctt_prefix_imp_prefix_subset in_tocks rst_assms(4))
    then show "\<rho> @ [[X]\<^sub>R, [Tock]\<^sub>E] \<in> P"
      by (simp add: r_def \<rho>_split case_assms(2))
  next
    assume case_assms: "\<rho> @ [[X]\<^sub>R, [Tock]\<^sub>E] \<in> P \<box>\<^sub>C Q" "\<rho>'' = []"
    then have "\<rho>' @ [[X]\<^sub>R, [Tock]\<^sub>E] \<in> P \<box>\<^sub>C Q"
      by (simp add: \<rho>_split)
    then obtain r s t where rst_assms: 
      "r \<in> tocks UNIV"
      "r @ s \<in> P"
      "r @ t \<in> Q"
      "\<forall>x\<in>tocks UNIV. x \<le>\<^sub>C r @ s \<longrightarrow> x \<le>\<^sub>C r"
      "\<forall>x\<in>tocks UNIV. x \<le>\<^sub>C r @ t \<longrightarrow> x \<le>\<^sub>C r"
      "(\<rho>' @ [[X]\<^sub>R, [Tock]\<^sub>E] = r @ s \<or> \<rho>' @ [[X]\<^sub>R, [Tock]\<^sub>E] = r @ t)"
      unfolding ExtChoiceCTT_def by auto
    have in_tocks: "\<rho>' @ [[X]\<^sub>R, [Tock]\<^sub>E] \<in> tocks UNIV"
      by (simp add: \<rho>_split tocks.empty_in_tocks tocks.tock_insert_in_tocks tocks_append_tocks)
    then have r_def: "r = \<rho>' @ [[X]\<^sub>R, [Tock]\<^sub>E]"
      using ctt_prefix_refl rst_assms(4) rst_assms(5) rst_assms(6) self_extension_ctt_prefix by fastforce
    then have "r \<in> P \<and> r \<in> Q"
      by (smt CT1_def CT_CT1 rst_assms assms(1) assms(2) ctt_prefix_concat ctt_prefix_imp_prefix_subset in_tocks rst_assms(4))
    then show "\<rho> @ [[X]\<^sub>R, [Tock]\<^sub>E] \<in> Q"
      by (simp add: r_def \<rho>_split case_assms(2))
  next
    assume case_assms: "\<rho> @ [[X]\<^sub>R, [Tock]\<^sub>E] \<in> P" "\<rho>'' = []" "\<rho> @ [[X]\<^sub>R, [Tock]\<^sub>E] \<in> Q"
    then have "\<rho>' @ [[X]\<^sub>R, [Tock]\<^sub>E] \<in> P \<and> \<rho>' @ [[X]\<^sub>R, [Tock]\<^sub>E] \<in> Q"
      by (simp add: \<rho>_split)
    also have "\<rho>' @ [[X]\<^sub>R, [Tock]\<^sub>E] \<in> tocks UNIV"
      by (simp add: \<rho>_split tocks.empty_in_tocks tocks.tock_insert_in_tocks tocks_append_tocks)
    then show "\<rho> @ [[X]\<^sub>R, [Tock]\<^sub>E] \<in> P \<box>\<^sub>C Q"
      unfolding ExtChoiceCTT_def apply auto
      apply (rule_tac x="\<rho>' @ [[X]\<^sub>R, [Tock]\<^sub>E]" in bexI, simp_all)
      apply (rule_tac x="[]" in exI, simp_all add: calculation)
      apply (rule_tac x="[]" in exI, simp_all add: calculation)
      by (simp add: \<rho>_split case_assms(2))
  qed
  have set3: "{e. e = Tock \<and> \<rho>'' \<noteq> [] \<and> \<rho> @ [[X]\<^sub>R, [e]\<^sub>E] \<in> P \<box>\<^sub>C Q} = 
    {e. e = Tock \<and> \<rho>'' \<noteq> [] \<and> \<rho> @ [[X]\<^sub>R, [e]\<^sub>E] \<in> P} \<union> {e. e = Tock \<and> \<rho>'' \<noteq> [] \<and> \<rho> @ [[X]\<^sub>R, [e]\<^sub>E] \<in> Q}"
  proof auto
    assume "\<rho>'' \<noteq> []" "\<rho> @ [[X]\<^sub>R, [Tock]\<^sub>E] \<in> P \<box>\<^sub>C Q"
    then show "\<rho> @ [[X]\<^sub>R, [Tock]\<^sub>E] \<notin> Q \<Longrightarrow> \<rho> @ [[X]\<^sub>R, [Tock]\<^sub>E] \<in> P"
      unfolding ExtChoiceCTT_def by auto
  next
    assume \<rho>''_nonempty: "\<rho>'' \<noteq> []"
    assume in_P: "\<rho> @ [[X]\<^sub>R, [Tock]\<^sub>E] \<in> P"
    have full_notin_tocks: "\<rho>' @ \<rho>'' @ [[X]\<^sub>R, [Tock]\<^sub>E] \<notin> tocks UNIV"
        by (metis \<rho>''_nonempty \<rho>_split append.assoc ctt_prefix_refl nontocks_append_tocks self_extension_ctt_prefix tocks.empty_in_tocks tocks.tock_insert_in_tocks top_greatest)
    have "\<forall>x\<in>tocks UNIV. x \<le>\<^sub>C \<rho> @ [[X]\<^sub>R, [Tock]\<^sub>E] \<longrightarrow> x \<le>\<^sub>C \<rho>'"
    proof (auto simp add: \<rho>_split)
      fix x :: "'a cttobs list"
      assume x_in_tocks: "x \<in> tocks UNIV"
      assume "x \<le>\<^sub>C \<rho>' @ \<rho>'' @ [[X]\<^sub>R, [Tock]\<^sub>E]"
      also have "\<And> y. x \<le>\<^sub>C y @ [[X]\<^sub>R, [Tock]\<^sub>E] \<Longrightarrow> x \<le>\<^sub>C y \<or> x = y @ [[X]\<^sub>R] \<or> x = y @ [[X]\<^sub>R, [Tock]\<^sub>E]"
      proof -
        fix y
        show "x \<le>\<^sub>C y @ [[X]\<^sub>R, [Tock]\<^sub>E] \<Longrightarrow> x \<le>\<^sub>C y \<or> x = y @ [[X]\<^sub>R] \<or> x = y @ [[X]\<^sub>R, [Tock]\<^sub>E]"
          using ctt_prefix.elims(2) ctt_prefix_antisym by (induct x y rule:ctt_prefix.induct, auto, fastforce)
      qed
      then have "x \<le>\<^sub>C \<rho>' @ \<rho>'' \<or> x = \<rho>' @ \<rho>'' @ [[X]\<^sub>R] \<or> x = \<rho>' @ \<rho>'' @ [[X]\<^sub>R, [Tock]\<^sub>E]"
        using calculation by force
      then show "x \<le>\<^sub>C \<rho>'"
        apply auto
        apply (simp add: \<rho>_split x_in_tocks)
        apply (metis append_assoc end_refusal_notin_tocks x_in_tocks)
        using full_notin_tocks x_in_tocks by blast
    qed
    then show "\<rho> @ [[X]\<^sub>R, [Tock]\<^sub>E] \<in> P \<box>\<^sub>C Q"
      unfolding ExtChoiceCTT_def apply auto
      apply (rule_tac x="\<rho>'" in bexI, auto simp add: \<rho>_split)
      apply (rule_tac x="\<rho>'' @ [[X]\<^sub>R, [Tock]\<^sub>E]" in exI, insert \<rho>_split in_P, auto)
      apply (rule_tac x="[]" in exI, auto simp add: \<rho>'_in_P_Q)
      done
  next
    assume \<rho>''_nonempty: "\<rho>'' \<noteq> []"
    assume in_Q: "\<rho> @ [[X]\<^sub>R, [Tock]\<^sub>E] \<in> Q"
    have full_notin_tocks: "\<rho>' @ \<rho>'' @ [[X]\<^sub>R, [Tock]\<^sub>E] \<notin> tocks UNIV"
        by (metis \<rho>''_nonempty \<rho>_split append.assoc ctt_prefix_refl nontocks_append_tocks self_extension_ctt_prefix tocks.empty_in_tocks tocks.tock_insert_in_tocks top_greatest)
    have "\<forall>x\<in>tocks UNIV. x \<le>\<^sub>C \<rho> @ [[X]\<^sub>R, [Tock]\<^sub>E] \<longrightarrow> x \<le>\<^sub>C \<rho>'"
    proof (auto simp add: \<rho>_split)
      fix x :: "'a cttobs list"
      assume x_in_tocks: "x \<in> tocks UNIV"
      assume "x \<le>\<^sub>C \<rho>' @ \<rho>'' @ [[X]\<^sub>R, [Tock]\<^sub>E]"
      also have "\<And> y. x \<le>\<^sub>C y @ [[X]\<^sub>R, [Tock]\<^sub>E] \<Longrightarrow> x \<le>\<^sub>C y \<or> x = y @ [[X]\<^sub>R] \<or> x = y @ [[X]\<^sub>R, [Tock]\<^sub>E]"
      proof -
        fix y
        show "x \<le>\<^sub>C y @ [[X]\<^sub>R, [Tock]\<^sub>E] \<Longrightarrow> x \<le>\<^sub>C y \<or> x = y @ [[X]\<^sub>R] \<or> x = y @ [[X]\<^sub>R, [Tock]\<^sub>E]"
          using ctt_prefix.elims(2) ctt_prefix_antisym by (induct x y rule:ctt_prefix.induct, auto, fastforce)
      qed
      then have "x \<le>\<^sub>C \<rho>' @ \<rho>'' \<or> x = \<rho>' @ \<rho>'' @ [[X]\<^sub>R] \<or> x = \<rho>' @ \<rho>'' @ [[X]\<^sub>R, [Tock]\<^sub>E]"
        using calculation by force
      then show "x \<le>\<^sub>C \<rho>'"
        apply auto
        apply (simp add: \<rho>_split x_in_tocks)
        apply (metis append_assoc end_refusal_notin_tocks x_in_tocks)
        using full_notin_tocks x_in_tocks by blast
    qed
    then show "\<rho> @ [[X]\<^sub>R, [Tock]\<^sub>E] \<in> P \<box>\<^sub>C Q"
      unfolding ExtChoiceCTT_def apply auto
      apply (rule_tac x="\<rho>'" in bexI, auto simp add: \<rho>_split)
      apply (rule_tac x="[]" in exI, auto simp add: \<rho>'_in_P_Q)
      apply (insert \<rho>_split in_Q, auto)
      done
  qed
  thm set1 set2 set3
  have in_P_or_Q: "\<rho> @ [[X]\<^sub>R] \<in> P \<or> \<rho> @ [[X]\<^sub>R] \<in> Q"
    using assm1 unfolding ExtChoiceCTT_def by auto
  show "\<rho> @ [[X \<union> Y]\<^sub>R] \<in> P \<box>\<^sub>C Q"
  proof (cases "\<rho>'' \<noteq> []", auto)
    assume case_assm: "\<rho>'' \<noteq> []"
    have "{e. e \<noteq> Tock \<and> \<rho> @ [[e]\<^sub>E] \<in> P \<box>\<^sub>C Q \<or> e = Tock \<and> \<rho> @ [[X]\<^sub>R, [e]\<^sub>E] \<in> P \<box>\<^sub>C Q}
      = {e. e \<noteq> Tock \<and> \<rho> @ [[e]\<^sub>E] \<in> P \<or> e = Tock \<and> \<rho> @ [[X]\<^sub>R, [e]\<^sub>E] \<in> P} \<union> {e. e \<noteq> Tock \<and> \<rho> @ [[e]\<^sub>E] \<in> Q \<or> e = Tock \<and> \<rho> @ [[X]\<^sub>R, [e]\<^sub>E] \<in> Q}"
      (is "?lhs = ?rhs")
    proof -
      have "?lhs = {e. e \<noteq> Tock \<and> \<rho> @ [[e]\<^sub>E] \<in> P \<box>\<^sub>C Q} \<union> {e. e = Tock \<and> \<rho> @ [[X]\<^sub>R, [e]\<^sub>E] \<in> P \<box>\<^sub>C Q}"
        by auto
      also have "... = {e. e \<noteq> Tock \<and> \<rho> @ [[e]\<^sub>E] \<in> P} \<union> {e. e \<noteq> Tock \<and> \<rho> @ [[e]\<^sub>E] \<in> Q} \<union> {e. e = Tock \<and> \<rho> @ [[X]\<^sub>R, [e]\<^sub>E] \<in> P \<box>\<^sub>C Q}"
        using set1 by auto
      also have "... = {e. e \<noteq> Tock \<and> \<rho> @ [[e]\<^sub>E] \<in> P} \<union> {e. e \<noteq> Tock \<and> \<rho> @ [[e]\<^sub>E] \<in> Q} \<union> {e. e = Tock \<and> \<rho> @ [[X]\<^sub>R, [e]\<^sub>E] \<in> P} \<union> {e. e = Tock \<and> \<rho> @ [[X]\<^sub>R, [e]\<^sub>E] \<in> Q}"
        using set3 case_assm by auto
      also have "... = ?rhs"
        by auto
      then show "?lhs = ?rhs"
        using calculation by auto
    qed
    then have 
      "(Y \<inter> {e. e \<noteq> Tock \<and> \<rho> @ [[e]\<^sub>E] \<in> P \<or> e = Tock \<and> \<rho> @ [[X]\<^sub>R, [e]\<^sub>E] \<in> P})
        \<union> (Y \<inter> {e. e \<noteq> Tock \<and> \<rho> @ [[e]\<^sub>E] \<in> Q \<or> e = Tock \<and> \<rho> @ [[X]\<^sub>R, [e]\<^sub>E] \<in> Q}) = {}"
      using assm2 inf_sup_distrib1 by auto
    then have "Y \<inter> {e. e \<noteq> Tock \<and> \<rho> @ [[e]\<^sub>E] \<in> P \<or> e = Tock \<and> \<rho> @ [[X]\<^sub>R, [e]\<^sub>E] \<in> P} = {}
      \<and> Y \<inter> {e. e \<noteq> Tock \<and> \<rho> @ [[e]\<^sub>E] \<in> Q \<or> e = Tock \<and> \<rho> @ [[X]\<^sub>R, [e]\<^sub>E] \<in> Q} = {}"
      by auto
    then have "\<rho> @ [[X \<union> Y]\<^sub>R] \<in> P \<or> \<rho> @ [[X \<union> Y]\<^sub>R] \<in> Q"
      using CT2_def CT_def assms(1) assms(2) in_P_or_Q by auto
    then show "\<rho> @ [[X \<union> Y]\<^sub>R] \<in> P \<box>\<^sub>C Q"
      unfolding ExtChoiceCTT_def apply auto
      apply (rule_tac x="\<rho>'" in bexI, auto simp add: \<rho>_split)
      apply (rule_tac x="\<rho>'' @ [[X \<union> Y]\<^sub>R]" in exI, auto)
      apply (rule_tac x="[]" in exI, auto simp add: \<rho>_split \<rho>'_in_P_Q case_assm)
      apply (metis \<rho>_split append.assoc ctt_prefix_notfront_is_whole end_refusal_notin_tocks)
      apply (rule_tac x="\<rho>'" in bexI, auto simp add: \<rho>_split)
      apply (rule_tac x="[]" in exI, auto simp add: \<rho>_split \<rho>'_in_P_Q case_assm)
      apply (metis \<rho>_split append.assoc ctt_prefix_notfront_is_whole end_refusal_notin_tocks)
      done
  next
    assume case_assm: "\<rho>'' = []"
    have "\<rho> @ [[{e. e \<in> X \<and> e \<noteq> Tock}]\<^sub>R] \<lesssim>\<^sub>C \<rho> @ [[X]\<^sub>R]"
      by (induct \<rho>, auto, case_tac a, auto)
    then have "\<rho> @ [[{e. e \<in> X \<and> e \<noteq> Tock}]\<^sub>R] \<in> P \<box>\<^sub>C Q"
      using CT1_ExtChoice CT1_def assm1 assms(1) assms(2) by blast
    then have "\<rho>' @ [[{e. e \<in> X \<and> e \<noteq> Tock}]\<^sub>R] \<in> P \<box>\<^sub>C Q"
      by (simp add: \<rho>_split case_assm)
    then have in_P_and_Q: "\<rho>' @ [[{e. e \<in> X \<and> e \<noteq> Tock}]\<^sub>R] \<in> P \<and> \<rho>' @ [[{e. e \<in> X \<and> e \<noteq> Tock}]\<^sub>R] \<in> Q"
      unfolding ExtChoiceCTT_def
    proof auto
      fix \<rho> \<sigma> \<tau> :: "'a cttobs list"
      assume case_assm1: "\<rho> \<in> tocks UNIV"
      assume case_assm2: "\<forall>\<rho>'\<in>tocks UNIV. \<rho>' \<le>\<^sub>C \<rho> @ \<sigma> \<longrightarrow> \<rho>' \<le>\<^sub>C \<rho>"
      assume case_assm3: "\<rho>' @ [[{e \<in> X. e \<noteq> Tock}]\<^sub>R] = \<rho> @ \<sigma>"
      assume case_assm4: "\<forall>X. \<sigma> = [[X]\<^sub>R] \<longrightarrow> (\<exists>Y. \<tau> = [[Y]\<^sub>R] \<and> (\<forall>e. (e \<in> X) = (e \<in> Y) \<or> e = Tock))"
      assume case_assm5: "\<rho> @ \<tau> \<in> Q"
      have \<rho>_def: "\<rho> = \<rho>'"
        by (metis (no_types, lifting) \<rho>_split butlast_append butlast_snoc case_assm1 case_assm2 case_assm3 ctt_prefix_antisym ctt_prefix_concat end_refusal_notin_tocks)
      then have \<sigma>_def: "\<sigma> = [[{e \<in> X. e \<noteq> Tock}]\<^sub>R]"
        using case_assm3 by blast
      obtain Y where Y_assms: "\<tau> = [[Y]\<^sub>R]" "\<forall>e. (e \<in> X) = (e \<in> Y) \<or> e = Tock"
        using case_assm4 by (erule_tac x="{e. e \<in> X \<and> e \<noteq> Tock}" in allE, simp add: \<sigma>_def, auto)
      then have "\<rho>' @ [[{e \<in> X. e \<noteq> Tock}]\<^sub>R] \<lesssim>\<^sub>C \<rho>' @ [[Y]\<^sub>R]"
        by (induct \<rho>', auto, case_tac a, auto)
      then have "\<rho>' @ [[{e \<in> X. e \<noteq> Tock}]\<^sub>R] \<in> Q"
        using CT1_def CT_CT1 Y_assms(1) \<rho>_def assms(2) case_assm5 by blast
      then show "\<rho> @ \<sigma> \<in> Q"
        by (simp add: case_assm3)
    next
      fix \<rho> \<sigma> \<tau> :: "'a cttobs list"
      assume case_assm1: "\<rho> \<in> tocks UNIV"
      assume case_assm2: "\<forall>\<rho>'\<in>tocks UNIV. \<rho>' \<le>\<^sub>C \<rho> @ \<tau> \<longrightarrow> \<rho>' \<le>\<^sub>C \<rho>"
      assume case_assm3: "\<rho>' @ [[{e \<in> X. e \<noteq> Tock}]\<^sub>R] = \<rho> @ \<tau>"
      assume case_assm4: "\<forall>X. \<tau> = [[X]\<^sub>R] \<longrightarrow> (\<exists>Y. \<sigma> = [[Y]\<^sub>R] \<and> (\<forall>e. (e \<in> X) = (e \<in> Y) \<or> e = Tock))"
      assume case_assm5: "\<rho> @ \<sigma> \<in> P"
      have \<rho>_def: "\<rho> = \<rho>'"
        by (metis (no_types, lifting) \<rho>_split butlast_append butlast_snoc case_assm1 case_assm2 case_assm3 ctt_prefix_antisym ctt_prefix_concat end_refusal_notin_tocks)
      then have \<sigma>_def: "\<tau> = [[{e \<in> X. e \<noteq> Tock}]\<^sub>R]"
        using case_assm3 by blast
      obtain Y where Y_assms: "\<sigma> = [[Y]\<^sub>R]" "\<forall>e. (e \<in> X) = (e \<in> Y) \<or> e = Tock"
        using case_assm4 by (erule_tac x="{e. e \<in> X \<and> e \<noteq> Tock}" in allE, simp add: \<sigma>_def, auto)
      then have "\<rho>' @ [[{e \<in> X. e \<noteq> Tock}]\<^sub>R] \<lesssim>\<^sub>C \<rho>' @ [[Y]\<^sub>R]"
        by (induct \<rho>', auto, case_tac a, auto)
      then have "\<rho>' @ [[{e \<in> X. e \<noteq> Tock}]\<^sub>R] \<in> P"
        using CT1_def CT_CT1 Y_assms(1) \<rho>_def assms(1) case_assm5 by blast
      then show "\<rho> @ \<tau> \<in> P"
        by (simp add: case_assm3)
    qed
    have notocks_assm2: "{e. e \<in> Y \<and> e \<noteq> Tock} \<inter> {e. e \<noteq> Tock \<and> \<rho> @ [[e]\<^sub>E] \<in> P \<or> e = Tock \<and> \<rho> @ [[{e. e \<in> X \<and> e \<noteq> Tock}]\<^sub>R, [e]\<^sub>E] \<in> P} = {} 
        \<and> {e. e \<in> Y \<and> e \<noteq> Tock} \<inter> {e. e \<noteq> Tock \<and> \<rho> @ [[e]\<^sub>E] \<in> Q \<or> e = Tock \<and> \<rho> @ [[{e. e \<in> X \<and> e \<noteq> Tock}]\<^sub>R, [e]\<^sub>E] \<in> Q} = {}"
      using set1 assm2 by blast
    have CT2_P_Q: "CT2 P \<and> CT2 Q"
      by (simp add: CT_CT2 assms(1) assms(2))
    then have notock_X_Y_in_P_Q: "\<rho> @ [[{e. e \<in> X \<union> Y \<and> e \<noteq> Tock}]\<^sub>R] \<in> P \<and> \<rho> @ [[{e. e \<in> X \<union> Y \<and> e \<noteq> Tock}]\<^sub>R] \<in> Q"
      unfolding CT2_def
    proof auto
      assume "\<forall>\<rho> X Y. \<rho> @ [[X]\<^sub>R] \<in> P \<and> 
          Y \<inter> {e. e \<noteq> Tock \<and> \<rho> @ [[e]\<^sub>E] \<in> P \<or> e = Tock \<and> \<rho> @ [[X]\<^sub>R, [e]\<^sub>E] \<in> P} = {} \<longrightarrow>
            \<rho> @ [[X \<union> Y]\<^sub>R] \<in> P"
      then have "\<rho> @ [[{e. e \<in> X \<and> e \<noteq> Tock} \<union> {e. e \<in> Y \<and> e \<noteq> Tock}]\<^sub>R] \<in> P"
        using in_P_and_Q notocks_assm2 case_assm \<rho>_split by auto
      also have "\<rho> @ [[{e. e \<in> X \<and> e \<noteq> Tock} \<union> {e. e \<in> Y \<and> e \<noteq> Tock}]\<^sub>R] = \<rho> @ [[{e. (e \<in> X \<or> e \<in> Y) \<and> e \<noteq> Tock}]\<^sub>R]"
        by auto
      then show "\<rho> @ [[{e. (e \<in> X \<or> e \<in> Y) \<and> e \<noteq> Tock}]\<^sub>R] \<in> P"
        using calculation by auto
    next
      assume "\<forall>\<rho> X Y. \<rho> @ [[X]\<^sub>R] \<in> Q \<and> 
          Y \<inter> {e. e \<noteq> Tock \<and> \<rho> @ [[e]\<^sub>E] \<in> Q \<or> e = Tock \<and> \<rho> @ [[X]\<^sub>R, [e]\<^sub>E] \<in> Q} = {} \<longrightarrow>
            \<rho> @ [[X \<union> Y]\<^sub>R] \<in> Q"
      then have "\<rho> @ [[{e. e \<in> X \<and> e \<noteq> Tock} \<union> {e. e \<in> Y \<and> e \<noteq> Tock}]\<^sub>R] \<in> Q"
        using in_P_and_Q notocks_assm2 case_assm \<rho>_split by auto
      also have "\<rho> @ [[{e. e \<in> X \<and> e \<noteq> Tock} \<union> {e. e \<in> Y \<and> e \<noteq> Tock}]\<^sub>R] = \<rho> @ [[{e. (e \<in> X \<or> e \<in> Y) \<and> e \<noteq> Tock}]\<^sub>R]"
        by auto
      then show "\<rho> @ [[{e. (e \<in> X \<or> e \<in> Y) \<and> e \<noteq> Tock}]\<^sub>R] \<in> Q"
        using calculation by auto
    qed
    have in_P_or_Q: "\<rho> @ [[X]\<^sub>R] \<in> P \<or> \<rho> @ [[X]\<^sub>R] \<in> Q"
      using assm1 unfolding ExtChoiceCTT_def by auto
    show "\<rho> @ [[X \<union> Y]\<^sub>R] \<in> P \<box>\<^sub>C Q"
    proof (cases "Tock \<in> Y")
      assume case_assm2: "Tock \<in> Y"
      have assm2_nontock_P: "{e. e \<in> Y \<and> e \<noteq> Tock} \<inter> {e. e \<noteq> Tock \<and> \<rho> @ [[e]\<^sub>E] \<in> P} = {}"
        using assm2 set1 by auto
      have assm2_nontock_Q: "{e. e \<in> Y \<and> e \<noteq> Tock} \<inter> {e. e \<noteq> Tock \<and> \<rho> @ [[e]\<^sub>E] \<in> Q} = {}"
        using assm2 set1 by auto
      have "{e. e \<in> Y \<and> e = Tock} \<inter> {e. e = Tock \<and> \<rho> @ [[X]\<^sub>R, [e]\<^sub>E] \<in> P \<box>\<^sub>C Q} = {}"
        using assm2 by auto
      then have "Tock \<notin> {e. e = Tock \<and> \<rho> @ [[X]\<^sub>R, [e]\<^sub>E] \<in> P \<box>\<^sub>C Q}"
        using case_assm2 by auto
      then have "Tock \<notin> {e. e = Tock \<and> \<rho> @ [[X]\<^sub>R, [e]\<^sub>E] \<in> P} \<inter> {e. e = Tock \<and> \<rho> @ [[X]\<^sub>R, [e]\<^sub>E] \<in> Q}"
        using set2 case_assm by auto
      then have "({e. e \<in> Y \<and> e = Tock} \<inter> {e. e = Tock \<and> \<rho> @ [[X]\<^sub>R, [e]\<^sub>E] \<in> P} = {} \<and> {e. e \<in> Y \<and> e = Tock} \<inter> {e. e = Tock \<and> \<rho> @ [[X]\<^sub>R, [e]\<^sub>E] \<in> Q} = {})
        \<or> (\<rho> @ [[X]\<^sub>R, [Tock]\<^sub>E] \<in> P \<and> {e. e \<in> Y \<and> e = Tock} \<inter> {e. e = Tock \<and> \<rho> @ [[X]\<^sub>R, [e]\<^sub>E] \<in> Q} = {})
        \<or> ({e. e \<in> Y \<and> e = Tock} \<inter> {e. e = Tock \<and> \<rho> @ [[X]\<^sub>R, [e]\<^sub>E] \<in> P} = {} \<and> \<rho> @ [[X]\<^sub>R, [Tock]\<^sub>E] \<in> Q)"
        by auto
      then have "(Y \<inter> {e. e \<noteq> Tock \<and> \<rho> @ [[e]\<^sub>E] \<in> P \<or> e = Tock \<and> \<rho> @ [[X]\<^sub>R, [e]\<^sub>E] \<in> P} = {} \<and> Y \<inter> {e. e \<noteq> Tock \<and> \<rho> @ [[e]\<^sub>E] \<in> Q \<or> e = Tock \<and> \<rho> @ [[X]\<^sub>R, [e]\<^sub>E] \<in> Q} = {})
        \<or> (\<rho> @ [[X]\<^sub>R, [Tock]\<^sub>E] \<in> P \<and> Y \<inter> {e. e \<noteq> Tock \<and> \<rho> @ [[e]\<^sub>E] \<in> Q \<or> e = Tock \<and> \<rho> @ [[X]\<^sub>R, [e]\<^sub>E] \<in> Q} = {})
        \<or> (Y \<inter> {e. e \<noteq> Tock \<and> \<rho> @ [[e]\<^sub>E] \<in> P \<or> e = Tock \<and> \<rho> @ [[X]\<^sub>R, [e]\<^sub>E] \<in> P} = {} \<and> \<rho> @ [[X]\<^sub>R, [Tock]\<^sub>E] \<in> Q)"
        using assm2_nontock_P assm2_nontock_Q by (safe, blast+)
      then show "\<rho> @ [[X \<union> Y]\<^sub>R] \<in> P \<box>\<^sub>C Q"
      proof safe
        assume case_assm3: "Y \<inter> {e. e \<noteq> Tock \<and> \<rho> @ [[e]\<^sub>E] \<in> P \<or> e = Tock \<and> \<rho> @ [[X]\<^sub>R, [e]\<^sub>E] \<in> P} = {}"
        assume case_assm4: "Y \<inter> {e. e \<noteq> Tock \<and> \<rho> @ [[e]\<^sub>E] \<in> Q \<or> e = Tock \<and> \<rho> @ [[X]\<^sub>R, [e]\<^sub>E] \<in> Q} = {}"
        show "\<rho> @ [[X \<union> Y]\<^sub>R] \<in> P \<box>\<^sub>C Q"
          using in_P_or_Q
        proof auto
          assume case_assm5: "\<rho> @ [[X]\<^sub>R] \<in> P"
          then have "\<rho> @ [[X \<union> Y]\<^sub>R] \<in> P"
            using CT2_P_Q case_assm3 unfolding CT2_def by auto
          also have "\<rho> @ [[{e \<in> X \<union> Y. e \<noteq> Tock}]\<^sub>R] \<in> Q"
            using notock_X_Y_in_P_Q by auto
          then show "\<rho> @ [[X \<union> Y]\<^sub>R] \<in> P \<box>\<^sub>C Q"
            unfolding ExtChoiceCTT_def using calculation apply auto
            apply (rule_tac x="\<rho>'" in bexI, simp_all add: \<rho>_split case_assm)
            apply (rule_tac x="[[X \<union> Y]\<^sub>R]" in exI, simp_all)
            apply (rule_tac x="[[{e \<in> X \<union> Y. e \<noteq> Tock}]\<^sub>R]" in exI, auto)
            using ctt_prefix_notfront_is_whole end_refusal_notin_tocks by blast+
        next
          assume case_assm5: "\<rho> @ [[X]\<^sub>R] \<in> Q"
          then have "\<rho> @ [[X \<union> Y]\<^sub>R] \<in> Q"
            using CT2_P_Q case_assm4 unfolding CT2_def by auto
          also have "\<rho> @ [[{e \<in> X \<union> Y. e \<noteq> Tock}]\<^sub>R] \<in> P"
            using notock_X_Y_in_P_Q by auto
          then show "\<rho> @ [[X \<union> Y]\<^sub>R] \<in> P \<box>\<^sub>C Q"
            unfolding ExtChoiceCTT_def using calculation apply auto
            apply (rule_tac x="\<rho>'" in bexI, simp_all add: \<rho>_split case_assm)
            apply (rule_tac x="[[{e \<in> X \<union> Y. e \<noteq> Tock}]\<^sub>R]" in exI, auto)
            apply (rule_tac x="[[X \<union> Y]\<^sub>R]" in exI, simp_all)
            using ctt_prefix_notfront_is_whole end_refusal_notin_tocks by blast+
        qed
      next
        assume case_assm3: "\<rho> @ [[X]\<^sub>R, [Tock]\<^sub>E] \<in> P"
        assume case_assm4: "Y \<inter> {e. e \<noteq> Tock \<and> \<rho> @ [[e]\<^sub>E] \<in> Q \<or> e = Tock \<and> \<rho> @ [[X]\<^sub>R, [e]\<^sub>E] \<in> Q} = {}"
        have CT1_P: "CT1 P"
          by (simp add: CT_CT1 assms(1))
        have "\<rho> @ [[X]\<^sub>R] \<lesssim>\<^sub>C \<rho> @ [[X]\<^sub>R, [Tock]\<^sub>E]"
          using ctt_prefix_subset_same_front by fastforce
        then have in_P: "\<rho> @ [[X]\<^sub>R] \<in> P"
          using CT1_P case_assm3 unfolding CT1_def by auto 
        have CT3_P: "CT3 P"
          by (simp add: CT_CT3 assms(1))
        then have "Tock \<notin> X"
          using CT3_def CT3_end_tock \<rho>'_in_P_Q \<rho>_split case_assm case_assm3 by force
        then have in_Q: "\<rho> @ [[X]\<^sub>R] \<in> Q"
          using assm1 unfolding ExtChoiceCTT_def
        proof auto
          fix r s t :: "'a cttobs list"
          assume 1: "r \<in> tocks UNIV"
          assume 2: "r @ s \<in> P"
          assume 3: "r @ t \<in> Q"
          assume 4: "\<forall>\<rho>''\<in>tocks UNIV. \<rho>'' \<le>\<^sub>C r @ s \<longrightarrow> \<rho>'' \<le>\<^sub>C r"
          assume 5: "\<forall>\<rho>''\<in>tocks UNIV. \<rho>'' \<le>\<^sub>C r @ t \<longrightarrow> \<rho>'' \<le>\<^sub>C r"
          assume 6: "\<forall>X. s = [[X]\<^sub>R] \<longrightarrow> (\<exists>Y. t = [[Y]\<^sub>R] \<and> (\<forall>e. (e \<in> X) = (e \<in> Y) \<or> e = Tock))"
          assume 7: "\<forall>X. t = [[X]\<^sub>R] \<longrightarrow> (\<exists>Y. s = [[Y]\<^sub>R] \<and> (\<forall>e. (e \<in> X) = (e \<in> Y) \<or> e = Tock))"
          assume 8: "\<rho> @ [[X]\<^sub>R] = r @ s"
          assume 9: "Tock \<notin> X"
          have r_is_\<rho>: "r = \<rho>"
            by (metis "1" "4" "8" \<rho>_split append.right_neutral butlast_append butlast_snoc case_assm ctt_prefix_antisym ctt_prefix_concat end_refusal_notin_tocks)
          then have "s = [[X]\<^sub>R]"
            using "8" by blast
          then obtain Y where Y_assms: "t = [[Y]\<^sub>R]" "\<forall>e. (e \<in> X) = (e \<in> Y) \<or> e = Tock"
            using "6" by auto
          then have "\<rho> @ [[Y]\<^sub>R] \<in> Q"
            using "3" r_is_\<rho> by blast
          also have "\<rho> @ [[X]\<^sub>R] \<lesssim>\<^sub>C \<rho> @ [[Y]\<^sub>R]"
            by (metis "9" Y_assms(2) ctt_prefix_subset.simps(2) ctt_prefix_subset_refl ctt_prefix_subset_same_front subsetI)
          then have "\<rho> @ [[X]\<^sub>R] \<in> Q"
            using CT1_def CT_CT1 assms(2) calculation by blast
          then show "r @ s \<in> Q"
            using "8" by auto
        qed
        then have "\<rho> @ [[X \<union> Y]\<^sub>R] \<in> Q"
          using CT2_P_Q CT2_def case_assm4 by blast
        then show "\<rho> @ [[X \<union> Y]\<^sub>R] \<in> P \<box>\<^sub>C Q"
          unfolding ExtChoiceCTT_def using notock_X_Y_in_P_Q apply auto
          apply (rule_tac x="\<rho>'" in bexI, simp_all add: \<rho>_split case_assm)
          apply (rule_tac x="[[{e \<in> X \<union> Y. e \<noteq> Tock}]\<^sub>R]" in exI, auto)
          apply (rule_tac x="[[X \<union> Y]\<^sub>R]" in exI, simp_all)
          using ctt_prefix_notfront_is_whole end_refusal_notin_tocks by blast+
      next
        assume case_assm3: "\<rho> @ [[X]\<^sub>R, [Tock]\<^sub>E] \<in> Q"
        assume case_assm4: "Y \<inter> {e. e \<noteq> Tock \<and> \<rho> @ [[e]\<^sub>E] \<in> P \<or> e = Tock \<and> \<rho> @ [[X]\<^sub>R, [e]\<^sub>E] \<in> P} = {}"
        have CT1_P: "CT1 Q"
          by (simp add: CT_CT1 assms(2))
        have "\<rho> @ [[X]\<^sub>R] \<lesssim>\<^sub>C \<rho> @ [[X]\<^sub>R, [Tock]\<^sub>E]"
          using ctt_prefix_subset_same_front by fastforce
        then have in_P: "\<rho> @ [[X]\<^sub>R] \<in> Q"
          using CT1_P case_assm3 unfolding CT1_def by auto 
        have CT3_P: "CT3 Q"
          by (simp add: CT_CT3 assms(2))
        then have "Tock \<notin> X"
          using CT3_def CT3_end_tock \<rho>'_in_P_Q \<rho>_split case_assm case_assm3 by force
        then have in_P: "\<rho> @ [[X]\<^sub>R] \<in> P"
          using assm1 unfolding ExtChoiceCTT_def
        proof auto
          fix r s t :: "'a cttobs list"
          assume 1: "r \<in> tocks UNIV"
          assume 2: "r @ s \<in> P"
          assume 3: "r @ t \<in> Q"
          assume 4: "\<forall>\<rho>''\<in>tocks UNIV. \<rho>'' \<le>\<^sub>C r @ s \<longrightarrow> \<rho>'' \<le>\<^sub>C r"
          assume 5: "\<forall>\<rho>''\<in>tocks UNIV. \<rho>'' \<le>\<^sub>C r @ t \<longrightarrow> \<rho>'' \<le>\<^sub>C r"
          assume 6: "\<forall>X. s = [[X]\<^sub>R] \<longrightarrow> (\<exists>Y. t = [[Y]\<^sub>R] \<and> (\<forall>e. (e \<in> X) = (e \<in> Y) \<or> e = Tock))"
          assume 7: "\<forall>X. t = [[X]\<^sub>R] \<longrightarrow> (\<exists>Y. s = [[Y]\<^sub>R] \<and> (\<forall>e. (e \<in> X) = (e \<in> Y) \<or> e = Tock))"
          assume 8: "\<rho> @ [[X]\<^sub>R] = r @ t"
          assume 9: "Tock \<notin> X"
          have r_is_\<rho>: "r = \<rho>"
            by (metis "1" "5" "8" \<rho>_split append.right_neutral butlast_append butlast_snoc case_assm ctt_prefix_antisym ctt_prefix_concat end_refusal_notin_tocks)
          then have "t = [[X]\<^sub>R]"
            using "8" by blast
          then obtain Y where Y_assms: "s = [[Y]\<^sub>R]" "\<forall>e. (e \<in> X) = (e \<in> Y) \<or> e = Tock"
            using "7" by auto
          then have "\<rho> @ [[Y]\<^sub>R] \<in> P"
            using "2" r_is_\<rho> by blast
          also have "\<rho> @ [[X]\<^sub>R] \<lesssim>\<^sub>C \<rho> @ [[Y]\<^sub>R]"
            by (metis "9" Y_assms(2) ctt_prefix_subset.simps(2) ctt_prefix_subset_refl ctt_prefix_subset_same_front subsetI)
          then have "\<rho> @ [[X]\<^sub>R] \<in> P"
            using CT1_def CT_CT1 assms(1) calculation by blast
          then show "r @ t \<in> P"
            using "8" by auto
        qed
        then have "\<rho> @ [[X \<union> Y]\<^sub>R] \<in> P"
          using CT2_P_Q CT2_def case_assm4 by blast
        then show "\<rho> @ [[X \<union> Y]\<^sub>R] \<in> P \<box>\<^sub>C Q"
          unfolding ExtChoiceCTT_def using notock_X_Y_in_P_Q apply auto
          apply (rule_tac x="\<rho>'" in bexI, simp_all add: \<rho>_split case_assm)
          apply (rule_tac x="[[X \<union> Y]\<^sub>R]" in exI, simp_all)
          apply (rule_tac x="[[{e \<in> X \<union> Y. e \<noteq> Tock}]\<^sub>R]" in exI, auto)
          using ctt_prefix_notfront_is_whole end_refusal_notin_tocks by blast+
      qed
    next
      assume case_assm2: "Tock \<notin> Y"
      then have "Y \<inter> {e. e \<noteq> Tock \<and> \<rho> @ [[e]\<^sub>E] \<in> P \<box>\<^sub>C Q \<or> e = Tock \<and> \<rho> @ [[X]\<^sub>R, [e]\<^sub>E] \<in> P \<box>\<^sub>C Q}
        = {e. e \<in> Y \<and> e \<noteq> Tock} \<inter> {e. e \<noteq> Tock \<and> \<rho> @ [[e]\<^sub>E] \<in> P \<box>\<^sub>C Q \<or> e = Tock \<and> \<rho> @ [[X]\<^sub>R, [e]\<^sub>E] \<in> P \<box>\<^sub>C Q}"
        by auto
      also have "... = {e. e \<in> Y \<and> e \<noteq> Tock} \<inter> {e. e \<noteq> Tock \<and> \<rho> @ [[e]\<^sub>E] \<in> P \<box>\<^sub>C Q}"
        by auto
      also have "... = {e. e \<in> Y \<and> e \<noteq> Tock} \<inter> ({e. e \<noteq> Tock \<and> \<rho> @ [[e]\<^sub>E] \<in> P} \<union> {e. e \<noteq> Tock \<and> \<rho> @ [[e]\<^sub>E] \<in> Q})"
        using set1 by auto
      also have "... = ({e. e \<in> Y \<and> e \<noteq> Tock} \<inter> {e. e \<noteq> Tock \<and> \<rho> @ [[e]\<^sub>E] \<in> P}) \<union> ({e. e \<in> Y \<and> e \<noteq> Tock} \<inter> {e. e \<noteq> Tock \<and> \<rho> @ [[e]\<^sub>E] \<in> Q})"
        by auto
      also have "... = ({e. e \<in> Y \<and> e \<noteq> Tock} \<inter> {e. e \<noteq> Tock \<and> \<rho> @ [[e]\<^sub>E] \<in> P \<or> e = Tock \<and> \<rho> @ [[X]\<^sub>R, [e]\<^sub>E] \<in> P}) 
        \<union> ({e. e \<in> Y \<and> e \<noteq> Tock} \<inter> {e. e \<noteq> Tock \<and> \<rho> @ [[e]\<^sub>E] \<in> Q \<or> e = Tock \<and> \<rho> @ [[X]\<^sub>R, [e]\<^sub>E] \<in> Q})"
        by auto
      also have "... = (Y \<inter> {e. e \<noteq> Tock \<and> \<rho> @ [[e]\<^sub>E] \<in> P \<or> e = Tock \<and> \<rho> @ [[X]\<^sub>R, [e]\<^sub>E] \<in> P}) 
        \<union> (Y \<inter> {e. e \<noteq> Tock \<and> \<rho> @ [[e]\<^sub>E] \<in> Q \<or> e = Tock \<and> \<rho> @ [[X]\<^sub>R, [e]\<^sub>E] \<in> Q})"
        using case_assm2 by auto
      then have assm2_expand: "Y \<inter> {e. e \<noteq> Tock \<and> \<rho> @ [[e]\<^sub>E] \<in> P \<or> e = Tock \<and> \<rho> @ [[X]\<^sub>R, [e]\<^sub>E] \<in> P} = {}
          \<and> Y \<inter> {e. e \<noteq> Tock \<and> \<rho> @ [[e]\<^sub>E] \<in> Q \<or> e = Tock \<and> \<rho> @ [[X]\<^sub>R, [e]\<^sub>E] \<in> Q} = {}"
        using calculation assm2 by auto
      show "\<rho> @ [[X \<union> Y]\<^sub>R] \<in> P \<box>\<^sub>C Q"
        using in_P_or_Q
      proof auto
        assume  case_assm3: "\<rho> @ [[X]\<^sub>R] \<in> P"
        have "CT2 P"
          by (simp add: CT2_P_Q)
        then have "\<rho> @ [[X \<union> Y]\<^sub>R] \<in> P"
          unfolding CT2_def using case_assm3 assm2_expand by auto
        then show  "\<rho> @ [[X \<union> Y]\<^sub>R] \<in> P \<box>\<^sub>C Q"
          unfolding ExtChoiceCTT_def using notock_X_Y_in_P_Q apply auto
          apply (rule_tac x="\<rho>'" in bexI, simp_all add: \<rho>_split case_assm)
          apply (rule_tac x="[[X \<union> Y]\<^sub>R]" in exI, simp_all)
          apply (rule_tac x="[[{e \<in> X \<union> Y. e \<noteq> Tock}]\<^sub>R]" in exI, auto)
          using ctt_prefix_notfront_is_whole end_refusal_notin_tocks by blast+
      next
        assume  case_assm3: "\<rho> @ [[X]\<^sub>R] \<in> Q"
        have "CT2 Q"
          by (simp add: CT2_P_Q)
        then have "\<rho> @ [[X \<union> Y]\<^sub>R] \<in> Q"
          unfolding CT2_def using case_assm3 assm2_expand by auto
        then show  "\<rho> @ [[X \<union> Y]\<^sub>R] \<in> P \<box>\<^sub>C Q"
          unfolding ExtChoiceCTT_def using notock_X_Y_in_P_Q apply auto
          apply (rule_tac x="\<rho>'" in bexI, simp_all add: \<rho>_split case_assm)
          apply (rule_tac x="[[{e \<in> X \<union> Y. e \<noteq> Tock}]\<^sub>R]" in exI, auto)
          apply (rule_tac x="[[X \<union> Y]\<^sub>R]" in exI, simp_all)
          using ctt_prefix_notfront_is_whole end_refusal_notin_tocks by blast+
      qed
    qed
  qed
qed

lemma CT3_ExtChoice: 
  assumes "CT3 P" "CT3 Q"
  shows "CT3 (P \<box>\<^sub>C Q)"
  using assms unfolding CT3_def ExtChoiceCTT_def by auto

lemma CT_ExtChoice:
  assumes "CT P" "CT Q"
  shows "CT (P \<box>\<^sub>C Q)"
  unfolding CT_def apply auto
  apply (metis CT_def ExtChoiceCTT_wf assms(1) assms(2))
  apply (simp add: CT0_ExtChoice assms(1) assms(2))
  apply (simp add: CT1_ExtChoice assms(1) assms(2))
  apply (simp add: CT2_ExtChoice assms(1) assms(2))
  apply  (simp add: CT3_ExtChoice CT_CT3 assms(1) assms(2))
  done

lemma ExtChoiceCTT_comm: "P \<box>\<^sub>C Q = Q \<box>\<^sub>C P"
  unfolding ExtChoiceCTT_def by auto

(*lemma ExtChoiceCTT_aux_assoc: 
  assumes "\<forall>t\<in>P. cttWF t" "\<forall>t\<in>Q. cttWF t" "\<forall>t\<in>R. cttWF t"
  shows "P \<box>\<^sup>C (Q \<box>\<^sup>C R) = (P \<box>\<^sup>C Q) \<box>\<^sup>C R"
  (is "?lhs = ?rhs")
proof -
  have "?lhs = {t. \<exists> \<rho>\<in>tocks(UNIV). \<exists> \<sigma> \<tau>. 
    \<rho> @ \<sigma> \<in> P \<and> \<rho> @ \<tau> \<in> (Q \<box>\<^sup>C R) \<and>
    (\<forall>\<rho>'\<in>tocks(UNIV). \<rho>' \<le>\<^sub>C \<rho> @ \<sigma> \<longrightarrow> \<rho>' \<le>\<^sub>C \<rho>) \<and>
    (\<forall>\<rho>'\<in>tocks(UNIV). \<rho>' \<le>\<^sub>C \<rho> @ \<tau> \<longrightarrow> \<rho>' \<le>\<^sub>C \<rho>) \<and>
    (((\<exists> X. \<sigma> = [[X]\<^sub>R]) \<or> (\<exists> X. \<tau> = [[X]\<^sub>R])) \<longrightarrow> \<rho> @ \<sigma> = \<rho> @ \<tau>) \<and>
    (t = \<rho> @ \<sigma> \<or> t = \<rho> @ \<tau>)}"
    unfolding ExtChoiceCTT_aux_def by simp
  also have "... =  {t. \<exists> \<rho>\<in>tocks(UNIV). \<exists> \<sigma> \<tau>. 
    \<rho> @ \<sigma> \<in> (P \<box>\<^sup>C Q) \<and> \<rho> @ \<tau> \<in> R \<and>
    (\<forall>\<rho>'\<in>tocks(UNIV). \<rho>' \<le>\<^sub>C \<rho> @ \<sigma> \<longrightarrow> \<rho>' \<le>\<^sub>C \<rho>) \<and>
    (\<forall>\<rho>'\<in>tocks(UNIV). \<rho>' \<le>\<^sub>C \<rho> @ \<tau> \<longrightarrow> \<rho>' \<le>\<^sub>C \<rho>) \<and>
    (((\<exists> X. \<sigma> = [[X]\<^sub>R]) \<or> (\<exists> X. \<tau> = [[X]\<^sub>R])) \<longrightarrow> \<rho> @ \<sigma> = \<rho> @ \<tau>) \<and>
    (t = \<rho> @ \<sigma> \<or> t = \<rho> @ \<tau>)}"
  proof (safe)
    fix \<rho> \<sigma> \<tau> :: "'a cttobs list"
    assume assm1: "\<rho> \<in> tocks UNIV"
    assume assm2: "\<rho> @ \<sigma> \<in> P"
    assume assm3: "\<rho> @ \<tau> \<in> Q \<box>\<^sup>C R"
    assume assm4: "\<forall>\<rho>'\<in>tocks UNIV. \<rho>' \<le>\<^sub>C \<rho> @ \<sigma> \<longrightarrow> \<rho>' \<le>\<^sub>C \<rho>"
    assume assm5: "\<forall>\<rho>'\<in>tocks UNIV. \<rho>' \<le>\<^sub>C \<rho> @ \<tau> \<longrightarrow> \<rho>' \<le>\<^sub>C \<rho>"
    assume assm6: "\<not> (\<exists>\<rho>'\<in>tocks UNIV.
              \<exists>\<sigma>' \<tau>. \<rho>' @ \<sigma>' \<in> P \<box>\<^sup>C Q \<and>
                     \<rho>' @ \<tau> \<in> R \<and>
                     (\<forall>\<rho>''\<in>tocks UNIV. \<rho>'' \<le>\<^sub>C \<rho>' @ \<sigma>' \<longrightarrow> \<rho>'' \<le>\<^sub>C \<rho>') \<and>
                     (\<forall>\<rho>''\<in>tocks UNIV. \<rho>'' \<le>\<^sub>C \<rho>' @ \<tau> \<longrightarrow> \<rho>'' \<le>\<^sub>C \<rho>') \<and>
                     ((\<exists>X. \<sigma>' = [[X]\<^sub>R]) \<or> (\<exists>X. \<tau> = [[X]\<^sub>R]) \<longrightarrow> \<rho>' @ \<sigma>' = \<rho>' @ \<tau>) \<and> (\<rho> @ \<sigma> = \<rho>' @ \<sigma>' \<or> \<rho> @ \<sigma> = \<rho>' @ \<tau>))"
    assume assm7: "\<nexists>X. \<tau> = [[X]\<^sub>R]"
    obtain \<rho>' \<sigma>' \<tau>' where additional_assms:
                    "\<rho>' \<in> tocks UNIV" "\<rho>' @ \<sigma>' \<in> Q" "\<rho>' @ \<tau>' \<in> R"
                    "\<forall>\<rho>''\<in>tocks UNIV. \<rho>'' \<le>\<^sub>C \<rho>' @ \<sigma>' \<longrightarrow> \<rho>'' \<le>\<^sub>C \<rho>'"
                    "\<forall>\<rho>''\<in>tocks UNIV. \<rho>'' \<le>\<^sub>C \<rho>' @ \<tau>' \<longrightarrow> \<rho>'' \<le>\<^sub>C \<rho>'"
                    "\<rho> @ \<tau> = \<rho>' @ \<sigma>' \<or> \<rho> @ \<tau> = \<rho>' @ \<tau>'"
                    "(\<exists>X. \<sigma>' = [[X]\<^sub>R]) \<or> (\<exists>X. \<tau>' = [[X]\<^sub>R]) \<longrightarrow> \<rho>' @ \<sigma>' = \<rho>' @ \<tau>'"
      using assm3 unfolding ExtChoiceCTT_aux_def by (clarify, blast)
    have "\<rho> = \<rho>'"
      using additional_assms(6)
    proof auto
      assume case1: "\<rho> @ \<tau> = \<rho>' @ \<sigma>'"
      have "\<rho> \<le>\<^sub>C \<rho>'" by (metis additional_assms(4) assm1 case1 ctt_prefix_concat)
      also have "\<rho>' \<le>\<^sub>C \<rho>" by (simp add: additional_assms(1) assm5 case1 ctt_prefix_concat)
      then show "\<rho> = \<rho>'" by (simp add: calculation ctt_prefix_antisym)
    next
      assume case1: "\<rho> @ \<tau> = \<rho>' @ \<tau>'"
      have "\<rho> \<le>\<^sub>C \<rho>'" by (metis additional_assms(5) assm1 case1 ctt_prefix_concat)
      also have "\<rho>' \<le>\<^sub>C \<rho>" by (simp add: additional_assms(1) assm5 case1 ctt_prefix_concat)
      then show "\<rho> = \<rho>'" by (simp add: calculation ctt_prefix_antisym)
    qed
    then have "\<nexists>X. \<sigma> = [[X]\<^sub>R] \<Longrightarrow> \<exists>\<rho>'\<in>tocks UNIV.
              \<exists>\<sigma>' \<tau>. \<rho>' @ \<sigma>' \<in> P \<box>\<^sup>C Q \<and>
                     \<rho>' @ \<tau> \<in> R \<and>
                     (\<forall>\<rho>''\<in>tocks UNIV. \<rho>'' \<le>\<^sub>C \<rho>' @ \<sigma>' \<longrightarrow> \<rho>'' \<le>\<^sub>C \<rho>') \<and>
                     (\<forall>\<rho>''\<in>tocks UNIV. \<rho>'' \<le>\<^sub>C \<rho>' @ \<tau> \<longrightarrow> \<rho>'' \<le>\<^sub>C \<rho>') \<and>
                     ((\<exists>X. \<sigma>' = [[X]\<^sub>R]) \<or> (\<exists>X. \<tau> = [[X]\<^sub>R]) \<longrightarrow> \<rho>' @ \<sigma>' = \<rho>' @ \<tau>) \<and> (\<rho> @ \<sigma> = \<rho>' @ \<sigma>' \<or> \<rho> @ \<sigma> = \<rho>' @ \<tau>)"
      apply (rule_tac x="\<rho>" in bexI, rule_tac x="\<sigma>" in exI, rule_tac x="\<tau>'" in exI, safe)
      using assm1 assm2 assm4 assm5 assm7 additional_assms apply (simp_all)
      unfolding ExtChoiceCTT_aux_def apply (safe)
      apply (rule_tac x="\<rho>" in bexI, rule_tac x="\<sigma>" in exI, rule_tac x="\<sigma>'" in exI, safe, blast, blast)+
      done
    then show "\<exists>X. \<sigma> = [[X]\<^sub>R]"
      using assm6 by blast
  next
    fix \<rho> \<sigma> \<tau> :: "'a cttobs list"
    assume assm1: "\<rho> \<in> tocks UNIV"
    assume assm2: "\<rho> @ \<tau> \<in> P"
    assume assm3: "\<rho> @ \<tau> \<in> Q \<box>\<^sup>C R"
    assume assm5: "\<forall>\<rho>'\<in>tocks UNIV. \<rho>' \<le>\<^sub>C \<rho> @ \<tau> \<longrightarrow> \<rho>' \<le>\<^sub>C \<rho>"
    obtain \<rho>' \<sigma>' \<tau>' where additional_assms:
                    "\<rho>' \<in> tocks UNIV" "\<rho>' @ \<sigma>' \<in> Q" "\<rho>' @ \<tau>' \<in> R"
                    "\<forall>\<rho>''\<in>tocks UNIV. \<rho>'' \<le>\<^sub>C \<rho>' @ \<sigma>' \<longrightarrow> \<rho>'' \<le>\<^sub>C \<rho>'"
                    "\<forall>\<rho>''\<in>tocks UNIV. \<rho>'' \<le>\<^sub>C \<rho>' @ \<tau>' \<longrightarrow> \<rho>'' \<le>\<^sub>C \<rho>'"
                    "\<rho> @ \<tau> = \<rho>' @ \<sigma>' \<or> \<rho> @ \<tau> = \<rho>' @ \<tau>'"
                    "(\<exists>X. \<sigma>' = [[X]\<^sub>R]) \<or> (\<exists>X. \<tau>' = [[X]\<^sub>R]) \<longrightarrow> \<rho>' @ \<sigma>' = \<rho>' @ \<tau>'"
      using assm3 unfolding ExtChoiceCTT_aux_def by (clarify, blast)
    have "\<rho> = \<rho>'"
      using additional_assms(6)
    proof auto
      assume case1: "\<rho> @ \<tau> = \<rho>' @ \<sigma>'"
      have "\<rho> \<le>\<^sub>C \<rho>'" by (metis additional_assms(4) assm1 case1 ctt_prefix_concat)
      also have "\<rho>' \<le>\<^sub>C \<rho>" by (simp add: additional_assms(1) assm5 case1 ctt_prefix_concat)
      then show "\<rho> = \<rho>'" by (simp add: calculation ctt_prefix_antisym)
    next
      assume case1: "\<rho> @ \<tau> = \<rho>' @ \<tau>'"
      have "\<rho> \<le>\<^sub>C \<rho>'" by (metis additional_assms(5) assm1 case1 ctt_prefix_concat)
      also have "\<rho>' \<le>\<^sub>C \<rho>" by (simp add: additional_assms(1) assm5 case1 ctt_prefix_concat)
      then show "\<rho> = \<rho>'" by (simp add: calculation ctt_prefix_antisym)
    qed
    then show "\<exists>\<rho>'\<in>tocks UNIV.
          \<exists>\<sigma> \<tau>'. \<rho>' @ \<sigma> \<in> P \<box>\<^sup>C Q \<and>
                 \<rho>' @ \<tau>' \<in> R \<and>
                 (\<forall>\<rho>''\<in>tocks UNIV. \<rho>'' \<le>\<^sub>C \<rho>' @ \<sigma> \<longrightarrow> \<rho>'' \<le>\<^sub>C \<rho>') \<and>
                 (\<forall>\<rho>''\<in>tocks UNIV. \<rho>'' \<le>\<^sub>C \<rho>' @ \<tau>' \<longrightarrow> \<rho>'' \<le>\<^sub>C \<rho>') \<and>
                 ((\<exists>X. \<sigma> = [[X]\<^sub>R]) \<or> (\<exists>X. \<tau>' = [[X]\<^sub>R]) \<longrightarrow> \<rho>' @ \<sigma> = \<rho>' @ \<tau>') \<and> (\<rho> @ \<tau> = \<rho>' @ \<sigma> \<or> \<rho> @ \<tau> = \<rho>' @ \<tau>')"
      apply (rule_tac x="\<rho>" in bexI, rule_tac x="\<tau>" in exI, rule_tac x="\<tau>'" in exI, safe)
      using assm1 assm2 assm5 additional_assms apply (simp_all)
      apply safe
      unfolding ExtChoiceCTT_aux_def apply (safe)
      apply (rule_tac x="\<rho>" in bexI, rule_tac x="\<sigma>'" in exI, rule_tac x="\<sigma>'" in exI, safe)
      apply (rule_tac x="\<rho>" in bexI, rule_tac x="\<sigma>'" in exI, rule_tac x="\<sigma>'" in exI, safe)
      apply (rule_tac x="\<rho>" in bexI, rule_tac x="\<sigma>'" in exI, rule_tac x="\<sigma>'" in exI, safe)
      apply (rule_tac x="\<rho>" in bexI, rule_tac x="\<tau>'" in exI, rule_tac x="\<sigma>'" in exI, safe)
      apply (rule_tac x="\<rho>" in bexI, rule_tac x="\<tau>'" in exI, rule_tac x="\<sigma>'" in exI, safe)
      apply (rule_tac x="\<rho>" in bexI, rule_tac x="\<tau>'" in exI, rule_tac x="\<sigma>'" in exI, safe)
      apply (rule_tac x="\<rho>" in bexI, rule_tac x="\<tau>'" in exI, rule_tac x="\<tau>'" in exI, safe)
      apply (rule_tac x="\<rho>" in bexI, rule_tac x="\<tau>'" in exI, rule_tac x="\<tau>'" in exI, safe)
      apply (blast)
      done
  next
    fix \<rho> \<sigma> \<tau> :: "'a cttobs list"
    assume assm1: "\<rho> \<in> tocks UNIV"
    assume assm2: "\<rho> @ \<sigma> \<in> P"
    assume assm3: "\<rho> @ \<tau> \<in> Q \<box>\<^sup>C R"
    assume assm4: "\<forall>\<rho>'\<in>tocks UNIV. \<rho>' \<le>\<^sub>C \<rho> @ \<sigma> \<longrightarrow> \<rho>' \<le>\<^sub>C \<rho>"
    assume assm5: "\<forall>\<rho>'\<in>tocks UNIV. \<rho>' \<le>\<^sub>C \<rho> @ \<tau> \<longrightarrow> \<rho>' \<le>\<^sub>C \<rho>"
    assume assm6: "\<not> (\<exists>\<rho>'\<in>tocks UNIV.
              \<exists>\<sigma> \<tau>'. \<rho>' @ \<sigma> \<in> P \<box>\<^sup>C Q \<and>
                     \<rho>' @ \<tau>' \<in> R \<and>
                     (\<forall>\<rho>''\<in>tocks UNIV. \<rho>'' \<le>\<^sub>C \<rho>' @ \<sigma> \<longrightarrow> \<rho>'' \<le>\<^sub>C \<rho>') \<and>
                     (\<forall>\<rho>''\<in>tocks UNIV. \<rho>'' \<le>\<^sub>C \<rho>' @ \<tau>' \<longrightarrow> \<rho>'' \<le>\<^sub>C \<rho>') \<and>
                     ((\<exists>X. \<sigma> = [[X]\<^sub>R]) \<or> (\<exists>X. \<tau>' = [[X]\<^sub>R]) \<longrightarrow> \<rho>' @ \<sigma> = \<rho>' @ \<tau>') \<and> (\<rho> @ \<tau> = \<rho>' @ \<sigma> \<or> \<rho> @ \<tau> = \<rho>' @ \<tau>'))"
    assume assm7: "\<nexists>X. \<tau> = [[X]\<^sub>R]"
    obtain \<rho>' \<sigma>' \<tau>' where additional_assms:
                    "\<rho>' \<in> tocks UNIV" "\<rho>' @ \<sigma>' \<in> Q" "\<rho>' @ \<tau>' \<in> R"
                    "\<forall>\<rho>''\<in>tocks UNIV. \<rho>'' \<le>\<^sub>C \<rho>' @ \<sigma>' \<longrightarrow> \<rho>'' \<le>\<^sub>C \<rho>'"
                    "\<forall>\<rho>''\<in>tocks UNIV. \<rho>'' \<le>\<^sub>C \<rho>' @ \<tau>' \<longrightarrow> \<rho>'' \<le>\<^sub>C \<rho>'"
                    "\<rho> @ \<tau> = \<rho>' @ \<sigma>' \<or> \<rho> @ \<tau> = \<rho>' @ \<tau>'"
                    "(\<exists>X. \<sigma>' = [[X]\<^sub>R]) \<or> (\<exists>X. \<tau>' = [[X]\<^sub>R]) \<longrightarrow> \<rho>' @ \<sigma>' = \<rho>' @ \<tau>'"
      using assm3 unfolding ExtChoiceCTT_aux_def by (clarify, blast)
    have "\<rho> = \<rho>'"
      using additional_assms(6)
    proof auto
      assume case1: "\<rho> @ \<tau> = \<rho>' @ \<sigma>'"
      have "\<rho> \<le>\<^sub>C \<rho>'" by (metis additional_assms(4) assm1 case1 ctt_prefix_concat)
      also have "\<rho>' \<le>\<^sub>C \<rho>" by (simp add: additional_assms(1) assm5 case1 ctt_prefix_concat)
      then show "\<rho> = \<rho>'" by (simp add: calculation ctt_prefix_antisym)
    next
      assume case1: "\<rho> @ \<tau> = \<rho>' @ \<tau>'"
      have "\<rho> \<le>\<^sub>C \<rho>'" by (metis additional_assms(5) assm1 case1 ctt_prefix_concat)
      also have "\<rho>' \<le>\<^sub>C \<rho>" by (simp add: additional_assms(1) assm5 case1 ctt_prefix_concat)
      then show "\<rho> = \<rho>'" by (simp add: calculation ctt_prefix_antisym)
    qed
    then have "\<nexists>X. \<sigma> = [[X]\<^sub>R] \<Longrightarrow> \<exists>\<rho>'\<in>tocks UNIV.
              \<exists>\<sigma> \<tau>'. \<rho>' @ \<sigma> \<in> P \<box>\<^sup>C Q \<and>
                     \<rho>' @ \<tau>' \<in> R \<and>
                     (\<forall>\<rho>''\<in>tocks UNIV. \<rho>'' \<le>\<^sub>C \<rho>' @ \<sigma> \<longrightarrow> \<rho>'' \<le>\<^sub>C \<rho>') \<and>
                     (\<forall>\<rho>''\<in>tocks UNIV. \<rho>'' \<le>\<^sub>C \<rho>' @ \<tau>' \<longrightarrow> \<rho>'' \<le>\<^sub>C \<rho>') \<and>
                     ((\<exists>X. \<sigma> = [[X]\<^sub>R]) \<or> (\<exists>X. \<tau>' = [[X]\<^sub>R]) \<longrightarrow> \<rho>' @ \<sigma> = \<rho>' @ \<tau>') \<and> (\<rho> @ \<tau> = \<rho>' @ \<sigma> \<or> \<rho> @ \<tau> = \<rho>' @ \<tau>')"
      apply (rule_tac x="\<rho>" in bexI, rule_tac x="\<sigma>'" in exI, rule_tac x="\<tau>'" in exI, safe)
      using assm1 assm2 assm4 assm5 assm7 additional_assms apply (simp_all)
      unfolding ExtChoiceCTT_aux_def apply (safe)
      apply (rule_tac x="\<rho>" in bexI, rule_tac x="\<sigma>" in exI, rule_tac x="\<sigma>'" in exI, safe, blast, blast)+
      done
    then show "\<exists>X. \<sigma> = [[X]\<^sub>R]"
      using assm6 by blast
  next
    fix \<rho> \<sigma> \<tau> :: "'a cttobs list"
    assume assm1: "\<rho> \<in> tocks UNIV"
    assume assm2: "\<rho> @ \<tau> \<in> P"
    assume assm3: "\<rho> @ \<tau> \<in> Q \<box>\<^sup>C R"
    assume assm5: "\<forall>\<rho>'\<in>tocks UNIV. \<rho>' \<le>\<^sub>C \<rho> @ \<tau> \<longrightarrow> \<rho>' \<le>\<^sub>C \<rho>"
    obtain \<rho>' \<sigma>' \<tau>' where additional_assms:
                    "\<rho>' \<in> tocks UNIV" "\<rho>' @ \<sigma>' \<in> Q" "\<rho>' @ \<tau>' \<in> R"
                    "\<forall>\<rho>''\<in>tocks UNIV. \<rho>'' \<le>\<^sub>C \<rho>' @ \<sigma>' \<longrightarrow> \<rho>'' \<le>\<^sub>C \<rho>'"
                    "\<forall>\<rho>''\<in>tocks UNIV. \<rho>'' \<le>\<^sub>C \<rho>' @ \<tau>' \<longrightarrow> \<rho>'' \<le>\<^sub>C \<rho>'"
                    "\<rho> @ \<tau> = \<rho>' @ \<sigma>' \<or> \<rho> @ \<tau> = \<rho>' @ \<tau>'"
                    "(\<exists>X. \<sigma>' = [[X]\<^sub>R]) \<or> (\<exists>X. \<tau>' = [[X]\<^sub>R]) \<longrightarrow> \<rho>' @ \<sigma>' = \<rho>' @ \<tau>'"
      using assm3 unfolding ExtChoiceCTT_aux_def by (clarify, blast)
    have "\<rho> = \<rho>'"
      using additional_assms(6)
    proof auto
      assume case1: "\<rho> @ \<tau> = \<rho>' @ \<sigma>'"
      have "\<rho> \<le>\<^sub>C \<rho>'" by (metis additional_assms(4) assm1 case1 ctt_prefix_concat)
      also have "\<rho>' \<le>\<^sub>C \<rho>" by (simp add: additional_assms(1) assm5 case1 ctt_prefix_concat)
      then show "\<rho> = \<rho>'" by (simp add: calculation ctt_prefix_antisym)
    next
      assume case1: "\<rho> @ \<tau> = \<rho>' @ \<tau>'"
      have "\<rho> \<le>\<^sub>C \<rho>'" by (metis additional_assms(5) assm1 case1 ctt_prefix_concat)
      also have "\<rho>' \<le>\<^sub>C \<rho>" by (simp add: additional_assms(1) assm5 case1 ctt_prefix_concat)
      then show "\<rho> = \<rho>'" by (simp add: calculation ctt_prefix_antisym)
    qed
    then show "\<exists>\<rho>'\<in>tocks UNIV.
          \<exists>\<sigma> \<tau>'. \<rho>' @ \<sigma> \<in> P \<box>\<^sup>C Q \<and>
                 \<rho>' @ \<tau>' \<in> R \<and>
                 (\<forall>\<rho>''\<in>tocks UNIV. \<rho>'' \<le>\<^sub>C \<rho>' @ \<sigma> \<longrightarrow> \<rho>'' \<le>\<^sub>C \<rho>') \<and>
                 (\<forall>\<rho>''\<in>tocks UNIV. \<rho>'' \<le>\<^sub>C \<rho>' @ \<tau>' \<longrightarrow> \<rho>'' \<le>\<^sub>C \<rho>') \<and>
                 ((\<exists>X. \<sigma> = [[X]\<^sub>R]) \<or> (\<exists>X. \<tau>' = [[X]\<^sub>R]) \<longrightarrow> \<rho>' @ \<sigma> = \<rho>' @ \<tau>') \<and> (\<rho> @ \<tau> = \<rho>' @ \<sigma> \<or> \<rho> @ \<tau> = \<rho>' @ \<tau>')"
      apply (rule_tac x="\<rho>" in bexI, rule_tac x="\<tau>" in exI, rule_tac x="\<tau>'" in exI, safe)
      using assm1 assm2 assm5 additional_assms apply (simp_all)
      apply safe
      unfolding ExtChoiceCTT_aux_def apply (safe)
      apply (rule_tac x="\<rho>" in bexI, rule_tac x="\<sigma>'" in exI, rule_tac x="\<sigma>'" in exI, safe)
      apply (rule_tac x="\<rho>" in bexI, rule_tac x="\<sigma>'" in exI, rule_tac x="\<sigma>'" in exI, safe)
      apply (rule_tac x="\<rho>" in bexI, rule_tac x="\<sigma>'" in exI, rule_tac x="\<sigma>'" in exI, safe)
      apply (rule_tac x="\<rho>" in bexI, rule_tac x="\<tau>'" in exI, rule_tac x="\<sigma>'" in exI, safe)
      apply (rule_tac x="\<rho>" in bexI, rule_tac x="\<tau>'" in exI, rule_tac x="\<sigma>'" in exI, safe)
      apply (rule_tac x="\<rho>" in bexI, rule_tac x="\<tau>'" in exI, rule_tac x="\<sigma>'" in exI, safe)
      apply (rule_tac x="\<rho>" in bexI, rule_tac x="\<tau>'" in exI, rule_tac x="\<tau>'" in exI, safe)
      apply (rule_tac x="\<rho>" in bexI, rule_tac x="\<tau>'" in exI, rule_tac x="\<tau>'" in exI, safe)
      apply (blast)
      done
  next
    fix \<rho> \<sigma> \<tau> :: "'a cttobs list"
    assume assm1: "\<rho> \<in> tocks UNIV"
    assume assm2: "\<rho> @ \<sigma> \<in> P \<box>\<^sup>C Q"
    assume assm3: "\<rho> @ \<tau> \<in> R"
    assume assm4: "\<forall>\<rho>'\<in>tocks UNIV. \<rho>' \<le>\<^sub>C \<rho> @ \<sigma> \<longrightarrow> \<rho>' \<le>\<^sub>C \<rho>"
    assume assm5: "\<forall>\<rho>'\<in>tocks UNIV. \<rho>' \<le>\<^sub>C \<rho> @ \<tau> \<longrightarrow> \<rho>' \<le>\<^sub>C \<rho>"
    assume assm6: "\<not> (\<exists>\<rho>'\<in>tocks UNIV.
              \<exists>\<sigma>' \<tau>. \<rho>' @ \<sigma>' \<in> P \<and>
                     \<rho>' @ \<tau> \<in> Q \<box>\<^sup>C R \<and>
                     (\<forall>\<rho>''\<in>tocks UNIV. \<rho>'' \<le>\<^sub>C \<rho>' @ \<sigma>' \<longrightarrow> \<rho>'' \<le>\<^sub>C \<rho>') \<and>
                     (\<forall>\<rho>''\<in>tocks UNIV. \<rho>'' \<le>\<^sub>C \<rho>' @ \<tau> \<longrightarrow> \<rho>'' \<le>\<^sub>C \<rho>') \<and>
                     ((\<exists>X. \<sigma>' = [[X]\<^sub>R]) \<or> (\<exists>X. \<tau> = [[X]\<^sub>R]) \<longrightarrow> \<rho>' @ \<sigma>' = \<rho>' @ \<tau>) \<and> (\<rho> @ \<sigma> = \<rho>' @ \<sigma>' \<or> \<rho> @ \<sigma> = \<rho>' @ \<tau>))"
    assume assm7: "\<nexists>X. \<tau> = [[X]\<^sub>R]"
    obtain \<rho>' \<sigma>' \<tau>' where additional_assms:
                    "\<rho>' \<in> tocks UNIV" "\<rho>' @ \<sigma>' \<in> P" "\<rho>' @ \<tau>' \<in> Q"
                    "\<forall>\<rho>''\<in>tocks UNIV. \<rho>'' \<le>\<^sub>C \<rho>' @ \<sigma>' \<longrightarrow> \<rho>'' \<le>\<^sub>C \<rho>'"
                    "\<forall>\<rho>''\<in>tocks UNIV. \<rho>'' \<le>\<^sub>C \<rho>' @ \<tau>' \<longrightarrow> \<rho>'' \<le>\<^sub>C \<rho>'"
                    "\<rho> @ \<sigma> = \<rho>' @ \<sigma>' \<or> \<rho> @ \<sigma> = \<rho>' @ \<tau>'"
                    "(\<exists>X. \<sigma>' = [[X]\<^sub>R]) \<or> (\<exists>X. \<tau>' = [[X]\<^sub>R]) \<longrightarrow> \<rho>' @ \<sigma>' = \<rho>' @ \<tau>'"
      using assm2 unfolding ExtChoiceCTT_aux_def by (clarify, blast)
    have "\<rho> = \<rho>'"
      using additional_assms(6)
    proof auto
      assume case1: "\<rho> @ \<sigma> = \<rho>' @ \<sigma>'"
      have "\<rho> \<le>\<^sub>C \<rho>'" by (metis additional_assms(4) assm1 case1 ctt_prefix_concat)
      also have "\<rho>' \<le>\<^sub>C \<rho>" by (simp add: additional_assms(1) assm4 case1 ctt_prefix_concat)
      then show "\<rho> = \<rho>'" by (simp add: calculation ctt_prefix_antisym)
    next
      assume case1: "\<rho> @ \<sigma> = \<rho>' @ \<tau>'"
      have "\<rho> \<le>\<^sub>C \<rho>'" by (metis additional_assms(5) assm1 case1 ctt_prefix_concat)
      also have "\<rho>' \<le>\<^sub>C \<rho>" by (simp add: additional_assms(1) assm4 case1 ctt_prefix_concat)
      then show "\<rho> = \<rho>'" by (simp add: calculation ctt_prefix_antisym)
    qed
    then have "\<nexists>X. \<sigma> = [[X]\<^sub>R] \<Longrightarrow> (\<exists>\<rho>'\<in>tocks UNIV.
              \<exists>\<sigma>' \<tau>. \<rho>' @ \<sigma>' \<in> P \<and>
                     \<rho>' @ \<tau> \<in> Q \<box>\<^sup>C R \<and>
                     (\<forall>\<rho>''\<in>tocks UNIV. \<rho>'' \<le>\<^sub>C \<rho>' @ \<sigma>' \<longrightarrow> \<rho>'' \<le>\<^sub>C \<rho>') \<and>
                     (\<forall>\<rho>''\<in>tocks UNIV. \<rho>'' \<le>\<^sub>C \<rho>' @ \<tau> \<longrightarrow> \<rho>'' \<le>\<^sub>C \<rho>') \<and>
                     ((\<exists>X. \<sigma>' = [[X]\<^sub>R]) \<or> (\<exists>X. \<tau> = [[X]\<^sub>R]) \<longrightarrow> \<rho>' @ \<sigma>' = \<rho>' @ \<tau>) \<and> (\<rho> @ \<sigma> = \<rho>' @ \<sigma>' \<or> \<rho> @ \<sigma> = \<rho>' @ \<tau>))"
      apply (rule_tac x="\<rho>" in bexI, rule_tac x="\<sigma>'" in exI, rule_tac x="\<tau>'" in exI, safe)
      using assm1 assm3 assm4 assm5 assm7 additional_assms apply (simp_all)
      unfolding ExtChoiceCTT_aux_def apply (safe)
      apply (rule_tac x="\<rho>" in bexI, rule_tac x="\<tau>'" in exI, rule_tac x="\<tau>" in exI, safe, blast, blast)+
      done
    then show "\<exists>X. \<sigma> = [[X]\<^sub>R]"
      using assm6 by blast
  next
    fix \<rho> \<sigma> \<tau> :: "'a cttobs list"
    assume assm1: "\<rho> \<in> tocks UNIV"
    assume assm2: "\<rho> @ \<tau> \<in> P \<box>\<^sup>C Q"
    assume assm3: "\<rho> @ \<tau> \<in> R"
    assume assm4: "\<forall>\<rho>'\<in>tocks UNIV. \<rho>' \<le>\<^sub>C \<rho> @ \<sigma> \<longrightarrow> \<rho>' \<le>\<^sub>C \<rho>"
    assume assm5: "\<forall>\<rho>'\<in>tocks UNIV. \<rho>' \<le>\<^sub>C \<rho> @ \<tau> \<longrightarrow> \<rho>' \<le>\<^sub>C \<rho>"
    obtain \<rho>' \<sigma>' \<tau>' where additional_assms:
                    "\<rho>' \<in> tocks UNIV" "\<rho>' @ \<sigma>' \<in> P" "\<rho>' @ \<tau>' \<in> Q"
                    "\<forall>\<rho>''\<in>tocks UNIV. \<rho>'' \<le>\<^sub>C \<rho>' @ \<sigma>' \<longrightarrow> \<rho>'' \<le>\<^sub>C \<rho>'"
                    "\<forall>\<rho>''\<in>tocks UNIV. \<rho>'' \<le>\<^sub>C \<rho>' @ \<tau>' \<longrightarrow> \<rho>'' \<le>\<^sub>C \<rho>'"
                    "\<rho> @ \<tau> = \<rho>' @ \<sigma>' \<or> \<rho> @ \<tau> = \<rho>' @ \<tau>'"
                    "(\<exists>X. \<sigma>' = [[X]\<^sub>R]) \<or> (\<exists>X. \<tau>' = [[X]\<^sub>R]) \<longrightarrow> \<rho>' @ \<sigma>' = \<rho>' @ \<tau>'"
      using assm2 unfolding ExtChoiceCTT_aux_def by (clarify, blast)
    have "\<rho> = \<rho>'"
      using additional_assms(6)
    proof auto
      assume case1: "\<rho> @ \<tau> = \<rho>' @ \<sigma>'"
      have "\<rho> \<le>\<^sub>C \<rho>'" by (metis additional_assms(4) assm1 case1 ctt_prefix_concat)
      also have "\<rho>' \<le>\<^sub>C \<rho>" by (simp add: additional_assms(1) assm5 case1 ctt_prefix_concat)
      then show "\<rho> = \<rho>'" by (simp add: calculation ctt_prefix_antisym)
    next
      assume case1: "\<rho> @ \<tau> = \<rho>' @ \<tau>'"
      have "\<rho> \<le>\<^sub>C \<rho>'" by (metis additional_assms(5) assm1 case1 ctt_prefix_concat)
      also have "\<rho>' \<le>\<^sub>C \<rho>" by (simp add: additional_assms(1) assm5 case1 ctt_prefix_concat)
      then show "\<rho> = \<rho>'" by (simp add: calculation ctt_prefix_antisym)
    qed
    then show "\<exists>\<rho>'\<in>tocks UNIV.
          \<exists>\<sigma> \<tau>'. \<rho>' @ \<sigma> \<in> P \<and>
                 \<rho>' @ \<tau>' \<in> Q \<box>\<^sup>C R \<and>
                 (\<forall>\<rho>''\<in>tocks UNIV. \<rho>'' \<le>\<^sub>C \<rho>' @ \<sigma> \<longrightarrow> \<rho>'' \<le>\<^sub>C \<rho>') \<and>
                 (\<forall>\<rho>''\<in>tocks UNIV. \<rho>'' \<le>\<^sub>C \<rho>' @ \<tau>' \<longrightarrow> \<rho>'' \<le>\<^sub>C \<rho>') \<and>
                 ((\<exists>X. \<sigma> = [[X]\<^sub>R]) \<or> (\<exists>X. \<tau>' = [[X]\<^sub>R]) \<longrightarrow> \<rho>' @ \<sigma> = \<rho>' @ \<tau>') \<and> (\<rho> @ \<tau> = \<rho>' @ \<sigma> \<or> \<rho> @ \<tau> = \<rho>' @ \<tau>')"
      apply (rule_tac x="\<rho>" in bexI, rule_tac x="\<sigma>'" in exI, rule_tac x="\<tau>" in exI, safe)
      using assm1 assm3 assm4 assm5 additional_assms apply (simp_all)
      unfolding ExtChoiceCTT_aux_def apply (safe)
      apply (rule_tac x="\<rho>" in bexI, rule_tac x="\<tau>'" in exI, rule_tac x="\<sigma>'" in exI, safe, blast, blast)+
      done
  next
    fix \<rho> \<sigma> \<tau> :: "'a cttobs list"
    assume assm1: "\<rho> \<in> tocks UNIV"
    assume assm2: "\<rho> @ \<sigma> \<in> P \<box>\<^sup>C Q"
    assume assm3: "\<rho> @ \<tau> \<in> R"
    assume assm4: "\<forall>\<rho>'\<in>tocks UNIV. \<rho>' \<le>\<^sub>C \<rho> @ \<sigma> \<longrightarrow> \<rho>' \<le>\<^sub>C \<rho>"
    assume assm5: "\<forall>\<rho>'\<in>tocks UNIV. \<rho>' \<le>\<^sub>C \<rho> @ \<tau> \<longrightarrow> \<rho>' \<le>\<^sub>C \<rho>"
    assume assm6: "\<not> (\<exists>\<rho>'\<in>tocks UNIV.
              \<exists>\<sigma> \<tau>'. \<rho>' @ \<sigma> \<in> P \<and>
                     \<rho>' @ \<tau>' \<in> Q \<box>\<^sup>C R \<and>
                     (\<forall>\<rho>''\<in>tocks UNIV. \<rho>'' \<le>\<^sub>C \<rho>' @ \<sigma> \<longrightarrow> \<rho>'' \<le>\<^sub>C \<rho>') \<and>
                     (\<forall>\<rho>''\<in>tocks UNIV. \<rho>'' \<le>\<^sub>C \<rho>' @ \<tau>' \<longrightarrow> \<rho>'' \<le>\<^sub>C \<rho>') \<and>
                     ((\<exists>X. \<sigma> = [[X]\<^sub>R]) \<or> (\<exists>X. \<tau>' = [[X]\<^sub>R]) \<longrightarrow> \<rho>' @ \<sigma> = \<rho>' @ \<tau>') \<and> (\<rho> @ \<tau> = \<rho>' @ \<sigma> \<or> \<rho> @ \<tau> = \<rho>' @ \<tau>'))"
    assume assm7: "\<nexists>X. \<tau> = [[X]\<^sub>R]"
    obtain \<rho>' \<sigma>' \<tau>' where additional_assms:
                    "\<rho>' \<in> tocks UNIV" "\<rho>' @ \<sigma>' \<in> P" "\<rho>' @ \<tau>' \<in> Q"
                    "\<forall>\<rho>''\<in>tocks UNIV. \<rho>'' \<le>\<^sub>C \<rho>' @ \<sigma>' \<longrightarrow> \<rho>'' \<le>\<^sub>C \<rho>'"
                    "\<forall>\<rho>''\<in>tocks UNIV. \<rho>'' \<le>\<^sub>C \<rho>' @ \<tau>' \<longrightarrow> \<rho>'' \<le>\<^sub>C \<rho>'"
                    "\<rho> @ \<sigma> = \<rho>' @ \<sigma>' \<or> \<rho> @ \<sigma> = \<rho>' @ \<tau>'"
                    "(\<exists>X. \<sigma>' = [[X]\<^sub>R]) \<or> (\<exists>X. \<tau>' = [[X]\<^sub>R]) \<longrightarrow> \<rho>' @ \<sigma>' = \<rho>' @ \<tau>'"
      using assm2 unfolding ExtChoiceCTT_aux_def by (clarify, blast)
    have "\<rho> = \<rho>'"
      using additional_assms(6)
    proof auto
      assume case1: "\<rho> @ \<sigma> = \<rho>' @ \<sigma>'"
      have "\<rho> \<le>\<^sub>C \<rho>'" by (metis additional_assms(4) assm1 case1 ctt_prefix_concat)
      also have "\<rho>' \<le>\<^sub>C \<rho>" by (simp add: additional_assms(1) assm4 case1 ctt_prefix_concat)
      then show "\<rho> = \<rho>'" by (simp add: calculation ctt_prefix_antisym)
    next
      assume case1: "\<rho> @ \<sigma> = \<rho>' @ \<tau>'"
      have "\<rho> \<le>\<^sub>C \<rho>'" by (metis additional_assms(5) assm1 case1 ctt_prefix_concat)
      also have "\<rho>' \<le>\<^sub>C \<rho>" by (simp add: additional_assms(1) assm4 case1 ctt_prefix_concat)
      then show "\<rho> = \<rho>'" by (simp add: calculation ctt_prefix_antisym)
    qed
    then have "\<nexists>X. \<sigma> = [[X]\<^sub>R] \<Longrightarrow> (\<exists>\<rho>'\<in>tocks UNIV.
              \<exists>\<sigma> \<tau>'. \<rho>' @ \<sigma> \<in> P \<and>
                     \<rho>' @ \<tau>' \<in> Q \<box>\<^sup>C R \<and>
                     (\<forall>\<rho>''\<in>tocks UNIV. \<rho>'' \<le>\<^sub>C \<rho>' @ \<sigma> \<longrightarrow> \<rho>'' \<le>\<^sub>C \<rho>') \<and>
                     (\<forall>\<rho>''\<in>tocks UNIV. \<rho>'' \<le>\<^sub>C \<rho>' @ \<tau>' \<longrightarrow> \<rho>'' \<le>\<^sub>C \<rho>') \<and>
                     ((\<exists>X. \<sigma> = [[X]\<^sub>R]) \<or> (\<exists>X. \<tau>' = [[X]\<^sub>R]) \<longrightarrow> \<rho>' @ \<sigma> = \<rho>' @ \<tau>') \<and> (\<rho> @ \<tau> = \<rho>' @ \<sigma> \<or> \<rho> @ \<tau> = \<rho>' @ \<tau>'))"
      apply (rule_tac x="\<rho>" in bexI, rule_tac x="\<sigma>'" in exI, rule_tac x="\<tau>" in exI, safe)
      using assm1 assm3 assm4 assm5 assm7 additional_assms apply (simp_all)
      unfolding ExtChoiceCTT_aux_def apply (safe)
      apply (rule_tac x="\<rho>" in bexI, rule_tac x="\<tau>'" in exI, rule_tac x="\<tau>" in exI, safe, blast+)
      done
    then show "\<exists>X. \<sigma> = [[X]\<^sub>R]"
      using assm6 by blast
  next
    fix \<rho> \<sigma> \<tau> :: "'a cttobs list"
    assume assm1: "\<rho> \<in> tocks UNIV"
    assume assm2: "\<rho> @ \<tau> \<in> P \<box>\<^sup>C Q"
    assume assm3: "\<rho> @ \<tau> \<in> R"
    assume assm4: "\<forall>\<rho>'\<in>tocks UNIV. \<rho>' \<le>\<^sub>C \<rho> @ \<sigma> \<longrightarrow> \<rho>' \<le>\<^sub>C \<rho>"
    assume assm5: "\<forall>\<rho>'\<in>tocks UNIV. \<rho>' \<le>\<^sub>C \<rho> @ \<tau> \<longrightarrow> \<rho>' \<le>\<^sub>C \<rho>"
    obtain \<rho>' \<sigma>' \<tau>' where additional_assms:
                    "\<rho>' \<in> tocks UNIV" "\<rho>' @ \<sigma>' \<in> P" "\<rho>' @ \<tau>' \<in> Q"
                    "\<forall>\<rho>''\<in>tocks UNIV. \<rho>'' \<le>\<^sub>C \<rho>' @ \<sigma>' \<longrightarrow> \<rho>'' \<le>\<^sub>C \<rho>'"
                    "\<forall>\<rho>''\<in>tocks UNIV. \<rho>'' \<le>\<^sub>C \<rho>' @ \<tau>' \<longrightarrow> \<rho>'' \<le>\<^sub>C \<rho>'"
                    "\<rho> @ \<tau> = \<rho>' @ \<sigma>' \<or> \<rho> @ \<tau> = \<rho>' @ \<tau>'"
                    "(\<exists>X. \<sigma>' = [[X]\<^sub>R]) \<or> (\<exists>X. \<tau>' = [[X]\<^sub>R]) \<longrightarrow> \<rho>' @ \<sigma>' = \<rho>' @ \<tau>'"
      using assm2 unfolding ExtChoiceCTT_aux_def by (clarify, blast)
    have "\<rho> = \<rho>'"
      using additional_assms(6)
    proof auto
      assume case1: "\<rho> @ \<tau> = \<rho>' @ \<sigma>'"
      have "\<rho> \<le>\<^sub>C \<rho>'" by (metis additional_assms(4) assm1 case1 ctt_prefix_concat)
      also have "\<rho>' \<le>\<^sub>C \<rho>" by (simp add: additional_assms(1) assm5 case1 ctt_prefix_concat)
      then show "\<rho> = \<rho>'" by (simp add: calculation ctt_prefix_antisym)
    next
      assume case1: "\<rho> @ \<tau> = \<rho>' @ \<tau>'"
      have "\<rho> \<le>\<^sub>C \<rho>'" by (metis additional_assms(5) assm1 case1 ctt_prefix_concat)
      also have "\<rho>' \<le>\<^sub>C \<rho>" by (simp add: additional_assms(1) assm5 case1 ctt_prefix_concat)
      then show "\<rho> = \<rho>'" by (simp add: calculation ctt_prefix_antisym)
    qed
    then show "\<exists>\<rho>'\<in>tocks UNIV.
          \<exists>\<sigma> \<tau>'. \<rho>' @ \<sigma> \<in> P \<and>
                 \<rho>' @ \<tau>' \<in> Q \<box>\<^sup>C R \<and>
                 (\<forall>\<rho>''\<in>tocks UNIV. \<rho>'' \<le>\<^sub>C \<rho>' @ \<sigma> \<longrightarrow> \<rho>'' \<le>\<^sub>C \<rho>') \<and>
                 (\<forall>\<rho>''\<in>tocks UNIV. \<rho>'' \<le>\<^sub>C \<rho>' @ \<tau>' \<longrightarrow> \<rho>'' \<le>\<^sub>C \<rho>') \<and>
                 ((\<exists>X. \<sigma> = [[X]\<^sub>R]) \<or> (\<exists>X. \<tau>' = [[X]\<^sub>R]) \<longrightarrow> \<rho>' @ \<sigma> = \<rho>' @ \<tau>') \<and> (\<rho> @ \<tau> = \<rho>' @ \<sigma> \<or> \<rho> @ \<tau> = \<rho>' @ \<tau>')"
      apply (rule_tac x="\<rho>" in bexI, rule_tac x="\<sigma>'" in exI, rule_tac x="\<tau>" in exI, safe)
      using assm1 assm3 assm4 assm5 additional_assms apply (simp_all)
      unfolding ExtChoiceCTT_aux_def apply (safe)
      apply (rule_tac x="\<rho>" in bexI, rule_tac x="\<tau>'" in exI, rule_tac x="\<sigma>'" in exI, safe, blast, blast)+
      done
  qed
  also have "... = ?rhs"
    unfolding ExtChoiceCTT_aux_def by simp
  then show ?thesis
    using calculation by auto
qed*)

lemma ExtChoiceCTT_union_dist: "P \<box>\<^sub>C (Q \<union> R) = (P \<box>\<^sub>C Q) \<union> (P \<box>\<^sub>C R)"
  unfolding ExtChoiceCTT_def by (safe, blast+)

lemma ExtChoice_subset_union: "P \<box>\<^sub>C Q \<subseteq> P \<union> Q"
  unfolding ExtChoiceCTT_def by auto

lemma ExtChoice_idempotent: "CT P \<Longrightarrow> P \<box>\<^sub>C P = P"
  unfolding ExtChoiceCTT_def apply auto
  using CT_wf split_tocks_longest by fastforce

subsection {* Sequential Composition *}

definition SeqCompCTT :: "'e cttobs list set \<Rightarrow> 'e cttobs list set \<Rightarrow> 'e cttobs list set" (infixl ";\<^sub>C" 60) where
  "P ;\<^sub>C Q = P \<union> {\<rho>. \<exists> s t. s @ [[Tick]\<^sub>E] \<in> P \<and> t \<in> Q \<and> \<rho> = s @ t}"

lemma SeqComp_wf: "\<forall> t\<in>P. cttWF t \<Longrightarrow> \<forall> t\<in>Q. cttWF t \<Longrightarrow> \<forall> t \<in> P ;\<^sub>C Q. cttWF t"
  unfolding SeqCompCTT_def
proof auto
  fix s ta
  assume "\<forall>x\<in>P. cttWF x" "s @ [[Tick]\<^sub>E] \<in> P"
  then have 1: "cttWF (s @ [[Tick]\<^sub>E])"
    by auto
  assume "\<forall>x\<in>Q. cttWF x" "ta \<in> Q"
  then have 2: "cttWF ta"
    by auto
  from 1 2 show "cttWF (s @ ta)"
    by (induct s rule:cttWF.induct, auto)
qed

lemma CT0_SeqComp: "CT0 P \<Longrightarrow> CT0 Q \<Longrightarrow> CT0 (P ;\<^sub>C Q)"
  unfolding SeqCompCTT_def CT0_def by auto

lemma CT1_SeqComp: "CT1 P \<Longrightarrow> CT1 Q \<Longrightarrow> CT1 (P ;\<^sub>C Q)"
  unfolding SeqCompCTT_def CT1_def
proof (safe, blast)
  fix \<rho> \<sigma> s t :: "'a cttobs list"
  assume assm1: "\<forall>\<rho> \<sigma>. \<rho> \<lesssim>\<^sub>C \<sigma> \<and> \<sigma> \<in> P \<longrightarrow> \<rho> \<in> P"
  assume assm2: "\<forall>\<rho> \<sigma>. \<rho> \<lesssim>\<^sub>C \<sigma> \<and> \<sigma> \<in> Q \<longrightarrow> \<rho> \<in> Q"
  assume assm3: "\<rho> \<notin> P"
  assume assm4: "\<rho> \<lesssim>\<^sub>C s @ t"
  assume assm5: "s @ [[Tick]\<^sub>E] \<in> P"
  assume assm6: "t \<in> Q"
  obtain r where 1: "\<rho> \<subseteq>\<^sub>C r \<and> r \<le>\<^sub>C s @ t"
    using assm4 ctt_prefix_subset_imp_ctt_subset_ctt_prefix by blast
  then obtain t' where 2: "r = s @ t' \<and> t' \<lesssim>\<^sub>C t"
    by (meson assm1 assm3 assm5 ctt_prefix_append_split ctt_prefix_concat ctt_prefix_imp_prefix_subset ctt_subset_imp_prefix_subset)
  then obtain s' t'' where 3: "s' \<subseteq>\<^sub>C s \<and> \<rho> = s' @ t''"
    using "1" ctt_prefix_concat ctt_prefix_ctt_subset ctt_prefix_split by blast
  then have 4: "t'' \<subseteq>\<^sub>C t'"
    using "1" "2" ctt_subset_remove_start by blast
  have "s' @ [[Tick]\<^sub>E] \<lesssim>\<^sub>C s @ [[Tick]\<^sub>E]"
    using 3 by (simp add: ctt_subset_end_event ctt_subset_imp_prefix_subset)
  then have 5: "s' @ [[Tick]\<^sub>E] \<in> P"
    using assm1 assm5 by blast
  have 6: "t'' \<in> Q"
    using "2" "4" assm2 assm6 ctt_subset_imp_prefix_subset by blast
  show "\<exists>s t. s @ [[Tick]\<^sub>E] \<in> P \<and> t \<in> Q \<and> \<rho> = s @ t"
    by (rule_tac x="s'" in exI, rule_tac x="t''" in exI, simp add: 3 5 6)
qed

lemma CT2_SeqComp: "CT P \<Longrightarrow> CT Q \<Longrightarrow> CT2 (P ;\<^sub>C Q)"
  unfolding SeqCompCTT_def CT2_def
proof auto
  fix \<rho> X Y
  assume assm1: "Y \<inter> {e. e \<noteq> Tock \<and> (\<rho> @ [[e]\<^sub>E] \<in> P \<or> (\<exists>s. s @ [[Tick]\<^sub>E] \<in> P \<and> (\<exists>t. t \<in> Q \<and> \<rho> @ [[e]\<^sub>E] = s @ t))) \<or>
                      e = Tock \<and>
                      (\<rho> @ [[X]\<^sub>R, [e]\<^sub>E] \<in> P \<or> (\<exists>s. s @ [[Tick]\<^sub>E] \<in> P \<and> (\<exists>t. t \<in> Q \<and> \<rho> @ [[X]\<^sub>R, [e]\<^sub>E] = s @ t)))} =
             {}"
  assume assm2: "CT P"
  assume assm3: "\<rho> @ [[X]\<^sub>R] \<in> P"
  have "Y \<inter> {e. e \<noteq> Tock \<and> (\<rho> @ [[e]\<^sub>E] \<in> P \<or> (\<exists>s. s @ [[Tick]\<^sub>E] \<in> P \<and> (\<exists>t. t \<in> Q \<and> \<rho> @ [[e]\<^sub>E] = s @ t))) \<or>
      e = Tock \<and> (\<rho> @ [[X]\<^sub>R, [e]\<^sub>E] \<in> P \<or> (\<exists>s. s @ [[Tick]\<^sub>E] \<in> P \<and> (\<exists>t. t \<in> Q \<and> \<rho> @ [[X]\<^sub>R, [e]\<^sub>E] = s @ t)))}
    = Y \<inter> ({e. e \<noteq> Tock \<and> \<rho> @ [[e]\<^sub>E] \<in> P \<or> e = Tock \<and> \<rho> @ [[X]\<^sub>R, [e]\<^sub>E] \<in> P}
      \<union> {e. e \<noteq> Tock \<and> (\<exists>s. s @ [[Tick]\<^sub>E] \<in> P \<and> (\<exists>t. t \<in> Q \<and> \<rho> @ [[e]\<^sub>E] = s @ t)) \<or>
        e = Tock \<and> (\<exists>s. s @ [[Tick]\<^sub>E] \<in> P \<and> (\<exists>t. t \<in> Q \<and> \<rho> @ [[X]\<^sub>R, [e]\<^sub>E] = s @ t))})"
    by auto
  then have "Y \<inter> ({e. e \<noteq> Tock \<and> \<rho> @ [[e]\<^sub>E] \<in> P \<or> e = Tock \<and> \<rho> @ [[X]\<^sub>R, [e]\<^sub>E] \<in> P}
      \<union> {e. e \<noteq> Tock \<and> (\<exists>s. s @ [[Tick]\<^sub>E] \<in> P \<and> (\<exists>t. t \<in> Q \<and> \<rho> @ [[e]\<^sub>E] = s @ t)) \<or>
        e = Tock \<and> (\<exists>s. s @ [[Tick]\<^sub>E] \<in> P \<and> (\<exists>t. t \<in> Q \<and> \<rho> @ [[X]\<^sub>R, [e]\<^sub>E] = s @ t))}) = {}"
    using assm1 by auto
  then have "(Y \<inter> {e. e \<noteq> Tock \<and> \<rho> @ [[e]\<^sub>E] \<in> P \<or> e = Tock \<and> \<rho> @ [[X]\<^sub>R, [e]\<^sub>E] \<in> P})
      \<union> (Y \<inter> {e. e \<noteq> Tock \<and> (\<exists>s. s @ [[Tick]\<^sub>E] \<in> P \<and> (\<exists>t. t \<in> Q \<and> \<rho> @ [[e]\<^sub>E] = s @ t)) \<or>
        e = Tock \<and> (\<exists>s. s @ [[Tick]\<^sub>E] \<in> P \<and> (\<exists>t. t \<in> Q \<and> \<rho> @ [[X]\<^sub>R, [e]\<^sub>E] = s @ t))}) = {}"
    by (simp add: Int_Un_distrib)  
  then have "Y \<inter> {e. e \<noteq> Tock \<and> \<rho> @ [[e]\<^sub>E] \<in> P \<or> e = Tock \<and> \<rho> @ [[X]\<^sub>R, [e]\<^sub>E] \<in> P} = {}
    \<and> Y \<inter> {e. e \<noteq> Tock \<and> (\<exists>s. s @ [[Tick]\<^sub>E] \<in> P \<and> (\<exists>t. t \<in> Q \<and> \<rho> @ [[e]\<^sub>E] = s @ t)) \<or>
        e = Tock \<and> (\<exists>s. s @ [[Tick]\<^sub>E] \<in> P \<and> (\<exists>t. t \<in> Q \<and> \<rho> @ [[X]\<^sub>R, [e]\<^sub>E] = s @ t))} = {}"
    by auto
  then show "\<rho> @ [[X \<union> Y]\<^sub>R] \<in> P"
    using CT2_def CT_CT2 assm2 assm3 by auto
next
  fix \<rho> X Y s t
  assume assm1: "Y \<inter> {e. e \<noteq> Tock \<and> (\<rho> @ [[e]\<^sub>E] \<in> P \<or> (\<exists>s. s @ [[Tick]\<^sub>E] \<in> P \<and> (\<exists>t. t \<in> Q \<and> \<rho> @ [[e]\<^sub>E] = s @ t))) \<or>
    e = Tock \<and> (\<rho> @ [[X]\<^sub>R, [e]\<^sub>E] \<in> P \<or> (\<exists>s. s @ [[Tick]\<^sub>E] \<in> P \<and> (\<exists>t. t \<in> Q \<and> \<rho> @ [[X]\<^sub>R, [e]\<^sub>E] = s @ t)))} = {}"
  assume assm2: "CT P"
  assume assm3: "CT Q"
  assume assm4: "\<forall>s. s @ [[Tick]\<^sub>E] \<in> P \<longrightarrow> (\<forall>t. t \<in> Q \<longrightarrow> \<rho> @ [[X \<union> Y]\<^sub>R] \<noteq> s @ t)"
  assume assm5: "s @ [[Tick]\<^sub>E] \<in> P"
  assume assm6: "t \<in> Q"
  assume assm7: "\<rho> @ [[X]\<^sub>R] = s @ t"
  have "t = [] \<or> (\<exists> t'. t = t' @ [[X]\<^sub>R])"
    by (metis append_butlast_last_id assm7 last_appendR last_snoc) 
  then show "\<rho> @ [[X \<union> Y]\<^sub>R] \<in> P"
  proof auto
    assume case_assm: "t = []"
    then have "s = \<rho> @ [[X]\<^sub>R]"
      by (simp add: assm7)
    then have "\<rho> @ [[X]\<^sub>R, [Tick]\<^sub>E] \<in> P"
      using assm5 by auto
    then have "cttWF (\<rho> @ [[X]\<^sub>R, [Tick]\<^sub>E])"
      using CT_wf assm2 by blast
    then have "False"
      by (induct \<rho> rule:cttWF.induct, auto)
    then show "\<rho> @ [[X \<union> Y]\<^sub>R] \<in> P"
      by auto
  next
    fix t'
    assume case_assm: "t = t' @ [[X]\<^sub>R]"
    then have 1: "{e. e \<noteq> Tock \<and> t' @ [[e]\<^sub>E] \<in> Q \<or> e = Tock \<and> t' @ [[X]\<^sub>R, [e]\<^sub>E] \<in> Q}
      \<subseteq> {e. e \<noteq> Tock \<and> (\<exists>s. s @ [[Tick]\<^sub>E] \<in> P \<and> (\<exists>t. t \<in> Q \<and> \<rho> @ [[e]\<^sub>E] = s @ t)) \<or>
          e = Tock \<and> (\<exists>s. s @ [[Tick]\<^sub>E] \<in> P \<and> (\<exists>t. t \<in> Q \<and> \<rho> @ [[X]\<^sub>R, [e]\<^sub>E] = s @ t))}"
      using assm5 assm7 by auto
    have "Y \<inter> {e. e \<noteq> Tock \<and> (\<rho> @ [[e]\<^sub>E] \<in> P \<or> (\<exists>s. s @ [[Tick]\<^sub>E] \<in> P \<and> (\<exists>t. t \<in> Q \<and> \<rho> @ [[e]\<^sub>E] = s @ t))) \<or>
        e = Tock \<and> (\<rho> @ [[X]\<^sub>R, [e]\<^sub>E] \<in> P \<or> (\<exists>s. s @ [[Tick]\<^sub>E] \<in> P \<and> (\<exists>t. t \<in> Q \<and> \<rho> @ [[X]\<^sub>R, [e]\<^sub>E] = s @ t)))}
      = Y \<inter> ({e. e \<noteq> Tock \<and> \<rho> @ [[e]\<^sub>E] \<in> P \<or> e = Tock \<and> \<rho> @ [[X]\<^sub>R, [e]\<^sub>E] \<in> P}
        \<union> {e. e \<noteq> Tock \<and> (\<exists>s. s @ [[Tick]\<^sub>E] \<in> P \<and> (\<exists>t. t \<in> Q \<and> \<rho> @ [[e]\<^sub>E] = s @ t)) \<or>
          e = Tock \<and> (\<exists>s. s @ [[Tick]\<^sub>E] \<in> P \<and> (\<exists>t. t \<in> Q \<and> \<rho> @ [[X]\<^sub>R, [e]\<^sub>E] = s @ t))})"
      by auto
    then have "Y \<inter> ({e. e \<noteq> Tock \<and> \<rho> @ [[e]\<^sub>E] \<in> P \<or> e = Tock \<and> \<rho> @ [[X]\<^sub>R, [e]\<^sub>E] \<in> P}
        \<union> {e. e \<noteq> Tock \<and> (\<exists>s. s @ [[Tick]\<^sub>E] \<in> P \<and> (\<exists>t. t \<in> Q \<and> \<rho> @ [[e]\<^sub>E] = s @ t)) \<or>
          e = Tock \<and> (\<exists>s. s @ [[Tick]\<^sub>E] \<in> P \<and> (\<exists>t. t \<in> Q \<and> \<rho> @ [[X]\<^sub>R, [e]\<^sub>E] = s @ t))}) = {}"
      using assm1 by auto
    then have "(Y \<inter> {e. e \<noteq> Tock \<and> \<rho> @ [[e]\<^sub>E] \<in> P \<or> e = Tock \<and> \<rho> @ [[X]\<^sub>R, [e]\<^sub>E] \<in> P})
        \<union> (Y \<inter> {e. e \<noteq> Tock \<and> (\<exists>s. s @ [[Tick]\<^sub>E] \<in> P \<and> (\<exists>t. t \<in> Q \<and> \<rho> @ [[e]\<^sub>E] = s @ t)) \<or>
          e = Tock \<and> (\<exists>s. s @ [[Tick]\<^sub>E] \<in> P \<and> (\<exists>t. t \<in> Q \<and> \<rho> @ [[X]\<^sub>R, [e]\<^sub>E] = s @ t))}) = {}"
      by (simp add: Int_Un_distrib)  
    then have "Y \<inter> {e. e \<noteq> Tock \<and> \<rho> @ [[e]\<^sub>E] \<in> P \<or> e = Tock \<and> \<rho> @ [[X]\<^sub>R, [e]\<^sub>E] \<in> P} = {}
      \<and> Y \<inter> {e. e \<noteq> Tock \<and> (\<exists>s. s @ [[Tick]\<^sub>E] \<in> P \<and> (\<exists>t. t \<in> Q \<and> \<rho> @ [[e]\<^sub>E] = s @ t)) \<or>
          e = Tock \<and> (\<exists>s. s @ [[Tick]\<^sub>E] \<in> P \<and> (\<exists>t. t \<in> Q \<and> \<rho> @ [[X]\<^sub>R, [e]\<^sub>E] = s @ t))} = {}"
      by auto    
    then have "Y \<inter> {e. e \<noteq> Tock \<and> \<rho> @ [[e]\<^sub>E] \<in> P \<or> e = Tock \<and> \<rho> @ [[X]\<^sub>R, [e]\<^sub>E] \<in> P} = {}
        \<and> Y \<inter> {e. e \<noteq> Tock \<and> t' @ [[e]\<^sub>E] \<in> Q \<or> e = Tock \<and> t' @ [[X]\<^sub>R, [e]\<^sub>E] \<in> Q} = {}"
      by (metis (no_types, lifting) 1 Int_left_commute inf.orderE inf_bot_right)
    then have "t' @ [[X \<union> Y]\<^sub>R] \<in> Q"
      using CT2_def CT_def assm3 assm6 case_assm by auto
    then have "\<rho> @ [[X \<union> Y]\<^sub>R] \<noteq> s @ t' @ [[X \<union> Y]\<^sub>R]"
      using assm4 assm5 by auto
    then have "False"
      using case_assm assm7 by auto
    then show "\<rho> @ [[X \<union> Y]\<^sub>R] \<in> P"
      by auto
  qed
qed

lemma CT3_SeqComp: 
  assumes "CT P" "CT Q"
  shows "CT3 (P ;\<^sub>C Q)"
  unfolding CT3_def SeqCompCTT_def
proof auto
  fix x
  show "x \<in> P \<Longrightarrow> CT3_trace x"
    using CT3_def CT_CT3 assms(1) by blast
next
  fix s t
  assume "s @ [[Tick]\<^sub>E] \<in> P"
  then have 1: "CT3_trace s"
    by (meson CT1_def CT3_def CT_CT1 CT_CT3 assms(1) ctt_prefix_concat ctt_prefix_imp_prefix_subset)
  assume "t \<in> Q"
  then have 2: "CT3_trace t \<and> cttWF t"
    using CT3_def CT_CT3 CT_wf assms(2) by blast
  show "CT3_trace (s @ t)"
    using 1 2 CT3_append by auto
qed     

lemma CT_SeqComp: 
  assumes "CT P" "CT Q"
  shows "CT (P ;\<^sub>C Q)"
  unfolding CT_def apply auto
  apply (metis CT_def SeqComp_wf assms(1) assms(2))
  apply (simp add: CT0_SeqComp CT_CT0 assms(1) assms(2))
  apply (simp add: CT1_SeqComp CT_CT1 assms(1) assms(2))
  apply (simp add: CT2_SeqComp assms(1) assms(2))
  apply (simp add: CT3_SeqComp assms(1) assms(2))
  done

subsection {* Parallel Composition *}

function merge_traces :: "'e cttobs list \<Rightarrow> 'e set \<Rightarrow> 'e cttobs list \<Rightarrow> 'e cttobs list set" (infixl "\<lbrakk>_\<rbrakk>\<^sup>T\<^sub>C" 55) where
  "merge_traces [] Z [] = {[]}" | 
  "merge_traces [] Z [[Y]\<^sub>R] = {[]}" | (* if one side lacks a refusal, the composition lacks a refusal *) 
  "merge_traces [] Z [[Tick]\<^sub>E] = {}" | (* both must terminate together *)
  "merge_traces [] Z ([Event f]\<^sub>E # \<sigma>) = {t. f \<notin> Z \<and> (\<exists> s. s \<in> merge_traces [] Z \<sigma> \<and> t = [Event f]\<^sub>E # s)}" | (* the event from one side is performed *) 
  "merge_traces [] Z ([Y]\<^sub>R # [Tock]\<^sub>E # \<sigma>) = {}" | (* Tock must always synchronise *)
  "merge_traces [[X]\<^sub>R] Z [] = {[]}" | (* if one side lacks a refusal, the composition lacks a refusal *) 
  "merge_traces [[X]\<^sub>R] Z [[Y]\<^sub>R] = {t. \<exists> W. W \<subseteq> X \<union> Y \<and> {e. e \<in> Y \<and> e \<notin> ((Event ` Z) \<union> {Tock, Tick})} = {e. e \<in> X \<and> e \<notin> ((Event ` Z) \<union> {Tock, Tick})} \<and> t = [[W]\<^sub>R]}" | (* intersect the refusals for non-synchronised events, union for synchronised events *) 
  "merge_traces [[X]\<^sub>R] Z [[Tick]\<^sub>E] = {}" | (* both must terminate together *) 
  "merge_traces [[X]\<^sub>R] Z ([Event f]\<^sub>E # \<sigma>) = {t. f \<notin> Z \<and> (\<exists> s. s \<in> merge_traces [[X]\<^sub>R] Z \<sigma> \<and> t = [Event f]\<^sub>E # s)}" | (* the event from one side is performed *)  
  "merge_traces [[X]\<^sub>R] Z ([Y]\<^sub>R # [Tock]\<^sub>E # \<sigma>) = {}" | (* Tock must always synchronise*)  
  "merge_traces [[Tick]\<^sub>E] Z [] = {}" | (* both must terminate together *)
  "merge_traces [[Tick]\<^sub>E] Z [[Y]\<^sub>R] = {}" | (* both must terminate together *)
  "merge_traces [[Tick]\<^sub>E] Z [[Tick]\<^sub>E] = {[[Tick]\<^sub>E]}" | (* both terminate together *)
  "merge_traces [[Tick]\<^sub>E] Z ([Event f]\<^sub>E # \<sigma>) = {t. f \<notin> Z \<and> (\<exists> s. s \<in> merge_traces [[Tick]\<^sub>E] Z \<sigma> \<and> t = [Event f]\<^sub>E # s)}" | (* the event from one side is performed *) 
  "merge_traces [[Tick]\<^sub>E] Z ([Y]\<^sub>R # [Tock]\<^sub>E # \<sigma>) = {t. (\<exists> W s. [[W]\<^sub>R] \<in> merge_traces [[UNIV]\<^sub>R] Z [[Y]\<^sub>R] \<and> s \<in> merge_traces [[Tick]\<^sub>E] Z \<sigma> \<and> t = [W]\<^sub>R # [Tock]\<^sub>E # s)}" | (* Tock must synchronize, but there are implicit tocks allowed after termination, the refusal set after Tick is everything *)
  "merge_traces ([Event e]\<^sub>E # \<sigma>) Z [] = {t. e \<notin> Z \<and> (\<exists> s. s \<in> merge_traces [] Z \<sigma> \<and> t = [Event e]\<^sub>E # s)}" | (* the event from one side is performed *)
  "merge_traces ([Event e]\<^sub>E # \<sigma>) Z [[Y]\<^sub>R] = {t. e \<notin> Z \<and> (\<exists> s. s \<in> merge_traces \<sigma> Z [[Y]\<^sub>R] \<and> t = [Event e]\<^sub>E # s)}" | (* *) 
  "merge_traces ([Event e]\<^sub>E # \<sigma>) Z [[Tick]\<^sub>E] = {t. e \<notin> Z \<and> (\<exists> s. s \<in> merge_traces \<sigma> Z [[Tick]\<^sub>E] \<and> t = [Event e]\<^sub>E # s)}" | (* *)  
  "merge_traces ([Event e]\<^sub>E # \<rho>) Z ([Event f]\<^sub>E # \<sigma>) = 
    {t. (e \<notin> Z \<and> f \<notin> Z \<and> ((\<exists> s. s \<in> merge_traces ([Event e]\<^sub>E # \<rho>) Z \<sigma> \<and> t = [Event f]\<^sub>E # s) \<or> (\<exists> s. s \<in> merge_traces \<rho> Z ([Event f]\<^sub>E # \<sigma>) \<and> t = [Event e]\<^sub>E # s)))
      \<or> (e \<in> Z \<and> f \<notin> Z \<and> (\<exists> s. s \<in> merge_traces ([Event e]\<^sub>E # \<rho>) Z \<sigma> \<and> t = [Event f]\<^sub>E # s))
      \<or> (e \<notin> Z \<and> f \<in> Z \<and> (\<exists> s. s \<in> merge_traces \<rho> Z ([Event f]\<^sub>E # \<sigma>) \<and> t = [Event e]\<^sub>E # s))
      \<or> (e \<in> Z \<and> f \<in> Z \<and> e = f \<and> (\<exists> s. s \<in> merge_traces \<rho> Z \<sigma> \<and> t = [Event e]\<^sub>E # s))}" | (* *) 
  "merge_traces ([Event e]\<^sub>E # \<rho>) Z ([Y]\<^sub>R # [Tock]\<^sub>E # \<sigma>) = {t. e \<notin> Z \<and> (\<exists> s. s \<in> merge_traces \<rho> Z ([Y]\<^sub>R # [Tock]\<^sub>E # \<sigma>) \<and> t = [Event e]\<^sub>E # s)}" | (* *)  
  "merge_traces ([X]\<^sub>R # [Tock]\<^sub>E # \<sigma>) Z [] = {}" | (* Tock must always synchronise*) 
  "merge_traces ([X]\<^sub>R # [Tock]\<^sub>E # \<sigma>) Z [[Y]\<^sub>R] = {}" | (* Tock must always synchronise*)  
  "merge_traces ([X]\<^sub>R # [Tock]\<^sub>E # \<sigma>) Z [[Tick]\<^sub>E] = {t. (\<exists> W s. [[W]\<^sub>R] \<in> merge_traces [[X]\<^sub>R] Z [[UNIV]\<^sub>R] \<and> s \<in> merge_traces [[Tick]\<^sub>E] Z \<sigma> \<and> t = [W]\<^sub>R # [Tock]\<^sub>E # s)}" | (* Tock must synchronize, but there are implicit tocks allowed after termination, the refusal set after Tick is everything *)
  "merge_traces ([X]\<^sub>R # [Tock]\<^sub>E # \<rho>) Z ([Event f]\<^sub>E # \<sigma>) = {t. f \<notin> Z \<and> (\<exists> s. s \<in> merge_traces ([X]\<^sub>R # [Tock]\<^sub>E # \<rho>) Z \<sigma> \<and> t = [Event f]\<^sub>E # s)}" | (* *)  
  "merge_traces ([X]\<^sub>R # [Tock]\<^sub>E # \<rho>) Z ([Y]\<^sub>R # [Tock]\<^sub>E # \<sigma>) = {t. (\<exists> W s. [[W]\<^sub>R] \<in> merge_traces [[X]\<^sub>R] Z [[Y]\<^sub>R] \<and> s \<in> merge_traces \<rho> Z \<sigma> \<and> t = [W]\<^sub>R # [Tock]\<^sub>E # s)}" | (* *) 
  (* non-well-formed traces produce empty sets *)
  "merge_traces ([X]\<^sub>R # [Tick]\<^sub>E # \<rho>) Z \<sigma> = {}" |
  "merge_traces ([X]\<^sub>R # [Event e]\<^sub>E # \<rho>) Z \<sigma> = {}" |
  "merge_traces ([X]\<^sub>R # [Y]\<^sub>R # \<rho>) Z \<sigma> = {}" |
  "merge_traces \<rho> Z ([X]\<^sub>R # [Tick]\<^sub>E # \<sigma>) = {}" |
  "merge_traces \<rho> Z ([X]\<^sub>R # [Event e]\<^sub>E # \<sigma>) = {}" |
  "merge_traces \<rho> Z ([X]\<^sub>R # [Y]\<^sub>R # \<sigma>) = {}" |
  "merge_traces ([Tick]\<^sub>E # x # \<rho>) Z \<sigma> = {}" |
  "merge_traces \<rho> Z ([Tick]\<^sub>E # y # \<sigma>) = {}" |
  "merge_traces ([Tock]\<^sub>E # \<rho>) Z \<sigma> = {}" |
  "merge_traces \<rho> Z ([Tock]\<^sub>E # \<sigma>) = {}"
  by (pat_completeness, simp_all)
termination by (lexicographic_order)

lemma merge_traces_comm: "(x \<lbrakk>Z\<rbrakk>\<^sup>T\<^sub>C y) = (y \<lbrakk>Z\<rbrakk>\<^sup>T\<^sub>C x)"
  by (induct x Z y rule:merge_traces.induct, simp_all, blast+)

lemma merge_traces_wf: "cttWF x \<Longrightarrow> cttWF y \<Longrightarrow> \<forall> z\<in>(x \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C y). cttWF z"
proof (auto, induct x A y rule:merge_traces.induct, simp+, (safe, simp+), (safe, simp+), (safe, simp+), (safe, simp))
  fix Z Y \<sigma> z
  assume assm1: "\<And>x xa xb z. cttWF [[Tick]\<^sub>E] \<Longrightarrow> cttWF \<sigma> \<Longrightarrow> z \<in> [[Tick]\<^sub>E] \<lbrakk>Z\<rbrakk>\<^sup>T\<^sub>C \<sigma> \<Longrightarrow> cttWF z"
  assume assm2: "cttWF ([Y]\<^sub>R # [Tock]\<^sub>E # \<sigma>)"
  assume assm3: "cttWF [[Tick]\<^sub>E]"
  have \<sigma>_wf: "cttWF \<sigma>"
    using assm2 by auto
  assume "z \<in> [[Tick]\<^sub>E] \<lbrakk>Z\<rbrakk>\<^sup>T\<^sub>C [Y]\<^sub>R # [Tock]\<^sub>E # \<sigma>"
  then obtain W s where s_assms: "s \<in> [[Tick]\<^sub>E] \<lbrakk>Z\<rbrakk>\<^sup>T\<^sub>C \<sigma>" "z = [W]\<^sub>R # [Tock]\<^sub>E # s"
    by auto
  then have "cttWF s"
    using assm1 \<sigma>_wf assm3 by auto
  then show "cttWF z"
    using s_assms by auto
next
  fix e \<sigma> Z z
  assume assm1: "\<And>x xa z. cttWF [] \<Longrightarrow> cttWF \<sigma> \<Longrightarrow> z \<in> [] \<lbrakk>Z\<rbrakk>\<^sup>T\<^sub>C \<sigma> \<Longrightarrow> cttWF z"
  assume assm2: "cttWF ([Event e]\<^sub>E # \<sigma>)"
  assume assm3: "z \<in> [Event e]\<^sub>E # \<sigma> \<lbrakk>Z\<rbrakk>\<^sup>T\<^sub>C []"
  then obtain s where "s \<in> ([] \<lbrakk>Z\<rbrakk>\<^sup>T\<^sub>C \<sigma>) \<and> z = [Event e]\<^sub>E # s"
    by auto
  also have "cttWF \<sigma>"
    using assm2 by auto
  then show "cttWF z"
    using assm1 calculation by auto
next
  fix e \<sigma> Z Y z
  assume assm1: "\<And>x xa z. cttWF \<sigma> \<Longrightarrow> cttWF [[Y]\<^sub>R] \<Longrightarrow> z \<in> \<sigma> \<lbrakk>Z\<rbrakk>\<^sup>T\<^sub>C [[Y]\<^sub>R] \<Longrightarrow> cttWF z"
  assume assm2: "cttWF ([Event e]\<^sub>E # \<sigma>)"
  assume assm3: "z \<in> [Event e]\<^sub>E # \<sigma> \<lbrakk>Z\<rbrakk>\<^sup>T\<^sub>C [[Y]\<^sub>R]"
  then obtain s where "s \<in> (\<sigma> \<lbrakk>Z\<rbrakk>\<^sup>T\<^sub>C [[Y]\<^sub>R]) \<and> z = [Event e]\<^sub>E # s"
    by auto
  also have "cttWF \<sigma>"
    using assm2 by auto
  then show "cttWF z"
    using assm1 calculation by auto
next
  fix e \<sigma> Z z
  assume assm1: "\<And>x xa z. cttWF \<sigma> \<Longrightarrow> cttWF [[Tick]\<^sub>E] \<Longrightarrow> z \<in> \<sigma> \<lbrakk>Z\<rbrakk>\<^sup>T\<^sub>C [[Tick]\<^sub>E] \<Longrightarrow> cttWF z"
  assume assm2: "cttWF ([Event e]\<^sub>E # \<sigma>)"
  assume assm3: "z \<in> [Event e]\<^sub>E # \<sigma> \<lbrakk>Z\<rbrakk>\<^sup>T\<^sub>C [[Tick]\<^sub>E]"
  then obtain s where "s \<in> (\<sigma> \<lbrakk>Z\<rbrakk>\<^sup>T\<^sub>C [[Tick]\<^sub>E]) \<and> z = [Event e]\<^sub>E # s"
    by auto
  also have "cttWF \<sigma>"
    using assm2 by auto
  then show "cttWF z"
    using assm1 calculation by auto
next
  fix e Z f
  fix \<rho> \<sigma> z :: "'a cttobs list"
  assume assm1: "cttWF ([Event e]\<^sub>E # \<rho>)"
  assume assm2: "cttWF ([Event f]\<^sub>E # \<sigma>)"
  assume assm3: "\<And>x xa z. cttWF ([Event e]\<^sub>E # \<rho>) \<Longrightarrow> cttWF \<sigma> \<Longrightarrow> z \<in> [Event e]\<^sub>E # \<rho> \<lbrakk>Z\<rbrakk>\<^sup>T\<^sub>C \<sigma> \<Longrightarrow> cttWF z"
  assume assm4: "\<And>x xa z. cttWF \<rho> \<Longrightarrow> cttWF ([Event f]\<^sub>E # \<sigma>) \<Longrightarrow> z \<in> \<rho> \<lbrakk>Z\<rbrakk>\<^sup>T\<^sub>C [Event f]\<^sub>E # \<sigma> \<Longrightarrow> cttWF z"
  assume assm5: "\<And>x xa z. cttWF \<rho> \<Longrightarrow> cttWF \<sigma> \<Longrightarrow> z \<in> \<rho> \<lbrakk>Z\<rbrakk>\<^sup>T\<^sub>C \<sigma> \<Longrightarrow> cttWF z"
  assume "z \<in> [Event e]\<^sub>E # \<rho> \<lbrakk>Z\<rbrakk>\<^sup>T\<^sub>C [Event f]\<^sub>E # \<sigma>"
  then obtain s where s_assms: "z = [Event f]\<^sub>E # s \<or> z = [Event e]\<^sub>E # s"
    "s \<in> ([Event e]\<^sub>E # \<rho> \<lbrakk>Z\<rbrakk>\<^sup>T\<^sub>C \<sigma>) \<or> s \<in> (\<rho> \<lbrakk>Z\<rbrakk>\<^sup>T\<^sub>C [Event f]\<^sub>E # \<sigma>) \<or> s \<in> (\<rho> \<lbrakk>Z\<rbrakk>\<^sup>T\<^sub>C \<sigma>)"
    by auto
  have \<rho>_wf: "cttWF \<rho>"
    using assm1 by auto
  have \<sigma>_wf: "cttWF \<sigma>"
    using assm2 by auto
  have "cttWF s"
    using s_assms assm1 assm2 assm3 assm4 assm5 \<rho>_wf \<sigma>_wf by auto
  then show "cttWF z"
    using s_assms by auto
next
  fix e Z Y 
  fix \<rho> \<sigma> z :: "'a cttobs list"
  assume assm1: "cttWF ([Event e]\<^sub>E # \<rho>)"
  then have \<rho>_wf: "cttWF \<rho>"
    by auto
  assume assm2: "cttWF ([Y]\<^sub>R # [Tock]\<^sub>E # \<sigma>)"
  assume assm3: "\<And>x xa z. cttWF \<rho> \<Longrightarrow> cttWF ([Y]\<^sub>R # [Tock]\<^sub>E # \<sigma>) \<Longrightarrow> z \<in> \<rho> \<lbrakk>Z\<rbrakk>\<^sup>T\<^sub>C [Y]\<^sub>R # [Tock]\<^sub>E # \<sigma> \<Longrightarrow> cttWF z"
  assume "z \<in> [Event e]\<^sub>E # \<rho> \<lbrakk>Z\<rbrakk>\<^sup>T\<^sub>C [Y]\<^sub>R # [Tock]\<^sub>E # \<sigma>"
  then obtain s where "s \<in> \<rho> \<lbrakk>Z\<rbrakk>\<^sup>T\<^sub>C [Y]\<^sub>R # [Tock]\<^sub>E # \<sigma>" "z = [Event e]\<^sub>E # s"
    by auto
  then show "cttWF z"
    using \<rho>_wf assm2 assm3 by auto
next
  fix X \<sigma> Z z
  show "z \<in> [X]\<^sub>R # [Tock]\<^sub>E # \<sigma> \<lbrakk>Z\<rbrakk>\<^sup>T\<^sub>C [] \<Longrightarrow> cttWF z"
    by auto
next
  fix X \<sigma> Z Y z
  show "z \<in> [X]\<^sub>R # [Tock]\<^sub>E # \<sigma> \<lbrakk>Z\<rbrakk>\<^sup>T\<^sub>C [[Y]\<^sub>R] \<Longrightarrow> cttWF z"
    by auto
next
  fix X \<sigma> Z z
  assume assm1: "cttWF ([X]\<^sub>R # [Tock]\<^sub>E # \<sigma>)"
  then have \<sigma>_wf: "cttWF \<sigma>"
    by auto
  assume assm2: "\<And>x xa xb z. cttWF [[Tick]\<^sub>E] \<Longrightarrow> cttWF \<sigma> \<Longrightarrow> z \<in> [[Tick]\<^sub>E] \<lbrakk>Z\<rbrakk>\<^sup>T\<^sub>C \<sigma> \<Longrightarrow> cttWF z"
  assume "z \<in> [X]\<^sub>R # [Tock]\<^sub>E # \<sigma> \<lbrakk>Z\<rbrakk>\<^sup>T\<^sub>C [[Tick]\<^sub>E]"
  then obtain s W where "s \<in> [[Tick]\<^sub>E] \<lbrakk>Z\<rbrakk>\<^sup>T\<^sub>C \<sigma>" "z = [W]\<^sub>R # [Tock]\<^sub>E # s"
    by auto
  then show "cttWF z"
    using \<sigma>_wf assm2 by auto
next
  fix X Z f
  fix \<rho> \<sigma> z :: "'a cttobs list"
  assume assm1: "cttWF ([Event f]\<^sub>E # \<sigma>)"
  then have \<sigma>_wf: "cttWF \<sigma>"
    by auto
  assume assm2: "cttWF ([X]\<^sub>R # [Tock]\<^sub>E # \<rho>)"
  assume assm3: "\<And>x xa z. cttWF ([X]\<^sub>R # [Tock]\<^sub>E # \<rho>) \<Longrightarrow> cttWF \<sigma> \<Longrightarrow> z \<in> [X]\<^sub>R # [Tock]\<^sub>E # \<rho> \<lbrakk>Z\<rbrakk>\<^sup>T\<^sub>C \<sigma> \<Longrightarrow> cttWF z"
  assume "z \<in> [X]\<^sub>R # [Tock]\<^sub>E # \<rho> \<lbrakk>Z\<rbrakk>\<^sup>T\<^sub>C [Event f]\<^sub>E # \<sigma>"
  then obtain s where "s \<in> [X]\<^sub>R # [Tock]\<^sub>E # \<rho> \<lbrakk>Z\<rbrakk>\<^sup>T\<^sub>C \<sigma>" "z = [Event f]\<^sub>E # s"
    by auto
  then show "cttWF z"
    using \<sigma>_wf assm2 assm3 by auto
next
  fix X Z Y
  fix \<rho> \<sigma> z :: "'a cttobs list"
  assume assm1: "cttWF ([X]\<^sub>R # [Tock]\<^sub>E # \<rho>)"
  then have \<rho>_wf: "cttWF \<rho>"
    by auto
  assume assm2: "cttWF ([Y]\<^sub>R # [Tock]\<^sub>E # \<sigma>)"
  then have \<sigma>_wf: "cttWF \<sigma>"
    by auto
  assume assm3: "\<And>x xa xb z. cttWF \<rho> \<Longrightarrow> cttWF \<sigma> \<Longrightarrow> z \<in> \<rho> \<lbrakk>Z\<rbrakk>\<^sup>T\<^sub>C \<sigma> \<Longrightarrow> cttWF z"
  assume "z \<in> [X]\<^sub>R # [Tock]\<^sub>E # \<rho> \<lbrakk>Z\<rbrakk>\<^sup>T\<^sub>C [Y]\<^sub>R # [Tock]\<^sub>E # \<sigma>"
  then obtain s W where "s \<in> \<rho> \<lbrakk>Z\<rbrakk>\<^sup>T\<^sub>C \<sigma>" "z = [W]\<^sub>R # [Tock]\<^sub>E # s"
    by auto
  then show "cttWF z"
    using \<rho>_wf \<sigma>_wf assm3 by auto
next
  fix X \<rho> Z \<sigma> z
  show "cttWF ([X]\<^sub>R # [Tick]\<^sub>E # \<rho>) \<Longrightarrow> cttWF z"
    by auto
next
  fix X e \<rho> Z \<sigma> z
  show "cttWF ([X]\<^sub>R # [Event e]\<^sub>E # \<rho>) \<Longrightarrow> cttWF z"
    by auto
next
  fix X Y \<rho> Z \<sigma> z
  show "cttWF ([X]\<^sub>R # [Y]\<^sub>R # \<rho>) \<Longrightarrow> cttWF z"
    by auto
next
  fix \<rho> Z X \<sigma> z
  show "cttWF ([X]\<^sub>R # [Tick]\<^sub>E # \<sigma>) \<Longrightarrow> cttWF z"
    by auto
next
  fix \<rho> Z X e \<sigma> z
  show "cttWF ([X]\<^sub>R # [Event e]\<^sub>E # \<sigma>) \<Longrightarrow> cttWF z"
    by auto
next
  fix \<rho> Z X Y \<sigma> z
  show "cttWF ([X]\<^sub>R # [Y]\<^sub>R # \<sigma>) \<Longrightarrow> cttWF z"
    by auto
next
  fix x \<rho> Z \<sigma> z
  show "cttWF ([Tick]\<^sub>E # x # \<rho>) \<Longrightarrow> cttWF z"
    by auto
next
  fix \<rho> Z y \<sigma> z
  show "cttWF ([Tick]\<^sub>E # y # \<sigma>) \<Longrightarrow> cttWF z"
    by auto
next
  fix \<rho> Z \<sigma> z
  show "cttWF ([Tock]\<^sub>E # \<rho>) \<Longrightarrow> cttWF z"
    by auto
next
  fix \<rho> Z \<sigma> z
  show "cttWF ([Tock]\<^sub>E # \<sigma>) \<Longrightarrow> cttWF z"
    by auto
qed

definition ParCompCTT :: "'e cttobs list set \<Rightarrow> 'e set \<Rightarrow> 'e cttobs list set \<Rightarrow> 'e cttobs list set" (infix "\<lbrakk>_\<rbrakk>\<^sub>C" 55) where
  "ParCompCTT P A Q = \<Union> {t. \<exists> p \<in> P. \<exists> q \<in> Q. t = merge_traces p A q}"

lemma ParCompCTT_wf: 
  assumes "\<forall>t\<in>P. cttWF t" "\<forall>t\<in>Q. cttWF t"
  shows "\<forall>t\<in>(P \<lbrakk>A\<rbrakk>\<^sub>C Q). cttWF t"
  unfolding ParCompCTT_def
proof auto
  fix p q x
  assume "p \<in> P"
  then have p_wf: "cttWF p"
    using assms(1) by auto
  assume "q \<in> Q"
  then have q_wf: "cttWF q"
    using assms(2) by auto
  show "x \<in> p \<lbrakk>A\<rbrakk>\<^sup>T\<^sub>C q \<Longrightarrow> cttWF x"
    using p_wf q_wf merge_traces_wf by auto
qed

section {* Refinement *}

definition RefinesCTT :: "'e cttobs list set \<Rightarrow> 'e cttobs list set \<Rightarrow> bool" (infix "\<sqsubseteq>\<^sub>C" 50) where
  "P \<sqsubseteq>\<^sub>C Q = (Q \<subseteq> P)"

subsection {* Compositionality *}

lemma Prefix_compositional: 
  "P \<sqsubseteq>\<^sub>C Q \<Longrightarrow> e \<rightarrow>\<^sub>C P \<sqsubseteq>\<^sub>C e \<rightarrow>\<^sub>C Q"
  unfolding RefinesCTT_def PrefixCTT_def by auto

lemma IntChoice_compositional1: 
  "P \<sqsubseteq>\<^sub>C Q \<Longrightarrow> P \<sqinter>\<^sub>C R \<sqsubseteq>\<^sub>C Q \<sqinter>\<^sub>C R"
  unfolding RefinesCTT_def IntChoiceCTT_def by auto

lemma IntChoice_compositional2: 
  "P \<sqsubseteq>\<^sub>C Q \<Longrightarrow> R \<sqinter>\<^sub>C P \<sqsubseteq>\<^sub>C R \<sqinter>\<^sub>C Q"
  unfolding RefinesCTT_def IntChoiceCTT_def by auto

lemma ExtChoice_compositional1: 
  "P \<sqsubseteq>\<^sub>C Q \<Longrightarrow> P \<box>\<^sub>C R \<sqsubseteq>\<^sub>C Q \<box>\<^sub>C R"
  unfolding RefinesCTT_def ExtChoiceCTT_def by auto

lemma ExtChoice_compositional2: 
  "P \<sqsubseteq>\<^sub>C Q \<Longrightarrow> R \<box>\<^sub>C P \<sqsubseteq>\<^sub>C R \<box>\<^sub>C Q"
  unfolding RefinesCTT_def ExtChoiceCTT_def by auto

lemma SeqComp_compositional1: 
  "P \<sqsubseteq>\<^sub>C Q \<Longrightarrow> P ;\<^sub>C R \<sqsubseteq>\<^sub>C Q ;\<^sub>C R"
  unfolding RefinesCTT_def SeqCompCTT_def by auto

lemma SeqComp_compositional2: 
  "P \<sqsubseteq>\<^sub>C Q \<Longrightarrow> R ;\<^sub>C P \<sqsubseteq>\<^sub>C R ;\<^sub>C Q"
  unfolding RefinesCTT_def SeqCompCTT_def by auto
end